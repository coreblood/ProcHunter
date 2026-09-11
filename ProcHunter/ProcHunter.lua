--=====================================================================
-- ProcHunter v1.3.0 — Uncapped Vault proc scanner
--
-- Lists every item in the Uncapped Vault that (a) can be equipped by
-- anyone (class/level restrictions ignored) and (b) carries an effect
-- spell found in the bundled proc database. Right-click withdraws.
--
-- Data path (confirmed live 2026-09-11): the realm does NOT answer a
-- third-party VLTGET — _G.UncappedVault.items is the real source. It
-- is read instantly on open and re-read every 2s while the window is
-- open. VLTGET is still sent underneath; a wire snapshot, if one ever
-- arrives, always takes over (and would bring VLTUPD-driven updates).
--
-- WITHDRAW: the working call into kirei's addon is unknown until the
-- current UncappedVault.lua is dissected, so withdrawal is a VERIFIED
-- CASCADE of harmless-if-wrong attempts — after each route it waits,
-- re-reads the vault, and only moves to the next route if the item
-- did not move. At most one route can take effect; the first that
-- works is remembered (db.wdRoute). CONFIRMED LIVE: the working
-- route delivers ONE copy per call and ignores the count, so a
-- withdrawal is target-based — the proven route is re-fired on a
-- ~0.9s cadence, measuring the actual delta each cycle, until the
-- requested count has moved, the row is gone, or deliveries stop
-- (then it reports "N of M (stopped)").
--
-- Slash: /ph, /prochunter        toggle the window
--        /ph debug               print all addon wire traffic (toggle)
--        /ph dump                describe _G.UncappedVault's data shape
--
-- 3.3.5a constraints honoured: no C_Timer, no SetShown, UI built
-- lazily after ADDON_LOADED, no dropdown init at file scope, frames
-- are shown-by-default so lazily built windows Hide() after build.
--=====================================================================

local ADDON   = "ProcHunter"
local VERSION = "1.3.0"
local SEND_PREFIX = "REAGENTBANK"
local RECV_PREFIX = "UNC"

local REQUEST_COOLDOWN = 3     -- min seconds between VLTGET sends
local DIRTY_DEBOUNCE   = 2     -- wait after a VLTUPD before re-requesting
local PRIME_INTERVAL   = 1     -- seconds between item-cache retry passes
local PRIME_MAX_TRIES  = 20    -- give up on an uncached item after this
local WIRE_WATCHDOG    = 5     -- silent seconds before the global fallback
local POLL_INTERVAL    = 2     -- global re-read cadence while window open
local WD_VERIFY_DELAY  = 1.5   -- seconds before verifying an unproven route
local WD_REPEAT_DELAY  = 0.9   -- cadence once the route is proven
local WD_MAX_ROUTE     = 5
local WD_MAX_CYCLES    = 200   -- hard cap on repeat cycles per withdrawal

-- client built-in fonts (zero size cost)
local FONTS = {
    { name = "Friz Quadrata", path = "Fonts\\FRIZQT__.TTF" },
    { name = "Arial Narrow",  path = "Fonts\\ARIALN.TTF" },
    { name = "Skurri",        path = "Fonts\\skurri.ttf" },
    { name = "Morpheus",      path = "Fonts\\MORPHEUS.ttf" },
}

local floor  = math.floor
local format = string.format
local lower  = string.lower
local find   = string.find
local gmatch = string.gmatch
local match  = string.match

--========================= shared state ==============================
-- (declared above every function that reads them — hard rule)
local db                    -- ProcHunterDB (SavedVariables)
local nameIndex             -- lowered item name -> array of proc spellIds
local spellClass = {}       -- spellId -> "flat" | "proc" (session cache)
local vault      = {}       -- committed snapshot rows
local staging    = {}       -- "e:rp" -> row, during a VLTROW stream
local matched    = {}       -- rows passing filters (display source)
local shown      = {}       -- matched after the text filter
local pending    = {}       -- entry -> retry count (waiting on item cache)
local pendingN   = 0
local flatHidden = 0        -- items hidden by the flat-stat filter
local ui                    -- main window (lazy)
local mmBtn                 -- minimap button (lazy)
local scanTip               -- hidden tooltip: item-cache priming + spell scans
local snapshotSeen = false
local lastRequest  = 0
local dirtyAt      = nil    -- GetTime() of last unhandled vault change
local awaitingAt   = nil    -- GetTime() of an unanswered VLTGET
local primeAt      = 0
local pollAt       = 0
local eqCount, procCount = 0, 0
local dataSource   = nil    -- "wire" | "UncappedVault"
local lastSig      = nil    -- change-detection signature of the snapshot
local wireDebug    = false
local pendingWD    = nil    -- in-flight withdraw (target-based; see header)
local wdDoneAt     = nil    -- show "withdrawn" until this fades
local wdDoneName   = nil
local wdFailed     = false
local visRows      = 14     -- rows that fit the current window height
local ROWH         = 22     -- current row height (depends on font size)
local ApplyLook             -- forward: applies font/size/alpha + relayout

--========================= small helpers =============================
local function Msg(text)
    DEFAULT_CHAT_FRAME:AddMessage("|cff33ff99ProcHunter|r " .. text)
end

local function Stamp()
    Msg("v" .. VERSION .. " — /ph or /prochunter to open")
end

local function ItemLink(e, rp)
    return format("item:%d:0:0:0:0:0:%d", e, rp or 0)
end

local function GetScanTip()
    if not scanTip then
        scanTip = CreateFrame("GameTooltip", "ProcHunterScanTip",
            nil, "GameTooltipTemplate")
        scanTip:SetOwner(UIParent, "ANCHOR_NONE")
    end
    return scanTip
end

-- Equippable by anyone: the row's item class is server truth —
-- 2 = weapon, 4 = armor (rings/trinkets/necks/cloaks/shields/relics
-- included). Rows without a class field use GetItemInfo's equip slot.
local function IsEquippable(row)
    if row.class then
        return row.class == 2 or row.class == 4
    end
    local equipLoc = select(9, GetItemInfo(row.e))
    if equipLoc == nil then return nil end -- uncached: unknown yet
    return equipLoc ~= "" and equipLoc ~= "INVTYPE_BAG"
        and equipLoc ~= "INVTYPE_QUIVER" and equipLoc ~= "INVTYPE_AMMO"
end

--========================= proc name index ===========================
local function IndexAdd(name, spellId)
    local k = lower(name)
    local t = nameIndex[k]
    if not t then t = {}; nameIndex[k] = t end
    for i = 1, #t do if t[i] == spellId then return end end
    t[#t + 1] = spellId
end

local function IndexTable(src)
    if type(src) ~= "table" then return end
    for spellId, v in pairs(src) do
        if type(v) == "string" then
            IndexAdd(v, spellId)
        elseif type(v) == "table" then
            for i = 1, #v do
                if type(v[i]) == "string" then IndexAdd(v[i], spellId) end
            end
        end
    end
end

local function BuildIndex()
    if nameIndex then return end
    nameIndex = {}
    IndexTable(ProcHunter_ProcDB)          -- generated item/set data
    IndexTable(ProcHunter_ProcDB_Manual)   -- hand overrides, if any
    -- ProcHunter_AbilityDB is deliberately NOT indexed: those are
    -- player abilities, not item effects.
end

--=================== flat-stat spell classification ==================
-- "+24 Intelligence"-style old-world bonuses are on-equip aura SPELLS,
-- so they matched the database like procs. Each candidate spell's own
-- tooltip is scanned once (spell data is client-local — instant, no
-- cache wait; the realm-shipped descScan pattern). A spell counts as a
-- passive flat bonus only if EVERY effect line is plain stat text with
-- no duration — anything unrecognised classifies as a real proc, so
-- uncertainty always keeps an item visible.
local function IsFlatLine(t)
    if find(t, "for %d+ sec") or find(t, "lasts %d") or find(t, " until ")
    then return false end
    -- Michael's rule: any PERCENTAGE bonus is a real effect and stays
    -- visible ("Improves critical strike damage by 3.15%") — only
    -- plain-number flat stats are hidden.
    if find(t, "%d%%") then return false end
    return (find(t, "^%+%d") 
        or find(t, "^increases? .+ by %d")
        or find(t, "^increases? .+ by up to %d")
        or find(t, "^improves? .+ by %d")
        or find(t, "^improves? .+ by up to %d")
        or find(t, "^decreases? .+ by %d")
        or find(t, "^reduces? .+ by %d")
        or find(t, "^restores %d+ .+ per %d+ sec")) and true or false
end

local function ClassifySpell(id)
    local c = spellClass[id]
    if c then return c end
    local tip = GetScanTip()
    tip:ClearLines()
    tip:SetHyperlink("spell:" .. id)
    local n = tip:NumLines() or 0
    local sawEffect, allFlat = false, true
    for i = 2, n do
        local fs = _G["ProcHunterScanTipTextLeft" .. i]
        local t = fs and fs:GetText()
        t = t and strtrim(lower(t)) or ""
        if t ~= "" and t ~= "passive" and not find(t, "^rank %d")
            and not find(t, "^requires") then
            sawEffect = true
            if not IsFlatLine(t) then allFlat = false; break end
        end
    end
    -- no readable effect text (custom/unknown spell) => keep visible
    c = (sawEffect and allFlat) and "flat" or "proc"
    spellClass[id] = c
    return c
end

--========================= cache priming =============================
local function Prime(e)
    local tip = GetScanTip()
    tip:ClearLines()
    tip:SetHyperlink("item:" .. e)
end

--========================= match pass ================================
local RefreshList -- forward (defined with the UI)

local function Rebuild()
    BuildIndex()
    for k in pairs(matched) do matched[k] = nil end
    for k in pairs(pending) do pending[k] = nil end
    pendingN, eqCount, procCount, flatHidden = 0, 0, 0, 0

    for i = 1, #vault do
        local row = vault[i]
        local eq = IsEquippable(row)
        if eq == nil then
            if not pending[row.e] then
                pending[row.e] = 0; pendingN = pendingN + 1; Prime(row.e)
            end
        elseif eq then
            eqCount = eqCount + 1
            local baseName = GetItemInfo(row.e)
            if not baseName then
                if not pending[row.e] then
                    pending[row.e] = 0; pendingN = pendingN + 1; Prime(row.e)
                end
            else
                local spells = nameIndex[lower(baseName)]
                if spells and #spells > 0 then
                    local procs, flats = {}, {}
                    for j = 1, #spells do
                        local id = spells[j]
                        if ClassifySpell(id) == "flat" then
                            flats[#flats + 1] = id
                        else
                            procs[#procs + 1] = id
                        end
                    end
                    if #procs == 0 and db.hideFlat then
                        flatHidden = flatHidden + 1
                    else
                        procCount = procCount + 1
                        local link = ItemLink(row.e, row.rp)
                        local dispName = GetItemInfo(link) or baseName
                        matched[#matched + 1] = {
                            e = row.e, rp = row.rp, count = row.count,
                            q = row.q, ilvl = row.ilvl,
                            name = dispName, link = link,
                            procs = procs, flats = flats,
                            spells = (#procs > 0) and procs or flats,
                        }
                    end
                end
            end
        end
    end

    table.sort(matched, function(a, b)
        local ai, bi = a.ilvl or 0, b.ilvl or 0
        if ai ~= bi then return ai > bi end
        return (a.name or "") < (b.name or "")
    end)
    if RefreshList then RefreshList() end
end

-- retry pass: any parked item whose info has arrived triggers a full
-- rebuild (vault snapshots are small; a rebuild is cheap and correct)
local function ResolvePending()
    if pendingN == 0 then return end
    local resolved, gaveUp = false, nil
    for e, tries in pairs(pending) do
        if GetItemInfo(e) then
            resolved = true
        elseif tries >= PRIME_MAX_TRIES then
            gaveUp = gaveUp or {}
            gaveUp[#gaveUp + 1] = e
        else
            pending[e] = tries + 1
            Prime(e)
        end
    end
    if gaveUp then
        for i = 1, #gaveUp do pending[gaveUp[i]] = nil; pendingN = pendingN - 1 end
        if RefreshList then RefreshList() end
    end
    if resolved then Rebuild() end
end

--========================= wire ======================================
local function Request()
    local now = GetTime()
    if now - lastRequest < REQUEST_COOLDOWN then return end
    lastRequest = now
    dirtyAt = nil
    awaitingAt = now
    SendAddonMessage(SEND_PREFIX, "VLTGET", "WHISPER", UnitName("player"))
end

local function StagingSig()
    local sig, n = 0, 0
    for _, row in pairs(staging) do
        n = n + 1
        sig = sig + row.e * 31 + (row.rp or 0) * 7 + (row.count or 1)
    end
    return sig * 100000 + n
end

local function CommitSnapshot(source)
    lastSig = StagingSig()
    for k in pairs(vault) do vault[k] = nil end
    local n = 0
    for _, row in pairs(staging) do n = n + 1; vault[n] = row end
    for k in pairs(staging) do staging[k] = nil end
    snapshotSeen = true
    awaitingAt = nil
    dataSource = source or "wire"
    Rebuild()
end

--=================== UncappedVault global read =======================
-- The confirmed live data path: kirei's addon keeps its items table
-- current through the realm's own transport; we read it directly.
local FIELD_E  = { "e", "entry", "id", "itemId", "itemid", "item" }
local FIELD_C  = { "count", "c", "n", "num", "stack", "stackCount" }
local FIELD_RP = { "rp", "randomProp", "randomprop", "rand", "suffix", "suffixId" }
local FIELD_Q  = { "q", "quality", "rarity" }
local FIELD_IL = { "ilvl", "itemLevel", "itemlevel", "level" }
local FIELD_CL = { "class", "itemClass", "itemclass", "cls" }

local function PickField(row, names)
    for i = 1, #names do
        local v = row[names[i]]
        if type(v) == "number" then return v end
    end
end

local function EntryFrom(v)
    if type(v) == "number" then return v end
    if type(v) == "string" then
        return tonumber(match(v, "item:(%d+)")) or tonumber(match(v, "^(%d+)$"))
    end
end

local function AbsorbRow(row)
    if type(row) ~= "table" then return false end
    local e = PickField(row, FIELD_E)
    if not e then
        e = EntryFrom(row.link or row.itemLink or row.itemlink)
    end
    if not e or e <= 0 then return false end
    local rp = PickField(row, FIELD_RP) or 0
    staging[e .. ":" .. rp] = {
        e = e, rp = rp,
        count = PickField(row, FIELD_C) or 1,
        q = PickField(row, FIELD_Q),
        ilvl = PickField(row, FIELD_IL),
        class = PickField(row, FIELD_CL),
    }
    return true
end

local function TryVaultGlobal()
    local UV = _G.UncappedVault
    local src = UV and type(UV) == "table" and UV.items
    if type(src) ~= "table" then return false end
    local got = 0
    for i = 1, #src do
        if AbsorbRow(src[i]) then got = got + 1 end
    end
    if got == 0 then
        for k, v in pairs(src) do
            if AbsorbRow(v) then
                got = got + 1
            else
                local e = EntryFrom(k)
                if e and type(v) == "number" and v > 0 then
                    staging[e .. ":0"] = { e = e, rp = 0, count = v }
                    got = got + 1
                end
            end
        end
    end
    if got > 0 then
        -- unchanged data: skip the rebuild churn (2s polling)
        if snapshotSeen and dataSource == "UncappedVault"
            and StagingSig() == lastSig then
            for k in pairs(staging) do staging[k] = nil end
            return true
        end
        CommitSnapshot("UncappedVault")
        return true
    end
    for k in pairs(staging) do staging[k] = nil end
    return false
end

local function DumpVault()
    local UV = _G.UncappedVault
    Msg("dump: UncappedVault is " .. type(UV))
    Msg("dump: remembered withdraw route: " .. tostring(db and db.wdRoute))
    if type(UV) ~= "table" then return end
    Msg("dump: .Withdraw is " .. type(UV.Withdraw) ..
        ", .Send is " .. type(UV.Send) .. ", .items is " .. type(UV.items))
    if type(UV.items) ~= "table" then return end
    local total, firstRow, firstKey = 0, nil, nil
    for k, v in pairs(UV.items) do
        total = total + 1
        if not firstRow then firstRow = v; firstKey = k end
    end
    Msg("dump: .items holds " .. total .. " entries, #items=" .. #UV.items)
    if firstRow == nil then return end
    Msg("dump: first key = " .. tostring(firstKey) ..
        " (" .. type(firstKey) .. "), value is " .. type(firstRow))
    if type(firstRow) == "table" then
        local shownN = 0
        for k, v in pairs(firstRow) do
            shownN = shownN + 1
            if shownN > 15 then Msg("dump: ...") break end
            Msg("dump:   ." .. tostring(k) .. " = " ..
                strsub(tostring(v), 1, 60) .. " (" .. type(v) .. ")")
        end
    else
        Msg("dump: first value = " .. strsub(tostring(firstRow), 1, 60))
    end
end

--========================= withdraw cascade ==========================
local function RowCount(e, rp)
    for i = 1, #vault do
        local r = vault[i]
        if r.e == e and (r.rp or 0) == (rp or 0) then return r.count or 1 end
    end
    return 0
end

-- Fire exactly route L. Every attempt is pcall-guarded and harmless
-- if wrong; verification between firings guarantees at most one route
-- ever takes effect. The verb carries the remaining count for
-- count-honoring routes; the live route ignores it (one per call).
local function TryRoute(w, L)
    local UV = _G.UncappedVault
    local rem = w.target - w.moved
    if rem < 1 then rem = 1 end
    local verb = format("VLTWD:%d:%d:%d", w.e, w.rp or 0, rem)
    if L == 1 and UV and type(UV.Withdraw) == "function" then
        return pcall(UV.Withdraw, w.e, w.rp or 0, rem) and true or false
    elseif L == 2 and UV and type(UV.Withdraw) == "function" then
        return pcall(UV.Withdraw, UV, w.e, w.rp or 0, rem) and true or false
    elseif L == 3 and UV and type(UV.Send) == "function" then
        return pcall(UV.Send, verb) and true or false
    elseif L == 4 and UV and type(UV.Send) == "function" then
        return pcall(UV.Send, UV, verb) and true or false
    elseif L == 5 then
        SendAddonMessage(SEND_PREFIX, verb, "WHISPER", UnitName("player"))
        return true
    end
    return false
end

local function CascadeNext(w)
    while w.route < WD_MAX_ROUTE do
        w.route = w.route + 1
        if TryRoute(w, w.route) then return true end
    end
    return false
end

local function StartWithdraw(m, count)
    if pendingWD then return end -- one at a time
    wdFailed, wdDoneAt, wdDoneName = false, nil, nil
    pendingWD = {
        e = m.e, rp = m.rp or 0,
        target = count, moved = 0, cycles = 0, proven = false,
        lastCount = m.count or 1, name = m.name or "?",
        route = (db.wdRoute and db.wdRoute - 1) or 0,
        at = GetTime(),
    }
    if not CascadeNext(pendingWD) then
        pendingWD = nil
        wdFailed = true
        db.wdRoute = nil
    end
    if RefreshList then RefreshList() end
end

local function CheckWithdraw(now)
    if not pendingWD then return end
    local w = pendingWD
    if now - w.at < (w.proven and WD_REPEAT_DELAY or WD_VERIFY_DELAY) then
        return
    end
    TryVaultGlobal()
    local c = RowCount(w.e, w.rp)
    local delta = (w.lastCount or 0) - c
    if delta > 0 then
        -- something moved: this route is the real one
        w.moved = w.moved + delta
        w.lastCount = c
        w.proven = true
        db.wdRoute = w.route
        if w.moved >= w.target or c == 0 then
            wdDoneAt = now
            wdDoneName = w.name ..
                ((w.target > 1) and format(" x%d", w.moved) or "")
            pendingWD = nil
        elseif w.cycles >= WD_MAX_CYCLES then
            wdDoneAt = now
            wdDoneName = format("%s — %d of %d (stopped)",
                w.name, w.moved, w.target)
            pendingWD = nil
        else
            -- the live route delivers one copy per call: re-fire the
            -- proven route until the target is reached
            w.cycles = w.cycles + 1
            TryRoute(w, w.route)
            w.at = now
        end
    else
        if w.proven then
            -- the proven route stopped delivering (bags full? refusal?)
            if w.moved > 0 then
                wdDoneAt = now
                wdDoneName = format("%s — %d of %d (stopped)",
                    w.name, w.moved, w.target)
            else
                wdFailed = true
            end
            pendingWD = nil
        elseif CascadeNext(w) then
            w.at = now
        else
            pendingWD = nil
            wdFailed = true
            db.wdRoute = nil
        end
    end
    if RefreshList then RefreshList() end
end

--========================= wire handler ==============================
local comms = CreateFrame("Frame")
comms:RegisterEvent("CHAT_MSG_ADDON")
comms:SetScript("OnEvent", function(_, _, prefix, msg)
    if wireDebug and msg then
        Msg("|cff888888[wire]|r " .. tostring(prefix) .. " " .. strsub(msg, 1, 70))
    end
    if prefix ~= RECV_PREFIX or not msg then return end
    if find(msg, "^VLTROW:") then
        local got = false
        for e, rp, c, q, cl, sub, il in gmatch(msg,
            "(%-?%d+),(%-?%d+),(%d+),(%-?%d+),(%-?%d+),(%-?%d+),(%-?%d+),[^;]*;") do
            got = true
            staging[e .. ":" .. rp] = {
                e = tonumber(e), rp = tonumber(rp), count = tonumber(c),
                q = tonumber(q), class = tonumber(cl), sub = tonumber(sub),
                ilvl = tonumber(il),
            }
        end
        if not got then
            for e, rp, c in gmatch(msg, "(%-?%d+),(%-?%d+),(%d+),[^;]*;") do
                staging[e .. ":" .. rp] = {
                    e = tonumber(e), rp = tonumber(rp), count = tonumber(c),
                }
            end
        end
    elseif find(msg, "^VLTEND:") or msg == "VLTEND" then
        CommitSnapshot("wire")
    elseif find(msg, "^VLTUPD") or find(msg, "^VLTROWUPD")
        or find(msg, "^VLTWDONE") or find(msg, "^VLTDEPALLDONE") then
        dirtyAt = GetTime()
    end
end)

--========================= ticker ====================================
local ticker = CreateFrame("Frame")
ticker:SetScript("OnUpdate", function()
    local now = GetTime()
    if dirtyAt and ui and ui:IsShown() and now - dirtyAt >= DIRTY_DEBOUNCE then
        Request()
    end
    if awaitingAt and now - awaitingAt >= WIRE_WATCHDOG then
        awaitingAt = nil
        if not TryVaultGlobal() and RefreshList then RefreshList() end
    end
    -- live updates: the wire's VLTUPD never arrives on this realm, so
    -- while the list is fed from the global, re-read it every 2s
    if ui and ui:IsShown() and dataSource ~= "wire"
        and now - pollAt >= POLL_INTERVAL then
        pollAt = now
        TryVaultGlobal()
    end
    CheckWithdraw(now)
    if wdDoneAt and now - wdDoneAt > 5 then
        wdDoneAt, wdDoneName = nil, nil
        if RefreshList then RefreshList() end
    end
    if pendingN > 0 and now - primeAt >= PRIME_INTERVAL then
        primeAt = now
        ResolvePending()
    end
end)

--========================= UI ========================================
local MAX_ROWS = 40

local function QualityHex(q)
    local c = q and ITEM_QUALITY_COLORS[q]
    return c and c.hex or "|cffffffff"
end

local function ProcLines(spells)
    local seen, out = {}, {}
    for i = 1, #spells do
        local id = spells[i]
        local sName = GetSpellInfo(id) or ("Spell #" .. id)
        local slot = seen[sName]
        if not slot then
            slot = { name = sName, ids = {} }
            seen[sName] = slot
            out[#out + 1] = slot
        end
        slot.ids[#slot.ids + 1] = id
    end
    return out
end

local function RowTooltip(row)
    GameTooltip:SetOwner(ui, "ANCHOR_NONE")
    GameTooltip:SetPoint("TOPLEFT", ui, "TOPRIGHT", 6, 0)
    GameTooltip:SetHyperlink(row.link)
    GameTooltip:AddLine(" ")
    GameTooltip:AddLine("Procs (ProcHunter database):", 0.2, 1, 0.6)
    local lines = ProcLines(row.procs)
    for i = 1, #lines do
        local l = lines[i]
        GameTooltip:AddLine("  " .. l.name .. " (" ..
            table.concat(l.ids, ", ") .. ")", 1, 1, 1)
        local src = ProcHunter_DropDB and ProcHunter_DropDB[l.ids[1]]
        if type(src) == "table" and #src > 0 then
            GameTooltip:AddLine("    from: " .. table.concat(src, ", "),
                0.6, 0.6, 0.6)
        end
    end
    local fl = ProcLines(row.flats)
    for i = 1, #fl do
        GameTooltip:AddLine("  " .. fl[i].name .. " (passive stat)",
            0.5, 0.5, 0.5)
    end
    GameTooltip:AddLine(" ")
    GameTooltip:AddLine("Right-click: withdraw to bags", 0.7, 0.7, 0.7)
    GameTooltip:AddLine("Shift+Right-click: withdraw one", 0.7, 0.7, 0.7)
    GameTooltip:Show()
end

local function BuildUI()
    if ui then return end
    ui = CreateFrame("Frame", "ProcHunterFrame", UIParent)
    ui:SetWidth(600); ui:SetHeight(430)
    ui:SetFrameStrata("HIGH")
    ui:SetBackdrop({
        bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
        edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
        tile = true, tileSize = 32, edgeSize = 32,
        insets = { left = 8, right = 8, top = 8, bottom = 8 },
    })
    ui:EnableMouse(true); ui:SetMovable(true)
    ui:RegisterForDrag("LeftButton")
    ui:SetScript("OnDragStart", function(self) self:StartMoving() end)
    ui:SetScript("OnDragStop", function(self)
        self:StopMovingOrSizing()
        local p, _, rp, x, y = self:GetPoint()
        db.pos = { p = p, rp = rp, x = x, y = y }
    end)
    if db.pos then
        ui:SetPoint(db.pos.p, UIParent, db.pos.rp, db.pos.x, db.pos.y)
    else
        ui:SetPoint("CENTER")
    end
    tinsert(UISpecialFrames, "ProcHunterFrame") -- Escape closes

    local title = ui:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
    title:SetPoint("TOP", 0, -14)
    title:SetText("|cff33ff99ProcHunter|r — vault items with procs")

    local close = CreateFrame("Button", nil, ui, "UIPanelCloseButton")
    close:SetPoint("TOPRIGHT", -4, -4)

    local refresh = CreateFrame("Button", nil, ui, "UIPanelButtonTemplate")
    refresh:SetWidth(70); refresh:SetHeight(20)
    refresh:SetPoint("TOPLEFT", 16, -34)
    refresh:SetText("Refresh")
    refresh:SetScript("OnClick", function()
        lastRequest = 0
        TryVaultGlobal()
        Request()
    end)

    local filterLabel = ui:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    filterLabel:SetPoint("LEFT", refresh, "RIGHT", 14, 0)
    filterLabel:SetText("Filter:")

    local filter = CreateFrame("EditBox", "ProcHunterFilterBox", ui,
        "InputBoxTemplate")
    filter:SetWidth(180); filter:SetHeight(18)
    filter:SetPoint("LEFT", filterLabel, "RIGHT", 10, 0)
    filter:SetAutoFocus(false)
    filter:SetScript("OnEscapePressed", function(self) self:ClearFocus() end)
    filter:SetScript("OnEnterPressed", function(self) self:ClearFocus() end)
    filter:SetScript("OnTextChanged", function() RefreshList() end)
    ui.filter = filter

    local status = ui:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    status:SetPoint("BOTTOMLEFT", 16, 14)
    status:SetPoint("BOTTOMRIGHT", -16, 14)
    status:SetJustifyH("LEFT")
    ui.status = status

    local scroll = CreateFrame("ScrollFrame", "ProcHunterScroll", ui,
        "FauxScrollFrameTemplate")
    scroll:SetPoint("TOPLEFT", 16, -64)
    scroll:SetPoint("BOTTOMRIGHT", -36, 34)
    scroll:SetScript("OnVerticalScroll", function(self, offset)
        FauxScrollFrame_OnVerticalScroll(self, offset, ROWH, RefreshList)
    end)
    ui.scroll = scroll

    ui.rows = {}

    local function CreateRow(i)
        local r = CreateFrame("Button", nil, ui)
        r:SetHeight(ROWH)
        r:SetPoint("TOPLEFT", 18, -64 - (i - 1) * ROWH)
        r:SetPoint("RIGHT", scroll, "RIGHT", -4, 0)
        r:SetHighlightTexture("Interface\\QuestFrame\\UI-QuestTitleHighlight")
        r:RegisterForClicks("RightButtonUp")

        r.icon = r:CreateTexture(nil, "ARTWORK")
        r.icon:SetWidth(18); r.icon:SetHeight(18)
        r.icon:SetPoint("LEFT", 2, 0)

        r.ilvl = r:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
        r.ilvl:SetPoint("LEFT", r.icon, "RIGHT", 6, 0)
        r.ilvl:SetWidth(34); r.ilvl:SetJustifyH("RIGHT")

        r.name = r:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
        r.name:SetPoint("LEFT", r.ilvl, "RIGHT", 8, 0)
        r.name:SetWidth(280); r.name:SetJustifyH("LEFT")

        r.proc = r:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
        r.proc:SetPoint("LEFT", r.name, "RIGHT", 8, 0)
        r.proc:SetPoint("RIGHT", -2, 0)
        r.proc:SetJustifyH("LEFT")

        r:SetScript("OnClick", function(self, button)
            if button == "RightButton" and self.data then
                local m = self.data
                StartWithdraw(m, IsShiftKeyDown() and 1 or (m.count or 1))
            end
        end)
        r:SetScript("OnEnter", function(self)
            if self.data then RowTooltip(self.data) end
        end)
        r:SetScript("OnLeave", function() GameTooltip:Hide() end)
        r:Hide()
        ui.rows[i] = r
        return r
    end

    local function EnsureRows(n)
        for i = #ui.rows + 1, n do CreateRow(i) end
    end

    local function LayoutRows()
        local w = ui:GetWidth() or 600
        local h = ui:GetHeight() or 430
        ROWH = floor((db.fontSize or 11) + 9)
        if ROWH < 16 then ROWH = 16 end
        visRows = floor((h - 98) / ROWH)
        if visRows < 4 then visRows = 4 end
        if visRows > MAX_ROWS then visRows = MAX_ROWS end
        EnsureRows(visRows)
        local nameW = floor((w - 160) * 0.55)
        if nameW < 120 then nameW = 120 end
        local path = FONTS[db.font or 1].path
        local size = db.fontSize or 11
        for i = 1, #ui.rows do
            local r = ui.rows[i]
            r:SetHeight(ROWH)
            r:ClearAllPoints()
            r:SetPoint("TOPLEFT", 18, -64 - (i - 1) * ROWH)
            r:SetPoint("RIGHT", scroll, "RIGHT", -4, 0)
            r.name:SetWidth(nameW)
            r.ilvl:SetFont(path, size)
            r.name:SetFont(path, size)
            r.proc:SetFont(path, size)
            if i > visRows then r:Hide() end
        end
        ui.status:SetFont(path, size)
    end
    ui.LayoutRows = LayoutRows

    ApplyLook = function()
        if not ui then return end
        ui:SetAlpha(db.alpha or 1)
        LayoutRows()
        if RefreshList then RefreshList() end
    end

    -- resizable: bottom-right grip, size saved, rows recomputed live
    ui:SetResizable(true)
    ui:SetMinResize(430, 240)
    ui:SetMaxResize(1200, 900)
    if db.size then
        ui:SetWidth(db.size.w); ui:SetHeight(db.size.h)
    end
    local grip = CreateFrame("Button", nil, ui)
    grip:SetWidth(16); grip:SetHeight(16)
    grip:SetPoint("BOTTOMRIGHT", -6, 6)
    grip:SetNormalTexture("Interface\\ChatFrame\\UI-ChatIM-SizeGrabber-Up")
    grip:SetHighlightTexture("Interface\\ChatFrame\\UI-ChatIM-SizeGrabber-Down")
    grip:SetScript("OnMouseDown", function() ui:StartSizing("BOTTOMRIGHT") end)
    grip:SetScript("OnMouseUp", function()
        ui:StopMovingOrSizing()
        db.size = { w = floor(ui:GetWidth() or 600),
                    h = floor(ui:GetHeight() or 430) }
    end)
    ui:SetScript("OnSizeChanged", function()
        if ui.LayoutRows then
            ui.LayoutRows()
            if RefreshList then RefreshList() end
        end
    end)

    ApplyLook()

        -- frames are SHOWN by default on 3.3.5a: without this, the first
    -- toggle press builds the window already "shown" and instantly
    -- hides it (press silently eaten — hit live in v1.0.0)
    ui:Hide()
end

RefreshList = function()
    if not ui then return end

    for k in pairs(shown) do shown[k] = nil end
    local q = lower(ui.filter:GetText() or "")
    for i = 1, #matched do
        local m = matched[i]
        local keep = q == ""
        if not keep and find(lower(m.name or ""), q, 1, true) then keep = true end
        if not keep then
            for j = 1, #m.spells do
                local sName = GetSpellInfo(m.spells[j])
                if sName and find(lower(sName), q, 1, true) then
                    keep = true; break
                end
            end
        end
        if keep then shown[#shown + 1] = m end
    end

    FauxScrollFrame_Update(ui.scroll, #shown, visRows, ROWH)
    local offset = FauxScrollFrame_GetOffset(ui.scroll)
    for i = 1, #ui.rows do
        local r = ui.rows[i]
        local m = (i <= visRows) and shown[i + offset] or nil
        if m then
            r.data = m
            r.icon:SetTexture(GetItemIcon(m.e) or
                "Interface\\Icons\\INV_Misc_QuestionMark")
            r.ilvl:SetText(m.ilvl and ("|cff888888" .. m.ilvl .. "|r") or "")
            local cnt = (m.count and m.count > 1)
                and (" |cff888888x" .. m.count .. "|r") or ""
            r.name:SetText(QualityHex(m.q) .. (m.name or "?") .. "|r" .. cnt)
            local lines = ProcLines(m.spells)
            local names = {}
            for j = 1, #lines do names[j] = lines[j].name end
            local color = (#m.procs > 0) and "|cff33ff99" or "|cff888888"
            r.proc:SetText(color .. table.concat(names, ", ") .. "|r")
            r:Show()
        else
            r.data = nil
            r:Hide()
        end
    end

    local tail = ""
    if not snapshotSeen then
        tail = awaitingAt and "  ·  |cff80ffffreading vault...|r"
            or "  ·  |cffff8080no vault data yet — Refresh (then /ph dump if still empty)|r"
    elseif dataSource == "UncappedVault" then
        tail = "  ·  source: UncappedVault"
    end
    if db.hideFlat and flatHidden > 0 then
        tail = tail .. format("  ·  |cff888888%d flat-stat hidden|r", flatHidden)
    end
    if pendingWD then
        tail = tail .. format("  ·  |cff80ffffwithdrawing %s %d/%d (route %d)...|r",
            pendingWD.name, pendingWD.moved, pendingWD.target, pendingWD.route)
    elseif wdDoneAt then
        tail = tail .. format("  ·  |cff33ff33withdrawn: %s|r", wdDoneName or "")
    elseif wdFailed then
        tail = tail .. "  ·  |cffff8080withdraw refused or ignored — send me UncappedVault.lua to pin the route|r"
    end
    ui.status:SetText(format(
        "%d in vault  ·  %d equippable  ·  |cff33ff99%d with procs|r  ·  showing %d%s%s",
        #vault, eqCount, procCount, #shown,
        pendingN > 0
            and format("  ·  |cff80ffff%d waiting on item cache|r", pendingN)
            or "",
        tail))
end

--========================= minimap button ============================
local function PlaceMinimapButton()
    if not mmBtn then return end
    mmBtn:ClearAllPoints()
    local p = db.mm or { x = -60, y = -35 }
    mmBtn:SetPoint("CENTER", Minimap, "CENTER", p.x, p.y)
end

local function BuildMinimapButton()
    if mmBtn or not Minimap then return end
    mmBtn = CreateFrame("Button", "ProcHunterMinimapButton", Minimap)
    mmBtn:SetWidth(31); mmBtn:SetHeight(31)
    mmBtn:SetFrameStrata("MEDIUM"); mmBtn:SetFrameLevel(8)
    mmBtn:RegisterForClicks("LeftButtonUp")
    mmBtn:SetHighlightTexture("Interface\\Minimap\\UI-Minimap-ZoomButton-Highlight")

    local overlay = mmBtn:CreateTexture(nil, "OVERLAY")
    overlay:SetWidth(53); overlay:SetHeight(53)
    overlay:SetTexture("Interface\\Minimap\\MiniMap-TrackingBorder")
    overlay:SetPoint("TOPLEFT", 0, 0)

    local icon = mmBtn:CreateTexture(nil, "BACKGROUND")
    icon:SetWidth(17); icon:SetHeight(17)
    icon:SetTexture("Interface\\Icons\\INV_Misc_Spyglass_03")
    icon:SetTexCoord(0.05, 0.95, 0.05, 0.95)
    icon:SetPoint("TOPLEFT", 7, -6)

    mmBtn:SetMovable(true)
    mmBtn:RegisterForDrag("LeftButton")
    mmBtn:SetScript("OnDragStart", function(self) self:StartMoving() end)
    mmBtn:SetScript("OnDragStop", function(self)
        self:StopMovingOrSizing()
        local mx, my = Minimap:GetCenter()
        local bx, by = self:GetCenter()
        if mx and bx then
            db.mm = { x = bx - mx, y = by - my }
        end
        PlaceMinimapButton()
    end)
    mmBtn:SetScript("OnClick", function()
        SlashCmdList["PROCHUNTER"]("")
    end)
    mmBtn:SetScript("OnEnter", function(self)
        GameTooltip:SetOwner(self, "ANCHOR_LEFT")
        GameTooltip:AddLine("ProcHunter", 0.2, 1, 0.6)
        GameTooltip:AddLine("Click: open the vault proc list", 1, 1, 1)
        GameTooltip:AddLine("Drag: move this button", 0.7, 0.7, 0.7)
        GameTooltip:Show()
    end)
    mmBtn:SetScript("OnLeave", function() GameTooltip:Hide() end)

    PlaceMinimapButton()
    if db.hideMinimap then mmBtn:Hide() end
end

--========================= options panel =============================
local function BuildOptions()
    local p = CreateFrame("Frame", "ProcHunterOptionsPanel", UIParent)
    p.name = "ProcHunter"
    p:Hide()

    local t = p:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
    t:SetPoint("TOPLEFT", 16, -16)
    t:SetText("|cff33ff99ProcHunter|r")

    local d = p:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    d:SetPoint("TOPLEFT", t, "BOTTOMLEFT", 0, -6)
    d:SetPoint("RIGHT", -20, 0)
    d:SetJustifyH("LEFT")
    d:SetText("Scans your Uncapped Vault and lists every equippable item " ..
        "that carries a proc. Right-click a row to withdraw it. " ..
        "v" .. VERSION)

    local open = CreateFrame("Button", nil, p, "UIPanelButtonTemplate")
    open:SetWidth(140); open:SetHeight(22)
    open:SetPoint("TOPLEFT", d, "BOTTOMLEFT", 0, -14)
    open:SetText("Open ProcHunter")
    open:SetScript("OnClick", function() SlashCmdList["PROCHUNTER"]("") end)

    local cb = CreateFrame("CheckButton", "ProcHunterMMCheck", p,
        "UICheckButtonTemplate")
    cb:SetPoint("TOPLEFT", open, "BOTTOMLEFT", -4, -14)
    _G["ProcHunterMMCheckText"]:SetText("Show minimap button")
    cb:SetChecked(not db.hideMinimap)
    cb:SetScript("OnClick", function(self)
        db.hideMinimap = not self:GetChecked() and true or nil
        if mmBtn then
            if db.hideMinimap then mmBtn:Hide() else mmBtn:Show() end
        end
    end)

    local cf = CreateFrame("CheckButton", "ProcHunterFlatCheck", p,
        "UICheckButtonTemplate")
    cf:SetPoint("TOPLEFT", cb, "BOTTOMLEFT", 0, -6)
    _G["ProcHunterFlatCheckText"]:SetText(
        "Hide items whose only effect is a flat stat bonus (e.g. +24 Intellect)")
    cf:SetChecked(db.hideFlat and true or false)
    cf:SetScript("OnClick", function(self)
        db.hideFlat = self:GetChecked() and true or false
        Rebuild()
    end)

    local function MakeSlider(sname, label, minV, maxV, step, getV, setV, anchor, dy)
        local sl = CreateFrame("Slider", sname, p, "OptionsSliderTemplate")
        sl:SetWidth(190)
        sl:SetPoint("TOPLEFT", anchor, "BOTTOMLEFT", 4, dy)
        sl:SetMinMaxValues(minV, maxV)
        sl:SetValueStep(step)
        _G[sname .. "Low"]:SetText(tostring(minV))
        _G[sname .. "High"]:SetText(tostring(maxV))
        _G[sname .. "Text"]:SetText(label .. ": " .. floor(getV() + 0.5))
        sl._loading = true
        sl:SetValue(getV())
        sl._loading = false
        sl:SetScript("OnValueChanged", function(self, v)
            if self._loading then return end
            v = floor((v or 0) + 0.5)
            _G[sname .. "Text"]:SetText(label .. ": " .. v)
            setV(v)
        end)
        return sl
    end

    local opSlider = MakeSlider("ProcHunterOpacitySlider", "Window opacity %",
        20, 100, 5,
        function() return (db.alpha or 1) * 100 end,
        function(v)
            db.alpha = v / 100
            if ui then ui:SetAlpha(db.alpha) end
        end, cf, -28)

    local fsSlider = MakeSlider("ProcHunterFontSizeSlider", "Font size",
        8, 18, 1,
        function() return db.fontSize or 11 end,
        function(v)
            db.fontSize = v
            if ApplyLook then ApplyLook() end
        end, opSlider, -28)

    local fontBtn = CreateFrame("Button", nil, p, "UIPanelButtonTemplate")
    fontBtn:SetWidth(190); fontBtn:SetHeight(22)
    fontBtn:SetPoint("TOPLEFT", fsSlider, "BOTTOMLEFT", -4, -16)
    fontBtn:SetText("Font: " .. FONTS[db.font or 1].name)
    fontBtn:SetScript("OnClick", function(self)
        db.font = ((db.font or 1) % #FONTS) + 1
        self:SetText("Font: " .. FONTS[db.font].name)
        if ApplyLook then ApplyLook() end
    end)

    local h = p:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    h:SetPoint("TOPLEFT", fontBtn, "BOTTOMLEFT", 4, -14)
    h:SetPoint("RIGHT", -20, 0)
    h:SetJustifyH("LEFT")
    h:SetText("Slash commands: |cffffd100/ph|r toggle window  ·  " ..
        "|cffffd100/ph debug|r print wire traffic  ·  " ..
        "|cffffd100/ph dump|r describe UncappedVault's data")

    InterfaceOptions_AddCategory(p)
end

--========================= toggle / slash ============================
local function Toggle()
    BuildUI()
    if ui:IsShown() then
        ui:Hide()
    else
        ui:Show()
        TryVaultGlobal()   -- instant fill from the confirmed data path
        RefreshList()
        Request()          -- wire attempt underneath, in case it ever lives
    end
end

SLASH_PROCHUNTER1 = "/prochunter"
SLASH_PROCHUNTER2 = "/ph"
SlashCmdList["PROCHUNTER"] = function(cmd)
    cmd = lower(cmd or "")
    cmd = match(cmd, "^%s*(.-)%s*$") or ""
    if cmd == "debug" then
        wireDebug = not wireDebug
        Msg("wire debug " .. (wireDebug and "ON — printing all addon messages"
            or "off"))
    elseif cmd == "dump" then
        DumpVault()
    else
        Toggle()
    end
end

--========================= init ======================================
local init = CreateFrame("Frame")
init:RegisterEvent("ADDON_LOADED")
init:RegisterEvent("PLAYER_LOGIN")
init:SetScript("OnEvent", function(_, event, arg1)
    if event == "ADDON_LOADED" and arg1 == ADDON then
        ProcHunterDB = ProcHunterDB or {}
        db = ProcHunterDB
        if db.hideFlat == nil then db.hideFlat = true end
        if db.fontSize == nil then db.fontSize = 11 end
        if db.alpha == nil then db.alpha = 1 end
        if db.font == nil then db.font = 1 end
        BuildOptions()
    elseif event == "PLAYER_LOGIN" then
        BuildMinimapButton()
        Stamp()
    end
end)
