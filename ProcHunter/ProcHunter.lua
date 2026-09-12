--=====================================================================
-- ProcHunter v1.6.1 — Uncapped Vault proc scanner
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
-- WITHDRAW (pinned from the dissected UncappedVault.lua, 2026-09-11):
-- Core.Withdraw(itemRowTable, count) — the row's own table from
-- Core.items (fields .e/.rp/.c), count clamped to the stack and sent
-- as text (%.0f, server parses uint64). Route 1 finds the live row
-- and calls it properly; routes 2 (Core.Send with the raw verb) and
-- 3 (raw SendAddonMessage) remain as fallbacks. The verify loop is
-- kept as a bag-space safety net: delta is measured after each call
-- and partial deliveries report "N of M (stopped)".
--
-- EXTRACT FLOW (Ctrl+Right-click): withdraw one copy -> identify the
-- exact bag slot it landed in (bag snapshot diff: only the slot that
-- APPEARED can ever be destroyed — a pre-existing, possibly imprinted
-- copy never is) -> ICEXSRC+ICINV asked; either dialect locates
-- spell+trigger (ICEXI..ICEXIEND, or ICITEM:B + ICIPROC..ICINVEND) ->
-- named consent dialog ("This DESTROYS the withdrawn copy") ->
-- ICUNLOCK:<bag>:<slot>:<spell>:<trigger> -> ICUNLOCKED flips the
-- tick live. Free on this realm (scrolls retired). Every stage has a
-- timeout that aborts loudly with nothing destroyed; the dialog only
-- allows procs not already unlocked; the slot is re-verified at the
-- moment of confirm and any drift aborts.
--
-- EXTRACTION TICK: ProcHunter requests the account's unlocked-proc
-- collection itself (ICCOLL -> ICCOLLROW:<spell>:<trigger>:<src> ...
-- ICCOLLEND, still ordinary UNC addon messages) and shows a green
-- tick left of the name when every proc NAME on the item is already
-- unlocked, a dimmed yellow tick when only some are. Wardrobe
-- streams triggered by other addons are absorbed for free.
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
local VERSION = "1.6.1"
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
local WD_MAX_ROUTE     = 3
local COLL_COOLDOWN    = 60    -- min seconds between ICCOLL requests
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
local amtDlg                -- withdraw-amount dialog (lazy)
local collSet      = nil    -- spellId -> true (account's unlocked procs)
local exFlow       = nil    -- in-flight extract {stage,e,rp,name,snap,bag,slot,rows,chosen,at}
local exDlg                 -- extract consent dialog (lazy)
local exDoneAt, exDoneName  -- success flash
local runAll       = nil    -- Extract All run {queue,idx,tries,learned,skipped,wait,stopping}
local exFailMsg    = nil    -- sticky abort reason
local collStaging  = nil
local lastCollReq  = 0

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

-- server rule: teleport procs can never be extracted. That includes
-- portal creators (Atiesh). Judged by either word appearing in the
-- spell's name or tooltip text.
local teleCache = {}
local function TeleText(t)
    t = lower(t)
    return find(t, "teleport") or find(t, "portal")
end
local function IsTeleportSpell(id)
    local c = teleCache[id]
    if c ~= nil then return c end
    local nm = GetSpellInfo(id)
    c = (nm and TeleText(nm)) and true or false
    if not c then
        local tip = GetScanTip()
        tip:ClearLines()
        tip:SetHyperlink("spell:" .. id)
        for i = 1, tip:NumLines() or 0 do
            local fs = _G["ProcHunterScanTipTextLeft" .. i]
            local t = fs and fs:GetText()
            if t and TeleText(t) then c = true break end
        end
    end
    teleCache[id] = c
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
                        -- extraction status, judged per unique proc NAME
                        -- (rank variants share a name; owning any rank
                        -- counts that name as unlocked)
                        local extN, extT = 0, 0
                        if collSet and #procs > 0 then
                            local byName = {}
                            for j = 1, #procs do
                                local id = procs[j]
                                -- teleport procs are unextractable by
                                -- server rule: they never count toward
                                -- the tick, or items could not complete
                                if not IsTeleportSpell(id) then
                                    local nm = GetSpellInfo(id) or ("#" .. id)
                                    local slot = byName[nm]
                                    if slot == nil then
                                        slot = false
                                        extT = extT + 1
                                    end
                                    if collSet[id] then slot = true end
                                    byName[nm] = slot
                                end
                            end
                            for _, got in pairs(byName) do
                                if got then extN = extN + 1 end
                            end
                        end
                        matched[#matched + 1] = {
                            e = row.e, rp = row.rp, count = row.count,
                            q = row.q, ilvl = row.ilvl,
                            name = dispName, link = link,
                            procs = procs, flats = flats,
                            spells = (#procs > 0) and procs or flats,
                            extN = extN, extT = extT,
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

local function RequestCollection()
    local now = GetTime()
    if now - lastCollReq < COLL_COOLDOWN then return end
    lastCollReq = now
    SendAddonMessage(SEND_PREFIX, "ICCOLL", "WHISPER", UnitName("player"))
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
    Msg("dump: ProcHunter v" .. VERSION)
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

local function FindUVRow(e, rp)
    local UV = _G.UncappedVault
    local src = UV and type(UV) == "table" and UV.items
    if type(src) ~= "table" then return nil end
    for i = 1, #src do
        local r = src[i]
        if type(r) == "table" and tonumber(r.e) == e
            and (tonumber(r.rp) or 0) == (rp or 0) then
            return r
        end
    end
end

-- Route 1 is the PINNED call from the dissected source:
-- Core.Withdraw(itemRowTable, count) — the row's own table, count
-- clamped server-addon-side to the stack. Routes 2/3 are fallbacks.
-- Count travels as %.0f per kirei's DE-03 note (server parses the
-- field as text; %.0f is exact where %d can wrap).
local function TryRoute(w, L)
    local UV = _G.UncappedVault
    local rem = w.target - w.moved
    if rem < 1 then rem = 1 end
    local verb = format("VLTWD:%d:%d:%s", w.e, w.rp or 0,
        format("%.0f", rem))
    if L == 1 and UV and type(UV.Withdraw) == "function" then
        local row = FindUVRow(w.e, w.rp)
        if row then
            return pcall(UV.Withdraw, row, rem) and true or false
        end
        return false
    elseif L == 2 and UV and type(UV.Send) == "function" then
        return pcall(UV.Send, verb) and true or false
    elseif L == 3 then
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

--========================= extract flow ==============================
local function BagEntry(bag, slot)
    local link = GetContainerItemLink(bag, slot)
    return link and tonumber(match(link, "item:(%d+)")) or 0
end

local function CountBagCopies(e)
    local n = 0
    for bag = 0, 4 do
        local sn = GetContainerNumSlots(bag) or 0
        for slot = 1, sn do
            if BagEntry(bag, slot) == e then n = n + 1 end
        end
    end
    return n
end

local function SnapshotBags()
    local snap = {}
    for bag = 0, 4 do
        local n = GetContainerNumSlots(bag) or 0
        for slot = 1, n do
            snap[bag .. ":" .. slot] = BagEntry(bag, slot)
        end
    end
    return snap
end

-- Only a slot that newly GAINED the entry qualifies: a pre-existing
-- (possibly imprinted) copy must never be the one destroyed.
local function FindNewCopy(snap, e)
    for bag = 0, 4 do
        local n = GetContainerNumSlots(bag) or 0
        for slot = 1, n do
            if BagEntry(bag, slot) == e
                and snap[bag .. ":" .. slot] ~= e then
                return bag, slot
            end
        end
    end
end

-- The live realm PUSHES the ICINV stream the instant the withdrawn
-- copy lands — before the bag diff has even pinned the slot. So every
-- proc row is cached per bag:slot bucket for the whole life of the
-- flow, whatever the stage; once the slot is pinned, a cache hit goes
-- straight to the dialog and no request is ever needed. Old-pack
-- realms that answer our explicit request still work: their rows land
-- in the same buckets and resolve at ICEXIEND/ICINVEND.
local function AddExRow(w, key, sp, tr)
    tr = tr or 0
    w.cache = w.cache or {}
    local b = w.cache[key]
    if not b then b = {} w.cache[key] = b end
    local k = sp .. ":" .. tr
    if b[k] then return end -- dedupe (dual-dialect realms)
    b[k] = true
    b[#b + 1] = { spell = sp, trigger = tr }
end

-- terminal for the locate stage: resolve the pinned bucket.
-- Returns true on success, or nil + reason ("none"/"dupes").
-- The server may number bags/slots DIFFERENTLY than the client
-- (confirmed live: pinned client bag:slot never matched a pushed
-- ICITEM:B header). So: exact key first, then fall back to the one
-- bucket whose proc NAMES match the item's own procs from the DB —
-- accepted only while the item exists in bags exactly once, because
-- only then can that bucket BE the fresh copy and nothing else.
-- ICUNLOCK later echoes the bucket's own coords back (srvKey): the
-- server understands its own numbering, whatever it is.
local function ResolveExRows(w)
    if not w.cache then return nil, "none" end
    local key = w.bag .. ":" .. w.slot
    local b = w.cache[key]
    if b and #b > 0 then
        w.srvKey, w.rows = key, b
        return true
    end
    local cand, candKey, n = nil, nil, 0
    for k, bk in pairs(w.cache) do
        if #bk > 0 then
            for i = 1, #bk do
                local nm = GetSpellInfo(bk[i].spell)
                if nm and w.expect and w.expect[lower(nm)] then
                    n = n + 1
                    cand, candKey = bk, k
                    break
                end
            end
        end
    end
    if n == 1 and CountBagCopies(w.e) == 1 then
        w.srvKey, w.rows = candKey, cand
        return true
    elseif n >= 1 then
        -- several matching buckets, or bag duplicates of the item:
        -- the fresh copy cannot be told apart with certainty, and a
        -- pre-existing (possibly imprinted) copy must NEVER be at risk
        return nil, "dupes"
    end
    return nil, "none"
end

local function AbortExtract(reason, keep)
    local w = exFlow
    exFlow = nil
    exFailMsg = reason
    if not keep and w and w.bag and BagEntry(w.bag, w.slot) == w.e then
        -- an unextractable copy goes STRAIGHT back to the vault.
        -- Client coords: the pinned slot is client-side truth, and
        -- VLTDEP is the same client-coord pair the pack's own
        -- drag-to-deposit sends.
        SendAddonMessage(SEND_PREFIX, format("VLTDEP:%d:%d",
            w.bag, w.slot), "WHISPER", UnitName("player"))
        exFailMsg = reason .. " — copy returned to the vault"
    end
    if runAll and runAll.idx <= #runAll.queue then
        -- unattended run: an aborted flow skips the item, never halts
        local q = runAll.queue[runAll.idx]
        runAll.skipped[q.name] = reason
        runAll.idx = runAll.idx + 1
        runAll.tries = 0
        runAll.wait = GetTime() + 2.5
    end
    if exDlg then exDlg:Hide() end
    if RefreshList then RefreshList() end
end

local ShowExtractDialog -- forward (defined with the UI section below)

local function StartExtract(m)
    if pendingWD or exFlow then return end
    exFailMsg, exDoneAt, exDoneName = nil, nil, nil
    local exp = {}
    local sl = m.spells or m.procs or {}
    for i = 1, #sl do
        local nm = GetSpellInfo(sl[i])
        if nm then exp[lower(nm)] = true end
    end
    exFlow = {
        stage = "withdraw", e = m.e, rp = m.rp or 0,
        name = m.name or "?", q = m.q, expect = exp,
        snap = SnapshotBags(), at = GetTime(),
    }
    StartWithdraw(m, 1)
    if not pendingWD then -- withdraw could not even start
        AbortExtract("withdrawal could not start")
    end
end

local function ConfirmExtract()
    local w = exFlow
    if not w or not w.chosen then return end
    if exDlg then exDlg:Hide() end
    -- the slot is re-verified at the moment of truth; any drift aborts
    if BagEntry(w.bag, w.slot) ~= w.e then
        AbortExtract("the bag slot changed — nothing destroyed")
        return
    end
    w.stage = "unlock"
    w.at = GetTime()
    -- echo the server's OWN coords for the copy (srvKey from the
    -- stream); its numbering can differ from the client's
    local sb, ss = match(w.srvKey or (w.bag .. ":" .. w.slot),
        "^(%d+):(%d+)$")
    SendAddonMessage(SEND_PREFIX, format("ICUNLOCK:%s:%s:%d:%d",
        sb, ss, w.chosen.spell, w.chosen.trigger or 0),
        "WHISPER", UnitName("player"))
    if RefreshList then RefreshList() end
end

--======================== extract all runner =========================
-- one consent up front, then unattended: per item -> withdraw one
-- copy -> auto-pick the first locked, non-teleport proc -> unlock ->
-- repeat until the item is fully green -> next item. Any failed flow
-- skips the item (reported at the end) and never halts the run.
local function LockedExtractable(m)
    local ids = m.procs or {}
    local byName = {}
    for i = 1, #ids do
        local id = ids[i]
        if not IsTeleportSpell(id) then
            local nm = lower(GetSpellInfo(id) or ("#" .. id))
            if byName[nm] == nil then byName[nm] = false end
            if collSet and collSet[id] then byName[nm] = true end
        end
    end
    local n = 0
    for _, got in pairs(byName) do if not got then n = n + 1 end end
    return n
end

local function FinishRunAll(word)
    local r = runAll
    runAll = nil
    if ui and ui.extractAll then ui.extractAll:SetText("Extract All") end
    Msg(format("extract all %s — %d proc%s learned",
        word, r.learned, r.learned == 1 and "" or "s"))
    for name, why in pairs(r.skipped) do
        Msg("  skipped " .. name .. ": " .. why)
    end
    if RefreshList then RefreshList() end
end

local function RunAllSkip(name, why)
    runAll.skipped[name] = why
    runAll.idx = runAll.idx + 1
    runAll.tries = 0
    runAll.wait = GetTime() + 2.5
end

local function RunAllTick(now)
    local r = runAll
    if not r then return end
    if exFlow or pendingWD then return end -- a flow is in the air
    if now < r.wait then return end
    if r.stopping then return FinishRunAll("stopped") end
    if r.idx > #r.queue then return FinishRunAll("finished") end
    local q = r.queue[r.idx]
    local m
    for i = 1, #matched do
        local c = matched[i]
        if c.e == q.e and (c.rp or 0) == (q.rp or 0) then m = c break end
    end
    if not m then return RunAllSkip(q.name, "no longer in the vault") end
    local locked = LockedExtractable(m)
    if locked == 0 then -- fully learned: next item
        r.idx = r.idx + 1
        r.tries = 0
        return
    end
    if CountBagCopies(m.e) > 0 then
        return RunAllSkip(m.name,
            "copies already in your bags — deposit them, then rerun")
    end
    if (m.count or 0) < 1 then
        return RunAllSkip(m.name, "no copies left in the vault")
    end
    r.tries = r.tries + 1
    if r.tries > locked + 2 then
        return RunAllSkip(m.name,
            "did not converge — unlocks not registering")
    end
    r.current = m.name
    StartExtract(m)
    if not exFlow then
        RunAllSkip(m.name, exFailMsg or "flow could not start")
    end
end

local function StartRunAll()
    if runAll then return end
    local queue = {}
    for i = 1, #matched do
        local m = matched[i]
        if LockedExtractable(m) > 0 then
            queue[#queue + 1] = { e = m.e, rp = m.rp, name = m.name }
        end
    end
    if #queue == 0 then
        Msg("extract all: nothing to learn — every extractable proc is already unlocked")
        return
    end
    runAll = { queue = queue, idx = 1, tries = 0, learned = 0,
        skipped = {}, wait = 0 }
    if ui and ui.extractAll then ui.extractAll:SetText("Stop") end
    Msg(format("extract all: %d item%s to work through",
        #queue, #queue == 1 and "" or "s"))
end

StaticPopupDialogs["PROCHUNTER_EXTRACTALL"] = {
    text = "Extract ALL missing procs?\n\nThis withdraws and DESTROYS " ..
        "one vault copy per proc learned, item after item, until " ..
        "everything extractable is unlocked. Teleport procs are " ..
        "skipped (server rule).",
    button1 = "Run it",
    button2 = "Cancel",
    OnAccept = StartRunAll,
    timeout = 0, whileDead = 1, hideOnEscape = 1,
}

local function ExtractTick(now)
    RunAllTick(now)
    local w = exFlow
    if not w then
        if exDoneAt and now - exDoneAt > 5 then
            exDoneAt, exDoneName = nil, nil
            if RefreshList then RefreshList() end
        end
        return
    end
    if w.stage == "withdraw" then
        local bag, slot = FindNewCopy(w.snap, w.e)
        if bag then
            w.bag, w.slot = bag, slot
            if ResolveExRows(w) then
                -- the realm already pushed this copy's procs while the
                -- bag diff was still running — no request needed
                w.stage = "dialog"
                w.at = now
                if ShowExtractDialog then ShowExtractDialog() end
            else
                w.stage = "locate"
                w.at = now
                -- both dialects requested; whichever the realm speaks,
                -- we hear. Old pack answers ICEXSRC with ICEXI rows;
                -- some realms only push ICINV on an explicit ask.
                SendAddonMessage(SEND_PREFIX, "ICEXSRC", "WHISPER",
                    UnitName("player"))
                SendAddonMessage(SEND_PREFIX, "ICINV", "WHISPER",
                    UnitName("player"))
            end
        elseif now - w.at > 8 then
            AbortExtract("the withdrawn copy never reached your bags")
        end
    elseif w.stage == "locate" then
        if now - w.at > 6 then
            local hit, why = ResolveExRows(w)
            if hit then
                -- rows arrived but the END line never did — use them
                w.stage = "dialog"
                w.at = now
                if ShowExtractDialog then ShowExtractDialog() end
            elseif why == "dupes" then
                AbortExtract("several copies of this item are in your bags — keep exactly ONE, then retry")
            else
                AbortExtract("no answer from the extraction picker")
            end
        end
    elseif w.stage == "unlock" then
        if now - w.at > 6 then
            AbortExtract("unlock not confirmed — check the Wardrobe before retrying")
        end
    end
end

-- Shift+Right-click: ask for an amount. Right-click alone withdraws
-- exactly ONE — on a vault with 17k-item stacks, bulk must never
-- happen by accident (learned the hard way in v1.3.0).
local function ShowAmountDialog(m)
    if pendingWD then return end
    if not amtDlg then
        amtDlg = CreateFrame("Frame", "ProcHunterAmountDialog", UIParent)
        amtDlg:SetWidth(260); amtDlg:SetHeight(120)
        amtDlg:SetPoint("CENTER")
        amtDlg:SetFrameStrata("DIALOG")
        amtDlg:SetBackdrop({
            bgFile = "Interface\\Buttons\\WHITE8X8",
            edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
            tile = false, edgeSize = 32,
            insets = { left = 8, right = 8, top = 8, bottom = 8 },
        })
        amtDlg:SetBackdropColor(0.07, 0.07, 0.09, 1)
        amtDlg:EnableMouse(true)

        amtDlg.title = amtDlg:CreateFontString(nil, "OVERLAY", "GameFontNormal")
        amtDlg.title:SetPoint("TOP", 0, -16)
        amtDlg.title:SetPoint("LEFT", 12, 0)
        amtDlg.title:SetPoint("RIGHT", -12, 0)

        amtDlg.have = amtDlg:CreateFontString(nil, "OVERLAY",
            "GameFontHighlightSmall")
        amtDlg.have:SetPoint("TOP", amtDlg.title, "BOTTOM", 0, -4)

        amtDlg.edit = CreateFrame("EditBox", "ProcHunterAmountEdit", amtDlg,
            "InputBoxTemplate")
        amtDlg.edit:SetWidth(80); amtDlg.edit:SetHeight(20)
        amtDlg.edit:SetPoint("TOP", amtDlg.have, "BOTTOM", 0, -8)
        amtDlg.edit:SetNumeric(1)
        amtDlg.edit:SetMaxLetters(6)
        amtDlg.edit:SetAutoFocus(true)

        local function Accept()
            local it = amtDlg.item
            local n = tonumber(amtDlg.edit:GetText() or "")
            amtDlg:Hide()
            if not it then return end
            -- re-resolve the row: the list is live and may have moved
            local fresh
            for i = 1, #matched do
                if matched[i].e == it.e
                    and (matched[i].rp or 0) == (it.rp or 0) then
                    fresh = matched[i]; break
                end
            end
            if not fresh then return end -- left the vault meanwhile
            n = floor(n or 1)
            if n < 1 then n = 1 end
            local cap = fresh.count or 1
            if n > cap then n = cap end
            StartWithdraw(fresh, n)
        end

        amtDlg.okBtn = CreateFrame("Button", nil, amtDlg,
            "UIPanelButtonTemplate")
        amtDlg.okBtn:SetWidth(100); amtDlg.okBtn:SetHeight(22)
        amtDlg.okBtn:SetPoint("BOTTOMLEFT", 16, 14)
        amtDlg.okBtn:SetText("Withdraw")
        amtDlg.okBtn:SetScript("OnClick", Accept)

        amtDlg.cancelBtn = CreateFrame("Button", nil, amtDlg,
            "UIPanelButtonTemplate")
        amtDlg.cancelBtn:SetWidth(100); amtDlg.cancelBtn:SetHeight(22)
        amtDlg.cancelBtn:SetPoint("BOTTOMRIGHT", -16, 14)
        amtDlg.cancelBtn:SetText("Cancel")
        amtDlg.cancelBtn:SetScript("OnClick", function() amtDlg:Hide() end)

        amtDlg.edit:SetScript("OnEnterPressed", Accept)
        amtDlg.edit:SetScript("OnEscapePressed", function() amtDlg:Hide() end)

        amtDlg:Hide() -- shown-by-default rule
    end
    amtDlg.item = m
    amtDlg.title:SetText("Withdraw: " .. (m.name or "?"))
    amtDlg.have:SetText(format("in vault: %d", m.count or 1))
    amtDlg.edit:SetText("1")
    amtDlg.edit:HighlightText()
    amtDlg:Show()
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
    elseif find(msg, "^ICEXI:") then
        -- old-pack dialect. Cached at ANY stage; filtered by entry
        -- (bag/slot re-checked at resolve time via the bucket key)
        if exFlow then
            local b, sl, en, eq, sp, tr = match(msg,
                "^ICEXI:(%d+):(%d+):(%d+):(%d+):(%d+):(%d+)$")
            if b and tonumber(en) == exFlow.e and tonumber(sp) > 0 then
                AddExRow(exFlow, tonumber(b) .. ":" .. tonumber(sl),
                    tonumber(sp), tonumber(tr))
            end
        end
    elseif find(msg, "^ICITEM:") then
        -- live-realm ICINV dialect: an ICITEM header announces which
        -- item the ICIPROC rows that follow belong to. Only B (bag)
        -- headers open a bucket; equipped-gear headers close it. The
        -- stream is cached at ANY stage — the realm pushes it the
        -- moment the copy lands, before the slot is even pinned.
        if exFlow then
            local b, sl = match(msg, "^ICITEM:B:(%d+):(%d+)")
            exFlow.curKey = b and (tonumber(b) .. ":" .. tonumber(sl))
                or nil
        end
    elseif find(msg, "^ICIPROC:") then
        -- ICIPROCBP/ICIPROCFACT/ICIPROCSRC lack the colon there: no match
        if exFlow and exFlow.curKey then
            local sp, tr = match(msg, "^ICIPROC:(%d+):(%d+)")
            if sp and tonumber(sp) > 0 then
                AddExRow(exFlow, exFlow.curKey,
                    tonumber(sp), tonumber(tr))
            end
        end
    elseif find(msg, "^ICEXIEND") or find(msg, "^ICINVEND") then
        if exFlow then
            exFlow.curKey = nil
            -- terminal only for the locate stage. An END arriving
            -- during withdraw just closes the pushed cache — never
            -- an abort (the slot is not even pinned yet).
            if exFlow.stage == "locate" then
                local hit, why = ResolveExRows(exFlow)
                if hit then
                    exFlow.stage = "dialog"
                    exFlow.at = GetTime()
                    if ShowExtractDialog then ShowExtractDialog() end
                elseif why == "dupes" then
                    AbortExtract("several copies of this item are in your bags — keep exactly ONE, then retry")
                else
                    AbortExtract("the server reports no extractable proc on this copy")
                end
            end
        end
    elseif find(msg, "^ICUNLOCKED:") then
        local sp = tonumber(match(msg, "^ICUNLOCKED:(%d+)"))
        if sp then
            collSet = collSet or {}
            collSet[sp] = true
            if exFlow and exFlow.stage == "unlock"
                and exFlow.chosen and exFlow.chosen.spell == sp then
                exDoneAt = GetTime()
                exDoneName = GetSpellInfo(sp) or ("#" .. sp)
                exFlow = nil
                if runAll then
                    runAll.learned = runAll.learned + 1
                    runAll.wait = GetTime() + 2.5 -- server throttle pacing
                end
            end
            Rebuild() -- Dashboard unlocks absorbed too: ticks stay live
        end
    elseif find(msg, "^ICERR:") then
        if exFlow then
            AbortExtract("server refused: " ..
                (match(msg, "^ICERR:[^:]*:(.*)$") or msg))
        end
    elseif find(msg, "^ICCOLLROW:") then
        local sp = match(msg, "^ICCOLLROW:(%d+):")
        if sp then
            collStaging = collStaging or {}
            collStaging[tonumber(sp)] = true
        end
    elseif find(msg, "^ICCOLLEND") then
        if collStaging then
            collSet = collStaging
            collStaging = nil
            Rebuild()
        end
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
    ExtractTick(now)
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
    if not collSet then
        GameTooltip:AddLine("Extraction data not received yet", 0.6, 0.6, 0.6)
    elseif row.extT and row.extT > 0 and row.extN >= row.extT then
        GameTooltip:AddLine("Extracted: all procs already unlocked", 0.2, 1, 0.4)
    elseif row.extN and row.extN > 0 then
        GameTooltip:AddLine(format("Extracted: %d of %d procs unlocked",
            row.extN, row.extT), 1, 0.85, 0.15)
    else
        GameTooltip:AddLine("Extracted: none yet", 0.6, 0.6, 0.6)
    end
    GameTooltip:AddLine("Right-click: withdraw ONE to bags", 0.7, 0.7, 0.7)
    GameTooltip:AddLine("Shift+Right-click: withdraw an amount...", 0.7, 0.7, 0.7)
    GameTooltip:AddLine("Ctrl+Right-click: extract a proc (destroys one copy)",
        0.7, 0.7, 0.7)
    GameTooltip:Show()
end

local function BuildUI()
    if ui then return end
    ui = CreateFrame("Frame", "ProcHunterFrame", UIParent)
    ui:SetWidth(600); ui:SetHeight(430)
    ui:SetFrameStrata("HIGH")
    ui:SetBackdrop({
        bgFile = "Interface\\Buttons\\WHITE8X8", -- solid: the stock
        -- parchment texture has transparency baked into the artwork
        edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
        tile = false, edgeSize = 32,
        insets = { left = 8, right = 8, top = 8, bottom = 8 },
    })
    ui:SetBackdropColor(0.07, 0.07, 0.09, 1)
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
    title:SetText("|cff33ff99ProcHunter|r v" .. VERSION .. " — vault items with procs")

    local close = CreateFrame("Button", nil, ui, "UIPanelCloseButton")
    close:SetPoint("TOPRIGHT", -4, -4)

    local refresh = CreateFrame("Button", nil, ui, "UIPanelButtonTemplate")
    refresh:SetWidth(70); refresh:SetHeight(20)
    refresh:SetPoint("TOPLEFT", 16, -34)
    refresh:SetText("Refresh")
    refresh:SetScript("OnClick", function()
        lastRequest = 0
        lastCollReq = 0
        TryVaultGlobal()
        Request()
        RequestCollection()
    end)

    local exAll = CreateFrame("Button", nil, ui, "UIPanelButtonTemplate")
    exAll:SetWidth(90); exAll:SetHeight(20)
    exAll:SetPoint("LEFT", refresh, "RIGHT", 6, 0)
    exAll:SetText("Extract All")
    exAll:SetScript("OnClick", function()
        if runAll then
            runAll.stopping = true
            Msg("extract all: stopping after the current item...")
        else
            StaticPopup_Show("PROCHUNTER_EXTRACTALL")
        end
    end)
    ui.extractAll = exAll

    local filterLabel = ui:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
    filterLabel:SetPoint("LEFT", exAll, "RIGHT", 14, 0)
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

        r.tick = r:CreateTexture(nil, "ARTWORK")
        r.tick:SetWidth(14); r.tick:SetHeight(14)
        r.tick:SetPoint("LEFT", r.ilvl, "RIGHT", 4, 0)
        r.tick:SetTexture("Interface\\RaidFrame\\ReadyCheck-Ready")
        r.tick:Hide()

        r.name = r:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
        r.name:SetPoint("LEFT", r.tick, "RIGHT", 4, 0)
        r.name:SetWidth(280); r.name:SetJustifyH("LEFT")

        r.proc = r:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
        r.proc:SetPoint("LEFT", r.name, "RIGHT", 8, 0)
        r.proc:SetPoint("RIGHT", -2, 0)
        r.proc:SetJustifyH("LEFT")

        r:SetScript("OnClick", function(self, button)
            if button == "RightButton" and self.data then
                if IsControlKeyDown() then
                    if runAll then
                        Msg("extract all is running — press Stop first")
                    else
                        StartExtract(self.data)
                    end
                elseif IsShiftKeyDown() then
                    ShowAmountDialog(self.data)
                else
                    StartWithdraw(self.data, 1) -- one, always
                end
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
            if m.extT and m.extT > 0 and m.extN >= m.extT then
                r.tick:SetVertexColor(1, 1, 1)       -- green tick: all unlocked
                r.tick:Show()
            elseif m.extN and m.extN > 0 then
                r.tick:SetVertexColor(1, 0.85, 0.15) -- dimmed yellow: partial
                r.tick:Show()
            else
                r.tick:Hide()
            end
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
    end
    if not collSet then
        tail = tail .. "  ·  |cff888888awaiting extraction data|r"
    end
    if pendingWD then
        tail = tail .. format("  ·  |cff80ffffwithdrawing %s %d/%d (route %d)...|r",
            pendingWD.name, pendingWD.moved, pendingWD.target, pendingWD.route)
    elseif wdDoneAt then
        tail = tail .. format("  ·  |cff33ff33withdrawn: %s|r", wdDoneName or "")
    elseif wdFailed then
        tail = tail .. "  ·  |cffff8080withdraw refused or ignored — send me UncappedVault.lua to pin the route|r"
    end
    if runAll then
        local shown = runAll.idx <= #runAll.queue
            and runAll.idx or #runAll.queue
        tail = tail .. format(
            "  ·  |cffffd100extract all %d/%d: %s (%d learned)|r",
            shown, #runAll.queue, runAll.current or "...",
            runAll.learned)
    end
    if exFlow then
        local st = exFlow.stage
        local word = st == "withdraw" and "withdrawing a copy"
            or st == "locate" and "locating the copy"
            or st == "dialog" and "awaiting your choice"
            or "awaiting unlock"
        tail = tail .. format("  ·  |cff80ffffextracting %s: %s...|r",
            exFlow.name, word)
    elseif exDoneAt then
        tail = tail .. format("  ·  |cff33ff33unlocked: %s|r", exDoneName or "")
    elseif exFailMsg then
        tail = tail .. "  ·  |cffff8080extract aborted: " .. exFailMsg .. "|r"
    end
    ui.status:SetText(format(
        "%d in vault  ·  |cff33ff99%d with procs|r%s%s",
        #vault, procCount,
        pendingN > 0
            and format("  ·  |cff80ffff%d waiting on item cache|r", pendingN)
            or "",
        tail))
end

--==================== extract consent dialog =========================
ShowExtractDialog = function()
    local w = exFlow
    if not w then return end
    if not exDlg then
        exDlg = CreateFrame("Frame", "ProcHunterExtractDialog", UIParent)
        exDlg:SetWidth(340); exDlg:SetHeight(230)
        exDlg:SetPoint("CENTER")
        exDlg:SetFrameStrata("DIALOG")
        exDlg:SetBackdrop({
            bgFile = "Interface\\Buttons\\WHITE8X8",
            edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
            tile = false, edgeSize = 32,
            insets = { left = 8, right = 8, top = 8, bottom = 8 },
        })
        exDlg:SetBackdropColor(0.07, 0.07, 0.09, 1)
        exDlg:EnableMouse(true)

        exDlg.title = exDlg:CreateFontString(nil, "OVERLAY", "GameFontNormal")
        exDlg.title:SetPoint("TOP", 0, -16)
        exDlg.title:SetText("Destroy & Learn")

        exDlg.item = exDlg:CreateFontString(nil, "OVERLAY",
            "GameFontHighlightSmall")
        exDlg.item:SetPoint("TOP", exDlg.title, "BOTTOM", 0, -6)
        exDlg.item:SetPoint("LEFT", 14, 0)
        exDlg.item:SetPoint("RIGHT", -14, 0)

        exDlg.warn = exDlg:CreateFontString(nil, "OVERLAY",
            "GameFontHighlightSmall")
        exDlg.warn:SetPoint("TOP", exDlg.item, "BOTTOM", 0, -4)
        exDlg.warn:SetPoint("LEFT", 14, 0)
        exDlg.warn:SetPoint("RIGHT", -14, 0)

        exDlg.rows = {}
        for i = 1, 6 do
            local pr = CreateFrame("Button", nil, exDlg)
            pr:SetHeight(18)
            pr:SetPoint("TOPLEFT", 24, -84 - (i - 1) * 19)
            pr:SetPoint("RIGHT", -24, 0)
            pr:SetHighlightTexture(
                "Interface\\QuestFrame\\UI-QuestTitleHighlight")
            pr.dot = pr:CreateTexture(nil, "ARTWORK")
            pr.dot:SetWidth(12); pr.dot:SetHeight(12)
            pr.dot:SetPoint("LEFT", 0, 0)
            pr.dot:SetTexture("Interface\\Buttons\\UI-RadioButton")
            pr.txt = pr:CreateFontString(nil, "OVERLAY",
                "GameFontHighlightSmall")
            pr.txt:SetPoint("LEFT", pr.dot, "RIGHT", 6, 0)
            pr.txt:SetPoint("RIGHT", 0, 0)
            pr.txt:SetJustifyH("LEFT")
            pr:SetScript("OnClick", function(self)
                if exFlow and self.row and not self.row.owned
                    and not self.row.tele then
                    exFlow.chosen = self.row
                    ShowExtractDialog() -- redraw selection
                end
            end)
            pr:SetScript("OnEnter", function(self)
                if not self.row then return end
                GameTooltip:SetOwner(self, "ANCHOR_RIGHT")
                -- the spell's own tooltip, same text the game shows
                GameTooltip:SetHyperlink("spell:" .. self.row.spell)
                local tr = self.row.trigger
                if tr and tr > 0 then
                    GameTooltip:AddLine(" ")
                    GameTooltip:AddLine("Trigger type " .. tr,
                        0.6, 0.6, 0.6)
                end
                GameTooltip:Show()
            end)
            pr:SetScript("OnLeave", function()
                GameTooltip:Hide()
            end)
            pr:Hide()
            exDlg.rows[i] = pr
        end

        exDlg.okBtn = CreateFrame("Button", nil, exDlg,
            "UIPanelButtonTemplate")
        exDlg.okBtn:SetWidth(140); exDlg.okBtn:SetHeight(22)
        exDlg.okBtn:SetPoint("BOTTOMLEFT", 16, 14)
        exDlg.okBtn:SetText("Destroy & Learn")
        exDlg.okBtn:SetScript("OnClick", ConfirmExtract)

        exDlg.cancelBtn = CreateFrame("Button", nil, exDlg,
            "UIPanelButtonTemplate")
        exDlg.cancelBtn:SetWidth(100); exDlg.cancelBtn:SetHeight(22)
        exDlg.cancelBtn:SetPoint("BOTTOMRIGHT", -16, 14)
        exDlg.cancelBtn:SetText("Cancel")
        exDlg.cancelBtn:SetScript("OnClick", function()
            AbortExtract("cancelled — the item stays in your bags", true)
        end)

        exDlg:Hide() -- shown-by-default rule
    end

    -- default selection: first locked, non-teleport proc
    local anyLearnable = false
    for i = 1, #w.rows do
        local r = w.rows[i]
        r.owned = collSet and collSet[r.spell] and true or false
        r.tele = IsTeleportSpell(r.spell)
        if not r.owned and not r.tele then anyLearnable = true end
    end
    if not anyLearnable then
        -- nothing on this copy can be learned (owned or teleport):
        -- it goes straight back, no dialog
        return AbortExtract("nothing left to learn on this copy")
    end
    if runAll then
        -- unattended run: choose and confirm without any UI
        w.chosen = nil
        for i = 1, #w.rows do
            local r = w.rows[i]
            if not r.owned and not r.tele then w.chosen = r break end
        end
        return ConfirmExtract()
    end
    if not w.chosen or w.chosen.owned or w.chosen.tele then
        w.chosen = nil
        for i = 1, #w.rows do
            local r = w.rows[i]
            if not r.owned and not r.tele then w.chosen = r; break end
        end
    end

    exDlg.item:SetText(QualityHex(w.q) .. w.name .. "|r")
    exDlg.warn:SetText("|cffff4040This DESTROYS the withdrawn copy.|r" ..
        "  One proc per copy.")
    exDlg.okBtn:Enable()
    for i = 1, 6 do
        local pr = exDlg.rows[i]
        local r = w.rows[i]
        if r then
            pr.row = r
            local nm = GetSpellInfo(r.spell) or ("Spell #" .. r.spell)
            if r.tele then
                pr.txt:SetText("|cff666666" .. nm ..
                    "  (teleport — cannot be extracted)|r")
                pr.dot:SetVertexColor(0.4, 0.4, 0.4)
            elseif r.owned then
                pr.txt:SetText("|cff666666" .. nm ..
                    "  (already unlocked)|r")
                pr.dot:SetVertexColor(0.4, 0.4, 0.4)
            else
                pr.txt:SetText((w.chosen == r and "|cff33ff99" or "|cffffffff")
                    .. nm .. "|r")
                pr.dot:SetVertexColor(1, 1, 1)
            end
            pr:Show()
        else
            pr.row = nil
            pr:Hide()
        end
    end
    exDlg:Show()
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
        "that carries a proc. Right-click withdraws one; Shift+Right-click asks for an amount. " ..
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
        Request()          -- also nudges kirei's addon to refresh its table
        RequestCollection()
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
        if db.wdSchema ~= 2 then db.wdRoute = nil; db.wdSchema = 2 end
        if db.fontSize == nil then db.fontSize = 11 end
        if db.alpha == nil then db.alpha = 1 end
        if db.font == nil then db.font = 1 end
        BuildOptions()
    elseif event == "PLAYER_LOGIN" then
        BuildMinimapButton()
        Stamp()
    end
end)
