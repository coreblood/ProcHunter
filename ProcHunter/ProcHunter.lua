--=====================================================================
-- ProcHunter v1.1.0 — Uncapped Vault proc scanner (read-only)
--
-- Lists every item in the Uncapped Vault that (a) can be equipped by
-- anyone (class/level restrictions ignored) and (b) carries an effect
-- spell found in the bundled proc database.
--
-- WIRE SAFETY: the only thing this addon ever sends is VLTGET — the
-- same read-only snapshot request the Dashboard's Vault tab sends.
-- It never deposits, withdraws, consumes or modifies anything.
--
-- Data sources, in order:
--   1. VLTGET -> VLTROW/VLTEND snapshot on the UNC prefix
--   2. If the wire stays silent for 5s, the UncappedVault addon's own
--      items table (_G.UncappedVault.items) is read directly.
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
local VERSION = "1.1.0"
local SEND_PREFIX = "REAGENTBANK"
local RECV_PREFIX = "UNC"

local REQUEST_COOLDOWN = 3     -- min seconds between VLTGET sends
local DIRTY_DEBOUNCE   = 2     -- wait after a VLTUPD before re-requesting
local PRIME_INTERVAL   = 1     -- seconds between item-cache retry passes
local PRIME_MAX_TRIES  = 20    -- give up on an uncached item after this
local WIRE_WATCHDOG    = 5     -- silent seconds before the global fallback

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
local vault      = {}       -- committed snapshot rows
local staging    = {}       -- "e:rp" -> row, during a VLTROW stream
local matched    = {}       -- rows passing both filters (display source)
local shown      = {}       -- matched after the text filter
local pending    = {}       -- entry -> retry count (waiting on item cache)
local pendingN   = 0
local ui                    -- main window (lazy)
local mmBtn                 -- minimap button (lazy)
local scanTip               -- hidden tooltip used only to prime item cache
local snapshotSeen = false
local lastRequest  = 0
local dirtyAt      = nil    -- GetTime() of last unhandled vault change
local awaitingAt   = nil    -- GetTime() of an unanswered VLTGET
local primeAt      = 0
local eqCount, procCount = 0, 0
local dataSource   = nil    -- "wire" | "UncappedVault"
local wireDebug    = false

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

-- Equippable by anyone: the wire row's item class is server truth —
-- 2 = weapon, 4 = armor (rings/trinkets/necks/cloaks/shields/relics
-- included). Bags (class 1), ammo, consumables etc. drop out here.
-- Rows without a class field (tolerant parse / global fallback) use
-- GetItemInfo's equip slot instead (needs the item cache).
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

--========================= cache priming =============================
local function Prime(e)
    if not scanTip then
        scanTip = CreateFrame("GameTooltip", "ProcHunterScanTip",
            nil, "GameTooltipTemplate")
        scanTip:SetOwner(UIParent, "ANCHOR_NONE")
    end
    scanTip:ClearLines()
    scanTip:SetHyperlink("item:" .. e)
end

--========================= match pass ================================
local RefreshList -- forward (defined with the UI)

local function Rebuild()
    BuildIndex()
    for k in pairs(matched) do matched[k] = nil end
    for k in pairs(pending) do pending[k] = nil end
    pendingN, eqCount, procCount = 0, 0, 0

    for i = 1, #vault do
        local row = vault[i]
        local eq = IsEquippable(row)
        if eq == nil then
            -- class unknown AND item uncached: park it
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
                    procCount = procCount + 1
                    local link = ItemLink(row.e, row.rp)
                    local dispName = GetItemInfo(link) or baseName
                    matched[#matched + 1] = {
                        e = row.e, rp = row.rp, count = row.count,
                        q = row.q, ilvl = row.ilvl,
                        name = dispName, link = link, spells = spells,
                    }
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

local function CommitSnapshot(source)
    for k in pairs(vault) do vault[k] = nil end
    local n = 0
    for _, row in pairs(staging) do n = n + 1; vault[n] = row end
    for k in pairs(staging) do staging[k] = nil end
    snapshotSeen = true
    awaitingAt = nil
    dataSource = source or "wire"
    Rebuild()
end

--=================== UncappedVault global fallback ===================
-- If the live realm moves vault data through kirei's transport hooks
-- instead of UNC addon messages, the UncappedVault addon still holds
-- the goods in _G.UncappedVault.items. Its exact shape is not
-- guaranteed, so every plausible field spelling is probed.
local FIELD_E  = { "e", "entry", "id", "itemId", "itemid", "item" }
local FIELD_C  = { "count", "c", "n", "num", "stack", "stackCount" }
local FIELD_RP = { "rp", "randomProp", "randomprop", "rand", "suffix", "suffixId" }
local FIELD_Q  = { "q", "quality", "rarity" }
local FIELD_IL = { "ilvl", "itemLevel", "itemlevel", "level" }
local FIELD_CL = { "class", "itemClass", "itemclass", "cls" }

local function PickField(row, names, wantNumber)
    for i = 1, #names do
        local v = row[names[i]]
        if type(v) == "number" then return v end
        if not wantNumber and type(v) == "string" then return v end
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
    local e = PickField(row, FIELD_E, true)
    if not e then
        -- entry may hide inside a link string
        e = EntryFrom(row.link or row.itemLink or row.itemlink)
    end
    if not e or e <= 0 then return false end
    local rp = PickField(row, FIELD_RP, true) or 0
    staging[e .. ":" .. rp] = {
        e = e, rp = rp,
        count = PickField(row, FIELD_C, true) or 1,
        q = PickField(row, FIELD_Q, true),
        ilvl = PickField(row, FIELD_IL, true),
        class = PickField(row, FIELD_CL, true),
    }
    return true
end

local function TryVaultGlobal()
    local UV = _G.UncappedVault
    local src = UV and type(UV) == "table" and UV.items
    if type(src) ~= "table" then return false end
    local got = 0
    -- array of row tables
    for i = 1, #src do
        if AbsorbRow(src[i]) then got = got + 1 end
    end
    if got == 0 then
        -- keyed shapes: entry -> row table, or entry -> count
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
        CommitSnapshot("UncappedVault")
        return true
    end
    for k in pairs(staging) do staging[k] = nil end
    return false
end

local function DumpVault()
    local UV = _G.UncappedVault
    Msg("dump: UncappedVault is " .. type(UV))
    if type(UV) ~= "table" then return end
    Msg("dump: .items is " .. type(UV.items))
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

--========================= wire handler ==============================
local comms = CreateFrame("Frame")
comms:RegisterEvent("CHAT_MSG_ADDON")
comms:SetScript("OnEvent", function(_, _, prefix, msg, chan, sender)
    if wireDebug and msg then
        Msg("|cff888888[wire]|r " .. tostring(prefix) .. " " .. strsub(msg, 1, 70))
    end
    if prefix ~= RECV_PREFIX or not msg then return end
    if find(msg, "^VLTROW:") then
        -- full 7-numeric-field rows (icon field skipped)
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
            -- tolerant fallback (proven VaultScan pattern): first three
            -- fields only; equippable check falls back to GetItemInfo
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
        -- vault changed; re-pull (debounced) while the window is open
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
        -- the wire never answered: fall back to UncappedVault's own data
        awaitingAt = nil
        if not TryVaultGlobal() and RefreshList then RefreshList() end
    end
    if pendingN > 0 and now - primeAt >= PRIME_INTERVAL then
        primeAt = now
        ResolvePending()
    end
end)

--========================= UI ========================================
local ROWS, ROW_H = 14, 22

local function QualityHex(q)
    local c = q and ITEM_QUALITY_COLORS[q]
    return c and c.hex or "|cffffffff"
end

local function ProcLines(spells)
    -- unique by spell name; keep every id per name for the tooltip
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
    local lines = ProcLines(row.spells)
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
    refresh:SetScript("OnClick", function() lastRequest = 0; Request() end)

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
        FauxScrollFrame_OnVerticalScroll(self, offset, ROW_H, RefreshList)
    end)
    ui.scroll = scroll

    ui.rows = {}
    for i = 1, ROWS do
        local r = CreateFrame("Button", nil, ui)
        r:SetHeight(ROW_H)
        r:SetPoint("TOPLEFT", 18, -64 - (i - 1) * ROW_H)
        r:SetPoint("RIGHT", scroll, "RIGHT", -4, 0)
        r:SetHighlightTexture("Interface\\QuestFrame\\UI-QuestTitleHighlight")

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

        r:SetScript("OnEnter", function(self)
            if self.data then RowTooltip(self.data) end
        end)
        r:SetScript("OnLeave", function() GameTooltip:Hide() end)
        r:Hide()
        ui.rows[i] = r
    end

    -- frames are SHOWN by default on 3.3.5a: without this, the first
    -- toggle press builds the window already "shown" and instantly
    -- hides it (press silently eaten — hit live in v1.0.0)
    ui:Hide()
end

RefreshList = function()
    if not ui then return end

    -- apply the text filter (item name or proc name)
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

    FauxScrollFrame_Update(ui.scroll, #shown, ROWS, ROW_H)
    local offset = FauxScrollFrame_GetOffset(ui.scroll)
    for i = 1, ROWS do
        local r = ui.rows[i]
        local m = shown[i + offset]
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
            r.proc:SetText("|cff33ff99" .. table.concat(names, ", ") .. "|r")
            r:Show()
        else
            r.data = nil
            r:Hide()
        end
    end

    local tail
    if not snapshotSeen then
        tail = awaitingAt and "  ·  |cff80ffffasking the server...|r"
            or "  ·  |cffff8080no snapshot yet — Refresh (then /ph dump if still empty)|r"
    elseif dataSource == "UncappedVault" then
        tail = "  ·  source: UncappedVault"
    else
        tail = ""
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
-- Free-drag with exact x/y offsets saved (no rim snapping): radius
-- placement breaks on scaled minimaps. Canonical LibDBIcon texture
-- layout: 31px button, 53px border at TOPLEFT 0,0, 17px icon at 7,-6.
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
        "that carries a proc. Read-only — it never touches your vault. " ..
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

    local h = p:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    h:SetPoint("TOPLEFT", cb, "BOTTOMLEFT", 4, -14)
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
        RefreshList()
        if not snapshotSeen or dirtyAt then Request() end
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
        BuildOptions()
    elseif event == "PLAYER_LOGIN" then
        BuildMinimapButton()
        Stamp()
    end
end)
