--=====================================================================
-- ProcHunter v1.0.0 — Uncapped Vault proc scanner (read-only)
--
-- Lists every item in the Uncapped Vault that (a) can be equipped by
-- anyone (class/level restrictions ignored) and (b) carries an effect
-- spell found in the bundled proc database.
--
-- WIRE SAFETY: the only thing this addon ever sends is VLTGET — the
-- same read-only snapshot request the Dashboard's Vault tab sends.
-- It never deposits, withdraws, consumes or modifies anything.
--
-- Wire (transport "REAGENTBANK", replies on "UNC"):
--   -> VLTGET                       request snapshot
--   <- VLTROW:e,rp,count,quality,class,subclass,ilvl,icon; ...  rows
--   <- VLTEND:                      snapshot complete
--   <- VLTUPD / VLTROWUPD           vault changed server-side
--
-- 3.3.5a constraints honoured: no C_Timer, no SetShown, UI built
-- lazily after ADDON_LOADED, no dropdown init at file scope.
--=====================================================================

local ADDON   = "ProcHunter"
local VERSION = "1.0.0"
local SEND_PREFIX = "REAGENTBANK"
local RECV_PREFIX = "UNC"

local REQUEST_COOLDOWN = 3     -- min seconds between VLTGET sends
local DIRTY_DEBOUNCE   = 2     -- wait after a VLTUPD before re-requesting
local PRIME_INTERVAL   = 1     -- seconds between item-cache retry passes
local PRIME_MAX_TRIES  = 20    -- give up on an uncached item after this

local floor  = math.floor
local format = string.format
local lower  = string.lower
local find   = string.find
local gmatch = string.gmatch

--========================= shared state ==============================
-- (declared above every function that reads them — hard rule)
local db                    -- ProcHunterDB (SavedVariables)
local nameIndex             -- lowered item name -> array of proc spellIds
local vault      = {}       -- committed snapshot rows
local staging    = {}       -- "e:rp" -> row, during a VLTROW stream
local stagingN   = 0
local matched    = {}       -- rows passing both filters (display source)
local shown      = {}       -- matched after the text filter
local pending    = {}       -- entry -> retry count (waiting on item cache)
local pendingN   = 0
local ui                    -- main window (lazy)
local scanTip               -- hidden tooltip used only to prime item cache
local snapshotSeen = false
local lastRequest  = 0
local dirtyAt      = nil    -- GetTime() of last unhandled vault change
local primeAt      = 0
local eqCount, procCount = 0, 0

--========================= small helpers =============================
local function Stamp()
    DEFAULT_CHAT_FRAME:AddMessage("|cff33ff99ProcHunter|r v" .. VERSION ..
        " — /ph or /prochunter to open")
end

local function ItemLink(e, rp)
    return format("item:%d:0:0:0:0:0:%d", e, rp or 0)
end

-- Equippable by anyone: the wire row's item class is server truth —
-- 2 = weapon, 4 = armor (rings/trinkets/necks/cloaks/shields/relics
-- included). Bags (class 1), ammo, consumables etc. drop out here.
-- If a row arrived through the tolerant fallback parser without a
-- class field, fall back to GetItemInfo's equip slot (needs cache).
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
    SendAddonMessage(SEND_PREFIX, "VLTGET", "WHISPER", UnitName("player"))
end

local function CommitSnapshot()
    for k in pairs(vault) do vault[k] = nil end
    local n = 0
    for _, row in pairs(staging) do n = n + 1; vault[n] = row end
    for k in pairs(staging) do staging[k] = nil end
    stagingN = 0
    snapshotSeen = true
    Rebuild()
end

local comms = CreateFrame("Frame")
comms:RegisterEvent("CHAT_MSG_ADDON")
comms:SetScript("OnEvent", function(_, _, prefix, msg)
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
        CommitSnapshot()
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

    ui.status:SetText(format(
        "%d in vault  ·  %d equippable  ·  |cff33ff99%d with procs|r  ·  showing %d%s%s",
        #vault, eqCount, procCount, #shown,
        pendingN > 0
            and format("  ·  |cff80ffff%d waiting on item cache|r", pendingN)
            or "",
        snapshotSeen and "" or "  ·  |cffff8080no snapshot yet — Refresh|r"))
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
SlashCmdList["PROCHUNTER"] = Toggle

--========================= init ======================================
local init = CreateFrame("Frame")
init:RegisterEvent("ADDON_LOADED")
init:RegisterEvent("PLAYER_LOGIN")
init:SetScript("OnEvent", function(_, event, arg1)
    if event == "ADDON_LOADED" and arg1 == ADDON then
        ProcHunterDB = ProcHunterDB or {}
        db = ProcHunterDB
    elseif event == "PLAYER_LOGIN" then
        Stamp()
    end
end)
