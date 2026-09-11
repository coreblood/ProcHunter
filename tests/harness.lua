-- ProcHunter v1.2.0 headless harness (Lua 5.1)
local T, P = 0, 0
local function ok(cond, msg)
    T = T + 1
    if cond then P = P + 1 else print("FAIL: " .. msg) end
end

--==================== WoW API stubs ====================
local clock = 1000
function GetTime() return clock end
strsub = string.sub
strtrim = function(s) return (s:gsub("^%s+", ""):gsub("%s+$", "")) end
local shiftDown = false
function IsShiftKeyDown() return shiftDown end
local optCategories = {}
function InterfaceOptions_AddCategory(p) optCategories[#optCategories+1] = p end

local sent = {}
function SendAddonMessage(prefix, msg, chan, target)
    sent[#sent + 1] = { prefix = prefix, msg = msg }
end
function UnitName() return "Mhortai" end

local chat = {}
DEFAULT_CHAT_FRAME = { AddMessage = function(_, m) chat[#chat + 1] = m end }

local items = {}
function GetItemInfo(arg)
    local e = tonumber(tostring(arg):match("^(%d+)$") or tostring(arg):match("^item:(%d+)"))
    local it = e and items[e]
    if not it then return nil end
    return it.name, "link", it.q or 2, it.ilvl or 1, 1, "class", "sub", 1,
        it.equipLoc or "INVTYPE_WEAPON", "tex", 0
end
function GetItemIcon() return "tex" end

local spells = { [100] = "Frost Bite", [101] = "Frost Bite",
    [888] = "Enrage", [999] = "Increase Intellect 24" }
function GetSpellInfo(id) return spells[id] end

-- spell tooltip text used by the classification scanner
local spellTips = {
    [100] = { "Frost Bite", "Chance on hit: Blasts the enemy for 100 Frost damage." },
    [101] = { "Frost Bite", "Chance on hit: Blasts the enemy for 100 Frost damage." },
    [999] = { "Increase Intellect 24", "Increases Intellect by 24." },
    [888] = { "Enrage", "Increases your attack power by 300 for 30 sec." },
}

ITEM_QUALITY_COLORS = {}
for i = 0, 7 do ITEM_QUALITY_COLORS[i] = { hex = "|cffffffff" } end
UISpecialFrames = {}
SlashCmdList = {}
tinsert = table.insert
FauxScrollFrame_Update = function() end
FauxScrollFrame_GetOffset = function() return 0 end
FauxScrollFrame_OnVerticalScroll = function() end

local lastStatus = ""
local function NewRegion(kind)
    local o = { _kind = kind, _text = "" }
    o.SetText = function(self, t)
        self._text = t
        if type(t) == "string" and t:find("in vault") then lastStatus = t end
    end
    o.GetText = function(self) return self._text end
    setmetatable(o, { __index = function(_, k)
        if type(k) == "string" and k:match("^[A-Z]") then return function() end end
    end })
    return o
end

local frames = {}
function CreateFrame(ftype, name, parent, template)
    local f = { _type = ftype, _name = name, _shown = true,
        _scripts = {}, _events = {}, _checked = false }
    f.RegisterEvent = function(self, ev) self._events[ev] = true end
    f.SetScript = function(self, h, fn) self._scripts[h] = fn end
    f.GetScript = function(self, h) return self._scripts[h] end
    f.Show = function(self) self._shown = true end
    f.Hide = function(self) self._shown = false end
    f.IsShown = function(self) return self._shown end
    f.CreateTexture = function() return NewRegion("tex") end
    f.CreateFontString = function() return NewRegion("fs") end
    f.GetPoint = function() return "CENTER", nil, "CENTER", 0, 0 end
    f.GetText = function(self) return self._text or "" end
    f.SetText = function(self, t) self._text = t end
    f.SetChecked = function(self, v) self._checked = not not v end
    f.GetChecked = function(self) return self._checked end
    if ftype == "GameTooltip" and name then
        f._lines = {}
        f.ClearLines = function(self) self._lines = {} end
        f.SetHyperlink = function(self, link)
            local sid = tonumber(tostring(link):match("^spell:(%d+)"))
            self._lines = sid and spellTips[sid] or {}
            for i, txt in ipairs(self._lines) do
                local g = _G[name .. "TextLeft" .. i] or NewRegion("fs")
                _G[name .. "TextLeft" .. i] = g
                g._text = txt
            end
        end
        f.NumLines = function(self) return #self._lines end
    end
    setmetatable(f, { __index = function(_, k)
        if type(k) == "string" and k:match("^[A-Z]") then return function() end end
    end })
    if name then _G[name] = f end
    if template == "UICheckButtonTemplate" and name then
        _G[name .. "Text"] = NewRegion("fs")
    end
    frames[#frames + 1] = f
    return f
end
UIParent = CreateFrame("Frame")
Minimap = CreateFrame("Minimap", "Minimap")
Minimap.GetCenter = function() return 100, 100 end
GameTooltip = CreateFrame("GameTooltip")

--==================== synthetic databases ====================
ProcHunter_ProcDB = {
    [100] = "Frostbrand Blade",
    [101] = { "Frostbrand Blade", "Frost Shield" },
    [200] = "Holy Satchel",                  -- proc-named BAG (must not show)
    [300] = "Mystery Maul",                  -- proc on an uncached item (empty tip)
    [888] = "Berserker Blade",               -- duration buff => real proc
    [999] = "Eagle Cuirass",                 -- flat stat only => hidden
}
ProcHunter_ProcDB_Manual = { [400] = "Override Ring" }
ProcHunter_AbilityDB = { [500] = "Frostbrand Blade" } -- must NOT be indexed
ProcHunter_DropDB = { [100] = { "Kirei's Chest" } }

dofile("ProcHunter/ProcHunter.lua")

--==================== find core frames ====================
local comms, ticker, init
for _, f in ipairs(frames) do
    if f._events["CHAT_MSG_ADDON"] then comms = f end
    if f._events["ADDON_LOADED"] then init = f end
    if not f._events["CHAT_MSG_ADDON"] and not f._events["ADDON_LOADED"]
        and f._scripts["OnUpdate"] and not f._name then ticker = f end
end
ok(comms and init and ticker, "core frames located")

init._scripts["OnEvent"](init, "ADDON_LOADED", "ProcHunter")
init._scripts["OnEvent"](init, "PLAYER_LOGIN")
ok(#chat == 1 and chat[1]:find("ProcHunter"), "exactly one login stamp")

--==================== wire path ====================
items[1001] = { name = "Frostbrand Blade", q = 4, ilvl = 200 }
items[1002] = { name = "Plain Chestplate", q = 3, ilvl = 180 }
items[1003] = { name = "Holy Satchel", q = 3, ilvl = 1 }
items[1004] = { name = "Holy Satchel", q = 1, ilvl = 1 }
items[1006] = { name = "Override Ring", q = 3, ilvl = 190 }
-- 1005 "Mystery Maul" stays uncached at first

local function feed(msg) comms._scripts["OnEvent"](comms, "CHAT_MSG_ADDON", "UNC", msg) end
local function tick() ticker._scripts["OnUpdate"](ticker) end

feed("VLTROW:1001,0,1,4,2,7,200,icon;1002,0,2,3,4,4,180,icon;")
feed("VLTROW:1001,0,1,4,2,7,200,icon;1003,0,1,3,1,0,1,icon;1004,0,5,1,0,0,1,icon;")
feed("VLTROW:1005,0,1,4,2,4,210,icon;1006,-13,1,3,4,0,190,icon;")
feed("VLTEND:")

SlashCmdList["PROCHUNTER"]()
local win = _G["ProcHunterFrame"]
ok(win._shown == true, "window visible on the FIRST toggle (v1.0.0 regression)")
ok(#sent == 1 and sent[1].msg == "VLTGET", "open always sends VLTGET underneath")
ok(lastStatus:find("6 in vault") ~= nil, "6 vault rows after dedupe: " .. lastStatus)
ok(lastStatus:find("4 equippable") ~= nil, "bag+consumable excluded: " .. lastStatus)
ok(lastStatus:find("2 with procs") ~= nil, "2 procs while maul uncached: " .. lastStatus)
ok(lastStatus:find("1 waiting") ~= nil, "1 pending on cache: " .. lastStatus)
ok(lastStatus:find("source: UncappedVault") == nil, "wire source has no tag")

items[1005] = { name = "Mystery Maul", q = 4, ilvl = 210 }
clock = clock + 2; tick()
ok(lastStatus:find("3 with procs") ~= nil, "maul joins after cache: " .. lastStatus)
ok(lastStatus:find("waiting") == nil, "pending cleared: " .. lastStatus)

--==================== VLTUPD debounce + cooldown ====================
local before = #sent
feed("VLTUPD:")
clock = clock + 3; tick()
ok(#sent == before + 1 and sent[#sent].msg == "VLTGET",
    "VLTUPD triggers one VLTGET")
before = #sent
feed("VLTUPD:")
clock = clock + 2.5; tick()
ok(#sent == before, "request cooldown respected")

--==================== fallback 3-field parse ====================
feed("VLTROW:1001,0,1,junkfield;")
feed("VLTEND:")
ok(lastStatus:find("1 in vault") and lastStatus:find("1 equippable")
    and lastStatus:find("1 with procs"),
    "tolerant parse + equipLoc fallback + proc match: " .. lastStatus)

--==================== filter box ====================
feed("VLTROW:1001,0,1,4,2,7,200,icon;1005,0,1,4,2,4,210,icon;1006,-13,1,3,4,0,190,icon;")
feed("VLTEND:")
ok(lastStatus:find("3 with procs") and lastStatus:find("showing 3"),
    "full snapshot back: " .. lastStatus)
local filterBox = _G["ProcHunterFilterBox"]
filterBox._text = "frost"; filterBox._scripts["OnTextChanged"]()
ok(lastStatus:find("showing 1") ~= nil, "filter 'frost': " .. lastStatus)
filterBox._text = "kirei"; filterBox._scripts["OnTextChanged"]()
ok(lastStatus:find("showing 0") ~= nil, "no-match filter: " .. lastStatus)
filterBox._text = ""; filterBox._scripts["OnTextChanged"]()
ok(lastStatus:find("showing 3") ~= nil, "filter cleared: " .. lastStatus)

--==================== flat-stat classification ====================
items[1007] = { name = "Eagle Cuirass", q = 2, ilvl = 100 }
items[1008] = { name = "Berserker Blade", q = 3, ilvl = 150 }
feed("VLTROW:1001,0,1,4,2,7,200,icon;1007,0,1,2,4,1,100,icon;1008,0,1,3,2,7,150,icon;")
feed("VLTEND:")
ok(lastStatus:find("2 with procs") ~= nil,
    "cuirass hidden, blade kept (duration guard): " .. lastStatus)
ok(lastStatus:find("1 flat%-stat hidden") ~= nil, "hidden counter: " .. lastStatus)
local cf = _G["ProcHunterFlatCheck"]
ok(cf ~= nil and cf._checked == true, "flat tickbox exists, default ON")
cf:SetChecked(false); cf._scripts["OnClick"](cf)
ok(lastStatus:find("3 with procs") ~= nil and lastStatus:find("hidden") == nil,
    "untick shows flat-only items: " .. lastStatus)
cf:SetChecked(true); cf._scripts["OnClick"](cf)
ok(lastStatus:find("2 with procs") ~= nil, "re-tick hides again: " .. lastStatus)

--==================== minimap + options ====================
local mm = _G["ProcHunterMinimapButton"]
ok(mm ~= nil, "minimap button exists")
mm._scripts["OnClick"]()
ok(win._shown == false, "minimap click closes")
clock = clock + 4
mm._scripts["OnClick"]()
ok(win._shown == true, "minimap click reopens")
ok(#optCategories == 1 and optCategories[1].name == "ProcHunter",
    "options panel registered")
local cb = _G["ProcHunterMMCheck"]
cb:SetChecked(false); cb._scripts["OnClick"](cb)
ok(mm._shown == false, "unticking hides minimap button")
cb:SetChecked(true); cb._scripts["OnClick"](cb)
ok(mm._shown == true, "ticking shows minimap button")

--==================== instant global read on open ====================
SlashCmdList["PROCHUNTER"]()  -- close
UncappedVault = { items = {
    { itemId = 1001, stackCount = 3, suffixId = 0, rarity = 4, itemLevel = 200 },
    { itemId = 1008, stackCount = 1 },
} }
clock = clock + 4
SlashCmdList["PROCHUNTER"]()  -- open: must fill instantly, no clock advance
ok(lastStatus:find("2 in vault") ~= nil and lastStatus:find("source: UncappedVault"),
    "instant fill from global on open: " .. lastStatus)
ok(lastStatus:find("2 with procs") ~= nil, "blade+blade matched from global: " .. lastStatus)

--==================== 2s poll picks up changes ====================
UncappedVault.items[#UncappedVault.items + 1] = { itemId = 1005, stackCount = 1 }
clock = clock + 2.1; tick()
ok(lastStatus:find("3 in vault") ~= nil, "poll absorbed a new deposit: " .. lastStatus)

--==================== withdraw: route 1 success ====================
UncappedVault.Withdraw = function(e, rp, c)
    for i = #UncappedVault.items, 1, -1 do
        local r = UncappedVault.items[i]
        if r.itemId == e then
            r.stackCount = (r.stackCount or 1) - c
            if r.stackCount <= 0 then table.remove(UncappedVault.items, i) end
            return
        end
    end
end
local function RowFor(e)
    for _, f in ipairs(frames) do
        if f.data and type(f.data) == "table" and f.data.e == e then return f end
    end
end
local blade = RowFor(1008)
ok(blade ~= nil, "row button for the berserker blade found")
blade._scripts["OnClick"](blade, "RightButton")
ok(lastStatus:find("withdrawing") ~= nil, "withdraw pending state: " .. lastStatus)
clock = clock + 1.6; tick()
ok(lastStatus:find("withdrawn: ") ~= nil, "route 1 withdraw verified: " .. lastStatus)
ok(lastStatus:find("2 in vault") ~= nil, "blade left the list: " .. lastStatus)
ok(ProcHunterDB.wdRoute == 1, "working route remembered")

--==================== withdraw: shift = one from a stack ====================
shiftDown = true
local stack = RowFor(1001)
ok(stack ~= nil and stack.data.count == 3, "stacked row found (x3)")
stack._scripts["OnClick"](stack, "RightButton")
clock = clock + 1.6; tick()
shiftDown = false
ok(lastStatus:find("withdrawn: ") ~= nil, "shift-withdraw verified: " .. lastStatus)
ok(RowFor(1001) and RowFor(1001).data.count == 2, "stack reduced 3 -> 2")

--==================== withdraw: cascade exhaustion ====================
UncappedVault.Withdraw = function() error("boom") end
UncappedVault.Send = nil
before = #sent
stack = RowFor(1001)
stack._scripts["OnClick"](stack, "RightButton")
ok(#sent == before + 1 and sent[#sent].msg:find("^VLTWD:1001:0:2") ~= nil,
    "cascade fell through to the raw VLTWD send")
clock = clock + 1.6; tick()
ok(lastStatus:find("refused or ignored") ~= nil, "failure surfaced: " .. lastStatus)
ok(ProcHunterDB.wdRoute == nil, "remembered route cleared on failure")

--==================== wire audit + debug/dump ====================
for i = 1, #sent do
    ok(sent[i].msg == "VLTGET" or sent[i].msg:find("^VLTWD:") ~= nil,
        "wire send #" .. i .. " is VLTGET or VLTWD only")
end
local chatBefore = #chat
SlashCmdList["PROCHUNTER"]("debug")
ok(chat[#chat]:find("debug"), "debug toggle announces")
comms._scripts["OnEvent"](comms, "CHAT_MSG_ADDON", "XYZ", "hello-wire")
ok(chat[#chat]:find("%[wire%]") and chat[#chat]:find("XYZ"), "debug prints traffic")
SlashCmdList["PROCHUNTER"]("debug")
SlashCmdList["PROCHUNTER"](" dump ")
ok(chat[#chat - 1]:find("dump:") or chat[#chat]:find("dump:"), "dump prints shape info")
ok(win._shown == true, "debug/dump args do not toggle the window")

print(string.format("%d/%d tests passed", P, T))
if P ~= T then os.exit(1) end
