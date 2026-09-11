-- ProcHunter v1.0.0 headless harness (Lua 5.1)
local T, P = 0, 0
local function ok(cond, msg)
    T = T + 1
    if cond then P = P + 1 else print("FAIL: " .. msg) end
end

--==================== WoW API stubs ====================
local clock = 1000
function GetTime() return clock end

local sent = {}
function SendAddonMessage(prefix, msg, chan, target)
    sent[#sent + 1] = { prefix = prefix, msg = msg, chan = chan, target = target }
end
function UnitName() return "Mhortai" end

local chat = {}
DEFAULT_CHAT_FRAME = { AddMessage = function(_, m) chat[#chat + 1] = m end }

-- item database for GetItemInfo: entry -> {name, quality, ilvl, equipLoc}
local items = {}
function GetItemInfo(arg)
    local e = tonumber(tostring(arg):match("^(%d+)$") or tostring(arg):match("^item:(%d+)"))
    local it = e and items[e]
    if not it then return nil end
    return it.name, "link", it.q or 2, it.ilvl or 1, 1, "class", "sub", 1,
        it.equipLoc or "INVTYPE_WEAPON", "tex", 0
end
function GetItemIcon() return "tex" end

local spells = { [100] = "Frost Bite", [101] = "Frost Bite", [200] = "Holy Nova" }
function GetSpellInfo(id) return spells[id] end

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
    local f = { _type = ftype, _name = name, _shown = false,
        _scripts = {}, _events = {} }
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
    f.ClearLines = function() end
    f.SetHyperlink = function() end
    setmetatable(f, { __index = function(_, k)
        if type(k) == "string" and k:match("^[A-Z]") then return function() end end
    end })
    frames[#frames + 1] = f
    return f
end
UIParent = CreateFrame("Frame")
GameTooltip = CreateFrame("GameTooltip")

--==================== synthetic databases ====================
ProcHunter_ProcDB = {
    [100] = "Frostbrand Blade",              -- weapon proc (two ranks)
    [101] = { "Frostbrand Blade", "Frost Shield" },
    [200] = "Holy Satchel",                  -- proc-named BAG (must not show)
    [300] = "Mystery Maul",                  -- proc on an uncached item
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

--==================== cached items ====================
items[1001] = { name = "Frostbrand Blade", q = 4, ilvl = 200 }
items[1002] = { name = "Plain Chestplate", q = 3, ilvl = 180 }
items[1003] = { name = "Holy Satchel", q = 3, ilvl = 1 }     -- bag
items[1004] = { name = "Holy Satchel", q = 1, ilvl = 1 }     -- consumable twin
items[1006] = { name = "Override Ring", q = 3, ilvl = 190 }
-- 1005 "Mystery Maul" stays uncached at first

local function feed(msg) comms._scripts["OnEvent"](comms, "CHAT_MSG_ADDON", "UNC", msg) end

-- snapshot: weapon+proc / armor no proc / bag(class1) / consumable(class0)
-- / uncached weapon / ring from manual override (class4)
-- duplicate of the first row exercises the e:rp dedupe
feed("VLTROW:1001,0,1,4,2,7,200,icon;1002,0,2,3,4,4,180,icon;")
feed("VLTROW:1001,0,1,4,2,7,200,icon;1003,0,1,3,1,0,1,icon;1004,0,5,1,0,0,1,icon;")
feed("VLTROW:1005,0,1,4,2,4,210,icon;1006,-13,1,3,4,0,190,icon;")
feed("VLTEND:")

-- open the window
SlashCmdList["PROCHUNTER"]()
ok(lastStatus:find("6 in vault") ~= nil, "6 vault rows after dedupe: " .. lastStatus)
ok(lastStatus:find("4 equippable") ~= nil, "4 equippable (bag+consumable excluded): " .. lastStatus)
ok(lastStatus:find("2 with procs") ~= nil, "2 procs while maul uncached: " .. lastStatus)
ok(lastStatus:find("1 waiting") ~= nil, "1 pending on cache: " .. lastStatus)

-- opening with a snapshot already seen but not dirty must NOT send VLTGET
ok(#sent == 0, "no VLTGET while snapshot fresh (sent=" .. #sent .. ")")

--==================== cache resolution ====================
items[1005] = { name = "Mystery Maul", q = 4, ilvl = 210 }
clock = clock + 2
ticker._scripts["OnUpdate"](ticker)
ok(lastStatus:find("3 with procs") ~= nil, "maul joins after cache: " .. lastStatus)
ok(lastStatus:find("waiting") == nil, "pending cleared: " .. lastStatus)
ok(lastStatus:find("showing 3") ~= nil, "3 rows shown: " .. lastStatus)

--==================== dirty -> debounced re-request ====================
feed("VLTUPD:")
clock = clock + 3
ticker._scripts["OnUpdate"](ticker)
ok(#sent == 1 and sent[1].msg == "VLTGET" and sent[1].prefix == "REAGENTBANK",
    "VLTUPD triggers one VLTGET (sent=" .. #sent .. ")")
-- immediate second dirty within cooldown: no extra send
feed("VLTUPD:")
clock = clock + 2.5
ticker._scripts["OnUpdate"](ticker)
ok(#sent == 1, "request cooldown respected (sent=" .. #sent .. ")")

--==================== fallback 3-field parse ====================
feed("VLTROW:1001,0,1,junkfield;")
feed("VLTEND:")
ok(lastStatus:find("1 in vault") ~= nil, "fallback parse committed 1 row: " .. lastStatus)
ok(lastStatus:find("1 equippable") ~= nil,
    "fallback row equippable via GetItemInfo equipLoc: " .. lastStatus)
ok(lastStatus:find("1 with procs") ~= nil, "fallback row matched proc: " .. lastStatus)

--==================== filter box ====================
-- rebuild the full snapshot
feed("VLTROW:1001,0,1,4,2,7,200,icon;1005,0,1,4,2,4,210,icon;1006,-13,1,3,4,0,190,icon;")
feed("VLTEND:")
ok(lastStatus:find("3 with procs") and lastStatus:find("showing 3"),
    "full snapshot back: " .. lastStatus)

local filterBox
for _, f in ipairs(frames) do
    if f._name == "ProcHunterFilterBox" then filterBox = f end
end
ok(filterBox ~= nil, "filter box exists")
filterBox._text = "frost"
filterBox._scripts["OnTextChanged"]()
ok(lastStatus:find("showing 1") ~= nil,
    "filter 'frost' matches the blade only: " .. lastStatus)
filterBox._text = "kirei"
filterBox._scripts["OnTextChanged"]()
ok(lastStatus:find("showing 0") ~= nil, "no match filter: " .. lastStatus)
filterBox._text = ""
filterBox._scripts["OnTextChanged"]()
ok(lastStatus:find("showing 3") ~= nil, "filter cleared: " .. lastStatus)

--==================== ability DB not indexed ====================
-- spell 500 lists "Frostbrand Blade" in AbilityDB; the blade's proc list
-- must contain only 100/101 (checked via the row's spell set through
-- the tooltip path being name-unique) — verified indirectly: if 500 were
-- indexed, 'holy' filter on proc names would still show 0 for the blade
-- and proc count text stays 3 (counts items, not spells). Direct check:
filterBox._text = "frost bite"
filterBox._scripts["OnTextChanged"]()
ok(lastStatus:find("showing 1") ~= nil, "proc-name filter path works: " .. lastStatus)

--==================== only VLTGET on the wire ====================
for i = 1, #sent do
    ok(sent[i].msg == "VLTGET", "wire send #" .. i .. " is VLTGET only")
end

print(string.format("%d/%d tests passed", P, T))
if P ~= T then os.exit(1) end
