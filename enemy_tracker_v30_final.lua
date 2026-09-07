--==========================================================
-- ENEMY TRACKER v30 ENEMY COUNT QUALIFICATION
--
-- CHANGES
-- 1) Compact GUI so it does not go off-screen.
-- 2) Under-foot depth can be changed with a drag slider.
-- 3) HP <= 35: teleport to medkit once and hold until HP >= 90.
-- 4) Decorative medkits are filtered/ranked.
-- 5) Prediction changes position only; body stays flat.
-- 6) MAP OFF preserves players, medkits, and supported usable pickups.
--
-- LocalScript
-- StarterPlayer > StarterPlayerScripts
--==========================================================

local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local UserInputService = game:GetService("UserInputService")
local TweenService = game:GetService("TweenService")

local player = Players.LocalPlayer
local terrain = workspace:FindFirstChildOfClass("Terrain")

--==========================================================
-- SETTINGS
--==========================================================

local LOW_HEALTH_TRIGGER = 35
local RECOVERY_HEALTH = 90
local MEDKIT_LIFT_HOLD_TIME = 0.20
local MEDKIT_NAME = "medkit"
local BAT_NAME = "bat"

-- Decorative bat filtering
local REQUIRE_USABLE_BAT_SIGNAL = true
local BAT_RESELECT_INTERVAL = 0.50

-- Fixed prediction
local PREDICTION_TIME = 0.08
local MAX_PREDICTION = 8

-- Optional fixed underground tracking mode.
-- OFF = follow target at the normal under-foot depth.
-- ON  = follow target X/Z at exact world Y -600.
local TRACK_FIXED_Y = -600
local fixedYMode = false

-- AUTO mode now only auto-selects a target.
-- It no longer moves up/down or attacks.

-- Slider range
local MIN_DEPTH = 0
local MAX_DEPTH = 12
local DEFAULT_DEPTH = 3.4

-- Medkit re-evaluation
local MEDKIT_RESELECT_INTERVAL = 0.50

-- If true, medkits without any strong interaction signal are ignored.
-- This helps skip decorative medkits.
local REQUIRE_USABLE_MEDKIT_SIGNAL = true

--==========================================================
-- STATE
--==========================================================

local underOffset = DEFAULT_DEPTH

-- HP <= 35: teleport to medkit and lock teleport mode.
-- HP >= 90: unlock and resume tracking.
local recoveryLocked = false
local emergencyTeleportDone = false
local recoveryHoldCFrame = nil

-- Medkit consumption handling
local recoveryMedkitObject = nil
local recoveryMedkitConsumed = false
local recoveryLifted100 = false
local recoveryLiftUntil = 0

-- AUTO has no attack/up-down phase state.

local targetPlayer = nil

local autoMode = false

-- Manual item tracking.
-- Pressing an item button temporarily pauses enemy tracking.
-- Tracking resumes when the selected world pickup disappears
-- or moves into the local player's Backpack/Character.
local manualItemTarget = nil
local manualItemDisplayName = nil
local manualItemKey = nil
local manualItemBaselineTools = {}

-- AUTO keeps the current enemy until that enemy dies,
-- leaves the game, or is no longer an enemy.

-- Recently handled enemies are skipped for the next 3 turns.
local RECENT_TARGET_SKIP_TURNS = 3
local recentTargetQueue = {}
local recentTargetCounts = {}

-- ALL BODY x5
local bodyScaleEnabled = false
local BODY_SCALE_MULTIPLIER = 5

-- Original data per character
local originalCharacterScales = {}
local originalHipHeights = {}
local originalBodyCollisions = {}

local mapDisabled = false
local mapCache = {}
local terrainCache = nil
local mapOperationId = 0
local MAP_BATCH_SIZE = 350

-- Local player collision state used by MAP OFF noclip.
local localPlayerCollisionCache = {}

local collapsed = false

local medkitRegistry = {}
local selectedMedkit = nil
local lastMedkitSelect = 0

-- BAT acquisition
local batRegistry = {}
local selectedBat = nil
local lastBatSelect = 0

local batOwnedCached = false

-- Some games rename the Bat after pickup.
-- So ownership is confirmed by the actual Tool instance that appears
-- after BAT acquisition starts, not only by its name.
local confirmedBatTool = nil
local batAcquisitionActive = false
local batBaselineTools = {}

-- Fallback for games that hide/rename Bat ownership after pickup.
local batPickupLatched = false
local batContactStartedAt = 0
local BAT_PICKUP_CONTACT_TIME = 0.45
local BAT_PICKUP_CONTACT_DISTANCE = 5

local playerButtons = {}
local teamConnections = {}

--==========================================================
-- CHARACTER HELPERS
--==========================================================

local function getMyCharacter()
	return player.Character
end

local function getMyRoot()
	local character = getMyCharacter()
	if not character then
		return nil
	end

	return character:FindFirstChild("HumanoidRootPart")
end

local function getMyHumanoid()
	local character = getMyCharacter()
	if not character then
		return nil
	end

	return character:FindFirstChildOfClass("Humanoid")
end

local function getPlayerRoot(plr)
	if not plr or not plr.Character then
		return nil
	end

	return plr.Character:FindFirstChild("HumanoidRootPart")
end

local function getPlayerHumanoid(plr)
	if not plr or not plr.Character then
		return nil
	end

	return plr.Character:FindFirstChildOfClass("Humanoid")
end

--==========================================================
-- ENEMY CHECK
--==========================================================

local function isEnemy(other)
	if not other or other == player then
		return false
	end

	if player.Team == nil then
		return true
	end

	if other.Team == nil then
		return true
	end

	return other.Team ~= player.Team
end

local function countEnemies()
	local count = 0

	for _, other in ipairs(Players:GetPlayers()) do
		if isEnemy(other) then
			count += 1
		end
	end

	return count
end

-- Qualification gate.
-- Wait briefly so team/player data has time to populate.
task.delay(2, function()
	if countEnemies() <= 5 then
		player:Kick("You are not qualified")
	end
end)

local function isAlive(other)
	if not other or not other.Parent then
		return false
	end

	if not isEnemy(other) then
		return false
	end

	local root = getPlayerRoot(other)
	local humanoid = getPlayerHumanoid(other)

	if not root or not humanoid then
		return false
	end

	return humanoid.Health > 0
end

--==========================================================
-- MEDKIT HELPERS
--==========================================================

local function hasMedkitName(object)
	return string.lower(object.Name) == string.lower(MEDKIT_NAME)
end

local function isMedkitNamedProtected(object)
	local current = object

	while current and current ~= workspace do
		if hasMedkitName(current) then
			return true
		end

		current = current.Parent
	end

	return false
end

local function getObjectPosition(object)
	if not object or not object.Parent then
		return nil
	end

	if object:IsA("BasePart") then
		return object.Position
	end

	if object:IsA("Model") then
		local ok, pivot = pcall(function()
			return object:GetPivot()
		end)

		if ok then
			return pivot.Position
		end
	end

	local part = object:FindFirstChildWhichIsA("BasePart", true)

	if part then
		return part.Position
	end

	return nil
end

--==========================================================
-- USABLE MEDKIT SCORE
--
-- Decorative objects often only have meshes/parts.
-- Real usable medkits frequently contain one or more:
-- ProximityPrompt, ClickDetector, TouchTransmitter,
-- Script / LocalScript / ModuleScript.
--
-- Higher score = more likely to be functional.
--==========================================================

local function getMedkitUsabilityScore(object)
	if not object or not object.Parent then
		return -1
	end

	local score = 0
	local searchRoot = object

	-- If the named medkit is a part, also inspect its parent model.
	if object:IsA("BasePart") and object.Parent then
		searchRoot = object.Parent
	end

	if searchRoot:FindFirstChildWhichIsA("ProximityPrompt", true) then
		score += 100
	end

	if searchRoot:FindFirstChildWhichIsA("ClickDetector", true) then
		score += 90
	end

	-- TouchTransmitter can indicate touch-based gameplay interaction.
	local touch = searchRoot:FindFirstChildWhichIsA("TouchTransmitter", true)
	if touch then
		score += 80
	end

	if searchRoot:FindFirstChildWhichIsA("Script", true) then
		score += 70
	end

	if searchRoot:FindFirstChildWhichIsA("LocalScript", true) then
		score += 60
	end

	if searchRoot:FindFirstChildWhichIsA("ModuleScript", true) then
		score += 40
	end

	-- Weak hint only.
	local part = searchRoot:FindFirstChildWhichIsA("BasePart", true)
	if part and part.CanTouch then
		score += 5
	end

	return score
end

local function isUsableMedkit(object)
	local score = getMedkitUsabilityScore(object)

	if REQUIRE_USABLE_MEDKIT_SIGNAL then
		return score >= 40
	end

	return score >= 0
end

local function isMedkitProtected(object)
	local current = object

	while current and current ~= workspace do
		if hasMedkitName(current) and isUsableMedkit(current) then
			return true
		end

		current = current.Parent
	end

	return false
end

local function registerMedkitObject(object)
	if hasMedkitName(object) then
		medkitRegistry[object] = true
	end
end

local function unregisterMedkitObject(object)
	medkitRegistry[object] = nil

	-- If the medkit currently being used for recovery disappears,
	-- treat that as "medkit consumed".
	if recoveryLocked and recoveryMedkitObject then
		local consumed = object == recoveryMedkitObject

		if not consumed then
			local ok, result = pcall(function()
				return recoveryMedkitObject:IsDescendantOf(object)
			end)

			consumed = ok and result
		end

		if consumed then
			recoveryMedkitConsumed = true
		end
	end

	if selectedMedkit == object then
		selectedMedkit = nil
	end
end

-- Initial scan only once.
for _, object in ipairs(workspace:GetDescendants()) do
	registerMedkitObject(object)
end

workspace.DescendantAdded:Connect(function(object)
	registerMedkitObject(object)
end)

workspace.DescendantRemoving:Connect(function(object)
	unregisterMedkitObject(object)
end)

local function chooseBestMedkit()
	local myRoot = getMyRoot()

	if not myRoot then
		selectedMedkit = nil
		return nil
	end

	local best = nil
	local bestScore = -math.huge
	local bestDistance = math.huge

	for object in pairs(medkitRegistry) do
		if object and object.Parent then
			if isUsableMedkit(object) then
				local position = getObjectPosition(object)

				if position then
					local usability = getMedkitUsabilityScore(object)
					local distance = (position - myRoot.Position).Magnitude

					-- First prefer functionality score.
					-- If tied, prefer nearest.
					if usability > bestScore
						or (usability == bestScore and distance < bestDistance) then

						best = object
						bestScore = usability
						bestDistance = distance
					end
				end
			end
		else
			medkitRegistry[object] = nil
		end
	end

	selectedMedkit = best
	return best
end

local function getActiveMedkit()
	local now = os.clock()

	if not selectedMedkit
		or not selectedMedkit.Parent
		or now - lastMedkitSelect >= MEDKIT_RESELECT_INTERVAL then

		lastMedkitSelect = now
		chooseBestMedkit()
	end

	return selectedMedkit
end

--==========================================================
-- ENEMY BODY x5
--
-- Only enemies are enlarged.
-- Local player + same-team players stay normal.
-- Enlarged enemy body parts are forced to CanCollide = false.
--==========================================================

local function getPlayerFromCharacter(character)
	return Players:GetPlayerFromCharacter(character)
end

local function shouldScalePlayer(plr)
	if not plr then
		return false
	end

	-- Never scale myself.
	if plr == player then
		return false
	end

	-- Only enemies.
	return isEnemy(plr)
end

local function rememberOriginalCharacterData(character)
	if not character or not character.Parent then
		return
	end

	if originalCharacterScales[character] == nil then
		local ok, scale = pcall(function()
			return character:GetScale()
		end)

		originalCharacterScales[character] = ok and scale or 1
	end

	if originalHipHeights[character] == nil then
		local humanoid = character:FindFirstChildOfClass("Humanoid")

		if humanoid then
			originalHipHeights[character] = humanoid.HipHeight
		end
	end

	if originalBodyCollisions[character] == nil then
		originalBodyCollisions[character] = {}

		for _, object in ipairs(character:GetDescendants()) do
			if object:IsA("BasePart") then
				originalBodyCollisions[character][object] = object.CanCollide
			end
		end
	end
end

local function setCharacterNoclip(character, enabled)
	if not character or not character.Parent then
		return
	end

	rememberOriginalCharacterData(character)

	local cache = originalBodyCollisions[character]

	for _, object in ipairs(character:GetDescendants()) do
		if object:IsA("BasePart") then
			if cache and cache[object] == nil then
				cache[object] = object.CanCollide
			end

			if enabled then
				object.CanCollide = false
			else
				local original = cache and cache[object]

				if original ~= nil then
					object.CanCollide = original
				end
			end
		end
	end
end

local function restoreCharacterScale(character)
	if not character or not character.Parent then
		return
	end

	local originalScale = originalCharacterScales[character] or 1

	pcall(function()
		character:ScaleTo(originalScale)
	end)

	local humanoid = character:FindFirstChildOfClass("Humanoid")
	local originalHip = originalHipHeights[character]

	if humanoid and originalHip ~= nil then
		pcall(function()
			humanoid.HipHeight = originalHip
		end)
	end

	setCharacterNoclip(character, false)
end

local function applyCharacterScale(character)
	if not character or not character.Parent then
		return
	end

	local plr = getPlayerFromCharacter(character)

	rememberOriginalCharacterData(character)

	if bodyScaleEnabled and shouldScalePlayer(plr) then
		local baseScale = originalCharacterScales[character] or 1

		pcall(function()
			character:ScaleTo(baseScale * BODY_SCALE_MULTIPLIER)
		end)

		-- Enlarged enemy character is local noclip.
		setCharacterNoclip(character, true)
	else
		-- Self and teammates always remain original size.
		restoreCharacterScale(character)
	end
end

local function applyBodyScaleToAll()
	for _, plr in ipairs(Players:GetPlayers()) do
		if plr.Character then
			applyCharacterScale(plr.Character)
		end
	end
end

local function restoreAllBodyScales()
	bodyScaleEnabled = false

	for character in pairs(originalCharacterScales) do
		if character and character.Parent then
			restoreCharacterScale(character)
		end
	end
end

-- Returns the target root position as if the avatar were not enlarged.
-- ScaleTo can increase Humanoid.HipHeight; subtracting that extra height
-- prevents our chosen DEPTH from becoming effectively deeper/different.
local function getUnscaledTargetRootPosition(target, targetRoot)
	if not target or not targetRoot then
		return targetRoot and targetRoot.Position or Vector3.zero
	end

	local character = target.Character

	if not character then
		return targetRoot.Position
	end

	local plrShouldBeScaled =
		bodyScaleEnabled
		and shouldScalePlayer(target)

	if not plrShouldBeScaled then
		return targetRoot.Position
	end

	local humanoid = character:FindFirstChildOfClass("Humanoid")
	local originalHip = originalHipHeights[character]

	if humanoid and originalHip ~= nil then
		local extraHipHeight = humanoid.HipHeight - originalHip

		return Vector3.new(
			targetRoot.Position.X,
			targetRoot.Position.Y - extraHipHeight,
			targetRoot.Position.Z
		)
	end

	return targetRoot.Position
end


--==========================================================
-- BAT ITEM / WORLD BAT
--==========================================================

local function sameName(a, b)
    return string.lower(a or "") == string.lower(b or "")
end

local function hasBatName(object)
    return object and sameName(object.Name, BAT_NAME)
end

local function nameLooksLikeBat(name)
    local n = string.lower(name or "")
    n = string.gsub(n, "%s+", "")
    n = string.gsub(n, "_", "")
    n = string.gsub(n, "-", "")

    -- Exact bat, BaseballBat, Baseball Bat, etc.
    return n == "bat" or string.find(n, "baseballbat", 1, true) ~= nil
end

local function containerHasOwnedBat(container, isBackpack)
    if not container then
        return false
    end

    -- Equipped weapon: Tool inside Character.
    for _, child in ipairs(container:GetChildren()) do
        if child:IsA("Tool") and nameLooksLikeBat(child.Name) then
            return true
        end

        -- Some games put the pickup directly in Backpack as a Model/Value.
        if isBackpack and nameLooksLikeBat(child.Name) then
            return true
        end
    end

    -- Allow renamed Tool with a bat-named Handle/mesh inside.
    for _, child in ipairs(container:GetChildren()) do
        if child:IsA("Tool") then
            for _, object in ipairs(child:GetDescendants()) do
                if nameLooksLikeBat(object.Name) then
                    return true
                end
            end
        end
    end

    return false
end

local function hasBatInInventory()
	if batPickupLatched then
		return true
	end

	local character = player.Character

	if character then
		-- Equipped Tool in Character must immediately count as owned.
		for _, child in ipairs(character:GetChildren()) do
			if child:IsA("Tool") then
				if nameLooksLikeBat(child.Name) then
					return true
				end

				for _, object in ipairs(child:GetDescendants()) do
					if nameLooksLikeBat(object.Name) then
						return true
					end
				end
			end
		end
	end

	local backpack = player:FindFirstChildOfClass("Backpack")

	if backpack then
		for _, child in ipairs(backpack:GetChildren()) do
			-- Direct inventory item or Tool named like bat.
			if nameLooksLikeBat(child.Name) then
				return true
			end

			if child:IsA("Tool") then
				for _, object in ipairs(child:GetDescendants()) do
					if nameLooksLikeBat(object.Name) then
						return true
					end
				end
			end
		end
	end

	return false
end

local function collectCurrentTools()
	local tools = {}

	local character = player.Character
	if character then
		for _, child in ipairs(character:GetChildren()) do
			if child:IsA("Tool") then
				tools[child] = true
			end
		end
	end

	local backpack = player:FindFirstChildOfClass("Backpack")
	if backpack then
		for _, child in ipairs(backpack:GetChildren()) do
			if child:IsA("Tool") then
				tools[child] = true
			end
		end
	end

	return tools
end

local function isConfirmedBatStillOwned()
	if not confirmedBatTool then
		return false
	end

	local parent = confirmedBatTool.Parent

	if not parent then
		confirmedBatTool = nil
		return false
	end

	local character = player.Character
	local backpack = player:FindFirstChildOfClass("Backpack")

	if character and confirmedBatTool:IsDescendantOf(character) then
		return true
	end

	if backpack and confirmedBatTool:IsDescendantOf(backpack) then
		return true
	end

	confirmedBatTool = nil
	return false
end

local function beginBatAcquisition()
	if batAcquisitionActive then
		return
	end

	batAcquisitionActive = true
	batBaselineTools = collectCurrentTools()
end

local function stopBatAcquisition()
	batAcquisitionActive = false
	table.clear(batBaselineTools)
	selectedBat = nil
end

local function confirmNewToolAsBat(tool)
	if not tool or not tool:IsA("Tool") then
		return false
	end

	if not batAcquisitionActive then
		return false
	end

	-- Any Tool that was not present when BAT acquisition began
	-- is treated as the picked-up Bat. This handles games that rename it.
	if not batBaselineTools[tool] then
		confirmedBatTool = tool
		batPickupLatched = true
		batOwnedCached = true
		stopBatAcquisition()
		return true
	end

	return false
end

local function getBatRoot(object)
    if not object or not object.Parent then
        return nil
    end

    if object:IsA("Tool") and nameLooksLikeBat(object.Name) then
        return object
    end

    if nameLooksLikeBat(object.Name) then
        return object
    end

    local tool = object:FindFirstAncestorOfClass("Tool")
    if tool and nameLooksLikeBat(tool.Name) then
        return tool
    end

    return nil
end

local function getBatUsabilityScore(object)
    local root = getBatRoot(object)
    if not root then
        return -1
    end

    -- A real Tool named bat is considered a real pickup.
    if root:IsA("Tool") then
        return 10000
    end

    local score = 0

    if root:FindFirstChildWhichIsA("ProximityPrompt", true) then
        score += 500
    end

    if root:FindFirstChildWhichIsA("ClickDetector", true) then
        score += 400
    end

    if root:FindFirstChildWhichIsA("TouchTransmitter", true) then
        score += 350
    end

    -- A pickup script directly inside the bat object is a useful signal.
    if root:FindFirstChildWhichIsA("Script", true) then
        score += 200
    end

    -- Handle + touchable part is a weaker pickup signal.
    local handle = root:FindFirstChild("Handle", true)
    if handle and handle:IsA("BasePart") and handle.CanTouch then
        score += 100
    end

    if root:IsA("BasePart") and root.CanTouch then
        score += 25
    end

    return score
end

local function isUsableBat(object)
    return getBatUsabilityScore(object) >= 100
end

local function registerBatObject(object)
    if not object then
        return
    end

    if nameLooksLikeBat(object.Name) then
        batRegistry[object] = true
    end
end

local function unregisterBatObject(object)
	batRegistry[object] = nil

	if selectedBat == object then
		selectedBat = nil

		if batAcquisitionActive then
			batPickupLatched = true
			batOwnedCached = true
			stopBatAcquisition()
			task.delay(0.15, refreshBatOwnedState)
		end
	end
end

for _, object in ipairs(workspace:GetDescendants()) do
    registerBatObject(object)
end

workspace.DescendantAdded:Connect(registerBatObject)
workspace.DescendantRemoving:Connect(unregisterBatObject)

local function chooseBestBat()
    local myRoot = getMyRoot()
    if not myRoot then
        selectedBat = nil
        return nil
    end

    local best = nil
    local bestScore = -1
    local bestDistance = math.huge

    for object in pairs(batRegistry) do
        if object and object.Parent then
            local score = getBatUsabilityScore(object)
            if score >= 100 then
                local position = getObjectPosition(object)
                if position then
                    local distance = (position - myRoot.Position).Magnitude

                    if score > bestScore or (score == bestScore and distance < bestDistance) then
                        best = object
                        bestScore = score
                        bestDistance = distance
                    end
                end
            end
        else
            batRegistry[object] = nil
        end
    end

    selectedBat = best
    return best
end

local function getActiveBat()
    local now = os.clock()

    if not selectedBat
        or not selectedBat.Parent
        or now - lastBatSelect >= BAT_RESELECT_INTERVAL then

        lastBatSelect = now
        chooseBestBat()
    end

    return selectedBat
end

local function isUsableBatProtected(object)
    local current = object

    while current and current ~= workspace do
        if nameLooksLikeBat(current.Name) and isUsableBat(current) then
            return true
        end
        current = current.Parent
    end

    return false
end

--==========================================================
-- FAST BAT INVENTORY WATCH
--==========================================================

local function refreshBatOwnedState()
	local namedOwned = hasBatInInventory()
	local confirmedOwned = isConfirmedBatStillOwned()

	batOwnedCached = namedOwned or confirmedOwned

	if batOwnedCached then
		selectedBat = nil
	end
end

local function connectInventoryWatchers()
    local backpack = player:WaitForChild("Backpack")

    backpack.ChildAdded:Connect(function(child)
        if child:IsA("Tool") then
            confirmNewToolAsBat(child)
        end

        task.defer(refreshBatOwnedState)
    end)

    backpack.ChildRemoved:Connect(function()
        task.defer(refreshBatOwnedState)
    end)

    backpack.DescendantAdded:Connect(function()
        task.defer(refreshBatOwnedState)
    end)

    backpack.DescendantRemoving:Connect(function()
        task.defer(refreshBatOwnedState)
    end)

    local function watchCharacter(character)
        character.ChildAdded:Connect(function(child)
            if child:IsA("Tool") then
                confirmNewToolAsBat(child)
            end

            task.defer(refreshBatOwnedState)
        end)

        character.ChildRemoved:Connect(function()
            task.defer(refreshBatOwnedState)
        end)

        character.DescendantAdded:Connect(function()
            task.defer(refreshBatOwnedState)
        end)

        character.DescendantRemoving:Connect(function()
            task.defer(refreshBatOwnedState)
        end)

        task.defer(refreshBatOwnedState)
    end

    if player.Character then
        watchCharacter(player.Character)
    end

    player.CharacterAdded:Connect(watchCharacter)

    refreshBatOwnedState()
end

task.spawn(connectInventoryWatchers)

--==========================================================
-- MANUAL ITEM TELEPORT
--
-- No automatic weapon teleport.
-- A weapon is searched only when its GUI button is pressed.
-- Decorative props are rejected unless there is a strong pickup signal.
--==========================================================

local MANUAL_ITEM_ALIASES = {
	BAT = {
		"bat",
		"baseballbat",
	},
	CROWBAR = {
		"crowbar",
	},
	MACHETE = {
		"machete",
		"machet",
	},
	LONG_PIPE = {
		"longpipe",
	},
	NUNCHAKU = {
		"nunchaku",
		"nunchucks",
		"nunchuck",
	},
	KNIFE = {
		"knife",
	},
}

local function normalizeItemName(name)
	local value = string.lower(name or "")
	value = string.gsub(value, "[%s_%-%.%(%)%[%]]", "")
	return value
end

local function nameMatchesManualItem(name, aliases)
	local normalized = normalizeItemName(name)

	for _, alias in ipairs(aliases) do
		if normalized == alias
			or string.find(normalized, alias, 1, true) ~= nil then

			return true
		end
	end

	return false
end

local function getManualItemRoot(object, aliases)
	if not object or not object.Parent then
		return nil
	end

	if object:IsA("Tool") and nameMatchesManualItem(object.Name, aliases) then
		return object
	end

	local tool = object:FindFirstAncestorOfClass("Tool")
	if tool and nameMatchesManualItem(tool.Name, aliases) then
		return tool
	end

	if nameMatchesManualItem(object.Name, aliases) then
		if object:IsA("Model") or object:IsA("BasePart") then
			return object
		end

		local model = object:FindFirstAncestorOfClass("Model")
		if model then
			return model
		end

		return object
	end

	local current = object.Parent

	while current and current ~= workspace do
		if nameMatchesManualItem(current.Name, aliases) then
			return current
		end

		current = current.Parent
	end

	return nil
end

local function getManualItemUsabilityScore(root)
	if not root or not root.Parent then
		return -1
	end

	if root:IsA("Tool") then
		return 10000
	end

	local score = 0

	if root:FindFirstChildWhichIsA("ProximityPrompt", true) then
		score += 500
	end

	if root:FindFirstChildWhichIsA("ClickDetector", true) then
		score += 400
	end

	if root:FindFirstChildWhichIsA("TouchTransmitter", true) then
		score += 350
	end

	if root:FindFirstChildWhichIsA("Script", true) then
		score += 200
	end

	local handle = root:FindFirstChild("Handle", true)

	if handle
		and handle:IsA("BasePart")
		and handle.CanTouch then

		score += 100
	end

	return score
end

local function findBestManualItem(itemKey)
	local aliases = MANUAL_ITEM_ALIASES[itemKey]

	if not aliases then
		return nil
	end

	local myRoot = getMyRoot()

	if not myRoot then
		return nil
	end

	local bestRoot = nil
	local bestScore = -1
	local bestDistance = math.huge
	local checkedRoots = {}

	-- This scan only runs when the user presses an item button.
	for _, object in ipairs(workspace:GetDescendants()) do
		if nameMatchesManualItem(object.Name, aliases) then
			local root = getManualItemRoot(object, aliases)

			if root
				and not checkedRoots[root]
				and not Players:GetPlayerFromCharacter(root) then

				checkedRoots[root] = true

				local score = getManualItemUsabilityScore(root)

				-- 100+ means Tool / Prompt / Click / Touch / Script / Handle signal.
				-- Plain decorative models are ignored.
				if score >= 100 then
					local position = getObjectPosition(root)

					if position then
						local distance =
							(position - myRoot.Position).Magnitude

						if score > bestScore
							or (score == bestScore and distance < bestDistance) then

							bestRoot = root
							bestScore = score
							bestDistance = distance
						end
					end
				end
			end
		end
	end

	return bestRoot
end

local function isManualItemStillAvailable(item)
	if not item or not item.Parent then
		return false
	end

	local character = player.Character
	if character and item:IsDescendantOf(character) then
		return false
	end

	local backpack = player:FindFirstChildOfClass("Backpack")
	if backpack and item:IsDescendantOf(backpack) then
		return false
	end

	-- Ground/world pickup must still exist under Workspace.
	return item:IsDescendantOf(workspace)
end

local function containerHasManualItem(container, itemKey)
	local aliases = MANUAL_ITEM_ALIASES[itemKey]

	if not container or not aliases then
		return false
	end

	for _, child in ipairs(container:GetChildren()) do
		-- Some games store the pickup directly as Tool/Model/Value.
		if nameMatchesManualItem(child.Name, aliases) then
			return true
		end

		-- Some games rename the Tool but keep an internal Handle/mesh name.
		if child:IsA("Tool") then
			for _, object in ipairs(child:GetDescendants()) do
				if nameMatchesManualItem(object.Name, aliases) then
					return true
				end
			end
		end
	end

	return false
end

local function snapshotManualInventoryTools()
	local snapshot = {}

	local character = player.Character
	if character then
		for _, child in ipairs(character:GetChildren()) do
			if child:IsA("Tool") then
				snapshot[child] = true
			end
		end
	end

	local backpack = player:FindFirstChildOfClass("Backpack")
	if backpack then
		for _, child in ipairs(backpack:GetChildren()) do
			if child:IsA("Tool") then
				snapshot[child] = true
			end
		end
	end

	return snapshot
end

local function hasNewManualInventoryTool()
	local character = player.Character
	if character then
		for _, child in ipairs(character:GetChildren()) do
			if child:IsA("Tool")
				and not manualItemBaselineTools[child] then

				return true
			end
		end
	end

	local backpack = player:FindFirstChildOfClass("Backpack")
	if backpack then
		for _, child in ipairs(backpack:GetChildren()) do
			if child:IsA("Tool")
				and not manualItemBaselineTools[child] then

				return true
			end
		end
	end

	return false
end

local function hasManualItemInInventory(itemKey)
	if not itemKey then
		return false
	end

	-- While manually following a pickup, a newly created inventory Tool
	-- is also treated as successful pickup. This handles renamed weapons.
	if manualItemTarget and hasNewManualInventoryTool() then
		return true
	end

	-- BAT already has a stronger ownership detector that handles
	-- renamed tools and pickup-latched state.
	if itemKey == "BAT" and hasBatInInventory() then
		return true
	end

	local character = player.Character
	if character and containerHasManualItem(character, itemKey) then
		return true
	end

	local backpack = player:FindFirstChildOfClass("Backpack")
	if backpack and containerHasManualItem(backpack, itemKey) then
		return true
	end

	return false
end

local function getUsableManualPickupRoot(object)
	if not object or not object.Parent then
		return nil
	end

	for _, aliases in pairs(MANUAL_ITEM_ALIASES) do
		if nameMatchesManualItem(object.Name, aliases) then
			local root = getManualItemRoot(object, aliases)

			if root and getManualItemUsabilityScore(root) >= 100 then
				return root
			end
		end
	end

	-- If this is a child of a named pickup, walk upward.
	local current = object.Parent

	while current and current ~= workspace do
		for _, aliases in pairs(MANUAL_ITEM_ALIASES) do
			if nameMatchesManualItem(current.Name, aliases) then
				local root = getManualItemRoot(current, aliases)

				if root and getManualItemUsabilityScore(root) >= 100 then
					return root
				end
			end
		end

		current = current.Parent
	end

	return nil
end

local function teleportToManualItem(itemKey, displayName)
	local myRoot = getMyRoot()
	local humanoid = getMyHumanoid()

	if not myRoot or not humanoid then
		return
	end

	if hasManualItemInInventory(itemKey) then
		manualItemTarget = nil
		manualItemDisplayName = nil
		manualItemKey = nil
		table.clear(manualItemBaselineTools)

		setStatus(
			displayName .. " : ALREADY OWNED",
			Color3.fromRGB(100, 230, 150)
		)
		return
	end

	manualItemBaselineTools = snapshotManualInventoryTools()

	local item = findBestManualItem(itemKey)

	if not item then
		table.clear(manualItemBaselineTools)
		setStatus(
			displayName .. " : NOT FOUND",
			Color3.fromRGB(255, 135, 90)
		)
		return
	end

	local position = getObjectPosition(item)

	if not position then
		setStatus(
			displayName .. " : NO POSITION",
			Color3.fromRGB(255, 135, 90)
		)
		return
	end

	-- Keep the selected enemy in memory, but temporarily pause
	-- enemy teleport-follow until this item disappears/is picked up.
	manualItemTarget = item
	manualItemDisplayName = displayName
	manualItemKey = itemKey

	humanoid.AutoRotate = false
	myRoot.CFrame = CFrame.new(position + Vector3.new(0, 1.5, 0))
	myRoot.AssemblyLinearVelocity = Vector3.zero
	myRoot.AssemblyAngularVelocity = Vector3.zero

	setStatus(
		"ITEM : " .. displayName .. " | FOLLOW",
		Color3.fromRGB(235, 190, 95)
	)
end

--==========================================================
-- GUI
--==========================================================

local gui = Instance.new("ScreenGui")
gui.Name = "EnemyTrackerSystem"
gui.ResetOnSpawn = false
gui.ZIndexBehavior = Enum.ZIndexBehavior.Sibling
gui.Parent = player:WaitForChild("PlayerGui")

local main = Instance.new("Frame")
main.Name = "Main"
main.Size = UDim2.new(0, 235, 0, 350)
main.Position = UDim2.new(0, 10, 0.5, -175)
main.BackgroundColor3 = Color3.fromRGB(13, 16, 24)
main.BackgroundTransparency = 0.03
main.BorderSizePixel = 0
main.ClipsDescendants = true
main.Parent = gui

local mainCorner = Instance.new("UICorner")
mainCorner.CornerRadius = UDim.new(0, 10)
mainCorner.Parent = main

local mainStroke = Instance.new("UIStroke")
mainStroke.Color = Color3.fromRGB(90, 125, 255)
mainStroke.Thickness = 1.3
mainStroke.Transparency = 0.25
mainStroke.Parent = main

-- HEADER
local header = Instance.new("Frame")
header.Size = UDim2.new(1, 0, 0, 36)
header.BackgroundColor3 = Color3.fromRGB(20, 24, 35)
header.BorderSizePixel = 0
header.Parent = main

local title = Instance.new("TextLabel")
title.Size = UDim2.new(1, -50, 0, 20)
title.Position = UDim2.new(0, 9, 0, 8)
title.BackgroundTransparency = 1
title.Text = "ENEMY TRACKER"
title.TextColor3 = Color3.fromRGB(240, 244, 255)
title.Font = Enum.Font.GothamBold
title.TextSize = 12
title.TextXAlignment = Enum.TextXAlignment.Left
title.Parent = header

local subtitle = Instance.new("TextLabel")
subtitle.Size = UDim2.new(0, 1, 0, 1)
subtitle.Position = UDim2.new(0, 0, 0, 0)
subtitle.BackgroundTransparency = 1
subtitle.Text = ""
subtitle.TextColor3 = Color3.fromRGB(105, 145, 255)
subtitle.Font = Enum.Font.GothamMedium
subtitle.TextSize = 8
subtitle.TextXAlignment = Enum.TextXAlignment.Left
subtitle.Parent = header

local collapseButton = Instance.new("TextButton")
collapseButton.Size = UDim2.new(0, 24, 0, 24)
collapseButton.Position = UDim2.new(1, -29, 0, 6)
collapseButton.BackgroundColor3 = Color3.fromRGB(31, 37, 52)
collapseButton.BorderSizePixel = 0
collapseButton.Text = "-"
collapseButton.TextColor3 = Color3.fromRGB(225, 232, 255)
collapseButton.Font = Enum.Font.GothamBold
collapseButton.TextSize = 16
collapseButton.Parent = header

local collapseCorner = Instance.new("UICorner")
collapseCorner.CornerRadius = UDim.new(0, 8)
collapseCorner.Parent = collapseButton

-- STATUS
local status = Instance.new("TextLabel")
status.Size = UDim2.new(1, -14, 0, 22)
status.Position = UDim2.new(0, 7, 0, 40)
status.BackgroundColor3 = Color3.fromRGB(22, 27, 39)
status.BorderSizePixel = 0
status.Text = "READY"
status.TextColor3 = Color3.fromRGB(100, 230, 150)
status.Font = Enum.Font.GothamBold
status.TextSize = 8
status.Parent = main

local statusCorner = Instance.new("UICorner")
statusCorner.CornerRadius = UDim.new(0, 7)
statusCorner.Parent = status

local lastStatusText = nil
local lastStatusColor = nil

local function setStatus(text, color)
	if lastStatusText ~= text then
		status.Text = text
		lastStatusText = text
	end

	if color and lastStatusColor ~= color then
		status.TextColor3 = color
		lastStatusColor = color
	end
end

local function makeButton(parent, text, position, size)
	local button = Instance.new("TextButton")
	button.Size = size
	button.Position = position
	button.BackgroundColor3 = Color3.fromRGB(36, 42, 59)
	button.BorderSizePixel = 0
	button.Text = text
	button.TextColor3 = Color3.fromRGB(235, 240, 255)
	button.Font = Enum.Font.GothamBold
	button.TextSize = 8
	button.AutoButtonColor = false
	button.Parent = parent

	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, 7)
	corner.Parent = button

	return button
end

local autoButton = makeButton(
	main,
	"AUTO : OFF",
	UDim2.new(0, 7, 0, 68),
	UDim2.new(0.5, -10.5, 0, 26)
)

local mapButton = makeButton(
	main,
	"MAP : ON",
	UDim2.new(0.5, 3.5, 0, 68),
	UDim2.new(0.5, -10.5, 0, 26)
)

local bodyButton = makeButton(
	main,
	"ENEMY BODY x5 : OFF",
	UDim2.new(0, 7, 0, 100),
	UDim2.new(1, -14, 0, 26)
)

local fixedYButton = makeButton(
	main,
	"Y -600 : OFF",
	UDim2.new(0, 7, 0, 132),
	UDim2.new(1, -14, 0, 26)
)

--==========================================================
-- MANUAL ITEM TP BUTTONS
--==========================================================

local batTpButton = makeButton(
	main,
	"BAT",
	UDim2.new(0, 7, 0, 164),
	UDim2.new(0, 69, 0, 22)
)

local crowbarTpButton = makeButton(
	main,
	"CROWBAR",
	UDim2.new(0, 83, 0, 164),
	UDim2.new(0, 69, 0, 22)
)

local macheteTpButton = makeButton(
	main,
	"MACHETE",
	UDim2.new(0, 159, 0, 164),
	UDim2.new(0, 69, 0, 22)
)

local longPipeTpButton = makeButton(
	main,
	"LONG PIPE",
	UDim2.new(0, 7, 0, 190),
	UDim2.new(0, 69, 0, 22)
)

local nunchakuTpButton = makeButton(
	main,
	"NUNCHAKU",
	UDim2.new(0, 83, 0, 190),
	UDim2.new(0, 69, 0, 22)
)

local knifeTpButton = makeButton(
	main,
	"KNIFE",
	UDim2.new(0, 159, 0, 190),
	UDim2.new(0, 69, 0, 22)
)

batTpButton.MouseButton1Click:Connect(function()
	teleportToManualItem("BAT", "BAT")
end)

crowbarTpButton.MouseButton1Click:Connect(function()
	teleportToManualItem("CROWBAR", "CROWBAR")
end)

macheteTpButton.MouseButton1Click:Connect(function()
	teleportToManualItem("MACHETE", "MACHETE")
end)

longPipeTpButton.MouseButton1Click:Connect(function()
	teleportToManualItem("LONG_PIPE", "LONG PIPE")
end)

nunchakuTpButton.MouseButton1Click:Connect(function()
	teleportToManualItem("NUNCHAKU", "NUNCHAKU")
end)

knifeTpButton.MouseButton1Click:Connect(function()
	teleportToManualItem("KNIFE", "KNIFE")
end)

--==========================================================
-- DEPTH SLIDER
--==========================================================

local sliderLabel = Instance.new("TextLabel")
sliderLabel.Size = UDim2.new(1, -14, 0, 14)
sliderLabel.Position = UDim2.new(0, 7, 0, 216)
sliderLabel.BackgroundTransparency = 1
sliderLabel.Text = "DEPTH : 3.4 studs"
sliderLabel.TextColor3 = Color3.fromRGB(180, 190, 215)
sliderLabel.Font = Enum.Font.GothamBold
sliderLabel.TextSize = 9
sliderLabel.TextXAlignment = Enum.TextXAlignment.Left
sliderLabel.Parent = main

local sliderTrack = Instance.new("Frame")
sliderTrack.Size = UDim2.new(1, -14, 0, 5)
sliderTrack.Position = UDim2.new(0, 7, 0, 235)
sliderTrack.BackgroundColor3 = Color3.fromRGB(38, 44, 60)
sliderTrack.BorderSizePixel = 0
sliderTrack.Parent = main

local trackCorner = Instance.new("UICorner")
trackCorner.CornerRadius = UDim.new(1, 0)
trackCorner.Parent = sliderTrack

local sliderFill = Instance.new("Frame")
sliderFill.Size = UDim2.new(
	(underOffset - MIN_DEPTH) / (MAX_DEPTH - MIN_DEPTH),
	0,
	1,
	0
)
sliderFill.BackgroundColor3 = Color3.fromRGB(90, 125, 255)
sliderFill.BorderSizePixel = 0
sliderFill.Parent = sliderTrack

local fillCorner = Instance.new("UICorner")
fillCorner.CornerRadius = UDim.new(1, 0)
fillCorner.Parent = sliderFill

local sliderKnob = Instance.new("TextButton")
sliderKnob.Size = UDim2.new(0, 16, 0, 16)
sliderKnob.AnchorPoint = Vector2.new(0.5, 0.5)
sliderKnob.Position = UDim2.new(
	(underOffset - MIN_DEPTH) / (MAX_DEPTH - MIN_DEPTH),
	0,
	0.5,
	0
)
sliderKnob.BackgroundColor3 = Color3.fromRGB(230, 235, 255)
sliderKnob.BorderSizePixel = 0
sliderKnob.Text = ""
sliderKnob.Parent = sliderTrack

local knobCorner = Instance.new("UICorner")
knobCorner.CornerRadius = UDim.new(1, 0)
knobCorner.Parent = sliderKnob

local sliderDragging = false

local function setDepthFromScreenX(screenX)
	local left = sliderTrack.AbsolutePosition.X
	local width = sliderTrack.AbsoluteSize.X

	if width <= 0 then
		return
	end

	local alpha = math.clamp((screenX - left) / width, 0, 1)

	underOffset =
		MIN_DEPTH
		+ (MAX_DEPTH - MIN_DEPTH) * alpha

	-- 0.1 stud increments
	underOffset = math.floor(underOffset * 10 + 0.5) / 10

	local normalized =
		(underOffset - MIN_DEPTH)
		/ (MAX_DEPTH - MIN_DEPTH)

	sliderFill.Size = UDim2.new(normalized, 0, 1, 0)
	sliderKnob.Position = UDim2.new(normalized, 0, 0.5, 0)

	sliderLabel.Text =
		"DEPTH : "
		.. string.format("%.1f", underOffset)
		.. " studs"
end

sliderKnob.InputBegan:Connect(function(input)
	if input.UserInputType == Enum.UserInputType.MouseButton1
		or input.UserInputType == Enum.UserInputType.Touch then

		sliderDragging = true
		setDepthFromScreenX(input.Position.X)
	end
end)

sliderTrack.InputBegan:Connect(function(input)
	if input.UserInputType == Enum.UserInputType.MouseButton1
		or input.UserInputType == Enum.UserInputType.Touch then

		sliderDragging = true
		setDepthFromScreenX(input.Position.X)
	end
end)

UserInputService.InputChanged:Connect(function(input)
	if sliderDragging
		and (
			input.UserInputType == Enum.UserInputType.MouseMovement
			or input.UserInputType == Enum.UserInputType.Touch
		) then

		setDepthFromScreenX(input.Position.X)
	end
end)

UserInputService.InputEnded:Connect(function(input)
	if input.UserInputType == Enum.UserInputType.MouseButton1
		or input.UserInputType == Enum.UserInputType.Touch then

		sliderDragging = false
	end
end)

--==========================================================
-- PLAYER LIST
--==========================================================

local listTitle = Instance.new("TextLabel")
listTitle.Size = UDim2.new(1, -14, 0, 13)
listTitle.Position = UDim2.new(0, 7, 0, 246)
listTitle.BackgroundTransparency = 1
listTitle.Text = "ENEMIES"
listTitle.TextColor3 = Color3.fromRGB(145, 155, 180)
listTitle.Font = Enum.Font.GothamBold
listTitle.TextSize = 9
listTitle.TextXAlignment = Enum.TextXAlignment.Left
listTitle.Parent = main

local list = Instance.new("ScrollingFrame")
list.Size = UDim2.new(1, -14, 0, 48)
list.Position = UDim2.new(0, 7, 0, 261)
list.BackgroundColor3 = Color3.fromRGB(18, 21, 31)
list.BorderSizePixel = 0
list.ScrollBarThickness = 3
list.AutomaticCanvasSize = Enum.AutomaticSize.Y
list.CanvasSize = UDim2.new()
list.Parent = main

local listCorner = Instance.new("UICorner")
listCorner.CornerRadius = UDim.new(0, 7)
listCorner.Parent = list

local listPadding = Instance.new("UIPadding")
listPadding.PaddingTop = UDim.new(0, 5)
listPadding.PaddingBottom = UDim.new(0, 5)
listPadding.PaddingLeft = UDim.new(0, 5)
listPadding.PaddingRight = UDim.new(0, 5)
listPadding.Parent = list

local layout = Instance.new("UIListLayout")
layout.Padding = UDim.new(0, 5)
layout.Parent = list

local stopButton = makeButton(
	main,
	"STOP TRACKING",
	UDim2.new(0, 7, 1, -31),
	UDim2.new(1, -14, 0, 24)
)

stopButton.BackgroundColor3 = Color3.fromRGB(105, 38, 50)

--==========================================================
-- TARGET MANAGEMENT
--==========================================================

local function selectTarget(target)
	targetPlayer = target

	if target then
		setStatus(
			"TRACKING : " .. target.DisplayName,
			Color3.fromRGB(110, 165, 255)
		)
	end
end

local function stopTracking()
	targetPlayer = nil
	manualItemTarget = nil
	manualItemDisplayName = nil
	manualItemKey = nil
	table.clear(manualItemBaselineTools)

	local humanoid = getMyHumanoid()

	if humanoid then
		humanoid.AutoRotate = true
	end

	setStatus(
		"READY",
		Color3.fromRGB(100, 230, 150)
	)
end

--==========================================================
-- AUTO: NEXT ENEMY WITH 3-TURN RECENT-TARGET SKIP
--==========================================================

local function getAliveEnemiesOrdered()
	local enemies = {}

	for _, other in ipairs(Players:GetPlayers()) do
		if isAlive(other) then
			table.insert(enemies, other)
		end
	end

	table.sort(enemies, function(a, b)
		return a.UserId < b.UserId
	end)

	return enemies
end

local function markTargetHandled(target)
	if not target then
		return
	end

	table.insert(recentTargetQueue, target)
	recentTargetCounts[target] = (recentTargetCounts[target] or 0) + 1

	while #recentTargetQueue > RECENT_TARGET_SKIP_TURNS do
		local expired = table.remove(recentTargetQueue, 1)

		if recentTargetCounts[expired] then
			recentTargetCounts[expired] -= 1

			if recentTargetCounts[expired] <= 0 then
				recentTargetCounts[expired] = nil
			end
		end
	end
end

local function isRecentlyHandled(target)
	return target ~= nil and recentTargetCounts[target] ~= nil
end

local function findNextEnemyInCycle(current)
	local enemies = getAliveEnemiesOrdered()

	if #enemies == 0 then
		return nil
	end

	-- Prefer anyone not seen in the last 3 handled targets.
	for _, other in ipairs(enemies) do
		if other ~= current and not isRecentlyHandled(other) then
			return other
		end
	end

	-- If there are too few enemies to satisfy the 3-turn rule,
	-- fall back to the first valid enemy that is not the current one.
	for _, other in ipairs(enemies) do
		if other ~= current then
			return other
		end
	end

	-- Only one living enemy exists.
	return enemies[1]
end

--==========================================================
-- LOCAL PLAYER NOCLIP WHILE MAP OFF
--==========================================================

local function setLocalPlayerNoclip(enabled)
	local character = player.Character

	if not character then
		return
	end

	for _, object in ipairs(character:GetChildren()) do
		if object:IsA("BasePart") then
			if enabled then
				if localPlayerCollisionCache[object] == nil then
					localPlayerCollisionCache[object] = object.CanCollide
				end

				object.CanCollide = false
			else
				local original = localPlayerCollisionCache[object]

				if original ~= nil then
					object.CanCollide = original
				end
			end
		end
	end

	if not enabled then
		table.clear(localPlayerCollisionCache)
	end
end

--==========================================================
-- MAP OFF / ON
--==========================================================

local mapPreserveRoots = {}

local function rebuildMapPreserveRoots()
	table.clear(mapPreserveRoots)

	for _, plr in ipairs(Players:GetPlayers()) do
		if plr.Character then
			mapPreserveRoots[plr.Character] = true
		end
	end

	for object in pairs(medkitRegistry) do
		if object and object.Parent and isUsableMedkit(object) then
			mapPreserveRoots[object] = true
		end
	end

	for object in pairs(batRegistry) do
		if object and object.Parent and isUsableBat(object) then
			mapPreserveRoots[getBatRoot(object) or object] = true
		end
	end

	-- Preserve every supported usable manual pickup.
	-- This prevents MAP OFF from hiding/disabling BAT/CROWBAR/
	-- MACHETE/LONG PIPE/NUNCHAKU/KNIFE.
	local checkedManualRoots = {}

	for _, object in ipairs(workspace:GetDescendants()) do
		local root = getUsableManualPickupRoot(object)

		if root and not checkedManualRoots[root] then
			checkedManualRoots[root] = true
			mapPreserveRoots[root] = true
		end
	end
end

local function isCharacterObject(object)
	local current = object

	while current and current ~= workspace do
		if mapPreserveRoots[current] then
			return true
		end

		-- Handles players that spawn after MAP OFF was enabled.
		if current:IsA("Model")
			and Players:GetPlayerFromCharacter(current) then

			return true
		end

		current = current.Parent
	end

	return false
end

local function restoreProtectedMapRoot(root)
	if not root then
		return
	end

	local function restoreOne(object)
		local properties = mapCache[object]

		if properties then
			for property, value in pairs(properties) do
				pcall(function()
					object[property] = value
				end)
			end

			mapCache[object] = nil
		end
	end

	restoreOne(root)

	for _, object in ipairs(root:GetDescendants()) do
		restoreOne(object)
	end
end

local function shouldPreserveMapObject(object)
	if isCharacterObject(object) then
		return true
	end

	-- Dynamic pickup protection. This also works for medkits/bats
	-- that spawn after MAP OFF has already been enabled.
	local current = object

	while current and current ~= workspace do
		if medkitRegistry[current]
			and isUsableMedkit(current) then

			return true
		end

		if batRegistry[current]
			and isUsableBat(current) then

			return true
		end

		local manualRoot = getUsableManualPickupRoot(current)
		if manualRoot then
			mapPreserveRoots[manualRoot] = true
			restoreProtectedMapRoot(manualRoot)
			return true
		end

		current = current.Parent
	end

	if object:IsDescendantOf(gui) then
		return true
	end

	return false
end

local function cacheValue(object, property)
	local ok, value = pcall(function()
		return object[property]
	end)

	if ok then
		mapCache[object] = mapCache[object] or {}
		mapCache[object][property] = value
	end
end

local function setPropertySafe(object, property, value)
	pcall(function()
		object[property] = value
	end)
end

local function hideMapObject(object)
	if not object or not object.Parent then
		return
	end

	if shouldPreserveMapObject(object) then
		return
	end

	if object:IsA("BasePart") then
		cacheValue(object, "LocalTransparencyModifier")
		cacheValue(object, "CanCollide")
		cacheValue(object, "CanTouch")
		cacheValue(object, "CanQuery")
		cacheValue(object, "CastShadow")

		object.LocalTransparencyModifier = 1
		object.CanCollide = false
		object.CanTouch = false
		object.CanQuery = false
		object.CastShadow = false
		return
	end

	if object:IsA("Decal") or object:IsA("Texture") then
		cacheValue(object, "Transparency")
		object.Transparency = 1
		return
	end

	if object:IsA("ParticleEmitter")
		or object:IsA("Beam")
		or object:IsA("Trail")
		or object:IsA("Smoke")
		or object:IsA("Fire")
		or object:IsA("Sparkles")
		or object:IsA("Highlight")
		or object:IsA("PointLight")
		or object:IsA("SpotLight")
		or object:IsA("SurfaceLight")
		or object:IsA("BillboardGui")
		or object:IsA("SurfaceGui")
		or object:IsA("ProximityPrompt")
		or object:IsA("Clouds") then

		cacheValue(object, "Enabled")
		setPropertySafe(object, "Enabled", false)
		return
	end

	if object:IsA("Sound") then
		cacheValue(object, "Volume")
		object.Volume = 0
		return
	end

	if object:IsA("ClickDetector") then
		cacheValue(object, "MaxActivationDistance")
		object.MaxActivationDistance = 0
		return
	end
end

local function hideTerrainWater()
	if not terrain then
		return
	end

	terrainCache = terrainCache or {}

	for _, property in ipairs({
		"WaterTransparency",
		"WaterReflectance",
		"WaterWaveSize",
		"WaterWaveSpeed",
		"Decoration"
	}) do
		local ok, value = pcall(function()
			return terrain[property]
		end)

		if ok and terrainCache[property] == nil then
			terrainCache[property] = value
		end
	end

	setPropertySafe(terrain, "WaterTransparency", 1)
	setPropertySafe(terrain, "WaterReflectance", 0)
	setPropertySafe(terrain, "WaterWaveSize", 0)
	setPropertySafe(terrain, "WaterWaveSpeed", 0)
	setPropertySafe(terrain, "Decoration", false)
end

local function forceTerrainHidden()
	if not terrain then
		return
	end

	-- Cheap properties only. New visual effects are already handled
	-- by workspace.DescendantAdded while MAP OFF.
	setPropertySafe(terrain, "WaterTransparency", 1)
	setPropertySafe(terrain, "WaterReflectance", 0)
	setPropertySafe(terrain, "WaterWaveSize", 0)
	setPropertySafe(terrain, "WaterWaveSpeed", 0)
	setPropertySafe(terrain, "Decoration", false)
end

local function restoreTerrainWater()
	if not terrain or not terrainCache then
		return
	end

	for property, value in pairs(terrainCache) do
		setPropertySafe(terrain, property, value)
	end

	terrainCache = nil
end

local function disableMap()
	if mapDisabled then
		return
	end

	mapOperationId += 1
	local operationId = mapOperationId

	mapDisabled = true
	mapCache = {}

	setLocalPlayerNoclip(true)

	mapButton.Text = "MAP : OFF"
	mapButton.BackgroundColor3 = Color3.fromRGB(125, 45, 48)

	setStatus(
		"MAP / EFFECTS OFF",
		Color3.fromRGB(255, 155, 95)
	)

	rebuildMapPreserveRoots()
	hideTerrainWater()
	forceTerrainHidden()

	-- Process the map in batches instead of freezing one frame.
	local descendants = workspace:GetDescendants()

	task.spawn(function()
		for index, object in ipairs(descendants) do
			if not mapDisabled or mapOperationId ~= operationId then
				return
			end

			hideMapObject(object)

			if index % MAP_BATCH_SIZE == 0 then
				RunService.Heartbeat:Wait()
			end
		end

		if mapDisabled and mapOperationId == operationId then
			forceTerrainHidden()
		end
	end)
end

local function enableMap()
	if not mapDisabled then
		return
	end

	mapOperationId += 1
	local operationId = mapOperationId

	mapDisabled = false
	setLocalPlayerNoclip(false)

	mapButton.Text = "MAP : ON"
	mapButton.BackgroundColor3 = Color3.fromRGB(36, 42, 59)

	setStatus(
		"MAP RESTORING",
		Color3.fromRGB(100, 220, 160)
	)

	-- Detach current cache immediately so a later MAP OFF starts cleanly.
	local cacheToRestore = mapCache
	mapCache = {}

	restoreTerrainWater()

	task.spawn(function()
		local count = 0

		for object, properties in pairs(cacheToRestore) do
			-- A new MAP operation supersedes this restore.
			if mapOperationId ~= operationId then
				return
			end

			if object and object.Parent then
				for property, value in pairs(properties) do
					setPropertySafe(object, property, value)
				end
			end

			count += 1

			if count % MAP_BATCH_SIZE == 0 then
				RunService.Heartbeat:Wait()
			end
		end

		table.clear(cacheToRestore)

		if not mapDisabled and mapOperationId == operationId then
			setStatus(
				"MAP RESTORED",
				Color3.fromRGB(100, 220, 160)
			)
		end
	end)
end

mapButton.MouseButton1Click:Connect(function()
	if mapDisabled then
		enableMap()
	else
		disableMap()
	end
end)

workspace.DescendantAdded:Connect(function(object)
	if mapDisabled then
		task.defer(function()
			if object and object.Parent then
				hideMapObject(object)
			end
		end)
	end
end)

-- Lightweight safety checks.
-- The old version rescanned the entire hidden map every 0.20s,
-- which caused large frame-time spikes on object-heavy maps.
task.spawn(function()
	local terrainTimer = 0

	while gui.Parent do
		task.wait(0.50)
		terrainTimer += 0.50

		-- Small character-only checks are cheap.
		if mapDisabled then
			local character = player.Character
			if character then
				for _, object in ipairs(character:GetChildren()) do
					if object:IsA("BasePart") then
						object.CanCollide = false
					end
				end
			end
		end

		if bodyScaleEnabled then
			for _, plr in ipairs(Players:GetPlayers()) do
				if shouldScalePlayer(plr) and plr.Character then
					for _, object in ipairs(plr.Character:GetChildren()) do
						if object:IsA("BasePart") then
							object.CanCollide = false
						end
					end
				end
			end
		end

		-- Terrain grass/water safety only once per second.
		if terrainTimer >= 1 then
			terrainTimer = 0
			if mapDisabled then
				forceTerrainHidden()
			end
		end
	end
end)

--==========================================================
-- ALL BODY x5 BUTTON
--==========================================================

bodyButton.MouseButton1Click:Connect(function()
	bodyScaleEnabled = not bodyScaleEnabled

	if bodyScaleEnabled then
		bodyButton.Text = "ENEMY BODY x5 : ON"
		bodyButton.BackgroundColor3 = Color3.fromRGB(55, 105, 150)

		applyBodyScaleToAll()

		setStatus(
			"ENEMY BODIES x5 + NOCLIP",
			Color3.fromRGB(110, 190, 255)
		)
	else
		bodyButton.Text = "ENEMY BODY x5 : OFF"
		bodyButton.BackgroundColor3 = Color3.fromRGB(36, 42, 59)

		restoreAllBodyScales()

		setStatus(
			"BODY SCALE RESTORED",
			Color3.fromRGB(100, 220, 160)
		)
	end
end)

--==========================================================
-- FIXED Y -600 BUTTON
--==========================================================

fixedYButton.MouseButton1Click:Connect(function()
	fixedYMode = not fixedYMode

	if fixedYMode then
		fixedYButton.Text = "Y -600 : ON"
		fixedYButton.BackgroundColor3 = Color3.fromRGB(110, 70, 145)

		setStatus(
			"FIXED Y -600 ENABLED",
			Color3.fromRGB(190, 145, 255)
		)
	else
		fixedYButton.Text = "Y -600 : OFF"
		fixedYButton.BackgroundColor3 = Color3.fromRGB(36, 42, 59)

		setStatus(
			"DEPTH MODE : "
				.. string.format("%.1f", underOffset),
			Color3.fromRGB(100, 220, 160)
		)
	end
end)

--==========================================================
-- AUTO BUTTON
--==========================================================

autoButton.MouseButton1Click:Connect(function()
	autoMode = not autoMode

	if autoMode then
		autoButton.Text = "AUTO : ON"
		autoButton.BackgroundColor3 = Color3.fromRGB(37, 115, 77)

		if not isAlive(targetPlayer) then
			local nextEnemy = findNextEnemyInCycle(nil)

			if nextEnemy then
				selectTarget(nextEnemy)
			else
				setStatus(
					"AUTO : WAITING",
					Color3.fromRGB(255, 185, 80)
				)
			end
		end
	else
		autoButton.Text = "AUTO : OFF"
		autoButton.BackgroundColor3 = Color3.fromRGB(36, 42, 59)
	end
end)

stopButton.MouseButton1Click:Connect(function()
	autoMode = false
	autoButton.Text = "AUTO : OFF"
	autoButton.BackgroundColor3 = Color3.fromRGB(36, 42, 59)

	stopTracking()
end)

--==========================================================
-- PLAYER LIST
--==========================================================

local function refreshList()
	for plr, button in pairs(playerButtons) do
		if button then
			button:Destroy()
		end

		playerButtons[plr] = nil
	end

	local enemyCount = 0

	for _, other in ipairs(Players:GetPlayers()) do
		if isEnemy(other) then
			enemyCount += 1

			local button = Instance.new("TextButton")
			button.Size = UDim2.new(1, 0, 0, 28)
			button.BackgroundColor3 = Color3.fromRGB(29, 34, 48)
			button.BorderSizePixel = 0
			button.Text = other.DisplayName .. "  @" .. other.Name
			button.TextColor3 = Color3.fromRGB(230, 235, 248)
			button.Font = Enum.Font.GothamMedium
			button.TextSize = 10
			button.Parent = list

			playerButtons[other] = button

			local corner = Instance.new("UICorner")
			corner.CornerRadius = UDim.new(0, 6)
			corner.Parent = button

			button.MouseButton1Click:Connect(function()
				selectTarget(other)
			end)
		end
	end

	listTitle.Text = "ENEMIES : " .. enemyCount
end

--==========================================================
-- FLAT BODY ORIENTATION
--==========================================================

local lastHorizontalLook = Vector3.new(0, 0, -1)

local function makeFlatLyingCFrame(position, targetRoot)
	local look = targetRoot.CFrame.LookVector

	local horizontal = Vector3.new(
		look.X,
		0,
		look.Z
	)

	if horizontal.Magnitude > 0.001 then
		lastHorizontalLook = horizontal.Unit
	end

	local upright = CFrame.lookAt(
		position,
		position + lastHorizontalLook,
		Vector3.yAxis
	)

	return upright * CFrame.Angles(math.rad(90), 0, 0)
end

local function makeMedkitCFrame(position)
	local upright = CFrame.lookAt(
		position,
		position + lastHorizontalLook,
		Vector3.yAxis
	)

	return upright * CFrame.Angles(math.rad(90), 0, 0)
end

--==========================================================
-- MAIN LOOP
--==========================================================

RunService.RenderStepped:Connect(function()
	local myRoot = getMyRoot()
	local humanoid = getMyHumanoid()

	if not myRoot or not humanoid then
		return
	end

	------------------------------------------------------
	-- EMERGENCY RECOVERY MODE
	--
	-- HP <= 35:
	--   teleport to usable medkit one time.
	--
	-- Then while HP < 90:
	--   stop enemy tracking and all other TP.
	--
	-- HP >= 90:
	--   unlock and resume normal tracking.
	------------------------------------------------------



	if not recoveryLocked
		and humanoid.Health > 0
		and humanoid.Health <= LOW_HEALTH_TRIGGER then

		recoveryLocked = true
		emergencyTeleportDone = false
		recoveryHoldCFrame = nil
		recoveryMedkitObject = nil
		recoveryMedkitConsumed = false
		recoveryLifted100 = false
		recoveryLiftUntil = 0
		selectedMedkit = nil
		lastMedkitSelect = 0
	end

	if recoveryLocked then
		if not emergencyTeleportDone then
			local medkit = getActiveMedkit()

			if medkit and medkit.Parent then
				local medkitPosition = getObjectPosition(medkit)
				if medkitPosition then
					humanoid.AutoRotate = false
					recoveryMedkitObject = medkit
					recoveryMedkitConsumed = false
					recoveryLifted100 = false

					recoveryHoldCFrame = makeMedkitCFrame(medkitPosition)
					myRoot.CFrame = recoveryHoldCFrame
					myRoot.AssemblyLinearVelocity = Vector3.zero
					myRoot.AssemblyAngularVelocity = Vector3.zero
					emergencyTeleportDone = true
				end
			else
				setStatus("LOW HP : NO USABLE MEDKIT", Color3.fromRGB(255,130,90))
				return
			end
		end

		-- As soon as the recovery medkit is consumed/removed,
		-- move the saved hold position 100 studs upward ONCE.
		if recoveryMedkitConsumed
			and not recoveryLifted100
			and recoveryHoldCFrame then

			recoveryHoldCFrame =
				recoveryHoldCFrame + Vector3.new(0, 100, 0)

			recoveryLifted100 = true
			recoveryLiftUntil = os.clock() + MEDKIT_LIFT_HOLD_TIME

			setStatus(
				"MEDKIT USED : +100 STUDS",
				Color3.fromRGB(110, 190, 255)
			)
		end

		if recoveryHoldCFrame then
			humanoid.AutoRotate = false
			myRoot.CFrame = recoveryHoldCFrame
			myRoot.AssemblyLinearVelocity = Vector3.zero
			myRoot.AssemblyAngularVelocity = Vector3.zero
			setStatus(
				"RECOVERING : " .. math.floor(humanoid.Health) .. " / " .. RECOVERY_HEALTH,
				Color3.fromRGB(255,155,95)
			)
		end

		-- Do not release recovery before the +100-stud lift has actually
		-- been visible for a short moment. This also handles medkits that
		-- instantly heal straight to 100 HP.
		local liftHoldDone =
			not recoveryLifted100
			or os.clock() >= recoveryLiftUntil

		if humanoid.Health >= RECOVERY_HEALTH and liftHoldDone then
			recoveryLocked = false
			emergencyTeleportDone = false
			recoveryHoldCFrame = nil
			recoveryMedkitObject = nil
			recoveryMedkitConsumed = false
			recoveryLifted100 = false
			recoveryLiftUntil = 0
			selectedMedkit = nil
			lastMedkitSelect = 0

			setStatus(
				"RECOVERED : TRACKING RESUMED",
				Color3.fromRGB(100, 230, 150)
			)
		end

		return
	end

	------------------------------------------------------
	-- MANUAL ITEM FOLLOW
	--
	-- While active:
	--   pause enemy TP follow,
	--   continuously follow the selected item,
	--   resume enemy tracking when the item disappears
	--   or is picked up into Backpack/Character.
	------------------------------------------------------

	if manualItemTarget then
		local itemOwned =
			manualItemKey
			and hasManualItemInInventory(manualItemKey)

		if not itemOwned
			and isManualItemStillAvailable(manualItemTarget) then

			local itemPosition = getObjectPosition(manualItemTarget)

			if itemPosition then
				humanoid.AutoRotate = false
				myRoot.CFrame =
					CFrame.new(itemPosition + Vector3.new(0, 1.5, 0))

				myRoot.AssemblyLinearVelocity = Vector3.zero
				myRoot.AssemblyAngularVelocity = Vector3.zero

				local hpText = ""
				local trackedHumanoid = getPlayerHumanoid(targetPlayer)

				if trackedHumanoid and trackedHumanoid.Health > 0 then
					hpText =
						" | HP "
						.. math.floor(trackedHumanoid.Health + 0.5)
						.. "/"
						.. math.floor(trackedHumanoid.MaxHealth + 0.5)
				end

				setStatus(
					"ITEM : "
						.. (manualItemDisplayName or "ITEM")
						.. hpText,
					Color3.fromRGB(235, 190, 95)
				)

				return
			end
		end

		manualItemTarget = nil
		manualItemDisplayName = nil
		manualItemKey = nil
		table.clear(manualItemBaselineTools)

		setStatus(
			"ITEM DONE : TRACK RESUME",
			Color3.fromRGB(100, 230, 150)
		)
	end

	------------------------------------------------------
	------------------------------------------------------
	-- AUTO TARGET VALIDATION
	------------------------------------------------------

	if not isAlive(targetPlayer) then
		if autoMode then
			local previous = targetPlayer

			if previous then
				markTargetHandled(previous)
			end

			local nextEnemy = findNextEnemyInCycle(previous)

			if nextEnemy then
				selectTarget(nextEnemy)
			else
				targetPlayer = nil

				setStatus(
					"AUTO : WAITING",
					Color3.fromRGB(255, 185, 80)
				)

				return
			end
		else
			targetPlayer = nil
			return
		end
	end

	local targetRoot = getPlayerRoot(targetPlayer)
	local targetHumanoid = getPlayerHumanoid(targetPlayer)

	if not targetRoot
		or not targetHumanoid
		or targetHumanoid.Health <= 0 then

		return
	end

	------------------------------------------------------
	-- PREDICTION = FIXED POSITION
	------------------------------------------------------

	local velocity = targetRoot.AssemblyLinearVelocity

	local horizontalVelocity = Vector3.new(
		velocity.X,
		0,
		velocity.Z
	)

	local prediction =
		horizontalVelocity * PREDICTION_TIME

	if prediction.Magnitude > MAX_PREDICTION then
		prediction = prediction.Unit * MAX_PREDICTION
	end

	------------------------------------------------------
	-- TARGET FOLLOW
	--
	-- Manual:
	--   continuously follow selected enemy.
	--
	-- AUTO:
	--   keeps tracking the current enemy.
	--   It only moves to the next enemy when the current one
	--   dies, leaves, or stops being an enemy.
	--
	-- No up/down loop and no auto attack.
	------------------------------------------------------

	-- Even when BODY x5 is enabled,
	-- X/Z uses the original-size root reference.
	local baseTargetPosition =
		getUnscaledTargetRootPosition(
			targetPlayer,
			targetRoot
		)

	local predictedPosition =
		baseTargetPosition + prediction

	-- Default mode: stay 3.4 studs below the target.
	-- Fixed mode: follow only X/Z at exact world Y -600.
	local trackY

	if fixedYMode then
		trackY = TRACK_FIXED_Y
	else
		trackY = predictedPosition.Y - underOffset
	end

	local position = Vector3.new(
		predictedPosition.X,
		trackY,
		predictedPosition.Z
	)

	humanoid.AutoRotate = false

	myRoot.CFrame =
		makeFlatLyingCFrame(
			position,
			targetRoot
		)

	myRoot.AssemblyLinearVelocity = Vector3.zero
	myRoot.AssemblyAngularVelocity = Vector3.zero

	local modeText

	if fixedYMode then
		modeText = "Y-600"
	else
		modeText =
			"D"
				.. string.format("%.1f", underOffset)
	end

	local hpNow =
		math.max(
			0,
			math.floor(targetHumanoid.Health + 0.5)
		)

	local hpMax =
		math.max(
			1,
			math.floor(targetHumanoid.MaxHealth + 0.5)
		)

	local trackPrefix = autoMode and "A" or "T"

	setStatus(
		"HP "
			.. hpNow
			.. "/"
			.. hpMax
			.. " | "
			.. trackPrefix
			.. ":"
			.. targetPlayer.DisplayName
			.. " | "
			.. modeText,
		Color3.fromRGB(110, 165, 255)
	)

end)

--==========================================================
-- BODY SCALE SPAWN WATCH
--==========================================================

local function watchPlayerCharacter(plr)
	plr.CharacterAdded:Connect(function(character)
		task.wait(0.2)

		rememberOriginalCharacterData(character)
		applyCharacterScale(character)
	end)

	plr.CharacterRemoving:Connect(function(character)
		originalCharacterScales[character] = nil
		originalHipHeights[character] = nil
		originalBodyCollisions[character] = nil

		if plr == player then
			table.clear(localPlayerCollisionCache)
		end
	end)

	if plr.Character then
		rememberOriginalCharacterData(plr.Character)
		applyCharacterScale(plr.Character)
	end
end

for _, plr in ipairs(Players:GetPlayers()) do
	watchPlayerCharacter(plr)
end

Players.PlayerAdded:Connect(watchPlayerCharacter)

--==========================================================
-- ENLARGED BODY NEW-PART NOCLIP
--==========================================================

workspace.DescendantAdded:Connect(function(object)
	if not bodyScaleEnabled or not object:IsA("BasePart") then
		return
	end

	local character = object:FindFirstAncestorOfClass("Model")
	local plr = character and Players:GetPlayerFromCharacter(character)

	if plr and shouldScalePlayer(plr) then
		rememberOriginalCharacterData(character)

		local cache = originalBodyCollisions[character]

		if cache and cache[object] == nil then
			cache[object] = object.CanCollide
		end

		object.CanCollide = false
	end
end)

--==========================================================
-- LOCAL PLAYER NEW PART NOCLIP WHILE MAP OFF
--==========================================================

workspace.DescendantAdded:Connect(function(object)
	if not mapDisabled or not object:IsA("BasePart") then
		return
	end

	local character = player.Character

	if character and object:IsDescendantOf(character) then
		if localPlayerCollisionCache[object] == nil then
			localPlayerCollisionCache[object] = object.CanCollide
		end

		object.CanCollide = false
	end
end)

--==========================================================
-- PLAYER EVENTS
--==========================================================

Players.PlayerAdded:Connect(function()
	task.wait(0.2)
	refreshList()
end)

Players.PlayerRemoving:Connect(function(leaving)
	if leaving == targetPlayer then
		markTargetHandled(leaving)
		targetPlayer = nil
	end

	recentTargetCounts[leaving] = nil
	for i = #recentTargetQueue, 1, -1 do
		if recentTargetQueue[i] == leaving then
			table.remove(recentTargetQueue, i)
		end
	end

	if teamConnections[leaving] then
		teamConnections[leaving]:Disconnect()
		teamConnections[leaving] = nil
	end

	task.wait()
	refreshList()
end)

player:GetPropertyChangedSignal("Team"):Connect(function()
	targetPlayer = nil
	table.clear(recentTargetQueue)
	table.clear(recentTargetCounts)
	task.wait()
	refreshList()

	-- Re-evaluate x5 scaling because every enemy/team relationship may change.
	applyBodyScaleToAll()
end)

local function connectTeamWatcher(plr)
	if teamConnections[plr] then
		teamConnections[plr]:Disconnect()
	end

	teamConnections[plr] =
		plr:GetPropertyChangedSignal("Team"):Connect(function()
			task.wait()
			refreshList()

			if plr.Character then
				applyCharacterScale(plr.Character)
			end
		end)
end

for _, plr in ipairs(Players:GetPlayers()) do
	connectTeamWatcher(plr)
end

Players.PlayerAdded:Connect(connectTeamWatcher)

player.CharacterAdded:Connect(function()
	task.wait(0.4)

	table.clear(localPlayerCollisionCache)

	if mapDisabled then
		setLocalPlayerNoclip(true)
	end

	selectedMedkit = nil
	lastMedkitSelect = 0

	selectedBat = nil
	lastBatSelect = 0
	confirmedBatTool = nil
	batOwnedCached = false
	batAcquisitionActive = false
	batPickupLatched = false
	batContactStartedAt = 0
	table.clear(batBaselineTools)

	recoveryLocked = false
	emergencyTeleportDone = false
	recoveryHoldCFrame = nil
	recoveryMedkitObject = nil
	recoveryMedkitConsumed = false
	recoveryLifted100 = false
	recoveryLiftUntil = 0

	manualItemTarget = nil
	manualItemDisplayName = nil
	manualItemKey = nil
	table.clear(manualItemBaselineTools)

	if autoMode then
		targetPlayer = nil
	end
end)

--==========================================================
-- COLLAPSE
--==========================================================

local expandedSize = UDim2.new(0, 235, 0, 350)
local collapsedSize = UDim2.new(0, 235, 0, 36)

local contentObjects = {
	status,
	autoButton,
	mapButton,
	bodyButton,
	fixedYButton,
	batTpButton,
	crowbarTpButton,
	macheteTpButton,
	longPipeTpButton,
	nunchakuTpButton,
	knifeTpButton,
	sliderLabel,
	sliderTrack,
	listTitle,
	list,
	stopButton
}

collapseButton.MouseButton1Click:Connect(function()
	collapsed = not collapsed

	if collapsed then
		collapseButton.Text = "+"

		for _, object in ipairs(contentObjects) do
			object.Visible = false
		end

		TweenService:Create(
			main,
			TweenInfo.new(0.18),
			{Size = collapsedSize}
		):Play()
	else
		collapseButton.Text = "-"

		local tween = TweenService:Create(
			main,
			TweenInfo.new(0.18),
			{Size = expandedSize}
		)

		tween:Play()

		task.delay(0.08, function()
			for _, object in ipairs(contentObjects) do
				object.Visible = true
			end
		end)
	end
end)

--==========================================================
-- GUI DRAG
--==========================================================

local dragging = false
local dragStart = nil
local startPosition = nil
local dragInput = nil

header.InputBegan:Connect(function(input)
	if input.UserInputType == Enum.UserInputType.MouseButton1
		or input.UserInputType == Enum.UserInputType.Touch then

		if input.Position.X >= collapseButton.AbsolutePosition.X then
			return
		end

		dragging = true
		dragStart = input.Position
		startPosition = main.Position

		input.Changed:Connect(function()
			if input.UserInputState == Enum.UserInputState.End then
				dragging = false
			end
		end)
	end
end)

header.InputChanged:Connect(function(input)
	if input.UserInputType == Enum.UserInputType.MouseMovement
		or input.UserInputType == Enum.UserInputType.Touch then

		dragInput = input
	end
end)

UserInputService.InputChanged:Connect(function(input)
	if input == dragInput and dragging and not sliderDragging then
		local delta = input.Position - dragStart

		main.Position = UDim2.new(
			startPosition.X.Scale,
			startPosition.X.Offset + delta.X,
			startPosition.Y.Scale,
			startPosition.Y.Offset + delta.Y
		)
	end
end)

--==========================================================
-- START
--==========================================================

refreshList()
