(function () {
  "use strict";

  const canvas = document.getElementById("game");
  const ctx = canvas.getContext("2d");
  const chatEl = document.getElementById("chat");
  const chatLog = document.getElementById("chatLog");
  const chatInput = document.getElementById("chatInput");
  const chatSend = document.getElementById("chatSend");
  const btnBattle = document.getElementById("btnBattle");
  const btnDigTrade = document.getElementById("btnDigTrade");
  const btnShop = document.getElementById("btnShop");
  const modeOverlay = document.getElementById("modeOverlay");
  const usernameInput = document.getElementById("usernameInput");
  const respawnBtn = document.getElementById("respawnBtn");

  const VIEW_TILES_X = 32;
  const VIEW_TILES_Y = 16;
  let TILE = 24;
  const WORLD_W = 250;
  const WORLD_H = 300;
  const BOTTOM_UI_ROWS = 6;
  let PLAYER_W = 10;
  let PLAYER_H = 20;
  const GROUND_SKIN = 2;
  function digReach() { return TILE * 2.25; }
  const BULLET_SPEED_MIN = 420;
  const BULLET_SPEED_MAX = 980;
  const MORTAR_SPEED_MIN = 360;
  const MORTAR_SPEED_MAX = 1280;
  const CANNON_MAX_RANGE_TILES = 17;
  function cannonMaxRangePx() { return CANNON_MAX_RANGE_TILES * TILE; }
  const SUPER_RARE_CHANCE = 1 / 500;
  const WEAPON_DROP_CHANCE = 0.08;
  const MORTAR_DROP_CHANCE = 0.04;
  const MAX_HP = 3;

  let GRAVITY = 2400;
  const JUMP_V = -580;
  const MAX_FALL = 900;

  const CANNON_META_NONE = 0;
  const CANNON_META_PREMADE = 1;
  const CANNON_META_PLAYER = 2;

  const T_AIR = 0;
  const T_DIRT = 1;
  const T_BEDROCK = 2;
  const T_WOOD = 3;
  const T_BRICK = 4;
  const T_CANNON = 5;
  const T_SAW = 6;
  const T_WATER = 7;
  const T_LAVA = 8;
  const T_LADDER = 9;
  const T_SLOPE_L = 10;
  const T_SLOPE_R = 11;

  const SOLID = new Set([T_DIRT, T_BEDROCK, T_WOOD, T_BRICK, T_CANNON, T_SAW, T_LAVA, T_SLOPE_L, T_SLOPE_R]);
  const DIGGABLE = new Set([T_DIRT, T_WOOD, T_BRICK, T_CANNON, T_SAW, T_WATER, T_LAVA, T_LADDER, T_SLOPE_L, T_SLOPE_R]);

  const RARE_DIG_CHANCE = 1 / 100;

  const ITEM_CATALOG = {
    pickaxe: { kind: "pickaxe", name: "Pickaxe" },
    mortar: { kind: "mortar", name: "Mortar" },
    blade: { kind: "blade", name: "Blade" },
    rusty_blaster: { kind: "weapon", name: "Rusty Blaster" },
    shard_pistol: { kind: "weapon", name: "Shard Pistol" },
    core_drill_gun: { kind: "weapon", name: "Core Drill Gun" },
    crystal_smg: { kind: "weapon", name: "Crystal SMG" },
    void_carbine: { kind: "weapon", name: "Void Carbine" },
    mythic: { kind: "weapon", name: "MYTHIC" },
    grenade_launcher: { kind: "weapon", name: "Grenade Launcher" },
    cannon_block: { kind: "build", name: "Cannon", tile: T_CANNON },
    saw_block: { kind: "build", name: "Saw", tile: T_SAW },
    water_block: { kind: "build", name: "Water", tile: T_WATER },
    lava_block: { kind: "build", name: "Lava", tile: T_LAVA },
    dirt_block: { kind: "build", name: "Dirt", tile: T_DIRT },
    ladder_block: { kind: "build", name: "Ladder", tile: T_LADDER },
    slope_l_block: { kind: "build", name: "Slope \\", tile: T_SLOPE_L },
    slope_r_block: { kind: "build", name: "Slope /", tile: T_SLOPE_R },
  };

  let digTimeMs = 1250;
  let moveSpeed = 200;
  let baseGravity = 2400;
  let baseMoveSpeed = 200;
  let started = false;
  let showChat = true;
  let showCenterInventory = false;
  let username = "miner";
  let gameMode = "Battle";

  let tiles;
  let cannonMeta;
  let camX = 0;
  let camY = 0;
  let mouseX = 0;
  let mouseY = 0;
  let mouseDownLeft = false;
  const keys = Object.create(null);

  let toast = { text: "", until: 0 };
  let digState = null;
  let bullets = [];
  let drops = [];
  let cannonLines = [];
  let premadeCannonList = [];
  let worldSurfaceY = 55;

  let lastWeaponFire = 0;
  const WEAPON_FIRE_DELAY_MS = 1500;
  let damageFlashUntil = 0;
  let superRareBannerUntil = 0;
  let camFollow = null;
  /** Smooth camera (world px); targets follow bullet or player */
  let camSmoothX = 0;
  let camSmoothY = 0;
  let camInitialized = false;
  let sawAnim = 0;
  let floatPhase = 0;
  let dragInv = null;
  /** Per-tile dig time accumulated (ms); does not reset when you stop digging */
  const digProgress = new Map();
  let wallJumpCooldown = 0;
  let trajSmoothPts = [];
  let lastPlaceKey = "";
  let placeCooldown = 0;

  const player = {
    x: 0, y: 0, vx: 0, vy: 0, grounded: false,
    hp: MAX_HP,
    hpDisplay: MAX_HP,
    lastDamageAt: 0,
    dead: false,
    chatBubble: { text: "", until: 0 },
  };

  const invWeapons = new Array(8).fill(null);
  const invBuilds = new Array(8).fill(null);
  const backpack = new Array(32).fill(null);
  let hotbarPage = "weapons";
  let selectedSlot = 0;

  function activeHotbar() { return hotbarPage === "weapons" ? invWeapons : invBuilds; }
  function syncPlayerSize() {
    PLAYER_W = Math.max(10, Math.round(TILE * 0.58));
    PLAYER_H = Math.max(18, Math.round(TILE * 1.55));
  }

  function playerHitbox() {
    const inset = Math.max(2, Math.round(TILE * 0.08));
    return { x: player.x + inset, y: player.y + inset, w: PLAYER_W - inset * 2, h: PLAYER_H - inset * 2 };
  }

  function log(text) { chatLog.textContent += text + "\n"; chatLog.scrollTop = chatLog.scrollHeight; }
  /** Plain name for system/chat (strip ^0–^9 color codes) */
  function displayUsername() {
    return username.replace(/\^[0-9]/g, "");
  }
  function tmsg(text, ms) { toast.text = text; toast.until = performance.now() + ms; }
  function idx(tx, ty) { return ty * WORLD_W + tx; }
  function inBounds(tx, ty) { return tx >= 0 && ty >= 0 && tx < WORLD_W && ty < WORLD_H; }
  function getTile(tx, ty) { return inBounds(tx, ty) ? tiles[idx(tx, ty)] : T_BEDROCK; }
  function setTile(tx, ty, v) {
    if (!inBounds(tx, ty)) return;
    const i = idx(tx, ty);
    if (tiles[i] !== v) digProgress.delete(tx + "," + ty);
    tiles[i] = v;
    if (v !== T_CANNON) cannonMeta[i] = CANNON_META_NONE;
  }
  function isSolidTile(t) { return SOLID.has(t); }
  function isDiggableTile(t) { return DIGGABLE.has(t); }

  /** Slope triangle fill test (world px) */
  function slopeSolidAt(px, py, t, tx, ty) {
    const lx = px - tx * TILE;
    const ly = py - ty * TILE;
    const u = lx / TILE;
    const v = ly / TILE;
    if (t === T_SLOPE_R) return u + v >= 1 - 0.015;
    if (t === T_SLOPE_L) return (1 - u) + v >= 1 - 0.015;
    return false;
  }

  function blocksProjectile(px, py) {
    const tx = Math.floor(px / TILE);
    const ty = Math.floor(py / TILE);
    if (!inBounds(tx, ty)) return true;
    const t = getTile(tx, ty);
    if (t === T_AIR || t === T_WATER) return false;
    if (t === T_SLOPE_L || t === T_SLOPE_R) return slopeSolidAt(px, py, t, tx, ty);
    return isSolidTile(t);
  }

  function segmentHitsBlocks(x0, y0, x1, y1) {
    const len = dist(x0, y0, x1, y1);
    const steps = Math.max(2, Math.ceil(len / (TILE * 0.12)));
    for (let i = 0; i <= steps; i++) {
      const u = i / steps;
      const px = x0 + (x1 - x0) * u;
      const py = y0 + (y1 - y0) * u;
      if (blocksProjectile(px, py)) return { x: px, y: py };
    }
    return null;
  }

  /** Top surface Y (world px) of slope ramp at horizontal position px */
  function slopeSurfaceYAt(px, tx, ty, t) {
    const tileTop = ty * TILE;
    const u = (px - tx * TILE) / TILE;
    if (t === T_SLOPE_R) return tileTop + TILE * (1 - u);
    if (t === T_SLOPE_L) return tileTop + TILE * u;
    return tileTop + TILE;
  }

  function solidSample(px, py) {
    const tx = Math.floor(px / TILE), ty = Math.floor(py / TILE);
    const t = getTile(tx, ty);
    if (t === T_SLOPE_L || t === T_SLOPE_R) return false;
    return isSolidTile(t);
  }

  function findGroundUnder(fx, footY) {
    const tx = Math.floor(fx / TILE);
    const ty0 = Math.floor(footY / TILE) - 1;
    const ty1 = Math.floor(footY / TILE) + 2;
    let best = null;
    for (let ty = ty0; ty <= ty1; ty++) {
      if (!inBounds(tx, ty)) continue;
      const t = getTile(tx, ty);
      if (t === T_SLOPE_L || t === T_SLOPE_R) {
        const sy = slopeSurfaceYAt(fx, tx, ty, t);
        if (footY >= sy - 6 && (best === null || sy < best)) best = sy;
      } else if (isSolidTile(t) && t !== T_LAVA && t !== T_SAW) {
        const sy = ty * TILE;
        if (footY >= sy - 4 && (best === null || sy < best)) best = sy;
      }
    }
    return best;
  }

  function resolveGroundAndSlope(dt) {
    const hb = playerHitbox();
    const feet = player.y + PLAYER_H;
    const samples = [hb.x + hb.w * 0.2, hb.x + hb.w * 0.5, hb.x + hb.w * 0.8];
    let groundY = null;
    for (const fx of samples) {
      const g = findGroundUnder(fx, feet + 2);
      if (g !== null) groundY = groundY === null ? g : Math.min(groundY, g);
    }
    if (groundY === null) return;
    const snap = groundY - PLAYER_H - GROUND_SKIN;
    if (feet >= groundY - 5 && player.vy >= -60) {
      if (player.y > snap - 1) {
        player.y = snap;
        player.vy = 0;
        player.grounded = true;
      }
    }
    if (!player.grounded) return;
    let onSlope = null;
    for (const fx of samples) {
      const tx = Math.floor(fx / TILE);
      const ty = Math.floor((player.y + PLAYER_H - 1) / TILE);
      const t = getTile(tx, ty);
      if (t === T_SLOPE_L || t === T_SLOPE_R) onSlope = t;
    }
    if (!onSlope) return;
    if (onSlope === T_SLOPE_R) {
      if (keys.d && !keys.a) player.vx += 48 * dt;
      else if (!keys.a) player.vx += 42 * dt;
    } else if (onSlope === T_SLOPE_L) {
      if (keys.a && !keys.d) player.vx -= 48 * dt;
      else if (!keys.d) player.vx -= 42 * dt;
    }
  }

  function solidAtRect(rx, ry, rw, rh) {
    const xs = [rx + 1, rx + rw / 2, rx + rw - 2];
    const ys = [ry + 1, ry + rh / 2, ry + rh - 2];
    for (const x of xs) for (const y of ys) if (solidSample(x, y)) return true;
    return false;
  }

  function solidAt(px, py, pw, ph) {
    return solidAtRect(px, py, pw, ph);
  }

  function center() { return { x: player.x + PLAYER_W / 2, y: player.y + PLAYER_H / 2 }; }
  function dist(ax, ay, bx, by) { return Math.hypot(ax - bx, ay - by); }
  function mouseTile() { return { tx: Math.floor((mouseX + camX) / TILE), ty: Math.floor((mouseY + camY) / TILE) }; }
  function inDigRange(tx, ty) { const c = center(); return dist(c.x, c.y, tx * TILE + TILE / 2, ty * TILE + TILE / 2) <= digReach(); }

  function playerRectOverlapsTile(tx, ty) {
    const tw = tx * TILE, th = ty * TILE;
    return player.x < tw + TILE && player.x + PLAYER_W > tw && player.y < th + TILE && player.y + PLAYER_H > th;
  }

  function inWater() {
    const cx = Math.floor(center().x / TILE), cy = Math.floor(center().y / TILE);
    return getTile(cx, cy) === T_WATER;
  }

  function inLadder() {
    const x0 = Math.floor(player.x / TILE), x1 = Math.floor((player.x + PLAYER_W - 1) / TILE);
    const y0 = Math.floor(player.y / TILE), y1 = Math.floor((player.y + PLAYER_H - 1) / TILE);
    for (let ty = y0; ty <= y1; ty++) for (let tx = x0; tx <= x1; tx++) if (getTile(tx, ty) === T_LADDER) return true;
    return false;
  }

  function battleRules() { return gameMode === "Battle"; }
  function shopRules() { return gameMode === "SHOP"; }
  function digTradeRules() { return gameMode === "Dig + Trade"; }

  function firstFree(arr) { for (let i = 0; i < arr.length; i++) if (!arr[i]) return i; return -1; }

  function mergeStack(arr, item) {
    if (item.kind === "mortar") return false;
    for (let i = 0; i < arr.length; i++) {
      const s = arr[i];
      if (s && s.kind === item.kind && s.name === item.name && "qty" in s) { s.qty += item.qty; return true; }
    }
    return false;
  }

  function hotbarForItem(item) {
    if (!item) return invWeapons;
    if (item.kind === "build") return invBuilds;
    return invWeapons;
  }

  function addToStorage(item) {
    const stackable = item.kind === "weapon" || item.kind === "build" || item.kind === "blade";
    const bar = hotbarForItem(item);
    if (stackable && mergeStack(bar, item)) return true;
    if (stackable && mergeStack(backpack, item)) return true;
    let i = firstFree(bar);
    if (i !== -1) { bar[i] = { ...item }; return true; }
    i = firstFree(backpack);
    if (i !== -1) { backpack[i] = { ...item }; return true; }
    return false;
  }

  function addWeaponPreferBackpack(item) {
    const bar = hotbarForItem(item);
    if (mergeStack(bar, item) || mergeStack(backpack, item)) return true;
    let i = firstFree(bar);
    if (i !== -1) { bar[i] = { ...item }; return true; }
    i = firstFree(backpack);
    if (i !== -1) { backpack[i] = { ...item }; return true; }
    return false;
  }

  function selectedItem() { return activeHotbar()[selectedSlot]; }
  function cleanupInventory() {
    for (const arr of [invWeapons, invBuilds, backpack]) {
      for (let i = 0; i < arr.length; i++) {
        const it = arr[i];
        if (it && (it.kind === "weapon" || it.kind === "build" || it.kind === "blade") && it.qty <= 0) arr[i] = null;
      }
    }
    const bar = activeHotbar();
    if (!bar[selectedSlot]) {
      const first = bar.findIndex(Boolean);
      selectedSlot = first >= 0 ? first : 0;
    }
  }

  function ensureStarterInventory() {
    invWeapons.fill(null);
    invBuilds.fill(null);
    backpack.fill(null);
    invWeapons[0] = { kind: "pickaxe", name: "Pickaxe", qty: 1 };
    invWeapons[1] = { kind: "mortar", name: "Mortar", qty: 1 };
    invWeapons[2] = { kind: "blade", name: "Blade", qty: 8 };
    invWeapons[3] = { kind: "weapon", name: "Grenade Launcher", qty: 6 };
    invBuilds[0] = { kind: "build", name: "Dirt", tile: T_DIRT, qty: 40 };
    invBuilds[1] = { kind: "build", name: "Saw", tile: T_SAW, qty: 2 };
    invBuilds[2] = { kind: "build", name: "Water", tile: T_WATER, qty: 6 };
    invBuilds[3] = { kind: "build", name: "Lava", tile: T_LAVA, qty: 4 };
    invBuilds[4] = { kind: "build", name: "Cannon", tile: T_CANNON, qty: 2 };
    invBuilds[5] = { kind: "build", name: "Ladder", tile: T_LADDER, qty: 4 };
    hotbarPage = "weapons";
    selectedSlot = 0;
  }

  function spawnDrop(tx, ty, item, color) { drops.push({ x: tx * TILE + 6, y: ty * TILE + 1, vy: 0, item, color }); }
  function spawnDropPx(px, py, item, color, shape = "square") { drops.push({ x: px, y: py, vy: 0, item, color, shape }); }

  function maybeSpawnDrop(tx, ty) {
    if (Math.random() < SUPER_RARE_CHANCE) {
      spawnDrop(tx, ty, { kind: "weapon", name: "MYTHIC", qty: 6 }, "#ff4d4d");
      superRareBannerUntil = performance.now() + 2500;
    } else if (Math.random() < MORTAR_DROP_CHANCE) spawnDrop(tx, ty, { kind: "mortar", name: "Mortar", qty: 1 }, "#7fd8ff");
    else if (Math.random() < WEAPON_DROP_CHANCE) {
      const names = ["Rusty Blaster", "Shard Pistol", "Core Drill Gun", "Crystal SMG", "Void Carbine", "Grenade Launcher"];
      spawnDrop(tx, ty, { kind: "weapon", name: names[(Math.random() * names.length) | 0], qty: 1 }, "#ffe66d");
    }
    const r = Math.random();
    if (r < 0.035) spawnDrop(tx, ty, { kind: "build", name: "Water", tile: T_WATER, qty: 1 }, "#64b5ff");
    else if (r < 0.055) spawnDrop(tx, ty, { kind: "build", name: "Lava", tile: T_LAVA, qty: 1 }, "#ff6a00");
    else if (r < 0.075) spawnDrop(tx, ty, { kind: "build", name: "Saw", tile: T_SAW, qty: 1 }, "#d0d3d8");
  }

  function rareTileDigRoll(tx, ty, t) {
    if (t !== T_CANNON && t !== T_WATER && t !== T_LAVA && t !== T_LADDER) return false;
    if (Math.random() >= RARE_DIG_CHANCE) return false;
    setTile(tx, ty, T_AIR);
    maybeSpawnDrop(tx, ty);
    return true;
  }

  function randomSurfaceY() { return 48 + ((Math.random() * 18) | 0); }

  function carveRandomFeatures(surface) {
    const pockets = 40 + ((Math.random() * 30) | 0);
    for (let p = 0; p < pockets; p++) {
      const cx = 4 + ((Math.random() * (WORLD_W - 8)) | 0);
      const cy = surface + 8 + ((Math.random() * (WORLD_H - surface - BOTTOM_UI_ROWS - 20)) | 0);
      const r = 2 + ((Math.random() * 5) | 0);
      for (let y = -r; y <= r; y++) for (let x = -r; x <= r; x++) {
        if (x * x + y * y <= r * r + Math.random() * 2) setTile(cx + x, cy + y, T_AIR);
      }
    }
    const structs = 26 + ((Math.random() * 16) | 0);
    for (let s = 0; s < structs; s++) {
      const sx = 6 + ((Math.random() * (WORLD_W - 20)) | 0);
      const base = surface - 3 - ((Math.random() * 8) | 0);
      const roll = Math.random();
      if (roll < 0.22) {
        for (let y = 0; y < 5; y++) for (let x = 0; x < 6; x++) {
          if (x === 0 || x === 5 || y === 0 || y === 4) setTile(sx + x, base + y, T_WOOD);
        }
      } else if (roll < 0.44) {
        for (let y = 0; y < 4; y++) for (let x = 0; x < 5; x++) setTile(sx + x, base + y, (x + y) % 2 ? T_BRICK : T_WOOD);
      } else if (roll < 0.66) {
        for (let x = 0; x < 7; x++) setTile(sx + x, base, T_BRICK);
        setTile(sx + 3, base - 1, T_CANNON);
        cannonMeta[idx(sx + 3, base - 1)] = CANNON_META_PREMADE;
        premadeCannonList.push({ tx: sx + 3, ty: base - 1 });
      } else if (roll < 0.82) {
        for (let x = 0; x < 6; x++) setTile(sx + x, base, T_WOOD);
        setTile(sx + 2, base - 1, T_SAW);
        setTile(sx + 4, base - 1, T_LAVA);
      } else {
        setTile(sx, base, T_SLOPE_L);
        setTile(sx + 1, base, T_SLOPE_R);
        setTile(sx + 2, base, T_WATER);
        setTile(sx + 3, base, T_WATER);
      }
    }
  }

  function applyBottomBorder() {
    for (let y = WORLD_H - BOTTOM_UI_ROWS; y < WORLD_H; y++) for (let x = 0; x < WORLD_W; x++) setTile(x, y, T_BEDROCK);
  }

  function buildWorld() {
    tiles = new Uint8Array(WORLD_W * WORLD_H);
    cannonMeta = new Uint8Array(WORLD_W * WORLD_H);
    premadeCannonList = [];
    const surface = randomSurfaceY();
    for (let y = 0; y < WORLD_H; y++) {
      for (let x = 0; x < WORLD_W; x++) {
        if (x === 0 || x === WORLD_W - 1 || y === WORLD_H - 1) { setTile(x, y, T_BEDROCK); continue; }
        if (y <= surface) setTile(x, y, T_AIR);
        else if (y >= WORLD_H - BOTTOM_UI_ROWS) setTile(x, y, T_BEDROCK);
        else setTile(x, y, Math.sin(x * 0.11 + y * 0.07 + Math.random() * 0.4) > -0.78 ? T_DIRT : T_AIR);
      }
    }
    carveRandomFeatures(surface);
    applyBottomBorder();
    worldSurfaceY = surface;
    randomSkySpawn(surface);
    player.vx = 0; player.vy = 0; player.grounded = false;
    player.hp = MAX_HP; player.hpDisplay = MAX_HP; player.dead = false;
    bullets = []; drops = []; cannonLines = []; digState = null;
    camFollow = null;
    digProgress.clear();
    camInitialized = false;
    ensureStarterInventory();
  }

  function buildShopWorld() {
    tiles = new Uint8Array(WORLD_W * WORLD_H);
    cannonMeta = new Uint8Array(WORLD_W * WORLD_H);
    premadeCannonList = [];
    for (let y = 0; y < WORLD_H; y++) for (let x = 0; x < WORLD_W; x++) {
      if (x === 0 || x === WORLD_W - 1 || y === WORLD_H - 1 || y >= WORLD_H - BOTTOM_UI_ROWS) setTile(x, y, T_BEDROCK);
      else setTile(x, y, T_AIR);
    }
    const rowY = 120;
    for (let x = 4; x < WORLD_W - 4; x++) {
      setTile(x, rowY, T_DIRT);
      setTile(x, rowY + 1, T_DIRT);
    }
    worldSurfaceY = rowY - 8;
    player.x = (WORLD_W / 2) * TILE - PLAYER_W / 2;
    player.y = (rowY - 8) * TILE;
    player.vx = 0; player.vy = 0;
    player.hp = MAX_HP; player.hpDisplay = MAX_HP; player.dead = false;
    bullets = []; drops = []; cannonLines = []; digState = null;
    camFollow = null;
    digProgress.clear();
    camInitialized = false;
    invWeapons.fill(null);
    invBuilds.fill(null);
    backpack.fill(null);
    invWeapons[0] = { kind: "pickaxe", name: "Pickaxe", qty: 1 };
    hotbarPage = "weapons";
    selectedSlot = 0;
  }

  function randomSkySpawn(surface) {
    const margin = 4;
    const tx = margin + ((Math.random() * (WORLD_W - margin * 2)) | 0);
    const ty = Math.max(2, Math.min(surface - 6, 8 + ((Math.random() * 12) | 0)));
    player.x = tx * TILE + (TILE - PLAYER_W) / 2;
    player.y = ty * TILE;
  }

  function applyDamage(amount, knockX = 0, knockY = 0) {
    if (!started || player.dead) return;
    if (digTradeRules() || shopRules()) return;
    const now = performance.now();
    if (now - player.lastDamageAt < 250) return;
    player.lastDamageAt = now;
    player.hp = Math.max(0, player.hp - amount);
    player.vx += knockX;
    player.vy += knockY;
    damageFlashUntil = now + 500;
    if (player.hp <= 0) {
      player.dead = true;
      const c = center();
      spawnDropPx(c.x - 6, c.y - 6, { kind: "coin", name: "Coin", qty: 1 }, "#f6d94a", "circle");
      tmsg("You died.", 1200);
      respawnBtn.style.display = "block";
    }
  }

  function hazardTiles() {
    if (!battleRules() || player.dead) return;
    const hb = playerHitbox();
    const footTy = Math.floor((player.y + PLAYER_H - 1) / TILE);
    const x0 = Math.floor(hb.x / TILE);
    const x1 = Math.floor((hb.x + hb.w - 1) / TILE);
    for (let tx = x0; tx <= x1; tx++) {
      let t = getTile(tx, footTy);
      if (t === T_LAVA || t === T_SAW) {
        applyHazardFrom(tx, footTy);
        return;
      }
    }
    const y0 = Math.floor(hb.y / TILE);
    const y1 = Math.floor((hb.y + hb.h - 1) / TILE);
    for (let ty = y0; ty <= y1; ty++) {
      for (let tx = x0; tx <= x1; tx++) {
        const t = getTile(tx, ty);
        if (t !== T_SAW && t !== T_LAVA) continue;
        const tw = tx * TILE, th = ty * TILE;
        if (hb.x < tw + TILE && hb.x + hb.w > tw && hb.y < th + TILE && hb.y + hb.h > th) {
          applyHazardFrom(tx, ty);
          return;
        }
      }
    }
  }

  function applyHazardFrom(tx, ty) {
    const cx = tx * TILE + TILE / 2, cy = ty * TILE + TILE / 2;
    const pc = center();
    const dx = pc.x - cx, dy = pc.y - cy;
    const len = Math.hypot(dx, dy) || 1;
    const knock = TILE * 2;
    applyDamage(1, (dx / len) * knock * 14, (dy / len) * knock * 10);
  }

  function wallTouchLeft() {
    const hb = playerHitbox();
    return solidSample(hb.x - 1, hb.y + hb.h * 0.35) || solidSample(hb.x - 1, hb.y + hb.h * 0.75);
  }

  function wallTouchRight() {
    const hb = playerHitbox();
    return solidSample(hb.x + hb.w + 1, hb.y + hb.h * 0.35) || solidSample(hb.x + hb.w + 1, hb.y + hb.h * 0.75);
  }

  function physicsSubstep(dt) {
    if (player.dead) return;
    wallJumpCooldown = Math.max(0, wallJumpCooldown - dt);
    const wasGrounded = player.grounded;
    const water = inWater();
    const ladder = inLadder();
    const g = water ? 520 : GRAVITY;
    const maxFall = water ? 200 : MAX_FALL;
    const jumpV = water ? -260 : JUMP_V;
    if (keys.a) player.vx = -moveSpeed;
    else if (keys.d) player.vx = moveSpeed;
    else player.vx *= Math.exp(-12 * dt);
    if (ladder) {
      player.vy = Math.min(player.vy, 80);
      if (keys.w) player.vy = -140;
      else player.vy += g * 0.15 * dt;
      player.vy *= Math.exp(-3 * dt);
      player.vy -= 40 * dt;
    } else if (water) {
      floatPhase += dt * 2.2;
      const bob = Math.sin(floatPhase) * 18;
      player.vy += g * 0.35 * dt;
      player.vy = Math.min(player.vy, 120) + bob * dt;
    } else {
    player.vy = Math.min(maxFall, player.vy + g * dt);
    }
    if (keys.w && wasGrounded && !water && !ladder) { player.vy = jumpV; player.grounded = false; }
    player.grounded = false;
    const touchL = !water && !ladder && wallTouchLeft();
    const touchR = !water && !ladder && wallTouchRight();
    if (!water && !ladder && !wasGrounded) {
      if (touchL && keys.a) {
        if (keys.w && wallJumpCooldown <= 0) {
          player.vy = -210;
          wallJumpCooldown = 0.4;
        } else if (!keys.w) {
          player.vy = Math.min(player.vy, 70);
        }
      } else if (touchR && keys.d) {
        if (keys.w && wallJumpCooldown <= 0) {
          player.vy = -210;
          wallJumpCooldown = 0.4;
        } else if (!keys.w) {
          player.vy = Math.min(player.vy, 70);
        }
      }
    }
    const hb = playerHitbox();
    player.x += player.vx * dt;
    if (solidAtRect(hb.x, player.y, hb.w, PLAYER_H)) { player.x -= player.vx * dt; player.vx = 0; }
    player.y += player.vy * dt;
    const hb2 = playerHitbox();
    if (solidAtRect(hb2.x, hb2.y, hb2.w, hb2.h)) {
      const vy = player.vy;
      player.y -= player.vy * dt;
      if (vy > 0) player.grounded = true;
      player.vy = 0;
    }
    if (!water && !ladder) resolveGroundAndSlope(dt);
    hazardTiles();
    player.hpDisplay += (player.hp - player.hpDisplay) * Math.min(1, dt * 8);
  }

  function physics(dt) {
    if (player.dead) return;
    const speed = Math.hypot(player.vx, player.vy);
    const substeps = Math.max(1, Math.ceil((speed * dt) / (TILE * 0.22)));
    const sdt = dt / substeps;
    for (let i = 0; i < substeps; i++) physicsSubstep(sdt);
  }

  function aimVector() {
    const c = center();
    let dx = mouseX + camX - c.x, dy = mouseY + camY - c.y;
    const len = Math.hypot(dx, dy) || 1;
    return { dx: dx / len, dy: dy / len, mouseDist: len };
  }

  function aimPower01() {
    const d = aimVector().mouseDist;
    const maxD = Math.hypot(canvas.width, canvas.height) || 1;
    return Math.max(0.12, Math.min(1, d / maxD));
  }

  /** Distance (px) along aim line before projectile curves down — scales with mouse distance */
  function straightPhaseDist() {
    const pow = aimPower01();
    const minD = TILE * 0.4;
    const maxD = Math.hypot(canvas.width, canvas.height);
    return minD + pow * (maxD - minD);
  }

  function arcBulletSpeed() {
    return 240 + aimPower01() * 560;
  }

  function makeCurveBullet(x, y, extra) {
    const aim = aimVector();
    const sp = arcBulletSpeed();
    return {
      x, y,
      vx: aim.dx * sp, vy: aim.dy * sp,
      straightLeft: straightPhaseDist(),
      curvePhase: false,
      gravity: true,
      damagePlayer: true,
      camLock: true,
      ...extra,
    };
  }

  function getWeaponProfile(item) {
    if (!item) return null;
    if (item.kind === "mortar") return { mode: "arcBlast", single: true, delayedCurve: true };
    if (item.kind === "blade") return { mode: "throwBlade", radius: 0.6, delayedCurve: true };
    if (item.kind !== "weapon") return null;
    if (item.name === "Core Drill Gun") return { mode: "laserLine", length: 12 };
    if (item.name === "Crystal SMG") return { mode: "straightBlast", speed: 780, radius: 1.5, gravity: false };
    if (item.name === "Void Carbine") return { mode: "arcBlast", radius: 3.2, delayedCurve: true };
    if (item.name === "Grenade Launcher") return { mode: "grenade", radius: 2.4, fuse: 2, delayedCurve: true };
    if (item.name === "Rusty Blaster") return { mode: "single", speed: 640, gravity: false, usePower: false };
    if (item.name === "Shard Pistol") return { mode: "single", speed: 720, gravity: false, usePower: false };
    if (item.name === "MYTHIC") return { mode: "arcBlast", radius: 3.8, delayedCurve: true };
    return { mode: "single", speed: 680, gravity: false, usePower: false };
  }

  function playerOverlapsExplosion(cx, cy, radiusPx) {
    const px = player.x, py = player.y, pw = PLAYER_W, ph = PLAYER_H;
    const qx = Math.max(px, Math.min(cx, px + pw));
    const qy = Math.max(py, Math.min(cy, py + ph));
    return dist(cx, cy, qx, qy) <= radiusPx;
  }

  function explode(tx, ty, radius, sourcePlayer) {
    const r = radius ?? 2;
    const cx = tx * TILE + TILE / 2;
    const cy = ty * TILE + TILE / 2;
    const blastR = (r + 0.85) * TILE;
    for (let y = -Math.ceil(r); y <= Math.ceil(r); y++) {
      for (let x = -Math.ceil(r); x <= Math.ceil(r); x++) {
        const nx = tx + x, ny = ty + y;
        if (!inBounds(nx, ny) || Math.hypot(x, y) > r + 0.1) continue;
        if (isDiggableTile(getTile(nx, ny))) { setTile(nx, ny, T_AIR); maybeSpawnDrop(nx, ny); }
      }
    }
    if (sourcePlayer && battleRules() && playerOverlapsExplosion(cx, cy, blastR)) {
      applyDamage(1, (center().x < cx ? -180 : 180), -120);
    }
  }

  function destroySingle(tx, ty, damagePlayer) {
    if (!inBounds(tx, ty) || !isDiggableTile(getTile(tx, ty))) return;
    setTile(tx, ty, T_AIR);
    maybeSpawnDrop(tx, ty);
    if (damagePlayer && battleRules()) {
      const cx = tx * TILE + TILE / 2, cy = ty * TILE + TILE / 2;
      if (playerOverlapsExplosion(cx, cy, TILE * 1.35)) applyDamage(1, (center().x < cx ? -140 : 140), -90);
    }
  }

  function canShootNow() {
    if (!battleRules()) return false;
    return performance.now() - lastWeaponFire >= WEAPON_FIRE_DELAY_MS;
  }

  function fireCurrent() {
    if (player.dead || shopRules() || digTradeRules()) return;
    if (!battleRules()) return;
    const sel = selectedItem();
    if (!sel) return;
    if (sel.kind === "pickaxe" || sel.kind === "build") return;
    const profile = getWeaponProfile(sel);
    if (!profile) return;
    if (!canShootNow()) { tmsg("Weapon cooling down…", 500); return; }
    if (sel.kind !== "mortar" && sel.qty <= 0) return tmsg("No ammo.", 900);
    const aim = aimVector();
    const c = center();
    lastWeaponFire = performance.now();
    if (sel.kind === "mortar") {
      const b = makeCurveBullet(c.x, c.y, { radius: 0, single: true });
      bullets.push(b);
      camFollow = b;
      return;
    }
    if (sel.kind === "blade") {
      if (sel.qty <= 0) return tmsg("No blades.", 900);
      sel.qty -= 1;
      const b = makeCurveBullet(c.x, c.y, { radius: profile.radius, blade: true });
      bullets.push(b);
      camFollow = b;
      cleanupInventory();
      return;
    }
    sel.qty -= 1;
    if (profile.mode === "laserLine") {
      const startTx = Math.floor(c.x / TILE), startTy = Math.floor(c.y / TILE);
      for (let i = 1; i <= profile.length; i++) {
        const tx = Math.floor(startTx + aim.dx * i);
        const ty = Math.floor(startTy + aim.dy * i);
        if (!inBounds(tx, ty)) break;
        if (isDiggableTile(getTile(tx, ty))) { setTile(tx, ty, T_AIR); maybeSpawnDrop(tx, ty); }
      }
      camFollow = null;
    } else if (profile.mode === "grenade") {
      const b = makeCurveBullet(c.x, c.y, { radius: profile.radius, fuse: profile.fuse });
      bullets.push(b);
      camFollow = b;
    } else if (profile.mode === "straightBlast") {
      const sp = profile.speed;
      const b = {
        x: c.x, y: c.y, vx: aim.dx * sp, vy: aim.dy * sp,
        gravity: false, radius: profile.radius, damagePlayer: true, camLock: false,
      };
      bullets.push(b);
    } else if (profile.mode === "arcBlast") {
      const b = makeCurveBullet(c.x, c.y, { radius: profile.radius });
      bullets.push(b);
      camFollow = b;
    } else {
      const sp = profile.speed;
      const b = {
        x: c.x, y: c.y, vx: aim.dx * sp, vy: aim.dy * sp,
        gravity: !!profile.gravity, radius: 0, damagePlayer: true, camLock: !!profile.gravity,
      };
      bullets.push(b);
      if (b.camLock) camFollow = b;
    }
    cleanupInventory();
  }

  function tryPlaceBuild() {
    if (!started || player.dead || shopRules()) return;
    const sel = selectedItem();
    if (!sel || sel.kind !== "build" || sel.qty <= 0) return;
    const { tx, ty } = mouseTile();
    if (!inBounds(tx, ty) || getTile(tx, ty) !== T_AIR || !inDigRange(tx, ty)) return;
    if (playerRectOverlapsTile(tx, ty)) { tmsg("Can't place on yourself.", 700); return; }
    setTile(tx, ty, sel.tile || T_DIRT);
    if (sel.tile === T_CANNON) cannonMeta[idx(tx, ty)] = CANNON_META_PLAYER;
    sel.qty -= 1;
    cleanupInventory();
  }

  function digUpdate(dtMs) {
    if (!started || player.dead) { digState = null; return; }
    if (shopRules()) { digState = null; return; }
    if (!mouseDownLeft) { digState = null; return; }
    const sel = selectedItem();
    if (!sel || sel.kind !== "pickaxe") { digState = null; return; }
    const { tx, ty } = mouseTile();
    if (!inBounds(tx, ty) || !inDigRange(tx, ty) || !isDiggableTile(getTile(tx, ty))) { digState = null; return; }
    const key = tx + "," + ty;
    if (!digState || digState.tx !== tx || digState.ty !== ty) digState = { tx, ty, flash: 0 };
    digState.flash += dtMs;
    const prev = digProgress.get(key) || 0;
    const acc = prev + dtMs;
    digProgress.set(key, acc);
    if (acc >= digTimeMs) {
      digProgress.delete(key);
      if (rareTileDigRoll(tx, ty, getTile(tx, ty))) { digState = null; return; }
      setTile(tx, ty, T_AIR);
      maybeSpawnDrop(tx, ty);
      if (Math.random() < 0.08) spawnDrop(tx, ty, { kind: "build", name: "Dirt", tile: T_DIRT, qty: 1 }, "#9b6a3b");
      digState = null;
    }
  }

  function tileBlocksCannonShot(t) {
    if (t === T_AIR || t === T_WATER) return false;
    if (t === T_SLOPE_L || t === T_SLOPE_R) return true;
    return isSolidTile(t);
  }

  function cannonLosFrom(ox, oy, px, py, skipTx, skipTy) {
    const steps = Math.max(6, Math.ceil(dist(ox, oy, px, py) / (TILE * 0.3)));
    for (let i = 1; i < steps; i++) {
      const u = i / steps;
      const wx = ox + (px - ox) * u, wy = oy + (py - oy) * u;
      const gx = Math.floor(wx / TILE), gy = Math.floor(wy / TILE);
      if (gx === skipTx && gy === skipTy) continue;
      if (tileBlocksCannonShot(getTile(gx, gy))) return false;
    }
    return true;
  }

  function rayMaxTravel(ox, oy, ux, uy, maxDist, skipTx, skipTy) {
    let d = TILE * 0.15;
    while (d < maxDist) {
      const wx = ox + ux * d, wy = oy + uy * d;
      const gx = Math.floor(wx / TILE), gy = Math.floor(wy / TILE);
      if (!inBounds(gx, gy)) return d;
      if (!(gx === skipTx && gy === skipTy) && tileBlocksCannonShot(getTile(gx, gy))) return Math.max(TILE * 0.25, d - TILE * 0.2);
      d += TILE * 0.18;
    }
    return maxDist;
  }

  function updateProjectiles(dt) {
    for (let i = bullets.length - 1; i >= 0; i--) {
      const b = bullets[i];
      if (b.fuse != null) {
        b.fuse -= dt;
        if (b.fuse <= 0) {
      const tx = Math.floor(b.x / TILE), ty = Math.floor(b.y / TILE);
          if (inBounds(tx, ty)) explode(tx, ty, b.radius, b.damagePlayer);
        bullets.splice(i, 1);
          if (camFollow === b) camFollow = null;
          continue;
        }
      }
      const spd = Math.hypot(b.vx, b.vy);
      const steps = Math.max(1, Math.ceil(spd * dt / (TILE * 0.1)));
      const sdt = dt / steps;
      let removed = false;
      for (let s = 0; s < steps && !removed; s++) {
        if (b.straightLeft != null) {
          if (!b.curvePhase) {
            const step = Math.hypot(b.vx, b.vy) * sdt;
            b.straightLeft -= step;
            if (b.straightLeft <= 0) b.curvePhase = true;
          } else {
            b.vy += 1100 * sdt;
          }
        } else if (b.gravity) {
          b.vy += 1100 * sdt;
        }
        const nx = b.x + b.vx * sdt;
        const ny = b.y + b.vy * sdt;
        const hit = segmentHitsBlocks(b.x, b.y, nx, ny);
        if (hit) {
          const tx = Math.floor(hit.x / TILE), ty = Math.floor(hit.y / TILE);
          if (b.single && inBounds(tx, ty)) destroySingle(tx, ty, b.damagePlayer);
          else if (b.radius && inBounds(tx, ty)) explode(tx, ty, b.radius, b.damagePlayer);
          else if (inBounds(tx, ty) && isDiggableTile(getTile(tx, ty))) setTile(tx, ty, T_AIR);
          removed = true;
        } else if (!inBounds(Math.floor(nx / TILE), Math.floor(ny / TILE))) {
          removed = true;
        } else {
          b.x = nx;
          b.y = ny;
        }
      }
      if (removed) {
        bullets.splice(i, 1);
        if (camFollow === b) camFollow = null;
      }
    }
    const pc = center();
    for (let i = cannonLines.length - 1; i >= 0; i--) {
      const L = cannonLines[i];
      const spd = Math.hypot(L.vx, L.vy) || 1;
      const ux = L.vx / spd, uy = L.vy / spd;
      let remain = spd * dt;
      let px = L.x, py = L.y;
      let remove = false;
      if (L.traveled == null) L.traveled = 0;
      while (remain > 0.001 && !remove) {
        const chunk = Math.min(remain, 7);
        const ax = px, ay = py;
        px += ux * chunk;
        py += uy * chunk;
        L.traveled += chunk;
        if (L.maxTravel != null && L.traveled >= L.maxTravel) { remove = true; break; }
        if (battleRules() && !player.dead) {
          const ppx = pc.x, ppy = pc.y;
          const abx = px - ax, aby = py - ay;
          const apx = ppx - ax, apy = ppy - ay;
          const ab2 = abx * abx + aby * aby || 1;
          let t = (apx * abx + apy * aby) / ab2;
          t = Math.max(0, Math.min(1, t));
          const qx = ax + abx * t, qy = ay + aby * t;
          if (dist(ppx, ppy, qx, qy) < 13) {
            applyDamage(1, ux * 140, -70);
            remove = true;
            break;
          }
        }
        const tx = Math.floor(px / TILE), ty = Math.floor(py / TILE);
        if (!inBounds(tx, ty)) { remove = true; break; }
        if (!(L.fromTx != null && tx === L.fromTx && ty === L.fromTy) && blocksProjectile(px, py)) { remove = true; break; }
        remain -= chunk;
      }
      L.x = px;
      L.y = py;
      if (remove) cannonLines.splice(i, 1);
    }
  }

  let cannonAcc = 0;
  function updatePremadeCannons(dt) {
    cannonAcc += dt;
    if (cannonAcc < 2) return;
    cannonAcc = 0;
    if (!started || player.dead || !battleRules()) return;
    const pc = center();
    for (const cn of premadeCannonList) {
      if (getTile(cn.tx, cn.ty) !== T_CANNON || cannonMeta[idx(cn.tx, cn.ty)] !== CANNON_META_PREMADE) continue;
      const ox = cn.tx * TILE + TILE / 2, oy = cn.ty * TILE + TILE / 2;
      let dx = pc.x - ox, dy = pc.y - oy;
      const len = Math.hypot(dx, dy) || 1;
      if (len > cannonMaxRangePx()) continue;
      if (!cannonLosFrom(ox, oy, pc.x, pc.y, cn.tx, cn.ty)) continue;
      dx /= len; dy /= len;
      const spd = 2400;
      const maxTravel = rayMaxTravel(ox, oy, dx, dy, cannonMaxRangePx() + TILE * 2, cn.tx, cn.ty);
      cannonLines.push({
        x: ox, y: oy, vx: dx * spd, vy: dy * spd,
        traveled: 0, maxTravel, fromTx: cn.tx, fromTy: cn.ty,
      });
    }
  }

  function updateDrops(dt) {
    for (let i = 0; i < drops.length; i++) {
      const d = drops[i];
      d.vy = Math.min(650, d.vy + 1400 * dt);
      d.y += d.vy * dt;
      const tx0 = Math.floor(d.x / TILE), tx1 = Math.floor((d.x + 11) / TILE), by = d.y + 12, ty = Math.floor(by / TILE);
      let landed = false;
      for (let tx = tx0; tx <= tx1; tx++) {
        if (isSolidTile(getTile(tx, ty)) || getTile(tx, ty) === T_WATER) {
          d.y = ty * TILE - 12;
          d.vy = 0;
          landed = true;
          break;
        }
      }
      if (!landed) {
        for (let j = 0; j < drops.length; j++) {
          if (i === j) continue;
          const o = drops[j];
          if (d.x < o.x + 12 && d.x + 12 > o.x && d.y + 12 >= o.y && d.y < o.y) { d.y = o.y - 12; d.vy = 0; break; }
        }
      }
    }
  }

  function pickupDrops() {
    const c = center();
    for (let i = drops.length - 1; i >= 0; i--) {
      const d = drops[i];
      if (dist(c.x, c.y, d.x + 6, d.y + 6) < 26) {
        if (d.item.kind === "coin") {
          drops.splice(i, 1);
          tmsg("Coin collected.", 700);
          continue;
        }
        const it = { ...d.item };
        const ok = (it.kind === "weapon" || it.kind === "blade" || it.kind === "mortar")
          ? addWeaponPreferBackpack(it)
          : addToStorage(it);
        if (ok) { tmsg("Picked up " + d.item.name, 900); drops.splice(i, 1); cleanupInventory(); }
        else tmsg("Inventories full.", 900);
      }
    }
  }

  function resizeCanvas() {
    const r = canvas.parentElement.getBoundingClientRect();
    const w = Math.max(320, Math.floor(r.width));
    const h = Math.max(240, Math.floor(r.height));
    const newTile = Math.max(14, Math.min(Math.floor(w / VIEW_TILES_X), Math.floor(h / VIEW_TILES_Y)));
    if (canvas.width !== w || canvas.height !== h || TILE !== newTile) {
      canvas.width = w;
      canvas.height = h;
      TILE = newTile;
      syncPlayerSize();
    }
  }

  function hotbarLayout() {
    const slotW = Math.min(58, Math.max(38, Math.floor((canvas.width - 72) / 8)));
    const slot = slotW + 6;
    const totalW = 8 * slot - 6;
    const overlapRisk = player.y - camY > canvas.height - 120;
    const y = overlapRisk ? canvas.height - 112 : canvas.height - 50;
    const sx = Math.floor((canvas.width - totalW) / 2);
    const btnH = 20;
    const btnY = y - btnH - 6;
    const h = Math.round(slotW * 0.72);
    return { sx, y, totalW, slot, slotW, h, btnY, btnH, btnW: 34 };
  }

  function hitHotbarSwitch(mx, my) {
    const hb = hotbarLayout();
    if (my < hb.btnY || my > hb.btnY + hb.btnH) return null;
    if (mx >= hb.sx && mx < hb.sx + hb.btnW) return "weapons";
    if (mx >= hb.sx + hb.btnW + 4 && mx < hb.sx + hb.btnW * 2 + 4) return "builds";
    return null;
  }

  function drawWorld() {
    const x0 = Math.floor(camX / TILE), y0 = Math.floor(camY / TILE), x1 = Math.ceil((camX + canvas.width) / TILE), y1 = Math.ceil((camY + canvas.height) / TILE);
    sawAnim += 0.08;
    for (let y = y0; y <= y1; y++) {
      for (let x = x0; x <= x1; x++) {
        if (!inBounds(x, y)) continue;
        const t = getTile(x, y), sx = x * TILE - camX, sy = y * TILE - camY;
        if (t === T_AIR) continue;
        if (t === T_DIRT) ctx.fillStyle = "#6b4f2a";
        else if (t === T_BEDROCK) ctx.fillStyle = "#2a2a2a";
        else if (t === T_WOOD) ctx.fillStyle = "#7a5a35";
        else if (t === T_BRICK) ctx.fillStyle = "#9f805c";
        else if (t === T_CANNON) ctx.fillStyle = "#596677";
        else if (t === T_SAW) ctx.fillStyle = "#cfd2d7";
        else if (t === T_WATER) ctx.fillStyle = "rgba(70,140,230,0.75)";
        else if (t === T_LAVA) ctx.fillStyle = "#ff6a00";
        else if (t === T_LADDER) ctx.fillStyle = "#c9a66a";
        else if (t === T_SLOPE_L || t === T_SLOPE_R) ctx.fillStyle = "#7a6548";
        else ctx.fillStyle = "#555";
        if (t === T_SLOPE_L || t === T_SLOPE_R) {
          ctx.beginPath();
          if (t === T_SLOPE_L) {
            ctx.moveTo(sx, sy + TILE);
            ctx.lineTo(sx + TILE, sy + TILE);
            ctx.lineTo(sx, sy);
          } else {
            ctx.moveTo(sx, sy + TILE);
            ctx.lineTo(sx + TILE, sy + TILE);
            ctx.lineTo(sx + TILE, sy);
          }
          ctx.closePath();
          ctx.fill();
          ctx.strokeStyle = "rgba(0,0,0,0.35)";
          ctx.stroke();
          continue;
        }
        ctx.fillRect(sx, sy, TILE, TILE);
        if (t === T_SAW) {
          ctx.save();
          ctx.translate(sx + TILE / 2, sy + TILE / 2);
          ctx.rotate(sawAnim + x * 0.4 + y * 0.3);
          ctx.strokeStyle = "#555";
          ctx.lineWidth = 2;
          for (let k = 0; k < 8; k++) {
            ctx.rotate((Math.PI * 2) / 8);
          ctx.beginPath();
            ctx.moveTo(0, 0);
            ctx.lineTo(0, -10);
          ctx.stroke();
          }
          ctx.beginPath();
          ctx.arc(0, 0, 9, 0, Math.PI * 2);
          ctx.strokeStyle = "#888";
          ctx.stroke();
          ctx.restore();
        }
        if (t === T_CANNON) {
          const pc = center();
          const ox = x * TILE + TILE / 2, oy = y * TILE + TILE / 2;
          let dx = pc.x - ox, dy = pc.y - oy;
          const len = Math.hypot(dx, dy) || 1;
          dx /= len; dy /= len;
          ctx.fillStyle = "#aab";
          ctx.beginPath();
          ctx.moveTo(ox - camX, oy - camY);
          ctx.lineTo(ox - camX + dx * TILE * 0.55, oy - camY + dy * TILE * 0.55);
          ctx.lineTo(ox - camX + dx * 8 - dy * 5, oy - camY + dy * 8 + dx * 5);
          ctx.closePath();
          ctx.fill();
        }
        if (t === T_LADDER) {
          ctx.strokeStyle = "rgba(0,0,0,0.45)";
          for (let s = 0; s < 4; s++) {
            const ly = sy + 4 + s * 5;
            ctx.beginPath();
            ctx.moveTo(sx + 4, ly);
            ctx.lineTo(sx + TILE - 4, ly);
            ctx.stroke();
          }
        }
        if (t !== T_WATER) {
          ctx.strokeStyle = "rgba(0,0,0,0.35)";
          ctx.strokeRect(sx + 0.5, sy + 0.5, TILE - 1, TILE - 1);
        }
      }
    }
  }

  function drawDigFlash() {
    if (!digState) return;
    const sx = digState.tx * TILE - camX;
    const sy = digState.ty * TILE - camY;
    const key = digState.tx + "," + digState.ty;
    const acc = digProgress.get(key) || 0;
    const p = Math.min(1, acc / digTimeMs);
    const blink = Math.floor(digState.flash / 90) % 2 === 0;
    if (blink) {
      ctx.fillStyle = "rgba(255,255,255," + (0.22 + p * 0.35) + ")";
      ctx.fillRect(sx, sy, TILE, TILE);
    }
  }

  function simTrajectoryStep(sel, profile, aim) {
    const c = center();
    if (profile.mode === "laserLine") return null;
    const sp = profile.delayedCurve ? arcBulletSpeed() : (profile.speed || BULLET_SPEED_MIN);
    let vx = aim.dx * sp, vy = aim.dy * sp;
    let x = c.x, y = c.y;
    let straightLeft = profile.delayedCurve ? straightPhaseDist() : -1;
    const pts = [];
    for (let i = 0; i < 70; i++) {
      const t = 0.035;
      const inCurve = profile.delayedCurve ? straightLeft <= 0 : !!profile.gravity;
      if (inCurve) vy += 1100 * t;
      else straightLeft -= Math.hypot(vx, vy) * t;
      x += vx * t; y += vy * t;
      if (!inBounds(Math.floor(x / TILE), Math.floor(y / TILE)) || blocksProjectile(x, y)) break;
      if (i % 3 === 0) pts.push({ x: x - camX, y: y - camY });
    }
    return pts;
  }

  function updateTrajSmooth(profile, aim, dt) {
    const target = simTrajectoryStep(null, profile, aim);
    if (!target || target.length === 0) {
      trajSmoothPts = [];
      return;
    }
    if (trajSmoothPts.length !== target.length) {
      trajSmoothPts = target.map((p) => ({ x: p.x, y: p.y }));
      return;
    }
    const k = 1 - Math.exp(-16 * dt);
    for (let i = 0; i < target.length; i++) {
      trajSmoothPts[i].x += (target[i].x - trajSmoothPts[i].x) * k;
      trajSmoothPts[i].y += (target[i].y - trajSmoothPts[i].y) * k;
    }
  }

  function drawTrajectory() {
    if (!started || document.activeElement === chatInput || player.dead) return;
    if (!canShootNow()) return;
    const sel = selectedItem();
    if (!sel || sel.kind === "pickaxe" || sel.kind === "build") return;
    const profile = getWeaponProfile(sel);
    if (!profile) return;
    const aim = aimVector();
    if (profile.mode === "laserLine") {
    const c = center();
      ctx.strokeStyle = "rgba(120,255,200,0.85)";
      ctx.setLineDash([4, 6]);
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.moveTo(c.x - camX, c.y - camY);
    let x = c.x, y = c.y;
      for (let i = 1; i <= profile.length; i++) {
        x += aim.dx * TILE;
        y += aim.dy * TILE;
        if (!inBounds(Math.floor(x / TILE), Math.floor(y / TILE))) break;
        ctx.lineTo(x - camX, y - camY);
      }
      ctx.stroke();
      ctx.setLineDash([]);
      return;
    }
    const pts = trajSmoothPts;
    if (!pts || pts.length === 0) return;
    ctx.strokeStyle = "rgba(255,255,255,0.45)";
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(pts[0].x, pts[0].y);
    for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y);
    ctx.stroke();
    ctx.fillStyle = "rgba(255,255,255,0.7)";
    for (const p of pts) {
      ctx.beginPath();
      ctx.arc(p.x, p.y, 2.5, 0, Math.PI * 2);
      ctx.fill();
    }
  }

  function drawProjectilesAndDrops() {
    ctx.fillStyle = "#ffe066";
    for (const b of bullets) {
      if (b.blade) {
        ctx.save();
        ctx.translate(b.x - camX, b.y - camY);
        ctx.rotate(performance.now() / 200);
        ctx.fillStyle = "#ddd";
        ctx.fillRect(-5, -2, 10, 4);
        ctx.restore();
      } else {
        ctx.beginPath();
        ctx.arc(b.x - camX, b.y - camY, 3, 0, Math.PI * 2);
        ctx.fill();
      }
    }
    ctx.strokeStyle = "#ff5555";
    ctx.lineWidth = 3;
    for (const L of cannonLines) {
      ctx.beginPath();
      ctx.moveTo(L.x - camX, L.y - camY);
      ctx.lineTo(L.x - camX - (L.vx / 3200) * 8, L.y - camY - (L.vy / 3200) * 8);
      ctx.stroke();
    }
    for (const d of drops) {
      ctx.fillStyle = d.color;
      if (d.shape === "circle" || (d.item && d.item.kind === "coin")) {
        ctx.beginPath();
        ctx.arc(d.x - camX + 6, d.y - camY + 6, 6, 0, Math.PI * 2);
        ctx.fill();
      } else {
        ctx.fillRect(d.x - camX, d.y - camY, 12, 12);
      }
    }
  }

  const NAME_COLORS = {
    0: "#cccccc", 1: "#111111", 2: "#ffffff", 3: "#e74c3c", 4: "#2ecc71",
    5: "#3498db", 6: "#f1c40f", 7: "#9b59b6", 8: "#1abc9c", 9: "#e67e22",
  };

  function drawColoredUsername(sx, sy) {
    const parts = [];
    let i = 0;
    let color = "#fff";
    while (i < username.length) {
      if (username[i] === "^" && /[0-9]/.test(username[i + 1])) {
        color = NAME_COLORS[username[i + 1]] || color;
        i += 2;
        continue;
      }
      parts.push({ ch: username[i], color });
      i++;
    }
    ctx.font = "11px Courier New";
    let tw = 0;
    for (const p of parts) tw += ctx.measureText(p.ch).width;
    let x = sx + PLAYER_W / 2 - tw / 2;
    for (const p of parts) {
      ctx.fillStyle = p.color;
      ctx.fillText(p.ch, x, sy - 14);
      x += ctx.measureText(p.ch).width;
    }
  }

  function drawPlayer() {
    const sx = player.x - camX, sy = player.y - camY;
    ctx.fillStyle = "#222";
    ctx.fillRect(sx - 2, sy - 10, PLAYER_W + 4, 6);
    ctx.fillStyle = "#66d977";
    ctx.fillRect(sx - 1, sy - 9, ((PLAYER_W + 2) * player.hpDisplay) / MAX_HP, 4);
    ctx.fillStyle = "#d24b4b";
    ctx.fillRect(sx, sy, PLAYER_W, PLAYER_H);
    drawColoredUsername(sx, sy);
    const now = performance.now();
    if (player.chatBubble.text && now < player.chatBubble.until) {
      ctx.fillStyle = "rgba(0,0,0,0.55)";
      const txt = player.chatBubble.text;
      const tw = Math.min(200, ctx.measureText(txt).width + 10);
      ctx.fillRect(sx + PLAYER_W / 2 - tw / 2, sy - 42, tw, 18);
    ctx.fillStyle = "#fff";
      ctx.font = "10px Courier New";
    ctx.textAlign = "center";
      ctx.fillText(txt.slice(0, 40), sx + PLAYER_W / 2, sy - 30);
    ctx.textAlign = "left";
    }
  }

  function drawHover() {
    const { tx, ty } = mouseTile();
    if (!inBounds(tx, ty) || !inDigRange(tx, ty)) return;
    ctx.strokeStyle = "#fff";
    ctx.lineWidth = 2;
    ctx.strokeRect(tx * TILE - camX + 1, ty * TILE - camY + 1, TILE - 2, TILE - 2);
  }

  function hotbarArrayForPage(page) { return page === "builds" ? invBuilds : invWeapons; }

  function drawHotbar() {
    const hb = hotbarLayout();
    const bar = activeHotbar();
    const boxTop = hb.btnY - 4;
    const boxH = hb.y + hb.h - boxTop + 8;
    ctx.strokeStyle = "#ccc";
    ctx.lineWidth = 2;
    ctx.strokeRect(hb.sx - 8, boxTop, hb.totalW + 16, boxH);
    ctx.fillStyle = hotbarPage === "weapons" ? "#d8d8d8" : "#555";
    ctx.fillRect(hb.sx, hb.btnY, hb.btnW, hb.btnH);
    ctx.fillStyle = hotbarPage === "builds" ? "#d8d8d8" : "#555";
    ctx.fillRect(hb.sx + hb.btnW + 4, hb.btnY, hb.btnW, hb.btnH);
    ctx.fillStyle = "#111";
    ctx.font = "bold 11px Courier New";
    ctx.textAlign = "center";
    ctx.fillText("A", hb.sx + hb.btnW / 2, hb.btnY + 14);
    ctx.fillText("B", hb.sx + hb.btnW + 4 + hb.btnW / 2, hb.btnY + 14);
    ctx.textAlign = "left";
    for (let i = 0; i < 8; i++) {
      const x = hb.sx + i * hb.slot;
      ctx.fillStyle = i === selectedSlot ? "#d8d8d8" : "#555";
      ctx.fillRect(x, hb.y, hb.slotW, hb.h);
      ctx.fillStyle = "#111";
      ctx.fillRect(x + 2, hb.y + 2, hb.slotW - 4, hb.h - 4);
      const it = bar[i];
      ctx.fillStyle = "#fff";
      ctx.font = "12px Courier New";
      ctx.fillText(String(i + 1), x + 4, hb.y + 12);
      if (it) {
        ctx.fillStyle = it.kind === "pickaxe" ? "#ffd27d" : it.kind === "mortar" ? "#90f0ff" : it.kind === "blade" ? "#ddd" : it.kind === "build" ? "#f2be7e" : "#ffe56d";
        ctx.fillText(it.name.slice(0, 8), x + 4, hb.y + 25);
        const hideQty = it.kind === "mortar";
        if (!hideQty && (it.qty > 1 || it.kind === "weapon" || it.kind === "build" || it.kind === "blade")) {
          ctx.fillStyle = "#9efca0";
          ctx.fillText(String(it.qty), x + hb.slotW - 14, hb.y + hb.h - 6);
        }
      }
    }
  }

  function drawDragGhost() {
    if (!dragInv || !started) return;
    const src = dragInv.from === "pack" ? backpack : hotbarArrayForPage(dragInv.page || hotbarPage);
    const it = src[dragInv.index];
    if (!it) return;
    const mx = dragInv.mx, my = dragInv.my;
    const w = 52, h = 38;
    ctx.save();
    ctx.globalAlpha = 0.94;
    ctx.fillStyle = "rgba(255, 252, 200, 0.96)";
    ctx.strokeStyle = "#ffffff";
    ctx.lineWidth = 3;
    ctx.fillRect(mx - w / 2, my - h / 2, w, h);
    ctx.strokeRect(mx - w / 2, my - h / 2, w, h);
      ctx.fillStyle = it.kind === "build" ? "#f2be7e" : it.kind === "mortar" ? "#90f0ff" : "#ffe56d";
    ctx.fillRect(mx - w / 2 + 6, my - 6, w - 12, 14);
    ctx.fillStyle = "#111";
    ctx.font = "bold 11px Courier New";
    ctx.textAlign = "center";
    ctx.fillText(it.name.slice(0, 9), mx, my + 14);
    ctx.restore();
  }

  function centerInvRect() {
    const panelW = 520;
    const panelH = 300;
    const x = Math.floor((canvas.width - panelW) / 2);
    const y = Math.floor((canvas.height - panelH) / 2);
    return { x, y, panelW, panelH };
  }

  function drawCenterInventory() {
    if (!showCenterInventory || !started) return;
    const r = centerInvRect();
    ctx.fillStyle = "rgba(0,0,0,.82)";
    ctx.fillRect(r.x, r.y, r.panelW, r.panelH);
    ctx.strokeStyle = "#888";
    ctx.strokeRect(r.x + 0.5, r.y + 0.5, r.panelW - 1, r.panelH - 1);
    ctx.fillStyle = "#fff";
    ctx.font = "13px Courier New";
    ctx.fillText("Inventory (Shift) — drag items between slots / hotbar", r.x + 10, r.y + 18);
    for (let i = 0; i < 32; i++) {
      const bx = r.x + 12 + (i % 8) * 62;
      const by = r.y + 28 + Math.floor(i / 8) * 62;
      ctx.fillStyle = "#222";
      ctx.fillRect(bx, by, 56, 56);
      const it = backpack[i];
      if (!it) continue;
      ctx.fillStyle = it.kind === "build" ? "#f2be7e" : it.kind === "mortar" ? "#90f0ff" : "#ffe56d";
      ctx.fillRect(bx + 8, by + 12, 40, 22);
      ctx.fillStyle = "#fff";
      ctx.font = "11px Courier New";
      ctx.fillText(it.name.slice(0, 8), bx + 5, by + 45);
      const hideQty = it.kind === "mortar";
      if (!hideQty && it.qty > 1) ctx.fillText(String(it.qty), bx + 40, by + 55);
    }
  }

  function drawToast() {
    if (!toast.text || performance.now() > toast.until) return;
    ctx.fillStyle = "rgba(0,0,0,.65)";
    ctx.fillRect(10, 10, Math.min(540, ctx.measureText(toast.text).width + 18), 26);
    ctx.fillStyle = "#fff";
    ctx.font = "14px Courier New";
    ctx.fillText(toast.text, 18, 28);
  }

  function drawBanners() {
    const now = performance.now();
    if (now < damageFlashUntil) {
      ctx.fillStyle = "rgba(255,255,255,0.55)";
      ctx.fillRect(0, 0, canvas.width, canvas.height);
    }
    if (now < superRareBannerUntil) {
      ctx.fillStyle = "rgba(0,0,0,0.55)";
      ctx.fillRect(0, canvas.height / 2 - 40, canvas.width, 80);
      ctx.fillStyle = "#ffd700";
      ctx.font = "bold 28px Courier New";
      ctx.textAlign = "center";
      ctx.fillText("SUPER RARE DUG", canvas.width / 2, canvas.height / 2 + 8);
      ctx.textAlign = "left";
    }
  }

  function clampTeleportTile(p) { return { x: Math.max(1, Math.min(WORLD_W - 2, p.x)), y: Math.max(1, Math.min(WORLD_H - 2, p.y)) }; }
  function parseTeleport(v) {
    const m = v.match(/^\s*\(?\s*(-?\d+)\s*,\s*(-?\d+)\s*\)?\s*$/);
    if (!m) return null;
    return { x: parseInt(m[1], 10), y: parseInt(m[2], 10) };
  }
  function parseItemCommandValue(raw) {
    const cleaned = raw.trim().toLowerCase();
    const parts = cleaned.split("_");
    const maybeAmt = parts[parts.length - 1];
    let qty = 1;
    let key = cleaned;
    if (/^\d+$/.test(maybeAmt)) { qty = Math.max(1, parseInt(maybeAmt, 10)); key = parts.slice(0, -1).join("_"); }
    return { key: key.replace(/\s+/g, "_"), qty };
  }

  function runCommand(text) {
    const t = text.trim().toLowerCase();
    if (t === "?commands") {
      log("[system] ?commands, ?digTime=, ?moveSpeed=, ?teleport=, ?resetPos, ?gravity=, ?normal, ?item=, ?list_items");
      return true;
    }
    if (t === "?list_items") { log("[system] Items: " + Object.keys(ITEM_CATALOG).join(", ")); return true; }
    if (t === "?resetpos") {
      randomSkySpawn(worldSurfaceY);
      player.vx = 0; player.vy = 0;
      log("[system] reset position (random top)");
      return true;
    }
    const m = text.match(/^\?([a-zA-Z]+)\s*=\s*(.+)\s*$/);
    if (!m) return false;
    const cmd = m[1].toLowerCase();
    const val = m[2];
    if (cmd === "digtime") { const n = Number(val); if (Number.isFinite(n)) { digTimeMs = Math.max(100, Math.min(20000, n)); log("[system] digTime=" + digTimeMs); } return true; }
    if (cmd === "movespeed") { const n = Number(val); if (Number.isFinite(n)) { moveSpeed = Math.max(40, Math.min(2000, n)); log("[system] moveSpeed=" + moveSpeed); } return true; }
    if (cmd === "gravity") { const n = Number(val); if (Number.isFinite(n)) { GRAVITY = Math.max(200, Math.min(8000, n)); log("[system] gravity=" + GRAVITY); } return true; }
    if (cmd === "teleport") {
      const p = parseTeleport(val); if (!p) return true;
      const c = clampTeleportTile(p);
      player.x = c.x * TILE - PLAYER_W / 2; player.y = c.y * TILE - PLAYER_H / 2; player.vx = 0; player.vy = 0;
      log("[system] teleported to (" + c.x + "," + c.y + ")");
      return true;
    }
    if (cmd === "item") {
      const parsed = parseItemCommandValue(val);
      const base = ITEM_CATALOG[parsed.key];
      if (!base) { log("[system] Unknown item. use ?list_items"); return true; }
      const item = { kind: base.kind, name: base.name, qty: parsed.qty };
      if (base.tile) item.tile = base.tile;
      const ok = base.kind === "weapon" || base.kind === "blade" ? addWeaponPreferBackpack(item) : addToStorage(item);
      if (ok) log("[system] added " + parsed.qty + "x " + base.name);
      else log("[system] inventories full");
      return true;
    }
    return true;
  }

  function sendChat() {
    let text = chatInput.value.trim();
    if (!text) return;
    if (text.length > 35) text = text.slice(0, 35);
    chatInput.value = "";
    if (text.startsWith("?")) {
      const low = text.toLowerCase();
      if (low === "?normal") {
        GRAVITY = baseGravity;
        moveSpeed = baseMoveSpeed;
        digTimeMs = 1250;
        log("[system] reset gravity, move speed, dig time to defaults");
        return;
      }
      runCommand(text);
      return;
    }
    log("[" + displayUsername() + "] " + text);
    player.chatBubble = { text, until: performance.now() + 4500 };
  }

  function toggleChatFocus() {
    if (document.activeElement === chatInput) {
      sendChat();
      chatInput.blur();
    } else {
      showChat = true;
      chatEl.classList.remove("hidden");
      chatInput.focus();
    }
  }
  function toggleChatVisibility() { showChat = !showChat; chatEl.classList.toggle("hidden", !showChat); }

  function hitHotbarIndex(mx, my) {
    if (hitHotbarSwitch(mx, my)) return -1;
    const hb = hotbarLayout();
    if (my < hb.y || my > hb.y + hb.h || mx < hb.sx || mx > hb.sx + hb.totalW) return -1;
    const i = Math.floor((mx - hb.sx) / hb.slot);
    return i >= 0 && i < 8 ? i : -1;
  }

  function hitBackpackIndex(mx, my) {
    const r = centerInvRect();
    const relX = mx - (r.x + 12);
    const relY = my - (r.y + 28);
    if (relX < 0 || relY < 0) return -1;
    const col = Math.floor(relX / 62), row = Math.floor(relY / 62);
    if (col < 0 || col >= 8 || row < 0 || row >= 4) return -1;
    return row * 8 + col;
  }

  function swapOrMove(a, ai, b, bi) {
    const tmp = a[ai];
    a[ai] = b[bi];
    b[bi] = tmp;
  }

  function onCanvasClick(e) {
    const hi = hitHotbarIndex(e.offsetX, e.offsetY);
    if (hi >= 0) { selectedSlot = hi; return true; }
    return false;
  }

  function startMode(mode) {
    username = (usernameInput.value || "miner").trim().slice(0, 20) || "miner";
    gameMode = mode;
    if (mode === "SHOP") buildShopWorld();
    else buildWorld();
    started = true;
    player.dead = false;
    camInitialized = false;
    document.body.classList.add("game-active");
    modeOverlay.style.display = "none";
    respawnBtn.style.display = "none";
    showChat = false;
    chatEl.classList.add("hidden");
    log("[system] " + displayUsername() + " joined " + mode);
  }

  function leaveToMenu() {
    started = false;
    mouseDownLeft = false;
    mouseDownPlace = false;
    camInitialized = false;
    document.body.classList.remove("game-active");
    modeOverlay.style.display = "grid";
    showCenterInventory = false;
    chatEl.classList.add("hidden");
    log("[system] Returned to main menu.");
  }

  function respawn() {
    randomSkySpawn(worldSurfaceY);
    player.vx = 0;
    player.vy = 0;
    player.hp = MAX_HP;
    player.hpDisplay = MAX_HP;
    player.dead = false;
    respawnBtn.style.display = "none";
  }

  let mouseDownPlace = false;

  function tryPlaceBuildHold(dt) {
    if (!mouseDownPlace || !started || player.dead || shopRules()) return;
    placeCooldown = Math.max(0, placeCooldown - dt);
    if (placeCooldown > 0) return;
    const sel = selectedItem();
    if (!sel || sel.kind !== "build" || sel.qty <= 0) return;
    const { tx, ty } = mouseTile();
    const key = tx + "," + ty;
    if (key === lastPlaceKey) return;
    const before = sel.qty;
    tryPlaceBuild();
    if (sel.qty < before) {
      lastPlaceKey = key;
      placeCooldown = 0.06;
    }
  }

  function tryShootOrDigClick() {
    if (!started || player.dead) return;
    if (shopRules()) {
      log("[system] You can't shoot or dig in SHOP");
      return;
    }
    const sel = selectedItem();
    if (hotbarPage === "builds") {
      if (sel && sel.kind === "build") {
        mouseDownPlace = true;
        lastPlaceKey = "";
        tryPlaceBuild();
      }
      return;
    }
    if (sel && sel.kind === "pickaxe") mouseDownLeft = true;
    else if (sel && sel.kind === "build") tryPlaceBuild();
    else fireCurrent();
  }

  let last = performance.now();
  function frame(now) {
    const dt = Math.min(0.05, (now - last) / 1000);
    last = now;
    resizeCanvas();
    if (started) {
      physics(dt);
      digUpdate(dt * 1000);
      tryPlaceBuildHold(dt);
      updateProjectiles(dt);
      updateDrops(dt);
      updatePremadeCannons(dt);
      pickupDrops();
      if (started && !player.dead && canShootNow()) {
        const sel = selectedItem();
        const profile = sel && sel.kind !== "pickaxe" && sel.kind !== "build" ? getWeaponProfile(sel) : null;
        if (profile && profile.mode !== "laserLine") updateTrajSmooth(profile, aimVector(), dt);
        else trajSmoothPts = [];
      } else {
        trajSmoothPts = [];
      }
      const follow = camFollow && bullets.indexOf(camFollow) >= 0 ? camFollow : null;
      const cw = canvas.width, ch = canvas.height;
      let targetX = Math.max(0, Math.min(WORLD_W * TILE - cw, (follow ? follow.x : center().x) - cw / 2));
      let targetY = Math.max(0, Math.min(WORLD_H * TILE - ch, (follow ? follow.y : center().y) - ch / 2));
      if (!camInitialized) {
        camSmoothX = targetX;
        camSmoothY = targetY;
        camInitialized = true;
      } else {
        const k = 1 - Math.exp(-4.2 * dt);
        camSmoothX += (targetX - camSmoothX) * k;
        camSmoothY += (targetY - camSmoothY) * k;
      }
      camX = camSmoothX;
      camY = camSmoothY;
    }
    ctx.fillStyle = "#78a8d8";
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    if (started) {
    drawWorld();
    drawTrajectory();
    drawProjectilesAndDrops();
    drawHover();
    drawDigFlash();
    drawPlayer();
    drawHotbar();
      drawDragGhost();
    drawCenterInventory();
    drawToast();
      drawBanners();
    }
    requestAnimationFrame(frame);
  }

  window.addEventListener("keydown", (e) => {
    const k = e.key.toLowerCase();
    if (k === "escape" && started) { e.preventDefault(); leaveToMenu(); return; }
    if (k === "enter") { e.preventDefault(); toggleChatFocus(); return; }
    if (document.activeElement === chatInput) return;
    if (k === "shift") { showCenterInventory = !showCenterInventory; return; }
    if (k === "h") { toggleChatVisibility(); return; }
    if (/^[1-8]$/.test(k)) { selectedSlot = Number(k) - 1; return; }
    if (player.dead) return;
    keys[k] = true;
  });
  window.addEventListener("keyup", (e) => { keys[e.key.toLowerCase()] = false; });
  canvas.addEventListener("mousemove", (e) => {
    const r = canvas.getBoundingClientRect();
    const sx = canvas.width / r.width;
    const sy = canvas.height / r.height;
    mouseX = (e.clientX - r.left) * sx;
    mouseY = (e.clientY - r.top) * sy;
    if (dragInv && started) {
      dragInv.mx = mouseX;
      dragInv.my = mouseY;
    }
  });

  canvas.addEventListener("mousedown", (e) => {
    if (!started) return;
    const pageSwitch = hitHotbarSwitch(e.offsetX, e.offsetY);
    if (pageSwitch) {
      hotbarPage = pageSwitch;
      return;
    }
    if (showCenterInventory) {
      const r = centerInvRect();
      if (e.offsetX >= r.x && e.offsetX <= r.x + r.panelW && e.offsetY >= r.y && e.offsetY <= r.y + r.panelH) {
        const bi = hitBackpackIndex(e.offsetX, e.offsetY);
        if (bi >= 0 && backpack[bi]) {
          dragInv = { from: "pack", index: bi, mx: mouseX, my: mouseY };
        }
        return;
      }
    }
    const hi = hitHotbarIndex(e.offsetX, e.offsetY);
    if (hi >= 0 && activeHotbar()[hi]) {
      dragInv = { from: "hot", page: hotbarPage, index: hi, mx: mouseX, my: mouseY };
      selectedSlot = hi;
      return;
    }
    if (e.button === 0) {
      if (onCanvasClick(e)) return;
      tryShootOrDigClick();
    }
  });

  canvas.addEventListener("mouseup", (e) => {
    if (e.button === 0) { mouseDownLeft = false; mouseDownPlace = false; lastPlaceKey = ""; }
    if (!dragInv || !started) return;
    const hi = hitHotbarIndex(mouseX, mouseY);
    const bi = showCenterInventory ? hitBackpackIndex(mouseX, mouseY) : -1;
    const targetBar = activeHotbar();
    const srcBar = dragInv.from === "hot" ? hotbarArrayForPage(dragInv.page) : null;
    if (dragInv.from === "pack" && hi >= 0) {
      swapOrMove(backpack, dragInv.index, targetBar, hi);
      selectedSlot = hi;
      cleanupInventory();
    } else if (dragInv.from === "hot" && hi >= 0 && hi !== dragInv.index) {
      swapOrMove(srcBar, dragInv.index, targetBar, hi);
      selectedSlot = hi;
    } else if (dragInv.from === "hot" && bi >= 0) {
      swapOrMove(srcBar, dragInv.index, backpack, bi);
      cleanupInventory();
    } else if (dragInv.from === "pack" && bi >= 0 && bi !== dragInv.index) {
      swapOrMove(backpack, dragInv.index, backpack, bi);
    }
    dragInv = null;
  });
  canvas.addEventListener("mouseleave", () => { mouseDownLeft = false; mouseDownPlace = false; dragInv = null; lastPlaceKey = ""; });
  canvas.addEventListener("contextmenu", (e) => e.preventDefault());

  chatSend.addEventListener("click", sendChat);
  btnBattle.addEventListener("click", () => startMode("Battle"));
  btnDigTrade.addEventListener("click", () => startMode("Dig + Trade"));
  btnShop.addEventListener("click", () => startMode("SHOP"));
  respawnBtn.addEventListener("click", respawn);

  window.addEventListener("resize", resizeCanvas);

  baseGravity = GRAVITY;
  moveSpeed = 200;
  baseMoveSpeed = 200;
  log("[system] Enter: chat, H: hide/show chat, ESC: menu.");
  chatEl.classList.add("hidden");
  tiles = new Uint8Array(WORLD_W * WORLD_H);
  cannonMeta = new Uint8Array(WORLD_W * WORLD_H);
  resizeCanvas();
  buildWorld();
  requestAnimationFrame(frame);
})();
