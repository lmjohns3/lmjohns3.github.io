// https://en.wikipedia.org/wiki/Penrose_tiling
// http://physics.princeton.edu/~steinh/growthQC.pdf
// https://github.com/Zygo/xscreensaver/blob/master/hacks/penrose.c

// This is an implementation of the Penrose tiling growth algorithm described in
// the "growthQC" paper, and implemented in the xscreensaver hack. I originally
// wanted to just translate the hack here, but the disconnect between C and
// Javascript was big enough that I went ahead and implemented my own version.
// Nonetheless, this code only exists thanks to the penrose.c code -- the corner
// hashing scheme comes from there, but I abandoned the C-style linked lists in
// favor of using Javascript's Map and Set classes, and developed my own logic
// for detecting badly-placed tiles.

import {hsluvToHex} from 'hsluv'

const ang = n => ((n % 10) + 10) % 10
const randint = n => Math.floor(n * Math.random()) >>> 0

////////////////////////////////////////////////////////////////////////////////
// Tile corners.

// There are thick and thin tiles, and each tile has 4 vertices: the "near"
// vertex is at the convergence of two double arrows (see Figure 1(a) in the
// paper), the "right" vertex is counterclockwise from that, the "far" vertex is
// next (and opposite from the "near" one), &c.
const THIN = 0b000, THICK = 0b100
const NEAR = 0b000, RIGHT = 0b001, FAR = 0b010, LEFT = 0b011

// If you are standing at a corner of type c looking towards the middle of the
// tile, left_neighbor(c) is the corner on your left, &c.
const right_neighbor = c => c + 1 & 0b11 | c & 0b100
const far_neighbor = c => c ^ 0b10
const left_neighbor = c => c - 1 & 0b11 | c & 0b100

// Thin/thick tile interior angles, in multiples of 36deg.
const ANGLES = [4, 1, 4, 1, 2, 3, 2, 3]

// Tables of sin and cos values for multiples of 36deg.
const COS = [...Array(10).keys()].map(i => Math.cos(Math.PI * i / 5))
const SIN = [...Array(10).keys()].map(i => Math.sin(Math.PI * i / 5))

// Directions around a vertex or circular path.
const CCW = 0, CW = 1

// Number of bits for each word in a corner hash.
const BITS = 3

// We pack a list of tile corners (up to 7 3-bit words) surrounding a vertex
// into a single integer. The lowest 3 bits specify the number of corners, and
// successively higher words encode tile corners, counterclockwise around the
// vertex. For example, with corners aaa bbb ccc we pack them as:
//
// 0 ... 0 c c c b b b a a a 0 1 1
// ------- ----- ----- ----- -----
//  empty    c     b     a     3
const _hash = (hash, corner, i) => corner << BITS * i | hash
const hashCorners = corners => corners.reduce(_hash, 0) << BITS | corners.length

const getLength = hash => hash & 0b111
const getMask = hash => ((1 << BITS * getLength(hash)) - 1) << BITS

// Rotate a corner hash by "rot" corners. This shifts the top rot*BITS to the
// bottom of the hash, and shifts the remaining rem*BITS upwards by rot*BITS.
const rotateHash = (hash, rot) => {
  const length = getLength(hash), rem = length - rot;
  return rot === 0 || length < 2 ? hash
       : (hash & (getMask(rot) << BITS * rem)) >> BITS * rem
       | (hash & getMask(rem)) << BITS * rot
       | length;
}

// Add a new word to an existing corner hash.
const addToHash = (hash, bits, high) => {
  const len = 1 + getLength(hash), mask = getMask(hash);
  return high ? bits << BITS * len | hash & mask | len
              : (hash & mask) << BITS | bits << BITS | len;
}

// Format a hash or bits for logging.
const formatBits = n => n.toString(2).padStart(BITS, '0');
const formatHash = hash => {
  const s = hash.toString(2).padStart(BITS * (1 + getLength(hash)), '0')
      , parts = [];
  for (let i = 0; i < s.length; i += 3) parts.push(s.slice(i, i+3));
  return parts.join('-');
}

// Valid combinations of corners at a vertex. These come from Figure 1(b) of the
// paper, clockwise starting from the star closest to the (b). Each rule starts
// at the tile at the top and goes counterclockwise around the central vertex.
const RULES = [
  hashCorners([THICK|NEAR, THICK|NEAR, THICK|NEAR, THICK|NEAR, THICK|NEAR]),
  hashCorners([THIN|FAR, THICK|RIGHT, THICK|LEFT]),
  hashCorners([THICK|NEAR, THICK|NEAR, THICK|NEAR, THIN|NEAR]),
  hashCorners([THICK|FAR, THIN|RIGHT, THIN|LEFT, THICK|FAR, THICK|FAR, THIN|RIGHT, THIN|LEFT]),
  hashCorners([THIN|LEFT, THICK|FAR, THICK|FAR, THICK|FAR, THICK|FAR, THIN|RIGHT]),
  hashCorners([THIN|NEAR, THICK|NEAR, THIN|NEAR]),
  hashCorners([THICK|FAR, THICK|FAR, THICK|FAR, THICK|FAR, THICK|FAR]),
  hashCorners([THICK|FAR, THIN|RIGHT, THICK|LEFT, THICK|RIGHT, THIN|LEFT]),
]

////////////////////////////////////////////////////////////////////////////////
// Vertex operations.

// Get a vertex object for a location. Creates vertices as needed. If x is a
// vertex object, returns that directly. If x is the key for an existing vertex,
// returns the associated object.
const getVertex = (x, y) => {
  if ((x || {}).key) return x;
  if (TILING.vertices.has(x)) return TILING.vertices.get(x);
  const round = n => Math.round(100 * n) / 100
      , allCorners = () => new Set(Array(8).keys())
      , key = `${round(x)}/${round(y)}`;
  if (!TILING.vertices.has(key))
    TILING.vertices.set(key, {
      key, x, y,              // Location of the vertex.
      corners: 0,             // Hash of tile corners.
      rules: new Set(RULES),  // Applicable tiling rules.
      angle: [null, null],    // Angles of ccw/cw side of gap.
      // Corners that can be placed on ccw/cw side of gap.
      completions: [allCorners(), allCorners()],
    });
  return TILING.vertices.get(key);
}

// Check which rules apply at a vertex with the given corners.
const checkRules = (corners, rules) => {
  const cornersLength = getLength(corners)
      , cornersMask = getMask(corners)
      , valid = new Set()
      , completions = [new Set(), new Set()];
  rules.forEach(rule => {
    const ruleLength = getLength(rule);
    if (ruleLength <= cornersLength) return;
    for (let i = 0; i < ruleLength; i++) {
      const rotated = rotateHash(rule, i);
      if (((rotated ^ corners) & cornersMask) !== 0) continue;
      valid.add(rule);
      // We've matched a rule, now add completions based on the rule. For
      // example if:
      //       rule = 000 xyz abc def ghi 011
      //     corner = 000 000 000 def ghi 010
      // we can add tile abc next to def (on the clockwise side of the tiling
      // gap) or xyz next to ghi (on the counterclockwise side).
      completions[CCW].add(rotated >> BITS*ruleLength);
      completions[CW].add((rotated >> BITS*(1+cornersLength)) & 0b111);
    }
  });
  return [valid, completions];
}

// Check whether a new tile connects to its neighbors in a valid way.
const wouldCreateHole = check => {
  let cur = check[0];
  const blocks = {};
  blocks[true] = cur ? 1 : 0;
  blocks[false] = cur ? 0 : 1;
  for (let i = 1; i < check.length; i++)
    if (check[i] !== cur) {
      cur = check[i];
      blocks[cur]++;
    }
  return blocks[true] > 2 || blocks[false] > 1;
}

// Create a new tile on one side of the gap at a vertex.
const createTile = (vertex, corner, side) => {
  if (vertex === null || corner === null || side === null) return null;

  const addOrRemove = (s, item, add) => add ? s.add(item) : s.delete(item);

  if (vertex.x < -TILING.size || vertex.x > TILING.size ||
      vertex.y < -TILING.size || vertex.y > TILING.size) {
    TILING.forced.delete(vertex.key);
    TILING.partial.delete(vertex.key);
    return null;
  }

  // Angles of each edge, traveling ccw starting from the given corner.
  const angleNR = ang(vertex.angle[side] - (side === CW ? 0 : ANGLES[corner]))
      , angleRF = ang(angleNR + 5 - ANGLES[right_neighbor(corner)])
      , angleFL = ang(angleRF + 5 - ANGLES[far_neighbor(corner)])
      , angleLN = ang(angleFL + 5 - ANGLES[left_neighbor(corner)]);

  // Tile vertices.
  const vertexN = vertex
      , vertexR = getVertex(vertexN.x + COS[angleNR], vertexN.y + SIN[angleNR])
      , vertexF = getVertex(vertexR.x + COS[angleRF], vertexR.y + SIN[angleRF])
      , vertexL = getVertex(vertexF.x + COS[angleFL], vertexF.y + SIN[angleFL]);

  if (wouldCreateHole([vertexN.angle[CW] === angleNR, vertexR.corners !== 0,
                       vertexR.angle[CW] === angleRF, vertexF.corners !== 0,
                       vertexF.angle[CW] === angleFL, vertexL.corners !== 0,
                       vertexL.angle[CW] === angleLN, vertexN.corners !== 0]))
    return null;

  // The far and left corners might need to be added to the cw or ccw side of
  // their gaps depending on the configuration of the existing tiles.
  const rightside = vertexR.angle[CW] === angleRF ? CW : CCW
      , farside = vertexF.angle[CW] === angleFL ? CW : CCW
      , leftside = vertexL.angle[CCW] === ang(5 + angleFL) ? CCW : CW;

  // Check that this vertex configuration is valid for the whole tile.
  if (!vertexN.completions[side].has(corner) ||
      !vertexR.completions[rightside].has(right_neighbor(corner)) ||
      !vertexF.completions[farside].has(far_neighbor(corner)) ||
      !vertexL.completions[leftside].has(left_neighbor(corner))) {
    vertex.completions[side].delete(corner);
    addOrRemove(TILING.forced, vertex.key,
                (vertex.completions[CCW].size === 1 ||
                 vertex.completions[CW].size === 1));
    return null;
  }

  // Add the new tile corners to the corresponding vertices.
  const addCorner = (v, a, c, s) => {
    if (v.angle[CW] === null) v.angle[CCW] = v.angle[CW] = ang(a);
    v.angle[s] = ang(v.angle[s] + (s === CW ? 1 : -1) * ANGLES[c]);
    v.corners = addToHash(v.corners, c, s === CW);
    [v.rules, v.completions] = checkRules(v.corners, v.rules);
    let vc = v.corners, gap = 10;
    for (let i = 0; i < getLength(v.corners); i++) {
      vc >>>= BITS;
      gap -= ANGLES[vc & 0b111];
    }
    addOrRemove(TILING.partial, v.key, gap > 0);
    addOrRemove(TILING.forced, v.key, (v.completions[CCW].size === 1 ||
                                       v.completions[CW].size === 1));
  };
  addCorner(vertexN, 0, corner, side);
  addCorner(vertexR, 5 + angleNR, right_neighbor(corner), rightside);
  addCorner(vertexF, 5 + angleRF, far_neighbor(corner), farside);
  addCorner(vertexL, angleLN, left_neighbor(corner), leftside);
  return {corner: corner,
          angle: angleNR,
          [NEAR]: vertexN,
          [RIGHT]: vertexR,
          [FAR]: vertexF,
          [LEFT]: vertexL};
}

////////////////////////////////////////////////////////////////////////////////
// Iteration.

// Draw a tile given by the locations of its vertices, and one corner type.
const drawTile = ({corner, angle, ...v}) => {
  const tile = corner & 0b100
      , hue = TILING.hue[tile] + 60 * Math.random()
      , path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  path.setAttribute('d', [`M ${v[NEAR].x} ${-v[NEAR].y}`,
                          `L ${v[RIGHT].x} ${-v[RIGHT].y}`,
                          `L ${v[FAR].x} ${-v[FAR].y}`,
                          `L ${v[LEFT].x} ${-v[LEFT].y}`,
                          'Z'].join(' '));
  path.setAttribute('fill', hsluvToHex([hue, 100, 80]));
  path.setAttribute('fill-opacity', tile ? 0.3 : 1);
  path.setAttribute('class', 'tile');
  path.setAttribute('style', 'opacity:0');
  TILING.svg.appendChild(path);
  setTimeout(() => path.setAttribute('style', 'opacity:1'), 1);

  //const corn = corner & 0b011
  //    , near = corn === RIGHT ? LEFT : corn === LEFT ? RIGHT : corn
  //    , base = angle + [0, 7, 5, 2, 0, 8, 5, 3][corner];
  //const arcAt = ({x, y}, radius, angle) => {
  //  const cc = t => [x + radius * COS[ang(t)], y + radius * SIN[ang(t)]];
  //  return ['M', ...cc(angle + (tile === THICK ? 2 : 4)),
  //          'A', radius, radius, 0, 0, 0, ...cc(angle)].join(' ');
  //};
  //const arcA = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  //arcA.setAttribute('d', arcAt(v[near], 0.2, base));
  //arcA.setAttribute('stroke', hsluvToHex([0, 70, 70]));
  //arcA.setAttribute('class', 'arc near');
  //TILING.svg.appendChild(arcA);
  //const arcB = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  //arcB.setAttribute(
  //  'd', arcAt(v[far_neighbor(near)], tile === THICK ? 0.8 : 0.2, 5 + base));
  //arcB.setAttribute('stroke', hsluvToHex([180, 70, 70]));
  //arcB.setAttribute('class', 'arc far');
  //TILING.svg.appendChild(arcB);

  //for (const t of document.querySelectorAll('#penrose text.angle'))
  //  t.parentNode.removeChild(t);
  //
  //const label = (v, s) => {
  //  const text = document.createElementNS('http://www.w3.org/2000/svg', 'text');
  //  text.setAttribute('x', v.x + 0.2 * COS[v.angle[s]]);
  //  text.setAttribute('y', -(v.y + 0.2 * SIN[v.angle[s]]));
  //  text.setAttribute('class', 'angle');
  //  text.innerHTML = v.angle[s];
  //  TILING.svg.appendChild(text);
  //};
  //
  //for (const [_, v] of TILING.vertices) if (v.angle[CW] !== v.angle[CCW]) {
  //  label(v, CW); label(v, CCW);
  //}
  //
  //const text = document.createElementNS('http://www.w3.org/2000/svg', 'text');
  //text.setAttribute('x', (v[NEAR].x + v[RIGHT].x + v[FAR].x + v[LEFT].x) / 4);
  //text.setAttribute('y', (v[NEAR].y + v[RIGHT].y + v[FAR].y + v[LEFT].y) / -4);
  //text.setAttribute('class', 'order');
  //text.innerHTML = TILING.vertices.size;
  //TILING.svg.appendChild(text);
}


// Add the next tile.
const step = () => {
  if (TILING.forced.size === 0) {
    TILING.hue[THICK] = 360 * Math.random();
    TILING.hue[THIN] = 360 * Math.random();
  }
  const {forced, partial} = TILING
      , uniform = s => {
        let i = randint(s.size);
        for (const e of s) if (i === 0) return e; else i--;
      }
      , vertex = getVertex(uniform(forced.size ? forced : partial))
      , ncw = vertex.completions[CW].size
      , nccw = vertex.completions[CCW].size
      , side = ncw === 1 && nccw !== 1 ? CW :
               ncw !== 1 && nccw === 1 ? CCW :
               ncw === 0 ? CCW :
               nccw === 0 ? CW :
               Math.random() < 0.5 ? CW : CCW
      , tile = createTile(vertex, uniform(vertex.completions[side]), side);
  if (tile) drawTile(tile);
}

// Run one frame of the animation process, which runs tiling steps at the
// desired rate.
const animate = millis => {
  if (TILING.millis === null)
    TILING.millis = millis;
  if (TILING.paused || millis - TILING.millis < 1000 / TILING.tps)
    return window.requestAnimationFrame(animate);
  if (TILING.forced.size + TILING.partial.size === 0)
    return restart();
  step();
  TILING.millis = millis;
  window.requestAnimationFrame(animate);
}

// Restart the tiling process.
const restart = () => {
  for (const tile of document.querySelectorAll('#penrose path.tile'))
    tile.setAttribute('style', 'opacity:0');

  TILING.vertices = new Map();
  TILING.partial = new Set();
  TILING.forced = new Set();

  TILING.hue = {[THICK]: 360 * Math.random(), [THIN]: 360 * Math.random()};
  TILING.size = 30;
  TILING.tps = 100;

  TILING.paused = false;
  TILING.millis = null;

  TILING.svg = document.getElementById('penrose');
  TILING.svg.innerHTML = '';
  TILING.svg.setAttribute('viewBox', [
    -TILING.size, -TILING.size, 2 * TILING.size, 2 * TILING.size,
  ].join(' '));

  const vertex = getVertex(0, 0), angle = randint(10);
  vertex.angle[CW] = vertex.angle[CCW] = angle;
  drawTile(createTile(vertex, randint(8), Math.random() < 0.5 ? CW : CCW));

  window.requestAnimationFrame(animate);
}

window.addEventListener('keydown', e => {
  if (e.code === 'KeyP') TILING.paused = !TILING.paused;
  if (e.code === 'KeyS') step();
  if (e.code === 'KeyZ') restart();
})

const TILING = {}

restart()
