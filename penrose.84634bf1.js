// modules are defined as an array
// [ module function, map of requires ]
//
// map of requires is short require name -> numeric require
//
// anything defined in a previous bundle is accessed via the
// orig method which is the require for previous bundles
parcelRequire = (function (modules, cache, entry, globalName) {
  // Save the require from previous bundle to this closure if any
  var previousRequire = typeof parcelRequire === 'function' && parcelRequire;
  var nodeRequire = typeof require === 'function' && require;

  function newRequire(name, jumped) {
    if (!cache[name]) {
      if (!modules[name]) {
        // if we cannot find the module within our internal map or
        // cache jump to the current global require ie. the last bundle
        // that was added to the page.
        var currentRequire = typeof parcelRequire === 'function' && parcelRequire;
        if (!jumped && currentRequire) {
          return currentRequire(name, true);
        }

        // If there are other bundles on this page the require from the
        // previous one is saved to 'previousRequire'. Repeat this as
        // many times as there are bundles until the module is found or
        // we exhaust the require chain.
        if (previousRequire) {
          return previousRequire(name, true);
        }

        // Try the node require function if it exists.
        if (nodeRequire && typeof name === 'string') {
          return nodeRequire(name);
        }

        var err = new Error('Cannot find module \'' + name + '\'');
        err.code = 'MODULE_NOT_FOUND';
        throw err;
      }

      localRequire.resolve = resolve;
      localRequire.cache = {};

      var module = cache[name] = new newRequire.Module(name);

      modules[name][0].call(module.exports, localRequire, module, module.exports, this);
    }

    return cache[name].exports;

    function localRequire(x){
      return newRequire(localRequire.resolve(x));
    }

    function resolve(x){
      return modules[name][1][x] || x;
    }
  }

  function Module(moduleName) {
    this.id = moduleName;
    this.bundle = newRequire;
    this.exports = {};
  }

  newRequire.isParcelRequire = true;
  newRequire.Module = Module;
  newRequire.modules = modules;
  newRequire.cache = cache;
  newRequire.parent = previousRequire;
  newRequire.register = function (id, exports) {
    modules[id] = [function (require, module) {
      module.exports = exports;
    }, {}];
  };

  var error;
  for (var i = 0; i < entry.length; i++) {
    try {
      newRequire(entry[i]);
    } catch (e) {
      // Save first error but execute all entries
      if (!error) {
        error = e;
      }
    }
  }

  if (entry.length) {
    // Expose entry point to Node, AMD or browser globals
    // Based on https://github.com/ForbesLindesay/umd/blob/master/template.js
    var mainExports = newRequire(entry[entry.length - 1]);

    // CommonJS
    if (typeof exports === "object" && typeof module !== "undefined") {
      module.exports = mainExports;

    // RequireJS
    } else if (typeof define === "function" && define.amd) {
     define(function () {
       return mainExports;
     });

    // <script>
    } else if (globalName) {
      this[globalName] = mainExports;
    }
  }

  // Override the current require with this new one
  parcelRequire = newRequire;

  if (error) {
    // throw error from earlier, _after updating parcelRequire_
    throw error;
  }

  return newRequire;
})({"node_modules/hsluv/hsluv.js":[function(require,module,exports) {
// Generated by Haxe 3.4.4
var hsluv = hsluv || {};
hsluv.Geometry = function() { };
hsluv.Geometry.intersectLineLine = function(a,b) {
	var x = (a.intercept - b.intercept) / (b.slope - a.slope);
	var y = a.slope * x + a.intercept;
	return { x : x, y : y};
};
hsluv.Geometry.distanceFromOrigin = function(point) {
	return Math.sqrt(Math.pow(point.x,2) + Math.pow(point.y,2));
};
hsluv.Geometry.distanceLineFromOrigin = function(line) {
	return Math.abs(line.intercept) / Math.sqrt(Math.pow(line.slope,2) + 1);
};
hsluv.Geometry.perpendicularThroughPoint = function(line,point) {
	var slope = -1 / line.slope;
	var intercept = point.y - slope * point.x;
	return { slope : slope, intercept : intercept};
};
hsluv.Geometry.angleFromOrigin = function(point) {
	return Math.atan2(point.y,point.x);
};
hsluv.Geometry.normalizeAngle = function(angle) {
	var m = 2 * Math.PI;
	return (angle % m + m) % m;
};
hsluv.Geometry.lengthOfRayUntilIntersect = function(theta,line) {
	return line.intercept / (Math.sin(theta) - line.slope * Math.cos(theta));
};
hsluv.Hsluv = function() { };
hsluv.Hsluv.getBounds = function(L) {
	var result = [];
	var sub1 = Math.pow(L + 16,3) / 1560896;
	var sub2 = sub1 > hsluv.Hsluv.epsilon ? sub1 : L / hsluv.Hsluv.kappa;
	var _g = 0;
	while(_g < 3) {
		var c = _g++;
		var m1 = hsluv.Hsluv.m[c][0];
		var m2 = hsluv.Hsluv.m[c][1];
		var m3 = hsluv.Hsluv.m[c][2];
		var _g1 = 0;
		while(_g1 < 2) {
			var t = _g1++;
			var top1 = (284517 * m1 - 94839 * m3) * sub2;
			var top2 = (838422 * m3 + 769860 * m2 + 731718 * m1) * L * sub2 - 769860 * t * L;
			var bottom = (632260 * m3 - 126452 * m2) * sub2 + 126452 * t;
			result.push({ slope : top1 / bottom, intercept : top2 / bottom});
		}
	}
	return result;
};
hsluv.Hsluv.maxSafeChromaForL = function(L) {
	var bounds = hsluv.Hsluv.getBounds(L);
	var min = Infinity;
	var _g = 0;
	while(_g < bounds.length) {
		var bound = bounds[_g];
		++_g;
		var length = hsluv.Geometry.distanceLineFromOrigin(bound);
		min = Math.min(min,length);
	}
	return min;
};
hsluv.Hsluv.maxChromaForLH = function(L,H) {
	var hrad = H / 360 * Math.PI * 2;
	var bounds = hsluv.Hsluv.getBounds(L);
	var min = Infinity;
	var _g = 0;
	while(_g < bounds.length) {
		var bound = bounds[_g];
		++_g;
		var length = hsluv.Geometry.lengthOfRayUntilIntersect(hrad,bound);
		if(length >= 0) {
			min = Math.min(min,length);
		}
	}
	return min;
};
hsluv.Hsluv.dotProduct = function(a,b) {
	var sum = 0;
	var _g1 = 0;
	var _g = a.length;
	while(_g1 < _g) {
		var i = _g1++;
		sum += a[i] * b[i];
	}
	return sum;
};
hsluv.Hsluv.fromLinear = function(c) {
	if(c <= 0.0031308) {
		return 12.92 * c;
	} else {
		return 1.055 * Math.pow(c,0.416666666666666685) - 0.055;
	}
};
hsluv.Hsluv.toLinear = function(c) {
	if(c > 0.04045) {
		return Math.pow((c + 0.055) / 1.055,2.4);
	} else {
		return c / 12.92;
	}
};
hsluv.Hsluv.xyzToRgb = function(tuple) {
	return [hsluv.Hsluv.fromLinear(hsluv.Hsluv.dotProduct(hsluv.Hsluv.m[0],tuple)),hsluv.Hsluv.fromLinear(hsluv.Hsluv.dotProduct(hsluv.Hsluv.m[1],tuple)),hsluv.Hsluv.fromLinear(hsluv.Hsluv.dotProduct(hsluv.Hsluv.m[2],tuple))];
};
hsluv.Hsluv.rgbToXyz = function(tuple) {
	var rgbl = [hsluv.Hsluv.toLinear(tuple[0]),hsluv.Hsluv.toLinear(tuple[1]),hsluv.Hsluv.toLinear(tuple[2])];
	return [hsluv.Hsluv.dotProduct(hsluv.Hsluv.minv[0],rgbl),hsluv.Hsluv.dotProduct(hsluv.Hsluv.minv[1],rgbl),hsluv.Hsluv.dotProduct(hsluv.Hsluv.minv[2],rgbl)];
};
hsluv.Hsluv.yToL = function(Y) {
	if(Y <= hsluv.Hsluv.epsilon) {
		return Y / hsluv.Hsluv.refY * hsluv.Hsluv.kappa;
	} else {
		return 116 * Math.pow(Y / hsluv.Hsluv.refY,0.333333333333333315) - 16;
	}
};
hsluv.Hsluv.lToY = function(L) {
	if(L <= 8) {
		return hsluv.Hsluv.refY * L / hsluv.Hsluv.kappa;
	} else {
		return hsluv.Hsluv.refY * Math.pow((L + 16) / 116,3);
	}
};
hsluv.Hsluv.xyzToLuv = function(tuple) {
	var X = tuple[0];
	var Y = tuple[1];
	var Z = tuple[2];
	var divider = X + 15 * Y + 3 * Z;
	var varU = 4 * X;
	var varV = 9 * Y;
	if(divider != 0) {
		varU /= divider;
		varV /= divider;
	} else {
		varU = NaN;
		varV = NaN;
	}
	var L = hsluv.Hsluv.yToL(Y);
	if(L == 0) {
		return [0,0,0];
	}
	var U = 13 * L * (varU - hsluv.Hsluv.refU);
	var V = 13 * L * (varV - hsluv.Hsluv.refV);
	return [L,U,V];
};
hsluv.Hsluv.luvToXyz = function(tuple) {
	var L = tuple[0];
	var U = tuple[1];
	var V = tuple[2];
	if(L == 0) {
		return [0,0,0];
	}
	var varU = U / (13 * L) + hsluv.Hsluv.refU;
	var varV = V / (13 * L) + hsluv.Hsluv.refV;
	var Y = hsluv.Hsluv.lToY(L);
	var X = 0 - 9 * Y * varU / ((varU - 4) * varV - varU * varV);
	var Z = (9 * Y - 15 * varV * Y - varV * X) / (3 * varV);
	return [X,Y,Z];
};
hsluv.Hsluv.luvToLch = function(tuple) {
	var L = tuple[0];
	var U = tuple[1];
	var V = tuple[2];
	var C = Math.sqrt(U * U + V * V);
	var H;
	if(C < 0.00000001) {
		H = 0;
	} else {
		var Hrad = Math.atan2(V,U);
		H = Hrad * 180.0 / Math.PI;
		if(H < 0) {
			H = 360 + H;
		}
	}
	return [L,C,H];
};
hsluv.Hsluv.lchToLuv = function(tuple) {
	var L = tuple[0];
	var C = tuple[1];
	var H = tuple[2];
	var Hrad = H / 360.0 * 2 * Math.PI;
	var U = Math.cos(Hrad) * C;
	var V = Math.sin(Hrad) * C;
	return [L,U,V];
};
hsluv.Hsluv.hsluvToLch = function(tuple) {
	var H = tuple[0];
	var S = tuple[1];
	var L = tuple[2];
	if(L > 99.9999999) {
		return [100,0,H];
	}
	if(L < 0.00000001) {
		return [0,0,H];
	}
	var max = hsluv.Hsluv.maxChromaForLH(L,H);
	var C = max / 100 * S;
	return [L,C,H];
};
hsluv.Hsluv.lchToHsluv = function(tuple) {
	var L = tuple[0];
	var C = tuple[1];
	var H = tuple[2];
	if(L > 99.9999999) {
		return [H,0,100];
	}
	if(L < 0.00000001) {
		return [H,0,0];
	}
	var max = hsluv.Hsluv.maxChromaForLH(L,H);
	var S = C / max * 100;
	return [H,S,L];
};
hsluv.Hsluv.hpluvToLch = function(tuple) {
	var H = tuple[0];
	var S = tuple[1];
	var L = tuple[2];
	if(L > 99.9999999) {
		return [100,0,H];
	}
	if(L < 0.00000001) {
		return [0,0,H];
	}
	var max = hsluv.Hsluv.maxSafeChromaForL(L);
	var C = max / 100 * S;
	return [L,C,H];
};
hsluv.Hsluv.lchToHpluv = function(tuple) {
	var L = tuple[0];
	var C = tuple[1];
	var H = tuple[2];
	if(L > 99.9999999) {
		return [H,0,100];
	}
	if(L < 0.00000001) {
		return [H,0,0];
	}
	var max = hsluv.Hsluv.maxSafeChromaForL(L);
	var S = C / max * 100;
	return [H,S,L];
};
hsluv.Hsluv.rgbToHex = function(tuple) {
	var h = "#";
	var _g = 0;
	while(_g < 3) {
		var i = _g++;
		var chan = tuple[i];
		var c = Math.round(chan * 255);
		var digit2 = c % 16;
		var digit1 = (c - digit2) / 16 | 0;
		h += hsluv.Hsluv.hexChars.charAt(digit1) + hsluv.Hsluv.hexChars.charAt(digit2);
	}
	return h;
};
hsluv.Hsluv.hexToRgb = function(hex) {
	hex = hex.toLowerCase();
	var ret = [];
	var _g = 0;
	while(_g < 3) {
		var i = _g++;
		var digit1 = hsluv.Hsluv.hexChars.indexOf(hex.charAt(i * 2 + 1));
		var digit2 = hsluv.Hsluv.hexChars.indexOf(hex.charAt(i * 2 + 2));
		var n = digit1 * 16 + digit2;
		ret.push(n / 255.0);
	}
	return ret;
};
hsluv.Hsluv.lchToRgb = function(tuple) {
	return hsluv.Hsluv.xyzToRgb(hsluv.Hsluv.luvToXyz(hsluv.Hsluv.lchToLuv(tuple)));
};
hsluv.Hsluv.rgbToLch = function(tuple) {
	return hsluv.Hsluv.luvToLch(hsluv.Hsluv.xyzToLuv(hsluv.Hsluv.rgbToXyz(tuple)));
};
hsluv.Hsluv.hsluvToRgb = function(tuple) {
	return hsluv.Hsluv.lchToRgb(hsluv.Hsluv.hsluvToLch(tuple));
};
hsluv.Hsluv.rgbToHsluv = function(tuple) {
	return hsluv.Hsluv.lchToHsluv(hsluv.Hsluv.rgbToLch(tuple));
};
hsluv.Hsluv.hpluvToRgb = function(tuple) {
	return hsluv.Hsluv.lchToRgb(hsluv.Hsluv.hpluvToLch(tuple));
};
hsluv.Hsluv.rgbToHpluv = function(tuple) {
	return hsluv.Hsluv.lchToHpluv(hsluv.Hsluv.rgbToLch(tuple));
};
hsluv.Hsluv.hsluvToHex = function(tuple) {
	return hsluv.Hsluv.rgbToHex(hsluv.Hsluv.hsluvToRgb(tuple));
};
hsluv.Hsluv.hpluvToHex = function(tuple) {
	return hsluv.Hsluv.rgbToHex(hsluv.Hsluv.hpluvToRgb(tuple));
};
hsluv.Hsluv.hexToHsluv = function(s) {
	return hsluv.Hsluv.rgbToHsluv(hsluv.Hsluv.hexToRgb(s));
};
hsluv.Hsluv.hexToHpluv = function(s) {
	return hsluv.Hsluv.rgbToHpluv(hsluv.Hsluv.hexToRgb(s));
};
hsluv.Hsluv.m = [[3.240969941904521,-1.537383177570093,-0.498610760293],[-0.96924363628087,1.87596750150772,0.041555057407175],[0.055630079696993,-0.20397695888897,1.056971514242878]];
hsluv.Hsluv.minv = [[0.41239079926595,0.35758433938387,0.18048078840183],[0.21263900587151,0.71516867876775,0.072192315360733],[0.019330818715591,0.11919477979462,0.95053215224966]];
hsluv.Hsluv.refY = 1.0;
hsluv.Hsluv.refU = 0.19783000664283;
hsluv.Hsluv.refV = 0.46831999493879;
hsluv.Hsluv.kappa = 903.2962962;
hsluv.Hsluv.epsilon = 0.0088564516;
hsluv.Hsluv.hexChars = "0123456789abcdef";
var root = {
    "hsluvToRgb": hsluv.Hsluv.hsluvToRgb,
    "rgbToHsluv": hsluv.Hsluv.rgbToHsluv,
    "hpluvToRgb": hsluv.Hsluv.hpluvToRgb,
    "rgbToHpluv": hsluv.Hsluv.rgbToHpluv,
    "hsluvToHex": hsluv.Hsluv.hsluvToHex,
    "hexToHsluv": hsluv.Hsluv.hexToHsluv,
    "hpluvToHex": hsluv.Hsluv.hpluvToHex,
    "hexToHpluv": hsluv.Hsluv.hexToHpluv,
    "lchToHpluv": hsluv.Hsluv.lchToHpluv,
    "hpluvToLch": hsluv.Hsluv.hpluvToLch,
    "lchToHsluv": hsluv.Hsluv.lchToHsluv,
    "hsluvToLch": hsluv.Hsluv.hsluvToLch,
    "lchToLuv": hsluv.Hsluv.lchToLuv,
    "luvToLch": hsluv.Hsluv.luvToLch,
    "xyzToLuv": hsluv.Hsluv.xyzToLuv,
    "luvToXyz": hsluv.Hsluv.luvToXyz,
    "xyzToRgb": hsluv.Hsluv.xyzToRgb,
    "rgbToXyz": hsluv.Hsluv.rgbToXyz,
    "lchToRgb": hsluv.Hsluv.lchToRgb,
    "rgbToLch": hsluv.Hsluv.rgbToLch
};

module.exports = root;

},{}],"penrose.js":[function(require,module,exports) {
"use strict";

var _hsluv = require("hsluv");

function _createForOfIteratorHelper(o, allowArrayLike) { var it; if (typeof Symbol === "undefined" || o[Symbol.iterator] == null) { if (Array.isArray(o) || (it = _unsupportedIterableToArray(o)) || allowArrayLike && o && typeof o.length === "number") { if (it) o = it; var i = 0; var F = function F() {}; return { s: F, n: function n() { if (i >= o.length) return { done: true }; return { done: false, value: o[i++] }; }, e: function e(_e2) { throw _e2; }, f: F }; } throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); } var normalCompletion = true, didErr = false, err; return { s: function s() { it = o[Symbol.iterator](); }, n: function n() { var step = it.next(); normalCompletion = step.done; return step; }, e: function e(_e3) { didErr = true; err = _e3; }, f: function f() { try { if (!normalCompletion && it.return != null) it.return(); } finally { if (didErr) throw err; } } }; }

function _objectWithoutProperties(source, excluded) { if (source == null) return {}; var target = _objectWithoutPropertiesLoose(source, excluded); var key, i; if (Object.getOwnPropertySymbols) { var sourceSymbolKeys = Object.getOwnPropertySymbols(source); for (i = 0; i < sourceSymbolKeys.length; i++) { key = sourceSymbolKeys[i]; if (excluded.indexOf(key) >= 0) continue; if (!Object.prototype.propertyIsEnumerable.call(source, key)) continue; target[key] = source[key]; } } return target; }

function _objectWithoutPropertiesLoose(source, excluded) { if (source == null) return {}; var target = {}; var sourceKeys = Object.keys(source); var key, i; for (i = 0; i < sourceKeys.length; i++) { key = sourceKeys[i]; if (excluded.indexOf(key) >= 0) continue; target[key] = source[key]; } return target; }

function _defineProperty(obj, key, value) { if (key in obj) { Object.defineProperty(obj, key, { value: value, enumerable: true, configurable: true, writable: true }); } else { obj[key] = value; } return obj; }

function _slicedToArray(arr, i) { return _arrayWithHoles(arr) || _iterableToArrayLimit(arr, i) || _unsupportedIterableToArray(arr, i) || _nonIterableRest(); }

function _nonIterableRest() { throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); }

function _iterableToArrayLimit(arr, i) { if (typeof Symbol === "undefined" || !(Symbol.iterator in Object(arr))) return; var _arr = []; var _n = true; var _d = false; var _e = undefined; try { for (var _i = arr[Symbol.iterator](), _s; !(_n = (_s = _i.next()).done); _n = true) { _arr.push(_s.value); if (i && _arr.length === i) break; } } catch (err) { _d = true; _e = err; } finally { try { if (!_n && _i["return"] != null) _i["return"](); } finally { if (_d) throw _e; } } return _arr; }

function _arrayWithHoles(arr) { if (Array.isArray(arr)) return arr; }

function _toConsumableArray(arr) { return _arrayWithoutHoles(arr) || _iterableToArray(arr) || _unsupportedIterableToArray(arr) || _nonIterableSpread(); }

function _nonIterableSpread() { throw new TypeError("Invalid attempt to spread non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method."); }

function _unsupportedIterableToArray(o, minLen) { if (!o) return; if (typeof o === "string") return _arrayLikeToArray(o, minLen); var n = Object.prototype.toString.call(o).slice(8, -1); if (n === "Object" && o.constructor) n = o.constructor.name; if (n === "Map" || n === "Set") return Array.from(o); if (n === "Arguments" || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(n)) return _arrayLikeToArray(o, minLen); }

function _iterableToArray(iter) { if (typeof Symbol !== "undefined" && Symbol.iterator in Object(iter)) return Array.from(iter); }

function _arrayWithoutHoles(arr) { if (Array.isArray(arr)) return _arrayLikeToArray(arr); }

function _arrayLikeToArray(arr, len) { if (len == null || len > arr.length) len = arr.length; for (var i = 0, arr2 = new Array(len); i < len; i++) { arr2[i] = arr[i]; } return arr2; }

var ang = function ang(n) {
  return (n % 10 + 10) % 10;
};

var randint = function randint(n) {
  return Math.floor(n * Math.random()) >>> 0;
}; ////////////////////////////////////////////////////////////////////////////////
// Tile corners.
// There are thick and thin tiles, and each tile has 4 vertices: the "near"
// vertex is at the convergence of two double arrows (see Figure 1(a) in the
// paper), the "right" vertex is counterclockwise from that, the "far" vertex is
// next (and opposite from the "near" one), &c.


var THIN = 0,
    THICK = 4;
var NEAR = 0,
    RIGHT = 1,
    FAR = 2,
    LEFT = 3; // If you are standing at a corner of type c looking towards the middle of the
// tile, left_neighbor(c) is the corner on your left, &c.

var right_neighbor = function right_neighbor(c) {
  return c + 1 & 3 | c & 4;
};

var far_neighbor = function far_neighbor(c) {
  return c ^ 2;
};

var left_neighbor = function left_neighbor(c) {
  return c - 1 & 3 | c & 4;
}; // Thin/thick tile interior angles, in multiples of 36deg.


var ANGLES = [4, 1, 4, 1, 2, 3, 2, 3]; // Tables of sin and cos values for multiples of 36deg.

var COS = _toConsumableArray(Array(10).keys()).map(function (i) {
  return Math.cos(Math.PI * i / 5);
});

var SIN = _toConsumableArray(Array(10).keys()).map(function (i) {
  return Math.sin(Math.PI * i / 5);
}); // Directions around a vertex or circular path.


var CCW = 0,
    CW = 1; // Number of bits for each word in a corner hash.

var BITS = 3; // We pack a list of tile corners (up to 7 3-bit words) surrounding a vertex
// into a single integer. The lowest 3 bits specify the number of corners, and
// successively higher words encode tile corners, counterclockwise around the
// vertex. For example, with corners aaa bbb ccc we pack them as:
//
// 0 ... 0 c c c b b b a a a 0 1 1
// ------- ----- ----- ----- -----
//  empty    c     b     a     3

var _hash = function _hash(hash, corner, i) {
  return corner << BITS * i | hash;
};

var hashCorners = function hashCorners(corners) {
  return corners.reduce(_hash, 0) << BITS | corners.length;
};

var getLength = function getLength(hash) {
  return hash & 7;
};

var getMask = function getMask(hash) {
  return (1 << BITS * getLength(hash)) - 1 << BITS;
}; // Rotate a corner hash by "rot" corners. This shifts the top rot*BITS to the
// bottom of the hash, and shifts the remaining rem*BITS upwards by rot*BITS.


var rotateHash = function rotateHash(hash, rot) {
  var length = getLength(hash),
      rem = length - rot;
  return rot === 0 || length < 2 ? hash : (hash & getMask(rot) << BITS * rem) >> BITS * rem | (hash & getMask(rem)) << BITS * rot | length;
}; // Add a new word to an existing corner hash.


var addToHash = function addToHash(hash, bits, high) {
  var len = 1 + getLength(hash),
      mask = getMask(hash);
  return high ? bits << BITS * len | hash & mask | len : (hash & mask) << BITS | bits << BITS | len;
}; // Format a hash or bits for logging.


var formatBits = function formatBits(n) {
  return n.toString(2).padStart(BITS, '0');
};

var formatHash = function formatHash(hash) {
  var s = hash.toString(2).padStart(BITS * (1 + getLength(hash)), '0'),
      parts = [];

  for (var i = 0; i < s.length; i += 3) {
    parts.push(s.slice(i, i + 3));
  }

  return parts.join('-');
}; // Valid combinations of corners at a vertex. These come from Figure 1(b) of the
// paper, clockwise starting from the star closest to the (b). Each rule starts
// at the tile at the top and goes counterclockwise around the central vertex.


var RULES = [hashCorners([THICK | NEAR, THICK | NEAR, THICK | NEAR, THICK | NEAR, THICK | NEAR]), hashCorners([THIN | FAR, THICK | RIGHT, THICK | LEFT]), hashCorners([THICK | NEAR, THICK | NEAR, THICK | NEAR, THIN | NEAR]), hashCorners([THICK | FAR, THIN | RIGHT, THIN | LEFT, THICK | FAR, THICK | FAR, THIN | RIGHT, THIN | LEFT]), hashCorners([THIN | LEFT, THICK | FAR, THICK | FAR, THICK | FAR, THICK | FAR, THIN | RIGHT]), hashCorners([THIN | NEAR, THICK | NEAR, THIN | NEAR]), hashCorners([THICK | FAR, THICK | FAR, THICK | FAR, THICK | FAR, THICK | FAR]), hashCorners([THICK | FAR, THIN | RIGHT, THICK | LEFT, THICK | RIGHT, THIN | LEFT])]; ////////////////////////////////////////////////////////////////////////////////
// Vertex operations.
// Get a vertex object for a location. Creates vertices as needed. If x is a
// vertex object, returns that directly. If x is the key for an existing vertex,
// returns the associated object.

var getVertex = function getVertex(x, y) {
  if ((x || {}).key) return x;
  if (TILING.vertices.has(x)) return TILING.vertices.get(x);

  var round = function round(n) {
    return Math.round(100 * n) / 100;
  },
      allCorners = function allCorners() {
    return new Set(Array(8).keys());
  },
      key = "".concat(round(x), "/").concat(round(y));

  if (!TILING.vertices.has(key)) TILING.vertices.set(key, {
    key: key,
    x: x,
    y: y,
    // Location of the vertex.
    corners: 0,
    // Hash of tile corners.
    rules: new Set(RULES),
    // Applicable tiling rules.
    angle: [null, null],
    // Angles of ccw/cw side of gap.
    // Corners that can be placed on ccw/cw side of gap.
    completions: [allCorners(), allCorners()]
  });
  return TILING.vertices.get(key);
}; // Check which rules apply at a vertex with the given corners.


var checkRules = function checkRules(corners, rules) {
  var cornersLength = getLength(corners),
      cornersMask = getMask(corners),
      valid = new Set(),
      completions = [new Set(), new Set()];
  rules.forEach(function (rule) {
    var ruleLength = getLength(rule);
    if (ruleLength <= cornersLength) return;

    for (var i = 0; i < ruleLength; i++) {
      var rotated = rotateHash(rule, i);
      if (((rotated ^ corners) & cornersMask) !== 0) continue;
      valid.add(rule); // We've matched a rule, now add completions based on the rule. For
      // example if:
      //       rule = 000 xyz abc def ghi 011
      //     corner = 000 000 000 def ghi 010
      // we can add tile abc next to def (on the clockwise side of the tiling
      // gap) or xyz next to ghi (on the counterclockwise side).

      completions[CCW].add(rotated >> BITS * ruleLength);
      completions[CW].add(rotated >> BITS * (1 + cornersLength) & 7);
    }
  });
  return [valid, completions];
}; // Check whether a new tile connects to its neighbors in a valid way.


var wouldCreateHole = function wouldCreateHole(check) {
  var cur = check[0];
  var blocks = {};
  blocks[true] = cur ? 1 : 0;
  blocks[false] = cur ? 0 : 1;

  for (var i = 1; i < check.length; i++) {
    if (check[i] !== cur) {
      cur = check[i];
      blocks[cur]++;
    }
  }

  return blocks[true] > 2 || blocks[false] > 1;
}; // Create a new tile on one side of the gap at a vertex.


var createTile = function createTile(vertex, corner, side) {
  var _ref;

  if (vertex === null || corner === null || side === null) return null;

  var addOrRemove = function addOrRemove(s, item, add) {
    return add ? s.add(item) : s.delete(item);
  };

  if (vertex.x < -TILING.size || vertex.x > TILING.size || vertex.y < -TILING.size || vertex.y > TILING.size) {
    TILING.forced.delete(vertex.key);
    TILING.partial.delete(vertex.key);
    return null;
  } // Angles of each edge, traveling ccw starting from the given corner.


  var angleNR = ang(vertex.angle[side] - (side === CW ? 0 : ANGLES[corner])),
      angleRF = ang(angleNR + 5 - ANGLES[right_neighbor(corner)]),
      angleFL = ang(angleRF + 5 - ANGLES[far_neighbor(corner)]),
      angleLN = ang(angleFL + 5 - ANGLES[left_neighbor(corner)]); // Tile vertices.

  var vertexN = vertex,
      vertexR = getVertex(vertexN.x + COS[angleNR], vertexN.y + SIN[angleNR]),
      vertexF = getVertex(vertexR.x + COS[angleRF], vertexR.y + SIN[angleRF]),
      vertexL = getVertex(vertexF.x + COS[angleFL], vertexF.y + SIN[angleFL]);
  if (wouldCreateHole([vertexN.angle[CW] === angleNR, vertexR.corners !== 0, vertexR.angle[CW] === angleRF, vertexF.corners !== 0, vertexF.angle[CW] === angleFL, vertexL.corners !== 0, vertexL.angle[CW] === angleLN, vertexN.corners !== 0])) return null; // The far and left corners might need to be added to the cw or ccw side of
  // their gaps depending on the configuration of the existing tiles.

  var rightside = vertexR.angle[CW] === angleRF ? CW : CCW,
      farside = vertexF.angle[CW] === angleFL ? CW : CCW,
      leftside = vertexL.angle[CCW] === ang(5 + angleFL) ? CCW : CW; // Check that this vertex configuration is valid for the whole tile.

  if (!vertexN.completions[side].has(corner) || !vertexR.completions[rightside].has(right_neighbor(corner)) || !vertexF.completions[farside].has(far_neighbor(corner)) || !vertexL.completions[leftside].has(left_neighbor(corner))) {
    vertex.completions[side].delete(corner);
    addOrRemove(TILING.forced, vertex.key, vertex.completions[CCW].size === 1 || vertex.completions[CW].size === 1);
    return null;
  } // Add the new tile corners to the corresponding vertices.


  var addCorner = function addCorner(v, a, c, s) {
    if (v.angle[CW] === null) v.angle[CCW] = v.angle[CW] = ang(a);
    v.angle[s] = ang(v.angle[s] + (s === CW ? 1 : -1) * ANGLES[c]);
    v.corners = addToHash(v.corners, c, s === CW);

    var _checkRules = checkRules(v.corners, v.rules);

    var _checkRules2 = _slicedToArray(_checkRules, 2);

    v.rules = _checkRules2[0];
    v.completions = _checkRules2[1];
    var vc = v.corners,
        gap = 10;

    for (var i = 0; i < getLength(v.corners); i++) {
      vc >>>= BITS;
      gap -= ANGLES[vc & 7];
    }

    addOrRemove(TILING.partial, v.key, gap > 0);
    addOrRemove(TILING.forced, v.key, v.completions[CCW].size === 1 || v.completions[CW].size === 1);
  };

  addCorner(vertexN, 0, corner, side);
  addCorner(vertexR, 5 + angleNR, right_neighbor(corner), rightside);
  addCorner(vertexF, 5 + angleRF, far_neighbor(corner), farside);
  addCorner(vertexL, angleLN, left_neighbor(corner), leftside);
  return _ref = {
    corner: corner,
    angle: angleNR
  }, _defineProperty(_ref, NEAR, vertexN), _defineProperty(_ref, RIGHT, vertexR), _defineProperty(_ref, FAR, vertexF), _defineProperty(_ref, LEFT, vertexL), _ref;
}; ////////////////////////////////////////////////////////////////////////////////
// Iteration.
// Draw a tile given by the locations of its vertices, and one corner type.


var drawTile = function drawTile(_ref2) {
  var corner = _ref2.corner,
      angle = _ref2.angle,
      v = _objectWithoutProperties(_ref2, ["corner", "angle"]);

  var tile = corner & 4,
      hue = TILING.hue[tile] + 60 * Math.random(),
      path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
  path.setAttribute('d', ["M ".concat(v[NEAR].x, " ").concat(-v[NEAR].y), "L ".concat(v[RIGHT].x, " ").concat(-v[RIGHT].y), "L ".concat(v[FAR].x, " ").concat(-v[FAR].y), "L ".concat(v[LEFT].x, " ").concat(-v[LEFT].y), 'Z'].join(' '));
  path.setAttribute('fill', (0, _hsluv.hsluvToHex)([hue, 100, 80]));
  path.setAttribute('fill-opacity', tile ? 0.3 : 1);
  path.setAttribute('class', 'tile');
  path.setAttribute('style', 'opacity:0');
  TILING.svg.appendChild(path);
  setTimeout(function () {
    return path.setAttribute('style', 'opacity:1');
  }, 1); //const corn = corner & 0b011
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
}; // Add the next tile.


var step = function step() {
  if (TILING.forced.size === 0) {
    TILING.hue[THICK] = 360 * Math.random();
    TILING.hue[THIN] = 360 * Math.random();
  }

  var forced = TILING.forced,
      partial = TILING.partial,
      uniform = function uniform(s) {
    var i = randint(s.size);

    var _iterator = _createForOfIteratorHelper(s),
        _step;

    try {
      for (_iterator.s(); !(_step = _iterator.n()).done;) {
        var e = _step.value;
        if (i === 0) return e;else i--;
      }
    } catch (err) {
      _iterator.e(err);
    } finally {
      _iterator.f();
    }
  },
      vertex = getVertex(uniform(forced.size ? forced : partial)),
      ncw = vertex.completions[CW].size,
      nccw = vertex.completions[CCW].size,
      side = ncw === 1 && nccw !== 1 ? CW : ncw !== 1 && nccw === 1 ? CCW : ncw === 0 ? CCW : nccw === 0 ? CW : Math.random() < 0.5 ? CW : CCW,
      tile = createTile(vertex, uniform(vertex.completions[side]), side);

  if (tile) drawTile(tile);
}; // Run one frame of the animation process, which runs tiling steps at the
// desired rate.


var animate = function animate(millis) {
  if (TILING.millis === null) TILING.millis = millis;
  if (TILING.paused || millis - TILING.millis < 1000 / TILING.tps) return window.requestAnimationFrame(animate);
  if (TILING.forced.size + TILING.partial.size === 0) return restart();
  step();
  TILING.millis = millis;
  window.requestAnimationFrame(animate);
}; // Restart the tiling process.


var restart = function restart() {
  var _TILING$hue;

  var _iterator2 = _createForOfIteratorHelper(document.querySelectorAll('#penrose path.tile')),
      _step2;

  try {
    for (_iterator2.s(); !(_step2 = _iterator2.n()).done;) {
      var tile = _step2.value;
      tile.setAttribute('style', 'opacity:0');
    }
  } catch (err) {
    _iterator2.e(err);
  } finally {
    _iterator2.f();
  }

  TILING.vertices = new Map();
  TILING.partial = new Set();
  TILING.forced = new Set();
  TILING.hue = (_TILING$hue = {}, _defineProperty(_TILING$hue, THICK, 360 * Math.random()), _defineProperty(_TILING$hue, THIN, 360 * Math.random()), _TILING$hue);
  TILING.size = 30;
  TILING.tps = 100;
  TILING.paused = false;
  TILING.millis = null;
  TILING.svg = document.getElementById('penrose');
  TILING.svg.innerHTML = '';
  TILING.svg.setAttribute('viewBox', [-TILING.size, -TILING.size, 2 * TILING.size, 2 * TILING.size].join(' '));
  var vertex = getVertex(0, 0),
      angle = randint(10);
  vertex.angle[CW] = vertex.angle[CCW] = angle;
  drawTile(createTile(vertex, randint(8), Math.random() < 0.5 ? CW : CCW));
  window.requestAnimationFrame(animate);
};

window.addEventListener('keydown', function (e) {
  if (e.code === 'KeyP') TILING.paused = !TILING.paused;
  if (e.code === 'KeyS') step();
  if (e.code === 'KeyZ') restart();
});
var TILING = {};
restart();
},{"hsluv":"node_modules/hsluv/hsluv.js"}]},{},["penrose.js"], null)