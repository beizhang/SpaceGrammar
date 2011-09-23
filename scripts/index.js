
/**
 * @author ZHANG Bei <zhang.bei@extjs.com>
 *         Sept 22, 2011
*/

var DisjointSet, SpaceGrammar, animtionInterval, auxinfo, boxNames, boxes, ctx, gen, key2arr, lastTemp, parse, parser, render, results, rules, sentences, value2arr, value2pairs, where, _ref;
var __hasProp = Object.prototype.hasOwnProperty;

where = function(obj, callback) {
  var item, key, res;
  res = {};
  for (key in obj) {
    if (!__hasProp.call(obj, key)) continue;
    item = obj[key];
    if (callback(key, item) !== false) res[key] = item;
  }
  return res;
};

key2arr = function(obj) {
  var key, value, _results;
  _results = [];
  for (key in obj) {
    if (!__hasProp.call(obj, key)) continue;
    value = obj[key];
    _results.push(key);
  }
  return _results;
};

value2arr = function(obj) {
  var key, value, _results;
  _results = [];
  for (key in obj) {
    if (!__hasProp.call(obj, key)) continue;
    value = obj[key];
    _results.push(value);
  }
  return _results;
};

value2pairs = function(obj) {
  var key, value, _results;
  _results = [];
  for (key in obj) {
    if (!__hasProp.call(obj, key)) continue;
    value = obj[key];
    _results.push({
      key: key,
      value: value
    });
  }
  return _results;
};

Math.sgn = function(x) {
  if (x > 0) {
    return 1;
  } else if (x < 0) {
    return -1;
  } else {
    return 0;
  }
};

Math.nrand = function() {
  var c, r, rad, x1, x2;
  if (Math.__lastc2 != null) {
    r = Math.__lastc2;
    delete Math.__lastc2;
    return r;
  }
  rad = 2;
  while (rad >= 1) {
    x1 = 2 * Math.random() - 1;
    x2 = 2 * Math.random() - 1;
    rad = x1 * x1 + x2 * x2;
  }
  if (rad === 0) return 0;
  c = Math.sqrt(-2 * Math.log(rad) / rad);
  Math.__lastc2 = x2 * c;
  return x1 * c;
};

DisjointSet = (function() {

  /**
   * @class DisjointSet
   * @constructor
  */

  function DisjointSet(list) {
    var name, _i, _len;
    this.parent = {};
    this.rank = {};
    for (_i = 0, _len = list.length; _i < _len; _i++) {
      name = list[_i];
      this.parent[name] = name;
      this.rank[name] = 0;
    }
  }

  DisjointSet.prototype.get = function(name) {
    if (this.parent[name] === name) return name;
    return this.parent[name] = this.get(this.parent[name]);
  };

  DisjointSet.prototype.union = function(x, y) {
    var parent, rank;
    x = this.get(x);
    y = this.get(y);
    if (x === y) return false;
    rank = this.rank;
    parent = this.parent;
    if (rank[x] > rank[y]) {
      parent[y] = parent[x];
    } else {
      parent[x] = parent[y];
      if (rank[x] === rank[y]) rank[y]++;
    }
    return true;
  };

  return DisjointSet;

})();

SpaceGrammar = {
  Box: (function() {

    function _Class(name, parts) {
      this.name = name;
      this.parts = parts;
    }

    _Class.prototype.draw = function(ctx) {
      var me;
      me = this;
      ctx.fillStyle = 'white';
      ctx.beginPath();
      ctx.rect(me.parts[0][0], me.parts[1][0], me.parts[0][1] - me.parts[0][0], me.parts[1][1] - me.parts[1][0]);
      ctx.fill();
      ctx.stroke();
      ctx.fillStyle = 'black';
      return ctx.fillText(me.name, (me.parts[0][0] + me.parts[0][1]) * 0.5, (me.parts[1][0] + me.parts[1][1]) * 0.5);
    };

    return _Class;

  })(),
  Parser: (function() {

    function _Class() {
      this.reset();
    }

    _Class.prototype.reset = function() {};

    _Class.prototype.slotMap = {
      'R1': [1, 3],
      'R2': [1, 2],
      'R3': [0, 2],
      'R4': [0, 3],
      'R5': [2, 2],
      'R6': [0, 4],
      'R7': [0, 0],
      'R8': [0, 1]
    };

    _Class.prototype.parseWord = function(word) {
      var slot;
      if (this.slotMap[word]) return this.slotMap[word];
      if (word.substr(0, 1) !== '-') return false;
      word = word.substr(1);
      if (this.slotMap[word]) slot = this.slotMap[word];
      if (slot) return [4 - slot[1], 4 - slot[0]];
      return false;
    };

    _Class.prototype.parse = function(text) {
      var a, b, boxNames, matches, phrase, regexp, rule, rules, words, x, y, z;
      regexp = /(\{.*?\})/g;
      rules = [];
      boxNames = {};
      text = text.replace('', '').replace(' ', '');
      while ((matches = regexp.exec(text)) !== null) {
        phrase = matches[1];
        phrase = phrase.substr(1, phrase.length - 2);
        words = phrase.split(',');
        a = words[0];
        b = words[1];
        x = this.parseWord(words[2]);
        y = this.parseWord(words[3]);
        z = this.parseWord(words[4]);
        rule = [a, b, x, y, z];
        rule.text = phrase;
        rules.push(rule);
        boxNames[a] = [];
        boxNames[b] = [];
      }
      return [rules, key2arr(boxNames)];
    };

    return _Class;

  })(),
  Generator: (function() {

    function _Class() {
      this.reset();
    }

    _Class.prototype.reset = function() {};

    _Class.prototype.auxTag = ['x-', 'x+', 'y-', 'y+', 'z-', 'z+'];

    _Class.prototype.config = {
      farRange: [30, 60],
      nearRange: [5, 10],
      targetArea: [800, 2000]
    };

    _Class.prototype.randomRange = function(range) {
      return Math.abs(Math.nrand() * (range[1] - range[0]) * 0.5 + (range[1] + range[0]) * 0.5);
    };

    _Class.prototype.analysisAux = function(rules, boxNames) {
      var addRel, aux, auxNames, base, baseh, basel, bottom, child, children, curr, d, derived, dir, ds, name, parents, queue, rule, s, sign, slot, target, _base, _i, _j, _k, _l, _len, _len2, _len3, _len4, _len5, _len6, _len7, _len8, _len9, _m, _n, _ref, _ref2, _ref3, _ref4;
      aux = {
        box: {}
      };
      _ref = ['x', 'y', 'z'];
      for (d = 0, _len = _ref.length; d < _len; d++) {
        dir = _ref[d];
        auxNames = [];
        for (_i = 0, _len2 = boxNames.length; _i < _len2; _i++) {
          name = boxNames[_i];
          auxNames.push(name + dir + '+');
          auxNames.push(name + dir + '-');
        }
        ds = new DisjointSet(auxNames);
        parents = {};
        children = {};
        addRel = function(lo, hi, type) {
          if (type == null) type = 'near';
          if (children[lo][hi]) {
            if (children[lo][hi] === 'near' && type === 'far') {
              children[lo][hi] = 'far';
            }
            return;
          }
          parents[hi]++;
          children[hi].parents = parents[hi];
          children[hi].top = false;
          return children[lo][hi] = type;
        };
        for (_j = 0, _len3 = rules.length; _j < _len3; _j++) {
          rule = rules[_j];
          base = rule[0] + dir;
          derived = rule[1] + dir;
          if (!base || !derived || base === derived || !(slot = rule[d + 2])) {
            continue;
          }
          _ref2 = ['-', '+'];
          for (s = 0, _len4 = _ref2.length; s < _len4; s++) {
            sign = _ref2[s];
            target = derived + sign;
            switch (slot[s]) {
              case 1:
                ds.union(target, base + '-');
                break;
              case 3:
                ds.union(target, base + '+');
            }
          }
        }
        for (_k = 0, _len5 = boxNames.length; _k < _len5; _k++) {
          name = boxNames[_k];
          if (ds.get(name + dir + '-') === name + dir + '-') {
            parents[name + dir + '-'] = 0;
            children[name + dir + '-'] = {
              top: true,
              parents: 0
            };
          }
          if (ds.get(name + dir + '+') === name + dir + '+') {
            parents[name + dir + '+'] = 0;
            children[name + dir + '+'] = {
              top: true,
              parents: 0
            };
          }
        }
        for (_l = 0, _len6 = boxNames.length; _l < _len6; _l++) {
          name = boxNames[_l];
          addRel(ds.get(name + dir + '-'), ds.get(name + dir + '+'), 'far');
        }
        for (_m = 0, _len7 = rules.length; _m < _len7; _m++) {
          rule = rules[_m];
          base = rule[0] + dir;
          derived = rule[1] + dir;
          if (!base || !derived || !(slot = rule[d + 2])) continue;
          basel = ds.get(base + '-');
          baseh = ds.get(base + '+');
          _ref3 = ['-', '+'];
          for (s = 0, _len8 = _ref3.length; s < _len8; s++) {
            sign = _ref3[s];
            target = ds.get(derived + sign);
            switch (slot[s]) {
              case 0:
                if (((slot[0] & 1) === 0 || (slot[1] & 1) === 0) && (target === basel)) {
                  console.error('Contradictive rule: ' + rule.text);
                } else {
                  addRel(target, basel);
                }
                break;
              case 2:
                if (((slot[0] & 1) === 0 || (slot[1] & 1) === 0) && basel === target) {
                  console.error('Contradictive rule: ' + rule.text);
                } else {
                  addRel(basel, target);
                }
                if (((slot[0] & 1) === 0 || (slot[1] & 1) === 0) && target === baseh) {
                  console.error('Contradictive rule: ' + rule.text);
                } else {
                  addRel(target, baseh);
                }
                break;
              case 4:
                if (((slot[0] & 1) === 0 || (slot[1] & 1) === 0) && baseh === target) {
                  console.error('Contradictive rule: ' + rule.text);
                } else {
                  addRel(baseh, target);
                }
            }
          }
        }
        queue = key2arr(where(parents, function(key, item) {
          return item === 0;
        }));
        bottom = 0;
        while (bottom < queue.length) {
          curr = queue[bottom++];
          for (child in children[curr]) {
            if (child === 'top') continue;
            parents[child]--;
            if (parents[child] === 0) queue.push(child);
          }
        }
        if (queue.length < parents.length) {
          console.error("Contradictive rules. (Cyclic order on " + dir + " axis)");
        }
        for (_n = 0, _len9 = boxNames.length; _n < _len9; _n++) {
          name = boxNames[_n];
          if ((_ref4 = (_base = aux['box'])[name]) == null) _base[name] = {};
          aux['box'][name][dir] = [ds.get(name + dir + '-'), ds.get(name + dir + '+')];
        }
        aux[dir] = where(children, function(key, item) {
          return ds.get(key) === key;
        });
      }
      return aux;
    };

    _Class.prototype.generateAux = function(children) {
      var a, aux, bottom, child, curr, d, diff2, dir, far, i, item, name, near, next, parents, pos, position, queue, removingBranch, results, ri, root, roots, _i, _j, _len, _len2, _len3, _len4, _ref;
      near = this.config.nearRange;
      far = this.config.farRange;
      results = {};
      _ref = ['x', 'y', 'z'];
      for (d = 0, _len = _ref.length; d < _len; d++) {
        dir = _ref[d];
        position = {};
        aux = children[dir];
        parents = {};
        for (name in aux) {
          a = aux[name];
          position[name] = [];
        }
        roots = key2arr(where(aux, function(key, item) {
          return item.top;
        }));
        for (ri = 0, _len2 = roots.length; ri < _len2; ri++) {
          root = roots[ri];
          position[root] = [0, root];
        }
        for (name in aux) {
          a = aux[name];
          parents[name] = a.parents;
        }
        queue = roots.slice(0);
        bottom = 0;
        while (bottom < queue.length) {
          curr = queue[bottom++];
          pos = position[curr];
          for (child in aux[curr]) {
            if (child !== 'top' && child !== 'parents') {
              parents[child]--;
              next = pos[0] + (function() {
                switch (aux[curr][child]) {
                  case 'near':
                    return this.randomRange(near);
                  case 'far':
                    return this.randomRange(far);
                }
              }).call(this);
              if (position[child].length) {
                if (position[child][1] !== pos[1]) {
                  removingBranch = position[child][1];
                  diff2 = next - position[child][0];
                  for (_i = 0, _len3 = queue.length; _i < _len3; _i++) {
                    item = queue[_i];
                    if (position[item].length === 2 && position[item][1] === removingBranch) {
                      position[item][0] += diff2;
                      position[item][1] = pos[1];
                    }
                  }
                  position[child] = [next, pos[1]];
                } else {
                  if (position[child][0] < next) position[child][0] = next;
                }
              } else {
                position[child] = [next, pos[1]];
              }
              if (parents[child] === 0) queue.push(child);
            }
          }
        }
        results[dir] = {};
        for (_j = 0, _len4 = queue.length; _j < _len4; _j++) {
          i = queue[_j];
          results[dir][i] = position[i][0];
        }
      }
      return results;
    };

    _Class.prototype.beautifyAux = function(auxinfo, results) {
      var area, axis, box, boxRange, delta, dir, i, name, parts, presure, ratio, sizex, sizey, targetArea, _ref;
      delta = 5;
      boxRange = this.config.farRange;
      targetArea = this.config.targetArea;
      for (i = 1; i <= 100; i++) {
        presure = {
          x: {},
          y: {}
        };
        for (name in auxinfo.x) {
          presure.x[name] = 0;
        }
        for (name in auxinfo.y) {
          presure.y[name] = 0;
        }
        _ref = auxinfo.box;
        for (name in _ref) {
          box = _ref[name];
          parts = (function() {
            var _i, _len, _ref2, _results;
            _ref2 = ['x', 'y', 'z'];
            _results = [];
            for (_i = 0, _len = _ref2.length; _i < _len; _i++) {
              dir = _ref2[_i];
              _results.push((function() {
                var _j, _len2, _ref3, _results2;
                _ref3 = auxinfo.box[name][dir];
                _results2 = [];
                for (_j = 0, _len2 = _ref3.length; _j < _len2; _j++) {
                  axis = _ref3[_j];
                  _results2.push(results[dir][axis]);
                }
                return _results2;
              })());
            }
            return _results;
          })();
          sizex = parts[0][1] - parts[0][0];
          sizey = parts[1][1] - parts[1][0];
          ratio = sizex / sizey;
          ratio = Math.log(ratio);
          ratio = Math.sgn(ratio) * Math.max(0, Math.abs(ratio) - Math.LN2);
          if (isNaN(ratio)) continue;
          presure.x[auxinfo.box[name].x[0]] -= ratio;
          presure.x[auxinfo.box[name].x[1]] += ratio;
          presure.y[auxinfo.box[name].y[1]] -= ratio;
          presure.y[auxinfo.box[name].y[0]] += ratio;
          ratio = 0;
          if (sizex < boxRange[0]) {
            ratio = Math.log(boxRange[0] / sizex);
          } else if (sizex > boxRange[1]) {
            ratio = Math.log(boxRange[1] / sizex);
          }
          presure.x[auxinfo.box[name].x[0]] += ratio;
          presure.x[auxinfo.box[name].x[1]] -= ratio;
          ratio = 0;
          if (sizey < boxRange[0]) {
            ratio = Math.log(boxRange[0] / sizey);
          } else if (sizey > boxRange[1]) {
            ratio = Math.log(boxRange[1] / sizey);
          }
          presure.y[auxinfo.box[name].y[0]] += ratio;
          presure.y[auxinfo.box[name].y[1]] -= ratio;
          ratio = 0;
          area = sizex * sizey;
          if (area < targetArea[0]) {
            ratio = Math.log(targetArea[0] / area) / 2;
          } else if (area > targetArea[1]) {
            ratio = Math.log(targetArea[1] / area) / 2;
          }
          presure.x[auxinfo.box[name].x[0]] += ratio;
          presure.x[auxinfo.box[name].x[1]] -= ratio;
          presure.y[auxinfo.box[name].y[0]] += ratio;
          presure.y[auxinfo.box[name].y[1]] -= ratio;
        }
        for (name in presure.x) {
          results.x[name] -= presure.x[name] * delta;
        }
        for (name in presure.y) {
          results.y[name] -= presure.y[name] * delta;
        }
      }
      return results;
    };

    return _Class;

  })()
};

/*
Initializting
*/

if (navigator.userAgent.match(/Android/i) || navigator.userAgent.match(/webOS/i) || navigator.userAgent.match(/iPhone/i) || navigator.userAgent.match(/iPad/i) || navigator.userAgent.match(/iPod/i)) {
  $.isTouch = true;
  $('body').addClass('touch').bind('touchstart', function(ev) {
    return ev.preventDefault();
  });
  $.clickEventName = 'touchstart';
} else {
  $.clickEventName = 'click';
}

sentences = [];

parser = new SpaceGrammar.Parser;

gen = new SpaceGrammar.Generator;

rules = [];

lastTemp = '';

boxNames = [];

auxinfo = [];

results = [];

boxes = [];

ctx = $('canvas')[0].getContext('2d');

animtionInterval = 0;

render = function() {
  var axis, dir, maxx, maxy, minx, miny, name, parts, rs, rs2, _i, _len;
  ctx.clearRect(0, 0, $('canvas').width(), $('canvas').height());
  ctx.fillStyle = 'white';
  ctx.strokeStyle = 'black';
  ctx.lineWidth = 2;
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  if (sentences) {
    ctx.beginPath();
    rs = JSON.stringify(results);
    results = gen.beautifyAux(auxinfo, results);
    rs2 = JSON.stringify(results);
    boxes = [];
    for (_i = 0, _len = boxNames.length; _i < _len; _i++) {
      name = boxNames[_i];
      parts = (function() {
        var _j, _len2, _ref, _results;
        _ref = ['x', 'y', 'z'];
        _results = [];
        for (_j = 0, _len2 = _ref.length; _j < _len2; _j++) {
          dir = _ref[_j];
          _results.push((function() {
            var _k, _len3, _ref2, _results2;
            _ref2 = auxinfo.box[name][dir];
            _results2 = [];
            for (_k = 0, _len3 = _ref2.length; _k < _len3; _k++) {
              axis = _ref2[_k];
              _results2.push(results[dir][axis]);
            }
            return _results2;
          })());
        }
        return _results;
      })();
      boxes.push(new SpaceGrammar.Box(name, parts));
    }
    minx = miny = -Infinity;
    maxx = maxy = Infinity;
    $.each(boxes, function(k, b) {
      if (b.parts[0][0] > minx) minx = b.parts[0][0];
      if (b.parts[0][1] < maxx) maxx = b.parts[0][1];
      if (b.parts[1][0] > miny) miny = b.parts[1][0];
      if (b.parts[1][1] < maxy) return maxy = b.parts[1][1];
    });
    ctx.save();
    ctx.translate(($('canvas').width() - (minx + maxx)) * 0.5, ($('canvas').height() - (miny + maxy)) * 0.5);
    $.each(boxes, function(k, b) {
      return b.draw(ctx);
    });
    return ctx.restore();
  }
};

parse = function() {
  var temp;
  temp = parser.parse(localStorage.lastSentence = $('textarea').val());
  if (JSON.stringify(temp) === lastTemp) return;
  lastTemp = JSON.stringify(temp);
  rules = temp[0], boxNames = temp[1];
  auxinfo = gen.analysisAux(rules, boxNames);
  results = gen.generateAux(auxinfo);
  return temp;
};

$('textarea').keydown(function(e) {
  e.stopPropagation();
  if (window.textareaDefer) {
    clearTimeout(window.textareaDefer);
    window.textareaDefer = false;
  }
  return window.textareaDefer = setTimeout(parse, 500);
});

$('textarea').val(localStorage.lastSentence || '{A1,A2,R8,R4,R4}{A2,A3,R8,R6,R4}{A3,A4,R4,R8,R4}{A4,A5,-R8,R5,R4}{A5,A6,-R8,R5,R4}');

$('#dice').bind($.clickEventName, function(e) {
  e.stopPropagation();
  lastTemp = '';
  return parse();
});

$('#open').bind($.clickEventName, function(e) {
  e.stopPropagation();
  $('.sentence').toggleClass('open');
  if ($('.sentence').hasClass('open')) {
    return $('#open').text('Collapse');
  } else {
    return $('#open').text('Edit');
  }
});

parse();

window.renderThread = setInterval(render, 50);

$(window).resize(function(e) {
  $('canvas').attr('width', $('.result').width() - 2).attr('height', $.isTouch ? 605 : $('.result').height() - 2);
  return render();
});

setTimeout((function() {
  return $(window).resize();
}), (_ref = $.isTouch) != null ? _ref : {
  100: 10
});
