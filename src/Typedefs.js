"use strict";

const $JSRTS = {
    throw: function (x) {
        throw x;
    },
    Lazy: function (e) {
        this.js_idris_lazy_calc = e;
        this.js_idris_lazy_val = void 0;
    },
    force: function (x) {
        if (x === undefined || x.js_idris_lazy_calc === undefined) {
            return x
        } else {
            if (x.js_idris_lazy_val === undefined) {
                x.js_idris_lazy_val = x.js_idris_lazy_calc()
            }
            return x.js_idris_lazy_val
        }
    },
    prim_strSubstr: function (offset, len, str) {
        return str.substr(Math.max(0, offset), Math.max(0, len))
    }
};
$JSRTS.os = require('os');

$JSRTS.fs = require('fs');

$JSRTS.prim_systemInfo = function (index) {
    switch (index) {
        case 0:
            return "node";
        case 1:
            return $JSRTS.os.platform();
    }
    return "";
};

$JSRTS.prim_writeStr = function (x) { return process.stdout.write(x) };

$JSRTS.prim_readStr = function () {
    var ret = '';
    var b = new Buffer(1024);
    var i = 0;
    while (true) {
        $JSRTS.fs.readSync(0, b, i, 1)
        if (b[i] == 10) {
            ret = b.toString('utf8', 0, i);
            break;
        }
        i++;
        if (i == b.length) {
            var nb = new Buffer(b.length * 2);
            b.copy(nb)
            b = nb;
        }
    }
    return ret;
};

$JSRTS.die = function (message) {
    console.error(message);
    process.exit(-1);
};
$JSRTS.jsbn = (function () {

  // Copyright (c) 2005  Tom Wu
  // All Rights Reserved.
  // See "LICENSE" for details.

  // Basic JavaScript BN library - subset useful for RSA encryption.

  // Bits per digit
  var dbits;

  // JavaScript engine analysis
  var canary = 0xdeadbeefcafe;
  var j_lm = ((canary & 0xffffff) == 0xefcafe);

  // (public) Constructor
  function BigInteger(a, b, c) {
    if (a != null)
      if ("number" == typeof a) this.fromNumber(a, b, c);
      else if (b == null && "string" != typeof a) this.fromString(a, 256);
      else this.fromString(a, b);
  }

  // return new, unset BigInteger
  function nbi() { return new BigInteger(null); }

  // am: Compute w_j += (x*this_i), propagate carries,
  // c is initial carry, returns final carry.
  // c < 3*dvalue, x < 2*dvalue, this_i < dvalue
  // We need to select the fastest one that works in this environment.

  // am1: use a single mult and divide to get the high bits,
  // max digit bits should be 26 because
  // max internal value = 2*dvalue^2-2*dvalue (< 2^53)
  function am1(i, x, w, j, c, n) {
    while (--n >= 0) {
      var v = x * this[i++] + w[j] + c;
      c = Math.floor(v / 0x4000000);
      w[j++] = v & 0x3ffffff;
    }
    return c;
  }
  // am2 avoids a big mult-and-extract completely.
  // Max digit bits should be <= 30 because we do bitwise ops
  // on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
  function am2(i, x, w, j, c, n) {
    var xl = x & 0x7fff, xh = x >> 15;
    while (--n >= 0) {
      var l = this[i] & 0x7fff;
      var h = this[i++] >> 15;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x7fff) << 15) + w[j] + (c & 0x3fffffff);
      c = (l >>> 30) + (m >>> 15) + xh * h + (c >>> 30);
      w[j++] = l & 0x3fffffff;
    }
    return c;
  }
  // Alternately, set max digit bits to 28 since some
  // browsers slow down when dealing with 32-bit numbers.
  function am3(i, x, w, j, c, n) {
    var xl = x & 0x3fff, xh = x >> 14;
    while (--n >= 0) {
      var l = this[i] & 0x3fff;
      var h = this[i++] >> 14;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x3fff) << 14) + w[j] + c;
      c = (l >> 28) + (m >> 14) + xh * h;
      w[j++] = l & 0xfffffff;
    }
    return c;
  }
  var inBrowser = typeof navigator !== "undefined";
  if (inBrowser && j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
    BigInteger.prototype.am = am2;
    dbits = 30;
  }
  else if (inBrowser && j_lm && (navigator.appName != "Netscape")) {
    BigInteger.prototype.am = am1;
    dbits = 26;
  }
  else { // Mozilla/Netscape seems to prefer am3
    BigInteger.prototype.am = am3;
    dbits = 28;
  }

  BigInteger.prototype.DB = dbits;
  BigInteger.prototype.DM = ((1 << dbits) - 1);
  BigInteger.prototype.DV = (1 << dbits);

  var BI_FP = 52;
  BigInteger.prototype.FV = Math.pow(2, BI_FP);
  BigInteger.prototype.F1 = BI_FP - dbits;
  BigInteger.prototype.F2 = 2 * dbits - BI_FP;

  // Digit conversions
  var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
  var BI_RC = new Array();
  var rr, vv;
  rr = "0".charCodeAt(0);
  for (vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
  rr = "a".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
  rr = "A".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

  function int2char(n) { return BI_RM.charAt(n); }
  function intAt(s, i) {
    var c = BI_RC[s.charCodeAt(i)];
    return (c == null) ? -1 : c;
  }

  // (protected) copy this to r
  function bnpCopyTo(r) {
    for (var i = this.t - 1; i >= 0; --i) r[i] = this[i];
    r.t = this.t;
    r.s = this.s;
  }

  // (protected) set from integer value x, -DV <= x < DV
  function bnpFromInt(x) {
    this.t = 1;
    this.s = (x < 0) ? -1 : 0;
    if (x > 0) this[0] = x;
    else if (x < -1) this[0] = x + this.DV;
    else this.t = 0;
  }

  // return bigint initialized to value
  function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

  // (protected) set from string and radix
  function bnpFromString(s, b) {
    var k;
    if (b == 16) k = 4;
    else if (b == 8) k = 3;
    else if (b == 256) k = 8; // byte array
    else if (b == 2) k = 1;
    else if (b == 32) k = 5;
    else if (b == 4) k = 2;
    else { this.fromRadix(s, b); return; }
    this.t = 0;
    this.s = 0;
    var i = s.length, mi = false, sh = 0;
    while (--i >= 0) {
      var x = (k == 8) ? s[i] & 0xff : intAt(s, i);
      if (x < 0) {
        if (s.charAt(i) == "-") mi = true;
        continue;
      }
      mi = false;
      if (sh == 0)
        this[this.t++] = x;
      else if (sh + k > this.DB) {
        this[this.t - 1] |= (x & ((1 << (this.DB - sh)) - 1)) << sh;
        this[this.t++] = (x >> (this.DB - sh));
      }
      else
        this[this.t - 1] |= x << sh;
      sh += k;
      if (sh >= this.DB) sh -= this.DB;
    }
    if (k == 8 && (s[0] & 0x80) != 0) {
      this.s = -1;
      if (sh > 0) this[this.t - 1] |= ((1 << (this.DB - sh)) - 1) << sh;
    }
    this.clamp();
    if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) clamp off excess high words
  function bnpClamp() {
    var c = this.s & this.DM;
    while (this.t > 0 && this[this.t - 1] == c)--this.t;
  }

  // (public) return string representation in given radix
  function bnToString(b) {
    if (this.s < 0) return "-" + this.negate().toString(b);
    var k;
    if (b == 16) k = 4;
    else if (b == 8) k = 3;
    else if (b == 2) k = 1;
    else if (b == 32) k = 5;
    else if (b == 4) k = 2;
    else return this.toRadix(b);
    var km = (1 << k) - 1, d, m = false, r = "", i = this.t;
    var p = this.DB - (i * this.DB) % k;
    if (i-- > 0) {
      if (p < this.DB && (d = this[i] >> p) > 0) { m = true; r = int2char(d); }
      while (i >= 0) {
        if (p < k) {
          d = (this[i] & ((1 << p) - 1)) << (k - p);
          d |= this[--i] >> (p += this.DB - k);
        }
        else {
          d = (this[i] >> (p -= k)) & km;
          if (p <= 0) { p += this.DB; --i; }
        }
        if (d > 0) m = true;
        if (m) r += int2char(d);
      }
    }
    return m ? r : "0";
  }

  // (public) -this
  function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this, r); return r; }

  // (public) |this|
  function bnAbs() { return (this.s < 0) ? this.negate() : this; }

  // (public) return + if this > a, - if this < a, 0 if equal
  function bnCompareTo(a) {
    var r = this.s - a.s;
    if (r != 0) return r;
    var i = this.t;
    r = i - a.t;
    if (r != 0) return (this.s < 0) ? -r : r;
    while (--i >= 0) if ((r = this[i] - a[i]) != 0) return r;
    return 0;
  }

  // returns bit length of the integer x
  function nbits(x) {
    var r = 1, t;
    if ((t = x >>> 16) != 0) { x = t; r += 16; }
    if ((t = x >> 8) != 0) { x = t; r += 8; }
    if ((t = x >> 4) != 0) { x = t; r += 4; }
    if ((t = x >> 2) != 0) { x = t; r += 2; }
    if ((t = x >> 1) != 0) { x = t; r += 1; }
    return r;
  }

  // (public) return the number of bits in "this"
  function bnBitLength() {
    if (this.t <= 0) return 0;
    return this.DB * (this.t - 1) + nbits(this[this.t - 1] ^ (this.s & this.DM));
  }

  // (protected) r = this << n*DB
  function bnpDLShiftTo(n, r) {
    var i;
    for (i = this.t - 1; i >= 0; --i) r[i + n] = this[i];
    for (i = n - 1; i >= 0; --i) r[i] = 0;
    r.t = this.t + n;
    r.s = this.s;
  }

  // (protected) r = this >> n*DB
  function bnpDRShiftTo(n, r) {
    for (var i = n; i < this.t; ++i) r[i - n] = this[i];
    r.t = Math.max(this.t - n, 0);
    r.s = this.s;
  }

  // (protected) r = this << n
  function bnpLShiftTo(n, r) {
    var bs = n % this.DB;
    var cbs = this.DB - bs;
    var bm = (1 << cbs) - 1;
    var ds = Math.floor(n / this.DB), c = (this.s << bs) & this.DM, i;
    for (i = this.t - 1; i >= 0; --i) {
      r[i + ds + 1] = (this[i] >> cbs) | c;
      c = (this[i] & bm) << bs;
    }
    for (i = ds - 1; i >= 0; --i) r[i] = 0;
    r[ds] = c;
    r.t = this.t + ds + 1;
    r.s = this.s;
    r.clamp();
  }

  // (protected) r = this >> n
  function bnpRShiftTo(n, r) {
    r.s = this.s;
    var ds = Math.floor(n / this.DB);
    if (ds >= this.t) { r.t = 0; return; }
    var bs = n % this.DB;
    var cbs = this.DB - bs;
    var bm = (1 << bs) - 1;
    r[0] = this[ds] >> bs;
    for (var i = ds + 1; i < this.t; ++i) {
      r[i - ds - 1] |= (this[i] & bm) << cbs;
      r[i - ds] = this[i] >> bs;
    }
    if (bs > 0) r[this.t - ds - 1] |= (this.s & bm) << cbs;
    r.t = this.t - ds;
    r.clamp();
  }

  // (protected) r = this - a
  function bnpSubTo(a, r) {
    var i = 0, c = 0, m = Math.min(a.t, this.t);
    while (i < m) {
      c += this[i] - a[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }
    if (a.t < this.t) {
      c -= a.s;
      while (i < this.t) {
        c += this[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += this.s;
    }
    else {
      c += this.s;
      while (i < a.t) {
        c -= a[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c -= a.s;
    }
    r.s = (c < 0) ? -1 : 0;
    if (c < -1) r[i++] = this.DV + c;
    else if (c > 0) r[i++] = c;
    r.t = i;
    r.clamp();
  }

  // (protected) r = this * a, r != this,a (HAC 14.12)
  // "this" should be the larger one if appropriate.
  function bnpMultiplyTo(a, r) {
    var x = this.abs(), y = a.abs();
    var i = x.t;
    r.t = i + y.t;
    while (--i >= 0) r[i] = 0;
    for (i = 0; i < y.t; ++i) r[i + x.t] = x.am(0, y[i], r, i, 0, x.t);
    r.s = 0;
    r.clamp();
    if (this.s != a.s) BigInteger.ZERO.subTo(r, r);
  }

  // (protected) r = this^2, r != this (HAC 14.16)
  function bnpSquareTo(r) {
    var x = this.abs();
    var i = r.t = 2 * x.t;
    while (--i >= 0) r[i] = 0;
    for (i = 0; i < x.t - 1; ++i) {
      var c = x.am(i, x[i], r, 2 * i, 0, 1);
      if ((r[i + x.t] += x.am(i + 1, 2 * x[i], r, 2 * i + 1, c, x.t - i - 1)) >= x.DV) {
        r[i + x.t] -= x.DV;
        r[i + x.t + 1] = 1;
      }
    }
    if (r.t > 0) r[r.t - 1] += x.am(i, x[i], r, 2 * i, 0, 1);
    r.s = 0;
    r.clamp();
  }

  // (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
  // r != q, this != m.  q or r may be null.
  function bnpDivRemTo(m, q, r) {
    var pm = m.abs();
    if (pm.t <= 0) return;
    var pt = this.abs();
    if (pt.t < pm.t) {
      if (q != null) q.fromInt(0);
      if (r != null) this.copyTo(r);
      return;
    }
    if (r == null) r = nbi();
    var y = nbi(), ts = this.s, ms = m.s;
    var nsh = this.DB - nbits(pm[pm.t - 1]);   // normalize modulus
    if (nsh > 0) { pm.lShiftTo(nsh, y); pt.lShiftTo(nsh, r); }
    else { pm.copyTo(y); pt.copyTo(r); }
    var ys = y.t;
    var y0 = y[ys - 1];
    if (y0 == 0) return;
    var yt = y0 * (1 << this.F1) + ((ys > 1) ? y[ys - 2] >> this.F2 : 0);
    var d1 = this.FV / yt, d2 = (1 << this.F1) / yt, e = 1 << this.F2;
    var i = r.t, j = i - ys, t = (q == null) ? nbi() : q;
    y.dlShiftTo(j, t);
    if (r.compareTo(t) >= 0) {
      r[r.t++] = 1;
      r.subTo(t, r);
    }
    BigInteger.ONE.dlShiftTo(ys, t);
    t.subTo(y, y);  // "negative" y so we can replace sub with am later
    while (y.t < ys) y[y.t++] = 0;
    while (--j >= 0) {
      // Estimate quotient digit
      var qd = (r[--i] == y0) ? this.DM : Math.floor(r[i] * d1 + (r[i - 1] + e) * d2);
      if ((r[i] += y.am(0, qd, r, j, 0, ys)) < qd) {   // Try it out
        y.dlShiftTo(j, t);
        r.subTo(t, r);
        while (r[i] < --qd) r.subTo(t, r);
      }
    }
    if (q != null) {
      r.drShiftTo(ys, q);
      if (ts != ms) BigInteger.ZERO.subTo(q, q);
    }
    r.t = ys;
    r.clamp();
    if (nsh > 0) r.rShiftTo(nsh, r); // Denormalize remainder
    if (ts < 0) BigInteger.ZERO.subTo(r, r);
  }

  // (public) this mod a
  function bnMod(a) {
    var r = nbi();
    this.abs().divRemTo(a, null, r);
    if (this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r, r);
    return r;
  }

  // Modular reduction using "classic" algorithm
  function Classic(m) { this.m = m; }
  function cConvert(x) {
    if (x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
    else return x;
  }
  function cRevert(x) { return x; }
  function cReduce(x) { x.divRemTo(this.m, null, x); }
  function cMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }
  function cSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  Classic.prototype.convert = cConvert;
  Classic.prototype.revert = cRevert;
  Classic.prototype.reduce = cReduce;
  Classic.prototype.mulTo = cMulTo;
  Classic.prototype.sqrTo = cSqrTo;

  // (protected) return "-1/this % 2^DB"; useful for Mont. reduction
  // justification:
  //         xy == 1 (mod m)
  //         xy =  1+km
  //   xy(2-xy) = (1+km)(1-km)
  // x[y(2-xy)] = 1-k^2m^2
  // x[y(2-xy)] == 1 (mod m^2)
  // if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
  // should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
  // JS multiply "overflows" differently from C/C++, so care is needed here.
  function bnpInvDigit() {
    if (this.t < 1) return 0;
    var x = this[0];
    if ((x & 1) == 0) return 0;
    var y = x & 3;       // y == 1/x mod 2^2
    y = (y * (2 - (x & 0xf) * y)) & 0xf; // y == 1/x mod 2^4
    y = (y * (2 - (x & 0xff) * y)) & 0xff;   // y == 1/x mod 2^8
    y = (y * (2 - (((x & 0xffff) * y) & 0xffff))) & 0xffff;    // y == 1/x mod 2^16
    // last step - calculate inverse mod DV directly;
    // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
    y = (y * (2 - x * y % this.DV)) % this.DV;       // y == 1/x mod 2^dbits
    // we really want the negative inverse, and -DV < y < DV
    return (y > 0) ? this.DV - y : -y;
  }

  // Montgomery reduction
  function Montgomery(m) {
    this.m = m;
    this.mp = m.invDigit();
    this.mpl = this.mp & 0x7fff;
    this.mph = this.mp >> 15;
    this.um = (1 << (m.DB - 15)) - 1;
    this.mt2 = 2 * m.t;
  }

  // xR mod m
  function montConvert(x) {
    var r = nbi();
    x.abs().dlShiftTo(this.m.t, r);
    r.divRemTo(this.m, null, r);
    if (x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r, r);
    return r;
  }

  // x/R mod m
  function montRevert(x) {
    var r = nbi();
    x.copyTo(r);
    this.reduce(r);
    return r;
  }

  // x = x/R mod m (HAC 14.32)
  function montReduce(x) {
    while (x.t <= this.mt2) // pad x so am has enough room later
      x[x.t++] = 0;
    for (var i = 0; i < this.m.t; ++i) {
      // faster way of calculating u0 = x[i]*mp mod DV
      var j = x[i] & 0x7fff;
      var u0 = (j * this.mpl + (((j * this.mph + (x[i] >> 15) * this.mpl) & this.um) << 15)) & x.DM;
      // use am to combine the multiply-shift-add into one call
      j = i + this.m.t;
      x[j] += this.m.am(0, u0, x, i, 0, this.m.t);
      // propagate carry
      while (x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
    }
    x.clamp();
    x.drShiftTo(this.m.t, x);
    if (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = "x^2/R mod m"; x != r
  function montSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  // r = "xy/R mod m"; x,y != r
  function montMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }

  Montgomery.prototype.convert = montConvert;
  Montgomery.prototype.revert = montRevert;
  Montgomery.prototype.reduce = montReduce;
  Montgomery.prototype.mulTo = montMulTo;
  Montgomery.prototype.sqrTo = montSqrTo;

  // (protected) true iff this is even
  function bnpIsEven() { return ((this.t > 0) ? (this[0] & 1) : this.s) == 0; }

  // (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
  function bnpExp(e, z) {
    if (e > 0xffffffff || e < 1) return BigInteger.ONE;
    var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e) - 1;
    g.copyTo(r);
    while (--i >= 0) {
      z.sqrTo(r, r2);
      if ((e & (1 << i)) > 0) z.mulTo(r2, g, r);
      else { var t = r; r = r2; r2 = t; }
    }
    return z.revert(r);
  }

  // (public) this^e % m, 0 <= e < 2^32
  function bnModPowInt(e, m) {
    var z;
    if (e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
    return this.exp(e, z);
  }

  // protected
  BigInteger.prototype.copyTo = bnpCopyTo;
  BigInteger.prototype.fromInt = bnpFromInt;
  BigInteger.prototype.fromString = bnpFromString;
  BigInteger.prototype.clamp = bnpClamp;
  BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
  BigInteger.prototype.drShiftTo = bnpDRShiftTo;
  BigInteger.prototype.lShiftTo = bnpLShiftTo;
  BigInteger.prototype.rShiftTo = bnpRShiftTo;
  BigInteger.prototype.subTo = bnpSubTo;
  BigInteger.prototype.multiplyTo = bnpMultiplyTo;
  BigInteger.prototype.squareTo = bnpSquareTo;
  BigInteger.prototype.divRemTo = bnpDivRemTo;
  BigInteger.prototype.invDigit = bnpInvDigit;
  BigInteger.prototype.isEven = bnpIsEven;
  BigInteger.prototype.exp = bnpExp;

  // public
  BigInteger.prototype.toString = bnToString;
  BigInteger.prototype.negate = bnNegate;
  BigInteger.prototype.abs = bnAbs;
  BigInteger.prototype.compareTo = bnCompareTo;
  BigInteger.prototype.bitLength = bnBitLength;
  BigInteger.prototype.mod = bnMod;
  BigInteger.prototype.modPowInt = bnModPowInt;

  // "constants"
  BigInteger.ZERO = nbv(0);
  BigInteger.ONE = nbv(1);

  // Copyright (c) 2005-2009  Tom Wu
  // All Rights Reserved.
  // See "LICENSE" for details.

  // Extended JavaScript BN functions, required for RSA private ops.

  // Version 1.1: new BigInteger("0", 10) returns "proper" zero
  // Version 1.2: square() API, isProbablePrime fix

  // (public)
  function bnClone() { var r = nbi(); this.copyTo(r); return r; }

  // (public) return value as integer
  function bnIntValue() {
    if (this.s < 0) {
      if (this.t == 1) return this[0] - this.DV;
      else if (this.t == 0) return -1;
    }
    else if (this.t == 1) return this[0];
    else if (this.t == 0) return 0;
    // assumes 16 < DB < 32
    return ((this[1] & ((1 << (32 - this.DB)) - 1)) << this.DB) | this[0];
  }

  // (public) return value as byte
  function bnByteValue() { return (this.t == 0) ? this.s : (this[0] << 24) >> 24; }

  // (public) return value as short (assumes DB>=16)
  function bnShortValue() { return (this.t == 0) ? this.s : (this[0] << 16) >> 16; }

  // (protected) return x s.t. r^x < DV
  function bnpChunkSize(r) { return Math.floor(Math.LN2 * this.DB / Math.log(r)); }

  // (public) 0 if this == 0, 1 if this > 0
  function bnSigNum() {
    if (this.s < 0) return -1;
    else if (this.t <= 0 || (this.t == 1 && this[0] <= 0)) return 0;
    else return 1;
  }

  // (protected) convert to radix string
  function bnpToRadix(b) {
    if (b == null) b = 10;
    if (this.signum() == 0 || b < 2 || b > 36) return "0";
    var cs = this.chunkSize(b);
    var a = Math.pow(b, cs);
    var d = nbv(a), y = nbi(), z = nbi(), r = "";
    this.divRemTo(d, y, z);
    while (y.signum() > 0) {
      r = (a + z.intValue()).toString(b).substr(1) + r;
      y.divRemTo(d, y, z);
    }
    return z.intValue().toString(b) + r;
  }

  // (protected) convert from radix string
  function bnpFromRadix(s, b) {
    this.fromInt(0);
    if (b == null) b = 10;
    var cs = this.chunkSize(b);
    var d = Math.pow(b, cs), mi = false, j = 0, w = 0;
    for (var i = 0; i < s.length; ++i) {
      var x = intAt(s, i);
      if (x < 0) {
        if (s.charAt(i) == "-" && this.signum() == 0) mi = true;
        continue;
      }
      w = b * w + x;
      if (++j >= cs) {
        this.dMultiply(d);
        this.dAddOffset(w, 0);
        j = 0;
        w = 0;
      }
    }
    if (j > 0) {
      this.dMultiply(Math.pow(b, j));
      this.dAddOffset(w, 0);
    }
    if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) alternate constructor
  function bnpFromNumber(a, b, c) {
    if ("number" == typeof b) {
      // new BigInteger(int,int,RNG)
      if (a < 2) this.fromInt(1);
      else {
        this.fromNumber(a, c);
        if (!this.testBit(a - 1))    // force MSB set
          this.bitwiseTo(BigInteger.ONE.shiftLeft(a - 1), op_or, this);
        if (this.isEven()) this.dAddOffset(1, 0); // force odd
        while (!this.isProbablePrime(b)) {
          this.dAddOffset(2, 0);
          if (this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a - 1), this);
        }
      }
    }
    else {
      // new BigInteger(int,RNG)
      var x = new Array(), t = a & 7;
      x.length = (a >> 3) + 1;
      b.nextBytes(x);
      if (t > 0) x[0] &= ((1 << t) - 1); else x[0] = 0;
      this.fromString(x, 256);
    }
  }

  // (public) convert to bigendian byte array
  function bnToByteArray() {
    var i = this.t, r = new Array();
    r[0] = this.s;
    var p = this.DB - (i * this.DB) % 8, d, k = 0;
    if (i-- > 0) {
      if (p < this.DB && (d = this[i] >> p) != (this.s & this.DM) >> p)
        r[k++] = d | (this.s << (this.DB - p));
      while (i >= 0) {
        if (p < 8) {
          d = (this[i] & ((1 << p) - 1)) << (8 - p);
          d |= this[--i] >> (p += this.DB - 8);
        }
        else {
          d = (this[i] >> (p -= 8)) & 0xff;
          if (p <= 0) { p += this.DB; --i; }
        }
        if ((d & 0x80) != 0) d |= -256;
        if (k == 0 && (this.s & 0x80) != (d & 0x80))++k;
        if (k > 0 || d != this.s) r[k++] = d;
      }
    }
    return r;
  }

  function bnEquals(a) { return (this.compareTo(a) == 0); }
  function bnMin(a) { return (this.compareTo(a) < 0) ? this : a; }
  function bnMax(a) { return (this.compareTo(a) > 0) ? this : a; }

  // (protected) r = this op a (bitwise)
  function bnpBitwiseTo(a, op, r) {
    var i, f, m = Math.min(a.t, this.t);
    for (i = 0; i < m; ++i) r[i] = op(this[i], a[i]);
    if (a.t < this.t) {
      f = a.s & this.DM;
      for (i = m; i < this.t; ++i) r[i] = op(this[i], f);
      r.t = this.t;
    }
    else {
      f = this.s & this.DM;
      for (i = m; i < a.t; ++i) r[i] = op(f, a[i]);
      r.t = a.t;
    }
    r.s = op(this.s, a.s);
    r.clamp();
  }

  // (public) this & a
  function op_and(x, y) { return x & y; }
  function bnAnd(a) { var r = nbi(); this.bitwiseTo(a, op_and, r); return r; }

  // (public) this | a
  function op_or(x, y) { return x | y; }
  function bnOr(a) { var r = nbi(); this.bitwiseTo(a, op_or, r); return r; }

  // (public) this ^ a
  function op_xor(x, y) { return x ^ y; }
  function bnXor(a) { var r = nbi(); this.bitwiseTo(a, op_xor, r); return r; }

  // (public) this & ~a
  function op_andnot(x, y) { return x & ~y; }
  function bnAndNot(a) { var r = nbi(); this.bitwiseTo(a, op_andnot, r); return r; }

  // (public) ~this
  function bnNot() {
    var r = nbi();
    for (var i = 0; i < this.t; ++i) r[i] = this.DM & ~this[i];
    r.t = this.t;
    r.s = ~this.s;
    return r;
  }

  // (public) this << n
  function bnShiftLeft(n) {
    var r = nbi();
    if (n < 0) this.rShiftTo(-n, r); else this.lShiftTo(n, r);
    return r;
  }

  // (public) this >> n
  function bnShiftRight(n) {
    var r = nbi();
    if (n < 0) this.lShiftTo(-n, r); else this.rShiftTo(n, r);
    return r;
  }

  // return index of lowest 1-bit in x, x < 2^31
  function lbit(x) {
    if (x == 0) return -1;
    var r = 0;
    if ((x & 0xffff) == 0) { x >>= 16; r += 16; }
    if ((x & 0xff) == 0) { x >>= 8; r += 8; }
    if ((x & 0xf) == 0) { x >>= 4; r += 4; }
    if ((x & 3) == 0) { x >>= 2; r += 2; }
    if ((x & 1) == 0)++r;
    return r;
  }

  // (public) returns index of lowest 1-bit (or -1 if none)
  function bnGetLowestSetBit() {
    for (var i = 0; i < this.t; ++i)
      if (this[i] != 0) return i * this.DB + lbit(this[i]);
    if (this.s < 0) return this.t * this.DB;
    return -1;
  }

  // return number of 1 bits in x
  function cbit(x) {
    var r = 0;
    while (x != 0) { x &= x - 1; ++r; }
    return r;
  }

  // (public) return number of set bits
  function bnBitCount() {
    var r = 0, x = this.s & this.DM;
    for (var i = 0; i < this.t; ++i) r += cbit(this[i] ^ x);
    return r;
  }

  // (public) true iff nth bit is set
  function bnTestBit(n) {
    var j = Math.floor(n / this.DB);
    if (j >= this.t) return (this.s != 0);
    return ((this[j] & (1 << (n % this.DB))) != 0);
  }

  // (protected) this op (1<<n)
  function bnpChangeBit(n, op) {
    var r = BigInteger.ONE.shiftLeft(n);
    this.bitwiseTo(r, op, r);
    return r;
  }

  // (public) this | (1<<n)
  function bnSetBit(n) { return this.changeBit(n, op_or); }

  // (public) this & ~(1<<n)
  function bnClearBit(n) { return this.changeBit(n, op_andnot); }

  // (public) this ^ (1<<n)
  function bnFlipBit(n) { return this.changeBit(n, op_xor); }

  // (protected) r = this + a
  function bnpAddTo(a, r) {
    var i = 0, c = 0, m = Math.min(a.t, this.t);
    while (i < m) {
      c += this[i] + a[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }
    if (a.t < this.t) {
      c += a.s;
      while (i < this.t) {
        c += this[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += this.s;
    }
    else {
      c += this.s;
      while (i < a.t) {
        c += a[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += a.s;
    }
    r.s = (c < 0) ? -1 : 0;
    if (c > 0) r[i++] = c;
    else if (c < -1) r[i++] = this.DV + c;
    r.t = i;
    r.clamp();
  }

  // (public) this + a
  function bnAdd(a) { var r = nbi(); this.addTo(a, r); return r; }

  // (public) this - a
  function bnSubtract(a) { var r = nbi(); this.subTo(a, r); return r; }

  // (public) this * a
  function bnMultiply(a) { var r = nbi(); this.multiplyTo(a, r); return r; }

  // (public) this^2
  function bnSquare() { var r = nbi(); this.squareTo(r); return r; }

  // (public) this / a
  function bnDivide(a) { var r = nbi(); this.divRemTo(a, r, null); return r; }

  // (public) this % a
  function bnRemainder(a) { var r = nbi(); this.divRemTo(a, null, r); return r; }

  // (public) [this/a,this%a]
  function bnDivideAndRemainder(a) {
    var q = nbi(), r = nbi();
    this.divRemTo(a, q, r);
    return new Array(q, r);
  }

  // (protected) this *= n, this >= 0, 1 < n < DV
  function bnpDMultiply(n) {
    this[this.t] = this.am(0, n - 1, this, 0, 0, this.t);
    ++this.t;
    this.clamp();
  }

  // (protected) this += n << w words, this >= 0
  function bnpDAddOffset(n, w) {
    if (n == 0) return;
    while (this.t <= w) this[this.t++] = 0;
    this[w] += n;
    while (this[w] >= this.DV) {
      this[w] -= this.DV;
      if (++w >= this.t) this[this.t++] = 0;
      ++this[w];
    }
  }

  // A "null" reducer
  function NullExp() { }
  function nNop(x) { return x; }
  function nMulTo(x, y, r) { x.multiplyTo(y, r); }
  function nSqrTo(x, r) { x.squareTo(r); }

  NullExp.prototype.convert = nNop;
  NullExp.prototype.revert = nNop;
  NullExp.prototype.mulTo = nMulTo;
  NullExp.prototype.sqrTo = nSqrTo;

  // (public) this^e
  function bnPow(e) { return this.exp(e, new NullExp()); }

  // (protected) r = lower n words of "this * a", a.t <= n
  // "this" should be the larger one if appropriate.
  function bnpMultiplyLowerTo(a, n, r) {
    var i = Math.min(this.t + a.t, n);
    r.s = 0; // assumes a,this >= 0
    r.t = i;
    while (i > 0) r[--i] = 0;
    var j;
    for (j = r.t - this.t; i < j; ++i) r[i + this.t] = this.am(0, a[i], r, i, 0, this.t);
    for (j = Math.min(a.t, n); i < j; ++i) this.am(0, a[i], r, i, 0, n - i);
    r.clamp();
  }

  // (protected) r = "this * a" without lower n words, n > 0
  // "this" should be the larger one if appropriate.
  function bnpMultiplyUpperTo(a, n, r) {
    --n;
    var i = r.t = this.t + a.t - n;
    r.s = 0; // assumes a,this >= 0
    while (--i >= 0) r[i] = 0;
    for (i = Math.max(n - this.t, 0); i < a.t; ++i)
      r[this.t + i - n] = this.am(n - i, a[i], r, 0, 0, this.t + i - n);
    r.clamp();
    r.drShiftTo(1, r);
  }

  // Barrett modular reduction
  function Barrett(m) {
    // setup Barrett
    this.r2 = nbi();
    this.q3 = nbi();
    BigInteger.ONE.dlShiftTo(2 * m.t, this.r2);
    this.mu = this.r2.divide(m);
    this.m = m;
  }

  function barrettConvert(x) {
    if (x.s < 0 || x.t > 2 * this.m.t) return x.mod(this.m);
    else if (x.compareTo(this.m) < 0) return x;
    else { var r = nbi(); x.copyTo(r); this.reduce(r); return r; }
  }

  function barrettRevert(x) { return x; }

  // x = x mod m (HAC 14.42)
  function barrettReduce(x) {
    x.drShiftTo(this.m.t - 1, this.r2);
    if (x.t > this.m.t + 1) { x.t = this.m.t + 1; x.clamp(); }
    this.mu.multiplyUpperTo(this.r2, this.m.t + 1, this.q3);
    this.m.multiplyLowerTo(this.q3, this.m.t + 1, this.r2);
    while (x.compareTo(this.r2) < 0) x.dAddOffset(1, this.m.t + 1);
    x.subTo(this.r2, x);
    while (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = x^2 mod m; x != r
  function barrettSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  // r = x*y mod m; x,y != r
  function barrettMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }

  Barrett.prototype.convert = barrettConvert;
  Barrett.prototype.revert = barrettRevert;
  Barrett.prototype.reduce = barrettReduce;
  Barrett.prototype.mulTo = barrettMulTo;
  Barrett.prototype.sqrTo = barrettSqrTo;

  // (public) this^e % m (HAC 14.85)
  function bnModPow(e, m) {
    var i = e.bitLength(), k, r = nbv(1), z;
    if (i <= 0) return r;
    else if (i < 18) k = 1;
    else if (i < 48) k = 3;
    else if (i < 144) k = 4;
    else if (i < 768) k = 5;
    else k = 6;
    if (i < 8)
      z = new Classic(m);
    else if (m.isEven())
      z = new Barrett(m);
    else
      z = new Montgomery(m);

    // precomputation
    var g = new Array(), n = 3, k1 = k - 1, km = (1 << k) - 1;
    g[1] = z.convert(this);
    if (k > 1) {
      var g2 = nbi();
      z.sqrTo(g[1], g2);
      while (n <= km) {
        g[n] = nbi();
        z.mulTo(g2, g[n - 2], g[n]);
        n += 2;
      }
    }

    var j = e.t - 1, w, is1 = true, r2 = nbi(), t;
    i = nbits(e[j]) - 1;
    while (j >= 0) {
      if (i >= k1) w = (e[j] >> (i - k1)) & km;
      else {
        w = (e[j] & ((1 << (i + 1)) - 1)) << (k1 - i);
        if (j > 0) w |= e[j - 1] >> (this.DB + i - k1);
      }

      n = k;
      while ((w & 1) == 0) { w >>= 1; --n; }
      if ((i -= n) < 0) { i += this.DB; --j; }
      if (is1) {    // ret == 1, don't bother squaring or multiplying it
        g[w].copyTo(r);
        is1 = false;
      }
      else {
        while (n > 1) { z.sqrTo(r, r2); z.sqrTo(r2, r); n -= 2; }
        if (n > 0) z.sqrTo(r, r2); else { t = r; r = r2; r2 = t; }
        z.mulTo(r2, g[w], r);
      }

      while (j >= 0 && (e[j] & (1 << i)) == 0) {
        z.sqrTo(r, r2); t = r; r = r2; r2 = t;
        if (--i < 0) { i = this.DB - 1; --j; }
      }
    }
    return z.revert(r);
  }

  // (public) gcd(this,a) (HAC 14.54)
  function bnGCD(a) {
    var x = (this.s < 0) ? this.negate() : this.clone();
    var y = (a.s < 0) ? a.negate() : a.clone();
    if (x.compareTo(y) < 0) { var t = x; x = y; y = t; }
    var i = x.getLowestSetBit(), g = y.getLowestSetBit();
    if (g < 0) return x;
    if (i < g) g = i;
    if (g > 0) {
      x.rShiftTo(g, x);
      y.rShiftTo(g, y);
    }
    while (x.signum() > 0) {
      if ((i = x.getLowestSetBit()) > 0) x.rShiftTo(i, x);
      if ((i = y.getLowestSetBit()) > 0) y.rShiftTo(i, y);
      if (x.compareTo(y) >= 0) {
        x.subTo(y, x);
        x.rShiftTo(1, x);
      }
      else {
        y.subTo(x, y);
        y.rShiftTo(1, y);
      }
    }
    if (g > 0) y.lShiftTo(g, y);
    return y;
  }

  // (protected) this % n, n < 2^26
  function bnpModInt(n) {
    if (n <= 0) return 0;
    var d = this.DV % n, r = (this.s < 0) ? n - 1 : 0;
    if (this.t > 0)
      if (d == 0) r = this[0] % n;
      else for (var i = this.t - 1; i >= 0; --i) r = (d * r + this[i]) % n;
    return r;
  }

  // (public) 1/this % m (HAC 14.61)
  function bnModInverse(m) {
    var ac = m.isEven();
    if ((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
    var u = m.clone(), v = this.clone();
    var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
    while (u.signum() != 0) {
      while (u.isEven()) {
        u.rShiftTo(1, u);
        if (ac) {
          if (!a.isEven() || !b.isEven()) { a.addTo(this, a); b.subTo(m, b); }
          a.rShiftTo(1, a);
        }
        else if (!b.isEven()) b.subTo(m, b);
        b.rShiftTo(1, b);
      }
      while (v.isEven()) {
        v.rShiftTo(1, v);
        if (ac) {
          if (!c.isEven() || !d.isEven()) { c.addTo(this, c); d.subTo(m, d); }
          c.rShiftTo(1, c);
        }
        else if (!d.isEven()) d.subTo(m, d);
        d.rShiftTo(1, d);
      }
      if (u.compareTo(v) >= 0) {
        u.subTo(v, u);
        if (ac) a.subTo(c, a);
        b.subTo(d, b);
      }
      else {
        v.subTo(u, v);
        if (ac) c.subTo(a, c);
        d.subTo(b, d);
      }
    }
    if (v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
    if (d.compareTo(m) >= 0) return d.subtract(m);
    if (d.signum() < 0) d.addTo(m, d); else return d;
    if (d.signum() < 0) return d.add(m); else return d;
  }

  var lowprimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997];
  var lplim = (1 << 26) / lowprimes[lowprimes.length - 1];

  // (public) test primality with certainty >= 1-.5^t
  function bnIsProbablePrime(t) {
    var i, x = this.abs();
    if (x.t == 1 && x[0] <= lowprimes[lowprimes.length - 1]) {
      for (i = 0; i < lowprimes.length; ++i)
        if (x[0] == lowprimes[i]) return true;
      return false;
    }
    if (x.isEven()) return false;
    i = 1;
    while (i < lowprimes.length) {
      var m = lowprimes[i], j = i + 1;
      while (j < lowprimes.length && m < lplim) m *= lowprimes[j++];
      m = x.modInt(m);
      while (i < j) if (m % lowprimes[i++] == 0) return false;
    }
    return x.millerRabin(t);
  }

  // (protected) true if probably prime (HAC 4.24, Miller-Rabin)
  function bnpMillerRabin(t) {
    var n1 = this.subtract(BigInteger.ONE);
    var k = n1.getLowestSetBit();
    if (k <= 0) return false;
    var r = n1.shiftRight(k);
    t = (t + 1) >> 1;
    if (t > lowprimes.length) t = lowprimes.length;
    var a = nbi();
    for (var i = 0; i < t; ++i) {
      //Pick bases at random, instead of starting at 2
      a.fromInt(lowprimes[Math.floor(Math.random() * lowprimes.length)]);
      var y = a.modPow(r, this);
      if (y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
        var j = 1;
        while (j++ < k && y.compareTo(n1) != 0) {
          y = y.modPowInt(2, this);
          if (y.compareTo(BigInteger.ONE) == 0) return false;
        }
        if (y.compareTo(n1) != 0) return false;
      }
    }
    return true;
  }

  // protected
  BigInteger.prototype.chunkSize = bnpChunkSize;
  BigInteger.prototype.toRadix = bnpToRadix;
  BigInteger.prototype.fromRadix = bnpFromRadix;
  BigInteger.prototype.fromNumber = bnpFromNumber;
  BigInteger.prototype.bitwiseTo = bnpBitwiseTo;
  BigInteger.prototype.changeBit = bnpChangeBit;
  BigInteger.prototype.addTo = bnpAddTo;
  BigInteger.prototype.dMultiply = bnpDMultiply;
  BigInteger.prototype.dAddOffset = bnpDAddOffset;
  BigInteger.prototype.multiplyLowerTo = bnpMultiplyLowerTo;
  BigInteger.prototype.multiplyUpperTo = bnpMultiplyUpperTo;
  BigInteger.prototype.modInt = bnpModInt;
  BigInteger.prototype.millerRabin = bnpMillerRabin;

  // public
  BigInteger.prototype.clone = bnClone;
  BigInteger.prototype.intValue = bnIntValue;
  BigInteger.prototype.byteValue = bnByteValue;
  BigInteger.prototype.shortValue = bnShortValue;
  BigInteger.prototype.signum = bnSigNum;
  BigInteger.prototype.toByteArray = bnToByteArray;
  BigInteger.prototype.equals = bnEquals;
  BigInteger.prototype.min = bnMin;
  BigInteger.prototype.max = bnMax;
  BigInteger.prototype.and = bnAnd;
  BigInteger.prototype.or = bnOr;
  BigInteger.prototype.xor = bnXor;
  BigInteger.prototype.andNot = bnAndNot;
  BigInteger.prototype.not = bnNot;
  BigInteger.prototype.shiftLeft = bnShiftLeft;
  BigInteger.prototype.shiftRight = bnShiftRight;
  BigInteger.prototype.getLowestSetBit = bnGetLowestSetBit;
  BigInteger.prototype.bitCount = bnBitCount;
  BigInteger.prototype.testBit = bnTestBit;
  BigInteger.prototype.setBit = bnSetBit;
  BigInteger.prototype.clearBit = bnClearBit;
  BigInteger.prototype.flipBit = bnFlipBit;
  BigInteger.prototype.add = bnAdd;
  BigInteger.prototype.subtract = bnSubtract;
  BigInteger.prototype.multiply = bnMultiply;
  BigInteger.prototype.divide = bnDivide;
  BigInteger.prototype.remainder = bnRemainder;
  BigInteger.prototype.divideAndRemainder = bnDivideAndRemainder;
  BigInteger.prototype.modPow = bnModPow;
  BigInteger.prototype.modInverse = bnModInverse;
  BigInteger.prototype.pow = bnPow;
  BigInteger.prototype.gcd = bnGCD;
  BigInteger.prototype.isProbablePrime = bnIsProbablePrime;

  // JSBN-specific extension
  BigInteger.prototype.square = bnSquare;

  // Expose the Barrett function
  BigInteger.prototype.Barrett = Barrett

  // BigInteger interfaces not implemented in jsbn:

  // BigInteger(int signum, byte[] magnitude)
  // double doubleValue()
  // float floatValue()
  // int hashCode()
  // long longValue()
  // static BigInteger valueOf(long val)

  // Random number generator - requires a PRNG backend, e.g. prng4.js

  // For best results, put code like
  // <body onClick='rng_seed_time();' onKeyPress='rng_seed_time();'>
  // in your main HTML document.

  var rng_state;
  var rng_pool;
  var rng_pptr;

  // Mix in a 32-bit integer into the pool
  function rng_seed_int(x) {
    rng_pool[rng_pptr++] ^= x & 255;
    rng_pool[rng_pptr++] ^= (x >> 8) & 255;
    rng_pool[rng_pptr++] ^= (x >> 16) & 255;
    rng_pool[rng_pptr++] ^= (x >> 24) & 255;
    if (rng_pptr >= rng_psize) rng_pptr -= rng_psize;
  }

  // Mix in the current time (w/milliseconds) into the pool
  function rng_seed_time() {
    rng_seed_int(new Date().getTime());
  }

  // Initialize the pool with junk if needed.
  if (rng_pool == null) {
    rng_pool = new Array();
    rng_pptr = 0;
    var t;
    if (typeof window !== "undefined" && window.crypto) {
      if (window.crypto.getRandomValues) {
        // Use webcrypto if available
        var ua = new Uint8Array(32);
        window.crypto.getRandomValues(ua);
        for (t = 0; t < 32; ++t)
          rng_pool[rng_pptr++] = ua[t];
      }
      else if (navigator.appName == "Netscape" && navigator.appVersion < "5") {
        // Extract entropy (256 bits) from NS4 RNG if available
        var z = window.crypto.random(32);
        for (t = 0; t < z.length; ++t)
          rng_pool[rng_pptr++] = z.charCodeAt(t) & 255;
      }
    }
    while (rng_pptr < rng_psize) {  // extract some randomness from Math.random()
      t = Math.floor(65536 * Math.random());
      rng_pool[rng_pptr++] = t >>> 8;
      rng_pool[rng_pptr++] = t & 255;
    }
    rng_pptr = 0;
    rng_seed_time();
    //rng_seed_int(window.screenX);
    //rng_seed_int(window.screenY);
  }

  function rng_get_byte() {
    if (rng_state == null) {
      rng_seed_time();
      rng_state = prng_newstate();
      rng_state.init(rng_pool);
      for (rng_pptr = 0; rng_pptr < rng_pool.length; ++rng_pptr)
        rng_pool[rng_pptr] = 0;
      rng_pptr = 0;
      //rng_pool = null;
    }
    // TODO: allow reseeding after first request
    return rng_state.next();
  }

  function rng_get_bytes(ba) {
    var i;
    for (i = 0; i < ba.length; ++i) ba[i] = rng_get_byte();
  }

  function SecureRandom() { }

  SecureRandom.prototype.nextBytes = rng_get_bytes;

  // prng4.js - uses Arcfour as a PRNG

  function Arcfour() {
    this.i = 0;
    this.j = 0;
    this.S = new Array();
  }

  // Initialize arcfour context from key, an array of ints, each from [0..255]
  function ARC4init(key) {
    var i, j, t;
    for (i = 0; i < 256; ++i)
      this.S[i] = i;
    j = 0;
    for (i = 0; i < 256; ++i) {
      j = (j + this.S[i] + key[i % key.length]) & 255;
      t = this.S[i];
      this.S[i] = this.S[j];
      this.S[j] = t;
    }
    this.i = 0;
    this.j = 0;
  }

  function ARC4next() {
    var t;
    this.i = (this.i + 1) & 255;
    this.j = (this.j + this.S[this.i]) & 255;
    t = this.S[this.i];
    this.S[this.i] = this.S[this.j];
    this.S[this.j] = t;
    return this.S[(t + this.S[this.i]) & 255];
  }

  Arcfour.prototype.init = ARC4init;
  Arcfour.prototype.next = ARC4next;

  // Plug in your RNG constructor here
  function prng_newstate() {
    return new Arcfour();
  }

  // Pool size must be a multiple of 4 and greater than 32.
  // An array of bytes the size of the pool will be passed to init()
  var rng_psize = 256;

  return {
    BigInteger: BigInteger,
    SecureRandom: SecureRandom
  };

}).call(this);



function $partial_0_2$prim_95__95_strCons(){
    return (function(x1){
        return (function(x2){
            return prim_95__95_strCons(x1, x2);
        });
    });
}

function $partial_0_1$prim_95__95_toStrBigInt(){
    return (function(x1){
        return prim_95__95_toStrBigInt(x1);
    });
}

function $partial_5_10$TParsec__Combinators__alt(x1, x2, x3, x4, x5){
    return (function(x6){
        return (function(x7){
            return (function(x8){
                return (function(x9){
                    return (function(x10){
                        return TParsec__Combinators__alt(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10);
                    });
                });
            });
        });
    });
}

function $partial_7_10$TParsec__Combinators__alt(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return TParsec__Combinators__alt(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10);
            });
        });
    });
}

function $partial_5_6$TParsec__Success__and(x1, x2, x3, x4, x5){
    return (function(x6){
        return TParsec__Success__and(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_8_11$TParsec__Combinators__andbind(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return (function(x10){
            return (function(x11){
                return TParsec__Combinators__andbind(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
            });
        });
    });
}

function $partial_10_11$TParsec__Combinators__andbind(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10){
    return (function(x11){
        return TParsec__Combinators__andbind(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
    });
}

function $partial_8_11$TParsec__Combinators__andbindm(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return (function(x10){
            return (function(x11){
                return TParsec__Combinators__andbindm(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
            });
        });
    });
}

function $partial_9_12$TParsec__Combinators__andoptbind(x1, x2, x3, x4, x5, x6, x7, x8, x9){
    return (function(x10){
        return (function(x11){
            return (function(x12){
                return TParsec__Combinators__andoptbind(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12);
            });
        });
    });
}

function $partial_5_8$TParsec__Combinators__anyTok(x1, x2, x3, x4, x5){
    return (function(x6){
        return (function(x7){
            return (function(x8){
                return TParsec__Combinators__anyTok(x1, x2, x3, x4, x5, x6, x7, x8);
            });
        });
    });
}

function $partial_7_8$TParsec__Combinators__exact(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return TParsec__Combinators__exact(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_9_12$TParsec__Combinators__guardM(x1, x2, x3, x4, x5, x6, x7, x8, x9){
    return (function(x10){
        return (function(x11){
            return (function(x12){
                return TParsec__Combinators__guardM(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12);
            });
        });
    });
}

function $partial_0_1$Backend__Haskell__guardParen(){
    return (function(x1){
        return Backend__Haskell__guardParen(x1);
    });
}

function $partial_2_3$Backend__Haskell__makeDefs(x1, x2){
    return (function(x3){
        return Backend__Haskell__makeDefs(x1, x2, x3);
    });
}

function $partial_2_3$Backend__Haskell__makeType(x1, x2){
    return (function(x3){
        return Backend__Haskell__makeType(x1, x2, x3);
    });
}

function $partial_8_11$TParsec__Combinators__mand(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return (function(x10){
            return (function(x11){
                return TParsec__Combinators__mand(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
            });
        });
    });
}

function $partial_7_11$TParsec__Combinators__map(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return (function(x11){
                    return TParsec__Combinators__map(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
                });
            });
        });
    });
}

function $partial_8_11$TParsec__Combinators__map(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return (function(x10){
            return (function(x11){
                return TParsec__Combinators__map(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
            });
        });
    });
}

function $partial_0_1$Backend__Haskell__renderDef(){
    return (function(x1){
        return Backend__Haskell__renderDef(x1);
    });
}

function $partial_0_1$Backend__Haskell__renderType(){
    return (function(x1){
        return Backend__Haskell__renderType(x1);
    });
}

function $partial_1_2$Main__setResult(x1){
    return (function(x2){
        return Main__setResult(x1, x2);
    });
}

function $partial_0_1$Parse__tdefRec(){
    return (function(x1){
        return Parse__tdefRec(x1);
    });
}

function $partial_1_2$TParsec__Combinators__Chars___123_alphas_95_0_125_(x1){
    return (function(x2){
        return TParsec__Combinators__Chars___123_alphas_95_0_125_(x1, x2);
    });
}

function $partial_1_4$TParsec__Combinators___123_alts_95_1_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return TParsec__Combinators___123_alts_95_1_125_(x1, x2, x3, x4);
            });
        });
    });
}

function $partial_2_3$TParsec__Combinators___123_andbind_95_2_125_(x1, x2){
    return (function(x3){
        return TParsec__Combinators___123_andbind_95_2_125_(x1, x2, x3);
    });
}

function $partial_2_3$TParsec__Combinators___123_andbindm_95_3_125_(x1, x2){
    return (function(x3){
        return TParsec__Combinators___123_andbindm_95_3_125_(x1, x2, x3);
    });
}

function $partial_2_3$TParsec__Combinators___123_andbindm_95_4_125_(x1, x2){
    return (function(x3){
        return TParsec__Combinators___123_andbindm_95_4_125_(x1, x2, x3);
    });
}

function $partial_1_2$TParsec__Combinators___123_andoptbind_95_5_125_(x1){
    return (function(x2){
        return TParsec__Combinators___123_andoptbind_95_5_125_(x1, x2);
    });
}

function $partial_3_4$TParsec__Combinators___123_andoptbind_95_6_125_(x1, x2, x3){
    return (function(x4){
        return TParsec__Combinators___123_andoptbind_95_6_125_(x1, x2, x3, x4);
    });
}

function $partial_0_1$TParsec__Combinators___123_ands_95_7_125_(){
    return (function(x1){
        return TParsec__Combinators___123_ands_95_7_125_(x1);
    });
}

function $partial_1_6$TParsec__Combinators___123_ands_95_8_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return (function(x6){
                        return TParsec__Combinators___123_ands_95_8_125_(x1, x2, x3, x4, x5, x6);
                    });
                });
            });
        });
    });
}

function $partial_1_3$TParsec__Combinators___123_ands_95_9_125_(x1){
    return (function(x2){
        return (function(x3){
            return TParsec__Combinators___123_ands_95_9_125_(x1, x2, x3);
        });
    });
}

function $partial_0_1$TParsec__Combinators___123_ands_95_10_125_(){
    return (function(x1){
        return TParsec__Combinators___123_ands_95_10_125_(x1);
    });
}

function $partial_5_6$TParsec__Combinators___123_anyOf_95_12_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return TParsec__Combinators___123_anyOf_95_12_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Combinators___123_anyTok_95_13_125_(x1, x2);
        });
    });
}

function $partial_2_4$TParsec__Combinators___123_anyTok_95_14_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return TParsec__Combinators___123_anyTok_95_14_125_(x1, x2, x3, x4);
        });
    });
}

function $partial_0_1$Typedefs___123_args_95_15_125_(){
    return (function(x1){
        return Typedefs___123_args_95_15_125_(x1);
    });
}

function $partial_0_3$TermParse___123_chooseParser_95_16_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return TermParse___123_chooseParser_95_16_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$TermParse___123_chooseParser_95_19_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return TermParse___123_chooseParser_95_19_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_1$TermParse___123_chooseParser_95_20_125_(){
    return (function(x1){
        return TermParse___123_chooseParser_95_20_125_(x1);
    });
}

function $partial_0_3$TermParse___123_chooseParser_95_21_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return TermParse___123_chooseParser_95_21_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$TermParse___123_chooseParser_95_23_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return TermParse___123_chooseParser_95_23_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_2$TermParse___123_chooseParser_95_25_125_(){
    return (function(x1){
        return (function(x2){
            return TermParse___123_chooseParser_95_25_125_(x1, x2);
        });
    });
}

function $partial_0_2$TermParse___123_chooseParser_95_32_125_(){
    return (function(x1){
        return (function(x2){
            return TermParse___123_chooseParser_95_32_125_(x1, x2);
        });
    });
}

function $partial_0_4$TermParse___123_chooseParser_95_37_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return TermParse___123_chooseParser_95_37_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_1$TermParse___123_chooseParser_95_43_125_(){
    return (function(x1){
        return TermParse___123_chooseParser_95_43_125_(x1);
    });
}

function $partial_0_3$TermParse___123_chooseParser_95_48_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return TermParse___123_chooseParser_95_48_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$TermParse___123_chooseParser_95_65_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return TermParse___123_chooseParser_95_65_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_1$TermParse___123_chooseParser_95_66_125_(){
    return (function(x1){
        return TermParse___123_chooseParser_95_66_125_(x1);
    });
}

function $partial_0_2$TermParse___123_chooseParser_95_67_125_(){
    return (function(x1){
        return (function(x2){
            return TermParse___123_chooseParser_95_67_125_(x1, x2);
        });
    });
}

function $partial_0_2$TermParse___123_chooseParser_95_68_125_(){
    return (function(x1){
        return (function(x2){
            return TermParse___123_chooseParser_95_68_125_(x1, x2);
        });
    });
}

function $partial_0_1$TermParse___123_chooseParser_95_71_125_(){
    return (function(x1){
        return TermParse___123_chooseParser_95_71_125_(x1);
    });
}

function $partial_3_7$TermParse___123_chooseParser_95_221_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return TermParse___123_chooseParser_95_221_125_(x1, x2, x3, x4, x5, x6, x7);
                });
            });
        });
    });
}

function $partial_3_7$TermParse___123_chooseParser_95_222_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return TermParse___123_chooseParser_95_222_125_(x1, x2, x3, x4, x5, x6, x7);
                });
            });
        });
    });
}

function $partial_5_10$TermParse___123_chooseParser_95_433_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return (function(x7){
            return (function(x8){
                return (function(x9){
                    return (function(x10){
                        return TermParse___123_chooseParser_95_433_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10);
                    });
                });
            });
        });
    });
}

function $partial_6_10$TermParse___123_chooseParser_95_434_125_(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return (function(x8){
            return (function(x9){
                return (function(x10){
                    return TermParse___123_chooseParser_95_434_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10);
                });
            });
        });
    });
}

function $partial_6_10$TermParse___123_chooseParser_95_435_125_(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return (function(x8){
            return (function(x9){
                return (function(x10){
                    return TermParse___123_chooseParser_95_435_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10);
                });
            });
        });
    });
}

function $partial_3_8$TermParse___123_chooseParser_95_646_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return (function(x8){
                        return TermParse___123_chooseParser_95_646_125_(x1, x2, x3, x4, x5, x6, x7, x8);
                    });
                });
            });
        });
    });
}

function $partial_4_8$TermParse___123_chooseParser_95_647_125_(x1, x2, x3, x4){
    return (function(x5){
        return (function(x6){
            return (function(x7){
                return (function(x8){
                    return TermParse___123_chooseParser_95_647_125_(x1, x2, x3, x4, x5, x6, x7, x8);
                });
            });
        });
    });
}

function $partial_4_8$TermParse___123_chooseParser_95_648_125_(x1, x2, x3, x4){
    return (function(x5){
        return (function(x6){
            return (function(x7){
                return (function(x8){
                    return TermParse___123_chooseParser_95_648_125_(x1, x2, x3, x4, x5, x6, x7, x8);
                });
            });
        });
    });
}

function $partial_3_7$TermParse___123_chooseParser_95_821_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return TermParse___123_chooseParser_95_821_125_(x1, x2, x3, x4, x5, x6, x7);
                });
            });
        });
    });
}

function $partial_5_9$TermParse___123_chooseParser_95_927_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return (function(x7){
            return (function(x8){
                return (function(x9){
                    return TermParse___123_chooseParser_95_927_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9);
                });
            });
        });
    });
}

function $partial_6_10$TermParse___123_chooseParser_95_928_125_(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return (function(x8){
            return (function(x9){
                return (function(x10){
                    return TermParse___123_chooseParser_95_928_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10);
                });
            });
        });
    });
}

function $partial_4_8$TermParse___123_chooseParser_95_1208_125_(x1, x2, x3, x4){
    return (function(x5){
        return (function(x6){
            return (function(x7){
                return (function(x8){
                    return TermParse___123_chooseParser_95_1208_125_(x1, x2, x3, x4, x5, x6, x7, x8);
                });
            });
        });
    });
}

function $partial_0_1$Data__NEList___123_consopt_95_1209_125_(){
    return (function(x1){
        return Data__NEList___123_consopt_95_1209_125_(x1);
    });
}

function $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_1210_125_(x1){
    return (function(x2){
        return TParsec__Combinators__Numbers___123_decimalDigit_95_1210_125_(x1, x2);
    });
}

function $partial_6_7$TParsec__Combinators__Numbers___123_decimalDigit_95_1211_125_(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return TParsec__Combinators__Numbers___123_decimalDigit_95_1211_125_(x1, x2, x3, x4, x5, x6, x7);
    });
}

function $partial_0_2$TParsec__Combinators__Numbers___123_decimalNat_95_1212_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Combinators__Numbers___123_decimalNat_95_1212_125_(x1, x2);
        });
    });
}

function $partial_0_1$TParsec__Combinators__Numbers___123_decimalNat_95_1213_125_(){
    return (function(x1){
        return TParsec__Combinators__Numbers___123_decimalNat_95_1213_125_(x1);
    });
}

function $partial_0_2$TermParse___123_deserialize_95_1214_125_(){
    return (function(x1){
        return (function(x2){
            return TermParse___123_deserialize_95_1214_125_(x1, x2);
        });
    });
}

function $partial_0_2$TermParse___123_deserialize_95_1215_125_(){
    return (function(x1){
        return (function(x2){
            return TermParse___123_deserialize_95_1215_125_(x1, x2);
        });
    });
}

function $partial_0_1$TermParse___123_deserialize_95_1216_125_(){
    return (function(x1){
        return TermParse___123_deserialize_95_1216_125_(x1);
    });
}

function $partial_0_1$TermParse___123_deserialize_95_1217_125_(){
    return (function(x1){
        return TermParse___123_deserialize_95_1217_125_(x1);
    });
}

function $partial_2_3$TermParse___123_deserialize_95_1218_125_(x1, x2){
    return (function(x3){
        return TermParse___123_deserialize_95_1218_125_(x1, x2, x3);
    });
}

function $partial_1_2$Main___123_deserialize0_95_1219_125_(x1){
    return (function(x2){
        return Main___123_deserialize0_95_1219_125_(x1, x2);
    });
}

function $partial_0_1$Main___123_deserialize0_95_1220_125_(){
    return (function(x1){
        return Main___123_deserialize0_95_1220_125_(x1);
    });
}

function $partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1223_125_(x1){
    return (function(x2){
        return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1223_125_(x1, x2);
    });
}

function $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1225_125_(){
    return (function(x1){
        return (function(x2){
            return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1225_125_(x1, x2);
        });
    });
}

function $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1226_125_(){
    return (function(x1){
        return (function(x2){
            return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1226_125_(x1, x2);
        });
    });
}

function $partial_5_6$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1232_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1232_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1233_125_(x1, x2, x3, x4){
    return (function(x5){
        return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1233_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_5_6$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1243_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1243_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1244_125_(x1, x2, x3, x4){
    return (function(x5){
        return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1244_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_2_3$TParsec__Combinators___123_exact_95_1246_125_(x1, x2){
    return (function(x3){
        return TParsec__Combinators___123_exact_95_1246_125_(x1, x2, x3);
    });
}

function $partial_3_4$Data__Vect___123_foldrImpl_95_1249_125_(x1, x2, x3){
    return (function(x4){
        return Data__Vect___123_foldrImpl_95_1249_125_(x1, x2, x3, x4);
    });
}

function $partial_0_2$Backend___123_generate_95_1250_125_(){
    return (function(x1){
        return (function(x2){
            return Backend___123_generate_95_1250_125_(x1, x2);
        });
    });
}

function $partial_1_2$TParsec__Success___123_getTok_95_1251_125_(x1){
    return (function(x2){
        return TParsec__Success___123_getTok_95_1251_125_(x1, x2);
    });
}

function $partial_0_2$Backend___123_getUsedIndices_95_1252_125_(){
    return (function(x1){
        return (function(x2){
            return Backend___123_getUsedIndices_95_1252_125_(x1, x2);
        });
    });
}

function $partial_0_2$Backend___123_getUsedIndices_95_1253_125_(){
    return (function(x1){
        return (function(x2){
            return Backend___123_getUsedIndices_95_1253_125_(x1, x2);
        });
    });
}

function $partial_0_2$Backend___123_getUsedIndices_95_1255_125_(){
    return (function(x1){
        return (function(x2){
            return Backend___123_getUsedIndices_95_1255_125_(x1, x2);
        });
    });
}

function $partial_1_2$Backend___123_getUsedVars_95_1259_125_(x1){
    return (function(x2){
        return Backend___123_getUsedVars_95_1259_125_(x1, x2);
    });
}

function $partial_2_4$TParsec__Combinators___123_guardM_95_1260_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return TParsec__Combinators___123_guardM_95_1260_125_(x1, x2, x3, x4);
        });
    });
}

function $partial_3_4$TParsec__Combinators___123_guardM_95_1261_125_(x1, x2, x3){
    return (function(x4){
        return TParsec__Combinators___123_guardM_95_1261_125_(x1, x2, x3, x4);
    });
}

function $partial_3_4$TParsec__Combinators___123_guardM_95_1262_125_(x1, x2, x3){
    return (function(x4){
        return TParsec__Combinators___123_guardM_95_1262_125_(x1, x2, x3, x4);
    });
}

function $partial_0_1$TParsec__Combinators___123_land_95_1264_125_(){
    return (function(x1){
        return TParsec__Combinators___123_land_95_1264_125_(x1);
    });
}

function $partial_0_3$Main___123_main_95_1268_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Main___123_main_95_1268_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_1$Main___123_main_95_1269_125_(){
    return (function(x1){
        return Main___123_main_95_1269_125_(x1);
    });
}

function $partial_0_1$Main___123_main_95_1270_125_(){
    return (function(x1){
        return Main___123_main_95_1270_125_(x1);
    });
}

function $partial_0_1$Main___123_main_95_1271_125_(){
    return (function(x1){
        return Main___123_main_95_1271_125_(x1);
    });
}

function $partial_0_1$Main___123_main_95_1272_125_(){
    return (function(x1){
        return Main___123_main_95_1272_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_1273_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_1273_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_1279_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_1279_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_1280_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_1280_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_1281_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_1281_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_1282_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_1282_125_(x1);
    });
}

function $partial_1_2$Backend__Haskell___123_makeDefs_95_1283_125_(x1){
    return (function(x2){
        return Backend__Haskell___123_makeDefs_95_1283_125_(x1, x2);
    });
}

function $partial_0_2$Backend__Haskell___123_makeDefs_95_1289_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__Haskell___123_makeDefs_95_1289_125_(x1, x2);
        });
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_1290_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_1290_125_(x1);
    });
}

function $partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Backend__Haskell___123_makeDefs_95_1292_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Backend__Haskell___123_makeDefs_95_1293_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Backend__Haskell___123_makeDefs_95_1298_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_1_2$Backend__Haskell___123_makeDefs_95_1299_125_(x1){
    return (function(x2){
        return Backend__Haskell___123_makeDefs_95_1299_125_(x1, x2);
    });
}

function $partial_0_2$Backend__Haskell___123_makeDefs_95_1300_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__Haskell___123_makeDefs_95_1300_125_(x1, x2);
        });
    });
}

function $partial_2_3$Backend__Haskell___123_makeDefs_95_1306_125_(x1, x2){
    return (function(x3){
        return Backend__Haskell___123_makeDefs_95_1306_125_(x1, x2, x3);
    });
}

function $partial_3_5$Backend__Haskell___123_makeDefs_95_1307_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return Backend__Haskell___123_makeDefs_95_1307_125_(x1, x2, x3, x4, x5);
        });
    });
}

function $partial_4_5$Backend__Haskell___123_makeDefs_95_1308_125_(x1, x2, x3, x4){
    return (function(x5){
        return Backend__Haskell___123_makeDefs_95_1308_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_0_2$Backend__Haskell___123_makeDefs_95_1310_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__Haskell___123_makeDefs_95_1310_125_(x1, x2);
        });
    });
}

function $partial_4_5$Backend__Haskell___123_makeDefs_95_1311_125_(x1, x2, x3, x4){
    return (function(x5){
        return Backend__Haskell___123_makeDefs_95_1311_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_1326_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_1326_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_1327_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_1327_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_1328_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_1328_125_(x1);
    });
}

function $partial_5_7$Backend__Haskell___123_makeDefs_95_1329_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return (function(x7){
            return Backend__Haskell___123_makeDefs_95_1329_125_(x1, x2, x3, x4, x5, x6, x7);
        });
    });
}

function $partial_5_6$Backend__Haskell___123_makeDefs_95_1330_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return Backend__Haskell___123_makeDefs_95_1330_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$Backend__Haskell___123_makeDefs_95_1333_125_(x1, x2, x3, x4){
    return (function(x5){
        return Backend__Haskell___123_makeDefs_95_1333_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_0_1$Backend__Haskell___123_makeDefs_95_1337_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeDefs_95_1337_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeType_95_1359_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeType_95_1359_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeType_95_1360_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeType_95_1360_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeType_95_1361_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeType_95_1361_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeType_95_1362_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeType_95_1362_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeType_95_1365_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeType_95_1365_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_makeType_95_1366_125_(){
    return (function(x1){
        return Backend__Haskell___123_makeType_95_1366_125_(x1);
    });
}

function $partial_0_2$Backend__Haskell___123_makeType_95_1367_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__Haskell___123_makeType_95_1367_125_(x1, x2);
        });
    });
}

function $partial_1_2$TParsec__Combinators___123_mand_95_1369_125_(x1){
    return (function(x2){
        return TParsec__Combinators___123_mand_95_1369_125_(x1, x2);
    });
}

function $partial_5_6$TParsec__Combinators___123_mand_95_1370_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return TParsec__Combinators___123_mand_95_1370_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_1_2$TParsec__Combinators___123_map_95_1371_125_(x1){
    return (function(x2){
        return TParsec__Combinators___123_map_95_1371_125_(x1, x2);
    });
}

function $partial_3_7$TermParse___123_muParser_95_1525_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return TermParse___123_muParser_95_1525_125_(x1, x2, x3, x4, x5, x6, x7);
                });
            });
        });
    });
}

function $partial_3_7$TermParse___123_muParser_95_1526_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return TermParse___123_muParser_95_1526_125_(x1, x2, x3, x4, x5, x6, x7);
                });
            });
        });
    });
}

function $partial_0_1$TParsec__Combinators___123_nelist_95_1527_125_(){
    return (function(x1){
        return TParsec__Combinators___123_nelist_95_1527_125_(x1);
    });
}

function $partial_1_3$TParsec__Combinators___123_nelist_95_1528_125_(x1){
    return (function(x2){
        return (function(x3){
            return TParsec__Combinators___123_nelist_95_1528_125_(x1, x2, x3);
        });
    });
}

function $partial_2_5$TParsec__Combinators___123_nelist_95_1529_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return TParsec__Combinators___123_nelist_95_1529_125_(x1, x2, x3, x4, x5);
            });
        });
    });
}

function $partial_2_5$TParsec__Combinators___123_nelist_95_1530_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return TParsec__Combinators___123_nelist_95_1530_125_(x1, x2, x3, x4, x5);
            });
        });
    });
}

function $partial_0_1$TParsec__Combinators___123_optand_95_1531_125_(){
    return (function(x1){
        return TParsec__Combinators___123_optand_95_1531_125_(x1);
    });
}

function $partial_0_1$TParsec__Combinators___123_optand_95_1533_125_(){
    return (function(x1){
        return TParsec__Combinators___123_optand_95_1533_125_(x1);
    });
}

function $partial_7_11$TParsec__Combinators__Chars___123_parens_95_1534_125_(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return (function(x11){
                    return TParsec__Combinators__Chars___123_parens_95_1534_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
                });
            });
        });
    });
}

function $partial_0_4$TParsec__Running___123_parseMaybe_95_1535_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return TParsec__Running___123_parseMaybe_95_1535_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_2$TParsec__Running___123_parseMaybe_95_1536_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Running___123_parseMaybe_95_1536_125_(x1, x2);
        });
    });
}

function $partial_0_4$TParsec__Running___123_parseMaybe_95_1537_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return TParsec__Running___123_parseMaybe_95_1537_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_1$TParsec__Running___123_parseMaybe_95_1539_125_(){
    return (function(x1){
        return TParsec__Running___123_parseMaybe_95_1539_125_(x1);
    });
}

function $partial_0_2$Parse___123_parseTDef_95_1540_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_parseTDef_95_1540_125_(x1, x2);
        });
    });
}

function $partial_0_2$Parse___123_parseTDef_95_1541_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_parseTDef_95_1541_125_(x1, x2);
        });
    });
}

function $partial_0_1$Parse___123_parseTDef_95_1542_125_(){
    return (function(x1){
        return Parse___123_parseTDef_95_1542_125_(x1);
    });
}

function $partial_0_1$TParsec__Combinators___123_rand_95_1544_125_(){
    return (function(x1){
        return TParsec__Combinators___123_rand_95_1544_125_(x1);
    });
}

function $partial_0_1$TParsec__Combinators___123_randbindm_95_1546_125_(){
    return (function(x1){
        return TParsec__Combinators___123_randbindm_95_1546_125_(x1);
    });
}

function $partial_0_2$Backend__Haskell___123_renderApp_95_1547_125_(){
    return (function(x1){
        return (function(x2){
            return Backend__Haskell___123_renderApp_95_1547_125_(x1, x2);
        });
    });
}

function $partial_0_1$Backend__Haskell___123_renderDef_95_1550_125_(){
    return (function(x1){
        return Backend__Haskell___123_renderDef_95_1550_125_(x1);
    });
}

function $partial_0_1$Backend__Haskell___123_renderDef_95_1554_125_(){
    return (function(x1){
        return Backend__Haskell___123_renderDef_95_1554_125_(x1);
    });
}

function $partial_7_8$TParsec__Combinators__Chars___123_string_95_1559_125_(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return TParsec__Combinators__Chars___123_string_95_1559_125_(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_0_1$TParsec__Combinators___123_sum_95_1560_125_(){
    return (function(x1){
        return TParsec__Combinators___123_sum_95_1560_125_(x1);
    });
}

function $partial_0_1$TParsec__Combinators___123_sum_95_1561_125_(){
    return (function(x1){
        return TParsec__Combinators___123_sum_95_1561_125_(x1);
    });
}

function $partial_0_3$Parse___123_tdef_95_1562_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Parse___123_tdef_95_1562_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$Parse___123_tdef_95_1565_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Parse___123_tdef_95_1565_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_4$Parse___123_tdef_95_1578_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Parse___123_tdef_95_1578_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_2$Parse___123_tdef_95_1579_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_tdef_95_1579_125_(x1, x2);
        });
    });
}

function $partial_0_4$Parse___123_tdef_95_1593_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Parse___123_tdef_95_1593_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_1608_125_(){
    return (function(x1){
        return Parse___123_tdef_95_1608_125_(x1);
    });
}

function $partial_0_3$Parse___123_tdef_95_1622_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Parse___123_tdef_95_1622_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_4$Parse___123_tdef_95_1667_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Parse___123_tdef_95_1667_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_1836_125_(){
    return (function(x1){
        return Parse___123_tdef_95_1836_125_(x1);
    });
}

function $partial_0_1$Parse___123_tdef_95_2009_125_(){
    return (function(x1){
        return Parse___123_tdef_95_2009_125_(x1);
    });
}

function $partial_0_1$Parse___123_tdef_95_2122_125_(){
    return (function(x1){
        return Parse___123_tdef_95_2122_125_(x1);
    });
}

function $partial_0_3$Parse___123_tdef_95_2232_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Parse___123_tdef_95_2232_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_3$Parse___123_tdef_95_2233_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Parse___123_tdef_95_2233_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_2237_125_(){
    return (function(x1){
        return Parse___123_tdef_95_2237_125_(x1);
    });
}

function $partial_1_5$Parse___123_tdef_95_2828_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Parse___123_tdef_95_2828_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_5$Parse___123_tdef_95_2829_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Parse___123_tdef_95_2829_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_2980_125_(){
    return (function(x1){
        return Parse___123_tdef_95_2980_125_(x1);
    });
}

function $partial_1_2$Parse___123_tdef_95_2981_125_(x1){
    return (function(x2){
        return Parse___123_tdef_95_2981_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_tdef_95_2982_125_(){
    return (function(x1){
        return Parse___123_tdef_95_2982_125_(x1);
    });
}

function $partial_3_8$Parse___123_tdef_95_4206_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return (function(x8){
                        return Parse___123_tdef_95_4206_125_(x1, x2, x3, x4, x5, x6, x7, x8);
                    });
                });
            });
        });
    });
}

function $partial_3_7$Parse___123_tdef_95_4207_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return Parse___123_tdef_95_4207_125_(x1, x2, x3, x4, x5, x6, x7);
                });
            });
        });
    });
}

function $partial_1_4$Parse___123_tdef_95_4208_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return Parse___123_tdef_95_4208_125_(x1, x2, x3, x4);
            });
        });
    });
}

function $partial_2_6$Parse___123_tdef_95_4209_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return (function(x6){
                    return Parse___123_tdef_95_4209_125_(x1, x2, x3, x4, x5, x6);
                });
            });
        });
    });
}

function $partial_2_6$Parse___123_tdef_95_4210_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return (function(x6){
                    return Parse___123_tdef_95_4210_125_(x1, x2, x3, x4, x5, x6);
                });
            });
        });
    });
}

function $partial_2_4$Parse___123_tdef_95_4245_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return Parse___123_tdef_95_4245_125_(x1, x2, x3, x4);
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_4259_125_(){
    return (function(x1){
        return Parse___123_tdef_95_4259_125_(x1);
    });
}

function $partial_1_4$Parse___123_tdef_95_5050_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return Parse___123_tdef_95_5050_125_(x1, x2, x3, x4);
            });
        });
    });
}

function $partial_2_6$Parse___123_tdef_95_5051_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return (function(x6){
                    return Parse___123_tdef_95_5051_125_(x1, x2, x3, x4, x5, x6);
                });
            });
        });
    });
}

function $partial_2_6$Parse___123_tdef_95_5052_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return (function(x5){
                return (function(x6){
                    return Parse___123_tdef_95_5052_125_(x1, x2, x3, x4, x5, x6);
                });
            });
        });
    });
}

function $partial_3_5$Parse___123_tdef_95_5087_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return Parse___123_tdef_95_5087_125_(x1, x2, x3, x4, x5);
        });
    });
}

function $partial_0_1$Parse___123_tdef_95_5101_125_(){
    return (function(x1){
        return Parse___123_tdef_95_5101_125_(x1);
    });
}

function $partial_0_2$Parse___123_tdef_95_5102_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_tdef_95_5102_125_(x1, x2);
        });
    });
}

function $partial_0_1$Parse___123_tdefRec_95_5106_125_(){
    return (function(x1){
        return Parse___123_tdefRec_95_5106_125_(x1);
    });
}

function $partial_0_2$Parse___123_tdefRec_95_5213_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_tdefRec_95_5213_125_(x1, x2);
        });
    });
}

function $partial_0_1$Text__PrettyPrint__WL__Core___123_toString_95_5214_125_(){
    return (function(x1){
        return Text__PrettyPrint__WL__Core___123_toString_95_5214_125_(x1);
    });
}

function $partial_1_2$Backend__Utils___123_unindex_95_5215_125_(x1){
    return (function(x2){
        return Backend__Utils___123_unindex_95_5215_125_(x1, x2);
    });
}

function $partial_7_11$TParsec__Combinators__Chars___123_withSpaces_95_5216_125_(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return (function(x9){
            return (function(x10){
                return (function(x11){
                    return TParsec__Combinators__Chars___123_withSpaces_95_5216_125_(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11);
                });
            });
        });
    });
}

function $partial_3_4$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0_95_lam_95_5970_125_(x1, x2, x3){
    return (function(x4){
        return Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0_95_lam_95_5970_125_(x1, x2, x3, x4);
    });
}

function $partial_2_3$Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5971_125_(x1, x2){
    return (function(x3){
        return Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5971_125_(x1, x2, x3);
    });
}

function $partial_2_3$Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5972_125_(x1, x2){
    return (function(x3){
        return Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5972_125_(x1, x2, x3);
    });
}

function $partial_2_3$Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5973_125_(x1, x2){
    return (function(x3){
        return Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5973_125_(x1, x2, x3);
    });
}

function $partial_2_3$Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5974_125_(x1, x2){
    return (function(x3){
        return Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5974_125_(x1, x2, x3);
    });
}

function $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5975_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5975_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_3$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5976_125_(x1){
    return (function(x2){
        return (function(x3){
            return Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5976_125_(x1, x2, x3);
        });
    });
}

function $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5977_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5977_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5978_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5978_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_2$Prelude__Functor___123_TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0_95_lam_95_5979_125_(x1){
    return (function(x2){
        return Prelude__Functor___123_TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0_95_lam_95_5979_125_(x1, x2);
    });
}

function $partial_1_2$Prelude__Functor___123_Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0_95_lam_95_5980_125_(x1){
    return (function(x2){
        return Prelude__Functor___123_Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0_95_lam_95_5980_125_(x1, x2);
    });
}

function $partial_1_5$Prelude__Functor___123_TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0_95_lam_95_5981_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Prelude__Functor___123_TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0_95_lam_95_5981_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_2_3$Prelude__Monad___123_TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0_95_lam_95_5982_125_(x1, x2){
    return (function(x3){
        return Prelude__Monad___123_TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0_95_lam_95_5982_125_(x1, x2, x3);
    });
}

function $partial_1_2$Prelude__Monad___123_Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0_95_lam_95_5983_125_(x1){
    return (function(x2){
        return Prelude__Monad___123_Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0_95_lam_95_5983_125_(x1, x2);
    });
}

function $partial_0_2$TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0_95_lam_95_5988_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0_95_lam_95_5988_125_(x1, x2);
        });
    });
}

function $partial_0_2$TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5990_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5990_125_(x1, x2);
        });
    });
}

function $partial_0_2$TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5991_125_(){
    return (function(x1){
        return (function(x2){
            return TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5991_125_(x1, x2);
        });
    });
}

function $partial_0_1$TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0_95_lam_95_5992_125_(){
    return (function(x1){
        return TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0_95_lam_95_5992_125_(x1);
    });
}

function $partial_0_1$Control__Monad__Trans___123_TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0_95_lam_95_5993_125_(){
    return (function(x1){
        return Control__Monad__Trans___123_TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0_95_lam_95_5993_125_(x1);
    });
}

function $partial_2_3$Control__Monad__Trans___123_Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0_95_lam_95_5994_125_(x1, x2){
    return (function(x3){
        return Control__Monad__Trans___123_Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0_95_lam_95_5994_125_(x1, x2, x3);
    });
}

function $partial_1_5$Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5995_125_(x1){
    return (function(x2){
        return (function(x3){
            return (function(x4){
                return (function(x5){
                    return Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5995_125_(x1, x2, x3, x4, x5);
                });
            });
        });
    });
}

function $partial_1_3$Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5996_125_(x1){
    return (function(x2){
        return (function(x3){
            return Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5996_125_(x1, x2, x3);
        });
    });
}

function $partial_0_2$Prelude__Traversable___123_Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0_95_lam_95_6000_125_(){
    return (function(x1){
        return (function(x2){
            return Prelude__Traversable___123_Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0_95_lam_95_6000_125_(x1, x2);
        });
    });
}

function $partial_8_9$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0(x1, x2, x3, x4, x5, x6, x7, x8){
    return (function(x9){
        return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0(x1, x2, x3, x4, x5, x6, x7, x8, x9);
    });
}

function $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33_empty_58_0(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33_empty_58_0(x1, x2, x3, x4, x5, x6, x7);
    });
}

function $partial_7_8$Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0(x1, x2, x3, x4, x5, x6, x7);
    });
}

function $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_5_6$Control__Monad__Trans__Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0(x1, x2, x3, x4, x5){
    return (function(x6){
        return Control__Monad__Trans__Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_0_1$$_5217_Induction__Nat__fixBox_58_go_58_0_95_lam(){
    return (function(x1){
        return $_5217_Induction__Nat__fixBox_58_go_58_0_95_lam(x1);
    });
}

function $partial_2_4$$_5218_Induction__Nat__fixBox_58_go_58_0_95_lam(x1, x2){
    return (function(x3){
        return (function(x4){
            return $_5218_Induction__Nat__fixBox_58_go_58_0_95_lam(x1, x2, x3, x4);
        });
    });
}

function $partial_3_4$$_5219_Induction__Nat__fixBox_58_go_58_0_95_lam(x1, x2, x3){
    return (function(x4){
        return $_5219_Induction__Nat__fixBox_58_go_58_0_95_lam(x1, x2, x3, x4);
    });
}

function $partial_6_7$$_5220_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return $_5220_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam(x1, x2, x3, x4, x5, x6, x7);
    });
}

function $partial_1_2$$_5225_Parse__tdef_58_nary_58_0_95_lam(x1){
    return (function(x2){
        return $_5225_Parse__tdef_58_nary_58_0_95_lam(x1, x2);
    });
}

function $partial_1_2$$_5226_Parse__tdef_58_nary_58_0_95_lam(x1){
    return (function(x2){
        return $_5226_Parse__tdef_58_nary_58_0_95_lam(x1, x2);
    });
}

function $partial_3_8$$_5967_Parse__tdef_58_nary_58_0_95_lam(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return (function(x8){
                        return $_5967_Parse__tdef_58_nary_58_0_95_lam(x1, x2, x3, x4, x5, x6, x7, x8);
                    });
                });
            });
        });
    });
}

function $partial_1_3$$_5968_Parse__tdef_58_nary_58_0_95_lam(x1){
    return (function(x2){
        return (function(x3){
            return $_5968_Parse__tdef_58_nary_58_0_95_lam(x1, x2, x3);
        });
    });
}

function $partial_3_7$$_5969_Parse__tdef_58_nary_58_0_95_lam(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return (function(x6){
                return (function(x7){
                    return $_5969_Parse__tdef_58_nary_58_0_95_lam(x1, x2, x3, x4, x5, x6, x7);
                });
            });
        });
    });
}

function $partial_3_4$Backend__Haskell__renderDef_58_renderConstructor_58_1(x1, x2, x3){
    return (function(x4){
        return Backend__Haskell__renderDef_58_renderConstructor_58_1(x1, x2, x3, x4);
    });
}

const $HC_0_0$MkUnit = ({type: 0});
const $HC_0_0$Refl = ({type: 0});
const $HC_0_0$TheWorld = ({type: 0});
function $HC_2_1$Prelude__List___58__58_($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_1$TermParse___58__58_($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_1$Data__Vect___58__58_($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_1$Backend__Haskell__ADT($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_1$Data__SortedMap__Branch2($1, $2, $3){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_5_2$Data__SortedMap__Branch3($1, $2, $3, $4, $5){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
    this.$5 = $5;
}

function $HC_2_4$Text__PrettyPrint__WL__Core__Cat($1, $2){
    this.type = 4;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_1$Text__PrettyPrint__WL__Core__Chara($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_2_1$Text__PrettyPrint__WL__Core__PrettyDoc__Chara($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_7$Text__PrettyPrint__WL__Core__Column($1){
    this.type = 7;
    this.$1 = $1;
}

const $HC_0_0$Text__PrettyPrint__WL__Core__Empty = ({type: 0});
const $HC_0_0$Text__PrettyPrint__WL__Core__PrettyDoc__Empty = ({type: 0});
function $HC_1_0$Data__SortedMap__Empty($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_1_1$Data__Fin__FS($1){
    this.type = 1;
    this.$1 = $1;
}

const $HC_0_0$Data__Fin__FZ = ({type: 0});
function $HC_1_0$TParsec__Result__HardFail($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_3_4$Backend__Haskell__HsParam($1, $2, $3){
    this.type = 4;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_1_2$Backend__Haskell__HsTuple($1){
    this.type = 2;
    this.$1 = $1;
}

const $HC_0_1$Backend__Haskell__HsUnit = ({type: 1});
function $HC_1_3$Backend__Haskell__HsVar($1){
    this.type = 3;
    this.$1 = $1;
}

const $HC_0_0$Backend__Haskell__HsVoid = ({type: 0});
const $HC_0_0$Typedefs__Inn = ({type: 0});
function $HC_1_1$Prelude__Maybe__Just($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_1_1$Prelude__Nat__LTESucc($1){
    this.type = 1;
    this.$1 = $1;
}

const $HC_0_0$Prelude__Nat__LTEZero = ({type: 0});
function $HC_2_0$Data__SortedMap__Leaf($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_0$Prelude__Either__Left($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_1_3$Text__PrettyPrint__WL__Core__Line($1){
    this.type = 3;
    this.$1 = $1;
}

function $HC_2_3$Text__PrettyPrint__WL__Core__PrettyDoc__Line($1, $2){
    this.type = 3;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_1$Data__SortedMap__M($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Builtins__MkDPair($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_0$Backend__MkDecl($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_0$Data__NEList__MkNEList($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Builtins__MkPair($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_0$TParsec__Types__MkPosition = ({type: 0});
function $HC_4_0$TParsec__Success__MkSuccess($1, $2, $3, $4){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
}

function $HC_2_5$Text__PrettyPrint__WL__Core__Nest($1, $2){
    this.type = 5;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($1){
    this.type = 8;
    this.$1 = $1;
}

const $HC_0_0$Prelude__List__Nil = ({type: 0});
const $HC_0_0$TermParse__Nil = ({type: 0});
const $HC_0_0$Data__Vect__Nil = ({type: 0});
const $HC_0_1$Prelude__Basics__No = ({type: 1});
const $HC_0_0$Prelude__Maybe__Nothing = ({type: 0});
const $HC_0_0$Prelude__Show__Open = ({type: 0});
function $HC_1_1$Prelude__Either__Right($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_1_1$TParsec__Result__SoftFail($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_2_1$Prelude__Strings__StrCons($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_0$Prelude__Strings__StrNil = ({type: 0});
function $HC_2_0$Backend__Haskell__Synonym($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_0$Typedefs__T0 = ({type: 0});
const $HC_0_1$Typedefs__T1 = ({type: 1});
function $HC_2_5$Typedefs__TMu($1, $2){
    this.type = 5;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_6$Typedefs__TName($1, $2){
    this.type = 6;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_3$Typedefs__TProd($1){
    this.type = 3;
    this.$1 = $1;
}

function $HC_1_2$Typedefs__TSum($1){
    this.type = 2;
    this.$1 = $1;
}

function $HC_1_4$Typedefs__TVar($1){
    this.type = 4;
    this.$1 = $1;
}

function $HC_2_2$Text__PrettyPrint__WL__Core__Text($1, $2){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_2$Text__PrettyPrint__WL__Core__PrettyDoc__Text($1, $2, $3){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_6$Text__PrettyPrint__WL__Core__Union($1, $2){
    this.type = 6;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_4_1$Parse__VMConsLess($1, $2, $3, $4){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
}

function $HC_4_2$Parse__VMConsMore($1, $2, $3, $4){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
}

function $HC_1_0$Parse__VMEnd($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_1_2$TParsec__Result__Value($1){
    this.type = 2;
    this.$1 = $1;
}

function $HC_1_0$Prelude__Basics__Yes($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_3_0$Prelude__Applicative__Alternative_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_3_0$Prelude__Applicative__Applicative_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_3_0$Backend__Backend_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_0$Prelude__Monad__Monad_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_0$Prelude__Interfaces__Ord_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

// prim__strCons

function prim_95__95_strCons($_0_arg, $_1_arg){
    return (($_0_arg)+($_1_arg));
}

// prim__toStrBigInt

function prim_95__95_toStrBigInt($_0_arg){
    return (($_0_arg).toString());
}

// Prelude.List.++

function Prelude__List___43__43_($_0_arg, $_1_arg, $_2_arg){
    
    if(($_1_arg.type === 1)) {
        return new $HC_2_1$Prelude__List___58__58_($_1_arg.$1, Prelude__List___43__43_(null, $_1_arg.$2, $_2_arg));
    } else {
        return $_2_arg;
    }
}

// Data.Inspect.MkSizedList

function Data__Inspect__MkSizedList($_0_arg, $_1_arg){
    return $_1_arg;
}

// TParsec.Combinators.Chars.alpha

function TParsec__Combinators__Chars__alpha($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_7_10$TParsec__Combinators__alt(null, null, null, $_2_arg, null, TParsec__Combinators__Chars__lowerAlpha(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, null), TParsec__Combinators__Chars__upperAlpha(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, null));
}

// TParsec.Combinators.Chars.alphas

function TParsec__Combinators__Chars__alphas($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    var $cg$1 = null;
    const $cg$3 = $_3_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_1_2$TParsec__Combinators__Chars___123_alphas_95_0_125_($_5_arg), null, TParsec__Combinators__nelist(null, null, null, $_2_arg, $_3_arg, $_8_arg)(TParsec__Combinators__Chars__alpha(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_6_arg, $_7_arg, null)));
}

// TParsec.Combinators.alt

function TParsec__Combinators__alt($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_m1, $_8_mlen, $_9_ts){
    
    return $_3_arg.$3(null)($_5_arg($_7_m1)($_8_mlen)($_9_ts))($_6_arg($_7_m1)($_8_mlen)($_9_ts));
}

// TParsec.Combinators.alts

function TParsec__Combinators__alts($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_5_10$TParsec__Combinators__alt(null, null, null, $_3_arg, null), $partial_1_4$TParsec__Combinators___123_alts_95_1_125_($_3_arg), $_5_arg);
}

// TParsec.Success.and

function TParsec__Success__and($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    var $cg$2 = null;
    $cg$2 = $_4_arg.$1;
    return new $HC_4_0$TParsec__Success__MkSuccess(new $HC_2_0$Builtins__MkPair($cg$2, $_5_arg.$1), $_5_arg.$2, Prelude__Nat__lteTransitive(null, null, null, $_5_arg.$3, null), $_5_arg.$4);
}

// TParsec.Combinators.andbind

function TParsec__Combinators__andbind($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_m1, $_9_mlen, $_10_ts){
    
    return $_4_arg.$2(null)(null)($_6_arg($_8_m1)($_9_mlen)($_10_ts))($partial_2_3$TParsec__Combinators___123_andbind_95_2_125_($_4_arg, $_7_arg));
}

// TParsec.Combinators.andbindm

function TParsec__Combinators__andbindm($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_m1, $_9_mlen, $_10_ts){
    
    return $_4_arg.$2(null)(null)($_6_arg($_8_m1)($_9_mlen)($_10_ts))($partial_2_3$TParsec__Combinators___123_andbindm_95_4_125_($_4_arg, $_7_arg));
}

// TParsec.Combinators.andoptbind

function TParsec__Combinators__andoptbind($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_m1, $_10_mlen, $_11_ts){
    
    return $_4_arg.$2(null)(null)($_7_arg($_9_m1)($_10_mlen)($_11_ts))($partial_3_4$TParsec__Combinators___123_andoptbind_95_6_125_($_5_arg, $_4_arg, $_8_arg));
}

// TParsec.Combinators.ands

function TParsec__Combinators__ands($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    var $cg$2 = null;
    const $cg$4 = $_3_arg.$1;
    $cg$2 = $cg$4.$1;
    var $cg$5 = null;
    const $cg$7 = $_3_arg.$1;
    $cg$5 = $cg$7.$1;
    return Data__NEList__foldr1_58_go_58_0(null, $partial_1_3$TParsec__Combinators___123_ands_95_9_125_($_3_arg), null, null, $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$2, $partial_0_1$TParsec__Combinators___123_ands_95_10_125_(), null, $_5_arg.$1), Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_7_11$TParsec__Combinators__map(null, null, null, null, $cg$5, $partial_0_1$TParsec__Combinators___123_ands_95_10_125_(), null), $_5_arg.$2));
}

// TParsec.Combinators.anyOf

function TParsec__Combinators__anyOf($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return TParsec__Combinators__alts(null, null, null, $_2_arg, null, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_5_6$TParsec__Combinators___123_anyOf_95_12_125_($_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg), $_6_arg));
}

// TParsec.Combinators.anyTok

function TParsec__Combinators__anyTok($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_m1, $_6_arg, $_7_ts){
    var $cg$1 = null;
    $cg$1 = $_2_arg.$2(null);
    return Prelude__Foldable__Prelude__Maybe___64_Prelude__Foldable__Foldable_36_Maybe_58__33_foldr_58_0(null, null, $partial_2_4$TParsec__Combinators___123_anyTok_95_14_125_($_2_arg, $_1_arg), $cg$1, TParsec__Success__getTok(null, null, $_3_arg, $_5_m1, $_7_ts));
}

// Typedefs.args

function Typedefs__args($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        const $cg$3 = $_2_arg.$1;
        const $cg$5 = $_2_arg.$2;
        if(($cg$5.type === 1)) {
            const $cg$7 = $cg$5.$1;
            return new $HC_1_2$Typedefs__TSum(new $HC_2_1$Data__Vect___58__58_($cg$3.$2, new $HC_2_1$Data__Vect___58__58_($cg$7.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Typedefs___123_args_95_15_125_(), $cg$5.$2))));
        } else {
            return $cg$3.$2;
        }
    } else {
        return $HC_0_0$Typedefs__T0;
    }
}

// TParsec.Combinators.Chars.char

function TParsec__Combinators__Chars__char($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_in){
    return $partial_7_8$TParsec__Combinators__exact(null, $_1_arg, $_2_arg, $_3_arg, $_6_arg, $_5_arg, $_4_arg($_7_in));
}

// Text.PrettyPrint.WL.Core.char

function Text__PrettyPrint__WL__Core__char($_0_arg){
    
    if(($_0_arg === "\n")) {
        return new $HC_1_3$Text__PrettyPrint__WL__Core__Line(false);
    } else {
        return new $HC_1_1$Text__PrettyPrint__WL__Core__Chara($_0_arg);
    }
}

// TermParse.chooseParser

function TermParse__chooseParser($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    for(;;) {
        
        if(($_1_arg.type === 0)) {
            return $partial_0_3$TermParse___123_chooseParser_95_21_125_();
        } else if(($_1_arg.type === 1)) {
            return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_1$TermParse___123_chooseParser_95_20_125_(), null, TParsec__Combinators__Chars__string(null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "()", null, $_3_arg));
        } else if(($_1_arg.type === 5)) {
            return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_1$TermParse___123_chooseParser_95_71_125_(), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_3_arg, $partial_3_7$TermParse___123_chooseParser_95_222_125_($_3_arg, $_1_arg.$2, $_4_arg)));
        } else if(($_1_arg.type === 6)) {
            $_0_arg = null;
            $_1_arg = $_1_arg.$2;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
        } else if(($_1_arg.type === 3)) {
            const $cg$18 = $_1_arg.$1;
            const $cg$20 = $cg$18.$2;
            const $cg$22 = $cg$20.$2;
            if(($cg$22.type === 1)) {
                return TParsec__Combinators__Chars__parens(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_3_arg, $partial_6_10$TermParse___123_chooseParser_95_435_125_($_3_arg, $cg$18.$1, $_4_arg, $cg$20.$1, $cg$22.$1, $cg$22.$2));
            } else {
                return TParsec__Combinators__Chars__parens(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_3_arg, $partial_4_8$TermParse___123_chooseParser_95_648_125_($_3_arg, $cg$18.$1, $_4_arg, $cg$20.$1));
            }
        } else if(($_1_arg.type === 2)) {
            const $cg$12 = $_1_arg.$1;
            const $cg$14 = $cg$12.$2;
            const $cg$16 = $cg$14.$2;
            if(($cg$16.type === 1)) {
                return TParsec__Combinators__Chars__parens(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_3_arg, $partial_6_10$TermParse___123_chooseParser_95_928_125_($_3_arg, $cg$12.$1, $_4_arg, $cg$14.$1, $cg$16.$1, $cg$16.$2));
            } else {
                return TParsec__Combinators__Chars__parens(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_3_arg, $partial_4_8$TermParse___123_chooseParser_95_1208_125_($_3_arg, $cg$12.$1, $_4_arg, $cg$14.$1));
            }
        } else {
            const $cg$3 = $_1_arg.$1;
            if(($cg$3.type === 1)) {
                const $cg$6 = $cg$3.$1;
                if(($cg$6.type === 1)) {
                    
                    $_0_arg = null;
                    $_1_arg = new $HC_1_4$Typedefs__TVar(new $HC_1_1$Data__Fin__FS($cg$6.$1));
                    $_2_arg = null;
                    $_3_arg = $_3_arg;
                    $_4_arg = $_4_arg.$2;
                } else {
                    
                    const $cg$9 = $_4_arg.$2;
                    return $cg$9.$1;
                }
            } else {
                
                return $_4_arg.$1;
            }
        }
    }
}

// Data.NEList.consopt

function Data__NEList__consopt($_0_arg, $_1_arg, $_2_arg){
    const $cg$2 = Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0(null, null, $partial_0_1$Data__NEList___123_consopt_95_1209_125_(), $_2_arg);
    var $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = $cg$2.$1;
    } else {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    }
    
    return new $HC_2_0$Data__NEList__MkNEList($_1_arg, $cg$1);
}

// TParsec.Combinators.Numbers.decimalDigit

function TParsec__Combinators__Numbers__decimalDigit($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return TParsec__Combinators__alts(null, null, null, $_2_arg, null, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_6_7$TParsec__Combinators__Numbers___123_decimalDigit_95_1211_125_($_3_arg, $_1_arg, $_2_arg, $_6_arg, $_5_arg, $_4_arg), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("0"))), "0"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("1"))), "1"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("2"))), "2"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("3"))), "3"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("4"))), "4"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("5"))), "5"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("6"))), "6"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("7"))), "7"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("8"))), "8"), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair((new $JSRTS.jsbn.BigInteger(("9"))), "9"), $HC_0_0$Prelude__List__Nil))))))))))));
}

// TParsec.Combinators.Numbers.decimalNat

function TParsec__Combinators__Numbers__decimalNat($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    var $cg$1 = null;
    const $cg$3 = $_3_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators__Numbers___123_decimalNat_95_1213_125_(), null, TParsec__Combinators__nelist(null, null, null, $_2_arg, $_3_arg, $_7_arg)(TParsec__Combinators__Numbers__decimalDigit(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, null)));
}

// TermParse.deserialize

function TermParse__deserialize($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return TParsec__Running__parseMaybe(null, null, null, $partial_0_2$TermParse___123_deserialize_95_1215_125_(), $partial_0_1$TermParse___123_deserialize_95_1216_125_(), $partial_0_1$TermParse___123_deserialize_95_1217_125_(), $_4_arg, $partial_2_3$TermParse___123_deserialize_95_1218_125_($_3_arg, $_2_arg));
}

// Prelude.List.elemBy

function Prelude__List__elemBy($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    for(;;) {
        
        if(($_3_arg.type === 1)) {
            
            if($_1_arg($_2_arg)($_3_arg.$1)) {
                return true;
            } else {
                $_0_arg = null;
                $_1_arg = $_1_arg;
                $_2_arg = $_2_arg;
                $_3_arg = $_3_arg.$2;
            }
        } else {
            return false;
        }
    }
}

// Text.PrettyPrint.WL.Combinators.encloseSep

function Text__PrettyPrint__WL__Combinators__encloseSep($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        
        if(($_3_arg.$2.type === 0)) {
            return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_arg, $_3_arg.$1), $_1_arg);
        } else {
            return new $HC_1_7$Text__PrettyPrint__WL__Core__Column($partial_4_5$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1233_125_($_0_arg, $_3_arg, $_2_arg, $_1_arg));
        }
    } else if(($_3_arg.type === 0)) {
        return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_arg, $_1_arg);
    } else {
        return new $HC_1_7$Text__PrettyPrint__WL__Core__Column($partial_4_5$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1244_125_($_0_arg, $_3_arg, $_2_arg, $_1_arg));
    }
}

// Control.Monad.State.evalState

function Control__Monad__State__evalState($_0_arg, $_1_arg, $_2_arg, $_8_in){
    const $cg$2 = $_2_arg($_8_in);
    return $cg$2.$1;
}

// TParsec.Combinators.exact

function TParsec__Combinators__exact($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_9_12$TParsec__Combinators__guardM(null, null, null, null, $_2_arg, $_3_arg, $partial_2_3$TParsec__Combinators___123_exact_95_1246_125_($_5_arg, $_6_arg), null, $partial_5_8$TParsec__Combinators__anyTok(null, $_1_arg, $_2_arg, $_4_arg, null));
}

// Data.Vect.filter

function Data__Vect__filter($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        const $cg$3 = Data__Vect__filter(null, null, $_2_arg, $_3_arg.$2);
        
        if($_2_arg($_3_arg.$1)) {
            return new $HC_2_0$Builtins__MkDPair($cg$3.$1.add((new $JSRTS.jsbn.BigInteger(("1")))), new $HC_2_1$Data__Vect___58__58_($_3_arg.$1, $cg$3.$2));
        } else {
            return new $HC_2_0$Builtins__MkDPair($cg$3.$1, $cg$3.$2);
        }
    } else {
        return new $HC_2_0$Builtins__MkDPair((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Data__Vect__Nil);
    }
}

// Data.Fin.finToInteger

function Data__Fin__finToInteger($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        return (new $JSRTS.jsbn.BigInteger(("1"))).add(Data__Fin__finToInteger(null, $_1_arg.$1));
    } else {
        return (new $JSRTS.jsbn.BigInteger(("0")));
    }
}

// Text.PrettyPrint.WL.Core.fits

function Text__PrettyPrint__WL__Core__fits($_0_arg, $_1_arg){
    for(;;) {
        
        if(($_1_arg.type === 1)) {
            
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) < 0)) {
                return false;
            } else {
                $_0_arg = ($_0_arg - 1);
                $_1_arg = $_1_arg.$2;
            }
        } else if(($_1_arg.type === 0)) {
            return (!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) < 0));
        } else if(($_1_arg.type === 3)) {
            return (!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) < 0));
        } else {
            
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) < 0)) {
                return false;
            } else {
                $_0_arg = ($_0_arg - $_1_arg.$1);
                $_1_arg = $_1_arg.$3;
            }
        }
    }
}

// Induction.Nat.fix

function Induction__Nat__fix($_0_arg, $_1_arg, $_2_arg){
    return Induction__Nat__fixBox_58_go_58_0(null, $_1_arg, null, $_2_arg.add((new $JSRTS.jsbn.BigInteger(("1")))), $_2_arg)(Prelude__Nat__lteRefl($_2_arg.add((new $JSRTS.jsbn.BigInteger(("1"))))));
}

// Text.PrettyPrint.WL.Core.flatten

function Text__PrettyPrint__WL__Core__flatten($_0_arg){
    for(;;) {
        
        if(($_0_arg.type === 4)) {
            return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__flatten($_0_arg.$1), Text__PrettyPrint__WL__Core__flatten($_0_arg.$2));
        } else if(($_0_arg.type === 7)) {
            return new $HC_1_7$Text__PrettyPrint__WL__Core__Column($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1223_125_($_0_arg.$1));
        } else if(($_0_arg.type === 3)) {
            
            if($_0_arg.$1) {
                return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
            } else {
                return new $HC_2_2$Text__PrettyPrint__WL__Core__Text(1, " ");
            }
        } else if(($_0_arg.type === 5)) {
            return new $HC_2_5$Text__PrettyPrint__WL__Core__Nest($_0_arg.$1, Text__PrettyPrint__WL__Core__flatten($_0_arg.$2));
        } else if(($_0_arg.type === 8)) {
            return new $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1223_125_($_0_arg.$1));
        } else if(($_0_arg.type === 6)) {
            $_0_arg = $_0_arg.$1;
        } else {
            return $_0_arg;
        }
    }
}

// Backend.Utils.foldr1'

function Backend__Utils__foldr1_39_($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    const $cg$3 = $_3_arg.$2;
    if(($cg$3.type === 1)) {
        return $_2_arg($_3_arg.$1)(Backend__Utils__foldr1_39_(null, null, $_2_arg, new $HC_2_1$Data__Vect___58__58_($cg$3.$1, $cg$3.$2)));
    } else {
        return $_3_arg.$1;
    }
}

// Data.Vect.foldrImpl

function Data__Vect__foldrImpl($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    var $tco$$_5_arg = $_5_arg;
    for(;;) {
        
        if(($_6_arg.type === 1)) {
            $tco$$_5_arg = $partial_3_4$Data__Vect___123_foldrImpl_95_1249_125_($_5_arg, $_3_arg, $_6_arg.$1);
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
            $_5_arg = $tco$$_5_arg;
            $_6_arg = $_6_arg.$2;
        } else {
            return $_5_arg($_4_arg);
        }
    }
}

// Data.Vect.fromList

function Data__Vect__fromList($_0_arg, $_1_arg){
    return Data__Vect__reverse_58_go_58_0(null, null, null, null, null, $HC_0_0$Data__Vect__Nil, Data__Vect__fromList_39_(null, null, $HC_0_0$Data__Vect__Nil, $_1_arg));
}

// Data.Vect.fromList'

function Data__Vect__fromList_39_($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    for(;;) {
        
        if(($_3_arg.type === 1)) {
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = new $HC_2_1$Data__Vect___58__58_($_3_arg.$1, $_2_arg);
            $_3_arg = $_3_arg.$2;
        } else {
            return $_2_arg;
        }
    }
}

// Backend.generate

function Backend__generate($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    var $cg$1 = null;
    $cg$1 = $_1_arg.$2;
    var $cg$2 = null;
    var $cg$3 = null;
    $cg$3 = $_1_arg.$3($_2_arg);
    $cg$2 = $_1_arg.$1(null)($cg$3)($_3_arg);
    const $cg$5 = Text__PrettyPrint__WL__Combinators__punctuate(new $HC_1_3$Text__PrettyPrint__WL__Core__Line(false), Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $cg$1, $cg$2));
    if(($cg$5.type === 1)) {
        return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Backend___123_generate_95_1250_125_(), $cg$5.$1, $cg$5.$2);
    } else {
        return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
}

// Main.getSource

function Main__getSource($_0_w){
    return (getSource());
}

// TParsec.Success.getTok

function TParsec__Success__getTok($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0(null, null, $partial_1_2$TParsec__Success___123_getTok_95_1251_125_($_3_arg), $_2_arg($_3_arg)($_4_arg));
}

// Backend.getUsedIndices

function Backend__getUsedIndices($_0_arg, $_1_arg){
    for(;;) {
        
        if(($_1_arg.type === 0)) {
            return $HC_0_0$Prelude__List__Nil;
        } else if(($_1_arg.type === 1)) {
            return $HC_0_0$Prelude__List__Nil;
        } else if(($_1_arg.type === 5)) {
            return Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend___123_getUsedIndices_95_1253_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $_1_arg.$2);
        } else if(($_1_arg.type === 6)) {
            $_0_arg = null;
            $_1_arg = $_1_arg.$2;
        } else if(($_1_arg.type === 3)) {
            return Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend___123_getUsedIndices_95_1255_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $_1_arg.$1);
        } else if(($_1_arg.type === 2)) {
            return Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend___123_getUsedIndices_95_1255_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $_1_arg.$1);
        } else {
            return new $HC_2_1$Prelude__List___58__58_($_1_arg.$1, $HC_0_0$Prelude__List__Nil);
        }
    }
}

// Backend.getUsedVars

function Backend__getUsedVars($_0_arg, $_1_arg, $_2_arg){
    return Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Backend___123_getUsedVars_95_1259_125_($_1_arg), Data__Vect__fromList(null, Backend__getUsedIndices(null, $_2_arg)));
}

// TParsec.Combinators.guardM

function TParsec__Combinators__guardM($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_m1, $_10_mlen, $_11_ts){
    
    return $_5_arg.$2(null)(null)($_8_arg($_9_m1)($_10_mlen)($_11_ts))($partial_3_4$TParsec__Combinators___123_guardM_95_1262_125_($_4_arg, $_5_arg, $_6_arg));
}

// Backend.Haskell.guardParen

function Backend__Haskell__guardParen($_0_arg){
    
    if(($_0_arg.type === 4)) {
        
        if(($_0_arg.$3.type === 0)) {
            
            if($_0_arg.$1.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return Backend__Haskell__renderType(new $HC_3_4$Backend__Haskell__HsParam((new $JSRTS.jsbn.BigInteger(("0"))), $_0_arg.$2, $HC_0_0$Data__Vect__Nil));
            } else {
                return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("("), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__Haskell__renderType($_0_arg), Text__PrettyPrint__WL__Core__char(")")));
            }
        } else {
            return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("("), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__Haskell__renderType($_0_arg), Text__PrettyPrint__WL__Core__char(")")));
        }
    } else {
        return Backend__Haskell__renderType($_0_arg);
    }
}

// Prelude.List.head'

function Prelude__List__head_39_($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        return new $HC_1_1$Prelude__Maybe__Just($_1_arg.$1);
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Data.Vect.index

function Data__Vect__index($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = $_2_arg.$1;
            $_3_arg = $_3_arg.$2;
        } else {
            
            return $_3_arg.$1;
        }
    }
}

// Data.SortedMap.insert

function Data__SortedMap__insert($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 0)) {
        return new $HC_2_1$Data__SortedMap__M($_4_arg.$1, new $HC_2_0$Data__SortedMap__Leaf($_2_arg, $_3_arg));
    } else {
        const $cg$3 = Data__SortedMap__treeInsert(null, null, $_4_arg.$1, null, $_2_arg, $_3_arg, $_4_arg.$2);
        if(($cg$3.type === 0)) {
            return new $HC_2_1$Data__SortedMap__M($_4_arg.$1, $cg$3.$1);
        } else {
            return new $HC_2_1$Data__SortedMap__M($_4_arg.$1, $cg$3.$1);
        }
    }
}

// Prelude.Nat.isLTE

function Prelude__Nat__isLTE($_0_arg, $_1_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Prelude__Nat__LTEZero);
    } else {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            const $_2_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            const $cg$4 = Prelude__Nat__isLTE($_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1")))), $_2_in);
            if(($cg$4.type === 1)) {
                return $HC_0_1$Prelude__Basics__No;
            } else {
                return new $HC_1_0$Prelude__Basics__Yes(new $HC_1_1$Prelude__Nat__LTESucc($cg$4.$1));
            }
        }
    }
}

// Prelude.Chars.isLower

function Prelude__Chars__isLower($_0_arg){
    var $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "a") > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === "a");
    }
    
    
    if($cg$1) {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "z") < 0)) {
            return true;
        } else {
            return ($_0_arg === "z");
        }
    } else {
        return false;
    }
}

// Prelude.Chars.isUpper

function Prelude__Chars__isUpper($_0_arg){
    var $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "A") > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === "A");
    }
    
    
    if($cg$1) {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "Z") < 0)) {
            return true;
        } else {
            return ($_0_arg === "Z");
        }
    } else {
        return false;
    }
}

// TParsec.Combinators.land

function TParsec__Combinators__land($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    var $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_land_95_1264_125_(), null, $partial_8_11$TParsec__Combinators__andbind(null, null, null, null, $_4_arg, null, $_7_arg, $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_1210_125_($_8_arg)));
}

// TParsec.Combinators.landopt

function TParsec__Combinators__landopt($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    var $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_land_95_1264_125_(), null, $partial_9_12$TParsec__Combinators__andoptbind(null, null, null, null, $_4_arg, $_5_arg, null, $_7_arg, $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_1210_125_($_8_arg)));
}

// Data.Fin.last

function Data__Fin__last($_0_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Data__Fin__FZ;
    } else {
        const $_1_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_1_1$Data__Fin__FS(Data__Fin__last($_1_in));
    }
}

// Prelude.List.length

function Prelude__List__length($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        return Prelude__List__length(null, $_1_arg.$2).add((new $JSRTS.jsbn.BigInteger(("1"))));
    } else {
        return (new $JSRTS.jsbn.BigInteger(("0")));
    }
}

// TParsec.Combinators.Chars.lowerAlpha

function TParsec__Combinators__Chars__lowerAlpha($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    const $cg$2 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0(true, true);
    var $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    } else {
        var $cg$3 = null;
        if((((("abcdefghijklmnopqrstuvwxyz".slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$3 = true;
        } else {
            $cg$3 = false;
        }
        
        const $cg$5 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$3, true);
        var $cg$4 = null;
        if(($cg$5.type === 1)) {
            $cg$4 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$4 = new $HC_2_1$Prelude__Strings__StrCons("abcdefghijklmnopqrstuvwxyz".slice(1)[0], "abcdefghijklmnopqrstuvwxyz".slice(1).slice(1));
        }
        
        $cg$1 = new $HC_2_1$Prelude__List___58__58_("abcdefghijklmnopqrstuvwxyz"[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$4));
    }
    
    return TParsec__Combinators__anyOf(null, $_1_arg, $_2_arg, $_3_arg, $_6_arg, $_5_arg, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_4_arg, $cg$1), null);
}

// Prelude.Nat.lteRefl

function Prelude__Nat__lteRefl($_0_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__Nat__LTEZero;
    } else {
        const $_1_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_1_1$Prelude__Nat__LTESucc(Prelude__Nat__lteRefl($_1_in));
    }
}

// Prelude.Nat.lteTransitive

function Prelude__Nat__lteTransitive($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_3_arg.type === 1)) {
        return new $HC_1_1$Prelude__Nat__LTESucc(Prelude__Nat__lteTransitive(null, null, null, $_3_arg.$1, null));
    } else {
        return $_3_arg;
    }
}

// Main.main

function Main__main(){
    const $_0_in = Main__deserialize0("1", "1");
    
    if(($_0_in.type === 1)) {
        return $partial_0_1$Main___123_main_95_1272_125_();
    } else {
        return $partial_1_2$Main__setResult("foo");
    }
}

// Backend.Haskell.makeDefs

function Backend__Haskell__makeDefs($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 0)) {
        return $partial_0_1$Backend__Haskell___123_makeDefs_95_1273_125_();
    } else if(($_2_arg.type === 1)) {
        return $partial_0_1$Backend__Haskell___123_makeDefs_95_1273_125_();
    } else if(($_2_arg.type === 5)) {
        const $_7_in = new $HC_2_5$Typedefs__TMu($_2_arg.$1, $_2_arg.$2);
        return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $partial_0_1$Backend__Haskell___123_makeDefs_95_1279_125_(), $partial_4_5$Backend__Haskell___123_makeDefs_95_1311_125_($_2_arg.$1, $_1_arg, $_7_in, $_2_arg.$2));
    } else if(($_2_arg.type === 6)) {
        const $_134_in = new $HC_2_6$Typedefs__TName($_2_arg.$1, $_2_arg.$2);
        return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $partial_0_1$Backend__Haskell___123_makeDefs_95_1279_125_(), $partial_4_5$Backend__Haskell___123_makeDefs_95_1333_125_($_2_arg.$1, $_1_arg, $_2_arg.$2, $_134_in));
    } else if(($_2_arg.type === 3)) {
        return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_1337_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_2_3$Backend__Haskell__makeDefs(null, $_1_arg), $_2_arg.$1));
    } else if(($_2_arg.type === 2)) {
        return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_1337_125_(), Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_2_3$Backend__Haskell__makeDefs(null, $_1_arg), $_2_arg.$1));
    } else {
        return $partial_0_1$Backend__Haskell___123_makeDefs_95_1273_125_();
    }
}

// Backend.Haskell.makeType

function Backend__Haskell__makeType($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 0)) {
        return $HC_0_0$Backend__Haskell__HsVoid;
    } else if(($_2_arg.type === 1)) {
        return $HC_0_1$Backend__Haskell__HsUnit;
    } else if(($_2_arg.type === 5)) {
        const $_5_in = new $HC_2_5$Typedefs__TMu($_2_arg.$1, $_2_arg.$2);
        const $cg$11 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeType_95_1359_125_(), Backend__getUsedVars(null, $_1_arg, $_5_in));
        var $cg$10 = null;
        $cg$10 = $cg$11.$1;
        const $cg$13 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeType_95_1362_125_(), Backend__getUsedVars(null, $_1_arg, $_5_in));
        var $cg$12 = null;
        $cg$12 = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeType_95_1361_125_(), $cg$13.$2);
        return new $HC_3_4$Backend__Haskell__HsParam($cg$10, $_2_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeType_95_1360_125_(), $cg$12));
    } else if(($_2_arg.type === 6)) {
        const $_34_in = new $HC_2_6$Typedefs__TName($_2_arg.$1, $_2_arg.$2);
        const $cg$7 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_95_1282_125_(), Backend__getUsedVars(null, $_1_arg, $_34_in));
        var $cg$6 = null;
        $cg$6 = $cg$7.$1;
        const $cg$9 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeType_95_1366_125_(), Backend__getUsedVars(null, $_1_arg, $_34_in));
        var $cg$8 = null;
        $cg$8 = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeType_95_1365_125_(), $cg$9.$2);
        return new $HC_3_4$Backend__Haskell__HsParam($cg$6, $_2_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeType_95_1360_125_(), $cg$8));
    } else if(($_2_arg.type === 3)) {
        return new $HC_1_2$Backend__Haskell__HsTuple(Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__Haskell__makeType(null, $_1_arg), $_2_arg.$1));
    } else if(($_2_arg.type === 2)) {
        return Backend__Utils__foldr1_39_(null, null, $partial_0_2$Backend__Haskell___123_makeType_95_1367_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_2_3$Backend__Haskell__makeType(null, $_1_arg), $_2_arg.$1));
    } else {
        const $cg$3 = Data__Vect__index(null, null, $_2_arg.$1, $_1_arg);
        if(($cg$3.type === 0)) {
            return new $HC_1_3$Backend__Haskell__HsVar($cg$3.$1);
        } else {
            const $cg$5 = $cg$3.$1;
            return new $HC_3_4$Backend__Haskell__HsParam($cg$5.$1, $cg$5.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeType_95_1360_125_(), $cg$5.$3));
        }
    }
}

// TParsec.Combinators.mand

function TParsec__Combinators__mand($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_m1, $_9_mlen, $_10_ts){
    
    return $_4_arg.$2(null)(null)($_6_arg)($partial_5_6$TParsec__Combinators___123_mand_95_1370_125_($_4_arg, $_7_arg, $_8_m1, $_9_mlen, $_10_ts));
}

// TParsec.Combinators.map

function TParsec__Combinators__map($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_m1, $_9_le, $_10_ts){
    return $_4_arg(null)(null)($partial_1_2$TParsec__Combinators___123_map_95_1371_125_($_5_arg))($_7_arg($_8_m1)($_9_le)($_10_ts));
}

// TermParse.muParser

function TermParse__muParser($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_1$TermParse___123_chooseParser_95_71_125_(), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_3_arg, $partial_3_7$TermParse___123_muParser_95_1526_125_($_3_arg, $_1_arg, $_4_arg)));
}

// TParsec.Combinators.nelist

function TParsec__Combinators__nelist($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    return Induction__Nat__fix(null, $partial_2_5$TParsec__Combinators___123_nelist_95_1530_125_($_4_arg, $_3_arg), $_5_arg);
}

// Prelude.Nat.notLTImpliesGTE

function Prelude__Nat__notLTImpliesGTE($_0_arg, $_1_arg, $_2_arg){
    
    if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__Nat__LTEZero;
    } else {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return null;
        } else {
            const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            return new $HC_1_1$Prelude__Nat__LTESucc(Prelude__Nat__notLTImpliesGTE($_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1")))), $_3_in, null));
        }
    }
}

// TParsec.Combinators.optand

function TParsec__Combinators__optand($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    var $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    var $cg$4 = null;
    const $cg$6 = $_4_arg.$1;
    $cg$4 = $cg$6.$1;
    return $partial_7_10$TParsec__Combinators__alt(null, null, null, $_5_arg, null, $partial_8_11$TParsec__Combinators__andbind(null, null, null, null, $_4_arg, null, $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_optand_95_1531_125_(), null, $_7_arg), $partial_1_6$TParsec__Combinators___123_ands_95_8_125_($_8_arg)), $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$4, $partial_0_1$TParsec__Combinators___123_optand_95_1533_125_(), null, $_8_arg));
}

// TParsec.Combinators.Chars.parens

function TParsec__Combinators__Chars__parens($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_13_in){
    return TParsec__Combinators__land(null, null, null, null, $_4_arg, null, null, TParsec__Combinators__rand(null, null, null, null, $_4_arg, null, null, TParsec__Combinators__Chars__char(null, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, "(")($_8_arg), $_13_in), $partial_7_11$TParsec__Combinators__Chars___123_parens_95_1534_125_($_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg));
}

// TParsec.Running.parseMaybe

function TParsec__Running__parseMaybe($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    const $cg$2 = Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0(null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TParsec__Running___123_parseMaybe_95_1535_125_(), $partial_0_2$TParsec__Running___123_parseMaybe_95_1536_125_(), $partial_0_4$TParsec__Running___123_parseMaybe_95_1537_125_()), $partial_0_1$TParsec__Running___123_parseMaybe_95_1539_125_(), $_3_arg(null)($_7_arg(Prelude__List__length(null, $_4_arg($_6_arg)))(Prelude__List__length(null, $_4_arg($_6_arg)))(Prelude__Nat__lteRefl(Prelude__List__length(null, $_4_arg($_6_arg))))($_5_arg($_4_arg($_6_arg)))));
    if(($cg$2.type === 1)) {
        return Prelude__List__head_39_(null, $cg$2.$1);
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Parse.parseTDef

function Parse__parseTDef($_0_arg){
    return TParsec__Running__parseMaybe(null, null, null, $partial_0_2$Parse___123_parseTDef_95_1541_125_(), $partial_0_1$Parse___123_parseTDef_95_1542_125_(), $partial_0_1$TermParse___123_deserialize_95_1217_125_(), $_0_arg, $partial_0_1$Parse__tdefRec());
}

// Main.deserialize0

exports.deserialize0Impl = function Main__deserialize0($_0_arg, $_1_arg){
    const $cg$2 = Parse__parseTDef($_0_arg);
    if(($cg$2.type === 1)) {
        const $cg$4 = $cg$2.$1;
        
        if($cg$4.$1.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0(null, null, $partial_1_2$Main___123_deserialize0_95_1219_125_($cg$4.$2), TermParse__deserialize(null, null, $partial_0_1$Main___123_deserialize0_95_1220_125_(), $cg$4.$2, $_1_arg));
        } else {
            return $HC_0_0$Prelude__Maybe__Nothing;
        }
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Parse.parseThenStrFun

function Parse__parseThenStrFun($_0_arg, $_1_arg){
    const $cg$2 = Parse__parseTDef($_0_arg);
    if(($cg$2.type === 1)) {
        return $_1_arg($cg$2.$1);
    } else {
        return ("Failed to parse \'" + ($_0_arg + "\'."));
    }
}

// Prelude.Show.primNumShow

function Prelude__Show__primNumShow($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    const $_4_in = $_1_arg($_3_arg);
    var $cg$1 = null;
    $cg$1 = (new $JSRTS.jsbn.BigInteger(("0")));
    var $cg$2 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($cg$1, (new $JSRTS.jsbn.BigInteger(("5")))) > 0)) {
        $cg$2 = true;
    } else {
        var $cg$3 = null;
        $cg$3 = (new $JSRTS.jsbn.BigInteger(("0")));
        $cg$2 = $cg$3.equals((new $JSRTS.jsbn.BigInteger(("5"))));
    }
    
    var $cg$4 = null;
    if($cg$2) {
        var $cg$5 = null;
        if((((($_4_in == "")) ? 1|0 : 0|0) === 0)) {
            $cg$5 = true;
        } else {
            $cg$5 = false;
        }
        
        const $cg$7 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$5, true);
        if(($cg$7.type === 1)) {
            $cg$4 = false;
        } else {
            $cg$4 = ($_4_in[0] === "-");
        }
    } else {
        $cg$4 = false;
    }
    
    
    if($cg$4) {
        return ("(" + ($_4_in + ")"));
    } else {
        return $_4_in;
    }
}

// Text.PrettyPrint.WL.Combinators.punctuate

function Text__PrettyPrint__WL__Combinators__punctuate($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        
        if(($_1_arg.$2.type === 0)) {
            return new $HC_2_1$Prelude__List___58__58_($_1_arg.$1, $HC_0_0$Prelude__List__Nil);
        } else {
            return new $HC_2_1$Prelude__List___58__58_(new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_1_arg.$1, $_0_arg), Text__PrettyPrint__WL__Combinators__punctuate($_0_arg, $_1_arg.$2));
        }
    } else {
        return $_1_arg;
    }
}

// TParsec.Combinators.rand

function TParsec__Combinators__rand($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    var $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_rand_95_1544_125_(), null, $partial_8_11$TParsec__Combinators__andbind(null, null, null, null, $_4_arg, null, $_7_arg, $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_1210_125_($_8_arg)));
}

// TParsec.Combinators.randbindm

function TParsec__Combinators__randbindm($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    var $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_randbindm_95_1546_125_(), null, $partial_8_11$TParsec__Combinators__andbindm(null, null, null, null, $_4_arg, null, $_6_arg, $_7_arg));
}

// Backend.Haskell.renderApp

function Backend__Haskell__renderApp($_0_arg, $_1_arg, $_2_arg){
    var $cg$1 = null;
    if((((($_1_arg == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    var $cg$2 = null;
    if(($cg$3.type === 1)) {
        $cg$2 = "";
    } else {
        var $cg$4 = null;
        if(Prelude__Chars__isLower($_1_arg[0])) {
            $cg$4 = String.fromCharCode(((($_1_arg[0]).charCodeAt(0)|0) - 32));
        } else {
            $cg$4 = $_1_arg[0];
        }
        
        $cg$2 = (($cg$4)+($_1_arg.slice(1)));
    }
    
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__text($cg$2), Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Backend__Haskell___123_renderApp_95_1547_125_(), $HC_0_0$Text__PrettyPrint__WL__Core__Empty, Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__Haskell___123_makeDefs_95_1300_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $_2_arg)));
}

// Backend.Haskell.renderDef

function Backend__Haskell__renderDef($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$7 = $_0_arg.$1;
        var $cg$6 = null;
        $cg$6 = $cg$7.$2;
        const $cg$9 = $_0_arg.$1;
        var $cg$8 = null;
        $cg$8 = $cg$9.$3;
        const $cg$11 = Text__PrettyPrint__WL__Combinators__punctuate(Text__PrettyPrint__WL__Core__text(" |"), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__Haskell___123_makeDefs_95_1300_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$TermParse___123_chooseParser_95_66_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_3_4$Backend__Haskell__renderDef_58_renderConstructor_58_1(null, null, null), $_0_arg.$2)));
        var $cg$10 = null;
        if(($cg$11.type === 1)) {
            $cg$10 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Backend__Haskell___123_renderApp_95_1547_125_(), $cg$11.$1, $cg$11.$2);
        } else {
            $cg$10 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        }
        
        return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__text("data"), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__Haskell__renderApp(null, $cg$6, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_renderDef_95_1550_125_(), $cg$8)), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("="), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), $cg$10))))));
    } else {
        const $cg$3 = $_0_arg.$1;
        var $cg$2 = null;
        $cg$2 = $cg$3.$2;
        const $cg$5 = $_0_arg.$1;
        var $cg$4 = null;
        $cg$4 = $cg$5.$3;
        return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__text("type"), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Backend__Haskell__renderApp(null, $cg$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_renderDef_95_1554_125_(), $cg$4)), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char("="), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), Backend__Haskell__renderType($_0_arg.$2)))))));
    }
}

// Backend.Haskell.renderType

function Backend__Haskell__renderType($_0_arg){
    
    if(($_0_arg.type === 4)) {
        return Backend__Haskell__renderApp(null, $_0_arg.$2, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell__guardParen(), $_0_arg.$3));
    } else if(($_0_arg.type === 2)) {
        return Text__PrettyPrint__WL__Combinators__encloseSep(Text__PrettyPrint__WL__Core__char("("), Text__PrettyPrint__WL__Core__char(")"), Text__PrettyPrint__WL__Core__char(","), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__Haskell___123_makeDefs_95_1300_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$TermParse___123_chooseParser_95_66_125_(), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell__renderType(), $_0_arg.$1)));
    } else if(($_0_arg.type === 1)) {
        return Text__PrettyPrint__WL__Core__text("()");
    } else if(($_0_arg.type === 3)) {
        var $cg$2 = null;
        if((((($_0_arg.$1 == "")) ? 1|0 : 0|0) === 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = false;
        }
        
        const $cg$4 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$2, true);
        var $cg$3 = null;
        if(($cg$4.type === 1)) {
            $cg$3 = "";
        } else {
            var $cg$5 = null;
            if(Prelude__Chars__isUpper($_0_arg.$1[0])) {
                $cg$5 = String.fromCharCode(((($_0_arg.$1[0]).charCodeAt(0)|0) + 32));
            } else {
                $cg$5 = $_0_arg.$1[0];
            }
            
            $cg$3 = (($cg$5)+($_0_arg.$1.slice(1)));
        }
        
        return Text__PrettyPrint__WL__Core__text($cg$3);
    } else {
        return Text__PrettyPrint__WL__Core__text("Void");
    }
}

// Prelude.List.replicate

function Prelude__List__replicate($_0_arg, $_1_arg, $_2_arg){
    
    if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__List__Nil;
    } else {
        const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_2_1$Prelude__List___58__58_($_2_arg, Prelude__List__replicate(null, $_3_in, $_2_arg));
    }
}

// Prelude.List.reverseOnto

function Prelude__List__reverseOnto($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            $_0_arg = null;
            $_1_arg = new $HC_2_1$Prelude__List___58__58_($_2_arg.$1, $_1_arg);
            $_2_arg = $_2_arg.$2;
        } else {
            return $_1_arg;
        }
    }
}

// TParsec.Combinators.roptand

function TParsec__Combinators__roptand($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg){
    var $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_rand_95_1544_125_(), null, TParsec__Combinators__optand(null, null, null, null, $_4_arg, $_5_arg, null, $_7_arg, $_8_arg));
}

// Main.setResult

function Main__setResult($_0_x, $_1_w){
    return (setResult(($_0_x)));
}

// TParsec.Combinators.Chars.space

function TParsec__Combinators__Chars__space($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    const $cg$2 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0(true, true);
    var $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    } else {
        var $cg$3 = null;
        if(((((" \t\n".slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$3 = true;
        } else {
            $cg$3 = false;
        }
        
        const $cg$5 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$3, true);
        var $cg$4 = null;
        if(($cg$5.type === 1)) {
            $cg$4 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$4 = new $HC_2_1$Prelude__Strings__StrCons(" \t\n".slice(1)[0], " \t\n".slice(1).slice(1));
        }
        
        $cg$1 = new $HC_2_1$Prelude__List___58__58_(" \t\n"[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$4));
    }
    
    return TParsec__Combinators__anyOf(null, $_1_arg, $_2_arg, $_3_arg, $_6_arg, $_5_arg, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_4_arg, $cg$1), null);
}

// Text.PrettyPrint.WL.Core.spaces

function Text__PrettyPrint__WL__Core__spaces($_0_arg){
    var $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) < 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === 0);
    }
    
    
    if($cg$1) {
        return "";
    } else {
        return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, (new $JSRTS.jsbn.BigInteger(''+($_0_arg))), " "));
    }
}

// TParsec.Combinators.Chars.string

function TParsec__Combinators__Chars__string($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_arg){
    var $cg$1 = null;
    if((((($_7_arg == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    if(($cg$3.type === 1)) {
        return null;
    } else {
        var $cg$4 = null;
        const $cg$6 = $_3_arg.$1;
        $cg$4 = $cg$6.$1;
        var $cg$7 = null;
        if((((($_7_arg.slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$7 = true;
        } else {
            $cg$7 = false;
        }
        
        const $cg$9 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$7, true);
        var $cg$8 = null;
        if(($cg$9.type === 1)) {
            $cg$8 = $HC_0_0$Prelude__List__Nil;
        } else {
            var $cg$10 = null;
            if((((($_7_arg.slice(1).slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                $cg$10 = true;
            } else {
                $cg$10 = false;
            }
            
            const $cg$12 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$10, true);
            var $cg$11 = null;
            if(($cg$12.type === 1)) {
                $cg$11 = $HC_0_0$Prelude__Strings__StrNil;
            } else {
                $cg$11 = new $HC_2_1$Prelude__Strings__StrCons($_7_arg.slice(1).slice(1)[0], $_7_arg.slice(1).slice(1).slice(1));
            }
            
            $cg$8 = new $HC_2_1$Prelude__List___58__58_($_7_arg.slice(1)[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$11));
        }
        
        return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$4, $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_1210_125_($_7_arg), null, TParsec__Combinators__ands(null, null, null, $_3_arg, null, new $HC_2_0$Data__NEList__MkNEList(TParsec__Combinators__Chars__char(null, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg[0])($_9_arg), Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_7_8$TParsec__Combinators__Chars___123_string_95_1559_125_($_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_9_arg), $cg$8))));
    }
}

// TParsec.Combinators.sum

function TParsec__Combinators__sum($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    var $cg$1 = null;
    const $cg$3 = $_4_arg.$1;
    $cg$1 = $cg$3.$1;
    var $cg$4 = null;
    const $cg$6 = $_4_arg.$1;
    $cg$4 = $cg$6.$1;
    return $partial_7_10$TParsec__Combinators__alt(null, null, null, $_4_arg, null, $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_sum_95_1560_125_(), null, $_6_arg), $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$4, $partial_0_1$TParsec__Combinators___123_sum_95_1561_125_(), null, $_7_arg));
}

// Parse.tdef

function Parse__tdef($_0_arg){
    return Induction__Nat__fix(null, $partial_0_2$Parse___123_tdef_95_5102_125_(), $_0_arg);
}

// Parse.tdefRec

function Parse__tdefRec($_0_arg){
    return Induction__Nat__fix(null, $partial_0_2$Parse___123_tdefRec_95_5213_125_(), $_0_arg);
}

// Text.PrettyPrint.WL.Core.text

function Text__PrettyPrint__WL__Core__text($_0_arg){
    
    if(($_0_arg === "")) {
        return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    } else {
        return new $HC_2_2$Text__PrettyPrint__WL__Core__Text((((new $JSRTS.jsbn.BigInteger(''+((($_0_arg).length))))).intValue()|0), $_0_arg);
    }
}

// Prelude.Maybe.toMaybe

function Prelude__Maybe__toMaybe($_0_arg, $_1_arg, $_2_arg){
    
    if($_1_arg) {
        return new $HC_1_1$Prelude__Maybe__Just($JSRTS.force($_2_arg));
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Text.PrettyPrint.WL.Core.toString

function Text__PrettyPrint__WL__Core__toString($_0_arg, $_1_arg, $_2_arg){
    return Text__PrettyPrint__WL__Core__showPrettyDoc_58_showPrettyDocS_58_0(null, Text__PrettyPrint__WL__Core__render_58_best_58_0($_0_arg, $_1_arg, null, $_1_arg, 0, 0, $_2_arg, $partial_0_1$Text__PrettyPrint__WL__Core___123_toString_95_5214_125_()), "");
}

// Parse.toVMax

function Parse__toVMax($_0_arg, $_1_arg, $_2_arg){
    
    const $cg$3 = $_2_arg.$1;
    const $cg$5 = $_2_arg.$2;
    if(($cg$5.type === 1)) {
        const $cg$7 = Parse__toVMax(null, null, new $HC_2_1$Data__Vect___58__58_($cg$5.$1, $cg$5.$2));
        const $cg$9 = Prelude__Nat__isLTE($cg$3.$1, $cg$7.$1);
        if(($cg$9.type === 1)) {
            return new $HC_2_0$Builtins__MkDPair($cg$3.$1, new $HC_4_2$Parse__VMConsMore($cg$7.$1, $cg$3.$2, $cg$7.$2, Prelude__Nat__notLTImpliesGTE($cg$7.$1, $cg$3.$1, null)));
        } else {
            return new $HC_2_0$Builtins__MkDPair($cg$7.$1, new $HC_4_1$Parse__VMConsLess($cg$3.$1, $cg$3.$2, $cg$7.$2, $cg$9.$1));
        }
    } else {
        return new $HC_2_0$Builtins__MkDPair($cg$3.$1, new $HC_1_0$Parse__VMEnd($cg$3.$2));
    }
}

// Data.SortedMap.treeInsert

function Data__SortedMap__treeInsert($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    const $cg$2 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg);
    if(($cg$2.type === 0)) {
        return new $HC_1_0$Prelude__Either__Left($cg$2.$1);
    } else {
        const $cg$4 = $cg$2.$1;
        const $cg$6 = $cg$4.$2;
        return new $HC_1_1$Prelude__Either__Right(new $HC_3_1$Data__SortedMap__Branch2($cg$4.$1, $cg$6.$1, $cg$6.$2));
    }
}

// Data.SortedMap.treeInsert'

function Data__SortedMap__treeInsert_39_($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if(($_6_arg.type === 1)) {
        
        
        if($_2_arg.$3($_4_arg)($_6_arg.$2)) {
            const $cg$36 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$1);
            if(($cg$36.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_1$Data__SortedMap__Branch2($cg$36.$1, $_6_arg.$2, $_6_arg.$3));
            } else {
                const $cg$38 = $cg$36.$1;
                const $cg$40 = $cg$38.$2;
                return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($cg$38.$1, $cg$40.$1, $cg$40.$2, $_6_arg.$2, $_6_arg.$3));
            }
        } else {
            const $cg$30 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$3);
            if(($cg$30.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$1, $_6_arg.$2, $cg$30.$1));
            } else {
                const $cg$32 = $cg$30.$1;
                const $cg$34 = $cg$32.$2;
                return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($_6_arg.$1, $_6_arg.$2, $cg$32.$1, $cg$34.$1, $cg$34.$2));
            }
        }
    } else if(($_6_arg.type === 2)) {
        
        
        if($_2_arg.$3($_4_arg)($_6_arg.$2)) {
            const $cg$22 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$1);
            if(($cg$22.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($cg$22.$1, $_6_arg.$2, $_6_arg.$3, $_6_arg.$4, $_6_arg.$5));
            } else {
                const $cg$24 = $cg$22.$1;
                const $cg$26 = $cg$24.$2;
                return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_3_1$Data__SortedMap__Branch2($cg$24.$1, $cg$26.$1, $cg$26.$2), new $HC_2_0$Builtins__MkPair($_6_arg.$2, new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$3, $_6_arg.$4, $_6_arg.$5))));
            }
        } else {
            
            
            if($_2_arg.$3($_4_arg)($_6_arg.$4)) {
                const $cg$16 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$3);
                if(($cg$16.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($_6_arg.$1, $_6_arg.$2, $cg$16.$1, $_6_arg.$4, $_6_arg.$5));
                } else {
                    const $cg$18 = $cg$16.$1;
                    const $cg$20 = $cg$18.$2;
                    return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$1, $_6_arg.$2, $cg$18.$1), new $HC_2_0$Builtins__MkPair($cg$20.$1, new $HC_3_1$Data__SortedMap__Branch2($cg$20.$2, $_6_arg.$4, $_6_arg.$5))));
                }
            } else {
                const $cg$10 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$5);
                if(($cg$10.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($_6_arg.$1, $_6_arg.$2, $_6_arg.$3, $_6_arg.$4, $cg$10.$1));
                } else {
                    const $cg$12 = $cg$10.$1;
                    const $cg$14 = $cg$12.$2;
                    return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$1, $_6_arg.$2, $_6_arg.$3), new $HC_2_0$Builtins__MkPair($_6_arg.$4, new $HC_3_1$Data__SortedMap__Branch2($cg$12.$1, $cg$14.$1, $cg$14.$2))));
                }
            }
        }
    } else {
        
        const $cg$4 = $_2_arg.$2($_4_arg)($_6_arg.$1);
        if(($cg$4 === 0)) {
            return new $HC_1_0$Prelude__Either__Left(new $HC_2_0$Data__SortedMap__Leaf($_4_arg, $_5_arg));
        } else if(($cg$4 > 0)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_2_0$Data__SortedMap__Leaf($_6_arg.$1, $_6_arg.$2), new $HC_2_0$Builtins__MkPair($_6_arg.$1, new $HC_2_0$Data__SortedMap__Leaf($_4_arg, $_5_arg))));
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_2_0$Data__SortedMap__Leaf($_4_arg, $_5_arg), new $HC_2_0$Builtins__MkPair($_4_arg, new $HC_2_0$Data__SortedMap__Leaf($_6_arg.$1, $_6_arg.$2))));
        }
    }
}

// Data.SortedMap.treeLookup

function Data__SortedMap__treeLookup($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    for(;;) {
        
        if(($_5_arg.type === 1)) {
            
            
            if($_2_arg.$3($_4_arg)($_5_arg.$2)) {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = $_2_arg;
                $_3_arg = null;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg.$1;
            } else {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = $_2_arg;
                $_3_arg = null;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg.$3;
            }
        } else if(($_5_arg.type === 2)) {
            
            
            if($_2_arg.$3($_4_arg)($_5_arg.$2)) {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = $_2_arg;
                $_3_arg = null;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg.$1;
            } else {
                
                
                if($_2_arg.$3($_4_arg)($_5_arg.$4)) {
                    $_0_arg = null;
                    $_1_arg = null;
                    $_2_arg = $_2_arg;
                    $_3_arg = null;
                    $_4_arg = $_4_arg;
                    $_5_arg = $_5_arg.$3;
                } else {
                    $_0_arg = null;
                    $_1_arg = null;
                    $_2_arg = $_2_arg;
                    $_3_arg = null;
                    $_4_arg = $_4_arg;
                    $_5_arg = $_5_arg.$5;
                }
            }
        } else {
            
            
            if($_2_arg.$1($_4_arg)($_5_arg.$1)) {
                return new $HC_1_1$Prelude__Maybe__Just($_5_arg.$2);
            } else {
                return $HC_0_0$Prelude__Maybe__Nothing;
            }
        }
    }
}

// Backend.Utils.unindex

function Backend__Utils__unindex($_0_arg, $_1_arg, $_2_arg){
    
    if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Data__Vect__Nil;
    } else {
        const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_2_1$Data__Vect___58__58_($_2_arg($HC_0_0$Data__Fin__FZ), Backend__Utils__unindex(null, $_3_in, $partial_1_2$Backend__Utils___123_unindex_95_5215_125_($_2_arg)));
    }
}

// TParsec.Combinators.Chars.upperAlpha

function TParsec__Combinators__Chars__upperAlpha($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    const $cg$2 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0(true, true);
    var $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    } else {
        var $cg$3 = null;
        if((((("ABCDEFGHIJKLMNOPQRSTUVWXYZ".slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$3 = true;
        } else {
            $cg$3 = false;
        }
        
        const $cg$5 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$3, true);
        var $cg$4 = null;
        if(($cg$5.type === 1)) {
            $cg$4 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$4 = new $HC_2_1$Prelude__Strings__StrCons("ABCDEFGHIJKLMNOPQRSTUVWXYZ".slice(1)[0], "ABCDEFGHIJKLMNOPQRSTUVWXYZ".slice(1).slice(1));
        }
        
        $cg$1 = new $HC_2_1$Prelude__List___58__58_("ABCDEFGHIJKLMNOPQRSTUVWXYZ"[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$4));
    }
    
    return TParsec__Combinators__anyOf(null, $_1_arg, $_2_arg, $_3_arg, $_6_arg, $_5_arg, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_4_arg, $cg$1), null);
}

// Data.Fin.weakenN

function Data__Fin__weakenN($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        return new $HC_1_1$Data__Fin__FS(Data__Fin__weakenN(null, null, $_2_arg.$1));
    } else {
        return $_2_arg;
    }
}

// Typedefs.weakenNTDefs

function Typedefs__weakenNTDefs($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_2_arg.type === 1)) {
        const $cg$3 = $_2_arg.$1;
        return new $HC_2_1$Data__Vect___58__58_(new $HC_2_0$Builtins__MkPair($cg$3.$1, Typedefs__weakenTDef(null, $cg$3.$2, $_3_arg, $_4_arg)), Typedefs__weakenNTDefs(null, null, $_2_arg.$2, $_3_arg, $_4_arg));
    } else {
        return $_2_arg;
    }
}

// Typedefs.weakenTDef

function Typedefs__weakenTDef($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_1_arg.type === 0)) {
        return $_1_arg;
    } else if(($_1_arg.type === 1)) {
        return $_1_arg;
    } else if(($_1_arg.type === 5)) {
        return new $HC_2_5$Typedefs__TMu($_1_arg.$1, Typedefs__weakenNTDefs(null, null, $_1_arg.$2, $_2_arg.add((new $JSRTS.jsbn.BigInteger(("1")))), new $HC_1_1$Prelude__Nat__LTESucc($_3_arg)));
    } else if(($_1_arg.type === 6)) {
        return new $HC_2_6$Typedefs__TName($_1_arg.$1, Typedefs__weakenTDef(null, $_1_arg.$2, $_2_arg, $_3_arg));
    } else if(($_1_arg.type === 3)) {
        return new $HC_1_3$Typedefs__TProd(Typedefs__weakenTDefs(null, null, $_1_arg.$1, $_2_arg, $_3_arg));
    } else if(($_1_arg.type === 2)) {
        return new $HC_1_2$Typedefs__TSum(Typedefs__weakenTDefs(null, null, $_1_arg.$1, $_2_arg, $_3_arg));
    } else {
        
        if($_2_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return null;
        } else {
            const $_11_in = $_2_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            var $_12_in = null;
            $_12_in = $_3_arg.$1;
            return new $HC_1_4$Typedefs__TVar(Data__Fin__weakenN(null, null, $_1_arg.$1));
        }
    }
}

// Typedefs.weakenTDefs

function Typedefs__weakenTDefs($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_2_arg.type === 1)) {
        return new $HC_2_1$Data__Vect___58__58_(Typedefs__weakenTDef(null, $_2_arg.$1, $_3_arg, $_4_arg), Typedefs__weakenTDefs(null, null, $_2_arg.$2, $_3_arg, $_4_arg));
    } else {
        return $_2_arg;
    }
}

// TParsec.Combinators.Chars.withSpaces

function TParsec__Combinators__Chars__withSpaces($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_arg){
    return TParsec__Combinators__roptand(null, null, null, null, $_4_arg, $_3_arg, null, TParsec__Combinators__nelist(null, null, null, $_3_arg, $_4_arg, $_8_arg)(TParsec__Combinators__Chars__space(null, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, null)), TParsec__Combinators__landopt(null, null, null, null, $_4_arg, $_3_arg, null, $_9_arg, $partial_7_11$TParsec__Combinators__Chars___123_withSpaces_95_5216_125_($_3_arg, $_4_arg, $_8_arg, $_2_arg, $_5_arg, $_6_arg, $_7_arg)));
}

// Prelude.List.zipWith

function Prelude__List__zipWith($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        
        if(($_4_arg.type === 1)) {
            return new $HC_2_1$Prelude__List___58__58_($_3_arg($_4_arg.$1)($_5_arg.$1), Prelude__List__zipWith(null, null, null, $_3_arg, $_4_arg.$2, $_5_arg.$2));
        } else {
            return $_4_arg;
        }
    } else {
        
        if(($_4_arg.type === 1)) {
            return $HC_0_0$Prelude__List__Nil;
        } else {
            return $_4_arg;
        }
    }
}

// TParsec.Combinators.Chars.{alphas_0}

function TParsec__Combinators__Chars___123_alphas_95_0_125_($_0_lift, $_1_lift){
    var $cg$1 = null;
    $cg$1 = $_1_lift.$1;
    var $cg$2 = null;
    $cg$2 = $_1_lift.$2;
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_0_lift, new $HC_2_1$Prelude__List___58__58_($cg$1, $cg$2)));
}

// TParsec.Combinators.{alts_1}

function TParsec__Combinators___123_alts_95_1_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    return $_0_lift.$2(null);
}

// TParsec.Combinators.{andbind_2}

function TParsec__Combinators___123_andbind_95_2_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    var $cg$4 = null;
    $cg$4 = $_2_lift.$1;
    var $cg$5 = null;
    $cg$5 = $_2_lift.$2;
    var $cg$6 = null;
    $cg$6 = $_2_lift.$3;
    var $cg$7 = null;
    $cg$7 = $_2_lift.$2;
    var $cg$8 = null;
    $cg$8 = $_2_lift.$2;
    var $cg$9 = null;
    $cg$9 = $_2_lift.$4;
    return $cg$3.$1(null)(null)($partial_5_6$TParsec__Success__and(null, null, null, null, $_2_lift))($_1_lift($cg$4)($cg$5)(Prelude__Nat__lteTransitive(null, null, null, $cg$6, null))($cg$7)(Prelude__Nat__lteRefl($cg$8))($cg$9));
}

// TParsec.Combinators.{andbindm_3}

function TParsec__Combinators___123_andbindm_95_3_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    var $cg$4 = null;
    $cg$4 = new $HC_4_0$TParsec__Success__MkSuccess(new $HC_2_0$Builtins__MkPair($_1_lift.$1, $_2_lift), $_1_lift.$2, $_1_lift.$3, $_1_lift.$4);
    return $cg$3.$2(null)($cg$4);
}

// TParsec.Combinators.{andbindm_4}

function TParsec__Combinators___123_andbindm_95_4_125_($_0_lift, $_1_lift, $_2_lift){
    
    var $cg$2 = null;
    $cg$2 = $_2_lift.$1;
    return $_0_lift.$2(null)(null)($_1_lift($cg$2))($partial_2_3$TParsec__Combinators___123_andbindm_95_3_125_($_0_lift, $_2_lift));
}

// TParsec.Combinators.{andoptbind_5}

function TParsec__Combinators___123_andoptbind_95_5_125_($_0_lift, $_1_lift){
    const $cg$2 = TParsec__Success__and(null, null, null, null, $_0_lift, $_1_lift);
    const $cg$4 = $cg$2.$1;
    var $cg$3 = null;
    $cg$3 = new $HC_2_0$Builtins__MkPair($cg$4.$1, new $HC_1_1$Prelude__Maybe__Just($cg$4.$2));
    return new $HC_4_0$TParsec__Success__MkSuccess($cg$3, $cg$2.$2, $cg$2.$3, $cg$2.$4);
}

// TParsec.Combinators.{andoptbind_6}

function TParsec__Combinators___123_andoptbind_95_6_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    var $cg$2 = null;
    const $cg$4 = $_1_lift.$1;
    var $cg$5 = null;
    $cg$5 = $_3_lift.$1;
    var $cg$6 = null;
    $cg$6 = $_3_lift.$2;
    var $cg$7 = null;
    $cg$7 = $_3_lift.$3;
    var $cg$8 = null;
    $cg$8 = $_3_lift.$2;
    var $cg$9 = null;
    $cg$9 = $_3_lift.$2;
    var $cg$10 = null;
    $cg$10 = $_3_lift.$4;
    $cg$2 = $cg$4.$1(null)(null)($partial_1_2$TParsec__Combinators___123_andoptbind_95_5_125_($_3_lift))($_2_lift($cg$5)($cg$6)(Prelude__Nat__lteTransitive(null, null, null, $cg$7, null))($cg$8)(Prelude__Nat__lteRefl($cg$9))($cg$10));
    var $cg$11 = null;
    const $cg$13 = $_1_lift.$1;
    var $cg$14 = null;
    $cg$14 = new $HC_4_0$TParsec__Success__MkSuccess(new $HC_2_0$Builtins__MkPair($_3_lift.$1, $HC_0_0$Prelude__Maybe__Nothing), $_3_lift.$2, $_3_lift.$3, $_3_lift.$4);
    $cg$11 = $cg$13.$2(null)($cg$14);
    return $_0_lift.$3(null)($cg$2)($cg$11);
}

// TParsec.Combinators.{ands_7}

function TParsec__Combinators___123_ands_95_7_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$1;
    const $cg$5 = $_0_lift.$2;
    var $cg$4 = null;
    $cg$4 = $cg$5.$1;
    const $cg$7 = $_0_lift.$2;
    var $cg$6 = null;
    $cg$6 = $cg$7.$2;
    return new $HC_2_0$Data__NEList__MkNEList($cg$3.$1, Prelude__List___43__43_(null, $cg$3.$2, new $HC_2_1$Prelude__List___58__58_($cg$4, $cg$6)));
}

// TParsec.Combinators.{ands_8}

function TParsec__Combinators___123_ands_95_8_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return $_0_lift($_4_lift)(Prelude__Nat__lteTransitive(null, null, null, $_5_lift, null));
}

// TParsec.Combinators.{ands_9}

function TParsec__Combinators___123_ands_95_9_125_($_0_lift, $_1_lift, $_2_lift){
    var $cg$1 = null;
    const $cg$3 = $_0_lift.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_ands_95_7_125_(), null, $partial_8_11$TParsec__Combinators__andbind(null, null, null, null, $_0_lift, null, $_1_lift, $partial_1_6$TParsec__Combinators___123_ands_95_8_125_($_2_lift)));
}

// TParsec.Combinators.{ands_10}

function TParsec__Combinators___123_ands_95_10_125_($_0_lift){
    return new $HC_2_0$Data__NEList__MkNEList($_0_lift, $HC_0_0$Prelude__List__Nil);
}

// TParsec.Combinators.{anyOf_12}

function TParsec__Combinators___123_anyOf_95_12_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return TParsec__Combinators__exact(null, $_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, null);
}

// TParsec.Combinators.{anyTok_13}

function TParsec__Combinators___123_anyTok_95_13_125_($_0_lift, $_1_lift){
    return $_1_lift;
}

// TParsec.Combinators.{anyTok_14}

function TParsec__Combinators___123_anyTok_95_14_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    var $cg$2 = null;
    const $cg$4 = $_0_lift.$1;
    var $cg$5 = null;
    const $cg$7 = $_0_lift.$1;
    var $cg$8 = null;
    $cg$8 = $_2_lift.$1;
    $cg$5 = $cg$7.$1(null)(null)($partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_())($_1_lift($cg$8));
    var $cg$9 = null;
    const $cg$11 = $_0_lift.$1;
    $cg$9 = $cg$11.$2(null)($_2_lift);
    $cg$2 = $cg$4.$3(null)(null)($cg$5)($cg$9);
    return $_0_lift.$3(null)($cg$2)($_3_lift);
}

// Typedefs.{args_15}

function Typedefs___123_args_95_15_125_($_0_lift){
    
    return $_0_lift.$2;
}

// TermParse.{chooseParser_16}

function TermParse___123_chooseParser_95_16_125_($_0_lift, $_1_lift, $_2_lift){
    return $_2_lift;
}

// TermParse.{chooseParser_19}

function TermParse___123_chooseParser_95_19_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $_3_lift($_2_lift);
}

// TermParse.{chooseParser_20}

function TermParse___123_chooseParser_95_20_125_($_0_lift){
    return $HC_0_0$MkUnit;
}

// TermParse.{chooseParser_21}

function TermParse___123_chooseParser_95_21_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33_empty_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $partial_0_1$TermParse___123_chooseParser_95_20_125_());
}

// TermParse.{chooseParser_23}

function TermParse___123_chooseParser_95_23_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Functor__TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0(null, null, null, null, null, $partial_0_3$TermParse___123_chooseParser_95_16_125_(), $_2_lift, $_3_lift);
}

// TermParse.{chooseParser_25}

function TermParse___123_chooseParser_95_25_125_($_0_lift, $_1_lift){
    return new $HC_1_2$TParsec__Result__Value(new $HC_2_0$Builtins__MkPair($HC_0_0$MkUnit, $_1_lift));
}

// TermParse.{chooseParser_32}

function TermParse___123_chooseParser_95_32_125_($_0_lift, $_1_lift){
    return $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $_1_lift);
}

// TermParse.{chooseParser_37}

function TermParse___123_chooseParser_95_37_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0(null, null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $_2_lift, $_3_lift);
}

// TermParse.{chooseParser_43}

function TermParse___123_chooseParser_95_43_125_($_0_lift){
    return $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33_empty_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $partial_0_1$TermParse___123_chooseParser_95_20_125_());
}

// TermParse.{chooseParser_48}

function TermParse___123_chooseParser_95_48_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_8_9$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), null, $_1_lift, $_2_lift);
}

// TermParse.{chooseParser_65}

function TermParse___123_chooseParser_95_65_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Monad__TParsec__Types___64_Prelude__Monad__Monad_36_TParsecT_32_e_32_a_32_m_58__33__62__62__61__58_0(null, null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $_2_lift, $_3_lift);
}

// TermParse.{chooseParser_66}

function TermParse___123_chooseParser_95_66_125_($_0_lift){
    return $_0_lift;
}

// TermParse.{chooseParser_67}

function TermParse___123_chooseParser_95_67_125_($_0_lift, $_1_lift){
    return ($_0_lift === $_1_lift);
}

// TermParse.{chooseParser_68}

function TermParse___123_chooseParser_95_68_125_($_0_lift, $_1_lift){
    return Data__Inspect__Data__Inspect___64_Data__Inspect__Inspect_36_SizedList_32_a_58_a_58__33_inspect_58_0_58_go_58_0(null, null, null, null, $_0_lift, $_1_lift, null);
}

// TermParse.{chooseParser_71}

function TermParse___123_chooseParser_95_71_125_($_0_lift){
    return $HC_0_0$Typedefs__Inn;
}

// TermParse.{chooseParser_221}

function TermParse___123_chooseParser_95_221_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TermParse__chooseParser(null, Typedefs__args(null, null, $_1_lift), null, $_0_lift, new $HC_2_1$TermParse___58__58_(TermParse__muParser(null, Typedefs__args(null, null, $_1_lift), null, $_0_lift, $_2_lift), $_2_lift)))($_5_lift)(Prelude__Nat__lteTransitive(null, null, null, $_6_lift, null));
}

// TermParse.{chooseParser_222}

function TermParse___123_chooseParser_95_222_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), null, null, TParsec__Combinators__Chars__string(null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "inn", null, $_0_lift), $partial_3_7$TermParse___123_chooseParser_95_221_125_($_0_lift, $_1_lift, $_2_lift))($_5_lift)(Prelude__Nat__lteTransitive(null, null, null, $_6_lift, null));
}

// TermParse.{chooseParser_433}

function TermParse___123_chooseParser_95_433_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift){
    return TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TermParse__chooseParser(null, new $HC_1_3$Typedefs__TProd(new $HC_2_1$Data__Vect___58__58_($_1_lift, new $HC_2_1$Data__Vect___58__58_($_2_lift, $_3_lift))), null, $_0_lift, $_4_lift))($_8_lift)(Prelude__Nat__lteTransitive(null, null, null, $_9_lift, null));
}

// TermParse.{chooseParser_434}

function TermParse___123_chooseParser_95_434_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift){
    return $partial_10_11$TParsec__Combinators__andbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), null, TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TermParse__chooseParser(null, $_1_lift, null, $_0_lift, $_2_lift)), $partial_5_10$TermParse___123_chooseParser_95_433_125_($_0_lift, $_3_lift, $_4_lift, $_5_lift, $_2_lift), $_8_lift, Prelude__Nat__lteTransitive(null, null, null, $_9_lift, null));
}

// TermParse.{chooseParser_435}

function TermParse___123_chooseParser_95_435_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), null, null, TParsec__Combinators__Chars__string(null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "both", null, $_0_lift), $partial_6_10$TermParse___123_chooseParser_95_434_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift))($_8_lift)(Prelude__Nat__lteTransitive(null, null, null, $_9_lift, null));
}

// TermParse.{chooseParser_646}

function TermParse___123_chooseParser_95_646_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift){
    return TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TermParse__chooseParser(null, $_1_lift, null, $_0_lift, $_2_lift))($_6_lift)(Prelude__Nat__lteTransitive(null, null, null, $_7_lift, null));
}

// TermParse.{chooseParser_647}

function TermParse___123_chooseParser_95_647_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift){
    return $partial_10_11$TParsec__Combinators__andbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), null, TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TermParse__chooseParser(null, $_1_lift, null, $_0_lift, $_2_lift)), $partial_3_8$TermParse___123_chooseParser_95_646_125_($_0_lift, $_3_lift, $_2_lift), $_6_lift, Prelude__Nat__lteTransitive(null, null, null, $_7_lift, null));
}

// TermParse.{chooseParser_648}

function TermParse___123_chooseParser_95_648_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), null, null, TParsec__Combinators__Chars__string(null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "both", null, $_0_lift), $partial_4_8$TermParse___123_chooseParser_95_647_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift))($_6_lift)(Prelude__Nat__lteTransitive(null, null, null, $_7_lift, null));
}

// TermParse.{chooseParser_821}

function TermParse___123_chooseParser_95_821_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TermParse__chooseParser(null, $_1_lift, null, $_0_lift, $_2_lift))($_5_lift)(Prelude__Nat__lteTransitive(null, null, null, $_6_lift, null));
}

// TermParse.{chooseParser_927}

function TermParse___123_chooseParser_95_927_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift){
    return TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TermParse__chooseParser(null, new $HC_1_2$Typedefs__TSum(new $HC_2_1$Data__Vect___58__58_($_1_lift, new $HC_2_1$Data__Vect___58__58_($_2_lift, $_3_lift))), null, $_0_lift, $_4_lift))($_7_lift)(Prelude__Nat__lteTransitive(null, null, null, $_8_lift, null));
}

// TermParse.{chooseParser_928}

function TermParse___123_chooseParser_95_928_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift){
    return TParsec__Combinators__sum(null, null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), null, TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), null, null, TParsec__Combinators__Chars__string(null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "left", null, $_0_lift), $partial_3_7$TermParse___123_chooseParser_95_821_125_($_0_lift, $_1_lift, $_2_lift)), TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), null, null, TParsec__Combinators__Chars__string(null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "right", null, $_0_lift), $partial_5_9$TermParse___123_chooseParser_95_927_125_($_0_lift, $_3_lift, $_4_lift, $_5_lift, $_2_lift)))($_8_lift)(Prelude__Nat__lteTransitive(null, null, null, $_9_lift, null));
}

// TermParse.{chooseParser_1208}

function TermParse___123_chooseParser_95_1208_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift){
    return TParsec__Combinators__sum(null, null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), null, TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), null, null, TParsec__Combinators__Chars__string(null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "left", null, $_0_lift), $partial_3_7$TermParse___123_chooseParser_95_821_125_($_0_lift, $_1_lift, $_2_lift)), TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), null, null, TParsec__Combinators__Chars__string(null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "right", null, $_0_lift), $partial_3_7$TermParse___123_chooseParser_95_821_125_($_0_lift, $_3_lift, $_2_lift)))($_6_lift)(Prelude__Nat__lteTransitive(null, null, null, $_7_lift, null));
}

// Data.NEList.{consopt_1209}

function Data__NEList___123_consopt_95_1209_125_($_0_lift){
    var $cg$1 = null;
    $cg$1 = $_0_lift.$1;
    var $cg$2 = null;
    $cg$2 = $_0_lift.$2;
    return new $HC_2_1$Prelude__List___58__58_($cg$1, $cg$2);
}

// TParsec.Combinators.Numbers.{decimalDigit_1210}

function TParsec__Combinators__Numbers___123_decimalDigit_95_1210_125_($_0_lift, $_1_lift){
    return $_0_lift;
}

// TParsec.Combinators.Numbers.{decimalDigit_1211}

function TParsec__Combinators__Numbers___123_decimalDigit_95_1211_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    
    var $cg$2 = null;
    const $cg$4 = $_0_lift.$1;
    $cg$2 = $cg$4.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$2, $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_1210_125_($_6_lift.$1), null, TParsec__Combinators__exact(null, $_1_lift, $_2_lift, $_0_lift, $_3_lift, $_4_lift, $_5_lift($_6_lift.$2), null));
}

// TParsec.Combinators.Numbers.{decimalNat_1212}

function TParsec__Combinators__Numbers___123_decimalNat_95_1212_125_($_0_lift, $_1_lift){
    return (new $JSRTS.jsbn.BigInteger(("10"))).multiply($_0_lift).add($_1_lift);
}

// TParsec.Combinators.Numbers.{decimalNat_1213}

function TParsec__Combinators__Numbers___123_decimalNat_95_1213_125_($_0_lift){
    var $cg$1 = null;
    $cg$1 = $_0_lift.$1;
    var $cg$2 = null;
    $cg$2 = $_0_lift.$2;
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$TParsec__Combinators__Numbers___123_decimalNat_95_1212_125_(), (new $JSRTS.jsbn.BigInteger(("0"))), new $HC_2_1$Prelude__List___58__58_($cg$1, $cg$2));
}

// TermParse.{deserialize_1214}

function TermParse___123_deserialize_95_1214_125_($_0_lift, $_1_lift){
    return new $HC_2_1$Prelude__List___58__58_($_1_lift, $HC_0_0$Prelude__List__Nil);
}

// TermParse.{deserialize_1215}

function TermParse___123_deserialize_95_1215_125_($_0_lift, $_1_lift){
    return TParsec__Running__TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0(null, null, null, null, $partial_0_2$TermParse___123_deserialize_95_1214_125_(), $_1_lift);
}

// TermParse.{deserialize_1216}

function TermParse___123_deserialize_95_1216_125_($_0_lift){
    var $cg$1 = null;
    if((((($_0_lift == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    if(($cg$3.type === 1)) {
        return $HC_0_0$Prelude__List__Nil;
    } else {
        var $cg$4 = null;
        if((((($_0_lift.slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$4 = true;
        } else {
            $cg$4 = false;
        }
        
        const $cg$6 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$4, true);
        var $cg$5 = null;
        if(($cg$6.type === 1)) {
            $cg$5 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$5 = new $HC_2_1$Prelude__Strings__StrCons($_0_lift.slice(1)[0], $_0_lift.slice(1).slice(1));
        }
        
        return new $HC_2_1$Prelude__List___58__58_($_0_lift[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$5));
    }
}

// TermParse.{deserialize_1217}

function TermParse___123_deserialize_95_1217_125_($_0_lift){
    return Data__Inspect__MkSizedList(null, $_0_lift);
}

// TermParse.{deserialize_1218}

function TermParse___123_deserialize_95_1218_125_($_0_lift, $_1_lift, $_2_lift){
    return TermParse__chooseParser(null, $_0_lift, null, $_2_lift, $_1_lift($_2_lift));
}

// Main.{deserialize0_1219}

function Main___123_deserialize0_95_1219_125_($_0_lift, $_1_lift){
    return new $HC_2_0$Builtins__MkDPair($_0_lift, $_1_lift);
}

// Main.{deserialize0_1220}

function Main___123_deserialize0_95_1220_125_($_0_lift){
    return $HC_0_0$TermParse__Nil;
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_1223}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1223_125_($_0_lift, $_1_lift){
    return Text__PrettyPrint__WL__Core__flatten($_0_lift($_1_lift));
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_1225}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1225_125_($_0_lift, $_1_lift){
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_lift, new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_1_3$Text__PrettyPrint__WL__Core__Line(true), $_1_lift));
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_1226}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1226_125_($_0_lift, $_1_lift){
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_lift, $_1_lift);
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_1231}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1231_125_($_0_lift, $_1_lift, $_2_lift){
    const $cg$2 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1226_125_(), new $HC_2_1$Prelude__List___58__58_($_0_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_1_lift), $_2_lift)), $_1_lift);
    if(($cg$2.type === 1)) {
        return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1225_125_(), $cg$2.$1, $cg$2.$2);
    } else {
        return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_1232}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1232_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    const $cg$2 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1226_125_(), new $HC_2_1$Prelude__List___58__58_($_1_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_2_lift), $_3_lift)), $_2_lift);
    var $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1225_125_(), $cg$2.$1, $cg$2.$2);
    } else {
        $cg$1 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
    
    var $cg$3 = null;
    if(($cg$1.type === 4)) {
        $cg$3 = new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__flatten($cg$1.$1), Text__PrettyPrint__WL__Core__flatten($cg$1.$2));
    } else if(($cg$1.type === 7)) {
        $cg$3 = new $HC_1_7$Text__PrettyPrint__WL__Core__Column($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1223_125_($cg$1.$1));
    } else if(($cg$1.type === 3)) {
        
        if($cg$1.$1) {
            $cg$3 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        } else {
            $cg$3 = new $HC_2_2$Text__PrettyPrint__WL__Core__Text(1, " ");
        }
    } else if(($cg$1.type === 5)) {
        $cg$3 = new $HC_2_5$Text__PrettyPrint__WL__Core__Nest($cg$1.$1, Text__PrettyPrint__WL__Core__flatten($cg$1.$2));
    } else if(($cg$1.type === 8)) {
        $cg$3 = new $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1223_125_($cg$1.$1));
    } else if(($cg$1.type === 6)) {
        $cg$3 = Text__PrettyPrint__WL__Core__flatten($cg$1.$1);
    } else {
        const $cg$5 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1226_125_(), new $HC_2_1$Prelude__List___58__58_($_1_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_2_lift), $_3_lift)), $_2_lift);
        if(($cg$5.type === 1)) {
            $cg$3 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1225_125_(), $cg$5.$1, $cg$5.$2);
        } else {
            $cg$3 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        }
    }
    
    return new $HC_2_5$Text__PrettyPrint__WL__Core__Nest(($_0_lift - $_5_lift), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_2_6$Text__PrettyPrint__WL__Core__Union($cg$3, new $JSRTS.Lazy((function(){
        return (function(){
            return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1231_125_($_1_lift, $_2_lift, $_3_lift);
        })();
    }))), $_4_lift));
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_1233}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1233_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($partial_5_6$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1232_125_($_4_lift, $_0_lift, $_1_lift, $_2_lift, $_3_lift));
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_1242}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1242_125_($_0_lift, $_1_lift, $_2_lift){
    const $cg$2 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1226_125_(), new $HC_2_1$Prelude__List___58__58_($_0_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_1_lift), $_2_lift)), $_1_lift);
    if(($cg$2.type === 1)) {
        return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1225_125_(), $cg$2.$1, $cg$2.$2);
    } else {
        return $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_1243}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1243_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    const $cg$2 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1226_125_(), new $HC_2_1$Prelude__List___58__58_($_1_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_2_lift), $_3_lift)), $_2_lift);
    var $cg$1 = null;
    if(($cg$2.type === 1)) {
        $cg$1 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1225_125_(), $cg$2.$1, $cg$2.$2);
    } else {
        $cg$1 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
    }
    
    var $cg$3 = null;
    if(($cg$1.type === 4)) {
        $cg$3 = new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__flatten($cg$1.$1), Text__PrettyPrint__WL__Core__flatten($cg$1.$2));
    } else if(($cg$1.type === 7)) {
        $cg$3 = new $HC_1_7$Text__PrettyPrint__WL__Core__Column($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1223_125_($cg$1.$1));
    } else if(($cg$1.type === 3)) {
        
        if($cg$1.$1) {
            $cg$3 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        } else {
            $cg$3 = new $HC_2_2$Text__PrettyPrint__WL__Core__Text(1, " ");
        }
    } else if(($cg$1.type === 5)) {
        $cg$3 = new $HC_2_5$Text__PrettyPrint__WL__Core__Nest($cg$1.$1, Text__PrettyPrint__WL__Core__flatten($cg$1.$2));
    } else if(($cg$1.type === 8)) {
        $cg$3 = new $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($partial_1_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1223_125_($cg$1.$1));
    } else if(($cg$1.type === 6)) {
        $cg$3 = Text__PrettyPrint__WL__Core__flatten($cg$1.$1);
    } else {
        const $cg$5 = Prelude__List__zipWith(null, null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1226_125_(), new $HC_2_1$Prelude__List___58__58_($_1_lift, Prelude__List__replicate(null, Prelude__List__length(null, $_2_lift), $_3_lift)), $_2_lift);
        if(($cg$5.type === 1)) {
            $cg$3 = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1225_125_(), $cg$5.$1, $cg$5.$2);
        } else {
            $cg$3 = $HC_0_0$Text__PrettyPrint__WL__Core__Empty;
        }
    }
    
    return new $HC_2_5$Text__PrettyPrint__WL__Core__Nest(($_0_lift - $_5_lift), new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_2_6$Text__PrettyPrint__WL__Core__Union($cg$3, new $JSRTS.Lazy((function(){
        return (function(){
            return Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1242_125_($_1_lift, $_2_lift, $_3_lift);
        })();
    }))), $_4_lift));
}

// Text.PrettyPrint.WL.Combinators.{encloseSep_1244}

function Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1244_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_1_8$Text__PrettyPrint__WL__Core__Nesting($partial_5_6$Text__PrettyPrint__WL__Combinators___123_encloseSep_95_1243_125_($_4_lift, $_0_lift, $_1_lift, $_2_lift, $_3_lift));
}

// TParsec.Combinators.{exact_1246}

function TParsec__Combinators___123_exact_95_1246_125_($_0_lift, $_1_lift, $_2_lift){
    return Prelude__Maybe__toMaybe(null, $_0_lift($_1_lift)($_2_lift), new $JSRTS.Lazy((function(){
        return (function(){
            return TermParse___123_chooseParser_95_66_125_($_2_lift);
        })();
    })));
}

// Data.Vect.{foldrImpl_1249}

function Data__Vect___123_foldrImpl_95_1249_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $_0_lift($_1_lift($_2_lift)($_3_lift));
}

// Backend.{generate_1250}

function Backend___123_generate_95_1250_125_($_0_lift, $_1_lift){
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_lift, new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(new $HC_1_3$Text__PrettyPrint__WL__Core__Line(false), $_1_lift));
}

// TParsec.Success.{getTok_1251}

function TParsec__Success___123_getTok_95_1251_125_($_0_lift, $_1_lift){
    
    if($_0_lift.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return null;
    } else {
        const $_6_in = $_0_lift.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        
        return new $HC_4_0$TParsec__Success__MkSuccess($_1_lift.$1, $_6_in, Prelude__Nat__lteRefl($_6_in.add((new $JSRTS.jsbn.BigInteger(("1"))))), $_1_lift.$2);
    }
}

// Backend.{getUsedIndices_1252}

function Backend___123_getUsedIndices_95_1252_125_($_0_lift, $_1_lift){
    var $cg$1 = null;
    if(($_0_lift.type === 1)) {
        $cg$1 = new $HC_2_1$Prelude__List___58__58_($_0_lift.$1, $HC_0_0$Prelude__List__Nil);
    } else {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    }
    
    return Prelude__List___43__43_(null, $cg$1, $_1_lift);
}

// Backend.{getUsedIndices_1253}

function Backend___123_getUsedIndices_95_1253_125_($_0_lift, $_1_lift){
    var $cg$1 = null;
    $cg$1 = $_0_lift.$2;
    return Prelude__List___43__43_(null, Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$Backend___123_getUsedIndices_95_1252_125_(), $HC_0_0$Prelude__List__Nil, Backend__getUsedIndices(null, $cg$1)), $_1_lift);
}

// Backend.{getUsedIndices_1255}

function Backend___123_getUsedIndices_95_1255_125_($_0_lift, $_1_lift){
    return Prelude__List___43__43_(null, Backend__getUsedIndices(null, $_0_lift), $_1_lift);
}

// Backend.{getUsedVars_1259}

function Backend___123_getUsedVars_95_1259_125_($_0_lift, $_1_lift){
    return Data__Vect__index(null, null, $_1_lift, $_0_lift);
}

// TParsec.Combinators.{guardM_1260}

function TParsec__Combinators___123_guardM_95_1260_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    var $cg$2 = null;
    const $cg$4 = $_1_lift.$1;
    $cg$2 = $cg$4.$2(null)($_2_lift);
    return $_0_lift.$3(null)($cg$2)($_3_lift);
}

// TParsec.Combinators.{guardM_1261}

function TParsec__Combinators___123_guardM_95_1261_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_4_0$TParsec__Success__MkSuccess($_3_lift, $_0_lift, $_1_lift, $_2_lift);
}

// TParsec.Combinators.{guardM_1262}

function TParsec__Combinators___123_guardM_95_1262_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    var $cg$1 = null;
    $cg$1 = $_0_lift.$2(null);
    var $cg$2 = null;
    $cg$2 = Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0(null, null, $partial_3_4$TParsec__Combinators___123_guardM_95_1261_125_($_3_lift.$2, $_3_lift.$3, $_3_lift.$4), $_2_lift($_3_lift.$1));
    return Prelude__Foldable__Prelude__Maybe___64_Prelude__Foldable__Foldable_36_Maybe_58__33_foldr_58_0(null, null, $partial_2_4$TParsec__Combinators___123_guardM_95_1260_125_($_0_lift, $_1_lift), $cg$1, $cg$2);
}

// TParsec.Combinators.{land_1264}

function TParsec__Combinators___123_land_95_1264_125_($_0_lift){
    
    return $_0_lift.$1;
}

// Main.{main_1268}

function Main___123_main_95_1268_125_($_0_lift, $_1_lift, $_2_lift){
    return Prelude__List__reverseOnto(null, $HC_0_0$Prelude__List__Nil, Control__Monad__State__evalState(null, null, Backend__Haskell__makeDefs(null, $_1_lift, $_2_lift), $HC_0_0$Prelude__List__Nil));
}

// Main.{main_1269}

function Main___123_main_95_1269_125_($_0_lift){
    return new $HC_1_0$Prelude__Either__Left(("x" + Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrBigInt(), $HC_0_0$Prelude__Show__Open, Data__Fin__finToInteger(null, $_0_lift))));
}

// Main.{main_1270}

function Main___123_main_95_1270_125_($_0_lift){
    return Backend__Utils__unindex(null, $_0_lift, $partial_0_1$Main___123_main_95_1269_125_());
}

// Main.{main_1271}

function Main___123_main_95_1271_125_($_0_lift){
    var $cg$1 = null;
    $cg$1 = $_0_lift.$1;
    var $cg$2 = null;
    $cg$2 = $_0_lift.$2;
    return Text__PrettyPrint__WL__Core__toString(1.0, 80, Backend__generate(null, new $HC_3_0$Backend__Backend_95_ictor($partial_0_3$Main___123_main_95_1268_125_(), $partial_0_1$Backend__Haskell__renderDef(), $partial_0_1$Main___123_main_95_1270_125_()), $cg$1, $cg$2));
}

// Main.{main_1272}

function Main___123_main_95_1272_125_($_0_lift){
    const $_3_in = Main__getSource($_0_lift);
    return Main__setResult(Parse__parseThenStrFun($_3_in, $partial_0_1$Main___123_main_95_1271_125_()), $_0_lift);
}

// Backend.Haskell.{makeDefs_1273}

function Backend__Haskell___123_makeDefs_95_1273_125_($_0_lift){
    return new $HC_2_0$Builtins__MkPair($HC_0_0$Prelude__List__Nil, $_0_lift);
}

// Backend.Haskell.{makeDefs_1279}

function Backend__Haskell___123_makeDefs_95_1279_125_($_0_lift){
    return new $HC_2_0$Builtins__MkPair($_0_lift, $_0_lift);
}

// Backend.Haskell.{makeDefs_1280}

function Backend__Haskell___123_makeDefs_95_1280_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeDefs_1281}

function Backend__Haskell___123_makeDefs_95_1281_125_($_0_lift){
    
    if(($_0_lift.type === 0)) {
        return $_0_lift.$1;
    } else {
        return "";
    }
}

// Backend.Haskell.{makeDefs_1282}

function Backend__Haskell___123_makeDefs_95_1282_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeDefs_1283}

function Backend__Haskell___123_makeDefs_95_1283_125_($_0_lift, $_1_lift){
    
    return new $HC_2_0$Builtins__MkPair($_1_lift.$1, Backend__Haskell__makeType(null, $_0_lift, $_1_lift.$2));
}

// Backend.Haskell.{makeDefs_1289}

function Backend__Haskell___123_makeDefs_95_1289_125_($_0_lift, $_1_lift){
    return Prelude__List___43__43_(null, $_0_lift, $_1_lift);
}

// Backend.Haskell.{makeDefs_1290}

function Backend__Haskell___123_makeDefs_95_1290_125_($_0_lift){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$Backend__Haskell___123_makeDefs_95_1289_125_(), $HC_0_0$Prelude__List__Nil, $_0_lift);
}

// Backend.Haskell.{makeDefs_1292}

function Backend__Haskell___123_makeDefs_95_1292_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$TermParse___123_chooseParser_95_16_125_(), $_2_lift, $_3_lift);
}

// Backend.Haskell.{makeDefs_1293}

function Backend__Haskell___123_makeDefs_95_1293_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_0$Builtins__MkPair($_1_lift, $_2_lift);
}

// Backend.Haskell.{makeDefs_1298}

function Backend__Haskell___123_makeDefs_95_1298_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $partial_7_8$Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $_2_lift, $_3_lift);
}

// Backend.Haskell.{makeDefs_1299}

function Backend__Haskell___123_makeDefs_95_1299_125_($_0_lift, $_1_lift){
    
    return Backend__Haskell__makeDefs(null, $_0_lift, $_1_lift.$2);
}

// Backend.Haskell.{makeDefs_1300}

function Backend__Haskell___123_makeDefs_95_1300_125_($_0_lift, $_1_lift){
    return new $HC_2_1$Prelude__List___58__58_($_0_lift, $_1_lift);
}

// Backend.Haskell.{makeDefs_1306}

function Backend__Haskell___123_makeDefs_95_1306_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_0$Builtins__MkPair($HC_0_0$MkUnit, new $HC_2_1$Prelude__List___58__58_($_0_lift, $_1_lift));
}

// Backend.Haskell.{makeDefs_1307}

function Backend__Haskell___123_makeDefs_95_1307_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_(new $HC_2_1$Backend__Haskell__ADT($_0_lift, $_1_lift), $_2_lift), $_4_lift);
}

// Backend.Haskell.{makeDefs_1308}

function Backend__Haskell___123_makeDefs_95_1308_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $partial_2_3$Backend__Haskell___123_makeDefs_95_1306_125_($_0_lift, $_1_lift), $partial_3_5$Backend__Haskell___123_makeDefs_95_1307_125_($_2_lift, $_3_lift, $_4_lift));
}

// Backend.Haskell.{makeDefs_1310}

function Backend__Haskell___123_makeDefs_95_1310_125_($_0_lift, $_1_lift){
    return ($_0_lift == $_1_lift);
}

// Backend.Haskell.{makeDefs_1311}

function Backend__Haskell___123_makeDefs_95_1311_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(Prelude__List__elemBy(null, $partial_0_2$Backend__Haskell___123_makeDefs_95_1310_125_(), $_0_lift, $_4_lift)) {
        return $partial_0_1$Backend__Haskell___123_makeDefs_95_1273_125_();
    } else {
        const $cg$3 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_95_1280_125_(), Backend__getUsedVars(null, $_1_lift, $_2_lift));
        var $cg$2 = null;
        $cg$2 = $cg$3.$1;
        const $cg$5 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_95_1282_125_(), Backend__getUsedVars(null, $_1_lift, $_2_lift));
        var $cg$4 = null;
        $cg$4 = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeDefs_95_1281_125_(), $cg$5.$2);
        const $_26_in = new $HC_3_0$Backend__MkDecl($cg$2, $_0_lift, $cg$4);
        const $_52_in = new $HC_2_1$Data__Vect___58__58_(new $HC_1_1$Prelude__Either__Right($_26_in), $_1_lift);
        const $_53_in = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Backend__Haskell___123_makeDefs_95_1283_125_($_52_in), $_3_lift);
        return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_1$Backend__Haskell___123_makeDefs_95_1290_125_(), Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0(null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_1_2$Backend__Haskell___123_makeDefs_95_1299_125_($_52_in), Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__Haskell___123_makeDefs_95_1300_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $_3_lift))), $partial_4_5$Backend__Haskell___123_makeDefs_95_1308_125_($_0_lift, $_4_lift, $_26_in, $_53_in));
    }
}

// Backend.Haskell.{makeDefs_1326}

function Backend__Haskell___123_makeDefs_95_1326_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeDefs_1327}

function Backend__Haskell___123_makeDefs_95_1327_125_($_0_lift){
    
    if(($_0_lift.type === 0)) {
        return $_0_lift.$1;
    } else {
        return "";
    }
}

// Backend.Haskell.{makeDefs_1328}

function Backend__Haskell___123_makeDefs_95_1328_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeDefs_1329}

function Backend__Haskell___123_makeDefs_95_1329_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    const $cg$2 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_95_1326_125_(), Backend__getUsedVars(null, $_0_lift, $_1_lift));
    var $cg$1 = null;
    $cg$1 = $cg$2.$1;
    const $cg$4 = Data__Vect__filter(null, null, $partial_0_1$Backend__Haskell___123_makeDefs_95_1328_125_(), Backend__getUsedVars(null, $_0_lift, $_1_lift));
    var $cg$3 = null;
    $cg$3 = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell___123_makeDefs_95_1327_125_(), $cg$4.$2);
    return new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Backend__Haskell__Synonym(new $HC_3_0$Backend__MkDecl($cg$1, $_2_lift, $cg$3), Backend__Haskell__makeType(null, $_0_lift, $_3_lift)), $_4_lift), $_6_lift);
}

// Backend.Haskell.{makeDefs_1330}

function Backend__Haskell___123_makeDefs_95_1330_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $partial_2_3$Backend__Haskell___123_makeDefs_95_1306_125_($_0_lift, $_1_lift), $partial_5_7$Backend__Haskell___123_makeDefs_95_1329_125_($_2_lift, $_3_lift, $_0_lift, $_4_lift, $_5_lift));
}

// Backend.Haskell.{makeDefs_1333}

function Backend__Haskell___123_makeDefs_95_1333_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(Prelude__List__elemBy(null, $partial_0_2$Backend__Haskell___123_makeDefs_95_1310_125_(), $_0_lift, $_4_lift)) {
        return $partial_0_1$Backend__Haskell___123_makeDefs_95_1273_125_();
    } else {
        return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), Backend__Haskell__makeDefs(null, $_1_lift, $_2_lift), $partial_5_6$Backend__Haskell___123_makeDefs_95_1330_125_($_0_lift, $_4_lift, $_1_lift, $_3_lift, $_2_lift));
    }
}

// Backend.Haskell.{makeDefs_1337}

function Backend__Haskell___123_makeDefs_95_1337_125_($_0_lift){
    return Data__Vect__foldrImpl(null, null, null, $partial_0_2$Backend__Haskell___123_makeDefs_95_1289_125_(), $HC_0_0$Prelude__List__Nil, $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $_0_lift);
}

// Backend.Haskell.{makeType_1359}

function Backend__Haskell___123_makeType_95_1359_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeType_1360}

function Backend__Haskell___123_makeType_95_1360_125_($_0_lift){
    return new $HC_1_3$Backend__Haskell__HsVar($_0_lift);
}

// Backend.Haskell.{makeType_1361}

function Backend__Haskell___123_makeType_95_1361_125_($_0_lift){
    
    if(($_0_lift.type === 0)) {
        return $_0_lift.$1;
    } else {
        return "";
    }
}

// Backend.Haskell.{makeType_1362}

function Backend__Haskell___123_makeType_95_1362_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeType_1365}

function Backend__Haskell___123_makeType_95_1365_125_($_0_lift){
    
    if(($_0_lift.type === 0)) {
        return $_0_lift.$1;
    } else {
        return "";
    }
}

// Backend.Haskell.{makeType_1366}

function Backend__Haskell___123_makeType_95_1366_125_($_0_lift){
    return (!(!($_0_lift.type === 0)));
}

// Backend.Haskell.{makeType_1367}

function Backend__Haskell___123_makeType_95_1367_125_($_0_lift, $_1_lift){
    return new $HC_3_4$Backend__Haskell__HsParam((new $JSRTS.jsbn.BigInteger(("2"))), "Either", new $HC_2_1$Data__Vect___58__58_($_0_lift, new $HC_2_1$Data__Vect___58__58_($_1_lift, $HC_0_0$Data__Vect__Nil)));
}

// TParsec.Combinators.{mand_1369}

function TParsec__Combinators___123_mand_95_1369_125_($_0_lift, $_1_lift){
    
    return new $HC_4_0$TParsec__Success__MkSuccess(new $HC_2_0$Builtins__MkPair($_0_lift, $_1_lift.$1), $_1_lift.$2, $_1_lift.$3, $_1_lift.$4);
}

// TParsec.Combinators.{mand_1370}

function TParsec__Combinators___123_mand_95_1370_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    
    const $cg$3 = $_0_lift.$1;
    return $cg$3.$1(null)(null)($partial_1_2$TParsec__Combinators___123_mand_95_1369_125_($_5_lift))($_1_lift($_2_lift)($_3_lift)($_4_lift));
}

// TParsec.Combinators.{map_1371}

function TParsec__Combinators___123_map_95_1371_125_($_0_lift, $_1_lift){
    
    return new $HC_4_0$TParsec__Success__MkSuccess($_0_lift($_1_lift.$1), $_1_lift.$2, $_1_lift.$3, $_1_lift.$4);
}

// TermParse.{muParser_1525}

function TermParse___123_muParser_95_1525_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TermParse__chooseParser(null, $_1_lift, null, $_0_lift, new $HC_2_1$TermParse___58__58_(TermParse__muParser(null, $_1_lift, null, $_0_lift, $_2_lift), $_2_lift)))($_5_lift)(Prelude__Nat__lteTransitive(null, null, null, $_6_lift, null));
}

// TermParse.{muParser_1526}

function TermParse___123_muParser_95_1526_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), null, null, TParsec__Combinators__Chars__string(null, $partial_0_2$TermParse___123_chooseParser_95_25_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_1$TermParse___123_chooseParser_95_43_125_(), $partial_0_3$TermParse___123_chooseParser_95_48_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$TermParse___123_chooseParser_95_23_125_(), $partial_0_2$TermParse___123_chooseParser_95_32_125_(), $partial_0_4$TermParse___123_chooseParser_95_37_125_()), $partial_0_4$TermParse___123_chooseParser_95_65_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "inn", null, $_0_lift), $partial_3_7$TermParse___123_muParser_95_1525_125_($_0_lift, $_1_lift, $_2_lift))($_5_lift)(Prelude__Nat__lteTransitive(null, null, null, $_6_lift, null));
}

// TParsec.Combinators.{nelist_1527}

function TParsec__Combinators___123_nelist_95_1527_125_($_0_lift){
    
    return Data__NEList__consopt(null, $_0_lift.$1, $_0_lift.$2);
}

// TParsec.Combinators.{nelist_1528}

function TParsec__Combinators___123_nelist_95_1528_125_($_0_lift, $_1_lift, $_2_lift){
    return $_0_lift($_1_lift)(Prelude__Nat__lteTransitive(null, null, null, $_2_lift, null));
}

// TParsec.Combinators.{nelist_1529}

function TParsec__Combinators___123_nelist_95_1529_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return $_0_lift($_3_lift)($_4_lift)($partial_1_3$TParsec__Combinators___123_nelist_95_1528_125_($_1_lift));
}

// TParsec.Combinators.{nelist_1530}

function TParsec__Combinators___123_nelist_95_1530_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    var $cg$1 = null;
    const $cg$3 = $_0_lift.$1;
    $cg$1 = $cg$3.$1;
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $cg$1, $partial_0_1$TParsec__Combinators___123_nelist_95_1527_125_(), null, $partial_9_12$TParsec__Combinators__andoptbind(null, null, null, null, $_0_lift, $_1_lift, null, $_4_lift, $partial_2_5$TParsec__Combinators___123_nelist_95_1529_125_($_3_lift, $_4_lift)));
}

// TParsec.Combinators.{optand_1531}

function TParsec__Combinators___123_optand_95_1531_125_($_0_lift){
    return new $HC_1_1$Prelude__Maybe__Just($_0_lift);
}

// TParsec.Combinators.{optand_1533}

function TParsec__Combinators___123_optand_95_1533_125_($_0_lift){
    return new $HC_2_0$Builtins__MkPair($HC_0_0$Prelude__Maybe__Nothing, $_0_lift);
}

// TParsec.Combinators.Chars.{parens_1534}

function TParsec__Combinators__Chars___123_parens_95_1534_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift, $_10_lift){
    return TParsec__Combinators__Chars__char(null, $_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, ")")($_6_lift)($_9_lift)(Prelude__Nat__lteTransitive(null, null, null, $_10_lift, null));
}

// TParsec.Running.{parseMaybe_1535}

function TParsec__Running___123_parseMaybe_95_1535_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0(null, null, $_2_lift, $_3_lift);
}

// TParsec.Running.{parseMaybe_1536}

function TParsec__Running___123_parseMaybe_95_1536_125_($_0_lift, $_1_lift){
    return new $HC_1_1$Prelude__Maybe__Just($_1_lift);
}

// TParsec.Running.{parseMaybe_1537}

function TParsec__Running___123_parseMaybe_95_1537_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Applicative__Prelude___64_Prelude__Applicative__Applicative_36_Maybe_58__33__60__42__62__58_0(null, null, $_2_lift, $_3_lift);
}

// TParsec.Running.{parseMaybe_1538}

function TParsec__Running___123_parseMaybe_95_1538_125_($_0_lift){
    
    return $_0_lift.$1;
}

// TParsec.Running.{parseMaybe_1539}

function TParsec__Running___123_parseMaybe_95_1539_125_($_0_lift){
    var $cg$1 = null;
    $cg$1 = $_0_lift.$2;
    return Prelude__Maybe__toMaybe(null, Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0($cg$1, (new $JSRTS.jsbn.BigInteger(("0")))), new $JSRTS.Lazy((function(){
        return (function(){
            return TParsec__Running___123_parseMaybe_95_1538_125_($_0_lift);
        })();
    })));
}

// Parse.{parseTDef_1540}

function Parse___123_parseTDef_95_1540_125_($_0_lift, $_1_lift){
    return TParsec__Running__Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0(null, $_1_lift);
}

// Parse.{parseTDef_1541}

function Parse___123_parseTDef_95_1541_125_($_0_lift, $_1_lift){
    return TParsec__Running__TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0(null, null, null, null, $partial_0_2$Parse___123_parseTDef_95_1540_125_(), $_1_lift);
}

// Parse.{parseTDef_1542}

function Parse___123_parseTDef_95_1542_125_($_0_lift){
    var $cg$1 = null;
    if((((($_0_lift == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    if(($cg$3.type === 1)) {
        return $HC_0_0$Prelude__List__Nil;
    } else {
        var $cg$4 = null;
        if((((($_0_lift.slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$4 = true;
        } else {
            $cg$4 = false;
        }
        
        const $cg$6 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$4, true);
        var $cg$5 = null;
        if(($cg$6.type === 1)) {
            $cg$5 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$5 = new $HC_2_1$Prelude__Strings__StrCons($_0_lift.slice(1)[0], $_0_lift.slice(1).slice(1));
        }
        
        return new $HC_2_1$Prelude__List___58__58_($_0_lift[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$5));
    }
}

// TParsec.Combinators.{rand_1544}

function TParsec__Combinators___123_rand_95_1544_125_($_0_lift){
    
    return $_0_lift.$2;
}

// TParsec.Combinators.{randbindm_1546}

function TParsec__Combinators___123_randbindm_95_1546_125_($_0_lift){
    
    return $_0_lift.$2;
}

// Backend.Haskell.{renderApp_1547}

function Backend__Haskell___123_renderApp_95_1547_125_($_0_lift, $_1_lift){
    return new $HC_2_4$Text__PrettyPrint__WL__Core__Cat($_0_lift, new $HC_2_4$Text__PrettyPrint__WL__Core__Cat(Text__PrettyPrint__WL__Core__char(" "), $_1_lift));
}

// Backend.Haskell.{renderDef_1550}

function Backend__Haskell___123_renderDef_95_1550_125_($_0_lift){
    var $cg$1 = null;
    if((((($_0_lift == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    var $cg$2 = null;
    if(($cg$3.type === 1)) {
        $cg$2 = "";
    } else {
        var $cg$4 = null;
        if(Prelude__Chars__isUpper($_0_lift[0])) {
            $cg$4 = String.fromCharCode(((($_0_lift[0]).charCodeAt(0)|0) + 32));
        } else {
            $cg$4 = $_0_lift[0];
        }
        
        $cg$2 = (($cg$4)+($_0_lift.slice(1)));
    }
    
    return Text__PrettyPrint__WL__Core__text($cg$2);
}

// Backend.Haskell.{renderDef_1554}

function Backend__Haskell___123_renderDef_95_1554_125_($_0_lift){
    var $cg$1 = null;
    if((((($_0_lift == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    const $cg$3 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true);
    var $cg$2 = null;
    if(($cg$3.type === 1)) {
        $cg$2 = "";
    } else {
        var $cg$4 = null;
        if(Prelude__Chars__isUpper($_0_lift[0])) {
            $cg$4 = String.fromCharCode(((($_0_lift[0]).charCodeAt(0)|0) + 32));
        } else {
            $cg$4 = $_0_lift[0];
        }
        
        $cg$2 = (($cg$4)+($_0_lift.slice(1)));
    }
    
    return Text__PrettyPrint__WL__Core__text($cg$2);
}

// TParsec.Combinators.Chars.{string_1559}

function TParsec__Combinators__Chars___123_string_95_1559_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift){
    return TParsec__Combinators__Chars__char(null, $_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_7_lift)($_6_lift);
}

// TParsec.Combinators.{sum_1560}

function TParsec__Combinators___123_sum_95_1560_125_($_0_lift){
    return new $HC_1_0$Prelude__Either__Left($_0_lift);
}

// TParsec.Combinators.{sum_1561}

function TParsec__Combinators___123_sum_95_1561_125_($_0_lift){
    return new $HC_1_1$Prelude__Either__Right($_0_lift);
}

// Parse.{tdef_1562}

function Parse___123_tdef_95_1562_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_0$Builtins__MkPair(new $HC_1_2$TParsec__Result__Value(new $HC_2_0$Builtins__MkPair($HC_0_0$MkUnit, $_1_lift)), $_2_lift);
}

// Parse.{tdef_1565}

function Parse___123_tdef_95_1565_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Functor__TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0(null, null, null, null, null, $partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $_2_lift, $_3_lift);
}

// Parse.{tdef_1578}

function Parse___123_tdef_95_1578_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $_2_lift, $_3_lift);
}

// Parse.{tdef_1579}

function Parse___123_tdef_95_1579_125_($_0_lift, $_1_lift){
    return $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), $_1_lift);
}

// Parse.{tdef_1593}

function Parse___123_tdef_95_1593_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0(null, null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), $_2_lift, $_3_lift);
}

// Parse.{tdef_1608}

function Parse___123_tdef_95_1608_125_($_0_lift){
    return $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33_empty_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), $partial_0_1$TermParse___123_chooseParser_95_20_125_());
}

// Parse.{tdef_1622}

function Parse___123_tdef_95_1622_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_8_9$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), null, $_1_lift, $_2_lift);
}

// Parse.{tdef_1667}

function Parse___123_tdef_95_1667_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Monad__TParsec__Types___64_Prelude__Monad__Monad_36_TParsecT_32_e_32_a_32_m_58__33__62__62__61__58_0(null, null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), $_2_lift, $_3_lift);
}

// Parse.{tdef_1836}

function Parse___123_tdef_95_1836_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$1;
    if(($cg$3.type === 0)) {
        return $HC_0_0$Prelude__Maybe__Nothing;
    } else {
        return Data__SortedMap__treeLookup(null, null, $cg$3.$1, null, $_0_lift.$2, $cg$3.$2);
    }
}

// Parse.{tdef_2009}

function Parse___123_tdef_95_2009_125_($_0_lift){
    return new $HC_2_0$Builtins__MkDPair((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Typedefs__T0);
}

// Parse.{tdef_2122}

function Parse___123_tdef_95_2122_125_($_0_lift){
    return new $HC_2_0$Builtins__MkDPair((new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_1$Typedefs__T1);
}

// Parse.{tdef_2232}

function Parse___123_tdef_95_2232_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_1_3$Typedefs__TProd($_2_lift);
}

// Parse.{tdef_2233}

function Parse___123_tdef_95_2233_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_1_2$Typedefs__TSum($_2_lift);
}

// Parse.{tdef_2237}

function Parse___123_tdef_95_2237_125_($_0_lift){
    return new $HC_2_0$Builtins__MkDPair($_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), new $HC_1_4$Typedefs__TVar(Data__Fin__last($_0_lift)));
}

// Parse.{tdef_2828}

function Parse___123_tdef_95_2828_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TParsec__Combinators__Numbers__decimalNat(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift))($_3_lift)(Prelude__Nat__lteTransitive(null, null, null, $_4_lift, null));
}

// Parse.{tdef_2829}

function Parse___123_tdef_95_2829_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, null, TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TParsec__Combinators__Chars__string(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "var", null, $_0_lift)), $partial_1_5$Parse___123_tdef_95_2828_125_($_0_lift))($_3_lift)(Prelude__Nat__lteTransitive(null, null, null, $_4_lift, null));
}

// Parse.{tdef_2980}

function Parse___123_tdef_95_2980_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$2;
    return new $HC_2_0$Builtins__MkDPair($cg$3.$1, new $HC_2_0$Builtins__MkPair($_0_lift.$1, $cg$3.$2));
}

// Parse.{tdef_2981}

function Parse___123_tdef_95_2981_125_($_0_lift, $_1_lift){
    
    const $cg$3 = $_1_lift.$2;
    const $cg$5 = $cg$3.$2;
    return new $HC_2_0$Builtins__MkPair($cg$5.$1, Typedefs__weakenTDef(null, $cg$5.$2, $_0_lift.add((new $JSRTS.jsbn.BigInteger(("1")))), $cg$3.$1));
}

// Parse.{tdef_2982}

function Parse___123_tdef_95_2982_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$2;
    var $cg$2 = null;
    $cg$2 = new $HC_2_1$Data__Vect___58__58_($cg$3.$1, Data__Vect__fromList(null, $cg$3.$2));
    const $_7459_in = Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Parse___123_tdef_95_2980_125_(), $cg$2);
    const $cg$5 = Parse__toVMax(null, null, $_7459_in);
    
    if($cg$5.$1.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__Maybe__Nothing;
    } else {
        const $_7469_in = $cg$5.$1.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_1_1$Prelude__Maybe__Just(new $HC_2_0$Builtins__MkPair($_0_lift.$1, new $HC_2_0$Builtins__MkDPair($_7469_in, new $HC_2_5$Typedefs__TMu($_0_lift.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$Parse___123_tdef_95_2981_125_($_7469_in), Parse__fromVMax_58_go_58_0(null, $_7469_in.add((new $JSRTS.jsbn.BigInteger(("1")))), null, null, null, null, Prelude__Nat__lteRefl($_7469_in.add((new $JSRTS.jsbn.BigInteger(("1"))))), $cg$5.$2))))));
    }
}

// Parse.{tdef_4206}

function Parse___123_tdef_95_4206_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift){
    return $_0_lift($_1_lift)($_2_lift)($_6_lift)(Prelude__Nat__lteTransitive(null, null, null, $_7_lift, null));
}

// Parse.{tdef_4207}

function Parse___123_tdef_95_4207_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return $partial_10_11$TParsec__Combinators__andbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TParsec__Combinators__Chars__alphas(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift)), $partial_3_8$Parse___123_tdef_95_4206_125_($_1_lift, $_0_lift, $_2_lift), $_5_lift, Prelude__Nat__lteTransitive(null, null, null, $_6_lift, null));
}

// Parse.{tdef_4208}

function Parse___123_tdef_95_4208_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return TParsec__Combinators__nelist(null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $_2_lift)(TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_2_lift, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_2_lift, $partial_3_7$Parse___123_tdef_95_4207_125_($_2_lift, $_0_lift, $_3_lift))));
}

// Parse.{tdef_4209}

function Parse___123_tdef_95_4209_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return $partial_10_11$TParsec__Combinators__andbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TParsec__Combinators__Chars__alphas(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift)), $partial_1_4$Parse___123_tdef_95_4208_125_($_1_lift), $_4_lift, Prelude__Nat__lteTransitive(null, null, null, $_5_lift, null));
}

// Parse.{tdef_4210}

function Parse___123_tdef_95_4210_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, null, TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TParsec__Combinators__Chars__string(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "mu", null, $_0_lift)), $partial_2_6$Parse___123_tdef_95_4209_125_($_0_lift, $_1_lift))($_4_lift)(Prelude__Nat__lteTransitive(null, null, null, $_5_lift, null));
}

// Parse.{tdef_4245}

function Parse___123_tdef_95_4245_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_2_0$Builtins__MkPair($HC_0_0$MkUnit, Data__SortedMap__insert(null, null, $_0_lift, $_1_lift, $_2_lift));
}

// Parse.{tdef_4259}

function Parse___123_tdef_95_4259_125_($_0_lift){
    
    return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0(null, null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), Prelude__Functor__TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0(null, null, null, null, null, $partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), Control__Monad__Trans__TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $partial_0_1$Backend__Haskell___123_makeDefs_95_1279_125_(), $partial_2_4$Parse___123_tdef_95_4245_125_($_0_lift.$1, $_0_lift.$2)))), $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), $_0_lift.$2));
}

// Parse.{tdef_5050}

function Parse___123_tdef_95_5050_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_2_lift, $_0_lift($_2_lift)($_3_lift));
}

// Parse.{tdef_5051}

function Parse___123_tdef_95_5051_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return $partial_10_11$TParsec__Combinators__andbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TParsec__Combinators__Chars__alphas(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift)), $partial_1_4$Parse___123_tdef_95_5050_125_($_1_lift), $_4_lift, Prelude__Nat__lteTransitive(null, null, null, $_5_lift, null));
}

// Parse.{tdef_5052}

function Parse___123_tdef_95_5052_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, null, TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TParsec__Combinators__Chars__string(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "name", null, $_0_lift)), $partial_2_6$Parse___123_tdef_95_5051_125_($_0_lift, $_1_lift))($_4_lift)(Prelude__Nat__lteTransitive(null, null, null, $_5_lift, null));
}

// Parse.{tdef_5087}

function Parse___123_tdef_95_5087_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_2_0$Builtins__MkPair($HC_0_0$MkUnit, Data__SortedMap__insert(null, null, $_0_lift, new $HC_2_0$Builtins__MkDPair($_1_lift, $_2_lift), $_3_lift));
}

// Parse.{tdef_5101}

function Parse___123_tdef_95_5101_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$2;
    return Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0(null, null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), Prelude__Functor__TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0(null, null, null, null, null, $partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), Control__Monad__Trans__TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_3$TermParse___123_chooseParser_95_16_125_(), $partial_0_2$TParsec__Combinators___123_anyTok_95_13_125_(), $partial_0_3$TermParse___123_chooseParser_95_16_125_()), $partial_0_4$TermParse___123_chooseParser_95_19_125_()), $partial_0_1$Backend__Haskell___123_makeDefs_95_1279_125_(), $partial_3_5$Parse___123_tdef_95_5087_125_($_0_lift.$1, $cg$3.$1, $cg$3.$2)))), $partial_6_7$Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), new $HC_2_0$Builtins__MkDPair($cg$3.$1, new $HC_2_6$Typedefs__TName($_0_lift.$1, $cg$3.$2))));
}

// Parse.{tdef_5102}

function Parse___123_tdef_95_5102_125_($_0_lift, $_1_lift){
    return TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TParsec__Combinators__alts(null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), null, new $HC_2_1$Prelude__List___58__58_($partial_9_12$TParsec__Combinators__guardM(null, null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$Parse___123_tdef_95_1836_125_(), null, $partial_8_11$TParsec__Combinators__mand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, Control__Monad__Trans__TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Backend__Haskell___123_makeDefs_95_1292_125_(), $partial_0_3$Backend__Haskell___123_makeDefs_95_1293_125_(), $partial_0_4$Backend__Haskell___123_makeDefs_95_1298_125_()), $partial_0_4$Parse___123_tdef_95_1578_125_()), $partial_0_1$Backend__Haskell___123_makeDefs_95_1279_125_()), TParsec__Combinators__Chars__alphas(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift))), new $HC_2_1$Prelude__List___58__58_($partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_1$Parse___123_tdef_95_2009_125_(), null, TParsec__Combinators__Chars__string(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "0", null, $_0_lift)), new $HC_2_1$Prelude__List___58__58_($partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_1$Parse___123_tdef_95_2122_125_(), null, TParsec__Combinators__Chars__string(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), "1", null, $_0_lift)), new $HC_2_1$Prelude__List___58__58_(Parse__tdef_58_nary_58_0(null, $_0_lift, $_1_lift, "*", $partial_0_3$Parse___123_tdef_95_2232_125_()), new $HC_2_1$Prelude__List___58__58_(Parse__tdef_58_nary_58_0(null, $_0_lift, $_1_lift, "+", $partial_0_3$Parse___123_tdef_95_2233_125_()), new $HC_2_1$Prelude__List___58__58_($partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_1$Parse___123_tdef_95_2237_125_(), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, $partial_1_5$Parse___123_tdef_95_2829_125_($_0_lift))), new $HC_2_1$Prelude__List___58__58_(TParsec__Combinators__randbindm(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, $partial_9_12$TParsec__Combinators__guardM(null, null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$Parse___123_tdef_95_2982_125_(), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, $partial_2_6$Parse___123_tdef_95_4210_125_($_0_lift, $_1_lift))), $partial_0_1$Parse___123_tdef_95_4259_125_()), new $HC_2_1$Prelude__List___58__58_(TParsec__Combinators__randbindm(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, $partial_2_6$Parse___123_tdef_95_5052_125_($_0_lift, $_1_lift)), $partial_0_1$Parse___123_tdef_95_5101_125_()), $HC_0_0$Prelude__List__Nil))))))))));
}

// Parse.{tdefRec_5106}

function Parse___123_tdefRec_95_5106_125_($_0_lift){
    
    const $cg$3 = $_0_lift.$2;
    if(($cg$3.type === 1)) {
        return $cg$3.$1;
    } else {
        return $_0_lift.$1;
    }
}

// Parse.{tdefRec_5213}

function Parse___123_tdefRec_95_5213_125_($_0_lift, $_1_lift){
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_1$Parse___123_tdefRec_95_5106_125_(), null, $partial_9_12$TParsec__Combinators__andoptbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), null, Parse__tdef($_0_lift), $partial_1_2$TParsec__Combinators__Numbers___123_decimalDigit_95_1210_125_($_1_lift)));
}

// Text.PrettyPrint.WL.Core.{toString_5214}

function Text__PrettyPrint__WL__Core___123_toString_95_5214_125_($_0_lift){
    return $HC_0_0$Text__PrettyPrint__WL__Core__PrettyDoc__Empty;
}

// Backend.Utils.{unindex_5215}

function Backend__Utils___123_unindex_95_5215_125_($_0_lift, $_1_lift){
    return $_0_lift(new $HC_1_1$Data__Fin__FS($_1_lift));
}

// TParsec.Combinators.Chars.{withSpaces_5216}

function TParsec__Combinators__Chars___123_withSpaces_95_5216_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift, $_8_lift, $_9_lift, $_10_lift){
    return TParsec__Combinators__nelist(null, null, null, $_0_lift, $_1_lift, $_2_lift)(TParsec__Combinators__Chars__space(null, $_3_lift, $_0_lift, $_1_lift, $_4_lift, $_5_lift, $_6_lift, null))($_9_lift)(Prelude__Nat__lteTransitive(null, null, null, $_10_lift, null));
}

// Prelude.Applicative.{TParsec.Types.@Prelude.Applicative.Alternative$TParsecT e a m:!<|>:0_lam_5970}

function Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0_95_lam_95_5970_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    if(($_3_lift.type === 1)) {
        return $_0_lift($_1_lift);
    } else {
        
        const $cg$4 = $_2_lift.$1;
        return $cg$4.$2(null)($_3_lift);
    }
}

// Prelude.Applicative.{TParsec.Result.@Prelude.Applicative.Applicative$ResultT e m:!<*>:0_lam_5971}

function Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5971_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    return $cg$3.$2(null)(Prelude__Applicative__TParsec__Result___64_Prelude__Applicative__Applicative_36_Result_32_e_58__33__60__42__62__58_0(null, null, null, $_1_lift, $_2_lift));
}

// Prelude.Applicative.{TParsec.Result.@Prelude.Applicative.Applicative$ResultT e m:!<*>:0_lam_5972}

function Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5972_125_($_0_lift, $_1_lift, $_2_lift){
    
    return $_0_lift.$2(null)(null)($_1_lift)($partial_2_3$Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5971_125_($_0_lift, $_2_lift));
}

// Prelude.Applicative.{Control.Monad.State.@Prelude.Applicative.Applicative$StateT stateType f:!<*>:0_lam_5973}

function Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5973_125_($_0_lift, $_1_lift, $_2_lift){
    
    
    const $cg$4 = $_0_lift.$1;
    return $cg$4.$2(null)(new $HC_2_0$Builtins__MkPair($_1_lift($_2_lift.$1), $_2_lift.$2));
}

// Prelude.Applicative.{Control.Monad.State.@Prelude.Applicative.Applicative$StateT stateType f:!<*>:0_lam_5974}

function Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5974_125_($_0_lift, $_1_lift, $_2_lift){
    
    
    return $_0_lift.$2(null)(null)($_1_lift($_2_lift.$2))($partial_2_3$Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5973_125_($_0_lift, $_2_lift.$1));
}

// Prelude.Applicative.{TParsec.Types.@Prelude.Applicative.Applicative$TParsecT e a m:!<*>:0_lam_5975}

function Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5975_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    var $cg$1 = null;
    const $cg$3 = $_0_lift.$1;
    $cg$1 = $cg$3.$1;
    return Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0(null, null, null, null, $cg$1, $_3_lift, $_4_lift);
}

// Prelude.Applicative.{TParsec.Types.@Prelude.Applicative.Applicative$TParsecT e a m:!<*>:0_lam_5976}

function Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5976_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    return $cg$3.$2(null)(new $HC_1_2$TParsec__Result__Value($_2_lift));
}

// Prelude.Applicative.{TParsec.Types.@Prelude.Applicative.Applicative$TParsecT e a m:!<*>:0_lam_5977}

function Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5977_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return Prelude__Applicative__TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0(null, null, null, null, $_0_lift, $_3_lift, $_4_lift);
}

// Prelude.Applicative.{TParsec.Types.@Prelude.Applicative.Applicative$TParsecT e a m:!<*>:0_lam_5978}

function Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5978_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return Prelude__Monad__TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0(null, null, null, null, $_0_lift, $_3_lift, $_4_lift);
}

// Prelude.Functor.{TParsec.Result.@Prelude.Functor.Functor$ResultT e m:!map:0_lam_5979}

function Prelude__Functor___123_TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0_95_lam_95_5979_125_($_0_lift, $_1_lift){
    return Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_Result_32_e_58__33_map_58_0(null, null, null, $_0_lift, $_1_lift);
}

// Prelude.Functor.{Control.Monad.State.@Prelude.Functor.Functor$StateT stateType f:!map:0_lam_5980}

function Prelude__Functor___123_Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0_95_lam_95_5980_125_($_0_lift, $_1_lift){
    
    return new $HC_2_0$Builtins__MkPair($_0_lift($_1_lift.$1), $_1_lift.$2);
}

// Prelude.Functor.{TParsec.Types.@Prelude.Functor.Functor$TParsecT e a m:!map:0_lam_5981}

function Prelude__Functor___123_TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0_95_lam_95_5981_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0(null, null, null, null, $_0_lift, $_3_lift, $_4_lift);
}

// Prelude.Monad.{TParsec.Result.@Prelude.Monad.Monad$ResultT e m:!>>=:0_lam_5982}

function Prelude__Monad___123_TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0_95_lam_95_5982_125_($_0_lift, $_1_lift, $_2_lift){
    
    if(($_2_lift.type === 0)) {
        
        const $cg$7 = $_0_lift.$1;
        return $cg$7.$2(null)(new $HC_1_0$TParsec__Result__HardFail($_2_lift.$1));
    } else if(($_2_lift.type === 1)) {
        
        const $cg$4 = $_0_lift.$1;
        return $cg$4.$2(null)(new $HC_1_1$TParsec__Result__SoftFail($_2_lift.$1));
    } else {
        return $_1_lift($_2_lift.$1);
    }
}

// Prelude.Monad.{Control.Monad.State.@Prelude.Monad.Monad$StateT stateType m:!>>=:0_lam_5983}

function Prelude__Monad___123_Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0_95_lam_95_5983_125_($_0_lift, $_1_lift){
    
    return $_0_lift($_1_lift.$1)($_1_lift.$2);
}

// TParsec.Running.{TParsec.Running.@TParsec.Running.MonadRun$ResultT e m:!runMonad:0_lam_5988}

function TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0_95_lam_95_5988_125_($_0_lift, $_1_lift){
    var $cg$1 = null;
    if(($_0_lift.type === 0)) {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    } else if(($_0_lift.type === 1)) {
        $cg$1 = $HC_0_0$Prelude__List__Nil;
    } else {
        $cg$1 = new $HC_2_1$Prelude__List___58__58_($_0_lift.$1, $HC_0_0$Prelude__List__Nil);
    }
    
    return Prelude__List___43__43_(null, $cg$1, $_1_lift);
}

// TParsec.Running.{Parse.@TParsec.Running.MonadRun$StateT PState Identity:!runMonad:0_lam_5990}

function TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5990_125_($_0_lift, $_1_lift){
    return Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_lift, $_1_lift);
}

// TParsec.Running.{Parse.@TParsec.Running.MonadRun$StateT PState Identity:!runMonad:0_lam_5991}

function TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5991_125_($_0_lift, $_1_lift){
    
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_lift, $_1_lift) < 0)) {
        return true;
    } else {
        return ($_0_lift == $_1_lift);
    }
}

// TParsec.Running.{TParsec.Running.@TParsec.Running.MonadRun$TParsecT e a m:!runMonad:0_lam_5992}

function TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0_95_lam_95_5992_125_($_0_lift){
    
    return $_0_lift.$1;
}

// Control.Monad.Trans.{TParsec.Result.@Control.Monad.Trans.MonadTrans$ResultT e:!lift:0_lam_5993}

function Control__Monad__Trans___123_TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0_95_lam_95_5993_125_($_0_lift){
    return new $HC_1_2$TParsec__Result__Value($_0_lift);
}

// Control.Monad.Trans.{Control.Monad.State.@Control.Monad.Trans.MonadTrans$StateT stateType:!lift:0_lam_5994}

function Control__Monad__Trans___123_Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0_95_lam_95_5994_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    return $cg$3.$2(null)(new $HC_2_0$Builtins__MkPair($_2_lift, $_1_lift));
}

// Control.Monad.Trans.{TParsec.Types.@Control.Monad.Trans.MonadTrans$TParsecT e a:!lift:0_lam_5995}

function Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5995_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    var $cg$1 = null;
    const $cg$3 = $_0_lift.$1;
    $cg$1 = $cg$3.$1;
    return Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0(null, null, null, null, $cg$1, $_3_lift, $_4_lift);
}

// Control.Monad.Trans.{TParsec.Types.@Control.Monad.Trans.MonadTrans$TParsecT e a:!lift:0_lam_5996}

function Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5996_125_($_0_lift, $_1_lift, $_2_lift){
    
    const $cg$3 = $_0_lift.$1;
    return $cg$3.$2(null)(new $HC_1_2$TParsec__Result__Value($_2_lift));
}

// Prelude.Traversable.{Data.Vect.@Prelude.Traversable.Traversable$Vect n:!traverse:0_lam_6000}

function Prelude__Traversable___123_Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0_95_lam_95_6000_125_($_0_lift, $_1_lift){
    return new $HC_2_1$Data__Vect___58__58_($_0_lift, $_1_lift);
}

// Prelude.Applicative.TParsec.Types.TParsecT e a m implementation of Prelude.Applicative.Alternative, method <|>

function Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_pos){
    
    return $_4_arg.$2(null)(null)($_6_arg($_8_pos))($partial_3_4$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33__60__124__62__58_0_95_lam_95_5970_125_($_7_arg, $_8_pos, $_4_arg));
}

// Prelude.Applicative.TParsec.Types.TParsecT e a m implementation of Prelude.Applicative.Alternative, method empty

function Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Alternative_36_TParsecT_32_e_32_a_32_m_58__33_empty_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_22_in){
    
    const $cg$3 = $_4_arg.$1;
    return $cg$3.$2(null)(new $HC_1_1$TParsec__Result__SoftFail($_5_arg($_22_in)));
}

// Prelude.Applicative.Prelude.Maybe implementation of Prelude.Applicative.Applicative, method <*>

function Prelude__Applicative__Prelude___64_Prelude__Applicative__Applicative_36_Maybe_58__33__60__42__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        
        if(($_2_arg.type === 1)) {
            return new $HC_1_1$Prelude__Maybe__Just($_2_arg.$1($_3_arg.$1));
        } else {
            return $HC_0_0$Prelude__Maybe__Nothing;
        }
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Prelude.Applicative.TParsec.Result.Result e implementation of Prelude.Applicative.Applicative, method <*>

function Prelude__Applicative__TParsec__Result___64_Prelude__Applicative__Applicative_36_Result_32_e_58__33__60__42__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_3_arg.type === 0)) {
        return $_3_arg;
    } else if(($_3_arg.type === 1)) {
        return $_3_arg;
    } else {
        
        if(($_4_arg.type === 0)) {
            return $_4_arg;
        } else if(($_4_arg.type === 1)) {
            return $_4_arg;
        } else {
            
            return new $HC_1_2$TParsec__Result__Value($_3_arg.$1($_4_arg.$1));
        }
    }
}

// Prelude.Applicative.TParsec.Result.ResultT e m implementation of Prelude.Applicative.Applicative, method <*>

function Prelude__Applicative__TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    return $_4_arg.$2(null)(null)($_5_arg)($partial_2_3$Prelude__Applicative___123_TParsec__Result___64_Prelude__Applicative__Applicative_36_ResultT_32_e_32_m_58__33__60__42__62__58_0_95_lam_95_5972_125_($_4_arg, $_6_arg));
}

// Prelude.Applicative.Control.Monad.State.StateT stateType f implementation of Prelude.Applicative.Applicative, method <*>

function Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_st){
    
    return $_4_arg.$2(null)(null)($_5_arg($_7_st))($partial_2_3$Prelude__Applicative___123_Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0_95_lam_95_5974_125_($_4_arg, $_6_arg));
}

// Prelude.Applicative.TParsec.Types.TParsecT e a m implementation of Prelude.Applicative.Applicative, method <*>

function Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_7_8$Prelude__Applicative__Control__Monad__State___64_Prelude__Applicative__Applicative_36_StateT_32_stateType_32_f_58__33__60__42__62__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5975_125_($_5_arg), $partial_1_3$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5976_125_($_5_arg), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5977_125_($_5_arg)), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5978_125_($_5_arg)), $_6_arg, $_7_arg);
}

// Prelude.Applicative.TParsec.Types.TParsecT e a m implementation of Prelude.Applicative.Applicative, method pure

function Prelude__Applicative__TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33_pure_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_st){
    
    const $cg$3 = $_4_arg.$1;
    return $cg$3.$2(null)(new $HC_1_2$TParsec__Result__Value(new $HC_2_0$Builtins__MkPair($_5_arg, $_6_st)));
}

// Decidable.Equality.Decidable.Equality.Bool implementation of Decidable.Equality.DecEq, method decEq

function Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($_0_arg, $_1_arg){
    
    if($_1_arg) {
        
        if($_0_arg) {
            return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
        } else {
            return $HC_0_1$Prelude__Basics__No;
        }
    } else {
        
        if($_0_arg) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            return new $HC_1_0$Prelude__Basics__Yes($HC_0_0$Refl);
        }
    }
}

// Prelude.Interfaces.Prelude.Nat.Nat implementation of Prelude.Interfaces.Eq, method ==

function Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0($_0_arg, $_1_arg){
    for(;;) {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            
            if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return true;
            } else {
                return false;
            }
        } else {
            const $_2_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            
            if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return false;
            } else {
                const $_3_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                $_0_arg = $_3_in;
                $_1_arg = $_2_in;
            }
        }
    }
}

// Prelude.Foldable.Prelude.List.List implementation of Prelude.Foldable.Foldable, method foldl

function Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    var $tco$$_3_arg = $_3_arg;
    for(;;) {
        
        if(($_4_arg.type === 1)) {
            $tco$$_3_arg = $_2_arg($_3_arg)($_4_arg.$1);
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = $_2_arg;
            $_3_arg = $tco$$_3_arg;
            $_4_arg = $_4_arg.$2;
        } else {
            return $_3_arg;
        }
    }
}

// Prelude.Foldable.Prelude.List.List implementation of Prelude.Foldable.Foldable, method foldr

function Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 1)) {
        return $_2_arg($_4_arg.$1)(Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $_2_arg, $_3_arg, $_4_arg.$2));
    } else {
        return $_3_arg;
    }
}

// Prelude.Foldable.Prelude.Maybe.Maybe implementation of Prelude.Foldable.Foldable, method foldr

function Prelude__Foldable__Prelude__Maybe___64_Prelude__Foldable__Foldable_36_Maybe_58__33_foldr_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 1)) {
        return $_2_arg($_4_arg.$1)($_3_arg);
    } else {
        return $_3_arg;
    }
}

// Prelude.Functor.Prelude.List.List implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        return new $HC_2_1$Prelude__List___58__58_($_2_arg($_3_arg.$1), Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_2_arg, $_3_arg.$2));
    } else {
        return $_3_arg;
    }
}

// Prelude.Functor.Prelude.Maybe implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__Prelude___64_Prelude__Functor__Functor_36_Maybe_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        return new $HC_1_1$Prelude__Maybe__Just($_2_arg($_3_arg.$1));
    } else {
        return $_3_arg;
    }
}

// Prelude.Functor.TParsec.Result.Result e implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_Result_32_e_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 0)) {
        return $_4_arg;
    } else if(($_4_arg.type === 1)) {
        return $_4_arg;
    } else {
        return new $HC_1_2$TParsec__Result__Value($_3_arg($_4_arg.$1));
    }
}

// Prelude.Functor.TParsec.Result.ResultT e m implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    return $_4_arg(null)(null)($partial_1_2$Prelude__Functor___123_TParsec__Result___64_Prelude__Functor__Functor_36_ResultT_32_e_32_m_58__33_map_58_0_95_lam_95_5979_125_($_5_arg))($_6_arg);
}

// Prelude.Functor.Control.Monad.State.StateT stateType f implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_st){
    return $_4_arg(null)(null)($partial_1_2$Prelude__Functor___123_Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0_95_lam_95_5980_125_($_5_arg))($_6_arg($_7_st));
}

// Prelude.Functor.TParsec.Types.TParsecT e a m implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_7_8$Prelude__Functor__Control__Monad__State___64_Prelude__Functor__Functor_36_StateT_32_stateType_32_f_58__33_map_58_0(null, null, null, null, $partial_1_5$Prelude__Functor___123_TParsec__Types___64_Prelude__Functor__Functor_36_TParsecT_32_e_32_a_32_m_58__33_map_58_0_95_lam_95_5981_125_($_5_arg), $_6_arg, $_7_arg);
}

// Prelude.Functor.Data.Vect.Vect n implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 1)) {
        return new $HC_2_1$Data__Vect___58__58_($_3_arg($_4_arg.$1), Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $_3_arg, $_4_arg.$2));
    } else {
        return $_4_arg;
    }
}

// Prelude.Monad.TParsec.Result.ResultT e m implementation of Prelude.Monad.Monad, method >>=

function Prelude__Monad__TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    return $_4_arg.$2(null)(null)($_5_arg)($partial_2_3$Prelude__Monad___123_TParsec__Result___64_Prelude__Monad__Monad_36_ResultT_32_e_32_m_58__33__62__62__61__58_0_95_lam_95_5982_125_($_4_arg, $_6_arg));
}

// Prelude.Monad.Control.Monad.State.StateT stateType m implementation of Prelude.Monad.Monad, method >>=

function Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_st){
    
    return $_4_arg.$2(null)(null)($_5_arg($_7_st))($partial_1_2$Prelude__Monad___123_Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0_95_lam_95_5983_125_($_6_arg));
}

// Prelude.Monad.TParsec.Types.TParsecT e a m implementation of Prelude.Monad.Monad, method >>=

function Prelude__Monad__TParsec__Types___64_Prelude__Monad__Monad_36_TParsecT_32_e_32_a_32_m_58__33__62__62__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    return $partial_7_8$Prelude__Monad__Control__Monad__State___64_Prelude__Monad__Monad_36_StateT_32_stateType_32_m_58__33__62__62__61__58_0(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5975_125_($_5_arg), $partial_1_3$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5976_125_($_5_arg), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5977_125_($_5_arg)), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5978_125_($_5_arg)), $_6_arg, $_7_arg);
}

// TParsec.Running.TParsec.Running.ResultT e m implementation of TParsec.Running.MonadRun, method runMonad

function TParsec__Running__TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0_95_lam_95_5988_125_(), $HC_0_0$Prelude__List__Nil, $_3_arg(null)($_4_arg));
}

// TParsec.Running.Parse.StateT PState Identity implementation of TParsec.Running.MonadRun, method runMonad

function TParsec__Running__Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0($_0_arg, $_1_arg){
    return new $HC_2_1$Prelude__List___58__58_(Control__Monad__State__evalState(null, null, $_1_arg, new $HC_1_0$Data__SortedMap__Empty(new $HC_3_0$Prelude__Interfaces__Ord_95_ictor($partial_0_2$Backend__Haskell___123_makeDefs_95_1310_125_(), $partial_0_2$TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5990_125_(), $partial_0_2$TParsec__Running___123_Parse___64_TParsec__Running__MonadRun_36_StateT_32_PState_32_Identity_58__33_runMonad_58_0_95_lam_95_5991_125_()))), $HC_0_0$Prelude__List__Nil);
}

// TParsec.Running.TParsec.Running.TParsecT e a m implementation of TParsec.Running.MonadRun, method runMonad

function TParsec__Running__TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    return Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$TParsec__Running___123_TParsec__Running___64_TParsec__Running__MonadRun_36_TParsecT_32_e_32_a_32_m_58__33_runMonad_58_0_95_lam_95_5992_125_(), TParsec__Running__TParsec__Running___64_TParsec__Running__MonadRun_36_ResultT_32_e_32_m_58__33_runMonad_58_0(null, null, null, $_4_arg, $_5_arg(new $HC_2_0$Builtins__MkPair($HC_0_0$TParsec__Types__MkPosition, $HC_0_0$Prelude__List__Nil))));
}

// Control.Monad.Trans.TParsec.Result.ResultT e implementation of Control.Monad.Trans.MonadTrans, method lift

function Control__Monad__Trans__TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_18_in){
    
    const $cg$3 = $_3_arg.$1;
    return $cg$3.$1(null)(null)($partial_0_1$Control__Monad__Trans___123_TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0_95_lam_95_5993_125_())($_18_in);
}

// Control.Monad.Trans.Control.Monad.State.StateT stateType implementation of Control.Monad.Trans.MonadTrans, method lift

function Control__Monad__Trans__Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_st){
    
    return $_3_arg.$2(null)(null)($_4_arg)($partial_2_3$Control__Monad__Trans___123_Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0_95_lam_95_5994_125_($_3_arg, $_5_st));
}

// Control.Monad.Trans.TParsec.Types.TParsecT e a implementation of Control.Monad.Trans.MonadTrans, method lift

function Control__Monad__Trans__TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_61_in){
    return $partial_5_6$Control__Monad__Trans__Control__Monad__State___64_Control__Monad__Trans__MonadTrans_36_StateT_32_stateType_58__33_lift_58_0(null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_1_5$Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5995_125_($_4_arg), $partial_1_3$Control__Monad__Trans___123_TParsec__Types___64_Control__Monad__Trans__MonadTrans_36_TParsecT_32_e_32_a_58__33_lift_58_0_95_lam_95_5996_125_($_4_arg), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5977_125_($_4_arg)), $partial_1_5$Prelude__Applicative___123_TParsec__Types___64_Prelude__Applicative__Applicative_36_TParsecT_32_e_32_a_32_m_58__33__60__42__62__58_0_95_lam_95_5978_125_($_4_arg)), Control__Monad__Trans__TParsec__Result___64_Control__Monad__Trans__MonadTrans_36_ResultT_32_e_58__33_lift_58_0(null, null, null, $_4_arg, $_61_in));
}

// Prelude.Interfaces.Prelude.Interfaces.Char implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg === $_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg < $_1_arg)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Interfaces.Prelude.Interfaces.Int implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg === $_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg < $_1_arg)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Interfaces.Prelude.Interfaces.Integer implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if(((($_0_arg.equals($_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if(((((($_0_arg).compareTo(($_1_arg)) < 0)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Interfaces.Prelude.Interfaces.String implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg == $_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg < $_1_arg)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Traversable.Prelude.List implementation of Prelude.Traversable.Traversable, method traverse

function Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        
        var $cg$4 = null;
        var $cg$5 = null;
        $cg$5 = $_3_arg.$2(null)($partial_0_2$Backend__Haskell___123_makeDefs_95_1300_125_());
        $cg$4 = $_3_arg.$3(null)(null)($cg$5)($_4_arg($_5_arg.$1));
        return $_3_arg.$3(null)(null)($cg$4)(Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0(null, null, null, $_3_arg, $_4_arg, $_5_arg.$2));
    } else {
        
        return $_3_arg.$2(null)($HC_0_0$Prelude__List__Nil);
    }
}

// Prelude.Traversable.Data.Vect.Vect n implementation of Prelude.Traversable.Traversable, method traverse

function Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if(($_6_arg.type === 1)) {
        
        var $cg$4 = null;
        var $cg$5 = null;
        $cg$5 = $_4_arg.$2(null)($partial_0_2$Prelude__Traversable___123_Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0_95_lam_95_6000_125_());
        $cg$4 = $_4_arg.$3(null)(null)($cg$5)($_5_arg($_6_arg.$1));
        return $_4_arg.$3(null)(null)($cg$4)(Prelude__Traversable__Data__Vect___64_Prelude__Traversable__Traversable_36_Vect_32_n_58__33_traverse_58_0(null, null, null, null, $_4_arg, $_5_arg, $_6_arg.$2));
    } else {
        
        return $_4_arg.$2(null)($HC_0_0$Data__Vect__Nil);
    }
}

// {runMain_0}

function $_0_runMain(){
    return $JSRTS.force(Main__main()($HC_0_0$TheWorld));
}

// {Induction.Nat.fixBox:go:0_lam_5217}

function $_5217_Induction__Nat__fixBox_58_go_58_0_95_lam($_0_lift){
    return null;
}

// {Induction.Nat.fixBox:go:0_lam_5218}

function $_5218_Induction__Nat__fixBox_58_go_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Induction__Nat__fixBox_58_go_58_0(null, $_0_lift, null, $_1_lift, $_2_lift)(Prelude__Nat__lteTransitive(null, null, null, $_3_lift, null));
}

// {Induction.Nat.fixBox:go:0_lam_5219}

function $_5219_Induction__Nat__fixBox_58_go_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $_0_lift($_1_lift)($partial_2_4$$_5218_Induction__Nat__fixBox_58_go_58_0_95_lam($_0_lift, $_2_lift));
}

// {Text.PrettyPrint.WL.Core.render:best:0_lam_5220}

function $_5220_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return Text__PrettyPrint__WL__Core__render_58_best_58_0($_0_lift, $_1_lift, null, $_2_lift, $_6_lift, $_3_lift, $_4_lift, $_5_lift);
}

// {Text.PrettyPrint.WL.Core.render:best:0_lam_5221}

function $_5221_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return Text__PrettyPrint__WL__Core__render_58_best_58_0($_0_lift, $_1_lift, null, $_2_lift, $_3_lift, $_4_lift, $JSRTS.force($_5_lift), $_6_lift);
}

// {Parse.tdef:nary:0_lam_5225}

function $_5225_Parse__tdef_58_nary_58_0_95_lam($_0_lift, $_1_lift){
    
    const $cg$3 = $_1_lift.$2;
    return Typedefs__weakenTDef(null, $cg$3.$2, $_0_lift, $cg$3.$1);
}

// {Parse.tdef:nary:0_lam_5226}

function $_5226_Parse__tdef_58_nary_58_0_95_lam($_0_lift, $_1_lift){
    
    const $cg$3 = $_1_lift.$2;
    var $cg$2 = null;
    $cg$2 = new $HC_2_1$Data__Vect___58__58_($cg$3.$1, Data__Vect__fromList(null, $cg$3.$2));
    const $cg$5 = Parse__toVMax(null, null, new $HC_2_1$Data__Vect___58__58_($_1_lift.$1, $cg$2));
    const $cg$7 = $_1_lift.$2;
    var $cg$6 = null;
    $cg$6 = $cg$7.$2;
    return new $HC_2_0$Builtins__MkDPair($cg$5.$1, $_0_lift(Prelude__List__length(null, $cg$6))($cg$5.$1)(Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_1_2$$_5225_Parse__tdef_58_nary_58_0_95_lam($cg$5.$1), Parse__fromVMax_58_go_58_0(null, $cg$5.$1, null, null, null, null, Prelude__Nat__lteRefl($cg$5.$1), $cg$5.$2))));
}

// {Parse.tdef:nary:0_lam_5967}

function $_5967_Parse__tdef_58_nary_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift, $_7_lift){
    return TParsec__Combinators__nelist(null, null, null, new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $_0_lift)(TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, $_1_lift($_0_lift)($_2_lift)))($_6_lift)(Prelude__Nat__lteTransitive(null, null, null, $_7_lift, null));
}

// {Parse.tdef:nary:0_lam_5968}

function $_5968_Parse__tdef_58_nary_58_0_95_lam($_0_lift, $_1_lift, $_2_lift){
    return $partial_8_11$TParsec__Combinators__andbind(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_1_lift, $_0_lift($_1_lift)($_2_lift)), $partial_3_8$$_5967_Parse__tdef_58_nary_58_0_95_lam($_1_lift, $_0_lift, $_2_lift));
}

// {Parse.tdef:nary:0_lam_5969}

function $_5969_Parse__tdef_58_nary_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift, $_6_lift){
    return TParsec__Combinators__rand(null, null, null, null, new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), null, null, TParsec__Combinators__Chars__withSpaces(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_0_lift, TParsec__Combinators__Chars__char(null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_1_lift)($_0_lift)), $partial_1_3$$_5968_Parse__tdef_58_nary_58_0_95_lam($_2_lift))($_5_lift)(Prelude__Nat__lteTransitive(null, null, null, $_6_lift, null));
}

// Induction.Nat.fixBox, go

function Induction__Nat__fixBox_58_go_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_in){
    
    if($_3_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $partial_0_1$$_5217_Induction__Nat__fixBox_58_go_58_0_95_lam();
    } else {
        const $_6_in = $_3_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return $partial_3_4$$_5219_Induction__Nat__fixBox_58_go_58_0_95_lam($_1_arg, $_4_in, $_6_in);
    }
}

// Data.NEList.foldr1, go

function Data__NEList__foldr1_58_go_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        return $_1_arg($_4_arg)(Data__NEList__foldr1_58_go_58_0(null, $_1_arg, null, null, $_5_arg.$1, $_5_arg.$2));
    } else {
        return $_4_arg;
    }
}

// Parse.fromVMax, go

function Parse__fromVMax_58_go_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    
    if(($_7_arg.type === 1)) {
        return new $HC_2_1$Data__Vect___58__58_(new $HC_2_0$Builtins__MkDPair($_7_arg.$1, new $HC_2_0$Builtins__MkPair(Prelude__Nat__lteTransitive(null, null, null, $_7_arg.$4, null), $_7_arg.$2)), Parse__fromVMax_58_go_58_0(null, $_1_arg, null, null, null, null, $_6_arg, $_7_arg.$3));
    } else if(($_7_arg.type === 2)) {
        return new $HC_2_1$Data__Vect___58__58_(new $HC_2_0$Builtins__MkDPair($_1_arg, new $HC_2_0$Builtins__MkPair($_6_arg, $_7_arg.$2)), Parse__fromVMax_58_go_58_0(null, $_7_arg.$1, null, null, null, null, Prelude__Nat__lteTransitive(null, null, null, $_7_arg.$4, null), $_7_arg.$3));
    } else {
        return new $HC_2_1$Data__Vect___58__58_(new $HC_2_0$Builtins__MkDPair($_1_arg, new $HC_2_0$Builtins__MkPair($_6_arg, $_7_arg.$1)), $HC_0_0$Data__Vect__Nil);
    }
}

// Text.PrettyPrint.WL.Core.render, best

function Text__PrettyPrint__WL__Core__render_58_best_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    var $tco$$_6_arg = $_6_arg;
    var $tco$$_7_arg = $_7_arg;
    for(;;) {
        
        if(($_6_arg.type === 4)) {
            $tco$$_7_arg = $partial_6_7$$_5220_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam($_0_arg, $_1_arg, $_3_arg, $_5_arg, $_6_arg.$2, $_7_arg);
            $_0_arg = $_0_arg;
            $_1_arg = $_1_arg;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
            $_5_arg = $_5_arg;
            $_6_arg = $_6_arg.$1;
            $_7_arg = $tco$$_7_arg;
        } else if(($_6_arg.type === 1)) {
            return new $HC_2_1$Text__PrettyPrint__WL__Core__PrettyDoc__Chara($_6_arg.$1, $_7_arg(($_4_arg + 1)));
        } else if(($_6_arg.type === 7)) {
            $tco$$_6_arg = $_6_arg.$1($_4_arg);
            $_0_arg = $_0_arg;
            $_1_arg = $_1_arg;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
            $_5_arg = $_5_arg;
            $_6_arg = $tco$$_6_arg;
            $_7_arg = $_7_arg;
        } else if(($_6_arg.type === 0)) {
            return $_7_arg($_4_arg);
        } else if(($_6_arg.type === 3)) {
            return new $HC_2_3$Text__PrettyPrint__WL__Core__PrettyDoc__Line($_5_arg, $_7_arg($_5_arg));
        } else if(($_6_arg.type === 5)) {
            $_0_arg = $_0_arg;
            $_1_arg = $_1_arg;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
            $_5_arg = ($_5_arg + $_6_arg.$1);
            $_6_arg = $_6_arg.$2;
            $_7_arg = $_7_arg;
        } else if(($_6_arg.type === 8)) {
            $tco$$_6_arg = $_6_arg.$1($_5_arg);
            $_0_arg = $_0_arg;
            $_1_arg = $_1_arg;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = $_4_arg;
            $_5_arg = $_5_arg;
            $_6_arg = $tco$$_6_arg;
            $_7_arg = $_7_arg;
        } else if(($_6_arg.type === 2)) {
            return new $HC_3_2$Text__PrettyPrint__WL__Core__PrettyDoc__Text($_6_arg.$1, $_6_arg.$2, $_7_arg(($_4_arg + $_6_arg.$1)));
        } else {
            return Text__PrettyPrint__WL__Core__render_58_nicest_58_0($_0_arg, $_1_arg, null, $_3_arg, $_4_arg, Text__PrettyPrint__WL__Core__render_58_best_58_0($_0_arg, $_1_arg, null, $_3_arg, $_4_arg, $_5_arg, $_6_arg.$1, $_7_arg), new $JSRTS.Lazy((function(){
                return (function(){
                    return $_5221_Text__PrettyPrint__WL__Core__render_58_best_58_0_95_lam($_0_arg, $_1_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg.$2, $_7_arg);
                })();
            })));
        }
    }
}

// Text.PrettyPrint.WL.Core.render, nicest

function Text__PrettyPrint__WL__Core__render_58_nicest_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    var $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0(($_1_arg - $_4_arg), ((Text__PrettyPrint__WL__Core__render_58_rwidth_58_0($_0_arg, $_1_arg, null) - $_4_arg) + $_3_arg)) < 0)) {
        $cg$1 = ($_1_arg - $_4_arg);
    } else {
        $cg$1 = ((Text__PrettyPrint__WL__Core__render_58_rwidth_58_0($_0_arg, $_1_arg, null) - $_4_arg) + $_3_arg);
    }
    
    
    if(Text__PrettyPrint__WL__Core__fits($cg$1, $_5_arg)) {
        return $_5_arg;
    } else {
        return $JSRTS.force($_6_arg);
    }
}

// Text.PrettyPrint.WL.Core.render, rwidth

function Text__PrettyPrint__WL__Core__render_58_rwidth_58_0($_0_arg, $_1_arg, $_2_arg){
    var $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_1_arg, ((($_1_arg * $_0_arg))|0)) < 0)) {
        $cg$1 = $_1_arg;
    } else {
        $cg$1 = ((($_1_arg * $_0_arg))|0);
    }
    
    
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0(0, $cg$1) > 0)) {
        return 0;
    } else {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_1_arg, ((($_1_arg * $_0_arg))|0)) < 0)) {
            return $_1_arg;
        } else {
            return ((($_1_arg * $_0_arg))|0);
        }
    }
}

// Data.Vect.reverse, go

function Data__Vect__reverse_58_go_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    for(;;) {
        
        if(($_6_arg.type === 1)) {
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = null;
            $_3_arg = null;
            $_4_arg = null;
            $_5_arg = new $HC_2_1$Data__Vect___58__58_($_6_arg.$1, $_5_arg);
            $_6_arg = $_6_arg.$2;
        } else {
            return $_5_arg;
        }
    }
}

// Text.PrettyPrint.WL.Core.showPrettyDoc, showPrettyDocS

function Text__PrettyPrint__WL__Core__showPrettyDoc_58_showPrettyDocS_58_0($_0_arg, $_1_arg, $_2_arg){
    
    if(($_1_arg.type === 1)) {
        return (($_1_arg.$1)+(Text__PrettyPrint__WL__Core__showPrettyDoc_58_showPrettyDocS_58_0(null, $_1_arg.$2, $_2_arg)));
    } else if(($_1_arg.type === 0)) {
        return $_2_arg;
    } else if(($_1_arg.type === 3)) {
        return ((("\n")+(Text__PrettyPrint__WL__Core__spaces($_1_arg.$1))) + Text__PrettyPrint__WL__Core__showPrettyDoc_58_showPrettyDocS_58_0(null, $_1_arg.$2, $_2_arg));
    } else {
        return ($_1_arg.$2 + Text__PrettyPrint__WL__Core__showPrettyDoc_58_showPrettyDocS_58_0(null, $_1_arg.$3, $_2_arg));
    }
}

// Parse.tdef, nary

function Parse__tdef_58_nary_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return $partial_8_11$TParsec__Combinators__map(null, null, null, null, $partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_1_2$$_5226_Parse__tdef_58_nary_58_0_95_lam($_4_arg), null, TParsec__Combinators__Chars__parens(null, null, $partial_0_3$Parse___123_tdef_95_1562_125_(), new $HC_3_0$Prelude__Applicative__Alternative_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_1$Parse___123_tdef_95_1608_125_(), $partial_0_3$Parse___123_tdef_95_1622_125_()), new $HC_2_0$Prelude__Monad__Monad_95_ictor(new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$Parse___123_tdef_95_1565_125_(), $partial_0_2$Parse___123_tdef_95_1579_125_(), $partial_0_4$Parse___123_tdef_95_1593_125_()), $partial_0_4$Parse___123_tdef_95_1667_125_()), $partial_0_1$TermParse___123_chooseParser_95_66_125_(), $partial_0_2$TermParse___123_chooseParser_95_67_125_(), $partial_0_2$TermParse___123_chooseParser_95_68_125_(), $_1_arg, $partial_3_7$$_5969_Parse__tdef_58_nary_58_0_95_lam($_1_arg, $_3_arg, $_2_arg)));
}

// Data.Inspect.Data.Inspect.SizedList a, a implementation of Data.Inspect.Inspect, method inspect, go

function Data__Inspect__Data__Inspect___64_Data__Inspect__Inspect_36_SizedList_32_a_58_a_58__33_inspect_58_0_58_go_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if($_4_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__Maybe__Nothing;
    } else {
        
        return new $HC_1_1$Prelude__Maybe__Just(new $HC_2_0$Builtins__MkPair($_5_arg.$1, $_5_arg.$2));
    }
}

// Backend.Haskell.renderDef, renderConstructor

function Backend__Haskell__renderDef_58_renderConstructor_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    const $cg$3 = $_3_arg.$2;
    if(($cg$3.type === 2)) {
        return Backend__Haskell__renderApp(null, $_3_arg.$1, Prelude__Functor__Data__Vect___64_Prelude__Functor__Functor_36_Vect_32_n_58__33_map_58_0(null, null, null, $partial_0_1$Backend__Haskell__guardParen(), $cg$3.$1));
    } else if(($cg$3.type === 1)) {
        return Backend__Haskell__renderApp(null, $_3_arg.$1, $HC_0_0$Data__Vect__Nil);
    } else {
        return Backend__Haskell__renderApp(null, $_3_arg.$1, new $HC_2_1$Data__Vect___58__58_(Backend__Haskell__guardParen($_3_arg.$2), $HC_0_0$Data__Vect__Nil));
    }
}

// with block in Prelude.Strings.unpack

function _95_Prelude__Strings__unpack_95_with_95_36($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        var $cg$2 = null;
        if((((($_1_arg.$2 == "")) ? 1|0 : 0|0) === 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = false;
        }
        
        const $cg$4 = Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$2, true);
        var $cg$3 = null;
        if(($cg$4.type === 1)) {
            $cg$3 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$3 = new $HC_2_1$Prelude__Strings__StrCons($_1_arg.$2[0], $_1_arg.$2.slice(1));
        }
        
        return new $HC_2_1$Prelude__List___58__58_($_1_arg.$1, _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$3));
    } else {
        return $HC_0_0$Prelude__List__Nil;
    }
}


