import 'dart:typed_data';

import 'package:hex/hex.dart';
import "package:pointycastle/api.dart"
    show PrivateKeyParameter, PublicKeyParameter;
import "package:pointycastle/digests/sha256.dart";
import 'package:pointycastle/ecc/api.dart'
    show ECPrivateKey, ECPublicKey, ECSignature, ECPoint;
import "package:pointycastle/ecc/curves/secp256k1.dart";
import 'package:pointycastle/macs/hmac.dart';
import "package:pointycastle/signers/ecdsa_signer.dart";

final _negativeFlag = BigInt.from(0x80);

final _zero32 = Uint8List.fromList(List.generate(32, (index) => 0));
final _ecGroupOrder = HEX
    .decode("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
final _ecpP = HEX
    .decode("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f");
final _secp256k1 = ECCurve_secp256k1();
final _n = _secp256k1.n;
final _g = _secp256k1.G;
BigInt _nDiv2 = _n >> 1;

// Exceptions
/// Bad Private Key
const _throwBadPrivate = 'Expected Private';

/// Bad Point
const _throwBadPoint = 'Expected Point';

/// Bad Tweak
const _throwBadTweak = 'Expected Tweak';

/// Bad Hash
const _throwBadHash = 'Expected Hash';

/// Bad Signature
const _throwBadSignature = 'Expected Signature';

/// Is Buffer Private Key ?
bool isPrivate(Uint8List x) {
  if (!isScalar(x)) return false;
  return _compare(x, _zero32) > 0 && // > 0
      _compare(x, _ecGroupOrder as Uint8List) < 0; // < G
}

/// Is Buffer Point
bool isPoint(Uint8List p) {
  if (p.length < 33) {
    return false;
  }
  var t = p[0];
  var x = p.sublist(1, 33);

  if (_compare(x, _zero32) == 0) {
    return false;
  }
  if (_compare(x, _ecpP as Uint8List) == 1) {
    return false;
  }
  try {
    decodeFrom(p);
  } catch (err) {
    return false;
  }
  if ((t == 0x02 || t == 0x03) && p.length == 33) {
    return true;
  }
  var y = p.sublist(33);
  if (_compare(y, _zero32) == 0) {
    return false;
  }
  if (_compare(y, _ecpP as Uint8List) == 1) {
    return false;
  }
  if (t == 0x04 && p.length == 65) {
    return true;
  }
  return false;
}

/// Is Scalar
bool isScalar(Uint8List x) {
  return x.length == 32;
}

/// Is Order Scalar
bool isOrderScalar(x) {
  if (!isScalar(x)) return false;
  return _compare(x, _ecGroupOrder as Uint8List) < 0; // < G
}

/// Is Signature
bool isSignature(Uint8List value) {
  Uint8List r = value.sublist(0, 32);
  Uint8List s = value.sublist(32, 64);

  return value.length == 64 &&
      _compare(r, _ecGroupOrder as Uint8List) < 0 &&
      _compare(s, _ecGroupOrder as Uint8List) < 0;
}

/// Is Point Compressed
bool _isPointCompressed(Uint8List p) {
  return p[0] != 0x04;
}

/// Assume Compression
bool assumeCompression(bool? value, Uint8List? pubkey) {
  if (value == null && pubkey != null) return _isPointCompressed(pubkey);
  if (value == null) return true;
  return value;
}

/// Point From Scalar
Uint8List? pointFromScalar(Uint8List d, bool _compressed) {
  if (!isPrivate(d)) throw ArgumentError(_throwBadPrivate);
  BigInt dd = fromBuffer(d);
  ECPoint pp = (_g * dd) as ECPoint;
  if (pp.isInfinity) return null;
  return getEncoded(pp, _compressed);
}

/// Point Add Scalar
Uint8List? pointAddScalar(Uint8List p, Uint8List tweak, bool _compressed) {
  if (!isPoint(p)) throw ArgumentError(_throwBadPoint);
  if (!isOrderScalar(tweak)) throw ArgumentError(_throwBadTweak);
  bool compressed = assumeCompression(_compressed, p);
  ECPoint? pp = decodeFrom(p);
  if (_compare(tweak, _zero32) == 0) return getEncoded(pp, compressed);
  BigInt tt = fromBuffer(tweak);
  ECPoint qq = (_g * tt) as ECPoint;
  ECPoint uu = (pp! + qq) as ECPoint;
  if (uu.isInfinity) return null;
  return getEncoded(uu, compressed);
}

/// Private Add
Uint8List? privateAdd(Uint8List d, Uint8List tweak) {
  if (!isPrivate(d)) throw ArgumentError(_throwBadPrivate);
  if (!isOrderScalar(tweak)) throw ArgumentError(_throwBadTweak);
  BigInt dd = fromBuffer(d);
  BigInt tt = fromBuffer(tweak);
  Uint8List dt = toBuffer((dd + tt) % _n);

  if (dt.length < 32) {
    Uint8List padLeadingZero = Uint8List(32 - dt.length);
    dt = Uint8List.fromList(padLeadingZero + dt);
  }

  if (!isPrivate(dt)) return null;
  return dt;
}

/// Sign Hash
Uint8List sign(Uint8List hash, Uint8List x) {
  if (!isScalar(hash)) throw ArgumentError(_throwBadHash);
  if (!isPrivate(x)) throw ArgumentError(_throwBadPrivate);
  ECSignature sig = deterministicGenerateK(hash, x);
  Uint8List buffer = Uint8List(64);
  buffer.setRange(0, 32, _encodeBigInt(sig.r));
  BigInt s;
  if (sig.s.compareTo(_nDiv2) > 0) {
    s = _n - sig.s;
  } else {
    s = sig.s;
  }
  buffer.setRange(32, 64, _encodeBigInt(s));
  return buffer;
}

/// Verify Signature
bool verify(Uint8List hash, Uint8List q, Uint8List signature) {
  if (!isScalar(hash)) throw ArgumentError(_throwBadHash);
  if (!isPoint(q)) throw ArgumentError(_throwBadPoint);
  // 1.4.1 Enforce r and s are both integers in the interval [1, n − 1] (1, isSignature enforces '< n - 1')
  if (!isSignature(signature)) throw ArgumentError(_throwBadSignature);

  ECPoint? Q = decodeFrom(q);
  BigInt r = fromBuffer(signature.sublist(0, 32));
  BigInt s = fromBuffer(signature.sublist(32, 64));

  final signer = ECDSASigner(null, HMac(SHA256Digest(), 64));
  signer.init(false, PublicKeyParameter(ECPublicKey(Q, _secp256k1)));
  return signer.verifySignature(hash, ECSignature(r, s));
  /* STEP BY STEP
  // 1.4.1 Enforce r and s are both integers in the interval [1, n − 1] (2, enforces '> 0')
  if (r.compareTo(n) >= 0) return false;
  if (s.compareTo(n) >= 0) return false;

  // 1.4.2 H = Hash(M), already done by the user
  // 1.4.3 e = H
  BigInt e = fromBuffer(hash);

  BigInt sInv = s.modInverse(n);
  BigInt u1 = (e * sInv) % n;
  BigInt u2 = (r * sInv) % n;

  // 1.4.5 Compute R = (xR, yR)
  //               R = u1G + u2Q
  ECPoint R = G * u1 + Q * u2;

  // 1.4.5 (cont.) Enforce R is not at infinity
  if (R.isInfinity) return false;

  // 1.4.6 Convert the field element R.x to an integer
  BigInt xR = R.x.toBigInteger();

  // 1.4.7 Set v = xR mod n
  BigInt v = xR % n;

  // 1.4.8 If v = r, output "valid", and if v != r, output "invalid"
  return v.compareTo(r) == 0;
  */
}

/// Decode a BigInt from bytes in big-endian encoding.
BigInt _decodeBigInt(List<int> bytes) {
  BigInt result = BigInt.from(0);
  for (int i = 0; i < bytes.length; i++) {
    result += BigInt.from(bytes[bytes.length - i - 1]) << (8 * i);
  }
  return result;
}

var _byteMask = BigInt.from(0xff);

/// Encode a BigInt into bytes using big-endian encoding.
Uint8List _encodeBigInt(BigInt number) {
  int needsPaddingByte;
  int rawSize;

  if (number > BigInt.zero) {
    rawSize = (number.bitLength + 7) >> 3;
    needsPaddingByte =
        ((number >> (rawSize - 1) * 8) & _negativeFlag) == _negativeFlag
            ? 1
            : 0;

    if (rawSize < 32) {
      needsPaddingByte = 1;
    }
  } else {
    needsPaddingByte = 0;
    rawSize = (number.bitLength + 8) >> 3;
  }

  final size = rawSize < 32 ? rawSize + needsPaddingByte : rawSize;
  var result = Uint8List(size);
  for (int i = 0; i < size; i++) {
    result[size - i - 1] = (number & _byteMask).toInt();
    number = number >> 8;
  }
  return result;
}

/// [BigInt] from [Uint8List] buffer
BigInt fromBuffer(Uint8List d) {
  return _decodeBigInt(d);
}

/// [BigInt] to [Uint8List] buffer
Uint8List toBuffer(BigInt d) {
  return _encodeBigInt(d);
}

/// [Uint8List] decode to [ECPoint]
ECPoint? decodeFrom(Uint8List P) {
  return _secp256k1.curve.decodePoint(P);
}

/// [ECPoint] encode to [Uint8List]
Uint8List getEncoded(ECPoint? P, [bool compressed = true]) {
  return P!.getEncoded(compressed);
}

/// Deterministic Generate K
ECSignature deterministicGenerateK(Uint8List hash, Uint8List x) {
  final signer = ECDSASigner(null, HMac(SHA256Digest(), 64));
  var pkp = PrivateKeyParameter(ECPrivateKey(_decodeBigInt(x), _secp256k1));
  signer.init(true, pkp);
//  signer.init(false, PublicKeyParameter(ECPublicKey(secp256k1.curve.decodePoint(x), secp256k1)));
  return signer.generateSignature(hash) as ECSignature;
}

/// Compare Two [Uint8List] Buffer
int _compare(Uint8List a, Uint8List b) {
  BigInt aa = fromBuffer(a);
  BigInt bb = fromBuffer(b);
  if (aa == bb) return 0;
  if (aa > bb) return 1;
  return -1;
}
