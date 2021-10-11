import math
import random
import warnings
import hashlib


# Euclidean algorithm for gcd computation
def egcd(a, b):
    if a == 0:
        return b, 0, 1
    else:
        g, y, x = egcd(b % a, a)
        return g, x - (b // a) * y, y


# Modular inversion computation
def mod_inv(a, p):
    if a < 0:
        return p - mod_inv(-a, p)
    g, x, y = egcd(a, p)
    if g != 1:
        raise ArithmeticError("Modular inverse does not exist")
    else:
        return x % p


# Function to map a message to a bit string
def hash_message_to_bits(msg):
    h = hashlib.sha256()
    h.update(msg.encode())
    h_as_bits = ''.join(format(byte, '08b') for byte in h.digest())
    return h_as_bits


# Function to map a truncated bit string to an integer modulo q
def bits_to_int(h_as_bits, q):
    val = 0
    len = int(math.log(q, 2) + 1)
    for i in range(len):
        val = val * 2
        if (h_as_bits[i] == '1'):
            val = val + 1
    return val % q


# An elliptic curve is represented as an object of type Curve.
# Note that for this lab, we use the short Weierstrass form of representation.
class Curve(object):

    def __init__(self, a, b, p, P_x, P_y, q):
        self.a = a
        self.b = b
        self.p = p
        self.P_x = P_x
        self.P_y = P_y
        self.q = q

    def is_singular(self):
        return (4 * self.a ** 3 + 27 * self.b ** 2) % self.p == 0

    def on_curve(self, x, y):
        return (y ** 2 - x ** 3 - self.a * x - self.b) % self.p == 0

    def is_equal(self, other):
        if not isinstance(other, Curve):
            return False
        return self.a == other.a and self.b == other.b and self.p == other.p


# A point at infinity on an elliptic curve is represented separately as an object of type PointInf.
# We make this distinction between a point at infinity and a regular point purely for the ease of implementation.
class PointInf(object):

    def __init__(self, curve, is_negative=False):
        self.curve = curve
        self.is_negative = is_negative

    def is_equal(self, other):
        if not isinstance(other, PointInf):
            return False
        return self.curve.is_equal(other.curve)

    def negate(self):
        # Write a function that negates a PointInf object.        
        # Ths is an optional extension and is not evaluated
        return PointInf(self.curve, is_negative=(not self.is_negative))

    def double(self):
        # Write a function that doubles a PointInf object.
        return PointInf(self.curve, is_negative=self.is_negative)

    def add(self, other):
        # Write a function that adds a Point object (or a PointInf object) to a PointInf object. 
        # See below for the description of a Point object
        # Make sure to output the correct kind of object depending on whether "other" is a
        # Point object or a PointInf object

        if not self.curve.is_equal(other.curve):
            raise ArithmeticError("Cannot add points that are on different curves")

        if isinstance(other, PointInf):
            return self.double()

        if isinstance(other, Point):
            return Point(other.curve, other.x, other.y)


# A point on an elliptic curve is represented as an object of type Point. 
# Note that for this lab, we will use the affine coordinates-based representation of a point on an elliptic curve.
class Point(object):

    def __init__(self, curve, x, y):
        self.curve = curve
        self.p = self.curve.p
        self.x = x % self.p  # Reduce x and y to p when initialising, for convenience
        self.y = y % self.p
        self.on_curve = True
        if not self.curve.on_curve(self.x, self.y):
            warnings.warn("Point (%d, %d) is not on curve \"%s\"" % (self.x, self.y, self.curve))
            self.on_curve = False

    def is_equal(self, other):
        if not isinstance(other, Point):
            return False
        return self.curve.is_equal(other.curve) and self.x == other.x and self.y == other.y

    def negate(self):
        # Write a function that negates a Point object and returns the resulting Point object
        # Ths is an optional extension and is not evaluated
        return Point(self.curve, self.x, -self.y)

    def double(self):
        # Write a function that doubles a Point object and returns the resulting Point object
        return self.add(self)

    def add(self, other):
        # Write a function that adds a Point object (or a PointInf object) to the current Point object and
        # returns the resulting Point object
        if not self.curve.is_equal(other.curve):
            raise ArithmeticError("Cannot add points that are on different curves")

        if isinstance(other, PointInf):
            return Point(self.curve, self.x, self.y)

        _lambda = 0
        y_delta = (self.y - other.y) % self.p
        x_delta = (self.x - other.x) % self.p
        # the only difference in the two cases is the slope(lambda), so simply reuse the code

        if y_delta == 0 and x_delta == 0:
            # Prevent division by 0
            if self.y == 0:
                return PointInf(self.curve)

            # take advantage of mod inverses, division is a thing of the past
            # (2y)^-1
            _lambda = ((3 * pow(self.x, 2, self.p) + self.curve.a) % self.p) * mod_inv(2 * self.y, self.p)
            _lambda %= self.p
        else:

            # Division by 0, should go to infinity
            # Covers P + (-P) = O
            if x_delta == 0:
                return PointInf(self.curve)

            # mod_inv at work again
            _lambda = y_delta * mod_inv(x_delta, self.p)
            _lambda %= self.p

        x_prime = (pow(_lambda, 2, self.p) - self.x - other.x) % self.p
        y_prime = - (self.y + _lambda * (x_prime - self.x)) % self.p

        return Point(self.curve, x_prime, y_prime)

    def scalar_multiply(self, scalar):
        # Write a function that performs a scalar multiplication on the current Point object and
        # returns the resulting Point object
        # Make sure to check that the scalar is of type int or long
        # Your function need not be "constant-time"

        # return self.scalar_multiply_Montgomery_Ladder(scalar)

        scalar = scalar % self.p
        result = PointInf(self.curve)

        for b in format(scalar, "b"):
            result = result.double()
            if b == "1":
                result = result.add(self)

        return result

    def scalar_multiply_Montgomery_Ladder(self, scalar):
        # Write a function that performs a "constant-time" scalar multiplication on the current
        # Point object and returns the resulting Point object
        # Make sure to check that the scalar is of type int or long
        # Implement an elementary timer to check that your implementation is indeed constant-time
        # This is not graded but is an extension for your to try out on your own

        scalar = scalar % self.p
        # avoid modifying the current state of the point, so make a copy of it
        p = Point(self.curve, self.x, self.y)
        result = PointInf(self.curve)

        for b in format(scalar, "b"):
            if b == "1":
                result = result.add(p)
                p = p.double()
            else:
                p = p.add(result)
                result = result.double()

        return result


# The parameters for an ECDSA scheme are represented as an object of type ECDSA_Params
class ECDSA_Params(object):
    def __init__(self, a, b, p, P_x, P_y, q):
        self.p = p
        self.q = q
        self.curve = Curve(a, b, p, P_x, P_y, q)
        self.P = Point(self.curve, P_x, P_y)


def KeyGen(params):
    # Write a function that takes as input an ECDSA_Params object and outputs the key pair (x, Q)
    x = random.randrange(1, params.q)
    Q = params.P.scalar_multiply(x)

    return x, Q


def Sign_FixedNonce(params, k, x, msg):
    # Write a function that takes as input an ECDSA_Params object, a fixed nonce k,
    # a signing key x, and a message msg, and outputs a signature (r, s)

    h = bits_to_int(hash_message_to_bits(msg), params.q)
    P_prim = params.P.scalar_multiply(k)
    r = P_prim.x % params.q

    if r == 0:
        return None

    k_inv = mod_inv(k, params.q)
    s = k_inv * ((h + (x * r) % params.q) % params.q)
    s %= params.q

    if s == 0:
        return None

    return r, s


def Sign(params, x, msg):
    # Write a function that takes as input an ECDSA_Params object, a signing key x,
    # and a message msg, and outputs a signature (r, s)
    # The nonce is to be generated uniformly at random in the appropriate range
    k = random.randrange(1, params.q)

    result = None

    while result is None:
        result = Sign_FixedNonce(params, k, x, msg)

    return result


def Verify(params, Q, msg, r, s):
    # Write a function that takes as input an ECDSA_Params object, a verification key Q,
    # a message msg, and a signature (r, s)
    # The output should be either 0 (indicating failure) or 1 (indicating success)

    if r < 1 or r >= params.q or s < 1 or s >= params.q:
        return 0

    w = mod_inv(s, params.q)
    h = bits_to_int(hash_message_to_bits(msg), params.q)

    u1 = (w * h) % params.q
    u2 = (w * r) % params.q

    uP = params.P.scalar_multiply(u1)
    uQ = Q.scalar_multiply(u2)

    Z = uP.add(uQ)

    if Z.x % params.q == r:
        return 1

    return 0


from module_1_ECC_ECDSA_tests import run_tests

run_tests(ECDSA_Params, Point, KeyGen, Sign, Sign_FixedNonce, Verify)
