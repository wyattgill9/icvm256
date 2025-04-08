# ICVM256 Elliptic Curve Implementation

class FiniteField:
    def __init__(self, p):
        self.p = p
        
    def add(self, a, b):
        return (a + b) % self.p
        
    def subtract(self, a, b):
        return (a - b) % self.p
        
    def multiply(self, a, b):
        return (a * b) % self.p
        
    def inverse(self, a):
        """Compute the multiplicative inverse using Extended Euclidean Algorithm"""
        if a == 0:
            raise ZeroDivisionError("Division by zero")
        
        s, old_s = 0, 1
        t, old_t = 1, 0
        r, old_r = self.p, a
        
        while r != 0:
            quotient = old_r // r
            old_r, r = r, old_r - quotient * r
            old_s, s = s, old_s - quotient * s
            old_t, t = t, old_t - quotient * t
        
        return old_s % self.p
    
    def divide(self, a, b):
        return self.multiply(a, self.inverse(b))
    
    def pow(self, a, n):
        """Fast exponentiation"""
        result = 1
        a = a % self.p
        while n > 0:
            if n % 2 == 1:
                result = self.multiply(result, a)
            a = self.multiply(a, a)
            n = n // 2
        return result

class EllipticCurve:
    """Elliptic curve in short Weierstrass form: y^2 = x^3 + ax + b over Fp"""
    
    def __init__(self, a, b, p, n, G_x, G_y):
        self.a = a
        self.b = b
        self.field = FiniteField(p)
        self.p = p
        self.n = n  # Order of the curve
        self.G = (G_x, G_y)  # Generator point
        
        if not self.is_on_curve(self.G):
            raise ValueError("Generator point is not on the curve")
    
    def is_on_curve(self, point):
        """Check if a point lies on the curve"""
        if point is None:  # None represents the point at infinity
            return True
        
        x, y = point
        # Check y^2 = x^3 + ax + b (mod p)
        left = self.field.pow(y, 2)
        right = self.field.add(
            self.field.add(
                self.field.pow(x, 3),
                self.field.multiply(self.a, x)
            ),
            self.b
        )
        return left == right
    
    def add_points(self, P1, P2):
        """Add two points on the curve"""
        if P1 is None:
            return P2
        if P2 is None:
            return P1
            
        x1, y1 = P1
        x2, y2 = P2
        
        if x1 == x2 and y1 == self.field.subtract(0, y2):
            return None  # Return point at infinity
        
        if x1 == x2 and y1 == y2:  # Point doubling
            # Slope = (3x^2 + a) / (2y)
            numerator = self.field.add(
                self.field.multiply(3, self.field.pow(x1, 2)),
                self.a
            )
            denominator = self.field.multiply(2, y1)
            slope = self.field.divide(numerator, denominator)
        else:  # Point addition
            numerator = self.field.subtract(y2, y1)
            denominator = self.field.subtract(x2, x1)
            slope = self.field.divide(numerator, denominator)
        
        x3 = self.field.subtract(
            self.field.subtract(self.field.pow(slope, 2), x1),
            x2
        )
        y3 = self.field.subtract(
            self.field.multiply(slope, self.field.subtract(x1, x3)),
            y1
        )
        
        return (x3, y3)
    
    def scalar_multiply(self, P, scalar):
        """Multiply a point by a scalar using double-and-add method"""
        scalar = scalar % self.n
        
        if scalar == 0 or P is None:
            return None  # Point at infinity
        
        result = None
        addend = P
        
        while scalar:
            if scalar & 1:
                result = self.add_points(result, addend)
            addend = self.add_points(addend, addend)
            scalar >>= 1
            
        return result
    
    def generate_keypair(self):
        """Generate a private key and corresponding public key"""
        import random
        private_key = random.randint(1, self.n - 1)
        public_key = self.scalar_multiply(self.G, private_key)
        return private_key, public_key
    
    def ecdh_shared_secret(self, private_key, public_key):
        """Compute a shared secret using ECDH"""
        shared_point = self.scalar_multiply(public_key, private_key)
        if shared_point is None:
            raise ValueError("Invalid shared point (point at infinity)")
        return shared_point[0]
    
    def hash_message(self, message):
        """Hash a message to an integer modulo n"""
        import hashlib
        hash_bytes = hashlib.sha256(message.encode()).digest()
        return int.from_bytes(hash_bytes, 'big') % self.n
    
    def sign_message(self, private_key, message):
        """Sign a message using ECDSA"""
        import random
        z = self.hash_message(message)
        
        r, s = 0, 0
        while r == 0 or s == 0:
            k = random.randint(1, self.n - 1)
            
            R = self.scalar_multiply(self.G, k)
            r = R[0] % self.n
            
            k_inv = self.field.inverse(k)
            s = self.field.multiply(k_inv, 
                self.field.add(z, self.field.multiply(r, private_key))) % self.n
        
        return (r, s)
    
    def verify_signature(self, public_key, message, signature):
        """Verify an ECDSA signature"""
        r, s = signature
        
        if not (1 <= r < self.n and 1 <= s < self.n):
            return False
            
        z = self.hash_message(message)
        
        s_inv = self.field.inverse(s)
        u1 = self.field.multiply(z, s_inv) % self.n
        u2 = self.field.multiply(r, s_inv) % self.n
        
        P1 = self.scalar_multiply(self.G, u1)
        P2 = self.scalar_multiply(public_key, u2)
        P = self.add_points(P1, P2)
        
        if P is None:
            return False
            
        return r == P[0] % self.n

def create_icvm256_curve():
    p = 2**256 - 189
    a = -3
    b = 41058363725152142129326129780047268409114441015993725554835345017341148081
    n = 2**256 - 4294968273
    G_x = 48439561293906451759052585252797914202762949526041747007087301598123930278343
    G_y = 36134250956634268608073503786472617942721831898550311769283126311524866117838
    
    return EllipticCurve(a, b, p, n, G_x, G_y)

