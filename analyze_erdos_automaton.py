#!/usr/bin/env python3
"""
Analyze the automaton structure for Erdős conjecture.

The key insight: We're not asking "does doubling preserve no-digit-2",
we're asking "does 2^n have digit 2".

The automaton that matters is the one that:
- Tracks the state of reading ternary digits
- Rejects if it sees digit 2
- The question is: for which n does the automaton accept 2^n?
"""

def to_base3(n):
    """Convert n to base 3 digits (LSB first)."""
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return digits

def to_base3_str(n):
    """Convert n to base 3 string (MSB first)."""
    return ''.join(map(str, reversed(to_base3(n))))

def has_digit_2(n):
    """Check if n has digit 2 in base 3."""
    while n > 0:
        if n % 3 == 2:
            return True
        n //= 3
    return False

def digit_at_position(n, k):
    """Get the k-th ternary digit (from right, 0-indexed)."""
    return (n // (3**k)) % 3

def first_digit_2_position(n):
    """Find the position of the first digit 2 (from right), or -1 if none."""
    pos = 0
    while n > 0:
        if n % 3 == 2:
            return pos
        n //= 3
        pos += 1
    return -1

# The simple automaton: states {accept, reject}
# - Start in accept
# - On digit 0 or 1: stay in accept
# - On digit 2: go to reject (and stay there)
# - Accept iff final state is accept

print("="*70)
print("ERDŐS CONJECTURE: Powers of 2 without digit 2")
print("="*70)

print("\nAll survivors up to 2^50:")
survivors = []
for n in range(51):
    power = 2**n
    if not has_digit_2(power):
        survivors.append(n)
        print(f"  2^{n:2d} = {power:15d} = {to_base3_str(power)}_3")

print(f"\nSurvivors: {survivors}")

# For non-survivors, find where the first 2 appears
print("\n" + "="*70)
print("NON-SURVIVORS: Position of first digit 2")
print("="*70)

for n in range(20):
    if n in survivors:
        continue
    power = 2**n
    pos = first_digit_2_position(power)
    b3 = to_base3_str(power)
    total_digits = len(b3)
    print(f"  2^{n:2d} = {b3}_3 (first 2 at position {pos} from right, total {total_digits} digits)")

# Analyze the mod 3^k structure
print("\n" + "="*70)
print("MODULAR STRUCTURE: 2^n mod 3^k")
print("="*70)

print("\n2^n mod 3 (determines last digit):")
for n in range(10):
    print(f"  2^{n} mod 3 = {pow(2, n, 3)}")
print("  Pattern: 1, 2, 1, 2, 1, 2, ... (period 2)")
print("  => Odd n always has last digit = 2!")

print("\n2^n mod 9 (determines last 2 digits):")
for n in range(10):
    val = pow(2, n, 9)
    d0 = val % 3
    d1 = (val // 3) % 3
    print(f"  2^{n} mod 9 = {val:2d} = {d1}{d0}_3")
print("  Period: 6")

print("\n2^n mod 27 (determines last 3 digits):")
for n in range(20):
    val = pow(2, n, 27)
    digits = to_base3_str(val).zfill(3)
    has_2 = '2' in digits
    status = "✗" if has_2 else "✓"
    print(f"  2^{n:2d} mod 27 = {val:2d} = {digits}_3 {status}")
print("  Period: 18")

# Count survivors at each modular level
print("\n" + "="*70)
print("SURVIVOR DENSITY BY MODULAR DEPTH")
print("="*70)

for k in range(1, 8):
    mod = 3**k
    period = 2 * (3**(k-1))  # Period of 2^n mod 3^k

    survivors_mod = 0
    for n in range(period):
        val = pow(2, n, mod)
        if not has_digit_2(val):
            survivors_mod += 1

    density = survivors_mod / period
    print(f"  mod 3^{k} = {mod:6d}: period = {period:5d}, survivors = {survivors_mod:4d}, density = {density:.4f}")

# The key insight: check if n ≡ r (mod period) always has digit 2
print("\n" + "="*70)
print("RESIDUE CLASS ANALYSIS mod 3^4 = 81")
print("="*70)

mod = 81
period = 54  # 2 * 3^3

# For each residue class, check if all members have digit 2
never_has_2 = []
always_has_2 = []

for r in range(period):
    # Check 2^(r + k*period) mod 81 for several k
    has_2_count = 0
    samples = 10
    for k in range(samples):
        n = r + k * period
        val = pow(2, n, mod)
        if has_digit_2(val):
            has_2_count += 1

    val_r = pow(2, r, mod)
    b3 = to_base3_str(val_r).zfill(4)

    if has_2_count == 0:
        never_has_2.append((r, b3))
    elif has_2_count == samples:
        always_has_2.append(r)

print(f"Residue classes (mod {period}) that NEVER have digit 2 in last 4 positions:")
for r, b3 in never_has_2:
    print(f"  n ≡ {r:2d} (mod {period}): 2^n mod 81 = {b3}_3")

print(f"\nCount: {len(never_has_2)} out of {period} residue classes survive mod 81")

# The critical observation about the automaton structure
print("\n" + "="*70)
print("THE AUTOMATON PERSPECTIVE")
print("="*70)

print("""
The automaton for Erdős is simple:
  - States: {ALIVE, DEAD}
  - Start: ALIVE
  - Transitions:
      ALIVE --[0]--> ALIVE
      ALIVE --[1]--> ALIVE
      ALIVE --[2]--> DEAD
      DEAD --[any]--> DEAD
  - Accept: ALIVE

The question is: for which n does the run on digits of 2^n end in ALIVE?

Key insight: This automaton reads ALL digits of 2^n.
As n grows, 2^n has more digits (~0.63n digits).
The probability each digit ≠ 2 is 2/3.
So P(all digits ≠ 2) ≈ (2/3)^{0.63n} → 0.

The three survivors {0, 2, 8} are "accidents" where the small number
of digits all happened to be in {0, 1}.
""")

# Verify the accidents
print("The three accidents:")
for n in [0, 2, 8]:
    power = 2**n
    b3 = to_base3_str(power)
    print(f"  2^{n} = {power} = {b3}_3 ({len(b3)} digits, all in {{0,1}})")

# The connection to our tail-rejection proof
print("\n" + "="*70)
print("CONNECTION TO TAIL REJECTION")
print("="*70)

print("""
In the Lean proof, we check:
  runAutoFrom (digits of N_orbit(seed, t) starting at position 14) s1 = none

This asks: does the automaton (starting from state s1) reject when
reading the tail of the orbit number?

The automaton:
  s0 --[0]--> s0 (accept)
  s0 --[1]--> s1 (accept)
  s0 --[2]--> reject
  s1 --[0]--> s0 (accept)
  s1 --[1]--> s1 (accept)
  s1 --[2]--> reject

This is the "survival" automaton that checks if a digit sequence
contains no 2. Starting from s1 means we're in a state where we
just saw a 1.

For the orbit number N_orbit(128, t), we know positions 0-13 are OK
(by the digit14 lemma). The question is whether positions 14+ are OK.

The equidistribution discovery: at each depth d, digit(14+d) is
perfectly uniform over {0, 1, 2} as t varies mod 3^{d+1}.

This means: at every depth, 1/3 of residue classes die.
After d steps, 2^d / 3^d = (2/3)^d fraction survive.
As d → ∞, this → 0.

But "fraction → 0" doesn't prove "every t eventually dies".
The proof needs to show: for every specific t, there exists d
such that digit(14+d) = 2.
""")
