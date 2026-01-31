#!/usr/bin/env python3
"""
Attempting to close the analytic gap in the Conservation Lemma.

Strategy: Find K such that for EVERY residue class r mod 3^K,
the first K digits of 4^r contain a blocking pattern.

Key fact: The first k digits of 4^m are determined by 4^m mod 3^k,
which depends only on m mod 3^(k-1) (for k ≥ 2).

So if we check all residue classes mod 3^K and all have patterns
in their first K+1 digits, we have an analytic proof.
"""

def to_base3(n, num_digits=None):
    """Convert n to base 3, LSB first, padded to num_digits if specified."""
    if n == 0:
        digits = [0]
    else:
        digits = []
        while n > 0:
            digits.append(n % 3)
            n //= 3
    if num_digits:
        while len(digits) < num_digits:
            digits.append(0)
    return digits

def first_pattern_position(digits):
    """Find position of first blocking pattern in digit list."""
    for i in range(len(digits) - 1):
        pair = (digits[i], digits[i+1])
        if pair in [(2, 2), (0, 2), (1, 1)]:
            return i, pair
    return None, None

print("=" * 80)
print("ANALYTIC CLOSURE ATTEMPT")
print("=" * 80)

print("""
Goal: Find K such that for every r in [0, 3^K), the first K+1 digits
of 4^r mod 3^(K+1) contain a blocking pattern.

This would give a complete analytic proof because:
1. First K+1 digits of 4^m depend only on m mod 3^K
2. If all residue classes have patterns in first K+1 digits,
   then ALL 4^m have patterns (for m ≥ some threshold)
""")

# Check increasing values of K
for K in range(2, 10):
    modulus = 3 ** K
    check_mod = 3 ** (K + 1)  # To get first K+1 digits

    all_have_pattern = True
    worst_case = None
    max_pattern_pos = -1

    for r in range(modulus):
        # Skip r < 5 (handled separately)
        if r < 5:
            test_m = r + modulus  # Use r + 3^K instead
        else:
            test_m = r

        # Get first K+1 digits
        val = pow(4, test_m, check_mod)
        digits = to_base3(val, K + 1)

        pos, pattern = first_pattern_position(digits)

        if pos is None:
            all_have_pattern = False
            worst_case = (r, digits)
        else:
            max_pattern_pos = max(max_pattern_pos, pos)

    if all_have_pattern:
        print(f"K = {K}: ✓ ALL {modulus} residue classes have pattern in first {K+1} digits")
        print(f"         Max pattern position: {max_pattern_pos}")
    else:
        print(f"K = {K}: ✗ Some residue classes lack pattern in first {K+1} digits")
        print(f"         Example: r = {worst_case[0]}, digits = {worst_case[1]}")

print("\n" + "=" * 80)
print("DEEPER ANALYSIS: Finding the critical K")
print("=" * 80)

# Find the minimum K where all classes have patterns
critical_K = None
for K in range(2, 15):
    modulus = 3 ** K
    check_mod = 3 ** (K + 1)

    all_have_pattern = True
    no_pattern_classes = []

    for r in range(modulus):
        test_m = r if r >= 5 else r + modulus
        val = pow(4, test_m, check_mod)
        digits = to_base3(val, K + 1)
        pos, _ = first_pattern_position(digits)

        if pos is None:
            all_have_pattern = False
            no_pattern_classes.append(r)

    if all_have_pattern:
        critical_K = K
        print(f"\n✓ CRITICAL K = {K}")
        print(f"  All {modulus} residue classes mod 3^{K} have blocking pattern")
        print(f"  in their first {K+1} digits.")
        break
    else:
        print(f"K = {K}: {len(no_pattern_classes)} classes without pattern in first {K+1} digits")
        if len(no_pattern_classes) <= 10:
            print(f"         Classes: {no_pattern_classes}")

if critical_K is None:
    print("\nNo critical K found up to K=14. Need deeper analysis.")

print("\n" + "=" * 80)
print("ALTERNATIVE: Pattern position by residue class")
print("=" * 80)

print("""
Alternative approach: Show that the pattern position k(m) depends only
on m mod 3^j for some fixed j, and is always bounded.
""")

# For each residue class mod 243, find max pattern position across many instances
from collections import defaultdict

modulus = 243  # 3^5
max_pos_by_class = defaultdict(int)
pattern_positions = defaultdict(list)

for m in range(5, 50000):
    r = m % modulus
    power = 4 ** m
    digits = to_base3(power)
    pos, _ = first_pattern_position(digits)

    if pos is not None:
        max_pos_by_class[r] = max(max_pos_by_class[r], pos)
        if len(pattern_positions[r]) < 100:
            pattern_positions[r].append((m, pos))

# Find global maximum
global_max = max(max_pos_by_class.values())
print(f"Global maximum pattern position (m < 50000): {global_max}")

# Which classes achieve this maximum?
max_classes = [r for r, p in max_pos_by_class.items() if p == global_max]
print(f"Achieved by {len(max_classes)} residue classes mod 243")

# Distribution of max positions
from collections import Counter
pos_dist = Counter(max_pos_by_class.values())
print(f"\nDistribution of max pattern positions by class:")
for pos in sorted(pos_dist.keys()):
    print(f"  Position {pos:2d}: {pos_dist[pos]:3d} classes")

print("\n" + "=" * 80)
print("KEY INSIGHT: Checking if pattern position stabilizes")
print("=" * 80)

# For the classes with highest max position, check if it keeps growing
# or stabilizes
print("\nFor classes with max position ≥ 10:")
high_pos_classes = [r for r, p in max_pos_by_class.items() if p >= 10]

for r in high_pos_classes[:5]:  # Check first 5
    positions = [pos for m, pos in pattern_positions[r]]
    print(f"\n  r = {r} (mod 243): positions = {positions[:20]}...")

    # Check later instances (m > 10000)
    late_positions = []
    for m in range(10000 + r, 50000, 243):
        power = 4 ** m
        digits = to_base3(power)
        pos, _ = first_pattern_position(digits)
        if pos is not None:
            late_positions.append(pos)

    if late_positions:
        print(f"    Late positions (m > 10000): max = {max(late_positions)}, sample = {late_positions[:10]}")

print("\n" + "=" * 80)
print("THE ANALYTIC ARGUMENT")
print("=" * 80)

# Check if we can prove the bound analytically
print("""
CLAIM: For m ≥ 5, the first blocking pattern in 4^m appears at position
       k(m) where k(m) is bounded by some constant K_max.

PROOF ATTEMPT:

1. The digit at position j of 4^m depends only on 4^m mod 3^(j+1).

2. 4^m mod 3^(j+1) depends only on m mod 3^j (since 4^(3^j) ≡ 1 mod 3^(j+1)).

3. So for each j, there are exactly 3^j possible values for
   (digit_0, digit_1, ..., digit_j).

4. The DFA accepting "no blocking pattern" sequences has transfer matrix:

   A = [[1, 1, 1],    (from digit 0)
        [1, 0, 1],    (from digit 1)
        [0, 1, 0]]    (from digit 2)

   Eigenvalues: 2, 0, -1. Dominant eigenvalue = 2.

5. Number of valid n-digit sequences ≈ C · 2^n.
   Total n-digit ternary sequences = 3^n.
   Ratio: (2/3)^n → 0 exponentially.

6. For 4^m to avoid all patterns in first n digits, its first n digits
   must be one of the ~2^n valid sequences out of 3^n total.

7. The key question: Does {4^m mod 3^n : m ∈ ℕ} "avoid" the valid sequences,
   or does it eventually hit a pattern?
""")

# Check: what fraction of residue classes mod 3^k have patterns?
print("\nFraction of residue classes with pattern in first k digits:")
for k in range(2, 12):
    modulus = 3 ** (k - 1)
    check_mod = 3 ** k

    has_pattern = 0
    for r in range(modulus):
        m = r if r >= 5 else r + modulus
        val = pow(4, m, check_mod)
        digits = to_base3(val, k)
        pos, _ = first_pattern_position(digits)
        if pos is not None:
            has_pattern += 1

    frac = has_pattern / modulus
    print(f"  k = {k:2d}: {has_pattern:6d} / {modulus:6d} = {frac:.4f} ({frac*100:.1f}%)")

print("\n" + "=" * 80)
print("CHECKING THE ORBIT STRUCTURE")
print("=" * 80)

print("""
The sequence 4^m mod 3^k has period 3^(k-1).

So the set {4^m mod 3^k : m ≥ 0} has exactly 3^(k-1) distinct elements.

Question: Among these 3^(k-1) residue classes, do ANY avoid all patterns
in their first k digits?
""")

# For each k, check if any residue class avoids patterns
for k in range(3, 15):
    period = 3 ** (k - 1)
    check_mod = 3 ** k

    # Generate all values in the orbit
    orbit = set()
    val = 1
    for _ in range(period):
        orbit.add(val)
        val = (val * 4) % check_mod

    # Check each for patterns
    no_pattern_count = 0
    no_pattern_examples = []

    for v in orbit:
        digits = to_base3(v, k)
        pos, _ = first_pattern_position(digits)
        if pos is None:
            no_pattern_count += 1
            if len(no_pattern_examples) < 3:
                no_pattern_examples.append((v, digits))

    if no_pattern_count == 0:
        print(f"k = {k:2d}: ✓ ALL {period} orbit elements have pattern in first {k} digits")
    else:
        print(f"k = {k:2d}: ✗ {no_pattern_count} orbit elements lack pattern")
        for v, d in no_pattern_examples:
            print(f"         Example: {v} = {d}")
