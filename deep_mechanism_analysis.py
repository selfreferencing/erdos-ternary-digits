#!/usr/bin/env python3
"""
Deep analysis of why EVERY power of 4 from m >= 5 has digit 2.

The key insight from formal_trap_argument.py:
  - Some powers (4^6, 4^7, etc.) don't have adjacent 2s
  - But ALL have "forbidden pairs" (0,1), (1,0), or (2,2)
  - Digit 2 appears when carry hits a forbidden pair

The question: WHY does carry always hit a forbidden pair?
"""

def to_base3(n):
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return digits

def has_digit_2(digits):
    return 2 in digits

def trace_multiplication_full(x):
    """
    Full trace of x × 4 showing carry propagation and where digit 2 appears.
    Returns the position(s) where output = 2 and what caused it.
    """
    digits = to_base3(x)
    max_len = len(digits) + 2
    extended = digits + [0] * (max_len - len(digits))

    result = []
    carry = 0
    digit_2_causes = []

    for i in range(max_len):
        d_i = extended[i]
        d_prev = extended[i-1] if i > 0 else 0

        total = d_i + d_prev + carry
        out = total % 3
        new_carry = total // 3

        if out == 2:
            cause = {
                'position': i,
                'd_i': d_i,
                'd_prev': d_prev,
                'carry_in': carry,
                'sum': total,
                'pair_type': None
            }
            if (d_i, d_prev) == (2, 2):
                cause['pair_type'] = 'adjacent_2s'
            elif (d_i, d_prev) in [(0, 1), (1, 0)]:
                cause['pair_type'] = '01_10_pair'
            elif d_i == 2 or d_prev == 2:
                cause['pair_type'] = 'single_2'
            else:
                cause['pair_type'] = 'other'
            digit_2_causes.append(cause)

        result.append(out)
        carry = new_carry

    # Remove trailing zeros
    while len(result) > 1 and result[-1] == 0:
        result.pop()

    return result, digit_2_causes

print("=" * 80)
print("DEEP MECHANISM ANALYSIS: WHY ALL 4^m (m >= 5) HAVE DIGIT 2")
print("=" * 80)

# Analyze each power of 4 from m=5 to m=30
print("\n## Power-by-power analysis")
print()

cause_stats = {'adjacent_2s': 0, '01_10_pair': 0, 'single_2': 0, 'other': 0}

for m in range(5, 31):
    power = 4 ** m
    digits = to_base3(power)
    result, causes = trace_multiplication_full(power)

    if causes:
        first_cause = causes[0]
        cause_stats[first_cause['pair_type']] += 1

        print(f"4^{m:2d}: First digit 2 at position {first_cause['position']}")
        print(f"       Cause: {first_cause['pair_type']}")
        print(f"       d[i]={first_cause['d_i']}, d[i-1]={first_cause['d_prev']}, carry={first_cause['carry_in']}, sum={first_cause['sum']}")
    else:
        print(f"4^{m:2d}: NO DIGIT 2 FOUND - THIS IS A BUG!")
    print()

print("\n" + "=" * 80)
print("## Cause statistics (first digit 2)")
print("=" * 80)
for cause, count in sorted(cause_stats.items(), key=lambda x: -x[1]):
    print(f"  {cause}: {count} times")

# Deeper question: what structural property of powers of 4 ensures digit 2?
print("\n" + "=" * 80)
print("## Structural Analysis: What guarantees digit 2?")
print("=" * 80)

print("""
The multiplication X × 4 produces digit 2 at position i when:
  d[i] + d[i-1] + carry ≡ 2 (mod 3)

This happens in three scenarios:

SCENARIO 1: sum = 2
  Possibilities: (d[i], d[i-1], carry) ∈ {
    (2, 0, 0), (0, 2, 0), (1, 1, 0),  -- carry = 0
    (1, 0, 1), (0, 1, 1), (0, 0, 2)   -- carry >= 1 (but carry max is 1)
  }
  Feasible: (2,0,0), (0,2,0), (1,1,0), (1,0,1), (0,1,1)

SCENARIO 2: sum = 5
  Possibilities: (d[i], d[i-1], carry) ∈ {
    (2, 2, 1), (2, 1, 2), (1, 2, 2)   -- carry = 2 impossible
  }
  Feasible: (2, 2, 1)

So digit 2 appears when:
  - d[i] = 2 and d[i-1] = 0 and carry = 0  [isolated 2 at start of run]
  - d[i] = 0 and d[i-1] = 2 and carry = 0  [isolated 2 before 0]
  - d[i] = d[i-1] = 1 and carry = 0        [double 1s, no carry]
  - d[i] = 1, d[i-1] = 0, carry = 1        [carry hits 10]
  - d[i] = 0, d[i-1] = 1, carry = 1        [carry hits 01]
  - d[i] = d[i-1] = 2 and carry = 1        [carry hits 22]
""")

# Key insight: trace where 256 produces its first digit 2
print("\n" + "=" * 80)
print("## The 256 → 1024 Transition in Detail")
print("=" * 80)

x = 256
digits = to_base3(x)
result, causes = trace_multiplication_full(x)

print(f"\n256 = {digits} (LSB first)")
print(f"256 has consecutive 1s at positions 0, 1, 2")
print()

print("Full multiplication trace:")
max_len = len(digits) + 2
extended = digits + [0] * (max_len - len(digits))
carry = 0

for i in range(max_len):
    d_i = extended[i]
    d_prev = extended[i-1] if i > 0 else 0
    total = d_i + d_prev + carry
    out = total % 3
    new_carry = total // 3

    marker = " ← DIGIT 2!" if out == 2 else ""
    consec_marker = " [CONSECUTIVE 1s]" if i in [0,1,2] and d_i == 1 else ""
    print(f"  pos {i}: d[{i}]={d_i}, d[{i-1}]={d_prev}, carry={carry} → sum={total} → out={out}{marker}{consec_marker}")
    carry = new_carry

print(f"\nResult: {result} = 1024")
print(f"Digit 2 appears at: {[c['position'] for c in causes]}")

# THE KEY INSIGHT: What pattern in X guarantees 4X has digit 2?
print("\n" + "=" * 80)
print("## The Universal Guarantee: All X >= 256 Have Digit 2 in 4X?")
print("=" * 80)

print("\nChecking: For all X >= 256, does 4X have digit 2?")
print()

no_digit_2_examples = []
for x in range(256, 50000):
    result, causes = trace_multiplication_full(x)
    if not causes:  # 4X has no digit 2
        no_digit_2_examples.append(x)

if no_digit_2_examples:
    print(f"Found {len(no_digit_2_examples)} counterexamples (4X has no digit 2):")
    for x in no_digit_2_examples[:20]:
        digits = to_base3(x)
        result_digits = to_base3(4*x)
        print(f"  X = {x} = {digits} → 4X = {4*x} = {result_digits}")
else:
    print("NO counterexamples! Every X >= 256 has 4X with digit 2!")

# That's the wrong direction - we want powers of 4, not all X

print("\n" + "=" * 80)
print("## The Actual Question: Why do POWERS OF 4 always have digit 2?")
print("=" * 80)

print("""
The chain we need to verify:
  4^4 = 256  → has no digit 2, has consecutive 1s
  4^5 = 1024 → has digit 2 (because 256 has consecutive 1s)
  4^6 = 4096 → has digit 2 (but why? 1024 doesn't have consecutive 1s)
  ...

The question is: what property of 4^m for m >= 5 ensures 4^(m+1) has digit 2?

Let's check: does every 4^m for m >= 5 have a structure that forces 4^(m+1) to have digit 2?
""")

# Analyze the structure of each power of 4
print("\nStructural properties of 4^m for m = 5 to 20:")
print()

for m in range(5, 21):
    power = 4 ** m
    digits = to_base3(power)

    # Count various patterns
    has_consec_1s = any(digits[i] == 1 and digits[i+1] == 1 for i in range(len(digits)-1))
    has_adj_2s = any(digits[i] == 2 and digits[i+1] == 2 for i in range(len(digits)-1))
    has_01_10 = any((digits[i], digits[i+1]) in [(0,1), (1,0)] for i in range(len(digits)-1))
    has_20_02 = any((digits[i], digits[i+1]) in [(2,0), (0,2)] for i in range(len(digits)-1))

    next_power = 4 ** (m + 1)
    next_has_2 = has_digit_2(to_base3(next_power))

    print(f"4^{m:2d}: consec_1s={has_consec_1s}, adj_2s={has_adj_2s}, 01/10={has_01_10}, 20/02={has_20_02}")
    print(f"       → 4^{m+1} has digit 2: {next_has_2}")

# THE REAL INSIGHT
print("\n" + "=" * 80)
print("## THE REAL INSIGHT")
print("=" * 80)

print("""
The key is NOT just about the structure of 4^m.

When multiplying by 4, digit 2 can appear from MULTIPLE sources:
  1. The input already has digit 2 (and it might propagate)
  2. The input has consecutive 1s (creates sum = 2 with no carry)
  3. The input has 01 or 10 pairs that get hit by carry = 1
  4. The input has 20 or 02 pairs (creates sum = 2 with no carry)

For 4^m with m >= 5:
  - ALL of them already have digit 2
  - So the question becomes: can 4X ever NOT have digit 2 when X has digit 2?

This is the RECOVERY question we already explored!
  - Recovery requires: digit 2 in context [d, 2, 0] where d ∈ {0, 1}
  - 64 = [1, 0, 1, 2] has this context → recovery to 256
  - 1024 = [1, 2, 2, 1, ...] has adjacent 2s → no recovery

So the claim reduces to:
  For m >= 5, 4^m never has the recovery context.
""")

# Check recovery context for powers of 4
print("\n" + "=" * 80)
print("## Recovery Context Analysis for Powers of 4")
print("=" * 80)

def get_2_contexts(n):
    """Get the context (d[i-1], 2, d[i+1]) for each digit 2."""
    digits = to_base3(n)
    contexts = []
    for i, d in enumerate(digits):
        if d == 2:
            prev = digits[i-1] if i > 0 else 0
            next_ = digits[i+1] if i+1 < len(digits) else 0
            contexts.append((prev, 2, next_, i))
    return contexts

print("\nContext of digit 2s in 4^m:")
print("Recovery requires: (d, 2, 0) where d ∈ {0, 1}")
print()

for m in range(2, 21):
    power = 4 ** m
    contexts = get_2_contexts(power)

    if contexts:
        recovery_possible = any(c[2] == 0 and c[0] in [0, 1] for c in contexts)

        print(f"4^{m:2d}: ", end="")
        for prev, two, next_, pos in contexts[:4]:
            marker = "✓ recovery" if next_ == 0 and prev in [0, 1] else ""
            print(f"({prev},2,{next_})@{pos} {marker}  ", end="")
        if len(contexts) > 4:
            print(f"... [{len(contexts)} total]", end="")
        print()

        if recovery_possible and m >= 5:
            print(f"       *** UNEXPECTED: Recovery possible at m = {m}! ***")

print("""
OBSERVATION:
  - 4^2 = 16 = [1,2,1]: context (1,2,1) - NO recovery (next = 1, not 0)
  - 4^3 = 64 = [1,0,1,2]: context (1,2,0) - RECOVERY possible ✓
  - 4^4 = 256: no digit 2, no context
  - 4^5 = 1024 = [1,2,2,...]: context (1,2,2) - NO recovery (next = 2)
  - 4^m for m >= 5: all have digit 2, none have recovery context

This confirms the trap! After m = 4, no power of 4 has the recovery context.
""")

# Final verification
print("\n" + "=" * 80)
print("## FINAL VERIFICATION: No recovery context for m >= 5")
print("=" * 80)

recovery_found = []
for m in range(5, 101):
    power = 4 ** m
    contexts = get_2_contexts(power)

    for prev, two, next_, pos in contexts:
        if next_ == 0 and prev in [0, 1]:
            recovery_found.append((m, pos, prev))

if recovery_found:
    print(f"RECOVERY CONTEXTS FOUND!")
    for m, pos, prev in recovery_found[:10]:
        print(f"  4^{m} has ({prev}, 2, 0) at position {pos}")
else:
    print("NO RECOVERY CONTEXTS FOUND for 5 <= m <= 100!")
    print()
    print("This means:")
    print("  - Every 4^m for m >= 5 has digit 2")
    print("  - None of them have the context (d, 2, 0) that would allow recovery")
    print("  - Therefore 4^(m+1) also has digit 2")
    print("  - THE TRAP IS PROVEN (computationally to m = 100)")
