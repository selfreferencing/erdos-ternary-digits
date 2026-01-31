#!/usr/bin/env python3
"""
Attempt to close the gap: prove a property that ALWAYS holds for 4^m when m >= 5.

Key observation: The three recovery conditions are:
  (a) All digit 2s in context (d, 2, 0) with d ∈ {0, 1}
  (b) No (0, 2) pairs
  (c) No consecutive 1s

We need to prove that for m >= 5, at least one is ALWAYS violated.

Approach: Find the "simplest" violation that persists.
"""

def to_base3(n):
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return digits

def analyze_violations(n):
    """Analyze which recovery conditions are violated."""
    digits = to_base3(n)

    # Condition (a): Check digit 2 contexts
    bad_contexts = []
    for i, d in enumerate(digits):
        if d == 2:
            prev = digits[i-1] if i > 0 else 0
            next_ = digits[i+1] if i+1 < len(digits) else 0
            is_recovery = (next_ == 0 and prev in [0, 1])
            if not is_recovery:
                bad_contexts.append((i, prev, 2, next_))

    # Condition (b): Check (0, 2) pairs
    pairs_02 = []
    for i in range(len(digits) - 1):
        if (digits[i], digits[i+1]) == (0, 2):
            pairs_02.append(i)

    # Condition (c): Check consecutive 1s
    consec_1s = []
    for i in range(len(digits) - 1):
        if digits[i] == 1 and digits[i+1] == 1:
            consec_1s.append(i)

    return {
        'bad_contexts': bad_contexts,
        'pairs_02': pairs_02,
        'consec_1s': consec_1s
    }

print("=" * 80)
print("ANALYZING VIOLATION PATTERNS IN POWERS OF 4")
print("=" * 80)

print("\nFor each 4^m (m >= 5), which conditions are violated?")
print()

violation_patterns = []

for m in range(5, 51):
    power = 4 ** m
    v = analyze_violations(power)

    pattern = []
    if v['bad_contexts']:
        pattern.append('(a)')
    if v['pairs_02']:
        pattern.append('(b)')
    if v['consec_1s']:
        pattern.append('(c)')

    violation_patterns.append((m, pattern, v))

    if m <= 15:
        print(f"4^{m:2d}: violations = {pattern}")
        if v['bad_contexts']:
            print(f"       bad contexts: {v['bad_contexts'][:3]}...")
        if v['consec_1s']:
            print(f"       consecutive 1s at: {v['consec_1s'][:3]}...")

# Analyze patterns
print("\n" + "=" * 80)
print("VIOLATION STATISTICS")
print("=" * 80)

counts = {'(a)': 0, '(b)': 0, '(c)': 0}
for m, pattern, v in violation_patterns:
    for p in pattern:
        counts[p] += 1

print(f"\nOut of 46 powers (m = 5 to 50):")
for p, c in counts.items():
    print(f"  Condition {p} violated: {c} times ({100*c/46:.1f}%)")

# Check if (a) alone is always violated
print("\n" + "=" * 80)
print("IS CONDITION (a) ALWAYS VIOLATED?")
print("=" * 80)

always_a = all('(a)' in pattern for m, pattern, v in violation_patterns)
print(f"\nCondition (a) violated for ALL m from 5 to 50: {always_a}")

if always_a:
    print("\n✓ THIS IS THE KEY! Condition (a) is ALWAYS violated.")
    print("  Every 4^m for m >= 5 has at least one digit 2 NOT in recovery context.")

# Analyze WHY (a) is always violated
print("\n" + "=" * 80)
print("WHY IS CONDITION (a) ALWAYS VIOLATED?")
print("=" * 80)

print("\nFor 4^m to satisfy condition (a):")
print("  Every digit 2 must be followed by 0 and preceded by 0 or 1")
print("  i.e., context must be (0,2,0) or (1,2,0)")
print()

# Look at what FOLLOWS digit 2 in powers of 4
following_digit_2 = {0: 0, 1: 0, 2: 0}
preceding_digit_2 = {0: 0, 1: 0, 2: 0}

for m in range(5, 101):
    power = 4 ** m
    digits = to_base3(power)

    for i, d in enumerate(digits):
        if d == 2:
            next_ = digits[i+1] if i+1 < len(digits) else 0
            prev = digits[i-1] if i > 0 else 0
            following_digit_2[next_] += 1
            preceding_digit_2[prev] += 1

total_2s = sum(following_digit_2.values())
print(f"Digit following a 2 in 4^m (m = 5 to 100): [total: {total_2s}]")
for d, c in following_digit_2.items():
    recovery = " ← required for recovery" if d == 0 else ""
    print(f"  followed by {d}: {c} times ({100*c/total_2s:.1f}%){recovery}")

print()
print("Digit preceding a 2:")
for d, c in preceding_digit_2.items():
    recovery = " ← OK for recovery" if d in [0, 1] else " ← blocks recovery"
    print(f"  preceded by {d}: {c} times ({100*c/total_2s:.1f}%){recovery}")

# KEY INSIGHT: digit 2 is often followed by another 2
print("\n" + "=" * 80)
print("KEY INSIGHT: DIGIT 2 CLUSTERING")
print("=" * 80)

print(f"""
The data shows:
  - {following_digit_2[2]} out of {total_2s} digit 2s are followed by another 2
  - This is {100*following_digit_2[2]/total_2s:.1f}% of all digit 2s
  - Only {following_digit_2[0]} ({100*following_digit_2[0]/total_2s:.1f}%) are followed by 0 (required for recovery)

The 2s tend to "cluster" - they appear in runs like ...22... or ...222...

This clustering is WHY recovery fails: even when a 2 is followed by 0,
the NEXT 2 in the number is likely not in recovery context.
""")

# Final check: is there a m >= 5 where all digit 2s are isolated (each followed by 0)?
print("\n" + "=" * 80)
print("ARE THERE ANY 4^m (m >= 5) WITH ALL DIGIT 2s ISOLATED?")
print("=" * 80)

for m in range(5, 101):
    power = 4 ** m
    digits = to_base3(power)

    all_followed_by_0 = True
    for i, d in enumerate(digits):
        if d == 2:
            next_ = digits[i+1] if i+1 < len(digits) else 0
            if next_ != 0:
                all_followed_by_0 = False
                break

    if all_followed_by_0:
        print(f"4^{m} has all digit 2s followed by 0")
        # Check other conditions
        v = analyze_violations(power)
        print(f"  But violates: consec_1s={v['consec_1s']}, pairs_02={v['pairs_02']}")

# Check powers of 4 in more detail
print("\n" + "=" * 80)
print("STRUCTURE OF DIGIT 2 RUNS IN POWERS OF 4")
print("=" * 80)

def get_2_runs(n):
    """Get the runs of consecutive 2s."""
    digits = to_base3(n)
    runs = []
    i = 0
    while i < len(digits):
        if digits[i] == 2:
            start = i
            while i < len(digits) and digits[i] == 2:
                i += 1
            runs.append((start, i - start))  # (position, length)
        else:
            i += 1
    return runs

print("\nRuns of consecutive 2s in 4^m:")
for m in range(5, 21):
    power = 4 ** m
    runs = get_2_runs(power)
    total_2s = sum(length for _, length in runs)

    run_lengths = [length for _, length in runs]
    max_run = max(run_lengths) if run_lengths else 0
    num_isolated = sum(1 for l in run_lengths if l == 1)

    print(f"4^{m:2d}: {len(runs)} runs, max length {max_run}, isolated 2s: {num_isolated}/{len(runs)}")

# FINAL ATTEMPT: Prove that 4^m always has adjacent 2s OR other blocking pattern
print("\n" + "=" * 80)
print("FINAL ANALYSIS: THE ADJACENCY MECHANISM")
print("=" * 80)

print("""
Key finding: When multiplying by 4:
  - Adjacent 2s (22) create output patterns that block recovery
  - Even isolated 2s can create adjacent 2s in the output

Let's trace: does 4^5 having adjacent 2s at position 1 cause 4^6 to have
a blocking pattern?
""")

for m in range(5, 15):
    power = 4 ** m
    next_power = 4 ** (m + 1)

    runs = get_2_runs(power)
    next_runs = get_2_runs(next_power)

    has_adj_2 = any(length >= 2 for _, length in runs)
    next_has_adj_2 = any(length >= 2 for _, length in next_runs)

    v = analyze_violations(power)
    next_v = analyze_violations(next_power)

    print(f"4^{m:2d}: adj_2s={has_adj_2}, consec_1s={bool(v['consec_1s'])}")
    print(f"  → 4^{m+1}: adj_2s={next_has_adj_2}, consec_1s={bool(next_v['consec_1s'])}")

print("\n" + "=" * 80)
print("CONCLUSION")
print("=" * 80)

print("""
THE GAP REMAINS:

While we've shown:
  1. Condition (a) is violated for all 4^m, m = 5 to 100
  2. The "digit 2 clustering" phenomenon explains why
  3. Only 37% of digit 2s are followed by 0 (needed for recovery)

We have NOT proven:
  - That condition (a) must be violated for ALL m >= 5
  - That the clustering persists indefinitely

POSSIBLE APPROACHES TO CLOSE THE GAP:

1. 3-adic analysis: Show that 4^m mod 3^k has a specific structure
   that forces adjacent 2s or non-recovery contexts.

2. Prove: "If 4^m has digit 2, then 4^(m+1) has adjacent 2s or consec 1s"
   This would give a simple persistence lemma.

3. Analyze the 9-state automaton paths more carefully to show
   no valid (digit-2-free) path exists for input = 4^m digits when m >= 5.

The structural argument is STRONG but not yet COMPLETE.
""")
