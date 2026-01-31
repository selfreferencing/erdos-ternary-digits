#!/usr/bin/env python3
"""
Fast version: Find K such that all orbit elements mod 3^K have blocking pattern.
Use flush to see output immediately.
"""
import sys

def to_base3(n, num_digits):
    digits = []
    for _ in range(num_digits):
        digits.append(n % 3)
        n //= 3
    return digits

def has_pattern(digits):
    """Check if digits contain blocking pattern."""
    for i in range(len(digits) - 1):
        pair = (digits[i], digits[i+1])
        if pair in [(2, 2), (0, 2), (1, 1)]:
            return True
    return False

print("Checking orbit {4^m mod 3^k} for blocking patterns", flush=True)
print("=" * 60, flush=True)

# Period of 4^m mod 3^k is 3^(k-1) for k >= 2
# So orbit size grows as 3^(k-1)

# k=3: period 9, k=10: period 19683, k=15: period ~4.7M

for k in range(3, 13):  # Limit to k=12 for speed
    period = 3 ** (k - 1)
    check_mod = 3 ** k

    no_pattern_count = 0
    no_pattern_examples = []

    val = 1
    for i in range(period):
        digits = to_base3(val, k)
        if not has_pattern(digits):
            no_pattern_count += 1
            if len(no_pattern_examples) < 3:
                no_pattern_examples.append(digits)
        val = (val * 4) % check_mod

    if no_pattern_count == 0:
        print(f"k={k:2d}: ✓ ALL {period} orbit elements have pattern!", flush=True)
        print(f"\n*** CRITICAL K FOUND: k = {k} ***", flush=True)
        print(f"Every 4^m mod 3^{k} has a blocking pattern in first {k} digits.", flush=True)
        print("This gives a complete analytic proof!", flush=True)
        break
    else:
        print(f"k={k:2d}: ✗ {no_pattern_count}/{period} orbit elements lack pattern", flush=True)
        for ex in no_pattern_examples[:2]:
            print(f"       Example: {ex}", flush=True)
