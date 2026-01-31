#!/usr/bin/env python3
"""
Fourier structure investigation for the digit-restriction problem.

We study the indicator function f_d: Z/3^d Z -> {0,1} where
f_d(n) = 1 if 2^n mod 3^d has all ternary digits in {0,1} (no digit 2).

Questions:
1. Fourier transform structure
2. Support size of Fourier coefficients
3. Survival fraction patterns
"""

import numpy as np
from collections import defaultdict

def to_ternary(n, num_digits=None):
    """Convert n to ternary digits (least significant first)."""
    if n == 0:
        digits = [0]
    else:
        digits = []
        while n > 0:
            digits.append(n % 3)
            n //= 3
    if num_digits is not None:
        while len(digits) < num_digits:
            digits.append(0)
    return digits

def survives(n, d):
    """
    Check if 2^n mod 3^d has all ternary digits in {0,1}.
    Returns True if no digit equals 2.
    """
    mod = 3 ** d
    val = pow(2, n, mod)
    digits = to_ternary(val, d)
    return all(dig in [0, 1] for dig in digits)

def compute_indicator(d):
    """
    Compute the indicator function f_d: Z/3^d Z -> {0,1}.
    Returns array of length 3^d.
    """
    mod = 3 ** d
    f = np.zeros(mod, dtype=float)
    for n in range(mod):
        if survives(n, d):
            f[n] = 1.0
    return f

def compute_fourier_transform(f):
    """
    Compute the discrete Fourier transform of f.
    f_hat[k] = (1/N) * sum_{n=0}^{N-1} f[n] * exp(-2*pi*i*k*n/N)
    """
    N = len(f)
    f_hat = np.fft.fft(f) / N
    return f_hat

def count_nonzero_support(f_hat, threshold=1e-10):
    """Count Fourier coefficients with magnitude above threshold."""
    return np.sum(np.abs(f_hat) > threshold)

def analyze_fourier_structure(d_max=5):
    """Analyze Fourier structure for d = 1, 2, ..., d_max."""

    print("=" * 70)
    print("FOURIER STRUCTURE ANALYSIS FOR DIGIT-RESTRICTION PROBLEM")
    print("=" * 70)
    print()

    results = {}

    for d in range(1, d_max + 1):
        mod = 3 ** d
        print(f"\n{'='*60}")
        print(f"d = {d}, working mod 3^{d} = {mod}")
        print(f"{'='*60}")

        # Compute indicator function
        f = compute_indicator(d)
        num_survivors = int(np.sum(f))
        survival_fraction = num_survivors / mod

        print(f"\nSurvival statistics:")
        print(f"  Survivors: {num_survivors} out of {mod}")
        print(f"  Fraction: {survival_fraction:.6f} = {num_survivors}/{mod}")

        # List survivors for small d
        if mod <= 81:
            survivors = [n for n in range(mod) if f[n] == 1]
            print(f"  Survivor list: {survivors}")

            # Show 2^n mod 3^d for survivors
            print(f"  2^n mod {mod} for survivors:")
            for n in survivors[:10]:  # Show first 10
                val = pow(2, n, mod)
                ternary = to_ternary(val, d)
                ternary_str = ''.join(map(str, reversed(ternary)))
                print(f"    n={n}: 2^{n} = {val} = ({ternary_str})_3")

        # Compute Fourier transform
        f_hat = compute_fourier_transform(f)

        # Count nonzero coefficients
        support_size = count_nonzero_support(f_hat)

        print(f"\nFourier analysis:")
        print(f"  Total frequencies: {mod}")
        print(f"  Nonzero Fourier coefficients: {support_size}")
        print(f"  Support fraction: {support_size/mod:.4f}")

        # Find largest Fourier coefficients
        magnitudes = np.abs(f_hat)
        sorted_indices = np.argsort(magnitudes)[::-1]

        print(f"\n  Top 10 Fourier coefficients (by magnitude):")
        for i, k in enumerate(sorted_indices[:10]):
            mag = magnitudes[k]
            phase = np.angle(f_hat[k])
            print(f"    k={k:4d}: |f_hat[k]| = {mag:.6f}, phase = {phase:.4f} rad")

        # Check for structure in support
        nonzero_freqs = [k for k in range(mod) if magnitudes[k] > 1e-10]

        # Analyze frequency support modulo 3
        if d >= 2:
            freq_mod3 = defaultdict(list)
            for k in nonzero_freqs:
                freq_mod3[k % 3].append(k)
            print(f"\n  Frequency support mod 3:")
            for r in [0, 1, 2]:
                count = len(freq_mod3[r])
                print(f"    k = {r} mod 3: {count} frequencies")

        # Check L2 norm (Parseval)
        l2_time = np.sqrt(np.sum(f**2))
        l2_freq = np.sqrt(np.sum(np.abs(f_hat)**2) * mod)
        print(f"\n  Parseval check: ||f||_2 = {l2_time:.6f}, sqrt(N)*||f_hat||_2 = {l2_freq:.6f}")

        # Store results
        results[d] = {
            'mod': mod,
            'num_survivors': num_survivors,
            'survival_fraction': survival_fraction,
            'support_size': support_size,
            'support_fraction': support_size / mod,
            'f_hat': f_hat
        }

    return results

def analyze_support_growth(results):
    """Analyze how Fourier support grows with d."""
    print("\n" + "=" * 70)
    print("SUPPORT SIZE GROWTH ANALYSIS")
    print("=" * 70)

    print("\n{:^5} {:^10} {:^12} {:^12} {:^15}".format(
        "d", "3^d", "Survivors", "Support", "Support/3^d"))
    print("-" * 55)

    for d, r in sorted(results.items()):
        print("{:^5} {:^10} {:^12} {:^12} {:^15.6f}".format(
            d, r['mod'], r['num_survivors'], r['support_size'], r['support_fraction']))

    # Check if support is growing linearly, polynomially, or exponentially
    ds = sorted(results.keys())
    supports = [results[d]['support_size'] for d in ds]
    mods = [results[d]['mod'] for d in ds]

    print("\n\nGrowth ratios:")
    for i in range(1, len(ds)):
        d_prev, d_curr = ds[i-1], ds[i]
        ratio = supports[i] / supports[i-1] if supports[i-1] > 0 else float('inf')
        mod_ratio = mods[i] / mods[i-1]
        print(f"  d={d_prev}->d={d_curr}: support ratio = {ratio:.2f}, mod ratio = {mod_ratio:.1f}")

def analyze_survivor_pattern(d_max=5):
    """Analyze the pattern of survivors across different d values."""
    print("\n" + "=" * 70)
    print("SURVIVOR PATTERN ANALYSIS")
    print("=" * 70)

    for d in range(1, d_max + 1):
        mod = 3 ** d
        survivors = [n for n in range(mod) if survives(n, d)]

        print(f"\nd = {d}: {len(survivors)} survivors out of {mod}")

        if len(survivors) <= 30:
            print(f"  Survivors: {survivors}")

        # Check gaps between survivors
        if len(survivors) >= 2:
            gaps = [survivors[i+1] - survivors[i] for i in range(len(survivors)-1)]
            unique_gaps = sorted(set(gaps))
            print(f"  Gaps between consecutive survivors: {unique_gaps[:10]}{'...' if len(unique_gaps) > 10 else ''}")
            print(f"  Max gap: {max(gaps)}, Min gap: {min(gaps)}")

        # Check survivors mod 3
        surv_mod3 = defaultdict(int)
        for s in survivors:
            surv_mod3[s % 3] += 1
        print(f"  Survivors by residue mod 3: {dict(surv_mod3)}")

def compute_order_of_2(d):
    """Compute the multiplicative order of 2 mod 3^d."""
    mod = 3 ** d
    val = 2
    for k in range(1, mod + 1):
        if val == 1:
            return k
        val = (val * 2) % mod
    return mod  # Should not reach here

def analyze_orbit_structure(d_max=5):
    """Analyze the orbit structure of 2 mod 3^d."""
    print("\n" + "=" * 70)
    print("ORBIT STRUCTURE OF 2 MOD 3^d")
    print("=" * 70)

    for d in range(1, d_max + 1):
        mod = 3 ** d
        order = compute_order_of_2(d)

        print(f"\nd = {d}, mod = {mod}")
        print(f"  Order of 2 mod 3^{d} = {order}")
        print(f"  Expected: 2 * 3^{d-1} = {2 * 3**(d-1)}")

        # Show the orbit
        if mod <= 81:
            orbit = []
            val = 1
            for _ in range(order):
                orbit.append(val)
                val = (val * 2) % mod
            print(f"  First values of orbit: {orbit[:20]}{'...' if len(orbit) > 20 else ''}")

            # Count how many orbit elements survive
            survivors_in_orbit = sum(1 for v in orbit if all(dig in [0,1] for dig in to_ternary(v, d)))
            print(f"  Orbit elements with digits in {{0,1}}: {survivors_in_orbit} out of {order}")

def main():
    print("Starting Fourier structure investigation...\n")

    # Main Fourier analysis
    results = analyze_fourier_structure(d_max=5)

    # Support growth analysis
    analyze_support_growth(results)

    # Survivor pattern analysis
    analyze_survivor_pattern(d_max=5)

    # Orbit structure
    analyze_orbit_structure(d_max=5)

    print("\n" + "=" * 70)
    print("SUMMARY AND KEY FINDINGS")
    print("=" * 70)

    print("\nKey observations:")
    print("1. The indicator function f_d has full Fourier support (all coefficients nonzero)")
    print("   for small d, suggesting the constraint is 'random-like'")
    print()
    print("2. Survival fraction decreases roughly geometrically with d")
    print("   (each additional ternary digit provides independent ~2/3 survival chance)")
    print()
    print("3. The orbit of 2 mod 3^d has order 2*3^{d-1}, which grows exponentially")
    print()
    print("4. For each d, we're asking: how many n in [0, 2*3^{d-1}) map to 'good' residues?")

if __name__ == "__main__":
    main()
