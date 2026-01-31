#!/usr/bin/env python3
"""
Investigate the persistence lemma for powers of 4.

Key question: Why does 64 → 256 "recover" (lose digit 2) but
1024 and beyond never recover?

The answer lies in the STRUCTURE of numbers that can be multiplied
by 4 without producing digit 2.
"""

def to_base3(n):
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return digits

def has_digit_2(n):
    return 2 in to_base3(n)

def has_consecutive_ones(n):
    """Check if n has consecutive 1s in base 3."""
    digits = to_base3(n)
    for i in range(len(digits) - 1):
        if digits[i] == 1 and digits[i+1] == 1:
            return True
    return False

def can_multiply_without_2(x):
    """
    Check if 4*x has no digit 2.

    Returns (True, result) if 4*x has no digit 2, else (False, result).
    """
    result = 4 * x
    return (not has_digit_2(result), result)

def analyze_recovery_conditions():
    """
    What conditions allow a number X with digit 2 to produce 4X without digit 2?
    """
    print("=" * 70)
    print("ANALYZING RECOVERY CONDITIONS")
    print("=" * 70)

    print("\nSearching for X with digit 2 such that 4X has no digit 2...")
    print("(This is the 'recovery' phenomenon we saw with 64 → 256)")
    print()

    recoveries = []
    for x in range(1, 10000):
        if has_digit_2(x):
            can_mult, result = can_multiply_without_2(x)
            if can_mult:
                recoveries.append((x, result))

    print(f"Found {len(recoveries)} recovery cases in [1, 10000]:")
    for x, result in recoveries[:30]:
        digits_x = to_base3(x)
        digits_r = to_base3(result)
        consec_x = "has 11" if has_consecutive_ones(x) else "no 11"
        consec_r = "has 11" if has_consecutive_ones(result) else "no 11"
        print(f"  {x:5d} ({digits_x}) → {result:5d} ({digits_r}) | input: {consec_x}, output: {consec_r}")

    if len(recoveries) > 30:
        print(f"  ... and {len(recoveries) - 30} more")

    return recoveries

def analyze_no_recovery_after_256():
    """
    Key question: Why can't any power of 4 beyond 256 recover?

    Hypothesis: 256's output structure (consecutive 1s) creates a trap.
    """
    print("\n" + "=" * 70)
    print("ANALYZING THE 256 TRAP")
    print("=" * 70)

    print("\nThe chain from 64 to 256:")
    print("  64 = [1, 0, 1, 2] → 256 = [1, 1, 1, 0, 0, 1]")
    print()
    print("Key observations:")
    print("  - 64 has digit 2 but NO consecutive 1s in positions 0,1,2")
    print("  - 256 has NO digit 2 but HAS consecutive 1s (positions 0,1,2)")
    print("  - The consecutive 1s FORCE 1024 to have digit 2")
    print()

    print("Now let's check: what pattern does 1024 have?")
    p = 1024
    digits = to_base3(p)
    has_2 = has_digit_2(p)
    consec = has_consecutive_ones(p)
    print(f"  1024 = {digits} (LSB first)")
    print(f"  Has digit 2: {has_2}")
    print(f"  Has consecutive 1s: {consec}")
    print()

    # Check if 1024 could potentially recover
    print("If 1024 could 'recover' to produce 4096 without digit 2:")
    print("  4096 would need to avoid digit 2")
    can_mult, result = can_multiply_without_2(1024)
    print(f"  4 × 1024 = 4096, has digit 2: {not can_mult}")
    print()

    # The key insight
    print("THE KEY INSIGHT:")
    print("  For X to 'recover' (produce 4X without digit 2), X must satisfy:")
    print("    1. X can have digit 2")
    print("    2. But the ×4 multiplication must avoid outputting digit 2")
    print()
    print("  This requires specific structural conditions on X's digits.")
    print("  Let's find what those conditions are...")

def find_recovery_pattern():
    """
    Find the pattern that allows recovery.
    """
    print("\n" + "=" * 70)
    print("FINDING THE RECOVERY PATTERN")
    print("=" * 70)

    # For each recovery case, analyze the digit 2 position and surrounding context
    print("\nAnalyzing recovery cases in detail:")
    print()

    for x in range(1, 3000):
        if has_digit_2(x):
            can_mult, result = can_multiply_without_2(x)
            if can_mult:
                digits_x = to_base3(x)
                digits_r = to_base3(result)

                # Find position of digit 2 in x
                pos_2 = [i for i, d in enumerate(digits_x) if d == 2]

                print(f"  X = {x:4d} = {digits_x}")
                print(f"    Digit 2 at positions: {pos_2}")

                # Check the context around each digit 2
                for p in pos_2:
                    prev = digits_x[p-1] if p > 0 else 0
                    next_ = digits_x[p+1] if p+1 < len(digits_x) else 0
                    print(f"    Position {p}: context = [{prev}, 2, {next_}]")

                print(f"    Result = {digits_r}, consecutive 1s: {has_consecutive_ones(result)}")
                print()

                if x > 200:
                    print("  ... (stopping at X > 200)")
                    break

def prove_no_recovery_after_256():
    """
    Attempt to prove that no power of 4 beyond 256 can lack digit 2.
    """
    print("\n" + "=" * 70)
    print("PROOF ATTEMPT: NO RECOVERY AFTER 256")
    print("=" * 70)

    print("""
The argument:

1. 256 = [1, 1, 1, 0, 0, 1] has consecutive 1s at positions 0, 1, 2.

2. When computing 4 × 256:
   - Position 1: d[1]=1, d[0]=1, carry=0 → sum=2 → OUTPUT DIGIT 2
   - Therefore 1024 has digit 2.

3. For 1024 to "recover" (i.e., 4096 has no digit 2), we need:
   - 1024's digit-2 positions to be "neutralized" by the ×4 operation
   - But this is constrained by the automaton rules

4. 1024 = [1, 2, 2, 1, 0, 1, 1]:
   - Has digit 2 at positions 1 and 2
   - When computing 4 × 1024:
     * Position 0: d[0]=1, d[-1]=0, carry=0 → sum=1 → OK
     * Position 1: d[1]=2, d[0]=1, carry=0 → sum=3 → out=0, carry=1
     * Position 2: d[2]=2, d[1]=2, carry=1 → sum=5 → out=2, carry=1 ← DIGIT 2!
""")

    # Verify this trace
    digits_1024 = to_base3(1024)
    print(f"Verification: 1024 = {digits_1024}")

    # Trace ×4
    result = []
    carry = 0
    extended = digits_1024 + [0, 0, 0]

    print("\nTrace of 4 × 1024:")
    for i in range(len(extended)):
        d_i = extended[i]
        d_prev = extended[i-1] if i > 0 else 0
        total = d_i + d_prev + carry
        out = total % 3
        new_carry = total // 3
        result.append(out)
        marker = " ← DIGIT 2!" if out == 2 else ""
        print(f"  pos {i}: d[{i}]={d_i} + d[{i-1}]={d_prev} + carry={carry} = {total} → out={out}{marker}")
        carry = new_carry
        if i > 8:
            break

    print(f"\n4 × 1024 = 4096, has digit 2: {has_digit_2(4096)}")

    print("""
5. The pattern continues:
   - Each power of 4 beyond 256 has digit 2
   - Each multiplication creates new digit 2s or preserves existing ones
   - The "consecutive 2s" or "2 with adjacent 2 or 1" patterns prevent recovery

6. The key difference from 64 → 256:
   - 64 = [1, 0, 1, 2]: the digit 2 is at the END (position 3)
   - There's a 0 at position 1, which breaks the "bad" pattern
   - This allows recovery to 256

   - 1024 = [1, 2, 2, 1, 0, 1, 1]: digit 2s are at positions 1 and 2
   - Adjacent to each other and to 1s
   - No "gap" to allow recovery
""")

def check_all_powers():
    """
    Exhaustively check all powers of 4 up to high limit.
    """
    print("\n" + "=" * 70)
    print("EXHAUSTIVE CHECK OF POWERS OF 4")
    print("=" * 70)

    max_m = 100
    solutions = []

    for m in range(max_m + 1):
        power = 4 ** m
        if not has_digit_2(power):
            solutions.append(m)
            digits = to_base3(power)
            consec = has_consecutive_ones(power)
            print(f"  4^{m:3d} = {power} has NO digit 2, consecutive 1s: {consec}")

    print(f"\nSolutions for m in [0, {max_m}]: {solutions}")
    print(f"Corresponding n = 2m: {[2*m for m in solutions]}")

    if solutions == [0, 1, 4]:
        print("\n✓ CONFIRMED: Only m ∈ {0, 1, 4} have 4^m without digit 2")
        print("✓ CONFIRMED: Only n ∈ {0, 2, 8} have 2^n without digit 2")
        return True
    else:
        print("\n✗ UNEXPECTED: Found additional solutions!")
        return False

def main():
    analyze_recovery_conditions()
    analyze_no_recovery_after_256()
    find_recovery_pattern()
    prove_no_recovery_after_256()
    confirmed = check_all_powers()

    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    if confirmed:
        print("""
The persistence lemma is VERIFIED computationally for m ≤ 100.

The structural argument:
1. 256 has consecutive 1s, forcing 1024 to have digit 2
2. 1024 has adjacent digit 2s (positions 1 and 2)
3. These adjacent 2s create a "trap" that prevents recovery
4. Each subsequent power inherits or creates new digit 2 patterns

The formal proof would require showing:
- Any 4^m for m > 4 with no digit 2 would need a specific structure
- That structure is impossible given the multiplication dynamics
- This is essentially a finite-state argument on digit patterns

For a complete formal proof, we would formalize the automaton
and prove that no accepting path (no digit 2) exists for m > 4.
""")
    else:
        print("Unexpected result - need to investigate further.")

if __name__ == "__main__":
    main()
