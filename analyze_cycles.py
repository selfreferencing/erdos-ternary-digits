#!/usr/bin/env python3
"""
Analyze cycles in the carry automaton for Erdős conjecture.
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

def from_base3(digits):
    """Convert base 3 digits (LSB first) to integer."""
    result = 0
    for i, d in enumerate(digits):
        result += d * (3 ** i)
    return result

def has_digit_2(n):
    """Check if n has digit 2 in base 3."""
    while n > 0:
        if n % 3 == 2:
            return True
        n //= 3
    return False

def double_with_trace(n):
    """Double n and trace the carry propagation."""
    digits = to_base3(n)
    carry = 0
    output = []
    trace = []

    for d in digits:
        val = 2 * d + carry
        out_digit = val % 3
        new_carry = val // 3
        trace.append({
            'in_digit': d,
            'carry_in': carry,
            'output': out_digit,
            'carry_out': new_carry
        })
        output.append(out_digit)
        carry = new_carry

    # Handle final carry
    while carry > 0:
        out_digit = carry % 3
        new_carry = carry // 3
        trace.append({
            'in_digit': 0,
            'carry_in': carry,
            'output': out_digit,
            'carry_out': new_carry
        })
        output.append(out_digit)
        carry = new_carry

    return from_base3(output), trace

def analyze_survivor_pattern(n):
    """Analyze what makes n survive (no digit 2)."""
    if has_digit_2(n):
        return None

    digits = to_base3(n)
    doubled, trace = double_with_trace(n)

    # Check which transitions were used
    transitions = []
    for t in trace:
        c_in = t['carry_in']
        d = t['in_digit']
        out = t['output']
        c_out = t['carry_out']
        transitions.append((c_in, d, out, c_out))

    return {
        'n': n,
        'base3': ''.join(map(str, reversed(digits))),
        'doubled': doubled,
        'doubled_base3': ''.join(map(str, reversed(to_base3(doubled)))),
        'has_2_after': has_digit_2(doubled),
        'transitions': transitions
    }

# Find all powers of 2 without digit 2 up to 2^100
print("Powers of 2 without digit 2:")
print("="*50)
survivors = []
for n in range(101):
    power = 2**n
    if not has_digit_2(power):
        survivors.append(n)
        b3 = ''.join(map(str, reversed(to_base3(power))))
        print(f"2^{n} = {power} = {b3}_3")

print(f"\nSurvivors: {survivors}")
print()

# Analyze the transition patterns for survivors
print("\nTransition analysis for 2^8 = 256:")
print("="*50)
analysis = analyze_survivor_pattern(256)
print(f"256 = {analysis['base3']}_3")
print(f"512 = {analysis['doubled_base3']}_3")
print(f"Has digit 2 after doubling: {analysis['has_2_after']}")
print("\nTransitions (carry_in, digit, output, carry_out):")
for i, t in enumerate(analysis['transitions']):
    status = "OK" if t[2] != 2 else "FORBIDDEN"
    print(f"  Position {i}: {t} - {status}")

# Analyze allowed vs forbidden transitions
print("\n\nAllowed transition patterns:")
print("="*50)
print("From state 0 (no carry):")
print("  digit=0: output=0, next=0  [ALLOWED]")
print("  digit=1: output=2, next=0  [FORBIDDEN]")
print("  digit=2: output=1, next=1  [ALLOWED]")
print()
print("From state 1 (carry):")
print("  digit=0: output=1, next=0  [ALLOWED]")
print("  digit=1: output=0, next=1  [ALLOWED]")
print("  digit=2: output=2, next=1  [FORBIDDEN]")

# For numbers with only digits {0,1}, analyze which survive doubling
print("\n\nNumbers with digits {0,1} that survive doubling:")
print("="*50)
count = 0
for n in range(1, 1000):
    digits = to_base3(n)
    if all(d in [0, 1] for d in digits):
        doubled = 2 * n
        if not has_digit_2(doubled):
            b3 = ''.join(map(str, reversed(digits)))
            b3_doubled = ''.join(map(str, reversed(to_base3(doubled))))
            print(f"{n} = {b3}_3 -> 2n = {doubled} = {b3_doubled}_3")
            count += 1

print(f"\nFound {count} numbers with digits {{0,1}} whose double also has no digit 2")

# Trace why 256 works
print("\n\nDetailed trace for 256 = 100111_3:")
print("="*50)
n = 256
digits = to_base3(n)  # [1, 1, 1, 0, 0, 1] (LSB first)
print(f"Digits (LSB first): {digits}")
print(f"Digits (MSB first): {list(reversed(digits))}")

carry = 0
print("\nDoubling step by step:")
for i, d in enumerate(digits):
    val = 2 * d + carry
    out = val % 3
    new_carry = val // 3
    print(f"  Pos {i}: 2×{d} + {carry} = {val} -> out={out}, carry={new_carry}")
    carry = new_carry

if carry > 0:
    print(f"  Final: carry={carry} -> out={carry}")

print(f"\n2 × 256 = 512 = {to_base3(512)} (LSB first)")
print(f"         = {''.join(map(str, reversed(to_base3(512))))}_3 (MSB first)")

# Check the constraint pattern
print("\n\nConstraint analysis:")
print("="*50)
print("For 256 = 100111_3 (MSB first), reading LSB first: 1,1,1,0,0,1")
print()
print("Constraints for no-digit-2 output when INPUT has digits {0,1,2}:")
print("  State 0 + digit 1 -> FORBIDDEN")
print("  State 1 + digit 2 -> FORBIDDEN")
print()
print("Constraints for no-digit-2 output when INPUT has digits {0,1} only:")
print("  State 0 + digit 1 -> FORBIDDEN")
print("  (digit 2 never appears in input)")
print()
print("So: in state 0, seeing digit 1 kills you immediately!")
print("The only way to read digit 1 safely is from state 1.")
print()
print("For 256 = 100111_3:")
digits_msb = [1, 0, 0, 1, 1, 1]  # MSB first
digits_lsb = list(reversed(digits_msb))  # LSB first
print(f"  Reading LSB first: {digits_lsb}")
carry = 0
for i, d in enumerate(digits_lsb):
    if d == 1 and carry == 0:
        print(f"  Position {i}: digit=1, carry=0 -> WOULD BE FORBIDDEN if this were the input")
    carry_out = (2*d + carry) // 3
    print(f"  Position {i}: digit={d}, carry_in={carry}, carry_out={carry_out}")
    carry = carry_out
