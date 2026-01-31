#!/usr/bin/env python3
"""
Deep analysis of why 256 = 4^4 is special in the automaton.

The key question: What makes the path for 64 → 256 succeed when
the paths for 4 → 16 and 16 → 64 fail?
"""

def to_base3(n):
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return digits

def trace_path(x, transitions):
    """
    Trace multiplying x by 4 through the automaton.
    Returns (success, output_digits, state_trace).
    """
    digits = to_base3(x)
    state = (0, 0)
    output = []
    trace = [(state, None, None)]

    for d in digits:
        result = transitions[state][d]
        if result is None:
            return False, output, trace, f"FORBIDDEN at input {d} from state {state}"
        y, next_state = result
        trace.append((next_state, d, y))
        output.append(y)
        state = next_state

    # Process remaining carries
    while state != (0, 0):
        d = 0
        result = transitions[state][d]
        if result is None:
            return False, output, trace, f"FORBIDDEN at final input 0 from state {state}"
        y, next_state = result
        trace.append((next_state, d, y))
        output.append(y)
        state = next_state

        # Safety limit
        if len(trace) > 50:
            return False, output, trace, "Did not converge to (0,0)"

    return True, output, trace, "SUCCESS"

def build_transitions():
    transitions = {}
    for prev in range(3):
        for carry in range(3):
            state = (prev, carry)
            transitions[state] = {}
            for x_i in range(3):
                total = x_i + prev + carry
                y_i = total % 3
                c_next = total // 3
                next_state = (x_i, c_next)
                if y_i == 2:
                    transitions[state][x_i] = None
                else:
                    transitions[state][x_i] = (y_i, next_state)
    return transitions

def main():
    transitions = build_transitions()

    print("=" * 70)
    print("WHY 256 = 4^4 IS SPECIAL")
    print("=" * 70)

    # Trace the chain of multiplications
    chain = [1, 4, 16, 64, 256, 1024]

    for i in range(len(chain) - 1):
        x = chain[i]
        target = chain[i + 1]

        print(f"\n{'='*70}")
        print(f"MULTIPLYING {x} × 4 = {target}")
        print(f"{'='*70}")

        digits_x = to_base3(x)
        digits_target = to_base3(target)

        print(f"\n{x} in base 3 (LSB first): {digits_x}")
        print(f"{target} in base 3 (LSB first): {digits_target}")

        success, output, trace, status = trace_path(x, transitions)

        print(f"\nAutomaton trace:")
        print(f"  Initial state: {trace[0][0]}")
        for j, (state, inp, out) in enumerate(trace[1:], 1):
            print(f"  Step {j}: input={inp} -> output={out}, new_state={state}")

        print(f"\nResult: {status}")
        if success:
            print(f"Output digits (LSB first): {output}")
            result = sum(d * 3**i for i, d in enumerate(output))
            print(f"Reconstructed: {result}")
            has_2 = 2 in output
            print(f"Contains digit 2: {has_2}")

    # Now analyze: what paths from (0,0) back to (0,0) are possible?
    print("\n" + "=" * 70)
    print("VALID ROUND-TRIP PATHS FROM (0,0) TO (0,0)")
    print("=" * 70)

    # BFS to find all paths of length ≤ 6 that return to (0,0)
    from collections import deque

    start = (0, 0)
    paths = []
    queue = deque([(start, [], [])])  # (current_state, input_seq, output_seq)

    while queue:
        state, inputs, outputs = queue.popleft()

        if len(inputs) > 0 and state == (0, 0):
            paths.append((inputs[:], outputs[:]))
            if len(paths) > 100:
                break

        if len(inputs) >= 8:
            continue

        for d in range(3):
            result = transitions[state][d]
            if result is not None:
                y, next_state = result
                queue.append((next_state, inputs + [d], outputs + [y]))

    print(f"\nFound {len(paths)} round-trip paths of length ≤ 8:")
    for inputs, outputs in paths[:30]:
        in_val = sum(d * 3**i for i, d in enumerate(inputs))
        out_val = sum(d * 3**i for i, d in enumerate(outputs))
        print(f"  Input: {inputs} ({in_val}) -> Output: {outputs} ({out_val})")
        # Check if out = 4 * in
        if out_val == 4 * in_val:
            print(f"    ✓ This is 4 × {in_val} = {out_val}")

    # Check which of these correspond to powers of 2
    print("\n" + "=" * 70)
    print("WHICH ROUND-TRIPS CORRESPOND TO POWERS OF 4?")
    print("=" * 70)

    powers_of_4 = {4**k for k in range(20)}

    print("\nPowers of 4 up to 4^10:")
    for k in range(11):
        p = 4**k
        digits = to_base3(p)
        # Check if 4*p (i.e., 4^{k+1}) can be computed
        success, output, trace, status = trace_path(p, transitions)
        marker = "✓" if success else "✗"
        print(f"  4^{k} = {p} = {digits} (LSB): {marker} ({status})")

    print("\n" + "=" * 70)
    print("THE KEY INSIGHT")
    print("=" * 70)
    print("""
The automaton reveals WHY only 4^0, 4^1, 4^4 work:

1. 4^0 = 1: Trivially has no digit 2

2. 4^1 = 4: Multiplying 1 (digits [1]) works because:
   - Start (0,0), input 1 -> output 1, state (1,0)
   - From (1,0), input 0 (final) -> output 1, state (0,0)
   - Result: [1,1] = 4 ✓

3. 4^2 = 16: FAILS because 4 has digits [1,1]:
   - Start (0,0), input 1 -> output 1, state (1,0)
   - From (1,0), input 1 -> FORBIDDEN (sum = 1+1+0 = 2)!

4. 4^4 = 256: Works because 64 has special digits [1,0,1,2]:
   - The digit sequence avoids the forbidden transitions
   - Crucially ends back at (0,0)

The forbidden transition (1,0) + input 1 = FORBIDDEN is the killer.
Any number with two consecutive 1s in base 3 will fail!

4 = [1,1] -> fails because of consecutive 1s
16 = [1,2,1] -> fails because first two are [1,2] and (1,0)+1 forbidden
64 = [1,0,1,2] -> fails at the END because state (1,1) + 0 forbidden

But 64's output 256 = [1,1,1,0,0,1] works for RECEIVING multiplication!
The question is whether we can ever MULTIPLY 256 by 4 and survive...
""")

    # Let's trace 256 -> 1024
    print("\n" + "=" * 70)
    print("CAN 256 BE MULTIPLIED BY 4?")
    print("=" * 70)

    success, output, trace, status = trace_path(256, transitions)
    print(f"\n256 = {to_base3(256)} (LSB first)")
    print(f"Result: {status}")
    print(f"\nTrace:")
    print(f"  Initial: {trace[0][0]}")
    for j, (state, inp, out) in enumerate(trace[1:], 1):
        print(f"  Step {j}: input={inp} -> output={out}, new_state={state}")

if __name__ == "__main__":
    main()
