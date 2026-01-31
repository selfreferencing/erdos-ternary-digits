#!/usr/bin/env python3
"""
Analyze the 9-state carry automaton for ×4 in base 3.

The automaton tracks (previous_digit, carry) pairs and determines
which input sequences produce only {0,1} output digits.

This is the key structure from GPT Pro Response 2 for attacking
the Erdős ternary digits conjecture.
"""

from collections import defaultdict
from itertools import product

def build_automaton():
    """
    Build the 9-state automaton for ×4 = "add shifted copy".

    State: (x_{i-1}, c_i) where x_{i-1} is previous input digit, c_i is carry
    Input: x_i (current digit)
    Output: y_i = (x_i + x_{i-1} + c_i) % 3
    Next carry: c_{i+1} = (x_i + x_{i-1} + c_i) // 3

    Constraint: y_i ∈ {0, 1} (no digit 2 in output)
    """
    states = [(prev, carry) for prev in range(3) for carry in range(3)]
    transitions = {}  # (state, input) -> (output, next_state) or None if forbidden

    for prev, carry in states:
        state = (prev, carry)
        transitions[state] = {}

        for x_i in range(3):
            total = x_i + prev + carry
            y_i = total % 3
            c_next = total // 3
            next_state = (x_i, c_next)

            if y_i == 2:
                transitions[state][x_i] = None  # Forbidden
            else:
                transitions[state][x_i] = (y_i, next_state)

    return states, transitions

def print_transition_table(states, transitions):
    """Print the full transition table."""
    print("=" * 70)
    print("9-STATE AUTOMATON FOR ×4 IN BASE 3")
    print("=" * 70)
    print("\nState = (prev_digit, carry)")
    print("Transition: state --[input/output]--> next_state")
    print("FORBIDDEN means output would be 2")
    print()

    for state in states:
        print(f"\nState {state}:")
        for x_i in range(3):
            result = transitions[state][x_i]
            if result is None:
                print(f"  input={x_i}: FORBIDDEN (sum={x_i + state[0] + state[1]} → output=2)")
            else:
                y_i, next_state = result
                print(f"  input={x_i}: output={y_i}, next={next_state}")

def build_allowed_graph(states, transitions):
    """Build the graph of allowed transitions only."""
    graph = defaultdict(list)

    for state in states:
        for x_i in range(3):
            result = transitions[state][x_i]
            if result is not None:
                y_i, next_state = result
                graph[state].append((x_i, y_i, next_state))

    return graph

def find_zero_loops(states, transitions):
    """Find which states can accept input 0 without producing digit 2."""
    zero_accepting = []

    for state in states:
        result = transitions[state][0]
        if result is not None:
            y_i, next_state = result
            zero_accepting.append((state, y_i, next_state))

    return zero_accepting

def find_strongly_connected_components(graph):
    """Find SCCs using Tarjan's algorithm (simplified)."""
    index_counter = [0]
    stack = []
    lowlinks = {}
    index = {}
    on_stack = {}
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlinks[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack[v] = True

        for _, _, w in graph.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlinks[v] = min(lowlinks[v], lowlinks[w])
            elif on_stack.get(w, False):
                lowlinks[v] = min(lowlinks[v], index[w])

        if lowlinks[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.append(w)
                if w == v:
                    break
            sccs.append(scc)

    for v in graph:
        if v not in index:
            strongconnect(v)

    return sccs

def analyze_zero_chains(graph, transitions):
    """
    Analyze which states can support infinite chains of 0-inputs.
    This is critical for the "eventually-integer" condition.
    """
    print("\n" + "=" * 70)
    print("ANALYSIS OF 0-INPUT CHAINS (Eventually-Integer Paths)")
    print("=" * 70)

    # Find states that can accept 0 and where they go
    zero_map = {}
    for state in [(p, c) for p in range(3) for c in range(3)]:
        result = transitions[state][0]
        if result is not None:
            y_i, next_state = result
            zero_map[state] = (y_i, next_state)

    print("\nStates that accept input 0:")
    for state, (y, nxt) in zero_map.items():
        print(f"  {state} --[0/{y}]--> {nxt}")

    # Find fixed points under 0-input (self-loops)
    print("\nFixed points under 0-input (self-loops):")
    for state, (y, nxt) in zero_map.items():
        if state == nxt:
            print(f"  {state} --[0/{y}]--> {state} (SELF-LOOP)")

    # Find cycles under 0-input
    print("\nCycles under repeated 0-input:")
    visited = set()
    for start in zero_map:
        if start in visited:
            continue

        path = [start]
        current = start

        while True:
            if current not in zero_map:
                print(f"  {start}: terminates at {current} (0-input forbidden)")
                break

            _, nxt = zero_map[current]

            if nxt in path:
                cycle_start = path.index(nxt)
                cycle = path[cycle_start:]
                print(f"  From {start}: reaches cycle {cycle}")
                visited.update(path)
                break

            if nxt in visited:
                print(f"  From {start}: merges into already-analyzed path at {nxt}")
                visited.update(path)
                break

            path.append(nxt)
            current = nxt

def analyze_power_of_4_chains(transitions):
    """
    Trace the specific chains for powers of 4: 1, 4, 16, 64, 256, ...
    """
    print("\n" + "=" * 70)
    print("TRACING POWERS OF 4 (The Known Solutions)")
    print("=" * 70)

    def to_base3(n):
        if n == 0:
            return [0]
        digits = []
        while n > 0:
            digits.append(n % 3)
            n //= 3
        return digits

    def trace_multiplication(x, transitions):
        """Trace 4*x through the automaton."""
        digits = to_base3(x)

        # Initial state: (0, 0) - no previous digit, no carry
        state = (0, 0)
        output = []
        trace = []

        for i, d in enumerate(digits):
            result = transitions[state][d]
            if result is None:
                trace.append(f"  pos {i}: state={state}, input={d} -> FORBIDDEN!")
                return None, trace

            y, next_state = result
            trace.append(f"  pos {i}: state={state}, input={d} -> output={y}, next={next_state}")
            output.append(y)
            state = next_state

        # Handle final carry
        prev, carry = state
        while carry > 0 or prev > 0:
            d = 0  # No more input digits
            result = transitions[state][d]
            if result is None:
                trace.append(f"  final: state={state}, input=0 -> FORBIDDEN!")
                return None, trace

            y, next_state = result
            trace.append(f"  final: state={state}, input=0 -> output={y}, next={next_state}")
            output.append(y)

            if next_state == (0, 0):
                break
            state = next_state

        return output, trace

    for m in range(10):
        power = 4 ** m
        print(f"\n4^{m} = {power}")
        print(f"  Base-3: {to_base3(power)} (LSB first)")

        if m > 0:
            prev_power = 4 ** (m - 1)
            output, trace = trace_multiplication(prev_power, transitions)

            if output is None:
                print("  4×(4^{m-1}): PRODUCES DIGIT 2!")
                for line in trace:
                    print(line)
            else:
                print(f"  4×{prev_power} = {power}: output digits = {output}")
                # Verify
                result = sum(d * 3**i for i, d in enumerate(output))
                if result == power:
                    print(f"  ✓ Verified: {output} = {power}")
                else:
                    print(f"  ✗ Error: got {result}, expected {power}")

                has_2 = 2 in output
                print(f"  Contains digit 2: {has_2}")

def analyze_forbidden_patterns(transitions):
    """
    Analyze patterns that lead to forbidden transitions.
    This helps understand what forces a digit 2.
    """
    print("\n" + "=" * 70)
    print("FORBIDDEN TRANSITION ANALYSIS")
    print("=" * 70)

    print("\nForbidden sums (produce digit 2):")
    print("  sum = 2: e.g., (prev=0, carry=0, input=2), (prev=1, carry=0, input=1), etc.")
    print("  sum = 5: e.g., (prev=2, carry=2, input=1), (prev=2, carry=1, input=2), etc.")

    print("\nAll forbidden (state, input) pairs:")
    for state in [(p, c) for p in range(3) for c in range(3)]:
        for x_i in range(3):
            result = transitions[state][x_i]
            if result is None:
                total = x_i + state[0] + state[1]
                print(f"  state={state}, input={x_i}: sum={total} → FORBIDDEN")

def count_survivors_by_depth(max_depth=10):
    """
    Count survivor sequences (no digit 2 output) by length.
    """
    print("\n" + "=" * 70)
    print("SURVIVOR COUNT BY SEQUENCE LENGTH")
    print("=" * 70)

    states, transitions = build_automaton()

    # Initial state
    start = (0, 0)

    for depth in range(1, max_depth + 1):
        count = 0

        # Enumerate all possible input sequences of given length
        for seq in product(range(3), repeat=depth):
            state = start
            valid = True

            for d in seq:
                result = transitions[state][d]
                if result is None:
                    valid = False
                    break
                _, state = result

            if valid:
                count += 1

        print(f"  Length {depth}: {count} survivors (expected: ~{2**depth} if (2/3)^depth density)")

def main():
    states, transitions = build_automaton()

    print_transition_table(states, transitions)

    graph = build_allowed_graph(states, transitions)

    print("\n" + "=" * 70)
    print("ALLOWED TRANSITION GRAPH")
    print("=" * 70)
    for state, edges in sorted(graph.items()):
        for inp, out, nxt in edges:
            print(f"  {state} --[{inp}/{out}]--> {nxt}")

    sccs = find_strongly_connected_components(graph)
    print("\n" + "=" * 70)
    print("STRONGLY CONNECTED COMPONENTS")
    print("=" * 70)
    for i, scc in enumerate(sccs):
        print(f"  SCC {i}: {scc}")

    analyze_zero_chains(graph, transitions)
    analyze_power_of_4_chains(transitions)
    analyze_forbidden_patterns(transitions)
    count_survivors_by_depth(8)

    # Summary
    print("\n" + "=" * 70)
    print("KEY FINDINGS SUMMARY")
    print("=" * 70)

    # Find the self-loop states under 0-input
    zero_selfloops = []
    for state in states:
        result = transitions[state][0]
        if result is not None:
            y, nxt = result
            if state == nxt:
                zero_selfloops.append((state, y))

    print(f"\nStates with 0-input self-loops: {zero_selfloops}")
    print("  These are the ONLY states that can support 'eventually-all-zeros' paths!")

    # Check which of these correspond to known solutions
    print("\nInterpretation for Erdős conjecture:")
    print("  An integer exponent m corresponds to a finite base-3 digit sequence")
    print("  ending in zeros. For 4^m to have no digit 2, the automaton must")
    print("  accept the digits of 4^{m-1}, then accept infinite zeros.")
    print("  ")
    print("  The 0-selfloop states determine which 'tails' are possible.")
    print("  If only specific patterns can reach 0-selfloop states,")
    print("  then only those patterns correspond to valid integer exponents.")

if __name__ == "__main__":
    main()
