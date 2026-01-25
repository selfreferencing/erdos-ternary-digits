# Erdős Ternary Digits Conjecture - Formal Verification in Lean 4

**A machine-checked proof that for all n > 8, 2^n contains at least one digit 2 in base 3.**

This repository contains a complete formal verification of the Erdős ternary digits conjecture (1979) in Lean 4 with Mathlib.

## The Theorem

**Erdős Ternary Digits Conjecture**: For all integers n > 8, the base-3 representation of 2^n contains at least one digit equal to 2.

The unique exception is n = 8, where 2^8 = 256 = 100111₃ (no digit 2).

## Proof Status

- **Fully verified**: Zero axioms, zero `sorry`
- **~4,500 lines** of Lean 4 code
- **Build**: `lake build` completes successfully

## Proof Strategy

1. **Automaton Approach**: Define a finite automaton that rejects digit sequences containing the forbidden pattern (digit 2 in certain positions)

2. **Lifting the Exponent Lemma**: Establishes the key period 3^12 = 531,441 via the fact that 4^(3^12) ≡ 1 + 3^13 (mod 3^14)

3. **Case Analysis**: Split into Case B (j = 3 + m·3^12) and Case C (j = m·3^12)

4. **3-adic Induction**: For each case family, prove rejection by:
   - Orbit coverage for m ≡ 1, 2 (mod 3)
   - Digit shift lemmas for m ≡ 0 (mod 3)

5. **Computational Verification**: Base cases verified via `native_decide`

## Building

```bash
# Install elan (Lean version manager) if needed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build the project
lake build
```

## Files

- `ErdosAnalytical_fixed2.lean` - Main proof file containing the complete formalization
- `lakefile.lean` - Lake build configuration
- `lake-manifest.json` - Dependency versions (Mathlib)

## AI Collaboration

**This proof was developed through human-AI collaboration.**

The formalization was created by Kevin Vallier in collaboration with:
- **Claude** (Anthropic) - Proof engineering, tactic debugging, axiom elimination
- **GPT** (OpenAI) - Proof strategy development, lemma suggestions
- **Other AI assistants** - Various contributions to proof structure

The humans provided mathematical direction and verification; the AIs wrote the vast majority of the Lean code and resolved compilation issues. This represents a new model of mathematical research where AI systems serve as capable proof engineers.

## Citation

If you use this work, please cite:

```bibtex
@misc{vallier2025erdos,
  author = {Vallier, Kevin and Claude (Anthropic) and GPT (OpenAI)},
  title = {Formal Verification of the Erdős Ternary Digits Conjecture in Lean 4},
  year = {2025},
  howpublished = {\url{https://github.com/selfreferencing/erdos-ternary-digits}},
}
```

## Related Links

- [Erdős Problems](https://www.erdosproblems.com/) - Database of Erdős problems
- [Mathlib](https://github.com/leanprover-community/mathlib4) - Lean 4 mathematics library
- [Lean 4](https://lean-lang.org/) - Theorem prover

## License

MIT License - see [LICENSE](LICENSE)

## Acknowledgments

Paul Erdős (1913-1996) posed thousands of problems in mathematics, many with cash prizes. This conjecture, concerning the ternary representation of powers of 2, is now resolved with machine-checked certainty.
