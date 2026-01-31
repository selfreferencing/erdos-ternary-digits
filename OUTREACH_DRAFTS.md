# Outreach Drafts for Erdős Ternary Digits Proof

## 1. Email to Thomas Bloom (erdosproblems.com)

**Subject:** Formal verification of Erdős ternary digits conjecture (2^n contains digit 2 in base 3)

Dear Dr. Bloom,

I'm writing to report a formally verified proof of a conjecture attributed to Erdős: for all n > 8, the base-3 representation of 2^n contains at least one digit 2.

The proof has been completely formalized in Lean 4 with Mathlib (~4,500 lines), with zero axioms and zero sorry statements. The formalization is available at:

https://github.com/selfreferencing/erdos-ternary-digits

A preprint describing the proof is available in the repository (and will be submitted to ArXiv).

**The theorem:** For all n > 8, 2^n contains digit 2 in base 3. The only exceptions are n ∈ {0, 2, 8}.

**Proof method:**
- Automaton characterization of digit-2-free numbers
- Lifting the Exponent lemma gives period 3^12
- 3-adic induction with orbit coverage

**Notable aspect:** This proof was developed through human-AI collaboration (myself, Claude/Anthropic, and GPT/OpenAI), with the AI systems contributing substantially to the Lean formalization. The machine-checked verification ensures correctness regardless of the proof's origin.

If this problem is tracked on erdosproblems.com, I would be happy to provide any additional information needed for updating its status.

Best regards,
Kevin Vallier
Bowling Green State University

---

## 2. Lean Zulip Post

**Topic:** Formal verification of Erdős ternary digits conjecture

**Message:**

I'm pleased to announce a complete formalization of the Erdős ternary digits conjecture in Lean 4 with Mathlib:

**Theorem:** For all n > 8, 2^n contains at least one digit 2 in base 3.

The only exceptions are n ∈ {0, 2, 8}, with n = 8 (2^8 = 256 = 100111₃) being the unique non-trivial case.

**Repository:** https://github.com/selfreferencing/erdos-ternary-digits

**Stats:**
- ~4,500 lines of Lean 4
- Zero axioms, zero sorry
- Builds with `lake build`

**Proof outline:**
1. Define 2-state automaton characterizing digit-2-free numbers
2. Use Lifting the Exponent to establish period 3^12 = 531,441
3. Case analysis: j = 3 + m·3^12 (Case B) and j = m·3^12 (Case C)
4. 3-adic induction with orbit coverage via ZMod computation

**Human-AI collaboration:** This formalization was developed collaboratively with Claude (Anthropic) and GPT (OpenAI), with the AI systems contributing substantially to proof engineering. The machine-checked verification validates the result regardless of origin.

Happy to answer questions about the proof structure or formalization techniques!

---

## 3. Twitter/X Announcement (Optional)

Formally verified an Erdős conjecture! 🎉

For all n > 8, 2^n contains digit 2 in base 3.

• Complete Lean 4 proof (~4,500 lines)
• Zero axioms, zero sorry
• Human-AI collaboration (me + Claude + GPT)

Code: https://github.com/selfreferencing/erdos-ternary-digits

The unique exception: 2^8 = 256 = 100111₃ (no digit 2!)

---

## 4. ArXiv Submission Notes

**Primary category:** math.NT (Number Theory)
**Secondary category:** cs.LO (Logic in Computer Science)

**MSC classes:**
- 11A63 (Radix representation; digital problems)
- 03B35 (Mechanization of proofs and logical operations)

**Comments for ArXiv:**
- 12 pages
- Lean 4 code available at https://github.com/selfreferencing/erdos-ternary-digits
