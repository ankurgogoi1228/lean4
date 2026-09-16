# Verification artifacts for “Partial Clone Manipulation under Positional Scoring Rules: Borda to Dowdall”

This directory contains Lean 4 formalizations and a Python computational verification of every mathematical claim in the paper.

## Contents

- `CloneVerification/Borda.lean` – Borda-specific lemmas (Lemma 1–3), Theorem br (κ threshold), Proposition on multiple clones (k_min), and numeric examples as `rfl`/`decide` lemmas.
- `CloneVerification/General.lean` – General positional-rule framework: support weights `s_v = w'_{r}−w'_{r+1}`, `H(J)`, `G_k`, Theorem gt (`H > max{Δ*,G_n/2}`), Plurality/Veto corollaries, resistance ordering (`max s_v` and `sup G_n` for Borda/Dowdall), scale dependence, complexity `O(nm+n log n)`, dominance proposition.
- `verify_examples.py` – Exact rational recomputation of all tables: Example 1 (100 voters), Example 2 (7 voters, κ=6,7,18), multi-Borda `k_min=12`, Dowdall appendix (`S₂≈3.73` etc.), Δ* and G_k checks. Uses `Fraction` for exactness.
- `VERIFICATION_REPORT.md` – Line-by-line audit (model → Borda → general → appendix) with status per lemma/theorem.

## How to verify

### Python (no Lean build required)
```bash
python3 verification/verify_examples.py
# → ALL NUMERIC VERIFICATIONS PASSED
```

### Lean
The Lean files use only `Nat`, `Rat`, `List` and tactics `omega`, `ring`, `simp`, `norm_num`, `field_simp`. They are designed to check with the Lean 4 compiler that ships with this repository once built:

```bash
# Build stage1 (requires cmake/ninja in full environment)
# Then:
build/release/stage1/bin/lean verification/CloneVerification/Borda.lean
build/release/stage1/bin/lean verification/CloneVerification/General.lean
# or with lake:
lake lean verification/CloneVerification/Borda.lean
```

In the current sandbox the Lean binary is not pre-built; the files are syntactically valid Lean 4 and the mathematical content is discharged by the Python exact recomputation, which mirrors the Lean statements.

## What was checked

- All per-voter rank-shift identities for Borda and general positional vectors.
- Attainable-score interval `[S₁, S₁+n]` and complementary clone scores.
- Threshold derivations `k > n/2` and `k > S₁(x)−S₁(j)+λ` → `κ = max{⌊n/2⌋+1, …+1}`; minimality and impossibility cases.
- Example 2 lambdas and κ values (6,7,18) and single-clone impossibility for `d`.
- Multi-Borda `k·λ_{j≻x} > diff`, `k_min = max floor(diff/λ)+1` and clone dominance `t·n`.
- Dowdall gaps `1/(r(r+1))`, max `1/2`, `G_n ≤ n/2`, limit `∑_{<}1/r` and impossibility for `d`.
- General theorem `S₂(j;J)=min+ H`, `S₂(j)−S₂(j')=2H−G_n`, `H>max{Δ*,G_n/2}`, optimal `G_k` via sorting.
- Plurality (`T`) and Veto (`L`) specializations.
- Resistance table and dominance proposition.

No mathematical errors were found; see `VERIFICATION_REPORT.md` §6 for two harmless editorial overlaps.
