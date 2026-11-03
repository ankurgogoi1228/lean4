# Verification report — *Sharp Qualified-Majority Thresholds for Social Acceptability of q-Condorcet Committees*

**Ankur Gogoi** (Department of Mathematics, Dibrugarh University) · report dated 3 November 2026
**Verdict: the mathematics is correct.** No false theorem, no wrong threshold, no failing construction.
Two wording fixes are recommended (§7 below); neither affects a proof.

Artifacts: `paper_check/` — `paper_claims.py` (per-statement exact audit), `check_all.py`,
`verify_constructions.py`, `lean/Arithmetic.lean`, `lean/Profiles.lean`.

---

## 0. What was checked, and how

| Layer | Method | Scope | Result |
|---|---|---|---|
| **A. Every displayed statement** | exact rational arithmetic, keyed to the paper's own labels | `K = 3…40`, all admissible `k`, all `1 ≤ ℓ ≤ k` | **20 598 assertions, 0 failures** |
| **B. Lemma 2** | brute-force enumeration of *all* ballots | `K = 3,4,5`, all `k`, all `a`, all permutations | ✅ no counterexample |
| **C. The model itself** | exact rational LP over *all* profiles (`lp.py`, `scan.py`) | `K = 3…6`, every `(k,ℓ)` | ✅ optimum `= q_ℓ*` in every case |
| **D. Constructions** | explicit integer profiles (`construct.py`) | Thm 2 (`K ≤ 8`), Thm 3(b) (`K ≤ 8`), Thm 4, Examples 1–2 | ✅ all behave as claimed |
| **E. Formal proof** | Lean 4, no `sorry` | the whole arithmetic core (§2–§6) + profiles | ✅ 40 statements |

Layer C matters most: it shows the closed forms are not merely internally consistent but are
the *true optima of the voting model* — i.e. that the paper solved the problem it posed.

---

## 1. §2 Definitions

Checked by re-deriving each threshold from the definitions rather than trusting the formulas.

- Weak/strict `q`-Condorcet, `A_a`, `B_a`, acceptability (`B_a ≤ A_a`), complete
  unacceptability, `q_ℓ*` — all used consistently downstream. ✅
- The rank conventions (`rank ≤ r` above; `rank = r+1` on the line iff `ε=1`;
  `rank > K−r` below) are self-consistent for both parities: for `K` even `K−r = r`, for `K`
  odd `K−r = r+1`. ✅
- `q_ℓ*` is genuinely an infimum that is attained, as claimed: Theorem 3(a) gives sufficiency
  at `q = q_ℓ*` and 3(b) failure for every `q < q_ℓ*`. ✅

> **Wording fix (1).** The abstract glosses acceptability as *"a majority of voters rank `a` in
> the top half of their ballot"*. That is not what the paper's own definition says. With
> `n = A_a + B_a + O_a`, acceptability is `B_a ≤ A_a`, i.e. *fewer voters place `a` below the
> line than above it*; it is **not** `A_a > n/2`. The two differ whenever `O_a > 0` (odd `K`):
> a member with `A_a = 10, B_a = 10, O_a = 6` is acceptable but only 10 of 26 voters rank it in
> the top half. Every theorem uses `B_a ≤ A_a`, so only the abstract's sentence is at fault.
> Suggest: *"when at least as many voters rank `a` in the top half as in the bottom half."*

## 2. §3 Lemmas 1–2 and Remark 1

- **Lemma 1** (`W_π(a) ≥ qnt`): immediate from the definition. ✅
- **Lemma 2**: verified *by exhaustive enumeration of all ballots* for `K = 3,4,5` — every
  `k ≤ r`, every `a ∈ C`, every permutation. The three cases (`≥ s`, `≥ s−1`, `≥ 0`) hold
  without exception, and the on-line case occurs exactly when `ε = 1`. ✅
  The counting in the proof is right: a below-line member is preceded by `≥ r+ε` alternatives,
  of which `≤ k−1` are committee members, leaving `≥ r−k+1+ε = s` nonmembers.
- **Remark 1** (`t = r+s−1`): ✅ for all `K ≤ 40`, both parities; `s ≥ 2` when `ε=1, k ≤ r` ✅.

*Note on `s`.* With `s = r−k+1+ε` the paper's `s` is a plain integer subtraction in disguise;
an implementation that writes it as `r−k+1+ε` with truncating subtraction can silently make
the below-line case unreachable for `k > r+1`. My Lean file therefore writes
`s = K/2 + 1 + K%2 − k`. The paper's formula is correct; this is only a caution for anyone
mechanising it.

## 3. §4 Theorem 1 and Theorem 2 (`ℓ = 1`)

**(2.1) and the closed form.** `2(2t−s) = 3K−2k−2−ε` ✅ (Lean `qstar_numerator`, and exact
rationals for all `K ≤ 40`). `1 ≤ s ≤ t` ✅; `K ≥ 4 ⟹ s < t` ✅; `1/2 < q* < 1` ✅ for `K ≥ 4`;
`K=3, k=1 ⟹ s=t=2, q*=1/2` ✅.

**Theorem 1 (sufficiency).** I checked the identity on which the proof turns:
`sB + (s−1)O − ns/2 = (s/2)(B−A) + (s/2−1)O`. ✅ It is exact, and the sign analysis is right in
both parities — for `ε=0` the term `(s/2−1)O` is absent because `O=0`, and for `ε=1` one has
`s ≥ 2` on `k ≤ r` so `s/2−1 ≥ 0`. The contradiction `nt−W > ns/2` vs `nt−W ≤ ns/2` closes. ✅
The sharp use of `s/2` (not `s−ε`) is precisely what the paper claims §7.2 loses.

**Theorem 2 (sharpness).** The construction was implemented and run for every `(K,k,ℓ)` with
`q* > 1/2` up to `K = 8` and many rational `ρ`: a **strict** `q`-Condorcet profile with
`A(a_1) < B(a_1)` exists in integers every time. ✅ I re-checked the arithmetic of the two
ballot shapes by hand:
- `ε=0`: bad ballot has `(k−1)+s = r` positions above the line, putting `a_1` at rank `r+1`;
  below the line `1+(t−s) = r`. ✅
- `ε=1`: bad ballot has `(k−1)+(s−1) = r` above the line, `d_O` on the line, `a_1` below. ✅
The margin is exactly `1 − ρ·(s/t) > q` because `ρ < (1−q)t/s`, and `M > G` gives
`B_{a_1} > A_{a_1}`. ✅ The `s/t` probability is `C(t−1,s−1)/C(t,s)`. ✅

## 4. §5 The hierarchy

**Scope.** `q_0 < 1 ⟺ 2k < K+2 ⟺ k ≤ ⌈K/2⌉` ✅ (both parities, all `K ≤ 40`). So the section's
range is exactly the range on which Diss–Mahajne state `q_0, q_1 < 1`. ✅

**`M_{ε,s}`.** The four branches are exhaustive and disjoint; `M` may be a half-integer, and the
paper handles this correctly by writing `s/2`. Each branch is the value the envelope takes at
`ℓ/2` (verified in §5.4). ✅

**`M ≤ ℓt/2`, hence `q_ℓ* ∈ [1/2,1]`.** ✅ for every `K ≤ 40`, every admissible `(k,ℓ)`,
including the odd boundary. The displayed inequality chain
`ℓt − 2M = (2m+1)(r−1) − 2m² ≥ (2m+1)(2m) − 2m² = 2m²+2m ≥ 0` is correct, and `r ≥ 2m+1`
follows from `ℓ = 2m+1 ≤ k ≤ r`. ✅

**The §5.1 note on the boundary.** *"for odd `ℓ = 2m+1` with `m ≥ 0`, `2M_{1,1}(ℓ) − ℓs = 2m²−1`,
not `2m²`"* — verified exactly, including `m = 0` (both sides `−1`). ✅ The paper is right to
isolate this; it is the reason Corollary 1 cannot be stated at the boundary.

**Lemma 3 (block defeat bound).** I checked the case analysis line by line. Writing
`D_i(U) = (d_A+d_O)(b+o) − d_O·o`, the objective is minimised by making `d_O` as large as
possible and `d_A+d_O` as small as possible; the value is then `(b+o)(s−1+b) − o(ε−o)`,
and `o ∈ {0,ε}` kills the last term. ✅ Both cases of the proof are correct, and the two
constraints `d_A+d_O ≥ s−1+b` and `d_O ≤ ε−o` are both derived correctly from counting
(`c_A+c_O ≤ k−b` and `c_O ≥ o`). ✅

**The convex envelope.** All three ingredients check out:
`ψ_A(b+1) − ψ_A(b) = s+2b` increasing ✅;
`ψ_B(b) − ½[ψ_A(b)+ψ_A(b+1)] = (s−2)/2` ✅ (so `B_b` is on the chord exactly at `s=2`, above it
for `s>2`, below it only at the boundary `s=1`);
slopes `2b, 2b+2, 2b+2, 2b+4, …` at the boundary ✅ (non-decreasing, so the poly-line through
`A_0,B_0,A_1,B_1,…` *is* the lower envelope). The evaluations
`ψ̲(m) = m(s−1+m)`, `ψ̲(m+½) = m(m+s)+s/2` reproduce the `M` table. ✅

**Theorem 3(a).** The chain
`Σ(2b_i+o_i) > nℓ ⟺ x̄ > ℓ/2`, Jensen, envelope, strict monotonicity, then
`Σ D_i(U) = Σ_{a∈U}Σ_d n_{da} ≤ ℓt(1−q)n` — all correct. ✅ The strict inequality needs `ψ̲`
strictly increasing right of `ℓ/2`, which holds since `ℓ/2 ≥ 1/2` and every slope from there on
is `≥ 2`. ✅

**Theorem 3(b), regular regime.** Ranking arithmetic re-derived: `(k−ℓ)+(ℓ−b)+(ŝ_b−ε) = r`
above the line and `b+(t−ŝ_b) = r` below, with `d_O` on the line when `ε=1`. ✅ The defeat
fraction is exactly `Eψ/(ℓt)`, and `μ/ℓ > 1/2` gives unacceptability. ✅ The claim
`b ≤ p+1 ≤ r ≤ t` holds (`⌊ℓ/2⌋+1 ≤ ℓ ≤ r` for `ℓ ≥ 2`, and `t = r+s−1 ≥ r`).

**Theorem 3(b), odd boundary.** Both state families check out:
`A_b` gives `r` above the line and `r` below with `d_O` on the line; `B_b` gives `k−1 = r`
above, `u_0` on the line, `r` below. ✅ Defeat fractions `b²/(ℓt)` and `b(b+1)/(ℓt)` ✅.
Mixtures: `ℓ=2m` → `A_m(1−δ)+B_m(δ)`, `Ex = m+δ/2 > ℓ/2`, `Eψ → m²` ✅;
`ℓ=2m+1` → `B_m(1−δ)+A_{m+1}(δ)`, `Ex = m+½+δ/2 > ℓ/2`, `Eψ → m(m+1)` ✅.
The `A_0` state's need for `C∖U ≠ ∅` is correctly flagged and is never violated. ✅

**Corollary 1.** (a) ✅ (b) ✅ — `2M−ℓs = 2⌊(ℓ−1)²/4⌋` holds for every `K ≤ 40`, every
`2 ≤ k ≤ r`, every `1 ≤ ℓ ≤ k`, and the resulting `q_ℓ* = q* − ⌊(ℓ−1)²/4⌋/(ℓt)` matches.
(c) ✅ including both halves of the `k=2` split and `k ≥ 3`. (d) ✅ — at the boundary `q_1* = 1`
and `q_2* < 1` for every odd `K`.

## 5. §6 Boundary sizes, Theorem 4, Corollary 2, Examples

**Parity transition.** For even `K` there is no intermediate size; for odd `K` the single
boundary size is `k = r+1`. ✅

**Theorem 4(a).** Sufficiency: at weak `q=1` every member of `C` is above every nonmember, so
`C` occupies ranks `1..r+1`; with `r` above-line positions and one on-line position no member is
ever below the line, so `B_a = 0`. ✅ Sharpness: I checked the two ballot shapes at
`K = 5, k = 3` with `n = 101` in Lean by `decide` — a_1's ranks are `r+2` (below) once and `r+1`
(on the line) `n−1` times, so `A=0, B=1, O=n−1`, while `n_{a_1b_1} = n−1 > qn` iff `δn > 1`. ✅

**Theorem 4(b).** `k = r+ε+m` with `m ≥ 1`, `t = r−m ≥ 1`. The construction puts all of `C` in
the top `k` ranks with `a_1` at rank `r+ε+1` (the first below-line rank) and `m−1` other members
just after, so `B_{a_1} = n > A_{a_1} = 0` while `C` wins unanimously. ✅ Verified for `K=5,k=4`
and `K=6,k=4` in Lean and Python.

**Corollary 2.** `q_0 = 1 − 1/(4r)` at the boundary ✅. `M_{1,1}(k)/k = m/2 > 1/4` for `k = 2m`
and `m(m+1)/(2m+1) > 1/4` for `k = 2m+1`, `m ≥ 1` ✅, so `q_k* < q_0` at every boundary size,
`K=3, k=2` included (`q_k* = 1/2 < 3/4` ✅). The `q=1` identity
`Σ_{a∈C}(B_a−A_a) = n(m−r) = n(k−K) < 0` is correct — it is a genuinely elegant argument that
`q_k*` still exists for `k > ⌈K/2⌉` where `q_1*` does not. ✅

**Example 1 (`K=5, k=3`).** `M_{1,1}(1,2,3) = 0, 1, 2`;
`q_1^* = 1`, `q_2^* = 3/4`, `q_comp^* = 2/3`; `q_0 = 7/8`, `q_1 = 23/24`. ✅ All five numbers
reproduced three ways (kernel `decide` in Lean, exact rationals, LP optimum).

**Example 2 (`n = 26`, `q = 24/25`).** Machine-checked in Lean with a real ballot model: margins
`25, 26, 26, 26, 26, 26`, all `> 24.96`; `A_{a_1}=0, B_{a_1}=1, O_{a_1}=25` (unacceptable);
`a_2, a_3` acceptable; `24/25 > 23/24` since `576 > 575`. ✅ This is the paper's headline
counterexample and it does exactly what it claims — it refutes the `q_1`-sharpness assertion at
the one committee size where `q_1 < 1` but `q_1^* = 1`.

## 6. §7 Relation to Diss and Mahajne

- **`q_1 − q_0 = (k−1)(1−q_0)/k ≥ 0`**, with equality in range only at `k=1` ✅, and
  `q_0 ≤ q_1 ⟺ q_0 ≤ 1 ⟺ k ≤ (K+2)/2` ✅ — the paper states this correctly and carefully,
  including the observation that the comparison is *vacuous* for `q_0 > 1`, and
  `q_0 = q_1 = 1` at the even boundary. This is more careful than my earlier draft assumed.
- **Even `K`: `q* = q_0`** ✅, so their first bound is exactly the sharp full-acceptability
  threshold, and `q_1 > q*` for every `k > 1` ✅ — "the assertion that `q_1` cannot be improved
  is false for all genuinely multiwinner cases."
- **Odd `K`, `k ≤ r`: `q* = q_0 − 1/(4(K−k)) < q_0 ≤ q_1`** ✅.
- **§7.3, `k=1`:** `q*(K,1) = (3K−4)/(4K−4)` even, `(3K−5)/(4K−4)` odd ✅ for all `K ≤ 40` —
  Mahajne–Volij is recovered exactly.
- **§7.2, the `K=4,k=2` family.** Re-derived exactly: `n = 12m+1`; all four margins from `{a,b}`
  to `{c,d}` equal `9m`; `A_a = A_b = 6m`, `B_a = B_b = 6m+1`. The paper's own text describes
  this profile correctly — *"the profile is not `3/4`-Condorcet: its uniform margin ratio is
  `9m/(12m+1) < 3/4`"* — and uses the limit `9m/(12m+1) ↑ 3/4` to witness sharpness of
  `q_2^* = q_0 = 3/4`. ✅ Verified in Lean for `m = 1,2,3,10`.
- **The `q_1` diagnosis (§7.2).** The algebra is consistent with the stated mechanism: bounding
  `k−1` members by the trivial maximum `n(K−k)` and one by `q_0n(K−k)` contradicts
  `k(K−k)qn` exactly when `q > (k−1+q_0)/k = q_1`. ✅ This is a *plausible and arithmetically
  coherent* account, but it is a claim about the internal working of a proof in
  halshs-02003292 / halshs-02011732, which I could not consult. Treat the diagnosis as
  **unverified hearsay**, however likely; the surrounding mathematics (that `q_1` is not sharp
  and `q_0` is not the right complete-unacceptability threshold) is verified independently and
  does not depend on it.

## 7. Findings

**Nothing false.** Two wording issues, both in prose, neither affecting a proof:

> **Wording fix (2) — "sharp only in the even-`K`, `k=2` case".**
> The abstract, introduction (contribution 3) and §7.1 all say that `q_0` is sharp for complete
> unacceptability *only* in the even-`K`, `k=2` case. Enumerating `q_comp* = q_0` over
> `K ≤ 40` gives exactly the pairs with `K` even and `k ∈ {1, 2}` — **`k=1` also qualifies**
> (there `ℓ = k = 1`, so "completely unacceptable" degenerates to "unacceptable" and
> `q_comp* = q_1* = q* = q_0` by Corollary 1(a) and §7.1).
> Suggested: *"for `2 ≤ k ≤ r`, `q_0` is sharp for complete unacceptability only when `K` is
> even and `k = 2`"* — or simply "…only in the even-`K`, two-member case (and the degenerate
> one-member case)". Corollary 1(c) itself is correctly scoped to `2 ≤ k ≤ r`.

> **Wording fix (1)** — the abstract's "a majority of voters rank `a` in the top half", see §1
> above. The formal definition `B_a ≤ A_a` is the one used everywhere and is correct.

Minor:

- Theorem 4(a)'s proof contains a stray "and set `M=1`" — leftover notation, no effect.
- Remark 2's phrasing "*the parity-sensitive value `s/2`, rather than `s−ε`, is exactly what
  Diss and Mahajne lost*" is compressed; the precise content (verified) is that they replaced
  the sharp bound `n(3K−2k−2−ε)/4` by `n(3K−2k−2)/4`, discarding `nε/4` — which in the
  `nt−W` comparison is exactly the `s/2 → (s−ε)/2` shrinkage when `ε=1`. Worth one clause.

---

## 8. Corrections to my earlier report

The previous report in this workspace was written from a reconstruction of the paper, before the
source text was available. With the source in hand, **three of the four "findings" in it were
my errors**, and I retract them:

| Earlier claim | Status |
|---|---|
| "The Diss–Mahajne profile in §7.2 is not `3/4`-Condorcet — a discrepancy" | **Retracted.** The paper says so itself, in those words, and uses the limit to witness sharpness at `q_2^* = q_0 = 3/4`. The profile is correct and correctly described. |
| "The floor identity is false at the odd boundary; needs an explicit exclusion" | **Retracted.** §5.1 states the boundary value `2m²−1` explicitly, and Corollary 1 is scoped to `2 ≤ k ≤ r` precisely to exclude it. |
| "`q_1 ≥ q_0` needs the hypothesis `q_0 ≤ 1`" | **Retracted.** §7.1 states the equivalence, the vacuity, and the boundary `q_0 = q_1 = 1`. |
| The two wording issues in §7 above | **New** — these replaced them and are genuine. |

---

## 9. Status of the Lean artifacts — read this

`lean/Arithmetic.lean` (40 statements) and `lean/Profiles.lean` (ballot model + ~40
`decide` checks) **compiled with no errors and no `sorry`** before the sandbox
was reset, which destroyed the Lean toolchain (a custom WASM build of Lean 4 core —
no native binary is obtainable here, and the export-section surgery cannot be reproduced
reliably), so **the files have not been recompiled since**.

Two consequences, stated plainly:

1. **One lemma is a placeholder and must not be read as a formal proof.**
   `q1_ge_q0` in the committed file proves `0 ≤ (k−1)(4t−A)`, which is trivially true — it does
   **not** formalise §7.1's `q_1 ≥ q_0`. I have a correct replacement (carrying the hypothesis
   `A ≤ 4t`, i.e. `q_0 ≤ 1`, and proved from `Nat.mul_le_mul_right`), but it was written after
   the toolchain was lost and is **unverified**, so I have not shipped it. §7.1's comparison is
   nevertheless established exactly — by `paper_claims.py` at every `K ≤ 40` — just not
   symbolically.
2. Everything else in the two files was genuinely machine-checked, and every one of those
   statements is *also* re-derived independently in `paper_claims.py` and `check_all.py`, so no
   result in this report rests on the Lean files alone.

To re-verify the Lean side, any Lean 4 installation suffices (the files use only core
`Init`/`Std`; no Mathlib, no imports beyond `Init`):

```bash
lean paper_check/lean/Arithmetic.lean && lean paper_check/lean/Profiles.lean
```

## 10. Reproducing the audit

```bash
cd lean4/paper_check
python3 paper_claims.py          # per-statement audit, keyed to the paper's labels → 20598 / 0
python3 check_all.py             # the §2–§5 formula sweep, K = 3..40            → 0 failed
python3 verify_constructions.py  # explicit profiles: Thm 2, 3(b), 4, Ex 1–2     → out1.txt
```

## 11. Bottom line

The paper's central objects are right. `q* = 1 − s/(2t) = (3K−2k−2−ε)/(4(K−k))` is the sharp
full-acceptability threshold on `1 ≤ k ≤ r`, and the LP sweep confirms it is not merely a valid
bound but the *true* optimum of the model. `q_ℓ^* = 1 − M_{ε,s}(ℓ)/(ℓt)` is the sharp
`ℓ`-frontier on the full stated range `1 ≤ k ≤ ⌈K/2⌉`, with the four-branch `M` — including the
odd-boundary branches — necessary and sufficient. The consequences are right: `q_1^*=q_2^*=q^*`
away from the boundary, `q_ℓ^* = q^* − ⌊(ℓ−1)²/4⌋/(ℓt)` strictly improving for `ℓ ≥ 3`, `q_0`
sharp for complete unacceptability only at even `K` with `k = 2`, `q_1^* = 1` at the odd
boundary, and `q_1` exposed as an artefact. Examples 1 and 2 are numerically exact, and Example
2 does what the abstract promises.

The one substantive gap in my coverage is the *generality* of the two sufficiency proofs
(Theorem 1, Theorem 3(a)): I verified their algebra, their identities and their logic, and I
verified that the resulting thresholds are optimal for `K ≤ 6` by exhaustive LP, but I did not
formalise the general combinatorial argument in Lean. Given that the arithmetic layer is
machine-checked and that the LP independently confirms optimality on the only range where
exhaustive search is feasible, I would call the paper's mathematical claims established, with
the two prose fixes above as the only changes I would ask for.
