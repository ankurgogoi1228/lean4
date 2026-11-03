# Verification report — *Sharp Qualified-Majority Thresholds for Social Acceptability of q-Condorcet Committees*

**Ankur Gogoi** (Department of Mathematics, Dibrugarh University)
Report dated 3 November 2026 · **audits the v1, v2 and v3 (polished) manuscripts**

> **Sign-off: GREEN FLAG** (issued 3 November 2026, on the v3 text).
>
> Scoped as follows. **In scope and passing:** every mathematical statement, identity, bound, case
> distinction, threshold, explicit profile and boundary classification; the abstract's definition;
> the `k=1` degenerate-case scoping; and the three v3 polish passages. **Not covered by the flag:**
> (i) the `.tex` has never been compiled — no TeX engine exists in either sandbox — so LaTeX
> presentation errors would not have surfaced; (ii) §7.2's attribution to the working-paper proof
> should be confirmed against the published appendix, though nothing depends on it; (iii) the Lean
> lemma `q1_ge_q0` is uncompiled, with §7.1 established numerically instead. None of these is a
> mathematical defect.
>
> **Verdict: clean.** The mathematics is correct — no false theorem, no wrong threshold, no failing
> construction. The two wording issues raised against v1 were fixed correctly and completely in v2,
> and the optional polish of v3 is also correct: I re-derived all three of its algebraic claims
> independently (§3) and every one holds. On the mathematical content I have nothing left to ask for.

| | v1 | v2 | v3 |
|---|---|---|---|
| Abstract's acceptability gloss | ✗ "a majority rank `a` in the top half" | ✅ `B_a ≤ A_a`, on-line neutral | ✅ unchanged |
| "`q_0` sharp only at even `K`, `k=2`" | ✗ true only for `2 ≤ k ≤ r` | ✅ scoped, `k=1` carved out | ✅ unchanged |
| "odd boundary `k=2`" ambiguity | — | ✗ one phrase, two cases | ✅ both cases named |
| Thm 4(a) stray "set `M=1`" | ✗ | ✗ | ✅ removed |
| Remark 2's `s/2` vs `s−ε` | vague | vague | ✅ clarified (algebra verified) |
| v2→v3 `.tex` diff | — | — | ✅ reviewed: 6 hunks, 7 paragraphs, prose only |
| Exact assertions checked | 20 598 | 21 019 | **22 796** |
| Failures | 0 | 0 | **0** |

Artifacts: `paper_check/paper_claims.py` (per-statement audit keyed to the paper's own labels),
`check_all.py`, `verify_constructions.py`, `lp.py`/`scan.py`, `lean/Arithmetic.lean`,
`lean/Profiles.lean`.

---

## 1. What was checked, and how

| Layer | Method | Scope | Result |
|---|---|---|---|
| **A. Every displayed statement** | exact rational arithmetic, keyed to the paper's labels | `K = 3…40`, all admissible `k`, all `1 ≤ ℓ ≤ k` | **22 796 assertions, 0 failures** |
| **B. Lemma 2** | brute-force enumeration of *every* ballot | `K = 3,4,5` (bounds), `K = 5,7` (tightness); all `k`, all `a`, all `K!` permutations | ✅ no counterexample; bounds attained |
| **C. The model itself** | exact rational LP over *all* profiles | `K = 3…6`, every `(k,ℓ)` | ✅ optimum `= q_ℓ*` in every case |
| **D. Constructions** | explicit integer profiles | Thm 2 (`K ≤ 8`), Thm 3(b) (`K ≤ 8`), Thm 4, Ex. 1–2 | ✅ all behave as claimed |
| **E. Formal proof** | Lean 4, no `sorry` | arithmetic core (§2–§6) + explicit profiles | ✅ 40 statements (caveat: §8) |

Layer C is the one that matters most for a paper of this kind: it shows the closed forms are the
*true optima of the voting model*, not merely internally consistent algebra.

## 2. The two v1 findings, and confirmation of the v2 fixes

**(a) The acceptability gloss.** v2's abstract states *"socially acceptable when no more voters
rank it below the line than above it, i.e. `B_a ≤ A_a` … on-line ranks are neutral"* — exactly the
§2 definition. No other sentence in the manuscript uses the "majority in the top half" phrasing, and
the neutral treatment of on-line ranks is applied consistently in every construction (Thm 2, the
Thm 3(b) boundary states, Thm 4(a) and Ex. 2 each put exactly one distinguished alternative on the
line, or none). ✅

**(b) The scope of "sharp only at even `K`, `k=2`."** Enumerating every `(K,k)` with
`q_comp* = q_0` over `K ≤ 40` returns exactly `K` even with `k ∈ {1, 2}`. v2 now scopes the
classification to `2 ≤ k ≤ r` (abstract, intro item 3, Cor. 1(c), §7.1, conclusion) — within which
the sharp pairs are exactly the even-`K`, `k=2` ones — and states the degenerate case explicitly:
for even `K`, `q_comp*(K,1) = q_1*(K,1) = q* = q_0` (sharp); for odd `K`,
`q_comp*(K,1) = q* = q_0 − 1/(4(K−1)) < q_0` (not sharp). Both halves verified. ✅ No stale instance
of the old claim survives anywhere in the text.

## 3. The v3 polish — re-derived independently

v3 changes no theorem, threshold, proof, profile or classification; it touches three passages of
prose. I checked each one's algebra from scratch rather than taking it on trust.

**1. Remark 2's clarifying clause.** Three identities, each verified for every `K ≤ 40`, every
`k ≤ r`, and separately for both parities:

- `4t − (3K−2k−2) = 2s − ε`. Dividing by 4 gives `t − (3K−2k−2)/4 = s/2 − ε/4`, which is exactly
  the claim that relaxing the sharp odd-`K` estimate to the parity-free `n(3K−2k−2)/4` leaves
  `nt − W_π(c_j) > n(s/2 − ε/4)`. ✅
- `q_0 − q^* = ε/(4t)`. So the quantity discarded by that relaxation is precisely the `−ε/(4t)`
  correction, as stated. ✅
- For odd `K`: `4(t − s/2) = 3K − 2k − 3`, i.e. `t − s/2 = (3K−2k−3)/4`. This is the claimed
  equivalence *retaining `s/2`* ⟺ `W_π(c_j) < n(3K−2k−3)/4`, and it also confirms that
  `n(3K−2k−3)/4` is the sharp odd-`K` form of `q^*` — i.e. that Diss–Mahajne's sharper Case 2 bound
  really is the paper's `q^*` in disguise. ✅

The accompanying gloss is right too: from Lemma 2 the on-line per-ballot deficit is `s−1 = s−ε`,
while `s/2` is the average deficit forced by `B_a > A_a`, and `q^* = 1 − s/(2t)` is what retains it.

**2. The two `k=2` cases, now named separately.** In-range odd `K ≥ 5` with `k = 2 ≤ r`:
`q_comp* = q^* = q_0 − 1/(4t) < q_0` ✅. Boundary instance `K = 3, k = 2 = r+1`:
`q_comp* = 1/2 < 3/4 = q_0` ✅. Both true, and the v2 ambiguity (one phrase pointing at two cases)
is resolved. ✅

**3. §7.1's restated range: "odd `K`: `q_0` is loose for complete unacceptability for `2 ≤ k ≤ r`."**
This is *stronger* than v2's `3 ≤ k ≤ r` and still correct: for odd `K` and `2 ≤ k ≤ r`,
`q_comp* = q_k^* = q^* − ⌊(k−1)²/4⌋/(kt) < q^* < q_0`, with the floor term vanishing at `k = 2` but
`q^* < q_0` holding by `1/(4t)` regardless. ✅ Verified for every odd `K ≤ 40`.

**Added tightness check on Lemma 2.** The two bounds `t−w ≥ s` (below the line) and `t−w ≥ s−1`
(on the line) are **attained** by some ballot for every `k` at `K = 5,7`, so they are best possible
per-ballot statements — which is what makes the §5 envelope sharp rather than merely valid. ✅

**4. The last link in Remark 2's chain.** The clause implicitly asserts two thresholds. Retaining
`s/2` gives threshold `1 − (s/2)/t = q^*`; relaxing to `s/2 − ε/4` gives
`1 − (s/2 − ε/4)/t = q_0` — so the relaxation turns the sharp `q^*` into exactly Diss–Mahajne's
`q_0`, which is the whole content of the diagnosis. Both identities verified for every `K ≤ 40`,
every `k ≤ r`, odd `K` for the second. ✅

### (d) The v2→v3 `.tex` diff — reviewed

The two `.tex` files are in the other sandbox, but the unified diff was supplied in full, so the
*content* of the change is checkable even though the files are not.

**Shape.** Six hunks, seven changed paragraphs, and every hunk has the same start line and the same
length on both sides (`-32,7/+32,7`, `-60,7/+60,7`, `-211,7/+211,7`, `-571,7/+571,7`,
`-640,13/+640,13`, `-720,7/+720,7`). That is a pure in-place replacement of seven paragraphs with
**no insertions and no deletions anywhere**, so no line number downstream can have shifted — which
independently supports "no other line differs" and the unchanged page count. ✅

**Content.** All seven are the expected ones, in the expected places: abstract, introduction
contribution 3, Remark 2, Thm 4(a)'s sharpness proof, §7.1 first paragraph, §7.1 second paragraph,
conclusion. I read each `+` line against the rest of the manuscript and against the algebra above:

- the five `k=2` disambiguations all state only facts I had already verified — `q_comp* = q_0` fails
  for odd `K` at `k=2` both in range (`K ≥ 5`) and at the boundary (`K = 3`); ✅
- the §7.1 strengthening from `3 ≤ k ≤ r` to `2 ≤ k ≤ r` is correct (and strictly stronger) ✅;
- Remark 2's new sentences are all identities I verified above, including the `q^* → q_0` link ✅;
- the Thm 4(a) deletion removes an assignment to `M` that is never referenced again in that proof —
  the exceptional ballot and the `n−1` ordinary ones carry the argument alone ✅.

No `+` line asserts anything new about the mathematics. The change is prose and one unused
assignment, as represented. ✅

**Byte identity — corroborated by the hash manifest.** The provenance record publishes SHA-256 for
fourteen files (the standalone `manifest.sha256` has fifteen entries, the extra one being the
provenance record itself). I checked the list itself rather than taking it on trust: all fourteen
embedded digests are valid 64-hex, there are thirteen distinct values, and there is **exactly one collision** —
`ce704e8df057477b…` for `Sharp_Threshold_q_Condorcet_Social_Acceptability.tex` *and*
`…_v3.tex`. Equal digests establish that those two files are byte-identical, so the `cmp` claim is
independently corroborated even though neither file is here. `…_v2.tex` carries a distinct digest
(`023ca38ae1f9364f…`), and no other pair collides, so no two supposedly-distinct files were
silently the same. ✅

Combined with the zero-drift diff shape and the 749/749 line counts, this is as far as the
`v2 → v3` transition can be pinned down without the files: identity of v3 with the formal source ✅,
seven prose paragraphs changed and nothing else ✅.

**Structural invariants, spot-checked against the v3 source supplied earlier.** One
`thebibliography`, nine `\bibitem`s, one `enumerate` (intro contributions), three `itemize` (the two
envelope regimes; the §6 parity transition; the two Thm 3(b) boundary state families), no standalone
References heading, and the starred thresholds (`q^*`, `q_ℓ^*`, `q_1^*`, `q_comp^*`) intact — all
consistent with the reported invariants.

### What I still could not verify

- **Rendering, and this one is material.** `P.pdf` is a plain-text `reportlab` rendering and
  `P.docx` a verbatim Courier rendering; neither is typeset. **The 9-page count therefore describes a
  plain-text artefact, not a typeset article**, and the package is *not* submission-ready even though
  the `.tex` is correct. I confirmed there is no TeX engine in this sandbox either
  (`pdflatex`, `xelatex`, `lualatex`, `tectonic`, `latexmk`, `pandoc` all absent, and no `reportlab`),
  so I cannot produce a typeset build from here. A real PDF needs a TeX installation — a separate
  build step, not a correction to the paper.
- **Provenance of the generator run** (`make_v2_tex.py` reproducing v2 from the persisted Markdown).
  The zero-drift diff shape is strong circumstantial support — a different generator would almost
  certainly have reflowed other lines — but not a proof.

## 4. §2–§3 Definitions and the two counting lemmas

- Weak/strict conventions kept separate, with the `q=1` distinction correctly drawn. ✅
- `A_a`, `B_a`, `rank > K−r` for below-line: consistent for both parities (`K−r = r` even, `r+1`
  odd). ✅
- `q_ℓ*` is an attained infimum, as claimed: Thm 3(a) gives sufficiency at `q = q_ℓ*`, 3(b) failure
  for every `q < q_ℓ*`. ✅
- **Lemma 1** (`W_π(a) ≥ qnt`): immediate. ✅
- **Lemma 2**: verified by exhaustive enumeration of all ballots for `K = 3,4,5` — every `k ≤ r`,
  every `a ∈ C`, every permutation: `t−w ≥ s` below the line, `≥ s−1` on it, `≥ 0` above, with the
  on-line case occurring exactly when `ε = 1`; and both non-trivial bounds are attained (`K = 5,7`).
  ✅
- **Remark 1** (`t = r+s−1`): ✅ all `K ≤ 40`, both parities; `s ≥ 2` when `ε=1, k ≤ r` ✅.

*Mechanisation note.* The paper's `s = r−k+1+ε` is correct; anyone formalising it should write
`K/2 + 1 + K%2 − k`, because with truncating subtraction a literal transcription silently makes the
below-line case unreachable for `k > r+1`. My Lean file does this. Not a paper error.

## 5. §4 Theorem 1, Theorem 2 (`ℓ = 1`)

- `2(2t−s) = 3K−2k−2−ε` ✅; `1 ≤ s ≤ t` ✅; `K ≥ 4 ⟹ s < t` ✅; `1/2 < q* < 1` for `K ≥ 4` ✅;
  `K=3, k=1 ⟹ s=t=2, q*=1/2` ✅.
- **Theorem 1.** The identity `sB + (s−1)O − ns/2 = (s/2)(B−A) + (s/2−1)O` is exact ✅, and the sign
  analysis is right in both parities (`ε=0`: the `O`-term is absent since `O = 0`; `ε=1`: `s ≥ 2` on
  `k ≤ r` so `s/2−1 ≥ 0`). The contradiction `nt−W > ns/2` vs `≤ ns/2` closes. ✅
- **Theorem 2.** The construction was implemented and run for every `(K,k)` with `q* > 1/2` up to
  `K = 8` and many rational `ρ`: a **strict** `q`-Condorcet profile with `A(a_1) < B(a_1)` exists in
  integers every time. ✅ Arithmetic of both ballot shapes re-derived by hand: above-line counts
  `(k−1)+s = r` (`ε=0`) and `(k−1)+(s−1) = r` (`ε=1`), below-line counts `r` in both, and the defeat
  fraction `ρ·(s/t) < 1−q` follows from `ρ < (1−q)t/s`, with `s/t = C(t−1,s−1)/C(t,s)`. ✅

## 6. §5 hierarchy, §6 boundaries, §7 comparisons

**Scope.** `q_0 < 1 ⟺ 2k < K+2 ⟺ k ≤ ⌈K/2⌉` ✅ — exactly the range on which Diss–Mahajne state
`q_0, q_1 < 1`.

**`M_{ε,s}`.** Four branches, exhaustive and disjoint; `M` may be a half-integer and the paper
handles this by writing `s/2` throughout ✅. The §5.1 boundary note — *"for odd `ℓ = 2m+1` with
`m ≥ 0`, `2M_{1,1}(ℓ) − ℓs = 2m²−1`, not `2m²`"* — verified including `m = 0` (both sides `−1`) ✅.

**`M ≤ ℓt/2`, hence `q_ℓ* ∈ [1/2,1]`.** ✅ every `K ≤ 40`, every admissible `(k,ℓ)`, boundary
included. The chain `ℓt − 2M = (2m+1)(r−1) − 2m² ≥ (2m+1)(2m) − 2m² = 2m²+2m ≥ 0` is correct, and
`r ≥ 2m+1` follows from `ℓ = 2m+1 ≤ k ≤ r`. ✅

**Lemma 3.** Writing `D_i(U) = (d_A+d_O)(b+o) − d_O·o`, the objective is minimised by maximising
`d_O` and minimising `d_A+d_O`; the value is then `(b+o)(s−1+b) − o(ε−o) = (b+o)(s−1+b)` because
`o ∈ {0,ε}`. ✅ Both counting inputs (`c_A+c_O ≤ k−b` and `c_O ≥ o`) are correct. ✅

**The convex envelope.** `ψ_A(b+1)−ψ_A(b) = s+2b` increasing ✅;
`ψ_B(b) − ½[ψ_A(b)+ψ_A(b+1)] = (s−2)/2` ✅ (so `B_b` is on the chord exactly at `s=2`, above it for
`s>2`, below it only at the boundary `s=1` — precisely why the boundary needs its own branches);
slopes `2b, 2b+2, 2b+2, 2b+4, …` at the boundary ✅, non-decreasing, so the polyline through
`A_0,B_0,A_1,B_1,…` *is* the lower envelope. Evaluations reproduce the `M` table. ✅

**Theorem 3(a).** `Σ(2b_i+o_i) > nℓ ⟺ x̄ > ℓ/2` ✅, then Lemma 3 + envelope + Jensen, plus strict
monotonicity of `ψ̲` right of `ℓ/2` (every slope there is `≥ 2`) ✅, against
`Σ D_i(U) = Σ_{a∈U}Σ_d n_{da} ≤ ℓt(1−q)n` ✅.

**Theorem 3(b).** Regular regime: `(k−ℓ)+(ℓ−b)+(ŝ_b−ε) = r` above the line, `b+(t−ŝ_b) = r` below,
defeat fraction exactly `Eψ/(ℓt)` ✅; `b ≤ p+1 ≤ r ≤ t` holds. Odd boundary: the `A_b` state gives
`r` above / `r` below with `d_O` on the line, the `B_b` state gives `k−1 = r` above with `u_0` on the
line ✅; defeat fractions `b²/(ℓt)` and `b(b+1)/(ℓt)` ✅; both mixtures give `Ex > ℓ/2` and
`Eψ → M_{1,1}(ℓ)` ✅. The `A_0` state's need for `C∖U ≠ ∅` is flagged and never violated ✅.

**Corollary 1.** (a) ✅ (b) `2M−ℓs = 2⌊(ℓ−1)²/4⌋` for every `K ≤ 40`, `2 ≤ k ≤ r`, `1 ≤ ℓ ≤ k` ✅
(c) ✅ including the `3 ≤ k ≤ r` range and both halves of the `k=2` split (d) ✅ (`q_1^* = 1`,
`q_2^* < 1` at every odd boundary).

**Theorem 4.** (a) sufficiency (`C` occupies ranks `1..r+1`, so `B_a = 0`) ✅; sharpness at
`K=5,k=3, n=101` machine-checked by `decide` in Lean (`A=0, B=1, O=n−1`, `n_{a_1b_1}=n−1 > qn` iff
`δn > 1`) ✅. (b) `k = r+ε+m`, `t = r−m ≥ 1`, `a_1` at rank `r+ε+1` with `m−1` members behind it,
`B_{a_1}=n > A_{a_1}=0` while `C` wins unanimously ✅. (c) vacuous ✅.

**Corollary 2.** `q_0 = 1−1/(4r)` ✅; `M_{1,1}(k)/k = m/2 > 1/4` (`k=2m`) and
`m(m+1)/(2m+1) > 1/4` (`k=2m+1`, `m≥1`) ✅, so `q_k^* < q_0` at every boundary size including
`K=3,k=2` (`1/2 < 3/4`) ✅. The `q=1` argument `Σ_{a∈C}(B_a−A_a) = n(m−r) = n(k−K) < 0` is correct,
and it is what makes `q_k^*` exist where `q_1^*` does not. ✅

**Examples.** Example 1: `M_{1,1}(1,2,3) = 0,1,2`; `q_1^*=1`, `q_2^*=3/4`, `q_comp^*=2/3`;
`q_0=7/8`, `q_1=23/24` — all reproduced three ways ✅. Example 2: margins `25,26,26,26,26,26`, all
`> 24.96`; `A_{a_1}=0, B_{a_1}=1, O_{a_1}=25`; `24/25 > 23/24` since `576 > 575` — machine-checked
against a real ballot model in Lean ✅. It does exactly what the paper claims.

**§7.1.** `q_1 − q_0 = (k−1)(1−q_0)/k ≥ 0`, equality in range only at `k=1` ✅;
`q_0 ≤ q_1 ⟺ q_0 ≤ 1 ⟺ k ≤ (K+2)/2` ✅, with the vacuity for `q_0 > 1` and `q_0=q_1=1` at the even
boundary ✅; even `K`: `q* = q_0`, so their first bound is the sharp *full*-acceptability threshold
and `q_1 > q*` for `k>1` ✅; odd `K`: `q* = q_0 − 1/(4(K−k)) < q_0 ≤ q_1` ✅. The `k=1` paragraph is
correct in both parities ✅, and the v3 restatement to `2 ≤ k ≤ r` is correct and stronger ✅.

**§7.3.** `q*(K,1) = (3K−4)/(4K−4)` even, `(3K−5)/(4K−4)` odd ✅ for all `K ≤ 40` — Mahajne–Volij
recovered exactly.

**§7.2, the `K=4,k=2` family.** Re-derived: `n = 12m+1`; all four margins `9m`; `A_a=A_b=6m`,
`B_a=B_b=6m+1`. The text correctly says the profile is **not** `3/4`-Condorcet (ratio
`9m/(12m+1) < 3/4`) and uses the limit `↑3/4` for sharpness of `q_2^* = q_0 = 3/4` ✅ (Lean-checked
for `m = 1,2,3,10`).

## 7. Remaining items

**One open item; nothing in it is an error.**

1. **§7.2's diagnosis of `q_1` is unverifiable from here.** The claim — that the working-paper proof
   bounds `k−1` members by the trivial maximum `n(K−k)` and one by `q_0n(K−k)`, producing
   `(k−1+q_0)/k = q_1` — is arithmetically **coherent**: I checked that this is exactly the
   contradiction threshold, and the `4t − (3K−2k−2) = 2s − ε` identity above independently confirms
   that their sharper odd-`K` bound `n(3K−2k−3)/4` is the paper's `q^*` in disguise. But it is a
   statement about the internal structure of a proof in halshs-02003292 / halshs-02011732, which I
   cannot consult. **Plausible, not verified. Nothing else in the paper depends on it.**
2. **(Now resolved.)** The claim that only those passages changed is supported by the diff shape
   (§3(d)): six same-length in-place hunks, no insertions or deletions. What remains unchecked is
   byte-identity/provenance and the rendered outputs (§3, "What I still could not verify").

Items 2–4 of my earlier list — the "odd boundary `k=2`" ambiguity, the stray "set `M=1`", and
Remark 2's compressed phrasing — are all **resolved in v3**, and the new Remark 2 clause is
algebraically correct.

## 8. Status of the Lean artifacts — read this

`lean/Arithmetic.lean` (40 statements) and `lean/Profiles.lean` (ballot model + ~40 `decide`
checks) **compiled with no errors and no `sorry`** before the sandbox was reset. The reset destroyed
the Lean toolchain (a custom WASM build of Lean 4 core — no native binary is obtainable in this
environment, and the export-section surgery that made the WASM usable cannot be reproduced reliably),
so **the files have not been recompiled since**. Two consequences:

1. **`q1_ge_q0` is uncompiled.** The version in the file is the honest one: it carries the hypothesis
   `A ≤ 4t` (i.e. `q_0 ≤ 1`, exactly §7.1's condition), states `k·q_0 ≤ k·q_1` cross-multiplied over
   the common denominator `4tk`, and reduces to `Nat.mul_le_mul_right` plus `omega`. It replaced a
   vacuous one-liner that proved `0 ≤ x` and did not formalise §7.1 at all. Because the replacement
   was written after the toolchain was lost it is **unverified**; §7.1's comparison is nevertheless
   established exactly, at every `K ≤ 40`, by `paper_claims.py`.
2. Everything else in the two files was genuinely machine-checked, and every one of those statements
   is *independently* re-derived in `paper_claims.py` / `check_all.py`, so no conclusion in this
   report rests on the Lean files alone.

Re-verify with any Lean 4 installation (core only — the files import nothing beyond `Init`):

```bash
lean paper_check/lean/Arithmetic.lean && lean paper_check/lean/Profiles.lean
```

## 9. History: corrections to my own earlier reports

My first report was written from a reconstruction of the paper before the source was available.
**Three of its four "findings" were my errors**, recorded here so the record is not misread:

| Earlier claim | Status |
|---|---|
| "The Diss–Mahajne profile in §7.2 is not `3/4`-Condorcet — a discrepancy" | **Retracted.** The paper says so itself, in those words, and uses the limit to witness `q_2^* = q_0 = 3/4`. |
| "The floor identity is false at the odd boundary; needs an exclusion" | **Retracted.** §5.1 states `2m²−1` explicitly and Cor. 1 is scoped to `2 ≤ k ≤ r` to exclude the boundary. |
| "`q_1 ≥ q_0` needs the hypothesis `q_0 ≤ 1`" | **Retracted.** §7.1 states the equivalence, the vacuity, and `q_0=q_1=1` at the even boundary. |
| The two wording issues raised against v1 | **Correct, and fixed in v2** (§2 above). |
| The three nits raised against v2 | **Correct, and fixed in v3** (§3 above). |

## 12. Sign-off

Re-run at sign-off on the v3 text: `paper_claims.py` **22 796 assertions, 0 failures**;
`check_all.py` **0 failures**; `verify_constructions.py` all constructions as claimed, with the only
`False` rows being the intended negative controls — the §7.2 profile failing weak `3/4`-Condorcet at
`m = 1,2,3,10` (margins `9m` against a required `9m + 3/4`, exactly as the paper states) and strict
`q`-Condorcet failing at `q = 1` (impossible by definition). Reading of the v3 source: eight
sections, one `enumerate`, three `itemize`, four `cases` blocks, nine `\bibitem`s with every `\cite`
key resolved, no standalone References heading, no leftover `M=1`, starred thresholds intact, and
the `k=2` disambiguation present in all four places (abstract, introduction, §7.1, conclusion).

**GREEN FLAG** on the mathematics and the manuscript text, scoped as in the header.

## 10. Reproducing the audit

```bash
cd lean4/paper_check
python3 paper_claims.py          # per-statement audit keyed to the paper's labels → 22796 / 0
python3 check_all.py             # the §2–§5 formula sweep, K = 3..40                → 0 failed
python3 verify_constructions.py  # explicit profiles: Thm 2, 3(b), 4, Ex. 1–2         → out1.txt
```

## 11. Bottom line

The paper is in good shape. `q^* = 1 − s/(2t) = (3K−2k−2−ε)/(4(K−k))` is the sharp
full-acceptability threshold on `1 ≤ k ≤ r`, and the LP sweep confirms it is the *true* optimum of
the model rather than merely a valid bound. `q_ℓ^* = 1 − M_{ε,s}(ℓ)/(ℓt)` is the sharp `ℓ`-frontier
on the full stated range `1 ≤ k ≤ ⌈K/2⌉`, with the four-branch `M` — odd-boundary branches included
— necessary and sufficient. The consequences hold up: `q_1^*=q_2^*=q^*` away from the boundary;
`q_ℓ^* = q^* − ⌊(ℓ−1)²/4⌋/(ℓt)` strictly improving for `ℓ ≥ 3`; `q_0` sharp for complete
unacceptability exactly at even `K` with `k = 2` inside `2 ≤ k ≤ r`, with the degenerate `k = 1`
case correctly carved out; `q_1^* = 1` and `q_2^* < 1` at the odd boundary; and `q_1` exposed as an
artefact. Examples 1 and 2 are numerically exact, and Example 2 does what the abstract promises.

The one gap in my coverage is the **generality** of the two sufficiency proofs (Thm 1, Thm 3(a)):
I verified their algebra, their identities and their logic, and confirmed the thresholds are optimal
by exhaustive LP for `K ≤ 6`, but did not formalise the general combinatorial argument. Given that
the arithmetic layer is machine-checked and that the LP independently confirms optimality on the
only range where exhaustive search is feasible, I regard the mathematical claims as established. The
outstanding items are the unverifiable §7.2 attribution, the uncompiled Lean lemma, and the
packaging claims I cannot inspect — none of which bears on a theorem.
