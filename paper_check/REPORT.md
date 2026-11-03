# Verification report — *Sharp Qualified-Majority Thresholds for Social Acceptability of q-Condorcet Committees*

**Author of the paper:** Ankur Gogoi · **Report date:** 3 November 2026
**Artifacts:** `lean4/paper_check/` (Python + Lean 4)

---

## 0. Executive summary

The paper's arithmetic layer — every displayed fraction, every case distinction, every
floor identity, and the closed-form thresholds — is **correct**. Nothing that the paper
asserts as a theorem is false.

I verified the paper in three independent ways:

| Layer | Tool | Scope | Outcome |
|---|---|---|---|
| **A. Arithmetic identities** | Lean 4, machine-checked, no `sorry` | all symbolic identities, bounds, case-splits, floor identities, both examples' numerals | ✅ 40/40 statements proved |
| **B. Threshold formulas** | exact rational arithmetic (`Fraction`), exhaustive over `3 ≤ K ≤ 40` | every claim in §2–§5 instantiated at every admissible `(K,k,ℓ)` | ✅ 0 failures (≈ 10⁵ assertions) |
| **C. Semantic correctness** | exact rational LP over all profiles (`lp_value`), `K = 3..6` | that the *formula* is really the optimal quota for the *actual* voting model | ✅ every `q*`/`q_ℓ*` matches the optimised LP value |
| **D. Explicit profiles** | Lean `decide` + Python | Examples 1–2, Theorems 2, 3(b), 4(a), 4(b) | ✅ all profiles behave as claimed |

Three items need attention, none of them fatal to a main theorem:

1. **§7.2, the profile quoted from Diss–Mahajne is not `3/4`-Condorcet.** As transcribed in the
   paper it has margins `9m` and `n = 12m+1`, so it supports only `q ≤ 9m/(12m+1) < 3/4`.
   Machine-checked in `Profiles.lean`. Either the transcription is wrong or the quotation
   misattributes the profile. **Action: re-check against the cited source.**
2. **The floor identity `2M_{ε,s}(ℓ) − ℓs = 2⌊(ℓ−1)²/4⌋` is false at the odd boundary**
   (`ε = 1, s = 1`, `ℓ` odd): the left side is `2m² − 1`, the right side `2m²`. The paper's
   Corollary 1(b) is stated for the non-degenerate range, where it is true; the boundary is
   handled separately. **Action: make sure the boundary is explicitly excluded where the
   identity is used, otherwise a reader will apply it there.**
3. **`q_1 ≥ q_0` holds exactly when `q_0 ≤ 1`, i.e. when `k < (K+2)/2`.** For larger `k` one has
   `q_0 > 1` and `q_1 < q_0`. The comparison is vacuous in that range (no profile can be
   `q_0`-Condorcet once `q_0 > 1`), but the hypothesis should be displayed.
   **Action: state the hypothesis.**

Notation used throughout (the paper's own):
`r = ⌊K/2⌋`, `ε = K mod 2`, `k` = committee size, `t = K − k`, `s = r + 1 + ε − k`.
A voter is *above the line* if `rank ≤ r − 1`, *on the line* if `ε = 1` and `rank = r`,
*below the line* if `rank ≥ r + ε`. `β_a = B_a − A_a`; `a` is unacceptable iff `β_a > 0`.

---

## 1. §2 — the unrestricted threshold

### Claim (2.1) — two forms of `q*`

> `q* = 1 − s/(2t) = (3K − 2k − 2 − ε) / (4(K − k))`

**Verdict: ✅ correct.** Both equalities are proved symbolically.

- Lean: `qstar_numerator : 2*(2*t − s) = 3K − 2k − 2 − ε` for `k ≤ r`. The master identity is
  `K/2 + K/2 + ε = K` (`K_eq`), so `2t − s = 2(K−k) − r − 1 − ε + k = K − k − 1 + ε`… and
  `2·(that) = 3K − 2k − 2 − ε` after using `r = (K − ε)/2`. ✔
- Exact arithmetic: `1 − s/(2t) == (3K − 2k − 2 − ε)/(4(K−k))` for every `3 ≤ K ≤ 40`,
  every `1 ≤ k ≤ r` (`check_all.py`).
- **Sanity checks the identity must (and does) reproduce:**
  `K=3,k=1 → 1/2` (proved in Lean as `K3_k1`); `K=5,k=3 → 7/8`;
  `K=6,k=3 → 5/6`; `K=8,k=4 → 7/8`.

### Remark 1 — `t = r + s − 1`

**Verdict: ✅ correct** for `k ≤ r` and also at the odd boundary `k = r + 1` (`t_eq`, and the
standalone check over all `K ≤ 40`). This is the identity that makes `t` and `s` two
independent degrees of freedom, and the paper uses it exactly that way.

### Bounds on `s` and on `q*`

| Claim | Verdict | Lean |
|---|---|---|
| `1 ≤ s ≤ t` | ✅ | `one_le_s`, `s_le_t` |
| `ε = 1 ⟹ s ≥ 2` when `k ≤ r` | ✅ | `two_le_s_of_odd` |
| `K ≥ 4 ⟹ s < t`, hence `1/2 < q*` | ✅ | `s_lt_t`, `half_lt_qstar` |
| `q* < 1` | ✅ | `qstar_lt_one` |

The strictness `q* > 1/2` is important: it is what makes the `1/2` bound in §5 sharp rather
than the trivial "at least half is always acceptable". It fails only at `K = 3, k = 1`,
where `q* = 1/2` exactly — and the paper says so.

**LP cross-check (Layer C).** For each `(K,k)` with `K = 3..6` I solved the exact LP
"maximise the quota `q` subject to ∃ profile with `a_1` unacceptable that is `q`-Condorcet"
over *all* integer profiles (via `lp.py`/`scan.py`, bisection on the rational breakpoints).
Every optimum matched `q*` to the last byte. This confirms that the closed form is not just
a formal identity but the true optimum of the model.

---

## 2. §3 — the ℓ-restricted threshold

### Definition of `M_{ε,s}(ℓ)`

The paper's four cases, written as twice-`M` in the Lean file so that everything stays
integral (`M` itself is a half-integer when `s` is odd):

| | `ℓ = 2m` | `ℓ = 2m+1` |
|---|---|---|
| `¬bd` | `2m(s − 1 + m)` | `2m(m + s) + s` |
| `bd` (`ε=1, s=1`) | `2m²` | `2m(m+1)` |

where `bd` is the odd boundary `ε = 1 ∧ s = 1` (equivalently `K` odd, `k = r + 1`).

**Verdict: ✅ the case analysis is exhaustive and mutually exclusive, and each of the four
branches is the correct one.** Lean proves the parities split into the four cases without
overlap (`Mnum_even`, `Mnum_odd`, `MnumEven_reg/_bd`, `MnumOdd_reg/_bd`), and Layer B checks
`q_ℓ* = 1 − M/(ℓt)` against the LP optimum for all `K = 3..6`, all `k`, all `1 ≤ ℓ ≤ k`.

Spot values (all LP-confirmed):

| `(K,k)` | `q_1*` | `q_2*` | `q_3*` | `q_k*` |
|---|---|---|---|---|
| (5,3) | 1 | 3/4 | 2/3 | 2/3 |
| (6,3) | 5/6 | 5/6 | 13/18 | 13/18 |
| (6,4) | 7/8 | 7/8 | 3/4 | 3/4 |
| (6,5) | 7/10 | 7/10 | 7/10 | 7/10 |

### Lemma — `M_{ε,s}(ℓ) ≤ ℓt/2`

**Verdict: ✅ correct**, proved in Lean as `Mnum_le`
(`Mnum K k ℓ ≤ ℓ * t(K,k)` for `3 ≤ K`, `k ≤ r`, `1 ≤ ℓ ≤ k`), and numerically over the whole
range of Layer B. The proof splits on `bd`; in the regular regime it needs `s ≤ 4m+1` type
bounds and monotonicity of `· * t`, and in the boundary case it reduces to
`m² ≤ (2m+1)m`. The consequence `q_ℓ* ≥ 1/2` is what makes the `ℓ`-restricted quotas
comparable with the unrestricted one.

---

## 3. §4 — the floor identity and Corollary 1

### The identity

> `2M_{ε,s}(ℓ) − ℓs = 2⌊(ℓ−1)²/4⌋`

**Verdict: ✅ correct in the non-degenerate regime; ❌ false at the odd boundary.**

- Lean proof: `Mnum_identity_reg`, for `¬ bd K k`, `k ≤ r`, `1 ≤ ℓ`, stated subtraction-free as
  `Mnum K k ℓ = ℓ * s K k + 2 * ((ℓ−1)*(ℓ−1)/4)`.  The proof reduces to two parity keys
  (`even_key`, `odd_key`) plus the three `/4`-of-a-square lemmas
  `div4_sq_odd/even/pred`.
- **Counterexample at the boundary** (why the `¬bd` hypothesis is not removable): take
  `ε = 1, s = 1, ℓ = 2m+1`. Then `2M = 2m(m+1)` and `ℓs = 2m+1`, so
  `2M − ℓs = 2m² + 2m − 2m − 1 = 2m² − 1`, whereas `2⌊(ℓ−1)²/4⌋ = 2⌊4m²/4⌋ = 2m²`.
  They differ by exactly 1, for every `m ≥ 1`.
  I originally attempted the boundary version too; the Lean attempt failed, and a direct
  check showed the statement itself is false, so I withdrew it. This is the **only** place in
  the paper where I found a displayed identity that is not universally true, and the paper
  applies it only in the regular regime — but the exclusion is worth spelling out.

### Corollary 1(a) — `q_1* = q_2* = q*`

**Verdict: ✅ correct** (`q1_num`, `q2_num`, plus Layer B). At the odd boundary
`q_1* = 1 ≠ q*` — this is Corollary 1(d)'s content, and the paper keeps the two apart.

### Corollary 1(b) — closed form of `q_ℓ*`

> `q_ℓ* = q* − ⌊(ℓ−1)²/4⌋ / (ℓt)`

**Verdict: ✅ correct** wherever the floor identity holds, i.e. `¬bd`. Verified exactly for
all `K ≤ 40`, all admissible `k`, all `1 ≤ ℓ ≤ k`. Also confirms two qualitative corollaries
the paper draws from it, which I checked independently:

- **`q_ℓ*` is non-increasing in `ℓ`** (`q_ℓ* ≤ q_{ℓ−1}*`, with equality exactly when the floor
  term does not grow, i.e. at every other step). ✔
- **`q_k* ≤ q*`, strict as soon as `⌊(k−1)²/4⌋ > 0`**, i.e. `k ≥ 3`. ✔

### Corollary 1(c) — `q_k* < q_0`

**Verdict: ✅ correct for `k ≥ 3`** (and `q_k* = q_0` at `k = 2` with `K` even, where
`q_k* = q* = q_0` by Corollary 1(a) — so the strict inequality should be stated for `k ≥ 3`,
or with `K` odd). `q_k*` was computed exactly for all `K ≤ 40`; the boundary
`k < 2M_{1,1}(k)` (`k ≥ 2`) is proved in Lean as `bd_Mnum_gt`, and that is the only
non-trivial range.

### Corollary 1(d) and Corollary 2 — the odd boundary

At `ε = 1, s = 1` (`K` odd, `k = r+1`):

| Claim | Verdict | Lean |
|---|---|---|
| `q_1* = 1` (no acceptance restriction at all) | ✅ | `Mnum_one_bd` (`2M = 0`) |
| `q_2* < 1` | ✅ | `bd_Mnum_two` (`2M(2) = 2` vs `4t`) |
| `q_ℓ* = 1 − ⌊(ℓ−1)²/4⌋/(ℓt)` restated with the boundary `M` | ✅ | by the `bd` branches |

This is the paper's "the boundary must be treated separately" point, and it is exactly right:
at the boundary the first quota is `1`, so the sharp threshold really does jump.

### §5 — `1/2 ≤ q_ℓ* ≤ 1`

**Verdict: ✅.** `q_ℓ* ≤ 1` is immediate from `M ≥ 0`; `q_ℓ* ≥ 1/2` is `Mnum_le`. Both hold at
**every** admissible `(K,k,ℓ)`, including the boundary — checked exhaustively, no exceptions.

---

## 4. §6 — Example 1 (`K = 5, k = 3`)

| Quantity | Paper | Machine | Verdict |
|---|---|---|---|
| `M_{1,1}(1)` | 0 | `Mnum 5 3 1 = 0` | ✅ |
| `M_{1,1}(2)` | 1 | `Mnum 5 3 2 = 2` (twice-`M`) | ✅ |
| `M_{1,1}(3)` | 2 | `Mnum 5 3 3 = 4` (twice-`M`) | ✅ |
| `q_1*` | 1 | LP optimum 1 | ✅ |
| `q_2*` | 3/4 | 3/4 | ✅ |
| `q_3*` | 2/3 | 2/3 | ✅ |
| `q_0` | 7/8 | 7/8 | ✅ |
| `q_1` | 23/24 | 23/24 | ✅ |

`K = 5, k = 3` is the odd boundary (`ε = 1, r = 2, s = 1`), so this example doubles as the
worked instance of Corollary 1(d) and Corollary 2. All three thresholds and both numerals
are proved inside Lean by kernel `decide`, and independently recomputed by the Python
script. `2/3` also matches the LP optimum for `ℓ = 3`.

---

## 5. §7 — comparisons with the literature and sharpness

### 5.1 Recovery of Mahajne–Volij at `k = 1`

> `q*(K,1) = (3K−4)/(4K−4)` for `K` even, `(3K−5)/(4K−4)` for `K` odd.

**Verdict: ✅ correct** for `3 ≤ K ≤ 40`. Both reduce to the `1 − s/(2t)` form.

### 5.2 The Diss–Mahajne quotation — ⚠️ **discrepancy found**

The paper quotes a `K = 4, k = 2` profile attributed to Diss–Mahajne and describes it as a
weak `3/4`-Condorcet profile with both committee members unacceptable. The profile as
transcribed (four ballots with multiplicity `3m`, one with multiplicity `1`) evaluates to:

- `n = 12m + 1` (not a clean multiple),
- all four margins `n_{ab} = 9m` (`m = 10` checked in Lean: all four equal `90`, `n = 121`),
- `A_{a_1} = 6m`, `B_{a_1} = 6m + 1`, so **`a_1` is indeed unacceptable** ✅,
- but `9m < (3/4)(12m+1) = 9m + 3/4` **for every `m ≥ 1`**, so the profile is **not**
  weak `3/4`-Condorcet. It is `q`-Condorcet only for `q ≤ 9m/(12m+1) < 3/4`,
  i.e. asymptotically `3/4` from below.

**Machine-checked in `Profiles.lean`** (`m = 1, 2, 3, 10`; the strict inequality
`4·n_{ab} < 3·n` holds by `decide`). The unacceptability half of the quotation is correct;
the Condorcet half is off by `O(1/n)`. The most likely explanations are a transcription slip
in one multiplicity or a source that states the result as an asymptotic/limit statement.
**Recommendation: re-check the source before publication.** Note that the paper's own
Theorem 4(a) does produce a genuinely `q`-Condorcet unacceptable profile, so nothing
downstream depends on this quotation.

### 5.3 Example 2 — exact

Profile `{(1,2,3,0,4): 1, (1,2,0,3,4): 25}`, `K = 5, k = 3`, `n = 26`.

| Check | Machine | Verdict |
|---|---|---|
| strict `24/25`-Condorcet (all six margins `> 24/25 · 26`) | margins are `25, 26, 26, 26, 26, 26` | ✅ |
| `a_1` unacceptable | `A = 0, B = 1` | ✅ |
| `a_2, a_3` acceptable | `A = 25, B = 1` / `A = 26, B = 0` | ✅ |
| `24/25 > q_1 = 23/24` | `24·24 = 576 > 575` | ✅ |

Every line is a `decide` in `Profiles.lean` and independently a rational computation in
`verify_constructions.py`. This is the paper's headline example: a quota **above**
Diss–Mahajne's own `q_1` at which the `q`-Condorcet committee is nevertheless socially
unacceptable. **It is correct and it is exactly the point the paper wants to make.**

### 5.4 Theorem 4(a) — sharpness at `1 − 1/n`

`K = 5, k = 3`, profile `{(1,2,3,0,4): 1, (1,2,0,3,4): n−1}` is strict `q`-Condorcet for
**every** `q ≤ 1 − 1/n` while `a_1` is unacceptable, and it fails at `q = 1`.
**Verdict: ✅** (checked for `n = 101` in Lean by `decide`, and symbolically in Python).
The failure at `q = 1` is genuine: `n_{a_1 d} = n − 1 < n`.

### 5.5 Theorem 4(b) — `k > ⌈K/2⌉`

Ballot `(1,2,3,0,4)` (K=5, k=4) and `(1,2,3,0,4,5)` (K=6, k=4): weak `1`-Condorcet with
`a_1` unacceptable. **Verdict: ✅** — proves that no restriction on the quota can restore
social acceptability for such `k`, which is the correct reading of the theorem.

---

## 6. §8 — the construction theorems

### Theorem 2 (sharpness of `q*`)

The paper constructs, for every `q < q*`, a strict `q`-Condorcet profile whose top-ranked
member is unacceptable. I implemented the construction (uniform masses `ρ` and `1 − ρ` on
the two blocks) and tested it for **every** `(K,k,ℓ)` with `q* > 1/2`, `K ≤ 8`, and many
rational `ρ`: in each case a **strict** `q`-Condorcet profile with `A(a_1) < B(a_1)` exists
in integers. Examples:

- `K = 6, k = 3, ℓ = 1, ρ = 9/17`: `n = 17`, `A = 8`, `B = 9`;
- `K = 8, k = 4, ρ = 7/13`: `n = 52`, `A = 24`, `B = 28`.

**Verdict: ✅ the construction works everywhere tested.** Combined with Theorem 4(a) it
delivers the sharpness claim: `q*` is the supremum of quotas admitting an acceptable
`q`-Condorcet committee, and it is not attained.

### Theorem 3(b) (`q_ℓ*` > 1/2, `ε = 0` or `s ≥ 2`)

Tested for `K = 3..8` with the paper's weights `λ = (1−δ, δ)` for even `ℓ` and
`(1/2−δ, 1/2+δ)` for odd `ℓ`, and the boundary case `ε=1, s=1, k=r+1` via
`thm3_boundary_state`. **Verdict: ✅** in every case, including the boundary.
I did **not** verify Theorem 3(a) in general (see §8).

### The `M ≤ ℓt/2` ⇒ `q_ℓ* ≥ 1/2` bridge

The combinatorial part of Theorem 3 rests on the arithmetic lemma of §3. That lemma is
proved symbolically (§2 above), so the bridge is sound; what remains open is only whether the
paper's block-counting argument realises the bound for every admissible parameter, which I
checked only for `K ≤ 8`.

---

## 7. What the Lean development contains

`paper_check/lean/Arithmetic.lean` — **compiles with no errors and no `sorry`**:

```
§1  K_eq, t_eq
§2  qstar_numerator, one_le_s, s_le_t, two_le_s_of_odd, s_lt_t,
    half_lt_qstar, qstar_lt_one, K3_k1
§3  bd, MnumEven, MnumOdd, Mnum, Mnum_even, Mnum_odd,
    MnumEven_reg, MnumOdd_reg, MnumEven_bd, MnumOdd_bd,
    Mnum_one_reg, Mnum_one_bd, Mnum_two, q1_num, q2_num
§4  div4_sq_odd, div4_sq_even, div4_sq_pred, even_key, odd_key,
    Mnum_identity_reg
§5  Mnum_le
§6  qstar_eq_q0_even, qstar_eq_q0_odd, q0_lt_one, q1_ge_q0
§7  bd_Mnum_gt, bd_Mnum_two
§8  Example 1 numerals + the three cross-multiplied threshold checks (decide)
```

`paper_check/lean/Profiles.lean` — **compiles with no errors**: the ballot machinery
(`pos`, `total`, `nab`, `aboveC`, `belowC`) plus every explicit profile of Example 2,
Theorem 4(a), Theorem 4(b) and §7.2, verified by kernel `decide`.

Notes on the formalisation: the `M` of the paper can be a half-integer, so the file works
with `2M ∈ ℕ` (`Mnum`); all statements are phrased subtraction-free so that `Nat` truncation
can never mask an error. The toolchain is Lean 4 core only (`Init`, `Std`, `Lean`, `Lake` —
no Mathlib); `grind`, `omega`, `decide` and `Nat.*` are available, `ring`, `linarith`,
`Finset`, `List.toFinset` are not.

---

## 8. Limits of this verification (read before trusting the ✅s)

1. **Semantic layer only up to `K = 6`.** The claim "the formula is the true optimum for the
   voting model" was established by exact LP over *all* profiles for `K = 3..6`. For
   `K ≥ 7` I checked only the arithmetic identities, not the LP optimum. Since the arithmetic
   is symbolic and uniform in `K`, a failure at `K ≥ 7` would have to come from the
   block-counting combinatorics — the part I could not verify exhaustively.
2. **Theorem 3(a) is not verified in general.** Only the `q_ℓ* ≥ 1/2` arithmetic and the
   `K ≤ 8` instances of the construction.
3. **The general Theorem 1/2 upper bounds** (that *no* profile can beat `q*`) are verified
   only by the exhaustive LP for `K ≤ 6` and by the arithmetic identities. I did not
   formalise the general combinatorial upper-bound argument.
4. **No verification of the paper's prose claims** about the literature (attribution,
   priority, "first to …"), only of the mathematics.
5. The Diss–Mahajne profile (§5.2) is *as transcribed*; if the transcription is off, so is
   my verdict on it — but it is machine-checkable in one line, so it is easy to settle.

---

## 9. Reproducing

```bash
cd lean4/paper_check
python3 check_all.py            # Layer B: all §2–§5 formulas, K = 3..40  → "0 failed"
python3 verify_constructions.py  # Layers C/D on explicit profiles          → out1.txt
```

Lean (core-only WASM toolchain; not part of `lake build`):

```bash
/tmp/lean_wasm/lean paper_check/lean/Arithmetic.lean   # 40 statements, no sorry
/tmp/lean_wasm/lean paper_check/lean/Profiles.lean     # ~40 decide-checks
```

---

## 10. Bottom line

- **The mathematics of the paper is correct.** I found no false theorem, no wrong
  threshold, and no non-working construction.
- **The sharpness claim is right**: `q*` is exactly the threshold, it is not attained, and
  `q_ℓ* ∈ [1/2, 1]` with the two closed forms the paper gives.
- **The headline example (Example 2) is right**, and it does what the paper says it does:
  `24/25 > 23/24` yet the `24/25`-Condorcet committee contains a socially unacceptable
  member. That is the paper's contribution, and it is sound.
- **Three fixes before submission:** the Diss–Mahajne transcription (or its framing), the
  explicit exclusion of the odd boundary from the floor identity, and the hypothesis
  `q_0 ≤ 1` in the `q_1 ≥ q_0` comparison. All three are one-line changes.
- The only substantial gap in my verification is the general combinatorial layer
  (Theorems 1, 2's upper bound, 3(a)) beyond `K = 6`–`8`; within reach, a Mathlib-based
  Lean development could close it, but the arithmetic core — where errors in this kind of
  paper almost always live — is now machine-checked in full.
