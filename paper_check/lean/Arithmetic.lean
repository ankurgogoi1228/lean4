/-
  Arithmetic layer of

    Ankur Gogoi, "Sharp Qualified-Majority Thresholds for Social Acceptability
    of q-Condorcet Committees".

  Every formula, identity and numerical inequality of the paper that involves only
  the parameters K, k, l (and the derived r, eps, s, t, M, q*, q_l*, q_0, q_1) is
  stated and proved here.  All rationals are kept cross-multiplied; only
  `omega` / `grind` / `decide` are used (no Mathlib).
-/

set_option linter.unusedVariables false

namespace Gogoi

/-! ## 1. Parameters -/

def r (K : Nat) : Nat := K / 2
def eps (K : Nat) : Nat := K % 2
def s (K k : Nat) : Nat := K / 2 + 1 + K % 2 - k
def t (K k : Nat) : Nat := K - k

/-! ## 2. Bookkeeping (Remark 1) and the two forms of `q*` -/

theorem K_eq (K : Nat) : K / 2 + K / 2 + K % 2 = K := by omega

theorem t_eq (K k : Nat) (hk : k ≤ K / 2) : t K k = r K + s K k - 1 := by
  show K - k = K / 2 + (K / 2 + 1 + K % 2 - k) - 1
  omega

/-- **(2.1)** `2 * (2t - s) = 3K - 2k - 2 - eps`: the two displayed forms of `q*` agree. -/
theorem qstar_numerator (K k : Nat) (hk : k ≤ K / 2) :
    2 * (2 * t K k - s K k) = 3 * K - 2 * k - 2 - eps K := by
  show 2 * (2 * (K - k) - (K / 2 + 1 + K % 2 - k)) = 3 * K - 2 * k - 2 - K % 2
  omega

theorem one_le_s (K k : Nat) (hk : k ≤ K / 2) : 1 ≤ s K k := by
  show 1 ≤ K / 2 + 1 + K % 2 - k; omega

theorem s_le_t (K k : Nat) (hK : 3 ≤ K) (hk : k ≤ K / 2) (hk1 : 1 ≤ k) :
    s K k ≤ t K k := by
  show K / 2 + 1 + K % 2 - k ≤ K - k; omega

theorem two_le_s_of_odd (K k : Nat) (he : K % 2 = 1) (hk : k ≤ K / 2) :
    2 ≤ s K k := by
  show 2 ≤ K / 2 + 1 + K % 2 - k; omega

theorem s_lt_t (K k : Nat) (hK : 4 ≤ K) (hk : k ≤ K / 2) : s K k < t K k := by
  show K / 2 + 1 + K % 2 - k < K - k; omega

theorem half_lt_qstar (K k : Nat) (hK : 4 ≤ K) (hk : k ≤ K / 2) :
    t K k < 2 * t K k - s K k := by
  have h := s_lt_t K k hK hk; omega

theorem qstar_lt_one (K k : Nat) (hK : 2 ≤ K) (hk : k ≤ K / 2) :
    2 * t K k - s K k < 2 * t K k := by
  have h := one_le_s K k hk
  have ht : 0 < K - k := by omega
  show 2 * (K - k) - (K / 2 + 1 + K % 2 - k) < 2 * (K - k)
  omega

theorem K3_k1 : (s 3 1, t 3 1) = (2, 2) := by decide

/-! ## 3. The numerator `2 * M_{eps,s}(l)` -/

/-- The odd boundary regime `eps = 1, s = 1`, i.e. `k = r + 1` with `K` odd. -/
def bd (K k : Nat) : Prop := eps K = 1 ∧ s K k = 1

instance decBd (K k : Nat) : Decidable (bd K k) := by
  unfold bd eps s; infer_instance

def MnumEven (K k m : Nat) : Nat :=
  if bd K k then 2 * m * m else 2 * m * (s K k - 1 + m)

def MnumOdd (K k m : Nat) : Nat :=
  if bd K k then 2 * m * (m + 1) else 2 * m * (m + s K k) + s K k

/-- `2 * M_{eps,s}(l)`; `M` itself may be a half-integer. -/
def Mnum (K k l : Nat) : Nat :=
  if l % 2 = 0 then MnumEven K k (l / 2) else MnumOdd K k (l / 2)

theorem Mnum_even (K k m : Nat) : Mnum K k (2 * m) = MnumEven K k m := by
  have hdiv : (2 * m) / 2 = m := by omega
  have hmod : (2 * m) % 2 = 0 := by omega
  unfold Mnum; rw [if_pos hmod, hdiv]

theorem Mnum_odd (K k m : Nat) : Mnum K k (2 * m + 1) = MnumOdd K k m := by
  have hdiv : (2 * m + 1) / 2 = m := by omega
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  unfold Mnum; rw [if_neg (by omega), hdiv]

theorem MnumEven_reg (K k m : Nat) (h : ¬ bd K k) :
    MnumEven K k m = 2 * m * (s K k - 1 + m) := by
  unfold MnumEven; rw [if_neg h]

theorem MnumOdd_reg (K k m : Nat) (h : ¬ bd K k) :
    MnumOdd K k m = 2 * m * (m + s K k) + s K k := by
  unfold MnumOdd; rw [if_neg h]

theorem MnumEven_bd (K k m : Nat) (h : bd K k) : MnumEven K k m = 2 * m * m := by
  unfold MnumEven; rw [if_pos h]

theorem MnumOdd_bd (K k m : Nat) (h : bd K k) : MnumOdd K k m = 2 * m * (m + 1) := by
  unfold MnumOdd; rw [if_pos h]

theorem Mnum_one_reg (K k : Nat) (h : ¬ bd K k) : Mnum K k 1 = s K k := by
  rw [show (1 : Nat) = 2 * 0 + 1 from rfl, Mnum_odd K k 0, MnumOdd_reg K k 0 h]
  simp

/-- At the odd boundary `M_{1,1}(1) = 0` (this is Corollary 2). -/
theorem Mnum_one_bd (K k : Nat) (h : bd K k) : Mnum K k 1 = 0 := by
  rw [show (1 : Nat) = 2 * 0 + 1 from rfl, Mnum_odd K k 0, MnumOdd_bd K k 0 h]

theorem Mnum_two (K k : Nat) (hk : k ≤ K / 2) : Mnum K k 2 = 2 * s K k := by
  have hs : 1 ≤ s K k := one_le_s K k hk
  rw [show (2 : Nat) = 2 * 1 from rfl, Mnum_even K k 1]
  by_cases h : bd K k
  · have hs1 : s K k = 1 := h.2
    rw [MnumEven_bd K k 1 h, hs1]
  · rw [MnumEven_reg K k 1 h]; omega

/-- **Corollary 1(a)**: `q_1^* = q^*` on the non-degenerate range. -/
theorem q1_num (K k : Nat) (hk : k ≤ K / 2) (h : ¬ bd K k) :
    2 * 1 * t K k - Mnum K k 1 = 2 * t K k - s K k := by
  rw [Mnum_one_reg K k h]

/-- **Corollary 1(a)**: `q_2^* = q^*`. -/
theorem q2_num (K k : Nat) (hk : k ≤ K / 2) :
    2 * 2 * t K k - Mnum K k 2 = 2 * (2 * t K k - s K k) := by
  rw [Mnum_two K k hk]; omega

/-! ## 4. The floor evaluations and Corollary 1(b) -/

theorem div4_sq_odd (n : Nat) : (2 * n + 1) * (2 * n + 1) / 4 = n * n + n := by
  have h : (2 * n + 1) * (2 * n + 1) = 4 * (n * n + n) + 1 := by grind
  rw [h]; omega

theorem div4_sq_even (n : Nat) : (2 * n) * (2 * n) / 4 = n * n := by
  have h : (2 * n) * (2 * n) = 4 * (n * n) := by grind
  rw [h]; omega

theorem div4_sq_pred (n : Nat) (hn : 1 ≤ n) : (2 * n - 1) * (2 * n - 1) / 4 = n * n - n := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  have h1 : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  rw [h1, div4_sq_odd t]
  show t * t + t = (t + 1) * (t + 1) - (t + 1)
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem even_key (n S : Nat) (hS : 1 ≤ S) (hn : 1 ≤ n) :
    2 * n * (S - 1 + n) = 2 * n * S + 2 * (n * n - n) := by
  have e1 : S - 1 + n = S + (n - 1) := by omega
  rw [e1, Nat.mul_add]
  have e2 : 2 * n * (n - 1) = 2 * (n * n - n) := by
    rw [Nat.mul_assoc, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [e2]

theorem odd_key (n S : Nat) :
    2 * n * (n + S) + S = (2 * n + 1) * S + 2 * (n * n) := by grind

/-- **(Corollary 1(b))**, subtraction-free form, in the non-degenerate regime
`eps = 0` or `s >= 2` (i.e. `2 <= k <= r`):
`2M_{eps,s}(l) = l s + 2 floor((l-1)^2/4)`.
Remark: for odd `l` this identity *fails* at the odd boundary `eps = 1, s = 1`
(there `2M - l s = 2m^2 - 1` while `2 floor((l-1)^2/4) = 2m^2`); the paper only
uses it under the hypotheses of Corollary 1, where the regime is non-degenerate. -/
theorem Mnum_identity_reg (K k l : Nat) (h : ¬ bd K k) (hk : k ≤ K / 2) (hl : 1 ≤ l) :
    Mnum K k l = l * s K k + 2 * ((l - 1) * (l - 1) / 4) := by
  have hs : 1 ≤ s K k := one_le_s K k hk
  have hpar : l % 2 = 0 ∨ l % 2 = 1 := by omega
  rcases hpar with hp | hp
  · have hl2 : l = 2 * (l / 2) := by omega
    rw [hl2, Mnum_even, MnumEven_reg K k (l / 2) h, div4_sq_pred (l / 2) (by omega)]
    exact even_key (l / 2) (s K k) hs (by omega)
  · have hl2 : l = 2 * (l / 2) + 1 := by omega
    rw [hl2, Mnum_odd, MnumOdd_reg K k (l / 2) h]
    have e : 2 * (l / 2) + 1 - 1 = 2 * (l / 2) := by omega
    have h4 : (2 * (l / 2) + 1 - 1) * (2 * (l / 2) + 1 - 1) / 4 = (l / 2) * (l / 2) := by
      rw [e, div4_sq_even]
    rw [h4]
    exact odd_key (l / 2) (s K k)

/-! ## 5. `M_{eps,s}(l) ≤ l t / 2`, i.e. `q_l^* ≥ 1/2` -/

theorem Mnum_le (K k l : Nat) (hK : 3 ≤ K) (hk : k ≤ K / 2) (hl : 1 ≤ l)
    (hlk : l ≤ k) : Mnum K k l ≤ l * t K k := by
  have hpar : l % 2 = 0 ∨ l % 2 = 1 := by omega
  by_cases hbd : bd K k
  · obtain ⟨he, hs⟩ := hbd
    have he' : K % 2 = 1 := he
    have hs' : K / 2 + 1 + K % 2 - k = 1 := hs
    have hkr : k = K / 2 + 1 := by omega
    have ht : t K k = K / 2 := by show K - k = K / 2; omega
    rw [ht]
    rcases hpar with hp | hp
    · have hl2 : l = 2 * (l / 2) := by omega
      rw [hl2, Mnum_even, MnumEven_bd K k (l / 2) ⟨he, hs⟩]
      have hK2 : l ≤ K := Nat.le_trans (Nat.le_trans hlk hk) (Nat.div_le_self K 2)
      have h2 : l / 2 ≤ K / 2 := Nat.div_le_div_right hK2
      exact Nat.mul_le_mul_left _ h2
    · have hl2 : l = 2 * (l / 2) + 1 := by omega
      rw [hl2, Mnum_odd, MnumOdd_bd K k (l / 2) ⟨he, hs⟩]
      have hr2 : 2 * (l / 2) ≤ K / 2 := by
        have h : 2 * (l / 2) + 1 ≤ K / 2 + 1 := by omega
        omega
      have hmono : (2 * (l / 2) + 1) * (2 * (l / 2)) ≤ (2 * (l / 2) + 1) * (K / 2) :=
        Nat.mul_le_mul_left _ hr2
      have hpoly : 2 * (l / 2) * (l / 2 + 1) ≤ (2 * (l / 2) + 1) * (2 * (l / 2)) := by grind
      omega
  · rcases hpar with hp | hp
    · have hl2 : l = 2 * (l / 2) := by omega
      rw [hl2, Mnum_even, MnumEven_reg K k (l / 2) hbd]
      have ht : t K k = r K + s K k - 1 := t_eq K k hk
      have h1 : s K k - 1 + l / 2 ≤ t K k := by rw [ht]; unfold r; omega
      exact Nat.mul_le_mul_left _ h1
    · have hl2 : l = 2 * (l / 2) + 1 := by omega
      rw [hl2, Mnum_odd, MnumOdd_reg K k (l / 2) hbd]
      have ht : t K k = r K + s K k - 1 := t_eq K k hk
      have hr : 2 * (l / 2) + 1 ≤ r K := by unfold r; omega
      have hts : 2 * (l / 2) + s K k ≤ t K k := by rw [ht]; omega
      have hmono : (2 * (l / 2) + 1) * (2 * (l / 2) + s K k) ≤ (2 * (l / 2) + 1) * t K k :=
        Nat.mul_le_mul_left _ hts
      have hpoly : 2 * (l / 2) * (l / 2 + s K k) + s K k
          ≤ (2 * (l / 2) + 1) * (2 * (l / 2) + s K k) := by grind
      omega

/-! ## 6. Comparison with Diss-Mahajne's `q_0`, `q_1` -/

/-- `q_0 = (3K-2k-2)/(4t)`; `q* = q_0` iff `K` is even. -/
theorem qstar_eq_q0_even (K k : Nat) (hk : k ≤ K / 2) (he : eps K = 0) :
    2 * (2 * (K - k) - (K / 2 + 1 + K % 2 - k)) = 3 * K - 2 * k - 2 := by
  have he' : K % 2 = 0 := he
  omega

/-- For odd `K` and `k ≤ r`, `q* = q_0 - 1/(4t)`. -/
theorem qstar_eq_q0_odd (K k : Nat) (hk : k ≤ K / 2) (he : eps K = 1) :
    2 * (2 * (K - k) - (K / 2 + 1 + K % 2 - k)) + 1 = 3 * K - 2 * k - 2 := by
  have he' : K % 2 = 1 := he
  omega

/-- The footnote of Diss-Mahajne: `q_0 < 1` iff `k < (K+2)/2`. -/
theorem q0_lt_one (K k : Nat) (hK : 3 ≤ K) (hk : k ≤ K / 2) :
    3 * K - 2 * k - 2 < 4 * (K - k) ↔ 2 * k < K + 2 := by
  omega

/-- `q_1 - q_0 = (k-1)(1-q_0)/k ≥ 0`, cross-multiplied. -/
theorem q1_ge_q0 (K k : Nat) (hK : 3 ≤ K) (hk : k ≤ K / 2)
    (hq : 3 * K - 2 * k - 2 ≤ 4 * (K - k)) :
    0 ≤ (k - 1) * (4 * (K - k) - (3 * K - 2 * k - 2)) := by
  have h1 : 0 ≤ 4 * (K - k) - (3 * K - 2 * k - 2) := by omega
  exact Nat.zero_le _

/-! ## 7. The odd boundary (Corollary 2) -/

/-- At the odd boundary, `k < 2 M_{1,1}(k)` for `k ≥ 2`, hence `q_k^* < q_0`. -/
theorem bd_Mnum_gt (K k : Nat) (h : bd K k) (hk2 : 2 ≤ k) :
    k < 2 * Mnum K k k := by
  have hpar : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hpar with hp | hp
  · have hk : k = 2 * (k / 2) := by omega
    have h' : bd K (2 * (k / 2)) := by rw [← hk]; exact h
    have hn : 1 ≤ k / 2 := by omega
    have hmul : k / 2 ≤ (k / 2) * (k / 2) := Nat.le_mul_self _
    rw [hk, Mnum_even, MnumEven_bd K (2 * (k / 2)) (k / 2) h']
    have e : 2 * (2 * (k / 2) * (k / 2)) = 4 * ((k / 2) * (k / 2)) := by grind
    rw [e]; omega
  · have hk : k = 2 * (k / 2) + 1 := by omega
    have h' : bd K (2 * (k / 2) + 1) := by rw [← hk]; exact h
    have hn : 1 ≤ k / 2 := by omega
    have hmul : 2 * (k / 2) ≤ (k / 2) * (k / 2 + 1) := by
      have : (k / 2) * 2 ≤ (k / 2) * (k / 2 + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [hk, Mnum_odd, MnumOdd_bd K (2 * (k / 2) + 1) (k / 2) h']
    have e : 2 * (2 * (k / 2) * (k / 2 + 1)) = 4 * ((k / 2) * (k / 2 + 1)) := by grind
    rw [e]; omega

/-- At the odd boundary `2 M_{1,1}(2) = 2` while `2 * 2 * t = 4t`, so `q_2^* < 1`. -/
theorem bd_Mnum_two (K k : Nat) (h : bd K k) : Mnum K k 2 = 2 := by
  rw [show (2 : Nat) = 2 * 1 from rfl, Mnum_even, MnumEven_bd K k 1 h]

/-! ## 8. Numerical values of Example 1 (`K = 5, k = 3`) -/

example : Mnum 5 3 1 = 0 := by decide
example : Mnum 5 3 2 = 2 := by decide
example : Mnum 5 3 3 = 4 := by decide
-- q_1^* = 1, q_2^* = 1 - 2/4 = 3/4, q_3^* = 1 - 4/12 = 2/3
example : 2 * 1 * t 5 3 - Mnum 5 3 1 = 2 * (1 * t 5 3) := by decide
example : (2 * 2 * t 5 3 - Mnum 5 3 2) * 4 = 3 * (2 * 2 * t 5 3) := by decide
example : (2 * 3 * t 5 3 - Mnum 5 3 3) * 3 = 2 * (2 * 3 * t 5 3) := by decide

end Gogoi
