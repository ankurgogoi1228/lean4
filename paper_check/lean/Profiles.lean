/-
  Machine verification, inside Lean, of the *explicit profiles* used in the paper:
    Example 2, Theorem 4(a) (sharpness), Theorem 4(b), and the K = 4, k = 2
    profile quoted from Diss-Mahajne in Section 7.2.

  A profile is a `List (Nat × Nat × Nat)` : a ballot encoded as `(r0, r1, r2, ...)`
  is awkward, so we use `List (List Nat × Nat)`: ballot (in decreasing order of
  preference) together with an integer multiplicity.
-/

namespace GogoiProfiles

/-- 0-indexed rank of `a` in the ballot `b` (0 = most preferred). -/
def pos (b : List Nat) (a : Nat) : Nat :=
  match b with
  | [] => 0
  | x :: xs => if x = a then 0 else 1 + pos xs a

/-- `sumF P f g` adds `g p` over the profile `P`, where `f p` receives the ballot
and the multiplicity.  (Written by hand so that no compiled list combinators are
needed.) -/
def sumF (P : List (List Nat × Nat)) (g : List Nat → Nat → Nat) : Nat :=
  match P with
  | [] => 0
  | p :: ps => g p.1 p.2 + sumF ps g

def total (P : List (List Nat × Nat)) : Nat := sumF P (fun _ m => m)

/-- `n_{ab}` : number of voters ranking `a` strictly above `b`. -/
def nab (P : List (List Nat × Nat)) (a b : Nat) : Nat :=
  sumF P (fun bal m => if pos bal a < pos bal b then m else 0)

/-- `A_a` : voters ranking `a` above the line. -/
def aboveC (K : Nat) (P : List (List Nat × Nat)) (a : Nat) : Nat :=
  sumF P (fun bal m => if pos bal a < K / 2 then m else 0)

/-- `B_a` : voters ranking `a` below the line. -/
def belowC (K : Nat) (P : List (List Nat × Nat)) (a : Nat) : Nat :=
  sumF P (fun bal m => if K / 2 + K % 2 ≤ pos bal a then m else 0)

/-! ## Example 2 : K = 5, k = 3, n = 26, q = 24/25 -/

def ex2 : List (List Nat × Nat) :=
  [([1, 2, 3, 0, 4], 1), ([1, 2, 0, 3, 4], 25)]

example : total ex2 = 26 := by decide
/-- strict `24/25`-Condorcet: `n_{ab} > (24/25) n` for all `a ∈ C`, `b ∈ D`. -/
example : 25 * nab ex2 0 3 > 24 * total ex2 := by decide
example : 25 * nab ex2 0 4 > 24 * total ex2 := by decide
example : 25 * nab ex2 1 3 > 24 * total ex2 := by decide
example : 25 * nab ex2 1 4 > 24 * total ex2 := by decide
example : 25 * nab ex2 2 3 > 24 * total ex2 := by decide
example : 25 * nab ex2 2 4 > 24 * total ex2 := by decide
/-- `a_1 = 0` is unacceptable; the other members are acceptable. -/
example : belowC 5 ex2 0 > aboveC 5 ex2 0 := by decide
example : belowC 5 ex2 1 ≤ aboveC 5 ex2 1 := by decide
example : belowC 5 ex2 2 ≤ aboveC 5 ex2 2 := by decide
/-- the margins themselves -/
example : nab ex2 0 3 = 25 := by decide
example : nab ex2 0 4 = 26 := by decide
/-- `24/25 > 23/24` : the quota really exceeds Diss-Mahajne's `q_1`. -/
example : 24 * 24 > 23 * 25 := by decide

/-! ## Theorem 4(a) : K = 5, k = 3, n = 101, q = 99/100 -/

def t4a : List (List Nat × Nat) :=
  [([1, 2, 3, 0, 4], 1), ([1, 2, 0, 3, 4], 100)]

example : 100 * nab t4a 0 3 > 99 * total t4a := by decide
example : 100 * nab t4a 0 4 > 99 * total t4a := by decide
example : 100 * nab t4a 1 3 > 99 * total t4a := by decide
example : 100 * nab t4a 1 4 > 99 * total t4a := by decide
example : 100 * nab t4a 2 3 > 99 * total t4a := by decide
example : 100 * nab t4a 2 4 > 99 * total t4a := by decide
example : belowC 5 t4a 0 > aboveC 5 t4a 0 := by decide
example : aboveC 5 t4a 0 = 0 := by decide

/-! ## Theorem 4(b) : `k > ceil(K/2)` (weak unanimity, yet unacceptable) -/

def t4b5 : List (List Nat × Nat) := [([1, 2, 3, 0, 4], 3)]
example : nab t4b5 0 4 = total t4b5 := by decide
example : nab t4b5 3 4 = total t4b5 := by decide
example : belowC 5 t4b5 0 > aboveC 5 t4b5 0 := by decide

def t4b6 : List (List Nat × Nat) := [([1, 2, 3, 0, 4, 5], 3)]
example : nab t4b6 0 5 = total t4b6 := by decide
example : nab t4b6 3 5 = total t4b6 := by decide
example : belowC 6 t4b6 0 > aboveC 6 t4b6 0 := by decide

/-! ## Section 7.2 : the `K = 4, k = 2` profile quoted from Diss-Mahajne -/

def dm (m : Nat) : List (List Nat × Nat) :=
  [([0, 3, 1, 2], 3 * m), ([0, 2, 1, 3], 3 * m), ([1, 2, 0, 3], 3 * m),
   ([1, 3, 0, 2], 3 * m), ([2, 3, 0, 1], 1)]

/-- It *is* completely unacceptable. -/
example : belowC 4 (dm 1) 0 > aboveC 4 (dm 1) 0 := by decide
example : belowC 4 (dm 1) 1 > aboveC 4 (dm 1) 1 := by decide

/-- **But it is not weak `3/4`-Condorcet.**  For `m = 1, 2, 3, 10` the margin
`n_{ac} = 9m` violates `4 n_{ac} ≥ 3 n`. -/
example : 4 * nab (dm 1) 0 2 < 3 * total (dm 1) := by decide
example : 4 * nab (dm 2) 0 2 < 3 * total (dm 2) := by decide
example : 4 * nab (dm 3) 0 2 < 3 * total (dm 3) := by decide
example : 4 * nab (dm 10) 0 2 < 3 * total (dm 10) := by decide
example : 4 * nab (dm 10) 0 3 < 3 * total (dm 10) := by decide
example : 4 * nab (dm 10) 1 2 < 3 * total (dm 10) := by decide
example : 4 * nab (dm 10) 1 3 < 3 * total (dm 10) := by decide
/-- all four margins are `9m`, so the profile is `q`-Condorcet only for
`q ≤ 9m/(12m+1) < 3/4`. -/
example : nab (dm 10) 0 2 = 90 := by decide
example : nab (dm 10) 0 3 = 90 := by decide
example : nab (dm 10) 1 2 = 90 := by decide
example : nab (dm 10) 1 3 = 90 := by decide
example : total (dm 10) = 121 := by decide

end GogoiProfiles
