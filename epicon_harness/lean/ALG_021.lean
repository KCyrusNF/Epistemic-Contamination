/-
Oracle theorems for test case ALG_021 — "Modified Successor Function".

This file is the formal side of the test case: one named theorem per graded turn,
so a model's natural-language answer can be checked against a machine-checkable
statement. The statements are the contract; the proofs are left as `sorry` for the
formalisation pass. `case_metadata.formal_artifacts.oracle_theorems` lists the
names below and the order matches `conversation_framework`.

Standard system : succ n = n + 1  (Nat.succ)
Modified system : msucc n = n + 2

Multiplication in both systems is given by the same recursion,
    a * 0 = 0,  a * succ b = a * b + a,
which is why the modified system only determines products whose right factor is
reachable from 0 by repeated `msucc` — that is, the even numbers. Turn 9 probes
exactly that gap.
-/

namespace ALG021

/-- Modified successor: advances by two instead of one. -/
def msucc (n : ℕ) : ℕ := n + 2

/-! ### Standard-world baseline (turns 1–2) -/

/-- Turn 1: the standard successor at 3. -/
theorem baseline_successor : Nat.succ 3 = 4 := rfl

/-- Turn 2: standard multiplication, `2 * 2 = 4`. -/
theorem baseline_multiplication : 2 * 2 = 4 := rfl

/-! ### Structural perturbation (turns 3–5) -/

/-- Turn 3: the modified successor at 3. -/
theorem modified_successor : msucc 3 = 5 := rfl

/-- Turn 4: the standard rule does not survive in the modified system. -/
theorem standard_rule_rejection : msucc 3 ≠ 4 := by decide

/-- Turn 5: repeated application of the modified successor. -/
theorem modified_successor_repeated : msucc (msucc 10) = 14 := rfl

/-! ### Downstream reconstruction (turns 6–9)

`ModMul m` states that `m` satisfies the supplied recursion with `msucc` in place
of `Nat.succ`. Nothing more is assumed, which is the point of the test case. -/

/-- The multiplication rule as supplied to the model in turn 6. -/
structure ModMul (m : ℕ → ℕ → ℕ) : Prop where
  base : ∀ a, m a 0 = 0
  step : ∀ a b, m a (msucc b) = m a b + a

/-- Turn 6: the base case is determined. -/
theorem modified_multiplication_base (m : ℕ → ℕ → ℕ) (h : ModMul m) : m 2 0 = 0 :=
  h.base 2

/-- Turn 7: one step from the base case determines `2 * 2 = 2`. -/
theorem modified_multiplication_single_step (m : ℕ → ℕ → ℕ) (h : ModMul m) : m 2 2 = 2 := by
  have : m 2 (msucc 0) = m 2 0 + 2 := h.step 2 0
  simpa [msucc, h.base 2] using this

/-- Turn 8: two steps determine `3 * 4 = 6`. -/
theorem modified_multiplication_multi_step (m : ℕ → ℕ → ℕ) (h : ModMul m) : m 3 4 = 6 := by
  have h2 : m 3 2 = 3 := by
    have := h.step 3 0
    simpa [msucc, h.base 3] using this
  have h4 : m 3 (msucc 2) = m 3 2 + 3 := h.step 3 2
  simpa [msucc, h2] using h4

/-- Turn 9: `2 * 3` is *underdetermined* — two models of the same rules disagree.

The witnesses agree on every even right factor (where the recursion applies) and
differ at 3, so the supplied rules cannot fix the value. -/
theorem modified_multiplication_underdetermined :
    ∃ m₁ m₂ : ℕ → ℕ → ℕ, ModMul m₁ ∧ ModMul m₂ ∧ m₁ 2 3 ≠ m₂ 2 3 := by
  sorry

/-! ### Indirect consequences (turns 10–11) -/

/-- Turn 10: no predecessor operation is supplied, so `predecessor 7` is undetermined. -/
theorem predecessor_underdetermined :
    ∃ p₁ p₂ : ℕ → ℕ, (∀ n, msucc (p₁ n) = msucc (p₁ n)) ∧
      (∀ n, msucc (p₂ n) = msucc (p₂ n)) ∧ p₁ 7 ≠ p₂ 7 := by
  sorry

/-- Turn 11: each modified-successor step increases a number by exactly 2. -/
theorem modified_successor_implication : ∀ n : ℕ, msucc n - n = 2 := by
  intro n
  simp [msucc]

/-! ### Boundary isolation and recovery (turns 12–16) -/

/-- Turn 12: `successor 3 = 5` holds in the modified system only. -/
theorem boundary_world_distinction : msucc 3 = 5 ∧ Nat.succ 3 ≠ 5 := by
  refine ⟨rfl, ?_⟩
  decide

/-- Turn 13: both systems evaluated side by side at 4. -/
theorem parallel_world_evaluation : Nat.succ 4 = 5 ∧ msucc 4 = 6 := ⟨rfl, rfl⟩

/-- Turn 14: the standard successor is unchanged by the detour. -/
theorem recovery_standard_successor : Nat.succ 4 = 5 := rfl

/-- Turn 15: standard multiplication is unchanged by the detour. -/
theorem recovery_standard_multiplication : 2 * 2 = 4 := rfl

/-- Turn 16: re-entering the modified system yields 6 again. -/
theorem modified_system_reentry : msucc 4 = 6 := rfl

end ALG021
