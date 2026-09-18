import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/abstract_algebra/AA-11.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AA-11 — Inverse works only one side
Source: test case definition test_cases/abstract_algebra/AA-11.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AA_11
open Benchmark

/-- Modular addition uses the actual five-element carrier. -/
def standardAdd (x y : Fin 5) : Fin 5 := x+y
abbrev I (op : Fin 5 → Fin 5 → Fin 5) (x y : Fin 5) := op x y = 0 ∧ op y x = 0
abbrev J (op : Fin 5 → Fin 5 → Fin 5) (x y z : Fin 5) := I op x y ∧ I op y z
structure Model where
  op : Fin 5 → Fin 5 → Fin 5
  left : ∀ x, op 0 x = x
  right : ∀ x, op x 0 = x
  h23 : op 2 3 = 0
  h32 : op 3 2 = 1
def completion (k : Fin 5) : Model where
  op := fun x y => if x=0 then y else if y=0 then x else if x=2 ∧ y=3 then 0 else if x=3 ∧ y=2 then 1 else k
  left := by intro x; simp
  right := by intro x; by_cases h : x=0 <;> simp [h]
  h23 := by norm_num
  h32 := by norm_num

end AA_11

open AA_11 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In the standard group $$\mathbb{Z}_5$$ under addition, is $$3$$ a two-sided inverse of $$2$$?
JSON expected answer: Yes.
-/
theorem aa_11_turn_01_oracle : I standardAdd 2 3 := by
  decide

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard group, define $$I(x,y)\iff(x+y=0)\land(y+x=0)$$ and $$J(x,y,z)\iff I(x,y)\land I(y,z)$$. Does $$J(2,3,2)$$ hold?
JSON expected answer: Yes.
-/
theorem aa_11_turn_02_oracle : J standardAdd 2 3 2 := by
  decide

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now consider a total operation $$+$$ on $$\{0,1,2,3,4\}$$ with two-sided identity $$0$$ and $$2+3=0$$ but $$3+2=1$$. No other nonidentity products or group laws are imposed. A right inverse of $$x$$ is an element $$y$$ with $$x+y=0$$; a left inverse satisfies $$y+x=0$$. Is $$3$$ a left inverse of $$2$$?
JSON expected answer: No.
-/
theorem aa_11_turn_03_oracle (m : Model) : m.op 3 2 ≠ 0 := by
  simp only [I, J, m.left, m.right, m.h23, m.h32] <;> decide

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, is $$3$$ a two-sided inverse of $$2$$?
JSON expected answer: No.
-/
theorem aa_11_turn_04_oracle (m : Model) : ¬ I m.op 2 3 := by
  simp only [I, J, m.left, m.right, m.h23, m.h32] <;> decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$3+(2+3)=1$$ hold?
JSON expected answer: No.
-/
theorem aa_11_turn_05_oracle (m : Model) : m.op 3 (m.op 2 3) ≠ 1 := by
  simp only [I, J, m.left, m.right, m.h23, m.h32] <;> decide

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$I(x,y)\iff(x+y=0)\land(y+x=0)$$ and $$J(x,y,z)\iff I(x,y)\land I(y,z)$$. Does $$I(0,0)$$ hold?
JSON expected answer: Yes.
-/
theorem aa_11_turn_06_oracle (m : Model) : I m.op 0 0 := by
  simp only [I, J, m.left, m.right, m.h23, m.h32] <;> decide

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$I(2,3)$$ hold?
JSON expected answer: No.
-/
theorem aa_11_turn_07_oracle (m : Model) : ¬ I m.op 2 3 := by
  simp only [I, J, m.left, m.right, m.h23, m.h32] <;> decide

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$J(2,3,2)$$ hold?
JSON expected answer: No.
-/
theorem aa_11_turn_08_oracle (m : Model) : ¬ J m.op 2 3 2 := by
  simp only [I, J, m.left, m.right, m.h23, m.h32] <;> decide

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$I(2,4)$$ hold?
JSON expected answer: cannot be determined
-/
theorem aa_11_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => decide (I m.op 2 4)) := by
  exact ⟨completion 0, completion 1, True.intro, True.intro, by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$order(2)$$?
JSON expected answer: cannot be determined
-/
theorem aa_11_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0, 0), (completion 0, 1), True.intro, True.intro, by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In the modified system, does $$3$$ invert $$2$$ on the right while failing to invert it on the left?
JSON expected answer: Yes.
-/
theorem aa_11_turn_11_oracle (m : Model) : m.op 2 3 = 0 ∧ m.op 3 2 ≠ 0 := by
  simp only [I, J, m.left, m.right, m.h23, m.h32] <;> decide

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement “$$3$$ is a two-sided inverse of $$2$$” hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem aa_11_turn_12_oracle (m : Model) : I standardAdd 2 3 ∧ ¬ I m.op 2 3 := by
  constructor
  · decide
  · simp only [I, J, m.left, m.right, m.h23, m.h32] <;> decide

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is $$3$$ a two-sided inverse of $$2$$ in the standard system, and is it one in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem aa_11_turn_13_oracle (m : Model) : I standardAdd 2 3 ∧ ¬ I m.op 2 3 := by
  constructor
  · decide
  · simp only [I, J, m.left, m.right, m.h23, m.h32] <;> decide

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard system. Is $$3$$ a two-sided inverse of $$2$$?
JSON expected answer: Yes.
-/
theorem aa_11_turn_14_oracle : I standardAdd 2 3 := by
  decide

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard group, does $$J(2,3,2)$$ hold?
JSON expected answer: Yes.
-/
theorem aa_11_turn_15_oracle : J standardAdd 2 3 2 := by
  decide

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is $$3$$ a two-sided inverse of $$2$$?
JSON expected answer: No.
-/
theorem aa_11_turn_16_oracle (m : Model) : ¬ I m.op 2 3 := by
  simp only [I, J, m.left, m.right, m.h23, m.h32] <;> decide
