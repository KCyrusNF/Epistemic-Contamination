import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/abstract_algebra/AA-41.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AA-41 — Zero not absorbing
Source: test case definition test_cases/abstract_algebra/AA-41.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AA_41
open Benchmark

-- Natural labels 0,1,2 denote the distinct symbols 0,u,v.
structure Standard where
  op : Nat → Nat → Nat
  zero : ∀ x, op 0 x = 0
structure Model where
  op : Nat → Nat → Nat
  h0 : op 0 0 = 0
  hu : op 0 1 = 1
def Z (op : Nat → Nat → Nat) (x : Nat) := op 0 x
def completion (k : Nat) : Model where
  op := fun x y => if x=0 ∧ y=0 then 0 else if x=0 ∧ y=1 then 1 else k
  h0 := by norm_num
  hu := by norm_num

end AA_41

open AA_41 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In the standard system, zero is absorbing for multiplication. Does $$0\cdot x=0$$ hold for every $$x$$?
JSON expected answer: Yes.
-/
theorem aa_41_turn_01_oracle (s : Standard) (x : Nat) : s.op 0 x = 0 := by
  simp only [Z, s.zero]

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system, define $$Z(x)=0\cdot x$$. What is $$Z(2)$$?
JSON expected answer: 0
-/
theorem aa_41_turn_02_oracle (s : Standard) : Z s.op 2 = 0 := by
  simp only [Z, s.zero]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now consider a carrier with distinct elements $$0,u,v$$ and total multiplication satisfying $$0\cdot u=u$$ and $$0\cdot0=0$$; other products are unconstrained. What is $$0\cdot u$$?
JSON expected answer: u
-/
theorem aa_41_turn_03_oracle (m : Model) : m.op 0 1 = 1 := by
  simp only [Z, m.h0, m.hu] <;> decide

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$0\cdot u=0$$ hold?
JSON expected answer: No.
-/
theorem aa_41_turn_04_oracle (m : Model) : m.op 0 1 ≠ 0 := by
  simp only [Z, m.h0, m.hu] <;> decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, what is $$0\cdot(0\cdot u)$$?
JSON expected answer: u
-/
theorem aa_41_turn_05_oracle (m : Model) : m.op 0 (m.op 0 1) = 1 := by
  simp only [Z, m.h0, m.hu] <;> decide

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In this modified system, use the same derived rule $$Z(x)=0\cdot x$$. What is $$Z(0)$$?
JSON expected answer: 0
-/
theorem aa_41_turn_06_oracle (m : Model) : Z m.op 0 = 0 := by
  simp only [Z, m.h0, m.hu] <;> decide

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$Z(u)$$?
JSON expected answer: u
-/
theorem aa_41_turn_07_oracle (m : Model) : Z m.op 1 = 1 := by
  simp only [Z, m.h0, m.hu] <;> decide

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$Z(Z(u))$$?
JSON expected answer: u
-/
theorem aa_41_turn_08_oracle (m : Model) : Z m.op (Z m.op 1) = 1 := by
  simp only [Z, m.h0, m.hu] <;> decide

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$Z(v)$$?
JSON expected answer: cannot be determined
-/
theorem aa_41_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => Z m.op 2) := by
  exact ⟨completion 0, completion 1, True.intro, True.intro, by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$u^{-1}$$?
JSON expected answer: cannot be determined
-/
theorem aa_41_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0, 0), (completion 0, 1), True.intro, True.intro, by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is zero absorbing for every element?
JSON expected answer: No.
-/
theorem aa_41_turn_11_oracle (m : Model) : ¬ (∀ x, m.op 0 x = 0) := by
  intro h
  have bad := h 1
  rw [m.hu] at bad
  contradiction

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement $$0\cdot u=0$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem aa_41_turn_12_oracle (s : Standard) (m : Model) : s.op 0 1 = 0 ∧ m.op 0 1 ≠ 0 := by
  constructor
  · exact s.zero 1
  · simp only [Z, m.h0, m.hu] <;> decide

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$0\cdot u$$ in the standard system, and what is it in the modified system?
JSON expected answer: 0 in the standard system and u in the modified system.
-/
theorem aa_41_turn_13_oracle (s : Standard) (m : Model) : parallel (s.op 0 1) (m.op 0 1) = (0,1) := by
  simp [parallel, s.zero, m.hu]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard system. What is $$0\cdot u$$?
JSON expected answer: 0
-/
theorem aa_41_turn_14_oracle (s : Standard) : s.op 0 1 = 0 := by
  simp only [Z, s.zero]

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, what is $$Z(u)$$?
JSON expected answer: 0
-/
theorem aa_41_turn_15_oracle (s : Standard) : Z s.op 1 = 0 := by
  simp only [Z, s.zero]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$0\cdot u$$?
JSON expected answer: u
-/
theorem aa_41_turn_16_oracle (m : Model) : m.op 0 1 = 1 := by
  simp only [Z, m.h0, m.hu] <;> decide
