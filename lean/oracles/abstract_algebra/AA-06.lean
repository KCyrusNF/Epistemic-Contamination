import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/abstract_algebra/AA-06.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AA-06 — Identity exists only on left
Source: test case definition test_cases/abstract_algebra/AA-06.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AA_06
open Benchmark

def e : Nat := 5
structure Standard where
  op : Nat → Nat → Nat
  left : ∀ x, op e x = x
  right : ∀ x, op x e = x
structure Model where
  op : Nat → Nat → Nat
  left : ∀ x, op e x = x
  h0 : op 0 e = 0
  h2 : op 2 e = 0
  h3 : op 3 e = 0
def N (op : Nat → Nat → Nat) (x : Nat) := op e (op x e)
def completion (k : Nat) : Model where
  op := fun x y => if x = e then y else if y = e ∧ (x = 0 ∨ x = 2 ∨ x = 3) then 0 else k
  left := by intro x; simp
  h0 := by simp [e]
  h2 := by simp [e]
  h3 := by simp [e]

end AA_06

open AA_06 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In the standard system, $$e$$ is a two-sided identity for $$\ast$$. If $$x=2$$, does $$e\ast x=x\ast e=x$$ hold?
JSON expected answer: Yes.
-/
theorem aa_06_turn_01_oracle (s : Standard) : s.op e 2 = 2 ∧ s.op 2 e = 2 := by
  simp [N, s.left, s.right]

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system, define $$N(x)=e\ast(x\ast e)$$ for every element. What is $$N(N(2))$$?
JSON expected answer: 2
-/
theorem aa_06_turn_02_oracle (s : Standard) : N s.op (N s.op 2) = 2 := by
  simp [N, s.left, s.right]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now consider a set containing distinct elements $$e,0,2,3,4$$ with a total operation $$\ast$$ satisfying $$e\ast x=x$$ for every element, $$0\ast e=0$$, and $$2\ast e=3\ast e=0$$. No other products are fixed. What is $$2\ast e$$?
JSON expected answer: 0
-/
theorem aa_06_turn_03_oracle (m : Model) : m.op 2 e = 0 := by
  exact m.h2

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$2\ast e=2$$ hold?
JSON expected answer: No.
-/
theorem aa_06_turn_04_oracle (m : Model) : m.op 2 e ≠ 2 := by
  simp only [N, m.left, m.h0, m.h2, m.h3] <;> decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, what is $$e\ast(3\ast e)$$?
JSON expected answer: 0
-/
theorem aa_06_turn_05_oracle (m : Model) : m.op e (m.op 3 e) = 0 := by
  simp only [N, m.left, m.h0, m.h2, m.h3] <;> decide

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$N(x)=e\ast(x\ast e)$$ for every element. What is $$N(0)$$?
JSON expected answer: 0
-/
theorem aa_06_turn_06_oracle (m : Model) : N m.op 0 = 0 := by
  simp only [N, m.left, m.h0, m.h2, m.h3] <;> decide

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$N(3)$$?
JSON expected answer: 0
-/
theorem aa_06_turn_07_oracle (m : Model) : N m.op 3 = 0 := by
  simp only [N, m.left, m.h0, m.h2, m.h3] <;> decide

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$N(N(2))$$?
JSON expected answer: 0
-/
theorem aa_06_turn_08_oracle (m : Model) : N m.op (N m.op 2) = 0 := by
  simp only [N, m.left, m.h0, m.h2, m.h3] <;> decide

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$N(4)$$?
JSON expected answer: cannot be determined
-/
theorem aa_06_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => N m.op 4) := by
  exact ⟨completion 0, completion 1, True.intro, True.intro, by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$inverse_{\ast}(2)$$?
JSON expected answer: cannot be determined
-/
theorem aa_06_turn_10_oracle : Underdetermined (fun _ : Model × (Nat → Nat) => True) (fun m => m.2 2) := by
  exact ⟨(completion 0, fun _ => 0), (completion 0, fun _ => 1), True.intro, True.intro, by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is $$e$$ guaranteed to be an identity on both sides?
JSON expected answer: No.
-/
theorem aa_06_turn_11_oracle (m : Model) : ¬ (∀ x, m.op x e = x) := by
  intro h
  have bad := h 2
  rw [m.h2] at bad
  contradiction

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement $$2\ast e=2$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem aa_06_turn_12_oracle (s : Standard) (m : Model) : s.op 2 e = 2 ∧ m.op 2 e ≠ 2 := by
  constructor
  · exact s.right 2
  · simp only [N, m.left, m.h0, m.h2, m.h3] <;> decide

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$2\ast e$$ in the standard system, and what is it in the modified system?
JSON expected answer: 2 in the standard system and 0 in the modified system.
-/
theorem aa_06_turn_13_oracle (s : Standard) (m : Model) : parallel (s.op 2 e) (m.op 2 e) = (2,0) := by
  rw [s.right, m.h2]
  rfl

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard system. What is $$2\ast e$$?
JSON expected answer: 2
-/
theorem aa_06_turn_14_oracle (s : Standard) : s.op 2 e = 2 := by
  exact s.right 2

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, what is $$N(N(2))$$?
JSON expected answer: 2
-/
theorem aa_06_turn_15_oracle (s : Standard) : N s.op (N s.op 2) = 2 := by
  simp [N, s.left, s.right]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$2\ast e$$?
JSON expected answer: 0
-/
theorem aa_06_turn_16_oracle (m : Model) : m.op 2 e = 0 := by
  exact m.h2
