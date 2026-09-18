import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/abstract_algebra/AA-21.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AA-21 — successor(n) = n + 2
Source: test case definition test_cases/abstract_algebra/AA-21.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AA_21
open Benchmark

/-- Ordinary and modified successors are separate functions. -/
def standardSuccessor (n : Nat) := n + 1
def modifiedSuccessor (n : Nat) := n + 2
/-- The complete supplied multiplication constraints; no odd base value is fixed. -/
structure Model where
  mul : Nat → Nat → Nat
  zero : ∀ a, mul a 0 = 0
  step : ∀ a b, mul a (b+2) = mul a b + a
/-- A completion is determined by a freely chosen value on each odd chain. -/
def completionMul (seed : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | 1 => seed a
  | n+2 => completionMul seed a n + a

def completion (seed : Nat → Nat) : Model where
  mul := completionMul seed
  zero := by intro a; rfl
  step := by intro a b; rfl

end AA_21

open AA_21 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In ordinary arithmetic over the natural numbers, if $$successor(n)=n+1$$, what is $$successor(3)$$?
JSON expected answer: 4
-/
theorem aa_21_turn_01_oracle : standardSuccessor 3 = 4 := by
  rfl

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In ordinary arithmetic over the natural numbers, multiplication is defined recursively by $$a\times0=0$$ and $$a\times successor(b)=a\times b+a$$. What is $$2\times2$$?
JSON expected answer: 4
-/
theorem aa_21_turn_02_oracle : (2:Nat)*2 = 4 := by
  rfl

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now consider a modified arithmetic system over the natural numbers in which ordinary addition $$+$$ retains its usual meaning, but $$successor(n)=n+2$$. In this modified system, what is $$successor(3)$$?
JSON expected answer: 5
-/
theorem aa_21_turn_03_oracle : modifiedSuccessor 3 = 5 := by
  rfl

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, is $$successor(3)=4$$?
JSON expected answer: No.
-/
theorem aa_21_turn_04_oracle : modifiedSuccessor 3 ≠ 4 := by
  decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In this modified system, what is $$successor(successor(10))$$?
JSON expected answer: 14
-/
theorem aa_21_turn_05_oracle : modifiedSuccessor (modifiedSuccessor 10) = 14 := by
  rfl

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In this modified system, let multiplication $$\times:\mathbb N\times\mathbb N\to\mathbb N$$ satisfy $$a\times0=0$$ and $$a\times successor(b)=a\times b+a$$ for all natural numbers. These clauses are its only constraints. What is $$2\times0$$?
JSON expected answer: 0
-/
theorem aa_21_turn_06_oracle (m : Model) : m.mul 2 0 = 0 := by
  exact m.zero 2

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$2\times2$$?
JSON expected answer: 2
-/
theorem aa_21_turn_07_oracle (m : Model) : m.mul 2 2 = 2 := by
  rw [m.step 2 0, m.zero]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$3\times4$$?
JSON expected answer: 6
-/
theorem aa_21_turn_08_oracle (m : Model) : m.mul 3 4 = 6 := by
  rw [m.step 3 2, m.step 3 0, m.zero]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In this modified system, what is $$2\times3$$?
JSON expected answer: cannot be determined
-/
theorem aa_21_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => m.mul 2 3) := by
  exact ⟨completion (fun _ => 0), completion (fun _ => 1), True.intro, True.intro, by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$predecessor(7)$$?
JSON expected answer: cannot be determined
-/
theorem aa_21_turn_10_oracle : Underdetermined (fun _ : Model × (Nat → Nat) => True) (fun m => m.2 7) := by
  exact ⟨(completion (fun _ => 0), fun _ => 0), (completion (fun _ => 0), fun _ => 1), True.intro, True.intro, by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, does each application of $$successor$$ increase a number by $$1$$ or by $$2$$?
JSON expected answer: 2
-/
theorem aa_21_turn_11_oracle (n : Nat) : modifiedSuccessor n - n = 2 := by
  simp [modifiedSuccessor]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement $$successor(3)=5$$ hold in ordinary arithmetic, in the modified system, or in both?
JSON expected answer: Only in the modified system.
-/
theorem aa_21_turn_12_oracle : standardSuccessor 3 ≠ 5 ∧ modifiedSuccessor 3 = 5 := by
  decide

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$successor(4)$$ in ordinary arithmetic, and what is it in the modified system?
JSON expected answer: 5 in ordinary arithmetic and 6 in the modified system.
-/
theorem aa_21_turn_13_oracle : parallel (standardSuccessor 4) (modifiedSuccessor 4) = (5,6) := by
  rfl

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary arithmetic. What is $$successor(4)$$?
JSON expected answer: 5
-/
theorem aa_21_turn_14_oracle : standardSuccessor 4 = 5 := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary arithmetic, what is $$2\times2$$?
JSON expected answer: 4
-/
theorem aa_21_turn_15_oracle : (2:Nat)*2 = 4 := by
  rfl

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$successor(4)$$?
JSON expected answer: 6
-/
theorem aa_21_turn_16_oracle : modifiedSuccessor 4 = 6 := by
  rfl
