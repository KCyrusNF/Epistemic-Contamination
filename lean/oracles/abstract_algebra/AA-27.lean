import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/abstract_algebra/AA-27.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AA-27 — a ⊞ successor(b) = successor(a ⊞ b) + 1
Source: test case definition test_cases/abstract_algebra/AA-27.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AA_27
open Benchmark

/-- The modified recursion doubles each step in the second argument. -/
def modifiedAdd : Nat → Nat → Nat
  | a, 0 => a
  | a, b+1 => modifiedAdd a b + 2
structure StandardH where
  H : Nat → Nat
  base : H 0 = 2
  step0 : H 1 = 2 + H 0
  step1 : H 2 = 2 + H 1
structure ModifiedH where
  H : Nat → Nat
  base : H 0 = 2
  step0 : H 1 = modifiedAdd 2 (H 0)
  step1 : H 2 = modifiedAdd 2 (H 1)
def completion (k : Nat) : ModifiedH where
  H := fun n => if n = 0 then 2 else if n = 1 then 6 else if n = 2 then 14 else k
  base := by norm_num [modifiedAdd]
  step0 := by norm_num [modifiedAdd]
  step1 := by norm_num [modifiedAdd]

end AA_27

open AA_27 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In ordinary arithmetic over $$\mathbb N$$, let $$successor(n)=n+1$$. Addition satisfies $$a+0=a$$ and $$a+successor(b)=successor(a+b)$$. What is $$2+2$$?
JSON expected answer: 4
-/
theorem aa_27_turn_01_oracle : (2:Nat)+2=4 := by
  rfl

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system, let $$H:\mathbb N\to\mathbb N$$ satisfy $$H(0)=2$$ and $$H(successor(n))=2+H(n)$$ for $$n\in\{0,1\}$$. What is $$H(2)$$?
JSON expected answer: 6
-/
theorem aa_27_turn_02_oracle (h : StandardH) : h.H 2 = 6 := by
  rw [h.step1, h.step0, h.base]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now modify addition on $$\mathbb N$$ by $$a+0=a$$ and $$a+successor(b)=successor(successor(a+b))$$ for every $$a,b$$. The successor function still advances by one ordinary natural-number step. What is $$2+1$$?
JSON expected answer: 4
-/
theorem aa_27_turn_03_oracle : modifiedAdd 2 1 = 4 := by
  rfl

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, is $$2+1=3$$?
JSON expected answer: No.
-/
theorem aa_27_turn_04_oracle : modifiedAdd 2 1 ≠ 3 := by
  decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, what is $$2+2$$?
JSON expected answer: 6
-/
theorem aa_27_turn_05_oracle : modifiedAdd 2 2 = 6 := by
  rfl

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct a total function $$H:\mathbb N\to\mathbb N$$ with only the constraints $$H(0)=2$$ and $$H(successor(n))=2+H(n)$$ for $$n\in\{0,1\}$$. What is $$H(0)$$?
JSON expected answer: 2
-/
theorem aa_27_turn_06_oracle (h : ModifiedH) : h.H 0 = 2 := by
  exact h.base

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$H(1)$$?
JSON expected answer: 6
-/
theorem aa_27_turn_07_oracle (h : ModifiedH) : h.H 1 = 6 := by
  rw [h.step0, h.base]; rfl

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$H(2)$$?
JSON expected answer: 14
-/
theorem aa_27_turn_08_oracle (h : ModifiedH) : h.H 2 = 14 := by
  rw [h.step1, h.step0, h.base]; rfl

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In this modified system, what is $$H(3)$$?
JSON expected answer: cannot be determined
-/
theorem aa_27_turn_09_oracle : Underdetermined (fun _ : ModifiedH => True) (fun h => h.H 3) := by
  exact ⟨completion 0, completion 1, True.intro, True.intro, by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$predecessor(4)$$?
JSON expected answer: cannot be determined
-/
theorem aa_27_turn_10_oracle : Underdetermined (fun _ : ModifiedH × (Nat → Nat) => True) (fun m => m.2 4) := by
  exact ⟨(completion 0, fun _ => 0), (completion 0, fun _ => 1), True.intro, True.intro, by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, does increasing the second argument by one successor step increase $$a+b$$ by $$1$$ or by $$2$$?
JSON expected answer: 2
-/
theorem aa_27_turn_11_oracle (a b : Nat) : modifiedAdd a (b+1) = modifiedAdd a b + 2 := by
  rfl

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement $$2+1=4$$ hold in ordinary arithmetic, in the modified system, or in both?
JSON expected answer: Only in the modified system.
-/
theorem aa_27_turn_12_oracle : (2:Nat)+1 ≠ 4 ∧ modifiedAdd 2 1 = 4 := by
  decide

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$2+2$$ in ordinary arithmetic, and what is it in the modified system?
JSON expected answer: 4 in ordinary arithmetic and 6 in the modified system.
-/
theorem aa_27_turn_13_oracle : parallel ((2:Nat)+2) (modifiedAdd 2 2) = (4,6) := by
  rfl

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary arithmetic. What is $$2+1$$?
JSON expected answer: 3
-/
theorem aa_27_turn_14_oracle : (2:Nat)+1=3 := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary arithmetic, what is $$H(2)$$?
JSON expected answer: 6
-/
theorem aa_27_turn_15_oracle (h : StandardH) : h.H 2 = 6 := by
  rw [h.step1, h.step0, h.base]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$2+1$$?
JSON expected answer: 4
-/
theorem aa_27_turn_16_oracle : modifiedAdd 2 1 = 4 := by
  rfl
