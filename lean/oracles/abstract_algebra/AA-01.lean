import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/abstract_algebra/AA-01.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AA-01 — Operation not associative
Source: test case definition test_cases/abstract_algebra/AA-01.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AA_01
open Benchmark

structure Model where
  op : Nat → Nat → Nat
  h11 : op 1 1 = 0
  h01 : op 0 1 = 1
  h02 : op 0 2 = 2
  h12 : op 1 2 = 3
  h13 : op 1 3 = 4
  h23 : op 2 3 = 5
def completion (k : Nat) : Model where
  op := fun x y => match x,y with
    | 1,1 => 0 | 0,1 => 1 | 0,2 => 2 | 1,2 => 3 | 1,3 => 4 | 2,3 => 5 | _,_ => k
  h11 := rfl
  h01 := rfl
  h02 := rfl
  h12 := rfl
  h13 := rfl
  h23 := rfl
def L (op : Nat → Nat → Nat) := iterateRight op 1

end AA_01

open AA_01 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In the standard system on $$\mathbb N$$, let $$x\ast y=x+y$$ using ordinary addition. Does $$(1\ast1)\ast2=1\ast(1\ast2)$$ hold?
JSON expected answer: Yes.
-/
theorem aa_01_turn_01_oracle : ((1:Nat)+1)+2 = 1+(1+2) := by
  rfl

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$L(x,0)=x$$ and $$L(x,n+1)=L(x,n)\ast1$$ for all natural numbers. Does $$L(L(1,1),1)=3$$ hold?
JSON expected answer: Yes.
-/
theorem aa_01_turn_02_oracle : L Nat.add (L Nat.add 1 1) 1 = 3 := by
  rfl

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a total operation $$\ast$$ on $$\mathbb N$$ with $$1\ast1=0$$, $$0\ast1=1$$, $$0\ast2=2$$, $$1\ast2=3$$, $$1\ast3=4$$, and $$2\ast3=5$$. Other products and algebraic laws are unconstrained; indexing arithmetic remains ordinary. What is $$(1\ast1)\ast2$$?
JSON expected answer: 2
-/
theorem aa_01_turn_03_oracle (m : Model) : m.op (m.op 1 1) 2 = 2 := by
  simp only [L, iterateRight, m.h11, m.h01, m.h02, m.h12, m.h13, m.h23] <;> decide

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$(1\ast1)\ast2=1\ast(1\ast2)$$ hold?
JSON expected answer: No.
-/
theorem aa_01_turn_04_oracle (m : Model) : m.op (m.op 1 1) 2 ≠ m.op 1 (m.op 1 2) := by
  simp only [L, iterateRight, m.h11, m.h01, m.h02, m.h12, m.h13, m.h23] <;> decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, what is $$((1\ast1)\ast2)\ast3$$?
JSON expected answer: 5
-/
theorem aa_01_turn_05_oracle (m : Model) : m.op (m.op (m.op 1 1) 2) 3 = 5 := by
  simp only [L, iterateRight, m.h11, m.h01, m.h02, m.h12, m.h13, m.h23] <;> decide

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$L(x,0)=x$$ and $$L(x,n+1)=L(x,n)\ast1$$ for all natural numbers. What is $$L(0,0)$$?
JSON expected answer: 0
-/
theorem aa_01_turn_06_oracle (m : Model) : L m.op 0 0 = 0 := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$L(1,1)$$?
JSON expected answer: 0
-/
theorem aa_01_turn_07_oracle (m : Model) : L m.op 1 1 = 0 := by
  simp only [L, iterateRight, m.h11, m.h01, m.h02, m.h12, m.h13, m.h23] <;> decide

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$L(L(1,1),1)$$?
JSON expected answer: 1
-/
theorem aa_01_turn_08_oracle (m : Model) : L m.op (L m.op 1 1) 1 = 1 := by
  simp only [L, iterateRight, m.h11, m.h01, m.h02, m.h12, m.h13, m.h23] <;> decide

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$L(2,1)$$?
JSON expected answer: cannot be determined
-/
theorem aa_01_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => L m.op 2 1) := by
  exact ⟨completion 0, completion 1, True.intro, True.intro, by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$inverse_{\ast}(1)$$?
JSON expected answer: cannot be determined
-/
theorem aa_01_turn_10_oracle : Underdetermined (fun _ : Model × (Nat → Nat) => True) (fun m => m.2 1) := by
  exact ⟨(completion 0, fun _ => 0), (completion 0, fun _ => 1), True.intro, True.intro, by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is $$\ast$$ associative for all triples?
JSON expected answer: No.
-/
theorem aa_01_turn_11_oracle (m : Model) : ¬ (∀ x y z, m.op (m.op x y) z = m.op x (m.op y z)) := by
  intro h
  have bad := h 1 1 2
  simp only [m.h11, m.h02, m.h12, m.h13] at bad
  contradiction

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement $$(1\ast1)\ast2=1\ast(1\ast2)$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem aa_01_turn_12_oracle (m : Model) : ((1:Nat)+1)+2 = 1+(1+2) ∧ m.op (m.op 1 1) 2 ≠ m.op 1 (m.op 1 2) := by
  constructor
  · rfl
  · simp only [L, iterateRight, m.h11, m.h01, m.h02, m.h12, m.h13, m.h23] <;> decide

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$(1\ast1)\ast2$$ in the standard system, and what is it in the modified system?
JSON expected answer: 4 in the standard system and 2 in the modified system.
-/
theorem aa_01_turn_13_oracle (m : Model) : parallel (((1:Nat)+1)+2) (m.op (m.op 1 1) 2) = (4,2) := by
  rw [m.h11, m.h02]
  rfl

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard system. Does $$(1\ast1)\ast2=1\ast(1\ast2)$$ hold?
JSON expected answer: Yes.
-/
theorem aa_01_turn_14_oracle : ((1:Nat)+1)+2 = 1+(1+2) := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, does $$L(L(1,1),1)=3$$ hold?
JSON expected answer: Yes.
-/
theorem aa_01_turn_15_oracle : L Nat.add (L Nat.add 1 1) 1 = 3 := by
  rfl

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$(1\ast1)\ast2$$?
JSON expected answer: 2
-/
theorem aa_01_turn_16_oracle (m : Model) : m.op (m.op 1 1) 2 = 2 := by
  simp only [L, iterateRight, m.h11, m.h01, m.h02, m.h12, m.h13, m.h23] <;> decide
