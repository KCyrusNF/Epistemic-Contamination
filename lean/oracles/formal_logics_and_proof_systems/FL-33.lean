import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/formal_logics_and_proof_systems/FL-33.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: FL-33 — Universal instantiation blocked for one constant
Source: test case definition test_cases/formal_logics_and_proof_systems/FL-33.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace FL_33
open Benchmark

-- Named atoms/constants P,Q,R,X correspond to 0,1,2,3.
structure Model where
  allowed : Nat → Bool
  blocked : allowed 0 = false
  q : allowed 1 = true
def completion (free : Bool) : Model where
  allowed := fun n => if n=0 then false else if n=1 then true else free
  blocked := by norm_num
  q := by norm_num
def allSteps (allow : Nat → Bool) (xs : List Nat) := xs.all allow

def I (allow : Nat → Bool) (f : Nat → α) (c : Nat) : Option α :=
  if allow c then some (f c) else none
def two (allow : Nat → Bool) (a b : Nat) : Option (Nat × Nat) :=
  (I allow (fun x y => (x,y)) a).bind (fun f => I allow f b)

end FL_33

open FL_33 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard proof system, from $$\forall x\,P(x)$$ can $$P(c)$$ be derived for any constant $$c$$?
JSON expected answer: Yes.
-/
theorem fl_33_turn_01_oracle {α : Type} (P : α → Prop) (h : ∀ x, P x) (c : α) : P c := by
  exact h c

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$I(F,c)$$ as the formula produced by instantiating the outer universal quantifier of $$F$$ at $$c$$. Can successive applications to $$\forall x\forall y\,R(x,y)$$ at $$c_1$$ then $$c_0$$ produce $$R(c_1,c_0)$$?
JSON expected answer: Yes.
-/
theorem fl_33_turn_02_oracle : two (fun _ => true) 1 0 = some (1,0) := by
  rfl

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use syntactic formulas and universal instantiation permitted exactly at constants outside a blocked set $$K$$. Stipulate $$c_0\in K$$ and $$c_1\notin K$$, with other membership unconstrained. No alternative instantiation rules are supplied. From $$\forall x\,P(x)$$, can this rule derive $$P(c_0)$$?
JSON expected answer: No.
-/
theorem fl_33_turn_03_oracle (m : Model) : I m.allowed id 0 = none := by
  simp_all [I, two, m.blocked, m.q]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard instantiation rule yield $$P(c_0)$$?
JSON expected answer: No.
-/
theorem fl_33_turn_04_oracle (m : Model) : I m.allowed id 0 = none := by
  simp_all [I, two, m.blocked, m.q]

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, can two instantiations at $$c_1$$ produce $$R(c_1,c_1)$$ from $$\forall x\forall y\,R(x,y)$$?
JSON expected answer: Yes.
-/
theorem fl_33_turn_05_oracle (m : Model) : two m.allowed 1 1 = some (1,1) := by
  simp_all [I, two, m.blocked, m.q]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$I(F,c)$$ by the permitted outer-quantifier instantiation, with failure when the constant is blocked. Can $$I(\forall x\,P(x),c_1)$$ produce $$P(c_1)$$?
JSON expected answer: Yes.
-/
theorem fl_33_turn_06_oracle (m : Model) : I m.allowed id 1 = some 1 := by
  simp_all [I, two, m.blocked, m.q]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, can $$I(\forall x\,P(x),c_0)$$ produce $$P(c_0)$$?
JSON expected answer: No.
-/
theorem fl_33_turn_07_oracle (m : Model) : I m.allowed id 0 = none := by
  simp_all [I, two, m.blocked, m.q]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, can successive applications of $$I$$ at $$c_1$$ then $$c_0$$ produce $$R(c_1,c_0)$$ from $$\forall x\forall y\,R(x,y)$$?
JSON expected answer: No.
-/
theorem fl_33_turn_08_oracle (m : Model) : two m.allowed 1 0 = none := by
  simp_all [I, two, m.blocked, m.q]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, can $$I(\forall x\,P(x),k)$$ produce $$P(k)$$?
JSON expected answer: cannot be determined
-/
theorem fl_33_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => I m.allowed id 3) := by
  exact ⟨completion false,completion true,True.intro,True.intro,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is the denotation of $$c_0$$?
JSON expected answer: cannot be determined
-/
theorem fl_33_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is universal instantiation valid for every constant?
JSON expected answer: No.
-/
theorem fl_33_turn_11_oracle (m : Model) : ¬ (∀ c, I m.allowed id c = some c) := by
  intro h
  have bad := h 0
  simp_all [I, two, m.blocked, m.q]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does instantiation to $$c_0$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem fl_33_turn_12_oracle (m : Model) : I (fun _ => true) id 0 = some 0 ∧ I m.allowed id 0 = none := by
  simp_all [I, two, m.blocked, m.q]

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Can $$P(c_0)$$ be derived from $$\forall x\,P(x)$$ in the standard system, and can it be derived by universal instantiation in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem fl_33_turn_13_oracle (m : Model) : I (fun _ => true) id 0 = some 0 ∧ I m.allowed id 0 = none := by
  simp_all [I, two, m.blocked, m.q]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard proof system. Can $$P(c_0)$$ be derived from $$\forall x\,P(x)$$?
JSON expected answer: Yes.
-/
theorem fl_33_turn_14_oracle : I (fun _ => true) id 0 = some 0 := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, can successive applications of $$I$$ at $$c_1$$ then $$c_0$$ produce $$R(c_1,c_0)$$ from $$\forall x\forall y\,R(x,y)$$?
JSON expected answer: Yes.
-/
theorem fl_33_turn_15_oracle : two (fun _ => true) 1 0 = some (1,0) := by
  rfl

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Can universal instantiation at $$c_0$$ derive $$P(c_0)$$ from $$\forall x\,P(x)$$?
JSON expected answer: No.
-/
theorem fl_33_turn_16_oracle (m : Model) : I m.allowed id 0 = none := by
  simp_all [I, two, m.blocked, m.q]
