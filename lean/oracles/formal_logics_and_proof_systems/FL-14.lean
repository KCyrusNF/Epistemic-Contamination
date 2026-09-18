import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/formal_logics_and_proof_systems/FL-14.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: FL-14 — Disjunction elimination invalid for one branch
Source: test case definition test_cases/formal_logics_and_proof_systems/FL-14.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace FL_14
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

/-- Branch implications are supplied by each query; this operation tests permission. -/
def casesRule (allow : Nat → Bool) (right result : Nat) : Option Nat :=
  if allow right then some result else none
/-- The following MP step has its antecedent available only after successful case analysis. -/
def propagate (allow : Nat → Bool) (right result next : Nat) :=
  (casesRule allow right result).map (fun _ => next)

end FL_14

open FL_14 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard proof system, from $$A\lor B$$, $$A\rightarrow C$$, and $$B\rightarrow C$$, can $$C$$ be derived by disjunction elimination?
JSON expected answer: Yes.
-/
theorem fl_14_turn_01_oracle {A B C : Prop} (h : A ∨ B) (left : A → C) (right : B → C) : C := by
  exact h.elim left right

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define case-analysis propagation as disjunction elimination followed by Modus Ponens along a supplied implication chain. From $$A\lor B,A\to C,B\to C,C\to D$$, does it yield $$D$$?
JSON expected answer: Yes.
-/
theorem fl_14_turn_02_oracle {A B C D : Prop} (h : A ∨ B) (left : A → C) (right : B → C) (next : C → D) : D := by
  exact next (h.elim left right)

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a syntactic calculus whose only inference rules are assumption lookup, Modus Ponens, and disjunction elimination. The last rule is permitted exactly when the right branch is outside a blocked class $$K$$. Stipulate $$B_0\in K$$ and $$B_1\notin K$$; other membership is unconstrained. All named atoms are distinct and premises are local to each query. From $$A\lor B_0,A\to C,B_0\to C$$, does disjunction elimination yield $$C$$?
JSON expected answer: No.
-/
theorem fl_14_turn_03_oracle (m : Model) : casesRule m.allowed 0 4 = none := by
  simp_all [casesRule,propagate,m.blocked,m.q]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard disjunction-elimination inference yield $$C$$ for the right branch $$B_0$$?
JSON expected answer: No.
-/
theorem fl_14_turn_04_oracle (m : Model) : casesRule m.allowed 0 4 = none := by
  simp_all [casesRule,propagate,m.blocked,m.q]

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, from $$A\lor B_1,A\to C,B_1\to C,C\to D$$, can case analysis followed by Modus Ponens derive $$D$$?
JSON expected answer: Yes.
-/
theorem fl_14_turn_05_oracle (m : Model) : propagate m.allowed 1 4 5 = some 5 := by
  simp_all [casesRule,propagate,m.blocked,m.q]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct case-analysis propagation: use the permitted disjunction elimination, then follow any supplied implication chain by Modus Ponens. With no subsequent implications, does it yield $$C$$ from $$A\lor B_1,A\to C,B_1\to C$$?
JSON expected answer: Yes.
-/
theorem fl_14_turn_06_oracle (m : Model) : casesRule m.allowed 1 4 = some 4 := by
  simp_all [casesRule,propagate,m.blocked,m.q]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does the same rule yield $$C$$ from $$A\lor B_0,A\to C,B_0\to C$$?
JSON expected answer: No.
-/
theorem fl_14_turn_07_oracle (m : Model) : casesRule m.allowed 0 4 = none := by
  simp_all [casesRule,propagate,m.blocked,m.q]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does case-analysis propagation yield $$D$$ from $$A\lor B_0,A\to C,B_0\to C,C\to D$$?
JSON expected answer: No.
-/
theorem fl_14_turn_08_oracle (m : Model) : propagate m.allowed 0 4 5 = none := by
  simp_all [casesRule,propagate,m.blocked,m.q]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does case-analysis propagation yield $$D$$ from $$A\lor X,A\to C,X\to C,C\to D$$?
JSON expected answer: cannot be determined
-/
theorem fl_14_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => propagate m.allowed 3 4 5) := by
  exact ⟨completion false,completion true,True.intro,True.intro,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is the truth value of $$A\lor B_0$$?
JSON expected answer: cannot be determined
-/
theorem fl_14_turn_10_oracle : Underdetermined (fun _ : Model × Bool => True) (fun m => m.2) := by
  exact ⟨(completion false,false),(completion false,true),True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is disjunction elimination valid for every branch?
JSON expected answer: No.
-/
theorem fl_14_turn_11_oracle (m : Model) : ¬ (∀ x, casesRule m.allowed x 4 = some 4) := by
  intro h
  have bad := h 0
  simp_all [casesRule,propagate,m.blocked,m.q]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does disjunction elimination for $$A\lor B_0$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem fl_14_turn_12_oracle (m : Model) : casesRule (fun _ => true) 0 4 = some 4 ∧ casesRule m.allowed 0 4 = none := by
  simp_all [casesRule,propagate,m.blocked,m.q]

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Can $$C$$ be derived from the two branches in the standard system, and can it be derived in the modified system when the right branch is $$B_0$$?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem fl_14_turn_13_oracle (m : Model) : casesRule (fun _ => true) 0 4 = some 4 ∧ casesRule m.allowed 0 4 = none := by
  simp_all [casesRule,propagate,m.blocked,m.q]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard proof system. Can $$C$$ be derived from $$A\lor B_0$$ and the two branch implications?
JSON expected answer: Yes.
-/
theorem fl_14_turn_14_oracle : casesRule (fun _ => true) 0 4 = some 4 := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, does case-analysis propagation derive $$D$$ from $$A\lor B_0,A\to C,B_0\to C,C\to D$$?
JSON expected answer: Yes.
-/
theorem fl_14_turn_15_oracle {A B C D : Prop} (h : A ∨ B) (left : A → C) (right : B → C) (next : C → D) : D := by
  exact next (h.elim left right)

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Can $$C$$ be derived by disjunction elimination from $$A\lor B_0$$ and the two branch implications?
JSON expected answer: No.
-/
theorem fl_14_turn_16_oracle (m : Model) : casesRule m.allowed 0 4 = none := by
  simp_all [casesRule,propagate,m.blocked,m.q]
