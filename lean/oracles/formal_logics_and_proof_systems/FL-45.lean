import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/formal_logics_and_proof_systems/FL-45.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: FL-45 — Cut rule invalid for one formula family
Source: test case definition test_cases/formal_logics_and_proof_systems/FL-45.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace FL_45
open Benchmark

-- Named atoms/constants P,Q,R,X correspond to 0,1,2,3.
structure Model where
  allowed : Nat → Bool
  blocked : allowed 0 = false
  q : allowed 1 = true
  r : allowed 2 = true
def completion (free : Bool) : Model where
  allowed := fun n => if n=0 then false else if n=1 ∨ n=2 then true else free
  blocked := by norm_num
  q := by norm_num
  r := by norm_num
def allSteps (allow : Nat → Bool) (xs : List Nat) := xs.all allow

end FL_45

open FL_45 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard proof system with cut, from $$\Gamma\vdash P$$ and $$\Delta,P\vdash Q$$ can $$\Gamma,\Delta\vdash Q$$ be derived?
JSON expected answer: Yes.
-/
theorem fl_45_turn_01_oracle {Γ Δ P Q : Prop} (first : Γ → P) (second : Δ → P → Q) : Γ ∧ Δ → Q := by
  rintro ⟨hg,hd⟩; exact second hd (first hg)

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$CutOK([X_1,\ldots,X_n])$$ to mean that successive cuts through these formulas are permitted when all required premise derivations are supplied. Does $$CutOK([P,Q])$$ hold?
JSON expected answer: Yes.
-/
theorem fl_45_turn_02_oracle : allSteps (fun _ => true) [0,1] = true := by
  rfl

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a syntactic proof calculus where cut is permitted exactly when its cut formula is outside a class $$C$$. Stipulate $$P\in C$$ and $$Q,R\notin C$$, leaving other membership unconstrained. From $$\Gamma\vdash P$$ and $$\Delta,P\vdash Q$$, can cut derive $$\Gamma,\Delta\vdash Q$$?
JSON expected answer: No.
-/
theorem fl_45_turn_03_oracle (m : Model) : m.allowed 0 = false := by
  exact m.blocked

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard cut inference succeed when the cut formula is $$P$$?
JSON expected answer: No.
-/
theorem fl_45_turn_04_oracle (m : Model) : m.allowed 0 = false := by
  exact m.blocked

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, with the required premise derivations supplied, can two successive cuts through $$R$$ and $$Q$$ both be performed?
JSON expected answer: Yes.
-/
theorem fl_45_turn_05_oracle (m : Model) : allSteps m.allowed [2,1] = true := by
  simp_all [allSteps, m.blocked, m.q, m.r]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$CutOK([])=true$$ and $$CutOK([X]+L)\iff(X\notin C)\land CutOK(L)$$. This tests permission with all required premise derivations supplied. Does $$CutOK([])$$ hold?
JSON expected answer: Yes.
-/
theorem fl_45_turn_06_oracle (m : Model) : allSteps m.allowed [] = true := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$CutOK([P])$$ hold?
JSON expected answer: No.
-/
theorem fl_45_turn_07_oracle (m : Model) : allSteps m.allowed [0] = false := by
  simp_all [allSteps, m.blocked, m.q, m.r]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$CutOK([R,P])$$ hold?
JSON expected answer: No.
-/
theorem fl_45_turn_08_oracle (m : Model) : allSteps m.allowed [2,0] = false := by
  simp_all [allSteps, m.blocked, m.q, m.r]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$CutOK([R,X])$$ hold?
JSON expected answer: cannot be determined
-/
theorem fl_45_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => allSteps m.allowed [2,3]) := by
  exact ⟨completion false,completion true,True.intro,True.intro,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is the truth value of $$P$$?
JSON expected answer: cannot be determined
-/
theorem fl_45_turn_10_oracle : Underdetermined (fun _ : Model × Bool => True) (fun m => m.2) := by
  exact ⟨(completion false,false),(completion false,true),True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is cut valid for every formula?
JSON expected answer: No.
-/
theorem fl_45_turn_11_oracle (m : Model) : ¬ (∀ a, m.allowed a = true) := by
  intro h
  have bad := h 0
  rw [m.blocked] at bad
  contradiction

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does cut through $$P$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem fl_45_turn_12_oracle (m : Model) : allSteps (fun _ => true) [0] = true ∧ allSteps m.allowed [0] = false := by
  simp_all [allSteps, m.blocked, m.q, m.r]

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Can the stated cut through $$P$$ be performed in the standard system, and can it be performed in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem fl_45_turn_13_oracle (m : Model) : allSteps (fun _ => true) [0] = true ∧ allSteps m.allowed [0] = false := by
  simp_all [allSteps, m.blocked, m.q, m.r]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard proof system. Can the cut through $$P$$ be performed?
JSON expected answer: Yes.
-/
theorem fl_45_turn_14_oracle : allSteps (fun _ => true) [0] = true := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, does $$CutOK([P,Q])$$ hold when the required premise derivations are supplied?
JSON expected answer: Yes.
-/
theorem fl_45_turn_15_oracle : allSteps (fun _ => true) [0,1] = true := by
  rfl

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is cut through $$P$$ permitted?
JSON expected answer: No.
-/
theorem fl_45_turn_16_oracle (m : Model) : m.allowed 0 = false := by
  exact m.blocked
