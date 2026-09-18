import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/formal_logics_and_proof_systems/FL-21.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: FL-21 — Explosion (⊥ ⊢ φ) blocked
Source: test case definition test_cases/formal_logics_and_proof_systems/FL-21.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace FL_21
open Benchmark

inductive Reach (allow : Nat → Bool) (edges : List (Nat × Nat)) (initial : List Nat) : Nat → Prop
  | assumption {a} : a ∈ initial → Reach allow edges initial a
  | mp {a b} : Reach allow edges initial a → (a,b) ∈ edges → allow a = true → Reach allow edges initial b

theorem invariant {allow edges initial} (p : Nat → Prop)
    (base : ∀ a, a ∈ initial → p a)
    (step : ∀ a b, p a → (a,b) ∈ edges → allow a = true → p b)
    {x} (h : Reach allow edges initial x) : p x := by
  induction h with
  | assumption h => exact base _ h
  | mp h edge ok ih => exact step _ _ ih edge ok

def initial (extra : Bool) : List Nat := if extra then [0,3] else [0]
def E (extra : Bool) (x : Nat) := Reach (fun _ => true) [(1,2)] (initial extra) x
theorem onlyAssumptions (extra : Bool) {x} (h : E extra x) : x ∈ initial extra := by
  apply invariant (fun x => x ∈ initial extra) ?_ ?_ h
  · intro a ha; exact ha
  · intro a b ha he ok
    simp only [List.mem_singleton, Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    cases extra <;> simp [initial] at ha

end FL_21

open FL_21 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard classical proof system with explosion, does $$\bot\vdash P$$ hold for every formula $$P$$?
JSON expected answer: Yes.
-/
theorem fl_21_turn_01_oracle (P : Prop) (bottom : False) : P := by
  exact bottom.elim

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system let $$\{\bot,P\to Q\}\subseteq\Gamma\subseteq\{\bot,P\to Q,X\}$$, with distinct atoms $$P,Q,X$$. Define $$E(F)$$ to mean derivability from $$\Gamma$$ by assumption lookup, Modus Ponens, and explosion. Do both $$E(P)$$ and $$E(Q)$$ hold?
JSON expected answer: Yes.
-/
theorem fl_21_turn_02_oracle (P Q : Prop) (bottom : False) : P ∧ Q := by
  exact bottom.elim

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use syntactic formulas and the same constraints on $$\Gamma$$, but allow only assumption lookup and Modus Ponens; explosion is blocked and no other rules or axioms are available. Can $$P$$ be derived from $$\bot$$ by explosion?
JSON expected answer: No.
-/
theorem fl_21_turn_03_oracle (extra : Bool) : ¬ E extra 1 := by
  intro h; have bad := onlyAssumptions extra h; cases extra <;> simp [initial] at bad

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$\bot\vdash P$$ follow from the blocked explosion rule?
JSON expected answer: No.
-/
theorem fl_21_turn_04_oracle (extra : Bool) : ¬ E extra 1 := by
  intro h; have bad := onlyAssumptions extra h; cases extra <;> simp [initial] at bad

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does applying Modus Ponens after an attempted explosion from $$\bot$$ yield $$Q$$ using $$P\to Q$$?
JSON expected answer: No.
-/
theorem fl_21_turn_05_oracle (extra : Bool) : ¬ E extra 2 := by
  intro h; have bad := onlyAssumptions extra h; cases extra <;> simp [initial] at bad

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$E(F)$$ as derivability from $$\Gamma$$ using the current rules. Does the base case $$E(\bot)$$ hold by assumption lookup?
JSON expected answer: Yes.
-/
theorem fl_21_turn_06_oracle (extra : Bool) : E extra 0 := by
  apply Reach.assumption; cases extra <;> simp [initial]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$E(P)$$ hold?
JSON expected answer: No.
-/
theorem fl_21_turn_07_oracle (extra : Bool) : ¬ E extra 1 := by
  intro h; have bad := onlyAssumptions extra h; cases extra <;> simp [initial] at bad

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$E(Q)$$ hold after closing $$\Gamma$$ under the available inference rules?
JSON expected answer: No.
-/
theorem fl_21_turn_08_oracle (extra : Bool) : ¬ E extra 2 := by
  intro h; have bad := onlyAssumptions extra h; cases extra <;> simp [initial] at bad

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$E(X)$$ hold?
JSON expected answer: cannot be determined
-/
theorem fl_21_turn_09_oracle : Underdetermined (fun _ : Bool => True) (fun extra => E extra 3) := by
  refine ⟨false,true,True.intro,True.intro,?_⟩
  intro h
  have yes : E true 3 := .assumption (by simp [initial])
  have bad := onlyAssumptions false (h.mpr yes)
  simp [initial] at bad

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what truth value does a valuation assign to $$P$$?
JSON expected answer: cannot be determined
-/
theorem fl_21_turn_10_oracle : Underdetermined (fun _ : Bool × Bool => True) (fun m => m.2) := by
  exact ⟨(false,false),(false,true),True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, does contradiction license every formula?
JSON expected answer: No.
-/
theorem fl_21_turn_11_oracle (extra : Bool) : ¬ (∀ x, E extra x) := by
  intro h; have bad := onlyAssumptions extra (h 1); cases extra <;> simp [initial] at bad

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$\bot\vdash P$$ by explosion hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem fl_21_turn_12_oracle (extra : Bool) : (∀ P : Prop, False → P) ∧ ¬ E extra 1 := by
  constructor
  · intro P h; exact h.elim
  · intro h; have bad := onlyAssumptions extra h; cases extra <;> simp [initial] at bad

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Can $$P$$ be derived from $$\bot$$ by explosion in the standard system, and can it be derived by explosion in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem fl_21_turn_13_oracle (extra : Bool) : (∀ P : Prop, False → P) ∧ ¬ E extra 1 := by
  constructor
  · intro P h; exact h.elim
  · intro h; have bad := onlyAssumptions extra h; cases extra <;> simp [initial] at bad

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard proof system. Does $$\bot\vdash P$$ hold by explosion?
JSON expected answer: Yes.
-/
theorem fl_21_turn_14_oracle (P : Prop) (bottom : False) : P := by
  exact bottom.elim

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system and its original rules, do both $$E(P)$$ and $$E(Q)$$ hold?
JSON expected answer: Yes.
-/
theorem fl_21_turn_15_oracle (P Q : Prop) (bottom : False) : P ∧ Q := by
  exact bottom.elim

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Can $$P$$ be derived from $$\bot$$ by explosion?
JSON expected answer: No.
-/
theorem fl_21_turn_16_oracle (extra : Bool) : ¬ E extra 1 := by
  intro h; have bad := onlyAssumptions extra h; cases extra <;> simp [initial] at bad
