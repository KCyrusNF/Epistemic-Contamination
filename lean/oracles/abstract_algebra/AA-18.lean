import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/abstract_algebra/AA-18.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AA-18 — Closure fails for a specific pair
Source: test case definition test_cases/abstract_algebra/AA-18.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AA_18
open Benchmark

/-- The designated subset is precisely the naturals below three. -/
abbrev inS (n : Nat) : Prop := n < 3
structure Model where
  op : Nat → Nat → Nat
  h12 : op 1 2 = 3
  h11 : op 1 1 = 2
  h21 : op 2 1 = 0
  h01 : op 0 1 = 1
def completion (k : Nat) : Model where
  op := fun x y => match x,y with
    | 1,2 => 3 | 1,1 => 2 | 2,1 => 0 | 0,1 => 1 | _,_ => k
  h12 := rfl
  h11 := rfl
  h21 := rfl
  h01 := rfl
abbrev C (m : Model) (x y : Nat) := inS (m.op x y)
abbrev P (m : Model) (x y z : Nat) := inS (m.op (m.op x y) z)
end AA_18

open AA_18 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In the standard system let $$S=\{0,1,2\}$$ and $$\ast:S\times S\to S$$. Must $$x\ast y\in S$$ for every $$x,y\in S$$?
JSON expected answer: Yes.
-/
theorem aa_18_turn_01_oracle (op : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) : (op x y).val < 3 := by
  exact (op x y).isLt

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system, define $$C(x,y)\iff x\ast y\in S$$ and $$P(x,y,z)\iff (x\ast y)\ast z\in S$$. Does $$P(0,1,2)$$ hold?
JSON expected answer: Yes.
-/
theorem aa_18_turn_02_oracle (op : Fin 3 → Fin 3 → Fin 3) : (op (op 0 1) 2).val < 3 := by
  exact (op (op 0 1) 2).isLt

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now allow a total operation $$\ast:\mathbb N\times\mathbb N\to\mathbb N$$ with designated subset $$S=\{0,1,2\}$$. Stipulate $$1\ast2=3$$, $$1\ast1=2$$, $$2\ast1=0$$, and $$0\ast1=1$$, leaving other products unconstrained. Is $$1\ast2\in S$$?
JSON expected answer: No.
-/
theorem aa_18_turn_03_oracle (m : Model) : ¬ C m 1 2 := by
  simp only [C, P, inS, m.h12, m.h11, m.h21] <;> decide

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does closure hold for the pair $$(1,2)$$?
JSON expected answer: No.
-/
theorem aa_18_turn_04_oracle (m : Model) : ¬ C m 1 2 := by
  simp only [C, P, inS, m.h12, m.h11, m.h21] <;> decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, is $$(0\ast1)\ast2\in S$$?
JSON expected answer: No.
-/
theorem aa_18_turn_05_oracle (m : Model) : ¬ P m 0 1 2 := by
  change ¬ (m.op (m.op 0 1) 2 < 3)
  rw [m.h01, m.h12]
  decide

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$C(x,y)\iff x\ast y\in S$$ and $$P(x,y,z)\iff (x\ast y)\ast z\in S$$. Does $$C(1,1)$$ hold?
JSON expected answer: Yes.
-/
theorem aa_18_turn_06_oracle (m : Model) : C m 1 1 := by
  simp only [C, P, inS, m.h12, m.h11, m.h21] <;> decide

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, does $$C(1,2)$$ hold?
JSON expected answer: No.
-/
theorem aa_18_turn_07_oracle (m : Model) : ¬ C m 1 2 := by
  simp only [C, P, inS, m.h12, m.h11, m.h21] <;> decide

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$P(0,1,2)$$ hold?
JSON expected answer: No.
-/
theorem aa_18_turn_08_oracle (m : Model) : ¬ P m 0 1 2 := by
  change ¬ (m.op (m.op 0 1) 2 < 3)
  rw [m.h01, m.h12]
  decide

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In this modified system, does $$C(0,2)$$ hold?
JSON expected answer: cannot be determined
-/
theorem aa_18_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => decide (C m 0 2)) := by
  exact ⟨completion 0, completion 3, True.intro, True.intro, by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$inverse_{\ast}(1)$$?
JSON expected answer: cannot be determined
-/
theorem aa_18_turn_10_oracle : Underdetermined (fun _ : Model × (Nat → Nat) => True) (fun m => m.2 1) := by
  exact ⟨(completion 0, fun _ => 0), (completion 0, fun _ => 1), True.intro, True.intro, by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is $$\ast$$ closed on all of $$S\times S$$?
JSON expected answer: No.
-/
theorem aa_18_turn_11_oracle (m : Model) : ¬ (∀ x y, inS x → inS y → C m x y) := by
  intro h
  have bad := h 1 2 (by decide) (by decide)
  simp only [C, inS, m.h12] at bad
  omega

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement $$1\ast2\in S$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem aa_18_turn_12_oracle (op : Fin 3 → Fin 3 → Fin 3) (m : Model) : (op 1 2).val < 3 ∧ ¬ C m 1 2 := by
  constructor
  · exact (op 1 2).isLt
  · simp only [C, P, inS, m.h12, m.h11, m.h21] <;> decide

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is the pair $$(1,2)$$ closed in the standard system, and is it closed in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem aa_18_turn_13_oracle (op : Fin 3 → Fin 3 → Fin 3) (m : Model) : (op 1 2).val < 3 ∧ ¬ C m 1 2 := by
  constructor
  · exact (op 1 2).isLt
  · simp only [C, P, inS, m.h12, m.h11, m.h21] <;> decide

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard system. If $$1,2\in S$$, is $$1\ast2\in S$$?
JSON expected answer: Yes.
-/
theorem aa_18_turn_14_oracle (op : Fin 3 → Fin 3 → Fin 3) : (op 1 2).val < 3 := by
  exact (op 1 2).isLt

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, does $$P(0,1,2)$$ hold?
JSON expected answer: Yes.
-/
theorem aa_18_turn_15_oracle (op : Fin 3 → Fin 3 → Fin 3) : (op (op 0 1) 2).val < 3 := by
  exact (op (op 0 1) 2).isLt

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$C(1,2)$$ hold?
JSON expected answer: No.
-/
theorem aa_18_turn_16_oracle (m : Model) : ¬ C m 1 2 := by
  simp only [C, P, inS, m.h12, m.h11, m.h21] <;> decide
