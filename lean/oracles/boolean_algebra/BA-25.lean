import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/boolean_algebra/BA-25.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: BA-25 — a ∧ ¬a ≠ 0
Source: test case definition test_cases/boolean_algebra/BA-25.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace BA_25
open Benchmark
variable {α : Type}
structure Model (α : Type) where
  meet : α → α → α
  neg : α → α
  zero : α
  a : α
  b : α
  c : α
  distinct : [zero,a,b,c].Nodup
  ha : meet a (neg a) = b
  hb : meet b (neg b) = b
  hz : meet zero (neg zero) = zero
def C (m : Model α) (x : α) := m.meet x (m.neg x)
def completion (k : Fin 4) : Model (Fin 4) where
  meet := fun x _ => if x=0 then 0 else if x=1 ∨ x=2 then 2 else k
  neg := id
  zero := 0
  a := 1
  b := 2
  c := 3
  distinct := by decide
  ha := by norm_num
  hb := by norm_num
  hz := by norm_num

theorem modifiedValue (m : Model α) : C m m.a = m.b := m.ha
theorem modifiedDifferent (m : Model α) : C m m.a ≠ m.zero := by
  rw [modifiedValue m]
  exact by
    have h := m.distinct
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h
    exact Ne.symm h.1.2.1

end BA_25

open BA_25 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary Boolean algebra, does $$a\land\neg a=0$$ hold?
JSON expected answer: Yes.
-/
theorem ba_25_turn_01_oracle {α : Type} [BooleanAlgebra α] (x : α) : x ⊓ xᶜ = ⊥ := by
  simp

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system, define $$C(x)=x\land\neg x$$. What is $$C(C(a))$$?
JSON expected answer: 0
-/
theorem ba_25_turn_02_oracle {α : Type} [BooleanAlgebra α] (x : α) : (x ⊓ xᶜ) ⊓ (x ⊓ xᶜ)ᶜ = ⊥ := by
  simp

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a carrier with total meet and negation operations and distinct elements $$0,a,b,c$$. Stipulate $$a\land\neg a=b$$, $$b\land\neg b=b$$, and $$0\land\neg0=0$$; no other Boolean laws are assumed. What is $$a\land\neg a$$?
JSON expected answer: b
-/
theorem ba_25_turn_03_oracle {α : Type} (m : Model α) : C m m.a = m.b := by
  exact modifiedValue m


/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$a\land\neg a=0$$ hold?
JSON expected answer: No.
-/
theorem ba_25_turn_04_oracle {α : Type} (m : Model α) : C m m.a ≠ m.zero := by
  exact modifiedDifferent m


/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, what is $$(a\land\neg a)\land\neg(a\land\neg a)$$?
JSON expected answer: b
-/
theorem ba_25_turn_05_oracle {α : Type} (m : Model α) : C m (C m m.a) = m.b := by
  rw [modifiedValue m]
  exact m.hb


/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$C(x)=x\land\neg x$$. What is $$C(0)$$?
JSON expected answer: 0
-/
theorem ba_25_turn_06_oracle {α : Type} (m : Model α) : C m m.zero = m.zero := by
  exact m.hz


/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$C(a)$$?
JSON expected answer: b
-/
theorem ba_25_turn_07_oracle {α : Type} (m : Model α) : C m m.a = m.b := by
  exact modifiedValue m


/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$C(C(a))$$?
JSON expected answer: b
-/
theorem ba_25_turn_08_oracle {α : Type} (m : Model α) : C m (C m m.a) = m.b := by
  rw [modifiedValue m]
  exact m.hb


/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$C(c)$$?
JSON expected answer: cannot be determined
-/
theorem ba_25_turn_09_oracle : Underdetermined (fun _ : Model (Fin 4) => True) (fun m => C m m.c) := by
  exact ⟨completion 0,completion 1,True.intro,True.intro,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$a\rightarrow0$$?
JSON expected answer: cannot be determined
-/
theorem ba_25_turn_10_oracle : Underdetermined (fun _ : Model (Fin 4) × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is $$x\land\neg x=0$$ guaranteed for every element?
JSON expected answer: No.
-/
theorem ba_25_turn_11_oracle {α : Type} (m : Model α) : ¬ (∀ x, C m x = m.zero) := by
  intro h
  exact modifiedDifferent m (h m.a)


/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$a\land\neg a=0$$ hold in ordinary Boolean algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ba_25_turn_12_oracle {α β : Type} [BooleanAlgebra α] (x : α) (m : Model β) : (x ⊓ xᶜ = ⊥) ∧ (C m m.a = m.b ∧ C m m.a ≠ m.zero) := by
  exact ⟨by simp, modifiedValue m, modifiedDifferent m⟩


/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$a\land\neg a$$ in ordinary Boolean algebra, and what is it in the modified system?
JSON expected answer: 0 in the standard system and b in the modified system.
-/
theorem ba_25_turn_13_oracle {α β : Type} [BooleanAlgebra α] (x : α) (m : Model β) : (x ⊓ xᶜ = ⊥) ∧ (C m m.a = m.b ∧ C m m.a ≠ m.zero) := by
  exact ⟨by simp, modifiedValue m, modifiedDifferent m⟩


/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary Boolean algebra. What is $$a\land\neg a$$?
JSON expected answer: 0
-/
theorem ba_25_turn_14_oracle {α : Type} [BooleanAlgebra α] (x : α) : x ⊓ xᶜ = ⊥ := by
  simp

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary Boolean algebra, what is $$C(C(a))$$?
JSON expected answer: 0
-/
theorem ba_25_turn_15_oracle {α : Type} [BooleanAlgebra α] (x : α) : (x ⊓ xᶜ) ⊓ (x ⊓ xᶜ)ᶜ = ⊥ := by
  simp

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$a\land\neg a$$?
JSON expected answer: b
-/
theorem ba_25_turn_16_oracle {α : Type} (m : Model α) : C m m.a = m.b := by
  exact modifiedValue m
