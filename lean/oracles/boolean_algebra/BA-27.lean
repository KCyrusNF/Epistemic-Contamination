import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/boolean_algebra/BA-27.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: BA-27 — Double complement does not return original element
Source: test case definition test_cases/boolean_algebra/BA-27.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace BA_27
open Benchmark
variable {α : Type}
structure Model (α : Type) where
  neg : α → α
  a : α
  b : α
  c : α
  d : α
  e : α
  distinct : [a,b,c,d,e].Nodup
  ha : neg a = c
  hc : neg c = b
  hb : neg b = d
  hd : neg d = b
def D (m : Model α) (x : α) := m.neg (m.neg x)
def completion (k : Fin 5) : Model (Fin 5) where
  neg := fun x => if x=0 then 2 else if x=2 then 1 else if x=1 then 3 else if x=3 then 1 else k
  a := 0
  b := 1
  c := 2
  d := 3
  e := 4
  distinct := by decide
  ha := by norm_num
  hc := by norm_num
  hb := by norm_num
  hd := by norm_num

theorem modifiedValue (m : Model α) : D m m.a = m.b := by simp [D, m.ha, m.hc]
theorem modifiedDifferent (m : Model α) : D m m.a ≠ m.a := by
  rw [modifiedValue m]
  exact by
    have h := m.distinct
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h
    exact Ne.symm h.1.1

end BA_27

open BA_27 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary Boolean algebra, does double complementation give $$\neg\neg a=a$$?
JSON expected answer: Yes.
-/
theorem ba_27_turn_01_oracle {α : Type} [BooleanAlgebra α] (x : α) : xᶜᶜ = x := by
  simp

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system, define $$D(x)=\neg\neg x$$. Is $$D(D(a))=a$$?
JSON expected answer: Yes.
-/
theorem ba_27_turn_02_oracle {α : Type} [BooleanAlgebra α] (x : α) : xᶜᶜᶜᶜ = x := by
  simp

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a carrier with total negation and distinct elements $$a,b,c,d,e$$. Stipulate $$\neg a=c$$, $$\neg c=b$$, $$\neg b=d$$, and $$\neg d=b$$; other values are unconstrained. What is $$\neg\neg a$$?
JSON expected answer: b
-/
theorem ba_27_turn_03_oracle {α : Type} (m : Model α) : D m m.a = m.b := by
  exact modifiedValue m


/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$\neg\neg a=a$$ hold?
JSON expected answer: No.
-/
theorem ba_27_turn_04_oracle {α : Type} (m : Model α) : D m m.a ≠ m.a := by
  exact modifiedDifferent m


/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, what is $$\neg\neg\neg a$$?
JSON expected answer: d
-/
theorem ba_27_turn_05_oracle {α : Type} (m : Model α) : m.neg (m.neg (m.neg m.a)) = m.d := by
  rw [m.ha, m.hc, m.hb]


/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$D(x)=\neg\neg x$$. What is $$D(b)$$?
JSON expected answer: b
-/
theorem ba_27_turn_06_oracle {α : Type} (m : Model α) : D m m.b = m.b := by
  simp [D, m.hb, m.hd]


/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$D(a)$$?
JSON expected answer: b
-/
theorem ba_27_turn_07_oracle {α : Type} (m : Model α) : D m m.a = m.b := by
  exact modifiedValue m


/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$D(D(a))$$?
JSON expected answer: b
-/
theorem ba_27_turn_08_oracle {α : Type} (m : Model α) : D m (D m m.a) = m.b := by
  rw [modifiedValue m]
  exact ba_27_turn_06_oracle m


/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$D(e)$$?
JSON expected answer: cannot be determined
-/
theorem ba_27_turn_09_oracle : Underdetermined (fun _ : Model (Fin 5) => True) (fun m => D m m.e) := by
  exact ⟨completion 0,completion 1,True.intro,True.intro,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$a\rightarrow b$$?
JSON expected answer: cannot be determined
-/
theorem ba_27_turn_10_oracle : Underdetermined (fun _ : Model (Fin 5) × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is double complementation guaranteed to return the original element?
JSON expected answer: No.
-/
theorem ba_27_turn_11_oracle {α : Type} (m : Model α) : ¬ (∀ x, D m x = x) := by
  intro h
  exact modifiedDifferent m (h m.a)


/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$\neg\neg a=a$$ hold in ordinary Boolean algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ba_27_turn_12_oracle {α β : Type} [BooleanAlgebra α] (x : α) (m : Model β) : (xᶜᶜ = x) ∧ (D m m.a = m.b ∧ D m m.a ≠ m.a) := by
  exact ⟨by simp, modifiedValue m, modifiedDifferent m⟩


/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$\neg\neg a$$ in ordinary Boolean algebra, and what is it in the modified system?
JSON expected answer: a in the standard system and b in the modified system.
-/
theorem ba_27_turn_13_oracle {α β : Type} [BooleanAlgebra α] (x : α) (m : Model β) : (xᶜᶜ = x) ∧ (D m m.a = m.b ∧ D m m.a ≠ m.a) := by
  exact ⟨by simp, modifiedValue m, modifiedDifferent m⟩


/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary Boolean algebra. Does $$\neg\neg a=a$$ hold?
JSON expected answer: Yes.
-/
theorem ba_27_turn_14_oracle {α : Type} [BooleanAlgebra α] (x : α) : xᶜᶜ = x := by
  simp

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary Boolean algebra, is $$D(D(a))=a$$?
JSON expected answer: Yes.
-/
theorem ba_27_turn_15_oracle {α : Type} [BooleanAlgebra α] (x : α) : xᶜᶜᶜᶜ = x := by
  simp

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$\neg\neg a$$?
JSON expected answer: b
-/
theorem ba_27_turn_16_oracle {α : Type} (m : Model α) : D m m.a = m.b := by
  exact modifiedValue m
