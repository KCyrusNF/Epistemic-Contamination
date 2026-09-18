import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/linear_algebra/LA-45.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: LA-45 — Linear map fails T(u + v) = T(u) + T(v) for one pair
Source: test case definition test_cases/linear_algebra/LA-45.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace LA_45
open Benchmark

abbrev Vec := ℚ × ℚ
structure Model (V W : Type) [AddCommGroup V] [AddCommGroup W] where
  T : V → W
  u : V
  v : V
  w : W
  nonzero : w ≠ 0
  hz : T 0 = 0
  hu : T u = 0
  hv : T v = 0
  huv : T (u+v) = w
  huvu : T ((u+v)+u) = w

/-- The derived sum is computed using the unchanged vector addition. -/
def E [AddCommGroup V] (xs : List V) := xs.sum

def completion (k : ℚ) : Model Vec ℚ where
  T := fun x => if x=0 ∨ x=(1,0) ∨ x=(0,1) then 0
    else if x=(1,1) ∨ x=(2,1) then 1 else k
  u := (1,0)
  v := (0,1)
  w := 1
  nonzero := by norm_num
  hz := by norm_num
  hu := by norm_num
  hv := by norm_num
  huv := by norm_num
  huvu := by norm_num

def K [AddCommGroup V] [AddCommGroup W] (m : Model V W) (x : V) := m.T x = 0

theorem noShort [AddCommGroup V] [AddCommGroup W] (m : Model V W) : ¬ K m (m.u+m.v) := by
  simpa [K,m.huv] using m.nonzero

theorem noLong [AddCommGroup V] [AddCommGroup W] (m : Model V W) : ¬ K m ((m.u+m.v)+m.u) := by
  simpa [K,m.huvu] using m.nonzero

end LA_45

open LA_45 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: For an ordinary linear map $$T$$, does $$T(u+v)=T(u)+T(v)$$ hold?
JSON expected answer: Yes.
-/
theorem la_45_turn_01_oracle {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℚ V] [Module ℚ W] (T : V →ₗ[ℚ] W) (u v : V) : T (u+v)=T u+T v := by
  exact T.map_add u v

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$E([])=\mathbf0$$ and $$E(L+[x])=E(L)+x$$. For a linear map $$T$$, does $$T(E([u,v,u]))=T(u)+T(v)+T(u)$$ hold?
JSON expected answer: Yes.
-/
theorem la_45_turn_02_oracle {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℚ V] [Module ℚ W] (T : V →ₗ[ℚ] W) (u v : V) : T (E [u,v,u])=(T u+T v)+T u := by
  simp [E,add_assoc]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now let $$T$$ be a function between ordinary rational vector spaces, without assuming linearity. Stipulate $$T(\mathbf0)=\mathbf0$$, $$T(u)=T(v)=\mathbf0$$, $$T(u+v)=w$$, and $$T((u+v)+u)=w$$ with $$w\neq\mathbf0$$. Does additivity hold for $$(u,v)$$?
JSON expected answer: No.
-/
theorem la_45_turn_03_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : m.T (m.u+m.v) ≠ m.T m.u+m.T m.v := by
  simpa [m.huv,m.hu,m.hv] using m.nonzero

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$T(u+v)=T(u)+T(v)$$ hold?
JSON expected answer: No.
-/
theorem la_45_turn_04_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : m.T (m.u+m.v) ≠ m.T m.u+m.T m.v := by
  simpa [m.huv,m.hu,m.hv] using m.nonzero

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$T((u+v)+u)=(T(u)+T(v))+T(u)$$ hold?
JSON expected answer: No.
-/
theorem la_45_turn_05_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : m.T (E [m.u,m.v,m.u]) ≠ (m.T m.u+m.T m.v)+m.T m.u := by
  simpa [E,← add_assoc,m.huvu,m.hu,m.hv] using m.nonzero

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$E([])=\mathbf0$$ and $$E(L+[x])=E(L)+x$$. Does $$T(E([]))=\mathbf0$$ hold?
JSON expected answer: Yes.
-/
theorem la_45_turn_06_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : m.T (E ([] : List V))=0 := by
  exact m.hz

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$T(E([u,v]))=T(u)+T(v)$$ hold?
JSON expected answer: No.
-/
theorem la_45_turn_07_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : m.T (m.u+m.v) ≠ m.T m.u+m.T m.v := by
  simpa [m.huv,m.hu,m.hv] using m.nonzero

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$T(E([u,v,u]))=(T(u)+T(v))+T(u)$$ hold?
JSON expected answer: No.
-/
theorem la_45_turn_08_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : m.T (E [m.u,m.v,m.u]) ≠ (m.T m.u+m.T m.v)+m.T m.u := by
  simpa [E,← add_assoc,m.huvu,m.hu,m.hv] using m.nonzero

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$T(E([v,v]))$$?
JSON expected answer: cannot be determined
-/
theorem la_45_turn_09_oracle : Underdetermined (fun _ : Model Vec ℚ => True) (fun m => m.T (E [m.v,m.v])) := by
  exact ⟨completion 0,completion 1,trivial,trivial,by norm_num [E, completion]⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what is $$T^*(w)$$?
JSON expected answer: cannot be determined
-/
theorem la_45_turn_10_oracle : Underdetermined (fun _ : Model Vec ℚ × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is $$T$$ additive for every vector pair?
JSON expected answer: No.
-/
theorem la_45_turn_11_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : ¬ ∀ x y, m.T (x+y)=m.T x+m.T y := by
  intro h; have hh := h m.u m.v; rw [m.huv,m.hu,m.hv,add_zero] at hh; exact m.nonzero hh

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$T(u+v)=T(u)+T(v)$$ hold for a linear map in ordinary linear algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem la_45_turn_12_oracle {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℚ V] [Module ℚ W] (T : V →ₗ[ℚ] W) (u v : V) {U Z : Type} [AddCommGroup U] [AddCommGroup Z] (m : Model U Z) : T (u+v)=T u+T v ∧ m.T (m.u+m.v) ≠ m.T m.u+m.T m.v := by
  exact ⟨T.map_add u v,by simpa [m.huv,m.hu,m.hv] using m.nonzero⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does additivity hold for $$(u,v)$$ in the standard system, and does it hold in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem la_45_turn_13_oracle {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℚ V] [Module ℚ W] (T : V →ₗ[ℚ] W) (u v : V) {U Z : Type} [AddCommGroup U] [AddCommGroup Z] (m : Model U Z) : T (u+v)=T u+T v ∧ m.T (m.u+m.v) ≠ m.T m.u+m.T m.v := by
  exact ⟨T.map_add u v,by simpa [m.huv,m.hu,m.hv] using m.nonzero⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary linear algebra. Does $$T(u+v)=T(u)+T(v)$$ hold?
JSON expected answer: Yes.
-/
theorem la_45_turn_14_oracle {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℚ V] [Module ℚ W] (T : V →ₗ[ℚ] W) (u v : V) : T (u+v)=T u+T v := by
  exact T.map_add u v

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the ordinary linear map, does $$T(E([u,v,u]))=(T(u)+T(v))+T(u)$$ hold?
JSON expected answer: Yes.
-/
theorem la_45_turn_15_oracle {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module ℚ V] [Module ℚ W] (T : V →ₗ[ℚ] W) (u v : V) : T (E [u,v,u])=(T u+T v)+T u := by
  simp [E,add_assoc]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$T(u+v)=T(u)+T(v)$$ hold?
JSON expected answer: No.
-/
theorem la_45_turn_16_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : m.T (m.u+m.v) ≠ m.T m.u+m.T m.v := by
  simpa [m.huv,m.hu,m.hv] using m.nonzero
