import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/linear_algebra/LA-49.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: LA-49 — Kernel not closed under addition
Source: test case definition test_cases/linear_algebra/LA-49.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace LA_49
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

end LA_49

open LA_49 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: For an ordinary linear map $$T$$, is $$ker(T)$$ closed under vector addition?
JSON expected answer: Yes.
-/
theorem la_49_turn_01_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] (T : V →ₗ[𝕜] W) (u v : V) (hu : T u=0) (hv : T v=0) : T (u+v)=0 := by
  simp [hu,hv]

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: For an ordinary linear map define $$K(x)\iff T(x)=\mathbf0$$ and $$E([])=\mathbf0$$, $$E(L+[x])=E(L)+x$$. If $$K(u),K(v)$$, does $$K(E([u,v,u]))$$ hold?
JSON expected answer: Yes.
-/
theorem la_49_turn_02_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] (T : V →ₗ[𝕜] W) (u v : V) (hu : T u=0) (hv : T v=0) : T (E [u,v,u])=0 := by
  simp [E,hu,hv]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now let $$T$$ be a function between ordinary rational vector spaces, without linearity. Define $$ker(T)=\{x:T(x)=\mathbf0\}$$. Stipulate $$T(\mathbf0)=T(u)=T(v)=\mathbf0$$ and $$T(u+v)=T((u+v)+u)=w$$ with $$w\neq\mathbf0$$. Is $$u+v\in ker(T)$$?
JSON expected answer: No.
-/
theorem la_49_turn_03_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : ¬ K m (m.u+m.v) := by
  exact noShort m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does kernel closure under addition hold for $$(u,v)$$?
JSON expected answer: No.
-/
theorem la_49_turn_04_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : ¬ K m (m.u+m.v) := by
  exact noShort m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, is $$(u+v)+u\in ker(T)$$?
JSON expected answer: No.
-/
theorem la_49_turn_05_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : ¬ K m (E [m.u,m.v,m.u]) := by
  simpa [E,add_assoc] using noLong m

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$K(x)\iff T(x)=\mathbf0$$ and $$E([])=\mathbf0$$, $$E(L+[x])=E(L)+x$$. Does $$K(E([]))$$ hold?
JSON expected answer: Yes.
-/
theorem la_49_turn_06_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : m.T (E ([] : List V))=0 := by
  exact m.hz

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$K(E([u,v]))$$ hold?
JSON expected answer: No.
-/
theorem la_49_turn_07_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : ¬ K m (m.u+m.v) := by
  exact noShort m

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$K(E([u,v,u]))$$ hold?
JSON expected answer: No.
-/
theorem la_49_turn_08_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : ¬ K m (E [m.u,m.v,m.u]) := by
  simpa [E,add_assoc] using noLong m

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$K(2u)$$ hold?
JSON expected answer: cannot be determined
-/
theorem la_49_turn_09_oracle : Underdetermined (fun _ : Model Vec ℚ => True) (fun m => K m ((2:ℚ) • m.u)) := by
  refine ⟨completion 0,completion 1,trivial,trivial,?_⟩; intro h; have hh := h.mp (by norm_num [K,completion]); norm_num [K,completion] at hh

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$rank(T)$$?
JSON expected answer: cannot be determined
-/
theorem la_49_turn_10_oracle : Underdetermined (fun _ : Model Vec ℚ × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is the kernel guaranteed to be closed under vector addition?
JSON expected answer: No.
-/
theorem la_49_turn_11_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : ¬ ∀ x y, K m x → K m y → K m (x+y) := by
  intro h; exact noShort m (h m.u m.v m.hu m.hv)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does kernel closure under addition hold in ordinary linear algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem la_49_turn_12_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W]
    (T : V →ₗ[𝕜] W) {U Z : Type} [AddCommGroup U] [AddCommGroup Z] (m : Model U Z) :
    (∀ x y, T x=0 → T y=0 → T (x+y)=0) ∧
    ¬ (∀ x y, K m x → K m y → K m (x+y)) := by
  constructor
  · intro x y hx hy
    simp [hx,hy]
  · exact la_49_turn_11_oracle m

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: With $$T(u)=T(v)=\mathbf0$$ in each system, is $$u+v\in ker(T)$$ for an ordinary linear map in the standard system, and is it in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem la_49_turn_13_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] (T : V →ₗ[𝕜] W) (u v : V) (hu : T u=0) (hv : T v=0) {U Z : Type} [AddCommGroup U] [AddCommGroup Z] (m : Model U Z) : T (u+v)=0 ∧ ¬ K m (m.u+m.v) := by
  exact ⟨by simp [hu,hv],noShort m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary linear algebra. If $$T(u)=T(v)=\mathbf0$$ for a linear map, does $$T(u+v)=\mathbf0$$ follow?
JSON expected answer: Yes.
-/
theorem la_49_turn_14_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] (T : V →ₗ[𝕜] W) (u v : V) (hu : T u=0) (hv : T v=0) : T (u+v)=0 := by
  simp [hu,hv]

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the ordinary linear map with $$K(u),K(v)$$, does $$K(E([u,v,u]))$$ hold?
JSON expected answer: Yes.
-/
theorem la_49_turn_15_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] (T : V →ₗ[𝕜] W) (u v : V) (hu : T u=0) (hv : T v=0) : T (E [u,v,u])=0 := by
  simp [E,hu,hv]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$K(u+v)$$ hold?
JSON expected answer: No.
-/
theorem la_49_turn_16_oracle [AddCommGroup V] [AddCommGroup W] (m : Model V W) : ¬ K m (m.u+m.v) := by
  exact noShort m
