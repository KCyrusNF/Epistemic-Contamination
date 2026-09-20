import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/linear_algebra/LA-33.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: LA-33 — Span not closed under vector addition
Source: test case definition test_cases/linear_algebra/LA-33.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace LA_33
open Benchmark

abbrev Vec := ℚ × ℚ
structure Model (V : Type) [AddCommGroup V] where
  members : Set V
  u : V
  v : V
  hz : 0 ∈ members
  hu : u ∈ members
  hv : v ∈ members
  huv : u+v ∉ members
  huvu : (u+v)+u ∉ members

def E [AddCommGroup V] (xs : List V) := xs.sum

def completion (extra : Bool) : Model Vec where
  members := {x | x=0 ∨ x=(1,0) ∨ x=(0,1) ∨ (extra=true ∧ x=(0,2))}
  u := (1,0)
  v := (0,1)
  hz := by simp
  hu := by simp
  hv := by simp
  huv := by norm_num
  huvu := by norm_num

end LA_33

open LA_33 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In ordinary linear algebra, is $$span(S)$$ closed under vector addition?
JSON expected answer: Yes.
-/
theorem la_33_turn_01_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (S : Set V) (u v : V) (hu : u ∈ Submodule.span 𝕜 S) (hv : v ∈ Submodule.span 𝕜 S) : u+v ∈ Submodule.span 𝕜 S := by
  exact (Submodule.span 𝕜 S).add_mem hu hv

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$M(x)\iff x\in span(S)$$ and $$Sum([])=\mathbf0$$, $$Sum(L+[x])=Sum(L)+x$$. If $$u,v\in span(S)$$, does $$M(Sum([u,v,u]))$$ hold?
JSON expected answer: Yes.
-/
theorem la_33_turn_02_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (S : Set V) (u v : V) (hu : u ∈ Submodule.span 𝕜 S) (hv : v ∈ Submodule.span 𝕜 S) : E [u,v,u] ∈ Submodule.span 𝕜 S := by
  simpa [E,add_assoc] using (Submodule.span 𝕜 S).add_mem ((Submodule.span 𝕜 S).add_mem hu hv) hu

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now retain ordinary rational vector arithmetic but interpret $$span(S)$$ as a designated subset, without requiring it to be the ordinary linear span. Stipulate $$\mathbf0,u,v\in span(S)$$, $$u+v\notin span(S)$$, and $$(u+v)+u\notin span(S)$$. Is $$u+v\in span(S)$$?
JSON expected answer: No.
-/
theorem la_33_turn_03_oracle [AddCommGroup V] (m : Model V) : m.u+m.v ∉ m.members := by
  exact m.huv

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard addition-closure property hold for $$(u,v)$$?
JSON expected answer: No.
-/
theorem la_33_turn_04_oracle [AddCommGroup V] (m : Model V) : m.u+m.v ∉ m.members := by
  exact m.huv

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, is $$(u+v)+u\in span(S)$$?
JSON expected answer: No.
-/
theorem la_33_turn_05_oracle [AddCommGroup V] (m : Model V) : E [m.u,m.v,m.u] ∉ m.members := by
  simpa [E,add_assoc] using m.huvu

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$M(x)\iff x\in span(S)$$ and $$Sum([])=\mathbf0$$, $$Sum(L+[x])=Sum(L)+x$$. Does $$M(Sum([]))$$ hold?
JSON expected answer: Yes.
-/
theorem la_33_turn_06_oracle [AddCommGroup V] (m : Model V) : E ([] : List V) ∈ m.members := by
  exact m.hz

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$M(Sum([u,v]))$$ hold?
JSON expected answer: No.
-/
theorem la_33_turn_07_oracle [AddCommGroup V] (m : Model V) : E [m.u,m.v] ∉ m.members := by
  simpa [E] using m.huv

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$M(Sum([u,v,u]))$$ hold?
JSON expected answer: No.
-/
theorem la_33_turn_08_oracle [AddCommGroup V] (m : Model V) : E [m.u,m.v,m.u] ∉ m.members := by
  simpa [E,add_assoc] using m.huvu

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$M(Sum([v,v]))$$ hold?
JSON expected answer: cannot be determined
-/
theorem la_33_turn_09_oracle : Underdetermined (fun _ : Model Vec => True) (fun m => E [m.v,m.v] ∈ m.members) := by
  refine ⟨completion false,completion true,trivial,trivial,?_⟩; intro h; have hh := h.mpr (by norm_num [E,completion]); norm_num [E,completion] at hh

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$dim(span(S))$$?
JSON expected answer: cannot be determined
-/
theorem la_33_turn_10_oracle : Underdetermined (fun _ : Model Vec × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is $$span(S)$$ guaranteed to be closed under vector addition?
JSON expected answer: No.
-/
theorem la_33_turn_11_oracle [AddCommGroup V] (m : Model V) : ¬ ∀ x ∈ m.members, ∀ y ∈ m.members, x+y ∈ m.members := by
  intro h; exact m.huv (h m.u m.hu m.v m.hv)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does addition-closure of $$span(S)$$ hold in ordinary linear algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem la_33_turn_12_oracle {𝕜 V U : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U]
    (S : Set V) (m : Model U) :
    (∀ x ∈ Submodule.span 𝕜 S, ∀ y ∈ Submodule.span 𝕜 S, x+y ∈ Submodule.span 𝕜 S) ∧
    ¬ (∀ x ∈ m.members, ∀ y ∈ m.members, x+y ∈ m.members) := by
  exact ⟨fun _ hx _ hy => (Submodule.span 𝕜 S).add_mem hx hy,la_33_turn_11_oracle m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: With $$u,v\in span(S)$$ in each system, is $$u+v\in span(S)$$ in the standard system, and is it in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem la_33_turn_13_oracle {𝕜 V U : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] (S : Set V) (u v : V) (hu : u ∈ Submodule.span 𝕜 S) (hv : v ∈ Submodule.span 𝕜 S) (m : Model U) : u+v ∈ Submodule.span 𝕜 S ∧ m.u+m.v ∉ m.members := by
  exact ⟨(Submodule.span 𝕜 S).add_mem hu hv,m.huv⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary linear algebra. If $$u,v\in span(S)$$, is $$u+v\in span(S)$$?
JSON expected answer: Yes.
-/
theorem la_33_turn_14_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (S : Set V) (u v : V) (hu : u ∈ Submodule.span 𝕜 S) (hv : v ∈ Submodule.span 𝕜 S) : u+v ∈ Submodule.span 𝕜 S := by
  exact (Submodule.span 𝕜 S).add_mem hu hv

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the ordinary span and $$u,v\in span(S)$$, does $$M(Sum([u,v,u]))$$ hold?
JSON expected answer: Yes.
-/
theorem la_33_turn_15_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (S : Set V) (u v : V) (hu : u ∈ Submodule.span 𝕜 S) (hv : v ∈ Submodule.span 𝕜 S) : E [u,v,u] ∈ Submodule.span 𝕜 S := by
  simpa [E,add_assoc] using (Submodule.span 𝕜 S).add_mem ((Submodule.span 𝕜 S).add_mem hu hv) hu

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$M(u+v)$$ hold?
JSON expected answer: No.
-/
theorem la_33_turn_16_oracle [AddCommGroup V] (m : Model V) : m.u+m.v ∉ m.members := by
  exact m.huv
