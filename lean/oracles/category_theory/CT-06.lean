import oracles.Support

open CategoryTheory

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/category_theory/CT-06.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: CT-06 — Composition undefined for one composable pair
Source: test case definition test_cases/category_theory/CT-06.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace CT_06
open Benchmark

/-- These baseline arrows are genuinely typed Mathlib category morphisms. -/

structure Model where
  comp : Nat → Nat → Option Nat
  gf : comp 1 0=none
  hg : comp 2 1=some 3
  mf : comp 3 0=none

def P (m : Model) (f : Nat) : List Nat → Option Nat
  | [] => some f
  | g::gs => (m.comp g f).bind (fun t => P m t gs)

def completion (free : Option Nat) : Model where
  comp := fun x y => if (x,y)=(1,0) then none else if (x,y)=(2,1) then some 3
    else if (x,y)=(3,0) then none else free
  gf := rfl
  hg := rfl
  mf := rfl

end CT_06

open CT_06 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary category, if $$f:A\to B$$ and $$g:B\to C$$, is the composite $$g\circ f$$ defined?
JSON expected answer: Yes.
-/
theorem ct_06_turn_01_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) : (∃ k : A ⟶ D, k = f ≫ g) := by
  exact ⟨f ≫ g,rfl⟩

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In an ordinary category with $$h:C\to D$$, define $$P([f])=f$$ and evaluate longer paths by successively composing the next arrow on the left of the accumulated value. Is $$P([f,g,h])$$ defined?
JSON expected answer: Yes.
-/
theorem ct_06_turn_02_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : (∃ k : A ⟶ E, k = (f ≫ g) ≫ h) := by
  exact ⟨(f ≫ g) ≫ h,rfl⟩

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now consider arrows with the same sources and targets and a partial composition operation; source-target compatibility does not guarantee a value. Stipulate that $$g\circ f$$ is undefined, $$h\circ g=m$$ is defined, and $$m\circ f$$ is undefined. Is $$g\circ f$$ defined?
JSON expected answer: No.
-/
theorem ct_06_turn_03_oracle (m : Model) : m.comp 1 0=none := by
  exact m.gf

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard composition-existence rule produce a composite for $$(f,g)$$?
JSON expected answer: No.
-/
theorem ct_06_turn_04_oracle (m : Model) : m.comp 1 0=none := by
  exact m.gf

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, is $$(h\circ g)\circ f$$ defined?
JSON expected answer: No.
-/
theorem ct_06_turn_05_oracle (m : Model) : (m.comp 2 1).bind (fun t => m.comp t 0)=none := by
  simp [m.hg,m.mf]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct path evaluation: $$P([f])=f$$; each next arrow is composed on the left of the accumulated value, and an undefined step makes the whole path undefined. What is $$P([f])$$?
JSON expected answer: f
-/
theorem ct_06_turn_06_oracle (m : Model) : P m 0 []=some 0 := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, is the two-morphism path $$[f,g]$$ defined?
JSON expected answer: No.
-/
theorem ct_06_turn_07_oracle (m : Model) : P m 0 [1]=none := by
  simp [P,m.gf]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, is the path $$[f,g,h]$$ defined?
JSON expected answer: No.
-/
theorem ct_06_turn_08_oracle (m : Model) : P m 0 [1,2]=none := by
  simp [P,m.gf]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, is $$P([r,s])$$ defined for additional arrows $$r:X\to Y$$ and $$s:Y\to Z$$?
JSON expected answer: cannot be determined
-/
theorem ct_06_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => (P m 4 [5]).isSome) := by
  exact ⟨completion none,completion (some 0),trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$f\otimes g$$?
JSON expected answer: cannot be determined
-/
theorem ct_06_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion none,0),(completion none,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can a source-target-compatible pair nevertheless lack a composite?
JSON expected answer: Yes.
-/
theorem ct_06_turn_11_oracle (m : Model) : ∃ x y, m.comp y x=none := by
  exact ⟨0,1,m.gf⟩

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement “$$g\circ f$$ is defined” hold in ordinary category theory, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ct_06_turn_12_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (m : Model) : (∃ k : A ⟶ D, k = f ≫ g) ∧ m.comp 1 0=none := by
  exact ⟨⟨f ≫ g,rfl⟩,m.gf⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is $$g\circ f$$ defined in ordinary category theory, and is it defined in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ct_06_turn_13_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (m : Model) : (∃ k : A ⟶ D, k = f ≫ g) ∧ m.comp 1 0=none := by
  exact ⟨⟨f ≫ g,rfl⟩,m.gf⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary category theory. Is $$g\circ f$$ defined?
JSON expected answer: Yes.
-/
theorem ct_06_turn_14_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) : (∃ k : A ⟶ D, k = f ≫ g) := by
  exact ⟨f ≫ g,rfl⟩

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary category theory, is $$P([f,g,h])$$ defined?
JSON expected answer: Yes.
-/
theorem ct_06_turn_15_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : (∃ k : A ⟶ E, k = (f ≫ g) ≫ h) := by
  exact ⟨(f ≫ g) ≫ h,rfl⟩

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is $$g\circ f$$ defined?
JSON expected answer: No.
-/
theorem ct_06_turn_16_oracle (m : Model) : m.comp 1 0=none := by
  exact m.gf
