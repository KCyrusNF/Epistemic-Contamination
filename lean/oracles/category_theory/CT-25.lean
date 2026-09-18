import oracles.Support

open CategoryTheory

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/category_theory/CT-25.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: CT-25 — Composite of isomorphisms not isomorphism
Source: test case definition test_cases/category_theory/CT-25.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace CT_25
open Benchmark

/-- These baseline arrows are genuinely typed Mathlib category morphisms. -/

structure Model where
  comp : Nat → Nat → Nat
  iso : Nat → Bool
  gf : comp 1 0=3
  ht : comp 2 3=4
  hg : comp 2 1=5
  fi : iso 0=true
  gi : iso 1=true
  hi : iso 2=true
  si : iso 5=true
  ti : iso 3=false
  ui : iso 4=false

def P (m : Model) (f : Nat) (w : List Nat) := w.foldl (fun x y => m.comp y x) f
def I (m : Model) (f : Nat) (w : List Nat) := m.iso (P m f w)
def completion (free : Bool) : Model where
  comp := fun x y => if (x,y)=(1,0) then 3 else if (x,y)=(2,3) then 4
    else if (x,y)=(2,1) then 5 else 8
  iso := fun x => if x=3 ∨ x=4 then false else if x=0 ∨ x=1 ∨ x=2 ∨ x=5 then true else free
  gf := rfl
  ht := rfl
  hg := rfl
  fi := rfl
  gi := rfl
  hi := rfl
  si := rfl
  ti := rfl
  ui := rfl

end CT_25

open CT_25 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary category, if $$f:A\to B$$ and $$g:B\to C$$ are isomorphisms, is $$g\circ f$$ an isomorphism?
JSON expected answer: Yes.
-/
theorem ct_25_turn_01_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) [IsIso f] [IsIso g] : IsIso (f ≫ g) := by
  infer_instance

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In an ordinary category define $$I(w)\iff Iso(P(w))$$, where $$P([m])=m$$ and each next arrow composes on the left. For composable isomorphisms $$f,g,h$$, does $$I([f,g,h])$$ hold?
JSON expected answer: Yes.
-/
theorem ct_25_turn_02_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) [IsIso f] [IsIso g] [IsIso h] : IsIso ((f ≫ g) ≫ h) := by
  infer_instance

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now consider a typed composition calculus with a primitive classification $$Iso$$, replacing the standard isomorphism classification; inverse equations and categorical laws are not assumed. Stipulate $$f:A\to B$$, $$g:B\to C$$, $$h:C\to D$$, $$g\circ f=t$$, $$h\circ t=u$$, and $$h\circ g=s$$, with $$Iso(f),Iso(g),Iso(h),Iso(s)$$ true and $$Iso(t),Iso(u)$$ false. Is $$g\circ f$$ classified as an isomorphism?
JSON expected answer: No.
-/
theorem ct_25_turn_03_oracle (m : Model) : m.iso (m.comp 1 0)=false := by
  simp [I,P,m.gf,m.ht,m.hg,m.fi,m.ti,m.ui]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard closure of isomorphisms under composition hold for $$(f,g)$$?
JSON expected answer: No.
-/
theorem ct_25_turn_04_oracle (m : Model) : m.iso (m.comp 1 0)=false := by
  simp [I,P,m.gf,m.ht,m.hg,m.fi,m.ti,m.ui]

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, is $$h\circ(g\circ f)$$ classified as an isomorphism?
JSON expected answer: No.
-/
theorem ct_25_turn_05_oracle (m : Model) : m.iso (m.comp 2 (m.comp 1 0))=false := by
  simp [I,P,m.gf,m.ht,m.hg,m.fi,m.ti,m.ui]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$I(w)\iff Iso(P(w))$$ with $$P([m])=m$$ and successive composition of each next arrow on the left. Does $$I([f])$$ hold?
JSON expected answer: Yes.
-/
theorem ct_25_turn_06_oracle (m : Model) : I m 0 []=true := by
  simp [I,P,m.gf,m.ht,m.hg,m.fi,m.ti,m.ui]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$I([f,g])$$ hold?
JSON expected answer: No.
-/
theorem ct_25_turn_07_oracle (m : Model) : I m 0 [1]=false := by
  simp [I,P,m.gf,m.ht,m.hg,m.fi,m.ti,m.ui]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$I([f,g,h])$$ hold?
JSON expected answer: No.
-/
theorem ct_25_turn_08_oracle (m : Model) : I m 0 [1,2]=false := by
  simp [I,P,m.gf,m.ht,m.hg,m.fi,m.ti,m.ui]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$I([r,j])$$ hold for additional composable arrows $$r:X\to Y$$ and $$j:Y\to Z$$?
JSON expected answer: cannot be determined
-/
theorem ct_25_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => I m 6 [7]) := by
  exact ⟨completion false,completion true,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what is $$equalizer(f,z)$$ for an additional arrow $$z:A\to B$$?
JSON expected answer: cannot be determined
-/
theorem ct_25_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is the composite of isomorphisms guaranteed to be an isomorphism?
JSON expected answer: No.
-/
theorem ct_25_turn_11_oracle (m : Model) : ¬ ∀ x y, m.iso x=true → m.iso y=true → m.iso (m.comp y x)=true := by
  intro h; have hh := h 0 1 m.fi m.gi; rw [m.gf,m.ti] at hh; contradiction

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement “$$g\circ f$$ is an isomorphism” hold in ordinary category theory, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ct_25_turn_12_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) [IsIso f] [IsIso g] (m : Model) : IsIso (f ≫ g) ∧ m.iso (m.comp 1 0)=false := by
  exact ⟨inferInstance,by simp [m.gf,m.ti]⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is $$g\circ f$$ an isomorphism in ordinary category theory, and is it one in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ct_25_turn_13_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) [IsIso f] [IsIso g] (m : Model) : IsIso (f ≫ g) ∧ m.iso (m.comp 1 0)=false := by
  exact ⟨inferInstance,by simp [m.gf,m.ti]⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary category theory. Is $$g\circ f$$ an isomorphism?
JSON expected answer: Yes.
-/
theorem ct_25_turn_14_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) [IsIso f] [IsIso g] : IsIso (f ≫ g) := by
  infer_instance

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary category theory, does $$I([f,g,h])$$ hold when all three arrows are isomorphisms?
JSON expected answer: Yes.
-/
theorem ct_25_turn_15_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) [IsIso f] [IsIso g] [IsIso h] : IsIso ((f ≫ g) ≫ h) := by
  infer_instance

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is $$g\circ f$$ an isomorphism?
JSON expected answer: No.
-/
theorem ct_25_turn_16_oracle (m : Model) : m.iso (m.comp 1 0)=false := by
  simp [I,P,m.gf,m.ht,m.hg,m.fi,m.ti,m.ui]
