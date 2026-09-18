import oracles.Support

open CategoryTheory

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/category_theory/CT-09.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: CT-09 — Composite morphism lands in wrong codomain for one pair
Source: test case definition test_cases/category_theory/CT-09.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace CT_09
open Benchmark

/-- These baseline arrows are genuinely typed Mathlib category morphisms. -/

structure Arrow where
  source : Nat
  target : Nat
  label : Nat
  deriving DecidableEq
structure Model where
  comp : Arrow → Arrow → Arrow
  f : Arrow
  g : Arrow
  h : Arrow
  r : Arrow
  t : Arrow
  u : Arrow
  fb : f.target=1
  gc : g.target=2
  td : t.target=3
  ue : u.target=4
  gf : comp g f=t
  ht : comp h t=u

def P (m : Model) (f : Arrow) (w : List Arrow) := w.foldl (fun x y => m.comp y x) f
def K (m : Model) (f : Arrow) (w : List Arrow) := (P m f w).target

def completion (free : Nat) : Model where
  comp := fun x y => if x.label=1 ∧ y.label=0 then ⟨0,3,4⟩
    else if x.label=2 ∧ y.label=4 then ⟨0,4,5⟩ else ⟨0,free,6⟩
  f := ⟨0,1,0⟩
  g := ⟨1,2,1⟩
  h := ⟨3,4,2⟩
  r := ⟨1,5,3⟩
  t := ⟨0,3,4⟩
  u := ⟨0,4,5⟩
  fb := rfl
  gc := rfl
  td := rfl
  ue := rfl
  gf := rfl
  ht := rfl

def cod {C : Type} [Category C] {A B : C} (_ : A ⟶ B) := B

end CT_09

open CT_09 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary category, if $$f:A\to B$$ and $$g:B\to C$$, what is the codomain of $$g\circ f$$?
JSON expected answer: C
-/
theorem ct_09_turn_01_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) : cod (f ≫ g)=D := by
  rfl

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In an ordinary category, let $$h:C\to D$$. Define $$K([f])=cod(f)$$ and $$K([f,g,\ldots])=cod(P([f,g,\ldots]))$$, where $$P$$ successively composes each next arrow on the left. What is $$K([f,g,h])$$?
JSON expected answer: D
-/
theorem ct_09_turn_02_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : cod ((f ≫ g) ≫ h)=E := by
  rfl

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use an untyped set of arrow records with source and codomain fields, and a total composition operation on records whose source-target behavior is constrained only by the supplied equations. Keep $$f:A\to B$$ and $$g:B\to C$$, but stipulate $$g\circ f=t:A\to D$$ with $$D\neq C$$. Also let $$h:D\to E$$ and stipulate $$h\circ t=u:A\to E$$. What is $$cod(g\circ f)$$?
JSON expected answer: D
-/
theorem ct_09_turn_03_oracle (m : Model) : (m.comp m.g m.f).target=3 := by
  simp [K,P,m.gf,m.ht,m.fb,m.td,m.ue,m.gc]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$g\circ f$$ have codomain $$C$$?
JSON expected answer: No.
-/
theorem ct_09_turn_04_oracle (m : Model) : (m.comp m.g m.f).target≠2 := by
  simp [K,P,m.gf,m.ht,m.fb,m.td,m.ue,m.gc]

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, suppose $$h:D\to E$$. What is the codomain of $$h\circ(g\circ f)$$?
JSON expected answer: E
-/
theorem ct_09_turn_05_oracle (m : Model) : (m.comp m.h (m.comp m.g m.f)).target=4 := by
  simp [K,P,m.gf,m.ht,m.fb,m.td,m.ue,m.gc]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$K(w)=cod(P(w))$$ for nonempty paths, with $$P([f])=f$$ and successive composition of each next arrow on the left. What is $$K([f])$$?
JSON expected answer: B
-/
theorem ct_09_turn_06_oracle (m : Model) : K m m.f []=1 := by
  simp [K,P,m.gf,m.ht,m.fb,m.td,m.ue,m.gc]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$K([f,g])$$?
JSON expected answer: D
-/
theorem ct_09_turn_07_oracle (m : Model) : K m m.f [m.g]=3 := by
  simp [K,P,m.gf,m.ht,m.fb,m.td,m.ue,m.gc]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$K([f,g,h])$$ given $$h:D\to E$$?
JSON expected answer: E
-/
theorem ct_09_turn_08_oracle (m : Model) : K m m.f [m.g,m.h]=4 := by
  simp [K,P,m.gf,m.ht,m.fb,m.td,m.ue,m.gc]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$K([f,r])$$ for another arrow $$r:B\to X$$?
JSON expected answer: cannot be determined
-/
theorem ct_09_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => K m m.f [m.r]) := by
  exact ⟨completion 0,completion 1,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$kernel(f)$$?
JSON expected answer: cannot be determined
-/
theorem ct_09_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can the codomain of a composite differ from the codomain of the second morphism?
JSON expected answer: Yes.
-/
theorem ct_09_turn_11_oracle (m : Model) : (m.comp m.g m.f).target≠m.g.target := by
  simp [K,P,m.gf,m.ht,m.fb,m.td,m.ue,m.gc]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement $$cod(g\circ f)=C$$ hold in ordinary category theory, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ct_09_turn_12_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (m : Model) : cod (f ≫ g)=D ∧ (m.comp m.g m.f).target=3 ∧ (m.comp m.g m.f).target≠m.g.target := by
  exact ⟨rfl,by simp [m.gf,m.td],by simp [m.gf,m.td,m.gc]⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$cod(g\circ f)$$ in ordinary category theory, and what is it in the modified system?
JSON expected answer: C in the standard system and D in the modified system.
-/
theorem ct_09_turn_13_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (m : Model) : cod (f ≫ g)=D ∧ (m.comp m.g m.f).target=3 ∧ (m.comp m.g m.f).target≠m.g.target := by
  exact ⟨rfl,by simp [m.gf,m.td],by simp [m.gf,m.td,m.gc]⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary category theory. What is $$cod(g\circ f)$$?
JSON expected answer: C
-/
theorem ct_09_turn_14_oracle {C : Type} [Category C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D) : cod (f ≫ g)=D := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard category and its arrow $$h:C\to D$$, what is $$K([f,g,h])$$?
JSON expected answer: D
-/
theorem ct_09_turn_15_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : cod ((f ≫ g) ≫ h)=E := by
  rfl

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$cod(g\circ f)$$?
JSON expected answer: D
-/
theorem ct_09_turn_16_oracle (m : Model) : (m.comp m.g m.f).target=3 := by
  simp [K,P,m.gf,m.ht,m.fb,m.td,m.ue,m.gc]
