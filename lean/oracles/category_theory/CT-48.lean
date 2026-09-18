import oracles.Support

open CategoryTheory

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/category_theory/CT-48.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: CT-48 — Functor fails F(g ∘ f) = F(g) ∘ F(f) for one pair
Source: test case definition test_cases/category_theory/CT-48.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace CT_48
open Benchmark

/-- A typed, identity-preserving map; composition preservation is intentionally absent. -/
structure Map (C D : Type) [Category C] [Category D] where
  obj : C → D
  map : ∀ {X Y : C}, (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id : ∀ X, map (𝟙 X)=𝟙 (obj X)
structure Model (C D : Type) [Category C] [Category D] where
  F : Map C D
  A : C
  B : C
  E : C
  H : C
  X : C
  Y : C
  Z : C
  f : A ⟶ B
  g : B ⟶ E
  h : E ⟶ H
  r : X ⟶ Y
  s : Y ⟶ Z
  u : F.obj A ⟶ F.obj E
  v : F.obj A ⟶ F.obj E
  p : F.obj A ⟶ F.obj H
  q : F.obj A ⟶ F.obj H
  hfg : F.map (f ≫ g)=u
  hparts : F.map f ≫ F.map g=v
  uv : u≠v
  hlong : F.map ((f ≫ g) ≫ h)=u ≫ F.map h
  hp : u ≫ F.map h=p
  hq : v ≫ F.map h=q
  pq : p≠q

def Preserves [Category C] [Category D] (F : Map C D) {A B E : C}
    (f : A ⟶ B) (g : B ⟶ E) := F.map (f ≫ g)=F.map f ≫ F.map g

theorem noShort [Category C] [Category D] (m : Model C D) : ¬ Preserves m.F m.f m.g := by
  unfold Preserves
  rw [m.hfg,m.hparts]
  exact m.uv

theorem noLong [Category C] [Category D] (m : Model C D) :
    m.F.map ((m.f ≫ m.g) ≫ m.h) ≠ (m.F.map m.f ≫ m.F.map m.g) ≫ m.F.map m.h := by
  rw [m.hlong,m.hparts,m.hp,m.hq]
  exact m.pq

inductive One | star
/-- Addition gives a genuine one-object category, including all category laws. -/
instance : Category One where
  Hom _ _ := Nat
  id _ := 0
  comp f g := f+g
  id_comp := by intros; simp
  comp_id := by intros; simp
  assoc := by intros; simp [Nat.add_assoc]

def numberMap (k : Nat) (n : Nat) :=
  if n=0 then 0 else if n=1 then 1 else if n=2 then 3 else if n=3 then 4 else if n=8 then k else 0

def completion (k : Nat) : Model One One where
  F := { obj := id, map := fun n => numberMap k n, map_id := by intro X; rfl }
  A := .star
  B := .star
  E := .star
  H := .star
  X := .star
  Y := .star
  Z := .star
  f := (1 : Nat)
  g := (1 : Nat)
  h := (1 : Nat)
  r := (4 : Nat)
  s := (4 : Nat)
  u := (3 : Nat)
  v := (2 : Nat)
  p := (4 : Nat)
  q := (3 : Nat)
  hfg := rfl
  hparts := rfl
  uv := by exact (by decide : (3 : Nat) ≠ 2)
  hlong := rfl
  hp := rfl
  hq := rfl
  pq := by exact (by decide : (4 : Nat) ≠ 3)

end CT_48

open CT_48 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: For an ordinary functor $$F$$ and arrows $$f:A\to B$$ and $$g:B\to C$$, does $$F(g\circ f)=F(g)\circ F(f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_48_turn_01_oracle {C D : Type} [Category C] [Category D] (F : C ⥤ D) {A B E H : C} (f : A ⟶ B) (g : B ⟶ E) (h : E ⟶ H) : F.map (f ≫ g)=F.map f ≫ F.map g := by
  exact F.map_comp f g

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: For an ordinary functor and a further arrow $$h:C\to D$$, define $$C(f,g)\iff F(g\circ f)=F(g)\circ F(f)$$. Does $$F(h\circ(g\circ f))=F(h)\circ(F(g)\circ F(f))$$ hold?
JSON expected answer: Yes.
-/
theorem ct_48_turn_02_oracle {C D : Type} [Category C] [Category D] (F : C ⥤ D) {A B E H : C} (f : A ⟶ B) (g : B ⟶ E) (h : E ⟶ H) : F.map ((f ≫ g) ≫ h)=(F.map f ≫ F.map g) ≫ F.map h := by
  simp only [F.map_comp]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a map between categories with the usual arrow typing, identities, and associative composition, but without the functor composition-preservation axiom. Stipulate $$F(g\circ f)=u$$ and $$F(g)\circ F(f)=v$$ with $$u\neq v$$; also $$F(h\circ(g\circ f))=F(h)\circ u$$, $$F(h)\circ u=p$$, and $$F(h)\circ v=q$$ with $$p\neq q$$. The map preserves identities. Does composition preservation hold for $$(f,g)$$?
JSON expected answer: No.
-/
theorem ct_48_turn_03_oracle [Category C] [Category D] (m : Model C D) : ¬ Preserves m.F m.f m.g := by
  exact noShort m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$F(g\circ f)=F(g)\circ F(f)$$ hold?
JSON expected answer: No.
-/
theorem ct_48_turn_04_oracle [Category C] [Category D] (m : Model C D) : ¬ Preserves m.F m.f m.g := by
  exact noShort m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$F(h\circ(g\circ f))=F(h)\circ(F(g)\circ F(f))$$ hold?
JSON expected answer: No.
-/
theorem ct_48_turn_05_oracle [Category C] [Category D] (m : Model C D) : m.F.map ((m.f ≫ m.g) ≫ m.h) ≠ (m.F.map m.f ≫ m.F.map m.g) ≫ m.F.map m.h := by
  exact noLong m

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$C(f,g)\iff F(g\circ f)=F(g)\circ F(f)$$. Does $$C(id_A,f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_48_turn_06_oracle [Category C] [Category D] (m : Model C D) : Preserves m.F (𝟙 m.A) m.f := by
  simp [Preserves,m.F.map_id]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$C(f,g)$$ hold?
JSON expected answer: No.
-/
theorem ct_48_turn_07_oracle [Category C] [Category D] (m : Model C D) : ¬ Preserves m.F m.f m.g := by
  exact noShort m

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$F(h\circ(g\circ f))=F(h)\circ(F(g)\circ F(f))$$ hold?
JSON expected answer: No.
-/
theorem ct_48_turn_08_oracle [Category C] [Category D] (m : Model C D) : m.F.map ((m.f ≫ m.g) ≫ m.h) ≠ (m.F.map m.f ≫ m.F.map m.g) ≫ m.F.map m.h := by
  exact noLong m

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$C(r,s)$$ hold for another composable pair $$r:X\to Y$$ and $$s:Y\to Z$$?
JSON expected answer: cannot be determined
-/
theorem ct_48_turn_09_oracle : Underdetermined (fun _ : Model One One => True) (fun m => Preserves m.F m.r m.s) := by
  refine ⟨completion 0,completion 1,trivial,trivial,?_⟩
  intro h
  have yes : Preserves (completion 0).F (completion 0).r (completion 0).s := by rfl
  have bad := h.mp yes
  change (1 : Nat) = 0 at bad
  omega

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$Nat(F,F)$$?
JSON expected answer: cannot be determined
-/
theorem ct_48_turn_10_oracle : Underdetermined (fun _ : Model One One × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is composition preservation guaranteed for every composable pair?
JSON expected answer: No.
-/
theorem ct_48_turn_11_oracle [Category C] [Category D] (m : Model C D) : ¬ ∀ (A B E : C) (f : A ⟶ B) (g : B ⟶ E), Preserves m.F f g := by
  intro h; exact noShort m (h m.A m.B m.E m.f m.g)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$F(g\circ f)=F(g)\circ F(f)$$ hold for a functor in ordinary category theory, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ct_48_turn_12_oracle {C D : Type} [Category C] [Category D] (F : C ⥤ D) {A B E H : C} (f : A ⟶ B) (g : B ⟶ E) (h : E ⟶ H) {U V : Type} [Category U] [Category V] (m : Model U V) : F.map (f ≫ g)=F.map f ≫ F.map g ∧ ¬ Preserves m.F m.f m.g := by
  exact ⟨F.map_comp f g,noShort m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does composition preservation hold for $$(f,g)$$ in ordinary category theory, and does it hold in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ct_48_turn_13_oracle {C D : Type} [Category C] [Category D] (F : C ⥤ D) {A B E H : C} (f : A ⟶ B) (g : B ⟶ E) (h : E ⟶ H) {U V : Type} [Category U] [Category V] (m : Model U V) : F.map (f ≫ g)=F.map f ≫ F.map g ∧ ¬ Preserves m.F m.f m.g := by
  exact ⟨F.map_comp f g,noShort m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary category theory. Does $$F(g\circ f)=F(g)\circ F(f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_48_turn_14_oracle {C D : Type} [Category C] [Category D] (F : C ⥤ D) {A B E H : C} (f : A ⟶ B) (g : B ⟶ E) (h : E ⟶ H) : F.map (f ≫ g)=F.map f ≫ F.map g := by
  exact F.map_comp f g

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary category theory, does $$F(h\circ g\circ f)=F(h)\circ F(g)\circ F(f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_48_turn_15_oracle {C D : Type} [Category C] [Category D] (F : C ⥤ D) {A B E H : C} (f : A ⟶ B) (g : B ⟶ E) (h : E ⟶ H) : F.map ((f ≫ g) ≫ h)=(F.map f ≫ F.map g) ≫ F.map h := by
  simp only [F.map_comp]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does composition preservation hold for $$(f,g)$$?
JSON expected answer: No.
-/
theorem ct_48_turn_16_oracle [Category C] [Category D] (m : Model C D) : ¬ Preserves m.F m.f m.g := by
  exact noShort m
