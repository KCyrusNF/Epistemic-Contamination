import oracles.Support

open CategoryTheory

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/category_theory/CT-52.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: CT-52 — Naturality fails for one morphism
Source: test case definition test_cases/category_theory/CT-52.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace CT_52
open Benchmark

structure Model (C D : Type) [Category C] [Category D] where
  F : C ⥤ D
  G : C ⥤ D
  eta : ∀ X, F.obj X ⟶ G.obj X
  A : C
  B : C
  E : C
  X : C
  Y : C
  f : A ⟶ B
  g : B ⟶ E
  j : X ⟶ Y
  p : F.obj A ⟶ G.obj B
  q : F.obj A ⟶ G.obj B
  r : F.obj A ⟶ G.obj E
  s : F.obj A ⟶ G.obj E
  hp : eta A ≫ G.map f=p
  hq : F.map f ≫ eta B=q
  pq : p≠q
  hg : eta B ≫ G.map g=F.map g ≫ eta E
  hr : p ≫ G.map g=r
  hs : q ≫ G.map g=s
  rs : r≠s

def N [Category C] [Category D] (m : Model C D) {A B : C} (f : A ⟶ B) :=
  m.eta A ≫ m.G.map f=m.F.map f ≫ m.eta B

theorem noShort [Category C] [Category D] (m : Model C D) : ¬ N m m.f := by
  unfold N
  rw [m.hp,m.hq]
  exact m.pq

theorem noComposite [Category C] [Category D] (m : Model C D) : ¬ N m (m.f ≫ m.g) := by
  intro h
  have lhs : m.eta m.A ≫ m.G.map (m.f ≫ m.g)=m.r := by
    rw [m.G.map_comp,← Category.assoc,m.hp,m.hr]
  have rhs : m.F.map (m.f ≫ m.g) ≫ m.eta m.E=m.s := by
    rw [m.F.map_comp,Category.assoc,← m.hg,← Category.assoc,m.hq,m.hs]
  exact m.rs (lhs.symm.trans (h.trans rhs))

inductive One | star
instance : Category One where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

theorem constantsDiffer : (fun _ : Bool => true) ≠ (fun _ : Bool => false) := by
  intro h
  have hh := congrFun h false
  contradiction

def completion (extra : Bool) : Model One One where
  F := 𝟭 One
  G := 𝟭 One
  eta := fun _ _ => false
  A := .star
  B := .star
  E := .star
  X := .star
  Y := .star
  f := Bool.not
  g := id
  j := if extra then id else Bool.not
  p := fun _ => true
  q := fun _ => false
  r := fun _ => true
  s := fun _ => false
  hp := rfl
  hq := rfl
  pq := constantsDiffer
  hg := rfl
  hr := rfl
  hs := rfl
  rs := constantsDiffer

end CT_52

open CT_52 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: For an ordinary natural transformation $$\eta:F\Rightarrow G$$ and a morphism $$f:A\to B$$, does $$G(f)\circ\eta_A=\eta_B\circ F(f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_52_turn_01_oracle {C D : Type} [Category C] [Category D] {F G : C ⥤ D} (η : F ⟶ G) {A B E : C} (f : A ⟶ B) (g : B ⟶ E) : η.app A ≫ G.map f=F.map f ≫ η.app B := by
  exact (η.naturality f).symm

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: For a natural transformation define $$N(m)\iff G(m)\circ\eta_{dom(m)}=\eta_{cod(m)}\circ F(m)$$. If $$f:A\to B$$ and $$g:B\to C$$, does $$N(g\circ f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_52_turn_02_oracle {C D : Type} [Category C] [Category D] {F G : C ⥤ D} (η : F ⟶ G) {A B E : C} (f : A ⟶ B) (g : B ⟶ E) : η.app A ≫ G.map (f ≫ g)=F.map (f ≫ g) ≫ η.app E := by
  exact (η.naturality (f ≫ g)).symm

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now let $$F,G$$ remain ordinary functors between categories, but replace naturality by a family of components $$\eta$$ with only the supplied equations. For $$f:A\to B$$ stipulate $$G(f)\circ\eta_A=p$$ and $$\eta_B\circ F(f)=q$$ with $$p\neq q$$. For $$g:B\to C$$ naturality holds, and $$G(g)\circ p=r$$, $$G(g)\circ q=s$$ with $$r\neq s$$. Does naturality hold for $$f$$?
JSON expected answer: No.
-/
theorem ct_52_turn_03_oracle [Category C] [Category D] (m : Model C D) : ¬ N m m.f := by
  exact noShort m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$G(f)\circ\eta_A=\eta_B\circ F(f)$$ hold?
JSON expected answer: No.
-/
theorem ct_52_turn_04_oracle [Category C] [Category D] (m : Model C D) : ¬ N m m.f := by
  exact noShort m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, are $$G(g)\circ(G(f)\circ\eta_A)$$ and $$G(g)\circ(\eta_B\circ F(f))$$ equal?
JSON expected answer: No.
-/
theorem ct_52_turn_05_oracle [Category C] [Category D] (m : Model C D) : (m.eta m.A ≫ m.G.map m.f) ≫ m.G.map m.g ≠ (m.F.map m.f ≫ m.eta m.B) ≫ m.G.map m.g := by
  rw [m.hp,m.hq,m.hr,m.hs]; exact m.rs

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$N(m)\iff G(m)\circ\eta_{dom(m)}=\eta_{cod(m)}\circ F(m)$$. Does $$N(id_A)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_52_turn_06_oracle [Category C] [Category D] (m : Model C D) : N m (𝟙 m.A) := by
  simp [N]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, does $$N(f)$$ hold?
JSON expected answer: No.
-/
theorem ct_52_turn_07_oracle [Category C] [Category D] (m : Model C D) : ¬ N m m.f := by
  exact noShort m

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$N(g\circ f)$$ hold?
JSON expected answer: No.
-/
theorem ct_52_turn_08_oracle [Category C] [Category D] (m : Model C D) : ¬ N m (m.f ≫ m.g) := by
  exact noComposite m

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$N(j)$$ hold for an additional arrow $$j:X\to Y$$?
JSON expected answer: cannot be determined
-/
theorem ct_52_turn_09_oracle : Underdetermined (fun _ : Model One One => True) (fun m => N m m.j) := by
  refine ⟨completion true,completion false,trivial,trivial,?_⟩; intro h; have hh := h.mp (by rfl); exact constantsDiffer hh

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$limit(F)$$?
JSON expected answer: cannot be determined
-/
theorem ct_52_turn_10_oracle : Underdetermined (fun _ : Model One One × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is the family $$\eta$$ natural for every morphism?
JSON expected answer: No.
-/
theorem ct_52_turn_11_oracle [Category C] [Category D] (m : Model C D) : ¬ ∀ (A B : C) (f : A ⟶ B), N m f := by
  intro h; exact noShort m (h m.A m.B m.f)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the naturality equation for $$f$$ hold in ordinary category theory, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ct_52_turn_12_oracle {C D : Type} [Category C] [Category D] {F G : C ⥤ D} (η : F ⟶ G) {A B E : C} (f : A ⟶ B) (g : B ⟶ E) {U V : Type} [Category U] [Category V] (m : Model U V) : η.app A ≫ G.map f=F.map f ≫ η.app B ∧ ¬ N m m.f := by
  exact ⟨(η.naturality f).symm,noShort m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does naturality hold for $$f$$ in ordinary category theory, and does it hold in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ct_52_turn_13_oracle {C D : Type} [Category C] [Category D] {F G : C ⥤ D} (η : F ⟶ G) {A B E : C} (f : A ⟶ B) (g : B ⟶ E) {U V : Type} [Category U] [Category V] (m : Model U V) : η.app A ≫ G.map f=F.map f ≫ η.app B ∧ ¬ N m m.f := by
  exact ⟨(η.naturality f).symm,noShort m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary category theory. Does $$G(f)\circ\eta_A=\eta_B\circ F(f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_52_turn_14_oracle {C D : Type} [Category C] [Category D] {F G : C ⥤ D} (η : F ⟶ G) {A B E : C} (f : A ⟶ B) (g : B ⟶ E) : η.app A ≫ G.map f=F.map f ≫ η.app B := by
  exact (η.naturality f).symm

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary category theory, does naturality hold for $$g\circ f$$?
JSON expected answer: Yes.
-/
theorem ct_52_turn_15_oracle {C D : Type} [Category C] [Category D] {F G : C ⥤ D} (η : F ⟶ G) {A B E : C} (f : A ⟶ B) (g : B ⟶ E) : η.app A ≫ G.map (f ≫ g)=F.map (f ≫ g) ≫ η.app E := by
  exact (η.naturality (f ≫ g)).symm

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does the naturality equation hold for $$f$$?
JSON expected answer: No.
-/
theorem ct_52_turn_16_oracle [Category C] [Category D] (m : Model C D) : ¬ N m m.f := by
  exact noShort m
