import oracles.Support

open CategoryTheory

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/category_theory/CT-60.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: CT-60 — Pullback square commutes but mediating morphism is non-unique
Source: test case definition test_cases/category_theory/CT-60.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace CT_60
open Benchmark

structure Model (α β γ : Type) where
  p1 : α → β
  p2 : α → γ
  a : β
  b : γ
  u : α
  v : α
  distinct : u≠v
  u1 : p1 u=a
  u2 : p2 u=b
  v1 : p1 v=a
  v2 : p2 v=b

def Mediates (m : Model α β γ) (x : α) := m.p1 x=m.a ∧ m.p2 x=m.b
noncomputable def M [Fintype α] (m : Model α β γ) : Finset α := by
  classical
  exact Finset.univ.filter (Mediates m)
theorem memM [Fintype α] (m : Model α β γ) (x : α) : x ∈ M m ↔ Mediates m x := by
  classical
  simp [M]
theorem notUnique (m : Model α β γ) : ¬ ∃! x, Mediates m x := by
  rintro ⟨x,hx,unique⟩
  exact m.distinct ((unique m.u ⟨m.u1,m.u2⟩).trans (unique m.v ⟨m.v1,m.v2⟩).symm)
theorem two [Fintype α] (m : Model α β γ) : 2 ≤ (M m).card := by
  classical
  have hs : {m.u,m.v} ⊆ M m := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with h | h
    · subst x; exact (memM _ _).mpr ⟨m.u1,m.u2⟩
    · subst x; exact (memM _ _).mpr ⟨m.v1,m.v2⟩
  simpa [m.distinct] using Finset.card_le_card hs

def completion (extra : Bool) : Model (Fin 3) Bool Bool where
  p1 := fun x => if x=2 then extra else true
  p2 := fun _ => true
  a := true
  b := true
  u := 0
  v := 1
  distinct := by decide
  u1 := rfl
  u2 := rfl
  v1 := rfl
  v2 := rfl

/-- A universal mediator property gives the finite solution set a single member. -/
theorem singletonOfUnique [Fintype α] (p : α → Prop) (h : ∃! x, p x) :
    (by
      classical
      exact Finset.univ.filter p : Finset α).card=1 := by
  classical
  rcases h with ⟨x,hx,unique⟩
  have hs : Finset.univ.filter p = {x} := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨unique y,fun e => e.symm ▸ hx⟩
  rw [hs]
  simp

/-- The actual projection equations for the fixed ordinary pullback cone. -/
def StandardMediates {C : Type} [Category C] {A B Z X : C}
    (f : A ⟶ Z) (g : B ⟶ Z) [Limits.HasPullback f g]
    (a : X ⟶ A) (b : X ⟶ B) (u : X ⟶ Limits.pullback f g) : Prop :=
  u ≫ Limits.pullback.fst f g = a ∧ u ≫ Limits.pullback.snd f g = b

/-- Derive uniqueness from the pullback, assuming only the stated existence. -/
theorem standardUnique {C : Type} [Category C] {A B Z X : C}
    (f : A ⟶ Z) (g : B ⟶ Z) [Limits.HasPullback f g]
    (a : X ⟶ A) (b : X ⟶ B)
    (existsMediator : ∃ u, StandardMediates f g a b u) :
    ∃! u, StandardMediates f g a b u := by
  rcases existsMediator with ⟨u,hu⟩
  refine ⟨u,hu,?_⟩
  intro v hv
  exact Limits.pullback.hom_ext (hv.1.trans hu.1.symm) (hv.2.trans hu.2.symm)

/-- The mediator set is a singleton even when the ambient hom-set is infinite. -/
theorem standardCard {C : Type} [Category C] {A B Z X : C}
    (f : A ⟶ Z) (g : B ⟶ Z) [Limits.HasPullback f g]
    (a : X ⟶ A) (b : X ⟶ B)
    (existsMediator : ∃ u, StandardMediates f g a b u) :
    ({u | StandardMediates f g a b u} : Set (X ⟶ Limits.pullback f g)).ncard = 1 := by
  rcases standardUnique f g a b existsMediator with ⟨u,hu,unique⟩
  have hs : ({v | StandardMediates f g a b v} : Set (X ⟶ Limits.pullback f g)) = {u} := by
    ext v
    change StandardMediates f g a b v ↔ v = u
    exact ⟨unique v,fun h => h.symm ▸ hu⟩
  rw [hs]
  exact Set.ncard_singleton u

end CT_60

open CT_60 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: For an ordinary pullback with projections $$p_1:P\to A$$ and $$p_2:P\to B$$, fix compatible cone arrows $$a:X\to A$$ and $$b:X\to B$$. If a mediator $$u:X\to P$$ satisfies $$p_1\circ u=a$$ and $$p_2\circ u=b$$, is it unique?
JSON expected answer: Yes.
-/
theorem ct_60_turn_01_oracle {C : Type} [Category C] {A B Z X : C} (f : A ⟶ Z) (g : B ⟶ Z) [Limits.HasPullback f g] (u v : X ⟶ Limits.pullback f g) (h1 : u ≫ Limits.pullback.fst f g = v ≫ Limits.pullback.fst f g) (h2 : u ≫ Limits.pullback.snd f g = v ≫ Limits.pullback.snd f g) : u=v := by
  exact Limits.pullback.hom_ext h1 h2

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$M=\{m:X\to P\mid(p_1\circ m=a)\land(p_2\circ m=b)\}$$ for the fixed cone. A mediator exists. What is $$|M|$$?
JSON expected answer: 1
-/
theorem ct_60_turn_02_oracle {C : Type} [Category C] {A B Z X : C}
    (f : A ⟶ Z) (g : B ⟶ Z) [Limits.HasPullback f g]
    (a : X ⟶ A) (b : X ⟶ B)
    (existsMediator : ∃ u, StandardMediates f g a b u) :
    ({u | StandardMediates f g a b u} : Set (X ⟶ Limits.pullback f g)).ncard = 1 := by
  exact standardCard f g a b existsMediator

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a finite typed composition calculus with a commuting square and the same cone and projection signatures, but no pullback uniqueness axiom. Stipulate distinct $$u,v:X\to P$$ with $$p_1\circ u=p_1\circ v=a$$ and $$p_2\circ u=p_2\circ v=b$$. Additional mediators are not excluded. Is the mediator unique?
JSON expected answer: No.
-/
theorem ct_60_turn_03_oracle (m : Model α β γ) : ¬ ∃! x, Mediates m x := by
  exact notUnique m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard uniqueness clause hold for this cone?
JSON expected answer: No.
-/
theorem ct_60_turn_04_oracle (m : Model α β γ) : ¬ ∃! x, Mediates m x := by
  exact notUnique m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, do $$u$$ and $$v$$ each satisfy both projection equations, giving four satisfied equations in total?
JSON expected answer: Yes.
-/
theorem ct_60_turn_05_oracle (m : Model α β γ) : Mediates m m.u ∧ Mediates m m.v := by
  exact ⟨⟨m.u1,m.u2⟩,⟨m.v1,m.v2⟩⟩

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$M=\{m:X\to P\mid(p_1\circ m=a)\land(p_2\circ m=b)\}$$. Is $$u\in M$$?
JSON expected answer: Yes.
-/
theorem ct_60_turn_06_oracle [Fintype α] (m : Model α β γ) : m.u ∈ M m := by
  exact (memM _ _).mpr ⟨m.u1,m.u2⟩

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, is $$v\in M$$?
JSON expected answer: Yes.
-/
theorem ct_60_turn_07_oracle [Fintype α] (m : Model α β γ) : m.v ∈ M m := by
  exact (memM _ _).mpr ⟨m.v1,m.v2⟩

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, is $$|M|\geq2$$?
JSON expected answer: Yes.
-/
theorem ct_60_turn_08_oracle [Fintype α] (m : Model α β γ) : 2 ≤ (M m).card := by
  exact two m

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$|M|$$?
JSON expected answer: cannot be determined
-/
theorem ct_60_turn_09_oracle : Underdetermined (fun _ : Model (Fin 3) Bool Bool => True) (fun m => (M m).card) := by
  refine ⟨completion false,completion true,trivial,trivial,?_⟩
  classical
  have h0 : M (completion false) = {0,1} := by
    ext x
    fin_cases x <;> simp [M,Mediates,completion]
  have h1 : M (completion true) = {0,1,2} := by
    ext x
    fin_cases x <;> simp [M,Mediates,completion]
  change (M (completion false)).card ≠ (M (completion true)).card
  rw [h0,h1]
  decide

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what is $$equalizer(u,v)$$?
JSON expected answer: cannot be determined
-/
theorem ct_60_turn_10_oracle : Underdetermined (fun _ : Model (Fin 3) Bool Bool × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can a commuting pullback-like square have non-unique mediating morphisms?
JSON expected answer: Yes.
-/
theorem ct_60_turn_11_oracle (m : Model α β γ) : ∃ u v, Mediates m u ∧ Mediates m v ∧ u≠v := by
  exact ⟨m.u,m.v,⟨m.u1,m.u2⟩,⟨m.v1,m.v2⟩,m.distinct⟩

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement “the mediating morphism is unique” hold for a pullback in ordinary category theory, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ct_60_turn_12_oracle {C : Type} [Category C] {A B Z X : C}
    (f : A ⟶ Z) (g : B ⟶ Z) [Limits.HasPullback f g]
    (a : X ⟶ A) (b : X ⟶ B)
    (existsMediator : ∃ u, StandardMediates f g a b u) (m : Model α β γ) :
    (∃! u, StandardMediates f g a b u) ∧ ¬ ∃! x, Mediates m x := by
  exact ⟨standardUnique f g a b existsMediator,notUnique m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is the mediator unique in ordinary category theory, and is it unique in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ct_60_turn_13_oracle {C : Type} [Category C] {A B Z X : C}
    (f : A ⟶ Z) (g : B ⟶ Z) [Limits.HasPullback f g]
    (a : X ⟶ A) (b : X ⟶ B)
    (existsMediator : ∃ u, StandardMediates f g a b u) (m : Model α β γ) :
    (∃! u, StandardMediates f g a b u) ∧ ¬ ∃! x, Mediates m x := by
  exact ⟨standardUnique f g a b existsMediator,notUnique m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary category theory. Is a pullback mediating morphism unique?
JSON expected answer: Yes.
-/
theorem ct_60_turn_14_oracle {C : Type} [Category C] {A B Z X : C} (f : A ⟶ Z) (g : B ⟶ Z) [Limits.HasPullback f g] (u v : X ⟶ Limits.pullback f g) (h1 : u ≫ Limits.pullback.fst f g = v ≫ Limits.pullback.fst f g) (h2 : u ≫ Limits.pullback.snd f g = v ≫ Limits.pullback.snd f g) : u=v := by
  exact Limits.pullback.hom_ext h1 h2

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary category theory, what is $$|M|$$ when a mediator exists for fixed cone data?
JSON expected answer: 1
-/
theorem ct_60_turn_15_oracle {C : Type} [Category C] {A B Z X : C}
    (f : A ⟶ Z) (g : B ⟶ Z) [Limits.HasPullback f g]
    (a : X ⟶ A) (b : X ⟶ B)
    (existsMediator : ∃ u, StandardMediates f g a b u) :
    ({u | StandardMediates f g a b u} : Set (X ⟶ Limits.pullback f g)).ncard = 1 := by
  exact standardCard f g a b existsMediator

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is the mediating morphism unique?
JSON expected answer: No.
-/
theorem ct_60_turn_16_oracle (m : Model α β γ) : ¬ ∃! x, Mediates m x := by
  exact notUnique m
