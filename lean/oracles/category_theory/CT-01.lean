import oracles.Support

open CategoryTheory

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/category_theory/CT-01.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: CT-01 — Morphism composition not associative
Source: test case definition test_cases/category_theory/CT-01.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace CT_01
open Benchmark

/-- These baseline arrows are genuinely typed Mathlib category morphisms. -/

structure Model (α : Type) where
  comp : α → α → α
  f : α
  g : α
  h : α
  k : α
  r : α
  t : α
  s : α
  u : α
  v : α
  l : α
  p : α
  q : α
  gf : comp g f=t
  hg : comp h g=s
  sf : comp s f=u
  ht : comp h t=v
  ks : comp k s=l
  lf : comp l f=p
  ku : comp k u=p
  kv : comp k v=q
  uv : u≠v
  pq : p≠q

/-- Right-associated evaluation, as specified in Turn 2 (not a left fold). -/
def P (m : Model α) : α → List α → α
  | f, [] => f
  | f, g::gs => m.comp (P m g gs) f

/-- The table can be realized as a typed one-object composition calculus.
No associativity or identity axiom is imported into it. -/
def completion (free : Nat) : Model Nat where
  comp := fun x y => if (x,y)=(1,0) then 5 else if (x,y)=(2,1) then 6
    else if (x,y)=(6,0) then 7 else if (x,y)=(2,5) then 8
    else if (x,y)=(3,6) then 9 else if (x,y)=(9,0) then 10
    else if (x,y)=(3,7) then 10 else if (x,y)=(3,8) then 11 else free
  f := 0
  g := 1
  h := 2
  k := 3
  r := 4
  t := 5
  s := 6
  u := 7
  v := 8
  l := 9
  p := 10
  q := 11
  gf := rfl
  hg := rfl
  sf := rfl
  ht := rfl
  ks := rfl
  lf := rfl
  ku := rfl
  kv := rfl
  uv := by decide
  pq := by decide

theorem noAssoc (m : Model α) : m.comp (m.comp m.h m.g) m.f ≠ m.comp m.h (m.comp m.g m.f) := by
  rw [m.hg,m.sf,m.gf,m.ht]
  exact m.uv

end CT_01

open CT_01 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary category, for composable morphisms $$f:A\to B$$, $$g:B\to C$$, and $$h:C\to D$$, does $$(h\circ g)\circ f=h\circ(g\circ f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_01_turn_01_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : f ≫ (g ≫ h) = (f ≫ g) ≫ h := by
  simp only [Category.assoc]

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In an ordinary category define path evaluation by $$P([f])=f$$ and $$P([f,g,\ldots,h])=P([g,\ldots,h])\circ f$$. Does $$P([f,g,h])=h\circ(g\circ f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_01_turn_02_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : f ≫ (g ≫ h) = (f ≫ g) ≫ h := by
  simp only [Category.assoc]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now consider a typed composition calculus with the same arrows and $$k:D\to E$$, without associativity. Stipulate $$g\circ f=t$$, $$h\circ g=s$$, $$s\circ f=u$$, $$h\circ t=v$$, $$k\circ s=l$$, and $$l\circ f=p$$, where $$u\neq v$$. All named composites have the endpoints determined by their paths. Does associativity hold for $$(f,g,h)$$?
JSON expected answer: No.
-/
theorem ct_01_turn_03_oracle (m : Model α) : m.comp (m.comp m.h m.g) m.f ≠ m.comp m.h (m.comp m.g m.f) := by
  exact noAssoc m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$(h\circ g)\circ f=h\circ(g\circ f)$$ hold?
JSON expected answer: No.
-/
theorem ct_01_turn_04_oracle (m : Model α) : m.comp (m.comp m.h m.g) m.f ≠ m.comp m.h (m.comp m.g m.f) := by
  exact noAssoc m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, stipulate also $$k\circ u=p$$ and $$k\circ v=q$$ with $$p\neq q$$. Are $$k\circ((h\circ g)\circ f)$$ and $$k\circ(h\circ(g\circ f))$$ equal?
JSON expected answer: No.
-/
theorem ct_01_turn_05_oracle (m : Model α) : m.comp m.k (m.comp (m.comp m.h m.g) m.f) ≠ m.comp m.k (m.comp m.h (m.comp m.g m.f)) := by
  simpa [m.hg,m.sf,m.gf,m.ht,m.ku,m.kv] using m.pq

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$P([f])=f$$ and $$P([f,g,\ldots,h])=P([g,\ldots,h])\circ f$$ for nonempty compatible paths. What is $$P([f])$$?
JSON expected answer: f
-/
theorem ct_01_turn_06_oracle (m : Model α) : P m m.f []=m.f := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$P([f,g])$$?
JSON expected answer: t
-/
theorem ct_01_turn_07_oracle (m : Model α) : P m m.f [m.g]=m.t := by
  simp [P,m.gf,m.hg,m.sf,m.ht,m.ks,m.lf,m.ku,m.kv]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$P([f,g,h])$$?
JSON expected answer: u
-/
theorem ct_01_turn_08_oracle (m : Model α) : P m m.f [m.g,m.h] = m.u := by
  change m.comp (m.comp m.h m.g) m.f = m.u
  rw [m.hg, m.sf]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$P([f,g,r])$$ for another arrow $$r:C\to D$$?
JSON expected answer: cannot be determined
-/
theorem ct_01_turn_09_oracle : Underdetermined (fun _ : Model Nat => True) (fun m => P m m.f [m.g,m.r]) := by
  exact ⟨completion 0,completion 1,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$f\times g$$?
JSON expected answer: cannot be determined
-/
theorem ct_01_turn_10_oracle : Underdetermined (fun _ : Model Nat × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is morphism composition associative for every composable triple?
JSON expected answer: No.
-/
theorem ct_01_turn_11_oracle (m : Model α) : ¬ ∀ x y z, m.comp (m.comp z y) x=m.comp z (m.comp y x) := by
  intro h; exact noAssoc m (h m.f m.g m.h)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$(h\circ g)\circ f=h\circ(g\circ f)$$ hold in an ordinary category, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ct_01_turn_12_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (m : Model α) : f ≫ (g ≫ h) = (f ≫ g) ≫ h ∧ m.comp (m.comp m.h m.g) m.f ≠ m.comp m.h (m.comp m.g m.f) := by
  exact ⟨by simp only [Category.assoc],noAssoc m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does associativity hold for $$(f,g,h)$$ in an ordinary category, and does it hold in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ct_01_turn_13_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (m : Model α) : f ≫ (g ≫ h) = (f ≫ g) ≫ h ∧ m.comp (m.comp m.h m.g) m.f ≠ m.comp m.h (m.comp m.g m.f) := by
  exact ⟨by simp only [Category.assoc],noAssoc m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary category theory. Does $$(h\circ g)\circ f=h\circ(g\circ f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_01_turn_14_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : f ≫ (g ≫ h) = (f ≫ g) ≫ h := by
  simp only [Category.assoc]

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary category theory, does $$P([f,g,h])=h\circ(g\circ f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_01_turn_15_oracle {C : Type} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) : f ≫ (g ≫ h) = (f ≫ g) ≫ h := by
  simp only [Category.assoc]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$(h\circ g)\circ f$$?
JSON expected answer: u
-/
theorem ct_01_turn_16_oracle (m : Model α) : m.comp (m.comp m.h m.g) m.f=m.u := by
  rw [m.hg,m.sf]
