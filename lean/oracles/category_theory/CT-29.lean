import oracles.Support

open CategoryTheory

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/category_theory/CT-29.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: CT-29 — Monomorphism cancellation fails for one pair
Source: test case definition test_cases/category_theory/CT-29.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace CT_29
open Benchmark

-- Baseline arrows below are typed Mathlib category morphisms.

/-- Postcomposition functions act on the indicated parallel hom-set. -/
structure Model (α β γ : Type) where
  postM : α → β
  postK : β → γ
  postN : α → γ
  f : α
  g : α
  r : α
  s : α
  fg : f≠g
  rs : r≠s
  collision : postM f=postM g
  factor : ∀ x, postN x=postK (postM x)

def Cancel (j : α → β) (x y : α) := j x=j y → x=y

def completion (free : Bool) : Model Nat Nat Nat where
  postM := fun x => if x=0 ∨ x=1 then 0 else if free then x else 0
  postK := id
  postN := fun x => if x=0 ∨ x=1 then 0 else if free then x else 0
  f := 0
  g := 1
  r := 2
  s := 3
  fg := by decide
  rs := by decide
  collision := rfl
  factor := by intros; rfl

theorem noM (m : Model α β γ) : ¬ Cancel m.postM m.f m.g := by
  intro h; exact m.fg (h m.collision)
theorem eqN (m : Model α β γ) : m.postN m.f=m.postN m.g := by
  rw [m.factor,m.factor,m.collision]
theorem noN (m : Model α β γ) : ¬ Cancel m.postN m.f m.g := by
  intro h; exact m.fg (h (eqN m))

end CT_29

open CT_29 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary category, if $$m:B\to C$$ is a monomorphism and $$m\circ f=m\circ g$$ for $$f,g:A\to B$$, does $$f=g$$ follow?
JSON expected answer: Yes.
-/
theorem ct_29_turn_01_oracle {C : Type} [Category C] {A B D : C} (m : B ⟶ D) [Mono m] (f g : A ⟶ B) (h : f ≫ m=g ≫ m) : f=g := by
  exact (cancel_mono m).mp h

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In an ordinary category define $$C_m(x,y)\iff (m\circ x=m\circ y\Rightarrow x=y)$$. For a monomorphism $$m$$, if $$n\circ x=n\circ y$$ implies $$m\circ x=m\circ y$$, does $$C_n(x,y)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_29_turn_02_oracle {C : Type} [Category C] {A B D E : C} (m : B ⟶ D) [Mono m] (n : B ⟶ E) (x y : A ⟶ B) (h : x ≫ n=y ≫ n → x ≫ m=y ≫ m) : x ≫ n=y ≫ n → x=y := by
  intro hn; exact (cancel_mono m).mp (h hn)

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a typed composition calculus in which the designation monic imposes no unstated cancellation axioms. Let $$m:B\to C$$, $$f,g:A\to B$$, and $$m\circ f=m\circ g$$ but $$f\neq g$$. Declare $$m$$ monic. Also let $$k:C\to D$$, $$n:B\to D$$ with $$n\circ x=k\circ(m\circ x)$$ for every $$x:A\to B$$. Does $$f=g$$ hold?
JSON expected answer: No.
-/
theorem ct_29_turn_03_oracle (m : Model α β γ) : m.f≠m.g := by
  exact m.fg

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does monomorphism cancellation correctly infer $$f=g$$ from $$m\circ f=m\circ g$$?
JSON expected answer: No.
-/
theorem ct_29_turn_04_oracle (m : Model α β γ) : ¬ Cancel m.postM m.f m.g := by
  exact noM m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$n\circ f=n\circ g$$ hold?
JSON expected answer: Yes.
-/
theorem ct_29_turn_05_oracle (m : Model α β γ) : m.postN m.f=m.postN m.g := by
  exact eqN m

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$C_j(x,y)\iff(j\circ x=j\circ y\Rightarrow x=y)$$. Does $$C_m(f,f)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_29_turn_06_oracle (m : Model α β γ) : Cancel m.postM m.f m.f := by
  intro _; rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, does $$C_m(f,g)$$ succeed?
JSON expected answer: No.
-/
theorem ct_29_turn_07_oracle (m : Model α β γ) : ¬ Cancel m.postM m.f m.g := by
  exact noM m

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$C_n(f,g)$$ hold?
JSON expected answer: No.
-/
theorem ct_29_turn_08_oracle (m : Model α β γ) : ¬ Cancel m.postN m.f m.g := by
  exact noN m

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$C_m(r,s)$$ hold for additional distinct arrows $$r,s:A\to B$$?
JSON expected answer: cannot be determined
-/
theorem ct_29_turn_09_oracle : Underdetermined (fun _ : Model Nat Nat Nat => True) (fun m => Cancel m.postM m.r m.s) := by
  refine ⟨completion false,completion true,trivial,trivial,?_⟩; intro h; have hh := h.mpr (by simp [Cancel,completion]); norm_num [Cancel,completion] at hh

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$cokernel(m)$$?
JSON expected answer: cannot be determined
-/
theorem ct_29_turn_10_oracle : Underdetermined (fun _ : Model Nat Nat Nat × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, does being declared monic guarantee left cancellation for every pair?
JSON expected answer: No.
-/
theorem ct_29_turn_11_oracle (m : Model α β γ) : ¬ ∀ x y, Cancel m.postM x y := by
  intro h; exact noM m (h m.f m.g)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the implication $$m\circ f=m\circ g\Rightarrow f=g$$ hold for a monomorphism in ordinary category theory, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ct_29_turn_12_oracle {C : Type} [Category C] {A B D : C} (j : B ⟶ D) [Mono j] (f g : A ⟶ B) (m : Model α β γ) : (f ≫ j=g ≫ j → f=g) ∧ ¬ Cancel m.postM m.f m.g := by
  exact ⟨(cancel_mono j).mp,noM m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does cancellation infer $$f=g$$ in ordinary category theory, and does it infer $$f=g$$ in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ct_29_turn_13_oracle {C : Type} [Category C] {A B D : C} (j : B ⟶ D) [Mono j] (f g : A ⟶ B) (m : Model α β γ) : (f ≫ j=g ≫ j → f=g) ∧ ¬ Cancel m.postM m.f m.g := by
  exact ⟨(cancel_mono j).mp,noM m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary category theory. If $$m$$ is monic and $$m\circ f=m\circ g$$, does $$f=g$$ follow?
JSON expected answer: Yes.
-/
theorem ct_29_turn_14_oracle {C : Type} [Category C] {A B D : C} (m : B ⟶ D) [Mono m] (f g : A ⟶ B) (h : f ≫ m=g ≫ m) : f=g := by
  exact (cancel_mono m).mp h

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary category theory, if $$m$$ is monic and $$n\circ x=n\circ y$$ implies $$m\circ x=m\circ y$$, does $$C_n(x,y)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_29_turn_15_oracle {C : Type} [Category C] {A B D E : C} (m : B ⟶ D) [Mono m] (n : B ⟶ E) (x y : A ⟶ B) (h : x ≫ n=y ≫ n → x ≫ m=y ≫ m) : x ≫ n=y ≫ n → x=y := by
  intro hn; exact (cancel_mono m).mp (h hn)

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$f=g$$ follow from $$m\circ f=m\circ g$$?
JSON expected answer: No.
-/
theorem ct_29_turn_16_oracle (m : Model α β γ) : ¬ Cancel m.postM m.f m.g := by
  exact noM m
