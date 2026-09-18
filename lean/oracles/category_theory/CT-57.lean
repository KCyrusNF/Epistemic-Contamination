import oracles.Support

open CategoryTheory

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/category_theory/CT-57.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: CT-57 — Product projection satisfies only one projection law
Source: test case definition test_cases/category_theory/CT-57.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace CT_57
open Benchmark

-- Baseline arrows below are typed Mathlib category morphisms.

/-- Separate hom-label types preserve the two projection result types. -/
structure Model (α β : Type) where
  second : α → β → β
  f : α
  g : β
  h : β
  r : α
  s : β
  hg : h≠g
  fg : second f g=h
  fh : second f h=h

def P (m : Model α β) (f : α) (g : β) := (f,m.second f g)
def completion (free : Nat) : Model Nat Nat where
  second := fun f g => if f=0 ∧ (g=0 ∨ g=1) then 1 else free
  f := 0
  g := 0
  h := 1
  r := 2
  s := 2
  hg := by decide
  fg := rfl
  fh := rfl

end CT_57

open CT_57 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: For an ordinary product $$A\times B$$ with pairing $$\langle f,g\rangle$$, do both projection laws $$\pi_1\circ\langle f,g\rangle=f$$ and $$\pi_2\circ\langle f,g\rangle=g$$ hold?
JSON expected answer: Yes.
-/
theorem ct_57_turn_01_oracle {C : Type} [Category C] {X A B : C} [Limits.HasBinaryProduct A B] (f : X ⟶ A) (g : X ⟶ B) : Limits.prod.lift f g ≫ Limits.prod.fst=f ∧ Limits.prod.lift f g ≫ Limits.prod.snd=g := by
  simp


/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$P(f,g)=(\pi_1\circ\langle f,g\rangle,\pi_2\circ\langle f,g\rangle)$$. Is $$P(f,g)=(f,g)$$?
JSON expected answer: Yes.
-/
theorem ct_57_turn_02_oracle {C : Type} [Category C] {X A B : C} [Limits.HasBinaryProduct A B] (f : X ⟶ A) (g : X ⟶ B) : (Limits.prod.lift f g ≫ Limits.prod.fst,Limits.prod.lift f g ≫ Limits.prod.snd)=(f,g) := by
  simp


/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a typed pairing calculus whose first projection law holds for every pairing. For $$f:X\to A$$ and $$g:X\to B$$, stipulate $$\pi_2\circ\langle f,g\rangle=h:X\to B$$ with $$h\neq g$$, and $$\pi_2\circ\langle f,h\rangle=h$$. Other second projections are unconstrained. What is $$\pi_2\circ\langle f,g\rangle$$?
JSON expected answer: h
-/
theorem ct_57_turn_03_oracle (m : Model α β) : m.second m.f m.g=m.h := by
  exact m.fg

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$\pi_2\circ\langle f,g\rangle=g$$ hold?
JSON expected answer: No.
-/
theorem ct_57_turn_04_oracle (m : Model α β) : m.second m.f m.g≠m.g := by
  rw [m.fg]; exact m.hg

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$\pi_2\circ\langle f,\pi_2\circ\langle f,g\rangle\rangle=h$$ hold?
JSON expected answer: Yes.
-/
theorem ct_57_turn_05_oracle (m : Model α β) : m.second m.f (m.second m.f m.g)=m.h := by
  simp [P,m.fg,m.fh]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In this modified system, define the derived projection pair $$P(f,g)=(\pi_1\circ\langle f,g\rangle,\pi_2\circ\langle f,g\rangle)$$. What is its first component?
JSON expected answer: f
-/
theorem ct_57_turn_06_oracle (m : Model α β) : (P m m.f m.g).1=m.f := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, what is the second component of $$P(f,g)$$?
JSON expected answer: h
-/
theorem ct_57_turn_07_oracle (m : Model α β) : (P m m.f m.g).2=m.h := by
  simp [P,m.fg,m.fh]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$P(f,\pi_2\circ\langle f,g\rangle)$$?
JSON expected answer: (f,h)
-/
theorem ct_57_turn_08_oracle (m : Model α β) : P m m.f (m.second m.f m.g)=(m.f,m.h) := by
  simp [P,m.fg,m.fh]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$P(r,s)$$ for an additional pairing $$\langle r,s\rangle$$?
JSON expected answer: cannot be determined
-/
theorem ct_57_turn_09_oracle : Underdetermined (fun _ : Model Nat Nat => True) (fun m => P m m.r m.s) := by
  exact ⟨completion 0,completion 1,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$coproduct(A,B)$$?
JSON expected answer: cannot be determined
-/
theorem ct_57_turn_10_oracle : Underdetermined (fun _ : Model Nat Nat × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, are both product projection laws guaranteed?
JSON expected answer: No.
-/
theorem ct_57_turn_11_oracle (m : Model α β) : ¬ ∀ f g, P m f g=(f,g) := by
  intro h; have hh := congrArg Prod.snd (h m.f m.g); simp only [P,m.fg] at hh; exact m.hg hh

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$\pi_2\circ\langle f,g\rangle=g$$ hold in ordinary category theory, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ct_57_turn_12_oracle {C : Type} [Category C] {X A B : C} [Limits.HasBinaryProduct A B] (f : X ⟶ A) (g : X ⟶ B) (m : Model α β) : Limits.prod.lift f g ≫ Limits.prod.snd=g ∧ m.second m.f m.g=m.h ∧ m.second m.f m.g≠m.g := by
  exact ⟨by simp,m.fg,by rw [m.fg]; exact m.hg⟩


/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$\pi_2\circ\langle f,g\rangle$$ in ordinary category theory, and what is it in the modified system?
JSON expected answer: g in the standard system and h in the modified system.
-/
theorem ct_57_turn_13_oracle {C : Type} [Category C] {X A B : C} [Limits.HasBinaryProduct A B] (f : X ⟶ A) (g : X ⟶ B) (m : Model α β) : Limits.prod.lift f g ≫ Limits.prod.snd=g ∧ m.second m.f m.g=m.h ∧ m.second m.f m.g≠m.g := by
  exact ⟨by simp,m.fg,by rw [m.fg]; exact m.hg⟩


/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary category theory. What is $$\pi_2\circ\langle f,g\rangle$$?
JSON expected answer: g
-/
theorem ct_57_turn_14_oracle {C : Type} [Category C] {X A B : C} [Limits.HasBinaryProduct A B] (f : X ⟶ A) (g : X ⟶ B) : Limits.prod.lift f g ≫ Limits.prod.snd=g := by
  simp


/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary category theory, is $$P(f,g)=(f,g)$$?
JSON expected answer: Yes.
-/
theorem ct_57_turn_15_oracle {C : Type} [Category C] {X A B : C} [Limits.HasBinaryProduct A B] (f : X ⟶ A) (g : X ⟶ B) : (Limits.prod.lift f g ≫ Limits.prod.fst,Limits.prod.lift f g ≫ Limits.prod.snd)=(f,g) := by
  simp


/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$\pi_2\circ\langle f,g\rangle$$?
JSON expected answer: h
-/
theorem ct_57_turn_16_oracle (m : Model α β) : m.second m.f m.g=m.h := by
  exact m.fg
