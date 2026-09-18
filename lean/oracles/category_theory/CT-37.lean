import oracles.Support

open CategoryTheory

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/category_theory/CT-37.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: CT-37 — Square commutes except one path pair
Source: test case definition test_cases/category_theory/CT-37.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace CT_37
open Benchmark

/-- These baseline arrows are genuinely typed Mathlib category morphisms. -/

structure Model (α β γ δ : Type) where
  p : α
  q : α
  postR : α → β
  postS : β → γ
  postT : α → δ
  pq : p≠q
  rpq : postR p≠postR q
  srpq : postS (postR p)≠postS (postR q)
abbrev Comm (p q : α) := p=q

def completion (free : Bool) : Model Bool Bool Bool Bool where
  p := false
  q := true
  postR := id
  postS := id
  postT := fun x => if free then x else false
  pq := by decide
  rpq := by decide
  srpq := by decide

end CT_37

open CT_37 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In ordinary category theory let $$f:A\to B$$, $$g:B\to D$$, $$h:A\to C$$, and $$k:C\to D$$ form a commutative square. Must its boundary composites satisfy $$g\circ f=k\circ h$$?
JSON expected answer: Yes.
-/
theorem ct_37_turn_01_oracle {C : Type} [Category C] {A D : C} (p q : A ⟶ D) (commutes : p=q) : Comm p q := by
  exact commutes

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In an ordinary commutative square with parallel boundary composites $$p,q:A\to D$$, define $$Comm(p,q)\iff p=q$$. For composable arrows $$r:D\to E$$ and $$s:E\to F$$, does $$Comm(s\circ(r\circ p),s\circ(r\circ q))$$ hold?
JSON expected answer: Yes.
-/
theorem ct_37_turn_02_oracle {C : Type} [Category C] {A D E F : C} (p q : A ⟶ D) (h : p=q) (r : D ⟶ E) (s : E ⟶ F) : Comm ((p ≫ r) ≫ s) ((q ≫ r) ≫ s) := by
  subst q; rfl

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now consider the corresponding square in a composition calculus, with $$g\circ f=p$$ and $$k\circ h=q$$, where $$p,q:A\to D$$ and $$p\neq q$$. The square is no longer required to commute. Stipulate $$r\circ p=p_1$$, $$r\circ q=q_1$$, $$s\circ p_1=p_2$$, $$s\circ q_1=q_2$$, with $$p_1\neq q_1$$ and $$p_2\neq q_2$$. Does this square commute?
JSON expected answer: No.
-/
theorem ct_37_turn_03_oracle (m : Model α β γ δ) : ¬ Comm m.p m.q := by
  exact m.pq

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$g\circ f=k\circ h$$ hold for the distinguished square?
JSON expected answer: No.
-/
theorem ct_37_turn_04_oracle (m : Model α β γ δ) : ¬ Comm m.p m.q := by
  exact m.pq

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$s\circ(r\circ p)=s\circ(r\circ q)$$ hold?
JSON expected answer: No.
-/
theorem ct_37_turn_05_oracle (m : Model α β γ δ) : ¬ Comm (m.postS (m.postR m.p)) (m.postS (m.postR m.q)) := by
  exact m.srpq

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$Comm(x,y)\iff x=y$$ for parallel boundary paths. Does $$Comm(p,p)$$ hold?
JSON expected answer: Yes.
-/
theorem ct_37_turn_06_oracle (m : Model α β γ δ) : Comm m.p m.p := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$Comm(r\circ p,r\circ q)$$ hold?
JSON expected answer: No.
-/
theorem ct_37_turn_07_oracle (m : Model α β γ δ) : ¬ Comm (m.postR m.p) (m.postR m.q) := by
  exact m.rpq

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$Comm(s\circ(r\circ p),s\circ(r\circ q))$$ hold?
JSON expected answer: No.
-/
theorem ct_37_turn_08_oracle (m : Model α β γ δ) : ¬ Comm (m.postS (m.postR m.p)) (m.postS (m.postR m.q)) := by
  exact m.srpq

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$Comm(t\circ p,t\circ q)$$ hold for another arrow $$t:D\to X$$?
JSON expected answer: cannot be determined
-/
theorem ct_37_turn_09_oracle : Underdetermined (fun _ : Model Bool Bool Bool Bool => True) (fun m => decide (Comm (m.postT m.p) (m.postT m.q))) := by
  exact ⟨completion false,completion true,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what is $$pullback(g,k)$$?
JSON expected answer: cannot be determined
-/
theorem ct_37_turn_10_oracle : Underdetermined (fun _ : Model Bool Bool Bool Bool × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, are all designated squares guaranteed to commute?
JSON expected answer: No.
-/
theorem ct_37_turn_11_oracle (m : Model α β γ δ) : ¬ Comm m.p m.q := by
  exact m.pq

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$g\circ f=k\circ h$$ hold for the corresponding square in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ct_37_turn_12_oracle {C : Type} [Category C] {A D : C} (p q : A ⟶ D) (h : p=q) (m : Model α β γ δ) : Comm p q ∧ ¬ Comm m.p m.q := by
  exact ⟨h,m.pq⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does the distinguished square commute in ordinary category theory, and does it commute in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ct_37_turn_13_oracle {C : Type} [Category C] {A D : C} (p q : A ⟶ D) (h : p=q) (m : Model α β γ δ) : Comm p q ∧ ¬ Comm m.p m.q := by
  exact ⟨h,m.pq⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary category theory. Does a commutative square satisfy equality of its two path composites?
JSON expected answer: Yes.
-/
theorem ct_37_turn_14_oracle {C : Type} [Category C] {A D : C} (p q : A ⟶ D) (commutes : p=q) : Comm p q := by
  exact commutes

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard commutative square, does $$Comm(s\circ(r\circ p),s\circ(r\circ q))$$ hold?
JSON expected answer: Yes.
-/
theorem ct_37_turn_15_oracle {C : Type} [Category C] {A D E F : C} (p q : A ⟶ D) (h : p=q) (r : D ⟶ E) (s : E ⟶ F) : Comm ((p ≫ r) ≫ s) ((q ≫ r) ≫ s) := by
  subst q; rfl

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does the distinguished square commute?
JSON expected answer: No.
-/
theorem ct_37_turn_16_oracle (m : Model α β γ δ) : ¬ Comm m.p m.q := by
  exact m.pq
