import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/boolean_algebra/BA-55.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: BA-55 — Meet is not greatest lower bound
Source: test case definition test_cases/boolean_algebra/BA-55.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace BA_55
open Benchmark

/-- GLB states both lower-bound inequalities and the maximality condition. -/
def GLB {α : Type} [PartialOrder α] (z x y : α) : Prop :=
  z ≤ x ∧ z ≤ y ∧ ∀ w, w ≤ x → w ≤ y → w ≤ z
structure Model (α : Type) [PartialOrder α] where
  meet : α → α → α
  a : α
  b : α
  c : α
  d : α
  m : α
  n : α
  l : α
  hab : meet a b = m
  ma : m ≤ a
  mb : m ≤ b
  na : n ≤ a
  nb : n ≤ b
  nm : ¬ n ≤ m
  cm : c = m
  hmc : meet m c = l
  lm : l ≤ m
  lc : l ≤ c
  ml : ¬ m ≤ l

def completion (k : Nat) : Model Nat where
  meet := fun x y => if x=3 ∧ y=4 then 2 else if x=2 ∧ y=2 then 1 else k
  a := 3
  b := 4
  c := 2
  d := 0
  m := 2
  n := 3
  l := 1
  hab := rfl
  ma := by decide
  mb := by decide
  na := by decide
  nb := by decide
  nm := by decide
  cm := rfl
  hmc := rfl
  lm := by decide
  lc := by decide
  ml := by decide

theorem noGLB [PartialOrder α] (m : Model α) : ¬ GLB m.m m.a m.b := by
  intro h
  exact m.nm (h.2.2 m.n m.na m.nb)

end BA_55

open BA_55 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary Boolean algebra, is $$a\land b$$ the greatest lower bound of $$a$$ and $$b$$?
JSON expected answer: Yes.
-/
theorem ba_55_turn_01_oracle {α : Type} [BooleanAlgebra α] (a b : α) : GLB (a ⊓ b) a b := by
  exact ⟨inf_le_left, inf_le_right, fun _ ha hb => le_inf ha hb⟩

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In an ordinary Boolean algebra define $$G(x,y)=x\land y$$ and $$LB(z;x,y)\iff(z\leq x)\land(z\leq y)$$. If $$LB(z;a,b)$$ and $$z\leq c$$, must $$z\leq G(G(a,b),c)$$ hold?
JSON expected answer: Yes.
-/
theorem ba_55_turn_02_oracle {α : Type} [BooleanAlgebra α] (a b c z : α) (ha : z ≤ a) (hb : z ≤ b) (hc : z ≤ c) : z ≤ (a ⊓ b) ⊓ c := by
  exact le_inf (le_inf ha hb) hc

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a partially ordered carrier with a total meet-labelled operation. Stipulate $$a\land b=m$$, $$m\leq a,b$$, $$n\leq a,b$$, and $$n\nleq m$$. Also let $$c=m$$ and stipulate $$m\land c=l$$ with $$l\leq m,c$$ and $$m\nleq l$$. Meet has no assumed greatest-lower-bound law. Is $$m$$ the greatest lower bound of $$a,b$$?
JSON expected answer: No.
-/
theorem ba_55_turn_03_oracle [PartialOrder α] (m : Model α) : ¬ GLB m.m m.a m.b := by
  exact noGLB m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard greatest-lower-bound property hold for $$m=a\land b$$?
JSON expected answer: No.
-/
theorem ba_55_turn_04_oracle [PartialOrder α] (m : Model α) : ¬ GLB m.m m.a m.b := by
  exact noGLB m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$m\leq(a\land b)\land c$$ hold?
JSON expected answer: No.
-/
theorem ba_55_turn_05_oracle [PartialOrder α] (m : Model α) : ¬ m.m ≤ m.meet (m.meet m.a m.b) m.c := by
  rw [m.hab, m.hmc]; exact m.ml

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$G(x,y)=x\land y$$ and $$LB(z;x,y)\iff(z\leq x)\land(z\leq y)$$. Does $$LB(m;a,b)$$ hold?
JSON expected answer: Yes.
-/
theorem ba_55_turn_06_oracle [PartialOrder α] (m : Model α) : m.m ≤ m.a ∧ m.m ≤ m.b := by
  exact ⟨m.ma, m.mb⟩

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$n\leq G(a,b)$$ hold?
JSON expected answer: No.
-/
theorem ba_55_turn_07_oracle [PartialOrder α] (m : Model α) : ¬ m.n ≤ m.meet m.a m.b := by
  rw [m.hab]; exact m.nm

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$m\leq G(G(a,b),c)$$ hold?
JSON expected answer: No.
-/
theorem ba_55_turn_08_oracle [PartialOrder α] (m : Model α) : ¬ m.m ≤ m.meet (m.meet m.a m.b) m.c := by
  rw [m.hab, m.hmc]; exact m.ml

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$m\leq G(a,d)$$ hold for an additional element $$d$$?
JSON expected answer: cannot be determined
-/
theorem ba_55_turn_09_oracle : Underdetermined (fun _ : Model Nat => True) (fun m => decide (m.m ≤ m.meet m.a m.d)) := by
  exact ⟨completion 0, completion 2, trivial, trivial, by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$a\rightarrow b$$?
JSON expected answer: cannot be determined
-/
theorem ba_55_turn_10_oracle : Underdetermined (fun _ : Model Nat × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0), (completion 0,1), trivial, trivial, by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is meet guaranteed to be a greatest lower bound?
JSON expected answer: No.
-/
theorem ba_55_turn_11_oracle [PartialOrder α] (m : Model α) : ¬ ∀ x y, GLB (m.meet x y) x y := by
  intro h; have hh := h m.a m.b; rw [m.hab] at hh; exact noGLB m hh

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement “$$a\land b$$ is the greatest lower bound of $$a,b$$” hold in ordinary Boolean algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ba_55_turn_12_oracle {α β : Type} [BooleanAlgebra α] [PartialOrder β] (a b : α) (m : Model β) : GLB (a ⊓ b) a b ∧ ¬ GLB m.m m.a m.b := by
  exact ⟨⟨inf_le_left, inf_le_right, fun _ ha hb => le_inf ha hb⟩, noGLB m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is $$a\land b$$ a greatest lower bound in ordinary Boolean algebra, and is it one in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ba_55_turn_13_oracle {α β : Type} [BooleanAlgebra α] [PartialOrder β] (a b : α) (m : Model β) : GLB (a ⊓ b) a b ∧ ¬ GLB m.m m.a m.b := by
  exact ⟨⟨inf_le_left, inf_le_right, fun _ ha hb => le_inf ha hb⟩, noGLB m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary Boolean algebra. Is $$a\land b$$ the greatest lower bound of $$a,b$$?
JSON expected answer: Yes.
-/
theorem ba_55_turn_14_oracle {α : Type} [BooleanAlgebra α] (a b : α) : GLB (a ⊓ b) a b := by
  exact ⟨inf_le_left, inf_le_right, fun _ ha hb => le_inf ha hb⟩

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary Boolean algebra, if $$LB(z;a,b)$$ and $$z\leq c$$, must $$z\leq G(G(a,b),c)$$ hold?
JSON expected answer: Yes.
-/
theorem ba_55_turn_15_oracle {α : Type} [BooleanAlgebra α] (a b c z : α) (ha : z ≤ a) (hb : z ≤ b) (hc : z ≤ c) : z ≤ (a ⊓ b) ⊓ c := by
  exact le_inf (le_inf ha hb) hc

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is $$m=a\land b$$ the greatest lower bound of $$a,b$$?
JSON expected answer: No.
-/
theorem ba_55_turn_16_oracle [PartialOrder α] (m : Model α) : ¬ GLB m.m m.a m.b := by
  exact noGLB m
