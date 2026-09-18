import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/boolean_algebra/BA-21.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: BA-21 — One element has no complement
Source: test case definition test_cases/boolean_algebra/BA-21.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace BA_21
open Benchmark

abbrev StdComp {α : Type} [BooleanAlgebra α] (x y : α) := x ⊓ y = ⊥ ∧ x ⊔ y = ⊤
/-- Distributivity proves uniqueness; it is not assumed as an extra axiom. -/
theorem uniqueComplement {α : Type} [BooleanAlgebra α] (a b c : α)
    (hb : StdComp a b) (hc : StdComp a c) : b=c := by
  have hbc : b=b ⊓ c := by
    calc
      b = b ⊓ (a ⊔ c) := by rw [hc.2]; simp
      _ = (b ⊓ a) ⊔ (b ⊓ c) := by rw [inf_sup_left]
      _ = b ⊓ c := by rw [inf_comm b a,hb.1]; simp
  have hcb : c=c ⊓ b := by
    calc
      c = c ⊓ (a ⊔ b) := by rw [hb.2]; simp
      _ = (c ⊓ a) ⊔ (c ⊓ b) := by rw [inf_sup_left]
      _ = c ⊓ b := by rw [inf_comm c a,hc.1]; simp
  exact hbc.trans ((inf_comm b c).trans hcb.symm)

structure Model (α : Type) where
  meet : α → α → α
  join : α → α → α
  zero : α
  one : α
  a : α
  b : α
  c : α
  d : α
  noA : ∀ x, ¬ (meet a x=zero ∧ join a x=one)
  bc : meet b c=zero ∧ join b c=one
  cb : meet c b=zero ∧ join c b=one

def Comp (m : Model α) (x y : α) := m.meet x y=m.zero ∧ m.join x y=m.one
noncomputable def C [Fintype α] (m : Model α) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (Comp m x)

theorem memC [Fintype α] (m : Model α) (x y : α) : y ∈ C m x ↔ Comp m x y := by
  classical
  simp [C]

def completion (extra : Bool) : Model (Fin 6) where
  meet := fun x y => if (x=3 ∧ y=4) ∨ (x=4 ∧ y=3) ∨ (x=5 ∧ extra=true) then 0 else 1
  join := fun _ _ => 1
  zero := 0
  one := 1
  a := 2
  b := 3
  c := 4
  d := 5
  noA := by intro x; fin_cases x <;> norm_num
  bc := by norm_num
  cb := by norm_num

end BA_21

open BA_21 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary Boolean algebra, does every element $$a$$ have a complement $$\neg a$$ satisfying $$a\land\neg a=0$$ and $$a\lor\neg a=1$$?
JSON expected answer: Yes.
-/
theorem ba_21_turn_01_oracle {α : Type} [BooleanAlgebra α] (a : α) : ∃ b, StdComp a b := by
  exact ⟨aᶜ,by simp [StdComp]⟩

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In a finite ordinary Boolean algebra define $$Comp(x,y)\iff(x\land y=0)\land(x\lor y=1)$$ and $$C(x)=\{y:Comp(x,y)\}$$. What is $$|C(1)|$$?
JSON expected answer: 1
-/
theorem ba_21_turn_02_oracle {α : Type} [BooleanAlgebra α] [Fintype α] [DecidableEq α] : (Finset.univ.filter (fun y : α => StdComp ⊤ y)).card=1 := by
  classical
  have h : Finset.univ.filter (fun y : α => StdComp ⊤ y) = {⊥} := by
    ext y
    simp [StdComp]
  rw [h]
  simp

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a finite carrier with total meet and join operations and distinguished elements $$0,1,a,b,c,d$$. No element $$x$$ satisfies both $$a\land x=0$$ and $$a\lor x=1$$. Stipulate also $$b\land c=0$$, $$b\lor c=1$$, $$c\land b=0$$, and $$c\lor b=1$$; other operation laws are not imposed. Does $$a$$ have a complement?
JSON expected answer: No.
-/
theorem ba_21_turn_03_oracle (m : Model α) : ¬ ∃ x, Comp m m.a x := by
  rintro ⟨x,h⟩; exact m.noA x h

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard existence-of-complement law hold for $$a$$?
JSON expected answer: No.
-/
theorem ba_21_turn_04_oracle (m : Model α) : ¬ ∃ x, Comp m m.a x := by
  rintro ⟨x,h⟩; exact m.noA x h

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, do the complement conditions hold from $$b$$ to $$c$$ and from $$c$$ to $$b$$?
JSON expected answer: Yes.
-/
theorem ba_21_turn_05_oracle (m : Model α) : Comp m m.b m.c ∧ Comp m m.c m.b := by
  exact ⟨m.bc,m.cb⟩

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$Comp(x,y)\iff(x\land y=0)\land(x\lor y=1)$$ and $$C(x)=\{y:Comp(x,y)\}$$. Does $$c\in C(b)$$ hold?
JSON expected answer: Yes.
-/
theorem ba_21_turn_06_oracle [Fintype α] (m : Model α) : m.c ∈ C m m.b := by
  exact (memC m m.b m.c).mpr m.bc

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, is $$C(a)$$ nonempty?
JSON expected answer: No.
-/
theorem ba_21_turn_07_oracle [Fintype α] (m : Model α) : ¬ (C m m.a).Nonempty := by
  rintro ⟨x,h⟩; exact m.noA x ((memC m m.a x).mp h)

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$b\in\bigcup_{x\in C(b)}C(x)$$ hold?
JSON expected answer: Yes.
-/
theorem ba_21_turn_08_oracle [Fintype α] (m : Model α) : ∃ x ∈ C m m.b, m.b ∈ C m x := by
  exact ⟨m.c,(memC _ _ _).mpr m.bc,(memC _ _ _).mpr m.cb⟩

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, is $$C(d)$$ nonempty?
JSON expected answer: cannot be determined
-/
theorem ba_21_turn_09_oracle : Underdetermined (fun _ : Model (Fin 6) => True) (fun m => ∃ x, Comp m m.d x) := by
  refine ⟨completion false,completion true,trivial,trivial,?_⟩; intro h; have hh := h.mpr ⟨0,by norm_num [Comp, completion]⟩; rcases hh with ⟨x,hx⟩; fin_cases x <;> simp [Comp,completion] at hx

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$a\oplus b$$?
JSON expected answer: cannot be determined
-/
theorem ba_21_turn_10_oracle : Underdetermined (fun _ : Model (Fin 6) × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is complement existence guaranteed for every element?
JSON expected answer: No.
-/
theorem ba_21_turn_11_oracle (m : Model α) : ¬ ∀ x, ∃ y, Comp m x y := by
  intro h; rcases h m.a with ⟨y,hy⟩; exact m.noA y hy

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement “$$a$$ has a complement” hold in ordinary Boolean algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ba_21_turn_12_oracle {α β : Type} [BooleanAlgebra α] (a : α) (m : Model β) : (∃ b, StdComp a b) ∧ ¬ ∃ x, Comp m m.a x := by
  exact ⟨⟨aᶜ,by simp [StdComp]⟩,by rintro ⟨x,h⟩; exact m.noA x h⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does $$a$$ have a complement in ordinary Boolean algebra, and does it have one in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ba_21_turn_13_oracle {α β : Type} [BooleanAlgebra α] (a : α) (m : Model β) : (∃ b, StdComp a b) ∧ ¬ ∃ x, Comp m m.a x := by
  exact ⟨⟨aᶜ,by simp [StdComp]⟩,by rintro ⟨x,h⟩; exact m.noA x h⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary Boolean algebra. Does every element have a complement?
JSON expected answer: Yes.
-/
theorem ba_21_turn_14_oracle {α : Type} [BooleanAlgebra α] (a : α) : ∃ b, StdComp a b := by
  exact ⟨aᶜ,by simp [StdComp]⟩

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the finite ordinary Boolean algebra, what is $$|C(1)|$$?
JSON expected answer: 1
-/
theorem ba_21_turn_15_oracle {α : Type} [BooleanAlgebra α] [Fintype α] [DecidableEq α] : (Finset.univ.filter (fun y : α => StdComp ⊤ y)).card=1 := by
  classical
  have h : Finset.univ.filter (fun y : α => StdComp ⊤ y) = {⊥} := by
    ext y
    simp [StdComp]
  rw [h]
  simp

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$a$$ have a complement?
JSON expected answer: No.
-/
theorem ba_21_turn_16_oracle (m : Model α) : ¬ ∃ x, Comp m m.a x := by
  rintro ⟨x,h⟩; exact m.noA x h
