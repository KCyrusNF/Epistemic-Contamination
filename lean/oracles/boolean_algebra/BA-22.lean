import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/boolean_algebra/BA-22.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: BA-22 — One element has two complements
Source: test case definition test_cases/boolean_algebra/BA-22.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace BA_22
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
  distinct : b≠c
  ab : meet a b=zero ∧ join a b=one
  ac : meet a c=zero ∧ join a c=one

def Comp (m : Model α) (x y : α) := m.meet x y=m.zero ∧ m.join x y=m.one
noncomputable def C [Fintype α] (m : Model α) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (Comp m x)
theorem memC [Fintype α] (m : Model α) (x y : α) : y ∈ C m x ↔ Comp m x y := by
  classical
  simp [C]
theorem two [Fintype α] (m : Model α) : 2 ≤ (C m m.a).card := by
  classical
  have hs : {m.b,m.c} ⊆ C m m.a := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with h | h
    · subst x; exact (memC _ _ _).mpr m.ab
    · subst x; exact (memC _ _ _).mpr m.ac
  have hc := Finset.card_le_card hs
  simpa [m.distinct] using hc

theorem notUnique (m : Model α) : ¬ ∃! x, Comp m m.a x := by
  rintro ⟨x,hx,unique⟩
  exact m.distinct ((unique m.b m.ab).trans (unique m.c m.ac).symm)

def completion (extra : Bool) : Model (Fin 5) where
  meet := fun x y => if x=0 ∧ (y=1 ∨ y=2 ∨ (y=0 ∧ extra=true)) then 3 else 4
  join := fun _ _ => 4
  zero := 3
  one := 4
  a := 0
  b := 1
  c := 2
  distinct := by decide
  ab := by norm_num
  ac := by norm_num

end BA_22

open BA_22 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary Boolean algebra, is the complement of an element unique?
JSON expected answer: Yes.
-/
theorem ba_22_turn_01_oracle {α : Type} [BooleanAlgebra α] (a b c : α) (hb : StdComp a b) (hc : StdComp a c) : b=c := by
  exact uniqueComplement a b c hb hc

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In a finite ordinary Boolean algebra define $$Comp(x,y)\iff(x\land y=0)\land(x\lor y=1)$$ and $$C(x)=\{y:Comp(x,y)\}$$. If $$b,c\in C(a)$$, must $$b=c$$?
JSON expected answer: Yes.
-/
theorem ba_22_turn_02_oracle {α : Type} [BooleanAlgebra α] (a b c : α) (hb : StdComp a b) (hc : StdComp a c) : b=c := by
  exact uniqueComplement a b c hb hc

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a finite carrier with total meet and join operations, without other Boolean axioms. Distinct elements $$b\neq c$$ both complement $$a$$: $$a\land b=0$$, $$a\lor b=1$$, $$a\land c=0$$, and $$a\lor c=1$$. Is the complement of $$a$$ unique?
JSON expected answer: No.
-/
theorem ba_22_turn_03_oracle (m : Model α) : ¬ ∃! x, Comp m m.a x := by
  exact notUnique m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard uniqueness-of-complement law hold for $$a$$?
JSON expected answer: No.
-/
theorem ba_22_turn_04_oracle (m : Model α) : ¬ ∃! x, Comp m m.a x := by
  exact notUnique m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, do both $$b$$ and $$c$$ satisfy the complement conditions for $$a$$?
JSON expected answer: Yes.
-/
theorem ba_22_turn_05_oracle (m : Model α) : Comp m m.a m.b ∧ Comp m m.a m.c := by
  exact ⟨m.ab,m.ac⟩

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$Comp(x,y)\iff(x\land y=0)\land(x\lor y=1)$$ and $$C(x)=\{y:Comp(x,y)\}$$. Does $$b\in C(a)$$ hold?
JSON expected answer: Yes.
-/
theorem ba_22_turn_06_oracle [Fintype α] (m : Model α) : m.b ∈ C m m.a := by
  exact (memC _ _ _).mpr m.ab

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$c\in C(a)$$ hold?
JSON expected answer: Yes.
-/
theorem ba_22_turn_07_oracle [Fintype α] (m : Model α) : m.c ∈ C m m.a := by
  exact (memC _ _ _).mpr m.ac

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$|C(a)|\geq2$$ hold?
JSON expected answer: Yes.
-/
theorem ba_22_turn_08_oracle [Fintype α] (m : Model α) : 2 ≤ (C m m.a).card := by
  exact two m

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$|C(a)|$$?
JSON expected answer: cannot be determined
-/
theorem ba_22_turn_09_oracle : Underdetermined (fun _ : Model (Fin 5) => True) (fun m => (C m m.a).card) := by
  refine ⟨completion false,completion true,trivial,trivial,?_⟩
  classical
  have h0 : C (completion false) 0 = {1,2} := by
    ext x
    fin_cases x <;> simp [C,Comp,completion]
  have h1 : C (completion true) 0 = {0,1,2} := by
    ext x
    fin_cases x <;> simp [C,Comp,completion]
  change (C (completion false) 0).card ≠ (C (completion true) 0).card
  rw [h0,h1]
  decide

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$a\rightarrow b$$?
JSON expected answer: cannot be determined
-/
theorem ba_22_turn_10_oracle : Underdetermined (fun _ : Model (Fin 5) × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can one element have two distinct complements?
JSON expected answer: Yes.
-/
theorem ba_22_turn_11_oracle (m : Model α) : ∃ b c, Comp m m.a b ∧ Comp m m.a c ∧ b≠c := by
  exact ⟨m.b,m.c,m.ab,m.ac,m.distinct⟩

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does complement uniqueness hold in ordinary Boolean algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ba_22_turn_12_oracle {α β : Type} [BooleanAlgebra α] (a : α) (m : Model β) : (∃! b, StdComp a b) ∧ ¬ ∃! x, Comp m m.a x := by
  refine ⟨⟨aᶜ,by simp [StdComp],?_⟩,notUnique m⟩; intro y hy; exact uniqueComplement a y aᶜ hy (by simp [StdComp])

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is the complement of $$a$$ unique in ordinary Boolean algebra, and is it unique in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ba_22_turn_13_oracle {α β : Type} [BooleanAlgebra α] (a : α) (m : Model β) : (∃! b, StdComp a b) ∧ ¬ ∃! x, Comp m m.a x := by
  refine ⟨⟨aᶜ,by simp [StdComp],?_⟩,notUnique m⟩; intro y hy; exact uniqueComplement a y aᶜ hy (by simp [StdComp])

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary Boolean algebra. If $$b$$ and $$c$$ both complement $$a$$, must $$b=c$$?
JSON expected answer: Yes.
-/
theorem ba_22_turn_14_oracle {α : Type} [BooleanAlgebra α] (a b c : α) (hb : StdComp a b) (hc : StdComp a c) : b=c := by
  exact uniqueComplement a b c hb hc

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the finite ordinary Boolean algebra, if $$b,c\in C(a)$$, must $$b=c$$?
JSON expected answer: Yes.
-/
theorem ba_22_turn_15_oracle {α : Type} [BooleanAlgebra α] (a b c : α) (hb : StdComp a b) (hc : StdComp a c) : b=c := by
  exact uniqueComplement a b c hb hc

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is the complement of $$a$$ unique?
JSON expected answer: No.
-/
theorem ba_22_turn_16_oracle (m : Model α) : ¬ ∃! x, Comp m m.a x := by
  exact notUnique m
