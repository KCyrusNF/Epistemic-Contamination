import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/boolean_algebra/BA-59.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: BA-59 — Dualizing a valid identity does not preserve validity
Source: test case definition test_cases/boolean_algebra/BA-59.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace BA_59
open Benchmark

structure Model (α : Type) where
  meet : α → α → α
  join : α → α → α
  zero : α
  one : α
  a : α
  b : α
  hab : b ≠ a
  meetOne : ∀ x, meet x one = x
  ha : join a zero = b
  hb : join b zero = b
/-- Syntax is kept separate from semantic validity. -/
inductive Term where
  | var | zero | one | meet (x y : Term) | join (x y : Term)
def dual : Term → Term
  | .var => .var | .zero => .one | .one => .zero
  | .meet x y => .join (dual x) (dual y)
  | .join x y => .meet (dual x) (dual y)
def eval (m : Model α) (x : α) : Term → α
  | .var => x | .zero => m.zero | .one => m.one
  | .meet a b => m.meet (eval m x a) (eval m x b)
  | .join a b => m.join (eval m x a) (eval m x b)
abbrev Valid (m : Model α) (t : Term) := ∀ x, eval m x t = x
abbrev D (m : Model α) (t : Term) := Valid m (dual t)
def I : Term := .meet .var .one
def J : Term := .join .var .zero
def K : Term := .meet I .one
def H : Term := .meet .var .var
def completion (extra : Bool) : Model (Fin 4) where
  meet := fun x _ => x
  join := fun x y => if x=0 ∧ y=2 then 1 else if extra=false ∧ x=2 ∧ y=2 then 0 else x
  zero := 2
  one := 3
  a := 0
  b := 1
  hab := by decide
  meetOne := by intro x; rfl
  ha := by cases extra <;> decide
  hb := by cases extra <;> decide

end BA_59

open BA_59 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary Boolean algebra, the principle of duality preserves valid identities under interchange of $$\land\leftrightarrow\lor$$ and $$0\leftrightarrow1$$. If $$x\land1=x$$ is valid, is its dual $$x\lor0=x$$ also valid?
JSON expected answer: Yes.
-/
theorem ba_59_turn_01_oracle {α : Type} [BooleanAlgebra α] : ∀ x : α, x ⊔ ⊥ = x := by
  simp

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In ordinary Boolean algebra, dualization exchanges $$\land,\lor$$ and $$0,1$$. Define $$D(I)$$ to mean validity of the syntactic dual of identity $$I$$. For $$I:x\land1=x$$, does $$D(I)$$ hold?
JSON expected answer: Yes.
-/
theorem ba_59_turn_02_oracle {α : Type} [BooleanAlgebra α] : ∀ x : α, x ⊔ ⊥ = x := by
  simp

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use total meet and join on a carrier with $$x\land1=x$$ for every $$x$$, but $$a\lor0=b$$ and $$b\lor0=b$$ with $$b\neq a$$. No other Boolean laws are imposed. Does the dual identity $$a\lor0=a$$ hold?
JSON expected answer: No.
-/
theorem ba_59_turn_03_oracle {α : Type} (m : Model α) : m.join m.a m.zero ≠ m.a := by
  rw [m.ha]
  exact m.hab


/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does dualizing the valid identity $$x\land1=x$$ preserve validity at $$a$$?
JSON expected answer: No.
-/
theorem ba_59_turn_04_oracle {α : Type} (m : Model α) : eval m m.a (dual I) ≠ m.a := by
  change m.join m.a m.zero ≠ m.a
  rw [m.ha]
  exact m.hab


/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$(a\lor0)\lor0=a$$ hold?
JSON expected answer: No.
-/
theorem ba_59_turn_05_oracle {α : Type} (m : Model α) : m.join (m.join m.a m.zero) m.zero ≠ m.a := by
  rw [m.ha, m.hb]
  exact m.hab


/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$D(I)$$ as validity of the syntactic dual under the same interchange of operations and constants. For $$J:x\lor0=x$$, does $$D(J)$$ hold?
JSON expected answer: Yes.
-/
theorem ba_59_turn_06_oracle {α : Type} (m : Model α) : D m J := by
  change ∀ x, m.meet x m.one = x
  exact m.meetOne


/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, for $$I:x\land1=x$$, does $$D(I)$$ hold?
JSON expected answer: No.
-/
theorem ba_59_turn_07_oracle {α : Type} (m : Model α) : ¬ D m I := by
  intro h
  have bad := h m.a
  change m.join m.a m.zero = m.a at bad
  rw [m.ha] at bad
  exact m.hab bad


/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, for $$K:(x\land1)\land1=x$$, does $$D(K)$$ hold?
JSON expected answer: No.
-/
theorem ba_59_turn_08_oracle {α : Type} (m : Model α) : ¬ D m K := by
  intro h
  have bad := h m.a
  change m.join (m.join m.a m.zero) m.zero = m.a at bad
  rw [m.ha, m.hb] at bad
  exact m.hab bad


/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, for $$H:x\land x=x$$, does $$D(H)$$ hold?
JSON expected answer: cannot be determined
-/
theorem ba_59_turn_09_oracle : Underdetermined (fun _ : Model (Fin 4) => True) (fun m => D m H) := by
  refine ⟨completion false,completion true,True.intro,True.intro,?_⟩
  intro h
  have yes : D (completion true) H := by decide
  have no : ¬ D (completion false) H := by decide
  exact no (h.mpr yes)

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$a\rightarrow b$$?
JSON expected answer: cannot be determined
-/
theorem ba_59_turn_10_oracle : Underdetermined (fun _ : Model (Fin 4) × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is validity preserved under dualization for every valid identity?
JSON expected answer: No.
-/
theorem ba_59_turn_11_oracle {α : Type} (m : Model α) : ¬ (∀ t, Valid m t → D m t) := by
  intro h
  have valid : Valid m I := by
    change ∀ x, m.meet x m.one = x
    exact m.meetOne
  exact ba_59_turn_04_oracle m ((h I valid) m.a)


/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does duality preserve the identity $$x\land1=x$$ in ordinary Boolean algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem ba_59_turn_12_oracle {α β : Type} [BooleanAlgebra α] (m : Model β) :
    (∀ x : α, x ⊔ ⊥ = x) ∧ ¬ D m I ∧ m.join m.a m.zero ≠ m.a := by
  refine ⟨by simp, ?_, ?_⟩
  · intro h
    have bad := h m.a
    change m.join m.a m.zero = m.a at bad
    rw [m.ha] at bad
    exact m.hab bad
  · rw [m.ha]
    exact m.hab


/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is $$a\lor0=a$$ valid in ordinary Boolean algebra, and is it valid in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem ba_59_turn_13_oracle {α β : Type} [BooleanAlgebra α] (m : Model β) :
    (∀ x : α, x ⊔ ⊥ = x) ∧ ¬ D m I ∧ m.join m.a m.zero ≠ m.a := by
  refine ⟨by simp, ?_, ?_⟩
  · intro h
    have bad := h m.a
    change m.join m.a m.zero = m.a at bad
    rw [m.ha] at bad
    exact m.hab bad
  · rw [m.ha]
    exact m.hab


/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary Boolean algebra. Is the dual of $$x\land1=x$$ valid?
JSON expected answer: Yes.
-/
theorem ba_59_turn_14_oracle {α : Type} [BooleanAlgebra α] : ∀ x : α, x ⊔ ⊥ = x := by
  simp

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary Boolean algebra, for $$K:(x\land1)\land1=x$$, does $$D(K)$$ hold?
JSON expected answer: Yes.
-/
theorem ba_59_turn_15_oracle {α : Type} [BooleanAlgebra α] : ∀ x : α, (x ⊔ ⊥) ⊔ ⊥ = x := by
  simp

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$D(I)$$ succeed?
JSON expected answer: No.
-/
theorem ba_59_turn_16_oracle {α : Type} (m : Model α) : ¬ D m I := by
  intro h
  have bad := h m.a
  change m.join m.a m.zero = m.a at bad
  rw [m.ha] at bad
  exact m.hab bad
