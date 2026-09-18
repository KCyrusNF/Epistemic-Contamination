import Mathlib

/-!
# oracles/Support.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Project: Epistemic Contamination
Purpose: shared definitions for separate per-turn mathematical oracles.

No modified relation is identified with Lean's built-in equality. Undefined
symbols are interpreted by arbitrary extensions, never by an imported operation.
-/
namespace Benchmark

/-- Two admissible interpretations disagree on the queried value. -/
def Underdetermined {M A : Type} (valid : M → Prop) (query : M → A) : Prop :=
  ∃ m₀ m₁, valid m₀ ∧ valid m₁ ∧ query m₀ ≠ query m₁

/-- An absent definition can be extended independently by two different values. -/
theorem undefinedNat (premises : Prop) (consistent : premises) :
    Underdetermined (fun _ : Nat => premises) (fun x => x) := by
  exact ⟨0, 1, consistent, consistent, by decide⟩

/-- Iterate the operation on the right by the distinguished element. -/
def iterateRight (op : Nat → Nat → Nat) (unit x : Nat) : Nat → Nat
  | 0 => x
  | n + 1 => op (iterateRight op unit x n) unit

/-- A path of length n+1 in a relation; length zero is identity. -/
def chain {A : Type} (r : A → A → Prop) : Nat → A → A → Prop
  | 0, x, y => x = y
  | n+1, x, z => ∃ y, chain r n x y ∧ r y z

theorem chain_transitive {A : Type} (r : A → A → Prop)
    (trans : ∀ x y z, r x y → r y z → r x z)
    (n : Nat) (x z : A) : chain r (n+1) x z → r x z := by
  induction n generalizing z with
  | zero => intro ⟨y, h, hy⟩; cases h; exact hy
  | succ n ih => intro ⟨y, hxy, hyz⟩; exact trans x y z (ih y hxy) hyz

/-- A pair records the standard and modified answers, in that order. -/
def parallel {A B : Type} (a : A) (b : B) : A × B := (a,b)
end Benchmark
