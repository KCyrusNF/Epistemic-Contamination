import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/linear_algebra/LA-42.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: LA-42 — Two bases of the same space have different cardinalities
Source: test case definition test_cases/linear_algebra/LA-42.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace LA_42
open Benchmark

/-- Lists are finite families; cardinality here is ordinary list length. -/
structure Model where
  B : List Nat
  C : List Nat
  E : List Nat
  D : List Nat
  hb : B.length=2
  hc : C.length=3
  he : E.length=2

def d (X : List Nat) := X.length
def Agree (xs : List Nat) := ∀ x ∈ xs, ∀ y ∈ xs, x=y

def completion (n : Nat) : Model where
  B := [0,1]
  C := [0,1,2]
  E := [3,4]
  D := List.range n
  hb := rfl
  hc := rfl
  he := rfl

theorem standardCards {V ι κ : Type} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] [Fintype κ] (B : Module.Basis ι ℚ V) (C : Module.Basis κ ℚ V) : Fintype.card ι=Fintype.card κ := by
  exact (Module.finrank_eq_card_basis B).symm.trans (Module.finrank_eq_card_basis C)

end LA_42

open LA_42 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In ordinary finite-dimensional linear algebra, do any two bases of the same vector space have the same cardinality?
JSON expected answer: Yes.
-/
theorem la_42_turn_01_oracle {V ι κ : Type} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ] (B : Module.Basis ι ℚ V) (C : Module.Basis κ ℚ V) : Fintype.card ι=Fintype.card κ := by
  exact standardCards B C

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In ordinary finite-dimensional linear algebra define $$d(X)=|X|$$ for a basis and $$Agree([X_1,\ldots,X_n])$$ to mean all listed cardinalities agree. If $$B,C,E$$ are bases of the same space, does $$Agree([B,C,E])$$ hold?
JSON expected answer: Yes.
-/
theorem la_42_turn_02_oracle {V ι κ : Type} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ] (B : Module.Basis ι ℚ V) (C : Module.Basis κ ℚ V) {ιE : Type} [Fintype ιE] (E : Module.Basis ιE ℚ V) : Agree [Fintype.card ι,Fintype.card κ,Fintype.card ιE] := by
  have h1 := standardCards B C; have h2 := standardCards B E; simp [Agree,← h1,← h2]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use finite families carrying the designation basis without the ordinary basis axioms. Declare $$B,C,E$$ bases of one labelled space with $$|B|=2$$, $$|C|=3$$, and $$|E|=2$$. Cardinalities use ordinary finite counting. Do $$B,C$$ have the same cardinality?
JSON expected answer: No.
-/
theorem la_42_turn_03_oracle (m : Model) : d m.B≠d m.C := by
  simp [d,m.hb,m.hc]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard basis-cardinality theorem hold for $$B$$ and $$C$$?
JSON expected answer: No.
-/
theorem la_42_turn_04_oracle (m : Model) : d m.B≠d m.C := by
  simp [d,m.hb,m.hc]

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, is $$|B|=|E|$$ while $$|E|\neq|C|$$?
JSON expected answer: Yes.
-/
theorem la_42_turn_05_oracle (m : Model) : d m.B=d m.E ∧ d m.E≠d m.C := by
  simp [d,m.hb,m.hc,m.he]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$d(X)=|X|$$ and $$Agree(L)$$ as equality of all listed basis-cardinality readings. What is $$d(B)$$?
JSON expected answer: 2
-/
theorem la_42_turn_06_oracle (m : Model) : d m.B=2 := by
  exact m.hb

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$d(C)$$?
JSON expected answer: 3
-/
theorem la_42_turn_07_oracle (m : Model) : d m.C=3 := by
  exact m.hc

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$Agree([B,E,C])$$ hold?
JSON expected answer: No.
-/
theorem la_42_turn_08_oracle (m : Model) : ¬ Agree [d m.B,d m.E,d m.C] := by
  simp [Agree,d,m.hb,m.he,m.hc]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$d(D)$$ for another finite family declared a basis?
JSON expected answer: cannot be determined
-/
theorem la_42_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => d m.D) := by
  exact ⟨completion 0,completion 1,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is the determinant of a basis-change matrix from $$B$$ to $$C$$?
JSON expected answer: cannot be determined
-/
theorem la_42_turn_10_oracle : Underdetermined (fun _ : Model × ℚ => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is basis cardinality an invariant of the space?
JSON expected answer: No.
-/
theorem la_42_turn_11_oracle (m : Model) : d m.B≠d m.C := by
  simp [d,m.hb,m.hc]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does equality of basis cardinalities hold in ordinary finite-dimensional linear algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem la_42_turn_12_oracle {V ι κ : Type} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ] (B : Module.Basis ι ℚ V) (C : Module.Basis κ ℚ V) (m : Model) : Fintype.card ι=Fintype.card κ ∧ d m.B≠d m.C := by
  exact ⟨standardCards B C,by simp [d,m.hb,m.hc]⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Do $$B$$ and $$C$$ have the same cardinality in the standard system, and do they have the same cardinality in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem la_42_turn_13_oracle {V ι κ : Type} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ] (B : Module.Basis ι ℚ V) (C : Module.Basis κ ℚ V) (m : Model) : Fintype.card ι=Fintype.card κ ∧ d m.B≠d m.C := by
  exact ⟨standardCards B C,by simp [d,m.hb,m.hc]⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary linear algebra. If $$|B|=2$$, must every basis of the same finite-dimensional space have cardinality $$2$$?
JSON expected answer: Yes.
-/
theorem la_42_turn_14_oracle {V ι κ : Type} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ] (B : Module.Basis ι ℚ V) (C : Module.Basis κ ℚ V) (hb : Fintype.card ι=2) : Fintype.card κ=2 := by
  rw [← standardCards B C]; exact hb

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary bases of the same finite-dimensional space, does $$Agree([B,C,E])$$ hold?
JSON expected answer: Yes.
-/
theorem la_42_turn_15_oracle {V ι κ : Type} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ] (B : Module.Basis ι ℚ V) (C : Module.Basis κ ℚ V) {ιE : Type} [Fintype ιE] (E : Module.Basis ιE ℚ V) : Agree [Fintype.card ι,Fintype.card κ,Fintype.card ιE] := by
  have h1 := standardCards B C; have h2 := standardCards B E; simp [Agree,← h1,← h2]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Do $$d(B)$$ and $$d(C)$$ agree?
JSON expected answer: No.
-/
theorem la_42_turn_16_oracle (m : Model) : d m.B≠d m.C := by
  simp [d,m.hb,m.hc]
