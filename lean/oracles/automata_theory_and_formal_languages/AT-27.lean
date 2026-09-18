import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/automata_theory_and_formal_languages/AT-27.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AT-27 — Kleene star disallows double repetition
Source: test case definition test_cases/automata_theory_and_formal_languages/AT-27.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AT_27
open Benchmark

/-- Repetition is ordinary list concatenation; the custom language is a predicate. -/
def word (n : Nat) : List Bool := (List.replicate n [false,true]).flatten

def StandardStar (w : List Bool) : Prop := ∃ n, w=word n
structure Model where
  star : List Bool → Prop
  h0 : star (word 0)
  h1 : star (word 1)
  h2 : ¬ star (word 2)
  h3 : star (word 3)

def Prefix (L : List Bool → Prop) : Nat → Prop
  | 0 => L (word 0)
  | n+1 => Prefix L n ∧ L (word (n+1))

def completion (extra : Bool) : Model where
  star := fun w => w=word 0 ∨ w=word 1 ∨ w=word 3 ∨ (extra=true ∧ w=word 4)
  h0 := by simp
  h1 := by simp
  h2 := by cases extra <;> decide
  h3 := by simp

theorem stdAll (n : Nat) : Prefix StandardStar n := by
  induction n with
  | zero => exact ⟨0,rfl⟩
  | succ n ih => exact ⟨ih,n+1,rfl⟩

end AT_27

open AT_27 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: For an ordinary language $$L$$, does Kleene star $$L^*$$ include every finite repetition count, including two repetitions?
JSON expected answer: Yes.
-/
theorem at_27_turn_01_oracle (n : Nat) : StandardStar (word n) := by
  exact ⟨n,rfl⟩

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: For ordinary $$L=\{ab\}$$, define $$M(n)\iff(ab)^n\in L^*$$ and $$Prefix(n)\iff\bigwedge_{j=0}^{n}M(j)$$. Does $$Prefix(3)$$ hold?
JSON expected answer: Yes.
-/
theorem at_27_turn_02_oracle : Prefix StandardStar 3 := by
  exact stdAll 3

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now replace star by a language-valued operation with $$\varepsilon,ab,(ab)^3\in L^*$$ but $$(ab)^2\notin L^*$$ for $$L=\{ab\}$$. Other repetition counts are unconstrained; ordinary word concatenation and exponent notation are unchanged. Is $$abab\in L^*$$?
JSON expected answer: No.
-/
theorem at_27_turn_03_oracle (m : Model) : ¬ m.star (word 2) := by
  exact m.h2

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard two-repetition membership of $$(ab)^2$$ hold?
JSON expected answer: No.
-/
theorem at_27_turn_04_oracle (m : Model) : ¬ m.star (word 2) := by
  exact m.h2

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does concatenating two admitted copies of $$ab$$ necessarily give an admitted word?
JSON expected answer: No.
-/
theorem at_27_turn_05_oracle (m : Model) : m.star (word 1) ∧ ¬ m.star (word 1++word 1) := by
  exact ⟨m.h1,m.h2⟩

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$M(n)\iff(ab)^n\in L^*$$ and $$Prefix(0)=M(0)$$, $$Prefix(n+1)\iff Prefix(n)\land M(n+1)$$. Does $$Prefix(0)$$ hold?
JSON expected answer: Yes.
-/
theorem at_27_turn_06_oracle (m : Model) : Prefix m.star 0 := by
  exact m.h0

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, does $$M(2)$$ hold?
JSON expected answer: No.
-/
theorem at_27_turn_07_oracle (m : Model) : ¬ m.star (word 2) := by
  exact m.h2

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$Prefix(3)$$ hold?
JSON expected answer: No.
-/
theorem at_27_turn_08_oracle (m : Model) : ¬ Prefix m.star 3 := by
  intro h; exact m.h2 h.1.2

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$M(4)$$ hold?
JSON expected answer: cannot be determined
-/
theorem at_27_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => m.star (word 4)) := by
  refine ⟨completion false,completion true,trivial,trivial,?_⟩; intro h; have hh := h.mpr (by simp [completion]); norm_num [completion,word] at hh

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what does $$reverse(L^*)$$ denote?
JSON expected answer: cannot be determined
-/
theorem at_27_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is closure under arbitrary finite repetition guaranteed?
JSON expected answer: No.
-/
theorem at_27_turn_11_oracle (m : Model) : ¬ ∀ n, m.star (word n) := by
  intro h; exact m.h2 (h 2)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$(ab)^2\in L^*$$ hold for ordinary Kleene star, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem at_27_turn_12_oracle (m : Model) : StandardStar (word 2) ∧ ¬ m.star (word 2) := by
  exact ⟨⟨2,rfl⟩,m.h2⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is $$abab$$ in $$L^*$$ in the standard system, and is it in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem at_27_turn_13_oracle (m : Model) : StandardStar (word 2) ∧ ¬ m.star (word 2) := by
  exact ⟨⟨2,rfl⟩,m.h2⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary Kleene star. Is $$(ab)^2\in L^*$$?
JSON expected answer: Yes.
-/
theorem at_27_turn_14_oracle : StandardStar (word 2) := by
  exact ⟨2,rfl⟩

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary Kleene star, does $$Prefix(3)$$ hold?
JSON expected answer: Yes.
-/
theorem at_27_turn_15_oracle : Prefix StandardStar 3 := by
  exact stdAll 3

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$M(2)$$ hold?
JSON expected answer: No.
-/
theorem at_27_turn_16_oracle (m : Model) : ¬ m.star (word 2) := by
  exact m.h2
