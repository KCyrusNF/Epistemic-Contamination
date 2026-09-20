import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/automata_theory_and_formal_languages/AT-14.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AT-14 — Acceptance checked one symbol before end
Source: test case definition test_cases/automata_theory_and_formal_languages/AT-14.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AT_14
open Benchmark

/-- States q₀,q₁,q₂ and symbols a,b,c use labels 0,1,2. -/
structure Model where
  step : Nat → Nat → Nat
  ha : step 0 0 = 1
  hb : step 1 1 = 2
  hc : step 2 2 = 2

def run (δ : Nat → Nat → Nat) (q : Nat) (w : List Nat) := w.foldl δ q

def wordPrefix (w : List Nat) := w.take (w.length-1)
def Accept (m : Model) (w : List Nat) : Prop := run m.step 0 (wordPrefix w)=2
def StdAccept (m : Model) (w : List Nat) : Prop := run m.step 0 w=2

/-- Ordinary acceptance tests the final state after the complete word. -/
def StandardAccept {Q Σ : Type} (δ : Q → Σ → Q) (start : Q)
    (F : Set Q) (w : List Σ) : Prop := w.foldl δ start ∈ F

def completion (k : Nat) : Model where
  step := fun q x => if q=0 ∧ x=0 then 1 else if q=1 ∧ x=1 then 2
    else if q=2 ∧ x=2 then 2 else k
  ha := rfl
  hb := rfl
  hc := rfl

end AT_14

open AT_14 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary finite automaton, is acceptance determined by the state reached after the entire input word has been consumed?
JSON expected answer: Yes.
-/
theorem at_14_turn_01_oracle {Q Σ : Type} (δ : Q → Σ → Q) (start : Q) (F : Set Q) (w : List Σ) :
    StandardAccept δ start F w ↔ w.foldl δ start ∈ F := by
  rfl

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard automaton let $$q_0\xrightarrow{a}q_1\xrightarrow{b}q_2\xrightarrow{c}q_2$$ with $$F=\{q_2\}$$ and distinct states. Define $$Accept(w)\iff\delta^*(q_0,w)\in F$$. Is $$Accept(ab)$$ true?
JSON expected answer: Yes.
-/
theorem at_14_turn_02_oracle (m : Model) : StdAccept m [0,1] := by
  simp [Accept,StdAccept,run,wordPrefix,m.ha,m.hb,m.hc]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now retain those transitions and accepting set, but check a nonempty word after all but its final symbol; for the empty word check the initial state. Other transitions are total but unconstrained. Is $$ab$$ accepted?
JSON expected answer: No.
-/
theorem at_14_turn_03_oracle (m : Model) : ¬ Accept m [0,1] := by
  simp [Accept,StdAccept,run,wordPrefix,m.ha,m.hb,m.hc]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard end-of-input acceptance verdict for $$ab$$ remain valid?
JSON expected answer: No.
-/
theorem at_14_turn_04_oracle (m : Model) : ¬ Accept m [0,1] := by
  simp [Accept,StdAccept,run,wordPrefix,m.ha,m.hb,m.hc]

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, is $$abcc$$ accepted?
JSON expected answer: Yes.
-/
theorem at_14_turn_05_oracle (m : Model) : Accept m [0,1,2,2] := by
  simp [Accept,StdAccept,run,wordPrefix,m.ha,m.hb,m.hc]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$Accept(w)\iff\delta^*(q_0,prefix(w))\in F$$, where $$prefix$$ removes the final symbol of a nonempty word and $$prefix(\varepsilon)=\varepsilon$$. Is $$Accept(\varepsilon)$$ true?
JSON expected answer: No.
-/
theorem at_14_turn_06_oracle (m : Model) : ¬ Accept m [] := by
  simp [Accept,StdAccept,run,wordPrefix,m.ha,m.hb,m.hc]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, is $$Accept(ab)$$ true?
JSON expected answer: No.
-/
theorem at_14_turn_07_oracle (m : Model) : ¬ Accept m [0,1] := by
  simp [Accept,StdAccept,run,wordPrefix,m.ha,m.hb,m.hc]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, do $$Accept(ab)$$ and $$Accept(abcc)$$ have the same truth value?
JSON expected answer: No.
-/
theorem at_14_turn_08_oracle (m : Model) : ¬ (Accept m [0,1] ↔ Accept m [0,1,2,2]) := by
  simp [Accept,StdAccept,run,wordPrefix,m.ha,m.hb,m.hc]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, is $$Accept(bb)$$ true?
JSON expected answer: cannot be determined
-/
theorem at_14_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => decide (run m.step 0 (wordPrefix [1,1])=2)) := by
  exact ⟨completion 0,completion 2,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what does $$minimize(\mathcal A)$$ return for this automaton?
JSON expected answer: cannot be determined
-/
theorem at_14_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is the final input symbol necessarily relevant to the acceptance check?
JSON expected answer: No.
-/
theorem at_14_turn_11_oracle (m : Model) (w : List Nat) (x y : Nat) : Accept m (w++[x]) ↔ Accept m (w++[y]) := by
  simp [Accept,wordPrefix]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does acceptance after consuming the full word characterize ordinary automata, the modified system, or both?
JSON expected answer: Only in the standard system.
-/
theorem at_14_turn_12_oracle (m : Model) :
    (∀ w, StdAccept m w ↔ run m.step 0 w=2) ∧
    ¬ (∀ w, Accept m w ↔ run m.step 0 w=2) := by
  constructor
  · intro w; rfl
  · intro h
    have bad := (h [0,1]).mpr (by simp [run,m.ha,m.hb])
    simpa [Accept,run,wordPrefix,m.ha] using bad

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is $$ab$$ accepted in the standard automaton, and is it accepted in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem at_14_turn_13_oracle (m : Model) : StdAccept m [0,1] ∧ ¬ Accept m [0,1] := by
  simp [Accept,StdAccept,run,wordPrefix,m.ha,m.hb,m.hc]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard automaton. Is $$ab$$ accepted?
JSON expected answer: Yes.
-/
theorem at_14_turn_14_oracle (m : Model) : StdAccept m [0,1] := by
  simp [StdAccept,run,m.ha,m.hb]

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard automaton, is $$Accept(ab)$$ true?
JSON expected answer: Yes.
-/
theorem at_14_turn_15_oracle (m : Model) : StdAccept m [0,1] := by
  simp [Accept,StdAccept,run,wordPrefix,m.ha,m.hb,m.hc]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is $$ab$$ accepted?
JSON expected answer: No.
-/
theorem at_14_turn_16_oracle (m : Model) : ¬ Accept m [0,1] := by
  simp [Accept,StdAccept,run,wordPrefix,m.ha,m.hb,m.hc]
