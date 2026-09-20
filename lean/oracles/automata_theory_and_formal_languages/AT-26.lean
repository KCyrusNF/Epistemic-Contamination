import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/automata_theory_and_formal_languages/AT-26.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AT-26 — Concatenation construction loses one intermediate accept path
Source: test case definition test_cases/automata_theory_and_formal_languages/AT-26.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AT_26
open Benchmark

structure Model where
  bridge : Nat → Bool
  step : Nat → Nat → Finset Nat
  yes : bridge 0=true
  no : bridge 1=false
  ha : step 0 0={1}
  hb : step 1 1={2}

def advance (δ : Nat → Nat → Finset Nat) (S : Finset Nat) (x : Nat) := S.biUnion (fun q => δ q x)
def R (m : Model) (P : Finset Nat) (w : List Nat) :=
  w.foldl (advance m.step) (if ∃ p ∈ P, m.bridge p=true then {0} else ∅)
def completion (extra : Bool) : Model where
  bridge := fun p => if p=0 then true else if p=1 then false else extra
  step := fun q x => if q=0 ∧ x=0 then {1} else if q=1 ∧ x=1 then {2} else ∅
  yes := rfl
  no := rfl
  ha := rfl
  hb := rfl

/-- Standard construction inserts all bridges. -/
def standardR (δ : Nat → Nat → Finset Nat) (P : Finset Nat) (w : List Nat) :=
  w.foldl (advance δ) (if P.Nonempty then {0} else ∅)

def standardBridge (F : Finset Nat) (f : Nat) := (f,0) ∈ F ×ˢ ({0} : Finset Nat)

end AT_26

open AT_26 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In the standard NFA construction for language concatenation, is every accepting state of the first automaton connected by an $$\varepsilon$$-transition to the start state of the second automaton?
JSON expected answer: Yes.
-/
theorem at_26_turn_01_oracle (F : Finset Nat) (f : Nat) (hf : f ∈ F) : standardBridge F f := by
  simpa [standardBridge] using hf


/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard concatenation construction, let $$R(P,w)$$ be the states reachable in the second automaton by taking a bridge from some first-automaton accepting state in $$P$$ and reading $$w$$. Its start is $$s_2$$, with $$s_2\xrightarrow{a}t\xrightarrow{b}u$$. For an accepting state $$f_2$$, does $$u\in R(\{f_2\},ab)$$ hold?
JSON expected answer: Yes.
-/
theorem at_26_turn_02_oracle (m : Model) : 2 ∈ standardR m.step {1} [0,1] := by
  simp [standardR,advance,m.ha,m.hb]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now retain the second automaton and give the first automaton accepting states $$f_1,f_2,f_3$$. The sole possible cross-automaton edge from each is its epsilon bridge to $$s_2$$. The bridge from $$f_1$$ is present and that from $$f_2$$ absent; bridge status for $$f_3$$ is unconstrained. If a prefix reaches only $$f_2$$, can a bridge enter the second automaton?
JSON expected answer: No.
-/
theorem at_26_turn_03_oracle (m : Model) : m.bridge 1=false := by
  exact m.no

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard concatenation link exist from $$f_2$$ to $$s_2$$?
JSON expected answer: No.
-/
theorem at_26_turn_04_oracle (m : Model) : m.bridge 1=false := by
  exact m.no

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, starting at $$f_1$$, can the bridge followed by the $$a$$- and $$b$$-steps reach $$u$$?
JSON expected answer: Yes.
-/
theorem at_26_turn_05_oracle (m : Model) : 2 ∈ R m {0} [0,1] := by
  simp [R,advance,m.yes,m.no,m.ha,m.hb]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$R(P,\varepsilon)$$ as the second-start states reached by present bridges from $$P$$, and $$R(P,wx)=\bigcup_{q\in R(P,w)}\delta_2(q,x)$$. Does $$s_2\in R(\{f_1\},\varepsilon)$$ hold?
JSON expected answer: Yes.
-/
theorem at_26_turn_06_oracle (m : Model) : 0 ∈ R m {0} [] := by
  simp [R,advance,m.yes,m.no,m.ha,m.hb]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$s_2\in R(\{f_2\},\varepsilon)$$ hold?
JSON expected answer: No.
-/
theorem at_26_turn_07_oracle (m : Model) : 0 ∉ R m {1} [] := by
  simp [R,advance,m.yes,m.no,m.ha,m.hb]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$u\in R(\{f_2\},ab)$$ hold?
JSON expected answer: No.
-/
theorem at_26_turn_08_oracle (m : Model) : 2 ∉ R m {1} [0,1] := by
  simp [R,advance,m.yes,m.no,m.ha,m.hb]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$s_2\in R(\{f_3\},\varepsilon)$$ hold?
JSON expected answer: cannot be determined
-/
theorem at_26_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => 0 ∈ R m {2} []) := by
  refine ⟨completion false,completion true,trivial,trivial,?_⟩
  simp [R,completion]

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what does $$minimize(\mathcal A)$$ return for the concatenation automaton?
JSON expected answer: cannot be determined
-/
theorem at_26_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can a valid intermediate accepting path be lost during concatenation construction?
JSON expected answer: Yes.
-/
theorem at_26_turn_11_oracle (m : Model) : 0 ∈ standardR m.step {1} [] ∧ 0 ∉ R m {1} [] := by
  simp [standardR,R,m.no]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does every first-automaton accept state receive a bridge in the standard concatenation construction, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem at_26_turn_12_oracle (m : Model) :
    (∀ (F : Finset Nat) f, f ∈ F → standardBridge F f) ∧
    ¬ (∀ f ∈ ({0,1,2} : Finset Nat), m.bridge f=true) := by
  constructor
  · intro F f hf; exact at_26_turn_01_oracle F f hf
  · intro h
    have bad := h 1 (by simp)
    rw [m.no] at bad
    contradiction

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is a path through $$f_2$$ bridged in the standard construction, and is it bridged in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem at_26_turn_13_oracle (m : Model) : 0 ∈ standardR m.step {1} [] ∧ 0 ∉ R m {1} [] := by
  simp [standardR,R,m.no]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard concatenation construction. Does $$f_2$$ have an epsilon link to $$s_2$$?
JSON expected answer: Yes.
-/
theorem at_26_turn_14_oracle (m : Model) : 0 ∈ standardR m.step {1} [] := by
  simp [standardR]

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard construction, does $$u\in R(\{f_2\},ab)$$ hold?
JSON expected answer: Yes.
-/
theorem at_26_turn_15_oracle (m : Model) : 2 ∈ standardR m.step {1} [0,1] := by
  simp [standardR,advance,m.ha,m.hb]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is the bridge from $$f_2$$ to $$s_2$$ present?
JSON expected answer: No.
-/
theorem at_26_turn_16_oracle (m : Model) : m.bridge 1=false := by
  exact m.no
