import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/automata_theory_and_formal_languages/AT-17.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AT-17 — NFA branch disappears after first nondeterministic split
Source: test case definition test_cases/automata_theory_and_formal_languages/AT-17.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AT_17
open Benchmark

/-- Ordered, duplicate-free successor lists represent finite successor sets. -/
structure Model where
  successors : Nat → Nat → List Nat
  nodup : ∀ q x, (successors q x).Nodup
  ha : successors 0 0=[1,2]
  hb1 : successors 1 1=[3]
  hb2 : successors 2 1=[4]

def advance (δ : Nat → Nat → List Nat) : List Nat → Bool → Nat → List Nat × Bool
  | [], used, _ => ([],used)
  | q::qs, used, x =>
    let s := δ q x
    let split := !used && decide (1 < s.length)
    let chosen := if split then s.take 1 else s
    let rest := advance δ qs (used || split) x
    (chosen++rest.1,rest.2)

def R (m : Model) (w : List Nat) : Finset Nat :=
  (w.foldl (fun state x => advance m.successors state.1 state.2 x) ([0],false)).1.toFinset

def standardR (m : Model) (w : List Nat) : Finset Nat :=
  (w.foldl (fun qs x => qs.flatMap (fun q => m.successors q x)) [0]).toFinset

def completion (extra : Bool) : Model where
  successors := fun q x => if (q,x)=(0,0) then [1,2] else if (q,x)=(1,1) then [3]
    else if (q,x)=(2,1) then [4] else if extra then [4] else []
  nodup := by
    intro q x
    split <;> try decide
    split <;> try decide
    split <;> try decide
    split <;> decide
  ha := rfl
  hb1 := rfl
  hb2 := rfl

end AT_17

open AT_17 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary NFA, after a nondeterministic transition $$\delta(q_0,a)=\{q_1,q_2\}$$, are both branches retained?
JSON expected answer: Yes.
-/
theorem at_17_turn_01_oracle (m : Model) : standardR m [0]={1,2} := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard NFA all displayed state names are distinct. Let $$R(w)$$ be the active-state set after reading $$w$$ from $$q_0$$. Let $$\delta(q_0,a)=\{q_1,q_2\}$$, $$\delta(q_1,b)=\{q_r\}$$, $$\delta(q_2,b)=\{q_f\}$$, and $$F=\{q_f\}$$. Is $$R(ab)\cap F$$ nonempty?
JSON expected answer: Yes.
-/
theorem at_17_turn_02_oracle (m : Model) : (standardR m [0,1] ∩ {4}).Nonempty := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now retain the same distinct states, alphabet $$\{a,b,c\}$$, and accepting set. At the first nondeterministic split in a run, retain only its first listed branch; subsequent steps propagate all surviving states normally. The ordered successors at $$(q_0,a)$$ are $$[q_1,q_2]$$; the listed $$b$$-transitions remain singleton transitions. Other transitions are total set-valued but unconstrained. What active-state set follows $$a$$?
JSON expected answer: {q_1}
-/
theorem at_17_turn_03_oracle (m : Model) : R m [0]={1} := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, is the active-state set after $$a$$ equal to $$\{q_1,q_2\}$$?
JSON expected answer: No.
-/
theorem at_17_turn_04_oracle (m : Model) : R m [0]≠{1,2} := by
  rw [at_17_turn_03_oracle m]
  decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, with $$q_1\xrightarrow{b}q_r$$ and $$q_2\xrightarrow{b}q_f$$, is $$ab$$ accepted?
JSON expected answer: No.
-/
theorem at_17_turn_05_oracle (m : Model) : ¬ (R m [0,1] ∩ {4}).Nonempty := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$R(w)$$ by propagating active states with the current branch rule, beginning with $$R(\varepsilon)=\{q_0\}$$ and no split yet used. What is $$R(\varepsilon)$$?
JSON expected answer: {q_0}
-/
theorem at_17_turn_06_oracle (m : Model) : R m []={0} := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$R(a)$$?
JSON expected answer: {q_1}
-/
theorem at_17_turn_07_oracle (m : Model) : R m [0]={1} := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, is $$R(ab)\cap F$$ nonempty?
JSON expected answer: No.
-/
theorem at_17_turn_08_oracle (m : Model) : ¬ (R m [0,1] ∩ {4}).Nonempty := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$R(c)$$?
JSON expected answer: cannot be determined
-/
theorem at_17_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => R m [2]) := by
  exact ⟨completion false,completion true,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what is $$\varepsilon\text{-closure}(q_0)$$?
JSON expected answer: cannot be determined
-/
theorem at_17_turn_10_oracle : Underdetermined (fun _ : Model × Finset Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,∅),(completion false,{0}),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can an accepting branch be lost immediately after a nondeterministic split?
JSON expected answer: Yes.
-/
theorem at_17_turn_11_oracle (m : Model) : 2 ∈ standardR m [0] ∧ 2 ∉ R m [0] ∧ (standardR m [0,1] ∩ {4}).Nonempty ∧ ¬ (R m [0,1] ∩ {4}).Nonempty := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does an NFA retain all branches after a nondeterministic split in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem at_17_turn_12_oracle (m : Model) : standardR m [0]={1,2} ∧ R m [0]≠{1,2} := by
  exact ⟨at_17_turn_01_oracle m,at_17_turn_04_oracle m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is $$ab$$ accepted in the standard NFA, and is it accepted in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem at_17_turn_13_oracle (m : Model) : (standardR m [0,1] ∩ {4}).Nonempty ∧ ¬ (R m [0,1] ∩ {4}).Nonempty := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard NFA. What active-state set follows from $$\delta(q_0,a)=\{q_1,q_2\}$$?
JSON expected answer: {q_1,q_2}
-/
theorem at_17_turn_14_oracle (m : Model) : standardR m [0]={1,2} := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard NFA, is $$R(ab)\cap F$$ nonempty?
JSON expected answer: Yes.
-/
theorem at_17_turn_15_oracle (m : Model) : (standardR m [0,1] ∩ {4}).Nonempty := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is $$ab$$ accepted?
JSON expected answer: No.
-/
theorem at_17_turn_16_oracle (m : Model) : ¬ (R m [0,1] ∩ {4}).Nonempty := by
  simp [R,standardR,advance,m.ha,m.hb1,m.hb2]
