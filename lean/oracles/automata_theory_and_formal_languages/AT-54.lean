import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/automata_theory_and_formal_languages/AT-54.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AT-54 — Halt state continues for one extra step
Source: test case definition test_cases/automata_theory_and_formal_languages/AT-54.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AT_54
open Benchmark

/-- None means stopping. Labels r,h,h₂,k are 0,1,2,3. -/
structure Model where
  next : Nat → Option Nat
  hr : next 0=some 1
  hh : next 1=some 3
  hk : next 3=none

/-- A relational trace does not assume that every unknown execution terminates. -/
inductive Trace (next : Nat → Option Nat) : Nat → List Nat → Prop
  | stop {q} : next q=none → Trace next q [q]
  | step {q r xs} : next q=some r → Trace next r xs → Trace next q (q::xs)

def completion (extra : Bool) : Model where
  next := fun q => if q=0 then some 1 else if q=1 then some 3
    else if q=2 ∧ extra=true then some 3 else none
  hr := rfl
  hh := rfl
  hk := rfl

def standardNext (q : Nat) : Option Nat := if q=0 then some 1 else none

theorem fromK (m : Model) : Trace m.next 3 [3] := Trace.stop m.hk
theorem fromH (m : Model) : Trace m.next 1 [1,3] := Trace.step m.hh (fromK m)
theorem fromR (m : Model) : Trace m.next 0 [0,1,3] := Trace.step m.hr (fromH m)

theorem traceUnique {next : Nat → Option Nat} {q xs ys}
    (h : Trace next q xs) (k : Trace next q ys) : xs=ys := by
  induction h generalizing ys with
  | stop hs => cases k with
    | stop => rfl
    | step ht _ => simp_all
  | step hs ht ih => cases k with
    | stop hk => simp_all
    | step hk kt =>
      have e := Option.some.inj (hs.symm.trans hk)
      cases e
      exact congrArg (fun z => _ :: z) (ih kt)

end AT_54

open AT_54 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard machine model, does entering a halt state stop execution immediately?
JSON expected answer: Yes.
-/
theorem at_54_turn_01_oracle : standardNext 1=none := by
  rfl

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard machine, define $$T(q)$$ recursively as the list beginning at $$q$$ and following transitions until the stopping rule applies. If $$r\to h$$ and $$h$$ is a halt state, are there transitions in $$T(r)$$ after $$h$$?
JSON expected answer: No.
-/
theorem at_54_turn_02_oracle : Trace standardNext 0 [0,1] := by
  exact Trace.step rfl (Trace.stop rfl)

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now take distinct states $$r,h,h_2,k$$ and designate $$h,h_2$$ halt states, but do not infer a stopping rule from that designation alone. On first reaching $$h$$ take exactly one transition $$h\to k$$ and stop at $$k$$. Also stipulate $$r\to h$$; the rule at $$h_2$$ is unconstrained. After entering $$h$$, what next state is executed?
JSON expected answer: k
-/
theorem at_54_turn_03_oracle (m : Model) : m.next 1=some 3 := by
  exact m.hh

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does execution stop immediately upon first entering $$h$$?
JSON expected answer: No.
-/
theorem at_54_turn_04_oracle (m : Model) : m.next 1≠none := by
  rw [m.hh] <;> decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, after the transitions from $$r$$ through $$h$$ to $$k$$, does execution stop?
JSON expected answer: Yes.
-/
theorem at_54_turn_05_oracle (m : Model) : Trace m.next 0 [0,1,3] ∧ m.next 3=none := by
  exact ⟨fromR m,m.hk⟩

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$T(q)$$ as the state list obtained by following the supplied transitions and stopping rule. What is the final state of the base trace $$T(k)$$?
JSON expected answer: k
-/
theorem at_54_turn_06_oracle (m : Model) : Trace m.next 3 [3] ∧ ([3] : List Nat).getLast?=some 3 := by
  exact ⟨fromK m,rfl⟩

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, how many transitions occur in $$T(h)$$?
JSON expected answer: 1
-/
theorem at_54_turn_07_oracle (m : Model) : Trace m.next 1 [1,3] ∧ ([1,3] : List Nat).length-1=1 := by
  exact ⟨fromH m,rfl⟩

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, is $$T(r)=[r,h,k]$$?
JSON expected answer: Yes.
-/
theorem at_54_turn_08_oracle (m : Model) : Trace m.next 0 [0,1,3] := by
  exact fromR m

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$T(h_2)$$?
JSON expected answer: cannot be determined
-/
theorem at_54_turn_09_oracle : Underdetermined (fun p : Model × List Nat => Trace p.1.next 2 p.2) (fun p => p.2) := by
  exact ⟨(completion false,[2]),(completion true,[2,3]),Trace.stop rfl,Trace.step rfl (Trace.stop rfl),by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what output value is produced at $$k$$?
JSON expected answer: cannot be determined
-/
theorem at_54_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun p => p.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can a halt state execute one additional transition?
JSON expected answer: Yes.
-/
theorem at_54_turn_11_oracle (m : Model) : m.next 1=some 3 := by
  exact m.hh

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does immediate stopping upon entering $$h$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem at_54_turn_12_oracle (m : Model) : standardNext 1=none ∧ m.next 1≠none := by
  exact ⟨rfl,by rw [m.hh] <;> decide⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does execution stop at $$h$$ in the standard system, and does it stop immediately at $$h$$ in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem at_54_turn_13_oracle (m : Model) : standardNext 1=none ∧ m.next 1≠none := by
  exact ⟨rfl,by rw [m.hh] <;> decide⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard machine model. Does entering $$h$$ stop execution immediately?
JSON expected answer: Yes.
-/
theorem at_54_turn_14_oracle : standardNext 1=none := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard machine with $$r\to h$$, are there transitions in $$T(r)$$ after $$h$$?
JSON expected answer: No.
-/
theorem at_54_turn_15_oracle : Trace standardNext 0 [0,1] := by
  exact Trace.step rfl (Trace.stop rfl)

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What state is executed immediately after $$h$$?
JSON expected answer: k
-/
theorem at_54_turn_16_oracle (m : Model) : m.next 1=some 3 := by
  exact m.hh
