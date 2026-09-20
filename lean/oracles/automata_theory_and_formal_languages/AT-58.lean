import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/automata_theory_and_formal_languages/AT-58.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AT-58 — Decider fails to halt on one finite input family
Source: test case definition test_cases/automata_theory_and_formal_languages/AT-58.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AT_58
open Benchmark

abbrev Word := List Bool
structure Machine (C : Type) where
  start : Word → C
  step : C → C
  final : C → Prop

def state (D : Machine C) (w : Word) (n : Nat) := (D.step^[n]) (D.start w)
def H (D : Machine C) (w : Word) := ∃ n, D.final (state D w n)
def All (D : Machine C) : List Word → Prop
  | [] => True
  | w::ws => H D w ∧ All D ws

def Decider (D : Machine C) := ∀ w, H D w
structure Model (C : Type) extends Machine C where
  loop0 : step (start [false])=start [false]
  loop00 : step (start [false,false])=start [false,false]
  no0 : ¬ final (start [false])
  no00 : ¬ final (start [false,false])
  yes1 : final (start [true])

theorem fixedState (D : Machine C) (w : Word) (h : D.step (D.start w)=D.start w) (n : Nat) :
    state D w n=D.start w := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [state,Function.iterate_succ_apply',h] using congrArg D.step ih

theorem noH (m : Model C) : ¬ H m.toMachine [false] := by
  rintro ⟨n,hn⟩
  rw [fixedState _ _ m.loop0 n] at hn
  exact m.no0 hn

/-- Concrete completions vary only unspecified inputs. -/
def completion (extra : Bool) : Model Word where
  start := id
  step := id
  final := fun w => w=[true] ∨ (extra=true ∧ w=[false,false,false])
  loop0 := rfl
  loop00 := rfl
  no0 := by simp
  no00 := by simp
  yes1 := by simp

theorem completeH (extra : Bool) : H (completion extra).toMachine [false,false,false] ↔ extra=true := by
  constructor
  · rintro ⟨n,hn⟩
    rw [fixedState _ _ rfl n] at hn
    simpa [completion] using hn
  · intro h; exact ⟨0,Or.inr ⟨h,rfl⟩⟩

end AT_58

open AT_58 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: By definition, does a standard decider halt on every finite input?
JSON expected answer: Yes.
-/
theorem at_58_turn_01_oracle (D : Machine C) (h : Decider D) (w : Word) : H D w := by
  exact h w

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: For a standard decider $$D$$ define $$H(w)$$ as halting on word $$w$$ and $$All([])=true$$, $$All([w]+L)\iff H(w)\land All(L)$$. Does $$All([0,00])$$ hold?
JSON expected answer: Yes.
-/
theorem at_58_turn_02_oracle (D : Machine C) (h : Decider D) : All D [[false],[false,false]] := by
  exact ⟨h _,h _,trivial⟩

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a machine carrying the label decider without assuming total halting. On each of the two words $$0$$ and $$00$$ its initial configuration has a self-loop and is nonhalting; on $$1$$ it halts immediately. All other input behavior is unconstrained. Does it halt on $$0$$?
JSON expected answer: No.
-/
theorem at_58_turn_03_oracle (m : Model C) : ¬ H m.toMachine [false] := by
  exact noH m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard decider requirement hold for input $$0$$?
JSON expected answer: No.
-/
theorem at_58_turn_04_oracle (m : Model C) : ¬ H m.toMachine [false] := by
  exact noH m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, after two transitions on input $$00$$, has the machine reached a halting configuration?
JSON expected answer: No.
-/
theorem at_58_turn_05_oracle (m : Model C) : ¬ m.final (state m.toMachine [false,false] 2) := by
  rw [fixedState _ _ m.loop00 2]; exact m.no00

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$H(w)$$ as halting and $$All([])=true$$, $$All([w]+L)\iff H(w)\land All(L)$$. Does $$All([])$$ hold?
JSON expected answer: Yes.
-/
theorem at_58_turn_06_oracle (m : Model C) : All m.toMachine [] := by
  trivial

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, does $$H(0)$$ hold?
JSON expected answer: No.
-/
theorem at_58_turn_07_oracle (m : Model C) : ¬ H m.toMachine [false] := by
  exact noH m

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$All([1,0,00])$$ hold?
JSON expected answer: No.
-/
theorem at_58_turn_08_oracle (m : Model C) : ¬ All m.toMachine [[true],[false],[false,false]] := by
  intro h; exact noH m h.2.1

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$H(000)$$ hold?
JSON expected answer: cannot be determined
-/
theorem at_58_turn_09_oracle : Underdetermined (fun _ : Model Word => True) (fun m => H m.toMachine [false,false,false]) := by
  refine ⟨completion false,completion true,trivial,trivial,?_⟩; intro h; have hh := h.mpr ((completeH true).mpr rfl); have bad := (completeH false).mp hh; contradiction

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what output word does $$output(D,1)$$ return?
JSON expected answer: cannot be determined
-/
theorem at_58_turn_10_oracle : Underdetermined (fun _ : Model Word × Word => True) (fun p => p.2) := by
  exact ⟨(completion false,[]),(completion false,[true]),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can a machine called a decider fail to halt on a finite input?
JSON expected answer: Yes.
-/
theorem at_58_turn_11_oracle (m : Model C) : ¬ Decider m.toMachine := by
  intro h; exact noH m (h [false])

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the requirement “halts on every finite input” hold for a standard decider, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem at_58_turn_12_oracle (D : Machine C) (h : Decider D) (m : Model U) :
    Decider D ∧ ¬ Decider m.toMachine := by
  exact ⟨h,at_58_turn_11_oracle m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does the machine halt on $$0$$ in the standard system, and does it halt on $$0$$ in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem at_58_turn_13_oracle (D : Machine C) (h : Decider D) (m : Model U) : H D [false] ∧ ¬ H m.toMachine [false] := by
  exact ⟨h _,noH m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard definition of decider. Must a decider halt on input $$0$$?
JSON expected answer: Yes.
-/
theorem at_58_turn_14_oracle (D : Machine C) (h : Decider D) : H D [false] := by
  exact h _

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard decider, does $$All([0,00])$$ hold?
JSON expected answer: Yes.
-/
theorem at_58_turn_15_oracle (D : Machine C) (h : Decider D) : All D [[false],[false,false]] := by
  exact ⟨h _,h _,trivial⟩

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$H(0)$$ hold?
JSON expected answer: No.
-/
theorem at_58_turn_16_oracle (m : Model C) : ¬ H m.toMachine [false] := by
  exact noH m
