import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/automata_theory_and_formal_languages/AT-42.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AT-42 — Pop operation removes two symbols
Source: test case definition test_cases/automata_theory_and_formal_languages/AT-42.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AT_42
open Benchmark

structure Model where
  pop : List Nat → List Nat
  two : ∀ a b xs, pop (a::b::xs)=xs

def P (pop : List Nat → List Nat) : Nat → List Nat → List Nat
  | 0,s => s
  | n+1,s => pop (P pop n s)

def completion (short : List Nat) : Model where
  pop := fun s => match s with | _::_::xs => xs | _ => short
  two := by intros; rfl

def standardPop (s : List Nat) := s.tail

end AT_42

open AT_42 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard pushdown automaton, does a pop operation remove exactly one stack symbol?
JSON expected answer: Yes.
-/
theorem at_42_turn_01_oracle (a : Nat) (s : List Nat) : standardPop (a::s)=s := by
  rfl

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system, with stack top on the left, define $$P_0(s)=s$$ and $$P_{n+1}(s)=pop(P_n(s))$$ whenever the indicated pops are defined. What is $$P_2(ABCD)$$?
JSON expected answer: CD
-/
theorem at_42_turn_02_oracle : P standardPop 2 [0,1,2,3]=[2,3] := by
  rfl

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now let $$pop$$ be a total function on finite stack words. It removes exactly the top two symbols whenever at least two are present; outputs on shorter stacks are unconstrained. What is $$pop(ABCD)$$?
JSON expected answer: CD
-/
theorem at_42_turn_03_oracle (m : Model) : P m.pop 1 [0,1,2,3]=[2,3] := by
  simp [P,m.two]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does one pop of $$ABCD$$ produce the standard result $$BCD$$?
JSON expected answer: No.
-/
theorem at_42_turn_04_oracle (m : Model) : m.pop [0,1,2,3]≠[1,2,3] := by
  rw [m.two] <;> decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, what remains after two successive pops of $$ABCD$$?
JSON expected answer: \varepsilon
-/
theorem at_42_turn_05_oracle (m : Model) : P m.pop 2 [0,1,2,3]=[] := by
  simp [P,m.two]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$P_0(s)=s$$ and $$P_{n+1}(s)=pop(P_n(s))$$ for natural-number indices. What is $$P_0(ABCD)$$?
JSON expected answer: ABCD
-/
theorem at_42_turn_06_oracle (m : Model) : P m.pop 0 [0,1,2,3]=[0,1,2,3] := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$P_1(ABCD)$$?
JSON expected answer: CD
-/
theorem at_42_turn_07_oracle (m : Model) : P m.pop 1 [0,1,2,3]=[2,3] := by
  simp [P,m.two]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$P_2(ABCD)$$?
JSON expected answer: \varepsilon
-/
theorem at_42_turn_08_oracle (m : Model) : P m.pop 2 [0,1,2,3]=[] := by
  simp [P,m.two]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$P_1(A)$$?
JSON expected answer: cannot be determined
-/
theorem at_42_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => P m.pop 1 [0]) := by
  exact ⟨completion [],completion [1],trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what is $$push(A,BC)$$?
JSON expected answer: cannot be determined
-/
theorem at_42_turn_10_oracle : Underdetermined (fun _ : Model × List Nat => True) (fun m => m.2) := by
  exact ⟨(completion [],[]),(completion [],[0]),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, does each pop remove two symbols rather than one whenever at least two are present?
JSON expected answer: Yes.
-/
theorem at_42_turn_11_oracle (m : Model) (a b : Nat) (xs : List Nat) : (m.pop (a::b::xs)).length+2=(a::b::xs).length := by
  simp [m.two]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does one pop of $$ABCD$$ produce $$BCD$$ in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem at_42_turn_12_oracle (m : Model) : standardPop [0,1,2,3]=[1,2,3] ∧ m.pop [0,1,2,3]=[2,3] := by
  exact ⟨rfl,m.two 0 1 [2,3]⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What does one pop of $$ABCD$$ produce in the standard system, and what does it produce in the modified system?
JSON expected answer: BCD in the standard system and CD in the modified system.
-/
theorem at_42_turn_13_oracle (m : Model) : standardPop [0,1,2,3]=[1,2,3] ∧ m.pop [0,1,2,3]=[2,3] := by
  exact ⟨rfl,m.two 0 1 [2,3]⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard pushdown system. What does one pop do to $$ABCD$$?
JSON expected answer: BCD
-/
theorem at_42_turn_14_oracle : standardPop [0,1,2,3]=[1,2,3] := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, what remains after two pops of $$ABCD$$?
JSON expected answer: CD
-/
theorem at_42_turn_15_oracle : P standardPop 2 [0,1,2,3]=[2,3] := by
  rfl

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$P_1(ABCD)$$?
JSON expected answer: CD
-/
theorem at_42_turn_16_oracle (m : Model) : P m.pop 1 [0,1,2,3]=[2,3] := by
  simp [P,m.two]
