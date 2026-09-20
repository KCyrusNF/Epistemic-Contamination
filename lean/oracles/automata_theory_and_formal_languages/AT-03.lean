import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/automata_theory_and_formal_languages/AT-03.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AT-03 — Transition depends on input-position parity
Source: test case definition test_cases/automata_theory_and_formal_languages/AT-03.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AT_03
open Benchmark

/-- State false is q₀, true is q₁; symbol false is a, true is b. -/
def standardStep (q : Bool) (_ : Bool) := !q

def run (step : Bool → Bool → Nat → Bool) : Bool → List Bool → Nat → Bool
  | q, [], _ => q
  | q, x::xs, i => run step (step q x i) xs (i+1)

def step (b : Bool → Nat → Bool) (q x : Bool) (i : Nat) : Bool :=
  if x then b q i else if i % 2 = 1 then !q else q

def stdRun (q : Bool) (xs : List Bool) := run (fun q x _ => standardStep q x) q xs 1

end AT_03

open AT_03 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary DFA, does the transition $$\delta(q,a)$$ depend only on the current state $$q$$ and input symbol $$a$$, not on the input position?
JSON expected answer: Yes.
-/
theorem at_03_turn_01_oracle {Q Σ : Type} (δ : Q → Σ → Q) (q : Q) (x : Σ) (i j : Nat) :
    (fun _ : Nat => δ q x) i = (fun _ : Nat => δ q x) j := by
  rfl

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard DFA with $$\delta(q_0,a)=q_1$$ and $$\delta(q_1,a)=q_0$$, what is $$\delta^*(q_0,aa)$$?
JSON expected answer: q_0
-/
theorem at_03_turn_02_oracle : stdRun false [false,false] = false := by
  decide

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use distinct states $$q_0,q_1$$ and alphabet $$\{a,b\}$$. Input positions start at $$1$$. At odd positions, reading $$a$$ swaps the two states; at even positions, reading $$a$$ leaves either state unchanged. Transitions on $$b$$ are total but unconstrained. Starting in $$q_0$$ at position $$1$$, what state follows $$aa$$?
JSON expected answer: q_1
-/
theorem at_03_turn_03_oracle (b : Bool → Nat → Bool) : run (step b) false [false,false] 1 = true := by
  simp [run,step]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, is the state after $$aa$$ equal to the standard result $$q_0$$?
JSON expected answer: No.
-/
theorem at_03_turn_04_oracle (b : Bool → Nat → Bool) : run (step b) false [false,false] 1 ≠ false := by
  simp [run,step]

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, what state follows $$aaa$$ from $$q_0$$ starting at position $$1$$?
JSON expected answer: q_0
-/
theorem at_03_turn_05_oracle (b : Bool → Nat → Bool) : run (step b) false [false,false,false] 1 = false := by
  simp [run,step]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct extended transitions by $$\delta^*(q,\varepsilon;i)=q$$ and $$\delta^*(q,xw;i)=\delta^*(\delta(q,x;i),w;i+1)$$, where $$i$$ is the next input position. Omitted positions start at $$1$$. What is $$\delta^*(q_0,\varepsilon)$$?
JSON expected answer: q_0
-/
theorem at_03_turn_06_oracle (b : Bool → Nat → Bool) : run (step b) false [] 1 = false := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$\delta^*(q_1,a;2)$$?
JSON expected answer: q_1
-/
theorem at_03_turn_07_oracle (b : Bool → Nat → Bool) : run (step b) true [false] 2 = true := by
  simp [run,step]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$\delta^*(q_0,aa)$$?
JSON expected answer: q_1
-/
theorem at_03_turn_08_oracle (b : Bool → Nat → Bool) : run (step b) false [false,false] 1 = true := by
  simp [run,step]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$\delta^*(q_0,b)$$?
JSON expected answer: cannot be determined
-/
theorem at_03_turn_09_oracle : Underdetermined (fun _ : Bool → Nat → Bool => True) (fun b => run (step b) false [true] 1) := by
  exact ⟨(fun _ _ => false),(fun _ _ => true),trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is the accepting-state set $$F$$?
JSON expected answer: cannot be determined
-/
theorem at_03_turn_10_oracle : Underdetermined (fun _ : (Bool → Nat → Bool) × Finset Bool => True) (fun m => m.2) := by
  exact ⟨((fun _ _ => false),∅),((fun _ _ => false),{false}),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can the same state-symbol pair have different outcomes at different input positions?
JSON expected answer: Yes.
-/
theorem at_03_turn_11_oracle (b : Bool → Nat → Bool) : step b false false 1 ≠ step b false false 2 := by
  simp [step]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does position-independence of $$\delta(q,a)$$ hold in an ordinary DFA, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem at_03_turn_12_oracle (b : Bool → Nat → Bool) :
    (∀ q x i j, (fun _ : Nat => standardStep q x) i = (fun _ : Nat => standardStep q x) j) ∧
    ¬ (∀ q x i j, step b q x i = step b q x j) := by
  constructor
  · intros; rfl
  · intro h
    have bad := h false false 1 2
    simp [step] at bad

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What state is reached from $$q_0$$ on $$aa$$ in the standard DFA, and what state is reached in the modified system?
JSON expected answer: q_0 in the standard system and q_1 in the modified system.
-/
theorem at_03_turn_13_oracle (b : Bool → Nat → Bool) : stdRun false [false,false]=false ∧ run (step b) false [false,false] 1=true ∧ step b false false 1≠step b false false 2 := by
  simp [stdRun,run,standardStep,step]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard DFA. What is $$\delta(q_1,a)$$?
JSON expected answer: q_0
-/
theorem at_03_turn_14_oracle : standardStep true false=false := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard DFA, what is $$\delta^*(q_0,aaa)$$?
JSON expected answer: q_1
-/
theorem at_03_turn_15_oracle : stdRun false [false,false,false]=true := by
  decide

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$\delta^*(q_0,aa)$$?
JSON expected answer: q_1
-/
theorem at_03_turn_16_oracle (b : Bool → Nat → Bool) : run (step b) false [false,false] 1 = true := by
  simp [run,step]
