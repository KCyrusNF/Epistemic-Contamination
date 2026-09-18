import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/formal_logics_and_proof_systems/FL-52.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: FL-52 — Additional premise can destroy derivability
Source: test case definition test_cases/formal_logics_and_proof_systems/FL-52.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace FL_52
open Benchmark

-- Added B,C,D are encoded as 0,1,2, respectively.
def W (free : List Nat → Bool) (xs : List Nat) : Bool :=
  if xs.all (fun x => x==0 || x==1) then !(xs.contains 0) else free xs
structure Standard where
  W : List Nat → Prop
  base : W []
  weaken : ∀ xs x, W xs → W (xs ++ [x])

end FL_52

open FL_52 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard monotonic proof system with weakening, if $$\Gamma\vdash A$$, does $$\Gamma,B\vdash A$$ also hold?
JSON expected answer: Yes.
-/
theorem fl_52_turn_01_oracle (s : Standard) : s.W [0] := by
  exact s.weaken [] 0 s.base

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system, suppose $$\Gamma\vdash A$$. Define $$W(L)\iff\Gamma,L\vdash A$$ for a finite list of added premises. Does $$W([B,C])$$ hold?
JSON expected answer: Yes.
-/
theorem fl_52_turn_02_oracle (s : Standard) : s.W [0,1] := by
  exact s.weaken [0] 1 (s.weaken [] 0 s.base)

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a syntactic derivability relation with distinct atoms $$A,B,C,D$$ and fixed context $$\Gamma$$. For any list consisting only of $$B,C$$, stipulate $$\Gamma,L\vdash A$$ exactly when $$B$$ is absent from $$L$$. Contexts involving other added atoms are unconstrained; no weakening or cut rule is assumed. Does $$\Gamma,B\vdash A$$ hold?
JSON expected answer: No.
-/
theorem fl_52_turn_03_oracle (free : List Nat → Bool) : W free [0] = false := by
  simp [W]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does standard weakening preserve $$A$$ after adding $$B$$?
JSON expected answer: No.
-/
theorem fl_52_turn_04_oracle (free : List Nat → Bool) : W free [0] = false := by
  simp [W]

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$\Gamma,C,C\vdash A$$ hold?
JSON expected answer: Yes.
-/
theorem fl_52_turn_05_oracle (free : List Nat → Bool) : W free [1,1] = true := by
  simp [W]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$W(L)\iff\Gamma,L\vdash A$$, appending the listed premises to the fixed context. Does $$W([])$$ hold?
JSON expected answer: Yes.
-/
theorem fl_52_turn_06_oracle (free : List Nat → Bool) : W free [] = true := by
  simp [W]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$W([B])$$ hold?
JSON expected answer: No.
-/
theorem fl_52_turn_07_oracle (free : List Nat → Bool) : W free [0] = false := by
  simp [W]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$W([C,B,C])$$ hold?
JSON expected answer: No.
-/
theorem fl_52_turn_08_oracle (free : List Nat → Bool) : W free [1,0,1] = false := by
  simp [W]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$W([D])$$ hold?
JSON expected answer: cannot be determined
-/
theorem fl_52_turn_09_oracle : Underdetermined (fun _ : List Nat → Bool => True) (fun free => W free [2]) := by
  exact ⟨(fun _ => false),(fun _ => true),True.intro,True.intro,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is the truth value of $$B$$?
JSON expected answer: cannot be determined
-/
theorem fl_52_turn_10_oracle : Underdetermined (fun _ : Bool => True) id := by
  exact ⟨false,true,True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can adding a premise destroy derivability?
JSON expected answer: Yes.
-/
theorem fl_52_turn_11_oracle (free : List Nat → Bool) : W free [] = true ∧ W free [0] = false := by
  simp [W]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does weakening by the premise $$B$$ preserve derivability in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem fl_52_turn_12_oracle (s : Standard) (free : List Nat → Bool) : s.W [0] ∧ W free [0] = false := by
  constructor
  · exact s.weaken [] 0 s.base
  · simp [W]

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does $$\Gamma,B\vdash A$$ follow from $$\Gamma\vdash A$$ in the standard system, and does it follow in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem fl_52_turn_13_oracle (s : Standard) (free : List Nat → Bool) : s.W [0] ∧ W free [0] = false := by
  constructor
  · exact s.weaken [] 0 s.base
  · simp [W]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard proof system. If $$\Gamma\vdash A$$, does $$\Gamma,B\vdash A$$ follow?
JSON expected answer: Yes.
-/
theorem fl_52_turn_14_oracle (s : Standard) : s.W [0] := by
  exact s.weaken [] 0 s.base

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system with $$\Gamma\vdash A$$, does $$W([B,C])$$ hold?
JSON expected answer: Yes.
-/
theorem fl_52_turn_15_oracle (s : Standard) : s.W [0,1] := by
  exact s.weaken [0] 1 (s.weaken [] 0 s.base)

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does adding $$B$$ to $$\Gamma$$ preserve derivability of $$A$$?
JSON expected answer: No.
-/
theorem fl_52_turn_16_oracle (free : List Nat → Bool) : W free [0] = false := by
  simp [W]
