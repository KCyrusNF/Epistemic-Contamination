import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/formal_logics_and_proof_systems/FL-10.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: FL-10 — Conjunction elimination returns only first conjunct
Source: test case definition test_cases/formal_logics_and_proof_systems/FL-10.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace FL_10
open Benchmark

inductive Formula where
  | atom (n : Nat) | conj (left right : Formula)
  deriving DecidableEq
abbrev A := Formula.atom 0
abbrev B := Formula.atom 1
abbrev C := Formula.atom 2
abbrev D := Formula.atom 3
abbrev AB := Formula.conj A B
abbrev CD := Formula.conj C D
abbrev nested := Formula.conj AB CD
def standardProject : Formula → Finset Formula
  | .conj l r => {l,r}
  | .atom _ => ∅
def project (free : Formula → Finset Formula) : Formula → Finset Formula
  | .conj l _ => {l}
  | f => free f
def setProject (p : Formula → Finset Formula) (s : Finset Formula) := s.biUnion p

end FL_10

open FL_10 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard proof system, from $$A\land B$$ can both $$A$$ and $$B$$ be derived by conjunction elimination?
JSON expected answer: Yes.
-/
theorem fl_10_turn_01_oracle : A ∈ standardProject AB ∧ B ∈ standardProject AB := by
  decide

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system let $$\pi(X\land Y)=\{X,Y\}$$ and extend $$\pi$$ to sets by union of its values. Does $$B\in\pi(\pi(\{(A\land B)\land(C\land D)\}))$$ hold?
JSON expected answer: Yes.
-/
theorem fl_10_turn_02_oracle : B ∈ setProject standardProject (setProject standardProject {nested}) := by
  decide

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use syntactic formulas with distinct atoms. Modify one-step conjunction elimination so $$\pi(X\land Y)=\{X\}$$. Let $$\pi$$ be a total set-valued operation on formulas; its values on nonconjunctions are unconstrained. No other elimination or formula-reordering rules are supplied. From $$A\land B$$, does this elimination return $$B$$?
JSON expected answer: No.
-/
theorem fl_10_turn_03_oracle (free : Formula → Finset Formula) : B ∉ project free AB := by
  simp [project,setProject,standardProject,A,B,C,D,AB,CD,nested]

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does conjunction elimination yield the second conjunct $$B$$ from $$A\land B$$?
JSON expected answer: No.
-/
theorem fl_10_turn_04_oracle (free : Formula → Finset Formula) : B ∉ project free AB := by
  simp [project,setProject,standardProject,A,B,C,D,AB,CD,nested]

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, from $$(A\land B)\land C$$, can $$A$$ be obtained by applying conjunction elimination twice?
JSON expected answer: Yes.
-/
theorem fl_10_turn_05_oracle (free : Formula → Finset Formula) : A ∈ setProject (project free) (setProject (project free) {Formula.conj AB C}) := by
  simp [project,setProject,standardProject,A,B,C,D,AB,CD,nested]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct setwise projection $$\pi(S)=\bigcup_{F\in S}\pi(F)$$ using the current one-step elimination. What is $$\pi(\varnothing)$$?
JSON expected answer: {}
-/
theorem fl_10_turn_06_oracle (free : Formula → Finset Formula) : setProject (project free) ∅ = ∅ := by
  simp [project,setProject,standardProject,A,B,C,D,AB,CD,nested]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$\pi(\{(A\land B)\land(C\land D)\})$$?
JSON expected answer: {A\land B}
-/
theorem fl_10_turn_07_oracle (free : Formula → Finset Formula) : setProject (project free) {nested} = {AB} := by
  simp [project,setProject,standardProject,A,B,C,D,AB,CD,nested]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$\pi(\pi(\{(A\land B)\land(C\land D)\}))$$?
JSON expected answer: {A}
-/
theorem fl_10_turn_08_oracle (free : Formula → Finset Formula) : setProject (project free) (setProject (project free) {nested}) = {A} := by
  simp [project,setProject,standardProject,A,B,C,D,AB,CD,nested]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$\pi(\{A\})$$?
JSON expected answer: cannot be determined
-/
theorem fl_10_turn_09_oracle : Underdetermined (fun _ : Formula → Finset Formula => True) (fun free => setProject (project free) {A}) := by
  exact ⟨(fun _ => ∅),(fun _ => {B}),True.intro,True.intro,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what truth value does a valuation assign to $$A$$?
JSON expected answer: cannot be determined
-/
theorem fl_10_turn_10_oracle : Underdetermined (fun _ : Bool => True) id := by
  exact ⟨false,true,True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In the modified system, is conjunction elimination guaranteed to recover both distinct conjuncts of every conjunction?
JSON expected answer: No.
-/
theorem fl_10_turn_11_oracle (free : Formula → Finset Formula) : ¬ (∀ l r, r ∈ project free (.conj l r)) := by
  intro h; have bad := h A B; simp [project,setProject,standardProject,A,B,C,D,AB,CD,nested] at bad

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement “one application of conjunction elimination returns $$B$$ from $$A\land B$$” hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem fl_10_turn_12_oracle (free : Formula → Finset Formula) : B ∈ standardProject AB ∧ B ∉ project free AB := by
  simp [project,setProject,standardProject,A,B,C,D,AB,CD,nested]

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does one application of conjunction elimination return $$B$$ from $$A\land B$$ in the standard system, and does it do so in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem fl_10_turn_13_oracle (free : Formula → Finset Formula) : B ∈ standardProject AB ∧ B ∉ project free AB := by
  simp [project,setProject,standardProject,A,B,C,D,AB,CD,nested]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard proof system. Does one application of conjunction elimination return $$B$$ from $$A\land B$$?
JSON expected answer: Yes.
-/
theorem fl_10_turn_14_oracle : B ∈ standardProject AB := by
  decide

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, does $$B\in\pi(\pi(\{(A\land B)\land(C\land D)\}))$$ hold?
JSON expected answer: Yes.
-/
theorem fl_10_turn_15_oracle : B ∈ setProject standardProject (setProject standardProject {nested}) := by
  decide

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$\pi(A\land B)$$?
JSON expected answer: {A}
-/
theorem fl_10_turn_16_oracle (free : Formula → Finset Formula) : project free AB = {A} := by
  simp [project,setProject,standardProject,A,B,C,D,AB,CD,nested]
