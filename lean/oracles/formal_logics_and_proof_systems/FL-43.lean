import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/formal_logics_and_proof_systems/FL-43.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: FL-43 — Contraction invalid; duplicate premises matter
Source: test case definition test_cases/formal_logics_and_proof_systems/FL-43.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace FL_43
open Benchmark

structure Standard where
  D : Nat → Bool
  contract : ∀ n, D (n+2) = true → D (n+1) = true
  weaken : ∀ n, D n = true → D (n+1) = true
structure Model where
  D : Nat → Bool
  two : D 2 = true
  one : D 1 = false
def Safe (D : Nat → Bool) (n k : Nat) := (List.range (k+1)).all (fun j => D (n-j))
def completion (free : Bool) : Model where
  D := fun n => if n=2 then true else if n=1 then false else free
  two := by norm_num
  one := by norm_num
theorem standardSafe (s : Standard) (h : s.D 4 = true) : Safe s.D 4 2 = true := by
  have h3 := s.contract 2 h
  have h2 := s.contract 1 h3
  simp [Safe,List.range_succ,h,h3,h2]

end FL_43

open FL_43 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard structural proof system with contraction and weakening, do duplicate copies of a premise leave derivability unchanged?
JSON expected answer: Yes.
-/
theorem fl_43_turn_01_oracle (s : Standard) (n : Nat) : s.D (n+2) = true ↔ s.D (n+1) = true := by
  exact ⟨s.contract n, s.weaken (n+1)⟩

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$D(n)\iff A^n\vdash B$$ and $$Safe(n,k)\iff\bigwedge_{j=0}^{k}D(n-j)$$ for $$k\leq n$$, where $$A^n$$ contains exactly $$n$$ copies. If $$D(4)$$ holds, does $$Safe(4,2)$$ follow by contraction?
JSON expected answer: Yes.
-/
theorem fl_43_turn_02_oracle (s : Standard) (h : s.D 4 = true) : Safe s.D 4 2 = true := by
  exact standardSafe s h

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a syntactic derivability relation on multisets of premises. Stipulate $$A,A\vdash B$$ and $$A\nvdash B$$, while other contexts are unconstrained; contraction and weakening are not assumed. Does $$A\vdash B$$ hold?
JSON expected answer: No.
-/
theorem fl_43_turn_03_oracle (m : Model) : m.D 1 = false := by
  exact m.one

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does contraction from $$A,A\vdash B$$ to $$A\vdash B$$ succeed?
JSON expected answer: No.
-/
theorem fl_43_turn_04_oracle (m : Model) : ¬ (m.D 2 = true → m.D 1 = true) := by
  intro h; have bad := h m.two; rw [m.one] at bad; contradiction

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does repeatedly deleting a duplicate from $$A,A\vdash B$$ preserve derivability after the first deletion?
JSON expected answer: No.
-/
theorem fl_43_turn_05_oracle (m : Model) : Safe m.D 2 1 = false := by
  simp [Safe,List.range_succ,m.two,m.one]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$D(n)\iff A^n\vdash B$$, where $$A^n$$ is the multiset of exactly $$n$$ copies. Define $$Safe(n,k)$$ to require $$D(n),D(n-1),\ldots,D(n-k)$$ for $$0\leq k\leq n$$, using ordinary indexing. Does $$Safe(2,0)$$ hold?
JSON expected answer: Yes.
-/
theorem fl_43_turn_06_oracle (m : Model) : Safe m.D 2 0 = true := by
  simp [Safe,List.range_succ,m.two,m.one]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$Safe(2,1)$$ hold?
JSON expected answer: No.
-/
theorem fl_43_turn_07_oracle (m : Model) : Safe m.D 2 1 = false := by
  simp [Safe,List.range_succ,m.two,m.one]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$Safe(2,2)$$ hold?
JSON expected answer: No.
-/
theorem fl_43_turn_08_oracle (m : Model) : Safe m.D 2 2 = false := by
  simp [Safe,List.range_succ,m.two,m.one]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$D(4)$$ hold?
JSON expected answer: cannot be determined
-/
theorem fl_43_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => m.D 4) := by
  exact ⟨completion false,completion true,True.intro,True.intro,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is the truth value of $$A$$?
JSON expected answer: cannot be determined
-/
theorem fl_43_turn_10_oracle : Underdetermined (fun _ : Model × Bool => True) (fun m => m.2) := by
  exact ⟨(completion false,false),(completion false,true),True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can deleting a duplicate premise change derivability?
JSON expected answer: Yes.
-/
theorem fl_43_turn_11_oracle (m : Model) : m.D 2 ≠ m.D 1 := by
  rw [m.two,m.one] <;> decide

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does contraction from $$A,A\vdash B$$ to $$A\vdash B$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem fl_43_turn_12_oracle (s : Standard) (m : Model) : (s.D 2 = true → s.D 1 = true) ∧ ¬ (m.D 2 = true → m.D 1 = true) := by
  constructor
  · exact s.contract 0
  · intro h; have bad := h m.two; rw [m.one] at bad; contradiction

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does $$A\vdash B$$ follow from $$A,A\vdash B$$ in the standard system, and does it follow in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem fl_43_turn_13_oracle (s : Standard) (m : Model) : (s.D 2 = true → s.D 1 = true) ∧ ¬ (m.D 2 = true → m.D 1 = true) := by
  constructor
  · exact s.contract 0
  · intro h; have bad := h m.two; rw [m.one] at bad; contradiction

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard proof system. If $$A,A\vdash B$$, does $$A\vdash B$$ follow?
JSON expected answer: Yes.
-/
theorem fl_43_turn_14_oracle (s : Standard) (h : s.D 2 = true) : s.D 1 = true := by
  exact s.contract 0 h

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, does $$D(4)$$ imply $$Safe(4,2)$$?
JSON expected answer: Yes.
-/
theorem fl_43_turn_15_oracle (s : Standard) (h : s.D 4 = true) : Safe s.D 4 2 = true := by
  exact standardSafe s h

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$A\vdash B$$ hold?
JSON expected answer: No.
-/
theorem fl_43_turn_16_oracle (m : Model) : m.D 1 = false := by
  exact m.one
