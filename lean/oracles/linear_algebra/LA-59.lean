import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/linear_algebra/LA-59.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: LA-59 — Rank-nullity fails by one dimension unit
Source: test case definition test_cases/linear_algebra/LA-59.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace LA_59
open Benchmark

/-- A labelled reading is a natural number; subtraction is explicitly integral. -/
structure Model where
  rank : Nat → Nat
  nullity : Nat → Nat
  rt : rank 0 = 1
  nt : nullity 0 = 1
  rs : rank 1 = 2
  ns : nullity 1 = 1

def D (m : Model) (x : Nat) : Int := 3 - (m.rank x : Int) - (m.nullity x : Int)
def completion (k : Nat) : Model where
  rank := fun x => if x=0 then 1 else if x=1 then 2 else k
  nullity := fun x => if x=0 ∨ x=1 then 1 else 0
  rt := rfl
  nt := rfl
  rs := rfl
  ns := rfl

/-- Rank-nullity is the standard premise; its arithmetic consequence is separate. -/
def Standard (dim rank nullity : Nat) : Prop := dim = rank + nullity

end LA_59

open LA_59 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In ordinary finite-dimensional linear algebra, does rank-nullity give $$dim(V)=rank(T)+nullity(T)$$?
JSON expected answer: Yes.
-/
theorem la_59_turn_01_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) : Module.finrank 𝕜 V=Module.finrank 𝕜 T.range+Module.finrank 𝕜 T.ker := by
  exact T.finrank_range_add_finrank_ker.symm


/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In ordinary finite-dimensional linear algebra define the integer defect $$D(T)=dim(V)-rank(T)-nullity(T)$$ for a linear map with domain $$V$$. What is $$D(T)$$?
JSON expected answer: 0
-/
theorem la_59_turn_02_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) : (Module.finrank 𝕜 V : Int)-(Module.finrank 𝕜 T.range : Int)-(Module.finrank 𝕜 T.ker : Int)=0 := by
  have h := T.finrank_range_add_finrank_ker
  omega


/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use primitive natural-number dimension, rank, and nullity readings, without ordinary vector-space or rank-nullity axioms. For maps $$T,S$$ with the same labelled domain, stipulate $$dim(V)=3$$, $$rank(T)=1$$, $$nullity(T)=1$$, $$rank(S)=2$$, and $$nullity(S)=1$$. Arithmetic remains ordinary, with differences evaluated in the integers. Does rank-nullity hold for $$T$$?
JSON expected answer: No.
-/
theorem la_59_turn_03_oracle (m : Model) : 3 ≠ m.rank 0 + m.nullity 0 := by
  rw [m.rt,m.nt] <;> decide

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, is $$dim(V)=rank(T)+nullity(T)$$?
JSON expected answer: No.
-/
theorem la_59_turn_04_oracle (m : Model) : 3 ≠ m.rank 0 + m.nullity 0 := by
  rw [m.rt,m.nt] <;> decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, what is $$[dim(V)-rank(T)-nullity(T)]+[dim(V)-rank(S)-nullity(S)]$$?
JSON expected answer: 1
-/
theorem la_59_turn_05_oracle (m : Model) : D m 0 + D m 1 = 1 := by
  simp [D,m.rt,m.nt,m.rs,m.ns]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct the integer defect $$D(X)=dim(V)-rank(X)-nullity(X)$$. What is $$D(S)$$?
JSON expected answer: 0
-/
theorem la_59_turn_06_oracle (m : Model) : D m 1 = 0 := by
  simp [D,m.rt,m.nt,m.rs,m.ns]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$D(T)$$?
JSON expected answer: 1
-/
theorem la_59_turn_07_oracle (m : Model) : D m 0 = 1 := by
  simp [D,m.rt,m.nt,m.rs,m.ns]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$D(T)+D(S)=0$$ hold?
JSON expected answer: No.
-/
theorem la_59_turn_08_oracle (m : Model) : D m 0 + D m 1 ≠ 0 := by
  simp [D,m.rt,m.nt,m.rs,m.ns]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$D(R)$$ for another map on the same labelled domain?
JSON expected answer: cannot be determined
-/
theorem la_59_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => D m 2) := by
  exact ⟨completion 0,completion 1,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$det(T)$$?
JSON expected answer: cannot be determined
-/
theorem la_59_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can rank-nullity fail by one dimension unit?
JSON expected answer: Yes.
-/
theorem la_59_turn_11_oracle (m : Model) : D m 0 = 1 := by
  simp [D,m.rt,m.nt,m.rs,m.ns]

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$dim(V)=rank(T)+nullity(T)$$ hold in ordinary finite-dimensional linear algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem la_59_turn_12_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) (m : Model) : (Module.finrank 𝕜 V=Module.finrank 𝕜 T.range+Module.finrank 𝕜 T.ker) ∧ 3≠m.rank 0+m.nullity 0 := by
  exact ⟨T.finrank_range_add_finrank_ker.symm,by rw [m.rt,m.nt] <;> decide⟩


/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What nullity corresponds to $$dim(V)=3$$ and $$rank(T)=1$$ in the standard system, and what nullity is stipulated in the modified system?
JSON expected answer: 2 in the standard system and 1 in the modified system.
-/
theorem la_59_turn_13_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) (hd : Module.finrank 𝕜 V=3) (hr : Module.finrank 𝕜 T.range=1) (m : Model) : Module.finrank 𝕜 T.ker=2 ∧ m.nullity 0=1 := by
  have h := T.finrank_range_add_finrank_ker
  exact ⟨by omega,m.nt⟩


/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary linear algebra. If $$dim(V)=3$$ and $$rank(T)=1$$, what is $$nullity(T)$$?
JSON expected answer: 2
-/
theorem la_59_turn_14_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) (hd : Module.finrank 𝕜 V=3) (hr : Module.finrank 𝕜 T.range=1) : Module.finrank 𝕜 T.ker=2 := by
  have h := T.finrank_range_add_finrank_ker
  omega


/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary linear algebra, what is the rank-nullity defect $$dim(V)-rank(T)-nullity(T)$$?
JSON expected answer: 0
-/
theorem la_59_turn_15_oracle {𝕜 V W : Type} [Field 𝕜] [AddCommGroup V] [AddCommGroup W] [Module 𝕜 V] [Module 𝕜 W] [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) : (Module.finrank 𝕜 V : Int)-(Module.finrank 𝕜 T.range : Int)-(Module.finrank 𝕜 T.ker : Int)=0 := by
  have h := T.finrank_range_add_finrank_ker
  omega


/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$dim(V)-rank(T)-nullity(T)$$?
JSON expected answer: 1
-/
theorem la_59_turn_16_oracle (m : Model) : D m 0 = 1 := by
  simp [D,m.rt,m.nt,m.rs,m.ns]
