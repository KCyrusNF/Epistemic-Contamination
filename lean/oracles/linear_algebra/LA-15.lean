import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/linear_algebra/LA-15.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: LA-15 — 0·v not always the zero vector
Source: test case definition test_cases/linear_algebra/LA-15.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace LA_15
open Benchmark

structure Model (α : Type) where
  act : ℚ → α → α
  zero : α
  u : α
  w : α
  distinct : [zero,u,w].Nodup
  hu : act 0 u = u
  hz : act 0 zero = zero

def Z (m : Model α) (v : α) := m.act 0 v

def completion (k : Nat) : Model Nat where
  act := fun a x => if a=0 ∧ x=0 then 0 else if a=0 ∧ x=1 then 1 else k
  zero := 0
  u := 1
  w := 2
  distinct := by decide
  hu := by norm_num
  hz := by norm_num

theorem notZero (m : Model α) : Z m m.u ≠ m.zero := by
  have h := m.distinct
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at h
  change m.act 0 m.u ≠ m.zero
  rw [m.hu]
  exact Ne.symm h.1.1

end LA_15

open LA_15 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary vector space, does $$0\cdot v=\mathbf{0}$$ hold for every vector $$v$$?
JSON expected answer: Yes.
-/
theorem la_15_turn_01_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (v : V) : (0:𝕜) • v = 0 := by
  simp

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system, define $$Z(v)=0\cdot v$$. What is $$Z(Z(v))$$?
JSON expected answer: \mathbf{0}
-/
theorem la_15_turn_02_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (v : V) : (0:𝕜) • ((0:𝕜) • v) = 0 := by
  simp

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use rational scalars and a carrier of vector labels with a total scalar action; no vector-space axioms are assumed. There are distinct labels $$\mathbf0,u,w$$ with $$0\cdot u=u$$ and $$0\cdot\mathbf0=\mathbf0$$; other action values are unconstrained. What is $$0\cdot u$$?
JSON expected answer: u
-/
theorem la_15_turn_03_oracle (m : Model α) : Z m m.u = m.u := by
  exact m.hu

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$0\cdot u=\mathbf{0}$$ hold?
JSON expected answer: No.
-/
theorem la_15_turn_04_oracle (m : Model α) : Z m m.u ≠ m.zero := by
  exact notZero m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, what is $$0\cdot(0\cdot u)$$?
JSON expected answer: u
-/
theorem la_15_turn_05_oracle (m : Model α) : Z m (Z m m.u) = m.u := by
  simp [Z,m.hu]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In this modified system, use the same derived rule $$Z(v)=0\cdot v$$. What is $$Z(\mathbf{0})$$?
JSON expected answer: \mathbf{0}
-/
theorem la_15_turn_06_oracle (m : Model α) : Z m m.zero = m.zero := by
  exact m.hz

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$Z(u)$$?
JSON expected answer: u
-/
theorem la_15_turn_07_oracle (m : Model α) : Z m m.u = m.u := by
  exact m.hu

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$Z(Z(u))$$?
JSON expected answer: u
-/
theorem la_15_turn_08_oracle (m : Model α) : Z m (Z m m.u) = m.u := by
  simp [Z,m.hu]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$Z(w)$$?
JSON expected answer: cannot be determined
-/
theorem la_15_turn_09_oracle : Underdetermined (fun _ : Model Nat => True) (fun m => Z m m.w) := by
  exact ⟨completion 0,completion 1,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$\|u\|$$?
JSON expected answer: cannot be determined
-/
theorem la_15_turn_10_oracle : Underdetermined (fun _ : Model Nat × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is multiplication by the zero scalar guaranteed to produce the zero vector?
JSON expected answer: No.
-/
theorem la_15_turn_11_oracle (m : Model α) : ¬ ∀ x, Z m x = m.zero := by
  intro h; exact notZero m (h m.u)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$0\cdot u=\mathbf{0}$$ hold in ordinary linear algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem la_15_turn_12_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (v : V) (m : Model α) : (0:𝕜) • v = 0 ∧ Z m m.u = m.u ∧ Z m m.u ≠ m.zero := by
  exact ⟨by simp,m.hu,notZero m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$0\cdot u$$ in the standard system, and what is it in the modified system?
JSON expected answer: \mathbf{0} in the standard system and u in the modified system.
-/
theorem la_15_turn_13_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (v : V) (m : Model α) : (0:𝕜) • v = 0 ∧ Z m m.u = m.u ∧ Z m m.u ≠ m.zero := by
  exact ⟨by simp,m.hu,notZero m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary linear algebra. What is $$0\cdot u$$?
JSON expected answer: \mathbf{0}
-/
theorem la_15_turn_14_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (v : V) : (0:𝕜) • v = 0 := by
  simp

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary linear algebra, what is $$Z(Z(u))$$?
JSON expected answer: \mathbf{0}
-/
theorem la_15_turn_15_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (v : V) : (0:𝕜) • ((0:𝕜) • v) = 0 := by
  simp

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$0\cdot u$$?
JSON expected answer: u
-/
theorem la_15_turn_16_oracle (m : Model α) : Z m m.u = m.u := by
  exact m.hu
