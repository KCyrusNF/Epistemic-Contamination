import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/linear_algebra/LA-60.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: LA-60 — det(AB) ≠ det(A)det(B) for one matrix pair
Source: test case definition test_cases/linear_algebra/LA-60.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace LA_60
open Benchmark

abbrev Mat := Matrix (Fin 2) (Fin 2) ℚ
structure Model (n : Type) [Fintype n] [DecidableEq n] where
  det : Matrix n n ℚ → ℚ
  A : Matrix n n ℚ
  B : Matrix n n ℚ
  C : Matrix n n ℚ
  ha : det A=2
  hb : det B=3
  hab : det (A*B)=5
  hba : det (B*A)=6

def Delta [Fintype n] [DecidableEq n] (m : Model n) (X Y : Matrix n n ℚ) :=
  m.det (X*Y)-m.det X*m.det Y

def A : Mat := !![2,0;0,1]
def B : Mat := !![1,1;0,1]
/-- This arbitrary function reads two entries; matrix multiplication stays standard. -/
def fake (k : ℚ) (M : Mat) : ℚ :=
  if M 0 0=2 ∧ M 0 1=0 then 2 else if M 0 0=1 ∧ M 0 1=1 then 3
  else if M 0 0=2 ∧ M 0 1=2 then 5 else if M 0 0=2 ∧ M 0 1=1 then 6 else k

def completion (k : ℚ) : Model (Fin 2) where
  det := fake k
  A := A
  B := B
  C := 1
  ha := by norm_num [fake,A]
  hb := by norm_num [fake,B]
  hab := by norm_num [fake,A,B,Matrix.mul_apply,Fin.sum_univ_two]
  hba := by norm_num [fake,A,B,Matrix.mul_apply,Fin.sum_univ_two]

end LA_60

open LA_60 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: For ordinary square matrices, does $$det(AB)=det(A)det(B)$$ hold?
JSON expected answer: Yes.
-/
theorem la_60_turn_01_oracle {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℚ) : (A*B).det=A.det*B.det := by
  exact Matrix.det_mul A B

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: For ordinary square rational matrices define $$\Delta(X,Y)=det(XY)-det(X)det(Y)$$. What is $$\Delta(A,B)$$?
JSON expected answer: 0
-/
theorem la_60_turn_02_oracle {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℚ) : (A*B).det-A.det*B.det=0 := by
  rw [Matrix.det_mul] <;> ring

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a rational-valued function written $$det$$ on square rational matrices, without the ordinary determinant axioms. Matrix multiplication and rational arithmetic remain ordinary. Stipulate $$det(A)=2$$, $$det(B)=3$$, $$det(AB)=5$$, and $$det(BA)=6$$. What is $$det(AB)$$?
JSON expected answer: 5
-/
theorem la_60_turn_03_oracle [Fintype n] [DecidableEq n] (m : Model n) : m.det (m.A*m.B)=5 := by
  exact m.hab

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$det(AB)=det(A)det(B)$$ hold?
JSON expected answer: No.
-/
theorem la_60_turn_04_oracle [Fintype n] [DecidableEq n] (m : Model n) : m.det (m.A*m.B)≠m.det m.A*m.det m.B := by
  norm_num [Delta,m.ha,m.hb,m.hab,m.hba]

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$[det(AB)-det(A)det(B)]+[det(BA)-det(B)det(A)]=0$$ hold?
JSON expected answer: No.
-/
theorem la_60_turn_05_oracle [Fintype n] [DecidableEq n] (m : Model n) : Delta m m.A m.B+Delta m m.B m.A≠0 := by
  norm_num [Delta,m.ha,m.hb,m.hab,m.hba]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$\Delta(X,Y)=det(XY)-det(X)det(Y)$$. What is $$\Delta(B,A)$$?
JSON expected answer: 0
-/
theorem la_60_turn_06_oracle [Fintype n] [DecidableEq n] (m : Model n) : Delta m m.B m.A=0 := by
  norm_num [Delta,m.ha,m.hb,m.hab,m.hba]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$\Delta(A,B)$$?
JSON expected answer: -1
-/
theorem la_60_turn_07_oracle [Fintype n] [DecidableEq n] (m : Model n) : Delta m m.A m.B= -1 := by
  norm_num [Delta,m.ha,m.hb,m.hab,m.hba]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, what is $$\Delta(A,B)+\Delta(B,A)$$?
JSON expected answer: -1
-/
theorem la_60_turn_08_oracle [Fintype n] [DecidableEq n] (m : Model n) : Delta m m.A m.B+Delta m m.B m.A= -1 := by
  norm_num [Delta,m.ha,m.hb,m.hab,m.hba]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$\Delta(A,C)$$ for an additional square matrix $$C$$ of the same size?
JSON expected answer: cannot be determined
-/
theorem la_60_turn_09_oracle : Underdetermined (fun _ : Model (Fin 2) => True) (fun m => Delta m m.A m.C) := by
  refine ⟨completion 0,completion 1,trivial,trivial,?_⟩; norm_num [Delta,completion,fake,A]

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what is $$spectral\_score(A)$$?
JSON expected answer: cannot be determined
-/
theorem la_60_turn_10_oracle : Underdetermined (fun _ : Model (Fin 2) × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is determinant multiplicativity guaranteed for every matrix pair?
JSON expected answer: No.
-/
theorem la_60_turn_11_oracle [Fintype n] [DecidableEq n] (m : Model n) : ¬ ∀ X Y, m.det (X*Y)=m.det X*m.det Y := by
  intro h; have hh := h m.A m.B; norm_num [m.ha,m.hb,m.hab] at hh

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$det(AB)=det(A)det(B)$$ hold in ordinary linear algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem la_60_turn_12_oracle {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℚ) (ha : A.det=2) (hb : B.det=3) {k : Type} [Fintype k] [DecidableEq k] (m : Model k) : (A*B).det=6 ∧ m.det (m.A*m.B)=5 ∧ m.det (m.A*m.B)≠m.det m.A*m.det m.B := by
  refine ⟨by rw [Matrix.det_mul,ha,hb]; norm_num,m.hab,?_⟩; norm_num [m.ha,m.hb,m.hab]

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$det(AB)$$ in the standard system when $$det(A)=2$$ and $$det(B)=3$$, and what is it in the modified system?
JSON expected answer: 6 in the standard system and 5 in the modified system.
-/
theorem la_60_turn_13_oracle {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℚ) (ha : A.det=2) (hb : B.det=3) {k : Type} [Fintype k] [DecidableEq k] (m : Model k) : (A*B).det=6 ∧ m.det (m.A*m.B)=5 ∧ m.det (m.A*m.B)≠m.det m.A*m.det m.B := by
  refine ⟨by rw [Matrix.det_mul,ha,hb]; norm_num,m.hab,?_⟩; norm_num [m.ha,m.hb,m.hab]

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary linear algebra. If $$det(A)=2$$ and $$det(B)=3$$, what is $$det(AB)$$?
JSON expected answer: 6
-/
theorem la_60_turn_14_oracle {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℚ) (ha : A.det=2) (hb : B.det=3) : (A*B).det=6 := by
  rw [Matrix.det_mul,ha,hb]; norm_num

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary linear algebra, what is $$\Delta(A,B)$$?
JSON expected answer: 0
-/
theorem la_60_turn_15_oracle {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℚ) : (A*B).det-A.det*B.det=0 := by
  rw [Matrix.det_mul] <;> ring

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. What is $$det(AB)$$?
JSON expected answer: 5
-/
theorem la_60_turn_16_oracle [Fintype n] [DecidableEq n] (m : Model n) : m.det (m.A*m.B)=5 := by
  exact m.hab
