import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/formal_logics_and_proof_systems/FL-01.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: FL-01 — Modus Ponens invalid for one antecedent class
Source: test case definition test_cases/formal_logics_and_proof_systems/FL-01.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace FL_01
open Benchmark

-- Named atoms/constants P,Q,R,X correspond to 0,1,2,3.
structure Model where
  allowed : Nat → Bool
  blocked : allowed 0 = false
  q : allowed 1 = true
  r : allowed 2 = true
def completion (free : Bool) : Model where
  allowed := fun n => if n=0 then false else if n=1 ∨ n=2 then true else free
  blocked := by norm_num
  q := by norm_num
  r := by norm_num
def allSteps (allow : Nat → Bool) (xs : List Nat) := xs.all allow

inductive Reach (allow : Nat → Bool) (edges : List (Nat × Nat)) (initial : List Nat) : Nat → Prop
  | assumption {a} : a ∈ initial → Reach allow edges initial a
  | mp {a b} : Reach allow edges initial a → (a,b) ∈ edges → allow a = true → Reach allow edges initial b

theorem invariant {allow edges initial} (p : Nat → Prop)
    (base : ∀ a, a ∈ initial → p a)
    (step : ∀ a b, p a → (a,b) ∈ edges → allow a = true → p b)
    {x} (h : Reach allow edges initial x) : p x := by
  induction h with
  | assumption h => exact base _ h
  | mp h edge ok ih => exact step _ _ ih edge ok

def chainEdges : List (Nat × Nat) := [(0,1),(1,2)]
theorem onlyP (m : Model) {x} (h : Reach m.allowed chainEdges [0] x) : x=0 := by
  apply invariant (fun x => x=0) ?_ ?_ h
  · intro a ha; simpa using ha
  · intro a b ha he ok
    subst a
    rw [m.blocked] at ok
    contradiction

end FL_01

open FL_01 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard proof system with Modus Ponens, from $$P$$ and $$P\rightarrow Q$$, can $$Q$$ be derived?
JSON expected answer: Yes.
-/
theorem fl_01_turn_01_oracle {P Q : Prop} (p : P) (mp : P → Q) : Q := by
  exact mp p

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard proof system, define a chain to succeed when each successive Modus Ponens application is permitted. Does the chain $$P,\ P\to Q,\ Q\to R$$ yield $$R$$?
JSON expected answer: Yes.
-/
theorem fl_01_turn_02_oracle {P Q R : Prop} (p : P) (pq : P → Q) (qr : Q → R) : R := by
  exact qr (pq p)

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use a syntactic proof calculus with assumption lookup and Modus Ponens as its only inference rules. Modus Ponens is permitted exactly for antecedents outside a class $$C$$. Stipulate $$P\in C$$ and $$Q,R\notin C$$; other membership is unconstrained. Distinct capital letters denote distinct atomic formulas, and each query uses only its stated premises. From $$P$$ and $$P\to Q$$, can Modus Ponens derive $$Q$$?
JSON expected answer: No.
-/
theorem fl_01_turn_03_oracle (m : Model) : ¬ Reach m.allowed chainEdges [0] 1 := by
  intro h; have bad := onlyP m h <;> omega

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard Modus Ponens inference from $$P$$ and $$P\rightarrow Q$$ yield $$Q$$?
JSON expected answer: No.
-/
theorem fl_01_turn_04_oracle (m : Model) : ¬ Reach m.allowed chainEdges [0] 1 := by
  intro h; have bad := onlyP m h <;> omega

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, from $$Q,Q\to R,R\to S$$, can successive Modus Ponens applications derive $$S$$?
JSON expected answer: Yes.
-/
theorem fl_01_turn_05_oracle (m : Model) : Reach m.allowed [(1,2),(2,4)] [1] 4 := by
  exact .mp (.mp (.assumption (by simp)) (by simp) m.q) (by simp) m.r

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct chain evaluation by assumption lookup followed by the permitted Modus Ponens steps. For the zero-step chain with sole premise $$Q$$, is $$Q$$ available?
JSON expected answer: Yes.
-/
theorem fl_01_turn_06_oracle (m : Model) : Reach m.allowed [] [1] 1 := by
  exact .assumption (by simp)

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, can $$R$$ be derived from $$Q$$ and $$Q\rightarrow R$$?
JSON expected answer: Yes.
-/
theorem fl_01_turn_07_oracle (m : Model) : Reach m.allowed [(1,2)] [1] 2 := by
  exact .mp (.assumption (by simp)) (by simp) m.q

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In this modified system, can $$R$$ be derived from $$P$$, $$P\rightarrow Q$$, and $$Q\rightarrow R$$ using the supplied rules?
JSON expected answer: No.
-/
theorem fl_01_turn_08_oracle (m : Model) : ¬ Reach m.allowed chainEdges [0] 2 := by
  intro h; have bad := onlyP m h <;> omega

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does the chain $$X,X\to Y,Y\to Q$$ yield $$Q$$, given $$Y\notin C$$?
JSON expected answer: cannot be determined
-/
theorem fl_01_turn_09_oracle : Underdetermined (fun m : Model => m.allowed 5 = true) (fun m => Reach m.allowed [(3,5),(5,1)] [3] 1) := by
  let no : Model := { completion false with allowed := fun n => if n=5 then true else (completion false).allowed n }
  let yes : Model := completion true
  refine ⟨no,yes,by decide,by decide,?_⟩
  intro eqv
  have hy : Reach yes.allowed [(3,5),(5,1)] [3] 1 :=
    .mp (a := 5) (.mp (a := 3) (.assumption (by simp)) (by simp) (by rfl))
      (by simp) (by rfl)
  have hn := eqv.mpr hy
  have only : (1:Nat)=3 := by
    apply invariant (fun x => x=3) ?_ ?_ hn
    · intro a ha; simpa using ha
    · intro a b ha he ok; subst a; simp [no,completion] at ok
  omega

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is the truth value of $$P$$?
JSON expected answer: cannot be determined
-/
theorem fl_01_turn_10_oracle : Underdetermined (fun _ : Model × Bool => True) (fun m => m.2) := by
  exact ⟨(completion false,false),(completion false,true),True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is Modus Ponens valid for every antecedent?
JSON expected answer: No.
-/
theorem fl_01_turn_11_oracle (m : Model) : ¬ (∀ a, m.allowed a = true) := by
  intro h; have bad := h 0; rw [m.blocked] at bad; contradiction

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the inference from $$P$$ and $$P\rightarrow Q$$ to $$Q$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem fl_01_turn_12_oracle (m : Model) : Reach (fun _ => true) chainEdges [0] 1 ∧ ¬ Reach m.allowed chainEdges [0] 1 := by
  constructor
  · exact .mp (a := 0) (.assumption (by simp)) (by simp [chainEdges]) rfl
  · intro h; have bad := onlyP m h <;> omega

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Can $$Q$$ be derived from $$P$$ and $$P\rightarrow Q$$ in the standard system, and can it be derived in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem fl_01_turn_13_oracle (m : Model) : Reach (fun _ => true) chainEdges [0] 1 ∧ ¬ Reach m.allowed chainEdges [0] 1 := by
  constructor
  · exact .mp (a := 0) (.assumption (by simp)) (by simp [chainEdges]) rfl
  · intro h; have bad := onlyP m h <;> omega

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard proof system. From $$P$$ and $$P\rightarrow Q$$, can $$Q$$ be derived?
JSON expected answer: Yes.
-/
theorem fl_01_turn_14_oracle {P Q : Prop} (p : P) (mp : P → Q) : Q := by
  exact mp p

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, from $$P$$, $$P\rightarrow Q$$, and $$Q\rightarrow R$$, can $$R$$ be derived?
JSON expected answer: Yes.
-/
theorem fl_01_turn_15_oracle {P Q R : Prop} (p : P) (pq : P → Q) (qr : Q → R) : R := by
  exact qr (pq p)

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. From $$P$$ and $$P\rightarrow Q$$, can $$Q$$ be derived by Modus Ponens?
JSON expected answer: No.
-/
theorem fl_01_turn_16_oracle (m : Model) : ¬ Reach m.allowed chainEdges [0] 1 := by
  intro h; have bad := onlyP m h <;> omega
