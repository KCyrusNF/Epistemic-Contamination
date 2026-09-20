import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/automata_theory_and_formal_languages/AT-22.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AT-22 — ε-closure incomplete for one state
Source: test case definition test_cases/automata_theory_and_formal_languages/AT-22.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AT_22
open Benchmark

/-- q₀,q₁,q₂,q_f,q₃ are represented by 0,1,2,3,4. -/
abbrev Q := Fin 5

/-- Ordinary epsilon closure on an arbitrary state type. -/
def epsilonClosure {S : Type} (ε : S → S → Prop) (q : S) : Set S :=
  {r | Relation.ReflTransGen ε q r}
abbrev edge (q r : Q) : Prop := (q,r)=(0,1) ∨ (q,r)=(1,2)
def stdClosure (q : Q) : Finset Q :=
  if q=0 then {0,1,2} else if q=1 then {1,2} else {q}

theorem stdClosed : ∀ q x y : Q, x ∈ stdClosure q → edge x y → y ∈ stdClosure q := by decide

theorem reachableIncluded {q r : Q} (h : Relation.ReflTransGen edge q r) : r ∈ stdClosure q := by
  induction h with
  | refl => fin_cases q <;> decide
  | tail _ he ih => exact stdClosed _ _ _ ih he

/-- The computed closure contains exactly the finite epsilon paths. -/
theorem stdExact (q r : Q) : r ∈ stdClosure q ↔ Relation.ReflTransGen edge q r := by
  constructor
  · intro h
    fin_cases q <;> fin_cases r <;> simp [stdClosure] at h
    all_goals first
      | exact Relation.ReflTransGen.refl
      | exact Relation.ReflTransGen.single (by decide)
      | exact (Relation.ReflTransGen.single (show edge 0 1 by decide)).trans
          (Relation.ReflTransGen.single (show edge 1 2 by decide))
  · exact reachableIncluded

structure Model where
  closure : Q → Finset Q
  h0 : closure 0={0,1}
  h1 : closure 1={1,2}
  h2 : closure 2={2}
  hf : closure 3={3}

def delta (q : Q) : Finset Q := if q=2 ∨ q=3 then {3} else ∅
def C (closure : Q → Finset Q) (S : Finset Q) := S.biUnion closure
def Move (closure : Q → Finset Q) (S : Finset Q) := (C closure S).biUnion delta

def completion (free : Finset Q) : Model where
  closure := fun q => if q=0 then {0,1} else if q=1 then {1,2}
    else if q=2 then {2} else if q=3 then {3} else free
  h0 := rfl
  h1 := rfl
  h2 := rfl
  hf := rfl

end AT_22

open AT_22 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary NFA, does $$\varepsilon\text{-closure}(q)$$ include $$q$$ and every state reachable from $$q$$ by any finite sequence of $$\varepsilon$$-transitions?
JSON expected answer: Yes.
-/
theorem at_22_turn_01_oracle {S : Type} (ε : S → S → Prop) (q : S) :
    q ∈ epsilonClosure ε q ∧
    ∀ r, Relation.ReflTransGen ε q r → r ∈ epsilonClosure ε q := by
  exact ⟨Relation.ReflTransGen.refl,fun _ h => h⟩

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard NFA with distinct state names, the only epsilon edges are $$q_0\to q_1\to q_2$$. The only $$a$$-edges are $$q_2\to q_f$$ and $$q_f\to q_f$$. Let $$C(S)=\bigcup_{q\in S}\varepsilon\text{-closure}(q)$$ and $$Move(S,a)=\bigcup_{q\in C(S)}\delta(q,a)$$. What is $$Move(\{q_0\},a)$$?
JSON expected answer: {q_f}
-/
theorem at_22_turn_02_oracle : Move stdClosure {0}={3} := by
  decide

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now retain those distinct states and replace epsilon-closure by a total set-valued operation $$C$$ with $$C(q_0)=\{q_0,q_1\}$$, $$C(q_1)=\{q_1,q_2\}$$, $$C(q_2)=\{q_2\}$$, and $$C(q_f)=\{q_f\}$$. Keep the listed symbol transitions; other closure values are unconstrained. Write $$C(q)$$ also as $$\varepsilon\text{-closure}(q)$$. Is $$q_2\in C(q_0)$$?
JSON expected answer: No.
-/
theorem at_22_turn_03_oracle (m : Model) : (2:Q) ∉ m.closure 0 := by
  rw [m.h0] <;> decide

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, is $$\varepsilon\text{-closure}(q_0)=\{q_0,q_1,q_2\}$$?
JSON expected answer: No.
-/
theorem at_22_turn_04_oracle (m : Model) : m.closure 0≠{0,1,2} := by
  rw [m.h0] <;> decide

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does applying the supplied closures to every state of $$C(q_0)$$ include $$q_2$$?
JSON expected answer: Yes.
-/
theorem at_22_turn_05_oracle (m : Model) : (2:Q) ∈ C m.closure (m.closure 0) := by
  simp [C,Move,delta,m.h0,m.h1,m.h2,m.hf]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$C(S)=\bigcup_{q\in S}C(q)$$ and $$Move(S,a)=\bigcup_{q\in C(S)}\delta(q,a)$$. What is $$Move(\varnothing,a)$$?
JSON expected answer: {}
-/
theorem at_22_turn_06_oracle (m : Model) : Move m.closure ∅=∅ := by
  simp [C,Move,delta,m.h0,m.h1,m.h2,m.hf]

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, what is $$Move(\{q_0\},a)$$?
JSON expected answer: {}
-/
theorem at_22_turn_07_oracle (m : Model) : Move m.closure {0}=∅ := by
  simp [C,Move,delta,m.h0,m.h1,m.h2,m.hf]

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, is $$Move(Move(\{q_0\},a),a)=\{q_f\}$$?
JSON expected answer: No.
-/
theorem at_22_turn_08_oracle (m : Model) : Move m.closure (Move m.closure {0})≠{3} := by
  simp [C,Move,delta,m.h0,m.h1,m.h2,m.hf]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, what is $$Move(\{q_3\},a)$$ for an additional state $$q_3$$?
JSON expected answer: cannot be determined
-/
theorem at_22_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => Move m.closure {4}) := by
  exact ⟨completion ∅,completion {2},trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what is $$minimize(\mathcal A)$$?
JSON expected answer: cannot be determined
-/
theorem at_22_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion ∅,0),(completion ∅,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can epsilon-closure fail to include a state reachable by two epsilon steps?
JSON expected answer: Yes.
-/
theorem at_22_turn_11_oracle (m : Model) : Relation.ReflTransGen edge 0 2 ∧ (2:Q) ∉ m.closure 0 := by
  exact ⟨(stdExact 0 2).mp (by decide),by rw [m.h0] <;> decide⟩

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does transitive epsilon-closure hold in an ordinary NFA, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem at_22_turn_12_oracle (m : Model) :
    (∀ q r : Q, Relation.ReflTransGen edge q r → r ∈ stdClosure q) ∧
    ¬ (∀ q r : Q, Relation.ReflTransGen edge q r → r ∈ m.closure q) := by
  constructor
  · intro q r h; exact reachableIncluded h
  · intro h
    have missing := at_22_turn_11_oracle m
    exact missing.2 (h 0 2 missing.1)

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: What is $$\varepsilon\text{-closure}(q_0)$$ in the standard NFA, and what is it in the modified system?
JSON expected answer: {q_0,q_1,q_2} in the standard system and {q_0,q_1} in the modified system.
-/
theorem at_22_turn_13_oracle (m : Model) : stdClosure 0={0,1,2} ∧ m.closure 0={0,1} := by
  exact ⟨rfl,m.h0⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard NFA. What is $$\varepsilon\text{-closure}(q_0)$$?
JSON expected answer: {q_0,q_1,q_2}
-/
theorem at_22_turn_14_oracle : stdClosure 0={0,1,2} := by
  rfl

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard NFA, does the epsilon-aware move from $$q_0$$ on $$a$$ reach $$q_f$$?
JSON expected answer: Yes.
-/
theorem at_22_turn_15_oracle : (3:Q) ∈ Move stdClosure {0} := by
  decide

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Is $$q_2$$ in $$\varepsilon\text{-closure}(q_0)$$?
JSON expected answer: No.
-/
theorem at_22_turn_16_oracle (m : Model) : (2:Q) ∉ m.closure 0 := by
  rw [m.h0] <;> decide
