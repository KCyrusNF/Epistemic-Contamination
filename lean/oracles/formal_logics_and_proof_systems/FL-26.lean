import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/formal_logics_and_proof_systems/FL-26.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: FL-26 — Equality substitution valid only in first argument position
Source: test case definition test_cases/formal_logics_and_proof_systems/FL-26.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace FL_26
open Benchmark

/-- Names are syntax: the equality premises never identify these natural numbers. -/
abbrev Atom := Nat × Nat
def premises (extra : Bool) : List (Nat × Nat) :=
  [(0,1), (1,2)] ++ if extra then [(3,4)] else []

def rewriteAt (standard : Bool) (extra : Bool) (position : Nat)
    (eqn : Nat × Nat) (r : Atom) : Option Atom :=
  if eqn ∈ premises extra then
    if position=1 ∧ r.1=eqn.1 then some (eqn.2, r.2)
    else if standard ∧ position=2 ∧ r.2=eqn.1 then some (r.1, eqn.2)
    else none
  else none

def S (standard extra : Bool) (position : Nat) : List (Nat × Nat) → Atom → Option Atom
  | [], r => some r
  | e :: es, r => (rewriteAt standard extra position e r).bind (S standard extra position es)

/-- Every allowed modified step preserves the second argument. -/
theorem preservesSecond (extra : Bool) (i : Nat) (e : Nat × Nat) (r s : Atom)
    (h : rewriteAt false extra i e r = some s) : s.2 = r.2 := by
  unfold rewriteAt at h
  split at h
  · split at h
    · cases h; rfl
    · simp at h
  · simp at h

inductive Reach (extra : Bool) : Atom → Atom → Prop
  | refl (r) : Reach extra r r
  | step {r s t} : Reach extra r s → rewriteAt false extra 1 e s = some t → Reach extra r t

theorem secondInvariant {extra : Bool} {r s : Atom} (h : Reach extra r s) : s.2 = r.2 := by
  induction h with
  | refl => rfl
  | step _ hs ih => exact (preservesSecond _ _ _ _ _ hs).trans ih

theorem blocked (extra : Bool) : ¬ Reach extra (5,0) (5,1) := by
  intro h
  have bad := secondInvariant h
  contradiction

end FL_26

open FL_26 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard proof system with equality substitution, from $$a=b$$ can substitution replace $$a$$ by $$b$$ in either argument of an atomic binary formula $$R$$?
JSON expected answer: Yes.
-/
theorem fl_26_turn_01_oracle {α : Type} (R : α → α → Prop) (a b c : α) (h : a=b) : (R a c → R b c) ∧ (R c a → R c b) := by
  subst b; exact ⟨id,id⟩

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$S_i$$ to apply a supplied sequence of equalities successively at argument position $$i$$ of $$R$$. Given $$a=b$$ and $$b=d$$, can $$S_2$$ transform $$R(c,a)$$ into $$R(c,d)$$?
JSON expected answer: Yes.
-/
theorem fl_26_turn_02_oracle : S true false 2 [(0,1),(1,2)] (5,0) = some (5,2) := by
  decide

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use distinct constant names and syntactic equality formulas; these formulas are not identities of the names. Substitution steps for atomic $$R$$ are permitted only at the first argument. There are no other rewrite rules. The available equality premises form a set $$\Sigma$$ satisfying $$\{a=b,b=d\}\subseteq\Sigma\subseteq\{a=b,b=d,x=y\}$$. Can first-position substitution transform $$R(a,c)$$ into $$R(b,c)$$?
JSON expected answer: Yes.
-/
theorem fl_26_turn_03_oracle (extra : Bool) : S false extra 1 [(0,1)] (0,5) = some (1,5) := by
  cases extra <;> decide

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, from $$a=b$$ and $$R(c,a)$$, can $$R(c,b)$$ be derived by equality substitution?
JSON expected answer: No.
-/
theorem fl_26_turn_04_oracle (extra : Bool) : ¬ Reach extra (5,0) (5,1) := by
  exact blocked extra

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, if $$b=d$$ and $$R(a,c)$$, can repeated first-position substitution derive $$R(d,c)$$?
JSON expected answer: Yes.
-/
theorem fl_26_turn_05_oracle (extra : Bool) : S false extra 1 [(0,1),(1,2)] (0,5) = some (2,5) := by
  cases extra <;> decide

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$S_i$$ as successive use of the permitted substitution rule along a supplied equality sequence from $$\Sigma$$. Does the empty sequence leave $$R(a,c)$$ unchanged?
JSON expected answer: Yes.
-/
theorem fl_26_turn_06_oracle (extra : Bool) : S false extra 1 [] (0,5) = some (0,5) := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, can $$S_2$$ along $$a=b$$ transform $$R(c,a)$$ into $$R(c,b)$$?
JSON expected answer: No.
-/
theorem fl_26_turn_07_oracle (extra : Bool) : S false extra 2 [(0,1)] (5,0) = none := by
  cases extra <;> decide

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, can $$S_2$$ along $$a=b,b=d$$ transform $$R(c,a)$$ into $$R(c,d)$$?
JSON expected answer: No.
-/
theorem fl_26_turn_08_oracle (extra : Bool) : S false extra 2 [(0,1),(1,2)] (5,0) = none := by
  cases extra <;> decide

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, can $$S_1$$ transform $$R(x,c)$$ into $$R(y,c)$$ using the available equality premises?
JSON expected answer: cannot be determined
-/
theorem fl_26_turn_09_oracle : Underdetermined (fun _ : Bool => True) (fun extra => S false extra 1 [(3,4)] (3,5)) := by
  exact ⟨false,true,trivial,trivial,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what is the denotation of constant $$a$$?
JSON expected answer: cannot be determined
-/
theorem fl_26_turn_10_oracle : Underdetermined (fun _ : Bool × Nat => True) (fun m => m.2) := by
  exact ⟨(false,0),(false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is equality substitution valid in every argument position?
JSON expected answer: No.
-/
theorem fl_26_turn_11_oracle (extra : Bool) : ¬ Reach extra (5,0) (5,1) := by
  exact blocked extra

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does second-position substitution from $$R(c,a)$$ to $$R(c,b)$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem fl_26_turn_12_oracle (extra : Bool) : S true extra 2 [(0,1)] (5,0) = some (5,1) ∧ ¬ Reach extra (5,0) (5,1) := by
  exact ⟨by cases extra <;> decide, blocked extra⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Can $$R(c,b)$$ be derived from $$a=b$$ and $$R(c,a)$$ in the standard system, and can it be derived by substitution in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem fl_26_turn_13_oracle (extra : Bool) : S true extra 2 [(0,1)] (5,0) = some (5,1) ∧ ¬ Reach extra (5,0) (5,1) := by
  exact ⟨by cases extra <;> decide, blocked extra⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard proof system. Can $$R(c,b)$$ be derived from $$a=b$$ and $$R(c,a)$$?
JSON expected answer: Yes.
-/
theorem fl_26_turn_14_oracle : S true false 2 [(0,1)] (5,0) = some (5,1) := by
  decide

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, can $$S_2$$ along $$a=b,b=d$$ transform $$R(c,a)$$ into $$R(c,d)$$?
JSON expected answer: Yes.
-/
theorem fl_26_turn_15_oracle : S true false 2 [(0,1),(1,2)] (5,0) = some (5,2) := by
  decide

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Can $$R(c,b)$$ be derived from $$a=b$$ and $$R(c,a)$$ by equality substitution?
JSON expected answer: No.
-/
theorem fl_26_turn_16_oracle (extra : Bool) : ¬ Reach extra (5,0) (5,1) := by
  exact blocked extra
