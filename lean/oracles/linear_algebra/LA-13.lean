import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/linear_algebra/LA-13.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: LA-13 — Scalar multiplication not associative with field multiplication
Source: test case definition test_cases/linear_algebra/LA-13.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace LA_13
open Benchmark

structure Model (α : Type) where
  act : ℚ → α → α
  v : α
  t : α
  u : α
  w : α
  p : α
  q : α
  h3 : act 3 v = t
  h2 : act 2 t = w
  h6 : act 6 v = u
  h4 : act 4 w = p
  h24 : act 24 v = q
  uw : u ≠ w
  pq : p ≠ q
/-- Left fold is precisely application in the order of the list. -/
def E (act : ℚ → α → α) (scalars : List ℚ) (v : α) := scalars.foldl (fun x a => act a x) v

def completion (k : Nat) : Model Nat where
  act := fun a x => if a=3 ∧ x=0 then 1 else if a=2 ∧ x=1 then 2
    else if a=6 ∧ x=0 then 3 else if a=4 ∧ x=2 then 4
    else if a=24 ∧ x=0 then 5 else if a=20 ∧ x=0 then k else 0
  v := 0
  t := 1
  u := 3
  w := 2
  p := 4
  q := 5
  h3 := by norm_num
  h2 := by norm_num
  h6 := by norm_num
  h4 := by norm_num
  h24 := by norm_num
  uw := by decide
  pq := by decide

theorem noAssoc (m : Model α) : m.act 6 m.v ≠ m.act 2 (m.act 3 m.v) := by
  rw [m.h3,m.h2,m.h6]
  exact m.uw

theorem noLong (m : Model α) : E m.act [3,2,4] m.v ≠ m.act 24 m.v := by
  simpa [E, m.h3, m.h2, m.h4, m.h24] using m.pq

end LA_13

open LA_13 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary vector space, does scalar multiplication satisfy $$(ab)v=a(bv)$$?
JSON expected answer: Yes.
-/
theorem la_13_turn_01_oracle {V : Type} [AddCommGroup V] [Module ℚ V] (a b : ℚ) (v : V) : (a*b) • v = a • (b • v) := by
  exact mul_smul a b v

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In an ordinary vector space define $$E([],x)=x$$ and $$E(L+[a],x)=a\cdot E(L,x)$$, applying scalars in list order. Does $$E([3,2,4],v)=24\cdot v$$ hold?
JSON expected answer: Yes.
-/
theorem la_13_turn_02_oracle {V : Type} [AddCommGroup V] [Module ℚ V] (v : V) : E (fun a x => a • x) [3,2,4] v = (24:ℚ) • v := by
  simp only [E, List.foldl_cons, List.foldl_nil]; rw [← mul_smul, ← mul_smul]; norm_num

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use ordinary rational scalars acting by an otherwise unconstrained total operation on vector labels. Stipulate $$3\cdot v=t$$, $$2\cdot t=w$$, $$6\cdot v=u$$ with $$u\neq w$$, and $$4\cdot w=p$$, $$24\cdot v=q$$ with $$p\neq q$$. Scalar-scalar multiplication remains ordinary. Does scalar associativity hold for $$(2,3,v)$$?
JSON expected answer: No.
-/
theorem la_13_turn_03_oracle (m : Model α) : m.act 6 m.v ≠ m.act 2 (m.act 3 m.v) := by
  exact noAssoc m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$(2\cdot3)\cdot v=2\cdot(3\cdot v)$$ hold?
JSON expected answer: No.
-/
theorem la_13_turn_04_oracle (m : Model α) : m.act 6 m.v ≠ m.act 2 (m.act 3 m.v) := by
  exact noAssoc m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$4\cdot(2\cdot(3\cdot v))=24\cdot v$$ hold?
JSON expected answer: No.
-/
theorem la_13_turn_05_oracle (m : Model α) : E m.act [3,2,4] m.v ≠ m.act 24 m.v := by
  exact noLong m

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$E([],x)=x$$ and $$E(L+[a],x)=a\cdot E(L,x)$$. Does $$E([],v)=v$$ hold?
JSON expected answer: Yes.
-/
theorem la_13_turn_06_oracle (m : Model α) : E m.act [] m.v = m.v := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$E([3,2],v)=6\cdot v$$ hold?
JSON expected answer: No.
-/
theorem la_13_turn_07_oracle (m : Model α) : E m.act [3,2] m.v ≠ m.act 6 m.v := by
  simpa [E, m.h3,m.h2,m.h6] using Ne.symm m.uw

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$E([3,2,4],v)=24\cdot v$$ hold?
JSON expected answer: No.
-/
theorem la_13_turn_08_oracle (m : Model α) : E m.act [3,2,4] m.v ≠ m.act 24 m.v := by
  exact noLong m

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$E([5,4],v)=20\cdot v$$ hold?
JSON expected answer: cannot be determined
-/
theorem la_13_turn_09_oracle : Underdetermined (fun _ : Model Nat => True) (fun m => decide (E m.act [5,4] m.v = m.act 20 m.v)) := by
  refine ⟨completion 0,completion 1,trivial,trivial,?_⟩ <;> decide

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$\|v\|$$?
JSON expected answer: cannot be determined
-/
theorem la_13_turn_10_oracle : Underdetermined (fun _ : Model Nat × Nat => True) (fun m => m.2) := by
  exact ⟨(completion 0,0),(completion 0,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is scalar multiplication associative with field multiplication for every scalar pair?
JSON expected answer: No.
-/
theorem la_13_turn_11_oracle (m : Model α) : ¬ ∀ a b x, m.act (a*b) x = m.act a (m.act b x) := by
  intro h; have hh := h 2 3 m.v; norm_num at hh; exact noAssoc m hh

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does $$(ab)v=a(bv)$$ hold in an ordinary vector space, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem la_13_turn_12_oracle {V : Type} [AddCommGroup V] [Module ℚ V] (v : V) (m : Model α) : (6:ℚ) • v = (2:ℚ) • ((3:ℚ) • v) ∧ m.act 6 m.v ≠ m.act 2 (m.act 3 m.v) := by
  constructor
  · rw [← mul_smul]; norm_num
  · exact noAssoc m

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does scalar associativity hold for $$(2,3,v)$$ in the standard system, and does it hold in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem la_13_turn_13_oracle {V : Type} [AddCommGroup V] [Module ℚ V] (v : V) (m : Model α) : (6:ℚ) • v = (2:ℚ) • ((3:ℚ) • v) ∧ m.act 6 m.v ≠ m.act 2 (m.act 3 m.v) := by
  constructor
  · rw [← mul_smul]; norm_num
  · exact noAssoc m

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary linear algebra. Does $$(2\cdot3)\cdot v=2\cdot(3\cdot v)$$ hold?
JSON expected answer: Yes.
-/
theorem la_13_turn_14_oracle {V : Type} [AddCommGroup V] [Module ℚ V] (a b : ℚ) (v : V) : (a*b) • v = a • (b • v) := by
  exact mul_smul a b v

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using ordinary linear algebra, does $$E([3,2,4],v)=24\cdot v$$ hold?
JSON expected answer: Yes.
-/
theorem la_13_turn_15_oracle {V : Type} [AddCommGroup V] [Module ℚ V] (v : V) : E (fun a x => a • x) [3,2,4] v = (24:ℚ) • v := by
  simp only [E, List.foldl_cons, List.foldl_nil]; rw [← mul_smul, ← mul_smul]; norm_num

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$6\cdot v=2\cdot(3\cdot v)$$ hold?
JSON expected answer: No.
-/
theorem la_13_turn_16_oracle (m : Model α) : m.act 6 m.v ≠ m.act 2 (m.act 3 m.v) := by
  exact noAssoc m
