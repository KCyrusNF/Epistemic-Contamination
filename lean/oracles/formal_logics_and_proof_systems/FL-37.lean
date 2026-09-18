import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/formal_logics_and_proof_systems/FL-37.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: FL-37 — Existential witness not reusable
Source: test case definition test_cases/formal_logics_and_proof_systems/FL-37.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace FL_37
open Benchmark

def available (uses : Nat) : Bool := uses == 0
def use (uses : Nat) : Option Nat := if available uses then some (uses+1) else none
def twice : Option Nat := (use 0).bind use
def standardAvailable (_uses : Nat) : Bool := true

end FL_37

open FL_37 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard proof system, a witness introduced from $$\exists x\,P(x)$$ may be used throughout its permitted subproof. Can the same witness support two consequences within that subproof?
JSON expected answer: Yes.
-/
theorem fl_37_turn_01_oracle {P Q R : Prop} (witness : P) (left : P → Q) (right : P → R) : Q ∧ R := by
  exact ⟨left witness,right witness⟩

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$A(w,n)$$ to mean availability of witness $$w$$ after $$n$$ permitted uses within its subproof. Can a fresh $$w$$ be used first with $$P(w)\to Q$$ and then with $$P(w)\to R$$ to obtain both conclusions?
JSON expected answer: Yes.
-/
theorem fl_37_turn_02_oracle {P Q R : Prop} (witness : P) (left : P → Q) (right : P → R) : Q ∧ R := by
  exact ⟨left witness,right witness⟩

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now modify witness use: introduction supplies one available witness token; a witness-dependent inference consumes it, and a consumed token cannot be used again. Each question describes its own use history inside the permitted subproof. If fresh $$w$$ is used first to derive $$Q$$, can that token then be reused to derive $$R$$?
JSON expected answer: No.
-/
theorem fl_37_turn_03_oracle : twice = none := by
  rfl

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, after the first use of $$w$$, is $$w$$ still available for a second witness-dependent inference?
JSON expected answer: No.
-/
theorem fl_37_turn_04_oracle : available 1 = false := by
  rfl

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, after using fresh tokens $$w$$ and $$v$$ once each, is either token available for another inference?
JSON expected answer: No.
-/
theorem fl_37_turn_05_oracle : available 1 = false ∧ available 1 = false := by
  decide

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$A(w,n)$$ as availability after $$n$$ permitted uses. Let $$u$$ have an unspecified use count $$k\in\{0,1\}$$. Does $$A(w,0)$$ hold for a newly introduced token?
JSON expected answer: Yes.
-/
theorem fl_37_turn_06_oracle : available 0 = true := by
  rfl

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, does $$A(w,1)$$ hold?
JSON expected answer: No.
-/
theorem fl_37_turn_07_oracle : available 1 = false := by
  rfl

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, starting with fresh $$w$$, can sequential uses of $$P(w)\to Q$$ and $$P(w)\to R$$ obtain both conclusions?
JSON expected answer: No.
-/
theorem fl_37_turn_08_oracle : twice = none := by
  rfl

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$A(u,k)$$ hold?
JSON expected answer: cannot be determined
-/
theorem fl_37_turn_09_oracle : Underdetermined (fun k : Nat => k=0 ∨ k=1) available := by
  exact ⟨0,1,Or.inl rfl,Or.inr rfl,by decide⟩

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what object does $$w$$ denote?
JSON expected answer: cannot be determined
-/
theorem fl_37_turn_10_oracle : Underdetermined (fun _ : Nat => True) id := by
  exact ⟨0,1,True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can an existential witness be reused after its first use?
JSON expected answer: No.
-/
theorem fl_37_turn_11_oracle : use 1 = none := by
  rfl

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does witness reuse within the permitted subproof hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem fl_37_turn_12_oracle : standardAvailable 1 = true ∧ available 1 = false := by
  decide

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Can the same witness support two consequences in the standard system, and can it do so in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem fl_37_turn_13_oracle : standardAvailable 1 = true ∧ available 1 = false := by
  decide

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard proof system. Can one existential witness support two permitted consequences within its subproof?
JSON expected answer: Yes.
-/
theorem fl_37_turn_14_oracle {P Q R : Prop} (witness : P) (left : P → Q) (right : P → R) : Q ∧ R := by
  exact ⟨left witness,right witness⟩

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, can both $$Q$$ and $$R$$ be derived from the same witness $$w$$ under the stated implications?
JSON expected answer: Yes.
-/
theorem fl_37_turn_15_oracle {P Q R : Prop} (witness : P) (left : P → Q) (right : P → R) : Q ∧ R := by
  exact ⟨left witness,right witness⟩

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$A(w,1)$$ hold after one use?
JSON expected answer: No.
-/
theorem fl_37_turn_16_oracle : available 1 = false := by
  rfl
