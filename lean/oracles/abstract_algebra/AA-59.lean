import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/abstract_algebra/AA-59.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AA-59 — Equality not transitive
Source: test case definition test_cases/abstract_algebra/AA-59.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AA_59
open Benchmark

-- Distinct names a,b,c,d,e are encoded as 0,1,2,3,4.
structure Model where
  rel : Nat → Nat → Prop
  hab : rel 0 1
  hbc : rel 1 2
  hcd : rel 2 3
  hnac : ¬ rel 0 2
  hnad : ¬ rel 0 3
def completion (extra : Bool) : Model where
  rel := fun x y => (x=0 ∧ y=1) ∨ (x=1 ∧ y=2) ∨ (x=2 ∧ y=3) ∨ (extra=true ∧ x=1 ∧ y=4)
  hab := by simp
  hbc := by simp
  hcd := by simp
  hnac := by simp
  hnad := by simp

theorem path2 (m : Model) : chain m.rel 2 0 2 :=
  ⟨1, ⟨0, rfl, m.hab⟩, m.hbc⟩
theorem path3 (m : Model) : chain m.rel 3 0 3 :=
  ⟨2, path2 m, m.hcd⟩
theorem vary_path : Underdetermined (fun _ : Model => True)
    (fun m => chain m.rel 2 0 4) := by
  refine ⟨completion false, completion true, True.intro, True.intro, ?_⟩
  intro eqv
  have yes : chain (completion true).rel 2 0 4 :=
    ⟨1, ⟨0, rfl, by simp [completion]⟩, by simp [completion]⟩
  have hn : chain (completion false).rel 2 0 4 := eqv.mpr yes
  rcases hn with ⟨y, _, hy⟩
  simp [completion] at hy

end AA_59

open AA_59 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In the standard system, equality is transitive. If $$x=y$$ and $$y=z$$, does $$x=z$$ follow?
JSON expected answer: Yes.
-/
theorem aa_59_turn_01_oracle  {A : Type} (x y z : A) (hxy : x=y) (hyz : y=z) : x=z := by
  exact hxy.trans hyz

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system define $$E_1(x,z)\iff x=z$$ and $$E_{n+1}(x,z)\iff\exists y\,(E_n(x,y)\land y=z)$$ for positive natural numbers. If $$a=b$$, $$b=c$$, and $$c=d$$, does $$E_3(a,d)$$ imply $$a=d$$?
JSON expected answer: Yes.
-/
theorem aa_59_turn_02_oracle  {A : Type} (a d : A) : chain Eq 3 a d → a=d := by
  exact chain_transitive Eq (fun _ _ _ => Eq.trans) 2 a d

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now consider a binary relation $$=$$ on distinct names $$a,b,c,d,e$$. Here the symbol $$=$$ denotes a binary relation on names, not identity of the names; no substitution or transitivity is assumed. Stipulate $$a=b$$, $$b=c$$, $$c=d$$, $$a\neq c$$, and $$a\neq d$$; all other pairs are unconstrained. Does $$a=c$$ hold?
JSON expected answer: No.
-/
theorem aa_59_turn_03_oracle (m : Model) : ¬ m.rel 0 2 := by
  exact m.hnac

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does transitivity correctly infer $$a=c$$ from $$a=b$$ and $$b=c$$?
JSON expected answer: No.
-/
theorem aa_59_turn_04_oracle (m : Model) : ¬ (m.rel 0 1 → m.rel 1 2 → m.rel 0 2) := by
  intro h; exact m.hnac (h m.hab m.hbc)

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, is there a chain $$a=b=c=d$$ even though $$a=d$$ fails?
JSON expected answer: Yes.
-/
theorem aa_59_turn_05_oracle (m : Model) : chain m.rel 3 0 3 ∧ ¬ m.rel 0 3 := by
  exact ⟨path3 m,m.hnad⟩

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$E_1(x,z)\iff x=z$$ and $$E_{n+1}(x,z)\iff\exists y\,(E_n(x,y)\land y=z)$$ for positive natural numbers. Does $$E_1(a,b)$$ hold?
JSON expected answer: Yes.
-/
theorem aa_59_turn_06_oracle (m : Model) : chain m.rel 1 0 1 := by
  exact ⟨0,rfl,m.hab⟩

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$E_2(a,c)$$ imply $$a=c$$?
JSON expected answer: No.
-/
theorem aa_59_turn_07_oracle (m : Model) : ¬ (chain m.rel 2 0 2 → m.rel 0 2) := by
  intro h; exact m.hnac (h (path2 m))

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$E_3(a,d)$$ hold?
JSON expected answer: Yes.
-/
theorem aa_59_turn_08_oracle (m : Model) : chain m.rel 3 0 3 := by
  exact path3 m

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$E_2(a,e)$$ hold?
JSON expected answer: cannot be determined
-/
theorem aa_59_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => chain m.rel 2 0 4) := by
  exact vary_path

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$hash(a)$$?
JSON expected answer: cannot be determined
-/
theorem aa_59_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),True.intro,True.intro,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, is the relation written $$=$$ transitive?
JSON expected answer: No.
-/
theorem aa_59_turn_11_oracle (m : Model) : ¬ (∀ x y z, m.rel x y → m.rel y z → m.rel x z) := by
  intro h; exact m.hnac (h 0 1 2 m.hab m.hbc)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement “$$a=b$$ and $$b=c$$ imply $$a=c$$” hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem aa_59_turn_12_oracle (m : Model) : (∀ x y z : Nat, x=y → y=z → x=z) ∧ ¬ (m.rel 0 1 → m.rel 1 2 → m.rel 0 2) := by
  constructor
  · intro x y z hxy hyz; exact hxy.trans hyz
  · intro h; exact m.hnac (h m.hab m.hbc)

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does $$a=c$$ follow from $$a=b$$ and $$b=c$$ in the standard system, and does it follow in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem aa_59_turn_13_oracle (m : Model) : (∀ x y z : Nat, x=y → y=z → x=z) ∧ ¬ (m.rel 0 1 → m.rel 1 2 → m.rel 0 2) := by
  constructor
  · intro x y z hxy hyz; exact hxy.trans hyz
  · intro h; exact m.hnac (h m.hab m.hbc)

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard system. If $$x=y$$ and $$y=z$$, does $$x=z$$ follow?
JSON expected answer: Yes.
-/
theorem aa_59_turn_14_oracle  {A : Type} (x y z : A) (hxy : x=y) (hyz : y=z) : x=z := by
  exact hxy.trans hyz

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard system, does $$E_3(a,d)$$ imply $$a=d$$?
JSON expected answer: Yes.
-/
theorem aa_59_turn_15_oracle  {A : Type} (a d : A) : chain Eq 3 a d → a=d := by
  exact chain_transitive Eq (fun _ _ _ => Eq.trans) 2 a d

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$a=c$$ hold?
JSON expected answer: No.
-/
theorem aa_59_turn_16_oracle (m : Model) : ¬ m.rel 0 2 := by
  exact m.hnac
