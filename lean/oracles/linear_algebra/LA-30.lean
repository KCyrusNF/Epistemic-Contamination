import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/linear_algebra/LA-30.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: LA-30 — One vector not expressible despite spanning declaration
Source: test case definition test_cases/linear_algebra/LA-30.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace LA_30
open Benchmark

abbrev Vec := ℚ × ℚ
def Rep [AddCommGroup V] [Module ℚ V] (e1 e2 x : V) := ∃ a b : ℚ, x=a • e1+b • e2
/-- Coverage is the definition of spanning by this two-element family. -/
def Spans [AddCommGroup V] [Module ℚ V] (e1 e2 : V) := ∀ x, Rep e1 e2 x

def AllRep [AddCommGroup V] [Module ℚ V] (e1 e2 : V) : List V → Prop
  | [] => True
  | x::xs => Rep e1 e2 x ∧ AllRep e1 e2 xs
structure Model (V : Type) [AddCommGroup V] [Module ℚ V] where
  e1 : V
  e2 : V
  u : V
  v : V
  w : V
  hu : u=e1+e2
  hv : ¬ Rep e1 e2 v

def completion (extra : Bool) : Model Vec where
  e1 := (1,0)
  e2 := (1,0)
  u := (2,0)
  v := (0,1)
  w := if extra then (0,0) else (0,2)
  hu := by norm_num
  hv := by
    rintro ⟨a,b,h⟩
    have hh := congrArg Prod.snd h
    simp at hh

theorem varies : Underdetermined (fun _ : Model Vec => True) (fun m => Rep m.e1 m.e2 m.w) := by
  refine ⟨completion true,completion false,trivial,trivial,?_⟩
  intro h
  have yes : Rep (completion true).e1 (completion true).e2 (completion true).w := ⟨0,0,by simp [completion]⟩
  rcases h.mp yes with ⟨a,b,hp⟩
  have hh := congrArg Prod.snd hp
  norm_num [completion] at hh

end LA_30

open LA_30 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In ordinary linear algebra, if a set $$S$$ spans a vector space $$V$$, is every vector in $$V$$ a linear combination of elements of $$S$$?
JSON expected answer: Yes.
-/
theorem la_30_turn_01_oracle {V : Type} [AddCommGroup V] [Module ℚ V] (e1 e2 v : V) (h : Spans e1 e2) : Rep e1 e2 v := by
  exact h v

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system, let $$S=\{e_1,e_2\}$$ span $$V$$. Define $$Rep_S(x)\iff\exists a,b\ (x=ae_1+be_2)$$ and $$AllRep([x_1,\ldots,x_n])\iff\bigwedge_{i=1}^{n}Rep_S(x_i)$$. Does $$AllRep([u,v,u])$$ hold for vectors in $$V$$?
JSON expected answer: Yes.
-/
theorem la_30_turn_02_oracle {V : Type} [AddCommGroup V] [Module ℚ V] (e1 e2 u v : V) (h : Spans e1 e2) : AllRep e1 e2 [u,v,u] := by
  exact ⟨h u,h v,h u,trivial⟩

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now retain ordinary rational vector-space operations, but spanning is a designation without the usual coverage requirement. Declare $$S=\{e_1,e_2\}$$ spanning, stipulate $$u=e_1+e_2$$, and let $$v$$ have no representation $$v=ae_1+be_2$$. Is $$v$$ expressible from $$S$$?
JSON expected answer: No.
-/
theorem la_30_turn_03_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ Rep m.e1 m.e2 m.v := by
  exact m.hv

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard spanning consequence hold for $$v$$?
JSON expected answer: No.
-/
theorem la_30_turn_04_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ Rep m.e1 m.e2 m.v := by
  exact m.hv

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, is $$u+u$$ expressible as a linear combination of $$S$$?
JSON expected answer: Yes.
-/
theorem la_30_turn_05_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : Rep m.e1 m.e2 (m.u+m.u) := by
  refine ⟨2,2,?_⟩; rw [m.hu]; simp only [show (2:ℚ)=1+1 by norm_num,add_smul,one_smul]; abel

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$Rep_S(x)\iff\exists a,b\ (x=ae_1+be_2)$$ and $$AllRep([])=true$$, $$AllRep([x]+L)\iff Rep_S(x)\land AllRep(L)$$. Does $$AllRep([])$$ hold?
JSON expected answer: Yes.
-/
theorem la_30_turn_06_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : AllRep m.e1 m.e2 [] := by
  trivial

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, does $$Rep_S(v)$$ hold?
JSON expected answer: No.
-/
theorem la_30_turn_07_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ Rep m.e1 m.e2 m.v := by
  exact m.hv

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$AllRep([u,v,u])$$ hold?
JSON expected answer: No.
-/
theorem la_30_turn_08_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ AllRep m.e1 m.e2 [m.u,m.v,m.u] := by
  intro h; exact m.hv h.2.1

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$Rep_S(w)$$ hold for another vector $$w$$?
JSON expected answer: cannot be determined
-/
theorem la_30_turn_09_oracle : Underdetermined (fun _ : Model Vec => True) (fun m => Rep m.e1 m.e2 m.w) := by
  exact varies

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$\|v\|$$?
JSON expected answer: cannot be determined
-/
theorem la_30_turn_10_oracle : Underdetermined (fun _ : Model Vec × Nat => True) (fun m => m.2) := by
  exact ⟨(completion true,0),(completion true,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, does a spanning declaration guarantee representability of every vector?
JSON expected answer: No.
-/
theorem la_30_turn_11_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ Spans m.e1 m.e2 := by
  intro h; exact m.hv (h m.v)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does “every vector is a linear combination of $$S$$” follow from spanning in ordinary linear algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem la_30_turn_12_oracle {V U : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup U] [Module ℚ U] (e1 e2 v : V) (h : Spans e1 e2) (m : Model U) : Rep e1 e2 v ∧ ¬ Rep m.e1 m.e2 m.v := by
  exact ⟨h v,m.hv⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Is $$v$$ representable from $$S$$ in the standard system, and is it representable in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem la_30_turn_13_oracle {V U : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup U] [Module ℚ U] (e1 e2 v : V) (h : Spans e1 e2) (m : Model U) : Rep e1 e2 v ∧ ¬ Rep m.e1 m.e2 m.v := by
  exact ⟨h v,m.hv⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary linear algebra. If $$S$$ spans $$V$$, is every $$v\in V$$ a linear combination of $$S$$?
JSON expected answer: Yes.
-/
theorem la_30_turn_14_oracle {V : Type} [AddCommGroup V] [Module ℚ V] (e1 e2 v : V) (h : Spans e1 e2) : Rep e1 e2 v := by
  exact h v

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using the standard spanning set, does $$AllRep([u,v,u])$$ hold?
JSON expected answer: Yes.
-/
theorem la_30_turn_15_oracle {V : Type} [AddCommGroup V] [Module ℚ V] (e1 e2 u v : V) (h : Spans e1 e2) : AllRep e1 e2 [u,v,u] := by
  exact ⟨h u,h v,h u,trivial⟩

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$Rep_S(v)$$ hold?
JSON expected answer: No.
-/
theorem la_30_turn_16_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ Rep m.e1 m.e2 m.v := by
  exact m.hv
