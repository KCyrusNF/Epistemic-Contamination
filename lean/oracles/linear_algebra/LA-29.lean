import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/linear_algebra/LA-29.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: LA-29 — Same vector has two incompatible coordinate decompositions in a declared basis
Source: test case definition test_cases/linear_algebra/LA-29.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace LA_29
open Benchmark

abbrev Vec := ℚ × ℚ
structure Model (V : Type) [AddCommGroup V] [Module ℚ V] where
  e1 : V
  e2 : V
  v : V
  w : V
  nonzero : v≠0
  wv : w≠v
  first : v=(1:ℚ) • e1+(0:ℚ) • e2
  second : v=(0:ℚ) • e1+(1:ℚ) • e2

def Coord [AddCommGroup V] [Module ℚ V] (m : Model V) (x : V) (p : ℚ × ℚ) :=
  x=p.1 • m.e1+p.2 • m.e2

theorem two [AddCommGroup V] [Module ℚ V] (m : Model V) : Coord m m.v (1,0) ∧ Coord m m.v (0,1) ∧ ((1,0):ℚ×ℚ)≠(0,1) := by
  exact ⟨m.first,m.second,by decide⟩
theorem notUnique [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ ∃! p, Coord m m.v p := by
  rintro ⟨p,hp,unique⟩
  have bad := (unique (1,0) m.first).trans (unique (0,1) m.second).symm
  have hh := congrArg Prod.fst bad
  norm_num at hh

def completion (extra : Bool) : Model Vec where
  e1 := (1,0)
  e2 := (1,0)
  v := (1,0)
  w := if extra then (0,0) else (0,1)
  nonzero := by norm_num
  wv := by cases extra <;> norm_num
  first := by simp
  second := by simp

theorem varies : Underdetermined (fun _ : Model Vec => True) (fun m => ∃ p, Coord m m.w p) := by
  refine ⟨completion true,completion false,trivial,trivial,?_⟩
  intro h
  have yes : ∃ p, Coord (completion true) (completion true).w p := ⟨(0,0),by simp [Coord,completion]⟩
  rcases h.mp yes with ⟨p,hp⟩
  have hh := congrArg Prod.snd hp
  simp [completion] at hh

/-- The inverse of the basis coordinate equivalence reconstructs the vector. -/
theorem standardUnique {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (b : Module.Basis (Fin 2) 𝕜 V) (v : V) : ∃! c : Fin 2 → 𝕜, b.equivFun.symm c=v := by
  refine ⟨b.equivFun v,b.equivFun.symm_apply_apply v,?_⟩
  intro c hc
  exact b.equivFun.symm.injective (hc.trans (b.equivFun.symm_apply_apply v).symm)

end LA_29

open LA_29 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In ordinary linear algebra, does a basis give each vector a unique coordinate decomposition?
JSON expected answer: Yes.
-/
theorem la_29_turn_01_oracle {𝕜 V ι : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (b : Module.Basis ι 𝕜 V) (v : V) : ∃! c : ι →₀ 𝕜, b.repr.symm c = v := by
  refine ⟨b.repr v,b.repr.symm_apply_apply v,?_⟩
  intro c hc
  exact b.repr.symm.injective (hc.trans (b.repr.symm_apply_apply v).symm)

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard system with basis $$B=(e_1,e_2)$$ define $$Coord_B(x,(a,b))\iff x=ae_1+be_2$$ and $$C_B(x)=\{(a,b):Coord_B(x,(a,b))\}$$. Is $$C_B(v)$$ a singleton?
JSON expected answer: Yes.
-/
theorem la_29_turn_02_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (b : Module.Basis (Fin 2) 𝕜 V) (v : V) : ∃! c : Fin 2 → 𝕜, b.equivFun.symm c=v := by
  exact standardUnique b v

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now retain ordinary rational vector-space operations, but let basis be a designation without an independence axiom. Declare $$B=(e_1,e_2)$$ a basis and stipulate $$v=1e_1+0e_2=0e_1+1e_2$$ with $$v\neq\mathbf0$$. Distinct coordinate pairs need not denote distinct vectors. Are the coordinates of $$v$$ unique?
JSON expected answer: No.
-/
theorem la_29_turn_03_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ ∃! p, Coord m m.v p := by
  exact notUnique m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard uniqueness-of-coordinates property hold for $$v$$?
JSON expected answer: No.
-/
theorem la_29_turn_04_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ ∃! p, Coord m m.v p := by
  exact notUnique m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, are both coordinate pairs $$(1,0)$$ and $$(0,1)$$ valid decompositions of $$v$$?
JSON expected answer: Yes.
-/
theorem la_29_turn_05_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : Coord m m.v (1,0) ∧ Coord m m.v (0,1) := by
  exact ⟨m.first,m.second⟩

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$Coord_B(x,(a,b))\iff x=ae_1+be_2$$ and $$C_B(x)=\{(a,b):Coord_B(x,(a,b))\}$$. Does $$Coord_B(v,(1,0))$$ hold?
JSON expected answer: Yes.
-/
theorem la_29_turn_06_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : Coord m m.v (1,0) := by
  exact m.first

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In this modified system, does $$Coord_B(v,(0,1))$$ hold?
JSON expected answer: Yes.
-/
theorem la_29_turn_07_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : Coord m m.v (0,1) := by
  exact m.second

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, are there distinct $$p,q\in C_B(v)$$?
JSON expected answer: Yes.
-/
theorem la_29_turn_08_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ∃ p q, Coord m m.v p ∧ Coord m m.v q ∧ p≠q := by
  exact ⟨(1,0),(0,1),m.first,m.second,by decide⟩

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, is $$C_B(w)$$ nonempty for a vector $$w\neq v$$?
JSON expected answer: cannot be determined
-/
theorem la_29_turn_09_oracle : Underdetermined (fun _ : Model Vec => True) (fun m => ∃ p, Coord m m.w p) := by
  exact varies

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$\|v\|$$?
JSON expected answer: cannot be determined
-/
theorem la_29_turn_10_oracle : Underdetermined (fun _ : Model Vec × Nat => True) (fun m => m.2) := by
  exact ⟨(completion true,0),(completion true,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, does being declared a basis guarantee unique coordinates?
JSON expected answer: No.
-/
theorem la_29_turn_11_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ ∃! p, Coord m m.v p := by
  exact notUnique m

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does uniqueness of coordinates for a basis hold in ordinary linear algebra, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem la_29_turn_12_oracle {𝕜 V U : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module ℚ U] (b : Module.Basis (Fin 2) 𝕜 V) (v : V) (m : Model U) : (∃! c : Fin 2 → 𝕜, b.equivFun.symm c=v) ∧ ¬ ∃! p, Coord m m.v p := by
  exact ⟨standardUnique b v,notUnique m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Are the coordinates of $$v$$ unique in the standard system, and are they unique in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem la_29_turn_13_oracle {𝕜 V U : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddCommGroup U] [Module ℚ U] (b : Module.Basis (Fin 2) 𝕜 V) (v : V) (m : Model U) : (∃! c : Fin 2 → 𝕜, b.equivFun.symm c=v) ∧ ¬ ∃! p, Coord m m.v p := by
  exact ⟨standardUnique b v,notUnique m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to ordinary linear algebra. Does a basis give unique coordinates?
JSON expected answer: Yes.
-/
theorem la_29_turn_14_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (b : Module.Basis (Fin 2) 𝕜 V) (v : V) : ∃! c : Fin 2 → 𝕜, b.equivFun.symm c=v := by
  exact standardUnique b v

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using an ordinary basis, is $$C_B(v)$$ a singleton?
JSON expected answer: Yes.
-/
theorem la_29_turn_15_oracle {𝕜 V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (b : Module.Basis (Fin 2) 𝕜 V) (v : V) : ∃! c : Fin 2 → 𝕜, b.equivFun.symm c=v := by
  exact standardUnique b v

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Are the coordinates of $$v$$ unique?
JSON expected answer: No.
-/
theorem la_29_turn_16_oracle [AddCommGroup V] [Module ℚ V] (m : Model V) : ¬ ∃! p, Coord m m.v p := by
  exact notUnique m
