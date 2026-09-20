import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/automata_theory_and_formal_languages/AT-33.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AT-33 — Two distinguishable states declared equivalent
Source: test case definition test_cases/automata_theory_and_formal_languages/AT-33.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AT_33
open Benchmark

/-- q₁,q₂,q_f,q_r,u,v use state labels 0 through 5. -/
def run (δ : Nat → Nat → Nat) (q : Nat) (w : List Nat) := w.foldl δ q
structure Model where
  step : Nat → Nat → Nat
  accepting : Nat → Prop
  related : Nat → Nat → Prop
  equivalence : Equivalence related
  ha0 : step 0 0=2
  ha1 : step 1 0=3
  hb2 : step 2 1=4
  hb3 : step 3 1=5
  yes2 : accepting 2
  no3 : ¬ accepting 3
  eq01 : related 0 1
  neq23 : ¬ related 2 3
  neq45 : ¬ related 4 5

def Behavior (m : Model) (q r : Nat) := ∀ w : List Nat,
  m.accepting (run m.step q w) ↔ m.accepting (run m.step r w)
def Well (m : Model) (q r : Nat) (w : List Nat) :=
  m.related q r → m.related (run m.step q w) (run m.step r w)
def StdWell (m : Model) (q r : Nat) (w : List Nat) :=
  Behavior m q r → Behavior m (run m.step q w) (run m.step r w)

theorem stdDifferent (m : Model) : ¬ Behavior m 0 1 := by
  intro h
  have hh := h [0]
  simp only [run,List.foldl_cons,List.foldl_nil,m.ha0,m.ha1] at hh
  exact m.no3 (hh.mp m.yes2)

def classOf (q : Nat) := if q=0 ∨ q=1 then 0 else q

def completion (extra : Bool) : Model where
  step := fun q x => if (q,x)=(0,0) then 2 else if (q,x)=(1,0) then 3
    else if (q,x)=(2,1) then 4 else if (q,x)=(3,1) then 5
    else if extra then 2 else if q=0 then 2 else 3
  accepting := fun q => q=2
  related := fun q r => classOf q=classOf r
  equivalence := ⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩
  ha0 := rfl
  ha1 := rfl
  hb2 := rfl
  hb3 := rfl
  yes2 := rfl
  no3 := by decide
  eq01 := rfl
  neq23 := by decide
  neq45 := by decide

theorem noShort (m : Model) : ¬ Well m 0 1 [0] := by
  intro h
  have hh := h m.eq01
  simp only [run,List.foldl_cons,List.foldl_nil,m.ha0,m.ha1] at hh
  exact m.neq23 hh
theorem noLong (m : Model) : ¬ Well m 0 1 [0,1] := by
  intro h
  have hh := h m.eq01
  simp only [run,List.foldl_cons,List.foldl_nil,m.ha0,m.ha1,m.hb2,m.hb3] at hh
  exact m.neq45 hh

end AT_33

open AT_33 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In an ordinary DFA, are two states equivalent only if no input suffix distinguishes their acceptance behavior?
JSON expected answer: Yes.
-/
theorem at_33_turn_01_oracle {Q Σ : Type} (step : Q → Σ → Q)
    (accepting : Q → Prop) (q r : Q)
    (h : ∀ w : List Σ, accepting (w.foldl step q) ↔ accepting (w.foldl step r))
    (w : List Σ) : accepting (w.foldl step q) ↔ accepting (w.foldl step r) := by
  exact h w

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In the standard DFA let $$\delta(q_1,a)=q_f$$ and $$\delta(q_2,a)=q_r$$, with $$q_f$$ accepting and $$q_r$$ rejecting. Define $$Well(q,r,w)\iff(q\sim r\Rightarrow\delta^*(q,w)\sim\delta^*(r,w))$$ using ordinary behavioral equivalence. Does $$Well(q_1,q_2,a)$$ hold?
JSON expected answer: Yes.
-/
theorem at_33_turn_02_oracle (m : Model) : StdWell m 0 1 [0] := by
  intro h; exact False.elim (stdDifferent m h)

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now retain ordinary transitions and acceptance but use an equivalence relation $$\sim$$ unrelated to behavior. Stipulate $$q_1\sim q_2$$, $$q_f\not\sim q_r$$, $$\delta(q_f,b)=u$$, $$\delta(q_r,b)=v$$, and $$u\not\sim v$$. The transitions on $$c$$ are total but unconstrained. Does $$q_1\sim q_2$$ hold?
JSON expected answer: Yes.
-/
theorem at_33_turn_03_oracle (m : Model) : m.related 0 1 := by
  exact m.eq01

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does the standard distinguishability criterion force $$q_1\not\sim q_2$$?
JSON expected answer: No.
-/
theorem at_33_turn_04_oracle (m : Model) : ¬ (¬ m.related 0 1) := by
  intro h; exact h m.eq01

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$\delta^*(q_1,ab)\sim\delta^*(q_2,ab)$$ hold?
JSON expected answer: No.
-/
theorem at_33_turn_05_oracle (m : Model) : ¬ m.related (run m.step 0 [0,1]) (run m.step 1 [0,1]) := by
  simpa [run,m.ha0,m.ha1,m.hb2,m.hb3] using m.neq45

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system reconstruct $$Well(q,r,w)\iff(q\sim r\Rightarrow\delta^*(q,w)\sim\delta^*(r,w))$$ with ordinary extended transitions. Does $$Well(q_1,q_2,\varepsilon)$$ hold?
JSON expected answer: Yes.
-/
theorem at_33_turn_06_oracle (m : Model) : Well m 0 1 [] := by
  intro h; exact h

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$Well(q_1,q_2,a)$$ hold?
JSON expected answer: No.
-/
theorem at_33_turn_07_oracle (m : Model) : ¬ Well m 0 1 [0] := by
  exact noShort m

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$Well(q_1,q_2,ab)$$ hold?
JSON expected answer: No.
-/
theorem at_33_turn_08_oracle (m : Model) : ¬ Well m 0 1 [0,1] := by
  exact noLong m

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$Well(q_1,q_2,c)$$ hold?
JSON expected answer: cannot be determined
-/
theorem at_33_turn_09_oracle : Underdetermined (fun _ : Model => True) (fun m => Well m 0 1 [2]) := by
  refine ⟨completion true,completion false,trivial,trivial,?_⟩; intro h; have hh := h.mp (by simp [Well,run,completion,classOf]); norm_num [Well,run,completion,classOf] at hh

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In the modified system, what does $$minimize(\mathcal A)$$ return?
JSON expected answer: cannot be determined
-/
theorem at_33_turn_10_oracle : Underdetermined (fun _ : Model × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false,0),(completion false,1),trivial,trivial,by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, can states with distinguishable behavior nevertheless be declared equivalent?
JSON expected answer: Yes.
-/
theorem at_33_turn_11_oracle (m : Model) : m.related 0 1 ∧ ¬ Behavior m 0 1 := by
  exact ⟨m.eq01,stdDifferent m⟩

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement $$q_1\sim q_2$$ hold under standard DFA equivalence, in the modified system, or in both?
JSON expected answer: Only in the modified system.
-/
theorem at_33_turn_12_oracle (m : Model) : ¬ Behavior m 0 1 ∧ m.related 0 1 := by
  exact ⟨stdDifferent m,m.eq01⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Are $$q_1$$ and $$q_2$$ equivalent in the standard DFA, and are they equivalent in the modified system?
JSON expected answer: No in the standard system and yes in the modified system.
-/
theorem at_33_turn_13_oracle (m : Model) : ¬ Behavior m 0 1 ∧ m.related 0 1 := by
  exact ⟨stdDifferent m,m.eq01⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to standard DFA equivalence. If suffix $$a$$ distinguishes $$q_1$$ and $$q_2$$, are they equivalent?
JSON expected answer: No.
-/
theorem at_33_turn_14_oracle (m : Model) : ¬ Behavior m 0 1 := by
  exact stdDifferent m

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using standard behavioral equivalence, does $$Well(q_1,q_2,ab)$$ hold?
JSON expected answer: Yes.
-/
theorem at_33_turn_15_oracle (m : Model) : StdWell m 0 1 [0,1] := by
  intro h; exact False.elim (stdDifferent m h)

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$q_1\sim q_2$$ hold?
JSON expected answer: Yes.
-/
theorem at_33_turn_16_oracle (m : Model) : m.related 0 1 := by
  exact m.eq01
