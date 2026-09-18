import oracles.Support

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-!
# oracles/abstract_algebra/AA-36.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Case: AA-36 — Left distributive only
Source: test case definition test_cases/abstract_algebra/AA-36.json
Turn 0 configures responses and has no mathematical oracle.
-/

namespace AA_36
open Benchmark

/-- Only the laws retained by Turn 3 are fields of this model. -/
structure Model (α : Type) where
  add : α → α → α
  mul : α → α → α
  a : α
  b : α
  c : α
  p : α
  q : α
  assoc : ∀ x y z, add (add x y) z = add x (add y z)
  left : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  hp : mul (add a b) c = p
  hq : add (mul a c) (mul b c) = q
  different : p ≠ q

def E (m : Model α) (x y z : α) := m.mul (m.add x y) z

def addF (f g : Bool → Bool) : Bool → Bool := fun x => Bool.xor (f x) (g x)
/-- Composition on Boolean functions is left distributive for pointwise XOR. -/
def completion (flag : Bool) : Model (Bool → Bool) where
  add := addF
  mul := fun f g => g ∘ f
  a := fun _ => flag
  b := fun _ => false
  c := Bool.not
  p := fun _ => !flag
  q := fun _ => flag
  assoc := by
    intro f g h
    funext x
    change Bool.xor (Bool.xor (f x) (g x)) (h x) =
      Bool.xor (f x) (Bool.xor (g x) (h x))
    cases f x <;> cases g x <;> cases h x <;> rfl
  left := by intros; rfl
  hp := by funext x; cases flag <;> rfl
  hq := by funext x; cases flag <;> rfl
  different := by
    intro h
    have hh := congrFun h false
    cases flag <;> simp at hh

theorem failure (m : Model α) : E m m.a m.b m.c ≠ m.add (m.mul m.a m.c) (m.mul m.b m.c) := by
  rw [E, m.hp, m.hq]
  exact m.different

theorem varies : Underdetermined (fun _ : Model (Bool → Bool) => True)
    (fun m => E m m.b m.c m.a = m.add (m.mul m.b m.a) (m.mul m.c m.a)) := by
  refine ⟨completion false, completion true, trivial, trivial, ?_⟩
  intro h
  have yes : E (completion false) (completion false).b (completion false).c (completion false).a =
      (completion false).add ((completion false).mul (completion false).b (completion false).a)
        ((completion false).mul (completion false).c (completion false).a) := by funext x; rfl
  have bad := h.mp yes
  have hh := congrFun bad false
  contradiction

end AA_36

open AA_36 Benchmark

/-- Turn 1: Verify competence with the standard foundational rule before modification.
Question: In a standard ring, does right distributivity give $$(x+y)\cdot z=x\cdot z+y\cdot z$$?
JSON expected answer: Yes.
-/
theorem aa_36_turn_01_oracle {R : Type} [Ring R] (x y z : R) : (x+y)*z = x*z+y*z := by
  exact add_mul x y z

/-- Turn 2: Verify competence with the corresponding standard derived rule before modification.
Question: In a standard ring define $$E(x,y,z)=(x+y)\cdot z$$. Does $$E(x+y,z,w)=(x\cdot w+y\cdot w)+z\cdot w$$ hold?
JSON expected answer: Yes.
-/
theorem aa_36_turn_02_oracle {R : Type} [Ring R] (x y z w : R) : ((x+y)+z)*w = (x*w+y*w)+z*w := by
  simp only [add_mul]

/-- Turn 3: Test adoption of the modified version of the foundational rule established in Turn 1.
Question: Now use two total operations $$+$$ and $$\cdot$$ on a carrier containing $$a,b,c,p,q$$. Addition is associative, and left distributivity holds universally. Stipulate $$(a+b)\cdot c=p$$ and $$a\cdot c+b\cdot c=q$$ with $$p\neq q$$. No right-distributivity law is imposed. Does right distributivity hold for $$(a,b,c)$$?
JSON expected answer: No.
-/
theorem aa_36_turn_03_oracle (m : Model α) : E m m.a m.b m.c ≠ m.add (m.mul m.a m.c) (m.mul m.b m.c) := by
  exact failure m

/-- Turn 4: Verify rejection of the superseded standard rule within the modified system.
Question: In the modified system, does $$(a+b)\cdot c=a\cdot c+b\cdot c$$ hold?
JSON expected answer: No.
-/
theorem aa_36_turn_04_oracle (m : Model α) : E m m.a m.b m.c ≠ m.add (m.mul m.a m.c) (m.mul m.b m.c) := by
  exact failure m

/-- Turn 5: Verify repeated application of the modified foundational rule.
Question: In the modified system, does $$a\cdot((b+c)+a)=(a\cdot b+a\cdot c)+a\cdot a$$ hold?
JSON expected answer: Yes.
-/
theorem aa_36_turn_05_oracle (m : Model α) : m.mul m.a (m.add (m.add m.b m.c) m.a) = m.add (m.add (m.mul m.a m.b) (m.mul m.a m.c)) (m.mul m.a m.a) := by
  rw [m.left, m.left]

/-- Turn 6: Reconstruct the derived rule established in Turn 2 under the modified foundational rule and verify its base case.
Question: In the modified system, reconstruct $$E(x,y,z)=(x+y)\cdot z$$. Does $$E(a,b,c)=p$$ hold?
JSON expected answer: Yes.
-/
theorem aa_36_turn_06_oracle (m : Model α) : E m m.a m.b m.c = m.p := by
  exact m.hp

/-- Turn 7: Verify single-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$E(a,b,c)=a\cdot c+b\cdot c$$ hold?
JSON expected answer: No.
-/
theorem aa_36_turn_07_oracle (m : Model α) : E m m.a m.b m.c ≠ m.add (m.mul m.a m.c) (m.mul m.b m.c) := by
  exact failure m

/-- Turn 8: Verify multi-step propagation through the reconstructed derived rule.
Question: In the modified system, does $$E(a,b,c+c)=p+p$$ hold?
JSON expected answer: Yes.
-/
theorem aa_36_turn_08_oracle (m : Model α) : E m m.a m.b (m.add m.c m.c) = m.add m.p m.p := by
  simp only [E, m.left, m.hp]

/-- Turn 9: Detect underdetermination within the supplied derived rule.
Question: In the modified system, does $$E(b,c,a)=b\cdot a+c\cdot a$$ hold?
JSON expected answer: cannot be determined
-/
theorem aa_36_turn_09_oracle : Underdetermined (fun _ : Model (Bool → Bool) => True) (fun m => E m m.b m.c m.a = m.add (m.mul m.b m.a) (m.mul m.c m.a)) := by
  exact varies

/-- Turn 10: Detect hallucinated completion of an undefined rule or operation.
Question: In this modified system, what is $$inverse_{\cdot}(a)$$?
JSON expected answer: cannot be determined
-/
theorem aa_36_turn_10_oracle : Underdetermined (fun _ : Model (Bool → Bool) × Nat => True) (fun m => m.2) := by
  exact ⟨(completion false, 0), (completion false, 1), trivial, trivial, by decide⟩

/-- Turn 11: Verify recognition of higher-level consequences of the modified foundational rule.
Question: In this modified system, are left and right distributivity both guaranteed?
JSON expected answer: No.
-/
theorem aa_36_turn_11_oracle (m : Model α) : ¬ (∀ x y z, m.mul (m.add x y) z = m.add (m.mul x z) (m.mul y z)) := by
  intro h; exact failure m (h m.a m.b m.c)

/-- Turn 12: Verify explicit separation between the standard and modified formal systems.
Question: Does the statement $$(a+b)\cdot c=a\cdot c+b\cdot c$$ hold in the standard system, in the modified system, or in both?
JSON expected answer: Only in the standard system.
-/
theorem aa_36_turn_12_oracle {R : Type} [Ring R] (x y z : R) (m : Model α) : (x+y)*z=x*z+y*z ∧ E m m.a m.b m.c ≠ m.add (m.mul m.a m.c) (m.mul m.b m.c) := by
  exact ⟨add_mul x y z, failure m⟩

/-- Turn 13: Verify simultaneous reasoning under distinct standard and modified rule sets.
Question: Does right distributivity hold for $$(a,b,c)$$ in the standard system, and does it hold in the modified system?
JSON expected answer: Yes in the standard system and no in the modified system.
-/
theorem aa_36_turn_13_oracle {R : Type} [Ring R] (x y z : R) (m : Model α) : (x+y)*z=x*z+y*z ∧ E m m.a m.b m.c ≠ m.add (m.mul m.a m.c) (m.mul m.b m.c) := by
  exact ⟨add_mul x y z, failure m⟩

/-- Turn 14: Detect residual contamination of the standard foundational rule after modified-system reasoning.
Question: Return to the standard system. Does $$(a+b)\cdot c=a\cdot c+b\cdot c$$ hold?
JSON expected answer: Yes.
-/
theorem aa_36_turn_14_oracle {R : Type} [Ring R] (x y z : R) : (x+y)*z = x*z+y*z := by
  exact add_mul x y z

/-- Turn 15: Verify recovery of the corresponding standard derived rule after modified-system reasoning.
Question: Still using a standard ring, does $$E(x+y,z,w)=(x\cdot w+y\cdot w)+z\cdot w$$ hold?
JSON expected answer: Yes.
-/
theorem aa_36_turn_15_oracle {R : Type} [Ring R] (x y z w : R) : ((x+y)+z)*w = (x*w+y*w)+z*w := by
  simp only [add_mul]

/-- Turn 16: Verify bidirectional switching by re-entering the modified system after standard recovery.
Question: Return to the modified system. Does $$(a+b)\cdot c=a\cdot c+b\cdot c$$ hold?
JSON expected answer: No.
-/
theorem aa_36_turn_16_oracle (m : Model α) : E m m.a m.b m.c ≠ m.add (m.mul m.a m.c) (m.mul m.b m.c) := by
  exact failure m
