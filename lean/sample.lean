/-
Placeholder artifact for templates/test_case_template.json.

The template's `formal_artifacts.lean_file` points here so that a freshly copied
test case validates out of the box. Replace it with the real oracle theorem set —
see lean/ALG_021.lean for a worked example whose theorem names line up with
`formal_artifacts.oracle_theorems` and with `conversation_framework`.
-/

namespace Sample

/-- Modified successor: advances by two instead of one. -/
def msucc (n : ℕ) : ℕ := n + 2

/-- One oracle theorem per graded turn; this is the shape to follow. -/
theorem baseline_successor : Nat.succ 3 = 4 := rfl

end Sample
