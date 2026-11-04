import Planted.Base

/-!
# Planted control

The declaration forms the books use (Elements/BookI to BookIII at 391da4e35): theorems with
docstrings, private theorems, examples, defs, abbrevs, `where`, `match`, `variable ... in`,
`open ... in`, `unfold`, `calc`, `show`, an inductive with `deriving DecidableEq`, an instance on that inductive (as I.4
and I.8 have), `@[deprecated]`, `decide`, `cases` and `simp` proofs. Nothing here escapes the
file: the census must find no escaping effect, and learns from this module which non-scoped
extensions plain declarations populate.
-/

namespace Planted.Plain

open Planted

/-- A docstring. -/
theorem two : 1 + 1 = 2 := rfl

private theorem three : 1 + 2 = 3 := by decide

def double (n : Nat) : Nat := n + n

abbrev Four : Nat := 4

inductive Pt where
  | a
  | b
  deriving DecidableEq

/-- An instance on a type declared in this file: own-keyed, as in I.4 and I.8. -/
instance instShapePt : Shape Pt := ⟨fun p => by cases p <;> exact 0⟩

example : Pt.a ≠ Pt.b := by decide

theorem byMatch (p : Pt) : p = .a ∨ p = .b := by
  match p with
  | .a => exact Or.inl rfl
  | .b => exact Or.inr rfl

def withWhere (n : Nat) : Nat := go n
where
  go (k : Nat) : Nat := k

variable (n : Nat) in
theorem withVariable : n + 0 = n := Nat.add_zero n

open Nat in
theorem withOpenIn : succ 0 = 1 := rfl

theorem bySimp (t : Tri) : area t + 0 = t.a := by simp

theorem byUnfold (n : Nat) : double n = n + n := by simp [double]

/-- `unfold` of a declaration from another module, as the books unfold the foundations' (18 uses). -/
theorem byUnfoldForeign (t : Tri) : area t = t.a := by
  unfold area
  try rfl

theorem byCalc (n : Nat) : n + 0 + 0 = n :=
  calc n + 0 + 0 = n + 0 := Nat.add_zero (n + 0)
    _ = n := Nat.add_zero n

theorem byShow (n : Nat) : n = n := by
  show n = n
  rfl

@[deprecated two (since := "2026-11-03")]
theorem oldTwo : 1 + 1 = 2 := rfl

end Planted.Plain
