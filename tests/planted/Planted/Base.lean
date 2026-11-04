/-!
# Planted base

Stands in for the foundations in the census's self-test (`--foundation Planted.Base`). It
declares what the planted effects attach to, and two effects of its own, which the census must
list and must not flag.
-/

namespace Planted

class Shape (α : Type) where
  sides : α → Nat

structure Tri where
  a : Nat

/-- A plain structure: another module makes it a class with `attribute [class]`. -/
structure Tag where
  n : Nat

def area (t : Tri) : Nat := t.a

def perimeter (t : Tri) : Nat := 3 * t.a

def volume (t : Tri) : Nat := 0 * t.a

/-- An instance in the foundations: listed, not flagged. -/
instance instShapeTri : Shape Tri := ⟨fun _ => 3⟩

/-- A simp lemma in the foundations: listed, not flagged. -/
@[simp] theorem area_def (t : Tri) : area t = t.a := rfl

end Planted

namespace Planted.Scope

/-- A scoped instance in the foundations: active only where `Planted.Scope` is opened. -/
scoped instance instShapeUnit : Planted.Shape Unit := ⟨fun _ => 0⟩

end Planted.Scope
