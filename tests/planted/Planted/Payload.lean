import Planted.Base

/-!
# Planted payloads

Pairs of exported entries that differ in one behaviour-bearing field only. The census must give
each pair different payloads (`test_planted_simp_in_every_scope`,
`test_planted_coercions_classes_and_attributes`):

- two simp theorems that differ only in `backwardRfl` (SimpTheorems.lean:182): the same statement,
  each proved by `(rfl)`, which marks neither `@[defeq]` (MutualDef.lean:1533 marks only `:= rfl`);
  only the first is `@[backward_defeq]`;
- two simp theorems whose keys differ only in a literal (`tagOf 2`, `tagOf 3`: the numeral is a
  `.lit` key, DiscrTree/Main.lean:285);
- two definitions that differ only in their `@[implemented_by]` target;
- a class with a universe that only an `outParam` uses, so `outLevelParams` is not empty
  (Class.lean:32);
- grind (run 2): an E-matching theorem in each scope, global and scoped, keyed on Base's `perimeter`;
  and two inductives apart only in `[grind cases]` versus `[grind cases eager]`.
-/

universe u v

namespace Planted.Payload

open Planted

/-! ## `backwardRfl` -/

theorem perimeter_bw (t : Tri) : perimeter t = 3 * t.a := (rfl)

attribute [backward_defeq] perimeter_bw

attribute [simp] perimeter_bw

theorem perimeter_plain (t : Tri) : perimeter t = 3 * t.a := (rfl)

attribute [simp] perimeter_plain

/-! ## A literal key -/

def tagOf (n : Nat) : Nat := n

@[simp] theorem tagOf_two : tagOf 2 = 2 := (rfl)

@[simp] theorem tagOf_three : tagOf 3 = 3 := (rfl)

/-! ## The `implemented_by` target -/

def implA (n : Nat) : Nat := n

def implB (n : Nat) : Nat := n + 0

@[implemented_by implA] def viaA (n : Nat) : Nat := n

@[implemented_by implB] def viaB (n : Nat) : Nat := n

/-! ## `outLevelParams` -/

class Measure (α : Type u) (β : outParam (Type v)) where
  measure : α → β

/-! ## grind -/

theorem perimeter_grind (t : Tri) : perimeter t = 3 * t.a := (rfl)

attribute [grind =] perimeter_grind

theorem perimeter_grind' (t : Tri) : perimeter t = 3 * t.a := (rfl)

attribute [scoped grind =] perimeter_grind'

inductive Lazy where
  | p
  | q

inductive Eager where
  | p
  | q

attribute [grind cases] Lazy

attribute [grind cases eager] Eager

end Planted.Payload
