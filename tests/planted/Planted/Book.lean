import Planted.Base

/-!
# Planted effects

One of each effect the census must list, outside the foundations, in each scope Lean allows:
global (escapes the file), scoped (escapes when the namespace is opened), local (never escapes,
and never reaches the .olean: only the source pass sees it). Also: removals, activation, a local
effect made by a macro, proof-local instances, a section instance variable and an option. Each local one is used after it, so
the source pass must elaborate the file in order to parse it. The reducibility changes come last,
since `Planted.area` is irreducible after them.
-/

set_option autoImplicit false

namespace Planted.Book

open Planted

-- Activation: opening a namespace makes its scoped entries active in this file.
open Planted.Scope

theorem uses_activated : Shape.sides () = 0 := rfl

/-! ## Instances -/

instance (priority := 900) instShapeNat : Shape Nat := ⟨fun _ => 0⟩

scoped instance instShapeString : Shape String := ⟨fun _ => 1⟩

local instance instShapeBool : Shape Bool := ⟨fun _ => 2⟩

theorem uses_local_instance : Shape.sides true = 2 := rfl

/-! ## Simp lemmas -/

@[simp] theorem area_mk (n : Nat) : area ⟨n⟩ = n := rfl

theorem area_mk' (n : Nat) : area ⟨n⟩ = n := rfl

attribute [scoped simp] area_mk'

attribute [local simp] Nat.add_zero

theorem uses_local_simp (n : Nat) : n + 0 = n := by simp

/-! ## Notation -/

notation:max "plantedG " t:max => Planted.area t

scoped notation:max "plantedS " t:max => Planted.perimeter t

local notation:max "plantedL " t:max => Planted.volume t

theorem uses_global_notation (t : Tri) : plantedG t = area t := rfl

theorem uses_local_notation (t : Tri) : plantedL t = volume t := rfl

/-! ## Macros -/

macro "planted_g" : tactic => `(tactic| rfl)

scoped macro "planted_s" : tactic => `(tactic| rfl)

local macro "planted_l" : tactic => `(tactic| rfl)

theorem uses_local_macro : 1 = 1 := by planted_l

-- A macro rule on a syntax kind this file does not declare: it changes `trivial` for importers.
macro_rules | `(tactic| trivial) => `(tactic| rfl)

/-! ## Coercions -/

def toTri (n : Nat) : Tri := ⟨n⟩

attribute [coe] toTri

instance instCoeNatTri : Coe Nat Tri := ⟨toTri⟩

local instance instCoeBoolTri : Coe Bool Tri := ⟨fun _ => ⟨0⟩⟩

scoped instance instCoeStringTri : Coe String Tri := ⟨fun _ => ⟨1⟩⟩

/-! ## Classes: a class of this module (own), and another module's structure made a class (escapes) -/

class OwnShape (α : Type) where
  n : Nat

attribute [class] Planted.Tag

/-! ## A local effect made by a macro: only the expansion carries `local` -/

macro "planted_local_simp " x:ident : command => `(attribute [local simp] $x)

planted_local_simp Nat.zero_add

theorem uses_generated_local_simp (n : Nat) : 0 + n = n := by simp

/-! ## Proof-local instances -/

theorem uses_haveI : Nonempty Tri := by
  haveI : Inhabited Tri := ⟨⟨0⟩⟩
  exact inferInstance

def uses_letI : Nat :=
  letI : Shape Tri := ⟨fun _ => 7⟩
  Shape.sides (⟨0⟩ : Tri)

theorem uses_have_instance : Nonempty Tri := by
  have h : Inhabited Tri := ⟨⟨1⟩⟩
  exact inferInstance

theorem uses_classical (p : Prop) : p ∨ ¬p := by
  classical
  exact Classical.em p

open Classical in
theorem uses_open_in (p : Prop) : p ∨ ¬p := Classical.em p

/-! ## A section instance variable -/

section

variable {α : Type} [Shape α]

def sidesOf (x : α) : Nat := Shape.sides x

end

/-! ## Another attribute: a compiler replacement, in a scoped extension the census does not decode -/

def dbl (n : Nat) : Nat := n + n

def dbl' (n : Nat) : Nat := 2 * n

@[csimp] theorem dbl_eq : @dbl = @dbl' := by
  funext n
  exact (Nat.two_mul n).symm

/-! ## Removals: never exported, so only the source pass sees them -/

attribute [-simp] Planted.area_def

attribute [-instance] instShapeNat

/-! ## Reducibility, last -/

attribute [local irreducible] Planted.volume

set_option allowUnsafeReducibility true in
attribute [scoped irreducible] Planted.perimeter

set_option allowUnsafeReducibility true in
attribute [irreducible] Planted.area

end Planted.Book
