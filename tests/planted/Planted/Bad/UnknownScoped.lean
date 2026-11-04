import Planted.Base

/-!
# Planted failure: a scoped extension the census neither decodes nor reviews

`@[ext]` records its theorem in a scoped extension the census does not decode, and no scoped
extension is on the reviewed list. The census must refuse, naming it (`unknown_extension`, scoped).
-/

namespace Planted.Bad.UnknownScoped

@[ext] structure Pair where
  x : Nat
  y : Nat

end Planted.Bad.UnknownScoped
