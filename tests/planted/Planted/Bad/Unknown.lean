import Planted.Base

/-!
# Planted failure: an extension the reviewed list does not name

`assert_not_exists` records an entry in its own extension, which is neither decoded nor on the
census's reviewed list. The census must refuse, naming it (`unknown_extension`).
-/

assert_not_exists Planted.Nope
