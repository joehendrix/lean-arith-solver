/-
This defines additional operations that could go into Lean's array definitions.
-/

namespace Array
instance {α} [Hashable α] : Hashable (Array α) where
  hash
  | ⟨l⟩ => Hashable.hash l

end Array