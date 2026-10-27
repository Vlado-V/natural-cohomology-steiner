module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Data.ZMod.Basic

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

/-- The first-coordinate subgroup, including the identity case `n = 1`. -/
def cyclicLabels (n : ℕ) : Multiplicative (ZMod n) →* Multiplicative (Fin 2 → ZMod n) where
  toFun a := Multiplicative.ofAdd (fun i => if i = 0 then a.toAdd else 0)
  map_one' := by ext i; simp
  map_mul' a b := by ext i; by_cases h : i = 0 <;> simp [h]

theorem cyclicLabels_injective (n : ℕ) : Function.Injective (cyclicLabels n) := by
  intro a b h
  have h0 := congrArg (fun x : Multiplicative (Fin 2 → ZMod n) => x.toAdd 0) h
  simpa [cyclicLabels] using h0

end SteinerGeometry
