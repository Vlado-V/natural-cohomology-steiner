module

public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TameCharacters
public import Mathlib.Analysis.Complex.Polynomial.Basic

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

noncomputable section

/-- A finite cyclic group has exactly its order many complex unit characters. -/
theorem cyclicScalarCharacters_card (m : ℕ) [NeZero m] :
    Nat.card (Multiplicative (ZMod m) →* ℂˣ) = m := by
  let G := Multiplicative (ZMod m)
  have hG : (Fintype.card G : ℂ) ≠ 0 := by
    simpa only [G, Fintype.card_multiplicative, ZMod.card, Nat.cast_ne_zero] using NeZero.ne m
  have := OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TameCharacters.tameFiniteAbelian_hasEnoughRoots
    ℂ G hG
  simpa only [G, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] using
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ

/-- Actual distinct scalar characters, indexed by the required finite cardinal. -/
theorem exists_cyclicScalarCharacters (m : ℕ) [NeZero m] :
    ∃ χ : Fin m → (Multiplicative (ZMod m) →* ℂˣ), Function.Injective χ := by
  classical
  let C := Multiplicative (ZMod m) →* ℂˣ
  let : Finite C := Nat.finite_of_card_ne_zero ((cyclicScalarCharacters_card m).trans_ne (NeZero.ne m))
  let : Fintype C := Fintype.ofFinite C
  let e : Fin m ≃ C := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact (cyclicScalarCharacters_card m).symm)
  exact ⟨e, e.injective⟩

end
end SteinerGeometry
