module

public import SteinerGeometry.FrameMapCoefficient
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistMaps

set_option backward.privateInPublic true
@[expose] public section

/-! Transport a map of negative powers to the corresponding integer twists. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry.NegativeTwistCast

open CategoryTheory AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective

universe u

variable {R : Type u} [CommRing R] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Regard a map between successive negative powers as a map of integer twists. -/
def castMap (j : σ) (b : ℕ) (d : ℤ)
    (hs : d = Int.negSucc (b + 1)) (ht : d + 1 = Int.negSucc b)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (b + 2) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (b + 1)) :
    TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d + 1) :=
  eqToHom (by rw [hs]; rfl) ≫ f ≫ eqToHom (by rw [ht]; rfl)

/-- Regard a morphism of the corresponding integer twists as a negative-power map. -/
def uncastMap (j : σ) (b : ℕ) (d : ℤ)
    (hs : d = Int.negSucc (b + 1)) (ht : d + 1 = Int.negSucc b)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d + 1)) :
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (b + 2) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (b + 1) :=
  eqToHom (by rw [hs]; rfl) ≫ f ≫ eqToHom (by rw [ht]; rfl)

@[simp] theorem castMap_uncastMap (j : σ) (b : ℕ) (d : ℤ)
    (hs : d = Int.negSucc (b + 1)) (ht : d + 1 = Int.negSucc b)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d + 1)) :
    castMap j b d hs ht (uncastMap j b d hs ht f) = f := by
  subst d
  simp only [castMap, uncastMap, eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp] theorem uncastMap_castMap (j : σ) (b : ℕ) (d : ℤ)
    (hs : d = Int.negSucc (b + 1)) (ht : d + 1 = Int.negSucc b)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (b + 2) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (b + 1)) :
    uncastMap j b d hs ht (castMap j b d hs ht f) = f := by
  subst d
  simp only [castMap, uncastMap, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Transporting the source and target degree does not change the scalar of the
map in the canonical chart frames. -/
theorem coefficient_castMap (i j : σ) (b : ℕ) (d : ℤ)
    (hs : d = Int.negSucc (b + 1)) (ht : d + 1 = Int.negSucc b)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (b + 2) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (b + 1)) :
    FrameMapCoefficient.coefficient (castMap j b d hs ht f)
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) i j d))
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d + 1))
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) i j (d + 1))) =
    FrameMapCoefficient.coefficient f
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
        (R := R) i j (b + 2))
      (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
        (R := R) i j (b + 1)) := by
  subst d
  simp only [castMap, eqToHom_refl, Category.id_comp, Category.comp_id,
    TwistPowers.MvPolynomial.coordinateHyperplaneTwist,
    TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization]
  rfl

end SteinerGeometry.NegativeTwistCast
