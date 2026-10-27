module

/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplanePowerFrameTransition
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneTransitions
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistFrameScalar
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameTransitionTransport
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistTransitions

set_option backward.privateInPublic true
@[expose] public section

/-! # Twist Frame Restriction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistFrameRestriction.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- On a coordinate overlap, the two `O(n)` frames differ by the `n`th power
of `X_k / X_i`. -/
theorem coordinateHyperplanePoleSheafPowerTrivialization_restrict_transition
    (i k j : σ) (n : ℕ) :
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization
          (R := R) i j n)).hom =
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
          (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization
            (R := R) k j n)).hom ≫
        UnitScalar.unitEndomorphismOfTopSection
          ((OpenFrames.Scheme.Modules.openTopSection
            (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
            (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k))) ^ n) :=
  HyperplanePowerFrameTransition.MvPolynomial.coordinateHyperplanePolePower_frameTransition (R := R) i k j n

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistFrameRestriction.MvPolynomial
