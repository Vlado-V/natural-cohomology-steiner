module

public import SteinerGeometry.PolynomialPresentation
public import SteinerGeometry.TransposeTargetIso

set_option backward.privateInPublic true
@[expose] public section

/-! Dual transposes of epimorphic matrices of homogeneous linear forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.NegativeLinearDualEpi
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For the native negative-twist polynomial maps, an epimorphic linear matrix
has epimorphic dual transpose. -/
theorem dual_transpose_epi (j : σ) {a b : ℕ}
    (M : Fin a → Fin b →
      MvPolynomial.homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) 1)
    (hf : Epi (negativeTwistPolynomialMap (R := R) j
      (fun _ : Fin a => 0) (fun _ : Fin b => 1) (by simp) M)) :
    Epi (SheafDual.dualMap (negativeTwistPolynomialMap (R := R) j
      (fun _ : Fin b => 0) (fun _ : Fin a => 1) (by simp) (fun k i => M i k))) := by
  rw [negativeTwistPolynomialMap_eq_finiteCoproduct] at hf ⊢
  let L := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j 1
  let O := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j 0
  let eO : O ≅ Invertible.Scheme.Modules.unitObj
      (Proj (MvPolynomial.homogeneousSubmodule σ R)) :=
    TensorSections.monoidalUnitObjIso _
  exact TransposeTargetIso.epi_dualMap_transpose L O
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j 1)
    eO (fun i k =>
      (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
        (R := R) j 1 0 (by omega)).symm (M i k)) hf

end SteinerGeometry.NegativeLinearDualEpi
