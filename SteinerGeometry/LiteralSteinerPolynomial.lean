module

public import SteinerGeometry.PolynomialMatrixSurjective
public import SteinerGeometry.PolynomialTopRank

set_option backward.privateInPublic true
@[expose] public section

/-! The literal sheaf presentation has the supplied polynomial entries. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 40000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.LiteralSteinerPolynomial
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem originalComponent_polynomial {n t r : ℕ}
    (M : Fin t → Fin (t+r) →
      MvPolynomial.homogeneousSubmodule (Fin (n+1)) Γ(Spec (.of R),⊤) 1)
    (i : Fin t) (j : Fin (t+r)) :
    (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
      (R := R) (0 : Fin (n+1)) 1 0 (by omega)
      (PolynomialTopRank.originalComponent (PolynomialMatrixSurjective.literalPresentation (R := R) M) i j)).val =
        (M i j).val := by
  let e := NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
    (R := R) (0 : Fin (n+1)) 1 0 (by omega)
  have hc : PolynomialTopRank.originalComponent
      (PolynomialMatrixSurjective.literalPresentation (R := R) M) i j =
      e.symm (M i j) := by
    unfold PolynomialTopRank.originalComponent PolynomialTopRank.lineComponent
      PolynomialMatrixSurjective.literalPresentation PolynomialMatrixSurjective.linearMap
    exact negativeTwistPolynomialMap_component (R := R) (0 : Fin (n+1))
      (fun _ : Fin (t+r) => 0) (fun _ : Fin t => 1) (by simp)
      (fun j i => M i j) i j
  rw [hc]
  change (e (e.symm (M i j))).val = (M i j).val
  exact congrArg Subtype.val (e.apply_symm_apply (M i j))

end SteinerGeometry.LiteralSteinerPolynomial
