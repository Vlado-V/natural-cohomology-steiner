module

public import SteinerGeometry.LaurentTopNaturality
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop

set_option backward.privateInPublic true
@[expose] public section

/-! # Naturality of the actual full-negative Laurent cohomology coordinates -/
noncomputable section
namespace SteinerGeometry.NegativeLaurentNaturality

open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective

universe u
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]

/-- An actual cochain map whose full-negative coefficient projection is `g`
induces exactly `g` on the projected positive cohomology. -/
theorem fullNegativeHomologyProjection_naturality
    {j j' : σ} {d d' : ℤ} (n : ℕ)
    (f : TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d ⟶
      TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j' d')
    (g : ModuleCat.of Γ(Spec (.of R), ⊤)
      (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u,u}
        (R := R) (σ := σ) d (n + 1)) ⟶
      ModuleCat.of Γ(Spec (.of R), ⊤)
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u,u}
          (R := R) (σ := σ) d' (n + 1)))
    (hfg : f.f (n + 1) ≫ ModuleCat.ofHom
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
          (R := R) (σ := σ) d' (n + 1)) =
      ModuleCat.ofHom
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
          (R := R) (σ := σ) d (n + 1)) ≫ g) :
    HomologicalComplex.homologyMap f (n + 1) ≫
        NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection
          (R := R) j' d' n =
      NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection
        (R := R) j d n ≫ g := by
  exact LaurentTopNaturality.homologyProjection_naturality f (n + 1) _ _ _ _
    (NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection_homologyπ
      (R := R) j d n)
    (NegativeLaurentHomology.MvPolynomial.coordinateFullNegativeHomologyProjection_homologyπ
      (R := R) j' d' n) g hfg

end SteinerGeometry.NegativeLaurentNaturality
