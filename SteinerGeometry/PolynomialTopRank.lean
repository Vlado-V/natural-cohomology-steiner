module

public import SteinerGeometry.CanonicalField
public import SteinerGeometry.ActualNegativeTopMap
public import SteinerGeometry.ProjectiveMatrixCohomology
public import SteinerGeometry.SteinerMatrixResidue

set_option backward.privateInPublic true
@[expose] public section

/-! Literal polynomial entries determine the genuine map on top cohomology. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.PolynomialTopRank
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open LaurentCochainMap LaurentResidueHomology ProjectiveTopNaturality
open ProjectiveMatrixCohomology
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance polynomialTopBiproducts (n : ℕ) : HasFiniteBiproducts (projectiveSpace R n).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

def lineComponent {n a b : ℕ} {d e : ℤ}
    (f : projectiveTwistSum R n a d ⟶ projectiveTwistSum R n b e)
    (i : Fin a) (j : Fin b) : projectiveTwist R n d ⟶ projectiveTwist R n e :=
  Sigma.ι (fun _ : Fin a => projectiveTwist R n d) i ≫ f ≫
    CoproductMatrixComponents.finiteCoproductProjection
      (fun _ : Fin b => projectiveTwist R n e) j

def originalComponent {n a b : ℕ}
    (i₀ : projectiveTwistSum R n a (-1) ⟶ projectiveTwistSum R n b 0)
    (i : Fin a) (j : Fin b) :
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (0 : Fin (n+1)) 1 ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (0 : Fin (n+1)) 0 :=
  lineComponent i₀ i j

variable (hfield : IsField Γ(Spec (.of R),⊤))

/-- It suffices to preserve the actual scalar in the distinguished frame
when tensoring the original linear presentation. -/
theorem maximalRank_of_originalEntries (p m a b : ℕ)
    (f : projectiveTwistSum R (p+1) a (degree (p+1) (m+1)) ⟶
      projectiveTwistSum R (p+1) b (degree (p+1) (m+1)+1))
    (i₀ : projectiveTwistSum R (p+1) a (-1) ⟶ projectiveTwistSum R (p+1) b 0)
    (M : Fin a → Fin b →
      MvPolynomial.homogeneousSubmodule (Fin ((p+1)+1)) Γ(Spec (.of R),⊤) 1)
    (hM : letI : Field Γ(Spec (.of R),⊤) := SteinerGeometry.canonicalField hfield
      Steiner.LinearMatrixMaximalRank M m)
    (hcoef : ∀ i j,
      ActualNegativeTopMap.chartCoefficient (R := R) (0 : Fin ((p+1)+1)) (0 : Fin ((p+1)+1))
        (degree (p+1) (m+1)) (lineComponent f i j) =
      FrameMapCoefficient.coefficient (originalComponent i₀ i j)
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (0 : Fin ((p+1)+1)))
        (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
          (R := R) (0 : Fin ((p+1)+1)) (0 : Fin ((p+1)+1)) 1)
        (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
          (R := R) (0 : Fin ((p+1)+1)) (0 : Fin ((p+1)+1)) 0))
    (hpoly : ∀ i j,
      (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
        (R := R) (0 : Fin ((p+1)+1)) 1 0 (by omega) (originalComponent i₀ i j)).val =
          (M i j).val) :
    HasMaximalRank ((topFunctor (R := R) p).map f) := by
  let L : Fin a → Fin b → Fin ((p+1)+1) → Γ(Spec (.of R),⊤) :=
    fun i j k => (M i j).val.coeff (Finsupp.single k 1)
  apply topMap_maximalRank (R := R) hfield p m a b
    (degree (p+1) (m+1)) rfl (by simp [degree]; omega) f L
  · intro i j
    have hp : (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
        (R := R) (0 : Fin ((p+1)+1)) 1 0 (by omega) (originalComponent i₀ i j)).val =
        LaurentChartMultiplication.linearPolynomial (L i j) := by
      letI : Field Γ(Spec (.of R),⊤) := SteinerGeometry.canonicalField hfield
      exact (hpoly i j).trans (SteinerMatrixResidue.linearForm_eq_coefficients (M i j))
    have hf := ActualNegativeTopMap.actual_top_projection_of_linear_coefficient (R := R) (p+1)
      (degree (p+1) (m+1)) (lineComponent f i j) (originalComponent i₀ i j)
      (L i j) (by
        have hc := hcoef i j
        exact hc) hp
    have he := congrArg (fun g => g.f (p+1) ≫
      projection (degree (p+1) (m+1)+1) (p+1) (LaurentMultiplication.fullIndex (p+1)))
      (actualLaurentMap_succ (R := R) (p+1) (degree (p+1) (m+1)) (lineComponent f i j))
    exact he.trans hf
  · letI : Field Γ(Spec (.of R),⊤) := SteinerGeometry.canonicalField hfield
    exact (SteinerMatrixResidue.polynomialMatrixMap_maximalRank_iff M m).2 hM

end SteinerGeometry.PolynomialTopRank
