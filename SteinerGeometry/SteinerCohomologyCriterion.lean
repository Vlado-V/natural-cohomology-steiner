module

public import SteinerGeometry.CohomologyRankForgetful
public import SteinerGeometry.PolynomialTopRank
public import SteinerGeometry.ProjectiveSteinerPresentation

set_option backward.privateInPublic true
@[expose] public section

/-! Natural cohomology of one fixed geometric Steiner cokernel from the
literal matrices of its negative presentations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 40000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.SteinerCohomologyCriterion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open ProjectiveSteinerBundle ProjectiveDualNormalization
open LaurentResidueHomology ProjectiveMatrixCohomology
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

def deepSourceIso {p t r : ℕ}
    (i : projectiveTwistSum R (p+1) t (-1) ⟶ projectiveTwistSum R (p+1) (t+r) 0)
    (m : ℕ) :
    (presentation i (degree (p+1) (m+1)+1)).X₁ ≅
      projectiveTwistSum R (p+1) t (degree (p+1) (m+1)) :=
  presentationSourceIso i _ ≪≫ eqToIso (by congr 1 <;> omega)

/-- The actual negative presentation, expressed in the canonical line sums. -/
def deepMap {p t r : ℕ}
    (i : projectiveTwistSum R (p+1) t (-1) ⟶ projectiveTwistSum R (p+1) (t+r) 0)
    (m : ℕ) :
    projectiveTwistSum R (p+1) t (degree (p+1) (m+1)) ⟶
      projectiveTwistSum R (p+1) (t+r) (degree (p+1) (m+1)+1) :=
  (deepSourceIso i m).inv ≫ (presentation i _).f ≫ (presentationTargetIso i _).hom

variable (hfield : IsField Γ(Spec (.of R),⊤))

/-- A formulation adapted to tensoring the original presentation: its
scalar in the canonical line frame is preserved in every negative twist. -/
theorem all_twists_natural_of_coefficients {p t r : ℕ}
    (i : projectiveTwistSum R (p+1) t (-1) ⟶ projectiveTwistSum R (p+1) (t+r) 0)
    [Epi (evaluation i)]
    (M : Fin t → Fin (t+r) →
      MvPolynomial.homogeneousSubmodule (Fin ((p+1)+1)) Γ(Spec (.of R),⊤) 1)
    (hM : letI : Field Γ(Spec (.of R),⊤) := SteinerGeometry.canonicalField hfield
      ∀ m, Steiner.LinearMatrixMaximalRank M m)
    (hcoef : ∀ m a b,
      ActualNegativeTopMap.chartCoefficient (R := R) (0 : Fin ((p+1)+1)) (0 : Fin ((p+1)+1))
        (degree (p+1) (m+1)) (PolynomialTopRank.lineComponent (deepMap i m) a b) =
      FrameMapCoefficient.coefficient (PolynomialTopRank.originalComponent i a b)
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (0 : Fin ((p+1)+1)))
        (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
          (R := R) (0 : Fin ((p+1)+1)) (0 : Fin ((p+1)+1)) 1)
        (NegativeTwistMaps.MvPolynomial.coordinateHyperplaneIdealModulePowerOverFrame
          (R := R) (0 : Fin ((p+1)+1)) (0 : Fin ((p+1)+1)) 0))
    (hpoly : ∀ a b,
      (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials
        (R := R) (0 : Fin ((p+1)+1)) 1 0 (by omega)
        (PolynomialTopRank.originalComponent i a b)).val = (M a b).val) :
    ∀ b : ℤ, SchemeModules.HasNaturalCohomology (twist (bundle i) b) := by
  apply ProjectiveSteinerPresentation.all_twists_natural (by omega) i
  intro b hb
  let m : ℕ := (-b - (p+2 : ℕ)).toNat
  have hm : (m : ℤ) = -b - (p+2 : ℕ) := by
    apply Int.toNat_of_nonneg
    omega
  have heq : b = degree (p+1) (m+1)+1 := by
    dsimp [degree]
    omega
  rw [heq]
  apply (CohomologyRankForgetful.coefficient_iff_zariski
    (ProjectiveTopNaturality.base (R := R) (p+1)).appTop.hom (p+1)
    (presentation i (degree (p+1) (m+1)+1)).f).1
  apply (topMap_maximalRank_conjugate_iff (R := R) p (deepSourceIso i m)
    (presentationTargetIso i _) (presentation i _).f).2
  refine PolynomialTopRank.maximalRank_of_originalEntries (R := R) hfield p m t (t+r)
    (deepMap i m) i M (hM m) ?_ ?_
  · exact hcoef m
  · exact hpoly

end SteinerGeometry.SteinerCohomologyCriterion
