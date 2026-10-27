module

public import SteinerGeometry.SheafBidual
public import SteinerGeometry.ProjectiveKernelBundle

set_option backward.privateInPublic true
@[expose] public section

/-! Canonical biduality for finite sums of projective line bundle twists. -/

noncomputable section
namespace SteinerGeometry.ProjectiveBidual
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open ProjectiveKernelBundle
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem lineSum_bidualEvaluation_isIso (n r : ℕ) (j : Fin (n+1))
    (d : Fin r → ℤ) : IsIso (SheafDual.bidualEvaluation (lineSum R n r j d)) :=
  SheafDual.bidualEvaluation_isIso_of_restrict_free_cover (lineSum R n r j d)
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+1)))
    (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R))
    (fun _ => ULift.{u} (Fin r)) (fun _ => inferInstance)
    (fun a => lineSumRestrictionFrame (R := R) n r a.down j d)

/-- The isomorphism is the natural section-evaluation map into the bidual. -/
def lineSumBidualIso (n r : ℕ) (j : Fin (n+1)) (d : Fin r → ℤ) :
    lineSum R n r j d ≅ SheafDual.dual (SheafDual.dual (lineSum R n r j d)) := by
  have := lineSum_bidualEvaluation_isIso (R := R) n r j d
  exact asIso (SheafDual.bidualEvaluation (lineSum R n r j d))

@[simp]
theorem lineSumBidualIso_hom (n r : ℕ) (j : Fin (n+1)) (d : Fin r → ℤ) :
    (lineSumBidualIso (R := R) n r j d).hom =
      SheafDual.bidualEvaluation (lineSum R n r j d) := rfl

end SteinerGeometry.ProjectiveBidual
