module

public import SteinerGeometry.CanonicalField
public import SteinerGeometry.PolynomialMatrixEpi
public import SteinerGeometry.PolynomialPresentation
public import SteinerGeometry.ProjectiveDualNormalization
public import SteinerGeometry.NegativeLinearDualEpi

set_option backward.privateInPublic true
@[expose] public section

/-! The literal homogeneous matrix gives an epimorphic projective presentation. -/
noncomputable section
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.PolynomialMatrixSurjective
open CategoryTheory AlgebraicGeometry Steiner
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] SteinerGeometry.polynomialPresentationFiniteBiproducts
attribute [local instance] TwistPowers.MvPolynomial.instMonoidalCategoryModules_oAI


def linearMap {n a b : ℕ}
    (M : Fin a → Fin b → MvPolynomial.homogeneousSubmodule (Fin (n+1)) Γ(Spec (.of R), ⊤) 1) :=
  negativeTwistPolynomialMap (R := R) (0 : Fin (n+1))
    (fun _ : Fin a => 0) (fun _ : Fin b => 1) (by simp) M

/-- The actual transposed negative presentation defining the Steiner cokernel. -/
def literalPresentation {n t r : ℕ}
    (M : Fin t → Fin (t+r) →
      MvPolynomial.homogeneousSubmodule (Fin (n+1)) Γ(Spec (.of R), ⊤) 1) :
    projectiveTwistSum R n t (-1) ⟶ projectiveTwistSum R n (t+r) 0 :=
  linearMap (R := R) (fun j i => M i j)


theorem linearMap_epi [IsNoetherianRing R]
    (hfield : IsField Γ(Spec (.of R), ⊤))
    {n t r : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (M : Fin t → Fin (t+r) →
      MvPolynomial.homogeneousSubmodule (Fin (n+1)) Γ(Spec (.of R), ⊤) 1)
    (hM : letI := canonicalField hfield; ∀ d, LinearMatrixMaximalRank M d) :
    Epi (linearMap (R := R) M) := by
  have hs : ∀ N : ℕ, criticalCeil n t r ≤ N →
      ∀ y : weightedPolynomialPiece (R := R) (σ := Fin (n+1)) (fun _ : Fin t => 0) N,
        ∃ x : weightedPolynomialPiece (R := R) (σ := Fin (n+1)) (fun _ : Fin (t+r) => 1) N,
          ∀ i, y.val i = ∑ j, (M i j).val * x.val j := by
    letI := canonicalField hfield
    intro N hN
    exact PolynomialMatrixEpi.weighted_surjective_of_all_ranks
      (R := Γ(Spec (.of R), ⊤)) hn ht hr M hM N hN
  change Epi (negativeTwistPolynomialMap (R := R) (0 : Fin (n+1))
    (fun _ : Fin t => 0) (fun _ : Fin (t+r) => 1) (by simp) M)
  apply negativeTwistPolynomialMap_epi (R := R) (0 : Fin (n+1)) (fun _ : Fin t => 0)
    (fun _ : Fin (t+r) => 1) (by simp) M (criticalCeil n t r)
  · simp
  · intro _
    exact criticalCeil_pos hn ht hr
  · intro N hN
    exact hs N hN


/-- The dual evaluation of the literal transposed matrix is an epimorphism.
The proof transports the original polynomial epimorphism through invertible
tensor duality, so no fiberwise or geometric rank hypothesis is assumed. -/
theorem literalPresentation_evaluation_epi [IsNoetherianRing R]
    (hfield : IsField Γ(Spec (.of R), ⊤))
    {n t r : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (M : Fin t → Fin (t+r) →
      MvPolynomial.homogeneousSubmodule (Fin (n+1)) Γ(Spec (.of R), ⊤) 1)
    (hM : letI := canonicalField hfield; ∀ d, LinearMatrixMaximalRank M d) :
    Epi (ProjectiveDualNormalization.evaluation (literalPresentation (R := R) M)) := by
  have hd := NegativeLinearDualEpi.dual_transpose_epi (R := R) (0 : Fin (n+1)) M
    (linearMap_epi (R := R) hfield hn ht hr M hM)
  haveI : Epi (SheafDual.dualMap (literalPresentation (R := R) M)) := hd
  exact inferInstanceAs (Epi
    ((ProjectiveDualNormalization.zeroSumDualIso (R := R) n (t+r)).inv ≫
      SheafDual.dualMap (literalPresentation (R := R) M) ≫
      (ProjectiveDualNormalization.minusOneSumDualIso (R := R) n t).hom))


end SteinerGeometry.PolynomialMatrixSurjective
