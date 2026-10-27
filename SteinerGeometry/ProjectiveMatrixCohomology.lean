import SteinerGeometry.ProjectiveTopNaturality
import SteinerGeometry.CohomologyMatrix
import SteinerGeometry.ResidueMatrixRank

/-! The actual top cohomology map of a projective matrix, with every
component identified through the Čech residue calculation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.ProjectiveMatrixCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry
open SheafCohomology.Projective
open ProjectiveTopNaturality LaurentCochainMap LaurentResidueHomology
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev topFunctor (p : ℕ) :=
  AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (base (R := R) (p+1)).appTop.hom (p+1)

local instance (p : ℕ) : (topFunctor (R := R) p).Additive := by
  dsimp [topFunctor, AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor]
  infer_instance

local instance projectiveFiniteBiproducts (n : ℕ) : HasFiniteBiproducts (projectiveSpace R n).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

def sumTopResidueEquiv (p m a : ℕ) (d : ℤ) (hd : d = degree (p+1) m) :
    projectiveTwistSumCohomology R (p+1) a d (p+1) ≃ₗ[Γ(Spec (.of R),⊤)]
      (Fin a → ProjectiveResiduePairing.ResidueCoefficients (Fin (p+2)) Γ(Spec (.of R),⊤) m) :=
  CohomologyMatrix.sumCoordinates (topFunctor (R := R) p)
    (fun _ : Fin a => projectiveTwist R (p+1) d)
    (fun _ => (topResidueIso (R := R) p m d hd).toLinearEquiv)

/-- Once the entrywise actual top-factor formula is proved, the whole
finite matrix acts by its literal transpose on residue coefficients. -/
theorem sumTopResidueEquiv_map (p m a b : ℕ) (d : ℤ)
    (hs : d = degree (p+1) (m+1)) (ht : d+1 = degree (p+1) m)
    (f : projectiveTwistSum R (p+1) a d ⟶ projectiveTwistSum R (p+1) b (d+1))
    (L : Fin a → Fin b → Fin (p+2) → Γ(Spec (.of R),⊤))
    (hfull : ∀ i j, (actualLaurentMap (p+1) d (d+1)
      (Sigma.ι (fun _ : Fin a => projectiveTwist R (p+1) d) i ≫ f ≫
        CoproductMatrixComponents.finiteCoproductProjection
          (fun _ : Fin b => projectiveTwist R (p+1) (d+1)) j)).f (p+1) ≫
          projection (d+1) (p+1) (LaurentMultiplication.fullIndex (p+1)) =
      (linearFormMap (0 : Fin (p+2)) d (L i j)).f (p+1) ≫
        projection (d+1) (p+1) (LaurentMultiplication.fullIndex (p+1)))
    (x : projectiveTwistSumCohomology R (p+1) a d (p+1)) :
    sumTopResidueEquiv p m b (d+1) ht ((topFunctor (R := R) p).map f x) =
      (CohomologyMatrix.matrixLinearMap
        (fun j i => ProjectiveResiduePairing.multiplyResidueLinearForm m (L i j)))
          (sumTopResidueEquiv p (m+1) a d hs x) := by
  apply CohomologyMatrix.sumCoordinates_map
  intro i j y
  exact ConcreteCategory.congr_hom
    (topResidueIso_naturality p m d hs ht _ (L i j) (hfull i j)) y

/-- Maximal rank of the positive polynomial matrix implies maximal rank
of the induced top map of these actual negative line bundles. -/
theorem topMap_maximalRank (hfield : IsField Γ(Spec (.of R),⊤))
    (p m a b : ℕ) (d : ℤ)
    (hs : d = degree (p+1) (m+1)) (ht : d+1 = degree (p+1) m)
    (f : projectiveTwistSum R (p+1) a d ⟶ projectiveTwistSum R (p+1) b (d+1))
    (L : Fin a → Fin b → Fin (p+2) → Γ(Spec (.of R),⊤))
    (hfull : ∀ i j, (actualLaurentMap (p+1) d (d+1)
      (Sigma.ι (fun _ : Fin a => projectiveTwist R (p+1) d) i ≫ f ≫
        CoproductMatrixComponents.finiteCoproductProjection
          (fun _ : Fin b => projectiveTwist R (p+1) (d+1)) j)).f (p+1) ≫
          projection (d+1) (p+1) (LaurentMultiplication.fullIndex (p+1)) =
      (linearFormMap (0 : Fin (p+2)) d (L i j)).f (p+1) ≫
        projection (d+1) (p+1) (LaurentMultiplication.fullIndex (p+1)))
    (hmax : letI : Field Γ(Spec (.of R),⊤) := hfield.toField
      HasMaximalRank (ResidueMatrixRank.polynomialMatrixMap m L)) :
    HasMaximalRank ((topFunctor (R := R) p).map f) := by
  letI : Field Γ(Spec (.of R),⊤) := hfield.toField
  have hr := (ResidueMatrixRank.residueMatrixMap_maximalRank_iff m L).2 hmax
  have he := hasMaximalRank_congr
    (sumTopResidueEquiv p (m+1) a d hs).toEquiv
    (sumTopResidueEquiv p m b (d+1) ht).toEquiv
    ((topFunctor (R := R) p).map f)
    (ResidueMatrixRank.residueMatrixMap m L)
    (sumTopResidueEquiv_map p m a b d hs ht f L hfull)
  exact he.2 hr

/-- The rank statement refers to the actual map, and is unchanged by
the two canonical line-sum identifications in a twisted presentation. -/
theorem topMap_maximalRank_conjugate_iff (p : ℕ)
    {A B A' B' : (projectiveSpace R (p+1)).Modules}
    (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) :
    HasMaximalRank ((topFunctor (R := R) p).map f) ↔
      HasMaximalRank ((topFunctor (R := R) p).map (eA.inv ≫ f ≫ eB.hom)) := by
  let F := topFunctor (R := R) p
  apply hasMaximalRank_congr (F.mapIso eA).toLinearEquiv.toEquiv
    (F.mapIso eB).toLinearEquiv.toEquiv
  intro x
  change (F.map f ≫ F.map eB.hom) x =
    (F.map eA.hom ≫ F.map (eA.inv ≫ f ≫ eB.hom)) x
  simp only [← F.map_comp, Iso.hom_inv_id_assoc]

end SteinerGeometry.ProjectiveMatrixCohomology
