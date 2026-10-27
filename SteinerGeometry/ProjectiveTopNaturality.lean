import SteinerGeometry.ProjectiveCohomology
import SteinerGeometry.OrderedCechNaturality
import SteinerGeometry.LaurentResidueHomology
import SteinerGeometry.ActualNegativeTopMap

/-! Residue coordinates natural for the actual maps of projective sheaves. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.ProjectiveTopNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry
open SheafCohomology.Projective
open LaurentCochainMap LaurentResidueHomology
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev base (n : ℕ) := MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+1))
abbrev cover (n : ℕ) := StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+1))

def twistLaurentIso (n : ℕ) (d : ℤ) :
    OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (base (R := R) n)
      (projectiveTwist R n d) (cover (R := R) n) ≅
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) (0 : Fin (n+1)) d :=
  ActualNegativeTopMap.comparison (R := R) (0 : Fin (n+1)) d

/-- The Laurent map here is transported from the literal morphism of sheaves. -/
def actualLaurentMap (n : ℕ) (d e : ℤ)
    (f : projectiveTwist R n d ⟶ projectiveTwist R n e) :=
  (twistLaurentIso (R := R) n d).inv ≫
    (OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
      (base (R := R) n) (cover (R := R) n)).map f ≫
    (twistLaurentIso (R := R) n e).hom

/-- Both calculations use precisely the same transported actual map. -/
theorem actualLaurentMap_succ (n : ℕ) (d : ℤ)
    (f : projectiveTwist R n d ⟶ projectiveTwist R n (d+1)) :
    actualLaurentMap n d (d+1) f =
      ActualNegativeTopMap.actualMap (R := R) (0 : Fin (n+1)) d f := rfl

/-- Actual top sheaf cohomology, coordinatized by complementary Laurent residues. -/
def topResidueIso (p m : ℕ) (d : ℤ) (hd : d = degree (p+1) m) :
    projectiveTwistCohomology R (p+1) d (p+1) ≅
      ModuleCat.of Γ(Spec (.of R),⊤)
        (ProjectiveResiduePairing.ResidueCoefficients (Fin (p+2)) Γ(Spec (.of R),⊤) m) := by
  letI : (projectiveTwist R (p+1) d).IsQuasicoherent :=
    InvertibleFinitePresentation.invertible_quasicoherent
      (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (p+2)) d)
  exact (OrderedCechNaturality.positiveIso (base (R := R) (p+1)) (cover (R := R) (p+1))
    (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R))
    (StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    (projectiveTwist R (p+1) d) p).symm ≪≫
    HomologicalComplex.homologyMapIso (twistLaurentIso (R := R) (p+1) d) (p+1) ≪≫
    (homologyResidueEquivAt (R := R) p m (0 : Fin (p+2)) d hd).toModuleIso

/-- A full-index cochain equality is sufficient: the actual map on top
sheaf cohomology is the transpose residue multiplication map. -/
theorem topResidueIso_naturality (p m : ℕ) (d : ℤ)
    (hs : d = degree (p+1) (m+1)) (ht : d+1 = degree (p+1) m)
    (f : projectiveTwist R (p+1) d ⟶ projectiveTwist R (p+1) (d+1))
    (L : Fin (p+2) → Γ(Spec (.of R),⊤))
    (hfull : (actualLaurentMap (p+1) d (d+1) f).f (p+1) ≫
        projection (d+1) (p+1) (LaurentMultiplication.fullIndex (p+1)) =
      (linearFormMap (0 : Fin (p+2)) d L).f (p+1) ≫
        projection (d+1) (p+1) (LaurentMultiplication.fullIndex (p+1))) :
    (AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (base (R := R) (p+1)).appTop.hom (p+1)).map f ≫
        (topResidueIso (R := R) p m (d+1) ht).hom =
      (topResidueIso (R := R) p (m+1) d hs).hom ≫
        ModuleCat.ofHom (ProjectiveResiduePairing.multiplyResidueLinearForm m L) := by
  let g := actualLaurentMap (p+1) d (d+1) f
  have hp : g.f (p+1) ≫ ModuleCat.ofHom
      (topResidueProjection (R := R) (p+1) m (d+1) ht) =
    ModuleCat.ofHom (topResidueProjection (R := R) (p+1) (m+1) d hs) ≫
      ModuleCat.ofHom (ProjectiveResiduePairing.multiplyResidueLinearForm m L) := by
    have hfull' := congrArg (fun k => k ≫ ModuleCat.ofHom
      (LaurentResidueShift.residueProjection (R := R) (fun i : Fin (p+2) => i)
        (fun i => ⟨i,rfl⟩) m (d+1) (by simpa only [Fintype.card_fin] using ht))) hfull
    have hlin : (linearFormMap (R := R) (0 : Fin (p+2)) d L).f (p+1) ≫
        ModuleCat.ofHom (topResidueProjection (R := R) (p+1) m (d+1) ht) =
      ModuleCat.ofHom (topResidueProjection (R := R) (p+1) (m+1) d hs) ≫
        ModuleCat.ofHom (ProjectiveResiduePairing.multiplyResidueLinearForm m L) := by
      apply ModuleCat.hom_ext
      exact linearFormMap_topResidue (p+1) m (0 : Fin (p+2)) d hs ht L
    exact (show g.f (p+1) ≫ ModuleCat.ofHom
      (topResidueProjection (R := R) (p+1) m (d+1) ht) =
        (linearFormMap (R := R) (0 : Fin (p+2)) d L).f (p+1) ≫ ModuleCat.ofHom
          (topResidueProjection (R := R) (p+1) m (d+1) ht) from by
            simpa only [g, topResidueProjection, ModuleCat.ofHom_comp,
              ModuleCat.ofHom_hom, Category.assoc] using hfull').trans hlin
  have hg := LaurentTopNaturality.homologyProjection_naturality g (p+1) _ _ _ _
    (homologyResidueEquivAt_homologyπ p (m+1) (0 : Fin (p+2)) d hs)
    (homologyResidueEquivAt_homologyπ p m (0 : Fin (p+2)) (d+1) ht) _ hp
  letI : (projectiveTwist R (p+1) d).IsQuasicoherent :=
    InvertibleFinitePresentation.invertible_quasicoherent
      (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (p+2)) d)
  letI : (projectiveTwist R (p+1) (d+1)).IsQuasicoherent :=
    InvertibleFinitePresentation.invertible_quasicoherent
      (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (p+2)) (d+1))
  have hn := OrderedCechNaturality.positiveIso_naturality (base (R := R) (p+1))
    (cover (R := R) (p+1))
    (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R))
    (StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) f p
  apply (cancel_epi (OrderedCechNaturality.positiveIso (base (R := R) (p+1))
    (cover (R := R) (p+1))
    (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R))
    (StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R))
    (projectiveTwist R (p+1) d) p).hom).1
  simp only [topResidueIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hg' := congrArg (fun k => HomologicalComplex.homologyMap
    (twistLaurentIso (R := R) (p+1) d).hom (p+1) ≫ k) hg
  have hc : HomologicalComplex.homologyMap (twistLaurentIso (R := R) (p+1) d).hom (p+1) ≫
      HomologicalComplex.homologyMap (twistLaurentIso (R := R) (p+1) d).inv (p+1) = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id,
      HomologicalComplex.homologyMap_id]
  simpa only [g, actualLaurentMap, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMapIso_hom, ← Category.assoc, hc,
    Category.id_comp] using hg'

end SteinerGeometry.ProjectiveTopNaturality
