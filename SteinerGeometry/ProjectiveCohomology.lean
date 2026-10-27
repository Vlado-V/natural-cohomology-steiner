import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentDimensions
import Mathlib.Algebra.Category.ModuleCat.Products
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.BaseCechCoefficientCohomology

/-! Cohomology of the actual coordinate hyperplane twists on projective space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry
open SheafCohomology.Projective

namespace SteinerGeometry

universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Polynomial projective space, with its actual structure sheaf. -/
abbrev projectiveSpace (R : Type u) [CommRing R] (n : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)

/-- The actual invertible sheaf `O(d)`, normalized at the zeroth coordinate. -/
abbrev projectiveTwist (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    (projectiveSpace R n).Modules :=
  TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) d

/-- Genuine sheaf cohomology, with scalars in the function ring of the affine base. -/
abbrev projectiveTwistCohomology (R : Type u) [CommRing R]
    (n : ℕ) (d : ℤ) (q : ℕ) :=
  ((AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1))).appTop.hom q).obj
      (projectiveTwist R n d))

/-- The Laurent calculation is identified with genuine sheaf cohomology in every degree. -/
def projectiveTwistLaurentEquiv (n : ℕ) (d : ℤ) (q : ℕ) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) (0 : Fin (n + 1)) d).homology q ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      projectiveTwistCohomology R n d q := by
  letI : (projectiveTwist R n d).IsQuasicoherent :=
    InvertibleFinitePresentation.invertible_quasicoherent
      (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible
        (R := R) (0 : Fin (n + 1)) d)
  let e := TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso
      (R := R) (0 : Fin (n + 1)) d ≪≫
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso
      (R := R) (0 : Fin (n + 1)) d
  exact (HomologicalComplex.homologyMapIso e q).toLinearEquiv.symm.trans
    (AbelianModuli.HilbertConstruction.Ordered.BaseCechCoefficientCohomology.orderedBaseCechCoefficientCohomologyLinearEquiv
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)))
      (projectiveTwist R n d)
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 1)))
      (IsOpenCover.mk (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R)))
      (StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) q)

/-- A negative twist has no global sections on positive-dimensional projective space. -/
theorem projectiveTwistCohomology_zero_of_neg (n : ℕ) (hn : 0 < n)
    (d : ℤ) (hd : d < 0) : Subsingleton (projectiveTwistCohomology R n d 0) := by
  letI : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  letI := LaurentZeroNegative.MvPolynomial.homogeneousLaurentHZero_subsingleton_of_neg
    (R := R) (0 : Fin (n + 1)) d hd
  exact (projectiveTwistLaurentEquiv (R := R) n d 0).symm.injective.subsingleton

/-- There is no intermediate cohomology for a line bundle twist on projective space; the only
possible positive degree is the dimension of projective space. -/
theorem projectiveTwistCohomology_positive_off_top (n : ℕ) (d : ℤ) (q : ℕ)
    (hq : 0 < q) (hqn : q ≠ n) :
    Subsingleton (projectiveTwistCohomology R n d q) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hq)
  letI := NegativeLaurentVanishing.MvPolynomial.coordinateHomogeneousLaurentPositiveHomology_subsingleton_of_card_ne
    (R := R) (0 : Fin (n + 1)) d i (by simp only [Fintype.card_fin]; omega)
  exact (projectiveTwistLaurentEquiv (R := R) n d (i + 1)).symm.injective.subsingleton

/-- In degree greater than `-n-1`, every positive cohomology group vanishes. -/
theorem projectiveTwistCohomology_positive_of_degree_gt (n : ℕ) (d : ℤ)
    (hd : -(n + 1 : ℤ) < d) (q : ℕ) (hq : 0 < q) :
    Subsingleton (projectiveTwistCohomology R n d q) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hq)
  letI := LaurentDimensions.MvPolynomial.coordinateHomogeneousLaurentPositiveHomology_subsingleton_of_degree_gt
    (R := R) (0 : Fin (n + 1)) d i (by simpa using hd)
  exact (projectiveTwistLaurentEquiv (R := R) n d (i + 1)).symm.injective.subsingleton

/-- Nonnegative twists have cohomology only in degree zero. -/
theorem projectiveTwistCohomology_positive_of_nonnegative (n : ℕ) (d : ℤ)
    (hd : 0 ≤ d) (q : ℕ) (hq : 0 < q) :
    Subsingleton (projectiveTwistCohomology R n d q) :=
  projectiveTwistCohomology_positive_of_degree_gt n d (by omega) q hq

/-- Line bundles have natural cohomology on projective space. -/
theorem projectiveTwist_naturalCohomology (n : ℕ) (hn : 0 < n) (d : ℤ) :
    ∃ q : ℕ, ∀ i : ℕ, i ≠ q → Subsingleton (projectiveTwistCohomology R n d i) := by
  by_cases hd : 0 ≤ d
  · refine ⟨0, fun i hi => projectiveTwistCohomology_positive_of_nonnegative n d hd i ?_⟩
    omega
  · refine ⟨n, ?_⟩
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      exact projectiveTwistCohomology_zero_of_neg n hn d (by omega)
    · exact projectiveTwistCohomology_positive_off_top n d i (by omega) hi

/-- Finite direct sums of line twists, as actual module sheaves. -/
abbrev projectiveTwistSum (R : Type u) [CommRing R] (n r : ℕ) (d : ℤ) :=
  ∐ fun _ : Fin r => projectiveTwist R n d

abbrev projectiveTwistSumCohomology (R : Type u) [CommRing R]
    (n r : ℕ) (d : ℤ) (q : ℕ) :=
  ((AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1))).appTop.hom q).obj
      (projectiveTwistSum R n r d))

/-- Sheaf cohomology commutes with these finite direct sums. -/
def projectiveTwistSumCohomologyEquiv (n r : ℕ) (d : ℤ) (q : ℕ) :
    projectiveTwistSumCohomology R n r d q ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      (Fin r → projectiveTwistCohomology R n d q) := by
  let F := AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1))).appTop.hom q
  let M := fun _ : Fin r => projectiveTwist R n d
  letI : F.Additive := by
    dsimp [F, AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor]
    infer_instance
  letI : Limits.HasFiniteBiproducts (projectiveSpace R n).Modules :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  letI : Limits.HasFiniteBiproducts (ModuleCat Γ(Spec (CommRingCat.of R), ⊤)) :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  letI : Limits.PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  exact ((F.mapIso (Limits.biproduct.isoCoproduct M).symm) ≪≫ F.mapBiproduct M ≪≫
    Limits.biproduct.isoProduct (F.obj ∘ M) ≪≫ ModuleCat.piIsoPi (F.obj ∘ M)).toLinearEquiv

/-- Vanishing of a twist passes to every finite direct sum of that twist. -/
theorem projectiveTwistSumCohomology_subsingleton (n r : ℕ) (d : ℤ) (q : ℕ)
    (h : Subsingleton (projectiveTwistCohomology R n d q)) :
    Subsingleton (projectiveTwistSumCohomology R n r d q) := by
  letI := h
  exact (projectiveTwistSumCohomologyEquiv (R := R) n r d q).injective.subsingleton

/-- Finite sums of nonnegative twists have no positive cohomology. -/
theorem projectiveTwistSumCohomology_positive_of_nonnegative (n r : ℕ) (d : ℤ)
    (hd : 0 ≤ d) (q : ℕ) (hq : 0 < q) :
    Subsingleton (projectiveTwistSumCohomology R n r d q) :=
  projectiveTwistSumCohomology_subsingleton n r d q
    (projectiveTwistCohomology_positive_of_nonnegative n d hd q hq)

/-- Finite sums of negative twists have cohomology only in top degree. -/
theorem projectiveTwistSumCohomology_negative_off_top (n r : ℕ) (hn : 0 < n)
    (d : ℤ) (hd : d < 0) (q : ℕ) (hqn : q ≠ n) :
    Subsingleton (projectiveTwistSumCohomology R n r d q) := by
  apply projectiveTwistSumCohomology_subsingleton n r d q
  by_cases hq : q = 0
  · subst q
    exact projectiveTwistCohomology_zero_of_neg n hn d hd
  · exact projectiveTwistCohomology_positive_off_top n d q (by omega) hqn

end SteinerGeometry
