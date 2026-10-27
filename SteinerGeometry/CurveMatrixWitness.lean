import SteinerGeometry.OperatorCohomology
import Steiner.SectionMultiplication
import Steiner.ScalarExtension

/-! The final linear-algebra interface of the elliptic-curve construction.
The hypotheses concern actual line bundles, their sections, and their
cohomology; no matrix-rank assertion is assumed. -/

noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Steiner
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

theorem exists_linearMatrix_of_curve_kernel_vanishing
    {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) {n t r : ℕ}
    (L B : Line.Bundles.LineBundle X)
    (s : Fin (n+1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    [FiniteDimensional ℂ ((sectionFunctor p).obj B.sheaf)]
    [FiniteDimensional ℂ ((sectionFunctor p).obj (L.tensor B).sheaf)]
    (hB : Module.finrank ℂ ((sectionFunctor p).obj B.sheaf) = t)
    (hLB : Module.finrank ℂ ((sectionFunctor p).obj (L.tensor B).sheaf) = t+r)
    (hv : ∀ d, IsZero (H p (curveContractionKernel L B s d) 0) ∨
      IsZero (H p (curveContractionKernel L B s d) 1)) :
    ∃ M : LinearMatrix ℂ n t (t+r), ∀ d, LinearMatrixMaximalRank M d := by
  let bB := Module.finBasisOfFinrankEq ℂ ((sectionFunctor p).obj B.sheaf) hB
  let bLB := Module.finBasisOfFinrankEq ℂ ((sectionFunctor p).obj (L.tensor B).sheaf) hLB
  apply exists_sectionMultiplication_matrix bB bLB
    (fun i => ((sectionFunctor p).map
      (LineBundle.SectionMultiplication.lineBundleSectionMultiply L B (s i))).hom)
  intro d
  rcases hv d with h0 | h1
  · exact Or.inl (curve_operatorDifferential_injective_of_h0 p L B s d h0)
  · exact Or.inr (curve_operatorDifferential_surjective_of_h1 p L B s hs d h1)

theorem genericMatrixConclusion_of_curve_kernel_vanishing
    {K : Type*} [Field K] [CharZero K]
    {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) {n t r : ℕ}
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (L B : Line.Bundles.LineBundle X)
    (s : Fin (n+1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    [FiniteDimensional ℂ ((sectionFunctor p).obj B.sheaf)]
    [FiniteDimensional ℂ ((sectionFunctor p).obj (L.tensor B).sheaf)]
    (hB : Module.finrank ℂ ((sectionFunctor p).obj B.sheaf) = t)
    (hLB : Module.finrank ℂ ((sectionFunctor p).obj (L.tensor B).sheaf) = t+r)
    (hv : ∀ d, IsZero (H p (curveContractionKernel L B s d) 0) ∨
      IsZero (H p (curveContractionKernel L B s d) 1)) :
    GenericMatrixConclusion K n t r := by
  obtain ⟨M, hM⟩ := exists_linearMatrix_of_curve_kernel_vanishing p L B s hs hB hLB hv
  exact genericMatrixConclusion_of_rational_extension hn ht hr M hM

end SteinerGeometry
