module

public import SteinerGeometry.CurveMatrixWitness
public import SteinerGeometry.CyclicContractionVanishing
public import SteinerGeometry.CyclicComplexBase
public import SteinerGeometry.LineEpimorphismCover

set_option backward.privateInPublic true
@[expose] public section

/-! Actual cyclic-cover line vanishing supplies one maximal-rank Steiner matrix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.CyclicEtaleIsogeny

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Steiner
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

variable {D : EllipticScheme} {n : ℕ} [NeZero n]
    (q : CyclicEtaleIsogeny D n) [IsLocallyNoetherian q.target.scheme.left]

omit [NeZero n] [IsLocallyNoetherian q.target.scheme.left] in
/-- The presentation's actual dual evaluation is basepoint-free. -/
theorem presentation_components_cover
    (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n) :
    ∀ x : q.target.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing
      (DualEvaluation.componentSections P.relationLine P.inclusion i) := by
  let : Epi (DualEvaluation.evaluation P.relationLine P.inclusion) := P.evaluation_epi
  exact LineEpimorphismCover.components_cover (DualEvaluation.targetLine P.relationLine)
    (DualEvaluation.evaluation P.relationLine P.inclusion)

/-- If the actual line summands upstairs have natural cohomology in a common
degree, the resulting matrix has maximal-rank polynomial maps in all degrees.
The finite-flat trace and epimorphic dual evaluation are used internally. -/
theorem genericMatrixConclusion_of_monomial_line_vanishing
    {K : Type*} [Field K] [CharZero K] {t r : ℕ}
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (A : Line.Bundles.LineBundle D.scheme.left)
    (P : CurvePresentationData (q.linePushforward A) n)
    (B : Line.Bundles.LineBundle q.target.scheme.left)
    [FiniteDimensional ℂ ((sectionFunctor q.target.scheme.hom).obj B.sheaf)]
    [FiniteDimensional ℂ ((sectionFunctor q.target.scheme.hom).obj
      ((DualEvaluation.targetLine P.relationLine).tensor B).sheaf)]
    (hB : Module.finrank ℂ ((sectionFunctor q.target.scheme.hom).obj B.sheaf) = t)
    (hLB : Module.finrank ℂ ((sectionFunctor q.target.scheme.hom).obj
      ((DualEvaluation.targetLine P.relationLine).tensor B).sheaf) = t+r)
    (hv : ∀ d, (∀ a : Sym (Fin n) (d+1),
        IsZero (H D.scheme.hom (q.contractionMonomialLine A B a).sheaf 0)) ∨
      (∀ a : Sym (Fin n) (d+1),
        IsZero (H D.scheme.hom (q.contractionMonomialLine A B a).sheaf 1))) :
    GenericMatrixConclusion K n t r := by
  let : IsProper q.target.scheme.hom := q.target.proper
  let : q.target.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from q.target.scheme.hom]
    infer_instance⟩
  apply genericMatrixConclusion_of_curve_kernel_vanishing q.target.scheme.hom hn ht hr
    (DualEvaluation.targetLine P.relationLine) B
    (DualEvaluation.componentSections P.relationLine P.inclusion)
    (q.presentation_components_cover A P) hB hLB
  intro d
  rcases hv d with h0 | h1
  · left
    apply q.contractionKernel_cohomology_zero q.target.scheme.hom A P B d 0
    intro a
    simpa only [q.map.hom.w] using h0 a
  · right
    apply q.contractionKernel_cohomology_zero q.target.scheme.hom A P B d 1
    intro a
    simpa only [q.map.hom.w] using h1 a

end SteinerGeometry.CyclicEtaleIsogeny
