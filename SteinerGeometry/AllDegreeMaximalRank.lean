module

public import SteinerGeometry.EllipticMatrixConstruction
public import SteinerGeometry.RectangularWitness
public import SteinerGeometry.RectangularGenusOne
public import SteinerGeometry.RectangularTorsion
public import Steiner.RationalBoundary

set_option backward.privateInPublic true
@[expose] public section

/-! The all-parameter maximal-rank theorem. The elliptic data are constructed
internally; the boundary uses the explicit rational Toeplitz matrix. -/
noncomputable section
namespace Steiner
open CategoryTheory AlgebraicGeometry SteinerGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open SteinerGeometry.EllipticCohomology

theorem genericMatrixConclusion_charZero
    (K : Type*) [Field K] [CharZero K] (n t r : ℕ)
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : n ≤ r) :
    GenericMatrixConclusion K n t r := by
  by_cases hboundary : r = n
  · subst r
    obtain ⟨M, hM⟩ := exists_rationalBoundary_maximalRank (K := K) n t (by omega)
    exact genericMatrixConclusion_of_extension_witness (RingHom.id K) hn ht hn M hM
  · have hr' : n < r := by omega
    let : NeZero n := ⟨by omega⟩
    obtain ⟨C, D, q, hq⟩ := exists_rectangularCyclicData n
    let : IsIntegral q.target.scheme.left := by rw [hq]; infer_instance
    let : IsNoetherian q.target.scheme.left := by rw [hq]; infer_instance
    let : CurveCohomologyFinite q.target.scheme.hom := by rw [hq]; infer_instance
    let : Infinite (TorsionLineClasses.TorsionClass q.target.scheme.left) := by
      rw [hq]
      infer_instance
    apply q.genericMatrixConclusion_of_elliptic_cover hn ht hr'
      D.topologicalKrullDim_le_one
    · rw [hq]
      exact C.topologicalKrullDim_le_one
    · exact D.structure_euler_zero
    · rw [hq]
      exact C.structure_euler_zero

theorem exists_allDegreeMaximalRank_charZero
    (K : Type*) [Field K] [CharZero K] (n t r : ℕ)
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : n ≤ r) :
    ∃ M : LinearMatrix K n t (t+r), ∀ d, LinearMatrixMaximalRank M d := by
  obtain ⟨P, ⟨u, hu⟩, hP⟩ := genericMatrixConclusion_charZero K n t r hn ht hr
  exact ⟨universalLinearMatrix K n t (t+r) u, hP u hu⟩

end Steiner
