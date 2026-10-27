module

public import Steiner.OperatorDuality

@[expose] public section

/-! The finite-dimensional part of the section-multiplication construction.
The geometric application supplies the section spaces and proves the two
vanishing conditions via its cohomology sequence. -/

noncomputable section
namespace Steiner
open Module

variable {K : Type*} [Field K] [CharZero K] {n a c : ℕ}
variable {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The section-contraction map controls maximal rank of the transposed
linear presentation, with its kernel and cokernel sides correctly reversed. -/
theorem operatorLinearMatrix_maximalRank
    (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin (n + 1) → V →ₗ[K] W) (d : ℕ)
    (h : Function.Injective (operatorDifferential T d) ∨
      Function.Surjective (operatorDifferential T d)) :
    LinearMatrixMaximalRank (operatorLinearMatrix bV bW T) d := by
  rcases h with h | h
  · apply linearMatrixMaximalRank_of_surjective
    exact (operatorDifferential_injective_iff_linearMatrixMap_surjective bV bW T d).mp h
  · apply linearMatrixMaximalRank_of_injective
    exact (operatorDifferential_surjective_iff_linearMatrixMap_injective bV bW T d).mp h

/-- One fixed multiplication-of-sections tensor supplies one fixed linear
matrix in every degree. The hypothesis is the differential consequence of
the geometric natural-cohomology calculation, not an assumed matrix rank. -/
theorem exists_sectionMultiplication_matrix
    (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin (n + 1) → V →ₗ[K] W)
    (h : ∀ d, Function.Injective (operatorDifferential T d) ∨
      Function.Surjective (operatorDifferential T d)) :
    ∃ M : LinearMatrix K n a c, ∀ d, LinearMatrixMaximalRank M d :=
  ⟨operatorLinearMatrix bV bW T, fun d => operatorLinearMatrix_maximalRank bV bW T d (h d)⟩

end Steiner
