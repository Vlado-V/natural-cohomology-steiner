module

public import Steiner.Critical

@[expose] public section

/-! Field extension preserves the ranks of the actual homogeneous maps.
One complex witness therefore suffices for the assertion over every
characteristic-zero coefficient field. -/

noncomputable section
namespace Steiner
open Module MvPolynomial

variable {K L : Type*} [Field K] [Field L] {n a c : ℕ}

def linearMatrixExtend (k : K →+* L) (M : LinearMatrix K n a c) :
    LinearMatrix L n a c := fun i j => formsMap k (M i j)

theorem linearMatrixCoordinates_extend (k : K →+* L) (M : LinearMatrix K n a c) :
    linearMatrixCoordinates L n (linearMatrixExtend k M) =
      k ∘ linearMatrixCoordinates K n M := by
  funext i
  exact formsMap_coordinates k (M i.1 i.2.1) i.2.2

theorem universalLinearMatrix_extend (k : K →+* L) (M : LinearMatrix K n a c) :
    universalLinearMatrix L n a c (k ∘ linearMatrixCoordinates K n M) =
      linearMatrixExtend k M := by
  rw [← linearMatrixCoordinates_extend, universalLinearMatrix_coordinates]

theorem linearMatrixMap_rank_extend (k : K →+* L) (M : LinearMatrix K n a c)
    (d : ℕ) :
    finrank L (linearMatrixMap (linearMatrixExtend k M) d).range =
      finrank K (linearMatrixMap M d).range := by
  have h := polynomialMatrixEval_rank_map_parameter k
    (linearMatrixCoordinates K n M) (linearMatrixPolynomial K n a c d)
  rw [linearMatrixPolynomial_rank, linearMatrixPolynomial_rank,
    universalLinearMatrix_extend, universalLinearMatrix_coordinates] at h
  exact h

theorem linearMatrixMaximalRank_extend_iff (k : K →+* L)
    (M : LinearMatrix K n a c) (d : ℕ) :
    LinearMatrixMaximalRank (linearMatrixExtend k M) d ↔ LinearMatrixMaximalRank M d := by
  simp only [LinearMatrixMaximalRank, linearMatrixMap_rank_extend,
    finrank_matrixSource]

/-- Descend an extension-field witness to an actual matrix over the infinite
base field, simultaneously in every homogeneous degree. -/
theorem exists_matrix_of_extension_witness [Infinite K]
    {n t r : ℕ} (k : K →+* L) (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (M : LinearMatrix L n t (t + r)) (hM : ∀ d, LinearMatrixMaximalRank M d) :
    ∃ N : LinearMatrix K n t (t + r), ∀ d, LinearMatrixMaximalRank N d := by
  obtain ⟨D, ⟨u, hu⟩, h⟩ :=
    genericMatrixConclusion_of_extension_witness k hn ht hr M hM
  exact ⟨universalLinearMatrix K n t (t + r) u, h u hu⟩

/-- A witness over any characteristic-zero extension of the rationals yields
the generic assertion over every characteristic-zero field. The geometric
construction itself only has to be performed once. -/
theorem genericMatrixConclusion_of_rational_extension [CharZero K]
    {E : Type*} [Field E] [CharZero E] {n t r : ℕ}
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (M : LinearMatrix E n t (t + r)) (hM : ∀ d, LinearMatrixMaximalRank M d) :
    GenericMatrixConclusion K n t r := by
  obtain ⟨N, hN⟩ := exists_matrix_of_extension_witness
    (Rat.castHom E) hn ht hr M hM
  let N' := linearMatrixExtend (Rat.castHom K) N
  have hN' (d : ℕ) : LinearMatrixMaximalRank N' d :=
    (linearMatrixMaximalRank_extend_iff (Rat.castHom K) N d).mpr (hN d)
  exact genericMatrixConclusion_of_extension_witness (RingHom.id K) hn ht hr N' hN'

end Steiner
