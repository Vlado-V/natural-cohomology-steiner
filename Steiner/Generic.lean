module

public import Steiner.LinearMatrix
public import Steiner.RankOpen

@[expose] public section

/-!
# Independent coefficients and the all-twist rank open

The parameters are the coefficients of every entry of a genuine matrix of
linear forms.  Two finite determinant conditions at the numerical crossing
give all twists simultaneously.  A simultaneous matrix witness supplies these finite nonvanishing conditions.
-/

noncomputable section

namespace Steiner

open Module MvPolynomial

variable (K : Type*) [Field K] (n : ℕ)

/-- One independent scalar parameter for every monomial coefficient of every entry. -/
abbrev LinearMatrixParameter (n a c : ℕ) := Fin a × Fin c × Sym (Fin (n + 1)) 1

/-- The universal matrix, specialized at its entry coefficients. -/
def universalLinearMatrix (a c : ℕ) :
    (LinearMatrixParameter n a c → K) →ₗ[K] LinearMatrix K n a c where
  toFun u i j := ∑ b, u (i, j, b) • formsBasis K (n + 1) 1 b
  map_add' u v := by
    funext i j
    change (∑ b, (u (i, j, b) + v (i, j, b)) • formsBasis K (n + 1) 1 b) =
      (∑ b, u (i, j, b) • formsBasis K (n + 1) 1 b) +
        (∑ b, v (i, j, b) • formsBasis K (n + 1) 1 b)
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' k u := by
    funext i j
    change (∑ b, (k * u (i, j, b)) • formsBasis K (n + 1) 1 b) =
      k • ∑ b, u (i, j, b) • formsBasis K (n + 1) 1 b
    simp only [Finset.smul_sum, smul_smul]

/-- Every linear matrix is obtained by specializing the universal coefficients. -/
def linearMatrixCoordinates {a c : ℕ} (L : LinearMatrix K n a c) :
    LinearMatrixParameter n a c → K := fun p => (formsBasis K (n + 1) 1).repr (L p.1 p.2.1) p.2.2

@[simp] theorem universalLinearMatrix_coordinates {a c : ℕ} (L : LinearMatrix K n a c) :
    universalLinearMatrix K n a c (linearMatrixCoordinates K n L) = L := by
  funext i j
  change (∑ b, (formsBasis K (n + 1) 1).repr (L i j) b • formsBasis K (n + 1) 1 b) = L i j
  exact (formsBasis K (n + 1) 1).sum_repr (L i j)

variable {K n} {a c : ℕ}

/-- Matrix multiplication at a fixed vector is linear in the entries. -/
def linearMatrixApplyParameter (t : ℕ) (v : MatrixSource K n c t) :
    LinearMatrix K n a c →ₗ[K] MatrixTarget K n a t where
  toFun L := linearMatrixMap L t v
  map_add' L M := by
    ext i
    simp [linearMatrixMap, add_mul, Finset.sum_add_distrib]
  map_smul' k L := by
    ext i
    simp [linearMatrixMap, Finset.smul_sum]

/-- Any polynomial family of entries gives polynomial multiplication maps. -/
theorem linearMatrixMap_polynomial_family {ι : Type*}
    (F : (ι → K) → LinearMatrix K n a c) (hF : IsPolynomialFamily F) (t : ℕ) :
    IsPolynomialFamily (fun u => linearMatrixMap (F u) t) := by
  apply isPolynomialFamily_linearMap
  intro v
  exact hF.linear_comp (linearMatrixApplyParameter t v)

/-- Every twist of the universal multiplication map has polynomial coefficients. -/
theorem universalLinearMatrixMap_isPolynomialFamily (a c t : ℕ) :
    IsPolynomialFamily (fun u : LinearMatrixParameter n a c → K =>
      linearMatrixMap (universalLinearMatrix K n a c u) t) := by
  classical
  apply isPolynomialFamily_linearMap
  intro v
  exact isPolynomialFamily_linear
    ((linearMatrixApplyParameter t v).comp (universalLinearMatrix K n a c))


/-- A maximal-rank witness supplies a determinant open of maximal-rank maps. -/
theorem universalLinearMatrix_maximalRank_principal_open
    (L : LinearMatrix K n a c) (t : ℕ) (hL : LinearMatrixMaximalRank L t) :
    ∃ D : MvPolynomial (LinearMatrixParameter n a c) K,
      eval (linearMatrixCoordinates K n L) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 →
        LinearMatrixMaximalRank (universalLinearMatrix K n a c u) t := by
  obtain ⟨D, hD, h⟩ := rank_polynomial_principal_open
    (fun u => linearMatrixMap (universalLinearMatrix K n a c u) t)
    (universalLinearMatrixMap_isPolynomialFamily a c t) (linearMatrixCoordinates K n L)
  refine ⟨D, hD, fun u hu => ?_⟩
  have hlow := h u hu
  rw [universalLinearMatrix_coordinates] at hlow
  dsimp [LinearMatrixMaximalRank] at hL ⊢
  rw [hL] at hlow
  exact le_antisymm
    (le_min (LinearMap.finrank_range_le _) (Submodule.finrank_le _)) hlow

/-- Injectivity is preserved on a coefficient principal open through its witness. -/
theorem universalLinearMatrix_injective_principal_open
    (L : LinearMatrix K n a c) (t : ℕ) (hL : Function.Injective (linearMatrixMap L t)) :
    ∃ D : MvPolynomial (LinearMatrixParameter n a c) K,
      eval (linearMatrixCoordinates K n L) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 →
        Function.Injective (linearMatrixMap (universalLinearMatrix K n a c u) t) := by
  apply injective_polynomial_principal_open
    (fun u => linearMatrixMap (universalLinearMatrix K n a c u) t)
    (universalLinearMatrixMap_isPolynomialFamily a c t) (linearMatrixCoordinates K n L)
  simpa using hL

/-- Surjectivity is preserved on a coefficient principal open through its witness. -/
theorem universalLinearMatrix_surjective_principal_open
    (L : LinearMatrix K n a c) (t : ℕ) (hL : Function.Surjective (linearMatrixMap L t)) :
    ∃ D : MvPolynomial (LinearMatrixParameter n a c) K,
      eval (linearMatrixCoordinates K n L) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 →
        Function.Surjective (linearMatrixMap (universalLinearMatrix K n a c u) t) := by
  obtain ⟨D, hD, h⟩ := rank_polynomial_principal_open
    (fun u => linearMatrixMap (universalLinearMatrix K n a c u) t)
    (universalLinearMatrixMap_isPolynomialFamily a c t) (linearMatrixCoordinates K n L)
  refine ⟨D, hD, fun u hu => ?_⟩
  have hlow := h u hu
  rw [universalLinearMatrix_coordinates, LinearMap.range_eq_top.mpr hL, finrank_top] at hlow
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact le_antisymm (Submodule.finrank_le _) hlow

/-- An injective and a surjective critical map, with no intervening twist,
supply one nonempty principal open for maximal rank in every degree. -/
theorem universalLinearMatrix_allTwists_principal_open
    (L : LinearMatrix K n a c) (p q : ℕ) (hpq : q ≤ p + 1)
    (hinj : Function.Injective (linearMatrixMap L p))
    (hsurj : Function.Surjective (linearMatrixMap L q)) :
    ∃ D : MvPolynomial (LinearMatrixParameter n a c) K,
      eval (linearMatrixCoordinates K n L) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 → ∀ t,
        LinearMatrixMaximalRank (universalLinearMatrix K n a c u) t := by
  obtain ⟨D₀, hD₀, h₀⟩ := universalLinearMatrix_injective_principal_open L p hinj
  obtain ⟨D₁, hD₁, h₁⟩ := universalLinearMatrix_surjective_principal_open L q hsurj
  refine ⟨D₀ * D₁, by simpa using mul_ne_zero hD₀ hD₁, ?_⟩
  intro u hu t
  have hu₀ : eval u D₀ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hu)).1
  have hu₁ : eval u D₁ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hu)).2
  by_cases ht : t ≤ p
  · exact linearMatrixMaximalRank_of_injective _ t
      (linearMatrixMap_injective_downward _ ht (h₀ u hu₀))
  · exact linearMatrixMaximalRank_of_surjective _ t
      (linearMatrixMap_surjective_upward _ (by omega : q ≤ t) (h₁ u hu₁))

/-- Surjectivity at the initial positive target degree already controls all
positive target degrees; degree zero has zero source by convention. -/
theorem universalLinearMatrix_allTwists_principal_open_of_surjective_zero
    (L : LinearMatrix K n a c) (hL : Function.Surjective (linearMatrixMap L 0)) :
    ∃ D : MvPolynomial (LinearMatrixParameter n a c) K,
      eval (linearMatrixCoordinates K n L) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 → ∀ t,
        LinearMatrixMaximalRank (universalLinearMatrix K n a c u) t := by
  obtain ⟨D, hD, h⟩ := universalLinearMatrix_surjective_principal_open L 0 hL
  exact ⟨D, hD, fun u hu t => linearMatrixMaximalRank_of_surjective _ t
    (linearMatrixMap_surjective_upward _ (Nat.zero_le _) (h u hu))⟩

end Steiner
