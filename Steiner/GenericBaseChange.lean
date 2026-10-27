module

public import Steiner.Generic
public import Steiner.BaseChange

@[expose] public section

/-! Coefficient extension and simultaneous minor descent for the actual
homogeneous multiplication maps of a matrix of linear forms. -/

noncomputable section
namespace Steiner
open Module MvPolynomial Matrix
variable {K L : Type*} [Field K] [Field L] {n a c t : ℕ}

/-- Coefficient extension on genuine homogeneous forms. -/
def formsMap (k : K →+* L) {m d : ℕ} : Forms K m d →ₛₗ[k] Forms L m d where
  toFun f := ⟨map k f.val, f.property.map k⟩
  map_add' f g := Subtype.ext (map_add _ _ _)
  map_smul' b f := by
    apply Subtype.ext
    change map k (b • f.val) = k b • map k f.val
    simp only [smul_eq_C_mul, map_mul, map_C]

@[simp] theorem formsMap_val (k : K →+* L) {m d : ℕ} (f : Forms K m d) :
    (formsMap k f).val = map k f.val := rfl

@[simp] theorem formsMap_basis (k : K →+* L) {m d : ℕ} (i : Sym (Fin m) d) :
    formsMap k (formsBasis K m d i) = formsBasis L m d i := by
  apply Subtype.ext
  exact formsBasis_map K m d k i

/-- Extending coefficients extends every monomial coordinate. -/
theorem formsMap_coordinates (k : K →+* L) {m d : ℕ}
    (f : Forms K m d) (i : Sym (Fin m) d) :
    (formsBasis L m d).repr (formsMap k f) i = k ((formsBasis K m d).repr f i) := by
  classical
  have hform : formsMap k f =
      ∑ j, k ((formsBasis K m d).repr f j) • formsBasis L m d j := by
    conv_lhs => rw [← (formsBasis K m d).sum_repr f]
    simp only [map_sum, map_smulₛₗ, formsMap_basis]
  rw [hform]
  simp [Finsupp.single_apply]

@[simp] theorem formsMap_multiplyLinear (k : K →+* L)
    (q : Forms K (n + 1) 1) (f : Forms K (n + 1) t) :
    formsMap k (multiplyLinear q f) = multiplyLinear (formsMap k q) (formsMap k f) := by
  apply Subtype.ext
  simp

/-- Monomial multiplication has field-independent structure coefficients. -/
def linearProductCoordinates (K : Type*) [Field K] (n t : ℕ)
    (b : Sym (Fin (n + 1)) (t + 1))
    (u : Sym (Fin (n + 1)) 1) (v : Sym (Fin (n + 1)) t) : K :=
  (formsBasis K (n + 1) (t + 1)).repr
    (multiplyLinear (formsBasis K (n + 1) 1 u) (formsBasis K (n + 1) t v)) b

@[simp] theorem linearProductCoordinates_map (k : K →+* L)
    (b : Sym (Fin (n + 1)) (t + 1))
    (u : Sym (Fin (n + 1)) 1) (v : Sym (Fin (n + 1)) t) :
    k (linearProductCoordinates K n t b u v) = linearProductCoordinates L n t b u v := by
  rw [linearProductCoordinates, ← formsMap_coordinates, formsMap_multiplyLinear,
    formsMap_basis, formsMap_basis]
  rfl

/-- The standard monomial basis on a vector of homogeneous forms. -/
def formVectorBasis (K : Type*) [Field K] (n b d : ℕ) :
    Basis (Σ _ : Fin b, Sym (Fin (n + 1)) d) K (Fin b → Forms K (n + 1) d) :=
  Pi.basis fun _ => formsBasis K (n + 1) d

/-- Universal degree matrix whose entries are linear polynomials in the original
matrix coefficients. Its rows and columns index actual homogeneous monomials. -/
def linearMatrixPolynomial (K : Type*) [Field K] (n a c t : ℕ) :
    Matrix (Σ _ : Fin a, Sym (Fin (n + 1)) (t + 1))
      (Σ _ : Fin c, Sym (Fin (n + 1)) t)
      (MvPolynomial (LinearMatrixParameter n a c) K) :=
  fun i j => ∑ u, X (i.1, j.1, u) * C (linearProductCoordinates K n t i.2 u j.2)

@[simp] theorem linearMatrixMap_single (M : LinearMatrix K n a c)
    (j : Fin c) (f : Forms K (n + 1) t) (i : Fin a) :
    linearMatrixMap M t (Pi.single j f) i = multiplyLinear (M i j) f := by
  classical
  apply Subtype.ext
  simp [linearMatrixMap, Pi.single_apply, apply_ite]

/-- Multiplication is linear in the linear-form argument. -/
def multiplyLinearLeft (f : Forms K (n + 1) t) :
    Forms K (n + 1) 1 →ₗ[K] Forms K (n + 1) (t + 1) where
  toFun q := multiplyLinear q f
  map_add' q q' := by apply Subtype.ext; simp [add_mul]
  map_smul' b q := by apply Subtype.ext; simp

/-- Evaluation of the universal polynomial degree matrix is exactly the matrix
of multiplication by the specialized linear matrix. -/
theorem linearMatrixPolynomial_eval (k : K →+* L)
    (u : LinearMatrixParameter n a c → L) :
    polynomialMatrixEval k u (linearMatrixPolynomial K n a c t) =
      LinearMap.toMatrix (formVectorBasis L n c t) (formVectorBasis L n a (t + 1))
        (linearMatrixMap (universalLinearMatrix L n a c u) t) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [formVectorBasis, Pi.basis_repr, Pi.basis_apply, linearMatrixMap_single]
  simp only [polynomialMatrixEval, Matrix.map_apply, linearMatrixPolynomial, map_sum,
    map_mul, eval₂Hom_C]
  simp only [linearProductCoordinates_map]
  have heq : multiplyLinear (universalLinearMatrix L n a c u i.1 j.1)
      (formsBasis L (n + 1) t j.2) =
      ∑ v, u (i.1, j.1, v) • multiplyLinear (formsBasis L (n + 1) 1 v)
        (formsBasis L (n + 1) t j.2) := by
    change multiplyLinearLeft _ (∑ v, _) = _
    simp only [map_sum, map_smul, multiplyLinearLeft]
    rfl
  rw [heq]
  simp [linearProductCoordinates]

/-- The universal polynomial rank is the rank of the actual multiplication map. -/
theorem linearMatrixPolynomial_rank (k : K →+* L)
    (u : LinearMatrixParameter n a c → L) :
    (polynomialMatrixEval k u (linearMatrixPolynomial K n a c t)).rank =
      finrank L (linearMatrixMap (universalLinearMatrix L n a c u) t).range := by
  classical
  rw [linearMatrixPolynomial_eval,
    Matrix.rank_eq_finrank_range_toLin _ (formVectorBasis L n a (t + 1))
      (formVectorBasis L n c t), Matrix.toLin_toMatrix]

/-- A finite list of maximal-rank conditions witnessed over any extension
field descends to one nonempty coefficient principal open over the base field. -/
theorem universalLinearMatrix_finiteRanks_principal_open_of_extension [Infinite K]
    (k : K →+* L) {J : Type*} [Fintype J] (degrees : J → ℕ)
    (M : LinearMatrix L n a c) (hM : ∀ j, LinearMatrixMaximalRank M (degrees j)) :
    ∃ D : MvPolynomial (LinearMatrixParameter n a c) K,
      (∃ u, eval u D ≠ 0) ∧
      ∀ u, eval u D ≠ 0 → ∀ j,
        LinearMatrixMaximalRank (universalLinearMatrix K n a c u) (degrees j) := by
  classical
  obtain ⟨D, hD, h⟩ := polynomial_matrix_ranks_descent k
    (fun j => linearMatrixPolynomial K n a c (degrees j))
    (fun _ => linearMatrixCoordinates L n M) 1 one_ne_zero
  refine ⟨D, hD, fun u hu j => ?_⟩
  have hlow := (h u hu).2 j
  rw [linearMatrixPolynomial_rank, linearMatrixPolynomial_rank,
    universalLinearMatrix_coordinates] at hlow
  have hmax := hM j
  dsimp [LinearMatrixMaximalRank] at hmax ⊢
  rw [hmax, finrank_matrixSource, finrank_matrixTarget] at hlow
  rw [finrank_matrixSource, finrank_matrixTarget]
  apply le_antisymm _ hlow
  simpa only [finrank_matrixSource, finrank_matrixTarget] using
    le_min (LinearMap.finrank_range_le
      (linearMatrixMap (universalLinearMatrix K n a c u) (degrees j)))
      (Submodule.finrank_le (linearMatrixMap
        (universalLinearMatrix K n a c u) (degrees j)).range)

/-- A critical injective/surjective pair over an extension field yields an
all-degree nonempty principal open over the original infinite field. -/
theorem universalLinearMatrix_allTwists_principal_open_of_extension [Infinite K]
    (k : K →+* L) (M : LinearMatrix L n a c) (p q : ℕ) (hpq : q ≤ p + 1)
    (hinj : Function.Injective (linearMatrixMap M p))
    (hsurj : Function.Surjective (linearMatrixMap M q)) :
    ∃ D : MvPolynomial (LinearMatrixParameter n a c) K,
      (∃ u, eval u D ≠ 0) ∧
      ∀ u, eval u D ≠ 0 → ∀ t,
        LinearMatrixMaximalRank (universalLinearMatrix K n a c u) t := by
  classical
  let degrees : Fin 2 → ℕ := ![p, q]
  have hM (j : Fin 2) : LinearMatrixMaximalRank M (degrees j) := by
    fin_cases j
    · exact linearMatrixMaximalRank_of_injective M p hinj
    · exact linearMatrixMaximalRank_of_surjective M q hsurj
  obtain ⟨D, hD, h⟩ := universalLinearMatrix_finiteRanks_principal_open_of_extension k degrees M hM
  have hsmall : finrank K (MatrixSource K n c p) ≤ finrank K (MatrixTarget K n a p) := by
    have hi := LinearMap.finrank_le_finrank_of_injective hinj
    simpa only [finrank_matrixSource, finrank_matrixTarget] using hi
  have hlarge : finrank K (MatrixTarget K n a q) ≤ finrank K (MatrixSource K n c q) := by
    have hs := LinearMap.finrank_le_finrank_of_surjective hsurj
    simpa only [finrank_matrixSource, finrank_matrixTarget] using hs
  refine ⟨D, hD, fun u hu t => ?_⟩
  have hi := (linearMatrixMaximalRank_iff_injective _ p hsmall).mp (h u hu 0)
  have hs := (linearMatrixMaximalRank_iff_surjective _ q hlarge).mp (h u hu 1)
  by_cases ht : t ≤ p
  · exact linearMatrixMaximalRank_of_injective _ t
      (linearMatrixMap_injective_downward _ ht hi)
  · exact linearMatrixMaximalRank_of_surjective _ t
      (linearMatrixMap_surjective_upward _ (by omega : q ≤ t) hs)

/-- Extension-field surjectivity in the initial positive degree yields an
all-degree principal open even when the injective critical degree is zero. -/
theorem universalLinearMatrix_allTwists_principal_open_of_extension_surjective_zero [Infinite K]
    (k : K →+* L) (M : LinearMatrix L n a c)
    (hsurj : Function.Surjective (linearMatrixMap M 0)) :
    ∃ D : MvPolynomial (LinearMatrixParameter n a c) K,
      (∃ u, eval u D ≠ 0) ∧
      ∀ u, eval u D ≠ 0 → ∀ t,
        LinearMatrixMaximalRank (universalLinearMatrix K n a c u) t := by
  classical
  obtain ⟨D, hD, h⟩ := universalLinearMatrix_finiteRanks_principal_open_of_extension k
    (fun _ : Unit => 0) M (fun _ => linearMatrixMaximalRank_of_surjective M 0 hsurj)
  have hlarge : finrank K (MatrixTarget K n a 0) ≤ finrank K (MatrixSource K n c 0) := by
    have hs := LinearMap.finrank_le_finrank_of_surjective hsurj
    simpa only [finrank_matrixSource, finrank_matrixTarget] using hs
  refine ⟨D, hD, fun u hu t => ?_⟩
  have hs := (linearMatrixMaximalRank_iff_surjective _ 0 hlarge).mp (h u hu ())
  exact linearMatrixMaximalRank_of_surjective _ t
    (linearMatrixMap_surjective_upward _ (Nat.zero_le _) hs)

end Steiner
