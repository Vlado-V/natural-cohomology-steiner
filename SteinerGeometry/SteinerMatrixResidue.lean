import SteinerGeometry.ResidueMatrixRank
import Steiner.LinearMatrix

/-! Residue rank transfer for the manuscript's literal homogeneous-polynomial matrices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.SteinerMatrixResidue
open ProjectiveResiduePairing ResidueMatrixRank
open scoped BigOperators
universe u
variable {K : Type u} [Field K]

def formsCoefficientEquiv (n m : ℕ) :
    Steiner.Forms K (n+1) m ≃ₗ[K] PolynomialCoefficients (Fin (n+1)) K m :=
  (Steiner.formsBasis K (n+1) m).repr.trans
    (Finsupp.domLCongr (R := K) (M := K) (Steiner.exponentEquiv (n+1) m))

theorem formsCoefficientEquiv_symm_single (n m : ℕ)
    (a : DegreeMonomial (Fin (n+1)) m) (c : K) :
    ((formsCoefficientEquiv (K := K) n m).symm (Finsupp.single a c)).val =
      MvPolynomial.monomial a.val c := by
  change ((Steiner.formsBasis K (n+1) m).repr.symm
    ((Finsupp.domLCongr (R := K) (M := K) (Steiner.exponentEquiv (n+1) m)).symm (Finsupp.single a c))).val = _
  rw [Finsupp.domLCongr_symm, Finsupp.domLCongr_single, Module.Basis.repr_symm_single]
  change c • (Steiner.formsBasis K (n+1) m ((Steiner.exponentEquiv (n+1) m).symm a)).val = _
  rw [Steiner.formsBasis_val_monomial, Equiv.apply_symm_apply]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem formsCoefficientEquiv_symm_val (n m : ℕ)
    (p : PolynomialCoefficients (Fin (n+1)) K m) :
    ((formsCoefficientEquiv (K := K) n m).symm p).val = polynomialOfCoefficients m p := by
  have h : (Steiner.Forms K (n+1) m).subtype.comp
      (formsCoefficientEquiv (K := K) n m).symm.toLinearMap = polynomialOfCoefficients m := by
    apply Finsupp.lhom_ext
    intro a c
    exact (formsCoefficientEquiv_symm_single n m a c).trans
      (polynomialOfCoefficients_single m a c).symm
  exact LinearMap.congr_fun h p

theorem polynomialOfCoefficients_multiplyLinearForm (n m : ℕ) (L : Fin (n+1) → K)
    (p : PolynomialCoefficients (Fin (n+1)) K m) :
    polynomialOfCoefficients (m+1) (multiplyLinearForm m L p) =
      (∑ k, MvPolynomial.monomial (Finsupp.single k 1) (L k)) * polynomialOfCoefficients m p := by
  simp only [multiplyLinearForm, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    polynomialOfCoefficients_multiplyCoordinate, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_mul_assoc]
  congr 1
  simp only [MvPolynomial.X, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

/-- The coordinate coefficients of a genuine homogeneous linear form. -/
def linearCoefficients {n : ℕ} (q : Steiner.Forms K (n+1) 1) (i : Fin (n+1)) : K :=
  q.val.coeff (Finsupp.single i 1)

theorem linearForm_eq_coefficients {n : ℕ} (q : Steiner.Forms K (n+1) 1) :
    q.val = ∑ i, MvPolynomial.monomial (Finsupp.single i 1) (linearCoefficients q i) := by
  have hq : q.val ∈ Submodule.span K (Set.range (MvPolynomial.X : Fin (n+1) → MvPolynomial (Fin (n+1)) K)) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact q.property
  suffices h : ∀ p : MvPolynomial (Fin (n+1)) K,
      p ∈ Submodule.span K (Set.range (MvPolynomial.X : Fin (n+1) → MvPolynomial (Fin (n+1)) K)) →
      p = ∑ i, MvPolynomial.monomial (Finsupp.single i 1) (p.coeff (Finsupp.single i 1)) from h q.val hq
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j,rfl⟩ := hx
      simp only [MvPolynomial.coeff_X, Finsupp.single_left_inj one_ne_zero]
      rw [Finset.sum_eq_single j]
      · simp [MvPolynomial.X]
      · intro b _ hbj
        simp [Ne.symm hbj]
      · simp
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [MvPolynomial.coeff_add, map_add, Finset.sum_add_distrib] using congrArg₂ (· + ·) ihx ihy
  | smul a x hx ih =>
      simpa only [MvPolynomial.coeff_smul, map_smul, Finset.smul_sum] using congrArg (a • ·) ih

def matrixCoefficients {n a b : ℕ} (M : Steiner.LinearMatrix K n a b) :
    Fin a → Fin b → Fin (n+1) → K := fun i j => linearCoefficients (M i j)

def matrixFormsCoefficientEquiv (n m a : ℕ) :
    (Fin a → Steiner.Forms K (n+1) m) ≃ₗ[K]
      (Fin a → PolynomialCoefficients (Fin (n+1)) K m) :=
  LinearEquiv.piCongrRight fun _ => formsCoefficientEquiv n m

theorem matrixFormsCoefficientEquiv_map {n a b : ℕ}
    (M : Steiner.LinearMatrix K n a b) (m : ℕ)
    (x : Fin b → Steiner.Forms K (n+1) m) :
    matrixFormsCoefficientEquiv n (m+1) a (Steiner.linearMatrixMap M m x) =
      polynomialMatrixMap m (matrixCoefficients M) (matrixFormsCoefficientEquiv n m b x) := by
  funext i
  apply polynomialOfCoefficients_injective (m+1)
  rw [← formsCoefficientEquiv_symm_val]
  change ((formsCoefficientEquiv n (m+1)).symm
    ((formsCoefficientEquiv n (m+1)) (Steiner.linearMatrixMap M m x i))).val = _
  rw [LinearEquiv.symm_apply_apply, Steiner.linearMatrixMap_val]
  simp only [polynomialMatrixMap, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, map_sum,
    polynomialOfCoefficients_multiplyLinearForm]
  apply Finset.sum_congr rfl
  intro j _
  change (M i j).val * (x j).val =
    (∑ k, MvPolynomial.monomial (Finsupp.single k 1) (linearCoefficients (M i j) k)) *
      polynomialOfCoefficients m (formsCoefficientEquiv n m (x j))
  rw [← linearForm_eq_coefficients (M i j), ← formsCoefficientEquiv_symm_val]
  rw [LinearEquiv.symm_apply_apply]

/-- The residue polynomial matrix is the manuscript's literal matrix map,
under the explicit monomial bases. -/
theorem polynomialMatrixMap_maximalRank_iff {n a b : ℕ}
    (M : Steiner.LinearMatrix K n a b) (m : ℕ) :
    HasMaximalRank (polynomialMatrixMap m (matrixCoefficients M)) ↔
      Steiner.LinearMatrixMaximalRank M m := by
  have h := hasMaximalRank_congr
    (matrixFormsCoefficientEquiv (K := K) n m b).toEquiv
    (matrixFormsCoefficientEquiv (K := K) n (m+1) a).toEquiv
    (Steiner.linearMatrixMap M m) (polynomialMatrixMap m (matrixCoefficients M))
    (matrixFormsCoefficientEquiv_map M m)
  exact h.symm.trans (hasMaximalRank_iff_finrank_range_eq_min (Steiner.linearMatrixMap M m))

end SteinerGeometry.SteinerMatrixResidue
