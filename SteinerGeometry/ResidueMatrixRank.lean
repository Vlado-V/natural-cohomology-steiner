module

public import SteinerGeometry.ProjectiveResiduePairing
public import SteinerGeometry.KernelNaturality
public import Mathlib.LinearAlgebra.Pi

set_option backward.privateInPublic true
@[expose] public section

/-! The matrix residue operation is the exact dual of polynomial matrix multiplication. -/
noncomputable section
namespace SteinerGeometry.ResidueMatrixRank
open ProjectiveResiduePairing
open scoped BigOperators
universe u v w
variable {K : Type u} [Field K] {σ : Type v} [Fintype σ]
variable {I J : Type w} [Fintype I] [Fintype J]

def polynomialMatrixMap (m : ℕ) (L : I → J → σ → K) :
    (J → PolynomialCoefficients σ K m) →ₗ[K]
      (I → PolynomialCoefficients σ K (m+1)) :=
  LinearMap.pi fun i => ∑ j, (multiplyLinearForm m (L i j)).comp (LinearMap.proj j)

def residueMatrixMap (m : ℕ) (L : I → J → σ → K) :
    (I → ResidueCoefficients σ K (m+1)) →ₗ[K]
      (J → ResidueCoefficients σ K m) :=
  LinearMap.pi fun j => ∑ i, (multiplyResidueLinearForm m (L i j)).comp (LinearMap.proj i)

def arrayDualEquiv (m : ℕ) (A : Type w) [Fintype A] :
    (A → ResidueCoefficients σ K m) ≃ₗ[K]
      Module.Dual K (A → PolynomialCoefficients σ K m) := by
  classical
  exact (LinearEquiv.piCongrRight fun _ : A => coefficientDualEquiv (σ := σ) (R := K) m).trans
    (LinearMap.lsum K (fun _ : A => PolynomialCoefficients σ K m) K)

omit [Fintype σ] in
theorem arrayDualEquiv_apply (m : ℕ) (A : Type w) [Fintype A]
    (q : A → ResidueCoefficients σ K m) (p : A → PolynomialCoefficients σ K m) :
    arrayDualEquiv m A q p = ∑ i, pairing (p i) (q i) := by
  classical
  simp [arrayDualEquiv, LinearMap.lsum_apply, pairing, coefficientDualEquiv]

omit [Fintype σ] in
theorem pairing_sum_left {A : Type w} [Fintype A] (m : ℕ)
    (p : A → PolynomialCoefficients σ K m) (q : ResidueCoefficients σ K m) :
    pairing (∑ i,p i) q = ∑ i,pairing (p i) q := map_sum (Finsupp.linearCombination K q) _ _

omit [Fintype σ] in
theorem pairing_sum_right {A : Type w} [Fintype A] (m : ℕ)
    (p : PolynomialCoefficients σ K m) (q : A → ResidueCoefficients σ K m) :
    pairing p (∑ i,q i) = ∑ i,pairing p (q i) := by
  change (coefficientDualEquiv (σ := σ) (R := K) m (∑ i,q i)) p = _
  rw [map_sum, LinearMap.sum_apply]
  rfl

/-- Every entry is transposed using the actual complementary-exponent
pairing, and the row/column sums are exchanged. -/
theorem arrayDualEquiv_residueMatrixMap (m : ℕ) (L : I → J → σ → K)
    (q : I → ResidueCoefficients σ K (m+1)) :
    arrayDualEquiv m J (residueMatrixMap m L q) =
      (polynomialMatrixMap m L).dualMap (arrayDualEquiv (m+1) I q) := by
  apply LinearMap.ext
  intro p
  change arrayDualEquiv m J (residueMatrixMap m L q) p =
    arrayDualEquiv (m+1) I q (polynomialMatrixMap m L p)
  simp only [arrayDualEquiv_apply, polynomialMatrixMap, residueMatrixMap,
    LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [show (∑ j, pairing (p j) (∑ i,multiplyResidueLinearForm m (L i j) (q i))) =
      ∑ j, ∑ i, pairing (p j) (multiplyResidueLinearForm m (L i j) (q i)) by
        apply Finset.sum_congr rfl
        intro j _
        exact pairing_sum_right m (p j) _]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [pairing_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  exact (pairing_multiplyLinearForm m (L i j) (p j) (q i)).symm

/-- Maximal rank passes from the polynomial coefficient matrix to the
actual transposed residue matrix. -/
theorem residueMatrixMap_maximalRank_iff (m : ℕ) (L : I → J → σ → K) :
    HasMaximalRank (residueMatrixMap m L) ↔ HasMaximalRank (polynomialMatrixMap m L) := by
  have h := hasMaximalRank_congr (arrayDualEquiv (m+1) I).toEquiv
    (arrayDualEquiv m J).toEquiv (residueMatrixMap m L) (polynomialMatrixMap m L).dualMap
    (arrayDualEquiv_residueMatrixMap m L)
  exact h.trans (hasMaximalRank_dualMap_iff (polynomialMatrixMap m L))

end SteinerGeometry.ResidueMatrixRank
