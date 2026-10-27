import SteinerGeometry.KernelMonomialCoordinates

/-! The local contraction matrix over a characteristic-zero algebra of regular functions. -/
noncomputable section
namespace SteinerGeometry
open MvPolynomial Steiner.SymmetricContraction
open scoped TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Integer derivative multiplicities with scalar coefficients, over the actual local ring. -/
def weightedContraction (f : Fin (n+1) → R) (d : ℕ) :
    (Sym (Fin (n+1)) (d+1) → M) →ₗ[R] (Sym (Fin (n+1)) d → M) where
  toFun v b := ∑ a, ∑ i, contractionMultiplicity d a b i • (f i • v a)
  map_add' v w := by
    funext b
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    funext b
    simp only [Pi.smul_apply, ← smul_comm (f _), smul_comm (_ : ℕ) r,
      Finset.smul_sum, RingHom.id_apply]

private theorem directional_apply (f : Fin (n+1) → R) (P : Aux n R) :
    directional f P = ∑ i, f i • pderiv i P := by
  rw [directional_eq_sum]
  change (Derivation.coeFnAddMonoidHom (∑ i, f i • pderiv (R := R) i)) P = _
  rw [map_sum, Finset.sum_apply]
  rfl

private theorem directional_monomial_coeff (f : Fin (n+1) → R) (d : ℕ)
    (a : Sym (Fin (n+1)) (d+1)) (b : Sym (Fin (n+1)) d) :
    (directional f (monomial (Steiner.operatorExponent (d+1) a) 1)).coeff
      (Steiner.operatorExponent d b) =
        ∑ i, (contractionMultiplicity d a b i : R) * f i := by
  classical
  rw [directional_apply]
  simp only [coeff_sum, coeff_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_pderiv, coeff_monomial]
  unfold contractionMultiplicity
  split_ifs with h
  · simp [smul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm]
  · simp

/-- Coefficient reading identifies the literal derivative with its integer multiplicity matrix. -/
theorem weightedContraction_coordinates (f : Fin (n+1) → R) (d : ℕ)
    (v : Sym (Fin (n+1)) (d+1) → M) :
    HomogeneousTensor.homogeneousTensorCoefficientVector d
      (tensorDirectional f (HomogeneousTensor.homogeneousTensorSynthesis (R := R) (d+1) v)) =
        weightedContraction f d v := by
  classical
  funext b
  change HomogeneousTensor.tensorCoefficients
    (tensorDirectional f (∑ a : Sym (Fin (n+1)) (d+1),
      (monomial (Steiner.operatorExponent (d+1) a) 1 : Aux n R) ⊗ₜ[R] v a))
    (Steiner.operatorExponent d b) = _
  simp only [map_sum, Finsupp.finsetSum_apply]
  change (∑ a, HomogeneousTensor.tensorCoefficients
    ((directional f (monomial (Steiner.operatorExponent (d+1) a) 1)) ⊗ₜ[R] v a)
    (Steiner.operatorExponent d b)) = _
  simp only [HomogeneousTensor.tensorCoefficients_tmul, directional_monomial_coeff,
    Finset.sum_smul, mul_smul, Nat.cast_smul_eq_nsmul]
  rfl

private theorem directional_monomial_coeff_zero (f : Fin (n+1) → R) (d : ℕ)
    (a : Sym (Fin (n+1)) (d+1)) (b : Fin (n+1) →₀ ℕ) (hb : b.degree ≠ d) :
    (directional f (monomial (Steiner.operatorExponent (d+1) a) 1)).coeff b = 0 := by
  classical
  rw [directional_apply]
  simp only [coeff_sum, coeff_smul]
  apply Finset.sum_eq_zero
  intro i _
  rw [coeff_pderiv, coeff_monomial]
  have hn : Steiner.operatorExponent (d+1) a ≠ b + Finsupp.single i 1 := by
    intro h
    have hd := congrArg Finsupp.degree h
    simp only [Steiner.operatorExponent_degree, map_add, Finsupp.degree_single] at hd
    omega
  simp [hn]

theorem tensorDirectional_synthesis_homogeneous (f : Fin (n+1) → R) (d : ℕ)
    (v : Sym (Fin (n+1)) (d+1) → M) :
    TensorHomogeneous d
      (tensorDirectional f (HomogeneousTensor.homogeneousTensorSynthesis (R := R) (d+1) v)) := by
  classical
  apply (HomogeneousTensor.tensorHomogeneous_iff_coefficients d _).mpr
  intro b hb
  change HomogeneousTensor.tensorCoefficients
    (tensorDirectional f (∑ a : Sym (Fin (n+1)) (d+1),
      (monomial (Steiner.operatorExponent (d+1) a) 1 : Aux n R) ⊗ₜ[R] v a)) b = 0
  simp only [map_sum, Finsupp.finsetSum_apply]
  change (∑ a, HomogeneousTensor.tensorCoefficients
    ((directional f (monomial (Steiner.operatorExponent (d+1) a) 1)) ⊗ₜ[R] v a) b) = 0
  simp only [HomogeneousTensor.tensorCoefficients_tmul,
    directional_monomial_coeff_zero f d _ b hb, zero_smul, Finset.sum_const_zero]

/-- Vanishing of the finite multiplicity matrix is exactly vanishing of the genuine derivative. -/
theorem weightedContraction_eq_zero_iff (f : Fin (n+1) → R) (d : ℕ)
    (v : Sym (Fin (n+1)) (d+1) → M) :
    weightedContraction f d v = 0 ↔
      tensorDirectional f (HomogeneousTensor.homogeneousTensorSynthesis (R := R) (d+1) v) = 0 := by
  rw [← weightedContraction_coordinates]
  constructor
  · intro h
    have ht := HomogeneousTensor.homogeneousTensorSynthesis_coefficients d _
      (tensorDirectional_synthesis_homogeneous f d v)
    rw [h] at ht
    simpa only [HomogeneousTensor.homogeneousTensorSynthesis, Pi.zero_apply,
      TensorProduct.tmul_zero, Finset.sum_const_zero] using ht.symm
  · intro h
    rw [h]
    exact map_zero (HomogeneousTensor.homogeneousTensorCoefficientMap d)

/-- The explicit finite monomial-product map is exactly the kernel of the
integer multiplicity matrix over every characteristic-zero base algebra. -/
theorem weightedContraction_kernel_exact {K : Type*} [Field K] [CharZero K] [Algebra K R]
    (f : Fin (n+1) → R) (A B : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    (d : ℕ) (x : Sym (Fin (n+1)) (d+1) → M) :
    weightedContraction f d x = 0 ↔
      ∃! v : Sym (Fin n) (d+1) → M, splitPolynomialMap A (d+1) v = x := by
  rw [weightedContraction_eq_zero_iff]
  exact splitPolynomialMap_exact (K := K) f A B hAB hBA hA (d+1) x

end SteinerGeometry
