import Steiner.SymmetricContraction

/-! The product of kernel-valued linear forms is killed by symmetric contraction. -/
noncomputable section
namespace SteinerGeometry
open MvPolynomial
open Steiner.SymmetricContraction
open scoped TensorProduct

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {n : ℕ}

/-- Symmetric contraction with values in an arbitrary coefficient module. -/
def moduleDirectional (e : Fin (n+1) → M) :
    Derivation R (Aux n R) (Aux n R ⊗[R] M) :=
  mkDerivation R (fun i => (1 : Aux n R) ⊗ₜ[R] e i)

@[simp] theorem moduleDirectional_linearForm (e : Fin (n+1) → M) (c : Fin (n+1) → R) :
    moduleDirectional e (linearForm c) = (1 : Aux n R) ⊗ₜ[R] (∑ i, c i • e i) := by
  classical
  simp only [linearForm, C_mul', map_sum, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [(moduleDirectional e).map_smul]
  simp only [moduleDirectional, mkDerivation_X, TensorProduct.tmul_smul]

/-- This is the local polynomial identity underlying the global symmetric-power
kernel map: multiplication of any number of kernel linear forms stays in the kernel. -/
theorem moduleDirectional_product_eq_zero {ι : Type*} (s : Finset ι)
    (e : Fin (n+1) → M) (c : ι → Fin (n+1) → R)
    (hc : ∀ j ∈ s, ∑ i, c j i • e i = 0) :
    moduleDirectional e (∏ j ∈ s, linearForm (c j)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Derivation.leibniz]
    rw [ih (fun k hk => hc k (Finset.mem_insert_of_mem hk)),
      moduleDirectional_linearForm, hc j (Finset.mem_insert_self _ _)]
    simp

/-- Extract one coefficient from a polynomial with values in a module. -/
def modulePolynomialCoeff (b : Fin (n+1) →₀ ℕ) : Aux n R ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp ((lcoeff R b).rTensor M)

@[simp] theorem modulePolynomialCoeff_tmul (b : Fin (n+1) →₀ ℕ)
    (P : Aux n R) (m : M) :
    modulePolynomialCoeff b (P ⊗ₜ[R] m) = P.coeff b • m := by
  simp [modulePolynomialCoeff]

/-- The module-valued derivation has the expected derivative coefficient formula. -/
theorem modulePolynomialCoeff_directional (b : Fin (n+1) →₀ ℕ)
    (e : Fin (n+1) → M) (P : Aux n R) :
    modulePolynomialCoeff b (moduleDirectional e P) =
      ∑ i, (pderiv i P).coeff b • e i := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [map_add, hP, hQ, add_smul, Finset.sum_add_distrib]
  | monomial a r =>
    rw [moduleDirectional, mkDerivation_monomial, Finsupp.sum_fintype]
    · simp only [map_smul, map_sum]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, modulePolynomialCoeff_tmul]
      simp only [pderiv_monomial, coeff_monomial, smul_smul]
      split_ifs <;> simp
    · intro i
      simp

/-- Vanishing of every coefficient of the contracted polynomial product. -/
theorem product_contraction_coeff_eq_zero {ι : Type*} (s : Finset ι)
    (e : Fin (n+1) → M) (c : ι → Fin (n+1) → R)
    (hc : ∀ j ∈ s, ∑ i, c j i • e i = 0) (b : Fin (n+1) →₀ ℕ) :
    ∑ i, (pderiv i (∏ j ∈ s, linearForm (c j))).coeff b • e i = 0 := by
  rw [← modulePolynomialCoeff_directional, moduleDirectional_product_eq_zero s e c hc, map_zero]

end SteinerGeometry
