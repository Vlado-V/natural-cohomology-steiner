module

public import Steiner.Homogeneous
public import Steiner.LinearMatrix
public import Steiner.FactorialWeights
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! Concrete coefficient transpose duality for polynomial differential
operators and actual matrices of linear forms in any finite number of variables. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Steiner
open Module MvPolynomial
open scoped TensorProduct
variable {n : ℕ} {K : Type*} [Field K]
variable {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] {a c : ℕ}

/-- Finite symmetric indices for degree-d polynomial exponents. -/
abbrev operatorExponentEquiv (d : ℕ) :
    Sym (Fin (n + 1)) d ≃ {s : Fin (n + 1) →₀ ℕ // s.degree = d} :=
  exponentEquiv (n + 1) d

/-- The actual exponent vector of a finite symmetric index. -/
def operatorExponent (d : ℕ) (s : Sym (Fin (n + 1)) d) : Fin (n + 1) →₀ ℕ :=
  (operatorExponentEquiv d s).val

@[simp] theorem operatorExponent_degree (d : ℕ) (s : Sym (Fin (n + 1)) d) :
    (operatorExponent d s).degree = d := (operatorExponentEquiv d s).property

theorem operatorExponent_injective (d : ℕ) :
    Function.Injective (operatorExponent (n := n) d) := by
  intro i j h
  apply (operatorExponentEquiv d).injective
  exact Subtype.ext h

/-- The homogeneous monomial in the shared finite exponent coordinates. -/
theorem formsBasis_val_tensorExponent (d : ℕ) (s : Sym (Fin (n + 1)) d) :
    (formsBasis K (n + 1) d s).val = monomial (operatorExponent d s) 1 := by
  simpa only [operatorExponent, operatorExponentEquiv]
    using formsBasis_val_monomial K (n + 1) d s

/-- Apply the coefficient operators after the actual partial
derivatives of the synthesized monomials. -/
def operatorDifferential (T : Fin (n + 1) → V →ₗ[K] W) (t : ℕ) :
    (Sym (Fin (n + 1)) (t + 1) → V) →ₗ[K] (Sym (Fin (n + 1)) t → W) :=
  LinearMap.pi fun s => ∑ b : Sym (Fin (n + 1)) (t + 1), ∑ i : Fin (n + 1),
    (pderiv i (monomial (operatorExponent (t + 1) b) 1 : Poly K (n + 1))).coeff
        (operatorExponent t s) • (T i).comp (LinearMap.proj b)

@[simp] theorem operatorDifferential_coeff (T : Fin (n + 1) → V →ₗ[K] W) (t : ℕ)
    (x : Sym (Fin (n + 1)) (t + 1) → V) (s : Sym (Fin (n + 1)) t) :
    operatorDifferential T t x s = ∑ b : Sym (Fin (n + 1)) (t + 1), ∑ i : Fin (n + 1),
      (pderiv i (monomial (operatorExponent (t + 1) b) 1 : Poly K (n + 1))).coeff
          (operatorExponent t s) • T i (x b) := by
  simp only [operatorDifferential, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- The entries of the genuine linear-form matrix are the transposed
coefficients of the operators, in the given coefficient-module bases. -/
def operatorLinearMatrix (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin (n + 1) → V →ₗ[K] W) : LinearMatrix K n a c := fun k j =>
  ∑ i : Fin (n + 1), (bW.repr (T i (bV k)) j) • (⟨X i, isHomogeneous_X K i⟩ : Forms K (n + 1) 1)

@[simp] theorem operatorLinearMatrix_val (bV : Basis (Fin a) K V)
    (bW : Basis (Fin c) K W) (T : Fin (n + 1) → V →ₗ[K] W) (k : Fin a) (j : Fin c) :
    (operatorLinearMatrix bV bW T k j).val =
      ∑ i : Fin (n + 1), C (bW.repr (T i (bV k)) j) * X i := by
  simp [operatorLinearMatrix, smul_eq_C_mul]

/-- Read one literal coefficient of one component of a homogeneous vector. -/
def polynomialVectorCoefficient {d : ℕ} (k : Fin a) (s : Fin (n + 1) →₀ ℕ) :
    (Fin a → Forms K (n + 1) d) →ₗ[K] K :=
  (lcoeff K s).comp ((Forms K (n + 1) d).subtype.comp (LinearMap.proj k))

@[simp] theorem polynomialVectorCoefficient_apply {d : ℕ} (k : Fin a)
    (s : Fin (n + 1) →₀ ℕ) (g : Fin a → Forms K (n + 1) d) :
    polynomialVectorCoefficient k s g = (g k).val.coeff s := rfl

/-- The factorial coefficient pairing identifies module-valued homogeneous
coefficients with the dual of a genuine polynomial vector space. -/
def operatorFactorialDualMap (b : Basis (Fin a) K V) (d : ℕ) :
    (Sym (Fin (n + 1)) d → V) →ₗ[K] Module.Dual K (Fin a → Forms K (n + 1) d) where
  toFun x := ∑ s : Sym (Fin (n + 1)) d, ∑ k : Fin a,
    (factorialWeight K (operatorExponent d s) * b.repr (x s) k) •
      polynomialVectorCoefficient k (operatorExponent d s)
  map_add' x y := by
    simp [map_add, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' q x := by
    simp [map_smul, Finset.smul_sum, smul_smul, smul_eq_mul, mul_left_comm]

@[simp] theorem operatorFactorialDualMap_apply (b : Basis (Fin a) K V) (d : ℕ)
    (x : Sym (Fin (n + 1)) d → V) (g : Fin a → Forms K (n + 1) d) :
    operatorFactorialDualMap (n := n) b d x g = ∑ s : Sym (Fin (n + 1)) d, ∑ k : Fin a,
      factorialWeight K (operatorExponent d s) * b.repr (x s) k *
        (g k).val.coeff (operatorExponent d s) := by
  simp [operatorFactorialDualMap, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

/-- Testing the pairing on a single coefficient-one monomial reads precisely
one module coordinate, multiplied by its nonzero factorial. -/
@[simp] theorem operatorFactorialDualMap_single_basis
    (b : Basis (Fin a) K V) (d : ℕ) (x : Sym (Fin (n + 1)) d → V)
    (k : Fin a) (s : Sym (Fin (n + 1)) d) :
    operatorFactorialDualMap (n := n) b d x (Pi.single k (formsBasis K (n + 1) d s)) =
      factorialWeight K (operatorExponent d s) * b.repr (x s) k := by
  classical
  rw [operatorFactorialDualMap_apply]
  calc
    _ = ∑ q : Sym (Fin (n + 1)) d,
        factorialWeight K (operatorExponent d q) * b.repr (x q) k *
          (formsBasis K (n + 1) d s).val.coeff (operatorExponent d q) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_eq_single k]
      · simp only [Pi.single_eq_same]
      · intro j _ hj
        simp [hj]
      · simp
    _ = _ := by
      simp [formsBasis_val_tensorExponent, coeff_monomial,
        (operatorExponent_injective d).eq_iff]

theorem operatorFactorialDualMap_injective [CharZero K]
    (b : Basis (Fin a) K V) (d : ℕ) :
    Function.Injective (operatorFactorialDualMap (n := n) b d) := by
  intro x y h
  funext s
  apply b.repr.injective
  ext k
  have htest := congrArg (fun f => f (Pi.single k (formsBasis K (n + 1) d s))) h
  simp only [operatorFactorialDualMap_single_basis] at htest
  exact mul_left_cancel₀ (factorialWeight_ne_zero K _) htest

/-- This pairing is a concrete perfect pairing in characteristic zero. -/
def operatorFactorialDual [CharZero K] (b : Basis (Fin a) K V) (d : ℕ) :
    (Sym (Fin (n + 1)) d → V) ≃ₗ[K] Module.Dual K (Fin a → Forms K (n + 1) d) := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  apply LinearMap.linearEquivOfInjective (operatorFactorialDualMap (n := n) b d)
    (operatorFactorialDualMap_injective b d)
  rw [Subspace.dual_finrank_eq]
  simp [Module.finrank_pi_fintype, Module.finrank_eq_card_basis b,
    Module.finrank_eq_card_basis (formsBasis K (n + 1) d), mul_comm]

@[simp] theorem operatorFactorialDual_apply [CharZero K] (b : Basis (Fin a) K V)
    (d : ℕ) (x : Sym (Fin (n + 1)) d → V) :
    operatorFactorialDual (n := n) b d x = operatorFactorialDualMap (n := n) b d x := rfl

@[simp] theorem operatorDifferential_single (T : Fin (n + 1) → V →ₗ[K] W) (t : ℕ)
    (b : Sym (Fin (n + 1)) (t + 1)) (v : V) (s : Sym (Fin (n + 1)) t) :
    operatorDifferential T t (Pi.single b v) s = ∑ i : Fin (n + 1),
      (pderiv i (monomial (operatorExponent (t + 1) b) 1 : Poly K (n + 1))).coeff
        (operatorExponent t s) • T i v := by
  classical
  rw [operatorDifferential_coeff, Finset.sum_eq_single b]
  · simp only [Pi.single_eq_same]
  · intro q _ hq
    simp [hq]
  · simp

@[simp] theorem operatorDifferential_single_repr (bW : Basis (Fin c) K W)
    (T : Fin (n + 1) → V →ₗ[K] W) (t : ℕ) (b : Sym (Fin (n + 1)) (t + 1))
    (v : V) (s : Sym (Fin (n + 1)) t) (j : Fin c) :
    bW.repr (operatorDifferential T t (Pi.single b v) s) j = ∑ i : Fin (n + 1),
      (pderiv i (monomial (operatorExponent (t + 1) b) 1 : Poly K (n + 1))).coeff
        (operatorExponent t s) * bW.repr (T i v) j := by
  rw [operatorDifferential_single]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

@[simp] theorem operatorFactorialDualMap_single_module_basis
    (b : Basis (Fin a) K V) (d : ℕ) (s : Sym (Fin (n + 1)) d)
    (k : Fin a) (g : Fin a → Forms K (n + 1) d) :
    operatorFactorialDualMap (n := n) b d (Pi.single s (b k)) g =
      factorialWeight K (operatorExponent d s) *
        (g k).val.coeff (operatorExponent d s) := by
  classical
  rw [operatorFactorialDualMap_apply, Finset.sum_eq_single s]
  · simp [Pi.single_eq_same, Basis.repr_self, Finsupp.single_apply]
  · intro q _ hq
    simp [hq]
  · simp

/-- Literal multiplication coefficients of the transposed operator matrix. -/
theorem operatorLinearMatrix_mul_single_coeff
    (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin (n + 1) → V →ₗ[K] W) (t : ℕ) (j : Fin c) (s : Sym (Fin (n + 1)) t)
    (k : Fin a) (b : Sym (Fin (n + 1)) (t + 1)) :
    (linearMatrixMap (operatorLinearMatrix bV bW T) t
      (Pi.single j (formsBasis K (n + 1) t s)) k).val.coeff
        (operatorExponent (t + 1) b) = ∑ i : Fin (n + 1),
      bW.repr (T i (bV k)) j *
        (X i * monomial (operatorExponent t s) 1 : Poly K (n + 1)).coeff
          (operatorExponent (t + 1) b) := by
  classical
  have hval : (linearMatrixMap (operatorLinearMatrix bV bW T) t
      (Pi.single j (formsBasis K (n + 1) t s)) k).val =
      (operatorLinearMatrix bV bW T k j).val * (formsBasis K (n + 1) t s).val := by
    rw [linearMatrixMap_val, Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same]
    · intro l _ hl
      simp [hl]
    · simp
  rw [hval]
  rw [operatorLinearMatrix_val, formsBasis_val_tensorExponent, Finset.sum_mul, coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, coeff_C_mul]

/-- The actual differential and actual polynomial matrix are adjoint under
the concrete factorial pairing. This is the coefficient transpose theorem. -/
theorem operatorFactorialDual_adjoint [CharZero K]
    (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin (n + 1) → V →ₗ[K] W) (t : ℕ) :
    (operatorFactorialDual (n := n) bW t).toLinearMap.comp (operatorDifferential T t) =
      (linearMatrixMap (operatorLinearMatrix bV bW T) t).dualMap.comp
        (operatorFactorialDual (n := n) bV (t + 1)).toLinearMap := by
  classical
  apply LinearMap.pi_ext'
  intro b
  apply bV.ext
  intro k
  apply LinearMap.pi_ext'
  intro j
  apply (formsBasis K (n + 1) t).ext
  intro s
  change operatorFactorialDualMap (n := n) bW t
      (operatorDifferential T t (Pi.single b (bV k))) (Pi.single j (formsBasis K (n + 1) t s)) =
    operatorFactorialDualMap (n := n) bV (t + 1) (Pi.single b (bV k))
      (linearMatrixMap (operatorLinearMatrix bV bW T) t (Pi.single j (formsBasis K (n + 1) t s)))
  rw [operatorFactorialDualMap_single_basis, operatorFactorialDualMap_single_module_basis,
    operatorDifferential_single_repr, operatorLinearMatrix_mul_single_coeff,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (factorialWeight K (operatorExponent t s) *
        (pderiv i (monomial (operatorExponent (t + 1) b) 1 : Poly K (n + 1))).coeff
          (operatorExponent t s)) * bW.repr (T i (bV k)) j := by ring
    _ = (factorialWeight K (operatorExponent (t + 1) b) *
        (X i * monomial (operatorExponent t s) 1 : Poly K (n + 1)).coeff
          (operatorExponent (t + 1) b)) * bW.repr (T i (bV k)) j := by
      rw [factorialWeight_pderiv_monomial_pair]
    _ = _ := by ring

theorem operatorDifferential_injective_iff_linearMatrixMap_surjective [CharZero K]
    (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin (n + 1) → V →ₗ[K] W) (t : ℕ) :
    Function.Injective (operatorDifferential T t) ↔
      Function.Surjective (linearMatrixMap (operatorLinearMatrix bV bW T) t) := by
  let S := operatorFactorialDual (n := n) bV (t + 1)
  let E := operatorFactorialDual (n := n) bW t
  let F := linearMatrixMap (operatorLinearMatrix bV bW T) t
  have hadj (x : Sym (Fin (n + 1)) (t + 1) → V) : E (operatorDifferential T t x) = F.dualMap (S x) :=
    LinearMap.congr_fun (operatorFactorialDual_adjoint bV bW T t) x
  constructor
  · intro hD
    apply LinearMap.dualMap_injective_iff.mp
    intro f g hfg
    obtain ⟨x, rfl⟩ := S.surjective f
    obtain ⟨y, rfl⟩ := S.surjective g
    have hxy : operatorDifferential T t x = operatorDifferential T t y :=
      E.injective (by rw [hadj, hadj]; exact hfg)
    exact congrArg S (hD hxy)
  · intro hF x y hxy
    apply S.injective
    apply (LinearMap.dualMap_injective_iff.mpr hF)
    rw [← hadj, ← hadj, hxy]

theorem operatorDifferential_surjective_iff_linearMatrixMap_injective [CharZero K]
    (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin (n + 1) → V →ₗ[K] W) (t : ℕ) :
    Function.Surjective (operatorDifferential T t) ↔
      Function.Injective (linearMatrixMap (operatorLinearMatrix bV bW T) t) := by
  let S := operatorFactorialDual (n := n) bV (t + 1)
  let E := operatorFactorialDual (n := n) bW t
  let F := linearMatrixMap (operatorLinearMatrix bV bW T) t
  have hadj (x : Sym (Fin (n + 1)) (t + 1) → V) : E (operatorDifferential T t x) = F.dualMap (S x) :=
    LinearMap.congr_fun (operatorFactorialDual_adjoint bV bW T t) x
  constructor
  · intro hD
    apply LinearMap.dualMap_surjective_iff.mp
    intro g
    obtain ⟨z, hz⟩ := E.surjective g
    obtain ⟨x, hx⟩ := hD z
    refine ⟨S x, ?_⟩
    rw [← hadj, hx, hz]
  · intro hF z
    obtain ⟨g, hg⟩ := (LinearMap.dualMap_surjective_iff.mpr hF) (E z)
    obtain ⟨x, rfl⟩ := S.surjective g
    refine ⟨x, E.injective ?_⟩
    rw [hadj, hg]

/-- Add one occurrence of an auxiliary variable to a homogeneous monomial
index. The exponent vector remains independent of the coefficient field. -/
def operatorRaisedIndex (t : ℕ) (s : Sym (Fin (n + 1)) t) (i : Fin (n + 1)) :
    Sym (Fin (n + 1)) (t + 1) :=
  (operatorExponentEquiv (t + 1)).symm
    ⟨operatorExponent t s + Finsupp.single i 1, by
      simp only [map_add, operatorExponent_degree, Finsupp.degree_single]⟩

@[simp] theorem operatorRaisedIndex_exponent (t : ℕ) (s : Sym (Fin (n + 1)) t) (i : Fin (n + 1)) :
    operatorExponent (t + 1) (operatorRaisedIndex t s i) =
      operatorExponent t s + Finsupp.single i 1 := by
  simp [operatorRaisedIndex, operatorExponent]

/-- The differential has exactly the usual partial-derivative coefficient
recurrence, expressed in the finite homogeneous monomial indices. -/
theorem operatorDifferential_apply (T : Fin (n + 1) → V →ₗ[K] W) (t : ℕ)
    (x : Sym (Fin (n + 1)) (t + 1) → V) (s : Sym (Fin (n + 1)) t) :
    operatorDifferential T t x s = ∑ i : Fin (n + 1),
      (((operatorExponent t s) i + 1 : ℕ) : K) •
        T i (x (operatorRaisedIndex t s i)) := by
  classical
  rw [operatorDifferential_coeff, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coeff_pderiv, coeff_monomial]
  rw [← operatorRaisedIndex_exponent t s i]
  simp only [(operatorExponent_injective (t + 1)).eq_iff, ite_mul,
    one_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Nat.cast_add, Nat.cast_one]

end Steiner
