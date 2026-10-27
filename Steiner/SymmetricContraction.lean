module

public import Steiner.Homogeneous
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

@[expose] public section

/-!
# Symmetric powers of a split directional derivative kernel

An invertible linear change of auxiliary variables sends a unimodular directional
partial derivative to one coordinate derivative. Its kernel is the remaining-variable
polynomial module, including after tensoring with an arbitrary coefficient module.
The integration identity is explicit, so no flatness assumption is involved.
-/

noncomputable section
namespace Steiner.SymmetricContraction
open MvPolynomial
open scoped TensorProduct

variable {n : ℕ} {R : Type*} [CommRing R]
abbrev Aux (n : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Fin (n + 1)) R
abbrev KernelPoly (n : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Fin n) R

/-- The linear auxiliary polynomial with coefficient vector `v`. -/
def linearForm (v : Fin (n + 1) → R) : Aux n R := ∑ i, C (v i) * X i

/-- Substitution by the rows of a matrix. -/
def linearChange (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Aux n R →ₐ[R] Aux n R :=
  aeval (fun i => linearForm (A i))

@[simp] theorem linearChange_X (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) :
    linearChange A (X i) = linearForm (A i) := by simp [linearChange]

@[simp] theorem linearChange_C (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r : R) :
    linearChange A (C r) = C r := by simp [linearChange]

@[simp] theorem linearForm_one_row (i : Fin (n + 1)) :
    linearForm ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i) = X i := by
  classical
  simp [linearForm, Matrix.one_apply]

theorem linearChange_linearForm (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (v : Fin (n + 1) → R) :
    linearChange A (linearForm v) = linearForm (fun k => ∑ j, v j * A j k) := by
  classical
  simp only [linearForm, map_sum, map_mul, linearChange_C, linearChange_X,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext k
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem linearChange_comp (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (linearChange A).comp (linearChange B) = linearChange (B * A) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, linearChange_X, linearChange_linearForm]
  rfl

@[simp] theorem linearChange_one :
    linearChange (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = AlgHom.id R (Aux n R) := by
  ext i
  simp

/-- An invertible linear auxiliary coordinate transformation. -/
def linearChangeEquiv (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hAB : A * B = 1) (hBA : B * A = 1) : Aux n R ≃ₐ[R] Aux n R :=
  AlgEquiv.ofAlgHom (linearChange A) (linearChange B)
    (by rw [linearChange_comp, hBA, linearChange_one])
    (by rw [linearChange_comp, hAB, linearChange_one])

/-- Directional differentiation with coefficient vector `f`. -/
def directional (f : Fin (n + 1) → R) : Derivation R (Aux n R) (Aux n R) :=
  mkDerivation R (fun i => C (f i))

@[simp] theorem directional_X (f : Fin (n + 1) → R) (i : Fin (n + 1)) :
    directional f (X i) = C (f i) := by simp [directional]

@[simp] theorem directional_C (f : Fin (n + 1) → R) (r : R) :
    directional f (C r) = 0 := by simp

theorem directional_eq_sum (f : Fin (n + 1) → R) :
    directional f = ∑ i, f i • pderiv i := by
  classical
  apply derivation_ext
  intro j
  simp [directional, Pi.single_apply]
  exact C_eq_smul_one


@[simp] theorem directional_linearForm (f v : Fin (n + 1) → R) :
    directional f (linearForm v) = C (∑ i, f i * v i) := by
  calc
    directional f (linearForm v) = ∑ i, C (v i) * C (f i) := by
      simp [linearForm, Derivation.leibniz, smul_eq_mul]
    _ = C (∑ i, f i * v i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← map_mul, mul_comm]

/-- Chain rule in coordinates whose first row is a lift and other rows lie in the kernel. -/
theorem directional_linearChange (f : Fin (n + 1) → R)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    (P : Aux n R) :
    directional f (linearChange A P) = linearChange A (pderiv 0 P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, Derivation.leibniz, linearChange_X, directional_linearForm,
      hA, pderiv_X, Pi.single_apply, map_add, smul_eq_mul, hP]
    split_ifs <;> simp [mul_comm]

/-- Set the first variable to zero and retain the remaining variables. -/
def kernelRestriction : Aux n R →ₐ[R] KernelPoly n R :=
  aeval (Fin.cases 0 X)

/-- Include the n kernel-coordinate variables as the last n ambient variables. -/
def kernelEmbeddingBase : KernelPoly n R →ₐ[R] Aux n R := rename Fin.succ

@[simp] theorem kernelRestriction_embedding (P : KernelPoly n R) :
    kernelRestriction (kernelEmbeddingBase P) = P := by
  have h : kernelRestriction.comp kernelEmbeddingBase = AlgHom.id R (KernelPoly n R) := by
    ext i
    simp [kernelRestriction, kernelEmbeddingBase]
  exact congrArg (fun h : KernelPoly n R →ₐ[R] KernelPoly n R => h P) h

/-- The projection onto polynomials independent of the first variable. -/
def zeroFirst : Aux n R →ₗ[R] Aux n R :=
  kernelEmbeddingBase.toLinearMap.comp kernelRestriction.toLinearMap

@[simp] theorem zeroFirst_monomial (s : Fin (n + 1) →₀ ℕ) (r : R) :
    zeroFirst (monomial s r) = if s 0 = 0 then monomial s r else 0 := by
  classical
  have hcomp : kernelEmbeddingBase.comp kernelRestriction =
      (aeval (fun i : Fin (n + 1) => if i = 0 then 0 else X i) : Aux n R →ₐ[R] Aux n R) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [kernelEmbeddingBase, kernelRestriction]
    · simp only [AlgHom.comp_apply, kernelRestriction, aeval_X]
      change rename Fin.succ (X j : KernelPoly n R) = X j.succ
      simp
  change (kernelEmbeddingBase.comp kernelRestriction) (monomial s r) = _
  rw [hcomp]
  rw [aeval_def, eval₂_monomial, Finsupp.prod_fintype]
  swap
  · simp
  change C r * (∏ i : Fin (n + 1), (if i = 0 then 0 else X i) ^ s i) = _
  by_cases hs : s 0 = 0
  · rw [ite_eq_left hs, MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    swap
    · simp
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp [hs]
    · simp [hi0]
  · rw [ite_eq_right hs]
    have hz : (∏ i : Fin (n + 1), (if i = 0 then 0 else (X i : Aux n R)) ^ s i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n + 1)))
      simp [zero_pow hs]
    rw [hz, mul_zero]

section Integration
variable {K : Type*} [Field K] [CharZero K] [Algebra K R]

/-- Formal integration in the first variable, with zero constant term. -/
def integrateFirst : Aux n R →ₗ[R] Aux n R :=
  (basisMonomials (Fin (n + 1)) R).constr R (fun s =>
    algebraMap K R (((s 0 + 1 : ℕ) : K)⁻¹) • monomial (s + Finsupp.single 0 1) 1)

omit [CharZero K] in
@[simp] theorem integrateFirst_monomial (s : Fin (n + 1) →₀ ℕ) (r : R) :
    integrateFirst (K := K) (monomial s r) =
      monomial (s + Finsupp.single 0 1)
        (r * algebraMap K R (((s 0 + 1 : ℕ) : K)⁻¹)) := by
  have hb := (basisMonomials (Fin (n + 1)) R).constr_basis R
    (fun t => algebraMap K R (((t 0 + 1 : ℕ) : K)⁻¹) •
      (monomial (t + Finsupp.single 0 1) 1 : Aux n R)) s
  change integrateFirst (K := K) (monomial s 1) = _ at hb
  have hr : monomial s r = r • (monomial s 1 : Aux n R) := by simp [smul_monomial]
  rw [hr, map_smul, hb, smul_smul, smul_monomial]
  simp

/-- Integration splits the derivative: the only missing term is the remaining-variable projection. -/
theorem integrateFirst_pderiv_add_zeroFirst (P : Aux n R) :
    integrateFirst (K := K) (pderiv 0 P) + zeroFirst P = P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add]
    rw [add_add_add_comm, hP, hQ]
  | monomial s r =>
    rw [pderiv_monomial, integrateFirst_monomial, zeroFirst_monomial]
    by_cases hs : s 0 = 0
    · simp [hs]
    · rw [ite_eq_right hs, add_zero]
      have hle : Finsupp.single (0 : Fin (n + 1)) 1 ≤ s :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hs)
      have hexp : s - Finsupp.single 0 1 + Finsupp.single 0 1 = s :=
        tsub_add_cancel_of_le hle
      have hn : (s - Finsupp.single (0 : Fin (n + 1)) 1 : Fin (n + 1) →₀ ℕ) 0 + 1 = s 0 := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      rw [hexp, hn]
      congr 1
      have hcast : (s 0 : K) ≠ 0 := Nat.cast_ne_zero.mpr hs
      calc
        (r * (s 0 : R)) * algebraMap K R ((s 0 : K)⁻¹) =
            r * algebraMap K R ((s 0 : K) * (s 0 : K)⁻¹) := by
          rw [map_mul, map_natCast]
          ring
        _ = r := by rw [mul_inv_cancel₀ hcast, map_one, mul_one]

/-- The scalar splitting identity as an equality of linear maps. -/
theorem first_derivative_split :
    (integrateFirst (K := K)).comp (pderiv (R := R) (0 : Fin (n + 1))).toLinearMap +
      zeroFirst = LinearMap.id := by
  apply LinearMap.ext
  intro P
  exact integrateFirst_pderiv_add_zeroFirst (K := K) P

/-- Differentiating the explicit zero-constant integral returns the original polynomial. -/
@[simp] theorem pderiv_integrateFirst (P : Aux n R) :
    pderiv (0 : Fin (n + 1)) (integrateFirst (K := K) P) = P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial s r =>
    rw [integrateFirst_monomial, pderiv_monomial]
    have he : s + Finsupp.single (0 : Fin (n + 1)) 1 - Finsupp.single 0 1 = s :=
      add_tsub_cancel_right _ _
    rw [he]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    congr 1
    have hn : (((s 0 + 1 : ℕ) : K)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    calc
      (r * algebraMap K R (((s 0 + 1 : ℕ) : K)⁻¹)) * ((s 0 + 1 : ℕ) : R) =
          r * algebraMap K R ((((s 0 + 1 : ℕ) : K)⁻¹) * ((s 0 + 1 : ℕ) : K)) := by
        rw [map_mul, map_natCast]
        ring
      _ = r := by rw [inv_mul_cancel₀ hn, map_one, mul_one]

omit [CharZero K] in
/-- Integration raises the homogeneous degree by one. -/
theorem integrateFirst_homogeneous {d : ℕ} {P : Aux n R}
    (hP : P.IsHomogeneous d) : (integrateFirst (K := K) P).IsHomogeneous (d + 1) := by
  classical
  rw [P.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro s hs
  rw [integrateFirst_monomial]
  apply isHomogeneous_monomial
  have hsdeg : s.degree = d := by
    simpa only [Finsupp.degree_apply] using (hP.degree_eq_sum_deg_support hs).symm
  simp [map_add, hsdeg]

end Integration

/-- The embedded remaining-variable polynomials have zero first partial derivative. -/
@[simp] theorem pderiv_kernelEmbeddingBase (P : KernelPoly n R) :
    pderiv (0 : Fin (n + 1)) (kernelEmbeddingBase P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [kernelEmbeddingBase]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    have hx : kernelEmbeddingBase (X i : KernelPoly n R) = (X i.succ : Aux n R) := by simp [kernelEmbeddingBase]
    rw [map_mul, pderiv_mul, hP, hx, zero_mul, zero_add,
      pderiv_X_of_ne (Fin.succ_ne_zero i), mul_zero]

section Tensor
variable {K : Type*} [Field K] [CharZero K] [Algebra K R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Auxiliary polynomials with arbitrary module coefficients. -/
abbrev AuxTensor := Aux n R ⊗[R] M
/-- KernelPoly auxiliary polynomials with arbitrary module coefficients. -/
abbrev KernelTensor := KernelPoly n R ⊗[R] M

/-- A directional partial derivative on module-valued auxiliary polynomials. -/
def tensorDirectional (f : Fin (n + 1) → R) : AuxTensor (n := n) (R := R) (M := M) →ₗ[R] AuxTensor (n := n) (R := R) (M := M) :=
  (directional f).toLinearMap.rTensor M

def tensorKernelEmbedding : KernelTensor (n := n) (R := R) (M := M) →ₗ[R] AuxTensor (n := n) (R := R) (M := M) :=
  kernelEmbeddingBase.toLinearMap.rTensor M

def tensorKernelRestriction : AuxTensor (n := n) (R := R) (M := M) →ₗ[R] KernelTensor (n := n) (R := R) (M := M) :=
  kernelRestriction.toLinearMap.rTensor M

@[simp] theorem tensorKernelRestriction_embedding (P : KernelTensor (n := n) (R := R) (M := M)) :
    tensorKernelRestriction (tensorKernelEmbedding P) = P := by
  have h : tensorKernelRestriction.comp tensorKernelEmbedding =
      (LinearMap.id : KernelTensor (n := n) (R := R) (M := M) →ₗ[R] KernelTensor (n := n) (R := R) (M := M)) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro P
    apply LinearMap.ext
    intro m
    simp [tensorKernelRestriction, tensorKernelEmbedding]
  exact LinearMap.congr_fun h P

theorem tensorKernelEmbedding_injective :
    Function.Injective (tensorKernelEmbedding (n := n) (R := R) (M := M)) := by
  intro P Q h
  simpa using congrArg (tensorKernelRestriction (n := n) (R := R) (M := M)) h

/-- Tensoring the explicit integration splitting requires no flatness assumption. -/
theorem tensor_first_derivative_split (P : AuxTensor (n := n) (R := R) (M := M)) :
    (integrateFirst (K := K)).rTensor M ((pderiv (R := R) (0 : Fin (n + 1))).toLinearMap.rTensor M P) +
      tensorKernelEmbedding (tensorKernelRestriction P) = P := by
  have h := congrArg (fun L : Aux n R →ₗ[R] Aux n R => L.rTensor M)
    (first_derivative_split (K := K) (R := R))
  simp only [LinearMap.rTensor_add, LinearMap.rTensor_comp, LinearMap.rTensor_id] at h
  have hP := LinearMap.congr_fun h P
  simpa [zeroFirst, tensorKernelEmbedding, tensorKernelRestriction,
    LinearMap.rTensor_comp] using hP

include K

/-- The kernel of the first derivative is exactly the remaining-variable module, with unique coordinates. -/
theorem tensor_pderiv_kernel (P : AuxTensor (n := n) (R := R) (M := M)) :
    (pderiv (R := R) (0 : Fin (n + 1))).toLinearMap.rTensor M P = 0 ↔
      ∃! Q : KernelTensor (n := n) (R := R) (M := M), tensorKernelEmbedding Q = P := by
  have hz : ((pderiv (R := R) (0 : Fin (n + 1))).toLinearMap.rTensor M).comp
      tensorKernelEmbedding = 0 := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro Q
    apply LinearMap.ext
    intro m
    simp [tensorKernelEmbedding]
  constructor
  · intro hP
    have hsplit := tensor_first_derivative_split (K := K) P
    rw [hP, map_zero, zero_add] at hsplit
    exact ⟨tensorKernelRestriction P, hsplit, fun Q hQ =>
      tensorKernelEmbedding_injective (hQ.trans hsplit.symm)⟩
  · rintro ⟨Q, rfl, hQ⟩
    exact LinearMap.congr_fun hz Q

/-- The remaining-variable kernel embedding after an invertible coordinate transformation. -/
def kernelEmbedding (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    KernelTensor (n := n) (R := R) (M := M) →ₗ[R] AuxTensor (n := n) (R := R) (M := M) :=
  ((linearChange A).toLinearMap.rTensor M).comp tensorKernelEmbedding

/-- The directional kernel is the symmetric algebra on the kernel coordinates.
The first row of `A` is a unimodular lift, the last n rows are the kernel basis. -/
theorem tensor_directional_kernel
    (f : Fin (n + 1) → R) (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    (P : AuxTensor (n := n) (R := R) (M := M)) :
    tensorDirectional f P = 0 ↔
      ∃! Q : KernelTensor (n := n) (R := R) (M := M), kernelEmbedding A Q = P := by
  let E := (linearChangeEquiv A B hAB hBA).toLinearEquiv.rTensor M
  have hchain : (tensorDirectional f).comp E.toLinearMap =
      E.toLinearMap.comp ((pderiv (R := R) (0 : Fin (n + 1))).toLinearMap.rTensor M) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro Q
    apply LinearMap.ext
    intro m
    change directional f (linearChange A Q) ⊗ₜ[R] m =
      linearChange A (pderiv 0 Q) ⊗ₜ[R] m
    rw [directional_linearChange f A hA]
  have hemb : ∀ Q, kernelEmbedding A Q = E (tensorKernelEmbedding Q) := by
    intro Q
    rfl
  have hker : tensorDirectional f P = 0 ↔
      (pderiv (R := R) (0 : Fin (n + 1))).toLinearMap.rTensor M (E.symm P) = 0 := by
    have hc := LinearMap.congr_fun hchain (E.symm P)
    simp only [LinearMap.comp_apply] at hc
    change tensorDirectional f (E (E.symm P)) =
      E ((pderiv (R := R) (0 : Fin (n + 1))).toLinearMap.rTensor M (E.symm P)) at hc
    rw [E.apply_symm_apply] at hc
    rw [hc]
    exact E.map_eq_zero_iff
  rw [hker, tensor_pderiv_kernel (K := K)]
  constructor
  · rintro ⟨Q, hQ, huniq⟩
    dsimp only at hQ huniq ⊢
    refine ⟨Q, ?_, ?_⟩
    · change kernelEmbedding A Q = P
      rw [hemb, hQ, E.apply_symm_apply]
    · intro Q' hQ'
      apply huniq
      apply E.injective
      rw [← hemb, hQ', E.apply_symm_apply]
  · rintro ⟨Q, hQ, huniq⟩
    dsimp only at hQ huniq ⊢
    refine ⟨Q, ?_, ?_⟩
    · apply E.injective
      rw [← hemb, hQ, E.apply_symm_apply]
    · intro Q' hQ'
      apply huniq
      rw [hemb, hQ', E.apply_symm_apply]

end Tensor

section Homogeneous
variable {σ τ : Type*}

/-- Any substitution by linear forms preserves homogeneous degree. -/
theorem linearSubstitution_homogeneous
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hφ : ∀ i, (φ (X i)).IsHomogeneous 1)
    {d : ℕ} {P : MvPolynomial σ R} (hP : P.IsHomogeneous d) :
    (φ P).IsHomogeneous d := by
  rw [aeval_unique φ]
  simpa only [one_mul] using hP.aeval (φ ∘ X) hφ

/-- Linear substitution commutes with extraction of every homogeneous component. -/
theorem linearSubstitution_homogeneousComponent
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hφ : ∀ i, (φ (X i)).IsHomogeneous 1)
    (d : ℕ) (P : MvPolynomial σ R) :
    homogeneousComponent d (φ P) = φ (homogeneousComponent d P) := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial s r =>
    have hp : (monomial s r : MvPolynomial σ R).IsHomogeneous s.degree :=
      isHomogeneous_monomial r rfl
    rw [homogeneousComponent_of_mem (linearSubstitution_homogeneous φ hφ hp),
      homogeneousComponent_of_mem hp]
    split_ifs <;> simp

@[simp] theorem linearForm_homogeneous (v : Fin (n + 1) → R) :
    (linearForm v).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun _i _ => isHomogeneous_C_mul_X _ _)

@[simp] theorem linearChange_homogeneous (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {d : ℕ} {P : Aux n R} (hP : P.IsHomogeneous d) :
    (linearChange A P).IsHomogeneous d :=
  linearSubstitution_homogeneous (linearChange A) (by intro i; simp) hP

theorem kernelRestriction_X_homogeneous (i : Fin (n + 1)) :
    (kernelRestriction (R := R) (X i)).IsHomogeneous 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [kernelRestriction] using (isHomogeneous_zero (σ := Fin n) R 1)
  · simpa [kernelRestriction] using (isHomogeneous_X R j)

theorem kernelEmbeddingBase_X_homogeneous (i : Fin n) :
    (kernelEmbeddingBase (R := R) (X i)).IsHomogeneous 1 := by
  simpa [kernelEmbeddingBase] using (isHomogeneous_X R i.succ)

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Homogeneous module-valued polynomials, expressed by the homogeneous projector. -/
def TensorHomogeneous (d : ℕ) (P : MvPolynomial σ R ⊗[R] M) : Prop :=
  (homogeneousComponent d).rTensor M P = P

/-- Linear auxiliary substitutions also preserve homogeneous degree for module coefficients. -/
theorem tensor_linearSubstitution_homogeneous
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hφ : ∀ i, (φ (X i)).IsHomogeneous 1)
    {d : ℕ} {P : MvPolynomial σ R ⊗[R] M} (hP : TensorHomogeneous d P) :
    TensorHomogeneous d (φ.toLinearMap.rTensor M P) := by
  have hc : (homogeneousComponent d).comp φ.toLinearMap =
      φ.toLinearMap.comp (homogeneousComponent d) := by
    apply LinearMap.ext
    intro Q
    exact linearSubstitution_homogeneousComponent φ hφ d Q
  have ht := congrArg (fun L : MvPolynomial σ R →ₗ[R] MvPolynomial τ R => L.rTensor M) hc
  rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp] at ht
  have htP := LinearMap.congr_fun ht P
  dsimp only [TensorHomogeneous, LinearMap.comp_apply] at hP ⊢
  simpa only [LinearMap.comp_apply, hP] using htP

/-- Read the remaining-variable coordinates using the inverse matrix. -/
def kernelCoordinates (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    AuxTensor (n := n) (R := R) (M := M) →ₗ[R] KernelTensor (n := n) (R := R) (M := M) :=
  tensorKernelRestriction.comp ((linearChange B).toLinearMap.rTensor M)

/-- The coordinates are unique because this map is a left inverse to the kernel embedding. -/
theorem kernelCoordinates_embedding (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hAB : A * B = 1) (Q : KernelTensor (n := n) (R := R) (M := M)) :
    kernelCoordinates B (kernelEmbedding A Q) = Q := by
  have hs : (kernelCoordinates (M := M) B).comp (kernelEmbedding A) = LinearMap.id := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro P
    apply LinearMap.ext
    intro m
    change kernelRestriction (linearChange B (linearChange A (kernelEmbeddingBase P))) ⊗ₜ[R] m =
      P ⊗ₜ[R] m
    have hab : linearChange B (linearChange A (kernelEmbeddingBase P)) = kernelEmbeddingBase P := by
      have h := congrArg (fun L : Aux n R →ₐ[R] Aux n R => L (kernelEmbeddingBase P))
        (linearChange_comp B A)
      simpa only [AlgHom.comp_apply, hAB, linearChange_one, AlgHom.id_apply] using h
    rw [hab, kernelRestriction_embedding]
  exact LinearMap.congr_fun hs Q

/-- The inverse-coordinate map preserves auxiliary homogeneous degree. -/
theorem kernelCoordinates_homogeneous (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {d : ℕ} {P : AuxTensor (n := n) (R := R) (M := M)} (hP : TensorHomogeneous d P) :
    TensorHomogeneous d (kernelCoordinates B P) := by
  exact tensor_linearSubstitution_homogeneous kernelRestriction
    kernelRestriction_X_homogeneous
    (tensor_linearSubstitution_homogeneous (linearChange B) (by intro i; simp) hP)

variable {K : Type*} [Field K] [CharZero K] [Algebra K R]
include K

/-- In each homogeneous degree the directional kernel is the symmetric power of
its n split kernel coordinates, with unique module-valued coefficients. -/
theorem tensor_directional_homogeneous_kernel
    (f : Fin (n + 1) → R) (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    {d : ℕ} (P : AuxTensor (n := n) (R := R) (M := M)) (hP : TensorHomogeneous d P) :
    tensorDirectional f P = 0 ↔
      ∃! Q : KernelTensor (n := n) (R := R) (M := M),
        TensorHomogeneous d Q ∧ kernelEmbedding A Q = P := by
  constructor
  · intro hD
    obtain ⟨Q, hQ, huniq⟩ := (tensor_directional_kernel (K := K) f A B hAB hBA hA P).mp hD
    dsimp only at hQ huniq
    have hcoord : kernelCoordinates B P = Q := by
      rw [← hQ]
      exact kernelCoordinates_embedding A B hAB Q
    refine ⟨Q, ⟨?_, hQ⟩, ?_⟩
    · rw [← hcoord]
      exact kernelCoordinates_homogeneous B hP
    · intro Q' hQ'
      exact huniq Q' hQ'.2
  · rintro ⟨Q, hQ, huniq⟩
    apply (tensor_directional_kernel (K := K) f A B hAB hBA hA P).mpr
    refine ⟨Q, hQ.2, ?_⟩
    intro Q' hQ'
    have hcoord : kernelCoordinates B P = Q' := by
      rw [← hQ']
      exact kernelCoordinates_embedding A B hAB Q'
    have hhom : TensorHomogeneous d Q' := by
      rw [← hcoord]
      exact kernelCoordinates_homogeneous B hP
    exact huniq Q' ⟨hhom, hQ'⟩

omit [CharZero K] in
/-- Integration commutes with homogeneous projection after shifting the degree. -/
theorem homogeneousComponent_integrateFirst (d : ℕ) (P : Aux n R) :
    homogeneousComponent (d + 1) (integrateFirst (K := K) P) =
      integrateFirst (K := K) (homogeneousComponent d P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial s r =>
    have hp : (monomial s r : Aux n R).IsHomogeneous s.degree :=
      isHomogeneous_monomial r rfl
    rw [homogeneousComponent_of_mem (integrateFirst_homogeneous (K := K) hp),
      homogeneousComponent_of_mem hp]
    by_cases hs : s.degree = d
    · simp [hs]
    · simp [Ne.symm hs]

/-- Formal integration remains a right inverse with arbitrary module coefficients. -/
@[simp] theorem tensor_pderiv_integrateFirst (P : AuxTensor (n := n) (R := R) (M := M)) :
    (pderiv (R := R) (0 : Fin (n + 1))).toLinearMap.rTensor M
      ((integrateFirst (K := K)).rTensor M P) = P := by
  have h : (pderiv (R := R) (0 : Fin (n + 1))).toLinearMap.comp
      (integrateFirst (K := K)) = LinearMap.id := by
    apply LinearMap.ext
    intro Q
    exact pderiv_integrateFirst (K := K) Q
  have ht := congrArg (fun L : Aux n R →ₗ[R] Aux n R => L.rTensor M) h
  rw [LinearMap.rTensor_comp, LinearMap.rTensor_id] at ht
  exact LinearMap.congr_fun ht P

omit [CharZero K] in
/-- The explicit right inverse raises homogeneous module-valued degree by one. -/
theorem tensor_integrateFirst_homogeneous {d : ℕ}
    {P : AuxTensor (n := n) (R := R) (M := M)} (hP : TensorHomogeneous d P) :
    TensorHomogeneous (d + 1) ((integrateFirst (K := K)).rTensor M P) := by
  have hc : (homogeneousComponent (d + 1) : Aux n R →ₗ[R] Aux n R).comp (integrateFirst (K := K) (n := n)) =
      (integrateFirst (K := K)).comp (homogeneousComponent d) := by
    apply LinearMap.ext
    intro Q
    exact homogeneousComponent_integrateFirst (K := K) d Q
  have ht := congrArg (fun L : Aux n R →ₗ[R] Aux n R => L.rTensor M) hc
  simp only [LinearMap.rTensor_comp] at ht
  have htP := LinearMap.congr_fun ht P
  dsimp only [TensorHomogeneous, LinearMap.comp_apply] at hP ⊢
  simpa only [LinearMap.comp_apply, hP] using htP

/-- A split nonzero linear contraction is surjective in each positive homogeneous degree. -/
theorem tensor_directional_homogeneous_surjective
    (f : Fin (n + 1) → R) (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    {d : ℕ} (P : AuxTensor (n := n) (R := R) (M := M)) (hP : TensorHomogeneous d P) :
    ∃ Q : AuxTensor (n := n) (R := R) (M := M),
      TensorHomogeneous (d + 1) Q ∧ tensorDirectional f Q = P := by
  let E := (linearChangeEquiv A B hAB hBA).toLinearEquiv.rTensor M
  have hchain : (tensorDirectional f).comp E.toLinearMap =
      E.toLinearMap.comp ((pderiv (R := R) (0 : Fin (n + 1))).toLinearMap.rTensor M) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro Q
    apply LinearMap.ext
    intro m
    change directional f (linearChange A Q) ⊗ₜ[R] m =
      linearChange A (pderiv 0 Q) ⊗ₜ[R] m
    rw [directional_linearChange f A hA]
  refine ⟨E ((integrateFirst (K := K)).rTensor M (E.symm P)), ?_, ?_⟩
  · change TensorHomogeneous (d + 1)
      ((linearChange A).toLinearMap.rTensor M
        ((integrateFirst (K := K)).rTensor M ((linearChange B).toLinearMap.rTensor M P)))
    apply tensor_linearSubstitution_homogeneous (linearChange A) (by intro i; simp)
    apply tensor_integrateFirst_homogeneous (K := K)
    exact tensor_linearSubstitution_homogeneous (linearChange B) (by intro i; simp) hP
  · have hc := LinearMap.congr_fun hchain
      ((integrateFirst (K := K)).rTensor M (E.symm P))
    simp only [LinearMap.comp_apply, tensor_pderiv_integrateFirst] at hc
    change tensorDirectional f (E ((integrateFirst (K := K)).rTensor M (E.symm P))) =
      E (E.symm P) at hc
    simpa only [E.apply_symm_apply] using hc

/-- The local split exact sequence for symmetric contraction, in actual homogeneous
polynomials with arbitrary module coefficients. It identifies the kernel with the
symmetric algebra on the n kernel coordinates and proves surjectivity, rather than
assuming exactness or a cohomological substitute. -/
theorem symmetric_contraction_exact
    (f : Fin (n + 1) → R) (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    (d : ℕ) :
    (∀ P : AuxTensor (n := n) (R := R) (M := M), TensorHomogeneous (d + 1) P →
      (tensorDirectional f P = 0 ↔
        ∃! Q : KernelTensor (n := n) (R := R) (M := M),
          TensorHomogeneous (d + 1) Q ∧ kernelEmbedding A Q = P)) ∧
    (∀ P : AuxTensor (n := n) (R := R) (M := M), TensorHomogeneous d P →
      ∃ Q : AuxTensor (n := n) (R := R) (M := M),
        TensorHomogeneous (d + 1) Q ∧ tensorDirectional f Q = P) := by
  exact ⟨fun P hP => tensor_directional_homogeneous_kernel (K := K) f A B hAB hBA hA P hP,
    fun P hP => tensor_directional_homogeneous_surjective (K := K) f A B hAB hBA hA P hP⟩

end Homogeneous

end Steiner.SymmetricContraction
