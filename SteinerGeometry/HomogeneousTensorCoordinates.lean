import Steiner.SymmetricContraction
import Steiner.OperatorDuality
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.FixedSubmodule

/-! Finite homogeneous coordinates for genuine module-valued polynomials.
Generalizes the earlier three-variable coordinate proof to every number of
variables. No freeness or flatness of the coefficient module is assumed. -/

noncomputable section
namespace SteinerGeometry.HomogeneousTensor
open MvPolynomial Steiner.SymmetricContraction
open scoped TensorProduct
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {σ : Type*}

/-- Coefficient identification for module-valued multivariate polynomials. -/
def tensorCoefficients : (MvPolynomial σ R ⊗[R] M) ≃ₗ[R] ((σ →₀ ℕ) →₀ M) := by
  classical
  exact (basisMonomials σ R).repr.rTensor M ≪≫ₗ
    TensorProduct.finsuppScalarLeft R M (σ →₀ ℕ)

@[simp] theorem tensorCoefficients_tmul (P : MvPolynomial σ R) (m : M) (s : σ →₀ ℕ) :
    tensorCoefficients (P ⊗ₜ[R] m) s = P.coeff s • m := by
  classical
  change TensorProduct.finsuppScalarLeft R M (σ →₀ ℕ)
    ((basisMonomials σ R).repr P ⊗ₜ[R] m) s = _
  rw [TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  rfl

@[simp] theorem tensorCoefficients_monomial (s : σ →₀ ℕ) (m : M) :
    tensorCoefficients ((monomial s 1 : MvPolynomial σ R) ⊗ₜ[R] m) =
      Finsupp.single s m := by
  classical
  ext t
  simp [coeff_monomial, Finsupp.single_apply, ite_smul]

@[simp] theorem tensorCoefficients_symm_single (s : σ →₀ ℕ) (m : M) :
    tensorCoefficients.symm (Finsupp.single s m) =
      (monomial s 1 : MvPolynomial σ R) ⊗ₜ[R] m := by
  apply tensorCoefficients.injective
  simp

/-- Finite tensor sums are read coefficientwise. -/
@[simp] theorem tensorCoefficients_sum {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ R ⊗[R] M) (α : σ →₀ ℕ) :
    tensorCoefficients (∑ j ∈ s, P j) α = ∑ j ∈ s, tensorCoefficients (P j) α := by
  simp only [map_sum, Finsupp.finsetSum_apply]

/-- Every module-valued polynomial is its finite sum of coefficient monomials. -/
theorem tensor_as_sum_monomials (P : MvPolynomial σ R ⊗[R] M) :
    P = (tensorCoefficients P).sum (fun s m => (monomial s 1) ⊗ₜ[R] m) := by
  have h : (tensorCoefficients P).sum (fun s m => Finsupp.single s m) =
      tensorCoefficients P := Finsupp.sum_single _
  apply_fun (tensorCoefficients (R := R) (M := M) (σ := σ)).symm at h
  simp only [Finsupp.sum, map_sum, tensorCoefficients_symm_single,
    LinearEquiv.symm_apply_apply] at h
  exact h.symm

/-- Homogeneous extraction keeps exactly the module coefficients of that degree. -/
theorem tensorCoefficients_component (n : ℕ) (P : MvPolynomial σ R ⊗[R] M)
    (s : σ →₀ ℕ) :
    tensorCoefficients ((homogeneousComponent n).rTensor M P) s =
      if s.degree = n then tensorCoefficients P s else 0 := by
  classical
  induction P using TensorProduct.inductionOn with
  | tmul P m => simp [coeff_homogeneousComponent, ite_smul]
  | add P Q hP hQ => simp [hP, hQ, ite_add_ite]

/-- Module-valued homogeneity is equivalently the expected support condition. -/
theorem tensorHomogeneous_iff_coefficients (n : ℕ) (P : MvPolynomial σ R ⊗[R] M) :
    TensorHomogeneous n P ↔ ∀ s : σ →₀ ℕ, s.degree ≠ n → tensorCoefficients P s = 0 := by
  constructor
  · intro hP s hs
    have h := congrArg (fun Q => tensorCoefficients Q s) hP
    rw [tensorCoefficients_component, ite_eq_right hs] at h
    exact h.symm
  · intro h
    apply tensorCoefficients.injective
    ext s
    rw [tensorCoefficients_component]
    split_ifs with hs
    · rfl
    · exact (h s hs).symm


variable {m : ℕ}

/-- Symmetric variable indices encode exactly the exponent vectors of degree `n`.
This equivalence depends on the indices alone, independently of the base ring. -/
def homogeneousTensorExponentEquiv (n : ℕ) :
    Sym (Fin m) n ≃ {s : Fin m →₀ ℕ // s.degree = n} :=
  Sym.equivNatSum (Fin m) n

/-- The exponent vector attached to one finite symmetric index. -/
def homogeneousTensorExponent (n : ℕ) (i : Sym (Fin m) n) : Fin m →₀ ℕ :=
  (homogeneousTensorExponentEquiv n i).val

@[simp] theorem homogeneousTensorExponent_degree (n : ℕ) (i : Sym (Fin m) n) :
    (homogeneousTensorExponent n i).degree = n :=
  (homogeneousTensorExponentEquiv n i).property

theorem homogeneousTensorExponent_injective (n : ℕ) :
    Function.Injective (homogeneousTensorExponent (m := m) n) := by
  intro i j h
  apply (homogeneousTensorExponentEquiv n).injective
  exact Subtype.ext h

theorem exists_homogeneousTensorExponent (n : ℕ) (s : Fin m →₀ ℕ)
    (hs : s.degree = n) : ∃ i : Sym (Fin m) n, homogeneousTensorExponent n i = s := by
  refine ⟨(homogeneousTensorExponentEquiv n).symm ⟨s,hs⟩, ?_⟩
  simp [homogeneousTensorExponent]

/-- The genuine submodule of tensors fixed by auxiliary degree-`n` extraction. -/
def homogeneousTensorSubmodule (n : ℕ) : Submodule R ((MvPolynomial (Fin m) R ⊗[R] M)) :=
  ((homogeneousComponent n).rTensor M).fixedSubmodule

@[simp] theorem mem_homogeneousTensorSubmodule (n : ℕ) (P : (MvPolynomial (Fin m) R ⊗[R] M)) :
    P ∈ homogeneousTensorSubmodule n ↔ TensorHomogeneous n P := Iff.rfl

/-- Read the finite degree-`n` coefficient vector from an actual tensor polynomial. -/
def homogeneousTensorCoefficientVector (n : ℕ) (P : (MvPolynomial (Fin m) R ⊗[R] M)) :
    Sym (Fin m) n → M := fun i => tensorCoefficients P (homogeneousTensorExponent n i)

/-- Coefficient reading is an actual linear map on the full tensor module. -/
def homogeneousTensorCoefficientMap (n : ℕ) :
    (MvPolynomial (Fin m) R ⊗[R] M) →ₗ[R] (Sym (Fin m) n → M) where
  toFun := homogeneousTensorCoefficientVector n
  map_add' P Q := by
    ext i
    simp [homogeneousTensorCoefficientVector]
  map_smul' r P := by
    ext i
    simp [homogeneousTensorCoefficientVector]

@[simp] theorem homogeneousTensorCoefficientVector_tmul (n : ℕ) (P : MvPolynomial (Fin m) R)
    (z : M) (i : Sym (Fin m) n) :
    homogeneousTensorCoefficientVector n (P ⊗ₜ[R] z) i =
      P.coeff (homogeneousTensorExponent n i) • z := by
  simp [homogeneousTensorCoefficientVector]

/-- Synthesize a tensor polynomial by the finite sum of its homogeneous monomials. -/
def homogeneousTensorSynthesis (n : ℕ) (c : Sym (Fin m) n → M) :
    (MvPolynomial (Fin m) R ⊗[R] M) :=
  ∑ i, monomial (homogeneousTensorExponent n i) 1 ⊗ₜ[R] c i

/-- Finite monomial synthesis is linear in the module coefficients. -/
def homogeneousTensorSynthesisMap (n : ℕ) :
    (Sym (Fin m) n → M) →ₗ[R] (MvPolynomial (Fin m) R ⊗[R] M) where
  toFun := homogeneousTensorSynthesis n
  map_add' c d := by
    simp [homogeneousTensorSynthesis, TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    simp [homogeneousTensorSynthesis, TensorProduct.tmul_smul, Finset.smul_sum]

/-- Each synthesized coefficient is exactly the coefficient supplied to it. -/
@[simp] theorem homogeneousTensorCoefficientVector_synthesis (n : ℕ)
    (c : Sym (Fin m) n → M) :
    homogeneousTensorCoefficientVector n (homogeneousTensorSynthesis (R := R) n c) = c := by
  classical
  funext i
  simp only [homogeneousTensorCoefficientVector, homogeneousTensorSynthesis,
    map_sum, Finsupp.finsetSum_apply, tensorCoefficients_monomial, Finsupp.single_apply]
  simp only [(homogeneousTensorExponent_injective n).eq_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Synthesis lands in the actual auxiliary-homogeneous submodule. -/
theorem homogeneousTensorSynthesis_homogeneous (n : ℕ) (c : Sym (Fin m) n → M) :
    TensorHomogeneous n (homogeneousTensorSynthesis (R := R) n c) := by
  apply (tensorHomogeneous_iff_coefficients n _).mpr
  intro s hs
  classical
  simp only [homogeneousTensorSynthesis, map_sum, Finsupp.finsetSum_apply,
    tensorCoefficients_monomial, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h : homogeneousTensorExponent n i ≠ s := by
    intro heq
    exact hs (heq ▸ homogeneousTensorExponent_degree n i)
  simp [h]

/-- Every homogeneous tensor is recovered by reading and synthesizing its coefficients. -/
theorem homogeneousTensorSynthesis_coefficients (n : ℕ)
    (P : (MvPolynomial (Fin m) R ⊗[R] M)) (hP : TensorHomogeneous n P) :
    homogeneousTensorSynthesis n (homogeneousTensorCoefficientVector n P) = P := by
  classical
  apply tensorCoefficients.injective
  ext s
  by_cases hs : s.degree = n
  · obtain ⟨i,rfl⟩ := exists_homogeneousTensorExponent n s hs
    exact congrFun (homogeneousTensorCoefficientVector_synthesis n
      (homogeneousTensorCoefficientVector n P)) i
  · rw [(tensorHomogeneous_iff_coefficients n _).mp
      (homogeneousTensorSynthesis_homogeneous n _) s hs,
      (tensorHomogeneous_iff_coefficients n _).mp hP s hs]

/-- The auxiliary degree-`n` submodule is the finite coefficient module indexed
by `Sym (Fin m) n`, over any commutative ring and with arbitrary module coefficients. -/
def homogeneousTensorCoordinates (n : ℕ) :
    homogeneousTensorSubmodule (R := R) (M := M) (m := m) n ≃ₗ[R] (Sym (Fin m) n → M) where
  toFun P := homogeneousTensorCoefficientVector n P.val
  invFun c := ⟨homogeneousTensorSynthesis n c, homogeneousTensorSynthesis_homogeneous n c⟩
  left_inv P := Subtype.ext (homogeneousTensorSynthesis_coefficients n P.val P.property)
  right_inv := homogeneousTensorCoefficientVector_synthesis n
  map_add' P Q := (homogeneousTensorCoefficientMap n).map_add P.val Q.val
  map_smul' r P := (homogeneousTensorCoefficientMap n).map_smul r P.val

@[simp] theorem homogeneousTensorCoordinates_apply (n : ℕ)
    (P : homogeneousTensorSubmodule (R := R) (M := M) n) (i : Sym (Fin m) n) :
    homogeneousTensorCoordinates n P i = tensorCoefficients P.val (homogeneousTensorExponent n i) := rfl

@[simp] theorem homogeneousTensorCoordinates_symm_val (n : ℕ) (c : Sym (Fin m) n → M) :
    ((homogeneousTensorCoordinates (R := R) n).symm c).val =
      ∑ i, (monomial (homogeneousTensorExponent n i) 1 : MvPolynomial (Fin m) R) ⊗ₜ[R] c i := rfl

end SteinerGeometry.HomogeneousTensor
