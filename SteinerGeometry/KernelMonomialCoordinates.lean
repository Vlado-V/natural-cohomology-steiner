module

public import SteinerGeometry.HomogeneousTensorCoordinates
public import SteinerGeometry.PolynomialWordExpansion

set_option backward.privateInPublic true
@[expose] public section

/-! The local symmetric-kernel isomorphism sends monomials to products of kernel columns. -/
noncomputable section
namespace SteinerGeometry
open MvPolynomial Steiner.SymmetricContraction
open scoped TensorProduct
variable {R : Type*} [CommRing R] {m n d : ℕ}

private theorem monomial_list_product (l : List (Fin m)) :
    (monomial ((l : Multiset (Fin m)).toFinsupp) 1 : MvPolynomial (Fin m) R) =
      (l.map (fun i => (X i : MvPolynomial (Fin m) R))).prod := by
  classical
  induction l with
  | nil => simp
  | cons i l ih =>
    have h : ((i :: l : List (Fin m)) : Multiset (Fin m)) = {i} + (l : Multiset (Fin m)) := rfl
    rw [h, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
    calc
      _ = monomial (Finsupp.single i 1) (1 : R) * monomial (Multiset.toFinsupp (l : Multiset _)) 1 := by
        rw [monomial_mul_monomial, one_mul]
      _ = _ := by rw [ih]; rfl

/-- The ordinary monomial associated to a symmetric index is the product of its ordered factors. -/
theorem monomial_symmetricWord (a : Sym (Fin m) d) :
    (monomial (HomogeneousTensor.homogeneousTensorExponent d a) 1 : MvPolynomial (Fin m) R) =
      ∏ j, X (symmetricWord a j) := by
  classical
  have he : HomogeneousTensor.homogeneousTensorExponent d a = a.val.toFinsupp := rfl
  rw [he]
  have h := monomial_list_product (R := R) a.val.toList
  rw [Multiset.coe_toList] at h
  rw [h]
  change (a.val.toList.map (fun i => (X i : MvPolynomial (Fin m) R))).prod = _
  have hl : List.ofFn (symmetricWord a) = a.val.toList := by
    exact List.Vector.toList_ofFn (symmetricWord a) |>.symm.trans
      (congrArg List.Vector.toList (List.Vector.ofFn_get _))
  rw [← hl, List.map_ofFn, List.prod_ofFn]
  rfl

/-- The local kernel coordinate embedding has exactly the product-of-linear-forms formula. -/
theorem kernelEmbedding_monomial {M : Type*} [AddCommGroup M] [Module R M]
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (a : Sym (Fin n) d) (z : M) :
    kernelEmbedding A ((monomial (HomogeneousTensor.homogeneousTensorExponent d a) 1 :
      KernelPoly n R) ⊗ₜ[R] z) =
        (∏ j, linearForm (A (symmetricWord a j).succ)) ⊗ₜ[R] z := by
  rw [monomial_symmetricWord]
  change (linearChange A (kernelEmbeddingBase (∏ j, X (symmetricWord a j)))) ⊗ₜ[R] z = _
  simp only [map_prod, kernelEmbeddingBase, rename_X, linearChange_X]

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The actual local monomial multiplication map in finite homogeneous coordinates. -/
def splitPolynomialMap (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (d : ℕ) :
    (Sym (Fin n) d → M) →ₗ[R] (Sym (Fin (n+1)) d → M) :=
  (HomogeneousTensor.homogeneousTensorCoefficientMap d).comp
    ((kernelEmbedding A).comp (HomogeneousTensor.homogeneousTensorSynthesisMap d))

/-- Each matrix entry is the coefficient of the product of the chosen kernel columns. -/
theorem splitPolynomialMap_apply (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (d : ℕ)
    (v : Sym (Fin n) d → M) (b : Sym (Fin (n+1)) d) :
    splitPolynomialMap A d v b = ∑ a : Sym (Fin n) d,
      (∏ j, linearForm (A (symmetricWord a j).succ)).coeff
        (HomogeneousTensor.homogeneousTensorExponent d b) • v a := by
  classical
  change HomogeneousTensor.tensorCoefficients
    (kernelEmbedding A (∑ a : Sym (Fin n) d,
      (monomial (HomogeneousTensor.homogeneousTensorExponent d a) 1 : KernelPoly n R) ⊗ₜ[R] v a))
    (HomogeneousTensor.homogeneousTensorExponent d b) = _
  simp only [map_sum, Finsupp.finsetSum_apply, kernelEmbedding_monomial,
    HomogeneousTensor.tensorCoefficients_tmul]

theorem kernelEmbedding_homogeneous (A : Matrix (Fin (n+1)) (Fin (n+1)) R)
    {P : KernelTensor (n := n) (R := R) (M := M)} (hP : TensorHomogeneous d P) :
    TensorHomogeneous d (kernelEmbedding A P) := by
  apply tensor_linearSubstitution_homogeneous (linearChange A) (by intro i; simp)
  exact tensor_linearSubstitution_homogeneous kernelEmbeddingBase
    kernelEmbeddingBase_X_homogeneous hP

theorem splitPolynomialMap_synthesis (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (d : ℕ)
    (v : Sym (Fin n) d → M) :
    HomogeneousTensor.homogeneousTensorSynthesis (R := R) d (splitPolynomialMap A d v) =
      kernelEmbedding A (HomogeneousTensor.homogeneousTensorSynthesis (R := R) d v) := by
  apply HomogeneousTensor.homogeneousTensorSynthesis_coefficients
  exact kernelEmbedding_homogeneous A
    (HomogeneousTensor.homogeneousTensorSynthesis_homogeneous d v)

theorem splitPolynomialMap_injective (A B : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hAB : A * B = 1) (d : ℕ) : Function.Injective (splitPolynomialMap (M := M) A d) := by
  intro v w h
  have hs := congrArg (HomogeneousTensor.homogeneousTensorSynthesis (R := R) d) h
  rw [splitPolynomialMap_synthesis, splitPolynomialMap_synthesis] at hs
  apply_fun kernelCoordinates B at hs
  rw [kernelCoordinates_embedding A B hAB, kernelCoordinates_embedding A B hAB] at hs
  apply_fun HomogeneousTensor.homogeneousTensorCoefficientVector d at hs
  simpa only [HomogeneousTensor.homogeneousTensorCoefficientVector_synthesis] using hs

/-- Finite product coordinates give exactly, and uniquely, every homogeneous
polynomial in the kernel of the split directional derivative. -/
theorem splitPolynomialMap_exact {K : Type*} [Field K] [CharZero K] [Algebra K R]
    (f : Fin (n+1) → R) (A B : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    (d : ℕ) (x : Sym (Fin (n+1)) d → M) :
    tensorDirectional f (HomogeneousTensor.homogeneousTensorSynthesis (R := R) d x) = 0 ↔
      ∃! v : Sym (Fin n) d → M, splitPolynomialMap A d v = x := by
  have hP := HomogeneousTensor.homogeneousTensorSynthesis_homogeneous (R := R) d x
  rw [tensor_directional_homogeneous_kernel (K := K) f A B hAB hBA hA _ hP]
  constructor
  · rintro ⟨Q, ⟨hQ, heQ⟩, huniq⟩
    have hex : splitPolynomialMap A d (HomogeneousTensor.homogeneousTensorCoefficientVector d Q) = x := by
      change HomogeneousTensor.homogeneousTensorCoefficientVector d
        (kernelEmbedding A (HomogeneousTensor.homogeneousTensorSynthesis (R := R) d
          (HomogeneousTensor.homogeneousTensorCoefficientVector d Q))) = x
      rw [HomogeneousTensor.homogeneousTensorSynthesis_coefficients d Q hQ, heQ,
        HomogeneousTensor.homogeneousTensorCoefficientVector_synthesis]
    refine ⟨HomogeneousTensor.homogeneousTensorCoefficientVector d Q, hex, ?_⟩
    intro v hv
    exact splitPolynomialMap_injective A B hAB d (hv.trans hex.symm)
  · rintro ⟨v, hv, _⟩
    refine ⟨HomogeneousTensor.homogeneousTensorSynthesis (R := R) d v,
      ⟨HomogeneousTensor.homogeneousTensorSynthesis_homogeneous d v, ?_⟩, ?_⟩
    · rw [← splitPolynomialMap_synthesis, hv]
    · intro Q hQ
      have hq := hQ.2
      rw [← hv, splitPolynomialMap_synthesis] at hq
      apply_fun kernelCoordinates B at hq
      simpa only [kernelCoordinates_embedding A B hAB] using hq

end SteinerGeometry
