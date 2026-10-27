module

public import SteinerGeometry.SectionTensorMonomials
public import SteinerGeometry.PolynomialProductKernel
public import Mathlib.Algebra.BigOperators.Group.Finset.Pi

set_option backward.privateInPublic true
@[expose] public section

/-! Ordinary polynomial expansion for the universal tensor monomial morphisms. -/
noncomputable section
namespace SteinerGeometry
open MvPolynomial Steiner.SymmetricContraction
variable {R : Type*} [CommRing R] {n s : ℕ}

private theorem monomial_list_variables (l : List (Fin (n+1))) :
    (monomial ((l : Multiset (Fin (n+1))).toFinsupp) 1 : Aux n R) =
      (l.map (fun i => (X i : Aux n R))).prod := by
  classical
  induction l with
  | nil => simp
  | cons i l ih =>
    have h : ((i :: l : List (Fin (n+1))) : Multiset (Fin (n+1))) =
        {i} + (l : Multiset (Fin (n+1))) := rfl
    rw [h, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
    calc
      _ = monomial (Finsupp.single i 1) (1 : R) * monomial (Multiset.toFinsupp (l : Multiset _)) 1 := by
        rw [monomial_mul_monomial, one_mul]
      _ = _ := by rw [ih]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- A word of variables multiplies to the corresponding commutative monomial. -/
theorem prod_variables_word (w : Fin s → Fin (n+1)) :
    (∏ j, (X (w j) : Aux n R)) = monomial (Steiner.operatorExponent s (wordMonomial w)) 1 := by
  classical
  have h := monomial_list_variables (R := R) (List.ofFn w)
  have he : Steiner.operatorExponent s (wordMonomial w) =
      (List.ofFn w : Multiset (Fin (n+1))).toFinsupp := by
    ext i
    calc
      _ = (wordMonomial w : Multiset (Fin (n+1))).count i :=
        Sym.coe_equivNatSum_apply_apply (Fin (n+1)) s (wordMonomial w) i
      _ = _ := by
        have hw : (wordMonomial w : Multiset (Fin (n+1))) =
            (List.ofFn w : Multiset (Fin (n+1))) := by
          exact congrArg (fun l : List (Fin (n+1)) => (l : Multiset (Fin (n+1))))
            (List.Vector.toList_ofFn w)
        rw [hw, Multiset.toFinsupp_apply]
  rw [he, h]
  simp [List.prod_ofFn]

/-- Product of linear forms, expanded without suppressing repeated-word multiplicities. -/
theorem product_linearForms_word_expansion (c : Fin s → Fin (n+1) → R) :
    (∏ j, linearForm (c j)) =
      ∑ w : Fin s → Fin (n+1),
        monomial (Steiner.operatorExponent s (wordMonomial w)) (∏ j, c j (w j)) := by
  classical
  simp only [linearForm]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.prod_mul_distrib, prod_variables_word]
  have hc : (∏ j, (C (c j (w j)) : Aux n R)) = C (∏ j, c j (w j)) := (map_prod C _ _).symm
  rw [hc, C_mul_monomial, mul_one]

/-- Coefficients of the product coincide exactly with the global tensor-monomial formula. -/
theorem product_linearForms_coeff (c : Fin s → Fin (n+1) → R)
    (b : Sym (Fin (n+1)) s) :
    (∏ j, linearForm (c j)).coeff (Steiner.operatorExponent s b) =
      ∑ w : Fin s → Fin (n+1), if wordMonomial w = b then ∏ j, c j (w j) else 0 := by
  classical
  rw [product_linearForms_word_expansion, coeff_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [coeff_monomial]
  simp only [(Steiner.operatorExponent_injective s).eq_iff]

/-- The natural multiplicity matrix has precisely the partial-derivative coefficients. -/
theorem weighted_coeff_derivative (d : ℕ) (P : Aux n R)
    (b : Sym (Fin (n+1)) d) (i : Fin (n+1)) :
    (∑ a : Sym (Fin (n+1)) (d+1), contractionMultiplicity d a b i •
      P.coeff (Steiner.operatorExponent (d+1) a)) =
      (pderiv i P).coeff (Steiner.operatorExponent d b) := by
  classical
  rw [coeff_pderiv, ← Steiner.operatorRaisedIndex_exponent d b i]
  simp only [contractionMultiplicity, ← Steiner.operatorRaisedIndex_exponent d b i,
    (Steiner.operatorExponent_injective (d+1)).eq_iff, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp [nsmul_eq_mul, mul_comm, Nat.cast_add, Nat.cast_one]

/-- The entire multiplicity matrix is contraction with the given module coefficients. -/
theorem weighted_contraction_coeff {M : Type*} [AddCommGroup M] [Module R M]
    (d : ℕ) (P : Aux n R) (b : Sym (Fin (n+1)) d) (e : Fin (n+1) → M) :
    (∑ a : Sym (Fin (n+1)) (d+1), ∑ i : Fin (n+1),
      contractionMultiplicity d a b i •
        (P.coeff (Steiner.operatorExponent (d+1) a) • e i)) =
      ∑ i, (pderiv i P).coeff (Steiner.operatorExponent d b) • e i := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← weighted_coeff_derivative d P b i, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a _
  exact (smul_assoc _ _ _).symm

end SteinerGeometry
