module

public import Steiner.OperatorDuality

set_option backward.privateInPublic true
@[expose] public section

/-! Triangular surjectivity of the actual coefficient differential. -/

noncomputable section
namespace SteinerGeometry
open Steiner MvPolynomial Module

variable {K : Type*} [Field K] [CharZero K]
variable {n : ℕ} {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- One surjective coefficient map already makes contraction surjective in every
positive degree. This is the triangular local calculation behind the sheaf epimorphism. -/
theorem operatorDifferential_surjective_of_coefficient
    (T : Fin (n+1) → V →ₗ[K] W) (j : Fin (n+1))
    (hT : Function.Surjective (T j)) (d : ℕ) :
    Function.Surjective (operatorDifferential T d) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro w _
  have hsingle : ∀ k : ℕ, ∀ b : Sym (Fin (n+1)) d,
      d - operatorExponent d b j = k → ∀ z : W,
      Pi.single b z ∈ (operatorDifferential T d).range := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro b hb z
      have hbnd : operatorExponent d b j ≤ d := by
        simpa only [operatorExponent_degree] using (Finsupp.le_degree j (operatorExponent d b))
      let a := operatorRaisedIndex d b j
      let q : K := (operatorExponent d b j : K) + 1
      have hq : q ≠ 0 := by
        simpa only [q, Nat.cast_add, Nat.cast_one] using
          (Nat.cast_ne_zero.mpr (by omega : operatorExponent d b j + 1 ≠ 0) :
            ((operatorExponent d b j + 1 : ℕ) : K) ≠ 0)
      obtain ⟨v, hv⟩ := hT (q⁻¹ • z)
      let y := operatorDifferential T d (Pi.single a v)
      have hyb : y b = z := by
        rw [show y b = _ from operatorDifferential_single T d a v b]
        rw [Finset.sum_eq_single j]
        · rw [coeff_pderiv, operatorRaisedIndex_exponent]
          simp only [coeff_monomial, ite_true, one_mul]
          change q • T j v = z
          rw [hv, smul_smul, mul_inv_cancel₀ hq, one_smul]
        · intro i _ hij
          have he : operatorExponent (d+1) a ≠ operatorExponent d b + Finsupp.single i 1 := by
            rw [operatorRaisedIndex_exponent]
            intro he
            have he' := congrArg (fun s : Fin (n+1) →₀ ℕ => s j) he
            simp only [Finsupp.add_apply, Finsupp.single_eq_same,
              Finsupp.single_eq_of_ne (Ne.symm hij)] at he'
            omega
          rw [coeff_pderiv, coeff_monomial, ite_eq_right he]
          simp
        · simp
      have hyc : ∀ c : Sym (Fin (n+1)) d, c ≠ b →
          Pi.single c (y c) ∈ (operatorDifferential T d).range := by
        intro c hcb
        have hcnd : operatorExponent d c j ≤ d := by
          simpa only [operatorExponent_degree] using (Finsupp.le_degree j (operatorExponent d c))
        by_cases hlt : operatorExponent d b j < operatorExponent d c j
        · apply ih (d - operatorExponent d c j) (by omega) c rfl
        · have hy0 : y c = 0 := by
            rw [show y c = _ from operatorDifferential_single T d a v c]
            apply Finset.sum_eq_zero
            intro i _
            have he : operatorExponent (d+1) a ≠
                operatorExponent d c + Finsupp.single i 1 := by
              rw [operatorRaisedIndex_exponent]
              intro he
              by_cases hij : i = j
              · subst i
                have hbc := add_right_cancel he
                exact hcb ((operatorExponent_injective d) hbc).symm
              · have he' := congrArg (fun s : Fin (n+1) →₀ ℕ => s j) he
                simp only [Finsupp.add_apply, Finsupp.single_eq_same,
                  Finsupp.single_eq_of_ne (Ne.symm hij)] at he'
                omega
            rw [coeff_pderiv, coeff_monomial, ite_eq_right he]
            simp
          rw [hy0, Pi.single_zero]
          exact Submodule.zero_mem _
      have hysum : ∑ c ∈ Finset.univ.erase b, Pi.single c (y c) ∈
          (operatorDifferential T d).range := by
        apply Submodule.sum_mem
        intro c hc
        exact hyc c (Finset.mem_erase.mp hc).1
      have hy : y ∈ (operatorDifferential T d).range := ⟨Pi.single a v, rfl⟩
      have hdecomp : y - ∑ c ∈ Finset.univ.erase b, Pi.single c (y c) = Pi.single b z := by
        ext c
        by_cases hcb : c = b
        · subst c
          simp [hyb]
        · simp [Pi.single_apply, hcb]
      rw [← hdecomp]
      exact Submodule.sub_mem _ hy hysum
  rw [← Finset.univ_sum_single w]
  exact Submodule.sum_mem _ (fun b _ => hsingle _ b rfl (w b))

end SteinerGeometry
