module

public import Steiner.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section

noncomputable section

namespace Steiner

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- Set the first coordinate to zero and shift the remaining coordinates down. -/
def eraseFirst : Poly K (n + 1) →ₐ[K] Poly K n :=
  MvPolynomial.killCompl (Fin.succ_injective n)

@[simp] theorem eraseFirst_X_zero :
    eraseFirst (X (0 : Fin (n + 1)) : Poly K (n + 1)) = 0 := by
  classical
  simp [eraseFirst, killCompl]

@[simp] theorem eraseFirst_X_succ (i : Fin n) :
    eraseFirst (X i.succ : Poly K (n + 1)) = X i := by
  have h := MvPolynomial.killCompl_rename_app (Fin.succ_injective n) (X i : Poly K n)
  simpa only [rename_X, eraseFirst] using h

theorem eraseFirst_isHomogeneous {p : Poly K (n + 1)} {d : ℕ}
    (hp : p.IsHomogeneous d) : (eraseFirst p).IsHomogeneous d := by
  intro e he
  have he' : p.coeff (e.mapDomain Fin.succ) ≠ 0 := by
    simpa only [eraseFirst, coeff_killCompl] using he
  have hd : (e.mapDomain Fin.succ).degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp he'
  have hd' : e.degree = d := by simpa only [Finsupp.degree_mapDomain] using hd
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd' 

/-- The kernel of specialization at the first coordinate is its principal ideal. -/
theorem x_dvd_of_eraseFirst_eq_zero (p : Poly K (n + 1))
    (hp : eraseFirst p = 0) : X 0 ∣ p := by
  classical
  apply X_dvd_iff_modMonomial_eq_zero.mpr
  ext e
  by_cases he : Finsupp.single (0 : Fin (n + 1)) 1 ≤ e
  · simp only [coeff_modMonomial_of_le p he, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · rw [coeff_modMonomial_of_not_le p he]
    have he0 : e 0 = 0 := by
      simpa only [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, not_not] using he
    have hs : (↑e.support : Set (Fin (n + 1))) ⊆ Set.range Fin.succ := by
      intro i hi
      refine Fin.cases ?_ (fun j _ => ⟨j, rfl⟩) i hi
      intro hz
      exfalso
      exact (Finsupp.mem_support_iff.mp hz) he0
    have hm := Finsupp.mapDomain_comapDomain Fin.succ (Fin.succ_injective n) e hs
    have hc := congrArg (fun q : Poly K n =>
      q.coeff (e.comapDomain Fin.succ (Fin.succ_injective n).injOn)) hp
    simpa only [eraseFirst, coeff_killCompl, hm, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hc

/-- Removing one first-coordinate factor lowers the homogeneous degree by one. -/
theorem homogeneous_div_x {t : ℕ} (p : Poly K (n + 1))
    (hp : p.IsHomogeneous (t + 1)) :
    (p.divMonomial (Finsupp.single 0 1)).IsHomogeneous t := by
  intro e he
  have hcoeff : p.coeff (Finsupp.single 0 1 + e) ≠ 0 := by
    simpa only [coeff_divMonomial] using he
  have hdeg : (Finsupp.single 0 1 + e).degree = t + 1 := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp hcoeff
  have hedeg : e.degree = t := by
    simp only [map_add, Finsupp.degree_single] at hdeg
    omega
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hedeg

/-- A homogeneous constant divisible by the first coordinate is zero. -/
theorem homogeneous_zero_of_x_dvd (p : Poly K (n + 1))
    (hp : p.IsHomogeneous 0) (hdiv : X 0 ∣ p) : p = 0 := by
  ext e
  by_cases he : e = 0
  · subst e
    obtain ⟨q, rfl⟩ := hdiv
    simp [coeff_X_mul']
  · simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      hp.coeff_eq_zero (fun hd => he ((Finsupp.degree_eq_zero_iff e).mp hd))

/-- Dividing by the first coordinate reconstructs a polynomial divisible by it. -/
theorem x_mul_div_of_x_dvd (p : Poly K (n + 1)) (hdiv : X 0 ∣ p) :
    X 0 * p.divMonomial (Finsupp.single 0 1) = p := by
  have hmod := (X_dvd_iff_modMonomial_eq_zero).mp hdiv
  simpa only [hmod, add_zero] using p.divMonomial_add_modMonomial_single 0

end Steiner
