module

public import OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeDegreeComponents
public import Steiner.Critical

set_option backward.privateInPublic true
@[expose] public section

/-! Surjectivity of the actual sheaf map from eventual homogeneous matrix rank. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.PolynomialMatrixEpi
open CategoryTheory AlgebraicGeometry Steiner
open OAI.AlgebraicGeometry.SheafCohomology.Projective
open OAI.AlgebraicGeometry.HilbertScheme.Presentations
universe u
variable {R : Type u}
attribute [local instance] MvPolynomial.gradedAlgebra

section Ring
variable [CommRing R]

theorem weighted_surjective_of_matrix_surjective
    {n a b N : ℕ} (hN : 1 ≤ N)
    (M : Fin a → Fin b → MvPolynomial.homogeneousSubmodule (Fin (n+1)) R 1)
    (hs : Function.Surjective (fun x : Fin b → MvPolynomial.homogeneousSubmodule (Fin (n+1)) R (N-1) =>
      fun i => (⟨∑ j, (M i j).val * (x j).val, by
        apply MvPolynomial.IsHomogeneous.sum
        intro j _
        simpa only [Nat.add_sub_cancel' hN] using (M i j).property.mul (x j).property⟩ :
          MvPolynomial.homogeneousSubmodule (Fin (n+1)) R N))) :
    ∀ y : WeightedFreeModules.GradedModules.weightedFreeGrading (σ := Fin (n+1)) R
        (fun _ : Fin a => (0 : ℤ)) (N : ℤ),
      ∃ x : WeightedFreeModules.GradedModules.weightedFreeGrading (σ := Fin (n+1)) R
          (fun _ : Fin b => (1 : ℤ)) (N : ℤ),
        ∀ i, y.val i = ∑ j, (M i j).val * x.val j := by
  intro y
  let et := WeightedFreeDegreeComponents.weightedFreeDegreeComponentsEquiv
    (R := R) (σ := Fin (n+1)) (fun _ : Fin a => 0) N (by simp)
  let es := WeightedFreeDegreeComponents.weightedFreeDegreeComponentsEquiv
    (R := R) (σ := Fin (n+1)) (fun _ : Fin b => 1) N (by simpa using fun _ : Fin b => hN)
  let yt : Fin a → MvPolynomial.homogeneousSubmodule (Fin (n+1)) R N :=
    fun i => ⟨y.val i, by
      have h := ((et y) i).property
      change (y.val i).IsHomogeneous (N-0) at h
      change (y.val i).IsHomogeneous N
      simpa only [Nat.sub_zero] using h⟩
  obtain ⟨x, hx⟩ := hs yt
  refine ⟨es.symm x, ?_⟩
  intro i
  have h := congrArg (fun z => (z i).val) hx
  have he (j : Fin b) : (es.symm x).val j = (x j).val := by
    exact congrArg (fun z => (z j).val) (es.apply_symm_apply x)
  simpa only [yt, he] using h.symm

end Ring

section Field
variable [Field R]

theorem weighted_surjective_of_all_ranks
    {n t r : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (M : LinearMatrix R n t (t+r)) (hM : ∀ d, LinearMatrixMaximalRank M d)
    (N : ℕ) (hN : criticalCeil n t r ≤ N) :
    ∀ y : WeightedFreeModules.GradedModules.weightedFreeGrading (σ := Fin (n+1)) R
        (fun _ : Fin t => (0 : ℤ)) (N : ℤ),
      ∃ x : WeightedFreeModules.GradedModules.weightedFreeGrading (σ := Fin (n+1)) R
          (fun _ : Fin (t+r) => (1 : ℤ)) (N : ℤ),
        ∀ i, y.val i = ∑ j, (M i j).val * x.val j := by
  have hpos := criticalCeil_pos hn ht hr
  have hs : Function.Surjective (linearMatrixMap M (N-1)) :=
    linearMatrixMap_surjective_upward M (by omega)
      (criticalSurjective_of_all_ranks M hn ht hr hM)
  apply weighted_surjective_of_matrix_surjective (show 1 ≤ N by omega) M
  intro y
  let yt : MatrixTarget R n t (N-1) :=
    fun i => ⟨(y i).val, by simpa only [Nat.sub_add_cancel (show 1 ≤ N by omega)] using (y i).property⟩
  obtain ⟨x, hx⟩ := hs yt
  refine ⟨x, ?_⟩
  funext i
  apply Subtype.ext
  simpa only [yt, linearMatrixMap_val] using congrArg (fun z => (z i).val) hx

end Field

end SteinerGeometry.PolynomialMatrixEpi
