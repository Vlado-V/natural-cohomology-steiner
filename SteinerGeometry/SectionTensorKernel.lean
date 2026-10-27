module

public import SteinerGeometry.PolynomialWordExpansion
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

set_option backward.privateInPublic true
@[expose] public section

/-! The universal monomial maps are annihilated by contraction on decomposable sections. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open Steiner MvPolynomial Steiner.SymmetricContraction

universe u
variable {X : Scheme.{u}}
local instance sectionTensorKernelBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

private instance sectionTensorKernelEvalAdditive (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive where
  map_add := by intros; rfl

/-- Evaluation of a sheaf morphism on a fixed section is additive in that morphism. -/
def sheafValueHom (M N : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    (M ⟶ N) →+ Γ(N, U) where
  toFun f := f.app U x
  map_zero' := rfl
  map_add' _f _g := rfl

private theorem structureSection_apply {N : X.Modules}
    (e : Line.Bundles.structureModule X ⟶ N) (U : X.Opens) (r : Γ(X, U)) :
    e.app U r = r • e.app U (1 : Γ(X, U)) := by
  have h := e.app_smul (U := U) r (1 : Γ(X, U))
  change e.app U (r * (1 : Γ(X, U))) = _ at h
  exact (congrArg (fun a : Γ(X, U) => e.app U a) (mul_one r)).symm.trans h

/-- Products of columns in the evaluation kernel are killed by the actual
contraction morphism, on every decomposable section of their tensor product. -/
theorem tensorMonomialMap_contraction_generator {n d : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N))
    (G : Fin (d+1) → X.Modules)
    (c : ∀ j, Fin (n+1) → (G j ⟶ Line.Bundles.structureModule X))
    (hc : ∀ j, ∑ i, c j i ≫ e i = 0)
    (U : X.Opens) (v : ∀ j, Γ(G j, U)) :
    ((tensorMonomialMap G c ≫ sectionContraction e d).app U)
      (tensorGenerator (d+1) G U v) = 0 := by
  classical
  let F : X.Modules ⥤ ModuleCat Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : F.Additive := by
    dsimp [F]
    exact sectionTensorKernelEvalAdditive U
  let z := tensorGenerator (d+1) G U v
  let a : Fin (d+1) → Fin (n+1) → Γ(X, U) := fun j i => structureMapValue (c j i) U (v j)
  let P : Aux n Γ(X, U) := ∏ j, linearForm (a j)
  let w : Fin (n+1) → Γ(N, U) := fun i => (e i).app U (1 : Γ(X, U))
  have hw (j : Fin (d+1)) : ∑ i, a j i • w i = 0 := by
    have h := congrArg (sheafValueHom (G j) N U (v j)) (hc j)
    rw [map_sum, map_zero] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    change a j i • w i = (e i).app U ((c j i).app U (v j))
    exact (structureSection_apply (e i) U _).symm
  have hp (b : Sym (Fin (n+1)) (d+1)) :
      biproductCoordinates F (Line.Bundles.structureModule X) (Sym (Fin (n+1)) (d+1))
        (F.map (tensorMonomialMap G c) z) b = P.coeff (operatorExponent (d+1) b) := by
    change structureMapValue (tensorMonomialMap G c ≫ biproduct.π _ b) U z = _
    rw [tensorMonomialMap_generator]
    exact (product_linearForms_coeff a b).symm
  change F.map (sectionContraction e d) (F.map (tensorMonomialMap G c) z) = 0
  apply (biproductCoordinates F N (Sym (Fin (n+1)) d)).injective
  ext b
  rw [map_zero, Pi.zero_apply]
  have h := sectionContraction_sections_weighted F e d
    (biproductCoordinates F (Line.Bundles.structureModule X) (Sym (Fin (n+1)) (d+1))
      (F.map (tensorMonomialMap G c) z)) b
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h]
  simp only [hp]
  calc
    _ = ∑ a' : Sym (Fin (n+1)) (d+1), ∑ i : Fin (n+1),
        contractionMultiplicity d a' b i • (P.coeff (operatorExponent (d+1) a') • w i) := by
      apply Finset.sum_congr rfl
      intro a' _
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact structureSection_apply (e i) U _
    _ = ∑ i, (pderiv i P).coeff (operatorExponent d b) • w i :=
      weighted_contraction_coeff d P b w
    _ = 0 := product_contraction_coeff_eq_zero Finset.univ w a (fun j _ => hw j) _

end SteinerGeometry
