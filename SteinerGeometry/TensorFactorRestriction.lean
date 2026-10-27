import SteinerGeometry.TensorFactorFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange

/-! Restriction coordinates for the ordered tensor products used in symmetric monomials. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

private theorem restrictedTensor_identity (M N : Y.Modules) :
    (Bilinear.Sheaves.SheafBilinearMap.restrictedCorepresentable f M N).homEquiv (𝟙 _) =
      (Tensor.Bifunctor.tensorBilinear M N).restrict f := by
  change (Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N _).symm
    (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _
      ((Scheme.Modules.restrictAdjunction f).homEquiv _ _ (𝟙 _))) = _
  rw [Adjunction.homEquiv_id, ← Tensor.Bifunctor.tensorBilinear_postcomp]
  have h := Bilinear.Sheaves.SheafBilinearMap.restrict_unit_naturality
    (Tensor.Bifunctor.tensorBilinear M N) f
  rw [← h]
  exact Equiv.symm_apply_apply _ _

/-- The canonical tensor map from restricted factors to the restricted tensor product. -/
def tensorRestrictComparison (M N : Y.Modules) :
    Tensor.ProductSheaf.tensorModule (M.restrict f) (N.restrict f) ⟶
      (Tensor.ProductSheaf.tensorModule M N).restrict f :=
  (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm
    ((Tensor.Bifunctor.tensorBilinear M N).restrict f)

/-- The canonical comparison is an isomorphism, with no flatness assumption on sections. -/
theorem tensorRestrictComparison_isIso (M N : Y.Modules) :
    IsIso (tensorRestrictComparison f M N) := by
  let e := Bilinear.Sheaves.SheafBilinearMap.restrictedCorepresentable f M N
  let q := Bilinear.Sheaves.SheafBilinearMap.corepresentable (M.restrict f) (N.restrict f)
  let a := e.homEquiv.symm (q.homEquiv (𝟙 _))
  have hc : tensorRestrictComparison f M N = q.homEquiv.symm (e.homEquiv (𝟙 _)) := by
    rw [restrictedTensor_identity]
    rfl
  let E : (Tensor.ProductSheaf.tensorModule M N).restrict f ≅
      Tensor.ProductSheaf.tensorModule (M.restrict f) (N.restrict f) := {
    hom := a
    inv := q.homEquiv.symm (e.homEquiv (𝟙 _))
    hom_inv_id := by
      apply e.homEquiv.injective
      rw [e.homEquiv_comp]
      dsimp [a]
      rw [Equiv.apply_symm_apply, ← q.homEquiv_eq, Equiv.apply_symm_apply]
    inv_hom_id := by
      apply q.homEquiv.injective
      rw [q.homEquiv_comp, Equiv.apply_symm_apply, ← e.homEquiv_eq]
      dsimp [a]
      rw [Equiv.apply_symm_apply] }
  rw [hc]
  exact E.isIso_inv

attribute [instance] tensorRestrictComparison_isIso

/-- Its section formula is the unaltered pure tensor, on the corresponding image open. -/
theorem tensorRestrictComparison_pure (M N : Y.Modules) (U : X.Opens)
    (x : Γ(M.restrict f, U)) (y : Γ(N.restrict f, U)) :
    (tensorRestrictComparison f M N).app U
      ((Tensor.Bifunctor.tensorBilinear (M.restrict f) (N.restrict f)).app U x y) =
        (Tensor.Bifunctor.tensorBilinear M N).app (f ''ᵁ U) x y := by
  have h := Tensor.Bifunctor.tensorBilinear_postcomp (tensorRestrictComparison f M N)
  unfold tensorRestrictComparison at h
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (fun β => β.app U x y) h

/-- Ordered tensor products commute with restriction, in the direction preserving pure tensors. -/
def tensorFactorsRestrictIso : (s : ℕ) → (G : Fin s → Y.Modules) →
    tensorFactors s (fun j => (G j).restrict f) ≅ (tensorFactors s G).restrict f
  | 0, _ => (Scheme.Modules.restrictUnitIso f).symm
  | s+1, G =>
    Tensor.Bifunctor.tensorModuleMapIso (Iso.refl _)
      (tensorFactorsRestrictIso s (fun j => G j.succ)) ≪≫
        @asIso _ _ _ _ (tensorRestrictComparison f (G 0) (tensorFactors s (fun j => G j.succ)))
          (tensorRestrictComparison_isIso f (G 0) (tensorFactors s (fun j => G j.succ)))

set_option backward.isDefEq.respectTransparency false in
/-- The ordered tensor restriction comparison sends a tensor generator to the same generator. -/
theorem tensorFactorsRestrictIso_generator (s : ℕ) (G : Fin s → Y.Modules)
    (U : X.Opens) (v : ∀ j, Γ((G j).restrict f, U)) :
    (tensorFactorsRestrictIso f s G).hom.app U
      (tensorGenerator s (fun j => (G j).restrict f) U v) =
        tensorGenerator s G (f ''ᵁ U) v := by
  induction s with
  | zero =>
    change (Scheme.Modules.restrictUnitIso f).inv.app U (1 : Γ(X, U)) = _
    change (f.appIso U).inv (1 : Γ(X, U)) = (1 : Γ(Y, f ''ᵁ U))
    exact map_one _
  | succ s ih =>
    change (tensorRestrictComparison f (G 0) (tensorFactors s (fun j => G j.succ))).app U
      ((Tensor.Bifunctor.tensorModuleMap (𝟙 _) (tensorFactorsRestrictIso f s
        (fun j => G j.succ)).hom).app U
          ((Tensor.Bifunctor.tensorBilinear ((G 0).restrict f)
            (tensorFactors s (fun j => (G j.succ).restrict f))).app U (v 0)
              (tensorGenerator s (fun j => (G j.succ).restrict f) U (fun j => v j.succ)))) = _
    have hm := congrArg (fun β => β.app U (v 0)
      (tensorGenerator s (fun j => (G j.succ).restrict f) U (fun j => v j.succ)))
        (Tensor.Bifunctor.tensorModuleMap_spec (𝟙 ((G 0).restrict f))
          (tensorFactorsRestrictIso f s (fun j => G j.succ)).hom)
    change (Tensor.Bifunctor.tensorModuleMap (𝟙 ((G 0).restrict f))
        (tensorFactorsRestrictIso f s (fun j => G j.succ)).hom).app U
        ((Tensor.Bifunctor.tensorBilinear ((G 0).restrict f)
          (tensorFactors s (fun j => (G j.succ).restrict f))).app U (v 0)
            (tensorGenerator s (fun j => (G j.succ).restrict f) U (fun j => v j.succ))) =
      (Tensor.Bifunctor.tensorBilinear _ _).app U (v 0)
      ((tensorFactorsRestrictIso f s (fun j => G j.succ)).hom.app U
        (tensorGenerator s (fun j => (G j.succ).restrict f) U (fun j => v j.succ))) at hm
    rw [hm, ih, tensorRestrictComparison_pure]
    rfl

end SteinerGeometry
