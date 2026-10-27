module

public import SteinerGeometry.PointLineBundle
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitLeftNaturality

set_option backward.privateInPublic true
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

universe u

/-- Multiplication by the actual ideal of the image of a morphism. -/
def pointTensorInclusion {X Y : Scheme.{u}} (a : Y ⟶ X) (E : X.Modules) :
    Tensor.ProductSheaf.tensorModule (OAI.MaximalSeshadri.IdealModule.closedModule a.ker) E ⟶ E :=
  Tensor.Bifunctor.tensorModuleMap
    (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι) (𝟙 E) ≫
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso E).hom

theorem pointIdeal_inclusion_app_zero {X Y : Scheme.{u}} (a : Y ⟶ X)
    (U : X.Opens)
    (x : Γ(OAI.MaximalSeshadri.IdealModule.closedModule a.ker, U)) :
    a.app U ((OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app U x) = 0 := by
  have hz := congrArg (fun h => h.app U x)
    (kernel.condition (OAI.MaximalSeshadri.IdealModule.structureMap a.ker.subschemeι))
  change a.ker.subschemeι.app U
    ((OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app U x) = 0 at hz
  let r : Γ(X, U) :=
    (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app U x
  have h := congrArg (fun z => a.toImage.app (a.ker.subschemeι ⁻¹ᵁ U) z) hz
  rw [map_zero] at h
  change (a.toImage ≫ a.imageι).app U r = 0 at h
  let t : Γ(Y, a ⁻¹ᵁ U) ⟶ Γ(Y, (a.toImage ≫ a.imageι) ⁻¹ᵁ U) :=
    Y.presheaf.map (eqToHom (by rw [a.toImage_imageι])).op
  have : IsIso t := by dsimp [t]; infer_instance
  apply (ConcreteCategory.bijective_of_isIso t).injective
  have hc := congrArg (fun g => g r) (Scheme.Hom.congr_app a.toImage_imageι U)
  change (a.toImage ≫ a.imageι).app U r = t (a.app U r) at hc
  rw [← hc, h, map_zero]

theorem pointTensorInclusion_pure {X Y : Scheme.{u}} (a : Y ⟶ X) (E : X.Modules)
    (U : X.Opens)
    (x : Γ(OAI.MaximalSeshadri.IdealModule.closedModule a.ker, U)) (y : Γ(E, U)) :
    (pointTensorInclusion a E).app U
      ((Tensor.Bifunctor.tensorBilinear _ E).app U x y) =
        (show Γ(X, U) from
          (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app U x) • y := by
  have h := congrArg (fun β => β.app U x y)
    (Tensor.Bifunctor.tensorModuleMap_spec
      (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι) (𝟙 E))
  change (Tensor.Bifunctor.tensorModuleMap
    (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι) (𝟙 E)).app U
    ((Tensor.Bifunctor.tensorBilinear _ E).app U x y) =
      (Tensor.Bifunctor.tensorBilinear _ E).app U
        ((OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app U x) y at h
  change (Tensor.ProductSheaf.tensorModuleUnitLeftIso E).hom.app U
    ((Tensor.Bifunctor.tensorModuleMap
      (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι) (𝟙 E)).app U
        ((Tensor.Bifunctor.tensorBilinear _ E).app U x y)) = _
  rw [h]
  have hu := congrArg (fun β => β.app U
    ((OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app U x) y)
    ((Tensor.Bifunctor.tensorBilinear_postcomp
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso E).hom).trans
        (Tensor.PullbackUnits.tensorModuleUnitLeftIso_formula E))
  exact hu

/-- Evaluation on the image kills its ideal times any module. -/
theorem pointTensorInclusion_unit_zero {X Y : Scheme.{u}} (a : Y ⟶ X)
    (E : X.Modules) :
    pointTensorInclusion a E ≫ (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E = 0 := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).injective
  rw [← Tensor.Bifunctor.tensorBilinear_postcomp]
  ext U x y
  change ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E).app U
    ((pointTensorInclusion a E).app U
      ((Tensor.Bifunctor.tensorBilinear _ E).app U x y)) = 0
  rw [pointTensorInclusion_pure, Scheme.Modules.Hom.app_smul]
  change a.app U ((OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app U x) •
    (show Γ((Scheme.Modules.pullback a).obj E, a ⁻¹ᵁ U) from
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E).app U y) =
        (0 : Γ((Scheme.Modules.pullback a).obj E, a ⁻¹ᵁ U))
  rw [pointIdeal_inclusion_app_zero, zero_smul]

/-- The canonical multiplication map into the kernel of point evaluation. -/
def pointTensorKernelMap {X Y : Scheme.{u}} (a : Y ⟶ X) (E : X.Modules) :
    Tensor.ProductSheaf.tensorModule (OAI.MaximalSeshadri.IdealModule.closedModule a.ker) E ⟶
      kernel ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E) :=
  kernel.lift _ (pointTensorInclusion a E) (pointTensorInclusion_unit_zero a E)

@[simp, reassoc]
theorem pointTensorKernelMap_ι {X Y : Scheme.{u}} (a : Y ⟶ X) (E : X.Modules) :
    pointTensorKernelMap a E ≫ kernel.ι _ = pointTensorInclusion a E :=
  kernel.lift_ι _ _ _

end SteinerGeometry
