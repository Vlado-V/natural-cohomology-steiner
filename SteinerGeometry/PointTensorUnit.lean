import SteinerGeometry.PointTensorMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitRight

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

private theorem pointTensor_mono_app_injective {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Mono f] (U : X.Opens) : Function.Injective (f.app U) := by
  have : Mono f.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map f))
  exact PresheafOfModules.injective_of_mono f.val (.op U)

def pointIdealImageComparison {X Y : Scheme.{u}} (a : Y ⟶ X) :
    OAI.MaximalSeshadri.IdealModule.closedModule a.ker ⟶
      OAI.MaximalSeshadri.IdealModule.idealModule a :=
  kernel.lift _ (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι) (by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    exact pointIdeal_inclusion_app_zero a U x)

@[simp, reassoc]
theorem pointIdealImageComparison_inclusion {X Y : Scheme.{u}} (a : Y ⟶ X) :
    pointIdealImageComparison a ≫ OAI.MaximalSeshadri.IdealModule.inclusion a =
      OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι := kernel.lift_ι _ _ _

instance pointIdealImageComparison_isIso {X Y : Scheme.{u}} (a : Y ⟶ X)
    [IsClosedImmersion a] : IsIso (pointIdealImageComparison a) := by
  apply OAI.MaximalSeshadri.IdealModule.isIso_of_affine_app
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have h₁ := pointTensor_mono_app_injective
    (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι) U.1
  have h₂ := pointTensor_mono_app_injective
    (OAI.MaximalSeshadri.IdealModule.inclusion a) U.1
  have hc (x : Γ(OAI.MaximalSeshadri.IdealModule.closedModule a.ker, U.1)) :=
    congrArg (fun f => f.app U.1 x) (pointIdealImageComparison_inclusion a)
  constructor
  · intro x y hxy
    apply h₁
    exact (hc x).symm.trans ((congrArg _ hxy).trans (hc y))
  · intro y
    have hy : (OAI.MaximalSeshadri.IdealModule.inclusion a).app U.1 y ∈ a.ker.ideal U := by
      rw [← OAI.MaximalSeshadri.IdealModule.image_eq_ideal a U]
      exact ⟨y, rfl⟩
    rw [← OAI.MaximalSeshadri.IdealModule.closed_image a.ker U] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, h₂ ((hc x).trans hx)⟩

def pointEvaluationUnitKernelIso {X Y : Scheme.{u}} (a : Y ⟶ X) :
    kernel ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
      (Line.Bundles.structureModule X)) ≅ OAI.MaximalSeshadri.IdealModule.idealModule a :=
    kernel.mapIso
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app (Line.Bundles.structureModule X))
      (OAI.MaximalSeshadri.IdealModule.structureMap a) (Iso.refl _)
      ((Scheme.Modules.pushforward a).mapIso (Line.Bundles.structureModulePullbackIso a))
      (by
        change _ = (𝟙 _) ≫ _
        rw [Category.id_comp]
        exact Tensor.PullbackUnits.structureModulePullbackIso_unit a)

theorem pointEvaluationUnitKernelIso_hom_ι {X Y : Scheme.{u}} (a : Y ⟶ X) :
    (pointEvaluationUnitKernelIso a).hom ≫ OAI.MaximalSeshadri.IdealModule.inclusion a =
      kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
        (Line.Bundles.structureModule X)) := by
  change kernel.lift _ _ _ ≫ kernel.ι _ = _
  rw [kernel.lift_ι]
  exact Category.comp_id _

theorem pointEvaluationUnitKernelIso_inv_ι {X Y : Scheme.{u}} (a : Y ⟶ X) :
    (pointEvaluationUnitKernelIso a).inv ≫
      kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
        (Line.Bundles.structureModule X)) = OAI.MaximalSeshadri.IdealModule.inclusion a := by
  apply (cancel_epi (pointEvaluationUnitKernelIso a).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    pointEvaluationUnitKernelIso_hom_ι]

def pointIdealEvaluationIso {X Y : Scheme.{u}} (a : Y ⟶ X) [IsClosedImmersion a] :
    OAI.MaximalSeshadri.IdealModule.closedModule a.ker ≅
      kernel ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
        (Line.Bundles.structureModule X)) :=
  asIso (pointIdealImageComparison a) ≪≫ (pointEvaluationUnitKernelIso a).symm

@[simp, reassoc]
theorem pointIdealEvaluationIso_ι {X Y : Scheme.{u}} (a : Y ⟶ X) [IsClosedImmersion a] :
    (pointIdealEvaluationIso a).hom ≫ kernel.ι _ =
      OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι := by
  change pointIdealImageComparison a ≫ (pointEvaluationUnitKernelIso a).inv ≫ _ = _
  rw [pointEvaluationUnitKernelIso_inv_ι]
  exact pointIdealImageComparison_inclusion a

theorem pointTensorInclusion_unit {X Y : Scheme.{u}} (a : Y ⟶ X) :
    pointTensorInclusion a (Line.Bundles.structureModule X) =
      (Tensor.UnitRight.tensorModuleUnitRightIso
        (OAI.MaximalSeshadri.IdealModule.closedModule a.ker)).hom ≫
          OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).injective
  rw [← Tensor.Bifunctor.tensorBilinear_postcomp,
    ← Tensor.Bifunctor.tensorBilinear_postcomp]
  apply Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro r
  change (pointTensorInclusion a (Line.Bundles.structureModule X)).app U
      ((Tensor.Bifunctor.tensorBilinear _ _).app U x r) =
    (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app U
      ((Tensor.UnitRight.tensorModuleUnitRightIso _).hom.app U
        ((Tensor.Bifunctor.tensorBilinear _ _).app U x r))
  rw [pointTensorInclusion_pure]
  have hu := Tensor.UnitRight.tensorModuleUnitRightIso_pairing
    (OAI.MaximalSeshadri.IdealModule.closedModule a.ker) U x r
  have hi := congrArg (fun z =>
    (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app U z) hu
  have hs := (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app_smul r x
  exact (mul_comm (show Γ(X, U) from
    (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app U x)
      (show Γ(X, U) from r)).trans (hs.symm.trans hi.symm)

instance pointTensorKernelMap_unit_isIso {X Y : Scheme.{u}} (a : Y ⟶ X)
    [IsClosedImmersion a] : IsIso (pointTensorKernelMap a (Line.Bundles.structureModule X)) := by
  have he : pointTensorKernelMap a (Line.Bundles.structureModule X) =
      (Tensor.UnitRight.tensorModuleUnitRightIso
        (OAI.MaximalSeshadri.IdealModule.closedModule a.ker)).hom ≫
          (pointIdealEvaluationIso a).hom := by
    apply (cancel_mono (kernel.ι _)).mp
    rw [pointTensorKernelMap_ι, Category.assoc, pointIdealEvaluationIso_ι,
      pointTensorInclusion_unit]
  rw [he]
  infer_instance

end SteinerGeometry
