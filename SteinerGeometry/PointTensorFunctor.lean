module

public import SteinerGeometry.PointTensorMap
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorRightNaturality

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

universe u

def actualTensorLeft {X : Scheme.{u}} (I : X.Modules) : X.Modules ⥤ X.Modules where
  obj E := Tensor.ProductSheaf.tensorModule I E
  map g := Tensor.Bifunctor.tensorModuleMap (𝟙 I) g
  map_id E := Tensor.Bifunctor.tensorModuleMap_id I E
  map_comp f g := by
    rw [Tensor.Bifunctor.tensorModuleMap_comp, Category.id_comp]

def pointEvaluationKernelFunctor {X Y : Scheme.{u}} (a : Y ⟶ X) : X.Modules ⥤ X.Modules where
  obj E := kernel ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E)
  map g := kernel.map _ _ g
    (((Scheme.Modules.pullback a) ⋙ Scheme.Modules.pushforward a).map g)
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.naturality g).symm
  map_id E := by
    apply (cancel_mono (kernel.ι _)).mp
    simp
  map_comp f g := by
    apply (cancel_mono (kernel.ι _)).mp
    simp only [kernel.map, Category.assoc, kernel.lift_ι_assoc, kernel.lift_ι]

instance pointEvaluationKernelFunctor_additive {X Y : Scheme.{u}} (a : Y ⟶ X) :
    (pointEvaluationKernelFunctor a).Additive where
  map_add := by
    intro M N f g
    apply (cancel_mono (kernel.ι
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app N))).mp
    simp [pointEvaluationKernelFunctor, kernel.map]

theorem pointTensorInclusion_natural {X Y : Scheme.{u}} (a : Y ⟶ X)
    {E F : X.Modules} (g : E ⟶ F) :
    Tensor.Bifunctor.tensorModuleMap (𝟙 _) g ≫ pointTensorInclusion a F =
      pointTensorInclusion a E ≫ g := by
  dsimp only [pointTensorInclusion]
  rw [Category.assoc, ← Tensor.UnitLeftNaturality.tensorModuleUnitLeftIso_hom_natural]
  simp only [← Category.assoc, Tensor.Bifunctor.tensorModuleMap_comp,
    Category.id_comp, Category.comp_id]
  congr 2

def pointTensorKernelTransformation {X Y : Scheme.{u}} (a : Y ⟶ X) :
    actualTensorLeft (OAI.MaximalSeshadri.IdealModule.closedModule a.ker) ⟶
      pointEvaluationKernelFunctor a where
  app E := pointTensorKernelMap a E
  naturality := by
    intro E F g
    apply (cancel_mono (kernel.ι _)).mp
    dsimp only [pointEvaluationKernelFunctor, actualTensorLeft]
    simp only [Category.assoc, pointTensorKernelMap_ι,
      kernel.map, kernel.lift_ι, pointTensorKernelMap_ι_assoc]
    exact pointTensorInclusion_natural a g

local instance pointTensorFunctorModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Module.SheafMonoidal.moduleMonoidalCategory X

def actualLineTensorFunctorIso {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) :
    (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor ≅
      actualTensorLeft L.sheaf :=
  NatIso.ofComponents
    (fun E => Module.MonoidalTensorComparison.moduleMonoidalTensorIso L.sheaf E)
    (fun g => Module.MonoidalTensorRightNaturality.moduleMonoidalTensorIso_natural_right
      L.sheaf g)

end SteinerGeometry
