import SteinerGeometry.PointTensorUnit
import SteinerGeometry.PointTensorFunctor
import SteinerGeometry.TensorFactorRestriction
import SteinerGeometry.PointKernelRestriction

/-! Open restriction of the actual point-ideal evaluation kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

/-- The ideal of a closed immersion restricts to the ideal of its open base change. -/
def pointIdealRestrictIso {X Y : Scheme.{u}} (a : Y ⟶ X) [IsClosedImmersion a]
    (U : X.Opens) :
    (OAI.MaximalSeshadri.IdealModule.closedModule a.ker).restrict U.ι ≅
      OAI.MaximalSeshadri.IdealModule.closedModule (a ∣_ U).ker :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso (pointIdealEvaluationIso a) ≪≫
    pointKernelRestrictIso a U (Line.Bundles.structureModule X) ≪≫
      (pointEvaluationKernelFunctor (a ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
        (pointIdealEvaluationIso (a ∣_ U)).symm

/-- This ideal comparison preserves the actual inclusion into the structure sheaf. -/
@[reassoc]
theorem pointIdealRestrictIso_inclusion {X Y : Scheme.{u}} (a : Y ⟶ X)
    [IsClosedImmersion a] (U : X.Opens) :
    (pointIdealRestrictIso a U).hom ≫
        OAI.MaximalSeshadri.IdealModule.inclusion (a ∣_ U).ker.subschemeι =
      (Scheme.Modules.restrictFunctor U.ι).map
          (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom := by
  have hi : (pointIdealEvaluationIso (a ∣_ U)).inv ≫
      OAI.MaximalSeshadri.IdealModule.inclusion (a ∣_ U).ker.subschemeι =
      kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction (a ∣_ U)).unit.app
        (Line.Bundles.structureModule U.toScheme)) := by
    rw [← pointIdealEvaluationIso_ι, Iso.inv_hom_id_assoc]
  simp only [pointIdealRestrictIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, hi]
  simp only [pointEvaluationKernelFunctor, kernel.map, kernel.lift_ι]
  rw [pointKernelRestrictIso_ι_assoc, ← Category.assoc, ← Functor.map_comp,
    pointIdealEvaluationIso_ι]

/-- Restriction and the ideal comparison identify the point-ideal tensor source. -/
def pointTensorSourceRestrictIso {X Y : Scheme.{u}} (a : Y ⟶ X)
    [IsClosedImmersion a] (U : X.Opens) (E : X.Modules) :
    Tensor.ProductSheaf.tensorModule
        (OAI.MaximalSeshadri.IdealModule.closedModule (a ∣_ U).ker) (E.restrict U.ι) ≅
      (Tensor.ProductSheaf.tensorModule
        (OAI.MaximalSeshadri.IdealModule.closedModule a.ker) E).restrict U.ι :=
  Tensor.Bifunctor.tensorModuleMapIso (pointIdealRestrictIso a U).symm (Iso.refl _) ≪≫
    asIso (tensorRestrictComparison U.ι
      (OAI.MaximalSeshadri.IdealModule.closedModule a.ker) E)

/-- Pure-tensor multiplication agrees with open restriction and the ideal comparison. -/
theorem pointTensorInclusion_restrict {X Y : Scheme.{u}} (a : Y ⟶ X)
    [IsClosedImmersion a] (U : X.Opens) (E : X.Modules) :
    tensorRestrictComparison U.ι (OAI.MaximalSeshadri.IdealModule.closedModule a.ker) E ≫
        (Scheme.Modules.restrictFunctor U.ι).map (pointTensorInclusion a E) =
      Tensor.Bifunctor.tensorModuleMap (pointIdealRestrictIso a U).hom (𝟙 _) ≫
        pointTensorInclusion (a ∣_ U) (E.restrict U.ι) := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).injective
  rw [← Tensor.Bifunctor.tensorBilinear_postcomp,
    ← Tensor.Bifunctor.tensorBilinear_postcomp]
  ext V x y
  change ((Scheme.Modules.restrictFunctor U.ι).map (pointTensorInclusion a E)).app V
      ((tensorRestrictComparison U.ι _ E).app V
        ((Tensor.Bifunctor.tensorBilinear _ _).app V x y)) =
    (pointTensorInclusion (a ∣_ U) (E.restrict U.ι)).app V
      ((Tensor.Bifunctor.tensorModuleMap (pointIdealRestrictIso a U).hom (𝟙 _)).app V
        ((Tensor.Bifunctor.tensorBilinear _ _).app V x y))
  rw [tensorRestrictComparison_pure]
  have hm := congrArg (fun β => β.app V x y)
    (Tensor.Bifunctor.tensorModuleMap_spec (pointIdealRestrictIso a U).hom (𝟙 (E.restrict U.ι)))
  change (Tensor.Bifunctor.tensorModuleMap (pointIdealRestrictIso a U).hom (𝟙 _)).app V
      ((Tensor.Bifunctor.tensorBilinear _ _).app V x y) =
    (Tensor.Bifunctor.tensorBilinear _ _).app V ((pointIdealRestrictIso a U).hom.app V x) y at hm
  rw [hm, pointTensorInclusion_pure]
  change (pointTensorInclusion a E).app (U.ι ''ᵁ V)
      ((Tensor.Bifunctor.tensorBilinear _ _).app (U.ι ''ᵁ V) x y) = _
  rw [pointTensorInclusion_pure]
  have hv := congrArg (fun f => f.app V x) (pointIdealRestrictIso_inclusion a U)
  change (OAI.MaximalSeshadri.IdealModule.inclusion (a ∣_ U).ker.subschemeι).app V
      ((pointIdealRestrictIso a U).hom.app V x) =
    (U.ι.appIso V).hom
      ((OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app (U.ι ''ᵁ V) x) at hv
  rw [hv]
  change (show Γ(X, U.ι ''ᵁ V) from
      (OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app (U.ι ''ᵁ V) x) •
      (show Γ(E, U.ι ''ᵁ V) from y) =
    (U.ι.appIso V).inv ((U.ι.appIso V).hom
      ((OAI.MaximalSeshadri.IdealModule.inclusion a.ker.subschemeι).app (U.ι ''ᵁ V) x)) •
      (show Γ(E, U.ι ''ᵁ V) from y)
  simp
  rfl

/-- The canonical tensor-to-kernel map is unchanged under open restriction,
through the actual source and target comparison isomorphisms. -/
theorem pointTensorKernelMap_restrict {X Y : Scheme.{u}} (a : Y ⟶ X)
    [IsClosedImmersion a] (U : X.Opens) (E : X.Modules) :
    (pointTensorSourceRestrictIso a U E).hom ≫
        (Scheme.Modules.restrictFunctor U.ι).map (pointTensorKernelMap a E) ≫
        (pointKernelRestrictIso a U E).hom =
      pointTensorKernelMap (a ∣_ U) (E.restrict U.ι) := by
  apply (cancel_mono (kernel.ι _)).mp
  simp only [Category.assoc, pointKernelRestrictIso_ι,
    ← Functor.map_comp, pointTensorKernelMap_ι]
  change (Tensor.Bifunctor.tensorModuleMap (pointIdealRestrictIso a U).inv (𝟙 _) ≫
    tensorRestrictComparison U.ι (OAI.MaximalSeshadri.IdealModule.closedModule a.ker) E) ≫
    (Scheme.Modules.restrictFunctor U.ι).map (pointTensorInclusion a E) =
      pointTensorInclusion (a ∣_ U) (E.restrict U.ι)
  rw [Category.assoc, pointTensorInclusion_restrict, ← Category.assoc,
    Tensor.Bifunctor.tensorModuleMap_comp, Iso.inv_hom_id, Category.id_comp,
    Tensor.Bifunctor.tensorModuleMap_id, Category.id_comp]

end SteinerGeometry
