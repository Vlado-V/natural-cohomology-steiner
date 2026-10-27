import SteinerGeometry.SheafDual
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.InversePairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PairingRetraction

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.SheafDual
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X Y : Scheme.{u}}

/-- The map to the actual sheaf dual represented by an inverse line pairing. -/
def inversePairingDualMap (K L : Line.Bundles.LineBundle X)
    (e : Tensor.ProductSheaf.tensorModule K.sheaf L.sheaf ≅ Line.Bundles.structureModule X) :
    K.sheaf ⟶ dual L.sheaf :=
  TensorHom.Construction.tensorInternalHomEquiv _ _ _ e.hom

/-- Evaluation recovers the original inverse pairing. -/
theorem inversePairingDualMap_evaluation (K L : Line.Bundles.LineBundle X)
    (e : Tensor.ProductSheaf.tensorModule K.sheaf L.sheaf ≅ Line.Bundles.structureModule X) :
    Tensor.Bifunctor.tensorModuleMap (inversePairingDualMap K L e) (𝟙 L.sheaf) ≫
      LineBundleDual.Construction.lineBundleEvaluation L = e.hom := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).injective
  have he : Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (dual L.sheaf) L.sheaf
      (Line.Bundles.structureModule X) (LineBundleDual.Construction.lineBundleEvaluation L) =
      TensorHom.Construction.sheafBilinearUncurry (𝟙 (dual L.sheaf)) :=
    LineBundleEvaluation.Construction.lineBundleEvaluation_bilinear L
  rw [Tensor.PullbackComparison.tensorHomEquiv_precomp, he]
  change TensorHom.Construction.sheafBilinearUncurry
    (inversePairingDualMap K L e) = _
  exact TensorHom.Construction.sheafBilinearUncurry_curry _

/-- Every inverse line pairing identifies its left line with the sheaf dual. -/
theorem inversePairingDualMap_isIso (K L : Line.Bundles.LineBundle X)
    (e : Tensor.ProductSheaf.tensorModule K.sheaf L.sheaf ≅ Line.Bundles.structureModule X) :
    IsIso (inversePairingDualMap K L e) := by
  have : IsIso (LineBundleDual.Construction.lineBundleEvaluation L) :=
    LineBundleEvaluation.Construction.lineBundleEvaluation_isIso L
  let h := inversePairingDualMap K L e
  let F := (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L).functor
  let a := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso L K.sheaf
  let b := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso L (dual L.sheaf)
  have ht : IsIso (Tensor.Bifunctor.tensorModuleMap h (𝟙 L.sheaf)) := by
    have hc : IsIso (Tensor.Bifunctor.tensorModuleMap h (𝟙 L.sheaf) ≫
        LineBundleDual.Construction.lineBundleEvaluation L) := by
      rw [show Tensor.Bifunctor.tensorModuleMap h (𝟙 L.sheaf) ≫
        LineBundleDual.Construction.lineBundleEvaluation L = e.hom from
          inversePairingDualMap_evaluation K L e]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp hc
  have hn : F.map h ≫ b.hom = a.hom ≫ Tensor.Bifunctor.tensorModuleMap h (𝟙 L.sheaf) :=
    Module.MonoidalTensorNaturality.moduleMonoidalTensorIso_natural_left h L.sheaf
  have hc : IsIso (F.map h ≫ b.hom) := by
    rw [hn]
    infer_instance
  have : IsIso (F.map h) := (isIso_comp_right_iff _ _).mp hc
  exact isIso_of_reflects_iso h F

/-- Canonical identification supplied by an actual inverse pairing. -/
def inversePairingDualIso (K L : Line.Bundles.LineBundle X)
    (e : Tensor.ProductSheaf.tensorModule K.sheaf L.sheaf ≅ Line.Bundles.structureModule X) :
    K.sheaf ≅ dual L.sheaf := by
  have := inversePairingDualMap_isIso K L e
  exact asIso (inversePairingDualMap K L e)

/-- Pulling back the evaluation pairing gives an inverse pairing on the source. -/
def pulledLineEvaluationIso (f : Y ⟶ X) (L : Line.Bundles.LineBundle X) :
    Tensor.ProductSheaf.tensorModule
      ((LineBundleDual.Construction.lineBundleDual L).pullback f).sheaf
      (L.pullback f).sheaf ≅ Line.Bundles.structureModule Y :=
  (Line.Bundles.LineBundle.tensorBaseChangeIso f
    (LineBundleDual.Construction.lineBundleDual L) L).symm ≪≫
      (Scheme.Modules.pullback f).mapIso (LineBundleEvaluation.Construction.lineBundleEvaluationIso L) ≪≫
        Line.Bundles.structureModulePullbackIso f

/-- Line-bundle duals commute with arbitrary actual scheme pullback. -/
def lineDualPullbackIso (f : Y ⟶ X) (L : Line.Bundles.LineBundle X) :
    (Scheme.Modules.pullback f).obj (dual L.sheaf) ≅ dual ((Scheme.Modules.pullback f).obj L.sheaf) :=
  inversePairingDualIso ((LineBundleDual.Construction.lineBundleDual L).pullback f)
    (L.pullback f) (pulledLineEvaluationIso f L)

/-- Evaluation is natural in the original line-bundle map. -/
theorem lineEvaluation_naturality (L M : Line.Bundles.LineBundle X)
    (h : L.sheaf ⟶ M.sheaf) :
    Tensor.Bifunctor.tensorModuleMap (dualMap h) (𝟙 L.sheaf) ≫
        LineBundleDual.Construction.lineBundleEvaluation L =
      Tensor.Bifunctor.tensorModuleMap (𝟙 (dual M.sheaf)) h ≫
        LineBundleDual.Construction.lineBundleEvaluation M := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).injective
  have heL : Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (dual L.sheaf) L.sheaf
      (Line.Bundles.structureModule X) (LineBundleDual.Construction.lineBundleEvaluation L) =
      TensorHom.Construction.sheafBilinearUncurry (𝟙 (dual L.sheaf)) :=
    LineBundleEvaluation.Construction.lineBundleEvaluation_bilinear L
  have heM : Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (dual M.sheaf) M.sheaf
      (Line.Bundles.structureModule X) (LineBundleDual.Construction.lineBundleEvaluation M) =
      TensorHom.Construction.sheafBilinearUncurry (𝟙 (dual M.sheaf)) :=
    LineBundleEvaluation.Construction.lineBundleEvaluation_bilinear M
  rw [Tensor.PullbackComparison.tensorHomEquiv_precomp,
    Tensor.PullbackComparison.tensorHomEquiv_precomp, heL, heM]
  ext U a b
  rfl

/-- Pullback preserves the naturality equation of the line evaluation pairings. -/
theorem pulledLineEvaluation_naturality (f : Y ⟶ X)
    (L M : Line.Bundles.LineBundle X) (h : L.sheaf ⟶ M.sheaf) :
    Tensor.Bifunctor.tensorModuleMap ((Scheme.Modules.pullback f).map (dualMap h))
        (𝟙 (L.pullback f).sheaf) ≫ (pulledLineEvaluationIso f L).hom =
      Tensor.Bifunctor.tensorModuleMap
        (𝟙 ((LineBundleDual.Construction.lineBundleDual M).pullback f).sheaf)
        ((Scheme.Modules.pullback f).map h) ≫ (pulledLineEvaluationIso f M).hom := by
  have hE : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f (dual M.sheaf) L.sheaf) :=
    LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f
      (LineBundleDual.Construction.lineBundleDual M) L
  have hEL : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f (dual L.sheaf) L.sheaf) :=
    LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f
      (LineBundleDual.Construction.lineBundleDual L) L
  have hEM : IsIso (Tensor.PullbackComparison.tensorPullbackComparison f (dual M.sheaf) M.sheaf) :=
    LineBundle.TensorBaseChange.lineBundle_tensorPullbackComparison_isIso f
      (LineBundleDual.Construction.lineBundleDual M) M
  let E := asIso (Tensor.PullbackComparison.tensorPullbackComparison f (dual M.sheaf) L.sheaf)
  let EL := asIso (Tensor.PullbackComparison.tensorPullbackComparison f (dual L.sheaf) L.sheaf)
  let EM := asIso (Tensor.PullbackComparison.tensorPullbackComparison f (dual M.sheaf) M.sheaf)
  have hL : (Scheme.Modules.pullback f).map
        (Tensor.Bifunctor.tensorModuleMap (dualMap h) (𝟙 L.sheaf)) ≫ EL.hom =
      E.hom ≫ Tensor.Bifunctor.tensorModuleMap
        ((Scheme.Modules.pullback f).map (dualMap h)) (𝟙 (L.pullback f).sheaf) := by
    have hh := Tensor.PullbackComparison.tensorPullbackComparison_natural f (dualMap h) (𝟙 L.sheaf)
    rw [(Scheme.Modules.pullback f).map_id] at hh
    exact hh
  have hM : (Scheme.Modules.pullback f).map
        (Tensor.Bifunctor.tensorModuleMap (𝟙 (dual M.sheaf)) h) ≫ EM.hom =
      E.hom ≫ Tensor.Bifunctor.tensorModuleMap
        (𝟙 ((LineBundleDual.Construction.lineBundleDual M).pullback f).sheaf)
        ((Scheme.Modules.pullback f).map h) := by
    have hh := Tensor.PullbackComparison.tensorPullbackComparison_natural f (𝟙 (dual M.sheaf)) h
    rw [(Scheme.Modules.pullback f).map_id] at hh
    exact hh
  apply (cancel_epi E.hom).mp
  change E.hom ≫ Tensor.Bifunctor.tensorModuleMap
      ((Scheme.Modules.pullback f).map (dualMap h)) (𝟙 (L.pullback f).sheaf) ≫
      EL.inv ≫ (Scheme.Modules.pullback f).map (LineBundleDual.Construction.lineBundleEvaluation L) ≫
      (Line.Bundles.structureModulePullbackIso f).hom =
    E.hom ≫ Tensor.Bifunctor.tensorModuleMap
      (𝟙 ((LineBundleDual.Construction.lineBundleDual M).pullback f).sheaf)
      ((Scheme.Modules.pullback f).map h) ≫ EM.inv ≫
      (Scheme.Modules.pullback f).map (LineBundleDual.Construction.lineBundleEvaluation M) ≫
      (Line.Bundles.structureModulePullbackIso f).hom
  rw [← reassoc_of% hL, ← reassoc_of% hM]
  simp only [Iso.hom_inv_id_assoc]
  have hn := congrArg
    (fun z => (Scheme.Modules.pullback f).map z ≫
      (Line.Bundles.structureModulePullbackIso f).hom)
    (lineEvaluation_naturality L M h)
  simpa only [Functor.map_comp, Category.assoc] using hn

/-- Canonical line-dual base change is natural in maps between line bundles. -/
theorem lineDualPullback_naturality (f : Y ⟶ X)
    (L M : Line.Bundles.LineBundle X) (h : L.sheaf ⟶ M.sheaf) :
    (Scheme.Modules.pullback f).map (dualMap h) ≫ (lineDualPullbackIso f L).hom =
      (lineDualPullbackIso f M).hom ≫ dualMap ((Scheme.Modules.pullback f).map h) := by
  let cL := (lineDualPullbackIso f L).hom
  let cM := (lineDualPullbackIso f M).hom
  have hcL : TensorHom.Construction.sheafBilinearUncurry cL =
      Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (pulledLineEvaluationIso f L).hom := by
    exact TensorHom.Construction.sheafBilinearUncurry_curry _
  have hcM : TensorHom.Construction.sheafBilinearUncurry cM =
      Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (pulledLineEvaluationIso f M).hom := by
    exact TensorHom.Construction.sheafBilinearUncurry_curry _
  apply TensorHom.Construction.sheafBilinearCurryEquiv.symm.injective
  have he := congrArg (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _)
    (pulledLineEvaluation_naturality f L M h)
  rw [Tensor.PullbackComparison.tensorHomEquiv_precomp,
    Tensor.PullbackComparison.tensorHomEquiv_precomp] at he
  change TensorHom.Construction.sheafBilinearUncurry
      ((Scheme.Modules.pullback f).map (dualMap h) ≫ cL) =
    TensorHom.Construction.sheafBilinearUncurry
      (cM ≫ dualMap ((Scheme.Modules.pullback f).map h))
  calc
    _ = (TensorHom.Construction.sheafBilinearUncurry cL).precomp
        ((Scheme.Modules.pullback f).map (dualMap h)) (𝟙 _) := by ext U a b; rfl
    _ = (TensorHom.Construction.sheafBilinearUncurry cM).precomp
        (𝟙 _) ((Scheme.Modules.pullback f).map h) := by rw [hcL, hcM]; exact he
    _ = _ := by ext U a b; rfl

end SteinerGeometry.SheafDual
