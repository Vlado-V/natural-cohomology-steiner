import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSectionComparison

/-! Compatibility of tensor frames with arbitrary local sections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

namespace SteinerGeometry.LocalTensorFrames
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u

local instance localTensorFrames_monoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

/-- A section over an open, regarded as a global section on that open subscheme. -/
def onOpen {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (x : Γ(M,U)) :
    Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)) :=
  (M.restrictAppIso U.ι ⊤).inv
    (M.presheaf.map (eqToHom U.ι_image_top).op x)

/-- Every local section becomes global after extension by direct image. -/
def extended {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (x : Γ(M,U)) :
    Γ((Scheme.Modules.pushforward U.ι).obj (M.restrict U.ι), (⊤ : X.Opens)) := by
  change Γ(M.restrict U.ι, U.ι ⁻¹ᵁ (⊤ : X.Opens))
  exact (M.restrict U.ι).presheaf.map (eqToHom (by simp)).op (onOpen M U x)

theorem unit_local_eq_extended {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (x : Γ(M,U)) :
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val.app (op U) x =
      ((Scheme.Modules.pushforward U.ι).obj (M.restrict U.ι)).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op (extended M U x) := by
  have hunit := ConcreteCategory.congr_hom
    (Scheme.Modules.restrictAdjunction_unit_app_app U.ι M U) x
  refine hunit.trans ?_
  simp only [extended, onOpen, Scheme.Modules.restrictAppIso, Iso.refl_inv]
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  rw [Scheme.Modules.restrict_map, Scheme.Modules.restrict_map]
  change M.presheaf.map _ x = M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ x))
  erw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply]
  congr 2

theorem onOpen_map {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (x : Γ(M,U)) :
    ((Scheme.Modules.restrictFunctor U.ι).map f).val.app (op ⊤) (onOpen M U x) =
      onOpen N U (f.val.app (op U) x) := by
  change f.val.app (op (U.ι ''ᵁ (⊤ : U.toScheme.Opens)))
      (M.presheaf.map (eqToHom U.ι_image_top).op x) =
    N.presheaf.map (eqToHom U.ι_image_top).op (f.val.app (op U) x)
  exact PresheafOfModules.naturality_apply f.val (eqToHom U.ι_image_top).op x

theorem restrict_unit_isIso {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)) := by
  let a := Scheme.Modules.restrictAdjunction U.ι
  have h : (Scheme.Modules.restrictFunctor U.ι).map (a.unit.app M) =
      inv (a.counit.app ((Scheme.Modules.restrictFunctor U.ι).obj M)) := by
    apply (cancel_mono (a.counit.app ((Scheme.Modules.restrictFunctor U.ι).obj M))).1
    rw [IsIso.inv_hom_id]
    change (Scheme.Modules.restrictFunctor U.ι).map (a.unit.app M) ≫
      a.counit.app ((Scheme.Modules.restrictFunctor U.ι).obj M) =
      𝟙 ((Scheme.Modules.restrictFunctor U.ι).obj M)
    exact a.left_triangle_components M
  rw [h]
  infer_instance

/-- Restriction's tensor comparison takes any local pure tensor to the pure
tensor of its two sections on the open subscheme. -/
theorem tensorSection_onOpen {X : Scheme.{u}} (M N : X.Modules)
    (U : X.affineOpens) (x : Γ(M,U.1)) (y : Γ(N,U.1)) :
    (TensorSections.restrictMonoidalTensorIso U.1.ι M N).hom.val.app (op ⊤)
        (onOpen (M ⊗ N) U.1 (TensorSections.tensorSection M N U.1 x y)) =
      TensorSections.tensorSection (M.restrict U.1.ι) (N.restrict U.1.ι) ⊤
        (onOpen M U.1 x) (onOpen N U.1 y) := by
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let : (Scheme.Modules.pullback U.1.ι).Monoidal :=
    PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal U.1.ι
  let : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).symm
  let A := (Scheme.Modules.pushforward U.1.ι).obj (F.obj M)
  let B := (Scheme.Modules.pushforward U.1.ι).obj (F.obj N)
  let a : M ⟶ A := (Scheme.Modules.restrictAdjunction U.1.ι).unit.app M
  let b : N ⟶ B := (Scheme.Modules.restrictAdjunction U.1.ι).unit.app N
  let d := (TensorSections.restrictMonoidalTensorIso U.1.ι M N).hom
  let d' := (TensorSections.restrictMonoidalTensorIso U.1.ι A B).hom
  let z := TensorSections.tensorSection M N U.1 x y
  let : IsIso (F.map a) := restrict_unit_isIso M U.1
  let : IsIso (F.map b) := restrict_unit_isIso N U.1
  have hn := (Functor.OplaxMonoidal.δ_natural F a b).symm
  change F.map (a ⊗ₘ b) ≫ d' = d ≫ (F.map a ⊗ₘ F.map b) at hn
  have hn' := congrArg (fun k => k.val.app (op ⊤) (onOpen (M ⊗ N) U.1 z)) hn
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hn'
  have hlocal :
      (F.map (a ⊗ₘ b)).val.app (op ⊤) (onOpen (M ⊗ N) U.1 z) =
      FrameSections.localTrivializationRestriction (A ⊗ B) U
        (TensorSections.tensorSection A B ⊤ (extended M U.1 x) (extended N U.1 y)) := by
    rw [onOpen_map, TensorFrameSections.tensorSection_map]
    change onOpen (A ⊗ B) U.1
        (TensorSections.tensorSection A B U.1 _ _) =
      onOpen (A ⊗ B) U.1
        ((A ⊗ B).presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
          (TensorSections.tensorSection A B ⊤ _ _))
    have hx := unit_local_eq_extended M U.1 x
    have hy := unit_local_eq_extended N U.1 y
    have hxy := congrArg₂ (TensorSections.tensorSection A B U.1) hx hy
    have ht := TensorSections.tensorSection_restrict A B (le_top : U.1 ≤ ⊤)
      (extended M U.1 x) (extended N U.1 y)
    exact congrArg (onOpen (A ⊗ B) U.1) (hxy.trans ht.symm)
  have hg := TensorFrameSections.tensorSection_localTrivializationRestriction A B U
    (extended M U.1 x) (extended N U.1 y)
  have hright :
      (F.map a ⊗ₘ F.map b).val.app (op ⊤)
        (TensorSections.tensorSection (F.obj M) (F.obj N) ⊤
          (onOpen M U.1 x) (onOpen N U.1 y)) =
      TensorSections.tensorSection (F.obj A) (F.obj B) ⊤
        (FrameSections.localTrivializationRestriction A U (extended M U.1 x))
        (FrameSections.localTrivializationRestriction B U (extended N U.1 y)) := by
    rw [TensorFrameSections.tensorSection_map, onOpen_map, onOpen_map]
    change TensorSections.tensorSection (F.obj A) (F.obj B) ⊤
        (onOpen A U.1 (a.val.app (op U.1) x))
        (onOpen B U.1 (b.val.app (op U.1) y)) = _
    have hx := congrArg (onOpen A U.1) (unit_local_eq_extended M U.1 x)
    have hy := congrArg (onOpen B U.1) (unit_local_eq_extended N U.1 y)
    exact congrArg₂ (TensorSections.tensorSection (F.obj A) (F.obj B) ⊤) hx hy
  let ef : F.obj M ⊗ F.obj N ≅ F.obj A ⊗ F.obj B := asIso (F.map a ⊗ₘ F.map b)
  let eApp := (SheafOfModules.evaluation U.1.toScheme.ringCatSheaf (op ⊤)).mapIso ef
  apply eApp.toLinearEquiv.injective
  exact hn'.symm.trans ((congrArg (fun v => d'.val.app (op ⊤) v) hlocal).trans
    (hg.trans hright.symm))

/-- The coefficient of a local section in a frame on the open subscheme. -/
def coefficient {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (x : Γ(M,U.1)) : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
  e.hom.val.app (op ⊤) (onOpen M U.1 x)

/-- Local tensor-frame coefficients multiply for arbitrary local sections. -/
theorem coefficient_tensorSection {X : Scheme.{u}} (M N : X.Modules)
    (U : X.affineOpens)
    (eM : M.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (eN : N.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (x : Γ(M,U.1)) (y : Γ(N,U.1)) :
    coefficient (M ⊗ N) U
      (TensorSections.restrictMonoidalTensorIso U.1.ι M N ≪≫
        (eM ⊗ᵢ eN) ≪≫ TensorSections.unitObjTensorIso U.1.toScheme)
      (TensorSections.tensorSection M N U.1 x y) =
      coefficient M U eM x * coefficient N U eN y := by
  change (TensorSections.unitObjTensorIso U.1.toScheme).hom.val.app (op ⊤)
      ((eM.hom ⊗ₘ eN.hom).val.app (op ⊤)
        ((TensorSections.restrictMonoidalTensorIso U.1.ι M N).hom.val.app (op ⊤)
          (onOpen (M ⊗ N) U.1 (TensorSections.tensorSection M N U.1 x y)))) = _
  rw [tensorSection_onOpen, TensorFrameSections.tensorSection_map]
  exact TensorFrameSections.unitObjTensorIso_hom_tensorSection_top U.1.toScheme _ _

/-- The subscheme coefficient agrees with the over-site frame coefficient. -/
theorem coefficient_restrictTrivializationOfOverIso {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (x : Γ(M,U.1)) :
    coefficient M U (FrameSections.restrictTrivializationOfOverIso M U.1 e) x =
      FrameSections.affineOpenTopSection U (e.hom.val.app (op (Over.mk (𝟙 U.1))) x) := by
  unfold coefficient
  rw [FrameSectionComparison.restrictTrivializationOfOverIso_hom_top_apply]
  rw [FrameSectionComparison.affineOpenTopSection_eq_overMap_terminal]
  let V := U.1.overEquivalence.symm.functor.obj (⊤ : U.1.toScheme.Opens)
  let k : V ⟶ Over.mk (𝟙 U.1) := Over.mkIdTerminal.from V
  have h := PresheafOfModules.naturality_apply e.hom.val k.op x
  change e.hom.val.app (op V) ((M.over U.1).val.map k.op x) =
    (X.ringCatSheaf.over U.1).obj.map k.op (e.hom.val.app (op (Over.mk (𝟙 U.1))) x) at h
  have hm : ((Scheme.Modules.overFunctorEquiv U.1).inv.app M).val.app (op ⊤)
      (onOpen M U.1 x) = (M.over U.1).val.map k.op x := by
    change M.presheaf.map (eqToHom U.1.ι_image_top).op x = M.presheaf.map k.left.op x
    exact congrArg (fun f => M.presheaf.map f x) (Subsingleton.elim _ _)
  exact (congrArg (fun y => e.hom.val.app (op V) y) hm).trans h

theorem coefficient_overSection {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (r : Γ(X,U.1)) :
    coefficient M U (FrameSections.restrictTrivializationOfOverIso M U.1 e)
      (FrameSections.overTrivializationSection M U.1 e r) =
      FrameSections.affineOpenTopSection U r := by
  rw [coefficient_restrictTrivializationOfOverIso,
    FrameSections.overTrivializationSection_coefficient]

end SteinerGeometry.LocalTensorFrames
