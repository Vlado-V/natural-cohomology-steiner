module

public import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors

set_option backward.privateInPublic true
@[expose] public section

/-! Actual maps between framed line sheaves act on every smaller open by
multiplication by the restriction of a single coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.FrameMapCoefficient
open CategoryTheory AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u

/-- The coefficient is obtained by evaluating the actual map in the two frames. -/
def coefficient {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) : Γ(X, U) :=
  Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U
    (eM.inv ≫ f.over U ≫ eN.hom)

/-- Equality of the genuine sheaf morphisms in local frames. -/
theorem over_map_eq_scalar {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    f.over U ≫ eN.hom = eM.hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U (coefficient f U eM eN) := by
  have h := (Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).symm_apply_apply
    (eM.inv ≫ f.over U ≫ eN.hom)
  change Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
    (coefficient f U eM eN) = eM.inv ≫ f.over U ≫ eN.hom at h
  rw [h]
  simp only [Iso.hom_inv_id_assoc]

/-- The same coefficient controls the map on every subopen of the frame open. -/
theorem map_subopen {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} (hVU : V ≤ U) (x : Γ(M, V)) :
    eN.hom.val.app (op (Over.mk (homOfLE hVU))) (f.app V x) =
      (show Γ(X, V) from eM.hom.val.app (op (Over.mk (homOfLE hVU))) x) *
        X.presheaf.map (homOfLE hVU).op (coefficient f U eM eN) := by
  have h := congrArg
    (fun q => q.val.app (op (Over.mk (homOfLE hVU))))
    (over_map_eq_scalar f U eM eN)
  have hx := ConcreteCategory.congr_hom h x
  change eN.hom.val.app (op (Over.mk (homOfLE hVU))) (f.app V x) =
    (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
      (coefficient f U eM eN)).val.app (op (Over.mk (homOfLE hVU)))
        (eM.hom.val.app (op (Over.mk (homOfLE hVU))) x) at hx
  exact hx

theorem base_map_apply {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens)
    (x : ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).obj M).obj (op U)) :
    (((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map f).app (op U)) x =
      f.app U x := rfl

theorem base_frame_apply {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    (U : X.Opens) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U)) :
    (TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso π M U e).hom x =
      e.hom.val.app (op (Over.mk (𝟙 U))) x := rfl

theorem base_scalar_apply {X S : Scheme.{u}} (π : X ⟶ S) (U : X.Opens) (r : Γ(X, U))
    (x : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π
      (Invertible.Scheme.Modules.unitObj X)).obj (op U)) :
    (TwistCechFactors.MvPolynomial.baseModulePresheafObjUnitScalar π U r) x =
      (show Γ(X, U) from x) * r := by
  change (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r).val.app
    (op (Over.mk (𝟙 U))) x = _
  rw [Dual.SheafOfModules.overUnitScalarEnd_app_apply]
  change (show Γ(X, U) from x) * (X.presheaf.map (𝟙 (op U))) r = _
  rw [X.presheaf.map_id]
  rfl

/-- The base-linear Cech factor map is multiplication by the same actual
coefficient after the two frame identifications. -/
theorem base_map_frame {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map f).app (op U) ≫
        (TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso π N U eN).hom =
      (TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso π M U eM).hom ≫
        TwistCechFactors.MvPolynomial.baseModulePresheafObjUnitScalar π U
          (coefficient f U eM eN) := by
  ext x
  simp only [ModuleCat.comp_apply]
  erw [base_scalar_apply, base_frame_apply, base_map_apply]
  have hM := base_frame_apply π M U eM x
  erw [hM]
  have h := map_subopen f U eM eN (le_refl U) x
  simpa only [homOfLE_refl, op_id, X.presheaf.map_id, CommRingCat.id_apply] using h

/-- Restricting both frames restricts their multiplication coefficient. -/
theorem coefficient_restrict {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} (hVU : V ≤ U) :
    coefficient f V
      (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U eM
        (Over.mk (homOfLE hVU)))
      (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N U eN
        (Over.mk (homOfLE hVU))) =
      X.presheaf.map (homOfLE hVU).op (coefficient f U eM eN) := by
  let x : Γ(M, V) :=
    (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U eM
      (Over.mk (homOfLE hVU))).inv.val.app (op (Over.mk (𝟙 V))) (show Γ(X, V) from 1)
  have h := map_subopen f U eM eN hVU x
  have hx : eM.hom.val.app (op (Over.mk (homOfLE hVU))) x = (show Γ(X, V) from 1) := by
    let e := ((SheafOfModules.evaluation (X.ringCatSheaf.over V)
      (op (Over.mk (𝟙 V)))).mapIso
      (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U eM
        (Over.mk (homOfLE hVU)))).toLinearEquiv
    exact e.apply_symm_apply (show Γ(X, V) from 1)
  rw [hx, one_mul] at h
  exact h

/-- The same statement on a smaller open, with coefficient restricted from
the larger frame. -/
theorem base_map_subopen {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    {V : X.Opens} (hVU : V ≤ U) :
    ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map f).app (op V) ≫
      (TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso π N V
        (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf N U eN
          (Over.mk (homOfLE hVU)))).hom =
    (TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso π M V
      (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U eM
        (Over.mk (homOfLE hVU)))).hom ≫
      TwistCechFactors.MvPolynomial.baseModulePresheafObjUnitScalar π V
        (X.presheaf.map (homOfLE hVU).op (coefficient f U eM eN)) := by
  rw [base_map_frame, coefficient_restrict]

end SteinerGeometry.FrameMapCoefficient
