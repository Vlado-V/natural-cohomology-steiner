module

public import SteinerGeometry.LocalTensorFrames
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalTensorSectionCoherence

set_option backward.privateInPublic true
@[expose] public section

/-! Coherent braiding of arbitrary local pure tensor sections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace SteinerGeometry.LocalTensorCoherence
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
set_option backward.isDefEq.respectTransparency false in
local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)) := by
  change (PresheafOfModules.sheafification
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsLocalization
    (OfModulesMonoidal.PresheafOfModules.sheafificationW
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj))
  infer_instance

local instance (X : Scheme.{u}) :
    (OfModulesMonoidal.PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal := by
  change (OfModulesMonoidal.PresheafOfModules.sheafificationW
    (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
      X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsMonoidal
  infer_instance

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules X.ringCatSheaf) := by
  change MonoidalCategory X.Modules
  exact Monoidal.Scheme.Modules.monoidalCategory X

noncomputable local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory
    (L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    (W := OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
    (Iso.refl _)).Monoidal)


noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Monoidal.Scheme.Modules.symmetricCategory X

noncomputable local instance (X : Scheme.{u}) :
    SymmetricCategory (SheafOfModules X.ringCatSheaf) := by
  change SymmetricCategory X.Modules
  exact Monoidal.Scheme.Modules.symmetricCategory X

noncomputable local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Braided :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory
    (L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    (W := OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
    (Iso.refl _)).Braided)

 theorem monoidalTensorObjIso_inv_braiding {X : Scheme.{u}} (M N : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (β_ M.val N.val).hom ≫
      (TensorSections.monoidalTensorObjIso N M).inv =
    (TensorSections.monoidalTensorObjIso M N).inv ≫ (β_ M N).hom := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let ε (A : X.Modules) := (Invertible.Scheme.Modules.sheafifyValIso A).hom
  have hIso (A B : X.Modules) :
      (TensorSections.monoidalTensorObjIso A B).inv =
        Functor.OplaxMonoidal.δ L A.val B.val ≫ (ε A ⊗ₘ ε B) := by rfl
  dsimp only [L] at hIso ⊢
  rw [hIso, hIso, Functor.map_braiding]
  simp only [Category.assoc]
  erw [Functor.Monoidal.μ_δ_assoc]
  exact congrArg (fun k => Functor.OplaxMonoidal.δ
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) M.val N.val ≫ k)
    (BraidedCategory.braiding_naturality (ε M) (ε N)).symm

/-- Braiding interchanges the factors of every local pure tensor section. -/
theorem braiding_tensorSection {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) :
    (β_ M N).hom.val.app (op U) (TensorSections.tensorSection M N U x y) =
      TensorSections.tensorSection N M U y x := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let t : (M.val ⊗ N.val).obj (op U) := x ⊗ₜ y
  let t' : (N.val ⊗ M.val).obj (op U) := y ⊗ₜ x
  let a := (adj.unit.app (M.val ⊗ N.val)).app (op U) t
  let a' := (adj.unit.app (N.val ⊗ M.val)).app (op U) t'
  have ht : (β_ M.val N.val).hom.app (op U) t = t' := by rfl
  have hunit := adj.unit_naturality (β_ M.val N.val).hom
  have hunitU := congrArg (fun k => k.app (op U)) hunit
  have hunitApply := ConcreteCategory.congr_hom hunitU t
  erw [PresheafOfModules.comp_app, ModuleCat.comp_apply,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hunitApply
  have hLa : (L.map (β_ M.val N.val).hom).val.app (op U) a = a' := by
    dsimp only [a, a']
    exact hunitApply.trans (congrArg
      (fun b => (adj.unit.app (N.val ⊗ M.val)).app (op U) b) ht)
  have hk := monoidalTensorObjIso_inv_braiding M N
  have hkU := congrArg (fun k => k.val.app (op U)) hk
  have hkApply := ConcreteCategory.congr_hom hkU a
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hkApply
  change (β_ M N).hom.val.app (op U)
    ((TensorSections.monoidalTensorObjIso M N).inv.val.app (op U) a) =
      (TensorSections.monoidalTensorObjIso N M).inv.val.app (op U) a'
  exact hkApply.symm.trans (congrArg
    (fun b => (TensorSections.monoidalTensorObjIso N M).inv.val.app (op U) b) hLa)

end SteinerGeometry.LocalTensorCoherence
