import SteinerGeometry.DualModelComparison
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleCancellationPairing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence

/-! Compatibility of scalar dual maps with the actual evaluation tensor. -/
noncomputable section

namespace SteinerGeometry.ScalarDualTensor

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective

universe u
variable {X : Scheme.{u}}

local instance : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

local instance : ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  Dual.Scheme.Modules.schemeSectionsMulCommutative X

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equality out of the sheaf tensor may be checked on local pure tensors. -/
theorem tensor_hom_ext {M N P : X.Modules} {f g : M ⊗ N ⟶ P}
    (h : ∀ (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)),
      f.val.app (.op U) (TensorSections.tensorSection M N U x y) =
        g.val.app (.op U) (TensorSections.tensorSection M N U x y)) : f = g := by
  let e := TensorSections.monoidalTensorObjIso M N
  apply (cancel_epi e.inv).1
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv (M.val ⊗ N.val) P).injective
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
  exact h U.unop x y

/-- Evaluation is natural in the module and contravariant in its dual. -/
theorem dualPairing_naturality {M N : X.Modules} (f : M ⟶ N) :
    (f ⊗ₘ 𝟙 (Dual.Scheme.Modules.dualObj N)) ≫ TensorFrameSections.dualPairing N =
      (𝟙 M ⊗ₘ Dual.Scheme.Modules.dualMapObj f) ≫ TensorFrameSections.dualPairing M := by
  apply tensor_hom_ext
  intro U x φ
  change (TensorFrameSections.dualPairing N).val.app (.op U)
      ((f ⊗ₘ 𝟙 (Dual.Scheme.Modules.dualObj N)).val.app (.op U)
        (TensorSections.tensorSection M (Dual.Scheme.Modules.dualObj N) U x φ)) =
    (TensorFrameSections.dualPairing M).val.app (.op U)
      ((𝟙 M ⊗ₘ Dual.Scheme.Modules.dualMapObj f).val.app (.op U)
        (TensorSections.tensorSection M (Dual.Scheme.Modules.dualObj N) U x φ))
  rw [TensorFrameSections.tensorSection_map, TensorFrameSections.tensorSection_map]
  change (TensorFrameSections.dualPairing N).val.app (.op U)
      (TensorSections.tensorSection N (Dual.Scheme.Modules.dualObj N) U
        (f.val.app (.op U) x) φ) =
    (TensorFrameSections.dualPairing M).val.app (.op U)
      (TensorSections.tensorSection M (Dual.Scheme.Modules.dualObj M) U x
        ((Dual.Scheme.Modules.dualMapObj f).val.app (.op U) φ))
  rw [TensorFrameSections.dualPairing_tensorSection,
    TensorFrameSections.dualPairing_tensorSection]
  simp only [Evaluation.SheafOfModules.evalSection_eq]
  change φ.val.app (.op (Over.mk (𝟙 U)))
      (N.val.map (𝟙 U).op (f.val.app (.op U) x)) =
    φ.val.app (.op (Over.mk (𝟙 U)))
      (f.val.app (.op U) (M.val.map (𝟙 U).op x))
  simp

/-- Functionals on an invertible sheaf satisfy the rank-one cross identity. -/
theorem evalSection_cross {M : X.Modules}
    (hM : Invertible.Scheme.Modules.IsInvertible M)
    (U : X.Opens) (φ ψ : Γ(Dual.Scheme.Modules.dualObj M, U))
    (x y : Γ(M, U)) :
    Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U φ x *
        Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U ψ y =
      Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U ψ x *
        Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U φ y := by
  obtain ⟨I, V, hV, htriv⟩ := hM
  apply X.sheaf.eq_of_locally_eq' (fun i : I => U ⊓ V i) U
    (fun _ => homOfLE inf_le_left)
  · rw [← inf_iSup_eq, hV, inf_top_eq]
  intro i
  obtain ⟨e⟩ := htriv i
  let W : X.Opens := U ⊓ V i
  let k : (.op U : X.Opensᵒᵖ) ⟶ .op W := (homOfLE inf_le_left).op
  let t := Invertible.Scheme.Modules.overTrivializationOfRestrictIso M W
    (Invertible.Scheme.Modules.restrictIsoOfPullbackIso M W
      (Invertible.Scheme.Modules.restrictTrivialization inf_le_right e))
  rw [map_mul, map_mul]
  change X.ringCatSheaf.obj.map k
      (Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U φ x) *
    X.ringCatSheaf.obj.map k
      (Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U ψ y) =
    X.ringCatSheaf.obj.map k
      (Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U ψ x) *
    X.ringCatSheaf.obj.map k
      (Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U φ y)
  rw [← Evaluation.SheafOfModules.evalSection_naturality X.ringCatSheaf M k,
    ← Evaluation.SheafOfModules.evalSection_naturality X.ringCatSheaf M k,
    ← Evaluation.SheafOfModules.evalSection_naturality X.ringCatSheaf M k,
    ← Evaluation.SheafOfModules.evalSection_naturality X.ringCatSheaf M k]
  rw [InvertibleEvaluation.SheafOfModules.evalSection_factor X.ringCatSheaf M W t
      (Dual.SheafOfModules.dualRestrict X.ringCatSheaf M k φ) (M.val.map k x),
    InvertibleEvaluation.SheafOfModules.evalSection_factor X.ringCatSheaf M W t
      (Dual.SheafOfModules.dualRestrict X.ringCatSheaf M k ψ) (M.val.map k y),
    InvertibleEvaluation.SheafOfModules.evalSection_factor X.ringCatSheaf M W t
      (Dual.SheafOfModules.dualRestrict X.ringCatSheaf M k ψ) (M.val.map k x),
    InvertibleEvaluation.SheafOfModules.evalSection_factor X.ringCatSheaf M W t
      (Dual.SheafOfModules.dualRestrict X.ringCatSheaf M k φ) (M.val.map k y)]
  ac_rfl

/-- The scalar dual sends a scalar to that scalar times the given functional. -/
theorem scalarDual_app_apply {M : X.Modules}
    (g : M ⟶ Invertible.Scheme.Modules.unitObj X)
    (U : X.Opens) (r : Γ(X, U)) (V : (Over U)ᵒᵖ)
    (y : (M.over U).val.obj V) :
    (((Dual.Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
      Dual.Scheme.Modules.dualMapObj g).val.app (.op U)
        (show Γ(Invertible.Scheme.Modules.unitObj X, U) from r)).val.app V y =
      (show Γ(X, V.unop.left) from g.val.app (.op V.unop.left) y) *
        X.presheaf.map V.unop.hom.op r := by
  rfl

theorem evalSection_restrict_apply {M : X.Modules} {U W : X.Opens}
    (i : W ⟶ U) (φ : Γ(Dual.Scheme.Modules.dualObj M, U))
    (y : Γ(M, W)) :
    Evaluation.SheafOfModules.evalSection X.ringCatSheaf M W
      (Dual.SheafOfModules.dualRestrict X.ringCatSheaf M i.op φ) y =
      φ.val.app (.op (Over.mk i)) y := by
  simp only [Evaluation.SheafOfModules.evalSection_eq]
  change φ.val.app (.op (Over.mk ((𝟙 W) ≫ i))) (M.val.map (𝟙 W).op y) = _
  rw [Category.id_comp, op_id, M.val.map_id]
  rfl

theorem scalarDual_eval {M : X.Modules}
    (g : M ⟶ Invertible.Scheme.Modules.unitObj X)
    (U : X.Opens) (r : Γ(X, U)) (x : Γ(M, U)) :
    Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U
      (((Dual.Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
        Dual.Scheme.Modules.dualMapObj g).val.app (.op U) r) x =
      (show Γ(X, U) from g.val.app (.op U) x) * r := by
  simp only [Evaluation.SheafOfModules.evalSection_eq]
  rw [scalarDual_app_apply]
  simp

theorem scalarDual_rankOne {M : X.Modules}
    (hM : Invertible.Scheme.Modules.IsInvertible M)
    (g : M ⟶ Invertible.Scheme.Modules.unitObj X)
    (U : X.Opens) (x : Γ(M, U)) (φ : Γ(Dual.Scheme.Modules.dualObj M, U)) :
    (show Γ(X, U) from g.val.app (.op U) x) • φ =
      ((Dual.Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
        Dual.Scheme.Modules.dualMapObj g).val.app (.op U)
          (Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U φ x) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [scalarDual_app_apply]
  change (show Γ(X, V.unop.left) from φ.val.app V y) *
      X.presheaf.map V.unop.hom.op (g.val.app (.op U) x) = _
  let k := V.unop.hom.op
  let φ' := Dual.SheafOfModules.dualRestrict X.ringCatSheaf M k φ
  let x' := M.val.map k x
  let ψ := ((Dual.Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
    Dual.Scheme.Modules.dualMapObj g).val.app (.op V.unop.left)
      (show Γ(Invertible.Scheme.Modules.unitObj X, V.unop.left) from
        (1 : Γ(X, V.unop.left)))
  have hcross := evalSection_cross hM V.unop.left φ' ψ x' y
  rw [scalarDual_eval, scalarDual_eval, mul_one, mul_one] at hcross
  have hφy : Evaluation.SheafOfModules.evalSection X.ringCatSheaf M
      V.unop.left φ' y = φ.val.app V y :=
    evalSection_restrict_apply V.unop.hom φ y
  have hφx := Evaluation.SheafOfModules.evalSection_naturality
    X.ringCatSheaf M k φ x
  have hg := PresheafOfModules.naturality_apply g.val k x
  change (show Γ(X, V.unop.left) from g.val.app (.op V.unop.left) x') =
    X.presheaf.map k (g.val.app (.op U) x) at hg
  change Evaluation.SheafOfModules.evalSection X.ringCatSheaf M V.unop.left φ' x' =
    X.presheaf.map k (Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U φ x) at hφx
  rw [hφx, hφy, hg] at hcross
  exact (mul_comm' _ _).trans (hcross.symm.trans (mul_comm' _ _))

set_option maxHeartbeats 1600000

def unitLeftIso (M : X.Modules) : Invertible.Scheme.Modules.unitObj X ⊗ M ≅ M :=
  ((TensorSections.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl M) ≪≫ λ_ M

theorem unitLeftIso_sheafification (M : X.Modules) :
    (TensorSections.monoidalTensorObjIso (Invertible.Scheme.Modules.unitObj X) M).inv ≫
      (unitLeftIso M).hom =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (λ_ M.val).hom ≫
      (Invertible.Scheme.Modules.sheafifyValIso M).hom := by
  let : (OfModulesMonoidal.PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @OfModulesMonoidal.PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let F : X.PresheafOfModules ⥤ X.Modules :=
    Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)
  let : F.Monoidal := by
    change (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)).Monoidal
    infer_instance
  let c := TensorSections.monoidalUnitObjIso X
  let d := Invertible.Scheme.Modules.sheafifyValIso M
  change (Localization.Monoidal.μ
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _) (Invertible.Scheme.Modules.unitObj X).val M.val).inv ≫
      (c.hom ⊗ₘ d.hom) ≫ (c.inv ⊗ₘ 𝟙 M) ≫ (λ_ M).hom =
    F.map (λ_ M.val).hom ≫ d.hom
  rw [← Category.assoc (c.hom ⊗ₘ d.hom), tensorHom_comp_tensorHom,
    c.hom_inv_id, Category.comp_id, id_tensorHom, leftUnitor_naturality]
  change Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) M.val ≫
      (λ_ (F.obj M.val)).hom ≫ d.hom = _
  have h := Functor.OplaxMonoidal.left_unitality_hom_assoc F M.val d.hom
  have heta : Functor.OplaxMonoidal.η F = 𝟙 _ := rfl
  rw [heta, id_whiskerRight, Category.id_comp] at h
  exact h

theorem unitLeftIso_tensorSection (M : X.Modules) (U : X.Opens) (r : Γ(X, U)) (y : Γ(M,U)) :
    (unitLeftIso M).hom.val.app (.op U)
      (TensorSections.tensorSection (Invertible.Scheme.Modules.unitObj X) M U r y) = r • y := by
  let A := Invertible.Scheme.Modules.unitObj X
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let c := Invertible.Scheme.Modules.sheafifyValIso M
  let q₀ : (A.val ⊗ M.val).obj (.op U) := r ⊗ₜ y
  let uq := (adj.unit.app (A.val ⊗ M.val)).app (.op U) q₀
  have hmor := unitLeftIso_sheafification M
  have hmorU := congrArg (fun k => k.val.app (.op U)) hmor
  have hmorApply := ConcreteCategory.congr_hom hmorU uq
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hmorApply
  change (unitLeftIso M).hom.val.app (.op U)
      ((TensorSections.monoidalTensorObjIso A M).inv.val.app (.op U) uq) = _
  rw [hmorApply]
  let f := (λ_ M.val).hom
  have hnat := adj.unit_naturality f
  have htri := adj.right_triangle_components M
  change adj.unit.app (A.val ⊗ M.val) ≫ (L.map f).val =
    f ≫ adj.unit.app M.val at hnat
  change adj.unit.app M.val ≫ c.hom.val = 𝟙 M.val at htri
  have hpresheaf :
      adj.unit.app (A.val ⊗ M.val) ≫ (L.map f).val ≫ c.hom.val = f := by
    rw [← Category.assoc, hnat, Category.assoc, htri, Category.comp_id]
  have hpresheafU := congrArg (fun k => k.app (.op U)) hpresheaf
  have hpresheafApply := ConcreteCategory.congr_hom hpresheafU q₀
  erw [PresheafOfModules.comp_app, ModuleCat.comp_apply,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hpresheafApply
  have hleft : ((λ_ M.val).hom.app (.op U)) q₀ = r • y := by
    have happ := PresheafOfModulesOfCommRing.leftUnitor_hom_app M.val (.op U)
    have heval := ConcreteCategory.congr_hom happ q₀
    exact heval.trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply r y)
  dsimp only [uq]
  exact hpresheafApply.trans hleft

/-- For a line bundle, dualizing a scalar map is its tensor by the dual line,
transported through the actual evaluation and unit isomorphisms. -/
@[reassoc]
theorem scalarDual_tensor_bridge (L : X.Modules)
    (hL : Invertible.Scheme.Modules.IsInvertible L)
    (g : L ⟶ Invertible.Scheme.Modules.unitObj X) :
    (InvertibleCancellationPairing.invertibleDualPairingIso L hL).inv ≫
        (g ⊗ₘ 𝟙 (Dual.Scheme.Modules.dualObj L)) ≫
          (unitLeftIso (Dual.Scheme.Modules.dualObj L)).hom =
      (Dual.Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
        Dual.Scheme.Modules.dualMapObj g := by
  apply (cancel_epi
    (InvertibleCancellationPairing.invertibleDualPairingIso L hL).hom).1
  rw [Iso.hom_inv_id_assoc]
  apply tensor_hom_ext
  intro U x φ
  change (unitLeftIso (Dual.Scheme.Modules.dualObj L)).hom.val.app (.op U)
      ((g ⊗ₘ 𝟙 (Dual.Scheme.Modules.dualObj L)).val.app (.op U)
        (TensorSections.tensorSection L (Dual.Scheme.Modules.dualObj L) U x φ)) =
    ((Dual.Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
      Dual.Scheme.Modules.dualMapObj g).val.app (.op U)
        ((TensorFrameSections.dualPairing L).val.app (.op U)
          (TensorSections.tensorSection L (Dual.Scheme.Modules.dualObj L) U x φ))
  rw [TensorFrameSections.tensorSection_map]
  change (unitLeftIso (Dual.Scheme.Modules.dualObj L)).hom.val.app (.op U)
      (TensorSections.tensorSection (Invertible.Scheme.Modules.unitObj X)
        (Dual.Scheme.Modules.dualObj L) U (g.val.app (.op U) x) φ) = _
  rw [unitLeftIso_tensorSection, TensorFrameSections.dualPairing_tensorSection]
  exact scalarDual_rankOne hL g U x φ

end SteinerGeometry.ScalarDualTensor
