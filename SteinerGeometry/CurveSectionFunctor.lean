import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace SteinerGeometry

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

variable {K : Type} [CommRing K] {C Y : Scheme}

/-- Actual global sections with scalars supplied by the structural morphism. -/
def sectionFunctor (p : C ⟶ Spec (.of K)) : C.Modules ⥤ ModuleCat K :=
  SheafOfModules.evaluation C.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom

instance sectionFunctor_additive (p : C ⟶ Spec (.of K)) : (sectionFunctor p).Additive :=
  ⟨by intros; rfl⟩

/-- Direct image leaves global sections unchanged, including the scalar action. -/
def sectionFunctorPushforwardIso (f : Y ⟶ C) (p : C ⟶ Spec (.of K)) (M : Y.Modules) :
    (sectionFunctor p).obj ((Scheme.Modules.pushforward f).obj M) ≃ₗ[K]
      (sectionFunctor (f ≫ p)).obj M where
  toFun s := s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r s := by
    change (M.smul (f.appTop (((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop) r))).hom s =
      (M.smul (((Scheme.ΓSpecIso (.of K)).inv ≫ (f ≫ p).appTop) r)).hom s
    rfl

/-- Evaluation is the pullback adjunction unit on genuine sections. -/
def sectionEvaluation (p : C ⟶ Spec (.of K)) (E : C.Modules) (a : Y ⟶ C) :
    (sectionFunctor p).obj E →ₗ[K]
      (sectionFunctor (a ≫ p)).obj ((Scheme.Modules.pullback a).obj E) :=
  (sectionFunctorPushforwardIso a p ((Scheme.Modules.pullback a).obj E)).toLinearMap.comp
    ((sectionFunctor p).map ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E)).hom

@[simp] theorem sectionEvaluation_apply (p : C ⟶ Spec (.of K)) (E : C.Modules)
    (a : Y ⟶ C) (s : (sectionFunctor p).obj E) :
    sectionEvaluation p E a s =
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E).app ⊤ s := rfl

theorem sectionEvaluation_natural (p : C ⟶ Spec (.of K)) {E N : C.Modules}
    (f : E ⟶ N) (a : Y ⟶ C) (s : (sectionFunctor p).obj E) :
    sectionEvaluation p N a ((sectionFunctor p).map f s) =
      (sectionFunctor (a ≫ p)).map ((Scheme.Modules.pullback a).map f)
        (sectionEvaluation p E a s) := by
  exact congrArg (fun g => g.app ⊤ s)
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.naturality f)

/-- Successive evaluation agrees with evaluation at the composite map under
the canonical comparison for pullback. -/
theorem sectionEvaluation_comp {Z : Scheme}
    (p : C ⟶ Spec (.of K)) (E : C.Modules) (a : Y ⟶ C) (b : Z ⟶ Y)
    (s : (sectionFunctor p).obj E) :
    sectionEvaluation (a ≫ p) ((Scheme.Modules.pullback a).obj E) b
      (sectionEvaluation p E a s) =
      ((Scheme.Modules.pullbackComp b a).inv.app E).app ⊤
        (sectionEvaluation p E (b ≫ a) s) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
      (Scheme.Modules.pullbackPushforwardAdjunction b))
    (Scheme.Modules.pullbackPushforwardAdjunction (b ≫ a))
    (Scheme.Modules.pullbackComp b a).inv E
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have hv := congrArg (fun g => g.app ⊤ s) h
  simp only [Adjunction.comp_unit_app] at hv
  change sectionEvaluation (a ≫ p) ((Scheme.Modules.pullback a).obj E) b
      (sectionEvaluation p E a s) =
    ((Scheme.Modules.pullbackComp b a).inv.app E).app ⊤
      (sectionEvaluation p E (b ≫ a) s) at hv
  exact hv

end
end SteinerGeometry
