module

public import SteinerGeometry.CurveSectionFunctor

set_option backward.privateInPublic true
@[expose] public section

/-! Actual section and fiber spaces for the curve generator theorem. -/

namespace SteinerGeometry

noncomputable section

open AlgebraicGeometry CategoryTheory

variable {K : Type} [Field K] {C : Scheme}

/-- Actual global sections, with the scalar action from the structural map. -/
abbrev CurveSectionSpace (p : C ⟶ Spec (.of K)) (E : C.Modules) :=
  (sectionFunctor p).obj E

/-- Actual sections of the pulled-back sheaf at a field-valued point. -/
abbrev CurveSectionFiber (p : C ⟶ Spec (.of K)) (E : C.Modules)
    (a : Spec (.of K) ⟶ C) :=
  (sectionFunctor (a ≫ p)).obj ((Scheme.Modules.pullback a).obj E)

/-- Canonical evaluation of genuine sections into the genuine fiber. -/
abbrev curveSectionEvaluation (p : C ⟶ Spec (.of K)) (E : C.Modules)
    (a : Spec (.of K) ⟶ C) : CurveSectionSpace p E →ₗ[K] CurveSectionFiber p E a :=
  sectionEvaluation p E a

@[simp] theorem curveSectionEvaluation_apply (p : C ⟶ Spec (.of K))
    (E : C.Modules) (a : Spec (.of K) ⟶ C) (s : CurveSectionSpace p E) :
    curveSectionEvaluation p E a s =
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E).app ⊤ s := rfl

theorem curveSectionEvaluation_natural (p : C ⟶ Spec (.of K))
    {E N : C.Modules} (f : E ⟶ N) (a : Spec (.of K) ⟶ C)
    (s : CurveSectionSpace p E) :
    curveSectionEvaluation p N a ((sectionFunctor p).map f s) =
      (sectionFunctor (a ≫ p)).map ((Scheme.Modules.pullback a).map f)
        (curveSectionEvaluation p E a s) :=
  sectionEvaluation_natural p f a s

end
end SteinerGeometry
