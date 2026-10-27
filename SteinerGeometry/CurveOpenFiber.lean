module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

set_option backward.privateInPublic true
@[expose] public section

/-! Restricting to an open neighbourhood does not change a module's fiber. -/

namespace SteinerGeometry

noncomputable section

open AlgebraicGeometry CategoryTheory

variable {C U Y : Scheme}

/-- The unit for restriction to an open immersion becomes an isomorphism
after pullback to any point in that open. -/
theorem openPullbackUnit_fiber_isIso
    (j : U ⟶ C) [IsOpenImmersion j]
    (b : Y ⟶ U) (E : C.Modules) :
    IsIso ((Scheme.Modules.pullback (b ≫ j)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app E)) := by
  have hi : IsIso ((Scheme.Modules.pullback j).map
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app E)) :=
    inferInstance
  have : IsIso ((Scheme.Modules.pullback j ⋙ Scheme.Modules.pullback b).map
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app E)) := by
    change IsIso ((Scheme.Modules.pullback b).map _)
    infer_instance
  exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp b j) _).mp this

/-- The canonical local comparison of the fiber of a direct image along an
open immersion with the fiber computed inside that open. -/
def openPushforwardFiberIso (j : U ⟶ C) [IsOpenImmersion j]
    (b : Y ⟶ U) (M : U.Modules) :
    (Scheme.Modules.pullback (b ≫ j)).obj ((Scheme.Modules.pushforward j).obj M) ≅
      (Scheme.Modules.pullback b).obj M :=
  (Scheme.Modules.pullbackComp b j).symm.app _ ≪≫
    (Scheme.Modules.pullback b).mapIso
      (asIso ((Scheme.Modules.pullbackPushforwardAdjunction j).counit.app M))

/-- A genuine fiber identification between a sheaf on the curve and its
restriction to a neighbourhood of the selected point. -/
def openRestrictionFiberIso (j : U ⟶ C) [IsOpenImmersion j]
    (b : Y ⟶ U) (E : C.Modules) :
    (Scheme.Modules.pullback (b ≫ j)).obj E ≅
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj E) :=
  (Scheme.Modules.pullbackComp b j).symm.app E

end
end SteinerGeometry
