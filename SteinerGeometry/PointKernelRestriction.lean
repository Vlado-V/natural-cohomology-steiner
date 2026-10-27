import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReductionKernelRestriction

/-! Open restriction of canonical closed evaluation kernels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

/-- The canonical evaluation kernel commutes with restriction to an open. -/
def pointKernelRestrictIso {X Y : Scheme.{u}} (a : Y ⟶ X) (U : X.Opens) (E : X.Modules) :
    (kernel ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E)).restrict U.ι ≅
      kernel ((Scheme.Modules.pullbackPushforwardAdjunction (a ∣_ U)).unit.app
        (E.restrict U.ι)) :=
  ReductionKernelRestriction.closedReductionKernelRestrictIso a U E

@[simp, reassoc]
theorem pointKernelRestrictIso_ι {X Y : Scheme.{u}} (a : Y ⟶ X) (U : X.Opens)
    (E : X.Modules) :
    (pointKernelRestrictIso a U E).hom ≫ kernel.ι _ =
      (Scheme.Modules.restrictFunctor U.ι).map
        (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E)) := by
  simp [pointKernelRestrictIso,
    ReductionKernelRestriction.closedReductionKernelRestrictIso,
    kernel.mapIso, kernel.map, PreservesKernel.iso_hom, Category.assoc,
    Closed.ReductionLayer.closedModuleUnit, Closed.ReductionLayer.closedReductionKernel]


end SteinerGeometry
