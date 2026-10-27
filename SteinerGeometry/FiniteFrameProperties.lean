import SteinerGeometry.FiniteLocalFrames

/-! Native local-freeness and finiteness from actual finite geometric frames. -/
namespace SteinerGeometry.TildeFiniteProjective
open CategoryTheory AlgebraicGeometry
universe u

theorem FiniteGeometricFrameCover.locallyFree {X : Scheme.{u}} {M : X.Modules}
    (D : FiniteGeometricFrameCover M) : M.IsLocallyFree := by
  apply KernelLocalFreeness.locallyFree_of_local_frames M D.U D.covers D.Q
  intro i
  exact overFrameOfPullback M (D.U i) (D.Q i) (D.frame i)

theorem FiniteGeometricFrameCover.finiteType {X : Scheme.{u}} {M : X.Modules}
    (D : FiniteGeometricFrameCover M) : M.IsQuasicoherent ∧ M.IsFiniteType := by
  let : ∀ i, Finite (D.Q i) := D.finite
  apply KernelLocalFreeness.finiteType_of_local_frames M D.U D.covers D.Q
  intro i
  exact overFrameOfPullback M (D.U i) (D.Q i) (D.frame i)

end SteinerGeometry.TildeFiniteProjective
