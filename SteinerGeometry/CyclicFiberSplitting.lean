import SteinerGeometry.CyclicLinePushforward
import SteinerGeometry.PointLineRank
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! The geometric fibers of the actual direct image have the degree of the
cyclic isogeny as their vector-space dimension. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

namespace SteinerGeometry

/-- Finite surjective maps lift every algebraically closed point. -/
private theorem finiteSurjective_geometricLift {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (y : Spec (.of K) ⟶ Y) : ∃ x : Spec (.of K) ⟶ X, x ≫ f = y := by
  let p := pullback.snd f y
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.snd f y))
  have : Surjective p := inferInstanceAs (Surjective (pullback.snd f y))
  have : JacobsonSpace ↥(pullback f y : Scheme) := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨a, _⟩ := p.surjective (IsLocalRing.closedPoint K)
  obtain ⟨b, _, hb⟩ := nonempty_inter_closedPoints
    (Set.nonempty_of_mem (Set.mem_univ a)) isOpen_univ.isLocallyClosed
  let s := pointOfClosedPoint p b hb
  refine ⟨s ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    pointOfClosedPoint_comp p b hb, Category.id_comp]

namespace CyclicEtaleIsogeny

variable {S : Scheme} {D : Abelian.Schemes.AbelianScheme 1 S} {n : ℕ}
    (q : CyclicEtaleIsogeny D n) [NeZero n]

/-- The fiber over the image of an actual field-valued point splits into line fibers. -/
def pullbackPushforwardFiberSplitting {K : Type} [Field K]
    (A : Line.Bundles.LineBundle D.scheme.left) (x : Spec (.of K) ⟶ D.scheme.left) :
    (Scheme.Modules.pullback (x ≫ q.map.hom.left)).obj (q.linePushforward A) ≅
      ∐ (fun i : Multiplicative (ZMod n) => ((q.translatedLineBundle A i).pullback x).sheaf) := by
  letI : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback x) :=
    (Scheme.Modules.pullbackPushforwardAdjunction x).leftAdjoint_preservesColimits
  exact (Scheme.Modules.pullbackComp x q.map.hom.left).symm.app (q.linePushforward A) ≪≫
    (Scheme.Modules.pullback x).mapIso (q.pullbackPushforwardSplitting A) ≪≫
    PreservesCoproduct.iso (Scheme.Modules.pullback x)
      (fun i : Multiplicative (ZMod n) => (q.translatedLineBundle A i).sheaf)

/-- A fiber over a lifted field point is an actual direct sum of n trivial lines. -/
def pullbackPushforwardFiberTrivialization {K : Type} [Field K]
    (A : Line.Bundles.LineBundle D.scheme.left) (x : Spec (.of K) ⟶ D.scheme.left) :
    (Scheme.Modules.pullback (x ≫ q.map.hom.left)).obj (q.linePushforward A) ≅
      ∐ (fun _ : Multiplicative (ZMod n) =>
        Line.Bundles.structureModule (Spec (.of K))) :=
  q.pullbackPushforwardFiberSplitting A x ≪≫
    Sigma.mapIso (fun i : Multiplicative (ZMod n) =>
      ((q.translatedLineBundle A i).pullback x).trivialization_of_subsingleton)

/-- The direct-image fiber at the image of a field-valued point has degree n. -/
theorem pullbackPushforward_fiber_finrank {K : Type} [Field K]
    (A : Line.Bundles.LineBundle D.scheme.left) (x : Spec (.of K) ⟶ D.scheme.left) :
    Module.finrank K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (𝟙 (Spec (.of K)))).obj
        ((Scheme.Modules.pullback (x ≫ q.map.hom.left)).obj (q.linePushforward A))) = n := by
  let e := (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor
    (𝟙 (Spec (.of K)))).mapIso (q.pullbackPushforwardFiberSplitting A x)
  exact e.toLinearEquiv.finrank_eq.trans
    ((fieldLine_coproduct_sections_finrank
      (fun i : Multiplicative (ZMod n) => (q.translatedLineBundle A i).pullback x)).trans
        (by simp))

/-- Every geometric fiber is isomorphic to a direct sum of n copies of its field. -/
def linePushforward_geometricFiberTrivialization {K : Type} [Field K] [IsAlgClosed K]
    (A : Line.Bundles.LineBundle D.scheme.left) (y : Spec (.of K) ⟶ q.target.scheme.left) :
    (Scheme.Modules.pullback y).obj (q.linePushforward A) ≅
      ∐ (fun _ : Multiplicative (ZMod n) =>
        Line.Bundles.structureModule (Spec (.of K))) := by
  let h := finiteSurjective_geometricLift q.map.hom.left y
  let x := Classical.choose h
  have hx : x ≫ q.map.hom.left = y := Classical.choose_spec h
  exact (Scheme.Modules.pullbackCongr hx.symm).app (q.linePushforward A) ≪≫
    q.pullbackPushforwardFiberTrivialization A x

/-- Every geometric fiber of the actual direct image has the isogeny's degree. -/
theorem linePushforward_geometricFiber_finrank {K : Type} [Field K] [IsAlgClosed K]
    (A : Line.Bundles.LineBundle D.scheme.left) (y : Spec (.of K) ⟶ q.target.scheme.left) :
    Module.finrank K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (𝟙 (Spec (.of K)))).obj
        ((Scheme.Modules.pullback y).obj (q.linePushforward A))) = n := by
  obtain ⟨x, hx⟩ :=
    finiteSurjective_geometricLift
      q.map.hom.left y
  rw [← hx]
  exact q.pullbackPushforward_fiber_finrank A x

/-- The actual geometric fiber is finite-dimensional. -/
theorem linePushforward_geometricFiber_finite {K : Type} [Field K] [IsAlgClosed K]
    (A : Line.Bundles.LineBundle D.scheme.left) (y : Spec (.of K) ⟶ q.target.scheme.left) :
    Module.Finite K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (𝟙 (Spec (.of K)))).obj
        ((Scheme.Modules.pullback y).obj (q.linePushforward A))) := by
  apply Module.finite_of_finrank_pos
  rw [q.linePushforward_geometricFiber_finrank A y]
  exact Nat.pos_of_ne_zero (NeZero.ne n)

end CyclicEtaleIsogeny
end SteinerGeometry
