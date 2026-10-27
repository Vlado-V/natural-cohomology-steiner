module

public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

set_option backward.privateInPublic true
@[expose] public section

/-! Simultaneous local frames for a finite family of actual line bundles. -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

namespace SteinerGeometry
universe u v

/-- Finitely many line bundles admit frames on the same neighborhood. -/
theorem commonLineFrames {X : Scheme.{u}} {I : Type v} [Finite I]
    (L : I → Line.Bundles.LineBundle X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ i, Nonempty
      ((Scheme.Modules.pullback U.ι).obj (L i).sheaf ≅
        Line.Bundles.structureModule U.toScheme) := by
  classical
  choose V hx hV using fun i => (L i).locallyTrivial x
  let U : X.Opens := ⨅ i, V i
  have hxU : x ∈ U := by
    change x ∈ ((⨅ i, V i : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  refine ⟨U, hxU, fun i => ⟨?_⟩⟩
  let j : U.toScheme ⟶ (V i).toScheme := X.homOfLE (iInf_le V i)
  have hj : j ≫ (V i).ι = U.ι := X.homOfLE_ι (iInf_le V i)
  exact (Scheme.Modules.pullbackCongr hj.symm).app (L i).sheaf ≪≫
    (Scheme.Modules.pullbackComp j (V i).ι).symm.app (L i).sheaf ≪≫
    (Scheme.Modules.pullback j).mapIso (Classical.choice (hV i)) ≪≫
    Line.Bundles.structureModulePullbackIso j

/-- The simultaneous frames may equally be expressed using literal restriction. -/
theorem commonLineRestrictionFrames {X : Scheme.{u}} {I : Type v} [Finite I]
    (L : I → Line.Bundles.LineBundle X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ i, Nonempty
      ((Scheme.Modules.restrictFunctor U.ι).obj (L i).sheaf ≅
        Line.Bundles.structureModule U.toScheme) := by
  obtain ⟨U, hx, hU⟩ := commonLineFrames L x
  exact ⟨U, hx, fun i => ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app (L i).sheaf ≪≫
    Classical.choice (hU i)⟩⟩

end SteinerGeometry
