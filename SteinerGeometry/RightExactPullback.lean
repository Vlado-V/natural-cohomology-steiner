module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

set_option backward.privateInPublic true
@[expose] public section

/-! Short exact pullback sequences when injectivity of the first map is known. -/
noncomputable section
namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- Pullback is right exact; a separately proved monomorphism of the first
map therefore upgrades the pulled-back sequence to a short exact sequence. -/
theorem pullback_shortExact_of_mono {X Y : Scheme.{0}} (q : Y ⟶ X)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Mono ((Scheme.Modules.pullback q).map S.f)] :
    (S.map (Scheme.Modules.pullback q)).ShortExact := by
  let F := Scheme.Modules.pullback q
  have : Epi S.g := hS.epi_g
  have : PreservesColimitsOfSize.{0, 0} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction q).leftAdjoint_preservesColimits
  have : Mono (S.map F).f := by
    change Mono ((Scheme.Modules.pullback q).map S.f)
    infer_instance
  have : Epi (S.map F).g := by
    change Epi ((Scheme.Modules.pullback q).map S.g)
    infer_instance
  exact { exact := hS.exact.map_of_epi_of_preservesCokernel F inferInstance inferInstance }

end SteinerGeometry
