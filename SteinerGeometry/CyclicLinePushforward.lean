import SteinerGeometry.PushforwardSplitting
import SteinerGeometry.LineBaseChange

/-! Direct images of line bundles along a cyclic étale isogeny split after
pullback along that same isogeny. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

namespace SteinerGeometry.CyclicEtaleIsogeny

variable {S : Scheme} {D : Abelian.Schemes.AbelianScheme 1 S} {n : ℕ}
    (q : CyclicEtaleIsogeny D n)

/-- The actual direct image of the original line bundle. -/
def linePushforward (A : Line.Bundles.LineBundle D.scheme.left) : q.target.scheme.left.Modules :=
  (Scheme.Modules.pushforward q.map.hom.left).obj A.sheaf

/-- Pulling back the direct image is the direct sum of its actual kernel translates. -/
def pullbackPushforwardSplitting [NeZero n] (A : Line.Bundles.LineBundle D.scheme.left) :
    (Scheme.Modules.pullback q.map.hom.left).obj (q.linePushforward A) ≅
      ∐ (fun i : Multiplicative (ZMod n) => (q.translatedLineBundle A i).sheaf) := by
  letI : Etale q.map.hom.left := q.etale
  exact lineBaseChangeIso (IsPullback.of_hasPullback q.map.hom.left q.map.hom.left).flip A ≪≫
    q.selfFiberPushforwardSplitting A

end SteinerGeometry.CyclicEtaleIsogeny
