module

public import SteinerGeometry.MonomialLineClasses
public import SteinerGeometry.LineDualPullback

set_option backward.privateInPublic true
@[expose] public section

/-! Native internal-Hom line duals in the actual symmetric-kernel summands. -/
noncomputable section
namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open OAI.AlgebraicGeometry.Picard.Homomorphisms

/-- The native internal-Hom dual has an inverse pairing in primal-first order. -/
theorem lineBundleDual_primal_pairing {X : Scheme.{0}} (L : Line.Bundles.LineBundle X) :
    Nonempty ((L.tensor (LineBundleDual.Construction.lineBundleDual L)).sheaf ≅
      Line.Bundles.structureModule X) :=
  EulerDegree.inverse_pairing_swap L (LineBundleDual.Construction.lineBundleDual L)
    ⟨LineBundleEvaluation.Construction.lineBundleEvaluationIso L⟩

/-- The actual monomial of native line duals is inverse to the primal monomial. -/
theorem monomialLineBundle_lineDual_pairing {X : Scheme.{0}} {m s : ℕ}
    (L : Fin m → Line.Bundles.LineBundle X) (a : Sym (Fin m) s) :
    Nonempty (((monomialLineBundle L a).tensor
      (monomialLineBundle (fun j => LineBundleDual.Construction.lineBundleDual (L j)) a)).sheaf ≅
        Line.Bundles.structureModule X) :=
  monomialLineBundle_inverse_pairing L
    (fun j => LineBundleDual.Construction.lineBundleDual (L j)) a
      (fun j => lineBundleDual_primal_pairing (L j))

/-- Primal avoidance proves nontriviality of the exact native-dual monomial
summand appearing in the symmetric-kernel decomposition. -/
theorem monomialLineBundle_lineDual_twist_nontrivial {X : Scheme.{0}} {m s : ℕ}
    (L : Fin m → Line.Bundles.LineBundle X) (a : Sym (Fin m) s)
    (N : Line.Bundles.LineBundle X)
    (hN : ¬ Nonempty (N.sheaf ≅ (monomialLineBundle L a).sheaf)) :
    ¬ Nonempty (((monomialLineBundle
      (fun j => LineBundleDual.Construction.lineBundleDual (L j)) a).tensor N).sheaf ≅
        Line.Bundles.structureModule X) :=
  monomialLineBundle_inverse_twist_nontrivial L
    (fun j => LineBundleDual.Construction.lineBundleDual (L j)) a
      (fun j => lineBundleDual_primal_pairing (L j)) N hN

end SteinerGeometry
