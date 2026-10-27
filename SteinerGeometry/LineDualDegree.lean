module

public import SteinerGeometry.MonomialDegree
public import SteinerGeometry.MonomialLineDual

set_option backward.privateInPublic true
@[expose] public section

/-! Euler degree of the native internal-Hom line dual. -/
noncomputable section
namespace SteinerGeometry.EulerDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open SteinerGeometry.EllipticCohomology

/-- The actual internal-Hom dual of any line bundle has its negative degree. -/
theorem lineBundleDual_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    (L : Line.Bundles.LineBundle X) :
    χ p (LineBundleDual.Construction.lineBundleDual L).sheaf = -χ p L.sheaf :=
  inversePair_euler p hd hO H hH L
    (LineBundleDual.Construction.lineBundleDual L) (lineBundleDual_primal_pairing L).some

/-- Degree of the exact native-dual monomial tensor a target line, as it
appears in the symmetric-kernel cohomology calculation. -/
theorem monomialLineBundle_lineDual_twist_euler {X : Scheme.{0}}
    [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    {m s : ℕ} (L : Fin m → Line.Bundles.LineBundle X) (a : Sym (Fin m) s)
    (r : ℤ) (hL : ∀ j, χ p (L j).sheaf = r) (N : Line.Bundles.LineBundle X) :
    χ p ((monomialLineBundle
      (fun j => LineBundleDual.Construction.lineBundleDual (L j)) a).tensor N).sheaf =
        χ p N.sheaf - (s : ℤ) * r :=
  monomialInverseTwist_euler p hd hO H hH L
    (fun j => LineBundleDual.Construction.lineBundleDual (L j)) a
    (fun j => lineBundleDual_primal_pairing (L j)) r hL N

end SteinerGeometry.EulerDegree
