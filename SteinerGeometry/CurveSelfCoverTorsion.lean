import SteinerGeometry.CurveSelfCoverEuler
import SteinerGeometry.EulerDegree
import SteinerGeometry.TorsionLineClasses

noncomputable section
namespace SteinerGeometry.EllipticCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

local instance curveSelfCoverTorsion_hasFiniteBiproducts (X : Scheme.{0}) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- Character summands of a self-cover have finite tensor order, so their
actual Euler characteristics give χ(O)=0. -/
theorem structure_euler_zero_of_trivialized_self_line_decomposition
    {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p]
    (hd : topologicalKrullDim X ≤ 1)
    (J : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ J.sheaf) (hs : s ≠ 0)
    (hJ : χ p (Line.Bundles.structureModule X) < χ p J.sheaf)
    (f : X ⟶ X) [IsAffineHom f] (hf : f ≫ p = p)
    [Finite (Line.Bundles.LineBundle.pullbackClassMonoidHom f).ker]
    {I : Type} [Fintype I] (hI : Fintype.card I ≠ 1)
    (L : I → Line.Bundles.LineBundle X)
    (e : (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X) ≅
      ⨁ (fun i => (L i).sheaf))
    (hL : ∀ i, Nonempty (((L i).pullback f).sheaf ≅ Line.Bundles.structureModule X)) :
    χ p (Line.Bundles.structureModule X) = 0 := by
  apply structure_euler_zero_of_self_line_decomposition p hd f hf hI L e
  intro i
  apply EulerDegree.isOfFinOrder_euler_eq_structure p hd J s hs hJ
  exact TorsionLineClasses.torsion_of_finite_pullbackKernel f (L i) (hL i)

end SteinerGeometry.EllipticCohomology
