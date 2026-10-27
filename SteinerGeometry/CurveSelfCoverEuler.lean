module

public import SteinerGeometry.CurveEulerBiproduct
public import SteinerGeometry.CurveCohomologyFinite
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LineBundleSectionFiniteness

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry.EllipticCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

local instance curveSelfCoverEuler_hasFiniteBiproducts (X : Scheme.{0}) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- For an actual finite self-cover, a character decomposition into equally
Euler-characteristic line bundles forces the structure Euler characteristic to vanish. -/
theorem structure_euler_zero_of_self_line_decomposition
    {X : Scheme.{0}} [IsNoetherian X] [X.IsSeparated]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p]
    (hd : topologicalKrullDim X ≤ 1)
    (f : X ⟶ X) [IsAffineHom f] (hf : f ≫ p = p)
    {I : Type} [Fintype I] (hI : Fintype.card I ≠ 1)
    (L : I → Line.Bundles.LineBundle X)
    (e : (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X) ≅
      ⨁ (fun i => (L i).sheaf))
    (hχ : ∀ i, χ p (L i).sheaf = χ p (Line.Bundles.structureModule X)) :
    χ p (Line.Bundles.structureModule X) = 0 := by
  apply structure_euler_zero_of_self_decomposition p hd f hf hI
    (fun i => (L i).sheaf) e
  · intro i
    let _ := (L i).isQuasicoherent
    let _ := (L i).isFiniteType
    exact CurveCohomologyFinite.finite (p := p) _ 0
  · intro i
    let _ := (L i).isQuasicoherent
    let _ := (L i).isFiniteType
    exact CurveCohomologyFinite.finite (p := p) _ 1
  · exact hχ

end SteinerGeometry.EllipticCohomology
