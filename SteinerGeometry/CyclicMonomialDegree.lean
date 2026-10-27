module

public import SteinerGeometry.CyclicContractionVanishing
public import SteinerGeometry.LineDualDegree

set_option backward.privateInPublic true
@[expose] public section

/-! Degrees and nontriviality of the actual cyclic-cover monomial lines. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.CyclicEtaleIsogeny
open CategoryTheory AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open EllipticCohomology

variable {D : Abelian.Schemes.AbelianScheme 1 (Spec (.of ℂ))} {n : ℕ}
    (q : CyclicEtaleIsogeny D n) [NeZero n]

/-- The primal translated lines whose native duals make up the first kernel. -/
def contractionPrimalLineFamily (A : Line.Bundles.LineBundle D.scheme.left) :
    Fin n → Line.Bundles.LineBundle D.scheme.left :=
  fun j => q.translatedLineBundle A (q.kernelIndexEquiv j)

/-- Translation invariance gives every actual primal factor the degree of A. -/
theorem contractionPrimalLineFamily_euler
    (A : Line.Bundles.LineBundle D.scheme.left) (r : ℤ)
    (hA : χ D.scheme.hom A.sheaf = r) (j : Fin n) :
    χ D.scheme.hom (q.contractionPrimalLineFamily A j).sheaf = r :=
  (EulerDegree.translation_euler D (q.kernelLabelPoint (q.kernelIndexEquiv j)) A).trans hA

/-- Every actual dual-monomial summand twisted by the pullback of B has the
same degree n*t-s*r, independent of its multi-index. -/
theorem contractionMonomialLine_euler
    [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [CurveCohomologyFinite D.scheme.hom]
    (hd : topologicalKrullDim D.scheme.left ≤ 1)
    (hO : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0)
    (H : Line.Bundles.LineBundle D.scheme.left) (hH : 0 < χ D.scheme.hom H.sheaf)
    (A : Line.Bundles.LineBundle D.scheme.left)
    (B : Line.Bundles.LineBundle q.target.scheme.left)
    (r t : ℤ) (hA : χ D.scheme.hom A.sheaf = r)
    (hB : χ D.scheme.hom (B.pullback q.map.hom.left).sheaf = (n : ℤ) * t)
    {s : ℕ} (a : Sym (Fin n) s) :
    χ D.scheme.hom (q.contractionMonomialLine A B a).sheaf =
      (n : ℤ) * t - (s : ℤ) * r := by
  have hL := fun j => q.contractionPrimalLineFamily_euler A r hA j
  have h := EulerDegree.monomialLineBundle_lineDual_twist_euler
    D.scheme.hom hd hO H hH (q.contractionPrimalLineFamily A) a r hL
      (B.pullback q.map.hom.left)
  rw [hB] at h
  exact h

/-- Avoiding the corresponding primal monomial guarantees that the actual
twisted dual-monomial summand is nontrivial. -/
theorem contractionMonomialLine_nontrivial
    (A : Line.Bundles.LineBundle D.scheme.left)
    (B : Line.Bundles.LineBundle q.target.scheme.left)
    {s : ℕ} (a : Sym (Fin n) s)
    (havoid : ¬ Nonempty ((B.pullback q.map.hom.left).sheaf ≅
      (monomialLineBundle (q.contractionPrimalLineFamily A) a).sheaf)) :
    ¬ Nonempty ((q.contractionMonomialLine A B a).sheaf ≅
      Line.Bundles.structureModule D.scheme.left) :=
  monomialLineBundle_lineDual_twist_nontrivial (q.contractionPrimalLineFamily A) a
    (B.pullback q.map.hom.left) havoid

end SteinerGeometry.CyclicEtaleIsogeny
