module

public import SteinerGeometry.EulerDegree
public import SteinerGeometry.MonomialLineClasses

set_option backward.privateInPublic true
@[expose] public section

/-! Genuine Euler degrees of the actual symmetric-kernel monomial lines. -/
noncomputable section
namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology EulerDegree

/-- Tensoring the ordered line factors adds their genuine Euler degrees. -/
theorem tensorLineFactors_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    (s : ℕ) (L : Fin s → Line.Bundles.LineBundle X) :
    χ p (tensorLineFactors s L).sheaf = ∑ j, χ p (L j).sheaf := by
  induction s with
  | zero =>
    change χ p (Line.Bundles.LineBundle.trivial X).sheaf = 0
    exact hO
  | succ s ih =>
    change χ p ((L 0).tensor (tensorLineFactors s (fun j => L j.succ))).sheaf = _
    rw [tensor_euler_add p hd hO H hH, ih, Fin.sum_univ_succ]

/-- A symmetric monomial has the sum of the degrees of its ordered factors. -/
theorem monomialLineBundle_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    {m s : ℕ} (L : Fin m → Line.Bundles.LineBundle X) (a : Sym (Fin m) s) :
    χ p (monomialLineBundle L a).sheaf = ∑ j, χ p (L (symmetricWord a j)).sheaf :=
  tensorLineFactors_euler p hd hO H hH s _

/-- Equal-degree factors give a monomial of that degree times its length. -/
theorem monomialLineBundle_euler_constant {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    {m s : ℕ} (L : Fin m → Line.Bundles.LineBundle X) (a : Sym (Fin m) s)
    (r : ℤ) (hL : ∀ j, χ p (L j).sheaf = r) :
    χ p (monomialLineBundle L a).sheaf = (s : ℤ) * r := by
  rw [monomialLineBundle_euler p hd hO H hH]
  simp_rw [hL]
  simp

/-- An inverse monomial twisted by N has exactly the expected degree gap. -/
theorem monomialInverseTwist_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    {m s : ℕ} (L M : Fin m → Line.Bundles.LineBundle X) (a : Sym (Fin m) s)
    (e : ∀ j, Nonempty (((L j).tensor (M j)).sheaf ≅ Line.Bundles.structureModule X))
    (r : ℤ) (hL : ∀ j, χ p (L j).sheaf = r) (N : Line.Bundles.LineBundle X) :
    χ p ((monomialLineBundle M a).tensor N).sheaf = χ p N.sheaf - (s : ℤ) * r := by
  have hM (j : Fin m) : χ p (M j).sheaf = -r := by
    rw [inversePair_euler p hd hO H hH (L j) (M j) (e j).some, hL]
  rw [tensor_euler_add p hd hO H hH,
    monomialLineBundle_euler_constant p hd hO H hH M a (-r) hM]
  ring

end SteinerGeometry
