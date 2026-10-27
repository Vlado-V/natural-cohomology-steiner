module

public import SteinerGeometry.FinitePicardAvoidance
public import SteinerGeometry.CyclicDegree

set_option backward.privateInPublic true
@[expose] public section

/-! Actual fixed-degree line bundles chosen by finite-order twists. -/
noncomputable section
namespace SteinerGeometry.TorsionLineChoice
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology EulerDegree PointEuler
open scoped CategoryTheory.MonObj

/-- The positive line of the identity point, constructed from its invertible ideal. -/
def identityPointLine (A : EllipticScheme) : Line.Bundles.LineBundle A.scheme.left :=
  (rationalPointIdealLineBundle A.scheme.hom η[A.scheme].left η[A.scheme].w).reciprocalFrameBundle

theorem pullback_tensorPower_euler {X Y : Scheme.{0}} (f : X ⟶ Y)
    (p : X ⟶ Spec (.of ℂ)) (L : Line.Bundles.LineBundle Y) (t : ℕ) :
    χ p ((L.tensorPower t).pullback f).sheaf = χ p ((L.pullback f).tensorPower t).sheaf := by
  have h : Line.Bundles.LineBundle.classOf ((L.tensorPower t).pullback f) =
      Line.Bundles.LineBundle.classOf ((L.pullback f).tensorPower t) := by
    change (Line.Bundles.LineBundle.pullbackClassMonoidHom f)
      (Line.Bundles.LineBundle.classOf (L.tensorPower t)) = _
    rw [Line.Bundles.LineBundle.classOf_tensorPower, map_pow,
      Line.Bundles.LineBundle.classOf_tensorPower]
    rfl
  exact congrArg (EulerIso.lineBundleClassEuler p) h

/-- Every finite-order line has Euler degree zero after the genuine genus-one
calculation, including the pullback of such a line. -/
theorem torsion_euler_zero {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p]
    (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    (L : Line.Bundles.LineBundle X)
    (ht : IsOfFinOrder (Line.Bundles.LineBundle.classOf L)) : χ p L.sheaf = 0 := by
  obtain ⟨s, hs⟩ := positive_euler_has_section p hd H.sheaf hH
  have h := isOfFinOrder_euler_eq_structure p hd H s hs (by simpa only [hO] using hH) L ht
  exact h.trans hO

/-- This degree-selection step uses only actual finite-order classes and the
finite kernel of the given cover. The rectangular construction supplies the
structure Euler equalities and the infinite torsion-class instance. -/
theorem exists_lineBundles_with_degrees_avoiding
    {D : EllipticScheme} {n : ℕ} [NeZero n] (q : CyclicEtaleIsogeny D n)
    [IsIntegral D.scheme.left] [IsNoetherian D.scheme.left]
    [IsIntegral q.target.scheme.left] [IsNoetherian q.target.scheme.left]
    [CurveCohomologyFinite D.scheme.hom] [CurveCohomologyFinite q.target.scheme.hom]
    [Infinite (TorsionLineClasses.TorsionClass q.target.scheme.left)]
    (hdD : topologicalKrullDim D.scheme.left ≤ 1)
    (hdC : topologicalKrullDim q.target.scheme.left ≤ 1)
    (hOD : χ D.scheme.hom (Line.Bundles.structureModule D.scheme.left) = 0)
    (hOC : χ q.target.scheme.hom (Line.Bundles.structureModule q.target.scheme.left) = 0)
    (r t : ℕ) {J : Type*} [Finite J]
    (forbidden : Line.Bundles.LineBundle D.scheme.left → J → Line.Bundles.LineBundle D.scheme.left) :
    ∃ (A : Line.Bundles.LineBundle D.scheme.left)
      (B : Line.Bundles.LineBundle q.target.scheme.left),
      χ D.scheme.hom A.sheaf = r ∧
      χ q.target.scheme.hom B.sheaf = t ∧
      χ D.scheme.hom (B.pullback q.map.hom.left).sheaf = (n : ℤ) * t ∧
      ∀ i, ¬ Nonempty ((B.pullback q.map.hom.left).sheaf ≅ (forbidden A i).sheaf) := by
  let HD := identityPointLine D
  let HC := identityPointLine q.target
  have hHD : χ D.scheme.hom HD.sheaf = 1 :=
    rationalPointLine_euler D.scheme.hom hdD η[D.scheme].left η[D.scheme].w hOD
  have hHC : χ q.target.scheme.hom HC.sheaf = 1 :=
    rationalPointLine_euler q.target.scheme.hom hdC η[q.target.scheme].left η[q.target.scheme].w hOC
  have hHP : χ D.scheme.hom (HC.pullback q.map.hom.left).sheaf = n :=
    CyclicDegree.pulledPointLine_euler q hdD hOC hOD
  let A := HD.tensorPower r
  let B₀ := HC.tensorPower t
  have hA : χ D.scheme.hom A.sheaf = r := by
    rw [tensorPower_euler D.scheme.hom hdD hOD HD (by omega) HD r, hHD, mul_one]
  have hB₀ : χ q.target.scheme.hom B₀.sheaf = t := by
    rw [tensorPower_euler q.target.scheme.hom hdC hOC HC (by omega) HC t, hHC, mul_one]
  have hPB₀ : χ D.scheme.hom (B₀.pullback q.map.hom.left).sheaf = (n : ℤ) * t := by
    rw [pullback_tensorPower_euler q.map.hom.left D.scheme.hom HC t,
      tensorPower_euler D.scheme.hom hdD hOD HD (by omega) (HC.pullback q.map.hom.left) t,
      hHP, mul_comm]
  obtain ⟨a, hav⟩ := FinitePicardAvoidance.exists_torsion_twist_avoiding q.map.hom B₀
    (Set.range (fun i => Line.Bundles.LineBundle.classOf (forbidden A i))) (Set.finite_range _)
  let P := TorsionLineClasses.representative a
  have hPfin : IsOfFinOrder (Line.Bundles.LineBundle.classOf P) := by
    change IsOfFinOrder (Line.Bundles.LineBundle.classOf (TorsionLineClasses.representative a))
    rw [TorsionLineClasses.representative_class]
    exact a.property
  have hPPfin : IsOfFinOrder (Line.Bundles.LineBundle.classOf (P.pullback q.map.hom.left)) :=
    (Line.Bundles.LineBundle.pullbackClassMonoidHom q.map.hom.left).isOfFinOrder hPfin
  have hP : χ q.target.scheme.hom P.sheaf = 0 :=
    torsion_euler_zero q.target.scheme.hom hdC hOC HC (by omega) P hPfin
  have hPP : χ D.scheme.hom (P.pullback q.map.hom.left).sheaf = 0 :=
    torsion_euler_zero D.scheme.hom hdD hOD HD (by omega) _ hPPfin
  refine ⟨A, B₀.tensor P, hA, ?_, ?_, ?_⟩
  · rw [tensor_euler_add q.target.scheme.hom hdC hOC HC (by omega), hB₀, hP, add_zero]
  · have he := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso D.scheme.hom
      (Line.Bundles.LineBundle.tensorBaseChangeIso q.map.hom.left B₀ P)
    rw [he, tensor_euler_add D.scheme.hom hdD hOD HD (by omega), hPB₀, hPP, add_zero]
  · intro i hi
    apply hav
    exact ⟨i, (Quotient.sound hi).symm⟩
end SteinerGeometry.TorsionLineChoice
