module

public import SteinerGeometry.EulerDegree
public import SteinerGeometry.TorsionLineClasses

set_option backward.privateInPublic true
@[expose] public section

/-! A genuine nontrivial degree-zero reference line for the elliptic argument. -/
noncomputable section
namespace SteinerGeometry.TorsionReferenceLine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

theorem exists_zero_euler_nontrivial_line
    {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p]
    [Infinite (TorsionLineClasses.TorsionClass X)]
    (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf) :
    ∃ P : Line.Bundles.LineBundle X, χ p P.sheaf = 0 ∧
      ¬ Nonempty (P.sheaf ≅ Line.Bundles.structureModule X) := by
  obtain ⟨a, ha⟩ := exists_ne (1 : TorsionLineClasses.TorsionClass X)
  let P := TorsionLineClasses.representative a
  have hfin : IsOfFinOrder (Line.Bundles.LineBundle.classOf P) := by
    change IsOfFinOrder (Line.Bundles.LineBundle.classOf
      (TorsionLineClasses.representative a))
    rw [TorsionLineClasses.representative_class]
    exact a.property
  obtain ⟨s, hs⟩ := positive_euler_has_section p hd H.sheaf hH
  have he := EulerDegree.isOfFinOrder_euler_eq_structure p hd H s hs (by omega) P hfin
  refine ⟨P, he.trans hO, ?_⟩
  intro h
  have hc : Line.Bundles.LineBundle.classOf P = 1 := Quotient.sound h
  apply ha
  apply Subtype.ext
  change Line.Bundles.LineBundle.classOf (TorsionLineClasses.representative a) = 1 at hc
  rw [TorsionLineClasses.representative_class] at hc
  exact hc

end SteinerGeometry.TorsionReferenceLine
