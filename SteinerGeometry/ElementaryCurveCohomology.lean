import SteinerGeometry.CurveCohomologyCore
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionMultiplication
import SteinerGeometry.CurveTensorFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.MapSheafification

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry.EllipticCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-- The two line-bundle structures retain exactly the same module sheaf. -/
def seshadriBundle {X : Scheme.{0}} (L : Line.Bundles.LineBundle X) :
    OAI.MaximalSeshadri.Geometry.LineBundle X where
  sheaf := L.sheaf
  locallyRankOne x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
    exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf ≪≫ e⟩⟩

theorem sectionMultiply_eq {X : Scheme.{0}} (L M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s =
      OAI.MaximalSeshadri.Geometry.sectionMultiply (seshadriBundle L) (seshadriBundle M) s := by
  rw [CurveTensorFrames.sectionMultiply_eq]
  unfold LineBundle.SectionMultiplication.lineBundleSectionMultiply
  rw [Tensor.MapSheafification.tensorModuleMap_eq_sheafification]
  rfl

theorem sectionCokernel_flasque {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : s ≠ 0) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (cokernel (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s))) := by
  rw [sectionMultiply_eq]
  exact CurveTensorFrames.tensor_multiply_cokernel_flasque hd
    (seshadriBundle L) (seshadriBundle M) s hs

theorem section_nonvanishing_nonempty {X : Scheme.{0}} [IsIntegral X]
    (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : s ≠ 0) :
    Nonempty (Ample.LineBundles.sectionNonvanishing s) := by
  have hne := (seshadriBundle L).isoOpen_ne_bot s hs
  have hsub : OAI.MaximalSeshadri.SectionOpens.isoOpen s ≤
      Ample.LineBundles.sectionNonvanishing s := by
    apply iSup_le
    intro U
    apply iSup_le
    intro hU
    apply le_sSup
    apply (Section.Nonvanishing.isIso_pullbackSection_iff U.ι s).mpr
    exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) s).mp hU
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr
    (fun he => hne (SetLike.coe_injective he))
  exact ⟨⟨x, hsub hx⟩⟩

theorem sectionCokernel_positive_vanish {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (L M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : s ≠ 0) (q : ℕ) :
    IsZero (H p (cokernel (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s)) (q + 1)) :=
  cohomology_isZero_of_flasque p _ (sectionCokernel_flasque hd L M s hs) q

theorem sectionCokernel_euler_nonneg {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (L M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : s ≠ 0) :
    0 ≤ χ p (cokernel (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s)) := by
  change 0 ≤ CohomologyEulerCharacteristic.coefficientEulerCharacteristic p _
  rw [CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing
    p _ (fun q => sectionCokernel_positive_vanish p hd L M s hs q)]
  exact Nat.cast_nonneg _


end SteinerGeometry.EllipticCohomology
