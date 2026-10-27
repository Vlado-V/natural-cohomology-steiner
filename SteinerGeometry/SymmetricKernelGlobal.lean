import SteinerGeometry.FirstKernelRestriction
import SteinerGeometry.FirstKernelTargetIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames

/-! Global splitting of the genuine symmetric contraction kernel into monomial line factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}
local instance symmetricKernelGlobalBiproducts (Z : Scheme.{u}) : HasFiniteBiproducts Z.Modules := HasFiniteBiproducts.of_hasFiniteProducts

private def restrictFrame {M : X.Modules} {U V : X.Opens} (h : U ≤ V)
    (e : M.restrict V.ι ≅ Line.Bundles.structureModule V.toScheme) :
    M.restrict U.ι ≅ Line.Bundles.structureModule U.toScheme :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) V.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (X.homOfLE h)

private theorem restrict_iso_smaller {M N : X.Modules} (a : M ⟶ N)
    {U V : X.Opens} (h : U ≤ V)
    [IsIso ((Scheme.Modules.restrictFunctor V.ι).map a)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) := by
  let g := X.homOfLE h
  let E : Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.restrictFunctor g :=
    Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm ≪≫
      Scheme.Modules.restrictFunctorComp g V.ι
  have he : (Scheme.Modules.restrictFunctor U.ι).map a =
      (E.app M).hom ≫ (Scheme.Modules.restrictFunctor g).map
        ((Scheme.Modules.restrictFunctor V.ι).map a) ≫ (E.app N).inv := by
    apply (cancel_mono (E.app N).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact E.hom.naturality a
  rw [he]
  infer_instance

/-- On a chart where the first-kernel lines are framed and one evaluation
coefficient is invertible, the restricted global monomial-kernel map is an isomorphism. -/
theorem symmetricKernel_isIso_on_restriction
    {K : Type u} [Field K] [CharZero K] (p : X ⟶ Spec (.of K)) {n d : ℕ}
    {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N))
    (L : Fin n → Line.Bundles.LineBundle X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e))
    (U : X.Opens)
    (frames : ∀ j, (L j).sheaf.restrict U.ι ≅ Line.Bundles.structureModule U.toScheme)
    (j : Fin (n+1)) [IsIso ((Scheme.Modules.restrictFunctor U.ι).map (e j))] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (splitMonomialKernelMap (d := d) e L (firstKernelColumns e L E)
        (firstKernelColumns_relation e L E))) := by
  let Lr := fun i => restrictionLineBundle U.ι (L i)
  let er := restrictedEvaluation U.ι e
  let Er := firstKernelSplittingRestrict U.ι e L E
  have hj : IsIso (er j) := by dsimp [er, restrictedEvaluation]; infer_instance
  let q : N.restrict U.ι ≅ Line.Bundles.structureModule U.toScheme := (asIso (er j)).symm
  let ef := fun i => er i ≫ q.hom
  let Ef := Er ≪≫ firstKernelTargetIso er q
  have hcf : firstKernelColumns ef Lr Ef = firstKernelColumns er Lr Er := by
    funext i
    exact firstKernelColumns_targetIso er q Lr Er i
  have hcr : restrictedKernelColumns U.ι L (firstKernelColumns e L E) =
      firstKernelColumns er Lr Er := by
    funext i
    exact firstKernelColumns_restrict U.ι e L E i
  have hchart : IsIso (splitMonomialKernelMap (d := d) ef Lr (firstKernelColumns ef Lr Ef)
      (firstKernelColumns_relation ef Lr Ef)) :=
    symmetricKernel_isIso_on_split_chart (U.ι ≫ p) ef Lr frames Ef j
  have hraw : IsIso (splitMonomialKernelMap (d := d) er Lr (firstKernelColumns er Lr Er)
      (firstKernelColumns_relation er Lr Er)) := by
    have heq := splitMonomialKernelMap_targetIso (d := d) er q Lr
      (firstKernelColumns er Lr Er) (firstKernelColumns_relation er Lr Er)
    have hpost : IsIso (splitMonomialKernelMap (d := d) er Lr (firstKernelColumns er Lr Er)
        (firstKernelColumns_relation er Lr Er) ≫ (contractionTargetKernelIso er q).hom) := by
      rw [heq]
      simpa only [hcf] using hchart
    exact (isIso_comp_right_iff _ (contractionTargetKernelIso er q).hom).mp hpost
  have hnat := splitMonomialKernelMap_restrict (d := d) U.ι e L (firstKernelColumns e L E)
    (firstKernelColumns_relation e L E)
  have hwhole : IsIso ((splitMonomialSourceRestrictIso U.ι L (d+1)).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (splitMonomialKernelMap (d := d) e L (firstKernelColumns e L E)
          (firstKernelColumns_relation e L E)) ≫ (contractionRestrictKernelIso U.ι e).hom) := by
    rw [hnat]
    simpa only [hcr] using hraw
  exact (isIso_comp_left_iff (splitMonomialSourceRestrictIso U.ι L (d+1)).inv _).mp
    ((isIso_comp_right_iff _ (contractionRestrictKernelIso U.ι e).hom).mp hwhole)

/-- The symmetric contraction kernel of an actual basepoint-free line-bundle
evaluation is the sum of the monomial line factors of its split first kernel. -/
theorem symmetricKernel_isIso
    {K : Type u} [Field K] [CharZero K] (p : X ⟶ Spec (.of K)) {n d : ℕ}
    (N : Line.Bundles.LineBundle X)
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf))
    (he : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (e j))
    (L : Fin n → Line.Bundles.LineBundle X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e)) :
    IsIso (splitMonomialKernelMap (d := d) e L (firstKernelColumns e L E)
      (firstKernelColumns_relation e L E)) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨j, hxj⟩ := he x
  obtain ⟨V, hxV, frames⟩ := commonLineRestrictionFrames L x
  let W := Ample.LineBundles.sectionNonvanishing (e j)
  let U : X.Opens := W ⊓ V
  have hxU : x ∈ U := ⟨hxj, hxV⟩
  have hW : IsIso ((Scheme.Modules.restrictFunctor W.ι).map (e j)) := by
    apply (Power.Nonvanishing.isIso_restrict_map_iff W.ι (e j)).mpr
    exact (Section.Nonvanishing.isIso_pullbackSection_iff W.ι (e j)).mp inferInstance
  have hU : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (e j)) :=
    restrict_iso_smaller (e j) (show U ≤ W from inf_le_left)
  let localFrames := fun i => restrictFrame
    (show U ≤ V from inf_le_right) (Classical.choice (frames i))
  refine ⟨U, hxU, ?_⟩
  apply (Power.Nonvanishing.isIso_restrict_map_iff U.ι _).mp
  exact symmetricKernel_isIso_on_restriction p e L E U localFrames j

end SteinerGeometry
