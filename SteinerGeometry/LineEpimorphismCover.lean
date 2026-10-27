import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ScalarSectionCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! A finite epimorphism onto a line bundle has a locally invertible component. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry.LineEpimorphismCover

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

local instance lineEpimorphismCoverBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- In any local frame, the scalar coordinates of an epimorphism from a
finite free module are jointly epimorphic. -/
theorem local_components_epi {X Y : Scheme.{u}} {ι : Type} [Fintype ι]
    (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (e : (⨁ fun _ : ι => Line.Bundles.structureModule X) ⟶ L.sheaf) [Epi e]
    (frame : (Scheme.Modules.pullback f).obj L.sheaf ≅ Line.Bundles.structureModule Y) :
    Epi (Sigma.desc (fun i : ι =>
      Ample.LineBundles.pullbackSection f (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e) ≫ frame.hom)) := by
  let F := Scheme.Modules.pullback f
  let : F.Additive := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
    exact Functor.additive_of_preservesBinaryBiproducts F
  let : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  let h : (⨁ fun _ : ι => Line.Bundles.structureModule Y) ⟶ Line.Bundles.structureModule Y :=
    (biproduct.mapIso (fun _ : ι => (Line.Bundles.structureModulePullbackIso f).symm)).hom ≫
      (F.mapBiproduct (fun _ : ι => Line.Bundles.structureModule X)).inv ≫ F.map e ≫ frame.hom
  have hh : h = biproduct.desc (fun i : ι =>
      Ample.LineBundles.pullbackSection f (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e) ≫ frame.hom) := by
    apply biproduct.hom_ext'
    intro i
    simp only [h, biproduct.mapIso_hom, Category.assoc, biproduct.ι_map_assoc,
      Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, biproduct.ι_desc,
      Ample.LineBundles.pullbackSection, Functor.map_comp]
    rfl
  have : Epi h := by dsimp [h]; infer_instance
  have ht : Epi (biproduct.desc (fun i : ι =>
      Ample.LineBundles.pullbackSection f (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e) ≫ frame.hom)) := by
    rwa [← hh]
  have heq : (biproduct.isoCoproduct (fun _ : ι => Line.Bundles.structureModule Y)).hom ≫
      Sigma.desc (fun i : ι =>
        Ample.LineBundles.pullbackSection f (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e) ≫ frame.hom) =
      biproduct.desc (fun i : ι =>
        Ample.LineBundles.pullbackSection f (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e) ≫ frame.hom) := by
    apply biproduct.hom_ext'
    intro i
    simp
  have : Epi ((biproduct.isoCoproduct (fun _ : ι => Line.Bundles.structureModule Y)).hom ≫
      Sigma.desc (fun i : ι =>
        Ample.LineBundles.pullbackSection f (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e) ≫ frame.hom)) := by
    rw [heq]
    exact ht
  exact epi_of_epi (biproduct.isoCoproduct (fun _ : ι => Line.Bundles.structureModule Y)).hom _

/-- At every point, at least one component of an epimorphism onto a line
bundle is a local frame. -/
theorem components_cover {X : Scheme.{0}} {ι : Type} [Fintype ι]
    (L : Line.Bundles.LineBundle X)
    (e : (⨁ fun _ : ι => Line.Bundles.structureModule X) ⟶ L.sheaf) [Epi e] :
    ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing
      (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e) := by
  intro x
  obtain ⟨U, hx, hU, ⟨frame⟩⟩ := L.exists_affine_frame x
  let : IsAffine U.toScheme := hU
  let t (i : ι) : End (Line.Bundles.structureModule U.toScheme) :=
    Ample.LineBundles.pullbackSection U.ι
      (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e) ≫ frame.hom
  let : Epi (Sigma.desc t) := local_components_epi U.ι L e frame
  obtain ⟨i, hi⟩ := Affine.ScalarSectionCover.affine_scalar_sections_cover (X := U.toScheme) (ι := ι) t (⟨x, hx⟩ : U.toScheme)
  refine ⟨i, ?_⟩
  have hn := Ample.Powers.sectionNonvanishing_comp_iso
    (Ample.LineBundles.pullbackSection U.ι
      (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e)) frame
  change (⟨x, hx⟩ : U.toScheme) ∈ Ample.LineBundles.sectionNonvanishing
    (Ample.LineBundles.pullbackSection U.ι
      (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e) ≫ frame.hom) at hi
  rw [hn, Section.Nonvanishing.sectionNonvanishing_pullback] at hi
  exact hi

/-- The component frame opens cover the whole scheme. -/
theorem iSup_component_nonvanishing {X : Scheme.{0}} {ι : Type} [Fintype ι]
    (L : Line.Bundles.LineBundle X)
    (e : (⨁ fun _ : ι => Line.Bundles.structureModule X) ⟶ L.sheaf) [Epi e] :
    (⨆ i, Ample.LineBundles.sectionNonvanishing
      (biproduct.ι (fun _ : ι => Line.Bundles.structureModule X) i ≫ e)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := components_cover L e x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

end SteinerGeometry.LineEpimorphismCover
