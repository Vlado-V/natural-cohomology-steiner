module

public import SteinerGeometry.SheafDual
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.EpimorphismCover

set_option backward.privateInPublic true
@[expose] public section

/-! Restriction of the actual dual map and local splitting. -/
noncomputable section
namespace SteinerGeometry.SheafDual
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} (a : Y ⟶ X) [IsOpenImmersion a]

theorem internalHom_restrict_natural {M N P Q : X.Modules} (f : M ⟶ N) (g : P ⟶ Q) :
    (Scheme.Modules.restrictFunctor a).map
        (InternalHomMaps.Construction.moduleInternalHomMap f g) ≫
      (InternalHomRestriction.Construction.moduleInternalHomRestrictIso a M Q).hom =
    (InternalHomRestriction.Construction.moduleInternalHomRestrictIso a N P).hom ≫
      InternalHomMaps.Construction.moduleInternalHomMap
        ((Scheme.Modules.restrictFunctor a).map f) ((Scheme.Modules.restrictFunctor a).map g) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro h
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  rfl

theorem internalHomMap_splitEpi_of_splitMono {M N P : Y.Modules}
    (f : M ⟶ N) [IsSplitMono f] :
    IsSplitEpi (InternalHomMaps.Construction.moduleInternalHomMap f (𝟙 P)) := by
  refine ⟨⟨InternalHomMaps.Construction.moduleInternalHomMap (retraction f) (𝟙 P), ?_⟩⟩
  rw [InternalHomMaps.Construction.moduleInternalHomMap_comp, IsSplitMono.id,
    Category.id_comp, InternalHomMaps.Construction.moduleInternalHomMap_id]

theorem restrict_dualMap_epi {M N : X.Modules} (f : M ⟶ N)
    [IsSplitMono ((Scheme.Modules.restrictFunctor a).map f)] :
    Epi ((Scheme.Modules.restrictFunctor a).map (dualMap f)) := by
  haveI := internalHomMap_splitEpi_of_splitMono
    ((Scheme.Modules.restrictFunctor a).map f) (P := (Line.Bundles.structureModule X).restrict a)
  have h := internalHom_restrict_natural a f (𝟙 (Line.Bundles.structureModule X))
  haveI : Epi ((InternalHomRestriction.Construction.moduleInternalHomRestrictIso a
      N (Line.Bundles.structureModule X)).hom ≫
      InternalHomMaps.Construction.moduleInternalHomMap
        ((Scheme.Modules.restrictFunctor a).map f)
        ((Scheme.Modules.restrictFunctor a).map (𝟙 (Line.Bundles.structureModule X)))) := by
    erw [CategoryTheory.Functor.map_id]
    exact (inferInstance : Epi
      ((InternalHomRestriction.Construction.moduleInternalHomRestrictIso a
        N (Line.Bundles.structureModule X)).hom ≫
        InternalHomMaps.Construction.moduleInternalHomMap
          ((Scheme.Modules.restrictFunctor a).map f)
          (𝟙 ((Line.Bundles.structureModule X).restrict a))))
  haveI : Epi ((Scheme.Modules.restrictFunctor a).map (dualMap f) ≫
      (InternalHomRestriction.Construction.moduleInternalHomRestrictIso a
        M (Line.Bundles.structureModule X)).hom) := by
    change Epi ((Scheme.Modules.restrictFunctor a).map
      (InternalHomMaps.Construction.moduleInternalHomMap f (𝟙 _)) ≫ _)
    rw [h]
    infer_instance
  let e := InternalHomRestriction.Construction.moduleInternalHomRestrictIso a
    M (Line.Bundles.structureModule X)
  have : Epi (((Scheme.Modules.restrictFunctor a).map (dualMap f) ≫ e.hom) ≫ e.inv) :=
    inferInstance
  simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using this

theorem dualMap_epi_of_local_split {M N : X.Modules} (f : M ⟶ N)
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hs : ∀ i, IsSplitMono ((Scheme.Modules.restrictFunctor (U i).ι).map f)) :
    Epi (dualMap f) := by
  apply Module.EpimorphismCover.module_epi_of_restrict_cover U hU
  intro i
  haveI := hs i
  exact restrict_dualMap_epi (U i).ι f

/-- On a chart with a genuine retraction, the restricted dual has a genuine section. -/
theorem restrict_dualMap_splitEpi {M N : X.Modules} (f : M ⟶ N)
    [IsSplitMono ((Scheme.Modules.restrictFunctor a).map f)] :
    IsSplitEpi ((Scheme.Modules.restrictFunctor a).map (dualMap f)) := by
  let F := Scheme.Modules.restrictFunctor a
  let P := (Line.Bundles.structureModule X).restrict a
  let u := InternalHomMaps.Construction.moduleInternalHomMap
    (retraction (F.map f)) (𝟙 P)
  let v := InternalHomMaps.Construction.moduleInternalHomMap (F.map f) (𝟙 P)
  let eM := InternalHomRestriction.Construction.moduleInternalHomRestrictIso
    a M (Line.Bundles.structureModule X)
  let eN := InternalHomRestriction.Construction.moduleInternalHomRestrictIso
    a N (Line.Bundles.structureModule X)
  have huv : u ≫ v = 𝟙 _ := by
    dsimp [u, v]
    rw [InternalHomMaps.Construction.moduleInternalHomMap_comp, IsSplitMono.id,
      Category.id_comp, InternalHomMaps.Construction.moduleInternalHomMap_id]
  have h := internalHom_restrict_natural a f (𝟙 (Line.Bundles.structureModule X))
  erw [CategoryTheory.Functor.map_id] at h
  change F.map (dualMap f) ≫ eM.hom = eN.hom ≫ v at h
  refine ⟨⟨eM.hom ≫ u ≫ eN.inv, ?_⟩⟩
  apply (cancel_mono eM.hom).mp
  simp only [Category.assoc, Category.id_comp]
  rw [h]
  simp only [Category.assoc, eN.inv_hom_id_assoc]
  rw [huv, Category.comp_id]

end SteinerGeometry.SheafDual
