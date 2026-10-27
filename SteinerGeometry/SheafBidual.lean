module

public import SteinerGeometry.SheafDualKernel
public import SteinerGeometry.FiniteLocalFrames
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible

set_option backward.privateInPublic true
@[expose] public section

/-! Natural bidual evaluation and reflexivity from actual finite local frames. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry.SheafDual
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X Y : Scheme.{u}}

local instance sheafBidualBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- A section acts on a local functional by evaluation. -/
def bidualEvaluation (M : X.Modules) : M ⟶ dual (dual M) :=
  pairingTranspose (𝟙 (dual M))

/-- Bidual evaluation commutes with every morphism of module sheaves. -/
@[reassoc]
theorem bidualEvaluation_naturality {M N : X.Modules} (f : M ⟶ N) :
    f ≫ bidualEvaluation N = bidualEvaluation M ≫ dualMap (dualMap f) := by
  have h : pairingTranspose (f ≫ bidualEvaluation N) = dualMap f := by
    rw [pairingTranspose_comp]
    simp only [bidualEvaluation, pairingTranspose_pairingTranspose, Category.id_comp]
  calc
    f ≫ bidualEvaluation N = pairingTranspose (pairingTranspose
        (f ≫ bidualEvaluation N)) := (pairingTranspose_pairingTranspose _).symm
    _ = pairingTranspose (dualMap f) := congrArg pairingTranspose h
    _ = bidualEvaluation M ≫ dualMap (dualMap f) := by
      simpa only [Category.comp_id, bidualEvaluation] using
        pairingTranspose_comp (𝟙 (dual M)) (dualMap f)

/-- Evaluation is an isomorphism for the structure sheaf. -/
theorem bidualEvaluation_unit_isIso :
    IsIso (bidualEvaluation (Line.Bundles.structureModule X)) := by
  let O := Line.Bundles.structureModule X
  let e := InternalHomUnit.Construction.internalHomUnitIso O
  let c : dual (dual O) ≅ O := dualIso e ≪≫ e
  have hc : bidualEvaluation O ≫ c.hom = 𝟙 O := by
    apply Scheme.Modules.hom_ext
    intro U
    apply AddCommGrpCat.ext
    intro s
    change (X.presheaf.map (𝟙 U).op s) *
      (X.presheaf.map (𝟙 U).op (1 : Γ(X, U))) = s
    simp only [op_id, X.presheaf.map_id, CommRingCat.id_apply]
    exact mul_one (show Γ(X, U) from s)
  have h : IsIso (bidualEvaluation O ≫ c.hom) := by rw [hc]; infer_instance
  exact (isIso_comp_right_iff (bidualEvaluation O) c.hom).mp h

/-- The natural double-dual comparison for a finite direct sum. -/
def bidualBiproductIso {ι : Type} [Fintype ι] (M : ι → X.Modules) :
    dual (dual (⨁ M)) ≅ ⨁ (fun i => dual (dual (M i))) :=
  dualIso (dualBiproductIso M) ≪≫ dualBiproductIso (fun i => dual (M i))

/-- Bidual evaluation has the expected diagonal matrix on a finite direct sum. -/
theorem bidualEvaluation_biproduct {ι : Type} [Fintype ι] (M : ι → X.Modules) :
    bidualEvaluation (⨁ M) ≫ (bidualBiproductIso M).hom =
      biproduct.map (fun i => bidualEvaluation (M i)) := by
  apply biproduct.hom_ext
  intro i
  simp only [bidualBiproductIso, Iso.trans_hom, dualIso, dualBiproductIso,
    Category.assoc, biproduct.lift_π, ← dualMap_comp, biproduct.ι_desc, biproduct.map_π]
  exact (bidualEvaluation_naturality (biproduct.π M i)).symm

/-- A finite direct sum of reflexive sheaves is reflexive. -/
theorem bidualEvaluation_biproduct_isIso {ι : Type} [Fintype ι]
    (M : ι → X.Modules) (h : ∀ i, IsIso (bidualEvaluation (M i))) :
    IsIso (bidualEvaluation (⨁ M)) := by
  have hmap : IsIso (biproduct.map (fun i => bidualEvaluation (M i))) := by
    let e := biproduct.mapIso (fun i => @asIso _ _ _ _ (bidualEvaluation (M i)) (h i))
    exact inferInstanceAs (IsIso e.hom)
  have hc : IsIso (bidualEvaluation (⨁ M) ≫ (bidualBiproductIso M).hom) := by
    rw [bidualEvaluation_biproduct]
    exact hmap
  exact (isIso_comp_right_iff _ _).mp hc

/-- Reflexivity transports along an actual sheaf isomorphism. -/
theorem bidualEvaluation_isIso_of_iso {M N : X.Modules} (e : M ≅ N)
    [IsIso (bidualEvaluation N)] : IsIso (bidualEvaluation M) := by
  let c := dualIso (dualIso e)
  have hc : IsIso (bidualEvaluation M ≫ c.hom) := by
    change IsIso (bidualEvaluation M ≫ dualMap (dualMap e.hom))
    rw [← bidualEvaluation_naturality]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hc

/-- Every finite free sheaf is canonically reflexive. -/
theorem bidualEvaluation_free_isIso (J : Type u) [Finite J] :
    IsIso (bidualEvaluation
      (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) J)) := by
  classical
  let := Fintype.ofFinite J
  let M : Fin (Fintype.card J) → X.Modules := fun _ => Line.Bundles.structureModule X
  let e : (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) J) ≅ ⨁ M :=
    Sigma.reindex (Fintype.equivFin J) M ≪≫ (biproduct.isoCoproduct M).symm
  have : IsIso (bidualEvaluation (⨁ M)) :=
    bidualEvaluation_biproduct_isIso M (fun _ => bidualEvaluation_unit_isIso)
  exact bidualEvaluation_isIso_of_iso e

/-- Open restriction commutes with the actual internal-Hom dual. -/
def restrictDualIso (a : Y ⟶ X) [IsOpenImmersion a] (M : X.Modules) :
    (dual M).restrict a ≅ dual (M.restrict a) :=
  InternalHomRestriction.Construction.moduleInternalHomRestrictIso
      a M (Line.Bundles.structureModule X) ≪≫
    InternalHomMaps.Construction.moduleInternalHomCongr
      (Iso.refl _) (Scheme.Modules.restrictUnitIso a)

/-- The canonical restriction comparison for the double dual. -/
def restrictBidualIso (a : Y ⟶ X) [IsOpenImmersion a] (M : X.Modules) :
    (dual (dual M)).restrict a ≅ dual (dual (M.restrict a)) :=
  restrictDualIso a (dual M) ≪≫ dualIso (restrictDualIso a M)

private theorem restrict_bidualEvaluation_aux (a : Y ⟶ X) [IsOpenImmersion a]
    (M : X.Modules) :
    (Scheme.Modules.restrictFunctor a).map (bidualEvaluation M) ≫
        (restrictDualIso a (dual M)).hom =
      bidualEvaluation (M.restrict a) ≫ dualMap (restrictDualIso a M).hom := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro s
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro φ
  rfl

/-- Evaluation agrees with evaluation on the restricted sheaf. -/
@[reassoc]
theorem restrict_bidualEvaluation (a : Y ⟶ X) [IsOpenImmersion a] (M : X.Modules) :
    (Scheme.Modules.restrictFunctor a).map (bidualEvaluation M) ≫
        (restrictBidualIso a M).hom = bidualEvaluation (M.restrict a) := by
  change (Scheme.Modules.restrictFunctor a).map (bidualEvaluation M) ≫
      ((restrictDualIso a (dual M)).hom ≫ dualMap (restrictDualIso a M).inv) = _
  rw [← Category.assoc, restrict_bidualEvaluation_aux, Category.assoc,
    ← dualMap_comp, Iso.inv_hom_id, dualMap_id, Category.comp_id]

/-- Finite free restriction frames make the canonical evaluation invertible. -/
theorem bidualEvaluation_isIso_of_restrict_free_cover (M : X.Modules)
    {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)
    (J : I → Type u) (hJ : ∀ i, Finite (J i))
    (e : ∀ i, M.restrict (U i).ι ≅ SheafOfModules.free (J i)) :
    IsIso (bidualEvaluation M) := by
  apply OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isIso_of_isIso_restrict
    (bidualEvaluation M) U hU
  intro i
  let a := (U i).ι
  have := hJ i
  have : IsIso (bidualEvaluation (show (U i).toScheme.Modules from SheafOfModules.free (J i))) :=
    bidualEvaluation_free_isIso (J i)
  have : IsIso (bidualEvaluation (M.restrict a)) := bidualEvaluation_isIso_of_iso (e i)
  have hc : IsIso ((Scheme.Modules.restrictFunctor a).map (bidualEvaluation M) ≫
      (restrictBidualIso a M).hom) := by
    rw [restrict_bidualEvaluation]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hc

/-- An actual finite geometric frame cover proves canonical biduality. -/
theorem bidualEvaluation_isIso_of_finiteFrames {M : X.Modules}
    (D : TildeFiniteProjective.FiniteGeometricFrameCover M) :
    IsIso (bidualEvaluation M) :=
  bidualEvaluation_isIso_of_restrict_free_cover M D.U D.covers D.Q D.finite
    (fun i => (Scheme.Modules.restrictFunctorIsoPullback (D.U i).ι).app M ≪≫ D.frame i)

/-- Canonical biduality for a sheaf supplied with finite local frames. -/
def bidualIsoOfFiniteFrames {M : X.Modules}
    (D : TildeFiniteProjective.FiniteGeometricFrameCover M) : M ≅ dual (dual M) := by
  have := bidualEvaluation_isIso_of_finiteFrames D
  exact asIso (bidualEvaluation M)

@[simp]
theorem bidualIsoOfFiniteFrames_hom {M : X.Modules}
    (D : TildeFiniteProjective.FiniteGeometricFrameCover M) :
    (bidualIsoOfFiniteFrames D).hom = bidualEvaluation M := rfl

end SteinerGeometry.SheafDual
