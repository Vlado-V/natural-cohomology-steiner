module

public import OAI.AlgebraicGeometry.Seshadri.Sheaves.CartierTensor
public import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionCokernel

set_option backward.privateInPublic true
@[expose] public section

/-! Local tensor frames and finite-support cokernel vanishing on curves.
These proofs use only the local frames and topology; no curve projection or
projective cohomology construction is needed. -/

noncomputable section
namespace SteinerGeometry.CurveTensorFrames
open OAI OAI.MaximalSeshadri
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.SectionOpens
variable {X : Scheme.{0}}

def frameOnSmaller {M : X.Modules} {U : X.Opens} (e : M.restrict U.ι ≅ O U.toScheme)
    (V : X.Opens) (h : V ≤ U) : M.restrict V.ι ≅ O V.toScheme :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
      restrictFrame (X.homOfLE h) e

lemma common_affine_frames (L M : LineBundle X) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) ∧
      Nonempty (M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) := by
  obtain ⟨A,hA,⟨e⟩⟩ := L.locallyRankOne x
  obtain ⟨B,hB,⟨f⟩⟩ := M.locallyRankOne x
  obtain ⟨_,⟨U,hUa,rfl⟩,hx,hU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ A ⊓ B from ⟨hA,hB⟩)
      (A ⊓ B).isOpen
  exact ⟨⟨U,hUa⟩,hx,⟨frameOnSmaller e U (fun _ hy => (hU hy).1)⟩,
    ⟨frameOnSmaller f U (fun _ hy => (hU hy).2)⟩⟩

def tensorLineBundle (L M : LineBundle X) : LineBundle X where
  sheaf := moduleTensor X L.sheaf M.sheaf
  locallyRankOne x := by
    obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
    exact ⟨U.1,hx,⟨moduleTensorRestrict U.1 L.sheaf M.sheaf ≪≫
      moduleTensorIso e f ≪≫ moduleTensorUnit (O U.1.toScheme)⟩⟩

lemma sectionMultiply_eq (L M : LineBundle X) (s : O X ⟶ L.sheaf) :
    sectionMultiply L M s = (moduleTensorUnit M.sheaf).inv ≫
      moduleTensorMap s (𝟙 M.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let sheafification : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let counit : sheafification.obj M.sheaf.val ≅ M.sheaf :=
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app M.sheaf
  change counit.inv ≫ sheafification.map
      ((λ_ M.sheaf.val).inv ≫ (s.val ⊗ₘ 𝟙 M.sheaf.val)) =
    (counit.inv ≫ sheafification.map (λ_ M.sheaf.val).inv) ≫
      sheafification.map (s.val ⊗ₘ 𝟙 M.sheaf.val)
  rw [sheafification.map_comp, Category.assoc]

def tensorFrame (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (tensorLineBundle L M).sheaf.restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L.sheaf M.sheaf ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

def tensorUnitTwist (M : LineBundle X) (U : X.Opens)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M.sheaf).symm ≪≫
    moduleTensorRestrict U (O X) M.sheaf ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

lemma tensor_multiply_framed (L M : LineBundle X) (s : O X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    f.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (sectionMultiply L M s) ≫
      (tensorFrame L M U e f).hom = (tensorUnitTwist M U f).hom ≫
        (restrictSection U.ι s ≫ e.hom) := by
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let c : O U.toScheme ⟶ O U.toScheme := restrictSection U.ι s ≫ e.hom
  let unitRestriction : F.obj (O X) ≅ O U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  let sourceUnit : moduleTensor X (O X) M.sheaf ≅ M.sheaf :=
    moduleTensorUnit M.sheaf
  let targetUnit : moduleTensor U.toScheme (O U.toScheme) (O U.toScheme) ≅
      O U.toScheme := moduleTensorUnit (O U.toScheme)
  let sourceRestriction : F.obj (moduleTensor X (O X) M.sheaf) ≅
      moduleTensor U.toScheme (F.obj (O X)) (F.obj M.sheaf) :=
    moduleTensorRestrict U (O X) M.sheaf
  let targetRestriction : F.obj (moduleTensor X L.sheaf M.sheaf) ≅
      moduleTensor U.toScheme (F.obj L.sheaf) (F.obj M.sheaf) :=
    moduleTensorRestrict U L.sheaf M.sheaf
  let tensorMap : moduleTensor X (O X) M.sheaf ⟶ moduleTensor X L.sheaf M.sheaf :=
    moduleTensorMap s (𝟙 M.sheaf)
  let multiplication : M.sheaf ⟶ moduleTensor X L.sheaf M.sheaf :=
    sectionMultiply L M s
  have multiplication_eq : multiplication = sourceUnit.inv ≫ tensorMap :=
    sectionMultiply_eq L M s
  have he : F.map s ≫ e.hom = unitRestriction.hom ≫ c := by
    change F.map s ≫ e.hom = unitRestriction.hom ≫
      (unitRestriction.inv ≫ F.map s) ≫ e.hom
    exact ((Category.assoc _ _ _).trans
      (unitRestriction.hom_inv_id_assoc (F.map s ≫ e.hom))).symm
  have ht : moduleTensorMap (F.map s ≫ e.hom) f.hom =
      moduleTensorMap unitRestriction.hom f.hom ≫
        moduleTensorMap c (𝟙 (O U.toScheme)) := by
    rw [← moduleTensorMap_comp (X := U.toScheme),Category.comp_id,← he]
  have naturality : F.map tensorMap ≫ targetRestriction.hom =
      sourceRestriction.hom ≫ moduleTensorMap (F.map s) (𝟙 (F.obj M.sheaf)) := by
    have naturality' : F.map tensorMap ≫ targetRestriction.hom =
        sourceRestriction.hom ≫ moduleTensorMap (F.map s) (F.map (𝟙 M.sheaf)) :=
      moduleTensorRestrict_natural U s (𝟙 M.sheaf)
    simpa only [F.map_id] using naturality'
  change f.inv ≫ F.map multiplication ≫ targetRestriction.hom ≫
      moduleTensorMap (X := U.toScheme) e.hom f.hom ≫ targetUnit.hom =
    (f.inv ≫ F.map sourceUnit.inv ≫ sourceRestriction.hom ≫
      moduleTensorMap unitRestriction.hom f.hom ≫ targetUnit.hom) ≫ c
  rw [multiplication_eq, F.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map tensorMap), naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (moduleTensorMap (X := U.toScheme) (F.map s) (𝟙 _)),
    ← moduleTensorMap_comp (X := U.toScheme),
    Category.id_comp]
  rw [ht,Category.assoc]
  have hscalar : moduleTensorMap c (𝟙 (O U.toScheme)) ≫ targetUnit.hom =
      targetUnit.hom ≫ c := by
    exact (moduleTensorUnit_scalar (X := U.toScheme) c (𝟙 (O U.toScheme))).trans
      (congrArg (fun morphism : O U.toScheme ⟶ O U.toScheme =>
        targetUnit.hom ≫ morphism) (Category.comp_id c))
  rw [hscalar]

lemma tensor_multiply_isoOpen (L M : LineBundle X) (s : O X ⟶ L.sheaf) :
    isoOpen (sectionMultiply L M s) = isoOpen s := by
  apply SetLike.coe_injective
  ext x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
  have h : U.1.ι ⁻¹ᵁ isoOpen (sectionMultiply L M s) = U.1.ι ⁻¹ᵁ isoOpen s := by
    let restrictedMultiply : M.sheaf.restrict U.1.ι ⟶
        (tensorLineBundle L M).sheaf.restrict U.1.ι :=
      (Scheme.Modules.restrictFunctor U.1.ι).map (sectionMultiply L M s)
    let tensorTrivialization : (tensorLineBundle L M).sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
      tensorFrame L M U.1 e f
    calc
      _ = isoOpen restrictedMultiply := (isoOpen_restrict (sectionMultiply L M s) U.1.ι).symm
      _ = isoOpen (restrictedMultiply ≫ tensorTrivialization.hom) :=
        (isoOpen_postcomp restrictedMultiply tensorTrivialization).symm
      _ = isoOpen (f.inv ≫ restrictedMultiply ≫ tensorTrivialization.hom) :=
        (isoOpen_precomp f.symm (restrictedMultiply ≫ tensorTrivialization.hom)).symm
      _ = isoOpen ((tensorUnitTwist M U.1 f).hom ≫ (restrictSection U.1.ι s ≫ e.hom)) :=
        congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme => isoOpen morphism)
          (tensor_multiply_framed L M s U.1 e f)
      _ = isoOpen (restrictSection U.1.ι s ≫ e.hom) :=
        isoOpen_precomp (tensorUnitTwist M U.1 f) _
      _ = isoOpen (restrictSection U.1.ι s) := isoOpen_postcomp _ e
      _ = _ := isoOpen_restrictSection s U.1.ι
  exact SetLike.ext_iff.mp h ⟨x,hx⟩

lemma tensor_multiply_shortExact [IsIntegral X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    (ShortComplex.mk (sectionMultiply L M s) (cokernel.π (sectionMultiply L M s))
      (cokernel.condition _)).ShortExact := by
  exact {
    exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
    mono_f := sectionMultiply_mono L M s hs }

theorem tensor_multiply_cokernel_flasque [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (cokernel (sectionMultiply L M s))) := by
  let S : Set X := (isoOpen s : Set X)ᶜ
  have hfin : S.Finite := L.cokernel_support_finite hd s hs
  have hclosed : ∀ x ∈ S, IsClosed ({x} : Set X) := by
    intro x hx
    have hc : closure ({x} : Set X) ⊆ S :=
      closure_minimal (Set.singleton_subset_iff.mpr hx) (isoOpen s).isOpen.isClosed_compl
    have hsub : (closure ({x} : Set X)).Subsingleton := by
      apply proper_irreducible_closed_subsingleton hd isClosed_closure
        isIrreducible_singleton.closure
      intro he
      have hb : S = Set.univ := Set.eq_univ_of_univ_subset (he ▸ hc)
      exact L.isoOpen_ne_bot s hs (SetLike.coe_injective (by simpa [S] using hb))
    have he : closure ({x} : Set X) = {x} := by
      apply Set.Subset.antisymm
      · intro y hy
        exact hsub hy (subset_closure (Set.mem_singleton x))
      · exact subset_closure
    exact he ▸ isClosed_closure
  apply FiniteSupport.finite_closed_support_flasque _ S hfin hclosed
  intro x hx
  apply cokernel_stalk_subsingleton (sectionMultiply L M s) x
  rw [tensor_multiply_isoOpen]
  exact not_not.mp hx


end SteinerGeometry.CurveTensorFrames
