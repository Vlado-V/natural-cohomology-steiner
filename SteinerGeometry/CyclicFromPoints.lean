import SteinerGeometry.CyclicSubgroup
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Splitting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry
open AbelianModuli.HilbertConstruction
open AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction

namespace SteinerGeometry.CyclicFromPoints

variable {S : Scheme} {D C : Abelian.Schemes.AbelianScheme 1 S}

/-- The actual kernel group on test schemes. -/
def kernelFunctor (q : D.Isogeny C) : (Over S)ᵒᵖ ⥤ GrpCat where
  obj T := GrpCat.of (q.kernelAt T.unop)
  map f := GrpCat.ofHom
    { toFun := fun a => ⟨f.unop ≫ a.val, by
        change (f.unop ≫ a.val) ≫ q.hom = 1
        rw [Category.assoc, show a.val ≫ q.hom = 1 from a.property, MonObj.comp_one]⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' a b := Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact Subtype.ext (Category.id_comp _)
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact Subtype.ext (Category.assoc _ _ _)

def kernelRepresentable (q : D.Isogeny C) :
    (kernelFunctor q ⋙ forget GrpCat).RepresentableBy q.kernelScheme where
  homEquiv := q.kernelSchemePointsEquiv _
  homEquiv_comp f t := Subtype.ext (Category.assoc f t q.kernelInclusion)

instance cyclicKernelGroup (q : D.Isogeny C) : GrpObj q.kernelScheme :=
  GrpObj.ofRepresentableBy q.kernelScheme (kernelFunctor q) (kernelRepresentable q)

def kernelYonedaIso (q : D.Isogeny C) : yonedaGrpObj q.kernelScheme ≅ kernelFunctor q :=
  yonedaGrpObjIsoOfRepresentableBy q.kernelScheme (kernelFunctor q) (kernelRepresentable q)

instance cyclicKernelInclusion_isMonHom (q : D.Isogeny C) : IsMonHom q.kernelInclusion where
  one_hom := by
    have h := congrArg (fun x : q.kernelAt (𝟙_ (Over S)) => x.val)
      (((kernelYonedaIso q).hom.app (Opposite.op (𝟙_ (Over S)))).hom.map_one)
    change (1 : 𝟙_ (Over S) ⟶ q.kernelScheme) ≫ q.kernelInclusion = 1 at h
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h
  mul_hom := by
    let T := q.kernelScheme
    let i := q.kernelInclusion
    have h := congrArg (fun x : q.kernelAt (T ⊗ T) => x.val)
      (((kernelYonedaIso q).hom.app (Opposite.op (T ⊗ T))).hom.map_mul (fst T T) (snd T T))
    change (fst T T * snd T T) ≫ i = (fst T T ≫ i) * (snd T T ≫ i) at h
    have hp : lift (fst T T ≫ i) (snd T T ≫ i) = i ⊗ₘ i := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst, tensorHom_fst]; rfl
      · simp only [lift_snd, tensorHom_snd]; rfl
    exact (congrArg (fun f => f ≫ i) (MonObj.mul_eq_mul (M := T))).trans
      (h.trans (congrArg (fun f => f ≫ μ[D.scheme]) hp))

def constantValuesEquiv (S : Scheme) [Subsingleton S] [Nonempty S]
    (G : Type) [Group G] : G ≃* LocallyConstant S G where
  toFun := LocallyConstant.const S
  invFun f := f (Classical.choice inferInstance)
  left_inv _ := rfl
  right_inv f := by
    apply LocallyConstant.ext
    intro x
    exact congrArg f (Subsingleton.elim _ _)
  map_mul' _ _ := rfl

/-- A cyclic identification of geometric kernel points gives a cyclic scheme kernel. -/
theorem exists_kernelIso_ofKernelPoints {K : Type} [Field K] [IsSepClosed K]
    {D C : Abelian.Schemes.AbelianScheme 1 (Spec (.of K))}
    (q : D.Isogeny C) [Etale q.hom.left] {n : ℕ} [NeZero n]
    (points : Multiplicative (ZMod n) ≃* q.kernelAt (𝟙_ (Over (Spec (.of K))))) :
    ∃ e : (cyclicGroup (S := Spec (.of K)) n).X ≅ q.kernelScheme,
      IsMonHom (e.hom ≫ q.kernelInclusion) := by
  have : Etale q.kernelScheme.hom :=
    inferInstanceAs (Etale (pullback.snd q.hom.left η[C.scheme].left))
  obtain ⟨G, hG, hfin, ⟨e⟩⟩ :=
    AbelianModuli.ReferenceFamily.Geometric.Splitting.GeometricSplitting.exists_constant_groupIso q.kernelScheme
  let _ := hG
  let _ := hfin
  let eG : G ≃* q.kernelAt (𝟙_ (Over (Spec (.of K)))) :=
    (constantValuesEquiv (Spec (.of K)) G).trans
      (((e.app (Opposite.op (𝟙_ (Over (Spec (.of K)))))).groupIsoToMulEquiv).trans
        (((kernelYonedaIso q).app (Opposite.op (𝟙_ (Over (Spec (.of K)))))).groupIsoToMulEquiv))
  let eLabels := points.trans eG.symm
  let eFun : AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor
      (Spec (.of K)) (Multiplicative (ZMod n)) ≅ yonedaGrpObj q.kernelScheme :=
    AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms.constantGroupIsoOfLabels
      (LocallyConstant.const (Spec (.of K)) eLabels) ≪≫ e
  let eGrp : cyclicGroup (S := Spec (.of K)) n ≅ Grp.mk q.kernelScheme :=
    (yonedaGrpFullyFaithful (C := Over (Spec (.of K)))).preimageIso
      (etaleGroupPointIso (Spec (.of K)) (Multiplicative (ZMod n)) ≪≫ eFun)
  let eScheme := (Grp.forget (Over (Spec (.of K)))).mapIso eGrp
  refine ⟨eScheme, ?_⟩
  change IsMonHom (eGrp.hom.hom.hom ≫ q.kernelInclusion)
  infer_instance

theorem exists_ofKernelPoints {K : Type} [Field K] [IsSepClosed K]
    {D C : Abelian.Schemes.AbelianScheme 1 (Spec (.of K))}
    (q : D.Isogeny C) [Etale q.hom.left] {n : ℕ} [NeZero n]
    (points : Multiplicative (ZMod n) ≃* q.kernelAt (𝟙_ (Over (Spec (.of K))))) :
    Nonempty (CyclicEtaleIsogeny D n) := by
  obtain ⟨e, he⟩ := exists_kernelIso_ofKernelPoints q points
  let : ConnectedSpace C.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton C.scheme.hom
  exact ⟨⟨C, q, inferInstance,
    fun c => isogeny_degree_of_cyclicKernel q e (Classical.choice inferInstance) c,
    e, he⟩⟩

end SteinerGeometry.CyclicFromPoints
