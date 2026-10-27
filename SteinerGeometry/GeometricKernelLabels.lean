module

public import SteinerGeometry.CyclicFromPoints

set_option backward.privateInPublic true
@[expose] public section

/-! Labels for the actual finite étale kernel, retaining its group structure. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry
open AbelianModuli.HilbertConstruction
open AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction

theorem geometricKernelIso_of_points
    {K : Type} [Field K] [IsSepClosed K]
    {D C : Abelian.Schemes.AbelianScheme 1 (Spec (.of K))}
    (q : D.Isogeny C) [Etale q.hom.left]
    {G : Type} [Group G]
    (points : G ≃* q.kernelAt (𝟙_ (Over (Spec (.of K))))) :
    ∃ e : (etaleGroupScheme (Spec (.of K)) G).X ≅ q.kernelScheme,
      IsMonHom e.hom ∧ IsMonHom (e.hom ≫ q.kernelInclusion) := by
  have : Etale q.kernelScheme.hom :=
    inferInstanceAs (Etale (pullback.snd q.hom.left η[C.scheme].left))
  obtain ⟨H, hH, hfin, ⟨e⟩⟩ :=
    AbelianModuli.ReferenceFamily.Geometric.Splitting.GeometricSplitting.exists_constant_groupIso q.kernelScheme
  let _ := hH
  let _ := hfin
  let eH : H ≃* q.kernelAt (𝟙_ (Over (Spec (.of K)))) :=
    (CyclicFromPoints.constantValuesEquiv (Spec (.of K)) H).trans
      (((e.app (Opposite.op (𝟙_ (Over (Spec (.of K)))))).groupIsoToMulEquiv).trans
        (((CyclicFromPoints.kernelYonedaIso q).app
          (Opposite.op (𝟙_ (Over (Spec (.of K)))))).groupIsoToMulEquiv))
  let labels := points.trans eH.symm
  let eFun : Constant.GroupMaps.constantGroupFunctor (Spec (.of K)) G ≅
      yonedaGrpObj q.kernelScheme :=
    Constant.GroupIsomorphisms.constantGroupIsoOfLabels
      (LocallyConstant.const (Spec (.of K)) labels) ≪≫ e
  let eGrp : etaleGroupScheme (Spec (.of K)) G ≅ Grp.mk q.kernelScheme :=
    (yonedaGrpFullyFaithful (C := Over (Spec (.of K)))).preimageIso
      (etaleGroupPointIso (Spec (.of K)) G ≪≫ eFun)
  refine ⟨(Grp.forget (Over (Spec (.of K)))).mapIso eGrp, ?_, ?_⟩
  · change IsMonHom eGrp.hom.hom.hom
    infer_instance
  · change IsMonHom (eGrp.hom.hom.hom ≫ q.kernelInclusion)
    infer_instance

end SteinerGeometry
