import SteinerGeometry.GeometricKernelLabels

/-! The group-valued, rather than only pointwise, kernel comparison. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry
open AbelianModuli.HilbertConstruction

theorem exists_kernelFunctorIso_of_points
    {K : Type} [Field K] [IsSepClosed K]
    {D C : Abelian.Schemes.AbelianScheme 1 (Spec (.of K))}
    (q : D.Isogeny C) [Etale q.hom.left]
    {G : Type} [Group G]
    (points : G ≃* q.kernelAt (𝟙_ (Over (Spec (.of K))))) :
    Nonempty (Constant.GroupMaps.constantGroupFunctor (Spec (.of K)) G ≅
      CyclicFromPoints.kernelFunctor q) := by
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
  exact ⟨Constant.GroupIsomorphisms.constantGroupIsoOfLabels
    (LocallyConstant.const (Spec (.of K)) (points.trans eH.symm)) ≪≫ e ≪≫
      CyclicFromPoints.kernelYonedaIso q⟩

def kernelFunctorIso_of_points
    {K : Type} [Field K] [IsSepClosed K]
    {D C : Abelian.Schemes.AbelianScheme 1 (Spec (.of K))}
    (q : D.Isogeny C) [Etale q.hom.left]
    {G : Type} [Group G]
    (points : G ≃* q.kernelAt (𝟙_ (Over (Spec (.of K))))) :
    Constant.GroupMaps.constantGroupFunctor (Spec (.of K)) G ≅
      CyclicFromPoints.kernelFunctor q :=
  Classical.choice (exists_kernelFunctorIso_of_points q points)

variable {S : Scheme} (A : Abelian.Schemes.AbelianScheme 1 S)
    (q : A.Isogeny A) (N : ℕ) (hq : q.hom = A.multiplication N)

def kernelTorsionPointsEquiv (T : Over S) : q.kernelAt T ≃* A.torsionPoints N T where
  toFun x := ⟨x.val, by
    change x.val ^ N = 1
    have hx : x.val ≫ q.hom = 1 := x.property
    simpa only [hq, A.comp_multiplication] using hx⟩
  invFun x := ⟨x.val, by
    have hx : x.val ^ N = 1 := x.property
    change x.val ≫ q.hom = 1
    simpa only [hq, A.comp_multiplication] using hx⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

def kernelTorsionFunctorIso : CyclicFromPoints.kernelFunctor q ≅ A.torsionFunctor N :=
  NatIso.ofComponents (fun T => (kernelTorsionPointsEquiv A q N hq T.unop).toGrpIso)
    (by
      intro T U f
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      exact Subtype.ext rfl)

end SteinerGeometry
