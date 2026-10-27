module

public import SteinerGeometry.SheafDual
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.Dual

set_option backward.privateInPublic true
@[expose] public section

/-! Comparison of the two actual sheaf models of the module dual. -/
noncomputable section
namespace SteinerGeometry.SheafDual
open CategoryTheory AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
namespace NativeDual
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {X : Scheme.{u}} (M : X.Modules)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Bundle a local additive linear map as a morphism of module sheaves on the over-site. -/
def toOverHom (U : X.Opens) (a : Γ(dual M, U)) :
    M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) where
  val := PresheafOfModules.homMk a.val (fun V r s => a.property V.unop r s)

/-- Forget the module-map bundle while retaining its pointwise linearity proof. -/
def fromOverHom (U : X.Opens)
    (a : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) : Γ(dual M, U) :=
  ⟨((SheafOfModules.toSheaf _).map a).hom,
    fun V r s => (a.val.app (.op V)).hom.map_smul r s⟩

@[simp] theorem toOverHom_fromOverHom (U : X.Opens)
    (a : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    toOverHom M U (fromOverHom M U a) = a := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

@[simp] theorem fromOverHom_toOverHom (U : X.Opens) (a : Γ(dual M, U)) :
    fromOverHom M U (toOverHom M U a) = a := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  rfl

/-- The sectionwise linear equivalence between the internal-Hom dual and the
native projective dual. -/
def sectionLinearEquiv (U : X.Opens) :
    (dual M).val.obj (.op U) ≃ₗ[Γ(X, U)]
      (Dual.Scheme.Modules.dualObj M).val.obj (.op U) where
  toFun := toOverHom M U
  invFun := fromOverHom M U
  left_inv := fromOverHom_toOverHom M U
  right_inv := toOverHom_fromOverHom M U
  map_add' a b := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    rfl
  map_smul' r a := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change X.presheaf.map V.unop.hom.op r *
        (show Γ(X, V.unop.left) from a.val.app V s) =
      (show Γ(X, V.unop.left) from a.val.app V s) * X.presheaf.map V.unop.hom.op r
    exact mul_comm _ _

/-- Changing the presentation of local linear maps commutes with restriction. -/
theorem sectionLinearEquiv_natural {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (a : (dual M).val.obj U) :
    sectionLinearEquiv M V.unop ((dual M).val.map f a) =
      (Dual.Scheme.Modules.dualObj M).val.map f
        (sectionLinearEquiv M U.unop a) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

end NativeDual

open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {X : Scheme.{u}}

/-- The internal-Hom construction and the native projective construction give
canonically isomorphic actual module sheaves. -/
def nativeDualIso (M : X.Modules) : dual M ≅ Dual.Scheme.Modules.dualObj M :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk
      (fun U => (NativeDual.sectionLinearEquiv M U.unop).toModuleIso)
      (fun {_ _} f => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact NativeDual.sectionLinearEquiv_natural M f a))

/-- The comparison is natural for the contravariant dual maps. -/
theorem nativeDualIso_natural {M N : X.Modules} (f : M ⟶ N) :
    dualMap f ≫ (nativeDualIso M).hom =
      (nativeDualIso N).hom ≫ Dual.Scheme.Modules.dualMapObj f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

end SteinerGeometry.SheafDual
