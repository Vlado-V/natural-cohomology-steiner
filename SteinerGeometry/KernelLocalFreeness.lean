module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Spaces

set_option backward.privateInPublic true
@[expose] public section

/-! # Locally free kernels from actual local split frames
A map locally conjugate to a projection onto a free direct summand has a
locally free kernel. The isomorphisms are constructed from preservation of
kernels by restriction and the categorical kernel of a biproduct projection.
-/

noncomputable section
namespace SteinerGeometry.KernelLocalFreeness

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

/-- Restriction to an open subscheme preserves finite limits. -/
theorem restrict_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  let G : TopCat.Presheaf AddCommGrpCat.{u} Y ⥤ TopCat.Presheaf AddCommGrpCat.{u} X :=
    (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op
  let : PreservesFiniteLimits G := by
    constructor
    intro J _ _
    exact whiskeringLeft_preservesLimitsOfShape J f.opensFunctor.op
  let : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f ⋙
      Scheme.Modules.toPresheaf X) :=
    comp_preservesFiniteLimits (Scheme.Modules.toPresheaf Y) G
  exact preservesFiniteLimits_of_reflects_of_preserves
    (Scheme.Modules.restrictFunctor f) (Scheme.Modules.toPresheaf X)

abbrev openFunctor (X : Scheme.{u}) (U : X.Opens) :
    X.Modules ⥤ SheafOfModules.{u} (X.ringCatSheaf.over U) :=
  SheafOfModules.overFunctor X.ringCatSheaf U

instance openFunctor_additive (X : Scheme.{u}) (U : X.Opens) :
    (openFunctor X U).Additive where
  map_add := rfl

instance openFunctor_preservesFiniteLimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteLimits (openFunctor X U) := by
  let F := openFunctor X U
  let G := (Scheme.Modules.overEquiv U).functor
  have hR : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) :=
    restrict_preservesFiniteLimits U.ι
  let : PreservesFiniteLimits (F ⋙ G) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _ (Scheme.Modules.overFunctorEquiv U).symm hR
  exact preservesFiniteLimits_of_reflects_of_preserves F G

/-- Local split frames identify the restriction of the genuine kernel with
the complementary free summand. -/
def localKernelIso {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (P Q : Type u)
    (eM : M.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) P ⊞
      SheafOfModules.free (R := X.ringCatSheaf.over U) Q)
    (eN : N.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) P)
    (hf : (openFunctor X U).map f ≫ eN.hom = eM.hom ≫ biprod.fst) :
    (kernel f).over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) Q :=
  PreservesKernel.iso (openFunctor X U) f ≪≫
    kernel.mapIso _ _ eM eN hf ≪≫ kernelBiprodFstIso

/-- A free frame supplies generators whose presentation map is an isomorphism. -/
def frameGenerators {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (Q : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) Q ≅ M.over U) :
    (M.over U).GeneratingSections :=
  (SheafOfModules.free.generatingSections Q).ofEpi e.hom

theorem frameGenerators_isIso {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (Q : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) Q ≅ M.over U) :
    IsIso (frameGenerators M U Q e).π := by
  unfold frameGenerators
  rw [SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
  change IsIso ((𝟙 _) ≫ e.hom)
  rw [Category.id_comp]
  infer_instance

/-- The local data built from explicit free frames. -/
def frameData {X : Scheme.{u}} (M : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : iSup U = ⊤) (Q : Type u)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) Q ≅ M.over (U i)) :
    M.LocalGeneratorsData where
  I := I
  X := U
  coversTop := by
    rw [Opens.coversTop_iff]
    exact IsOpenCover.mk hU
  generators i := frameGenerators M (U i) Q (e i)

theorem frameData_locallyFree {X : Scheme.{u}} (M : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : iSup U = ⊤) (Q : Type u)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) Q ≅ M.over (U i)) :
    (frameData M U hU Q e).IsLocallyFreeData where
  isIso i := frameGenerators_isIso M (U i) Q (e i)

/-- An actual map with local projection frames has a locally free kernel. -/
theorem kernel_locallyFree_of_local_split_frames {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤) (P Q : Type u)
    (eM : ∀ i, (M.over (U i)) ≅ SheafOfModules.free (R := X.ringCatSheaf.over (U i)) P ⊞
      SheafOfModules.free (R := X.ringCatSheaf.over (U i)) Q)
    (eN : ∀ i, (N.over (U i)) ≅ SheafOfModules.free (R := X.ringCatSheaf.over (U i)) P)
    (hf : ∀ i, (openFunctor X (U i)).map f ≫ (eN i).hom = (eM i).hom ≫ biprod.fst) :
    (kernel f).IsLocallyFree := by
  let e := fun i => (localKernelIso f (U i) P Q (eM i) (eN i) (hf i)).symm
  let q := frameData (kernel f) U hU Q e
  let : q.IsLocallyFreeData := frameData_locallyFree (kernel f) U hU Q e
  exact q.isLocallyFree

/-- When the complementary frame is finite, the same kernel is of finite
 type and quasicoherent, in addition to being locally free. -/
theorem kernel_finiteType_of_local_split_frames {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤) (P Q : Type u) [Finite Q]
    (eM : ∀ i, (M.over (U i)) ≅ SheafOfModules.free (R := X.ringCatSheaf.over (U i)) P ⊞
      SheafOfModules.free (R := X.ringCatSheaf.over (U i)) Q)
    (eN : ∀ i, (N.over (U i)) ≅ SheafOfModules.free (R := X.ringCatSheaf.over (U i)) P)
    (hf : ∀ i, (openFunctor X (U i)).map f ≫ (eN i).hom = (eM i).hom ≫ biprod.fst) :
    (kernel f).IsQuasicoherent ∧ (kernel f).IsFiniteType := by
  let e := fun i => (localKernelIso f (U i) P Q (eM i) (eN i) (hf i)).symm
  let q := frameData (kernel f) U hU Q e
  let : q.IsLocallyFreeData := frameData_locallyFree (kernel f) U hU Q e
  constructor
  · exact q.quasiCoherentData.isQuasicoherent
  · refine { exists_localGeneratorsData := ?_ }
    refine ⟨q, ?_⟩
    constructor
    intro i
    exact ⟨inferInstanceAs (Finite Q)⟩


/-- Local free frames may have different finite ranks on different opens. -/
def varyingFrameData {X : Scheme.{u}} (M : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : iSup U = ⊤) (Q : I → Type u)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Q i) ≅ M.over (U i)) :
    M.LocalGeneratorsData where
  I := I
  X := U
  coversTop := by
    rw [Opens.coversTop_iff]
    exact IsOpenCover.mk hU
  generators i := frameGenerators M (U i) (Q i) (e i)

theorem varyingFrameData_locallyFree {X : Scheme.{u}} (M : X.Modules) {I : Type u}
    (U : I → X.Opens) (hU : iSup U = ⊤) (Q : I → Type u)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Q i) ≅ M.over (U i)) :
    (varyingFrameData M U hU Q e).IsLocallyFreeData where
  isIso i := frameGenerators_isIso M (U i) (Q i) (e i)

/-- Arbitrary local frames yield the standard locally-free predicate. -/
theorem locallyFree_of_local_frames {X : Scheme.{u}} (M : X.Modules) {I : Type u}
    (U : I → X.Opens) (hU : iSup U = ⊤) (Q : I → Type u)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Q i) ≅ M.over (U i)) :
    M.IsLocallyFree := by
  let q := varyingFrameData M U hU Q e
  let : q.IsLocallyFreeData := varyingFrameData_locallyFree M U hU Q e
  exact q.isLocallyFree

/-- Finite local frames also supply finite type and quasicoherence. -/
theorem finiteType_of_local_frames {X : Scheme.{u}} (M : X.Modules) {I : Type u}
    (U : I → X.Opens) (hU : iSup U = ⊤) (Q : I → Type u) [hQ : ∀ i, Finite (Q i)]
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (Q i) ≅ M.over (U i)) :
    M.IsQuasicoherent ∧ M.IsFiniteType := by
  let q := varyingFrameData M U hU Q e
  let : q.IsLocallyFreeData := varyingFrameData_locallyFree M U hU Q e
  constructor
  · exact q.quasiCoherentData.isQuasicoherent
  · refine { exists_localGeneratorsData := ?_ }
    refine ⟨q, ?_⟩
    constructor
    intro i
    exact ⟨hQ i⟩

end SteinerGeometry.KernelLocalFreeness
