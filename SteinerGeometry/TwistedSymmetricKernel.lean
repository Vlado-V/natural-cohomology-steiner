import SteinerGeometry.SymmetricKernelGlobal
import SteinerGeometry.SectionContraction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MonoidalTensorNaturality

/-! Tensoring the symmetric contraction by an actual line bundle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u v

section Additive
variable {C : Type u} {D : Type v} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]

/-- An additive functor carries finite sums to finite sums, with the specified
chosen biproducts on both sides. -/
def additiveBiproductIso (F : C ⥤ D) [F.Additive] {ι : Type} [Fintype ι]
    (G : ι → C) : F.obj (⨁ G) ≅ ⨁ fun i => F.obj (G i) where
  hom := biproduct.lift (fun i => F.map (biproduct.π G i))
  inv := biproduct.desc (fun i => F.map (biproduct.ι G i))
  hom_inv_id := by
    rw [biproduct.lift_desc]
    simp only [← Functor.map_comp, ← Functor.map_sum, biproduct.total]
    exact F.map_id _
  inv_hom_id := by
    classical
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      ← Functor.map_comp]
    by_cases h : i = j
    · subst j
      simp
    · simp [biproduct.ι_π_ne _ h]

end Additive

variable {X : Scheme.{u}}
local instance twistedSymmetricKernelBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance twistedSymmetricKernelMonoidal : MonoidalCategory X.Modules := Module.SheafMonoidal.moduleMonoidalCategory X

private instance twistedSymmetricKernelRightTensorAdditive (B : Line.Bundles.LineBundle X) :
    (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Actual tensor products distribute over the fixed finite sums. -/
def rightTensorBiproductIso (B : Line.Bundles.LineBundle X)
    {ι : Type} [Fintype ι] (G : ι → X.Modules) :
    (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor.obj (⨁ G) ≅
      ⨁ fun i => Tensor.ProductSheaf.tensorModule (G i) B.sheaf :=
  additiveBiproductIso
      (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor G ≪≫
    biproduct.mapIso (fun i =>
      LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso B (G i))

@[simp, reassoc] theorem rightTensorBiproductIso_hom_π (B : Line.Bundles.LineBundle X)
    {ι : Type} [Fintype ι] (G : ι → X.Modules) (i : ι) :
    (rightTensorBiproductIso B G).hom ≫ biproduct.π _ i =
      (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor.map
        (biproduct.π G i) ≫
          (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso B (G i)).hom := by
  simp only [rightTensorBiproductIso, Iso.trans_hom, Category.assoc,
    biproduct.mapIso_hom, biproduct.map_π, additiveBiproductIso, biproduct.lift_π_assoc]

@[simp, reassoc] theorem rightTensorBiproductIso_ι_inv (B : Line.Bundles.LineBundle X)
    {ι : Type} [Fintype ι] (G : ι → X.Modules) (i : ι) :
    biproduct.ι _ i ≫ (rightTensorBiproductIso B G).inv =
      (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso B (G i)).inv ≫
        (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor.map
          (biproduct.ι G i) := by
  change biproduct.ι _ i ≫ (biproduct.map (fun j =>
      (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso B (G j)).inv) ≫
        biproduct.desc (fun j =>
          (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor.map
            (biproduct.ι G j))) = _
  rw [← Category.assoc, biproduct.ι_map, Category.assoc, biproduct.ι_desc]

/-- Tensoring a free monomial sheaf with B gives the corresponding sum of B. -/
def rightTensorFreeIso (B : Line.Bundles.LineBundle X) (n d : ℕ) :
    (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor.obj
      (homogeneousFreeSheaf (X := X) n d) ≅
        ⨁ fun _ : Sym (Fin (n+1)) d => B.sheaf :=
  rightTensorBiproductIso B (fun _ : Sym (Fin (n+1)) d => Line.Bundles.structureModule X) ≪≫
    biproduct.mapIso (fun _ => Tensor.ProductSheaf.tensorModuleUnitLeftIso B.sheaf)

@[simp, reassoc] theorem rightTensorFreeIso_ι_inv (B : Line.Bundles.LineBundle X)
    (n d : ℕ) (a : Sym (Fin (n+1)) d) :
    biproduct.ι _ a ≫ (rightTensorFreeIso B n d).inv =
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso B.sheaf).inv ≫
        (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso B
          (Line.Bundles.structureModule X)).inv ≫
          (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor.map
            (biproduct.ι (fun _ : Sym (Fin (n+1)) d => Line.Bundles.structureModule X) a) := by
  change biproduct.ι _ a ≫ (biproduct.map (fun _ =>
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso B.sheaf).inv) ≫
        (rightTensorBiproductIso B _).inv) = _
  rw [← Category.assoc, biproduct.ι_map, Category.assoc, rightTensorBiproductIso_ι_inv]

/-- The tensor transport of contraction is exactly multiplication by the same
sections with the same derivative multiplicities. -/
theorem rightTensor_sectionContraction (N B : Line.Bundles.LineBundle X) {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf)) :
    (rightTensorFreeIso B n (d+1)).inv ≫
      (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor.map
        (sectionContraction e d) ≫
        (rightTensorBiproductIso B (fun _ : Sym (Fin (n+1)) d => N.sheaf)).hom =
      curveSectionContraction N B e d := by
  classical
  let F := (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor
  change _ = sectionContraction (fun i =>
    (Tensor.ProductSheaf.tensorModuleUnitLeftIso B.sheaf).inv ≫
      Tensor.Bifunctor.tensorModuleMap (e i) (𝟙 B.sheaf)) d
  apply biproduct.hom_ext'
  intro a
  apply biproduct.hom_ext
  intro b
  rw [← Category.assoc, ← Category.assoc, rightTensorFreeIso_ι_inv]
  simp only [Category.assoc, rightTensorBiproductIso_hom_π]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [sectionContraction_component]
  change _ = biproduct.ι _ a ≫ sectionContraction _ d ≫ biproduct.π _ b
  rw [sectionContraction_component]
  simp only [Functor.map_sum, Functor.map_nsmul, Preadditive.comp_sum,
    Preadditive.comp_nsmul, Preadditive.sum_comp, Preadditive.nsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hn := Module.MonoidalTensorNaturality.moduleMonoidalTensorIso_natural_left (e i) B.sheaf
  change F.map (e i) ≫
      (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso B N.sheaf).hom =
    (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso B
      (Line.Bundles.structureModule X)).hom ≫ Tensor.Bifunctor.tensorModuleMap (e i) (𝟙 B.sheaf) at hn
  rw [hn, Iso.inv_hom_id_assoc]

/-- Tensoring the actual contraction kernel by B gives the kernel of the
section-multiplication contraction. -/
def rightTensorContractionKernelIso (N B : Line.Bundles.LineBundle X) {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf)) :
    (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor.obj
      (kernel (sectionContraction e d)) ≅ kernel (curveSectionContraction N B e d) :=
  PreservesKernel.iso
      (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor
      (sectionContraction e d) ≪≫
    kernel.mapIso _ _ (rightTensorFreeIso B n (d+1))
      (rightTensorBiproductIso B (fun _ : Sym (Fin (n+1)) d => N.sheaf)) (by
        apply (cancel_epi (rightTensorFreeIso B n (d+1)).inv).mp
        simpa only [Category.assoc, Iso.inv_hom_id_assoc] using rightTensor_sectionContraction N B e)

/-- The twisted symmetric kernel splits into the actual tensor-monomial line
bundles determined by a split first kernel. -/
def twistedSymmetricKernelIso
    {K : Type u} [Field K] [CharZero K] (p : X ⟶ Spec (.of K)) {n d : ℕ}
    (N B : Line.Bundles.LineBundle X)
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf))
    (he : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (e j))
    (L : Fin n → Line.Bundles.LineBundle X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e)) :
    (⨁ fun a : Sym (Fin n) (d+1) => ((monomialLineBundle L a).tensor B).sheaf) ≅
      kernel (curveSectionContraction N B e d) := by
  have := symmetricKernel_isIso (d := d) p N e he L E
  exact (rightTensorBiproductIso B
      (fun a : Sym (Fin n) (d+1) => (monomialLineBundle L a).sheaf)).symm ≪≫
    (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence B).functor.mapIso
      (asIso (splitMonomialKernelMap (d := d) e L (firstKernelColumns e L E)
        (firstKernelColumns_relation e L E))) ≪≫ rightTensorContractionKernelIso N B e

end SteinerGeometry
