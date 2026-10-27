import SteinerGeometry.TwistedSymmetricKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackLeftUnit

/-! Concrete base change of the line-bundle symmetric contraction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X)
local instance pullbackContractionBiproducts (Z : Scheme.{u}) : HasFiniteBiproducts Z.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
private instance pullbackContractionPullbackAdditive : (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- A nonvanishing coefficient cover remains a cover after any base change. -/
theorem sectionCover_pullback {n : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N))
    (he : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (e j)) :
    ∀ y : Y, ∃ j, y ∈ Ample.LineBundles.sectionNonvanishing
      (Ample.LineBundles.pullbackSection f (e j)) := by
  intro y
  obtain ⟨j, hj⟩ := he (f y)
  have hex : ∃ U : X.Opens, IsIso (Ample.LineBundles.pullbackSection U.ι (e j)) ∧ f y ∈ U := by
    simpa only [Ample.LineBundles.sectionNonvanishing, TopologicalSpace.Opens.mem_sSup,
      Set.mem_ofPred_eq] using hj
  obtain ⟨U, hU, hy⟩ := hex
  let _ := hU
  refine ⟨j, TopologicalSpace.Opens.mem_sSup.mpr ⟨f ⁻¹ᵁ U, ?_, hy⟩⟩
  exact Section.Nonvanishing.isIso_pullbackSection_preimage f (e j) U

/-- The actual tensor-unit comparison commutes with arbitrary pullback. -/
theorem pullback_unitLeft_inv (M : X.Modules) :
    (Scheme.Modules.pullback f).map (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv ≫
      Tensor.PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule X) M =
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso ((Scheme.Modules.pullback f).obj M)).inv ≫
        Tensor.Bifunctor.tensorModuleMap (Line.Bundles.structureModulePullbackIso f).inv
          (𝟙 ((Scheme.Modules.pullback f).obj M)) := by
  let P := Scheme.Modules.pullback f
  let h := Tensor.Bifunctor.tensorModuleMap (Line.Bundles.structureModulePullbackIso f).hom
    (𝟙 (P.obj M))
  apply (cancel_mono (h ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso (P.obj M)).hom)).mp
  simp only [Category.assoc]
  rw [Tensor.PullbackLeftUnit.tensorPullbackComparison_leftUnit_formula]
  rw [← P.map_comp]
  simp only [Iso.inv_hom_id, P.map_id]
  dsimp [h]
  rw [← Category.assoc
    (Tensor.Bifunctor.tensorModuleMap (Line.Bundles.structureModulePullbackIso f).inv _) _ _,
    Tensor.Bifunctor.tensorModuleMap_comp]
  simp only [Iso.inv_hom_id, Category.id_comp]
  rw [Tensor.Bifunctor.tensorModuleMap_id]
  simp
  rfl

/-- Multiplication by a line-bundle section commutes with actual scheme pullback. -/
theorem pullback_lineBundleSectionMultiply (N B : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ N.sheaf) :
    (Scheme.Modules.pullback f).map (LineBundle.SectionMultiplication.lineBundleSectionMultiply N B s) ≫
      (N.tensorBaseChangeIso f B).hom =
      LineBundle.SectionMultiplication.lineBundleSectionMultiply
        (N.pullback f) (B.pullback f) (Ample.LineBundles.pullbackSection f s) := by
  let P := Scheme.Modules.pullback f
  change P.map ((Tensor.ProductSheaf.tensorModuleUnitLeftIso B.sheaf).inv ≫
    Tensor.Bifunctor.tensorModuleMap s (𝟙 B.sheaf)) ≫
      Tensor.PullbackComparison.tensorPullbackComparison f N.sheaf B.sheaf = _
  rw [P.map_comp, Category.assoc, Tensor.PullbackComparison.tensorPullbackComparison_natural]
  rw [← Category.assoc, pullback_unitLeft_inv]
  rw [Category.assoc, Tensor.Bifunctor.tensorModuleMap_comp]
  simp only [Category.id_comp]
  rw [(Scheme.Modules.pullback f).map_id]
  rfl

/-- A finite sum of the original line bundle pulls back to the same finite sum
of the pulled-back line bundle. -/
def pullbackLineSumIso (B : Line.Bundles.LineBundle X) {ι : Type} [Fintype ι] :
    (Scheme.Modules.pullback f).obj (⨁ fun _ : ι => B.sheaf) ≅
      ⨁ fun _ : ι => (B.pullback f).sheaf :=
  additiveBiproductIso (Scheme.Modules.pullback f) _

/-- The target comparison includes the genuine tensor-product base-change map. -/
def pullbackContractionTargetIso (N B : Line.Bundles.LineBundle X) (n d : ℕ) :
    (Scheme.Modules.pullback f).obj
      (⨁ fun _ : Sym (Fin (n+1)) d => (N.tensor B).sheaf) ≅
        ⨁ fun _ : Sym (Fin (n+1)) d => ((N.pullback f).tensor (B.pullback f)).sheaf :=
  pullbackLineSumIso f (N.tensor B) ≪≫
    biproduct.mapIso (fun _ => N.tensorBaseChangeIso f B)

/-- The square for the derivative coefficient matrix commutes under arbitrary
scheme pullback, with its actual pulled-back line sections. -/
theorem curveSectionContraction_pullback (N B : Line.Bundles.LineBundle X) {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf)) :
    (pullbackLineSumIso f B (ι := Sym (Fin (n+1)) (d+1))).inv ≫
      (Scheme.Modules.pullback f).map (curveSectionContraction N B e d) ≫
      (pullbackContractionTargetIso f N B n d).hom =
      curveSectionContraction (N.pullback f) (B.pullback f)
        (fun i => Ample.LineBundles.pullbackSection f (e i)) d := by
  classical
  let P := Scheme.Modules.pullback f
  change _ = sectionContraction _ d
  apply biproduct.hom_ext'
  intro a
  apply biproduct.hom_ext
  intro b
  change biproduct.ι _ a ≫
      (biproduct.desc (fun i => P.map (biproduct.ι _ i))) ≫
      P.map (sectionContraction _ d) ≫
      (biproduct.lift (fun i => P.map (biproduct.π _ i)) ≫
        biproduct.map (fun _ => (N.tensorBaseChangeIso f B).hom)) ≫ biproduct.π _ b = _
  simp only [Category.assoc, biproduct.map_π, biproduct.lift_π_assoc,
    biproduct.ι_desc_assoc]
  rw [← P.map_comp_assoc, ← P.map_comp_assoc]
  simp only [Category.assoc]
  rw [sectionContraction_component, sectionContraction_component]
  simp only [P.map_sum, P.map_nsmul, Preadditive.sum_comp, Preadditive.nsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact pullback_lineBundleSectionMultiply f N B (e i)

/-- Whenever pullback preserves this kernel, its canonical comparison and
the concrete tensor square identify it with the pulled-back contraction. -/
def pullbackCurveKernelIso (N B : Line.Bundles.LineBundle X) {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf))
    [PreservesLimit (parallelPair (curveSectionContraction N B e d) 0)
      (Scheme.Modules.pullback f)] :
    (Scheme.Modules.pullback f).obj (kernel (curveSectionContraction N B e d)) ≅
      kernel (curveSectionContraction (N.pullback f) (B.pullback f)
        (fun i => Ample.LineBundles.pullbackSection f (e i)) d) :=
  PreservesKernel.iso (Scheme.Modules.pullback f) (curveSectionContraction N B e d) ≪≫
    kernel.mapIso _ _ (pullbackLineSumIso f B)
      (pullbackContractionTargetIso f N B n d) (by
        apply (cancel_epi (pullbackLineSumIso f B).inv).mp
        simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
          curveSectionContraction_pullback f N B e)

/-- A splitting of the first evaluation kernel after base change gives the
actual monomial-line decomposition of the pulled-back contraction kernel. -/
def pulledTwistedSymmetricKernelIso
    {K : Type u} [Field K] [CharZero K] (p : X ⟶ Spec (.of K)) {n d : ℕ}
    (N B : Line.Bundles.LineBundle X)
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf))
    (he : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (e j))
    (L : Fin n → Line.Bundles.LineBundle Y)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation
      (fun i => Ample.LineBundles.pullbackSection f (e i))))
    [PreservesLimit (parallelPair (curveSectionContraction N B e d) 0)
      (Scheme.Modules.pullback f)] :
    (⨁ fun a : Sym (Fin n) (d+1) => ((monomialLineBundle L a).tensor (B.pullback f)).sheaf) ≅
      (Scheme.Modules.pullback f).obj (kernel (curveSectionContraction N B e d)) :=
  twistedSymmetricKernelIso (f ≫ p) (N.pullback f) (B.pullback f)
      (fun i => Ample.LineBundles.pullbackSection f (e i)) (sectionCover_pullback f e he) L E ≪≫
    (pullbackCurveKernelIso f N B e).symm

end SteinerGeometry
