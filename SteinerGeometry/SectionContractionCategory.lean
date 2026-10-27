import Steiner.OperatorDuality
import SteinerGeometry.SectionContractionAlgebra
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Symmetric contraction is an actual morphism of finite sums. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits Steiner MvPolynomial

universe u v
section Coordinates
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {K : Type*} [Ring K]

/-- Coordinates in the image of a finite biproduct under an additive module-valued functor. -/
def biproductCoordinates (F : C ⥤ ModuleCat K) [F.Additive]
    (B : C) (ι : Type) [Fintype ι] :
    F.obj (⨁ fun _ : ι => B) ≃ₗ[K] (ι → F.obj B) where
  toFun x i := F.map (biproduct.π (fun _ : ι => B) i) x
  invFun x := ∑ i, F.map (biproduct.ι (fun _ : ι => B) i) (x i)
  left_inv x := by
    have h := congrArg (fun f : (⨁ fun _ : ι => B) ⟶ ⨁ fun _ : ι => B => F.map f x)
      (biproduct.total (f := fun _ : ι => B))
    simpa only [F.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply, F.map_comp, ModuleCat.comp_apply,
      F.map_id, ModuleCat.id_apply] using h
  right_inv x := by
    classical
    funext i
    simp only [map_sum]
    have hcomp (j : ι) : F.map (biproduct.π (fun _ : ι => B) i)
        (F.map (biproduct.ι (fun _ : ι => B) j) (x j)) = if j = i then x j else 0 := by
      rw [← ModuleCat.comp_apply, ← F.map_comp]
      by_cases hji : j = i
      · subst j
        simp
      · simp [biproduct.ι_π_ne _ hji, hji]
    simp only [hcomp]
    simp
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' a x := by ext i; exact map_smul _ _ _

end Coordinates

section Maps
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {K : Type*} [Field K]
variable {n : ℕ} {B D : C}

/-- Natural multiplicity of one coordinate derivative between monomial indices. -/
def contractionMultiplicity (d : ℕ) (a : Sym (Fin (n+1)) (d+1))
    (b : Sym (Fin (n+1)) d) (i : Fin (n+1)) : ℕ :=
  if operatorExponent (d+1) a = operatorExponent d b + Finsupp.single i 1
    then operatorExponent d b i + 1 else 0

/-- The actual morphism of finite sums implementing homogeneous symmetric contraction. -/
def sectionContraction (T : Fin (n+1) → (B ⟶ D)) (d : ℕ) :
    (⨁ fun _ : Sym (Fin (n+1)) (d+1) => B) ⟶
      (⨁ fun _ : Sym (Fin (n+1)) d => D) :=
  biproduct.matrix (fun a b => ∑ i, contractionMultiplicity d a b i • T i)

@[simp] theorem sectionContraction_component (T : Fin (n+1) → (B ⟶ D)) (d : ℕ)
    (a : Sym (Fin (n+1)) (d+1)) (b : Sym (Fin (n+1)) d) :
    biproduct.ι _ a ≫ sectionContraction T d ≫ biproduct.π _ b =
      ∑ i, contractionMultiplicity d a b i • T i := by
  exact biproduct.matrix_components _ _ _

/-- The section formula before choosing a coefficient field: all matrix entries
are literal natural-number multiplicities, so this holds over any ring. -/
theorem sectionContraction_sections_weighted {R : Type*} [Ring R]
    (F : C ⥤ ModuleCat R) [F.Additive]
    (T : Fin (n+1) → (B ⟶ D)) (d : ℕ)
    (x : Sym (Fin (n+1)) (d+1) → F.obj B) (b : Sym (Fin (n+1)) d) :
    biproductCoordinates F D (Sym (Fin (n+1)) d)
      (F.map (sectionContraction T d)
        ((biproductCoordinates F B (Sym (Fin (n+1)) (d+1))).symm x)) b =
      ∑ a : Sym (Fin (n+1)) (d+1), ∑ i : Fin (n+1),
        contractionMultiplicity d a b i • (F.map (T i) (x a)) := by
  classical
  change F.map (biproduct.π _ b)
      (F.map (sectionContraction T d) (∑ a, F.map (biproduct.ι _ a) (x a))) = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← F.map_comp, ← F.map_comp,
    sectionContraction_component, F.map_sum]
  change (∑ i, F.map (contractionMultiplicity d a b i • T i)).hom (x a) = _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [F.map_nsmul, ModuleCat.hom_nsmul, LinearMap.smul_apply]

/-- Taking sections under any additive functor produces exactly the coefficient differential. -/
theorem sectionContraction_sections (F : C ⥤ ModuleCat K) [F.Additive]
    (T : Fin (n+1) → (B ⟶ D)) (d : ℕ)
    (x : Sym (Fin (n+1)) (d+1) → F.obj B) :
    biproductCoordinates F D (Sym (Fin (n+1)) d)
      (F.map (sectionContraction T d)
        ((biproductCoordinates F B (Sym (Fin (n+1)) (d+1))).symm x)) =
      operatorDifferential (fun i => (F.map (T i)).hom) d x := by
  classical
  ext b
  change F.map (biproduct.π _ b)
      (F.map (sectionContraction T d) (∑ a, F.map (biproduct.ι _ a) (x a))) = _
  simp only [map_sum]
  rw [operatorDifferential_coeff]
  apply Finset.sum_congr rfl
  intro a _
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← F.map_comp, ← F.map_comp,
    sectionContraction_component, F.map_sum]
  change (∑ i, F.map (contractionMultiplicity d a b i • T i)).hom (x a) = _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [F.map_nsmul, ModuleCat.hom_nsmul, LinearMap.smul_apply, contractionMultiplicity, coeff_pderiv,
    coeff_monomial]
  split_ifs with h
  · simpa only [Nat.cast_add, Nat.cast_one, one_mul] using
      (Nat.cast_smul_eq_nsmul K (operatorExponent d b i + 1) ((F.map (T i)).hom (x a))).symm
  · simp

/-- A surjective coefficient after an additive module-valued functor makes the
whole finite contraction matrix surjective after that same functor. -/
theorem sectionContraction_map_surjective [CharZero K]
    (F : C ⥤ ModuleCat K) [F.Additive] (T : Fin (n+1) → (B ⟶ D))
    (j : Fin (n+1)) (hT : Function.Surjective (F.map (T j))) (d : ℕ) :
    Function.Surjective (F.map (sectionContraction T d)) := by
  intro y
  obtain ⟨x, hx⟩ := operatorDifferential_surjective_of_coefficient
    (fun i => (F.map (T i)).hom) j hT d
    (biproductCoordinates F D (Sym (Fin (n+1)) d) y)
  refine ⟨(biproductCoordinates F B (Sym (Fin (n+1)) (d+1))).symm x, ?_⟩
  apply (biproductCoordinates F D (Sym (Fin (n+1)) d)).injective
  rw [sectionContraction_sections, hx]

end Maps

variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]
variable {K : Type*} [Field K] {n : ℕ} {B D : C}

/-- Sections of the actual kernel sheaf identify with the kernel of the coefficient
operator whenever the section functor preserves finite limits. -/
theorem sectionContraction_kernel_sections [HasFiniteLimits C]
    (F : C ⥤ ModuleCat K) [F.Additive] [PreservesFiniteLimits F]
    (T : Fin (n+1) → (B ⟶ D)) (d : ℕ)
    (x : Sym (Fin (n+1)) (d+1) → F.obj B) :
    operatorDifferential (fun i => (F.map (T i)).hom) d x = 0 ↔
      ∃! z : F.obj (kernel (sectionContraction T d)),
        biproductCoordinates F B (Sym (Fin (n+1)) (d+1))
          (F.map (kernel.ι (sectionContraction T d)) z) = x := by
  let S := ShortComplex.kernelSequence (sectionContraction T d)
  have hS : (S.map F).Exact := (ShortComplex.kernelSequence_exact _).map_of_mono_of_preservesKernel
    F inferInstance inferInstance
  have hi : Function.Injective (F.map (kernel.ι (sectionContraction T d))) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  constructor
  · intro hx
    let y := (biproductCoordinates F B (Sym (Fin (n+1)) (d+1))).symm x
    have hy : F.map (sectionContraction T d) y = 0 := by
      apply (biproductCoordinates F D (Sym (Fin (n+1)) d)).injective
      simpa only [y, sectionContraction_sections, map_zero] using hx
    obtain ⟨z, hz⟩ := (S.map F).moduleCat_exact_iff.mp hS y hy
    refine ⟨z, ?_, ?_⟩
    · change biproductCoordinates F B _ (F.map (kernel.ι _) z) = x
      change F.map (kernel.ι _) z = y at hz
      rw [hz]
      exact LinearEquiv.apply_symm_apply _ x
    · intro z' hz'
      apply hi
      apply (biproductCoordinates F B (Sym (Fin (n+1)) (d+1))).injective
      rw [hz']
      change x = biproductCoordinates F B _ (F.map (kernel.ι _) z)
      rw [show F.map (kernel.ι _) z = y from hz]
      exact (LinearEquiv.apply_symm_apply _ x).symm
  · rintro ⟨z, hz, _⟩
    rw [← hz]
    have hzero : F.map (sectionContraction T d) (F.map (kernel.ι _) z) = 0 := by
      rw [← ModuleCat.comp_apply, ← F.map_comp, kernel.condition, F.map_zero]
      rfl
    have h := sectionContraction_sections F T d
      (biproductCoordinates F B (Sym (Fin (n+1)) (d+1))
        (F.map (kernel.ι (sectionContraction T d)) z))
    rw [LinearEquiv.symm_apply_apply, hzero, map_zero] at h
    exact h.symm

end SteinerGeometry
