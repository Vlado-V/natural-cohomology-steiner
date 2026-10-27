import SteinerGeometry.CyclicFromPoints
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup

/-! Compatibility of the actual zero-fiber kernel and the Picard equalizer kernel. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.KernelComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry
open AbelianModuli.HilbertConstruction

variable {S : Scheme} {D C : Abelian.Schemes.AbelianScheme 1 S}

/-- Both actual kernel objects represent the same zero-fiber functor. -/
def isogenyKernelIso (q : D.Isogeny C) :
    q.kernelScheme ≅ Picard.Homomorphisms.Kernel.Construction.kernelScheme q.hom :=
  (SteinerGeometry.exactKernelIso q
    (Picard.Homomorphisms.Kernel.Construction.kernelScheme q.hom)
    (Picard.Homomorphisms.Kernel.Construction.kernelInclusion q.hom)
    (Picard.Homomorphisms.Kernel.Construction.kernelScheme_universal q.hom)).symm

/-- The inverse comparison preserves the literal inclusion in the abelian scheme. -/
@[reassoc]
theorem isogenyKernelIso_inv_inclusion (q : D.Isogeny C) :
    (isogenyKernelIso q).inv ≫ q.kernelInclusion =
      Picard.Homomorphisms.Kernel.Construction.kernelInclusion q.hom :=
  SteinerGeometry.exactKernelIso_comp q
    (Picard.Homomorphisms.Kernel.Construction.kernelScheme q.hom)
    (Picard.Homomorphisms.Kernel.Construction.kernelInclusion q.hom)
    (Picard.Homomorphisms.Kernel.Construction.kernelScheme_universal q.hom)

/-- The comparison preserves the literal inclusion in the abelian scheme. -/
@[reassoc]
theorem isogenyKernelIso_hom_inclusion (q : D.Isogeny C) :
    (isogenyKernelIso q).hom ≫
        Picard.Homomorphisms.Kernel.Construction.kernelInclusion q.hom = q.kernelInclusion := by
  rw [← isogenyKernelIso_inv_inclusion q, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- Multiplication and unit preservation can be checked after a monic group inclusion. -/
theorem isMonHom_of_comp_mono {A B E : Over S} [MonObj A] [MonObj B] [MonObj E]
    (f : A ⟶ B) (g : B ⟶ E) [Mono g] [IsMonHom g] [IsMonHom (f ≫ g)] :
    IsMonHom f where
  one_hom := by
    apply (cancel_mono g).mp
    rw [Category.assoc, IsMonHom.one_hom (f ≫ g), IsMonHom.one_hom g]
  mul_hom := by
    apply (cancel_mono g).mp
    simp only [Category.assoc]
    rw [IsMonHom.mul_hom (f ≫ g), IsMonHom.mul_hom g,
      ← Category.assoc, tensorHom_comp_tensorHom]

/-- The comparison respects the represented group structures, not just the schemes. -/
instance isogenyKernelIso_hom_isMonHom (q : D.Isogeny C) :
    IsMonHom (isogenyKernelIso q).hom := by
  have : IsMonHom ((isogenyKernelIso q).hom ≫
      Picard.Homomorphisms.Kernel.Construction.kernelInclusion q.hom) := by
    rw [isogenyKernelIso_hom_inclusion]
    infer_instance
  exact isMonHom_of_comp_mono (isogenyKernelIso q).hom
    (Picard.Homomorphisms.Kernel.Construction.kernelInclusion q.hom)

/-- The inverse comparison also respects multiplication and the identity section. -/
instance isogenyKernelIso_inv_isMonHom (q : D.Isogeny C) :
    IsMonHom (isogenyKernelIso q).inv := inferInstance

end SteinerGeometry.KernelComparison
