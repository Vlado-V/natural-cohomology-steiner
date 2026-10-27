module

public import SteinerGeometry.FinitePicardAvoidance
public import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EffectiveKernelCharacters
public import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterIndependence

set_option backward.privateInPublic true
@[expose] public section

/-! Actual natural characters of a finite group cover descend to distinct
finite-order line classes on its target. -/
noncomputable section
namespace SteinerGeometry.CharacterTorsion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
open scoped CategoryTheory.MonObj
universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {A B : Over (Spec (.of k))}
    [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- A character on every test scheme, natural for actual pullback of units. -/
structure NaturalKernelCharacter where
  value : ∀ T : Over (Spec (.of k)),
    (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ
  natural : ∀ {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
    Units.map t.left.appTop.hom (value T x) = value U (t ≫ x)

variable [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom]
    [GeometricallyConnected A.hom] [IsFinite f.left] [Flat f.left] [Surjective f.left]

/-- With no extra source functions, isomorphic descended lines recover the same actual kernel character. -/
theorem character_eq_of_lineClass_eq (hp : Function.Surjective A.hom.appTop)
    (χ ψ : ∀ T : Over (Spec (.of k)), (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over (Spec (.of k))} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))
    (hψ : ∀ {T U : Over (Spec (.of k))} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (ψ T x) = ψ U (t ≫ x))
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f ψ hψ)) :
    χ = ψ := by
  obtain ⟨e⟩ := Quotient.exact h
  funext T
  apply MonoidHom.ext
  intro z
  apply Units.ext
  let x : T ⟶ A := 1
  let y : T ⟶ A := x * (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)
  have hy : y ≫ f = x ≫ f := Picard.Homomorphisms.LineKernelCocycle.Construction.kernel_translate_comp f x z
  have hc := LineCharacterIndependence.Construction.KernelCharacters.canonicalScalar_eq_of_lineIso A.hom hp f.left
    (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ) (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f ψ hψ) e
    (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f χ hχ) (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f ψ hψ)
    (x ≫ f).left x.left y.left rfl (congrArg Over.Hom.left hy) (x.w.trans y.w.symm)
  exact (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine_kernelValue f χ hχ x z).symm.trans
    (hc.trans (EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine_kernelValue f ψ hψ x z))

/-- The genuine descended invertible sheaf, rather than a formal Picard symbol. -/
def descendedLine (χ : NaturalKernelCharacter f) : Line.Bundles.LineBundle B.left :=
  EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine
    f χ.value χ.natural

/-- Descent trivializes this line on the actual finite cover. -/
def descendedLine_pullbackIso (χ : NaturalKernelCharacter f) :
    ((descendedLine f χ).pullback f.left).sheaf ≅ Line.Bundles.structureModule A.left :=
  EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame
    f χ.value χ.natural

/-- Finite pullback kernel proves finite order, without identifying tensor
products of a separately constructed Fourier family. -/
def descendedTorsionClass (χ : NaturalKernelCharacter f) :
    TorsionLineClasses.TorsionClass B.left :=
  ⟨Line.Bundles.LineBundle.classOf (descendedLine f χ),
    FinitePicardAvoidance.pullback_trivial_isOfFinOrder f (descendedLine f χ)
      ⟨descendedLine_pullbackIso f χ⟩⟩

/-- Distinct actual natural kernel characters give distinct line classes. -/
theorem descendedTorsionClass_injective (hp : Function.Surjective A.hom.appTop) :
    Function.Injective (descendedTorsionClass f) := by
  intro χ ψ h
  have he : χ.value = ψ.value :=
    character_eq_of_lineClass_eq
      f hp χ.value ψ.value χ.natural ψ.natural (congrArg Subtype.val h)
  cases χ
  cases ψ
  cases he
  rfl

/-- A finite family of distinct kernel characters injects into actual torsion
line classes of the fixed target. -/
def characterFamilyEmbedding (hp : Function.Surjective A.hom.appTop)
    {J : Type u} (family : J → NaturalKernelCharacter f)
    (hinj : Function.Injective family) : J ↪ TorsionLineClasses.TorsionClass B.left where
  toFun j := descendedTorsionClass f (family j)
  inj' := (descendedTorsionClass_injective f hp).comp hinj

end SteinerGeometry.CharacterTorsion
