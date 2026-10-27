module

public import SteinerGeometry.ConstantKernelCharacters
public import SteinerGeometry.CyclicScalarCharacters
public import SteinerGeometry.KernelComparison

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry.CyclicNaturalCharacters

noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

attribute [local instance] Over.cartesianMonoidalCategory

abbrev base := Spec (.of ℂ)

def complexCoefficientUnits : ℂˣ →* Γ(base, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of ℂ)).inv.hom.toMonoidHom

theorem complexCoefficientUnits_injective : Function.Injective complexCoefficientUnits := by
  intro a b h
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of ℂ)).inv).1
  exact congrArg Units.val h

def coefficientCharacter {G : Type} [Group G] (χ : G →* ℂˣ) : G →* Γ(base, ⊤)ˣ :=
  complexCoefficientUnits.comp χ

theorem coefficientCharacter_injective {G : Type} [Group G] :
    Function.Injective (coefficientCharacter (G := G)) := by
  intro χ ψ h
  apply MonoidHom.ext
  intro g
  exact complexCoefficientUnits_injective (DFunLike.congr_fun h g)

variable (m : ℕ) [NeZero m]
    {K : Over base} [GrpObj K]
    (e : ConstantKernelCharacters.groupScheme base (Multiplicative (ZMod m)) ≅ K)
    [IsMonHom e.inv]

def fromCharacter (χ : Multiplicative (ZMod m) →* ℂˣ) :
    ∀ T : Over base, (T ⟶ K) →* Γ(T.left, ⊤)ˣ :=
  ConstantKernelCharacters.transportedValue base (Multiplicative (ZMod m)) e (coefficientCharacter χ)

omit [NeZero m] in
theorem fromCharacter_natural (χ : Multiplicative (ZMod m) →* ℂˣ)
    {T U : Over base} (t : U ⟶ T) (x : T ⟶ K) :
    Units.map t.left.appTop.hom (fromCharacter m e χ T x) =
      fromCharacter m e χ U (t ≫ x) :=
  ConstantKernelCharacters.transportedValue_natural base (Multiplicative (ZMod m))
    e (coefficientCharacter χ) t x

omit [NeZero m] in
theorem fromCharacter_injective : Function.Injective (fromCharacter m e) :=
  (ConstantKernelCharacters.transportedValue_injective base (Multiplicative (ZMod m)) e).comp
    coefficientCharacter_injective

include e in
/-- Distinct natural regular-unit characters on a genuinely constant cyclic group scheme. -/
theorem exists_family :
    ∃ family : Fin m → ∀ T : Over base, (T ⟶ K) →* Γ(T.left, ⊤)ˣ,
      (∀ j {T U : Over base} (t : U ⟶ T) (x : T ⟶ K),
        Units.map t.left.appTop.hom (family j T x) = family j U (t ≫ x)) ∧
      Function.Injective family := by
  obtain ⟨χ, hχ⟩ := exists_cyclicScalarCharacters m
  exact ⟨fun j => fromCharacter m e (χ j), fun j => fromCharacter_natural m e (χ j),
    (fromCharacter_injective m e).comp hχ⟩

/-- The natural characters are characters of the actual Picard kernel of the isogeny. -/
theorem exists_isogenyKernelFamily {D C : Abelian.Schemes.AbelianScheme 1 base}
    (q : D.Isogeny C)
    (ec : (cyclicGroup (S := base) m).X ≅ q.kernelScheme) [IsMonHom ec.hom] :
    ∃ family : Fin m → ∀ T : Over base,
        (T ⟶ OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel.Construction.kernelScheme q.hom) →*
          Γ(T.left, ⊤)ˣ,
      (∀ j {T U : Over base} (t : U ⟶ T)
          (x : T ⟶ OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel.Construction.kernelScheme q.hom),
        Units.map t.left.appTop.hom (family j T x) = family j U (t ≫ x)) ∧
      Function.Injective family := by
  let e : ConstantKernelCharacters.groupScheme base (Multiplicative (ZMod m)) ≅
      OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel.Construction.kernelScheme q.hom :=
    ec ≪≫ KernelComparison.isogenyKernelIso q
  let : IsMonHom e.hom := by
    change IsMonHom (ec.hom ≫ (KernelComparison.isogenyKernelIso q).hom)
    infer_instance
  let : IsMonHom e.inv := inferInstance
  exact exists_family m e

end
end SteinerGeometry.CyclicNaturalCharacters
