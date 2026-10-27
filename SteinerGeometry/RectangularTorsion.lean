module

public import SteinerGeometry.CharacterTorsion
public import SteinerGeometry.CyclicNaturalCharacters
public import SteinerGeometry.RectangularIsogeny
public import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions

set_option backward.privateInPublic true
@[expose] public section

/-! The actual cyclic covers of a fixed rectangular elliptic curve yield
arbitrarily many distinct torsion line bundles on that same curve. -/
noncomputable section
namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open CharacterTorsion TorsionLineClasses

namespace RectangularModel
variable {k : ℕ} [NeZero k] (B : RectangularModel k)

/-- The source may vary, but all these distinct actual torsion classes live on
one fixed target curve. -/
theorem exists_injective_torsion_family (m : ℕ) :
    ∃ family : Fin m → TorsionClass B.elliptic.scheme.left, Function.Injective family := by
  classical
  by_cases hm : m = 0
  · subst m
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  let _ : NeZero m := ⟨hm⟩
  obtain ⟨A, q, _, _, ec, hec, _⟩ := B.exists_cyclicIsogenyInto m
  let _ : IsMonHom ec.hom := hec
  obtain ⟨family, hnatural, hinj⟩ := CyclicNaturalCharacters.exists_isogenyKernelFamily m q ec
  let chars : Fin m → NaturalKernelCharacter q.hom :=
    fun j => ⟨family j, hnatural j⟩
  have hchars : Function.Injective chars := by
    intro i j h
    exact hinj (congrArg NaturalKernelCharacter.value h)
  have : IsIso A.elliptic.scheme.hom.appTop :=
    OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso
      A.elliptic.scheme
  have hp : Function.Surjective A.elliptic.scheme.hom.appTop :=
    (ConcreteCategory.bijective_of_isIso A.elliptic.scheme.hom.appTop).surjective
  let e := characterFamilyEmbedding q.hom hp chars hchars
  exact ⟨e, e.injective⟩

/-- Infinitely many actual finite-order line classes on every fixed rectangular
complex elliptic curve, proved from its cyclic covers. -/
instance rectangularTorsion_infinite : Infinite (TorsionClass B.elliptic.scheme.left) :=
  infinite_of_large_finite_families (B.exists_injective_torsion_family)

end RectangularModel
end SteinerGeometry
