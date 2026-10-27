module

public import SteinerGeometry.SectionContractionCategory

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Evaluation of a tuple of regular coordinates commutes with any natural
semilinear section map. In particular, it applies to pullback of sections at
a field-valued point. -/
theorem biproductCoordinates_semilinear_natural
    (F : C ⥤ ModuleCat R) [F.Additive]
    (G : C ⥤ ModuleCat S) [G.Additive]
    (φ : R →+* S) (a : ∀ M, F.obj M →ₛₗ[φ] G.obj M)
    (ha : ∀ {M N} (f : M ⟶ N) (x : F.obj M),
      a N (F.map f x) = G.map f (a M x))
    (B : C) (ι : Type) [Fintype ι] (x : F.obj (⨁ fun _ : ι => B)) :
    biproductCoordinates G B ι (a _ x) =
      fun i => a B (biproductCoordinates F B ι x i) := by
  funext i
  exact (ha (biproduct.π (fun _ : ι => B) i) x).symm

/-- A local bundle frame commutes with semilinear evaluation, including each
coordinate of the frame. -/
theorem frameCoordinates_semilinear_natural
    (F : C ⥤ ModuleCat R) [F.Additive]
    (G : C ⥤ ModuleCat S) [G.Additive]
    (φ : R →+* S) (a : ∀ M, F.obj M →ₛₗ[φ] G.obj M)
    (ha : ∀ {M N} (f : M ⟶ N) (x : F.obj M),
      a N (F.map f x) = G.map f (a M x))
    (B M : C) (ι : Type) [Fintype ι]
    (frame : M ≅ ⨁ fun _ : ι => B) (x : F.obj M) :
    biproductCoordinates G B ι (G.map frame.hom (a M x)) =
      fun i => a B (biproductCoordinates F B ι (F.map frame.hom x) i) := by
  rw [← ha frame.hom x]
  exact biproductCoordinates_semilinear_natural F G φ a ha B ι _

end
end SteinerGeometry
