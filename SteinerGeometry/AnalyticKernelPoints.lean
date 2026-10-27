module

public import SteinerGeometry.CyclicFromPoints

set_option backward.privateInPublic true
@[expose] public section

/-! Transfer of an actual analytic group kernel to geometric points of an
algebraic isogeny. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

theorem kernelPointsEquiv
    {S : Scheme} {D C : Abelian.Schemes.AbelianScheme 1 S}
    (q : D.Isogeny C) {T U : Type} [AddCommGroup T] [AddCommGroup U]
    (f : T →+ U)
    (eD : Multiplicative T ≃* (𝟙_ (Over S) ⟶ D.scheme))
    (eC : Multiplicative U ≃* (𝟙_ (Over S) ⟶ C.scheme))
    (hf : ∀ x : T, eD (Multiplicative.ofAdd x) ≫ q.hom =
      eC (Multiplicative.ofAdd (f x))) :
    Nonempty (Multiplicative f.ker ≃* q.kernelAt (𝟙_ (Over S))) := by
  let kmap : Multiplicative f.ker → q.kernelAt (𝟙_ (Over S)) := fun x =>
    ⟨eD (Multiplicative.ofAdd x.toAdd.val), by
      change eD (Multiplicative.ofAdd x.toAdd.val) ≫ q.hom = 1
      rw [hf, x.toAdd.property]
      exact eC.map_one⟩
  have hinj : Function.Injective kmap := by
    intro x y h
    have hval := congrArg Subtype.val h
    have hxy := eD.injective hval
    exact congrArg Multiplicative.ofAdd (Subtype.ext hxy)
  have hsurj : Function.Surjective kmap := by
    intro a
    let x : T := (eD.symm a.val).toAdd
    have hx : f x = 0 := by
      have hh : eC (Multiplicative.ofAdd (f x)) = 1 := by
        rw [← hf]
        change eD (eD.symm a.val) ≫ q.hom = 1
        rw [eD.apply_symm_apply]
        exact a.property
      have hh' : eC (Multiplicative.ofAdd (f x)) = eC 1 :=
        hh.trans eC.map_one.symm
      exact eC.injective hh'
    refine ⟨Multiplicative.ofAdd ⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact eD.apply_symm_apply a.val
  let h : Multiplicative f.ker →* q.kernelAt (𝟙_ (Over S)) :=
    { toFun := kmap
      map_one' := by
        apply Subtype.ext
        exact eD.map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact eD.map_mul _ _ }
  exact ⟨MulEquiv.ofBijective h ⟨hinj, hsurj⟩⟩

end SteinerGeometry
