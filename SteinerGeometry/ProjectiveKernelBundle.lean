import SteinerGeometry.KernelAffineLocalFreeness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers
import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech

/-! Kernels of epimorphisms between sums of genuine projective line bundles. -/
noncomputable section
namespace SteinerGeometry.ProjectiveKernelBundle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev space (R : Type u) [CommRing R] (n : ℕ) :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R)

abbrev lineSum (R : Type u) [CommRing R] (n r : ℕ) (j : Fin (n+1)) (d : Fin r → ℤ) :
    (space R n).Modules :=
  ∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (d k)

/-- Additive functors preserve a finite sum, using its finite biproduct structure. -/
def finiteSumMapIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] (r : ℕ) (M : Fin r → C) :
    F.obj (∐ M) ≅ ∐ (F.obj ∘ M) := by
  letI : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  exact F.mapIso (biproduct.isoCoproduct M).symm ≪≫ F.mapBiproduct M ≪≫
    biproduct.isoCoproduct (F.obj ∘ M)

/-- Every standard affine chart trivializes every finite sum of the twists. -/
def lineSumRestrictionFrame (n r : ℕ) (i j : Fin (n+1)) (d : Fin r → ℤ) :
    (Scheme.Modules.restrictFunctor
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι).obj (lineSum R n r j d) ≅
      SheafOfModules.free (R := (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme.ringCatSheaf)
        (ULift.{u} (Fin r)) := by
  let F := Scheme.Modules.restrictFunctor
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι
  let : F.Additive := { map_add := by intros; rfl }
  letI : HasFiniteBiproducts (space R n).Modules := HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasFiniteBiproducts (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme.Modules :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact finiteSumMapIso F r _ ≪≫ Sigma.mapIso (fun k =>
    TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) i j (d k)) ≪≫
      (Sigma.reindex Equiv.ulift (fun _ : Fin r =>
        SheafOfModules.unit (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme.ringCatSheaf)).symm

/-- A surjection between sums of line bundles on projective space has a
locally free kernel; this is a statement about the actual sheaf kernel. -/
theorem kernel_isLocallyFree (n r t : ℕ) (j : Fin (n+1))
    (d : Fin r → ℤ) (e : Fin t → ℤ)
    (f : lineSum R n r j d ⟶ lineSum R n t j e) [Epi f] :
    (kernel f).IsLocallyFree := by
  have hd (k : Fin r) := InvertibleFinitePresentation.invertible_quasicoherent
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) j (d k))
  have he (k : Fin t) := InvertibleFinitePresentation.invertible_quasicoherent
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) j (e k))
  have : (lineSum R n r j d).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _ hd
  have : (lineSum R n t j e).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _ he
  apply KernelAffineLocalFreeness.locallyFree_kernel_of_affine_free_cover f
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+1)))
    (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R))
    (fun a => StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) a)
    (ULift.{u} (Fin r)) (ULift.{u} (Fin t))
  · intro a
    exact lineSumRestrictionFrame n r a.down j d
  · intro a
    exact lineSumRestrictionFrame n t a.down j e

end SteinerGeometry.ProjectiveKernelBundle
