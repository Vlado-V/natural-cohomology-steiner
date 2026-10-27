module

public import SteinerGeometry.RectangularModel
public import SteinerGeometry.RectangularDoublingKernel
public import SteinerGeometry.AnalyticKernelPoints
public import SteinerGeometry.GeometricKernelLabels
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismScalars

set_option backward.privateInPublic true
@[expose] public section

/-! The actual degree-four self-cover of an algebraic rectangular torus,
with its four kernel labels retained. -/
noncomputable section
namespace SteinerGeometry.RectangularModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

variable {k : ℕ} [NeZero k] (B : RectangularModel k)

theorem doubling_etale : Etale (((𝟙 B.elliptic.scheme) ^ 2).left) :=
  OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale.TorsionEtale.power_etale
    B.elliptic.scheme 2
    (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt.TorsionEtale.integer_unit_at_stalk
      (𝟙 complexBase) 2)

/-- Multiplication by two on the same algebraic curve is finite, flat and surjective. -/
def doubling : B.elliptic.Isogeny B.elliptic := by
  let f : B.elliptic.scheme ⟶ B.elliptic.scheme := (𝟙 B.elliptic.scheme) ^ 2
  letI : Etale f.left := B.doubling_etale
  letI : IsProper f.left :=
    OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.power_isProper
      B.elliptic.scheme 2
  letI : IsFinite f.left :=
    OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified f.left
  letI : ConnectedSpace B.elliptic.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton B.elliptic.scheme.hom
  have hs : Surjective f.left := by
    have hc : IsClopen (Set.range f.left) :=
      ⟨f.left.isClosedMap.isClosed_range, f.left.isOpenMap.isOpen_range⟩
    exact ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty f.left))⟩
  exact
    { hom := f
      preservesGroup := by
        change IsMonHom (B.elliptic.multiplication 2)
        rw [← B.elliptic.endRing_natCast_hom 2]
        infer_instance
      finite := inferInstance
      flat := (Etale.iff_flat_and_formallyUnramified.mp B.doubling_etale).1
      surjective := hs }

instance doubling_map_etale : Etale B.doubling.hom.left := B.doubling_etale

theorem pointEquiv_doubling (x : RectangularTorus k) :
    B.pointEquiv (Multiplicative.ofAdd x) ≫ B.doubling.hom =
      B.pointEquiv (Multiplicative.ofAdd (rectangularDoubling k x)) := by
  change B.pointEquiv (Multiplicative.ofAdd x) ≫ (𝟙 B.elliptic.scheme) ^ 2 = _
  rw [MonObj.comp_pow, Category.comp_id]
  exact (map_pow B.pointEquiv (Multiplicative.ofAdd x) 2).symm

theorem doubling_kernel_points :
    Nonempty (Multiplicative (ZMod 2 × ZMod 2) ≃*
      B.doubling.kernelAt (𝟙_ (Over complexBase))) := by
  obtain ⟨e⟩ := kernelPointsEquiv B.doubling (rectangularDoubling k)
    B.pointEquiv B.pointEquiv B.pointEquiv_doubling
  exact ⟨(AddEquiv.toMultiplicative (rectangularDoublingKernelEquiv k)).trans e⟩

theorem doubling_kernel_iso :
    ∃ e : (OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme
        complexBase (Multiplicative (ZMod 2 × ZMod 2))).X ≅ B.doubling.kernelScheme,
      IsMonHom e.hom ∧ IsMonHom (e.hom ≫ B.doubling.kernelInclusion) := by
  obtain ⟨e⟩ := B.doubling_kernel_points
  exact geometricKernelIso_of_points B.doubling e

end SteinerGeometry.RectangularModel
