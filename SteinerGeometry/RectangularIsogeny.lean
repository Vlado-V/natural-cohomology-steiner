import SteinerGeometry.RectangularModel
import SteinerGeometry.AnalyticKernelPoints
import SteinerGeometry.GeometricKernelLabels

namespace SteinerGeometry

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.RepresentationTheory.Theta.Geometric

namespace RectangularModel

variable {k : ℕ} [NeZero k] (B : RectangularModel k)

/-- Algebraize the identity map between actual rectangular period tori. -/
theorem exists_rectangularIsogeny (m : ℕ) [NeZero m] :
    ∃ (A : RectangularModel (k * m)) (q : A.elliptic.Isogeny B.elliptic),
      Etale q.hom.left ∧
      ∀ t, A.pointEquiv (Multiplicative.ofAdd t) ≫ q.hom =
        B.pointEquiv (Multiplicative.ofAdd (rectangularRelativeProjection k m t)) := by
  obtain ⟨A⟩ := exists_rectangularModel (k * m)
  obtain ⟨F, hFg, hfin, het, hsurj, hF⟩ :=
    Torus.Isogeny.exists_algebraic_torus_isogeny
      (rectangularPeriodData (k * m)) (rectangularPeriodData k)
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (m • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
      (rectangularLattice_mul_le k m)
      (nsmul_rectangular_mem_mul k m)
      m (Nat.pos_of_ne_zero (NeZero.ne m)) (by intro; rfl) (by intro; rfl)
      A.variety B.variety A.comparison B.comparison A.comparison_add B.comparison_add
  let : Etale F.left := het
  let q : A.elliptic.Isogeny B.elliptic :=
    { hom := F
      preservesGroup := hFg
      finite := hfin
      flat := (Etale.iff_flat_and_formallyUnramified.mp het).1
      surjective := hsurj }
  refine ⟨A, q, het, ?_⟩
  intro t
  exact hF t

/-- Every fixed rectangular model admits genuine cyclic étale covers of all positive degrees. -/
theorem exists_cyclicIsogenyInto (m : ℕ) [NeZero m] :
    ∃ (A : RectangularModel (k * m)) (q : A.elliptic.Isogeny B.elliptic),
      Etale q.hom.left ∧
      (∀ c, q.hom.left.finrank c = m) ∧
      ∃ e : (cyclicGroup (S := complexBase) m).X ≅ q.kernelScheme,
        IsMonHom e.hom ∧ IsMonHom (e.hom ≫ q.kernelInclusion) := by
  obtain ⟨A, q, het, hq⟩ := B.exists_rectangularIsogeny m
  let : Etale q.hom.left := het
  obtain ⟨ek⟩ := kernelPointsEquiv q (rectangularRelativeProjection k m)
    A.pointEquiv B.pointEquiv hq
  let points : Multiplicative (ZMod m) ≃* q.kernelAt (𝟙_ (Over complexBase)) :=
    (AddEquiv.toMultiplicative (rectangularRelativeKernelEquiv k m)).trans ek
  obtain ⟨e, he, hec⟩ := geometricKernelIso_of_points q points
  let : ConnectedSpace B.elliptic.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton B.elliptic.scheme.hom
  refine ⟨A, q, het, ?_, e, he, hec⟩
  exact fun c => isogeny_degree_of_cyclicKernel q e (Classical.choice inferInstance) c

/-- The same cover packaged with its cyclic kernel and degree for subsequent sheaf arguments. -/
theorem exists_cyclicEtaleCover (m : ℕ) [NeZero m] :
    ∃ (A : RectangularModel (k * m)) (q : CyclicEtaleIsogeny A.elliptic m),
      q.target = B.elliptic := by
  obtain ⟨A, q, het, hdeg, e, _, he⟩ := B.exists_cyclicIsogenyInto m
  exact ⟨A, ⟨B.elliptic, q, het, hdeg, e, he⟩, rfl⟩

end RectangularModel

end
end SteinerGeometry
