module

public import SteinerGeometry.PullbackContraction
public import SteinerGeometry.KernelPullbackLineSum
public import SteinerGeometry.LineEpimorphismCover

set_option backward.privateInPublic true
@[expose] public section

/-! Unconditional geometric base change of the symmetric contraction kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
variable {X Y : Scheme.{0}} (f : Y ⟶ X)
variable {K : Type} [Field K] [CharZero K]
local instance symmetricKernelBaseChangeBiproducts (Z : Scheme.{0}) :
    HasFiniteBiproducts Z.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The canonical comparison is invertible for every scheme base change:
the contraction is an epimorphism onto a finite sum of a line bundle. -/
theorem curveSectionContraction_kernelComparison_isIso (p : X ⟶ Spec (.of K))
    (N B : Line.Bundles.LineBundle X) {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf))
    (he : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (e j)) :
    IsIso (kernelComparison (curveSectionContraction N B e d) (Scheme.Modules.pullback f)) := by
  let _ : (⨁ fun _ : Sym (Fin (n+1)) (d+1) => B.sheaf).IsQuasicoherent :=
    KernelPullbackLineSum.lineSum_isQuasicoherent B _
  let _ : Epi (curveSectionContraction N B e d) := curveSectionContraction_epi p N B e he d
  exact KernelPullbackLineSum.kernelComparison_isIso_of_epi_lineSum f (N.tensor B)
    (Sym (Fin (n+1)) d) (curveSectionContraction N B e d)

/-- The actual pulled-back kernel is the kernel of the pulled-back section
contraction, without an assumed exactness or flatness hypothesis. -/
def curveKernelBaseChangeIso (p : X ⟶ Spec (.of K))
    (N B : Line.Bundles.LineBundle X) {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf))
    (he : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (e j)) :
    (Scheme.Modules.pullback f).obj (kernel (curveSectionContraction N B e d)) ≅
      kernel (curveSectionContraction (N.pullback f) (B.pullback f)
        (fun i => Ample.LineBundles.pullbackSection f (e i)) d) := by
  haveI := curveSectionContraction_kernelComparison_isIso (d := d) f p N B e he
  letI : PreservesLimit (parallelPair (curveSectionContraction N B e d) 0)
      (Scheme.Modules.pullback f) :=
    PreservesKernel.of_iso_comparison (Scheme.Modules.pullback f) (curveSectionContraction N B e d)
  exact pullbackCurveKernelIso f N B e

/-- The base-change isomorphism takes the kernel inclusion to the genuine
pullback of the original inclusion, in the canonical finite-sum coordinates. -/
@[simp, reassoc] theorem curveKernelBaseChangeIso_hom_ι (p : X ⟶ Spec (.of K))
    (N B : Line.Bundles.LineBundle X) {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf))
    (he : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (e j)) :
    (curveKernelBaseChangeIso (d := d) f p N B e he).hom ≫
      kernel.ι (curveSectionContraction (N.pullback f) (B.pullback f)
        (fun i => Ample.LineBundles.pullbackSection f (e i)) d) =
      (Scheme.Modules.pullback f).map (kernel.ι (curveSectionContraction N B e d)) ≫
        (pullbackLineSumIso f B).hom := by
  simp [curveKernelBaseChangeIso, pullbackCurveKernelIso, PreservesKernel.iso_hom]

/-- Splitting the first kernel on the covering curve splits the genuine
pullback of the original symmetric contraction kernel into line monomials. -/
def curveKernelBaseChangeSplitIso (p : X ⟶ Spec (.of K))
    (N B : Line.Bundles.LineBundle X) {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N.sheaf))
    (he : ∀ x : X, ∃ j, x ∈ Ample.LineBundles.sectionNonvanishing (e j))
    (L : Fin n → Line.Bundles.LineBundle Y)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation
      (fun i => Ample.LineBundles.pullbackSection f (e i)))) :
    (⨁ fun a : Sym (Fin n) (d+1) => ((monomialLineBundle L a).tensor (B.pullback f)).sheaf) ≅
      (Scheme.Modules.pullback f).obj (kernel (curveSectionContraction N B e d)) :=
  twistedSymmetricKernelIso (f ≫ p) (N.pullback f) (B.pullback f)
      (fun i => Ample.LineBundles.pullbackSection f (e i)) (sectionCover_pullback f e he) L E ≪≫
    (curveKernelBaseChangeIso f p N B e he).symm

/-- The base-change splitting from the actual epimorphism of free sheaves.
Its nonvanishing cover is derived, not supplied as an extra hypothesis. -/
def curveKernelBaseChangeSplitIso_of_epi (p : X ⟶ Spec (.of K))
    (N B : Line.Bundles.LineBundle X) {n d : ℕ}
    (ev : (⨁ fun _ : Fin (n+1) => Line.Bundles.structureModule X) ⟶ N.sheaf) [Epi ev]
    (L : Fin n → Line.Bundles.LineBundle Y)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation
      (fun i : Fin (n+1) => Ample.LineBundles.pullbackSection f
        (biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i ≫ ev)))) :
    (⨁ fun a : Sym (Fin n) (d+1) => ((monomialLineBundle L a).tensor (B.pullback f)).sheaf) ≅
      (Scheme.Modules.pullback f).obj (kernel (curveSectionContraction N B
        (fun i => biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i ≫ ev) d)) :=
  curveKernelBaseChangeSplitIso f p N B _ (LineEpimorphismCover.components_cover N ev) L E

end SteinerGeometry
