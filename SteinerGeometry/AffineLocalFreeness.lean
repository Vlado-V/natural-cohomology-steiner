import SteinerGeometry.SheafLocalFreeTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionCounit

/-! # Locally free sheaves from finite projective affine sections -/

noncomputable section
namespace SteinerGeometry.TildeFiniteProjective

open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

/-- The actual affine global-sections adjunction transports local freeness
from a finite projective module to its quasicoherent sheaf. -/
theorem locallyFree_of_affine_sections_projective (X : Scheme.{u}) [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent]
    [Module.Finite Γ(X, ⊤) Γ(M, ⊤)] [Module.Projective Γ(X, ⊤) Γ(M, ⊤)] :
    M.IsLocallyFree := by
  let A := (Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj M
  have : Module.Finite Γ(X, ⊤) A := inferInstanceAs (Module.Finite Γ(X, ⊤) Γ(M, ⊤))
  have : Module.Projective Γ(X, ⊤) A := inferInstanceAs (Module.Projective Γ(X, ⊤) Γ(M, ⊤))
  have hA := tilde_locallyFree_of_finite_projective A
  have hL := locallyFree_pullback X.toSpecΓ (tilde A) hA
  exact locallyFree_of_iso (Affine.SectionCounit.AffineSectionAdjunction.counitIso X M) hL

end SteinerGeometry.TildeFiniteProjective
