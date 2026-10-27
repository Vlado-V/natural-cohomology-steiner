module

public import SteinerGeometry.TransposeDuality

set_option backward.privateInPublic true
@[expose] public section

/-! Transpose duality with an arbitrary target isomorphic to the structure module. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.TransposeTargetIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective

universe u
variable {X : Scheme.{u}}
local instance : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The epimorphic dual-transpose theorem is invariant under an isomorphism
from the target line to the structure module. -/
theorem epi_dualMap_transpose {a b : ℕ} (L O : X.Modules)
    (hL : Invertible.Scheme.Modules.IsInvertible L)
    (eO : O ≅ Invertible.Scheme.Modules.unitObj X)
    (g : Fin a → Fin b → (L ⟶ O))
    (hf : Epi (finiteCoproductFromMatrix (fun _ : Fin b => L)
      (fun _ : Fin a => O) g)) :
    Epi (SheafDual.dualMap (finiteCoproductFromMatrix (fun _ : Fin a => L)
      (fun _ : Fin b => O) (fun j i => g i j))) := by
  let := hf
  have hnormalized : Epi (finiteCoproductFromMatrix (fun _ : Fin b => L)
      (fun _ : Fin a => Invertible.Scheme.Modules.unitObj X)
      (fun i j => g i j ≫ eO.hom)) := by
    have h := TransposeDuality.epi_matrix_transport (𝟭 X.Modules)
      (fun _ : Fin b => L) (fun _ : Fin a => O) g
      (fun _ : Fin b => L) (fun _ : Fin a => Invertible.Scheme.Modules.unitObj X)
      (fun _ => Iso.refl L) (fun _ => eO)
    simpa using h
  have hn := TransposeDuality.epi_dualMap_transpose L hL
    (fun i j => g i j ≫ eO.hom) hnormalized
  rw [← finiteCoproductFromMatrix_postcompose (fun _ : Fin a => L) (fun _ : Fin b => O)
    (fun _ : Fin b => Invertible.Scheme.Modules.unitObj X) (fun j i => g i j)
    (fun _ => eO), SheafDual.dualMap_comp] at hn
  exact @epi_of_epi _ _ _ _ _
    (SheafDual.dualMap (Sigma.mapIso (fun _ : Fin b => eO)).hom)
    (SheafDual.dualMap (finiteCoproductFromMatrix (fun _ : Fin a => L)
      (fun _ : Fin b => O) (fun j i => g i j))) hn

end SteinerGeometry.TransposeTargetIso
