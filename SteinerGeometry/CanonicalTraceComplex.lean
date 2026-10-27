import SteinerGeometry.CanonicalTrace
import SteinerGeometry.NativeCohomology

noncomputable section
namespace SteinerGeometry.CanonicalTrace
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-- A positive integer is an invertible global function on any complex scheme. -/
def complexDegreeUnit {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) (n : ℕ) (hn : 0 < n) :
    Γ(X, ⊤)ˣ :=
  Units.map (Coefficient.ModulePresheaf.schemeCoefficientMap p).toMonoidHom
    (Units.mk0 (n : ℂ) (by exact_mod_cast Nat.ne_of_gt hn))

@[simp] theorem complexDegreeUnit_val {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))
    (n : ℕ) (hn : 0 < n) : (complexDegreeUnit p n hn : Γ(X, ⊤)) = n := by
  simp [complexDegreeUnit]

/-- Positive constant-degree finite flat maps over ℂ have a split pullback unit
for every quasicoherent module. The degree unit is constructed from the base field. -/
theorem finiteFlat_pullbackUnit_splitMono_complex
    {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] {n : ℕ}
    (hn : ∀ x, f.finrank x = n) (p : X ⟶ Spec (.of ℂ)) (hnpos : 0 < n)
    (M : X.Modules) [M.IsQuasicoherent] :
    IsSplitMono ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) :=
  finiteFlat_pullbackUnit_splitMono f hn (complexDegreeUnit p n hnpos)
    (complexDegreeUnit_val p n hnpos) M

end SteinerGeometry.CanonicalTrace
