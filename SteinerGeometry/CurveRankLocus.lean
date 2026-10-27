import SteinerGeometry.CurveGeneratorFrames
import OAI.AlgebraicGeometry.Seshadri.Geometry.CurveFinite

namespace SteinerGeometry

noncomputable section

open AlgebraicGeometry TopologicalSpace

variable {K : Type*} [Field K] [Infinite K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {X : Type*} {F : X → Type*}
variable [∀ x, AddCommGroup (F x)] [∀ x, Module K (F x)]
variable [∀ x, FiniteDimensional K (F x)]

omit [Infinite K] [∀ x, FiniteDimensional K (F x)] in
/-- Actual scheme rank opens on an integral Noetherian curve imply the finite
rank-drop condition. The points may be an injectively indexed family of closed
points, so the fiber vector spaces all have the original ground field. -/
theorem hasFiniteRankDrop_of_scheme_opens
    {C : Scheme} [IsIntegral C] [IsNoetherian C]
    (hd : topologicalKrullDim C ≤ 1)
    (point : X → C) (hpoint : Function.Injective point)
    (e : ∀ x, V →ₗ[K] F x)
    (rankOpen : ∀ (k : ℕ), (Fin k → V) → C.Opens)
    (rankOpen_spec : ∀ (k : ℕ) (s : Fin k → V) (x : X),
      point x ∈ rankOpen k s ↔ LinearIndependent K (fun i => e x (s i))) :
    HasFiniteRankDrop e := by
  intro k s hnonempty
  obtain ⟨p, hp⟩ := hnonempty
  have hbad : ((rankOpen k s : Set C)ᶜ).Finite :=
    OAI.MaximalSeshadri.Geometry.proper_closed_finite_of_dimension_one hd
      (rankOpen k s).isOpen.isClosed_compl (by
        intro he
        have hmem : point p ∈ (rankOpen k s : Set C)ᶜ := he ▸ Set.mem_univ (point p)
        exact hmem ((rankOpen_spec k s p).mpr hp))
  have hpre : (point ⁻¹' (rankOpen k s : Set C)ᶜ).Finite :=
    Set.Finite.preimage hpoint.injOn hbad
  apply hpre.subset
  intro x hx
  exact fun h => hx ((rankOpen_spec k s x).mp h)

/-- A scheme-coordinate version of the rank-plus-one theorem. Its geometric
input consists of genuine open subsets of the curve expressing full column
rank of the evaluation matrices. -/
theorem exists_rank_add_one_generators_of_scheme_opens
    {C : Scheme} [IsIntegral C] [IsNoetherian C]
    (hd : topologicalKrullDim C ≤ 1)
    (point : X → C) (hpoint : Function.Injective point)
    (e : ∀ x, V →ₗ[K] F x) (he : ∀ x, Function.Surjective (e x))
    (n : ℕ) (hdim : ∀ x, Module.finrank K (F x) = n + 1)
    (rankOpen : ∀ (k : ℕ), (Fin k → V) → C.Opens)
    (rankOpen_spec : ∀ (k : ℕ) (s : Fin k → V) (x : X),
      point x ∈ rankOpen k s ↔ LinearIndependent K (fun i => e x (s i)))
    (p : X) :
    ∃ s : Fin (n + 2) → V,
      ∀ x, Submodule.span K (Set.range (fun i => e x (s i))) = ⊤ :=
  exists_rank_add_one_generators e he n hdim
    (hasFiniteRankDrop_of_scheme_opens hd point hpoint e rankOpen rankOpen_spec) p

end
end SteinerGeometry
