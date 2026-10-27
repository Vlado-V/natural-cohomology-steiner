import SteinerGeometry.CurveRankLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.MatrixRankScalarExtension

namespace SteinerGeometry

noncomputable section

open AlgebraicGeometry CategoryTheory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

variable {K : Type} [Field K] {Y : Scheme}

/-- The coefficients of a regular matrix evaluated at an actual field point. -/
def regularMatrixAtPoint {m k : ℕ} (A : Matrix (Fin m) (Fin k) Γ(Y, ⊤))
    (c : Spec (.of K) ⟶ Y) : Matrix (Fin m) (Fin k) K :=
  A.map ((Scheme.ΓSpecIso (.of K)).hom.hom.comp c.appTop.hom)

/-- Full column rank of the evaluated matrix is membership in the regular
maximal-minor open. Both the open and the evaluation come from the same matrix. -/
theorem regularMatrixAtPoint_fullRank_iff {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) Γ(Y, ⊤)) (c : Spec (.of K) ⟶ Y) :
    Set.range c ⊆ (Matrix.RankLowerOpen.matrixRankLowerOpen A k : Set Y) ↔
      k ≤ (regularMatrixAtPoint A c).rank := by
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  have hr := Field.MatrixRankScalarExtension.fieldMatrix_rank_map
    (Scheme.ΓSpecIso (.of K)).hom.hom (A.map c.appTop.hom)
  have he : ((A.map c.appTop.hom).map (Scheme.ΓSpecIso (.of K)).hom.hom) =
      regularMatrixAtPoint A c := rfl
  rw [he] at hr
  exact (Matrix.RankLowerOpen.matrixRankLowerOpen_field_point c A k).trans
    (by rw [hr])

/-- Full column rank is precisely linear independence of the section values
in a chosen vector-bundle frame. -/
theorem regularMatrixAtPoint_independent_iff {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) Γ(Y, ⊤)) (c : Spec (.of K) ⟶ Y) :
    LinearIndependent K (regularMatrixAtPoint A c).col ↔
      Set.range c ⊆ (Matrix.RankLowerOpen.matrixRankLowerOpen A k : Set Y) := by
  rw [linearIndependent_iff_card_le_finrank_span, Fintype.card_fin]
  change k ≤ Module.finrank K (Submodule.span K (Set.range (regularMatrixAtPoint A c).col)) ↔ _
  rw [← _root_.Matrix.rank_eq_finrank_span_cols]
  exact (regularMatrixAtPoint_fullRank_iff A c).symm

variable {X : Type} {F : X → Type}
variable [∀ x, AddCommGroup (F x)] [∀ x, Module K (F x)]
variable {V : Type} [AddCommGroup V] [Module K V]

/-- Regular coordinates for a fixed tuple of sections on one bundle chart.
The `point` map records the underlying closed point. `fiber_independent` is
the coordinate-frame comparison; it does not assert any genericity or rank. -/
structure LocalSectionMatrix (C : Scheme) (point : X → C)
    (e : ∀ x, V →ₗ[K] F x) {k : ℕ} (s : Fin k → V) where
  /-- A genuine algebraic open on which the vector bundle is framed. -/
  chart : C.Opens
  rows : ℕ
  /-- Coefficients are regular functions on the same chart. -/
  matrix : Matrix (Fin rows) (Fin k) Γ(chart.toScheme, ⊤)
  liftPoint : ∀ x : X, point x ∈ chart → (Spec (.of K) ⟶ chart.toScheme)
  liftPoint_underlying : ∀ (x : X) (hx : point x ∈ chart),
    chart.ι (liftPoint x hx (⊥ : PrimeSpectrum K)) = point x
  fiber_independent : ∀ (x : X) (hx : point x ∈ chart),
    LinearIndependent K (fun i => e x (s i)) ↔
      LinearIndependent K (regularMatrixAtPoint matrix (liftPoint x hx)).col

/-- Build the rank-test data from actual regular section coordinates and
fiber-frame linear equivalences. The only comparison input is the value of
each individual section; independence is proved from the frame equivalence. -/
def LocalSectionMatrix.of_frame_coordinates
    {C : Scheme} (point : X → C) (e : ∀ x, V →ₗ[K] F x)
    {k n : ℕ} (s : Fin k → V) (U : C.Opens)
    (coordinates : V → Fin n → Γ(U.toScheme, ⊤))
    (liftPoint : ∀ x : X, point x ∈ U → (Spec (.of K) ⟶ U.toScheme))
    (liftPoint_underlying : ∀ (x : X) (hx : point x ∈ U),
      U.ι (liftPoint x hx (⊥ : PrimeSpectrum K)) = point x)
    (frame : ∀ (x : X) (_ : point x ∈ U), F x ≃ₗ[K] (Fin n → K))
    (frame_value : ∀ (x : X) (hx : point x ∈ U) (v : V),
      frame x hx (e x v) = fun j =>
        ((Scheme.ΓSpecIso (.of K)).hom.hom.comp (liftPoint x hx).appTop.hom)
          (coordinates v j)) :
    LocalSectionMatrix C point e s where
  chart := U
  rows := n
  matrix := fun i j => coordinates (s j) i
  liftPoint := liftPoint
  liftPoint_underlying := liftPoint_underlying
  fiber_independent x hx := by
    have hv : (regularMatrixAtPoint (fun i j => coordinates (s j) i)
        (liftPoint x hx)).col = fun i => frame x hx (e x (s i)) := by
      funext i j
      exact (congrFun (frame_value x hx (s i)) j).symm
    rw [hv]
    exact ((frame x hx).toLinearMap.linearIndependent_iff_of_injOn
      (frame x hx).injective.injOn).symm

/-- Local regular section matrices supply the finite-rank-drop theorem on an
actual integral Noetherian curve. This proof constructs a nonempty minor open
inside one chart, and puts the entire bad locus inside its finite complement. -/
theorem hasFiniteRankDrop_of_local_section_matrices
    {C : Scheme} [IsIntegral C] [IsNoetherian C]
    (hd : topologicalKrullDim C ≤ 1)
    (point : X → C) (hpoint : Function.Injective point)
    (e : ∀ x, V →ₗ[K] F x)
    (hregular : ∀ (k : ℕ) (s : Fin k → V) (p : X),
      LinearIndependent K (fun i => e p (s i)) →
        ∃ D : LocalSectionMatrix C point e s, point p ∈ D.chart) :
    HasFiniteRankDrop e := by
  intro k s hnonempty
  obtain ⟨p, hp⟩ := hnonempty
  obtain ⟨D, hpD⟩ := hregular k s p hp
  let R := Matrix.RankLowerOpen.matrixRankLowerOpen D.matrix k
  let U := D.chart.ι ''ᵁ R
  have hpR : Set.range (D.liftPoint p hpD) ⊆ (R : Set D.chart.toScheme) :=
    (regularMatrixAtPoint_independent_iff D.matrix (D.liftPoint p hpD)).mp
      ((D.fiber_independent p hpD).mp hp)
  have hpU : point p ∈ U := by
    refine ⟨D.liftPoint p hpD (⊥ : PrimeSpectrum K), hpR ⟨_, rfl⟩, ?_⟩
    exact D.liftPoint_underlying p hpD
  have hgood (x : X) (hx : point x ∈ U) :
      LinearIndependent K (fun i => e x (s i)) := by
    obtain ⟨y, hy, hyeq⟩ := hx
    have hxD : point x ∈ D.chart := hyeq ▸ y.property
    have hc : Set.range (D.liftPoint x hxD) ⊆ (R : Set D.chart.toScheme) := by
      rintro z ⟨t, rfl⟩
      have heq : D.liftPoint x hxD t = y := by
        apply Subtype.ext
        change D.chart.ι (D.liftPoint x hxD t) = D.chart.ι y
        rw [Subsingleton.elim t (⊥ : PrimeSpectrum K), D.liftPoint_underlying]
        exact hyeq.symm
      exact heq ▸ hy
    exact (D.fiber_independent x hxD).mpr
      ((regularMatrixAtPoint_independent_iff D.matrix (D.liftPoint x hxD)).mpr hc)
  have hbad : ((U : Set C)ᶜ).Finite :=
    OAI.MaximalSeshadri.Geometry.proper_closed_finite_of_dimension_one hd U.isOpen.isClosed_compl
      (by intro h; exact (show point p ∈ (U : Set C)ᶜ from h ▸ Set.mem_univ _) hpU)
  exact (Set.Finite.preimage hpoint.injOn hbad).subset (fun x hx => fun hu => hx (hgood x hu))

end
end SteinerGeometry
