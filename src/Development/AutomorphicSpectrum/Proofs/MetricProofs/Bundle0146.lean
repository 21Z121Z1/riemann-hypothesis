import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Formalism.NormUnitaryBounds.NormUnitary
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0143
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0136
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0117
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0144
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0132
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0115
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIndependentLeOfDualMin
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem exists_independent_le_of_dual_min :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (μ : ℝ), 0 < μ →
      (∀ y : V, y ≠ 0 → (∀ x ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) → μ ≤ ‖y‖) →
      ∃ b : Fin (Module.finrank ℝ V) → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
        ∀ i, ‖b i‖ ≤ (Module.finrank ℝ V : ℝ) ^ (3 / 2 : ℝ) / μ := by
  intro V _ _ _ L _ _ μ hμ hdual
  set n := Module.finrank ℝ V with hn
  set c : ℝ := (n : ℝ) / μ with hc
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hμ.le
  have hspan : Submodule.span ℝ (L : Set V) = ⊤ := IsZLattice.span_top
  have main : ∀ k, k ≤ n → ∃ b : Fin k → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
      (∀ i, ‖b i‖ ^ 2 ≤ n * c ^ 2) ∧
      (∀ w ∈ Submodule.span ℝ (Set.range b), ∃ z ∈ Submodule.span ℤ (Set.range b),
        ‖w - z‖ ^ 2 ≤ k * c ^ 2 / 4) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, ?_⟩
      intro w hw
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hw0 : w = 0 := by
        rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hw
        exact hw
      simp [hw0]
    | succ k ih =>
      intro hk
      obtain ⟨b, hbL, hbli, hbn, hcov⟩ := ih (by omega)
      set W := Submodule.span ℝ (Set.range b) with hW
      set N := Submodule.span ℤ (Set.range b) with hN
      have hNL : N ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
      have hNW : Submodule.span ℝ (N : Set V) = W := Submodule.span_span_of_tower ℤ ℝ (Set.range b)
      have hWtop : W ≠ ⊤ := by
        intro h
        have h1 : Module.finrank ℝ W = k := by rw [hW, finrank_span_eq_card hbli, Fintype.card_fin]
        rw [h, finrank_top] at h1
        omega
      have hNsubW : ∀ y ∈ N, y ∈ W := fun y hy => by rw [← hNW]; exact Submodule.subset_span hy
      obtain ⟨m, hmL, hp0, hpn⟩ := Formalism.NormUnitaryCountingLemmas.exists_starProjection_ne_zero_norm_le_of_dualMinimum L hspan hμ hdual W N hNL hNW hWtop
      set p := Wᗮ.starProjection m with hp
      have hpW : p ∈ Wᗮ := Wᗮ.starProjection_apply_mem m
      have hwW : m - p ∈ W := by
        have := Wᗮ.sub_starProjection_mem_orthogonal m
        rwa [Submodule.orthogonal_orthogonal] at this
      obtain ⟨z, hzN, hz⟩ := hcov (m - p) hwW
      have hzW : z ∈ W := hNsubW z hzN
      set v := m - z with hv
      have hvdec : v = (m - p - z) + p := by rw [hv]; abel
      have hvL : v ∈ L := L.sub_mem hmL (hNL hzN)
      have hp2 : ‖p‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpn 2
      have pyth : ∀ a ∈ W, ∀ q ∈ Wᗮ, ‖a + q‖ ^ 2 = ‖a‖ ^ 2 + ‖q‖ ^ 2 := by
        intro a ha q hq
        have h0 : ⟪a, q⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal ha hq
        rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_real h0]
      have hvW : v ∉ W := by
        intro h
        apply hp0
        have hmW : m ∈ W := by
          have e : m = v + z := by rw [hv]; abel
          rw [e]
          exact W.add_mem h hzW
        have hm' : m ∈ Wᗮᗮ := by rwa [Submodule.orthogonal_orthogonal]
        exact Wᗮ.starProjection_apply_eq_zero_iff.mpr hm'
      have hsub : m - p - z ∈ W := W.sub_mem hwW hzW
      refine ⟨Fin.cons v b, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hvL
        · simpa using hbL j
      · exact linearIndependent_finCons.mpr ⟨hbli, hvW⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          rw [hvdec, pyth _ hsub _ hpW]
          have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
          nlinarith [sq_nonneg c, mul_le_mul_of_nonneg_right hkn (sq_nonneg c)]
        · simpa using hbn j
      · intro w' hw'
        rw [Fin.range_cons, Submodule.mem_span_insert] at hw'
        obtain ⟨t, u, hu, rfl⟩ := hw'
        set s := t - round t with hs
        have hs2 : s ^ 2 ≤ 1 / 4 := by
          have h := abs_sub_round t
          rw [← hs] at h
          nlinarith [abs_nonneg s, sq_abs s]
        have hq : s • (m - p - z) + u ∈ W := W.add_mem (W.smul_mem _ hsub) hu
        obtain ⟨z', hz'N, hz'⟩ := hcov (s • (m - p - z) + u) hq
        refine ⟨(round t : ℤ) • v + z', ?_, ?_⟩
        · rw [Fin.range_cons, Submodule.mem_span_insert]
          exact ⟨round t, z', hz'N, rfl⟩
        · have e : t • v + u - ((round t : ℤ) • v + z') = (s • (m - p - z) + u - z') + s • p := by
            rw [← Int.cast_smul_eq_zsmul ℝ, hs, hvdec]
            module
          rw [e, pyth _ (W.sub_mem hq (hNsubW z' hz'N)) _ (Wᗮ.smul_mem _ hpW), norm_smul,
            mul_pow, Real.norm_eq_abs, sq_abs]
          have h4 := mul_le_mul hs2 hp2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
          push_cast
          nlinarith [h4, hz']
  obtain ⟨b, hbL, hbli, hbn, -⟩ := main n le_rfl
  refine ⟨b, hbL, hbli, fun i => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast i.pos
  have key : (n : ℝ) ^ (3 / 2 : ℝ) / μ = Real.sqrt (n * c ^ 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc0, hc, Real.sqrt_eq_rpow, ← mul_div_assoc,
      ← Real.rpow_add_one hnR.ne']
    norm_num
  rw [key]
  calc ‖b i‖ = Real.sqrt (‖b i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (hbn i)

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRiemannLatticeOfPeriod
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ}

def diagAct (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
  (Algebra.lmul ℂ (Fin g → ℂ)).toRingHom.comp (Pi.ringHom fun i => (ty i).comp (algebraMap (𝓞 E) E))

theorem diagAct_apply (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (i : Fin g) :
    diagAct ty a x i = ty i (a : E) * x i := rfl

theorem embedding_eq_of_integers {s t : E →+* ℂ} (h : ∀ a : 𝓞 E, s (a : E) = t (a : E)) : s = t :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem mem_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) (x : Fin g → ℂ) :
    x ∈ eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ↔ ∀ i, ty i ≠ s → x i = 0 := by
  have key : ∀ (a : 𝓞 E) (i : Fin g),
      ((diagAct ty a - (s.comp (algebraMap (𝓞 E) E)) a • LinearMap.id : Module.End ℂ (Fin g → ℂ)) x) i = (ty i (a : E) - s (a : E)) * x i := by
    intro a i
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      diagAct_apply, RingHom.comp_apply]
    ring_nf
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i hi
    by_contra hx
    refine hi (embedding_eq_of_integers fun a => ?_)
    have h1 := congrFun (h a) i
    rw [key] at h1
    simpa [hx, sub_eq_zero] using h1
  · intro h a
    funext i
    rw [key]
    by_cases hi : ty i = s
    · simp [hi]
    · simp [h i hi]

def eigSpDiagEquiv (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ≃ₗ[ℂ] ({i // ty i = s} → ℂ) where
  toFun x j := x.1 j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun i => open Classical in if h : ty i = s then f ⟨i, h⟩ else 0,
    (mem_eigSp_diagAct ty s _).2 fun i hi => by simp [hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases h : ty i = s
    · simp [h]
    · simp [h, (mem_eigSp_diagAct ty s x.1).1 x.2 i h]
  right_inv f := by
    funext j
    simp [j.2]

theorem finrank_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = Nat.card {i // ty i = s} := by
  classical
  rw [(eigSpDiagEquiv ty s).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Diag

theorem free_of_period {Λ : Type} [AddCommGroup Λ] {g : ℕ} (P : Λ →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧ Module.finrank ℤ Λ = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    have : ((L : Set (Fin g → ℂ))) = Set.range P := by
      ext x; simp [L]
    rw [this, hs]⟩
  let e : Λ ≃ₗ[ℤ] L := (AddMonoidHom.ofInjective hi).toIntLinearEquiv
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem riemLat_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P → ∃ R : RiemLat E g D.La, R.P = P ∧ R.form = D.EF ∧ (∀ a x i, R.B a x i = ty i (a : E) * x i) ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q := by
  intro E _ _ _ H D g ty P hty hP
  obtain ⟨hact, hinj, hdisc, hspan, Hm, hherm, hpos, him⟩ := hP
  obtain ⟨hfree, hfin, hrank⟩ := free_of_period P hinj hdisc hspan
  refine ⟨{ free := hfree, fin := hfin, rank := hrank, form := D.EF, alt := D.alt, unimod := D.unimod
            adj := ?_, P := P, Hm := Hm, herm := hherm, pos := hpos, im := him, B := diagAct ty, act := ?_ },
    rfl, rfl, fun a x i => diagAct_apply ty a x i, fun s => ?_⟩
  · intro a a' h x y
    have : a' = H.bar a := by
      apply RingOfIntegers.ext
      rw [H.bar_eq a]
      exact h
    rw [this]
    exact D.adj a x y
  · intro a x
    funext i
    exact hact a x i
  · show Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = _
    rw [finrank_eigSp_diagAct]
    by_cases h : s (H.rt : E) = H.rt0
    · rw [if_pos h]
      exact (hty s).1 h
    · rw [if_neg h]
      exact (hty s).2 h

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticPluckerColumnSwapStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_plucker_column_swap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → ∀ (l : Fin BM.q) (x₀ : FA.Re.R.X), FA.pr (FA.Re.π x₀) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FA.Re.R.lift x₀ x₀) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FC.Lca τ ca cb c a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalIntegrabilityStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_integrability : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, pPhi M F keep v bl h ε w ∈ pO M Rb keep v F kb V r h ∧ pRho M Rb keep v F kb r h ε (pPhi M F keep v bl h ε w) = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead.chart_reads | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead.chart_reads | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead.chart_reads <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightBoundFullIntersectionSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

namespace MuPos

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} =
      ⋂ k, ⋃ i, {z : (Σ k, J k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem contDiffAt_logH {A : HermLine J} (hA : IsSmoothHerm A) {n : ℕ}
    {g : (Fin n → ℂ) → (Σ k, J k) → ℂ} {t : Fin n → ℂ} (hg : AnalyticAt ℂ g t)
    (hz : ∀ k, ∃ i, g t ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun s => Real.log (A.h (g s))) t := by
  have h1 : ContDiffAt ℝ 2 A.h (g t) :=
    ((hA.contDiffAt (isOpen_blockNonzero.mem_nhds hz)).of_le (by norm_cast))
  have h2 : ContDiffAt ℝ 2 g t := hg.restrictScalars.contDiffAt
  exact (h1.comp t h2).log (A.pos _ hz).ne'

theorem levi_const_mul {n : ℕ} {f : (Fin n → ℂ) → ℝ} {t : Fin n → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f t)
    (v : Fin n → ℂ) : levi (fun y => c * f y) t v = c * levi f t v := by
  have h := ReciprocityTheory.AnForm.levi_add_smul c (contDiffAt_const (c := (0 : ℝ))) hf v
  simp only [zero_add] at h
  rw [h]
  simp [levi]

theorem exists_analytic_sum {n : ℕ} (s : Finset ℕ) (f : ℕ → (Fin n → ℂ) → ℝ) (t : Fin n → ℂ)
    (h : ∀ r ∈ s, ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ u in 𝓝 t, f r u = (G u).re) :
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ u in 𝓝 t, ∑ r ∈ s, f r u = (G u).re := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, analyticAt_const, by simp⟩
  | insert r s hr ih =>
    obtain ⟨G₁, hG₁, e₁⟩ := h r (Finset.mem_insert_self r s)
    obtain ⟨G₂, hG₂, e₂⟩ := ih fun r' hr' => h r' (Finset.mem_insert_of_mem hr')
    refine ⟨fun u => G₁ u + G₂ u, hG₁.add hG₂, ?_⟩
    filter_upwards [e₁, e₂] with u h₁ h₂
    rw [Finset.sum_insert hr, h₁, h₂, Complex.add_re]

theorem levi_split {n : ℕ} {fM fA F : (Fin n → ℂ) → ℝ} {G : (Fin n → ℂ) → ℂ} {t : Fin n → ℂ} {p q : ℝ}
    (hq : q ≠ 0) (hM : ContDiffAt ℝ 2 fM t) (hA : ContDiffAt ℝ 2 fA t) (hG : AnalyticAt ℂ G t)
    (hE : ∀ᶠ s in 𝓝 t, fM s = q * (F s + (G s).re) + p * fA s) (v : Fin n → ℂ) :
    levi fM t v = q * levi F t v + p * levi fA t v := by
  have hRe : ContDiffAt ℝ 2 (fun y => (G y).re) t :=
    Complex.reCLM.contDiff.contDiffAt.comp t (hG.restrictScalars.contDiffAt)
  have hMA : ContDiffAt ℝ 2 (fun y => fM y + (-p) * fA y) t := hM.add (contDiffAt_const.mul hA)
  have hR : ContDiffAt ℝ 2 (fun y => (fM y + (-p) * fA y) + (-q) * (G y).re) t :=
    hMA.add (contDiffAt_const.mul hRe)
  have hF : F =ᶠ[𝓝 t] fun y => q⁻¹ * ((fM y + (-p) * fA y) + (-q) * (G y).re) := by
    filter_upwards [hE] with y hy
    rw [hy]
    field_simp
    ring
  rw [ReciprocityTheory.AnForm.levi_congr hF v, levi_const_mul _ hR, ReciprocityTheory.AnForm.levi_add_smul (-q) hMA hRe,
    ReciprocityTheory.AnForm.levi_add_smul (-p) hM hA, ReciprocityTheory.AnForm.levi_re_analytic hG]
  field_simp
  ring

def sqDiv (A B : HermLine J) (p : ℕ) : HermLine J where
  a := (2 : ℤ) • A.a - (p : ℤ) • B.a
  h z := A.h z ^ 2 * (B.h z ^ p)⁻¹
  pos z hz := by
    have h1 := A.pos z hz
    have h2 := B.pos z hz
    positivity
  smul c z hc := by
    rw [A.smul c z hc, B.smul c z hc]
    have : ∀ k, ‖c k‖ ^ ((2 : ℤ) • A.a - (p : ℤ) • B.a) k =
        (‖c k‖ ^ A.a k) ^ 2 * ((‖c k‖ ^ B.a k) ^ p)⁻¹ := fun k => by
      have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [zpow_sub₀ h0, mul_comm (2 : ℤ), mul_comm (p : ℤ), _root_.zpow_mul, _root_.zpow_mul, div_eq_mul_inv]
      simp only [zpow_natCast, zpow_ofNat]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, mul_pow, mul_inv]
    ring

theorem sqDiv_smooth {A B : HermLine J} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (p : ℕ) :
    IsSmoothHerm (sqDiv A B p) :=
  (hA.pow 2).mul ((hB.pow p).inv fun z hz => (pow_pos (B.pos z hz) p).ne')

end MuPos

open MuPos

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

theorem chart_levi_split (D : ComponentData II Ψ K J Ω W) (S : Finset ℕ) (hS : S ⊆ D.S)
    (A : HermLine J) (hA : IsSmoothHerm A) (F : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℝ) (a : Fin D.nCharts) (p q : ℕ) (hq : q ≠ 0)
    (t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) (ht : ‖t‖ ≤ 1 / 2)
    (hform : ∀ s ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, Real.log (A.h ((D.chart a).γ s)) =
      q * (F s + ∑ r ∈ S, Real.log (D.vertFactor r ((D.chart a).γ s))) + p * Real.log (D.A'.h ((D.chart a).γ s)))
    (v : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) :
    levi (fun s => Real.log (A.h ((D.chart a).γ s))) t v =
      q * levi F t v + p * levi (fun s => Real.log (D.A'.h ((D.chart a).γ s))) t v := by
  have hb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 := by
    rw [mem_ball_zero_iff]; linarith
  have hγ : AnalyticAt ℂ (D.chart a).γ t := (D.chart a).analytic t hb
  have hz : ∀ k, ∃ i, (D.chart a).γ t ⟨k, i⟩ ≠ 0 := ((D.chart a).mem t hb).1
  obtain ⟨G, hG, hGe⟩ := exists_analytic_sum S (fun r s => Real.log (D.vertFactor r ((D.chart a).γ s))) t
    fun r hr => (GlobalTheory.T.vertical_factor_smooth_hermitian_metric K J II Ψ Ω W D r (hS hr)).2 a t hb
  refine levi_split (G := G) (by exact_mod_cast hq) (contDiffAt_logH hA hγ hz)
    (contDiffAt_logH D.A'_pos.1 hγ hz) hG ?_ v
  filter_upwards [hGe, Metric.isOpen_ball.mem_nhds hb] with s h₁ h₂
  rw [hform s h₂, h₁]

theorem chart_levi_sqDiv (D : ComponentData II Ψ K J Ω W) (A : HermLine J) (hA : IsSmoothHerm A)
    (a : Fin D.nCharts) (p : ℕ) (t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) (ht : ‖t‖ ≤ 1 / 2) (v : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) :
    levi (fun s => Real.log ((sqDiv A D.A' p).h ((D.chart a).γ s))) t v =
      2 * levi (fun s => Real.log (A.h ((D.chart a).γ s))) t v -
        p * levi (fun s => Real.log (D.A'.h ((D.chart a).γ s))) t v := by
  have hb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 := by
    rw [mem_ball_zero_iff]; linarith
  have hγ : AnalyticAt ℂ (D.chart a).γ t := (D.chart a).analytic t hb
  have hz : ∀ k, ∃ i, (D.chart a).γ t ⟨k, i⟩ ≠ 0 := ((D.chart a).mem t hb).1
  have h1 := contDiffAt_logH hA hγ hz
  have h2 := contDiffAt_logH D.A'_pos.1 hγ hz
  have hE : (fun s => Real.log ((sqDiv A D.A' p).h ((D.chart a).γ s))) =ᶠ[𝓝 t]
      fun s => 2 * Real.log (A.h ((D.chart a).γ s)) + (-(p : ℝ)) * Real.log (D.A'.h ((D.chart a).γ s)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hb] with s hs
    have hzs : ∀ k, ∃ i, (D.chart a).γ s ⟨k, i⟩ ≠ 0 := ((D.chart a).mem s hs).1
    have p1 := A.pos _ hzs
    have p2 := D.A'.pos _ hzs
    show Real.log (A.h _ ^ 2 * (D.A'.h _ ^ p)⁻¹) = _
    rw [Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [ReciprocityTheory.AnForm.levi_congr hE v, ReciprocityTheory.AnForm.levi_add_smul _ (contDiffAt_const.mul h1) h2,
    levi_const_mul _ h1]
  ring

theorem posU_of_nefOnFibres : PB.Inputs → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), IsFullIntersectionSystem II → S'.IsTied → (∀ B : ℕ, 4 * D.f + 2 ≤ B → NefOnFibres (mCoordIdeal D.y) (muTwDeg Hd B)) → PosU S' := by
  intro hPB K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w S' hII hT hNef B p q hB hp hpq
  obtain ⟨δ₀, hδ₀, hApos⟩ := GlobalTheory.T.uniform_levi_positivity_on_charts K J II Ψ Ω W D
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq1 : 1 ≤ q := hp.trans hpq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hδ : 0 < p * δ₀ / (2 * q) := by positivity
  have hev := (GlobalTheory.T.regularized_weight_dominates_eventually K J II Ψ Ω W D Hd M w S' hT).and
    (GlobalTheory.T.regularized_levi_lower_bound_eventually K J II Ψ Ω W D Hd M w S' hT _ hδ)
  have key : ∀ LF LA V : ℝ, 0 ≤ V → -(p * δ₀ / (2 * q) * V) ≤ LF → δ₀ * V ≤ LA →
      0 ≤ q * LF + p * LA ∧ 0 ≤ 2 * (q * LF + p * LA) - p * LA := by
    intro LF LA V hV h1 h2
    have e1 : -(p * δ₀ / 2 * V) ≤ q * LF := by
      have := mul_le_mul_of_nonneg_left h1 hq0.le
      have e : (q : ℝ) * -(p * δ₀ / (2 * q) * V) = -(p * δ₀ / 2 * V) := by
        field_simp
      linarith
    have e2 : p * (δ₀ * V) ≤ p * LA := mul_le_mul_of_nonneg_left h2 hp0.le
    have e3 : 0 ≤ p * δ₀ * V := by positivity
    constructor <;> nlinarith
  obtain ⟨t₀, ht₀, hsub⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 hev
  refine ⟨t₀, ht₀, fun t' ht' ht'₀ => ?_⟩
  obtain ⟨⟨-, -, hMU⟩, hreg⟩ := hsub ⟨ht', ht'₀⟩
  obtain ⟨hsm, hdeg, hform⟩ := hMU B p q
  set A := MUc Hd S' B p q t' with hAdef
  have hsplit : ∀ (a : Fin D.nCharts) (t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), ‖t‖ ≤ 1 / 2 → ∀ v : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ,
      levi (fun s => Real.log (A.h ((D.chart a).γ s))) t v =
        q * levi (fun s => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v +
          p * levi (fun s => Real.log (D.A'.h ((D.chart a).γ s))) t v := by
    intro a t ht v
    refine chart_levi_split D (D.SB B) (Finset.filter_subset _ _) A hsm _ a p q (by omega) t ht (fun s hs => ?_) v
    exact hform _ ((D.chart a).mem s hs)
  have hsemi : IsSemipositiveH (mCoordIdeal D.y) A := by
    refine GlobalTheory.T.semipositive_levi_of_log_metric K J II Ψ Ω W D A hsm fun a t ht v => ?_
    have e := hsplit a t ht v
    have b1 := hreg a t ht v
    have b2 := hApos a t ht v
    rw [e]
    exact (key _ _ _ (by positivity) b1 b2).1
  have hN : IsSemipositiveH (mCoordIdeal D.y) (sqDiv A D.A' p) := by
    refine GlobalTheory.T.semipositive_levi_of_log_metric K J II Ψ Ω W D _ (sqDiv_smooth hsm D.A'_pos.1 p) fun a t ht v => ?_
    have e0 := chart_levi_sqDiv D A hsm a p t ht v
    have e := hsplit a t ht v
    have b1 := hreg a t ht v
    have b2 := hApos a t ht v
    rw [e0, e]
    exact (key _ _ _ (by positivity) b1 b2).2
  refine ⟨hsemi, ?_, ?_⟩
  · rw [hdeg]
    exact GlobalTheory.T.nef_on_fibres_add_nonneg hPB K J _ _ _ p q (hNef B hB) fun k => (D.a'_pos k).le
  · refine GlobalTheory.T.ample_on_generic_fibre_of_semipositive hPB II hII K J _ (sqDiv A D.A' p) A D.a' 2 p hN hsm D.a'_pos (by norm_num) hp ?_
    ext k
    simp [sqDiv, D.A'_deg]

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem ptsIntegrable_of_resK :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → PtsIntegrableStatement :=
  fun h => GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists (GlobalTheory.T.resolution_exists_of_resolution_statement h)

end GlobalTheory.CompanionTheory.Ar.Giv
end

