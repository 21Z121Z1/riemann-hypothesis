import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0356
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0210
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0370
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceTransposePow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0249
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0235
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0365

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePh
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KernelExpansion

theorem exists_mem_of_dense {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H))] (S : Submodule ℂ H) (hS : Dense (S : Set H))
    (x : H) : ∃ g ∈ S, T g = T x := by
  have : FiniteDimensional ℂ (S.map (T : H →ₗ[ℂ] H)) :=
    Submodule.finiteDimensional_of_le LinearMap.map_le_range
  have hc : IsClosed ((fun z => T z) ⁻¹' (S.map (T : H →ₗ[ℂ] H) : Set H)) :=
    (Submodule.closed_of_finiteDimensional _).preimage T.continuous
  have hx : x ∈ closure (S : Set H) := hS x
  exact hc.closure_subset_iff.2 (fun z hz => ⟨z, hz, rfl⟩) hx

theorem exists_orthonormal {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H))]
    (hT : IsOrthProjOnto T (LinearMap.range (T : H →ₗ[ℂ] H))) (D : ℕ)
    (hD : Module.finrank ℂ (LinearMap.range (T : H →ₗ[ℂ] H)) = D) :
    ∃ y : Fin D → H, Orthonormal ℂ y ∧ Submodule.span ℂ (Set.range y) = LinearMap.range (T : H →ₗ[ℂ] H) ∧
      (∀ i, T (y i) = y i) ∧ ∀ g, T g = ∑ i, ⟪y i, g⟫_ℂ • y i := by
  subst hD
  let b := stdOrthonormalBasis ℂ (LinearMap.range (T : H →ₗ[ℂ] H))
  have hfix : ∀ i, T (b i : H) = b i := by
    intro i
    obtain ⟨z, hz⟩ := (b i).2
    have := congrArg (fun A : H →L[ℂ] H => A z) hT.1
    rw [← hz]
    exact this
  have hexp : ∀ g, T g = ∑ i, ⟪(b i : H), g⟫_ℂ • (b i : H) := by
    intro g
    have h := congrArg Subtype.val (b.sum_repr' ⟨T g, g, rfl⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hT.2.1, hfix]
  refine ⟨fun i => b i, b.orthonormal.comp_linearIsometry (Submodule.subtypeₗᵢ _), ?_, hfix, hexp⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  · rintro _ ⟨g, rfl⟩
    show T g ∈ _
    rw [hexp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def compactSub {X : Type} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {y | ∃ C : Set X, IsCompact C ∧ ∀ᵐ z ∂μ, z ∉ C → (y : X → ℂ) z = 0}
  add_mem' := by
    rintro a b ⟨C, hC, ha⟩ ⟨C', hC', hb⟩
    refine ⟨C ∪ C', hC.union hC', ?_⟩
    filter_upwards [ha, hb, Lp.coeFn_add a b] with z h1 h2 h3 hz
    rw [Set.mem_union, not_or] at hz
    rw [h3, Pi.add_apply, h1 hz.1, h2 hz.2, add_zero]
  zero_mem' := ⟨∅, isCompact_empty, by
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z h _
    rw [h]; rfl⟩
  smul_mem' := by
    rintro c a ⟨C, hC, ha⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [ha, Lp.coeFn_smul c a] with z h1 h2 hz
    rw [h2, Pi.smul_apply, h1 hz, smul_zero]

theorem coeFn_sum_smul {X ι : Type} [MeasurableSpace X] (μ : Measure X) (s : Finset ι) (c : ι → ℂ)
    (y : ι → Lp ℂ 2 μ) (F : ι → X → ℂ) (h : ∀ i, (y i : X → ℂ) =ᵐ[μ] F i) :
    ((∑ i ∈ s, c i • y i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, c i * F i x := by
  first
  | exact @_root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq
  | exact _root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq
  | (apply _root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq ..)

theorem ae_eq_of_pairing {X ι : Type} [Fintype ι] [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] (k : X → ℂ) (hk : Continuous k)
    (c : ι → ℂ) (y : ι → Lp ℂ 2 μ) (F : ι → X → ℂ) (hF : ∀ i, Continuous (F i))
    (h : ∀ i, (y i : X → ℂ) =ᵐ[μ] F i)
    (hp : ∀ g ∈ compactSub μ, ∫ z, k z * (g : X → ℂ) z ∂μ = ∑ i, ⟪y i, g⟫_ℂ * c i) :
    (fun z => k z - ∑ i, c i * star (F i z)) =ᵐ[μ] 0 := by
  have hc : ∀ i, Continuous fun z => c i * star (F i z) := fun i => continuous_const.mul (hF i).star
  refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    (hk.sub (continuous_finset_sum _ fun i _ => hc i)).locallyIntegrable fun s hs => ?_
  have hm : MeasurableSet s := hs.isClosed.measurableSet
  have hg := indicatorConstLp_coeFn (p := 2) (hs := hm) (hμs := hs.measure_lt_top.ne) (c := (1 : ℂ)) (μ := μ)
  have h1 := hp (indicatorConstLp 2 hm hs.measure_lt_top.ne (1 : ℂ)) ⟨s, hs, by
    filter_upwards [hg] with z hz hzs
    rw [hz, Set.indicator_of_notMem hzs]⟩
  have e : ∀ u : X → ℂ, ∫ z, u z * (indicatorConstLp 2 hm hs.measure_lt_top.ne (1 : ℂ) : Lp ℂ 2 μ) z ∂μ =
      ∫ z in s, u z ∂μ := by
    intro u
    rw [← integral_indicator hm]
    refine integral_congr_ae ?_
    filter_upwards [hg] with z hz
    rw [hz]
    by_cases hzs : z ∈ s <;> simp [hzs]
  rw [integral_sub (hk.continuousOn.integrableOn_compact hs)
    ((continuous_finset_sum _ fun i _ => hc i).continuousOn.integrableOn_compact hs),
    integral_finset_sum _ fun i _ => (hc i).continuousOn.integrableOn_compact hs, ← e, h1, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, ← e, mul_comm, L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h i] with z hz
  rw [hz]
  simp [mul_comm]

theorem integral_mul_star {X : Type} [MeasurableSpace X] (μ : Measure X) (y : Lp ℂ 2 μ) (F : X → ℂ)
    (h : (y : X → ℂ) =ᵐ[μ] F) (hy : ‖y‖ = 1) :
    Integrable (fun x => F x * star (F x)) μ ∧ ∫ x, F x * star (F x) ∂μ = 1 := by
  have e : (fun x => ⟪(y : X → ℂ) x, (y : X → ℂ) x⟫_ℂ) =ᵐ[μ] fun x => F x * star (F x) := by
    filter_upwards [h] with z hz
    rw [hz, RCLike.inner_apply]
    rfl
  refine ⟨(L2.integrable_inner y y).congr e, ?_⟩
  rw [← integral_congr_ae e, ← L2.inner_def, inner_self_eq_norm_sq_to_K, hy]
  simp

theorem norm_sum_sq_le {ι : Type} [Fintype ι] (c F : ι → ℂ) :
    ‖∑ i, c i * F i‖ ^ 2 ≤ (∑ i, ‖c i‖ ^ 2) * ‖∑ i, F i * star (F i)‖ := by
  have e : ∑ i, F i * star (F i) = ((∑ i, ‖F i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Complex.mul_conj' (F i)
  rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => ‖c i‖) (fun i => ‖F i‖))
  gcongr
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

theorem two_mul_rank_le {n : ℕ} (ε : Fin n → Bool) : 2 * rkR ε ≤ n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  unfold rkR
  omega

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hdec : LocDec B h)
    (hb : HBig B 32 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hle, hi⟩ := GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d h hd hdec
  have h1 := hi 0 le_rfl fun v => by
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with h0 | h0
    · exact Or.inl h0
    · right
      have h2 : (2 : ℝ) * rkR (B.I.ε v) ≤ B.I.n := by exact_mod_cast two_mul_rank_le _
      have h3 : (0 : ℝ) < rkR (B.I.ε v) := by exact_mod_cast h0
      have h4 := Real.sqrt_pos.2 h3
      refine lt_of_lt_of_le ?_ (hb v)
      have h5 : (B.I.n : ℝ) * rkR (B.I.ε v) < (B.I.n : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_lt_mul_of_pos_right h5 h4]
  refine h1.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
  simpa using hle g

theorem kernelB : KernelB := by
  intro B d h hd hn hdec hb hfin T hT
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  have : (Measure.pi fun v => Formalism.REAL.muG (B.I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  have : (B.I.muA B.μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  obtain ⟨-, -, -, hP⟩ := GlobalTheory.T.globalConvolutionOrthogonalProjector_proof B d hd (integrable_ph B d h hd hdec hb)
  obtain ⟨hproj, -, -, hfd, hD⟩ := hP T hT
  have := hfd hfin
  obtain ⟨hbd, hKc, hKi, -⟩ := GlobalTheory.T.automorphicKernel_convergence_properties B d h hd hn hdec hb
  obtain ⟨y, hy, hspan, hfix, hexp⟩ := exists_orthonormal T hproj B.D hD
  have hrep : ∀ g ∈ compactSub ((B.I.muA B.μf).restrict B.fund), IsContRep B (T g)
      (fun x => ∫ z in B.fund, kern B.I (phe B d) x z * (g : B.I.GA → ℂ) z ∂(B.I.muA B.μf)) := by
    rintro g ⟨C, hC, hg⟩
    exact GlobalTheory.T.isContRep_kernel_integral_compact_support B d h hd hn hdec hb T hT g C hC hg
  have huniq : ∀ (u : B.I.L2 B.μf B.fund) f f', IsContRep B u f → IsContRep B u f' → f' = f :=
    fun u f f' h1 h2 => (GlobalTheory.ExtContRep.ext_ae_eq_contRep B u f h1).2.1 f' h2
  have hF : ∀ i, ∃ F, IsContRep B (y i) F := by
    intro i
    obtain ⟨g, hg, e⟩ := exists_mem_of_dense T (compactSub _) (GlobalTheory.T.dense_compactly_supported_L2 B) (y i)
    exact ⟨_, hfix i ▸ e ▸ hrep g hg⟩
  choose F hF using hF
  have hK : ∀ x z, kern B.I (phe B d) x z = ∑ i, F i x * star (F i z) := by
    intro x z
    have hkx : Continuous fun z => kern B.I (phe B d) x z :=
      Continuous.comp (g := fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) (f := fun z => (x, z)) hKc
        (Continuous.prodMk_right x)
    have h0 := ae_eq_of_pairing ((B.I.muA B.μf).restrict B.fund) _ hkx (fun i => F i x) y F
      (fun i => (hF i).1) (fun i => (hF i).2.2) fun g hg => by
        have h1 : IsContRep B (T g) fun x => ∑ i, ⟪y i, g⟫_ℂ * F i x := by
          refine ⟨continuous_finset_sum _ fun i _ => continuous_const.mul (hF i).1, fun γ hγ x => ?_, ?_⟩
          · exact Finset.sum_congr rfl fun i _ => by rw [(hF i).2.1 γ hγ]
          · rw [hexp]
            exact coeFn_sum_smul _ _ _ y F fun i => (hF i).2.2
        exact congrFun (huniq _ _ _ h1 (hrep g hg)) x
    have z0 : IsContRep B 0 0 := ⟨continuous_const, fun _ _ _ => rfl, Lp.coeFn_zero _ _ _⟩
    have z1 : IsContRep B 0 fun z => kern B.I (phe B d) x z - ∑ i, F i x * star (F i z) := by
      refine ⟨hkx.sub (continuous_finset_sum _ fun i _ => continuous_const.mul (hF i).1.star),
        fun γ hγ w => ?_, (Lp.coeFn_zero _ _ _).trans h0.symm⟩
      beta_reduce
      rw [(hKi γ hγ x w).2]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [(hF i).2.1 γ hγ]
    exact sub_eq_zero.1 (congrFun (huniq _ _ _ z0 z1) z)
  have hI := fun i => integral_mul_star _ (y i) (F i) (hF i).2.2 (hy.1 i)
  refine ⟨y, F, hy, hspan, hF, hK, ?_, ?_, fun c x => ?_⟩
  · simp only [hK]
    exact integrable_finset_sum _ fun i _ => (hI i).1
  · simp only [hK]
    rw [integral_finset_sum _ fun i _ => (hI i).1]
    simp only [(hI _).2]
    simp
  · refine (norm_sum_sq_le c fun i => F i x).trans ?_
    rw [← hK]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_tsum_le_tsum_norm (hbd x x).1).trans ((hbd x x).2.trans (le_of_eq ?_))
    rw [mul_inv, ← sq, ← pow_mul]
    congr 2
    ring

end GlobalTheory.KernelExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeInfinitesimalCharLargeGap
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.DSId.LowCharGap
open GlobalTheory.Dec.FormF
variable {n : ℕ}

private theorem mul_mem_UJset' {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hh : inUJ ε h) : g * h ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg', hh']

private theorem eword_congr_on_UJset {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ UJset ε, f g = f' g) (w : List (Fin n × Fin n)) :
    ∀ g ∈ UJset ε, Eword ε w f g = Eword ε w f' g := by
  induction w with
  | nil => intro g hg; exact h g hg
  | cons p w ih =>
    intro g hg
    have key : ∀ X, inG ε X → Rd X (Eword ε w f) g = Rd X (Eword ε w f') g := by
      intro X hX
      show deriv (fun t : ℝ => Eword ε w f (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
        deriv (fun t : ℝ => Eword ε w f' (g * NormedSpace.exp ((t : ℂ) • X))) 0
      congr 1
      funext t
      exact ih _ (mul_mem_UJset' hg (expUJ n ε X hX t))
    show Rd (cpart1 ε (Matrix.single p.1 p.2 1)) (Eword ε w f) g +
        Complex.I * Rd (cpart2 ε (Matrix.single p.1 p.2 1)) (Eword ε w f) g =
      Rd (cpart1 ε (Matrix.single p.1 p.2 1)) (Eword ε w f') g +
        Complex.I * Rd (cpart2 ε (Matrix.single p.1 p.2 1)) (Eword ε w f') g
    rw [key _ (cpartMem n ε _).1, key _ (cpartMem n ε _).2.1]

lemma gelf_congr {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (h : ∀ g ∈ UJset ε, f g = f' g) (m : ℕ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    gelf ε m f g = gelf ε m f' g := by
  unfold gelf
  exact Finset.sum_congr rfl (fun a _ => eword_congr_on_UJset h _ g hg)

private theorem star_mem_Kset_of_mem {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    star k ∈ Kset ε := by
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  have h := congrArg star hk'.2
  simp only [star_mul] at h
  have hJ : star (Jm ε) = Jm ε := by rw [Matrix.star_eq_conjTranspose, Jm_conjTranspose]
  rw [hJ] at h
  show star k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ star k * Jm ε = Jm ε * star k
  exact ⟨Unitary.star_mem hk'.1, h.symm⟩

private theorem posDef_conjTranspose_mul_exp_mul {ε : Fin n → Bool} {m X : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ Kset ε)
    (hX : inP ε X) : (mᴴ * NormedSpace.exp X * m).PosDef := by
  have hm' : m ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ m * Jm ε = Jm ε * m := hm
  have hu : mᴴ * m = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hm'.1
  apply Matrix.PosDef.conjTranspose_mul_mul_same (exp_posDef hX)
  intro a b hab
  have := congrArg (fun x => (mᴴ).mulVec x) hab
  simpa only [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec] using this
set_option maxHeartbeats 1000000 in

lemma compress_of_formula (hF : FormulaGap) {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hlam : IsHCParam lam) (hσ : IsDS ε lam σ)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h)
    (hS : IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ)) {w : lowKSub ε lam σ}
    (hw : IsHighestUnit ε lam σ (w : H))
    {τ : Matrix (Fin n) (Fin n) ℂ → (lowKSub ε lam σ →L[ℂ] lowKSub ε lam σ)} (hτ : IsTau ε (lowK ε lam) τ w)
    (hτσ : ∀ k ∈ Kset ε, ∀ v : lowKSub ε lam σ, (τ k v : H) = σ (k.map star) v) :
    ∀ g ∈ UJset ε, ∀ u v : lowKSub ε lam σ,
      ⟪(v : H), σ g u⟫_ℂ = ⟪v, Psi ε lam τ w (g.map star) u⟫_ℂ := by
  intro g hg u v
  obtain ⟨-, -, hU, -, -, -, -⟩ := id hσ
  have hKU : IsURepOn (Kset ε) σ := URep_K hU
  obtain ⟨⟨-, hmul⟩, -, hcont⟩ := id hU
  obtain ⟨hfin, hstab, -, -, -⟩ := id hS
  obtain ⟨k, X, hk, hX, rfl⟩ := (polar n ε).1 g hg
  have hsk : star k ∈ Kset ε := star_mem_Kset_of_mem hk
  have hkb : k.map star ∈ Kset ε := K_star hk
  have hXb : inP ε (X.map star) := P_star hX
  have hXg : inG ε X := hX.1
  have hexp : NormedSpace.exp X ∈ UJset ε := by
    have h1 := expUJ n ε X hXg 1
    simp only [Complex.ofReal_one, one_smul] at h1
    exact h1
  have hv'mem : σ (star k) (v : H) ∈ lowKSub ε lam σ := hstab _ hsk _ v.2
  have hcontτ : ∀ y : lowKSub ε lam σ, ContinuousOn (fun m => τ m y) (Kset ε) := by
    intro y
    have h1 : ContinuousOn (fun m : Matrix (Fin n) (Fin n) ℂ => σ (m.map star) (y : H)) (Kset ε) :=
      (hcont (y : H)).comp (continuous_id.matrix_map continuous_star).continuousOn
        (fun m hm => K_UJ (K_star hm))
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact h1.congr (fun m hm => hτσ m hm y)
  have hF' := hF n ε lam H σ hlam hσ h hgap hh (w : H) hw X hX (u : H) u.2 (σ (star k) (v : H)) hv'mem
  have hP := psEntry GlobalTheory.T.phi_positive_definite_cholesky_formula n ε lam (lowKSub ε lam σ) τ w hfin hcontτ
    (NormedSpace.exp (X.map star)) (exp_posDef hXb) u ⟨σ (star k) (v : H), hv'mem⟩
  have hC := muConj n ε (fun m => Phi lam (m⁻¹ * NormedSpace.exp (X.map star) * m) *
    (⟪(⟨σ (star k) (v : H), hv'mem⟩ : lowKSub ε lam σ), τ m w⟫_ℂ * ⟪τ m w, u⟫_ℂ))
  try simp only [] at hC
  have hconj : (k * NormedSpace.exp X).map star = k.map star * NormedSpace.exp (X.map star) := by
    rw [map_star_mul, exp_star]
  rw [hconj, (GlobalTheory.T.psi_polar_decomposition_equivariance n ε lam (lowKSub ε lam σ) τ w hlam hτ).1 _ hkb _ hXb,
    ContinuousLinearMap.comp_apply, hmul k (K_UJ hk) _ hexp, ContinuousLinearMap.comp_apply]
  have e1 : ⟪(v : H), σ k (σ (NormedSpace.exp X) (u : H))⟫_ℂ =
      ⟪σ (star k) (v : H), σ (NormedSpace.exp X) (u : H)⟫_ℂ := by
    rw [inner_rep_K hKU hsk, star_star]
  have e2 : ⟪v, τ (k.map star) (ps ε lam τ w (NormedSpace.exp (X.map star)) u)⟫_ℂ =
      ⟪(⟨σ (star k) (v : H), hv'mem⟩ : lowKSub ε lam σ), ps ε lam τ w (NormedSpace.exp (X.map star)) u⟫_ℂ := by
    rw [Submodule.coe_inner, Submodule.coe_inner, hτσ _ hkb, map_star_star]
    have h5 := inner_rep_K hKU hsk (v : H) ((ps ε lam τ w (NormedSpace.exp (X.map star)) u : lowKSub ε lam σ) : H)
    rw [star_star] at h5
    exact h5.symm
  rw [e1, e2, hF', hP, ← hC]
  congr 1
  congr 1
  funext k'
  have hm : toMK k' ∈ Kset ε := by rw [← range_toMK ε]; exact Set.mem_range_self k'
  have hmb := K_star hm
  rw [Submodule.coe_inner, Submodule.coe_inner, hτσ _ hmb, map_star_star]
  rw [K_inv hmb, K_inv hm, map_star_ct, ← exp_star, ← map_star_mul, ← map_star_mul, Phi_star]
  have hpos := (GlobalTheory.T.phi_positive_definite_cholesky_formula n lam _ (posDef_conjTranspose_mul_exp_mul hm hX)).2.1
  have him : (Phi lam ((toMK k')ᴴ * NormedSpace.exp X * toMK k')).im = 0 := by
    have h2 := (Complex.lt_def.mp hpos).2
    rw [Complex.zero_im] at h2
    linarith
  have hreal : star (Phi lam ((toMK k')ᴴ * NormedSpace.exp X * toMK k')) =
      Phi lam ((toMK k')ᴴ * NormedSpace.exp X * toMK k') :=
    Complex.ext (by simp [Complex.star_def]) (by simp [Complex.star_def, him])
  rw [hreal]
  try rfl

lemma two_mul_lt_gap {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hgap : GapAtLeast ε lam h)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (a b : Fin n) (hab : ε a ≠ ε b) :
    2 * (n : ℝ) < |lam a - lam b| := by
  have h1 := hgap a b hab
  have hn : (0:ℝ) < n := by exact_mod_cast (Fin.pos a)
  have ht : ∃ x, ε x = true := by
    cases h : ε a
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
    · exact ⟨a, h⟩
  have hf : ∃ x, ε x = false := by
    cases h : ε a
    · exact ⟨a, h⟩
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
  obtain ⟨x, hx⟩ := ht
  obtain ⟨y, hy⟩ := hf
  have hq1 : 1 ≤ rkR ε := by
    unfold rkR
    apply le_min
    · exact Finset.card_pos.mpr ⟨x, by simp [hx]⟩
    · exact Finset.card_pos.mpr ⟨y, by simp [hy]⟩
  have hq : (1:ℝ) ≤ ((rkR ε : ℕ) : ℝ) := by exact_mod_cast hq1
  have hp : (1:ℝ) ≤ ((rkR ε : ℕ) : ℝ) ^ ((3:ℝ)/2) := Real.one_le_rpow hq (by norm_num)
  nlinarith

theorem lowChar_of_formula (hF : FormulaGap) (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hlam : IsHCParam lam) (hσ : IsDS ε lam σ) (h : ℝ) (hgap : GapAtLeast ε lam h)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h)
    (hS : IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ)) :
    ∀ s ∈ lowKSub ε lam σ, ∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g s⟫_ℂ) := by
  haveI : CompleteSpace H := hσ.1
  obtain ⟨-, -, hU, -, -, -, -⟩ := id hσ
  have hKU : IsURepOn (Kset ε) σ := URep_K hU
  obtain ⟨⟨hσ1, -⟩, -, -⟩ := id hU
  obtain ⟨c, hc⟩ := GlobalTheory.T.gelfandInvariants_scalar_on_lowestKType_coefficients n ε lam H σ hU hS
  obtain ⟨-, -, -, ⟨v0, hv0S, hv0, hv0w⟩, -⟩ := id hS
  obtain ⟨w, hwdef⟩ : ∃ w : H, w = ((‖v0‖ : ℂ))⁻¹ • v0 := ⟨_, rfl⟩
  have hwS : w ∈ lowKSub ε lam σ := by rw [hwdef]; exact (lowKSub ε lam σ).smul_mem _ hv0S
  have hwn : ‖w‖ = 1 := by rw [hwdef]; exact norm_smul_inv_norm (𝕜 := ℂ) hv0
  have hww : IsWtOn (Kset ε) σ (lowK ε lam) w := by
    intro θ hθ
    rw [hwdef, map_smul, hv0w θ hθ]
    exact smul_comm _ _ _
  obtain ⟨τ, hτ, hτσ⟩ := GlobalTheory.T.kType_extends_holomorphic_complexifiedK n ε (lowK ε lam) H σ (lowKSub ε lam σ) ⟨w, hwS⟩ hKU hS hwn hww
  have hhw : IsHighestUnit ε lam σ ((⟨w, hwS⟩ : lowKSub ε lam σ) : H) := by
    show _ ∧ _ ∧ _
    exact ⟨hwn, hwS, hww⟩
  have hcomp := compress_of_formula hF hlam hσ hgap hh hS hhw hτ hτσ
  have h1UJ : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := K_UJ (one_K ε)
  have hPE := GlobalTheory.T.psiEntries_centreEigenfunctions_discreteSeries n ε lam (lowKSub ε lam σ) τ ⟨w, hwS⟩ hlam hτ ⟨w, hwS⟩ ⟨w, hwS⟩
  have hEC := eigConj n ε _ _ hPE.1 hPE.2
  have hfs : SmoothOnG ε (fun g => ⟪w, σ g w⟫_ℂ) := (hc w hwS w).1
  have hone : ⟪w, σ 1 w⟫_ℂ = 1 := by
    rw [hσ1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hwn]
    simp
  have hcm : ∀ m, c m = gelfVal (fun a => (lam a : ℂ)) (m + 1) := by
    intro m
    have h1 := (hc w hwS w).2 m 1 h1UJ
    have h2 := gelf_congr hfs (fun g hg => hcomp g hg ⟨w, hwS⟩ ⟨w, hwS⟩) m h1UJ
    have h3 := hEC.2.2 m 1 h1UJ
    have h4 := hcomp 1 h1UJ ⟨w, hwS⟩ ⟨w, hwS⟩
    have h5 : c m * ⟪w, σ 1 w⟫_ℂ = gelfVal (fun a => -(-(lam a : ℂ))) (m + 1) * ⟪w, σ 1 w⟫_ℂ := by
      rw [← h1, h2, h3]
      exact congrArg _ h4.symm
    rw [hone, mul_one, mul_one] at h5
    simpa only [neg_neg] using h5
  intro s hs y
  show _ ∧ _
  refine ⟨(hc s hs y).1, fun m g hg => ?_⟩
  rw [(hc s hs y).2 m g hg, hcm m]

theorem lowChar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ, GapAtLeast ε lam h → 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h → ∀ s ∈ lowKSub ε lam σ, ∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g s⟫_ℂ) := fun n ε lam H _ _ σ hlam hσ h hgap hh =>
  lowChar_of_formula GlobalTheory.T.lowestKType_compressionFormula_of_strictLowestKType n ε lam H σ hlam hσ h hgap hh
    (GlobalTheory.T.lowestKType_isKType_of_large_gaps n ε lam H σ hlam hσ (fun a b hab => two_mul_lt_gap hgap hh a b hab))

end GlobalTheory.DSId.LowCharGap
end
end

