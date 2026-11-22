import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import ReciprocityTheory.DualLattices.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDensityBoundNearPoint
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder

namespace GlobalTheory.LineCos

def splitLin (d : ℕ) : V (d + 1) ≃ₗ[ℝ] (Fin d → ℂ) × ℂ where
  toFun z := (base z, fib z)
  invFun p := WithLp.toLp 2 (Fin.snoc p.1 p.2 : Fin (d + 1) → ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [fib]
    · simp [base]
  right_inv p := by
    ext i
    · simp [base]
    · simp [fib]

theorem exists_lintegral_le_iterated (d : ℕ) : ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : V (d + 1) → ENNReal,
    ∫⁻ z, F z ≤ c * ∫⁻ b : Fin d → ℂ, ∫⁻ x : ℂ, F ((splitLin d).symm (b, x)) := by
  let e : V (d + 1) ≃L[ℝ] (Fin d → ℂ) × ℂ := (splitLin d).toContinuousLinearEquiv
  let em : V (d + 1) ≃ᵐ (Fin d → ℂ) × ℂ := e.toHomeomorph.toMeasurableEquiv
  haveI : Measure.IsAddHaarMeasure (Measure.map e (volume : Measure (V (d + 1)))) := inferInstance
  haveI : Measure.IsAddHaarMeasure (volume : Measure ((Fin d → ℂ) × ℂ)) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin d → ℂ)) (volume : Measure ℂ)
  have h := Measure.isAddLeftInvariant_eq_smul (Measure.map e (volume : Measure (V (d + 1))))
    (volume : Measure ((Fin d → ℂ) × ℂ))
  refine ⟨Measure.addHaarScalarFactor (Measure.map e (volume : Measure (V (d + 1))))
    (volume : Measure ((Fin d → ℂ) × ℂ)), ENNReal.coe_ne_top, fun F => ?_⟩
  have h1 : ∫⁻ z, F z = ∫⁻ p, F (e.symm p) ∂(Measure.map e (volume : Measure (V (d + 1)))) := by
    have := lintegral_map_equiv (μ := (volume : Measure (V (d + 1)))) (fun p => F (e.symm p)) em
    simpa [em] using this.symm
  rw [h1]
  conv_lhs => rw [h]
  rw [lintegral_smul_measure]
  refine mul_le_mul_right ?_ _
  exact lintegral_prod_le (μ := (volume : Measure (Fin d → ℂ))) (ν := (volume : Measure ℂ)) (fun p => F (e.symm p))

def fsDensity (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  G.det.re / (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2)

theorem fsDensity_pos (s : Bool) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) : 0 < fsDensity s G x :=
  div_pos (Complex.pos_iff.1 hG.det_pos).1
    (mul_pos Real.pi_pos (pow_pos (re_hform_pos hG (lineVec_ne_zero s x)) 2))

theorem continuousOn_fsDensity {d : ℕ} {O : Set (V (d + 1))} {G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ} (s : Bool)
    (hc : ContinuousOn (fun z => G (base z)) O) (hp : ∀ z ∈ O, (G (base z)).PosDef) :
    ContinuousOn (fun z => fsDensity s (G (base z)) (fib z)) O := by
  have he : ∀ i j, ContinuousOn (fun z => G (base z) i j) O := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)
  have hx : Continuous (fun z : V (d + 1) => fib z) := by
    unfold fib
    fun_prop
  have hw : ∀ i, Continuous (fun z : V (d + 1) => lineVec s (fib z) i) := fun i => by
    cases s
    · fin_cases i
      · exact continuous_const
      · exact hx
    · fin_cases i
      · exact hx
      · exact continuous_const
  have hh : ContinuousOn (fun z => hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))) O := by
    unfold hform
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    exact (((hw i).mul ((Complex.continuous_conj).comp (hw j))).continuousOn).mul (he i j)
  have hdet : ContinuousOn (fun z => (G (base z)).det) O :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hc
  refine (Complex.continuous_re.comp_continuousOn hdet).div
    (continuousOn_const.mul ((Complex.continuous_re.comp_continuousOn hh).pow 2)) fun z hz => ?_
  exact (mul_pos Real.pi_pos (pow_pos (re_hform_pos (hp z hz) (lineVec_ne_zero s _)) 2)).ne'

theorem measurable_cosSq (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) : Measurable (cosSq s G) := by
  have hw : ∀ i, Continuous (fun x : ℂ => lineVec s x i) := fun i => by
    cases s
    · fin_cases i
      · exact continuous_const
      · exact continuous_id
    · fin_cases i
      · exact continuous_id
      · exact continuous_const
  have hh : ∀ (b : ℂ → Fin 2 → ℂ), (∀ j, Continuous fun z => b z j) →
      Continuous (fun z => hform G (lineVec s z) (b z)) := fun b hb => by
    unfold hform
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hw i).mul ((Complex.continuous_conj).comp (hb j))).mul continuous_const
  exact ((hh (fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) fun j => continuous_const).norm.pow 2).measurable.div
    ((Complex.continuous_re.comp (hh _ hw)).mul continuous_const).measurable

theorem lintegral_fsDensity_indicator (s : Bool) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫⁻ x, (cosSq s G ⁻¹' A).indicator (fun x => ENNReal.ofReal (fsDensity s G x)) x =
      volume.restrict (Icc (0 : ℝ) 1) A := by
  rw [← GlobalTheory.T.cosine_square_pushforward_uniform G s hG, Measure.map_apply (measurable_cosSq s G) hA,
    withDensity_apply _ (measurable_cosSq s G hA), lintegral_indicator (measurable_cosSq s G hA)]
  rfl

theorem exists_map_cosSq_le (d : ℕ) (T : Set (V (d + 1))) (ρ : V (d + 1) → ℝ)
    (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (z₀ : V (d + 1))
    (hT : IsOpen T) (hz₀ : z₀ ∈ T) (hρ : ContinuousOn ρ T) (hG : ContinuousOn (fun z => G (base z)) T)
    (hp : ∀ z ∈ T, (G (base z)).PosDef) :
    ∃ N : Set (V (d + 1)), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ T ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map (fun z => cosSq s (G (base z)) (fib z))
          ((volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)) ≤
        C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨c, hc, hF⟩ := exists_lintegral_le_iterated d
  have hfs := continuousOn_fsDensity s hG hp
  have h0 := fsDensity_pos s (hp z₀ hz₀) (fib z₀)
  set R : ℝ := (|ρ z₀| + 1) / fsDensity s (G (base z₀)) (fib z₀) with hR
  have hR0 : 0 ≤ R := by positivity
  have hb : Continuous (fun z : V (d + 1) => base z) := by
    unfold base
    fun_prop
  let K : Set (Fin d → ℂ) := Metric.ball (base z₀) 1
  let N : Set (V (d + 1)) := (T ∩ (fun z => R * fsDensity s (G (base z)) (fib z) - ρ z) ⁻¹' Ioi 0) ∩
    (fun z => base z) ⁻¹' K
  have hN : IsOpen N :=
    (((continuousOn_const.mul hfs).sub hρ).isOpen_inter_preimage hT isOpen_Ioi).inter
      (Metric.isOpen_ball.preimage hb)
  have hNT : N ⊆ T := fun z hz => hz.1.1
  refine ⟨N, hN, ⟨⟨hz₀, ?_⟩, Metric.mem_ball_self one_pos⟩, hNT, c * (ENNReal.ofReal R * volume K),
    ENNReal.mul_ne_top hc (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne), ?_⟩
  · show 0 < R * fsDensity s (G (base z₀)) (fib z₀) - ρ z₀
    rw [hR, div_mul_cancel₀ _ h0.ne']
    linarith [le_abs_self (ρ z₀)]
  set f : V (d + 1) → ℝ := fun z => cosSq s (G (base z)) (fib z) with hf
  have hf' : Measurable (N.piecewise f 0) :=
    ((continuousOn_cosSq s hG hp).mono hNT).measurable_piecewise continuousOn_const hN.measurableSet
  have hae : f =ᵐ[(volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)] N.piecewise f 0 := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [ae_restrict_mem hN.measurableSet] with z hz
    rw [Set.piecewise_eq_of_mem _ _ _ hz]
  rw [Measure.map_congr hae, Measure.le_iff]
  intro A hA
  rw [Measure.map_apply hf' hA, withDensity_apply _ (hf' hA), Measure.restrict_restrict (hf' hA),
    ← lintegral_indicator ((hf' hA).inter hN.measurableSet), Measure.smul_apply, smul_eq_mul]
  refine (hF _).trans ?_
  rw [mul_assoc c]
  refine mul_le_mul_right ?_ _
  have key : ∀ b : Fin d → ℂ, ∫⁻ x : ℂ, (N.piecewise f 0 ⁻¹' A ∩ N).indicator (fun z => ENNReal.ofReal (ρ z))
      ((splitLin d).symm (b, x)) ≤
      K.indicator (fun _ => ENNReal.ofReal R * volume.restrict (Icc (0 : ℝ) 1) A) b := by
    intro b
    have hbase : ∀ x, base ((splitLin d).symm (b, x)) = b := fun x =>
      congrArg Prod.fst ((splitLin d).apply_symm_apply (b, x))
    have hfib : ∀ x, fib ((splitLin d).symm (b, x)) = x := fun x =>
      congrArg Prod.snd ((splitLin d).apply_symm_apply (b, x))
    by_cases hex : ∃ x, (splitLin d).symm (b, x) ∈ N
    · obtain ⟨x₀, hx₀⟩ := hex
      have hbK : b ∈ K := by
        have := hx₀.2
        rwa [mem_preimage, hbase] at this
      have hGb : (G b).PosDef := by
        have := hp _ (hNT hx₀)
        rwa [hbase] at this
      rw [indicator_of_mem hbK, ← lintegral_fsDensity_indicator s hGb hA,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      by_cases hx : (splitLin d).symm (b, x) ∈ N.piecewise f 0 ⁻¹' A ∩ N
      · have h1 : x ∈ cosSq s (G b) ⁻¹' A := by
          have := hx.1
          rw [mem_preimage, Set.piecewise_eq_of_mem _ _ _ hx.2, hf] at this
          simpa only [hbase, hfib, mem_preimage] using this
        have h2 : 0 < R * fsDensity s (G b) x - ρ ((splitLin d).symm (b, x)) := by
          have := hx.2.1.2
          simpa only [mem_preimage, hbase, hfib, mem_Ioi] using this
        simp only [indicator_of_mem hx, indicator_of_mem h1]
        rw [← ENNReal.ofReal_mul hR0]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · simp only [indicator_of_notMem hx]
        exact zero_le
    · have : ∀ x : ℂ, (N.piecewise f 0 ⁻¹' A ∩ N).indicator (fun z => ENNReal.ofReal (ρ z))
          ((splitLin d).symm (b, x)) = 0 := fun x => indicator_of_notMem (fun h => hex ⟨x, h.2⟩) _
      simp only [this, lintegral_zero]
      exact zero_le
  refine (lintegral_mono key).trans (le_of_eq ?_)
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const]
  ring

end GlobalTheory.LineCos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFrobeniusCharP
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LemY

theorem map_frobenius_charP (p : ℕ) [Fact p.Prime] {S K : Type} [CommRing S] [CommRing K] [CharP S p] [CharP K p]
    (f : S →+* K) (x : WittVector p S) :
    WittVector.map f (WittVector.frobenius x) = WittVector.frobenius (WittVector.map f x) := by
  ext n
  simp [WittVector.coeff_frobenius_charP, WittVector.map_coeff, map_pow]

theorem map_mulVec_witt (p : ℕ) [Fact p.Prime] {S K : Type} [CommRing S] [CommRing K] (f : S →+* K) (d : ℕ)
    (U : Matrix (Fin d) (Fin d) (WittVector p S)) (B : Fin d → WittVector p S) (i : Fin d) :
    WittVector.map f ((U *ᵥ B) i) = (U.map (WittVector.map f) *ᵥ (fun j => WittVector.map f (B j))) i := by
  rw [RingHom.map_mulVec]; rfl

theorem step : ∀ (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p] [PerfectRing S p] [Field K] [Algebra S K] [IsFractionRing S K] [CharP K p] [PerfectRing K p] (d : ℕ) (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Z : Fin d → WittVector p S) (Y : Fin d → WittVector p K), (∀ i, WittVector.frobenius (Y i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y) i + WittVector.map (algebraMap S K) (Z i)) → ∃ (B Z₁ : Fin d → WittVector p S) (Y₁ : Fin d → WittVector p K), (∀ i, Y i = WittVector.map (algebraMap S K) (B i) + (p : WittVector p K) * Y₁ i) ∧ ∀ i, WittVector.frobenius (Y₁ i) = (U.map (WittVector.map (algebraMap S K)) *ᵥ Y₁) i + WittVector.map (algebraMap S K) (Z₁ i) := by
  intro p _ S K _ _ _ _ _ _ _ _ _ _ d U Z Y hY
  set f : S →+* K := algebraMap S K with hf
  set F : WittVector p S →+* WittVector p K := WittVector.map f with hF

  have h0 : ∀ i, (Y i).coeff 0 ^ p = ((U.map WittVector.constantCoeff).map f *ᵥ fun j => (Y j).coeff 0) i
      + f ((Z i).coeff 0) := by
    intro i
    have := congrArg (fun w => w.coeff 0) (hY i)
    rw [WittVector.coeff_frobenius_charP] at this
    rw [this]
    have e1 := RingHom.map_mulVec (WittVector.constantCoeff (p := p) (R := K)) (U.map F) Y i
    change WittVector.constantCoeff ((U.map F *ᵥ Y) i + F (Z i)) = _
    rw [map_add, e1]
    simp [Matrix.map_map, Function.comp_def, WittVector.constantCoeff_apply, hF, WittVector.map_coeff]
  have hb : ∀ i, ∃ c, f c = (Y i).coeff 0 := fun i =>
    RingHom.mem_range.mp (GlobalTheory.T.artin_schreier_system_integral p S K d (U.map WittVector.constantCoeff) (fun i => (Z i).coeff 0)
      (fun i => (Y i).coeff 0) h0 i)
  choose b hbY using hb
  set B : Fin d → WittVector p S := fun i => WittVector.teichmuller p (b i) with hB
  have hdiff : ∀ i, ∃ c, Y i - F (B i) = (p : WittVector p K) * c := by
    intro i
    have hm : Y i - F (B i) ∈ Ideal.span {(p : WittVector p K)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
        WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, hB, hF, WittVector.map_teichmuller,
        WittVector.teichmuller_coeff_zero, hbY, sub_self]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose Y₁ hY₁ using hdiff
  have hYfun : Y = (fun j => F (B j)) + (p : WittVector p K) • Y₁ := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hY₁ j
  set Wv : Fin d → WittVector p S := fun i => (U *ᵥ B) i + Z i - WittVector.frobenius (B i) with hWv
  have hWimg : ∀ i, F (Wv i) = (p : WittVector p K) * (WittVector.frobenius (Y₁ i) - (U.map F *ᵥ Y₁) i) := by
    intro i
    have h := hY i
    have e2 : (U.map F *ᵥ Y) i = (U.map F *ᵥ fun j => F (B j)) i + (p : WittVector p K) * (U.map F *ᵥ Y₁) i := by
      rw [hYfun, Matrix.mulVec_add, Matrix.mulVec_smul]
      rfl
    have e3 : Y i = F (B i) + (p : WittVector p K) * Y₁ i := by linear_combination hY₁ i
    rw [e2, e3, map_add, map_mul, map_natCast] at h
    have e4 : F (Wv i) = (U.map F *ᵥ fun j => F (B j)) i + F (Z i) - WittVector.frobenius (F (B i)) := by
      rw [hWv]
      simp only
      rw [map_sub, map_add, map_mulVec_witt, hF, map_frobenius_charP]
    rw [e4]
    linear_combination (-1 : WittVector p K) * h
  have hW0 : ∀ i, (Wv i).coeff 0 = 0 := by
    intro i
    apply IsFractionRing.injective S K
    rw [map_zero]
    have h1 : F (Wv i) ∈ Ideal.span {(p : WittVector p K)} :=
      Ideal.mem_span_singleton'.mpr ⟨_, by rw [hWimg i, mul_comm]⟩
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, hF, WittVector.map_coeff] at h1
    exact h1
  have hZ : ∀ i, ∃ c, c * (p : WittVector p S) = Wv i := fun i =>
    Ideal.mem_span_singleton'.mp ((WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr (hW0 i))
  choose Z₁ hZ₁ using hZ
  refine ⟨B, Z₁, Y₁, fun i => by linear_combination hY₁ i, fun i => ?_⟩
  have hp : (p : WittVector p K) ≠ 0 := WittVector.p_nonzero p K
  apply mul_left_cancel₀ hp
  have := hWimg i
  rw [← hZ₁ i, map_mul, map_natCast] at this
  linear_combination -this

end GlobalTheory.LemY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalField
section
noncomputable section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped NNReal ENNReal

namespace GlobalTheory.KSp

theorem map_linearEquiv_haar : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃ₗ[F] V), μ.map T = (distribHaarChar F (LinearEquiv.det T))⁻¹ • μ := by
  intro F _ _ _ _ _ V _ _ _ _ _ _ _ μ _ T
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  set n := Module.finrank F V
  set b := Module.finBasis F V
  set e : V ≃ₗ[F] (Fin n → F) := b.equivFun
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup F V
  have hec : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

  let E : V ≃L[F] (Fin n → F) := { e with continuous_toFun := hec, continuous_invFun := hes }
  let Em : V ≃ᵐ (Fin n → F) := E.toHomeomorph.toMeasurableEquiv
  have hEm : (Em : V → Fin n → F) = e := rfl
  have hEms : (Em.symm : (Fin n → F) → V) = e.symm := rfl
  let P : Measure (Fin n → F) := Measure.pi fun _ => (Measure.addHaar : Measure F)
  set X := μ.map Em with hX
  haveI : X.IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  set M := LinearMap.toMatrix b b T.toLinearMap
  have hM : ∀ y, M.mulVec (e y) = e (T y) := fun y => by
    simp [M, e, LinearMap.toMatrix_mulVec_repr]
  have hdet : ((LinearEquiv.det T : Fˣ) : F) = M.det := by
    simp [M, LinearMap.det_toMatrix]
  set d := distribHaarChar F (LinearEquiv.det T)
  have key : (d : ℝ≥0∞) • P.map M.mulVec = P :=
    GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure F) M (LinearEquiv.det T) hdet
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by simpa using (distribHaarChar_pos (A := F) (g := LinearEquiv.det T)).ne'
  have hPM : P.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • P := by
    conv_rhs => rw [← key]
    rw [smul_smul, ENNReal.coe_inv (by simpa using hd0), ENNReal.inv_mul_cancel hd0 ENNReal.coe_ne_top,
      one_smul]
  have hXP : X = (Measure.addHaarScalarFactor X P : ℝ≥0∞) • P := Measure.isAddLeftInvariant_eq_smul X P
  have hmv : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hXM : X.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • X := by
    rw [hXP, Measure.map_smul, hPM, smul_comm]
  have hμ : μ = X.map Em.symm := by rw [hX, Measure.map_map Em.symm.measurable Em.measurable]; simp
  have hcomp : (T : V → V) ∘ Em.symm = Em.symm ∘ M.mulVec := by
    funext x
    show T (e.symm x) = e.symm (M.mulVec x)
    apply e.injective
    rw [← hM, e.apply_symm_apply, e.apply_symm_apply]
  have hTm : Measurable (T : V → V) := by
    have : Continuous (T : V → V) := IsModuleTopology.continuous_of_linearMap T.toLinearMap
    exact this.measurable
  calc μ.map T = (X.map Em.symm).map T := by rw [← hμ]
    _ = X.map ((T : V → V) ∘ Em.symm) := Measure.map_map hTm Em.symm.measurable
    _ = X.map (Em.symm ∘ M.mulVec) := by rw [hcomp]
    _ = (X.map M.mulVec).map Em.symm := (Measure.map_map Em.symm.measurable hmv).symm
    _ = (d⁻¹ : ℝ≥0) • μ := by rw [hXM, Measure.map_smul, ← hμ]; rfl

end GlobalTheory.KSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfMonic
section
open Polynomial

namespace GlobalTheory.MonicRootRange

theorem isAlgClosed_fractionRing (T : Type) [CommRing T] [IsDomain T]
    (h : GlobalTheory.LocAcyc.AbsIntClosed T) : IsAlgClosed (FractionRing T) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  set f := algebraMap T (FractionRing T)
  have hinj : Function.Injective f := IsFractionRing.injective T (FractionRing T)
  have hb0 : f b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hsmul : (b • p : (FractionRing T)[X]) = C (f b) * p := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  have hn : 1 ≤ p.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  have hdeg : q.natDegree = p.natDegree := by
    have := congrArg natDegree hq
    rwa [natDegree_map_eq_of_injective hinj, hsmul, natDegree_C_mul hb0] at this
  have hq0 : q ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hdeg; omega
  have hc0 : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hinj).mpr (leadingCoeff_ne_zero.mpr hq0)
  obtain ⟨w, hw⟩ := h q.integralNormalization (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  refine ⟨f w / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (hdeg ▸ hn) f (f w / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hc0, eval₂_at_apply, hw, map_zero] at key
  have h2 : q.eval₂ f (f w / f q.leadingCoeff) = 0 :=
    (mul_eq_zero.mp key.symm).resolve_left (pow_ne_zero _ hc0)
  rw [← eval_map, hq, hsmul, eval_mul, eval_C] at h2
  exact (mul_eq_zero.mp h2).resolve_left hb0

end GlobalTheory.MonicRootRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
section
open ValuativeRel

noncomputable section

namespace GlobalTheory.UnfoldLoss

open GlobalTheory.SplitFlip GlobalTheory.FunObj

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def varLat (G : Grid k) (ϖ : kˣ) (n : ℕ) : AddSubgroup (Vars G) where
  carrier := {e | ∀ j r, valuation k (e j r) ≤ valuation k ((ϖ ^ n : kˣ) : k)}
  zero_mem' := fun j r => by
    show valuation k 0 ≤ _
    simp
  add_mem' := fun {a b} ha hb j r => (Valuation.map_add _ _ _).trans (max_le (ha j r) (hb j r))
  neg_mem' := fun {a} ha j r => by
    show valuation k (-(a j r)) ≤ _
    rw [Valuation.map_neg]
    exact ha j r

def varCount (G : Grid k) : ℕ :=
  ∑ j : Fin (G.m - 1), Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)))

end GlobalTheory.UnfoldLoss
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoQuotientPowFreeOverRegularLocalRingStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modDepthGE_two_quotient_pow_free_over_regularLocalRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ≠ 0 → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B] [Nontrivial B] (k : ℕ), 1 ≤ k → ReciprocityTheory.CA.ModDepthGE R (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) 2 := by
  first | (exact @GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing) | (exact GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing) | (intros; apply GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularFormPolynomialE4E6
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

open ReciprocityTheory.PGsh in

theorem isMF_eq_sum_monomials :
    ∀ (w : ℕ) (F : ℍ → ℂ), IsMF w F → ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ),
      (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
        ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro w F hF
  obtain ⟨g, hg⟩ := hF
  have hm := coe_mem_monoSpanF w g
  rw [monoSpanF, Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨(monoIdx w).image fun a => (a, monoB w a),
    fun p => if h : p.1 ∈ monoIdx w then c ⟨p.1, h⟩ else 0, ?_, fun τ => ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact monoIdx_wt ha
  · rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h), ← hg τ, ← hc,
      Finset.sum_apply, ← Finset.sum_coe_sort (monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coe_monoW a.2]
    simp [a.2]

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFreeOfRegularOfFreeQuotientLocalStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R), f ∈ maximalIdeal R → IsSMulRegular A f → Module.Free (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) → Module.Free R A := by
  first | exact @GlobalTheory.AnnRegSeq.free_of_free_quotient_map | exact GlobalTheory.AnnRegSeq.free_of_free_quotient_map | (intros; apply GlobalTheory.AnnRegSeq.free_of_free_quotient_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgCStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed : ∀ (D : Type) [CommRing D] [IsDomain D], AIC D ↔ (IsIntegrallyClosed D ∧ IsAlgClosed (FractionRing D)) := by
  first | (exact @GlobalTheory.AICIff.aic_iff) | (exact GlobalTheory.AICIff.aic_iff) | (intros; apply GlobalTheory.AICIff.aic_iff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFiniteStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_linearEquiv_of_pi_fin_pow_finite : ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N] (l : ℕ), 0 < l → Nonempty ((Fin l → M) ≃ₗ[R] (Fin l → N)) → Nonempty (M ≃ₗ[R] N) := by
  first | (exact @GlobalTheory.PowCancel.cancel_pow) | (exact GlobalTheory.PowCancel.cancel_pow) | (intros; apply GlobalTheory.PowCancel.cancel_pow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdL
section
namespace GlobalTheory.DiagVol

def ordL {n : Type*} (c : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => c + 1) (fun i => 2 * (i.val + 1))

end GlobalTheory.DiagVol
end

