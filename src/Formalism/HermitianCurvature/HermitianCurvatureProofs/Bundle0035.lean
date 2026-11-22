import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousOnG2SymmetricInterval
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.CompositeFormulaLevelZero

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DiscMeanValue
section
open MeasureTheory Set Metric
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume

lemma J_all {u : ℝ} (hu : 0 < u) :
    ‖∫ t in (-1 : ℝ)..1, (g0 t : ℂ) * ee u t‖ ≤ 10 / (u * Real.sqrt u) := by
  rcases le_or_gt 1 u with h | h
  · exact J_bound h
  · have hb : ‖∫ t in (-1 : ℝ)..1, (g0 t : ℂ) * ee u t‖ ≤ 1 * |1 - (-1 : ℝ)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t _
      rw [norm_mul]
      have h1 : ‖(g0 t : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, show g0 t = Real.sqrt (1 - t ^ 2) from rfl,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (1 - t ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
          _ = 1 := Real.sqrt_one
      have h2 : ‖ee u t‖ = 1 := by
        simp only [ee]
        exact Complex.norm_exp_I_mul_ofReal _
      rw [h2, mul_one]
      exact h1
    have hsu : Real.sqrt u ≤ 1 := by
      calc Real.sqrt u ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h.le
        _ = 1 := Real.sqrt_one
    have hpos : 0 < u * Real.sqrt u := mul_pos hu (Real.sqrt_pos.mpr hu)
    have hle : u * Real.sqrt u ≤ 1 := by nlinarith [Real.sqrt_nonneg u]
    have h10 : 2 ≤ 10 / (u * Real.sqrt u) := by
      rw [le_div_iff₀ hpos]
      linarith
    have e2 : (1 : ℝ) * |1 - (-1 : ℝ)| = 2 := by norm_num
    linarith

lemma vol_sq_lt (s : ℝ) : volume {b : ℝ | b ^ 2 < s} = ENNReal.ofReal (2 * Real.sqrt s) := by
  have hset : {b : ℝ | b ^ 2 < s} = Ioo (-Real.sqrt s) (Real.sqrt s) := by
    ext b
    simp only [mem_setOf_eq, mem_Ioo]
    exact Real.sq_lt
  rw [hset, Real.volume_Ioo]
  congr 1
  ring

lemma disc_fubini {R ρ : ℝ} (hR : 0 < R) :
    ∫ z in ball (0 : ℂ) R, ee ρ z.re = ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t := by
  classical
  set e := Complex.measurableEquivRealProd with he
  have hpres : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod
  set F : ℂ → ℂ := (ball (0 : ℂ) R).indicator (fun z => ee ρ z.re) with hF
  set S : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 < R ^ 2} with hS
  have hmemS : ∀ p : ℝ × ℝ, e.symm p ∈ ball (0 : ℂ) R ↔ p ∈ S := by
    intro p
    rw [Complex.measurableEquivRealProd_symm_apply, mem_ball, dist_zero_right,
      Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_lt' hR]
    rfl
  have hFG : ∀ p : ℝ × ℝ, F (e.symm p) = S.indicator (fun q => ee ρ q.1) p := by
    intro p
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, hF, Set.indicator_of_mem ((hmemS p).mpr hp),
        Complex.measurableEquivRealProd_symm_apply]
    · rw [Set.indicator_of_notMem hp, hF,
        Set.indicator_of_notMem (fun h => hp ((hmemS p).mp h))]
  have hcont : Continuous (fun z : ℂ => ee ρ z.re) := by
    unfold ee
    fun_prop
  have hFint : Integrable F := by
    rw [hF, integrable_indicator_iff measurableSet_ball]
    refine Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne
      hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [ee]
    rw [Complex.norm_exp_I_mul_ofReal]
  have hGint : Integrable (S.indicator (fun q : ℝ × ℝ => ee ρ q.1)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    have h1 : (fun p => F (e.symm p)) = S.indicator (fun q : ℝ × ℝ => ee ρ q.1) := funext hFG
    rw [← h1]
    exact (hpres.integrable_comp_emb e.symm.measurableEmbedding).mpr hFint
  have hSmeas : ∀ a : ℝ, MeasurableSet {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2} := fun a =>
    measurableSet_lt (by fun_prop) measurable_const
  calc ∫ z in ball (0 : ℂ) R, ee ρ z.re = ∫ z, F z := (integral_indicator measurableSet_ball).symm
    _ = ∫ p, F (e.symm p) := (hpres.integral_comp' F).symm
    _ = ∫ p, S.indicator (fun q : ℝ × ℝ => ee ρ q.1) p ∂(volume.prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact integral_congr_ae (Filter.Eventually.of_forall hFG)
    _ = ∫ a, ∫ b, S.indicator (fun q : ℝ × ℝ => ee ρ q.1) (a, b) := integral_prod _ hGint
    _ = ∫ a, ((2 * Real.sqrt (R ^ 2 - a ^ 2) : ℝ) : ℂ) * ee ρ a := by
        congr 1
        funext a
        have hin : (fun b => S.indicator (fun q : ℝ × ℝ => ee ρ q.1) (a, b)) =
            {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2}.indicator (fun _ => ee ρ a) := by
          funext b
          by_cases hb : b ^ 2 < R ^ 2 - a ^ 2
          · rw [Set.indicator_of_mem (show b ∈ {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2} from hb),
              Set.indicator_of_mem (show (a, b) ∈ S from show a ^ 2 + b ^ 2 < R ^ 2 by linarith)]
          · rw [Set.indicator_of_notMem (show b ∉ {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2} from hb),
              Set.indicator_of_notMem (show (a, b) ∉ S from fun h => hb (by
                have h' : a ^ 2 + b ^ 2 < R ^ 2 := h
                linarith))]
        rw [hin, integral_indicator_const _ (hSmeas a), measureReal_def, vol_sq_lt,
          ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    _ = ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t := by
        rw [intervalIntegral.integral_of_le (by linarith),
          setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro a ha
        have h2 : R ^ 2 - a ^ 2 ≤ 0 := by
          simp only [mem_Ioc, not_and_or, not_lt, not_le] at ha
          rcases ha with h | h <;> nlinarith
        rw [Real.sqrt_eq_zero'.mpr h2]
        simp

lemma disc_scale {R ρ : ℝ} (hR : 0 < R) :
    ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t =
      ((2 * R ^ 2 : ℝ) : ℂ) * ∫ s in (-1 : ℝ)..1, (g0 s : ℂ) * ee (ρ * R) s := by
  have hR0 : R ≠ 0 := hR.ne'
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR0
  have hsq : ∀ s : ℝ, Real.sqrt (1 - s ^ 2) = Real.sqrt (R ^ 2 - (R * s) ^ 2) / R := by
    intro s
    rw [show R ^ 2 - (R * s) ^ 2 = R ^ 2 * (1 - s ^ 2) by ring, Real.sqrt_mul (sq_nonneg R),
      Real.sqrt_sq hR.le, mul_div_cancel_left₀ _ hR0]
  have hee : ∀ s : ℝ, ee (ρ * R) s = ee ρ (R * s) := by
    intro s
    simp only [ee]
    congr 2
    push_cast
    ring
  have key : (fun s : ℝ => (g0 s : ℂ) * ee (ρ * R) s) =
      fun s => ((Real.sqrt (R ^ 2 - (R * s) ^ 2) / R : ℝ) : ℂ) * ee ρ (R * s) := by
    funext s
    rw [hee, show g0 s = Real.sqrt (1 - s ^ 2) from rfl, hsq]
  have hint : (∫ s in (-1 : ℝ)..1, (g0 s : ℂ) * ee (ρ * R) s) =
      ∫ s in (-1 : ℝ)..1, ((Real.sqrt (R ^ 2 - (R * s) ^ 2) / R : ℝ) : ℂ) * ee ρ (R * s) := by
    rw [key]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (fun t : ℝ => ((Real.sqrt (R ^ 2 - t ^ 2) / R : ℝ) : ℂ) * ee ρ t) hR0
  rw [hint, hcomp, mul_neg, mul_one, Complex.real_smul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  push_cast
  field_simp

end Formalism.FourierDecayAlt.P.DiscFubiniVolume

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.DiscFubiniVolume

theorem disc_mean_value : C6.DiscMean := by
  intro β hβ
  refine ⟨20 / Real.pi * ‖β‖ ^ (-(3 / 2 : ℝ)), fun ξ x₀ R hξ hR => ?_⟩
  classical
  set γ := β * ξ with hγ
  have hγ0 : γ ≠ 0 := mul_ne_zero hβ hξ
  have hγn : 0 < ‖γ‖ := norm_pos_iff.mpr hγ0
  set c : ℝ := ‖γ‖ with hc
  have hpsi : ∀ x : ℂ, G.psi β (ξ * x) = Complex.exp (Complex.I * ((γ * x).re : ℂ)) := by
    intro x
    simp only [G.psi, hγ, mul_assoc]
  have htr : ∫ x in ball x₀ R, G.psi β (ξ * x) =
      Complex.exp (Complex.I * ((γ * x₀).re : ℂ)) *
        ∫ w in ball (0 : ℂ) R, Complex.exp (Complex.I * ((γ * w).re : ℂ)) := by
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
      ← integral_const_mul, ← integral_add_left_eq_self _ x₀]
    congr 1
    funext w
    by_cases hw : w ∈ ball (0 : ℂ) R
    · have hw' : x₀ + w ∈ ball x₀ R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        simpa using hw
      rw [Set.indicator_of_mem hw', Set.indicator_of_mem hw, hpsi, mul_add, Complex.add_re,
        Complex.ofReal_add, mul_add, Complex.exp_add]
    · have hw' : x₀ + w ∉ ball x₀ R := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        simpa using hw
      rw [Set.indicator_of_notMem hw', Set.indicator_of_notMem hw, mul_zero]
  set u : Circle := Circle.exp (-Complex.arg γ) with hu
  have hrot : ∀ v : ℂ, γ * (rotation u v) = (c : ℂ) * v := by
    intro v
    rw [rotation_apply, hu, Circle.coe_exp]
    nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I γ]
    calc (↑‖γ‖ * Complex.exp (↑γ.arg * Complex.I)) * (Complex.exp (↑(-γ.arg) * Complex.I) * v)
        = ↑‖γ‖ * (Complex.exp (↑γ.arg * Complex.I) * Complex.exp (↑(-γ.arg) * Complex.I)) * v := by
          ring
      _ = ↑‖γ‖ * v := by
          rw [← Complex.exp_add, Complex.ofReal_neg, neg_mul, add_neg_cancel, Complex.exp_zero,
            mul_one]
  have hrotI : ∫ w in ball (0 : ℂ) R, Complex.exp (Complex.I * ((γ * w).re : ℂ)) =
      ∫ v in ball (0 : ℂ) R, ee c v.re := by
    have hL := LinearIsometryEquiv.measurePreserving (rotation u)
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
      ← hL.integral_comp (rotation u).toHomeomorph.measurableEmbedding]
    congr 1
    funext v
    have hn : rotation u v ∈ ball (0 : ℂ) R ↔ v ∈ ball (0 : ℂ) R := by
      simp only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
    by_cases hv : v ∈ ball (0 : ℂ) R
    · rw [Set.indicator_of_mem (hn.mpr hv), Set.indicator_of_mem hv, hrot, Complex.re_ofReal_mul]
      rfl
    · rw [Set.indicator_of_notMem (fun h => hv (hn.mp h)), Set.indicator_of_notMem hv]
  have hvol : (volume (ball x₀ R)).toReal = R ^ 2 * Real.pi := by
    rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le]
    simp
  have hJ := J_all (u := c * R) (by positivity)
  have hx : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have hy : 0 < R * ‖ξ‖ := mul_pos hR (norm_pos_iff.mpr hξ)
  have hcR : c * R = ‖β‖ * (R * ‖ξ‖) := by
    rw [hc, hγ, norm_mul]
    ring
  have hpow : c * R * Real.sqrt (c * R) = (‖β‖ * (R * ‖ξ‖)) ^ (3 / 2 : ℝ) := by
    rw [hcR, Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity), Real.rpow_one]
  have hkey : 10 / (c * R * Real.sqrt (c * R)) =
      10 * (‖β‖ ^ (-(3 / 2 : ℝ)) * (R * ‖ξ‖) ^ (-(3 / 2 : ℝ))) := by
    rw [hpow, ← Real.mul_rpow hx.le hy.le, Real.rpow_neg (by positivity), div_eq_mul_inv]
  simp only [C6.meanDisc]
  rw [htr, hrotI, disc_fubini hR, disc_scale hR, hvol]
  calc _ = 2 / Real.pi * ‖∫ s in (-1 : ℝ)..1, (g0 s : ℂ) * ee (c * R) s‖ := by
        have hn1 : ‖Complex.exp (Complex.I * ((γ * x₀).re : ℂ))‖ = 1 :=
          Complex.norm_exp_I_mul_ofReal _
        have hn2 : ‖((2 * R ^ 2 : ℝ) : ℂ)‖ = 2 * R ^ 2 := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hn3 : ‖(R ^ 2 * Real.pi)⁻¹‖ = (R ^ 2 * Real.pi)⁻¹ :=
          Real.norm_of_nonneg (by positivity)
        rw [norm_smul, norm_mul, norm_mul, hn1, hn2, hn3]
        have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
        field_simp
    _ ≤ 2 / Real.pi * (10 / (c * R * Real.sqrt (c * R))) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = 20 / Real.pi * ‖β‖ ^ (-(3 / 2 : ℝ)) * (R * ‖ξ‖) ^ (-(3 / 2 : ℝ)) := by
        rw [hkey]
        ring

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EqOfContinuousOffZero
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

theorem isClosed_nonneg_complex : IsClosed {z : ℂ | 0 ≤ z} := by
  have h : {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.le_def, Complex.zero_re, Complex.zero_im]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  rw [h]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq Complex.continuous_im continuous_const)

theorem integral_nonneg_complex {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ)
    (h : ∀ a, 0 ≤ f a) : 0 ≤ ∫ a, f a ∂ν := by
  have hre : ∀ a, f a = ((f a).re : ℂ) := fun a => by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      exact ((Complex.le_def.mp (h a)).2).symm
  have hf : (fun a => f a) = fun a => ((f a).re : ℂ) := funext hre
  rw [hf]
  first
  | rw [integral_complex_ofReal]
  | rw [integral_ofReal]
  | rw [← RCLike.ofReal_eq_complex_ofReal, integral_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun a => (Complex.le_def.mp (h a)).1)

theorem continuous_fsv (s : ℂ) : Continuous (fsv s) := by
  unfold fsv
  exact ((continuous_const.mul continuous_id).sub
    (continuous_const.mul Complex.continuous_conj)).cexp

theorem nonneg_of_continuous {φ : ℂ → ℂ} (hc : Continuous φ) (h : ∀ t, t ≠ 0 → 0 ≤ φ t) :
    ∀ t, 0 ≤ φ t := by
  have hcl : IsClosed {t | 0 ≤ φ t} := isClosed_nonneg_complex.preimage hc
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆ {t | 0 ≤ φ t} := fun t ht => h t ht
  have hcl2 := hcl.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at hcl2
  intro t
  exact hcl2 (Set.mem_univ t)

theorem eq_of_continuous_off_zero {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, t ≠ 0 → f t = g t) : f = g := hf.ext_on (dense_compl_singleton (0 : ℂ)) hg (fun t ht => h t ht)

theorem update_mem_OmX {m : ℕ} {c : Fin m → ℂ} (hc : c ∈ OmX m) (l : Fin m) {t : ℂ} (ht : t ≠ 0) :
    Function.update c l t ∈ OmX m := by
  intro j
  rcases eq_or_ne j l with rfl | hj
  · simpa using ht
  · rw [Function.update_of_ne hj]
    exact hc j

theorem nonneg_all_levels {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hTI : TopIdent (S := S) P z z' π π' μ L st K l0) (hTN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hSI : SliceIn (S := S) P z z' π π' L st K l0) (hSD : StepDens (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) :
    ∀ (n : ℕ) (i : Fin (P.r + 1)), i.val + n = P.r → ∀ c ∈ OmX P.r,
      ∀ x : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → 0 ≤ RRform L st μ i w x x c := by
  intro n
  induction n with
  | zero =>
    intro i hi c hc x hx
    have hi' : i = Fin.last P.r := Fin.ext (by simpa using hi)
    subst hi'
    rw [(hTI w hw x x hx hx c hc).2]
    exact integral_nonneg_complex μ _ (fun g => hTN w hw x hx c hc (Matrix.of g))
  | succ n ih =>
    intro i hi c hc x hx
    have hlt : i.val < P.r := by omega
    obtain ⟨l, rfl⟩ : ∃ l : Fin P.r, l.castSucc = i := ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    obtain ⟨φ, hφc, hφ, -, hint⟩ := hSD w hw l x x hx hx c hc
    rw [← hint]
    apply integral_nonneg_complex
    apply nonneg_of_continuous hφc
    intro t ht
    rw [hφ t ht]
    unfold ph
    apply mul_nonneg
    · exact Complex.zero_le_real.mpr (by positivity)
    · have hn : (l.succ).val + n = P.r := by
        simp only [Fin.coe_castSucc] at hi
        simp only [Fin.val_succ]
        omega
      exact ih l.succ hn _ (update_mem_OmX hc l ht) _ (hSI w hw l x hx)

theorem thmPFromStepsAll : ThmPFromStepsAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st K l0
  intro hTI hTN hTT hSI hSD hST hFS w hw
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy c hc
    refine ⟨(hTI w hw x y hx hy c hc).1, ?_, ?_⟩
    · intro s Wv Wv' h1 h2
      obtain ⟨hK, hD⟩ := hTT w hw s Wv Wv' h1 h2 x y hx hy c hc
      rw [(hTI w hw _ y hK hy c hc).2]
      congr 1
      funext g
      rw [hD]
    · exact nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw 0
        (Fin.last P.r) (by simp) c hc x hx
  · intro l x y hx hy c hc
    obtain ⟨φ, hφc, hφ, hC, -⟩ := hSD w hw l x y hx hy c hc
    refine ⟨φ, hφc, hφ, hC, ?_⟩
    intro s Wv Wv' h1 h2
    obtain ⟨hK, hT⟩ := hST w hw l s Wv Wv' h1 h2 x y hx hy c hc
    obtain ⟨ψ, hψc, hψ, -, hψint⟩ := hSD w hw l _ y hK hy c hc
    rw [← hψint]
    congr 1
    apply eq_of_continuous_off_zero ((continuous_fsv s).mul hφc) hψc
    intro t ht
    show fsv s t * φ t = ψ t
    rw [hψ t ht, hT t ht, hφ t ht]
  · intro i c hc
    refine ⟨hFS w hw i c hc, ?_⟩
    intro x hx
    have hxK : InK (K i) x := fun a => (Submodule.mem_pi.mp hx) a (Set.mem_univ a)
    exact nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw (P.r - i.val) i
      (by omega) c hc x hxK

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec
section
open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

lemma mul_mem (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x)
    (Φ : RadSp k r z z' π π') :
    (fun c g => m (c, g) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) ∈ RadSp k r z z' π π' := by
  have hΦm : (Φ : Fn k r (Wq →L[ℂ] Wp)) ∈ RadSp k r z z' π π' := Φ.2
  obtain ⟨h0, hs, he⟩ := hΦm
  refine (show _ ∧ _ ∧ _ from ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩)
  · show m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0
    rw [h0 x hx, smul_zero]
  · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
    refine ⟨U, fun x => m x • F x, hU, hxU, hm.contDiffOn.smul hF, fun x hx hg => ?_⟩
    show m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = m x • F x
    rw [hΦ x hx hg]
  · show m (x.1, h * x.2 * h') • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 (h * x.2 * h') =
      (π h).comp ((m (x.1, x.2) • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2).comp (π' h'))
    rw [hinv x hx h hh h' hh', he x hx h hh h' hh']
    ext v
    simp

def mulOp (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x) :
    Module.End ℂ (RadSp k r z z' π π') where
  toFun Φ := ⟨_, mul_mem m hm hinv Φ⟩
  map_add' Φ Ψ := by
    ext c g v
    simp [smul_add]
  map_smul' a Φ := by
    ext c g v
    simp [smul_smul, mul_comm]

lemma mulOp_isMulOp (m : (Fin r → ℂ) × Mx k r → ℂ) (hm : ContDiff ℝ ∞ m)
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', m (x.1, h * x.2 * h') = m x) :
    multiplicationOperator (mulOp (π := π) (π' := π') m hm hinv) (fun c g => m (c, g)) := by
  intro _ _ _
  rfl

lemma contDiff_fsv (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hL : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul Complex.conjCLE.contDiff)
  exact Complex.contDiff_exp.comp hL

lemma contDiff_fsv_coord (l : Fin r) (s : ℂ) :
    ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => fsv s (x.1 l)) :=
  (contDiff_fsv s).comp (by fun_prop : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => x.1 l))

def hermLin (H : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℂ] ℂ where
  toFun g := herm H (g *ᵥ v) w
  map_add' g g' := by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
  map_smul' a g := by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul]

lemma contDiff_zeta : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => zeta k r z z' x.2) := by
  unfold zeta zetaL
  let Lc : Mx k r →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (hermLin (Hpk k r) (fvec k r z' (Fin.last r)) (fvec k r z (Fin.last r)))
  have h1 : ContDiff ℝ ∞ (fun g : Mx k r => Lc g) := (Lc.restrictScalars ℝ).contDiff
  exact h1.comp contDiff_snd

lemma herm_mulVec_mulVec (H h : Mx k r) (hh : hᴴ * H * h = H) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm H (h *ᵥ v) (h *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh]

lemma zeta_inv (g : Mx k r) (h h' : Mx k r) (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    zeta k r z z' (h * g * h') = zeta k r z z' g := by
  simp only [UWset, Set.mem_setOf_eq] at hh hh'
  obtain ⟨hU, hb, hz⟩ := hh
  obtain ⟨hU', hb', hz'⟩ := hh'
  simp only [UH, Set.mem_setOf_eq] at hU
  have hf' : h' *ᵥ fvec k r z' (Fin.last r) = fvec k r z' (Fin.last r) := by
    unfold fvec
    rw [dif_neg (by simp)]
    exact hz'
  have hf : h *ᵥ fvec k r z (Fin.last r) = fvec k r z (Fin.last r) := by
    unfold fvec
    rw [dif_neg (by simp)]
    exact hz
  unfold zeta zetaL
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf']
  conv_lhs => rw [← hf]
  exact herm_mulVec_mulVec _ _ hU _ _

end Wave

theorem waveCExists : WaveCExists := by
  intro Wp Wq _ _ _ _ k r z z' π π' l s
  exact ⟨mulOp (π := π) (π' := π') (fun x => fsv s (x.1 l)) (contDiff_fsv_coord l s)
    (fun _ _ _ _ _ _ => rfl), mulOp_isMulOp _ _ _⟩

theorem waveZExists : WaveZExists := by
  intro Wp Wq _ _ _ _ k r z z' π π' s
  exact ⟨mulOp (π := π) (π' := π') (fun x => fsv s (zeta k r z z' x.2))
    ((contDiff_fsv s).comp (contDiff_zeta (k := k) (r := r) (z := z) (z' := z')))
    (fun x _ h hh h' hh' => by
      show fsv s (zeta k r z z' (h * x.2 * h')) = fsv s (zeta k r z z' x.2)
      rw [zeta_inv _ _ _ hh hh']), mulOp_isMulOp _ _ _⟩

section Zero

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

end Zero

end Formalism.FourierDecayAlt.P5
end
end

