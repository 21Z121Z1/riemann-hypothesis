import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContinuousPointNormSqQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TopLeSpanBf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0004

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbel
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
  {I : Submodule ℤ (Vsp X.dim)}

theorem cab_core (hP : Ext.PackingCount) (hGT : Ext.GaussianTailBound) (hA : PropAStatement)
    (hS : GSupStatement) (hI : IsSplit P I) (c : ℕ) (hc : c ≤ DF) (σ : E →+* ℂ)
    (ξ : Vsp X.dim) (hξ1 : ‖ξ‖ = 1) (hξI : ∀ a ∈ I, Hf ξ a = 0)
 :
    ∃ s' ∈ X.Sec P.q 1,
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ‖ ≤ P.eps1 * c.factorial) ∧
      P.K6⁻¹ * X.l2 P.q s' ≤ (c.factorial : ℝ) ^ 2 := by
  classical
  have hK := Col.hK_of hI
  set η := Col.wmap (IR I) ξ with hη
  have hη1 : ‖η‖ ≤ 1 := by rw [hη, cab_norm_wmap_xi hK hξI, hξ1]
  have hq2 : (2 : ℝ) ≤ P.q := cab_q_ge P
  have hq2n : 2 ≤ P.q := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) < P.q := by linarith
  have hR0sq := P.hR0
  have hR0ne : P.R0 ≠ 0 := by intro h; rw [h] at hR0sq; norm_num at hR0sq
  have hR0pos : 0 < |P.R0| := abs_pos.mpr hR0ne
  have hlat := cab_YB_abs hI hP P.q
  have hGle : Col.gB (IR I) ≤ X.gA := cab_gB_le (IR I)
  have hGle' : (Col.gB (IR I) : ℝ) ≤ X.gA := by exact_mod_cast hGle
  have hcD : (c : ℝ) ≤ DF := by exact_mod_cast hc
  have h90 : 90 * ((Fintype.card (Fin (Col.gB (IR I))) : ℝ) + c) ≤ |P.R0| ^ 2 := by
    rw [sq_abs, Fintype.card_fin]; nlinarith [hR0sq.2]
  obtain ⟨β, hβ, hjet, hl2⟩ := hA (Fin (Col.gB (IR I))) (Col.YB hI hP P.q) P.q c |P.R0| P.hq (Col.YB_coc hI hP P.q) hR0pos hlat
    (by rw [sq_abs]; exact hR0sq.1) h90 (cabPoly η c) (cabPoly_deg η c)
  have hJ := cab_J_le η hη1 c P.q P.hq
  rw [Fintype.card_fin] at hJ
  have hl2' : (Col.YB hI hP P.q).l2 P.q β ≤ 6 * (c.factorial * (2 / (P.q * Real.pi)) ^ c * (2 / P.q) ^ Fintype.card (Fin (Col.gB (IR I)))) := by
    rw [Fintype.card_fin]; linarith
  have h90' : 90 * (Fintype.card (Fin (Col.gB (IR I))) : ℝ) ≤ |P.R0| ^ 2 := by
    have : (0 : ℝ) ≤ 90 * c := by positivity
    linarith
  set Bsq : ℝ := 12 * (5.12 : ℝ) ^ (Col.gB (IR I)) * c.factorial * (2 / (P.q * Real.pi)) ^ c with hBsq
  have hsup : ∀ t, (Col.YB hI hP P.q).ptN2 P.q β t ≤ Bsq := by
    intro t
    have := cab_sup hS (Col.YB hI hP P.q) P.q c hq2n |P.R0| hR0pos hlat h90' β hβ hl2' t
    rwa [Fintype.card_fin] at this
  have hBsq0 : 0 ≤ Bsq := by rw [hBsq]; positivity
  set B := Real.sqrt Bsq with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hBβ : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2 := by
    intro t; rw [hBdef, Real.sq_sqrt hBsq0]; exact hsup t
  have hT2 : ∀ c' v, ‖Col.Tc X I P.q β c' v‖ ≤ B * Real.exp (P.q * Real.pi * ‖v‖ ^ 2 / 2) *
      Real.exp (-(P.q * Real.pi * ‖Col.uc (IR I) v - Col.uc (IR I) (cabOut c' : Vsp X.dim)‖ ^ 2)) := by
    intro c' v
    have := Col.norm_Tc_le hI hB0 hBβ c' v
    rw [Col.uQ_out] at this
    refine this.trans (le_of_eq ?_)
    rw [show cabOut c' = Quotient.out c' from rfl]; ring_nf
  set s' : (Fin 1 → Vsp X.dim) → ℂ := Col.colS X I P.q β with hs'
  have hs'mem : s' ∈ X.Sec P.q 1 := Col.colS_mem hI hP hGT hB0 hBβ hβ
  have hsPd : Differentiable ℂ (Col.sP X I P.q β) := by
    have h1 : Differentiable ℂ s' := hs'mem.1
    let D : Vsp X.dim →L[ℂ] (Fin 1 → Vsp X.dim) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ _
    have : Col.sP X I P.q β = s' ∘ D := by funext v; rfl
    rw [this]; exact h1.comp D.differentiable
  refine ⟨s', hs'mem, ?_, ?_⟩
  · intro xs hxs
    set F0 := Col.F0 I P.q β with hF0
    set R : Vsp X.dim → ℂ := fun v => Col.sP X I P.q β v - F0 v with hR
    have hF0d : Differentiable ℂ F0 := differentiable_zeroModeLift I P.q β hβ.1
    have hRd : Differentiable ℂ R := hsPd.sub hF0d
    have hsplit : Col.sP X I P.q β = F0 + R := by funext v; simp [hR]
    have hd1 : d1 s' c xs = iteratedFDeriv ℂ c (Col.sP X I P.q β) 0 xs :=
      iteratedFDeriv_single_column (contDiff_of_differentiable_fd hsPd c) xs
    have hmain : iteratedFDeriv ℂ c F0 0 xs = (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ :=
      cab_main hK σ hξI β hβ.1 hjet F0 hF0d (fun v hv => zeroModeLift_on_part hI P.q β σ v hv) xs
        (fun k => (hxs k).1)
    have hadd : iteratedFDeriv ℂ c (Col.sP X I P.q β) 0 xs =
        iteratedFDeriv ℂ c F0 0 xs + iteratedFDeriv ℂ c R 0 xs := by
      rw [hsplit, iteratedFDeriv_add_apply (contDiff_of_differentiable_fd hF0d c).contDiffAt
        (contDiff_of_differentiable_fd hRd c).contDiffAt]
      rfl
    rw [hd1, hadd, hmain, add_sub_cancel_left]
    obtain ⟨g', hg', hs, hle⟩ := cab_sum_nz hP hGT hI
    have hbd := cab_R hI hP hGT hβ B hB0 (Col.summable_Tc hI hP hGT hB0 hBβ) hT2
    have htd := cab_tail_deriv R hRd c xs (fun k => (hxs k).2.le) P.q hq0 B hB0 _ hs hbd
    refine htd.trans ?_
    have hstep : B * ((P.q : ℝ) * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
        ∑' a : cabNZ X I, Real.exp (-(Real.pi / 2 * P.q *
          ‖Col.uc (IR I) (cabOut (a : Col.Qc X I) : Vsp X.dim)‖ ^ 2)) ≤
        B * ((P.q : ℝ) * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
          (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0 (E := E) P.q P.R0))) := by
      gcongr
    refine hstep.trans ?_
    have hnum := cab_numeric c (Col.gB (IR I)) X.gA g' (dstar (E := E) P.m) P.q (t0 (E := E) P.q P.R0) hq2 hGle hg'
      (threshold_ge_log_bound P hc) (threshold_ge_rank_log_two P)
    refine hnum.trans (le_of_eq ?_)
    simp only [Par.eps1]
  · have h4 := Col.l2_colS_le_four_mul hI hP hGT hβ hB0 hBβ
    have hJ1 := cab_J_one P (G := Col.gB (IR I)) hc
    have hl2Y : (Col.YB hI hP P.q).l2 P.q β ≤ 6 := by
      have := hl2'; rw [Fintype.card_fin] at this; nlinarith
    have hK6 := twentyfour_le_constant P
    have hf1 : (1 : ℝ) ≤ (c.factorial : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ c.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero c)
      nlinarith
    have hK6p : 0 < P.K6 := by linarith
    rw [inv_mul_le_iff₀ hK6p]
    have : P.K6 ≤ P.K6 * (c.factorial : ℝ) ^ 2 := le_mul_of_one_le_right hK6p.le hf1
    have : X.l2 P.q s' ≤ 4 * (Col.YB hI hP P.q).l2 P.q β := h4
    linarith

end

theorem colAbel_holds (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) :
    ColAbelStatement := by
  intro E _ _ _ X DF P I hI c hc σ ξ _ hξ1 hξI
  exact cab_core hx.1 hx.2.1 hA hS hI c hc σ ξ hξ1 hξI

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.EpsilonLeHalf
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

noncomputable section

theorem epsilon_le_half {E : Type} [Field E] [NumberField E] {X : PT E} {DF : ℕ} (P : Par X DF) :
    P.eps1 ≤ 1 / 2 := by
  have h6 := P.C6
  have hr0 : (0:ℝ) ≤ X.r := Nat.cast_nonneg _
  have hr : 0 ≤ (X.r : ℝ) * Real.log X.r := mul_nonneg hr0 (Real.log_natCast_nonneg _)
  have hrest : 0 ≤ ((DF : ℝ) + 1) * (X.r * Real.log X.r + 3 * X.r + 3) :=
    mul_nonneg (by positivity) (by linarith)
  have e1 := Real.exp_one_gt_d9
  have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have p2 : (2.7:ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := by gcongr; linarith
  have p3 : (2.7:ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := by gcongr; linarith
  have hl43 : Real.log 4.3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num), e2]
    norm_num at p2
    linarith
  have hl14 : Real.log 7 + Real.log 2 ≤ 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), Real.log_le_iff_le_exp (by norm_num), e3]
    norm_num at p3
    linarith
  have hds : (dstar (E := E) P.m : ℝ) * Real.log 4.3 ≤ 2 * dstar (E := E) P.m := by
    have h := mul_le_mul_of_nonneg_left hl43 (Nat.cast_nonneg (α := ℝ) (dstar (E := E) P.m))
    linarith
  have key : (7:ℝ) * 2 ^ X.gA * (4.3:ℝ) ^ dstar (E := E) P.m =
      Real.exp (Real.log 7 + X.gA * Real.log 2 + dstar (E := E) P.m * Real.log 4.3) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
  unfold Par.eps1
  rw [key, ← Real.exp_add]
  have half : (1:ℝ) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [half, Real.exp_le_exp]
  linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PointNormSqNonnegQuotient
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

def gam (hI : IsSplit P I) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) : Vsp X.dim := ∑ j, n j • cp hI j

theorem gam_mem (hI : IsSplit P I) (n) : gam hI n ∈ X.L := by
  unfold gam
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (cp_mem hI j)

theorem gam_pair (hI : IsSplit P I) (n) (i) :
    (Hf (gam hI n) ((Ib hI i : IR I) : Vsp X.dim)).im = n i := by
  unfold gam
  rw [Col.Hf_sum_l, Complex.im_sum]
  simp_rw [← Int.cast_smul_eq_zsmul ℂ, Col.Hf_smul_l, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, cp_pair hI, Pi.single_apply]
  simp

theorem pointNormSq_nonneg_quotient (hP : Ext.PackingCount) (hI : IsSplit P I) (β) (t) :
    0 ≤ (YB hI hP 1).ptN2 1 β t := by
  unfold GT.ptN2
  positivity

theorem fibre_sum (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (W : Vsp X.dim) :
    ∫⁻ t in cubeIco (Fin (Module.finrank ℝ (IR I))), ENNReal.ofReal (X.ptN2 1 s fun _ => W + tb hI t) =
      ∑' n, ENNReal.ofReal ((YB hI hP 1).ptN2 1 (zmB hI s) (wmap (IR I) (W + gam hI n)) *
        Real.exp (-(2 * Real.pi) * ‖uc (IR I) (W + gam hI n)‖ ^ 2)) := by
  have hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0 := Col.iso_IR hI.iso
  have hE2 : ∀ a : ℝ, Real.exp a ^ 2 = Real.exp (2 * a) := fun a => by
    rw [sq, ← Real.exp_add, two_mul]
  have hp1add : ∀ a b, Col.p1 (IR I) (a + b) = Col.p1 (IR I) a + Col.p1 (IR I) b := by
    intro a b
    simp only [Col.p1, z_add, add_smul, Finset.sum_add_distrib]
  have hp2add : ∀ a b, Col.p2 (IR I) (a + b) = Col.p2 (IR I) a + Col.p2 (IR I) b := by
    intro a b
    simp only [Col.p2, hp1add]
    abel
  have hp2K : ∀ b ∈ IR I, Col.p2 (IR I) b = 0 := by
    intro b hb
    have h := congrArg Subtype.val ((Col.ob (IR I)).sum_repr' ⟨b, hb⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [Col.p2, Col.p1, sub_eq_zero]
    conv_lhs => rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [z_of_K hI k hb, Complex.coe_smul]
    rfl
  have hucn : ∀ v, ‖Col.uc (IR I) v‖ ^ 2 = ∑ k, (Col.z (IR I) k v).im ^ 2 := by
    intro v
    rw [← Col.Hf_self_re, Col.uc, Col.Hf_sum_l]
    simp [Col.Hf_sum_r, Col.Hf_rsmul_l, Col.Hf_rsmul_r, Col.Hf_e hK, Complex.re_sum, sq]
  have hnadd : ∀ a b : Vsp X.dim, ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * (Hf a b).re + ‖b‖ ^ 2 := by
    intro a b
    rw [← Col.Hf_self_re, ← Col.Hf_self_re, ← Col.Hf_self_re, Col.Hf_add_l, Col.Hf_add_r,
      Col.Hf_add_r, Col.Hf_swap a b]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  set c : ℝ := Real.exp (-Real.pi * (2 * ∑ k, (Col.z (IR I) k W).im ^ 2 + ‖Col.p2 (IR I) W‖ ^ 2))
    with hc
  have hpt : ∀ t, X.ptN2 1 s (fun _ => W + tb hI t) = ‖zmG I s (W + tb hI t)‖ ^ 2 * c := by
    intro t
    have hw := Col.norm_sq_decomp hK (W + tb hI t)
    have hy : ∀ k, (Col.z (IR I) k (W + tb hI t)).im = (Col.z (IR I) k W).im := fun k => by
      rw [z_add, Complex.add_im, z_of_K hI k (tb_mem hI t), Complex.ofReal_im, add_zero]
    have hp : Col.p2 (IR I) (W + tb hI t) = Col.p2 (IR I) W := by
      rw [hp2add, hp2K _ (tb_mem hI t), add_zero]
    have key : ‖W + tb hI t‖ ^ 2 = (Col.S (IR I) (W + tb hI t)).re +
        2 * ∑ k, (Col.z (IR I) k W).im ^ 2 + ‖Col.p2 (IR I) W‖ ^ 2 := by
      rw [hw, hp]
      have : ∑ k, ‖Col.z (IR I) k (W + tb hI t)‖ ^ 2 =
          (Col.S (IR I) (W + tb hI t)).re + 2 * ∑ k, (Col.z (IR I) k W).im ^ 2 := by
        rw [Col.S, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hy k, Complex.sq_norm, Complex.normSq_apply, sq, Complex.mul_re]
        ring
      rw [this]
    have e1 : X.ptN2 1 s (fun _ => W + tb hI t) =
        ‖s (fun _ => W + tb hI t)‖ ^ 2 * Real.exp (-Real.pi * ‖W + tb hI t‖ ^ 2) := by
      unfold PT.ptN2 HC
      simp [Col.Hf_self_re]
    have e2 : ‖zmG I s (W + tb hI t)‖ ^ 2 = ‖s (fun _ => W + tb hI t)‖ ^ 2 *
        Real.exp (-Real.pi * (Col.S (IR I) (W + tb hI t)).re) := by
      unfold zmG
      rw [norm_mul, mul_pow, Complex.norm_exp, hE2]
      congr 2
      simp [Complex.mul_re]
      ring
    rw [e1, e2, mul_assoc, hc, ← Real.exp_add, key]
    congr 2
    ring
  have hcont : Continuous fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => ‖zmG I s (W + tb hI t)‖ ^ 2 * c :=
    (((zmG_continuous hs).comp (continuous_const.add (tb_continuous hI))).norm.pow 2).mul continuous_const
  have hint : IntegrableOn (fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => ‖zmG I s (W + tb hI t)‖ ^ 2 * c)
      (cubeIco (Fin (Module.finrank ℝ (IR I)))) := by
    refine (hcont.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1))).mono_set ?_
    rw [cubeIco_eq]
    exact Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self
  have hpar : HasSum (fun n => ‖zmC hI s n W‖ ^ 2)
      (∫ t in {x : Fin (Module.finrank ℝ (IR I)) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
        ‖zmG I s (W + tb hI t)‖ ^ 2) := fibre_parseval hI hs W
  have hcube : ∫ t in cubeIco (Fin (Module.finrank ℝ (IR I))), ‖zmG I s (W + tb hI t)‖ ^ 2 * c =
      (∑' n, ‖zmC hI s n W‖ ^ 2) * c := by
    rw [integral_mul_const, setIntegral_congr_set (cube_ae_eq _), hpar.tsum_eq]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => by positivity),
    hcube, ← tsum_mul_right,
    ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hpar.summable.mul_right c)]
  congr 1
  funext n
  congr 1
  have hγ := gam_mem hI n
  have hadd := zmC_add hI hs hγ n (gam_pair hI n) 0 W
  rw [zero_add] at hadd
  have hB : zmB hI s (Col.wmap (IR I) (W + gam hI n)) = zmC hI s 0 (W + gam hI n) := by
    unfold zmB
    rw [Col.jj_wmap' hK, ← zeroMode_proj_two hI hs]
  have heps : ‖(X.eps (gam hI n) : ℂ)‖ = 1 := by
    rcases X.eps_pm _ hγ with h | h <;> simp [h]
  have hg : (gaugeExp I (gam hI n) W).re =
      2 * Real.pi * ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k W).im +
        Real.pi * ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k (gam hI n)).im +
        Real.pi * (Hf (Col.p2 (IR I) W) (Col.p2 (IR I) (gam hI n))).re +
        Real.pi * ‖Col.p2 (IR I) (gam hI n)‖ ^ 2 / 2 := by
    unfold gaugeExp
    simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Col.Hf_self_re, Finset.mul_sum]
  have hp2n := hnadd (Col.p2 (IR I) W) (Col.p2 (IR I) (gam hI n))
  rw [← hp2add] at hp2n
  have hucW : ‖Col.uc (IR I) (W + gam hI n)‖ ^ 2 =
      ∑ k, ((Col.z (IR I) k W).im + (Col.z (IR I) k (gam hI n)).im) ^ 2 := by
    rw [hucn]
    simp [z_add]
  have hsq : ∑ k, ((Col.z (IR I) k W).im + (Col.z (IR I) k (gam hI n)).im) ^ 2 =
      ∑ k, (Col.z (IR I) k W).im ^ 2 +
        2 * ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k W).im +
        ∑ k, (Col.z (IR I) k (gam hI n)).im * (Col.z (IR I) k (gam hI n)).im := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold GT.ptN2
  rw [hB, hadd, Col.norm_wmap hK, norm_mul, norm_mul, heps, one_mul, Complex.norm_exp, mul_pow, hE2,
    hp2n, hucW, hsq, hg, hc]
  rw [mul_comm (Real.exp _) (‖zmC hI s n W‖ ^ 2), mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem YB_cube (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (A0 : EuclideanSpace ℂ (Fin (gB (IR I)))) :
    ∫⁻ r in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))),
        ENNReal.ofReal ((YB hI hP 1).ptN2 1 (zmB hI s) (A0 + (bB hI hP).equivFun.symm r)) =
      ENNReal.ofReal ((YB hI hP 1).l2 1 (zmB hI s)) := by
  have hF : zmB hI s ∈ (Col.YB hI hP 1).Sec 1 := zeroMode_mem_sections hI hP hs
  have hE : ∀ a b : ℝ, Real.exp a ^ 2 * Real.exp b = Real.exp (2 * a + b) := fun a b => by
    rw [Real.exp_add, sq, ← Real.exp_add, two_mul]
  have hper : ∀ γ ∈ lat (Col.YB hI hP 1).b, ∀ v,
      (Col.YB hI hP 1).ptN2 1 (zmB hI s) (v + γ) = (Col.YB hI hP 1).ptN2 1 (zmB hI s) v := by
    intro γ hγ v
    have h1 := hF.2 γ hγ v
    have hka := (Col.YB hI hP 1).ka_abs γ hγ
    have hn : ‖v + γ‖ ^ 2 = ‖v‖ ^ 2 + 2 * (Hf v γ).re + ‖γ‖ ^ 2 := by
      rw [← Col.Hf_self_re, ← Col.Hf_self_re, ← Col.Hf_self_re, Col.Hf_add_l, Col.Hf_add_r,
        Col.Hf_add_r, Col.Hf_swap v γ]
      simp only [Complex.add_re, Complex.conj_re]
      ring
    have hre : ((((1 : ℕ) : ℂ) * (Real.pi : ℂ) * Hf v γ + ((1 : ℕ) : ℂ) * (Real.pi : ℂ) * Hf γ γ / 2)).re =
        Real.pi * (Hf v γ).re + Real.pi * ‖γ‖ ^ 2 / 2 := by
      rw [← Col.Hf_self_re]
      simp [Complex.add_re, Complex.mul_re]
    unfold GT.ptN2
    rw [h1, norm_mul, norm_mul, hka, one_mul, Complex.norm_exp, hre, mul_pow, mul_right_comm, hE, hn,
      mul_comm]
    congr 2
    push_cast
    ring
  have hBsymm : ∀ x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ,
      (Col.bB hI hP).equivFun.symm x = ∑ i, x i • (Col.bB hI hP) i := fun x =>
    Module.Basis.equivFun_symm_apply _ _
  have hBc : Continuous (Col.bB hI hP).equivFun.symm :=
    (Col.bB hI hP).equivFun.symm.toLinearMap.continuous_of_finiteDimensional
  have hcont : Continuous ((Col.YB hI hP 1).ptN2 1 (zmB hI s)) := by
    unfold GT.ptN2
    exact (hF.1.continuous.norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  set g : (Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) → ℝ :=
    fun x => (Col.YB hI hP 1).ptN2 1 (zmB hI s) ((Col.bB hI hP).equivFun.symm x) with hgdef
  have hgc : Continuous g := hcont.comp hBc
  have hgper : ∀ (x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ)
      (n : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℤ), g (x + fun i => (n i : ℝ)) = g x := by
    intro x n
    simp only [hgdef, map_add]
    apply hper
    rw [hBsymm]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  set a0 := (Col.bB hI hP).equivFun A0 with ha0
  have hshift : ∀ x, (Col.YB hI hP 1).ptN2 1 (zmB hI s) (A0 + (Col.bB hI hP).equivFun.symm x) =
      g (x + a0) := by
    intro x
    simp only [hgdef, map_add, ha0, LinearEquiv.symm_apply_apply]
    rw [add_comm]
  have hbox : ∫ x in {x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      g (x + a0) = ∫ x in {x : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
      g x := by
    have h := tof_box_shift (fun x => (g x : ℂ)) (Complex.continuous_ofReal.comp hgc)
      (fun x n => by simp only [hgper]) a0
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h
  have hcube : ∫ x in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))), g (x + a0) =
      ∫ x in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))), g x := by
    rw [setIntegral_congr_set (cube_ae_eq _), setIntegral_congr_set (cube_ae_eq _)]
    exact hbox
  have hint : IntegrableOn (fun x => g (x + a0)) (cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I)))))) := by
    refine ((hgc.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1))).mono_set ?_
    rw [cubeIco_eq]
    exact Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self
  have hl2 : (Col.YB hI hP 1).l2 1 (zmB hI s) =
      ∫ x in cubeIco (Fin (2 * Fintype.card (Fin (gB (IR I))))), g (x + a0) := by
    unfold GT.l2
    rw [avg_fd_cube, hcube]
    rfl
  simp_rw [hshift]
  rw [hl2, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => by simp only [hgdef]; unfold GT.ptN2; positivity)]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

