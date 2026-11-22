import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0297
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0249
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FmSmulLeft
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmu
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowAsm
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem gl_isLocPt_snoc {a : C.LPt} {j m : ℕ} (ha : D.IsLocPt a j) (hm : 1 ≤ m) {c : ℂ} (hc : c ≠ 0) :
    D.IsLocPt (a ++ [(m, c)]) (j + m) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact ha.1 x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hm, hc⟩
  · rw [← ha.2]
    simp [D.ptSize, List.map_append, List.sum_append]

theorem gl_fsv (σ z : ℂ) : P5.fsv σ z = G.psi (-U.betaU) (1 * σ * z) := by
  rw [TBBx1.fsv_eq]
  unfold G.psi U.betaU Formalism.QuantumDeterminants.cStd
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
  push_cast
  ring

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gl_inner_self (u : H) : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

end vec

theorem germDataLowAll_of_parts (hGr : GLGram) (hFi : GLFibre) (hCo : GLCont) (hGe : GLGerm) : GermDataLowAll := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF hnn b s hb hs hbs hlev h hh w hw hN hBdd
  have hi : b + s - 1 ≤ P.r := hlev
  have hN' : w.length ≤ N := by omega
  obtain ⟨H, i1, i2, i3, Vec, hVec⟩ := hGr hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 1) hi w hw hN'
  let _ := i1; let _ := i2; have _ := i3
  have hs0 : s ≠ 0 := by omega
  have hpi : (0 : ℝ) < Real.pi ^ (s - 1) := pow_pos Real.pi_pos _
  set κ : ℝ := (Real.pi ^ (s - 1))⁻¹ with hκ
  have hκκ : Real.pi ^ (2 * (s - 1)) * (κ * κ) = 1 := by
    rw [hκ, pow_mul', sq, ← mul_inv, mul_inv_cancel₀ (by positivity)]
  let ut : ℂ → ℂ → H := fun x D => (((κ * ‖x‖ ^ (s - 1)) : ℝ) : ℂ) • Vec (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])
  let bt : ℂ → H := fun z => if z = 0 then 0 else ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])

  have hcv : ∀ x : ℂ, x ≠ 0 → ∀ c : ℂ, PBK.cvec s ut x c = (κ : ℂ) • Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)]) := by
    intro x hx c
    have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
    have hn : (‖x‖ ^ (s - 1) : ℝ) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    simp only [PBK.cvec, ut, smul_smul, List.append_assoc, List.cons_append, List.nil_append]
    rw [mul_div_cancel₀ c ha, ← Complex.ofReal_mul]
    congr 2
    field_simp

  have hj : b + s - 2 + 1 = b + s - 1 := by omega
  have hloc : ∀ t : ℂ, t ≠ 0 → D.IsLocPt (h ++ [(s - 1, t)]) (b + s - 2) := by
    intro t ht
    have := gl_isLocPt_snoc hh (by omega : 1 ≤ s - 1) ht
    rwa [show b - 1 + (s - 1) = b + s - 2 by omega] at this

  have hgram : ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      ∫ c, ⟪PBK.cvec s ut x c, PBK.cvec s ut x' c⟫_ℂ =
        ((κ * κ : ℝ) : ℂ) * TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x'⁻¹)]) := by
    intro x x' hx hx'
    obtain ⟨-, hfib⟩ := hFi hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) (by omega) w hw hN'
      (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x'⁻¹)]) (hloc _ (inv_ne_zero hx)) (hloc _ (inv_ne_zero hx'))
    rw [hj] at hfib
    rw [← hfib, ← integral_const_mul]
    congr 1
    funext c
    rw [hcv x hx c, hcv x' hx' c, GermFibreKernels.inner_real_smul_smul, hVec]

  have hbz : ∀ z : ℂ, z ≠ 0 → PBK.bz s bt z = Vec (h ++ [(s, z)]) := by
    intro z hz
    simp only [PBK.bz, bt, if_neg hz, smul_smul, ← Complex.ofReal_mul]
    rw [mul_inv_cancel₀, Complex.ofReal_one, one_smul]
    have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
    have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
    positivity

  have hVecR : ∀ i (hi' : i = b + s - 1) a a', TBB.NP p nn F i w a a' = ⟪Vec a, Vec a'⟫_ℂ := by
    intro i hi' a a'; subst hi'; exact hVec a a'
  have hcont1 : ∀ t : ℂ, t ≠ 0 → ContinuousOn (fun c : ℂ => Vec ((h ++ [(s - 1, t)]) ++ [(1, c)])) {0}ᶜ := by
    intro t ht
    have hk := hCo hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) 1 le_rfl (by omega) w hw hN' _ (hloc t ht)
    exact GermFibreKernels.vec_continuousOn _ Vec (hVecR _ hj) (fun c => (h ++ [(s - 1, t)]) ++ [(1, c)]) {0}ᶜ hk
  have hcontS : ContinuousOn (fun z : ℂ => Vec (h ++ [(s, z)])) {0}ᶜ := by
    have hk := hCo hA Wp Wq P p nn F Y N Cb hCb hF hnn (b - 1) s (by omega) (by omega) w hw hN' h hh
    exact GermFibreKernels.vec_continuousOn _ Vec (hVecR _ (by omega)) (fun z => h ++ [(s, z)]) {0}ᶜ hk

  obtain ⟨B0, hB0⟩ := hBdd w (TBBx1.isExt_self hw hN')
  refine ⟨H, i1, i2, i3, ut, bt, -U.betaU, (-1) ^ (s + 1), 1, κ * κ * B0, Real.pi ^ (2 * (s - 1)), 1,
    zero_le_one, ?_, Or.inl rfl, ?_, gl_fsv, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    exact one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ h1)
  · have hae : ∀ᵐ z : ℂ ∂volume, z ∈ ({0}ᶜ : Set ℂ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℂ))
    have hmeas0 : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
    refine ⟨hs0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold U.betaU Formalism.QuantumDeterminants.cStd
      simp [Complex.I_ne_zero]
    · simp [norm_pow]
    ·
      intro _ _ x hx
      refine (PBK.memLp_cvec s ut x hx).2 ?_
      have hfun : PBK.cvec s ut x = fun c => (κ : ℂ) • Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)]) := funext (hcv x hx)
      rw [hfun]
      refine MemLp.const_smul ?_ _
      have hmeas : AEStronglyMeasurable (fun c : ℂ => Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)])) volume := by
        have h2 := (hcont1 x⁻¹ (inv_ne_zero hx)).aestronglyMeasurable (μ := volume) hmeas0
        rwa [Measure.restrict_eq_self_of_ae_mem hae] at h2
      refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
      obtain ⟨hint, -⟩ := hFi hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) (by omega) w hw hN' _ _
        (hloc _ (inv_ne_zero hx)) (hloc _ (inv_ne_zero hx))
      rw [hj] at hint
      refine (Complex.reCLM.integrable_comp hint).congr (Eventually.of_forall fun c => ?_)
      simp only [Complex.reCLM_apply]
      rw [hVec, gl_inner_self, Complex.ofReal_re]
    ·
      intro _ _ x hx
      have e1 := PBK.cvec_inner s ut ut x x hx hx
      simp only [div_self (pow_ne_zero _ hx), norm_one, Complex.ofReal_one, one_smul, one_mul] at e1
      have e2 : ∫ D, ⟪ut x D, ut x D⟫_ℂ = ((∫ D, ‖ut x D‖ ^ 2 : ℝ) : ℂ) := by
        simp_rw [gl_inner_self]; exact integral_ofReal
      rw [e2, hgram x x hx hx] at e1
      have e3 := congrArg Complex.re e1
      rw [Complex.ofReal_re, Complex.re_ofReal_mul] at e3
      rw [← e3]
      have hE : (TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x⁻¹)])).re ≤ B0 :=
        hB0 ⟨⟨x⁻¹, inv_ne_zero hx⟩, rfl⟩
      exact mul_le_mul_of_nonneg_left hE (mul_self_nonneg κ)
    ·
      intro _ _
      let _ : MeasurableSpace H := borel H
      have _ : BorelSpace H := ⟨rfl⟩
      let g : ℂ → H := fun z => ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])
      have hgc : ContinuousOn g {0}ᶜ := by
        refine ContinuousOn.smul ?_ hcontS
        refine Complex.continuous_ofReal.comp_continuousOn ?_
        refine ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) fun z hz => ?_
        have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
        have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
        positivity
      have hbt' : bt = ({0}ᶜ : Set ℂ).piecewise g (fun _ => 0) := by
        funext z
        by_cases hz : z = 0
        · simp [bt, hz]
        · simp [bt, hz, Set.piecewise, g]
      show StronglyMeasurable bt
      rw [stronglyMeasurable_iff_measurable_separable, hbt']
      refine ⟨ContinuousOn.measurable_piecewise hgc continuousOn_const hmeas0, ?_⟩
      refine TopologicalSpace.IsSeparable.mono (s := g '' {0}ᶜ ∪ {0}) ?_ (Set.range_subset_iff.2 fun z => ?_)
      · exact (hgc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace _)).union
          (Set.finite_singleton (0 : H)).isSeparable
      · by_cases hz : z ∈ ({0}ᶜ : Set ℂ)
        · left; rw [Set.piecewise_eq_of_mem _ _ _ hz]; exact ⟨z, hz, rfl⟩
        · right; rw [Set.piecewise_eq_of_notMem _ _ _ hz]; rfl
    ·
      intro _ _ K' hK hK0
      have hsub : K' ⊆ {0}ᶜ := fun z hz hz0 => hK0 (by rw [Set.mem_singleton_iff.1 hz0] at hz; exact hz)
      have hc : ContinuousOn (fun z => ‖Vec (h ++ [(s, z)])‖ ^ 2) K' := (hcontS.norm.pow 2).mono hsub
      refine (hc.congr fun z hz => ?_).integrableOn_compact hK
      rw [hbz z (fun h0 => hK0 (h0 ▸ hz))]
    ·
      intro _ _ K' hK hK0
      obtain ⟨C, hC⟩ := hGe hA Wp Wq P p nn F Y N Cb hCb hF hnn b s hb hs hi h hh w hw hN' H Vec hVec K' hK hK0
      refine ⟨C, fun x hx => Eventually.of_forall fun D hD => ?_⟩
      have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
      refine le_of_eq_of_le ?_ (hC x hx D hD)
      congr 2
      unfold PBK.mainD
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz0 : z ≠ 0 := by
        rintro rfl
        have hr := (Polynomial.mem_nthRoots (by omega : 0 < s)).1 (Multiset.mem_toFinset.1 hz)
        rw [zero_pow hs0] at hr
        exact hD0 (by simpa using hr.symm)
      exact congrArg (fun v => G.psi (-U.betaU) ((s : ℂ) * z * x) • v) (if_neg hz0)
  · intro t t' ht ht'
    have hg := hgram t⁻¹ t'⁻¹ (inv_ne_zero ht) (inv_ne_zero ht')
    simp only [inv_inv] at hg
    show _ = _ * ‖∫ c, ⟪PBK.cvec s ut t⁻¹ c, PBK.cvec s ut t'⁻¹ c⟫_ℂ‖
    rw [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg κ), ← mul_assoc, hκκ,
      one_mul]
  · intro z hz
    unfold TBB.Ew
    rw [hbz z hz, hVec, gl_inner_self, Complex.ofReal_re, one_mul]

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowFibre
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt MeasureTheory
open scoped ComplexConjugate

noncomputable section

open Classical

theorem nPt_append_one (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j + 1 ≤ P.r) (c : ℂ) :
    TBB.nPt P.k P.r TT (a ++ [(1, c)]) = TBB.nPt P.k P.r TT a * KB.levW P (j + 1) c := by
  unfold TBB.nPt
  rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, ha.2,
    Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r (D.ptGG TT (a ++ [(1, c)])) (D.ptGG TT a) (fun _ _ => 1) a 1 le_rfl
      (by rw [ha.2]; omega)]
  congr 1
  simp only [C.nAux, KB.levW]
  rw [if_neg (by omega), if_neg (by omega)]
  have e : 1 + j + 1 - 1 = j + 1 := by omega
  rw [e]
  simp only [one_mul, mul_one, Nat.cast_one]
  congr 1
  ring

theorem nPt_nonneg_loc (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j ≤ P.r) :
    0 ≤ TBB.nPt P.k P.r TT a :=
  Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r _ (fun _ _ => 1) (fun _ _ => one_pos) a 1 le_rfl (by rw [ha.2]; omega)

theorem levW_nonneg_low (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) (c : ℂ) : 0 ≤ KB.levW P (j + 1) c := by
  simp only [KB.levW]
  rw [if_neg (by omega)]
  exact zpow_nonneg (norm_nonneg _) _

theorem glFibre : GLFibre := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn j hj w hw hN a b ha hb
  have hPS : KB.PStd := Formalism.FourierDecayAlt.P.standard_pairing_of_heads Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top
  have hjr : j ≤ P.r := by omega
  obtain ⟨φ, -, hφi, hφ, hφs⟩ := hPS hA Wp Wq P p F j hjr w a b ha hb Cb hCb hF hw.1
  set K : ℝ := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) /
    TBB.normC nn w with hK
  have hae : (fun c => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)])) =ᵐ[volume]
      fun c => (K : ℂ) * φ c := by
    filter_upwards [Formalism.FourierDecayAlt.P.TBBx1.ae_ne_zero] with c hc
    rw [hφ c hc]
    unfold TBB.NP
    rw [nPt_append_one P _ a j ha hj c, nPt_append_one P _ b j hb hj c,
      Real.sqrt_mul (nPt_nonneg_loc P _ a j ha hjr), Real.sqrt_mul (nPt_nonneg_loc P _ b j hb hjr)]
    have hl := Real.mul_self_sqrt (levW_nonneg_low P j hj c)
    rw [hK]
    have : Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (KB.levW P (j + 1) c) *
        (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) * Real.sqrt (KB.levW P (j + 1) c)) / TBB.normC nn w =
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) / TBB.normC nn w *
          KB.levW P (j + 1) c := by
      calc _ = Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) /
              TBB.normC nn w * (Real.sqrt (KB.levW P (j + 1) c) * Real.sqrt (KB.levW P (j + 1) c)) := by ring
        _ = _ := by rw [hl]
    rw [this]
    push_cast
    ring
  refine ⟨(hφi.const_mul (K : ℂ)).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_const_mul]
  have h0 := hφs 0
  simp only [P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_mul,
    Formalism.FourierDecayAlt.P.PBASM.waveG_zero_eq_self] at h0
  rw [h0]
  unfold TBB.NP
  congr 1
  unfold KB.Pl.RR D.RRplace
  rw [dif_pos ⟨ha, hb⟩, dif_pos hjr]
  rfl

end

end Formalism.FourierDecayAlt.P.CutBP

theorem Formalism.FourierDecayAlt.P.CutBP.low_level_fibre : Formalism.FourierDecayAlt.P.CutBP.GLFibre := Formalism.FourierDecayAlt.P.CutBP.glFibre
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGermW
section
namespace Formalism.FourierDecayAlt.P.CutBP.GLG

open Formalism.FourierDecayAlt

noncomputable section

theorem zpow_two_nat (x : ℝ) (e : ℤ) (n : ℕ) (he : e = 2 * (n : ℤ)) : x ^ e = (x ^ n) ^ 2 := by
  subst he
  rw [show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul']

theorem nPt_block {P : M.Par} (TT : ℝ) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r) (h : C.LPt)
    (hh : D.ptSize h = b - 1) (t c : ℂ) :
    TBB.nPt P.k P.r TT (h ++ [(m + 1, t), (1, c)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h *
        ((‖t‖ ^ ((m + 1) * (U.Mlev P.k (P.r - (b + (m + 2) - 1)) + m))) ^ 2 *
          (‖c‖ ^ (U.Mlev P.k (P.r - (b + (m + 2) - 1)) - 2)) ^ 2) := by
  have e : h ++ [(m + 1, t), (1, c)] = (h ++ [(m + 1, t)]) ++ [(1, c)] := by simp
  have hs1 : D.ptSize (h ++ [(m + 1, t)]) = b - 1 + (m + 1) := by
    simp only [D.ptSize, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hh ⊢
    omega
  unfold TBB.nPt
  rw [e, PBD.weight_product_append, PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hs1, hh]
  simp only [C.nAux, one_mul, mul_one]
  rw [if_neg (by omega), if_neg (by omega), mul_assoc]
  congr 2
  · apply zpow_two_nat
    unfold C.Mlev U.Mlev
    have e1 : 1 + (b - 1) + (m + 1) - 1 = b + m := by omega
    rw [e1]
    push_cast [Nat.cast_sub (show b + (m + 2) - 1 ≤ P.r from hi), Nat.cast_sub (show b + m ≤ P.r + 1 by omega)]
    rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
    push_cast
    ring
  · apply zpow_two_nat
    unfold C.Mlev U.Mlev
    have e1 : 1 + (b - 1 + (m + 1)) + 1 - 1 = b + (m + 2) - 1 := by omega
    rw [e1]
    have h3 : 2 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 := by omega
    push_cast [Nat.cast_sub h3, Nat.cast_sub hi]
    rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
    push_cast
    ring

theorem nPt_long {P : M.Par} (TT : ℝ) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r) (h : C.LPt)
    (hh : D.ptSize h = b - 1) (z : ℂ) :
    TBB.nPt P.k P.r TT (h ++ [(m + 2, z)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h * (‖z‖ ^ ((m + 2) * (U.Mlev P.k (P.r - (b + (m + 2) - 1)) + m - 1))) ^ 2 := by
  unfold TBB.nPt
  rw [PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hh]
  simp only [C.nAux, one_mul, mul_one]
  rw [if_neg (by omega)]
  congr 1
  apply zpow_two_nat
  unfold C.Mlev U.Mlev
  have e1 : 1 + (b - 1) + (m + 2) - 1 = b + (m + 2) - 1 := by omega
  rw [e1]
  have h3 : 1 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 + m := by omega
  push_cast [Nat.cast_sub h3, Nat.cast_sub hi]
  rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutBP.GLG
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowGram
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section forms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)

theorem formC_zero_l (y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hy : PBL.CV (p.T.bs j) y) : p.form j hj w 0 y = 0 := by
  have h := PBL.form_slC p j hj w 0 0 y 1 PBL.cv_zero PBL.cv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem formC_zero_r (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) : p.form j hj w x 0 = 0 := by
  have h := PBL.form_srC p j hj w x 0 0 1 hx PBL.cv_zero PBL.cv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem formC_smul_l (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w (c • x) y = c * p.form j hj w x y := by
  have h := PBL.form_slC p j hj w 0 x y c PBL.cv_zero hx hy
  rwa [zero_add, formC_zero_l p j hj w y hy, zero_add] at h

theorem formC_smul_r (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w x (c • y) = conj c * p.form j hj w x y := by
  have h := PBL.form_srC p j hj w x 0 y c hx PBL.cv_zero hy
  rwa [zero_add, formC_zero_r p j hj w x hx, zero_add] at h

end forms

theorem glGram : GLGram := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn i hi w hw hN
  have hpos : TBBx5.FormNonneg p := TBBx5.formNonneg_of hA (Formalism.FourierDecayAlt.P.pb_formPos : PBL.FormPos) p
  have hnC : 0 < TBB.normC nn w := by
    unfold TBB.normC
    refine List.prod_pos fun x hx => ?_
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
    exact hnn _
  set c0 : ℝ := 1 / TBB.normC nn w with hc0
  have hc0n : 0 ≤ c0 := by positivity
  let sq : C.LPt → ℝ := fun a => Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a)
  let u : C.LPt → (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) := fun a =>
    if ha : D.IsLocPt a i then ((sq a : ℝ) : ℂ) • KB.slv p.T F i hi w a ha.2 else 0
  have hslv : ∀ a (ha : D.IsLocPt a i), PBL.CV (p.T.bs i) (KB.slv p.T F i hi w a ha.2) :=
    fun a ha e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F i hi w a ha hF e
  have hu : ∀ a, PBL.CV (p.T.bs i) (u a) := by
    intro a
    by_cases ha : D.IsLocPt a i
    · simp only [u, dif_pos ha]; exact PBL.cv_smul _ (hslv a ha)
    · simp only [u, dif_neg ha]; exact PBL.cv_zero
  let β : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) →
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) → ℂ :=
    fun x y => (c0 : ℂ) * p.form i hi w x y
  have hpsd : ∀ Y' : Finset C.LPt, TB.PSDOn Y' (fun a b => β (u a) (u b)) := by
    intro Y'
    refine PBL.gram_psd (PBL.CV (S := Fin w.length) (p.T.bs i)) β PBL.cv_zero (fun x y hx hy => PBL.cv_add hx hy)
      (fun c x hx => PBL.cv_smul c hx) ?_ ?_ ?_ Y' u hu
    · intro x₁ x₂ y c h₁ h₂ hy
      simp only [β, PBL.form_slC p i hi w x₁ x₂ y c h₁ h₂ hy]; ring
    · intro x y₁ y₂ c hx h₁ h₂
      simp only [β, PBL.form_srC p i hi w x y₁ y₂ c hx h₁ h₂]; ring
    · intro x hx
      obtain ⟨ε, hε, hnv⟩ := PBL.nv_of_cv hx
      exact mul_nonneg (by exact_mod_cast hc0n) (hpos i hi w hw.1 x ε hε hnv)
  obtain ⟨H, i1, i2, i3, V, hV⟩ := Formalism.FourierDecayAlt.P.GermFibreKernels.kolmogorov _ hpsd
  refine ⟨H, i1, i2, i3, V, fun a b => ?_⟩
  rw [← hV]
  simp only [β]
  by_cases ha : D.IsLocPt a i
  · by_cases hb : D.IsLocPt b i
    · simp only [u, dif_pos ha, dif_pos hb]
      rw [formC_smul_l p i hi w _ _ _ (hslv a ha) (PBL.cv_smul _ (hslv b hb)),
        formC_smul_r p i hi w _ _ _ (hslv a ha) (hslv b hb), Complex.conj_ofReal]
      have hrr : p.RR F i w a b = p.form i hi w (KB.slv p.T F i hi w a ha.2) (KB.slv p.T F i hi w b hb.2) := by
        unfold KB.Pl.RR D.RRplace
        rw [dif_pos ⟨ha, hb⟩, dif_pos hi]
        rfl
      unfold TBB.NP
      rw [hrr, hc0]
      simp only [sq]
      push_cast
      ring
    · simp only [u, dif_neg hb]
      rw [formC_zero_r p i hi w _ (hu a)]
      unfold TBB.NP KB.Pl.RR D.RRplace
      rw [dif_neg (fun h => hb h.2)]
      simp
  · simp only [u, dif_neg ha]
    rw [formC_zero_l p i hi w _ (hu b)]
    unfold TBB.NP KB.Pl.RR D.RRplace
    rw [dif_neg (fun h => ha h.1)]
    simp

end

end Formalism.FourierDecayAlt.P.CutBP

theorem Formalism.FourierDecayAlt.P.CutBP.low_level_gram : Formalism.FourierDecayAlt.P.CutBP.GLGram := Formalism.FourierDecayAlt.P.CutBP.glGram
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuFacts
section
namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData MeasureTheory
open scoped InnerProductSpace ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

variable [CompleteSpace Wp] [CompleteSpace Wq]
variable {Bs : B.RealPlaceData k r Wp Wq} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
  {u u' : Fin k → ℝ} {νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)} {A : JDat k r Wp Wq}

theorem lowest_unit_vector_is_K_finite (hG : A.Good Bs ε lam h u u' νq νq') : PI.UpqRep.IsKFinHpk (k := k) (r := r) A.σ A.w0 :=
  PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hG.1.2.2.2.2.1

end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
end

