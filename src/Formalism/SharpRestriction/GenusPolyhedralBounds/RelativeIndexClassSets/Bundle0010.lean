import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0009
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HasseOrdBd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0043
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FourthHypothesisOfParams
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

section Run

variable (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L)

def h0R (T : ParamsT D L P) : ℝ := 4 * (T.TO : ℝ) ^ 2 + D.R.t + 1

theorem two_mul_order_sq_le_length : 2 * (T.TO : ℝ) ^ 2 ≤ ((runOf T S hZ).kl : ℝ) := by
  have hR := rn_of T S hZ
  have h1 := hR.sq_mul_sq_le; have h4 := hR.forty_eight_le_constant
  have h5 : 2 * (T.TO : ℝ) ^ 2 ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 * (T.TO : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  linarith [b_le_kl T S hZ]

theorem A_le_kf : (D.R.f : ℝ) * D.R.r ≤ 2 * ((D.R.k : ℝ) * D.R.f) := by
  have h1 : D.R.r ≤ 2 * D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have h2 : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

theorem setCn_of (B : WeightFamilies.Prov D) (hO : OPO L B) (hDom : DomAt D L D.R.m T.nWn 1000) :
    Inh.SetCn L B 10 1000 (runOf T S hZ).ka (runOf T S hZ).wL (runOf T S hZ).wF T.TO T.nP T.nWn (h0R T) := by
  have hR := rn_of T S hZ
  have hkl := two_mul_order_sq_le_length T S hZ
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hb := hR.b_pos
  have hAk := A_le_kf (D := D)
  have hTO1 := hR.one_le_order_alt
  have hAkb : ((D.R.f : ℝ) * D.R.r) * L.sc.b ≤ 2 * ((D.R.k : ℝ) * D.R.f) * L.sc.b :=
    mul_le_mul_of_nonneg_right hAk hb.le
  have hkfb : 0 ≤ (D.R.k : ℝ) * D.R.f * L.sc.b := by positivity
  refine ⟨rfl, (runOf T S hZ).gapP, (runOf T S hZ).gapM, le_rfl, fun τ => ?_, fun τ i h => ?_,
    fun τ i h => (runOf T S hZ).lastM _ τ i h, ?_, T.even_nP₂, T.nP_ge, T.nW_lo.2.2, ?_, T.nW_lo.1, T.split,
    (runOf T S hZ).isL, (runOf T S hZ).isF, ?_, (runOf T S hZ).T_pos, ?_, ?_, ?_, T.nW_40, ?_, ?_, hO, hDom⟩
  · rw [RunN.ncAt_ka]
    push_cast
    unfold h0R
    nlinarith [sq_nonneg (T.TO : ℝ)]
  · rw [RunN.ka_last _ τ i h]
    unfold h0R
    linarith
  · have := ka_le T S hZ
    linarith
  · unfold sizeConstantAtParamsWeight
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · rw [le_div_iff₀ (by linarith)]
    have := wL_le T S hZ
    linarith
  · rw [dm_eq T]; have := T.TO_40; omega
  · rw [dm_eq T]; exact T.TO_40
  · rw [dm_eq T]; exact T.TO_nW
  · rw [baseDegree_at_lift_index]
    have h := T.order_ge_rank_bound
    have e : g0 D = 2 * 5 ^ 4 * D.R.r := rfl
    rw [e]
    have : 2 * (2 * 5 ^ 4 * D.R.r) * 1 ≤ 2 * (2 * 5 ^ 4 * D.R.r) * (T.Dp + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [dm_eq T]; exact T.TO_11D2

theorem fourth_hypothesis_of_params : L.sc.b ≤ (runOf T S hZ).ka.size ∧ (T.TO : ℝ) * (runOf T S hZ).wL.size ≤ 2 * (runOf T S hZ).ka.size ∧
    (runOf T S hZ).wF.size ≤ ((WeightFamilies.dimY D D.R.m : ℝ) + 2) * (runOf T S hZ).wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T.TO ∧
    WeightFamilies.PPv D L T.CP T.eP ^ 3 * (T.TO : ℝ) ^ 2 ≤ L.sc.b ∧ WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP ≤ L.sc.b ∧
    (∀ i, 2 * DF (runOf T S hZ).ka + 2 < D.host.g i) := by
  have hR := rn_of T S hZ
  have hbk := b_le_ka T S hZ
  have hTb : (T.TO : ℝ) ≤ L.sc.b := hR.toBs.TO_le_sb.trans hR.toBs.sb_le_b
  refine ⟨hbk, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · have := (runOf T S hZ).T_wL_le
    have e : ((runOf T S hZ).T : ℝ) = (T.TO : ℝ) := rfl
    rw [e] at this
    linarith
  · have h := (runOf T S hZ).wF_size_le
    have e : ((runOf T S hZ).nP : ℝ) = (T.nP : ℝ) := rfl
    rw [e] at h
    have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
    have hr := hR.r6; have hT := hR.one_le_order_alt; have hn := hR.nPW; have hn2 := hR.nW_le
    have a0 : (0 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
    have a1 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * 1 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * T.TO := mul_le_mul_of_nonneg_left hT a0
    have a2 : (D.R.f : ℝ) * D.R.r * T.nP ≤ (D.R.f : ℝ) * D.R.r * T.TO :=
      mul_le_mul_of_nonneg_left (hn.trans hn2) (by positivity)
    have a3 : (D.R.f : ℝ) * D.R.r * T.TO ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * T.TO := by
      have : (D.R.f : ℝ) * D.R.r ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have a4 : (1 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by nlinarith
    have e2 : ((Dm D : ℕ) : ℝ) = (WeightFamilies.dimY D D.R.m : ℝ) := rfl
    rw [e2] at h
    nlinarith
  · rw [WeightFamilies.PPv_rec T]
    exact hR.h32.trans hR.toBs.sb_le_b
  · rw [WeightFamilies.PPv_rec T, eRR, ← hR.sb_sq]
    exact mul_le_mul (hR.toBs.rd_pow_le (by norm_num)) hR.toBs.PP_le_sb hR.PP_pos.le hR.sb_pos.le
  · have h1 : (DF (runOf T S hZ).ka : ℝ) ≤ 4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b :=
      (DF_le_size _).trans (ka_le T S hZ)
    have h2 := hR.g_gt h1 (g_ge P i)
    exact_mod_cast h2

theorem lk_bounds : 1 ≤ 1 + Real.log (runOf T S hZ).ka.size ∧ 1 + Real.log (runOf T S hZ).ka.size ≤ 6 * zBase L := by
  have hR := rn_of T S hZ
  have h1 := WeightFamilies.Wt.one_le_size (runOf T S hZ).ka
  have h2 := ka_le T S hZ
  have hA := hR.forty_eight_le_constant
  have hb := hR.b_pos
  constructor
  · have := Real.log_nonneg h1; linarith
  · have a1 : Real.log (runOf T S hZ).ka.size ≤ Real.log (4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b) :=
      Real.log_le_log (by linarith) h2
    have a2 : Real.log (4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b) = Real.log (4 * ((D.R.f : ℝ) * D.R.r)) + L.sc.L := by
      rw [Real.log_mul (by positivity) hb.ne']
      congr 1
      exact Real.log_exp _
    have a3 : Real.log (4 * ((D.R.f : ℝ) * D.R.r)) ≤ 4 * ((D.R.f : ℝ) * D.R.r) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have a4 := A_le_Z L
    have a5 : L.sc.L ≤ zBase L := by
      unfold zBase
      have := one_le_L L
      nlinarith
    linarith

theorem poly_of (B : WeightFamilies.Prov D) (hOb : WeightFamilies.Obound B L 1 2) :
    PolyDom (j := D.R.m) D B L Kc0 (NonvanishingSectionCondition T) T.CP T.eP 2 1 2 1 1 0 (1 / 2) (1 / 2) 0
      (WeightFamilies.PPv D L 1 1 * (1 + Real.log (runOf T S hZ).ka.size)) (runOf T S hZ).ka := by
  have hR := rn_of T S hZ
  have hZ1 : (1 : ℝ) ≤ zBase L := le_trans (by norm_num) hZ
  have hPP := hR.toBs.PP_ge
  have hPP60 : (100 : ℝ) ≤ T.PP := le_trans (by norm_num) hPP
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
  have hDp : (1 : ℝ) ≤ (T.Dp : ℝ) := by
    have := Inh.dimY_pos' D (Inh.h1m D)
    rw [dm_eq T] at this
    exact_mod_cast this
  obtain ⟨l1, l2⟩ := lk_bounds T S hZ
  obtain ⟨p1, p2⟩ := polyA hZ (zBase_pow_twelve_le T hZ1) (growthZero_le_thirty_zBase P) (PO_le L) l1 l2 hDp
  have hPP2 : T.PP ≤ T.PP ^ 2 := by nlinarith
  refine ⟨le_rfl, by norm_num, le_rfl, by norm_num, growthZero_nonneg L, hOb, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, le_rfl,
    le_rfl, ?_⟩
  · show WeightFamilies.RRv D 2 * D.host.rdE ^ 2 ≤ WeightFamilies.RRv D 2 ^ 2
    rw [eRR]; exact le_of_eq (by ring)
  · rw [WeightFamilies.PPv_rec T]; linarith
  · rw [WeightFamilies.PPv_rec T]
    show 4 * (10 : ℝ) ≤ _
    nlinarith
  · rw [WeightFamilies.PPv_rec T]; linarith
  · rw [WeightFamilies.PPv_rec T]; linarith
  · rw [WeightFamilies.PPv_rec T, growth_at_one_eq_zBase]
    exact p1
  · rw [WeightFamilies.PPv_rec T, growth_at_one_eq_zBase, dm_eq T]
    exact p2
  · rw [WeightFamilies.PPv_rec T]; linarith

theorem numRun_of (hCnW : P.CnW = 10) (hg : ∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) (hx : (10 : ℝ) ^ 60 ≤ L.sc.x)
    (e : 𝓞 D.host.E ≃+* D.what₂.O) (Sg : ∀ j, WeightFamilies.Wt D j → Prop) (τ0 : D.what₂.Tau) :
    Inh.NumRun L (Inh.provS D D.host.E e Sg) Kc0 (NonvanishingSectionCondition T) 1 2 1 1 T.CP T.eP 2 L.Ct 0 (1 / 2) (1 / 2) 0
      (WeightFamilies.PPv D L 1 1 * (1 + Real.log (runOf T S hZ).ka.size))
      (runOf T S hZ).ka (runOf T S hZ).wL (runOf T S hZ).wF T.TO T.nP T.nWn (h0R T) τ0 where
  parA := parA_of P S hg hx
  setC := setCn_of T S hZ _ (opo_of P e Sg) (domAt_of P T S hCnW hg hx)
  h3 := third_hypothesis_of_params T S hZ
  h4 := fourth_hypothesis_of_params T S hZ
  g2 := ⟨(runOf T S hZ).w2, (runOf T S hZ).run_isSecondWeight⟩
  Tx := T.TO_poly
  poly := poly_of T S hZ _ (obound_of P e Sg)
  page := le_rfl
  pd := by
    rw [growth_at_one_eq_zBase]
    have := (lk_bounds T S hZ).1
    have hZ0 : (0 : ℝ) ≤ zBase L := le_trans (by positivity) hZ
    exact mul_nonneg hZ0 (by linarith)

end Run

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ReductionUniformizerSmulMem
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem le_of_coe_le_toE {n : ℤ} {a : WithTop ℤ} (h : (((n : ℤ) : ℝ) : EReal) ≤ toE a) : ((n : ℤ) : WithTop ℤ) ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => exact le_top
  | coe m =>
    have h' : (((n : ℤ) : ℝ) : EReal) ≤ (((m : ℤ) : ℝ) : EReal) := h
    exact WithTop.coe_le_coe.2 (by exact_mod_cast h')

theorem ereal_bound {ep T : ℕ} {v d : EReal} {ν t : ℝ} (hd : d = (ν : EReal)) (hv : (t : EReal) ≤ v) :
    (((ep : ℝ) * (t - (T : ℝ) * ν) : ℝ) : EReal) ≤ (ep : EReal) * (v - (T : EReal) * d) := by
  have h1 : ((t - (T : ℝ) * ν : ℝ) : EReal) ≤ v - (T : EReal) * d := by
    rw [hd, EReal.coe_sub, EReal.coe_mul, EReal.coe_natCast]
    exact EReal.sub_le_sub hv le_rfl
  rw [EReal.coe_mul, EReal.coe_natCast]
  exact mul_le_mul_of_nonneg_left h1 (by exact_mod_cast Nat.cast_nonneg ep)

section Val

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {ι : Type*} (y : ι → X.Pt la)

def Dp (u : WeightFamilies.Wt D j) (t : ι → ℝ) : Submodule (𝓞 B.KO) (B.Cusp j u) where
  carrier := {F | ∀ ζ, ((t ζ : ℝ) : EReal) ≤ X.vAt la (y ζ) (X.inc u F)}
  zero_mem' := fun ζ => by rw [map_zero, X.vAt_zero]; exact le_top
  add_mem' := fun {a b} ha hb ζ => by
    rw [map_add]
    exact le_trans (le_min (ha ζ) (hb ζ)) (X.vAt_add la (y ζ) _ _)
  smul_mem' := fun a F hF ζ => by
    by_cases ha : a = 0
    · rw [ha, zero_smul, map_zero, X.vAt_zero]; exact le_top
    · have ha' : algebraMap (𝓞 B.KO) B.KO a ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 B.KO) B.KO)).2 ha
      rw [← algebraMap_smul B.KO a F, map_smul, X.vAt_smul la (y ζ) _ _ ha']
      have h0 : (0 : ℤ) ≤ vAdd la (algebraMap (𝓞 B.KO) B.KO a) :=
        (Formalism.MainNotions.Gaps.SizeBoundsAlt.val_le_one_iff la ha').1 (la.valuation_le_one a)
      have h1 : (0 : EReal) ≤ (((vAdd la (algebraMap (𝓞 B.KO) B.KO a) : ℤ) : ℝ) : EReal) := by exact_mod_cast h0
      calc ((t ζ : ℝ) : EReal) = 0 + (t ζ : ℝ) := (zero_add _).symm
        _ ≤ _ := add_le_add h1 (hF ζ)

theorem mem_Dp {u : WeightFamilies.Wt D j} {t : ι → ℝ} {F : B.Cusp j u} :
    F ∈ Dp X la y u t ↔ ∀ ζ, ((t ζ : ℝ) : EReal) ≤ X.vAt la (y ζ) (X.inc u F) := Iff.rfl

theorem Dp_mono (u : WeightFamilies.Wt D j) {t t' : ι → ℝ} (h : ∀ ζ, t' ζ ≤ t ζ) : Dp X la y u t ≤ Dp X la y u t' :=
  fun _ hF ζ => le_trans (by exact_mod_cast h ζ) (hF ζ)

theorem emb_mul_Dp_le {wL : WeightFamilies.Wt D j} (W : Submodule (𝓞 B.KO) (B.Cusp j wL)) (ν : ι → ℝ)
    (hW : W ≤ Dp X la y wL ν) (u : WeightFamilies.Wt D j) (t : ι → ℝ) :
    X.emb wL W * X.emb u (Dp X la y u t) ≤ X.emb (wadd wL u) (Dp X la y (wadd wL u) fun ζ => ν ζ + t ζ) := by
  refine Submodule.mul_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG, rfl⟩
  obtain ⟨H, hH⟩ := X.inc_mul wL u F G
  refine ⟨H, fun ζ => ?_, hH.symm⟩
  rw [← hH, X.vAt_mul, EReal.coe_add]
  exact add_le_add (hW hF ζ) (hG ζ)

theorem emb_pow_mul_Dp_le {wL : WeightFamilies.Wt D j} (W : Submodule (𝓞 B.KO) (B.Cusp j wL)) (ν : ι → ℝ)
    (hW : W ≤ Dp X la y wL ν) (u : WeightFamilies.Wt D j) (t : ι → ℝ) (n : ℕ) :
    X.emb wL W ^ n * X.emb u (Dp X la y u t) ≤
      X.emb (addL u wL n) (Dp X la y (addL u wL n) fun ζ => (n : ℝ) * ν ζ + t ζ) := by
  induction n with
  | zero =>
    rw [pow_zero, one_mul, addL_zero]
    exact T0.emb_mono X u (Dp_mono X la y u fun ζ => by simp)
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    refine (mul_le_mul' le_rfl ih).trans ((emb_mul_Dp_le X la y W ν hW _ _).trans ?_)
    rw [wadd_addL]
    exact T0.emb_mono X _ (Dp_mono X la y _ fun ζ => by push_cast; linarith)

end Val

section AA

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} {G : GlobalFamilyData X (addL wF wL T) wL wF}
  {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (S : Scal B)

theorem rhoO_embV_mem_AAp (hC : Q.InCurve) (hT : Q.InTie S) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (m : PtsG G la → ℕ)
    (f : B.Cusp j (addL wF wL T))
    (hf : ∀ ζ, ((((-(m ζ : ℤ) : ℤ)) : ℝ) : EReal) ≤ (ep (unifO X la G.N) ζ : EReal) *
      (X.vAt la (Q.y ζ) (X.inc _ f) - (T : EReal) * X.depth S.sW wL la (Q.y ζ))) :
    rhoO G la (embV X la G.N _ f) ∈ Q.AAp T m := by
  refine Submodule.subset_span ⟨toHK X la G.w wF T (embV X la G.N _ f), ⟨fun β _ => ?_, fun β hβ ζ => ?_⟩, rfl⟩
  · exact (mem_HK X la G.w).2 (hasse_presentation X la G.w wF β _
      ((mem_HK X la G.w).1 (toHK X la G.w wF T (embV X la G.N _ f)).2))
  · exact le_of_coe_le_toE ((hf ζ).trans (hasse_order_bound G la Q S T integralClosure_dvr' hC hT hw f β hβ _ ζ))

theorem AAp_mono {m m' : PtsG G la → ℕ} (h : ∀ ζ, m ζ ≤ m' ζ) : Q.AAp T m ≤ Q.AAp T m' := by
  refine Submodule.span_mono (Set.image_mono ?_)
  rintro x ⟨hx, hb⟩
  refine ⟨hx, fun β hβ ζ => le_trans (WithTop.coe_le_coe.2 ?_) (hb β hβ ζ)⟩
  have := h ζ
  omega

theorem AA_le_AAp (m : PtsG G la → ℕ) : Q.AA T ≤ Q.AAp T m := AAp_mono Q fun _ => Nat.zero_le _

theorem smul_Lc_eq (c0 : X.Kl la) (z : Lc X la G.w) : (algebraMap (X.Kl la) (Kp X la G.N) c0) • z = c0 • z := by
  rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply (Kp X la G.N) (Rp X la G.N) (Lc X la G.w),
    IsScalarTower.algebraMap_apply (X.Kl la) (Rp X la G.N) (Lc X la G.w),
    IsScalarTower.algebraMap_apply (X.Kl la) (Kp X la G.N) (Rp X la G.N)]

theorem hasse_smul_Kl (β : Idx D j G.N →₀ ℕ) (c0 : X.Kl la) (z : Lc X la G.w) :
    hasse X la G.w β ((algebraMap (X.Kl la) (Kp X la G.N) c0) • z) =
      (algebraMap (X.Kl la) (Kp X la G.N) c0) • hasse X la G.w β z := by
  rw [smul_Lc_eq, map_smul, smul_Lc_eq]

theorem unifO_pow_eq (e : ℕ) : algebraMap (Op X la G.N) (Kp X la G.N) (unifO X la G.N ^ e) =
    algebraMap (X.Kl la) (Kp X la G.N) (algebraMap (X.Ol la) (X.Kl la) (unif X la ^ e)) := by
  unfold unifO
  rw [← map_pow, ← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la G.N) (Kp X la G.N),
    IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la G.N)]

theorem ordA_unif_smul (hC : Q.InCurve) (ζ : PtsG G la) (e : ℕ) (a : SectionSheafQuotient X la G.w wF) :
    Q.ordA ζ (algebraMap (Op X la G.N) (Kp X la G.N) (unifO X la G.N ^ e) • a) =
      (((e : ℤ) * (ep (unifO X la G.N) ζ : ℤ) : ℤ) : WithTop ℤ) + Q.ordA ζ a := by
  have := isDVRAt_of_curve Q hC ζ
  have hU := isUnif_of_curve Q hC
  have h1 : algebraMap (Op X la G.N) (Kp X la G.N) (unifO X la G.N ^ e) • a =
      (algebraMap (Op X la G.N) (OsK X la G.w) (unifO X la G.N ^ e)) • a := by
    rw [IsScalarTower.algebraMap_apply (Op X la G.N) (Kp X la G.N) (OsK X la G.w)]
    exact (algebraMap_smul (OsK X la G.w) _ a).symm
  unfold LocalPointData.ordA
  rw [h1, ordV_smul Q.c ζ hU hC.2.2, Algebra.algebraMap_eq_smul_one, ord_pow_smul ζ hU, ord_one ζ hU, add_zero]

theorem smul_AAp_mem (hC : Q.InCurve) (e : ℕ) (m m' : PtsG G la → ℕ)
    (h : ∀ ζ, m' ζ ≤ m ζ + e * ep (unifO X la G.N) ζ) {x : WK X la G.w wF (a0 D j T)} (hx : x ∈ Q.AAp T m') :
    unifO X la G.N ^ e • x ∈ Q.AAp T m := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x0, ⟨hx0, hb0⟩, rfl⟩ := hx
    have hc := unifO_pow_eq (X := X) (G := G) (la := la) e
    set c : Kp X la G.N := algebraMap (Op X la G.N) (Kp X la G.N) (unifO X la G.N ^ e) with hcdef
    have hh : ∀ β, hasse X la G.w β ((c • x0 : ↥(HK X la G.w wF)) : Lw X la G.w) =
        c • hasse X la G.w β (x0 : Lw X la G.w) := fun β => by
      rw [hc]; exact hasse_smul_Kl β _ _
    have hx1 : ∀ β : Idx D j G.N →₀ ℕ, β.sum (fun _ n => n) ≤ a0 D j T - 1 →
        hasse X la G.w β ((c • x0 : ↥(HK X la G.w wF)) : Lw X la G.w) ∈ HK X la G.w wF := fun β hβ => by
      rw [hh]; exact (c • (⟨_, hx0 β hβ⟩ : ↥(HK X la G.w wF))).2
    refine Submodule.subset_span ⟨c • x0, ⟨hx1, fun β hβ ζ => ?_⟩, ?_⟩
    · rw [show (⟨hasse X la G.w β ((c • x0 : ↥(HK X la G.w wF)) : Lw X la G.w), hx1 β hβ⟩ : ↥(HK X la G.w wF)) =
        c • ⟨hasse X la G.w β (x0 : Lw X la G.w), hx0 β hβ⟩ from Subtype.ext (hh β), LinearMap.map_smul_of_tower,
        ordA_unif_smul Q hC]
      refine le_trans ?_ (add_le_add le_rfl (hb0 β hβ ζ))
      rw [← WithTop.coe_add]
      refine WithTop.coe_le_coe.2 ?_
      have := h ζ
      push_cast
      have h2 : ((m' ζ : ℕ) : ℤ) ≤ (m ζ : ℤ) + (e : ℤ) * (ep (unifO X la G.N) ζ : ℤ) := by exact_mod_cast this
      linarith
    · rw [LinearMap.map_smul_of_tower]
      rfl
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ih => rw [smul_comm]; exact Submodule.smul_mem _ r ih

theorem depth_eq_nu (hT : Q.InTie S) (ζ : PtsG G la) :
    X.depth S.sW wL la (Q.y ζ) = ((Q.nu S ζ : ℝ) : EReal) := (EReal.coe_toReal (hT ζ).1 (hT ζ).2.1).symm

theorem WWc_le_Dp (hT : Q.InTie S) : X.WWc S.sW wL ≤ Dp X la Q.y wL (Q.nu S) := fun F hF ζ => by
  rw [← depth_eq_nu Q S hT ζ]
  exact iInf₂_le F hF

theorem Mlat_le_Dp (u : WeightFamilies.Wt D j) : B.Mlat j u ≤ Dp X la Q.y u fun _ => 0 := fun F hF ζ => by
  exact_mod_cast (X.Mlat_eq u F).1 hF la (Q.y ζ)

theorem rhoO_mem_of_upO (Ds : Submodule (𝓞 B.KO) (B.Cusp j (addL wF wL T))) (m : PtsG G la → ℕ)
    (h : ∀ F ∈ Ds, rhoO G la (embV X la G.N _ F) ∈ Q.AAp T m) (f : ↥(Vw X la G.N (addL wF wL T)))
    (hf : (f : Rp X la G.N) ∈ upO X la G.N (X.emb _ Ds)) : rhoO G la f ∈ Q.AAp T m := by
  have h1 : f ∈ Submodule.span (Op X la G.N) (embV X la G.N (addL wF wL T) '' (Ds : Set (B.Cusp j (addL wF wL T)))) := by
    rw [mem_span_subtype_iff (R := Op X la G.N) (Vw X la G.N (addL wF wL T))]
    refine Submodule.span_mono ?_ hf
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨embV X la G.N _ F, ⟨F, hF, rfl⟩, rfl⟩
  have h2 : Submodule.span (Op X la G.N) (embV X la G.N (addL wF wL T) '' (Ds : Set (B.Cusp j (addL wF wL T)))) ≤
      (Q.AAp T m).comap (rhoO G la) := by
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact h F hF
  exact h2 h1

theorem le_mm (e : ℕ) (ζ : PtsG G la) :
    (ep (unifO X la G.N) ζ : ℝ) * ((T : ℝ) * Q.nu S ζ - (e : ℝ)) ≤ (Q.mm S T e ζ : ℝ) := by
  unfold LocalPointData.mm
  have h1 := Int.le_ceil ((ep (unifO X la G.N) ζ : ℝ) * ((T : ℝ) * Q.nu S ζ - (e : ℝ)))
  set c := ⌈(ep (unifO X la G.N) ζ : ℝ) * ((T : ℝ) * Q.nu S ζ - (e : ℝ))⌉ with hc
  have h2 : c ≤ ((max 0 c).toNat : ℤ) := by omega
  have h3 : (c : ℝ) ≤ (((max 0 c).toNat : ℤ) : ℝ) := by exact_mod_cast h2
  rw [Int.cast_natCast] at h3
  exact h1.trans h3

theorem mm_zero_le (e : ℕ) (ζ : PtsG G la) : Q.mm S T 0 ζ ≤ Q.mm S T e ζ + e * ep (unifO X la G.N) ζ := by
  unfold LocalPointData.mm
  have h : (ep (unifO X la G.N) ζ : ℝ) * ((T : ℝ) * Q.nu S ζ - ((0 : ℕ) : ℝ)) =
      (ep (unifO X la G.N) ζ : ℝ) * ((T : ℝ) * Q.nu S ζ - (e : ℝ)) + (((e * ep (unifO X la G.N) ζ : ℕ) : ℤ) : ℝ) := by
    push_cast; ring
  rw [h, Int.ceil_add_intCast]
  omega

theorem reduction_integral_mem (hC : Q.InCurve) (hT : Q.InTie S) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL)
    {x : ↥(Vw X la G.N (addL wF wL T))} (hx : x ∈ M1 X la G.N (addL wF wL T)) :
    rhoO G la x ∈ Q.AAp T (Q.mm S T 0) := by
  have h2 : M1 X la G.N (addL wF wL T) ≤ (Q.AAp T (Q.mm S T 0)).comap (rhoO G la) := by
    rw [integralForms_eq_span, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    refine rhoO_embV_mem_AAp Q S hC hT hw _ _ fun ζ => ?_
    refine le_trans ?_ (ereal_bound (t := 0) (depth_eq_nu Q S hT ζ) (Mlat_le_Dp Q _ F.2 ζ))
    refine EReal.coe_le_coe_iff.2 ?_
    have := le_mm Q S (T := T) 0 ζ
    push_cast at this ⊢
    linarith
  exact h2 hx

theorem reduction_uniformizer_smul_mem (hC : Q.InCurve) (hT : Q.InTie S) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (e : ℕ)
    {x : ↥(Vw X la G.N (addL wF wL T))} (hx : x ∈ (M1 X la G.N (addL wF wL T)).map ((unifO X la G.N ^ e) •
      (LinearMap.id : ↥(Vw X la G.N (addL wF wL T)) →ₗ[Op X la G.N] ↥(Vw X la G.N (addL wF wL T))))) :
    rhoO G la x ∈ Q.AAp T (Q.mm S T e) := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  exact smul_AAp_mem Q hC e _ _ (mm_zero_le Q S e) (reduction_integral_mem Q S hC hT hw hy)

theorem reduced_generators_le (hC : Q.InCurve) (hT : Q.InTie S) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL)
    (hth : ∀ i, G.th' i ∈ B.Mlat j wF) : firstLength_le_prime_bound G la T ≤ Q.AA T := by
  rw [reducedGenerators_eq_map, Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.2 ?_
  rintro f ⟨al, i, hal, hf⟩
  refine rhoO_mem_of_upO Q (Dp X la Q.y (addL wF wL T) fun ζ => (T : ℝ) * Q.nu S ζ + 0) _ (fun F hF => ?_) f ?_
  · refine rhoO_embV_mem_AAp Q S hC hT hw _ _ fun ζ => ?_
    refine le_trans ?_ (ereal_bound (depth_eq_nu Q S hT ζ) (hF ζ))
    refine EReal.coe_le_coe_iff.2 ?_
    simp
  · rw [hf]
    have hle : ∑ i, al i ≤ T := le_trans hal.le (Nat.sub_le _ _)
    exact upO_mono la G.N (emb_pow_mul_Dp_le X la Q.y _ _ (WWc_le_Dp Q S hT) wF _ T)
      (secPow_mul_mem_upO la G.w hw al hle (A := X.emb wF (Dp X la Q.y wF fun _ => 0))
        ⟨G.th' i, Mlat_le_Dp Q wF (hth i), rfl⟩)

end AA

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

