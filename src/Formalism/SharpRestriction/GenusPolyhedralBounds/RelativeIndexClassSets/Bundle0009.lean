import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0008
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.BaseDegreeAtLiftIndex
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PvsDimYPos

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NonvanishingSectionCondition
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem dm_eq (T : ParamsT D L P) : WeightFamilies.dimY D D.R.m = T.Dp := by
  rw [T.Dp_eq]
  unfold WeightFamilies.dimY Ranks.sigW Ranks.r
  simp [Nat.choose_two_right]

theorem order_le_modulus (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) : T.TO ≤ q0N T := by
  unfold q0N
  have hT40 := T.TO_40
  have hTpos : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast (show 0 < T.TO by omega)
  have hZ' : (1 : ℝ) ≤ zBase L := by
    have h : (1 : ℝ) ≤ 10 ^ 60 := by norm_num
    linarith
  have hPP : 1 ≤ T.PP := by
    rw [T.PP_eq]
    exact one_le_mul_of_one_le_of_one_le T.one_le_CP (Real.one_le_rpow hZ' (by linarith [T.eP_ge]))
  have hbpos : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have h1 : (T.TO : ℝ) ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (le_mul_of_one_le_right hTpos.le hPP) T.TO_PP'
  have h2 := mul_self_le_mul_self hTpos.le h1
  rw [← Real.rpow_add hbpos] at h2
  norm_num at h2
  have hq : (T.TO : ℝ) ≤ L.sc.b / (T.TO : ℝ) := by
    rw [le_div_iff₀ hTpos]
    linarith
  exact_mod_cast le_trans hq (Nat.le_ceil _)

abbrev runOf (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) : RunN D where
  T := T.TO
  nW := T.nWn
  nP := T.nP
  Q0 := q0N T
  T_pos := by have := T.TO_40; omega
  nW_even := T.nW_even
  even_nP₂ := T.even_nP₂
  split := T.split
  nP_le_nW := T.nW_lo.2.2
  hQ0 := by
    rw [dm_eq T]
    have := T.TO_nW; have := order_le_modulus T S hZ
    omega

def Kc0 : KAdm := ⟨1, 1, 1, 1, 1, 1, 1, 1, 2⟩

def NonvanishingSectionCondition (T : ParamsT D L P) : KHyp := ⟨10, 20, 1000, 12, T.CP, T.eP, 2⟩

section Run

variable (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L)

theorem eTq : ((runOf T S hZ).Tq : ℝ) = (T.TO : ℝ) + ((T.Dp : ℝ) + 2) := by
  unfold RunN.Tq Tp
  dsimp only [runOf]
  rw [dm_eq T]
  push_cast
  ring

theorem eQ : ((runOf T S hZ).Q : ℝ) = (T.TO : ℝ) + ((T.Dp : ℝ) + 2) + 2 * D.R.r := by
  unfold RunN.Q
  push_cast
  linarith [eTq T S hZ]

theorem ekl : ((runOf T S hZ).kl : ℝ) =
    ((T.Dp : ℝ) + 2) * T.nWn + 2 * D.R.r + ((T.TO : ℝ) + ((T.Dp : ℝ) + 2)) * (q0N T : ℝ) := by
  unfold RunN.kl
  push_cast
  rw [eTq T S hZ]
  have hd : (Dm D : ℝ) = (T.Dp : ℝ) := by
    first
    | (unfold Dm; exact_mod_cast dm_eq T)
    | (simp only [Dm]; exact_mod_cast dm_eq T)
    | exact_mod_cast dm_eq T
  rw [hd]

theorem enV : (D.R.nV : ℝ) = (T.nP : ℝ) + (T.TO : ℝ) * T.nWn := by
  have h := T.split
  unfold Ranks.nV
  exact_mod_cast h

theorem ka_le : (runOf T S hZ).ka.size ≤ 4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).sK ?_
  have h := (runOf T S hZ).ka_size_le
  rw [ekl, eTq, eQ, enV T] at h
  exact h

theorem b_le_kl : L.sc.b ≤ ((runOf T S hZ).kl : ℝ) := by
  rw [ekl T S hZ]
  have hT40 := T.TO_40
  have hTpos : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast (show 0 < T.TO by omega)
  have hq : L.sc.b / (T.TO : ℝ) ≤ (q0N T : ℝ) := by unfold q0N; exact Nat.le_ceil _
  have hq' : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℝ) := by
    rw [div_le_iff₀ hTpos] at hq
    linarith
  have h0 : (0 : ℝ) ≤ (T.Dp : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (T.nWn : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (q0N T : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (D.R.r : ℝ) := by positivity
  nlinarith [mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h1,
    mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h2]

theorem b_le_ka : L.sc.b ≤ (runOf T S hZ).ka.size := (b_le_kl T S hZ).trans (runOf T S hZ).ka_size_ge

theorem wL_le : (runOf T S hZ).wL.size * (T.TO : ℝ) ≤ 2 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).sL ?_
  have h := (runOf T S hZ).wL_size_le
  rw [eQ] at h
  exact h

theorem dF_le : (DF (runOf T S hZ).wL : ℝ) ≤ 2 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).dL ?_
  have h := (runOf T S hZ).DF_wL_le
  rw [eQ] at h
  exact h

theorem g_ge (P : ParameterChoice' D L) (i : Fin 2) : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) := by
  obtain ⟨Y, h1, -, -, h2⟩ := P.g_Y
  exact h1.trans (h2 i).1

theorem qq_ge (P : ParameterChoice' D L) : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (qq D : ℝ) := by
  unfold qq
  first
  | (rw [Nat.cast_min]; exact le_min (g_ge P 0) (g_ge P 1))
  | (push_cast; exact le_min (g_ge P 0) (g_ge P 1))

theorem eRR : WeightFamilies.RRv D 2 = D.host.rdE ^ 2 := by
  unfold WeightFamilies.RRv
  first
  | rfl
  | simp

theorem eg0 : (g0 D : ℝ) = 1250 * D.R.r := by
  unfold g0
  push_cast
  ring

theorem growth_at_one_eq_zBase : WeightFamilies.PPv D L 1 1 = zBase L := by
  unfold WeightFamilies.PPv
  simp

theorem third_hypothesis_of_params : H3 L (NonvanishingSectionCondition T) T.CP T.eP 2 0 (runOf T S hZ).wL T.TO := by
  have hR := rn_of T S hZ
  have hd0 : (0 : ℝ) ≤ (DF (runOf T S hZ).wL : ℝ) := Nat.cast_nonneg _
  have hd := dF_le T S hZ
  have hq := qq_ge P
  have hq0 : (0 : ℝ) < (qq D : ℝ) := lt_of_lt_of_le (by have := hR.b_pos; have := hR.k1; positivity) hq
  have hb := hR.h3b hd0 hd hq
  have hx1 : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hm0 : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T]
    exact hR.h3a hd0 hd hq
  · rw [Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T, eg0]
    exact hb
  · rw [Real.rpow_zero, one_mul, WeightFamilies.PPv_rec T, dm_eq T]
    refine le_trans ?_ T.TO_ge
    have hden : 0 < (D.R.m : ℝ) * L.de2 := mul_pos hm0 L.thickDensity_pos
    apply div_le_div_of_nonneg_right _ hden.le
    have hP := hR.PP_pos
    exact le_mul_of_one_le_right (by positivity) hx1
  · show (T.TO : ℝ) * (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * g0 D ≤ 1
    rw [eRR, WeightFamilies.PPv_rec T, eg0]
    have e : (T.TO : ℝ) * (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * (1250 * D.R.r) =
        ((T.TO : ℝ) * (1250 * D.R.r) * D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2) / (qq D : ℝ) := by ring
    rw [e, div_le_one hq0]
    exact hb
  · show (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * WeightFamilies.RRv D 2 ^ 2 *
      (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) ≤ 1 / 2
    rw [eRR, WeightFamilies.PPv_rec T]
    have hfm : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 4 := by
      have : (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 3 := pow_le_pow_left₀ hm0.le hmk 3
      calc (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) * (D.R.k : ℝ) ^ 3 :=
            mul_le_mul hfk this (by positivity) (by positivity)
        _ = (D.R.k : ℝ) ^ 4 := by ring
    have he := hR.h3e hd0 hd hq (fm := (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3) (by positivity) hfm
    have e : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 *
        (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) =
        ((D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 *
        (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2)) / (qq D : ℝ) := by ring
    rw [e, div_le_iff₀ hq0]
    linarith
  · rw [dm_eq T]
    have := hR.h3f hd0 hd hq
    have e : (T.Dp : ℝ) + 2 + 2 = (T.Dp : ℝ) + 4 := by ring
    rw [e] at this
    exact this

end Run

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocal
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem deepC (large₂ : SizeData₂ D) (X : PJ D B P j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T nP nW : ℕ) (h0 CK C1 A1 Gc Prw CG AG p Pd : ℝ)
    (hC : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0)
    (tW : G.TiedW S Gc Prw) (tZ : G.TiedZ S T Gc) (dH : DeepHerm X ka) (dS : DeepSubMul X) (dL : DeepLogD X ka Pd)
    (pG : PageGd X ka large₂ CG AG Pd) (hG0 : 0 ≤ Gc) (hP0 : 0 ≤ Prw)
    (hlat : Submodule.IsLattice B.KO (B.Mlat j ka))
    (hLAM : ∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 → -(p * ka.size) ≤ WeightFamilies.meanLogSup B F)
    (hS2 : ∀ (F : B.Cusp j ka) (σ : B.KO →+* ℂ), B.supN j ka σ F ^ 2 ≤
      Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) * B.l2NormAlt j ka σ F ^ 2) :
    Summable (fun la => (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la) ∧
      ∑' la, (SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la ≤
        G.rz * ((2 * Gc + Prw + p + 3 / 2 * (Pd + PO D large₂)) * ka.size) := by
  obtain ⟨hk, -, -, -, -, -, -, -, -, -, -, -, -, hV, hIL, hIF, -, -, hD, -, -, h40, -, -, hO, -⟩ := hC
  obtain ⟨-, hwM, hrw, hmx, hmxm⟩ := tW
  obtain ⟨hz0, hz, hWd⟩ := tZ
  obtain ⟨dd, Hm, hconj⟩ := dH
  have hwt := SizeBoundsAlt.hwt_of X ka wL wF T nP nW hIF hIL.1 (hk.trans hV) hD
  obtain ⟨z', hz1, hz2⟩ := SizeBoundsAlt.exists_zFam X ka wL (X.wF0 wL wF) (a0 D j T) hwt G.w hwM G.th0 (fun k => (hz0 k).2.1)
    G.alz (fun k => (hz0 k).2.2.2)
  have hzM : ∀ k β, G.zc k β ∈ B.Mlat j ka := by
    intro k β
    have : G.zc k β = z' k β := X.inc_inj ka ((hz k β).trans (hz1 k β).symm)
    rw [this]; exact hz2 k β
  exact deepPacketP large₂ X ka wL (X.wF0 wL wF) (a0 D j T) hwt G.w G.th0 G.alz (fun k => (hz0 k).2.2.2) G.zc hz _
    (fun la => SizeBoundsAlt.gaussC_nonneg _ G.zc la) (SizeBoundsAlt.gaussC_gaussLe hzM) hWd Hm
    (fun Ctr hC => SizeBoundsAlt.trans_of_minima _root_.transference_successive_minima _ hlat.span_eq_top Hm hconj Ctr hC)
    dS p hLAM Gc Prw Pd
    (fun σ F => (hS2 F σ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr pG) (sq_nonneg _)))
    hG0 hP0 G.mx (fun σ k => (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (hmx σ k))) hmxm
    (fun k => (hz0 k).2.2.1) (vanishingOrder_le_weight_size ka T nP nW (hk.trans hV) (lt_of_lt_of_le (by norm_num) h40)) hrw dL hO

theorem quotC {large₂ : SizeData₂ D} {X : PJ D B P j} {K : KAdm} {H : KHyp} {Ch Ah Cq Aq C2 A2 CR CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    {Gc PH Prw Pet Pd : ℝ}
    (hQ : j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL))
    (hH : HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (G : GlobalFamilyData X ka wL wF)
    (tQ : G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka) :
    Summable (fun la => lenQ G K.CRm T (cc D large₂ C2 A2 CR wL) la * X.lN la) ∧
      ∑' la, lenQ G K.CRm T (cc D large₂ C2 A2 CR wL) la * X.lN la ≤ 2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by
  by_cases hj : j < D.R.m
  · obtain ⟨-, hS, -, -, -, h3, -, -⟩ := hH
    obtain ⟨hrq, -, hspan, hsup⟩ := tQ
    have hT : 0 < T := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact (quotCoreE large₂ ka (T : ℝ) (cc D large₂ C2 A2 CR wL)
      (hQ hj (le_trans (by norm_num) hP.1) hP.2.2.2.2.2.1 hS.1 (lastPos_of_SetC hS) hS.2.2.2.2.2.2.2.1
        (by exact_mod_cast hT) (cc_pos_of hS h3 hP) (T_mul_cc_le_one h3 hP)) G.rq hrq G.th hspan hsup).2
  · obtain ⟨hs, h0'⟩ := lenQ_tsum_of_ge (X := X) G (not_lt.1 hj) K.CRm T (cc D large₂ C2 A2 CR wL)
    refine ⟨hs, ?_⟩
    have hrq : G.rq = 0 := by
      rw [tQ.1]
      exact rhoP_eq_zero_of_rho (rho_eq_zero_of_ge (not_lt.1 hj)) _ _ _ ka
    rw [h0', hrq]
    simp

theorem rLa_tsum_le_comb (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) {ka wL wF : WeightFamilies.Wt D j}
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus)
    (lA : LatAt B j ka) (sA : SupBoundByL2AtWeight large₂ B j ka K.CG K.AG) (mA : LAMwAt large₂ B j ka K.CL K.AL)
    (qA : j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL))
    (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ)
    (tW : G.TiedW S Gc Prw) (tZ : G.TiedZ S T Gc) (tQ : G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah)
    (dH : DeepHerm (X j h1 h2) ka) (dS : DeepSubMul (X j h1 h2)) (dL : DeepLogD (X j h1 h2) ka Pd)
    (pG : PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd)
    (hP : PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka)
    (Qf : ∀ la, LocalPointData G la) (hHt : Heights Qf Gc PH Prw Pet) :
    Summable (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la) ∧
    ∑' la, rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL) * (X j h1 h2).lN la ≤
      (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((∑' la, ((Qf la).Ila.toNat : ℝ) * (X j h1 h2).lN la) +
        (if j < D.R.m then (T : ℝ) * (max 0 (cc D large₂ C2 A2 CR wL) / (2 * (G.iet : ℝ))) *
          ∑' la, (Qf la).Net * (X j h1 h2).lN la else 0)) +
      G.rz * ((2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) * ka.size) +
      2 * (G.rq : ℝ) * WeightFamilies.PPv D large₂ Cq Aq * ka.size := by
  obtain ⟨hCs, hCb⟩ := deepC large₂ (X j h1 h2) G S T nP nW h0 H.CK H.C1 H.A1 Gc Prw K.CG K.AG
    (WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size)) Pd hH.2.1 tW tZ dH dS dL pG hP.2.2.1 hP.2.2.2.1 lA mA sA
  obtain ⟨hQs, hQb⟩ := quotC qA hH G tQ hP
  obtain ⟨hs, he⟩ := rLa_tsum_split Qf K.CRm T (cc D large₂ C2 A2 CR wL) hHt.2.1 (fun hj => (hHt.2.2.2 hj).1) hCs hQs
  refine ⟨hs, ?_⟩
  rw [he]
  linarith

theorem sumC : SumC D B P := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA G Gc PH Prw Pet Pd
    tW tTh tZ tQ tEt dH dS dL pG sRd sRho sRhoP hP hB Qf hHt
  obtain ⟨hs, hb⟩ := rLa_tsum_le_comb large₂ X K H Ch Ah Cq Aq C2 A2 CR CT h1 h2 S T nP nW h0 nus hH lA sA mA qA G Gc PH Prw Pet Pd
    tW tZ tQ dH dS dL pG hP Qf hHt
  exact ⟨hs, hb.trans (sumGC large₂ (X j h1 h2) h1 K H Ch Ah Cq Aq C2 A2 CR CT S T nP nW h0 nus hH G Gc PH Prw Pet Pd
    tTh dL sRd sRho sRhoP hP Qf hHt)⟩

theorem theorem_zero_split_of_local (hL : LocalC D B P) : Conclusion1OfComb (D := D) (B := B) (P := P) := theorem_zero_split_of_local_and_sum hL sumC

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ZeroGeneratorsLeThetaSpan
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Up

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

def upO (A : Submodule (𝓞 B.KO) X.Forms) : Submodule (Op X la N) (Rp X la N) :=
  Submodule.span (Op X la N) (emb X la N '' (A : Set X.Forms))

variable {X}

theorem emb_mem_upO {A : Submodule (𝓞 B.KO) X.Forms} {F : X.Forms} (h : F ∈ A) : emb X la N F ∈ upO X la N A :=
  Submodule.subset_span ⟨F, h, rfl⟩

theorem upO_mono {A A' : Submodule (𝓞 B.KO) X.Forms} (h : A ≤ A') : upO X la N A ≤ upO X la N A' :=
  Submodule.span_mono (Set.image_mono h)

theorem upO_mul_le (A A' : Submodule (𝓞 B.KO) X.Forms) : upO X la N A * upO X la N A' ≤ upO X la N (A * A') := by
  unfold upO
  rw [Submodule.span_mul_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  exact ⟨a * b, Submodule.mul_mem_mul ha hb, map_mul _ _ _⟩

theorem upO_pow_le (A : Submodule (𝓞 B.KO) X.Forms) (n : ℕ) : upO X la N A ^ n ≤ upO X la N (A ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Submodule.one_le]
    exact Submodule.subset_span ⟨1, Submodule.one_le.1 le_rfl, map_one _⟩
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (mul_le_mul' ih le_rfl).trans (upO_mul_le la N _ _)

theorem mem_span_emb_iff {ka : WeightFamilies.Wt D j} {M : Submodule (𝓞 B.KO) X.Forms} (hM : M ≤ X.Msup ka) (f : ↥(Vw X la N ka)) :
    f ∈ Submodule.span (Op X la N) {f : ↥(Vw X la N ka) | ∃ F ∈ M, (f : Rp X la N) = emb X la N F} ↔
      (f : Rp X la N) ∈ upO X la N M := by
  rw [mem_span_subtype_iff (R := Op X la N) (Vw X la N ka)]
  have h : ((↑) '' {f : ↥(Vw X la N ka) | ∃ F ∈ M, (f : Rp X la N) = emb X la N F} : Set (Rp X la N)) =
      emb X la N '' (M : Set X.Forms) := by
    ext x
    constructor
    · rintro ⟨f, ⟨F, hF, hf⟩, rfl⟩; exact ⟨F, hF, hf.symm⟩
    · rintro ⟨F, hF, rfl⟩
      obtain ⟨F', _, rfl⟩ := hM hF
      exact ⟨⟨_, emb_mem_Vw X la N ka F'⟩, ⟨_, hF, rfl⟩, rfl⟩
  rw [h]
  rfl

end Up

section Sec

variable {X : PJ D B P j} (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
  {W : Submodule (𝓞 B.KO) (B.Cusp j wL)}

theorem sec_mem_upO (hw : ∀ k, w k ∈ W) (i : Fin (WeightFamilies.dimY D j + 1)) : sec X la w i ∈ upO X la N (X.emb wL W) := by
  unfold sec
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ _ (emb_mem_upO la N ⟨w k, hw k, rfl⟩)

theorem secPow_mem_upO (hw : ∀ k, w k ∈ W) (al : Fin (WeightFamilies.dimY D j) → ℕ) :
    secPow X la w al ∈ upO X la N (X.emb wL W) ^ ∑ i, al i := by
  unfold secPow
  have h : ∀ s : Finset (Fin (WeightFamilies.dimY D j)),
      ∏ i ∈ s, sec X la w i.succ ^ al i ∈ upO X la N (X.emb wL W) ^ ∑ i ∈ s, al i := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]; exact Submodule.one_le.1 le_rfl
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
      exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (sec_mem_upO la w hw _) _) ih
  exact h Finset.univ

theorem secPow_mul_mem_upO (hw : ∀ k, w k ∈ W) (al : Fin (WeightFamilies.dimY D j) → ℕ) {n : ℕ} (hn : ∑ i, al i ≤ n)
    {A : Submodule (𝓞 B.KO) X.Forms} {F : X.Forms} (hF : F ∈ A) :
    secPow X la w al * sec X la w 0 ^ (n - ∑ i, al i) * emb X la N F ∈ upO X la N (X.emb wL W ^ n * A) := by
  refine upO_mul_le la N _ _ (Submodule.mul_mem_mul (upO_pow_le la N _ _ ?_) (emb_mem_upO la N hF))
  have h := Submodule.mul_mem_mul (secPow_mem_upO (X := X) la w hw al)
    (Submodule.pow_mem_pow _ (sec_mem_upO (X := X) la w hw 0) (n - ∑ i, al i))
  rwa [← pow_add, Nat.add_sub_cancel' hn] at h

end Sec

section Chain

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B)

theorem thetaSpan_le_integralForms (hΘ : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T)) :
    Th1 X la G.N (addL wF wL T) S wL wF T ≤ M1 X la G.N (addL wF wL T) :=
  Submodule.span_mono (Set.image_mono (Submodule.comap_mono (Submodule.span_mono (Set.image_mono hΘ))))

theorem mem_thetaSpan_iff (hΘ : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T))
    (f : ↥(Vw X la G.N (addL wF wL T))) : f ∈ Th1 X la G.N (addL wF wL T) S wL wF T ↔
      (f : Rp X la G.N) ∈ upO X la G.N (X.Theta S (addL wF wL T) wL wF T) := by
  rw [Th1_eq X la G.N _ S wL wF T hΘ]
  exact mem_span_emb_iff la G.N hΘ f

theorem generators_le_thetaSpan (hΘ : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T))
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hth : ∀ i, G.th' i ∈ X.Thc S.sF wF) :
    N1 G la ≤ Th1 X la G.N (addL wF wL T) S wL wF T := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨al, i, hal, hf⟩
  refine (mem_thetaSpan_iff G la S hΘ f).2 ?_
  rw [hf]
  have hle : ∑ i, al i ≤ T := le_trans hal.le (Nat.sub_le _ _)
  exact upO_mono la G.N (le_sup_of_le_left le_sup_left)
    (secPow_mul_mem_upO la G.w hw al hle (A := X.emb wF (X.Thc S.sF wF)) ⟨G.th' i, hth i, rfl⟩)

theorem zeroGenerators_le_thetaSpan (hΘ : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T))
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hth : ∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF))
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T) :
    Zl G la ≤ Th1 X la G.N (addL wF wL T) S wL wF T := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨k, hf⟩
  refine (mem_thetaSpan_iff G la S hΘ f).2 ?_
  rw [hf]
  have h := secPow_mul_mem_upO la G.w hw (G.alz k) (n := a0 D j T) (hal k).le
    (A := X.emb (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF))) ⟨G.th0 k, hth k, rfl⟩
  rw [hal k, Nat.sub_self, pow_zero, mul_one] at h
  exact upO_mono la G.N (le_sup_of_le_left le_sup_right) h

end Chain

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

