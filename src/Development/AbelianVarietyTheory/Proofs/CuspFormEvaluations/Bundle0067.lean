import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0060
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0066
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0062
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

noncomputable section

namespace GlobalTheory.Shares.WtDic

variable {D : D7}

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_conjEmb {E : Type} [Field E] (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun x => by simp [conjEmb]

theorem tauEmb_ne_conj (t t' : D.what₂.Tau) : DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 : conjEmb (DV.tauEmb D t') =
      D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    exact (Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm
  have h2 := (Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩
  exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2

theorem wtA_tau {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj, this]
  · simp

theorem wtA_conj {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [(tauEmb_ne_conj _ _).symm]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h => ht' (tauEmb_inj (by
      have := congrArg conjEmb h
      rwa [conjEmb_conjEmb, conjEmb_conjEmb] at this)).symm
    simp [(tauEmb_ne_conj _ _).symm, this]
  · simp

theorem matrixExtendByZero_mul {p : ℕ} (c : ℕ) (f : Fin p → ℕ) (i : ℕ) : ext0 (fun k => c * f k) i = c * ext0 f i := by
  unfold ext0; split_ifs <;> rfl

theorem wtA_wsmul {j : ℕ} (c : ℕ) (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA (wsmul c w) x = c * wtA w x := by
  simp only [wtA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((wsmul c w).aP t) x.2 = c * ext0 (w.aP t) x.2 := matrixExtendByZero_mul _ _ _
  have h2 : ext0 ((wsmul c w).aM t) x.2 = c * ext0 (w.aM t) x.2 := matrixExtendByZero_mul _ _ _
  rw [h1, h2]
  split_ifs <;> ring

theorem wtA_wscalar (j n : ℕ) (hn : Even n) (x : (D.host.E →+* ℂ) × ℕ) : wtA (wscalar D j n hn) x = 0 := by
  simp only [wtA]
  refine Finset.sum_eq_zero fun t _ => ?_
  have h1 : ext0 ((wscalar D j n hn).aP t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl
  have h2 : ext0 ((wscalar D j n hn).aM t) x.2 = 0 := by unfold ext0; split_ifs <;> rfl
  rw [h1, h2]
  simp

theorem laR_wadd (T : Top D) (j : ℕ) (k : (T.U j T.σ₀).Comp) (u u' : WeightFamilies.Wt D j) :
    laR T j (wadd u u') k = laR T j u k + laR T j u' k := by
  funext τ a
  have hn : (wadd u u').n / 2 = u.n / 2 + u'.n / 2 := by
    have h1 := u.n_even
    have h2 := u'.n_even
    rw [n_wadd]
    rw [Nat.even_iff] at h1 h2
    omega
  simp only [laR, laU, Pi.add_apply, wtA_wadd, hn]
  split_ifs <;> push_cast <;> ring

theorem laR_wsmul (T : Top D) (j : ℕ) (k : (T.U j T.σ₀).Comp) (m : ℕ) (u : WeightFamilies.Wt D j) :
    laR T j (wsmul m u) k = m • laR T j u k := by
  funext τ a
  have hn : (wsmul m u).n / 2 = m * (u.n / 2) := by
    obtain ⟨s, hs⟩ := u.n_even
    show m * u.n / 2 = _
    rw [hs, ← two_mul, Nat.mul_div_cancel_left _ two_pos, Nat.mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
  simp only [laR, laU, Pi.smul_apply, wtA_wsmul, hn, nsmul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem card_lower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  have e : {p : Fin r × Fin r // p.2 < p.1} ≃ Σ a : Fin r, Finset.Iio a :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Finset.mem_Iio.2 p.2⟩
      invFun := fun x => ⟨(x.1, x.2.1), Finset.mem_Iio.1 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_coe, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem choose_split (p q : ℕ) : (p + q) * (p + q - 1) / 2 = p * q + p * (p - 1) / 2 + q * (q - 1) / 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

theorem weights_dictionary : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (k : (T.U j T.σ₀).Comp), (∀ u u' : WeightFamilies.Wt D j, laR T j (wadd u u') k = laR T j u k + laR T j u' k) ∧ (∀ (m : ℕ) (u : WeightFamilies.Wt D j), laR T j (wsmul m u) k = m • laR T j u k) ∧ (∀ (u v : WeightFamilies.Wt D j) (m : ℕ), laR T j (addL u v m) k = laR T j u k + m • laR T j v k) ∧ (∀ i : ℕ, laR T j (etWt D j i) k = (i * (g0 D / 2)) • de2W ((T.U j T.σ₀).X k)) ∧ nd ((T.U j T.σ₀).X k) = WeightFamilies.dimY D j ∧ ((T.U j T.σ₀).X k).p0 = (D.R.sigW j).2 ∧ ((T.U j T.σ₀).X k).Ψ.card = D.R.f ∧ ∃ tt : ((T.U j T.σ₀).X k).Ψ ≃ D.what₂.Tau, ∀ (u : WeightFamilies.Wt D j) (τ : ((T.U j T.σ₀).X k).Ψ) (a : Fin D.R.r), laR T j u k τ a = if ((T.U j T.σ₀).X k).p0 ≤ (a : ℕ) then (ext0 (u.aP (tt τ)) ((a : ℕ) - ((T.U j T.σ₀).X k).p0) : ℤ) + ((u.n / 2 : ℕ) : ℤ) else -(ext0 (u.aM (tt τ)) (((T.U j T.σ₀).X k).p0 - 1 - (a : ℕ)) : ℤ) - ((u.n / 2 : ℕ) : ℤ) := by
  intro D T h j hj k
  obtain ⟨hr, hk, -⟩ := h.unf j hj T.σ₀ T.good_σ₀
  obtain ⟨hp0, hΨ⟩ := hk k
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  have hc : Fintype.card ((T.U j T.σ₀).X k).Ψ = D.R.f := by
    have h1 := GlobalTheory.RunIn.WtSize.two_mul_card_cm ((T.U j T.σ₀).X k)
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame.finrank_eq D] at h1
    omega
  refine ⟨laR_wadd T j k, laR_wsmul T j k, fun u v m => ?_, fun i => ?_, ?_, hp0.trans hq, ?_, ?_⟩
  · rw [addL, laR_wadd, laR_wsmul]
  · funext τ a
    have hn : (etWt D j i).n / 2 = i * (g0 D / 2) := by
      show g0 D * i / 2 = _
      unfold g0
      rw [mul_assoc 2, mul_assoc 2, Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos, mul_comm]
    have hw : ∀ x, wtA (etWt D j i) x = 0 := wtA_wscalar _ _ _
    simp only [laR, laU, Pi.smul_apply, hw, hn, nsmul_eq_mul, de2W]
    split_ifs <;> simp
  · rw [nd, Fintype.card_prod, hc, card_lower, WeightFamilies.dimY, ← choose_split, hr, hp, hq]
  · rw [← hc, Fintype.card_coe]
  · let f : D.what₂.Tau → ((T.U j T.σ₀).X k).Ψ := fun t => ⟨DV.tauEmb D t, (hΨ _).2 (h.pins.1.2.2.2 t)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun t t' e => tauEmb_inj (congrArg Subtype.val e), fun τ => ?_⟩
      obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q h.pins.1 τ.1 ((hΨ _).1 τ.2)
      exact ⟨t, Subtype.ext ht.symm⟩
    have hinv : ∀ τ, Function.invFun (relab T.Q.c T.σ₀) τ = τ := fun τ =>
      Function.leftInverse_invFun (GlobalTheory.RunIn.WtSize.relab_bijective T.Q.c T.σ₀).1 τ
    refine ⟨(Equiv.ofBijective f hf).symm, fun u τ a => ?_⟩
    obtain ⟨t, rfl⟩ := (Equiv.ofBijective f hf).surjective τ
    rw [Equiv.symm_apply_apply]
    have e : ((Equiv.ofBijective f hf) t).1 = DV.tauEmb D t := rfl
    simp only [laR, laU, hinv, e, wtA_tau, wtA_conj]

end GlobalTheory.Shares.WtDic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjHalfIntegralGenerator
section
namespace GlobalTheory.CMConjugationOfSquareRoot

open NumberField Complex
open scoped ComplexConjugate

theorem conj_eq_neg_of_sq_eq_neg {z : ℂ} {d : ℝ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) :
    conj z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by linarith) with h0 | h0
    · exact h0
    · rw [h0] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hre0]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem complexConj_rt (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    IsCMField.complexConj E ((H.rt : 𝓞 E) : E) = -((H.rt : 𝓞 E) : E) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply conj_eq_neg_of_sq_eq_neg (d := (H.d : ℝ)) (by exact_mod_cast H.d_prime.pos)
  have h := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
  simpa using h

theorem conj_halfIntegralGenerator (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ReciprocityTheory.ChartRestriction.G.FD.cc ((H.w0 : 𝓞 E) : E) = (1 : E) - ((H.w0 : 𝓞 E) : E) := by
  have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.two_weight_eq_one_add_root
    push_cast at this
    exact this
  have h3 : (2 : E) * IsCMField.complexConj E (H.w0 : E) = 1 - (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    rw [map_mul, map_add, map_one, complexConj_rt] at this
    have h22 : IsCMField.complexConj E (2 : E) = 2 := map_ofNat _ 2
    rw [h22] at this
    rw [this]; ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.cc
  apply mul_left_cancel₀ (two_ne_zero : (2 : E) ≠ 0)
  rw [h3, mul_sub, h2]; ring

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ReciprocityTheory.ChartRestriction.G.FD.cc (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H) : E) = (1 : E) - (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H) : E) := fun H => conj_halfIntegralGenerator H

end GlobalTheory.CMConjugationOfSquareRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormHalfSupAtOrthonormalFrameFirstMin
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem half_sup_at_ortho_frame : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, 0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) → ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧ supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤ 2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧ 0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 80 * large₂.sc.L := by
  intro D T hL hG large₂ j hj w hrows hL2 hn hlast σ hσ f hf hsup
  have hfs : f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf
  have hRS := (hL.unf j hj σ hσ).2.2.2.2.1 (wtA w) w.n (dom_wtA w) f hfs
  unfold Formalism.L2.Pj.supN at hsup ⊢
  have hStop : Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≠ ⊤ := by
    intro h
    rw [h] at hsup
    simp at hsup
  have hSpos : 0 < Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) :=
    (ENNReal.toReal_pos_iff.mp hsup).1
  have hhalf := ENNReal.half_lt_self hSpos.ne' hStop
  have hhalf' := hhalf
  unfold Formalism.L2.Pj.supE at hhalf'
  obtain ⟨⟨k, x, hx⟩, hp⟩ := lt_iSup_iff.mp hhalf'
  have hB := (hRS k).2.1
  have hb := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem ((T.U j σ).X k) hx
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom ((T.U j σ).X k) hx hb
  have ho := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf ((T.U j σ).X k) hx
  have hpn := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k)
    (rdU (T.U j σ) f k) hB x hx _ hb
  have hu1 : ∀ τ i, ‖dmin ((T.U j σ).X k).Gm
      (rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf ((T.U j σ).X k) x)) τ i‖ = 1 :=
    fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho ((T.U j σ).X k) ho τ i
  have hpu := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit ((T.U j σ).X k)
    (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) hu1
  have hrd := Formalism.L2.Pj.rdU_mem (T.U j σ) f k hy
  have hlt := (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top hStop two_ne_zero)
    ENNReal.ofReal_ne_top).mpr hp
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal'] at hlt
  have hlt' : (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal / 2 <
      max (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x) 0 := by
    simpa using hlt
  have hm : 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x := by
    rcases lt_max_iff.mp (lt_trans (half_pos hsup) hlt') with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  rw [max_eq_left hm.le] at hlt'
  have hle : ∀ z ∈ ((T.U j σ).X k).dom,
      ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z ≤
        (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal := by
    intro z hz
    have h1 : ENNReal.ofReal (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z) ≤
        Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) := by
      unfold Formalism.L2.Pj.supE
      exact le_iSup_of_le (⟨k, ⟨z, hz⟩⟩ : Formalism.L2.Pj.FPt (T.U j σ).X) le_rfl
    exact (ENNReal.ofReal_le_iff_le_toReal hStop).mp h1
  refine ⟨k, ⟨_, hy⟩, hu1, ho, ?_, ?_⟩
  · rw [← hrd, ← hpu, hpn]
    linarith
  · exact GlobalTheory.T.firstMinimum_bound_at_halfSupremum_cuspForm D T hL hG large₂ j hj w hrows hL2 hn σ hσ f hf k _ hy
      (fun z hz => by rw [hpn]; linarith [hle z hz]) (by rw [hpn]; exact hm)

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAlgIndependentCoeffsFlatDatum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
open MeasureTheory

namespace GlobalTheory.GenericFlat

theorem ae_cast {a b n m : ℕ} (hab : a = b) (hnm : n = m) (P : (Fin (a + 1) × Fin n → ℂ) → Prop)
    (hP : ∀ᵐ t : Fin (a + 1) × Fin n → ℂ, P t) :
    ∀ᵐ t : Fin (b + 1) × Fin m → ℂ,
      P fun p => t (Fin.cast (congrArg (· + 1) hab) p.1, Fin.cast hnm p.2) := by
  subst hab hnm
  simpa using hP

theorem exists_generic_flatAt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1), ∃ t : Idx D j N → ℂ, (∀ Q : MvPolynomial (Idx D j N) T.Q.c.F, Q ≠ 0 → MvPolynomial.eval₂ T.σ₀ t Q ≠ 0) ∧ Nonempty (FlatAt h j A t) := by
  intro D T h j _hj N wL wF w Tn c1 A
  have hC : Countable T.Q.c.F := (Module.finBasis ℚ T.Q.c.F).equivFun.injective.countable

  have hk : ∀ k : (T.U j T.σ₀).Comp, ∀ᵐ t : Fin (WeightFamilies.dimY D j + 1) × Fin N → ℂ,
      ∃ Fl : FlatM ((T.U j T.σ₀).X k) (A.Xa k),
        (∀ x, Fl.w0 x = ∑ i, t (0, i) * rdR h j (w i) k x) ∧
        ∀ a x, Fl.s a x = ∑ i, t ((Fin.cast (A.dim k) a).succ, i) * rdR h j (w i) k x := by
    intro k
    have H := GlobalTheory.T.ae_exists_flat_datum_linearCombination _ _ ((T.U j T.σ₀).X k) (A.Xa k) T.Q.c.F T.σ₀ (A.rel k)
    refine (ae_cast (A.dim k) (A.hN k) _ H).mono ?_
    rintro t ⟨Fl, h0, hs⟩
    refine ⟨Fl, fun x => ?_, fun a x => ?_⟩
    · rw [h0]
      refine Fintype.sum_equiv (finCongr (A.hN k)) _ _ fun i => ?_
      simp only [A.hw k i, finCongr_apply]
      congr 2
    · rw [hs]
      refine Fintype.sum_equiv (finCongr (A.hN k)) _ _ fun i => ?_
      simp only [A.hw k i, finCongr_apply]
      congr 2

  have hall := (ae_all_iff.2 hk).and
    (GlobalTheory.ae_eval₂_ne_zero_of_countable T.Q.c.F T.σ₀ (Fin (WeightFamilies.dimY D j + 1) × Fin N))
  obtain ⟨t, ht, hg⟩ := hall.exists
  choose Fl h0 hs using ht
  exact ⟨t, hg, ⟨⟨Fl, h0, hs⟩⟩⟩

end GlobalTheory.GenericFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortSpanThetaTieOfScalars
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem exists_short_span_thetaTie_of_scalars : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (C1 A1 Gc : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), ScalB large₂ X C1 A1 S ka wL wF Tn → EtaleWeightGaps.GrowthConstantBound large₂ B Gc → ∃ Sh : Finset (B.Cusp j wF), Submodule.span B.KO (Sh : Set (B.Cusp j wF)) = ⊤ ∧ (∀ g ∈ Sh, g ∈ X.Thc S.sF wF ∧ WeightFamilies.meanLogSup B g ≤ Gc * wF.size) ∧ ∀ G : EtaleWeightGaps.GlobalFamilyData X ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh S Gc := by
  intro D B P j X large₂ C1 A1 Gc S ka wL wF Tn hS hG
  obtain ⟨-, -, -, -, -, po, hpo, -, PLam, hPLam, -, ⟨Sh, hSub, hSpan, hMean⟩, -, -⟩ := hS

  have hconst : Formalism.MainNotions.WeightAlgebra.Gc large₂ B PLam po ≤ Gc := by
    refine le_trans ?_ (hG po hpo)
    unfold Formalism.MainNotions.WeightAlgebra.Gc
    linarith
  have hbound : Formalism.MainNotions.WeightAlgebra.Gc large₂ B PLam po * wF.size ≤ Gc * wF.size :=
    mul_le_mul_of_nonneg_right hconst (le_trans zero_le_one wF.one_le_size)
  refine ⟨Sh, hSpan, fun g hg => ⟨hSub hg, (hMean g hg).trans hbound⟩, fun G hG' i => ?_⟩
  exact ⟨hSub (hG' i), (hMean _ (hG' i)).trans hbound⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSmulMemLattice
section
namespace GlobalTheory.SmulMemOfSpan

open NumberField

theorem exists_smul_mem_of_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin r → E)) (v : Fin r → E)
    (hv : v ∈ Submodule.span E (L : Set (Fin r → E))) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ (c : E) • v ∈ L := by
  have hL : ∀ (n : RingOfIntegers E) (w : Fin r → E), w ∈ L → (n : E) • w ∈ L := by
    intro n w hw
    rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    exact L.smul_mem n hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [RingOfIntegers.coe_eq_algebraMap, map_one, one_smul]
    exact hx
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have e : ((c * d : RingOfIntegers E) : E) • (x + y) =
        (d : E) • ((c : E) • x) + (c : E) • ((d : E) • y) := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
      ring
    rw [e]
    exact L.add_mem (hL d _ hcx) (hL c _ hdy)
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨n, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) a
    have hy0 : algebraMap (RingOfIntegers E) E y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    refine ⟨y * c, mul_ne_zero (nonZeroDivisors.ne_zero hy) hc, ?_⟩
    have e : ((y * c : RingOfIntegers E) : E) •
        ((algebraMap (RingOfIntegers E) E n / algebraMap (RingOfIntegers E) E y) • x) =
        (n : E) • ((c : E) • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
      field_simp
    rw [e]
    exact hL n _ hcx

theorem exists_smul_mem_lattice : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E), ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ (↑c : E) • v ∈ ReciprocityTheory.ChartRestriction.G.FD.Data.Λ X := by
  intro E _ _ _ r X v
  refine exists_smul_mem_of_span X.Λ v ?_
  rw [X.Λ_span]
  exact Submodule.mem_top

end GlobalTheory.SmulMemOfSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsValueBasisInSpanningForms
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem exists_indep_of_span_image {α : Type} {δ : ℕ} (S : Set α) (v : α → Fin δ → ℂ)
    (h : Submodule.span ℂ (v '' S) = ⊤) :
    ∃ θ : Fin δ → α, (∀ i, θ i ∈ S) ∧ LinearIndependent ℂ fun i => v (θ i) := by
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent ℂ (v '' S)
  rw [h] at hsp
  let bs : Module.Basis b ℂ (Fin δ → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp])
  let e : Fin δ ≃ b := (Pi.basisFun ℂ (Fin δ)).indexEquiv bs
  choose θ hθ hv using fun i : Fin δ => hb (e i).2
  refine ⟨θ, hθ, ?_⟩
  have : (fun i => v (θ i)) = (Subtype.val : b → Fin δ → ℂ) ∘ e := funext hv
  rw [this]
  exact hli.comp e e.injective

theorem ev_mem_sp_of_mem_span {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) (s : Set (B.Cusp j u)) (F : B.Cusp j u) (hF : F ∈ Submodule.span B.KO s) :
    R.ev (X.inc u F) ∈ R.sp u s := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul, R.ev_smul]; exact Submodule.smul_mem _ _ hx

theorem exists_valueBasis_in_spanning (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j)
    (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ)
    (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y) (hA : AnFacts R w t ka wF T Mg xs)
    (Sh : Set (B.Cusp j wF)) (hS : Submodule.span B.KO Sh = ⊤) :
    ∃ θ : Fin δ → B.Cusp j wF, (∀ i, θ i ∈ Sh) ∧
      LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (θ i))) := by
  refine exists_indep_of_span_image Sh (fun F q => R.ev (X.inc wF F) (xs q)) ?_
  rw [eq_top_iff]
  intro v _
  obtain ⟨f, hf, hv⟩ := hA.interp v
  have h1 : R.sp wF Set.univ ≤ R.sp wF Sh := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, -, rfl⟩
    exact ev_mem_sp_of_mem_span R wF Sh F (hS ▸ Submodule.mem_top)
  have h2 : LinearMap.funLeft ℂ ℂ xs f ∈ (R.sp wF Sh).map (LinearMap.funLeft ℂ ℂ xs) :=
    Submodule.mem_map_of_mem (h1 hf)
  rw [Rdg.sp, Submodule.map_span, Set.image_image] at h2
  have h3 : v = LinearMap.funLeft ℂ ℂ xs f := funext fun q => (hv q).symm
  rw [h3]
  exact h2

end GlobalTheory.Shares
end

