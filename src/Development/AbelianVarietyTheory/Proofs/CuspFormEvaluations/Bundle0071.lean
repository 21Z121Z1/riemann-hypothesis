import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageTwoLeLAndSigns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem page_two_le_L_and_signs : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → 2 ≤ large₂.sc.L ∧ 2 ≤ D.R.f ∧ 6 ≤ D.R.r ∧ 0 ≤ lamStar D ∧ (1 ≤ j → 1 ≤ WeightFamilies.dimY D j) ∧ (FamilyHypotheses.SupBoundPageRows D large₂ ka ↔ ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka) := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hc
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hf : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hr : 6 ≤ D.R.r := by unfold Ranks.r; omega
  refine ⟨?_, hf, hr, ?_, ?_, Iff.rfl⟩
  · obtain ⟨-, hS, -⟩ := hp
    have hn : ka.n = D.R.nV := hS.1
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hC, hZ, -⟩ := hS
    obtain ⟨-, -, -, -, hlf, -, -, -, hln⟩ := hc
    by_contra hL
    push_neg at hL
    have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (by omega : 0 < D.R.f)
    have hr0 : (0 : ℝ) < D.R.r := by exact_mod_cast (by omega : 0 < D.R.r)
    have hrn : (D.R.r : ℝ) ≤ ka.n := by
      rw [hn]; exact_mod_cast (by unfold Ranks.nV; omega : D.R.r ≤ D.R.nV)
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have he4 : Real.exp 4 ≤ 81 := by
      have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
        _ = 81 := by norm_num
    have hf1 : (D.R.f : ℝ) ≤ 81 :=
      ((Real.log_le_iff_le_exp hf0).1 (by linarith : Real.log D.R.f ≤ 4)).trans he4
    have hr1 : (D.R.r : ℝ) ≤ 81 :=
      hrn.trans (((Real.log_le_iff_le_exp (hr0.trans_le hrn)).1
        (by linarith : Real.log ka.n ≤ 4)).trans he4)
    have hfr : (D.R.f : ℝ) * D.R.r ≤ 81 * 81 := mul_le_mul hf1 hr1 hr0.le (by norm_num)
    have hZ2 : Zb D large₂ ≤ 81 * 81 * 2 := by
      unfold Zb
      have := mul_pos hf0 hr0
      nlinarith
    have hC2 : (1000 : ℝ) ^ 20 ≤ H.C1 ^ 20 := pow_le_pow_left₀ (by norm_num) hC 20
    have : (81 * 81 * 2 : ℝ) < 1000 ^ 20 := by norm_num
    linarith
  · unfold lamStar
    have h1 := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
    have h2 := Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)
    push_cast at h1 h2
    have e : 4 * ((D.R.f : ℝ) / 2) ^ 2 = (D.R.f : ℝ) ^ 2 := by ring
    rw [e]
    exact add_nonneg h1 h2
  · intro hj
    unfold WeightFamilies.dimY
    have hp5 : 5 ≤ (D.R.sigW j).1 := by
      show 5 ≤ D.R.k + j - 1
      omega
    have h1 : 1 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 := by
      have : 5 * 4 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) := Nat.mul_le_mul hp5 (by omega)
      omega
    exact Nat.mul_pos (by omega) (by omega)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointsInterpolationGenericSections
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem addL_zero_pts {D : D7} {j : ℕ} (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  show wadd u (wsmul 0 wL) = u
  cases u
  simp [wadd, wsmul]

theorem rdg_s_apply {D : D7} {T : Top D} {h : LawsP T} {j : ℕ} {hj : InR D j} {n : SecNorm (recB h.toLawsCore)}
    {R : Rdg (recPlusN h j hj n)} {e : R.Y ≃ DomPt T j} (hR : IsRdgU h j hj n R e) {N : ℕ} {wL : WeightFamilies.Wt D j}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (t : Idx D j N → ℂ) (i : Fin (WeightFamilies.dimY D j + 1)) (y : R.Y) :
    R.s w t i y = ∑ k, t (i, k) * rdR h j (w k) (e y).1 (e y).2.1 := by
  simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]

theorem mem_sp_of_rdOnto {D : D7} {T : Top D} {h : LawsP T} {j : ℕ} {hj : InR D j} {n : SecNorm (recB h.toLawsCore)}
    {R : Rdg (recPlusN h j hj n)} {e : R.Y ≃ DomPt T j} (hR : IsRdgU h j hj n R e) {u : WeightFamilies.Wt D j}
    (hO : RdOnto h j u) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)
    (hf : ∀ k, f k ∈ ((T.U j T.σ₀).X k).SS (laR T j u k)) :
    (fun y => f (e y).1 (e y).2.1) ∈ R.sp u Set.univ := by
  obtain ⟨m, a, F, -, hF⟩ := hO f hf
  have hfun : (fun y => f (e y).1 (e y).2.1) = ∑ i, a i • R.ev ((recPlusN h j hj n).inc u (F i)) := by
    funext y
    rw [hF _ _ (e y).2.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, Set.mem_univ _, rfl⟩)

theorem points_and_interp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → (∀ q, R.s w t 0 (xs q) ≠ 0 ∧ ∀ i : Fin (WeightFamilies.dimY D j), R.s w t i.succ (xs q) = 0) ∧ ∀ v : Fin δ → ℂ, ∃ f ∈ R.sp wF Set.univ, ∀ q, f (xs q) = v q := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hxs hO

  have hvan : ∀ (k : (T.U j T.σ₀).Comp) (a : Fin (nd ((T.U j T.σ₀).X k))) (p : Fin (Fl.Fl k).δ),
      (Fl.Fl k).s a ((Fl.Fl k).xs p) = 0 := by
    intro k a p
    have hb : (fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) ∈
        Bor ((T.U j T.σ₀).X k).Ψ D.R.r := by
      intro τ
      refine ⟨?_, fun a c hca => Matrix.one_apply_ne hca.ne'⟩
      show (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ).det ≠ 0
      simp
    have hself : (Fl.Fl k).xs p = lact 1 (rmul ((Fl.Fl k).xs p)
        (fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ))) := by
      funext τ a c
      simp only [lact, rmul, mat, Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), one_mul]
      have hm : (Matrix.of ((Fl.Fl k).xs p τ) : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) * 1 =
          Matrix.of ((Fl.Fl k).xs p τ) := Matrix.mul_one _
      exact (congrFun (congrFun hm a) c).symm
    exact (((Fl.Fl k).S_eq _ ((Fl.Fl k).xs_mem p)).2
      ⟨p, 1, ((T.U j T.σ₀).X k).Γ.one_mem, _, hb, hself⟩) a
  refine ⟨fun q => ⟨?_, fun i => ?_⟩, fun v => ?_⟩
  · rw [rdg_s_apply hR, hxs q]
    dsimp only
    rw [← Fl.h0]
    exact (Fl.Fl _).w0_ne _
  · rw [rdg_s_apply hR, hxs q]
    dsimp only
    have hs := Fl.hs (en q).1 (Fin.cast (A.dim (en q).1).symm i) ((Fl.Fl (en q).1).xs (en q).2)
    have hi : Fin.cast (A.dim (en q).1) (Fin.cast (A.dim (en q).1).symm i) = i := Fin.ext rfl
    rw [hi] at hs
    rw [← hs]
    exact hvan _ _ _
  ·
    have hF : ∀ k : (T.U j T.σ₀).Comp, ∃ F ∈ ((T.U j T.σ₀).X k).SSgt (A.Xa k).Fp 0,
        ∀ p, F ((Fl.Fl k).xs p) = v (en.symm ⟨k, p⟩) := by
      intro k
      obtain ⟨bb, m, h1, h2, h3⟩ := (A.mar k).1
      exact interpStatement_holds _ _ (A.Xa k) (Fl.Fl k)
        (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
        ⟨bb, m, h1, h2, fun x0 hx0 z hz ξ => by simpa using h3 0 (Set.mem_insert _ _) x0 hx0 z hz ξ⟩
        (A.mar k).2.2.1 (fun P hP => by simpa using (A.mar k).2.2.2.2 0 P (by simpa using hP)) _
    choose F hFmem hFval using hF
    have hO0 : RdOnto h j wF := by
      have h0 := hO 0
      rwa [addL_zero_pts] at h0
    have hf : ∀ k, F k ∈ ((T.U j T.σ₀).X k).SS (laR T j wF k) := by
      intro k
      rw [← A.hF k]
      exact (hFmem k).1
    refine ⟨_, mem_sp_of_rdOnto hR hO0 F hf, fun q => ?_⟩
    show F (e (xs q)).1 (e (xs q)).2.1 = v q
    rw [hxs q]
    exact (hFval _ _).trans (by simp)

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem pPow_size : ∀ (D : D7) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ D.host.q ∧ 1 ≤ D.host.d ∧ 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ∧ (c2 D w : ℝ) * Real.log D.host.QS + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.q + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.d ≤ ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ ∀ a b c : ℕ, 1 ≤ pPow D a b c ∧ Real.log (pPow D a b c) = a * Real.log D.host.QS + b * Real.log D.host.q + c * Real.log D.host.d := by
  intro D j w
  have hq : 1 ≤ D.host.q := by have := D.host.qd_big.1; omega
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hqR : (1 : ℝ) ≤ D.host.q := by exact_mod_cast hq
  have hdR : (1 : ℝ) ≤ D.host.d := by exact_mod_cast hd
  have hlq : 0 ≤ Real.log D.host.q := Real.log_nonneg hqR
  have hld : 0 ≤ Real.log D.host.d := Real.log_nonneg hdR
  have hQ : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hl2 : 0 ≤ Real.log D.host.QS := Real.log_nonneg hQ
  have hQf : (D.host.QS : ℝ) ≤ 4 * ((D.R.f : ℝ) / 2) ^ 2 := by
    have h1 : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
    have h2 : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
    rw [h2]; nlinarith [sq_nonneg (D.R.n : ℝ)]
  have hlf : Real.log D.host.QS ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) := Real.log_le_log (by linarith) hQf
  have hlog : Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) =
      Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) + Real.log D.host.q + Real.log D.host.d := by
    have h0 : (0 : ℝ) < 4 * ((D.R.f : ℝ) / 2) ^ 2 := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul h0.ne' (by positivity)]
  have hD : (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := Nat.cast_nonneg _
  refine ⟨hq, hd, ?_, ?_, ?_, ?_⟩
  · rw [hlog]; linarith
  · apply Real.log_nonneg
    have h0 : (1 : ℝ) ≤ D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).one_le
    have h1 : (1 : ℝ) ≤ D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).one_le
    nlinarith
  · have hc2 : (c2 D w : ℝ) = (WeightAlgebra.DF w : ℝ) := rfl
    have hch : (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) ≤ (WeightAlgebra.DF w : ℝ) + 1 := by
      have h1 := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) / 2 by positivity)).le
      unfold Formalism.MainNotions.DIV.Cons.cHalf
      linarith
    have a1 := mul_le_mul_of_nonneg_left hlf hD
    have a2 := mul_le_mul_of_nonneg_right hch hlq
    have a3 := mul_le_mul_of_nonneg_right hch hld
    rw [hlog, hc2]
    nlinarith
  · intro a b c
    have hQ0 : 0 < D.host.QS := D.host.QS_pos
    refine ⟨?_, ?_⟩
    · unfold pPow
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · unfold pPow
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem pageRows_of_pageAt : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → PageAt large₂ C2 A2 → 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka ∧ 16 ≤ D.R.f := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hPg hCK
  have hm4 := EtaleWeightGaps.lift_index_pow_four_le_degree hPg
  obtain ⟨Q, PT, -, hC, hA⟩ := hPg
  have hPP : WeightFamilies.PPv D large₂ C2 A2 = PT.PP := by rw [← hC, ← hA]; exact WeightFamilies.PPv_rec PT
  obtain ⟨hA', hS, -, h4, -⟩ := hp
  obtain ⟨-, -, -, -, hg, -, -, hp1, hp2, -⟩ := hA'
  obtain ⟨hn, -, -, -, -, -, -, hsz, -, -, -, -, -, -, -, -, -, hT, -⟩ := hS
  obtain ⟨-, -, -, hP3, -⟩ := h4
  rw [hPP] at hCK hP3
  have hL := EtaleWeightGaps.Num.Pm.one_le_L large₂
  have hf2 := EtaleWeightGaps.Num.Pm.two_le_f D
  have hr6 := EtaleWeightGaps.Num.Pm.six_le_r D
  have hm2 := EtaleWeightGaps.Num.Pm.two_le_m D
  have hkr := EtaleWeightGaps.Num.Pm.k_le_r D
  have hrt := EtaleWeightGaps.Num.Pm.r_le_alt_alt D
  have hlf := EtaleWeightGaps.Num.Pm.log_f_le Q
  have hlr := EtaleWeightGaps.Num.Pm.log_r_le Q
  obtain ⟨hlc, hlt⟩ := EtaleWeightGaps.Num.Pm.log_cond_le Q
  have hb : Real.log large₂.sc.b = large₂.sc.L := EtaleWeightGaps.Num.Pm.log_b large₂
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  have hf0 : (0 : ℝ) < D.R.f := by linarith
  have hr0 : (0 : ℝ) < D.R.r := by linarith
  have hP0 : 0 < PT.PP := PT.PP_pos (by unfold zBase; positivity)
  refine ⟨⟨hg, ?_, ?_, ?_, ?_, hp1, hp2, ?_, ?_⟩, ?_⟩
  · rw [EtaleWeightGaps.Num.Pm.lrd_eq]; linarith [log_rdE_le_scL Q]
  · have hd := EtaleWeightGaps.Num.Pm.one_le_d D
    have hq := EtaleWeightGaps.Num.Pm.one_le_q D
    have h1 : (D.host.d : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by
      rw [EtaleWeightGaps.Num.Pm.condE_cast]
      have hS : (1 : ℝ) ≤ (D.host.QS : ℝ) := by exact_mod_cast D.host.QS_pos
      have : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q := by nlinarith
      nlinarith
    linarith [Real.log_le_log (by linarith) h1]
  · linarith [Q.ccK_log]
  · linarith
  · have hs : 1 + (WeightAlgebra.DF ka : ℝ) ≤ ka.size := by
      unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
      have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (ka.n : ℝ) := by positivity
      push_cast at h2 ⊢
      linarith
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hT1 : (1 : ℝ) ≤ (Tn : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hT)
    have hP3' : PT.PP ^ 3 ≤ large₂.sc.b := (le_mul_of_one_le_right (by positivity) hT1).trans hP3
    have hlP : 3 * Real.log PT.PP ≤ large₂.sc.L := by
      have := Real.log_le_log (by positivity) hP3'
      rw [Real.log_pow, hb] at this
      exact_mod_cast this
    have h1 : H.CK ≤ PT.PP ^ 2 * D.R.f := by
      have : 0 ≤ PT.PP ^ 2 * D.R.f := by positivity
      linarith
    have h2 : H.CK * D.R.k ≤ PT.PP ^ 2 * D.R.f * D.R.r := mul_le_mul h1 hkr hk0 (by positivity)
    have h3 : H.CK * D.R.k * D.R.f * large₂.sc.b ≤ PT.PP ^ 2 * D.R.f * D.R.r * D.R.f * large₂.sc.b := by gcongr
    have h4 := Real.log_le_log (by positivity) (hs.trans (hsz.trans h3))
    rw [Real.log_mul (by positivity) hb0.ne', Real.log_mul (by positivity) hf0.ne',
      Real.log_mul (by positivity) hr0.ne', Real.log_mul (by positivity) hf0.ne', Real.log_pow, hb] at h4
    push_cast at h4
    linarith
  · have h1 : (ka.n : ℝ) ≤ (D.R.t : ℝ) ^ 2 := by
      rw [hn]; unfold Ranks.nV; push_cast; nlinarith
    have h2 : (0 : ℝ) < ka.n := by rw [hn]; unfold Ranks.nV; push_cast; linarith
    have h3 := Real.log_le_log h2 h1
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  · have : (2 : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hm2 4
    have h : (16 : ℝ) ≤ D.R.f := by linarith
    exact_mod_cast h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSize
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gc_arith (f r L A n s lam lp a b M : ℝ) (hf : 2 ≤ f) (hr : 6 ≤ r) (hL : 2 ≤ L) (hA : 0 ≤ A)
    (hn : 1 ≤ n) (hs : A + f * r * n + 1 ≤ s) (hlam : 0 ≤ lam) (hlp : 0 ≤ lp) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : a + b ≤ M) :
    (140 * r * L * A + 10 * L * A + 200 * f * r * n * L ≤ 400 * (f * r * L) * s) ∧
    (2 * (lam + 2 * lp) * s + 400 * (f * r * L) * s + lam * s ≤
      (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s) ∧
    ((lam + 2 * lp) * s + (400 * (f * r * L) * s + 3 * f * r * n * L + 5 * a + b + 2) ≤
      (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s) := by
  have hfr : 12 ≤ f * r := by nlinarith
  have hrf : r ≤ f * r := by nlinarith
  obtain ⟨F, hF⟩ : ∃ F, F = f * r := ⟨_, rfl⟩
  rw [← hF] at hfr hrf hs
  have hFn : F ≤ F * n := by nlinarith
  have hnF : n ≤ F * n := by nlinarith
  have hs3 : 13 ≤ s := by linarith
  have hAs : A ≤ s := by linarith
  have hns : n ≤ s := by linarith
  have hFns : F * n ≤ s := by linarith
  have hZ : 24 ≤ F * L := by nlinarith
  have hLZ : L ≤ F * L := by nlinarith
  have hrL : r * L ≤ F * L := by nlinarith
  have hZs : 24 ≤ F * L * s := by nlinarith
  have h1 : r * L * A ≤ F * L * s := mul_le_mul hrL hAs hA (by linarith)
  have h2 : L * A ≤ F * L * s := mul_le_mul hLZ hAs hA (by linarith)
  have h3 : F * L * n ≤ F * L * s := mul_le_mul_of_nonneg_left hns (by linarith)
  have hLs : 0 ≤ L * s := by positivity
  have hM0 : 0 ≤ M := by linarith
  have hMs : M * 13 ≤ M * s := mul_le_mul_of_nonneg_left hs3 hM0
  have hlams : 0 ≤ lam * s := by positivity
  have hlps : 0 ≤ lp * s := by positivity
  have h4 : 12 * (lam * s) ≤ F * (lam * s) := mul_le_mul_of_nonneg_right hfr hlams
  have h5 : 12 * (lp * s) ≤ F * (lp * s) := mul_le_mul_of_nonneg_right hfr hlps
  have e : (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s =
      1040 * (F * L * s) + 3 * (L * s) + 2 * (M * s) + 2 * (F * (lam * s)) + 4 * (F * (lp * s)) := by
    rw [hF]; ring
  have e1 : 400 * (f * r * L) * s = 400 * (F * L * s) := by rw [hF]; ring
  have e2 : 200 * f * r * n * L = 200 * (F * L * n) := by rw [hF]; ring
  have e3 : 3 * f * r * n * L = 3 * (F * L * n) := by rw [hF]; ring
  have e4 : 140 * r * L * A = 140 * (r * L * A) := by ring
  have e5 : 10 * L * A = 10 * (L * A) := by ring
  have e6 : 2 * (lam + 2 * lp) * s = 2 * (lam * s) + 4 * (lp * s) := by ring
  have e7 : (lam + 2 * lp) * s = lam * s + 2 * (lp * s) := by ring
  rw [e, e1, e2, e3, e4, e5, e6, e7]
  refine ⟨by linarith, by linarith, by linarith⟩

theorem lamStar_nonneg_nat (D : D7) : 0 ≤ lamStar D := by
  unfold lamStar
  have h1 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    have := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
    simpa only [Nat.cast_mul] using this
  have h2 : 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := by
    have := Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)
    have e : 4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d =
        ((D.R.f ^ 2 * D.host.q * D.host.d : ℕ) : ℝ) := by push_cast; ring
    rw [e]; exact this
  linarith

theorem sup_bounds_le_Gc : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (p : ℕ), 2 ≤ large₂.sc.L → 0 < w.n → (140 * D.R.r * large₂.sc.L * absA w + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L ≤ 400 * Zb D large₂ * w.size) ∧ (2 * (lamStar D + 2 * Real.log p) * w.size + 400 * Zb D large₂ * w.size + lamStar D * w.size ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) ∧ ((lamStar D + 2 * Real.log p) * w.size + (400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) := by
  intro D B large₂ j w p hL hn
  have hf : (2 : ℝ) ≤ D.R.f := by
    have : 2 ≤ D.R.f := by
      unfold Ranks.f Ranks.n
      have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity)
      omega
    exact_mod_cast this
  have hr : (6 : ℝ) ≤ D.R.r := by
    have : 6 ≤ D.R.r := by
      unfold Ranks.r
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      omega
    exact_mod_cast this
  have hA : 0 ≤ absA w := by unfold absA; positivity
  have hn' : (1 : ℝ) ≤ w.n := by exact_mod_cast hn
  have hs : absA w + (D.R.f : ℝ) * D.R.r * w.n + 1 ≤ w.size := by
    unfold WeightFamilies.Wt.size absA
    have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
    have : (D.R.f : ℝ) * D.R.r * w.n ≤
        (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hm h0]
    linarith
  have hb : 0 ≤ Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [Real.log_abs]
    exact Real.log_intCast_nonneg _
  unfold WeightAlgebra.Gc Zb
  exact gc_arith _ _ _ _ _ _ _ _ _ _ _ hf hr hL hA hn' hs (lamStar_nonneg_nat D)
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg _) hb (le_max_left _ _)

end GlobalTheory.RunIn
end

