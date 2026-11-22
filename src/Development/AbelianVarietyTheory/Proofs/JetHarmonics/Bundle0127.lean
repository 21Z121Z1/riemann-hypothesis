import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0034
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddFirstSecond
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0064
import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexConjFrobeniusDepthContentBoundProof
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinPartCanonGaugeCongr
section
set_option autoImplicit false

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeIntCut
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart)

namespace GlobalTheory

theorem bilinPart_canonGauge_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → (∀ i j, ((bilinPart k h)ᵀ - bilinPart k h) i j ∈ (algebraMap R k).range) ∧ (∀ a : O, (∀ i j, ((dAct k B a)ᵀ * bilinPart k h - bilinPart k h * dAct k B (star a)) i j ∈ (algebraMap R k).range)) ∧ (∀ a : O, (∀ i j, (dAct k B a) i j ∈ (algebraMap R k).range)) ∧ dAct k B 1 = 1 ∧ (∀ a b : O, dAct k B (a + b) = dAct k B a + dAct k B b) ∧ ∀ a b : O, dAct k B (a * b) = dAct k B a * dAct k B b := by
  intro R _ d O _ _ k _ _ _ B h hc
  refine ⟨fun i j => ?_, fun a i j => ?_, fun a i j => ?_, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_one k B,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add k B, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul k B⟩
  · have e := congrArg (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1)) hc.sy
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_expS_two _ (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_swap_sub_low h hc.ax0 hc.ax1) _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz i j), map_sub, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_swap', coeff_map,
      Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single, add_comm (Finsupp.single (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.swE d _) 1)] at e
    exact ⟨_, e⟩
  · obtain ⟨r, hr⟩ := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.M_int B h hc a j i
    refine ⟨-r, ?_⟩
    rw [map_neg, hr]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gaugeBilinearTerm_eq_neg_double_sum, bilinPart,
      neg_mul, Finset.sum_neg_distrib, mul_comm (dAct k B _ _ _)]
    ring
  · exact ⟨coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act a i), by
      unfold dAct FB.actK; rw [coeff_map]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinearLogFormEvalZeroRightEqZero
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeIntCut
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart dLin)

namespace GlobalTheory.GaugeShift

open ReciprocityTheory.ChartRestriction.G.TB.LogPf (CZ ev_sub ev_zeroFam logOf)
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix (bilL lg)
open GlobalTheory.TwistCheck (ev_bilL cc_log bilL_mixed balanced_iff)

variable {S : Type} [CommRing S] {d : ℕ}

theorem cz2 {n : ℕ} {a b : Pt S n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    CZ (![a, b] : Fin 2 → Pt S n d) := by
  intro j i
  fin_cases j
  · exact ha i
  · exact hb i

theorem coeff_mixed (g : PS S 2 d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), l) 1) g =
      constantCoeff (pderiv S ((0 : Fin 2), i) (pderiv S ((1 : Fin 2), l) g)) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, coeff_pderiv, zero_add]
  simp

variable [Algebra ℚ S]

theorem ev_zero_log {n : ℕ} (G : FGLaw S d) (i : Fin d) : ev (n := n) ![0] (logOf G i) = 0 := by
  have e : (![0] : Fin 1 → Pt S n d) = fun _ _ => 0 := by
    funext j c; fin_cases j; rfl
  rw [e, ev_zeroFam, cc_log, map_zero]

theorem cz0 {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt S n d) i) = 0 := by simp

theorem bilinearLogForm_eval_zero_left_eq_zero (G : FGLaw S d) (c : Fin d → Fin d → S) : ev (n := 1) ![0, pt S d 0] (bilL G c) = 0 := by
  rw [ev_bilL G c (cz2 cz0 (FBMap.cz_pt _))]
  simp [ev_zero_log]

theorem bilinearLogForm_eval_zero_right_eq_zero (G : FGLaw S d) (c : Fin d → Fin d → S) : ev (n := 1) ![pt S d 0, 0] (bilL G c) = 0 := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) cz0)]
  simp [ev_zero_log]

theorem bilL_add_left (G : FGLaw S d) (c : Fin d → Fin d → S) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1), pt S d 2] (bilL G c) =
      ev (n := 3) ![pt S d 0, pt S d 2] (bilL G c) + ev (n := 3) ![pt S d 1, pt S d 2] (bilL G c) := by
  rw [ev_bilL G c (cz2 (CIndFrFix2c.constantCoeff_add_first_second G) (FBMap.cz_pt _)), ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _)),
    ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CIndFrFix2c.formal_log_add_first_two, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem bilL_add_right (G : FGLaw S d) (c : Fin d → Fin d → S) :
    ev (n := 3) ![pt S d 0, G.add (pt S d 1) (pt S d 2)] (bilL G c) =
      ev (n := 3) ![pt S d 0, pt S d 1] (bilL G c) + ev (n := 3) ![pt S d 0, pt S d 2] (bilL G c) := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) (CIndFrFix2b.constantCoeff_add_second_third G)), ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _)),
    ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CIndFrFix2b.formal_log_add_last_two, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem bilL_swap (G : FGLaw S d) (c : Fin d → Fin d → S) (hs : ∀ i l, c i l = c l i) :
    ev (n := 2) ![pt S d 1, pt S d 0] (bilL G c) = bilL G c := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, bilL, lg, smul_eq_C_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hs l i, mul_comm (ev _ _)]

theorem canon_sub_bilin : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ β : Matrix (Fin d) (Fin d) k, βᵀ = β → (∀ a : O, (dAct k B a)ᵀ * β = β * dAct k B (star a)) → ∃ h' : PS k 2 d, B.IsCanonGauge k h' ∧ bilinPart k h' = bilinPart k h - β := by
  intro R _ d O _ _ k _ _ _ B h hc β hs hb
  let G : FGLaw k d := FBMap.mapG (algebraMap R k) B.G
  let A : OAct O G := FBMap.mapA (algebraMap R k) B.A
  have hF : B.FK k = G.F := rfl
  have hA : ∀ a, B.actK k a = A.act a := fun _ => rfl
  have p {n : ℕ} (j : Fin n) := FBMap.cz_pt (R := k) (d := d) j
  have q (a : O) (j : Fin 2) := FBMap.cz_comp1 (A.act a) (A.const a) (pt k d j) (p j)
  refine ⟨h - bilL G β, ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩, ?_⟩
  · rw [ev_sub (cz2 cz0 (p _)), hc.ax0, bilinearLogForm_eval_zero_left_eq_zero G β, sub_zero]
  · rw [ev_sub (cz2 (p _) cz0), hc.ax1, bilinearLogForm_eval_zero_right_eq_zero G β, sub_zero]
  · rw [hc.ph1, hF, ev_sub (cz2 (p _) (p _)), ev_sub (cz2 (p _) (p _)),
      ev_sub (cz2 (CIndFrFix2c.constantCoeff_add_first_second G) (p _)), bilL_add_left G β]
    congr 1; ring
  · rw [hc.ph2, hF, ev_sub (cz2 (p _) (p _)), ev_sub (cz2 (p _) (p _)),
      ev_sub (cz2 (p _) (CIndFrFix2b.constantCoeff_add_second_third G)), bilL_add_right G β]
    congr 1; ring
  · rw [hc.sy, ev_sub (cz2 (p _) (p _)), bilL_swap G β (fun i l => congrFun (congrFun hs l) i)]
    congr 1; ring
  · have hbal := (balanced_iff G A a (star a) β).1 (hb a)
    rw [hc.ad a, hA, hA, ev_sub (cz2 (q _ _) (p _)), ev_sub (cz2 (p _) (q _ _)), hbal]
    congr 1; ring
  · funext i l
    have := coeff_mixed (bilL G β) i l
    rw [bilL_mixed G β] at this
    simp only [bilinPart, map_sub, this, Matrix.sub_apply]

end GlobalTheory.GaugeShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartValuesBoundProductsOnPlanes
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem valO_self : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb] (I0 : Orb → Type) [∀ o, Fintype (I0 o)] (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V) (Ls : LetSys C dd) (N n : ℕ) (pl : Fin N × Fin 2 ↪ Fin n) (ν : ℝ), SelfSep Y p → (ν : EReal) ≤ Y.nuPlE Ls n → RF.ValO (fun o => (Y.rawSelf (p o)).rowData (H o)) N (imgFamS Y p Ls pl) ν := by
  intro C _ _ V O _ _ dd Y d _ Orb _ I0 _ p H Ls N n pl ν hs hν
  rintro Po ⟨P, hP, hQ⟩ kind hk S t ht gr hg
  have h := hν.trans (val_self Y p H Ls n hs (GlobalTheory.T.valEqSelfSt_of_hyps C V O dd Y d Orb I0 p H Ls n) N pl P hP Po hQ kind hk S t ht gr hg)
  exact WithBot.coe_le_coe.1 h

end GlobalTheory.RowAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudSizesBetweenZeroAndTwiceB
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem sizes_le_two_mul : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → L.Sc + L.etaSz ≤ 2 * L.sc.b ∧ ∀ j, InR D j → (∀ τ, 0 ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b) ∧ (∀ t, wj D j (plOf D (false, t)) ≤ 2 * L.sc.b') ∧ ∀ z, (numOf D L).w j z = wj D j (plOf D z) := by
  intro D L P hx hkb
  have hk : (5 : ℝ) ≤ D.R.k := by
    have : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    exact_mod_cast this
  have hx0 : 0 < L.sc.x := by linarith
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    positivity
  have hbb : 5 * L.sc.b' ≤ L.sc.b := le_trans (by nlinarith) hkb
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' / 3 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  have hw0 : 0 < L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' / 3 := by
    unfold Scale.w''
    exact div_le_div_of_nonneg_left hb'.le (by norm_num) (by nlinarith)
  have ht := L.t_win.1
  have he1 : 1 ≤ L.etaSz := le_trans ht P.t_le_eta
  have he : L.etaSz ≤ L.sc.b' / 9 := by
    have h1 := P.teta
    have h2 : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n / 3 :=
      div_le_div_of_nonneg_left hw0.le (by norm_num) hx
    nlinarith
  have hS0 := L.Sc_pos
  have hS : L.Sc ≤ L.sc.b' / 3 := by
    have := P.kS_le
    nlinarith
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  have hLa : 0 < L.LaG := by
    have h1 : 0 < L.LaG * L.sc.b' / D.R.k := by have := P.S_le; linarith
    have h2 : 0 < L.LaG * L.sc.b' := (div_pos_iff_of_pos_right hk0).1 h1
    exact (mul_pos_iff_of_pos_right hb').1 h2
  have hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
    intro t
    have h1 := P.bT_le t
    have h2 := P.rho_le
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h4 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
      have := P.Crho_pos
      have := Real.log_nonneg (show 1 ≤ L.sc.x by linarith)
      positivity
    unfold LevelStarExponents.rhoP at h2
    set A := LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k with hA
    have h5 : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * A := by rw [hA]; ring
    have h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = A * L.sc.b' := by rw [hA]; ring
    have h7 : A ≤ 1 / 4 := by linarith
    rw [h6] at h1
    nlinarith
  refine ⟨by linarith, fun j hj => ?_⟩
  have hoff : ∀ τ, (D.eTau τ : D.R.GG) ∉ D.host.thickPlaces →
      0 ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b' := by
    intro τ hτ
    by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at htop
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 htop
      obtain ⟨h1, h2⟩ := L.win_top j hj.1 hj.2 τ ⟨t, htT⟩ hteq.symm
      have h3 := hbT ⟨t, htT⟩
      have h4 := L.bT_ge ⟨t, htT⟩
      have h5 : 0 ≤ L.sc.b' / L.sc.x := by positivity
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := L.win_thin j hj.1 hj.2 τ ⟨(D.eTau τ).2, htop, hτ⟩
      constructor <;> linarith
  refine ⟨fun τ => ?_, fun t => (hoff _ ?_).2, fun z => ?_⟩
  · by_cases hτ : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨h1, h2⟩ := L.win_thick j hj.1 hj.2 τ hτ
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := hoff τ hτ
      constructor <;> linarith
  · classical
    intro h
    unfold Host.thickPlaces at h
    obtain ⟨s, -, hs⟩ := Finset.mem_image.1 h
    have h1 : (D.eTau (plOf D (false, t)) : D.R.GG) = D.R.tau1 t := by
      simp [plOf]
    rw [h1] at hs
    have h2 := congrArg (fun g : D.R.GG => g.1.1) hs
    simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h2
    exact absurd h2 (by decide)
  · have h1 : 1 ≤ j ∧ j ≤ (numOf D L).R.m := hj
    have h2 : j - 1 < D.R.m := by have := hj.1; have := hj.2; omega
    rw [NumDatum.w, NumDatum.eQ, dif_pos h1, wj, dif_pos h2]
    rfl

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEmbeddingsIntegralAndDistinctModMaximal
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.EmbSep

theorem v_intCast_eq_zero {C : Type} [Field C] (V : VF C) {n : ℤ} (hn : ¬ (V.l : ℤ) ∣ n) : V.v (n : C) = 0 := by
  have hint : ∀ m : ℤ, V.Ge 0 (m : C) := fun m => by
    rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
    · simpa using VF.ge_natCast (V := V) k
    · simpa using (VF.ge_natCast (V := V) k).neg
  have hp : Prime (V.l : ℤ) := Nat.prime_iff_prime_int.1 V.l_prime
  obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hn
  have h1 : (a : C) * (V.l : C) + (b : C) * (n : C) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → C) hab
  refine le_antisymm ?_ (hint n)
  by_contra hc
  have hc' : 0 < V.v (n : C) := lt_of_not_ge hc
  have h2 : 0 < V.v ((a : C) * (V.l : C)) := by
    rw [V.v.map_mul, V.v_l]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (hint a))
  have h3 : 0 < V.v ((b : C) * (n : C)) := by
    rw [V.v.map_mul]
    exact lt_of_lt_of_le hc' (le_add_of_nonneg_left (hint b))
  have h4 := V.v.map_lt_add h2 h3
  rw [h1, V.v.map_one] at h4
  exact lt_irrefl _ h4

theorem exists_v_sub_eq_zero {C : Type} [Field C] (V : VF C) {I : Type} [Fintype I] (M : Matrix I I C)
    (h : ∀ i j, V.Ge 0 (M i j)) (hd : V.v M.det = 0) {j j' : I} (hj : j ≠ j') :
    ∃ i, V.v (M i j - M i j') = 0 := by
  by_contra hc
  push Not at hc
  have hpos : ∀ i, 0 < V.v (M i j - M i j') := fun i =>
    lt_of_le_of_ne ((h i j).sub (h i j')) (hc i).symm
  have hd0 : M.det ≠ 0 := by
    intro h0
    rw [h0, V.v.map_zero] at hd
    exact WithTop.top_ne_zero hd
  have hM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (Ne.isUnit hd0)
  have h1 := congrFun (congrFun hM j) j
  have h2 := congrFun (congrFun hM j) j'
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  rw [Matrix.mul_apply, Matrix.one_apply_ne hj] at h2
  have h3 : ∑ i, M⁻¹ j i * (M i j - M i j') = 1 := by
    simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_zero]
  have h4 : 0 < V.v (∑ i, M⁻¹ j i * (M i j - M i j')) := by
    refine V.v.map_lt_sum WithTop.zero_ne_top fun i _ => ?_
    rw [V.v.map_mul]
    exact lt_of_lt_of_le (hpos i) (le_add_of_nonneg_left (inv_int M h hd j i))
  rw [h3, V.v.map_one] at h4
  exact lt_irrefl _ h4

theorem cmEmbeddings_integral_and_distinct_mod_maximal' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → (∀ τ x, V.Ge 0 (emA3 io ι τ x)) ∧ ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a : 𝓞 E, V.v (emA3 io ι τ a - emA3 io ι τ' a) = 0 := by
  intro E _ _ _ H lv c T io C _ _ V ι _ hd
  have hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_of_isIntegral V (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral x))
  refine ⟨hint, fun τ τ' hne => ?_⟩
  let b : (E →+* ℂ) → 𝓞 E := fun i => RingOfIntegers.basis E (equivReindex E i)
  let M : Matrix (E →+* ℂ) (E →+* ℂ) c.F := Matrix.of fun i σ => embK c σ (b i)
  have hM : (algebraMap c.F ℂ).mapMatrix M = basisMatrix E := by
    ext i σ
    simp only [basisMatrix, Matrix.of_apply, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
    rfl
  have hdet : M.det ^ 2 = (discr E : c.F) := by
    apply (algebraMap c.F ℂ).injective
    rw [map_pow, RingHom.map_det, hM, map_intCast, discr_eq_basisMatrix_det_sq]
  let N : Matrix (E →+* ℂ) (E →+* ℂ) C := (ι.comp io).mapMatrix M
  have hN : N.det ^ 2 = (discr E : C) := by
    rw [← RingHom.map_det, ← map_pow, hdet, map_intCast]
  have hNi : ∀ i j, V.Ge 0 (N i j) := fun i j => hint j (b i)
  have hv : V.v N.det = 0 := by
    have h1 := v_intCast_eq_zero V hd
    rw [← hN, pow_two, V.v.map_mul] at h1
    have h0 : 0 ≤ V.v N.det := det_int N hNi
    refine le_antisymm ?_ h0
    rw [← h1]
    exact le_add_of_nonneg_right h0
  obtain ⟨i, hi⟩ := exists_v_sub_eq_zero V N hNi hv hne
  exact ⟨b i, hi⟩

end GlobalTheory.EmbSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeDirectionsEigenbasisValuedIntegers
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth.EigExt

theorem res_surjective_of_extends {R O : Type} [CommRing R] [CommRing O] (ι : R →+* O) {d s : ℕ}
    (u : Fin s → Fin d → R) (w : Fin d → Fin d → R) (emb : Fin s ↪ Fin d) (hw : ∀ i, w (emb i) = u i)
    (hb : ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j) :
    Function.Surjective (res (fun i j => ι (u i j))) := by
  classical
  have h1 : IsUnit (Matrix.of w) := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    intro v
    obtain ⟨a, ha, -⟩ := hb v
    exact ⟨a, funext fun j => ha j⟩
  have h2 : IsUnit (ι.mapMatrix (Matrix.of w)) := h1.map _
  rw [← Matrix.mulVec_surjective_iff_isUnit] at h2
  intro g
  obtain ⟨f, hf⟩ := h2 (Function.extend emb g 0)
  refine ⟨f, funext fun i => ?_⟩
  have h3 := congrFun hf (emb i)
  rw [emb.injective.extend_apply] at h3
  rw [← h3]
  show ∑ j, ι (u i j) * f j = ∑ j, ι (w (emb i) j) * f j
  rw [hw]

theorem ι_injective {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) : Function.Injective X.ι := by
  intro a b h
  apply IsFractionRing.injective T.V T.Fr
  apply X.ιF.injective
  rw [X.comp, X.comp, h]

theorem flat {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) :
    letI := X.ι.toAlgebra; Module.Flat T.V X.O := by
  letI := X.ι.toAlgebra
  haveI : IsDomain X.O := Function.Injective.isDomain (algebraMap X.O X.C) X.ints.hom_inj
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : X.ι a * x = 0 := hx
  have ha' : X.ι a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (ι_injective X (h.trans (map_zero _).symm))
  exact (mul_eq_zero.1 hx').resolve_left ha'

theorem linPart_add {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
    (Ch : IntegralChartA3 Xo c T io y) (a b : 𝓞 E) :
    linPart (Ch.actT (a + b)) = linPart (Ch.actT a) + linPart (Ch.actT b) := by
  letI := io.toAlgebra
  have key : ∀ a i j, ReciprocityTheory.ChartRestriction.G.TB.dAct T.Fr Ch.ch.B a i j = algebraMap T.V T.Fr (linPart (Ch.actT a) i j) := by
    intro a i j
    show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)
      (MvPowerSeries.map (algebraMap T.Fr T.Fr) (Ch.ch.B.A.act a i)) = _
    rw [MvPowerSeries.coeff_map, Ch.gen.1.2.1 a i, MvPowerSeries.coeff_map]
    rfl
  ext i j
  apply IsFractionRing.injective T.V T.Fr
  rw [Matrix.add_apply, map_add, ← key, ← key, ← key, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add, Matrix.add_apply]

end GlobalTheory.CharDepth.EigExt

open GlobalTheory.CharDepth.EigExt in

theorem GlobalTheory.CharDepth.isEigBasis_valExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → ∀ τ : E →+* ℂ, IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO τ) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) ∧ Function.Surjective (res (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j))) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X τO hτ τ
  constructor
  · obtain ⟨τT, hT, hT', -⟩ := GlobalTheory.T.exists_cmType_embeddings_into_valuation_ring E H l c T io p X
    have he : τO τ = X.ι.comp (τT τ) := by
      ext a
      apply X.ints.hom_inj
      rw [hτ τ a]
      exact (hT' τ a).symm
    letI := X.ι.toAlgebra
    haveI := flat X
    rw [he]
    exact GlobalTheory.T.isEigenBasis_map_flat_baseChange T.V X.O (𝓞 E) _ _ Ch.actT (linPart_add Ch) (τT τ) _
      (GlobalTheory.T.integral_chart_directions_isEigenBasis E H Dw l Xo c T io y Ch τ (τT τ) (hT τ))
  · obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ
    exact res_surjective_of_extends X.ι _ w emb hw hb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexConjFrobeniusDepthContentBoundProofStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexConjFrobeniusDepthContentBound_proof : PhiCBd := by
  first | exact @GlobalTheory.GoodDepth.ConjPkg.phiCBd | exact GlobalTheory.GoodDepth.ConjPkg.phiCBd | (intros; apply GlobalTheory.GoodDepth.ConjPkg.phiCBd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundOfTwoSteps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

noncomputable section

namespace GlobalTheory.DepthLink

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

end GlobalTheory.DepthLink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSymmBalancedCongrOfSeparability
section
open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeIntCut
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart)

namespace GlobalTheory

theorem exists_addHom_tensor_int_of_biadditive {M N P : Type} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] (f : M → N → P) (h1 : ∀ m m' n, f (m + m') n = f m n + f m' n)
    (h2 : ∀ m n n', f m (n + n') = f m n + f m n') :
    ∃ g : M ⊗[ℤ] N →+ P, ∀ m n, g (m ⊗ₜ[ℤ] n) = f m n := by
  let F : M →+ N →+ P := AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (f m) (h2 m))
    (fun m m' => by ext n; exact h1 m m' n)
  refine ⟨TensorProduct.liftAddHom F (fun r m n => ?_), fun m n => ?_⟩
  · rw [map_zsmul, map_zsmul]; rfl
  · rw [TensorProduct.liftAddHom_tmul]; rfl

end GlobalTheory
end

