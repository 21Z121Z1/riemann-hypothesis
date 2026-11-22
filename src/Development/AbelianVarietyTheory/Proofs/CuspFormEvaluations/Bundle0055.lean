import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NegLogSqrtLeOfJbound
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem neg_log_sqrt_le_of_jbound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (dg n : ℕ) (P : I2.Par X dg) (S tableLineDegreeFive cc : ℝ), (Real.pi⁻¹) ^ dg * P.Jbound n ≤ S → p14 E X.r n P.m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q ≤ cc → -Real.log (Real.sqrt S) ≤ tableLineDegreeFive * dg + cc * P.ph := by
  intro E _ _ _ X dg n P S tableLineDegreeFive cc hS hP14 hcc
  have hf : 0 < I2.PT.f E := by
    have h1 := P.hfr
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at h1; simp at h1
    · exact h
  have hdp : 0 < I2.dstar (E := E) P.m := Nat.mul_pos (Nat.mul_pos two_pos hf) P.hm1
  have hd0 : (1 : ℝ) ≤ (I2.dstar (E := E) P.m : ℝ) := by exact_mod_cast hdp
  have hd : (0 : ℝ) < 2 * (I2.dstar (E := E) P.m : ℝ) := by linarith
  have hB := Real.rpow_pos_of_pos hd ((I2.dstar (E := E) P.m : ℝ) / 2)
  have h6 : (0 : ℝ) < 6 * (2 * (I2.dstar (E := E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2) :=
    mul_pos (by norm_num) hB
  have hph : 0 ≤ P.ph := by
    unfold I2.Par.ph I2.PT.ph
    split_ifs <;> positivity
  have hA : (4 : ℝ)⁻¹ ^ n ≠ 0 := by positivity
  have hBn : (6 * (2 * (I2.dstar (E := E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2))⁻¹ ^ n ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero h6.ne')
  have hC : (2 : ℝ)⁻¹ ^ ((X.r + 2) * dg) ≠ 0 := by positivity
  have hJpos : 0 < P.Jbound n := by
    unfold I2.Par.Jbound
    exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (inv_pos.2 h6) _))
      (pow_pos (by norm_num) _)) (Real.exp_pos _)
  have hJ : Real.log (P.Jbound n) = -(n * Real.log 4) -
      n * (Real.log 6 + (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ))) -
      (((X.r + 2) * dg : ℕ) : ℝ) * Real.log 2 -
      2 * (8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q * P.ph) := by
    unfold I2.Par.Jbound
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero hA hBn) hC) (Real.exp_pos _).ne',
      Real.log_mul (mul_ne_zero hA hBn) hC, Real.log_mul hA hBn, Real.log_exp, Real.log_pow,
      Real.log_pow, Real.log_pow, Real.log_inv, Real.log_inv, Real.log_inv,
      Real.log_mul (by norm_num) hB.ne', Real.log_rpow hd]
    unfold I2.Cchi
    ring
  have hdg : (1 : ℝ) ≤ dg := by exact_mod_cast P.hDF
  have h24 : Real.log 24 = Real.log 4 + Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hl2d : 0 ≤ Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := Real.log_nonneg (by linarith)
  have hT : 0 ≤ Real.log 24 + (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by
    have : 0 < Real.log 24 := Real.log_pos (by norm_num)
    have : 0 ≤ (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by positivity
    linarith
  have hpi : (0 : ℝ) < (Real.pi⁻¹) ^ dg := pow_pos (inv_pos.2 Real.pi_pos) _
  have hpos : 0 < (Real.pi⁻¹) ^ dg * P.Jbound n := mul_pos hpi hJpos
  have hlS := Real.log_le_log hpos hS
  rw [Real.log_mul hpi.ne' hJpos.ne', Real.log_pow, Real.log_inv, hJ] at hlS
  rw [Real.log_sqrt (hpos.le.trans hS)]
  have e2 := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hT) (sub_nonneg.2 hdg)
  have e3 := mul_le_mul_of_nonneg_right hcc hph
  have e4 := mul_le_mul_of_nonneg_right hP14 (by linarith : (0 : ℝ) ≤ dg)
  unfold p14 at e4
  push_cast at hlS
  rw [h24] at e2 e4
  linarith [e2, e3, e4]

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.OneDivisionUpstairsFreeWeight
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares.DivOne

open GlobalTheory.Up GlobalTheory.Up.DivUpPf

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def smoothWtG (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) (z : V (nd X)) : ℝ :=
  phla X G (cpt X x0 z) + ((-1) * Real.log (densF X x0 z) + ((-bb) * rhF X x0 z +
    (1 / 2) * Real.log (∑ k, ‖Xa.w k (cpt X x0 z)‖ ^ 2)))

theorem smoothWtG_contDiffOn (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) :
    ContDiffOn ℝ ∞ (smoothWtG Xa G x0 bb) (OmF X x0) := fun _ hz =>
  ((IW.phla_cpt_cdAt X x0 hz G).add ((contDiffAt_const.mul (OntoB.logDens_contDiffAt hz)).add
    ((contDiffAt_const.mul (OntoB.rhF_contDiffAt hz)).add
      (contDiffAt_const.mul (logw_contDiffAt Xa x0 hz))))).contDiffWithinAt

theorem smoothWtG_levi (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ)
    (hm : bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) :
    0 ≤ (leviV (nd X) (fun w => ((smoothWtG Xa G x0 bb w : ℝ) : ℂ)) z ξ).re := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz G).of_le HE.two_le_inf
  have h2 := (OntoB.logDens_contDiffAt hz).of_le HE.two_le_inf
  have h3 := (OntoB.rhF_contDiffAt hz).of_le HE.two_le_inf
  have h4 := (logw_contDiffAt Xa x0 hz).of_le HE.two_le_inf
  have h5 := logSum_levi_nonneg (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz) ξ
  unfold smoothWtG
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 ((contDiffAt_const.mul h2).add
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2)
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4)),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h3) (contDiffAt_const.mul h4),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h4]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  unfold leviRh leviO leviM leviDens at hm
  linarith

theorem inAt_iffG (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb t : ℝ)
    (k0 : Fin (nd X)) (hnull : volume {y | y ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 y) = 0} = 0)
    (F : V (nd X) → ℂ) :
    InAt X x0 (fun x => open Classical in if x ∈ X.dom then
      ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
        ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-t) else 0) bb F ↔
      ∫⁻ z in OmF X x0, ENNReal.ofReal (‖F z‖ ^ 2 *
        (∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2) ^ (-t) *
        Real.exp (-smoothWtG Xa G x0 bb z)) < ⊤ := by
  have hU := OntoB.isOpen_OmF X x0
  have hd : AEMeasurable (fun z => ENNReal.ofReal (densF X x0 z)) (volume.restrict (OmF X x0)) :=
    (OntoB.densF_continuousOn.aemeasurable hU.measurableSet).ennreal_ofReal
  unfold InAt muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine iff_of_eq (congrArg (· < ⊤) (lintegral_congr_ae ?_))
  have hae : ∀ᵐ z ∂(volume : Measure (V (nd X))), z ∈ OmF X x0 → Fl.s k0 (cpt X x0 z) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hnull
    simpa using hz
  filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae hae] with z hz hz'
  have hs : ∃ k, Fl.s k (cpt X x0 z) ≠ 0 := ⟨k0, hz' hz⟩
  have hsp : 0 < ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2 := sum_normSq_pos hs
  have hdom : cpt X x0 z ∈ X.dom := hz
  have hw := sum_normSq_w_pos Xa hdom
  have hdp := OntoB.densF_pos hz
  have hka : 0 < kaF X x0 bb z := Real.exp_pos _
  simp only [Pi.mul_apply]
  rw [if_pos hdom, ENNReal.ofReal_rpow_of_pos hw, ENNReal.ofReal_rpow_of_pos hsp,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hw.le _)),
    Real.rpow_def_of_pos hw, Real.rpow_def_of_pos hsp, ← Real.exp_add, ← Real.exp_add,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hdp.le]
  congr 1
  rw [kaF, div_eq_mul_inv, ← Real.exp_neg]
  conv_lhs => rw [← Real.exp_log hdp]
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  unfold smoothWtG
  ring

end

theorem divOne_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ bb : ℝ, (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) → ∀ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) → InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X + 1 : ℕ) : ℝ) - 1 / 2)) else 0) bb F → ∃ H : Fin (nd X) → V (nd X) → ℂ, (∀ k, DifferentiableOn ℂ (H k) (OmF X x0) ∧ InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X : ℕ) : ℝ) - 1 / 2)) else 0) bb (H k)) ∧ ∀ z ∈ OmF X x0, F z = ∑ k, Fl.s k (cpt X x0 z) * H k z := by
  intro E _ _ _ r X Xa Fl G x0 ho bb hm ⟨k0, z0, hz0, hz0'⟩ F hF hI
  have hU := OntoB.isOpen_OmF X x0
  have hc := OmFConnStatement_holds r X x0 ho
  have hgn := HE.hgn_of hU hc (s_diffOn Fl x0 k0) hz0 (fun h => hz0' h.self_of_nhds)
  have hnull := HE.zeros_null hU (s_diffOn Fl x0 k0) hgn
  obtain ⟨S, hS, -⟩ := exhaustG_holds r X x0 ho _ (s_diffOn Fl x0 k0)
  have hcast : ((nd X + 1 : ℕ) : ℝ) - 1 / 2 = ((nd X : ℝ) - 1 / 2) + 1 := by
    push_cast; ring
  rw [inAt_iffG Xa Fl G x0 bb _ k0 hnull, hcast] at hI
  obtain ⟨H, hH, hFH⟩ := SkodaIter.step Xa.n_ge hU (s := fun k z => Fl.s k (cpt X x0 z)) k0
    (s_diffOn Fl x0) hgn ⟨S, hS⟩ (smoothWtG_contDiffOn Xa G x0 bb)
    (fun z hz ξ => smoothWtG_levi Xa G x0 bb hz ξ (hm z hz ξ)) (t := (nd X : ℝ) - 1 / 2)
    (by linarith) hF hI
  exact ⟨H, fun k => ⟨(hH k).1, (inAt_iffG Xa Fl G x0 bb _ k0 hnull _).2 (hH k).2⟩, hFH⟩

end GlobalTheory.Shares.DivOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivLevelSqEqAlpha
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlphaChain

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem polyDeriv_comp_clm {J V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Q : MvPolynomial J ℂ) (u : J → V)
    (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (g : V →L[ℂ] V) (c : J → ℂ) (hg : ∀ l, g (u l) = c l • u l) (κ : ℂ)
    (hκ : ∀ m ∈ Q.support, (m.prod fun l k => c l ^ k) = κ) :
    I2.polyDeriv Q u (G ∘ g) 0 = κ * I2.polyDeriv Q u G 0 := by
  unfold I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right g hG 0
    (i := Multiset.card (Finsupp.toMultiset m)) le_top
  rw [h, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [hg]
  rw [ContinuousMultilinearMap.map_smul_univ, ← hκ m hm, smul_eq_mul]
  have : (∏ k : Fin (Multiset.card (Finsupp.toMultiset m)),
      c ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm))) =
      m.prod fun l k => c l ^ k := by
    have e1 : (∏ k : Fin (Multiset.card (Finsupp.toMultiset m)),
      c ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm))) =
      ∏ k : Fin (Finsupp.toMultiset m).toList.length, c ((Finsupp.toMultiset m).toList.get k) :=
      Fintype.prod_equiv (finCongr (Multiset.length_toList _).symm) _ _ (fun _ => rfl)
    rw [e1, ← List.prod_ofFn]
    have e2 : (List.ofFn fun k => c ((Finsupp.toMultiset m).toList.get k)) = (Finsupp.toMultiset m).toList.map c := by
      rw [List.ofFn_comp' , List.ofFn_get]
    rw [e2, Multiset.prod_map_toList]
    classical
    rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])]
  rw [this]; ring

theorem hf_act_act {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (M : ℂ)
    (h : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M) (v w : I2.Vsp dim) :
    I2.Hf (I2.act β v) (I2.act β w) = M * I2.Hf v w := by
  unfold I2.Hf I2.act
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul]
  rw [← h i.1]; ring

theorem translate_eq_comp {E : Type} [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (α β : 𝓞 E) (M n : ℕ)
    (h : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M)
    (h' : ∀ τ : E →+* ℂ, τ (α : E) * τ (β : E) = M) (s : (Fin 1 → I2.Vsp X.dim) → ℂ)
    (a v : Fin n → I2.Vsp X.dim) :
    X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s) v =
      X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s) (fun b => I2.act β (v b)) := by
  unfold I2.PT.U I2.HC I2.s0
  simp only [hf_act_act β M h, ← Finset.mul_sum]
  congr 1
  · congr 1; push_cast; ring
  · refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    funext _
    ext i
    simp [PullbackSections.vspActL, I2.act]
    rw [← h' i.1]; ring

def colMap {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (n : ℕ) :
    (Fin n → I2.Vsp dim) →L[ℂ] (Fin n → I2.Vsp dim) :=
  LinearMap.toContinuousLinearMap (LinearMap.pi fun b => (vspActL β).comp (LinearMap.proj b))

theorem differentiable_translate {E : Type} [Field E] [NumberField E] (X : I2.PT E) (q n : ℕ)
    (p : I2.Vsp X.dim →ₗ[ℂ] I2.Vsp X.dim) (s : (Fin 1 → I2.Vsp X.dim) → ℂ) (hs : Differentiable ℂ s)
    (a : Fin n → I2.Vsp X.dim) : Differentiable ℂ (X.U q a (I2.s0 X p s)) := by
  have hp : Differentiable ℂ p := (LinearMap.toContinuousLinearMap p).differentiable
  have h1 : Differentiable ℂ (I2.s0 X (n := n) p s) := by
    unfold I2.s0
    have hk : ∀ k : Fin n, Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => s fun _ => p (v k) := fun k =>
      hs.comp (differentiable_pi.2 fun _ => hp.comp (differentiable_apply k))
    exact fun v => (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (hk k v).hasFDerivAt).differentiableAt
  have h2 : Differentiable ℂ fun v : Fin n → I2.Vsp X.dim => I2.HC v a := by
    unfold I2.HC I2.Hf
    refine Differentiable.fun_sum fun k _ => Differentiable.fun_sum fun i _ => Differentiable.mul_const ?_ _
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp (differentiable_apply k)
  unfold I2.PT.U
  exact (((h2.const_mul _).sub_const _).cexp).mul (h1.comp (differentiable_id.sub_const a))

theorem polyDeriv_levelSq_eq_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (α β : 𝓞 E) (M n : ℕ), (β : E) = IsCMField.complexConj E (α : E) → α * β = (M : 𝓞 E) → ∀ s : (Fin 1 → I2.Vsp X.dim) → ℂ, Differentiable ℂ s → ∀ (a : Fin n → I2.Vsp X.dim) (Io : Type) (P : MvPolynomial Io ℂ) (u : Io → Fin n → I2.Vsp X.dim) (sc : Io → ℂ) (κ : ℂ), (∀ ℓ b, I2.act β (u ℓ b) = sc ℓ • u ℓ b) → (∀ m ∈ P.support, (m.prod fun ℓ e => sc ℓ ^ e) = κ) → I2.polyDeriv P u (X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s)) 0 = κ * I2.polyDeriv P u (X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s)) 0 := by
  intro E _ _ _ X α β M n hβ hα s hs a Io P u sc κ hu hκ
  have hbar : ∀ τ : E →+* ℂ, τ (β : E) = (starRingEnd ℂ) (τ (α : E)) := fun τ => by
    rw [hβ, IsCMField.complexEmbedding_complexConj]
  have h' : ∀ τ : E →+* ℂ, τ (α : E) * τ (β : E) = M := by
    intro τ
    have := congrArg (fun a : 𝓞 E => τ (a : E)) hα
    simpa using this
  have h'' : ∀ τ : E →+* ℂ, τ (β : E) * (starRingEnd ℂ) (τ (β : E)) = M := by
    intro τ
    rw [← h' τ, hbar, Complex.conj_conj, mul_comm]
  have hfun : X.U (M ^ 2) a (I2.s0 X ((M : ℂ) • LinearMap.id) s) =
      (X.U M (fun b => I2.act β (a b)) (I2.s0 X (vspActL α) s)) ∘ colMap β n := by
    funext v
    rw [translate_eq_comp X α β M n h'' h']
    rfl
  rw [hfun]
  refine polyDeriv_comp_clm P u _ ?_ (colMap β n) sc (fun l => funext fun b => hu l b) κ hκ
  exact GlobalTheory.SCV.contDiff_of_differentiable (differentiable_translate X M n (vspActL α) s hs _) ⊤

end GlobalTheory.AlphaChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RealBounds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RunParametersOfLower

theorem real_bounds (f r m ρ w D q t : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hm : 1 ≤ m) (hmf : m ≤ f)
    (hf2 : f ^ 2 ≤ ρ) (hρ : 16 ≤ ρ) (hw0 : 0 ≤ w) (hw : w ≤ f ^ 2) (hD : 1 ≤ D)
    (hq : (ρ ^ 7) ^ 4 * (90 * (f * r + D)) * D * r ≤ q)
    (ht : t = q * (q / (90 * (f * r + D) * (ρ ^ 7) ^ 4))) :
    (2 * f * m) ^ 2 * (2 * w * ρ) * (f * (90 * (f * r + D)) * (ρ ^ 7) ^ 3) < q ∧
    1 ≤ q / (90 * (f * r + D) * (ρ ^ 7) ^ 4) ∧
    90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ q / 2 ∧ D ≤ q ∧
    4 * D * (7 + Real.log (q * D)) + 2 * f * m + 1 ≤ t ∧
    f * r * Real.log 2 + 2 * (2 * f * m) + 3 + (D + 1) * (r * Real.log r + 3 * r + 3) ≤ t := by
  have hρ1 : (1 : ℝ) ≤ ρ := by linarith
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hN : r ≤ f * r := by nlinarith
  have hN1 : 1 ≤ f * r := by linarith
  have hfρ : f ≤ ρ := by nlinarith
  have hfm : f * m ≤ ρ := by nlinarith
  have hm2 : m ^ 2 ≤ ρ := by nlinarith
  have hd0 : 0 ≤ 2 * f * m := by positivity
  have hd : 2 * f * m ≤ 2 * ρ := by linarith
  have hwρ : w ≤ ρ := hw.trans hf2
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlogr : Real.log r ≤ r := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < r by linarith); linarith
  have h3' : f * r * Real.log 2 ≤ f * r * 1 := by gcongr
  obtain ⟨N, hNdef⟩ : ∃ N, N = f * r := ⟨_, rfl⟩
  rw [← hNdef] at hq ht hN hN1 h3' ⊢
  obtain ⟨S, hS⟩ : ∃ S, S = 90 * (N + D) := ⟨_, rfl⟩
  rw [← hS] at hq ht ⊢
  have hS180 : 180 ≤ S := by linarith
  have hS0 : 0 < S := by linarith
  have hB : 0 < S * (ρ ^ 7) ^ 4 := by positivity
  have hDr : 1 ≤ D * r := one_le_mul_of_one_le_of_one_le hD hr
  have hDDr : D ≤ D * r := by nlinarith
  have hrDr : r ≤ D * r := by nlinarith
  have hq' : D * r * (S * (ρ ^ 7) ^ 4) ≤ q := by linarith
  have hBq : S * (ρ ^ 7) ^ 4 ≤ q := by
    have := mul_le_mul_of_nonneg_right hDr hB.le
    linarith
  have hq0 : 0 < q := by linarith
  have hb : D * r ≤ q / (S * (ρ ^ 7) ^ 4) := by rw [le_div_iff₀ hB]; exact hq'
  have htq : q * (D * r) ≤ t := by rw [ht]; gcongr
  have hT : ρ ^ 5 ≤ (ρ ^ 7) ^ 4 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hρ1 (by norm_num)
  have hT4 : 16 * ρ ^ 4 ≤ ρ ^ 5 := by
    rw [pow_succ' ρ 4]; gcongr
  have hT1 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have hqT : 180 * (ρ ^ 7) ^ 4 ≤ q := by
    have : 180 * (ρ ^ 7) ^ 4 ≤ S * (ρ ^ 7) ^ 4 := by gcongr
    linarith
  have hSρ : S * ρ ≤ q := by
    have : S * ρ ≤ S * (ρ ^ 7) ^ 4 := by
      have : ρ ≤ (ρ ^ 7) ^ 4 := by linarith
      gcongr
    linarith
  have hS16 : S * 16 ≤ S * ρ := by gcongr
  have hDq : D ≤ q := by linarith
  refine ⟨?_, by linarith, ?_, hDq, ?_, ?_⟩
  · have h1 : (2 * f * m) ^ 2 * (2 * w * ρ) * (f * S * (ρ ^ 7) ^ 3) ≤
        (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * S * (ρ ^ 7) ^ 3) := by
      gcongr
    have h2 : (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * S * (ρ ^ 7) ^ 3) = 8 * (S * ρ ^ 26) := by ring
    have h3 : S * (ρ ^ 7) ^ 4 = ρ ^ 2 * (S * ρ ^ 26) := by ring
    have h4 : 0 < S * ρ ^ 26 := by positivity
    have h5 : 8 * (S * ρ ^ 26) < ρ ^ 2 * (S * ρ ^ 26) :=
      mul_lt_mul_of_pos_right (by nlinarith) h4
    linarith
  · have h1 : 90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ 90 * ρ * (2 * ρ) ^ 2 * ρ := by gcongr
    have h2 : 90 * ρ * (2 * ρ) ^ 2 * ρ = 360 * ρ ^ 4 := by ring
    linarith
  · have h1 : Real.log q = Real.log (q / 16) + Real.log 16 := by
      rw [Real.log_div hq0.ne' (by norm_num)]; ring
    have h2 : Real.log (q / 16) ≤ q / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h4 : Real.log D ≤ Real.log q := Real.log_le_log (by linarith) hDq
    have h5 : Real.log (q * D) = Real.log q + Real.log D := Real.log_mul hq0.ne' (by linarith)
    have h6 : 4 * D * (7 + Real.log (q * D)) ≤ 4 * D * (q / 8 + 37) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    have h7 : (2 * ρ + 1) * 1 ≤ (2 * ρ + 1) * D := by gcongr
    have h8 : (q / 2 + 148 + (2 * ρ + 1)) * D ≤ q * D := by
      apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
    have h9 : q * D ≤ q * (D * r) := by gcongr
    linarith
  · have h2' : 0 ≤ Real.log r := Real.log_nonneg hr
    have h4 : r * Real.log r + 3 * r + 3 ≤ r * (N + 6) := by
      have : r * Real.log r ≤ r * N := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
      linarith
    have h5 : (D + 1) * (r * Real.log r + 3 * r + 3) ≤ (2 * D) * (r * (N + 6)) := by
      apply mul_le_mul (by linarith) h4 (by positivity) (by positivity)
    have h6 : (N + 4 * ρ + 3) * 1 ≤ (N + 4 * ρ + 3) * (D * r) := by gcongr
    have h7 : (N + 4 * ρ + 3 + 2 * (N + 6)) * (D * r) ≤ q * (D * r) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
    linarith

theorem runOK_of_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r DF q m : ℕ), 1 ≤ DF → 2 ≤ I2.PT.f E * r → 1 ≤ m → m ^ 4 ≤ I2.PT.f E → (I2.PT.f E : ℝ) ^ 2 ≤ I2.PT.rd E → 16 ≤ I2.PT.rd E → I2.RR (E := E) ^ 4 * (90 * (I2.PT.f E * r + DF)) * DF * r ≤ q → RunOK E r DF q (Real.sqrt (90 * (I2.PT.f E * r + DF))) m := by
  intro E _ _ _ r DF q m hDF hfr hm1 hmf hf2 hrd hlo
  have hf : 1 ≤ I2.PT.f E := by
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hfr; omega
    · exact h
  have hmf' : m ≤ I2.PT.f E := (Nat.le_self_pow (by norm_num) m).trans hmf
  have hfR : (1 : ℝ) ≤ I2.PT.f E := by exact_mod_cast hf
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hDR : (1 : ℝ) ≤ DF := by exact_mod_cast hDF
  have hmfR : (m : ℝ) ≤ I2.PT.f E := by exact_mod_cast hmf'
  have hfrR : (2 : ℝ) ≤ I2.PT.f E * r := by exact_mod_cast hfr
  have hfrd : (I2.PT.f E : ℝ) ≤ I2.PT.rd E := by nlinarith
  have hw : (I2.PT.f E : ℝ) ^ ((3 : ℝ) / 2) ≤ (I2.PT.f E : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hfR (by norm_num)
  have hS0 : (0 : ℝ) < 90 * (I2.PT.f E * r + DF) := by positivity
  have hsq : Real.sqrt (90 * (I2.PT.f E * r + DF)) ^ 2 = 90 * (I2.PT.f E * r + DF) := Real.sq_sqrt hS0.le
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := real_bounds (I2.PT.f E) r m (I2.PT.rd E) _ DF q
    (I2.t0 (E := E) q (Real.sqrt (90 * (I2.PT.f E * r + DF)))) hfR hrR hmR hmfR hf2 hrd
    (by positivity) hw hDR hlo (by unfold I2.t0 I2.b0 I2.RR; rw [hsq])
  have hc4 : DF ≤ q := by exact_mod_cast c4
  have hq1 : 1 ≤ q := hDF.trans hc4
  have hq0 : (0 : ℝ) < q := by linarith
  have hρ0 : 0 < I2.PT.rd E := by linarith
  have hd : (I2.dstar (E := E) m : ℝ) = 2 * I2.PT.f E * m := by unfold I2.dstar; push_cast; ring
  intro X hX hdim
  subst hX
  refine ⟨⟨q, _, m, hq1, hDF, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, ?_, ?_,
    hc4, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [hsq]
    unfold I2.PT.gA
    push_cast
    constructor <;> linarith
  · unfold I2.th I2.omStar I2.RR
    rw [Real.sq_sqrt (by positivity), ← mul_div_assoc, div_lt_one hq0, hsq, hd]
    exact c1
  · unfold I2.b0 I2.RR; rw [hsq]; exact c2
  · unfold I2.M1
    rw [hd]; exact c3
  · rw [hd]; linarith
  · unfold I2.PT.gA
    rw [hd]
    push_cast
    linarith

end GlobalTheory.RunParametersOfLower
end

