import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LaurentCoeffSectionValueArcEqFourierJacobi
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0071
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionary
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LetterSquaredLengthLeFlowHeight

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEvREqFjAnLie
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
open GlobalTheory.ArcCoeff

namespace GlobalTheory.ArcCoeffAt

theorem coeff_evR_eq_fj_anLie : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (th : a.D₀.P.L.Sec) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c σ → IsUnf U → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ w₁ : ℂ, Ha.T < w₁.im → ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E) (C : ℝ), (U.X k).IsIso ξ' ∧ IsBePar ξ a.be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ 0 < C ∧ (∀ v, Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → C ≤ v * Real.sqrt |((NumberField.discr E : ℤ) : ℝ)|) ∧ ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)) (y : FrPt Xo c ℂ⸨X⸩), IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ∃ (x : (U.X k).dom) (κ : ℂ), ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), AnLie Uw.F Ha.i (Ha.Pw w₁) (U.un k x) z ∧ (∀ v, Uw.Pm k x (gm v) = L (Ha.Pw w₁ v)) ∧ (∀ v v', (Uw.F.Di (Uw.ik k)).EF (gm v) (gm v') = (Uw.F.Di Ha.i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (gm t) : Fin r → E) = ξ') ∧ ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → (evR Xo c F y).coeff jj * eTwoPi w₁ ^ jj = κ * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 := by
  intro hL hL2 E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha _ th ξ ν₀ jj a' n hEv hσ hU halg hχ hmono hpush hth
    hrk hξ0 hβ hD hTr w₁ hw₁
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e) th hth
  obtain ⟨k, ξ', sE, hiso, hbe, hpos, hlev, hdict⟩ :=
    GlobalTheory.ArcFlow.holArc_eq_flow_orbit hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha hσ hU hrk ξ hξ0 w₁ hw₁
  obtain ⟨C₀, hC₀, hC₀', hcov⟩ := GlobalTheory.LatticeCovolumeL2.det_im_eq_covol E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ k ξ' hσ hU hiso hrk
  set B : ℝ := ‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ (Uw.g - Θ.S.card) * ((((Θ.τ w₁).map Complex.im).submatrix
    (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ with hBdef
  have hB : 0 < B := by
    have h1 := ((Θ.pos w₁ hw₁).2.submatrix (e := fun k : {k // k ∉ Θ.S} => k.1) Subtype.val_injective).det_pos
    have h2 := norm_pos_iff.2 Θ.κ_ne
    positivity
  refine ⟨k, ξ', sE, B * C₀, hiso, hbe, hpos, hlev, mul_pos hB hC₀, fun v hv => ?_, fun e z y hy hz => ?_⟩
  · rw [GlobalTheory.T.abelianPart_sectionNormSq_eq_thetaData hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha th Θ w₁ v hw₁ hv]
    exact mul_le_mul_of_nonneg_left hC₀' hB.le
  have hzt := GlobalTheory.T.arc_letter_analyticVectors_independent_blockType hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha y e th z hσ halg (GlobalTheory.ThetaShiftProofs.mono_j Y hmono) hy hz
  obtain ⟨x, hx, L, gm, hEF, hLz, ⟨t, ht, htξ⟩, hflow⟩ := hdict z hzt
  obtain ⟨T', hT'⟩ := GlobalTheory.T.hasSum_sectionValue_arc_framedPoint hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha y e th Θ z hEv halg hχ hmono hpush hth hy hz
  set K : ℝ := (B * C₀ * ∏ τ, ((U.X k).tt ξ' x τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x with hKdef
  have htt : ∀ x' ∈ (U.X k).dom, 0 < ∏ τ, ((U.X k).tt ξ' x' τ)⁻¹ := fun x' hx' =>
    Finset.prod_pos fun τ _ => inv_pos.2 (GlobalTheory.FjCauchy.tt_pos _ hiso hx' τ)
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos (mul_pos (mul_pos hB hC₀) (htt x hx)) _)
    (MinimumGrowthBounds.nfac_pos _ _ hx)
  let fl : ℂ → Frame (U.X k).Ψ r := fun w => (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x
  have key : ∀ w : ℂ, ∃ cw : ℂ, max Ha.T T' < w.im → ∀ F ∈ sec Xo c a' n,
      HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (cw * rdU U F k (fl w)) ∧
        ‖cw * rdU U F k (fl w)‖ = K * ‖rdU U F k (fl w)‖ := by
    intro w
    by_cases hw : max Ha.T T' < w.im
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
    obtain ⟨hxw, hPm, hlie⟩ := hflow w hw1
    obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ z hσ hzt w hw1
    obtain ⟨s, hs⟩ := frChg_of_anLie Uw.F Ha.i _ (Ha.period w hw1) _ _ z hlie hyw.1
    have hv := GlobalTheory.ThetaSquareIntegrable.theta_l2_of_analytic_generator E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha th Θ w yw hw1 hyw.1.1 hyw.2
    have hoff : (((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)) =
        (((Θ.τ w₁).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)) := by
      ext i j
      exact congrArg Complex.im (tau_col_const Ha Θ w w₁ i.1 j.1 j.2)
    rw [hcov w ⟨_, hxw⟩ L gm hw1 hPm hEF ⟨t, fun v' hv' => by
      have := ht v'
      rwa [hv', map_zero, neg_eq_zero] at this, htξ⟩, hoff, ← _root_.mul_assoc, ← _root_.mul_assoc, ← hBdef] at hv
    refine ⟨toC s ^ n, fun _ F hF => ?_⟩
    obtain ⟨e1, e2⟩ := evR_eq_and_norm hL hL2 U Uw hEv hσ hU k ⟨_, hxw⟩ yw s _ hs Ha.i _ (Ha.period w hw1) hyw.1.1 hv
      a' n F hD hF
    have hsum := hT' w hw2 yw hyw a' n F hF
    rw [e1] at hsum e2
    refine ⟨hsum, e2.trans ?_⟩
    have hn := GlobalTheory.ArcQ.nfac_parallel_flow E H Dw l Xo c σ r U k n ξ' hD.2 hiso x hx _ hxw
    rw [hKdef, Real.mul_rpow (mul_pos hB hC₀).le (htt _ hxw).le, Real.mul_rpow (mul_pos hB hC₀).le (htt _ hx).le]
    dsimp only [fl]
    linear_combination ((B * C₀) ^ ((n : ℝ) / 2) * ‖rdU U F k (fl w)‖) * hn
  choose cw hcw using key
  have hfl : Differentiable ℂ fl := (FlowMeanContinuity.flow_differentiable (U.X k) ξ' x).comp (by fun_prop)
  obtain ⟨κ, hκ, hκ'⟩ := GlobalTheory.exists_const_ratio_of_norm_eq {F // F ∈ sec Xo c a' n} (max Ha.T T') K
    (fun F w => cw w * rdU U F.1 k (fl w)) (fun F w => rdU U F.1 k (fl w)) cw hK
    (fun F => ⟨differentiableOn_of_hasSum _ _ _ fun w hw => (hcw w hw F.1 F.2).1,
      (hU.2.2.2.2.1 a' n hD F.1 F.2 k).1.comp hfl.differentiableOn
        fun w hw => (hflow w (max_lt_iff.1 hw).1).1⟩)
    (fun F w hw => ⟨rfl, (hcw w hw F.1 F.2).2⟩)
  refine ⟨⟨x, hx⟩, κ, L, gm, ?_, fun v => ?_, hEF, hLz, ⟨t, ht, htξ⟩, hκ, fun F hF hbdd => ?_⟩
  · obtain ⟨h1, -, h3⟩ := hflow w₁ hw₁
    have e0 : (⟨_, h1⟩ : (U.X k).dom) = ⟨x, hx⟩ := Subtype.ext (by
      simp only [sub_self, zero_mul]
      exact EmbeddingHermitianPairs.flow_zero _ _ _)
    rwa [e0] at h3
  · obtain ⟨h1, h2, -⟩ := hflow w₁ hw₁
    rw [← h2 v]
    congr 3
    simp only [sub_self, zero_mul]
    exact (EmbeddingHermitianPairs.flow_zero _ _ _).symm
  · refine coeff_eq_of_betaAt (U.X k) hbdd hiso hx ξ l.M' a.be
      (fun y z => (dvd_mul_left _ 2).trans (a.be_dvd y z)) hβ hbe hpos (hTr k) (hlev _) κ w₁ _ (max Ha.T T')
      fun w hw => ?_
    exact hκ' ⟨F, hF⟩ w hw ▸ (hcw w hw F hF).1

end GlobalTheory.ArcCoeffAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmObjOfPeriod
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.PeriodObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D D' : Datum H}
  {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)}

theorem mem_lat_iff (hP : IsPeriod D ty P) (ρ : ℂ) (a : D.La) :
    a ∈ PureType.lat hP ρ ↔ P (H.rt • a) = ρ • P a := by
  refine ⟨fun h => funext fun j => ?_, fun h j hj => ?_⟩
  · rw [hP.1, Pi.smul_apply, smul_eq_mul]
    by_cases hj : ty j (H.rt : E) = ρ
    · rw [hj]
    · rw [h j hj, mul_zero, mul_zero]
  · have := congrFun h j
    rw [hP.1, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_mul_right_iff.1 this).resolve_left hj

theorem exists_lat_move (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (gam : D.La ≃ₗ[𝓞 E] D'.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hE : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    (hh : ∀ a, P' (gam a) = h (P a)) {p q : ℕ} (Z : GlobalTheory.CM.CMLat hP p q) :
    ∃ Z' : GlobalTheory.CM.CMLat hP' p q, Z'.hh = Z.hh :=
  ⟨{ D₁ := Z.D₁
     sigP := Z.sigP
     sigM := Z.sigM
     f := fun j => gam.toLinearMap ∘ₗ Z.f j
     pure := fun j a => by
       refine (mem_lat_iff hP' _ _).2 ?_
       show P' (H.rt • gam (Z.f j a)) = _ • P' (gam (Z.f j a))
       rw [← map_smul, hh, hh, (mem_lat_iff hP _ _).1 (Z.pure j a), map_smul]
     hh := Z.hh
     form := fun j a b => (hE _ _).trans (Z.form j a b)
     span := by
       obtain ⟨n, hn, hs⟩ := Z.span
       refine ⟨n, hn, fun a => ?_⟩
       obtain ⟨x, hx⟩ := hs (gam.symm a)
       refine ⟨x, ?_⟩
       have := congrArg gam hx
       rw [map_nsmul, gam.apply_symm_apply, map_sum] at this
       exact this }, rfl⟩

theorem isExp_move {R : Type} [CommRing R] {T : GlobalTheory.CM.PAT H (Sp R)} {σ : R →+* ℂ} (hP : IsPeriod D ty P)
    (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hE : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    (hh : ∀ a, P' (gam a) = h (P a)) {e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)}
    (he : GlobalTheory.CM.IsExp T σ D' ty P' e) : GlobalTheory.CM.IsExp T σ D ty P fun z => e (h z) := by
  obtain ⟨hP', hol, add, onto, ker, lin, weil⟩ := he
  have hd : Differentiable ℂ h := h.toContinuousLinearEquiv.differentiable
  refine ⟨hP, fun U f => ⟨?_, ?_⟩, fun z w => ?_, onto.comp h.surjective, fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩
  · exact (hol U f).1.preimage hd.continuous
  · exact (hol U f).2.comp hd.differentiableOn fun z hz => hz
  · beta_reduce
    rw [map_add, add]
  · refine (ker _).trans ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩
      exact ⟨gam.symm a, h.injective (by rw [← hh, gam.apply_symm_apply, ha])⟩
    · rintro ⟨a, rfl⟩
      exact ⟨gam a, hh a⟩
  · let m : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have hm : ∀ z, m z = fun k => ty k (a : E) * z k := fun _ => rfl
    have hc : h.toLinearMap.restrictScalars ℝ ∘ₗ m = m ∘ₗ h.toLinearMap.restrictScalars ℝ :=
      LinearMap.ext_on_range hP.2.2.2.1 fun x => by
        show h (m (P x)) = m (h (P x))
        rw [← hh, hm, hm, ← funext (hP.1 a x), ← funext (hP'.1 a (gam x)), ← hh, map_smul]
    have hz : h (m z) = m (h z) := LinearMap.congr_fun hc z
    show e (h (m z)) = _
    rw [hz, hm, lin]
  · beta_reduce
    rw [map_smul, map_smul, ← hh, ← hh]
    exact weil k _ _ c hk (by rw [hE]; exact hc)

end GlobalTheory.ArcCM.PeriodObj

namespace GlobalTheory.ArcCM

theorem exists_cmObj_of_period : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)) (hP : IsPeriod DB ty PB) (Z : GlobalTheory.CM.CMLat hP DB.p DB.q), 1 ≤ DB.p + DB.q → IsTypeFn H DB.p DB.q ty → l.A = 1 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (σ₁ : K →+* ℂ) (ρ : 𝓞 K) (X : GlobalTheory.CM.CMObj H K ρ σ₁ DB.p DB.q) (ex : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G)), σ₁.comp (algebraMap c.F K) = c.F.val.toRingHom ∧ σ₁ (ρ : K) = H.rt0 ∧ X.hh = Z.hh ∧ GlobalTheory.CM.IsExp X.B (σ₁.comp (algebraMap (𝓞 K) K)) DB ty PB ex := by
  intro kn E _ _ _ H l c DB g ty PB hP Z hpq hty hA
  obtain ⟨Xo⟩ := kn.n1ab E H DB l hpq
  obtain ⟨FU⟩ := kn.n1c E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty
  have hζ : algebraMap (KA l) ℂ (baseKA l).ζ =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((1 : ℤ) : ℂ)) / l.A) := by
    show zeta l.A = _
    rw [hA, zeta]
    simp [Complex.exp_neg]
  obtain ⟨y, e, he⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod kn.theta kn.laws E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq
    rfl hty DB LinearMap.id PB ⟨rfl, rfl, fun _ => LinearMap.id, fun _ => 1, fun n m _ _ a => ⟨0, by simp⟩,
      fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩, fun n _ a a' => by simp, hζ, rfl⟩ hP
  obtain ⟨i, P', hP', hy⟩ := FU.onto y he.1
  obtain ⟨gam, h, hE, -, -, hh⟩ := (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed kn.theta kn.laws E H DB l Xo
    (algebraMap (KA l) ℂ) g ty hpq rfl hty DB (FU.Di i) LinearMap.id (FU.t i) PB P' y (FU.u i P') e (FU.ex i P') he
    ⟨FU.over_σ i P' hP', hP', ⟨FU.ex_add i P' hP', FU.ex_onto i P' hP', ExpUniqFamily.isHolTo_ex FU i P' hP',
      (FU.ex_diff i P' hP').1, (FU.ex_diff i P' hP').2⟩, FU.ex_ker i P' hP', FU.ex_lin i P' hP', FU.ex_weil i P' hP',
      FU.ex_eta i P' hP', FU.ex_etaA i P' hP'⟩).1 hy.symm
  obtain ⟨Z', hZ'⟩ := PeriodObj.exists_lat_move hP hP' gam h hE hh Z
  obtain ⟨K, _, hk, ρ, X, y₀, t₀, m, m', gA, tyA, PA, eA, F, hle, hρ, hX, -, hy₀, -⟩ :=
    kn.cm E H DB l Xo g ty FU i P' hP' Z' c.F c.fin
  obtain ⟨eB, heB, -⟩ := GlobalTheory.CM.ExCompare.exists_isExp_of_family FU i hP' (algebraMap (𝓞 K) K) (algebraMap K ℂ)
    X.B m m' hy₀
  exact ⟨K, inferInstance, inferInstance, (IntermediateField.inclusion hle).toRingHom.toAlgebra, algebraMap K ℂ, ρ, X,
    fun z => eB (h z), RingHom.ext fun _ => rfl, hρ, hX.trans hZ', PeriodObj.isExp_move hP gam h hE hh heB⟩

end GlobalTheory.ArcCM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsKeyIntegral
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcGamma

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (h : IsLieBasis v) : IsLieBasis fun i : Fin m => v (i.cast e) := by
  subst e
  exact h

theorem isLieComb_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    IsLieComb (fun i : Fin m => c (i.cast e)) (fun i : Fin m => v (i.cast e)) w := by
  subst e
  exact h

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (Chart.dualMapR g) ≫ spMap (Chart.dualMapR f) = spMap (Chart.dualMapR (g.comp f)) := by
  rw [spMap_comp_spMap]
  refine congrArg spMap (RingHom.ext fun x => ?_)
  ext <;> simp [Chart.dualMapR]

section Pull

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {f : A →+* A'} {D₀ : Out.DegPre A}
  {D₁ : Out.DegPre A'} (p : Out.IsPullDeg f D₀ D₁)
include p

theorem g_eq : D₁.P.g = D₀.P.g :=
  H1.dim_unique _ D₁.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D₀.P.smoothDim)
    (eSec D₁.P.A (Classical.arbitrary (PrimeSpectrum A')))

theorem keyPB_of_pull {th : D₀.P.L.Sec} {th₁ : D₁.P.L.Sec} (h : ThBC p th th₁) {g₀ n₀ g₁ n₁ v hv v₁ hv₁}
    (hvv : ∀ i, (v₁ i).left ≫ prj p = spMap (Chart.dualMapR f) ≫ (v (i.cast (g_eq p))).left) :
    KeyPB ⟨D₁.P, g₁, D₁.rig, D₁.rig_gen, th₁, n₁, v₁, hv₁⟩ ⟨D₀.P, g₀, D₀.rig, D₀.rig_gen, th, n₀, v, hv⟩ f := by
  refine ⟨prj p, p.he, p.w, g_eq p, Chart.dualMapR f, pull_grp p, p.w_gen, p.w_rig,
    KeyPow.appLE_eq_of_stalk _ th th₁ ((ArcQBC.through_iff _ _).1 h), fun a => ?_, ?_, hvv⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end Pull

section Val

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {V Fr : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Field Fr] [Algebra V Fr] [IsFractionRing V Fr] {io : K →+* Fr}

theorem mem_range_iff (h : OverLa w V io 1) (y : K) :
    io y ∈ Set.range (algebraMap V Fr) ↔ w.valuation K y ≤ 1 := by
  have e : io y ∈ Set.range (algebraMap V Fr) ↔ valV V (io y) ≤ 1 :=
    ⟨fun ⟨r, hr⟩ => hr ▸ HeightOneSpectrum.valuation_le_one _ r,
      fun hy => IsDiscreteValuationRing.exists_lift_of_le_one hy⟩
  rw [e]
  by_cases hy : y = 0
  · simp [hy]
  have h1 := h.2 y
  simp only [vV, vLa, Nat.cast_one, _root_.one_mul, neg_inj] at h1
  have a : valV V (io y) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 hy)
  have b : w.valuation K y ≠ 0 := ((w.valuation K).ne_zero_iff).2 hy
  rw [← WithZero.log_le_log a one_ne_zero, ← WithZero.log_le_log b one_ne_zero, h1]

theorem vV_eq_neg_count (h : OverLa w V io 1) {gm : Fr} {ca : K} {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
    (hc : IsLocGen w ca I) (u : Vˣ) (e : gm⁻¹ = io ca * algebraMap V Fr u) : vV V gm = -FractionalIdeal.count K w I := by
  have hu : valV V (algebraMap V Fr u) = 1 := by
    refine eq_one_of_one_le_mul_left (HeightOneSpectrum.valuation_le_one _ (u : V))
      (HeightOneSpectrum.valuation_le_one (K := Fr) (IsDiscreteValuationRing.maximalIdeal V) ((u⁻¹ : Vˣ) : V)) ?_
    rw [valV, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h1 := h.2 ca
  have h2 := congrArg (valV V) e
  rw [map_mul, hu, _root_.mul_one, map_inv₀, inv_eq_iff_eq_inv] at h2
  simp only [vV, vLa, Nat.cast_one, _root_.one_mul, neg_inj] at h1
  rw [vV, h2, WithZero.log_inv, h1, valuation_eq_exp_count w hc.1, hc.2]
  simp

end Val

theorem exists_ringHom {K R V Fr : Type} [Field K] [CommRing R] [Algebra R K] [CommRing V] [Field Fr] [Algebra V Fr]
    (hi : Function.Injective (algebraMap V Fr)) (io : K →+* Fr)
    (h : ∀ r : R, io (algebraMap R K r) ∈ Set.range (algebraMap V Fr)) :
    ∃ j : R →+* V, (algebraMap V Fr).comp j = io.comp (algebraMap R K) := by
  choose j hj using h
  exact ⟨⟨⟨⟨j, hi (by simp [hj])⟩, fun a b => hi (by simp [hj])⟩, hi (by simp [hj]), fun a b => hi (by simp [hj])⟩,
    RingHom.ext hj⟩

theorem exists_keyIntegral {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {V Fr : Type} [CommRing V]
    [IsDomain V] [Field Fr] [Algebra V Fr] (hi : Function.Injective (algebraMap V Fr)) {io : K →+* Fr}
    (hval : ∀ y : K, io y ∈ Set.range (algebraMap V Fr) ↔ w.valuation K y ≤ 1)
    {D : Out.DegPre K} {DV : Out.DegPre V} {DF : Out.DegPre Fr} (pw : Out.IsPullDeg (algebraMap V Fr) DV DF)
    (pK : Out.IsPullDeg io D DF) {th : D.P.L.Sec} {thw : DV.P.L.Sec} {th₁ th₂ : DF.P.L.Sec} {gm : Fr} (hgm : gm ≠ 0)
    (nw : ThNZ thw) (h₁ : ThBC pw thw th₁) (h₂ : ThBC pK th th₂) (hm : ThMul gm th₁ th₂) {g₀ n₀ v hv}
    {B : Out.PolAV (Sp (𝓞 K))} {φ : D.P.A.left ⟶ B.A.left}
    (hφ : IsGrpPullback D.P.A B.A (spMap (algebraMap (𝓞 K) K)) φ) {ρ : 𝓞 K →+* V} {ψ : DV.P.A.left ⟶ B.A.left}
    (hρ : ∀ x, algebraMap V Fr (ρ x) = io (x : K)) (hψ : IsGrpPullback DV.P.A B.A (spMap ρ) ψ)
    (hc : prj pw ≫ ψ = prj pK ≫ φ) {M : Matrix (Fin D.P.g) (Fin D.P.g) K}
    (hM : IsModelAt B ⟨D.P, g₀, D.rig, D.rig_gen, th, n₀, v, hv⟩ φ w M) :
    ∃ x' : KeyIn Fr, KeyPB x' ⟨D.P, g₀, D.rig, D.rig_gen, th, n₀, v, hv⟩ io ∧ KeyIntegral V x' gm⁻¹ (io M.det) := by
  obtain ⟨R, _, _, _, _, _, ρR, xR, φR, hg, hρR, hvalR, hfib, -, hw⟩ := hM
  obtain ⟨j, hj⟩ := exists_ringHom hi io fun r : R => (hval _).2 ((hvalR _).1 ⟨r, rfl⟩)
  have hjρ : j.comp ρR = ρ := RingHom.ext fun x => hi (by
    rw [hρ, RingHom.comp_apply, ← RingHom.comp_apply (algebraMap V Fr), hj, RingHom.comp_apply,
      ← RingHom.comp_apply (algebraMap R K), hρR])
  have hG : IsGrpPullback xR.P.A B.A (spMap ρR) φR := hfib.1
  have n : IsGrpPullback DV.P.A B.A (spMap j ≫ spMap ρR) ψ :=
    hψ.congr (by rw [spMap_comp_spMap]; exact congrArg spMap hjρ.symm) rfl
  have sq : ψ ≫ B.A.hom = (DV.P.A.hom ≫ spMap j) ≫ spMap ρR := n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := hG.1.lift_fst _ _ sq
  have e₂ := hG.1.lift_snd _ _ sq
  generalize hG.1.lift _ _ sq = ψ' at e₁ e₂
  have hψ' : IsGrpPullback DV.P.A xR.P.A (spMap j) ψ' := hG.cancel (e₁ ▸ n) e₂
  have eK : DF.P.g = D.P.g := g_eq pK
  have eV : DF.P.g = DV.P.g := g_eq pw
  have eR : DV.P.g = xR.P.g := eV.symm.trans (eK.trans hg.symm)
  have := D.P.isAb.comm
  have := DV.P.isAb.comm
  have := DF.P.isAb.comm
  have := xR.P.isAb.comm
  obtain ⟨vV, hvV, eVv⟩ := exists_isLieBasis_baseChange R V j _ _ ψ' hψ' xR.P.isAb.smooth _ _ (isLieBasis_cast eR xR.basis)
  obtain ⟨v₁, hv₁, ev₁⟩ := exists_isLieBasis_baseChange V Fr _ _ _ (prj pw) (pull_grp pw) DV.P.isAb.smooth _ _
    (isLieBasis_cast eV hvV)
  obtain ⟨v₂, hv₂, ev₂⟩ := exists_isLieBasis_baseChange K Fr _ _ _ (prj pK) (pull_grp pK) D.P.isAb.smooth _ _
    (isLieBasis_cast eK hv)
  have gF : 1 ≤ DF.P.g := eK ▸ g₀
  refine ⟨⟨DF.P, gF, DF.rig, DF.rig_gen, th₂, ArcQBC.thNZ_of_thBC pK h₂ n₀, v₂, hv₂⟩, keyPB_of_pull pK h₂ ev₂,
    th₁, ArcQBC.thNZ_of_thBC pw h₁ nw, v₁, hv₁, (M.submatrix (Fin.cast eK) (Fin.cast eK)).map io,
    ⟨DV.P, eV ▸ gF, DV.rig, DV.rig_gen, thw, nw, vV, hvV⟩, fun i => ?_, fun i => ?_, ?_, keyPB_of_pull pw h₁ ev₁⟩
  · show th₁.f i = constFn DF.P.A.hom _ gm⁻¹ * th₂.f i
    rw [hm i, ← _root_.mul_assoc, ← KeyPow.constFn_mul, inv_mul_cancel₀ hgm, KeyPow.constFn_one, _root_.one_mul]
  · obtain ⟨wK, hwK, hwK'⟩ := hw (i.cast eK)
    refine (lieComb_baseChange K Fr io _ _ (prj pK) (pull_grp pK) _ _ wK _ v₂ (v₁ i) ev₂ (isLieComb_cast eK hwK)).1
      (hφ.1.hom_ext ?_ ?_)
    · have hd : Formalism.L2.Pj.dualMap (algebraMap R K) = Chart.dualMapR (algebraMap R K) := rfl
      rw [Category.assoc, ← hc, ← Category.assoc, ev₁, ← e₁, Category.assoc, ← Category.assoc (vV _).left, eVv,
        Category.assoc, Category.assoc, hwK', hd, ← Category.assoc, ← Category.assoc (spMap (Chart.dualMapR io)),
        dual_comp, dual_comp, hj]
      rfl
    · rw [Category.assoc, (pull_grp pK).1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (LieCombBaseChange.dualMap_over io).symm
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact congrArg io (Matrix.det_submatrix_equiv_self (finCongr eK) M)

theorem vV_gamma : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → M.γ ≠ 0 → vV Tv.V M.γ = -FractionalIdeal.count K₁ w s.Tl.I := by
  intro _ E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ hO hρ hψ hc _ hgm
  obtain ⟨-, -, -, hB, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hloc, -, hmod⟩ := s.good
  obtain ⟨N, hN, hL⟩ := hmod w
  obtain ⟨th₁, th₂, h₁, h₂, hm⟩ := M.th_tie
  have hval := mem_range_iff hO
  obtain ⟨x', hPB, hInt⟩ := exists_keyIntegral (IsFractionRing.injective Tv.V Tv.Fr) hval M.pw M.pK hgm M.thw_nz h₁ h₂ hm
    hB.1 hρ hψ.2.1 hc hN
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ca, _, _, _, -, -, -, -, -, hca, -⟩ := hloc w
  obtain ⟨u, hu⟩ := KeyVal.integral_section_unit K₁ _ _ _ w (hloc w) Tv.V Tv.Fr io x' _ _ ca N.det 1 hval hPB hInt hL
    (by simp) hca
  exact vV_eq_neg_count hO hca u hu

end GlobalTheory.ArcGamma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionaryStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicArc_agrees_analyticDictionary : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (Λ : GtAn₀ a), letI := H.starRing; ∃ (gam : (Fu.Di Ha.i).La ≃ₗ[𝓞 E] Λ.A.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] Λ.A.V), (∀ z, Λ.ex₀ (h z) = Ha.ex₀ z) ∧ (∀ v, Λ.y (gam v) = Ha.y v) ∧ (∀ w v, h (Ha.Pw w v) = Λ.A.Pw w (gam v)) ∧ ∀ v v', Λ.A.EF (gam v) (gam v') = (Fu.Di Ha.i).EF v v' := by
  first | exact @GlobalTheory.ArcCompare.holArc_agrees | exact GlobalTheory.ArcCompare.holArc_agrees | (intros; apply GlobalTheory.ArcCompare.holArc_agrees <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LaurentCoeffSectionValueArcEqFourierJacobiStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCoeff_sectionValue_arc_eq_fourierJacobi : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (th : a.D₀.P.L.Sec) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c σ → IsUnf U → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ w₁ : ℂ, Ha.T < w₁.im → ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E) (C : ℝ), (U.X k).IsIso ξ' ∧ IsBePar ξ a.be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ 0 < C ∧ (∀ v, Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → C ≤ v * Real.sqrt |((NumberField.discr E : ℤ) : ℝ)|) ∧ ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)) (y : FrPt Xo c ℂ⸨X⸩), IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ∃ (x : (U.X k).dom) (κ : ℂ), ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), (∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w₁ v)) ∧ (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') ∧ ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → (evR Xo c F y).coeff jj * eTwoPi w₁ ^ jj = κ * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 := by
  first | exact @GlobalTheory.ArcCoeff.coeff_evR_eq_fj | exact GlobalTheory.ArcCoeff.coeff_evR_eq_fj | (intros; apply GlobalTheory.ArcCoeff.coeff_evR_eq_fj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LetterSquaredLengthLeFlowHeightStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.letter_squaredLength_le_flow_height : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (aC : ArcIn Dw l β ℂ (σ.comp β)) (p : Out.IsPullDeg em a.D₀ aC.D₀) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y aC χ) (Ha : HolArc Y σ aC χ W Uw.F) (k : U.Comp) (ξ' : Fin r → E) (x x'' : (U.X k).dom) (sf : (U.X k).Ψ → ℂ) (w₁ : ℂ) (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La) (ep : ℝ) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ), σ = em.comp (algebraMap c.F K₁) → GoodEmb c σ → IsUnf U → InBC em (a.restrict β) aC p → 1 ≤ La → 0 < ep → (U.X k).IsIso ξ' → Ha.T < w₁.im → (∀ v, Uw.Pm k x (gm v) = L (Ha.Pw w₁ v)) → (∀ v v', (Uw.F.Di (Uw.ik k)).EF (gm v) (gm v') = (Uw.F.Di Ha.i).EF v v') → (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = s.ξ (p.xe (Ha.y v'))) ∧ (Uw.φ k (gm t) : Fin r → E) = ξ') → x''.1 = (U.X k).flow ξ' sf x.1 → (∀ τ, (U.X k).tt ξ' x''.1 τ = ep) → IsRiem Uw.F (Uw.ik k) (Uw.Pm k x'') Hm → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (eC : Out.GtPt aC.D₀ (epsR ℂ)) (z : Fin Uw.g → ℂ), LetBC p (e τ i) eC → AnVec Ha eC z → Real.pi * (hermForm Hm (L z) (L z)).re ≤ (La * Real.sqrt (max 1 ep⁻¹) * (s.line τ i).n em) ^ 2 := by
  first | exact @GlobalTheory.LetterLen.letter_length_le | exact GlobalTheory.LetterLen.letter_length_le | (intros; apply GlobalTheory.LetterLen.letter_length_le <;> assumption)
end

