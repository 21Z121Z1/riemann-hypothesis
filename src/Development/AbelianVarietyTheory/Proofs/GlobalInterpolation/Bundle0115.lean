import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0109
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0111
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0075
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0078
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0112
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0089
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrime
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0113

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DeltaNeZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.SeamMoves

variable {X : Fields} {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
  (cD : D.what₂.Tau → ℂ)

def reidx (a b : ℕ) : VCx X.Tau a b ≃ₗ[ℂ] TaylorLogMetric.VC D a b := LinearEquiv.funCongrLeft ℂ (Fin b → Fin a → ℂ) s.iT.symm

theorem form_reidx (A : ℝ) (a b : ℕ) (x y : VCx X.Tau a b) :
    formV A D.what₂.Tau a b (reidx s a b x) (reidx s a b y) = Formalism.L2.Ker.HV A⁻¹ x y := by
  change (∑ τ, ∑ i, ∑ j, x (s.iT.symm τ) i j * (starRingEnd ℂ) (y (s.iT.symm τ) i j)) / (A : ℂ) =
    ((A⁻¹ : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)
  rw [Equiv.sum_comp s.iT.symm (fun τ => ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)), Complex.ofReal_inv, div_eq_inv_mul]

theorem isHerm_formV (A : ℝ) (n : Type) [Fintype n] (a b : ℕ) : IsHerm (formV A n a b) := by
  intro x y
  simp [formV, map_sum, mul_comm]

theorem iop_eq {a b : ℕ} (Λ₁ Λ₂ : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.Iop D B.tor Λ₁ Λ₂ G = inter (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) Λ₁ Λ₂ G := rfl

theorem alV_eq {a b : ℕ} (x : VCx X.Tau a b) {m : ℤ}
    (hm : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x)).re = (m : ℝ)) :
    alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x = TaylorLogMetric.al D B.tor (reidx s a b x) := by
  have h1 : TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x) = Formalism.L2.Ker.HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x x :=
    form_reidx s _ a b x x
  unfold TaylorLogMetric.al
  rw [hm, round_intCast]
  rw [h1] at hm
  unfold alV alphaQ Formalism.L2.Th1.H.qOf
  rw [hm, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

include B in
theorem delta_ne_zero : δ ≠ 0 := by
  rintro rfl
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  have h2 : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨c, -, rfl⟩
    simp
  rw [B.lat] at h1
  have h3 : B.L.ω₁ = 0 := AddSubgroup.mem_bot.1 (h2 h1)
  exact B.L.indep.ne_zero 0 h3

theorem aa_ne_bot (hcc : cc ≠ ⊥) : (ambOf s B χ cD).AA ≠ ⊥ := by
  intro h
  have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
    refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
    simp
  rw [h, Submodule.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h1
  exact hcc h1

theorem aa_fg : (ambOf s B χ cD).AA.FG := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  obtain ⟨z, hz, hden⟩ := D.host.AA0.isFractional
  have hz0 : j z ≠ 0 := fun h => nonZeroDivisors.ne_zero hz (by
    have h1 := hj z
    rw [h] at h1
    have h2 : (z : D.host.E) = 0 := s.iE.symm.injective (by rw [← h1]; simp)
    exact RingOfIntegers.coe_injective (by simpa using h2))
  have hfr : IsFractional (nonZeroDivisors (𝓞 X.E)) (ambOf s B χ cD).AA := by
    refine (FractionalIdeal.isFractional_span_iff).2 ⟨j z, mem_nonZeroDivisors_of_ne_zero hz0, ?_⟩
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    have hw' : (w : D.host.E) = (z : D.host.E) * t := by rw [Algebra.smul_def] at hw; exact hw
    rw [e, hw']
    ring
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl ⟨_, hfr⟩

theorem vac_eq {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (h : Base.chiFac χ a b (s.lat N) (s.lat N') ≠ 0) :
    vac (ambOf s B χ cD) N N' = fun z => B.thMoved a b (s.lat N) (s.lat N') (reidx s a b z) := by
  funext z
  exact inv_mul_cancel_left₀ h _

theorem moves_ambOf : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → Moves (ambOf s B χ cD) a b := by
  intro X D s cc δ B χ cD a b hX hs hcc hχ hE hL hZ ha hb
  obtain ⟨hsd, hlam⟩ := GlobalTheory.T.fieldIso_selfDual_and_periodLattices_agree X D s cc δ B χ cD hs
  obtain ⟨hth, hm1, hm2⟩ := GlobalTheory.T.movedVacuum_mem_thetaFunctions_and_moves D cc δ B χ a b hχ hE hL hZ ha hb
  have hq := GlobalTheory.T.quadraticForm_integral_of_selfDual_periodLattices D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  have key := fun (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) (h : IsSdLat N₂)
      (h' : IsSdLat N₂') (θ : TaylorLogMetric.VC D a b → ℂ) =>
    Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N₁ N₁') (lam (ambOf s B χ cD) N₂ N₂') (TaylorLogMetric.La D B.tor (s.lat N₁) (s.lat N₁'))
      (TaylorLogMetric.La D B.tor (s.lat N₂) (s.lat N₂')) θ (form_reidx s _ a b) (hlam a b N₁ N₁') (hlam a b N₂ N₂')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N₂ N₂' h h') (reidx s a b x) ((hlam a b N₂ N₂' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N₂ N₂' h h')).1 (hL.1 a b _ _ (hadm N₂ N₂' h h')).2
  refine ⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, aa_fg s B χ cD, aa_ne_bot s B χ cD hcc.1, ?_, ?_, ?_⟩
  · intro N N' h h'
    obtain ⟨hc, han, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    obtain ⟨h1, h2, h3⟩ := (key N N N' N' h h' 0).1
    refine ⟨hc, ?_, h1, h2⟩
    rw [vac_eq s B χ cD N N' hc]
    refine ⟨fun z _ => ?_, h3 _ hfix⟩
    exact (han _ (Set.mem_univ _)).comp ((reidx s a b).toLinearMap.toContinuousLinearMap.analyticAt z)
  · intro N N' N'' h h' h''
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N N'' (hth _ _ (hsd _ _ h) (hsd _ _ h'')).1,
      (key N N N' N'' h h'' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N N'' h h'')).1,
      hm1 _ _ _ (hsd _ _ h) (hsd _ _ h') (hsd _ _ h''), iop_eq]
  · intro N N₁ N' h h₁ h'
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N₁ N' (hth _ _ (hsd _ _ h₁) (hsd _ _ h')).1,
      (key N N₁ N' N' h₁ h' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N₁ N' h₁ h')).1,
      hm2 _ _ _ (hsd _ _ h) (hsd _ _ h₁) (hsd _ _ h'), iop_eq]

end GlobalTheory.ThetaMove.SeamMoves
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasWithDutyWallAndChoices
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC

theorem has_withDuty_wall_and_choices {Q : PtProp} {C : FC} {cD ch C8 C5 c6 Cb : ℝ} (p : Pt C) {R : Ranks} {H : Host R} {q0 : ℕ}
    {a b : R.A → ℤ} {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} {u0 : ℕ} (hC : Std C) (hT : H.CT2 = C.CT2)
    (hH : HostGood p.L.sc C8 C5 c6 Cb H q0) (hq : (q0 : ℝ) < p.L.sc.X')
    (h0 : ∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) (hW : WOK p.L.sc cD ch C.GK H a b)
    (hV : Val C cD ch p.L) (hF : p.From H a b c u0) (hI : CanonInst p.ta.Gx) (hQ : p.Has Q) :
    p.Has ((withDuty Q).and WallPt) ∧ ThickSetLowerBound p.L ∧ ChBad_at p.ta.Gx Cb ∧ ChQD_at p.D p.L.sc.x p.L.sc.eps C5 := by
  have hw := GlobalTheory.EX.wreq_of_wok C cD ch p R H a b M c u0 hC hV hF hI h0 hW
  obtain ⟨hv, -, hT2, -, hQD, hBox, -, -, hBad, -, -, -, ⟨hp, hmod, -, hne, hne'⟩, hlev⟩ := hH
  have hb := GlobalTheory.EX.chBad_of_from C p R H a b M c u0 Cb hF hI hBad
  have eS := hF.QS_eq
  have hBW := hF.boxesW hBox
  have hQW := hF.qdRowsW hBox
  obtain ⟨eR, -, eT2, eq, ed, eg, ep, ep', hsub, -⟩ := hF
  subst eR
  have hq0 : (0 : ℝ) < q0 := by exact_mod_cast hp.pos
  have hXb := X'_le_b p.L.sc
  refine ⟨⟨⟨hQ, hw, ?_, ?_, q0, hsub (by rw [hlev]; simp), hp, ?_, ?_, hq, ?_, ?_, ?_⟩,
    ⟨hV.mem_box.1, hV.mem_box.2, hw⟩⟩, ?_, hb, ?_⟩
  · exact hBW
  · exact hQW
  · rw [eS, eq, ed]; exact hmod
  · rw [Real.log_le_iff_le_exp hq0]
    exact hq.le.trans hXb
  · rw [ep]; exact hne
  · rw [ep']; exact hne'
  · intro i hi
    have hg := (hv.2.2.2.2.1 i).1
    rw [← eg, ← hi] at hg
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  · unfold ThickSetLowerBound Host.secondSet_card_lower_bound
    rw [eT2, hV.secondConstant_eq, hV.host.2.2.2.2.2.1, ← hT, ← hv.2.2.2.2.2.1]
    exact hT2
  · unfold ChQD_at
    rw [eq, ed]
    exact hQD

end GlobalTheory.EX.DC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeCharProductFormulaNormOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Formalism.L2.Host (HChar atFin upF aboveF IsUnitAt ordF)
open GlobalTheory.CharVal (valuation_conjP conjP_conjP')
open GlobalTheory.NormOneUnit (locK_unr locK_tame exists_of_star_eq under_eq_iff)

namespace GlobalTheory.NormOneProd

variable {E : Type} [Field E] [NumberField E] [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E]

omit [StarRing E] in

theorem exists_val_eq {P : HeightOneSpectrum (𝓞 E)}
    (hu : ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) (x : Eˣ) :
    ∃ k : Fˣ, P.valuation E ((x / upF F k : Eˣ) : E) = 1 := by
  obtain ⟨k, hk⟩ := (P.under (𝓞 F)).valuation_surjective F (P.valuation E (x : E))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at hk
    exact x.ne_zero hk
  refine ⟨Units.mk0 k hk0, ?_⟩
  have hy' : ((x / upF F (Units.mk0 k hk0) : Eˣ) : E) = x / algebraMap F E k := Units.val_div_eq_div_val _ _
  rw [hy', map_div₀, GlobalTheory.MuConj.valuation_up P hu, hk, div_self (by simp)]

theorem split_unit (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P ≠ conjPrime₂ P) {y y' : Eˣ} (hy : (y' : E) = star (y : E))
    (h2 : (conjPrime₂ P).valuation E (y : E) = 1) : χ.locK P y' * χ.locK (conjPrime₂ P) y = 1 := by
  classical
  obtain ⟨e, he, e', he', hee⟩ := exists_coprime hP
  have he1 : P.valuation E (e : E) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 he
  have hy0 : P.valuation E (y : E) ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ he1 (Units.mk0 _ hy0)⁻¹
  have hn' : P.valuation E ((e : E) ^ n * y) < 1 := by
    rw [map_mul, map_pow]
    rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hn
    rwa [← lt_div_iff₀ (zero_lt_iff.2 hy0), one_div]
  have hm : e ^ n - 1 ∈ (conjPrime₂ P).asIdeal := by
    refine Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one e n) ?_
    have : e - 1 = -e' := by rw [← hee]; ring
    rw [this]
    exact neg_mem he'
  obtain ⟨k, hk⟩ := exists_of_star_eq hF hr hc (x := (e : E) ^ n * y + star ((e : E) ^ n * y : E))
    (by rw [star_add, star_star, add_comm])
  have v1 : (conjPrime₂ P).valuation E (algebraMap F E k - y) < 1 := by
    have e1 : algebraMap F E k - y = ((e ^ n - 1 : 𝓞 E) : E) * y + star ((e : E) ^ n * y : E) := by
      rw [hk]; push_cast; ring
    rw [e1]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul, h2, mul_one]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hm
    · rw [valuation_conjP, star_star]
      exact hn'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_sub, Valuation.map_neg, h2] at v1
    exact lt_irrefl _ v1
  have a1 : χ.locK (conjPrime₂ P) (upF F (Units.mk0 k hk0)) = χ.locK (conjPrime₂ P) y := locK_tame (ht _) h2 v1
  have a2 : χ.locK P (upF F (Units.mk0 k hk0)) = χ.locK P y' := by
    refine locK_tame (ht _) (hy ▸ (valuation_conjP P _).symm.trans h2) ?_
    rw [valuation_conjP, star_sub, hF, ← hy] at v1
    exact v1
  have hab : aboveF (L := E) F (P.under (𝓞 F)) = {P, conjPrime₂ P} := by
    ext Q
    rw [GlobalTheory.Mem.ReadTwist.mem_above, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff hF hr hc P Q
  have h := hχ.1 (P.under (𝓞 F)) (Units.mk0 k hk0)
  rwa [HChar.resFin_apply, hab, Finset.prod_pair hP, a1, a2] at h

open Classical in

theorem place_prod (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a)
    (hu : ∀ P : HeightOneSpectrum (𝓞 E),
      ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2)
    {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) (hun : ∀ P, conjPrime₂ P = P → χ.UnrAt P)
    {x z : Eˣ} (hxz : (x : E) = z * star (x : E)) (P : HeightOneSpectrum (𝓞 E)) :
    ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q x = χ.locK P z := by
  obtain ⟨k, hk⟩ := exists_val_eq (hu (conjPrime₂ P)) x
  set y : Eˣ := x / upF F k with hy
  have hy' : (y : E) = x / algebraMap F E k := Units.val_div_eq_div_val _ _
  have hyz : (y : E) = z * star (y : E) := by
    rw [hy', star_div₀, hF, ← mul_div_assoc, ← hxz]
  have h := hχ.1 (P.under (𝓞 F)) k
  rw [HChar.resFin_apply] at h
  have e1 : ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q x = ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q y := by
    simp only [hy, map_div, Finset.prod_div_distrib, h, div_one]
  have hab : aboveF (L := E) F (P.under (𝓞 F)) = {P, conjPrime₂ P} := by
    ext Q
    rw [GlobalTheory.Mem.ReadTwist.mem_above, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff hF hr hc P Q
  rw [e1, hab]
  by_cases hP : P = conjPrime₂ P
  · have h1 : P.valuation E (y : E) = 1 := hP ▸ hk
    have h2 : P.valuation E (z : E) = 1 := by
      have h3 := congrArg (P.valuation E) hyz
      rw [map_mul, ← valuation_conjP, hk, h1, mul_one] at h3
      exact h3.symm
    rw [← hP, Finset.pair_eq_singleton, Finset.prod_singleton, locK_unr (hun P hP.symm) h1, locK_unr (hun P hP.symm) h2]
  · have hs0 : star (y : E) ≠ 0 := star_ne_zero.2 y.ne_zero
    have h3 := split_unit hF hr hc hχ ht hP (y' := Units.mk0 _ hs0) rfl hk
    have e2 : y = z * Units.mk0 _ hs0 := Units.ext hyz
    rw [Finset.prod_pair hP, congrArg (χ.locK P) e2, map_mul, mul_assoc, h3, mul_one]

theorem inf_mul_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (rep : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E)) (V : Finset (HeightOneSpectrum (𝓞 F))) (x z : Eˣ), (∀ y : F, star (algebraMap F E y) = algebraMap F E y) → Module.finrank F E = 2 → (∃ a : E, star a ≠ a) → (∀ P : HeightOneSpectrum (𝓞 E), ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) → χ.TrivOn F → (∀ P, χ.TameAt P) → (∀ P, conjPrime₂ P = P → χ.UnrAt P) → (∀ v, (rep v).under (𝓞 F) = v) → (x : E) = z * star (x : E) → (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ V → χ.UnrAt P ∧ P.valuation E (x : E) = 1) → χ.inf x * ∏ v ∈ V, χ.locK (rep v) z = 1 := by
  intro F E _ _ _ _ _ _ χ rep V x z hF hr hc hu hχ ht hun hrep hxz hV
  classical
  have hm : ∀ P : HeightOneSpectrum (𝓞 E), P ∈ V.biUnion (aboveF (L := E) F) ↔ P.under (𝓞 F) ∈ V := fun P => by
    simp only [Finset.mem_biUnion, GlobalTheory.Mem.ReadTwist.mem_above, exists_eq_right']
  have h := GlobalTheory.HeckeProduct.productRule χ (V.biUnion (aboveF (L := E) F)) (fun P hP => (hV P fun e => hP ((hm P).2 e)).1) x
  have hfp : (∏ᶠ (P : HeightOneSpectrum (𝓞 E)) (_ : P ∉ V.biUnion (aboveF (L := E) F)), χ.val P ^ ordF P x) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun P => ?_
    by_cases hP : P ∈ V.biUnion (aboveF (L := E) F)
    · rw [finprod_eq_if, if_neg (not_not.2 hP)]
    rw [finprod_eq_if, if_pos hP, ordF, (hV P fun e => hP ((hm P).2 e)).2, WithZero.log_one, neg_zero, zpow_zero]
  have hpl : ∀ v ∈ V, ∏ Q ∈ aboveF (L := E) F v, χ.locK Q x = χ.locK (rep v) z := fun v _ => by
    have := place_prod hF hr hc hu hχ ht hun hxz (rep v)
    rwa [hrep] at this
  rw [hfp, mul_one, Finset.prod_biUnion, Finset.prod_congr rfl hpl] at h
  · exact h
  · intro v _ w _ hvw
    exact Finset.disjoint_left.2 fun P h1 h2 =>
      hvw ((GlobalTheory.Mem.ReadTwist.mem_above.1 h1).symm.trans (GlobalTheory.Mem.ReadTwist.mem_above.1 h2))

end GlobalTheory.NormOneProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwColumn

variable {D : D7} {u : D.what₂.Word}

def WtSigns (X : Ch D u) : Prop :=
  (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) ∧ ∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ

theorem levelChainSharpColumnValuation_of_pointKernelLiftLaws (X : Ch D u) (Lv : LevTie X) (Vt : ValTie Lv) (Kt : KerTie Lv) (hK : KerLaws Vt Kt)
    (hS : StabUnit X) (hW : WtSigns X) : Conclusion5Sharp X := by
  have hB : WtBounds X := wtBounds_of_nonneg D u X hW.1 hW.2
  exact levelChainSharpColumnValuation_of_stability D u X (formsStable_of_tgtEq D u X Lv Kt hK.tgt)
    (levelChainUOperatorCommutation_of_pointPairLaw D u X Lv Kt hK.tgt hK.uk) (UKS.ukSharp D u X Lv Vt Kt hK hS hB) hB

private theorem Fi_zero_eq_span_range_emb (Z : Ch D u) :
    Z.fm.Fi 0 = Submodule.span ℂ (Set.range (Z.fm.emb 0)) := by
  apply le_antisymm
  · rw [← (Z.fm.emb_basis 0).2]
    exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact emb_mem_Fi Z 0 x

private theorem mem_Fi_zero_iff_of_shared {X Y : Ch D u} {e : Fn X 0 ≃ₗ[ℂ] Fn Y 0} {eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0}
    (h : Shared X Y e eL) (φ : Fn X 0) : e φ ∈ Y.fm.Fi 0 ↔ φ ∈ X.fm.Fi 0 := by
  obtain ⟨ev, eF, hs⟩ := h
  have hmap : Y.fm.Fi 0 = (X.fm.Fi 0).map (e : Fn X 0 →ₗ[ℂ] Fn Y 0) := by
    rw [Fi_zero_eq_span_range_emb, Fi_zero_eq_span_range_emb, Submodule.map_span]
    congr 1
    ext ψ
    constructor
    · rintro ⟨y, rfl⟩
      have hy := hs.emb_eq (eL.symm y)
      rw [eL.apply_symm_apply] at hy
      exact ⟨X.fm.emb 0 (eL.symm y), ⟨_, rfl⟩, hy.symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨eL x, hs.emb_eq x⟩
  rw [hmap]
  constructor
  · rintro ⟨ψ, hψ, hψe⟩
    rwa [← e.injective hψe]
  · intro hφ
    exact ⟨φ, hφ, rfl⟩

theorem step0Tie_of_twTie (Tw : TwForms D) (μ : D.what₂.Tup) (h : TwTie Tw u μ) (hU : UComm (own D u)) :
    Step0Tie Tw u μ := by
  intro w hw
  obtain ⟨ev, eF, hs⟩ := h
  have hwo : OverT (own D u) w := (hs.overT_iff w).1 ((OverT_tw Tw μ w).2 hw)
  refine ⟨hs.seen_eq w hwo, fun x hx => ?_⟩
  exact (TwTie.Nlam_iff ⟨ev, eF, hs⟩ hU hw x).2 hx

theorem uComm_own_of_twTie (Tw : TwForms D) (μ : D.what₂.Tup) (h : TwTie Tw u μ) (hU : UComm (tw Tw u μ)) :
    UComm (own D u) := by
  have hF := mem_Fi_zero_iff_of_shared h
  obtain ⟨ev, eF, hs⟩ := h

  have hmem : ∀ v, ∀ φ ∈ (own D u).fm.Fi 0, Uop (own D u) 0 v φ ∈ (own D u).fm.Fi 0 := by
    intro v φ hφ
    rw [← hF, hs.U_eq v φ hφ]
    exact hU.1 _ _ ((hF φ).2 hφ)
  refine ⟨hmem, fun v v' hvv' φ hφ => (D.e0Tw u μ).injective ?_⟩
  rw [hs.U_eq v _ (hmem v' φ hφ), hs.U_eq v' φ hφ, hs.U_eq v' _ (hmem v φ hφ), hs.U_eq v φ hφ]
  exact hU.2 _ _ (fun he => hvv' (ev.injective he)) _ ((hF φ).2 hφ)

theorem tuple_chain_sharp_column_valuation (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup)
    (Lv : LevTie (tw Tw u μ)) (Vt : ValTie Lv) (Kt : KerTie Lv) (hK : KerLaws Vt Kt)
    (hS : StabUnit (tw Tw u μ)) (hW : WtSigns (tw Tw u μ)) (h0 : Step0Tie Tw u μ) : TupleChainSharpColumnValuation Tw u μ :=
  TwSharp.tupleChainSharpColumnValuation_of_twisted D u Tw μ h0 (levelChainSharpColumnValuation_of_pointKernelLiftLaws (tw Tw u μ) Lv Vt Kt hK hS hW)

theorem tupleChainSharpColumnValuation_of_kerLaws (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup) (h0 : TwTie Tw u μ)
    (Lv : LevTie (tw Tw u μ)) (Vt : ValTie Lv) (Kt : KerTie Lv) (hK : KerLaws Vt Kt)
    (hS : StabUnit (tw Tw u μ)) (hW : WtSigns (tw Tw u μ)) : TupleChainSharpColumnValuation Tw u μ := by

  have hF : FormsStable (tw Tw u μ) := formsStable_of_tgtEq D u _ Lv Kt hK.tgt
  have hUt : UComm (tw Tw u μ) :=
    ⟨fun v φ hφ => hF.1 0 (Nat.zero_le _) v φ hφ, fun v v' _ φ hφ => hF.2.1 0 (Nat.zero_le _) v v' φ hφ⟩
  exact tuple_chain_sharp_column_valuation D u Tw μ Lv Vt Kt hK hS hW
    (step0Tie_of_twTie Tw μ h0 (uComm_own_of_twTie Tw μ h0 hUt))

end GlobalTheory.LvT.TwColumn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharEqHeckeCharLocalComponentOfValuesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localChar_eq_heckeChar_localComponent_of_values : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) (P : HeightOneSpectrum (𝓞 E)) (ψ : Formalism.L2.Host.HChar E) (cq : K) (t : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ), ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → (∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ cq = ((ψ.locK P q : ℂˣ) : ℂ)) → (∀ (x : Eˣ) (y : 𝓞 E) (c : (𝓞 E ⧸ P.asIdeal)ˣ), (x : E) = (y : E) → (c : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk P.asIdeal y → σ ((t c : Kˣ) : K) = ((ψ.locK P x : ℂˣ) : ℂ)) → ∀ a : Eˣ, σ (LocE.locChar (Formalism.L2.Col.qOf P) cq t (a : E)) = ((ψ.locK P a : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.LocCharComp.locChar_eq_locK | exact GlobalTheory.LocCharComp.locChar_eq_locK | (intros; apply GlobalTheory.LocCharComp.locChar_eq_locK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_primes_and_level_prime : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → NormPrimes ∧ LevelPrime := by
  first | exact @GlobalTheory.EX.normPrimes_and_levelPrime | exact GlobalTheory.EX.normPrimes_and_levelPrime | (intros; apply GlobalTheory.EX.normPrimes_and_levelPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBoundStatement
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X → Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / ((4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A * Real.log X) ≤ ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) := by
  first | exact @GlobalTheory.Hk.normPrimes_short_interval_lower | exact GlobalTheory.Hk.normPrimes_short_interval_lower | (intros; apply GlobalTheory.Hk.normPrimes_short_interval_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFactsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), A.AA.FG → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → (per A N N').FG ∧ (∀ x : HomE X.E a b, ∃ n : ℕ, 0 < n ∧ (n : X.E) • x ∈ per A N N') ∧ (∀ r : 𝓞 X.E, r ≠ 0 → (smulLat (r : X.E) (per A N N')).toAddSubgroup.relIndex (per A N N').toAddSubgroup ≠ 0) ∧ ∀ P : HeightOneSpectrum (𝓞 X.E), localization₂ P.asIdeal A.AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) → ∀ y : HomE X.E a b, y ∈ localization₂ P.asIdeal (per A N N') ↔ ∀ v ∈ localization₂ P.asIdeal N, y v ∈ localization₂ P.asIdeal N' := by
  first | exact @GlobalTheory.MomT.LatFin.per_lattice_facts | exact GlobalTheory.MomT.LatFin.per_lattice_facts | (intros; apply GlobalTheory.MomT.LatFin.per_lattice_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeOverColumnBaseLatticeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_over_columnBaseLattice : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase := by
  first | exact @GlobalTheory.OverObj.selfDualOverBase | exact GlobalTheory.OverObj.selfDualOverBase | (intros; apply GlobalTheory.OverObj.selfDualOverBase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameCharacterValuesEqHeckeCharLocalValuesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_character_values_eq_heckeChar_local_values : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K] (σ : K →+* ℂ) (μ : Chr F E K) (ξ : Formalism.L2.Host.HChar E), GlobalTheory.Mem.Col2.Reads σ μ ξ → (∀ P, ξ.TameAt P) → ∀ P : HeightOneSpectrum (𝓞 E), (ξ.UnrAt P → σ ((unifVal μ P : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ)) ∧ (((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ ((qVal μ P : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TwistVal.main | exact GlobalTheory.TwistVal.main | (intros; apply GlobalTheory.TwistVal.main <;> assumption)
end

