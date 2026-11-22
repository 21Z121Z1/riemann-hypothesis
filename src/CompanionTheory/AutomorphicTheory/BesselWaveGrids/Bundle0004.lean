import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TBBTie
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0293
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0004
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Bundle0001
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Assemble

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.NormalizedMeasureScaling
section
noncomputable section

namespace CompanionTheory.WaveGrid.Ties

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.Pf.BesselExpansion Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open scoped ENNReal

section energy

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {k r : ℕ}

theorem norm_JF_eq (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (d : Fin (r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) {γ γ' : B.Mat k r} (hγ : γ ∈ B.GV k r) (hγ' : γ' ∈ B.GV k r)
    (hZ : Zhat k r Bs.z Bs.z' γ = D.ptMatN (PBJ.bigPt d) (r + 1))
    (hZ' : Zhat k r Bs.z Bs.z' γ' = D.ptMatN (PBJ.bigPt d) (r + 1)) (hpos : 0 < Gf k r Bs.z Bs.z' γ) :
    ‖B.hsVec (B.JF Bs F γ)‖ = ‖B.hsVec (B.JF Bs F γ')‖ := by
  have hl : D.IsLocPt (PBJ.bigPt d) (r + 1) := PBJ.Dens.isLocPt_bigPt d hd
  have hpos' : 0 < Gf k r Bs.z Bs.z' γ' := by
    rw [← ptG_spec k r _ _ (PBJ.bigPt d) _ hl hZ', ptG_spec k r _ _ (PBJ.bigPt d) _ hl hZ]
    exact hpos
  obtain ⟨s, hs, s', hs', hγs⟩ := fibre_orbit_description k r Bs.z Bs.z'
    ⟨Bs.k_pos, Dx2.VV.std_vector_z Bs, Dx2.VV.std_vector_z_prime Bs⟩ _ hγ _ hγ' hpos (hZ.trans hZ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Dx2.VV.std_vector_z Bs) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Dx2.VV.std_vector_z_prime Bs) hs'
  have hlaw := Dx2.VV.orbJ_pt Bs (PBJ.bigPt d) hl hγ hZ hpos hhA hnA hfA hhB hnB hfB F
  rw [← hγs] at hlaw
  have hw : (hl.2 ▸ D.ptPerm (PBJ.bigPt d) : Equiv.Perm (Fin (r + 1))) = 1 :=
    PBM.cast_perm_eq_one _ _ (PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Dx2.VV.ptMatN_monoP' (PBJ.bigPt d) (r + 1) hl.2 hl.1
  rw [hw] at hmono hlaw
  rw [PBM.orbJ_one_eq Bs hγ' hpos' hnz (hZ'.trans hmono) F, PBM.orbJ_one_eq Bs hγ hpos hnz (hZ.trans hmono) F] at hlaw
  rw [← hlaw, CutBP.hsVec_norm_CinL Bs hhA hhB]

theorem normSq_sec (hk : 2 ≤ k) (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hsec : IsSection k r Bs.z Bs.z' μsec) :
    B.normSq Bs F = jNormSq k r (Tz k r Bs.z) (Tz k r Bs.z')
      fun q => Real.sqrt (hsNormSq (B.JF Bs F (bigCell k r q.1 (μsec q.2)))) := by
  unfold B.normSq jNormSq
  refine lintegral_congr fun q => ?_
  by_cases hw0 : bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q = 0
  · rw [hw0, zero_mul, zero_mul]
  obtain ⟨hc, hζ⟩ := Formalism.MainNotions.S.Pv.LemmaJ.bcWeight_ne hk hw0
  have hζ0 : q.2 ≠ 0 := by
    intro h
    rw [h, map_zero] at hζ
    exact absurd (mul_pos Bs.T_pos Bs.T'_pos) (not_lt.2 hζ.le)
  obtain ⟨d, hd1, hd2⟩ : ∃ d : Fin (r + 1) → ℂ, (fun i : Fin r => d i.castSucc) = q.1 ∧ d (Fin.last r) = q.2 :=
    ⟨Fin.snoc q.1 q.2, by funext i; simp, by simp⟩
  have hd : ∀ a, d a ≠ 0 := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [hd2]; exact hζ0
    · rw [congrFun hd1 i]; exact hc i
  have hZ := PBM.zhat_bigCell_pt Bs d (by rw [hd2]; exact hζ)
  have hZ' := PBM.zhat_bigCell_pt { Bs with μsec := μsec, sec := hsec } d (by rw [hd2]; exact hζ)
  rw [hd1, hd2] at hZ hZ'
  have e := norm_JF_eq Bs F d hd (bigCellMem k r _ _ hc (Bs.sec.2 _ hζ).1) (bigCellMem k r _ _ hc (hsec.2 _ hζ).1) hZ hZ'
    (Formalism.MainNotions.S.Pv.LemmaJ.Gf_big Bs.z_mem Bs.z'_mem Bs.sec q.1 hc q.2 hζ)
  congr 2
  rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_nonneg _), Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_eq]
  change ‖B.hsVec (B.JF Bs F (bigCell k r q.1 (Bs.μsec q.2)))‖ ^ 2 = _
  rw [e, PiLp.norm_sq_eq_of_L2]
  rfl

end energy

theorem energy_identity : EnergyTie := by
  intro k r L f μsec u u' p _ hc _ _ htie _ _ hsec
  obtain ⟨hz, hz', hπ, hπ', hW, hN, hW'⟩ := htie
  have e : TBB.jN2 p f = jNorm2 L f μsec := by
    refine (GlobalTheory.T.jN2_eq_normSq_base (parOfL L u u') L.Wp L.Wq p f).trans ?_
    have h := normSq_sec (k := k) (r := r) p.hl.2.2 p.T.base f μsec (by
      have e1 : (p.T.base.z : Fin (2 * r + k + 1) → ℂ) = L.z := hz
      have e2 : (p.T.base.z' : Fin (2 * r + k + 1) → ℂ) = L.z' := hz'
      exact e1 ▸ e2 ▸ hsec)
    refine h.trans ?_
    unfold jNorm2 LocBessel.J B.JF
    rw [hc]
    simp only [hz, hz', hπ, hπ', hW, hN, hW']
  rw [e]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal]
  exact one_le_pow₀ (by linarith [Real.pi_gt_three])

section scale

variable {k r : ℕ}

@[reducible] def withN (L : LocBessel k r) (κ : ℝ≥0∞) : LocBessel k r := { L with κN := κ }

theorem pairMeas_smul (L : LocBessel k r) (κ s : ℝ≥0∞) (h : L.μN = s • (withN L κ).μN) :
    pairMeas L = (s * s) • pairMeas (withN L κ) := by
  have i1 : SFinite (withN L κ).μN := Formalism.MainNotions.FrameBoundFromBesselTorus.sFinite_haarLie _ _
  have i2 : SigmaFinite L.μW := L.hμW.1.1
  have i3 : SigmaFinite L.μW' := L.hμW'.1.1
  unfold pairMeas
  rw [h]
  change (L.μW.prod (s • (withN L κ).μN)).prod (L.μW'.prod (s • (withN L κ).μN)) =
    (s * s) • (L.μW.prod (withN L κ).μN).prod (L.μW'.prod (withN L κ).μN)
  rw [Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left, smul_smul]

theorem orbSq_le (L : LocBessel k r) (κ s : ℝ≥0∞) (hs0 : s ≠ 0) (hs : s ≠ ⊤)
    (h : pairMeas L = s • pairMeas (withN L κ)) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) :
    orbSq L f γ ≤ ENNReal.ofReal (s.toReal ^ 2) * orbSq (withN L κ) f γ := by
  unfold orbSq
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hc => ?_
  have hq : IsOrbQuot (withN L κ) g μR (s⁻¹ • ν) := by
    intro φ hφ
    have e := hc.2.2.2 φ hφ
    rw [h, lintegral_smul_measure] at e
    rw [lintegral_smul_measure, ← e, smul_eq_mul, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hs0 hs, one_mul]
  have e : OrbInt L f g ν = ((s.toReal : ℝ) : ℂ) • OrbInt (withN L κ) f g (s⁻¹ • ν) := by
    have e1 : ν = s • (s⁻¹ • ν) := by rw [smul_smul, ENNReal.mul_inv_cancel hs0 hs, one_smul]
    unfold OrbInt
    conv_lhs => rw [e1, integral_smul_measure]
    rw [Complex.coe_smul]
    rfl
  rw [e, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' le_rfl ?_
  exact le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le (s⁻¹ • ν) (le_iSup_of_le ⟨hc.1, hc.2.1, hc.2.2.1, hq⟩ le_rfl)))

theorem jNorm2_eq (L : LocBessel k r) (κ s : ℝ≥0∞) (h : pairMeas L = s • pairMeas (withN L κ))
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    jNorm2 L f μsec = ENNReal.ofReal (s.toReal ^ 2) * jNorm2 (withN L κ) f μsec := by
  have hJ : ∀ g, L.J f g = ((s.toReal : ℝ) : ℂ) • (withN L κ).J f g := fun g => by
    change ∫ x, besselIntg L f g x ∂(pairMeas L) = _ • ∫ x, besselIntg L f g x ∂(pairMeas (withN L κ))
    rw [h, integral_smul_measure, Complex.coe_smul]
  rw [Formalism.MainNotions.BesselShellMomentBounds.jNorm2_eq, Formalism.MainNotions.BesselShellMomentBounds.jNorm2_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold Formalism.MainNotions.BesselShellMomentBounds.dens
  rw [hJ, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change _ = _ * (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * _)
  ring

end scale

end CompanionTheory.WaveGrid.Ties
end
end

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.SpanBall
section
noncomputable section

namespace CompanionTheory.WaveGrid.SpanBall

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P PI.UpqRep Matrix CompanionTheory.LimBd.Main CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace

def steps (n : ℕ) : Finset (Fin n → ℤ) :=
  insert 0 (Finset.univ.image (fun s : Fin n => (Pi.single s 1 : Fin n → ℤ)) ∪
    Finset.univ.image fun s : Fin n => -(Pi.single s 1 : Fin n → ℤ))

def ball (n : ℕ) : ℕ → Finset (Fin n → ℤ)
  | 0 => {0}
  | e + 1 => Finset.image₂ (· + ·) (ball n e) (steps n)

theorem zero_mem_steps (n : ℕ) : (0 : Fin n → ℤ) ∈ steps n := Finset.mem_insert_self _ _

theorem single_mem_steps {n : ℕ} (s : Fin n) : (Pi.single s 1 : Fin n → ℤ) ∈ steps n :=
  Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)))

theorem neg_single_mem_steps {n : ℕ} (s : Fin n) : -(Pi.single s 1 : Fin n → ℤ) ∈ steps n :=
  Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)))

theorem card_steps (n : ℕ) : (steps n).card ≤ 2 * n + 1 := by
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) 1)
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun s : Fin n => (Pi.single s 1 : Fin n → ℤ))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
    (f := fun s : Fin n => -(Pi.single s 1 : Fin n → ℤ))
  rw [Finset.card_univ, Fintype.card_fin] at h1 h2
  omega

theorem card_ball (n : ℕ) : ∀ e, (ball n e).card ≤ (2 * n + 1) ^ e
  | 0 => by simp [ball]
  | e + 1 => by
    rw [pow_succ]
    exact Finset.card_image₂_le _ _ _ |>.trans (Nat.mul_le_mul (card_ball n e) (card_steps n))

theorem sum_natAbs_le_one_of_mem_unitShifts {n : ℕ} {s : Fin n → ℤ} (h : s ∈ steps n) : ∑ i, (s i).natAbs ≤ 1 := by
  have key : ∀ t : Fin n, ∑ i, ((Pi.single t 1 : Fin n → ℤ) i).natAbs = 1 := fun t => by
    rw [Finset.sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
    simp
  simp only [steps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · simp
  · exact (key t).le
  · simpa only [Pi.neg_apply, Int.natAbs_neg] using (key t).le

theorem sum_natAbs_le_of_mem_ball {n : ℕ} : ∀ e, ∀ ν ∈ ball n e, ∑ i, (ν i).natAbs ≤ e
  | 0, ν, h => by
    rw [ball, Finset.mem_singleton] at h
    simp [h]
  | e + 1, ν, h => by
    obtain ⟨x, hx, s, hs, rfl⟩ := Finset.mem_image₂.1 h
    have h1 := sum_natAbs_le_of_mem_ball e x hx
    have h2 := sum_natAbs_le_one_of_mem_unitShifts hs
    have h3 : ∑ i, ((x + s) i).natAbs ≤ ∑ i, (x i).natAbs + ∑ i, (s i).natAbs := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _
    omega

theorem abs_ball {n e : ℕ} {ν : Fin n → ℤ} (h : ν ∈ ball n e) (a : Fin n) : |(ν a : ℝ)| ≤ e := by
  have h1 : (ν a).natAbs ≤ e := le_trans
    (Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)) (sum_natAbs_le_of_mem_ball e ν h)
  have h2 : (((ν a).natAbs : ℕ) : ℝ) ≤ e := by exact_mod_cast h1
  rwa [Nat.cast_natAbs, Int.cast_abs] at h2

theorem add_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    μ + Pi.single s 1 = fun a => μ a + ((Pi.single s 1 : Fin n → ℤ) a : ℝ) := by
  funext a
  by_cases h : a = s
  · subst h; simp
  · simp [h]

theorem sub_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    μ - Pi.single s 1 = fun a => μ a + ((-(Pi.single s 1 : Fin n → ℤ)) a : ℝ) := by
  funext a
  by_cases h : a = s
  · subst h; simp [sub_eq_add_neg]
  · simp [h]

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

def spanOn (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (S : Finset (Fin (2 * r + k + 1) → ℤ)) : Submodule ℂ (B.Mat k r → ℂ) :=
  Submodule.span ℂ {φ | ∃ ν ∈ S, IsCoef k r ε (fun a => lam a + (ν a : ℝ)) φ}

theorem mem_spanStep_of_eq {μ : Fin (2 * r + k + 1) → ℝ} {φ ψ ψ' : B.Mat k r → ℂ} (hφ : IsCoef k r ε μ φ)
    (hψ' : ψ' ∈ spanOn k r ε μ (steps _)) (h : ∀ g ∈ B.GV k r, ψ g = ψ' g) : ψ ∈ spanOn k r ε μ (steps _) := by
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, hσ, -, hw, -⟩ := hφ
  have h1 : IsCoef k r ε μ (ψ - ψ') :=
    ⟨H, i1, i2, i3, σ, 0, w, hμ, hσ, kfin_zero σ, hw, fun g hg => by simp [h g hg]⟩
  have h0 : ψ - ψ' ∈ spanOn k r ε μ (steps _) := Submodule.subset_span ⟨0, zero_mem_steps _, by simpa using h1⟩
  simpa using Submodule.add_mem _ h0 hψ'

theorem letterStep {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) {μ : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} {q φ : B.Mat k r → ℂ} (hq : IsLetter k r q) (hφ : IsCoef k r ε μ φ) (hg : PI.ZuckTensor.GapAtLeast ε μ h)
    (hlt : t _ ε + 1 < h) : q * φ ∈ spanOn k r ε μ (steps _) := by
  rcases hq with rfl | ⟨x, y, hq⟩
  · rw [one_mul]
    exact Submodule.subset_span ⟨0, zero_mem_steps _, by simpa using hφ⟩
  have hφ' := hφ
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, ⟨P, hP, hτ⟩, hv, hw, hφG⟩ := hφ'
  rw [kfin_iff hP] at hv hw
  rcases hq with hq | hq
  · obtain ⟨X⟩ := hZ _ ε μ H _ hμ hτ h hg hlt
    obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (P *ᵥ x) (P *ᵥ y) hv hw
    refine mem_spanStep_of_eq hφ (ψ' := ∑ i, fun g => ⟪wI i, X.σs (sI i) (P * g * P⁻¹) (vI i)⟫_ℂ)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, single_mem_steps (sI i),
        add_single μ (sI i) ▸ isCoef_of_J hP (X.ds _ (hI i).1).1 (X.ds _ (hI i).1).2 (hI i).2.1 (hI i).2.2⟩) fun g hgG => ?_
    have := hsum _ (forth_mem hP.1 hgG)
    simp only [back_forth hP.1, dot_transport hP] at this
    rw [Pi.mul_apply, hq g hgG, hφG g hgG, mul_comm, this, Finset.sum_apply]
  · obtain ⟨X⟩ := hZd _ ε μ H _ hμ hτ h hg hlt
    obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (P *ᵥ x) (P *ᵥ y) hv hw
    refine mem_spanStep_of_eq hφ (ψ' := ∑ i, fun g => ⟪wI i, X.σs (sI i) (P * g * P⁻¹) (vI i)⟫_ℂ)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, neg_single_mem_steps (sI i),
        sub_single μ (sI i) ▸ isCoef_of_J hP (X.ds _ (hI i).1).1 (X.ds _ (hI i).1).2 (hI i).2.1 (hI i).2.2⟩) fun g hgG => ?_
    have := hsum _ (forth_mem hP.1 hgG)
    have hi : (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]
    simp only [back_forth hP.1, hi, dot_transport hP] at this
    rw [Pi.mul_apply, hq g hgG, hφG g hgG, mul_comm, this, Finset.sum_apply]

theorem spanBall {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) {lam : Fin (2 * r + k + 1) → ℝ}
    {h : ℝ} (d : ℕ) {q φ : B.Mat k r → ℂ} (hq : q ∈ Letters k r ^ d) (hφ : IsCoef k r ε lam φ)
    (hg : PI.ZuckTensor.GapAtLeast ε lam h) (hlt : t _ ε + 1 + 2 * (d : ℝ) < h) :
    q * φ ∈ spanOn k r ε lam (ball _ d) := by
  induction d generalizing q with
  | zero =>
    rw [pow_zero, Submodule.mem_one] at hq
    obtain ⟨c, rfl⟩ := hq
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, Finset.mem_singleton_self _, by simpa using hφ⟩)
  | succ d ih =>
    push_cast at hlt
    have step : Letters k r * spanOn k r ε lam (ball _ d) ≤ spanOn k r ε lam (ball _ (d + 1)) := by
      unfold Letters
      rw [spanOn, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨a, ha, b, ⟨ν, hν, hb⟩, rfl⟩
      have hgμ : PI.ZuckTensor.GapAtLeast ε (fun a => lam a + (ν a : ℝ)) (h - 2 * d) :=
        gap_of_box (lam := lam) (μ := fun a => lam a + (ν a : ℝ)) (c := d) (fun s => by simpa using abs_ball hν s) hg (by linarith)
      refine Submodule.span_mono ?_ (letterStep hZ hZd ha hb hgμ (by linarith))
      rintro ψ ⟨s, hs, hψ⟩
      refine ⟨ν + s, Finset.mem_image₂_of_mem hν hs, ?_⟩
      simpa only [Pi.add_apply, Int.cast_add, add_assoc] using hψ
    rw [pow_succ'] at hq
    refine Submodule.mul_induction_on hq (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [mul_assoc]
      exact step (Submodule.mul_mem_mul ha (ih hb (by linarith)))
    · rw [add_mul]
      exact Submodule.add_mem _ ha hb

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sumOn (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (S : Finset (Fin (2 * r + k + 1) → ℤ)) : Submodule ℂ (B.Mat k r → (Wq →L[ℂ] Wp)) where
  carrier := {G | ∃ F : (Fin (2 * r + k + 1) → ℤ) → B.Mat k r → (Wq →L[ℂ] Wp),
    (∀ ν, F ν ∈ Wsp k r Wp Wq ε fun a => lam a + (ν a : ℝ)) ∧ G = ∑ ν ∈ S, F ν}
  add_mem' := by
    rintro _ _ ⟨F, hF, rfl⟩ ⟨F', hF', rfl⟩
    exact ⟨F + F', fun ν => Submodule.add_mem _ (hF ν) (hF' ν), by simp [Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
  smul_mem' := by
    rintro c _ ⟨F, hF, rfl⟩
    exact ⟨c • F, fun ν => Submodule.smul_mem _ c (hF ν), by simp [Finset.smul_sum]⟩

theorem smul_mem_sumOn {lam : Fin (2 * r + k + 1) → ℝ} {S : Finset (Fin (2 * r + k + 1) → ℤ)} {φ : B.Mat k r → ℂ}
    (hφ : φ ∈ spanOn k r ε lam S) (T : Wq →L[ℂ] Wp) : (fun g => φ g • T) ∈ sumOn k r Wp Wq ε lam S := by
  classical
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ν, hν, h⟩ := h
    refine ⟨fun ν' => if ν' = ν then fun g => φ g • T else 0, fun ν' => ?_, by simp [hν]⟩
    dsimp only
    split_ifs with e
    · subst e
      exact Submodule.subset_span ⟨φ, T, h, rfl⟩
    · exact Submodule.zero_mem _
  | zero =>
    convert Submodule.zero_mem _ using 2 with g
    simp
  | add φ ψ _ _ h h' =>
    convert Submodule.add_mem _ h h' using 2 with g
    simp [add_smul]
  | smul c φ _ h =>
    convert Submodule.smul_mem _ c h using 2 with g
    simp [smul_smul]

theorem mul_mem_sumOn {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t)
    {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ} {d : ℕ} {q : B.Mat k r → ℂ} (hq : q ∈ Letters k r ^ d)
    (hg : PI.ZuckTensor.GapAtLeast ε lam h) (hlt : t _ ε + 1 + 2 * (d : ℝ) < h) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ Wsp k r Wp Wq ε lam) : (fun g => q g • F g) ∈ sumOn k r Wp Wq ε lam (ball _ d) := by
  induction hF using Submodule.span_induction with
  | mem F h' =>
    obtain ⟨φ, T, hφ, rfl⟩ := h'
    convert smul_mem_sumOn (spanBall hZ hZd d hq hφ hg hlt) T using 2 with g
    rw [smul_smul, Pi.mul_apply]
  | zero =>
    convert Submodule.zero_mem _ using 2 with g
    simp
  | add F F' _ _ h h' =>
    convert Submodule.add_mem _ h h' using 2 with g
    simp
  | smul c F _ h =>
    convert Submodule.smul_mem _ c h using 2 with g
    simp only [Pi.smul_apply]
    rw [smul_comm]

end CompanionTheory.WaveGrid.SpanBall
end
end

