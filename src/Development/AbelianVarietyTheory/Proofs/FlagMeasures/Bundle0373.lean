import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicFrameLevelConjFormLevelWithCharacters
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0352
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0369
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0220
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0208
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0258
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0219
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0211
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0370
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapPreimageVolumeLowerBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicFrameLevelConjFormLevelWithCharactersStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicFrameLevel_conj_formLevel_with_characters : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Fr : AdFrame cm.sig J (hat F S.Lb) (gp 0 * gp 1) k), ∃ κ : UPts cm.sig J (Ad F), κ.1 ∈ stabGL (hat F S.Lb) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.St.G.LvlZero.level_conj_frame | exact GlobalTheory.St.G.LvlZero.level_conj_frame | (intros; apply GlobalTheory.St.G.LvlZero.level_conj_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicIteratedIntegrability
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Per.FJConv

theorem iterated_integrableOn {G N : Type} [TopologicalSpace G] [FirstCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [TopologicalSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]
    {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N} (hμ : μ 𝓕 ≠ ⊤) (hν : ν 𝓝 ≠ ⊤) {P : G → N → ℂ}
    (hP : Continuous fun q : G × N => P q.1 q.2) {M : ℝ} (hM : ∀ g n, ‖P g n‖ ≤ M) :
    (∀ g, IntegrableOn (P g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P g n ∂ν) 𝓕 μ := by
  have h1 : ∀ g, Continuous (P g) := fun g => hP.comp (Continuous.prodMk_right g)
  have h2 : ∀ n, Continuous fun g => P g n := fun n => hP.comp (Continuous.prodMk_left n)
  have : IsFiniteMeasure (ν.restrict 𝓝) := isFiniteMeasure_restrict.2 hν
  refine ⟨fun g => Measure.integrableOn_of_bounded (M := M) hν (h1 g).measurable.aestronglyMeasurable
    (.of_forall (hM g)), ?_⟩
  have hc : Continuous fun g => ∫ n in 𝓝, P g n ∂ν :=
    continuous_of_dominated (bound := fun _ => M) (fun g => (h1 g).measurable.aestronglyMeasurable)
      (fun g => .of_forall (hM g)) (integrable_const M) (.of_forall h2)
  exact Measure.integrableOn_of_bounded (M := M * ν.real 𝓝) hμ hc.measurable.aestronglyMeasurable
    (.of_forall fun g => norm_setIntegral_le_of_norm_le_const hν.lt_top fun n _ => hM g n)

theorem continuous_theta {D : D7} {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) {L A B : HSp D}
    {ι : A.V →ₗ[D.host.E] B.V} (d : FJDat L A B ι) (hr : 1 < A.rank) (hψ : Continuous Wl.ψ) (Φ : X.Sch L A) :
    Continuous fun q : GA D A × GA D B => d.theta Wl.ψ (omZ Wl L A Φ) q.2 q.1 := by
  have i0 : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have i1 : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  obtain ⟨-, ha, htc, -⟩ := GlobalTheory.T.theta_unipotent_conjugation D L A B ι d
  have hL := d.line.rank_one
  have hθ := GlobalTheory.T.weil_representation_continuous D X T Wl L A X.etaT⁻¹ (X.etaT ^ A.rank) (by omega) (resEta_line T hL) (resEta_pow T _) Φ
  have hcen : Continuous (cenCo L d.c) := continuous_const.mul (ht.comp (continuous_const.mul continuous_id))
  have htp : Continuous (tPt L A d.c) :=
    continuous_pi fun _ => continuous_pi fun k => (continuous_const.mul (continuous_apply k)).neg
  simp only [FJDat.theta_eq]
  exact (hψ.comp (hcen.comp (htc.comp continuous_snd))).mul
    (hθ.comp ((continuous_const.prodMk continuous_fst).prodMk (htp.comp (ha.comp continuous_snd))))

theorem conv_of_isAniso : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → IsAniso A → ∀ μ 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ → ∀ ν 𝓝, IsUnitN B d.eM ν 𝓝 → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) → ∀ (Φ : X.Sch L A) φ F, IsAutFun A φ → IsAutFun B F → d.Conv Wl.ψ (omZ Wl L A Φ) μ 𝓕 ν 𝓝 s φ F := by
  intro D X T Wl L A B ι d hr hA μ 𝓕 hμ h𝓕 ν 𝓝 hν s hs Φ φ F hφ hF
  have hψ : IsCharAF D.host.F Wl.ψ := Wl.ψ_std.1
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ d.isIsoSub).1
  obtain ⟨s₀, hcont, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ A) hK hcov μ h𝓕
  obtain ⟨hchr, -, -, hconj⟩ := GlobalTheory.T.theta_unipotent_conjugation D L A B ι d
  have haut := GlobalTheory.T.theta_kernel_invariance D X T Wl L A B ι d hr Φ
  have hv : Continuous fun q : GA D A × d.N => (q.2 : GA D B) := continuous_subtype_val.comp continuous_snd
  have hP : Continuous fun q : GA D A × d.N => d.perFun Wl.ψ (omZ Wl L A Φ) s₀ φ F q.1 q.2 :=
    (((hφ.cont.comp continuous_fst).star.mul (hF.cont.comp (hv.mul (hcont.comp continuous_fst)))).mul
      ((continuous_theta Wl d hr hψ.1 Φ).comp (continuous_fst.prodMk hv))).mul ((hchr _ hψ).2.comp hv).star
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hP.continuousOn
  refine iterated_integrableOn hfin.ne (by rw [hν.2.2]; exact ENNReal.one_ne_top) hP (M := M) fun g n => ?_
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  have hn : s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ ∈ d.N := (hconj _ _ ((hrel _ _).2 rfl) n n.2).1
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hn⟩
  have e' : s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s₀ γ * (γ' * k') * (s₀ γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  have e2 : (n : GA D B) * s₀ (γ * k) = s₀ γ * (γ' * (k' * s₀ k)) := by
    rw [e1]; simp only [map_mul, mul_assoc, inv_mul_cancel_left]
  have e3 : d.theta Wl.ψ (omZ Wl L A Φ) n (γ * k) = d.theta Wl.ψ (omZ Wl L A Φ) k' k := by
    rw [e1, (haut k _ (mul_mem γ'.2 k'.2)).2 γ hγ _ ((hrel _ _).2 rfl), (haut k _ k'.2).1 _ γ'.2 hγ']
  have hc : ∀ x, ‖d.chr Wl.ψ x‖ = 1 := fun x => hψ.2.1 _
  refine le_trans (le_of_eq ?_) (hM (k, k') ⟨hk, hk'⟩)
  simp only [FJDat.perFun, norm_mul, norm_star, hc]
  rw [e2, e3, hφ.left γ hγ, hF.left _ (hQ γ hγ), hF.left (γ' : GA D B) hγ']

end GlobalTheory.Per.FJConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselEnergyNormalisedFrameChange
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem lintegral_comp_scale {r : ℕ} (s : Fin r → ℝ) (hs : ∀ a, 0 < s a)
    (G : (Fin r → ℂ) × ℂ → ENNReal) :
    ∫⁻ p : (Fin r → ℂ) × ℂ, G (fun a => (s a : ℂ) * p.1 a, p.2) =
      ENNReal.ofReal (∏ a, (s a ^ 2)⁻¹) * ∫⁻ p, G p := by
  let f : (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℂ) :=
    LinearMap.pi fun i => ((s i • LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i)
  let T : ((Fin r → ℂ) × ℂ) →ₗ[ℝ] ((Fin r → ℂ) × ℂ) := f.prodMap LinearMap.id
  have hdet : LinearMap.det T = ∏ a, s a ^ 2 := by
    simp only [T, f, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_smul, LinearMap.det_id,
      Complex.finrank_real_complex, mul_one]
  have hpos : 0 < ∏ a, s a ^ 2 := Finset.prod_pos fun a _ => pow_pos (hs a) 2
  have hne : LinearMap.det T ≠ 0 := hdet ▸ hpos.ne'
  haveI : (volume : Measure ((Fin r → ℂ) × ℂ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ((Fin r → ℂ) × ℂ)) hne
  let e : ((Fin r → ℂ) × ℂ) ≃ᵐ ((Fin r → ℂ) × ℂ) :=
    (T.equivOfDetNeZero hne).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : _ → _) = T := rfl
  have h := lintegral_map_equiv (μ := (volume : Measure ((Fin r → ℂ) × ℂ))) G e
  rw [he, hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.2 hpos), smul_eq_mul] at h
  rw [Finset.prod_inv_distrib, h]
  refine lintegral_congr fun p => ?_
  congr 1

theorem bcWeight_scale (k r : ℕ) (T T' : ℝ) (s : Fin r → ℝ) (hs : ∀ a, 0 < s a) (p : (Fin r → ℂ) × ℂ) :
    bcWeight k r T T' p = (∏ a, (s a ^ (2 * (Mdim k r a - 2)))⁻¹) *
      bcWeight k r T T' (fun a => (s a : ℂ) * p.1 a, p.2) := by
  unfold bcWeight
  split_ifs with h
  · rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    have := (hs a).ne'
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs a), mul_pow]
    field_simp
  · simp

theorem gamLev_inv_eq (k r : ℕ) (t : ℝ) (ht : 0 < t) :
    (D.GamLev k r t⁻¹ 1 0)⁻¹ = (∏ a : Fin r, ((t ^ (2 * (r - a.val))) ^ (2 * (Mdim k r a - 2)))⁻¹) *
      ∏ a : Fin r, ((t ^ (2 * (r - a.val))) ^ 2)⁻¹ := by
  unfold D.GamLev
  rw [Finset.prod_Ioc_succ_top (Nat.zero_le r), ← Finset.prod_mul_distrib]
  have h1 : Finset.Ioc 0 r = Finset.Ico 1 (r + 1) := by ext; simp; omega
  rw [h1, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, Finset.prod_range]
  have h0 : ((r : ℤ) + 1 - ((r + 1 : ℕ) : ℤ)) = 0 := by push_cast; ring
  rw [h0]
  simp only [mul_zero, zero_mul, neg_zero, zpow_zero, div_one, mul_one]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  obtain ⟨d, hd⟩ : ∃ d, r = a.val + (d + 1) := ⟨r - a.val - 1, by have := a.isLt; omega⟩
  have h2 : r - a.val = d + 1 := by omega
  have h3 : Mdim k r a - 2 = 2 * d + k + 1 := by unfold Mdim; omega
  have h4 : 4 * ((r : ℤ) + 1 - ((1 + a.val : ℕ) : ℤ)) * (C.Mlev k r (1 + a.val) - 1) =
      ((2 * (d + 1) * (2 * (2 * d + k + 1)) + 2 * (d + 1) * 2 : ℕ) : ℤ) := by
    unfold C.Mlev
    have : (r : ℤ) = a.val + (d + 1) := by exact_mod_cast hd
    push_cast
    rw [this]; ring
  rw [h4, h2, h3, _root_.inv_zpow', neg_neg, zpow_natCast, ← pow_mul, ← pow_mul, pow_add, mul_inv]

theorem energy_change_of_frame : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∫⁻ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p * Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) = ENNReal.ofReal (lamN L cN ^ 4 / D.GamLev k r ‖cStd / L.c‖⁻¹ 1 0) * B.normSq Bs (conjF (cStd / L.c) F) := by
  intro k r L μsec Bs cN F _ hstd hrat hc h0 htop
  have hJ := GlobalTheory.T.besselFunction_eq_scalar_sq_normalisedBessel_torusConjugate k r L μsec Bs cN F hstd hrat hc h0 htop
  have hα : cStd / L.c ≠ 0 := div_ne_zero (by simp [cStd]) hc
  set α := cStd / L.c with hαdef
  have hB := (GlobalTheory.T.besselTorusElement_properties k r α hα).2.2.2
  have ht : 0 < ‖α‖ := norm_pos_iff.2 hα
  obtain ⟨hz, hz', -, -, -, -, -, hμ⟩ := hstd
  let s : Fin r → ℝ := fun a => ‖α‖ ^ (2 * (r - a.val))
  have hs : ∀ a, 0 < s a := fun a => pow_pos ht _
  let G : (Fin r → ℂ) × ℂ → ENNReal := fun p =>
    ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
      ‖B.hsVec (B.JF Bs (conjF α F) (B.gq Bs p))‖ ^ 2)
  have hG : B.normSq Bs (conjF α F) = ∫⁻ p, G p := by
    simp only [B.normSq, jNormSq, hz, hz', G]
  let A : ℝ := lamN L cN ^ 4 * ∏ a, (s a ^ (2 * (Mdim k r a - 2)))⁻¹
  have hA : 0 ≤ A := mul_nonneg (by positivity)
    (Finset.prod_nonneg fun a _ => inv_nonneg.2 (pow_pos (hs a) _).le)
  have hhs : ∀ X : L.Wq →L[ℂ] L.Wp, Formalism.MainNotions.S.hsNormSq X = ‖B.hsVec X‖ ^ 2 := by
    intro X
    rw [PiLp.norm_sq_eq_of_L2]
    unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hpt : ∀ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
      Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) =
      ENNReal.ofReal A * G (fun a => (s a : ℂ) * p.1 a, p.2) := by
    intro p
    simp only [G]
    rw [← ENNReal.ofReal_mul hA, hJ, hB, hhs, bcWeight_scale k r _ _ s hs p]
    congr 1
    have hsm : ∀ (c : ℂ) (X : L.Wq →L[ℂ] L.Wp), B.hsVec (c • X) = c • B.hsVec X := fun _ _ => rfl
    rw [hsm, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [B.gq, hμ, A, s]
    ring
  rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_scale s hs G,
    hG, ← mul_assoc, ← ENNReal.ofReal_mul hA, div_eq_mul_inv, gamLev_inv_eq k r _ ht]
  simp only [A, s, mul_assoc]

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BoundedEquivariantMapSmoothContinuousSeminormBou
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem sq_nnnorm_sub_le {W : Type} [NormedAddCommGroup W] (a b c : W) :
    (‖a - b‖₊ : ENNReal) ^ 2 ≤ 2 * (‖a - c‖₊ : ENNReal) ^ 2 + 2 * (‖b - c‖₊ : ENNReal) ^ 2 := by
  have h : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := by
    simpa [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub a c b
  have h2 : (‖a - b‖₊ : NNReal) ^ 2 ≤ 2 * (‖a - c‖₊ : NNReal) ^ 2 + 2 * (‖b - c‖₊ : NNReal) ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [sq_nonneg (‖a - c‖ - ‖b - c‖), norm_nonneg (a - b), norm_nonneg (a - c),
      norm_nonneg (b - c)]
  exact_mod_cast h2

theorem list_sq_le {ι : Type} (c : ℝ) (hc : 0 ≤ c) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (l : List ι) :
    (l.map fun w => 2 * ENNReal.ofReal (c * a w ^ 2)).sum ≤
      ENNReal.ofReal (2 * c * (l.map a).sum ^ 2) := by
  induction l with
  | nil => simp
  | cons w l ih =>
    have hS : 0 ≤ (l.map a).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact ha i)
    simp only [List.map_cons, List.sum_cons]
    have e : 2 * ENNReal.ofReal (c * a w ^ 2) = ENNReal.ofReal (2 * (c * a w ^ 2)) := by
      rw [ENNReal.ofReal_mul (p := 2) (q := c * a w ^ 2) (by norm_num)]; simp
    rw [e]
    refine (add_le_add le_rfl ih).trans ?_
    rw [← ENNReal.ofReal_add (by have := ha w; positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := ha w
    nlinarith [mul_nonneg hc (mul_nonneg this hS)]

theorem list_sum_le_two {ι : Type} (l : List ι) (A a b : ι → ENNReal)
    (h : ∀ i ∈ l, A i ≤ 2 * a i + 2 * b i) :
    (l.map A).sum ≤ 2 * (l.map a).sum + 2 * (l.map b).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have h1 := h w List.mem_cons_self
    have h2 := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
    calc A w + (l.map A).sum ≤ (2 * a w + 2 * b w) + (2 * (l.map a).sum + 2 * (l.map b).sum) :=
          add_le_add h1 h2
      _ = 2 * a w + 2 * (l.map a).sum + (2 * b w + 2 * (l.map b).sum) := by
          rw [add_add_add_comm]

theorem reg_main : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (T : H → Mat k r → Wp), IsURepOn (GG k r) σ → IsHaarOn (GG k r) μG → (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) → (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) → (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) → (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) → ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧ ∀ u : H, IsSmoothVec σ u → ∃ f : Mat k r → Wp, ContinuousOn f (GG k r) ∧ (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => T u (Matrix.of x)) ∧ ‖f 1‖ ≤ C * (Ws.map fun ws => ‖dsigW σ ws u‖).sum := by
  intro k r H _ _ _ Wp _ _ _ σ μ T hσ hμ hadd hsm hbd heq
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hGae : ∀ᵐ y ∂μ, (Matrix.of y : Mat k r) ∈ GG k r := by
    rw [ae_iff]; exact hμ.2.2.1
  have hGm : MeasurableSet {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} :=
    IsClosed.measurableSet (α := Mt k r) (gg_closedSub k r).2.1
  have hrest : μ.restrict {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} = μ :=
    Measure.restrict_eq_self_of_ae_mem hGae
  have hcm : ∀ (Λ' : H →L[ℂ] Wp) (v : H),
      AEStronglyMeasurable (fun y : Mt k r => Λ' (σ (Matrix.of y) v)) μ := by
    intro Λ' v
    have hc : ContinuousOn (fun y : Mt k r => Λ' (σ (Matrix.of y) v))
        {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} :=
      Λ'.continuous.comp_continuousOn (hσ.2.2 v)
    have := hc.aestronglyMeasurable (μ := μ) hGm
    rwa [hrest] at this
  obtain ⟨C₀, Ws, K₀, hK₀, hWs, hsob⟩ := GlobalTheory.T.sobolev_inequality_at_identity_besselModelUnitaryGroup k r μ hμ
  have hsu := GlobalTheory.T.sobolev_ineq_translate_compact k r μ C₀ Ws K₀ hμ hK₀ hsob
  have hclm : ∀ Q : Set (Mt k r), IsCompact Q → ∃ K₂ : Set (Mt k r), IsCompact K₂ ∧
      ∀ (Λ' : H →L[ℂ] Wp) (u : H), IsSmoothVec (k := k) (r := r) σ u → ∀ x ∈ Q,
      (Matrix.of x : Mat k r) ∈ GG k r →
      ENNReal.ofReal (‖Λ' (σ (Matrix.of x) u)‖ ^ 2) ≤ ENNReal.ofReal |C₀| *
        (Ws.map fun ws => ∫⁻ y in K₂, (‖Λ' (σ (Matrix.of y) (dsigW σ ws u))‖₊ : ENNReal) ^ 2 ∂μ).sum := by
    intro Q hQ
    obtain ⟨K₂, hK₂, h⟩ := hsu Q hQ
    refine ⟨K₂, hK₂, fun Λ' u hu x hx hxG => ?_⟩
    obtain ⟨hs, hd⟩ := GlobalTheory.T.smooth_functional_orbit_smoothVector k r σ Λ' hσ u hu
    have hcont : ∀ ws ∈ Ws, ContinuousOn (rdWord ws fun g : Mat k r => Λ' (σ g u)) (GG k r) := by
      intro ws hws
      have h1 : ContinuousOn (fun g : Mat k r => Λ' (σ g (dsigW σ ws u))) (GG k r) :=
        Λ'.continuous.comp_continuousOn (hσ.2.2 _)
      exact h1.congr (fun x hx => hd ws (hWs ws hws) x hx)
    refine (h Wp _ hs hcont x hx hxG).trans (le_of_eq ?_)
    congr 2
    refine List.map_congr_left fun ws hws => ?_
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGae] with y hy
    rw [hd ws (hWs ws hws) _ hy]
  obtain ⟨K₁, hK₁, hone⟩ := hclm {oneM k r} isCompact_singleton
  obtain ⟨c₁, hc₁⟩ := hbd K₁ hK₁
  choose Λ hΛ using GlobalTheory.T.ballMean_continuousLinearFunctional k r σ μ T hμ hadd hsm hbd heq
  refine ⟨Real.sqrt (|C₀| * (2 * |c₁|)), Ws, hWs, fun u hu => ?_⟩
  have hloc : ∀ (v : H) (K : Set (Mt k r)), IsCompact K →
      AEStronglyMeasurable (fun z : Mt k r => T v (Matrix.of z)) (μ.restrict K) ∧
      ∫⁻ x in K, (‖T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ < ⊤ := by
    intro v K hK
    obtain ⟨C, hC⟩ := hbd K hK
    exact ⟨(hC v).1, (hC v).2.trans_lt ENNReal.ofReal_lt_top⟩
  have hconv : ∀ (v : H) (K : Set (Mt k r)), IsCompact K → Filter.Tendsto (fun j : ℕ =>
      ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ)
      Filter.atTop (nhds 0) :=
    fun v K hK => GlobalTheory.T.tendsto_average_L2_compact k r μ hμ _ (hloc v) K hK

  have hAm : ∀ (j : ℕ) (v : H) (K : Set (Mt k r)), IsCompact K → AEMeasurable (fun y : Mt k r =>
      (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) y - T v (Matrix.of y)‖₊ : ENNReal) ^ 2) (μ.restrict K) := by
    intro j v K hK
    have h1 : AEStronglyMeasurable (fun y : Mt k r => avgR μ j (fun z : Mt k r => T v (Matrix.of z)) y) μ := by
      refine (hcm (Λ j) v).congr ?_
      filter_upwards [hGae] with x hx
      exact hΛ j v x hx
    exact ((h1.restrict.sub (hloc v K hK).1).nnnorm.aemeasurable.coe_nnreal_ennreal).pow_const 2

  have hsp : ∀ (j l : ℕ) (v : H) (K : Set (Mt k r)), IsCompact K →
      ∫⁻ y in K, (‖(Λ j - Λ l) (σ (Matrix.of y) v)‖₊ : ENNReal) ^ 2 ∂μ ≤
      2 * ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ +
      2 * ∫⁻ x in K, (‖avgR μ l (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ := by
    intro j l v K hK
    rw [← lintegral_const_mul' 2 _ (by simp), ← lintegral_const_mul' 2 _ (by simp),
      ← lintegral_add_left' ((hAm j v K hK).const_mul 2)]
    refine lintegral_mono_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGae] with y hy
    rw [ContinuousLinearMap.sub_apply, hΛ j v y hy, hΛ l v y hy]
    exact sq_nnnorm_sub_le _ _ _
  have hsp1 : ∀ (j : ℕ) (v : H) (K : Set (Mt k r)), IsCompact K →
      ∫⁻ y in K, (‖Λ j (σ (Matrix.of y) v)‖₊ : ENNReal) ^ 2 ∂μ ≤
      2 * ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ +
      2 * ∫⁻ x in K, (‖T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ := by
    intro j v K hK
    rw [← lintegral_const_mul' 2 _ (by simp), ← lintegral_const_mul' 2 _ (by simp),
      ← lintegral_add_left' ((hAm j v K hK).const_mul 2)]
    refine lintegral_mono_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGae] with y hy
    rw [hΛ j v y hy]
    simpa using sq_nnnorm_sub_le (avgR μ j (fun z : Mt k r => T v (Matrix.of z)) y) 0 (T v (Matrix.of y))
  have hEt : ∀ K : Set (Mt k r), IsCompact K → Filter.Tendsto (fun j : ℕ =>
      (Ws.map fun ws => ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
        T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ).sum) Filter.atTop (nhds 0) := by
    intro K hK
    have h := tendsto_list_sum (f := fun (ws : List (Mat k r)) (j : ℕ) =>
      ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
        T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ) (a := fun _ => 0) Ws
      (fun ws _ => hconv _ K hK)
    have e0 : (Ws.map fun _ => (0 : ENNReal)).sum = 0 := by simp
    rwa [e0] at h
  have hCau : ∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q,
      (Matrix.of x : Mat k r) ∈ GG k r →
      ‖Λ j (σ (Matrix.of x) u) - Λ l (σ (Matrix.of x) u)‖ ≤ ε := by
    intro Q hQ ε hε
    obtain ⟨K₂, hK₂, h⟩ := hclm Q hQ
    have hG : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal |C₀| * (2 *
        (Ws.map fun ws => ∫⁻ x in K₂, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
          T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ).sum)) Filter.atTop (nhds 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |C₀|)
        (ENNReal.Tendsto.const_mul (a := 2) (hEt K₂ hK₂) (Or.inr (by simp)))
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h1
    have hη : (0 : ENNReal) < ENNReal.ofReal (ε ^ 2 / 2) := ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hG.eventually_lt_const hη)
    refine ⟨N, fun j hj l hl x hx hxG => ?_⟩
    have hb := h (Λ j - Λ l) u hu x hx hxG
    have hs := list_sum_le_two Ws _ _ _ (fun ws _ => hsp j l (dsigW σ ws u) K₂ hK₂)
    have h3 : ENNReal.ofReal (‖(Λ j - Λ l) (σ (Matrix.of x) u)‖ ^ 2) ≤
        ENNReal.ofReal (ε ^ 2 / 2) + ENNReal.ofReal (ε ^ 2 / 2) := by
      refine hb.trans ((mul_le_mul' le_rfl hs).trans ?_)
      rw [mul_add]
      exact add_le_add (hN j hj).le (hN l hl).le
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    have h4 : ‖(Λ j - Λ l) (σ (Matrix.of x) u)‖ ^ 2 ≤ ε ^ 2 := by linarith
    have h5 := (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le (by norm_num)).1 h4
    simpa using h5
  obtain ⟨F, hFc, hFae, hFl⟩ := GlobalTheory.T.exists_continuous_limit_uniformCauchy k r μ hμ (fun j g => Λ j (σ g u))
    (fun z : Mt k r => T u (Matrix.of z)) (fun j => (Λ j).continuous.comp_continuousOn (hσ.2.2 u))
    (fun Q hQ => (hloc u Q hQ).1) hCau (fun Q hQ => by
      refine (hconv u Q hQ).congr fun j => ?_
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hGae] with x hx
      rw [hΛ j u x hx])
  refine ⟨F, hFc, hFae, ?_⟩
  have h1G : (1 : Mat k r) ∈ GG k r := (gg_closedSub k r).2.2.1
  have hlim := hFl 1 h1G
  have hb : ∀ j : ℕ, ENNReal.ofReal (‖Λ j (σ 1 u)‖ ^ 2) ≤ ENNReal.ofReal |C₀| * (2 *
      (Ws.map fun ws => ∫⁻ x in K₁, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
          T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ).sum +
      2 * (Ws.map fun ws => ENNReal.ofReal (|c₁| * ‖dsigW σ ws u‖ ^ 2)).sum) := by
    intro j
    have h0 := hone (Λ j) u hu (oneM k r) rfl h1G
    refine h0.trans (mul_le_mul' le_rfl (list_sum_le_two Ws _ _ _ fun ws _ => ?_))
    refine (hsp1 j (dsigW σ ws u) K₁ hK₁).trans ?_
    gcongr
    refine (hc₁ _).2.trans (ENNReal.ofReal_le_ofReal ?_)
    have := le_abs_self c₁
    have h2 := sq_nonneg ‖dsigW σ ws u‖
    nlinarith
  have hlimL : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal (‖Λ j (σ 1 u)‖ ^ 2)) Filter.atTop
      (nhds (ENNReal.ofReal (‖F 1‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hlim.norm.pow 2)
  have hlimR := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |C₀|)
    ((ENNReal.Tendsto.const_mul (a := 2) (hEt K₁ hK₁) (Or.inr (by simp))).add
      (tendsto_const_nhds (x := 2 * (Ws.map fun ws => ENNReal.ofReal (|c₁| * ‖dsigW σ ws u‖ ^ 2)).sum)))
    (Or.inr ENNReal.ofReal_ne_top)
  have hfin := le_of_tendsto_of_tendsto' hlimL hlimR hb
  rw [mul_zero, zero_add, ← List.sum_map_mul_left] at hfin
  have hS := list_sq_le |c₁| (abs_nonneg _) (fun ws : List (Mat k r) => ‖dsigW σ ws u‖)
    (fun _ => norm_nonneg _) Ws
  have hSn : 0 ≤ (Ws.map fun ws => ‖dsigW σ ws u‖).sum := List.sum_nonneg (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _)
  have h3 := hfin.trans (mul_le_mul' le_rfl hS)
  rw [← ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  have h4 := Real.abs_le_sqrt (h := h3)
  rw [abs_norm] at h4
  have e : |C₀| * (2 * |c₁| * (Ws.map fun ws => ‖dsigW σ ws u‖).sum ^ 2) =
      (|C₀| * (2 * |c₁|)) * (Ws.map fun ws => ‖dsigW σ ws u‖).sum ^ 2 := by ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hSn] at h4
  exact h4

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapParamOfIsHCTypeW
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem capParam_of_isHCTypeW : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (U : ℕ → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → (∀ i : Fin k, U (i.val + 1) = u i) → Q.CapParam k r z π U := by
  intro k r z u U Wp _ _ _ π hz hT hπ hU
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨u', hu'⟩ := GlobalTheory.CapelliOfHC.exists_isType k r Wp z π u hz hT hπ'
  intro Bs hB w v
  rw [hu'.2.2.2.2.2 Bs hB w v]
  congr 1
  have key : ∀ f : ℕ → ℝ, ∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (f i : ℂ)) =
      ∏ s : Fin k, (w - (k : ℂ) / 2 + 1 / 2 + (f (s.val + 1) : ℂ)) := by
    intro f
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
      ← Fin.prod_univ_eq_prod_range (fun i => w - (k : ℂ) / 2 + 1 / 2 + (f (1 + i) : ℂ))]
    exact Finset.prod_congr rfl fun s _ => by rw [add_comm 1 s.val]
  rw [key, key, ← GlobalTheory.SupNonzero.prod_eq hu' hπ']
  simp only [hU]

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIsometricOfRepresentativesStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnDictionary_isometric_of_representatives : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : Formalism.L2.SG.TermOp.ColSys X u what₂) (hinj : Function.Injective (Formalism.L2.SG.TermOp.sharp hK cs)), Formalism.L2.SG.TermOp.ColReps hK cs → ColDictIsom X Tr hK cs hinj := by
  first | exact @GlobalTheory.St.colDict_isometric_of_reps | exact GlobalTheory.St.colDict_isometric_of_reps | (intros; apply GlobalTheory.St.colDict_isometric_of_reps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepBoundedEvaluationRowsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousRep_bounded_evaluation_rows : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  first | exact @GlobalTheory.EvalBound.exists_contRep_bound | exact GlobalTheory.EvalBound.exists_contRep_bound | (intros; apply GlobalTheory.EvalBound.exists_contRep_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOntoStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u F wt J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, J ξ = p := by
  first | exact @GlobalTheory.St.coefficient_map_exists_onto | exact GlobalTheory.St.coefficient_map_exists_onto | (intros; apply GlobalTheory.St.coefficient_map_exists_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapPreimageVolumeLowerBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMap_preimage_volume_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E) (S0 : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x → gramR (Fv F v) σ J x = (S0 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → ∀ W : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsOpen W → x ∈ W → ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ nhds S0, ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ ((gramR (Fv F v) σ J) ⁻¹' (Subtype.val '' S) ∩ W) := by
  first | exact @GlobalTheory.GramPreimageLB.lb_gram_preimage | exact GlobalTheory.GramPreimageLB.lb_gram_preimage | (intros; apply GlobalTheory.GramPreimageLB.lb_gram_preimage <;> assumption)
end

