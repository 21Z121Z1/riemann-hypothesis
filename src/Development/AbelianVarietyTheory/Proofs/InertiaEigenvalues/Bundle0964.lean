import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import GroundTheory.GlobalFields.TateThesis.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0886
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0958
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0903
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0888
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0427
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0952
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedWhittakerIntegralEqEulerProductSchurSums
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSCell

theorem exists_isUnifV : ∀ (E : Type) [Field E] [NumberField E], ∃ ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ, ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E) := by
  intro E _ _
  refine ⟨fun w => GroundTheory.Global.uniformizerUnit w, fun w => ?_⟩
  have h := GroundTheory.Global.valued_uniformizerUnit_zpow w 1
  rw [zpow_one] at h
  exact h

set_option maxHeartbeats 4000000 in

theorem lintegral_unfolded_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (ℓ : ℕ) + 1 = a ∧
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E a)), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit φ.1) (GlobalTheory.JSW.whit φ.1) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
            ENNReal.ofReal (H x) * GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x := by
  intro E _ _ _ a π ha hπ T hT
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨α, π₀, ω, hα, hmk, hωu, hω, hπ₀, hsat⟩ := GlobalTheory.T.exists_cuspRep_bump_data_satake_unitary E (m + 1) π hπ T hT
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV E
  obtain ⟨F, hF, l₀, hl₀, ⟨U, hUo, hU⟩, hK, hW0, ⟨C, hC, hCp⟩, hprof⟩ := GlobalTheory.T.exists_shifted_vector_shintani_formula_ramified E m T π₀ hπ₀ α hsat ϖ hϖ
  have hSm : F ∈ Sm E (m + 1) := (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ₀ hF : GlobalTheory.MSpanDecay.Good F).mem_Sm
  let φ : Sm E (m + 1) := ⟨F, hSm⟩
  have hFc : Continuous F := by
    refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E (m + 1) φ
      (GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hUo.mem_nhds U.one_mem) fun k hk => ?_))
    exact Subtype.ext (funext fun g => hU k hk g)
  obtain ⟨hWc, hWN⟩ := GlobalTheory.T.globalWhittakerCoefficient_continuous_norm_invariant E (m + 1) F hFc (GlobalTheory.T.cuspFormRapidKernelSmoothSpan_left_invariant E (m + 1) π₀ F hF)
  obtain ⟨Φ, J, hΦs, hΦc, hΦr, hΦreal, hΦ1, hJ0, horb⟩ := GlobalTheory.T.exists_archimedeanBump_ideal_rowOrbit E (m + 1) (Fin.last m) T U hUo
  have hWU : ∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g := fun u hu g => by
    rw [GlobalTheory.JSW.whit_mul_right]
    exact congrArg (fun f => GlobalTheory.JSW.whit f g) (funext fun z => hU u hu z)
  have hWK : ∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g :=
    fun k hk h1 h2 g => by
      rw [GlobalTheory.JSW.whit_mul_right]
      exact congrArg (fun f => GlobalTheory.JSW.whit f g) (funext fun z => hK k hk h1 h2 z)
  let αc : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ := fun w i => ((α w i : ℂˣ) : ℂ)
  have hpw := GlobalTheory.T.cell_identity_rankinSelberg_torus_translate E m T ϖ hϖ αc F l₀ U Φ J hl₀ hWU hWK hWN hprof hΦr hJ0
    (fun y hy => (horb y hy).imp fun κ hκ => ⟨hκ.1, hκ.2.2⟩)
  obtain ⟨K, hKc, hKp⟩ := GlobalTheory.T.cell_decomposition_lattice_integral_unfolding E m T ϖ hϖ F l₀ U Φ J C hC hl₀ hWU hWK hWN hCp hΦc hΦr hJ0 horb
  obtain ⟨hBc, hBN, hBtop⟩ := GlobalTheory.T.unfoldedRankinSelbergIntegrand_continuous_invariant E (m + 1) (Fin.last m) (by simp) F Φ J (Pi.single (Fin.last m) 1) hWc hWN
    hΦs.continuous hΦr
  have hΦ1' : Φ (Pi.single (Fin.last m) 1) ≠ 0 := fun h => by rw [h] at hΦ1; simp at hΦ1
  have hone := GlobalTheory.T.unfoldedRankinSelbergIntegrand_ne_zero_identity E m T ϖ F Φ J l₀ hl₀ hW0 hΦ1'
  refine ⟨α, Fin.last m, Φ, J, Pi.single (Fin.last m) 1, π₀, ω, φ, by simp, hα, hmk, hωu, hω, Or.inr hF, ?_, hΦs,
    hΦc, hΦr, hΦreal, fun h => hΦ1' (congrFun h _), ?_⟩
  · intro h
    apply hW0
    have e : F = 0 := congrArg Subtype.val h
    rw [e]
    simp [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
  intro μ _ 𝓕₀ h𝓕

  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → GA E (m + 1) → ℝ, B = fun x g =>
      (GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g)).toReal :=
    ⟨_, rfl⟩
  have hB1 : Continuous (Function.uncurry B) := by
    have h1 : Continuous fun p : ℝ × GA E (m + 1) => (p.1, GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * p.2) :=
      continuous_fst.prodMk (continuous_const.mul continuous_snd)
    have h2' := hBc.comp h1
    have h2 : Continuous fun p : ℝ × GA E (m + 1) => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) p.1
        (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * p.2) := h2'
    have h3 := ENNReal.continuousOn_toReal.comp_continuous h2 fun p => hBtop _ _
    subst hBdef
    exact h3
  have hBg : ∀ (x : ℝ) (h : GA E (m + 1) → GA E (m + 1)), Continuous h →
      Continuous fun g => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (h g) := by
    intro x h hh
    have h2 := hBc.comp (continuous_const.prodMk hh : Continuous fun g => (x, h g))
    exact h2
  have hB2 : ∀ x g, 0 ≤ B x g := fun _ _ => by rw [hBdef]; exact ENNReal.toReal_nonneg
  have hB3 : ∀ x, 0 < B x 1 := fun x => by
    rw [hBdef]
    refine ENNReal.toReal_pos ?_ (hBtop _ _)
    rw [mul_one]
    exact hone x
  have hB4 : ∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B x (u * g) = B x g := fun x u hu g => by
    rw [hBdef]
    beta_reduce
    have e : GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * (u * g) =
        (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * u * (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1)⁻¹) * (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) := by
      group
    rw [e, hBN x _ (GlobalTheory.CellDec.tl_conj_mem ϖ l₀.1 hu)]
  have hB5 : ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ x g, g ∈ GlobalTheory.CellDec.C0 E (m + 1) T → B x g ≠ 0 →
      ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K :=
    ⟨K, hKc, fun x g hg h => hKp x g hg fun h0 => h (by rw [hBdef]; simp only; rw [h0]; rfl)⟩
  obtain ⟨hI, hIc⟩ := GlobalTheory.T.lintegral_unipotentCell_pos_lt_top_continuous E (m + 1) μ T 𝓕₀ h𝓕 B hB1 hB2 hB3 hB4 hB5
  have hd : 0 < GlobalTheory.CellDec.dinv (m + 1) l₀.1 := by
    unfold GlobalTheory.CellDec.dinv
    refine Finset.prod_pos fun w _ => zpow_pos ?_ _
    have := NumberField.HeightOneSpectrum.one_lt_absNorm w
    unfold Formalism.UG.qV
    exact_mod_cast (zero_lt_one.trans this)

  have key : ∀ x : ℝ, ∫⁻ g in 𝓕₀, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x g ∂μ =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) αc x *
        (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
          ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ) := by
    intro x
    have hmeas : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, Measurable fun g =>
        GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) := fun l =>
      (hBg x _ (continuous_const.mul continuous_id)).measurable
    have hnm : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T) μ :=
      h𝓕.nullMeasurableSet.inter (GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) T).measurableSet.nullMeasurableSet
    have hmx : Measurable fun g => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x g :=
      (hBg x (fun g => g) continuous_id).measurable
    rw [GlobalTheory.CellDec.cell_lintegral μ T ϖ hϖ 𝓕₀ h𝓕 _ hmx
      (hBN x), ← GlobalTheory.T.tsum_schurSquareCellProduct_eq_eulerProduct E (m + 1) T αc x l₀, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun l => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have e1 : ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
          GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
          ENNReal.ofReal (B x g) * GlobalTheory.RSCell.cellProd T αc x (l.1 - l₀.1) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem₀ hnm] with g hg
      rw [hpw x g hg.2 l, hBdef, ENNReal.ofReal_toReal (hBtop _ _)]
    have hm2 : Measurable fun g => ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * ENNReal.ofReal (B x g) := by
      rw [hBdef]
      exact measurable_const.mul (ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp (hmeas l₀)))
    rw [e1, lintegral_mul_const _ hm2, mul_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨fun x => (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
    ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal, ?_, ?_, fun x _ => ⟨?_, ?_⟩⟩
  · have e : (fun x => (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal) =
        fun x => GlobalTheory.CellDec.dinv (m + 1) l₀.1 * (∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal := by
      funext x
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le]
    rw [e]
    exact (continuous_const.mul hIc).continuousWithinAt
  · exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (hI 1).1.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI 1).2.ne)
  · exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (hI x).1.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI x).2.ne)
  · rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI x).2.ne), mul_comm]
    exact key x

end GlobalTheory.RSCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumReadingConstantsLevelCoverRelateCore
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries
open CategoryTheory

noncomputable section

namespace GlobalTheory.CoverConstMove

theorem kappa_eq {D : D7} {r : ℕ} (X X' : Data D.host.E r) (hψ : X.Ψ = X'.Ψ) (hξ : X.ξ0 = X'.ξ0) : X.κ0 = X'.κ0 := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h0 : D.host.φ₀ ∈ X.Ψ
    · exact ⟨_, h0⟩
    · exact ⟨_, not_not.1 (mt (X.cmType _).2 h0)⟩
  have s₁ := X.κ0_sign ⟨τ, hτ⟩
  have s₂ := X'.κ0_sign ⟨τ, hψ ▸ hτ⟩
  simp only at s₁ s₂
  rcases X.κ0_xi with h1 | h1 <;> rcases X'.κ0_xi with h2 | h2
  · rw [h1, h2, hξ]
  · exfalso
    rw [h1, hξ] at s₁
    rw [h2, map_neg, Complex.neg_im] at s₂
    linarith
  · exfalso
    rw [h2, ← hξ] at s₂
    rw [h1, map_neg, Complex.neg_im] at s₁
    linarith
  · rw [h1, h2, hξ]

set_option maxHeartbeats 2000000 in

theorem const_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D (T.V j σ) →* Module.End ℂ (WO V (T.V j σ) → ℂ)), IsPair ψ θ V (T.V j σ) χV χW om → ∀ hr : (T.V j σ).rank = D.R.r, (∀ k, IsMod (T.V j σ) hr ((T.U j σ).X k)) → ∀ (h : GA D (T.V j σ)) (δ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ γ : GA D (T.V j σ), (∀ τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ, Matrix.reindex (finCongr hr) (finCongr hr) (realM θ (Formalism.L2.Theta.mt (T.V j σ) γ) τ) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) → ∀ (hx₁ : (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom) (hx₂ : (C.dict₂ h).2 ∈ (C.U₂.X (C.dict₂ h).1).dom), IsUnitFr ((T.U j σ).X (T.dict j σ h).1) (T.dict j σ h).2 → ∀ (F₁ F₂ : WO V (T.V j σ) → ℂ) (m₁ m₂ : ℂ), (∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (C.U₂.X (C.dict₂ h).1).Λ) (idx : Fin g ≃ (C.U₂.X (C.dict₂ h).1).Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw j)), IsSympl (C.U₂.X (C.dict₂ h).1) bas → IdxIs C.d.c₂ C.σ₂ (C.U₂.X (C.dict₂ h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads C.U₂ (C.dict₂ h).1 bas idx e ⟨(C.dict₂ h).2, hx₂⟩ ϑ → ∀ w : WO V (T.V j σ), w.map (finPart D) = 0 → F₁ w = m₁ * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (C.U₂.X (C.dict₂ h).1) bas idx (C.dict₂ h).2 (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b) (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b)) * ∏ b, ϑ (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b)) → (∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((T.U j σ).X (T.dict j σ h).1).Λ) (idx : Fin g ≃ ((T.U j σ).X (T.dict j σ h).1).Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw j)), IsSympl ((T.U j σ).X (T.dict j σ h).1) bas → IdxIs T.Q.c σ ((T.U j σ).X (T.dict j σ h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads (T.U j σ) (T.dict j σ h).1 bas idx e ⟨(T.dict j σ h).2, hx₁⟩ ϑ → ∀ w : WO V (T.V j σ), w.map (finPart D) = 0 → F₂ w = m₂ * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx ((T.U j σ).X (T.dict j σ h).1) bas idx (T.dict j σ h).2 (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b) (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b)) * ∏ b, ϑ (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b)) → (∀ w, F₂ (actO V (T.V j σ) 1 γ w) = F₁ w) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a V.rank, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a V.rank, C.IsPull f f₂ → m₁ * rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = m₂ * rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 := by
  intro D T hT j hj σ hσ C hC ψ θ V χV χW om hP hr hM h δ hΛ hiso hfr γ hγ hx₁ hx₂ hu F₁ F₂ m₁ m₂ c₁ c₂ hF a f hf f₂ hf₂ hp
  obtain ⟨o₁, o₂⟩ := GlobalTheory.CoverFrameOver.un_over D T hT j hj σ hσ C hC h δ hΛ hiso hfr _ _ hx₂ hx₁ hfr
  obtain ⟨t, ht, hval, hlift⟩ := GlobalTheory.T.exists_scalar_levelCover_analyticFibre D T j σ C hC.1 hC.2.2.1 _ _ o₁ o₂
  obtain ⟨hlev, hA₂, hσ₂, hU₂, hdom, hr₂, g₂, e₂, F₂', ik₂, φ₂, th₂, hW₂, hth₂, -⟩ := hC
  have hU := hT.unf j hj σ hσ
  obtain ⟨-, -, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  have hr1 : 1 ≤ D.R.r := (hnum _ hj).2.1
  obtain ⟨Wt⟩ := nonempty_uw (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU
  have hSD : ∀ k, SelfD ((T.U j σ).X k) ((T.U j σ).X k).Λ := fun k => (GlobalTheory.T.uniformisation_component_lattices_markings _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU hr1 Wt k).2.1
  obtain ⟨Dc, hDc, -⟩ := GlobalTheory.Dict.exists_dic _ _ _ _ _ σ _ Wt.g 0 ((T.U j σ).X (T.dict j σ h).1) 0 Wt.e hσ hU.1
    (hU.2.1 _).1 (hU.2.1 _).2 (hSD _) ⟨fun _ => antitone_const, Even.zero⟩
  have hi : IdxIs T.Q.c σ ((T.U j σ).X (T.dict j σ h).1) Dc.idx Wt.e := hDc ▸ ⟨Dc.per_eq, Dc.ty_eq⟩
  obtain ⟨A, hmk, ϑ, hϑ, hone⟩ := GlobalTheory.Dict.uw_anFib _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU hr1 Wt _
    Dc.bas Dc.idx Dc.sympl hi.1 hi.2 ⟨_, hx₁⟩ hu
  obtain ⟨A₂, r₂⟩ := hlift _ _ _ Dc.bas Dc.idx Wt.e _ _ (Wt.mark _) Dc.sympl hx₁ (hSD _) ϑ ⟨A, hmk, hϑ⟩
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := fun τ =>
    ((hU.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hξ : ((T.U j σ).X (T.dict j σ h).1).ξ0 = (C.U₂.X (C.dict₂ h).1).ξ0 := (hM _).model.2.trans (hW₂ _).2.symm
  have hS : SameSp ((T.U j σ).X (T.dict j σ h).1) (C.U₂.X (C.dict₂ h).1) :=
    ⟨Finset.ext hΨ, (hM _).model.1.trans (hW₂ _).1.symm, (hU.2.1 _).1.trans (hU₂.2.1 _).1.symm, hξ,
      kappa_eq _ _ (Finset.ext hΨ) hξ⟩
  have hS' : SameSp (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1) :=
    ⟨hS.psi.symm, hS.gm.symm, hS.p0.symm, hS.xi.symm, hS.ka.symm⟩
  have hδ₂ : IsUn (C.U₂.X (C.dict₂ h).1) δ⁻¹ := fun u v => by
    have e := hiso ((δ⁻¹).1 *ᵥ u) ((δ⁻¹).1 *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.one_mulVec, hS.gm] at e
    exact e.symm
  have hδ₁ : IsUn ((T.U j σ).X (T.dict j σ h).1) δ := fun u v => by
    rw [hiso u v, hS.gm]
  obtain ⟨idx₂, hi₂, hpv, hty, hidx⟩ := GlobalTheory.FrameConstMove.exists_idx hS hi
  have hSD₁₂ : SelfD (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1).Λ := by
    refine ⟨(hSD _).1, fun v => ((hSD (T.dict j σ h).1).2 v).trans ?_⟩
    exact forall₂_congr fun y _ => by rw [hS.EF_eq]
  have hmt : GlobalTheory.LevelCusp.IsMatch (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1) δ := by
    refine ⟨hS.psi.symm, hS.p0.symm, hS.xi.symm, hiso, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · show δ.1 *ᵥ v ∈ (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E))
      rw [hΛ]
      exact ⟨v, hv, rfl⟩
    · have hv' : δ.1 *ᵥ v ∈ (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) := hv
      rw [hΛ] at hv'
      obtain ⟨u, hu', e⟩ := hv'
      have e' := congrArg (fun w => (δ⁻¹).1 *ᵥ w) e
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e'
      exact e' ▸ hu'
  have hlat : mapL δ⁻¹ ((T.U j σ).X (T.dict j σ h).1).Λ = (C.U₂.X (C.dict₂ h).1).Λ := by
    ext v
    rw [Lev.mem_mapL, Lev.lin_apply, inv_inv]
    exact (hmt.lat v).symm
  have hSD₂ : SelfD (C.U₂.X (C.dict₂ h).1) (C.U₂.X (C.dict₂ h).1).Λ := hlat ▸ Lev.selfD_mapL hδ₂ hSD₁₂
  obtain ⟨bas₂, hb₂⟩ := GlobalTheory.Dict.Letters.exists_isSympl (C.U₂.X (C.dict₂ h).1) hSD₂ idx₂
  have hx1eq : (T.dict j σ h).2 = lact δ (castFr hmt.psi (C.dict₂ h).2) := funext fun τ => by
    change mat (T.dict j σ h).2 τ = δ.1.map τ.1 * mat (C.dict₂ h).2 ⟨τ.1, _⟩
    exact hfr τ.1 _ τ.2
  have hfr₂ : lact δ⁻¹ (castFr hS.psi (T.dict j σ h).2) = (C.dict₂ h).2 := funext fun τ => by
    change (δ⁻¹).1.map τ.1 * mat (T.dict j σ h).2 ⟨τ.1, _⟩ = mat (C.dict₂ h).2 τ
    rw [hfr τ.1 τ.2, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mul]
  obtain ⟨-, -, -, A₃, r₃, -, -⟩ := letI : Algebra C.d.c₂.F ℂ := C.σ₂.toAlgebra
    GlobalTheory.Dict.anFib_move _ _ _ _ _ _ _ _ _ _ hS Dc.bas Dc.idx bas₂ idx₂ Wt.e _ _ _ A₂ δ⁻¹ Dc.sympl hb₂ hx₁ (hSD _) hδ₂
      (hpv _) hty
  have g₂ : GenReads C.U₂ (C.dict₂ h).1 bas₂ idx₂ Wt.e ⟨_, hx₂⟩ fun z => t * ϑ z := by
    have := r₃ _ r₂
    clear r₃
    revert A₃
    rw [hlat, hfr₂]
    exact fun A₃ h => ⟨A₃, h⟩
  have hrel : ∀ τ : D.host.E →+* ℂ, relab T.Q.c σ τ = relab C.d.c₂ C.σ₂ τ := fun τ => by
    ext a
    exact (RingHom.congr_fun hσ₂ _).symm.trans (congrArg C.σ₂ (Subtype.ext rfl))
  have hi₂' : IdxIs C.d.c₂ C.σ₂ (C.U₂.X (C.dict₂ h).1) idx₂ Wt.e :=
    ⟨fun x v j' => (hi₂.1 x v j').trans (by rw [hrel]), fun j' => (hi₂.2 j').trans (hrel _)⟩
  have hM₂ : IsMod (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) :=
    ⟨hW₂ _, fun τ => (hΨ τ).symm.trans ((hM _).psi τ), hS.ka.symm.trans (hM _).kap⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FrameConstMove.exists_ne_zero_of_meanOne hone
  obtain ⟨pt, -, hpt, -⟩ := (GlobalTheory.AdTh.RealCoord.zOf_coordinates D ψ θ V (T.V j σ) _ _ hr (C.U₂.X (C.dict₂ h).1) bas₂ idx₂
    hP.weil.std hP.inf hP.std hP.even hM₂ hb₂ (C.dict₂ h).2).2.2.2.2 hx₂
  obtain ⟨w0, wz⟩ := hpt fun _ => z
  generalize pt (fun _ => z) = w at w0 wz
  have wz' : zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) Dc.idx (T.dict j σ h).2 (actO V (T.V j σ) 1 γ w) =
      fun _ => z := by
    rw [← wz]
    funext b j'
    have hid : Dc.idx j' = (⟨(idx₂ j').1.1, hmt.psi.le (idx₂ j').1.2⟩, (idx₂ j').2) := by
      have e := hidx j'
      refine Prod.ext (Subtype.ext ?_) ?_
      · rw [e]
      · rw [e]
    refine Eq.trans ?_ (GlobalTheory.FrameConstMove.perC_match hmt (C.dict₂ h).2
      (fun τ a => realM θ w τ (Fin.cast hr.symm a) b) (idx₂ j').1 (idx₂ j').2)
    show perC _ _ _ (Dc.idx j') = _
    rw [hid, hx1eq]
    refine congrArg (fun u => perC _ _ u _) (funext fun τ => funext fun a' => ?_)
    rw [GlobalTheory.FrameConstMove.actO_one_left, GlobalTheory.FrameConstMove.realM_mul, ← hγ τ.1 τ.2]
    exact Fintype.sum_equiv (finCongr hr) _ _ fun c => rfl
  have v₂ := c₂ _ Dc.bas Dc.idx Wt.e Dc.sympl hi ϑ ⟨A, hϑ⟩ (actO V (T.V j σ) 1 γ w)
    (by rw [GlobalTheory.FrameConstMove.actO_one_left, Matrix.map_mul, w0, Matrix.mul_zero])
  have v₁ := c₁ _ bas₂ idx₂ Wt.e hb₂ hi₂' _ g₂ w w0
  rw [hF, wz'] at v₂
  rw [v₂, wz] at v₁
  have hxx : ∀ z w, hx ((T.U j σ).X (T.dict j σ h).1) Dc.bas Dc.idx (T.dict j σ h).2 z w =
      hx (C.U₂.X (C.dict₂ h).1) bas₂ idx₂ (C.dict₂ h).2 z w := by
    intro z' w'
    rw [hx1eq]
    exact GlobalTheory.FrameConstMove.hx_match hS' hb₂ Dc.sympl hx₂ (fun v => (hpv (castFr hS'.psi (C.dict₂ h).2) v).symm) hδ₁ z' w'
  simp only [hxx, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] at v₁
  have key : m₁ * t ^ V.rank = m₂ := by
    have hne : cexp (-(Real.pi / 2 : ℂ) * ∑ b : Fin V.rank, hx (C.U₂.X (C.dict₂ h).1) bas₂ idx₂ (C.dict₂ h).2 z z) *
        ϑ z ^ V.rank ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero _ hz)
    apply mul_right_cancel₀ hne
    linear_combination -v₁
  have u₁ : rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = toC (evR C.d.Xo₂ C.d.c₂ f₂ (C.U₂.un _ ⟨_, hx₂⟩)) := dif_pos hx₂
  have u₂ : rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 =
      toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un _ ⟨_, hx₁⟩)) := dif_pos hx₁
  rw [u₁, u₂, hval V.rank a f hf f₂ hp, ← key]
  ring

end GlobalTheory.CoverConstMove
end
end

