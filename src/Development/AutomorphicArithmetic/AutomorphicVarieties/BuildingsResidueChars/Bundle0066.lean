import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.RibetLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinLieAlgebraAction
section
open UpperTheory.V.Sd.Eis

private theorem complex_linear_combination_eq_half_of_relations (a b c d e f x y z w κ : ℂ) (hc : c - Complex.I * d ≠ 0)
    (h1 : a * e + b * f = 1) (h2 : c * e + d * f = 0)
    (hp1 : x + w = 0) (hp2 : y - z = Complex.I * κ) (hp3 : x - w = Complex.I * (y + z))
    (hE : e * (c * x + d * y) + f * (c * z + d * w) = 0) :
    e * (a * x + b * y) + f * (a * z + b * w) = κ / 2 := by
  have hw : w = -x := by linear_combination hp1
  have hs : y + z = -2 * Complex.I * x := by
    linear_combination (norm := skip) (Complex.I) * hp3 + (Complex.I) * hp1
    ring_nf; simp only [Complex.I_sq]; ring_nf
  have hy : y = -Complex.I * x + Complex.I * κ / 2 := by
    linear_combination (1/2) * hs + (1/2) * hp2
  have hz : z = -Complex.I * x - Complex.I * κ / 2 := by
    linear_combination (1/2) * hs - (1/2) * hp2
  subst hw hy hz
  apply mul_left_cancel₀ hc
  linear_combination (norm := skip) (a - Complex.I * b) * hE
    + (-κ/2) * (Complex.I * d - c) * h1 + (-κ/2) * (a - Complex.I * b) * h2
  ring_nf; simp only [Complex.I_sq, Complex.I_pow_four]; ring_nf

theorem UpperTheory.eisenstein_lie_algebra_action :
    UpperTheory.V.Sd.Eis.LieAlg := by
  intro h p κ hp1 hp2 hp3 hE
  have hMN : (h : Matrix (Fin 2) (Fin 2) ℝ) * ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1 := congrFun (congrFun hMN 0) 0
  have e2 := congrFun (congrFun hMN 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e1 e2
  have hdet : (h : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hMN
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [Matrix.det_fin_two] at hdet
  have hc : ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) - Complex.I * ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp at hre him
    apply hdet
    rw [hre, him]; ring
  have hent : ∀ (k i j : Fin 2),
      (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.single (0 : Fin 2) k (1 : ℝ)
        * (h : Matrix (Fin 2) (Fin 2) ℝ)) i j
        = ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i 0 * (h : Matrix (Fin 2) (Fin 2) ℝ) k j := by
    intro k i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  simp only [hent, Fin.sum_univ_two, Complex.ofReal_mul] at hE ⊢
  have e1' : ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)
      + ((h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 1 := by
    exact_mod_cast e1
  have e2' : ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)
      + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) * (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 0 := by
    exact_mod_cast e2
  have := complex_linear_combination_eq_half_of_relations _ _ _ _ _ _ (p 0 0) (p 0 1) (p 1 0) (p 1 1) κ hc e1' e2' hp1 hp2 hp3
    (by linear_combination hE)
  linear_combination this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinNormEqAbsPow
section
open UpperTheory.V.Sd.Eis NumberField GlobalTheory.Mem.Chr.CharModel

theorem UpperTheory.eisenstein_norm_eq_abs_pow :
    UpperTheory.V.Sd.Eis.AbsPow := by
  intro F _ _ _ s
  have H := absChar_isAbsPow (F := F) s
  refine ⟨⟨absHom F s, (absChar F s).2⟩, fun y hy => ?_, fun w => ⟨H.1 w, ?_⟩⟩
  · change Complex.exp (s * logNorm F (UpperTheory.V.TR.infId F y)) = _
    have h1 : finPart F (UpperTheory.V.TR.infId F y) = 1 := by
      apply Units.ext
      change (UpperTheory.V.TR.infId F y).val.2 = 1
      change ((1 : AdeleRing (𝓞 F) F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val).2 = 1
      change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) - 0 + 0 = 1
      simp
    have h2 : (infPart F (UpperTheory.V.TR.infId F y)).val = UpperTheory.V.TR.infEq F y.val := by
      change ((1 : AdeleRing (𝓞 F) F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val).1 = _
      change (1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F y.val = _
      simp
    have h3 : ∀ w : InfinitePlace F, ‖UpperTheory.V.TR.infEq F y.val w‖ = y.val w := fun w => by
      have := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.isometry.dist_eq (y.val w) 0
      have e0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 = 0 :=
        map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      rw [e0, dist_zero_right, dist_zero_right, Real.norm_of_nonneg (hy w).le] at this
      exact this
    rw [logNorm, h1, logFin_one, sub_zero, logInf, h2]
    simp only [h3, InfinitePlace.mult, IsTotallyReal.isReal, if_true, Nat.cast_one, one_mul]
    rw [← Real.log_prod (fun w _ => (hy w).ne'), Real.rpow_def_of_pos (Finset.prod_pos fun w _ => hy w),
      Complex.ofReal_exp, Complex.ofReal_mul, mul_comm]
  · refine (H.2.1 w).trans ?_
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinPeriodDerivative
section
open UpperTheory.V.Sd.Eis

private theorem UpperTheory.exists_bound_of_continuous_periodic_cocompact (A : Type) [AddCommGroup A] [TopologicalSpace A] (Γ : AddSubgroup A)
    (hC : Cocpt Γ) (g : A → ℝ → ℂ) (hg : Continuous (Function.uncurry g))
    (hgp : ∀ γ ∈ Γ, ∀ (x : A), g (γ + x) = g x) :
    ∃ M : ℝ, ∀ x : A, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖g x t‖ ≤ M := by
  obtain ⟨C, hCc, hCx⟩ := hC
  have hK : IsCompact (C ×ˢ Set.Icc (-1 : ℝ) 1) := hCc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨M, fun x t ht => ?_⟩
  obtain ⟨γ, hγ, hxγ⟩ := hCx x
  have h1 : g x = g (x - γ) := by
    have := hgp γ hγ (x - γ)
    rw [add_sub_cancel] at this
    exact this
  rw [h1]
  exact hM (x - γ, t) ⟨hxγ, ht⟩

theorem UpperTheory.eisenstein_period_derivative :
    UpperTheory.V.Sd.Eis.PerDeriv := by
  intro A _ _ _ _ _ _ Γ hC μ D hDt f f' hf hf' hfp hf'p hd
  obtain ⟨M, hM⟩ := UpperTheory.exists_bound_of_continuous_periodic_cocompact A Γ hC f' hf' hf'p
  obtain ⟨N, hN⟩ := UpperTheory.exists_bound_of_continuous_periodic_cocompact A Γ hC f hf hfp
  have hslice : ∀ (g : A → ℝ → ℂ), Continuous (Function.uncurry g) → ∀ t : ℝ, Continuous (fun x => g x t) :=
    fun g hg t => hg.comp (continuous_id.prodMk continuous_const)
  haveI hfin : MeasureTheory.IsFiniteMeasure (μ.restrict D) := MeasureTheory.isFiniteMeasure_restrict.2 hDt
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict D)
    (F := fun t x => f x t) (F' := fun t x => f' x t) (x₀ := (0 : ℝ)) (bound := fun _ => M)
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun t => (hslice f hf t).aestronglyMeasurable)
    (MeasureTheory.Measure.integrableOn_of_bounded (M := N) hDt (hslice f hf 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hN x 0 ⟨by norm_num, by norm_num⟩))
    (hslice f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht => hM x t ht)
    (MeasureTheory.integrable_const M)
    (Filter.Eventually.of_forall fun x t _ => hd x t)
  exact key.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinSmoothContinuous
section
open UpperTheory.V.Sd.Eis
open NumberField Topology Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host UpperTheory.V

private theorem cont_map {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (a : ℕ) (f : R →+* S) (hf : Continuous f) :
    Continuous (fun g : GL (Fin a) R => GeneralLinearGroup.map f g) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hf
  · exact Units.continuous_coe_inv.matrix_map hf

private theorem cont_pInf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : Continuous (TR.pInf F) := by
  have h : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
        (continuous_apply w)
  exact h.comp continuous_fst

theorem UpperTheory.eisenstein_smooth_continuous :
    UpperTheory.V.Sd.Eis.SmCont := by
  intro F _ _ _ a φ hU
  have hy := cont_map a (TR.pInf F) (cont_pInf F)
  have hk := cont_map a (pFin F) continuous_snd
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  set k₀ := GeneralLinearGroup.map (pFin F) g₀ with hk₀
  have hy' : Continuous fun g : GA F a => TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (TR.Rinf F))).comp hy
  have hc : ContinuousAt (fun g : GA F a =>
      TR.chart φ.1 (finGL F a k₀) (TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val)) g₀ :=
    ContinuousAt.comp (f := fun g : GA F a => TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val)
      (TR.contDiffAt_chart φ.2 _ (TR.val_mem_invSet _)).continuousAt hy'.continuousAt
  refine hc.congr ?_
  have hk' : Continuous fun g : GA F a => k₀⁻¹ * GeneralLinearGroup.map (pFin F) g :=
    continuous_const.mul hk
  have hn : ∀ᶠ g : GA F a in 𝓝 g₀, TR.finRep F a (k₀⁻¹ * GeneralLinearGroup.map (pFin F) g) φ = φ := by
    refine (hU.preimage hk').mem_nhds ?_
    change TR.finRep F a (k₀⁻¹ * k₀) φ = φ
    rw [inv_mul_cancel, map_one]; rfl
  filter_upwards [hn] with g hg
  rw [TR.chart_val]
  have e := congrFun (congrArg Subtype.val hg) (finGL F a k₀ * TR.infGL F a (GeneralLinearGroup.map (TR.pInf F) g))
  rw [← e]
  change φ.1 (_ * finGL F a _) = _
  rw [← TR.infGL_comm, mul_assoc, ← map_mul, mul_inv_cancel_left, TR.infGL_mul_finGL]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCharacterSeparation
section
open UpperTheory.V.Sd.Eis

private theorem exists_addChar_fourier_coeff_ne_zero_of_ne_zero {α : Type} [AddCommGroup α] [Fintype α] (F : α → ℂ) (hF : F ≠ 0) :
    ∃ ψ : AddChar α ℂ, ∑ a, F a * ψ (-a) ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hF
  funext x
  have key : ∑ ψ : AddChar α ℂ, ∑ a, F a * ψ (x - a) = (Fintype.card α : ℂ) * F x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite, sub_eq_zero]
    rw [Finset.sum_eq_single x]
    · simp [mul_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have key2 : ∑ ψ : AddChar α ℂ, ∑ a, F a * ψ (x - a) = 0 := by
    apply Finset.sum_eq_zero
    intro ψ _
    simp_rw [sub_eq_add_neg, AddChar.map_add_eq_mul, mul_left_comm (F _), ← Finset.mul_sum, h ψ,
      mul_zero]
  have hc : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have := key.symm.trans key2
  simpa [hc] using this

theorem UpperTheory.exists_character_separation :
    UpperTheory.V.Sd.Eis.CharPick := by
  intro T _ U₀ hU₀ f₀ hf₀ hinv
  classical
  have inv_out : ∀ (V : Subgroup T) (w : T → ℂ), (∀ t u, u ∈ V → w (t * u) = w t) →
      ∀ t : T, w ((QuotientGroup.mk t : T ⧸ V).out) = w t := by
    intro V w hw t
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul V t
    rw [hh, hw _ _ h.2]
  haveI : Fintype (T ⧸ U₀) := Fintype.ofFinite _
  let F : Additive (T ⧸ U₀) → ℂ := fun a => f₀ (Additive.toMul a).out
  have hF : F ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hf₀
    intro h0
    apply ht
    have := congrFun h0 (Additive.ofMul (QuotientGroup.mk t))
    simp only [F, toMul_ofMul, Pi.zero_apply] at this
    rw [inv_out U₀ f₀ hinv t] at this
    exact this
  obtain ⟨ψ, hψ⟩ := exists_addChar_fourier_coeff_ne_zero_of_ne_zero F hF
  let χ : T →* ℂˣ :=
    { toFun := fun t => ⟨ψ (Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀)),
        ψ (-(Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀))),
        by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
        by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [AddChar.map_add_eq_mul] }
  have hχval : ∀ t, (((χ t)⁻¹ : ℂˣ) : ℂ) = ψ (-(Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀))) :=
    fun t => rfl
  have hχU₀ : ∀ u ∈ U₀, χ u = 1 := by
    intro u hu
    ext
    simp [χ, (QuotientGroup.eq_one_iff u).mpr hu]
  let aV : Subgroup T → (T → ℂ) → ℂ := fun V h =>
    ∑ᶠ q : T ⧸ V, h q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ)
  have aV_lin : ∀ V : Subgroup T, V.FiniteIndex → ∀ (c : ℂ) (p p' : T → ℂ),
      aV V (c • p + p') = c * aV V p + aV V p' := by
    intro V hV c p p'
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    simp only [aV, finsum_eq_sum_of_fintype, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have aV_zero : ∀ V : Subgroup T, aV V 0 = 0 := by
    intro V; simp [aV]
  have kill : ∀ V : Subgroup T, V.FiniteIndex → V ≤ U₀ → ∀ g : T → ℂ,
      (∀ t u, u ∈ V → g (t * u) = g t) → ∀ s, aV V (fun t => g (t * s)) = (χ s : ℂ) * aV V g := by
    intro V hV hVU g hg s
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    let φ : T → ℂ := fun t => g t * (((χ t)⁻¹ : ℂˣ) : ℂ)
    have hφ : ∀ t u, u ∈ V → φ (t * u) = φ t := by
      intro t u hu
      simp only [φ, map_mul, hχU₀ u (hVU hu), mul_one, hg t u hu]
    simp only [aV, finsum_eq_sum_of_fintype]
    have hre : ∑ q : T ⧸ V, g q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ)
        = ∑ q : T ⧸ V, g (q * (QuotientGroup.mk s : T ⧸ V)).out
            * (((χ (q * (QuotientGroup.mk s : T ⧸ V)).out)⁻¹ : ℂˣ) : ℂ) :=
      (Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk s : T ⧸ V))
        (fun q => g q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ))).symm
    rw [hre, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    have hq : q * (QuotientGroup.mk s : T ⧸ V) = QuotientGroup.mk (q.out * s) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have h2 := inv_out V φ hφ (q.out * s)
    rw [hq]
    change _ = _ * φ _
    rw [h2]
    simp only [φ, map_mul, mul_inv, Units.val_mul]
    have hs1 : (χ s : ℂ) * (((χ s)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    linear_combination (-(g (q.out * s) * (((χ q.out)⁻¹ : ℂˣ) : ℂ))) * hs1
  have fiber : ∀ V : Subgroup T, V ≤ U₀ → V.FiniteIndex → aV V f₀ ≠ 0 := by
    intro V hVU hV
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    let π : T ⧸ V →* T ⧸ U₀ := QuotientGroup.map V U₀ (MonoidHom.id T) (fun x hx => hVU hx)
    let φ0 : T → ℂ := fun t => f₀ t * (((χ t)⁻¹ : ℂˣ) : ℂ)
    have hφ0 : ∀ t u, u ∈ U₀ → φ0 (t * u) = φ0 t := by
      intro t u hu
      simp only [φ0, map_mul, hχU₀ u hu, mul_one, hinv t u hu]
    let Kf : T ⧸ U₀ → ℂ := fun r => φ0 r.out
    have hH : ∀ q : T ⧸ V, f₀ q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ) = Kf (π q) := by
      intro q
      have : π q = QuotientGroup.mk q.out := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [this]
      exact (inv_out U₀ φ0 hφ0 q.out).symm
    have hsurj : ∀ r : T ⧸ U₀, r ∈ Set.range π := by
      intro r
      refine ⟨QuotientGroup.mk r.out, ?_⟩
      change (QuotientGroup.mk r.out : T ⧸ U₀) = r
      exact QuotientGroup.out_eq' r
    have hcard : ∀ r : T ⧸ U₀, (Finset.univ.filter fun q => π q = r).card
        = (Finset.univ.filter fun q => π q = 1).card :=
      fun r => MonoidHom.card_fiber_eq_of_mem_range π (hsurj r) (hsurj 1)
    have hpos : (Finset.univ.filter fun q => π q = 1).card ≠ 0 := by
      rw [Finset.card_ne_zero]
      exact ⟨1, by simp⟩
    have hsumK : ∑ r, Kf r ≠ 0 := by
      have e : ∑ r, Kf r = ∑ a, F a * ψ (-a) := by
        refine Fintype.sum_equiv Additive.ofMul _ _ (fun r => ?_)
        simp only [Kf, φ0, F, hχval, QuotientGroup.out_eq', toMul_ofMul]
      rw [e]; exact hψ
    simp only [aV, finsum_eq_sum_of_fintype, hH]
    rw [← Finset.sum_fiberwise' Finset.univ π Kf]
    simp only [Finset.sum_const, hcard, nsmul_eq_mul, ← Finset.mul_sum]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hpos) hsumK
  let Kset : Set (T → ℂ) := {p | ∃ (U : Subgroup T) (g : T → ℂ) (s : T), U.FiniteIndex ∧
      (∀ t u, u ∈ U → g (t * u) = g t) ∧ p = (fun t => g (t * s)) - (χ s : ℂ) • g}
  have key : ∀ p : T → ℂ, p ∈ Submodule.span ℂ Kset → ∃ V : Subgroup T, V ≤ U₀ ∧ V.FiniteIndex ∧
      ∀ V' : Subgroup T, V' ≤ V → V'.FiniteIndex → aV V' p = 0 := by
    intro p hmem
    induction hmem using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨U, g, s, hU, hg, rfl⟩ := hp
      haveI := hU
      haveI := hU₀
      refine ⟨U ⊓ U₀, inf_le_right, inferInstance, fun V' hV' hV'f => ?_⟩
      have hg' : ∀ t u, u ∈ V' → g (t * u) = g t :=
        fun t u hu => hg t u (Subgroup.mem_inf.mp (hV' hu)).1
      have e : (fun t => g (t * s)) - (χ s : ℂ) • g = (-(χ s : ℂ)) • g + (fun t => g (t * s)) := by
        funext t; simp; ring
      rw [e, aV_lin V' hV'f, kill V' hV'f (hV'.trans inf_le_right) g hg' s]
      ring
    | zero => exact ⟨U₀, le_rfl, hU₀, fun V' _ _ => aV_zero V'⟩
    | add x y _ _ hx hy =>
      obtain ⟨V1, hV1U, hV1f, hV1⟩ := hx
      obtain ⟨V2, hV2U, hV2f, hV2⟩ := hy
      haveI := hV1f
      haveI := hV2f
      refine ⟨V1 ⊓ V2, inf_le_left.trans hV1U, inferInstance, fun V' hV' hV'f => ?_⟩
      have := aV_lin V' hV'f 1 x y
      rw [one_smul, one_mul] at this
      rw [this, hV1 V' (hV'.trans inf_le_left) hV'f, hV2 V' (hV'.trans inf_le_right) hV'f, add_zero]
    | smul c x _ hx =>
      obtain ⟨V1, hV1U, hV1f, hV1⟩ := hx
      refine ⟨V1, hV1U, hV1f, fun V' hV' hV'f => ?_⟩
      have := aV_lin V' hV'f c x 0
      rw [add_zero, aV_zero, add_zero] at this
      rw [this, hV1 V' hV' hV'f, mul_zero]
  have hnot : f₀ ∉ Submodule.span ℂ Kset := by
    intro hmem
    obtain ⟨V, hVU, hVf, hV⟩ := key f₀ hmem
    exact fiber V hVU hVf (hV V le_rfl hVf)
  obtain ⟨L, hL, hLK⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨χ, L, hχU₀, hL, ?_⟩
  intro U hU f hf s
  have hmemK : (fun t => f (t * s)) - (χ s : ℂ) • f ∈ Submodule.span ℂ Kset :=
    Submodule.subset_span ⟨U, f, s, hU, hf, rfl⟩
  have h0 : L ((fun t => f (t * s)) - (χ s : ℂ) • f) = 0 := by
    have := Submodule.mem_map_of_mem (f := L) hmemK
    rw [hLK, Submodule.mem_bot] at this
    exact this
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticCharacterOfSubgroupIndexTwo
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.Ws UpperTheory.V.Sd.S2

private theorem exists_sign_character_index_two {Γ R : Type} [Group Γ] [CommRing R] (H : Subgroup Γ) (h : H.index = 2) :
    ∃ φ : Γ →* Rˣ, (∀ g ∈ H, φ g = 1) ∧ ∀ g ∉ H, φ g = -1 := by
  classical
  refine ⟨MonoidHom.mk' (fun g => if g ∈ H then 1 else -1) fun a b => ?_, fun g hg => if_pos hg, fun g hg => if_neg hg⟩
  by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [Subgroup.mul_mem_iff_of_index_two h, ha, hb]

theorem UpperTheory.exists_quadratic_character_of_subgroup_index_two :
    UpperTheory.V.Sd.S2.HypEx := by
  intro Ω _ _ _ l _ c D T hg hok htwo hdeep
  obtain ⟨k₀, hdeg, hreal, hsp, hps⟩ := htwo.quad
  haveI : FiniteDimensional ℚ k₀ := Module.finite_of_finrank_pos (by omega)
  haveI hnf : NumberField k₀ := {}
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
  obtain ⟨hE, hO, hI⟩ := galEmbTop ℚ k₀ Ω
  have hfix : galOf ℚ k₀ Ω = k₀.fixingSubgroup := by
    ext σ
    rw [mem_galOf, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩
  have hr : (resQ k₀).range = k₀.fixingSubgroup := (range_galEmb ℚ k₀ Ω).trans hfix
  have hidx : k₀.fixingSubgroup.index = 2 := by rw [← hfix, hI, hdeg]
  obtain ⟨φ, h1, h2⟩ := exists_sign_character_index_two (R := PadicAlgCl l) k₀.fixingSubgroup hidx
  refine ⟨k₀, hnf, hreal, φ, ⟨hg, hok, htwo, hdeep, hdeg, ?_, ?_, hps, h1, h2⟩, hr, hidx, hE, ?_⟩
  · exact hsp 2 (by simp)
  · exact hsp l (by simp)
  · rw [← MonoidHom.coe_range, hr, ← hfix]
    exact hO
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRibetLattice
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

theorem UpperTheory.exists_ribet_lattice :
    UpperTheory.V.Sd.S2.RibOf := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r hyp hch hd u hu
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois k₀ Ω := {}
  have hc : Continuous (resQ k₀ : G k₀ Ω →* G ℚ Ω) := by
    have h := (galEmbTop ℚ k₀ Ω).1.continuous
    have e : (resQ k₀ : G k₀ Ω →* G ℚ Ω) = galEmb ℚ k₀ Ω := by
      ext σ x
      rw [galEmb_apply]; rfl
    rw [e]; exact h
  let H : Subgroup (G k₀ Ω) := T.F.fixingSubgroup.comap (resQ k₀)
  have hHo : IsOpen (H : Set (G k₀ Ω)) := T.F.fixingSubgroup_isOpen.preimage hc
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 (H.isClosed_of_isOpen hHo).isCompact
  have hg : resQ T.F T.g0 ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact T.g0.commutes ⟨x, hx⟩
  have huH : u ∈ H := by
    show resQ k₀ u ∈ T.F.fixingSubgroup
    rw [hu]; exact mul_mem hg hg
  obtain ⟨ρ', ⟨g, hρ⟩, q1, q2, q3, s, q4⟩ := ribetLat l H (r.comp H.subtype) 1 (((up D.ξ).comp (resQ k₀)).comp H.subtype)
    (hd.cont.comp continuous_subtype_val) (hd.irr H hHo) (fun s => ⟨by simp, hch.unit _ _⟩)
    (fun s i => by
      have := hd.res s i
      simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.comp_apply, MonoidHom.one_apply,
        Subgroup.coe_subtype] using this) ⟨u, huH⟩ (by
      have := hch.sq
      rw [← hu] at this
      exact this)
  have e : ∀ s : H, ((MulAut.conj g).toMonoidHom.comp r) s = ρ' s := fun s => (hρ s).symm
  refine ⟨(MulAut.conj g).toMonoidHom.comp r, ⟨g, fun _ => rfl⟩, ?_, ?_, fun h hh => ?_, s, s.2, ?_⟩
  · rw [e ⟨u, huH⟩]; exact q1
  · rw [e ⟨u, huH⟩]; exact q2
  · rw [e ⟨h, hh⟩]; exact q3 ⟨h, hh⟩
  · rw [e s]; exact q4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSplitPrimeCmDatum
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

theorem UpperTheory.exists_splitPrime_cmDatum :
    UpperTheory.V.Sd.S3.SplitPrime := by
  intro Ω _ _ _ U hU hc M hM
  obtain ⟨N, hN, hNU⟩ := UpperTheory.V.CF.kwAbs Ω U hU hc
  obtain ⟨w, hw, hMw, hmod⟩ := Nat.exists_prime_gt_modEq_one M (Nat.mul_ne_zero hM.ne' hN.ne')
  have hwM : w ≡ 1 [MOD M] := Nat.ModEq.of_dvd (Dvd.intro N rfl) hmod
  have hwN : w ≡ 1 [MOD N] := Nat.ModEq.of_dvd (Dvd.intro_left M rfl) hmod
  refine ⟨w, hw, hMw, hwM, ?_⟩
  intro A hA g hg
  haveI : Fact (Nat.Prime w) := ⟨hw⟩
  have hcop : N.Coprime w := by
    have h := Nat.ModEq.gcd_eq hwN
    rw [Nat.gcd_one_left] at h
    exact Nat.Coprime.symm h
  obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω w A hA N hcop g hg
  apply hNU
  intro ζ hζ
  rw [hk ζ hζ]
  have hpow : w ^ k % N = 1 % N := by
    have h := Nat.ModEq.pow k hwN
    rwa [one_pow] at h
  rw [← Nat.div_add_mod (w ^ k) N, pow_add, pow_mul, hζ, one_pow, one_mul, hpow]
  rcases Nat.lt_or_ge 1 N with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have hN1 : N = 1 := by omega
    subst hN1
    simp only [pow_one] at hζ
    simp [hζ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeOverField
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem key {R : Type} [Field R] {g s t : M2 R} {x y : R} (h : g * t = s * g) (hg0 : g 0 0 ≠ 0)
    (hg : g 1 1 = 1 ∧ g 0 1 = 0) (hs : s 1 1 = 1 ∧ s 0 1 = 0) (ht : t 1 1 = 1 ∧ t 0 1 = 0) (hne : s 0 0 ≠ 1)
    (hx : t 1 0 + t 1 1 * x = (t 0 0 + t 0 1 * x) * x) (hy : s 1 0 + s 1 1 * y = (s 0 0 + s 0 1 * y) * y) :
    g 1 0 + g 1 1 * x - (g 0 0 + g 0 1 * x) * y = 0 := by
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hg.1, hg.2, hs.1, hs.2, ht.1, ht.2] at h0 h1 hx hy ⊢
  have e : t 0 0 = s 0 0 := mul_left_cancel₀ hg0 (by linear_combination h0)
  rw [e] at h1 hx
  refine mul_left_cancel₀ (sub_ne_zero.2 hne) ?_
  linear_combination h1 - hx + g 0 0 * hy
end

