import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.FiniteIdeleCongruenceVolumePos
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma eq_one_of_mul'' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private noncomputable def ef (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (A ℚ)ˣ := (IdeleGroup.prodEquiv ℚ).symm (1, x)

private lemma ef_fst (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ((ef x : (A ℚ)ˣ) : A ℚ).1 = 1 := rfl

private lemma inv_mul_at (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : H.P ℚ) :
    Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) *
      Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
  rw [← map_mul]
  have h := congrArg (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v) (Units.inv_mul x)
  have h' : ((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
      (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
  rw [h', map_one]

private lemma natCast_ne (L : ℕ) (hL : 0 < L) (v : H.P ℚ) : (L : H.Kv v) ≠ 0 := by
  exact_mod_cast hL.ne'

private lemma v_natCast_of_not_bad (L : ℕ) (v : H.P ℚ) (h : ¬ Bad L v) : Valued.v (L : H.Kv v) = 1 := by
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (L : 𝓞 ℚ)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h] at h2
  exact_mod_cast h2

private lemma finite_bad (L : ℕ) (hL : 0 < L) : {v : H.P ℚ | Bad L v}.Finite := by
  have hne : Ideal.span {(L : 𝓞 ℚ)} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hL.ne'
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

private lemma nhds_cong (L : ℕ) (hL : 0 < L) (v : H.P ℚ) :
    {x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ | Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ Valued.v (L : H.Kv v)} ∈
      𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
  have hB : IsOpen {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} := by
    have : {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} =
        {y | Valued.v.restrict y ≤ Valued.v.restrict (L : H.Kv v)} := by
      ext y
      simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff]
    rw [this]
    exact Valued.isOpen_closedBall _ (by simp [natCast_ne L hL v])
  have he : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v := RestrictedProduct.continuous_eval v
  have hf : Continuous fun x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ => (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 :=
    (he.comp Units.continuous_val).sub continuous_const
  refine (hB.preimage hf).mem_nhds ?_
  have h0 : ((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 = 0 := sub_self _
  change Valued.v (((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ _
  rw [h0, map_zero]
  exact zero_le'

theorem UpperTheory.finiteIdele_congruenceVolume_pos :
    ∀ L : ℕ, 0 < L → 0 < cT L := by
  intro L hL
  set S : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (fun u => (IdeleGroup.prodEquiv ℚ).symm (1, u)) ⁻¹' TT L with hS
  have hcT : cT L = (finiteIdeleMeasure ℚ S).toReal := rfl
  have hsub : S ⊆ (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    intro x hx
    have hu : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := fun v => hx.1.2 v
    refine (mem_finiteIntegralUnits ℚ).2 fun v => ?_
    have hi := inv_mul_at x v
    rw [hu v, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hu v).le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  have hnhds : S ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    have h1 : (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
      (isOpen_finiteIntegralUnits ℚ).mem_nhds (one_mem _)
    have h2 := (Filter.biInter_mem (finite_bad L hL)).2 fun v (_ : Bad L v) => nhds_cong L hL v
    filter_upwards [h1, h2] with x hx hc
    obtain hxi := (mem_finiteIntegralUnits ℚ).1 hx
    have hle : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 := fun v =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).1
    have hle' : ∀ v : H.P ℚ, Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 :=
      fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).2
    refine ⟨⟨ef_fst x, fun v => ?_⟩, fun v => ?_⟩
    · exact eq_one_of_mul'' (hle v) (hle' v) (by rw [mul_comm]; exact inv_mul_at x v)
    · have hcp : H.cp v ((ef x : (A ℚ)ˣ) : A ℚ) - 1 = (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 := rfl
      change Valued.v (H.cp v (((ef x : (A ℚ)ˣ) : A ℚ) - 1)) ≤ _
      rw [map_sub, map_one, hcp]
      by_cases hb : Bad L v
      · exact Set.mem_iInter₂.1 hc v hb
      · rw [v_natCast_of_not_bad L v hb]
        refine (Valuation.map_sub _ _ _).trans (max_le (hle v) ?_)
        rw [map_one]
  rw [hcT]
  refine ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds _ hnhds).ne' ?_
  refine ((measure_mono hsub).trans_lt ?_).ne
  rw [finiteIdeleMeasure_finiteIntegralUnits]
  exact ENNReal.one_lt_top
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.FixedAndHeckeEigenOfFinsetLinearCombination
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem finsum_Tj_eq {E : Type} [Field E] [NumberField E] {w : H.P E} {ϖ : w.adicCompletion E}
    (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ t : Finset (GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w 2),
      ∀ F : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w 2 → ℂ,
        ∑ᶠ x, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j x.out * F x =
          ∑ x ∈ t, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j x.out * F x := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  refine ⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun x hx => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hx

theorem UpperTheory.fixed_and_heckeEigen_of_finset_linearCombination :
    ∀ (E : Type) [Field E] [NumberField E] (w : H.P E) (ι : Type) (s : Finset ι) (c : ι → ℂ) (φ : ι → GL (Fin 2) (A E) → ℂ) (B : Multiset ℂˣ), s.Nonempty → (∀ i, H.Fix w (φ i)) → (∀ i, EigAt w B (φ i)) → H.Fix w (fun g => ∑ i ∈ s, c i * φ i g) ∧ EigAt w B (fun g => ∑ i ∈ s, c i * φ i g) := by
  intro E _ _ w ι s c φ B hs hF hE
  obtain ⟨i₀, -⟩ := hs
  refine ⟨fun g k hk => ?_, fun g => ⟨(hE i₀ g).card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩⟩
  · simp only [fun i => hF i g k hk]
  · simp only [fun i => (hE i g).inv y k hk]
  · obtain ⟨t, ht⟩ := finsum_Tj_eq (w := w) hϖ j
    rw [ht]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := (hE i g).eig ϖ hϖ j hj y
    rw [ht] at e
    rw [mul_left_comm, ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => mul_left_comm _ _ _
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.HasDerivAtWhittakerPeriodOneParameter
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem cover : ∃ C : Set (Fin 2 → A ℚ), IsCompact C ∧ FS2 ℚ ⊆ C := by
  obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
    ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
      (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  exact ⟨Set.univ.pi fun _ : Fin 2 => C, isCompact_univ_pi fun _ => hC, fun x hx i hi => hEC (hx i hi)⟩

private theorem cont_nE' {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous fun u : Fin 2 → A ℚ => nE D u :=
  continuous_gl.comp (continuous_nU.comp ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
    ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)))

private theorem deriv_at {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (f : Sm E 2)
    (c : ℝ → GL (Fin 2) (Cinf E)) (X : Lie E 2) (x : GL (Fin 2) (A E)) (c0 : c 0 = 1)
    (cadd : ∀ s t, c (s + t) = c s * c t) (cd : HasDerivAt (fun t => toL (c t).val) X 0) (t : ℝ) :
    HasDerivAt (fun τ => f.1 (x * infGL E 2 (c τ))) ((lie E 2 X f).1 (x * infGL E 2 (c t))) t := by
  have h := hasDerivAt_curve f (x * infGL E 2 (c t)) c X c0 cd
  have h2 : HasDerivAt (fun s => f.1 (x * infGL E 2 (c t) * infGL E 2 (c s))) ((lie E 2 X f).1 (x * infGL E 2 (c t))) (t - t) := by
    rw [sub_self]; exact h
  have h3 := HasDerivAt.comp_sub_const t t h2
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
  have e : c τ = c t * c (τ - t) := by rw [← cadd]; congr 1; ring
  simp only [e, map_mul, mul_assoc]

theorem UpperTheory.hasDerivAt_whittakerPeriod_oneParameter :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2) (c : ℝ → GL (Fin 2) (Cinf E)) (X : Lie E 2)
        (g : GL (Fin 2) (A E)), c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → HasDerivAt (fun t => toL (c t).val) X 0 →
        Continuous f.1 → Continuous (lie E 2 X f).1 → (∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B) →
        HasDerivAt (fun t : ℝ => Wo D f.1 (g * infGL E 2 (c t))) (Wo D (lie E 2 X f).1 g) 0 := by
  intro E _ _ _ D f c X g c0 cadd cd hf hl ⟨B, hB⟩
  obtain ⟨C, hC, hsub⟩ := cover
  have hfin : adeleMeasurePi ℚ (FS2 ℚ) < ⊤ := (measure_mono hsub).trans_lt hC.measure_lt_top
  haveI : IsFiniteMeasure ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := ⟨by simpa using hfin⟩
  have hn := cont_nE' D
  have hψ : Continuous fun u : Fin 2 → A ℚ => ψ (u 1) := continuous_ψ.comp (continuous_apply 1)
  have hF : ∀ h : GL (Fin 2) (A E), Continuous fun u : Fin 2 → A ℚ => f.1 (nE D u * h) * ψ (u 1) :=
    fun h => (hf.comp (hn.mul continuous_const)).mul hψ
  have hF' : ∀ h : GL (Fin 2) (A E), Continuous fun u : Fin 2 → A ℚ => (lie E 2 X f).1 (nE D u * h) * ψ (u 1) :=
    fun h => (hl.comp (hn.mul continuous_const)).mul hψ
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (adeleMeasurePi ℚ).restrict (FS2 ℚ)) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t u => f.1 (nE D u * (g * infGL E 2 (c t))) * ψ (u 1))
    (F' := fun t u => (lie E 2 X f).1 (nE D u * (g * infGL E 2 (c t))) * ψ (u 1))
    (bound := fun _ => B) Filter.univ_mem
    (Eventually.of_forall fun t => (hF _).aestronglyMeasurable)
    (((hF _).continuousOn.integrableOn_compact hC).mono_set hsub)
    (hF' _).aestronglyMeasurable
    (ae_of_all _ fun u t _ => by rw [norm_mul, norm_ψ, mul_one]; exact hB _)
    (integrable_const _)
    (ae_of_all _ fun u t _ => by
      have h := deriv_at f c X (nE D u * g) c0 cadd cd t
      simp only [mul_assoc] at h
      exact h.mul_const (ψ (u 1)))
  have h2 := key.2
  simp only [c0, map_one, mul_one] at h2
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.HasLevelOfUnitIdeleCongruentOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.hasLevel_of_unitIdele_congruent_one :
    ∀ (L : ℕ), 0 < L → ∀ t : (A ℚ)ˣ, t ∈ UU → (∀ v, Dv L v ((t : A ℚ) - 1)) → Lev L (aE t) := by
  intro L _ t ht hD
  have h1 : (t : A ℚ).1 = 1 := ht.1
  have hu : ∀ v : H.P ℚ, Valued.v (H.cp v (t : A ℚ)) = 1 := ht.2
  have hi : ∀ v : H.P ℚ, Valued.v (H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ)) = 1 := by
    intro v
    have hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have := congrArg Valued.v hm
    rwa [map_mul, hu v, one_mul, map_one] at this
  have hz : ∀ v : H.P ℚ, Dv L v 0 := by
    intro v
    simp [Dv]
  refine ⟨fun i j => ?_, fun v => ⟨?_, fun i j => ?_⟩⟩
  · fin_cases i <;> fin_cases j <;> simp [aE, h1] <;> rfl
  · rw [H.KAt, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
    have e1 : (1 : H.Kv v) ∈ Formalism.UG.Ov ℚ v := one_mem _
    have e0 : (0 : H.Kv v) ∈ Formalism.UG.Ov ℚ v := zero_mem _
    have et : H.cp v (t : A ℚ) ∈ Formalism.UG.Ov ℚ v := (hu v).le
    have ei : H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) ∈ Formalism.UG.Ov ℚ v := (hi v).le
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa [aE, Matrix.GeneralLinearGroup.map] using et
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e1
    · fin_cases i <;> fin_cases j
      · exact ei
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e0
      · simpa [aE, Matrix.GeneralLinearGroup.map] using e1
  · fin_cases i <;> fin_cases j
    · simpa [aE] using hD v
    · simpa [aE] using hz v
    · simpa [aE] using hz v
    · simpa [aE] using hz v
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IdeleCongruenceConditionMulCongruenceUnitIff
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.ideleCongruenceCondition_mul_congruenceUnit_iff :
    ∀ N : ℕ, 0 < N → ∀ τ ∈ TT N, ∀ y : (A ℚ)ˣ, ((∀ v, Bad N v → Dv N v (((y * τ : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y * τ : (A ℚ)ˣ) : A ℚ)) ≤ 1) ↔ ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) := by
  intro N _ τ hτ y
  obtain ⟨⟨_, hu⟩, hd⟩ := hτ
  have h1 : ∀ v : H.P ℚ, Valued.v (H.cp v ((y * τ : (A ℚ)ˣ) : A ℚ)) = Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) := by
    intro v
    rw [Units.val_mul, map_mul, map_mul, hu v, mul_one]
  have h2 : ∀ v : H.P ℚ, Dv N v (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) ↔ Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1) := by
    intro v
    have hv := hd v
    have he : Valued.v (H.cp v (((y : A ℚ) - 1) * (τ : A ℚ))) = Valued.v (H.cp v ((y : A ℚ) - 1)) := by
      rw [map_mul, map_mul, hu v, mul_one]
    unfold Dv at hv ⊢
    constructor
    · intro h
      have e : ((y : A ℚ) - 1) * (τ : A ℚ) = (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) - ((τ : A ℚ) - 1) := by
        rw [Units.val_mul]; ring
      rw [← he, e, map_sub]
      exact Valuation.map_sub_le _ h hv
    · intro h
      have e : (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) = ((y : A ℚ) - 1) * (τ : A ℚ) + ((τ : A ℚ) - 1) := by
        rw [Units.val_mul]; ring
      rw [e, map_add]
      exact Valuation.map_add_le _ (he ▸ h) hv
  simp only [h1, h2]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IdeleEmbeddingUniformizerOfSplitPlacePair
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange UpperTheory.ConvolutionTheory.R2.H
open private UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.val_iota UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.finrank_two from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe

private theorem e_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F)
    (x y : PlacesOver E v) (h : x ≠ y) : x.1.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  have hs := sum_ramificationIdx_mul_inertiaDeg E v
  rw [UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.finrank_two D] at hs
  have hpos : ∀ x : PlacesOver E v, 1 ≤ x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) := fun x =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have h1 := Finset.sum_le_sum_of_subset (f := fun x : PlacesOver E v => x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F))
    (Finset.subset_univ {x, y})
  rw [Finset.sum_pair h, hs] at h1
  have h2 := hpos x
  have h3 := hpos y
  exact Nat.eq_one_of_mul_eq_one_right (show x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) = 1 by omega)

private theorem map_sg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : P F) (w w' : P E)
    [hl : w.asIdeal.LiesOver v.asIdeal] [hl' : w'.asIdeal.LiesOver v.asIdeal] (hne : w ≠ w')
    (hu : ∀ u : P E, u.asIdeal.LiesOver v.asIdeal → u = w ∨ u = w') (x : Kv v) :
    adeleMap F E (sg v x) = sg w (completionMap v w x) + sg w' (completionMap v w' x) ∧
      ∀ a b, sg w a * sg w' b = 0 := by
  obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := sgLaws F v
  obtain ⟨-, -, hc₁, -, -, -, -, hs₁, -, -⟩ := sgLaws E w
  obtain ⟨-, -, hc₂, -, -, -, -, hs₂, -, -⟩ := sgLaws E w'
  refine ⟨Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_), fun a b => Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_)⟩
  · change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = (sg w _).1 + (sg w' _).1
    rw [(hs x).1, (hs₁ _).1, (hs₂ _).1, map_zero, add_zero]
  · change completionMap (below F u) u ((sg v x).2 (below F u)) = (sg w _).2 u + (sg w' _).2 u
    by_cases h : u = w
    · subst h
      have hb : below F u = v := (below_eq_iff _ _).2 hl
      subst hb
      rw [(hs₂ _).2 _ hne, add_zero]
      exact (congrArg _ (hc x)).trans (hc₁ _).symm
    by_cases h' : u = w'
    · subst h'
      have hb : below F u = v := (below_eq_iff _ _).2 hl'
      subst hb
      rw [(hs₁ _).2 _ h, zero_add]
      exact (congrArg _ (hc x)).trans (hc₂ _).symm
    · have hb : below F u ≠ v := fun hb => (hu u ((below_eq_iff _ _).1 hb)).elim h h'
      rw [(hs x).2 _ hb, map_zero, (hs₁ _).2 _ h, (hs₂ _).2 _ h', add_zero]
  · change (sg w a).1 * (sg w' b).1 = 0
    rw [(hs₁ _).1, zero_mul]
  · change (sg w a).2 u * (sg w' b).2 u = 0
    by_cases h : u = w
    · subst h
      rw [(hs₂ _).2 _ hne, mul_zero]
    · rw [(hs₁ _).2 _ h, zero_mul]

theorem UpperTheory.ideleEmbedding_uniformizer_of_split_place_pair :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w w' : H.P E), w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → H.SplitAt v w → H.SplitAt v w' →
          (∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') →
          ∀ ϖ : (H.Kv v)ˣ, H.IsU ϖ → ∃ (ϖ₁ : (H.Kv w)ˣ) (ϖ₂ : (H.Kv w')ˣ), H.IsU ϖ₁ ∧ H.IsU ϖ₂ ∧
            ideleEmbedding ℚ E (H.idl v ϖ) = H.idl w ϖ₁ * H.idl w' ϖ₂ := by
  intro E _ _ D v w w' hne hw hw' _ _ hall ϖ hϖ
  haveI hl : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  haveI hl' : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
  have hn : (⟨w, hl⟩ : PlacesOver E v) ≠ ⟨w', hl'⟩ := fun h => hne (congrArg Subtype.val h)
  obtain ⟨-, -, -, hi, -, -, -, -, -, -⟩ := sgLaws ℚ v
  obtain ⟨-, -, -, hi₁, -, -, -, -, -, -⟩ := sgLaws E w
  obtain ⟨-, -, -, hi₂, -, -, -, -, -, -⟩ := sgLaws E w'
  refine ⟨Units.map (completionMap v w : Kv v →* Kv w) ϖ, Units.map (completionMap v w' : Kv v →* Kv w') ϖ, ?_, ?_, Units.ext ?_⟩
  · change Valued.v (completionMap v w (ϖ : Kv v)) = _
    rw [UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.val_iota v w (e_one D v _ _ hn)]
    exact hϖ
  · change Valued.v (completionMap v w' (ϖ : Kv v)) = _
    rw [UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.val_iota v w' (e_one D v _ _ hn.symm)]
    exact hϖ
  · obtain ⟨h1, h2⟩ := map_sg v w w' hne (fun u hu => hall u (HeightOneSpectrum.ext hu.over.symm)) ((ϖ : Kv v) - 1)
    change adeleMap ℚ E ((idl v ϖ : (A ℚ)ˣ) : A ℚ) = _
    rw [Units.val_mul, hi, hi₁, hi₂, map_add, map_one, h1, map_sub, map_sub, map_one, map_one, add_mul, mul_add, mul_add, h2]
    simp only [one_mul, mul_one, add_zero, Units.coe_map, MonoidHom.coe_coe]
    abel
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegralEvenPowerGaussianMulAbsRpow
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private noncomputable def gg (a : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (2 * a - 1) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ))

private theorem gg_int {a : ℂ} (ha : 0 < a.re) : IntegrableOn (gg a) (Set.Ioi 0) ∧
    ∫ r in Set.Ioi (0 : ℝ), gg a r = (Real.pi : ℂ) ^ (-a) * Complex.Gamma a / 2 := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * Complex.exp (-((Real.pi : ℝ) * t))
  have key : ∀ x ∈ Set.Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • F (x ^ (2 : ℝ)) = 2 * gg a x := fun x hx => by
    have hx' : (0 : ℝ) < x := hx
    have h0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx'.ne'
    have h1 : ((x ^ (2 : ℝ) : ℝ) : ℂ) ^ (a - 1) = (x : ℂ) ^ (2 * (a - 1)) := by
      rw [Real.rpow_two, sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx'.le hx'.le, ← Complex.cpow_add _ _ h0]
      congr 1
      ring
    have h2 : (x : ℂ) ^ (2 * a - 1) = x * (x : ℂ) ^ (2 * (a - 1)) := by
      rw [show 2 * a - 1 = 1 + 2 * (a - 1) by ring, Complex.cpow_add _ _ h0, Complex.cpow_one]
    simp only [F, gg, h1, h2, Complex.real_smul]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, abs_two]
    push_cast
    ring_nf
  have hF : IntegrableOn F (Set.Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (a - 1)) 0 Real.pi_pos).2
      (by simpa using Complex.GammaIntegral_convergent ha)
    refine (h.const_mul ((Real.pi : ℂ) ^ (a - 1))⁻¹).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : (Real.pi : ℂ) ^ (a - 1) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, Real.pi_ne_zero]
    simp only [F]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (le_of_lt ht)]
    push_cast
    field_simp
  have h1 := (integrableOn_Ioi_comp_rpow_iff F (p := 2) two_ne_zero).2 hF
  have h2 := integral_comp_rpow_Ioi F (p := 2) two_ne_zero
  refine ⟨?_, ?_⟩
  · refine ((h1.congr_fun key measurableSet_Ioi).const_mul (2 : ℂ)⁻¹).congr (ae_of_all _ fun x => ?_)
    simp
  · rw [setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul,
      Complex.integral_cpow_mul_exp_neg_mul_Ioi ha Real.pi_pos] at h2
    rw [eq_div_iff two_ne_zero, mul_comm, h2, Complex.cpow_neg, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm)]

theorem UpperTheory.integral_even_power_gaussian_mul_abs_rpow :
    ∀ (e : ℕ) (s : ℂ), 0 < s.re → Integrable (fun r : ℝ => (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1)) ∧ ∫ r : ℝ, (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1) = (Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e) := by
  intro e s hs
  have ha : 0 < (s + e).re := by simp; positivity
  have hf : ∀ r : ℝ, r ≠ 0 → (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1) =
      gg (s + e) |r| := fun r hr => by
    have h1 : ((|r| : ℝ) : ℂ) ≠ 0 := by simpa using hr
    have h2 : (r : ℂ) ^ (2 * e) = ((|r| : ℝ) : ℂ) ^ ((2 * e : ℕ) : ℂ) := by
      rw [Complex.cpow_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_pow, pow_mul, pow_mul, sq_abs]
    rw [h2, gg, mul_right_comm, ← Complex.cpow_add _ _ h1, sq_abs]
    congr 2
    push_cast
    ring
  have hae : (fun r : ℝ => (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1)) =ᵐ[volume]
      fun r => gg (s + e) |r| := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with r hr using hf r hr
  obtain ⟨hi, hv⟩ := gg_int ha
  have hp : IntegrableOn (fun r => gg (s + e) |r|) (Set.Ioi 0) :=
    hi.congr_fun (fun r hr => by rw [abs_of_pos hr]) measurableSet_Ioi
  have hn : IntegrableOn (fun r => gg (s + e) |r|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    have m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hp
  have hall : Integrable fun r => gg (s + e) |r| := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hn.union hp
  refine ⟨hall.congr hae.symm, ?_⟩
  have e1 : ∫ r in Set.Ioi (0 : ℝ), gg (s + e) |r| = ∫ r in Set.Ioi (0 : ℝ), gg (s + e) r :=
    setIntegral_congr_fun measurableSet_Ioi fun r hr => by rw [abs_of_pos hr]
  have e2 : ∫ r in Set.Iic (0 : ℝ), gg (s + e) |r| = ∫ r in Set.Ioi (0 : ℝ), gg (s + e) |r| := by
    rw [← neg_zero, ← integral_comp_neg_Iic]
    simp
  rw [integral_congr_ae hae, ← intervalIntegral.integral_Iic_add_Ioi hn hp, e2, e1, hv]
  ring
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegralUnfoldedIntegrandEqZetaIntegral
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem fub3 {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (κ : Measure Z) [SFinite μ] [SFinite ν] [SFinite κ]
    (f : X → Z → ℂ) (g : Y → Z → ℂ)
    (h : Integrable (fun q : X × Y × Z => f q.1 q.2.2 * g q.2.1 q.2.2) (μ.prod (ν.prod κ))) :
    ∫ q : X × Y × Z, f q.1 q.2.2 * g q.2.1 q.2.2 ∂(μ.prod (ν.prod κ)) =
      ∫ k, ∫ y, f y k * ∫ z, g z k ∂ν ∂μ ∂κ := by
  have hp : MeasurePreserving (MeasurableEquiv.prodAssoc : (X × Y) × Z ≃ᵐ X × Y × Z)
      ((μ.prod ν).prod κ) (μ.prod (ν.prod κ)) := measurePreserving_prodAssoc μ ν κ
  have h2 := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 h
  rw [← hp.integral_comp' (fun q : X × Y × Z => f q.1 q.2.2 * g q.2.1 q.2.2)]
  refine (integral_prod_symm _ h2).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  change ∫ x : X × Y, f x.1 k * g x.2 k ∂(μ.prod ν) = ∫ y, f y k * ∫ z, g z k ∂ν ∂μ
  rw [integral_prod_mul (fun y => f y k) (fun z => g z k), integral_mul_const]

theorem UpperTheory.integral_unfoldedIntegrand_eq_zetaIntegral :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (M₀ : Meas ℚ) (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ),
        Integrable (Un.Hh D χ φ Φ s) ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) →
        ∫ q, Un.Hh D χ φ Φ s q ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) = Zu D M₀ χ φ Φ s := by
  intro E _ _ D χ φ M₀ Φ s h
  haveI := M₀.prob
  haveI : SFinite (ideleMeasure ℚ) := inferInstance
  exact fub3 (ideleMeasure ℚ) (ideleMeasure ℚ) M₀.κ
    (fun y k => Wo D φ (em E (aE y * gl k)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1))
    (fun z k => (Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s)) h
end

