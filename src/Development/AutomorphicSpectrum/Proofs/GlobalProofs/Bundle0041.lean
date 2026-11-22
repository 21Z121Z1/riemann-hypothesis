import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0009
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV

theorem fibre_mass_eq {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace R] [MeasurableSpace R]
    (μ : Measure V) (ν : Measure R) (q : V → R) (hq : Measurable q) (B : Set R) (fib : R → Measure V)
    (h : IsFibreFamily μ q id Set.univ ν B fib) {A : Set V} {S : Set R} (hA : MeasurableSet A)
    (hS : MeasurableSet S) : μ (A ∩ q ⁻¹' S) = ∫⁻ s in S, fib s A ∂ν := by
  obtain ⟨h1, h2, -⟩ := h
  have hT : MeasurableSet (A ∩ q ⁻¹' S) := hA.inter (hq hS)
  have e := h2 ((A ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator hT)
  simp only [Measure.restrict_univ, lintegral_indicator_one hT] at e
  rw [e, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae : ∀ᵐ x ∂(fib b), q x = b := by
    refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx hx'.1
  by_cases hb : b ∈ S
  · rw [Set.indicator_of_mem hb]
    refine measure_congr ?_
    filter_upwards [hae] with x hx
    refine propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show q x ∈ S
    rwa [hx]
  · rw [Set.indicator_of_notMem hb]
    refine measure_mono_null (t := {x | ¬ q x = b}) ?_ hae
    intro x hx hxb
    apply hb
    rw [← hxb]
    exact hx.2

theorem tendsto_mean {R : Type} [TopologicalSpace R] [MeasurableSpace R] (ν : Measure R) (G : R → ℝ≥0∞) (c : R)
    (hG : ContinuousAt (fun s => (G s).toReal) c) (hfin : ∀ᶠ s in nhds c, G s ≠ ⊤) (S : ℕ → Set R)
    (hS : ∀ k, MeasurableSet (S k)) (hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets)
    (hpos : ∀ k, ν (S k) ≠ 0) (htop : ∀ k, ν (S k) ≠ ⊤) :
    Filter.Tendsto (fun k => (∫⁻ s in S k, G s ∂ν).toReal / (ν (S k)).toReal) Filter.atTop
      (nhds (G c).toReal) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hN : {s | G s ≠ ⊤ ∧ dist (G s).toReal (G c).toReal < ε / 2} ∈ nhds c :=
    Filter.inter_mem hfin (hG.eventually (Metric.ball_mem_nhds _ (half_pos hε)))
  have hev := hl.eventually (Filter.eventually_smallSets_subset.2 hN)
  filter_upwards [hev] with k hk
  set g := (G c).toReal with hg
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  set n := ν (S k) with hn
  have hnr : 0 < n.toReal := ENNReal.toReal_pos (hpos k) (htop k)
  have hup : ∫⁻ s in S k, G s ∂ν ≤ ENNReal.ofReal (g + ε / 2) * n := by
    rw [hn, ← setLIntegral_const]
    refine setLIntegral_mono' (hS k) fun s hs => ?_
    obtain ⟨h1, h2⟩ := hk hs
    rw [← ENNReal.ofReal_toReal h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_lt.1 (Real.dist_eq _ _ ▸ h2)).2
    linarith
  have hlo : ENNReal.ofReal (g - ε / 2) * n ≤ ∫⁻ s in S k, G s ∂ν := by
    rw [hn, ← setLIntegral_const]
    refine setLIntegral_mono' (hS k) fun s hs => ?_
    obtain ⟨h1, h2⟩ := hk hs
    rw [← ENNReal.ofReal_toReal h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_lt.1 (Real.dist_eq _ _ ▸ h2)).1
    linarith
  have hfinU : ENNReal.ofReal (g + ε / 2) * n ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htop k)
  have hup' : (∫⁻ s in S k, G s ∂ν).toReal ≤ (g + ε / 2) * n.toReal := by
    have := ENNReal.toReal_mono hfinU hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hlo' : (g - ε / 2) * n.toReal ≤ (∫⁻ s in S k, G s ∂ν).toReal := by
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hfinU hup) hlo
    rw [ENNReal.toReal_mul] at this
    refine le_trans ?_ this
    refine mul_le_mul_of_nonneg_right ?_ hnr.le
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : g - ε / 2 ≤ (∫⁻ s in S k, G s ∂ν).toReal / n.toReal := (le_div_iff₀ hnr).2 hlo'
    linarith
  · have : (∫⁻ s in S k, G s ∂ν).toReal / n.toReal ≤ g + ε / 2 := (div_le_iff₀ hnr).2 hup'
    linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV in

theorem GlobalTheory.CompanionTheory.Hypotheses₂.OneV.avgV_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 2 < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J 1 (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv 1) mv → ∀ c : Fv F v, c ≠ 0 → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ U : ℕ → Set (Fv F v), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : Fv F v) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : Fv F v)).smallSets → (∀ k, MeasurableSet (A ∩ {X | c - qR (Fv F v) σ J (X 0) ∈ U k}) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M (A ∩ {X | c - qR (Fv F v) σ J (X 0) ∈ U k}) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M (A ∩ {X | c - qR (Fv F v) σ J (X 0) ∈ U k})).toReal / (lv (U k)).toReal) Filter.atTop (nhds (mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ c) A).toReal) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b v lv hlv mv hmv c hc A hAc hAo U hU hUt
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  haveI := hlv.1
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW 1 M
  obtain ⟨n1, n2⟩ := GlobalTheory.CompanionTheory.SW.NullV.null_nonunits F E σ hσ M J hJ (by omega) v
    (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M) lv (hW 1 M) hlv.1
  have hmv' : GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J 1 (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv 1 M)
      (lv.map (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ)) mv := by
    rw [(GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hσ (Fv F v) d b).2.2 lv hlv.1]
    exact hmv
  have FF := GlobalTheory.CompanionTheory.SW.isFibreFamily_length F E σ hσ M J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) _ lv
    (hW 1 M) hlv.1 n1 n2 mv hmv'
  have hqc : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => qR (Fv F v) σ J (X 0) :=
    GlobalTheory.CompanionTheory.SW.LenFib.continuous_qR (Fv F v) hσ J
  have hAm : MeasurableSet A := hAo.measurableSet
  have hAcl : IsClosed A := hAc.isClosed

  let S : ℕ → Set (Fv F v) := fun k => {s | c - s ∈ U k}
  have hSo : ∀ k, IsOpen (S k) := fun k => (hU k).2.1.preimage (continuous_const.sub continuous_id)
  have hSm : ∀ k, MeasurableSet (S k) := fun k => (hSo k).measurableSet
  have hSc : ∀ k, c ∈ S k := fun k => by
    show c - c ∈ U k
    rw [sub_self]
    exact (hU k).2.2
  haveI : lv.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular lv
  have hSU : ∀ k, lv (S k) = lv (U k) := fun k =>
    (Measure.measurePreserving_sub_left lv c).measure_preimage (hU k).2.1.measurableSet.nullMeasurableSet
  have hpos : ∀ k, lv (S k) ≠ 0 := fun k => (hSo k).measure_ne_zero lv ⟨c, hSc k⟩
  have htop : ∀ k, lv (S k) ≠ ⊤ := fun k => by
    rw [hSU]
    exact (hU k).1.measure_lt_top.ne
  have hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have hcont : Filter.Tendsto (fun u : Fv F v => c - u) (nhds 0) (nhds c) := by
      have : Continuous fun u : Fv F v => c - u := continuous_const.sub continuous_id
      simpa using this.tendsto 0
    have h0 := (Filter.tendsto_smallSets_iff.1 hUt) _ (hcont ht)
    filter_upwards [h0] with k hk s hs
    have := hk hs
    simpa using this

  let φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ := A.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hAo.frontier_eq, hAcl.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hAc fun x hx => ?_
    exact Set.indicator_of_notMem hx _
  obtain ⟨hI, hC⟩ := FF.2.2 φ hφc hφs (Set.subset_univ _)
  have hint : ∀ s, ∫ X, φ X ∂(mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s)) =
      (mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A).toReal := fun s => by
    simp [φ, integral_indicator hAm, Measure.real]
  have hUn : {s : Fv F v | IsUnit s} ∈ nhds c := by
    have : {s : Fv F v | IsUnit s} = {0}ᶜ := by
      ext s
      simp
    rw [this]
    exact isOpen_compl_singleton.mem_nhds hc
  have hG : ContinuousAt (fun s => (mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A).toReal) c := by
    have h := hC.continuousAt (x := c) hUn
    simpa only [hint] using h
  have hfin : ∀ᶠ s in nhds c, mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A ≠ ⊤ := by
    filter_upwards [hUn] with s hs
    have h := hI s hs
    rw [integrable_indicator_iff hAm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  refine ⟨fun k => ?_, ?_⟩
  · have hO : IsOpen (A ∩ {X | c - qR (Fv F v) σ J (X 0) ∈ U k}) :=
      hAo.inter ((hU k).2.1.preimage (continuous_const.sub hqc))
    exact ⟨hO.measurableSet, ne_top_of_le_ne_top hAc.measure_lt_top.ne (measure_mono Set.inter_subset_left)⟩
  · have key := tendsto_mean lv (fun s => mv (GlobalTheory.CompanionTheory.SW.hermScal (Fv F v) σ s) A) c hG hfin S hSm hl hpos htop
    refine key.congr fun k => ?_
    rw [hSU k, ← fibre_mass_eq _ lv _ hqc.measurable _ _ FF hAm (hSm k)]
    rfl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

section Abstract

variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

theorem integral_indicator_char_of_trivial (μ : Measure G) (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (χ : G → ℂ) (h1 : ∀ x ∈ H, χ x = 1) :
    ∫ x, (H : Set G).indicator χ x ∂μ = ((μ (H : Set G)).toReal : ℂ) := by
  rw [integral_indicator hH, setIntegral_congr_fun hH (g := fun _ => (1 : ℂ)) (fun x hx => h1 x hx)]
  simp [Measure.real]

theorem integral_indicator_char_of_ne (μ : Measure G) [μ.IsAddLeftInvariant] (H : AddSubgroup G)
    (χ : G → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) {h : G} (hh : h ∈ H) (hne : χ h ≠ 1) :
    ∫ x, (H : Set G).indicator χ x ∂μ = 0 := by
  have key : ∀ x, (H : Set G).indicator χ (x + h) = (H : Set G).indicator χ x * χ h := by
    intro x
    by_cases hx : x ∈ H
    · have hxh : x + h ∈ H := H.add_mem hx hh
      rw [Set.indicator_of_mem (by exact hxh), Set.indicator_of_mem (by exact hx), hχ]
    · have hxh : x + h ∉ H := fun hc => hx (by simpa using H.sub_mem hc hh)
      rw [Set.indicator_of_notMem (by exact hxh), Set.indicator_of_notMem (by exact hx), zero_mul]
  have h2 := integral_add_right_eq_self (μ := μ) ((H : Set G).indicator χ) h
  simp only [key] at h2
  rw [integral_mul_const] at h2
  have h3 : (∫ x, (H : Set G).indicator χ x ∂μ) * (χ h - 1) = 0 := by
    rw [mul_sub, h2, mul_one, sub_self]
  exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hne)

end Abstract

variable {F : Type} [Field F] [NumberField F]

def psiF (ψ : AddChar (AF F) ℂ) (y : Af F) : ℂ := ψ (pairA F 0 y)

def annV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) : Set (Fv F v) :=
  {t | ∀ s ∈ U, psiV F ψ v (s * t) = 1}

def annF (ψ : AddChar (AF F) ℂ) (B : Set (Af F)) : Set (Af F) :=
  {b | ∀ y ∈ B, psiF ψ (y * b) = 1}

def fouInf (ψ : AddChar (AF F) ℂ) (lam : Measure (Ainf F)) (ρ : Ainf F → ℝ) (t : Ainf F) : ℂ :=
  ∫ x, (ρ x : ℂ) * psiInf F ψ (x * t) ∂lam

theorem psiF_add (ψ : AddChar (AF F) ℂ) (x y : Af F) : psiF ψ (x + y) = psiF ψ x * psiF ψ y := by
  have h : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := Prod.ext (add_zero (0 : Ainf F)).symm rfl
  rw [psiF, h, AddChar.map_add_eq_mul]
  rfl

theorem psiF_zero (ψ : AddChar (AF F) ℂ) : psiF ψ 0 = 1 := by
  have h : pairA F 0 (0 : Af F) = 0 := rfl
  rw [psiF, h, AddChar.map_zero_eq_one]

theorem psiF_singleV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    psiF ψ (singleV F v s) = psiV F ψ v s := rfl

theorem psi_pairA (ψ : AddChar (AF F) ℂ) (x : Ainf F) (y : Af F) :
    ψ (pairA F x y) = psiInf F ψ x * psiF ψ y := by
  have h : pairA F x y = pairA F x 0 + pairA F 0 y :=
    Prod.ext (add_zero x).symm (zero_add y).symm
  rw [h, AddChar.map_add_eq_mul]
  rfl

theorem psiV_zero (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : psiV F ψ v 0 = 1 := by
  classical
  have h : singleV F v (0 : Fv F v) = 0 := RestrictedProduct.single_zero _ v
  rw [← psiF_singleV, h, psiF_zero]

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y :=
  GlobalTheory.CompanionTheory.SW.PiV.psiV_add ψ v x y

theorem psiV_neg_of_eq_one (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) {x : Fv F v}
    (hx : psiV F ψ v x = 1) : psiV F ψ v (-x) = 1 := by
  have h := psiV_add ψ v (-x) x
  rw [neg_add_cancel, psiV_zero, hx, mul_one] at h
  exact h.symm

def annS (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) :
    AddSubgroup (Fv F v) where
  carrier := annV ψ v U
  add_mem' := by
    intro a b ha hb s hs
    rw [mul_add, psiV_add, ha s hs, hb s hs, one_mul]
  zero_mem' := by
    intro s _
    rw [mul_zero, psiV_zero]
  neg_mem' := by
    intro a ha s hs
    rw [mul_neg]
    exact psiV_neg_of_eq_one ψ v (ha s hs)

theorem coe_annS (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) :
    (annS ψ v U : Set (Fv F v)) = annV ψ v U := rfl

def boxS (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fv F v)) :
    AddSubgroup (Af F) where
  carrier := Coef.boxA S fun v => (U v : Set (Fv F v))
  add_mem' := by
    intro a b ha hb
    exact ⟨fun v hv => (U v).add_mem (ha.1 v hv) (hb.1 v hv),
      fun v hv => add_mem (ha.2 v hv) (hb.2 v hv)⟩
  zero_mem' := ⟨fun v _ => (U v).zero_mem, fun v _ => zero_mem _⟩
  neg_mem' := by
    intro a ha
    exact ⟨fun v hv => (U v).neg_mem (ha.1 v hv),
      fun v hv => neg_mem (ha.2 v hv)⟩

theorem coe_boxS (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fv F v)) :
    (boxS S U : Set (Af F)) = Coef.boxA S fun v => (U v : Set (Fv F v)) := rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableSetIntF
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

theorem placesCountable (F : Type) [Field F] [NumberField F] : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have : Countable (𝓞 F) := inferInstanceAs (Countable {x : F // x ∈ integralClosure ℤ F})
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    exact ⟨s, hs⟩
  have : Countable (Ideal (𝓞 F)) := hs.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h)

theorem measurableSet_intF (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (intF (F := F) S) := by
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI := placesCountable F
  have hset : intF (F := F) S = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S,
      {y : Af F | y v ∈ v.adicCompletionIntegers F} := by
    ext y; simp [intF]
  rw [hset]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hcont : Continuous fun y : Af F => y v := RestrictedProduct.continuous_eval v
  exact (hO.preimage hcont).measurableSet

theorem coefS_tendsto (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (db : Measure (AF F))
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (hI : Integrable (starT σ J ψ dx Φ) db) (t : F) :
    Filter.Tendsto (fun S => Coef.coefS σ J ψ dx db Φ t S) Filter.atTop (nhds (coefT σ J ψ dx db Φ t)) := by
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI := placesCountable F
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  have hchar : AEStronglyMeasurable (fun b : AF F => ψ (-(algebraMap F (AF F) t * b))) db :=
    (hψc.comp (by fun_prop)).aestronglyMeasurable
  have hf : AEStronglyMeasurable
      (fun b : AF F => starT σ J ψ dx Φ b * ψ (-(algebraMap F (AF F) t * b))) db :=
    hI.aestronglyMeasurable.mul hchar
  have hsnd : Measurable (fun b : AF F => sndA F b) := by
    have : Continuous (fun b : AF F => sndA F b) := continuous_snd
    exact this.measurable
  unfold coefS coefT
  refine tendsto_integral_filter_of_dominated_convergence (fun b => ‖starT σ J ψ dx Φ b‖) ?_ ?_ hI.norm ?_
  · refine Filter.Eventually.of_forall fun S => ?_
    have hind : Measurable (fun b : AF F => (intF (F := F) S).indicator (fun _ => (1 : ℂ)) (sndA F b)) :=
      (measurable_const.indicator (measurableSet_intF F S)).comp hsnd
    exact hind.aestronglyMeasurable.mul hf
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun b => ?_
    have h1 : ‖(intF (F := F) S).indicator (fun _ => (1 : ℂ)) (sndA F b)‖ ≤ 1 := by
      by_cases h : sndA F b ∈ intF (F := F) S <;> simp [h]
    rw [norm_mul, norm_mul, hψn, mul_one]
    exact (mul_le_of_le_one_left (norm_nonneg _) h1)
  · refine Filter.Eventually.of_forall fun b => ?_
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ (sndA F b) v ∈ v.adicCompletionIntegers F}.Finite :=
      (sndA F b).2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    have hmem : sndA F b ∈ intF (F := F) S := by
      intro v hv
      by_contra hcon
      exact hv (hS (hfin.mem_toFinset.2 hcon))
    simp [hmem]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end

