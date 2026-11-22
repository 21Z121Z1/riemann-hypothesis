import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariant
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import GroundTheory.GlobalFields.TateThesis.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicAnnihilatorBoxProduct
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

private theorem integral_indicator_mul_char_of_trivial {K : Type} [CommRing K] [MeasurableSpace K]
    (μ : Measure K) (p : K → ℂ) (S : AddSubgroup K) (hSm : MeasurableSet (S : Set K)) (y : K)
    (h : ∀ s ∈ S, p (s * y) = 1) :
    ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = ((μ (S : Set K)).toReal : ℂ) := by
  have hfun : (fun x => (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y)) =
      (S : Set K).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ (S : Set K)
    · rw [Set.indicator_of_mem hx, one_mul, h x hx]
    · rw [Set.indicator_of_notMem hx, zero_mul]
  rw [hfun, integral_indicator_const _ hSm, measureReal_def, Complex.real_smul, mul_one]

private theorem integral_indicator_mul_char_eq_zero {K : Type} [CommRing K] [MeasurableSpace K] [MeasurableAdd K]
    (μ : Measure K) [μ.IsAddLeftInvariant] (p : K → ℂ) (hadd : ∀ x y, p (x + y) = p x * p y)
    (S : AddSubgroup K) (y : K) (h : ∃ s ∈ S, p (s * y) ≠ 1) :
    ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = 0 := by
  obtain ⟨s, hs, hps⟩ := h
  have hI : ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ =
      p (s * y) * ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ := by
    rw [← integral_const_mul, ← integral_add_left_eq_self
      (fun x => (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y)) s]
    congr 1
    funext x
    beta_reduce
    by_cases hx : x ∈ (S : Set K)
    · have hsx : s + x ∈ (S : Set K) := (S.add_mem_cancel_left hs).mpr hx
      rw [Set.indicator_of_mem hsx, Set.indicator_of_mem hx, add_mul, hadd]
      ring
    · have hsx : s + x ∉ (S : Set K) := fun h' => hx ((S.add_mem_cancel_left hs).mp h')
      rw [Set.indicator_of_notMem hsx, Set.indicator_of_notMem hx]
      ring
  have h1 : (1 - p (s * y)) * ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp h1 with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hps
  · exact h0

theorem ann_core {K : Type} [CommRing K] [TopologicalSpace K] [T2Space K] [MeasurableSpace K] [MeasurableAdd K]
    (μ : Measure K) (p : K → ℂ) (hadd : ∀ x y, p (x + y) = p x * p y)
    (hSD : SelfDual μ (fun s t => p (s * t)))
    (U A B : AddSubgroup K) (hUc : IsCompact (U : Set K)) (hUo : IsOpen (U : Set K))
    (hUm : MeasurableSet (U : Set K)) (hAm : MeasurableSet (A : Set K)) (hAf : μ (A : Set K) ≠ ⊤)
    (hA : ∀ y, y ∈ A ↔ ∀ s ∈ U, p (s * y) = 1)
    (hB : ∀ z, z ∈ B ↔ ∀ s ∈ A, p (s * z) = 1) :
    B = U ∧ (μ (U : Set K)).toReal * (μ (A : Set K)).toReal = 1 := by
  obtain ⟨hHaar, hinv⟩ := hSD
  have hp0 : p 0 = 1 := by simpa using (hA 0).mp A.zero_mem 0 U.zero_mem
  have hΦc : Continuous ((U : Set K).indicator (fun _ => (1 : ℂ))) :=
    IsClopen.continuous_indicator ⟨hUc.isClosed, hUo⟩ continuous_const
  have hΦs : HasCompactSupport ((U : Set K).indicator (fun _ => (1 : ℂ))) :=
    HasCompactSupport.intro hUc (fun x hx => Set.indicator_of_notMem hx _)
  have hFT : ∀ y, ∫ x, (U : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ =
      (A : Set K).indicator (fun _ => ((μ (U : Set K)).toReal : ℂ)) y := by
    intro y
    by_cases h : ∀ s ∈ U, p (s * y) = 1
    · rw [integral_indicator_mul_char_of_trivial μ p U hUm y h,
        Set.indicator_of_mem (show y ∈ (A : Set K) from (hA y).mpr h)]
    · push_neg at h
      rw [integral_indicator_mul_char_eq_zero μ p hadd U y h,
        Set.indicator_of_notMem (show y ∉ (A : Set K) from fun h' => by
          obtain ⟨s, hs, hps⟩ := h
          exact hps ((hA y).mp h' s hs))]
  have hint : Integrable (fun y => ∫ x, (U : Set K).indicator (fun _ => (1 : ℂ)) x *
      (fun s t => p (s * t)) x y ∂μ) μ := by
    simp only [hFT]
    exact (integrable_indicator_iff hAm).mpr (integrableOn_const hAf)
  have key : ∀ z, ((μ (U : Set K)).toReal : ℂ) *
      ∫ y, (A : Set K).indicator (fun _ => (1 : ℂ)) y * p (y * z) ∂μ =
      (U : Set K).indicator (fun _ => (1 : ℂ)) (-z) := by
    intro z
    rw [← integral_const_mul, ← hinv _ hΦc hΦs hint z]
    congr 1
    funext y
    beta_reduce
    rw [hFT y]
    by_cases hy : y ∈ (A : Set K)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      ring
  have h0 := key 0
  have hc0 : ∀ s ∈ A, p (s * 0) = 1 := fun s _ => by rw [mul_zero, hp0]
  rw [integral_indicator_mul_char_of_trivial μ p A hAm 0 hc0, neg_zero,
    Set.indicator_of_mem (show (0 : K) ∈ (U : Set K) from U.zero_mem)] at h0
  have hprod : (μ (U : Set K)).toReal * (μ (A : Set K)).toReal = 1 := by exact_mod_cast h0
  refine ⟨?_, hprod⟩
  ext z
  rw [hB z]
  have hz := key z
  constructor
  · intro h
    rw [integral_indicator_mul_char_of_trivial μ p A hAm z h, h0] at hz
    by_contra hzU
    rw [Set.indicator_of_notMem (show -z ∉ (U : Set K) from fun h' => hzU (by simpa using U.neg_mem h'))] at hz
    exact one_ne_zero hz
  · intro hzU
    by_contra h
    push_neg at h
    rw [integral_indicator_mul_char_eq_zero μ p hadd A z h, mul_zero,
      Set.indicator_of_mem (show -z ∈ (U : Set K) from U.neg_mem hzU)] at hz
    exact zero_ne_one hz

theorem localDual : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (c : ℝ≥0), GlobalTheory.CompanionTheory.SW.IsStdV v lam → SelfDual (c • lam) (fun s t => psiV F ψ v (s * t)) → ∀ U : AddSubgroup (Fv F v), IsCompact (U : Set (Fv F v)) → IsOpen (U : Set (Fv F v)) → annV ψ v (annV ψ v U) = U ∧ IsCompact (annV ψ v U) ∧ IsOpen (annV ψ v U) ∧ (c : ℝ) ^ 2 * (lam U).toReal * (lam (annV ψ v U)).toReal = 1 := by
  intro F _ _ ψ hψ v lam c _ hSD U hUc hUo
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hc, y, hy⟩ := (GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v
  have ha := psiV_add ψ v
  have h0 := psiV_zero ψ v
  have hinv := hSD.1
  have hcomp : IsCompact (annV ψ v U) := GlobalTheory.CompanionTheory.SW.PiV.ann_isCompact hc h0 hy U hUo
  have hnear : {x | ‖psiV F ψ v x - 1‖ < 1 / 2} ∈ nhds (0 : Fv F v) :=
    (isOpen_lt (hc.sub continuous_const).norm continuous_const).mem_nhds (by
      change ‖psiV F ψ v 0 - 1‖ < 1 / 2
      rw [h0]
      norm_num)
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_subset _ hnear
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_of_isCompact _ hUc
  have htriv : ∀ x ∈ GlobalTheory.CompanionTheory.SW.PiV.ball v m, psiV F ψ v x = 1 := fun x hx =>
    char_eq_one_of_near (GlobalTheory.CompanionTheory.SW.PiV.ball v m) _ h0 ha (fun x hx => hm hx) hx
  have hsub : (GlobalTheory.CompanionTheory.SW.PiV.ball v (m - n) : Set (Fv F v)) ⊆ annV ψ v U := by
    intro t ht s hs
    refine htriv _ ?_
    rw [GlobalTheory.CompanionTheory.SW.PiV.mem_ball, map_mul]
    calc Valued.v s * Valued.v t ≤ WithZero.exp n * WithZero.exp (m - n) :=
          mul_le_mul' (hn hs) ht
      _ = WithZero.exp m := by rw [← WithZero.exp_add, add_sub_cancel]
  have hopen : IsOpen (annV ψ v U) :=
    AddSubgroup.isOpen_of_mem_nhds (annS ψ v U) (g := 0)
      (Filter.mem_of_superset ((GlobalTheory.CompanionTheory.SW.PiV.ball_isOpen (m - n)).mem_nhds
        (GlobalTheory.CompanionTheory.SW.PiV.ball v (m - n)).zero_mem) hsub)
  have hcore := ann_core (c • lam) (psiV F ψ v) ha hSD U (annS ψ v U) (annS ψ v (annV ψ v U))
    hUc hUo hUo.measurableSet hopen.measurableSet hcomp.measure_lt_top.ne
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  refine ⟨?_, hcomp, hopen, ?_⟩
  · rw [← coe_annS, hcore.1]
  · have h5 := hcore.2
    rw [coe_annS] at h5
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal] at h5
    rw [← h5]
    ring

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanForm
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Glob.CharAF

theorem real_char (f : AddChar ℝ ℂ) (hf : Continuous f) (hn : ∀ t, ‖f t‖ = 1) :
    ∃ α : ℝ, ∀ t : ℝ, f t = Complex.exp (2 * Real.pi * Complex.I * ((α * t : ℝ) : ℂ)) := by
  have hne : ∀ t, f t ≠ 0 := fun t h => by
    have := hn t
    simp [h] at this
  let χ : AddChar ℝ ℂˣ :=
    { toFun := fun t => Units.mk0 (f t) (hne t)
      map_zero_eq_one' := Units.ext (by simp)
      map_add_eq_mul' := fun a b => Units.ext (by simp [AddChar.map_add_eq_mul]) }
  have hχ : Continuous χ := Units.isEmbedding_val₀.continuous_iff.2 hf
  obtain ⟨s, hs, -⟩ := GroundTheory.Global.existsUnique_addChar_real_units χ hχ
  have hs' : ∀ t : ℝ, f t = Complex.exp (s * t) := hs
  have hre : s.re = 0 := by
    have h1 := hn 1
    rw [hs' 1, Complex.norm_exp] at h1
    simpa using h1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨s.im / (2 * Real.pi), fun t => ?_⟩
  rw [hs' t]
  congr 1
  have hs2 : s = (s.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  push_cast
  rw [hs2]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re]
  field_simp
  simp
  ring

theorem pi_char {ι : Type} [Fintype ι] [DecidableEq ι] (g : AddChar (ι → ℝ) ℂ) (hg : Continuous g)
    (hn : ∀ x, ‖g x‖ = 1) :
    ∃ α : ι → ℝ, ∀ x, g x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, α w * x w : ℝ) : ℂ)) := by
  have key : ∀ w, ∃ α : ℝ, ∀ t : ℝ, g (Pi.single w t) =
      Complex.exp (2 * Real.pi * Complex.I * ((α * t : ℝ) : ℂ)) := fun w =>
    real_char (g.compAddMonoidHom (AddMonoidHom.single (fun _ => ℝ) w))
      (show Continuous (fun t : ℝ => g (Pi.single w t)) from hg.comp (continuous_pi fun j => by
        by_cases h : j = w
        · subst h
          simp only [Pi.single_eq_same]
          exact continuous_id
        · simpa [Pi.single_apply, h] using continuous_const)) (fun t => hn _)
  choose α hα using key
  refine ⟨α, fun x => ?_⟩
  have hx : x = ∑ w, Pi.single w (x w) := (Finset.univ_sum_single x).symm
  have hsum : ∀ s : Finset ι, g (∑ w ∈ s, Pi.single w (x w)) = ∏ w ∈ s, g (Pi.single w (x w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hw ih => rw [Finset.sum_insert hw, Finset.prod_insert hw, AddChar.map_add_eq_mul, ih]
  conv_lhs => rw [hx]
  rw [hsum, Finset.prod_congr rfl fun w _ => hα w (x w), ← Complex.exp_sum, ← Finset.mul_sum]
  push_cast
  rfl

theorem places_indep {F : Type} [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (β : InfinitePlace F → ℝ)
    (h : ∀ c : F, ∑ w, β w * ρ w c = 0) : β = 0 := by
  have hinj : Function.Injective (fun w => ((ρ w : F →+* ℝ) : F →* ℝ)) := by
    intro w w' hww
    have h1 : w.embedding = w'.embedding := by
      ext x
      rw [← hρ, ← hρ]
      exact congrArg (fun f : F →* ℝ => ((f x : ℝ) : ℂ)) hww
    rw [← InfinitePlace.mk_embedding w, h1, InfinitePlace.mk_embedding]
  have hli := (linearIndependent_monoidHom F ℝ).comp _ hinj
  funext w
  refine Fintype.linearIndependent_iff.1 hli β ?_ w
  funext c
  simpa using h c

theorem exists_dual {F : Type} [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    (htr : ∀ z : F, ∑ w, ρ w z = ((Algebra.trace ℚ F z : ℚ) : ℝ))
    (α : InfinitePlace F → ℝ) (N : ℕ) (hN : 0 < N)
    (hint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, α w * ρ w ((N : F) * (r : F)) = n) :
    ∃ a : F, ∀ w, α w = ρ w a := by
  have hrat : ∀ c : F, ∃ q : ℚ, ∑ w, α w * ρ w c = q := by
    intro c
    obtain ⟨y, hy, hyi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, (r : F) = (y : F) * c :=
      ⟨IsIntegralClosure.mk' (𝓞 F) (y • c) hyi,
        (IsIntegralClosure.algebraMap_mk' (𝓞 F) (y • c) hyi).trans (by simp)⟩
    obtain ⟨n, hn⟩ := hint r
    refine ⟨n / (N * y), ?_⟩
    have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 : ∑ w, α w * ρ w ((N : F) * (r : F)) = N * y * ∑ w, α w * ρ w c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hr]
      simp only [map_mul, map_natCast, map_intCast]
      ring
    rw [h1] at hn
    push_cast
    field_simp
    linarith
  choose q hq using hrat
  let L : F →ₗ[ℚ] ℚ :=
    { toFun := q
      map_add' := fun x y => by
        have : ((q (x + y) : ℚ) : ℝ) = ((q x + q y : ℚ) : ℝ) := by
          push_cast
          rw [← hq, ← hq, ← hq, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [map_add]
          ring
        exact_mod_cast this
      map_smul' := fun t x => by
        have : ((q (t • x) : ℚ) : ℝ) = ((t * q x : ℚ) : ℝ) := by
          push_cast
          rw [← hq, ← hq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          have : t • x = (t : F) * x := by simp [Algebra.smul_def]
          rw [this, map_mul, map_ratCast]
          ring
        exact_mod_cast this }
  let a : F := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).symm L
  have ha : ∀ c, q c = Algebra.trace ℚ F (a * c) := by
    intro c
    have h1 := LinearMap.BilinForm.toDual_def (traceForm_nondegenerate ℚ F) (m := a) (n := c)
    rw [LinearEquiv.apply_symm_apply, Algebra.traceForm_apply] at h1
    exact h1
  refine ⟨a, fun w => ?_⟩
  have h0 : (fun w => α w - ρ w a) = 0 := by
    refine places_indep ρ hρ _ fun c => ?_
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hq c, ha c, ← htr (a * c)]
    simp [map_mul]
  have h1 := congrFun h0 w
  simpa [sub_eq_zero] using h1

theorem exists_char_data : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ a : F, a ≠ 0 ∧ (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) ∧ ∃ ψf : AddChar (Af F) ℂ, GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf ∧ ∀ y : Af F, ψ (pairA F 0 y) = ψf (algebraMap F (Af F) a * y) := by
  intro F _ _ hF ρ e hρ he heρ ψ hψ
  classical
  have htr := GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ
  have hes : Continuous e.toEquiv.symm := (Equiv.continuous_symm_iff e.toEquiv).2 he.isOpenMap

  let φ : (InfinitePlace F → ℝ) →+ AF F :=
    { toFun := fun x => pairA F (e.symm x) 0
      map_zero' := by
        rw [map_zero]
        rfl
      map_add' := fun x y => by
        rw [map_add]
        exact Prod.ext rfl (add_zero _).symm }
  have hφ : Continuous φ := (hes.prodMk continuous_const : Continuous fun x => (e.symm x, (0 : Af F)))
  obtain ⟨α, hα⟩ := pi_char (ψ.compAddMonoidHom φ) (hψ.1.comp hφ) (fun x => hψ.2.1 _)
  have hinf : ∀ x : Ainf F, ψ (pairA F x 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ w, α w * e x w : ℝ) : ℂ)) := fun x => by
    have := hα (e x)
    simpa [φ] using this
  have hsplit : ∀ c : F, ψ (pairA F (algebraMap F (Ainf F) c) 0) *
      ψ (pairA F 0 (algebraMap F (Af F) c)) = 1 := fun c => by
    rw [← AddChar.map_add_eq_mul, ← hψ.2.2.1 c]
    exact congrArg ψ (Prod.ext (add_zero _) (zero_add _))

  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.2.1 _ (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  have hint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, α w * ρ w ((N : F) * (r : F)) = n := by
    intro r
    have hr : algebraMap F (Af F) (r : F) ∈ GlobalTheory.CompanionTheory.SW.Core.Oh F :=
      ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 _).2 ⟨r, rfl⟩
    have h1 : ψ (pairA F 0 (algebraMap F (Af F) ((N : F) * (r : F)))) = 1 := by
      have := hNU _ hr
      rw [map_mul, map_natCast]
      exact this
    have h2 := hsplit ((N : F) * (r : F))
    rw [h1, mul_one, hinf, Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨n, ?_⟩
    have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have h3 : ((∑ w, α w * e (algebraMap F (Ainf F) ((N : F) * (r : F))) w : ℝ) : ℂ) = n := by
      apply mul_left_cancel₀ hI
      rw [hn]
      ring
    simp only [heρ] at h3
    exact_mod_cast h3
  obtain ⟨a, ha⟩ := exists_dual ρ hρ htr α N hN hint
  have hinf' : ∀ x : Ainf F, ψ (pairA F x 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ)) := fun x => by
    rw [hinf]
    simp only [ha]
  have hfin : ∀ c : F, ψ (pairA F 0 (algebraMap F (Af F) c)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F (a * c) : ℚ) : ℂ)) := fun c => by
    have h1 := hsplit c
    have h2 : ((∑ w, ρ w a * e (algebraMap F (Ainf F) c) w : ℝ) : ℂ) = ((Algebra.trace ℚ F (a * c) : ℚ) : ℂ) := by
      have h3 := htr (a * c)
      simp only [map_mul] at h3
      simp only [heρ]
      rw [h3]
      push_cast
      rfl
    rw [hinf', h2] at h1
    rw [neg_mul, Complex.exp_neg]
    exact eq_inv_of_mul_eq_one_right h1
  have hp : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 : ∀ x : Ainf F, ψ (pairA F x 0) = 1 := fun x => by
      rw [hinf']
      simp
    have h2 : ∀ y : Af F, ψ (pairA F 0 y) = 1 := by
      intro y
      have hc : Continuous fun y : Af F => ψ (pairA F 0 y) := hψ.1.comp hp
      refine (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.1.induction_on y (isClosed_eq hc continuous_const) fun c => ?_
      rw [hfin]
      simp
    obtain ⟨z, hz⟩ := hψ.2.2.2
    apply hz
    have h3 : z = pairA F z.1 0 + pairA F 0 z.2 := Prod.ext (add_zero _).symm (zero_add _).symm
    rw [h3, AddChar.map_add_eq_mul, h1, h2, one_mul]

  let ψf : AddChar (Af F) ℂ :=
    { toFun := fun y => ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * y))
      map_zero_eq_one' := by
        rw [mul_zero]
        exact ψ.map_zero_eq_one
      map_add_eq_mul' := fun x y => by
        rw [mul_add, ← AddChar.map_add_eq_mul]
        exact congrArg ψ (Prod.ext (add_zero _).symm rfl) }
  refine ⟨a, ha0, hinf', ψf, ⟨?_, fun b => ?_⟩, fun y => ?_⟩
  · exact hψ.1.comp (hp.comp (continuous_const.mul continuous_id))
  · show ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * algebraMap F (Af F) b)) = _
    rw [← map_mul, hfin, mul_inv_cancel_left₀ ha0]
  · show _ = ψ (pairA F 0 (algebraMap F (Af F) a⁻¹ * (algebraMap F (Af F) a * y)))
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_mul]

end GlobalTheory.CompanionTheory.Glob.CharAF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicIntegrableProductIndicator
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem integral_pure_indicator_char : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (db : Measure (AF F)) (laminf : Measure (Ainf F)) (lf : Measure (Af F)), laminf.IsAddHaarMeasure → lf.IsAddHaarMeasure → ∀ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) → MeasurePreserving e (laminf.prod lf) db → ∀ (g : Ainf F → ℂ) (B : AddSubgroup (Af F)), MeasurableSet (B : Set (Af F)) → lf (B : Set (Af F)) ≠ ⊤ → ∀ b : AF F, ∫ y, (g (fstA F y) * (B : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F y)) * ψ (y * b) ∂db = (∫ x, g x * psiInf F ψ (x * fstA F b) ∂laminf) * ((lf (B : Set (Af F))).toReal : ℂ) * (annF ψ (B : Set (Af F))).indicator (fun _ => (1 : ℂ)) (sndA F b) := by
  intro F _ _ ψ _ db laminf lf hl hf e he hmp g B hB hfin b
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).2.1
  haveI : SecondCountableTopology (Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).2.2.1
  haveI : SecondCountableTopology (Ainf F) := by
    haveI : SecondCountableTopology (Ainf F × Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).1.2.1
    exact (Topology.IsEmbedding.of_comp (f := fun x : Ainf F => (x, (0 : Af F))) (g := Prod.fst)
      (by fun_prop) continuous_fst Topology.IsEmbedding.id).secondCountableTopology
  haveI : LocallyCompactSpace (Ainf F) := inferInstance
  haveI : IsLocallyFiniteMeasure laminf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : IsLocallyFiniteMeasure lf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SFinite laminf := inferInstance
  haveI : SFinite lf := inferInstance
  set χ : Af F → ℂ := fun u => psiF ψ (u * sndA F b) with hχ
  have hχadd : ∀ x y, χ (x + y) = χ x * χ y := fun x y => by
    simp only [hχ, add_mul, psiF_add]
  have hpt : ∀ p : Ainf F × Af F,
      (g (fstA F (e p)) * (B : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F (e p))) * ψ (e p * b) =
        (g p.1 * psiInf F ψ (p.1 * fstA F b)) * (B : Set (Af F)).indicator χ p.2 := by
    rintro ⟨x, u⟩
    have h1 : e (x, u) * b = pairA F (x * fstA F b) (u * sndA F b) := by
      rw [he]; rfl
    have h2 : fstA F (e (x, u)) = x := by rw [he]; rfl
    have h3 : sndA F (e (x, u)) = u := by rw [he]; rfl
    rw [h1, h2, h3, psi_pairA]
    by_cases hu : u ∈ (B : Set (Af F))
    · simp only [Set.indicator_of_mem hu, hχ]
      ring
    · simp only [Set.indicator_of_notMem hu]
      ring
  rw [← hmp.integral_comp e.measurableEmbedding]
  simp only [hpt]
  rw [integral_prod_mul (fun x => g x * psiInf F ψ (x * fstA F b))
    (fun u => (B : Set (Af F)).indicator χ u), mul_assoc]
  congr 1
  by_cases hb : sndA F b ∈ annF ψ (B : Set (Af F))
  · rw [integral_indicator_char_of_trivial lf B hB χ (fun x hx => hb x hx),
      Set.indicator_of_mem hb, mul_one]
  · obtain ⟨y, hy, hne⟩ : ∃ y ∈ (B : Set (Af F)), psiF ψ (y * sndA F b) ≠ 1 := by
      simpa [annF] using hb
    rw [integral_indicator_char_of_ne lf B χ hχadd hy hne, Set.indicator_of_notMem hb, mul_zero]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsRealApproximateIdentity
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem integrable_inf_mul_indicator_finiteMass : ∀ (F : Type) [Field F] [NumberField F] (db : Measure (AF F)) (laminf : Measure (Ainf F)) (lf : Measure (Af F)), laminf.IsAddHaarMeasure → lf.IsAddHaarMeasure → ∀ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) → MeasurePreserving e (laminf.prod lf) db → ∀ (g : Ainf F → ℂ) (B : Set (Af F)), Integrable g laminf → MeasurableSet B → lf B ≠ ⊤ → Integrable (fun y => g (fstA F y) * B.indicator (fun _ => (1 : ℂ)) (sndA F y)) db := by
  intro F _ _ db laminf lf _ _ e he hmp g B hg hB hfin
  have hind : Integrable (B.indicator (fun _ => (1 : ℂ))) lf :=
    (integrable_indicator_iff hB).mpr (integrableOn_const hfin)
  refine (hmp.integrable_comp_emb e.measurableEmbedding).mp ?_
  have hfun : ((fun y => g (fstA F y) * B.indicator (fun _ => (1 : ℂ)) (sndA F y)) ∘ e) =
      fun p : Ainf F × Af F => g p.1 * B.indicator (fun _ => (1 : ℂ)) p.2 := by
    funext p
    simp only [Function.comp_apply, he p]
    rfl
  rw [hfun]
  exact hg.mul_prod hind

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

