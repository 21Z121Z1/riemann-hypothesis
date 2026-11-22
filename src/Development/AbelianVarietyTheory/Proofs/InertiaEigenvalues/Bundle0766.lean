import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0758
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalArchimedeanKernelConvolutionOperator
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW.KerCusp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_unip {r : ℕ} : Continuous (fun x : BlockIx a r → Ad E => (unip x : GA E a)) := by
  have hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E))) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn

theorem measurable_integrand {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    {X : Type} [MeasurableSpace X] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : Measurable k)
    (hγ : Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)))) (φ : Sm E a)
    (hc : Continuous φ.1) (g : GA E a) :
    Measurable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) := by
  let Φ : invSet E a → (BlockIx a r → Ad E) → ℂ := fun y u => chart φ.1 (unip u * g) y.1
  have hΦ : Measurable (Function.uncurry Φ) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun u => ?_) (fun y => ?_)
    · exact ((φ.2 (unip u * g)).continuousOn).restrict
    · have e : Φ y = fun u => φ.1 (unip u * g * infGL E a y.2.unit) := by
        funext u; exact dif_pos y.2
      rw [e]
      exact (hc.comp ((continuous_unip.mul continuous_const).mul continuous_const)).measurable
  have hy : Measurable (fun x : X => (⟨toL (γ x).val, val_mem_invSet (γ x)⟩ : invSet E a)) :=
    Measurable.subtype_mk hγ
  have e : (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) =
      fun p => k p.2 * Function.uncurry Φ (⟨toL (γ p.2).val, val_mem_invSet (γ p.2)⟩, p.1) := by
    funext p
    rcases p with ⟨u, x⟩
    simp only [Function.uncurry_apply_pair, Φ, chart_val]
  rw [e]
  exact (hk.comp measurable_snd).mul (hΦ.comp ((hy.comp measurable_snd).prodMk measurable_fst))

end GlobalTheory.JSW.KerCusp

namespace GlobalTheory.JSW

theorem isCuspidal_kerOp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, IsBCC φ.1 →
      IsCuspidal (kerOp ν k γ φ.1) := by
  intro E _ _ _ a X _ ν _ k γ hk φ hφ r h0 h1 _ _ μ 𝓕 hμ hF g
  haveI := hμ
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := hφ.bdd
  have hk0 : Integrable (fun x => ‖k x‖) ν := by simpa using hk.2.2 0
  have hm := KerCusp.measurable_integrand (r := r) hk.1 hk.2.1 φ hφ.cont g
  have hint : Integrable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) =>
      k x * φ.1 (unip u * g * infGL E a (γ x))) ((μ.restrict 𝓕).prod ν) := by
    refine Integrable.mono' ((integrable_const C).mul_prod hk0) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨u, x⟩
    simp only [Function.uncurry_apply_pair, norm_mul]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  change ∫ u in 𝓕, (∫ x, k x * φ.1 (unip u * g * infGL E a (γ x)) ∂ν) ∂μ = 0
  rw [integral_integral_swap hint]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans (integral_zero X ℂ)
  rw [integral_const_mul]
  have e : ∀ u : BlockIx a r → Ad E, unip u * g * infGL E a (γ x) = unip u * (g * infGL E a (γ x)) :=
    fun u => mul_assoc _ _ _
  simp only [e]
  rw [hφ.cusp r h0 h1 μ 𝓕 hμ hF _, mul_zero]

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelOperatorIntegrableContinuousSmooth
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem measurable_smooth_comp_infGL {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    {X : Type} [MeasurableSpace X] (γ : X → GL (Fin a) (Cinf E))
    (hγ : Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)))) (φ : Sm E a) (g : GA E a) :
    Measurable (fun x => φ.1 (g * infGL E a (γ x))) := by
  classical
  have hc : Measurable (chart φ.1 g) := by
    have e : chart φ.1 g = (invSet E a).piecewise (chart φ.1 g) (fun _ => 0) := by
      funext x
      by_cases h : x ∈ invSet E a
      · simp [Set.piecewise, h]
      · have h' : ¬ IsUnit (Matrix.of x) := h
        simp only [Set.piecewise, h, if_false]
        simp [chart, h']
    rw [e]
    exact ContinuousOn.measurable_piecewise (φ.2 g).continuousOn continuousOn_const isOpen_invSet.measurableSet
  have hγ' : Measurable (fun x => toL (γ x).val) := hγ
  have h2 := hc.comp hγ'
  simpa [Function.comp_def, chart_val] using h2

theorem kerOp_integrable_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, Continuous φ.1 →
    (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
      (∀ g, Integrable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν) ∧ Continuous (kerOp ν k γ φ.1) := by
  intro E _ _ _ a X _ ν k γ hk φ hφc hb
  obtain ⟨C, hC⟩ := hb
  have hint : Integrable (fun x => ‖k x‖ * C) ν := by
    have h0 := hk.2.2 0
    simp only [pow_zero, mul_one] at h0
    exact h0.mul_const C
  have hm : ∀ g, AEStronglyMeasurable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν := fun g =>
    (hk.1.mul (measurable_smooth_comp_infGL γ hk.2.1 φ g)).aestronglyMeasurable
  have hbd : ∀ g, ∀ᵐ x ∂ν, ‖k x * φ.1 (g * infGL E a (γ x))‖ ≤ ‖k x‖ * C := fun g =>
    Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  refine ⟨fun g => Integrable.mono' hint (hm g) (hbd g), ?_⟩
  exact continuous_of_dominated hm hbd hint (Filter.Eventually.of_forall fun x =>
    continuous_const.mul (hφc.comp (continuous_id.mul continuous_const)))

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowFiniteMemCompactOnSupport
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem GlobalTheory.JSW.lastRow_finite_compact : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := by
  intro E _ _ m S β ⟨C, hC, hCβ⟩
  let F : GA E (m + 1) → (Fin (m + 1) → Af E) :=
    fun c j => pFin E ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)
  have hF : Continuous F := by
    refine continuous_pi fun j => ?_
    have h0 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) :=
      Units.continuous_val
    have h1 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j :=
      h0.matrix_elem (Fin.last m) j
    exact continuous_snd.comp h1
  refine ⟨F '' C, hC.image hF, fun h hS hβ => ?_⟩
  obtain ⟨u, hu, huC⟩ := hCβ h hS hβ
  refine ⟨u⁻¹ * h, huC, ?_⟩
  set c : GA E (m + 1) := u⁻¹ * h with hc
  have hh : h = u * c := by rw [hc]; group
  have key : ∀ j, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j := by
    intro j
    have hm : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) =
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) * (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := by
      rw [hh]; rfl
    rw [hm, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hu.2, one_mul]
    · intro l _ hl
      rw [hu.1 (Fin.last m) l (lt_of_le_of_ne (Fin.le_last l) hl), zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  funext j
  simp only [F, key j]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieSkewAdjointMatrix
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory.LieSkew

open GlobalTheory.ExpDeriv

theorem inner_integral_identity : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc hc0 f f' hf hf' hcf' hd H t
  exact GlobalTheory.T.inner_rightRegularRep_sub_eq_intervalIntegral_derivative Γ μ c hc hc0 hf hf' hcf' hd H t (GlobalTheory.T.integrable_conj_mul_translate_path' Γ μ c hc hf' hcf' H t)

theorem hasDerivAt_inner_R : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ H : L2 Γ μ, HasDerivAt (fun t => inner ℂ H (R Γ μ (c t) hf.toL2)) (inner ℂ H hf'.toL2) 0 := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc hc0 f f' hf hf' hcf' hd H
  have hk : Continuous fun s => inner ℂ H (R Γ μ (c s) hf'.toL2) :=
    continuous_const.inner ((continuous_R hf'.toL2).comp hc)
  have e : (fun t => inner ℂ H (R Γ μ (c t) hf.toL2)) =
      fun t => inner ℂ H hf.toL2 + ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
    funext t
    rw [← inner_integral_identity Γ μ c hc hc0 hf hf' hcf' hd H t, add_sub_cancel]
  rw [e]
  have := ((hk.integral_hasStrictDerivAt 0 0).hasDerivAt).const_add (inner ℂ H hf.toL2)
  simpa [hc0] using this

theorem inner_lie_eq_neg_inner_lie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (μ : Measure (GA E N))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)
    (hW : IsStable W) (hA : ∀ φ ∈ W, IsAutForm φ) (X : Lie E N) (φ ψ : W) :
    inner ℂ (toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩) (toL2ₗ μ W h ψ) =
      - inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩) := by
  set c : ℝ → GA E N := fun t => infGL E N (expGL X t) with hcdef
  have hc : Continuous c := by
    have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Matrix.of X) := by
      open scoped Matrix.Norms.Operator in
      exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    have hinv : ∀ t, (expGL X t)⁻¹ = expGL X (-t) := fun t =>
      (eq_inv_of_mul_eq_one_right (by rw [← expGL_add, add_neg_cancel, expGL_zero])).symm
    have he : Continuous (expGL X) := Units.continuous_iff.2 ⟨hv, by
      simp only [hinv, expGL_val]
      exact hv.comp continuous_neg⟩
    exact GlobalTheory.CuspQuot.continuous_infGL.comp he
  have hc0 : c 0 = 1 := by simp only [c, expGL_zero, map_one]
  have hcinv : ∀ t, c (-t) = (c t)⁻¹ := fun t => by
    simp only [c, ← map_inv]
    congr 1
    refine (eq_inv_of_mul_eq_one_right ?_)
    rw [← expGL_add, add_neg_cancel, expGL_zero]
  have hcont : ∀ θ ∈ W, Continuous (θ : GA E N → ℂ) := fun θ hθ =>
    ContAut.continuous_of_isOpen_stab E N θ (hA θ hθ).level
  set F := toL2ₗ μ W h φ
  set Ψ := toL2ₗ μ W h ψ
  set F' := toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩
  set Ψ' := toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩
  have dF := hasDerivAt_inner_R (latticeGL E N) μ c hc hc0 (h φ φ.2) (h _ (hW (.lie X) φ.1 φ.2))
    (hcont _ (hW (.lie X) φ.1 φ.2)) (fun x t => hasDerivAt_along X φ.1 x t) Ψ
  have dΨ := hasDerivAt_inner_R (latticeGL E N) μ c hc hc0 (h ψ ψ.2) (h _ (hW (.lie X) ψ.1 ψ.2))
    (hcont _ (hW (.lie X) ψ.1 ψ.2)) (fun x t => hasDerivAt_along X ψ.1 x t) F
  have d1 : HasDerivAt (fun t => inner ℂ (R (latticeGL E N) μ (c t) F) Ψ) (inner ℂ F' Ψ) 0 := by
    have := dF.star
    simp only [← starRingEnd_apply, inner_conj_symm] at this
    exact this
  have d2 : HasDerivAt (fun t => inner ℂ F (R (latticeGL E N) μ (c (-t)) Ψ)) (-inner ℂ F Ψ') 0 := by
    have h0 : HasDerivAt (fun t => inner ℂ F (R (latticeGL E N) μ (c t) Ψ)) (inner ℂ F Ψ') (-0) := by
      rw [neg_zero]; exact dΨ
    have := h0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simpa [Function.comp_def] using this
  have e : (fun t => inner ℂ (R (latticeGL E N) μ (c t) F) Ψ) =
      fun t => inner ℂ F (R (latticeGL E N) μ (c (-t)) Ψ) := by
    funext t
    let U : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
      ⟨(R (latticeGL E N) μ (c t)).toLinearMap, fun v => norm_R _ v⟩
    have hU : ∀ v, U v = R (latticeGL E N) μ (c t) v := fun _ => rfl
    have hΨ : R (latticeGL E N) μ (c t) (R (latticeGL E N) μ (c t)⁻¹ Ψ) = Ψ := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    calc inner ℂ (R (latticeGL E N) μ (c t) F) Ψ
        = inner ℂ (U F) (U (R (latticeGL E N) μ (c t)⁻¹ Ψ)) := by rw [hU, hU, hΨ]
      _ = inner ℂ F (R (latticeGL E N) μ (c t)⁻¹ Ψ) := U.inner_map_map _ _
      _ = _ := by rw [hcinv]
  rw [e] at d1
  exact d1.unique d2

theorem lie_skew : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hW : IsStable W), (∀ φ ∈ W, IsAutForm φ) → ∀ (X : Matrix (Fin N) (Fin N) (Cinf E)) (φ ψ : W), inner ℂ (toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩) (toL2ₗ μ W h ψ) = - inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩) := by
  intro E _ _ _ N μ _ _ W h hW hA X φ ψ
  exact inner_lie_eq_neg_inner_lie μ W h hW hA X φ ψ

end GlobalTheory.LieSkew
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentMemMaxCompactGLIffMemMaxCompact
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.LocInteg

theorem kappa_mem_int {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (F : FinIso L n)
    (w : HeightOneSpectrum (𝓞 L)) {z : AL L} (hz : z ∈ ALint L) : F.κ z w ∈ w.adicCompletionIntegers L := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨a, ha, rfl⟩
    · rw [F.left]
      exact GlobalTheory.AdeleBaseChange.algebraMap_int_mem y w
    · have h := GlobalTheory.UnramDict.kappa_tmul F 1 a
      rw [map_one, one_mul] at h
      change F.κ.toRingHom _ w ∈ _
      rw [h]
      exact GlobalTheory.AdeleBaseChange.adMap_int ha w
  | one => rw [map_one]; exact one_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem cLoc_mem_KGL_iff : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (w : HeightOneSpectrum (𝓞 L)) (y : GAf L n), F.j y ∈ locU n w → (cLoc w (F.j y) ∈ GlobalTheory.LFun.KGL w n ↔ y ∈ Umax L n) := by
  intro L _ _ _ n F w y hy
  constructor
  · intro hK i j
    exact GlobalTheory.UnramDict.mem_ALint F _ fun u => by
      rw [← F.loc]
      exact GlobalTheory.UnramDict.cLoc_entry_mem hy hK u i j
  · intro hyU
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [F.loc]
      exact kappa_mem_int F w (hyU i j)
    · rw [← map_inv, ← map_inv, F.loc]
      exact kappa_mem_int F w ((inv_mem hyU : y⁻¹ ∈ Umax L n) i j)

end GlobalTheory.LocInteg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmoothOfChartDerivativesAtIdentity
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
open scoped ContDiff

namespace GlobalTheory.SmOfDeriv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def compLmul (ℓ : Lie E a →L[ℝ] ℂ) : Lie E a →L[ℝ] (Lie E a →L[ℝ] ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => ℓ.comp (lmul M)
      map_add' := fun M N => by
        ext v
        change ℓ (toL ((Matrix.of M + Matrix.of N) * Matrix.of v)) = ℓ (toL (Matrix.of M * Matrix.of v)) + ℓ (toL (Matrix.of N * Matrix.of v))
        rw [Matrix.add_mul]
        exact map_add ℓ (toL (Matrix.of M * Matrix.of v)) (toL (Matrix.of N * Matrix.of v))
      map_smul' := fun c M => by
        ext v
        change ℓ (toL ((c • Matrix.of M) * Matrix.of v)) = c • ℓ (toL (Matrix.of M * Matrix.of v))
        rw [Matrix.smul_mul]
        exact map_smul ℓ c (toL (Matrix.of M * Matrix.of v)) }

theorem contDiffAt_inv {z : Lie E a} (hz : z ∈ invSet E a) :
    ContDiffAt ℝ ∞ (fun x : Lie E a => toL (Matrix.of x)⁻¹) z := by
  have hdet : IsUnit (Matrix.of z).det := (Matrix.isUnit_iff_isUnit_det _).1 hz
  have h1 : ContDiffAt ℝ ∞ (fun x : Lie E a => Ring.inverse (Matrix.of x).det) z := by
    have h := contDiffAt_ringInverse ℝ (n := ∞) hdet.unit
    rw [IsUnit.unit_spec] at h
    exact h.comp z (contDiff_det (E := E)).contDiffAt
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have h2 : ContDiff ℝ ∞ fun x : Lie E a => Matrix.adjugate (Matrix.of x) i j := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => ?_)
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact (contDiff_apply ℝ _ k).comp (contDiff_apply ℝ _ (σ k))
  have e : (fun x : Lie E a => toL (Matrix.of x)⁻¹ i j) =
      fun x => Ring.inverse (Matrix.of x).det * Matrix.adjugate (Matrix.of x) i j := by
    funext x
    rw [Matrix.inv_def]
    rfl
  rw [e]
  exact h1.mul h2.contDiffAt

theorem hasFDerivAt_chart {f : GA E a → ℂ} {ι : Type} [Fintype ι] {fs : ι → GA E a → ℂ}
    {ℓ : ι → (Lie E a →L[ℝ] ℂ)} (hd : ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a))
    (g : GA E a) {z : Lie E a} (hz : z ∈ invSet E a) :
    HasFDerivAt (chart f g) (∑ i, chart (fs i) g z • compLmul (ℓ i) (toL (Matrix.of z)⁻¹)) z := by
  obtain ⟨y, hy⟩ := hz
  obtain rfl : z = toL y.val := hy.symm
  have e : chart f g = chart f (g * infGL E a y) ∘ lmul (toL (y⁻¹).val) := by
    rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : lmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.inv_mul
  have h := hd (g * infGL E a y)
  rw [← e1] at h
  have h2 := h.comp (toL y.val) (lmul (toL (y⁻¹).val)).hasFDerivAt
  rw [← e] at h2
  refine h2.congr_fderiv ?_
  have ei : toL (Matrix.of (toL y.val))⁻¹ = toL (y⁻¹).val := by
    change toL (y.val)⁻¹ = toL (y⁻¹).val
    rw [Matrix.coe_units_inv]
  rw [ei]
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chart_val]
  rfl

theorem mem_Sm_of_hasFDerivAt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (K : Set (GA E a → ℂ)),
    (∀ f ∈ K, ∃ (ι : Type) (_ : Fintype ι) (fs : ι → GA E a → ℂ) (ℓ : ι → (Lie E a →L[ℝ] ℂ)), (∀ i, fs i ∈ K) ∧
      ∀ g, HasFDerivAt (chart f g) (∑ i, fs i g • ℓ i) (oneL E a)) → ∀ f ∈ K, f ∈ Sm E a := by
  intro E _ _ _ a K hK
  have key : ∀ n : ℕ, ∀ f ∈ K, ∀ g, ∀ z ∈ invSet E a, ContDiffAt ℝ n (chart f g) z := by
    intro n
    induction n with
    | zero =>
      intro f hf g z hz
      obtain ⟨ι, _, fs, ℓ, -, hd⟩ := hK f hf
      exact contDiffAt_zero.2 ⟨invSet E a, isOpen_invSet.mem_nhds hz, fun x hx =>
        (hasFDerivAt_chart hd g hx).continuousAt.continuousWithinAt⟩
    | succ n ih =>
      intro f hf g z hz
      obtain ⟨ι, _, fs, ℓ, hfs, hd⟩ := hK f hf
      rw [Nat.cast_succ]
      refine contDiffAt_succ_iff_hasFDerivAt.2 ⟨_, ⟨invSet E a, isOpen_invSet.mem_nhds hz,
        fun x hx => hasFDerivAt_chart hd g hx⟩, ?_⟩
      refine ContDiffAt.sum fun i _ => (ih (fs i) (hfs i) g z hz).smul ?_
      exact (compLmul (ℓ i)).contDiff.contDiffAt.comp z (contDiffAt_infty.1 (contDiffAt_inv hz) n)
  intro f hf g z hz
  exact (contDiffAt_infty.2 fun n => key n f hf g z hz).contDiffWithinAt

end GlobalTheory.SmOfDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFderivChartLeOfBoundedLieDerivatives
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem norm_toL_mul_le {E : Type} [Field E] [NumberField E] {a : ℕ} (A : Matrix (Fin a) (Fin a) (Cinf E)) (B : Lie E a) :
    ‖toL (A * Matrix.of B)‖ ≤ a * (‖toL A‖ * ‖B‖) := by
  have h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖B‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  show ‖(A * Matrix.of B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k, ‖A i k * Matrix.of B k j‖ ≤ ‖toL A‖ * ‖B‖ := fun k => by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
    · exact (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
    · exact (norm_le_pi_norm (B k) j).trans (norm_le_pi_norm B k)
  calc ∑ k, ‖A i k * Matrix.of B k j‖ ≤ ∑ _k : Fin a, ‖toL A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => hk k
    _ = _ := by simp

theorem norm_fderiv_chart_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  intro E _ _ _ a φ hC
  choose C hC using hC
  set D : ℝ := ∑ i, max (C i) 0 * ‖lieCoord E a i‖ with hDdef
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (norm_nonneg _)
  have hlie : ∀ (X : Lie E a) (h : GA E a), ‖lieD X φ.1 h‖ ≤ D * ‖X‖ := by
    intro X h
    have e : lieD X φ.1 h = ∑ i, ((lieBasis E a).coord i X) • lieD (lieBasis E a i) φ.1 h := by
      conv_lhs => rw [← sum_lieCoord X]
      simp only [lieD, map_sum, map_smul]
    rw [e, hDdef, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    have h1 : ‖(lieBasis E a).coord i X‖ ≤ ‖lieCoord E a i‖ * ‖X‖ := by
      have : ‖lieCoord E a i X‖ = ‖(lieBasis E a).coord i X‖ := by simp [lieCoord]
      rw [← this]; exact (lieCoord E a i).le_opNorm X
    have h2 : ‖lieD (lieBasis E a i) φ.1 h‖ ≤ max (C i) 0 := by
      have := hC i h
      rw [GlobalTheory.CuspRep.lie_apply] at this
      exact this.trans (le_max_left _ _)
    calc ‖(lieBasis E a).coord i X‖ * ‖lieD (lieBasis E a i) φ.1 h‖
        ≤ (‖lieCoord E a i‖ * ‖X‖) * max (C i) 0 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨a * D, fun g y => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun W => ?_
  set X : Lie E a := toL ((y⁻¹).val * Matrix.of W) with hX
  have e := chart_lieD φ.2 X g (val_mem_invSet y)
  have eW : rmul X (toL y.val) = W := by
    change y.val * ((y⁻¹).val * Matrix.of W) = Matrix.of W
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [eW, chart_val] at e
  rw [← e]
  calc ‖lieD X φ.1 (g * infGL E a y)‖ ≤ D * ‖X‖ := hlie _ _
    _ ≤ D * (a * (‖toL (y⁻¹).val‖ * ‖W‖)) := mul_le_mul_of_nonneg_left (norm_toL_mul_le _ _) hD
    _ = a * D * ‖toL (y⁻¹).val‖ * ‖W‖ := by ring

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductDatumThetaHasShapeAdjointPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productDatumTheta_hasShape_adjoint_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (P : Finset (Pl D.host.E)) (e e₀ : AE D) (PP : Pl D.host.E), IsIdemSum e P → PP ∈ P → Formalism.L2.NTheta.IsIdemAt e₀ PP → ∀ ω₁ ω₂ : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ, (∀ y y', y PP = y' PP → ω₁ y = ω₁ y') → (∀ y y', (∀ PP' ∈ P, PP' ≠ PP → y PP' = y' PP') → ω₂ y = ω₂ y') → ∀ f₀ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latH S T ΛS ΛT) 1 f₀ (adjDat S T βS βT e fun y => ω₁ y * ω₂ y) f → HasShape ψ S T (cA D e₀) (adjDat S T βS βT e₀ ω₁) f := by
  first | exact @GlobalTheory.DownLift.ProdShape.hasShape_adjDat | exact GlobalTheory.DownLift.ProdShape.hasShape_adjDat | (intros; apply GlobalTheory.DownLift.ProdShape.hasShape_adjDat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApplyStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurComplementExtensionFunction_blockDiag_apply : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), ∀ h : GA E (m + 1), schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h * b₁ 1 * (χ 0 : ℂ) := by
  first | (exact @GlobalTheory.SchurExt.schurF_blockGL) | (exact GlobalTheory.SchurExt.schurF_blockGL) | (intros; apply GlobalTheory.SchurExt.schurF_blockGL  <;> assumption)
end

