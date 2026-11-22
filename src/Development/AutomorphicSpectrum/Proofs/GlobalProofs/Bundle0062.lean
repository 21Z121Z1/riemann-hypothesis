import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariant
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesSelfDual
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0027
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterOrthogonalIsRational
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann

section Core

open GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.SelfDual Topology

variable {F : Type} [Field F] [NumberField F]

theorem fin_eq_zero (ψf : AddChar (A F) ℂ) (hψ : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) {y : A F}
    (hy : ∀ t : F, ψf (algebraMap F (A F) t * y) = 1) : y = 0 := by
  obtain ⟨hlc, hsc, ht2, hOc, hOo, hden, hint, hnb, hcp, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hall : ∀ z : A F, ψf (z * y) = 1 := by
    intro z
    have hcl : IsClosed {z : A F | ψf (z * y) = 1} :=
      isClosed_eq (hψ.1.comp (continuous_id.mul continuous_const)) continuous_const
    exact hden.induction_on (p := fun z => ψf (z * y) = 1) z hcl hy
  have hMc : IsCompact (MG ψf : Set (A F)) := by
    refine isCompact_of_relIndex (ohG_le_MG hψ) ?_ hOc
    rw [relIndex_MG hψ]
    exact Int.natAbs_ne_zero.2 (discr_ne_zero F)
  obtain ⟨N, hN, hNK⟩ := hcp _ hMc
  have hinv : ∀ m : ℕ, 0 < m → (m : A F) * algebraMap F (A F) (m : F)⁻¹ = 1 := by
    intro m hm
    have hm' : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← map_natCast (algebraMap F (A F)), ← map_mul, mul_inv_cancel₀ hm', map_one]
  have hmul : ∀ m : ℕ, 0 < m → algebraMap F (A F) (m : F)⁻¹ * ((N : A F) * y) ∈ Oh F := by
    intro m hm
    have h1 : algebraMap F (A F) (m : F)⁻¹ * y ∈ MG ψf := by
      intro z _
      show ψf (z * _) = 1
      rw [← mul_assoc]
      exact hall _
    have h2 := hNK _ h1
    rwa [mul_left_comm] at h2
  have hw : (N : A F) * y = 0 := by
    by_contra hne
    have hU : ({(N : A F) * y}ᶜ : Set (A F)) ∈ 𝓝 (0 : A F) :=
      isOpen_compl_singleton.mem_nhds (fun h => hne (Eq.symm h))
    obtain ⟨m, hm, hmU⟩ := hnb _ hU
    apply hmU _ (hmul m hm)
    rw [← mul_assoc, hinv m hm, one_mul]
    rfl
  calc y = algebraMap F (A F) (N : F)⁻¹ * ((N : A F) * y) := by
        rw [← mul_assoc, mul_comm (algebraMap F (A F) _), hinv N hN, one_mul]
    _ = 0 := by rw [hw, mul_zero]

theorem coeff_eq_zero (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (D : InfinitePlace F → ℝ)
    (h : ∀ t : F, ∑ w, ρ w t * D w = 0) : ∀ w, D w = 0 := by
  have hinj : Function.Injective (fun w => ((ρ w : F →+* ℝ) : F →* ℝ)) := by
    intro w w' hww
    have h1 : w.embedding = w'.embedding := by
      ext x
      rw [← hρ, ← hρ]
      have : ρ w x = ρ w' x := DFunLike.congr_fun hww x
      rw [this]
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1]
  have hli := (linearIndependent_monoidHom F ℝ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  refine hli D ?_
  ext t
  simpa [mul_comm] using h t

theorem real_eq_of_int (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (X : InfinitePlace F → ℝ)
    (hX : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, ρ w (r : F) * X w = n) : ∃ c : F, ∀ w, X w = ρ w c := by
  classical
  set e := integralBasis F with he
  have hXe : ∀ i, ∃ n : ℤ, ∑ w, ρ w (e i) * X w = n := by
    intro i
    obtain ⟨n, hn⟩ := hX (RingOfIntegers.basis F i)
    refine ⟨n, ?_⟩
    rw [← hn, he, integralBasis_apply]
  choose n hn using hXe
  set c : F := e.traceDual.equivFun.symm (fun i => (n i : ℚ)) with hc
  have hrepr : ∀ i, Algebra.trace ℚ F (c * e i) = n i := by
    intro i
    have h1 := Module.Basis.traceDual_repr_apply e c i
    rw [Algebra.traceForm_apply] at h1
    rw [← h1, ← Module.Basis.equivFun_apply, hc, LinearEquiv.apply_symm_apply]
  refine ⟨c, fun w => ?_⟩
  have hz : ∀ t : F, ∑ w, ρ w t * (ρ w c - X w) = 0 := by
    let Lf : F →ₗ[ℚ] ℝ := ∑ w, (ρ w c - X w) • (ρ w).toRatAlgHom.toLinearMap
    have hL : Lf = 0 := by
      refine e.ext fun i => ?_
      have h2 := GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ (c * e i)
      rw [hrepr] at h2
      simp only [Lf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
        AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply]
      simp only [map_mul] at h2
      have h3 : ∑ w, (ρ w c - X w) * ρ w (e i) = ∑ w, ρ w c * ρ w (e i) - ∑ w, ρ w (e i) * X w := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring
      rw [h3, h2, hn]
      simp
    intro t
    have := LinearMap.congr_fun hL t
    simp only [Lf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
      AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have := coeff_eq_zero ρ hρ _ hz w
  linarith

def eR (s : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))

theorem eR_add (s u : ℝ) : eR (s + u) = eR s * eR u := by
  simp only [eR, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eR_zero : eR 0 = 1 := by simp [eR]

theorem eR_int {s : ℝ} (h : eR s = 1) : ∃ n : ℤ, s = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h1 : (s : ℂ) = n := by
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    rw [hn]
    ring
  exact_mod_cast h1

theorem sub_field (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (ψf : AddChar (A F) ℂ)
    (hstd : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) {X : InfinitePlace F → ℝ} {y : A F}
    (H : ∀ t : F, eR (∑ w, ρ w t * X w) * ψf (algebraMap F (A F) t * y) = 1) (c : F) (t : F) :
    eR (∑ w, ρ w t * (X w - ρ w c)) * ψf (algebraMap F (A F) t * (y - algebraMap F (A F) c)) = 1 := by
  have hT : eR (∑ w, ρ w (t * c)) * ψf (algebraMap F (A F) (t * c)) = 1 := by
    rw [GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ, hstd.2, eR, ← Complex.exp_add]
    have h0 : 2 * (Real.pi : ℂ) * Complex.I * (((Algebra.trace ℚ F (t * c) : ℚ) : ℝ) : ℂ) +
        -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℚ F (t * c) : ℚ) : ℂ) = 0 := by
      push_cast
      ring
    rw [h0, Complex.exp_zero]
  have e1 : ∑ w, ρ w t * X w = ∑ w, ρ w t * (X w - ρ w c) + ∑ w, ρ w (t * c) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [map_mul]; ring
  have e2 : algebraMap F (A F) t * y =
      algebraMap F (A F) t * (y - algebraMap F (A F) c) + algebraMap F (A F) (t * c) := by
    rw [map_mul]
    ring
  have h := H t
  rw [e1, e2, eR_add, AddChar.map_add_eq_mul] at h
  have key : ∀ p q r s : ℂ, (p * q) * (r * s) = 1 → q * s = 1 → p * r = 1 :=
    fun p q r s h1 h2 => by linear_combination h1 - p * r * h2
  exact key _ _ _ _ h hT

theorem core (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (ψf : AddChar (A F) ℂ)
    (hstd : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) (X : InfinitePlace F → ℝ) (y : A F)
    (H : ∀ t : F, eR (∑ w, ρ w t * X w) * ψf (algebraMap F (A F) t * y) = 1) :
    ∃ c : F, (∀ w, X w = ρ w c) ∧ y = algebraMap F (A F) c := by
  obtain ⟨-, -, -, -, hOo, hden, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hopen : IsOpen {z : A F | y - z ∈ Oh F} := hOo.preimage (continuous_const.sub continuous_id)
  obtain ⟨c1, hc1⟩ := hden.exists_mem_open hopen ⟨y, by
    show y - y ∈ Oh F
    rw [sub_self]
    exact (ohG F).zero_mem⟩
  have hc1' : y - algebraMap F (A F) c1 ∈ Oh F := hc1
  have H1 := sub_field hF ρ hρ ψf hstd H c1
  have hXint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, ρ w (r : F) * (X w - ρ w c1) = n := by
    intro r
    have h1 := H1 r
    rw [((GlobalTheory.T.standard_adelic_character F).2 ψf hstd).2.1 _ (oh_mul ((hint _).2 ⟨r, rfl⟩) hc1'), mul_one] at h1
    exact eR_int h1
  obtain ⟨c2, hc2⟩ := real_eq_of_int hF ρ hρ _ hXint
  have H2 := sub_field hF ρ hρ ψf hstd H1 c2
  have hy0 : y - algebraMap F (A F) c1 - algebraMap F (A F) c2 = 0 := fin_eq_zero ψf hstd fun t => by
    have h1 := H2 t
    have h0 : ∑ w, ρ w t * ((X w - ρ w c1) - ρ w c2) = 0 :=
      Finset.sum_eq_zero fun w _ => by rw [← hc2 w, sub_self, mul_zero]
    rwa [h0, eR_zero, one_mul] at h1
  refine ⟨c1 + c2, fun w => ?_, ?_⟩
  · have := hc2 w
    rw [map_add]
    linarith
  · rw [map_add]
    linear_combination hy0

end Core

theorem annihilator_eq : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ x : AF F, (∀ t : F, ψ (algebraMap F (AF F) t * x) = 1) → ∃ c : F, x = algebraMap F (AF F) c := by
  intro F _ _ hF ψ hψ x hx
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF
  obtain ⟨a, ha, hinf, ψf, hstd, hfin⟩ := GlobalTheory.T.adelic_character_archimedean_form F hF ρ e hρ he heρ ψ hψ
  have hsplit : ∀ (u : Ainf F) (v : Af F),
      ψ (u, v) = eR (∑ w, ρ w a * e u w) * ψf (algebraMap F (Af F) a * v) := by
    intro u v
    have h : ((u, v) : AF F) = pairA F u 0 + pairA F 0 v := by
      show ((u, v) : Ainf F × Af F) = ((u, 0) : Ainf F × Af F) + ((0, v) : Ainf F × Af F)
      rw [Prod.mk_add_mk, add_zero, zero_add]
    rw [h, AddChar.map_add_eq_mul, hinf, hfin]
    rfl
  have H : ∀ t : F, eR (∑ w, ρ w t * (ρ w a * e x.1 w)) *
      ψf (algebraMap F (Af F) t * (algebraMap F (Af F) a * x.2)) = 1 := by
    intro t
    have h := hx t
    have hm : algebraMap F (AF F) t * x =
        (algebraMap F (Ainf F) t * x.1, algebraMap F (Af F) t * x.2) := rfl
    rw [hm, hsplit] at h
    have e1 : ∑ w, ρ w a * e (algebraMap F (Ainf F) t * x.1) w = ∑ w, ρ w t * (ρ w a * e x.1 w) :=
      Finset.sum_congr rfl fun w _ => by rw [map_mul, Pi.mul_apply, heρ]; ring
    have e2 : algebraMap F (Af F) a * (algebraMap F (Af F) t * x.2) =
        algebraMap F (Af F) t * (algebraMap F (Af F) a * x.2) := mul_left_comm _ _ _
    rw [e1, e2] at h
    exact h
  obtain ⟨c, hc1, hc2⟩ := core hF ρ hρ ψf hstd _ _ H
  refine ⟨a⁻¹ * c, ?_⟩
  have hx1 : x.1 = algebraMap F (Ainf F) (a⁻¹ * c) := by
    apply e.injective
    funext w
    rw [heρ, map_mul, map_inv₀]
    have hne : ρ w a ≠ 0 := (map_ne_zero _).2 ha
    have h1 := hc1 w
    rw [← h1]
    field_simp
  have hx2 : x.2 = algebraMap F (Af F) (a⁻¹ * c) := by
    rw [map_mul, ← hc2, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  exact Prod.ext hx1 hx2

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSchwartzBruhatCompactSupportNonzero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest

open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

theorem exists_compactSupport_ne_zero :
    ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι],
      ∃ f ∈ schwartzBruhatPi F ι, HasCompactSupport f ∧ f 0 ≠ 0 := by
  intro F _ _ ι _ _
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (0 : ι → 𝔸[F])
  obtain ⟨r, -, -, hr0, hrU, hrS⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_bump (K := F) 0 U hU
  refine ⟨_, hrS, HasCompactSupport.intro hUc fun x hx => ?_, ?_⟩
  · have : r x = 0 := by
      by_contra h
      exact hx (hrU x h)
    simp [this]
  · exact_mod_cast hr0.ne'

end GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.InducedCellSemisimplificationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_cell_semisimplification : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k := by
  first | exact @GlobalTheory.CompanionTheory.Glob.cellSemisimplification | exact GlobalTheory.CompanionTheory.Glob.cellSemisimplification | (intros; apply GlobalTheory.CompanionTheory.Glob.cellSemisimplification <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemAnnihilatorSmallBallEventually
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

variable {F : Type} [Field F] [NumberField F]

theorem singleV_apply_self' (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) : (singleV F v s) v = s := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v s

theorem singleV_apply_ne' (v w : HeightOneSpectrum (𝓞 F)) (s : Fv F v) (h : w ≠ v) :
    (singleV F v s) w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) s h

theorem singleV_mul_box (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) (b : Af F) :
    singleV F v s * b = singleV F v (s * b v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change (singleV F v s) w * b w = (singleV F v (s * b v)) w
  by_cases h : w = v
  · subst h
    rw [singleV_apply_self', singleV_apply_self']
  · rw [singleV_apply_ne' v w _ h, singleV_apply_ne' v w _ h, zero_mul]

open Classical in
theorem sum_singleV_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (c : Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (∑ v ∈ T, singleV F v (c v)) w = if w ∈ T then c w else 0 := by
  classical
  have h1 : (∑ v ∈ T, singleV F v (c v)) w = ∑ v ∈ T, (singleV F v (c v)) w :=
    map_sum (evalV F w) _ T
  rw [h1]
  split_ifs with hw
  · rw [Finset.sum_eq_single w (fun v _ hv => singleV_apply_ne' v w _ (Ne.symm hv))
      (fun h => absurd hw h), singleV_apply_self']
  · exact Finset.sum_eq_zero fun v hv => singleV_apply_ne' v w _ (fun h => hw (h ▸ hv))

theorem singleV_mem_boxA (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hU : ∀ v, (0 : Fv F v) ∈ U v) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v)
    (hS : v ∈ S → s ∈ U v) (hO : v ∉ S → s ∈ v.adicCompletionIntegers F) :
    singleV F v s ∈ Coef.boxA S U := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · by_cases h : w = v
    · subst h; rw [singleV_apply_self']; exact hS hw
    · rw [singleV_apply_ne' v w _ h]; exact hU w
  · by_cases h : w = v
    · subst h; rw [singleV_apply_self']; exact hO hw
    · rw [singleV_apply_ne' v w _ h]; exact zero_mem _

theorem annF_boxA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  intro F _ _ ψ hψ S hS U hU
  classical
  ext b
  constructor
  · intro hb
    have key : ∀ v (s : Fv F v), (v ∈ S → s ∈ U v) → (v ∉ S → s ∈ v.adicCompletionIntegers F) →
        psiV F ψ v (s * b v) = 1 := by
      intro v s h1 h2
      have := hb _ (singleV_mem_boxA S U hU v s h1 h2)
      rwa [singleV_mul_box, psiF_singleV] at this
    refine ⟨fun v hv s hs => key v s (fun _ => hs) (fun h => absurd hv h), fun v hv => ?_⟩
    have hmem : b v ∈ annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) :=
      fun s hs => key v s (fun h => absurd h hv) (fun _ => hs)
    rw [hS v hv] at hmem
    exact hmem
  · rintro ⟨hb1, hb2⟩ y ⟨hy1, hy2⟩
    obtain ⟨T, hT⟩ := GlobalTheory.T.adelic_character_trivial_almost_everywhere F ψ hψ
    set c := y * b with hc
    have hcv : ∀ v, c v = y v * b v := fun v => rfl
    set T' := T ∪ S with hT'
    set e : Af F := ∑ v ∈ T', singleV F v (c v) with he
    have hcint : ∀ v, v ∉ S → c v ∈ v.adicCompletionIntegers F := fun v hv => by
      rw [hcv]; exact mul_mem (hy2 v hv) (hb2 v hv)
    have hd : psiF ψ (c - e) = 1 := by
      have happ : ∀ w, (c - e) w = c w - (if w ∈ T' then c w else 0) := fun w => by
        rw [← sum_singleV_apply T' c w]; rfl
      refine hT _ (fun w => ?_) (fun w hw => ?_)
      · rw [happ]
        split_ifs with h
        · rw [sub_self]; exact zero_mem _
        · rw [sub_zero]
          exact hcint w (fun hw => h (Finset.mem_union_right _ hw))
      · rw [happ, if_pos (Finset.mem_union_left _ hw), sub_self]
    have hsum : psiF ψ e = 1 := by
      rw [he]
      refine Finset.sum_induction _ (fun x => psiF ψ x = 1) (fun a b ha hb => by rw [psiF_add, ha, hb, one_mul])
        (psiF_zero ψ) (fun v _ => ?_)
      rw [psiF_singleV]
      by_cases hv : v ∈ S
      · rw [hcv]; exact hb1 v hv (y v) (hy1 v hv)
      · have h1 : c v ∈ annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) := by
          rw [hS v hv]; exact hcint v hv
        have := h1 1 (one_mem _)
        rwa [one_mul] at this
    have : c = (c - e) + e := by abel
    change psiF ψ c = 1
    rw [this, psiF_add, hd, hsum, one_mul]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

