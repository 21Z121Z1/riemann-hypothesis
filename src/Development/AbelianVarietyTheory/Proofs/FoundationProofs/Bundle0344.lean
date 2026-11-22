import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.FrobeniusPowerCompatibility
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0343
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuadCharOfOfIsNormChar
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Published UpperTheory.V.Af.Bc

namespace GlobalTheory.QuadNormChar

theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem tendsto_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem fixes_or {F E Ω : Type} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosed Ω] [CharZero F] (h2 : Module.finrank F E = 2) (σ : G F Ω)
    (hσ : ∃ e : E, σ (algebraMap E Ω e) ≠ algebraMap E Ω e) (τ : G F Ω) :
    τ ∈ (res F Ω E).range ∨ σ⁻¹ * τ ∈ (res F Ω E).range := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hfix : ∀ ρ : G F Ω, (∀ e : E, ρ (algebraMap E Ω e) = algebraMap E Ω e) → ρ ∈ (res F Ω E).range :=
    fun ρ hρ => ⟨AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) hρ, AlgEquiv.ext fun _ => rfl⟩
  let f : G F Ω → (E →ₐ[F] Ω) := fun ρ => (ρ : Ω →ₐ[F] Ω).comp (IsScalarTower.toAlgHom F E Ω)
  have hf : ∀ ρ e, f ρ e = ρ (algebraMap E Ω e) := fun _ _ => rfl
  have hcard : Fintype.card (E →ₐ[F] Ω) = 2 := by rw [AlgHom.card, h2]
  obtain ⟨e₀, he₀⟩ := hσ
  have h01 : f 1 ≠ f σ := fun h => he₀ (by have := DFunLike.congr_fun h e₀; rw [hf, hf] at this; exact this.symm)
  by_cases h1 : f τ = f 1
  · left
    exact hfix τ fun e => by have := DFunLike.congr_fun h1 e; rw [hf, hf] at this; exact this
  · by_cases h2' : f τ = f σ
    · right
      refine hfix _ fun e => ?_
      have := DFunLike.congr_fun h2' e
      rw [hf, hf] at this
      rw [AlgEquiv.mul_apply, this]
      exact σ.symm_apply_apply _
    · exfalso
      have : 2 < Fintype.card (E →ₐ[F] Ω) :=
        Fintype.two_lt_card_iff.2 ⟨f 1, f σ, f τ, h01, Ne.symm h1, Ne.symm h2'⟩
      omega

end GlobalTheory.QuadNormChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetModuleMaximalParabolicPrincipalSeriesType
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem exists_uniformiser_max (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ ϖ : k, ϖ ≠ 0 ∧ valuation k ϖ < 1 ∧ ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ := by
  set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  obtain ⟨x, hx⟩ := valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hx' : e (valuation k x) = WithZero.exp (-1 : ℤ) := by rw [hx]; simp
  refine ⟨x, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero, map_zero] at hx'
    exact WithZero.zero_ne_coe hx'
  · rw [← e.strictMono.lt_iff_lt, hx', map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro y hy
    rw [← e.strictMono.le_iff_le, hx']
    have hlt : e (valuation k y) < 1 := by rw [← map_one e]; exact e.strictMono hy
    rcases eq_or_ne (e (valuation k y)) 0 with h | h
    · rw [h]; exact zero_le'
    · rw [← WithZero.exp_log h] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]; omega

theorem eig_jacquet_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Cut ψ r → ∀ v ∈ twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  intro k _ _ _ _ r t ψ V _ _ π hπ hψ hord hcut v hv heig
  obtain ⟨ϖ, hϖ0, hϖ1, hϖmax⟩ := exists_uniformiser_max k
  let z : GL (Fin (r + t)) k := diagT k (Fin (r + t)) (fun i => if (i : ℕ) < r then Units.mk0 ϖ hϖ0 else 1)
  have hz : z.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then ϖ else 1) := by
    simp only [z]; rw [val_diagT]; congr 1; funext i; split_ifs <;> simp
  obtain ⟨hD, -⟩ := GlobalTheory.T.principalSeriesCongruenceSubgroup_smoothCharacterDatum k (r + t) ψ hψ hord
  obtain ⟨hSD, hSmono⟩ := GlobalTheory.T.compactSubgroupSmoothCharacterDatum_monotone k (r + t) ψ r ϖ hψ hϖ0 hϖ1 hϖmax
  obtain ⟨h0J, hθ1, h1KO, hconj⟩ := GlobalTheory.T.principalSeriesUnipotentStrip_properties k (r + t) ψ r ϖ hϖ0 hϖ1 hϖmax hcut
  obtain ⟨m, hm⟩ := GlobalTheory.T.twistedJacquetKernel_mem_twistedSpan_finite_stage _ V π _ (strip ψ r ϖ) hSmono (GlobalTheory.T.strips_exhaust_parabolicUnipotentRadical k r t ψ ϖ hψ hϖ0 hϖ1 hϖmax) v hv
  refine GlobalTheory.T.eigenvector_eq_zero_of_mem_twistedSpan_chain (GL (Fin (r + t)) k) V π hπ (grp ψ) (strip ψ r ϖ) (theta ψ) z hD hSD hSmono
    (fun y hy => ⟨h0J y hy, hθ1 0 y hy⟩) (hconj z hz) ?_ ?_ m v hm heig
  · intro y hy
    by_cases hyJ : y ∈ grp ψ
    · exact Or.inl ⟨hyJ, hθ1 1 y hy⟩
    · exact Or.inr (GlobalTheory.T.principalSeriesType_not_intertwine_outside k (r + t) ψ hord y (h1KO y hy) hyJ)
  · intro j hj
    obtain ⟨y, hy, hblk⟩ := GlobalTheory.T.exists_strip_clearing_upperRight_principalSeriesCongruence k (r + t) ψ r ϖ hord hcut j hj
    have hyJ : y ∈ grp ψ := h0J y hy
    have hyinv : y⁻¹ ∈ grp ψ := hD.inv y hyJ
    have hg : y⁻¹ * j ∈ grp ψ := hD.mul _ hyinv _ hj
    obtain ⟨h1, h2⟩ := GlobalTheory.T.conj_blockLower_mem_principalSeriesCongruence k (r + t) ψ r ϖ hϖ0 hϖ1 z hz (y⁻¹ * j) hg hblk
    refine ⟨y, hy, h1, ?_⟩
    rw [h2, GlobalTheory.T.principalSeriesTypeCharacter_mul k (r + t) ψ hord _ hyinv _ hj, hθ1 0 _ ((hSD 0).inv y hy), one_mul]

end GlobalTheory.PsType
end

