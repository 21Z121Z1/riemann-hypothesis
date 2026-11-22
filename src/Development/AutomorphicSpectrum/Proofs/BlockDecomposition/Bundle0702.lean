import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPlaneUnfoldingIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0321
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0377
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0688
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianVolumeOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0525
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0472
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0016
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0355
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0415
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeVectorLinearCombination
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.HeckeSum

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem heckeVec_finset_sum {ι : Type} (ρ : Representation ℂ G V) (K : Subgroup G) (s : Finset ι) (f : ι → ℂ)
    (h : ι → G → ℂ) (x : V) (hf : ∀ p ∈ s, {c : G ⧸ K | h p c.out ≠ 0}.Finite) :
    heckeVec ρ K (fun g => ∑ p ∈ s, f p * h p g) x = ∑ p ∈ s, f p • heckeVec ρ K (h p) x := by
  have e : ∀ c : G ⧸ K, (∑ p ∈ s, f p * h p c.out) • ρ c.out x =
      ∑ p ∈ s, f p • (h p c.out • ρ c.out x) := fun c => by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun p _ => mul_smul _ _ _
  unfold heckeVec
  rw [finsum_congr e, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_finsum]
  · intro p hp
    exact (hf p hp).subset fun c hc h0 => hc (by simp [h0])

theorem biInv_out {K : Subgroup G} {h : G → ℂ} (hh : IsBiInv K h) (g : G) :
    h ((g : G ⧸ K).out) = h g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  have e := hh 1 k g
  simp only [OneMemClass.coe_one, one_mul] at e
  rw [hk, e]

variable {A B : Type} [Group A] [Group B]

theorem finite_pair {KA : Subgroup A} {KB : Subgroup B} {fA : A → ℂ} {fB : B → ℂ}
    (hA : IsBiInv KA fA) (hB : IsBiInv KB fB) (fa : {c : A ⧸ KA | fA c.out ≠ 0}.Finite)
    (fb : {c : B ⧸ KB | fB c.out ≠ 0}.Finite) :
    {c : (A × B) ⧸ KA.prod KB | fA c.out.1 * fB c.out.2 ≠ 0}.Finite := by
  refine Set.Finite.of_finite_image
    (f := fun c : (A × B) ⧸ KA.prod KB => (((c.out.1 : A ⧸ KA)), ((c.out.2 : B ⧸ KB))))
    ((fa.prod fb).subset ?_) ?_
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : fA c.out.1 * fB c.out.2 ≠ 0 := hc
    refine ⟨?_, ?_⟩
    · change fA ((c.out.1 : A ⧸ KA).out) ≠ 0
      rw [biInv_out hA]
      exact left_ne_zero_of_mul hc'
    · change fB ((c.out.2 : B ⧸ KB).out) ≠ 0
      rw [biInv_out hB]
      exact right_ne_zero_of_mul hc'
  · intro c _ d _ e
    have e1 := QuotientGroup.eq.1 (congrArg Prod.fst e)
    have e2 := QuotientGroup.eq.1 (congrArg Prod.snd e)
    rw [← c.out_eq', ← d.out_eq']
    exact QuotientGroup.eq.2 (Subgroup.mem_prod.2 ⟨by simpa using e1, by simpa using e2⟩)

end Abstract

theorem heckeVec_Tj_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℂ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : V),
    heckeVec ρ (K2 a b w) (fun g => ∑ p ∈ s, f p * (Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2)) x =
      ∑ p ∈ s, f p • heckeVec ρ (K2 a b w) (fun g => Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2) x := by
  intro E _ _ _ a b w ϖ hϖ s f V _ _ ρ x
  refine heckeVec_finset_sum ρ (K2 a b w) s f
    (fun p g => Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2) x fun p _ => ?_
  have ha := Tj_mem_hecke (n := a) hϖ p.1
  have hb := Tj_mem_hecke (n := b) hϖ p.2
  exact finite_pair ha.1 hb.1 (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w a) ha.2)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w b) hb.2)

end GlobalTheory.CompanionTheory.CtS.HeckeSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPlaneUnfoldingIntegralStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_plane_unfolding_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (μ : Measure (HA (AF F) σ (hypOne J))) 𝓕, IsHaarH F E σ (M + 2) (hypOne J) μ → IsFDH F E σ (M + 2) (hypOne J) μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA → ∀ (Φ : (Fin (n + 1) → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (hypOne J), Ψ (actW (AF F) σ (hypOne J) h (e0 _ M)) = ∫⁻ Y, ∫⁻ a, Φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E)))) → ∫⁻ X, Φ X ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E))) = ∫⁻ y, Ψ y ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.unfold_frames | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.unfold_frames | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.unfold_frames <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Imports
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem prod₂_detRep_isIrreducible :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      JacquetOfInducedFiltration k) →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ →
      IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) →
      (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible := by
  intro hJ k _ _ _ _ a b χ₁ χ₂ s₁ s₂ u₁ u₂ hne
  haveI := GlobalTheory.CompanionTheory.DegPrinSeries.nontrivial_subrepresentation k a b χ₁ χ₂ s₁ s₂
  show IsSimpleOrder (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b)))
    ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)))
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hc⟩ := GlobalTheory.T.admissible_unitary_semisimple _ (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k (a + b))
    (GlobalTheory.CompanionTheory.DegenSeries.isAdmissible_degenerate k a b χ₁ χ₂ s₁ s₂)
    (GlobalTheory.CompanionTheory.DegenerateSeries.isUnitarisable_degenerateSeries k a b χ₁ χ₂ s₁ s₂ u₁ u₂) W
  by_contra h
  push_neg at h
  have hW' : W' ≠ ⊥ := by
    rintro rfl
    exact h.2 (eq_top_of_isCompl_bot hc)
  exact GlobalTheory.T.induced_two_characters_not_scalar k a b χ₁ χ₂ W W' hc h.1 hW'
    (GlobalTheory.T.jacquet_induced_two_characters k a b χ₁ χ₂ (hJ k) s₁ s₂ u₁ u₂ hne)

end GlobalTheory.CompanionTheory.SmGL.Bernstein
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableRadialCutoffWeightStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_radial_cutoff_weight : ∀ σ : ℝ, 0 < σ → σ < 1 → Integrable (fun p : ℝ × ℝ =>
    (p.1 ^ 2 + p.2 ^ 2) ^ (-1 - σ / 2) * ((p.1 ^ 2 + p.2 ^ 2) / max |p.1| |p.2|) *
      (GlobalTheory.CompanionTheory.PerUInt.phi p.1 * GlobalTheory.CompanionTheory.PerUInt.phi p.2)) := by
  first | exact @GlobalTheory.CompanionTheory.PerUInt.Outer.integrable_firstColumn | exact GlobalTheory.CompanionTheory.PerUInt.Outer.integrable_firstColumn | (intros; apply GlobalTheory.CompanionTheory.PerUInt.Outer.integrable_firstColumn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianVolumeOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_hermitian_volume_one : PositivityTheory.SiegelWeilFormula.Gunr.HermitianLatticeVolumeOne := by
  first | exact @GlobalTheory.CompanionTheory.GoodHerm.volume_integral_hermitian_one | exact GlobalTheory.CompanionTheory.GoodHerm.volume_integral_hermitian_one | (intros; apply GlobalTheory.CompanionTheory.GoodHerm.volume_integral_hermitian_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicSmooth
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem pairing_phi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ]
        TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ,
      (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ hψ h1 n s V V' _ _ _ _ T T' hT hT' B hB hnd
  borelize k
  let ν : Measure k := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hinv : TwInv T T' B s := hB
  have hlin := GlobalTheory.T.mirabolic_evaluation_linear ν ψ T B hψ hT
  have hex := GlobalTheory.T.mirabolic_pairing_exists_eventual_value ν ψ c T T' B s hψ hc hT hT' hinv
  have huniq : ∀ {v v' A A'}, EvVal ν ψ T B v v' A → EvVal ν ψ T B v v' A' → A = A' := by
    rintro v v' A A' ⟨t₀, h₀⟩ ⟨t₁, h₁⟩
    rcases le_total (valuation k (t₀ : k)) (valuation k (t₁ : k)) with h | h
    · rw [← h₀ t₁ h, h₁ t₁ le_rfl]
    · rw [← h₀ t₀ le_rfl, h₁ t₀ h]
  choose f hf using hex
  let B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ f
    (fun v₁ v₂ v' => huniq (hf _ _) (hlin.1 _ _ _ _ _ (hf _ _) (hf _ _)))
    (fun z v v' => huniq (hf _ _) (hlin.2.1 _ _ _ _ (hf _ _)))
    (fun v v₁ v₂ => huniq (hf _ _) (hlin.2.2.1 _ _ _ _ _ (hf _ _) (hf _ _)))
    (fun z v v' => huniq (hf _ _) (hlin.2.2.2 _ _ _ _ (hf _ _)))
  have hB₀ : ∀ v v', B₀ v v' = f v v' := fun _ _ => rfl
  refine GlobalTheory.T.twisted_invariant_pairing_character ψ n s V V' T T' B₀ ?_ ?_ ?_ ?_
  · intro y v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_depth_induction ν ψ T T' B s hψ hT hinv y v v' _ (hf _ _)).1
  · intro y v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_depth_induction ν ψ T T' B s hψ hT hinv y v v' _ (hf _ _)).2
  · intro p v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (GlobalTheory.T.mirabolic_pairing_conductor_shift ν ψ c T T' B s hψ hc hT hT' hinv p v v' _ (hf _ _))
  · intro v hv
    obtain ⟨v', A, hA, hA0⟩ := GlobalTheory.T.mirabolic_pairing_conductor_extension ν ψ c T T' B s hψ hc hT hT' hinv hnd v hv
    exact ⟨v', by rw [hB₀, huniq (hf _ _) hA]; exact hA0⟩

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InversePointTorusScalingStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_point_torus_scaling : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ (ξ : Matrix (Fin V.rank) (Fin 1) D.host.E), (invPt V a ξ).map (finPart D) = ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) ∧ ∀ ρ, (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => ((t i : ℂ))⁻¹) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ξ).map (tauE D ρ)) ∧ (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => (t i : ℂ)) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ξ).map (tauE D ρ)) ∧ (((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ).map (tauE D ρ)) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCoord.torus_coords | exact GlobalTheory.CompanionTheory.TorusCoord.torus_coords | (intros; apply GlobalTheory.CompanionTheory.TorusCoord.torus_coords <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegment
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegFineCons

theorem finSigmaFinEquiv_one_val {s : ℕ} (i : Fin s) (b : Fin 1) :
    ((finSigmaFinEquiv (m := s) (n := fun _ => 1) ⟨i, b⟩ : Fin _) : ℕ) = i := by
  rw [finSigmaFinEquiv_apply, Subsingleton.elim b 0]
  simp

theorem eq_one_of_sum_eq {s : ℕ} (c : Fin s → ℕ) (h1 : ∀ a, 1 ≤ c a) (h : ∑ a, c a = s) (a : Fin s) : c a = 1 := by
  have h2 : ∑ _a : Fin s, 1 = ∑ a, c a := by simpa using h.symm
  exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => h1 i)).1 h2 a (Finset.mem_univ a)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem sum_concat_fst {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ b, (x a b).1 := by
  rw [← Fintype.sum_sigma' (fun a b => (x a b).1)]
  exact Equiv.sum_comp finSigmaFinEquiv.symm (fun p : Σ a, Fin (c a) => (x p.1 p.2).1)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem concat_finSigmaFinEquiv {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) (p : Σ a, Fin (c a)) :
    concat c x (finSigmaFinEquiv p) = x p.1 p.2 := by
  have key : ∀ q : Σ a, Fin (c a), q = p → x q.1 q.2 = x p.1 p.2 := by
    rintro _ rfl
    rfl
  exact key _ (Equiv.symm_apply_apply _ _)

theorem exists_cusp_word (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : IrrGL k) :
    ∃ (c : ℕ) (x : Fin c → IrrGL k) (hd : ∑ b, (x b).1 = y.1), (∀ b, (x b).IsCusp) ∧ 1 ≤ jm x hd y.rep := by
  obtain ⟨c, x, hd, hc, φ, hφ⟩ := GlobalTheory.CompanionTheory.SubEmb.subEmbedding k y.1 _ y.rep y.2.rep.smooth y.2.rep.irr
  have := Model.nontrivial_of_isIrreducible y.2.rep.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.2.rep.V)
  exact ⟨c, x, hd, hc, GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA x hd _ y.2.rep.smooth φ
    ⟨v, fun h => hv (hφ (h.trans (map_zero φ).symm))⟩⟩

theorem equiv_piTensor_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJac Γ) (u : IrrGL k) (hu : IsLSeg Γ u.rep) (hs : ∑ i, (dec Γ i).1 = u.1) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Levi k fun i => Fin ((dec Γ i).1)) X), ρ.IsIrreducible → IsSubquotient ρ (jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep) → Nonempty (ρ.Equiv (piTensor fun i => (dec Γ i).rep)) := by
  intro k _ _ _ _ hA Γ hF u hu hs X _ _ ρ hi hsub
  have hsm : IsSmooth ρ := hsub.isSmooth (isSmooth_jac _ u.2.rep.smooth)
  obtain ⟨σ, ⟨E⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (fun i => (dec Γ i).1) (⟨X, ρ, hsm, hi⟩ : IrrRep _)
  replace E : ρ.Equiv (piTensor fun a => (σ a).rep.ρ) := E
  suffices hσ : σ = fun a => (dec Γ a).2 by
    subst hσ
    exact ⟨E⟩
  let y : Fin Γ.len → IrrGL k := fun i => ⟨(dec Γ i).1, σ i⟩
  have hy : ∑ a, (y a).1 = u.1 := hs
  have h1 : 1 ≤ jm y hy u.rep := Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2
    ((IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans hsub))
  choose c x hd hcusp hpos using fun a => exists_cusp_word hA (y a)
  have hcat : ∑ i, (concat c x i).1 = u.1 := by
    rw [sum_concat_fst, ← hy]
    exact Finset.sum_congr rfl fun a _ => hd a
  have h2 : 1 ≤ jm (concat c x) hcat u.rep := h1.trans
    (GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat hA y hy c x hd hcat hpos u.rep u.2.rep.smooth
      (hasFiniteLength_of_isIrreducible u.2.rep.irr))
  obtain ⟨h, hcon⟩ := (hF u.rep hu).2 _ (concat c x) hcat (fun a => hcusp _ _) h2
  have hc0 : ∀ a, 1 ≤ c a := fun a => by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; exact Fin.isEmpty
    have h3 : (y a).1 = 0 := by rw [← hd a]; simp
    exact Γ.d_pos.ne' h3
  obtain rfl : c = fun _ => 1 := funext (eq_one_of_sum_eq c hc0 h)
  funext a
  have h3 : x a 0 = dec Γ (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) :=
    (concat_finSigmaFinEquiv _ x ⟨a, 0⟩).symm.trans (hcon (finSigmaFinEquiv ⟨a, 0⟩))
  have h4 : dec Γ (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) = dec Γ a :=
    congrArg _ (Fin.ext (finSigmaFinEquiv_one_val a 0))
  have h5 : x a 0 = y a := GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm (y a) (y a).rep (.refl _) (x a) (hd a) (hpos a)
  have h6 : (⟨(dec Γ a).1, σ a⟩ : IrrGL k) = ⟨(dec Γ a).1, (dec Γ a).2⟩ := (h5.symm.trans h3).trans h4
  exact sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h6

end GlobalTheory.CompanionTheory.SegFineCons

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangularStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_unitary_upper_triangular : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ), IsUnit g → ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ, g = k * b ∧ b.BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular | exact GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular | (intros; apply GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIndicatorIntegralIndex
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintInd

theorem finsum_out_indicator {A : Type} [AddCommGroup A] (S Λ : AddSubgroup A) (hSΛ : S ≤ Λ)
    (K : Subgroup (Multiplicative A)) (hK : ∀ X, X ∈ K ↔ Multiplicative.toAdd X ∈ S) :
    ∑ᶠ q : Multiplicative A ⧸ K, (if Multiplicative.toAdd q.out ∈ Λ then (1 : ℂ) else 0) =
      ((S.relIndex Λ : ℕ) : ℂ) := by
  have hrep : ∀ x : Multiplicative A,
      Multiplicative.toAdd ((x : Multiplicative A ⧸ K).out) ∈ Λ ↔ Multiplicative.toAdd x ∈ Λ := by
    intro x
    have h1 : ((x : Multiplicative A ⧸ K).out)⁻¹ * x ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (x : Multiplicative A ⧸ K))
    have h2 : -Multiplicative.toAdd ((x : Multiplicative A ⧸ K).out) + Multiplicative.toAdd x ∈ Λ :=
      hSΛ ((hK _).1 h1)
    constructor
    · intro h
      have := Λ.add_mem h h2
      simpa using this
    · intro h
      have := Λ.add_mem h (Λ.neg_mem h2)
      simpa using this
  let T : Set (Multiplicative A ⧸ K) := {q | Multiplicative.toAdd q.out ∈ Λ}
  have hsame : ∀ x y : Multiplicative A, (x : Multiplicative A ⧸ K) = y ↔
      -Multiplicative.toAdd x + Multiplicative.toAdd y ∈ S := by
    intro x y
    rw [QuotientGroup.eq, hK]
    rfl
  let f : Λ → T := fun x => ⟨((Multiplicative.ofAdd (x : A) : Multiplicative A) : Multiplicative A ⧸ K),
    (hrep _).2 x.2⟩
  let g : Λ ⧸ S.addSubgroupOf Λ → T := fun y => Quotient.liftOn' y f (by
    intro x y hxy
    have h : -(x : A) + (y : A) ∈ S := by
      have := QuotientAddGroup.leftRel_apply.1 hxy
      simpa [AddSubgroup.mem_addSubgroupOf] using this
    exact Subtype.ext ((hsame _ _).2 h))
  have hg : Function.Bijective g := by
    constructor
    · intro y₁ y₂
      induction y₁ using QuotientAddGroup.induction_on with | H x =>
      induction y₂ using QuotientAddGroup.induction_on with | H y =>
      intro h
      have h' : ((Multiplicative.ofAdd (x : A) : Multiplicative A) : Multiplicative A ⧸ K) =
          ((Multiplicative.ofAdd (y : A) : Multiplicative A) : Multiplicative A ⧸ K) :=
        congrArg Subtype.val h
      refine QuotientAddGroup.eq.2 ?_
      rw [AddSubgroup.mem_addSubgroupOf]
      simpa using (hsame _ _).1 h'
    · rintro ⟨q, hq⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨((⟨Multiplicative.toAdd x, (hrep x).1 hq⟩ : Λ) : Λ ⧸ S.addSubgroupOf Λ), rfl⟩
  have hcard : Nat.card T = S.relIndex Λ := (Nat.card_congr (Equiv.ofBijective g hg)).symm
  have hfun : (fun q : Multiplicative A ⧸ K => if Multiplicative.toAdd q.out ∈ Λ then (1 : ℂ) else 0) =
      T.indicator 1 := by
    funext q
    by_cases h : q ∈ T
    · rw [Set.indicator_of_mem h]; exact if_pos h
    · rw [Set.indicator_of_notMem h]; exact if_neg h
  rw [hfun, ← hcard]
  by_cases hT : T.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hT, Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card T hT]
    simp
  · rw [finsum_of_infinite_support (by simpa using hT)]
    haveI : Infinite T := Set.Infinite.to_subtype hT
    simp

theorem mem_intMat_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    X ∈ intMat a b w ↔ Multiplicative.toAdd X ∈ intSub a b w := by
  constructor
  · intro hX
    induction hX using Subgroup.closure_induction with
    | mem x hx => exact fun i j => hx i j
    | one => exact isInt_zero w _ _
    | mul x y _ _ hx hy => exact IsInt.add hx hy
    | inv x _ hx => exact IsInt.neg hx
  · intro hX
    exact Subgroup.subset_closure fun i j => hX i j

theorem hint_indicator_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E))), intSub a b w ≤ Λ → hint (intMat a b w) (fun X => if Multiplicative.toAdd X ∈ Λ then (1 : ℂ) else 0) = (((intSub a b w).relIndex Λ : ℕ) : ℂ) := by
  intro E _ _ _ a b w Λ h
  have hstab : intMat a b w ≤
      rStab (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        if Multiplicative.toAdd X ∈ Λ then (1 : ℂ) else 0) := by
    intro k hk x
    have hkΛ : Multiplicative.toAdd k ∈ Λ := h ((mem_intMat_iff a b w k).1 hk)
    have e : (Multiplicative.toAdd (x * k) ∈ Λ) ↔ Multiplicative.toAdd x ∈ Λ := by
      rw [toAdd_mul]
      exact Λ.add_mem_cancel_right hkΛ
    simp only [e]
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level _ (intMat a b w) (intMat a b w) _ le_rfl hstab
    (by simp [Subgroup.relIndex_self])]
  rw [Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_mul]
  exact finsum_out_indicator (intSub a b w) Λ h (intMat a b w) (mem_intMat_iff a b w)

end GlobalTheory.CompanionTheory.HintInd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelOpenCompactStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_level_open_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M N : ℕ), 0 < N →
    IsOpen (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ∧
    IsCompact (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_isOpen_isCompact | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_isOpen_isCompact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramifiedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_characters_unramified : PositivityTheory.SiegelWeilFormula.Gunr.LevChars := by
  first | exact @GlobalTheory.CompanionTheory.GunrLevChars.levChars | exact GlobalTheory.CompanionTheory.GunrLevChars.levChars | (intros; apply GlobalTheory.CompanionTheory.GunrLevChars.levChars <;> assumption)
end

