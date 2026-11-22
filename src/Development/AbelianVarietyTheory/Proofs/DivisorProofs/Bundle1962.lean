import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorCountBoundOfCosetDepthBound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedExponent
section
noncomputable section

namespace GlobalTheory.BotLValue

section General

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem gamma_ne_zero {s : ℂ} {n : ℤ} (h : 0 < 2 * s.re + ((|n| : ℤ) : ℝ)) :
    Complex.Gamma (s + ((|n| : ℤ) : ℂ) / 2) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by
    have e : (s + ((|n| : ℤ) : ℂ) / 2).re = s.re + ((|n| : ℤ) : ℝ) / 2 := by
      rw [Complex.add_re, ← Complex.ofReal_intCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [e]
    linarith)

theorem exists_isHeckeL_of_completed {χ : HChar E} {n : I → ℤ} {Λ : ℂ → ℂ} (h : IsCompletedL χ n Λ) :
    ∃ L, IsHeckeL χ L := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hA : ∀ (z : ℂ) i, (2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2))) ≠ 0 := fun z i =>
    mul_ne_zero two_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
  refine ⟨fun z => Λ z * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
    (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹), ?_, fun z hz => ?_⟩
  · refine h.1.mul (Differentiable.fun_finsetProd fun i _ => ?_)
    refine Differentiable.mul (fun z => ?_) ?_
    · refine DifferentiableAt.inv ?_ (hA z i)
      exact (((differentiableAt_id.add_const _).neg).const_cpow (Or.inl hpi)).const_mul 2
    · exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  · obtain ⟨L, h1, h2⟩ := h.2 z hz
    have key : archFactor n z * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹) = 1 := by
      unfold archFactor
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun i _ => ?_
      have h0 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
      rw [mul_mul_mul_comm, mul_inv_cancel₀ (hA z i), mul_inv_cancel₀ (gamma_ne_zero (by linarith)), one_mul]
    show HasProd _ (Λ z * _)
    rwa [h2, mul_comm (archFactor n z), mul_assoc, key, mul_one]

theorem exists_heckeL_ne_zero (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) [IsTotallyComplex E]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {n : I → ℤ} (hu : IsUnitary χ)
    (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0) :
    ∃ L, IsHeckeL χ L ∧ ∀ s : ℤ, (∀ i, 0 < 2 * s + |n i|) → L s ≠ 0 := by
  have hB := GlobalTheory.HeckeStrip.completedLBoundedInStrips
  have hn' : ∃ i, -n i ≠ 0 := hn.imp fun i h => neg_ne_zero.2 h
  have hi' := GlobalTheory.Published.HeckeFEModel.hasInf_inv hi
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  obtain ⟨Λ, hΛ, -⟩ := hB E I φ hφ χ n hu hi hn
  obtain ⟨Λ', hΛ', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -n i) hu' hi' hn'
  obtain ⟨L, hL⟩ := exists_isHeckeL_of_completed hΛ
  obtain ⟨L', hL'⟩ := exists_isHeckeL_of_completed hΛ'
  refine ⟨L, hL, fun s hs => ?_⟩
  rcases le_or_gt 1 s with h1 | h1
  · have e : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [← e]
    exact hL.ne_zero_nat hu (by omega)
  have g1 : ∀ i, Complex.Gamma ((1 - (s : ℂ)) + ((|-n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => gamma_ne_zero (by
    have h0 : (0 : ℝ) ≤ ((|-n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (-n i)
    have h2 : (s : ℝ) < 1 := by exact_mod_cast h1
    rw [Complex.sub_re, Complex.one_re, Complex.intCast_re]
    linarith)
  have hL1 : L' (1 - (s : ℂ)) ≠ 0 := by
    have e : (((1 - s).toNat : ℕ) : ℂ) = 1 - (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [← e]
    exact hL'.ne_zero_nat hu' (by omega)
  have hΛ'1 : Λ' (1 - (s : ℂ)) ≠ 0 := by
    rw [GlobalTheory.LValNe.completed_eq hΛ' hL' g1]
    exact mul_ne_zero (GlobalTheory.LValNe.archFactor_ne_zero g1) hL1
  have hΛs : Λ s ≠ 0 := fun h0 => hΛ'1 ((GlobalTheory.Published.HeckeFEModel.zero_iff hFE hφ hu hi hn hΛ hΛ' s).1 h0)
  have g0 : ∀ i, Complex.Gamma ((s : ℂ) + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => gamma_ne_zero (by
    rw [Complex.intCast_re]
    exact_mod_cast hs i)
  rw [GlobalTheory.LValNe.completed_eq hΛ hL g0] at hΛs
  exact right_ne_zero_of_mul hΛs

end General

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)

open NumberField IsDedekindDomain in
private theorem eq_or_eq_of_comp_eq_of_finrank_two {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2) (ψ : F →+* ℂ)
    (ρ α β : E →+* ℂ) (hρ : ρ.comp (algebraMap F E) = ψ) (hα : α.comp (algebraMap F E) = ψ)
    (hβ : β.comp (algebraMap F E) = ψ) (hαβ : α ≠ β) : ρ = α ∨ ρ = β := by
  classical
  letI : Algebra F ℂ := ψ.toAlgebra
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let mk : ∀ γ : E →+* ℂ, γ.comp (algebraMap F E) = ψ → E →ₐ[F] ℂ := fun γ hγ =>
    { toRingHom := γ
      commutes' := fun a => (congrArg (fun f : F →+* ℂ => f a) hγ : _) }
  have hcoe : ∀ (γ : E →+* ℂ) (hγ : γ.comp (algebraMap F E) = ψ), ((mk γ hγ : E →ₐ[F] ℂ) : E →+* ℂ) = γ :=
    fun γ hγ => rfl
  by_contra hne
  push_neg at hne
  have hcard := AlgHom.card F E ℂ
  rw [h2] at hcard
  have hfa : mk ρ hρ ≠ mk α hα := fun e => hne.1 (by rw [← hcoe ρ hρ, ← hcoe α hα, e])
  have hfb : mk ρ hρ ≠ mk β hβ := fun e => hne.2 (by rw [← hcoe ρ hρ, ← hcoe β hβ, e])
  have hab : mk α hα ≠ mk β hβ := fun e => hαβ (by rw [← hcoe α hα, ← hcoe β hβ, e])
  have h3 : ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hfa, hfb]), Finset.card_pair hab]
  have := Finset.card_le_univ ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ))
  omega

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.BotLValue.isCMType_embOver {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, _root_.GlobalTheory.AdelicU.EmbOver E w) :
    _root_.GlobalTheory.CMVal.IsCMType fun w => (τ w).1 := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt at h
  obtain ⟨hF, hE, h2, hσ⟩ := h
  unfold _root_.GlobalTheory.CMVal.IsCMType
  have hreal : ∀ v : InfinitePlace F, ComplexEmbedding.conjugate v.embedding = v.embedding :=
    fun v => ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp (hF.isReal v))
  have hconj : ∀ (v : InfinitePlace F) (γ : E →+* ℂ), γ.comp (algebraMap F E) = v.embedding →
      (ComplexEmbedding.conjugate γ).comp (algebraMap F E) = v.embedding := by
    intro v γ hγ
    rw [← hreal v, ← hγ]
    rfl
  have hτ : ∀ v : InfinitePlace F, ((τ v).1).comp (algebraMap F E) = v.embedding := fun v => (τ v).2
  have hne : ∀ v : InfinitePlace F, (τ v).1 ≠ ComplexEmbedding.conjugate (τ v).1 := by
    intro v e
    have hc := hE.isComplex (InfinitePlace.mk (τ v).1)
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff] at hc
    exact hc e.symm
  intro ρ
  set v := InfinitePlace.mk (ρ.comp (algebraMap F E)) with hvdef
  have hv : ρ.comp (algebraMap F E) = v.embedding := by
    rcases InfinitePlace.embedding_mk_eq (ρ.comp (algebraMap F E)) with e | e
    · exact e.symm
    · rw [← hreal v, e]
      exact (star_star _).symm
  refine ⟨v, eq_or_eq_of_comp_eq_of_finrank_two h2 v.embedding ρ _ _ hv (hτ v) (hconj v _ (hτ v)) (hne v), ?_⟩
  intro w hw
  have hw' : ρ.comp (algebraMap F E) = w.embedding := by
    rcases hw with e | e
    · rw [e]; exact hτ w
    · rw [e]; exact hconj w _ (hτ w)
  rw [hvdef, hw', InfinitePlace.mk_embedding]

theorem charL_holValueAt_ne_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (χ : Chr F E), IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ (k : InfinitePlace F → ℤ) (d : ℕ), HasExp B.emb χ k → (∀ w, (d : ℤ) < |k w|) → ∀ T : Finset (Pl F), UnrOff χ (T : Set (Pl F)) →
    (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → ¬ UnrAt χ w) → ∀ z : ℤ, -(d : ℤ) ≤ 2 * z →
      ∃ c : ℂ, c ≠ 0 ∧ GlobalTheory.Cont.HolValueAt (charL χ (T : Set (Pl F))) (z : ℂ) c := by
  intro hK F E _ _ _ _ _ σ B hB χ hχ _ k d hk hd T _ hram z hz
  have := hB.cm.2.1
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.HeckeBridge.exists_hchar F E σ hB.cm χ hχ
  have hi := hinf _ _ hk
  have hu := GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf E H _ _ hi
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨L, hL, hne⟩ := exists_heckeL_ne_zero hK.heckeTateFunctionalEquation.abs (isCMType_embOver hB.cm B.emb) hu hi
    ⟨w₀, fun h => by have := hd w₀; rw [h, abs_zero] at this; omega⟩
  have hun : ∀ w, UnrAt χ w ↔ H.UnrAt w := fun w => forall₂_congr fun x _ => by rw [hloc]
  have hfam : charFam χ = heckeFam H := funext fun w => by
    by_cases h : H.UnrAt w
    · rw [heckeFam_of_unrAt h, charFam_of_unrAt ((hun w).2 h)]
      exact congrArg _ (hloc _ _).symm
    · rw [heckeFam_of_not_unrAt h]
      exact if_neg (mt (hun w).1 h)
  refine ⟨L z, hne z fun w => by have := hd w; omega, ?_⟩
  refine (GlobalTheory.Cont.holValueAt_self (σ := (z : ℂ).re - 1) (fun s _ => hL.1.analyticAt s) (by linarith)).congr
    ⟨1, fun s hs => ?_⟩
  rw [charL, hfam]
  exact (GlobalTheory.SqStep.heckeL_eq_of_ram (S := above E (T : Set (Pl F))) (fun w hw => mt (hun w).2 (hram w hw)) hL hs).symm

end GlobalTheory.BotLValue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicTermsVanish
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitTorusZero

open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

variable {D : D7} {V : HSp D}

theorem exists_minLevi (Φ : WittFrame V) (γ : GF V) :
    ∃ (g : GF V) (P : Finset (SV (wittIndex V))), IsMinLevi Φ (g * γ * g⁻¹) P := by
  classical
  let A : Finset (Finset (SV (wittIndex V))) := Finset.univ.filter fun P =>
    IsPar P ∧ ∃ g : GF V, rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P
  have hA : (∅ : Finset (SV (wittIndex V))) ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨by simp, by simp⟩, 1, ?_⟩
    simp [WittFrame.levi]
  obtain ⟨P, hPA, hmax⟩ := A.exists_max_image Finset.card ⟨_, hA⟩
  obtain ⟨hP, g, hg⟩ := (Finset.mem_filter.1 hPA).2
  refine ⟨g, P, hP, hg, fun g' P' hP' h' => hmax P' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP', g' * g, ?_⟩)⟩
  have e : g' * g * γ * (g' * g)⁻¹ = g' * (g * γ * g⁻¹) * g'⁻¹ := by group
  rw [e]; exact h'

theorem rat_mem_GQ (g : GF V) : rat V g ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨g, rfl⟩

theorem zeroClause_of_conj (μ : Measure (GA D V)) (f : GA D V → ℂ) (γ g : GF V)
    (h : ZeroClause μ f (rat V (g * γ * g⁻¹))) : ZeroClause μ f (rat V γ) := by
  have hg := rat_mem_GQ g
  have e : ratClass (GQ V) (rat V (g * γ * g⁻¹)) = ratClass (GQ V) (rat V γ) := by
    ext δ
    simp only [ratClass, Set.mem_ofPred_eq, map_mul, map_inv]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(rat V g)⁻¹ * k, mul_mem (inv_mem hg) hk, by group⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨rat V g * k, mul_mem hg hk, by group⟩
  intro 𝓕 h𝓕
  have := h 𝓕 h𝓕
  unfold HasClassInt classKernel at *
  rw [e] at this
  exact this

theorem summable_class {f : GA D V → ℂ} (hf : HasCompactSupport f) {γ : GA D V} (hγ : γ ∈ GQ V) (x : GA D V) :
    Summable fun δ : ratClass (GQ V) γ => f (x⁻¹ * δ * x) := by
  have hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V := fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  apply summable_of_hasFiniteSupport
  refine ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_
  intro δ hδ
  exact hδ

theorem fd_of_quot {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {φ : GA D V → ℂ} (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ) (hi : Integrable (descend (GQ V) φ) (autMeasure V μ)) :
    IntegrableOn φ 𝓕 μ ∧ ∫ x in 𝓕, φ x ∂μ = ∫ q, descend (GQ V) φ q ∂autMeasure V μ := by
  refine ⟨?_, ?_⟩
  · have := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (p := 1)).1 (memLp_one_iff_integrable.2 hi)
    rw [hφ.lift_descend] at this
    exact memLp_one_iff_integrable.1 this
  · rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
    exact congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm

theorem exists_regular {k : ℕ} (c c' : ℝ) : ∃ T : A0 k, Regular c T ∧ Regular c' T := by
  set C := max (max c c') 1
  have h1 : c ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : c' ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : 1 ≤ C := le_max_right _ _
  have key : ∀ b, b ≤ C → Regular b (WithLp.toLp 2 fun i : Fin k => C * ((k : ℝ) - i) : A0 k) := fun b hb => by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      nlinarith
    · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast i.2
      nlinarith
  exact ⟨_, key c h1, key c' h2⟩

theorem exists_haar_cent (γ : GA D V) : ∃ dt : Measure (cent γ), dt.IsHaarMeasure := by
  have : LocallyCompactSpace (cent γ) := (GlobalTheory.Orb.isClosed_cent γ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩

theorem hyperZero : GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm →
    GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → HyperZero := by
  intro hLW hPC hTV hRS D V lam S M T U μa μf μ _ _ fa ff hTD γ hreg hirr hna
  obtain ⟨Φ, L, a, hgood⟩ := exists_isGood V
  obtain ⟨g, P, hP⟩ := exists_minLevi Φ γ
  refine zeroClause_of_conj μ _ γ g ?_
  set γ0 := g * γ * g⁻¹ with hγ0
  have hreg0 : IsRegSS γ0.1.1 := by
    show IsRegSS ((g.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * γ.1.1 * ((g.1)⁻¹ : GL (Fin V.rank) D.host.E).1)
    unfold IsRegSS
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact hreg
  have hPne : P ≠ ∅ := by
    obtain ⟨g', P', hpar', hne', hmem'⟩ := GlobalTheory.T.exists_conj_mem_standardLevi_of_reducible_charpoly hTD.1.pos hRS Φ γ hreg hirr hna
    have e : g' * g⁻¹ * γ0 * (g' * g⁻¹)⁻¹ = g' * γ * g'⁻¹ := by rw [hγ0]; group
    have hle := hP.2.2 (g' * g⁻¹) P' hpar' (e ▸ hmem')
    rintro rfl
    have := Finset.card_pos.2 hne'
    rw [Finset.card_empty] at hle
    omega
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V :=
    (IsTestFnG.isPureTensor ⟨fa, ff, hTD.2.2.2.2.2.1, hTD.2.2.2.2.2.2, rfl⟩).2
  obtain ⟨c1, hc1⟩ := ((hLW.2 D V Φ L a hgood).2 μ).1 _ hf
  obtain ⟨dt, hdt⟩ := exists_haar_cent (rat V γ0)
  obtain ⟨c2, hc2⟩ := ((hLW.2 D V Φ L a hgood).2 μ).2 _ hf γ0 hreg0 P hP dt
  obtain ⟨Tr, h1, h2⟩ := exists_regular (k := wittIndex V) c1 c2
  have hint := (hc1 Tr h1).1 _ (GlobalTheory.regSS_conjClass_isSSClass γ0 hreg0)
  have heq := (hc2 Tr h2).2
  have hz := GlobalTheory.T.elliptic_trace_from_model hLW hPC hTV hRS D V lam S M T U μa μf μ fa ff hTD Φ L a hgood γ0 hreg0 P hP hPne dt Tr
  have hk : kT Φ (levelAll D.sp.cm.sig V.gram L a) {δ | IsConj γ0 δ} (tensor D.sp.cm.sig V.gram fa ff) Tr =
      classKernel (GQ V) (rat V γ0) (tensor D.sp.cm.sig V.gram fa ff) :=
    funext (GlobalTheory.T.test_data_trace_identity hPC hTD Φ _ γ0 Tr)
  rw [hk] at hint heq
  intro 𝓕 h𝓕
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (classKernel (GQ V) (rat V γ0) (tensor D.sp.cm.sig V.gram fa ff)) :=
    fun δ hδ x => classKernel_mul _ _ hδ x
  obtain ⟨hi, hv⟩ := fd_of_quot h𝓕 hinv hint
  refine ⟨summable_class (GlobalTheory.Orb.continuous_of_mem_ccAd hf).2 (rat_mem_GQ γ0), hi, ?_⟩
  rw [hv, heq, hz, mul_zero]

end GlobalTheory.SplitTorusZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceActionOnTensorCoords
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoordAct

theorem at_mul_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (a : AE F E) {z : AE F E} (hz : At (evFin F v) z) : At (evFin F v) (a * z) := fun u hu => by
  rw [← mul_smul_comm, hz u hu, mul_zero]

theorem at_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (a : AE F E) {z : AE F E} (hz : At (evFin F v) z) : At (evFin F v) (z * a) := fun u hu => by
  rw [← smul_mul_assoc, hz u hu, zero_mul]

theorem at_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    {ι : Type} (s : Finset ι) (f : ι → AE F E) (hf : ∀ i, At (evFin F v) (f i)) :
    At (evFin F v) (∑ i ∈ s, f i) := fun u hu => by
  rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => hf i u hu

theorem act_kap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  intro F E _ _ _ _ _ σ v w hw h n d X Y A Bm g₁ g₂ _ _ x
  set P : Matrix (Fin n) (Fin d) (w.adicCompletion E) := (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ with hP
  have hK : kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x = P.map (ptAt hw h) := kap_apply hw h _ _ x
  have hmm : (P.map (ptAt hw h)).map (locW h) = P := by
    rw [Matrix.map_map]; exact Matrix.ext fun i j => locW_ptAt hw h _
  rw [hK, kap_apply]
  simp only [actAB]
  change mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ = _
  have hat : ∀ i j, At (evFin F v) ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ) i j) := fun i j => by
    simp only [Matrix.mul_apply]
    refine at_sum _ _ fun k => at_mul_right _ (at_sum _ _ fun l => at_mul_left _ (at_ptAt hw h _))
  have e1 : mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ =
      ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ).map (locW h)).map (ptAt hw h) := by
    exact Matrix.ext fun i j => (ptAt_locW hw h (hat i j)).symm
  rw [e1]
  congr 1
  rw [Matrix.map_mul, Matrix.map_mul, hmm, Matrix.transpose_map, hP]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hB : (((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ *
      ((Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have hA : (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hB, Matrix.mul_one, ← Matrix.mul_assoc (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)), hA, Matrix.one_mul]

end GlobalTheory.InertCoordAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledFirstFactorMemSiegelClosureStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_doubledFirstFactor_mem_siegelClosure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  first | exact @GlobalTheory.InertDblGen.inlD_mem_closure | exact GlobalTheory.InertDblGen.inlD_mem_closure | (intros; apply GlobalTheory.InertDblGen.inlD_mem_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlacePointSupportedAndSurjective
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoord

theorem kap_at_and_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (AE F E), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  intro F E _ _ _ _ _ v w hw h m n A Bm
  refine ⟨fun x u hu => ?_, fun γ hγ => ?_⟩
  · ext i j
    rw [Matrix.smul_apply, kap_apply, Matrix.map_apply, Matrix.zero_apply]
    exact at_ptAt hw h _ u hu
  · refine ⟨(((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ))ᵀ, ?_⟩
    rw [kap_apply, Matrix.transpose_transpose]
    have e : (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *
        (((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ)) *
        (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = γ.map (locW h) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
    rw [e]
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply]
    refine ptAt_locW hw h fun u hu => ?_
    have := congrFun (congrFun (hγ u hu) i) j
    rwa [Matrix.smul_apply, Matrix.zero_apply] at this

end GlobalTheory.InertCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmulStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • (G.M'.vac v))) →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • G.M'.vac v := by
  first | exact @GlobalTheory.VacUniqInert.vac_unique | exact GlobalTheory.VacUniqInert.vac_unique | (intros; apply GlobalTheory.VacUniqInert.vac_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCountOfDepth
section
open GlobalTheory.SumSize GlobalTheory.RowClaim

namespace GlobalTheory.SumCount

theorem infCountK : GlobalTheory.FunPr.Hypotheses₂ → DepthK → InfCountK := fun hP hD =>
  infCountK_of GlobalTheory.T.datumCountBound_largeData (GlobalTheory.T.cosine_count_of_hypotheses hP) (GlobalTheory.T.pureTensorCountBound_of_cosetDepthBound hD)

end GlobalTheory.SumCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGLConjPlaceOfSelfDualBaseFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.ConjPlaceLev

theorem inBasis_conjPl_mem_KO_of_isBaseFrame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Lev.IsBaseFrame V β Λ 1 → ∀ x ∈ UA D.sp.cm V.gram, ∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin V.rank) → inBasis rfl β (Formalism.DivisionValues.conjPl w) x ∈ KO (Kw (Formalism.DivisionValues.conjPl w)) (Fin V.rank) := by
  intro D V β Λ h x hx w hw
  exact GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO V β Λ h.1 h.2.1 x hx w hw

end GlobalTheory.ConjPlaceLev
end
end

