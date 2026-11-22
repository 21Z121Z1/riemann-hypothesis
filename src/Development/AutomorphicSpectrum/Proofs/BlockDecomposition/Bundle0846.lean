import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0835
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0844
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0843
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0837
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0777
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0779
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0784
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0845
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0804
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0787
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0778
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0808
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0823
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0827
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0841
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0842
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0839
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0840
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0833
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0838

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCutoffContinuousCompactSupport
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem phiA_test : ∀ (F : Type) [Field F] [NumberField F] (G : Ainf F → ℝ) (a : (AF F)ˣ), Continuous G → HasCompactSupport G →
    Continuous (phiA G a) ∧ HasCompactSupport (phiA G a) := by
  intro F _ _ G a hc hs
  have h1 : (a : AF F).1 * ((a⁻¹ : (AF F)ˣ) : AF F).1 = 1 :=
    congrArg Prod.fst (a.mul_inv)
  have h2 : ((a⁻¹ : (AF F)ˣ) : AF F).1 * (a : AF F).1 = 1 :=
    congrArg Prod.fst (a.inv_mul)
  let m : Ainf F ≃ₜ Ainf F :=
    { toFun := fun x => (a : AF F).1 * x
      invFun := fun x => ((a⁻¹ : (AF F)ˣ) : AF F).1 * x
      left_inv := fun x => by simp only [← mul_assoc, h2, one_mul]
      right_inv := fun x => by simp only [← mul_assoc, h1, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  let e : (Unit → Ainf F) ≃ₜ Ainf F := (Homeomorph.funUnique Unit (Ainf F)).trans m
  have he : phiA G a = G ∘ e := by
    funext y
    rfl
  rw [he]
  exact ⟨hc.comp e.continuous, hs.comp_homeomorph e⟩

end GlobalTheory.CompanionTheory.BasePsi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceCutoffContinuousCompactSupportStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_place_cutoff_continuous_compact_support : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    ∀ v : HeightOneSpectrum (𝓞 F), Continuous (psiA S g a v) ∧ HasCompactSupport (psiA S g a v) := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.Test.psiA_isTest | exact GlobalTheory.CompanionTheory.BasePsi.Test.psiA_isTest | (intros; apply GlobalTheory.CompanionTheory.BasePsi.Test.psiA_isTest <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisenstein
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.FJE in

theorem GlobalTheory.CompanionTheory.FJE.fjEis : ZUnfold → ThTwist → FJEis := by
  intro hZ hTw D n ρ p hn M m ψ hψ b₀ hb χ χ' hχ hχ' θ hθ Ω hΩ s f hf hl hs g
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : m.μ.IsAddHaarMeasure := m.hμ.1
  obtain ⟨hcM, hcC⟩ := GlobalTheory.T.countable_matrices_and_cosets D ρ p
  have hsum := fun g' => (hZ D n ρ p hn M m ψ hψ b₀ hb χ hχ s f hf hl hs g').1
  have hC := (hZ D n ρ p hn M m ψ hψ b₀ hb χ hχ s f hf hl hs g).2
  obtain ⟨t, ht, hT⟩ := GlobalTheory.T.fourier_jacobi_terms_summable M m ψ hψ b₀ χ s f hl g hC
  have hF : LeftInv (GF D n) (eisS f) := GlobalTheory.Eis.leftInv_cosetSum (GlobalTheory.T.section_left_invariant_rational_parabolic χ s f hχ hl)
  have hTr := fun q : GlobalTheory.Eis.Cosets (P D p) (GF D p) => GlobalTheory.T.lattice_translation_preserved M ((q.out : GF D p) : G D p) q.out.2
  choose T hT1 hT2 hT3 using hTr

  have hterm := fun (q : GlobalTheory.Eis.Cosets (P D p) (GF D p)) (v : Mx D ρ p × Mx D ρ p) =>
    GlobalTheory.T.theta_fourier_jacobi_lattice_swap M m ψ hψ b₀ hb hTw χ' hχ' θ hθ Ω hΩ χ s f hl g ((q.out : GF D p) : G D p) q.out.2 (T q) (hT3 q) v

  set A : GlobalTheory.Eis.Cosets (P D p) (GF D p) → Matrix (Fin ρ) (Fin p) D.host.E → Mx D ρ p × Mx D ρ p → ℂ :=
    fun q η v => Wz M m ψ b₀ f (M.sh (rt η) * M.emb (q.out : GF D p) * (M.nzx 0 v.2 * (M.sh v.1 * g))) with hA
  set Sq : GlobalTheory.Eis.Cosets (P D p) (GF D p) → Mx D ρ p × Mx D ρ p → ℂ := fun q v => ∑' η, A q η v with hSq
  have hAs : ∀ q v, Summable (fun η => ‖A q η v‖) := fun q v =>
    (summable_congr fun η => (hterm q v).1 η).2 (hT q (T q v).1).1
  have hSqle : ∀ q v, ‖Sq q v‖ ≤ t q := fun q v => by
    refine (norm_tsum_le_tsum_norm (hAs q v)).trans ?_
    rw [tsum_congr fun η => (hterm q v).1 η]
    exact (hT q (T q v).1).2
  have hAm : ∀ q η, StronglyMeasurable (A q η) := fun q η =>
    GlobalTheory.T.stronglyMeasurable_coefficient_composition M m ψ hψ b₀ f hf _ (by
      have h1 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 :=
        M.nzx_cont.comp (continuous_const.prodMk continuous_snd)
      have h2 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.sh v.1 := M.sh_cont.comp continuous_fst
      exact continuous_const.mul (h1.mul (h2.mul continuous_const)))
  have hSqm : ∀ q, StronglyMeasurable (Sq q) := fun q =>
    GlobalTheory.CompanionTheory.FJE.tsum_meas (fun η => hAm q η) fun v => (hAs q v).of_norm
  set Fz : Mx D ρ p × Mx D ρ p → ℂ := fun v => zc M m ψ b₀ (eisS f) (M.nzx 0 v.2 * (M.sh v.1 * g)) with hFz
  have hq : ∀ v, HasSum (fun q => Sq q v) (Fz v) := fun v =>
    (hsum (M.nzx 0 v.2 * (M.sh v.1 * g))).prod_fiberwise fun q => (hAs q v).of_norm.hasSum
  have hqn : ∀ v, Summable fun q => ‖Sq q v‖ := fun v => .of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hSqle q v) ht
  have hFzm : StronglyMeasurable Fz := by
    have : Fz = fun v => ∑' q, Sq q v := funext fun v => (hq v).tsum_eq.symm
    rw [this]
    exact GlobalTheory.CompanionTheory.FJE.tsum_meas hSqm fun v => (hqn v).of_norm
  have hFzb : ∀ y x, ‖zc M m ψ b₀ (eisS f) (M.nzx 0 x * (M.sh y * g))‖ ≤ ∑' q, t q := fun y x => by
    have := (hq (y, x)).tsum_eq
    simp only [hFz] at this
    rw [← this]
    exact (norm_tsum_le_tsum_norm (hqn _)).trans ((hqn _).tsum_le_tsum (fun q => hSqle q _) ht)
  have h1 := GlobalTheory.T.fourier_jacobi_expansion_bounded M m ψ hψ b₀ (eisS f) hF g θ hθ (Ω 1) (hΩ.mem 1) _ hFzb hFzm

  have hcont : ∀ h, Continuous (Ω h) := fun h => hΩ.cont.comp (continuous_const.prodMk continuous_id)
  have hsm : ∀ h, StronglyMeasurable (Ω h) := fun h => (hcont h).stronglyMeasurable
  have hbd := fun h => GlobalTheory.T.exists_bound_lattice_sum_norm_schwartzA θ hθ (Ω h) (hΩ.mem h)
  obtain ⟨Bθ, hBθ⟩ := hbd 1
  have hthm : StronglyMeasurable fun v : Mx D ρ p × Mx D ρ p => conj (th ψ b₀ (Ω 1) 0 v.2 v.1) := by
    simp only [th_zero]
    exact Complex.continuous_conj.comp_stronglyMeasurable
      (GlobalTheory.T.stronglyMeasurable_twisted_lattice_sum ψ hψ b₀ (Ω 1) (hsm 1) fun y => (hBθ y).1)
  have hthb : ∀ v : Mx D ρ p × Mx D ρ p, ‖conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ≤ Bθ := fun v => by
    rw [RCLike.norm_conj, th_zero]
    have hn1 : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖chv ψ b₀ v.2 (rt ξ) * Ω 1 (rt ξ + v.1)‖ = ‖Ω 1 (rt ξ + v.1)‖ := fun ξ => by
      rw [norm_mul, (GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀).2.2.1, one_mul]
    refine (norm_tsum_le_tsum_norm ((summable_congr hn1).2 (hBθ v.1).1)).trans ?_
    rw [tsum_congr hn1]
    exact (hBθ v.1).2

  have hI : ∀ q, ∫ v in m.𝓕 ×ˢ m.𝓕, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) ∂(m.μ.prod m.μ) =
      Rsec M m ψ b₀ f g Ω (((q.out : GF D p) : G D p) * 1) := fun q => by
    have hΦm : StronglyMeasurable fun y => Wz M m ψ b₀ f (M.sh y * M.emb (q.out : GF D p) * g) :=
      GlobalTheory.T.stronglyMeasurable_coefficient_composition M m ψ hψ b₀ f hf _ ((M.sh_cont.mul continuous_const).mul continuous_const)
    obtain ⟨B₂, hB₂⟩ := hbd ((q.out : GF D p) : G D p)
    have e1 : ∀ v, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) =
        Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb (q.out : GF D p) * g)) (Ω ((q.out : GF D p) : G D p)) (T q v) :=
      fun v => (hterm q v).2
    simp only [e1]
    rw [GlobalTheory.T.lattice_transform_invariance m (T q) (hT1 q) (hT2 q) _ (fun ξ₁ ξ₂ v => GlobalTheory.T.lattice_twisted_sum_periodic ψ hψ b₀ _ _ ξ₁ ξ₂ v),
      GlobalTheory.T.twisted_lattice_sums_bounded_product m ψ hψ b₀ hb _ _ (t q) B₂ hΦm (hsm _) (fun y => hT q y) hB₂, mul_one]
    rfl

  set ν := (m.μ.prod m.μ).restrict (m.𝓕 ×ˢ m.𝓕) with hν
  have hmass : ν Set.univ = 1 := by
    rw [hν, Measure.restrict_apply_univ, Measure.prod_prod, m.hμ.2.2, one_mul]
  haveI : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hbound : ∀ q v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ≤ t q * Bθ := fun q v => by
    rw [norm_mul]
    exact mul_le_mul (hSqle q v) (hthb v) (norm_nonneg _) ((norm_nonneg _).trans (hSqle q v))
  have hint : ∀ q, Integrable (fun v => Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)) ν := fun q =>
    Integrable.of_bound ((hSqm q).mul hthm).aestronglyMeasurable (t q * Bθ) (.of_forall (hbound q))
  have hnorm : ∀ q, ∫ v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ∂ν ≤ t q * Bθ := fun q => by
    have h2 := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun v => ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖) (C := t q * Bθ)
      (.of_forall fun v => by simpa using hbound q v)
    have h3 : ν.real Set.univ = 1 := by simp [Measure.real, hmass]
    rw [h3, mul_one] at h2
    exact (le_abs_self _).trans (by simpa using h2)
  have hfs : Summable fun q => ∫ v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ∂ν :=
    .of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm (ht.mul_right Bθ)
  have hfin2 := hasSum_integral_of_summable_integral_norm hint hfs
  have e : (fun v => ∑' q, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)) =
      fun v => Fz v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) := funext fun v => by
    rw [tsum_mul_right, (hq v).tsum_eq]
  rw [e] at hfin2
  rw [h1, ← hfin2.tsum_eq, eisS, GlobalTheory.Eis.cosetSum]
  exact tsum_congr fun q => hI q
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqCoefficientNonrepresented
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem vanish_ring {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : AddChar A ℂ) (hψc : Continuous ψ) (hψn : ∀ x, ‖ψ x‖ = 1) (κ : Type) [Fintype κ]
    [FirstCountableTopology (κ → A)] [MeasurableSpace (κ → A)] [OpensMeasurableSpace (κ → A)]
    (μ : Measure (κ → A)) [μ.IsOpenPosMeasure]
    (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (φ : Y → ℂ) (g : Y → κ → A)
    (hg : Measurable g) (N : Set (κ → A)) (hN : IsOpen N)
    (hb : Integrable φ ν → Integrable (fun v : κ → A => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ →
      ∀ N' : Set (κ → A), IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : (κ → A) → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0)
    (z₀ : κ → A) (hz : z₀ ∈ closure N) :
    ∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) ∂μ = 0 := by
  have hdot : Continuous (fun p : (κ → A) × (κ → A) => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have hd1 : ∀ w, Continuous fun v : κ → A => ψ (-(v ⬝ᵥ w)) := fun w =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_id continuous_const)).neg
  have hd2 : ∀ v, Continuous fun w : κ → A => ψ (-(v ⬝ᵥ w)) := fun v =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_const continuous_id)).neg
  have hd3 : ∀ v, Continuous fun w : κ → A => ψ (v ⬝ᵥ w) := fun v =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_const continuous_id))
  by_cases hφ : Integrable φ ν
  swap
  · have h0 : ∀ v : κ → A, ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν = 0 := fun v =>
      integral_undef fun hi => hφ (integrable_of_mul_unimodular ν φ (fun y => ψ (v ⬝ᵥ g y)) hi
        ((hd3 v).measurable.comp hg).aestronglyMeasurable fun y => hψn _)
    refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
    show (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) = 0
    rw [h0 v, zero_mul]
  by_cases hJ : Integrable (fun v : κ → A => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ
  swap
  · exact integral_undef fun hi => hJ (integrable_of_mul_unimodular μ _ (fun v => ψ (-(v ⬝ᵥ z₀))) hi
      (hd1 z₀).aestronglyMeasurable fun y => hψn _)
  exact vanish_abs μ (fun v z => ψ (-(v ⬝ᵥ z))) hd1 hd2 (fun _ _ => hψn _) _ hJ N hN (hb hφ hJ) z₀ hz

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem vanish_generic (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyReal F)
    (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)]
    [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) (hμ : GlobalTheory.SWLit.IsTamagawa F κ μ)
    (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F)
    (hg : Measurable g) (N : Set (κ → AF F)) (hN : IsOpen N) (hgN : ∀ y, g y ∉ N)
    (z₀ : κ → AF F) (hz : z₀ ∈ closure N) :
    ∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) ∂μ = 0 := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ.1
  refine vanish_ring ψ hψ.1 hψ.2.1 κ μ Y ν φ g hg N hN ?_ z₀ hz
  intro hφ hJ N' hN' hsub z₁ hz₁
  obtain ⟨Φ, hΦ, hΦ0, hΦN, hΦ1⟩ := GlobalTheory.T.exists_nonnegative_schwartz_bump F κ N' hN' z₁ hz₁
  obtain ⟨hΦc, -, hΦi⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  exact ⟨Φ, hΦc, hΦi μ hμ.1, hΦ0, hΦN, hΦ1,
    GlobalTheory.T.tamagawa_fourier_integrable F hF ψ hψ κ μ hμ Y ν φ g hφ hg hJ Φ hΦ (fun y => hΦN _ fun h' => hgN y (hsub h'))⟩

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

variable {D : D7}

theorem posOn_add_smul_one {n : ℕ} {ε δ : ℝ} {Z : Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℂ (Fin n → ℂ)}
    (hS : NonnegOn ε Z S) (hε : ε = 1 ∨ ε = -1) (hδ : 0 < δ) :
    PosOn ε (Z + ((ε * δ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) S := by
  intro w hw hne
  have h0 := hS w hw
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hB : 0 < (star w ⬝ᵥ w).re := by
    have e : (star w ⬝ᵥ w).re = ∑ j, Complex.normSq (w j) := by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    rw [e]
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have e2 : (star w ⬝ᵥ (Z + ((ε * δ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).mulVec w).re =
      (star w ⬝ᵥ Z.mulVec w).re + ε * δ * (star w ⬝ᵥ w).re := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
  rw [e2]
  have : ε * ((star w ⬝ᵥ Z.mulVec w).re + ε * δ * (star w ⬝ᵥ w).re) =
      ε * (star w ⬝ᵥ Z.mulVec w).re + (ε * ε) * δ * (star w ⬝ᵥ w).re := by ring
  rw [this, hεε, one_mul]
  exact add_pos_of_nonneg_of_pos h0 (mul_pos hδ hB)

theorem compAt_add' (θ : InfFam D) (ρ : D.what₂.Tau) {m n : ℕ} (a b : Mx D m n) :
    compAt θ ρ (a + b) = compAt θ ρ a + compAt θ ρ b := by
  exact Matrix.map_add (⇑((θ ρ).comp (infPart D))) ((θ ρ).comp (infPart D)).map_add a b

theorem compAt_neg' (θ : InfFam D) (ρ : D.what₂.Tau) {m n : ℕ} (a : Mx D m n) :
    compAt θ ρ (-a) = -compAt θ ρ a := by
  exact Matrix.map_neg (⇑((θ ρ).comp (infPart D))) ((θ ρ).comp (infPart D)).map_neg a

theorem W_eq_zero_of_obstruction (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V))
    (φ : Mx D V.rank r → ℂ) (h : Hyp D r V ψ θ μ lam ν φ) (β : HermE D r) (ρ : D.what₂.Tau) (ε : ℝ)
    (S : Submodule ℂ (Fin r → ℂ)) (hε : ε = 1 ∨ ε = -1) (hS : NonnegOn ε (β.1.map (tauE D ρ)) S)
    (hT : ∀ T : Submodule ℂ (Fin V.rank → ℂ), PosOn ε (gramAt D V ρ) T →
      Module.finrank ℂ T < Module.finrank ℂ S) :
    W ψ V μ lam φ β = 0 := by
  obtain ⟨hr, hψ, hθ, ⟨𝓕, hF⟩, ⟨𝓖, hG⟩, -, -, -⟩ := h
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele D.host.F
  haveI : BorelSpace (AF D.host.F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D V.rank r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hF.1
  obtain ⟨n, c, u, R, hu, hR, hRu, hcu, hTam⟩ := GlobalTheory.T.hermitian_coordinates_trace_pairing D r lam 𝓖 hG
  have hin := GlobalTheory.T.gram_map_continuous_hermitian D θ hθ V r ρ
  let g : Mx D V.rank r → Fin n → AF D.host.F := fun y => u (inner V y y)
  have hgc : Continuous g := hu.comp hin.1
  let N : Set (Fin n → AF D.host.F) := {w | PosOn ε (compAt θ ρ (R w)) S}
  have hN : IsOpen N :=
    (GlobalTheory.T.positive_on_subspace_open r ε S).preimage ((GlobalTheory.RealWeil.continuous_compAt hθ ρ r r).comp hR)
  have hgN : ∀ y, g y ∉ N := by
    intro y hy
    have h1 : PosOn ε (compAt θ ρ (R (u (inner V y y)))) S := hy
    rw [hRu _ (hin.2 y).1, (hin.2 y).2] at h1
    obtain ⟨T, hT1, hT2⟩ := GlobalTheory.T.positivity_pulls_back_to_subspace _ _ _ _ ε S h1
    have := hT T hT1
    omega
  let z₀ : Fin n → AF D.host.F := u (rat β.1)
  have hcl : ∀ e' : ℕ → Mx D r r, (∀ k, e' k ∈ hermA D r) → Filter.Tendsto e' Filter.atTop (nhds 0) →
      (∀ k : ℕ, compAt θ ρ (e' k) = ((ε * ((1 : ℝ) / ((k : ℝ) + 1)) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) →
      z₀ ∈ closure N := by
    intro e' he' het hec
    have hlim : Filter.Tendsto (fun k => u (rat β.1 + e' k)) Filter.atTop (nhds z₀) := by
      have h2 : Filter.Tendsto (fun k => rat β.1 + e' k) Filter.atTop (nhds (rat β.1 + 0)) :=
        tendsto_const_nhds.add het
      rw [add_zero] at h2
      exact (hu.tendsto _).comp h2
    refine mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
    show PosOn ε (compAt θ ρ (R (u (rat β.1 + e' k)))) S
    have hrat : compAt θ ρ (rat β.1) = β.1.map (tauE D ρ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ ρ β.1
    rw [hRu _ ((hermA D r).add_mem (GlobalTheory.CompanionTheory.HermPoisson.rat_mem_hermA β) (he' k)), compAt_add', hec k, hrat]
    exact posOn_add_smul_one hS hε (by positivity)
  obtain ⟨e, he, het, hec⟩ := GlobalTheory.T.hermitian_scalar_sequence_tends_zero D θ hθ r
  have hz : z₀ ∈ closure N := by
    rcases hε with rfl | rfl
    · refine hcl e he het fun k => ?_
      rw [hec k, one_mul]
    · refine hcl (fun k => -e k) (fun k => (hermA D r).neg_mem (he k)) ?_ fun k => ?_
      · have h3 := het.neg
        rw [neg_zero] at h3
        exact h3
      · rw [compAt_neg', hec k]
        simp
  have key := vanish_generic D.host.F D.sp.cm.totReal ψ hψ (Fin n) (lam.map c.symm) hTam _ μ φ g
    hgc.measurable N hN hgN z₀ hz
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  have hemb : MeasurableEmbedding (c.symm) := c.symm.toHomeomorph.measurableEmbedding
  rw [hemb.integral_map] at key
  refine Eq.trans ?_ key
  unfold W
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have h1 : ∀ x : Mx D r r, c.symm b ⬝ᵥ u x = halfTr (Matrix.trace (HMul.hMul b.1 x : Mx D r r)) := fun x => by
    rw [← hcu]; simp
  show Jt ψ V μ φ b * _ = (∫ y, φ y * ψ (c.symm b ⬝ᵥ u (inner V y y)) ∂μ) * ψ (-(c.symm b ⬝ᵥ u (rat β.1)))
  simp only [h1]
  rw [Matrix.trace_mul_comm]
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem noFrame : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  intro D r V ψ θ μ lam ν φ h t β hβ hno
  obtain ⟨ρ, ε, S, hε, hS, hT⟩ := GlobalTheory.T.nonrepresented_signature_obstruction D r V h.1 t β hβ hno
  rw [W_eq_zero_of_obstruction r V ψ θ μ lam ν φ h β ρ ε S hε hS hT]
  haveI hemp : IsEmpty {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} :=
    ⟨fun x => hno ⟨x.1, x.2⟩⟩
  unfold IfrB
  have h0 : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) q) = fun _ => (0 : ℂ) := by
    funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, tsum_empty]
  rw [h0]
  simp [MeasureTheory.average]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCosetsParamRationalStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_cosets_param_rational : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn),
    ∃ e : ratHerm D ρ × (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) → Cosets (P D n) (GF D n),
      Function.Injective e ∧
      (∀ q, zKer hn (ratOf q.out) = ⊥ ↔ q ∈ Set.range e) ∧
      (∀ (l l' : ratHerm D ρ) u (h : M.nzx l'.1 0 ∈ GF D n),
        rmulEquiv (P D n) (GF D n) ⟨M.nzx l'.1 0, h⟩ (e (l, u)) = e (l' + l, u)) ∧
      ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D ρ) u (y : G D n),
        term (P D n) (GF D n) f y (e (l, u)) =
          f (M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * y) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell | exact GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell | (intros; apply GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleEqNormModule
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem ideleModule_eq_md_of_isNm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (x : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ x n → (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) = md n := by
  intro F E _ _ _ _ _ σ hcm x n h
  have h1 := GlobalTheory.T.idele_module_conjugation_invariant F E σ hcm x
  have h2 := GlobalTheory.T.idele_module_base_change_sq F E σ hcm n
  have hu : (ofF n : (AF F ⊗[F] E)ˣ) = Units.map (sigR (AF F) σ).toMonoidHom x * x := Units.ext h
  rw [hu, map_mul, map_mul] at h2
  have h3 : ((IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (Units.map (sigR (AF F) σ).toMonoidHom x)) : ℝ)) *
      (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) = md n ^ 2 := h2
  rw [h1] at h3
  have hp : 0 < (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) :=
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x)).2
  have hq : 0 < md n := (IdeleGroup.ideleModule F n).2
  nlinarith [sq_nonneg ((IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) - md n)]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurablePureAdelicFunctionStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_pure_adelic_function : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), Continuous G → (∀ v ∈ S, Continuous (g v)) →
    Measurable (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.measurable_pure_rv_zero | exact GlobalTheory.CompanionTheory.BasePsi.measurable_pure_rv_zero | (intros; apply GlobalTheory.CompanionTheory.BasePsi.measurable_pure_rv_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleRayEqPowDegreeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_ray_eq_pow_degree : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.md_ray | exact GlobalTheory.CompanionTheory.BasePsi.md_ray | (intros; apply GlobalTheory.CompanionTheory.BasePsi.md_ray <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionEnlargeFiniteSetStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_function_enlarge_finite_set : ∀ (F : Type) [Field F] [NumberField F] (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)),
    IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    (∫ y, phiA G a y ∂(Measure.pi fun _ : Unit => li)) * ∏ v ∈ T, ∫ y, psiA S g a v y ∂(Measure.pi fun _ : Unit => lam v) =
      (md a)⁻¹ * ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v)) := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.Integrals.integrals_translates | exact GlobalTheory.CompanionTheory.BasePsi.Integrals.integrals_translates | (intros; apply GlobalTheory.CompanionTheory.BasePsi.Integrals.integrals_translates <;> assumption)
end

