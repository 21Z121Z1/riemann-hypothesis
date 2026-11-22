import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0614
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundSiegelTorus
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem param_le_rbar_pow {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    ∀ (k m : ℕ) (h : m < r), m + k + 1 = r → t ⟨m, h⟩ ≤ rbar t ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro m h e
    have h1 := ratio_le_rbar t ⟨m, h⟩
    have h2 : ¬ m + 1 < r := by omega
    simpa [ratio, h2] using h1
  | succ k ih =>
    intro m h e
    have hm : m + 1 < r := by omega
    have h1 := ih (m + 1) hm (by omega)
    have h2 := ratio_le_rbar t ⟨m, h⟩
    have h3 : t ⟨m, h⟩ / t ⟨m + 1, hm⟩ ≤ rbar t := by simpa [ratio, hm] using h2
    have h4 : t ⟨m, h⟩ ≤ rbar t * t ⟨m + 1, hm⟩ := (div_le_iff₀ (ht _)).1 h3
    have h5 : 0 ≤ rbar t := zero_le_one.trans (one_le_rbar t)
    calc t ⟨m, h⟩ ≤ rbar t * t ⟨m + 1, hm⟩ := h4
      _ ≤ rbar t * rbar t ^ (k + 1) := mul_le_mul_of_nonneg_left h1 h5
      _ = rbar t ^ (k + 1 + 1) := by ring

theorem param_le_rbar_pow_rank {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) (i : Fin r) : t i ≤ rbar t ^ r := by
  have h1 := param_le_rbar_pow ht (r - i.val - 1) i.val i.2 (by omega)
  exact h1.trans (pow_le_pow_right₀ (one_le_rbar t) (by omega))

theorem one_add_prod_le_rbar_pow {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    1 + ∏ i, t i ≤ 2 * rbar t ^ (r * r) := by
  have h1 : ∏ i, t i ≤ rbar t ^ (r * r) := by
    have := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin r))) (fun i _ => (ht i).le)
      fun i _ => param_le_rbar_pow_rank ht i
    simpa [pow_mul] using this
  have h2 : 1 ≤ rbar t ^ (r * r) := one_le_pow₀ (one_le_rbar t)
  linarith

theorem height_le_rbar_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ c : ℝ, 0 < c → ∃ b : ℕ, ∀ Ω Cm : Set (GAd σ J), IsCompact Ω → IsCompact Cm → ∃ H : ℝ, 0 ≤ H ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, (height σ J (p * a * k) : ℝ) ≤ H * rbar t ^ b := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW c hc
  have hc' : 0 < min 1 c ^ r := pow_pos (lt_min one_pos hc) _
  obtain ⟨Ch, Ah, hCh⟩ := @GlobalTheory.TorusHeight.height_torus_le F E _ _ _ _ _ σ hσ n J r X Y _ hc'
  refine ⟨r * r * Ah, fun Ω Cm hΩ hCm => ?_⟩
  have hcont : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  obtain ⟨R₁, hR₁⟩ := (hΩ.image hcont).bddAbove
  obtain ⟨R₂, hR₂⟩ := (hCm.image hcont).bddAbove
  set R₁' := max R₁ 0 with hR₁'
  set R₂' := max R₂ 0 with hR₂'
  set Ch' := max Ch 0 with hCh'
  have hR₁0 : 0 ≤ R₁' := le_max_right _ _
  have hR₂0 : 0 ≤ R₂' := le_max_right _ _
  have hCh0 : 0 ≤ Ch' := le_max_right _ _
  refine ⟨R₁' * (Ch' * 2 ^ Ah) * R₂', by positivity, fun p hp t ht a ha k hk => ?_⟩
  have h1 : (height σ J a : ℝ) ≤ Ch * (1 + ∏ i, t i) ^ Ah :=
    hCh t (GlobalTheory.SiegelHt.cone_low hc ht) a ha.1
      (@GlobalTheory.SiegelTorusMat.archMat_torus F E _ _ _ _ _ σ hσ n J hJ r X Y hW t
        (fun i => hc'.trans_le (GlobalTheory.SiegelHt.cone_low hc ht i)) a ha)
  have hprod0 : 0 ≤ 1 + ∏ i, t i := add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => (ht.1 i).le)
  have h2 := one_add_prod_le_rbar_pow (r := r) ht.1
  have h3 : (height σ J a : ℝ) ≤ Ch' * (2 * rbar t ^ (r * r)) ^ Ah :=
    h1.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hprod0 h2 _) (pow_nonneg hprod0 _) hCh0)
  have hpb : (height σ J p : ℝ) ≤ R₁' := (hR₁ ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  have hkb : (height σ J k : ℝ) ≤ R₂' := (hR₂ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
  have h5 : (height σ J (p * a * k) : ℝ) ≤ (height σ J p : ℝ) * height σ J a * height σ J k := by
    exact_mod_cast (height_mul_le σ J _ _).trans (mul_le_mul' (height_mul_le σ J _ _) le_rfl)
  calc (height σ J (p * a * k) : ℝ) ≤ (height σ J p : ℝ) * height σ J a * height σ J k := h5
    _ ≤ R₁' * (Ch' * (2 * rbar t ^ (r * r)) ^ Ah) * R₂' :=
        mul_le_mul (mul_le_mul hpb h3 (NNReal.coe_nonneg _) hR₁0) hkb (NNReal.coe_nonneg _)
          (mul_nonneg hR₁0 ((NNReal.coe_nonneg _).trans h3))
    _ = R₁' * (Ch' * 2 ^ Ah) * R₂' * rbar t ^ (r * r * Ah) := by
      rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisFurther
section
open scoped Classical

open NumberField GlobalTheory.CuspRep Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.WeightJoin

theorem main : PositivityTheory.Rg.BcB.F.RS.WeightJoin := by
  intro E _ _ _ hU n a b μ e π lam n₁ n₂ hn hμ hπ hw h₁ h₂ hinf τ lam' hτ
  obtain ⟨-, he, hc⟩ := GlobalTheory.BCT.MuProps.main E hU μ e hμ
  let U : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.TwistDisc.expo_pow]
  rcases NumberField.InfinitePlace.embedding_mk_eq τ with h | h
  · have hv := hw (InfinitePlace.mk τ)
    have hinfv := hinf (InfinitePlace.mk τ)
    have hev := he (InfinitePlace.mk τ)
    rw [h] at hv hinfv hev
    rw [GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, hev, ← hinfv]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ => by ring
  · have hv := GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn (hw (InfinitePlace.mk τ))
    have hinfv := hinf (InfinitePlace.mk τ)
    have hev := hc (InfinitePlace.mk τ)
    have hs₁ := (h₁ (InfinitePlace.mk τ).embedding).2
    have hs₂ := (h₂ (InfinitePlace.mk τ).embedding).2
    have hcc : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h]; exact star_star τ
    have hcc' : (starRingEnd ℂ).comp (InfinitePlace.mk τ).embedding = τ := hcc
    rw [hcc'] at hs₁ hs₂
    rw [hcc] at hv hev
    rw [GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, GlobalTheory.DefiniteBC.infOfWeight_dual, ← hinfv, hev, hs₁, hs₂,
      Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

end GlobalTheory.CompanionTheory.WeightJoin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfOfTwPart
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.JoinInfProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def infOf (τ : E →+* ℂ) (x : Σ M : ℕ, Submodule ℂ (Sm E M)) : Multiset ℂ :=
  if h : ∃ m, HasInfCharGL x.2 τ m then h.choose else 0

theorem infOf_eq {τ : E →+* ℂ} {x : Σ M : ℕ, Submodule ℂ (Sm E M)} (h0 : x.2 ≠ ⊥) {m : Multiset ℂ}
    (h : HasInfCharGL x.2 τ m) : infOf τ x = m := by
  have hex : ∃ m, HasInfCharGL x.2 τ m := ⟨m, h⟩
  unfold infOf
  rw [dif_pos hex]
  exact GlobalTheory.BcSpehProof.hasInfCharGL_unique h0 hex.choose_spec h

theorem sum_m {n : ℕ} (P : Pre E n) (τ : E →+* ℂ) : ∑ i, P.m i τ = ((parts P).map (infOf τ)).sum := by
  rw [PositivityTheory.Rg.BcB.F.RS.parts, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (infOf_eq (P.discrete i).ne_bot (P.inf i τ)).symm

theorem infOf_twPart {n : ℕ} (P : Pre E n) (χ : HChar E) (τ : E →+* ℂ) (i : Fin P.c) :
    infOf τ (twPart χ ⟨P.N i, P.V i⟩) = (P.m i τ).map (· + expo χ τ) := by
  have hne : Submodule.map ((GlobalTheory.CuspRep.mulChi (P.N i) χ : Sm E (P.N i) ≃ₗ[ℂ] Sm E (P.N i)) :
      Sm E (P.N i) →ₗ[ℂ] Sm E (P.N i)) (P.V i) ≠ ⊥ := by
    intro hb
    exact (P.discrete i).ne_bot (Submodule.map_eq_bot_iff.1 hb)
  exact infOf_eq hne (GlobalTheory.BCT.TwistDisc.hasInfCharGL_map (P.inf i τ) χ)

theorem sum_tw {n : ℕ} (P : Pre E n) (χ : HChar E) (τ : E →+* ℂ) :
    (((parts P).map (twPart χ)).map (infOf τ)).sum = (∑ i, P.m i τ).map (· + expo χ τ) := by
  rw [PositivityTheory.Rg.BcB.F.RS.parts, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
  have hmap : ∀ s : Finset (Fin P.c), (∑ i ∈ s, P.m i τ).map (· + expo χ τ) =
      ∑ i ∈ s, (P.m i τ).map (· + expo χ τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add, ih]
  rw [hmap Finset.univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact infOf_twPart P χ τ i

end GlobalTheory.CompanionTheory.JoinInfProof

theorem GlobalTheory.CompanionTheory.JoinInfProof.joinInf : PositivityTheory.Rg.BcB.F.RS.JoinInf := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pb D hJ τ
  rw [sum_m D τ, hJ, List.map_append, List.sum_append, sum_tw Pa χ₁ τ, sum_tw Pb χ₂ τ]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugateStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_character_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), π.HasInfChar τ m → π.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map fun z => -(starRingEnd ℂ) z := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq | exact GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq | (intros; apply GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.RealTateConv

theorem integrable_mulR_abs_rpow_mul_one_add_rpow_neg :
    ∀ (q N : ℝ), 0 < q → q < N →
      MeasureTheory.Integrable (fun a : ℝˣ => |(a : ℝ)| ^ q * (1 + |(a : ℝ)|) ^ (-N)) Ad3.mulR := by
  intro q N hq hN
  have h := GlobalTheory.T.integrable_power_weight_real (q - 1) N (by linarith) (by linarith)
  let g : ℝ → ℂ := fun x => ((|x| ^ q * (1 + |x|) ^ (-N) : ℝ) : ℂ)
  have key : Integrable (fun x : ℝ => |x|⁻¹ • g x) volume := by
    have hc : Integrable (fun x : ℝ => ((|x| ^ (q - 1) * (1 + |x|) ^ (-N) : ℝ) : ℂ)) volume :=
      h.ofReal
    refine hc.congr ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx
    have hpos : 0 < |x| := abs_pos.2 hx
    simp only [g]
    rw [Real.rpow_sub_one hpos.ne', Complex.real_smul]
    push_cast
    ring
  have h2 := ((integrable_mulR_iff g).2 key).re
  simpa [g] using h2

end GlobalTheory.CompanionTheory.RealTateConv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableRadialCutoffWeight
section
noncomputable section

open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.PerUInt.Outer

theorem integrable_rpow_abs_mul_phi (τ : ℝ) (hτ : 0 ≤ τ) (h1 : τ < 1) :
    Integrable (fun x : ℝ => |x| ^ (-τ) * phi x) := by
  have hI : IntegrableOn (fun x : ℝ => x ^ (-τ)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = indicator (Ioc 0 1) (fun x : ℝ => x ^ (-τ)) := ⟨_, rfl⟩
  have hG : Integrable G := hGdef ▸ hI.integrable_indicator measurableSet_Ioc
  have hG' : Integrable (fun x => G (-x)) := hG.comp_neg
  have hGn : ∀ y, 0 ≤ G y := by
    intro y
    rw [hGdef]
    refine indicator_nonneg (fun x hx => Real.rpow_nonneg hx.1.le _) y
  have hD : Integrable (fun x => G x + G (-x) + phi x) := (hG.add hG').add integrable_phi
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by
    simpa [ae_iff] using (measure_singleton (0 : ℝ) : volume {(0 : ℝ)} = 0)
  refine hD.mono' ((continuous_abs.measurable.pow_const (-τ)).mul measurable_phi).aestronglyMeasurable ?_
  filter_upwards [h0] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg x) _) (phi_nonneg x))]
  have hp0 := phi_nonneg x
  have hp1 := phi_le_one x
  have hr0 : 0 ≤ |x| ^ (-τ) := Real.rpow_nonneg (abs_nonneg x) _
  have hGx := hGn x
  have hGnx := hGn (-x)
  by_cases hx1 : |x| ≤ 1
  · have hle : |x| ^ (-τ) * phi x ≤ |x| ^ (-τ) := mul_le_of_le_one_right hr0 hp1
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have hm : -x ∈ Ioc (0 : ℝ) 1 := ⟨by linarith, by rwa [abs_of_neg hneg] at hx1⟩
      have : G (-x) = |x| ^ (-τ) := by
        rw [hGdef, indicator_of_mem hm, abs_of_neg hneg]
      linarith
    · have hm : x ∈ Ioc (0 : ℝ) 1 := ⟨hpos, by rwa [abs_of_pos hpos] at hx1⟩
      have : G x = |x| ^ (-τ) := by
        rw [hGdef, indicator_of_mem hm, abs_of_pos hpos]
      linarith
  · have hge : 1 ≤ |x| := (not_le.1 hx1).le
    have h2 : |x| ^ (-τ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hge (by linarith)
    have h3 : |x| ^ (-τ) * phi x ≤ phi x := mul_le_of_le_one_left hp0 h2
    linarith

theorem rpow_anti {x y r : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hr : r ≤ 0) : y ^ r ≤ x ^ r :=
  Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hr (mem_Ioi.2 hx) (mem_Ioi.2 (hx.trans_le hxy)) hxy

theorem rpow_bound (σ a b : ℝ) (hσ : 0 < σ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a ^ 2 + b ^ 2) ^ (-1 - σ / 2) * ((a ^ 2 + b ^ 2) / max |a| |b|) ≤
      |a| ^ (-((1 + σ) / 2)) * |b| ^ (-((1 + σ) / 2)) := by
  have hA : 0 < |a| := abs_pos.2 ha
  have hB : 0 < |b| := abs_pos.2 hb
  have hma : |a| ≤ max |a| |b| := le_max_left _ _
  have hmb : |b| ≤ max |a| |b| := le_max_right _ _
  have hc : (max |a| |b|) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases max_choice |a| |b| with h | h
    · rw [h, sq_abs]; nlinarith [sq_nonneg b]
    · rw [h, sq_abs]; nlinarith [sq_nonneg a]
  generalize max |a| |b| = m at hma hmb hc ⊢
  generalize a ^ 2 + b ^ 2 = c at hc ⊢
  have hm : 0 < m := lt_of_lt_of_le hA hma
  have hm2 : 0 < m ^ 2 := pow_pos hm 2
  have hc0 : 0 < c := lt_of_lt_of_le hm2 hc
  have e1 : c ^ (-1 - σ / 2) * (c / m) = c ^ (-(σ / 2)) / m := by
    have h : c ^ (-(σ / 2)) = c ^ (-1 - σ / 2) * c := by
      rw [show -(σ / 2) = (-1 - σ / 2) + 1 by ring, Real.rpow_add hc0, Real.rpow_one]
    rw [h]
    ring
  have e2 : c ^ (-(σ / 2)) ≤ (m ^ 2) ^ (-(σ / 2)) :=
    rpow_anti hm2 hc (by linarith)
  have e3 : (m ^ 2) ^ (-(σ / 2)) / m = m ^ (-((1 + σ) / 2)) * m ^ (-((1 + σ) / 2)) := by
    rw [← Real.rpow_natCast m 2, ← Real.rpow_mul hm.le, ← Real.rpow_add hm,
      ← Real.rpow_sub_one hm.ne']
    congr 1
    push_cast
    ring
  have e4 : m ^ (-((1 + σ) / 2)) ≤ |a| ^ (-((1 + σ) / 2)) :=
    rpow_anti hA hma (by linarith)
  have e5 : m ^ (-((1 + σ) / 2)) ≤ |b| ^ (-((1 + σ) / 2)) :=
    rpow_anti hB hmb (by linarith)
  have hmr : 0 ≤ m ^ (-((1 + σ) / 2)) := Real.rpow_nonneg hm.le _
  calc c ^ (-1 - σ / 2) * (c / m) = c ^ (-(σ / 2)) / m := e1
    _ ≤ (m ^ 2) ^ (-(σ / 2)) / m := div_le_div_of_nonneg_right e2 hm.le
    _ = m ^ (-((1 + σ) / 2)) * m ^ (-((1 + σ) / 2)) := e3
    _ ≤ |a| ^ (-((1 + σ) / 2)) * |b| ^ (-((1 + σ) / 2)) :=
      mul_le_mul e4 e5 hmr (Real.rpow_nonneg hA.le _)

theorem integrable_firstColumn : ∀ σ : ℝ, 0 < σ → σ < 1 → Integrable (fun p : ℝ × ℝ =>
    (p.1 ^ 2 + p.2 ^ 2) ^ (-1 - σ / 2) * ((p.1 ^ 2 + p.2 ^ 2) / max |p.1| |p.2|) *
      (phi p.1 * phi p.2)) := by
  intro σ h0 h1
  have hg := integrable_rpow_abs_mul_phi ((1 + σ) / 2) (by linarith) (by linarith)
  have hP : Integrable (fun p : ℝ × ℝ =>
      (|p.1| ^ (-((1 + σ) / 2)) * phi p.1) * (|p.2| ^ (-((1 + σ) / 2)) * phi p.2)) := by
    rw [Measure.volume_eq_prod]
    exact hg.mul_prod hg
  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
    simpa [ae_iff] using (measure_singleton (0 : ℝ) : volume {(0 : ℝ)} = 0)
  have hne1 : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae hne
  have hne2 : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae hne
  have hc : Measurable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) :=
    (measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)
  have hmx : Measurable (fun p : ℝ × ℝ => max |p.1| |p.2|) :=
    (continuous_abs.measurable.comp measurable_fst).max
      (continuous_abs.measurable.comp measurable_snd)
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      (p.1 ^ 2 + p.2 ^ 2) ^ (-1 - σ / 2) * ((p.1 ^ 2 + p.2 ^ 2) / max |p.1| |p.2|) *
        (phi p.1 * phi p.2)) :=
    ((hc.pow_const _).mul (hc.div hmx)).mul
      ((measurable_phi.comp measurable_fst).mul (measurable_phi.comp measurable_snd))
  refine hP.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [hne1, hne2] with p hp1 hp2
  have hc0 : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
  have hm0 : 0 ≤ max |p.1| |p.2| := le_max_of_le_left (abs_nonneg _)
  have hph : 0 ≤ phi p.1 * phi p.2 := mul_nonneg (phi_nonneg _) (phi_nonneg _)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hc0 _) (div_nonneg hc0 hm0)) hph)]
  calc _ ≤ (|p.1| ^ (-((1 + σ) / 2)) * |p.2| ^ (-((1 + σ) / 2))) * (phi p.1 * phi p.2) :=
        mul_le_mul_of_nonneg_right (rpow_bound σ p.1 p.2 h0 hp1 hp2) hph
    _ = _ := by ring

end GlobalTheory.CompanionTheory.PerUInt.Outer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianInvariance
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrInv

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen
  PositivityTheory.SiegelWeilFormula.Gunr Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trPair_add_left (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair (F := F) (E := E) R (A + B) C = trPair (F := F) (E := E) R A C + trPair (F := F) (E := E) R B C := by
  simp only [trPair, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]

theorem trPair_add_right (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair (F := F) (E := E) R A (B + C) = trPair (F := F) (E := E) R A B + trPair (F := F) (E := E) R A C := by
  simp only [trPair, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem multiplicity_add_lattice_preserving {R : Type} [CommRing R] [MeasurableSpace R] {n : ℕ} (lam : Measure (Fin n → R))
    (L : AddSubgroup (Fin n → R)) (b h : Matrix (Fin n) (Fin n) R) (hh : ∀ y ∈ L, h.mulVec y ∈ L) :
    nu2 lam L L (b + h) = nu2 lam L L b := by
  have e : {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + (b + h).mulVec y'} = {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + b.mulVec y'} := by
    ext x
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨y + h.mulVec y', L.add_mem hy (hh y' hy'), y', hy', ?_⟩
      rw [Matrix.add_mulVec]
      abel
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨y - h.mulVec y', L.sub_mem hy (hh y' hy'), y', hy', ?_⟩
      rw [Matrix.add_mulVec]
      abel
  simp only [nu2, e]

section Good

variable {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem trPair_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {A B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) :
    trPair (F := F) (E := E) (Fv F v) A B ∈ v.adicCompletionIntegers F := by
  have e : algebraMap F (Fv F v) (1 / 2) = (2 : Fv F v)⁻¹ := by
    rw [one_div, map_inv₀, map_ofNat]
  rw [trPair, e]
  exact mul_mem hG.half_mem (hG.trace_mem
    (sum_mem fun a _ => sum_mem fun c _ => mul_mem (hA a c) (hB c a)))

theorem gramR_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {Y : Fin n → Fin M → Fv F v ⊗[F] E}
    (hY : Y ∈ latV (M := M) (n := n) bs v) (a c : Fin n) : gramR (Fv F v) σ J Y a c ∈ S := by
  have hmem : ∀ a i, Y a i ∈ S := fun a i => by
    have : Y a i ∈ (S : Set (Fv F v ⊗[F] E)) := by
      rw [hG.carrier]
      exact fun k => hY a i k
    exact this
  have hsig : ∀ x ∈ S, sigR (Fv F v) σ x ∈ S := fun x hx => by
    have := (σS ⟨x, hx⟩).2
    rwa [hG.sig ⟨x, hx⟩] at this
  show ∑ i, ∑ j, sigR (Fv F v) σ (Y a i) * JR (Fv F v) J i j * Y c j ∈ S
  exact sum_mem fun i _ => sum_mem fun j _ =>
    mul_mem (mul_mem (hsig _ (hmem a i)) (hG.J_int i j)) (hmem c j)

theorem jtR_add (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (b h : HermR (Fv F v) σ n) (hh : h ∈ H0 S σ n) :
    jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (b + h) = jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) b := by
  unfold jtR
  congr 1
  funext Y
  by_cases hY : Y ∈ latV (M := M) (n := n) bs v
  · have h1 : ψv (trPair (F := F) (E := E) (Fv F v) (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J Y)) = 1 :=
      hG.psi_of_mem (trPair_mem hG hh (gramR_mem hG hY))
    rw [AddSubgroup.coe_add, trPair_add_left, hG.psi_add, h1, mul_one]
  · simp [Set.indicator_of_notMem hY]

theorem character_add_integral_hermitian (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (hT : ∀ a b, σ (T b a) = T a b)
    (b h : HermR (Fv F v) σ n) (hh : h ∈ H0 S σ n) :
    ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 (b + h).1) = ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 b.1) := by
  have h1 : trPair (F := F) (E := E) (Fv F v) (hermOf (Fv F v) σ T hT).1 h.1 ∈ v.adicCompletionIntegers F :=
    trPair_mem hG (fun i j => hG.T_int i j) hh
  have h2 : ψv (-trPair (F := F) (E := E) (Fv F v) (hermOf (Fv F v) σ T hT).1 h.1) = 1 :=
    hG.psi_of_mem (neg_mem h1)
  rw [AddSubgroup.coe_add, trPair_add_right, neg_add, hG.psi_add, h2, mul_one]

theorem mulVec_mem_L (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (hL : (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hh : ∀ i j, h i j ∈ S) (y : Fin n → Fv F v ⊗[F] E) (hy : y ∈ L) : h.mulVec y ∈ L := by
  have key : ∀ w : Fin n → Fv F v ⊗[F] E, w ∈ L ↔ ∀ a, w a ∈ S := fun w => by
    have e1 : w ∈ L ↔ w ∈ (latO bs v : Set (Fin n → Fv F v ⊗[F] E)) := by
      rw [← hL]; rfl
    have e2 : ∀ x, x ∈ S ↔ x ∈ Rv bs v := fun x => by
      rw [← hG.carrier]; rfl
    rw [e1]
    simp only [e2]
    rfl
  rw [key] at hy ⊢
  intro a
  show ∑ j, h a j * y j ∈ S
  exact sum_mem fun j _ => mul_mem (hh a j) (hy j)

end Good

theorem integrand_invariant_integral_hermitian : HermitianLatticeInvariance := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG hT μv lam L hL z b h hh
  unfold whI
  rw [jtR_add hG μv b h hh, character_add_integral_hermitian hG hT b h hh]
  have e : nu2 lam L L (b + h).1 = nu2 lam L L b.1 := by
    rw [AddSubgroup.coe_add]
    exact multiplicity_add_lattice_preserving lam L _ _ (mulVec_mem_L hG L hL _ hh)
  rw [e]

end GlobalTheory.CompanionTheory.GunrInv

end
end

