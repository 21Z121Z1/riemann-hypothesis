import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0106
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0098
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0107
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0067
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0100

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitDivisibleOfVanishingLevelStatement
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_divisible_of_vanishing_level : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y := by
  first | exact @GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul | exact GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul | (intros; apply GlobalTheory.CompanionTheory.Tower.lim_eq_pow_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorSandwichApproxStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_sandwich_approx : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ), IsStdV v lam → (∀ s, 0 ≤ g s) → GoodFac v lam C g → ∀ η : ℝ, 0 < η → ∃ ψm ψp : Fv F v → ℝ, Continuous ψm ∧ HasCompactSupport ψm ∧ Continuous ψp ∧ HasCompactSupport ψp ∧ (∀ s, 0 ≤ ψm s) ∧ (∀ s, s ≠ 0 → ψm s ≤ g s ∧ g s ≤ ψp s) ∧ 1 - η ≤ ∫ s, ψm s ∂lam ∧ ∫ s, ψp s ∂lam ≤ 1 + η := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.exists_sandwich | exact GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.exists_sandwich | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.exists_sandwich <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyInnerProductStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mackey_inner_product : ReciprocityTheory.Ty.Fin.St.MackeyIp := by
  first | exact @GlobalTheory.CompanionTheory.MackeyFn.mackeyIp | exact GlobalTheory.CompanionTheory.MackeyFn.mackeyIp | (intros; apply GlobalTheory.CompanionTheory.MackeyFn.mackeyIp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProperStatement
section
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_embedding_of_injective_proper : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (W : Set V), IsOpen W → ∀ (B B' : Set X), IsOpen B → IsOpen B' → B' ⊆ B → ∀ fib fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B ∩ W) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B' ∩ W) ν B' fib' → ∀ b ∈ B', fib' b = fib b := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter | exact GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter | (intros; apply GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultipliableLocalFactorsStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multipliable_local_factors : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), (∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ β : F, β ≠ 0 → Multipliable fun v => g v (algebraMap F (Fv F v) β) := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors | exact GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.multipliable_localFactors <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetConjugateNegOfProdStatement
section
open Formalism.REAL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiset_conjugate_neg_of_prod : ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n → (∀ u : ℂ, (m.map (u + ·)).prod = (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) → m' = m.map fun z => -(starRingEnd ℂ) z := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq | exact GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq | (intros; apply GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatTransUpToSqPullback
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CoefUpTo

theorem coef_upTo : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    {F F' : C ⥤ ModuleCat.{w} R} (α : F ⟶ F') (s : R), (∀ T, UpTo s (α.app T).hom) →
    ∀ n, UpTo (s ^ 2) ((Mor.ofNatTrans α).pull n) := by
  intro R _ C _ F F' α s h n
  have inj : ∀ k (f : Cn F k), (Mor.ofNatTrans α).pullC k f = 0 → s • f = 0 := fun k f hf =>
    funext fun c => (h _).1 (f c) (congrFun hf c)
  have surj : ∀ k (g : Cn F' k), ∃ f : Cn F k, (Mor.ofNatTrans α).pullC k f = s • g := fun k g => by
    choose f hf using fun c : ComposableArrows C k => (h (c.obj (Fin.last k))).2 (g c)
    exact ⟨f, funext hf⟩
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
    have hz : (cx F').d n ((Mor.ofNatTrans α).pullC n a) = 0 := by
      have ha' : d F n a = 0 := ha
      change d F' n _ = 0
      rw [Mor.d_pullC, ha', map_zero]
    have hx' : (cx F').cls ((Mor.ofNatTrans α).pullC n a) hz = 0 := hx
    rw [(CrystallineSemistableComparison.P.cls_surj (cx F') n).2.1] at hx'
    have hd : (cx F).d n ((s ^ 2) • a) = 0 := by rw [map_smul, ha, smul_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj (cx F) n).2.2.2.2 (s ^ 2) a ha hd, (CrystallineSemistableComparison.P.cls_surj (cx F) n).2.1]
    cases n with
    | zero =>
      have h0 : (Mor.ofNatTrans α).pullC 0 a = 0 := hx'
      have h1 : (s ^ 2) • a = 0 := by rw [pow_two, mul_smul, inj 0 a h0, smul_zero]
      rw [h1]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨g', hg'⟩ := hx'
      have hg'' : d F' n g' = (Mor.ofNatTrans α).pullC (n + 1) a := hg'
      obtain ⟨g, hg⟩ := surj n g'
      have h0 : (Mor.ofNatTrans α).pullC (n + 1) (s • a - d F n g) = 0 := by
        rw [map_sub, ← Mor.d_pullC, hg, map_smul, map_smul, hg'']
        simp
      have h1 := inj _ _ h0
      rw [smul_sub, sub_eq_zero] at h1
      refine ⟨s • g, ?_⟩
      change d F n (s • g) = (s ^ 2) • a
      rw [map_smul, ← h1, pow_two, mul_smul]
  · obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F') n).1 y
    have hb' : d F' n b = 0 := hb
    obtain ⟨f, hf⟩ := surj n b
    have h0 : (Mor.ofNatTrans α).pullC (n + 1) (d F n f) = 0 := by
      rw [← Mor.d_pullC, hf, map_smul, hb', smul_zero]
    have h1 : d F n (s • f) = 0 := by rw [map_smul]; exact inj _ _ h0
    have hd : (cx F').d n ((s ^ 2) • b) = 0 := by rw [map_smul, hb, smul_zero]
    have e : (Mor.ofNatTrans α).pullC n (s • f) = (s ^ 2) • b := by
      rw [map_smul, hf, pow_two, mul_smul]
    refine ⟨(cx F).cls (s • f) h1, ?_⟩
    rw [← (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.2.2.2 (s ^ 2) b hb hd]
    change (cx F').cls ((Mor.ofNatTrans α).pullC n (s • f)) _ = _
    simp only [e]

end GlobalTheory.CompanionTheory.CoefUpTo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationOfDichotomyStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newton_approximation_of_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := by
  first | exact @GlobalTheory.CompanionTheory.NewtonStep.step_comp | exact GlobalTheory.CompanionTheory.NewtonStep.step_comp | (intros; apply GlobalTheory.CompanionTheory.NewtonStep.step_comp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapThirdPropertyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_third_property : PositivityTheory.Rg.Tf.Loc.N1 → PositivityTheory.Rg.Tf.Loc.N2 → PositivityTheory.Rg.Tf.Loc.N3 := by
  first | exact @GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective | exact GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective | (intros; apply GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalRiemannExtensionLocal
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Branch

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets MvPolynomial Topology Filter Metric

theorem normalRiemannExtensionLocal (hud : LocalUniversalDenominator.Statement)
    (hbq : NormalBoundedQuotient.Statement) (hvan : VanishNearPoint.Statement) :
    NormalRiemannExtensionLocal.Statement := by
  intro σ _ I h w U f hI hIc hh hw hU hf hb
  classical
  have hpoly : ∀ q : MvPolynomial σ ℂ, Differentiable ℂ (fun z : σ → ℂ => eval z q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [eval_add]; exact hp.add hq
    | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)
  obtain ⟨g, hg, N, hNo, hwN, hNU, F, hF, hFg⟩ := hud σ I h w U f hI hh hw hU hf hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hhg : h * g ∉ I := fun hm => (hI.mem_or_mem hm).elim hh hg
  obtain ⟨B, hBo, hwB, hBN, hdense⟩ : ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ N ∧
      zeroSetIn I ∩ B ⊆ closure ((zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0}) := by
    refine ⟨N, hNo, hwN, subset_rfl, fun z hz => ?_⟩
    have h1 := hNo.inter_closure ⟨hz.2, zeroSetIn_subset_closure_diff hvan I (h * g) hI hhg hz.1⟩
    refine closure_mono (fun y hy => ?_) h1
    exact ⟨⟨hy.2.1, hy.1⟩, hy.2.2⟩
  set T := (zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0} with hT
  have hGd : Differentiable ℂ (fun z : σ → ℂ => eval z g) := hpoly g

  have hTS : ∀ z ∈ T, z ∈ (zeroSetIn I ∩ U) \ {z | eval z h = 0} ∧ eval z g ≠ 0 ∧
      eval z g * f z = F z := by
    intro z hz
    have hz2 : eval z h ≠ 0 ∧ eval z g ≠ 0 := by
      simpa only [Set.mem_ofPred_eq, eval_mul, mul_eq_zero, not_or] using hz.2
    exact ⟨⟨⟨hz.1.1, hNU (hBN hz.1.2)⟩, hz2.1⟩, hz2.2,
      hFg z ⟨⟨hz.1.1, hBN hz.1.2⟩, hz2.1⟩⟩
  have hTf : ∀ z ∈ T, F z / eval z g = f z := fun z hz => by
    obtain ⟨-, hg0, he⟩ := hTS z hz
    rw [← he, mul_div_cancel_left₀ _ hg0]
  have hbound : (fun z => F z / eval z g) '' ((zeroSetIn I ∩ B) \ {z | eval z g = 0}) ⊆
      Metric.closedBall 0 M := by
    rintro _ ⟨p, hp, rfl⟩
    have hpc : p ∈ closure T := hdense hp.1
    have hcont : ContinuousWithinAt (fun z => F z / eval z g) T p :=
      (((hF.continuousOn.continuousAt (hNo.mem_nhds (hBN hp.1.2))).div
        (hGd p).continuousAt hp.2)).continuousWithinAt
    refine closure_minimal ?_ Metric.isClosed_closedBall (hcont.mem_closure_image hpc)
    rintro _ ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖F z / eval z g‖ ≤ M
    rw [hTf z hz]
    exact hM _ ⟨z, (hTS z hz).1, rfl⟩
  have hnv : ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z g = 0) := by
    intro hev
    obtain ⟨z, hzW, hzT⟩ := mem_closure_iff_nhds.1 (hdense ⟨hw, hwB⟩) _ hev
    exact (hTS z hzT).2.1 (hzW hzT.1.1)
  obtain ⟨V, hVo, hwV, H, hH, hFGH⟩ := hbq σ I w B F (fun z => eval z g) hI hIc hw hBo hwB
    (hF.mono hBN) hGd.differentiableOn hnv ((Metric.isBounded_closedBall).subset hbound)
  refine ⟨V ∩ B, hVo.inter hBo, ⟨hwV, hwB⟩, fun z hz => hNU (hBN hz.2), H, hH.mono Set.inter_subset_left, ?_⟩
  intro p hp
  obtain ⟨Up, hUpo, hpUp, Fp, hFp, hfFp⟩ :=
    hf p ⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩
  rw [hfFp ⟨⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩, hpUp⟩]

  set O := V ∩ Up
  have hOo : IsOpen O := hVo.inter hUpo
  have hpO : p ∈ O := ⟨hp.1.2.1, hpUp⟩
  set s := O ∩ T
  have heq : Set.EqOn H Fp s := by
    intro z hz
    obtain ⟨hzS, hg0, he⟩ := hTS z hz.2
    have h1 : eval z g * H z = eval z g * f z := by
      rw [he, hFGH z ⟨hz.2.1.1, hz.1.1⟩]
    rw [mul_left_cancel₀ hg0 h1, hfFp ⟨hzS, hz.1.2⟩]
  have hsO : insert p s ⊆ O := Set.insert_subset_iff.2 ⟨hpO, fun z hz => hz.1⟩
  exact heq.of_subset_closure ((hH.mono Set.inter_subset_left).continuousOn.mono hsO)
    ((hFp.mono Set.inter_subset_right).continuousOn.mono hsO) (Set.subset_insert p s)
    (Set.insert_subset_iff.2 ⟨hOo.inter_closure ⟨hpO, hdense ⟨hp.1.1, hp.1.2.2⟩⟩, subset_closure⟩)
    (Set.mem_insert p s)

theorem irreducibleGermCurve
    (hslice : ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w →
      GermIrreducibleAt X w → AccPt w (𝓟 X) →
      ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧
        IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧
        ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0)
    (hdisc : ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ)
      (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), IsAnalyticNear Y w → GermIrreducibleAt Y w →
      (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) →
      (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0) →
      ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N)
    (hCv : CentredDiscCoverCurve.Statement) : IrreducibleGermCurve.Statement := by
  intro σ _ X w hX hirr hacc
  obtain ⟨Y, W, A, hW, hYX, hYa, hYi, hiso, hdom⟩ := hslice σ X w hX hirr hacc
  obtain ⟨Y', p, ρ, N, hY'Y, hcov⟩ := hdisc σ Y w A hYa hYi hiso hdom
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγY⟩ := hCv σ Y' w p ρ N hcov
  have hcont : ContinuousAt γ 0 := hγd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
  have hpre : γ ⁻¹' W ∈ 𝓝 (0 : ℂ) := hcont.preimage_mem_nhds (by rw [hγ0]; exact hW)
  obtain ⟨r', hr', hsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hpre (ball_mem_nhds (0 : ℂ) hr))
  have hle : ball (0 : ℂ) r' ⊆ ball 0 r := fun t ht => (hsub ht).2
  exact ⟨r', hr', γ, hγd.mono hle, hγi.mono hle, hγ0,
    fun t ht => hYX ⟨hY'Y (hγY (hle ht)), (hsub ht).1⟩⟩

end GlobalTheory.CompanionTheory.Ar.Branch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatementStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pattern_group_statement : ReciprocityTheory.Ty.Fin.St.PatGroup := by
  first | exact @GlobalTheory.CompanionTheory.PatGrp.patGroup | exact GlobalTheory.CompanionTheory.PatGrp.patGroup | (intros; apply GlobalTheory.CompanionTheory.PatGrp.patGroup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternSetCardColumnStep
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

theorem isPat_colGe (d j : ℕ) : IsPat (colGe d j) := by
  refine ⟨fun i h => lt_irrefl _ h.1, ?_⟩
  intro a b c hab hbc
  exact ⟨hab.1.trans hbc.1, hbc.2⟩

def colGeSplit (d j : ℕ) (hj : j < d) :
    Fin j ⊕ {p : Fin d × Fin d // colGe d (j + 1) p.1 p.2} →
      {p : Fin d × Fin d // colGe d j p.1 p.2}
  | Sum.inl i => ⟨(⟨i.1, i.2.trans hj⟩, ⟨j, hj⟩), by
      refine ⟨?_, le_refl _⟩
      exact Fin.mk_lt_mk.2 i.2⟩
  | Sum.inr p => ⟨p.1, p.2.1, Nat.le_of_succ_le p.2.2⟩

theorem colGeSplit_bijective (d j : ℕ) (hj : j < d) : Function.Bijective (colGeSplit d j hj) := by
  constructor
  · rintro (a | a) (b | b) h
    · have h1 := congrArg (fun x => (x.1.1 : Fin d).1) h
      simp only [colGeSplit] at h1
      exact congrArg Sum.inl (Fin.ext h1)
    · have h1 := congrArg (fun x => (x.1.2 : Fin d).1) h
      simp only [colGeSplit] at h1
      have := b.2.2
      omega
    · have h1 := congrArg (fun x => (x.1.2 : Fin d).1) h
      simp only [colGeSplit] at h1
      have := a.2.2
      omega
    · have h1 := congrArg (fun x => x.1) h
      simp only [colGeSplit] at h1
      exact congrArg Sum.inr (Subtype.ext h1)
  · rintro ⟨⟨i, l⟩, hil, hjl⟩
    by_cases e : (l : ℕ) = j
    · have hi : (i : ℕ) < j := by
        have : (i : ℕ) < l := hil
        omega
      refine ⟨Sum.inl ⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      simp only [colGeSplit]
      exact Prod.ext rfl (Fin.ext e.symm)
    · have hl : j + 1 ≤ (l : ℕ) := by
        have : j ≤ (l : ℕ) := hjl
        omega
      exact ⟨Sum.inr ⟨(i, l), hil, hl⟩, rfl⟩

theorem natCard_colGe (d j : ℕ) (hj : j < d) :
    Nat.card {p : Fin d × Fin d // colGe d j p.1 p.2} =
      j + Nat.card {p : Fin d × Fin d // colGe d (j + 1) p.1 p.2} := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (colGeSplit_bijective d j hj)), Nat.card_sum,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ncard_patSet_colGe (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (hj : j < d) :
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard := by
  rw [GlobalTheory.CompanionTheory.PatGrp.card_patSet (isPat_colGe d j), GlobalTheory.CompanionTheory.PatGrp.card_patSet (isPat_colGe d (j + 1)),
    natCard_colGe d j hj, pow_add]

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end

