import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurablePeriodicArchRestriction
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SobClass.ClassMeas

theorem slice_le {G V : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [T2Space V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (ν₀ : Measure V) [ν₀.IsAddHaarMeasure]
    (ι : V →+ G) (π : G →+ V) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) {K : Set G}
    (hK : IsCompact K) (h0 : {w | w - ι (π w) ∈ K} ∈ 𝓝 (0 : G)) :
    ∃ c : NNReal, ∀ (J : Type) [Fintype J] (t : J → G) (K' : Set G), IsCompact K' → (∀ k ∈ K, ∃ j, k - t j ∈ K') →
      ∀ f : G → ENNReal, (∀ x, ∀ k ∈ K', f (x + k) = f x) → ∀ x, Measurable (fun y => f (x + ι y)) →
        ∫⁻ y, f (x + ι y) ∂ν₀ ≤ c * (Fintype.card J * ∫⁻ w, f w ∂μ) := by
  set W : Set G := {w | w - ι (π w) ∈ K} with hW
  have hp : Continuous fun w => w - ι (π w) := continuous_id.sub (hι.comp hπ)
  have hV : MeasurableSet W := (hK.isClosed.preimage hp).measurableSet
  have hsub : ∀ B : Set V, π ⁻¹' B ∩ W ⊆ (fun p : G × V => p.1 + ι p.2) '' (K ×ˢ B) := fun B w hw =>
    ⟨(_, _), ⟨hw.2, hw.1⟩, sub_add_cancel _ _⟩
  let ν : Measure V := (μ.restrict W).map π
  have hν : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ W) := fun A hA => by
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have : IsFiniteMeasureOnCompacts ν := ⟨fun A hA => by
    rw [hν A hA.measurableSet]
    exact (measure_mono (hsub A)).trans_lt
      ((hK.prod hA).image (continuous_fst.add (hι.comp continuous_snd))).measure_lt_top⟩
  have : ν.IsAddLeftInvariant := (forall_measure_preimage_add_iff ν).1 fun t A hA => by
    rw [hν A hA, hν _ (measurable_const_add t hA), ← measure_preimage_add μ (ι t) (π ⁻¹' A ∩ W)]
    congr 1
    ext w
    simp only [hW, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, map_add, hπι, add_sub_add_left_eq_sub]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • ν₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul ν ν₀⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := hν Set.univ MeasurableSet.univ
    rw [hc, zero_smul, Set.preimage_univ, Set.univ_inter] at h1
    exact (Measure.measure_pos_of_mem_nhds μ h0).ne h1
  refine ⟨c⁻¹, fun J _ t K' hK' hcov f hf x hm => ?_⟩
  have e1 : ∫⁻ y, f (x + ι y) ∂ν = c * ∫⁻ y, f (x + ι y) ∂ν₀ := by
    rw [hc, lintegral_smul_measure]; rfl
  have e2 : ∫⁻ y, f (x + ι y) ∂ν ≤ Fintype.card J * ∫⁻ w, f w ∂μ := by
    let S : J → Set G := fun j => {w | w - ι (π w) - t j ∈ K'}
    have hS : ∀ j, MeasurableSet (S j) := fun j =>
      (hK'.isClosed.preimage (hp.sub continuous_const)).measurableSet
    have hWS : W ⊆ ⋃ j, S j := fun w hw => Set.mem_iUnion.2 (hcov _ hw)
    rw [lintegral_map hm hπ.measurable]
    refine (lintegral_mono_set hWS).trans ((lintegral_iUnion_le _ _).trans ?_)
    rw [tsum_fintype, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
    rw [setLIntegral_congr_fun (g := fun w => f (x - t j + w)) (hS j) (fun w hw => by
      show f (x + ι (π w)) = f (x - t j + w)
      rw [← hf _ _ hw]
      congr 1
      abel)]
    exact (setLIntegral_le_lintegral _ _).trans (lintegral_add_left_eq_self f _).le
  rw [e1] at e2
  rw [ENNReal.coe_inv hc0]
  exact (ENNReal.mul_le_iff_le_inv (ENNReal.coe_ne_zero.2 hc0) ENNReal.coe_ne_top).1 e2

variable (F : Type) [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  have : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem isOpen_int : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

theorem card_quot (m : ℕ) : Nat.card (𝓞 F ⧸ Ideal.span {(m : 𝓞 F)}) = m ^ Module.finrank ℤ (𝓞 F) := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
    ← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap]
  simp

theorem exists_rep (m : ℕ) (hm : 1 ≤ m) (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    ∃ (q : 𝓞 F ⧸ Ideal.span {(m : 𝓞 F)}) (b : FiniteAdeleRing (𝓞 F) F), (∀ v, b v ∈ v.adicCompletionIntegers F) ∧
      a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) q.out = m * b := by
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F (m : 𝓞 F) (by exact_mod_cast (by omega : m ≠ 0)) a ha
  obtain ⟨s, hs⟩ : ∃ s, s * (m : 𝓞 F) = r - (Ideal.Quotient.mk (Ideal.span {(m : 𝓞 F)}) r).out := by
    rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq]
    exact (Quotient.out_eq _).symm
  refine ⟨Ideal.Quotient.mk _ r, y + algebraMap (𝓞 F) _ s, fun v => add_mem (hy v) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v s), ?_⟩
  have := congrArg (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F)) hs
  rw [map_mul, map_sub, map_natCast] at this
  rw [map_natCast] at e
  rw [e]
  linear_combination -this

theorem class_meas : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (a : ℕ) (C : ℝ), ∀ m : ℕ, 1 ≤ m → ∀ f : (κ → AF F) → ENNReal, (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → f (x + (m : AF F) • a') = f x) → ∀ x : κ → AF F, Measurable (fun y : κ → mixedEmbedding.mixedSpace F => f (x + GlobalTheory.SobClass.archInc F y)) → ∫⁻ y : κ → mixedEmbedding.mixedSpace F, f (x + GlobalTheory.SobClass.archInc F y) ≤ ENNReal.ofReal (C * (m : ℝ) ^ a) * ∫⁻ z, f z ∂μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := t2Space_adeleRing_of_numberField F
  refine ⟨Measure.addHaar, inferInstance, ?_⟩
  let ι : (κ → mixedEmbedding.mixedSpace F) →+ (κ → AF F) := AddMonoidHom.mk' (archInc F) archInc_add
  let π : (κ → AF F) →+ (κ → mixedEmbedding.mixedSpace F) := AddMonoidHom.mk' (fun z i => evI F (z i))
    (fun z z' => funext fun i => map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (z i).1 (z' i).1)
  have hι : Continuous ι := continuous_pi fun i =>
    Continuous.prodMk ((continuous_ofMixed F).comp (continuous_apply i)) continuous_const
  have hπ : Continuous π := continuous_pi fun i =>
    (continuous_toMixed F).comp (continuous_fst.comp (continuous_apply i))
  have hπι : ∀ y, π (ι y) = y := fun y => funext fun i => evI_archInc y i
  let I : Set (FiniteAdeleRing (𝓞 F) F) := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  let K : Set (κ → AF F) := Set.pi Set.univ fun _ => (({0} : Set (Ainf F)) ×ˢ I : Set (Ainf F × Af F))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_singleton.prod (GlobalTheory.AdeleCocompact.isCompact_integral F)
  have h0 : {w | w - ι (π w) ∈ K} ∈ 𝓝 (0 : κ → AF F) := by
    have ho : IsOpen (Set.pi Set.univ fun _ : κ => {a : AF F | a.2 ∈ I}) :=
      isOpen_set_pi Set.finite_univ fun _ _ => (isOpen_int F).preimage continuous_snd
    refine mem_of_superset (ho.mem_nhds fun i _ v => zero_mem _) fun w hw i _ => ⟨?_, ?_⟩
    · show (w i).1 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1) = 0
      rw [RingEquiv.symm_apply_apply, sub_self]
    · show (w i).2 - 0 ∈ I
      rw [sub_zero]
      exact hw i trivial
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc⟩ := slice_le (Measure.addHaar : Measure (κ → AF F)) volume ι π hι hπ hπι hK h0
  refine ⟨Module.finrank ℤ (𝓞 F) * Fintype.card κ, c, fun m hm f hf x hx => ?_⟩
  have hcard := card_quot F m
  haveI : Finite (𝓞 F ⧸ Ideal.span {(m : 𝓞 F)}) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {(m : 𝓞 F)})
  have key := hc (κ → 𝓞 F ⧸ Ideal.span {(m : 𝓞 F)})
    (fun q i => pairA F 0 (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) (q i).out)) ((fun a => (m : AF F) • a) '' K)
    (hK.image (continuous_const_smul _)) ?_ f ?_ x hx
  · rw [Fintype.card_fun, ← Nat.card_eq_fintype_card, hcard, ← pow_mul, ← mul_assoc] at key
    refine key.trans (le_of_eq ?_)
    congr 1
    rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ← Nat.cast_pow, ENNReal.ofReal_natCast]
  · intro k hk
    choose q b hb e using fun i => exists_rep F m hm (k i).2 (hk i trivial).2
    refine ⟨q, fun i => pairA F 0 (b i), fun i _ => ⟨rfl, hb i⟩, funext fun i => Prod.ext ?_ (e i).symm⟩
    have : (k i).1 = 0 := (hk i trivial).1
    show ((m : AF F)).1 * 0 = (k i).1 - 0
    rw [this, mul_zero, sub_zero]
  · rintro z _ ⟨a, ha, rfl⟩
    refine hf z a fun i => ⟨?_, (ha i trivial).2⟩
    have : (a i).1 = 0 := (ha i trivial).1
    rw [evI, this, map_zero]

end GlobalTheory.SobClass.ClassMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormArchLeSupInfinite
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ThetaDecay

theorem archAt_eq_ext (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (a : AF F) :
    archAt F w a = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := rfl

theorem evI_fst (F : Type) [Field F] [NumberField F] (a : AF F) (v : {w : InfinitePlace F // w.IsReal}) :
    ((evI F a).1 v : ℂ) = archAt F v.1 a := by
  rw [archAt_eq_ext, evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

theorem evI_snd (F : Type) [Field F] [NumberField F] (a : AF F) (v : {w : InfinitePlace F // w.IsComplex}) :
    (evI F a).2 v = archAt F v.1 a := by
  rw [archAt_eq_ext, evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]

theorem norm_evI_sup : ∀ (F : Type) [Field F] [NumberField F] (a : AF F),
    (∀ w, ‖archAt F w a‖ ≤ ‖evI F a‖) ∧ ∀ B : ℝ, 0 ≤ B → (∀ w, ‖archAt F w a‖ ≤ B) → ‖evI F a‖ ≤ B := by
  intro F _ _ a
  refine ⟨fun w => ?_, fun B hB h => ?_⟩
  · rcases w.isReal_or_isComplex with hw | hw
    · have e := evI_fst F a ⟨w, hw⟩
      have : ‖archAt F w a‖ = ‖(evI F a).1 ⟨w, hw⟩‖ := by
        rw [← e, Complex.norm_real]
      rw [this]
      exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
    · have e := evI_snd F a ⟨w, hw⟩
      have : ‖archAt F w a‖ = ‖(evI F a).2 ⟨w, hw⟩‖ := by rw [e]
      rw [this]
      exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
  · rw [Prod.norm_def, max_le_iff]
    refine ⟨(pi_norm_le_iff_of_nonneg hB).2 fun v => ?_, (pi_norm_le_iff_of_nonneg hB).2 fun v => ?_⟩
    · have := h v.1
      rw [← evI_fst F a v, Complex.norm_real] at this
      exact this
    · have := h v.1
      rw [← evI_snd F a v] at this
      exact this

end GlobalTheory.ThetaDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddNormPowLeSumLinearFormPowStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_norm_pow_le_sum_linearForm_pow : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ), ∃ (K : ℕ) (l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (C : ℝ), (∀ j, ‖l j‖ ≤ 1) ∧ ∀ y, (1 + ‖y‖) ^ N ≤ C * (1 + ∑ j, |l j y| ^ N) := by
  first | exact @GlobalTheory.ArchDecay.onePlusNormPow_le_sum_linearForm_pow | exact GlobalTheory.ArchDecay.onePlusNormPow_le_sum_linearForm_pow | (intros; apply GlobalTheory.ArchDecay.onePlusNormPow_le_sum_linearForm_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorFamilyAdjointLiftSingleEigensystemStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorFamily_adjointLift_single_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∃ Tc : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H, (∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = Tc i (R.jX A3.A.μ0 f)) ∧ ∀ c, ∃ x : (A3.rowI A3.A.μ0).OpIx → ℂ, ∀ w ∈ R.EEc c, ∀ i, Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = x i • LinearMap.adjoint (R.Th A3.A.μ0) w := by
  first | exact @GlobalTheory.UpSystem.up_sys | exact GlobalTheory.UpSystem.up_sys | (intros; apply GlobalTheory.UpSystem.up_sys <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaLevel

theorem heis_fix : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Φ ∈ schA F κ, ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ a b : κ → AF F, IsMulInt F m₀ a → IsMulInt F m₀ b → schr ψ (a, b) Φ = Φ := by
  intro F _ _ κ _ ψ hψ Φ hΦ
  obtain ⟨m₃, hm₃, h3⟩ := GlobalTheory.PsiTriv.exists_nat_trivial ψ hψ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨m₁, hm₁, h1⟩ := GlobalTheory.SBTransl.transInv g hg
    obtain ⟨M, hM, h2⟩ := GlobalTheory.SuppDen.support_bounded_denominators g hg
    exact ⟨2 * m₁ * M * m₃, by positivity, GlobalTheory.PureFix.pureA_fixed ψ g m₁ M m₃ hm₁ hM hm₃ h1 h2 h3 f⟩
  | zero =>
    refine ⟨1, one_pos, fun a b _ _ => ?_⟩
    funext x; simp [schr]
  | add x y _ _ hx hy =>
    obtain ⟨k, hk, hx⟩ := hx
    obtain ⟨l, hl, hy⟩ := hy
    refine ⟨k * l, by positivity, fun a b ha hb => ?_⟩
    have ha' : IsMulInt F k a := IsMulInt.mono (k := l) (by rwa [mul_comm] at ha)
    have hb' : IsMulInt F k b := IsMulInt.mono (k := l) (by rwa [mul_comm] at hb)
    have e1 := hx a b ha' hb'
    have e2 := hy a b ha.mono hb.mono
    funext z
    have hx1 := congrFun e1 z
    have hy1 := congrFun e2 z
    simp only [schr, Pi.add_apply, mul_add] at hx1 hy1 ⊢
    rw [hx1, hy1]
  | smul c x _ hx =>
    obtain ⟨k, hk, hx⟩ := hx
    refine ⟨k, hk, fun a b ha hb => ?_⟩
    funext z
    have hx1 := congrFun (hx a b ha hb) z
    simp only [schr, Pi.smul_apply, smul_eq_mul] at hx1 ⊢
    rw [mul_left_comm, hx1]

open Formalism.UG in

theorem transport_denom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)),
    ∃ C : ℝ, ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ N : ℕ, 0 < N ∧
      (N : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ∧
      ∀ (M : ℕ) (y : Fin n × Fin d → AF F), IsMulInt F (M * N) y →
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).1 ∧
        IsMulInt F M (e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ)).2 := by
  intro F E _ _ _ _ _ n d e
  classical
  set Y : Fin n × Fin d → Matrix (Fin n) (Fin d) (AF F ⊗[F] E) :=
    fun j => e.symm (0, fun k => if j = k then 1 else 0) with hY
  let f1 : Fin n × Fin d → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) :=
    fun i => (LinearMap.proj i).comp ((LinearMap.fst (AF F) _ _).comp e.toLinearMap)
  let f2 : Fin n × Fin d → (Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) :=
    fun i => (LinearMap.proj i).comp ((LinearMap.snd (AF F) _ _).comp e.toLinearMap)
  choose K1 hK1f hK11 hK1 using fun i => GlobalTheory.LinFormBound.main (f1 i)
  choose K2 hK2f hK21 hK2 using fun i => GlobalTheory.LinFormBound.main (f2 i)
  choose KY hKYf hKY1 hKY using fun j => GlobalTheory.FixedBound.exists_entry_absFin_bound (Y j)
  have prod_one : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i v, 1 ≤ K i v) →
      ∀ v, 1 ≤ ∏ i, K i v := fun K hK v => Finset.one_le_prod' fun i _ => hK i v
  have prod_fin : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i, (Function.mulSupport (K i)).Finite) →
      (Function.mulSupport fun v => ∏ i, K i v).Finite := fun K hK =>
    ((Finset.univ : Finset (Fin n × Fin d)).finite_toSet.biUnion fun i _ => hK i).subset
      (Finset.mulSupport_prod _ _)
  have single_le : ∀ (K : Fin n × Fin d → HeightOneSpectrum (𝓞 F) → ℝ≥0), (∀ i v, 1 ≤ K i v) →
      ∀ i v, K i v ≤ ∏ i, K i v := fun K hK i v => Finset.single_le_prod' (fun j _ => hK j v) (Finset.mem_univ i)
  set Ka : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v with hKa
  have hKa1 : ∀ v, 1 ≤ Ka v := fun v => one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (prod_one K1 hK11 v) (prod_one K2 hK21 v)) (prod_one KY hKY1 v)
  have hKaf : (Function.mulSupport Ka).Finite :=
    ((((prod_fin K1 hK1f).union (prod_fin K2 hK2f)).subset (Function.mulSupport_mul _ _)).union
      (prod_fin KY hKYf)).subset (Function.mulSupport_mul _ _)
  have hle1 : ∀ i j v, K1 i v * KY j v ≤ Ka v := fun i j v =>
    calc K1 i v * KY j v ≤ (∏ i, K1 i v) * ∏ j, KY j v := mul_le_mul' (single_le K1 hK11 i v) (single_le KY hKY1 j v)
      _ ≤ Ka v := by
        show (∏ i, K1 i v) * ∏ j, KY j v ≤ (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v
        rw [mul_right_comm]
        exact le_mul_of_one_le_right' (prod_one K2 hK21 v)
  have hle2 : ∀ i j v, K2 i v * KY j v ≤ Ka v := fun i j v =>
    calc K2 i v * KY j v ≤ (∏ i, K2 i v) * ∏ j, KY j v := mul_le_mul' (single_le K2 hK21 i v) (single_le KY hKY1 j v)
      _ ≤ Ka v := by
        show (∏ i, K2 i v) * ∏ j, KY j v ≤ (∏ i, K1 i v) * (∏ i, K2 i v) * ∏ j, KY j v
        exact mul_le_mul_left (le_mul_of_one_le_left' (prod_one K1 hK11 v)) _
  refine ⟨((∏ᶠ v, Ka v : ℝ≥0) : ℝ), fun g h => ?_⟩
  set B : HeightOneSpectrum (𝓞 F) → ℝ≥0 :=
    fun v => Ka v * htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) with hB
  have hB1 : ∀ v, 1 ≤ B v := fun v =>
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hKa1 v) (one_le_htOf _ _)) (one_le_htOf _ _)
  have hgf := finite_mulSupport_htFin F g
  have hhf := finite_mulSupport_htFin F h
  have hBf : (Function.mulSupport B).Finite :=
    (((hKaf.union hgf).subset (Function.mulSupport_mul _ _)).union hhf).subset (Function.mulSupport_mul _ _)
  obtain ⟨N, hN, hNle, hNint⟩ := GlobalTheory.SmoothForms.denom_global B hB1 hBf
  have hfin : ∀ {m : ℕ} (k : GL (Fin m) (AF F ⊗[F] E)), ∏ᶠ v, htFin F v (bc (compFin F E v) k) ≤ heightGL F k :=
    fun k => by
      unfold heightGL
      exact le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)
  refine ⟨N, hN, ?_, ?_⟩
  · have e1 : ∏ᶠ v, B v = (∏ᶠ v, Ka v) * (∏ᶠ v, htFin F v (bc (compFin F E v) g)) *
        ∏ᶠ v, htFin F v (bc (compFin F E v) h) := by
      rw [hB, finprod_mul_distrib ((hKaf.union hgf).subset (Function.mulSupport_mul _ _)) hhf,
        finprod_mul_distrib hKaf hgf]
    have : (N : ℝ≥0) ≤ (∏ᶠ v, Ka v) * (heightGL F g * heightGL F h) := by
      refine hNle.trans ?_
      rw [e1, mul_assoc]
      exact mul_le_mul_right (mul_le_mul' (hfin g) (hfin h)) _
    exact_mod_cast this
  intro M y hy
  set L : (Fin n × Fin d → AF F) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    e.toLinearMap ∘ₗ sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) ∘ₗ
      e.symm.toLinearMap ∘ₗ LinearMap.inr (AF F) _ _ with hL
  have hLy : e ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, y) * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) =
      ∑ j, y j • L (fun k => if j = k then 1 else 0) := LinearMap.pi_apply_eq_sum_univ L y
  have hsz : ∀ j v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v
      (sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (Y j) p.1 p.2))) ≤
      htFin F v (bc (compFin F E v) g) * KY j v * htFin F v (bc (compFin F E v) h) := fun j v =>
    Finset.sup_le fun p _ => (GlobalTheory.absFin_mul_mul_transpose_le g (Y j) h v p.1 p.2).trans
      (mul_le_mul_left (mul_le_mul_right (hKY j v) _) _)
  have hcomp : ∀ t : Fin n × Fin d → AF F, (∀ j v, ‖evFin F v (t j)‖₊ ≤ B v) →
      (∑ j, y j * t j).1 = 0 ∧ ∀ v, ‖evFin F v (∑ j, y j * t j)‖ ≤ ‖(M : Fv F v)‖ := by
    intro t ht
    refine ⟨?_, fun v => ?_⟩
    · change fstA F (∑ j, y j * t j) = 0
      rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_mul]
      change (y j).1 * _ = 0
      rw [hy.1 j, zero_mul]
    · rw [map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
      rw [map_mul, norm_mul]
      have h1 := hy.2 v j
      have h2 := hNint v (evFin F v (t j)) (ht j v)
      rw [Nat.cast_mul, norm_mul] at h1
      rw [norm_mul] at h2
      calc ‖evFin F v (y j)‖ * ‖evFin F v (t j)‖ ≤ ‖(M : Fv F v)‖ * ‖(N : Fv F v)‖ * ‖evFin F v (t j)‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖(M : Fv F v)‖ * (‖(N : Fv F v)‖ * ‖evFin F v (t j)‖) := mul_assoc _ _ _
        _ ≤ ‖(M : Fv F v)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖(M : Fv F v)‖ := mul_one _
  have htB : ∀ (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F) (K : HeightOneSpectrum (𝓞 F) → ℝ≥0),
      (∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) →
      (∀ j v, K v * KY j v ≤ Ka v) → ∀ j v,
      ‖evFin F v (f (sand (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (Y j)))‖₊ ≤ B v := by
    intro f K hf hK j v
    refine (hf _ v).trans ?_
    refine (mul_le_mul_right (hsz j v) _).trans ?_
    calc K v * (htFin F v (bc (compFin F E v) g) * KY j v * htFin F v (bc (compFin F E v) h)) =
        K v * KY j v * htFin F v (bc (compFin F E v) g) * htFin F v (bc (compFin F E v) h) := by ring
      _ ≤ B v := mul_le_mul_left (mul_le_mul_left (hK j v) _) _
  refine ⟨⟨fun i => ?_, fun v i => ?_⟩, ⟨fun i => ?_, fun v i => ?_⟩⟩
  all_goals rw [hLy]
  all_goals simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  · exact (hcomp _ fun j v => htB (f1 i) (K1 i) (hK1 i) (fun j v => hle1 i j v) j v).1
  · exact (hcomp _ fun j v => htB (f1 i) (K1 i) (hK1 i) (fun j v => hle1 i j v) j v).2 v
  · exact (hcomp _ fun j v => htB (f2 i) (K2 i) (hK2 i) (fun j v => hle2 i j v) j v).1
  · exact (hcomp _ fun j v => htB (f2 i) (K2 i) (hK2 i) (fun j v => hle2 i j v) j v).2 v

theorem periodic_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧ ∀ x a : Fin n × Fin d → AF F, (∀ i, evI F (a i) = 0 ∧ ∀ v, evFin F v (a i) ∈ v.adicCompletionIntegers F) → om (g, h) Φ (x + (m : AF F) • a) = om (g, h) Φ x := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  have hsp := hP.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨m₀, hm₀, hinv⟩ := heis_fix B.ψ hstd.1 Φ hΦ
  obtain ⟨C, hC⟩ := transport_denom (M.co.e.trans (LinearEquiv.prodComm (AF F) _ _))
  refine ⟨m₀ * C, 1, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · rw [pow_one]
    have : ((m₀ * N : ℕ) : ℝ) = m₀ * N := by push_cast; ring
    rw [this, mul_assoc (m₀ : ℝ) C]
    exact mul_le_mul_of_nonneg_left hNle (by positivity)
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (y, 0) (om (g, h) Φ) = om (g, h) Φ := by
    clear hNle hC
    intro y hy
    set w' := M.co.e.symm (y, 0) with hw'
    set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' *
      (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    have hΦw : M.co.rho B.ψ w Φ = Φ := hinv _ _ h2 h1
    have hact : actAB (cA σ) (g, h) w = w' := by
      simp only [actAB, hw]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
        Matrix.mul_one]
    have himpl := hsp.impl (g, h) w Φ hΦ
    rw [hΦw, hact] at himpl
    rw [Darboux.rho, hw', LinearEquiv.apply_symm_apply] at himpl
    exact himpl.symm
  intro x a ha
  have hy : IsMulInt F (m₀ * N) (((m₀ * N : ℕ) : AF F) • a) := by
    refine ⟨fun i => ?_, fun v i => ?_⟩
    · change fstA F (((m₀ * N : ℕ) : AF F) * a i) = 0
      rw [map_mul]
      have h0 : fstA F (a i) = 0 := by
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (ha i).1
      rw [h0, mul_zero]
    · change ‖evFin F v (((m₀ * N : ℕ) : AF F) * a i)‖ ≤ _
      rw [map_mul, map_natCast, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (Valued.toNormedField.norm_le_one_iff.2 ((ha i).2 v))
  have := congrFun (hfix _ hy) x
  simpa [schr] using this

end GlobalTheory.ThetaLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLagrangianSubspaceExistsStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_lagrangian_subspace_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), Module.finrank F E = 2 →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
      ∃ K : Submodule F (Matrix (Fin n) (Fin d) E), Module.finrank F K = n * d ∧ ∀ z ∈ K, (M.co.e (incM F z)).1 = 0 := by
  first | exact @GlobalTheory.MixedLagr.rat_first_zero_dim | exact GlobalTheory.MixedLagr.rat_first_zero_dim | (intros; apply GlobalTheory.MixedLagr.rat_first_zero_dim <;> assumption)
end

