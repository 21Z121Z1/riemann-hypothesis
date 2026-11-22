import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasUpq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay
section
noncomputable section

namespace GlobalTheory.Core.Rk.RapidInt

open scoped TensorProduct ENNReal NNReal ComplexConjugate Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Cont GlobalTheory.GaugeEx GlobalTheory.Core.Rk.NSing
open NumberField.mixedEmbedding
open scoped Classical

section Mixed

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

theorem norm_toMixed_le (y : InfiniteAdeleRing F) :
    ‖InfiniteAdeleRing.ringEquiv_mixedSpace F y‖ ≤ ∑ v, ‖y v‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.norm_def]
  have hS : 0 ≤ ∑ v, ‖y v‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine max_le ((pi_norm_le_iff_of_nonneg hS).2 fun v => ?_) ((pi_norm_le_iff_of_nonneg hS).2 fun v => ?_)
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _)]
    exact Finset.single_le_sum (f := fun w => ‖y w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ v.1)
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _)]
    exact Finset.single_le_sum (f := fun w => ‖y w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ v.1)

end Mixed

section Tup

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (M n : ℕ)

def crdTup : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₗ[Ainf F] (Fin n → Fin M → Fin d → Ainf F) :=
  LinearEquiv.piCongrRight fun _ => LinearEquiv.piCongrRight fun _ =>
    (Algebra.TensorProduct.basis (Ainf F) b).equivFun

def mixTup : (Fin n → Fin M → Fin d → Ainf F) ≃+ (Fin n → Fin M → Fin d → mixedSpace F) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ =>
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv

theorem continuous_crdTup : Continuous (crdTup F E b M n) :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).toLinearMap

theorem continuous_crdTup_symm : Continuous (crdTup F E b M n).symm :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).symm.toLinearMap

theorem continuous_mixTup : Continuous (mixTup F M n (d := d)) :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (continuous_toMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

theorem continuous_mixTup_symm : Continuous (mixTup F M n (d := d)).symm :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (continuous_ofMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

def tupEquiv : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (Fin n → Fin M → Fin d → mixedSpace F) where
  toAddEquiv := (crdTup F E b M n).toAddEquiv.trans (mixTup F M n)
  continuous_toFun := (continuous_mixTup F M n).comp (continuous_crdTup F E b M n)
  continuous_invFun := (continuous_crdTup_symm F E b M n).comp (continuous_mixTup_symm F M n)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2000 in
theorem norm_tupEquiv_le (X : Fin n → Fin M → Ainf F ⊗[F] E) : ‖tupEquiv F E b M n X‖ ≤ sizeTup b X := by
  have h0 : ∀ a i k v, 0 ≤ ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v‖ := fun _ _ _ _ => norm_nonneg _
  have hS : 0 ≤ sizeTup b X := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => h0 a i k v
  refine (pi_norm_le_iff_of_nonneg hS).2 fun a => (pi_norm_le_iff_of_nonneg hS).2 fun i =>
    (pi_norm_le_iff_of_nonneg hS).2 fun k => ?_
  change ‖InfiniteAdeleRing.ringEquiv_mixedSpace F ((Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k)‖ ≤ _
  refine (norm_toMixed_le F _).trans ?_
  calc ∑ v, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v‖ ≤ sizeInf b (X a i) :=
        Finset.single_le_sum (f := fun k => ∑ v, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X a i) k v‖)
          (fun k _ => Finset.sum_nonneg fun v _ => h0 a i k v) (Finset.mem_univ k)
    _ ≤ ∑ i, sizeInf b (X a i) :=
        Finset.single_le_sum (f := fun i => sizeInf b (X a i))
          (fun i _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => h0 a i k v) (Finset.mem_univ i)
    _ ≤ sizeTup b X :=
        Finset.single_le_sum (f := fun a => ∑ i, sizeInf b (X a i))
          (fun a _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun v _ => h0 a i k v)
          (Finset.mem_univ a)

end Tup

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2000 in

theorem integrable_of_rapidDecay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (M n : ℕ) (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μi.IsAddHaarMeasure →
    ∀ Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φi → RapidDecay b Φi → Integrable Φi μi := by
  intro F E _ _ _ _ _ d b M n μi hμ Φi hc hr
  set e := tupEquiv F E b M n with he
  have hmap : (μi.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μi e
  set N : ℕ := Module.finrank ℝ (Fin n → Fin M → Fin d → mixedSpace F) + 1 with hN
  have hint := integrable_one_add_norm (μ := μi.map e) (r := (N : ℝ)) (by rw [hN]; push_cast; linarith)
  obtain ⟨C, hC⟩ := hr N
  have hbd : ∀ X, ‖Φi X‖ ≤ C * (1 + ‖e X‖) ^ (-(N : ℝ)) := by
    intro X
    have h1 : ‖e X‖ ≤ sizeTup b X := norm_tupEquiv_le F E b M n X
    have h2 : 0 ≤ ‖e X‖ := norm_nonneg _
    have hs : 0 < 1 + sizeTup b X := by linarith
    have hw : 0 < 1 + ‖e X‖ := by linarith
    have hC0 : 0 ≤ C := le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg hs.le _)) (hC X)
    rw [Real.rpow_neg hw.le, Real.rpow_natCast, ← div_eq_mul_inv]
    have h3 : ‖Φi X‖ ≤ C / (1 + sizeTup b X) ^ N := by
      rw [le_div_iff₀ (pow_pos hs _)]; exact hC X
    exact h3.trans (div_le_div_of_nonneg_left hC0 (pow_pos hw _) (pow_le_pow_left₀ hw.le (by linarith) _))
  have hg : Integrable (Φi ∘ e.symm) (μi.map e) := by
    refine (hint.const_mul C).mono' (hc.comp e.symm.continuous).aestronglyMeasurable (ae_of_all _ fun w => ?_)
    have := hbd (e.symm w)
    simpa using this
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  rw [hemb.integrable_map_iff] at hg
  simpa [Function.comp_def] using hg

end GlobalTheory.Core.Rk.RapidInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnitaryAdelicEqSumFiniteCosetsRealIntegr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetDisint

theorem integral_eq_of_lintegral_eq {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (m : Measure Y)
    (f : X → ℂ) (g : Y → ℂ) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ c : ℂ → ENNReal, Measurable c → ∫⁻ x, c (f x) ∂μ = ∫⁻ y, c (g y) ∂m) (hi : Integrable f μ) :
    Integrable g m ∧ ∫ x, f x ∂μ = ∫ y, g y ∂m := by
  have e : μ.map f = m.map g := by
    ext S hS
    rw [Measure.map_apply hf hS, Measure.map_apply hg hS]
    have h1 := h (S.indicator 1) (measurable_one.indicator hS)
    have e1 : ∀ x, S.indicator (1 : ℂ → ENNReal) (f x) = (f ⁻¹' S).indicator 1 x := fun x => by
      by_cases hx : f x ∈ S <;> simp [Set.indicator, hx]
    have e2 : ∀ y, S.indicator (1 : ℂ → ENNReal) (g y) = (g ⁻¹' S).indicator 1 y := fun y => by
      by_cases hy : g y ∈ S <;> simp [Set.indicator, hy]
    simp only [e1, e2] at h1
    rwa [lintegral_indicator_one (hf hS), lintegral_indicator_one (hg hS)] at h1
  refine ⟨?_, ?_⟩
  · have h1 : Integrable (fun z : ℂ => z) (μ.map f) :=
      (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).2 hi
    rw [e] at h1
    exact (integrable_map_measure aestronglyMeasurable_id hg.aemeasurable).1 h1
  · have a1 := integral_map (μ := μ) hf.aemeasurable (f := fun z : ℂ => z) aestronglyMeasurable_id
    have a2 := integral_map (μ := m) hg.aemeasurable (f := fun z : ℂ => z) aestronglyMeasurable_id
    rw [← a1, ← a2, e]

variable {D : D7}

theorem continuous_realPt {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} (hW : W.SigOK) {Fr : Frames W}
    (hFr : IsFrames W Fr) : Continuous fun b : (∀ ρ, Upq W ρ) => realElt θ W fun ρ => realMat W Fr ρ (b ρ) := by
  obtain ⟨h1, -, -, -, -⟩ := Formalism.IndefR.Eqv.ga_facts D W
  unfold realElt
  refine continuous_list_prod _ fun ρ _ => ?_
  have hm : Continuous fun b : (∀ ρ, Upq W ρ) => UpqT.mat (b ρ) :=
    (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply ρ)
  refine (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ W ρ).comp_continuous
    (continuous_const.matrix_mul ((continuous_const.matrix_mul hm).matrix_mul continuous_const)) fun b => ?_
  refine conjFrame_mem_UH _ _ _ (sig_sum W hW (tauE D ρ)) _ _ (hFr ρ) ?_ (b ρ)
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ((map_ne_zero _).2 (GlobalTheory.DefiniteQuotient.gram_hermND W).2).isUnit

theorem finE_toFin (W : HSp D) (h : GA D W) : finE W h = finE W (GlobalTheory.AutMult.toFin W h : GA D W) := by
  conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin h]
  rw [map_mul]
  have : finE W (GlobalTheory.AutMult.toInf W h : GA D W) = 1 := by
    show Formalism.UG.bc (swapAE D) (finHom W _) = 1
    rw [MonoidHom.mem_ker.1 (GlobalTheory.AutMult.toInf W h).2, map_one]
  rw [this, one_mul]

end GlobalTheory.CosetDisint

end

namespace GlobalTheory.CosetDisint

theorem integral_eq_cosetSum : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → IsOpen {h : GA D W | finE W h ∈ K} → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ℂ, Continuous Z → Integrable Z ν → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ))‖ₑ ∂(Measure.pi mR) < ⊤ ∧ ∫ g, Z g ∂ν = ∫ b, ∑' x : FinCos W (levA W K), Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  intro D θ hθ W hW K ν hν hO Fr hFr mR hmR Z hZc hZi hZinv
  obtain ⟨i0, -, -, i3, i4⟩ := Formalism.IndefR.Eqv.ga_facts D W
  haveI := i0; haveI := i3; haveI := i4
  haveI : ν.IsHaarMeasure := hν.1
  haveI := Formalism.IndefR.Eqv.gfC_secondCountable D W
  set O : Set (GA D W) := {h | finE W h ∈ K} with hOdef
  have hOm : MeasurableSet O := hO.measurableSet
  set φ : (∀ ρ, Upq W ρ) → GA D W := fun b => realElt θ W fun ρ => realMat W Fr ρ (b ρ) with hφdef
  have hφ : Continuous φ := continuous_realPt hθ hW hFr
  have hZm : Measurable Z := hZc.measurable
  set L' := (levA W K).subgroupOf (GfC W) with hL'
  have hmemL : ∀ y : GfC W, y ∈ L' ↔ finE W (y : GA D W) ∈ K := fun y => by
    rw [hL', Subgroup.mem_subgroupOf, mem_levA]
    exact and_iff_right y.2
  have hL'o : IsOpen (L' : Set (GfC W)) := by
    have : (L' : Set (GfC W)) = Subtype.val ⁻¹' O := Set.ext fun y => hmemL y
    rw [this]; exact hO.preimage continuous_subtype_val

  haveI : Countable (GfC W ⧸ L') := by
    have hpd : (Set.univ : Set (GfC W ⧸ L')).PairwiseDisjoint
        (fun q => (fun x => (Quotient.out q : GfC W)⁻¹ * x) ⁻¹' (L' : Set (GfC W))) := by
      intro q _ q' _ hne
      refine Set.disjoint_left.2 fun x h1 h2 => hne ?_
      have e1 : QuotientGroup.mk (Quotient.out q) = (QuotientGroup.mk x : GfC W ⧸ L') := QuotientGroup.eq.2 h1
      have e2 : QuotientGroup.mk (Quotient.out q') = (QuotientGroup.mk x : GfC W ⧸ L') := QuotientGroup.eq.2 h2
      rw [QuotientGroup.out_eq'] at e1 e2
      exact e1.trans e2.symm
    exact Set.countable_univ_iff.1 (hpd.countable_of_isOpen
      (fun q _ => hL'o.preimage (continuous_const.mul continuous_id))
      (fun q _ => ⟨Quotient.out q, by simp [L'.one_mem]⟩))

  let s : GfC W ⧸ L' → Set (GA D W) := fun q => (fun g => (FinCos.rep q)⁻¹ * g) ⁻¹' O
  have hmem : ∀ q g, g ∈ s q ↔ q = QuotientGroup.mk (GlobalTheory.AutMult.toFin W g) := by
    intro q g
    show finE W ((FinCos.rep q)⁻¹ * g) ∈ K ↔ _
    rw [finE_toFin, map_mul, map_inv, FinCos.rep, GlobalTheory.AutMult.toFin_coe, ← hmemL]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq]
  have hsm : ∀ q, MeasurableSet (s q) := fun q => (measurable_const_mul _) hOm
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro q q' hne
    exact Set.disjoint_left.2 fun g h1 h2 => hne (((hmem q g).1 h1).trans ((hmem q' g).1 h2).symm)
  have hU : (⋃ q, s q) = Set.univ := Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, (hmem _ g).2 rfl⟩

  have key : ∀ q : GfC W ⧸ L', ∀ G : GA D W → ENNReal, Measurable G → (∀ g, ∀ k ∈ levA W K, G (g * k) = G g) →
      ∫⁻ g in s q, G g ∂ν = ∫⁻ b, G (FinCos.rep q * φ b) ∂(Measure.pi mR) := by
    intro q G hG hGi
    have hpre : (fun h => FinCos.rep q * h) ⁻¹' s q = O := by
      ext h; simp [s]
    rw [← (measurePreserving_mul_left ν (FinCos.rep q)).setLIntegral_comp_preimage_emb
      (measurableEmbedding_mulLeft _) G (s q), hpre]
    exact GlobalTheory.T.level_measure_pushforward_eq_product_real_measures D θ hθ W hW K ν hν Fr hFr mR hmR (fun h => G (FinCos.rep q * h)) (hG.comp (measurable_const_mul _))
      (fun g k hk => by simp only [← mul_assoc]; exact hGi _ k hk) hOm
  have hcm : ∀ q : GfC W ⧸ L', Continuous fun b => Z (FinCos.rep q * φ b) := fun q =>
    hZc.comp (continuous_const.mul hφ)

  have hlin : ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * φ b)‖ₑ ∂(Measure.pi mR) = ∫⁻ g, ‖Z g‖ₑ ∂ν := by
    rw [lintegral_tsum fun q => (hcm q).measurable.enorm.aemeasurable]
    rw [← Measure.restrict_univ (μ := ν), ← hU, lintegral_iUnion hsm hd]
    refine tsum_congr fun q => (key q (fun g => ‖Z g‖ₑ) hZm.enorm fun g k hk => by rw [hZinv g k hk]).symm
  have hfin : ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * φ b)‖ₑ ∂(Measure.pi mR) < ⊤ := by
    rw [hlin]; exact hZi.2
  refine ⟨hfin, ?_⟩

  have hint : ∀ q : GfC W ⧸ L', ∫ g in s q, Z g ∂ν = ∫ b, Z (FinCos.rep q * φ b) ∂(Measure.pi mR) := fun q =>
    (integral_eq_of_lintegral_eq (ν.restrict (s q)) (Measure.pi mR) Z _ hZm (hcm q).measurable
      (fun c hc => key q (fun g => c (Z g)) (hc.comp hZm) fun g k hk => by simp only [hZinv g k hk])
      hZi.integrableOn).2
  have hsum := hasSum_integral_iUnion hsm hd (by rw [hU]; exact hZi.integrableOn)
  rw [hU, Measure.restrict_univ] at hsum
  rw [← hsum.tsum_eq, integral_tsum (fun q => (hcm q).aestronglyMeasurable)
    (by rw [← lintegral_tsum fun q => (hcm q).measurable.enorm.aemeasurable]; exact hfin.ne)]
  exact tsum_congr hint

end GlobalTheory.CosetDisint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseRowFourierTransformMemSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaModel

theorem finv_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψk : AddChar k Circle) (ν : Measure k), Continuous ψk → ψk ≠ 1 → ν.IsAddHaarMeasure → ∀ (C : ℂ) (Φ : Matrix Unit n k → ℂ), Φ ∈ SB (Matrix Unit n k) → GlobalTheory.KappaModel.finv ψk ν C Φ ∈ SB (Matrix n Unit k) := by
  intro k _ _ _ _ _ _ n _ _ ψk ν hψ hne hν C Φ hΦ
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψk hψ hne
  let e : (n → k) ≃ₜ Matrix Unit n k :=
    { toFun := fun η => Matrix.of fun _ r => η r
      invFun := fun M => M ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let e' : Matrix n Unit k ≃ₜ (n → k) :=
    { toFun := fun x r => x r ()
      invFun := fun y => Matrix.of fun r _ => y r
      left_inv := fun M => by ext i j; rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hf : (fun η : n → k => Φ (Matrix.of fun _ r => η r)) ∈ SB (n → k) :=
    ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩
  have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n => ν) hc hf
  have eq : finv ψk ν C Φ = fun x => C * (fun y : n → k => ∫ η, Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ : n => ν)) (e' x) := by
    funext x; rfl
  rw [eq]
  refine ⟨?_, ?_⟩
  · exact (hF.1.comp_continuous e'.continuous).comp (fun z => C * z)
  · exact (hF.2.comp_homeomorph e').mul_left

end GlobalTheory.KappaModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvolutionOrthDecBlockSumRealMatStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCartanInvolution_orthDecBlockSumRealMat : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H), (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → ∀ τ, IsCartanInv (gramAt D B τ) (sumMat o sW sH τ) := by
  first | exact @GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat | exact GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat | (intros; apply GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem isHeckeChar_resEta_inv : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (m : ℕ), IsHeckeChar D χ → ResEta D χ m → IsHeckeChar D χ⁻¹ ∧ ResEta D χ⁻¹ m := by
  intro D χ m h1 h2
  refine ⟨⟨h1.1.inv, fun x => ?_⟩, resEta_inv h2⟩
  rw [MonoidHom.inv_apply, h1.2, inv_one]

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem theta_annih (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ J z f) :=
  GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf))

theorem om_annih (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    {sS sS' : Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT sT' : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : sS' * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS)
    (hT : sT' * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (annih (heisO ψ S T) θ τ (cplxO sS sT) z f) =
      annih (heisO ψ S T) θ τ (cplxO sS' sT') (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) := by
  unfold annih
  rw [map_add, map_smul, GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ _ hf, GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ _ hf,
    GlobalTheory.WeilVacMove.cplxO_move θ τ g h hS hT]

theorem om_foldr (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {sS sS' : RealMat S} {sT sT' : RealMat T}
    (hS : ∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ)
    (hT : ∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) :
    IsThetaFunO ψ S T (l.foldr (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 F) f) ∧
      om (g, h) (l.foldr (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 F) f) =
        (l.map fun p => (p.1, compAt θ p.1 (mt T h) * p.2 * compAt θ p.1 (mt S g⁻¹))).foldr
          (fun p F => annih (heisO ψ S T) θ p.1 (cplxO (sS' p.1) (sT' p.1)) p.2 F) (om (g, h) f) := by
  induction l with
  | nil => exact ⟨hf, rfl⟩
  | cons p l ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ← ih.2]
    exact ⟨theta_annih hθ hW.std p.1 _ p.2 ih.1, om_annih hW hθ g h p.1 (hS p.1) (hT p.1) p.2 ih.1⟩

end GlobalTheory.FockMove

namespace GlobalTheory.FockMove

theorem isFockVec_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (sS sS' : RealMat S) (sT : RealMat T) (g : GA D S), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → ∀ f, IsFockVec ψ θ S T sS sT f → IsFockVec ψ θ S T sS' sT (om (g, 1) f) := by
  intro D ψ S T χS χT om hW θ hθ sS sS' sT g hS f hf
  obtain ⟨hth, N, hN⟩ := hf
  have hT : ∀ τ, sT τ * compAt θ τ (mt T 1) = compAt θ τ (mt T 1) * sT τ := by
    intro τ
    rw [GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, Matrix.mul_one, Matrix.one_mul]
  refine ⟨hW.om_pres _ _ hth, N, fun l hl => ?_⟩
  let l₀ : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ) :=
    l.map fun p => (p.1, compAt θ p.1 (mt T (1 : GA D T)⁻¹) * p.2 * compAt θ p.1 (mt S g))
  have e : (l₀.map fun p => (p.1, compAt θ p.1 (mt T (1 : GA D T)) * p.2 * compAt θ p.1 (mt S g⁻¹))) = l := by
    simp only [l₀, List.map_map]
    conv_rhs => rw [← List.map_id l]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, id]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.mul_one]
  have key := (om_foldr hW hθ g 1 hS hT hth l₀).2
  rw [e] at key
  rw [← key, hN l₀ (by simp [l₀, hl]), map_zero]

end GlobalTheory.FockMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixClosedDerivLinearAddStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhatAdelicMatrix_closed_deriv_linear_add : ∀ (D : D7) (m n : ℕ) (φ : Mx D m n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → (∀ M : ℝ →+ Mx D m n, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ x, HasDerivAt (fun t : ℝ => φ (x + M t)) (φ' x) 0) ∧ (∀ ℓ : Mx D m n →+ ℂ, Continuous ℓ → (∀ u : Mx D m n, u.map (infPart D) = 0 → ℓ u = 0) → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat fun x => ℓ x * φ x) ∧ ∀ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat (φ + φ') := by
  first | exact @GlobalTheory.SchwartzDeriv.isSchwartzBruhat_closed | exact GlobalTheory.SchwartzDeriv.isSchwartzBruhat_closed | (intros; apply GlobalTheory.SchwartzDeriv.isSchwartzBruhat_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionSuperpositionOrthogonalSlicesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ A T fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ := by
  first | exact @GlobalTheory.SuperposS.superpos_isTheta | exact GlobalTheory.SuperposS.superpos_isTheta | (intros; apply GlobalTheory.SuperposS.superpos_isTheta <;> assumption)
end

