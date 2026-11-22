import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0024
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0021
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0020
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0006

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DetAdm
section
noncomputable section

namespace PI.VolStabS.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabS.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabS
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported

theorem detAdm_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M : ℕ} (ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (h1 : ∀ K, IsCompact K → ν1 K < ⊤) (h2 : ∀ K, IsCompact K → ν2 K < ⊤)
    (h : ∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) : ν1 = ν2 := by
  classical
  let ι := Fin a × Fin M × Fin (Module.finrank F E)
  let Ψ := psiH F E a M
  let Ψm := Ψ.toMeasurableEquiv
  have hfin : ∀ ν : Measure (Fin a → Fin M → AF F ⊗[F] E), (∀ K, IsCompact K → ν K < ⊤) →
      ∀ K, IsCompact K → ν.map Ψm K < ⊤ := by
    intro ν hν K hK
    rw [Ψm.map_apply]
    exact hν _ (Ψ.isCompact_preimage.2 hK)
  suffices hμ : ν1.map Ψm = ν2.map Ψm by
    rw [← Ψm.map_symm_map (μ := ν1), ← Ψm.map_symm_map (μ := ν2), hμ]
  set μ1 := ν1.map Ψm with hμ1
  set μ2 := ν2.map Ψm with hμ2

  have hbox : ∀ D, IsBoxD D → ∀ U : Set (ι → Ainf F), MeasurableSet U →
      μ1 (U ×ˢ boxS D) = μ2 (U ×ˢ boxS D) := by
    intro D hD
    let ρ := fun μ : Measure ((ι → Ainf F) × (ι → Af F)) =>
      (μ.restrict (univ ×ˢ boxS D)).map Prod.fst
    have hβ : MeasurableSet (boxS D) := (isCompact_boxS hD).isClosed.measurableSet
    have hρ : ∀ μ U, MeasurableSet U → ρ μ U = μ (U ×ˢ boxS D) := by
      intro μ U hU
      simp only [ρ]
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
      congr 1
      ext p
      simp
    have hint : ∀ μ (f : C_c(ι → Ainf F, ℝ)), ∫ x, f x ∂(ρ μ) =
        ∫ p, f p.1 * (boxS D).indicator (fun _ => (1 : ℝ)) p.2 ∂μ := by
      intro μ f
      simp only [ρ]
      rw [integral_map measurable_fst.aemeasurable (map_continuous f).aestronglyMeasurable,
        ← integral_indicator (MeasurableSet.univ.prod hβ)]
      congr 1
      funext p
      by_cases hp : p.2 ∈ boxS D
      · rw [Set.indicator_of_mem (mk_mem_prod (mem_univ p.1) hp : p ∈ univ ×ˢ boxS D),
          Set.indicator_of_mem hp, mul_one]
      · rw [Set.indicator_of_notMem (fun h' => hp h'.2), Set.indicator_of_notMem hp, mul_zero]
    have hfc : ∀ μ : Measure ((ι → Ainf F) × (ι → Af F)), (∀ K, IsCompact K → μ K < ⊤) →
        IsFiniteMeasureOnCompacts (ρ μ) := fun μ hμ =>
      ⟨fun K hK => by
        rw [hρ μ K hK.measurableSet]
        exact hμ _ (hK.prod (isCompact_boxS hD))⟩
    have := hfc μ1 (hfin ν1 h1)
    have := hfc μ2 (hfin ν2 h2)
    have hρeq : ρ μ1 = ρ μ2 := Measure.ext_of_integral_eq_on_compactlySupported fun f => by
      rw [hint, hint, hμ1, hμ2, integral_map_equiv, integral_map_equiv]
      exact key_int ν1 ν2 h hD f
    intro U hU
    rw [← hρ μ1 U hU, ← hρ μ2 U hU, hρeq]

  obtain ⟨bs, hbs, hbU⟩ := boxes_seq (F := F) (ι := ι)
  refine Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) {U : Set (ι → Ainf F) | MeasurableSet U} (boxes F ι))
    (fun n => compactCovering (ι → Ainf F) n.unpair.1 ×ˢ bs n.unpair.2) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← generateFrom_prod_eq isCountablySpanning_measurableSet ⟨bs, hbs, hbU⟩,
      generateFrom_boxes, MeasurableSpace.generateFrom_measurableSet]
  · rintro _ ⟨U, hU, β, hβ, rfl⟩ _ ⟨U', hU', β', hβ', rfl⟩ _
    rw [prod_inter_prod]
    have hU2 : MeasurableSet U := hU
    have hU2' : MeasurableSet U' := hU'
    exact mem_image2_of_mem (hU2.inter hU2') (boxes_inter hβ hβ')
  · refine eq_univ_of_forall fun p => mem_iUnion.2 ?_
    have h1' : p.1 ∈ ⋃ m, compactCovering (ι → Ainf F) m := by
      rw [iUnion_compactCovering]
      trivial
    have h2' : p.2 ∈ ⋃ n, bs n := by
      rw [hbU]
      trivial
    obtain ⟨m, hm⟩ := mem_iUnion.1 h1'
    obtain ⟨n, hn⟩ := mem_iUnion.1 h2'
    refine ⟨Nat.pair m n, ?_⟩
    simp only [Nat.unpair_pair]
    exact ⟨hm, hn⟩
  · intro n
    exact mem_image2_of_mem (show MeasurableSet (compactCovering (ι → Ainf F) n.unpair.1) from
      (isCompact_compactCovering _ _).measurableSet) (hbs _)
  · intro n
    obtain ⟨D, hD, e⟩ := hbs n.unpair.2
    rw [e]
    exact (hfin ν1 h1 _ ((isCompact_compactCovering _ _).prod (isCompact_boxS hD))).ne
  · rintro _ ⟨U, hU, β, ⟨D, hD, rfl⟩, rfl⟩
    exact hbox D hD U hU

end PI.VolStabS.DeterminantAdmissible

namespace PI.VolStabS

theorem detAdm_holds : DetAdm := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ν1 ν2 h1 h2 h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact DeterminantAdmissible.detAdm_gen ν1 ν2 h1 h2 h

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCntD
section
noncomputable section

namespace PI.VolStabS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨_, hE, _, hτ⟩ := hCM
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hτ, hτ, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    haveI := hE
    have hc := IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hc
    apply hc
    ext x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← hτ, hall]
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv]
  abel

theorem anti_coeff (σ : E →ₐ[F] E) {δ : E} (hδ0 : δ ≠ 0) (hσδ : σ δ = -δ) (s t : F)
    (h : σ (s • (1 : E) + t • δ) = s • 1 + t • δ) : t = 0 := by
  simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, hσδ, mul_one] at h
  have h2 : (2 : E) * (algebraMap F E t * δ) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact (algebraMap F E).injective (by rw [h4, map_zero])
    · exact absurd h4 hδ0

theorem exists_basis_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) :
    ∃ (δ : E) (D0 : F) (c : Module.Basis (Fin 2) F E), δ ≠ 0 ∧ σ δ = -δ ∧
      δ * δ = algebraMap F E D0 ∧ D0 ≠ 0 ∧ c 0 = 1 ∧ c 1 = δ := by
  obtain ⟨δ, hδ0, hσδ⟩ := exists_anti σ hCM
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      apply anti_coeff σ hδ0 hσδ s t
      rw [hst, map_zero]
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right one_ne_zero, rfl⟩
  let c := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hc : ⇑c = ![(1 : E), δ] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  obtain ⟨s, t, hst⟩ : ∃ s t : F, δ * δ = s • (1 : E) + t • δ := by
    have hsum := c.sum_repr (δ * δ)
    rw [Fin.sum_univ_two, hc] at hsum
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hsum
    exact ⟨_, _, hsum.symm⟩
  have ht : t = 0 := by
    apply anti_coeff σ hδ0 hσδ s t
    rw [← hst, map_mul, hσδ, neg_mul_neg]
  subst ht
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
  refine ⟨δ, s, c, hδ0, hσδ, hst, ?_, by simp [hc], by simp [hc]⟩
  rintro rfl
  rw [map_zero] at hst
  exact hδ0 (mul_self_eq_zero.mp hst)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensPos
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set
open scoped TensorProduct ENNReal

namespace LocPosW

theorem pos_of_lb {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure V} {ν : Measure X} {f : V → Y} {ι : X → Y} (hι : Function.Injective ι)
    {U : Set V} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν Set.univ fib)
    {f' : V → X} (hf' : Continuous f') (hff : ∀ v, f v = ι (f' v))
    {φ : V → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hφ0 : ∀ v, 0 ≤ φ v) {W : Set V} (hWU : W ⊆ U) {δ : ℝ} (hδ : 0 < δ)
    (hWφ : ∀ v ∈ W, δ ≤ φ v) {b0 : X} {c : ℝ≥0∞} (hc : 0 < c) (hc' : c ≠ ⊤) {N : Set X}
    (hN : N ∈ 𝓝 b0) (hlb : ∀ S ⊆ N, MeasurableSet S → c * ν S ≤ μ (f ⁻¹' (ι '' S) ∩ W))
    (hνpos : ∀ O : Set X, IsOpen O → O.Nonempty → ν O ≠ 0) (hνfin : ∃ N' ∈ 𝓝 b0, ν N' < ⊤) :
    0 < ∫ v, φ v ∂(fib b0) := by
  classical
  set g : X → ℝ := fun b => ∫ v, φ v ∂(fib b) with hg
  obtain ⟨hint, hcont⟩ := hfib.2.2 φ hφc hφs hφU
  have hgc : ContinuousAt g b0 := (hcont b0 (mem_univ _)).continuousAt univ_mem
  by_contra hneg
  push Not at hneg
  set η := δ * c.toReal with hηdef
  have hη : 0 < η := mul_pos hδ (ENNReal.toReal_pos hc.ne' hc')
  obtain ⟨N', hN', hN'fin⟩ := hνfin
  have hev : ∀ᶠ b in 𝓝 b0, g b < η := hgc.eventually (Iio_mem_nhds (lt_of_le_of_lt hneg hη))
  obtain ⟨O, hOsub, hOo, hbO⟩ := mem_nhds_iff.1 (inter_mem (inter_mem hN hN') hev)
  have hOm : MeasurableSet O := hOo.measurableSet
  have hOpos : ν O ≠ 0 := hνpos O hOo ⟨b0, hbO⟩
  have hOfin : ν O ≠ ⊤ := ne_top_of_le_ne_top hN'fin.ne (measure_mono fun b hb => (hOsub hb).1.2)
  have hfO : f ⁻¹' (ι '' O) = f' ⁻¹' O := by
    ext v
    simp only [mem_preimage, mem_image, hff, hι.eq_iff, exists_eq_right]
  let ψ : V → ℝ≥0∞ := (f ⁻¹' (ι '' O)).indicator (fun v => ENNReal.ofReal (φ v))
  have hψm : Measurable ψ := by
    refine Measurable.indicator (ENNReal.measurable_ofReal.comp hφc.measurable) ?_
    rw [hfO]
    exact hf'.measurable hOm
  have hdis := hfib.2.1 ψ hψm
  have hin : ∀ b, ∫⁻ v, ψ v ∂(fib b) = O.indicator (fun b => ENNReal.ofReal (g b)) b := by
    intro b
    have hnull := hfib.1 b
    by_cases hb : b ∈ O
    · rw [indicator_of_mem hb]
      have hae : ψ =ᵐ[fib b] fun v => ENNReal.ofReal (φ v) := by
        refine ae_iff.2 (measure_mono_null (fun v hv => ?_) hnull)
        intro hvin
        apply hv
        have h1 : f v = ι b := hvin.1
        have h2 : f' v = b := hι (by rw [← hff]; exact h1)
        have h3 : v ∈ f ⁻¹' (ι '' O) := by rw [hfO]; show f' v ∈ O; rw [h2]; exact hb
        exact indicator_of_mem h3 _
      rw [lintegral_congr_ae hae,
        ← ofReal_integral_eq_lintegral_ofReal (hint b (mem_univ b)) (ae_of_all _ hφ0)]
    · rw [indicator_of_notMem hb]
      have hae : ψ =ᵐ[fib b] 0 := by
        refine ae_iff.2 (measure_mono_null (fun v hv => ?_) hnull)
        intro hvin
        apply hv
        have h1 : f v = ι b := hvin.1
        have h2 : f' v = b := hι (by rw [← hff]; exact h1)
        have h3 : v ∉ f ⁻¹' (ι '' O) := by rw [hfO]; show f' v ∉ O; rw [h2]; exact hb
        exact indicator_of_notMem h3 _
      rw [lintegral_congr_ae hae]
      simp
  simp_rw [hin] at hdis
  rw [lintegral_indicator hOm] at hdis
  have hup : ∫⁻ b in O, ENNReal.ofReal (g b) ∂ν < ∫⁻ b in O, ENNReal.ofReal η ∂ν := by
    have hle : ∫⁻ b in O, ENNReal.ofReal (g b) ∂ν ≤ ∫⁻ b in O, ENNReal.ofReal η ∂ν :=
      setLIntegral_mono measurable_const fun b hb => ENNReal.ofReal_le_ofReal (hOsub hb).2.le
    refine setLIntegral_strict_mono hOm hOpos measurable_const ?_ (ae_of_all _ fun b hb => ?_)
    · refine ne_top_of_le_ne_top ?_ hle
      rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hOfin
    · exact (ENNReal.ofReal_lt_ofReal_iff hη).2 (hOsub hb).2
  rw [setLIntegral_const] at hup
  have hlow : ENNReal.ofReal η * ν O ≤ ∫⁻ v in U, ψ v ∂μ := by
    calc ENNReal.ofReal η * ν O = ENNReal.ofReal δ * (c * ν O) := by
          rw [hηdef, ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_toReal hc', mul_assoc]
      _ ≤ ENNReal.ofReal δ * μ (f ⁻¹' (ι '' O) ∩ W) :=
          mul_le_mul_right (hlb O (fun b hb => (hOsub hb).1.1) hOm) _
      _ = ∫⁻ v in f ⁻¹' (ι '' O) ∩ W, ENNReal.ofReal δ ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ v in f ⁻¹' (ι '' O) ∩ W, ψ v ∂μ :=
          setLIntegral_mono hψm fun v hv => by
            show ENNReal.ofReal δ ≤ (f ⁻¹' (ι '' O)).indicator (fun v => ENNReal.ofReal (φ v)) v
            rw [indicator_of_mem hv.1]
            exact ENNReal.ofReal_le_ofReal (hWφ v hv.2)
      _ ≤ ∫⁻ v in U, ψ v ∂μ := lintegral_mono_set (inter_subset_right.trans hWU)
  rw [hdis] at hlow
  exact lt_irrefl _ (hlow.trans_lt hup)

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X0 : Fin n → Fin M → E) :
    gramR R σ J (ratTup R X0) = (gramE σ J X0).map (inclR R) := by
  have hs : ∀ e : E, sigR R σ (inclR R e) = inclR R (σ e) := fun e => by
    simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  ext p q
  simp only [gramR, hR, gramE, hE, Formalism.UG.hform, Matrix.map_apply, ratTup, JR, map_sum, map_mul, hs]
  rfl

end LocPosW

open LocPosW

def LBInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ (μinf : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a)),
    μinf.IsAddHaarMeasure → νinf.IsAddHaarMeasure →
    ∀ W : Set (Fin a → Fin M → Ainf F ⊗[F] E), IsOpen W → ratTup (F := F) (Ainf F) X0 ∈ W →
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 (hermOf (Ainf F) σ (gramE σ J X0) hT),
      ∀ S ⊆ N, MeasurableSet S →
        c * νinf S ≤ μinf ((gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W)

theorem archPos_of_lb (hL : LBInf) : ArchPos := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ νinf hν fibInf hfib
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Ainf F) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (HermR (Ainf F) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set X1 := ratTup (F := F) (Ainf F) X0 with hX1
  have hX1U : X1 ∈ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    linIndep_of_isUnit_det (Ainf F) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset t7 hX1U
  obtain ⟨φ, hφ1, hφ0, hφc, hφr⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := X1)) isOpen_interior.isClosed_compl
    (disjoint_singleton_left.2 fun h => h hxK)
  have hsupp : Function.support φ ⊆ interior K := fun X hX => by
    by_contra h
    exact hX (hφ0 h)
  have hts : tsupport φ ⊆ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    (closure_mono hsupp).trans ((closure_minimal interior_subset hK.isClosed).trans hKU)
  let W : Set (Fin a → Fin M → Ainf F ⊗[F] E) := {X | (1 / 2 : ℝ) < φ X}
  have hWo : IsOpen W := isOpen_lt continuous_const φ.continuous
  have hX1W : X1 ∈ W := by
    show (1 / 2 : ℝ) < φ X1
    rw [hφ1 (mem_singleton X1)]
    norm_num
  have hWU : W ⊆ {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    fun X hX => hts (subset_tsupport _ (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hX).ne')
  obtain ⟨c, hc0, hctop, N, hN, hlb⟩ :=
    hL F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μinf νinf hμ.1 hν.1 W hWo hX1W
  have hpos := pos_of_lb (f' := gramH (Ainf F) σ hσ J hJ.1) Subtype.val_injective hfib
    (continuous_gramH (Ainf F) σ hσ J hJ.1) (fun _ => rfl) φ.continuous hφc hts
    (fun X => (hφr X).1) hWU (by norm_num : (0 : ℝ) < 1 / 2) (fun X hX => hX.le) hc0 hctop hN hlb
    (fun O hO hne => (hO.measure_pos νinf hne).ne') (νinf.finiteAt_nhds _)
  refine ⟨fun X => ((φ X : ℝ) : ℂ), Complex.continuous_ofReal.comp φ.continuous,
    hφc.comp_left Complex.ofReal_zero, ?_⟩
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMuInv
section
noncomputable section

namespace PI.VolStabS.TopoMuInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem smul_apply (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (x : Fin n) :
    (h • X) x = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ X x :=
  rfl

theorem BR_smul (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) (h • Y) = BR R σ J X Y := by
  have hg' : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR R J *
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) = JR R J := h.2
  simp only [BR, smul_apply, hR, TopoGram.hform_mulVec, hg']

theorem BR_smul_left (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) Y = BR R σ J X (h⁻¹ • Y) := by
  conv_lhs => rw [← smul_inv_smul h Y]
  exact BR_smul R σ J h X (h⁻¹ • Y)

theorem smul_neg' (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    h • (-X) = -(h • X) := by
  funext x
  simp only [smul_apply, Pi.neg_apply, mulVec_neg]

def smulAddEquiv (h : HA R σ J) (n : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃+ (Fin n → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  map_add' X Y := by
    funext x
    change ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (X x + Y x) = _
    rw [mulVec_add]
    rfl

theorem selfDual_map (ψR : R → ℂ) {n : ℕ} (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : SdW F E σ M J R ψR n μ) (h : HA R σ J) :
    SdW F E σ M J R ψR n (μ.map (fun X => h • X)) := by
  let e := PI.VolStabS.smulHomeo R σ (a := n) J h
  let em := e.toMeasurableEquiv
  have hmap : μ.map (fun X => h • X) = μ.map em := rfl
  have : μ.IsAddHaarMeasure := hμ.1
  refine ⟨?_, fun Φ hc hcs hI z => ?_⟩
  · exact (smulAddEquiv R σ J h n).isAddHaarMeasure_map μ e.continuous e.symm.continuous
  rw [hmap] at hI ⊢
  let Fh : (Fin n → Fin M → R ⊗[F] E) → ℂ := fun w =>
    ∫ x, Φ (h • x) * ψR (BR R σ J x w) ∂μ
  have hin : ∀ y, ∫ x, Φ x * ψR (BR R σ J x y) ∂(μ.map em) = Fh (h⁻¹ • y) := fun y => by
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Φ (h • x) * ψR (BR R σ J (h • x) y) = Φ (h • x) * ψR (BR R σ J x (h⁻¹ • y))
    rw [BR_smul_left]
  have hI' : Integrable Fh μ := by
    rw [integrable_map_equiv] at hI
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    show ∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em) = Fh y
    rw [hin, inv_smul_smul]
  have key := hμ.2 (fun x => Φ (h • x)) (hc.comp e.continuous) (hcs.comp_homeomorph e) hI'
    (h⁻¹ • z)
  rw [integral_map_equiv]
  have e3 : (fun y => (∫ x, Φ x * ψR (BR R σ J x (em y)) ∂(μ.map em)) *
      ψR (BR R σ J (em y) z)) = fun y => Fh y * ψR (BR R σ J y (h⁻¹ • z)) := by
    funext y
    show (∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em)) * ψR (BR R σ J (h • y) z) = _
    rw [hin, inv_smul_smul, BR_smul_left]
  rw [e3]
  refine key.trans ?_
  show Φ (h • -(h⁻¹ • z)) = Φ (-z)
  rw [smul_neg', smul_inv_smul]

end PI.VolStabS.TopoMuInv

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem muInvInf_of (hU : SdUniq) : MuInvInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact (hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).1 _ _
    (TopoMuInv.selfDual_map (Ainf F) σ J (psiInf F ψ) μinf hμ h) hμ

theorem muInvV_of (hU : SdUniq) : MuInvV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact ((hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).2.2 v).1 _ _
    (TopoMuInv.selfDual_map (Fv F v) σ J (psiV F ψ v) μv hμ h) hμ

theorem nuInv_of_pin (hD : DetAdm) (hC : CompG) (hP : FibPin) (hU : SdUniq) : NuInv :=
  nuInv_of_steps hD hC hP (muInvInf_of hU) (muInvV_of hU)

end PI.VolStabS
end
end

