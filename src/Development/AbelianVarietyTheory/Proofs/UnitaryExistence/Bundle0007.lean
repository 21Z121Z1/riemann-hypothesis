import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0004
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InvariantProbabilityLatticeQuotientUnique
section
noncomputable section
open MeasureTheory
open scoped Pointwise Topology ENNReal
namespace GlobalTheory.LatticeQuotUniq
open GlobalTheory.AutQuotCheck

section Alg
variable {G : Type} [Group G] [MeasurableSpace G] (Γ : Subgroup G)

def fibreMeasure (q : Quotient (QuotientGroup.rightRel Γ)) : Measure G :=
  Quotient.lift (fun g : G => Measure.sum fun γ : Γ => Measure.dirac ((γ : G) * g)) (by
    intro a b hab
    obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ a b).1 (Quotient.sound hab)
    have := Measure.sum_comp_equiv (Equiv.mulRight (⟨δ, hδ⟩ : Γ))
      (fun γ : Γ => Measure.dirac ((γ : G) * a))
    rw [← this]
    congr 1
    ext1 γ
    simp [mul_assoc]) q

theorem fibreMeasure_apply (g : G) {A : Set G} (hA : MeasurableSet A) :
    fibreMeasure Γ (cls Γ g) A = ∑' γ : Γ, A.indicator (1 : G → ℝ≥0∞) ((γ : G) * g) := by
  show (Measure.sum fun γ : Γ => Measure.dirac ((γ : G) * g)) A = _
  rw [Measure.sum_apply _ hA]
  simp only [Measure.dirac_apply' _ hA]

theorem measurable_fibreMeasure [MeasurableMul G] [Countable Γ] : Measurable (fibreMeasure Γ) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  refine measurable_from_quotient.2 ?_
  have : ((fun q => fibreMeasure Γ q A) ∘ Quotient.mk'') =
      fun g : G => ∑' γ : Γ, A.indicator (1 : G → ℝ≥0∞) ((γ : G) * g) := by
    ext g; exact fibreMeasure_apply Γ g hA
  rw [this]
  exact Measurable.ennreal_tsum fun γ =>
    (measurable_one.indicator hA).comp (measurable_const_mul _)

theorem fibreMeasure_of_injOn {A : Set G} (hA : MeasurableSet A)
    (h : ∀ γ : Γ, ∀ x ∈ A, (γ : G) * x ∈ A → γ = 1) (q : Quotient (QuotientGroup.rightRel Γ)) :
    fibreMeasure Γ q A = (cls Γ '' A).indicator 1 q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [show fibreMeasure Γ (Quotient.mk _ g) A = _ from fibreMeasure_apply Γ g hA]
    by_cases hg : (Quotient.mk _ g) ∈ cls Γ '' A
    · rw [Set.indicator_of_mem hg]
      obtain ⟨a, ha, hag⟩ := hg
      obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ g a).1 hag.symm
      rw [tsum_eq_single (⟨δ, hδ⟩ : Γ)]
      · simp [Set.indicator_of_mem ha]
      · intro γ hγ
        refine Set.indicator_of_notMem (fun hm => hγ ?_) _
        have := h (γ * (⟨δ, hδ⟩ : Γ)⁻¹) _ ha (by simpa [mul_assoc] using hm)
        exact mul_inv_eq_one.1 this
    · rw [Set.indicator_of_notMem hg]
      refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem (fun hm => hg ?_) _
      exact ⟨_, hm, cls_smul Γ γ g⟩

theorem indicator_le_fibreMeasure {s : Set (Quotient (QuotientGroup.rightRel Γ))} (hs : MeasurableSet s)
    (q : Quotient (QuotientGroup.rightRel Γ)) :
    s.indicator 1 q ≤ fibreMeasure Γ q (cls Γ ⁻¹' s) := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [show fibreMeasure Γ (Quotient.mk _ g) _ = _ from fibreMeasure_apply Γ g (measurable_cls Γ hs)]
    refine le_trans ?_ (ENNReal.le_tsum (1 : Γ))
    by_cases hg : (Quotient.mk _ g) ∈ s
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (by simpa using hg)]; simp
    · rw [Set.indicator_of_notMem hg]; exact zero_le

theorem preimage_image_cls (A : Set G) :
    cls Γ ⁻¹' (cls Γ '' A) = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' A := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ x a).1 h.symm
    exact ⟨⟨δ, hδ⟩, ha⟩
  · rintro ⟨γ, h⟩
    exact ⟨_, h, cls_smul Γ γ x⟩

theorem measurableSet_image_cls [MeasurableMul G] [Countable Γ] {A : Set G} (hA : MeasurableSet A) :
    MeasurableSet (cls Γ '' A) := by
  show MeasurableSet (cls Γ ⁻¹' (cls Γ '' A))
  rw [preimage_image_cls]
  exact MeasurableSet.iUnion fun γ => measurable_const_mul _ hA

theorem exists_strict_domain [MeasurableMul G] [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {F : Set G} (hF : IsFundamentalDomain Γ F μ) :
    ∃ E : Set G, MeasurableSet E ∧ E =ᵐ[μ] F ∧ (∀ γ : Γ, ∀ x ∈ E, (γ : G) * x ∈ E → γ = 1) ∧
      μ (cls Γ ⁻¹' (cls Γ '' E)ᶜ) = 0 := by
  obtain ⟨E, hsub, hE, hae⟩ := hF.fundamentalInterior.nullMeasurableSet.exists_measurable_subset_ae_eq
  have h2 : fundamentalInterior Γ F =ᵐ[μ] F := by
    rw [← sdiff_fundamentalFrontier]
    exact diff_ae_eq_self.2 (measure_mono_null Set.inter_subset_right hF.measure_fundamentalFrontier)
  have h3 := hae.trans h2
  refine ⟨E, hE, h3, ?_, ?_⟩
  · intro γ x hx hγ
    by_contra hne
    have := (mem_fundamentalInterior.1 (hsub hγ)).2 γ hne
    exact this ⟨x, fundamentalInterior_subset (hsub hx), rfl⟩
  · rw [Set.preimage_compl, preimage_image_cls]
    have h4 : ∀ᵐ x ∂μ, ∀ γ : Γ, ((γ : G) * x ∈ F → (γ : G) * x ∈ E) := by
      refine ae_all_iff.2 fun γ => ?_
      exact (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h3.symm.le
    have h5 : ∀ᵐ x ∂μ, x ∈ ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' E := by
      filter_upwards [h4, hF.ae_covers] with x hx ⟨γ, hγ⟩
      exact Set.mem_iUnion.2 ⟨γ, hx γ hγ⟩
    exact h5

end Alg

theorem invariant_prob_eq : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ ⊤ → ∀ (ν : Measure (Quotient (QuotientGroup.rightRel Γ))) [IsProbabilityMeasure ν], (∀ (h : G) (ρ : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ)), (∀ g : G, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s) → ν = (μ 𝓕)⁻¹ • (μ.restrict 𝓕).map (fun g : G => (Quotient.mk _ g : Quotient (QuotientGroup.rightRel Γ))) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ F hF hfin ν _ hinv
  have h0 : μ F ≠ 0 := hF.measure_ne_zero (NeZero.ne μ)
  haveI : μ.IsMulRightInvariant := ⟨rightInvariant_of_covolume Γ μ hF h0 hfin⟩
  obtain ⟨E, hE, hEF, hEs, hEn⟩ := exists_strict_domain Γ μ hF
  have hκ := measurable_fibreMeasure Γ
  set L : Measure G := ν.bind (fibreMeasure Γ) with hL
  have hLa : ∀ A, MeasurableSet A → L A = ∫⁻ q, fibreMeasure Γ q A ∂ν :=
    fun A hA => Measure.bind_apply hA hκ.aemeasurable
  have hLi : ∀ A, MeasurableSet A → (∀ γ : Γ, ∀ x ∈ A, (γ : G) * x ∈ A → γ = 1) →
      L A = ν (cls Γ '' A) := by
    intro A hA h
    rw [hLa A hA]
    simp_rw [fibreMeasure_of_injOn Γ hA h]
    exact lintegral_indicator_one (measurableSet_image_cls Γ hA)
  haveI : L.IsMulRightInvariant := by
    refine ⟨fun h => ?_⟩
    let ρ : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ) :=
      Quotient.lift (fun g => cls Γ (g * h)) (by
        intro a b hab
        obtain ⟨δ, hδ, rfl⟩ := (cls_eq_iff Γ a b).1 (Quotient.sound hab)
        exact (cls_eq_iff Γ _ _).2 ⟨δ, hδ, mul_assoc _ _ _⟩)
    have hρ : Measurable ρ :=
      measurable_from_quotient.2 ((measurable_cls Γ).comp (measurable_mul_const h))
    have hmp : MeasurePreserving ρ ν ν := ⟨hρ, by
      ext s hs
      rw [Measure.map_apply hρ hs]
      exact hinv h ρ (fun _ => rfl) s hs⟩
    ext A hA
    rw [Measure.map_apply (measurable_mul_const h) hA, hLa _ (measurable_mul_const h hA), hLa _ hA,
      ← hmp.lintegral_comp (f := fun q => fibreMeasure Γ q A) ((Measure.measurable_coe hA).comp hκ)]
    refine lintegral_congr fun q => ?_
    induction q using Quotient.inductionOn with
    | h g =>
      refine (fibreMeasure_apply Γ g (measurable_mul_const h hA)).trans
        (Eq.trans ?_ (fibreMeasure_apply Γ (g * h) hA).symm)
      refine tsum_congr fun γ => ?_
      rw [← mul_assoc]
      rfl
  haveI : IsLocallyFiniteMeasure L := by
    have hpos : 0 < μ E := by rw [measure_congr hEF]; exact pos_iff_ne_zero.2 h0
    have hn := Measure.div_mem_nhds_one_of_haar_pos μ E hE hpos
    refine ⟨fun g => ?_⟩
    have hc : ContinuousAt (fun p : G × G => p.1 / p.2) (g, g) := continuous_div'.continuousAt
    have h1 : (fun p : G × G => p.1 / p.2) ⁻¹' (E / E) ∈ 𝓝 (g, g) := hc (by simpa using hn)
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 h1
    obtain ⟨W, hW, hWo, hgW⟩ := mem_nhds_iff.1 (Filter.inter_mem hU hV)
    refine ⟨W, hWo.mem_nhds hgW, ?_⟩
    rw [hLi W hWo.measurableSet]
    · exact measure_lt_top _ _
    · intro γ x hx hγ
      have : ((γ : G) * x) / x ∈ E / E := hUV (Set.mk_mem_prod (hW hγ).1 (hW hx).2)
      obtain ⟨a, ha, b, hb, hab⟩ := this
      refine hEs γ b hb ?_
      have : a = (γ : G) * b := by
        simp only [mul_div_cancel_right] at hab
        rw [← hab]; simp
      rwa [← this]
  haveI : μ.inv.IsHaarMeasure := {}
  have e := Measure.isMulLeftInvariant_eq_smul L.inv μ.inv
  set c := Measure.haarScalarFactor L.inv μ.inv
  have e2 : L = (c : ℝ≥0∞) • μ := by
    have := congrArg Measure.inv e
    rw [Measure.inv_inv] at this
    rw [this]
    show Measure.map _ _ = _
    rw [Measure.map_smul]
    exact congrArg (c • ·) (Measure.inv_inv μ)
  have hT := measurableSet_image_cls Γ hE
  have hnull : ν (cls Γ '' E)ᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc ν (cls Γ '' E)ᶜ = ∫⁻ q, (cls Γ '' E)ᶜ.indicator 1 q ∂ν := (lintegral_indicator_one hT.compl).symm
      _ ≤ _ := lintegral_mono fun q => indicator_le_fibreMeasure Γ hT.compl q
      _ = L _ := (hLa _ (measurable_cls Γ hT.compl)).symm
      _ = 0 := by rw [e2, Measure.smul_apply, hEn, smul_zero]
  have key : ν = (c : ℝ≥0∞) • (μ.restrict F).map (cls Γ) := by
    ext s hs
    rw [Measure.smul_apply, Measure.map_apply (measurable_cls Γ) hs, ← Measure.restrict_congr_set hEF,
      Measure.restrict_apply (measurable_cls Γ hs), ← Measure.smul_apply, ← e2,
      hLi _ ((measurable_cls Γ hs).inter hE) (fun γ x hx hγ => hEs γ x hx.2 hγ.2),
      Set.image_preimage_inter]
    exact (measure_inter_conull hnull).symm
  have h1 : (c : ℝ≥0∞) * μ F = 1 := by
    have := congrArg (fun m => m Set.univ) key
    simp only [measure_univ, Measure.smul_apply, smul_eq_mul] at this
    rw [Measure.map_apply (measurable_cls Γ) MeasurableSet.univ] at this
    simpa using this.symm
  rw [← ENNReal.eq_inv_of_mul_eq_one_left h1]
  exact key

end GlobalTheory.LatticeQuotUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LintegralUnfoldArithmeticQuotientDoubleCosets
section
open MeasureTheory Topology Matrix
open scoped ENNReal

namespace GlobalTheory.PeterssonUnfold

theorem unfold_lintegral :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ H Kf : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 ≠ 0 → μ 𝓕 ≠ ⊤ → MeasurableSet (H : Set G) → Kf ≤ H → ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ k, Group (R k)] [∀ k, TopologicalSpace (R k)] [∀ k, IsTopologicalGroup (R k)] [∀ k, T2Space (R k)] [∀ k, LocallyCompactSpace (R k)] [∀ k, SecondCountableTopology (R k)] [∀ k, MeasurableSpace (R k)] [∀ k, BorelSpace (R k)] (ν : ∀ k, Measure (R k)) [∀ k, (ν k).IsHaarMeasure] (ψ : ∀ k, G →* R k) (Λ : ∀ k, Subgroup (R k)) (s : ∀ k, R k) (g : ι → G) (P : Type) (Q : P → P → Prop) (dict : G → P) (pt : ∀ k, R k → P), (∀ k, Measurable (ψ k)) → (∀ k t, ∃ h ∈ H, ψ k h = t) → (∀ k, ∀ z ∈ Kf, ψ k z = 1) → (∀ k, ∀ γ ∈ Γ, ψ k γ = 1 → γ = 1) → (∀ k k', ∃ (e : R k ≃ᵐ R k') (α : R k → R k) (u : R k), MeasurePreserving e (ν k) (ν k') ∧ Measurable α ∧ (∀ x, ψ k' x = e (α (ψ k x))) ∧ ∀ t, α (α t) = u⁻¹ * t * u) → (∀ k, ∃ W ∈ 𝓝 (1 : R k), ∀ w ∈ Λ k, w ∈ W → w = 1) → Equivalence Q → (∀ x x', Q (dict x) (dict x') ↔ ∃ γ ∈ Γ, ∃ z ∈ Kf, x' = γ * x * z) → (∀ k, ∀ h ∈ H, Q (dict (g k * h)) (pt k (s k * ψ k h))) → (∀ x, ∃ k t, Q (dict x) (pt k t)) → (∀ k k' t t', Q (pt k t) (pt k' t') → k = k') → (∀ k t t', Q (pt k t) (pt k t') ↔ ∃ w ∈ Λ k, t' = w * t) → ∃ (κ : ℝ≥0∞) (D : ∀ k, Set (R k)), κ ≠ 0 ∧ κ ≠ ⊤ ∧ (∀ k, Countable (Λ k) ∧ IsFundamentalDomain (Λ k) (D k) (ν k)) ∧ ∀ Φ : P → ℝ≥0∞, (∀ x q, Q (dict x) q → Φ q = Φ (dict x)) → (∀ k, Measurable fun t => Φ (pt k t)) → Measurable (fun x => Φ (dict x)) ∧ ∫⁻ x in 𝓕, Φ (dict x) ∂μ = κ * ∑ k, ∫⁻ t in D k, Φ (pt k t) ∂(ν k) := by
  classical
  intro G _ _ _ μ _ _ Γ H Kf _ 𝓕 h𝓕 h0 htop hH hKH ι _ R _ _ _ _ _ _ _ _ ν _ ψ Λ s g P Q dict pt
    hψ hsurj hK hΓ hcomp hdisc hQ hdict hpt hcov hsep hΛ
  have hD := fun k => GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete (R k) (Λ k) (hdisc k)
  have hcount : ∀ k, Countable (Λ k) := fun k => (hD k).1
  choose D hDm hDu using fun k => (hD k).2
  have hpt' : ∀ k y, (g k)⁻¹ * y ∈ H → Q (dict y) (pt k (s k * ψ k ((g k)⁻¹ * y))) := by
    intro k y hy
    have := hpt k _ hy
    rwa [mul_inv_cancel_left] at this
  have hΓQ : ∀ δ ∈ Γ, ∀ y, Q (dict y) (dict (δ * y)) := fun δ hδ y =>
    (hdict _ _).2 ⟨δ, hδ, 1, Kf.one_mem, by rw [mul_one]⟩
  have inj1 : ∀ k k' y, ∀ δ ∈ Γ, (g k)⁻¹ * y ∈ H → (g k')⁻¹ * (δ * y) ∈ H →
      Q (pt k (s k * ψ k ((g k)⁻¹ * y))) (pt k' (s k' * ψ k' ((g k')⁻¹ * (δ * y)))) :=
    fun k k' y δ hδ hy hy' =>
      hQ.trans (hQ.symm (hpt' k y hy)) (hQ.trans (hΓQ δ hδ y) (hpt' k' _ hy'))
  have inj2 : ∀ k y, ∀ δ ∈ Γ, (g k)⁻¹ * y ∈ H → (g k)⁻¹ * (δ * y) ∈ H →
      ∃ w ∈ Λ k, s k * ψ k ((g k)⁻¹ * (δ * y)) = w * (s k * ψ k ((g k)⁻¹ * y)) ∧
        (w = 1 → δ = 1) := by
    intro k y δ hδ hy hy'
    obtain ⟨w, hw, he⟩ := (hΛ k _ _).1 (inj1 k k y δ hδ hy hy')
    refine ⟨w, hw, he, fun h1 => hΓ k δ hδ ?_⟩
    rw [h1, one_mul, mul_right_inj, map_mul, map_mul, map_mul, mul_right_inj] at he
    exact mul_eq_right.1 he
  let E : ι → Set G := fun k => {y | (g k)⁻¹ * y ∈ H ∧ s k * ψ k ((g k)⁻¹ * y) ∈ D k}
  have hms : ∀ k, Measurable fun y : G => s k * ψ k ((g k)⁻¹ * y) := fun k =>
    ((hψ k).comp (measurable_const_mul _)).const_mul _
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (measurable_const_mul (g k)⁻¹ hH).inter (hms k (hDm k))
  have cover : ∀ x, ∃ γ ∈ Γ, ∃ k, γ * x ∈ E k := by
    intro x
    obtain ⟨k, t, hq⟩ := hcov x
    obtain ⟨w, hw, -⟩ := hDu k t
    obtain ⟨h, hh, he⟩ := hsurj k ((s k)⁻¹ * (w * t))
    have h1 : Q (pt k t) (pt k (s k * ψ k h)) :=
      (hΛ k _ _).2 ⟨w, w.2, by rw [he, mul_inv_cancel_left]⟩
    obtain ⟨γ, hγ, z, hz, hx⟩ := (hdict x (g k * h)).1
      (hQ.trans hq (hQ.trans h1 (hQ.symm (hpt k h hh))))
    have h2 : (g k)⁻¹ * (γ * x) = h * z⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_inv_cancel_right]
    refine ⟨γ, hγ, k, ?_, ?_⟩
    · rw [h2]; exact H.mul_mem hh (H.inv_mem (hKH hz))
    · rw [h2, map_mul, map_inv, hK k z hz, inv_one, mul_one, he, mul_inv_cancel_left]
      exact hw
  have uniq : ∀ k k' y, ∀ δ ∈ Γ, y ∈ E k → δ * y ∈ E k' → k = k' ∧ δ = 1 := by
    intro k k' y δ hδ hy hy'
    obtain rfl : k = k' := hsep _ _ _ _ (inj1 k k' y δ hδ hy.1 hy'.1)
    refine ⟨rfl, ?_⟩
    obtain ⟨w, hw, he, h1⟩ := inj2 k y δ hδ hy.1 hy'.1
    refine h1 ?_
    have := (hDu k (s k * ψ k ((g k)⁻¹ * y))).unique (y₁ := ⟨w, hw⟩) (y₂ := 1)
      (by have := hy'.2; rwa [he] at this) (by simpa using hy.2)
    exact congrArg Subtype.val this
  have hE : IsFundamentalDomain Γ (⋃ k, E k) μ := by
    refine IsFundamentalDomain.mk' (MeasurableSet.iUnion hEm).nullMeasurableSet fun x => ?_
    obtain ⟨γ, hγ, k, hx⟩ := cover x
    refine ⟨⟨γ, hγ⟩, Set.mem_iUnion.2 ⟨k, hx⟩, fun γ' hγ' => ?_⟩
    obtain ⟨k', hx'⟩ := Set.mem_iUnion.1 hγ'
    have := (uniq k k' (γ * x) (γ' * γ⁻¹) (Γ.mul_mem γ'.2 (Γ.inv_mem hγ)) hx
      (by rw [mul_assoc, inv_mul_cancel_left]; exact hx')).2
    exact Subtype.ext (mul_inv_eq_one.1 this)
  have hH0 : μ H ≠ 0 := by
    intro hH0
    apply h0
    rw [h𝓕.measure_eq hE]
    refine measure_iUnion_null fun k => measure_mono_null (t := (fun y => (g k)⁻¹ * y) ⁻¹' H)
      (fun y hy => hy.1) ?_
    rw [measure_preimage_mul, hH0]
  have hloc : ∀ k t, ∃ W ∈ 𝓝 t, μ ((H : Set G) ∩ ψ k ⁻¹' W) ≠ ⊤ := by
    intro k t
    obtain ⟨U, hU, hΛU⟩ := hdisc k
    obtain ⟨V₀, hV₀, hVU⟩ := exists_nhds_split_inv hU
    obtain ⟨V, hVV, hVo, hV1⟩ := mem_nhds_iff.1 hV₀
    have ho : IsOpen {u : R k | s k * u * (s k * t)⁻¹ ∈ V} := hVo.preimage (by fun_prop)
    refine ⟨_, ho.mem_nhds (by simpa using hV1), fun hinf => ?_⟩
    rw [← measure_preimage_mul μ (g k)⁻¹] at hinf
    obtain ⟨x, hx, y, hy, δ, hδ, hxy⟩ := h𝓕.exists_ne_one_smul_eq
      (measurable_const_mul (g k)⁻¹ (hH.inter (hψ k ho.measurableSet))).nullMeasurableSet
      (by rw [hinf]; exact lt_top_iff_ne_top.2 htop)
    subst hxy
    obtain ⟨w, hw, he, h1⟩ := inj2 k x δ δ.2 hx.1 hy.1
    refine hδ (Subtype.ext (h1 (hΛU w hw ?_)))
    have h2 : s k * ψ k ((g k)⁻¹ * (δ * x)) * (s k * t)⁻¹ ∈ V := hy.2
    have h3 : s k * ψ k ((g k)⁻¹ * x) * (s k * t)⁻¹ ∈ V := hx.2
    rw [he, mul_assoc] at h2
    have := hVU _ (hVV h2) _ (hVV h3)
    rwa [mul_div_cancel_right] at this
  obtain ⟨κ, hκ0, hκt, hκ⟩ := GlobalTheory.map_restrict_subgroup_eq_common_smul_haar G μ H hH hH0 ι R ν ψ hψ hsurj hloc hcomp
  refine ⟨κ, D, hκ0, hκt, fun k => ⟨hcount k,
    IsFundamentalDomain.mk' (hDm k).nullMeasurableSet (hDu k)⟩, fun Φ hΦ hΦm => ?_⟩
  have hinv : ∀ δ ∈ Γ, ∀ y, Φ (dict (δ * y)) = Φ (dict y) := fun δ hδ y => hΦ _ _ (hΓQ δ hδ y)
  have hval : ∀ k y, (g k)⁻¹ * y ∈ H → Φ (dict y) = Φ (pt k (s k * ψ k ((g k)⁻¹ * y))) :=
    fun k y hy => (hΦ _ _ (hpt' k y hy)).symm
  refine ⟨fun B hB => ?_, ?_⟩
  · have : (fun x => Φ (dict x)) ⁻¹' B = ⋃ γ : Γ, ⋃ k, (fun x => (γ : G) * x) ⁻¹'
        (((fun y => (g k)⁻¹ * y) ⁻¹' H) ∩
          (fun y => Φ (pt k (s k * ψ k ((g k)⁻¹ * y)))) ⁻¹' B) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hx
        obtain ⟨γ, hγ, k, hk⟩ := cover x
        refine ⟨⟨γ, hγ⟩, k, hk.1, ?_⟩
        rw [← hval k _ hk.1, hinv γ hγ]; exact hx
      · rintro ⟨γ, k, hk, hx⟩
        rwa [← hval k _ hk, hinv γ γ.2] at hx
    rw [this]
    exact MeasurableSet.iUnion fun γ => MeasurableSet.iUnion fun k => measurable_const_mul _
      ((measurable_const_mul _ hH).inter (((hΦm k).comp (hms k)) hB))
  · rw [h𝓕.setLIntegral_eq hE _ fun γ x => hinv γ γ.2 x,
      lintegral_iUnion hEm (fun k k' hk => Set.disjoint_left.2 fun y hy hy' =>
        hk (uniq k k' y 1 Γ.one_mem hy (by rwa [one_mul])).1), tsum_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    let F : R k → ℝ≥0∞ := (D k).indicator fun t => Φ (pt k t)
    have hF : Measurable F := (hΦm k).indicator (hDm k)
    calc ∫⁻ x in E k, Φ (dict x) ∂μ
        = ∫⁻ x, (H : Set G).indicator (fun h => F (s k * ψ k h)) ((g k)⁻¹ * x) ∂μ := by
          rw [← lintegral_indicator (hEm k)]
          refine lintegral_congr fun x => ?_
          by_cases hx : (g k)⁻¹ * x ∈ H
          · rw [Set.indicator_of_mem (s := (H : Set G)) hx]
            by_cases hx' : s k * ψ k ((g k)⁻¹ * x) ∈ D k
            · rw [Set.indicator_of_mem (show x ∈ E k from ⟨hx, hx'⟩), hval k x hx]
              exact (Set.indicator_of_mem hx' fun t => Φ (pt k t)).symm
            · rw [Set.indicator_of_notMem (fun h : x ∈ E k => hx' h.2)]
              exact (Set.indicator_of_notMem hx' fun t => Φ (pt k t)).symm
          · rw [Set.indicator_of_notMem (fun h : x ∈ E k => hx h.1),
              Set.indicator_of_notMem (s := (H : Set G)) hx]
      _ = ∫⁻ h in (H : Set G), F (s k * ψ k h) ∂μ := by
          rw [lintegral_mul_left_eq_self
            ((H : Set G).indicator (fun h => F (s k * ψ k h))) (g k)⁻¹, lintegral_indicator hH]
      _ = ∫⁻ t, F (s k * t) ∂((μ.restrict H).map (ψ k)) :=
          (lintegral_map (f := fun t => F (s k * t)) (hF.comp (measurable_const_mul _)) (hψ k)).symm
      _ = κ * ∫⁻ t in D k, Φ (pt k t) ∂(ν k) := by
          rw [hκ, lintegral_smul_measure, lintegral_mul_left_eq_self F, lintegral_indicator (hDm k),
            smul_eq_mul]

end GlobalTheory.PeterssonUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemAdelicCompletionPseudoBasisIff
section
noncomputable section

namespace GlobalTheory.AdLat

open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

section
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def adCoord (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n) : (Fin n → RA F E) →+ RA F E where
  toFun w := ∑ i, w i * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b)
  map_zero' := by simp
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]

theorem sum_mul_repr_single (e : Module.Basis (Fin n) E (Fin n → E)) (x : Fin n → E) (b : Fin n) :
    ∑ i, x i * e.repr (Pi.single i 1) b = e.repr x b := by
  conv_rhs => rw [pi_eq_sum_univ' x]
  simp [map_sum]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.adCoord_tmul (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n)
    (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    _root_.GlobalTheory.AdLat.adCoord F e b (fun i => a ⊗ₜ x i) = a ⊗ₜ e.repr x b := by
  have hx : e.repr x b = ∑ i, x i * e.repr (Pi.single i 1) b := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Pi.single i (x i) = x i • (Pi.single i 1 : Fin n → E) by
        ext j; by_cases h : j = i <;> simp [Pi.single_apply, h],
      map_smul, Finsupp.smul_apply, smul_eq_mul]
  change ∑ i, (a ⊗ₜ x i) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hx, TensorProduct.tmul_sum]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.adCoord_smul (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n)
    (r : _root_.GlobalTheory.AdLat.RA F E) (w : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.adCoord F e b (r • w) = r * _root_.GlobalTheory.AdLat.adCoord F e b w := by
  change ∑ i, (r • w) i * _ = r * ∑ i, w i * _
  simp [Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.AdLat.adCoord_sum (e : Module.Basis (Fin n) E (Fin n → E))
    (z : Fin n → _root_.GlobalTheory.AdLat.RA F E) (b : Fin n) :
    _root_.GlobalTheory.AdLat.adCoord F e b (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) = z b := by
  have h1 : ∀ a, _root_.GlobalTheory.AdLat.adCoord F e b (_root_.GlobalTheory.AdLat.fv F (e a)) =
      if a = b then 1 else 0 := by
    intro a
    have := _root_.GlobalTheory.AdLat.adCoord_tmul F e b 1 (e a)
    unfold _root_.GlobalTheory.AdLat.fv
    rw [this, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp [Algebra.TensorProduct.one_def]
  simp only [map_sum, _root_.GlobalTheory.AdLat.adCoord_smul, h1, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
theorem _root_.GlobalTheory.AdLat.mem_hat_pseudoBasis_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (e : Module.Basis (Fin n) E (Fin n → E)) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E), (∀ v, v ∈ L ↔ ∀ a, e.repr v a ∈ cI a) → ∀ z : Fin n → _root_.GlobalTheory.AdLat.RA F E, (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) ↔ ∀ a, z a ∈ _root_.GlobalTheory.AdLat.hat1 F (cI a : Set E) := by
  intro F E _ _ _ _ _ n L e cI hL z
  constructor
  · intro hz b
    rw [← _root_.GlobalTheory.AdLat.adCoord_sum F e z b]
    have key : _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) ≤
        (_root_.GlobalTheory.AdLat.hat1 F (cI b : Set E)).comap (_root_.GlobalTheory.AdLat.adCoord F e b) := by
      unfold _root_.GlobalTheory.AdLat.hat
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, x, hx, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe]
      rw [_root_.GlobalTheory.AdLat.adCoord_tmul]
      unfold _root_.GlobalTheory.AdLat.hat1
      exact AddSubgroup.subset_closure ⟨c, hc, _, (hL x).1 hx b, rfl⟩
    exact key hz
  · intro hz
    refine AddSubgroup.sum_mem _ fun a _ => ?_
    have key : _root_.GlobalTheory.AdLat.hat1 F (cI a : Set E) ≤
        (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))).comap
          ((smulAddHom (_root_.GlobalTheory.AdLat.RA F E)
            (Fin n → _root_.GlobalTheory.AdLat.RA F E)).flip (_root_.GlobalTheory.AdLat.fv F (e a))) := by
      unfold _root_.GlobalTheory.AdLat.hat1
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, y, hy, rfl⟩
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe,
        AddMonoidHom.flip_apply, smulAddHom_apply]
      have hmem : y • e a ∈ L := by
        rw [hL]
        intro a'
        rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; simpa using hy
        · simpa using (cI a').zero_mem
      unfold _root_.GlobalTheory.AdLat.hat
      refine AddSubgroup.subset_closure ⟨c, hc, _, hmem, ?_⟩
      funext i
      unfold _root_.GlobalTheory.AdLat.fv
      change (c ⊗ₜ[F] y) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] e a i) = c ⊗ₜ[F] (y • e a) i
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Pi.smul_apply, smul_eq_mul]
    exact key (hz a)

end GlobalTheory.AdLat
end
end

