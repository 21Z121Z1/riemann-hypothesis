import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0066
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af

section Real

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))

private theorem infDiag_eqR (k : Eˣ) : infDiag k = TR.infId E (Units.map (diagR E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - TR.infEq E 1 + TR.infEq E ((TR.infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

private theorem denseRange_unitsR : DenseRange (Units.map (diagR E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

private theorem diagR_mk (φ : E →+* ℂ) (k : E) : ((diagR E k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
  have e : diagR E k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hr (WithAbs.toAbs _ k)
  rw [e, InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]

private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  have hc : ∀ v, Continuous fun u : (TR.Rinf E)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
  have ho : IsOpen {u : (TR.Rinf E)ˣ | ∀ v, 0 < u.val v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
  have hcl : IsClosed {u : (TR.Rinf E)ˣ |
      ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ} :=
    isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
      (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
        (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
  refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
  rintro _ ⟨hk, k, rfl⟩
  have h1 := h k fun φ => by
    have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : E)
    exact h2.trans_eq (Complex.ofReal_injective h3)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
  refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (diagR_mk φ (k : E)).symm

private theorem expo_intR {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (v : InfinitePlace E) :
    ∃ k : ℤ, TR.expo χ v = k := by
  classical
  refine ⟨∑ φ : E →+* ℂ, if InfinitePlace.mk φ = v then n φ else 0, TR.expo_eq_of_exp χ v _ fun t => ?_⟩
  rw [chiInf_pos h _ fun w => Real.exp_pos _]
  simp only [TR.expU_val, Complex.ofReal_exp, ← Complex.exp_int_mul]
  rw [← Complex.exp_sum, Int.cast_sum, Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun φ _ => ?_)
  split_ifs with e
  · rw [e, Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne e]

end Real

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem sys_twist {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {R : G K Ω →* GL (Fin n) (Qbar l)}
    {sat sat' : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop} (hA : AttachedSys ι R sat) {art : Ideles K →* Gab K Ω}
    {κ : HChar K} {m : (K →+* ℂ) → ℤ} {μ : G K Ω →* (Qbar l)ˣ} (ha : IsGlobalArtin art) (h : IsLAdicOf art ι κ m μ)
    (hs : ∀ w B, sat w B → κ.UnrAt w → sat' w (B.map (· * κ.val w))) : AttachedSys ι (tw R μ) sat' := by
  refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G K Ω) _ n R).2.2 μ hA.1, ?_⟩
  filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified κ), ev_notMem (K := K) l]
    with w ⟨B, hB, hE⟩ hu hl
  refine ⟨_, hs w B hB hu, ?_⟩
  have hc : UpperTheory.V.Af.Bc.CharEig ι μ w (κ.val w : ℂ) := by
    refine fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have h4 := UpperTheory.frobenius_eigenvalues_twist K Ω l ι n R μ w _ _ hE hc
  convert h4 using 1
  simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, mul_assoc]

theorem UpperTheory.V.Sd.twR :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.TwR := by
  rintro - F Ω _ _ _ _ _ _ l _ ι n r κ ⟨-, art, χ, a, ha, hχ, hL⟩ ⟨π, hr, hA⟩
  exact ⟨π.twist χ, hr.twist (expo_intR hχ), sys_twist hA ha hL fun w B hB hu => hB.twist hu⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LineOfNotIrr
section
open Polynomial Formalism.ConjugateSelfDual Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.V.Sd
open scoped Matrix

private lemma trace_zero {k : Type} [Field k] (S T : Matrix (Fin 2) (Fin 2) k) (hT : T.det ≠ 0)
    (hS : S.charpoly.Separable) (v : Fin 2 → k) (hv : v ≠ 0) (hw : T *ᵥ v ∉ Submodule.span k {v})
    (a b c : k) (ha : S *ᵥ v = a • v) (hb : S *ᵥ (T *ᵥ v) = b • (T *ᵥ v))
    (hc : S *ᵥ (T *ᵥ (T *ᵥ v)) = c • (T *ᵥ (T *ᵥ v))) : T.trace = 0 :=
  _root_.UpperTheory.Reformulated.B.Qf25.trace_zero S T hT hS v hv hw a b c ha hb hc

private lemma line_of_not_irr {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (h : ¬ IsIrr ρ) :
    ∃ v : Fin 2 → k, v ≠ 0 ∧ ∀ g, ∃ c : k, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := by
  simp only [IsIrr, IsIrrSub, not_and, not_forall] at h
  obtain ⟨W, -, hW, hne⟩ := h top_ne_bot (fun _ _ _ => Submodule.mem_top)
  rw [not_or] at hne
  have h2 : Module.finrank k W < 2 := by
    simpa using Submodule.finrank_lt hne.2
  have h0 : Module.finrank k W ≠ 0 := fun h => hne.1 (Submodule.finrank_eq_zero.mp h)
  have h1 : Module.finrank k W = 1 := by omega
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.mp h1
  refine ⟨v, fun h => hv (Subtype.ext h), fun g => ?_⟩
  obtain ⟨c, hc⟩ := hall ⟨_, hW g v v.2⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

private lemma moves_line {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (h : IsIrr ρ) (v : Fin 2 → k)
    (hv : v ≠ 0) : ∃ t, (ρ t : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∉ Submodule.span k {v} := by
  by_contra hcon
  push Not at hcon
  have hinv : IsInv ρ (Submodule.span k {v}) := by
    intro g u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (hcon g)
  rcases h.2.2 _ le_top hinv with h1 | h1
  · exact hv (Submodule.span_singleton_eq_bot.mp h1)
  · have := finrank_span_singleton (K := k) hv
    rw [h1] at this
    simp at this

private lemma core {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (hirr : IsIrr ρ) (H : Subgroup Γ)
    (hN : H.Normal) (hs : ∃ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) k).charpoly.Separable)
    (hred : ¬ IsIrr (ρ.comp H.subtype)) :
    ∃ D : Γ → Prop, (∀ s ∈ H, D s) ∧ (∃ t, ¬ D t) ∧ (∀ s t, D s → ¬ D t → ¬ D (t * s)) ∧
      ∀ t, ¬ D t → (ρ t : Matrix (Fin 2) (Fin 2) k).trace = 0 := by
  obtain ⟨v, hv, hev⟩ := line_of_not_irr _ hred
  obtain ⟨s₀, hs₀, hsep⟩ := hs
  have hev' : ∀ s ∈ H, ∃ c : k, (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := fun s hs => hev ⟨s, hs⟩
  have hmul : ∀ (s t : Γ) (u : Fin 2 → k), (ρ (s * t) : Matrix (Fin 2) (Fin 2) k) *ᵥ u =
      (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ t : Matrix (Fin 2) (Fin 2) k) *ᵥ u) := by
    intro s t u
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hconj : ∀ g, ∃ c : k, (ρ s₀ : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) =
      c • ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) := by
    intro g
    obtain ⟨c, hc⟩ := hev' _ (hN.conj_mem' s₀ hs₀ g)
    refine ⟨c, ?_⟩
    rw [← Matrix.mulVec_smul, ← hc, ← hmul, ← hmul]
    congr 3
    group
  refine ⟨fun s => (ρ s : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ Submodule.span k {v}, fun s hs => ?_,
    moves_line ρ hirr v hv, fun s t hs ht hts => ht ?_, fun t ht => ?_⟩
  · obtain ⟨c, hc⟩ := hev' s hs
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hv
      have := hmul s⁻¹ s v
      rw [← hc, zero_smul, Matrix.mulVec_zero] at this
      simpa using this
    simp only [hmul, ← hc, Matrix.mulVec_smul] at hts
    exact (Submodule.smul_mem_iff _ hc0).mp hts
  · obtain ⟨a, ha⟩ := hev' s₀ hs₀
    obtain ⟨b, hb⟩ := hconj t
    obtain ⟨c, hc⟩ := hconj (t * t)
    rw [hmul t t] at hc
    exact trace_zero _ _ (Matrix.GeneralLinearGroup.det_ne_zero (ρ t)) hsep v hv ht a b c ha hb hc

theorem UpperTheory.V.Sd.sIabs :
    UpperTheory.V.Sd.SIabs := by
  intro l _ _ Γ _ ρ Φ hΦ hirr hres H hN hs hred
  obtain ⟨D, hH, ⟨t₀, ht₀⟩, hmul, htr⟩ := core ρ hirr H hN hs hred
  have hneg : ∀ t, ¬ D t → ‖(Φ t : Qbar l) + 1‖ < 1 := by
    intro t ht
    have h := hres t 1
    rw [Matrix.charpoly_fin_two, htr t ht, Fin.prod_univ_two] at h
    have e : (X - C ((![1, Φ] : Fin 2 → Γ →* (Qbar l)ˣ) 0 t : Qbar l)) * (X - C ((![1, Φ] : Fin 2 → Γ →* (Qbar l)ˣ) 1 t : Qbar l)) =
        X ^ 2 - C ((Φ t : Qbar l) + 1) * X + C (Φ t : Qbar l) := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_add, map_one]
      ring
    rw [e] at h
    simpa [coeff_X_pow, coeff_C, coeff_one] using h
  have hpos : ∀ s, D s → ‖(Φ s : Qbar l) - 1‖ < 1 := by
    intro s hs
    have h1 := hneg _ ht₀
    have h2 := hneg _ (hmul s t₀ hs ht₀)
    rw [map_mul, Units.val_mul] at h2
    have e : (Φ t₀ : Qbar l) * ((Φ s : Qbar l) - 1) = ((Φ t₀ : Qbar l) * Φ s + 1) + (-((Φ t₀ : Qbar l) + 1)) := by ring
    have h3 := IsUltrametricDist.norm_add_le_max ((Φ t₀ : Qbar l) * Φ s + 1) (-((Φ t₀ : Qbar l) + 1))
    rw [← e, norm_mul, hΦ, one_mul, norm_neg] at h3
    exact h3.trans_lt (max_lt h2 h1)
  refine ⟨fun s hs => by simpa [Cong] using hpos s (hH s hs), fun s => ?_⟩
  have e : ((Φ s ^ 2 : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) = ((Φ s : Qbar l) + 1) * ((Φ s : Qbar l) - 1) := by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; ring
  have p1 : ‖(Φ s : Qbar l) + 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (Φ s : Qbar l) 1
    simpa [hΦ] using this
  have p2 : ‖(Φ s : Qbar l) - 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (Φ s : Qbar l) (-1)
    simpa [hΦ, sub_eq_add_neg] using this
  rw [Cong, e, norm_mul]
  by_cases hs : D s
  · exact mul_lt_one_of_nonneg_of_lt_one_right p1 (norm_nonneg _) (hpos s hs)
  · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hneg s hs) p2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SelfTwGal
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem tendsto_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

theorem UpperTheory.V.Sd.selfTwGal :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Sd.SelfTwGal := by
  intro P F Ω _ _ _ _ _ l _ ι n r sat hu hc hatt η m hm hη hη1 hT
  obtain ⟨art, ha⟩ := P.litN.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η) hm hη)
  have hpow : δ ^ m = 1 := hL.pow_eq_one ha.quot.surjective hη
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv A hA =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hA).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hA hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  refine ⟨δ, ?_, isOpen_ker_of_pow δ hδc hm fun g => DFunLike.congr_fun hpow g, ?_, ?_⟩
  · rintro rfl
    refine hη1 (Subtype.ext (MonoidHom.ext fun x => Units.ext ?_))
    obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
    have e := hL x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, MonoidHom.one_apply, Units.val_one, eq_comm,
      map_eq_one_iff _ ι.symm.injective] at e
    exact e
  · refine isoOfFrob P F Ω l ι n r _ hc (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ n r δ hc hδc) hatt.1
      ((UpperTheory.galoisRep_irreducibility_criterion.1 _ (G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hT] with v hv hw
    obtain ⟨B, hB, hF⟩ := hv
    obtain ⟨h1, B', hB', h2⟩ := hw
    obtain rfl := hu v _ _ hB hB'
    refine ⟨_, hF, ?_⟩
    have h4 := UpperTheory.frobenius_eigenvalues_twist F Ω l ι n r δ _ _ _ hF (hE v h1)
    convert h4 using 1
    conv_lhs => rw [← h2]
    simp only [algSat_eq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
  · intro E _ _ _ _ _ hN
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := F) E
    haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
    have hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, CharEig ι (δ.comp (res F Ω E)) w 1 := by
      filter_upwards [hN.2.2, (tendsto_under' (K := F) (K' := E)).eventually hT] with w h1 h2
      have hf := normV_under (K := F) w
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ hf).2 δ _ (hE _ h2.1)
      rwa [← Units.val_pow_eq_pow_val, h1 _ hf, Units.val_one] at h3
    have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 hw) (f := fun s => δ (res F Ω E s)) (f' := fun _ => 1)
      (hδc.comp (continuous_restrictScalarsHom F E Ω)) continuous_const fun v hv _ A hA σ hσ => by
        have h := ((not_not.1 hv : CharEig _ _ _ _) A hA).2 σ hσ
        rw [map_eq_one_iff _ ι.injective, map_inv, Units.val_eq_one, inv_eq_one] at h
        exact h
    exact MonoidHom.ext fun s => congrFun key s
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial UpperTheory.V.Af UpperTheory.V.Sd

private theorem charpoly_smul' {K : Type} [Field K] [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by field_simp⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h, mul_sub]

private theorem scaleRoots_prod' {K ι : Type} [Field K] (m : Finset ι) (a : ι → K) (s : K) :
    (∏ j ∈ m, (X - C (a j))).scaleRoots s = ∏ j ∈ m, (X - C (a j * s)) := by
  classical
  induction m using Finset.induction_on with
  | empty => simp [one_scaleRoots]
  | insert j m hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots]

private theorem sub_le' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

private theorem prod_cong {K ι : Type} [NormedField K] [IsUltrametricDist K] (m : Finset ι) (a b : ι → K)
    (ha : ∀ j, ‖a j‖ ≤ 1) (hab : ∀ j, ‖b j - a j‖ < 1) :
    ∀ i, ‖(∏ j ∈ m, (X - C (a j))).coeff i‖ ≤ 1 ∧
      ‖(∏ j ∈ m, (X - C (a j))).coeff i - (∏ j ∈ m, (X - C (b j))).coeff i‖ < 1 := by
  classical
  induction m using Finset.induction_on with
  | empty =>
    intro i
    simp only [Finset.prod_empty, sub_self, norm_zero, zero_lt_one, and_true, coeff_one]
    split_ifs <;> simp
  | insert j m hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    set p := ∏ j ∈ m, (X - C (a j))
    set q := ∏ j ∈ m, (X - C (b j))
    have hb : ‖b j‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (b j - a j) (a j)
      rw [sub_add_cancel] at this
      exact this.trans (max_le (hab j).le (ha j))
    have h1 : ∀ i, ‖a j * p.coeff i‖ ≤ 1 := fun i => by
      rw [norm_mul]; exact mul_le_one₀ (ha j) (norm_nonneg _) (ih i).1
    have h2 : ∀ i, ‖a j * p.coeff i - b j * q.coeff i‖ < 1 := fun i => by
      have e : a j * p.coeff i - b j * q.coeff i = b j * (p.coeff i - q.coeff i) - (b j - a j) * p.coeff i := by ring
      rw [e]
      refine (sub_le' _ _).trans_lt (max_lt ?_ ?_) <;> rw [norm_mul]
      · exact mul_lt_one_of_nonneg_of_lt_one_right hb (norm_nonneg _) (ih i).2
      · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hab j) (ih i).1
    intro i
    cases i with
    | zero =>
      simp only [sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub, norm_neg]
      refine ⟨h1 0, ?_⟩
      rw [neg_sub_neg, norm_sub_rev]
      exact h2 0
    | succ i =>
      simp only [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
      refine ⟨(sub_le' _ _).trans (max_le (ih i).1 (h1 _)), ?_⟩
      rw [sub_sub_sub_comm]
      exact (sub_le' _ _).trans_lt (max_lt (ih i).2 (h2 _))

theorem UpperTheory.V.Sd.shapeFacts :
    UpperTheory.V.Sd.ShapeFacts := by
  intro l _ Γ _ n r δ
  have conj : ∀ (g : GL (Fin n) (Qbar l)) (s : Γ), ((g * tw r δ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      (δ s : Qbar l) • ((g * r s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := fun g s => by
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro H χ ⟨g, hg⟩
    refine ⟨g, fun s hs => ?_⟩
    rw [conj, hg s hs, ← Matrix.diagonal_smul]
    congr 1
    ext i
    simp [mul_comm]
  · rintro H χ χ' e ⟨g, hg⟩ h
    let P : GL (Fin n) (Qbar l) := ⟨e.toPEquiv.toMatrix, e.symm.toPEquiv.toMatrix,
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
    refine ⟨P * g, fun s hs => ?_⟩
    have e1 : P * g * r s * (P * g)⁻¹ = P * (g * r s * g⁻¹) * P⁻¹ := by group
    rw [e1, Units.val_mul, Units.val_mul P, hg s hs]
    change e.toPEquiv.toMatrix * _ * e.symm.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [Matrix.diagonal_apply, h i s hs]
  · rintro H κ ⟨g, hg⟩
    refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · rw [conj, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
    · rw [conj, Matrix.smul_apply, (hg s).2 i]
      simp [mul_comm]
  · intro χ hδ h s i
    have e1 : ∏ j, (X - C (((χ j * δ) s : (Qbar l)ˣ) : Qbar l)) = (∏ j, (X - C (χ j s : Qbar l))).scaleRoots (δ s) := by
      rw [scaleRoots_prod']; simp
    have e2 : (∏ j, (X - C (χ j s : Qbar l))).natDegree = n := by
      rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]; simp
    rw [e1, tw_val, charpoly_smul' _ (Units.ne_zero _), coeff_scaleRoots, coeff_scaleRoots, e2,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, ← sub_mul, norm_mul, norm_pow, hδ, one_pow, mul_one]
    exact h s i
  · intro χ χ' e hχ h hc s i
    have h1 := h s i
    rw [← Equiv.prod_comp e fun j => (X - C (χ j s : Qbar l))] at h1
    have h2 := (prod_cong Finset.univ (fun j => (χ (e j) s : Qbar l)) (fun j => (χ' j s : Qbar l))
      (fun j => (hχ _ _).le) (fun j => hc j s) i).2
    rw [← sub_add_sub_cancel _ ((∏ j, (X - C (χ (e j) s : Qbar l))).coeff i)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
  · intro hr
    have key : ∀ W, IsInv (tw r δ) W ↔ IsInv r W := fun W => by
      constructor
      · intro h g v hv
        have := W.smul_mem ((δ g : Qbar l)⁻¹) (h g v hv)
        rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
      · intro h g v hv
        rw [tw_val, Matrix.smul_mulVec]
        exact W.smul_mem _ (h g v hv)
    unfold IsIrr IsIrrSub at hr ⊢
    simpa only [key] using hr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SymmetricCubePreservesSymplecticForm
section
open Polynomial UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped Matrix

namespace UpperTheory.V.Sd

private noncomputable def s3F {S : Type} [CommRing S] (t d : S) : S[X] :=
  X ^ 4 + C (-(t ^ 3 - 2 * t * d)) * X ^ 3 + C (2 * d ^ 3 + (t ^ 3 - 3 * t * d) * d * t) * X ^ 2 +
    C (-(d ^ 3 * (t ^ 3 - 2 * t * d))) * X ^ 1 + C (d ^ 6) * X ^ 0

section Rel

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private def Rl (x y : K) : Prop := ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1

private theorem Rl.left {x y : K} (h : Rl x y) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.2.le h.1)

private theorem Rl.add {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x + z) (y + w) := by
  refine ⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.1 h'.1), ?_⟩
  rw [add_sub_add_comm]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h.2 h'.2)

omit [IsUltrametricDist K] in
private theorem Rl.neg {x y : K} (h : Rl x y) : Rl (-x) (-y) := by
  refine ⟨by simpa using h.1, ?_⟩
  rw [show -x - -y = -(x - y) by ring, norm_neg]
  exact h.2

private theorem Rl.sub {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x - z) (y - w) := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

private theorem Rl.mul {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x * z) (y * w) := by
  refine ⟨by rw [norm_mul]; exact mul_le_one₀ h.1 (norm_nonneg _) h'.1, ?_⟩
  rw [show x * z - y * w = x * (z - w) + (x - y) * w by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h.left (norm_nonneg _) h'.2
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h.2 h'.1

private theorem Rl.pow {x y : K} (h : Rl x y) (n : ℕ) : Rl (x ^ n) (y ^ n) := by
  induction n with
  | zero => simp [Rl]
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

private theorem Rl.nat (n : ℕ) : Rl (n : K) n := ⟨IsUltrametricDist.norm_natCast_le_one K n, by simp⟩

end Rel

end UpperTheory.V.Sd
end

