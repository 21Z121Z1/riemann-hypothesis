import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerMapEqConstMulProdInner
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem MultilinearMap.inner_map_eq_const_mul_prod_inner
    {ι : Type} [Fintype ι] {Xs : ι → Type} [∀ i, NormedAddCommGroup (Xs i)]
    [∀ i, InnerProductSpace ℂ (Xs i)] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : MultilinearMap ℂ Xs E) (K : ℝ) (hf : ∀ x, ‖f x‖ ^ 2 = K * ∏ i, ‖x i‖ ^ 2) :
    ∀ x y, ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by
  classical
  have hdiag : ∀ x, ⟪f x, f x⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, x i⟫_ℂ := by
    intro x
    simp only [inner_self_eq_norm_sq_to_K]
    have h := congrArg (fun r : ℝ => (r : ℂ)) (hf x)
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_prod] at h
    exact h
  have hprod : ∀ (x y : ∀ i, Xs i) (j : ι) (u v : Xs j),
      ∏ i, ⟪Function.update x j u i, Function.update y j v i⟫_ℂ
        = ⟪u, v⟫_ℂ * ∏ i ∈ Finset.univ.erase j, ⟪x i, y i⟫_ℂ := by
    intro x y j u v
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
      Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have key : ∀ s : Finset ι, ∀ x y : (∀ i, Xs i), (∀ i ∉ s, x i = y i) →
      ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x y h
      have hxy : x = y := funext fun i => h i (Finset.notMem_empty i)
      subst hxy
      exact hdiag x
    | insert j s hj ih =>
      intro x y hxy
      set C := ∏ i ∈ Finset.univ.erase j, ⟪x i, y i⟫_ℂ with hC
      have hd : ∀ u : Xs j, ⟪f (Function.update x j u), f (Function.update y j u)⟫_ℂ
          = (K : ℂ) * (⟪u, u⟫_ℂ * C) := by
        intro u
        rw [ih _ _ ?_, hprod]
        intro i hi
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij, Function.update_of_ne hij]
          exact hxy i (by simp [hij, hi])
      have hab : ∀ a b : Xs j, ⟪f (Function.update x j a), f (Function.update y j b)⟫_ℂ
          = (K : ℂ) * (⟪a, b⟫_ℂ * C) := by
        intro a b
        have ha := hd a
        have hb := hd b
        have h1 := hd (a + b)
        have h2 := hd (a + Complex.I • b)
        simp only [MultilinearMap.map_update_add, MultilinearMap.map_update_smul, inner_add_left,
          inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I] at h1 h2
        have e1 : ⟪f (Function.update x j a), f (Function.update y j b)⟫_ℂ
            + ⟪f (Function.update x j b), f (Function.update y j a)⟫_ℂ
            = (K : ℂ) * C * (⟪a, b⟫_ℂ + ⟪b, a⟫_ℂ) := by
          linear_combination h1 - ha - hb
        have e2 : Complex.I * (⟪f (Function.update x j a), f (Function.update y j b)⟫_ℂ
            - ⟪f (Function.update x j b), f (Function.update y j a)⟫_ℂ
            - (K : ℂ) * C * (⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ)) = 0 := by
          linear_combination h2 - ha + Complex.I * Complex.I * hb
        have e3 := (mul_eq_zero.mp e2).resolve_left Complex.I_ne_zero
        linear_combination (e1 + e3) / 2
      have := hab (x j) (y j)
      simp only [Function.update_eq_self] at this
      rw [this, ← hprod x y j (x j) (y j)]
      simp only [Function.update_eq_self]
  intro x y
  exact key Finset.univ x y (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfTsumTranslateNormLe
section
open MeasureTheory

namespace GlobalTheory

theorem integrable_of_tsum_translate_norm_le
    (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [Countable Γ] (μ : Measure G) (hμ : μ.IsAddLeftInvariant) (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h𝓕μ : μ 𝓕 < ⊤) (c : G → ℂ) (hc : Continuous c)
    (C : ℝ) (hC : ∀ w : G, Summable (fun γ : Γ => ‖c ((γ : G) + w)‖) ∧
      ∑' γ : Γ, ‖c ((γ : G) + w)‖ ≤ C) : Integrable c μ := by
  haveI : VAddInvariantMeasure Γ G μ := ⟨fun g s _ => measure_preimage_add μ (g : G) s⟩
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rw [h𝓕.lintegral_eq_tsum'' (fun x => ‖c x‖ₑ)]
  rw [← lintegral_tsum (f := fun (γ : Γ) x => ‖c (γ +ᵥ x)‖ₑ) fun γ : Γ =>
    ((hc.comp (continuous_const_vadd (γ : G))).measurable.enorm).aemeasurable]
  have hpt : ∀ x, ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ ≤ ENNReal.ofReal C := by
    intro x
    have h1 : ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ = ENNReal.ofReal (∑' γ : Γ, ‖c ((γ : G) + x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hC x).1]
      refine tsum_congr fun γ => ?_
      rw [ofReal_norm_eq_enorm]
      rfl
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hC x).2
  calc ∫⁻ x in 𝓕, ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ ∂μ ≤ ∫⁻ _ in 𝓕, ENNReal.ofReal C ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal C * μ 𝓕 := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h𝓕μ

example : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G), μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ c : G → ℂ, Continuous c → ∀ C : ℝ, (∀ w : G, Summable (fun γ : Γ => ‖c ((γ : G) + w)‖) ∧ ∑' γ : Γ, ‖c ((γ : G) + w)‖ ≤ C) → Integrable c μ :=
  fun G _ _ _ _ _ _ Γ _ μ hμ 𝓕 h𝓕 h𝓕μ c hc C hC =>
    integrable_of_tsum_translate_norm_le G Γ μ hμ 𝓕 h𝓕 h𝓕μ c hc C hC

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralContinuousMultilinearMapPiMeasure
section
open MeasureTheory

namespace GlobalTheory.MultilinFubini

theorem aestronglyMeasurable_pi_of_forall {α : Type*} {m0 : MeasurableSpace α} {ν : Measure α}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    {f : ∀ i, α → E i} (hf : ∀ i, AEStronglyMeasurable (f i) ν) :
    AEStronglyMeasurable (fun x i => f i x) ν := by
  have key : ∀ s : Finset ι,
      AEStronglyMeasurable (fun x (i : ι) => if i ∈ s then f i x else 0) ν := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, if_false]; exact aestronglyMeasurable_const
    | insert a s ha ih =>
      have hc : Continuous (fun p : E a × (∀ i, E i) => Function.update p.2 a p.1) :=
        continuous_snd.update a continuous_fst
      refine (hc.comp_aestronglyMeasurable ((hf a).prodMk ih)).congr (ae_of_all _ fun x => ?_)
      funext i
      by_cases hi : i = a
      · subst hi; simp
      · simp [Function.update_of_ne hi, hi]
  simpa using key Finset.univ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
  {E : ι → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

def vecOn (g : ∀ i, X i → E i) (s : Finset ι) (m : ∀ i, E i) (x : ∀ i : s, X i) : ∀ i, E i :=
  fun i => if h : i ∈ s then g i (x ⟨i, h⟩) else m i

theorem integrable_vecOn (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) (m : ∀ i, E i) :
    Integrable (fun x => Φ (vecOn g s m x)) (Measure.pi fun i : s => μ i) := by
  have hmeas : AEStronglyMeasurable (fun x => vecOn g s m x) (Measure.pi fun i : s => μ i) := by
    refine aestronglyMeasurable_pi_of_forall (f := fun i x => vecOn g s m x i) fun i => ?_
    by_cases hi : i ∈ s
    · simp only [vecOn, dif_pos hi]
      exact (hg i).1.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun j : s => μ j) ⟨i, hi⟩)
    · simp only [vecOn, dif_neg hi]; exact aestronglyMeasurable_const
  have hdom : Integrable (fun x : ∀ j : s, X j => ‖Φ‖ * ((∏ j : s, ‖g j (x j)‖) * ∏ i ∈ sᶜ, ‖m i‖))
      (Measure.pi fun i : s => μ i) :=
    ((Integrable.fintype_prod_dep (f := fun (j : s) (y : X j) => ‖g j y‖)
      fun j => (hg j).norm).mul_const _).const_mul _
  refine hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => ?_)
  refine (Φ.le_opNorm _).trans (le_of_eq ?_)
  congr 1
  rw [← Finset.prod_mul_prod_compl s]
  congr 1
  · rw [← Finset.prod_coe_sort s]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [vecOn, j.2]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp [vecOn, Finset.mem_compl.1 hi]

theorem integral_vecOn (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, CompleteSpace (E i)] [CompleteSpace F]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) : ∀ m : ∀ i, E i,
    ∫ x, Φ (vecOn g s m x) ∂(Measure.pi fun i : s => μ i) =
      Φ (fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro m
    rw [Measure.pi_of_empty (x := fun i => isEmptyElim i)]
    have hc : (fun x : ∀ i : (∅ : Finset ι), X i => Φ (vecOn g ∅ m x)) = fun _ => Φ m := by
      funext x; congr 1
    rw [hc]; simp
  | insert a s ha ih =>
    intro m
    rw [Finset.insert_eq]
    have hd : Disjoint ({a} : Finset ι) s := Finset.disjoint_singleton_left.2 ha
    have hmp := measurePreserving_piFinsetUnion hd μ
    letI : Unique ↥({a} : Finset ι) :=
      ⟨⟨⟨a, Finset.mem_singleton_self a⟩⟩, fun j => Subtype.ext (Finset.mem_singleton.1 j.2)⟩
    have hpt : ∀ p : (∀ i : ({a} : Finset ι), X i) × (∀ i : s, X i),
        vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p) =
          vecOn g s (Function.update m a (g a (p.1 default))) p.2 := by
      rintro ⟨y, z⟩
      have he : (MeasurableEquiv.piFinsetUnion X hd (y, z) : ∀ i : ↥({a} ∪ s), X i) =
          Equiv.piFinsetUnion X hd (y, z) := rfl
      funext i
      by_cases hia : i = a
      · subst hia
        have h1 : i ∈ ({i} : Finset ι) ∪ s := by simp
        simp only [vecOn, dif_pos h1, dif_neg ha, Function.update_self, he]
        rw [Equiv.piFinsetUnion_left X hd (Finset.mem_singleton_self i)]
        rfl
      · by_cases his : i ∈ s
        · have h1 : i ∈ ({a} : Finset ι) ∪ s := by simp [his]
          simp only [vecOn, dif_pos h1, dif_pos his, he]
          rw [Equiv.piFinsetUnion_right X hd his]
        · have h1 : i ∉ ({a} : Finset ι) ∪ s := by simp [his, hia]
          simp only [vecOn, dif_neg h1, dif_neg his, Function.update_of_ne hia]
    have hint : Integrable (fun p => Φ (vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p)))
        ((Measure.pi fun i : ({a} : Finset ι) => μ i).prod (Measure.pi fun i : s => μ i)) :=
      (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2
        (integrable_vecOn μ Φ g hg _ m)
    rw [← hmp.integral_comp', integral_prod _ hint]
    simp only [hpt, ih]
    set w : ∀ i, E i := fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i with hw
    have hupd : ∀ c : E a, (fun i => if i ∈ s then ∫ y, g i y ∂μ i else Function.update m a c i) =
        Function.update w a c := by
      intro c; funext i
      by_cases hia : i = a
      · subst hia; simp [hw, ha]
      · by_cases his : i ∈ s
        · simp [hw, his, Function.update_of_ne hia]
        · simp [hw, his, Function.update_of_ne hia]
    simp only [hupd]
    have hL : ∀ c : E a, Φ (Function.update w a c) = Φ.toContinuousLinearMap w a c := fun c => rfl
    simp only [hL]
    have h1 := (measurePreserving_piUnique (fun i : ({a} : Finset ι) => μ i)).integral_comp'
      (fun t => Φ.toContinuousLinearMap w a (g a t))
    rw [show (∫ x : ∀ i : ({a} : Finset ι), X i, Φ.toContinuousLinearMap w a (g a (x default))
        ∂Measure.pi fun i : ({a} : Finset ι) => μ i) = ∫ t, Φ.toContinuousLinearMap w a (g a t) ∂μ a from h1]
    rw [(Φ.toContinuousLinearMap w a).integral_comp_comm (hg a), ← hL]
    congr 1
    funext i
    by_cases hia : i = a
    · subst hia; simp [hw]
    · by_cases his : i ∈ s
      · simp [hw, his, Function.update_of_ne hia]
      · simp [hw, his, hia, Function.update_of_ne hia]

theorem integral_multilinear_pi : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (E : ι → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i), (∀ i, Integrable (g i) (μ i)) → Integrable (fun x : ∀ i, X i => Φ fun i => g i (x i)) (Measure.pi μ) ∧ ∫ x, Φ (fun i => g i (x i)) ∂Measure.pi μ = Φ fun i => ∫ y, g i y ∂μ i := by
  intro ι _ _ X _ μ _ E _ _ _ F _ _ _ Φ g hg
  constructor
  · have hmeas : AEStronglyMeasurable (fun x : ∀ i, X i => fun i => g i (x i)) (Measure.pi μ) :=
      aestronglyMeasurable_pi_of_forall (f := fun i (x : ∀ i, X i) => g i (x i)) fun i =>
        (hg i).1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval μ i)
    have hdom : Integrable (fun x : ∀ i, X i => ‖Φ‖ * ∏ i, ‖g i (x i)‖) (Measure.pi μ) :=
      (Integrable.fintype_prod_dep (f := fun i (y : X i) => ‖g i y‖) fun i => (hg i).norm).const_mul _
    exact hdom.mono' (Φ.cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun x => Φ.le_opNorm _)
  · let e : (↥(Finset.univ : Finset ι)) ≃ ι := Equiv.subtypeUnivEquiv Finset.mem_univ
    have hmp := measurePreserving_piCongrLeft μ e
    rw [← hmp.integral_comp']
    have hpt : ∀ z : ∀ i : (Finset.univ : Finset ι), X i,
        (fun i => g i (MeasurableEquiv.piCongrLeft X e z i)) = vecOn g Finset.univ 0 z := by
      intro z; funext i
      have h := Equiv.piCongrLeft_apply_apply X e z ⟨i, Finset.mem_univ i⟩
      simp only [vecOn, dif_pos (Finset.mem_univ i)]
      rw [MeasurableEquiv.coe_piCongrLeft]
      exact congrArg (g i) h
    refine ((integral_congr_ae (ae_of_all _ fun z => congrArg Φ (hpt z))).trans
      (integral_vecOn μ Φ g hg Finset.univ 0)).trans ?_
    simp

end GlobalTheory.MultilinFubini
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHaarEqZeroOfFibreIntegralsEqZero
section
open MeasureTheory

namespace GlobalTheory

theorem integral_haar_eq_zero_of_fibre_integrals_eq_zero :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ (P Q : Subgroup H), IsClosed (P : Set H) → IsClosed (Q : Set H) → (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) → (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) → (∀ h, h ∈ P → h ∈ Q → h = 1) → ∀ F : H → ℂ, (∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∫ p, F ((p : H) * q) ∂ν = 0) → ∫ h, F h ∂μ = 0 := by
  intro H _ _ _ _ _ _ _ _ μ hμ P Q hP hQ hcomm hgen hdisj F hF
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology (P : Set H)
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology (Q : Set H)
  haveI : BorelSpace P := Subtype.borelSpace (P : Set H)
  haveI : BorelSpace Q := Subtype.borelSpace (Q : Set H)
  let m : P × Q →* H :=
    { toFun := fun x => (x.1 : H) * x.2
      map_one' := by simp
      map_mul' := by
        rintro ⟨p, q⟩ ⟨p', q'⟩
        simp only [Prod.mk_mul_mk, Subgroup.coe_mul]
        have h := hcomm p' p'.2 q q.2
        calc (p : H) * p' * (q * q') = p * (p' * q) * q' := by simp only [mul_assoc]
          _ = p * (q * p') * q' := by rw [h]
          _ = p * q * (p' * q') := by simp only [mul_assoc] }
  have hm : ∀ x : P × Q, m x = (x.1 : H) * x.2 := fun _ => rfl
  have hcont : Continuous m :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hsurj : Function.Surjective m := by
    intro h
    obtain ⟨p, hp, q, hq, rfl⟩ := hgen h
    exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  have hinj : Function.Injective m := by
    rw [injective_iff_map_eq_one]
    rintro ⟨p, q⟩ h
    rw [hm] at h
    have h1 : (p : H) = (q : H)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hp1 : (p : H) = 1 := hdisj p p.2 (h1 ▸ Q.inv_mem q.2)
    have hq1 : (q : H) = 1 := by simpa [hp1] using h
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hq1)
  have hopen : IsOpenMap m := m.isOpenMap_of_sigmaCompact hsurj hcont
  let e : (P × Q) ≃* H := MulEquiv.ofBijective m ⟨hinj, hsurj⟩
  let φ : (P × Q) ≃ₜ H := e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen
  let νP : Measure P := Measure.haar
  let νQ : Measure Q := Measure.haar
  haveI : νP.IsHaarMeasure := inferInstance
  haveI : νQ.IsHaarMeasure := inferInstance
  haveI : (νP.prod νQ).IsHaarMeasure := inferInstance
  haveI : ((νP.prod νQ).map e).IsHaarMeasure :=
    e.isHaarMeasure_map (νP.prod νQ) φ.continuous φ.symm.continuous
  have hμeq := Measure.isMulLeftInvariant_eq_smul μ ((νP.prod νQ).map e)
  have hzero : ∫ h, F h ∂((νP.prod νQ).map e) = 0 := by
    have hemb : MeasurableEmbedding e := φ.measurableEmbedding
    rw [hemb.integral_map]
    by_cases hint : Integrable (fun x => F (e x)) (νP.prod νQ)
    · rw [integral_prod_symm _ hint]
      have : ∀ q : Q, ∫ p : P, F (e (p, q)) ∂νP = 0 := fun q => hF νP inferInstance q q.2
      simp [this]
    · exact integral_undef hint
  rw [hμeq, integral_smul_nnreal_measure, hzero, smul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerMemISupRangeEqSumSmul
section
namespace GlobalTheory

open Representation

theorem intertwiner_mem_iSup_range_eq_sum_smul (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hS : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id)
    (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ)
    (hinj : Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)))
    (ψ : π.IntertwiningMap ρ)
    (hψ : LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap) :
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by
  classical
  let Φ : (Fin m → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
  have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by
    intro w; simp [Φ, LinearMap.sum_apply]
  have hΦinj : Function.Injective Φ := by
    intro a b h; apply hinj; simpa [hΦ] using h
  have hle : (⨆ j, LinearMap.range (φ j).toLinearMap) ≤ LinearMap.range Φ := by
    refine iSup_le fun j => ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨Pi.single j n, ?_⟩
    rw [hΦ]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hmem : ∀ n, ψ.toLinearMap n ∈ LinearMap.range Φ := fun n =>
    hle (hψ ⟨n, rfl⟩)
  let e := LinearEquiv.ofInjective Φ hΦinj
  let Wm : N →ₗ[ℂ] (Fin m → N) := e.symm.toLinearMap ∘ₗ ψ.toLinearMap.codRestrict _ hmem
  have hW : ∀ n, Φ (Wm n) = ψ n := by
    intro n
    simp only [Wm, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 : e (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ⟨ψ.toLinearMap n, hmem n⟩ := e.apply_symm_apply _
    have h3 := congrArg Subtype.val h2
    change Φ (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ψ n
    rw [← LinearEquiv.ofInjective_apply Φ (h := hΦinj)]
    exact h3
  have hWg : ∀ g n, Wm (π g n) = fun j => π g (Wm n j) := by
    intro g n
    apply hΦinj
    rw [hW, hΦ, ψ.isIntertwining, ← hW, hΦ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(φ j).isIntertwining]
  have hc : ∀ j, ∃ c : ℂ, ∀ n, Wm n j = c • n := by
    intro j
    let θ : π.IntertwiningMap π :=
      (LinearMap.proj j ∘ₗ Wm).intertwiningMap_of_isIntertwiningMap π π (by
        intro g v
        simp [hWg])
    obtain ⟨c, hc⟩ := hS θ
    refine ⟨c, fun n => ?_⟩
    have h1 : Wm n j = θ.toLinearMap n := rfl
    rw [h1, hc]
    simp
  choose c hc using hc
  refine ⟨c, fun n => ?_⟩
  rw [← hW, hΦ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, map_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory

open scoped Pointwise

theorem lintegral_fundamentalDomain_le_of_meets_orbits
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (ν : Measure G) [ν.IsMulLeftInvariant] {𝓕 S : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 ν) (_hS : MeasurableSet S)
    (hmeet : ∀ g, ∃ γ ∈ Γ, γ * g ∈ S) {f : G → ℝ≥0∞} (_hf : Measurable f)
    (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in S, f g ∂ν := by
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • S ∩ 𝓕 := by
    intro g hg
    obtain ⟨γ, hγ, hγS⟩ := hmeet g
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩
    refine Set.mem_smul_set.2 ⟨γ * g, hγS, ?_⟩
    show (γ⁻¹ : G) * (γ * g) = g
    group
  calc ∫⁻ g in 𝓕, f g ∂ν ≤ ∫⁻ g in ⋃ γ : Γ, γ • S ∩ 𝓕, f g ∂ν := lintegral_mono_set hsub
    _ ≤ ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f g ∂ν := lintegral_iUnion_le _ _
    _ = ∑' γ : Γ, ∫⁻ g in γ • S ∩ 𝓕, f (γ⁻¹ • g) ∂ν := by
        refine tsum_congr fun γ => ?_
        congr 1
        funext g
        show f g = f ((γ⁻¹ : Γ) * g)
        exact (hinv _ (γ⁻¹ : Γ).2 g).symm
    _ = ∫⁻ g in S, f g ∂ν := (h𝓕.setLIntegral_eq_tsum' f S).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MainThm
section
open MeasureTheory DoubleCoset

namespace GlobalTheory.TwistedOperatorMainTheorem

theorem main_thm : ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (m : MeasureTheory.Measure G) [MeasureTheory.Measure.IsHaarMeasure m] (J : Subgroup G), IsOpen (↑J : Set G) → IsCompact (↑J : Set G) → ∀ (ι : Type) [Countable ι] (x : ι → G), Pairwise (Function.onFun Disjoint fun (i : ι) ↦ DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) → ∀ (F : G → ℂ), (∀ (g j : G), j ∈ J → ∀ j' ∈ J, F (j * g * j') = F g) → (∀ (g : G), F g ≠ (0 : ℂ) → ∃ (i : ι), g ∈ DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) → (Summable fun (i : ι) ↦ MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) * ‖F (x i)‖) → MeasureTheory.Integrable F m ∧ HasSum (fun (i : ι) ↦ (↑(MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G))) : ℂ) * F (x i)) (∫ (g : G), F g ∂m) ∧ HasSum (fun (c : DoubleCoset.Quotient (↑J : Set G) (↑J : Set G)) ↦ (↑(MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (Quotient.out c) (↑J : Set G) (↑J : Set G))) : ℂ) * F (Quotient.out c)) (∫ (g : G), F g ∂m) := by
  intro G _ _ _ _ _ m _ J hJo hJc ι _ x hdisj F hF hsupp hsum

  have hmeas : ∀ a : G, MeasurableSet (doubleCoset a (J : Set G) J) := fun a =>
    (IsOpen.mul_left hJo).measurableSet
  have hfin : ∀ a : G, m (doubleCoset a (J : Set G) J) < ⊤ := fun a =>
    ((hJc.mul isCompact_singleton).mul hJc).measure_lt_top

  have hconst : ∀ a g, g ∈ doubleCoset a (J : Set G) J → F g = F a := by
    intro a g hg
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset.1 hg
    exact hF a u hu w hw
  have hint : ∀ i, ∫ g in doubleCoset (x i) (J : Set G) J, F g ∂m =
      (m.real (doubleCoset (x i) (J : Set G) J) : ℂ) * F (x i) := by
    intro i
    rw [setIntegral_congr_fun (hmeas _) (fun g hg => hconst (x i) g hg), setIntegral_const, Complex.real_smul]
  have hnorm : ∀ i, ∫ g in doubleCoset (x i) (J : Set G) J, ‖F g‖ ∂m =
      m.real (doubleCoset (x i) (J : Set G) J) * ‖F (x i)‖ := by
    intro i
    rw [setIntegral_congr_fun (hmeas _) (fun g hg => by rw [hconst (x i) g hg]), setIntegral_const, smul_eq_mul]
  have hon : ∀ i, IntegrableOn F (doubleCoset (x i) (J : Set G) J) m := fun i =>
    (integrableOn_const (hfin (x i)).ne).congr_fun (fun g hg => (hconst (x i) g hg).symm) (hmeas _)

  have hU : IntegrableOn F (⋃ i, doubleCoset (x i) (J : Set G) J) m :=
    integrableOn_iUnion_of_summable_integral_norm hon (by simpa only [hnorm] using hsum)
  have hout : ∀ g, g ∉ ⋃ i, doubleCoset (x i) (J : Set G) J → F g = 0 := by
    intro g hg
    by_contra h
    obtain ⟨i, hi⟩ := hsupp g h
    exact hg (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hsumI : HasSum (fun i => (m.real (doubleCoset (x i) (J : Set G) J) : ℂ) * F (x i)) (∫ g, F g ∂m) := by
    have h := hasSum_integral_iUnion (fun i => hmeas (x i)) hdisj hU
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at h
    simp only [hint] at h
    exact h
  refine ⟨hU.integrable_of_forall_notMem_eq_zero hout, hsumI, ?_⟩

  have hinj : Function.Injective (fun i => DoubleCoset.mk J J (x i)) := by
    intro i j hij
    by_contra hne
    have hj : x j ∈ doubleCoset (x i) (J : Set G) J := by
      obtain ⟨u, hu, w, hw, e⟩ := (DoubleCoset.eq J J (x i) (x j)).1 hij
      exact mem_doubleCoset.2 ⟨u, hu, w, hw, e⟩
    exact Set.disjoint_left.1 (hdisj hne) hj (mem_doubleCoset_self J J (x j))
  have hcls : ∀ i, Quotient.out (DoubleCoset.mk J J (x i)) ∈ doubleCoset (x i) (J : Set G) J := by
    intro i
    obtain ⟨u, w, hu, hw, e⟩ := DoubleCoset.mk_out_eq_mul J J (x i)
    exact mem_doubleCoset.2 ⟨u, hu, w, hw, e⟩
  have hzero : ∀ c ∉ Set.range (fun i => DoubleCoset.mk J J (x i)),
      (m.real (doubleCoset (Quotient.out c) (J : Set G) J) : ℂ) * F (Quotient.out c) = 0 := by
    intro c hc
    by_contra h
    obtain ⟨i, hi⟩ := hsupp _ (right_ne_zero_of_mul h)
    refine hc ⟨i, ?_⟩
    show DoubleCoset.mk J J (x i) = c
    rw [← DoubleCoset.out_eq' J J c]
    exact (DoubleCoset.mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hi)).symm
  refine (hinj.hasSum_iff hzero).1 ?_
  convert hsumI using 1
  funext i
  show (m.real (doubleCoset (Quotient.out (DoubleCoset.mk J J (x i))) (J : Set G) J) : ℂ) *
      F (Quotient.out (DoubleCoset.mk J J (x i))) = _
  rw [doubleCoset_eq_of_mem (hcls i), hconst (x i) _ (hcls i)]

end GlobalTheory.TwistedOperatorMainTheorem
end

