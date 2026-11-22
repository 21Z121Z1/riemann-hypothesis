import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSubMemPow
section
namespace GlobalTheory.IntSubMemPow

theorem exists_int_sub_mem {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (P : Ideal R)
    (hP : P ≠ ⊤) (hc : Nat.card (R ⧸ P) = p) (a : R) : ∃ m : ℤ, a - (m : R) ∈ P := by
  have : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  have : Finite (R ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)

  have hord : addOrderOf (1 : R ⧸ P) = p := by
    have hdvd : addOrderOf (1 : R ⧸ P) ∣ p := hc ▸ addOrderOf_dvd_natCard 1
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) one_ne_zero
    · exact h1

  have htop : AddSubgroup.zmultiples (1 : R ⧸ P) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hc]
  have hmem : Ideal.Quotient.mk P a ∈ AddSubgroup.zmultiples (1 : R ⧸ P) := by
    rw [htop]; exact AddSubgroup.mem_top _
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine ⟨m, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, ← hm, zsmul_one, sub_self]

theorem span_sup_sq_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R)
    (hP : P.IsMaximal) (h0 : P ≠ ⊥) (x : R) (hx : x ∈ P) (hx2 : x ∉ P ^ 2) :
    Ideal.span {x} ⊔ P ^ 2 = P := by
  have hprime : Prime P := Ideal.prime_of_isPrime h0 hP.isPrime
  have hle : Ideal.span {x} ⊔ P ^ 2 ≤ P :=
    sup_le ((Ideal.span_singleton_le_iff_mem P).mpr hx) (Ideal.pow_le_self two_ne_zero)

  have hdvd : Ideal.span {x} ⊔ P ^ 2 ∣ P ^ 2 := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hprime 2).mp hdvd
  rw [associated_iff_eq] at hassoc
  interval_cases i
  · exfalso
    rw [pow_zero, Ideal.one_eq_top] at hassoc
    exact hP.ne_top (top_le_iff.mp (hassoc ▸ hle))
  · simpa using hassoc
  · exfalso
    exact hx2 (hassoc ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))

private lemma pow_le_span_pow_sup_pow_succ {R : Type} [CommRing R] (P : Ideal R) (x : R) (hx : x ∈ P)
    (h : Ideal.span {x} ⊔ P ^ 2 = P) (k : ℕ) :
    P ^ k ≤ Ideal.span {x ^ k} ⊔ P ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun r hr s hs => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (ih hr)
    have hs' := hs
    rw [← h] at hs'
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hs'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hd
    have hsplit : (c * x ^ k + b) * (c' * x + e) =
        (c * c') * x ^ (k + 1) + (c * (x ^ k * e) + b * (c' * x + e)) := by ring
    rw [hsplit]
    refine Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) ?_
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) ?_
    · have : x ^ k * e ∈ P ^ k * P ^ 2 := Ideal.mul_mem_mul (Ideal.pow_mem_pow hx k) he
      rwa [← pow_add] at this
    · have : b * (c' * x + e) ∈ P ^ (k + 1) * P := Ideal.mul_mem_mul hb hs
      rwa [← pow_succ] at this

theorem exists_sub_mul_pow_mem {R : Type} [CommRing R] (P : Ideal R) (x : R) (hx : x ∈ P)
    (h : Ideal.span {x} ⊔ P ^ 2 = P) (k : ℕ) :
    ∀ y ∈ P ^ k, ∃ c : R, y - c * x ^ k ∈ P ^ (k + 1) := by
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (pow_le_span_pow_sup_pow_succ P x hx h k hy)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  exact ⟨c, by simpa using hb⟩

theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : Nat.Prime p)
    (P : Ideal (NumberField.RingOfIntegers E)) (hP : Ideal.IsMaximal P)
    (hpP : (p : NumberField.RingOfIntegers E) ∈ P) (hN : Ideal.absNorm P = p)
    (hp2 : (p : NumberField.RingOfIntegers E) ∉ P ^ (2 : ℕ)) (k : ℕ)
    (a : NumberField.RingOfIntegers E) :
    ∃ m : ℤ, a - (m : NumberField.RingOfIntegers E) ∈ P ^ k := by
  have h0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN
    exact hp.ne_zero hN.symm
  have hcard : Nat.card (NumberField.RingOfIntegers E ⧸ P) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hgen : Ideal.span {(p : NumberField.RingOfIntegers E)} ⊔ P ^ 2 = P := span_sup_sq_eq P hP h0 _ hpP hp2
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih

    obtain ⟨c, hc⟩ := exists_sub_mul_pow_mem P _ hpP hgen k _ hm
    obtain ⟨n, hn⟩ := exists_int_sub_mem hp P hP.ne_top hcard c
    refine ⟨m + n * (p : ℤ) ^ k, ?_⟩
    have hrest : (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k ∈ P ^ (k + 1) := by
      have : (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k ∈ P * P ^ k :=
        Ideal.mul_mem_mul hn (Ideal.pow_mem_pow hpP k)
      rwa [← pow_succ'] at this
    have heq : a - ((m + n * (p : ℤ) ^ k : ℤ) : NumberField.RingOfIntegers E) =
        (a - (m : NumberField.RingOfIntegers E) - c * (p : NumberField.RingOfIntegers E) ^ k) + (c - (n : NumberField.RingOfIntegers E)) * (p : NumberField.RingOfIntegers E) ^ k := by
      push_cast; ring
    rw [heq]
    exact Ideal.add_mem _ hc hrest

end GlobalTheory.IntSubMemPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricIntertwinerOfMatrixCoeffEq
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem inner_translate_translate_of_norm {G : Type} [Group G] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖) (w : H)
    (g h : G) : ⟪σ g w, σ h w⟫_ℂ = ⟪w, σ (g⁻¹ * h) w⟫_ℂ := by
  have hmul : σ h w = σ g (σ (g⁻¹ * h) w) := by
    show σ h w = (σ g * σ (g⁻¹ * h)) w
    rw [← map_mul, mul_inv_cancel_left]
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }
  rw [hmul]
  exact T.inner_map_map w (σ (g⁻¹ * h) w)

theorem exists_isometric_intertwiner_of_matrixCoeff_eq :
    ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (Hp : Type) [NormedAddCommGroup Hp]
      [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)),
      (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ g x, ‖π g x‖ = ‖x‖) → ∀ (w : H) (v : Hp),
      (∀ y : H, (∀ g, ⟪y, σ g w⟫_ℂ = 0) → y = 0) → (∀ g, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) →
      ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by
  intro G _ H _ _ _ σ Hp _ _ _ π hσ hπ w v hcyc hvw

  obtain ⟨A, hA⟩ : ∃ A : (G →₀ ℂ) →ₗ[ℂ] H, A = Finsupp.linearCombination ℂ (fun g => σ g w) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (G →₀ ℂ) →ₗ[ℂ] Hp, B = Finsupp.linearCombination ℂ (fun g => π g v) :=
    ⟨_, rfl⟩

  have hkey : ∀ g h : G, ⟪π g v, π h v⟫_ℂ = ⟪σ g w, σ h w⟫_ℂ := by
    intro g h
    rw [inner_translate_translate_of_norm π hπ, inner_translate_translate_of_norm σ hσ, hvw]
  have hinner : ∀ c d, ⟪B c, B d⟫_ℂ = ⟪A c, A d⟫_ℂ := by
    intro c d
    rw [hA, hB]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hkey]
  have hnorm : ∀ c, ‖B c‖ = ‖A c‖ := by
    intro c
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (A c), hinner]
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]

  obtain ⟨F, hF⟩ : ∃ F : LinearMap.range A →ₗ[ℂ] Hp,
      ∀ c, F ⟨A c, LinearMap.mem_range_self A c⟩ = B c :=
    ⟨(LinearMap.ker A).liftQ B hker ∘ₗ A.quotKerEquivRange.symm.toLinearMap, fun c => by simp⟩
  have hFn : ∀ y, ‖F y‖ = ‖y‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hF, hnorm]
    rfl
  let F' : LinearMap.range A →ₗᵢ[ℂ] Hp := { toLinearMap := F, norm_map' := hFn }

  have hclos : (LinearMap.range A).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    refine hcyc y fun g => inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp hy _ ?_)
    exact ⟨Finsupp.single g 1, by simp [hA]⟩
  have hdense : DenseRange (LinearMap.range A).subtypeL :=
    denseRange_subtype_val.mpr (Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos)
  have huni : IsUniformInducing (LinearMap.range A).subtypeL :=
    (LinearMap.range A).subtypeₗᵢ.isometry.isUniformInducing

  obtain ⟨X, hXdef⟩ : ∃ X : H →L[ℂ] Hp, X = F'.toContinuousLinearMap.extend (LinearMap.range A).subtypeL :=
    ⟨_, rfl⟩
  have hX : ∀ c, X (A c) = B c := fun c => by
    rw [hXdef]
    exact (ContinuousLinearMap.extend_eq F'.toContinuousLinearMap hdense huni
      ⟨A c, LinearMap.mem_range_self A c⟩).trans (hF c)
  have hXn : ∀ u, ‖X u‖ = ‖u‖ := by
    intro u
    refine hdense.induction_on (p := fun u => ‖X u‖ = ‖u‖) u
      (isClosed_eq (continuous_norm.comp X.continuous) continuous_norm) ?_
    rintro ⟨_, c, rfl⟩
    show ‖X (A c)‖ = ‖A c‖
    rw [hX, hnorm]

  have hshA : ∀ g c, σ g (A c) = A (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    rw [hA, Finsupp.linearCombination_mapDomain]
    change (σ g : H →ₗ[ℂ] H) _ = _
    rw [Finsupp.apply_linearCombination]
    refine congrArg (fun f => Finsupp.linearCombination ℂ f c) ?_
    funext h
    simp [map_mul]
  have hshB : ∀ g c, π g (B c) = B (Finsupp.mapDomain (g * ·) c) := by
    intro g c
    rw [hB, Finsupp.linearCombination_mapDomain]
    change (π g : Hp →ₗ[ℂ] Hp) _ = _
    rw [Finsupp.apply_linearCombination]
    refine congrArg (fun f => Finsupp.linearCombination ℂ f c) ?_
    funext h
    simp [map_mul]
  have hXi : ∀ g u, X (σ g u) = π g (X u) := by
    intro g u
    refine hdense.induction_on (p := fun u => X (σ g u) = π g (X u)) u
      (isClosed_eq (X.continuous.comp (σ g).continuous) ((π g).continuous.comp X.continuous)) ?_
    rintro ⟨_, c, rfl⟩
    show X (σ g (A c)) = π g (X (A c))
    rw [hshA, hX, hX, hshB]
  have hw : A (Finsupp.single 1 1) = w := by simp [hA]
  have hv : B (Finsupp.single 1 1) = v := by simp [hB]
  refine ⟨{ toLinearMap := (X : H →ₗ[ℂ] Hp), norm_map' := hXn }, ?_, fun g u => hXi g u⟩
  show X w = v
  rw [← hw, hX, hv]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMapMulRightEqSmul
section
open MeasureTheory

namespace GlobalTheory.IwasawaShape

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableInv G] in
theorem lintegral_mul_left_of_map {ρ : Measure G} {p : G} (h : ρ.map (fun g => p * g) = ρ) (f : G → ENNReal)
    (hf : Measurable f) : ∫⁻ x, f (p * x) ∂ρ = ∫⁻ x, f x ∂ρ := by
  have e := lintegral_map (μ := ρ) hf (measurable_const_mul p)
  rw [h] at e
  exact e.symm

theorem exists_map_mul_right_eq_smul (P : Subgroup G) (hP : MeasurableSet (P : Set G)) (ρ : Measure G)
    [SigmaFinite ρ] (h0 : ρ (P : Set G)ᶜ = 0) (hinv : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ)
    (T : Set G) (hT : MeasurableSet T) (hT0 : ρ T ≠ 0) (hT1 : ρ T ≠ ⊤) (l : G) (hl : l ∈ P) :
    ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ρ.map (fun g => g * l) = D • ρ := by
  classical
  have e : MeasurableEmbedding (Subtype.val : P → G) := MeasurableEmbedding.subtype_coe hP
  have : MeasurableMul₂ P := ⟨e.measurable_comp_iff.1
    ((measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd))⟩
  have : MeasurableInv P := ⟨e.measurable_comp_iff.1 measurable_subtype_coe.inv⟩
  set ρ' : Measure P := ρ.comap Subtype.val with hρ'
  have hmap : ρ'.map Subtype.val = ρ := by
    rw [hρ', e.map_comap, Subtype.range_coe_subtype, Measure.restrict_eq_self_of_ae_mem]
    exact ae_iff.2 h0
  have inj : ∀ α β : Measure P, α.map Subtype.val = β.map Subtype.val → α = β := fun α β h => by
    rw [← e.comap_map α, ← e.comap_map β, h]
  have : SigmaFinite ρ' :=
    SigmaFinite.of_map ρ' measurable_subtype_coe.aemeasurable (by rw [hmap]; infer_instance)
  have : ρ'.IsMulLeftInvariant := ⟨fun s => inj _ _ (by
    rw [Measure.map_map measurable_subtype_coe (measurable_const_mul s)]
    have hc : (Subtype.val ∘ fun x : P => s * x) = (fun g : G => (s : G) * g) ∘ Subtype.val := rfl
    rw [hc, ← Measure.map_map (measurable_const_mul _) measurable_subtype_coe, hmap, hinv s s.2])⟩
  let l' : P := ⟨l, hl⟩
  set ν' : Measure P := ρ'.map (fun x => x * l') with hν'
  have : ν'.IsMulLeftInvariant := ⟨fun s => by
    rw [hν', Measure.map_map (measurable_const_mul s) (measurable_mul_const l')]
    have hc : ((fun x : P => s * x) ∘ fun x => x * l') = (fun x => x * l') ∘ (fun x => s * x) := by
      funext x; simp [Function.comp, mul_assoc]
    rw [hc, ← Measure.map_map (measurable_mul_const l') (measurable_const_mul s), map_mul_left_eq_self]⟩
  have : SigmaFinite ν' := SigmaFinite.of_map ν' (measurable_mul_const l'⁻¹).aemeasurable (by
    rw [hν', Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
    have hc : ((fun x : P => x * l'⁻¹) ∘ fun x => x * l') = id := by funext x; simp
    rw [hc, Measure.map_id]; infer_instance)
  have hρT' : ρ' (Subtype.val ⁻¹' T) = ρ T := by
    rw [hρ', e.comap_apply, Set.image_preimage_eq_inter_range]
    exact measure_inter_conull (by rw [Subtype.range_coe_subtype]; exact h0)
  have hEq := measure_eq_div_smul ν' ρ' (s := Subtype.val ⁻¹' T) (by rw [hρT']; exact hT0)
    (by rw [hρT']; exact hT1)
  set D := ν' (Subtype.val ⁻¹' T) / ρ' (Subtype.val ⁻¹' T) with hD
  have hmapD : ρ.map (fun g => g * l) = D • ρ := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_map (measurable_mul_const l) measurable_subtype_coe]
    have hc : ((fun g : G => g * l) ∘ Subtype.val) = Subtype.val ∘ (fun x : P => x * l') := rfl
    rw [hc, ← Measure.map_map measurable_subtype_coe (measurable_mul_const l'), ← hν', hEq,
      Measure.map_smul, hmap]
  have huniv : (ρ.map fun g => g * l) Set.univ ≠ 0 := by
    rw [Measure.map_apply (measurable_mul_const l) MeasurableSet.univ, Set.preimage_univ]
    exact fun h => hT0 (measure_mono_null (Set.subset_univ _) h)
  have hD0 : D ≠ 0 := by
    intro h
    apply huniv
    rw [hmapD, h, zero_smul, Measure.coe_zero, Pi.zero_apply]
  have hD1 : D ≠ ⊤ := by
    intro h
    have : SigmaFinite (ρ.map fun g => g * l) :=
      SigmaFinite.of_map _ (measurable_mul_const l⁻¹).aemeasurable (by
        rw [Measure.map_map (measurable_mul_const _) (measurable_mul_const _)]
        have hc : ((fun g : G => g * l⁻¹) ∘ fun g => g * l) = id := by funext x; simp
        rw [hc, Measure.map_id]; infer_instance)
    obtain ⟨n, hn⟩ : ∃ n, (ρ.map fun g => g * l) (spanningSets (ρ.map fun g => g * l) n) ≠ 0 := by
      by_contra hne
      push Not at hne
      apply huniv
      rw [← iUnion_spanningSets (ρ.map fun g => g * l)]
      exact measure_iUnion_null hne
    have hlt := measure_spanningSets_lt_top (ρ.map fun g => g * l) n
    set Sn := spanningSets (ρ.map fun g => g * l) n
    rw [hmapD, Measure.smul_apply, smul_eq_mul, h] at hn hlt
    rcases eq_or_ne (ρ Sn) 0 with h' | h'
    · exact hn (by rw [h', mul_zero])
    · rw [ENNReal.top_mul h'] at hlt
      exact lt_irrefl _ hlt
  exact ⟨D, hD0, hD1, hmapD⟩

theorem exists_lintegral_eq_mul (μ ρ κ : Measure G) [SigmaFinite μ] [SFinite ρ] [IsProbabilityMeasure κ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (hμ : μ ≠ 0) (P K : Set G)
    (hKl : ∀ k ∈ K, κ.map (fun g => k * g) = κ) (hPl : ∀ p ∈ P, ρ.map (fun g => p * g) = ρ)
    (hPr : ∀ p ∈ P, ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ρ.map (fun g => g * p) = D • ρ)
    (hdec : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) (T : Set G) (hT : MeasurableSet T)
    (hTK : ∀ k ∈ K, ∀ g, k⁻¹ * g ∈ T ↔ g ∈ T) (hT0 : ρ T ≠ 0) (hT1 : ρ T ≠ ⊤) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂μ = c * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ := by
  classical
  have hind : Measurable (T.indicator (1 : G → ENNReal)) := measurable_one.indicator hT
  have ind_ne_top : ∀ x, T.indicator (1 : G → ENNReal) x ≠ ⊤ := fun x => by
    by_cases hx : x ∈ T <;> simp [Set.indicator_apply, hx]
  have hLm : ∀ φ : G → ENNReal, Measurable φ →
      Measurable fun h => T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ :=
    fun φ hφ => (hind.comp measurable_inv).mul
      ((hφ.comp (by fun_prop : Measurable fun y : (G × G) × G => y.1.2 * y.1.1 * y.2)).lintegral_prod_right').lintegral_prod_right'

  have key : ∀ h : G, ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ = D * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ := by
    intro h
    obtain ⟨p0, hp0, k0, hk0, rfl⟩ := hdec h
    obtain ⟨D, hD0, hDt, hD⟩ := hPr p0 hp0
    refine ⟨D, hD0, hDt, fun φ hφ => ?_⟩
    have hF : Measurable fun x => ∫⁻ k, φ (x * k) ∂κ := (hφ.comp measurable_mul).lintegral_prod_right'
    have e1 : ∀ q, ∫⁻ k, φ (q * (p0 * k0) * k) ∂κ = ∫⁻ k, φ (q * p0 * k) ∂κ := by
      intro q
      have := lintegral_mul_left_of_map (hKl k0 hk0) (fun k => φ (q * p0 * k))
        (hφ.comp (measurable_const_mul _))
      simpa only [mul_assoc] using this
    simp_rw [e1]
    have := lintegral_map (μ := ρ) hF (measurable_mul_const p0)
    rw [hD, lintegral_smul_measure, smul_eq_mul] at this
    exact this.symm

  have mix : ∀ φ : G → ENNReal, Measurable φ →
      ρ T * ∫⁻ g, φ g ∂μ = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ ∂μ := by
    intro φ hφ
    have s1 : ∫⁻ g, φ g ∂μ = ∫⁻ g, ∫⁻ k, φ (g * k) ∂κ ∂μ := by
      rw [lintegral_lintegral_swap (f := fun g k => φ (g * k)) (by exact (hφ.comp measurable_mul).aemeasurable)]
      simp_rw [lintegral_mul_right_eq_self]
      rw [lintegral_const, measure_univ, mul_one]
    have s2 : ∀ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) ∂ρ = ρ T := by
      intro g
      obtain ⟨p0, hp0, k0, hk0, rfl⟩ := hdec g
      have e : ∀ q, T.indicator (1 : G → ENNReal) ((p0 * k0)⁻¹ * q) = T.indicator 1 (p0⁻¹ * q) := by
        intro q
        have hm : (p0 * k0)⁻¹ * q ∈ T ↔ p0⁻¹ * q ∈ T := by
          rw [mul_inv_rev, mul_assoc]; exact hTK k0 hk0 _
        simp only [Set.indicator_apply, hm, Pi.one_apply]
      simp_rw [e]
      have := lintegral_mul_left_of_map (hPl p0 hp0) (fun x => T.indicator (1 : G → ENNReal) (p0⁻¹ * x))
        (hind.comp (measurable_const_mul _))
      simp only [inv_mul_cancel_left] at this
      rw [← this, lintegral_indicator_one hT]
    have hW1 : ∫⁻ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ ∂μ
        = ρ T * ∫⁻ g, φ g ∂μ := by
      have e : ∀ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ
          = ρ T * ∫⁻ k, φ (g * k) ∂κ := by
        intro g
        exact (lintegral_mul_const _ (hind.comp (measurable_const_mul g⁻¹))).trans (congrArg (· * _) (s2 g))
      simp_rw [e]
      rw [lintegral_const_mul' _ _ hT1, ← s1]
    have hmF : Measurable fun x : G × G =>
        T.indicator (1 : G → ENNReal) (x.1⁻¹ * x.2) * ∫⁻ k, φ (x.1 * k) ∂κ :=
      (hind.comp (measurable_fst.inv.mul measurable_snd)).mul
        (((hφ.comp measurable_mul).lintegral_prod_right').comp measurable_fst)
    have hmG : Measurable fun x : G × G =>
        T.indicator (1 : G → ENNReal) x.2⁻¹ * ∫⁻ k, φ (x.1 * x.2 * k) ∂κ :=
      (hind.comp measurable_snd.inv).mul
        ((hφ.comp (by fun_prop : Measurable fun y : (G × G) × G => y.1.1 * y.1.2 * y.2)).lintegral_prod_right')
    have hW2 : ∫⁻ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ ∂μ
        = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ ∂μ := by
      rw [lintegral_lintegral_swap (f := fun g q => T.indicator (1 : G → ENNReal) (g⁻¹ * q) *
        ∫⁻ k, φ (g * k) ∂κ) (by exact hmF.aemeasurable)]
      have e : ∀ q, ∫⁻ g, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂μ
          = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ k, φ (q * h * k) ∂κ ∂μ := by
        intro q
        refine (lintegral_mul_left_eq_self (μ := μ) (fun g => T.indicator (1 : G → ENNReal) (g⁻¹ * q) *
          ∫⁻ k, φ (g * k) ∂κ) q).symm.trans ?_
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      simp_rw [e]
      rw [lintegral_lintegral_swap (f := fun q h => T.indicator (1 : G → ENNReal) h⁻¹ *
        ∫⁻ k, φ (q * h * k) ∂κ) (by exact hmG.aemeasurable)]
      exact lintegral_congr fun h => lintegral_const_mul' _ _ (ind_ne_top _)
    rw [← hW1, hW2]

  obtain ⟨S, hS, hS0, hS1⟩ : ∃ S, MeasurableSet S ∧ μ S ≠ 0 ∧ μ S ≠ ⊤ := by
    by_contra hne
    push Not at hne
    apply hμ
    have hz : ∀ n, μ (spanningSets μ n) = 0 := fun n => by
      by_contra hn
      exact (measure_spanningSets_lt_top μ n).ne (hne _ (measurableSet_spanningSets μ n) hn)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
    exact measure_iUnion_null hz
  have hφ0 : Measurable (S.indicator (1 : G → ENNReal)) := measurable_one.indicator hS
  have hμS : ∫⁻ g, S.indicator (1 : G → ENNReal) g ∂μ = μ S := lintegral_indicator_one hS
  have mix0 := mix _ hφ0
  rw [hμS] at mix0
  have hL0 : ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ ≠ 0 := by
    intro h0
    have : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, S.indicator (1 : G → ENNReal) (q * h * k) ∂κ ∂ρ ∂μ = 0 := by
      refine (lintegral_congr fun h => ?_).trans lintegral_zero
      obtain ⟨D, -, -, hD⟩ := key h
      rw [hD _ hφ0, h0, mul_zero, mul_zero]
    rw [this] at mix0
    exact mul_ne_zero hT0 hS0 mix0
  have hLt : ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ ≠ ⊤ := by
    intro ht
    have : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, S.indicator (1 : G → ENNReal) (q * h * k) ∂κ ∂ρ ∂μ
        = (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) * ⊤ := by
      rw [← (lintegral_mul_const ⊤ (hind.comp measurable_inv) : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ⊤ ∂μ = (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) * ⊤)]
      refine lintegral_congr fun h => ?_
      obtain ⟨D, hD0, -, hD⟩ := key h
      rw [hD _ hφ0, ht, ENNReal.mul_top hD0]
    rw [this] at mix0
    rcases eq_or_ne (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) 0 with hz | hz
    · rw [hz, zero_mul] at mix0
      exact mul_ne_zero hT0 hS0 mix0
    · rw [ENNReal.mul_top hz] at mix0
      exact ENNReal.mul_ne_top hT1 hS1 mix0
  refine ⟨μ S / ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ,
    (ENNReal.div_pos_iff.2 ⟨hS0, hLt⟩).ne', ENNReal.div_ne_top hS1 hL0, fun φ hφ => ?_⟩
  have E : ρ T * ((∫⁻ g, φ g ∂μ) * ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ)
      = ρ T * (μ S * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ) := by
    rw [← mul_assoc]
    rw [mix _ hφ]
    rw [← lintegral_mul_const _ (hLm _ hφ)]
    rw [← mul_assoc]
    rw [mix0]
    rw [← lintegral_mul_const _ (hLm _ hφ0)]
    refine lintegral_congr fun h => ?_
    obtain ⟨D, -, -, hD⟩ := key h
    rw [hD _ hφ, hD _ hφ0]
    ring
  have E' := (ENNReal.mul_right_inj hT0 hT1).1 E
  rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  exact (ENNReal.eq_div_iff hL0 hLt).2 (by rw [mul_comm]; exact E')

end GlobalTheory.IwasawaShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPowSmulMem
section
namespace GlobalTheory.PowSmulMem

theorem exists_pow_smul_mem {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V]
    {O : Subring E} {p : E} (hp : p ∈ O) (hO : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ' : Submodule O V) (hsp : Submodule.span E (Λ' : Set V) = ⊤) (v : V) :
    ∃ a : ℕ, ∀ b, a ≤ b → p ^ b • v ∈ Λ' := by
  have hv : v ∈ Submodule.span E (Λ' : Set V) := hsp ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun b _ => ?_⟩
    exact Λ'.smul_mem (⟨p ^ b, O.pow_mem hp b⟩ : O) hx
  | zero => exact ⟨0, fun b _ => by rw [smul_zero]; exact Λ'.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    refine ⟨max a c, fun b hb => ?_⟩
    rw [smul_add]
    exact Λ'.add_mem (ha b (le_trans (le_max_left _ _) hb)) (hc b (le_trans (le_max_right _ _) hb))
  | smul e x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hO e
    refine ⟨a + c, fun b hb => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
    have h : p ^ (a + c + d) • e • x = (p ^ c * e) • (p ^ (a + d) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [h]
    exact Λ'.smul_mem (⟨p ^ c * e, hc⟩ : O) (ha _ (Nat.le_add_right _ _))

theorem main : ∀ {E : Type} [inst : CommRing E] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module E V] {O : Subring E} {p : E}, p ∈ O → (∀ (e : E), ∃ (a : ℕ), p ^ a * e ∈ O) → ∀ (Λ Λ' : Submodule (↥O) V), Submodule.FG Λ → Submodule.span E (↑Λ' : Set V) = ⊤ → ∃ (a : ℕ), ∀ v ∈ Λ, p ^ a • v ∈ Λ' := by
  intro E _ V _ _ O p hp hO Λ Λ' hfg hsp
  classical
  obtain ⟨s, rfl⟩ := hfg
  choose f hf using exists_pow_smul_mem hp hO Λ' hsp
  refine ⟨s.sup f, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx => exact hf x _ (Finset.le_sup (Finset.mem_coe.mp hx))
  | zero => rw [smul_zero]; exact Λ'.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Λ'.add_mem hx hy
  | smul e x _ hx =>
    have h : p ^ s.sup f • e • x = e • (p ^ s.sup f • x) := by
      change p ^ s.sup f • (e : E) • x = (e : E) • (p ^ s.sup f • x)
      exact smul_comm _ _ _
    rw [h]
    exact Λ'.smul_mem e hx

end GlobalTheory.PowSmulMem
end

