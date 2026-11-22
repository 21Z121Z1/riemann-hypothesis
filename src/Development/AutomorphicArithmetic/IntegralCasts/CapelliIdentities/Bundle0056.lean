import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ReprMem
section
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.ReprMem.repr_mem :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
    [inst_2 : Algebra F E] (t : E) (c : F),
    t ^ (2 : ℕ) = (Algebra.algebraMap F E : F → E) c →
      ∀ x ∈ F⟮t⟯, ∃ (a : F) (b : F), x = (Algebra.algebraMap F E : F → E) a + (Algebra.algebraMap F E : F → E) b * t := by
  intro F E _ _ _ t c h x hx
  have hint : IsIntegral F t := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [h]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin F {t} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a * a' + b * b' * c, a * b' + b * a', ?_⟩
    simp only [map_add, map_mul]
    rw [← h]
    ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Reps
section
theorem UpperTheory.Reformulated.B.Qh68.reps.{u_1} :
    ∀ {α : Type u_1} (r : α → α → Prop),
    Equivalence r → ∀ (A : Finset α), ∃ T ⊆ A, (∀ t ∈ T, ∀ t' ∈ T, r t t' → t = t') ∧ ∀ a ∈ A, ∃ t ∈ T, r a t := by
  intro α r hr A
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | insert a s _ ih =>
    obtain ⟨T, hTs, hinj, hcov⟩ := ih
    by_cases h : ∃ t ∈ T, r a t
    · refine ⟨T, hTs.trans (Finset.subset_insert a s), hinj, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact h
      · exact hcov b hb
    · refine ⟨insert a T, Finset.insert_subset_insert a hTs, ?_, ?_⟩
      · intro t ht t' ht' htt
        rcases Finset.mem_insert.mp ht with h1 | h1
        · rcases Finset.mem_insert.mp ht' with h2 | h2
          · rw [h1, h2]
          · exact absurd ⟨t', h2, h1 ▸ htt⟩ h
        · rcases Finset.mem_insert.mp ht' with h2 | h2
          · exact absurd ⟨t, h1, h2 ▸ hr.symm htt⟩ h
          · exact hinj t h1 t' h2 htt
      · intro b hb
        rcases Finset.mem_insert.mp hb with h1 | h1
        · exact ⟨b, Finset.mem_insert.mpr (Or.inl h1), hr.refl b⟩
        · obtain ⟨t, ht, hbt⟩ := hcov b h1
          exact ⟨t, Finset.mem_insert_of_mem ht, hbt⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RepsProd
section
open scoped Classical

noncomputable def UpperTheory.Reformulated.B.P9.IsReps.{u_1} :
    {V : Type u_1} → [inst : AddCommGroup V] → AddSubgroup V → AddSubgroup V → Finset V → Prop :=
    fun {V : Type u_1} [AddCommGroup V] (Λ₁ Λ₂ : AddSubgroup V) (S : Finset V) ↦
      (∀ x ∈ S, x ∈ Λ₂) ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ Λ₁ → x = y) ∧ ∀ y ∈ Λ₂, ∃ x ∈ S, y - x ∈ Λ₁

theorem UpperTheory.Reformulated.B.P9.aux2 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a b : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} →
        b ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} → a + b ∈ Λ ∧ (p : V → V) (a + b) = a + b := by
  intro V _ p Λ a b ha hb
  exact ⟨Λ.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2]⟩

theorem UpperTheory.Reformulated.B.P9.aux3 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V), (0 : V) ∈ Λ ∧ (p : V → V) (0 : V) = (0 : V) := by
  intro V _ p Λ
  exact ⟨Λ.zero_mem, map_zero p⟩

theorem UpperTheory.Reformulated.B.P9.aux4 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} → -a ∈ Λ ∧ (p : V → V) (-a) = -a := by
  intro V _ p Λ a ha
  exact ⟨Λ.neg_mem ha.1, by rw [map_neg, ha.2]⟩

noncomputable def UpperTheory.Reformulated.B.P9.partP :
    {V : Type} → [inst : AddCommGroup V] → (V →+ V) → AddSubgroup V → AddSubgroup V :=
    fun {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) ↦
      { carrier := {x : V | x ∈ Λ ∧ (p : V → V) x = x}, add_mem' := @UpperTheory.Reformulated.B.P9.aux2 V inst p Λ,
        zero_mem' := UpperTheory.Reformulated.B.P9.aux3 p Λ, neg_mem' := @UpperTheory.Reformulated.B.P9.aux4 V inst p Λ : AddSubgroup V }

theorem UpperTheory.Reformulated.B.P9.aux6 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a b : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} →
        b ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} → a + b ∈ Λ ∧ (p : V → V) (a + b) = (0 : V) := by
  intro V _ p Λ a b ha hb
  exact ⟨Λ.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩

theorem UpperTheory.Reformulated.B.P9.aux7 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V), (0 : V) ∈ Λ ∧ (p : V → V) (0 : V) = (0 : V) := by
  intro V _ p Λ
  exact ⟨Λ.zero_mem, map_zero p⟩

theorem UpperTheory.Reformulated.B.P9.aux8 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} → -a ∈ Λ ∧ (p : V → V) (-a) = (0 : V) := by
  intro V _ p Λ a ha
  exact ⟨Λ.neg_mem ha.1, by rw [map_neg, ha.2, neg_zero]⟩

noncomputable def UpperTheory.Reformulated.B.P9.partQ :
    {V : Type} → [inst : AddCommGroup V] → (V →+ V) → AddSubgroup V → AddSubgroup V :=
    fun {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) ↦
      { carrier := {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)}, add_mem' := @UpperTheory.Reformulated.B.P9.aux6 V inst p Λ,
        zero_mem' := UpperTheory.Reformulated.B.P9.aux7 p Λ, neg_mem' := @UpperTheory.Reformulated.B.P9.aux8 V inst p Λ : AddSubgroup V }

theorem UpperTheory.Reformulated.B.P9.reps_prod :
    ∀ {V : Type} [inst : AddCommGroup V] [_root_.Module ℂ V] {M Λ : AddSubgroup V} (p : V →+ V),
      (∀ (x : V), (p : V → V) ((p : V → V) x) = (p : V → V) x) →
        (∀ x ∈ Λ, (p : V → V) x ∈ Λ) →
          (∀ x ∈ M, (p : V → V) x ∈ M) →
            ∀ {A B : Finset V},
              UpperTheory.Reformulated.B.P9.IsReps M (UpperTheory.Reformulated.B.P9.partP p Λ) A →
                UpperTheory.Reformulated.B.P9.IsReps M (UpperTheory.Reformulated.B.P9.partQ p Λ) B →
                  UpperTheory.Reformulated.B.P9.IsReps M Λ (Finset.image (fun (w : V × V) ↦ w.1 + w.2) (A ×ˢ B)) := by
  intro V _ _ M Λ p hpp hΛ hM A B hA hB
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hA1' : ∀ x ∈ A, x ∈ Λ ∧ p x = x := hA1
  have hB1' : ∀ x ∈ B, x ∈ Λ ∧ p x = 0 := hB1
  have hA3' : ∀ y, (y ∈ Λ ∧ p y = y) → ∃ x ∈ A, y - x ∈ M := hA3
  have hB3' : ∀ y, (y ∈ Λ ∧ p y = 0) → ∃ x ∈ B, y - x ∈ M := hB3
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨a, b⟩, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hw
    exact Λ.add_mem (hA1' a ha).1 (hB1' b hb).1
  · intro x hx y hy hxy
    obtain ⟨⟨a, b⟩, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hw
    obtain ⟨⟨a', b'⟩, hw', rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨ha', hb'⟩ := Finset.mem_product.1 hw'
    change a + b - (a' + b') ∈ M at hxy
    change a + b = a' + b'
    have h1 : p (a + b - (a' + b')) = a - a' := by
      rw [map_sub, map_add, map_add, (hA1' a ha).2, (hA1' a' ha').2, (hB1' b hb).2,
        (hB1' b' hb').2, add_zero, add_zero]
    have h2 : a = a' := hA2 a ha a' ha' (h1 ▸ hM _ hxy)
    have h3 : b = b' := by
      refine hB2 b hb b' hb' ?_
      rwa [h2, add_sub_add_left_eq_sub] at hxy
    rw [h2, h3]
  · intro y hy
    obtain ⟨a, ha, hya⟩ := hA3' (p y) ⟨hΛ y hy, hpp y⟩
    obtain ⟨b, hb, hyb⟩ := hB3' (y - p y)
      ⟨Λ.sub_mem hy (hΛ y hy), by rw [map_sub, hpp, sub_self]⟩
    refine ⟨a + b, Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, rfl⟩, ?_⟩
    have h : y - (a + b) = (p y - a) + (y - p y - b) := by abel
    rw [h]
    exact M.add_mem hya hyb
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ResidueHomNorm
section
theorem UpperTheory.residue_hom_norm :
    ∀ {O R Ω : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [NormedField Ω]
        [IsUltrametricDist Ω] [Algebra O Ω]
        (hres : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ IsLocalRing.maximalIdeal R)
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (hint : ∀ x : Ω, ‖x‖ ≤ 1 → IsIntegral O x)
        (y : R →ₐ[O] Ω),
        (∀ a, ‖y a‖ ≤ 1) ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
  intro O R Ω _ _ _ _ _ _ _ hres hO hint y
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
    intro m hmem
    by_contra hge
    have hge' : 1 ≤ ‖y m‖ := not_lt.mp hge
    have hne : y m ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hge'
      linarith
    have hu : ‖(y m)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hge'
    obtain ⟨p, hp, hev⟩ := hint _ hu
    have hrev : Polynomial.eval₂ (algebraMap O Ω) (y m) p.reverse = 0 := by
      haveI : Invertible (y m)⁻¹ := invertibleOfNonzero (inv_ne_zero hne)
      have h := Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) (y m)⁻¹ p
      rw [invOf_eq_inv, inv_inv, hev] at h
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (inv_ne_zero hne))
    have hq : y (Polynomial.aeval m p.reverse) = 0 := by
      rw [Polynomial.aeval_algHom_apply y m p.reverse |>.symm]
      simpa [Polynomial.aeval_def] using hrev
    have hdvd : m ∣ Polynomial.aeval m p.reverse - 1 := by
      have h := Polynomial.sub_dvd_eval_sub m 0 (p.reverse.map (algebraMap O R))
      have h0 : (p.reverse.map (algebraMap O R)).eval 0 = 1 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
          Polynomial.coeff_zero_reverse, hp.leadingCoeff, map_one]
      rw [h0, sub_zero, Polynomial.eval_map_algebraMap] at h
      exact h
    have hunit : IsUnit (Polynomial.aeval m p.reverse : R) := by
      by_contra hnu
      have h1 : (Polynomial.aeval m p.reverse : R) ∈ IsLocalRing.maximalIdeal R :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have h2 : Polynomial.aeval m p.reverse - 1 ∈ IsLocalRing.maximalIdeal R :=
        Ideal.mem_of_dvd _ hdvd hmem
      have h3 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        have := Ideal.sub_mem _ h1 h2
        simpa using this
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3
    have := hunit.map y
    rw [hq] at this
    exact not_isUnit_zero this
  refine ⟨fun x => ?_, hm⟩
  obtain ⟨a, ha⟩ := hres x
  have hx : y x = algebraMap O Ω a + y (x - algebraMap O R a) := by
    rw [map_sub, AlgHom.commutes]
    ring
  rw [hx]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (hO a) (hm _ ha).le)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RestrictedProductMeasureSet
section
open MeasureTheory in
private theorem UpperTheory.restricted_product_measure_set
    (V G Gi : Type) (Gv : V → Type) [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
    (q : G → Gi) (p : ∀ v, G → Gv v) (K : ∀ v, Set (Gv v))
    (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v))
    [SigmaFinite μi] [∀ v, SigmaFinite (m v)]
    (hq : Measurable q) (hp : ∀ v, Measurable (p v)) (hK : ∀ v, MeasurableSet (K v))
    (h1 : ∀ v, m v (K v) = 1) (A : Set Gi) (hA : MeasurableSet A)
    (S : Finset V) (a : NNReal)
    (h : Measure.map (fun g => (q g, fun v : S => p v g)) (μ.restrict {g | ∀ v ∉ S, p v g ∈ K v}) =
      a • μi.prod (Measure.pi fun v : S => m v)) :
    μ {g | q g ∈ A ∧ ∀ v, p v g ∈ K v} = (a : ENNReal) * μi A := by
  have hf : Measurable (fun g => (q g, fun v : S => p v g)) :=
    hq.prodMk (measurable_pi_lambda _ fun v => hp v)
  have hB : MeasurableSet (A ×ˢ (Set.univ.pi fun v : S => K v)) :=
    hA.prod (MeasurableSet.univ_pi fun v => hK v)
  have h2 := congrArg (fun ν => ν (A ×ˢ (Set.univ.pi fun v : S => K v))) h
  simp only [Measure.map_apply hf hB, Measure.restrict_apply (hf hB)] at h2
  rw [Measure.coe_nnreal_smul_apply, Measure.prod_prod, Measure.pi_pi] at h2
  simp only [h1, Finset.prod_const_one, mul_one] at h2
  rw [← h2]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, true_imp_iff]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨⟨ha, fun v => hb v⟩, fun v _ => hb v⟩
  · rintro ⟨⟨ha, hb⟩, hc⟩
    refine ⟨ha, fun v => ?_⟩
    by_cases hv : v ∈ S
    · exact hb ⟨v, hv⟩
    · exact hc v hv

theorem UpperTheory.restricted_product_measure :
    ∀ (V G Gi : Type) (Gv : V → Type) [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
        (q : G → Gi) (p : ∀ v, G → Gv v) (K : ∀ v, Set (Gv v))
        (μ : MeasureTheory.Measure G) (μi : MeasureTheory.Measure Gi) (m : ∀ v, MeasureTheory.Measure (Gv v))
        [MeasureTheory.SigmaFinite μi] [∀ v, MeasureTheory.SigmaFinite (m v)],
        Measurable q → (∀ v, Measurable (p v)) → (∀ v, MeasurableSet (K v)) → (∀ v, m v (K v) = 1) →
        (∃ A : Set Gi, MeasurableSet A ∧ μi A ≠ 0 ∧ μi A ≠ ⊤) →
        ∀ (S T : Finset V) (a b : NNReal),
          MeasureTheory.Measure.map (fun g => (q g, fun v : S => p v g)) (μ.restrict {g | ∀ v ∉ S, p v g ∈ K v}) =
            a • μi.prod (MeasureTheory.Measure.pi fun v : S => m v) →
          MeasureTheory.Measure.map (fun g => (q g, fun v : T => p v g)) (μ.restrict {g | ∀ v ∉ T, p v g ∈ K v}) =
            b • μi.prod (MeasureTheory.Measure.pi fun v : T => m v) →
          a = b := by
  intro V G Gi Gv _ _ _ q p K μ μi m _ _ hq hp hK h1 ⟨A, hA, h0, ht⟩ S T a b hS hT
  have e1 := UpperTheory.restricted_product_measure_set V G Gi Gv q p K μ μi m hq hp hK h1 A hA S a hS
  have e2 := UpperTheory.restricted_product_measure_set V G Gi Gv q p K μ μi m hq hp hK h1 A hA T b hT
  have e : (a : ENNReal) * μi A = (b : ENNReal) * μi A := e1.symm.trans e2
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 ht).1 e)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RieszRepresentationSesquilinear
section
theorem UpperTheory.Reformulated.B.Qh51.riesz_representation_sesquilinear :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] [FiniteDimensional ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ (a b : V), ((B : V → V →ₗ⋆[ℂ] ℂ) b : V → ℂ) a = Star.star (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) b)) →
      (∀ (a : V), a ≠ (0 : V) → (0 : ℝ) < (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) a).re) →
        ∀ (L : V →ₗ⋆[ℂ] ℂ), ∃ (u : V), ∀ (b : V), (L : V → ℂ) b = ((B : V → V →ₗ⋆[ℂ] ℂ) u : V → ℂ) b := by
  intro V _ _ _ B _ hpos L
  let e := Module.finBasis ℂ V
  let Φ : V →ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) :=
    { toFun := fun u i => B u (e i)
      map_add' := fun u v => by funext i; simp
      map_smul' := fun c u => by funext i; simp }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have h0 : B u = 0 := e.ext fun i => congrFun hu i
    by_contra hne
    have h := hpos u hne
    rw [h0] at h
    simp at h
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨u, hu⟩ := hsurj fun i => L (e i)
  have hL : L = B u := e.ext fun i => (congrFun hu i).symm
  exact ⟨u, fun b => by rw [hL]⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RightCosetSpaceCompact
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace.{u_1} :
    {G : Type u_1} → [inst : Group G] → Subgroup G → Type u_1 :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient (MulAction.orbitRel (↥Γ) G)

noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk.{u_1} :
    {G : Type u_1} → [inst : Group G] → (Γ : Subgroup G) → G → UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient.mk (MulAction.orbitRel (↥Γ) G)

theorem UpperTheory.Reformulated.B.RightCosetSpaceCompact.exists_isCompact_subset_mk_image.{u_1} :
    ∀ {G : Type u_1} [inst : Group G] (Γ : Subgroup G) [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] {K : Set (UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ)},
      IsCompact K → ∃ (D : Set G), IsCompact D ∧ K ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D := by
  intro G _ Γ _ _ _ K hK
  have hopen : IsOpenMap (UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ) :=
    isOpenMap_quotient_mk'_mul (Γ := ↥Γ) (T := G)
  refine hK.induction_on
    (p := fun S => ∃ D : Set G, IsCompact D ∧ S ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D) ?_ ?_ ?_ ?_
  · exact ⟨∅, isCompact_empty, Set.empty_subset _⟩
  · rintro s t hst ⟨D, hD, htD⟩
    exact ⟨D, hD, hst.trans htD⟩
  · rintro s t ⟨D, hD, hsD⟩ ⟨E, hE, htE⟩
    refine ⟨D ∪ E, hD.union hE, ?_⟩
    rw [Set.image_union]
    exact Set.union_subset_union hsD htE
  · intro x _
    obtain ⟨g, rfl⟩ : ∃ g : G, UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ g = x := Quotient.exists_rep x
    obtain ⟨D, hD, hgD⟩ := exists_compact_mem_nhds g
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hgD), D, hD, subset_rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RingSec
section
theorem UpperTheory.Reformulated.B.Qh66.ring_sec :
    ∀ (Ω C : Type) [inst : Field Ω] [IsAlgClosed Ω]
    [inst_2 : CommRing C] [Nontrivial C] (φ : Ω →+* C), φ.FiniteType → ∃ (ρ : C →+* Ω), ρ.comp φ = RingHom.id Ω := by
  intro Ω C _ _ _ _ φ hφ
  letI : Algebra Ω C := φ.toAlgebra
  haveI : Algebra.FiniteType Ω C := hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite Ω (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing Ω (C ⧸ m)
  let f : (C ⧸ m) →ₐ[Ω] Ω := IsAlgClosed.lift
  refine ⟨(f.comp (Ideal.Quotient.mkₐ Ω m)).toRingHom, ?_⟩
  ext x
  exact (f.comp (Ideal.Quotient.mkₐ Ω m)).commutes x
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootEqOne
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe14.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

private lemma UpperTheory.Reformulated.B.Qe14.pow_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : K} (h : ‖η - 1‖ < 1) (n : ℕ) : ‖η ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : η ^ (n + 1) - 1 = (η ^ n - 1) * (η - 1) + ((η ^ n - 1) + (η - 1)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ih h.le
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih h)

private lemma UpperTheory.Reformulated.B.Qe14.sum_close {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : K} (h : ‖η - 1‖ < 1) (n : ℕ) : ‖∑ i ∈ Finset.range n, η ^ i - (n : K)‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ∑ i ∈ Finset.range (n + 1), η ^ i - ((n + 1 : ℕ) : K)
        = (∑ i ∈ Finset.range n, η ^ i - (n : K)) + (η ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt ih (UpperTheory.Reformulated.B.Qe14.pow_close h n))

theorem UpperTheory.Reformulated.B.Qe14.root_eq_one :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] {m : ℕ},
      ¬v ∣ m →
        ∀ {η : UpperTheory.Reformulated.B.Qe14.Om v},
          η ^ m = (1 : UpperTheory.Reformulated.B.Qe14.Om v) →
            ‖η - (1 : UpperTheory.Reformulated.B.Qe14.Om v)‖ < (1 : ℝ) → η = (1 : UpperTheory.Reformulated.B.Qe14.Om v) := by
  intro v inst m hm η hη h
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, η ^ i) * (η - 1) = 0 := by
    rw [geom_sum_mul, hη, sub_self]
  have h2 : ∑ i ∈ Finset.range m, η ^ i = 0 :=
    (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hne)
  have h3 := UpperTheory.Reformulated.B.Qe14.sum_close h m
  rw [h2, zero_sub, norm_neg] at h3
  have h4 : ((m : ℕ) : PadicAlgCl v) = algebraMap ℚ_[v] (PadicAlgCl v) (m : ℚ_[v]) := by
    simp
  have h5 : ‖((m : ℕ) : PadicAlgCl v)‖ = ‖(m : ℚ_[v])‖ := by
    rw [h4]; exact PadicAlgCl.norm_extends v _
  rw [h5, Padic.norm_natCast_lt_one_iff] at h3
  exact hm h3
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootOrbit
section
theorem UpperTheory.Reformulated.B.Qi49.root_orbit :
    ∀ {A B G Ω : Type} [inst : CommRing A]
    [inst_1 : CommRing B] [inst_2 : Algebra A B] [inst_3 : Group G] [Finite G] [inst_5 : MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] [inst_8 : Field Ω] (φ ψ : B →+* Ω),
    φ.comp (Algebra.algebraMap A B) = ψ.comp (Algebra.algebraMap A B) →
      ∀ (b : B), ∃ (g : G), (ψ : B → Ω) b = (φ : B → Ω) (g • b) := by
  intro A B G Ω _ _ _ _ _ _ _ _ _ φ ψ h b
  classical
  cases nonempty_fintype G
  obtain ⟨p, hp⟩ := (Polynomial.mem_lifts _).1 (Algebra.IsInvariant.charpoly_mem_lifts A B G b)
  have hmap : (MulSemiringAction.charpoly G b).map φ = (MulSemiringAction.charpoly G b).map ψ := by
    rw [← hp, Polynomial.map_map, Polynomial.map_map, h]
  have hroot : ((MulSemiringAction.charpoly G b).map ψ).eval (ψ b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, MulSemiringAction.eval_charpoly, map_zero]
  rw [← hmap, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at hroot
  obtain ⟨g, -, hg⟩ := hroot
  refine ⟨g, ?_⟩
  simpa [sub_eq_zero] using hg
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Saturation
section
noncomputable def UpperTheory.Reformulated.B.IdealSaturationByElement.sat :
    {R : Type} → [inst : CommRing R] → Ideal R → R → Ideal R :=
  fun {R} _ Q f =>
    { carrier := {g : R | ∃ n : ℕ, f ^ n * g ∈ Q}
      add_mem' := by
        rintro a b ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : f ^ (m + n) * (a + b) = f ^ n * (f ^ m * a) + f ^ m * (f ^ n * b) := by ring
        rw [h]
        exact Q.add_mem (Q.mul_mem_left _ hm) (Q.mul_mem_left _ hn)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : f ^ n * (c • a) = c * (f ^ n * a) := by
          rw [smul_eq_mul]; ring
        rw [h]
        exact Q.mul_mem_left _ hn }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SaturationByPowers
section
noncomputable def UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers.{u_1} :
    {A : Type u_1} → [inst : CommRing A] → Ideal A → A → Ideal A :=
  fun {A} _ J a =>
    { carrier := {x : A | ∃ n : ℕ, a ^ n * x ∈ J}
      add_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : a ^ (m + n) * (x + y) = a ^ n * (a ^ m * x) + a ^ m * (a ^ n * y) := by ring
        rw [h]
        exact J.add_mem (J.mul_mem_left _ hm) (J.mul_mem_left _ hn)
      zero_mem' := ⟨0, by rw [mul_zero]; exact J.zero_mem⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : a ^ n * (c • x) = c * (a ^ n * x) := by rw [smul_eq_mul]; ring
        rw [h]
        exact J.mul_mem_left _ hn }
end

