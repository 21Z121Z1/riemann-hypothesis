import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherExtra
section
open MeasureTheory in
theorem UpperTheory.Reformulated.B.Qo7.eq_zero_of_orth :
    ∀ {K : Type} [inst : TopologicalSpace K] [CompactSpace K]
    [inst_2 : MeasurableSpace K] [BorelSpace K] (μ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (S : Set C(K, ℂ)),
    (1 : C(K, ℂ)) ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) →
        (∀ a ∈ S, Star.star a ∈ S) →
          (∀ (x y : K), x ≠ y → ∃ a ∈ S, (a : K → ℂ) x ≠ (a : K → ℂ) y) →
            ∀ (f : C(K, ℂ)), (∀ a ∈ S, ∫ (x : K), (a : K → ℂ) x * (f : K → ℂ) x ∂μ = (0 : ℂ)) → f = (0 : C(K, ℂ)) := by
  intro K _ _ _ _ μ _ _ S h1 hmul hstar hsep f hf
  have hint : ∀ g : C(K, ℂ), Integrable (fun x => g x) μ := fun g =>
    (BoundedContinuousFunction.mkOfCompact g).integrable μ
  have hint' : ∀ a : C(K, ℂ), Integrable (fun x => a x * f x) μ := fun a => hint (a * f)
  let L0 : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∫ x, a x * f x ∂μ
      map_add' := fun a b => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint' a) (hint' b)
      map_smul' := fun c a => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hL : Continuous L0 := by
    refine (L0.mkContinuous (‖f‖ * μ.real Set.univ) fun a => ?_).continuous
    have : ‖∫ x, a x * f x ∂μ‖ ≤ (‖a‖ * ‖f‖) * μ.real Set.univ := by
      refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul]
      exact mul_le_mul (a.norm_coe_le_norm x) (f.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)
    calc ‖L0 a‖ ≤ (‖a‖ * ‖f‖) * μ.real Set.univ := this
      _ = _ := by ring
  have hspan : ∀ a ∈ StarAlgebra.adjoin ℂ S, a ∈ Submodule.span ℂ S := by
    intro a ha
    induction ha using StarAlgebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span hx
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have h := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨u, hu, v, hv, rfl⟩
      exact hmul u hu v hv
    | star x _ hx =>
      clear * - hx hstar
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hstar y hy)
      | zero => simp
      | add y z _ _ hy hz => rw [star_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [star_smul]; exact Submodule.smul_mem _ _ hy
  have hker : Submodule.span ℂ S ≤ LinearMap.ker L0 :=
    Submodule.span_le.2 fun a ha => hf a ha
  have hsp : (StarAlgebra.adjoin ℂ S).SeparatesPoints := by
    intro x y hxy
    obtain ⟨a, ha, hne⟩ := hsep x y hxy
    exact ⟨a, ⟨a, StarAlgebra.subset_adjoin ℂ S ha, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsp
  have hall : ∀ a : C(K, ℂ), L0 a = 0 := by
    intro a
    have ha : a ∈ closure (StarAlgebra.adjoin ℂ S : Set C(K, ℂ)) := by
      have : a ∈ (StarAlgebra.adjoin ℂ S).topologicalClosure := by
        rw [htop]; exact StarSubalgebra.mem_top
      exact this
    exact closure_minimal (t := {b | L0 b = 0}) (fun b hb => hker (hspan b hb))
      (isClosed_eq hL continuous_const) ha
  have h0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0 := by
    have h := hall (star f)
    change ∫ x, (star f) x * f x ∂μ = 0 at h
    have e : (fun x => (star f) x * f x) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
      funext x
      simp only [ContinuousMap.star_apply, RCLike.star_def]
      rw [Complex.conj_mul']
      push_cast
      rfl
    rw [e, integral_complex_ofReal] at h
    exact_mod_cast h
  have hc : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
  have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable μ
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hi).1 h0
  have heq := (hc.ae_eq_iff_eq μ continuous_zero).1 hae
  ext x
  simpa using congrFun heq x
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherSide
section
theorem UpperTheory.Reformulated.B.Rc5.exists_reps :
    ∀ {α : Type} (r : α → α → Prop),
    (∀ (a b : α), r a b → r b a) →
      (∀ (a b c : α), r a b → r b c → r a c) →
        ∀ (t : Finset α), ∃ C ⊆ t, (∀ a ∈ C, ∀ b ∈ C, r a b → a = b) ∧ ∀ x ∈ t, x ∈ C ∨ ∃ c ∈ C, r x c := by
  intro α r hs _ t
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | insert y s _ ih =>
    obtain ⟨C, hC, h1, h2⟩ := ih
    by_cases h : ∃ c ∈ C, r y c
    · refine ⟨C, hC.trans (Finset.subset_insert _ _), h1, ?_⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Or.inr h
      · exact h2 x hx
    · refine ⟨insert y C, Finset.insert_subset_insert _ hC, ?_, ?_⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with ha | ha
        · rcases Finset.mem_insert.1 hb with hb | hb
          · rw [ha, hb]
          · exact absurd ⟨b, hb, ha ▸ hab⟩ h
        · rcases Finset.mem_insert.1 hb with hb | hb
          · exact absurd ⟨a, ha, hb ▸ hs a b hab⟩ h
          · exact h1 a ha b hb hab
      · intro x hx
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact Or.inl (Finset.mem_insert.2 (Or.inl hx))
        · rcases h2 x hx with h3 | ⟨c, hc, h3⟩
          · exact Or.inl (Finset.mem_insert_of_mem h3)
          · exact Or.inr ⟨c, Finset.mem_insert_of_mem hc, h3⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherTer
section
theorem UpperTheory.Reformulated.B.Qk64.diag_mul :
    ∀ {n : ℕ} {Q : Type} [inst : CommRing Q]
    (a b : Matrix (Fin n) (Fin n) Q),
    (∀ (i j : Fin n), i < j → a i j = (0 : Q)) →
      (∀ (i j : Fin n), i < j → b i j = (0 : Q)) → ∀ (i : Fin n), (a * b) i i = a i i * b i i := by
  intro n Q _ a b ha hb i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hb j i h, mul_zero]
  · rw [ha i j h, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsLast
section
theorem UpperTheory.Reformulated.B.DYhb1.main :
    ∀ (A M : Type) [inst : CommRing A] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module A M] [Module.Finite A M]
      [Module.Projective A M],
      ∃ (n : ℕ) (e : Fin n → M) (f : Fin n → Module.Dual A M), ∀ (m : M), ∑ i : Fin n, (f i : M → A) m • e i = m := by
  intro A M _ _ _ _ _
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  refine ⟨n, fun i => p (fun j => if i = j then 1 else 0),
    fun i => (LinearMap.proj i).comp s, fun m => ?_⟩
  have h1 : p (s m) = m := by
    have := LinearMap.congr_fun hs m
    simpa using this
  have h2 := LinearMap.pi_apply_eq_sum_univ p (s m)
  rw [h1] at h2
  exact h2.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMore
section
theorem UpperTheory.Reformulated.B.DYdc6.main :
    ∀ {X : ℕ → Type} [∀ (n : ℕ), Finite (X n)] [∀ (n : ℕ), Nonempty (X n)] (f : (n : ℕ) → X (n + (1 : ℕ)) → X n),
      ∃ (x : (n : ℕ) → X n), ∀ (n : ℕ), f n (x (n + (1 : ℕ))) = x n := by
  intro X _ _ f
  let F : CategoryTheory.Functor ℕᵒᵖ Type :=
    CategoryTheory.Functor.ofOpSequence (X := X) (fun n => TypeCat.ofHom (f n))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => inferInstanceAs (Finite (X j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => inferInstanceAs (Nonempty (X j.unop))
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => s (Opposite.op n), fun n => ?_⟩
  have h := hs (CategoryTheory.homOfLE (Nat.le_add_right n 1)).op
  rw [CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreFurther
section
theorem UpperTheory.Reformulated.B.Qh12.ell :
    ∀ (O Λ Γ X : Type) [inst : CommRing O] [inst_1 : CommRing Λ] [inst_2 : Algebra O Λ]
    [inst_3 : CommGroup Γ] [inst_4 : AddCommGroup X] [inst_5 : _root_.Module O X] (th₀ : Λ →ₐ[O] O) (d : Λ →ₗ[O] X)
    (χ : Γ →* Multiplicative X),
    (∀ (a b : Λ), (d : Λ → X) (a * b) = (th₀ : Λ → O) a • (d : Λ → X) b + (th₀ : Λ → O) b • (d : Λ → X) a) →
      ∃ (th : MonoidAlgebra Λ Γ →ₐ[O] O) (ell : MonoidAlgebra Λ Γ →ₗ[O] X),
        (∀ (g : Γ) (a : Λ), (th : MonoidAlgebra Λ Γ → O) (MonoidAlgebra.single g a) = (th₀ : Λ → O) a) ∧
          (∀ (a b : MonoidAlgebra Λ Γ),
              (ell : MonoidAlgebra Λ Γ → X) (a * b) =
                (th : MonoidAlgebra Λ Γ → O) a • (ell : MonoidAlgebra Λ Γ → X) b +
                  (th : MonoidAlgebra Λ Γ → O) b • (ell : MonoidAlgebra Λ Γ → X) a) ∧
            ∀ (g : Γ) (a : Λ),
              (ell : MonoidAlgebra Λ Γ → X) (MonoidAlgebra.single g a) =
                (d : Λ → X) a +
                  (th₀ : Λ → O) a • (Multiplicative.toAdd : Multiplicative X → X) ((χ : Γ → Multiplicative X) g) := by
  intro O Λ Γ X _ _ _ _ _ _ th₀ d χ hd
  classical
  let th : MonoidAlgebra Λ Γ →ₐ[O] O :=
    MonoidAlgebra.liftNCAlgHom th₀ (1 : Γ →* O) (fun _ _ => Commute.all _ _)
  have hth : ∀ (g : Γ) (a : Λ), th (MonoidAlgebra.single g a) = th₀ a := by
    intro g a
    simp [th]
  let ell : MonoidAlgebra Λ Γ →ₗ[O] X :=
    (Finsupp.lsum O (fun g : Γ => d + th₀.toLinearMap.smulRight (Multiplicative.toAdd (χ g)))) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv O).toLinearMap
  have hell : ∀ (g : Γ) (a : Λ), ell (MonoidAlgebra.single g a)
      = d a + th₀ a • Multiplicative.toAdd (χ g) := by
    intro g a
    simp [ell]
  refine ⟨th, ell, hth, ?_, hell⟩
  intro a b
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    simp only [add_mul, map_add, ha, ha', add_smul, smul_add]
    abel
  | single g a =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      simp only [mul_add, map_add, hb, hb', add_smul, smul_add]
      abel
    | single h b =>
      rw [MonoidAlgebra.single_mul_single, hell, hell, hell, hth, hth, hd, map_mul, map_mul,
        toAdd_mul]
      module
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreLast
section
theorem UpperTheory.Reformulated.B.Qk10.exists_w :
    ∀ (K : Type) [inst : Field K] [NumberField K] {p : ℕ},
    Nat.Prime p →
      ∃ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (↑p : NumberField.RingOfIntegers K) ∈ w.asIdeal := by
  intro K _ _ p hp
  have hnu : ¬ IsUnit (p : NumberField.RingOfIntegers K) := by
    intro h
    have h1 : IsUnit (algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ)) := by
      simpa using h
    have h2 : IsUnit (p : ℤ) := (isUnit_map_iff _ _).mp h1
    exact (Nat.prime_iff_prime_int.mp hp).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span {(p : NumberField.RingOfIntegers K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (p : NumberField.RingOfIntegers K) ∈ M :=
    hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  rw [Ideal.mem_bot] at hmem
  exact hp.ne_zero (Nat.cast_eq_zero.mp hmem)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreRest
section
theorem UpperTheory.Reformulated.B.Qi28.exists_extend.{u_1, u_2} :
    ∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]
    [Algebra.IsIntegral R A] (ev : R →+* ℂ),
    RingHom.ker (Algebra.algebraMap R A) ≤ RingHom.ker ev → ∃ (χ : A →+* ℂ), χ.comp (Algebra.algebraMap R A) = ev := by
  intro R A _ _ _ _ ev h
  haveI hP : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := A) (RingHom.ker ev) ⊥
    (by rw [← RingHom.ker_eq_comap_bot]; exact h)
  haveI : Q.LiesOver (RingHom.ker ev) := ⟨hQP.symm⟩
  letI : Algebra (R ⧸ RingHom.ker ev) ℂ := (RingHom.kerLift ev).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker ev) ℂ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ev)
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker ev) (A ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : FaithfulSMul (R ⧸ RingHom.ker ev) (A ⧸ Q) := inferInstance
  haveI : IsDomain (R ⧸ RingHom.ker ev) := Ideal.Quotient.isDomain _
  haveI : IsDomain (A ⧸ Q) := Ideal.Quotient.isDomain _
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker ev) (A ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 ‹_›
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker ev) ℂ :=
    Module.isTorsionFree_iff_faithfulSMul.2 ‹_›
  let φ : (A ⧸ Q) →ₐ[R ⧸ RingHom.ker ev] ℂ := IsAlgClosed.lift
  refine ⟨(φ : (A ⧸ Q) →+* ℂ).comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  exact φ.commutes (Ideal.Quotient.mk (RingHom.ker ev) r)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreSide
section
theorem UpperTheory.Reformulated.B.Qi36.aux :
    ∀ {R Q M : Type} [inst : CommRing R] [inst_1 : Group Q]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (π : Representation R Q M) (H : Subgroup Q) (f : Q → M),
    (∀ (g h : Q), f (g * h) = f g + ((π : Q → M →ₗ[R] M) g : M → M) (f h)) →
      (∀ u ∈ H, f u = (0 : M)) → ∃ (m : M), ∀ (g : Q), H.index • f g = ((π : Q → M →ₗ[R] M) g : M → M) m - m := by
  intro R Q M _ _ _ _ π H f hf hH
  by_cases h0 : H.index = 0
  · exact ⟨0, fun g => by simp [h0]⟩
  haveI : Finite (Q ⧸ H) := Nat.finite_of_card_ne_zero h0
  letI : Fintype (Q ⧸ H) := Fintype.ofFinite _
  have key : ∀ a b : Q, (a : Q ⧸ H) = (b : Q ⧸ H) → f a = f b := by
    intro a b hab
    have hm : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h1 := hf a (a⁻¹ * b)
    rw [hH _ hm, map_zero, add_zero, mul_inv_cancel_left] at h1
    exact h1.symm
  have step : ∀ (g : Q) (x : Q ⧸ H), f (g • x).out = f g + π g (f x.out) := by
    intro g x
    rw [← hf]
    apply key
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe, QuotientGroup.out_eq']
  refine ⟨-∑ x : Q ⧸ H, f x.out, fun g => ?_⟩
  have hs : ∑ x : Q ⧸ H, f (g • x).out = ∑ x : Q ⧸ H, f x.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun x : Q ⧸ H => f x.out)
  simp only [step, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs
  rw [← map_sum] at hs
  rw [Subgroup.index, Nat.card_eq_fintype_card, map_neg, sub_neg_eq_add,
    eq_sub_of_add_eq hs]
  abel
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreTail
section
theorem UpperTheory.Reformulated.B.Qi6.det_ne_zero :
    ∀ {F : Type} [inst : NormedField F] [IsUltrametricDist F] {m : ℕ}
    (t : F),
    ‖t‖ = (1 : ℝ) →
      ∀ (E : Matrix (Fin m) (Fin m) F),
        (∀ (a b : Fin m), ‖E a b‖ < (1 : ℝ)) → (t • (1 : Matrix (Fin m) (Fin m) F) + E).det ≠ (0 : F) := by
  intro F _ _ m t ht E hE hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  haveI : Nonempty (Fin m) := ⟨i⟩
  obtain ⟨a, ha⟩ := Finite.exists_max (fun j => ‖v j‖)
  have hpos : 0 < ‖v a‖ := lt_of_lt_of_le (norm_pos_iff.mpr hi) (ha i)
  have hrow : t * v a = -∑ b, E a b * v b := by
    have h := congrFun hMv a
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact eq_neg_of_add_eq_zero_left h
  obtain ⟨b, -, hb⟩ := IsUltrametricDist.exists_norm_finset_sum_le (Finset.univ : Finset (Fin m))
    (fun b => E a b * v b)
  have h1 : ‖v a‖ = ‖∑ b, E a b * v b‖ := by
    rw [← norm_neg (∑ b, E a b * v b), ← hrow, norm_mul, ht, one_mul]
  have h2 : ‖E a b * v b‖ < ‖v a‖ := by
    rw [norm_mul]
    calc ‖E a b‖ * ‖v b‖ ≤ ‖E a b‖ * ‖v a‖ :=
          mul_le_mul_of_nonneg_left (ha b) (norm_nonneg _)
      _ < 1 * ‖v a‖ := mul_lt_mul_of_pos_right (hE a b) hpos
      _ = ‖v a‖ := one_mul _
  exact absurd (h1.le.trans hb) (not_le.mpr h2)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreTer
section
theorem UpperTheory.Reformulated.B.Qf50.multiset_eq_of_sum :
    ∀ {Γ : Type} [inst : Monoid Γ] (s t : Multiset (Γ →* ℂ)),
    (∀ (g : Γ),
        (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) s).sum =
          (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) t).sum) →
      s = t := by
  classical
  intro Γ _ s t h
  have key : ∀ (u : Finset (Γ →* ℂ)) (r : Multiset (Γ →* ℂ)), r.toFinset ⊆ u → ∀ g : Γ,
      (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) r).sum
        = ∑ f ∈ u, (r.count f : ℂ) * f g := by
    intro u r hr g
    rw [Finset.sum_multiset_map_count, Finset.sum_subset hr]
    · exact Finset.sum_congr rfl fun f _ => by simp
    · intro f _ hf
      have : r.count f = 0 := Multiset.count_eq_zero.2 (by simpa using hf)
      simp [this]
  set u : Finset (Γ →* ℂ) := s.toFinset ∪ t.toFinset with hu
  have hs : s.toFinset ⊆ u := Finset.subset_union_left
  have ht : t.toFinset ⊆ u := Finset.subset_union_right
  have lin := linearIndependent_iff'.1 (linearIndependent_monoidHom Γ ℂ) u
    (fun f => (s.count f : ℂ) - (t.count f : ℂ)) (by
      funext g
      have e := h g
      rw [key u s hs g, key u t ht g] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib]
      exact sub_eq_zero.2 e)
  ext f
  by_cases hf : f ∈ u
  · have := lin f hf
    exact_mod_cast sub_eq_zero.1 this
  · have h1 : f ∉ s := fun m => hf (hs (by simpa using m))
    have h2 : f ∉ t := fun m => hf (ht (by simpa using m))
    rw [Multiset.count_eq_zero.2 h1, Multiset.count_eq_zero.2 h2]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRest
section
theorem UpperTheory.Reformulated.B.DYha2.main :
    ∀ {X Y : Type} [inst : AddCommGroup X] [inst_1 : _root_.Module ℂ X] [inst_2 : AddCommGroup Y]
      [inst_3 : _root_.Module ℂ Y] {x : X} {y : Y}, x ≠ (0 : X) → y ≠ (0 : Y) → x ⊗ₜ[ℂ] y ≠ (0 : TensorProduct ℂ X Y) := by
  intro X Y _ _ _ _ x y hx hy h
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero ℂ hy
  have key := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ f g)) h
  simp only [TensorProduct.lift.tmul, map_zero, LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at key
  exact (mul_ne_zero hf hg) key
end

