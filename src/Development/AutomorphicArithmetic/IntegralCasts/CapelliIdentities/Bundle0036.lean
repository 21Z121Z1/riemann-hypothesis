import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideBis
section
namespace EqOneOfPowersNearOne

private lemma key {R : Type} [NormedRing R] [NormedAlgebra ℂ R] {a : R}
    (h : ∀ (p : ℕ), ‖a ^ p - (1 : R)‖ < (1 / 2 : ℝ)) (N : ℕ) :
    (N : ℝ) * ‖a - 1‖ < ‖a - 1‖ * (N / 2) + 1 / 2 := by
  set S : R := ∑ k ∈ Finset.range N, a ^ k with hS
  have hgeom : S * (a - 1) = a ^ N - 1 := geom_sum_mul a N
  have hdiff : (N : R) - S = ∑ k ∈ Finset.range N, ((1 : R) - a ^ k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hbound : ‖(N : R) - S‖ ≤ N / 2 := by
    rw [hdiff]
    calc ‖∑ k ∈ Finset.range N, ((1 : R) - a ^ k)‖
        ≤ ∑ k ∈ Finset.range N, ‖(1 : R) - a ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, (1 / 2 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_sub_rev]; exact (h k).le
      _ = N / 2 := by simp; ring
  have hnorm : ‖(N : R) * (a - 1)‖ = (N : ℝ) * ‖a - 1‖ := by
    have : (N : R) * (a - 1) = (N : ℂ) • (a - 1) := by
      rw [Algebra.smul_def]; simp
    rw [this, norm_smul]; simp
  have hsplit : (N : R) * (a - 1) = ((N : R) - S) * (a - 1) + S * (a - 1) := by
    rw [sub_mul]; abel
  calc (N : ℝ) * ‖a - 1‖ = ‖(N : R) * (a - 1)‖ := hnorm.symm
    _ ≤ ‖((N : R) - S) * (a - 1)‖ + ‖S * (a - 1)‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖(N : R) - S‖ * ‖a - 1‖ + ‖a ^ N - 1‖ := by
        rw [hgeom]; gcongr; exact norm_mul_le _ _
    _ < ‖a - 1‖ * (N / 2) + 1 / 2 := by
        have := h N
        nlinarith [norm_nonneg (a - 1)]

end EqOneOfPowersNearOne

theorem UpperTheory.Reformulated.B.Yhd7.main :
    ∀ {R : Type} [inst : NormedRing R] [NormedAlgebra ℂ R] {a : R},
      (∀ (p : ℕ), ‖a ^ p - (1 : R)‖ < (1 / 2 : ℝ)) → a = (1 : R) := by
  intro R _ _ a h
  by_contra hne
  have hpos : 0 < ‖a - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖a - 1‖)
  have hk := EqOneOfPowersNearOne.key h N
  have h1 : 1 < (N : ℝ) * ‖a - 1‖ := by
    rw [div_lt_iff₀ hpos] at hN; linarith
  nlinarith
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IndependenceCharacters
section
theorem UpperTheory.Reformulated.B.LinearIndependentOfDistinctEigensystems.indep :
    ∀ {V I J : Type} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℂ V] (T : I → Module.End ℂ V) (v : J → V) (lam : J → I → ℂ),
    (∀ (j : J), v j ≠ (0 : V)) →
      (∀ (j : J) (i : I), (T i : V → V) (v j) = lam j i • v j) → Function.Injective lam → LinearIndependent ℂ v := by
  intro V I J _ _ T v lam hv hT hinj
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ j hj; simp at hj
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ b ∈ s, g b = 0 := by
      intro b hb
      have hne : lam b ≠ lam a := fun h => ha (hinj h ▸ hb)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have h1 : g a • lam a i • v a + ∑ j ∈ s, g j • lam j i • v j = 0 := by
        have := congrArg (T i) hg
        simpa only [map_add, map_sum, map_smul, map_zero, hT] using this
      have h2 : g a • lam a i • v a + ∑ j ∈ s, g j • lam a i • v j = 0 := by
        have := congrArg (fun x => lam a i • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_comm (lam a i)] using this
      have h3 : ∑ j ∈ s, (g j * (lam j i - lam a i)) • v j = 0 := by
        have h4 : ∑ j ∈ s, g j • lam j i • v j = ∑ j ∈ s, g j • lam a i • v j :=
          add_left_cancel (h1.trans h2.symm)
        simp only [mul_smul, sub_smul, smul_sub, Finset.sum_sub_distrib, h4, sub_self]
      have h5 := ih (fun j => g j * (lam j i - lam a i)) h3 b hb
      exact (mul_eq_zero.mp h5).resolve_right (sub_ne_zero.mpr hi)
    have h0 : ∑ j ∈ s, g j • v j = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]
    rw [h0, add_zero] at hg
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs j hj
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IndependenceEigenvectors
section
theorem UpperTheory.Reformulated.B.IndependenceEigenvectors.indep :
    ∀ {V I J : Type} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℂ V] (T : I → Module.End ℂ V) (v : J → V) (lam : J → I → ℂ),
    (∀ (j : J), v j ≠ (0 : V)) →
      (∀ (j : J) (i : I), (T i : V → V) (v j) = lam j i • v j) → Function.Injective lam → LinearIndependent ℂ v := by
  intro V I J _ _ T v lam hv hT hinj
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ j hj; simp at hj
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ j ∈ s, g j = 0 := by
      intro j hj
      have hne : lam j ≠ lam a := fun h => ha (hinj h ▸ hj)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have h1 : (g a * lam a i) • v a + ∑ k ∈ s, (g k * lam k i) • v k = 0 := by
        have h := congrArg (T i) hg
        simpa only [map_add, map_sum, map_smul, map_zero, hT, smul_smul] using h
      have h2 : (g a * lam a i) • v a + ∑ k ∈ s, (g k * lam a i) • v k = 0 := by
        have h := congrArg (fun x => lam a i • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm (lam a i)] using h
      have h3 : ∑ k ∈ s, (g k * (lam k i - lam a i)) • v k = 0 := by
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr (add_left_cancel (h1.trans h2.symm))
      have h4 := ih (fun k => g k * (lam k i - lam a i)) h3 j hj
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hi)
    have hz : ∑ k ∈ s, g k • v k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hs k hk, zero_smul]
    rw [hz, add_zero] at hg
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs j hj
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfEmbUnique
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf27.Ainf :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ NumberField.InfiniteAdeleRing F

theorem UpperTheory.Reformulated.B.Qf27.aux2 :
    ∀ {F : Type} [inst : Field F], SMulCommClass F (UpperTheory.Reformulated.B.Qf27.Ainf F) (UpperTheory.Reformulated.B.Qf27.Ainf F) := by
  intro F _
  infer_instance

theorem UpperTheory.Reformulated.B.Qf27.aux3 :
    ∀ {F : Type} [inst : Field F], IsScalarTower F (UpperTheory.Reformulated.B.Qf27.Ainf F) (UpperTheory.Reformulated.B.Qf27.Ainf F) := by
  intro F _
  infer_instance

theorem UpperTheory.Reformulated.B.Qf27.aux4 :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E], SMulCommClass F E E := by
  intro F E _ _ _
  infer_instance

theorem UpperTheory.Reformulated.B.Qf27.aux5 :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E], IsScalarTower F E E := by
  intro F E _ _ _
  infer_instance

noncomputable def UpperTheory.Reformulated.B.Qf27.IsInfEmb :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] → [inst_2 : Algebra F E] → (E →+* ℂ) → (TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ) → Prop :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (τ : E →+* ℂ)
        (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ) ↦
      (∀ (x : E),
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E → ℂ) ((1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] x) = (τ : E → ℂ) x) ∧
        Continuous fun (a : UpperTheory.Reformulated.B.Qf27.Ainf F) ↦
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E → ℂ) (a ⊗ₜ[F] (1 : E))

theorem UpperTheory.Reformulated.B.Qf27.infEmb_unique :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] {τ : E →+* ℂ}
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qf27.IsInfEmb τ θ' → θ = θ' := by
  intro F E _ _ _ _ τ θ θ' h h'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have hd : DenseRange (algebraMap F (UpperTheory.Reformulated.B.Qf27.Ainf F)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have key : ∀ c : F, (algebraMap F (UpperTheory.Reformulated.B.Qf27.Ainf F) c) ⊗ₜ[F] (1 : E)
      = (1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] (algebraMap F E c) := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hA : (fun a : UpperTheory.Reformulated.B.Qf27.Ainf F ↦ θ (a ⊗ₜ[F] (1 : E)))
      = fun a : UpperTheory.Reformulated.B.Qf27.Ainf F ↦ θ' (a ⊗ₜ[F] (1 : E)) := by
    refine hd.equalizer h2 h2' ?_
    funext c
    simp only [Function.comp_apply]
    rw [key, h1, h1']
  refine RingHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x =>
    have e : a ⊗ₜ[F] x = (a ⊗ₜ[F] (1 : E)) * ((1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h1, h1', congrFun hA a]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfiniteNormOneElements
section
theorem UpperTheory.infinite_norm_one_elements :
    ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
        {t : E | t * σ t = 1}.Infinite := by
  intro F E _ _ _ _ σ hE hσ
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hw : ¬ NumberField.ComplexEmbedding.IsReal w.embedding :=
    NumberField.InfinitePlace.isComplex_iff.mp (hE.isComplex w)
  generalize w.embedding = τ at hw
  have hinv : ∀ x : E, σ (σ x) = x := fun x =>
    τ.injective (by rw [hσ, hσ, star_star])
  obtain ⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by
    by_contra h
    push Not at h
    apply hw
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [h] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  have h1 : ∀ n : ℕ, (n : E) + a ≠ 0 := by
    intro n hn
    apply ha
    have : a = -(n : E) := by linear_combination hn
    rw [this, map_neg, map_natCast]
  have h2 : ∀ n : ℕ, (n : E) + σ a ≠ 0 := by
    intro n hn
    apply h1 n
    have := congrArg σ hn
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + a) / ((n : E) + σ a)) ?_ ?_
  · intro m n hmn
    have h3 := (div_eq_div_iff (h2 m) (h2 n)).mp hmn
    have h4 : ((m : E) - n) * (σ a - a) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact Nat.cast_injective (R := E) (sub_eq_zero.mp h)
    · exact absurd (sub_eq_zero.mp h) ha
  · intro n
    show _ * σ _ = 1
    rw [map_div₀, map_add, map_add, map_natCast, hinv, div_mul_div_cancel₀ (h2 n), div_self (h1 n)]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfiniteTraceAlgebraMap
section
theorem UpperTheory.Reformulated.B.Qh34.aux1.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],
      ∑ x : NumberField.InfinitePlace K,
          (↑x.mult : ℝ) *
            ((NumberField.InfinitePlace.Completion.extensionEmbedding x : x.Completion → ℂ)
                ((0 : NumberField.InfiniteAdeleRing K) x)).re =
        (0 : ℝ) := by
  intro K _ _
  refine Finset.sum_eq_zero fun w _ => ?_
  have h : (0 : NumberField.InfiniteAdeleRing K) w = 0 := rfl
  rw [h, map_zero, Complex.zero_re, mul_zero]

theorem UpperTheory.Reformulated.B.Qh34.aux2.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x y : NumberField.InfiniteAdeleRing K),
      ∑ w : NumberField.InfinitePlace K,
          (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) ((x + y) w)).re =
        ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re +
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (y w)).re := by
  intro K _ _ x y
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (x + y) w = x w + y w := rfl
  rw [h, map_add, Complex.add_re, mul_add]

noncomputable def UpperTheory.Reformulated.B.Qh34.infiniteTrace.{u_1} :
    (K : Type u_1) → [inst : Field K] → [NumberField K] → NumberField.InfiniteAdeleRing K →+ ℝ :=
    fun (K : Type u_1) [Field K] [NumberField K] ↦
      {
        toFun := fun (x : NumberField.InfiniteAdeleRing K) ↦
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re,
        map_zero' := UpperTheory.Reformulated.B.Qh34.aux1 K, map_add' := UpperTheory.Reformulated.B.Qh34.aux2 K : NumberField.InfiniteAdeleRing K →+ ℝ }

theorem UpperTheory.Reformulated.B.Qh34.infiniteTrace_algebraMap.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (k : K),
      (UpperTheory.Reformulated.B.Qh34.infiniteTrace K : NumberField.InfiniteAdeleRing K → ℝ)
          ((Algebra.algebraMap K (NumberField.InfiniteAdeleRing K) : K → NumberField.InfiniteAdeleRing K) k) =
        (↑((Algebra.trace ℚ K : K → ℚ) k) : ℝ) := by
  classical
  intro K _ _ k
  have h1 : ((Algebra.trace ℚ K k : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ k).re := by
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := k)
    have h' : ∑ φ : K →+* ℂ, φ k = ∑ σ : K →ₐ[ℚ] ℂ, σ k :=
      Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun _ => rfl)
    rw [← Complex.re_sum, h', ← h]
    simp
  rw [h1, ← Finset.sum_fiberwise Finset.univ NumberField.InfinitePlace.mk]
  change ∑ w : NumberField.InfinitePlace K, (↑w.mult : ℝ) *
    (NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap K (NumberField.InfiniteAdeleRing K) k w)).re = _
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap K (NumberField.InfiniteAdeleRing K) k w) = w.embedding k := by
    simp
  have h3 : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => NumberField.InfinitePlace.mk φ = w),
      (φ k).re = (w.embedding k).re := by
    intro φ hφ
    rw [← (Finset.mem_filter.1 hφ).2]
    rcases NumberField.InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [h2, Finset.sum_congr rfl h3, Finset.sum_const, NumberField.InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InnerProductFormulaField
section
noncomputable def UpperTheory.Reformulated.B.InnerProductFormulaField.GlRel.{u_2, u_5} :
    {R : Type u_2} → [DecidableEq R] → {A : Type u_5} → [Ring A] → (R → R → A) → Prop :=
    fun {R : Type u_2} [inst : DecidableEq R] {A : Type u_5} [inst_1 : Ring A] (T : R → R → A) ↦
      ∀ (a b c d : R),
        @Eq A
          (@HSub.hSub A A A
            (@instHSub A
              (@SubNegMonoid.toSub A
                (@AddGroup.toSubNegMonoid A (@AddGroupWithOne.toAddGroup A (@Ring.toAddGroupWithOne A inst_1)))))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst_1))))
              (T a b) (T c d))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@Ring.toSemiring A inst_1))))
              (T c d) (T a b)))
          (@HSub.hSub A A A
            (@instHSub A
              (@SubNegMonoid.toSub A
                (@AddGroup.toSubNegMonoid A (@AddGroupWithOne.toAddGroup A (@Ring.toAddGroupWithOne A inst_1)))))
            (@ite A (@Eq R b c) (inst b c) (T a d)
              (@OfNat.ofNat A (nat_lit 0)
                (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst_1))))))
            (@ite A (@Eq R d a) (inst d a) (T c b)
              (@OfNat.ofNat A (nat_lit 0)
                (@Zero.toOfNat0 A (@MulZeroClass.toZero A (@instMulZeroClassOfSemiring A (@Ring.toSemiring A inst_1)))))))

theorem UpperTheory.Reformulated.B.InnerProductFormulaField.aux2 :
    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).AtLeastTwo := by
  exact ⟨le_refl _⟩

noncomputable def UpperTheory.Reformulated.B.InnerProductFormulaField.CasimirValue :
    Prop :=
    ∀ (k M : Type) [inst : CommRing k] [inst_1 : AddCommGroup M]
      [inst_2 :
        @_root_.Module k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
          (@AddCommGroup.toAddCommMonoid M inst_1)]
      (r : Nat)
      (T :
        Fin r →
          Fin r →
            @Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
              (@AddCommGroup.toAddCommMonoid M inst_1) inst_2),
      @UpperTheory.Reformulated.B.InnerProductFormulaField.GlRel (Fin r) (instDecidableEqFin r)
          (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
            (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
          (@Module.End.instRing k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)) inst_1 inst_2) T →
        ∀ (v : M) (κ : Fin r → k),
          (∀ (b b' : Fin r),
              @LT.lt (Fin r) (@instLTFin r) b b' →
                @Eq M
                  (@DFunLike.coe
                    (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    M (fun (x : M) ↦ M)
                    (@LinearMap.instFunLike k k M M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) (@AddCommGroup.toAddCommMonoid M inst_1) inst_2 inst_2
                      (@RingHom.id k
                        (@Semiring.toNonAssocSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                    (T b b') v)
                  (@OfNat.ofNat M (nat_lit 0)
                    (@Zero.toOfNat0 M
                      (@NegZeroClass.toZero M
                        (@SubNegZeroMonoid.toNegZeroClass M
                          (@SubtractionMonoid.toSubNegZeroMonoid M
                            (@SubtractionCommMonoid.toSubtractionMonoid M
                              (@AddCommGroup.toDivisionAddCommMonoid M inst_1)))))))) →
            (∀ (b : Fin r),
                @Eq M
                  (@DFunLike.coe
                    (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                    M (fun (x : M) ↦ M)
                    (@LinearMap.instFunLike k k M M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                      (@AddCommGroup.toAddCommMonoid M inst_1) (@AddCommGroup.toAddCommMonoid M inst_1) inst_2 inst_2
                      (@RingHom.id k
                        (@Semiring.toNonAssocSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                    (T b b) v)
                  (@HSMul.hSMul k M M
                    (@instHSMul k M
                      (@SMulZeroClass.toSMul k M
                        (@AddZero.toZero M
                          (@AddZeroClass.toAddZero M
                            (@AddMonoid.toAddZeroClass M
                              (@SubNegMonoid.toAddMonoid M
                                (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))))
                        (@DistribSMul.toSMulZeroClass k M
                          (@AddMonoid.toAddZeroClass M
                            (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))
                          (@DistribMulAction.toDistribSMul k M
                            (@Semiring.toMonoid k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))
                            (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1)))
                            (@Module.toDistribMulAction k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                              (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))))
                    (κ b) v)) →
              @Eq M
                (@DFunLike.coe
                  (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                  M (fun (x : M) ↦ M)
                  (@LinearMap.instFunLike k k M M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                    (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)) (@AddCommGroup.toAddCommMonoid M inst_1)
                    (@AddCommGroup.toAddCommMonoid M inst_1) inst_2 inst_2
                    (@RingHom.id k
                      (@Semiring.toNonAssocSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                  (∑ b : Fin r,
                    ∑ b' : Fin r,
                      @HMul.hMul
                        (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                          (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                        (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                          (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                        (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                          (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                        (@instHMul
                          (@Module.End k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                            (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)
                          (@Module.End.instMul k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                            (@AddCommGroup.toAddCommMonoid M inst_1) inst_2))
                        (T b b') (T b' b))
                  v)
                (@HSMul.hSMul k M M
                  (@instHSMul k M
                    (@SMulZeroClass.toSMul k M
                      (@AddZero.toZero M
                        (@AddZeroClass.toAddZero M
                          (@AddMonoid.toAddZeroClass M
                            (@SubNegMonoid.toAddMonoid M
                              (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))))
                      (@DistribSMul.toSMulZeroClass k M
                        (@AddMonoid.toAddZeroClass M
                          (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1))))
                        (@DistribMulAction.toDistribSMul k M
                          (@Semiring.toMonoid k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))
                          (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_1)))
                          (@Module.toDistribMulAction k M (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst))
                            (@AddCommGroup.toAddCommMonoid M inst_1) inst_2)))))
                  (∑ b : Fin r,
                    @HMul.hMul k k k
                      (@instHMul k
                        (@Distrib.toMul k
                          (@instDistribOfSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                      (κ b)
                      (@HSub.hSub k k k
                        (@instHSub k
                          (@SubNegMonoid.toSub k
                            (@AddGroup.toSubNegMonoid k
                              (@AddGroupWithOne.toAddGroup k (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst))))))
                        (@HSub.hSub k k k
                          (@instHSub k
                            (@SubNegMonoid.toSub k
                              (@AddGroup.toSubNegMonoid k
                                (@AddGroupWithOne.toAddGroup k (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst))))))
                          (@HAdd.hAdd k k k
                            (@instHAdd k
                              (@Distrib.toAdd k
                                (@instDistribOfSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                            (κ b)
                            (@Nat.cast k
                              (@AddMonoidWithOne.toNatCast k
                                (@AddGroupWithOne.toAddMonoidWithOne k
                                  (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst))))
                              r))
                          (@OfNat.ofNat k (nat_lit 1)
                            (@One.toOfNat1 k
                              (@AddMonoidWithOne.toOne k
                                (@AddGroupWithOne.toAddMonoidWithOne k
                                  (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst)))))))
                        (@HMul.hMul k k k
                          (@instHMul k
                            (@Distrib.toMul k
                              (@instDistribOfSemiring k (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k inst)))))
                          (@OfNat.ofNat k (nat_lit 2)
                            (@instOfNatAtLeastTwo k (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast k
                                (@AddGroupWithOne.toAddMonoidWithOne k
                                  (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst))))
                              UpperTheory.Reformulated.B.InnerProductFormulaField.aux2))
                          (@Nat.cast k
                            (@AddMonoidWithOne.toNatCast k
                              (@AddGroupWithOne.toAddMonoidWithOne k (@Ring.toAddGroupWithOne k (@CommRing.toRing k inst))))
                            (@Fin.val r b)))))
                  v)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LowerIff
section
theorem UpperTheory.Reformulated.B.Re1.lower_iff :
    ∀ {n : ℕ} (P : Fin n → Prop) [inst : DecidablePred P],
    (∀ (a b : Fin n), a ≤ b → P b → P a) → ∀ (b : Fin n), P b ↔ (↑b : ℕ) < (Finset.filter P Finset.univ).card := by
  intro n P _ h b
  exact (Fin.lt_card_filter_univ_iff_apply_of_imp P (fun i j hij => h j i hij)).symm
end

