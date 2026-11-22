import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestRest
section
namespace ZbYhc5Helpers

private lemma key {g : ℕ} (c : ℂ) (u u' : Fin g → ℂ) :
    c • (u + Complex.I • u') = (c.re • u - c.im • u') + Complex.I • (c.im • u + c.re • u') := by
  funext i
  apply Complex.ext <;> simp [Complex.real_smul] <;> ring

end ZbYhc5Helpers

theorem UpperTheory.Reformulated.B.Yhc5.main :
    ∀ {g : ℕ} {T : Set (Fin g → ℂ)} {w : Fin g → ℂ},
      w ∈ Submodule.span ℂ T → ∃ u ∈ Submodule.span ℝ T, ∃ u' ∈ Submodule.span ℝ T, w = u + Complex.I • u' := by
  intro g T w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨x, Submodule.subset_span hx, 0, Submodule.zero_mem _, by simp⟩
  | zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, a', ha', rfl⟩ := hx
    obtain ⟨b, hb, b', hb', rfl⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb', by
      rw [smul_add]; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, a', ha', rfl⟩ := hx
    refine ⟨c.re • a - c.im • a', ?_, c.im • a + c.re • a', ?_, ZbYhc5Helpers.key c a a'⟩
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailTer
section
theorem UpperTheory.Reformulated.B.Yra3.main :
    ∀ {R L : Type} [inst : CommRing R] [inst_1 : CommRing L] (φ : R →+* L),
      (∀ (z : L), ∃ (a : R) (b : R), IsUnit ((φ : R → L) b) ∧ z * (φ : R → L) b = (φ : R → L) a) →
        ∀ (s : Finset L), ∃ (b : R), IsUnit ((φ : R → L) b) ∧ ∀ z ∈ s, z * (φ : R → L) b ∈ Set.range (⇑φ : R → L) := by
  intro R L _ _ φ h s
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert z s _ ih =>
    obtain ⟨b0, hb0, hs⟩ := ih
    obtain ⟨a, b, hb, hz⟩ := h z
    refine ⟨b0 * b, by rw [map_mul]; exact hb0.mul hb, ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · refine ⟨a * b0, ?_⟩
      rw [map_mul, map_mul, ← hz]; ring
    · obtain ⟨c, hc⟩ := hs w hw
      refine ⟨c * b, ?_⟩
      rw [map_mul, map_mul, hc]; ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTer
section
theorem UpperTheory.Reformulated.B.DYdc5.main.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (P : Ideal R) [hP : P.IsPrime] (t : ℕ),
      t ≠ (0 : ℕ) → (↑t : R) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ t ∧ (↑p : R) ∈ P := by
  intro R _ P hP t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht hmem
    have h1 : t ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by simpa using hmem))
    obtain ⟨p, hp, k, rfl⟩ := Nat.exists_prime_and_dvd h1
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact ⟨p, hp, dvd_mul_right p k, h⟩
    · have hk : k ≠ 0 := by
        rintro rfl
        simp at ht
      have hlt : k < p * k :=
        lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hk) hp.one_lt
      obtain ⟨q, hq, hqk, hqP⟩ := ih k hlt hk h
      exact ⟨q, hq, hqk.mul_left p, hqP⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerAlt
section
noncomputable def UpperTheory.Reformulated.B.PadicComplexIntegerSubring.intSub :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] := fun p _ =>
  { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
    mul_mem' := fun {a b} ha hb => by
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      rw [norm_mul]
      exact mul_le_one₀ ha (norm_nonneg b) hb
    one_mem' := by
      simp only [Set.mem_setOf_eq, norm_one, le_refl]
    add_mem' := fun {a b} ha hb => by
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
    zero_mem' := by
      simp only [Set.mem_setOf_eq, norm_zero, zero_le_one]
    neg_mem' := fun {a} ha => by
      simp only [Set.mem_setOf_eq] at ha ⊢
      rwa [norm_neg] }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerBis
section
noncomputable def UpperTheory.Reformulated.B.PadicComplexRingOfIntegers.intRing :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] :=
  fun p _ =>
    { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : ℂ_[p])‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha' hb')
      zero_mem' := by
        show ‖(0 : ℂ_[p])‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rwa [norm_neg] }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerLast
section
theorem UpperTheory.Reformulated.B.Qf31.isCompact_box :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
    [ProperSpace L] (c : Matrix (Fin m) (Fin m) L) (r : ℝ),
    IsCompact
      {g : GL (Fin m) L |
        (∀ (i j : Fin m), ‖(↑g : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r) ∧
          ∀ (i j : Fin m), ‖(↑g⁻¹ : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r} := by
  intro L _ _ m _ c r
  have hK : IsCompact {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} := by
    have h : IsCompact (Set.univ.pi fun i : Fin m =>
        Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall (c i j) r
    have e : {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} =
        (Set.univ.pi fun i : Fin m =>
          Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) := by
      ext A
      constructor
      · intro hA i _ j _
        exact mem_closedBall_iff_norm.2 (hA i j)
      · intro hA i j
        exact mem_closedBall_iff_norm.1 (hA i (Set.mem_univ i) j (Set.mem_univ j))
    rw [e]
    exact h
  have hK' : IsCompact (MulOpposite.unop ⁻¹'
      {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r}) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin m) (Fin m) L)).symm.isCompact_preimage.2 hK
  exact (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin m) (Fin m) L)).isCompact_preimage (hK.prod hK')
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerRest
section
noncomputable def UpperTheory.Reformulated.B.Qe31.Statement :
    Prop :=
    ∀ (T : Type) [inst : CommRing T] [IsNoetherianRing T] (P : Ideal T) [inst_2 : P.IsPrime] (h : ℕ) (f : Fin h → T),
      (∀ (i : Fin h), f i ∈ P) →
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
            Ideal.span
                (Set.range fun (i : Fin h) ↦
                  (Algebra.algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) ⊔
              IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ (2 : ℕ) →
          ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)

theorem UpperTheory.Reformulated.B.Qe31.proof :
    UpperTheory.Reformulated.B.Qe31.Statement := by
  intro T _ _ P _ h f _ hle
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
      Ideal.span (Set.range fun (i : Fin h) ↦
        (algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    rwa [smul_eq_mul, ← pow_two]
  have hI : Ideal.span (Set.range fun (i : Fin h) ↦
        (algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) =
      (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime P)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have key : ∀ x ∈ P, ∃ s ∉ P, s * x ∈ Ideal.span (Set.range f) := by
    intro x hx
    have h1 : algebraMap T (Localization.AtPrime P) x ∈
        (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime P)) := by
      rw [← hI]
      apply hm
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩ :=
      (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).1 h1
    rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hab
    obtain ⟨⟨c, hc⟩, hcab⟩ := hab
    refine ⟨c * b, P.primeCompl.mul_mem hc hb, ?_⟩
    have : c * b * x = c * a := by
      simp only at hcab
      rw [← hcab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian P
  have hSP : ∀ x ∈ S, x ∈ P := fun x hx ↦ hS ▸ Submodule.subset_span hx
  choose! g hg1 hg2 using key
  refine ⟨∏ y ∈ S, g y, P.primeCompl.prod_mem (fun y hy ↦ hg1 y (hSP y hy)), ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g hy
    rw [hc, mul_comm (g y) c, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hg2 y (hSP y hy))
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact Ideal.add_mem _ ha hb
  | smul c a _ ha =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerSide
section
theorem UpperTheory.Reformulated.B.Qf12.lift_ex :
    ∀ {A M Q Q' : Type} [inst : CommRing A] [inst_1 : AddCommGroup M]
    [inst_2 : AddCommGroup Q] [inst_3 : AddCommGroup Q'] [inst_4 : _root_.Module A M] [inst_5 : _root_.Module A Q]
    [inst_6 : _root_.Module A Q'] (π : M →ₗ[A] Q),
    Function.Surjective (⇑π : M → Q) →
      ∀ (g : M →ₗ[A] Q'),
        (∀ (m : M), (π : M → Q) m = (0 : Q) → (g : M → Q') m = (0 : Q')) →
          ∃ (q : Q →ₗ[A] Q'), ∀ (m : M), (q : Q → Q') ((π : M → Q) m) = (g : M → Q') m := by
  intro A M Q Q' _ _ _ _ _ _ _ π hπ g hg
  have hle : LinearMap.ker π ≤ LinearMap.ker g := fun m hm =>
    LinearMap.mem_ker.mpr (hg m (LinearMap.mem_ker.mp hm))
  refine ⟨((LinearMap.ker π).liftQ g hle).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, fun m => ?_⟩
  have h : (π.quotKerEquivOfSurjective hπ).symm (π m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerTail
section
theorem UpperTheory.Reformulated.B.Qf13.pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω _ A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = (a ^ n - b ^ n) * a + (a - b) * b ^ n := by ring
    rw [e]
    refine A.valuation.map_add_lt ?_ ?_
    · rw [map_mul]
      calc A.valuation (a ^ n - b ^ n) * A.valuation a
          ≤ A.valuation (a ^ n - b ^ n) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
    · rw [map_mul, map_pow]
      have hb' : A.valuation b ^ n ≤ 1 := pow_le_one' hb n
      calc A.valuation (a - b) * A.valuation b ^ n
          ≤ A.valuation (a - b) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerTer
section
noncomputable def UpperTheory.Reformulated.B.PadicComplexValuationRing.intS (p : ℕ) [inst : Fact (Nat.Prime p)] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  mul_mem' := fun {a b} ha hb =>
    (norm_mul_le a b).trans (mul_le_one₀ ha (norm_nonneg b) hb)
  neg_mem' := fun {a} ha => by
    simpa only [Set.mem_setOf_eq, norm_neg] using ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InPApplyEqZero
section
noncomputable def UpperTheory.Reformulated.B.Qh16.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qh16.inG :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) ↦
      X.conjTranspose * UpperTheory.Reformulated.B.Qh16.Jm ε + UpperTheory.Reformulated.B.Qh16.Jm ε * X = (0 : Matrix (Fin n) (Fin n) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qh16.inP :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) ↦
      UpperTheory.Reformulated.B.Qh16.inG ε X ∧ X * UpperTheory.Reformulated.B.Qh16.Jm ε = -(UpperTheory.Reformulated.B.Qh16.Jm ε * X)

theorem UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero :
    ∀ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ},
      UpperTheory.Reformulated.B.Qh16.inP ε X → ∀ {a b : Fin n}, ε a = ε b → X a b = (0 : ℂ) := by
  intro n ε X h a b hab
  have h1 := congrFun (congrFun h.2 a) b
  unfold UpperTheory.Reformulated.B.Qh16.Jm at h1
  rw [Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hab] at h1
  split_ifs at h1
  · linear_combination (1 / 2 : ℂ) * h1
  · linear_combination (-1 / 2 : ℂ) * h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InclR
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh24.Fv :
    (F : Type) →
      [inst : Field F] → [NumberField F] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → Type :=
    fun (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

theorem UpperTheory.Reformulated.B.Qh24.aux2 :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      SubsemiringClass (ValuationSubring (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v))
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) := by
  intros
  infer_instance

noncomputable def UpperTheory.Reformulated.B.Qh24.inclR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] → (R : Type) → [inst_3 : CommRing R] → [inst_4 : Algebra F R] → E →+* TensorProduct F R E :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] ↦
      Algebra.TensorProduct.includeRight.toRingHom

noncomputable def UpperTheory.Reformulated.B.Qh24.OEv :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          [inst_2 : Field E] →
            [inst_3 : Algebra F E] →
              (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
                Set (TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E) :=
    fun {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
        (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      (↑(Submodule.span (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v))
            ((fun (x : NumberField.RingOfIntegers E) ↦
                (UpperTheory.Reformulated.B.Qh24.inclR (UpperTheory.Reformulated.B.Qh24.Fv F v) : E → TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E)
                  (↑x : E)) ''
              Set.univ)) :
        Set (TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E))

theorem UpperTheory.Reformulated.B.Qh24.oev_mul :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      {s t : TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E},
      s ∈ UpperTheory.Reformulated.B.Qh24.OEv v → t ∈ UpperTheory.Reformulated.B.Qh24.OEv v → s * t ∈ UpperTheory.Reformulated.B.Qh24.OEv v := by
  intro F E _ _ _ _ _ v s t hs ht
  unfold UpperTheory.Reformulated.B.Qh24.OEv at *
  simp only [SetLike.mem_coe] at *
  induction hs using Submodule.span_induction with
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha
  | mem a ha =>
    induction ht using Submodule.span_induction with
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
    | mem b hb =>
      obtain ⟨x, -, rfl⟩ := ha
      obtain ⟨y, -, rfl⟩ := hb
      refine Submodule.subset_span ⟨x * y, Set.mem_univ _, ?_⟩
      beta_reduce
      rw [← map_mul]
      rfl
end

