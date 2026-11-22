import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AlgebraSmulCommClassComplex
section
noncomputable def UpperTheory.Reformulated.B.Qe25.OmX :
    (m : ℕ) → Set (Fin m → ℂ) :=
    fun (m : ℕ) ↦ {x : Fin m → ℂ | ∀ (l : Fin m), x l ≠ (0 : ℂ)}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe25.Mx :
    ℕ → ℕ → Type :=
    fun (k r : ℕ) ↦ Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe25.Fn.{u_2} :
    ℕ → ℕ → Type u_2 → Type u_2 :=
    fun (k r : ℕ) (E : Type u_2) ↦ (Fin r → ℂ) → UpperTheory.Reformulated.B.Qe25.Mx k r → E

noncomputable def UpperTheory.Reformulated.B.Qe25.Mdim :
    ℕ → (r : ℕ) → Fin r → ℕ :=
    fun (k r : ℕ) (a : Fin r) ↦ (2 : ℕ) * (r - (↑a : ℕ)) + k + (1 : ℕ)

theorem UpperTheory.Reformulated.B.Qe25.aux5 :
    ∀ (k r : ℕ) (a : Fin r), (2 : ℕ) * r + k - (↑a : ℕ) < (2 : ℕ) * r + k + (1 : ℕ) := by
  intro k r a
  omega

noncomputable def UpperTheory.Reformulated.B.Qe25.esI :
    (k r : ℕ) → Fin r → Fin ((2 : ℕ) * r + k + (1 : ℕ)) :=
    fun (k r : ℕ) (a : Fin r) ↦
      (⟨(2 : ℕ) * r + k - (↑a : ℕ), UpperTheory.Reformulated.B.Qe25.aux5 k r a⟩ : Fin ((2 : ℕ) * r + k + (1 : ℕ)))

theorem UpperTheory.Reformulated.B.Qe25.aux7 :
    ∀ (k r : ℕ) (a : Fin r), (↑a : ℕ) < (2 : ℕ) * r + k + (1 : ℕ) := by
  intro k r a
  have := a.isLt
  omega

noncomputable def UpperTheory.Reformulated.B.Qe25.eI :
    (k r : ℕ) → Fin r → Fin ((2 : ℕ) * r + k + (1 : ℕ)) :=
    fun (k r : ℕ) (a : Fin r) ↦ (⟨(↑a : ℕ), UpperTheory.Reformulated.B.Qe25.aux7 k r a⟩ : Fin ((2 : ℕ) * r + k + (1 : ℕ)))

noncomputable def UpperTheory.Reformulated.B.Qe25.w1 :
    (k r : ℕ) → Fin r → ℂ → UpperTheory.Reformulated.B.Qe25.Mx k r :=
    fun (k r : ℕ) (l : Fin r) (c : ℂ) (p q : Fin ((2 : ℕ) * r + k + (1 : ℕ))) ↦
      if p = UpperTheory.Reformulated.B.Qe25.esI k r l ∧ q = UpperTheory.Reformulated.B.Qe25.eI k r l then c
      else
        if p = UpperTheory.Reformulated.B.Qe25.eI k r l ∧ q = UpperTheory.Reformulated.B.Qe25.esI k r l then (Star.star c)⁻¹
        else if p = q ∧ p ≠ UpperTheory.Reformulated.B.Qe25.eI k r l ∧ p ≠ UpperTheory.Reformulated.B.Qe25.esI k r l then (1 : ℂ) else (0 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qe25.wCell :
    (k r : ℕ) → Fin (r + (1 : ℕ)) → (Fin r → ℂ) → UpperTheory.Reformulated.B.Qe25.Mx k r :=
    fun (k r : ℕ) (i : Fin (r + (1 : ℕ))) (c : Fin r → ℂ) ↦
      (List.map (fun (a : Fin r) ↦ UpperTheory.Reformulated.B.Qe25.w1 k r a (c a))
          (List.filter (fun (a : Fin r) ↦ Decidable.decide ((↑a : ℕ) < (↑i : ℕ))) (List.finRange r))).prod

noncomputable def UpperTheory.Reformulated.B.Qe25.resG.{u_1} :
    {E : Type u_1} →
      [inst : NormedAddCommGroup E] →
        [NormedSpace ℂ E] → (k r : ℕ) → Fin (r + (1 : ℕ)) → (UpperTheory.Reformulated.B.Qe25.Mx k r → E) → UpperTheory.Reformulated.B.Qe25.Fn k r E :=
    fun {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + (1 : ℕ)))
        (J : UpperTheory.Reformulated.B.Qe25.Mx k r → E) (c : Fin r → ℂ) (g : UpperTheory.Reformulated.B.Qe25.Mx k r) ↦
      (↑(∏ a : Fin r, if (↑a : ℕ) < (↑i : ℕ) then ‖c a‖ ^ (UpperTheory.Reformulated.B.Qe25.Mdim k r a - (1 : ℕ)) else (1 : ℝ)) : ℂ) •
        J (UpperTheory.Reformulated.B.Qe25.wCell k r i c * g)

noncomputable def UpperTheory.Reformulated.B.Qe25.gaugeF :
    ℕ → (r : ℕ) → (Fin r → ℂ) → ℂ :=
    fun (k r : ℕ) (c : Fin r → ℂ) ↦
      UpperTheory.Reformulated.B.Qe25.resG k r (Fin.last r) (fun (x : UpperTheory.Reformulated.B.Qe25.Mx k r) ↦ (1 : ℂ)) c (1 : UpperTheory.Reformulated.B.Qe25.Mx k r)

theorem UpperTheory.Reformulated.B.Qe25.algebra_smulCommClass_complex.{u_1} :
    ∀ (m : ℕ) (E : Type u_1) [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {f g : (Fin m → ℂ) → E},
      f ∈
          {f : (Fin m → ℂ) → E |
            ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (UpperTheory.Reformulated.B.Qe25.OmX m) ∧ ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, f x = (0 : E)} →
        g ∈
            {f : (Fin m → ℂ) → E |
              ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (UpperTheory.Reformulated.B.Qe25.OmX m) ∧ ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, f x = (0 : E)} →
          ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f + g) (UpperTheory.Reformulated.B.Qe25.OmX m) ∧
            ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, (f + g) x = (0 : E) := by
  intro m E _ _ f g hf hg
  exact ⟨hf.1.add hg.1, fun x hx ↦ by simp [hf.2 x hx, hg.2 x hx]⟩

theorem UpperTheory.Reformulated.B.Qe25.zero_contDiffOn_supported.{u_1} :
    ∀ (m : ℕ) (E : Type u_1) [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E],
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (0 : (Fin m → ℂ) → E) (UpperTheory.Reformulated.B.Qe25.OmX m) ∧
        ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, (0 : (Fin m → ℂ) → E) x = (0 : E) := by
  intro m E _ _
  exact ⟨contDiffOn_const, fun _ _ ↦ rfl⟩

theorem UpperTheory.Reformulated.B.Qe25.sign_action_map_comm.{u_1} :
    ∀ (m : ℕ) (E : Type u_1) [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] (a : ℂ) {f : (Fin m → ℂ) → E},
      f ∈
          {f : (Fin m → ℂ) → E |
            ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (UpperTheory.Reformulated.B.Qe25.OmX m) ∧ ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, f x = (0 : E)} →
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a • f) (UpperTheory.Reformulated.B.Qe25.OmX m) ∧ ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, (a • f) x = (0 : E) := by
  intro m E _ _ a f hf
  exact ⟨hf.1.const_smul a, fun x hx ↦ by simp [hf.2 x hx]⟩

noncomputable def UpperTheory.Reformulated.B.Qe25.WSm.{u_1} :
    (m : ℕ) → (E : Type u_1) → [inst : NormedAddCommGroup E] → [inst_1 : NormedSpace ℂ E] → Submodule ℂ ((Fin m → ℂ) → E) :=
    fun (m : ℕ) (E : Type u_1) [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] ↦
      {
        carrier :=
          {f : (Fin m → ℂ) → E |
            ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (UpperTheory.Reformulated.B.Qe25.OmX m) ∧ ∀ x ∉ UpperTheory.Reformulated.B.Qe25.OmX m, f x = (0 : E)},
        add_mem' := @UpperTheory.Reformulated.B.Qe25.algebra_smulCommClass_complex m E inst inst_1, zero_mem' := UpperTheory.Reformulated.B.Qe25.zero_contDiffOn_supported m E,
        smul_mem' := UpperTheory.Reformulated.B.Qe25.sign_action_map_comm m E : Submodule ℂ ((Fin m → ℂ) → E) }

private theorem UpperTheory.Reformulated.B.Qe25.gauge_eq (k r : ℕ) (c : Fin r → ℂ) :
    UpperTheory.Reformulated.B.Qe25.gaugeF k r c =
      ((∏ a : Fin r, ‖c a‖ ^ (UpperTheory.Reformulated.B.Qe25.Mdim k r a - 1) : ℝ) : ℂ) := by
  simp [UpperTheory.Reformulated.B.Qe25.gaugeF, UpperTheory.Reformulated.B.Qe25.resG]

private theorem UpperTheory.Reformulated.B.Qe25.gauge_ne (k r : ℕ) (c : Fin r → ℂ)
    (hc : c ∈ UpperTheory.Reformulated.B.Qe25.OmX r) : UpperTheory.Reformulated.B.Qe25.gaugeF k r c ≠ 0 := by
  rw [UpperTheory.Reformulated.B.Qe25.gauge_eq, Complex.ofReal_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun a _ ↦ pow_ne_zero _ (norm_ne_zero_iff.2 (hc a))

private theorem UpperTheory.Reformulated.B.Qe25.gauge_smooth (k r : ℕ) (c : Fin r → ℂ)
    (hc : c ∈ UpperTheory.Reformulated.B.Qe25.OmX r) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (UpperTheory.Reformulated.B.Qe25.gaugeF k r) c := by
  have h : UpperTheory.Reformulated.B.Qe25.gaugeF k r = fun c ↦ Complex.ofRealCLM
      (∏ a : Fin r, ‖c a‖ ^ (UpperTheory.Reformulated.B.Qe25.Mdim k r a - 1)) :=
    funext fun c ↦ UpperTheory.Reformulated.B.Qe25.gauge_eq k r c
  rw [h]
  refine Complex.ofRealCLM.contDiff.contDiffAt.comp c (contDiffAt_prod fun a _ ↦ ?_)
  exact (ContDiffAt.norm ℝ (contDiffAt_apply ℝ ℂ a c) (hc a)).pow _

theorem UpperTheory.Reformulated.B.Qe25.loc :
    ∀ {X : Type} [inst : NormedAddCommGroup X] [inst_1 : NormedSpace ℂ X] {k r : ℕ} (Φ : (Fin r → ℂ) → X)
      (U : Set (Fin r → ℂ)) (c : Fin r → ℂ),
      IsOpen U →
        U ⊆ UpperTheory.Reformulated.B.Qe25.OmX r →
          c ∈ U →
            ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun (c' : Fin r → ℂ) ↦ UpperTheory.Reformulated.B.Qe25.gaugeF k r c' • Φ c') U →
              ∃ φ ∈ UpperTheory.Reformulated.B.Qe25.WSm r X,
                Φ =ᶠ[nhds c] φ ∧
                  (fun (c' : Fin r → ℂ) ↦ UpperTheory.Reformulated.B.Qe25.gaugeF k r c' • Φ c') =ᶠ[nhds c] fun (c' : Fin r → ℂ) ↦
                    UpperTheory.Reformulated.B.Qe25.gaugeF k r c' • φ c' := by
  intro X _ _ k r Φ U c hU hUO hc hs
  have hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ U := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun c' ↦ (UpperTheory.Reformulated.B.Qe25.gaugeF k r c')⁻¹) U := fun x hx ↦
      ((UpperTheory.Reformulated.B.Qe25.gauge_smooth k r x (hUO hx)).inv
        (UpperTheory.Reformulated.B.Qe25.gauge_ne k r x (hUO hx))).contDiffWithinAt
    refine (h1.smul hs).congr fun x hx ↦ ?_
    simp only [Pi.smul_apply']
    rw [smul_smul, inv_mul_cancel₀ (UpperTheory.Reformulated.B.Qe25.gauge_ne k r x (hUO hx)), one_smul]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU c hc
  let b : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hsupp : tsupport b ⊆ U := by
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show ε / 2 < ε by linarith)).trans hball
  have heq : Φ =ᶠ[nhds c] fun x ↦ b x • Φ x := by
    filter_upwards [b.eventuallyEq_one] with x hx
    simp [hx]
  refine ⟨fun x ↦ b x • Φ x, ⟨fun x _ ↦ ?_, fun x hx ↦ ?_⟩, heq, ?_⟩
  · by_cases hxU : x ∈ U
    · exact (b.contDiff.contDiffAt.smul (hΦ.contDiffAt (hU.mem_nhds hxU))).contDiffWithinAt
    · have h0 : (b : (Fin r → ℂ) → ℝ) =ᶠ[nhds x] 0 :=
        notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hxU (hsupp h)
      have h1 : (fun x ↦ b x • Φ x) =ᶠ[nhds x] fun _ ↦ (0 : X) := by
        filter_upwards [h0] with y hy
        simp [hy]
      exact (contDiffAt_const.congr_of_eventuallyEq h1).contDiffWithinAt
  · have h0 : b x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hUO (hsupp h))
    simp [h0]
  · filter_upwards [heq] with x hx
    rw [← hx]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AlgebraicPointIntegral
section
open Polynomial

private theorem UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (p : O[X])
    (hp : ∃ i, p.coeff i ∉ IsLocalRing.maximalIdeal O) :
    ∃ g q : O[X], g.Monic ∧ IsUnit (q.coeff 0) ∧ p = g * q := by
  have h0 : (p : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    obtain ⟨i, hi⟩ := hp
    intro h
    apply hi
    have := congrArg (PowerSeries.coeff i) h
    rwa [PowerSeries.coeff_map, Polynomial.coeff_coe, map_zero,
      IsLocalRing.residue_eq_zero_iff] at this
  obtain ⟨g, h, hg, hh, e⟩ := PowerSeries.exists_isWeierstrassFactorization h0
  have hI : IsLocalRing.maximalIdeal O ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hd := hg.isWeierstrassDivisorAt hI
  have hn : (((g : PowerSeries O).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat) = g.natDegree := by
    rw [← hg.coe_natDegree_eq_order_map (g : PowerSeries O) 1
      (by rwa [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)]
    simp
  have hdeg : g.degree = g.natDegree := Polynomial.degree_eq_natDegree hg.monic.ne_zero
  have e2 := Polynomial.modByMonic_add_div p g
  have key := hd.eq_of_mul_add_eq_mul_add (q := h) (q' := ((p /ₘ g : O[X]) : PowerSeries O))
    (r := 0) (r' := p %ₘ g)
    (by rw [hn, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _)
    (by rw [hn, ← hdeg]; exact Polynomial.degree_modByMonic_lt p hg.monic)
    (by
      rw [← e, Polynomial.coe_zero, add_zero, ← Polynomial.coe_mul, ← Polynomial.coe_add,
        add_comm, e2])
  refine ⟨g, p /ₘ g, hg.monic, ?_, ?_⟩
  · have := PowerSeries.isUnit_iff_constantCoeff.1 hh
    rw [key.1] at this
    simpa using this
  · rw [← key.2, zero_add] at e2
    exact e2.symm

theorem UpperTheory.Reformulated.B.AlgebraicPointIntegral.algpt_int :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O]
    [inst_2 : IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {R : Type} [inst_4 : CommRing R]
    [inst_5 : Algebra O R] [inst_6 : IsLocalRing R] {K : Type} [inst_7 : Field K] [inst_8 : Algebra O K]
    [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K),
    ∀ a ∈ IsLocalRing.maximalIdeal R, IsIntegral O ((f : R → K) a) := by
  intro O _ _ _ _ R _ _ _ K _ _ _ _ f a ha
  classical
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := O) (f a)
  obtain ⟨inst⟩ : Nonempty (NormalizedGCDMonoid O) := inferInstance
  have h1 : aeval (f a) p.primPart = 0 := aeval_primPart_eq_zero hp0 hp
  have h2 : ∃ i, p.primPart.coeff i ∉ IsLocalRing.maximalIdeal O := by
    by_contra hc
    push Not at hc
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    apply hϖ.not_isUnit
    apply isPrimitive_iff_isUnit_of_C_dvd.1 p.isPrimitive_primPart
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have := hc i
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  obtain ⟨g, q, hg, hq, e⟩ := UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor _ h2
  have h3 : IsUnit (aeval a q) := by
    by_contra hu
    have hm : aeval a q ∈ IsLocalRing.maximalIdeal R := hu
    have e3 : aeval a q = aeval a q.divX * a + algebraMap O R (q.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add q]
      simp
    rw [e3, Ideal.add_mem_iff_right _ (Ideal.mul_mem_left _ _ ha)] at hm
    exact hm (hq.map _)
  have h4 : aeval (f a) q ≠ 0 := by
    rw [aeval_algHom_apply]
    exact (h3.map f).ne_zero
  rw [e, map_mul] at h1
  exact ⟨g, hg, (mul_eq_zero.1 h1).resolve_right h4⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalConjugation
section
noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp [UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat, Matrix.one_apply, eq_comm]
  · intro b _ hb
    simp [UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat, hb]
  · simp

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m, inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m, val_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux4 g,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self {R : Type*} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.AntidiagonalConjugation.aux2 m)

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (g * h) = UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g * UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv g) = g :=
  Units.ext (Matrix.transpose_transpose (↑g : Matrix n n R))

private theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_Jgl {R : Type*} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m) = UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m).transpose = UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.AntidiagonalConjugation.Jmat]
  refine if_congr ⟨?_, ?_⟩ rfl rfl <;> rintro rfl <;> simp

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.AntidiagonalConjugation.theta (UpperTheory.Reformulated.B.AntidiagonalConjugation.theta g) = g := by
  intro m R _ g
  simp only [UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_trInv,
    UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_Jgl]
  rw [mul_assoc, mul_assoc, mul_assoc, UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, mul_one, ← mul_assoc,
    UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, one_mul]

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.AntidiagonalConjugation.theta (g * h) = UpperTheory.Reformulated.B.AntidiagonalConjugation.theta g * UpperTheory.Reformulated.B.AntidiagonalConjugation.theta h := by
  intro m R _ g h
  simp only [UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, UpperTheory.Reformulated.B.AntidiagonalConjugation.trInv_mul, mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m) (UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl R m), UpperTheory.Reformulated.B.AntidiagonalConjugation.Jgl_mul_self, one_mul]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, invFun := UpperTheory.Reformulated.B.AntidiagonalConjugation.theta, left_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8,
        right_inv := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8, map_mul' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R := by
  intro m R _ s t
  have hsq : UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R * UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R = 1 :=
    MulEquiv.ext fun g => UpperTheory.Reformulated.B.AntidiagonalConjugation.aux8 g
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp [hne, hsq]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalConjugation.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux11 m R, map_mul' := UpperTheory.Reformulated.B.AntidiagonalConjugation.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) → G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R → MulAut (UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R))
              ((UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy_left :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.AntidiagonalConjugation.conjBy h r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).left =
        h * ((r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).left *
          ((UpperTheory.Reformulated.B.AntidiagonalConjugation.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) ((r : G → UpperTheory.Reformulated.B.AntidiagonalConjugation.GG m R) g).right :
              GL (Fin m) R → GL (Fin m) R)
            h⁻¹ := by
  intro G R _ _ m h r g
  change (UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL h * r g * (UpperTheory.Reformulated.B.AntidiagonalConjugation.ofGL h)⁻¹).left = _
  rw [← map_inv, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, one_mul,
    MulAut.one_apply]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ArithmeticCylinders
section
theorem UpperTheory.Reformulated.B.ArithmeticCylinders.eigen_pow_eq_one :
    ∀ {L : Type} [inst : Field L] {d : Type} [inst_1 : Fintype d] [inst_2 : DecidableEq d]
    (M : Matrix d d L) (n : ℕ), M ^ n = (1 : Matrix d d L) → ∀ (μ : L), M.charpoly.IsRoot μ → μ ^ n = (1 : L) := by
  intro L _ d _ _ M n hM μ hμ
  have h1 : μ ∈ spectrum L M := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hμ
  have h2 : μ ^ n ∈ spectrum L (M ^ n) := spectrum.pow_mem_pow M n h1
  rw [hM, spectrum.mem_iff] at h2
  by_contra hne
  apply h2
  have hu : IsUnit (μ ^ n - 1) := (sub_ne_zero.mpr hne).isUnit
  have h3 := hu.map (algebraMap L (Matrix d d L))
  rwa [map_sub, map_one] at h3
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Artin
section
theorem UpperTheory.Reformulated.B.Qh30.artin :
    ∀ {P : Type} [inst : Mul P] (T : Finset (P → ℂ))
    (c : (P → ℂ) → ℂ),
    (∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q) →
      (∀ (p : P), ∑ χ ∈ T, c χ * χ p = (0 : ℂ)) → ∀ χ ∈ T, c χ = (0 : ℂ) := by
  intro P inst T
  classical
  induction T using Finset.induction_on with
  | empty => intro c _ _ χ hχ; simp at hχ
  | insert ψ T hψ ih =>
    intro c hT h
    have hψm := hT ψ (Finset.mem_insert_self ψ T)
    have hT' : ∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q :=
      fun χ hχ => hT χ (Finset.mem_insert_of_mem hχ)
    have key : ∀ q : P, ∀ χ ∈ T, c χ * (χ q - ψ q) = 0 := by
      intro q
      refine ih (fun χ => c χ * (χ q - ψ q)) hT' ?_
      intro p
      have h1 := h (q * p)
      have h2 := h p
      rw [Finset.sum_insert hψ] at h1 h2
      have h3 : ∑ χ ∈ T, c χ * (χ q - ψ q) * χ p
          = ∑ χ ∈ T, c χ * χ (q * p) - ψ q * ∑ χ ∈ T, c χ * χ p := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [(hT' χ hχ).2]
        ring
      rw [hψm.2] at h1
      rw [h3]
      linear_combination h1 - ψ q * h2
    have hc : ∀ χ ∈ T, c χ = 0 := by
      intro χ hχ
      by_contra hne
      have : χ = ψ := by
        funext q
        exact sub_eq_zero.mp ((mul_eq_zero.mp (key q χ hχ)).resolve_left hne)
      exact hψ (this ▸ hχ)
    have hcψ : c ψ = 0 := by
      by_contra hne
      apply hψm.1
      funext p
      have h2 := h p
      rw [Finset.sum_insert hψ, Finset.sum_eq_zero (fun χ hχ => by rw [hc χ hχ, zero_mul]),
        add_zero] at h2
      exact (mul_eq_zero.mp h2).resolve_left hne
    intro χ hχ
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact hcψ
    · exact hc χ hχ
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AuxiliaryNormPrimes
section
noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyNu.{u_1} :
    {L : Type u_1} → [NormedField L] → Multiset L → ℝ :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦
      (Multiset.map (fun (z : L) ↦ ‖z‖) (Multiset.filter (fun (z : L) ↦ (1 : ℝ) ≤ ‖z‖) R)).prod

noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyF.{u_1} :
    {L : Type u_1} → [inst : NormedField L] → Multiset L → Polynomial L :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦
      (Multiset.map (fun (z : L) ↦ Polynomial.X - (Polynomial.C : L → Polynomial L) z) R).prod

noncomputable def UpperTheory.Reformulated.B.AuxiliaryNormPrimes.gtpolyP.{u_1} :
    {L : Type u_1} → [NormedField L] → Multiset L → Multiset L :=
    fun {L : Type u_1} [NormedField L] (R : Multiset L) ↦ Multiset.filter (fun (z : L) ↦ ‖z‖ < (1 : ℝ)) R

private theorem UpperTheory.Reformulated.B.AuxiliaryNormPrimes.norm_sub_le_max' {L : Type*} [NormedField L] [IsUltrametricDist L]
    (x y : L) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [norm_neg, ← sub_eq_add_neg] at h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BiHomSum
section
noncomputable def UpperTheory.Reformulated.B.Qf22.biHom :
    {K ι κ : Type} → [inst : Field K] → ℕ → MvPolynomial κ (MvPolynomial ι K) → Prop :=
    fun {K ι κ : Type} [Field K] (d : ℕ) (F : MvPolynomial κ (MvPolynomial ι K)) ↦
      ∀ (β : κ →₀ ℕ) (n : ι →₀ ℕ),
        MvPolynomial.coeff n (MvPolynomial.coeff β F) ≠ (0 : K) →
          (Finsupp.degree : (ι →₀ ℕ) → ℕ) n + (Finsupp.degree : (κ →₀ ℕ) → ℕ) β = d

theorem UpperTheory.Reformulated.B.Qf22.biHom_sum.{u_1} :
    ∀ {K ι κ : Type} [inst : Field K] [Fintype κ] {α : Type u_1} {d : ℕ} (s : Finset α)
      (F : α → MvPolynomial κ (MvPolynomial ι K)),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf22.biHom d (F a)) → UpperTheory.Reformulated.B.Qf22.biHom d (∑ a ∈ s, F a) := by
  intro K ι κ _ _ α d s F h β n hne
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum] at hne
  obtain ⟨a, ha, hna⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h a ha β n hna
end

