import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqAdjointAddGeOfJointEigenspaces
section
namespace GlobalTheory

open scoped InnerProductSpace

theorem norm_sq_adjoint_add_ge_of_joint_eigenspaces (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (ι : Type) (S : ι → Submodule ℂ V) (A : Vp →L[ℂ] V) (B : Vm →L[ℂ] V) (wp wm : ι → ℝ) (c : ℝ) (hS : (⨆ i, S i) = ⊤)
    (hw : ∀ i, ∀ v ∈ S i, A (ContinuousLinearMap.adjoint A v) = (wp i : ℂ) • v ∧ B (ContinuousLinearMap.adjoint B v) = (wm i : ℂ) • v)
    (hc : ∀ i, c ≤ wp i ∨ c ≤ wm i) (v : V) :
    c * ‖v‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint A v‖ ^ 2 + ‖ContinuousLinearMap.adjoint B v‖ ^ 2 := by
  have hA : ∀ x : V, (⟪A (ContinuousLinearMap.adjoint A x), x⟫_ℂ).re = ‖ContinuousLinearMap.adjoint A x‖ ^ 2 := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hB : ∀ x : V, (⟪B (ContinuousLinearMap.adjoint B x), x⟫_ℂ).re = ‖ContinuousLinearMap.adjoint B x‖ ^ 2 := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hsm : ∀ (r : ℝ) (x : V), (⟪(r : ℂ) • x, x⟫_ℂ).re = r * ‖x‖ ^ 2 := by
    intro r x
    rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
    congr 1
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  let X : V →ₗ[ℂ] V := (A ∘L ContinuousLinearMap.adjoint A + B ∘L ContinuousLinearMap.adjoint B : V →L[ℂ] V).toLinearMap
  have hX : ∀ x, X x = A (ContinuousLinearMap.adjoint A x) + B (ContinuousLinearMap.adjoint B x) := fun x => rfl
  have hsym : X.IsSymmetric := by
    intro x y
    rw [hX, hX, inner_add_left, inner_add_right]
    rw [← ContinuousLinearMap.adjoint_inner_right A, ← ContinuousLinearMap.adjoint_inner_right B,
      ← ContinuousLinearMap.adjoint_inner_left A, ← ContinuousLinearMap.adjoint_inner_left B]
  have hge : ∀ i, ∀ x ∈ S i, x ≠ 0 → c ≤ wp i + wm i := by
    intro i x hx hx0
    have hn : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    have h1 := hA x
    have h2 := hB x
    rw [(hw i x hx).1, hsm] at h1
    rw [(hw i x hx).2, hsm] at h2
    have p1 : 0 ≤ wp i := by
      have : 0 ≤ wp i * ‖x‖ ^ 2 := by rw [h1]; positivity
      exact nonneg_of_mul_nonneg_left this hn
    have p2 : 0 ≤ wm i := by
      have : 0 ≤ wm i * ‖x‖ ^ 2 := by rw [h2]; positivity
      exact nonneg_of_mul_nonneg_left this hn
    rcases hc i with h | h <;> linarith
  have hev : ∀ (μ : ℝ) (e : V), X e = (μ : ℂ) • e → e ≠ 0 → c ≤ μ := by
    intro μ e he he0
    by_contra hlt
    apply he0
    have hmem : e ∈ (⨆ i, S i)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro i
      rw [Submodule.mem_orthogonal]
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      have hle := hge i x hx hx0
      have hXx : X x = ((wp i + wm i : ℝ) : ℂ) • x := by
        rw [hX, (hw i x hx).1, (hw i x hx).2, ← add_smul]; push_cast; rfl
      have h := hsym x e
      rw [hXx, he, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
      have hne : ((wp i + wm i : ℝ) : ℂ) ≠ (μ : ℂ) := by
        intro h'
        have := Complex.ofReal_injective h'
        apply hlt; linarith
      by_contra h0
      exact hne (mul_right_cancel₀ h0 h)
    rw [hS, Submodule.top_orthogonal_eq_bot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have hn : Module.finrank ℂ V = Module.finrank ℂ V := rfl
  set b := hsym.eigenvectorBasis hn with hb
  have hμ : ∀ j, c ≤ hsym.eigenvalues hn j := fun j =>
    hev _ (b j) (hsym.apply_eigenvectorBasis hn j) (b.orthonormal.ne_zero j)
  rw [← hA, ← hB, ← Complex.add_re, ← inner_add_left, ← hX]
  rw [← b.sum_inner_mul_inner (X v) v, Complex.re_sum, ← b.sum_sq_norm_inner_right v, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : ⟪X v, b j⟫_ℂ = (hsym.eigenvalues hn j : ℂ) * ⟪v, b j⟫_ℂ := by
    rw [hsym v (b j), hb, hsym.apply_eigenvectorBasis hn j, inner_smul_right]; rfl
  rw [h1, mul_assoc, Complex.re_ofReal_mul, ← inner_conj_symm v (b j), Complex.conj_mul']
  have : ((‖⟪b j, v⟫_ℂ‖ : ℂ) ^ 2).re = ‖⟪b j, v⟫_ℂ‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [this]
  exact mul_le_mul_of_nonneg_right (hμ j) (sq_nonneg _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSumEigenprojectorLeOfResolventBound
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

open Finset Complex in
open scoped InnerProductSpace in
private lemma circleIntegral_finset_sum_of_continuousOn {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (s : Finset ι) (f : ι → ℂ → E) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (Metric.sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a s ha ih =>
    have ha' : ContinuousOn (f a) (Metric.sphere c R) := hf a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, ContinuousOn (f i) (Metric.sphere c R) :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : ContinuousOn (fun z => ∑ i ∈ s, f i z) (Metric.sphere c R) :=
      continuousOn_finset_sum s hs
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add (ha'.circleIntegrable hR) (hsum.circleIntegrable hR), ih hs]

open Finset Complex in
open scoped InnerProductSpace in

theorem _root_.GlobalTheory.norm_sum_eigenprojector_le_of_resolvent_bound :
    ∀ (H κ : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [Fintype κ] [DecidableEq κ]
    (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (In : Finset κ)
    (c : ℂ) (R Mc : ℝ), FiniteDimensional ℂ VV → 0 < R → 0 ≤ Mc →
    (∀ x ∈ VV, ∑ i, p i x = x) →
    (∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = lam i • p i x) →
    (∀ i ∈ In, ‖lam i - c‖ < R) → (∀ i, i ∉ In → R < ‖lam i - c‖) →
    (∀ ζ : ℂ, ‖ζ - c‖ = R → ∀ x ∈ VV, ‖x‖ ≤ Mc * ‖ζ • x - T x‖) →
    ∀ x ∈ VV, ‖∑ i ∈ In, p i x‖ ≤ R * Mc * ‖x‖ := by
  intro H κ _ _ _ _ VV T p lam In c R Mc hfin hR hMc hsum hp hin hout hres x hx
  haveI : FiniteDimensional ℂ VV := hfin
  haveI : CompleteSpace VV := FiniteDimensional.complete ℂ VV

  have hne : ∀ i, ∀ ζ ∈ Metric.sphere c R, ζ - lam i ≠ 0 := by
    intro i ζ hζ h
    rw [mem_sphere_iff_norm] at hζ
    rw [sub_eq_zero] at h
    rw [h] at hζ
    by_cases hi : i ∈ In
    · exact lt_irrefl _ (hζ ▸ hin i hi)
    · exact lt_irrefl _ (hζ ▸ hout i hi)
  let v : κ → VV := fun i => ⟨p i x, (hp i x hx).1⟩
  let F : ℂ → VV := fun ζ => ∑ i, (ζ - lam i)⁻¹ • v i

  have hF : ∀ ζ ∈ Metric.sphere c R, ‖F ζ‖ ≤ Mc * ‖x‖ := by
    intro ζ hζ
    have hcoe : ((F ζ : VV) : H) = ∑ i, (ζ - lam i)⁻¹ • p i x := by
      simp [F, v]
    have key : ζ • ((F ζ : VV) : H) - T ((F ζ : VV) : H) = x := by
      rw [hcoe, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      conv_rhs => rw [← hsum x hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hp i x hx).2, smul_smul, smul_smul, ← sub_smul]
      have h1 : ζ * (ζ - lam i)⁻¹ - (ζ - lam i)⁻¹ * lam i = 1 := by
        rw [mul_comm ζ, ← mul_sub, inv_mul_cancel₀ (hne i ζ hζ)]
      rw [h1, one_smul]
    have := hres ζ (mem_sphere_iff_norm.mp hζ) _ (F ζ).2
    rw [key] at this
    simpa [Submodule.coe_norm] using this

  have hval : ∀ i, (∮ z in C(c, R), (z - lam i)⁻¹) =
      if i ∈ In then 2 * (Real.pi : ℂ) * I else 0 := by
    intro i
    by_cases hi : i ∈ In
    · rw [if_pos hi]
      exact circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_iff_norm.mpr (hin i hi))
    · rw [if_neg hi]
      have hoff : ∀ z ∈ Metric.closedBall c R, z - lam i ≠ 0 := by
        intro z hz h
        rw [sub_eq_zero] at h
        rw [mem_closedBall_iff_norm, h] at hz
        exact absurd (hout i hi) (not_lt.mpr hz)
      refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
        Set.countable_empty ?_ ?_
      · exact (continuousOn_id.sub continuousOn_const).inv₀ hoff
      · intro z hz
        exact (differentiableAt_id.sub_const _).inv
          (hoff z (Metric.ball_subset_closedBall hz.1))
  have hint : (∮ z in C(c, R), F z) = (2 * (Real.pi : ℂ) * I) • ∑ i ∈ In, v i := by
    have hcont : ∀ i ∈ (Finset.univ : Finset κ),
        ContinuousOn (fun z : ℂ => (z - lam i)⁻¹ • v i) (Metric.sphere c R) := by
      intro i _
      exact ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz => hne i z hz).smul
        continuousOn_const
    simp only [F]
    rw [circleIntegral_finset_sum_of_continuousOn _ _ c hR.le hcont]
    simp only [circleIntegral.integral_smul_const, hval, ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.smul_sum]
  have hbound := circleIntegral.norm_integral_le_of_norm_le_const hR.le hF
  rw [hint, norm_smul] at hbound
  have hnorm : ‖(2 * (Real.pi : ℂ) * I)‖ = 2 * Real.pi := by
    simp [Real.pi_pos.le]
  rw [hnorm] at hbound
  have hS : ‖∑ i ∈ In, p i x‖ = ‖∑ i ∈ In, v i‖ := by
    have hc : ((∑ i ∈ In, v i : VV) : H) = ∑ i ∈ In, p i x := by simp [v]
    rw [← hc]
    rfl
  rw [hS]
  have hpi : 0 < 2 * Real.pi := by positivity
  nlinarith [hbound]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotLeSqSup
section
namespace GlobalTheory.NotLeSqSup

theorem not_le_sq_sup {A : Type} [CommRing A] {m I : Ideal A} {n : ℕ}
    (hn : m ^ (n + 1) = ⊥) (hI : ¬ m ≤ I) : ¬ m ≤ m ^ 2 ⊔ I := by
  intro h
  have key : ∀ j : ℕ, m ≤ m ^ (j + 1) ⊔ I := by
    intro j
    induction j with
    | zero => simpa using (le_sup_left : m ≤ m ⊔ I)
    | succ j ih =>
      calc m ≤ m ^ 2 ⊔ I := h
        _ ≤ m ^ (j + 1 + 1) ⊔ I := by
          refine sup_le ?_ le_sup_right
          calc m ^ 2 = m * m := pow_two m
            _ ≤ m * (m ^ (j + 1) ⊔ I) := Ideal.mul_mono_right ih
            _ = m * m ^ (j + 1) ⊔ m * I := Ideal.mul_sup _ _ _
            _ ≤ m ^ (j + 1 + 1) ⊔ I :=
              sup_le_sup (le_of_eq (pow_succ' m (j + 1)).symm)
                (Ideal.mul_le.mpr fun r _ s hs => I.mul_mem_left r hs)
  apply hI
  simpa [hn] using key n

theorem main : ∀ {k A : Type} [inst : Field k] [inst_1 : CommRing A] [inst_2 : Algebra k A] (aug : A →ₐ[k] k) {I : Ideal A} {n : ℕ}, RingHom.ker aug ^ (n + (1 : ℕ)) = ⊥ → I ≤ RingHom.ker aug → ¬RingHom.ker aug ≤ I → ∃ (φ : A →ₐ[k] DualNumber k), AlgHom.comp (TrivSqZeroExt.fstHom k k k) φ = aug ∧ (∀ a ∈ I, (φ : A → DualNumber k) a = (0 : DualNumber k)) ∧ ∃ a ∈ RingHom.ker aug, (φ : A → DualNumber k) a ≠ (0 : DualNumber k) := by
  intro k A _ _ _ aug I n hn hIm hmI
  have hx : ¬ RingHom.ker aug ≤ RingHom.ker aug ^ 2 ⊔ I := not_le_sq_sup hn hmI
  obtain ⟨x, hxm, hxN⟩ := Set.not_subset.mp hx
  let N : Submodule k A := (RingHom.ker aug ^ 2 ⊔ I).restrictScalars k
  have hq : N.mkQ x ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxN
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k (A ⧸ N), f (N.mkQ x) ≠ 0 := by
    by_contra h; push_neg at h
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  let g : A →ₗ[k] k := f.comp N.mkQ
  have hgN : ∀ a ∈ RingHom.ker aug ^ 2 ⊔ I, g a = 0 := by
    intro a ha
    have : N.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ha
    simp only [g, LinearMap.comp_apply, this, map_zero]
  let D : A →ₗ[k] k := g.comp (LinearMap.id - (Algebra.linearMap k A).comp aug.toLinearMap)
  have hD : ∀ a, D a = g (a - algebraMap k A (aug a)) := fun a => rfl
  have hsub : ∀ a, a - algebraMap k A (aug a) ∈ RingHom.ker aug := by
    intro a; simp [RingHom.mem_ker]
  have hDmul : ∀ a b, D (a * b) = aug a * D b + aug b * D a := by
    intro a b
    have e : a * b - algebraMap k A (aug (a * b)) =
        (a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))
          + aug a • (b - algebraMap k A (aug b)) + aug b • (a - algebraMap k A (aug a)) := by
      rw [map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    have h0 : g ((a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))) = 0 :=
      hgN _ (Ideal.mem_sup_left (by rw [pow_two]; exact Ideal.mul_mem_mul (hsub a) (hsub b)))
    rw [hD, hD, hD, e, map_add, map_add, h0, map_smul, map_smul, smul_eq_mul, smul_eq_mul, zero_add]
  let L : A →ₗ[k] DualNumber k :=
    (Algebra.linearMap k (DualNumber k)).comp aug.toLinearMap + (TrivSqZeroExt.inrHom k k).comp D
  have hLfst : ∀ a, (L a).fst = aug a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  have hLsnd : ∀ a, (L a).snd = D a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  let φ : A →ₐ[k] DualNumber k := AlgHom.ofLinearMap L
    (by ext <;> simp [hLfst, hLsnd, hD])
    (by intro a b; ext <;> simp [hLfst, hLsnd, hDmul] <;> ring)
  have hφ : ∀ a, φ a = L a := fun a => rfl
  refine ⟨φ, ?_, ?_, x, hxm, ?_⟩
  · ext a; simp [hφ, hLfst]
  · intro a ha
    ext
    · simp [hφ, hLfst]; exact hIm ha
    · simp only [hφ, hLsnd, TrivSqZeroExt.snd_zero]
      rw [hD]
      have : aug a = 0 := hIm ha
      rw [this, map_zero, sub_zero]
      exact hgN a (Ideal.mem_sup_right ha)
  · intro h0
    apply hf
    have := congrArg TrivSqZeroExt.snd h0
    rw [hφ, hLsnd, hD, TrivSqZeroExt.snd_zero, (RingHom.mem_ker).mp hxm, map_zero, sub_zero] at this
    exact this

end GlobalTheory.NotLeSqSup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowSubSelfMemSpanOfSplitsCompletely
section
open NumberField

namespace GlobalTheory

theorem eq_of_le_of_multiset_prod_eq_pow_card {g : ℕ} (hg : 0 < g) (s : Multiset ℕ)
    (hle : ∀ a ∈ s, g ≤ a) (hprod : s.prod = g ^ s.card) : ∀ a ∈ s, a = g := by
  intro a ha
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  have ht : g ^ t.card ≤ t.prod :=
    Multiset.pow_card_le_prod (fun b hb => hle b (Multiset.mem_cons_of_mem hb))
  rw [Multiset.prod_cons, Multiset.card_cons, pow_succ'] at hprod
  have hpos : 0 < g ^ t.card := pow_pos hg _
  have h1 : a * g ^ t.card ≤ g * g ^ t.card := hprod ▸ Nat.mul_le_mul_left a ht
  exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hpos) (hle a (Multiset.mem_cons_self _ _))

theorem pow_sub_self_mem_span_of_splits_completely (E : Type) [Field E] [NumberField E] (g : ℕ)
    (hg : g.Prime)
    (hcard : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card =
      Module.finrank ℚ E)
    (hnd : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup)
    (x : 𝓞 E) : x ^ g - x ∈ Ideal.span {(g : 𝓞 E)} := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {(g : 𝓞 E)} with hI
  set s := UniqueFactorizationMonoid.normalizedFactors I with hs
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg.ne_zero
  have hprod : s.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hprime : ∀ P ∈ s, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hN : Ideal.absNorm I = g ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have hle : ∀ a ∈ s.map Ideal.absNorm, g ≤ a := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp ha
    have hdvd : Ideal.absNorm P ∣ g ^ Module.finrank ℚ E := by
      rw [← hN, ← hprod]
      exact map_dvd _ (Multiset.dvd_prod hP)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hg).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
      exact (hprime P hP).ne_one (by rw [hk, Ideal.one_eq_top])
    rw [hk]
    exact Nat.le_self_pow hk0 g
  have hall : ∀ a ∈ s.map Ideal.absNorm, a = g := by
    refine eq_of_le_of_multiset_prod_eq_pow_card hg.pos _ hle ?_
    rw [← map_multiset_prod, hprod, hN, Multiset.card_map, hcard]
  have hmem : ∀ P ∈ s, x ^ g - x ∈ P := by
    intro P hP
    have hNP : Ideal.absNorm P = g := hall _ (Multiset.mem_map_of_mem _ hP)
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (hprime P hP)
    have hPm : P.IsMaximal := hPp.isMaximal (hprime P hP).ne_zero
    have hc : Nat.card (𝓞 E ⧸ P) = g := by
      rw [← hNP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hfin : Finite (𝓞 E ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hg.ne_zero)
    let := Fintype.ofFinite (𝓞 E ⧸ P)
    let := Ideal.Quotient.field P
    rw [← Ideal.Quotient.eq, map_pow, ← hc, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hdvd : (∏ P ∈ (⟨s, hnd⟩ : Finset (Ideal (𝓞 E))), P) ∣ Ideal.span {x ^ g - x} :=
    Finset.prod_primes_dvd _ hprime fun P hP =>
      Ideal.dvd_span_singleton.mpr (hmem P hP)
  have he : (∏ P ∈ (⟨s, hnd⟩ : Finset (Ideal (𝓞 E))), P) = I := by
    rw [← hprod, Finset.prod_mk, Multiset.map_id']
  rw [he] at hdvd
  exact Ideal.dvd_span_singleton.mp hdvd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdLeOfInterlacingPairing
section
open Finset

namespace GlobalTheory

theorem prod_le_of_interlacing_pairing :
    ∀ (k l : ℕ) (c B Y : ℝ) (lam v a : ℕ → ℝ), 0 ≤ c → 1 ≤ B → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ v s) ∧ (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lam s)) → (∀ i ∈ Finset.Icc 1 k, 1 ≤ |Y + 1 / 2 + v i|) → (∀ s ∈ Finset.Icc 1 (k - 1), 0 ≤ a s ∧ a s ≤ |lam s + Y| + 1 + c ∧ a s ≤ B) → ∏ s ∈ Finset.Icc 1 (k - 1), a s ≤ B * (∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s + Y| 1)) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
  intro k l c B Y lam v a hc hB hlam hv hW ha
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℕ, ∀ s, φ s = if -Y < lam s then s else s + 1 := ⟨_, fun _ => rfl⟩
  have hmem : ∀ s ∈ Finset.Icc 1 (k - 1), φ s ∈ Finset.Icc 1 k := by
    intro s hs
    rw [Finset.mem_Icc] at hs ⊢
    rw [hφ]; split_ifs <;> omega
  have hinj : ∀ s ∈ Finset.Icc 1 (k - 1), ∀ t ∈ Finset.Icc 1 (k - 1), φ s = φ t → s = t := by
    intro s hs t ht h
    rw [Finset.mem_Icc] at hs ht
    rw [hφ, hφ] at h
    split_ifs at h with h1 h2 h2
    · exact h
    · subst h
      have := hlam t ht.1 hs.2
      linarith [not_lt.mp h2]
    · subst h
      have := hlam s hs.1 ht.2
      linarith [not_lt.mp h1]
    · omega
  have hR : ∀ s, 1 ≤ 1 + (1 + c) / max |lam s + Y| 1 := by
    intro s
    have : 0 ≤ (1 + c) / max |lam s + Y| 1 := by positivity
    linarith
  have hkey : ∀ s ∈ Finset.Icc 1 (k - 1), a s ≤ (if φ s = l then B else 1) *
      (1 + (1 + c) / max |lam s + Y| 1) * |Y + 1 / 2 + v (φ s)| := by
    intro s hs
    have hw := hW _ (hmem s hs)
    obtain ⟨h0, h1, h2⟩ := ha s hs
    have hr := hR s
    split_ifs with hl
    · calc a s ≤ B * 1 * 1 := by linarith
        _ ≤ _ := by gcongr
    · rw [Finset.mem_Icc] at hs
      obtain ⟨hv1, hv2⟩ := hv s hs.1 (by omega)
      have hd : |lam s + Y| ≤ |Y + 1 / 2 + v (φ s)| := by
        rw [hφ] at hl ⊢
        split_ifs at hl ⊢ with hy
        · have := hv1 hl
          rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
        · have := hv2 hl
          have := not_lt.mp hy
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have hM : max |lam s + Y| 1 ≤ |Y + 1 / 2 + v (φ s)| := max_le hd hw
      have hM1 : (1 : ℝ) ≤ max |lam s + Y| 1 := le_max_right _ _
      have hM2 : |lam s + Y| ≤ max |lam s + Y| 1 := le_max_left _ _
      have e : (1 + (1 + c) / max |lam s + Y| 1) * max |lam s + Y| 1
          = max |lam s + Y| 1 + (1 + c) := by
        field_simp
      rw [one_mul]
      calc a s ≤ (1 + (1 + c) / max |lam s + Y| 1) * max |lam s + Y| 1 := by rw [e]; linarith
        _ ≤ _ := by gcongr
  have hB' : ∏ s ∈ Finset.Icc 1 (k - 1), (if φ s = l then B else 1) ≤ B := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hcard : ((Finset.Icc 1 (k - 1)).filter (fun s => φ s = l)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro s hs t ht
      rw [Finset.mem_filter] at hs ht
      exact hinj s hs.1 t ht.1 (hs.2.trans ht.2.symm)
    calc _ ≤ B ^ 1 := pow_le_pow_right₀ hB hcard
      _ = B := pow_one B
  have hW' : ∏ s ∈ Finset.Icc 1 (k - 1), |Y + 1 / 2 + v (φ s)|
      ≤ ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
    rw [← Finset.prod_image (f := fun i => |Y + 1 / 2 + v i|) (g := φ)
      (fun s hs t ht h => hinj s hs t ht h)]
    have hsub : (Finset.Icc 1 (k - 1)).image φ ⊆ Finset.Icc 1 k := by
      intro i hi
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
      exact hmem s hs
    rw [← Finset.prod_sdiff hsub]
    refine le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => abs_nonneg _) ?_
    calc (1 : ℝ) = ∏ i ∈ Finset.Icc 1 k \ (Finset.Icc 1 (k - 1)).image φ, 1 := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i hi => hW i (Finset.mem_sdiff.mp hi).1)
  calc ∏ s ∈ Finset.Icc 1 (k - 1), a s
      ≤ ∏ s ∈ Finset.Icc 1 (k - 1), ((if φ s = l then B else 1) *
        (1 + (1 + c) / max |lam s + Y| 1) * |Y + 1 / 2 + v (φ s)|) :=
        Finset.prod_le_prod (fun s hs => (ha s hs).1) hkey
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ _ := by
      have h1 : 0 ≤ ∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s + Y| 1) :=
        Finset.prod_nonneg fun s _ => zero_le_one.trans (hR s)
      have h2 : 0 ≤ ∏ s ∈ Finset.Icc 1 (k - 1), |Y + 1 / 2 + v (φ s)| :=
        Finset.prod_nonneg fun _ _ => abs_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_right hB' h1) hW' h2
        (mul_nonneg (by linarith) h1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormAddSqLeOfBounds
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem sum_norm_add_sq_le_of_bounds :
    ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by
  intro V ι _ _ u v c s N hc hs hN hu hv
  have hcs : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hv0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ (c * s * N) ^ 2 := by
    calc _ ≤ _ := hcs
      _ ≤ (c ^ 2 * N) * (s ^ 2 * N) := mul_le_mul hu hv hv0 (by positivity)
      _ = _ := by ring
  have h2 : ∑ i, ‖u i‖ * ‖v i‖ ≤ c * s * N :=
    (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun i _ => by positivity) (by positivity)
      two_ne_zero).1 h1
  have h3 : ∑ i, ‖u i + v i‖ ^ 2 ≤ ∑ i, (‖u i‖ ^ 2 + 2 * (‖u i‖ * ‖v i‖) + ‖v i‖ ^ 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖u i + v i‖ ^ 2 ≤ (‖u i‖ + ‖v i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ = _ := by ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h3
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoIntegralInnerOfTendstoELpNormTwo
section
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem tendsto_integral_inner_of_tendsto_eLpNorm_two :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v v' : ℕ → X → E) (u u' : X → E), (∀ n, MemLp (v n) 2 μ) → (∀ n, MemLp (v' n) 2 μ) → MemLp u 2 μ → MemLp u' 2 μ → Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) → Tendsto (fun n => eLpNorm (v' n - u') 2 μ) atTop (𝓝 0) → Tendsto (fun n => ∫ x, inner ℂ (v' n x) (v n x) ∂μ) atTop (𝓝 (∫ x, inner ℂ (u' x) (u x) ∂μ)) := by
  intro X _ μ E _ _ v v' u u' hv hv' hu hu' h h'
  have key : ∀ (f g : X → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      ∫ x, inner ℂ (f x) (g x) ∂μ = inner ℂ (hf.toLp f) (hg.toLp g) := by
    intro f g hf hg
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have h1 : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hu.toLp u)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv u hu).2 h
  have h2 : Tendsto (fun n => (hv' n).toLp (v' n)) atTop (𝓝 (hu'.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v' hv' u' hu').2 h'
  rw [key u' u hu' hu]
  simp_rw [fun n => key (v' n) (v n) (hv' n) (hv n)]
  exact h2.inner h1

end GlobalTheory
end

