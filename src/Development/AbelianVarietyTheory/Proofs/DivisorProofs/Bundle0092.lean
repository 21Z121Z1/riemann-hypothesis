import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsOfSchemeOverArtinianFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.PinchPoints

theorem ring_lift_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (a : R₁) (b : R₂)
    (hab : g₁ a = g₂ b) : ∃ x : P, f₁ x = a ∧ f₂ x = b :=
  ((Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))).2.2 a b hab

theorem ring_ext_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (x y : P)
    (h₁ : f₁ x = f₁ y) (h₂ : f₂ x = f₂ y) : x = y :=
  ((Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))).2.1 x y ⟨h₁, h₂⟩

theorem scheme_exists_of_isPullback {X Y Z W : Scheme.{0}} {fst : W ⟶ X} {snd : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y) (hxy : f x = g y) :
    ∃ w, fst w = x ∧ snd w = y := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]

theorem closedImmersion_of_isPullback {W X Y Z : Scheme.{0}} {fst : W ⟶ X} {snd : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [IsClosedImmersion g] :
    IsClosedImmersion fst :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance

theorem spec_subsingleton_of_artinian (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P] :
    Subsingleton (Spec P) :=
  ⟨fun a b => PrimeSpectrum.ext
    ((IsLocalRing.eq_maximalIdeal (@IsArtinianRing.isMaximal_of_isPrime P _ a.asIdeal a.isPrime _)).trans
      (IsLocalRing.eq_maximalIdeal (@IsArtinianRing.isMaximal_of_isPrime P _ b.asIdeal b.isPrime _)).symm)⟩

theorem spec_nonempty_iff (R : CommRingCat.{0}) : Nonempty (Spec R) ↔ Nontrivial R := by
  rw [← not_isEmpty_iff, ← not_subsingleton_iff_nontrivial]
  exact not_congr (PrimeSpectrum.isEmpty_iff_subsingleton (R := R))

theorem points_of_pinch : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y Y₁ Y₂ Y₀ : Scheme.{0}) (p : Y ⟶ Spec P) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback j₁ p₁ p (Spec.map f₁) → IsPullback j₂ p₂ p (Spec.map f₂) → IsPullback i₁ p₀ p₁ (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) ∧ ∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → ∃ y₀ : Y₀, i₁ y₀ = y₁ ∧ i₂ y₀ = y₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ Y Y₁ Y₂ Y₀ p p₁ p₂ p₀ j₁ j₂ i₁ i₂ h₁ h₂ h₀ hcomm
  have hf₁ : Function.Surjective f₁ := fun a => by
    obtain ⟨b, hb⟩ := hg₂ (g₁ a)
    obtain ⟨x, hx, -⟩ := ring_lift_of_isPullback hP a b hb.symm
    exact ⟨x, hx⟩
  have hf₂ : Function.Surjective f₂ := fun b => by
    obtain ⟨a, ha⟩ := hg₁ (g₂ b)
    obtain ⟨x, -, hx⟩ := ring_lift_of_isPullback hP a b ha
    exact ⟨x, hx⟩
  haveI := IsClosedImmersion.spec_of_surjective f₁ hf₁
  haveI := IsClosedImmersion.spec_of_surjective f₂ hf₂
  haveI : IsClosedImmersion j₁ := closedImmersion_of_isPullback h₁
  haveI : IsClosedImmersion j₂ := closedImmersion_of_isPullback h₂
  haveI : Subsingleton (Spec P) := spec_subsingleton_of_artinian P
  haveI : Subsingleton (Spec R₁) := (Spec.map f₁).isClosedEmbedding.injective.subsingleton
  have lift₁ : Nontrivial R₁ → ∀ y : Y, ∃ y₁, j₁ y₁ = y := fun hn y => by
    obtain ⟨s⟩ := (spec_nonempty_iff R₁).2 hn
    obtain ⟨y₁, hy, -⟩ := scheme_exists_of_isPullback h₁ y s (Subsingleton.elim _ _)
    exact ⟨y₁, hy⟩
  have lift₂ : Nontrivial R₂ → ∀ y : Y, ∃ y₂, j₂ y₂ = y := fun hn y => by
    obtain ⟨s⟩ := (spec_nonempty_iff R₂).2 hn
    obtain ⟨y₂, hy, -⟩ := scheme_exists_of_isPullback h₂ y s (Subsingleton.elim _ _)
    exact ⟨y₂, hy⟩
  refine ⟨fun y => ?_, fun y₁ y₂ hy => ?_⟩
  · by_cases hn : Nontrivial R₁
    · exact Or.inl (lift₁ hn y)
    · by_cases hn₂ : Nontrivial R₂
      · exact Or.inr (lift₂ hn₂ y)
      · exfalso
        rw [not_nontrivial_iff_subsingleton] at hn hn₂
        exact one_ne_zero (ring_ext_of_isPullback hP (1 : P) 0 (Subsingleton.elim _ _)
          (Subsingleton.elim _ _))
  · have hn₁ : Nontrivial R₁ := (spec_nonempty_iff R₁).1 ⟨p₁ y₁⟩
    have hn₂ : Nontrivial R₂ := (spec_nonempty_iff R₂).1 ⟨p₂ y₂⟩
    have hn₀ : Nontrivial R₀ := by
      by_contra hc
      rw [not_nontrivial_iff_subsingleton] at hc
      obtain ⟨e, he₁, he₂⟩ := ring_lift_of_isPullback hP (1 : R₁) (0 : R₂) (Subsingleton.elim _ _)
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
      · have h' := hu.map f₂.hom
        rw [show f₂.hom e = 0 from he₂] at h'
        exact not_isUnit_zero h'
      · have h' := hu.map f₁.hom
        rw [map_sub, map_one, show f₁.hom e = 1 from he₁, sub_self] at h'
        exact not_isUnit_zero h'
    obtain ⟨s₀⟩ := (spec_nonempty_iff R₀).2 hn₀
    obtain ⟨y₀, hy₀, -⟩ := scheme_exists_of_isPullback h₀ y₁ s₀ (Subsingleton.elim _ _)
    refine ⟨y₀, hy₀, j₂.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply, hy₀, hy]

end GlobalTheory.PinchPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyGrowthSpreadOfIntegralMonodromy
section
open Filter Topology

namespace GlobalTheory

lemma intMatrix_smul_sum_norm_le {m g : ℕ} (M : Fin m → Fin m → ℤ) (x y : Fin m → Fin g → ℂ)
    (h : ∀ j, y j = ∑ i, M j i • x i) :
    ‖y‖ ≤ (∑ j, ∑ i, ‖M j i‖) * ‖x‖ := by
  have hS : 0 ≤ ∑ j, ∑ i, ‖M j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hS (norm_nonneg x))).2 fun j => ?_
  rw [h j]
  calc ‖∑ i, M j i • x i‖ ≤ ∑ i, ‖M j i • x i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖M j i‖ * ‖x‖ := Finset.sum_le_sum fun i _ =>
        (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _))
    _ = (∑ i, ‖M j i‖) * ‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j, ∑ i, ‖M j i‖) * ‖x‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun j => ∑ i, ‖M j i‖)
          (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _) (Finset.mem_univ j)) (norm_nonneg x)

theorem polyGrowth_spread_of_integral_monodromy : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ) (P Q : Fin m → Fin m → ℤ), (∀ s : ℂ, s.re < 0 → ∀ j, lam (s + 2 * Real.pi * Complex.I) j = ∑ i, P j i • lam s i) → (∀ s : ℂ, s.re < 0 → ∀ j, lam s j = ∑ i, Q j i • lam (s + 2 * Real.pi * Complex.I) i) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  intro g m lam C k P Q h1 h2 h3 R
  set τ : ℂ := 2 * Real.pi * Complex.I with hτ
  have hτre : τ.re = 0 := by simp [hτ]
  have hτim : τ.im = 2 * Real.pi := by simp [hτ]
  have hτn : ‖τ‖ = 2 * Real.pi := by simp [hτ, abs_of_pos Real.pi_pos]
  have hexp : ∀ s, Complex.exp (s + τ) = Complex.exp s := by
    intro s; rw [Complex.exp_add, hτ, Complex.exp_two_pi_mul_I, mul_one]
  have hSP : 0 ≤ ∑ j, ∑ i, ‖P j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  have hSQ : 0 ≤ ∑ j, ∑ i, ‖Q j i‖ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  set A : ℝ := 1 + ∑ j, ∑ i, ‖P j i‖ + ∑ j, ∑ i, ‖Q j i‖ with hA
  have hA1 : 1 ≤ A := by linarith
  have hPA : ∀ s : ℂ, s.re < 0 → ‖lam (s + τ)‖ ≤ A * ‖lam s‖ := fun s hs =>
    (intMatrix_smul_sum_norm_le P _ _ (h1 s hs)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hQA : ∀ s : ℂ, s.re < 0 → ‖lam s‖ ≤ A * ‖lam (s + τ)‖ := fun s hs =>
    (intMatrix_smul_sum_norm_le Q _ _ (h2 s hs)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  set B : ℝ := A * (1 + 2 * Real.pi) ^ k with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ (by linarith [Real.pi_pos]))
  have hgrow : ∀ s t : ℂ, ‖t‖ ≤ ‖s‖ + 2 * Real.pi →
      (1 + ‖t‖) ^ k ≤ (1 + 2 * Real.pi) ^ k * (1 + ‖s‖) ^ k := by
    intro s t h
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [norm_nonneg s, Real.pi_pos]
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have key : ∀ n : ℕ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 →
      |s.im| ≤ Real.pi + 2 * Real.pi * n → ‖lam s‖ ≤ max C 0 * B ^ n * (1 + ‖s‖) ^ k := by
    intro n
    induction n with
    | zero =>
      intro s hs he hi
      have hX : 0 ≤ (1 + ‖s‖) ^ k := by positivity
      calc ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := h3 s hs he (by simpa using hi)
        _ ≤ max C 0 * B ^ 0 * (1 + ‖s‖) ^ k := by
          rw [pow_zero, mul_one]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    | succ n ih =>
      intro s hs he hi
      have hX : 0 ≤ (1 + ‖s‖) ^ k := by positivity
      have hBn : 1 ≤ B ^ (n + 1) := one_le_pow₀ hB1
      by_cases hsm : |s.im| ≤ Real.pi
      · calc ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := h3 s hs he hsm
          _ ≤ max C 0 * B ^ (n + 1) * (1 + ‖s‖) ^ k := by
            apply mul_le_mul_of_nonneg_right _ hX
            calc C ≤ max C 0 := le_max_left _ _
              _ = max C 0 * 1 := (mul_one _).symm
              _ ≤ max C 0 * B ^ (n + 1) := mul_le_mul_of_nonneg_left hBn hM
      · push_neg at hsm
        have hn0 : (0 : ℝ) ≤ 2 * Real.pi * n := by positivity
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hi
        obtain ⟨hi1, hi2⟩ := abs_le.mp hi
        obtain ⟨t, hlt, htre, hte, htn, hti⟩ : ∃ t : ℂ, ‖lam s‖ ≤ A * ‖lam t‖ ∧ t.re = s.re ∧
            Complex.exp t = Complex.exp s ∧ ‖t‖ ≤ ‖s‖ + 2 * Real.pi ∧
            |t.im| ≤ Real.pi + 2 * Real.pi * n := by
          rcases lt_abs.mp hsm with hpos | hneg
          · refine ⟨s - τ, ?_, ?_, ?_, ?_, ?_⟩
            · have := hPA (s - τ) (by simp [Complex.sub_re, hτre, hs])
              rwa [sub_add_cancel] at this
            · simp [hτre]
            · have := hexp (s - τ); rw [sub_add_cancel] at this; exact this.symm
            · calc ‖s - τ‖ ≤ ‖s‖ + ‖τ‖ := norm_sub_le _ _
                _ = ‖s‖ + 2 * Real.pi := by rw [hτn]
            · rw [Complex.sub_im, hτim, abs_le]; constructor <;> nlinarith [Real.pi_pos]
          · refine ⟨s + τ, hQA s hs, ?_, hexp s, ?_, ?_⟩
            · simp [hτre]
            · calc ‖s + τ‖ ≤ ‖s‖ + ‖τ‖ := norm_add_le _ _
                _ = ‖s‖ + 2 * Real.pi := by rw [hτn]
            · rw [Complex.add_im, hτim, abs_le]; constructor <;> nlinarith [Real.pi_pos]
        have hIH := ih t (by rw [htre]; exact hs) (by rw [hte]; exact he) hti
        calc ‖lam s‖ ≤ A * ‖lam t‖ := hlt
          _ ≤ A * (max C 0 * B ^ n * (1 + ‖t‖) ^ k) :=
            mul_le_mul_of_nonneg_left hIH (by linarith)
          _ ≤ A * (max C 0 * B ^ n * ((1 + 2 * Real.pi) ^ k * (1 + ‖s‖) ^ k)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hgrow s t htn)
                (mul_nonneg hM (pow_nonneg (by linarith) n))) (by linarith)
          _ = max C 0 * B ^ (n + 1) * (1 + ‖s‖) ^ k := by rw [hB]; ring
  refine ⟨max C 0 * B ^ ⌈R / (2 * Real.pi)⌉₊, fun s hs he hi => key _ s hs he (hi.trans ?_)⟩
  have hc : R / (2 * Real.pi) ≤ (⌈R / (2 * Real.pi)⌉₊ : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ (by positivity)] at hc
  linarith [Real.pi_pos]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSolvabilityTransferAlgClosedFields
section
open MvPolynomial

namespace GlobalTheory.PointTransfer

theorem exists_algHom_algebraicClosure (F A : Type) [Field F] [CommRing A] [Nontrivial A] [Algebra F A]
    [Algebra.FiniteType F A] : Nonempty (A →ₐ[F] AlgebraicClosure F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩

theorem exists_common_zero {Ω τ : Type} [Field Ω] [IsAlgClosed Ω] [Finite τ]
    (I : Ideal (MvPolynomial τ Ω)) (hI : I ≠ ⊤) : ∃ y : τ → Ω, ∀ f ∈ I, aeval y f = 0 := by
  by_contra h
  have he : zeroLocus Ω I = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact h ⟨y, fun f hf => hy f hf⟩
  have h2 := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) I
  rw [he, MvPolynomial.vanishingIdeal_empty] at h2
  exact hI (Ideal.radical_eq_top.1 h2.symm)

noncomputable def partialEval {F A σ τ : Type} [CommRing F] [CommRing A] [Algebra F A] (u : σ → A) :
    MvPolynomial (σ ⊕ τ) F →ₐ[F] MvPolynomial τ A :=
  aeval (Sum.elim (fun s => C (u s)) X)

theorem eval₂Hom_partialEval {F A B σ τ : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (ψ : A →ₐ[F] B) (u : σ → A) (y : τ → B) (g : MvPolynomial (σ ⊕ τ) F) :
    eval₂Hom (ψ : A →+* B) y (partialEval u g) = aeval (Sum.elim (fun s => ψ (u s)) y) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [partialEval, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    cases i <;> simp [partialEval]

theorem map_partialEval {F A B σ τ : Type} [CommRing F] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (ψ : A →ₐ[F] B) (u : σ → A) (g : MvPolynomial (σ ⊕ τ) F) :
    MvPolynomial.map (ψ : A →+* B) (partialEval u g) = partialEval (fun s => ψ (u s)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [partialEval, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    cases i <;> simp [partialEval]

theorem solvable_transfer (F σ τ : Type) [Field F] [Finite σ] [Finite τ]
    (P : Ideal (MvPolynomial σ F)) (J : Ideal (MvPolynomial (σ ⊕ τ) F))
    (H : ∀ u : σ → AlgebraicClosure F, (∀ g ∈ P, aeval u g = 0) →
      ∃ y : τ → AlgebraicClosure F, ∀ g ∈ J, aeval (Sum.elim u y) g = 0)
    (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (u : σ → Ω)
    (hu : ∀ g ∈ P, aeval u g = 0) :
    ∃ y : τ → Ω, ∀ g ∈ J, aeval (Sum.elim u y) g = 0 := by
  have hI : J.map (partialEval (F := F) (τ := τ) u) ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial τ Ω) ∈ Submodule.span (MvPolynomial τ Ω)
        ((partialEval (F := F) (τ := τ) u) '' (J : Set _)) := by
      have : (1 : MvPolynomial τ Ω) ∈ J.map (partialEval (F := F) (τ := τ) u) := by
        rw [htop]; trivial
      exact this
    obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 h1
    choose g' hg'J hg' using fun i => (g i).2
    let S : Set Ω := Set.range u ∪ ⋃ i, ((c i).coeffs : Set Ω)
    have hS : S.Finite :=
      (Set.finite_range u).union (Set.finite_iUnion fun i => (c i).coeffs.finite_toSet)
    let A : Subalgebra F Ω := Algebra.adjoin F S
    haveI : Algebra.FiniteType F A :=
      (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
    obtain ⟨ψ⟩ := exists_algHom_algebraicClosure F A
    let uA : σ → A := fun s => ⟨u s, Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)⟩
    have hc : ∀ i, c i ∈ Set.range (MvPolynomial.map (σ := τ) (A.val : A →+* Ω)) := by
      intro i
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro a ha
      exact ⟨⟨a, Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨i, ha⟩))⟩, rfl⟩
    choose c' hc' using hc
    have hid : ∑ i, c' i * partialEval uA (g' i) = 1 := by
      apply MvPolynomial.map_injective (A.val : A →+* Ω) Subtype.val_injective
      rw [map_one, ← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hc', map_partialEval, smul_eq_mul, ← hg' i]
      rfl
    obtain ⟨y, hy⟩ := H (fun s => ψ (uA s)) (by
      intro p hp
      have h0 : aeval uA p = 0 := by
        apply Subtype.val_injective
        have := DFunLike.congr_fun (MvPolynomial.comp_aeval uA A.val) p
        exact this.trans (hu p hp)
      have := DFunLike.congr_fun (MvPolynomial.comp_aeval uA ψ) p
      rw [← this, AlgHom.comp_apply, h0, map_zero])
    have := congrArg (eval₂Hom (ψ : A →+* AlgebraicClosure F) y) hid
    rw [map_one, map_sum, Finset.sum_eq_zero] at this
    · exact zero_ne_one this
    · intro i _
      rw [map_mul, eval₂Hom_partialEval, hy _ (hg'J i), mul_zero]
  obtain ⟨y, hy⟩ := exists_common_zero _ hI
  refine ⟨y, fun g hg => ?_⟩
  have h := hy _ (Ideal.mem_map_of_mem _ hg)
  have h2 := eval₂Hom_partialEval (AlgHom.id F Ω) u y g
  exact h2.symm.trans h

end GlobalTheory.PointTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefExistsConjTransposeMulMulEqOne
section
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory

open Matrix

theorem posDef_exists_conjTranspose_mul_mul_eq_one :
    ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef →
      ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  intro d H hP
  have hH : H.IsHermitian := hP.isHermitian
  set U : Matrix (Fin d) (Fin d) ℂ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := hH.eigenvectorUnitary.2.1
  have hU2 : U * Uᴴ = 1 := hH.eigenvectorUnitary.2.2
  have hspec : H = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hP.eigenvalues_pos i
  let r : Fin d → ℝ := fun i => Real.sqrt (hH.eigenvalues i)
  have hr : ∀ i, 0 < r i := fun i => Real.sqrt_pos.2 (hpos i)
  have hrr : ∀ i, r i * r i = hH.eigenvalues i := fun i => Real.mul_self_sqrt (hpos i).le
  let s : Fin d → ℂ := fun i => (((r i)⁻¹ : ℝ) : ℂ)
  let t : Fin d → ℂ := fun i => ((r i : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ (hr i).ne', Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ (hr i).ne', Complex.ofReal_one]
  let Y : Matrix (Fin d) (Fin d) ℂ := U * diagonal s
  let Z : Matrix (Fin d) (Fin d) ℂ := diagonal t * Uᴴ
  have hYZ : Y * Z = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), hst, Matrix.one_mul, hU2]
  have hZY : Z * Y = 1 := by
    simp only [Y, Z]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hts]
  refine ⟨⟨Y, Z, hYZ, hZY⟩, ?_⟩
  show Yᴴ * H * Y = 1
  have hsH : (diagonal s)ᴴ = diagonal s := by
    rw [diagonal_conjTranspose]
    congr 1; funext i
    simp [s]
  have hdiag : diagonal s * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    simp only [s, ← hrr i, ← Complex.ofReal_mul]
    rw [show (r i)⁻¹ * (r i * r i) * (r i)⁻¹ = ((r i)⁻¹ * r i) * (r i * (r i)⁻¹) by ring,
      inv_mul_cancel₀ (hr i).ne', mul_inv_cancel₀ (hr i).ne']
    simp
  simp only [Y]
  rw [conjTranspose_mul, hsH, hspec]
  calc diagonal s * Uᴴ * (U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal s)
      = diagonal s * (Uᴴ * U) * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal s := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU1, Matrix.mul_one, Matrix.mul_one, hdiag]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefRealGramPairHermitianForms
section
open Matrix

namespace GlobalTheory.HermGram

noncomputable def reForm {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ H *ᵥ star w).re)
    (by intro a b c; simp [add_dotProduct])
    (by intro c a b; simp [smul_dotProduct, Complex.smul_re])
    (by intro a b c; simp [star_add, mulVec_add, dotProduct_add])
    (by intro c a b
        have : star (c • b) = c • star b := by
          ext i; simp [Complex.conj_ofReal]
        rw [this, mulVec_smul, dotProduct_smul, Complex.smul_re])

theorem reForm_apply {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    reForm H z w = (z ⬝ᵥ H *ᵥ star w).re := rfl

theorem reForm_symm {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (z w : Fin g → ℂ) : reForm H z w = reForm H w z := by
  simp only [reForm_apply]
  have : star (z ⬝ᵥ H *ᵥ star w) = w ⬝ᵥ H *ᵥ star z := by
    simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hH.apply i j]; ring
  rw [← this]; simp

theorem gram_posDef {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) :
    (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext k l
    simp only [conjTranspose_apply, of_apply, star_trivial]
    exact reForm_symm hH (e l) (e k)
  · intro x hx
    set v : Fin g → ℂ := ∑ k, x k • e k with hvdef
    have hv : v ≠ 0 := by
      intro h0
      apply hx
      apply e.equivFun.symm.injective
      rw [map_zero, Module.Basis.equivFun_symm_apply]
      exact h0
    have key : star x ⬝ᵥ (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re) *ᵥ x
        = reForm H v v := by
      rw [hvdef]
      change star x ⬝ᵥ (Matrix.of fun k l => reForm H (e k) (e l)) *ᵥ x = _
      simp only [star_trivial, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, dotProduct, mulVec, of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [reForm_symm hH (e l) (e k)]; ring
    rw [key, reForm_apply]
    exact hpos v hv

theorem gram_posDef_pair (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (p₁ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re)
    (p₂ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hγ : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) :
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  refine ⟨gram_posDef e h₁ p₁, ?_⟩
  have hG : (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ) =
      Matrix.of fun k l => (e k ⬝ᵥ H₂.mulVec (star (e l))).re := by
    ext k l
    rw [of_apply, hγ, mul_apply]
    have hs : γ (e l) = ∑ m, e.repr (γ (e l)) m • e m := (e.sum_repr _).symm
    have : (e k ⬝ᵥ H₁.mulVec (star (γ (e l)))).re = reForm H₁ (e k) (γ (e l)) := rfl
    rw [this, hs]
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.toMatrix_apply, of_apply,
      LinearMap.restrictScalars_apply, reForm_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hG]
  exact gram_posDef e h₂ p₂

end GlobalTheory.HermGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfFiniteAppLE
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem preimage_eq_of_finite_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π] {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → IsAffineOpen V → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (π.appLE U V h).hom.Finite → π ⁻¹ᵁ U = V := by
  intro X Y _ π _ U V hU hV hne h hfin
  have : IsAffine U := hU
  have : IsAffine V := hV
  have hf : IsFinite (π.resLE U V h) := by
    have hS : IsFinite (Spec.map (π.resLE U V h).appTop) := (IsFinite.SpecMap_iff _).mpr
      ((RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso π U V h)).mpr hfin)
    rw [Arrow.iso_w' (arrowIsoSpecΓOfIsAffine (π.resLE U V h)).symm]
    infer_instance
  have : UniversallyClosed (Y.homOfLE h ≫ π ∣_ U) := by
    change UniversallyClosed (π.resLE U V h)
    infer_instance
  have : UniversallyClosed (Y.homOfLE h) := .of_comp_of_isSeparated _ (π ∣_ U)
  obtain ⟨y, hy⟩ := hne
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨y, h hy⟩⟩
  have hcl : IsClopen (Set.range (Y.homOfLE h).base) :=
    ⟨(Y.homOfLE h).isClosedMap.isClosed_range,
      (Y.homOfLE h).isOpenEmbedding.isOpenMap.isOpen_range⟩
  have huniv : Set.range (Y.homOfLE h).base = Set.univ :=
    (isClopen_iff.mp hcl).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨_, ⟨⟨y, hy⟩, rfl⟩⟩)
  refine le_antisymm (fun x hx => ?_) h
  obtain ⟨⟨w, hw⟩, hz⟩ : (⟨x, hx⟩ : π ⁻¹ᵁ U) ∈ Set.range (Y.homOfLE h).base := by
    rw [huniv]; trivial
  have hz' : ((Y.homOfLE h) ⟨w, hw⟩).1 = x := congrArg Subtype.val hz
  have hzx : w = x := (Scheme.homOfLE_apply h ⟨w, hw⟩).symm.trans hz'
  exact hzx ▸ hw

end GlobalTheory
end

