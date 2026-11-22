import ReciprocityTheory.SemistableReduction.Bundle0003
import ReciprocityTheory.SemistableReduction.Bundle0010
import Lemmata.MiscLemmasR.Imports
import ReciprocityTheory.SemistableReduction.Bundle0009
import ReciprocityTheory.SemistableReduction.Bundle0001
import ReciprocityTheory.SemistableReduction.SphereTorusA

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegCC
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

theorem hermForm_smul_smul {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a b : K) (u w : Fin r → K) : S.h (a • u) (b • w) = S.c a * b * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermForm_sum_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {ι : Type} (s : Finset ι) (u : ι → Fin r → K) (w : Fin r → K) :
    S.h (∑ i ∈ s, u i) w = ∑ i ∈ s, S.h (u i) w := by
  simp only [HermForm.h, Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

theorem hermForm_conj {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (u w : Fin r → K) : S.c (S.h u w) = S.h w u := by
  simp only [HermForm.h, map_sum, map_mul, S.c_invol, S.G_herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def intInv {K : Type} [Field K] [NumberField K] (c : K →+* K) : 𝓞 K →+* 𝓞 K :=
  RingOfIntegers.mapRingHom c

theorem intInv_coe {K : Type} [Field K] [NumberField K] (c : K →+* K) (a : 𝓞 K) :
    algebraMap (𝓞 K) K (intInv c a) = c (algebraMap (𝓞 K) K a) := rfl

theorem mem_one_map {K : Type} [Field K] [NumberField K] (c : K →+* K) {x : K}
    (hx : x ∈ (1 : Submodule (𝓞 K) K)) : c x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.mp hx
  exact Submodule.mem_one.mpr ⟨intInv c y, intInv_coe c y⟩

def cImage {K : Type} [Field K] [NumberField K] (c : K →+* K) (C : Submodule (𝓞 K) K) :
    Submodule (𝓞 K) K := Bl.ThirdBlockLemmaC.goal1 c C

theorem mem_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K) (C : Submodule (𝓞 K) K)
    {x : K} : x ∈ cImage c C ↔ c x ∈ C := Iff.rfl

theorem cImage_fg {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (C : Submodule (𝓞 K) K) (hC : C.FG) : (cImage c C).FG := by
  haveI : RingHomSurjective (intInv c) :=
    ⟨fun y => ⟨intInv c y, by
      apply RingOfIntegers.ext
      show algebraMap (𝓞 K) K (intInv c (intInv c y)) = algebraMap (𝓞 K) K y
      rw [intInv_coe, intInv_coe, hc]⟩⟩
  let f : K →ₛₗ[intInv c] K :=
    { toFun := c
      map_add' := map_add c
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, intInv_coe] }
  have h : cImage c C = C.map f := by
    ext x
    rw [mem_cImage, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨c x, hx, hc x⟩
    · rintro ⟨y, hy, rfl⟩
      show c (c y) ∈ C
      rw [hc]
      exact hy
  rw [h]
  exact hC.map f

theorem one_le_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K)
    (C : Submodule (𝓞 K) K) (h1 : 1 ≤ C) : 1 ≤ cImage c C := by
  intro x hx
  rw [mem_cImage]
  exact h1 (mem_one_map c hx)

theorem relIndex_cImage {K : Type} [Field K] [NumberField K] (c : K →+* K)
    (hc : ∀ x, c (c x) = x) (C : Submodule (𝓞 K) K) :
    (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex (cImage c C).toAddSubgroup =
      (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup := by
  have h1 : (1 : Submodule (𝓞 K) K).toAddSubgroup
      = (1 : Submodule (𝓞 K) K).toAddSubgroup.comap c.toAddMonoidHom := by
    ext x
    constructor
    · intro hx
      exact mem_one_map c hx
    · intro hx
      have h' : c (c x) ∈ (1 : Submodule (𝓞 K) K) := mem_one_map c hx
      rwa [hc] at h'
  have h2 : (cImage c C).toAddSubgroup = C.toAddSubgroup.comap c.toAddMonoidHom := by
    ext x
    exact mem_cImage c C
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  · rw [← h1]
  · exact fun y => ⟨c y, hc y⟩

theorem prod_mem_prod_sub {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) (x : Fin k → K) (hx : ∀ i, x i ∈ p i) :
    ∏ i, x i ∈ ∏ i, p i := by
  classical
  suffices h : ∀ s : Finset (Fin k), ∏ i ∈ s, x i ∈ ∏ i ∈ s, p i by exact h Finset.univ
  intro s
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (hx a) ih

theorem det_mem_prod_sub {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) (T : Matrix (Fin k) (Fin k) K)
    (hT : ∀ i j, T i j ∈ p i) : T.det ∈ ∏ i, p i := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem_prod_sub p (fun i => Tᵀ (σ i) i) fun i => hT i (σ i)) _

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SjHolds
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric Real

theorem sj_holds (hLin : SphereLinLogStatement) : SJStatement := by
  intro n a f u hf hu hfu
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) := nontrivial_of_ne u 0 hu0
  haveI hprob : IsProbabilityMeasure (sphereProb n) := by
    unfold sphereProb
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · rw [Measure.toSphere_apply_univ]
      refine mul_ne_zero ?_ (Metric.measure_ball_pos _ _ one_pos).ne'
      exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    · rw [Measure.toSphere_apply_univ]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  have hT : (0:ℝ) < 2 * π := by positivity

  have hsp : Continuous (fun z : UnitSphereC n => spherePoint z) := by
    unfold spherePoint; fun_prop
  have hcont : Continuous (fun z : UnitSphereC n => MvPolynomial.eval (spherePoint z) f) :=
    (MvPolynomial.continuous_eval f).comp hsp
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨L, hL⟩ : ∃ L : UnitSphereC n → ℝ,
      L = fun z => Real.log ‖MvPolynomial.eval (spherePoint z) f‖ := ⟨_, rfl⟩
  have hLM : ∀ z, L z ≤ M := fun z => by
    rw [hL]
    exact (Real.log_le_self (norm_nonneg _)).trans (hM z (Set.mem_univ _))
  have hLmeas : Measurable L := by
    rw [hL]; exact hcont.norm.measurable.log

  obtain ⟨c, hc⟩ : ∃ c : EuclideanSpace ℂ (Fin n),
      c = WithLp.toLp 2 (fun i => starRingEnd ℂ (WithLp.ofLp u i)) := ⟨_, rfl⟩
  have hcn : ‖c‖ = 1 := by
    rw [← hu, hc, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hcn; exact zero_ne_one hcn
  obtain ⟨hGint, hGeq⟩ := hLin n c hc0
  obtain ⟨G, hG⟩ : ∃ G : UnitSphereC n → ℝ,
      G = fun z => Real.log ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ := ⟨_, rfl⟩
  have hGint' : Integrable G (sphereProb n) := by rw [hG]; exact hGint
  have hGeq' : ∫ z, G z ∂(sphereProb n) = Real.log ‖c‖ - (harmonic (n - 1) : ℝ) / 2 := by
    rw [hG]; exact hGeq
  have hip : ∀ z : UnitSphereC n,
      ‖inner ℂ u (z : EuclideanSpace ℂ (Fin n))‖ = ‖∑ i, WithLp.ofLp c i * spherePoint z i‖ := by
    intro z
    rw [hc]
    simp [PiLp.inner_apply, spherePoint, mul_comm]

  have hpoly : ∀ (w v : Fin n → ℂ) (ζ : ℂ) (p : MvPolynomial (Fin n) ℂ),
      (MvPolynomial.aeval (fun i => Polynomial.C (w i) + Polynomial.C (v i) * Polynomial.X) p).eval ζ =
        MvPolynomial.eval (fun i => w i + ζ * v i) p := by
    intro w v ζ p
    induction p using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp =>
      simp [hp]
      exact Or.inl (mul_comm _ _)

  have hcirc : ∀ z : UnitSphereC n, inner ℂ u (z : EuclideanSpace ℂ (Fin n)) ≠ 0 →
      IntegrableOn (fun θ => L (rotS hu θ z)) (Set.Ioc 0 (2 * π)) ∧
      2 * π * (Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ +
          (a : ℝ) * Real.log ‖inner ℂ u (z : EuclideanSpace ℂ (Fin n))‖) ≤
        ∫ θ in Set.Ioc 0 (2 * π), L (rotS hu θ z) := by
    intro z hz
    set s := inner ℂ u (z : EuclideanSpace ℂ (Fin n)) with hs
    set q : Polynomial ℂ := MvPolynomial.aeval (fun i => Polynomial.C (s * WithLp.ofLp u i) +
      Polynomial.C (WithLp.ofLp (z : EuclideanSpace ℂ (Fin n)) i - s * WithLp.ofLp u i) * Polynomial.X) f
      with hqdef
    have hq : ∀ ζ, q.eval ζ = MvPolynomial.eval (fun i => s * WithLp.ofLp u i +
        ζ * (WithLp.ofLp (z : EuclideanSpace ℂ (Fin n)) i - s * WithLp.ofLp u i)) f := fun ζ => by
      rw [hqdef]; exact hpoly _ _ _ _
    have hq0 : q.eval 0 = s ^ a * MvPolynomial.eval (WithLp.ofLp u) f := by
      rw [hq]; simp only [zero_mul, add_zero]
      exact eval_smul_of_isHomogeneous hf s _
    have hrot : ∀ θ : ℝ, spherePoint (rotS hu θ z) = fun i => s * WithLp.ofLp u i +
        circleMap 0 1 θ * (WithLp.ofLp (z : EuclideanSpace ℂ (Fin n)) i - s * WithLp.ofLp u i) := by
      intro θ
      funext i
      simp [spherePoint, coe_rotS, hs]
    have hqc : ∀ θ : ℝ, Real.log ‖q.eval (circleMap 0 1 θ)‖ = L (rotS hu θ z) := by
      intro θ
      simp only [hL]
      rw [hq, hrot]
    have hne : q.eval 0 ≠ 0 := by
      rw [hq0]; exact mul_ne_zero (pow_ne_zero _ hz) hfu
    have hJ := log_norm_eval_zero_le_circleAverage q hne
    have hci : CircleIntegrable (fun ζ => Real.log ‖q.eval ζ‖) 0 1 :=
      circleIntegrable_log_norm_meromorphicOn
        (fun x _ => (q.differentiable.analyticAt x).meromorphicAt)
    have hii : IntervalIntegrable (fun θ => L (rotS hu θ z)) MeasureTheory.volume 0 (2 * π) := by
      have := hci
      unfold CircleIntegrable at this
      simpa only [hqc] using this
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hii, ?_⟩
    rw [hq0, norm_mul, norm_pow, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 hz))
      (norm_ne_zero_iff.2 hfu), Real.log_pow] at hJ
    unfold Real.circleAverage at hJ
    simp only [hqc, smul_eq_mul] at hJ
    rw [intervalIntegral.integral_of_le hT.le] at hJ
    have h2 := mul_le_mul_of_nonneg_left hJ hT.le
    rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul] at h2
    linarith

  obtain ⟨h, hh⟩ : ∃ h : UnitSphereC n → ℝ,
      h = fun z => M - Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ - (a : ℝ) * G z := ⟨_, rfl⟩
  have hae : ∀ᵐ (z : UnitSphereC n) ∂(sphereProb n), inner ℂ u (z : EuclideanSpace ℂ (Fin n)) ≠ 0 := by
    have := sphereProb_inner_eq_zero hu0
    exact ae_iff.2 (by simpa using this)
  have hC : ∀ᵐ (z : UnitSphereC n) ∂(sphereProb n), 0 ≤ h z ∧
      ∫⁻ θ in Set.Ioc 0 (2 * π), ENNReal.ofReal (M - L (rotS hu θ z)) ≤
        ENNReal.ofReal (2 * π) * ENNReal.ofReal (h z) := by
    filter_upwards [hae] with z hz
    obtain ⟨hint, hJ⟩ := hcirc z hz
    have hGz : Real.log ‖inner ℂ u (z : EuclideanSpace ℂ (Fin n))‖ = G z := by rw [hG, hip]
    rw [hGz] at hJ
    have hint2 : IntegrableOn (fun θ => M - L (rotS hu θ z)) (Set.Ioc 0 (2 * π)) :=
      (integrable_const M).sub hint
    have hI : ∫ θ in Set.Ioc 0 (2 * π), (M - L (rotS hu θ z)) =
        2 * π * M - ∫ θ in Set.Ioc 0 (2 * π), L (rotS hu θ z) := by
      rw [integral_sub (integrable_const M) hint, integral_const]
      simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hT.le, smul_eq_mul, Real.pi_pos.le]
    have hnn : 0 ≤ ∫ θ in Set.Ioc 0 (2 * π), (M - L (rotS hu θ z)) :=
      setIntegral_nonneg measurableSet_Ioc (fun θ _ => sub_nonneg.2 (hLM _))
    have hhz : 2 * π * h z = 2 * π * M - 2 * π * (Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ +
        (a : ℝ) * G z) := by
      rw [hh]; ring
    refine ⟨?_, ?_⟩
    · have : 0 ≤ 2 * π * h z := by linarith
      exact (mul_nonneg_iff_of_pos_left hT).1 this
    · rw [← ofReal_integral_eq_lintegral_ofReal hint2
        (ae_of_all _ fun θ => sub_nonneg.2 (hLM _)), ← ENNReal.ofReal_mul hT.le]
      exact ENNReal.ofReal_le_ofReal (by linarith)

  obtain ⟨g, hg⟩ : ∃ g : UnitSphereC n → ENNReal, g = fun z => ENNReal.ofReal (M - L z) :=
    ⟨_, rfl⟩
  have hgmeas : Measurable g := by
    rw [hg]; exact (measurable_const.sub hLmeas).ennreal_ofReal
  have hrotInv : ∀ θ, ∫⁻ z, g (rotS hu θ z) ∂(sphereProb n) = ∫⁻ z, g z ∂(sphereProb n) :=
    fun θ => (measurePreserving_rotS hu θ).lintegral_comp hgmeas
  have hmeas2 : Measurable (fun p : ℝ × UnitSphereC n => g (rotS hu p.1 p.2)) :=
    hgmeas.comp (continuous_rotS hu).measurable
  have hswap : ∫⁻ θ in Set.Ioc 0 (2 * π), ∫⁻ z, g (rotS hu θ z) ∂(sphereProb n) =
      ∫⁻ z, (∫⁻ θ in Set.Ioc 0 (2 * π), g (rotS hu θ z)) ∂(sphereProb n) :=
    lintegral_lintegral_swap hmeas2.aemeasurable
  have hleft : ∫⁻ θ in Set.Ioc 0 (2 * π), ∫⁻ z, g (rotS hu θ z) ∂(sphereProb n) =
      ENNReal.ofReal (2 * π) * ∫⁻ z, g z ∂(sphereProb n) := by
    simp_rw [hrotInv]
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  have hmain : ENNReal.ofReal (2 * π) * ∫⁻ z, g z ∂(sphereProb n) ≤
      ENNReal.ofReal (2 * π) * ∫⁻ z, ENNReal.ofReal (h z) ∂(sphereProb n) := by
    rw [← hleft, hswap, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hC] with z hz
    simp only [hg]
    exact hz.2
  have hglint : ∫⁻ z, g z ∂(sphereProb n) ≤ ∫⁻ z, ENNReal.ofReal (h z) ∂(sphereProb n) :=
    by
      have h0 : ENNReal.ofReal (2 * π) ≠ 0 := (ENNReal.ofReal_pos.2 hT).ne'
      have h1 : ENNReal.ofReal (2 * π) ≠ ⊤ := ENNReal.ofReal_ne_top
      first
        | exact (ENNReal.mul_le_mul_iff_right h0 h1).1 hmain
        | exact (ENNReal.mul_le_mul_iff_left h0 h1).1 hmain
        | exact (ENNReal.mul_le_mul_left h0 h1).1 hmain
        | exact ENNReal.le_of_mul_le_mul_left hmain h0 h1
  have hhint : Integrable h (sphereProb n) := by
    rw [hh]; exact ((integrable_const _).sub (integrable_const _)).sub (hGint'.const_mul _)
  have hfin : ∫⁻ z, g z ∂(sphereProb n) ≠ ⊤ := (hglint.trans_lt hhint.lintegral_lt_top).ne
  have hg0 : ∀ z, 0 ≤ M - L z := fun z => sub_nonneg.2 (hLM z)
  have hgint : Integrable (fun z => M - L z) (sphereProb n) := by
    have := integrable_toReal_of_lintegral_ne_top hgmeas.aemeasurable hfin
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [hg]
    exact ENNReal.toReal_ofReal (hg0 z)
  have hLint : Integrable L (sphereProb n) := by
    have := (integrable_const M).sub hgint
    refine this.congr (ae_of_all _ fun z => ?_)
    simp

  have hh0 : 0 ≤ᵐ[sphereProb n] h := by
    filter_upwards [hC] with z hz
    exact hz.1
  have hint_g : ∫ z, (M - L z) ∂(sphereProb n) ≤ ∫ z, h z ∂(sphereProb n) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgint.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae hh0 hhint.aestronglyMeasurable]
    apply ENNReal.toReal_mono hhint.lintegral_lt_top.ne
    simpa only [hg] using hglint
  have hIh : ∫ z, h z ∂(sphereProb n) = M - Real.log ‖MvPolynomial.eval (WithLp.ofLp u) f‖ -
      (a : ℝ) * ∫ z, G z ∂(sphereProb n) := by
    simp only [hh]
    rw [integral_sub (integrable_const _) (hGint'.const_mul _), integral_const, integral_const_mul]
    simp
  rw [hGeq', hcn, Real.log_one] at hIh
  have hIg : ∫ z, (M - L z) ∂(sphereProb n) = M - ∫ z, L z ∂(sphereProb n) := by
    rw [integral_sub (integrable_const _) hLint, integral_const]
    simp
  refine ⟨by rw [hL] at hLint; exact hLint, ?_⟩
  have hfin2 : ∫ z, L z ∂(sphereProb n) =
      ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) f‖ ∂(sphereProb n) := by rw [hL]
  rw [← hfin2]
  linarith

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SphereTorusB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory

def scaledTorusMean {ι : Type*} [Fintype ι] (r : ι → ℂ) (f : MvPolynomial ι ℂ) : ℝ :=
  ∫ θ, Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖ ∂(torusProb ι)

theorem scaledTorusMean_one {ι : Type*} [Fintype ι] (f : MvPolynomial ι ℂ) :
    scaledTorusMean (fun _ => 1) f = torusMean f := by
  unfold scaledTorusMean torusMean
  simp only [one_mul]

theorem eval_update_eq_eval_aeval {ι : Type*} [DecidableEq ι] (w : ι → ℂ) (i : ι) (z : ℂ)
    (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval (Function.update w i z) f =
      (MvPolynomial.aeval (fun j => if j = i then (Polynomial.X : Polynomial ℂ)
        else Polynomial.C (w j)) f).eval z := by
  induction f using MvPolynomial.induction_on
  · simp
  · simp_all
  rename_i p j hp
  simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X, Polynomial.eval_mul, hp]
  congr 1
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Function.update_of_ne h]

theorem eval_bind₁_scale {ι : Type*} (r w : ι → ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval w
        (MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f) =
      MvPolynomial.eval (fun j => r j * w j) f := by
  induction f using MvPolynomial.induction_on
  · simp
  · simp_all
  · simp_all

private theorem bind1_C_mul_X_ne_zero_of_ne_zero {ι : Type} (r : ι → ℂ) (hr : ∀ j, r j ≠ 0)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f ≠ 0 := by
  intro h
  apply hf
  refine MvPolynomial.funext fun v => ?_
  have hv := eval_bind₁_scale r (fun j => v j / r j) f
  rw [h, map_zero] at hv
  have e : (fun j => r j * (v j / r j)) = v := by
    funext j
    first
      | exact mul_div_cancel₀ (v j) (hr j)
      | field_simp [hr j]
      | (rw [mul_comm]; exact div_mul_cancel₀ (v j) (hr j))
  rw [e] at hv
  rw [← hv, map_zero]

theorem integrable_scaled {ι : Type} [Fintype ι] (hBasic : TorusMeanBasicStatement)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ) (hr : ∀ j, r j ≠ 0) :
    Integrable (fun θ => Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖)
      (torusProb ι) := by
  have h := (hBasic ι).1 _ (bind1_C_mul_X_ne_zero_of_ne_zero r hr f hf)
  simpa only [eval_bind₁_scale] using h

theorem scaledTorusMean_le_update {ι : Type} [Fintype ι] [DecidableEq ι]
    (hBasic : TorusMeanBasicStatement) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ)
    (hr : ∀ j, r j ≠ 0) (i : ι) (hri : ‖r i‖ ≤ 1) :
    scaledTorusMean r f ≤ scaledTorusMean (Function.update r i 1) f := by
  have hr' : ∀ j, Function.update r i 1 j ≠ 0 := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · rw [Function.update_of_ne h]; exact hr j
  obtain ⟨hI1, hE1⟩ := integral_torus_eq_iter i (integrable_scaled hBasic f hf r hr)
  obtain ⟨hI2, hE2⟩ := integral_torus_eq_iter i (integrable_scaled hBasic f hf _ hr')
  unfold scaledTorusMean
  rw [hE1, hE2]
  refine integral_mono hI1 hI2 fun x => ?_
  set p : Polynomial ℂ := MvPolynomial.aeval (fun j => if j = i then (Polynomial.X : Polynomial ℂ)
        else Polynomial.C (r j * torusPoint x j)) f
  have key : ∀ (s : ι → ℂ), (∀ j, j ≠ i → s j = r j) → ∀ t : ℝ,
      MvPolynomial.eval (fun j => s j * torusPoint (Function.update x i t) j) f =
        p.eval (s i * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))) := by
    intro s hs t
    rw [← eval_update_eq_eval_aeval]
    refine congrArg (fun w => MvPolynomial.eval w f) (funext fun j => ?_)
    by_cases h : j = i
    · subst h; simp [torusPoint]
    · simp [Function.update_of_ne h, hs j h, torusPoint]
  have k1 := key r (fun _ _ => rfl)
  have k2 := key (Function.update r i 1) (fun j h => Function.update_of_ne h _ _)
  simp only [Function.update_self, one_mul] at k2
  beta_reduce
  simp only [k1, k2]
  exact integral_log_eval_mul_le p (hr i) hri

theorem scaledTorusMean_le_torusMean {ι : Type} [Fintype ι] [DecidableEq ι]
    (hBasic : TorusMeanBasicStatement) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ)
    (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, ‖r j‖ ≤ 1) :
    scaledTorusMean r f ≤ torusMean f := by
  classical
  have key : ∀ s : Finset ι, scaledTorusMean r f ≤
      scaledTorusMean (fun j => if j ∈ s then (1 : ℂ) else r j) f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      refine ih.trans ?_
      have hr' : ∀ j, (fun j => if j ∈ s then (1 : ℂ) else r j) j ≠ 0 := fun j => by
        dsimp only
        split_ifs <;> simp [hr j]
      have hra : ‖(fun j => if j ∈ s then (1 : ℂ) else r j) a‖ ≤ 1 := by
        simp [ha, hr1 a]
      have hle := scaledTorusMean_le_update hBasic f hf _ hr' a hra
      have e : Function.update (fun j => if j ∈ s then (1 : ℂ) else r j) a 1 =
          fun j => if j ∈ insert a s then (1 : ℂ) else r j := by
        funext j
        by_cases hj : j = a
        · subst hj
          simp
        · simp [Finset.mem_insert, hj, Function.update_of_ne hj]
      rw [e] at hle
      exact hle
  have hu := key Finset.univ
  simp only [Finset.mem_univ, if_true] at hu
  rwa [scaledTorusMean_one] at hu

end ReciprocityTheory.MultiplicativeHeights
end
end

