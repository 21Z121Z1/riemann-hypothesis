import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitQuadraticOrderPrincipal
section
namespace GlobalTheory.CompanionTheory.SplitQuadratic

theorem isPrincipalIdealRing_of_sq_eq_sq :
    ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O]
      (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) →
      (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) →
      (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) →
      IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by
  intro R O _ _ _ _ ι δ e hδ hspan _ he h2
  obtain ⟨e', he'⟩ := he.exists_right_inv
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  have hee' : ι e * ι e' = 1 := by rw [← map_mul, he', map_one]
  have h2' : 2 * ι h = 1 := by
    have := congrArg ι hh
    rwa [map_mul, map_one, map_ofNat] at this
  have hδ' : δ * δ = ι e * ι e := by rw [hδ, map_mul]

  have hu2 : (ι e' * δ) * (ι e' * δ) = 1 := by
    linear_combination (ι e' * ι e') * hδ' + (ι e * ι e' + 1) * hee'

  set ε₁ : O := ι h * (1 + ι e' * δ) with hε₁
  set ε₂ : O := ι h * (1 - ι e' * δ) with hε₂
  have h11 : ε₁ * ε₁ = ε₁ := by
    rw [hε₁]
    linear_combination (ι h * (1 + ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h22 : ε₂ * ε₂ = ε₂ := by
    rw [hε₂]
    linear_combination (ι h * (1 - ι e' * δ)) * h2' + (ι h * ι h) * hu2
  have h12 : ε₁ * ε₂ = 0 := by
    rw [hε₁, hε₂]
    linear_combination (-(ι h * ι h)) * hu2
  have hsum : ε₁ + ε₂ = 1 := by
    rw [hε₁, hε₂]
    linear_combination h2'

  let φ : R × R →+* O :=
    { toFun := fun x => ι x.1 * ε₁ + ι x.2 * ε₂
      map_one' := by
        simp only [Prod.fst_one, Prod.snd_one, map_one, one_mul]
        exact hsum
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination (-(ι x.1 * ι y.1)) * h11 + (-(ι x.2 * ι y.2)) * h22 +
          (-(ι x.1 * ι y.2 + ι x.2 * ι y.1)) * h12
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        ring }
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨p, q, rfl⟩ := hspan y
    refine ⟨(p + q * e, p - q * e), ?_⟩
    show ι (p + q * e) * ε₁ + ι (p - q * e) * ε₂ = ι p + ι q * δ
    rw [hε₁, hε₂]
    simp only [map_add, map_sub, map_mul]
    linear_combination (ι p + ι q * ι e * ι e' * δ) * h2' + (ι q * δ) * hee'
  exact IsPrincipalIdealRing.of_surjective φ hsurj

end GlobalTheory.CompanionTheory.SplitQuadratic
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StripOpenRealDiscs
section
namespace GlobalTheory.CompanionTheory.Strip

theorem strip_open_real_discs (n : ℕ) (X : Fin n → ℝ) :
    IsOpen {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} ∧
    (∀ t : ℝ, (t : ℂ) ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}) ∧
    ∀ z ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}, ∃ (t ρ : ℝ), 0 < ρ ∧
      z ∈ Metric.ball (t : ℂ) ρ ∧
      Metric.ball (t : ℂ) ρ ⊆ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} := by
  set S := {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} with hS
  have hpi : 0 < Real.pi / 4 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have h : S = ⋂ j, {z : ℂ | |z.im * X j| < Real.pi / 4} := by
      ext z
      simp [hS]
    rw [h]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  · intro t
    simp [hS, hpi]
  · intro z hz
    have hopen : IsOpen {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
      have h : {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} = ⋂ j, {r : ℝ | r * |X j| < Real.pi / 4} := by
        ext r
        simp
      rw [h]
      exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
    have hmem : |z.im| ∈ {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
      intro j
      have h := hz j
      rwa [abs_mul] at h
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
    refine ⟨z.re, |z.im| + ε / 2, by positivity, ?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      linarith
    · intro w hw j
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      have him : |w.im| < |z.im| + ε / 2 := by
        have h1 : |(w - (z.re : ℂ)).im| ≤ ‖w - (z.re : ℂ)‖ := Complex.abs_im_le_norm _
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
        linarith
      have hρ : (|z.im| + ε / 2) * |X j| < Real.pi / 4 := by
        have hin : |z.im| + ε / 2 ∈ Metric.ball |z.im| ε := by
          rw [Metric.mem_ball, Real.dist_eq, show |z.im| + ε / 2 - |z.im| = ε / 2 by ring,
            abs_of_pos (by positivity)]
          linarith
        exact hball hin j
      show |w.im * X j| < Real.pi / 4
      rw [abs_mul]
      calc |w.im| * |X j| ≤ (|z.im| + ε / 2) * |X j| :=
            mul_le_mul_of_nonneg_right him.le (abs_nonneg _)
        _ < Real.pi / 4 := hρ

end GlobalTheory.CompanionTheory.Strip
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumPerfectApply
section
namespace GlobalTheory.CompanionTheory.Pairing

theorem sum_perfect_apply {R : Type} [CommRing R] {ι : Type} [Fintype ι] {X Y : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] [∀ i, AddCommGroup (Y i)]
    [∀ i, Module R (Y i)] (B : ∀ i, Y i →ₗ[R] X i →ₗ[R] R)
    (y : ∀ i, Y i) (x : ∀ i, X i) :
    (∑ i, (B i).compl₁₂ (LinearMap.proj i : (∀ i, Y i) →ₗ[R] Y i)
      (LinearMap.proj i : (∀ i, X i) →ₗ[R] X i)) y x = ∑ i, B i (y i) (x i) := by
  simp [LinearMap.sum_apply]

theorem sum_perfect : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (X Y : ι → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)] (B : ∀ i, Y i →ₗ[R] X i →ₗ[R] R), (∀ i, Function.Injective (B i)) → (∀ i, Function.Injective (B i).flip) → Function.Injective (∑ i, (B i).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)) ∧ Function.Injective (∑ i, (B i).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)).flip := by
  intro R _ ι _ X Y _ _ _ _ B hB hBf
  classical
  constructor
  · rw [← LinearMap.coe_sum, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    funext j
    have hj : B j (y j) = 0 := by
      ext x₀
      have h := LinearMap.congr_fun hy (Pi.single j x₀)
      rw [sum_perfect_apply, Fintype.sum_eq_single j (fun i hi => by rw [Pi.single_eq_of_ne hi, map_zero]),
        Pi.single_eq_same] at h
      simpa using h
    exact hB j (hj.trans (map_zero _).symm)
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    funext j
    have hj : (B j).flip (x j) = 0 := by
      ext y₀
      have h := LinearMap.congr_fun hx (Pi.single j y₀)
      rw [LinearMap.flip_apply, sum_perfect_apply, Fintype.sum_eq_single j (fun i hi => by
        rw [Pi.single_eq_of_ne hi, map_zero, LinearMap.zero_apply]), Pi.single_eq_same] at h
      simpa using h
    exact hBf j (hj.trans (map_zero _).symm)

end GlobalTheory.CompanionTheory.Pairing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableLatticeWeightThree
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.MajSum

lemma summable_one_add_abs_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun m : ℤ => ((1 + |(m : ℝ)|) ^ s)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hs) ?_
  have hcof : ({0} : Set ℤ)ᶜ ∈ cofinite := (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite
  have hev : ∀ᶠ m : ℤ in cofinite, ‖((1 + |(m : ℝ)|) ^ s)⁻¹‖ ≤ |(m : ℝ)| ^ (-s) := by
    filter_upwards [hcof] with m hm
    have hm' : m ≠ 0 := by simpa using hm
    have hm0 : 0 < |(m : ℝ)| := abs_pos.2 (by exact_mod_cast hm')
    have hpos : 0 < 1 + |(m : ℝ)| := by linarith
    rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.rpow_nonneg hpos.le s)), Real.rpow_neg hm0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hm0 s)
      (Real.rpow_le_rpow hm0.le (by linarith) (by linarith))
  simpa [Filter.eventually_cofinite] using hev

lemma term_le {x y z c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hc : 1 ≤ c) :
    ((1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2)⁻¹ ≤
      c ^ 5 * (((1 + x) ^ (3 / 2 : ℝ))⁻¹ * (((1 + y) ^ (3 / 2 : ℝ))⁻¹ * ((1 + z) ^ (2 : ℝ))⁻¹)) := by
  have hc0 : 0 < c := by linarith
  have hX : 0 < 1 + x := by linarith
  have hY : 0 < 1 + y := by linarith
  have hZ : 0 < 1 + z := by linarith
  have hS : 0 < 1 + x + y := by linarith
  have h1 : (1 + x) ^ (3 / 2 : ℝ) * (1 + y) ^ (3 / 2 : ℝ) ≤ (1 + x + y) ^ 3 := by
    rw [← Real.mul_rpow hX.le hY.le]
    have hle : (1 + x) * (1 + y) ≤ (1 + x + y) ^ 2 := by nlinarith [mul_nonneg hx hy]
    calc ((1 + x) * (1 + y)) ^ (3 / 2 : ℝ)
        ≤ ((1 + x + y) ^ 2) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = (1 + x + y) ^ 3 := by
          rw [← Real.rpow_natCast (1 + x + y) 2, ← Real.rpow_mul hS.le,
            ← Real.rpow_natCast (1 + x + y) 3]
          norm_num
  have h2 : 1 + x + y ≤ c * (1 + x / c + y / c) := by
    have : c * (1 + x / c + y / c) = c + x + y := by field_simp
    rw [this]; linarith
  have h3 : 1 + z ≤ c * (1 + z / c) := by
    have : c * (1 + z / c) = c + z := by field_simp
    rw [this]; linarith
  have hP : 0 < 1 + x / c + y / c := by positivity
  have hQ : 0 < 1 + z / c := by positivity
  have h4 : (1 + x + y) ^ 3 ≤ (c * (1 + x / c + y / c)) ^ 3 :=
    pow_le_pow_left₀ hS.le h2 3
  have h5 : (1 + z) ^ 2 ≤ (c * (1 + z / c)) ^ 2 := pow_le_pow_left₀ hZ.le h3 2
  have hA : 0 < (1 + x) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hX _
  have hB : 0 < (1 + y) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hY _
  have hC : 0 < (1 + z) ^ (2 : ℝ) := Real.rpow_pos_of_pos hZ _
  have hC' : (1 + z) ^ (2 : ℝ) = (1 + z) ^ 2 := by
    rw [← Real.rpow_natCast (1 + z) 2]; norm_num
  have key : (1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)) ≤
      c ^ 5 * ((1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2) := by
    rw [hC', ← mul_assoc]
    calc (1 + x) ^ (3 / 2 : ℝ) * (1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ 2
        ≤ (c * (1 + x / c + y / c)) ^ 3 * (c * (1 + z / c)) ^ 2 :=
          mul_le_mul (h1.trans h4) h5 (by positivity) (by positivity)
      _ = c ^ 5 * ((1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2) := by ring
  have hD : 0 < (1 + x / c + y / c) ^ 3 * (1 + z / c) ^ 2 := by positivity
  have hE : 0 < (1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)) := by
    positivity
  have hinv : ((1 + x) ^ (3 / 2 : ℝ))⁻¹ * (((1 + y) ^ (3 / 2 : ℝ))⁻¹ * ((1 + z) ^ (2 : ℝ))⁻¹) =
      ((1 + x) ^ (3 / 2 : ℝ) * ((1 + y) ^ (3 / 2 : ℝ) * (1 + z) ^ (2 : ℝ)))⁻¹ := by
    rw [mul_inv, mul_inv]
  rw [hinv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hD hE]
  linarith

lemma exists_int_of_den_eq_one {M : ℕ} (hM : 0 < M) {q : ℚ} (h : ((M : ℚ) * q).den = 1) :
    ∃ m : ℤ, (m : ℚ) / M = q := by
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨((M : ℚ) * q).num, ?_⟩
  rw [Rat.coe_int_num_of_den_eq_one h]
  field_simp

theorem summable_lattice_majorant :
    ∀ M : ℕ, 0 < M → Summable (fun p : ℚ × ℚ × ℚ =>
      if ((M : ℚ) * p.1).den = 1 ∧ ((M : ℚ) * p.2.1).den = 1 ∧ ((M : ℚ) * p.2.2).den = 1 then
        ((1 + |(p.1 : ℝ)| + |(p.2.1 : ℝ)|) ^ 3 * (1 + |(p.2.2 : ℝ)|) ^ 2)⁻¹ else (0 : ℝ)) := by
  intro M hM
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let g : ℤ × ℤ × ℤ → ℚ × ℚ × ℚ :=
    fun t => ((t.1 : ℚ) / M, (t.2.1 : ℚ) / M, (t.2.2 : ℚ) / M)
  have hdiv : ∀ a b : ℤ, (a : ℚ) / M = (b : ℚ) / M → a = b := by
    intro a b hab
    have : (a : ℚ) = b := by
      field_simp at hab
      exact hab
    exact_mod_cast this
  have hg : Function.Injective g := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [hdiv _ _ h1, hdiv _ _ h2, hdiv _ _ h3]
  have hden : ∀ a : ℤ, ((M : ℚ) * ((a : ℚ) / M)).den = 1 := by
    intro a
    rw [mul_div_cancel₀ _ hM0]
    exact Rat.den_intCast a
  refine (hg.summable_iff ?_).1 ?_
  · rintro ⟨p, q, r⟩ hx
    refine if_neg ?_
    rintro ⟨h1, h2, h3⟩
    obtain ⟨a, rfl⟩ := exists_int_of_den_eq_one hM h1
    obtain ⟨b, rfl⟩ := exists_int_of_den_eq_one hM h2
    obtain ⟨c, rfl⟩ := exists_int_of_den_eq_one hM h3
    exact hx ⟨(a, b, c), rfl⟩
  · have hA := summable_one_add_abs_rpow (s := 3 / 2) (by norm_num)
    have hC := summable_one_add_abs_rpow (s := 2) (by norm_num)
    have hnA : 0 ≤ fun m : ℤ => ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ := fun m => by
      positivity
    have hnC : 0 ≤ fun m : ℤ => ((1 + |(m : ℝ)|) ^ (2 : ℝ))⁻¹ := fun m => by
      positivity
    have hBC := hA.mul_of_nonneg hC hnA hnC
    have hnBC : 0 ≤ fun t : ℤ × ℤ =>
        ((1 + |(t.1 : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ * ((1 + |(t.2 : ℝ)|) ^ (2 : ℝ))⁻¹ := fun t => by
      positivity
    have hABC := (hA.mul_of_nonneg hBC hnA hnBC).mul_left ((M : ℝ) ^ 5)
    refine Summable.of_nonneg_of_le ?_ ?_ hABC
    · rintro ⟨a, b, c⟩
      simp only [Function.comp, g]
      split_ifs <;> positivity
    · rintro ⟨a, b, c⟩
      simp only [Function.comp, g]
      rw [if_pos ⟨hden a, hden b, hden c⟩]
      have hcast : ∀ u : ℤ, |(((u : ℚ) / M : ℚ) : ℝ)| = |(u : ℝ)| / M := by
        intro u
        push_cast
        rw [abs_div, Nat.abs_cast]
      rw [hcast a, hcast b, hcast c]
      exact term_le (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hMR

end GlobalTheory.CompanionTheory.MajSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfLatticeDecay
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.LatticeCount

theorem summable_inv_one_add_sq_int :
    Summable (fun m : ℤ => ((1 : ℝ) + (m : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine Summable.of_norm_bounded_eventually h ?_
  have hfin : ({0} : Set ℤ).Finite := Set.finite_singleton 0
  refine Filter.mem_cofinite.2 (hfin.subset ?_)
  intro m hm
  by_contra h0
  have h0' : m ≠ 0 := by simpa using h0
  apply hm
  have hm0 : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast h0'
    positivity
  have hpos : (0 : ℝ) < 1 + (m : ℝ) ^ 2 := by positivity
  show ‖((1 : ℝ) + (m : ℝ) ^ 2)⁻¹‖ ≤ 1 / (m : ℝ) ^ 2
  rw [Real.norm_of_nonneg (inv_nonneg.2 hpos.le), one_div]
  exact inv_anti₀ hm0 (by linarith)

theorem summable_prod_inv_one_add_sq (d : ℕ) :
    Summable (fun n : Fin d → ℤ => ∏ k, ((1 : ℝ) + (n k : ℝ) ^ 2)⁻¹) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
    have h2 := summable_inv_one_add_sq_int.mul_of_nonneg ih
      (fun m => by positivity) (fun n => Finset.prod_nonneg (fun k _ => by positivity))
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff]
    refine h2.congr ?_
    intro x
    simp [Fin.prod_univ_succ, Fin.consEquiv]
    exact mul_comm _ _

theorem summable_of_lattice_decay (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ)
    (hf : Function.Injective f) (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hC : ∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C)
    (hint : ∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) : Summable w := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let S := {i // w i ≠ 0}
  choose n hn using fun i : S => hint i.1 i.2
  have hinj : Function.Injective n := by
    intro a b hab
    apply Subtype.ext
    apply hf
    funext k
    have h1 := hn a k
    have h2 := hn b k
    rw [hab] at h1
    exact mul_left_cancel₀ hNpos.ne' (h1.trans h2.symm)
  have hg := ((summable_prod_inv_one_add_sq d).comp_injective hinj).mul_left (((N : ℝ) ^ 2) ^ d * C)
  have hbound : ∀ a : S, ‖w a.1‖ ≤ ((N : ℝ) ^ 2) ^ d * C *
      ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)⁻¹ := by
    intro a
    have hle : ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) ≤
        ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) := by
      have : ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) =
          ∏ k : Fin d, ((N : ℝ) ^ 2 * (1 + f a.1 k ^ 2)) := by
        rw [Finset.prod_mul_distrib]; simp
      rw [this]
      refine Finset.prod_le_prod (fun k _ => by positivity) (fun k _ => ?_)
      rw [← hn a k]
      have : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hpos : (0 : ℝ) < ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) :=
      Finset.prod_pos (fun k _ => by positivity)
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖w a.1‖ * ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)
        ≤ ‖w a.1‖ * (((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ((N : ℝ) ^ 2) ^ d * (‖w a.1‖ * ∏ k, (1 + f a.1 k ^ 2)) := by ring
      _ ≤ ((N : ℝ) ^ 2) ^ d * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hsub : Summable (w ∘ (Subtype.val : S → ι)) :=
    Summable.of_norm_bounded hg hbound
  refine (Function.Injective.summable_iff Subtype.val_injective ?_).1 hsub
  intro x hx
  by_contra h0
  exact hx ⟨⟨x, h0⟩, rfl⟩

end GlobalTheory.CompanionTheory.LatticeCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOverLatticeQuotientLocallyConstant
section
open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem integrable_of_summable_quotient_periodic :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] (ν : Measure G) [ν.IsAddHaarMeasure] (U : AddSubgroup G),
    IsOpen (U : Set G) → IsCompact (U : Set G) → ∀ ι : H →+ G, (∀ g, ∃ h, g - ι h ∈ U) →
    ∀ f : G → ℂ, (∀ g, ∀ u ∈ U, f (g + u) = f g) →
    Summable (fun x : H ⧸ U.comap ι => ‖f (ι (Quotient.out x))‖) → Integrable f ν := by
  intro G H _ _ _ _ _ _ _ ν _ U hUo hUc ι hι f hf hs
  let r : H ⧸ U.comap ι → G := fun x => ι (Quotient.out x)
  let c : H ⧸ U.comap ι → Set G := fun x => (fun g => g - r x) ⁻¹' (U : Set G)
  have hcopen : ∀ x, IsOpen (c x) := fun x => hUo.preimage (by fun_prop)
  have hcov : ⋃ x, c x = univ := by
    refine eq_univ_of_forall fun g => mem_iUnion.2 ?_
    obtain ⟨h, hh⟩ := hι g
    refine ⟨(QuotientAddGroup.mk h : H ⧸ U.comap ι), ?_⟩
    have h1 : -h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι) ∈ U.comap ι :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
    have h2 : ι (-h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι)) ∈ U := h1
    have h3 := U.sub_mem hh h2
    have h4 : g - ι h - ι (-h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι))
        = g - r (QuotientAddGroup.mk h : H ⧸ U.comap ι) := by
      simp only [r, map_add, map_neg]; abel
    change g - r _ ∈ U
    rwa [h4] at h3
  have hdisj : Pairwise (Function.onFun Disjoint c) := by
    intro x y hxy
    refine Set.disjoint_left.2 fun g hgx hgy => hxy ?_
    have hgx' : g - r x ∈ U := hgx
    have hgy' : g - r y ∈ U := hgy
    have h1 : ι (-Quotient.out x + Quotient.out y) ∈ U := by
      have h3 := U.sub_mem hgx' hgy'
      have h4 : g - r x - (g - r y) = ι (-Quotient.out x + Quotient.out y) := by
        simp only [r, map_add, map_neg]; abel
      rwa [h4] at h3
    have h2 : (QuotientAddGroup.mk (Quotient.out x) : H ⧸ U.comap ι) = QuotientAddGroup.mk (Quotient.out y) :=
      QuotientAddGroup.eq.2 h1
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h2
  have hne : ∀ x, (c x).Nonempty := fun x => ⟨r x, by
    change r x - r x ∈ U
    simp⟩
  have hcount : Countable (H ⧸ U.comap ι) := by
    have hinj : Function.Injective c := by
      intro x y hxy
      by_contra hne'
      obtain ⟨g, hg⟩ := hne x
      exact Set.disjoint_left.1 (hdisj hne') hg (hxy ▸ hg)
    have hpd : (range c).PairwiseDisjoint id := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      exact hdisj (fun h => hxy (by rw [h]))
    have := hpd.countable_of_isOpen (by rintro _ ⟨x, rfl⟩; exact hcopen x)
      (by rintro _ ⟨x, rfl⟩; exact hne x)
    have := this.to_subtype
    exact Function.Injective.countable (f := Set.rangeFactorization c)
      (fun x y h => hinj (congrArg Subtype.val h))
  have hconst : ∀ x, ∀ g ∈ c x, f g = f (r x) := by
    intro x g hg
    have := hf (r x) (g - r x) hg
    rw [← this]; congr 1; abel
  have hcont : Continuous f := by
    refine IsLocallyConstant.continuous ?_
    refine (IsLocallyConstant.iff_exists_open f).2 fun g => ?_
    refine ⟨(fun y => y - g) ⁻¹' (U : Set G), hUo.preimage (by fun_prop), by simp, ?_⟩
    intro y hy
    have := hf g (y - g) hy
    rw [← this]; congr 1; abel
  have hmeas : ∀ x, ν (c x) = ν (U : Set G) := by
    intro x
    have : c x = (fun g => g + (- r x)) ⁻¹' (U : Set G) := by
      ext g; simp [c, sub_eq_add_neg]
    rw [this, measure_preimage_add_right]
  have hUfin : ν (U : Set G) < ⊤ := hUc.measure_lt_top
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hsum : ∑' x, ‖f (r x)‖ₑ < ⊤ := by
    have h1 : ∑' x, ‖f (r x)‖ₑ = ∑' x, ENNReal.ofReal ‖f (r x)‖ := by
      simp [ofReal_norm_eq_enorm]
    rw [h1]
    exact hs.tsum_ofReal_lt_top
  have hint : ∫⁻ g, ‖f g‖ₑ ∂ν = (∑' x, ‖f (r x)‖ₑ) * ν (U : Set G) := by
    calc ∫⁻ g, ‖f g‖ₑ ∂ν = ∫⁻ g in ⋃ x, c x, ‖f g‖ₑ ∂ν := by rw [hcov, Measure.restrict_univ]
      _ = ∑' x, ∫⁻ g in c x, ‖f g‖ₑ ∂ν :=
          lintegral_iUnion (fun x => (hcopen x).measurableSet) hdisj _
      _ = ∑' x, ‖f (r x)‖ₑ * ν (U : Set G) := by
          refine tsum_congr fun x => ?_
          rw [setLIntegral_congr_fun (hcopen x).measurableSet
            (g := fun _ => ‖f (r x)‖ₑ) (fun g hg => by simp only [hconst x g hg]),
            setLIntegral_const, hmeas]
      _ = (∑' x, ‖f (r x)‖ₑ) * ν (U : Set G) := ENNReal.tsum_mul_right
  change ∫⁻ g, ‖f g‖ₑ ∂ν < ⊤
  rw [hint]
  exact ENNReal.mul_lt_top hsum hUfin

end GlobalTheory.CompanionTheory.SiegelND.Integ
end

