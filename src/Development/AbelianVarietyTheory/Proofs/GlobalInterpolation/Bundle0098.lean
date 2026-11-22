import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0082
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StarDetMulDetMem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open Matrix

noncomputable section

namespace GlobalTheory.DetSelfDual

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem star_mem_one {a : E} (ha : a ∈ (1 : Submodule (𝓞 E) E)) : star a ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
  exact Submodule.mem_one.2 (star_range r)

theorem carries_iff (N : Submodule (𝓞 E) (Sp E n)) (A : Matrix (Fin n) (Fin n) E) :
    (∀ v ∈ stdLat E n, A.mulVec v ∈ N) ↔ ∀ j, A.col j ∈ N := by
  constructor
  · intro h j
    have := h _ (single_mem_stdLat j 1)
    rwa [map_one, Matrix.mulVec_single_one] at this
  · intro h v hv
    rw [Matrix.mulVec_eq_sum]
    refine N.sum_mem fun j _ => ?_
    obtain ⟨r, hr⟩ := (mem_stdLat v).1 hv j
    have : (MulOpposite.op (v j) • Aᵀ j : Sp E n) = r • A.col j := by
      funext i
      simp [← hr, Algebra.smul_def, Matrix.col, mul_comm]
    rw [this]
    exact N.smul_mem r (h j)

theorem det_mem_detLat {N : Submodule (𝓞 E) (Sp E n)} {A : Matrix (Fin n) (Fin n) E}
    (h : ∀ j, A.col j ∈ N) : A.det ∈ detLat N :=
  Submodule.subset_span ⟨A, (carries_iff N A).2 h, rfl⟩

omit [StarRing E] [NumberField E] in
theorem det_mem_one {A : Matrix (Fin n) (Fin n) E} (h : ∀ i j, A i j ∈ (1 : Submodule (𝓞 E) E)) :
    A.det ∈ (1 : Submodule (𝓞 E) E) := by
  choose B hB using fun i j => Submodule.mem_one.1 (h i j)
  refine Submodule.mem_one.2 ⟨Matrix.det (Matrix.of B), ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  simpa using hB i j

theorem star_det_mul_det_mem {N : Submodule (𝓞 E) (Sp E n)} (hN : dual (hStd E n) N = N)
    {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ j, A.col j ∈ N) (hB : ∀ j, B.col j ∈ N) :
    star A.det * B.det ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← Matrix.det_conjTranspose, ← Matrix.det_mul]
  refine det_mem_one fun i j => ?_
  have := (mem_dual N (B.col j)).1 (hN.symm ▸ hB j) _ (hA i)
  rw [hStd_apply] at this
  simpa [Matrix.mul_apply, Matrix.col] using this

theorem star_mul_mem {N : Submodule (𝓞 E) (Sp E n)} (hN : dual (hStd E n) N = N)
    {a b : E} (ha : a ∈ detLat N) (hb : b ∈ detLat N) : star a * b ∈ (1 : Submodule (𝓞 E) E) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨A, hA, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨B, hB, rfl⟩ := hy
      exact star_det_mul_det_mem hN ((carries_iff N A).1 hA) ((carries_iff N B).1 hB)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
  | zero => simp
  | add x y _ _ hx hy => rw [star_add, add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    obtain ⟨s, hs⟩ := star_range r
    rw [Algebra.smul_def, star_mul', ← hs, mul_assoc, ← Algebra.smul_def]
    exact Submodule.smul_mem _ s hx

omit [StarRing E] in
theorem exists_det_ne_zero {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    ∃ A : Matrix (Fin n) (Fin n) E, (∀ j, A.col j ∈ N) ∧ A.det ≠ 0 := by
  have h : ∀ j : Fin n, ∃ t : nonZeroDivisors (𝓞 E), t • (Pi.single j 1 : Sp E n) ∈ N := by
    intro j
    have := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (N : Set (Sp E n))
      (Pi.single j 1) (by rw [hN.span_eq_top]; trivial)
    rwa [Submodule.span_eq] at this
  choose t ht using h
  refine ⟨Matrix.diagonal fun j => algebraMap (𝓞 E) E (t j), fun j => ?_, ?_⟩
  · convert ht j using 1
    funext i
    by_cases hij : i = j
    · subst hij; simp [Matrix.col, Submonoid.smul_def, Algebra.smul_def]
    · simp [Matrix.col, hij]
  · rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    simp

omit [StarRing E] in
theorem exists_denom (P : HeightOneSpectrum (𝓞 E)) (F : Finset E) (h : ∀ x ∈ F, P.valuation E x ≤ 1) :
    ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∀ x ∈ F, t • x ∈ (1 : Submodule (𝓞 E) E) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by simp⟩
  | insert a F _ ih =>
    obtain ⟨t, ht, H⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    obtain ⟨s, hs, Hs⟩ := (mem_locP' (P := P) 1 a).1
      ((maxV_one.mem_locP one_ne_zero a).2 (h a (Finset.mem_insert_self _ _)))
    refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim ht hs, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [mul_smul]; exact Submodule.smul_mem _ t Hs
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ s (H x hx)

theorem exists_max_det {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ B : Matrix (Fin n) (Fin n) E, (∀ j, B.col j ∈ N) ∧ B.det ≠ 0 ∧
      ∀ C : Matrix (Fin n) (Fin n) E, (∀ j, C.col j ∈ N) → P.valuation E C.det ≤ P.valuation E B.det := by
  obtain ⟨A, hA, hA0⟩ := exists_det_ne_zero hN.1
  have hsA : P.valuation E (star A.det) ≠ 0 := by simpa using hA0
  obtain ⟨z, ⟨B, hB, hB0, rfl⟩, hz⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ B : Matrix (Fin n) (Fin n) E, (∀ j, B.col j ∈ N) ∧ B.det ≠ 0 ∧
      WithZero.log (P.valuation E B.det) = z)
    ⟨- WithZero.log (P.valuation E (star A.det)), by
      rintro z ⟨B, hB, hB0, rfl⟩
      have hvB : P.valuation E B.det ≠ 0 := by simpa using hB0
      have h1 := (maxV_one (P := P)).1 _ (star_det_mul_det_mem hN.2 hA hB)
      rw [map_mul] at h1
      have h2 := (WithZero.log_le_log (mul_ne_zero hsA hvB) one_ne_zero).2 h1
      rw [WithZero.log_mul hsA hvB, WithZero.log_one] at h2
      linarith⟩
    ⟨_, A, hA, hA0, rfl⟩
  refine ⟨B, hB, hB0, fun C hC => ?_⟩
  by_cases hC0 : C.det = 0
  · simp [hC0]
  · exact (WithZero.log_le_log (by simpa using hC0) (by simpa using hB0)).1 (hz _ ⟨C, hC, hC0, rfl⟩)

theorem exists_unit_at {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ a ∈ detLat N, ∃ b ∈ detLat N, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ star a * b = algebraMap (𝓞 E) E t := by
  classical
  obtain ⟨B, hB, hB0, hmax⟩ := exists_max_det hN P
  have hvB : P.valuation E B.det ≠ 0 := by simpa using hB0
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB0
  have h1 : ∀ x ∈ N, ∀ i, P.valuation E ((B⁻¹ *ᵥ x) i) ≤ 1 := by
    intro x hx i
    have hc := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer B x hu) i
    rw [Matrix.cramer_apply, Pi.smul_apply, smul_eq_mul] at hc
    have := hmax (B.updateCol i x) (fun j => by
      by_cases hj : j = i
      · subst hj
        convert hx using 1
        funext k; simp [Matrix.col]
      · convert hB j using 1
        funext k; simp [Matrix.col, Matrix.updateCol_ne hj])
    rw [← hc, map_mul] at this
    exact (mul_le_iff_le_one_right (zero_lt_iff.2 hvB)).1 this
  obtain ⟨S, hS⟩ := hN.1.fg
  obtain ⟨t, ht, H⟩ := exists_denom P ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p => (B⁻¹ *ᵥ p.1) p.2)
    (by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
      exact h1 _ (hS ▸ Submodule.subset_span (Finset.mem_product.1 hp).1) _)
  have h2 : ∀ x ∈ N, ∀ i, t • (B⁻¹ *ᵥ x) i ∈ (1 : Submodule (𝓞 E) E) := by
    intro x hx i
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact H _ (Finset.mem_image.2 ⟨(y, i), Finset.mem_product.2 ⟨hy, Finset.mem_univ _⟩, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, Pi.add_apply, smul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_comm]; exact Submodule.smul_mem _ r hx
  let A : Matrix (Fin n) (Fin n) E := (algebraMap (𝓞 E) E t • B⁻¹)ᴴ
  have hA : ∀ j, A.col j ∈ N := by
    intro j
    have hd : dual (hStd E n) N = N := hN.2
    rw [← hd, mem_dual]
    intro y hy
    convert star_mem_one (h2 y hy j) using 1
    rw [hStd_apply, Algebra.smul_def, Matrix.mulVec, dotProduct, Finset.mul_sum, star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [A, Matrix.col, Matrix.transpose_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul']
    ring
  refine ⟨A.det, det_mem_detLat hA, B.det, det_mem_detLat hB, t ^ n,
    fun h => ht (P.isPrime.mem_of_pow_mem n h), ?_⟩
  rw [← Matrix.det_conjTranspose, Matrix.conjTranspose_conjTranspose, ← Matrix.det_mul, Matrix.smul_mul,
    Matrix.nonsing_inv_mul _ hu, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, map_pow]

theorem detLat_mul_conj (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
    (N : Submodule (𝓞 E) (Sp E n)) (hN : IsSdLat N) :
    ∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ star x ∈ detLat N) ∧ detLat N * J = 1 := by
  let J : Submodule (𝓞 E) E :=
    { carrier := {x | star x ∈ detLat N}
      add_mem' := fun {a b} ha hb => by
        show star (a + b) ∈ detLat N
        rw [star_add]; exact Submodule.add_mem _ ha hb
      zero_mem' := by
        show star (0 : E) ∈ detLat N
        simp
      smul_mem' := fun r x hx => by
        show star (r • x) ∈ detLat N
        obtain ⟨s, hs⟩ := star_range r
        rw [Algebra.smul_def, star_mul', ← hs, ← Algebra.smul_def]
        exact Submodule.smul_mem _ s hx }
  have hJ : ∀ x, x ∈ J ↔ star x ∈ detLat N := fun x => Iff.rfl
  refine ⟨J, hJ, le_antisymm (Submodule.mul_le.2 fun a ha b hb => ?_) ?_⟩
  · have := star_mul_mem hN.2 ((hJ b).1 hb) ha
    rwa [star_star, mul_comm] at this
  · rw [Submodule.one_le]
    by_contra hne
    let I : Ideal (𝓞 E) := (detLat N * J).comap (Algebra.linearMap (𝓞 E) E)
    have hI : I ≠ ⊤ := by
      rw [Ideal.ne_top_iff_one]
      intro h
      apply hne
      simpa [I] using h
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨a, ha, b, hb, t, ht, h⟩ := exists_unit_at hN
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩
    apply ht
    apply hIM
    show algebraMap (𝓞 E) E t ∈ detLat N * J
    rw [← h, mul_comm (star a) b]
    exact Submodule.mul_mem_mul hb ((hJ _).2 (by rwa [star_star]))

end GlobalTheory.DetSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumRpowZerosLe
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.ZeroSum

theorem mem_disc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} {ρ : ℂ}
    (h : ρ ∈ zerosBox χ (1 / 2) T) :
    ⌊ρ.im⌋ ∈ Finset.Icc (-⌈T⌉) ⌈T⌉ ∧ ρ ∈ zerosDisc χ (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I) 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [abs_le] at h3
  have a1 := Int.floor_le ρ.im
  have a2 := Int.lt_floor_add_one ρ.im
  have a3 := Int.le_ceil T
  refine ⟨?_, ?_, Or.inr ?_, h4⟩
  · rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]; push_cast; linarith
    · have : ((⌊ρ.im⌋ : ℤ) : ℝ) ≤ (⌈T⌉ : ℤ) := by linarith
      exact_mod_cast this
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have b1 : |(ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).re| ≤ 2 := by
      rw [abs_le]; simp; constructor <;> linarith
    have b2 : |(ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).im| ≤ 1 := by
      have : (ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).im = ρ.im - ⌊ρ.im⌋ := by simp
      rw [this, abs_le]; constructor <;> linarith
    linarith
  · rintro rfl
    simp at h2

theorem total_count : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ),
    2 ≤ T → ∃ h : (zerosBox χ (1 / 2) T).Finite,
      ∑ ρ ∈ h.toFinset, (ord χ ρ : ℝ) ≤ C * (q * T ^ 2) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.T.iteratedDeriv_logDeriv_dirichletL_via_nearby_zeros
  refine ⟨12 * C, by positivity, fun q _ χ T hT => ?_⟩
  have hf : ∀ n : ℤ, (zerosDisc χ (2 + ((n : ℝ) : ℂ) * I) 3).Finite :=
    fun n => (H q χ 2 n 0 (by norm_num) le_rfl).1
  have hfin : (zerosBox χ (1 / 2) T).Finite := by
    refine ((Finset.Icc (-⌈T⌉) ⌈T⌉).finite_toSet.biUnion (fun n _ => hf n)).subset ?_
    intro ρ hρ
    simp only [Set.mem_iUnion]
    exact ⟨_, (mem_disc χ hρ).1, (mem_disc χ hρ).2⟩
  refine ⟨hfin, ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have a3 := Int.ceil_lt_add_one T
  have a4 := Int.le_ceil T
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc (-⌈T⌉) ⌈T⌉) (g := fun ρ : ℂ => ⌊ρ.im⌋)
    (fun ρ hρ => (mem_disc χ (hfin.mem_toFinset.1 hρ)).1)]
  have key : ∀ n ∈ Finset.Icc (-⌈T⌉) ⌈T⌉,
      ∑ ρ ∈ hfin.toFinset with ⌊ρ.im⌋ = n, (ord χ ρ : ℝ) ≤ C * (q * (3 * T)) := by
    intro n hn
    have h2 := (H q χ 2 n 0 (by norm_num) le_rfl).2.1
    rw [finsum_mem_eq_finite_toFinset_sum _ (hf n)] at h2
    have hn' : |(n : ℝ)| ≤ T + 1 := by
      rw [Finset.mem_Icc] at hn
      have c1 : ((-⌈T⌉ : ℤ) : ℝ) ≤ n := by exact_mod_cast hn.1
      have c2 : (n : ℝ) ≤ (⌈T⌉ : ℤ) := by exact_mod_cast hn.2
      push_cast at c1
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ ∑ ρ ∈ (hf n).toFinset, (ord χ ρ : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
          intro ρ hρ
          rw [Finset.mem_filter] at hρ
          rw [Set.Finite.mem_toFinset, ← hρ.2]
          exact (mem_disc χ (hfin.mem_toFinset.1 hρ.1)).2
      _ ≤ _ := h2
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hC.le
          refine (Real.log_le_self (by positivity)).trans ?_
          refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine (Finset.sum_le_card_nsmul _ _ _ key).trans ?_
  rw [nsmul_eq_mul]
  have hc : ((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℝ) ≤ 4 * T := by
    have h0 : (0 : ℤ) ≤ ⌈T⌉ + 1 - -⌈T⌉ := by
      have : (0 : ℤ) ≤ ⌈T⌉ := Int.ceil_nonneg (by linarith)
      omega
    have : (((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℤ) : ℝ) = ((⌈T⌉ + 1 - -⌈T⌉ : ℤ) : ℝ) := by
      rw [Int.card_Icc, Int.toNat_of_nonneg h0]
    push_cast at this
    rw [this]; linarith
  calc _ ≤ (4 * T) * (C * (q * (3 * T))) := by gcongr
    _ = _ := by ring

theorem layers {ι : Type*} (s : Finset ι) (w δ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {L η e : ℝ}
    (hL : 0 < L) (J : ℕ) (hJ : L * e < J) (hη : 0 ≤ η) :
    ∑ i ∈ s with η ≤ δ i, w i * Real.exp (-(L * δ i)) ≤
      ∑ j ∈ Finset.range J, Real.exp (-(L * η) - j) *
        (∑ i ∈ s with δ i ≤ min (η + (j + 1) / L) e, w i) + Real.exp (-(L * e)) * ∑ i ∈ s, w i := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hwi := hw i
  have hnn : ∀ j ∈ Finset.range J, 0 ≤ Real.exp (-(L * η) - j) *
      (if δ i ≤ min (η + (j + 1) / L) e then w i else 0) := by
    intro j _
    split_ifs <;> positivity
  have hs := Finset.sum_nonneg hnn
  have he : 0 ≤ Real.exp (-(L * e)) * w i := by positivity
  split_ifs with h
  · by_cases h2 : δ i ≤ e
    · have h0 : 0 ≤ L * (δ i - η) := mul_nonneg hL.le (by linarith)
      have a1 := Nat.floor_le h0
      have a2 := Nat.lt_floor_add_one (L * (δ i - η))
      have hm : ⌊L * (δ i - η)⌋₊ ∈ Finset.range J := by
        rw [Finset.mem_range, Nat.floor_lt h0]
        nlinarith
      have := Finset.single_le_sum hnn hm
      rw [if_pos] at this
      · have h3 : Real.exp (-(L * δ i)) ≤ Real.exp (-(L * η) - ⌊L * (δ i - η)⌋₊) :=
          Real.exp_le_exp.2 (by linarith)
        nlinarith
      · refine le_min ?_ h2
        have : δ i - η ≤ (⌊L * (δ i - η)⌋₊ + 1) / L := by
          rw [le_div_iff₀ hL]; linarith
        linarith
    · have h3 : Real.exp (-(L * δ i)) ≤ Real.exp (-(L * e)) :=
        Real.exp_le_exp.2 (by nlinarith)
      nlinarith
  · linarith

theorem sum_rpow_zeros_le : ∃ A C η₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < η₀ ∧ ∀ (q : ℕ) [NeZero q] (T u η : ℝ), 2 ≤ T → ((q : ℝ) * T) ^ A ≤ u → 0 ≤ η → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤ C * (u ^ (-η / 2) + u ^ (-η₀)) := by
  obtain ⟨A₁, C₁, η₁, hA₁, hC₁, hη₁, H₁⟩ := GlobalTheory.T.logFree_zeroDensity_dirichlet_one_modulus
  obtain ⟨C₂, hC₂, H₂⟩ := total_count
  obtain ⟨e, he0, he1, he2⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ η₁ ∧ e ≤ 1 / 2 :=
    ⟨min η₁ (1 / 2), by positivity, min_le_left _ _, min_le_right _ _⟩
  have hr : Real.exp (-1 / 2) < 1 := by
    simpa using Real.exp_lt_exp.2 (show (-1 / 2 : ℝ) < 0 by norm_num)
  have hsum := summable_geometric_of_lt_one (Real.exp_pos (-1 / 2)).le hr
  set K := ∑' j : ℕ, Real.exp (-1 / 2) ^ j with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => by positivity
  refine ⟨2 * A₁ + 4 / e, C₁ * Real.exp (1 / 2) * K + C₂, e / 2, by positivity, by positivity,
    by positivity, fun q _ T u η hT hu hη => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hqT : (1 : ℝ) < q * T := by nlinarith
  have hu1 : 1 < u := (Real.one_lt_rpow hqT (by positivity)).trans_le hu
  have hu0 : 0 < u := by linarith
  have hL : 0 < Real.log u := Real.log_pos hu1
  have hM : 0 < Real.log (q * T) := Real.log_pos hqT
  have hLM : (2 * A₁ + 4 / e) * Real.log (q * T) ≤ Real.log u := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by positivity) hu
  set L := Real.log u with hLdef
  set M := Real.log (q * T) with hMdef
  have h4 : 0 < 4 / e := by positivity
  have hLM1 : 2 * A₁ * M ≤ L := by nlinarith
  have hLM2 : 4 * M ≤ e * L := by
    have : 4 / e * M ≤ L := by nlinarith [mul_pos hA₁ hM]
    rw [div_mul_eq_mul_div, div_le_iff₀ he0] at this
    linarith
  choose hfin hcount using fun χ : DirichletCharacter ℂ q => H₂ q χ T hT
  obtain ⟨J, hJ⟩ := exists_nat_gt (L * e)
  have step1 : ∀ χ : DirichletCharacter ℂ q,
      (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤
      ∑ j ∈ Finset.range J, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) +
        Real.exp (-(L * e)) * (C₂ * (q * T ^ 2)) := by
    intro χ
    have h := layers (hfin χ).toFinset (fun ρ => (ord χ ρ : ℝ)) (fun ρ => 1 - ρ.re)
      (fun _ => Nat.cast_nonneg _) hL J hJ hη
    have e1 : zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η} =
        ((hfin χ).toFinset.filter (fun ρ : ℂ => η ≤ 1 - ρ.re) : Finset ℂ) := by
      ext ρ
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
      exact and_congr_right fun _ => ⟨fun _ => by linarith, fun _ => by linarith⟩
    have e2 : ∀ x : ℝ, x ≤ e → zerosBox χ (1 - x) T =
        ((hfin χ).toFinset.filter (fun ρ : ℂ => 1 - ρ.re ≤ x) : Finset ℂ) := by
      intro x hx
      ext ρ
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset, zerosBox]
      constructor
      · rintro ⟨a, b, c, d⟩
        exact ⟨⟨by linarith, b, c, d⟩, by linarith⟩
      · rintro ⟨⟨a, b, c, d⟩, f⟩
        exact ⟨by linarith, b, c, d⟩
    rw [e1, finsum_mem_coe_finset]
    calc _ = _ := by
          refine Finset.sum_congr rfl fun ρ _ => ?_
          rw [Real.rpow_def_of_pos hu0, show Real.log u * (ρ.re - 1) = -(L * (1 - ρ.re)) by ring]
      _ ≤ _ := h
      _ ≤ _ := by
          refine add_le_add (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
            (mul_le_mul_of_nonneg_left (hcount χ) (Real.exp_pos _).le)
          rw [e2 _ (min_le_right _ _), finsum_mem_coe_finset]
  refine (Finset.sum_le_sum fun χ _ => step1 χ).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hA : ∑ j ∈ Finset.range J, ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) ≤
        C₁ * Real.exp (1 / 2) * K * u ^ (-η / 2) := by
    have : ∀ j ∈ Finset.range J, ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) ≤
        C₁ * Real.exp (1 / 2) * u ^ (-η / 2) * Real.exp (-1 / 2) ^ j := by
      intro j _
      rw [← Finset.mul_sum]
      have hx0 : 0 ≤ min (η + (j + 1) / L) e := by positivity
      have hx1 := min_le_left (η + (j + 1) / L) e
      have hx2 := min_le_right (η + (j + 1) / L) e
      generalize min (η + (j + 1) / L) e = x at hx0 hx1 hx2 ⊢
      have h := H₁ q T (1 - x) hT (by linarith) (by linarith)
      refine (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans ?_
      rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos (by linarith), ← Real.exp_nat_mul,
        mul_left_comm, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁.le
      rw [← hLdef, ← hMdef]
      have hx3 : L * x ≤ L * η + (j + 1) := by
        have := mul_le_mul_of_nonneg_left hx1 hL.le
        rwa [mul_add, mul_div_cancel₀ _ hL.ne'] at this
      nlinarith [mul_le_mul_of_nonneg_right hLM1 hx0]
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.mul_sum]
    have := hsum.sum_le_tsum (Finset.range J) (fun _ _ => by positivity)
    calc _ ≤ C₁ * Real.exp (1 / 2) * u ^ (-η / 2) * K := by gcongr
      _ = _ := by ring
  have hB : ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * e)) * (C₂ * (q * T ^ 2)) ≤
      C₂ * u ^ (-(e / 2)) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    have ht : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hE : Real.exp (2 * M) = (q * T) ^ 2 := by
      rw [show 2 * M = M + M by ring, Real.exp_add, hMdef, Real.exp_log (by linarith), sq]
    calc _ ≤ (q : ℝ) * (Real.exp (-(L * e)) * (C₂ * (q * T ^ 2))) := by gcongr
      _ = C₂ * (Real.exp (-(L * e)) * Real.exp (2 * M)) := by rw [hE]; ring
      _ ≤ _ := by
        rw [← Real.exp_add, Real.rpow_def_of_pos hu0, ← hLdef]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₂.le
        linarith
  have p1 : 0 ≤ u ^ (-η / 2) := by positivity
  have p2 : 0 ≤ u ^ (-(e / 2)) := by positivity
  have p3 : 0 ≤ C₁ * Real.exp (1 / 2) * K := by positivity
  nlinarith [mul_nonneg p3 p2, mul_nonneg hC₂.le p1]

end GlobalTheory.Lin.ZeroSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowPpDimToLeRpow
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_pp_dim_to_le_rpow :
    SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.x ^ L.Ct) ∧
      (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct) ∧ (((TOv L.sc : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct)) := by
  intro eps h0 h1 C hC
  obtain ⟨xr, hxr⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max xr (max C.T.CP 2), fun D L he hx hV => ?_⟩⟩⟩
  have hx1 : xr ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx2 : C.T.CP ≤ L.sc.x := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx
  have hx3 : (2 : ℝ) ≤ L.sc.x := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx
  have hone : (1 : ℝ) ≤ L.sc.x := by linarith
  have hpos : (0 : ℝ) < L.sc.x := by linarith
  obtain ⟨-, -, -, -, -, -, -, hZ0, hZ, hD, -⟩ := hxr L.sc D.R he hx1 hV.ranks
  have hCt : L.Ct = 401 := hV.Ct_eq.trans hC.1.2.2.2.2.2.2.2.2.2
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  beta_reduce
  rw [hCt, heP]
  refine ⟨?_, hD.trans (Real.rpow_le_rpow_of_exponent_le hone (by norm_num)), ?_⟩
  · have hz0 : 0 ≤ zBase L := le_trans (Real.rpow_nonneg hpos.le _) hZ0
    have hz : zBase L ^ (12 : ℝ) ≤ L.sc.x ^ ((687 : ℝ) / 100 * 12) := by
      rw [Real.rpow_mul hpos.le]
      exact Real.rpow_le_rpow hz0 hZ (by norm_num)
    calc C.T.CP * zBase L ^ (12 : ℝ) ≤ L.sc.x * L.sc.x ^ ((687 : ℝ) / 100 * 12) :=
          mul_le_mul hx2 hz (Real.rpow_nonneg hz0 _) hpos.le
      _ = L.sc.x ^ (1 + (687 : ℝ) / 100 * 12) := by rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ L.sc.x ^ (401 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
  · have h377 : (1 : ℝ) ≤ L.sc.x ^ (377 : ℝ) := Real.one_le_rpow hone (by norm_num)
    have hc : ((TOv L.sc : ℕ) : ℝ) < L.sc.x ^ (377 : ℝ) + 1 := Nat.ceil_lt_add_one (by linarith)
    calc ((TOv L.sc : ℕ) : ℝ) ≤ L.sc.x * L.sc.x ^ (377 : ℝ) := by nlinarith
      _ = L.sc.x ^ (1 + 377 : ℝ) := by rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ L.sc.x ^ (401 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by norm_num)

end GlobalTheory.EX
end

