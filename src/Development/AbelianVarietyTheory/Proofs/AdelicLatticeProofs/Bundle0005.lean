import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneInfinite
section
namespace GlobalTheory.NormOneInfinite

theorem normOne_infinite {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
    (c : Gal(E/F)) (hc : ∀ x : E, (c : E → E) ((c : E → E) x) = x) (h1 : c ≠ (1 : Gal(E/F))) :
    Set.Infinite {l : E | l * (c : E → E) l = (1 : E)} := by
  have hx : ∃ x : E, c x ≠ x := by
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    exact h1 (AlgEquiv.ext fun x => by rw [hall x, AlgEquiv.one_apply])
  obtain ⟨x, hx⟩ := hx
  have hcd : c (x - c x) = -(x - c x) := by
    rw [map_sub, hc x]
    ring
  have hd : x - c x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcn : ∀ n : ℕ, c (n : E) = n := fun n => map_natCast c n
  have h2d : ∀ y : E, y = -y → y = 0 := by
    intro y hy
    have h2 : (2 : E) * y = 0 := by linear_combination hy
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hsub : ∀ n : ℕ, (n : E) - (x - c x) ≠ 0 := by
    intro n h0
    have e : x - c x = n := (sub_eq_zero.mp h0).symm
    apply hd
    apply h2d
    calc x - c x = c (x - c x) := by rw [e, hcn]
      _ = -(x - c x) := hcd
  have hadd : ∀ n : ℕ, (n : E) + (x - c x) ≠ 0 := by
    intro n h0
    have e : x - c x = -(n : E) := by linear_combination h0
    apply hd
    apply h2d
    calc x - c x = c (x - c x) := by rw [e, map_neg, hcn]
      _ = -(x - c x) := hcd
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + (x - c x)) / ((n : E) - (x - c x))) ?_ ?_
  · intro n m hnm
    simp only at hnm
    rw [div_eq_div_iff (hsub n) (hsub m)] at hnm
    have h3 : (2 : E) * (x - c x) * ((m : E) - n) = 0 := by linear_combination hnm
    rcases mul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' two_ne_zero
      · exact absurd h' hd
    · exact (Nat.cast_injective (sub_eq_zero.mp h)).symm
  · intro n
    change ((n : E) + (x - c x)) / ((n : E) - (x - c x)) *
      c (((n : E) + (x - c x)) / ((n : E) - (x - c x))) = 1
    rw [map_div₀, map_add, map_sub c (n : E) (x - c x), hcn, hcd]
    have h4 : (n : E) + -(x - c x) = (n : E) - (x - c x) := by ring
    have h5 : (n : E) - -(x - c x) = (n : E) + (x - c x) := by ring
    rw [h4, h5, div_mul_div_comm, mul_comm ((n : E) - (x - c x))]
    exact div_self (mul_ne_zero (hadd n) (hsub n))

end GlobalTheory.NormOneInfinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneSubRePosOfNormLeHalf
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem eulerTerm_norm_le_rpow (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
  have hn0 : 0 < n := by omega
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
  have : (0 : ℝ) ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc ‖c‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) := by gcongr
    _ = (n : ℝ) ^ (-s.re) := one_mul _

theorem eulerTerm_norm_le_half (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 1 < s.re) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  refine (eulerTerm_norm_le_rpow n hn c s hc).trans ?_
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

theorem one_sub_re_pos_of_norm_le_half (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) : 0 < (1 - z).re := by
  rw [Complex.sub_re, Complex.one_re]
  have := Complex.re_le_norm z
  linarith

theorem eulerProduct_eq_exp_and_pos :
    ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → (∀ s : ℂ, 1 < s.re → Summable (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) ∧ HasProd (fun i => (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))))) ∧ ∀ e : ι ≃ ι, (∀ i, N (e i) = N i) → (∀ i, c (e i) = starRingEnd ℂ (c i)) → ∀ s : ℂ, 1 < s.re → s.im = 0 → (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))).im = 0 ∧ 0 < (Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))).re := by
  intro ι N c hN hc hsum
  have hsmall : ∀ s : ℂ, 1 < s.re → ∀ i, ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
    fun s hs i => eulerTerm_norm_le_half (N i) (hN i) (c i) s (hc i) hs
  have hne : ∀ s : ℂ, 1 < s.re → ∀ i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
    intro s hs i h
    have := one_sub_re_pos_of_norm_le_half _ (hsmall s hs i)
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hsummable : ∀ s : ℂ, 1 < s.re →
      Summable (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) := by
    intro s hs
    refine Summable.of_norm_bounded ((hsum s.re hs).mul_left (3 / 2)) (fun i => ?_)
    rw [norm_neg, sub_eq_add_neg]
    refine (Complex.norm_log_one_add_half_le_self (by rw [norm_neg]; exact hsmall s hs i)).trans ?_
    rw [norm_neg]
    gcongr
    exact eulerTerm_norm_le_rpow (N i) (hN i) (c i) s (hc i)
  refine ⟨fun s hs => ⟨hsummable s hs, ?_⟩, ?_⟩
  · convert (hsummable s hs).hasSum.cexp using 1
    funext i
    simp only [Function.comp, Complex.exp_neg, Complex.exp_log (hne s hs i)]
  · intro e hNe hce s hs him
    have hsre : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hreal : ∀ i, starRingEnd ℂ (((N i : ℕ) : ℂ) ^ (-s)) = ((N i : ℕ) : ℂ) ^ (-s) := by
      intro i
      rw [hsre, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.conj_ofReal]
    have hterm : ∀ i, starRingEnd ℂ (-Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) =
        -Complex.log (1 - c (e i) * ((N (e i) : ℕ) : ℂ) ^ (-s)) := by
      intro i
      have harg : (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)).arg ≠ Real.pi := by
        rw [Ne, Complex.arg_eq_pi_iff]
        have := one_sub_re_pos_of_norm_le_half _ (hsmall s hs i)
        intro h
        linarith [h.1]
      rw [map_neg, ← Complex.log_conj _ harg, map_sub, map_one, map_mul, hreal, hce, hNe]
    set S := ∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)) with hS
    have hconj : starRingEnd ℂ S = S := by
      rw [hS, Complex.conj_tsum]
      simp_rw [hterm]
      exact Equiv.tsum_eq e (fun i => -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))
    have hSim : S.im = 0 := Complex.conj_eq_iff_im.mp hconj
    rw [Complex.exp_im, Complex.exp_re, hSim, Real.sin_zero, Real.cos_zero, mul_zero, mul_one]
    exact ⟨rfl, Real.exp_pos _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ProdLeftEqMaps
section
namespace GlobalTheory.ProductLeftMaps

open TensorProduct

theorem prodLeft_eq_maps {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : TensorProduct F (A × B) E) :
    TensorProduct.prodLeft F F A B E z =
      ((Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F A E) z,
       (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F B E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul x e =>
    obtain ⟨a, b⟩ := x
    simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add, map_add]
    rfl

theorem main : ∀ {F A B E : Type} [inst : Field F] [inst_1 : CommRing A] [inst_2 : CommRing B]
    [inst_3 : CommRing E] [inst_4 : Algebra F A] [inst_5 : Algebra F B] [inst_6 : Algebra F E]
    (z : TensorProduct F (A × B) E),
    (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F A E) z = (0 : TensorProduct F A E) →
    (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F B E) z = (0 : TensorProduct F B E) →
    z = (0 : TensorProduct F (A × B) E) := by
  intro F A B E _ _ _ _ _ _ _ z h1 h2
  apply (TensorProduct.prodLeft F F A B E).injective
  rw [prodLeft_eq_maps, h1, h2, map_zero]
  rfl

end GlobalTheory.ProductLeftMaps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RayCharacterExtendsToIdeals
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open UniqueFactorizationMonoid in

theorem exists_multiplicative_ideal_extension :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (c : HeightOneSpectrum (𝓞 K) → ℂ), (∀ P, ¬ m ≤ P.asIdeal → ‖c P‖ = 1) → ∃ X : Ideal (𝓞 K) → ℂ, X ⊥ = 0 ∧ X ⊤ = 1 ∧ (∀ I J, X (I * J) = X I * X J) ∧ (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) ∧ (∀ I, I ⊔ m ≠ ⊤ → X I = 0) ∧ ∀ P, ¬ m ≤ P.asIdeal → X P.asIdeal = c P := by
  intro K _ _ m c hc
  let d : Ideal (𝓞 K) → ℂ := fun Q =>
    if h : Q.IsPrime ∧ Q ≠ ⊥ then (if m ≤ Q then 0 else c ⟨Q, h.1, h.2⟩) else 0
  have hd : ∀ P : HeightOneSpectrum (𝓞 K), ¬ m ≤ P.asIdeal → d P.asIdeal = c P := by
    intro P hP
    simp only [d]
    rw [dif_pos ⟨P.isPrime, P.ne_bot⟩, if_neg hP]
  have hd0 : ∀ Q, m ≤ Q → d Q = 0 := by
    intro Q hQ
    simp only [d]
    split_ifs <;> rfl
  refine ⟨fun I => if I = ⊥ then 0 else ((normalizedFactors I).map d).prod, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · have : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
    simp only [if_neg this]
    rw [← Ideal.one_eq_top, normalizedFactors_one]
    simp
  · intro I J
    by_cases hI : I = ⊥
    · simp [hI]
    by_cases hJ : J = ⊥
    · simp [hJ]
    have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
    simp only [if_neg hI, if_neg hJ, if_neg hIJ]
    rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]
  · intro I hI hm
    simp only [if_neg hI]
    refine Multiset.prod_induction (fun z : ℂ => ‖z‖ = 1) _ ?_ (by simp) ?_
    · intro a b ha hb
      simp [ha, hb]
    · intro a ha
      obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.1 ha
      have hp : Prime Q := prime_of_normalized_factor Q hQ
      have hle : I ≤ Q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hQ)
      have hQp : Q.IsPrime := Ideal.isPrime_of_prime hp
      have hm' : ¬ m ≤ Q := fun h => hQp.ne_top (top_le_iff.1 (hm ▸ sup_le hle h))
      have := hd ⟨Q, hQp, hp.ne_zero⟩ hm'
      simp only at this
      rw [this]
      exact hc _ hm'
  · intro I hm
    by_cases hI : I = ⊥
    · simp [hI]
    simp only [if_neg hI]
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hm
    apply Multiset.prod_eq_zero
    refine Multiset.mem_map.2 ⟨Q, ?_, hd0 Q (le_sup_right.trans hle)⟩
    exact (Ideal.mem_normalizedFactors_iff hI).2 ⟨hQ.isPrime, le_sup_left.trans hle⟩
  · intro P hP
    simp only [if_neg P.ne_bot]
    rw [normalizedFactors_irreducible P.irreducible, normalize_eq]
    simp [hd P hP]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RayInvariantContinuousEqOne
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem exists_near_one_mod_ideal (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (hm : m ≠ ⊥) : ∃ C : ℝ, ∀ z : mixedSpace K, ∃ β : 𝓞 K, β - 1 ∈ m ∧
      ‖z - mixedEmbedding K β‖ ≤ C := by
  set N : ℕ := Ideal.absNorm m with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; exact fun h => hm (Ideal.absNorm_eq_zero_iff.mp h)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
  refine ⟨(N : ℝ) * ∑ i, ‖latticeBasis K i‖, fun z => ?_⟩
  set w : mixedSpace K := (N : ℝ)⁻¹ • (z - 1) with hw
  have hmem := (ZSpan.floor (latticeBasis K) w).2
  obtain ⟨a, ha⟩ := (mem_span_latticeBasis K).mp hmem
  refine ⟨1 + (N : 𝓞 K) * a, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact m.mul_mem_right _ (Ideal.absNorm_mem m)
  · have ha' : mixedEmbedding K (a : K) = (ZSpan.floor (latticeBasis K) w : mixedSpace K) := ha
    have h1 : z - mixedEmbedding K ((1 + (N : 𝓞 K) * a : 𝓞 K) : K)
        = (N : ℝ) • ZSpan.fract (latticeBasis K) w := by
      rw [ZSpan.fract_apply, ← ha', smul_sub, hw, smul_inv_smul₀ hNR]
      simp only [map_add, map_one, map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      ring
    rw [h1, _root_.norm_smul, Real.norm_natCast]
    exact mul_le_mul_of_nonneg_left (ZSpan.norm_fract_le _ _) (Nat.cast_nonneg _)

theorem eq_one_of_homogeneous_of_eq_one_on_class :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (φ : mixedSpace K → ℂ), m ≠ ⊥ → ContinuousOn φ {x | mixedEmbedding.norm x ≠ 0} → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → φ (mixedEmbedding K β) = 1) → ∀ x, mixedEmbedding.norm x ≠ 0 → φ x = 1 := by
  intro K _ _ m φ hm hc hh h1 x hx
  obtain ⟨C, hC⟩ := exists_near_one_mod_ideal K m hm
  choose β hβm hβ using hC
  set y : ℕ → mixedSpace K := fun n =>
    ((n : ℝ) + 1)⁻¹ • mixedEmbedding K (β (((n : ℝ) + 1) • x)) with hy
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hlim : Filter.Tendsto y Filter.atTop (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * C) Filter.atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have : x - y n = ((n : ℝ) + 1)⁻¹ •
        (((n : ℝ) + 1) • x - mixedEmbedding K (β (((n : ℝ) + 1) • x))) := by
      rw [smul_sub, inv_smul_smul₀ (hpos n).ne']
    rw [norm_sub_rev, this, _root_.norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hpos n)).le, one_div]
    exact mul_le_mul_of_nonneg_left (hβ _) (inv_pos.mpr (hpos n)).le
  have hopen : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
  have hca : ContinuousAt φ x := hc.continuousAt (hopen.mem_nhds hx)
  have hev : ∀ᶠ n in Filter.atTop, φ (y n) = 1 := by
    filter_upwards [hlim.eventually (hopen.mem_nhds hx)] with n hn
    have hne : β (((n : ℝ) + 1) • x) ≠ 0 := by
      intro h0
      apply hn
      simp [hy, h0]
    simp only [hy]
    rw [hh _ _ (inv_pos.mpr (hpos n))]
    exact h1 _ hne (hβm _)
  have h2 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds (φ x)) := hca.tendsto.comp hlim
  have h3 : Filter.Tendsto (fun n => φ (y n)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  exact tendsto_nhds_unique h2 h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SummableGaussianCoset
section
open scoped ContDiff

namespace GlobalTheory.GaussCoset

theorem exp_le_inv_pow {c : ℝ} (hc : 0 < c) (R : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-c * t ^ 2 + R * t) ≤
      ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by
  have hsq : 0 ≤ (2 * c * t - (R + 1)) ^ 2 / (4 * c) := by positivity
  have hid : (2 * c * t - (R + 1)) ^ 2 / (4 * c) =
      (R + 1) ^ 2 / (4 * c) - t - (-c * t ^ 2 + R * t) := by
    field_simp
    ring
  have h1 : Real.exp (-c * t ^ 2 + R * t) ≤
      Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-t) ≤ (n.factorial : ℝ) * t⁻¹ ^ n := by
    have hpos : 0 < t ^ n / (n.factorial : ℝ) := by positivity
    have hle : t ^ n / (n.factorial : ℝ) ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le n
    rw [Real.exp_neg, inv_pow, ← div_eq_mul_inv, ← inv_div]
    exact inv_anti₀ hpos hle
  calc Real.exp (-c * t ^ 2 + R * t)
      ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t) := h1
    _ ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * ((n.factorial : ℝ) * t⁻¹ ^ n) := by gcongr
    _ = ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by ring

theorem summable_lattice {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] {c : ℝ} (hc : 0 < c)
    (R : ℝ) (x : V) :
    Summable fun z : L => Real.exp (-c * ‖(z : V) - x‖ ^ 2 + R * ‖(z : V) - x‖) := by
  have hmaj := (ZLattice.summable_norm_sub_inv_pow L (Module.finrank ℤ L + 1)
    (Nat.lt_succ_self _) x).mul_left
      (((Module.finrank ℤ L + 1).factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c)))
  refine Summable.of_norm_bounded_eventually hmaj ?_
  have hfin : {z : L | (z : V) = x}.Finite := by
    apply Set.Subsingleton.finite
    intro a ha b hb
    exact Subtype.ext (ha.trans hb.symm)
  filter_upwards [hfin.compl_mem_cofinite] with z hz
  have hne : (z : V) ≠ x := hz
  have hpos : 0 < ‖(z : V) - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_le_inv_pow hc R (Module.finrank ℤ L + 1) hpos

theorem discrete_of_finite {V : Type} [NormedAddCommGroup V] (L : AddSubgroup V)
    (h : {v : V | v ∈ L ∧ ‖v‖ ≤ 1}.Finite) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hU : IsOpen (Metric.ball (0 : V) 1 ∩ ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ) :=
    Metric.isOpen_ball.inter (h.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hset : ({0} : Set L) = Subtype.val ⁻¹' (Metric.ball (0 : V) 1 ∩
      ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ) := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simp
    · rintro ⟨h1, h2⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      have h1' : ‖(z : V)‖ < 1 := by simpa using h1
      apply h2
      refine ⟨⟨z.2, h1'.le⟩, ?_⟩
      intro hz0
      apply hne
      simpa using hz0
  rw [hset]
  exact hU.preimage continuous_subtype_val

theorem summable_gaussian_coset : ∀ (G V : Type) [AddCommGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (Γ U : AddSubgroup G), (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U ∧ ‖p g‖ ≤ R}.Finite) → ∀ (c : ℝ), 0 < c → ∀ (R : ℝ) (w : G) (y : V), Summable fun g : Γ => Set.indicator (U : Set G) (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w) := by
  intro G V _ _ _ _ p Γ U hinj hfin c hc R w y
  by_cases hS : ∃ g₀ : Γ, (g₀ : G) + w ∈ U
  swap
  · simp only [not_exists] at hS
    have hzero : (fun g : Γ => Set.indicator (U : Set G)
        (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w)) = 0 := by
      funext g
      exact Set.indicator_of_notMem (hS g) _
    rw [hzero]
    exact summable_zero
  obtain ⟨g₀, hg₀⟩ := hS
  obtain ⟨L, hL⟩ : ∃ L : Submodule ℤ V, ∀ v, v ∈ L ↔ v ∈ (Γ ⊓ U).map p :=
    ⟨((Γ ⊓ U).map p).toIntSubmodule, fun _ => Iff.rfl⟩
  have hfin1 : {v : V | v ∈ L.toAddSubgroup ∧ ‖v‖ ≤ 1}.Finite := by
    refine ((hfin 1).image p).subset ?_
    rintro v ⟨hv, hv1⟩
    rw [Submodule.mem_toAddSubgroup, hL] at hv
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.mp hv
    obtain ⟨hgΓ, hgU⟩ := AddSubgroup.mem_inf.mp hg
    exact ⟨g, ⟨hgΓ, hgU, hv1⟩, rfl⟩
  have : DiscreteTopology L := discrete_of_finite L.toAddSubgroup hfin1
  let S := {g : Γ // (g : G) + w ∈ U}
  have hmem : ∀ s : S, p ((s.1 : G) - g₀) ∈ L := by
    intro s
    rw [hL]
    refine AddSubgroup.mem_map_of_mem p (AddSubgroup.mem_inf.mpr ⟨Γ.sub_mem s.1.2 g₀.2, ?_⟩)
    have hd := U.sub_mem s.2 hg₀
    rwa [add_sub_add_right_eq_sub] at hd
  let φ : S → L := fun s => ⟨p ((s.1 : G) - g₀), hmem s⟩
  have hφ : Function.Injective φ := by
    intro s t hst
    have h1 : p ((s.1 : G) - g₀) = p ((t.1 : G) - g₀) := congrArg Subtype.val hst
    have h2 : p ((s.1 : G) - t.1) = p ((s.1 : G) - g₀) - p ((t.1 : G) - g₀) := by
      rw [← map_sub]
      congr 1
      abel
    rw [h1, sub_self] at h2
    have h3 := hinj _ (Γ.sub_mem s.1.2 t.1.2) h2
    exact Subtype.ext (Subtype.ext (sub_eq_zero.mp h3))
  let F : Γ → ℝ := fun g => Set.indicator (U : Set G)
    (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w)
  show Summable F
  have hL' : Summable fun z : L =>
      Real.exp (-c * ‖(z : V) - -(p g₀ + y)‖ ^ 2 + R * ‖(z : V) - -(p g₀ + y)‖) :=
    summable_lattice L hc R _
  have hcomp : Summable (F ∘ (Subtype.val : S → Γ)) := by
    have heq : F ∘ (Subtype.val : S → Γ) = (fun z : L =>
        Real.exp (-c * ‖(z : V) - -(p g₀ + y)‖ ^ 2 + R * ‖(z : V) - -(p g₀ + y)‖)) ∘ φ := by
      funext s
      have hshift : ((φ s : L) : V) - -(p g₀ + y) = p (s.1 : G) + y := by
        show p ((s.1 : G) - g₀) - -(p g₀ + y) = p (s.1 : G) + y
        rw [map_sub]
        abel
      simp only [Function.comp_apply, F]
      rw [Set.indicator_of_mem (show (s.1 : G) + w ∈ (U : Set G) from s.2), hshift]
    rw [heq]
    exact hL'.comp_injective hφ
  refine (Function.Injective.summable_iff Subtype.val_injective ?_).mp hcomp
  intro g hg
  have hnot : (g : G) + w ∉ (U : Set G) := fun h => hg ⟨⟨g, h⟩, rfl⟩
  exact Set.indicator_of_notMem hnot _

end GlobalTheory.GaussCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealEqSumClassGroup
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in

theorem _root_.GlobalTheory.existsUnique_isPrincipal_mul_classRep {K : Type} [Field K] [NumberField K]
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c))) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃! c, (I * (b c : Ideal (𝓞 K))).IsPrincipal := by
  have hI0 : I ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  have key : ∀ c, (I * (b c : Ideal (𝓞 K))).IsPrincipal ↔
      ClassGroup.mk0 (b c) = (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹ := by
    intro c
    rw [eq_inv_iff_mul_eq_one, mul_comm, ← map_mul]
    rw [ClassGroup.mk0_eq_one_iff]
    rfl
  obtain ⟨c, hc⟩ := hb.2 (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹
  refine ⟨c, (key c).2 hc, fun c' hc' => hb.1 ?_⟩
  simp only
  rw [(key c').1 hc']
  exact hc.symm

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in

theorem _root_.GlobalTheory.tsum_isPrincipal_mul_eq {K : Type} [Field K] [NumberField K]
    (B : Ideal (𝓞 K)) (hB : B ≠ ⊥) (F : Ideal (𝓞 K) → ℂ) :
    ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * B).IsPrincipal}, F (I * B) =
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B}, F J := by
  let e : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * B).IsPrincipal} →
      {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B} :=
    fun I => ⟨I.1 * B, mul_ne_zero I.2.1 hB, I.2.2, Ideal.mul_le_inf.trans inf_le_right⟩
  have he : Function.Bijective e := by
    constructor
    · intro I I' h
      have h' : I.1 * B = I'.1 * B := congrArg Subtype.val h
      exact Subtype.ext (mul_right_cancel₀ hB h')
    · intro J
      obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 J.2.2.2
      have hI0 : I ≠ ⊥ := by
        rintro rfl
        exact J.2.1 (by rw [hI, Ideal.mul_bot])
      refine ⟨⟨I, hI0, ?_⟩, Subtype.ext ?_⟩
      · rw [mul_comm, ← hI]; exact J.2.2.1
      · show I * B = J.1
        rw [hI, mul_comm]
  exact (Equiv.ofBijective e he).tsum_eq (fun J => F J.1)

end GlobalTheory
end

