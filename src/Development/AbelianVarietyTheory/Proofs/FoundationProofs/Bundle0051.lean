import Mathlib
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import GroundTheory.PAdicHodge.AxLemma
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerReal
section
open Finset Filter Topology MeasureTheory
open Formalism.HermitianLattices.GL2PrimeSums

namespace GlobalTheory.TailIntegralOfSummatory

noncomputable def recSum (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ Icc 1 N, a n / (n : ℂ)

lemma recSum_succ (a : ℕ → ℂ) (N : ℕ) :
    recSum a (N + 1) = recSum a N + a (N + 1) / ((N + 1 : ℕ) : ℂ) := by
  unfold recSum
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma sum_eq (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n = N * recSum a N - ∑ k ∈ range N, recSum a k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, recSum_succ]
    have h : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    field_simp
    push_cast
    ring

lemma kronecker (a : ℕ → ℂ) (S : ℂ) (h : Tendsto (recSum a) atTop (𝓝 S)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a n) / (N : ℂ)) atTop (𝓝 0) := by
  have h2 := h.sub h.cesaro_smul
  rw [sub_self] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [sum_eq, Complex.real_smul]
  push_cast
  field_simp

lemma kronecker_real (a : ℕ → ℂ) (S : ℂ) (h : Tendsto (recSum a) atTop (𝓝 S)) :
    Tendsto (fun U : ℝ => psum a U / (U : ℂ)) atTop (𝓝 0) := by
  have h1 := (kronecker a S h).comp (tendsto_nat_floor_atTop (α := ℝ))
  have h2 : Tendsto (fun U : ℝ => (((⌊U⌋₊ : ℝ) / U : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_nat_floor_div_atTop (R := ℝ))
  have h3 := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU
  have hN : 0 < ⌊U⌋₊ := Nat.floor_pos.2 hU
  have hN' : (⌊U⌋₊ : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Function.comp, psum]
  push_cast
  field_simp

lemma sum_Icc_zero (a : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ Icc 0 N, (if k = 0 then 0 else a k) = ∑ k ∈ Icc 1 N, a k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega)]
    simp

lemma integral_eq (a : ℕ → ℂ) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, psum a u / (u : ℂ) ^ 2 =
      (recSum a ⌊U⌋₊ - psum a U / U) - (recSum a ⌊y⌋₊ - psum a y / y) := by
  have hd : ∀ t : ℝ, t ≠ 0 → HasDerivAt (fun t : ℝ => ((t : ℂ))⁻¹) (-(((t : ℂ)) ^ 2)⁻¹) t := by
    intro t ht
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    exact (hasDerivAt_inv ht').comp_ofReal
  have hne : ∀ t ∈ Set.Icc y U, t ≠ 0 := fun t ht => by
    have := ht.1
    intro h0
    linarith
  have hint : IntegrableOn (deriv (fun t : ℝ => ((t : ℂ))⁻¹)) (Set.Icc y U) := by
    have hc : ContinuousOn (fun t : ℝ => -(((t : ℂ)) ^ 2)⁻¹) (Set.Icc y U) := by
      refine ContinuousOn.neg (ContinuousOn.inv₀ (by fun_prop) ?_)
      intro t ht
      exact pow_ne_zero _ (by exact_mod_cast hne t ht)
    refine (hc.integrableOn_Icc).congr_fun ?_ measurableSet_Icc
    intro t ht
    exact ((hd t (hne t ht)).deriv).symm
  have key := sum_mul_eq_sub_sub_integral_mul (f := fun t : ℝ => ((t : ℂ))⁻¹)
    (fun k => if k = 0 then 0 else a k) (a := y) (b := U) (by linarith) hU
    (fun t ht => (hd t (hne t ht)).differentiableAt) hint
  simp only [sum_Icc_zero] at key
  have hfl : ⌊y⌋₊ ≤ ⌊U⌋₊ := Nat.floor_le_floor hU
  have hL : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, (((k : ℝ) : ℂ))⁻¹ * (if k = 0 then 0 else a k)
      = recSum a ⌊U⌋₊ - recSum a ⌊y⌋₊ := by
    have e : ∀ N : ℕ, recSum a N = ∑ n ∈ Ioc 0 N, a n / (n : ℂ) := fun N => by
      unfold recSum
      rfl
    rw [e, e, eq_sub_iff_add_eq', ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k ≠ 0 := by
      have := (Finset.mem_Ioc.1 hk).1
      omega
    rw [if_neg this, div_eq_inv_mul]
    simp
  have hI : ∫ t in Set.Ioc y U, deriv (fun t : ℝ => ((t : ℂ))⁻¹) t * ∑ k ∈ Icc 1 ⌊t⌋₊, a k
      = -∫ u in y..U, psum a u / (u : ℂ) ^ 2 := by
    rw [intervalIntegral.integral_of_le hU, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have := (hd t (hne t ⟨ht.1.le, ht.2⟩)).deriv
    simp only [this, psum]
    ring
  rw [hL, hI] at key
  simp only [psum] at key ⊢
  linear_combination -key

theorem tail_integral : Formalism.HermitianLattices.GL2PrimeSums.SmoothedRemainderIntegralFormula := by
  intro a S h y hy
  have h' : Tendsto (recSum a) atTop (𝓝 S) := h
  refine ⟨(S - 0) - (recSum a ⌊y⌋₊ - psum a y / y), ?_, ?_⟩
  · have h1 := ((h'.comp (tendsto_nat_floor_atTop (α := ℝ))).sub
      (kronecker_real a S h')).sub_const (recSum a ⌊y⌋₊ - psum a y / y)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop y] with U hU
    rw [integral_eq a hy hU]
    rfl
  · have hy0 : (y : ℂ) ≠ 0 := by
      have : y ≠ 0 := by linarith
      exact_mod_cast this
    have e : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ)
        = y * recSum a ⌊y⌋₊ - psum a y := by
      unfold recSum psum
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    unfold Gchi
    rw [e]
    field_simp
    ring

end GlobalTheory.TailIntegralOfSummatory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCocycleCoboundaryOfNorms
section
open GlobalTheory.NeedB Polynomial
open scoped IntermediateField

namespace GlobalTheory.NeedB.NormCob

theorem hom_pow {G : Type*} [Group G] {N : ℕ} (y : G → ZMod N) (hy : ∀ g h, y (g * h) = y g + y h) (σ : G) (q : ℕ) :
    y (σ ^ q) = q * y σ := by
  have h1 : y 1 = 0 := by
    have := hy 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  induction q with
  | zero => simp [h1]
  | succ q ih => rw [pow_succ, hy, ih]; push_cast; ring

theorem exists_generator {G : Type*} [Group G] {N : ℕ} (hN : 0 < N) (y : G → ZMod N)
    (hy : ∀ g h, y (g * h) = y g + y h) :
    ∃ (d m : ℕ) (σ : G), 0 < m ∧ m * d = N ∧ y σ = m ∧ ∀ g, m ∣ (y g).val := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  have h1 : y 1 = 0 := by simpa using hom_pow y hy 1 0
  have hex : ∃ m : ℕ, 0 < m ∧ ∃ g, y g = m := ⟨N, hN, 1, by simp [h1]⟩
  obtain ⟨hm, σ, hσ⟩ := Nat.find_spec hex
  set m := Nat.find hex with hmdef
  have key : ∀ n : ℕ, (∃ g, y g = n) → m ∣ n := by
    rintro n ⟨g, hg⟩
    by_contra hnd
    have hr : 0 < n % m := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    refine Nat.find_min hex (Nat.mod_lt n hm) ⟨hr, g * (σ ^ (n / m))⁻¹, ?_⟩
    have h2 := hy (g * (σ ^ (n / m))⁻¹) (σ ^ (n / m))
    rw [inv_mul_cancel_right, hg, hom_pow y hy, hσ] at h2
    have h3 : (n : ZMod N) = ((n % m : ℕ) : ZMod N) + ((n / m : ℕ) : ZMod N) * m := by
      conv_lhs => rw [← Nat.mod_add_div' n m]
      push_cast; ring
    exact (add_right_cancel (h2.symm.trans h3))
  obtain ⟨d, hd⟩ := key N ⟨1, by simp [h1]⟩
  exact ⟨d, m, σ, hm, hd.symm, hσ, fun g => key _ ⟨g, by simp⟩⟩

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem agree {β : Ω} {g g' : Ω ≃ₐ[K] Ω} (h : g β = g' β) (x : K⟮β⟯) : g x = g' x := by
  have : (g : Ω →ₐ[K] Ω).comp K⟮β⟯.val = (g' : Ω →ₐ[K] Ω).comp K⟮β⟯.val := by
    apply IntermediateField.adjoin_algHom_ext
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact h
  exact DFunLike.congr_fun this x

theorem norm_eq_prod [CharZero K] [IsAlgClosure K Ω] {β : Ω} (σ : Ω ≃ₐ[K] Ω) (d : ℕ)
    (hinj : ∀ i < d, ∀ j < d, (σ ^ i) β = (σ ^ j) β → i = j)
    (hsurj : ∀ g : Ω ≃ₐ[K] Ω, ∃ j < d, g β = (σ ^ j) β) (γ : K⟮β⟯) :
    algebraMap K Ω (Algebra.norm K γ) = ∏ j ∈ Finset.range d, (σ ^ j) γ := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  rw [Algebra.norm_eq_prod_embeddings K Ω γ]
  symm
  refine Finset.prod_bij (fun j _ => ((σ ^ j : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp K⟮β⟯.val) (by simp) ?_ ?_ ?_
  · intro i hi j hj hij
    exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
      (DFunLike.congr_fun hij (IntermediateField.AdjoinSimple.gen K β))
  · intro τ _
    obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (F := K) (E := Ω) (K := Ω)
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) τ
    let g : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
    obtain ⟨j, hj, hg⟩ := hsurj g
    refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
    rw [← hφ]
    ext x
    exact (agree hg x).symm
  · intro j _
    rfl

theorem carry_coboundary : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w ∧ ∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h) := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb ((map_eq_zero _).mp hβ.symm)
  obtain ⟨hlc, hdef, hhom, -⟩ := GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  set y := kum (N := N) (K := K) ζ β with hydef
  obtain ⟨d, m, σ, hm, hmd, hσ, hdvd⟩ := exists_generator hN y hhom
  have hpow : ∀ j : ℕ, y (σ ^ j) = ((m * j : ℕ) : ZMod N) := fun j => by
    rw [hom_pow y hhom, hσ]; push_cast; ring
  have hval : ∀ g, (y g).val = m * ((y g).val / m) := fun g => (Nat.mul_div_cancel' (hdvd g)).symm
  have hlt : ∀ g, (y g).val / m < d := fun g => by
    apply Nat.div_lt_of_lt_mul
    rw [hmd]; exact ZMod.val_lt _
  have hyk : ∀ g, y g = y (σ ^ ((y g).val / m)) := fun g => by
    rw [hpow, ← hval, ZMod.natCast_zmod_val]
  have hag : ∀ g g', y g = y g' → g β = g' β := fun g g' h => by rw [hdef g, hdef g', h]
  haveI : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  obtain ⟨γ, hγ⟩ := hnorm K⟮β⟯ inferInstance a ha
  have hγ0 : (γ : Ω) ≠ 0 := by
    intro h
    have : γ = 0 := Subtype.ext h
    rw [this, Algebra.norm_zero] at hγ
    exact ha hγ.symm
  have hprod : algebraMap K Ω a = ∏ j ∈ Finset.range d, (σ ^ j) γ := by
    rw [← hγ]
    refine norm_eq_prod σ d ?_ (fun g => ⟨_, hlt g, hag _ _ (hyk g)⟩) γ
    intro i hi j hj hij
    have hi' : m * i < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hi hm
    have hj' : m * j < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hj hm
    rw [hdef, hdef (σ ^ j), hpow, hpow, ZMod.val_cast_of_lt hi', ZMod.val_cast_of_lt hj'] at hij
    exact Nat.eq_of_mul_eq_mul_left hm (hζ.pow_inj hi' hj' (mul_right_cancel₀ hβ0 hij))
  let P : ℕ → Ω := fun n => ∏ j ∈ Finset.range n, (σ ^ j) γ
  have hP0 : ∀ n, P n ≠ 0 := fun n => Finset.prod_ne_zero_iff.mpr fun j _ => (_root_.map_ne_zero _).mpr hγ0
  have hPadd : ∀ (g : Ω ≃ₐ[K] Ω) (i n : ℕ), y g = y (σ ^ i) → P i * g (P n) = P (i + n) := by
    intro g i n hg
    simp only [P]
    rw [Finset.prod_range_add, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    have : y (g * σ ^ j) = y (σ ^ (i + j)) := by rw [pow_add, hhom, hhom, hg]
    exact agree (hag _ _ this) γ
  have hPd : ∀ r, P (d + r) = algebraMap K Ω a * P r := by
    intro r
    have h1 : y 1 = y (σ ^ d) := by
      rw [hpow, hmd, ← pow_zero σ, hpow]; simp
    rw [← hPadd 1 d r h1, hprod]
    rfl
  refine ⟨fun g => Units.mk0 (P ((y g).val / m)) (hP0 _),
    hlc.comp (fun z : ZMod N => Units.mk0 (P (z.val / m)) (hP0 _)), fun g h => ?_⟩
  simp only [Units.val_mk0]
  rw [hPadd g _ _ (hyk g), hhom, ZMod.val_add]
  have hg := hlt g
  have hh := hlt h
  rw [hval g, hval h, ← mul_add, Nat.mul_div_cancel_left _ hm, Nat.mul_div_cancel_left _ hm]
  generalize (y g).val / m = i at *
  generalize (y h).val / m = j at *
  by_cases hij : i + j < d
  · have : m * (i + j) < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hij hm
    rw [Nat.mod_eq_of_lt this, Nat.mul_div_cancel_left _ hm, mul_comm]
  · obtain ⟨r, hr⟩ : ∃ r, i + j = d + r := ⟨i + j - d, by omega⟩
    have hrd : r < d := by omega
    have : m * r < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hrd hm
    rw [hr, mul_add, hmd, Nat.add_mod_left, Nat.mod_eq_of_lt this, Nat.mul_div_cancel_left _ hm, hPd, pow_add, hα]
    ring

end GlobalTheory.NeedB.NormCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombination
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.LauZ

variable (p : ℕ) [hp : Fact p.Prime]

def red : Lau p →+* LaurentSeries (ZMod p) where
  toFun f := f.map (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_one' := by
    ext n
    show PadicInt.toZMod ((1 : Lau p).coeff n) = (1 : LaurentSeries (ZMod p)).coeff n
    rw [HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> simp
  map_mul' x y := HahnSeries.map_mul _
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

theorem red_coeff (f : Lau p) (n : ℤ) : (red p f).coeff n = PadicInt.toZMod (f.coeff n) := rfl

def lift (F : LaurentSeries (ZMod p)) : Lau p :=
  ⟨fun n => ((F.coeff n).val : ℤ_[p]), F.isPWO_support'.mono fun n hn => by
    simp only [Function.mem_support] at hn ⊢
    intro h; apply hn; rw [h]; simp⟩

theorem red_lift (F : LaurentSeries (ZMod p)) : red p (lift p F) = F := by
  ext n
  rw [red_coeff]
  show PadicInt.toZMod (((F.coeff n).val : ℕ) : ℤ_[p]) = F.coeff n
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem red_single (a : ℤ) : red p (HahnSeries.single a (1 : ℤ_[p])) = HahnSeries.single a (1 : ZMod p) := by
  ext n
  rw [red_coeff]
  by_cases h : n = a
  · subst h; simp
  · simp [HahnSeries.coeff_single_of_ne h]

theorem exists_pow_comb (f : Lau p) : ∃ (g : Fin p → Lau p) (h : Lau p),
    f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * g j ^ p + (p : Lau p) * h := by
  obtain ⟨G, hG⟩ := GlobalTheory.T.laurentSeries_eq_sum_single_mul_pow_prime p (red p f)
  set S : Lau p := ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * lift p (G j) ^ p
  have hS : red p S = red p f := by
    rw [hG]
    simp only [S, map_sum, map_mul, map_pow, red_single, red_lift]
  have h0 : (f - S).map (PadicInt.toZMod (p := p)).toNonUnitalRingHom = 0 := by
    show red p (f - S) = 0
    rw [map_sub, hS, sub_self]
  obtain ⟨h, hh⟩ := (GlobalTheory.K5.Basic.dvd_iff_map p (f - S)).2 h0
  exact ⟨fun j => lift p (G j), h, by rw [← hh, add_sub_cancel]⟩

end GlobalTheory.K5.LauZ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelOneTwelveMulFinrankModularFormLowerBoundStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound : ∀ n : ℤ, Even n → n + 5 + 3 * (if n % 4 = 0 then 1 else -1) + 4 * (if n % 6 = 0 then 1 else if n % 6 = 2 then -1 else 0) ≤ 12 * (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := by
  first | exact @GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound | exact GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound | (intros; apply GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineFunctionalEqPeriodMul
section
open TensorProduct GroundTheory.PAdicHodge UniformSpace

namespace GlobalTheory

theorem line_functional_eq_period_mul : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
  (g : S → Module.End ℤ_[l] M) (ρ : S → Matrix (Fin 2) (Fin 2) (PadicAlgCl l))
  (L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l]) (F : Finset (PadicAlgCl l)),
  (∀ K : IntermediateField ℚ_[l] (PadicAlgCl l), (∀ a ∈ F, a ∈ K) → ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l,
    ∃ s, ∀ b ∈ B, L (1 ⊗ₜ[ℤ_[l]] g s b) = τ • L (1 ⊗ₜ[ℤ_[l]] b)) →
  ∀ (m : ℕ) (σ : Fin m → (Fin 2 → PadicAlgCl l) →ₗ[PadicAlgCl l] TensorProduct ℤ_[l] (PadicAlgCl l) M),
  (∀ i v, σ i v ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype)) →
  (∀ i s v, LinearMap.baseChange (PadicAlgCl l) (g s) (σ i v) = σ i (Matrix.mulVec (ρ s) v)) →
  (∀ i, L (σ i ![1, 0]) = 0) →
  ∃ (κ : Fin m → PadicAlgCl l) (per : ℂ_[l]), ‖per‖ = 1 ∧ ∀ i v, L (σ i v) = per * ((κ i * v 1 : PadicAlgCl l) : ℂ_[l]) := by
  intro l _ M S _ _ B g ρ L F hgal m σ hσB hσeq hσ0
  classical

  have hsm : ∀ (a : PadicAlgCl l) (z : ℂ_[l]), a • z = (a : ℂ_[l]) * z := fun a z => by
    rw [Algebra.smul_def]; rfl
  set y : Fin m → ℂ_[l] := fun i => L (σ i ![0, 1]) with hy
  have hLv : ∀ i v, L (σ i v) = (v 1 : ℂ_[l]) * y i := by
    intro i v
    have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
      ext j; fin_cases j <;> simp
    calc L (σ i v) = L (σ i (v 0 • ![1, 0] + v 1 • ![0, 1])) := by rw [← hv]
      _ = _ := by rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, hσ0, smul_zero,
          zero_add, hsm]
  by_cases hall : ∀ i, y i = 0
  · refine ⟨0, 1, norm_one, fun i v => ?_⟩
    rw [hLv, hall i]; simp
  push_neg at hall
  obtain ⟨i₀, hy0⟩ := hall

  have hex : ∀ i, ∃ Sf : Finset (PadicAlgCl l × B),
      σ i ![0, 1] = ∑ q ∈ Sf, q.1 ⊗ₜ[ℤ_[l]] (q.2 : M) := by
    intro i
    obtain ⟨t, ht⟩ := hσB i ![0, 1]
    obtain ⟨Sf, rfl⟩ := TensorProduct.exists_finset t
    refine ⟨Sf, ?_⟩
    rw [← ht, map_sum]
    simp [LinearMap.baseChange_tmul]
  choose Sf hSf using hex
  set T : Finset (PadicAlgCl l) := F ∪ Finset.univ.biUnion (fun i => (Sf i).image Prod.fst) with hT
  set K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (T : Set (PadicAlgCl l))
    with hK
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hTK : ∀ a ∈ T, a ∈ K := fun a ha => IntermediateField.subset_adjoin _ _ (by simpa using ha)
  have hFK : ∀ a ∈ F, a ∈ K := fun a ha => hTK a (Finset.mem_union_left _ ha)
  have hSK : ∀ i, ∀ q ∈ Sf i, q.1 ∈ K := fun i q hq =>
    hTK _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
      Finset.mem_image_of_mem _ hq⟩))

  have hmul : ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l, ∃ c : PadicAlgCl l,
      ∀ i, τ • y i = (c : ℂ_[l]) * y i := by
    intro τ
    obtain ⟨s, hs⟩ := hgal K hFK τ
    refine ⟨ρ s 1 1, fun i => ?_⟩
    have h1 : L (LinearMap.baseChange (PadicAlgCl l) (g s) (σ i ![0, 1])) = τ • y i := by
      rw [hy]
      simp only
      rw [hSf i, map_sum, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [LinearMap.baseChange_tmul]
      have e1 : ∀ x : M, q.1 ⊗ₜ[ℤ_[l]] x = q.1 • ((1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] x) := fun x => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, e1 (q.2 : M), map_smul, map_smul, hsm, hsm, hs _ q.2.2, smul_mul',
        gal_smul_coe, show τ q.1 = q.1 from τ.commutes ⟨q.1, hSK i q hq⟩]
    rw [← h1, hσeq, hLv]
    congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hfix : ∀ i, ∃ k : K, ((k : PadicAlgCl l) : ℂ_[l]) = y i / y i₀ := by
    intro i
    refine exists_eq_coe_of_forall_smul_eq fun τ => ?_
    obtain ⟨c, hc⟩ := hmul τ
    have hne : τ • y i₀ ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_smul_gal, norm_ne_zero_iff]; exact hy0
    have hc0 : (c : ℂ_[l]) ≠ 0 := by
      intro h0; apply hne; rw [hc, h0, zero_mul]
    rw [smul_div₀', hc, hc]
    field_simp
  choose k hk using hfix

  obtain ⟨a, ha⟩ := (Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt (y i₀)
    (norm_pos_iff.2 hy0)
  rw [dist_eq_norm] at ha
  have hna : ‖(a : ℂ_[l])‖ = ‖y i₀‖ := by
    have e : (a : ℂ_[l]) = -(y i₀ - (a : ℂ_[l])) + y i₀ := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact ha.ne),
      norm_neg, max_eq_right ha.le]
  have ha0 : (a : ℂ_[l]) ≠ 0 := by
    rw [← norm_ne_zero_iff, hna, norm_ne_zero_iff]; exact hy0
  refine ⟨fun i => (k i : PadicAlgCl l) * a, y i₀ / (a : ℂ_[l]), ?_, fun i v => ?_⟩
  · rw [norm_div, hna, div_self (norm_ne_zero_iff.2 hy0)]
  · rw [hLv, Completion.coe_mul, Completion.coe_mul, hk i]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MapOneDirichlet
section
open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.KummerEisensteinGalois

theorem map_smF_hom {K L : Type} [Field K] [CharZero K] [Field L] [CharZero L] (f : K →+* L) (c : ℤ) (j M : ℕ) (ζ : K)
    (a b : ℤ) (n : ℕ) : f (smF c j M ζ a b n) = smF c j M (f ζ) a b n := by
  simp [smF, eisF, const0, coefPos, apply_ite f, map_ofNat]

theorem map_cmul_hom {K L : Type} [Field K] [CharZero K] [Field L] [CharZero L] (f : K →+* L) (u v : ℕ → K) (n : ℕ) :
    f (cmul u v n) = cmul (fun i => f (u i)) (fun i => f (v i)) n := by
  simp [cmul, map_sum, map_mul]

theorem map_one_dirichlet {K L : Type} [Field K] [Field L] (f : K →+* L) (q : ℕ) (x : ZMod q) :
    f ((1 : DirichletCharacter K q) x) = (1 : DirichletCharacter L q) x := by
  by_cases h : IsUnit x
  · obtain ⟨u, rfl⟩ := h
    simp [MulChar.one_apply_coe]
  · simp [MulChar.map_nonunit _ h]

theorem map_pieceT_one : ∀ (N p m k : ℕ) [NeZero p] (K L : Type) [Field K] [CharZero K] [Field L] [CharZero L] (f : K →+* L) (c d : ℤ) (w w' : ℤ × ℤ)
    (ζ : K) (S : Finset (GL (Fin 2) (ZMod (p ^ m)))) (r : ℕ),
    f (pieceT N p m m k (1 : DirichletCharacter K (p ^ m)) c d w w' ζ S r) =
      pieceT N p m m k (1 : DirichletCharacter L (p ^ m)) c d w w' (f ζ) S r := by
  intro N p m k _ K L _ _ _ _ f c d w w' ζ S r
  simp only [pieceT, map_mul, map_neg, map_zpow₀, map_natCast, map_sum, map_cmul_hom, map_smF_hom, map_one_dirichlet]

end GlobalTheory.KummerEisensteinGalois
end

