import ReciprocityTheory.Chebotarev.Bundle0002

-- bundled from ReciprocityTheory.Chebotarev.CasimirPowerSurjectiveSymmetric
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

def E1 : Prop :=
  (∀ (E : Type) [Field E] [NumberField E] (f : NZIdeal E → ℂ), (∀ a, ‖f a‖ ≤ 1) → ∀ s : ℝ, 1 < s →
      Summable (fun a : NZIdeal E => f a * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)))) ∧
  (∀ (E : Type) [Field E] [NumberField E] (s : ℝ), 1 < s →
      dedekindZeta E s = ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) ∧
  (∀ (E : Type) [Field E] [NumberField E] (s : ℝ), 1 < s →
      Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)))

def E2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (χ : DirichletCharacter ℂ l) (s : ℝ), 1 < s →
    Complex.exp (abelian₂ E χ s) = Lser E χ s

def CasimirPowerSurjectiveSymmetric : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (χ : DirichletCharacter ℂ l),
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → ‖abelian₂ E χ s - Psum E χ s‖ ≤ C

def faceMap_castSucc_comp_eq_succ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E],
    ∃ C : ℝ, ∀ s : ℝ, s ∈ Set.Ioc 1 2 → |PE E s - Real.log (1 / (s - 1))| ≤ C

def SmoothMapSeminormBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (χ : DirichletCharacter ℂ l),
    ContinuousOn (fun s : ℝ => abelian₂ E χ s) (Set.Ioi 1)

def KProp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Irreducible (Polynomial.cyclotomic l E) →
    ∀ χ : DirichletCharacter ℂ l, χ ≠ 1 → ∃ L1 : ℂ, Tendsto (fun s : ℝ => Lser E χ s) (𝓝[>] 1) (𝓝 L1)

def S1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Irreducible (Polynomial.cyclotomic l E) →
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), PE E s - C ≤ ((l - 1 : ℕ) : ℝ) * Pcl E l 1 s

def S2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Irreducible (Polynomial.cyclotomic l E) →
    ∀ χ : DirichletCharacter ℂ l, χ ≠ 1 → ∀ m : ℕ, m ≠ 0 →
      ∃ q : Prm E, Nat.Coprime (Nrm q) (m * l) ∧ χ ((Nrm q : ℕ) : ZMod l) ≠ 1

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.CycOrth
section
open NumberField

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem cyor_nrm_pos (q : Prm E) : 0 < Nrm q := by
  unfold Nrm
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact q.ne_bot

theorem cyor_norm_cpow (q : Prm E) (s : ℝ) :
    ‖((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ = ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  rw [Complex.norm_natCast_cpow_of_pos (cyor_nrm_pos q)]
  simp

theorem cyor_cast_rpow (q : Prm E) (s : ℝ) :
    ((((Nrm q : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) = ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp

theorem cyor_term_norm_le {l : ℕ} (χ : DirichletCharacter ℂ l) (q : Prm E) (s : ℝ) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  rw [norm_mul, cyor_norm_cpow]
  have h1 := DirichletCharacter.norm_le_one χ ((Nrm q : ℕ) : ZMod l)
  have h2 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [norm_nonneg (χ ((Nrm q : ℕ) : ZMod l))]

theorem cyor_summable {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    Summable (fun q : Prm E => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))) :=
  Summable.of_norm_bounded hS (fun q => cyor_term_norm_le χ q s)

theorem psum_orth (l : ℕ) [NeZero l] (a : (ZMod l)ˣ) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    ∑ χ : DirichletCharacter ℂ l, χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s
      = ((Nat.totient l : ℕ) : ℂ) * (Pcl E l (a : ZMod l) s : ℂ) := by
  unfold Psum Pcl
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun χ _ => (cyor_summable χ s hS).mul_left _)]
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  congr 1
  funext q
  have hinv : (((a⁻¹ : (ZMod l)ˣ) : ZMod l)) = ((a : ZMod l))⁻¹ := by
    rw [ZMod.inv_coe_unit]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  simp_rw [hinv]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit]
  by_cases h : (a : ZMod l) = ((Nrm q : ℕ) : ZMod l)
  · rw [if_pos h, if_pos h.symm, cyor_cast_rpow]
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp

theorem norm_psum_le {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    ‖Psum E χ s‖ ≤ PE E s := by
  unfold Psum PE
  refine (norm_tsum_le_tsum_norm (cyor_summable χ s hS).norm).trans ?_
  exact Summable.tsum_le_tsum (fun q => cyor_term_norm_le χ q s) (cyor_summable χ s hS).norm hS

theorem pcl_one_le_re_psum_one (l : ℕ) [NeZero l] (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    Pcl E l 1 s ≤ (Psum E (1 : DirichletCharacter ℂ l) s).re := by
  unfold Pcl Psum
  rw [Complex.re_tsum (cyor_summable _ s hS)]
  have hS2 : Summable (fun q : Prm E =>
      if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hS
    · split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine Summable.tsum_le_tsum (fun q => ?_) hS2 (Complex.reCLM.summable (cyor_summable _ s hS))
  rw [← cyor_cast_rpow]
  split_ifs with h
  · rw [h]; simp
  · by_cases hu : IsUnit ((Nrm q : ℕ) : ZMod l)
    · rw [MulChar.one_apply hu, one_mul, Complex.ofReal_re]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · rw [MulChar.map_nonunit _ hu]; simp

theorem re_psum_one_le (l : ℕ) [NeZero l] (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    (Psum E (1 : DirichletCharacter ℂ l) s).re ≤ PE E s :=
  (Complex.re_le_norm _).trans (norm_psum_le _ s hS)

theorem pcl_nonneg (l : ℕ) (a : ZMod l) (s : ℝ) : 0 ≤ Pcl E l a s := by
  unfold Pcl
  refine tsum_nonneg (fun q => ?_)
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact le_rfl

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.CycTail
section
open NumberField IsDedekindDomain

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

noncomputable def primeBelow (q : Prm E) : ℕ := Ideal.absNorm (q.asIdeal.under ℤ)

theorem primeBelow_prime (q : Prm E) : (primeBelow q).Prime := by
  have : NeZero q.asIdeal := ⟨q.ne_bot⟩
  exact Nat.absNorm_under_prime q.asIdeal

theorem nrm_eq_primeBelow_pow (q : Prm E) : ∃ f : ℕ, Nrm q = primeBelow q ^ f :=
  have : q.asIdeal.LiesOver (Ideal.span {((primeBelow q : ℕ) : ℤ)}) := Int.liesOver_span_absNorm q.asIdeal
  ⟨_, Ideal.absNorm_eq_pow_inertiaDeg' q.asIdeal (primeBelow_prime q)⟩

theorem two_le_nrm (q : Prm E) : 2 ≤ Nrm q := by
  have h0 : Nrm q ≠ 0 := by
    unfold Nrm; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot
  have h1 : Nrm q ≠ 1 := by
    unfold Nrm; rw [Ne, Ideal.absNorm_eq_one_iff]; exact q.isPrime.ne_top
  omega

theorem primeBelow_sq_le (q : Prm E) (h : ¬ (Nrm q).Prime) : primeBelow q ^ 2 ≤ Nrm q := by
  obtain ⟨f, hf⟩ := nrm_eq_primeBelow_pow q
  have hp := primeBelow_prime q
  have h1 : Nrm q ≠ 1 := by have := two_le_nrm q; omega
  rw [hf] at h h1 ⊢
  have hf0 : f ≠ 0 := by rintro rfl; simp at h1
  have hf1 : f ≠ 1 := by rintro rfl; simp [hp] at h
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem mem_primesOverFinset_primeBelow (q : Prm E) :
    q.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((primeBelow q : ℕ) : ℤ)}) (𝓞 E) := by
  have hp := primeBelow_prime q
  have : (Ideal.span {((primeBelow q : ℕ) : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  rw [IsDedekindDomain.mem_primesOverFinset_iff (by simp [hp.ne_zero])]
  exact ⟨q.isPrime, Int.liesOver_span_absNorm q.asIdeal⟩

theorem card_primesOverFinset_le (p : ℕ) (hp : p.Prime) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 E)).card ≤ Module.finrank ℚ E := by
  have : (Ideal.span {(p:ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E (by simp [hp.ne_zero])

theorem card_filter_primeBelow_le (u : Finset (Prm E)) (p : ℕ) (hp : p.Prime) :
    (u.filter fun x => primeBelow x = p).card ≤ Module.finrank ℚ E := by
  classical
  refine le_trans ?_ (card_primesOverFinset_le (E := E) p hp)
  refine Finset.card_le_card_of_injOn (fun x => x.asIdeal) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter] at hx
    have := mem_primesOverFinset_primeBelow x
    rw [hx.2] at this
    exact this
  · intro x _ y _ hxy
    exact HeightOneSpectrum.ext hxy

theorem nonprime_term_le (q : Prm E) :
    (if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) ≤ 1 / ((primeBelow q : ℕ) : ℝ) ^ 2 := by
  split_ifs with h
  · positivity
  · have hq := primeBelow_sq_le q h
    have hp := (primeBelow_prime q).pos
    have hq' : ((primeBelow q : ℝ)) ^ 2 ≤ (Nrm q : ℝ) := by exact_mod_cast hq
    have hpos : (0 : ℝ) < (primeBelow q : ℝ) ^ 2 := by positivity
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos hq'

theorem summable_nonprime_norm :
    Summable (fun q : Prm E => if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) := by
  classical
  let G : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hG : Summable G := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hG0 : ∀ n, 0 ≤ G n := fun n => by positivity
  refine summable_of_sum_le (c := Module.finrank ℚ E * ∑' n, G n) (fun q => by
    dsimp only; split_ifs <;> positivity) (fun u => ?_)
  calc ∑ x ∈ u, (if (Nrm x).Prime then (0 : ℝ) else ((Nrm x : ℕ) : ℝ)⁻¹)
        ≤ ∑ x ∈ u, G (primeBelow x) := Finset.sum_le_sum fun x _ => nonprime_term_le x
    _ = ∑ b ∈ u.image (fun x => primeBelow x),
          (u.filter fun x => primeBelow x = b).card • G b := Finset.sum_comp _ _
    _ ≤ ∑ b ∈ u.image (fun x => primeBelow x), (Module.finrank ℚ E : ℝ) * G b := by
        refine Finset.sum_le_sum fun b hb => ?_
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hb
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hG0 _)
        exact_mod_cast card_filter_primeBelow_le u _ (primeBelow_prime x)
    _ = (Module.finrank ℚ E : ℝ) * ∑ b ∈ u.image (fun x => primeBelow x), G b := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ E : ℝ) * ∑' n, G n :=
        mul_le_mul_of_nonneg_left (hG.sum_le_tsum _ fun n _ => hG0 n) (by positivity)

theorem finite_norm_mem (T : Finset ℕ) : {q : Prm E | Nrm q ∈ T}.Finite := by
  have h : {I : Ideal (𝓞 E) | Ideal.absNorm I ∈ T}.Finite := by
    have : {I : Ideal (𝓞 E) | Ideal.absNorm I ∈ T} = ⋃ n ∈ T, {I : Ideal (𝓞 E) | Ideal.absNorm I = n} := by
      ext; simp
    rw [this]
    exact Set.Finite.biUnion T.finite_toSet fun n _ => Ideal.finite_setOfPred_absNorm_eq n
  exact h.preimage (f := fun q : Prm E => q.asIdeal) (fun x _ y _ hxy => HeightOneSpectrum.ext hxy)

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.EulerFac
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

def Smooth {E : Type} [Field E] [NumberField E] (S : Finset (Prm E)) (a : Ideal (𝓞 E)) : Prop :=
  ∀ q : Prm E, q.asIdeal ∣ a → q ∈ S

theorem prm_eq_of_dvd {E : Type} [Field E] [NumberField E] {p q : Prm E}
    (h : p.asIdeal ∣ q.asIdeal) : p = q :=
  IsDedekindDomain.HeightOneSpectrum.ext ((prime_dvd_prime_iff_eq p.prime q.prime).1 h)

theorem smooth_empty_iff {E : Type} [Field E] [NumberField E] {a : Ideal (𝓞 E)} (ha : a ≠ ⊥) :
    Smooth ∅ a ↔ a = ⊤ := by
  constructor
  · intro hs
    by_contra htop
    obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal a htop
    have hMb : M ≠ ⊥ := fun h => ha (le_bot_iff.1 (h ▸ haM))
    let q : Prm E := ⟨M, hM.isPrime, hMb⟩
    exact absurd (hs q (Ideal.dvd_iff_le.2 haM)) (Finset.notMem_empty q)
  · rintro rfl q hq
    rw [← Ideal.one_eq_top] at hq
    exact absurd (isUnit_of_dvd_one hq) q.prime.not_isUnit

theorem smooth_insert_mul {E : Type} [Field E] [NumberField E] [DecidableEq (Prm E)] {S : Finset (Prm E)} {b : Ideal (𝓞 E)}
    (q : Prm E) (k : ℕ) (hb : Smooth S b) : Smooth (insert q S) (q.asIdeal ^ k * b) := by
  intro p hp
  rcases p.prime.dvd_or_dvd hp with h | h
  · exact Finset.mem_insert.2 (Or.inl (prm_eq_of_dvd (p.prime.dvd_of_dvd_pow h)))
  · exact Finset.mem_insert_of_mem (hb p h)

theorem smooth_insert_decomp {E : Type} [Field E] [NumberField E] [DecidableEq (Prm E)] {S : Finset (Prm E)} (q : Prm E)
    {a : Ideal (𝓞 E)} (ha : a ≠ ⊥) (hs : Smooth (insert q S) a) :
    ∃ (k : ℕ) (b : Ideal (𝓞 E)), b ≠ ⊥ ∧ Smooth S b ∧ a = q.asIdeal ^ k * b := by
  obtain ⟨k, b, hqb, hab⟩ := WfDvdMonoid.max_power_factor (a₀ := a) ha q.irreducible
  refine ⟨k, b, ?_, ?_, hab⟩
  · rintro rfl
    exact ha (by rw [hab, Ideal.mul_bot])
  · intro p hp
    have hpa : p.asIdeal ∣ a := hab ▸ dvd_mul_of_dvd_right hp _
    rcases Finset.mem_insert.1 (hs p hpa) with h | h
    · exact absurd (h ▸ hp) hqb
    · exact h

theorem smooth_mul_inj {E : Type} [Field E] [NumberField E] {S : Finset (Prm E)} {q : Prm E} (hq : q ∉ S)
    {b b' : Ideal (𝓞 E)} (hb : Smooth S b) (hb' : Smooth S b') {k k' : ℕ}
    (h : q.asIdeal ^ k * b = q.asIdeal ^ k' * b') : k = k' ∧ b = b' := by
  have hq0 : q.asIdeal ≠ 0 := q.ne_bot
  have key : ∀ {c c' : Ideal (𝓞 E)} {m m' : ℕ}, Smooth S c → m < m' →
      q.asIdeal ^ m * c ≠ q.asIdeal ^ m' * c' := by
    intro c c' m m' hc hlt he
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [show q.asIdeal ^ (m + n + 1) * c' = q.asIdeal ^ m * (q.asIdeal ^ (n + 1) * c') by
      rw [← mul_assoc, ← pow_add, add_assoc]] at he
    have hc' := mul_left_cancel₀ (pow_ne_zero m hq0) he
    exact hq (hc q (hc' ▸ dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero n)) _))
  rcases lt_trichotomy k k' with hlt | rfl | hlt
  · exact absurd h (key hb hlt)
  · exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero k hq0) h⟩
  · exact absurd h.symm (key hb' hlt)

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.EulerSum
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

noncomputable def idealZetaR (E : Type) [Field E] [NumberField E] (s : ℝ) : ℝ :=
  ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)

theorem idealZetaR_tendsto_sum_card_div (E : Type) [Field E] [NumberField E] :
    ∃ c : ℝ, Tendsto (fun n : ℕ ↦
    (∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = k} : ℝ)) / n)
      atTop (𝓝 c) := by
  refine ⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ E).comp tendsto_natCast_atTop_atTop).congr
    fun n ↦ ?_⟩
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem idealZetaR_term_eq (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 0 < s) (n : ℕ) :
    LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) n =
      (((Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  · rw [LSeries.term_of_ne_zero hn, Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_cpow (Nat.cast_nonneg n), div_eq_mul_inv]
    push_cast
    rfl

theorem summable_idealZetaR (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
  obtain ⟨c, hc⟩ := idealZetaR_tendsto_sum_card_div E
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = k} : ℝ))
      =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    simp_rw [Real.rpow_one]
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ c hc
    filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd h (Nat.cast_ne_zero.mpr hn)
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ ↦ Nat.cast_nonneg _) zero_le_one
    (s := (s : ℂ)) (by simpa using hs)
  unfold LSeriesSummable at this
  have h2 := (funext (idealZetaR_term_eq E (zero_lt_one.trans hs)))
  simp only [Complex.ofReal_natCast] at this h2
  rw [h2] at this
  exact Complex.summable_ofReal.mp this

theorem dedekindZeta_eq_idealZetaR (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    dedekindZeta E (s : ℂ) = ((idealZetaR E s : ℝ) : ℂ) := by
  unfold dedekindZeta LSeries idealZetaR
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n ↦ idealZetaR_term_eq E (zero_lt_one.trans hs) n

theorem sum_le_idealZetaR (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s)
    (T : Finset (Ideal (𝓞 E))) :
    ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤ idealZetaR E s := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := Ideal.absNorm) (t := T.image Ideal.absNorm)
    (fun I hI ↦ Finset.mem_image_of_mem _ hI)]
  refine le_trans ?_ ((summable_idealZetaR E hs).sum_le_tsum (T.image Ideal.absNorm)
    (fun n _ ↦ by positivity))
  refine Finset.sum_le_sum fun n _ ↦ ?_
  rw [Finset.sum_congr rfl (g := fun _ ↦ (n : ℝ) ^ (-s))
    (fun I hI ↦ by rw [(Finset.mem_filter.mp hI).2]), Finset.sum_const, nsmul_eq_mul]
  have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n
  have hc : Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} = hfin.toFinset.card :=
    Nat.card_eq_card_finite_toFinset hfin
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [hc, Nat.cast_le]
  refine Finset.card_le_card fun I hI ↦ ?_
  simp only [Finset.mem_filter] at hI
  simpa using hI.2

theorem summable_absNorm_rpow_ideal (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) :=
  summable_of_sum_le (c := idealZetaR E s) (fun _ ↦ by positivity) fun u ↦ sum_le_idealZetaR E hs u

theorem hasSum_absNorm_rpow_ideal (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    HasSum (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) (idealZetaR E s) := by
  have hsum := (summable_absNorm_rpow_ideal E hs).hasSum
  have h1 := ((Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 E) → ℕ)).hasSum_iff).mpr hsum
  have h2 := h1.sigma (g := fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)) (fun n ↦ by
    have : Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n).to_subtype
    have hc : ∀ c : {I : Ideal (𝓞 E) // Ideal.absNorm I = n},
        ((Ideal.absNorm (Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 E) → ℕ) ⟨n, c⟩) : ℕ) : ℝ)
          ^ (-s) = (n : ℝ) ^ (-s) := fun c ↦ by
      simp [Equiv.sigmaFiberEquiv, c.2]
    simp only [Function.comp_apply, hc]
    have h3 : HasSum (fun _ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n} ↦ (n : ℝ) ^ (-s))
        (∑' _ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n}, (n : ℝ) ^ (-s)) :=
      Summable.of_finite.hasSum
    rw [tsum_const, nsmul_eq_mul] at h3
    exact h3)
  rw [idealZetaR, h2.tsum_eq]
  exact hsum

theorem summable_absNorm_rpow (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun a : NZIdeal E => ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s)) :=
  (summable_absNorm_rpow_ideal E hs).subtype _

theorem dedekindZeta_eq_tsum (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    dedekindZeta E s = ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) := by
  have hsupp : Function.support (fun a : Ideal (𝓞 E) => ((Ideal.absNorm a : ℕ) : ℝ) ^ (-s)) ⊆
      {a | a ≠ ⊥} := by
    intro a ha hbot
    apply ha
    have hb : a = ⊥ := by simpa using hbot
    simp [hb, Real.zero_rpow (neg_ne_zero.mpr (zero_lt_one.trans hs).ne')]
  have h1 : ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) = idealZetaR E s := by
    rw [← (hasSum_absNorm_rpow_ideal E hs).tsum_eq]
    exact tsum_subtype_eq_of_support_subset hsupp
  rw [dedekindZeta_eq_idealZetaR E hs, ← h1, Complex.ofReal_tsum]
  refine tsum_congr fun a ↦ ?_
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]

theorem two_le_Nrm {E : Type} [Field E] [NumberField E] (q : Prm E) : 2 ≤ Nrm q := by
  have h0 : Ideal.absNorm q.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact q.ne_bot
  have h1 : Ideal.absNorm q.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact q.isPrime.ne_top
  unfold Nrm
  omega

theorem summable_prm_rpow (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) := by
  classical
  refine summable_of_sum_le (c := idealZetaR E s) (fun _ ↦ by positivity) fun u ↦ ?_
  unfold Nrm
  rw [← Finset.sum_image (f := fun I : Ideal (𝓞 E) ↦ ((Ideal.absNorm I : ℕ) : ℝ) ^ (-s))
    (g := IsDedekindDomain.HeightOneSpectrum.asIdeal)
    (fun v _ w _ h ↦ IsDedekindDomain.HeightOneSpectrum.ext h)]
  exact sum_le_idealZetaR E hs _

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.SplitDef
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

noncomputable def under {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') : Prm E where
  asIdeal := P.asIdeal.under (𝓞 E)
  isPrime := Ideal.IsPrime.under _ _
  ne_bot := Ideal.under_ne_bot (𝓞 E) P.ne_bot

theorem under_asIdeal {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') : (under (E := E) P).asIdeal = P.asIdeal.under (𝓞 E) := rfl

end ReciprocityTheory.Cheb
end

