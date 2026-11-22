import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.SChainPf
section
noncomputable section
open UpperTheory.V.ZK

namespace LateralTheory.Q.SChainPf

variable {A : Type} [CommRing A]

lemma bd_single {G : Type} [Group G] (m : ℕ) (g : Fin (m + 1) → G) (a : A) :
    bd A G m (Finsupp.single g a) = Finsupp.single (fun i => g i.succ) a +
      ∑ j : Fin (m + 1), ((-1 : A) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) a := by
  simp only [bd, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma bd_eq {G : Type} [Group G] (m : ℕ) :
    bd A G m = (groupHomology.inhomogeneousChains.d (Rep.trivial A G A) m).hom := by
  refine Finsupp.lhom_ext fun g a => ?_
  rw [bd_single, groupHomology.inhomogeneousChains.d_single]
  simp

lemma bd_bd {G : Type} [Group G] (m : ℕ) (z : Ch A G (m + 2)) : bd A G m (bd A G (m + 1) z) = 0 := by
  rw [bd_eq, bd_eq]
  have h := groupHomology.inhomogeneousChains.d_comp_d (Rep.trivial A G A) m
  have := congrArg (fun φ => φ.hom z) h
  simpa using this

lemma cm_single {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (g : Fin m → G) (a : A) :
    cm A f m (Finsupp.single g a) = Finsupp.single (fun i => f (g i)) a := by
  simp [cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

lemma contract_map {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (j : Fin (m + 1))
    (g : Fin (m + 1) → G) :
    (fun i => f (Fin.contractNth j (· * ·) g i)) = Fin.contractNth j (· * ·) (fun i => f (g i)) := by
  funext i
  simp only [Fin.contractNth]
  split_ifs <;> simp [map_mul]

lemma bd_cm {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Ch A G (m + 1)) :
    bd A H m (cm A f (m + 1) z) = cm A f m (bd A G m z) := by
  have : (bd A H m).comp (cm A f (m + 1)) = (cm A f m).comp (bd A G m) := by
    refine Finsupp.lhom_ext fun g a => ?_
    simp only [LinearMap.comp_apply, cm_single, bd_single, map_add, map_sum, map_smul]
    simp only [contract_map]
  exact LinearMap.congr_fun this z

lemma cm_comp {G H K : Type} [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) (m : ℕ)
    (z : Ch A G m) : cm A (g.comp f) m z = cm A g m (cm A f m z) := by
  have : cm A (g.comp f) m = (cm A g m).comp (cm A f m) := by
    refine Finsupp.lhom_ext fun x a => ?_
    simp [cm_single]
  exact LinearMap.congr_fun this z

lemma prism_single {G : Type} [Group G] (k : G) (m : ℕ) (g : Fin m → G) (a : A) :
    prism A k m (Finsupp.single g a) = ∑ i : Fin (m + 1), ((-1 : A) ^ (i : ℕ)) •
      Finsupp.single (Fin.insertNth (α := fun _ => G) i k
        fun j => if (j : ℕ) < i then g j else k⁻¹ * g j * k) a := by
  simp only [prism, Finsupp.linearCombination_single, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma insert_map {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (i : Fin (m + 1)) (k : G)
    (h : Fin m → G) :
    (fun j => f (Fin.insertNth (α := fun _ => G) i k h j)) =
      Fin.insertNth (α := fun _ => H) i (f k) (fun j => f (h j)) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun j => ?_) j <;> simp

lemma conj_map {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (i : Fin (m + 1)) (k : G)
    (g : Fin m → G) :
    (fun j : Fin m => f (if (j : ℕ) < i then g j else k⁻¹ * g j * k)) =
      fun j : Fin m => if (j : ℕ) < i then f (g j) else (f k)⁻¹ * f (g j) * f k := by
  funext j
  split_ifs <;> simp [map_mul, map_inv]

lemma cm_prism {G H : Type} [Group G] [Group H] (f : G →* H) (k : G) (m : ℕ) (z : Ch A G m) :
    cm A f (m + 1) (prism A k m z) = prism A (f k) m (cm A f m z) := by
  have : (cm A f (m + 1)).comp (prism A k m) = (prism A (f k) m).comp (cm A f m) := by
    refine Finsupp.lhom_ext fun g a => ?_
    simp only [LinearMap.comp_apply, cm_single, prism_single, map_sum, map_smul]
    simp only [insert_map, conj_map]
  exact LinearMap.congr_fun this z

def S (n : ℕ) : A := ∑ j : Fin n, (-1 : A) ^ ((j : ℕ) + 1)

lemma S_pair (n : ℕ) : (S n : A) + S (n + 1) = -1 := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    have h2 : (S (n + 2) : A) = S n := by
      simp only [S, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
      ring
    rw [h2, add_comm]; exact ih

lemma bd_single_triv {G : Type} [Group G] [Subsingleton G] (m : ℕ) (g : Fin (m + 1) → G)
    (h : Fin m → G) (a : A) : bd A G m (Finsupp.single g a) = Finsupp.single h ((1 + S (m + 1)) * a) := by
  rw [bd_single]
  have e1 : (fun i => g i.succ) = h := Subsingleton.elim _ _
  have e2 : ∀ j : Fin (m + 1), Fin.contractNth j (· * ·) g = h := fun _ => Subsingleton.elim _ _
  simp only [e1, e2, Finsupp.smul_single, smul_eq_mul, ← Finsupp.single_finsetSum, ← Finsupp.single_add,
    S, add_mul, Finset.sum_mul, one_mul]

lemma triv_bd {G : Type} [Group G] [Subsingleton G] (m : ℕ) (z : Ch A G (m + 1)) (hz : Cyc z) : Bd z := by
  let g1 : Fin (m + 1) → G := fun _ => 1
  let g0 : Fin m → G := fun _ => 1
  let g2 : Fin (m + 2) → G := fun _ => 1
  have hz1 : z = Finsupp.single g1 (z g1) := by
    ext x; rw [Subsingleton.elim x g1]; simp
  generalize z g1 = c at hz1
  subst hz1
  have hc : (1 + S (m + 1)) * c = 0 := by
    have := hz
    unfold Cyc at this
    rw [bd_single_triv m g1 g0] at this
    simpa using congrArg (fun w => w g0) this
  refine ⟨Finsupp.single g2 (c), ?_⟩
  rw [bd_single_triv (m + 1) g2 g1]
  congr 1
  have := S_pair (A := A) (m + 1)
  linear_combination (-1 : A) * hc + (c) * this

theorem SChain_of : UpperTheory.V.ZK.SChain :=
  fun _ _ => ⟨fun _ _ m z => bd_bd m z, fun _ _ _ _ f m z => bd_cm f m z,
    fun _ _ _ _ _ _ f g m z => cm_comp f g m z, fun _ _ _ _ f k m z => cm_prism f k m z,
    fun _ _ _ m z hz => triv_bd m z hz⟩

end LateralTheory.Q.SChainPf
end
end

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.SDetectCut
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.ZK

namespace LateralTheory.Q.SDetectCut

theorem root_eq_one {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) (q : ℕ) (η : R) (hη : η ^ q = 1)
    (h1 : η - 1 ∈ P) (hq : (q : R) ∉ P) : η = 1 := by
  by_contra hne
  apply hq
  have h0 : ∑ i ∈ Finset.range q, η ^ i = 0 := by
    have := mul_geom_sum η q
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have h2 : Ideal.Quotient.mk P η = 1 := by
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq]
    exact h1
  have h3 := congrArg (Ideal.Quotient.mk P) h0
  simp only [map_sum, map_pow, h2, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    map_zero] at h3
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h3

theorem surj_of_prime {A k : Type} [CommRing A] [CommRing k] (f : A →+* k) (hp : (Nat.card k).Prime) :
    Function.Surjective f := by
  intro y
  have : Fact (Nat.card k).Prime := ⟨hp⟩
  have : Finite k := Nat.finite_of_card_ne_zero hp.ne_zero
  have : Nontrivial k := Finite.one_lt_card_iff_nontrivial.1 hp.one_lt
  obtain ⟨n, hn⟩ := mem_zmultiples_of_prime_card (G := k) (p := Nat.card k) rfl (g := 1) (g' := y) one_ne_zero
  exact ⟨n, by simpa using hn⟩

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
theorem val_le (B : ValuationSubring Ω) (x : 𝓞 F) : B.valuation (algebraMap F Ω (x : F)) ≤ 1 := by
  have hz : IsIntegral ℤ (algebraMap F Ω (x : F)) := x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom
  exact (Valuation.integer.integers B.valuation).mem_of_integral hz.tower_top

omit [NumberField F] in

theorem frob_fix {v : HeightOneSpectrum (𝓞 F)} {B : ValuationSubring Ω} (hB : IsPlaceOver B v) {N : ℕ} (hN : N ≠ 0)
    {σ : G F Ω} (hσ : IsFrob B N σ) {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 F) ∉ v.asIdeal) {ζ : 𝓞 F}
    (hζ : IsPrimitiveRoot ζ q) {β : F} {x : Ω} (hx : x ^ q = algebraMap F Ω β) {a b t : 𝓞 F}
    (hb : b ∉ v.asIdeal) (ht : t ∉ v.asIdeal) (hab : β * b = a) (hc : a - t ^ q * b ∈ v.asIdeal) : σ x = x := by
  have : NeZero q := ⟨hq0⟩
  let ι : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F)
  have hι : ∀ y : 𝓞 F, ι y = algebraMap F Ω (y : F) := fun _ => rfl
  have hinj : Function.Injective ι := (algebraMap F Ω).injective.comp (RingOfIntegers.coe_injective)
  have hone : ∀ y : 𝓞 F, y ∉ v.asIdeal → B.valuation (ι y) = 1 := fun y hy =>
    le_antisymm (val_le B y) (not_lt.1 fun h => hy ((hB y).1 h))
  have hζ' : IsPrimitiveRoot (ι ζ) q := hζ.map_of_injective hinj
  have h1 : B.valuation (x ^ q - ι t ^ q) < 1 := by
    have e : (x ^ q - ι t ^ q) * ι b = ι (a - t ^ q * b) := by
      rw [hx, map_sub, map_mul, map_pow, sub_mul, hι a, hι b, ← hab, map_mul]
    have := (hB _).2 hc
    rw [← hι, ← e, map_mul, hone b hb, mul_one] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i : ℕ, B.valuation (x - ι (ζ ^ i * t)) < 1 := by
    by_contra! h
    have e := congrArg (Polynomial.eval x) (X_pow_sub_C_eq_prod hζ' (Nat.pos_of_ne_zero hq0) (rfl : ι t ^ q = ι t ^ q))
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_prod] at e
    rw [e, map_prod] at h1
    refine absurd h1 (not_lt.2 (Finset.one_le_prod' fun i _ => ?_))
    have := h i
    rwa [map_mul, map_pow] at this
  set c := ζ ^ i * t with hcdef
  have hcv : c ∉ v.asIdeal := fun h =>
    ht ((v.isPrime.mem_or_mem h).resolve_left fun h' =>
      v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' ((hζ.isUnit hq0).pow i)))
  have hxv : B.valuation x = 1 := by
    rw [← hone c hcv]
    exact Valuation.map_eq_of_sub_lt _ (by rw [hone c hcv]; exact hi)
  have h2 : B.valuation (σ (x - ι c)) < 1 := by
    have e : σ (x - ι c) = (σ (x - ι c) - (x - ι c) ^ N) + (x - ι c) ^ N := by ring
    rw [e]
    refine Valuation.map_add_lt _ (hσ.2 _ hi.le) ?_
    rw [map_pow]
    exact pow_lt_one' hi hN
  have h3 : B.valuation (σ x - x) < 1 := by
    have e : σ x - x = σ (x - ι c) - (x - ι c) := by
      rw [map_sub, hι, AlgEquiv.commutes]; ring
    rw [e]
    exact Valuation.map_sub_lt _ h2 hi
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hxv
  have h4 : (σ x / x) ^ q = 1 := by
    rw [div_pow, ← map_pow, hx, AlgEquiv.commutes, ← hx, div_self (pow_ne_zero _ hx0)]
  obtain ⟨j, -, hj⟩ := hζ'.eq_pow_of_pow_eq_one h4
  have h5 : σ x = ι (ζ ^ j) * x := by rw [map_pow, hj, div_mul_cancel₀ _ hx0]
  have h6 : ζ ^ j - 1 ∈ v.asIdeal := by
    rw [← hB, ← hι]
    have e : σ x - x = ι (ζ ^ j - 1) * x := by rw [h5, map_sub, map_one]; ring
    rwa [e, map_mul, hxv, mul_one] at h3
  have h7 : ζ ^ j = 1 := root_eq_one v.asIdeal q _ (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) h6 hq
  rw [h5, h7, map_one, one_mul]

theorem goal : SDetect := by
  intro L F _ _ _ _ _ l ν hl ζ hζ β b hb H
  have hq0 : l ^ ν ≠ 0 := pow_ne_zero _ hl.ne_zero
  generalize l ^ ν = q at *
  let Ω := AlgebraicClosure F
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F Ω (β : F)) (Nat.pos_of_ne_zero hq0)
  have hS : {v : HeightOneSpectrum (𝓞 F) | b * (q : 𝓞 F) ∈ v.asIdeal}.Finite := by
    simp_rw [← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors (by simp [hb, hq0])
  have : IsGalois F Ω := {}
  have hfix : ∀ g : Ω ≃ₐ[F] Ω, g x = x := by
    intro g
    have hV : IsOpen {σ : G F Ω | σ x = g x} := by
      have h1 : IsOpen (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := stabilizer_isOpen_of_isIntegral x
      have h2 := h1.preimage (continuous_const_mul g⁻¹)
      convert h2 using 1
      ext σ
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul,
        inv_smul_eq_iff]
      rfl
    obtain ⟨σ, hσV, v, hv, hd, B, hB, hσ⟩ :=
      (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
        hS).inter_open_nonempty _ hV ⟨g, rfl⟩
    have hp : (Nat.card (𝓞 F ⧸ v.asIdeal)).Prime := by
      have := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    have := v.isMaximal
    obtain ⟨s, a, b', hb', hab, hr⟩ := H v (fun h => hv (Ideal.mul_mem_right _ _ h)) (surj_of_prime _ hp)
    let := Ideal.Quotient.field v.asIdeal
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : 𝓞 F ⧸ v.asIdeal)
    rw [← hσV]
    refine frob_fix hB hp.ne_zero hσ hq0 (fun h => hv (Ideal.mul_mem_left _ _ h))
      (IsPrimitiveRoot.coe_units_iff.2 hζ) hx (a := a) (b := b') (t := t)
      (fun h => hb' (Ideal.Quotient.eq_zero_iff_mem.2 h))
      (fun h => s.ne_zero (ht ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)) hab ?_
    rw [← Ideal.Quotient.eq, map_mul, map_pow, ht, hr, Units.val_pow_eq_pow_val]
  obtain ⟨δ, hδ⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hfix
  have hd : (β : F) = δ ^ q := (algebraMap F Ω).injective (by rw [map_pow, hδ, hx])
  have h0 : δ ≠ 0 := by
    rintro rfl
    exact β.ne_zero (by rw [hd, zero_pow hq0])
  exact ⟨Units.mk0 δ h0, Units.ext (by simpa using hd)⟩

end LateralTheory.Q.SDetectCut
end

-- bundled from Development.EtaleCohomology.CyclotomicDiscriminants.SFewOfCut
section
noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain UpperTheory.V.KL UpperTheory.V.ZK

namespace LateralTheory.Q.SFewOfCut

theorem one_add_pow_eq (w : ℤ) (d : ℕ) : ∃ t : ℤ, (1 + w) ^ d = 1 + w * (d + w * t) := by
  induction d with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t + d + w * t, by rw [pow_succ, ht]; push_cast; ring⟩

theorem not_dvd_pow_sub_one (l c M d : ℕ) (hl : l.Prime) (hM : M < l ^ c) (hd0 : 0 < d) (hd : d < M) :
    ¬ (l : ℤ) ^ (c + M) ∣ (1 + (l : ℤ) ^ c) ^ d - 1 := by
  obtain ⟨t, ht⟩ := one_add_pow_eq ((l : ℤ) ^ c) d
  have hl0 : (l : ℤ) ^ c ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  rw [ht, add_sub_cancel_left, pow_add, mul_dvd_mul_iff_left hl0]
  intro h
  have key : ∀ j, j ≤ c → j ≤ M → l ^ j ≤ d := by
    intro j hjc hjM
    have h1 : (l : ℤ) ^ j ∣ (d : ℤ) + (l : ℤ) ^ c * t := (pow_dvd_pow _ hjM).trans h
    have h2 : (l : ℤ) ^ j ∣ (d : ℤ) := (dvd_add_left ((pow_dvd_pow _ hjc).mul_right t)).1 h1
    exact Nat.le_of_dvd hd0 (by exact_mod_cast h2)
  rcases le_total c M with h1 | h1
  · have := key c le_rfl h1; omega
  · have := key M h1 le_rfl
    have := Nat.lt_pow_self (n := M) hl.one_lt
    omega

theorem cast_dvd_of_not_dvd (l ν w : ℕ) (hl : l.Prime) (f : ℤ) (hf : ¬ (l : ℤ) ^ w ∣ f) :
    (f : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ w := by
  induction w generalizing f with
  | zero => simp at hf
  | succ w ih =>
    by_cases h : (l : ℤ) ∣ f
    · obtain ⟨g, rfl⟩ := h
      have hg : ¬ (l : ℤ) ^ w ∣ g := fun h => hf (by rw [pow_succ']; exact mul_dvd_mul_left _ h)
      rw [pow_succ']
      push_cast
      exact mul_dvd_mul_left _ (ih g hg)
    · have hc : IsCoprime f ((l : ℤ) ^ ν) :=
        (((Nat.prime_iff_prime_int.1 hl).irreducible.coprime_iff_not_dvd.2 h).symm).pow_right
      obtain ⟨a, b, hab⟩ := hc
      have h0 : ((l : ZMod (l ^ ν))) ^ ν = 0 := by exact_mod_cast ZMod.natCast_self (l ^ ν)
      have h1 : (f : ZMod (l ^ ν)) * a = 1 := by
        have := congrArg (Int.cast : ℤ → ZMod (l ^ ν)) hab
        push_cast at this
        rw [h0] at this
        linear_combination this
      exact (Dvd.intro _ h1).trans (one_dvd _)

theorem not_dvd_sub (l c M i j : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (hM : M < l ^ c) (hij : j < i) (hi : i < M) :
    ¬ (l : ℤ) ^ (c + M) ∣ (1 + (l : ℤ) ^ c) ^ i - (1 + (l : ℤ) ^ c) ^ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  intro h
  have h1 : (1 + (l : ℤ) ^ c) ^ (j + d) - (1 + (l : ℤ) ^ c) ^ j =
      (1 + (l : ℤ) ^ c) ^ j * ((1 + (l : ℤ) ^ c) ^ d - 1) := by ring
  rw [h1] at h
  have hco : IsCoprime (l : ℤ) (1 + (l : ℤ) ^ c) := by
    obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hc
    exact ⟨-(l : ℤ) ^ c', 1, by ring⟩
  exact not_dvd_pow_sub_one l c M d hl hM (by omega) (by omega) (hco.pow.dvd_of_dvd_mul_left h)

theorem pe_dvd (l c ν M E : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (hM : M < l ^ c) (hE : E < M) :
    (pe (1 + l ^ c) M E : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ (M * (c + M)) := by
  have h1 : (pe (1 + l ^ c) M E : ZMod (l ^ ν)) ∣
      ∏ _j ∈ (Finset.range M).erase E, (l : ZMod (l ^ ν)) ^ (c + M) := by
    unfold pe
    rw [Int.cast_prod]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun j hj => cast_dvd_of_not_dvd l ν _ hl _ ?_
    rw [Finset.mem_erase, Finset.mem_range] at hj
    push_cast
    rcases lt_or_gt_of_ne hj.1 with h | h
    · exact not_dvd_sub l c M E j hl hc hM h hE
    · rw [dvd_sub_comm]
      exact not_dvd_sub l c M j E hl hc hM h hj.2
  refine h1.trans ?_
  rw [Finset.prod_const, ← pow_mul, mul_comm]
  refine pow_dvd_pow _ (Nat.mul_le_mul_right _ ?_)
  exact (Finset.card_erase_le).trans (Finset.card_range M).le

theorem exists_index (G : Type) [CommGroup G] [Finite G] [IsCyclic G] (q : ℕ) (hq : q ∣ Nat.card G) :
    ∃ v : G →* Cq q, ∀ u, v u = 1 → ∃ s, u = s ^ q := by
  let e : Multiplicative (ZMod (Nat.card G)) ≃* G := zmodCyclicMulEquiv inferInstance
  haveI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  refine ⟨(AddMonoidHom.toMultiplicative (ZMod.castHom hq (ZMod q)).toAddMonoidHom).comp e.symm.toMonoidHom, ?_⟩
  intro u hu
  obtain ⟨x, rfl⟩ := e.surjective u
  have h1 : ZMod.castHom hq (ZMod q) (Multiplicative.toAdd x) = 0 := by
    simpa using congrArg Multiplicative.toAdd hu
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (Multiplicative.toAdd x)
  rw [← hn, map_natCast, ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨m, rfl⟩ := h1
  refine ⟨e (Multiplicative.ofAdd (m : ZMod _)), ?_⟩
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul, hn, ofAdd_toAdd]

theorem prim_map {R k : Type} [CommRing R] [IsDomain R] [Field k] (r : R →+* k) (l ν : ℕ) (hl : l.Prime)
    (hν : 1 ≤ ν) (hr : r l ≠ 0) (ζ : Rˣ) (hζ : IsPrimitiveRoot ζ (l ^ ν)) :
    IsPrimitiveRoot (Units.map (r : R →* k) ζ) (l ^ ν) := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hν
  have h1 : Units.map (r : R →* k) ζ ^ l ^ (n + 1) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h2 : ¬ Units.map (r : R →* k) ζ ^ l ^ n = 1 := by
    intro h
    have h3 : IsPrimitiveRoot ((ζ : R) ^ l ^ n) l :=
      (IsPrimitiveRoot.coe_units_iff.2 hζ).pow (pow_pos hl.pos _) (pow_succ l n)
    have h4 := congrArg r (h3.geom_sum_eq_zero hl.one_lt)
    have h5 : r ((ζ : R) ^ l ^ n) = 1 := by simpa using congrArg Units.val h
    rw [map_sum] at h4
    simp only [map_pow r ((ζ : R) ^ l ^ n), h5] at h4
    apply hr
    simpa using h4
  rw [← orderOf_eq_prime_pow h2 h1]
  exact IsPrimitiveRoot.orderOf _

section Res

variable {F : Type} [Field F] {k : Type} [Field k] {r : 𝓞 F →+* k}

theorem res_one : Res r 1 1 := ⟨1, 1, by simp, by simp, by simp⟩

theorem res_mul {α β : Fˣ} {u w : kˣ} (h : Res r α u) (h' : Res r β w) : Res r (α * β) (u * w) := by
  obtain ⟨a, b, hb, h1, h2⟩ := h
  obtain ⟨a', b', hb', h1', h2'⟩ := h'
  refine ⟨a * a', b * b', by rw [map_mul]; exact mul_ne_zero hb hb', ?_, ?_⟩
  · have e1 : ((b * b' : 𝓞 F) : F) = (b : F) * (b' : F) := rfl
    have e2 : ((a * a' : 𝓞 F) : F) = (a : F) * (a' : F) := rfl
    rw [e1, e2, ← h1, ← h1', Units.val_mul]; ring
  · rw [map_mul, map_mul, h2, h2', Units.val_mul]; ring

theorem res_inv {α : Fˣ} {u : kˣ} (h : Res r α u) : Res r α⁻¹ u⁻¹ := by
  obtain ⟨a, b, hb, h1, h2⟩ := h
  refine ⟨b, a, by rw [h2]; exact mul_ne_zero u.ne_zero hb, ?_, ?_⟩
  · rw [← h1, Units.inv_mul_cancel_left]
  · rw [h2, Units.inv_mul_cancel_left]

theorem res_pow {α : Fˣ} {u : kˣ} (h : Res r α u) (n : ℕ) : Res r (α ^ n) (u ^ n) := by
  induction n with
  | zero => simpa using res_one
  | succ n ih => rw [pow_succ, pow_succ]; exact res_mul ih h

end Res

theorem isPrimFam_pi {R A I : Type} [CommRing R] [CommRing A] {m : ℕ}
    (Φ : I → ∀ n : ℕ, Ch A (GL (Fin n) R) (m + 1) →ₗ[A] A) (h : ∀ i, IsPrimFam (Φ i)) :
    IsPrimFam fun n => LinearMap.pi fun i => Φ i n :=
  ⟨fun n z hz => funext fun i => (h i).bdry n z hz, fun n n' hn z hz => funext fun i => (h i).stab n n' hn z hz,
    fun d n z hz => funext fun i => (h i).psi d n z hz⟩

theorem sFewOf : SFewOf := by
  classical
  intro hT hP hC hU hD L F _ _ _ _ _ hL l c ν e hl ζ γ hlay hc hr S hS hinj
  choose 𝔡 h𝔡 using hS
  choose N y b hy hb hval using fun α : S => hC L F l c ν e ζ γ hlay hc α (𝔡 α α.2) (h𝔡 α α.2)
  have hl0 : (l : 𝓞 F) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hb0 : (l : 𝓞 F) * ∏ α, b α ≠ 0 := mul_ne_zero hl0 (Finset.prod_ne_zero_iff.2 fun α _ => hb α)
  let I : Type := {P : HeightOneSpectrum (𝓞 F) // (l : 𝓞 F) * ∏ α, b α ∉ P.asIdeal ∧
    Function.Surjective ((Ideal.Quotient.mk P.asIdeal).comp (algebraMap (𝓞 L) (𝓞 F)))}
  have main : ∀ P : I, ∃ Φ : ∀ n : ℕ, Ch (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) (2 * e + 2 + 1) →ₗ[ZMod (l ^ ν)]
      ZMod (l ^ ν), IsPrimFam Φ ∧ ∀ α α' : S, l ^ (2 * e + 2) • Φ _ (y α) = l ^ (2 * e + 2) • Φ _ (y α') →
        letI := P.1.isMaximal
        letI := Ideal.Quotient.field P.1.asIdeal
        ∃ s : (𝓞 F ⧸ P.1.asIdeal)ˣ, Res (Ideal.Quotient.mk P.1.asIdeal)
          (nrm γ ((1 + l ^ c) ^ (e + 1)) α ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))) *
            (nrm γ ((1 + l ^ c) ^ (e + 1)) α' ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))))⁻¹) (s ^ l ^ ν) := by
    rintro ⟨P, hPb, hPs⟩
    letI := P.isMaximal
    letI := Ideal.Quotient.field P.asIdeal
    haveI : Finite (𝓞 F ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
    have hlP : Ideal.Quotient.mk P.asIdeal (l : 𝓞 F) ≠ 0 := fun h =>
      hPb (Ideal.mul_mem_right _ _ (Ideal.Quotient.eq_zero_iff_mem.1 h))
    have hbP : ∀ α, Ideal.Quotient.mk P.asIdeal (b α) ≠ 0 := fun α h =>
      hPb (Ideal.mem_of_dvd _ ((Finset.dvd_prod_of_mem b (Finset.mem_univ α)).mul_left _)
        (Ideal.Quotient.eq_zero_iff_mem.1 h))
    have hz := prim_map (Ideal.Quotient.mk P.asIdeal) l ν hl.out (hlay.c_pos.trans hlay.c_le) hlP ζ hlay.prim
    obtain ⟨v, hv⟩ := exists_index (𝓞 F ⧸ P.asIdeal)ˣ (l ^ ν) (by rw [hz.eq_orderOf]; exact orderOf_dvd_natCard _)
    obtain ⟨θ, hθ, hθv⟩ := hT _ (l ^ ν) e _ hz v
    refine ⟨_, hP _ _ _ θ hθ (𝓞 L) ((Ideal.Quotient.mk P.asIdeal).comp (algebraMap (𝓞 L) (𝓞 F))), ?_⟩
    intro α α' hαα
    obtain ⟨u, hu, hu1⟩ := hval α _ _ hPs (hbP α) _ v θ hθ hθv
    obtain ⟨u', hu', hu1'⟩ := hval α' _ _ hPs (hbP α') _ v θ hθ hθv
    simp only [LinearMap.comp_apply] at hαα
    rw [hu1, hu1'] at hαα
    obtain ⟨x, hx⟩ := pe_dvd l c ν (2 * e + 3) (e + 1) hl.out hlay.c_pos hc (by omega)
    obtain ⟨s, hs⟩ := hv (u ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))) *
        (u' ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))))⁻¹) (by
      rw [map_mul, map_inv, map_pow, map_pow, mul_inv_eq_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_pow]
      simp only [nsmul_eq_mul, Nat.cast_pow] at hαα ⊢
      rw [pow_add, hx]
      linear_combination x * hαα)
    exact ⟨s, hs ▸ res_mul (res_pow hu _) (res_inv (res_pow hu' _))⟩
  choose Φ hΦ hsep using main
  let f : S → (I → ZMod (l ^ ν)) := fun α => l ^ (2 * e + 2) • (LinearMap.pi fun i => Φ i (N α)) (y α)
  have hf : Function.Injective f := by
    intro α α' h
    obtain ⟨δ, hδ⟩ := hD L F l ν hl.out ζ hlay.prim _ _ hb0 fun P _ hPb hPs =>
      hsep ⟨P, hPb, hPs⟩ α α' (congrFun h ⟨P, hPb, hPs⟩)
    exact Subtype.ext (hinj _ α.2 _ α'.2 ⟨δ, (mul_inv_eq_iff_eq_mul.1 hδ).trans (mul_comm _ _)⟩)
  have hcard := hU L hL (2 * e + 2) ⟨e + 1, by ring⟩ hr l ν (I → ZMod (l ^ ν)) _ (isPrimFam_pi Φ hΦ)
    (Finset.univ.image f) (by
      intro s hs
      obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hs
      exact ⟨N α, y α, hy α, rfl⟩)
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_coe,
    show 2 * (2 * e + 2 + 1) + 4 = 4 * e + 10 by ring] at hcard
  exact hcard

end LateralTheory.Q.SFewOfCut

end
end

