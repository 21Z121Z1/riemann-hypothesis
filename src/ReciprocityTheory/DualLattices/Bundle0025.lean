import ReciprocityTheory.DualLattices.Bundle0022
import ReciprocityTheory.DualLattices.Bundle0006
import ReciprocityTheory.DualLattices.Bundle0012
import ReciprocityTheory.DualLattices.HeightFunctionalStatementOfPairingProperties
import ReciprocityTheory.DualLattices.Bundle0023
import ReciprocityTheory.DualLattices.Bundle0014

-- bundled from ReciprocityTheory.DualLattices.EmbeddingSeparatingGroup
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem embeddingSeparatingGroup : EmbeddingSeparatingGroupStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U
  have hv : v.Integers R := hS.integers
  have hpv : v (algebraMap R C (p : R)) < 1 := hS.p_lt
  have hp : p.Prime := Fact.out

  have hvnat : ∀ n : ℕ, ¬ p ∣ n → v (algebraMap R C (n : R)) = 1 := by
    intro n hn
    by_contra hne
    have hlt : v (algebraMap R C (n : R)) < 1 := lt_of_le_of_ne (hv.map_le_one _) hne
    have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hn
    have h1 : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n) = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one]
    have h2 : (p : R) * (Nat.gcdA p n : R) + (n : R) * (Nat.gcdB p n : R) = 1 := by
      have := congrArg (fun z : ℤ => (z : R)) h1
      push_cast at this
      exact this
    have h3 : v (algebraMap R C ((p : R) * (Nat.gcdA p n : R) + (n : R) * (Nat.gcdB p n : R))) < 1 := by
      rw [map_add]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hv.map_le_one _)) hpv
      · rw [map_mul, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hv.map_le_one _)) hlt
    rw [h2, map_one, Valuation.map_one] at h3
    exact lt_irrefl _ h3
  have hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : R) := by
    intro n hn
    have hn0 : (n : C) ≠ 0 := by
      have : n ≠ 0 := fun h => hn (h ▸ dvd_zero p)
      exact_mod_cast this
    exact hv.isUnit_of_one (isUnit_iff_ne_zero.2 (by rw [map_natCast]; exact hn0)) (hvnat n hn)
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have heig : ∀ a j, (H.ρ a).map (algebraMap ℤ_[p] R) * U.εT j = U.sg j a • U.εT j := U.εT_eig
  have hres1 : FrobeniusGroupField.res hv 1 ≠ 0 := (FrobeniusGroupField.res_ne_zero hv 1).2 (by simp)

  have hex : ∀ t : Option (Fin U.m × Fin U.m × Bool), ∃ (b : O) (m : ℕ), 0 < m ∧ ¬ p ∣ m ∧
      H.ρ b ^ m = 1 ∧
      (match t with
        | none => ∀ j, U.εT j ≠ 0 → v (algebraMap R C (U.sg j b - 1)) = 1
        | some (i, k, e) => U.εT i ≠ 0 → U.εT k ≠ 0 → cond e (k ≠ U.φ i) (i ≠ k) →
            FrobeniusGroupField.res hv (U.sg k b) ≠ FrobeniusGroupField.res hv (U.sg i b) ^ p ^ e.toNat) := by
    intro t
    rcases t with _ | ⟨i, k, e⟩
    · obtain ⟨b, m, s, hm, hmp, hbm, hb⟩ := FrobeniusGroupField.seed p hv hpv H.ρ U.εT U.sg heig 0 2
      refine ⟨b, m, hm, hmp, hbm, ?_⟩
      intro j hj
      have h2 : FrobeniusGroupField.res hv (U.sg j 0 + ((2 : ℤ) : R)) = FrobeniusGroupField.res hv 2 := by simp
      have hr2 : FrobeniusGroupField.res hv 2 ≠ 0 := (FrobeniusGroupField.res_ne_zero hv 2).2 (by simpa using hvnat 2 hp2')
      have hfer : ∀ s : ℕ, FrobeniusGroupField.res hv 2 ^ p ^ s = FrobeniusGroupField.res hv 2 := by
        intro s
        induction s with
        | zero => simp
        | succ s ih =>
          have hf := FrobeniusGroupField.fermat p hv hpv (2 : ℤ_[p])
          rw [map_ofNat] at hf
          rw [pow_succ, pow_mul, ih, hf]
      have hbj := hb j hj (by rw [h2]; exact hr2)
      rw [h2, hfer] at hbj
      apply (FrobeniusGroupField.res_ne_zero hv _).1
      rw [map_sub, hbj, map_one]
      have h21 : FrobeniusGroupField.res hv 2 - 1 = FrobeniusGroupField.res hv 1 := by
        rw [← map_one (FrobeniusGroupField.res hv), ← map_sub]
        norm_num
      rw [h21]
      exact hres1
    · by_cases hall : U.εT i ≠ 0 ∧ U.εT k ≠ 0 ∧ cond e (k ≠ U.φ i) (i ≠ k)
      · obtain ⟨hi, hk, hik⟩ := hall
        have ha : ∃ a, FrobeniusGroupField.res hv (U.sg k a) ≠ FrobeniusGroupField.res hv (U.sg i a) ^ p ^ e.toNat := by
          cases e
          · simp only [cond_false, Bool.toNat_false, pow_zero, pow_one] at hik ⊢
            obtain ⟨a, ha⟩ := U.distinct i k hik
            refine ⟨a, fun heq => ?_⟩
            have h0 : FrobeniusGroupField.res hv (U.sg i a - U.sg k a) = 0 := by rw [map_sub, heq, sub_self]
            exact ((FrobeniusGroupField.res_ne_zero hv _).2 ha) h0
          · simp only [cond_true, Bool.toNat_true, pow_one] at hik ⊢
            obtain ⟨a, ha⟩ := U.distinct k (U.φ i) hik
            refine ⟨a, ?_⟩
            have hfr : FrobeniusGroupField.res hv (U.sg (U.φ i) a) = FrobeniusGroupField.res hv (U.sg i a) ^ p := by
              have h0 := (FrobeniusGroupField.res_eq_zero hv _).2 (U.frob i a)
              rw [map_sub, map_pow, sub_eq_zero] at h0
              exact h0
            rw [← hfr]
            intro heq
            have h0 : FrobeniusGroupField.res hv (U.sg k a - U.sg (U.φ i) a) = 0 := by rw [map_sub, heq, sub_self]
            exact ((FrobeniusGroupField.res_ne_zero hv _).2 ha) h0
        obtain ⟨a, ha⟩ := ha
        obtain ⟨b, m, hm, hmp, hbm, hb⟩ :=
          FrobeniusGroupField.pair p hp2 hv hpv H.ρ U.εT U.sg heig a e.toNat i k hi hk ha
        exact ⟨b, m, hm, hmp, hbm, fun _ _ _ => hb⟩
      · exact ⟨1, 1, one_pos, hp.not_dvd_one, by simp, fun hi hk hik => absurd ⟨hi, hk, hik⟩ hall⟩
  choose b m0 hm0 hmp0 hbm0 hQ using hex

  let m : Option (Fin U.m × Fin U.m × Bool) → ℕ := fun t => 2 * m0 t
  have hm : ∀ t, 0 < m t := fun t => by
    have := hm0 t
    show 0 < 2 * m0 t
    omega
  have hmp : ∀ t, ¬ p ∣ m t := fun t h => ((Nat.Prime.dvd_mul hp).1 h).elim hp2' (hmp0 t)
  have hbm : ∀ t, H.ρ (b t) ^ m t = 1 := fun t => by
    show H.ρ (b t) ^ (2 * m0 t) = 1
    rw [mul_comm, pow_mul, hbm0 t, one_pow]
  haveI : ∀ t, NeZero (m t) := fun t => ⟨(hm t).ne'⟩
  have hone : ∀ t, (1 : ZMod (m t)).val = 1 := fun t => by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_eq_of_lt (by have := hm0 t; show 1 < 2 * m0 t; omega)
  let G := ∀ t : Option (Fin U.m × Fin U.m × Bool), Multiplicative (ZMod (m t))
  let β : G → O := fun γ => ∏ t, b t ^ (Multiplicative.toAdd (γ t)).val
  have key : ∀ (s : Finset (Option (Fin U.m × Fin U.m × Bool)))
      (n : Option (Fin U.m × Fin U.m × Bool) → ℕ),
      H.ρ (∏ t ∈ s, b t ^ n t) = H.ρ (∏ t ∈ s, b t ^ (n t % m t)) := by
    intro s n
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, map_mul, ih, map_pow, map_pow,
      ← pow_eq_pow_mod _ (hbm a)]
  have hmul : ∀ γ γ' : G, H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ') := by
    intro γ γ'
    have e1 : β (γ * γ') = ∏ t, b t ^ (((Multiplicative.toAdd (γ t)).val +
        (Multiplicative.toAdd (γ' t)).val) % m t) := by
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [Pi.mul_apply, toAdd_mul, ZMod.val_add]
    have k2 := key Finset.univ
      (fun t => (Multiplicative.toAdd (γ t)).val + (Multiplicative.toAdd (γ' t)).val)
    beta_reduce at k2
    rw [e1, ← k2, ← map_mul]
    congr 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => pow_add _ _ _
  have h1 : H.ρ (β 1) = 1 := by
    have hb1 : β 1 = 1 := by
      refine (Finset.prod_congr rfl fun t _ => ?_).trans Finset.prod_const_one
      show b t ^ (Multiplicative.toAdd ((1 : G) t)).val = 1
      rw [Pi.one_apply, toAdd_one, ZMod.val_zero, pow_zero]
    rw [hb1, map_one]
  have hcard : IsUnit (Fintype.card G : R) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one fun t _ => ?_
    have hc : Fintype.card (Multiplicative (ZMod (m t))) = m t := by simp
    rw [hc]
    exact hunit _ (hmp t)
  let gen : Option (Fin U.m × Fin U.m × Bool) → G := fun t =>
    Pi.mulSingle (M := fun t => Multiplicative (ZMod (m t))) t (Multiplicative.ofAdd (1 : ZMod (m t)))
  have hgen : ∀ t, β (gen t) = b t := by
    intro t
    show ∏ u, b u ^ (Multiplicative.toAdd
      (Pi.mulSingle (M := fun t => Multiplicative (ZMod (m t))) t (Multiplicative.ofAdd (1 : ZMod (m t))) u)).val
      = b t
    rw [Finset.prod_eq_single t]
    · rw [Pi.mulSingle_eq_same, toAdd_ofAdd, hone, pow_one]
    · intro u _ hu
      rw [Pi.mulSingle_eq_of_ne hu, toAdd_one, ZMod.val_zero, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ t) h
  have hsep' : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      FrobeniusGroupField.res hv (U.sg k (b (some (i, k, false)))) ≠ FrobeniusGroupField.res hv (U.sg i (b (some (i, k, false)))) := by
    intro i k hi hk hik
    have hq := hQ (some (i, k, false)) hi hk (by simpa using hik)
    simpa using hq
  have hsepψ : ∀ j k, U.εT j ≠ 0 → U.εT k ≠ 0 → j ≠ k → ∃ γ : G, U.sg j (β γ) ≠ U.sg k (β γ) := by
    intro j k hj hk hjk
    refine ⟨gen (some (j, k, false)), ?_⟩
    rw [hgen]
    intro heq
    exact hsep' j k hj hk hjk (by rw [heq])
  refine ⟨G, inferInstance, inferInstance, β, hmul, h1, hcard, ?_, ?_, ?_⟩
  · intro i γ hi
    obtain ⟨j, hj, hψ⟩ := FrobeniusGroupField.proj p hv hpv hcard (fun γ => H.ρ (β γ)) hmul h1 U.εT U.εT_orth
      U.εT_sum (fun j γ => U.sg j (β γ)) (fun j γ => U.εT_eig (β γ) j)
      (fun j k hj hk hjk => hsepψ j k hj hk hjk) i hi
    have hjφ : j = U.φ i := by
      by_contra hne
      have hq := hQ (some (i, j, true)) hi hj (by simpa using hne)
      simp only [Bool.toNat_true, pow_one] at hq
      have h2 := hψ (gen (some (i, j, true)))
      simp only [hgen] at h2
      exact hq (by rw [h2, map_pow])
    rw [← hjφ]
    exact hψ γ
  · intro i k hi hk hik
    refine ⟨gen (some (i, k, false)), ?_⟩
    rw [hgen]
    apply (FrobeniusGroupField.res_ne_zero hv _).1
    rw [map_sub, sub_ne_zero]
    exact (hsep' i k hi hk hik).symm
  · intro i hi
    exact ⟨gen none, by rw [hgen]; exact hQ none i hi⟩

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.IsHeightUnique
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

lemma lhom_ext {R S : LAlg R₀} {f g : LHom R S} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (AlgHom.ext h)

lemma isHeight_map (hB1 : PairingPropertiesStatement B) {R S : LAlg R₀} (Dp : DualPair R) (Dq : DualPair S)
    (g : LHom R S) (f : LHom Dp.D Dq.D) (hfπ : ∀ x, Dq.π.1 (f.1 x) = g.1 (Dp.π.1 x))
    (hfσ : ∀ x, f.1 (Dp.σ.1 x) = Dq.σ.1 (g.1 x)) (hfη : f.1 Dp.η = Dq.η) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (H : B.IsHeight Dp N y h) :
    B.IsHeight Dq N (B.map g y) (g.1.toLinearMap ∘ₗ h) := by
  obtain ⟨-, -, -, -, -, -, hnat, -⟩ := hB1
  intro v
  obtain ⟨z, hz, hze⟩ := H v
  refine ⟨Units.map (f.1 : (Dp.D : Type u) →* Dq.D) z, ?_, ?_⟩
  · have h1 := hnat _ _ f N _ _ z hz
    have hf : ∀ a ∈ Dp.π.ker, f.1.toLinearMap a ∈ Dq.π.ker := by
      intro a ha
      rw [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
      change Dq.π.1 (f.1 a) = 0
      rw [hfπ, ha, map_zero]
    have e1 : B.map f (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) = B.tg Dq.π Dq.sqZero (v ⊗ₜ Dq.ηk) := by
      rw [← B.tg_nat Dp.π Dq.π Dp.sqZero Dq.sqZero f hf, LinearMap.lTensor_tmul]
      congr 2
      exact Subtype.ext hfη
    have e2 : B.map f (B.map Dp.σ y) = B.map Dq.σ (B.map g y) := by
      have hc : f.comp Dp.σ = Dq.σ.comp g := lhom_ext fun x => hfσ x
      rw [← B.map_comp, ← B.map_comp, hc]
    rw [e1, e2] at h1
    exact h1
  · simp only [Units.coe_map, MonoidHom.coe_coe, hze, map_add, map_one, map_mul, hfσ, hfη]
    rfl

lemma nsmul_tg_eta {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (hN : (N : (R : Type u)) = 0) (v : B.gg) :
    N • B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk) = 0 := by
  rw [← map_nsmul, ← tmul_smul]
  have : N • Dp.ηk = 0 := by
    apply Subtype.ext
    change N • Dp.η = 0
    rw [nsmul_eq_mul, ← map_natCast Dp.σ.1, hN, map_zero, zero_mul]
  rw [this, tmul_zero, map_zero]

lemma isHeight_mul_p (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N p : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : (N * p) • y = 0) (h : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp (N * p) y h) : B.IsHeight Dp N (p • y) h := by
  obtain ⟨-, -, -, -, -, -, -, hNp⟩ := hB1
  intro v
  obtain ⟨z, hz, hze⟩ := H v
  refine ⟨z, ?_, hze⟩
  have h1 := hNp _ N p _ _ z (B.nsmul_tg_eta Dp N hN v) (by rw [← map_nsmul, hy, map_zero]) hz
  rwa [← map_nsmul] at h1

lemma isHeight_unique (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (h h' : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y h') : h = h' :=
  ((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).unique H H'

lemma isHeight_exists (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) :
    ∃ h, B.IsHeight Dp N y h :=
  ((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).exists

lemma isHeight_add (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y y' : B.G R} {h h' : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y' h') : B.IsHeight Dp N (y + y') (h + h') :=
  (heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.2 y y' h h' H H'

lemma isHeight_zero (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) : B.IsHeight Dp N 0 0 := by
  obtain ⟨h, hh⟩ := B.isHeight_exists hB1 Dp N hN 0 (smul_zero N)
  have h2 := B.isHeight_add hB1 Dp N hN hh hh
  rw [add_zero] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ hh h2
  have h4 : h = 0 := by
    have := congrArg (fun k => k - h) h3
    simpa using this.symm
  rwa [h4] at hh

lemma isHeight_neg (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) : B.IsHeight Dp N (-y) (-h) := by
  obtain ⟨h', hh'⟩ := B.isHeight_exists hB1 Dp N hN (-y) (by rw [smul_neg, hy, neg_zero])
  have h2 := B.isHeight_add hB1 Dp N hN H hh'
  rw [add_neg_cancel] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ h2 (B.isHeight_zero hB1 Dp N hN)
  have h4 : h' = -h := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h3
  rwa [h4] at hh'

lemma isHeight_zsmul (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (k : ℤ) : B.IsHeight Dp N (k • y) (k • h) := by
  have hnat : ∀ m : ℕ, B.IsHeight Dp N (m • y) (m • h) := by
    intro m
    induction m with
    | zero => simpa using B.isHeight_zero hB1 Dp N hN
    | succ m ih => rw [succ_nsmul, succ_nsmul]; exact B.isHeight_add hB1 Dp N hN ih H
  rcases k with m | m
  · simpa using hnat m
  · have hm : N • ((m + 1) • y) = 0 := by rw [smul_comm, hy, smul_zero]
    have := B.isHeight_neg hB1 Dp N hN hm (hnat (m + 1))
    simpa [negSucc_zsmul] using this

lemma isHeight_sum (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {ι : Type} (s : Finset ι) (y : ι → B.G R) (hy : ∀ i, N • y i = 0)
    (h : ι → B.gg →ₗ[R₀] (R : Type u)) (H : ∀ i, B.IsHeight Dp N (y i) (h i)) :
    B.IsHeight Dp N (∑ i ∈ s, y i) (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using B.isHeight_zero hB1 Dp N hN
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact B.isHeight_add hB1 Dp N hN (H a) ih

end BX

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.RestrictHopfOrderLength
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.PullbackHopfOrder

private theorem red_surj {p : ℕ} [Fact p.Prime] {g : ℕ} (n : Nb p g) : ∃ t, red p g t = n := by
  refine ⟨fun i => ((n i).val : ℤ_[p]), funext fun i => ?_⟩
  simp [red]

private theorem red_mulVec {p : ℕ} [Fact p.Prime] {g : ℕ} (M : Matrix (Ix g) (Ix g) ℤ_[p])
    (t : TT p g) : red p g (M *ᵥ t) = M.map PadicInt.toZMod *ᵥ red p g t := by
  funext i
  simp [red, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem restrict_hopfOrder_length : RestrictedHopfOrderStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H a ha r Bw hrange hkerB d hd
  have hE : H.ρ a * H.ρ a = H.ρ a := by rw [← map_mul, ha]
  have hcol : ∀ j : Ix g, ∃ k : Fin r → ℤ_[p], Bw *ᵥ k = H.ρ a *ᵥ Pi.single j 1 := by
    intro j
    have hm : H.ρ a *ᵥ Pi.single j 1 ∈ LinearMap.range (Matrix.mulVecLin Bw) := by
      rw [hrange]
      exact ⟨Pi.single j 1, rfl⟩
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, hk⟩
  choose kk hkk using hcol
  let K : Matrix (Fin r) (Ix g) ℤ_[p] := Matrix.of fun i j => kk j i
  have hBK : Bw * K = H.ρ a := by
    ext i j
    have h1 : (Bw * K) i j = (Bw *ᵥ kk j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, K]
    rw [h1, hkk j]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hKB : K * Bw = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    apply LinearMap.ker_eq_bot.mp hkerB
    show Bw *ᵥ ((K * Bw) *ᵥ x) = Bw *ᵥ x
    obtain ⟨y, hy⟩ : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin (H.ρ a)) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBK, ← hy]
    show H.ρ a *ᵥ (H.ρ a *ᵥ y) = H.ρ a *ᵥ y
    rw [Matrix.mulVec_mulVec, hE]
  let ψ := psiW Bw
  let χ : Nb p g →+ (Fin r → ZMod p) := (Matrix.mulVecLin (K.map PadicInt.toZMod)).toAddMonoidHom
  have hχψ : ∀ x, χ (ψ x) = x := by
    intro x
    show K.map PadicInt.toZMod *ᵥ (Bw.map PadicInt.toZMod *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hKB, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hred : ∀ t, ψ (χ (red p g t)) = red p g (H.ρ a *ᵥ t) := by
    intro t
    show Bw.map PadicInt.toZMod *ᵥ (K.map PadicInt.toZMod *ᵥ red p g t) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hBK, ← red_mulVec]
  have hA : ∀ f ∈ H.AA.carrier, (fun n => f (ψ (χ n))) ∈ H.AA.carrier := by
    intro f hf
    obtain ⟨f', hf', hff⟩ := H.h3 a f hf
    convert hf' using 1
    funext n
    obtain ⟨t, rfl⟩ := red_surj n
    rw [hff, hred]
  have hinj : Function.Injective ψ := fun x y h => by rw [← hχψ x, ← hχψ y, h]
  have hEE : H.ρL a * H.ρL a = H.ρL a := by rw [← map_mul, ha]
  let e := hd.some
  let Q1 : Matrix (Fin g) (Fin d) R :=
    LinearMap.toMatrix' ((LinearMap.range (H.ρL a).mulVecLin).subtype ∘ₗ e.symm.toLinearMap)
  let Q2 : Matrix (Fin d) (Fin g) R :=
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ (H.ρL a).mulVecLin.rangeRestrict)
  have hQ12 : Q1 * Q2 = H.ρL a := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun x => ?_
    simp [Matrix.toLin'_apply]
  have hQ21 : Q2 * Q1 = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    refine LinearMap.ext fun y => ?_
    have hz : (H.ρL a).mulVecLin.rangeRestrict ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) =
        e.symm y := by
      apply Subtype.ext
      obtain ⟨w, hw⟩ := (e.symm y).2
      show H.ρL a *ᵥ ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) = e.symm y
      rw [← hw]
      show H.ρL a *ᵥ (H.ρL a *ᵥ w) = H.ρL a *ᵥ w
      rw [Matrix.mulVec_mulVec, hEE]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, LinearMap.id_apply]
    rw [hz, LinearEquiv.apply_symm_apply]
  have hF : Q2ᵀ * Q1ᵀ = (H.ρL a)ᵀ := by rw [← Matrix.transpose_mul, hQ12]
  have h21 : Q1ᵀ * Q2ᵀ = 1 := by rw [← Matrix.transpose_mul, hQ21, Matrix.transpose_one]
  obtain ⟨eO⟩ := omega_pull p ψ χ hχψ H.AA.carrier hA H.φ H.cotangent_surjective H.cotangent_ker_eq (H.ρL a)ᵀ Q2ᵀ Q1ᵀ hF h21
    (fun f f' l hff hl => H.cotangent_linear a f f' l (fun t => by rw [hff, hred]) hl)
  refine ⟨pullHopf ψ H.AA (isLat_pull v hS.integers ψ hinj H.AA), pullHopf_carrier _ _ _, ?_⟩
  rw [pullHopf_carrier]
  exact ⟨d, fun _ => (p : R), ⟨eO.trans (qPi p d)⟩, by simp [Finset.prod_const]⟩

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ThmAFull
section
noncomputable section

open TensorProduct Matrix

namespace ReciprocityTheory.PGsh

variable {R₀ : Type} [CommRing R₀]

private lemma ev_expand (B : BX R₀) {O : LAlg R₀} {g : ℕ} (gb : Module.Basis (Fin g) R₀ B.gg)
    (h : B.gg →ₗ[R₀] (O : Type)) (b : B.gg ⊗[R₀] (O : Type)) :
    B.ev h b = ∑ a, h (gb a) * B.ev (Algebra.linearMap R₀ (O : Type) ∘ₗ gb.coord a) b := by
  induction b using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul x r =>
    simp only [BX.ev, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Algebra.linearMap_apply, Module.Basis.coord_apply]
    conv_lhs => rw [← gb.sum_repr x]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Algebra.smul_def]
    ring
  | add a b ha hb =>
    simp only [BX.ev, map_add] at *
    rw [ha, hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

private lemma stdJ_form {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  simp [Matrix.mul_apply, stdJ, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem thmAFull (B : BX R₀) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) {p : ℕ}
    (Tw : ATower R₀ p) : ThmAFullStatement B Tw := by
  intro _ Dp g gb τ E ht bt hc hEt hdiag hdet hpair hheight hbt
  have h4 := b4 B hB1 hB3 Tw Dp (Fin g ⊕ Fin g) τ E ht bt hpair hheight hbt
  have hJ : (thmAPhi B gb ht bt)ᵀ * stdJ (Tw.O : Type) g * thmAPhi B gb ht bt = Tw.c • E := by
    ext i j
    rw [stdJ_form, Matrix.smul_apply, smul_eq_mul, h4 i j, ev_expand B gb (ht j),
      ev_expand B gb (ht i), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [thmAPhi, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    ring
  exact ⟨hJ, a1 (Tw.O : Type) g E _ Tw.c hEt hdiag hdet hc hJ⟩

end ReciprocityTheory.PGsh
end
end

