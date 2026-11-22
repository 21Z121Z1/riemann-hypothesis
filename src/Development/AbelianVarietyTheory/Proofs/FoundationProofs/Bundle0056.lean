import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductEqOddThetaProductQuotient
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg.ThQuot

theorem ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

theorem ee_nat_mul (n : ℕ) (z : ℂ) : ee ((n : ℂ) * z) = ee z ^ n := by
  unfold ee
  rw [← Complex.exp_nat_mul]; congr 1; ring

theorem ee_neg (z : ℂ) : ee (-z) = (ee z)⁻¹ := by
  unfold ee
  rw [← Complex.exp_neg]; congr 1; ring

theorem norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  unfold ee
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  have h1 := τ.im_pos
  have h2 := Real.pi_pos
  have : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  have : 0 < 2 * Real.pi * τ.im := by positivity
  linarith

theorem multipliable_one_sub {q : ℂ} (hq : ‖q‖ < 1) (t : ℂ) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + 1) * t) := by
  have h : Summable (fun n : ℕ => -(q ^ (n + 1) * t)) := by
    have h0 := (summable_geometric_of_norm_lt_one hq).mul_right (q * t)
    refine h0.neg.congr fun n => ?_
    ring
  simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable h

theorem hasProd_pow_div {f g : ℕ → ℂ} {a b : ℂ} (hf : HasProd f a) (hg : HasProd g b) (hb : b ≠ 0) (k : ℕ) :
    HasProd (fun n => f n ^ k / g n) (a ^ k / b) := by
  unfold HasProd at *
  simp only [Finset.prod_div_distrib, Finset.prod_pow]
  exact (hf.pow k).div hg hb

theorem twelve_dvd {c : ℕ} (h1 : 1 < c) (h : Nat.Coprime c 6) : ∃ k, c ^ 2 = 12 * k + 1 := by
  have h2 : ¬ 2 ∣ c := fun hd => by
    have := Nat.Coprime.coprime_dvd_left hd h
    norm_num at this
  have h3 : ¬ 3 ∣ c := fun hd => by
    have := Nat.Coprime.coprime_dvd_left hd h
    norm_num at this
  obtain ⟨m, hm⟩ : ∃ m, c = 6 * m + 1 ∨ c = 6 * m + 5 := ⟨c / 6, by omega⟩
  rcases hm with rfl | rfl
  · exact ⟨3 * m ^ 2 + m, by ring⟩
  · exact ⟨3 * m ^ 2 + 5 * m + 2, by ring⟩

theorem cth_eq_th_quot : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → th ((c : ℂ) * z) τ ≠ 0 →
    cth c (ee (τ : ℂ)) (ee z) = (-1) ^ (c * (c - 1) / 2) * th z τ ^ (c ^ 2) / th ((c : ℂ) * z) τ := by
  intro c τ z h1 hc hne
  obtain ⟨k, hk⟩ := twelve_dvd h1 hc
  have hodd : Odd c := by
    have : Odd (c ^ 2) := ⟨6 * k, by omega⟩
    exact (Nat.odd_pow_iff (by norm_num)).mp this
  obtain ⟨j, hj⟩ := hodd
  have hq := norm_ee_lt_one τ
  set s := ee (z / 2) with hs
  set u := ee ((τ : ℂ) / 12) with hu
  have hs0 : s ≠ 0 := ee_ne_zero _
  have hu0 : u ≠ 0 := ee_ne_zero _
  have ht : ee z = s ^ 2 := by
    rw [hs, ← ee_nat_mul]; congr 1; push_cast; ring
  have hqu : ee (τ : ℂ) = u ^ 12 := by
    rw [hu, ← ee_nat_mul]; congr 1; push_cast; ring
  have e1 : ee (-z / 2) = s⁻¹ := by rw [neg_div, ee_neg]
  have e2 : ee ((c : ℂ) * z / 2) = s ^ c := by rw [mul_div_assoc, ee_nat_mul]
  have e3 : ee (-((c : ℂ) * z) / 2) = (s ^ c)⁻¹ := by rw [neg_div, ee_neg, e2]
  have e4 : ee ((c : ℂ) * z) = ee z ^ c := ee_nat_mul c z
  unfold th at hne ⊢
  unfold cth
  rw [e2, e3, e4] at hne ⊢
  rw [e1, ← hs, ← hu] at *
  have mf := ((multipliable_one_sub hq (ee z)).mul (multipliable_one_sub hq (ee z)⁻¹)).hasProd
  have mg := ((multipliable_one_sub hq (ee z ^ c)).mul (multipliable_one_sub hq (ee z ^ c)⁻¹)).hasProd
  set A := ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) with hA
  set B := ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z ^ c) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z ^ c)⁻¹) with hB
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hne
  have hd : s ^ c - (s ^ c)⁻¹ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hP : ∏' m : ℕ, cthFac c (ee (τ : ℂ)) (ee z) (m + 1) = A ^ (c ^ 2) / B := by
    have := hasProd_pow_div mf mg hB0 (c ^ 2)
    refine (HasProd.tprod_eq ?_)
    simpa only [cthFac, mul_pow] using this
  rw [hP]
  have x1 : (c ^ 2 - 1) / 12 = k := by omega
  have x2 : c * (c - 1) / 2 = c * j := by
    have : c * (c - 1) = 2 * (c * j) := by
      have : c - 1 = 2 * j := by omega
      rw [this]; ring
    omega
  have x3 : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = -((c * j : ℕ) : ℤ) := by
    have : (c : ℤ) - (c : ℤ) ^ 2 = 2 * (-((c * j : ℕ) : ℤ)) := by
      subst hj; push_cast; ring
    rw [this]; omega
  rw [x1, x2, x3, zpow_neg, zpow_natCast, ht, hqu]
  have hsc : s ^ c ≠ 0 := pow_ne_zero _ hs0
  have y1 : s ^ c - (s ^ c)⁻¹ = -(1 - (s ^ 2) ^ c) / s ^ c := by
    field_simp; ring
  have y2 : s - s⁻¹ = -(1 - s ^ 2) / s := by field_simp; ring
  have hd' : 1 - (s ^ 2) ^ c ≠ 0 := by
    intro h; apply hd; rw [y1, h]; simp
  have hc2 : Odd (c ^ 2) := ⟨6 * k, by omega⟩
  have y3 : s ^ (c ^ 2) = s ^ c * (s ^ 2) ^ (c * j) := by
    rw [← pow_mul, ← pow_add]; congr 1; subst hj; ring
  have y4 : u ^ (c ^ 2) = u * (u ^ 12) ^ k := by rw [hk, ← pow_mul]; ring
  have y5 : ((-1 : ℂ)) ^ (c * j) * (-1) ^ (c * j) = 1 := by rw [← mul_pow]; simp
  rw [y1, y2, mul_pow, mul_pow, div_pow, hc2.neg_pow, y3, y4, neg_pow (s ^ 2)]
  have hS : (s ^ 2) ^ (c * j) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hs0)
  generalize (s ^ 2) ^ (c * j) = S at *
  generalize (1 - (s ^ 2) ^ c) = D at *
  generalize (1 - s ^ 2) ^ (c ^ 2) = E at *
  generalize s ^ c = T at *
  generalize A ^ (c ^ 2) = A' at *
  generalize (u ^ 12) ^ k = U at *
  generalize ((-1 : ℂ)) ^ (c * j) = ε at *
  have hε : ε ≠ 0 := left_ne_zero_of_mul (y5 ▸ one_ne_zero)
  have hi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right y5
  rw [mul_inv, hi]
  field_simp

end GlobalTheory.Sieg.ThQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanHeisenbergTranslatesVacuumEqTop
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem span_translates_vacuum : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → ∀ e : M, (∀ v, Fixes W A v → ∃ c : ℂ, v = c • e) → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ (Set.range fun x => W x e) = ⊤ := by
  intro R X M _ _ _ _ _ σ w γ W h A hA e he hsm
  rw [eq_top_iff]
  intro v _
  obtain ⟨T, hT, hv⟩ := hsm v
  let S : Submodule R X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [h.add_left, ha.2 t ht, hb.2 t ht, mul_one]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => h.zero_left t⟩
      smul_mem' := fun r a ha => ⟨A.smul_mem r ha.1, fun t ht => by
        rw [h.adj]; exact ha.2 _ (T.smul_mem _ ht)⟩ }
  have hSm : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  have hSv : Fixes W S v := fun a ha => hv a ha.1 ha.2
  have hSt : ∀ t ∈ T, Fixes W S (W (-t) v) := by
    intro t ht a ha
    rw [h.comm, ha.2 _ (T.neg_mem ht), one_smul, hSv a ha]
  obtain ⟨h1, -, -⟩ := perfect_pairing_quotients h S.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup T.toAddSubgroup
    (fun a ha => ⟨fun hs => hs.2, fun hs => ⟨ha, hs⟩⟩)
    (fun t _ => ⟨fun ht a ha => h.iso hA ha ht,
      fun ht => (hA t).2 fun a ha => h.swap_eq_one (ht a ha)⟩) hT
  have hn : idx S A ≠ 0 := by
    unfold idx
    rw [h1]
    exact hT
  obtain ⟨-, -, h2⟩ := perfect_pairing_quotients h A.toAddSubgroup T.toAddSubgroup
    S.toAddSubgroup A.toAddSubgroup
    (fun t _ => hA t)
    (fun a ha => ⟨fun hs t ht => h.swap_eq_one (hs.2 t ht),
      fun hs => ⟨ha, fun t ht => h.swap_eq_one (hs t ht)⟩⟩) hn
  obtain ⟨t1, t2, -⟩ := sumOp_transversal h S A hA
  obtain ⟨⟨m, f, hf, hu⟩, hfix, -⟩ := t2 hn
  have hg : ∀ t ∈ T, ∑ i, γ t (f i) • W (f i) v ∈ Submodule.span ℂ (Set.range fun x => W x e) := by
    intro t ht
    obtain ⟨c, hc⟩ := he _ (hfix _ (hSt t ht))
    rw [(t1 _ (hSt t ht) _ f hf hu).1] at hc
    have h3 := congrArg (W t) hc
    rw [map_sum, map_smul] at h3
    have h4 : ∀ i, W t (W (f i) (W (-t) v)) = γ (w • t) (-t) • (γ t (f i) • W (f i) v) := by
      intro i
      rw [h.comm, h.comp t (-t), add_neg_cancel, h.zero, map_smul, smul_comm]
    rw [Finset.sum_congr rfl fun i _ => h4 i, ← Finset.smul_sum] at h3
    rw [← Submodule.smul_mem_iff _ (h.ne_zero (w • t) (-t)), h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  haveI : Finite (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hT
  letI := Fintype.ofFinite (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup)
  have h5 := Submodule.sum_mem (Submodule.span ℂ (Set.range fun x => W x e))
    (t := (Finset.univ : Finset
      (T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup)))
    (fun q _ => hg _ (Quotient.out q : T.toAddSubgroup).2)
  rw [Finset.sum_comm] at h5
  obtain ⟨i₀, hi₀, hi⟩ := hu 0 A.zero_mem
  simp only [zero_sub, neg_mem_iff] at hi₀ hi
  have h6 : ∀ i, ∑ q : T.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf T.toAddSubgroup,
      γ ((Quotient.out q : T.toAddSubgroup) : X) (f i) • W (f i) v
      = if i = i₀ then (idx A T : ℂ) • v else 0 := by
    intro i
    rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, h2 _ (hf i)]
    by_cases hii : i = i₀
    · subst hii
      rw [if_pos rfl, if_pos (show f i ∈ S.toAddSubgroup from hi₀), hSv _ hi₀]
      rfl
    · rw [if_neg hii, if_neg (fun hh : f i ∈ S.toAddSubgroup => hii (hi i hh)), zero_smul]
  rw [Finset.sum_congr rfl fun i _ => h6 i, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h5
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hT)).1 h5

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumGl2FirstColumnUnitSetSuccFibre
section
noncomputable section

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

theorem glFibre_val_map {p n : ℕ} [NeZero p] (x : ZMod (p ^ (n + 1))) :
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val = x.val % p ^ n := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

theorem glFibre_isUnit_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ n)) :
    IsUnit x ↔ ¬ p ∣ x.val := by
  have hp : p.Prime := Fact.out
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
    hp.coprime_iff_not_dvd]

theorem glFibre_dvd_map_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ (n + 1))) :
    p ∣ (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val ↔ p ∣ x.val := by
  rw [glFibre_val_map, Nat.dvd_mod_iff (dvd_pow_self p (by omega))]

theorem sum_unitSet_succ_fibre : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (K : Type) [CommRing K] (G : GL (Fin 2) (ZMod (p ^ n)) → K) (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K), 1 ≤ n → ∑ γ ∈ unitSet p (n + 1), G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) = ∑ γ ∈ unitSet p n, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  intro p _ n K _ G Φ hn
  set ρ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) with hρ
  have hent : ∀ (γ : GL (Fin 2) (ZMod (p ^ (n + 1)))) (a b : Fin 2),
      (Matrix.GeneralLinearGroup.map ρ γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) a b =
        ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) a b) := fun _ _ _ => rfl
  have hmaps : ∀ γ ∈ unitSet p (n + 1), Matrix.GeneralLinearGroup.map ρ γ ∈ unitSet p n := by
    intro γ hγ
    simp only [unitSet, mem_filter, mem_univ, true_and] at hγ ⊢
    rw [hent, hent, hρ, glFibre_dvd_map_iff hn, glFibre_dvd_map_iff hn]
    exact hγ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [Finset.sum_congr rfl (fun γ hγ => by rw [(mem_filter.mp hγ).2]), ← Finset.mul_sum]
  congr 1
  simp only [← Finset.sum_product']
  refine Finset.sum_bij (fun γ _ => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1))) ?_ ?_ ?_ ?_
  · intro γ hγ
    obtain ⟨_, hγg⟩ := mem_filter.mp hγ
    simp only [mem_product, mem_filter, mem_univ, true_and, ← hγg, hent, and_self]
  · intro γ _ δ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    ext a b
    fin_cases a <;> fin_cases b
    exacts [h1, h2, h3, h4]
  · rintro ⟨a, b, c, d⟩ hb
    simp only [mem_product, mem_filter, mem_univ, true_and] at hb
    obtain ⟨ha, hb', hc, hd⟩ := hb
    let B : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))) := !![a, b; c, d]
    have hBm : ρ.mapMatrix B = (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) := by
      ext i j
      fin_cases i <;> fin_cases j
      exacts [ha, hb', hc, hd]
    have hdet : IsUnit B.det := by
      have h1 : IsUnit (ρ B.det) := by
        rw [RingHom.map_det, hBm]; exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      rw [glFibre_isUnit_iff hn, hρ, glFibre_dvd_map_iff hn] at h1
      exact (glFibre_isUnit_iff (by omega) _).mpr h1
    obtain ⟨γ, hγ⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr hdet
    have hmap : Matrix.GeneralLinearGroup.map ρ γ = g := by
      apply Units.ext
      rw [← hBm, ← hγ]; rfl
    refine ⟨γ, ?_, ?_⟩
    · refine mem_filter.mpr ⟨?_, hmap⟩
      simp only [unitSet, mem_filter, mem_univ, true_and] at hg ⊢
      rw [← glFibre_dvd_map_iff hn, ← glFibre_dvd_map_iff hn, ← hρ, ← hent, ← hent, hmap]
      exact hg
    · simp only [hγ, B]
      rfl
  · intro γ _
    rfl

end GlobalTheory.KummerEisensteinGalois
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeMulCardOddFrameWeightsDvdThreeStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.three_mul_card_oddFrame_weights_dvd_three : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (evM s w F ρ).det ≠ 0 → 3 * (Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card = r := by
  first | exact @GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd | exact GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd | (intros; apply GlobalTheory.OddFrame.ThirdDiv.three_mul_card_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisFixedEqDivLevelElements
section
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.FixFrac

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def fracField (T : Tower p Ω) : Subfield Ω where
  carrier := {x | ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b}
  zero_mem' := ⟨0, 0, zero_mem _, 1, one_mem _, one_ne_zero, by simp⟩
  one_mem' := ⟨0, 1, one_mem _, 1, one_mem _, one_ne_zero, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, a, ha, b, hb, hb0, rfl⟩ ⟨m', c, hc, d, hd, hd0, rfl⟩
    have h1 := Lev_mono T (le_max_left m m')
    have h2 := Lev_mono T (le_max_right m m')
    refine ⟨max m m', a * d + b * c, add_mem (mul_mem (h1 ha) (h2 hd)) (mul_mem (h1 hb) (h2 hc)),
      b * d, mul_mem (h1 hb) (h2 hd), mul_ne_zero hb0 hd0, ?_⟩
    rw [div_add_div _ _ hb0 hd0]
  mul_mem' := by
    rintro _ _ ⟨m, a, ha, b, hb, hb0, rfl⟩ ⟨m', c, hc, d, hd, hd0, rfl⟩
    have h1 := Lev_mono T (le_max_left m m')
    have h2 := Lev_mono T (le_max_right m m')
    exact ⟨max m m', a * c, mul_mem (h1 ha) (h2 hc), b * d, mul_mem (h1 hb) (h2 hd),
      mul_ne_zero hb0 hd0, div_mul_div_comm a b c d⟩
  neg_mem' := by
    rintro _ ⟨m, a, ha, b, hb, hb0, rfl⟩
    exact ⟨m, -a, neg_mem ha, b, hb, hb0, (neg_div b a).symm⟩
  inv_mem' := by
    rintro _ ⟨m, a, ha, b, hb, hb0, rfl⟩
    by_cases ha0 : a = 0
    · exact ⟨0, 0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [ha0]⟩
    · exact ⟨m, b, hb, a, ha, ha0, inv_div a b⟩

theorem mem_fracField_of_mem (T : Tower p Ω) {m : ℕ} {a : Ω} (ha : a ∈ Lev T m) :
    a ∈ fracField T :=
  ⟨m, a, ha, 1, one_mem _, one_ne_zero, (div_one a).symm⟩

theorem fixed_eq_div : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (x : Ω), (∀ h ∈ Hinf T, h x = x) →
    ∃ m : ℕ, ∃ a ∈ Lev T m, ∃ b ∈ Lev T m, b ≠ 0 ∧ x = a / b := by
  intro p _ Ω _ _ hC T x hx
  haveI : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hC.inj
  letI : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hC.alg
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  haveI : IsAlgClosed Ω := hC.clo
  haveI : IsAlgClosure (FractionRing (O0 p)) Ω := ⟨hC.clo, inferInstance⟩
  haveI : CharZero Ω := Basic.charZero_of_isClo hC
  haveI : CharZero (FractionRing (O0 p)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  haveI : IsGalois (FractionRing (O0 p)) Ω := IsAlgClosure.isGalois _ _
  let E := IntermediateField.adjoin (FractionRing (O0 p)) (Set.range T.ζ ∪ Set.range T.qq)
  have hxE : x ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hfix : ∀ y ∈ E, σ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ
    have hmem : σ.restrictScalars (O0 p) ∈ Hinf T := by
      rw [mem_Hinf]
      intro n
      exact ⟨hfix _ (IntermediateField.subset_adjoin _ _ (Or.inl ⟨n, rfl⟩)),
        hfix _ (IntermediateField.subset_adjoin _ _ (Or.inr ⟨n, rfl⟩))⟩
    exact hx _ hmem
  have halg : ∀ c : FractionRing (O0 p), algebraMap (FractionRing (O0 p)) Ω c ∈ fracField T := by
    intro c
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (O0 p)) c
    dsimp only
    rw [IsFractionRing.mk'_eq_div, map_div₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    exact ⟨0, _, Subalgebra.algebraMap_mem _ a, _, Subalgebra.algebraMap_mem _ (s : O0 p),
      (map_ne_zero_iff _ hC.inj).2 (nonZeroDivisors.ne_zero s.2), rfl⟩
  have hle : E ≤ (fracField T).toIntermediateField halg := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · exact mem_fracField_of_mem T (zeta_mem_Lev T n)
    · exact mem_fracField_of_mem T (qq_mem_Lev T n)
  exact hle hxE

end GlobalTheory.FixFrac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGnExponentsKummerCochains
section
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumExpo

theorem exponents : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n m : ℕ), 2 * n ≤ m → ∀ lz lq : Gal p Ω → ZMod (p ^ n),
  IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq → ∀ g ∈ Gn T n,
  ∃ (i j : ℕ) (s t : ℤ), g (T.ζ m) = T.ζ m ^ i ∧ g (T.qq m) = T.ζ m ^ j * T.qq m ∧
    (i : ℤ) = 1 + p ^ n * ((lz g).val : ℤ) + p ^ (2 * n) * s ∧ (j : ℤ) = p ^ n * ((lq g).val : ℤ) + p ^ (2 * n) * t := by
  intro p _ Ω _ _ T n m hm lz lq hz hq g hg
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm

  have h1 : (g (T.ζ (2 * n + k))) ^ (p ^ (2 * n + k)) = 1 := by
    rw [← map_pow, (T.prim _).pow_eq_one, map_one]
  obtain ⟨i, -, hi⟩ := (T.prim _).eq_pow_of_pow_eq_one h1
  have hqne := qq_ne T (2 * n + k)
  have h2 : (g (T.qq (2 * n + k)) / T.qq (2 * n + k)) ^ (p ^ (2 * n + k)) = 1 := by
    rw [div_pow, ← map_pow, kummerTower_qq_pow_level_eq_q, AlgEquiv.commutes, ← kummerTower_qq_pow_level_eq_q T (2 * n + k),
      div_self (pow_ne_zero _ hqne)]
  obtain ⟨j, -, hj⟩ := (T.prim _).eq_pow_of_pow_eq_one h2
  have hj' : g (T.qq (2 * n + k)) = T.ζ (2 * n + k) ^ j * T.qq (2 * n + k) := by
    rw [hj, div_mul_cancel₀ _ hqne]

  have ez : T.ζ (2 * n + k) ^ (p ^ k) = T.ζ (2 * n) := zeta_pow T (2 * n) k
  have eq' : T.qq (2 * n + k) ^ (p ^ k) = T.qq (2 * n) := qq_pow T (2 * n) k
  have ezn : T.ζ (2 * n) ^ (p ^ n) = T.ζ n := by
    have := zeta_pow T n n
    rwa [← two_mul] at this
  have gz : g (T.ζ (2 * n)) = T.ζ (2 * n) ^ i := by
    rw [← ez, map_pow, ← hi, ← pow_mul, ← pow_mul, Nat.mul_comm i]
  have gq : g (T.qq (2 * n)) = T.ζ (2 * n) ^ j * T.qq (2 * n) := by
    rw [← eq', map_pow, hj', mul_pow, ← pow_mul, mul_comm j, pow_mul, ez]
  have kz := hz g hg
  have kq := hq g hg
  rw [gz, ← ezn, ← pow_mul, ← pow_succ] at kz
  rw [gq, ← ezn, ← pow_mul] at kq
  have kq' := mul_right_cancel₀ (qq_ne T (2 * n)) kq
  rw [GlobalTheory.K5.Basic.zeta_pow_eq_iff] at kz kq'
  rw [Nat.modEq_iff_dvd] at kz kq'
  obtain ⟨s, hs⟩ := kz
  obtain ⟨t, ht⟩ := kq'
  refine ⟨i, j, -s, -t, hi.symm, hj', ?_, ?_⟩
  · push_cast at hs ⊢
    linear_combination -hs
  · push_cast at ht ⊢
    linear_combination -ht

end GlobalTheory.KumExpo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicCompleteStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_integers_adic_complete : ∀ (p : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : O0 p)}) (O0 p) := by
  first | exact @GlobalTheory.K5.o0_isAdicComplete_span_p | exact GlobalTheory.K5.o0_isAdicComplete_span_p | (intros; apply GlobalTheory.K5.o0_isAdicComplete_span_p <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperMulEqMulDiamondDiagGamma1InterGamma0Statement
section
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upper_mul_eq_mul_diamond_diag_gamma1InterGamma0 : ∀ (N l q j : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → j < q → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 → ∃ γ' ∈ GlobalTheory.Hk.lev N l, !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * (mat σ * dg q 1) := by
  first | exact @GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag | exact GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag | (intros; apply GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperTriangularMulEqMulUpperTriangularGamma1InteStatement
section
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperTriangular_mul_eq_mul_upperTriangular_gamma1InterGamma0 : ∀ (N l q j : ℕ) (γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → j < q → γ ∈ GlobalTheory.Hk.lev N l → ¬ (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 → ∃ j' < q, ∃ γ' ∈ GlobalTheory.Hk.lev N l, !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * !![(1 : ℤ), (j' : ℤ); 0, (q : ℤ)] := by
  first | exact @GlobalTheory.Hk.tinv_fin_fin | exact GlobalTheory.Hk.tinv_fin_fin | (intros; apply GlobalTheory.Hk.tinv_fin_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationAddPowSubLeStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ y β : L, v ((y + β) ^ p - y ^ p - β ^ p) ≤ v (p : L) * v β * (max (v y) (v β)) ^ (p - 1) := by
  first | exact @GlobalTheory.AlmostEt.valuation_add_pow_sub_le | exact GlobalTheory.AlmostEt.valuation_add_pow_sub_le | (intros; apply GlobalTheory.AlmostEt.valuation_add_pow_sub_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfPowEqSpanStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span : ∀ (E Ω R : Type) [Field E] [Field Ω] [Algebra E Ω] [CommRing R] [Algebra R E] (B : ValuationSubring Ω) (J : Submodule R E) (N : ℕ), 0 < N → (∀ x : R, algebraMap E Ω (algebraMap R E x) ∈ B) → ∀ w : E, w ≠ 0 → (J ^ N = Submodule.span R {w}) → ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / c ^ N)) = 1 := by
  first | exact @GlobalTheory.valuation_eq_one_of_pow_eq_span | exact GlobalTheory.valuation_eq_one_of_pow_eq_span | (intros; apply GlobalTheory.valuation_eq_one_of_pow_eq_span <;> assumption)
end

