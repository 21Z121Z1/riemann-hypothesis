import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelEmbeddingInjectiveRangeAdjoinRoots
section
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.K5.LevEmb

theorem emb_inj_range : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ ι : On p m →ₐ[O0 p] Ω, IsEmb T m ι →
    Function.Injective ι ∧ ι.range = Lev T m := by
  intro p _ Ω _ _ hΩ T m hm ι hι
  obtain ⟨b, hb⟩ := GlobalTheory.K5.OnFree.on_free p m
  have hadj : Algebra.adjoin (O0 p) {xn p m, yn p m} = ⊤ :=
    GlobalTheory.K5.OnDVR.adjoin_eq_top_of_basis b (xn p m) (yn p m) (fun i => (i : ℕ)) (fun j => (j : ℕ))
      (fun i j => hb i j)
  refine ⟨?_, ?_⟩
  · obtain ⟨hdom, -, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
    haveI : Module.Finite (O0 p) (On p m) := Module.Finite.of_basis b
    haveI : Algebra.IsIntegral (O0 p) (On p m) := Algebra.IsIntegral.of_finite _ _
    have hk : RingHom.ker (ι : On p m →+* Ω) = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := O0 p)
      rw [eq_bot_iff]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker] at ha
      have h1 : algebraMap (O0 p) Ω a = 0 := by
        rw [← ι.commutes]; exact ha
      rw [Ideal.mem_bot]
      exact hΩ.inj (by rw [h1, map_zero])
    exact (RingHom.injective_iff_ker_eq_bot _).2 hk
  · rw [← Algebra.map_top, ← hadj, AlgHom.map_adjoin, Set.image_pair, hι.1, hι.2]
    rfl

end GlobalTheory.K5.LevEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceTower
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.TraceTower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_pow (T : Tower p Ω) (m k : ℕ) : T.ζ (m + k) ^ (p ^ k) = T.ζ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, pow_succ', pow_mul, T.ζpow, ih]

theorem qq_pow (T : Tower p Ω) (m k : ℕ) : T.qq (m + k) ^ (p ^ k) = T.qq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← Nat.add_assoc, pow_succ', pow_mul, T.qpow, ih]

theorem zeta_pow' (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : T.ζ n ^ (p ^ (n - m)) = T.ζ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using zeta_pow T m k

theorem qq_pow' (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : T.qq n ^ (p ^ (n - m)) = T.qq m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using qq_pow T m k

theorem qq_pow_top (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  have := qq_pow' T (Nat.zero_le n)
  simpa [T.q0] using this

theorem geo (ω : Ω) (K : ℕ) (hω : IsPrimitiveRoot ω K) (i : ℕ) :
    ∑ c ∈ Finset.range K, (ω ^ i) ^ c = if K ∣ i then (K : Ω) else 0 := by
  split_ifs with h
  · rw [(hω.pow_eq_one_iff_dvd i).2 h]; simp
  · have h1 : ω ^ i ≠ 1 := fun e => h ((hω.pow_eq_one_iff_dvd i).1 e)
    have h2 := geom_sum_mul (ω ^ i) K
    have h3 : (ω ^ i) ^ K = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    rw [h3, sub_self] at h2
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 h1)

theorem lift_hom {R A S M : Type} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [Field S]
    [Algebra R S] [Algebra.IsAlgebraic R S] [Field M] [IsAlgClosed M]
    (hA : Function.Injective (algebraMap R A)) (ι : A →ₐ[R] S) (f : A →+* M)
    (hι : Function.Injective ι) (hf : Function.Injective f) :
    ∃ τ : S →+* M, ∀ x, τ (ι x) = f x := by
  letI : Algebra A S := ι.toRingHom.toAlgebra
  letI : Algebra A M := f.toAlgebra
  haveI : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  haveI : Algebra.IsAlgebraic A S := Algebra.IsAlgebraic.extendScalars (R := R) hA
  haveI : Module.IsTorsionFree A S := Module.isTorsionFree_iff_algebraMap_injective.2 hι
  haveI : Module.IsTorsionFree A M := Module.isTorsionFree_iff_algebraMap_injective.2 hf
  let L : S →ₐ[A] M := IsAlgClosed.lift
  exact ⟨L.toRingHom, fun x => L.commutes x⟩

theorem ext_aut (hΩ : IsClo p Ω) {A : Type} [CommRing A] [IsDomain A] [Algebra (O0 p) A]
    [Algebra.IsIntegral (O0 p) A] (ι f : A →ₐ[O0 p] Ω) :
    ∃ σ : Gal p Ω, ∀ x : A, σ (ι x) = f x := by
  haveI := hΩ.clo
  haveI := hΩ.alg
  haveI : IsDomain (O0 p) := hΩ.inj.isDomain _
  have hinj : ∀ g : A →ₐ[O0 p] Ω, Function.Injective g := by
    intro g
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := O0 p) ?_
    rw [eq_bot_iff]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes] at hr
    exact hΩ.inj (by rw [hr, map_zero])
  have hA : Function.Injective (algebraMap (O0 p) A) := by
    intro x y hxy
    apply hΩ.inj
    rw [← ι.commutes, ← ι.commutes, hxy]
  obtain ⟨τ, hτ⟩ := lift_hom hA ι f.toRingHom (hinj ι) (hinj f)
  let τ' : Ω →ₐ[O0 p] Ω :=
    { τ with
      commutes' := fun r => by
        show τ _ = _
        rw [← ι.commutes, hτ, ι.commutes]
        exact f.commutes r }
  haveI : Module.IsTorsionFree (O0 p) Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hΩ.inj
  exact ⟨AlgEquiv.ofBijective τ' (Algebra.IsAlgebraic.algHom_bijective τ'), hτ⟩

open Polynomial in

theorem exists_hom (T : Tower p Ω) (n : ℕ) (a b : ℕ) (ha : ¬ p ∣ a) :
    ∃ f : On p n →ₐ[O0 p] Ω, f (xn p n) = T.ζ n ^ a ∧ f (yn p n) = T.ζ n ^ b * T.qq n := by
  classical
  have hp := (Fact.out : p.Prime)
  have hcop : a.Coprime (p ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 ha))
  have hprim : IsPrimitiveRoot (T.ζ n ^ a) (p ^ n) := (T.prim n).pow_of_coprime a hcop
  let φ : Polynomial (Polynomial (O0 p)) →ₐ[O0 p] Ω :=
    aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n)
  have hle : towerIdeal p n ≤ RingHom.ker φ := by
    refine Ideal.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) (C (cyclotomic (p ^ n) (O0 p))) = 0
      rw [aevalTower_C, aeval_def, ← eval_map, map_cyclotomic]
      exact hprim.isRoot_cyclotomic (pow_pos hp.pos n)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) (X ^ (p ^ n) - C (C (qO p))) = 0
      rw [map_sub, map_pow, aevalTower_X, aevalTower_C, aeval_C, mul_pow, qq_pow_top, ← pow_mul,
        mul_comm b, pow_mul, (T.prim n).pow_eq_one, one_pow, one_mul, sub_self]
  let f0 : On p n →ₐ[O0 p] Ω := Ideal.Quotient.liftₐ (towerIdeal p n) φ (fun x hx => (RingHom.mem_ker).1 (hle hx))
  have hf0x : f0 (xn p n) = T.ζ n ^ a := by
    show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) (C X) = _
    rw [aevalTower_C, aeval_X]
  have hf0y : f0 (yn p n) = T.ζ n ^ b * T.qq n := by
    show aevalTower (aeval (T.ζ n ^ a)) (T.ζ n ^ b * T.qq n) X = _
    rw [aevalTower_X]
  exact ⟨f0, hf0x, hf0y⟩

theorem exists_aut (hΩ : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) (a b : ℕ) (ha : ¬ p ∣ a) :
    ∃ σ : Gal p Ω, σ (T.ζ n) = T.ζ n ^ a ∧ σ (T.qq n) = T.ζ n ^ b * T.qq n := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨ι, hx, hy⟩ := exists_hom T n 1 0 hp.not_dvd_one
  obtain ⟨f, hfx, hfy⟩ := exists_hom T n a b ha
  obtain ⟨_, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  obtain ⟨B, -⟩ := GlobalTheory.K5.OnFree.on_free p n
  haveI : Module.Finite (O0 p) (On p n) := Module.Finite.of_basis B
  haveI : Algebra.IsIntegral (O0 p) (On p n) := Algebra.IsIntegral.of_finite (O0 p) (On p n)
  obtain ⟨σ, key⟩ := ext_aut hΩ ι f
  have k1 := key (xn p n)
  have k2 := key (yn p n)
  rw [hx, hfx, pow_one] at k1
  rw [hy, hfy, pow_zero, one_mul] at k2
  exact ⟨σ, k1, k2⟩

theorem gms_iff {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω)
    (m s : ℕ) (g : Gal p Ω) : g ∈ Gms T m s ↔ g (T.ζ m) = T.ζ m ∧ g (T.qq s) = T.qq s := by
  rw [Gms, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    AlgEquiv.smul_def, AlgEquiv.smul_def]

end GlobalTheory.K5.TraceTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformPoleOrder
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem uniform_pole_order : ∀ (E : Subring ℂ) (M : ℕ) (f : ℍ → ℂ), 0 < M →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ) →
    (∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * f (γ • τ)) → ∃ w : ℕ, Lv E M w f := by
  intro E M f hM hinv hw
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  choose w hw using hw
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  let lift : SL(2, ZMod M) → SL(2, ℤ) := fun g => if h : ∃ γ, red γ = g then h.choose else 1
  let W : ℕ := Finset.univ.sup fun g => w (lift g)
  refine ⟨W, hinv, fun γ => ?_⟩
  have hex : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
  have hl : lift (red γ) = hex.choose := dif_pos hex
  set γ' := lift (red γ) with hγ'
  have hred : red γ' = red γ := by rw [hl]; exact hex.choose_spec
  have hmem : γ * γ'⁻¹ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem']
    show red (γ * γ'⁻¹) = 1
    rw [map_mul, map_inv, hred, mul_inv_cancel]
  have hf : ∀ τ : ℍ, f (γ • τ) = f (γ' • τ) := fun τ => by
    have := hinv _ hmem (γ' • τ)
    rw [← this, ← mul_smul, inv_mul_cancel_right]
  have hle : w γ' ≤ W := Finset.le_sup (f := fun g => w (lift g)) (Finset.mem_univ (red γ))
  have hD : QAll (· ∈ E) M fun τ => DD τ ^ (W - w γ') :=
    QAllSubring.pow _ (eis_qAll M hM DD (Or.inr (Or.inr rfl)) E)
  have := QAllSubring.mul hD (hw γ')
  convert this using 2 with τ
  rw [hf τ, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitPieceMuEq
section
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem pieceTRaw_eq (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (x y : ℤ) (r : ℕ) :
    pieceTRaw N p m m k ψ (x, 0) (y, 0) ζ (unitSet p m) r = -((p : K) ^ ((m : ℤ) * ((k : ℤ) - 4))) *
      ∑ i ∈ range (r + 1),
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val) (r - i)) := by
  unfold pieceTRaw cmul
  congr 1
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have h := drop_const p m N k hm hpN hk ψ hψ ζ x y 0 0 i (r - i)
  simp only [mul_zero, add_zero] at h
  rw [← h]
  have e := sum_unitSet p m ψ (fun u a v b =>
    eisF (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val) i *
        eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val) (r - i))
  rw [← e]
  refine sum_congr rfl fun γ _ => ?_
  simp [rowT]

theorem coef_eq (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m))
    (a₀ b₀ t : ℤ) (ht : (p : ℤ) ^ m * t ≡ 1 [ZMOD N]) (r : ℕ) :
    pieceTRaw N p m m k ψ (a₀ * t, 0) (b₀ * t, 0) ζ (unitSet p m) r =
      if p ^ m ∣ r then -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
        (N : K) ^ ((2 : ℤ) - k) * coPtMu N p m k ψ a₀ b₀ r else 0 := by
  have hp : p.Prime := Fact.out
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  rw [pieceTRaw_eq p m N k hm hpN hk ψ hψ ζ]
  rw [sum_congr rfl fun i hi => by
    rw [GlobalTheory.T.primitiveCharacter_entry_sum_eisenstein_product p m N k K hm hN hpN hk ψ hψ ζ hζ a₀ b₀ t ht,
      Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hi))]]
  split_ifs with h
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have e' : (p : K) ^ ((m : ℤ) * (((k' + 2 : ℕ) : ℤ) - 4)) * (p : K) ^ m *
        ((((N * p ^ m : ℕ) : K)) ^ (k' + 2 - 2))⁻¹ = (p : K) ^ (-(m : ℤ)) * (N : K) ^ ((2 : ℤ) - ((k' + 2 : ℕ) : ℤ)) := by
      rw [Nat.add_sub_cancel, zpow_mul]
      push_cast
      rw [show ((k' : ℤ) + 2 - 4) = (k' : ℤ) - 2 by ring, show (2 : ℤ) - (k' + 2) = -(k' : ℤ) by ring,
        zpow_sub₀ (zpow_ne_zero _ hpK), zpow_neg, zpow_neg]
      simp only [zpow_natCast]
      field_simp
      ring
    unfold coPtMu cmul
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]
    calc _ = -((p : K) ^ ((m : ℤ) * (((k' + 2 : ℕ) : ℤ) - 4)) * (p : K) ^ m *
        ((((N * p ^ m : ℕ) : K)) ^ (k' + 2 - 2))⁻¹) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
          (ffMu N p m (k' + 2) ψ a₀ i * eeMu N p m ψ b₀ (r - i)) := by ring
      _ = _ := by rw [e']; ring
  · simp

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu

theorem GlobalTheory.KummerEisensteinGalois.unitPieceMu_eq : ∀ (p : ℕ) [Fact p.Prime] (N m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (a b t : ℤ) (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ (N * p ^ m) → 0 < N → ¬ p ∣ N → 1 ≤ m → 3 ≤ k → ψ.IsPrimitive → (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → Integral (p ^ m) (pieceTRaw N p m m k ψ (a * t, 0) (b * t, 0) ζ (unitSet p m)) ∧ ∀ r : ℕ, toQ (p ^ m) (pieceTRaw N p m m k ψ (a * t, 0) (b * t, 0) ζ (unitSet p m)) r = -((p : K) ^ (-(m : ℤ))) * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (N : K) ^ ((2 : ℤ) - k) * up (p ^ m) (coPtMu N p m k ψ a b) r := by
  intro p _ N m k K _ _ ψ a b t ζ _ hζ hN hpN hm hk hψ ht
  refine ⟨fun r hr => ?_, fun r => ?_⟩
  · rw [GlobalTheory.KummerEisensteinGalois.UnitPieceMu.coef_eq p m N k hm hN hpN hk ψ hψ ζ hζ a b t ht, if_neg hr]
  · unfold toQ up
    rw [GlobalTheory.KummerEisensteinGalois.UnitPieceMu.coef_eq p m N k hm hN hpN hk ψ hψ ζ hζ a b t ht, if_pos (dvd_mul_right _ _)]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringGaloisStableOfKummer
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory

theorem isPGroup_coatom_normal_index_eq {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (K : Subgroup P) (hK : IsCoatom K) :
    K.Normal ∧ K.index = p := by
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hN : K.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom K Group.normalizerCondition_of_isNilpotent hK
  have hQ : IsPGroup p (P ⧸ K) := hP.to_quotient K
  have hidx : K.index ≠ 1 := fun h => hK.1 (Subgroup.index_eq_one.1 h)
  have hdvd : p ∣ Nat.card (P ⧸ K) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hidx (by rw [Subgroup.index_eq_card, hn, pow_zero])
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  have htop : (Subgroup.zpowers x).comap (QuotientGroup.mk' K) = ⊤ := by
    apply hK.2
    refine lt_of_le_of_ne ?_ ?_
    · intro k hk
      have : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).2 hk
      rw [Subgroup.mem_comap, this]
      exact one_mem _
    · intro h
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K x
      have : y ∈ K := by
        rw [h, Subgroup.mem_comap]
        exact Subgroup.mem_zpowers _
      exact hx1 ((QuotientGroup.eq_one_iff y).2 this)
  have hz : Subgroup.zpowers x = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K z
    have : y ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' K) := by
      rw [htop]; exact Subgroup.mem_top _
    exact this
  have hcard : Nat.card (P ⧸ K) = p := by
    rw [← hx, ← Nat.card_zpowers, hz, Subgroup.card_top]
  exact ⟨hN, by rw [Subgroup.index_eq_card, hcard]⟩

theorem valuationSubring_galois_stable_of_kummer : ∀ (l : ℕ), l.Prime → ∀ (F L : Type) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L], IsPGroup l (L ≃ₐ[F] L) → (∃ ζ : F, IsPrimitiveRoot ζ l) → ∀ W : ValuationSubring L, (∀ θ : L, θ ≠ 0 → θ ^ l ∈ (algebraMap F L).range → ∀ τ : L ≃ₐ[F] L, ∀ x ∈ IntermediateField.adjoin F {θ}, τ x ∈ W ↔ x ∈ W) → ∀ (τ : L ≃ₐ[F] L) (x : L), τ x ∈ W ↔ x ∈ W := by
  intro l hl F L _ _ _ _ _ hP hζ W hW
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  let D : Subgroup (L ≃ₐ[F] L) :=
    { carrier := {σ | ∀ x, σ x ∈ W ↔ x ∈ W}
      mul_mem' := by
        intro a b ha hb x
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AlgEquiv.mul_apply, ha, hb]
      one_mem' := by intro x; simp
      inv_mem' := by
        intro a ha x
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (a⁻¹ x)]
        simp }
  suffices hD : D = ⊤ by
    intro τ x
    have hτ : τ ∈ D := hD ▸ Subgroup.mem_top τ
    exact hτ x
  by_contra hD
  obtain ⟨H, hH, hDH⟩ := (eq_top_or_exists_le_coatom D).resolve_left hD
  obtain ⟨hHn, hHi⟩ := isPGroup_coatom_normal_index_eq hP H hH
  haveI : IsGalois F (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
  have hfr : Module.finrank F (IntermediateField.fixedField H) = l := by
    have h1 := Module.finrank_mul_finrank F (IntermediateField.fixedField H) L
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F L,
      ← H.card_mul_index, hHi, mul_comm (Nat.card H)] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  haveI : IsCyclic (IntermediateField.fixedField H ≃ₐ[F] IntermediateField.fixedField H) :=
    isCyclic_of_prime_card (p := l) (by rw [IsGalois.card_aut_eq_finrank, hfr])
  obtain ⟨ζ, hζ⟩ := hζ
  have hK : (primitiveRoots (Module.finrank F (IntermediateField.fixedField H)) F).Nonempty :=
    ⟨ζ, by rw [hfr, mem_primitiveRoots hl.pos]; exact hζ⟩
  obtain ⟨α, ⟨δ, hδ⟩, hα⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic F (IntermediateField.fixedField H) hK
  rw [hfr] at hδ
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h1 : (⊤ : IntermediateField F (IntermediateField.fixedField H)) = ⊥ := by
      rw [← hα]; exact IntermediateField.adjoin_simple_eq_bot_iff.2 (zero_mem _)
    have h2 := congrArg
      (fun E : IntermediateField F (IntermediateField.fixedField H) => Module.finrank F E) h1
    simp only [IntermediateField.finrank_top', IntermediateField.finrank_bot] at h2
    exact hl.one_lt.ne' (hfr ▸ h2)
  have hθ0 : (α : L) ≠ 0 := fun h => hα0 (Subtype.ext h)
  have hθl : (α : L) ^ l ∈ (algebraMap F L).range := by
    refine ⟨δ, ?_⟩
    have := congrArg (fun y : IntermediateField.fixedField H => (y : L)) hδ
    simpa using this
  have hKθ : ∀ x ∈ IntermediateField.fixedField H, x ∈ IntermediateField.adjoin F {(α : L)} := by
    intro x hx
    have hm : x ∈ (IntermediateField.adjoin F {α}).map (IntermediateField.fixedField H).val :=
      ⟨⟨x, hx⟩, by rw [hα]; trivial, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at hm
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∉ H := by
    by_contra h
    exact hH.1 (eq_top_iff.2 fun g _ => by_contra fun hg => h ⟨g, hg⟩)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace (IntermediateField.fixedField H) L W (W.comap (τ : L →+* L))
    (fun a => (hW α hθ0 hθl τ a (hKθ a a.2)).symm)
  have hη : σ.restrictScalars F ∈ H := by
    refine (IntermediateField.fixingSubgroup_fixedField H).le ?_
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  have hτη : τ * σ.restrictScalars F ∈ D := fun x => hσ x
  exact hτ ((H.mul_mem_cancel_right hη).1 (hDH hτη))

end GlobalTheory
end

