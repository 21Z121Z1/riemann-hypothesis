import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0521

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryDivisorsExistDiscretelyValued
section
noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.InertZeta

theorem elementaryDivisors_exist_discretely_valued : Smith := by
  intro L _ _ ϖ n hϖ g hg
  have hv0 : Valued.v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.exp_ne_zero
  have hϖ0 : ϖ ≠ 0 := fun h => hv0 (by rw [h, map_zero])
  have hnt : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, hv0, by rw [hϖ]; decide⟩
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hA : IsDiscreteValuationRing A := Valuation.valuationSubring_isDiscreteValuationRing _
  have : IsPrincipalIdealRing (intL L) := inferInstanceAs (IsPrincipalIdealRing A)
  let G : GL (Fin n) L := Matrix.nonsingInvUnit g (isUnit_iff_ne_zero.2 hg)
  obtain ⟨c, hc0, hcg, -⟩ := P.glint_exists_denom (n := Fin n) A G
  obtain ⟨d, -, k₁, h₁, k₂, h₂, e⟩ := P.cartan_decomp_gen (intL L) Valued.v (fun _ => Iff.rfl) ϖ hϖ0
    (fun x hx => by
      have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      refine ⟨-WithZero.log (Valued.v x), ?_⟩
      rw [hϖ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hx']) G c hc0 hcg
  refine ⟨d, k₁, (k₁⁻¹ : GL (Fin n) L), k₂, (k₂⁻¹ : GL (Fin n) L), P.cartan_entries_of_mem _ _ h₁,
    P.cartan_entries_of_mem _ _ (inv_mem h₁), P.cartan_entries_of_mem _ _ h₂,
    P.cartan_entries_of_mem _ _ (inv_mem h₂), k₁.inv_mul, k₂.mul_inv, ?_⟩
  exact e

end GlobalTheory.InertZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceOfValuationRing
section
open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.EmbeddingPlace

open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    FinitePlace.mk v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def,
    NNReal.coe_le_one]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)

open NumberField IsDedekindDomain in
private theorem valuation_le_one_iff_exists_eq_mul_inv_of_notMem {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (v : HeightOneSpectrum R) (x : L) :
    v.valuation L x ≤ 1 ↔
      ∃ a, ∃ s ∉ v.asIdeal, x = algebraMap R L a * (algebraMap R L s)⁻¹ := by
  rw [← Valuation.mem_valuationSubring_iff,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    ← ValuationSubring.mem_toSubring, HeightOneSpectrum.valuationSubringAtPrime_toSubring,
    Subalgebra.mem_toSubring]
  simp only [Localization.subalgebra.ofField]
  change (∃ a s, ∃ (_ : s ∈ v.asIdeal.primeCompl),
      x = algebraMap R L a * (algebraMap R L s)⁻¹) ↔ _
  exact ⟨fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩, fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩⟩

open NumberField IsDedekindDomain in
private theorem exists_heightOneSpectrum_range_iff_finitePlace_le_one {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p ≠ 0)
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) (ι : K →+* FractionRing O) :
    ∃ la : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ la.asIdeal ∧
      ∀ x : K, ι x ∈ (algebraMap O (FractionRing O)).range ↔ FinitePlace.mk la x ≤ 1 := by
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hint : ∀ y : 𝓞 K, IsIntegral O (ι (algebraMap (𝓞 K) K y)) := fun y =>
    IsIntegral.map_of_comp_eq (algebraMap ℤ O) ι (RingHom.ext_int _ _)
      (RingOfIntegers.isIntegral_coe y)
  let ψ : 𝓞 K →+* O :=
    { toFun := fun y => IsIntegralClosure.mk' O (ι (algebraMap (𝓞 K) K y)) (hint y)
      map_one' := hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_mul' := fun a b => hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_zero' := hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_add' := fun a b => hinj (by simp [IsIntegralClosure.algebraMap_mk']) }
  have hψ : ∀ y : 𝓞 K, algebraMap O (FractionRing O) (ψ y) = ι (algebraMap (𝓞 K) K y) :=
    fun y => IsIntegralClosure.algebraMap_mk' O _ (hint y)
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal O).comap ψ
  have hpP : (p : 𝓞 K) ∈ P := Ideal.mem_comap.mpr (by rw [map_natCast]; exact hpO)
  have hPne : P ≠ ⊥ := by
    intro h
    have hp0 := hpP
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hp0
    exact hp hp0
  have hunitP : ∀ s : 𝓞 K, s ∉ P → IsUnit (ψ s) := fun s hs =>
    IsLocalRing.notMem_maximalIdeal.mp hs
  let la : HeightOneSpectrum (𝓞 K) :=
    { asIdeal := P, isPrime := Ideal.IsPrime.comap ψ, ne_bot := hPne }
  refine ⟨la, hpP, fun x => ?_⟩
  rw [_root_.GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff]
  constructor
  · rintro ⟨o, ho⟩
    by_contra hx
    push_neg at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hy : la.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hx
    obtain ⟨a, s, hs, hxa⟩ := (valuation_le_one_iff_exists_eq_mul_inv_of_notMem la x⁻¹).mp hy.le
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        exact hs (zero_mem _)
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr this
    have hsa : algebraMap (𝓞 K) K a = x⁻¹ * algebraMap (𝓞 K) K s := by
      rw [hxa, inv_mul_cancel_right₀ hs0]
    have hvs : la.valuation K (algebraMap (𝓞 K) K s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact le_antisymm (la.intValuation_le_one s)
        (not_lt.mp fun h => hs ((la.intValuation_lt_one_iff_mem s).mp h))
    have hva : la.intValuation a < 1 := by
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
      change la.valuation K (algebraMap (𝓞 K) K a) < 1
      rw [hsa, map_mul, hvs, mul_one]
      exact hy
    have ha : ψ a ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mem_comap.mp ((la.intValuation_lt_one_iff_mem a).mp hva)
    have heq : o * ψ a = ψ s := hinj (by
      rw [map_mul, ho, hψ, hψ, hsa, map_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0,
        map_one, one_mul])
    have hunit : IsUnit (o * ψ a) := by
      rw [heq]
      exact hunitP s hs
    exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_mul_isUnit_right hunit)
  · intro h
    obtain ⟨a, s, hs, rfl⟩ := (valuation_le_one_iff_exists_eq_mul_inv_of_notMem la x).mp h
    refine ⟨ψ a * ↑(hunitP s hs).unit⁻¹, ?_⟩
    rw [map_mul, map_units_inv, IsUnit.unit_spec, hψ, hψ, map_mul, map_inv₀]

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.EmbeddingPlace.exists_place : ∀ (D : _root_.Formalism.BasicNotions.D7) (Ks : Type) [Field Ks] [NumberField Ks] (i : D.ntw.Tw) (ι : Ks →+* FractionRing (D.ntw.O i)), ∃ la : HeightOneSpectrum (𝓞 Ks), ((D.ntw.l i : ℕ) : 𝓞 Ks) ∈ la.asIdeal ∧ ∀ x : Ks, ι x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range ↔ FinitePlace.mk la x ≤ 1 := by
  intro D Ks _ _ i ι
  haveI := D.ntw.domO i
  haveI := D.ntw.dvrO i
  exact exists_heightOneSpectrum_range_iff_finitePlace_le_one (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero (D.ntw.O_l i) ι

end GlobalTheory.EmbeddingPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryBlockDiagonalLeviElement
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem _root_.GlobalTheory.InertZeta.leviExists : _root_.GlobalTheory.InertZeta.LeviExists := by
  intro L _ _ ϖ σ q N hq a g₀
  obtain ⟨-, -, hσϖ, hv, -⟩ := hq
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp at hv
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.SatakeWeyl.embExists L σ (N + 2) N _root_.GlobalTheory.InertZeta.mid
    _root_.GlobalTheory.InertZeta.mid_injective _root_.GlobalTheory.InertZeta.mid_rev
  obtain ⟨h1, h2⟩ := hι g₀
  set d : Fin (N + 2) → L := fun i => if i = 0 then ϖ ^ a else if i = Fin.last (N + 1) then ϖ ^ (-a) else 1
  have hd : ∀ i, σ (d i) * d i.rev = 1 := by
    intro i
    rcases _root_.GlobalTheory.InertZeta.idx_cases i with rfl | ⟨k, rfl⟩ | rfl
    · simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, mul_inv_cancel₀ (zpow_ne_zero a hϖ)]
    · simp [d, ← _root_.GlobalTheory.InertZeta.mid_rev, _root_.GlobalTheory.InertZeta.mid_ne_zero,
        _root_.GlobalTheory.InertZeta.mid_ne_last]
    · simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, inv_mul_cancel₀ (zpow_ne_zero a hϖ)]
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.SatakeWeyl.exists_mat (σ := σ) (Matrix.diagonal d) (by
    ext i j
    unfold _root_.Formalism.UG.cT
    rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, _root_.Formalism.UG.P.fIwasawa_antiJ]
    split_ifs with h
    · subst h
      simpa using hd i
    · simp)
  have h0 : (0 : Fin (N + 2)) ∉ Set.range _root_.GlobalTheory.InertZeta.mid :=
    fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_zero k hk
  have hl : Fin.last (N + 1) ∉ Set.range _root_.GlobalTheory.InertZeta.mid :=
    fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_last k hk
  have hm : _root_.GlobalTheory.SatakeWeyl.mat (D * ι g₀) =
      Matrix.diagonal d * _root_.GlobalTheory.SatakeWeyl.mat (ι g₀) := by
    rw [← hD]
    rfl
  refine ⟨D * ι g₀, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hm, Matrix.diagonal_mul]
    have hne : i ≠ j := fun h => hij (h ▸ rfl)
    by_cases hi : i ∈ Set.range _root_.GlobalTheory.InertZeta.mid
    · by_cases hj : j ∈ Set.range _root_.GlobalTheory.InertZeta.mid
      · obtain ⟨k, rfl⟩ := hi
        obtain ⟨l, rfl⟩ := hj
        simp [_root_.GlobalTheory.InertZeta.blk_mid] at hij
      · rw [h2 i j (Or.inr hj), Matrix.one_apply_ne hne, mul_zero]
    · rw [h2 i j (Or.inl hi), Matrix.one_apply_ne hne, mul_zero]
  · rw [hm, Matrix.diagonal_mul, h2 0 0 (Or.inl h0), Matrix.one_apply_eq, mul_one]
    simp [d]
  · rw [hm, Matrix.diagonal_mul, h2 _ _ (Or.inl hl), Matrix.one_apply_eq, mul_one]
    simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero]
  · intro i j
    rw [hm, Matrix.diagonal_mul, h1]
    simp [d, _root_.GlobalTheory.InertZeta.mid_ne_zero, _root_.GlobalTheory.InertZeta.mid_ne_last]

end GlobalTheory.InertZeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumSpherical
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem det_mat_ne_zero {n : ℕ} (g : GU σ n) : (mat g).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n) L).isUnit).ne_zero

theorem constTerm (hF : FracExists) (hP : Pointwise) (hC : Count) (hS : SmallCorner) (hG : GenFun)
    (hU : IsUnramInv ϖ σ q) {a : ℤ} {g₀ : GU σ N} {m : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m) (X : ℂ)
    (hX : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun c : RadQuot σ N => X ^ len (mat (m * (c.out : radQ σ N).1)))
      ((q : ℂ) ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * X ^ (a.natAbs + len (mat g₀)) * jFac q N X) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hq : 1 ≤ q := le_trans (by norm_num) hU.2.2.2.2.2.1
  obtain ⟨U, V, C, hfr, hdet⟩ := hF L ϖ N hv (mat g₀) (det_mat_ne_zero g₀)
  have hPt := hP L ϖ σ q N hU a g₀ m hm U V C (len (mat g₀)) hfr hdet
  have hcard : ∀ j : ℕ, Nat.card {c : RadQuot σ N //
      len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j} =
      q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * q ^ (2 * N * (j / 2) + j) := by
    intro j
    have hiff : ∀ c : RadQuot σ N, len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j ↔
        Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) (c.out : radQ σ N).1 :=
      fun c => (hPt _ (c.out : radQ σ N).2).2 j
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    rw [hC L ϖ σ q N hU C (C * V * mat g₀) (len (mat g₀)) (a.toNat + j / 2) (2 * a.toNat + j) hfr.2.2.1 hdet
      (fun r hr => hS L ϖ σ q N hU g₀ U V C hfr _ _ r (by omega) hr) ?_]
    · rw [← pow_add]; congr 1; generalize j / 2 = t; ring
    · intro u hu k hk hkK hsm
      have hlen : len (mat (m * (u * k))) = len (mat (m * u)) := by
        have h := len_mat_mul (KU σ (N + 2)).one_mem hkK (m * u)
        rwa [one_mul, mul_assoc] at h
      refine ((hPt _ (mul_mem hu hk)).2 j).mp ?_
      rw [hlen]
      exact ((hPt u hu).2 j).mpr hsm
  have key := hG (RadQuot σ N) (fun c => len (mat (m * (c.out : radQ σ N).1))) (a.natAbs + len (mat g₀))
    (q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat)) q N X (Nat.one_le_pow _ _ hq) hq
    (fun c => (hPt _ (c.out : radQ σ N).2).1) hcard hX
  push_cast at key
  exact key

theorem bijective_cells (hS : CosetSurj) (hI : CosetInj) (hU : IsUnramInv ϖ σ q)
    (m : ℤ → GU σ N ⧸ KU σ N → GU σ (N + 2)) (hm : ∀ a y, IsLeviElt ϖ a y.out (m a y)) :
    Function.Bijective fun p : (ℤ × (GU σ N ⧸ KU σ N)) × RadQuot σ N =>
      (QuotientGroup.mk (m p.1.1 p.1.2 * (p.2.out : radQ σ N).1) : GU σ (N + 2) ⧸ KU σ (N + 2)) := by
  constructor
  · rintro ⟨⟨a, y⟩, c⟩ ⟨⟨a', y'⟩, c'⟩ h
    have h' := QuotientGroup.eq.mp h
    obtain ⟨rfl, hy⟩ := hI L ϖ σ q N hU a a' y.out y'.out (m a y) (m a' y') (hm a y) (hm a' y')
      _ (c.out : radQ σ N).2 _ (c'.out : radQ σ N).2 h'
    have hyy : y = y' := by
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      exact QuotientGroup.eq.mpr hy
    subst hyy
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using h'
    rw [hc]
  · intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨a, y, hay⟩ := hS L ϖ σ q N hU g
    obtain ⟨u, hu, k, hk, rfl⟩ := hay (m a y) (hm a y)
    refine ⟨((a, y), (QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N)), ?_⟩
    dsimp only
    apply QuotientGroup.eq.mpr
    have h1 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N))
    rw [Subgroup.mem_subgroupOf] at h1
    have e : (m a y * ((QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N).out : radQ σ N).1)⁻¹ * (m a y * u * k) =
        (((QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N).out)⁻¹ * ⟨u, hu⟩ : radQ σ N).1 * k := by
      simp [mul_assoc]
    rw [e]
    exact mul_mem h1 hk

theorem zVal_succ (q N : ℕ) (X y : ℂ) {r : ℕ} (α : Fin (r + 1) → ℂ) :
    zVal q (N + 2) X y α = (1 - X) * (1 + q * X) * ((1 - y * α 0)⁻¹ * (1 - y / α 0)⁻¹) *
      zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α) := by
  have hp : ∏ j ∈ Finset.range (N + 2), (1 - (-(q : ℂ)) ^ j * X) =
      (1 - X) * (1 + q * X) * ∏ j ∈ Finset.range N, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X)) := by
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    have h : ∀ j ∈ Finset.range N,
        (1 - (-(q : ℂ)) ^ (j + 1 + 1) * X) = (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X)) := by
      intro j _; ring
    rw [Finset.prod_congr rfl h]; ring
  have ho : Odd (N + 2) ↔ Odd N := by rw [Nat.odd_add]; simp
  unfold zVal
  rw [hp, Fin.prod_univ_succ, if_congr ho rfl rfl]
  simp only [Fin.tail]
  ring

theorem hasSum_small (hR : SmallRank) (hU : IsUnramInv ϖ σ q) {n : ℕ} (hn : n ≤ 1) (F : GU σ n → ℂ)
    (hF : ∀ k ∈ KU σ n, F k = 1) : HasSum (fun x : GU σ n ⧸ KU σ n => F x.out) 1 := by
  have hK : ∀ g : GU σ n, g ∈ KU σ n := fun g => hR L ϖ σ q n hU hn g
  have h1 : (fun x : GU σ n ⧸ KU σ n => F x.out) = fun _ => 1 := funext fun x => hF _ (hK _)
  rw [h1]
  refine hasSum_single (f := fun _ : GU σ n ⧸ KU σ n => (1 : ℂ)) (QuotientGroup.mk 1) fun b hb => ?_
  exfalso; apply hb
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
  exact QuotientGroup.eq.mpr (hK _)

theorem len_of_mem {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) : len (mat k) = 0 := by
  apply HasLen.len_eq
  apply hasLen_of_isInt
  intro i j
  rw [KU, Subgroup.mem_subgroupOf] at hk
  unfold intPts at hk
  obtain ⟨A, hA⟩ := (Subgroup.mem_inf.mp hk).2
  show (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intL L
  rw [← hA]
  exact ((A : Matrix (Fin n) (Fin n) (intL L)) i j).2

private lemma ordL_one_twisted_operators : ordL (1 : L) = 0 := by
  have h : Valued.v (1 : L) ≠ 0 := by simp
  have hu : WithZero.unzero h = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  unfold ordL
  rw [dif_neg h, hu]
  simp

private lemma chiDeltaU_one' {n m : ℕ} (α : Fin m → ℂ) : chiDeltaU (σ := σ) (n := n) q α 1 = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · simp [ordL_one_twisted_operators]
  · rfl

private lemma isBorelU_one' {n : ℕ} : IsBorelU (1 : GU σ n) := by
  intro i j h
  simp [Matrix.one_apply_ne h.ne']

private lemma isSphericalU_apply_mul_of_mem_KU {n m : ℕ} {α : Fin m → ℂ} {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) (g k : GU σ n)
    (hk : k ∈ KU σ n) : φ (g * k) = φ g := by
  have h := hφ 1 g k isBorelU_one' hk
  rwa [one_mul, chiDeltaU_one', one_mul] at h

private lemma exists_mem_KU_out_mk_eq_mul {n : ℕ} (g : GU σ n) :
    ∃ k ∈ KU σ n, (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out = g * k := by
  refine ⟨g⁻¹ * (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out, ?_, (mul_inv_cancel_left _ _).symm⟩
  have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : GU σ n ⧸ KU σ n))
  simpa [_root_.mul_inv_rev] using inv_mem h

theorem hasSum_spherical [CompleteSpace L] (hF : FracExists) (hP : Pointwise) (hC : Count) (hS : SmallCorner)
    (hG : GenFun) (hSu : CosetSurj) (hI : CosetInj) (hL : LeviExists) (hT : SphTrans) (hR : SmallRank) (hSt : Step)
    (hU : IsUnramInv ϖ σ q) (r : ℕ) : ∀ (n : ℕ), 2 * r ≤ n → n ≤ 2 * r + 1 → ∀ (α : Fin r → ℂ) (X y : ℂ)
      (φ : GU σ n → ℂ), (∀ i, α i ≠ 0) → y * q = X * (q : ℂ) ^ n → ‖y‖ < 1 →
      (∀ i, ‖y‖ * ‖α i‖ < 1 ∧ ‖y‖ * ‖α i‖⁻¹ < 1) → IsSphericalU q α φ → φ 1 = 1 →
      HasSum (fun x : GU σ n ⧸ KU σ n => X ^ len (mat x.out) * φ x.out) (zVal q n X y α) := by
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  induction r with
  | zero =>
    intro n hn0 hn1 α X y φ _ hyX hy _ hφ h1
    have hn : n ≤ 1 := by omega
    have hK : ∀ g : GU σ n, g ∈ KU σ n := fun g => hR L ϖ σ q n hU hn g
    have hφk : ∀ g : GU σ n, φ g = 1 := by
      intro g
      have h := isSphericalU_apply_mul_of_mem_KU hφ 1 g (hK g)
      rwa [one_mul, h1] at h
    have hsum := hasSum_small hR hU hn (fun g => X ^ len (mat g) * φ g)
      (fun k hk => by rw [len_of_mem hk, hφk, pow_zero, one_mul])
    convert hsum using 1
    interval_cases n
    · simp [zVal]
    · have hyx : y = X := by
        apply mul_right_cancel₀ hq0
        rw [hyX]; ring
      subst hyx
      have hy1 : (1 : ℂ) - y ≠ 0 := by
        intro h
        have h' : y = 1 := by linear_combination -h
        rw [h'] at hy; simp at hy
      simp [zVal, hy1]
  | succ r ih =>
    intro n hn0 hn1 α X y φ hα hyX hy hαy hφ h1
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
    obtain ⟨φ₀, hφ₀, hφ₀1, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q N r hU (by omega) (by omega)
      (Fin.tail α) (fun i => hα _)
    have hZ := ih N (by omega) (by omega) (Fin.tail α) ((q : ℂ) ^ 2 * X) y φ₀ (fun i => hα _)
      (by rw [hyX]; ring) hy (fun i => hαy _) hφ₀ hφ₀1
    have hy' : y = (q : ℂ) ^ (N + 1) * X := by
      apply mul_right_cancel₀ hq0
      rw [hyX]; ring
    choose m hm using fun (a : ℤ) (b : GU σ N ⧸ KU σ N) => hL L ϖ σ q N hU a b.out
    have hstep := hSt (GU σ N ⧸ KU σ N) (RadQuot σ N) q N
      (fun a b c => len (mat (m a b * (c.out : radQ σ N).1))) (fun b => len (mat b.out)) (fun b => φ₀ b.out)
      (α 0) X y (zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α))
      (by omega) (hα 0) hy' hy (hαy 0).1 (hαy 0).2
      (fun X' hX' a b => constTerm hF hP hC hS hG hU (hm a b) X' hX') hZ
    rw [zVal_succ, ← (Equiv.ofBijective _ (bijective_cells hSu hI hU m hm)).hasSum_iff]
    convert hstep using 1
    funext p
    obtain ⟨⟨a, b⟩, c⟩ := p
    simp only [Function.comp_apply, Equiv.ofBijective_apply]
    obtain ⟨k, hk, hout⟩ := exists_mem_KU_out_mk_eq_mul (m a b * (c.out : radQ σ N).1)
    have hlen := len_mat_mul (KU σ (N + 2)).one_mem hk (m a b * (c.out : radQ σ N).1)
    rw [one_mul] at hlen
    rw [hout, isSphericalU_apply_mul_of_mem_KU hφ _ _ hk, hlen,
      hT L ϖ σ q N r hU (by omega) α φ φ₀ hα hφ h1 hφ₀ hφ₀1 a b.out (m a b) (hm a b) _ (c.out : radQ σ N).2]

end GlobalTheory.InertZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosets
section
open GlobalTheory.InertZeta

open MeasureTheory Pointwise

namespace GlobalTheory.InertZeta

theorem cosetIntegral_holds : CosetIntegral := by
  intro G _ _ _ _ _ μ _ K hK hμK F Z hF hZ
  classical
  set f : G ⧸ K → ℂ := fun x => F x.out with hf
  let A : G ⧸ K → Set G := fun x => QuotientGroup.mk ⁻¹' {x}
  have hA : ∀ x, A x = x.out • (K : Set G) := by
    intro x; ext g
    simp only [A, Set.mem_preimage, Set.mem_singleton_iff, mem_leftCoset_iff]
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rw [eq_comm, QuotientGroup.eq]
    rfl
  have hAm : ∀ x, MeasurableSet (A x) := fun x => by
    rw [hA]; exact (hK.smul x.out).measurableSet
  have hAμ : ∀ x, μ (A x) = 1 := fun x => by rw [hA, measure_smul]; exact hμK
  have hconst : ∀ x, ∀ g ∈ A x, F g = f x := by
    intro x g hg
    rw [hA, mem_leftCoset_iff] at hg
    have := hF x.out _ hg
    rwa [mul_inv_cancel_left] at this
  have hself : ∀ g : G, g ∈ A (QuotientGroup.mk g) := fun g => rfl
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro x y hxy
    exact (Set.disjoint_singleton.mpr hxy).preimage _
  set S := Function.support f with hSdef
  have hS : S.Countable := hZ.summable.countable_support
  haveI : Countable S := hS.to_subtype
  let B : S → Set G := fun i => A i.1
  have hBint : ∀ i : S, ∫ g in B i, F g ∂μ = f i.1 := by
    intro i
    rw [setIntegral_congr_fun (hAm i.1) (fun g hg => hconst i.1 g hg), setIntegral_const]
    simp [Measure.real, hAμ]
  have hBnorm : ∀ i : S, ∫ g in B i, ‖F g‖ ∂μ = ‖f i.1‖ := by
    intro i
    rw [setIntegral_congr_fun (g := fun _ => ‖f i.1‖) (hAm i.1) (fun g hg => by simp only [hconst i.1 g hg]), setIntegral_const]
    simp [Measure.real, hAμ]
  have hBon : ∀ i : S, IntegrableOn F (B i) μ := by
    intro i
    have h1 : IntegrableOn (fun _ : G => f i.1) (B i) μ :=
      integrableOn_const (by simp [B, hAμ]) (by simp)
    exact h1.congr_fun (fun g hg => (hconst i.1 g hg).symm) (hAm i.1)
  have hsumm : Summable fun i : S => ∫ g in B i, ‖F g‖ ∂μ := by
    simp only [hBnorm]
    exact (summable_norm_iff.mpr hZ.summable).subtype S
  have hU : IntegrableOn F (Set.iUnion B) μ :=
    integrableOn_iUnion_of_summable_integral_norm hBon hsumm
  have hzero : ∀ g ∉ Set.iUnion B, F g = 0 := by
    intro g hg
    have hnot : (QuotientGroup.mk g : G ⧸ K) ∉ S := by
      intro hm
      exact hg (Set.mem_iUnion.mpr ⟨⟨_, hm⟩, hself g⟩)
    rw [hconst _ g (hself g)]
    simpa [hSdef] using hnot
  have hInt : Integrable F μ := hU.integrable_of_forall_notMem_eq_zero hzero
  refine ⟨hInt, ?_⟩
  have h1 := hasSum_integral_iUnion (fun i : S => hAm i.1) (fun i j hij => hdisj (fun h => hij (Subtype.ext h))) hU
  have hfun : (fun i : S => ∫ g in B i, F g ∂μ) = fun i => f i.1 := funext hBint
  rw [hfun] at h1
  have h2 : HasSum (fun i : S => f i.1) Z :=
    (hasSum_subtype_iff_of_support_subset (s := S) subset_rfl).mpr hZ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact h1.unique h2

end GlobalTheory.InertZeta
end

