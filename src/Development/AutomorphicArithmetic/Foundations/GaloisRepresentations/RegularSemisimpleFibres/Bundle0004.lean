import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0289
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0103

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftOk
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.Gal.InertialTypesAlt.coprime_pow_sub_one_self {q m : ℕ} (hm : 0 < m) (hq : 2 ≤ q) : Nat.Coprime (q ^ m - 1) q := by
  have hpos : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
  have e : q ^ m - 1 + 1 = q ^ m := by omega
  have a := Nat.gcd_dvd_left (q ^ m - 1) q
  have b := Nat.gcd_dvd_right (q ^ m - 1) q
  have c : Nat.gcd (q ^ m - 1) q ∣ q ^ m - 1 + 1 := by
    rw [e]
    exact b.trans (dvd_pow_self q hm.ne')
  exact Nat.dvd_one.1 ((Nat.dvd_add_right a).1 c)

private theorem UpperTheory.Gal.InertialTypesAlt.reg_dvd {q l m k : ℕ} (i : ℕ) (hq : 2 ≤ q) (hl : 0 < l) (hm : 0 < m) (hd : l ∣ m)
    (h : GlobalTheory.Shin.Reg q m k) : GlobalTheory.Shin.Reg (q ^ l) (m / l) (k * q ^ i) := by
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left c hl]
  intro j hj hjc hmod
  have hcop : Nat.gcd (q ^ (l * c) - 1) (q ^ i) = 1 :=
    Nat.Coprime.pow_right i (UpperTheory.Gal.InertialTypesAlt.coprime_pow_sub_one_self hm hq)
  refine h (l * j) (Nat.mul_pos hl hj) (Nat.mul_lt_mul_of_pos_left hjc hl) ?_
  rw [← pow_mul] at hmod
  apply Nat.ModEq.cancel_right_of_coprime hcop
  have e : k * q ^ (l * j) * q ^ i = k * q ^ i * (q ^ l) ^ j := by
    rw [← pow_mul]; ring
  rw [e]
  exact hmod

private theorem UpperTheory.Gal.InertialTypesAlt.reg_ndvd {q l m k : ℕ} (hq : 2 ≤ q) (hl : l.Prime) (hm : 0 < m) (hd : ¬ l ∣ m)
    (h : GlobalTheory.Shin.Reg q m k) : GlobalTheory.Shin.Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) := by
  intro j hj hjm hmod
  have hpos : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
  have hgt : 1 < q ^ m := Nat.one_lt_pow hm.ne' (by omega)
  have hx : q ^ m - 1 + 1 = q ^ m := by omega
  have hgeo := geom_sum_mul_add (q ^ m - 1) l
  rw [hx] at hgeo
  have hS : (∑ i ∈ Finset.range l, q ^ (m * i)) = ∑ i ∈ Finset.range l, (q ^ m) ^ i :=
    Finset.sum_congr rfl fun i _ => pow_mul q m i
  rw [← hS] at hgeo
  set S := ∑ i ∈ Finset.range l, q ^ (m * i) with hSdef
  have hbig : 1 < (q ^ m) ^ l := Nat.one_lt_pow hl.ne_zero hgt
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0] at hgeo
    omega
  have hmodulus : (q ^ l) ^ m - 1 = (q ^ m - 1) * S := by
    have : (q ^ l) ^ m = (q ^ m) ^ l := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [this, ← hgeo, Nat.mul_comm]
    simp
  rw [hmodulus] at hmod
  have e1 : k * (q ^ l) ^ j ≡ k [MOD q ^ m - 1] := by
    apply Nat.ModEq.mul_right_cancel' hS0
    have e : k * (q ^ l) ^ j * S = k * S * (q ^ l) ^ j := by ring
    rw [e]
    exact hmod
  have hone : q ^ m ≡ 1 [MOD q ^ m - 1] := by
    have : (q ^ m - 1) + 1 ≡ 0 + 1 [MOD q ^ m - 1] :=
      Nat.ModEq.add_right 1 (by simp [Nat.ModEq])
    rwa [hx] at this
  have hcop : Nat.Coprime m l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm
  have hr0 : (l * j) % m ≠ 0 := by
    intro h0
    have h1 : m ∣ l * j := Nat.dvd_of_mod_eq_zero h0
    have h2 : m ∣ j := hcop.dvd_of_dvd_mul_left h1
    have := Nat.le_of_dvd hj h2
    omega
  have hrm : (l * j) % m < m := Nat.mod_lt _ hm
  have hpow : q ^ (l * j) ≡ q ^ ((l * j) % m) [MOD q ^ m - 1] := by
    have hsplit : q ^ (l * j) = (q ^ m) ^ ((l * j) / m) * q ^ ((l * j) % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hsplit]
    have := (hone.pow ((l * j) / m)).mul_right (q ^ ((l * j) % m))
    simpa using this
  refine h _ (Nat.pos_of_ne_zero hr0) hrm ?_
  have e2 : k * q ^ ((l * j) % m) ≡ k * q ^ (l * j) [MOD q ^ m - 1] := (hpow.mul_left k).symm
  refine e2.trans ?_
  rw [pow_mul]
  exact e1

private theorem UpperTheory.Gal.InertialTypesAlt.deg_append (A B : List (ℕ × ℕ)) :
    GlobalTheory.Shin.deg (A ++ B) = GlobalTheory.Shin.deg A + GlobalTheory.Shin.deg B := by
  simp [GlobalTheory.Shin.deg]

private theorem UpperTheory.Gal.InertialTypesAlt.block_dvd (q l : ℕ) (p : ℕ × ℕ) (hd : l ∣ p.1) :
    GlobalTheory.Shin.deg (GlobalTheory.Shin.liftL q l [p]) = p.1 := by
  have h : ((List.range l).map fun i => (p.1 / l, p.2 * q ^ i)).map Prod.fst = List.replicate l (p.1 / l) := by
    rw [List.map_map]
    apply List.eq_replicate_iff.2
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    rfl
  have h2 : GlobalTheory.Shin.deg (GlobalTheory.Shin.liftL q l [p]) = (List.replicate l (p.1 / l)).sum := by
    rw [← h]
    simp [GlobalTheory.Shin.deg, GlobalTheory.Shin.liftL]
  rw [h2, List.sum_replicate, smul_eq_mul]
  exact Nat.mul_div_cancel' hd

private theorem UpperTheory.Gal.InertialTypesAlt.liftAll_spec (q l : ℕ) (L : List (ℕ × ℕ)) (hq : 2 ≤ q) (hl : l.Prime)
    (h : ∀ p ∈ L, 0 < p.1 ∧ GlobalTheory.Shin.Reg q p.1 p.2) :
    GlobalTheory.Shin.deg (GlobalTheory.Shin.liftAll q l L) = GlobalTheory.Shin.deg L ∧
      ∀ p ∈ GlobalTheory.Shin.liftAll q l L, 0 < p.1 ∧ GlobalTheory.Shin.Reg (q ^ l) p.1 p.2 := by
  induction L with
  | nil => simp [GlobalTheory.Shin.liftAll, GlobalTheory.Shin.deg]
  | cons p L ih =>
    obtain ⟨ih1, ih2⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨hp0, hpR⟩ := h p List.mem_cons_self
    have hsplit : GlobalTheory.Shin.liftAll q l (p :: L) =
        (if l ∣ p.1 then GlobalTheory.Shin.liftL q l [p] else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]) ++
          GlobalTheory.Shin.liftAll q l L := by
      simp only [GlobalTheory.Shin.liftAll, List.flatMap_cons]
    have hdegp : GlobalTheory.Shin.deg (p :: L) = p.1 + GlobalTheory.Shin.deg L := by simp [GlobalTheory.Shin.deg]
    rw [hsplit, UpperTheory.Gal.InertialTypesAlt.deg_append, ih1, hdegp]
    by_cases hd : l ∣ p.1
    · rw [if_pos hd]
      refine ⟨by rw [UpperTheory.Gal.InertialTypesAlt.block_dvd q l p hd], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · simp only [GlobalTheory.Shin.liftL, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        exact ⟨Nat.div_pos (Nat.le_of_dvd hp0 hd) hl.pos, UpperTheory.Gal.InertialTypesAlt.reg_dvd i hq hl.pos hp0 hd hpR⟩
      · exact ih2 x hx
    · rw [if_neg hd]
      refine ⟨by simp [GlobalTheory.Shin.deg], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hp0, UpperTheory.Gal.InertialTypesAlt.reg_ndvd hq hl hp0 hd hpR⟩
      · exact ih2 x hx

theorem UpperTheory.Gal.InertialTypesAlt.liftOk :
    LiftOk := by
  intro a l hl hok
  obtain ⟨hq, hD, hL⟩ := hok
  obtain ⟨h1, h2⟩ := UpperTheory.Gal.InertialTypesAlt.liftAll_spec a.q l a.L hq hl hL
  have hD' : GlobalTheory.Shin.deg (a.D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range l, a.q ^ i)) = GlobalTheory.Shin.deg a.D := by
    simp [GlobalTheory.Shin.deg, List.map_map, Function.comp_def]
  refine ⟨⟨?_, ?_, h2⟩, ?_⟩
  · show 2 ≤ a.q ^ l
    calc 2 ≤ a.q := hq
      _ ≤ a.q ^ l := Nat.le_self_pow hl.ne_zero a.q
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
    exact hD r hr
  · show GlobalTheory.Shin.deg (a.D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range l, a.q ^ i)) + GlobalTheory.Shin.deg (GlobalTheory.Shin.liftAll a.q l a.L) =
      GlobalTheory.Shin.deg a.D + GlobalTheory.Shin.deg a.L
    rw [hD', h1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PNameOf
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem natCard_of_finrank {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) : Nat.card K = g ^ m := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hK]

private theorem frob_top {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (x : K) : x ^ g ^ m = x := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_of_finrank hm hK
  rw [← hc]
  exact FiniteField.pow_card x

private theorem aeval_pow_prime_pow_eq_pow {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    (Y : (ZMod g)[X]) (x : K) (j : ℕ) : aeval (x ^ g ^ j) Y = (aeval x Y) ^ g ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, pow_mul, ← ih, ← Polynomial.expand_aeval, ZMod.expand_card, map_pow]

private theorem conj_ne {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (z : Kˣ) (hz : (minpoly (ZMod g) (z : K)).natDegree = m)
    (a : ℕ) (ha : 0 < a) (ham : a < m) : (z : K) ^ g ^ a ≠ z := by
  intro h
  classical
  have hg : g.Prime := Fact.out
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  set F := IntermediateField.adjoin (ZMod g) {(z : K)} with hFdef
  have hF : Module.finrank (ZMod g) F = m := by
    rw [IntermediateField.adjoin.finrank hint, hz]
  have hfix : ∀ y ∈ F, y ^ g ^ a = y := by
    intro y hy
    have hy' : y ∈ Algebra.adjoin (ZMod g) {(z : K)} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      exact hy
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    show (aeval (z : K) p) ^ g ^ a = aeval (z : K) p
    rw [← aeval_pow_prime_pow_eq_pow, h]
  have hq : 1 < g ^ a := Nat.one_lt_pow ha.ne' hg.one_lt
  have hP0 : (X ^ (g ^ a) - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hle := Polynomial.card_le_degree_of_subset_roots (p := (X ^ (g ^ a) - X : K[X]))
    (Z := Finset.univ.map (Function.Embedding.subtype (· ∈ F))) (by
      intro y hy
      rw [Finset.map_val, Multiset.mem_map] at hy
      obtain ⟨⟨y, hyF⟩, -, rfl⟩ := hy
      rw [Polynomial.mem_roots hP0, IsRoot, eval_sub, eval_pow, eval_X]
      simp only [Function.Embedding.coe_subtype]
      rw [hfix y hyF, sub_self])
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, Finset.card_map, Finset.card_univ,
    Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hF] at hle
  have := Nat.pow_lt_pow_right hg.one_lt ham
  omega

private theorem conj_inj {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (z : Kˣ) (hz : (minpoly (ZMod g) (z : K)).natDegree = m)
    (i j : ℕ) (hij : i < j) (hj : j < m) : (z : K) ^ g ^ i ≠ (z : K) ^ g ^ j := by
  intro h
  have key : ∀ x : K, (x ^ g ^ i) ^ g ^ (m - i) = x := by
    intro x
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (by omega)]
    exact frob_top hm hK x
  apply conj_ne hm hK z hz (j - i) (by omega) (by omega)
  have hs : (z : K) ^ g ^ j = ((z : K) ^ g ^ (j - i)) ^ g ^ i := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
  rw [hs] at h
  have h2 := congrArg (fun y => y ^ g ^ (m - i)) h
  simp only [key] at h2
  exact h2.symm

private theorem aeval_conj {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    (Y : (ZMod g)[X]) (x : K) (hx : aeval x Y = 0) (j : ℕ) : aeval (x ^ g ^ j) Y = 0 := by
  rw [aeval_pow_prime_pow_eq_pow, hx, zero_pow (pow_ne_zero _ (Fact.out : g.Prime).ne_zero)]

private theorem roots_conj {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = m) (Y : (ZMod g)[X]) (hY : Irreducible Y) (hYm : Y.Monic)
    (hYd : Y.natDegree = m) (z : Kˣ) (hz : aeval (z : K) Y = 0) {L : Type} [Field L] (ι : K →+* L) :
    ((Y.map (algebraMap (ZMod g) K)).map ι).roots = (Multiset.range m).map fun j => ι ((z : K) ^ g ^ j) := by
  have hzm : (minpoly (ZMod g) (z : K)).natDegree = m := by
    rw [← minpoly.eq_of_irreducible_of_monic hY hz hYm, hYd]
  have hnd : ((Multiset.range m).map fun j => ι ((z : K) ^ g ^ j)).Nodup := by
    rw [Multiset.nodup_map_iff_inj_on (Multiset.nodup_range m)]
    intro i hi j hj hij
    simp only [Multiset.mem_range] at hi hj
    have h' : (z : K) ^ g ^ i = (z : K) ^ g ^ j := ι.injective hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd h' (conj_inj hm hK z hzm i j h hj)
    · exact h
    · exact absurd h'.symm (conj_inj hm hK z hzm j i h hi)
  have hP0 : ((Y.map (algebraMap (ZMod g) K)).map ι) ≠ 0 := ((hYm.map _).map _).ne_zero
  have hle : ((Multiset.range m).map fun j => ι ((z : K) ^ g ^ j)) ≤
      ((Y.map (algebraMap (ZMod g) K)).map ι).roots := by
    rw [Multiset.le_iff_subset hnd]
    intro y hy
    rw [Multiset.mem_map] at hy
    obtain ⟨j, -, rfl⟩ := hy
    rw [mem_roots hP0, IsRoot, eval_map, eval₂_map, ← Polynomial.hom_eval₂, ← aeval_def,
      aeval_conj Y _ hz j, map_zero]
  have hdeg : ((Y.map (algebraMap (ZMod g) K)).map ι).natDegree = m := by
    rw [natDegree_map, natDegree_map, hYd]
  refine (Multiset.eq_of_le_of_card_le hle ?_).symm
  rw [Multiset.card_map, Multiset.card_range, ← hdeg]
  exact card_roots' _

private theorem false_of_reg_of_mul_pow_modEq {g m c i j : ℕ} (hg : 0 < g) (hc : Reg g m c) (hij : i < j) (hj : j < m)
    (h : c * g ^ i ≡ c * g ^ j [MOD g ^ m - 1]) : False := by
  have hone : g ^ m ≡ 1 [MOD g ^ m - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hg)
  have h2 := h.mul_right (g ^ (m - i))
  have e1 : c * g ^ i * g ^ (m - i) = c * g ^ m := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have e2 : c * g ^ j * g ^ (m - i) = c * g ^ (j - i) * g ^ m := by
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [e1, e2] at h2
  have h3 : c * g ^ m ≡ c [MOD g ^ m - 1] := by simpa using hone.mul_left c
  have h4 : c * g ^ (j - i) * g ^ m ≡ c * g ^ (j - i) [MOD g ^ m - 1] := by
    simpa using hone.mul_left (c * g ^ (j - i))
  exact hc (j - i) (by omega) (by omega) (h4.symm.trans (h2.symm.trans h3))

private theorem regular_character_of_pow {g : ℕ} [Fact g.Prime] {m : ℕ} (hm : 0 < m) {K 𝔨 : Type} [Field K] [Algebra (ZMod g) K] [Field 𝔨]
    (hK : Module.finrank (ZMod g) K = m) (ι : K →+* 𝔨) (Θ : 𝔨 →* ℂ) (hΘ : Inj Θ) (c : ℕ) (hc : Reg g m c) :
    GlobalTheory.Published.IsRegularChar g m ((Units.map (Θ.comp ι.toMonoidHom)) ^ c : Kˣ →* ℂˣ) := by
  intro i j hi hj hij
  have hg : g.Prime := Fact.out
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hm)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf ζ = g ^ m - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, natCard_of_finrank hm hK]
  have hv := DFunLike.congr_fun hij ζ
  simp only [MonoidHom.pow_apply, ← pow_mul] at hv
  rw [← map_pow, ← map_pow] at hv
  have hv' : Θ (ι ((ζ ^ (c * g ^ i) : Kˣ) : K)) = Θ (ι ((ζ ^ (c * g ^ j) : Kˣ) : K)) :=
    congrArg (fun u : ℂˣ => (u : ℂ)) hv
  have h1 := hΘ _ _ (by simp) (by simp) hv'
  have h2 : ζ ^ (c * g ^ i) = ζ ^ (c * g ^ j) := Units.ext (ι.injective h1)
  rw [pow_eq_pow_iff_modEq, hord] at h2
  rcases lt_trichotomy i j with h | h | h
  · exact (false_of_reg_of_mul_pow_modEq hg.pos hc h hj h2).elim
  · exact h
  · exact (false_of_reg_of_mul_pow_modEq hg.pos hc h hi h2.symm).elim

theorem UpperTheory.Gal.InertialTypesAlt.nameOf :
    NameOf := by
  intro g _ m hm F K 𝔨 _ _ _ _ _ hK r e ι Θ hΘ c hc
  refine ⟨(Units.map (Θ.comp ι.toMonoidHom)) ^ c, ?_, regular_character_of_pow hm hK ι Θ hΘ c hc, ?_⟩
  · intro u
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rfl
  · intro τ hτ y hy z hz
    set Y : (ZMod g)[X] := (y : Matrix (Fin m) (Fin m) (ZMod g)).charpoly with hYdef
    have hYm : Y.Monic := Matrix.charpoly_monic _
    have hYd : Y.natDegree = m := by
      rw [hYdef, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    let γ : GL (Fin m) F := Matrix.GeneralLinearGroup.map r.symm.toRingHom y
    have hyγ : Matrix.GeneralLinearGroup.map r.toRingHom γ = y := by
      ext i j
      simp [γ]
    have hγc : (γ : Matrix (Fin m) (Fin m) F).charpoly = Y.map r.symm.toRingHom := by
      rw [show (γ : Matrix (Fin m) (Fin m) F) = (y : Matrix (Fin m) (Fin m) (ZMod g)).map r.symm.toRingHom
        from rfl, Matrix.charpoly_map]
    have hirr : Irreducible (LinearMap.charpoly (Matrix.toLin' (γ : Matrix (Fin m) (Fin m) F))) := by
      rw [Matrix.charpoly_toLin', hγc]
      exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv r.symm)).mpr hy
    rw [← hyγ, hτ γ]
    delta cusp psiG
    congr 1
    refine (GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible F (Fin m → F) _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F (Θ.comp e) c).1 _ hirr).trans ?_
    rw [Matrix.charpoly_toLin', hγc]
    delta GlobalTheory.CuspGL.rootSum
    rw [Polynomial.map_map]
    have hP : (Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).Splits :=
      IsAlgClosed.splits _
    have hroots : (Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map e =
        ((Y.map (algebraMap (ZMod g) K)).map ι).roots := by
      rw [← hP.roots_map e, Polynomial.map_map, Polynomial.map_map]
      congr 2
      exact Subsingleton.elim _ _
    have hre : ((Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map
        fun α => (Θ.comp e) α ^ c) =
        (((Y.map ((algebraMap F (AlgebraicClosure F)).comp r.symm.toRingHom)).roots.map e).map
        fun β => Θ β ^ c) := by
      rw [Multiset.map_map]
      rfl
    rw [hre, hroots, roots_conj hm hK Y hy hYm hYd z hz ι, Multiset.map_map,
      Finset.sum_eq_multiset_sum, Finset.range_val]
    apply congrArg
    apply Multiset.map_congr rfl
    intro j _
    simp only [Function.comp_apply]
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_pow_eq_pow_val]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PPlaceEx
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.placeEx :
    PlaceEx := by
  intro K M Ω _ _ _ _ _ _ _ _ A v hv n P
  let f : 𝓞 M →+* A := ((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap M Ω) x.isIntegral_coe)
  let I : Ideal (𝓞 M) := (IsLocalRing.maximalIdeal A).comap f
  have hmem : ∀ x : 𝓞 M, x ∈ I ↔ A.valuation (algebraMap M Ω (x : M)) < 1 := fun x =>
    ValuationSubring.valuation_lt_one_iff A (f x)
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hval : A.valuation ((Ideal.absNorm v.asIdeal : ℕ) : Ω) < 1 := by
    have h := (hv ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K)).2 (Ideal.absNorm_mem v.asIdeal)
    simpa using h
  have hne : I ≠ ⊥ := by
    intro h0
    have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 M) ∈ I := (hmem _).2 (by simpa using hval)
    rw [h0, Ideal.mem_bot] at h1
    exact Nat.cast_ne_zero.2 hN0 h1
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n P
    ⟨I, Ideal.comap_isPrime _ _, hne⟩
  exact ⟨⟨I, Ideal.comap_isPrime _ _, hne⟩, fun x => (hmem x).symm, τ, hτ⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PPolBot
section
noncomputable section

open Polynomial

namespace UpperTheory.Gal.InertialTypesAlt

private theorem polBot_block (Q : ℕ) (x : ℂ) (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (c : ℕ → ℕ) (m : ℕ) :
    (((Multiset.range m).map fun j => ((1 : ℕ), ((c j : ℕ) : ZMod (Q - 1)))).map
      fun b => (X - C (x ^ b.2.val)) ^ b.1).prod = ∏ j ∈ Finset.range m, (X - C (x ^ c j)) := by
  haveI : NeZero (Q - 1) := ⟨by omega⟩
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod, Finset.range_val]
  congr 1
  apply Multiset.map_congr rfl
  intro j _
  simp only [Function.comp, pow_one, ZMod.val_natCast]
  rw [← pow_eq_pow_mod _ hx]

private theorem polBot_list (q Q : ℕ) (x : ℂ) (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (L : List (ℕ × ℕ)) :
    (((L.map fun p => (Multiset.range p.1).map fun j =>
      ((1 : ℕ), ((p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (Q - 1)))).sum).map
        fun b => (X - C (x ^ b.2.val)) ^ b.1).prod =
      (L.map fun p => ∏ j ∈ Finset.range p.1, (X - C (x ^ (p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)))))).prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, Multiset.map_add, Multiset.prod_add, ih, List.map_cons, List.prod_cons,
      polBot_block Q x hQ hx (fun j => p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1))) p.1]

theorem polBot : PolBot := by
  intro q Q L x hQ hx
  have h := polBot_list q Q x hQ hx L
  simpa [Lbl.pol, Lbl.blocks] using h

end UpperTheory.Gal.InertialTypesAlt
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PPolTop
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem polTop_sum (q : ℕ) (hq : 2 ≤ q) (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, p.1 = 1) :
    (L.map fun p => (Multiset.range p.1).map fun j =>
      ((1 : ℕ), ((p.2 * q ^ j * ((q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (q - 1)))).sum =
      ((L.map fun p => (p.1, ((p.2 : ℕ) : ZMod (q - 1))) : List _) : Multiset _) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have h1 : p.1 = 1 := hL p (by simp)
    have hpos : 0 < q - 1 := by omega
    rw [List.map_cons, List.sum_cons, ih (fun r hr => hL r (List.mem_cons_of_mem _ hr)), List.map_cons,
      h1]
    simp [Nat.div_self hpos]

theorem UpperTheory.Gal.InertialTypesAlt.polTop :
    PolTop := by
  intro b x hq hL hx
  have hpos : 0 < b.q - 1 := by omega
  have hb : b.blocks b.q = ((b.D ++ b.L).map fun p => (p.1, ((p.2 : ℕ) : ZMod (b.q - 1))) : List _) := by
    unfold Lbl.blocks
    rw [polTop_sum b.q hq b.L hL, List.map_append, ← Multiset.coe_add]
    simp [Nat.div_self hpos]
  refine ⟨hb, ?_⟩
  unfold Lbl.pol
  rw [hb, Multiset.map_coe, Multiset.prod_coe, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  rw [ZMod.val_natCast, ← pow_eq_pow_mod p.2 hx]
end

