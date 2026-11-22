import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0007
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0003
import GroundTheory.AutomorphicForms.SmoothRep
import GroundTheory.AutomorphicForms.HeckeIrreducible
import ReciprocityTheory.BurnsideSurjectivity.Burnside

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzPinB
section
noncomputable section

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain Polynomial

namespace DiscreteGroups.sglob.DzPin

theorem exists_maximal_above (L : Type) [Field L] [NumberField L] (p : ℕ) [hp : Fact p.Prime] :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ (p : 𝓞 L) ∈ Q := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 L)) ≤ Ideal.span {(p : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 L)).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) _ hker
  refine ⟨Q, hQ, ?_⟩
  have h : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 L)) Q := hQc ▸ Ideal.subset_span rfl
  simpa using h

theorem exists_iota (L : Type) [Field L] [NumberField L] (p : ℕ) [hp : Fact p.Prime]
    (Q : Ideal (𝓞 L)) [hQ : Q.IsMaximal] (hpQ : (p : 𝓞 L) ∈ Q) {N : ℕ} {μ : 𝓞 L}
    (hμ : IsPrimitiveRoot μ N) (hNQ : (N : 𝓞 L) ∉ Q) (K : Type) [Field K] [Fintype K]
    [Algebra (ZMod p) K] (hK : Fintype.card K = N + 1) : Nonempty (K →+* 𝓞 L ⧸ Q) := by
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  have hpz : ((p : ℕ) : 𝓞 L ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    exact hpQ
  haveI : CharP (𝓞 L ⧸ Q) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpz)
  letI : Algebra (ZMod p) (𝓞 L ⧸ Q) := ZMod.algebra _ p
  haveI := FiniteField.isSplittingField_sub K (ZMod p)
  have hμ' : IsPrimitiveRoot (Ideal.Quotient.mk Q μ) N := Stick.isPrimitiveRoot_mk Q hNQ hμ
  have hs : (map (algebraMap (ZMod p) (𝓞 L ⧸ Q)) (X ^ Fintype.card K - X)).Splits := by
    have e : (X ^ Fintype.card K - X : (𝓞 L ⧸ Q)[X]) = X * (X ^ N - C 1) := by
      rw [hK, C_1]; ring
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, e]
    exact Splits.X.mul (X_pow_sub_one_splits hμ')
  exact ⟨(IsSplittingField.lift K (X ^ Fintype.card K - X) hs).toRingHom⟩

theorem exists_emb (m : ℕ) [NeZero m] (L : Type) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {m} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) (c : ℂ)
    (hc : IsPrimitiveRoot c m) : ∃ φ : L →+* ℂ, φ ζ = c := by
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos m)
  let x : primitiveRoots m ℂ := ⟨c, (mem_primitiveRoots (NeZero.pos m)).2 hc⟩
  refine ⟨((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).symm x).toRingHom, ?_⟩
  have h := congrArg Subtype.val ((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).apply_symm_apply x)
  rw [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe] at h
  exact h

theorem exists_setup (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (K : Type) [Field K]
    [Fintype K] [Algebra (ZMod p) K] (hK : Fintype.card K = p ^ n) (ψ₀ : AddChar (ZMod p) Circle)
    (hψ₀ : ψ₀ ≠ 1) :
    ∃ (Q : HeightOneSpectrum (𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ)))
      (ω : MulChar K (𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ))) (Ω : Kˣ →* ℂˣ),
      Function.Injective Ω ∧
      ∀ t : ℕ, t.Coprime (p * (p ^ n - 1)) →
        ∃ (Φ : 𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ) →+* ℂ) (D : Stick.GSDatum p n K _ Q),
          Function.Injective Φ ∧ D.ω = ω ∧ Φ D.ζ = ((ψ₀ 1 : Circle) : ℂ) ∧
          ∀ z : Kˣ, Φ (ω z) = ((Ω z : ℂˣ) : ℂ) ^ t := by
  classical
  have hp2 := hp.out.two_le
  have hpn : p ≤ p ^ n := Nat.le_self_pow (by omega) p
  set N := p ^ n - 1 with hNdef
  have hN1 : N + 1 = p ^ n := by omega
  have hN0 : 0 < N := by omega
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.out.ne_zero (by omega)⟩
  haveI : NeZero (((p * N : ℕ)) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  haveI : IsCyclotomicExtension {p * N} ℚ (CyclotomicField (p * N) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (p * N) ℚ
    all_goals rfl
  have hζL := IsCyclotomicExtension.zeta_spec (p * N) ℚ (CyclotomicField (p * N) ℚ)
  let z : 𝓞 (CyclotomicField (p * N) ℚ) := hζL.toInteger
  have hzL : algebraMap (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ) z = IsCyclotomicExtension.zeta (p * N) ℚ (CyclotomicField (p * N) ℚ) := rfl
  have hz : IsPrimitiveRoot z (p * N) := hζL.toInteger_isPrimitiveRoot
  have hμ : IsPrimitiveRoot (z ^ p) N := hz.pow (NeZero.pos _) rfl
  obtain ⟨Q0, hQmax, hpQ⟩ := exists_maximal_above (CyclotomicField (p * N) ℚ) p
  have hNQ : (N : 𝓞 (CyclotomicField (p * N) ℚ)) ∉ Q0 := by
    intro h
    have h1 : (p : 𝓞 (CyclotomicField (p * N) ℚ)) ^ n ∈ Q0 := Ideal.pow_mem_of_mem _ hpQ n (by omega)
    have h2 : (1 : 𝓞 (CyclotomicField (p * N) ℚ)) = (p : 𝓞 (CyclotomicField (p * N) ℚ)) ^ n - N := by
      have e : ((N + 1 : ℕ) : 𝓞 (CyclotomicField (p * N) ℚ)) = ((p ^ n : ℕ) : 𝓞 (CyclotomicField (p * N) ℚ)) := by rw [hN1]
      push_cast at e
      rw [← e]; ring
    exact hQmax.ne_top ((Ideal.eq_top_iff_one _).2 (h2 ▸ Q0.sub_mem h1 h))
  obtain ⟨ι⟩ := exists_iota (CyclotomicField (p * N) ℚ) p Q0 hpQ hμ hNQ K (by omega)
  have hne : Q0 ≠ ⊥ := by
    rintro rfl
    exact (Nat.cast_ne_zero.mpr hp.out.ne_zero) ((Submodule.mem_bot _).1 hpQ)
  let Q : HeightOneSpectrum (𝓞 (CyclotomicField (p * N) ℚ)) := ⟨Q0, hQmax.isPrime, hne⟩
  obtain ⟨ω, hω1, hωN⟩ := Stick.exists_powResChar Q0 ι (n := N) (by rw [hK]) hμ
  have hdiv : (Fintype.card K - 1) / N = 1 := by rw [hK, ← hNdef, Nat.div_self hN0]
  have mk_ω : ∀ x, Ideal.Quotient.mk Q.asIdeal (ω x) = ι x := by
    intro x
    have h := hω1 x
    rw [hdiv, pow_one] at h
    exact h
  have hωu : ∀ y : Kˣ, ω y ^ N = 1 := by
    intro y; rw [← MulChar.pow_apply_coe, hωN, MulChar.one_apply_coe]

  let c : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((p * N : ℕ) : ℂ))
  have hc : IsPrimitiveRoot c (p * N) := Complex.isPrimitiveRoot_exp _ (NeZero.ne _)
  have hemb : ∀ t : ℕ, t.Coprime (p * N) →
      ∃ Φ : 𝓞 (CyclotomicField (p * N) ℚ) →+* ℂ, Function.Injective Φ ∧ Φ z = c ^ t := by
    intro t ht
    obtain ⟨φ, hφ⟩ := exists_emb (p * N) (CyclotomicField (p * N) ℚ) hζL (c ^ t) (hc.pow_of_coprime t ht)
    exact ⟨φ.comp (algebraMap (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ)), φ.injective.comp (IsFractionRing.injective (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ)),
      by rw [RingHom.comp_apply, hzL, hφ]⟩
  obtain ⟨Φ1, hΦ1i, hΦ1z⟩ := hemb 1 (Nat.coprime_one_left _)

  let Ω : Kˣ →* ℂˣ := (Units.map Φ1.toMonoidHom).comp ω.toUnitHom
  have hΩ : ∀ y : Kˣ, ((Ω y : ℂˣ) : ℂ) = Φ1 (ω y) := fun y => rfl
  refine ⟨Q, ω, Ω, ?_, ?_⟩
  · intro y₁ y₂ h
    have h1 : Φ1 (ω y₁) = Φ1 (ω y₂) := by rw [← hΩ, ← hΩ, h]
    have h2 := congrArg (Ideal.Quotient.mk Q.asIdeal) (hΦ1i h1)
    rw [mk_ω, mk_ω] at h2
    exact Units.ext (ι.injective h2)
  · intro t ht
    obtain ⟨Φ, hΦi, hΦz⟩ := hemb t ht

    have hpow : ∀ x : 𝓞 (CyclotomicField (p * N) ℚ), x ^ N = 1 → Φ x = Φ1 x ^ t := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one hx
      simp only [map_pow, hΦz, hΦ1z, pow_one]
      ring

    have hw : IsPrimitiveRoot ((ψ₀ 1 : Circle) : ℂ) p := by
      have h1 : ((ψ₀ 1 : Circle) : ℂ) ^ p = 1 := by
        rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, nsmul_one, ZMod.natCast_self,
          AddChar.map_zero_eq_one, Circle.coe_one]
      have h2 : ((ψ₀ 1 : Circle) : ℂ) ≠ 1 := by
        intro h
        apply hψ₀
        refine AddChar.ext_iff.2 fun y => Circle.coe_injective ?_
        rw [addChar_apply_eq_pow, h, one_pow, AddChar.one_apply, Circle.coe_one]
      have h3 := IsPrimitiveRoot.orderOf ((ψ₀ 1 : Circle) : ℂ)
      rwa [orderOf_eq_prime h1 h2] at h3
    have hzN : IsPrimitiveRoot (Φ (z ^ N)) p := by
      rw [map_pow, hΦz]
      exact (hc.pow_of_coprime t ht).pow (NeZero.pos _) (by ring)
    obtain ⟨j, -, hj⟩ := hzN.eq_pow_of_pow_eq_one hw.pow_eq_one
    have hΦζ : Φ ((z ^ N) ^ j) = ((ψ₀ 1 : Circle) : ℂ) := by rw [map_pow, hj]
    have hprim : IsPrimitiveRoot ((z ^ N) ^ j) p :=
      IsPrimitiveRoot.of_map_of_injective (f := Φ) (by rw [hΦζ]; exact hw) hΦi
    let D : Stick.GSDatum p n K (𝓞 (CyclotomicField (p * N) ℚ)) Q :=
      { card_eq := hK, ι := ι, ω := ω, mk_ω := mk_ω, ζ := (z ^ N) ^ j, prim := hprim }
    refine ⟨Φ, D, hΦi, rfl, hΦζ, fun y => ?_⟩
    rw [hpow _ (hωu y), hΩ]

theorem nm_eq {g : ℕ} [hg : Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod g) K] (hK : Fintype.card K = g ^ n) (Ω : Kˣ →* ℂˣ) (m : ℕ) :
    ((Ω.comp (Units.map (algebraMap (ZMod g) K).toMonoidHom)) ^ m).comp
        (Units.map (Algebra.norm (ZMod g) : K →* ZMod g)) = Ω ^ ((g ^ n - 1) / (g - 1) * m) := by
  have hg2 := hg.out.two_le
  have hfin : Module.finrank (ZMod g) K = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hK] at h
    exact (Nat.pow_right_injective hg2 h).symm
  refine MonoidHom.ext fun z => ?_
  have hz : Units.map (algebraMap (ZMod g) K).toMonoidHom
      (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z) = z ^ ((g ^ n - 1) / (g - 1)) := by
    refine Units.ext ?_
    simp only [Units.coe_map, Units.val_pow_eq_pow_val, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe]
    rw [FiniteField.algebraMap_norm_eq_prod_pow, Finset.prod_pow_eq_pow_sum, Nat.card_zmod, hfin,
      Nat.geomSum_eq hg2]
  rw [MonoidHom.comp_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, hz, map_pow, ← pow_mul,
    MonoidHom.pow_apply]

end DiscreteGroups.sglob.DzPin
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.InCellMulRightIff
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {S : Subgroup (GL (Fin m) k)}

theorem inCell_mul_left_iff (p₀ : parab k (eOne m)) (g : GL (Fin m) k) :
    InCell S ((p₀ : GL (Fin m) k) * g) ↔ InCell S g := by
  constructor
  · rintro ⟨p, y, hy, e⟩
    refine ⟨p₀⁻¹ * p, y, hy, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc g = (p₀ : GL (Fin m) k)⁻¹ * ((p₀ : GL (Fin m) k) * g) := by group
      _ = _ := by rw [e]; group
  · rintro ⟨p, y, hy, e⟩
    exact ⟨p₀ * p, y, hy, by rw [e]; simp only [Subgroup.coe_mul]; group⟩

theorem inCell_mul_right_iff {s : GL (Fin m) k} (hs : s ∈ S) (g : GL (Fin m) k) :
    InCell S (g * s) ↔ InCell S g := by
  constructor
  · rintro ⟨p, y, hy, e⟩
    refine ⟨p, y * s⁻¹, S.mul_mem hy (S.inv_mem hs), ?_⟩
    calc g = g * s * s⁻¹ := by group
      _ = _ := by rw [e]; group
  · rintro ⟨p, y, hy, e⟩
    exact ⟨p, y * s, S.mul_mem hy hs, by rw [e]; group⟩

variable (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)
include hS4

theorem cellFun_mul_left (p₀ : parab k (eOne m)) (g : GL (Fin m) k) :
    cellFun S ((p₀ : GL (Fin m) k) * g) = dl p₀ * cellFun S g := by
  by_cases h : InCell S g
  · obtain ⟨p, y, hy, rfl⟩ := h
    have e : (p₀ : GL (Fin m) k) * (p * wRev k m * y) = ((p₀ * p : parab k (eOne m)) : GL (Fin m) k) * wRev k m * y := by
      simp only [Subgroup.coe_mul]; group
    rw [e, cellFun_eq hS4 _ hy, cellFun_eq hS4 _ hy, dl_mul, Units.val_mul]
  · have h' : ¬ InCell S ((p₀ : GL (Fin m) k) * g) := fun h' => h ((inCell_mul_left_iff p₀ g).1 h')
    rw [cellFun, dif_neg h', cellFun, dif_neg h, mul_zero]

theorem cellFun_mul_right {s : GL (Fin m) k} (hs : s ∈ S) (g : GL (Fin m) k) :
    cellFun S (g * s) = cellFun S g := by
  by_cases h : InCell S g
  · obtain ⟨p, y, hy, rfl⟩ := h
    have e : (p : GL (Fin m) k) * wRev k m * y * s = p * wRev k m * (y * s) := by group
    rw [e, cellFun_eq hS4 _ (S.mul_mem hy hs), cellFun_eq hS4 _ hy]
  · rw [cellFun, dif_neg (fun h' => h ((inCell_mul_right_iff hs g).1 h')), cellFun, dif_neg h]

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvUnifA
section
noncomputable section

namespace DiscreteGroups.sglob.LConvU

open GroundTheory.Automorphic Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

include hρ hKc hKo

theorem fixedProj_eq_avg {L : Subgroup G} (hLK : L ≤ K) (hLo : IsOpen (L : Set G)) :
    ∃ (N : ℕ) (r : Fin N → G), 0 < N ∧ (∀ i, r i ∈ K) ∧
      ∀ v : V, v ∈ fixedVectors ρ L →
        (fixedProj ρ hρ hKc hKo v : V) = (N : ℂ)⁻¹ • ∑ i, ρ (r i) v := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hHo : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) := hLo.preimage continuous_subtype_val
  have : Finite (K ⧸ L.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hHo
  let _ : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  have hNpos : 0 < Fintype.card (K ⧸ L.subgroupOf K) :=
    Fintype.card_pos_iff.mpr ⟨QuotientGroup.mk (1 : K)⟩
  let eQ := Fintype.equivFin (K ⧸ L.subgroupOf K)
  refine ⟨Fintype.card (K ⧸ L.subgroupOf K), fun i => ((Quotient.out (eQ.symm i) : K) : G), hNpos,
    fun i => (Quotient.out (eQ.symm i)).2, ?_⟩
  intro v hv
  obtain ⟨s, hs⟩ : ∃ s : V, s = ∑ q : K ⧸ L.subgroupOf K, ρ ((Quotient.out q : K) : G) v := ⟨_, rfl⟩
  have hreidx : ∑ i, ρ ((Quotient.out (eQ.symm i) : K) : G) v = s := by
    rw [hs]
    exact Fintype.sum_equiv eQ.symm _ _ (fun _ => rfl)
  have hsK : s ∈ fixedVectors ρ K := by
    intro k hk
    have key : ∀ q : K ⧸ L.subgroupOf K, ρ k (ρ ((Quotient.out q : K) : G) v) =
        ρ ((Quotient.out ((⟨k, hk⟩ : K) • q) : K) : G) v := by
      intro q
      rw [← Module.End.mul_apply, ← map_mul]
      have h1 : (((⟨k, hk⟩ : K) * Quotient.out q : K) : G) = k * ((Quotient.out q : K) : G) := rfl
      rw [← h1]
      apply act_eq_of_mk_eq ρ hv
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    rw [hs, map_sum, Finset.sum_congr rfl (fun q _ => key q)]
    exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ (fun _ => rfl)
  have hsub : s - ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • v ∈ coinvariantsKer ρ K := by
    have h1 : s - ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • v =
        ∑ q : K ⧸ L.subgroupOf K, (ρ ((Quotient.out q : K) : G) v - v) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul, hs]
    rw [h1]
    exact Submodule.sum_mem _ fun q _ => sub_mem_coinvariantsKer (Quotient.out q).2 v
  have h1 : (fixedProj ρ hρ hKc hKo s : V) = s := fixedProj_apply_of_mem hρ hKc hKo hsK
  have h2 := fixedProj_apply_of_mem_coinvariantsKer hρ hKc hKo hsub
  rw [map_sub, map_smul, sub_eq_zero] at h2
  have h3 : ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • (fixedProj ρ hρ hKc hKo v : V) = s := by
    rw [← h1, h2, Submodule.coe_smul]
  rw [hreidx, ← h3, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hNpos.ne'), one_smul]

theorem map_fixedProj_of_invariant {U : Type*} [AddCommGroup U] [Module ℂ U] (f : V →ₗ[ℂ] U)
    (v : V) (hf : ∀ k ∈ K, f (ρ k v) = f v) : f (fixedProj ρ hρ hKc hKo v : V) = f v := by
  have hLo : IsOpen ((K ⊓ stabilizerOf ρ v : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter (hρ v)
  obtain ⟨N, r, hN, hr, h⟩ := fixedProj_eq_avg hρ hKc hKo (L := K ⊓ stabilizerOf ρ v) inf_le_left hLo
  rw [h v (fun l hl => hl.2), map_smul, map_sum, Finset.sum_congr rfl (fun i _ => hf (r i) (hr i)),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_smul]

variable (ρ) in

def hop (g : G) : Module.End ℂ (fixedVectors ρ K) :=
  (fixedProj ρ hρ hKc hKo) ∘ₗ (ρ g) ∘ₗ (fixedVectors ρ K).subtype

theorem hop_apply (g : G) (w : fixedVectors ρ K) :
    hop ρ hρ hKc hKo g w = fixedProj ρ hρ hKc hKo (ρ g w) := rfl

theorem hop_of_mem {κ : G} (hκ : κ ∈ K) : hop ρ hρ hKc hKo κ = 1 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [hop_apply, fixedProj_apply_act hρ hKc hKo hκ, Module.End.one_apply,
    fixedProj_apply_of_mem hρ hKc hKo w.2]

theorem hop_one : hop ρ hρ hKc hKo 1 = 1 := hop_of_mem hρ hKc hKo K.one_mem

theorem hop_mul {g h : G}
    (H : ∀ w ∈ fixedVectors ρ K, ∀ κ ∈ K,
      fixedProj ρ hρ hKc hKo (ρ (g * κ * h) w) = fixedProj ρ hρ hKc hKo (ρ (g * h) w)) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h = hop ρ hρ hKc hKo (g * h) := by
  refine LinearMap.ext fun w => ?_
  show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) =
    fixedProj ρ hρ hKc hKo (ρ (g * h) w)
  have key := map_fixedProj_of_invariant hρ hKc hKo ((fixedProj ρ hρ hKc hKo) ∘ₗ ρ g) (ρ h w)
    (fun κ hκ => by
      simp only [LinearMap.comp_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, H w w.2 κ hκ,
        map_mul, Module.End.mul_apply])
  simp only [LinearMap.comp_apply] at key
  rw [key, map_mul, Module.End.mul_apply]

theorem hop_mul_mem_span (g h : G) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
  let L : Subgroup G := K ⊓ K.comap (MulAut.conj h⁻¹).toMonoidHom
  have hLo : IsOpen (L : Set G) := by
    have hc : Continuous fun x : G => h⁻¹ * x * h⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hKo.inter (hKo.preimage hc)
  obtain ⟨N, r, hN, -, hav⟩ := fixedProj_eq_avg hρ hKc hKo (L := L) inf_le_left hLo
  have hfix : ∀ w : fixedVectors ρ K, ρ h (w : V) ∈ fixedVectors ρ L := by
    intro w l hl
    have hl2 : h⁻¹ * l * h ∈ K := by
      have := hl.2
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
    calc ρ l (ρ h w) = ρ h (ρ (h⁻¹ * l * h) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]; congr 2; group
      _ = ρ h w := by rw [w.2 _ hl2]
  have heq : hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h =
      (N : ℂ)⁻¹ • ∑ i, hop ρ hρ hKc hKo (g * r i * h) := by
    refine LinearMap.ext fun w => ?_
    show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) = _
    rw [hav _ (hfix w), map_smul, map_smul, map_sum, map_sum, LinearMap.smul_apply,
      LinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = fixedProj ρ hρ hKc hKo (ρ (g * r i * h) w)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩)

theorem span_hop_mul_mem {a b : Module.End ℂ (fixedVectors ρ K)}
    (ha : a ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)))
    (hb : b ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo))) :
    a * b ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      exact hop_mul_mem_span hρ hKc hKo g h
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem span_hop_eq_top [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    [Nontrivial (fixedVectors ρ K)] :
    Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) = ⊤ := by
  have hone : (1 : Module.End ℂ (fixedVectors ρ K)) ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
    rw [← hop_one hρ hKc hKo]; exact Submodule.subset_span ⟨1, rfl⟩
  let A : Subalgebra ℂ (Module.End ℂ (fixedVectors ρ K)) :=
    Submodule.toSubalgebra _ hone (fun a b ha hb => span_hop_mul_mem hρ hKc hKo ha hb)
  have hirr : ∀ U : Submodule ℂ (fixedVectors ρ K),
      (∀ a : A, ∀ w ∈ U, A.val a w ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    right
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hT : ∀ g, hop ρ hρ hKc hKo g u ∈ U := fun g =>
      hU ⟨hop ρ hρ hKc hKo g, Submodule.subset_span ⟨g, rfl⟩⟩ u huU
    rw [eq_top_iff]
    intro w _
    have hu0' : (u : V) ≠ 0 := fun h => hu0 (Subtype.ext h)
    have hw := HeckeAlgebra.mem_span_orbit (ρ := ρ) hu0' (w : V)
    have hww : w = fixedProj ρ hρ hKc hKo (w : V) :=
      Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo w.2).symm
    rw [hww]
    have hle : Submodule.map (fixedProj ρ hρ hKc hKo)
        (Submodule.span ℂ (Set.range fun g => ρ g (u : V))) ≤ U := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact hT g
    exact hle ⟨_, hw, rfl⟩
  have hsurj := ReciprocityTheory.GC.burnside_surj_of_irred (k := ℂ) A.val hirr
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := hsurj x
  rw [← ha]
  exact a.2

end DiscreteGroups.sglob.LConvU
end
end

