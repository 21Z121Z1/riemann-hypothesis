import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0026
import Development.AutomorphicArithmetic.LocalEmbeddings.CoinvFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0013

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ArtinEl
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ellC_index (l : ℕ) [hl : Fact l.Prime] (M : Type) [CommGroup M] [Finite M] :
    ∃ n : ℕ, (ellC l M).index = l ^ n := by
  have hp : IsPGroup l (M ⧸ ellC l M) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' l hl.out.ne_one
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have h1 : orderOf (x ^ l ^ e) ∣ m := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, ← he, pow_orderOf_eq_one])
    exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm).symm
  exact IsPGroup.iff_card.1 hp

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isUnit_iff_val (p : 𝒪[k]) : IsUnit p ↔ valuation k (p : k) = 1 :=
  (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one

private theorem unif_of_ord {x : kˣ} (hx : ord k x = 1) : IsUnif x := by
  have hv : valuation k (x : k) = uniformizer k := by
    obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact uniformizer_ne_zero hy.symm
    have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
    have h2 := ord_mul k (x * (Units.mk0 y hy0)⁻¹) (Units.mk0 y hy0)
    rw [inv_mul_cancel_right, hx, h1] at h2
    have h3 := ord_eq_zero_iff.1 (show ord k (x * (Units.mk0 y hy0)⁻¹) = 0 by omega)
    have h4 : (x : k) = ((x * (Units.mk0 y hy0)⁻¹ : kˣ) : k) * y := by simp [hy0]
    rw [h4, map_mul, h3, one_mul, hy]
  have hlt : valuation k (x : k) < 1 := hv ▸ uniformizer_lt_one
  refine ⟨⟨x, hlt.le⟩, ⟨fun h => hlt.ne ((isUnit_iff_val _).1 h), fun a b hab => ?_⟩, rfl⟩
  by_contra hn
  rw [not_or, isUnit_iff_val, isUnit_iff_val] at hn
  have ha : valuation k (a : k) < 1 := lt_of_le_of_ne a.2 hn.1
  have hb : valuation k (b : k) ≤ uniformizer k := le_uniformizer_iff.2 (lt_of_le_of_ne b.2 hn.2)
  have h5 : valuation k (x : k) = valuation k (a : k) * valuation k (b : k) := by
    rw [← map_mul]; exact congrArg (fun z : 𝒪[k] => valuation k (z : k)) hab
  have h6 : valuation k (a : k) * valuation k (b : k) < 1 * uniformizer k :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ha hb zero_le' (zero_lt_iff.2 uniformizer_ne_zero)
  rw [← h5, hv, one_mul] at h6
  exact lt_irrefl _ h6

private theorem exists_lift {H : Type} [Group H] [TopologicalSpace H] (f : H →* kˣ) (hf : Continuous f)
    (h1 : ∀ s, valuation k (f s : k) = 1) :
    ∃ g : H →* 𝒪[k]ˣ, (∀ s, Units.map (algebraMap 𝒪[k] k).toMonoidHom (g s) = f s) ∧
      IsOpen (((Units.map (residue 𝒪[k]).toMonoidHom).comp g).ker : Set H) := by
  let g0 : H →* 𝒪[k] :=
    { toFun := fun s => ⟨f s, (h1 s).le⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp) }
  refine ⟨g0.toHomUnits, fun s => Units.ext rfl, ?_⟩
  have e : (((Units.map (residue 𝒪[k]).toMonoidHom).comp g0.toHomUnits).ker : Set H) =
      (fun s => (f s : k) - 1) ⁻¹' {x : k | valuation k x < 1} := by
    ext s
    have e1 : (s ∈ ((Units.map (residue 𝒪[k]).toMonoidHom).comp g0.toHomUnits).ker) ↔ residue 𝒪[k] (g0 s - 1) = 0 := by
      rw [MonoidHom.mem_ker, Units.ext_iff, map_sub, map_one, sub_eq_zero]; rfl
    rw [SetLike.mem_coe, e1, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_val]
    exact ⟨fun h => lt_of_le_of_ne (g0 s - 1).2 h, fun h => ne_of_lt h⟩
  rw [e]
  refine IsOpen.preimage ((Units.continuous_val.comp hf).sub continuous_const) ?_
  simpa using IsValuativeTopology.isOpen_ball (R := k) 1

end Loc

theorem UpperTheory.V.Pa.Lev.artinEl :
    GlobalTheory.Published.TameLocal → ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (a : Weil hB →* (w.adicCompletion E)ˣ), IsLocalArtin hB a → ∀ fr τ : G E Ω, fr ∈ Dec (F := E) Bq → IsFrob (F := E) Bq (normV w) fr⁻¹ → GlobalTheory.TameQuot.IsProGen E Bq l τ → resCard (w.adicCompletion E) = normV w ∧ ∃ (h1 : fr ∈ Weil hB) (h2 : τ ∈ Weil hB), IsUnif (a ⟨fr, h1⟩) ∧ IsGenMod _ (ellC l _) (a ⟨τ, h2⟩) ∧ (∀ (σ : G E Ω) (h3 : σ ∈ Weil hB), σ ∈ GlobalTheory.TameQuot.ineKer E Bq l → a ⟨σ, h3⟩ ∈ unitsC _ (ellC l _)) ∧ (τ ^ normV w)⁻¹ * (fr⁻¹ * τ * fr) ∈ GlobalTheory.TameQuot.ineKer E Bq l := by
  intro hT l _ E Ω _ _ _ _ _ Bq w hB hl a ha fr τ hfr hF hτ
  have h0 : fr⁻¹ ∈ Weil hB := mem_Weil_of_isFrob hB hF
  have h1 : fr ∈ Weil hB := (inv_mem_iff (H := Weil hB)).1 h0
  have hval : ∀ s : Ine (F := E) Bq,
      valuation (w.adicCompletion E) ((a.comp (ineIncl hB) s : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := fun s => by
    refine ord_eq_zero_iff.1 ?_
    rw [MonoidHom.comp_apply, ha.ord_eq, deg_eq_zero_iff.2 s.2, neg_zero]
  obtain ⟨g, hg, hop⟩ := exists_lift (a.comp (ineIncl hB)) ha.cont hval
  set r := (Units.map (residue 𝒪[w.adicCompletion E]).toMonoidHom).comp g with hr
  have hrs : Function.Surjective r := fun y => by
    obtain ⟨d, rfl⟩ := surjective_units_map_of_local_ringHom (residue 𝒪[w.adicCompletion E]) residue_surjective
      inferInstance y
    obtain ⟨s, hs⟩ := ha.surj (Units.map (algebraMap 𝒪[w.adicCompletion E] (w.adicCompletion E)).toMonoidHom d)
    have hs0 : deg s = 0 := by
      have := ha.ord_eq s
      rw [hs, ord_eq_zero ((isUnit_iff_val _).1 d.isUnit)] at this
      omega
    refine ⟨⟨s, deg_eq_zero_iff.1 hs0⟩, ?_⟩
    have h5 := (hg ⟨s, deg_eq_zero_iff.1 hs0⟩).trans hs
    have h6 : g ⟨s, deg_eq_zero_iff.1 hs0⟩ = d := Units.ext (Subtype.ext (congrArg Units.val h5))
    rw [hr, MonoidHom.comp_apply, h6]
  have hopen : ∀ C : Subgroup 𝓀[w.adicCompletion E]ˣ, IsOpen ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq)) :=
    fun C => Subgroup.isOpen_mono (fun s hs => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hs]; exact C.one_mem) hop
  have hker : GlobalTheory.TameQuot.proKer l (Ine (F := E) Bq) ≤ (ellC l _).comap r := fun s hs =>
    GlobalTheory.TameQuot.mem_proKer.1 hs _ inferInstance (hopen _) (by
      rw [Subgroup.index_comap_of_surjective _ hrs]; exact ellC_index l _)
  refine ⟨resCard_eq_normV _, h1, Ine_le_Weil hB hτ.1, unif_of_ord ?_, ⟨g ⟨τ, hτ.1⟩, hg _, ?_⟩, fun σ h3 hσ => ?_, ?_⟩
  · have h2 : deg (⟨fr, h1⟩ : Weil hB)⁻¹ = 1 := deg_eq_one_iff.2 hF
    rw [ha.ord_eq, ← deg_inv, h2]
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨s, rfl⟩ := hrs y
    set C := Subgroup.zpowers (r ⟨τ, hτ.1⟩) ⊔ ellC l _ with hC
    have hle : Subgroup.zpowers τ ⊔ GlobalTheory.TameQuot.ineKer E Bq l ≤ (C.comap r).map (Ine (F := E) Bq).subtype := by
      refine sup_le ((Subgroup.zpowers_le).2 ⟨⟨τ, hτ.1⟩, ?_, rfl⟩) (Subgroup.map_mono (hker.trans ?_))
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.comap_mono le_sup_right
    have h4 : (s : G E Ω) ∈ closure (Subtype.val '' ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq))) :=
      closure_mono (fun z hz => hle hz) (hτ.2 s.2)
    have h5 : s ∈ closure ((C.comap r : Subgroup _) : Set (Ine (F := E) Bq)) := closure_subtype.2 h4
    rw [(Subgroup.isClosed_of_isOpen _ (hopen C)).closure_eq] at h5
    exact h5
  · obtain ⟨s, hs, rfl⟩ := hσ
    exact ⟨g s, hker hs, hg s⟩
  · have hτd : τ ∈ Dec (F := E) Bq := Weil_le_Dec hB (Ine_le_Weil hB hτ.1)
    have := ((hT.1 E Ω l Bq w hB hl).2.2.2.2.2 ⟨fr⁻¹, inv_mem hfr⟩ ⟨τ, hτd⟩ hF hτ).2.1
    simpa using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.DelIso
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Pa.Lev

private theorem di_card (l : ℕ) [hl : Fact l.Prime] (G : Type) [CommGroup G] [Finite G] :
    Nat.card (G ⧸ ellC l G) = l ^ padicValNat l (Nat.card G) := by
  classical
  have hl' := hl.out
  have hQ : IsPGroup l (G ⧸ ellC l G) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨b, c, hc, hbc⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' l hl'.ne_one
      refine ⟨b, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show (orderOf (x ^ l ^ b)).Coprime l
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hl'.ne_zero) ⟨c, hbc⟩, hbc,
        Nat.mul_div_cancel_left _ (pow_pos hl'.pos _)]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl').2 hc)
  have hC : ¬ l ∣ Nat.card (ellC l G) := by
    intro hd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' l hd
    have h1 : (orderOf (y : G)).Coprime l := y.2
    rw [Subgroup.orderOf_coe, hy] at h1
    exact hl'.one_lt.ne' ((Nat.coprime_self l).1 h1)
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hpos : Nat.card (ellC l G) ≠ 0 := Nat.card_pos.ne'
  rw [hk, Subgroup.card_eq_card_quotient_mul_card_subgroup (ellC l G), hk,
    padicValNat.mul (pow_ne_zero _ hl'.ne_zero) hpos, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hC, add_zero]

private theorem di_cyc (l : ℕ) [Fact l.Prime] (G : Type) [CommGroup G] [Finite G] (x : G)
    (hx : Subgroup.zpowers x ⊔ ellC l G = ⊤) (a : ℕ) (ha : a = padicValNat l (Nat.card G)) :
    ∃ e : Multiplicative (ZMod (l ^ a)) ≃* G ⧸ ellC l G, e (Multiplicative.ofAdd 1) = (x : G ⧸ ellC l G) := by
  classical
  have hl' := (Fact.out : l.Prime)
  haveI : NeZero (l ^ a) := ⟨pow_ne_zero _ hl'.ne_zero⟩
  have hcard : Nat.card (G ⧸ ellC l G) = l ^ a := by rw [ha]; exact di_card l G
  let ψ : ZMod (l ^ a) →+ Additive (G ⧸ ellC l G) :=
    ZMod.lift (l ^ a) ⟨zmultiplesHom _ (Additive.ofMul (x : G ⧸ ellC l G)), by
      rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, ← hcard, pow_card_eq_one', ofMul_one]⟩
  let Φ : Multiplicative (ZMod (l ^ a)) →* G ⧸ ellC l G := AddMonoidHom.toMultiplicativeLeft ψ
  have hΦ : ∀ m : ℤ, Φ (Multiplicative.ofAdd (m : ZMod (l ^ a))) = (x : G ⧸ ellC l G) ^ m := by
    intro m
    show Additive.toMul (ψ (m : ZMod (l ^ a))) = _
    rw [ZMod.lift_coe]
    show Additive.toMul (zmultiplesHom _ (Additive.ofMul (x : G ⧸ ellC l G)) m) = _
    rw [zmultiplesHom_apply, toMul_zsmul, toMul_ofMul]
  have hsurj : Function.Surjective Φ := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H g =>
      have hg : g ∈ Subgroup.zpowers x ⊔ ellC l G := hx ▸ Subgroup.mem_top g
      obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.1 hg
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      refine ⟨Multiplicative.ofAdd (m : ZMod (l ^ a)), ?_⟩
      rw [hΦ, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff v).2 hv, mul_one, QuotientGroup.mk_zpow]
  have hbij : Function.Bijective Φ := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [hcard]
    show Nat.card (ZMod (l ^ a)) ≤ _
    rw [Nat.card_zmod]
  refine ⟨MulEquiv.ofBijective Φ hbij, ?_⟩
  have h1 := hΦ 1
  rw [Int.cast_one, zpow_one] at h1
  exact h1

private theorem di_pi {q n : ℕ} (G : Fin q → Type) [∀ j, Group (G j)] (H K : ∀ j, Subgroup (G j))
    (Z : Fin q → Type) [∀ j, Group (Z j)] (f : ∀ j, H j →* (Fin n → Z j)) (hs : ∀ j, Function.Surjective (f j))
    (hk : ∀ j (g : H j), f j g = 1 ↔ (g : G j) ∈ K j)
    [((Subgroup.pi Set.univ K).subgroupOf (Subgroup.pi Set.univ H)).Normal] :
    ∃ e : (∀ p : Fin q × Fin n, Z p.1) ≃*
        (Subgroup.pi Set.univ H ⧸ (Subgroup.pi Set.univ K).subgroupOf (Subgroup.pi Set.univ H)),
      ∀ j i (z : Z j) (t : H j), f j t = Pi.mulSingle i z → ∃ g : Subgroup.pi Set.univ H,
        (g : ∀ j, G j) = Pi.mulSingle j (t : G j) ∧ e (Pi.mulSingle (j, i) z) = g := by
  classical
  let Φ : Subgroup.pi Set.univ H →* (∀ p : Fin q × Fin n, Z p.1) :=
    Pi.monoidHom fun p => (Pi.evalMonoidHom _ p.2).comp ((f p.1).comp
      (((Pi.evalMonoidHom G p.1).comp (Subgroup.pi Set.univ H).subtype).codRestrict (H p.1)
        fun g => (Subgroup.mem_pi _).1 g.2 p.1 (Set.mem_univ _)))
  have hΦ : ∀ (g : Subgroup.pi Set.univ H) (p : Fin q × Fin n),
      Φ g p = f p.1 ⟨(g : ∀ j, G j) p.1, (Subgroup.mem_pi _).1 g.2 p.1 (Set.mem_univ _)⟩ p.2 := fun g p => rfl
  have hsurj : Function.Surjective Φ := by
    intro z
    choose t ht using fun j => hs j (fun i => z (j, i))
    refine ⟨⟨fun j => (t j : G j), (Subgroup.mem_pi _).2 fun j _ => (t j).2⟩, funext fun p => ?_⟩
    rw [hΦ]
    exact congrFun (ht p.1) p.2
  have hker : Φ.ker = (Subgroup.pi Set.univ K).subgroupOf (Subgroup.pi Set.univ H) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_pi]
    constructor
    · intro h j _
      refine (hk j ⟨_, (Subgroup.mem_pi _).1 g.2 j (Set.mem_univ _)⟩).1 (funext fun i => ?_)
      have := congrFun h (j, i)
      rw [hΦ] at this
      exact this
    · intro h
      funext p
      rw [hΦ]
      exact congrFun ((hk p.1 ⟨_, (Subgroup.mem_pi _).1 g.2 p.1 (Set.mem_univ _)⟩).2 (h p.1 (Set.mem_univ _))) p.2
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective Φ hsurj).symm.trans (QuotientGroup.quotientMulEquivOfEq hker), ?_⟩
  intro j i z t ht
  have hmemg : Pi.mulSingle j (t : G j) ∈ Subgroup.pi Set.univ H := by
    refine (Subgroup.mem_pi _).2 fun j' _ => ?_
    by_cases h : j' = j
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact t.2
    · rw [Pi.mulSingle_eq_of_ne h]
      exact one_mem _
  have hΦg : Φ ⟨_, hmemg⟩ = Pi.mulSingle (j, i) z := by
    funext p
    obtain ⟨j', i'⟩ := p
    rw [hΦ]
    by_cases h : j' = j
    · subst h
      have key : f j' ⟨Pi.mulSingle j' (t : G j') j', (Subgroup.mem_pi _).1 hmemg j' (Set.mem_univ _)⟩ = f j' t := by
        congr 1
        exact Subtype.ext (Pi.mulSingle_eq_same _ _)
      rw [key, ht]
      by_cases hi : i' = i
      · subst hi
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne (fun hp => hi (congrArg Prod.snd hp))]
    · have key : f j' ⟨Pi.mulSingle j (t : G j) j', (Subgroup.mem_pi _).1 hmemg j' (Set.mem_univ _)⟩ = 1 := by
        rw [show (⟨Pi.mulSingle j (t : G j) j', (Subgroup.mem_pi _).1 hmemg j' (Set.mem_univ _)⟩ : H j') = 1 from
          Subtype.ext (Pi.mulSingle_eq_of_ne h _), map_one]
      rw [key, Pi.mulSingle_eq_of_ne (fun hp => h (congrArg Prod.fst hp))]
      rfl
  refine ⟨⟨_, hmemg⟩, rfl, ?_⟩
  have hs1 : (QuotientGroup.quotientKerEquivOfSurjective Φ hsurj).symm (Φ ⟨_, hmemg⟩) =
      ((⟨_, hmemg⟩ : Subgroup.pi Set.univ H) : Subgroup.pi Set.univ H ⧸ Φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, ← hΦg, hs1, QuotientGroup.quotientMulEquivOfEq_mk]

private theorem di_loc (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n l : ℕ)
    [Fact l.Prime] (δ : kˣ) (hδ : IsGenMod k (ellC l _) δ) :
    ∃ f : iwC k n ⊤ →* (Fin n → Multiplicative (ZMod (l ^ padicValNat l (resCard k - 1)))), Function.Surjective f ∧
      (∀ g : iwC k n ⊤, f g = 1 ↔ (g : GL (Fin n) k) ∈ iwC k n (ellC l _)) ∧
      ∀ i, ∃ t : iwC k n ⊤, (t : GL (Fin n) k) = diagT k (Fin n) (Pi.mulSingle i δ) ∧
        f t = Pi.mulSingle i (Multiplicative.ofAdd 1) := by
  classical
  obtain ⟨d, hdδ, hgen⟩ := hδ
  obtain ⟨f0, hs0, hk0, hv0⟩ := iwQuot k n (ellC l 𝓀[k]ˣ)
  obtain ⟨e, he⟩ := di_cyc l _ _ hgen (padicValNat l (resCard k - 1)) (by rw [Nat.card_units]; rfl)
  refine ⟨(MonoidHom.compLeft e.symm.toMonoidHom (Fin n)).comp f0, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨g, hg⟩ := hs0 (fun i => e (y i))
    refine ⟨g, funext fun i => ?_⟩
    show e.symm (f0 g i) = y i
    rw [hg]
    exact e.symm_apply_apply (y i)
  · intro g
    rw [← hk0 g]
    constructor
    · intro h
      funext i
      exact (MulEquiv.map_eq_one_iff e.symm).1 (congrFun h i)
    · intro h
      funext i
      show e.symm (f0 g i) = 1
      rw [congrFun h i]
      exact map_one e.symm
  · intro i
    let u : Fin n → 𝒪[k]ˣ := Pi.mulSingle i d
    have hmem : ∀ w : Fin n → 𝒪[k]ˣ,
        diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) (w i)) ∈ iwC k n ⊤ := by
      intro w
      unfold iwC
      refine Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ ?_)
      unfold torC unitsC
      exact (Subgroup.mem_pi _).2 fun i' _ => Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.2 (Subgroup.mem_top _))
    refine ⟨⟨_, hmem u⟩, ?_, ?_⟩
    · show diagT k (Fin n) _ = _
      congr 1
      funext i'
      by_cases h : i' = i
      · rw [h]
        simp only [u, Pi.mulSingle_eq_same]
        exact hdδ
      · simp only [u, Pi.mulSingle_eq_of_ne h, map_one]
    · funext i'
      refine (congrArg e.symm (hv0 u (hmem u) i')).trans ?_
      by_cases h : i' = i
      · rw [h]
        simp only [u, Pi.mulSingle_eq_same]
        rw [MulEquiv.symm_apply_eq]
        exact he.symm
      · simp only [u, Pi.mulSingle_eq_of_ne h, map_one, QuotientGroup.mk_one]

end UpperTheory.V.Pa.Lev

theorem UpperTheory.V.Pa.Lev.delIso :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (l : ℕ) [Fact l.Prime] (δ : ∀ j, ((w j).adicCompletion L)ˣ) [((UIw1 l n w).subgroupOf (UIw n w)).Normal], (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∃ e : Del l n (fun j => padicValNat l (qj w j - 1)) ≃* (UIw n w ⧸ (UIw1 l n w).subgroupOf (UIw n w)), ∀ j i, ∃ g : UIw n w, (g : GV n w) = atJ n w j (diagT _ (Fin n) (Pi.mulSingle i (δ j))) ∧ e (Pi.mulSingle (j, i) (Multiplicative.ofAdd 1)) = (g : UIw n w ⧸ (UIw1 l n w).subgroupOf (UIw n w)) := by
  intro L _ _ n q w l _ δ _ hδ
  choose f hs hk ht using fun j => di_loc ((w j).adicCompletion L) n l (δ j) (hδ j)
  haveI hN : ((Subgroup.pi Set.univ (fun j => iwC ((w j).adicCompletion L) n (ellC l _))).subgroupOf
      (Subgroup.pi Set.univ (fun j => iwC ((w j).adicCompletion L) n ⊤))).Normal :=
    (inferInstance : ((UIw1 l n w).subgroupOf (UIw n w)).Normal)
  obtain ⟨e, he⟩ := di_pi (fun j => GLw n (w j)) (fun j => iwC ((w j).adicCompletion L) n ⊤)
    (fun j => iwC ((w j).adicCompletion L) n (ellC l _))
    (fun j => Multiplicative (ZMod (l ^ padicValNat l (qj w j - 1)))) f hs hk
  refine ⟨e, fun j i => ?_⟩
  obtain ⟨t, htd, htf⟩ := ht j i
  obtain ⟨g, hg, heg⟩ := he j i _ t htf
  refine ⟨g, ?_, heg⟩
  show (g : ∀ j, GLw n (w j)) = _
  rw [hg, htd]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.IsoFix
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Pa.Lev.isoFix :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GL (Fin n) k) Y) (σ : SmIrr (GL (Fin n) k)) (I : Subgroup (GL (Fin n) k)), IsCompact (I : Set (GL (Fin n) k)) → IsoSum π ⊤ σ → ∀ y ∈ fixd π I, y ∈ ⨆ f : {f : σ.V →ₗ[ℂ] Y // ∀ g v, f (σ.ρ g v) = π g (f v)}, (fixd σ.ρ I).map f.1 := by
  intro k _ _ _ _ n Y _ _ π σ I hI hs y hy
  refine UpperTheory.Dv.CoinvFin.mem_of_span π hI
    {w | ∃ f : σ.V →ₗ[ℂ] Y, (∀ g v, f (σ.ρ g v) = π g (f v)) ∧ ∃ v, w = f v} _ ?_ ?_ hy
  · rintro _ ⟨f, hf, v, rfl⟩
    refine ⟨UpperTheory.Dv.CoinvFin.stab σ.ρ v, σ.smooth v, fun K' hK' _ => ?_⟩
    refine Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨UpperTheory.Dv.CoinvFin.av σ.ρ I K' v, UpperTheory.Dv.CoinvFin.av_fixed σ.ρ I K' hK', ?_⟩
    simp only [UpperTheory.Dv.CoinvFin.av, map_sum, hf]
  · refine (iSup_le fun f => ?_ : _ ≤ Submodule.span ℂ _) (hs Submodule.mem_top)
    rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨f.1, f.2.1, v, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.MultiPsi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem one_place {O A N ι : Type} [CommRing O] [IsDomain O] [CommRing A] [AddCommGroup N] [Fintype ι] {n : ℕ}
    (e : MvPolynomial (Fin n) O →+* A) (Φ : A → A → N)
    (h1 : ∀ s (f : ι → A), Φ s (∑ m, f m) = ∑ m, Φ s (f m))
    (h2 : ∀ t (f : ι → A), Φ (∑ m, f m) t = ∑ m, Φ (f m) t)
    (h3 : ∀ s t z, z.IsSymmetric → Φ s (t * e z) = Φ (s * e z) t)
    {a c : ι → MvPolynomial (Fin n) O} (h : Hk.IsDual a c) (x : MvPolynomial (Fin n) O) (s t : A) :
    ∑ k, Φ (e (a k) * s) (e (c k) * t * e x) = ∑ k, Φ (e x * (e (a k) * s)) (e (c k) * t) := by
  have hd := UpperTheory.V.AlgebraTools.hkDualExp O n ι a c h
  have hs := (UpperTheory.V.AlgebraTools.hkDdProps O n).2.2.1
  have e1 : ∀ k, Φ (e (a k) * s) (e (c k) * t * e x)
      = ∑ m, Φ (e (a k * Hk.dd (c k * (x * a m))) * s) (e (c m) * t) := by
    intro k
    have : e (c k) * t * e x = ∑ m, e (c m) * t * e (Hk.dd (c k * (x * a m))) := by
      rw [mul_right_comm, ← map_mul, ← (hd (c k * x)).2, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, mul_right_comm, show a m * (c k * x) = c k * (x * a m) by ring]
    rw [this, h1]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h3 _ _ _ (hs _), map_mul, mul_right_comm]
  rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← h2, ← Finset.sum_mul, ← map_sum, (hd _).1, map_mul, mul_assoc]

private theorem many_places {O A N ι : Type} [CommRing O] [IsDomain O] [CommRing A] [AddCommGroup N] [Fintype ι] {n q : ℕ}
    (e : Fin q → MvPolynomial (Fin n) O →+* A) (Φ : A → A → N)
    (h1 : ∀ s (f : ι → A), Φ s (∑ m, f m) = ∑ m, Φ s (f m))
    (h2 : ∀ t (f : ι → A), Φ (∑ m, f m) t = ∑ m, Φ (f m) t)
    (h3 : ∀ j s t z, z.IsSymmetric → Φ s (t * e j z) = Φ (s * e j z) t)
    {a c : ι → MvPolynomial (Fin n) O} (h : Hk.IsDual a c) (j : Fin q) (x : MvPolynomial (Fin n) O) :
    ∑ i : Fin q → ι, Φ (∏ j, e j (a (i j))) ((∏ j, e j (c (i j))) * e j x)
      = ∑ i : Fin q → ι, Φ (e j x * ∏ j, e j (a (i j))) (∏ j, e j (c (i j))) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := j.pos; omega⟩
  rw [← (Fin.insertNthEquiv (fun _ => ι) j).sum_comp, ← (Fin.insertNthEquiv (fun _ => ι) j).sum_comp,
    Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.prod_univ_succAbove _ j, Fin.insertNthEquiv_apply, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  exact one_place (e j) Φ h1 h2 (h3 j) h x _ _

private theorem esymm_root {O R B : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing B] {q n : ℕ} (β : R →+* B)
    (P : Fin q → Polynomial B) (j : Fin q) (k : ℕ) (hk : k ≤ n) :
    Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β (emb O R j (MvPolynomial.esymm (Fin n) O k)))
      = algebraMap B (MSplitAlg P n) ((-1) ^ k * (P j).coeff (n - k)) := by
  have h0 := congrArg (fun p => p.coeff (n - k)) (MSplitAlg.prod_root P n j)
  have hc : Multiset.card (Finset.univ.val.map fun i : Fin n => MSplitAlg.root P n j i) = n := by simp
  have h1 := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map fun i : Fin n => MSplitAlg.root P n j i)
    (k := n - k) (by rw [hc]; omega)
  rw [hc, Multiset.map_map, show n - (n - k) = k by omega, Finset.esymm_map_val] at h1
  simp only [Polynomial.coeff_map] at h0
  rw [map_mul, ← h0, Finset.prod_eq_multiset_prod]
  simp only [Function.comp_def] at h1
  rw [h1, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp [emb, MvPolynomial.esymm, MSplitAlg.root, map_sum, map_prod]

theorem UpperTheory.V.Pa.Lev.multiPsi :
    ∀ (O R B M V : Type) [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (tr : V →+ M) (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) O), Hk.IsDual a c → (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) → (∀ (t : R) v, tr (t • v) = β t • tr v) → (∀ j k, k ≤ n → ∀ v, tr (act (emb O R j (MvPolynomial.esymm (Fin n) O k)) v) = ((-1) ^ k * (P j).coeff (n - k)) • tr v) → ∀ ψ : V →+ MSplitAlg P n ⊗[B] M, (∀ v, ψ v = ∑ i : Fin q → ι, Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β (∏ j, emb O R j (a (i j)))) ⊗ₜ tr (act (∏ j, emb O R j (c (i j))) v)) → ∀ (t : PU R q n) v, ψ (act t v) = Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) • ψ v := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β P act tr ι _ a c hd _ _ hβ he ψ hψ
  let π : PU R q n →+* MSplitAlg P n := (Ideal.Quotient.mk (mSplitIdeal P n)).comp (MvPolynomial.map β)
  have hπ : ∀ t, Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) = π t := fun _ => rfl
  simp only [hπ] at hψ ⊢
  have sc : ∀ (b : B) (y : MSplitAlg P n) (m : M), y ⊗ₜ[B] (b • m) = (y * algebraMap B _ b) ⊗ₜ[B] m := by
    intro b y m
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  have hC : ∀ (r : R) (y : MSplitAlg P n) w,
      y ⊗ₜ[B] tr (act (MvPolynomial.C r) w) = (y * π (MvPolynomial.C r)) ⊗ₜ[B] tr w := by
    intro r y w
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply, hβ, sc, ← hπ,
      MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    rfl
  have bal : ∀ j (z : MvPolynomial (Fin n) O), z.IsSymmetric → ∀ (y : MSplitAlg P n) w,
      y ⊗ₜ[B] tr (act (emb O R j z) w) = (y * π (emb O R j z)) ⊗ₜ[B] tr w := by
    intro j z hz
    obtain ⟨p, hp⟩ := MvPolynomial.esymmAlgHom_surjective O (σ := Fin n) (n := n) (by simp) ⟨z, hz⟩
    obtain rfl : z = (MvPolynomial.esymmAlgHom (Fin n) O n p : MvPolynomial (Fin n) O) := by rw [hp]
    clear hp hz
    rw [MvPolynomial.esymmAlgHom_apply]
    induction p using MvPolynomial.induction_on with
    | C r =>
      have : emb O R j (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) O (i + 1))
          (MvPolynomial.C r : MvPolynomial (Fin n) O)) = MvPolynomial.C (algebraMap O R r) := by simp [emb]
      rw [this]
      exact hC _
    | add p p' hp hp' =>
      intro y w
      rw [map_add, map_add, map_add, map_add, LinearMap.add_apply, map_add, TensorProduct.tmul_add, hp, hp', mul_add,
        TensorProduct.add_tmul]
    | mul_X p i hp =>
      intro y w
      rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, hp, MvPolynomial.aeval_X, he j _ i.2, sc,
        ← esymm_root (O := O) β P j _ i.2, hπ, mul_assoc]
  intro t
  induction t using MvPolynomial.induction_on with
  | C r =>
    intro v
    rw [hψ, hψ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hC, TensorProduct.smul_tmul',
      smul_eq_mul, mul_comm]
  | add p p' hp hp' =>
    intro v
    rw [map_add, map_add, LinearMap.add_apply, map_add, hp, hp', add_smul]
  | mul_X p ji hp =>
    intro v
    obtain ⟨j, i⟩ := ji
    have hX : (MvPolynomial.X (j, i) : PU R q n) = emb O R j (MvPolynomial.X i) := by simp [emb]
    rw [map_mul, map_mul, Module.End.mul_apply, hp, mul_smul, hX, hψ, hψ, Finset.smul_sum (r := π (emb O R j _))]
    congr 1
    have := many_places (emb O R) (fun s t => π s ⊗ₜ[B] tr (act t v))
      (fun s f => by simp only [map_sum, LinearMap.sum_apply, TensorProduct.tmul_sum])
      (fun s f => by simp only [map_sum, TensorProduct.sum_tmul])
      (fun j s t z hz => by
        show π s ⊗ₜ[B] tr (act (t * emb O R j z) v) = π (s * emb O R j z) ⊗ₜ[B] tr (act t v)
        rw [mul_comm t, map_mul, Module.End.mul_apply, bal j z hz, map_mul]) hd j (MvPolynomial.X i)
    simp only [map_mul, Module.End.mul_apply] at this
    rw [this]
    simp only [TensorProduct.smul_tmul', smul_eq_mul]
end

