import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0028
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0030
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0016
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0029
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzFeCard
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

theorem sum_range_lt (n k : ℕ) : ∑ x ∈ Finset.range n, (if x < k then 1 else 0) = min n k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.lt_or_ge n k with h | h
    · rw [if_pos h, min_eq_left h.le, min_eq_left (by omega)]
    · rw [if_neg (by omega), min_eq_right h, min_eq_right (by omega), add_zero]

theorem card_SIdx : Fintype.card (SIdx m) = (m + 1) * m / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ k : Fin (m + 1), ∑ i : Fin (m + 1), (if (i, k).1 < (i, k).2 then 1 else 0) = (k : ℕ) := fun k => by
    show ∑ i : Fin (m + 1), (if (i : ℕ) < (k : ℕ) then 1 else 0) = (k : ℕ)
    rw [Fin.sum_univ_eq_sum_range (fun x => if x < (k : ℕ) then 1 else 0), sum_range_lt]
    exact min_eq_right k.2.le
  rw [Finset.sum_congr rfl (fun k _ => h k), Fin.sum_univ_eq_sum_range (fun x => x), Finset.sum_range_id]
  simp

theorem sum_range_between (n j m : ℕ) :
    ∑ x ∈ Finset.range n, (if j < x ∧ x < m then 1 else 0) = min n m - min n (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.min_def]
    split_ifs <;> omega

theorem card_WIdx (j : ℕ) : Fintype.card (WIdx m j) = m - 1 - j := by
  rw [Fintype.card_subtype, Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun x => if j < x ∧ x < m then 1 else 0), sum_range_between]
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem sum_split (j : ℕ) (f : ZMod g → ℂ) :
    ∑ b : JIdx m j → ZMod g, f (b (j0 m j)) =
      (Fintype.card ({i : JIdx m j // i ≠ j0 m j} → ZMod g) : ℂ) * ∑ s : ZMod g, f s := by
  rw [← (Equiv.funSplitAt (j0 m j) (ZMod g)).symm.sum_comp, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp [Equiv.funSplitAt_symm_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end DiscreteGroups.sglob.DzFe
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzFinPair
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.DzType

theorem lFinPair : LFinPair := by
  intro hLFE g _ m ψ₀ hψ τ hτ γ hγ l hl hl0 W hW s hs
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  classical
  have h1 : ∀ u ∈ unipB (ZMod g) (Fin m), ∀ x, W (u * x) = (((ψ₀ (superDiag u))⁻¹ : Circle) : ℂ) * W x := hW.1
  have h2 : ∀ b ∈ DiscreteGroups.sglob.DzFp.lowB (ZMod g) m, ∀ x, W (x * b) = W x := fun b hb =>
    hW.2.1 b (DiscreteGroups.sglob.DzFp.mem_lowB.1 hb)
  obtain ⟨v, hv0, hv⟩ := DiscreteGroups.sglob.DzFp.exists_eigen hl hl0
  have hR := DiscreteGroups.sglob.DzFp.sum_cell hψ W h1 h2 (fun x => l (τ.ρ (corner x) v)) (fun u hu x => by
    show l (τ.ρ (corner (u * x)) v) = _ * l (τ.ρ (corner x) v)
    rw [DiscreteGroups.sglob.DzRed.corner_mul, map_mul, Module.End.mul_apply, hl _ (DiscreteGroups.sglob.DzRed.corner_mem hu),
      DiscreteGroups.sglob.DzRed.superDiag_corner])
  have hL := DiscreteGroups.sglob.DzFp.sum_cell hψ W h1 h2 (fun h => l (τ.ρ (tilde (corner (tilde h))) v)) (fun u hu x => by
    show l (τ.ρ (tilde (corner (tilde (u * x)))) v) = _ * l (τ.ρ (tilde (corner (tilde x))) v)
    rw [DiscreteGroups.sglob.DzRed.tilde_mul_left u x,
      DiscreteGroups.sglob.DzRed.corner_mul (longElt m (ZMod g) * GlobalTheory.CuspRep.invT m (ZMod g) u * (longElt m (ZMod g))⁻¹)
        (tilde x),
      DiscreteGroups.sglob.DzRed.tilde_mul_left
        (corner (longElt m (ZMod g) * GlobalTheory.CuspRep.invT m (ZMod g) u * (longElt m (ZMod g))⁻¹)) (corner (tilde x)),
      map_mul, Module.End.mul_apply,
      hl _ (DiscreteGroups.sglob.DzRed.conjT_mem (DiscreteGroups.sglob.DzRed.corner_mem (DiscreteGroups.sglob.DzRed.conjT_mem hu))),
      DiscreteGroups.sglob.DzRed.superDiag_conjT, ← DiscreteGroups.sglob.DzRed.corner_inv, DiscreteGroups.sglob.DzRed.superDiag_corner,
      ← DiscreteGroups.sglob.DzFp.conjT_inv, DiscreteGroups.sglob.DzRed.superDiag_conjT, inv_inv])
  have hre : ∑ᶠ x, l (τ.ρ (tilde (corner x)) v) * W (tilde x) =
      ∑ᶠ h, l (τ.ρ (tilde (corner (tilde h))) v) * W h := by
    have := finsum_comp_equiv (Function.Involutive.toPerm _ (DiscreteGroups.sglob.DzFp.tilde_tilde (R := ZMod g) (n := m)))
      (f := fun h => l (τ.ρ (tilde (corner (tilde h))) v) * W h)
    rw [← this]
    refine finsum_congr fun x => ?_
    show _ = l (τ.ρ (tilde (corner (tilde (tilde x)))) v) * W (tilde x)
    rw [DiscreteGroups.sglob.DzFp.tilde_tilde]
  have hs' := hs v
  rw [hre, hL, hR, DiscreteGroups.sglob.DzFp.sum_lower_corner hψ hl hv] at hs'
  set c := longElt (m + 1) (ZMod g) * corner (longElt m (ZMod g)) with hcdef
  set X := ∑ᶠ b : DiscreteGroups.sglob.DzFp.lowB (ZMod g) m, τ.ρ (corner (b : GL (Fin m) (ZMod g))) v with hXdef
  have hLsum : ∑ᶠ b : DiscreteGroups.sglob.DzFp.lowB (ZMod g) m, l (τ.ρ (tilde (corner (tilde (b : GL (Fin m) (ZMod g))))) v) =
      l (τ.ρ c X) := by
    rw [hXdef, DiscreteGroups.sglob.DzFp.map_finsum_lower' (τ.ρ c), DiscreteGroups.sglob.DzFp.map_finsum_lower l]
    refine finsum_congr fun b => ?_
    rw [DiscreteGroups.sglob.DzFp.tilde_corner, DiscreteGroups.sglob.DzFp.tilde_tilde, ← hcdef, map_mul, Module.End.mul_apply]
  rw [hLsum] at hs'
  have hfe := hLFE g m ψ₀ hψ τ hτ γ hγ l hl X fun b hb =>
    DiscreteGroups.sglob.DzFp.corner_fixed τ.ρ v b (DiscreteGroups.sglob.DzFp.mem_lowB.2 hb)
  have hlX : l X = l v := by
    rw [hXdef, DiscreteGroups.sglob.DzFp.map_finsum_lower l]
    exact DiscreteGroups.sglob.DzFp.sum_lower_corner hψ hl hv
  rw [hlX] at hfe
  have hK : (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * W 1 ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne') hW.2.2
  have hcX : l (τ.ρ c X) = s * l v := by
    apply mul_left_cancel₀ hK
    rw [hs']
    ring
  rw [hcX] at hfe
  apply mul_right_cancel₀ hv0
  rw [← hfe]
  ring

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalChi
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem liftsChar_pow {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (χ₀ : (ZMod g)ˣ →* ℂˣ)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hlc : LiftsChar i χ₀ χ) : ∀ x, χ x ^ (g - 1) = 1 := by
  intro x
  have hg0 : (g : ℚ_[g]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  have hgk : (g : w.adicCompletion E) ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hg0
  set y : ℚ_[g] := i.symm (x : w.adicCompletion E) with hy
  have hy0 : y ≠ 0 := (map_ne_zero i.symm).2 x.ne_zero
  have hn : ‖y * (g : ℚ_[g]) ^ (-y.valuation)‖ = 1 := by
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hy0, Padic.norm_p_zpow, neg_neg, ← zpow_add₀, neg_add_cancel,
      zpow_zero]
    exact Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  let γ : (w.adicCompletion E)ˣ := Units.mk0 _ hgk
  have hγ : χ γ = 1 := hlc.2 γ rfl
  have hu := hlc.1 (PadicInt.mkUnits hn) (x * γ ^ (-y.valuation)) (by
    rw [PadicInt.mkUnits_eq, map_mul, map_zpow₀, map_natCast, hy, RingEquiv.apply_symm_apply, Units.val_mul,
      Units.val_zpow_eq_zpow_val]
    rfl)
  rw [map_mul, map_zpow, hγ, one_zpow, mul_one] at hu
  rw [hu, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]

theorem hasExponent_one_of_res {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ζ : kˣ →* ℂˣ) (ζb : 𝓀[k]ˣ →* ℂˣ)
    (hcompat : ∀ x : 𝒪[k]ˣ, ζ (Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) x) =
      ζb (Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) x)) (hne : ζb ≠ 1) : HasExponent ζ 1 := by
  have hv := Valuation.integer.integers (valuation k)
  refine ⟨fun x hx => ?_, fun b hb => ?_⟩
  · let a : 𝒪[k] := ⟨x, (Valuation.mem_integer_iff _ _).2 hx.1.le⟩
    have ha : IsUnit a := hv.isUnit_iff_valuation_eq_one.2 hx.1
    have e : Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) ha.unit = x := Units.ext rfl
    have e' : Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) ha.unit = 1 := by
      refine Units.ext ?_
      show IsLocalRing.residue 𝒪[k] a = 1
      rw [← map_one (IsLocalRing.residue 𝒪[k]), residue_eq_iff_valuation_lt]
      have h2 := hx.2
      rw [pow_one] at h2
      exact lt_of_le_of_lt h2 uniformizer_lt_one
    rw [← e, hcompat, e', map_one]
  · obtain rfl : b = 0 := by omega
    obtain ⟨z, hz⟩ : ∃ z, ζb z ≠ 1 := by
      by_contra h
      exact hne (MonoidHom.ext fun z => not_not.1 (not_exists.1 h z))
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (z : 𝓀[k])
    have hau : IsUnit a := (IsLocalRing.residue_ne_zero_iff_isUnit a).1 (ha ▸ z.ne_zero)
    have h1 : valuation k ((Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) hau.unit : kˣ) : k) = 1 :=
      hv.isUnit_iff_valuation_eq_one.1 hau
    refine ⟨_, ⟨h1, ?_⟩, ?_⟩
    · rw [pow_zero]
      exact (Valuation.map_sub _ _ _).trans (by rw [h1, map_one, max_self])
    · rw [hcompat]
      have : Units.map (IsLocalRing.residue 𝒪[k] : 𝒪[k] →* 𝓀[k]) hau.unit = z := Units.ext ha
      rwa [this]

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalKappa
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal ValuativeRel GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option linter.style.haveILetI false in
theorem kappa_range_sub {K F : Type} [Field K] [Field F] [DecidableEq F] [Finite K] (f : K →+* F) :
    Set.range f ⊆ ↑((Polynomial.X ^ Nat.card K - Polynomial.X : Polynomial F).roots.toFinset) := by
  letI := Fintype.ofFinite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  rintro _ ⟨z, rfl⟩
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero F hq1),
    Polynomial.IsRoot.def]
  have hz : z ^ Nat.card K = z := by rw [Nat.card_eq_fintype_card]; exact FiniteField.pow_card z
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← map_pow, hz, sub_self]

theorem kappa_exists {K1 K2 F : Type} [Field K1] [Field K2] [Field F] [Finite K1] [Finite K2]
    (hc : Nat.card K1 = Nat.card K2) (f1 : K1 →+* F) (f2 : K2 →+* F) :
    ∃ κ : K1 ≃+* K2, ∀ z, f2 (κ z) = f1 z := by
  classical
  have hq1 : 1 < Nat.card K1 := Finite.one_lt_card
  have hRc : (Polynomial.X ^ Nat.card K1 - Polynomial.X : Polynomial F).roots.toFinset.card ≤ Nat.card K1 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq F hq1).le)
  have hr : ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card K1 → ∀ f : K →+* F,
      Set.range f = ↑((Polynomial.X ^ Nat.card K1 - Polynomial.X : Polynomial F).roots.toFinset) := by
    intro K _ _ hK f
    have hs := kappa_range_sub f
    rw [hK] at hs
    refine Set.eq_of_subset_of_ncard_le hs ?_ (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, ← Set.image_univ, Set.ncard_image_of_injective _ f.injective, Set.ncard_univ, hK]
    exact hRc
  have heq : f1.range = f2.range := SetLike.coe_injective (by
    rw [RingHom.coe_range, RingHom.coe_range, hr K1 rfl f1, hr K2 hc.symm f2])
  let e1 : K1 ≃+* f1.range := RingEquiv.ofBijective f1.rangeRestrict
    ⟨fun a b h => f1.injective (congrArg Subtype.val h), f1.rangeRestrict_surjective⟩
  let e2 : K2 ≃+* f2.range := RingEquiv.ofBijective f2.rangeRestrict
    ⟨fun a b h => f2.injective (congrArg Subtype.val h), f2.rangeRestrict_surjective⟩
  refine ⟨(e1.trans (RingEquiv.subringCongr heq)).trans e2.symm, fun z => ?_⟩
  exact congrArg Subtype.val (e2.apply_symm_apply ((RingEquiv.subringCongr heq) (e1 z)))

section Ring

variable {Ω : Type} [Field Ω]

def kappaToA {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω) : 𝓞 F →+* A :=
  ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A fun x =>
    mem_of_isIntegral_int A (NumberField.RingOfIntegers.isIntegral_coe x).algebraMap

def kappaQ {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω) :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp (kappaToA A)

theorem kappa_ker_A {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (hv : IsPlaceOver A v) :
    RingHom.ker (kappaQ A : 𝓞 F →+* IsLocalRing.ResidueField A) = v.asIdeal := by
  ext y
  rw [RingHom.mem_ker, kappaQ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff, ← hv y]
  rfl

end Ring

section Compl

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem kappa_val_le_iff (y : v.adicCompletion L) :
    valuation (v.adicCompletion L) y ≤ 1 ↔ Valued.v y ≤ 1 :=
  (DiscreteGroups.sglob.DzIso.val_le_iff y).trans Valued.toNormedField.norm_le_one_iff

theorem kappa_val_lt_iff (y : v.adicCompletion L) :
    valuation (v.adicCompletion L) y < 1 ↔ Valued.v y < 1 :=
  (DiscreteGroups.sglob.DzIso.val_lt_iff y).trans Valued.toNormedField.norm_lt_one_iff

theorem kappa_v_int (y : 𝓞 L) :
    Valued.v (algebraMap L (v.adicCompletion L) (y : L)) = v.valuation L (y : L) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) v (y : L)

def kappaToO : 𝓞 L →+* 𝒪[v.adicCompletion L] :=
  ((algebraMap L (v.adicCompletion L)).comp (algebraMap (𝓞 L) L)).codRestrict 𝒪[v.adicCompletion L] fun y =>
    (Valuation.mem_integer_iff _ _).2 ((kappa_val_le_iff v _).2
      ((kappa_v_int v y).trans_le (v.valuation_le_one y)))

def kappaP : 𝓞 L →+* 𝓀[v.adicCompletion L] := (IsLocalRing.residue 𝒪[v.adicCompletion L]).comp (kappaToO v)

theorem kappa_ker_O : RingHom.ker (kappaP v) = v.asIdeal := by
  ext y
  rw [RingHom.mem_ker, kappaP, RingHom.comp_apply, ← map_zero (IsLocalRing.residue 𝒪[v.adicCompletion L]),
    residue_eq_iff_valuation_lt]
  have e1 : ((kappaToO v y : 𝒪[v.adicCompletion L]) : v.adicCompletion L) -
      ((0 : 𝒪[v.adicCompletion L]) : v.adicCompletion L) = algebraMap L (v.adicCompletion L) (y : L) := by
    rw [ZeroMemClass.coe_zero, sub_zero]
    rfl
  rw [e1, kappa_val_lt_iff v, kappa_v_int v y]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v y

theorem kappa_surj_O : Function.Surjective (kappaP v) := by
  intro z
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective z
  have hu : Valued.v (u : v.adicCompletion L) ≤ 1 :=
    (kappa_val_le_iff v _).1 ((Valuation.mem_integer_iff _ _).1 u.2)
  obtain ⟨x, hx⟩ := exists_int_approx_compl v (u : v.adicCompletion L) hu
  refine ⟨x, ?_⟩
  rw [kappaP, RingHom.comp_apply, residue_eq_iff_valuation_lt, Valuation.map_sub_swap]
  exact (kappa_val_lt_iff v _).2 hx

end Compl

theorem exists_resIso {L E' Ω : Type} [Field L] [NumberField L] [Field E'] [NumberField E'] [Field Ω]
    [Algebra L Ω] [Algebra E' Ω] [IsAlgClosure L Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime] (n : ℕ)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v) (w' : HeightOneSpectrum (𝓞 E'))
    (h' : IsPlaceOver A w') (hvN : normV v = g ^ n) (hwN : normV w' = g ^ n) (K : Type) [Field K]
    (red : 𝓞 E' →+* K) (hr : Function.Surjective red) (hk : RingHom.ker red = w'.asIdeal) :
    ∃ κ : 𝓀[v.adicCompletion L] ≃+* K, ∀ (u : 𝒪[v.adicCompletion L]) (y : 𝓞 L) (x : 𝓞 E'),
      Valued.v ((u : v.adicCompletion L) - algebraMap L (v.adicCompletion L) (y : L)) < 1 →
      A.valuation (algebraMap L Ω (y : L) - algebraMap E' Ω (x : E')) < 1 →
      κ (IsLocalRing.residue 𝒪[v.adicCompletion L] u) = red x := by
  classical
  have hkp : RingHom.ker (kappaP v) = RingHom.ker (kappaQ A : 𝓞 L →+* IsLocalRing.ResidueField A) := by
    rw [kappa_ker_O, kappa_ker_A A v hv]
  have hkr : RingHom.ker red = RingHom.ker (kappaQ A : 𝓞 E' →+* IsLocalRing.ResidueField A) := by
    rw [hk, kappa_ker_A A w' h']
  let e1 := RingHom.quotientKerEquivOfSurjective (kappa_surj_O v)
  let e2 := RingHom.quotientKerEquivOfSurjective hr
  let f1 : 𝓀[v.adicCompletion L] →+* IsLocalRing.ResidueField A :=
    (Ideal.Quotient.lift (RingHom.ker (kappaP v)) (kappaQ A)
      fun a ha => (RingHom.mem_ker).1 (hkp ▸ ha)).comp e1.symm.toRingHom
  let f2 : K →+* IsLocalRing.ResidueField A :=
    (Ideal.Quotient.lift (RingHom.ker red) (kappaQ A)
      fun a ha => (RingHom.mem_ker).1 (hkr ▸ ha)).comp e2.symm.toRingHom
  have hf1 : ∀ y, f1 (kappaP v y) = kappaQ A y := fun y => by
    have : e1.symm (kappaP v y) = Ideal.Quotient.mk _ y := e1.symm_apply_eq.2 rfl
    simp only [f1, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this,
      Ideal.Quotient.lift_mk]
  have hf2 : ∀ x, f2 (red x) = kappaQ A x := fun x => by
    have : e2.symm (red x) = Ideal.Quotient.mk _ x := e2.symm_apply_eq.2 rfl
    simp only [f2, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this,
      Ideal.Quotient.lift_mk]
  have hgn : g ^ n ≠ 0 := pow_ne_zero _ (Fact.out : g.Prime).ne_zero
  have hc1 : Nat.card 𝓀[v.adicCompletion L] = g ^ n := by
    rw [← hvN, ← GlobalTheory.LocLanglands.resCard_eq_normV v]
    rfl
  have hc2 : Nat.card K = g ^ n := by
    rw [← hwN, normV]
    exact (Nat.card_congr ((Ideal.quotEquivOfEq hk.symm).trans e2).toEquiv).symm
  have : Finite 𝓀[v.adicCompletion L] := Nat.finite_of_card_ne_zero (by rw [hc1]; exact hgn)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hc2]; exact hgn)
  obtain ⟨κ, hκ⟩ := kappa_exists (hc1.trans hc2.symm) f1 f2
  refine ⟨κ, fun u y x huy hyx => f2.injective ?_⟩
  rw [hκ, hf2]
  have h1 : IsLocalRing.residue 𝒪[v.adicCompletion L] u = kappaP v y := by
    rw [kappaP, RingHom.comp_apply, residue_eq_iff_valuation_lt]
    exact (kappa_val_lt_iff v _).2 huy
  rw [h1, hf1, kappaQ, kappaQ, RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact hyx

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalRes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A w'}

theorem val_artin_ine {a' : Weil h' →* (w'.adicCompletion E')ˣ} (ha' : IsLocalArtin h' a') (t : Ine (F := E') A) :
    Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1 := by
  have h1 := ha'.ord_eq (ineIncl h' t)
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, deg_ineIncl] at h1
  have hv0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact Units.ne_zero _
  have hl : WithZero.log (Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E')) = 0 := by
    simpa using h1
  rw [← WithZero.exp_log hv0, hl, WithZero.exp_zero]

theorem val_alg_lt_one_of_mem (x : 𝓞 E') (hx : x ∈ w'.asIdeal) :
    Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
  rw [e]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E') w' x).mpr hx

theorem val_alg_le_one (x : 𝓞 E') : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) ≤ 1 := by
  have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
  rw [e]
  exact w'.valuation_le_one x

variable {a' : Weil h' →* (w'.adicCompletion E')ˣ} (ha' : IsLocalArtin h' a') {K : Type} [Field K]
  {red : 𝓞 E' →+* K} (hk : RingHom.ker red = w'.asIdeal)
include ha' hk

theorem red_ne_zero_of_approx {t : Ine (F := E') A} {x : 𝓞 E'}
    (hx : Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1) :
    red x ≠ 0 := by
  intro h0
  have hxm : x ∈ w'.asIdeal := by rw [← hk, RingHom.mem_ker]; exact h0
  have hlt : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') < 1 := by
    have e : ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') =
        (((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') -
          algebraMap E' (w'.adicCompletion E') (x : E')) + algebraMap E' (w'.adicCompletion E') (x : E') := by ring
    rw [e]
    exact Valuation.map_add_lt _ hx (val_alg_lt_one_of_mem x hxm)
  rw [val_artin_ine ha' t] at hlt
  exact lt_irrefl _ hlt

theorem red_eq_of_approx {t : Ine (F := E') A} {x x' : 𝓞 E'}
    (hx : Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1)
    (hx' : Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) < 1) :
    red x = red x' := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hk]
  apply mem_of_val_lt_one w'
  have e : algebraMap E' (w'.adicCompletion E') (((x - x' : 𝓞 E')) : E') =
      ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) -
        ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) := by
    rw [show (((x - x' : 𝓞 E')) : E') = (x : E') - (x' : E') by push_cast; ring, map_sub]; ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hx' hx)

theorem exists_resHom : ∃ R : Ine (F := E') A →* Kˣ, ∀ (t : Ine (F := E') A) (x : 𝓞 E'),
    Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
      ((R t : Kˣ) : K) = red x := by
  have hex : ∀ t : Ine (F := E') A, ∃ x : 𝓞 E',
      Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 :=
    fun t => exists_int_approx_compl w' _ (val_artin_ine ha' t).le
  choose x hx using hex
  refine ⟨MonoidHom.mk' (fun t => Units.mk0 (red (x t)) (red_ne_zero_of_approx ha' hk (hx t))) ?_,
    fun t y hy => red_eq_of_approx ha' hk (hx t) hy⟩
  intro s t
  ext
  simp only [Units.val_mk0, Units.val_mul]
  rw [← map_mul]
  apply red_eq_of_approx ha' hk (hx (s * t))
  rw [map_mul, map_mul, Units.val_mul]
  have e : ((a' (ineIncl h' s) : w'.adicCompletion E') * (a' (ineIncl h' t) : w'.adicCompletion E')) -
      algebraMap E' (w'.adicCompletion E') (((x s * x t : 𝓞 E')) : E') =
      (a' (ineIncl h' s) : w'.adicCompletion E') *
        ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x t : E')) +
      ((a' (ineIncl h' s) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x s : E')) *
        algebraMap E' (w'.adicCompletion E') (x t : E') := by
    rw [show (((x s * x t : 𝓞 E')) : E') = (x s : E') * (x t : E') by push_cast; ring, map_mul]; ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul, val_artin_ine ha' s, one_mul]; exact hx t
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_alg_le_one (x t))) (hx s)

end DiscreteGroups.sglob.DzType

end
end

