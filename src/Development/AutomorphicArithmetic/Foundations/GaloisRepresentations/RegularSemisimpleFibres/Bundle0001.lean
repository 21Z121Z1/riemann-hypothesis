import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0003
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0032
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0013
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0030
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0783
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0004
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeEx

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.BaseCase
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

def BaseCase : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω] (n : ℕ) (π : CuspSub K n)
    (A : ValuationSubring Ω) (Θ : IsLocalRing.ResidueField A →* ℂ) (v : HeightOneSpectrum (𝓞 K)) e e',
    ResEmb A v e → ResEmb A v e' → ∀ τ τ', π.IsLocComp v τ → π.IsLocComp v τ' →
    ∀ a : Lbl, HasLbl (Θ.comp e.toMonoidHom) τ.ρ a → HasLbl (Θ.comp e'.toMonoidHom) τ'.ρ a

end UpperTheory.Gal.InertialTypesAlt
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PArtRead
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem resS_eq_resS_of_mul_sub_eq_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (y₁ y₂ : 𝒪[k]) (h : valuation k ((y₁ : k) - y₂) < 1) :
    IsLocalRing.residue 𝒪[k] y₁ = IsLocalRing.residue 𝒪[k] y₂ := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ne_of_lt h

private theorem residue_eq_of_valuation_sub_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (z₁ z₂ : A)
    (h : A.valuation ((z₁ : Ω) - z₂) < 1) :
    IsLocalRing.residue A z₁ = IsLocalRing.residue A z₂ := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact h

theorem UpperTheory.Gal.InertialTypesAlt.artRead :
    ArtRead := by
  unfold ArtRead
  intro E Ω _ _ _ _ _ A v h g _ hg1 hg2 a ha e he t ϖ hϖ
  unfold ResEmb at he
  have hp : Nat.Prime g := Fact.out
  have hEq : (valuation (HeightOneSpectrum.adicCompletion E v)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  have hα : Valued.v (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) = 1 :=
    DiscreteGroups.sglob.DzType.val_artin_ine ha t
  obtain ⟨u, hu⟩ := valuation_eq_one_iff.1 (hEq.eq_one_iff_eq_one.2 hα)
  have hg0 : (g : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap E Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hp.ne_zero)
  have hg1' : (g : Ω) ≠ 1 := by
    rw [← map_natCast (algebraMap E Ω), ← map_one (algebraMap E Ω)]
    intro hc
    have := (algebraMap E Ω).injective hc
    exact hp.one_lt.ne' (by exact_mod_cast this)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos (normV v - 1) with hm | hm
    · rw [hm, pow_zero] at hϖ
      exact hg1' hϖ.symm
    · rw [zero_pow hm.ne'] at hϖ
      exact hg0 hϖ.symm
  have hz : A.valuation ((t : G E Ω) ϖ / ϖ) = 1 := DiscreteGroups.sglob.DzType.val_ratio (Ine_le_Dec A t.2) hϖ0
  obtain ⟨z, hzdef⟩ : ∃ z : A, (z : Ω) = (t : G E Ω) ϖ / ϖ :=
    ⟨⟨_, (A.valuation_le_one_iff _).1 hz.le⟩, rfl⟩
  obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl v
    (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) hα.le
  have hx2 := UpperTheory.Zero.LLC.tameRecAll E Ω g A v h hg1 hg2 a ha ϖ hϖ t x hx
  refine ⟨z, u, hzdef, hu, ?_, ?_⟩
  · have hxA : algebraMap E Ω x ∈ A := by
      have h1 : ((t : G E Ω) ϖ / ϖ - algebraMap E Ω x) ∈ A := (A.valuation_le_one_iff _).1 hx2.le
      have h2 := A.sub_mem z.2 h1
      rw [hzdef, sub_sub_cancel] at h2
      exact h2
    have hyK : valuation (HeightOneSpectrum.adicCompletion E v)
        (algebraMap E (HeightOneSpectrum.adicCompletion E v) x) ≤ 1 :=
      hEq.le_one_iff_le_one.2 (DiscreteGroups.sglob.DzType.val_alg_le_one x)
    let y : 𝒪[HeightOneSpectrum.adicCompletion E v] := ⟨_, hyK⟩
    let zx : A := ⟨_, hxA⟩
    have hu' : (((u : 𝒪[HeightOneSpectrum.adicCompletion E v])) : HeightOneSpectrum.adicCompletion E v) =
        (a (ineIncl h t) : HeightOneSpectrum.adicCompletion E v) := congrArg Units.val hu
    have h1 : IsLocalRing.residue _ (u : 𝒪[HeightOneSpectrum.adicCompletion E v]) = IsLocalRing.residue _ y := by
      apply resS_eq_resS_of_mul_sub_eq_mul
      show valuation (HeightOneSpectrum.adicCompletion E v)
        (((u : 𝒪[HeightOneSpectrum.adicCompletion E v]) : HeightOneSpectrum.adicCompletion E v) -
          algebraMap E (HeightOneSpectrum.adicCompletion E v) x) < 1
      rw [hu']
      exact hEq.lt_one_iff_lt_one.2 hx
    have h2 : IsLocalRing.residue A z = IsLocalRing.residue A zx := by
      apply residue_eq_of_valuation_sub_lt_one
      show A.valuation ((z : Ω) - algebraMap E Ω x) < 1
      rw [hzdef]
      exact hx2
    rw [h2, ← he x y zx rfl rfl, ← h1]
    rfl
  · have hzm : z ^ (normV v - 1) = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, hzdef, div_pow, ← map_pow, hϖ, map_natCast, div_self hg0]
      rfl
    rw [← map_pow, hzm, map_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PBaseQ
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.baseQ :
    CardRes → BaseQ := by
  intro _ E _ _ v g _ i hi
  have e : 𝓀[v.adicCompletion E] ≃+* ZMod g :=
    (Ideal.quotEquivOfEq (DiscreteGroups.sglob.DzIso.ker_redO i hi).symm).trans
      (RingHom.quotientKerEquivOfSurjective (DiscreteGroups.sglob.DzIso.redO_surjective i hi))
  exact ⟨DiscreteGroups.sglob.DzType.g_not_mem_sq v g i hi, by rw [Nat.card_congr e.toEquiv, Nat.card_zmod], ⟨e⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCardRes
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.cardRes :
    CardRes := by
  intro E _ _ v
  rw [GroundTheory.Global.natCard_residueField_integer]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspChar
section
noncomputable section

open GlobalTheory.SmGL GlobalTheory.Shin GlobalTheory.SplitWeil

namespace UpperTheory.Gal.InertialTypesAlt

private theorem blk_two {m a : ℕ} (ha : a < m) (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (i : Fin m) :
    (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i = 0 ↔ (i : ℕ) < a) := by
  obtain ⟨⟨b, j⟩, hbj⟩ : ∃ p, (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd).symm i = p := ⟨_, rfl⟩
  have hi := stdBlocks_val (![a, m - a] : Fin 2 → ℕ) hd b j
  rw [← hbj, Equiv.apply_symm_apply] at hi
  unfold blk
  rw [hbj]
  have hj := j.isLt
  fin_cases b
  · simp at hi hj ⊢
    omega
  · simp at hi hj ⊢
    omega

private theorem blk_lt_iff {m a : ℕ} (ha : a < m) (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (i j : Fin m) :
    blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i < blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j ↔
      (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  have hi := blk_two ha hd i
  have hj := blk_two ha hd j
  have h1 := (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i).isLt
  have h2 := (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j).isLt
  rw [Fin.lt_iff_val_lt_val]
  rw [Fin.ext_iff, Fin.val_zero] at hi hj
  omega

private theorem rad_le {F : Type} [Field F] {m a : ℕ} (h0 : 0 < a) (ha : a < m) (H : Subgroup (GL (Fin m) F))
    (hH : (H : Set (GL (Fin m) F)) = {u : GL (Fin m) F | ∀ i j : Fin m, (u : Matrix (Fin m) (Fin m) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)})
    (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (u : GL (Fin m) F)
    (hu : u ∈ unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd)) : u ∈ H := by
  have hu' := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.mp hu
  have hmem : u ∈ (H : Set (GL (Fin m) F)) := by
    rw [hH]
    intro i j
    by_cases h : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr h
    · left
      rw [hu' i j (by rwa [blk_lt_iff ha hd])]
      simp [Matrix.one_apply]
  exact hmem

theorem cuspChar : CuspChar := by
  intro F _ _ θ hθ m hm W _ _ _ κ hirr hcusp
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hc := GlobalTheory.T.isCharacterOverSubfield_of_representation ℂ ℂ (GL (Fin m) F) W κ
  have hprim : GlobalTheory.CuspGL.IsPrimitive
      (GlobalTheory.CuspGL.extZero (fun g : GL (Fin m) F => algebraMap ℂ ℂ (κ.character g))) := by
    refine GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical F m _ hc.1 fun a h0 ham => ?_
    obtain ⟨A, H, -, hH, -⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F m a ham.le
    have hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m := by
      simp [Fin.sum_univ_two]
      omega
    have hne : unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) ≠ ⊥ := by
      rw [GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]
      refine ⟨⟨0, hm⟩, ⟨a, ham⟩, ?_⟩
      rw [blk_lt_iff ham hd]
      exact ⟨h0, le_refl a⟩
    have hfix : ∀ v : W, (∀ u ∈ H, κ u v = v) → v = 0 := fun v hv =>
      hcusp 2 _ _ hne v fun u hu => hv u (rad_le h0 ham H hH hd u hu)
    have hz := PositivityTheory.GreenCharacters.sum_char_eq_zero κ H hfix
    rw [← hH, finsum_mem_def, finsum_eq_sum_of_fintype]
    rw [← hz]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ H <;> simp [Set.indicator_apply, hu]
  obtain ⟨k, hk, hx⟩ := GlobalTheory.CuspFormula.exists_regular F θ hθ m hm _ (hc.2 hirr) hprim
  refine ⟨k, hk, fun x => ?_⟩
  have := hx x
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this

end UpperTheory.Gal.InertialTypesAlt
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspIne
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.InertialTypesAlt.cuspIne :
    TameRead → TypeChar → NameOf → BaseQ → CuspIne := by
  intro hT hC hN hB
  intro E Ω _ _ _ _ _ A v h g _ i hi Θ hΘ e y c hy hdz hreg htr rc hrc f hf hdiv t ϖ hϖ z hz
  obtain ⟨a, ha, hL⟩ := hrc
  have hty := (UpperTheory.Zero.LLC.typeIff E Ω A v h rc).mp hL.type y
  have hn : 0 < y.fst := Nat.pos_of_dvd_of_pos hdiv hf
  obtain ⟨D⟩ := UpperTheory.Zero.LLC.extEx E Ω A v h g i hi y.fst hn
  obtain ⟨⟨R, hR⟩, hsys⟩ := UpperTheory.Zero.LLC.resEx E Ω A v h g i hi y.fst hn D
  have hrank := (hsys R hR).rank
  obtain ⟨ι, hι⟩ := hT E Ω A v h g y.fst hn D R hR
  obtain ⟨_, hcard, ⟨r⟩⟩ := hB E v g i hi
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion E v] :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : g.Prime).ne_zero)
  obtain ⟨θ, hθ, hreg', hnames⟩ :=
    hN g y.fst hn 𝓀[HeightOneSpectrum.adicCompletion E v] D.K (IsLocalRing.ResidueField A) hrank r e ι Θ hΘ c hreg
  have hcls : GlobalTheory.LocLanglands.cls y.snd.rep = y := by
    unfold GlobalTheory.LocLanglands.cls
    exact IrrGL.of_rep y
  have hy' : (GlobalTheory.LocLanglands.cls y.snd.rep).IsCusp := by rw [hcls]; exact hy
  have hdz' : UpperTheory.Zero.LLC.DZ (GlobalTheory.LocLanglands.cls y.snd.rep) := by rw [hcls]; exact hdz
  obtain ⟨τ, hcusp, hinfl⟩ :=
    (UpperTheory.Zero.LLC.typeEx E Ω A v h g i hi y.fst hn y.snd.rep).1 hy' hdz'
  have hchar := hC E v g i hi r y τ hcusp hinfl
  have hnm := hnames τ (fun γ => (hchar γ).trans (htr γ))
  obtain ⟨_, hin⟩ := hty g i hi y.fst hn D R hR θ hreg' τ hcusp hnm y.snd.rep hcls hinfl
  rw [hin t]
  set N := (g ^ f - 1) / (g ^ y.fst - 1) with hN'
  have hdvd : g ^ y.fst - 1 ∣ g ^ f - 1 := by
    obtain ⟨m, hm⟩ := hdiv
    rw [hm, pow_mul]
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (g ^ y.fst) 1 m
  have hϖ' : (ϖ ^ N) ^ (g ^ y.fst - 1) = (g : Ω) := by
    rw [← pow_mul, hN', Nat.div_mul_cancel hdvd, hϖ]
  have hz' : ((z ^ N : A) : Ω) = (t : G E Ω) (ϖ ^ N) / ϖ ^ N := by
    rw [map_pow, ← div_pow, ← hz]
    push_cast
    rfl
  have hιR : ι ((R t : D.Kˣ) : D.K) = (IsLocalRing.residue A z) ^ N := by
    rw [hι t (ϖ ^ N) hϖ' (z ^ N) hz', map_pow]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  congr 2
  rw [map_pow, Units.val_pow_eq_pow_val, hθ, hιR, map_pow, ← pow_mul, ← pow_mul]
  ring_nf
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PCuspIso
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Semi

variable {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')
  {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F' V']
  (e : V ≃+ V') (he : ∀ (c : F) (x : V), e (c • x) = r c • e x)

include he in
private theorem symm_smul (c : F') (y : V') : e.symm (c • y) = r.symm c • e.symm y := by
  apply e.injective
  rw [he]
  simp

private def smap (W : Submodule F V) : Submodule F' V' where
  carrier := e '' W
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, W.add_mem ha hb, map_add e a b⟩
  zero_mem' := ⟨0, W.zero_mem, map_zero e⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨r.symm c • a, W.smul_mem _ ha, by rw [he]; simp⟩

private def scomap (W : Submodule F' V') : Submodule F V where
  carrier := e ⁻¹' W
  add_mem' := by
    intro a b ha hb
    simpa using W.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_preimage, SetLike.mem_coe, he] at ha ⊢
    exact W.smul_mem _ ha

private theorem mem_smap {W : Submodule F V} {y : V'} : y ∈ smap r e he W ↔ e.symm y ∈ W := by
  change y ∈ e '' (W : Set V) ↔ _
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨e.symm y, h, by simp⟩

private def smapE : Submodule F V ≃ Submodule F' V' where
  toFun := smap r e he
  invFun := scomap r e he
  left_inv W := by
    ext x
    change e x ∈ smap r e he W ↔ _
    rw [mem_smap]
    simp
  right_inv W := by
    ext y
    rw [mem_smap]
    change e (e.symm y) ∈ W ↔ _
    simp

private def eRes (W : Submodule F V) : W ≃+ smap r e he W where
  toFun x := ⟨e x, (mem_smap r e he).2 (by simp)⟩
  invFun y := ⟨e.symm y, (mem_smap r e he).1 y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

include he in
private theorem charpoly_semi [FiniteDimensional F V] [FiniteDimensional F' V']
    (g : Module.End F V) (g' : Module.End F' V') (hg : ∀ x, e (g x) = g' (e x)) :
    LinearMap.charpoly g' = (LinearMap.charpoly g).map r.toRingHom := by
  classical
  let b := Module.finBasis F V
  have hf : ∀ f : Fin (Module.finrank F V) →₀ F,
      Finsupp.mapRange r.symm (map_zero r.symm) (Finsupp.mapRange r (map_zero r) f) = f := by
    intro f
    ext i
    simp
  let repr' : V' ≃ₗ[F'] (Fin (Module.finrank F V) →₀ F') :=
    { toFun := fun y => Finsupp.mapRange r (map_zero r) (b.repr (e.symm y))
      invFun := fun c => e (b.repr.symm (Finsupp.mapRange r.symm (map_zero r.symm) c))
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro c y
        ext i
        simp [symm_smul r e he]
      left_inv := by
        intro y
        show e (b.repr.symm (Finsupp.mapRange r.symm _ (Finsupp.mapRange r _ (b.repr (e.symm y))))) = y
        rw [hf]
        simp
      right_inv := by
        intro c
        ext i
        simp }
  let b' : Module.Basis (Fin (Module.finrank F V)) F' V' := Module.Basis.ofRepr repr'
  have hb' : ∀ j, b' j = e (b j) := by
    intro j
    simp [b', repr']
  rw [← LinearMap.charpoly_toMatrix g b, ← LinearMap.charpoly_toMatrix g' b', ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', ← hg]
  show (Finsupp.mapRange r (map_zero r) (b.repr (e.symm (e (g (b j)))))) i = _
  simp

end Semi

private theorem semilinear_equiv_conjugate_endomorphism {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') (s : F[X] → ℂ) (s' : F'[X] → ℂ)
    (hs : ∀ P, s' (P.map r.toRingHom) = s P) (n : ℕ) :
    ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F' V']
      [FiniteDimensional F' V'] (e : V ≃+ V') (_ : ∀ (c : F) (x : V), e (c • x) = r c • e x)
      (g : Module.End F V) (g' : Module.End F' V'), (∀ x, e (g x) = g' (e x)) →
      GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s' n V' g' = GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V g := by
  induction n with
  | zero =>
    intro V V' _ _ _ _ _ _ e he g g' hg
    rfl
  | succ n ih =>
    intro V V' _ _ _ _ _ _ e he g g' hg
    rw [GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, charpoly_semi r e he g g' hg, hs]
    congr 1
    have htop : smapE r e he ⊤ = ⊤ := by
      ext y
      change y ∈ smap r e he ⊤ ↔ _
      rw [mem_smap]
      simp
    have hsymm : ∀ y, e.symm (g' y) = g (e.symm y) := by
      intro y
      apply e.injective
      rw [hg]
      simp
    have hiff : ∀ W : Submodule F V, (W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) ↔
        (smapE r e he W ≠ ⊤ ∧ ∀ y ∈ smapE r e he W, g' y ∈ smapE r e he W) := by
      intro W
      constructor
      · rintro ⟨hW, hinv⟩
        refine ⟨?_, ?_⟩
        · intro h
          apply hW
          apply (smapE r e he).injective
          rw [h, htop]
        · intro y hy
          change g' y ∈ smap r e he W
          change y ∈ smap r e he W at hy
          rw [mem_smap] at hy ⊢
          rw [hsymm]
          exact hinv _ hy
      · rintro ⟨hW, hinv⟩
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact hW htop
        · intro x hx
          have h1 : e x ∈ smap r e he W := by
            rw [mem_smap]
            simpa using hx
          have h2 := hinv (e x) h1
          change g' (e x) ∈ smap r e he W at h2
          rw [mem_smap, hsymm] at h2
          simpa using h2
    symm
    apply finsum_eq_of_bijective ((smapE r e he).subtypeEquiv hiff) (Equiv.bijective _)
    intro W
    symm
    exact ih _ _ (eRes r e he W.1)
      (by
        intro c x
        apply Subtype.ext
        simp [eRes, he])
      _ _
      (by
        intro x
        apply Subtype.ext
        simp [eRes, hg]
        rfl)

private theorem rootSum_iso {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')
    (j : AlgebraicClosure F ≃+* AlgebraicClosure F')
    (hj : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) (θ : AlgebraicClosure F' →* ℂ) (c : ℕ) (P : F[X]) :
    GlobalTheory.CuspGL.rootSum θ c (P.map r.toRingHom) = GlobalTheory.CuspGL.rootSum (θ.comp j.toMonoidHom) c P := by
  unfold GlobalTheory.CuspGL.rootSum
  have hpoly : (P.map r.toRingHom).map (algebraMap F' (AlgebraicClosure F')) =
      (P.map (algebraMap F (AlgebraicClosure F))).map j.toRingHom := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext x
    exact (hj x).symm
  rw [hpoly, ← roots_map_of_injective_of_card_eq_natDegree j.injective IsAlgClosed.card_roots_eq_natDegree,
    Multiset.map_map]
  rfl

theorem UpperTheory.Gal.InertialTypesAlt.cuspIso :
    CuspIso := by
  intro F F' _ _ _ r j hj θ m c g
  unfold cusp psiG GlobalTheory.CuspGL.psi
  congr 1
  rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
  apply semilinear_equiv_conjugate_endomorphism r (GlobalTheory.CuspGL.rootSum (θ.comp j.toMonoidHom) c) (GlobalTheory.CuspGL.rootSum θ c)
    (rootSum_iso r j hj θ c) (m + 1) (Fin m → F) (Fin m → F') (AddEquiv.piCongrRight fun _ => r.toAddEquiv)
  · intro a x
    funext i
    simp
  · intro x
    funext i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
end

