import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.QzSep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem exists_qz_ne_zero_annihilators_of_ne_zero (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (m : M) (hm : m ≠ 0) : ∃ x : QZ l, x ≠ 0 ∧ ∀ a : ℤ_[l], a • m = 0 → a • x = 0 := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hdec : ∀ (N : Type) [AddCommGroup N] [Module ℤ_[l] N] (a : ℤ_[l]) (ha : a ≠ 0) (y : N),
      a • y = 0 ↔ (l : ℤ_[l]) ^ a.valuation • y = 0 := by
    intro N _ _ a ha y
    conv_lhs => rw [PadicInt.unitCoeff_spec ha, mul_smul]
    exact (PadicInt.unitCoeff ha).isUnit.smul_eq_zero
  by_cases hex : ∃ r : ℕ, (l : ℤ_[l]) ^ r • m = 0
  · classical
    set r := Nat.find hex with hrdef
    have hr : (l : ℤ_[l]) ^ r • m = 0 := Nat.find_spec hex
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_smul] at hr
      exact hm hr
    obtain ⟨ι, hinj, hrange, hlin⟩ := zmodToQZ l r
    haveI : Fact (1 < l ^ r) := ⟨Nat.one_lt_pow hr0 hl1⟩
    have hι0 : ι 0 = 0 := by simpa using hlin 0 0
    refine ⟨ι 1, fun h => one_ne_zero (hinj (h.trans hι0.symm)), ?_⟩
    have hx : (l : ℤ_[l]) ^ r • ι 1 = 0 := by
      have := (hrange (ι 1)).mp ⟨1, rfl⟩
      exact_mod_cast this
    intro a ha
    by_cases a0 : a = 0
    · rw [a0, zero_smul]
    · rw [hdec _ a a0] at ha ⊢
      have hle : r ≤ a.valuation := Nat.find_min' hex ha
      rw [← Nat.add_sub_cancel' hle, pow_add, mul_comm, mul_smul, hx, smul_zero]
  · push_neg at hex
    obtain ⟨ι, hinj, hrange, hlin⟩ := zmodToQZ l 1
    haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl1⟩
    have hι0 : ι 0 = 0 := by simpa using hlin 0 0
    refine ⟨ι 1, fun h => one_ne_zero (hinj (h.trans hι0.symm)), ?_⟩
    intro a ha
    by_cases a0 : a = 0
    · rw [a0, zero_smul]
    · exact absurd ((hdec _ a a0 m).mp ha) (hex _)

theorem UpperTheory.V.Tower.qzSep :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (m : M), m ≠ 0 → ∃ f : M →ₗ[ℤ_[l]] QZ l, f m ≠ 0 := by
  intro l _ M _ _ m hm
  obtain ⟨x, hx0, hx⟩ := exists_qz_ne_zero_annihilators_of_ne_zero l M m hm
  set K := LinearMap.ker (LinearMap.toSpanSingleton ℤ_[l] M m) with hK
  have hle : K ≤ LinearMap.ker (LinearMap.toSpanSingleton ℤ_[l] (QZ l) x) := by
    intro a ha
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at ha ⊢
    exact hx a ha
  let f := K.liftQ (LinearMap.toSpanSingleton ℤ_[l] M m) le_rfl
  let g := K.liftQ (LinearMap.toSpanSingleton ℤ_[l] (QZ l) x) hle
  have hf : Function.Injective f := LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot _ _ le_rfl)
  haveI := UpperTheory.V.PropA.qzInj l
  obtain ⟨h, hh⟩ := Module.Injective.out f hf g
  refine ⟨h, ?_⟩
  have h1 := hh (K.mkQ 1)
  simp only [f, g, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
    one_smul] at h1
  rw [h1]
  exact hx0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.RankXRk
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem finite_simple (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    [h : IsSimpleModule ℤ_[l] M] : Finite M := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 h
  have := IsLocalRing.eq_maximalIdeal hI
  subst this
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (ℤ_[l] ⧸ IsLocalRing.maximalIdeal ℤ_[l]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := l)).toEquiv.symm
  exact Finite.of_equiv _ e.toEquiv.symm

private theorem finite_of_len (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (h : IsFiniteLength ℤ_[l] M) : Finite M := by
  induction h with
  | of_subsingleton => infer_instance
  | @of_simple_quotient M _ _ N _ _ ih =>
    haveI : Finite (M ⧸ N.toAddSubgroup) := finite_simple l (M ⧸ N)
    haveI : Finite N.toAddSubgroup := ih
    exact Finite.of_equiv _ (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := N.toAddSubgroup)).symm

private theorem len_le_iff (l : ℕ) [hl : Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (r : ℕ) :
    Module.length ℤ_[l] M ≤ r ↔ Finite M ∧ Nat.card M ≤ l ^ r := by
  constructor
  · intro h
    haveI := finite_of_len l M (Module.length_ne_top_iff.1 (ne_top_of_le_ne_top (ENat.coe_ne_top r) h))
    obtain ⟨k, hk, hc⟩ := lenOfCard l M
    rw [hk] at h
    exact ⟨inferInstance, hc ▸ Nat.pow_le_pow_right hl.out.pos (by exact_mod_cast h)⟩
  · rintro ⟨_, h⟩
    obtain ⟨k, hk, hc⟩ := lenOfCard l M
    rw [hc] at h
    rw [hk]
    exact_mod_cast (Nat.pow_le_pow_iff_right hl.out.one_lt).1 h

private theorem xdual_comp {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {R S A B : Type} [CommRing R] [CommRing S] [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module S B] (ι : A →+ B) (hι : Function.Injective ι) (N : ℕ) (U : Subgroup (G F Ω)) (φ : U → A) :
    φ ∈ XDual N U R A ↔ (fun x => ι (φ x)) ∈ XDual N U S B := by
  have h0 : ∀ a, ι a = 0 ↔ a = 0 := fun a => map_eq_zero_iff ι hι
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1.comp ι, fun a b => by simp only [h2, map_add], fun A u h => (h0 _).2 (h3 A u h),
      fun A hA u h => (h0 _).2 (h4 A hA u h)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨IsLocallyConstant.desc φ ι h1 hι, fun a b => hι (by rw [map_add]; exact h2 a b),
      fun A u h => (h0 _).1 (h3 A u h), fun A hA u h => (h0 _).1 (h4 A hA u h)⟩

theorem UpperTheory.V.Tower.rankXRk :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G k Ω)) (r : ℕ), xRank l N U ≤ r ↔ Two.XRk l N (cycU l U) r := by
  intro k Ω _ _ _ _ _ l _ N U r
  obtain ⟨ι, hι, hr⟩ : ∃ ι : ZMod l →+ QZ l, Function.Injective ι ∧ ∀ x, x ∈ Set.range ι ↔ (l : ℤ_[l]) • x = 0 := by
    obtain ⟨ι, hι, hr, -⟩ := zmodToQZ l 1
    have key : ∀ n, n = l → (∃ ι : ZMod n →+ QZ l, Function.Injective ι ∧ ∀ x, x ∈ Set.range ι ↔ (l : ℤ_[l]) • x = 0) →
        ∃ ι : ZMod l →+ QZ l, Function.Injective ι ∧ ∀ x, x ∈ Set.range ι ↔ (l : ℤ_[l]) • x = 0 := by
      rintro n rfl h
      exact h
    exact key _ (pow_one l) ⟨ι, hι, fun x => by rw [hr, pow_one]⟩
  let f : XDual N (cycU l U) (ZMod l) (ZMod l) → Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]) := fun φ =>
    ⟨⟨fun x => ι (φ.1 x), (xdual_comp ι hι N _ φ.1).1 φ.2⟩,
      (Submodule.mem_torsionBy_iff _ _).2 (Subtype.ext (funext fun x => (hr _).1 ⟨_, rfl⟩))⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (funext fun x => hι (congrFun (congrArg (fun z => z.1.1) h) x)), fun ψ => ?_⟩
    have hψ : ∀ x, ψ.1.1 x ∈ Set.range ι := fun x =>
      (hr _).2 (congrFun (congrArg Subtype.val ((Submodule.mem_torsionBy_iff _ _).1 ψ.2)) x)
    choose φ hφ using hψ
    have h : (fun x => ι (φ x)) = ψ.1.1 := funext hφ
    exact ⟨⟨φ, (xdual_comp ι hι N _ φ).2 (h ▸ ψ.1.2)⟩, Subtype.ext (Subtype.ext h)⟩
  have e := Equiv.ofBijective f hf
  rw [xRank, len_le_iff, ← e.finite_iff, ← Nat.card_congr e]
  exact Iff.rfl
end

