import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.GaloisCohomology.Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthAddMonoidHomFiniteGroupFractionQuotientLe
section
open Formalism.NG

namespace GlobalTheory.HomLen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem length_self_eq_top : Module.length O O = ⊤ := by
  by_contra h
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h
  obtain ⟨_, h2⟩ := h
  haveI : IsArtinianRing O := h2
  exact IsDiscreteValuationRing.not_a_field O
    (IsLocalRing.isField_iff_maximalIdeal_eq.1 (IsArtinianRing.isField_of_isDomain O))

theorem length_ker_smul_le (x : O) :
    Module.length O (LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O)) ≤
      Module.length O (O ⧸ Ideal.span {x}) := by
  by_cases hx : x = 0
  · subst hx
    have e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O :=
      Submodule.quotEquivOfEqBot _ (by simp)
    rw [e.length_eq, length_self_eq_top]
    exact le_top
  set K := FractionRing O
  have hxK : algebraMap O K x ≠ 0 := by
    simpa using (IsFractionRing.injective O K).ne hx
  set c : K := (algebraMap O K x)⁻¹ with hc
  let g0 : O →ₗ[O] KO O := (Submodule.mkQ (1 : Submodule O K)) ∘ₗ LinearMap.toSpanSingleton O K c
  have hg0 : ∀ y, g0 y ∈ LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O) := by
    intro y
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, g0,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply,
      Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    refine ⟨y, ?_⟩
    rw [smul_smul, Algebra.smul_def, hc, map_mul, mul_right_comm, mul_inv_cancel₀ hxK, one_mul]
  let g : O →ₗ[O] LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O) := g0.codRestrict _ hg0
  have hgs : Function.Surjective g := by
    rintro ⟨t, ht⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at ht
    obtain ⟨y, hy⟩ := ht
    refine ⟨y, ?_⟩
    apply Subtype.ext
    simp only [g, g0, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    congr 1
    rw [Algebra.smul_def, hy, Algebra.smul_def, hc, mul_comm _ z, mul_assoc, mul_inv_cancel₀ hxK,
      mul_one]
  have hker : Ideal.span {x} ≤ LinearMap.ker g := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    apply Subtype.ext
    simp only [g, g0, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, ZeroMemClass.coe_zero]
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    refine ⟨1, ?_⟩
    rw [Algebra.smul_def, hc, mul_inv_cancel₀ hxK, map_one]
  have hqs : Function.Surjective ((Ideal.span {x}).liftQ g hker) := by
    intro t
    obtain ⟨y, rfl⟩ := hgs t
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  exact Module.length_le_of_surjective _ hqs

end GlobalTheory.HomLen

namespace GlobalTheory.HomLen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem evalGen_injective {A M : Type} [AddCommGroup A] [AddCommGroup M] (a : A) :
    Function.Injective (fun f : (AddSubgroup.zmultiples a) →+ M =>
      f ⟨a, AddSubgroup.mem_zmultiples a⟩) := by
  intro f g hfg
  ext ⟨b, hb⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hb
  have : (⟨k • a, hb⟩ : AddSubgroup.zmultiples a) = k • ⟨a, AddSubgroup.mem_zmultiples a⟩ := rfl
  simp only at hfg
  rw [this, map_zsmul, map_zsmul, hfg]

def evalGen {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M] (a : A) :
    ((AddSubgroup.zmultiples a) →+ M) →ₗ[O] M where
  toFun f := f ⟨a, AddSubgroup.mem_zmultiples a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem length_cyclic_le (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] {M : Type} [AddCommGroup M]
    [Module O M] (eM : M ≃ₗ[O] KO O) {A : Type} [AddCommGroup A] (a : A) (p : ℕ)
    [Fact p.Prime] (ha : addOrderOf a = p) :
    Module.length O ((AddSubgroup.zmultiples a) →+ M) ≤
      if p = l then Module.length O (O ⧸ Ideal.span {(l : O)}) else 0 := by
  have hkill : ∀ f : (AddSubgroup.zmultiples a) →+ M, p • f ⟨a, AddSubgroup.mem_zmultiples a⟩ = 0 := by
    intro f
    rw [← map_nsmul]
    have : p • (⟨a, AddSubgroup.mem_zmultiples a⟩ : AddSubgroup.zmultiples a) = 0 := by
      apply Subtype.ext
      simp [← ha, addOrderOf_nsmul_eq_zero]
    rw [this, map_zero]
  split_ifs with hpl
  · subst hpl
    let T := LinearMap.ker ((p : O) • LinearMap.id : KO O →ₗ[O] KO O)
    have hT : ∀ f, (eM.toLinearMap ∘ₗ evalGen (O := O) (M := M) a) f ∈ T := by
      intro f
      simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearEquiv.coe_coe, evalGen, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← map_smul, Nat.cast_smul_eq_nsmul, hkill, map_zero]
    let v := (eM.toLinearMap ∘ₗ evalGen (O := O) (M := M) a).codRestrict T hT
    have hv : Function.Injective v := by
      intro f g hfg
      apply evalGen_injective a
      have := congrArg Subtype.val hfg
      simpa [v, evalGen] using this
    exact (Module.length_le_of_injective v hv).trans (length_ker_smul_le _)
  · have hunit : IsUnit (p : O) := by
      have h1 : IsUnit (p : ℤ_[l]) := by
        rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes (Fact.out) (Fact.out)).2 (Ne.symm hpl)
      simpa using h1.map (algebraMap ℤ_[l] O)
    haveI : Subsingleton ((AddSubgroup.zmultiples a) →+ M) := by
      constructor
      intro f g
      apply evalGen_injective a
      simp only
      have hf := hkill f
      have hg := hkill g
      rw [← Nat.cast_smul_eq_nsmul O] at hf hg
      rw [hunit.smul_eq_zero.1 hf, hunit.smul_eq_zero.1 hg]
    rw [Module.length_eq_zero]

end GlobalTheory.HomLen

namespace GlobalTheory.HomLen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def restr {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M] (B : AddSubgroup A) :
    (A →+ M) →ₗ[O] (B →+ M) where
  toFun f := f.comp B.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pull {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M] (B : AddSubgroup A) :
    (A ⧸ B →+ M) →ₗ[O] (A →+ M) where
  toFun g := g.comp (QuotientAddGroup.mk' B)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem length_le_add {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M]
    (B : AddSubgroup A) :
    Module.length O (A →+ M) ≤ Module.length O (A ⧸ B →+ M) + Module.length O (B →+ M) := by
  have hpull : Function.Injective (pull (O := O) (M := M) B) := by
    intro g h hgh
    ext x
    exact DFunLike.congr_fun hgh x
  have hex : Function.Exact (pull (O := O) (M := M) B) (restr (O := O) (M := M) B).rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hle : B ≤ f.ker := by
        intro b hb
        have := DFunLike.congr_fun hf ⟨b, hb⟩
        simpa [restr] using this
      exact ⟨QuotientAddGroup.lift B f hle, by ext x; rfl⟩
    · rintro ⟨g, rfl⟩
      ext b
      show g (QuotientAddGroup.mk (b : A)) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).2 b.2, map_zero]
  rw [Module.length_eq_add_of_exact _ _ hpull (restr B).surjective_rangeRestrict hex]
  gcongr
  exact Module.length_le_of_injective (LinearMap.range (restr (O := O) (M := M) B)).subtype
    (Submodule.subtype_injective _)

theorem length_addMonoidHom_le_of_card_eq (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] {M : Type} [AddCommGroup M]
    [Module O M] (eM : M ≃ₗ[O] KO O) (n : ℕ) :
    ∀ (A : Type) [AddCommGroup A] [Finite A], Nat.card A = n →
      Module.length O (A →+ M) ≤
        Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l n : ℕ∞) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ hn
  by_cases h1 : n = 1
  · haveI : Subsingleton A := by
      exact (Nat.card_eq_one_iff_unique.1 (hn.trans h1)).1
    haveI : Subsingleton (A →+ M) :=
      ⟨fun f g => by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    rw [Module.length_eq_zero]
    simp
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  haveI := Fact.mk hp
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' (G := A) p (hn ▸ hpn)
  set B := AddSubgroup.zmultiples a
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B
  rw [Nat.card_zmultiples, ha, hn] at hcard
  have hn0 : n ≠ 0 := by rw [← hn]; exact Nat.card_pos.ne'
  have hq0 : Nat.card (A ⧸ B) ≠ 0 := by
    rintro h; rw [h, zero_mul] at hcard; exact hn0 hcard
  have hlt : Nat.card (A ⧸ B) < n := by
    rw [hcard]; exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hq0) hp.one_lt
  have ihq := ih _ hlt (A ⧸ B) rfl
  have hB := length_cyclic_le l eM a p ha
  have hv : padicValNat l n = padicValNat l (Nat.card (A ⧸ B)) + (if p = l then 1 else 0) := by
    rw [hcard, padicValNat.mul hq0 hp.ne_zero]
    congr 1
    split_ifs with h
    · subst h; exact padicValNat_self
    · exact padicValNat_primes (Ne.symm h)
  calc Module.length O (A →+ M)
      ≤ Module.length O (A ⧸ B →+ M) + Module.length O (B →+ M) := length_le_add B
    _ ≤ Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (Nat.card (A ⧸ B)) : ℕ∞) +
          (if p = l then Module.length O (O ⧸ Ideal.span {(l : O)}) else 0) := add_le_add ihq hB
    _ = Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l n : ℕ∞) := by
      rw [hv]
      split_ifs <;> simp [mul_add]

theorem length_addMonoidHom_le : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] (M : Type) [AddCommGroup M] [Module O M] (eM : M ≃ₗ[O] KO O)
    (A : Type) [AddCommGroup A] [Finite A],
    Module.length O (A →+ M) ≤
      Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (Nat.card A) : ℕ∞) := by
  intro l _ O _ _ _ _ M _ _ eM A _ _
  exact length_addMonoidHom_le_of_card_eq l eM _ A rfl

end GlobalTheory.HomLen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuCocycleCoboundaryLift
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.MuTowerInj

section Abstract

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {R₁ R₂ R₃ M₁ M₂ M₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]
  [DiscreteTopology M₁] [DiscreteTopology M₂] [DiscreteTopology M₃]

def twoCocycleMapOfEquivariantAdd (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) : Z2 ρ₁ →+ Z2 ρ₂ where
  toFun f := ⟨u ∘ f.1, (continuous_of_discreteTopology (f := u)).comp f.2.1, fun g h k => by
    simp only [Function.comp_apply, ← hu, ← map_sub, ← map_add, f.2.2 g h k, map_zero]⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero u)
  map_add' f f' := Subtype.ext (funext fun _ => map_add u _ _)

def secondCohomologyMapOfEquivariantAdd (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) : H2 ρ₁ →+ H2 ρ₂ :=
  QuotientAddGroup.map ((B2 ρ₁).comap (Z2 ρ₁).subtype).toAddSubgroup
    ((B2 ρ₂).comap (Z2 ρ₂).subtype).toAddSubgroup (twoCocycleMapOfEquivariantAdd ρ₁ ρ₂ u hu) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem ρ₁ _).1 hf
    refine (separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨u ∘ c, (continuous_of_discreteTopology (f := u)).comp hc, ?_⟩
    funext p
    have e := congrFun hcf p
    simp only [Submodule.coe_subtype] at e
    change _ = u (f.1 p)
    rw [← e]
    simp [d1, hu]

theorem mapH2Add_mk (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) (z : Z2 ρ₁) :
    secondCohomologyMapOfEquivariantAdd ρ₁ ρ₂ u hu (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (twoCocycleMapOfEquivariantAdd ρ₁ ρ₂ u hu z) := rfl

theorem ker_le_range [ContinuousMul Γ] (ρ₁ : Representation R₁ Γ M₁)
    (ρ₂ : Representation R₂ Γ M₂) (ρ₃ : Representation R₃ Γ M₃) (h₂ : ContAction ρ₂)
    (u : M₁ →+ M₂) (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m))
    (p : M₂ →+ M₃) (hp : ∀ g m, p (ρ₂ g m) = ρ₃ g (p m))
    (hinj : Function.Injective u) (hsurj : Function.Surjective p)
    (hex : ∀ m, p m = 0 → ∃ k, u k = m) :
    (secondCohomologyMapOfEquivariantAdd ρ₂ ρ₃ p hp).ker ≤ (secondCohomologyMapOfEquivariantAdd ρ₁ ρ₂ u hu).range := by
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [AddMonoidHom.mem_ker, mapH2Add_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem ρ₃ _).1 hx

  have hsc : Continuous (Function.surjInv hsurj ∘ c) :=
    (continuous_of_discreteTopology (f := Function.surjInv hsurj)).comp hc
  have hb : d1 ρ₂ (Function.surjInv hsurj ∘ c) ∈ Z2 ρ₂ :=
    coboundaries2_le_cocycles2 ρ₂ h₂ ((separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨_, hsc, rfl⟩)
  have hf' : f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c) ∈ Z2 ρ₂ := (Z2 ρ₂).sub_mem f.2 hb

  have hker : ∀ q, p ((f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) q) = 0 := by
    rintro ⟨g, h⟩
    have e : ρ₃ g (c h) - c (g * h) + c g = p (f.1 (g, h)) := by
      have e0 := congrFun hcf (g, h)
      rw [d1_apply] at e0
      exact e0
    rw [Pi.sub_apply, d1_apply, map_sub, map_add, map_sub, hp]
    simp only [Function.comp_apply, Function.surjInv_eq hsurj]
    rw [e, sub_self]
  obtain ⟨k, hk⟩ : ∃ k : Γ × Γ → M₁, ∀ q, u (k q) = (f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) q :=
    ⟨fun q => Function.invFun u _, fun q => Function.invFun_eq (hex _ (hker q))⟩
  have hkc : Continuous k := by
    have hk' : k = Function.invFun u ∘ (f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) := by
      funext q
      rw [Function.comp_apply, ← hk q, Function.leftInverse_invFun hinj]
    rw [hk']
    exact (continuous_of_discreteTopology (f := Function.invFun u)).comp ((mem_cocycles2 ρ₂ _).1 hf').1
  have hkZ : k ∈ Z2 ρ₁ := by
    refine (mem_cocycles2 ρ₁ k).2 ⟨hkc, fun g h t => hinj ?_⟩
    rw [map_zero, map_sub, map_add, map_sub, hu, hk, hk, hk, hk]
    exact ((mem_cocycles2 ρ₂ _).1 hf').2 g h t
  refine AddMonoidHom.mem_range.2 ⟨Submodule.Quotient.mk ⟨k, hkZ⟩, ?_⟩
  rw [mapH2Add_mk, Submodule.Quotient.eq, Submodule.mem_comap]
  refine (separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨-(Function.surjInv hsurj ∘ c), hsc.neg, ?_⟩
  funext q
  rw [map_neg, Pi.neg_apply]
  show _ = u (k q) - f.1 q
  rw [hk q, Pi.sub_apply]
  abel

theorem injective_of_card {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Finite A] [Finite B] [Finite C] (f : A →+ B) (g : B →+ C) (h : g.ker ≤ f.range)
    (hc : Nat.card B = Nat.card A * Nat.card C) : Function.Injective f := by
  have eA : Nat.card f.ker * Nat.card f.range = Nat.card A := by
    rw [← AddSubgroup.index_ker]
    exact AddSubgroup.card_mul_index _
  have eB : Nat.card g.ker * Nat.card g.range = Nat.card B := by
    rw [← AddSubgroup.index_ker]
    exact AddSubgroup.card_mul_index _
  have h1 : Nat.card g.ker ≤ Nat.card f.range := AddSubgroup.card_le_of_le h
  have h2 : Nat.card g.range ≤ Nat.card C :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hpos : 0 < Nat.card f.range * Nat.card C := Nat.mul_pos Nat.card_pos Nat.card_pos

  have hk : Nat.card f.ker ≤ 1 := by
    by_contra hne
    rw [not_le] at hne
    have hlt : Nat.card f.range * Nat.card C < Nat.card f.range * Nat.card C :=
      calc Nat.card f.range * Nat.card C
          < Nat.card f.ker * (Nat.card f.range * Nat.card C) := lt_mul_of_one_lt_left hpos hne
        _ = Nat.card A * Nat.card C := by rw [← eA, mul_assoc]
        _ = Nat.card B := hc.symm
        _ = Nat.card g.ker * Nat.card g.range := eB.symm
        _ ≤ Nat.card f.range * Nat.card C := Nat.mul_le_mul h1 h2
    exact lt_irrefl _ hlt
  rw [AddSubgroup.card_le_one_iff_eq_bot] at hk
  exact (AddMonoidHom.ker_eq_bot_iff f).1 hk

end Abstract

section Cyclic

variable (l : ℕ) [Fact l.Prime] (n : ℕ)

omit [Fact l.Prime] in
theorem pow_mul_val (x : ℕ) :
    ((l ^ n * (x : ZMod (l ^ 1)).val : ℕ) : ZMod (l ^ (n + 1))) = ((l ^ n * x : ℕ) : _) := by
  rw [ZMod.val_natCast, pow_one]
  conv_rhs => rw [← Nat.mod_add_div x l]
  rw [mul_add, Nat.cast_add, ← mul_assoc, ← pow_succ, Nat.cast_mul (l ^ (n + 1)), ZMod.natCast_self,
    zero_mul, add_zero]

def iota : ZMod (l ^ 1) →+ ZMod (l ^ (n + 1)) :=
  AddMonoidHom.mk' (fun b => ((l ^ n * b.val : ℕ) : ZMod (l ^ (n + 1)))) fun a b => by
    obtain ⟨x, rfl⟩ := ZMod.natCast_zmod_surjective a
    obtain ⟨y, rfl⟩ := ZMod.natCast_zmod_surjective b
    rw [← Nat.cast_add, pow_mul_val, pow_mul_val, pow_mul_val, mul_add, Nat.cast_add]

theorem iota_apply (b : ZMod (l ^ 1)) :
    iota l n b = ((l ^ n * b.val : ℕ) : ZMod (l ^ (n + 1))) := rfl

theorem iota_natCast (x : ℕ) : iota l n x = ((l ^ n * x : ℕ) : ZMod (l ^ (n + 1))) := by
  rw [iota_apply, pow_mul_val]

theorem iota_injective : Function.Injective (iota l n) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  rw [iota_apply, CharP.cast_eq_zero_iff (ZMod (l ^ (n + 1))) (l ^ (n + 1)), pow_succ,
    Nat.mul_dvd_mul_iff_left (pow_pos (Fact.out : l.Prime).pos n)] at hb
  have hlt : b.val < l := by simpa using ZMod.val_lt b
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt hb hlt

theorem iota_mul (u : ℤ_[l]) (b : ZMod (l ^ 1)) :
    iota l n (PadicInt.toZModPow 1 u * b) = PadicInt.toZModPow (n + 1) u * iota l n b := by
  obtain ⟨y, rfl⟩ := ZMod.natCast_zmod_surjective b
  set w := PadicInt.toZModPow (n + 1) u with hw

  have h1 : PadicInt.toZModPow 1 u = ((w.val : ℕ) : ZMod (l ^ 1)) := by
    rw [← PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega), RingHom.comp_apply,
      ZMod.castHom_apply, ZMod.cast_eq_val]
  have h2 : ((w.val : ℕ) : ZMod (l ^ (n + 1))) = w := ZMod.natCast_zmod_val w
  rw [h1, ← Nat.cast_mul, iota_natCast, iota_natCast]
  conv_rhs => rw [← h2]
  push_cast
  ring

def red : ZMod (l ^ (n + 1)) →+* ZMod (l ^ n) :=
  ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))

theorem red_toZModPow (u : ℤ_[l]) :
    red l n (PadicInt.toZModPow (n + 1) u) = PadicInt.toZModPow n u := by
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) u

omit [Fact l.Prime] in
theorem red_surjective : Function.Surjective (red l n) := by
  exact ZMod.ringHom_surjective (red l n)

theorem exists_iota_of_red (m : ZMod (l ^ (n + 1))) (hm : red l n m = 0) :
    ∃ k, iota l n k = m := by
  have h0 : ((m.val : ℕ) : ZMod (l ^ n)) = 0 := by
    rw [← ZMod.cast_eq_val]
    exact hm
  rw [CharP.cast_eq_zero_iff (ZMod (l ^ n)) (l ^ n)] at h0
  obtain ⟨t, ht⟩ := h0
  exact ⟨t, by rw [iota_natCast, ← ht, ZMod.natCast_zmod_val]⟩

end Cyclic

theorem card_H2_muLoc (hD : LocalTateDuality) (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (hA : IsPlaceOver A v) (r : ℕ) :
    Nat.card (H2 (muLoc F l r A)) = l ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  ·
    have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    have : Subsingleton (H2 (muLoc F l 0 A)) := ⟨fun x y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (Subtype.ext (funext fun _ => Subsingleton.elim _ _))⟩
    exact (Nat.card_of_subsingleton (0 : H2 (muLoc F l 0 A))).trans (pow_zero l).symm
  · obtain ⟨⟨e⟩, -⟩ := hD F Ω l r (ZMod (l ^ r)) A (muLoc F l r A) v hr hA
      (GlobalTheory.TameQuot.contAction_muDec A l r)
    exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)

theorem mk_eq_zero_of_coboundary : LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (n : ℕ) (w : Z2 (muLoc F l 1 A)) (a : Dec (F := F) A → ZMod (l ^ (n + 1))), Continuous a → (∀ g h : Dec (F := F) A, ((cycMod F Ω l (n + 1) g : (ZMod (l ^ (n + 1)))ˣ) : ZMod (l ^ (n + 1))) * a h - a (g * h) + a g = ((l ^ n * (w.1 (g, h)).val : ℕ) : ZMod (l ^ (n + 1)))) → (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  intro hD F Ω _ _ _ _ _ l _ A v hA n w a ha hrel

  have hu : ∀ (g : Dec (F := F) A) (m : ZMod (l ^ 1)),
      iota l n (muLoc F l 1 A g m) = muLoc F l (n + 1) A g (iota l n m) := fun g m =>
    iota_mul l n ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) m
  have hp : ∀ (g : Dec (F := F) A) (m : ZMod (l ^ (n + 1))),
      (red l n).toAddMonoidHom (muLoc F l (n + 1) A g m) =
        muLoc F l n A g ((red l n).toAddMonoidHom m) := by
    intro g m
    show red l n (PadicInt.toZModPow (n + 1) ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) * m) =
      PadicInt.toZModPow n ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) * red l n m
    rw [map_mul, red_toZModPow]
  have hcard : ∀ r, Nat.card (H2 (muLoc F l r A)) = l ^ r := card_H2_muLoc hD F Ω l A v hA
  have : ∀ r, Finite (H2 (muLoc F l r A)) := fun r =>
    Nat.finite_of_card_ne_zero (by rw [hcard r]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)

  have hinj := injective_of_card
    (secondCohomologyMapOfEquivariantAdd (muLoc F l 1 A) (muLoc F l (n + 1) A) (iota l n) hu)
    (secondCohomologyMapOfEquivariantAdd (muLoc F l (n + 1) A) (muLoc F l n A) (red l n).toAddMonoidHom hp)
    (ker_le_range _ _ _ (GlobalTheory.TameQuot.contAction_muDec A l (n + 1)) _ hu _ hp
      (iota_injective l n) (red_surjective l n) (exists_iota_of_red l n))
    (by rw [hcard, hcard, hcard]; ring)
  apply hinj
  rw [map_zero, mapH2Add_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨a, ha, ?_⟩
  funext ⟨g, h⟩
  rw [d1_apply]
  exact (hrel g h).trans (iota_apply l n _).symm

end GlobalTheory.MuTowerInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotIsRootResidueCofactorUnramifiedExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isRoot_residue_cofactor_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O, (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z) → ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic → r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree → p.natDegree = d * r.natDegree → p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) → ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := by
  first | exact @GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor | exact GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor | (intros; apply GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValIntStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l], ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 → ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  first | exact @GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one | exact GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one | (intros; apply GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesTwistedScalingTriangularLaurentStatement
section
open GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesTwistedScaling_triangular_laurent : ∀ {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M] (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M), Monotone Sub → ∀ (y : ℕ) (f : ℤ → M), (∃ m : ℤ, ∀ j < m, f j = 0) → (∀ j, f j ∈ Sub j) → ∀ k : ℤ, (∀ j < k, f j ∈ Sub (j - y)) → (∃ m : ℤ, ∀ j < m, conv w (fun m => u ^ m • f m) j = 0) ∧ (∀ j, conv w (fun m => u ^ m • f m) j ∈ Sub j) ∧ (∀ j < k, conv w (fun m => u ^ m • f m) j ∈ Sub (j - y)) ∧ conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k ∈ Sub (k - y) := by
  first | exact @GlobalTheory.NL.Twist.tri | exact GlobalTheory.NL.Twist.tri | (intros; apply GlobalTheory.NL.Twist.tri <;> assumption)
end

