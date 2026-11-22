import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0085
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicIntegralReadingOfTrivialisations
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureGaloisStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.RingSide

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

def jMap (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂) :
    integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* M₂.Z.presheaf.stalk z₂ :=
  (M₂.stalkEquiv z₂).symm.toRingHom.comp ((RingHom.id Ω₂).restrict _ (M₂.O z₂) h)

theorem stalkHom_jMap (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) : M₂.stalkHom z₂ (jMap z₂ h b) = b := by
  rw [← RatModel.coe_stalkEquiv]
  simp [jMap]

theorem jMap_mem_max_iff (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (c : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) :
    jMap z₂ h c ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂) ↔ ¬ ((c : Ω₂) ≠ 0 ∧ (c : Ω₂)⁻¹ ∈ M₂.O z₂) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← MulEquiv.isUnit_map (M₂.stalkEquiv z₂).toMulEquiv, RatModel.isUnit_O_iff]
  change ¬ ((M₂.stalkEquiv z₂ (jMap z₂ h c) : Ω₂) ≠ 0 ∧ (M₂.stalkEquiv z₂ (jMap z₂ h c) : Ω₂)⁻¹ ∈ M₂.O z₂) ↔ _
  rw [RatModel.coe_stalkEquiv, stalkHom_jMap]

theorem algHom_mem_integralClosure
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    (τ : Ω₂ →ₐ[Ω₁] Ω₂) {b : Ω₂} (hb : b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) :
    τ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ := by
  let τ' : Ω₂ →ₐ[M₁.Z.presheaf.stalk z₁] Ω₂ :=
    { τ.toRingHom with
      commutes' := fun x => by
        change τ (algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x) = algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x
        rw [halg]
        exact τ.commutes _ }
  exact IsIntegral.map τ' hb

theorem algHom_mem_O
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) {z₂ : M₂.Z}
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    (τ : Ω₂ →ₐ[Ω₁] Ω₂)
    (hu : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ → (τ s)⁻¹ ∈ M₂.O z₂)
    {x : Ω₂} (hx : x ∈ M₂.O z₂) : τ x ∈ M₂.O z₂ := by
  obtain ⟨b, hb, s, hs, hs0, hsO, rfl⟩ := hloc x hx
  rw [map_div₀, div_eq_mul_inv]
  exact mul_mem (hB _ (algHom_mem_integralClosure halg τ hb)) (hu s hs hs0 hsO)

end GlobalTheory.Poinc.RingSide

namespace GlobalTheory.Poinc.RingSide

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

theorem exists_stalk_ringEquiv
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) (z₂ : M₂.Z)
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (H : ∀ b b' : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, (b' : Ω₂) = σ b →
      (jMap z₂ hB b ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂) ↔ jMap z₂ hB b' ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂))) :
    ∃ σ₂ : M₂.Z.presheaf.stalk z₂ ≃+* M₂.Z.presheaf.stalk z₂, ∀ x, M₂.stalkHom z₂ (σ₂ x) = σ (M₂.stalkHom z₂ x) := by
  have hu : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ →
      (σ.toAlgHom s)⁻¹ ∈ M₂.O z₂ := by
    intro s hs hs0 hsO
    have hs' : σ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ :=
      algHom_mem_integralClosure halg σ.toAlgHom hs
    have key := H ⟨s, hs⟩ ⟨σ s, hs'⟩ rfl
    rw [jMap_mem_max_iff, jMap_mem_max_iff] at key
    exact ((not_iff_not.mp key).mp ⟨hs0, hsO⟩).2
  have hu' : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ →
      (σ.symm.toAlgHom s)⁻¹ ∈ M₂.O z₂ := by
    intro s hs hs0 hsO
    have ht : σ.symm s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ :=
      algHom_mem_integralClosure halg σ.symm.toAlgHom hs
    have key := H ⟨σ.symm s, ht⟩ ⟨s, hs⟩ (σ.apply_symm_apply s).symm
    rw [jMap_mem_max_iff, jMap_mem_max_iff] at key
    exact ((not_iff_not.mp key).mpr ⟨hs0, hsO⟩).2
  have hσ : ∀ x ∈ M₂.O z₂, σ x ∈ M₂.O z₂ := fun x hx =>
    algHom_mem_O halg hB hloc σ.toAlgHom hu hx
  have hσ' : ∀ x ∈ M₂.O z₂, σ.symm x ∈ M₂.O z₂ := fun x hx =>
    algHom_mem_O halg hB hloc σ.symm.toAlgHom hu' hx
  let e : M₂.O z₂ ≃+* M₂.O z₂ :=
    { toFun := fun x => ⟨σ x, hσ x x.2⟩
      invFun := fun x => ⟨σ.symm x, hσ' x x.2⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : Ω₂))
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : Ω₂))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : Ω₂) y)
      map_add' := fun x y => Subtype.ext (map_add σ (x : Ω₂) y) }
  refine ⟨(M₂.stalkEquiv z₂).trans (e.trans (M₂.stalkEquiv z₂).symm), fun x => ?_⟩
  rw [← RatModel.coe_stalkEquiv, ← RatModel.coe_stalkEquiv]
  simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

theorem injective_of_ext
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) {z₂ : M₂.Z}
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    {V V' : Type} [CommRing V] [CommRing V'] (ev : M₁.Z.presheaf.stalk z₁ →+* V) (io : V →+* V')
    (ev₂ : M₂.Z.presheaf.stalk z₂ →+* V') (hev : Function.Injective ev) (hio : Function.Injective io)
    (hE : ∀ x x₂, M₂.stalkHom z₂ x₂ = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x) → ev₂ x₂ = io (ev x)) :
    Function.Injective ev₂ := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  by_contra hy0
  have hY : M₂.stalkHom z₂ y ≠ 0 := by
    intro h
    apply hy0
    apply M₂.stalkHom_injective z₂
    rw [h, map_zero]
  have hYO : M₂.stalkHom z₂ y ∈ M₂.O z₂ := by
    rw [← RatModel.coe_stalkEquiv]
    exact (M₂.stalkEquiv z₂ y).2
  obtain ⟨b, hb, s, hs, hs0, -, hYe⟩ := hloc _ hYO
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_div] at hYe
    exact hY hYe
  have hjb : jMap z₂ hB ⟨b, hb⟩ = y * jMap z₂ hB ⟨s, hs⟩ := by
    apply M₂.stalkHom_injective z₂
    rw [map_mul, stalkHom_jMap, stalkHom_jMap, hYe]
    exact (div_mul_cancel₀ b hs0).symm
  have hev0 : ev₂ (jMap z₂ hB ⟨b, hb⟩) = 0 := by
    rw [hjb, map_mul, hy, zero_mul]
  have hbB : (⟨b, hb⟩ : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) ≠ 0 := fun h =>
    hb0 (congrArg Subtype.val h)
  have hne := Ideal.comap_ne_bot_of_integral_mem hbB (Ideal.mem_span_singleton_self _)
    (integralClosure.isIntegral _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, hc⟩ := ha
  have h1 : ev₂ (jMap z₂ hB (algebraMap _ _ a)) = io (ev a) := by
    apply hE
    rw [stalkHom_jMap]
    exact halg a
  have h2 : ev₂ (jMap z₂ hB (algebraMap _ _ a)) = 0 := by
    rw [← hc, map_mul, map_mul, hev0, mul_zero]
  rw [h2] at h1
  have h3 : ev a = ev 0 := hio (by rw [map_zero, map_zero, ← h1])
  exact ha0 (hev h3)

end GlobalTheory.Poinc.RingSide

open GlobalTheory.Poinc.RingSide in

theorem GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  intro g n F W Z i X₁ act 𝔗 z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ :=
    ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ x =
      algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom z₁ x) := fun _ => rfl
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme 𝔗.X₂.M.Z := by
    exact @GlobalTheory.IsNormalScheme.pred _ 𝔗.X₂.normal
  obtain ⟨𝔷, h𝔷⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁)
  obtain ⟨z₂, hz₂, hmem⟩ := GlobalTheory.Poinc.FinPts.maximal_point hN 𝔗.p_fin 𝔗.p_pt halg 𝔷 h𝔷
  have hB : ∀ b ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, b ∈ 𝔗.X₂.M.O z₂ :=
    fun b hb => GlobalTheory.Poinc.FinPts.mem_O_of_isIntegral hN 𝔗.p_pt halg hb hz₂
  have hloc := GlobalTheory.Poinc.exists_div_integralClosure_of_mem_O _ _ _ _ X₁.M 𝔗.X₂.M 𝔗.p hN
    𝔗.p_fin 𝔗.p_pt z₁ z₂ hz₂
  refine ⟨z₂, jMap z₂ hB, hz₂, fun b => stalkHom_jMap z₂ hB b, ?_, ?_, ?_, ?_⟩
  · have hc : (maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap (jMap z₂ hB) = 𝔷 := by
      ext c
      rw [Ideal.mem_comap, jMap_mem_max_iff, hmem c]
      tauto
    rw [hc]
    exact h𝔷
  · intro x hx
    exact GlobalTheory.Poinc.FinPts.isIntegral_of_mem_O 𝔗.p_fin 𝔗.p_pt halg hx
  · intro σ H
    exact exists_stalk_ringEquiv halg z₂ hB hloc σ H
  · intro V _ ev V' _ io ev₂ hev hio hE
    exact injective_of_ext halg hB hloc ev io ev₂ hev hio hE.2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDescent

theorem restrict_isPullback {R : Type} [CommRing R] {S Y Z Y' : Scheme.{0}} {π : S ⟶ Sp R} {y : Y ⟶ Sp R}
    {p : Z ⟶ Y} {q : Z ⟶ S} (hpb : IsPullback p q y π) (f : Y' ⟶ Y) :
    IsPullback (pullback.snd p f) (pullback.fst p f ≫ q) (f ≫ y) π :=
  IsPullback.paste_vert (IsPullback.of_hasPullback p f).flip hpb

theorem uniq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (W : Scheme.{0}) (g₁ g₂ : Y ⟶ W), p ≫ g₁ = p ≫ g₂ → g₁ = g₂ := by
  intro R _ _ _ _ S Y Z π y p q hprop hsurj hint hflat hpb W g₁ g₂ he
  have hpS : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hsurj
  have heqz := GlobalTheory.T.flat_descent_sections_injective_equalizer R S Y Z π y p q hprop hsurj hint hflat hpb
  have hbase : g₁.base = g₂.base := by
    ext x
    obtain ⟨z, rfl⟩ := p.surjective x
    have := congrArg (fun k : Z ⟶ W => k z) he
    simpa only [Scheme.Hom.comp_apply] using this
  refine Scheme.Hom.ext hbase fun U => ?_
  have : Mono (p.app (g₂ ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (heqz _).1
  rw [← cancel_mono (p.app (g₂ ⁻¹ᵁ U)), ← Scheme.Hom.comp_app, Scheme.Hom.congr_app he.symm,
    Category.assoc, Scheme.Hom.naturality, ← Category.assoc, ← Scheme.Hom.comp_app]
  rfl

theorem exAff : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (W : Scheme.{0}) [IsAffine W] (h : Z ⟶ W), pullback.fst p p ≫ h = pullback.snd p p ≫ h → ∃ h₀ : Y ⟶ W, p ≫ h₀ = h := by
  intro R _ _ _ _ S Y Z π y p q hprop hsurj hint hflat hpb W _ h hh
  obtain ⟨hinj, hdesc⟩ := GlobalTheory.T.flat_descent_sections_injective_equalizer R S Y Z π y p q hprop hsurj hint hflat hpb ⊤
  have hmem : ∀ x : Γ(W, ⊤), h.appTop x ∈ (p.app ⊤).hom.range := by
    intro x
    refine hdesc (h.appTop x) fun e => ?_
    have := congrArg (fun k : pullback p p ⟶ W => k.appTop.hom x) hh
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.trans ?_
    change _ = (CommRingCat.Hom.hom ((pullback p p).presheaf.map (𝟙 (Opposite.op (⊤ : (pullback p p).Opens)))))
      ((pullback.snd p p).appTop.hom (h.appTop.hom x))
    rw [CategoryTheory.Functor.map_id]
    rfl
  let φ : Γ(W, ⊤) →+* Γ(Y, ⊤) :=
    (RingEquiv.ofBijective (p.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (p.app ⊤).hom.rangeRestrict_surjective⟩).symm.toRingHom.comp
      (h.appTop.hom.codRestrict _ hmem)
  have hφ : CommRingCat.ofHom φ ≫ p.appTop = h.appTop := by
    ext x
    exact congrArg Subtype.val ((RingEquiv.ofBijective (p.app ⊤).hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (p.app ⊤).hom.rangeRestrict_surjective⟩).apply_symm_apply
      (h.appTop.hom.codRestrict _ hmem x))
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫ W.isoSpec.inv, ?_⟩
  have h1 : h = Z.toSpecΓ ≫ Spec.map h.appTop ≫ W.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  rw [h1, ← Category.assoc p, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp_assoc, hφ]

theorem descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ h : Z ⟶ W, pullback.fst p p ≫ h = pullback.snd p p ≫ h → ∃! h₀ : Y ⟶ W, p ≫ h₀ = h := by
  intro R _ _ _ _ S Y Z W π y p q hprop hsurj hint hflat hpb h hh
  have hpS : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hsurj
  have hpC : UniversallyClosed p := MorphismProperty.of_isPullback (P := @UniversallyClosed) hpb.flip inferInstance
  have hfib : Function.FactorsThrough h.base.hom p.base.hom := by
    intro a b hab
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := p) a b hab
    have := congrArg (fun k : pullback p p ⟶ W => k z) hh
    simp only [Scheme.Hom.comp_apply, hz1, hz2] at this
    exact this
  have hq : Topology.IsQuotientMap p.base.hom :=
    IsClosedMap.isQuotientMap p.isClosedMap p.base.hom.continuous p.surjective
  let b : Y.carrier ⟶ W.carrier := TopCat.ofHom (hq.lift h.base.hom hfib)
  have hb : ∀ z, b (p z) = h z := fun z => congrArg (fun k : C(Z, W) => k z) (hq.lift_comp h.base.hom hfib)
  let V : W.affineOpens → Y.Opens := fun i => TopologicalSpace.Opens.comap b.hom i.1
  have hV : TopologicalSpace.IsOpenCover V := W.isBasis_affineOpens.isOpenCover.comap b.hom
  let 𝒰 := Y.openCoverOfIsOpenCover V hV
  have hloc : ∀ i, ∃ u : (V i).toScheme ⟶ W, pullback.snd p (V i).ι ≫ u = pullback.fst p (V i).ι ≫ h := by
    intro i
    have hr : Set.range (pullback.fst p (V i).ι ≫ h) ⊆ Set.range i.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, ← hb, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply]
      exact ((pullback.snd p (V i).ι) w).2
    let hi := IsOpenImmersion.lift i.1.ι _ hr
    have : IsAffine i.1.toScheme := i.2
    have heq : pullback.fst (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ hi =
        pullback.snd (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ hi := by
      rw [← cancel_mono i.1.ι]
      simp only [Category.assoc, hi, IsOpenImmersion.lift_fac]
      let m : pullback (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ⟶ pullback p p :=
        pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _)
          (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc])
      have e1 : pullback.fst (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ pullback.fst p (V i).ι =
          m ≫ pullback.fst p p := (pullback.lift_fst _ _ _).symm
      have e2 : pullback.snd (pullback.snd p (V i).ι) (pullback.snd p (V i).ι) ≫ pullback.fst p (V i).ι =
          m ≫ pullback.snd p p := (pullback.lift_snd _ _ _).symm
      rw [reassoc_of% e1, reassoc_of% e2, hh]
    obtain ⟨u, hu⟩ := exAff R S (V i).toScheme (pullback p (V i).ι) π ((V i).ι ≫ y) (pullback.snd p (V i).ι)
      (pullback.fst p (V i).ι ≫ q) hprop hsurj hint inferInstance (restrict_isPullback hpb _) i.1.toScheme hi heq
    exact ⟨u ≫ i.1.ι, by rw [← Category.assoc, hu, IsOpenImmersion.lift_fac]⟩
  choose u hu using hloc
  have hc : ∀ i j, pullback.fst (V i).ι (V j).ι ≫ u i = pullback.snd (V i).ι (V j).ι ≫ u j := by
    intro i j
    let f := pullback.fst (V i).ι (V j).ι ≫ (V i).ι
    apply uniq R S _ (pullback p f) π (f ≫ y) (pullback.snd p f) (pullback.fst p f ≫ q) hprop hsurj hint
      inferInstance (restrict_isPullback hpb f) W
    let mi : pullback p f ⟶ pullback p (V i).ι := pullback.lift (pullback.fst p f)
      (pullback.snd p f ≫ pullback.fst _ _) (by rw [pullback.condition, Category.assoc])
    let mj : pullback p f ⟶ pullback p (V j).ι := pullback.lift (pullback.fst p f)
      (pullback.snd p f ≫ pullback.snd _ _) (by
        rw [pullback.condition]
        show pullback.snd p f ≫ pullback.fst (V i).ι (V j).ι ≫ (V i).ι = _
        rw [pullback.condition, Category.assoc])
    have ei : pullback.snd p f ≫ pullback.fst (V i).ι (V j).ι = mi ≫ pullback.snd p (V i).ι :=
      (pullback.lift_snd _ _ _).symm
    have ej : pullback.snd p f ≫ pullback.snd (V i).ι (V j).ι = mj ≫ pullback.snd p (V j).ι :=
      (pullback.lift_snd _ _ _).symm
    rw [reassoc_of% ei, reassoc_of% ej, hu, hu, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  have hglue : p ≫ 𝒰.glueMorphisms u hc = h := by
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ p) _ _ fun i => ?_
    change pullback.fst p (V i).ι ≫ _ = pullback.fst p (V i).ι ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc]
    change pullback.snd p (V i).ι ≫ 𝒰.f i ≫ _ = _
    exact (congrArg (pullback.snd p (V i).ι ≫ ·) (𝒰.ι_glueMorphisms u hc i)).trans (hu i)
  refine ⟨𝒰.glueMorphisms u hc, hglue, fun g hg => ?_⟩
  exact uniq R S Y Z π y p q hprop hsurj hint hflat hpb W g _ (hg.trans hglue.symm)

end GlobalTheory.MorDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCentredPointGenericBothModels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DvrTrait
open GlobalTheory.Points

theorem exists_factor_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {K : Type} [Field K] (y : Sp K ⟶ M.Z) (hy : ∀ w, y w = genericPoint M.Z) :
    ∃ β : Ω →+* K, y = spMap β ≫ M.pt := by
  have hs : ∀ w, y w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf y _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  refine ⟨β, ?_⟩
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
  have h1 := top_le_preimage_of_specializes hs hz
  have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
  refine ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_
  exact ((valR_spMap_comp β M.pt U h2 f).trans (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f)).symm

theorem exists_trait : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y X M : RatModel o Ω)
    (f : M.Z ⟶ X.Z) (d : Y.Z ⟶ X.Z), X.IsHom M (AlgHom.id o Ω) f → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d →
    ∀ z : M.Z, f z ∈ Set.range d → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (ξ : Sp V ⟶ M.Z) (τ : Sp V ⟶ Y.Z) (κ : Ω →+* FractionRing V), z ∈ Set.range ξ ∧
      spMap (algebraMap V (FractionRing V)) ≫ ξ = spMap κ ≫ M.pt ∧
      spMap (algebraMap V (FractionRing V)) ≫ τ = spMap κ ≫ Y.pt := by
  intro o Ω _ _ _ _ Y X M f d hf hd hop z hz
  obtain ⟨V, _, _, _, _, ξ, -, hξ, w, hw⟩ := GlobalTheory.DvrCentre.exists_complete_dvr_centre o Ω M z
  have ef : M.pt ≫ f = X.pt := by
    have h := hf
    have e : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    rw [RatModel.IsHom, e, Category.id_comp] at h
    exact h
  have ed : Y.pt ≫ d = X.pt := by
    have h := hd
    have e : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    rw [RatModel.IsHom, e, Category.id_comp] at h
    exact h
  have hbot : ξ (⊥ : PrimeSpectrum V) = genericPoint M.Z := by
    have h2 : (⊥ : PrimeSpectrum V) ⤳ w := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have h3 := h2.map ξ.continuous
    rw [hw] at h3
    exact (h3.antisymm (genericPoint_specializes _)).eq
  have hy : ∀ u, (spMap (algebraMap V (FractionRing V)) ≫ ξ) u = genericPoint M.Z := fun u => by
    refine (Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg ξ ?_) hbot)
    rw [Subsingleton.elim u (⊥ : PrimeSpectrum (FractionRing V))]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V)))
  obtain ⟨κ, hκ⟩ := exists_factor_pt M _ hy
  have hsp : ∀ u : Sp V, (ξ ≫ f) u ⤳ f z := fun u => by
    rw [← hξ, Scheme.Hom.comp_apply]
    exact ((IsLocalRing.specializes_closedPoint (R := V) u).map ξ.continuous).map f.continuous
  have hr : Set.range (ξ ≫ f) ⊆ Set.range d := by
    rintro _ ⟨u, rfl⟩
    exact (hsp u).mem_open d.isOpenEmbedding.isOpen_range hz
  refine ⟨V, inferInstance, inferInstance, inferInstance, ξ, IsOpenImmersion.lift d (ξ ≫ f) hr, κ,
    ⟨_, hξ⟩, hκ, ?_⟩
  rw [← cancel_mono d, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, hκ, Category.assoc,
    Category.assoc, ef, ed]

end GlobalTheory.DvrTrait
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrFactorPointPadicAlgClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

theorem GlobalTheory.ValPt.exists_dvr_factor : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ y : Sp (OO p) ⟶ M.Z, ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (fV : V →+* V') (fK : FractionRing V →+* FractionRing V') (κ' : FractionRing V' →+* PadicAlgCl p) (iV : V' →+* OO p) (ξ : Sp V' ⟶ M.Z), IsLocalHom fV ∧ (∀ x, fK (algebraMap V _ x) = algebraMap V' _ (fV x)) ∧ κ'.comp fK = κ ∧ IsLocalHom iV ∧ (∀ x, (iV x : PadicAlgCl p) = κ' (algebraMap V' _ x)) ∧ spMap iV ≫ ξ = y := by
  intro o Ω _ _ _ _ M p _ V _ _ _ hc κ hV y

  haveI : CharZero (FractionRing V) := κ.charZero
  haveI : CharZero V := (algebraMap V (FractionRing V)).charZero
  set x : M.Z := y (cPt p) with hxdef
  obtain ⟨φ, hφloc, hφ, -⟩ := GlobalTheory.ValPt.exists_unique_stalk_hom M.Z x p y rfl
  obtain ⟨U, hU, hxU, hft⟩ := GlobalTheory.RatModel.exists_affineOpen_finiteType_int o Ω M x
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV
  let y₀ : Γ(M.Z, U) →+* PadicAlgCl p := (OO p).subtype.comp (φ.comp (M.Z.presheaf.germ U x hxU).hom)
  obtain ⟨W, _, _, _, hcW, _, fV, fK, κ', -, hfVloc, -, hfK, hκ', hW, hy₀⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ Γ(M.Z, U) y₀
  let j : W →+* PadicAlgCl p := κ'.comp (algebraMap W (FractionRing W))
  have hj : Function.Injective j :=
    κ'.injective.comp (IsFractionRing.injective W (FractionRing W))
  let ψ : M.Z.presheaf.stalk x →+* PadicAlgCl p := (OO p).subtype.comp φ

  have hψK : ∀ s, ψ s ∈ κ'.range := by
    intro s
    let xU : U := ⟨x, hxU⟩
    letI := M.Z.presheaf.algebra_section_stalk xU
    haveI := hU.isLocalization_stalk xU
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf xU).asIdeal.primeCompl (show M.Z.presheaf.stalk (xU : M.Z) from s)
    have hb : IsUnit (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) (b : Γ(M.Z, U))) :=
      IsLocalization.map_units _ b
    have hb' : ψ (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) (b : Γ(M.Z, U))) ≠ 0 :=
      ((hb.map φ).map (OO p).subtype).ne_zero
    have hga : ∀ c : Γ(M.Z, U), ψ (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) c) = y₀ c := fun c => rfl
    obtain ⟨ka, hka⟩ := hy₀ a
    obtain ⟨kb, hkb⟩ := hy₀ (b : Γ(M.Z, U))
    have e1 : ψ s * y₀ b = y₀ a := by
      rw [← hga, ← hga, ← map_mul, hab]
    have hb'' : y₀ b ≠ 0 := by rw [← hga]; exact hb'
    refine ⟨ka * kb⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hka, hkb, ← e1, mul_inv_cancel_right₀ hb'']
  have hψW : ∀ s, ψ s ∈ j.range := by
    intro s
    obtain ⟨k, hk⟩ := hψK s
    have hn : ‖κ' k‖ ≤ 1 := by rw [hk]; exact (mem_OO_iff _).1 (φ s).2
    obtain ⟨w, hw⟩ := (hW k).1 hn
    exact ⟨w, by rw [← hk, ← hw]; rfl⟩
  let e := RingEquiv.ofBijective j.rangeRestrict ⟨fun a b h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let φ' : M.Z.presheaf.stalk x →+* W := e.symm.toRingHom.comp (ψ.codRestrict j.range hψW)
  have hjφ' : ∀ s, j (φ' s) = ψ s := by
    intro s
    have h := e.apply_symm_apply (ψ.codRestrict j.range hψW s)
    exact congrArg Subtype.val h
  have hjO : ∀ w, j w ∈ OO p := fun w => (mem_OO_iff _).2 ((hW _).2 ⟨w, rfl⟩)
  let iV : W →+* OO p := j.codRestrict (OO p) hjO
  have hiVloc : IsLocalHom iV := by
    constructor
    intro w hw
    obtain ⟨u, hu⟩ := hw
    have hw0 : j w ≠ 0 := by
      intro h0
      have : ((u : OO p) : PadicAlgCl p) = 0 := by rw [hu]; exact h0
      exact u.ne_zero (Subtype.ext this)
    have hwne : algebraMap W (FractionRing W) w ≠ 0 := fun h => hw0 (by simp [j, h])
    have hinv : ‖κ' (algebraMap W (FractionRing W) w)⁻¹‖ ≤ 1 := by
      have h1 : ((u⁻¹ : (OO p)ˣ) : OO p) * (u : OO p) = 1 := u.inv_mul
      have h2 : ((((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p)) * j w = 1 := by
        have := congrArg (fun t : OO p => (t : PadicAlgCl p)) h1
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        rw [hu] at this; exact this
      have h3 : κ' (algebraMap W (FractionRing W) w)⁻¹ = (((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p) := by
        rw [map_inv₀]
        exact (eq_inv_of_mul_eq_one_left h2).symm
      rw [h3]; exact (mem_OO_iff _).1 (Subtype.prop _)
    obtain ⟨w', hw'⟩ := (hW _).1 hinv
    have hww : w * w' = 1 := by
      apply IsFractionRing.injective W (FractionRing W)
      rw [map_mul, hw', map_one, mul_inv_cancel₀ hwne]
    exact ⟨⟨w, w', hww, by rw [mul_comm]; exact hww⟩, rfl⟩
  have hcomp : iV.comp φ' = φ := by
    ext s
    exact hjφ' s
  refine ⟨W, inferInstance, inferInstance, inferInstance, fV, fK, κ', iV, spMap φ' ≫ M.Z.fromSpecStalk x,
    hfVloc, hfK, hκ', hiVloc, fun w => rfl, ?_⟩
  rw [← Category.assoc, ← hφ, ← hcomp]
  show (Spec.map (CommRingCat.ofHom iV) ≫ Spec.map (CommRingCat.ofHom φ')) ≫ _ = Spec.map (CommRingCat.ofHom (iV.comp φ')) ≫ _
  rw [← Spec.map_comp]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicIntegralReadingOfTrivialisationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubic_integral_reading_of_trivialisations : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ κ : D.toPre.X → (FractionRing R)ˣ, GlobalTheory.ThFam.Reads D.toPre κ ∧ (∀ a, ∃ u : Rˣ, ((κ (-a) : (FractionRing R)ˣ) : FractionRing R) = (κ a : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a a' b, ∃ u : Rˣ, ((κ (a + a' + b) * κ a * κ a' * κ b : (FractionRing R)ˣ) : FractionRing R) = ((κ (a + a') * κ (a + b) * κ (a' + b) : (FractionRing R)ˣ) : FractionRing R) * algebraMap R (FractionRing R) (u : R)) ∧ (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R (FractionRing R) s) ∧ ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R (FractionRing R) s}.Finite := by
  first | exact @GlobalTheory.ThFamRead.exists_reading | exact GlobalTheory.ThFamRead.exists_reading | (intros; apply GlobalTheory.ThFamRead.exists_reading <;> assumption)
end

