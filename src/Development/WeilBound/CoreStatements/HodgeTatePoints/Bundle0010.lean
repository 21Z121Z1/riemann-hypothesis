import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Gamdel
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gamdel

theorem mem_mulLat_iff {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {w : Ω} (hw : w ≠ 0)
    (L : AddSubgroup V) (v : V) : v ∈ mulLat w L ↔ w⁻¹ • v ∈ L := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.mulLat
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, huv⟩
    rw [← huv]
    simpa [inv_smul_smul₀ hw] using hu
  · intro h
    exact ⟨w⁻¹ • v, h, by simp [smul_inv_smul₀ hw]⟩

theorem smul_mem_stdLat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (ι : Type) {a : Ω} (ha : a ∈ R) {v : ι → Ω} (hv : v ∈ stdLat R ι) : a • v ∈ stdLat R ι := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.stdLat at hv ⊢
  rw [AddSubgroup.mem_pi] at hv ⊢
  intro j hj
  have hvj : v j ∈ R := by simpa using hv j hj
  simpa [smul_eq_mul] using R.mul_mem ha hvj

def graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V') (f : V →ₗ[Ω] V') :
    AddSubgroup (V × V') where
  carrier := {p | w • p.1 ∈ A ∧ p.2 - f p.1 ∈ B}
  zero_mem' := by
    refine ⟨by simp, by simp⟩
  add_mem' := by
    rintro p q ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · have := A.add_mem h1 h3
      simpa [smul_add] using this
    · have := B.add_mem h2 h4
      convert this using 1
      simp only [Prod.snd_add, Prod.fst_add, map_add]
      abel
  neg_mem' := by
    rintro p ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := A.neg_mem h1
      simpa [smul_neg] using this
    · have := B.neg_mem h2
      convert this using 1
      simp only [Prod.snd_neg, Prod.fst_neg, map_neg]
      abel

theorem mem_graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V') (f : V →ₗ[Ω] V') (a : V)
    (b : V') : (a, b) ∈ graphLat w A B f ↔ w • a ∈ A ∧ b - f a ∈ B := Iff.rfl

theorem smul_mem_graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V')
    (f : V →ₗ[Ω] V') (a : Ω) (hA : ∀ v ∈ A, a • v ∈ A) (hB : ∀ v ∈ B, a • v ∈ B)
    (v : V × V') (hv : v ∈ graphLat w A B f) : a • v ∈ graphLat w A B f := by
  have hv' := (PositivityTheory.HtPt.Gamdel.mem_graphLat w A B f v.1 v.2).1 hv
  refine (PositivityTheory.HtPt.Gamdel.mem_graphLat w A B f (a • v).1 (a • v).2).2 ⟨?_, ?_⟩
  · rw [Prod.smul_fst, smul_smul, mul_comm, ← smul_smul]
    exact hA _ hv'.1
  · rw [Prod.smul_snd, Prod.smul_fst, map_smul, ← smul_sub]
    exact hB _ hv'.2

theorem glue_gamdel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω), w ∈ R → w ≠ 0 → ∀ (r s n : ℕ) (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω)), (∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) → (∀ a ∈ R, ∀ v ∈ om, a • v ∈ om) → ∀ (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)), (∀ a ∈ W, i a ∈ stdLat R (Fin n)) → (∀ b ∈ stdLat R (Fin n), q b ∈ om) → (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) → (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) → (∀ c ∈ om, ∃ b ∈ stdLat R (Fin n), c - q b ∈ mulLat w om) → ∃ (Gam : AddSubgroup ((Fin r → Ω) × (Fin n → Ω))) (Del : AddSubgroup ((Fin n → Ω) × (Fin s → Ω))), (∀ a b, (a, b) ∈ Gam ↔ w • a ∈ W ∧ b - i a ∈ stdLat R (Fin n)) ∧ (∀ b c, (b, c) ∈ Del ↔ w • b ∈ stdLat R (Fin n) ∧ c - q b ∈ om) ∧ (∀ a ∈ R, (∀ v ∈ Gam, a • v ∈ Gam) ∧ ∀ v ∈ Del, a • v ∈ Del) ∧ ((∀ a, (∃ b, (a, b) ∈ Gam) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ Gam ↔ b ∈ stdLat R (Fin n)) ∧ ∀ a, (a, 0) ∈ Gam ↔ a ∈ W) ∧ ((∀ b, (∃ c, (b, c) ∈ Del) ↔ w • b ∈ stdLat R (Fin n)) ∧ (∀ c, (∃ b, (b, c) ∈ Del) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ Del ↔ c ∈ om) ∧ ∀ b, (b, 0) ∈ Del ↔ ∃ a, (a, b) ∈ Gam) := by
  intro o Ω _ _ _ R w hwR hw r s n W om hW hom i q hiW hqS hexW hexS hsurj
  have hS : ∀ a ∈ R, ∀ v ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n),
      a • v ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n) :=
    fun a ha v hv => PositivityTheory.HtPt.Gamdel.smul_mem_stdLat R (Fin n) ha hv
  have hmem := fun {V : Type} [AddCommGroup V] [Module Ω V] (L : AddSubgroup V) (x : V) =>
    PositivityTheory.HtPt.Gamdel.mem_mulLat_iff hw L x
  refine ⟨PositivityTheory.HtPt.Gamdel.graphLat w W (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) i,
    PositivityTheory.HtPt.Gamdel.graphLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) om q,
    fun a b => PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _, fun b c => PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _,
    fun a ha => ⟨PositivityTheory.HtPt.Gamdel.smul_mem_graphLat _ _ _ _ a (hW a ha) (hS a ha),
      PositivityTheory.HtPt.Gamdel.smul_mem_graphLat _ _ _ _ a (hS a ha) (hom a ha)⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨b, hb⟩
      exact ((PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).1 hb).1
    · intro ha
      refine ⟨i a, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨ha, ?_⟩⟩
      rw [sub_self]
      exact AddSubgroup.zero_mem _
  · intro b
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, smul_zero, map_zero, sub_zero]
    exact ⟨fun h => h.2, fun h => ⟨W.zero_mem, h⟩⟩
  · intro a
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : i (w • a) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) := by
        rw [hmem, map_smul, inv_smul_smul₀ hw]
        exact h2
      have h4 := hexW _ h1 h3
      rwa [hmem, inv_smul_smul₀ hw] at h4
    · intro ha
      exact ⟨hW w hwR a ha, hiW a ha⟩
  · intro b
    constructor
    · rintro ⟨c, hc⟩
      exact ((PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).1 hc).1
    · intro hb
      refine ⟨q b, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨hb, ?_⟩⟩
      rw [sub_self]
      exact AddSubgroup.zero_mem _
  · intro c
    constructor
    · rintro ⟨b, hb⟩
      rw [PositivityTheory.HtPt.Gamdel.mem_graphLat] at hb
      have h1 := hom w hwR _ hb.2
      have h2 := hqS _ hb.1
      have hc : w • c = w • (c - q b) + q (w • b) := by
        rw [map_smul, smul_sub, sub_add_cancel]
      rw [hc]
      exact om.add_mem h1 h2
    · intro hc
      obtain ⟨b0, hb0, h⟩ := hsurj _ hc
      rw [hmem, smul_sub, inv_smul_smul₀ hw] at h
      refine ⟨w⁻¹ • b0, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
      · rwa [smul_inv_smul₀ hw]
      · rwa [map_smul]
  · intro c
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, smul_zero, map_zero, sub_zero]
    exact ⟨fun h => h.2, fun h => ⟨AddSubgroup.zero_mem _, h⟩⟩
  · intro b
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : q (w • b) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w om := by
        rw [hmem, map_smul, inv_smul_smul₀ hw]
        exact h2
      obtain ⟨a0, ha0, h4⟩ := (hexS _ h1).1 h3
      rw [hmem, smul_sub, inv_smul_smul₀ hw] at h4
      refine ⟨w⁻¹ • a0, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
      · rwa [smul_inv_smul₀ hw]
      · rwa [map_smul]
    · rintro ⟨a, ha⟩
      rw [PositivityTheory.HtPt.Gamdel.mem_graphLat] at ha
      obtain ⟨h1, h2⟩ := ha
      have hwb : w • b ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n) := by
        have e : w • b = w • (b - i a) + i (w • a) := by
          rw [map_smul, smul_sub, sub_add_cancel]
        rw [e]
        exact AddSubgroup.add_mem _ (hS w hwR _ h2) (hiW _ h1)
      refine ⟨hwb, ?_⟩
      have h3 : w • b - i (w • a) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) := by
        rw [hmem, map_smul, ← smul_sub, inv_smul_smul₀ hw]
        exact h2
      have h4 := (hexS _ hwb).2 ⟨w • a, h1, h3⟩
      rwa [hmem, map_smul, inv_smul_smul₀ hw] at h4

end PositivityTheory.HtPt.Gamdel
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem dom_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  intro X Ω _ ξ X' Ω' _ ξ' i f hd p'
  obtain ⟨q, hq⟩ := p'
  have hp : genPt ξ ⤳ f q := RegAtDom.map_genPt hd ▸ hq.map f.continuous
  refine ⟨hp, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(f.stalkMap q).hom s, RegAtDom.genMap_stalkMap hd q hq hp s⟩
  · rintro _ ⟨s, rfl⟩ ⟨h0, -, t, ht⟩
    have hv := RegAtDom.genMap_stalkMap hd q hq hp s
    have hone : genMap ξ' ⟨q, hq⟩ (1 - (f.stalkMap q).hom s * t) = 0 := by
      rw [map_sub, map_mul, map_one, hv, ht, mul_inv_cancel₀ h0, sub_self]
    have hu : IsUnit ((f.stalkMap q).hom s) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((f.stalkMap q).hom s * t) with h | h
      · exact isUnit_of_mul_isUnit_left h
      · have h' := h.map (genMap ξ' ⟨q, hq⟩)
        rw [hone] at h'
        exact absurd h' not_isUnit_zero
    exact RegAtMono.unitAt_of_isUnit ξ ⟨f q, hp⟩ (isUnit_of_map_unit (f.stalkMap q).hom s hu)

theorem genfib_map : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1) (n : ℕ), unitAt ξ' p' (n : Ω') ↔ unitAt ξ ⟨f p'.1, h⟩ (n : Ω) := by
  intro X Ω _ ξ X' Ω' _ ξ' i f hd p' h n
  obtain ⟨h', hc⟩ := dom_local X Ω ξ X' Ω' ξ' i f hd p'
  have := IsCtrOf.unitAt_iff (i := i) (p := ⟨f p'.1, h⟩) (p' := p') hc (natCast_mem _ n)
  rwa [map_natCast] at this

theorem dom_comp {X X₁ X₂ : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂}
    {f : X₁ ⟶ X} {g : X₂ ⟶ X₁} {i : Ω →+* Ω₁} {k : Ω₁ →+* Ω₂} (hf : Dominates ξ₁ ξ f i)
    (hg : Dominates ξ₂ ξ₁ g k) : Dominates ξ₂ ξ (g ≫ f) (k.comp i) := by
  unfold Dominates at *
  rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem iso_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X₁ X₂ : Scheme.{0}) (Ω' : Type) [Field Ω'] (i : Ω →+* Ω') (p : Cpt ξ), (∀ (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω') ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g i → IsoAt ξ₁ f (RingHom.id Ω) p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → NormAt ξ₂ g i p₁) → NormAt ξ₂ (g ≫ f) i p) ∧ (∀ (ξ₁ : Spec (CommRingCat.of Ω') ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω') ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g (RingHom.id Ω') → NormAt ξ₁ f i p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → IsoAt ξ₂ g (RingHom.id Ω') p₁) → NormAt ξ₂ (g ≫ f) i p) ∧ (∀ (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g (RingHom.id Ω) → IsoAt ξ₁ f (RingHom.id Ω) p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → IsoAt ξ₂ g (RingHom.id Ω) p₁) → IsoAt ξ₂ (g ≫ f) (RingHom.id Ω) p) := by
  intro X Ω _ ξ X₁ X₂ Ω' _ i p
  refine ⟨fun ξ₁ ξ₂ f g hg hf hn => ?_, fun ξ₁ ξ₂ f g hg hf hn => ?_, fun ξ₁ ξ₂ f g hg hf hn => ?_⟩
  · have hr : ∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → regAt ξ p = regAt ξ₁ p₁ := fun p₁ h => by
      rw [hf.regAt_eq p₁ h, Subring.map_id]
    refine ⟨fun q hq => ?_, ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.comp_id] at h⟩
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ i g hg q
      rw [hr ⟨_, h⟩ hq]
      exact (hn ⟨_, h⟩ hq).exists_max q rfl
    · obtain ⟨p₁, h₁, hu⟩ := hf.existsUnique
      rw [hr p₁ h₁]
      intro P hP
      obtain ⟨q, ⟨hq, hq'⟩, hqu⟩ := (hn p₁ h₁).existsUnique P hP
      refine ⟨q, ⟨(congrArg f hq).trans h₁, hq'⟩, fun q' hq'' => hqu q' ⟨?_, hq''.2⟩⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ i g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ hq''.1)
  · have hr : ∀ (q : Cpt ξ₂) (p₁ : Cpt ξ₁), g q.1 = p₁.1 → f p₁.1 = p.1 → regAt ξ₂ q = regAt ξ₁ p₁ :=
      fun q p₁ h h' => by rw [(hn p₁ h').regAt_eq q h, Subring.map_id]
    refine ⟨fun q hq => ?_, fun P hP => ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.id_comp] at h⟩
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q
      rw [hr q ⟨_, h⟩ rfl hq]
      exact hf.exists_max ⟨_, h⟩ hq
    · obtain ⟨p₁, ⟨h₁, h₁'⟩, hu⟩ := hf.existsUnique P hP
      obtain ⟨q, hq, hqu⟩ := (hn p₁ h₁).existsUnique
      refine ⟨q, ⟨(congrArg f hq).trans h₁, (hr q p₁ hq h₁).trans h₁'⟩, fun q' hq' => hqu q' ?_⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ ⟨hq'.1, (hr q' ⟨_, h⟩ rfl hq'.1).symm.trans hq'.2⟩)
  · refine ⟨?_, fun q hq => ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.comp_id] at h⟩
    · obtain ⟨p₁, h₁, hu⟩ := hf.existsUnique
      obtain ⟨q, hq, hqu⟩ := (hn p₁ h₁).existsUnique
      refine ⟨q, (congrArg f hq).trans h₁, fun q' hq' => hqu q' ?_⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ hq')
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q
      rw [(hn ⟨_, h⟩ hq).regAt_eq q rfl, Subring.map_id, hf.regAt_eq ⟨_, h⟩ hq]

theorem norm_iso : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (p : Cpt ξ), NormAt ξ' f (RingHom.id Ω) p → (∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) → IsoAt ξ' f (RingHom.id Ω) p := by
  intro X Ω _ ξ X' ξ' f p hN hp
  have e : (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring = regAt ξ p := by
    rw [Subring.map_id]
    ext a
    exact ⟨hp a, fun ha => isIntegral_algebraMap (x := (⟨a, ha⟩ : regAt ξ p))⟩
  haveI loc : IsLocalRing (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := by
    rw [e]
    exact NormAt.isLocalRing_regAt p
  have hr : ∀ q : Cpt ξ', f q.1 = p.1 →
      regAt ξ' q = (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := fun q hq => by
    obtain ⟨P, hP, h⟩ := hN.exists_max q hq
    exact h.trans (NormAt.ofPrime_of_isLocalRing _ P hP)
  refine ⟨?_, fun q hq => ?_, hN.dom⟩
  · obtain ⟨q, hq, hu⟩ := hN.existsUnique _ (IsLocalRing.maximalIdeal.isMaximal _)
    exact ⟨q, hq.1, fun q' hq' => hu q' ⟨hq', (hr q' hq').trans
      (NormAt.ofPrime_of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _)).symm⟩⟩
  · rw [hr q hq, e, Subring.map_id]

end PositivityTheory.HtPt.Mb
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Gsplit
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gsplit

theorem coprime_different (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr E) :
    IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨a, b, hab⟩ := (hpz.irreducible.coprime_iff_not_dvd).mpr hd
  rw [Ideal.isCoprime_iff_exists]
  refine ⟨(a : 𝓞 E) * p, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),
    (b : 𝓞 E) * (NumberField.discr E : 𝓞 E),
    Ideal.mul_mem_left _ _ (NumberField.discr_mem_differentIdeal E (𝓞 E)), ?_⟩
  have := congrArg (Int.cast : ℤ → 𝓞 E) hab
  push_cast at this
  exact this

theorem not_sq_dvd (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr E) (w : Ideal (𝓞 E)) (hw : w ≠ ⊤) :
    ¬ w ^ 2 ∣ Ideal.span {(p : 𝓞 E)} := by
  intro h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpz.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hdiff : w ^ (2 - 1) ∣ differentIdeal ℤ (𝓞 E) :=
    pow_sub_one_dvd_differentIdeal ℤ w 2 hne (by rw [hmap]; exact h)
  rw [show 2 - 1 = 1 from rfl, pow_one] at hdiff
  have hspan : w ∣ Ideal.span {(p : 𝓞 E)} := (dvd_pow_self w two_ne_zero).trans h
  exact hw (Ideal.isUnit_iff.mp
    ((PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd).isUnit_of_dvd' hspan hdiff))

theorem glue_split : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (w : Ideal (𝓞 E)) [w.IsPrime], (p : 𝓞 E) ∈ w → ∃ ε : 𝓞 E, ε - 1 ∈ w ∧ (∀ w' : Ideal (𝓞 E), w'.IsPrime → (p : 𝓞 E) ∈ w' → w' ≠ w → ε ∈ w') ∧ (∀ a : 𝓞 E, (p : 𝓞 E) ∣ ε * a ↔ a ∈ w) ∧ (p : 𝓞 E) ∣ ε * ε - ε ∧ IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) := by
  intro E hEf hEn p hp hd w hw hpw
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hwtop : w ≠ ⊤ := hw.ne_top
  have hwbot : w ≠ ⊥ := fun h => hp0 (by rw [h] at hpw; exact Ideal.mem_bot.mp hpw)
  have hmax : w.IsMaximal := hw.isMaximal hwbot
  obtain ⟨J, hJ⟩ : w ∣ Ideal.span {(p : 𝓞 E)} := Ideal.dvd_span_singleton.mpr hpw
  have hJw : ¬ J ≤ w := by
    intro hle
    apply PositivityTheory.HtPt.Gsplit.not_sq_dvd E p hp hd w hwtop
    rw [hJ, pow_two]
    exact mul_dvd_mul_left w (Ideal.dvd_iff_le.mpr hle)
  have hsup : w ⊔ J = ⊤ := by
    by_contra hne
    apply hJw
    have heq : w ⊔ J = w := by
      by_contra h'
      exact hne (hmax.out.2 _ (lt_of_le_of_ne le_sup_left (Ne.symm h')))
    exact le_sup_right.trans heq.le
  have h1 : (1 : 𝓞 E) ∈ w ⊔ J := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨x, hx, ε, hε, hxε⟩ := Submodule.mem_sup.mp h1
  have hε1 : ε - 1 ∈ w := by
    have heq : ε - 1 = -x := by
      rw [← hxε]
      ring
    rw [heq]
    exact w.neg_mem hx
  have hεw : ε ∉ w := fun h => hwtop ((Ideal.eq_top_iff_one w).mpr (by
    have h2 := w.sub_mem h hε1
    simpa using h2))
  have hmemI : ∀ b, (p : 𝓞 E) ∣ b ↔ b ∈ w * J := by
    intro b
    rw [← Ideal.mem_span_singleton, hJ]
  refine ⟨ε, hε1, ?_, ?_, ?_, PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd⟩
  · intro w' hw' hpw' hne
    have hle : w * J ≤ w' := by
      rw [← hJ, Ideal.span_singleton_le_iff_mem]
      exact hpw'
    rcases hw'.mul_le.mp hle with h | h
    · exact absurd (hmax.eq_of_le hw'.ne_top h).symm hne
    · exact h hε
  · intro a
    rw [hmemI]
    constructor
    · intro h
      have hle' : w * J ≤ w := Ideal.mul_le_left
      have hw1 : ε * a ∈ w := hle' h
      rcases hw.mem_or_mem hw1 with h' | h'
      · exact absurd h' hεw
      · exact h'
    · intro ha
      rw [mul_comm ε a]
      exact Ideal.mul_mem_mul ha hε
  · rw [hmemI]
    have heq : ε * ε - ε = (ε - 1) * ε := by ring
    rw [heq]
    exact Ideal.mul_mem_mul hε1 hε

end PositivityTheory.HtPt.Gsplit
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcTors
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

section
variable {S Y : Scheme.{0}} {G : Over S} [GrpObj G]

theorem pow_congr {a b : Y ⟶ S} (h : a = b) (g : Over.mk a ⟶ G) (g' : Over.mk b ⟶ G) (e : g.left = g'.left) (N : ℕ) :
    g ^ N = 1 ↔ g' ^ N = 1 := by
  subst h
  rw [Over.OverMorphism.ext e]

theorem mul_congr {a b : Y ⟶ S} (h : a = b) (g k : Over.mk a ⟶ G) (g' k' : Over.mk b ⟶ G) (e : g.left = g'.left)
    (e' : k.left = k'.left) : (g * k).left = (g' * k').left := by
  subst h
  rw [Over.OverMorphism.ext e, Over.OverMorphism.ext e']

theorem comp_pow_pt {A B : Over S} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) : ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
  {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

theorem tors_of_pt (h : Γ.IsTorsionAlong G x N i) (v : Y ⟶ Γ.G.left) {c : Y ⟶ S} (g : Over.mk c ⟶ G)
    (e : g.left = v ≫ i) : g ^ N = 1 := by
  have hc : c = (v ≫ Γ.G.hom) ≫ x := by
    rw [Category.assoc, ← h.isOver, ← Category.assoc, ← e]; exact (Over.w g).symm
  subst hc
  exact (h.kernel (Over.mk (v ≫ Γ.G.hom)) g).2 ⟨Over.homMk v rfl, e.symm⟩

theorem pt_of_tors (h : Γ.IsTorsionAlong G x N i) (b : Y ⟶ Spec (CommRingCat.of R)) {c : Y ⟶ S} (hc : c = b ≫ x)
    (g : Over.mk c ⟶ G) (hg : g ^ N = 1) : ∃ v : Y ⟶ Γ.G.left, v ≫ Γ.G.hom = b ∧ v ≫ i = g.left := by
  subst hc
  obtain ⟨y, hy⟩ := (h.kernel (Over.mk b) g).1 hg
  exact ⟨y.left, Over.w y, hy⟩

end

theorem torsion_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsSeparated G.hom → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N i' → ∀ (B : Type) [CommRing B] (b : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R') (σ : T → (Spec (CommRingCat.of B) ⟶ G.left)), Function.Injective j → j.comp b = algebraMap R _ → j'.comp b = (algebraMap R' _).comp φ → (∀ t, σ t ≫ G.hom = Spec.map (CommRingCat.ofHom b) ≫ x) → (∀ t, Spec.map (CommRingCat.ofHom j) ≫ σ t = (Γ.pt t).left ≫ i) → (∀ t, Spec.map (CommRingCat.ofHom j') ≫ σ t = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ φ F := by
  intro R _ _ T _ _ Γ S G _ _ x N i h hsep R' _ _ φ Γ' i' h' B _ b j j' σ hj hjb hj'b hσ hσj hσj'
  let g : Over.mk (i' ≫ G.hom) ⟶ G := Over.homMk i' rfl
  obtain ⟨F, hF1, hF2⟩ := pt_of_tors h (Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (h'.isOver.trans (Category.assoc _ _ _).symm) g (tors_of_pt h' (𝟙 _) g (Category.id_comp _).symm)
  replace hF2 : F ≫ i = i' := hF2
  refine ⟨F, hF2, ?_, fun Y y z y₀ z₀ hy hz => ?_, ?_⟩
  · have hl : ∀ c : PullbackCone Γ.G.hom (Spec.map (CommRingCat.ofHom φ)), ∃ v : c.pt ⟶ Γ'.G.left,
        v ≫ F = c.fst ∧ v ≫ Γ'.G.hom = c.snd := fun c => by
      let k : Over.mk ((c.fst ≫ i) ≫ G.hom) ⟶ G := Over.homMk (c.fst ≫ i) rfl
      obtain ⟨v, h1, h2⟩ := pt_of_tors h' c.snd
        (by rw [Category.assoc, h.isOver, ← Category.assoc, c.condition, Category.assoc]) k (tors_of_pt h c.fst k rfl)
      exact ⟨v, tors_ext h (by rw [Category.assoc, hF1, ← Category.assoc, h1, c.condition])
        (by rw [Category.assoc, hF2, h2]; rfl), h1⟩
    choose l h1 h2 using hl
    exact ⟨⟨hF1⟩, ⟨PullbackCone.IsLimit.mk hF1 l h1 h2 fun c m a1 a2 => tors_ext h' (a2.trans (h2 c).symm) (by
      rw [← hF2, ← Category.assoc, ← Category.assoc, a1, h1])⟩⟩
  · have w : ∀ {y₀ : Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G},
        (y₀.left ≫ i) ≫ G.hom = (Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x := fun {y₀} => by
      rw [Category.assoc, h.isOver, ← Category.assoc, Over.w y₀]; rfl
    have w' : ∀ {y : Y ⟶ Γ'.G}, (y.left ≫ i') ≫ G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ x := fun {y} => by
      rw [Category.assoc, h'.isOver, ← Category.assoc, Over.w y]
    refine tors_ext h ?_ ?_
    · rw [Category.assoc, hF1, ← Category.assoc, Over.w (y * z)]
      exact Over.w (y₀ * z₀)
    · refine (h.mul _ y₀ z₀ (Over.homMk (y₀.left ≫ i) w) (Over.homMk (z₀.left ≫ i) w) rfl rfl).symm.trans ?_
      rw [Category.assoc, hF2]
      refine Eq.trans ?_ (h'.mul Y y z (Over.homMk (y.left ≫ i') w') (Over.homMk (z.left ≫ i') w') rfl rfl)
      refine mul_congr (Category.assoc _ _ _) _ _ _ _ ?_ ?_
      · show y₀.left ≫ i = y.left ≫ i'
        rw [hy, Category.assoc, hF2]
      · show z₀.left ≫ i = z.left ≫ i'
        rw [hz, Category.assoc, hF2]
  · have : IsDomain B := hj.isDomain j
    have : IsDominant (Spec.map (CommRingCat.ofHom j)) := ⟨by
      have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)
      exact this⟩
    have hσ' : ∀ t, ∃ v : Spec (CommRingCat.of B) ⟶ Γ.G.left,
        v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom b) ∧ v ≫ i = σ t := fun t => by
      let k : Over.mk (σ t ≫ G.hom) ⟶ G := Over.homMk (σ t) rfl
      refine pt_of_tors h _ (hσ t) k ?_
      let ψ : Over.mk (Spec.map (CommRingCat.ofHom j) ≫ σ t ≫ G.hom) ⟶ Over.mk (σ t ≫ G.hom) :=
        Over.homMk (Spec.map (CommRingCat.ofHom j)) rfl
      have h1 : ψ ≫ k ^ N = ψ ≫ 1 := by
        rw [comp_pow_pt, MonObj.comp_one]
        exact tors_of_pt h (Γ.pt t).left _ (hσj t)
      exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of B)) G.hom
        ((Over.w _).trans (Over.w _).symm) (Spec.map (CommRingCat.ofHom j)) (congrArg (·.left) h1))
    choose v h1 h2 using hσ'
    refine ⟨B, inferInstance, b, j, j', v, hj, hjb, hj'b, h1, fun t => tors_ext h ?_ ?_, fun t => tors_ext h ?_ ?_⟩
    · rw [Category.assoc, h1, Over.w, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjb]; rfl
    · rw [Category.assoc, h2, hσj]
    · rw [Category.assoc, Category.assoc, h1, hF1, ← Category.assoc, Over.w, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hj'b, CommRingCat.ofHom_comp, Spec.map_comp]; rfl
    · rw [Category.assoc, Category.assoc, h2, hF2, hσj']

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoDefs
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

structure PairHost {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
    (H : Host E) (H' : Host E') where

  ψ : 𝓞 E' →+* Matrix (Fin 2) (Fin 2) (𝓞 E)

  σ : 𝓞 E' ≃+* 𝓞 E'
  bar : ∀ a i j, ψ (H'.bar a) i j = H.bar (ψ a j i)
  w0 : ψ H'.w0 = Matrix.scalar (Fin 2) H.w0
  conj : ∀ a, ψ (σ a) * Matrix.diagonal ![1, -1] = Matrix.diagonal ![1, -1] * ψ a
  rt : σ H'.rt = H'.rt
  chars : ∀ (k : Type) [Field k] [CharZero k] (τ τ' : 𝓞 E' →+* k), τ H'.rt = τ' H'.rt →
    τ' = τ ∨ τ' = τ.comp σ.toRingHom

end PositivityTheory.HtPt.Kftwo
end
end

