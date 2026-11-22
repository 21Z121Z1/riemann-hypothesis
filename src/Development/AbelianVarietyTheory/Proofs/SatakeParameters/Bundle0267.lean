import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ColSpanMap
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.Bundle0063
import Formalism.LocalToGlobal.Columns.Bundle0064
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowNormOneIdeleEqPrincipalMulIntegralUnit
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section
namespace GlobalTheory.TwV.Xc.ClsPow

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_eq_diag_mul (y : (FiniteAdeleRing (𝓞 E) E)ˣ) :
    ∃ (k : Eˣ) (u : (FiniteAdeleRing (𝓞 E) E)ˣ),
      (∀ P : HeightOneSpectrum (𝓞 E), Valued.v ((u : FiniteAdeleRing (𝓞 E) E) P) = 1) ∧
      y ^ Fintype.card (ClassGroup (𝓞 E)) = Units.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)).toMonoidHom k * u := by
  classical
  let a : Neutral.B1.Ideles E := ⟨((1 : InfiniteAdeleRing E), (y : FiniteAdeleRing (𝓞 E) E)),
    ((1 : InfiniteAdeleRing E), ((y⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)),
    Prod.ext (mul_one _) y.mul_inv, Prod.ext (mul_one _) y.inv_mul⟩
  have hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf E (a ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨k, u, hu, he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff E _).1 hc
  refine ⟨k, ⟨(u : AdeleRing (𝓞 E) E).2, ((u⁻¹ : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2, ?_, ?_⟩, fun P => (hu.2 P).1, ?_⟩
  · exact congrArg Prod.snd u.mul_inv
  · exact congrArg Prod.snd u.inv_mul
  · apply Units.ext
    have h2 : ((a ^ Fintype.card (ClassGroup (𝓞 E)) : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 =
        ((Neutral.B1.diagUnits E k * u : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 := by rw [he]
    have h3 : ∀ (t : Neutral.B1.Ideles E) (n : ℕ), ((t ^ n : Neutral.B1.Ideles E) : AdeleRing (𝓞 E) E).2 = ((t : AdeleRing (𝓞 E) E).2) ^ n := by
      intro t n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl
    rw [h3] at h2
    rw [Units.val_pow_eq_pow_val]
    exact h2.trans rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_pow_eq_ratId_mul (x : (AfE F E)ˣ) :
    ∃ (a : Eˣ) (k : (AfE F E)ˣ), k ∈ intU F E ∧ x ^ Fintype.card (ClassGroup (𝓞 E)) = ratId F E a * k := by
  obtain ⟨ι, h1, h2⟩ := GlobalTheory.TwU.exists_isAdIso F E
  obtain ⟨a, u, hu, he⟩ := exists_pow_eq_diag_mul (Units.map ι.toRingHom.toMonoidHom x)
  have hinv : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) P) = 1 := by
    intro P
    have e : (((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) P) * ((u : FiniteAdeleRing (𝓞 E) E) P) = 1 := by
      exact congrArg (fun t : FiniteAdeleRing (𝓞 E) E => t P) (Units.inv_mul u)
    have e2 := congrArg Valued.v e
    rw [map_mul, hu P, mul_one, map_one] at e2
    exact e2
  refine ⟨a, Units.map ι.symm.toRingHom.toMonoidHom u, ?_, ?_⟩
  · rw [intU, Submonoid.mem_units_iff]
    constructor
    · show ι.symm (u : FiniteAdeleRing (𝓞 E) E) ∈ RInt F E
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hu P]
    · show ι.symm ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ RInt F E
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hinv P]
  · apply Units.ext
    apply ι.injective
    have e := congrArg (fun t : (FiniteAdeleRing (𝓞 E) E)ˣ => (t : FiniteAdeleRing (𝓞 E) E)) he
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at e
    rw [Units.val_pow_eq_pow_val, map_pow, e, Units.val_mul, map_mul]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply]
    congr 1
    rw [ratId, Units.coe_map]
    show _ = ι (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (a : E))
    rw [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, h1]

theorem conjId_ratId (σ : E →ₐ[F] E) (a : Eˣ) :
    conjId σ (ratId F E a) = ratId F E (Units.map (σ : E →+* E).toMonoidHom a) := by
  apply Units.ext
  simp [conjId, ratId, sigR, inclE]

theorem sigR_mem_RInt (σ : E →ₐ[F] E) {y : AfE F E} (hy : y ∈ RInt F E) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) y ∈ RInt F E := by
  have hle : RInt F E ≤ (RInt F E).comap (sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    refine (Subring.closure_le).2 ?_
    rintro g (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨c, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨⟨σ (algebraMap (𝓞 E) E b), ⟨RingOfIntegers.mapRingHom (σ : E →+* E) b, ?_⟩⟩, ?_⟩)
      · rfl
      · simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨c, ?_⟩)
      simp [sigR]
  exact hle hy

theorem conjId_mem_intU (σ : E →ₐ[F] E) {k : (AfE F E)ˣ} (hk : k ∈ intU F E) : conjId σ k ∈ intU F E := by
  rw [intU, Submonoid.mem_units_iff] at hk ⊢
  refine ⟨sigR_mem_RInt σ hk.1, ?_⟩
  rw [← map_inv]
  exact sigR_mem_RInt σ hk.2

theorem conjId_conjId (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (k : (AfE F E)ˣ) : conjId σ (conjId σ k) = k := by
  apply Units.ext
  show sigR σ (FiniteAdeleRing (𝓞 F) F) (sigR σ (FiniteAdeleRing (𝓞 F) F) (k : AfE F E)) = k
  induction (k : AfE F E) using TensorProduct.induction_on with
  | zero => simp
  | tmul e c => simp [sigR, hσ]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

theorem normOne_idele_pow_eq_normOne_principal_mul_unit (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (x : (AfE F E)ˣ) (hx : x ∈ U1 σ) :
    ∃ (m : ℕ) (z : Eˣ) (k : (AfE F E)ˣ), 0 < m ∧ (z : E) * σ (z : E) = 1 ∧ k ∈ U1 σ ∧ k ∈ intU F E ∧
      x ^ m = ratId F E z * k := by
  classical
  obtain ⟨a, k₀, hk₀, he⟩ := exists_pow_eq_ratId_mul (F := F) x
  set h := Fintype.card (ClassGroup (𝓞 E))
  have hx' : x * conjId σ x = 1 := by
    rw [U1, MonoidHom.mem_ker] at hx
    exact hx
  have hw : x ^ h * conjId σ (x ^ h) = 1 := by rw [map_pow, ← mul_pow, hx', one_pow]
  have hw' : x ^ h = (conjId σ (x ^ h))⁻¹ := eq_inv_of_mul_eq_one_left hw
  let sa : Eˣ := Units.map (σ : E →+* E).toMonoidHom a
  refine ⟨2 * h, a * sa⁻¹, k₀ * (conjId σ k₀)⁻¹, Nat.mul_pos two_pos Fintype.card_pos, ?_, ?_, ?_, ?_⟩
  · have ha : (a : E) ≠ 0 := a.ne_zero
    have hsa : σ (a : E) ≠ 0 := by
      intro h0
      apply ha
      rw [← hσ (a : E), h0, map_zero]
    simp only [sa, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      AlgHom.coe_toRingHom, RingHom.coe_coe, map_mul, map_inv₀, hσ]
    field_simp
  · rw [U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply, map_mul, map_inv, conjId_conjId σ hσ]
    rw [mul_assoc, inv_mul_cancel_left, mul_inv_cancel]
  · exact mul_mem hk₀ (inv_mem (conjId_mem_intU σ hk₀))
  · have hc : conjId σ (x ^ h) = ratId F E sa * conjId σ k₀ := by rw [he, map_mul, conjId_ratId]
    rw [mul_comm 2 h, pow_mul, sq]
    calc x ^ h * x ^ h = x ^ h * (conjId σ (x ^ h))⁻¹ := by rw [← hw']
      _ = ratId F E (a * sa⁻¹) * (k₀ * (conjId σ k₀)⁻¹) := by
        rw [hc, he, map_mul, map_inv, mul_inv]
        ac_rfl

theorem _root_.GlobalTheory.TwV.Xc.exists_pow_normOne_idele_eq_principal_mul_integralUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ x ∈ U1 σ, ∃ (m : ℕ) (z : Eˣ) (k : (AfE F E)ˣ), 0 < m ∧ (z : E) * σ (z : E) = 1 ∧ k ∈ U1 σ ∧ k ∈ intU F E ∧ x ^ m = ratId F E z * k :=
  fun _ _ _ _ _ _ _ σ hσ x hx => normOne_idele_pow_eq_normOne_principal_mul_unit σ hσ x hx

end GlobalTheory.TwV.Xc.ClsPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrimeUnderFirstFactorAtPlaceOverP
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F)
    (ha : a ∈ v.adicCompletionIntegers F) (c : v.adicCompletion F) (hc0 : c ≠ 0) (hc : Valued.v c ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (a - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) ≤ Valued.v c := by
  have hopen : IsOpen {x : v.adicCompletion F |
      (x - a) * c⁻¹ ∈ (Valued.v.valuationSubring : ValuationSubring (v.adicCompletion F))} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage
      ((continuous_sub_right _).mul continuous_const)
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap (K := F)).exists_mem_open hopen ⟨a, by simp⟩
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  have hy' : Valued.v (algebraMap F (v.adicCompletion F) y - a) ≤ Valued.v c := by
    have h1 : Valued.v ((algebraMap F (v.adicCompletion F) y - a) * c⁻¹) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff _ _).1 hy
    rw [map_mul, map_inv₀] at h1
    have h2 := mul_le_mul' h1 (le_refl (Valued.v c))
    rwa [mul_assoc, inv_mul_cancel₀ hvc, mul_one, one_mul] at h2
  have ha1 : Valued.v a ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ha
  have e2 : ∀ z : F, Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z := fun z =>
    v.valuedAdicCompletion_eq_valuation' z
  have hy1 : v.valuation F y ≤ 1 := by
    rw [← e2]
    have e : algebraMap F (v.adicCompletion F) y = (algebraMap F (v.adicCompletion F) y - a) + a := by ring
    rw [e]
    exact Valuation.map_add_le _ (hy'.trans hc) ha1
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer hy1 (Units.mk0 (Valued.v c) hvc)
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) - algebraMap F (v.adicCompletion F) y) ≤ Valued.v c := by
    rw [← map_sub, e2]
    exact hr.le
  have e : a - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) =
      -(algebraMap F (v.adicCompletion F) y - a) - (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) - algebraMap F (v.adicCompletion F) y) := by ring
  rw [e]
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ hr')
  rw [Valuation.map_neg]; exact hy'

end GlobalTheory.TwV.Xc.PrimeAt

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

theorem iw_algebraMap (A : LocAt F E n G) (hA : SplAlg A) (v : Fin G.P.nV) (f : F) :
    A.iw v (algebraMap F E f) = (A.eQ v).symm (algebraMap F ((A.pl v).1.adicCompletion F) f) := by
  have h1 : inclE (F := F) ((A.pl v).1.adicCompletion F) (algebraMap F E f) =
      (1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f := by
    change algebraMap F E f ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F) = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  simp only [LocAt.iw, LocAt.phE, LocAt.ph, RingHom.comp_apply, h1]
  rw [show (A.spl v).toRingHom ((1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f) =
    A.spl v ((1 : E) ⊗ₜ[F] algebraMap F ((A.pl v).1.adicCompletion F) f) from rfl, hA v]
  rfl

theorem iw_int (A : LocAt F E n G) (v : Fin G.P.nV) (x : 𝓞 E) :
    A.iw v (x : E) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
  haveI := (G.P.setting v).frac_alt
  have h1 : IsIntegral ℤ (A.iw v (x : E)) := x.2.map (A.iw v).toIntAlgHom
  have h2 : IsIntegral (G.P.W v) (A.iw v (x : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

end GlobalTheory.TwV.Xc.PrimeAt

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

def toW (A : LocAt F E n G) (v : Fin G.P.nV) : 𝓞 E →+* G.P.W v :=
  haveI := (G.P.setting v).frac_alt
  (RingEquiv.ofBijective (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective (G.P.W v) (G.P.Qq v) (congrArg Subtype.val h),
        (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict_surjective⟩).symm.toRingHom.comp
    (((A.iw v).comp (algebraMap (𝓞 E) E)).codRestrict _ (fun x => iw_int A v x))

theorem toW_spec (A : LocAt F E n G) (v : Fin G.P.nV) (x : 𝓞 E) :
    algebraMap (G.P.W v) (G.P.Qq v) (toW A v x) = A.iw v (x : E) := by
  haveI := (G.P.setting v).frac_alt
  set e := RingEquiv.ofBijective (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective (G.P.W v) (G.P.Qq v) (congrArg Subtype.val h),
        (algebraMap (G.P.W v) (G.P.Qq v)).rangeRestrict_surjective⟩ with he
  have h : (e (toW A v x) : G.P.Qq v) = A.iw v (x : E) := by
    simp only [toW, he, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply, RingHom.codRestrict_apply]
  rw [← h]
  rfl

end GlobalTheory.TwV.Xc.PrimeAt

namespace GlobalTheory.TwV.Xc.PrimeAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

theorem p_irr (v : Fin G.P.nV) : Irreducible ((p : ℕ) : G.P.W v) := (G.P.setting v).p_unif

def primeAt (A : LocAt F E n G) (v : Fin G.P.nV) : HeightOneSpectrum (𝓞 E) where
  asIdeal := Ideal.comap (toW A v) (Ideal.span {((p : ℕ) : G.P.W v)})
  isPrime := by
    haveI : (Ideal.span {((p : ℕ) : G.P.W v)}).IsPrime :=
      (Ideal.span_singleton_prime (p_irr (G := G) v).ne_zero).2 (p_irr (G := G) v).prime
    exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hm : ((p : ℕ) : 𝓞 E) ∈ Ideal.comap (toW A v) (Ideal.span {((p : ℕ) : G.P.W v)}) := by
      rw [Ideal.mem_comap, map_natCast]; exact Ideal.mem_span_singleton_self _
    rw [h, Ideal.mem_bot] at hm
    have hp0 : ((p : ℕ) : G.P.W v) = 0 := by
      have := congrArg (toW A v) hm; rwa [map_natCast, map_zero] at this
    exact (p_irr (G := G) v).ne_zero hp0

theorem mem_primeAt (A : LocAt F E n G) (v : Fin G.P.nV) (x : 𝓞 E) :
    x ∈ (primeAt A v).asIdeal ↔ ((p : ℕ) : G.P.W v) ∣ toW A v x := by
  change x ∈ Ideal.comap (toW A v) _ ↔ _
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]

theorem exists_primeOf_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n p : ℕ)
    [Fact p.Prime] (G : GAtP p) (A : LocAt F E n G), LocInt A → SplAlg A → ∀ v, ∃ P : HeightOneSpectrum (𝓞 E),
    PrimeOf p (G.P.W v) (A.iw v) P ∧
    (∀ (y : G.P.W v) (k : ℕ), ∃ (x : 𝓞 E) (z : G.P.W v), A.iw v x = algebraMap _ _ (y + (p : G.P.W v) ^ k * z)) ∧
    ((p : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  intro F E _ _ _ _ _ n p _ G A hW hA v
  refine ⟨primeAt A v, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨toW A v x, (toW_spec A v x).symm, mem_primeAt A v x⟩
  · intro y k
    set K := (A.pl v).1.adicCompletion F
    have ha : A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) y) ∈ (A.pl v).1.adicCompletionIntegers F :=
      (hW v _).1 ⟨y, rfl⟩
    have hpK : ((p : ℕ) : K) ≠ 0 := by
      rw [← map_natCast (algebraMap F K)]
      exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    have hc0 : ((p : ℕ) : K) ^ k ≠ 0 := pow_ne_zero _ hpK
    have hp1 : Valued.v ((p : ℕ) : K) ≤ 1 := by
      have e2 : Valued.v (algebraMap F K ((p : ℕ) : F)) = (A.pl v).1.valuation F ((p : ℕ) : F) :=
        (A.pl v).1.valuedAdicCompletion_eq_valuation' _
      rw [← map_natCast (algebraMap F K), e2, ← map_natCast (algebraMap (𝓞 F) F)]
      exact (A.pl v).1.valuation_le_one _
    have hc : Valued.v (((p : ℕ) : K) ^ k) ≤ 1 := by
      rw [map_pow]; exact pow_le_one₀ zero_le' hp1
    obtain ⟨r, hr⟩ := exists_int_near (A.pl v).1 _ ha _ hc0 hc
    set a := A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) y)
    set d := a - algebraMap F K (algebraMap (𝓞 F) F r)
    have hdq : d * (((p : ℕ) : K) ^ k)⁻¹ ∈ (A.pl v).1.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
      have hv0 : Valued.v (((p : ℕ) : K) ^ k) ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
      calc Valued.v d * (Valued.v (((p : ℕ) : K) ^ k))⁻¹ ≤ Valued.v (((p : ℕ) : K) ^ k) * (Valued.v (((p : ℕ) : K) ^ k))⁻¹ :=
            mul_le_mul' hr le_rfl
        _ = 1 := mul_inv_cancel₀ hv0
    obtain ⟨z', hz'⟩ := (hW v ((A.eQ v).symm (d * (((p : ℕ) : K) ^ k)⁻¹))).2 (by rwa [RingEquiv.apply_symm_apply])
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r, -z', ?_⟩
    have hx : ((algebraMap (𝓞 F) (𝓞 E) r : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F r) := by
      change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = _
      rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    rw [hx, iw_algebraMap A hA v]
    have e1 : algebraMap F K (algebraMap (𝓞 F) F r) = a - (((p : ℕ) : K) ^ k) * (d * (((p : ℕ) : K) ^ k)⁻¹) := by
      rw [mul_comm d, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]; simp [d]
    rw [e1, map_sub, map_mul, map_pow, map_natCast, ← hz', RingEquiv.symm_apply_apply]
    simp only [map_add, map_mul, map_pow, map_natCast, map_neg]
    ring
  · rw [mem_primeAt, map_natCast]
  · intro h
    have h1 : toW A v ((p : ℕ) : 𝓞 E) ∈ Ideal.map (toW A v) ((primeAt A v).asIdeal ^ 2) := Ideal.mem_map_of_mem _ h
    rw [Ideal.map_pow, map_natCast] at h1
    have h2 : Ideal.map (toW A v) (primeAt A v).asIdeal ^ 2 ≤ (Ideal.span {((p : ℕ) : G.P.W v)}) ^ 2 :=
      Ideal.pow_right_mono (Ideal.map_comap_le) 2
    have h3 := h2 h1
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3
    have hi := p_irr (G := G) v
    obtain ⟨c, hc⟩ := h3
    have : ((p : ℕ) : G.P.W v) * (((p : ℕ) : G.P.W v) * c) = ((p : ℕ) : G.P.W v) * 1 := by rw [mul_one, ← mul_assoc, ← sq, ← hc]
    have hu := mul_left_cancel₀ hi.ne_zero this
    exact hi.not_isUnit ⟨⟨_, c, hu, by rw [mul_comm]; exact hu⟩, rfl⟩

end GlobalTheory.TwV.Xc.PrimeAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfComponentZeroUnderPrime
section
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.VanishAwayInt

theorem exists_away {F : Type} [Field F] [NumberField F] (p : Ideal (𝓞 F)) [hp : p.IsPrime] (N : 𝓞 F) (hN : N ≠ 0) :
    ∃ t : 𝓞 F, t ∉ p ∧ ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal ≠ p →
      ∃ c y : 𝓞 F, y ∉ w.asIdeal ∧ y * t = N * c := by
  classical
  have hI : Ideal.span {N} ≠ ⊥ := by simpa using hN
  have hpu : ¬ IsUnit p := by
    rw [Ideal.isUnit_iff]; exact hp.ne_top
  obtain ⟨b, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hpu hI).exists_eq_pow_mul_and_not_dvd
  have hbp : ¬ b ≤ p := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.1 hbp
  refine ⟨t, htp, fun w hw => ?_⟩
  have hpw : ¬ p ^ multiplicity p (Ideal.span {N}) ≤ w.asIdeal := by
    intro h
    rcases Nat.eq_zero_or_pos (multiplicity p (Ideal.span {N})) with h0 | hm
    · rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at h
      exact w.isPrime.ne_top h
    · have hle : p ≤ w.asIdeal := w.isPrime.le_of_pow_le h
      have hpb : p ≠ ⊥ := by
        intro h'
        apply hI
        rw [eq_bot_iff]
        calc Ideal.span {N} = p ^ multiplicity p (Ideal.span {N}) * b := hb
          _ ≤ p ^ multiplicity p (Ideal.span {N}) := Ideal.mul_le_left
          _ ≤ p := Ideal.pow_le_self hm.ne'
          _ = ⊥ := h'
      have hmax : p.IsMaximal := hp.isMaximal hpb
      exact hw (hmax.eq_of_le w.isPrime.ne_top hle).symm
  obtain ⟨y, hy, hyw⟩ := SetLike.not_le_iff_exists.1 hpw
  have hyt : y * t ∈ Ideal.span {N} := by
    rw [hb]; exact Ideal.mul_mem_mul hy htb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyt
  exact ⟨c, y, hyw, by rw [← hc, mul_comm]⟩

theorem intAtA_of_prV_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    (∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) → IntAtA (F := F) P z := by
  intro F E _ _ _ _ _ P z hz
  obtain ⟨m, hm, hmz⟩ := GlobalTheory.St.G.IntAd.exists_nat_denom (F := F) (E := E) z
  haveI : (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime := Ideal.comap_isPrime _ _
  have hm0 : (m : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  obtain ⟨t, htp, ht⟩ := exists_away (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))) (m : 𝓞 F) hm0
  refine ⟨algebraMap (𝓞 F) (𝓞 E) t, htp, ?_⟩
  have key : iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) =
      algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F t) := rfl
  apply GlobalTheory.St.G.IntAd.mem_of_local
  intro w
  by_cases hw : w.asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  · rw [map_mul, hz w hw, mul_zero]; exact zero_mem _
  · obtain ⟨c, y, hyw, hyc⟩ := ht w hw
    have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have hy0 : algebraMap (𝓞 F) F y ≠ 0 := by
      intro h0
      apply hyw
      rw [(FaithfulSMul.algebraMap_eq_zero_iff (𝓞 F) F).1 h0]
      exact zero_mem _
    set q : F := algebraMap (𝓞 F) F t / (m : F) with hqdef
    have e : iA F E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) * z =
        algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) q * ((m : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * z) := by
      rw [key, ← mul_assoc, ← map_natCast (algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) m, ← map_mul, hqdef,
        div_mul_cancel₀ _ hmF]
    rw [e, map_mul]
    refine mul_mem ?_ (Formalism.UG.P.afsplit_prV_int w _ hmz)
    have hc : prV (E := E) w (algebraMap F (E ⊗[F] FiniteAdeleRing (𝓞 F) F) q) =
        algebraMap F (E ⊗[F] w.adicCompletion F) q :=
      (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F w)).commutes q
    rw [hc, Algebra.TensorProduct.algebraMap_apply']
    have hq' : q = algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F y := by
      rw [hqdef, div_eq_div_iff hmF hy0]
      have := congrArg (algebraMap (𝓞 F) F) hyc
      rw [map_mul, map_mul, map_natCast] at this
      linear_combination this
    have hq : algebraMap F (w.adicCompletion F) q ∈ w.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q]
      rw [hq', map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      have hy1 : w.intValuation y = 1 :=
        le_antisymm (w.intValuation_le_one y) (not_lt.1 fun h => hyw ((w.intValuation_lt_one_iff_mem y).1 h))
      rw [hy1, div_one]
      exact w.intValuation_le_one c
    exact Subring.subset_closure (Or.inr ⟨⟨_, hq⟩, rfl⟩)

end GlobalTheory.VanishAwayInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLevelAwayDefiniteUnitaryLevelFromLocalLevelsStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevelAway_definiteUnitaryLevelFromLocalLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → IsLevelAway w₀ (GlobalTheory.Cong.AdaptLev.levelOf a w₀ H) := by
  first | (exact @GlobalTheory.Cong.LevAway.isLevelAway_levelOf) | (exact GlobalTheory.Cong.LevAway.isLevelAway_levelOf) | (intros; apply GlobalTheory.Cong.LevAway.isLevelAway_levelOf  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPtMoveEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem isPt_move_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad), LocGood σ J A → LocInt A → LocHyp S A → A.ActB → (∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) → ∀ (i : G.comp) (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J → ∀ κa : S.U, A.IsAway i γ κa.1 → ∀ (g g' : (∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))), (∀ v, colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) = colSpan (G.P.W v) (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) → ∀ x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F), A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∃ κ : S.U, x'.1 = GlobalTheory.TwU.ratA F (A.gamI i γ) * x.1 * κ.1 ∧ S.chi κ * S.chi κa = 1 := by
  intro F E _ _ _ _ _ σ n p G A J T f bad S hG hW hH hA hbad i γ hγ κa hκa g g' hg x x' hx hx'
  have hy := A.isPt_smul hA i g x.1 κa.1 hx γ hκa
  have hyU : GlobalTheory.TwU.ratA F (A.gamI i γ) * x.1 * κa.1⁻¹ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (ratInU _ hγ) x.2) (Subgroup.inv_mem _ ((S.U_eq κa.1).1 κa.2).1)
  obtain ⟨κ₁, e₁, hχ₁⟩ := ptOne_of (A := A) S hW hH hbad i (fun v => colSpan (G.P.W v)
      (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (fun v => (G.lev i).act v γ * g v) g' ⟨_, hyU⟩ x' (fun v => rfl) (fun v => (hg v).symm) hy hx'
  refine ⟨κa⁻¹ * κ₁, ?_, ?_⟩
  · rw [e₁]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  · rw [map_mul, map_inv]
    apply Units.ext
    simp [hχ₁]

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepKernelData_integral_awayFromLevels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt := by
  first | exact @GlobalTheory.TopInt.topInt | exact GlobalTheory.TopInt.topInt | (intros; apply GlobalTheory.TopInt.topInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceLeTwistedK1Statement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_congruence_le_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (r c : ℕ), 0 < c → prinCong N P c ≤ twK1H P N r c := by
  first | exact @GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 | exact GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 | (intros; apply GlobalTheory.PrincipalCongruenceLevelK1.principal_congruence_le_level_k1 <;> assumption)
end

