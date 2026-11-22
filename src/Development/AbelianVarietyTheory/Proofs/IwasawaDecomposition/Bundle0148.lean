import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0136
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAlgClosedOverNumberFieldCompEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

set_option autoImplicit false

namespace GlobalTheory.AlgClosedIsoOverNumberField

open Cardinal

theorem exists_ringEquiv_commutes (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  classical

  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hL : ℵ₀ < #L := hKL ▸ hK
  have hs' : #K = #s :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have ht' : #L = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hL
  obtain ⟨f⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (hs'.symm.trans (hKL.trans ht'))

  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht

  let e₀ : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R f).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e₀.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

theorem exists_ringEquiv_comp_eq :
    ∀ (K Ω₁ Ω₂ : Type) [Field K] [NumberField K] [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁]
      [IsAlgClosed Ω₂] [CharZero Ω₁] [CharZero Ω₂] (a : K →+* Ω₁) (b : K →+* Ω₂),
      Cardinal.mk Ω₁ = Cardinal.mk Ω₂ → Cardinal.aleph0 < Cardinal.mk Ω₁ →
        ∃ ι : Ω₁ ≃+* Ω₂, ∀ x, ι (a x) = b x := by
  intro K Ω₁ Ω₂ _ _ _ _ _ _ _ _ a b hcard hbig
  let : Algebra K Ω₁ := a.toAlgebra
  let : Algebra K Ω₂ := b.toAlgebra

  have hK : #K ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
    rwa [Cardinal.mkRat, max_self] at this
  obtain ⟨e, he⟩ := exists_ringEquiv_commutes K Ω₁ Ω₂ hK hbig hcard
  exact ⟨e, he⟩

end GlobalTheory.AlgClosedIsoOverNumberField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetAutWdTieLabConj
section
noncomputable section

namespace GlobalTheory.HeightCounting.TrueConjLabels

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne Pointwise

section General

variable {Ω : Type} [Field Ω]

theorem val_lt_iff {A B : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ x, x ∈ A ↔ c x ∈ B) (y : Ω) :
    B.valuation (c y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← hc, ← map_inv₀, ← hc, map_eq_zero_iff _ c.injective]

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

theorem exists_transport_elt (s : E ≃+* E) (c : Ω ≃+* Ω) (hs : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (s x))
    (t : G E Ω) : ∃ γ : G E Ω, ∀ x, γ (c x) = c (t x) := by
  refine ⟨{ (c.symm.trans (t.toRingEquiv.trans c)) with commutes' := fun y => ?_ }, fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := s.surjective y
    show c (t (c.symm _)) = _
    rw [← hs, c.symm_apply_apply, t.commutes]
  · show c (t (c.symm (c x))) = _
    rw [c.symm_apply_apply]

end General

section Host

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def conjInt (H : Host R) : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem coe_conjInt (x : 𝓞 H.E) : ((conjInt H x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := rfl

theorem isConjPl_iff {w w' : PlE H} : IsConjPl H w w' ↔ ∀ x, x ∈ w.asIdeal ↔ conjInt H x ∈ w'.asIdeal := by
  refine ⟨fun h x => h x _ (coe_conjInt x), fun h x y hy => ?_⟩
  have : y = conjInt H x := RingOfIntegers.ext (hy.trans (coe_conjInt x).symm)
  rw [this]; exact h x

theorem eq_of_isConjPl {w₀ w₁ w : PlE H} (h₀ : IsConjPl H w₀ w) (h₁ : IsConjPl H w₁ w) : w₀ = w₁ := by
  apply HeightOneSpectrum.ext
  ext x
  rw [isConjPl_iff.1 h₀, isConjPl_iff.1 h₁]

theorem exists_ext (N : NData R H what₂) {w₀ w : PlE H} (h : IsConjPl H w₀ w) : ∃ c : N.Om ≃+* N.Om,
    (∀ x : H.E, c (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x)) ∧
    ∀ x, x ∈ N.plOm.1 w₀ ↔ c x ∈ N.plOm.1 w := by
  let c₀ : N.Om ≃+* N.Om := IsAlgClosure.equivOfEquiv N.Om N.Om H.conj.toRingEquiv
  have h₀ : ∀ x : H.E, c₀ (algebraMap H.E N.Om x) = algebraMap H.E N.Om (H.conj x) := fun x =>
    IsAlgClosure.equivOfEquiv_algebraMap N.Om N.Om H.conj.toRingEquiv x
  let B : ValuationSubring N.Om := (N.plOm.1 w₀).comap c₀.symm.toRingHom
  have hB : ∀ x, x ∈ N.plOm.1 w₀ ↔ c₀ x ∈ B := fun x => by
    simp [B, ValuationSubring.mem_comap]
  have hBw : IsPlaceOver (F := H.E) B w := fun y => by
    obtain ⟨x, rfl⟩ := (conjInt H).surjective y
    rw [coe_conjInt, ← h₀, val_lt_iff c₀ hB, ← isConjPl_iff.1 h]
    exact N.plOm.2 w₀ x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hBw (N.plOm.2 w)
  refine ⟨c₀.trans σ.toRingEquiv, fun x => ?_, fun x => ?_⟩
  · show σ (c₀ _) = _
    rw [h₀, σ.commutes]
  · show _ ↔ σ (c₀ x) ∈ _
    rw [hB, ← hσ, ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff.symm

end Host

theorem exists_gamma (D : D7) (k : Fin 2) : ∃ γ : PlE D.host → G D.host.E D.nd.Om,
    (∀ v, γ (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    ∀ v w, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ w (c x) = c (D.ntypes.tg k v x) := by
  have key : ∀ w : PlE D.host, ∃ γ : G D.host.E D.nd.Om, (∀ v, w = D.naut.plGw k v → γ = D.ntypes.tg k v) ∧
      ∀ v, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
      (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
      (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ ∀ x, γ (c x) = c (D.ntypes.tg k v x) := by
    intro w
    by_cases h : ∃ v, IsConjPl D.host (D.naut.plGw k v) w
    · obtain ⟨v, hv⟩ := h
      obtain ⟨c, h1, h2⟩ := exists_ext D.nd hv
      obtain ⟨γ, hγ⟩ := exists_transport_elt D.host.conj.toRingEquiv c h1 (D.ntypes.tg k v)
      refine ⟨γ, fun v' e => absurd (e ▸ hv) (D.naut.plGw_nconj k v v'), fun v' hv' => ?_⟩
      obtain rfl : v = v' := D.naut.plGw_inj k (eq_of_isConjPl hv hv')
      exact ⟨c, h1, h2, hγ⟩
    · refine ⟨Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1) w, fun v e => ?_, fun v hv => absurd ⟨v, hv⟩ h⟩
      rw [e]; exact (D.naut.plGw_inj k).extend_apply _ _ v
  choose γ h1 h2 using key
  exact ⟨γ, fun v => h1 _ v rfl, fun v w hw => h2 w v hw⟩

set_option maxHeartbeats 1000000 in

theorem exists_labels_true_conj : ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (Rw : RowWD D), ∃ lab h A C tm tg hl,
    (∀ k v, A.plGw k v = D.naut.plGw k v) ∧
    ∃ T : GlobalTheory.RowTie.WDTie (setAut D hE lab h A C tm tg hl).nd (setAut D hE lab h A C tm tg hl).naut,
      LabTrue (setAut D hE lab h A C tm tg hl) T ∧ LabConj (setAut D hE lab h A C tm tg hl) T ∧
      ∃ Rs : RowSide (setAut D hE lab h A C tm tg hl),
        (∀ σ w, T.e w (Rs.locR σ w) = Rw.par σ w) ∧ ∀ σ w, Rs.satR σ w = Rw.sat σ w := by
  intro D hE Rw
  have hS : ∀ k v, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    fun k v => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  let lab : ∀ k, D.what₂.FT → D.nd.PlG k → Polynomial (ZMod (D.host.g k)) := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (Rw.par σ (D.naut.plGw k v))
  have h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = D.R.r := fun k σ v =>
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ⟨WD.lab_monic _ _ _, ((WD.natDegree_lab_eq_iff (hS k v) _).2 (Rw.tame σ k v)).trans (Rw.dim σ _)⟩
  choose γ hγ1 hγ2 using exists_gamma D
  let A : NAut (ndLab D.nd lab h) := nAutWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj
    D.naut.plGw_nconj D.ntypes.teichC γ
  have hA : ∀ k v (a : A.LP (A.plGw k v)), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.items₂ k (A.plGw k v) a = WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) a := fun k v a => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact congrArg (fun x => WD.lab (h := D.nd.plOm.2 (D.naut.plGw k v)) (D.ntypes.teichC k) x a) (hγ1 k v)
  have hl : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod := by
    intro k v L hL
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    rw [hA k v L] at hL ⊢
    exact WD.inePol_eq_of_natDegree_lab _ _ _ hL
  obtain ⟨C⟩ := GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc _ _ _ _ A hE
  refine ⟨lab, h, A, C, D.ntypes.tg_mem, D.ntypes.tg_gen, hl, fun _ _ => rfl,
    wdTieWD (ndLab D.nd lab h) hE D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj D.ntypes.teichC γ,
    fun k v a => hA k v a, fun k v w hw => ?_, ⟨Rw.par, Rw.sat, fun k σ v => (hA k v _).symm⟩, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c, h1, h2, h3⟩ := hγ2 k v w hw
  exact ⟨c, γ k w, h1, h2, h3, fun _ => rfl⟩

end GlobalTheory.HeightCounting.TrueConjLabels

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial

theorem exists_setAut_wdTie_labConj : ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (Rw : RowWD D), ∃ lab h A C tm tg hl, (∀ k v, A.plGw k v = D.naut.plGw k v) ∧ ∃ T : GlobalTheory.RowTie.WDTie (setAut D hE lab h A C tm tg hl).nd (setAut D hE lab h A C tm tg hl).naut, LabTrue (setAut D hE lab h A C tm tg hl) T ∧ LabConj (setAut D hE lab h A C tm tg hl) T ∧ ∃ Rs : RowSide (setAut D hE lab h A C tm tg hl), (∀ σ w, T.e w (Rs.locR σ w) = Rw.par σ w) ∧ ∀ σ w, Rs.satR σ w = Rw.sat σ w :=
  TrueConjLabels.exists_labels_true_conj

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwoPrimesSameNormOfTrivialFrobenius
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

theorem card_le_of_pow_eq_self {R : Type} [CommRing R] [IsDomain R] [Finite R] {q : ℕ} (hq : 1 < q)
    (h : ∀ x : R, x ^ q = x) : Nat.card R ≤ q := by
  classical
  have := Fintype.ofFinite R
  have hd : (Polynomial.X ^ q - Polynomial.X : Polynomial R).natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq), Polynomial.natDegree_X_pow]
  have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hd
    omega
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine le_trans (Polynomial.card_le_degree_of_subset_roots ?_) hd.le
  intro x _
  rw [Polynomial.mem_roots hne]
  simp [h x]

theorem exists_two_primes_of_isFrob_one (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] (σ : F ≃ₐ[K] F) (hσ : σ ≠ 1) :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → IsFrob F v 1 →
      ∃ P Q : HeightOneSpectrum (𝓞 F), P ≠ Q ∧ P.asIdeal.LiesOver v.asIdeal ∧ Q.asIdeal.LiesOver v.asIdeal ∧
        Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal := by
  let e : 𝓞 F ≃ₐ[𝓞 K] 𝓞 F := RingOfIntegers.mapAlgEquiv σ
  obtain ⟨θ, hθ⟩ : ∃ θ : 𝓞 F, e θ - θ ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hσ
    ext x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
    have h : ∀ a : 𝓞 F, σ (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F) F a := fun a =>
      congrArg (algebraMap (𝓞 F) F) (sub_eq_zero.1 (hc a))
    simp only [map_div₀, h, AlgEquiv.one_apply]
  have hfin : {P : HeightOneSpectrum (𝓞 F) | P.asIdeal ∣ Ideal.span {e θ - θ}}.Finite :=
    Ideal.finite_factors (by simpa using hθ)
  refine ⟨{v | ∃ P : HeightOneSpectrum (𝓞 F), P.asIdeal ∣ Ideal.span {e θ - θ} ∧
    P.asIdeal.under (𝓞 K) = v.asIdeal}, ?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      ((hfin.image (fun P => P.asIdeal.under (𝓞 K))).subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨v, ⟨P, hP, hv⟩, rfl⟩
    exact ⟨P, hP, hv⟩
  rintro v hv ⟨P, hP, hPo, hx⟩
  have hvp := v.isPrime
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hfP : Finite (𝓞 F ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hfv : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Finite.one_lt_card
  have hle : Nat.card (𝓞 F ⧸ P) ≤ Nat.card (𝓞 K ⧸ v.asIdeal) := by
    have h0 : Ideal.absNorm v.asIdeal = Nat.card (𝓞 K ⧸ v.asIdeal) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [← h0]
    refine card_le_of_pow_eq_self hq fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have := hx x
    rw [one_smul] at this
    rw [← map_pow]
    exact (Ideal.Quotient.eq.2 this).symm
  have hinj : Function.Injective (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 F ⧸ P)) := FaithfulSMul.algebraMap_injective _ _
  have hbij : Function.Bijective (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 F ⧸ P)) :=
    hinj.bijective_of_nat_card_le hle
  have hN : Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_eq_of_bijective _ hbij).symm
  have hQo : (P.comap e).LiesOver v.asIdeal := inferInstance
  have hQ : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  have hQne : P.comap e ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _
  refine ⟨⟨P, hP, hne⟩, ⟨P.comap e, hQ, hQne⟩, ?_, hPo, hQo, hN, ?_⟩
  · intro h
    have h' : P = P.comap e := congrArg HeightOneSpectrum.asIdeal h
    apply hv
    refine ⟨⟨P, hP, hne⟩, ?_, hPo.over.symm⟩
    rw [Ideal.dvd_span_singleton]
    obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk P θ)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h1 : algebraMap (𝓞 K) (𝓞 F) a - θ ∈ P := Ideal.Quotient.eq.1 ha
    have h2 : e (algebraMap (𝓞 K) (𝓞 F) a - θ) ∈ P := by
      have := h' ▸ h1
      exact this
    rw [map_sub, AlgEquiv.commutes] at h2
    have := P.sub_mem h1 h2
    show e θ - θ ∈ P
    convert this using 1
    ring
  · show Ideal.absNorm (P.comap e) = _
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    refine Nat.card_congr (Ideal.quotientEquiv (P.comap e) P e.toRingEquiv ?_).toEquiv
    exact (Ideal.map_comap_of_surjective (e.toRingEquiv : 𝓞 F →+* 𝓞 F) e.surjective P).symm

end GlobalTheory.Mem.Fld
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKummerFieldOfPowerIdealRoots
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

variable {E : Type} [Field E] [NumberField E]

theorem exists_finite_units_mod_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set (𝓞 E)ˣ, S.Finite ∧ ∀ u : (𝓞 E)ˣ, ∃ s ∈ S, ∃ w : (𝓞 E)ˣ, u = s * w ^ h := by
  have : Group.FG (𝓞 E)ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  have := Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 E)ˣ h0
  have : Finite ((𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Set.range (Quotient.out : (𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range → (𝓞 E)ˣ),
    @Set.finite_range _ _ _ this, fun u => ?_⟩
  obtain ⟨⟨_, w, rfl⟩, hw⟩ := QuotientGroup.mk_out_eq_mul (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range u
  refine ⟨_, ⟨(u : (𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range), rfl⟩, w⁻¹, ?_⟩
  rw [hw]
  simp

theorem exists_finite_mod_units_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set E, S.Finite ∧ ∀ y ∈ powIdealElts E h, ∃ s ∈ S, ∃ (x : E) (u : (𝓞 E)ˣ),
      y = x ^ h * s * ((u : 𝓞 E) : E) := by
  classical
  have key : ∀ y : powIdealElts E h, ∃ 𝔞 : (FractionalIdeal (𝓞 E)⁰ E)ˣ,
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (y : E) = (𝔞 : FractionalIdeal (𝓞 E)⁰ E) ^ h := by
    rintro ⟨y, hy, 𝔞, ha⟩
    refine ⟨Units.mk0 𝔞 ?_, ha⟩
    rintro rfl
    rw [zero_pow h0, FractionalIdeal.spanSingleton_eq_zero_iff] at ha
    exact hy ha
  choose A hA using key
  let c : powIdealElts E h → ClassGroup (𝓞 E) := fun y => ClassGroup.mk E (A y)
  let r : Set.range c → E := fun t => (t.2.choose : E)
  refine ⟨Set.range r, Set.finite_range _, fun y hy => ⟨_, ⟨⟨c ⟨y, hy⟩, _, rfl⟩, rfl⟩, ?_⟩⟩
  have ht : c ⟨y, hy⟩ ∈ Set.range c := ⟨_, rfl⟩
  have h1 : c ht.choose = c ⟨y, hy⟩ := ht.choose_spec
  change ∃ (x : E) (u : (𝓞 E)ˣ), y = x ^ h * (ht.choose : E) * ((u : 𝓞 E) : E)
  generalize ht.choose = s at h1
  have h2 : ClassGroup.mk E (A ⟨y, hy⟩ * (A s)⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact h1.symm
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h2)
  have h3 : ((A ⟨y, hy⟩ : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ x * A s := by
    rw [← hx, ← Units.val_mul, inv_mul_cancel_right]
  have h4 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x ^ h * s) = FractionalIdeal.spanSingleton (𝓞 E)⁰ y := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow, hA s, ← mul_pow,
      ← h3]
    exact (hA ⟨y, hy⟩).symm
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h4
  refine ⟨x, u, ?_⟩
  rw [← hu, Units.smul_def, Algebra.smul_def, mul_comm]

theorem exists_finite_mod_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set E, S.Finite ∧ ∀ y ∈ powIdealElts E h, ∃ s ∈ S, ∃ x : E, y = x ^ h * s := by
  obtain ⟨S, hS, H⟩ := exists_finite_mod_units_pow (E := E) h0
  obtain ⟨T, hT, H'⟩ := exists_finite_units_mod_pow (E := E) h0
  refine ⟨Set.image2 (fun s (t : (𝓞 E)ˣ) => s * ((t : 𝓞 E) : E)) S T, hS.image2 _ hT, fun y hy => ?_⟩
  obtain ⟨s, hs, x, u, rfl⟩ := H y hy
  obtain ⟨t, ht, w, rfl⟩ := H' u
  refine ⟨_, ⟨s, hs, t, ht, rfl⟩, x * ((w : 𝓞 E) : E), ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, RingOfIntegers.coe_eq_algebraMap]
  ring

theorem finiteDimensional_kummerField (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ) (h0 : h ≠ 0) :
    FiniteDimensional ℚ (kummerField φ h) := by
  obtain ⟨S, hS, H⟩ := exists_finite_mod_pow (E := E) h0
  let R : Set ℂ := ⋃ s ∈ insert 1 S, {z | z ^ h = φ s}
  have hR : R.Finite := (hS.insert 1).biUnion fun s _ =>
    ((Polynomial.nthRoots h (φ s)).finite_toSet).subset fun z hz =>
      (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero h0)).2 hz
  have : Finite R := hR
  have h1 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ R) := by
    refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
    obtain ⟨s, -, hs⟩ := Set.mem_iUnion₂.1 hz
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero h0) ?_
    rw [show z ^ h = φ s from hs]
    exact (Algebra.IsIntegral.isIntegral s).map φ.toRatAlgHom
  have h2 : FiniteDimensional ℚ (imField φ) :=
    (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv.finiteDimensional
  have h3 : FiniteDimensional ℚ (imField φ ⊔ IntermediateField.adjoin ℚ R : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_sup _ _
  have hE : ∀ x, φ x ∈ imField φ ⊔ IntermediateField.adjoin ℚ R := fun x =>
    (le_sup_left : imField φ ≤ _) ⟨x, rfl⟩
  have hz : ∀ s ∈ insert 1 S, ∀ z : ℂ, z ^ h = φ s → z ∈ imField φ ⊔ IntermediateField.adjoin ℚ R :=
    fun s hs z hz => (le_sup_right : IntermediateField.adjoin ℚ R ≤ _)
      (IntermediateField.subset_adjoin ℚ R (Set.mem_iUnion₂.2 ⟨s, hs, hz⟩))
  have hle : kummerField φ h ≤ imField φ ⊔ IntermediateField.adjoin ℚ R := by
    refine (kummerField_le_iff φ).2 ⟨hE, hz 1 (Set.mem_insert _ _) _ ?_, fun y hy z hzy => ?_⟩
    · rw [map_one]
      exact (Complex.isPrimitiveRoot_exp h h0).pow_eq_one
    · obtain ⟨s, hs, x, rfl⟩ := H y hy
      have hx : φ x ≠ 0 := by
        rw [map_ne_zero]
        rintro rfl
        exact hy.1 (by rw [zero_pow h0, zero_mul])
      have h4 := hz s (Set.mem_insert_of_mem _ hs) (z / φ x) (by
        rw [div_pow, hzy, map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hx)])
      simpa [hx] using mul_mem h4 (hE x)
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

end GlobalTheory.Mem.FieldsEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMulInv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open GlobalTheory.DualPairCheck
open scoped TensorProduct

namespace GlobalTheory.OrientedAdjoint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

theorem gram_mul_inv (V : HSp D) : V.gram.map (incA D) * V.gram⁻¹.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gram_conj (V : HSp D) : ((V.gram.map (incA D)).map (cA D))ᵀ = V.gram.map (incA D) := by
  ext i j
  exact (cA_incA _).trans (congrArg (incA D) (gram_star V j i))

section Generic
variable {A : Type} [CommRing A] {m n : ℕ}

theorem inv_conj (σ : A →+* A) (P Pi : Matrix (Fin n) (Fin n) A) (h : P * Pi = 1) (hP : (P.map σ)ᵀ = P) :
    (Pi.map σ)ᵀ = Pi := by
  have h' : Pi * P = 1 := mul_eq_one_comm.1 h
  have h2 : P * (Pi.map σ)ᵀ = 1 := by
    rw [← hP, ← Matrix.transpose_mul, ← Matrix.map_mul, h',
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  calc _ = (Pi * P) * (Pi.map σ)ᵀ := by rw [h', Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]

end Generic

end GlobalTheory.OrientedAdjoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawNormClassSumFockStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lawNorm_classSum_fock : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h [Fintype S.Cl], S.LawNorm emb σ lam h := by
  first | exact @GlobalTheory.Mem.Col2.GStep.lawNorm | exact GlobalTheory.Mem.Col2.GStep.lawNorm | (intros; apply GlobalTheory.Mem.Col2.GStep.lawNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalDilatedClassStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFunctional_dilated_class : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → ∀ P a c, ∃ e : A.lv P (S.cl c.1 (A.diaPt P a c)) ≃ₗ[Res P.1] A.lv P c, ∀ x, A.fv P (S.cl c.1 (A.diaPt P a c)) x = (a : Res P.1) * A.fv P c (e x) := by
  first | exact @GlobalTheory.Mem.Col2.DilFv.dil_fv | exact GlobalTheory.Mem.Col2.DilFv.dil_fv | (intros; apply GlobalTheory.Mem.Col2.DilFv.dil_fv <;> assumption)
end

