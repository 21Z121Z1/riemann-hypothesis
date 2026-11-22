import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0110
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0137
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0136
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open scoped TensorProduct

namespace GlobalTheory.Mem.ReadTwist

section General

open Formalism.L2.DIV GlobalTheory.Mem.LocTriv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem afIso_finAf_apply (a : Ideles E) (P : HeightOneSpectrum (𝓞 E)) :
    afIso F E (finAf F E a : AfE F E) P = ev P (a : AdeleRing (𝓞 E) E) := by
  rw [afIso_finAf]
  rfl

theorem mem_above {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} :
    P ∈ aboveF (L := E) F v ↔ P.under (𝓞 F) = v := by
  unfold aboveF
  rw [Set.Finite.mem_toFinset]
  rfl

theorem finAf_mem_intU_iff (a : Ideles E) : finAf F E a ∈ intU F E ↔ a ∈ unitIdl E := by
  unfold intU
  rw [Submonoid.mem_units_iff, ← map_inv]
  change (finAf F E a : AfE F E) ∈ RInt F E ∧ (finAf F E a⁻¹ : AfE F E) ∈ RInt F E ↔ _
  simp only [mem_rInt_iff, afIso_finAf]
  refine ⟨fun h P => le_antisymm (h.1 P) ?_, fun h => ⟨fun P => (h P).le, fun P => ((unitIdl E).inv_mem h P).le⟩⟩
  have h1 : (a : AdeleRing (𝓞 E) E).2 P * ((a⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 P = 1 :=
    congrArg (fun z : AdeleRing (𝓞 E) E => z.2 P) a.mul_inv
  have h2 := congrArg (Valued.v : Valuation (P.adicCompletion E) _) h1
  rw [map_mul, map_one] at h2
  rw [← h2]
  exact mul_le_of_le_one_right' (h.2 P)

theorem local_mem_suppAt (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    finAf F E (localIdele E P x) ∈ suppAt E (P.under (𝓞 F)) := by
  rw [mem_suppAt_iff]
  intro Q hQ
  rw [afIso_finAf_apply]
  exact ev_local_ne (fun e => hQ (by rw [e])) x

theorem local_mem_unitIdl {P : HeightOneSpectrum (𝓞 E)} {x : (P.adicCompletion E)ˣ} (hx : IsUnitAt P x) :
    localIdele E P x ∈ unitIdl E := fun Q => by
  change Valued.v (ev Q (localIdele E P x : AdeleRing (𝓞 E) E)) = 1
  by_cases h : Q = P
  · subst h
    rw [ev_local_self]
    exact hx
  · rw [ev_local_ne h, map_one]

theorem finAf_part {v : HeightOneSpectrum (𝓞 F)} {a : Ideles E} (ha : finAf F E a ∈ suppAt E v) :
    finAf F E (part a (aboveF (L := E) F v)) = finAf F E a := by
  refine Units.ext ((afIso F E).injective (FiniteAdeleRing.ext _ fun P => ?_))
  rw [afIso_finAf_apply]
  by_cases h : P ∈ aboveF (L := E) F v
  · rw [ev_part_mem a h, afIso_finAf_apply]
  · rw [ev_part_not_mem a h]
    exact ((mem_suppAt_iff F E v _).1 ha P fun e => h (mem_above.2 e)).symm

theorem plc_dvd_iff (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

theorem plc_ne_zero (v : HeightOneSpectrum (𝓞 F)) : Formalism.EigenvalueLevelCeiling.plc v ≠ 0 := fun h => by
  have h1 := (plc_dvd_iff v _).2 (Ideal.absNorm_mem v.asIdeal)
  rw [h, zero_dvd_iff] at h1
  exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h1)

theorem plc_under_eq_iff (P : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime) :
    Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 F)) = p ↔ (p : 𝓞 E) ∈ P.asIdeal := by
  have h1 : (p : 𝓞 E) ∈ P.asIdeal ↔ (p : 𝓞 F) ∈ (P.under (𝓞 F)).asIdeal := by
    rw [← map_natCast (algebraMap (𝓞 F) (𝓞 E))]
    rfl
  rw [h1, ← plc_dvd_iff, Nat.dvd_prime hp]
  refine ⟨Or.inr, fun h => h.resolve_left fun e => ?_⟩
  have h2 := (plc_dvd_iff (P.under (𝓞 F)) 1).1 (by rw [e])
  rw [Nat.cast_one] at h2
  exact (P.under (𝓞 F)).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

theorem exists_under_eq (v : HeightOneSpectrum (𝓞 F)) : ∃ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem local_mem_wildAt {P : HeightOneSpectrum (𝓞 E)} {x : (P.adicCompletion E)ˣ} (hx : IsUnitAt P x)
    (h1 : Valued.v ((x : P.adicCompletion E) - 1) ≤ WithZero.exp (-1 : ℤ)) :
    finAf F E (localIdele E P x) ∈ wildAt E (P.under (𝓞 F)) := by
  refine ⟨?_, local_mem_suppAt P x⟩
  have hu := (finAf_mem_intU_iff (F := F) _).2 (local_mem_unitIdl hx)
  set y := finAf F E (localIdele E P x) with hy
  have hu1 : (y : AfE F E) ∈ RInt F E := hu.1
  have hu2 : ((y⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := hu.2
  refine ⟨⟨⟨_, hu1⟩, ⟨_, hu2⟩, Subtype.ext y.mul_inv, Subtype.ext y.inv_mul⟩, ?_, Units.ext rfl⟩
  rw [SetLike.mem_coe, mem_kerRed]
  set p := Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 F)) with hp
  have hp0 : (p : E) ≠ 0 := Nat.cast_ne_zero.2 (plc_ne_zero _)
  have hv0 : Valued.v (algebraMap E (P.adicCompletion E) (p : E)⁻¹) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 (inv_ne_zero hp0))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Valued.v (algebraMap E (P.adicCompletion E) (p : E)⁻¹) ≤ WithZero.exp (m : ℤ) := by
    refine ⟨(WithZero.log (Valued.v (algebraMap E (P.adicCompletion E) (p : E)⁻¹))).toNat, ?_⟩
    conv_lhs => rw [← WithZero.exp_log hv0]
    exact WithZero.exp_le_exp.2 (Int.self_le_toNat _)
  have hw : (p : E)⁻¹ ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) * ((y : AfE F E) - 1) ^ (m + 1) ∈ RInt F E := by
    rw [mem_rInt_iff]
    intro Q
    rw [map_mul, map_pow, map_sub, map_one, afIso_tmul_one]
    change Valued.v (algebraMap E (Q.adicCompletion E) (p : E)⁻¹ * (afIso F E (y : AfE F E) Q - 1) ^ (m + 1)) ≤ 1
    rw [hy, afIso_finAf_apply]
    by_cases h : Q = P
    · subst h
      rw [ev_local_self, map_mul, map_pow]
      refine (mul_le_mul' hm (pow_le_pow_left' h1 _)).trans ?_
      rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      simp
    · rw [ev_local_ne h]
      simp
  refine ⟨m + 1, Ideal.mem_span_singleton'.2 ⟨⟨_, hw⟩, Subtype.ext ?_⟩⟩
  change (p : E)⁻¹ ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) * ((y : AfE F E) - 1) ^ (m + 1) * ((p : RInt F E) : AfE F E) =
    ((y : AfE F E) - 1) ^ (m + 1)
  have e : ((p : RInt F E) : AfE F E) = (p : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) :=
    (SubringClass.coe_natCast _ _).trans (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E)
      (B := FiniteAdeleRing (𝓞 F) F)) p).symm
  rw [e, mul_right_comm, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hp0, mul_one,
    ← Algebra.TensorProduct.one_def, one_mul]

theorem afIso_one_tmul (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E))
    (h : a (P.under (𝓞 F)) = algebraMap F _ k) :
    afIso F E (1 ⊗ₜ[F] a) P = algebraMap E _ (algebraMap F E k) := by
  have h4 := (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a k P
  change ∀ n : ℕ, _ → Valued.v (afIso F E (1 ⊗ₜ[F] a) P - _) ≤ _ at h4
  by_contra hne
  have h0 := (Valuation.ne_zero_iff (Valued.v : Valuation (P.adicCompletion E) _)).2 (sub_ne_zero.2 hne)
  have h5 := h4 ((-WithZero.log (Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)))).toNat + 1)
    (by rw [h, sub_self, map_zero]; exact zero_le')
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp, WithZero.log_exp] at h5
  omega

theorem finAf_locF_mem (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    finAf F E (locF F v k) ∈ (idF F E).range := by
  refine ⟨Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (localIdele F v (atFin v k)), Units.ext ((afIso F E).injective (FiniteAdeleRing.ext _ fun P => ?_))⟩
  rw [afIso_finAf_apply, locF, Units.coe_prod, map_prod]
  change afIso F E (1 ⊗ₜ[F] ((localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F).2) P = _
  by_cases h : P ∈ aboveF (L := E) F v
  · rw [Finset.prod_eq_single_of_mem P h (fun Q _ hQ => ev_local_ne hQ.symm _), ev_local_self]
    obtain rfl := mem_above.1 h
    exact afIso_one_tmul _ (k : F) P (ev_local_self (P.under (𝓞 F)) (atFin _ k))
  · rw [Finset.prod_eq_one fun Q hQ => ev_local_ne (fun e : P = Q => h (e ▸ hQ)) _,
      afIso_one_tmul _ 1 P ((ev_local_ne (fun e => h (mem_above.2 e)) (atFin v k)).trans (map_one _).symm),
      map_one, map_one]

variable {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr F E K} {ξ : HChar E}

theorem pow_eq_one_iff (h : Reads σ μ ξ) (a : Ideles E) (n : ℕ) : ξ.1 a ^ n = 1 ↔ μ (finAf F E a) ^ n = 1 := by
  rw [Units.ext_iff, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h a, ← map_pow, Units.val_one,
    Units.val_one, map_eq_one_iff σ σ.injective]

theorem eq_one_iff (h : Reads σ μ ξ) (a : Ideles E) : ξ.1 a = 1 ↔ μ (finAf F E a) = 1 := by
  simpa using pow_eq_one_iff h a 1

theorem inert_pow_iff (h : Reads σ μ ξ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (∀ y ∈ inertAt E v, μ y ^ n = 1) ↔
      ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → ∀ x, IsUnitAt P x → ξ.loc P x ^ n = 1 := by
  constructor
  · rintro hy P rfl x hx
    exact (pow_eq_one_iff h _ n).2
      (hy _ ⟨(finAf_mem_intU_iff _).2 (local_mem_unitIdl hx), local_mem_suppAt P x⟩)
  · intro hP y hy
    obtain ⟨a, rfl⟩ := finAf_surjective F E y
    rw [← finAf_part hy.2, ← pow_eq_one_iff h, part, map_prod, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun P hPv => hP P (mem_above.1 hPv) _ ((finAf_mem_intU_iff a).1 hy.1 P)

theorem mem_qprime_iff (h : Reads σ μ ξ) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ Qprime μ ↔ ∃ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v ∧ ¬ ξ.UnrAt P := by
  have h1 := inert_pow_iff h v 1
  simp only [pow_one] at h1
  refine (not_congr h1).trans ?_
  simp only [not_forall, exists_prop, HChar.UnrAt]

theorem tameAt (h : Reads σ μ ξ) (hw : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ μ.ker)
    (P : HeightOneSpectrum (𝓞 E)) : ξ.TameAt P := fun x hx h1 =>
  (eq_one_iff h _).2 (hw _ (local_mem_wildAt hx (by simpa using h1)))

theorem trivOn (h : Reads σ μ ξ) (hF : (idF F E).range ≤ μ.ker) : ξ.TrivOn F := by
  constructor
  · intro v k
    have h1 := (eq_one_iff h _).2 (hF (finAf_locF_mem v k))
    rw [locF, map_prod] at h1
    rw [HChar.resFin, MonoidHom.finsetProd_apply]
    exact h1
  · intro w k
    rw [HChar.resInf, MonoidHom.finsetProd_apply]
    refine Finset.prod_eq_one fun w' _ => (eq_one_iff h (infIdele E w' (atInf w' (upF F k)))).2 ?_
    have e : finAf F E (infIdele E w' (atInf w' (upF F k))) = 1 :=
      Units.ext ((afIso F E).injective (by rw [afIso_finAf, Units.val_one, map_one]; rfl))
    rw [e, map_one]

end General

theorem isTwist_of_reads : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (K : Type) [Field K] (σ : K →+* ℂ) (S : Set ℕ) (μ : Formalism.L2.DIV.Tup H.F H.E K S) (ξ : HChar H.E), Reads σ (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ξ → IsTwist H S ξ ∧ (∀ v : HeightOneSpectrum (𝓞 H.F), v ∈ Formalism.L2.DIV.Qprime (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ↔ ∃ P : HeightOneSpectrum (𝓞 H.E), P.under (𝓞 H.F) = v ∧ ¬ ξ.UnrAt P) ∧ ∀ p : ℕ, p.Prime → (Formalism.L2.DIV.IsBaseChar p (μ.1 : Formalism.L2.DIV.Chr H.F H.E K) ↔ IsDelta (H := H) p ξ) := by
  intro R H K _ σ S μ ξ h
  obtain ⟨⟨⟨⟨-, hfin⟩, hF⟩, hw⟩, hg⟩ := μ.2
  have htw : IsTwist H S ξ := by
    refine ⟨?_, trivOn h hF, tameAt h fun v => Subgroup.mem_iInf.1 hw v, fun P hP => ?_⟩
    · obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
      exact ⟨n, hn, h.orderDvd e⟩
    · rw [← GlobalTheory.Mem.GoodPlace.goodPl_under_iff]
      by_contra hn
      exact (mem_qprime_iff h _).2 ⟨P, rfl, hP⟩ (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg _) hn)
  refine ⟨htw, mem_qprime_iff h, fun p hp => ⟨fun hb => ⟨htw.1, htw.2.1, htw.2.2.1, fun P hP => ?_, fun P hP n => ?_⟩,
    fun hd => ⟨hp, fun v => ⟨fun hv n => ?_, fun hv hq => ?_⟩⟩⟩⟩
  · by_contra hn
    exact (hb.2 _).2 (fun e => hP ((plc_under_eq_iff P hp).1 e)) ((mem_qprime_iff h _).2 ⟨P, rfl, hn⟩)
  · rw [← (hb.2 _).1 ((plc_under_eq_iff (F := H.F) P hp).2 hP) n, inert_pow_iff h]
    exact ⟨fun hx Q hQ => twist_pow_units_of_under_eq R H S ξ htw Q P hQ n hx, fun hx => hx P rfl⟩
  · rw [inert_pow_iff h]
    obtain ⟨P, rfl⟩ := exists_under_eq (E := H.E) v
    exact ⟨fun hx => (hd.ine P ((plc_under_eq_iff P hp).1 hv) n).1 (hx P rfl),
      fun hn Q hQ => (hd.ine Q ((plc_under_eq_iff (F := H.F) Q hp).1 (hQ ▸ hv)) n).2 hn⟩
  · obtain ⟨P, rfl, hP⟩ := (mem_qprime_iff h _).1 hq
    exact hP (hd.unr P fun e => hv ((plc_under_eq_iff P hp).2 e))

end GlobalTheory.Mem.ReadTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMinorsIffBasis
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem prod_zsum_expand {A : Type*} [CommRing A] {L : Type*} [Fintype L] [DecidableEq L]
    {α β : L → Type*} [∀ s, Fintype (β s)] (f : ∀ s, α s → A) (g : ∀ s, β s → A)
    (c : ∀ s, α s → β s → ℤ) (h : ∀ s j, f s j = ∑ k, c s j k • g s k) (j : ∀ s, α s) :
    ∏ s, f s (j s) = ∑ κ : (∀ s, β s), (∏ s, c s (j s) (κ s)) • ∏ s, g s (κ s) := by
  simp only [h, zsmul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl

theorem norm_dual_zsum_le_one (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℂ_[p] M]
    (φ : Module.Dual ℂ_[p] M) {κ : Type*} [Fintype κ] (n : κ → ℤ) (x : κ → M)
    (hx : ∀ k, ‖φ (x k)‖ ≤ 1) : ‖φ (∑ k, n k • x k)‖ ≤ 1 := by
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [map_zsmul, zsmul_eq_mul, norm_mul]
  calc ‖(n k : ℂ_[p])‖ * ‖φ (x k)‖ ≤ 1 * 1 :=
        mul_le_mul (IsUltrametricDist.norm_intCast_le_one _ _) (hx k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem integral_minors_iff_basis : ∀ (p : ℕ) [Fact p.Prime] (Lt : Type) [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ)
    (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ) (d : ∀ s, ι s → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, b s k = ∑ J, (d s k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      (∀ J : WeylLatticeDuality.ColChoice N nu,
          ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ↔
        ∀ κ : (∀ s, ι s), ‖φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
          (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s))))‖ ≤ 1 := by
  intro p _ Lt _ N nu hY ι _ b c d hc hd φ
  classical
  let Ψ : Lt → MvPolynomial (Fin N × Fin N) ℚ →+* MvPolynomial (Lt × ℕ × Fin N) ℂ_[p] := fun s =>
    (MvPolynomial.map (algebraMap ℚ ℂ_[p])).comp (MvPolynomial.rename (sig N s)).toRingHom
  have hF : ∀ J : WeylLatticeDuality.ColChoice N nu,
      MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
        ∏ s, Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s)) := by
    intro J
    have h1 : Int.castRingHom ℂ_[p] = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
    rw [h1, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J, map_prod]
    rfl
  have hG : ∀ κ : (∀ s, ι s), MvPolynomial.map (algebraMap ℚ ℂ_[p])
      (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) = ∏ s, Ψ s (b s (κ s)) := by
    intro κ
    rw [map_prod]
    rfl
  have hc' : ∀ s J, Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) = ∑ k, c s J k • Ψ s (b s k) := by
    intro s J
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_zsmul, Int.cast_smul_eq_zsmul]
  have hd' : ∀ s k, Ψ s (b s k) = ∑ J, d s k J • Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) := by
    intro s k
    conv_lhs => rw [hd]
    rw [map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← map_zsmul, Int.cast_smul_eq_zsmul]
  constructor
  · intro h κ
    rw [hG, prod_zsum_expand (fun s k => Ψ s (b s k)) _ d hd' κ]
    refine norm_dual_zsum_le_one p φ _ _ fun J => ?_
    exact (le_of_eq (congrArg (fun x => ‖φ x‖) (hF J)).symm).trans (h J)
  · intro h J
    rw [hF, prod_zsum_expand (fun s J => Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) _ c hc' J]
    refine norm_dual_zsum_le_one p φ _ _ fun κ => ?_
    have := h κ
    rw [hG] at this
    exact this

end GlobalTheory.WeylLatDualProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
section
noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

@[reducible] def algK (D : D7) (jE : D.host.E →+* Qb) {M : Fld} (h : KQbar D jE ≤ M) : Algebra D.host.K M :=
  ((IntermediateField.inclusion h).toRingHom.comp (D.host.K.equivMap jE.toRatAlgHom).toRingHom).toAlgebra

theorem nfOf {M : Fld} (h : FiniteDimensional ℚ M) : NumberField M where
  to_finiteDimensional := h

theorem isOfFinOrder_fbar {g : ℕ} [Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : IsOfFinOrder x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have := IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 : IsOfFinOrder (Units.mk0 y hy) := isOfFinOrder_of_finite _
  exact ((IntermediateField.adjoin (ZMod g) {x}).val.toMonoidHom.comp (Units.coeHom _)).isOfFinOrder h1

section Iota

theorem mem_of_monoidHom {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g : ℕ} [Fact g.Prime]
    (t : Formalism.CyclotomicNorms.Fbar g →* Ω) (x : Formalism.CyclotomicNorms.Fbar g) : t x ∈ B := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
    rcases eq_or_ne (t 0) 0 with h0 | h0
    · rw [h0]; exact zero_mem _
    · rw [(mul_eq_left₀ h0).1 h]; exact one_mem _
  · exact mem_of_pow_eq_one B (isOfFinOrder_fbar hx).orderOf_pos
      (by rw [← map_pow, pow_orderOf_eq_one, map_one])

def redHom {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g l : ℕ} [Fact g.Prime] [Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (t : Formalism.CyclotomicNorms.Fbar g →* Ω) :
    Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar l where
  toFun x := redThrough B κ (t x)
  map_one' := by rw [map_one]; exact redThrough_one B κ
  map_mul' x y := by
    rw [map_mul]; exact redThrough_mul B κ (mem_of_monoidHom B t x) (mem_of_monoidHom B t y)

end Iota

theorem redHom_inj {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g l : ℕ} [Fact g.Prime] [hl : Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (x y : Formalism.CyclotomicNorms.Fbar g) (hx : x ≠ 0) (hy : y ≠ 0)
    (cx : (orderOf x).Coprime l) (cy : (orderOf y).Coprime l) (h : redHom B κ t x = redHom B κ t y) : x = y := by
  let ρ : B →+* Formalism.CyclotomicNorms.Fbar l := κ.toRingHom.comp (IsLocalRing.residue B)
  have hρ : ∀ z (hz : z ∈ B), redThrough B κ z = ρ ⟨z, hz⟩ := fun z hz => by
    unfold redThrough; rw [dif_pos hz]; rfl
  have hz : x * y⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero hy)
  set n := orderOf (x * y⁻¹) with hn
  have hnpos : 0 < n := (isOfFinOrder_fbar hz).orderOf_pos
  have hcop : n.Coprime l := by
    refine Nat.Coprime.coprime_dvd_left ?_ (Nat.Coprime.mul_left cx cy)
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [mul_pow, inv_pow, pow_mul, pow_orderOf_eq_one, mul_comm (orderOf x), pow_mul, pow_orderOf_eq_one]
    simp
  have hmem := mem_of_monoidHom B t (x * y⁻¹)
  have hprim : IsPrimitiveRoot (t (x * y⁻¹)) n := by
    refine ⟨by rw [← map_pow, hn, pow_orderOf_eq_one, map_one], fun m hm => orderOf_dvd_of_pow_eq_one ?_⟩
    refine ht _ _ (pow_ne_zero _ hz) one_ne_zero ?_
    rw [map_pow, map_one]
    exact hm
  have hprimB : IsPrimitiveRoot (⟨t (x * y⁻¹), hmem⟩ : B) n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.1 hprim
  have hred1 : ρ ⟨t (x * y⁻¹), hmem⟩ = 1 := by
    have hxy : x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
    have hy0 : redHom B κ t y ≠ 0 := by
      intro h0
      have hyo := (isOfFinOrder_fbar hy).orderOf_pos
      have : redHom B κ t y ^ orderOf y = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [h0, zero_pow hyo.ne'] at this
      exact zero_ne_one this
    have h2 : redHom B κ t (x * y⁻¹) * redHom B κ t y = 1 * redHom B κ t y := by
      rw [← map_mul, ← hxy, one_mul, h]
    have h3 := mul_right_cancel₀ hy0 h2
    rw [← hρ]
    exact h3
  have : NeZero ((n : ℕ) : Formalism.CyclotomicNorms.Fbar l) := ⟨fun h0 =>
    (Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop.symm ((CharP.cast_eq_zero_iff _ l n).1 h0)⟩
  have h3 : IsPrimitiveRoot (1 : Formalism.CyclotomicNorms.Fbar l) n := by
    rw [← Polynomial.isRoot_cyclotomic_iff, ← hred1, ← Polynomial.map_cyclotomic n ρ, Polynomial.IsRoot,
      Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [(hprimB.isRoot_cyclotomic hnpos).eq_zero, map_zero]
  have hn1 : n = 1 := IsPrimitiveRoot.one_left_iff.1 h3
  rw [hn, orderOf_eq_one_iff] at hn1
  calc x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
    _ = y := by rw [hn1, one_mul]

end GlobalTheory.ParRay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalLevelVectorLawsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFunctional_levelVector_laws : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c (x : A.N c.1 (S.rep c)), A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x) ∧ (∀ P c, A.fv P c ≠ 0) ∧ ∀ P c, A.te T P c ≠ 0 := by
  first | exact @GlobalTheory.Mem.Col2.fv_te_laws | exact GlobalTheory.Mem.Col2.fv_te_laws | (intros; apply GlobalTheory.Mem.Col2.fv_te_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeDiamond_preserves_complexForms : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaStable emb σ hc := by
  first | exact @GlobalTheory.Mem.Col2.DiaStab.lawDiaStable | exact GlobalTheory.Mem.Col2.DiaStab.lawDiaStable | (intros; apply GlobalTheory.Mem.Col2.DiaStab.lawDiaStable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesIntegralFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeDiamond_preserves_integralForms : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (hF : ((I.S 0).fam emb (lamT hc 0)).Ok) P a x, x ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L → ∃ y ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L, (I.S 0).embF emb σ (lamT hc 0) hF y = J.diaLin emb σ P a ((I.S 0).embF emb σ (lamT hc 0) hF x) := by
  first | exact @GlobalTheory.Mem.Col2.DiaLat.dia_lat | exact GlobalTheory.Mem.Col2.DiaLat.dia_lat | (intros; apply GlobalTheory.Mem.Col2.DiaLat.dia_lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondRepresentationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeDiamond_representation : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaOne emb σ ∧ J.LawDiaMul emb σ := by
  first | exact @GlobalTheory.Mem.Col2.DiaRep.diamond_rep | exact GlobalTheory.Mem.Col2.DiaRep.diamond_rep | (intros; apply GlobalTheory.Mem.Col2.DiaRep.diamond_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationHermitianDualEqStatement
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_hermitianDual_eq : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A → Submodule.IsLattice E B → localization₂ (conjPrime₂ Q).asIdeal A = localization₂ (conjPrime₂ Q).asIdeal B → localization₂ Q.asIdeal (dual (hStd E n) A) = localization₂ Q.asIdeal (dual (hStd E n) B) := by
  first | exact @GlobalTheory.DualLoc.use₅ | exact GlobalTheory.DualLoc.use₅ | (intros; apply GlobalTheory.DualLoc.use₅ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.IntNormFinExt

theorem mem_OL_iff_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (x : ↥K.1), x ∈ Loc.OL K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  fun l _ K x => GlobalTheory.EmbThroughCompletion.mem_OL_iff K x

end GlobalTheory.IntNormFinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyHostHeckeCharacterFrameStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_hostHeckeCharacterFrame : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (e : Fin R.m → R.Psi → ℚ), (∀ k, SplitsC H.E (H.g k)) → SplitsC H.E H.pde → SplitsC H.E H.pde' → (∀ j τ, ∃ z : ℤ, e j τ = z) → (∀ j, UpperTheory.MUQ (embPsi H) (e j)) → Nonempty (HFrame H e) := by
  first | exact @GlobalTheory.nonempty_hFrame | exact GlobalTheory.nonempty_hFrame | (intros; apply GlobalTheory.nonempty_hFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyIsoKGStatement
section
open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_isoKG_of_trace_positive : ∀ (K E : Type) [Field K] [CharZero K] [Field E] [Algebra K E] [FiniteDimensional K E] (cj : E →+* E) (σ : K →+* K) (ι : Type) [Fintype ι], Fintype.card ι = Module.finrank K E → (∀ x, cj (algebraMap K E x) = algebraMap K E (σ x)) → (∀ y, cj (cj y) = y) → (∀ y, Algebra.trace K E (cj y) = σ (Algebra.trace K E y)) → (∀ y, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace K E (y * cj y) = (a : K)) → Nonempty (IsoKG K E cj ι) := by
  first | exact @GlobalTheory.FourCopiesIso.nonempty_isoKG | exact GlobalTheory.FourCopiesIso.nonempty_isoKG | (intros; apply GlobalTheory.FourCopiesIso.nonempty_isoKG <;> assumption)
end

