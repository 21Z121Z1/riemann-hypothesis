import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import GroundTheory.LocalFields.LubinTateLimitGalois
import GroundTheory.LocalFields.LubinTateUnramified
import GroundTheory.LocalFields.KroneckerWeber
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
import Formalism.GaloisCohomology.LocalTateDualityK

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInfMaximalUnramified
section
noncomputable section

open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup IntermediateField

namespace GlobalTheory.PZ.LTExists

section General

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {Ω : Type} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra F Ω] [ValuativeExtension F Ω] [Algebra.IsAlgebraic F Ω]

theorem finrank_inf_maximalUnramified [IsSepClosed Ω] [CharZero F] (E : IntermediateField F Ω)
    [FiniteDimensional F E] :
    Module.finrank F ↥(E ⊓ maximalUnramifiedExtension F Ω) = residueDegree F E := by
  set M := E ⊓ maximalUnramifiedExtension F Ω with hM
  have hME : M ≤ E := inf_le_left
  haveI : FiniteDimensional F M :=
    Module.Finite.of_injective (IntermediateField.inclusion hME).toLinearMap
      (IntermediateField.inclusion_injective hME)
  apply le_antisymm
  · obtain ⟨x, hx⟩ := Field.exists_primitive_element F M
    have hxM : F⟮(x : Ω)⟯ = M := by
      have := congrArg (IntermediateField.map M.val) hx
      rwa [adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map, fieldRange_val] at this
    obtain ⟨U, hU, hxU⟩ := mem_maximalUnramifiedExtension_iff.mp x.2.2
    have := hU.1
    have hMU : M ≤ U := hxM ▸ adjoin_simple_le_iff.mpr hxU
    have he : ramificationIndex F M = 1 := by
      have h := ramificationIndex_dvd_of_le hMU
      rw [hU.ramificationIndex_eq_one] at h
      exact Nat.dvd_one.mp h
    rw [← ramificationIndex_mul_residueDegree F M, he, one_mul]
    exact Nat.le_of_dvd (residueDegree_pos F E) (residueDegree_dvd_of_le hME)
  · obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot_card_residueField_sub_one (L := E)
    have hξ' : IsPrimitiveRoot ((ξ : E) : Ω) (Nat.card 𝓀[F] ^ residueDegree F E - 1) := by
      rw [← card_residueField_eq_pow_residueDegree F E]
      exact (hξ.map_of_injective (f := (𝒪[E]).subtype) Subtype.val_injective).map_of_injective
        (f := E.val) Subtype.val_injective
    have hf0 : residueDegree F E ≠ 0 := (residueDegree_pos F E).ne'
    rw [← (isUnramifiedSubextension_adjoin hf0 hξ').2]
    exact IntermediateField.finrank_le_of_le_right
      (le_inf (adjoin_simple_le_iff.mpr (ξ : E).2) (adjoin_le_maximalUnramifiedExtension hf0 hξ'))

theorem exists_data [IsAlgClosed Ω] [Normal F Ω] {π : 𝒪[F]} (hπ : Irreducible π) :
    ∃ (χ : (Ω ≃ₐ[F] Ω) →* 𝒪[F]ˣ) (z : ℕ → Ω), z 0 = 0 ∧ z 1 ≠ 0 ∧
      (∀ n, algebraMap F Ω (π : F) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[F] = z n) ∧
      ∀ g, ∃ φ : PowerSeries 𝒪[F], PowerSeries.constantCoeff φ = 0 ∧
        PowerSeries.coeff 1 φ = χ g ∧
        PowerSeries.C π * φ + φ ^ Nat.card 𝓀[F] =
          PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[F]) φ ∧
        ∀ n, HasSum (fun k => algebraMap F Ω ((PowerSeries.coeff k φ : 𝒪[F]) : F) * z n ^ k)
          (g (z n)) := by
  have hq := one_lt_card_residueField' F
  have hf := isLubinTateSeries_ltPoly π
  set p := (ltPoly π).map (algebraMap 𝒪[F] F) with hp

  have hsurj : ∀ y : Ω, ∃ x : Ω, Polynomial.aeval x p = y := by
    intro y
    have hd : (p.map (algebraMap F Ω)).natDegree ≠ 0 := by
      rw [hp, Polynomial.map_map, (ltPoly_monic π).natDegree_map, natDegree_ltPoly]
      omega
    obtain ⟨x, hx⟩ := IsAlgClosed.eval_surjective hd y
    exact ⟨x, (Polynomial.eval_map_algebraMap p x).symm.trans hx⟩
  choose r hr using hsurj
  have hπ0 : algebraMap F Ω (π : F) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F Ω).injective]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-algebraMap F Ω (π : F)) (n := Nat.card 𝓀[F] - 1) (by omega)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), zero_eq_neg] at hw
    exact hπ0 hw
  let z : ℕ → Ω := fun n => Nat.casesOn n 0 fun m => r^[m] w
  have hz : ∀ n, Polynomial.aeval (z (n + 1)) p = z n := by
    rintro (_ | n)
    · show Polynomial.aeval w p = 0
      rw [hp, aeval_ltPoly, ← Nat.sub_add_cancel hq.le, pow_succ, hw]
      ring
    · show Polynomial.aeval (r^[n + 1] w) p = r^[n] w
      rw [Function.iterate_succ_apply', hr]
  have hiter : ∀ k n, Polynomial.aeval (z (n + k)) ((ltPolyIter π k).map (algebraMap 𝒪[F] F)) = z n := by
    intro k
    induction k with
    | zero => intro n; simp [ltPolyIter_zero]
    | succ k ih =>
      intro n
      rw [ltPolyIter_succ, Polynomial.map_comp, Polynomial.aeval_comp, ← hz n,
        show n + (k + 1) = n + 1 + k by ring, ih]
  have h0 : ∀ n, Polynomial.aeval (z n) ((ltPolyIter π n).map (algebraMap 𝒪[F] F)) = 0 := by
    intro n
    have h := hiter n 0
    rwa [zero_add] at h
  have hv : ∀ n, valuation Ω (z n) < 1 := fun n =>
    valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n (h0 n)
  let e := lubinTateLimitGalEquiv (Ω := Ω) hπ hf
  refine ⟨e.symm.toMulEquiv.toMonoidHom.comp (AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ)), z, rfl, hw0,
    fun n => by rw [← hz n, hp, aeval_ltPoly], fun g => ?_⟩
  set u : 𝒪[F]ˣ := e.symm (AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ) g) with hu
  have hφ0 := (lubinTateHom hπ hf hf (u : 𝒪[F])).constantCoeff_eq_zero
  refine ⟨(lubinTateHom hπ hf hf (u : 𝒪[F])).toPowerSeries, hφ0, coeff_one_lubinTateHom hπ hf hf _, ?_, fun n => ?_⟩
  · have h := subst_lubinTateHom hπ hf hf (u : 𝒪[F])
    have hc : ((ltPoly π : Polynomial 𝒪[F]) : PowerSeries 𝒪[F]) =
        PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[F] := by
      simp [ltPoly]
    generalize (lubinTateHom hπ hf hf (u : 𝒪[F])).toPowerSeries = φ at h hφ0
    rw [hc] at h
    rw [← h]
    have hs : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ0
    rw [← PowerSeries.coe_substAlgHom hs, map_add, map_mul, map_pow, PowerSeries.substAlgHom_X]
    congr 2
    exact ((PowerSeries.substAlgHom hs).commutes π).symm
  · let x : IdealPoint Ω (lubinTateFormalGroup hπ hf) := IdealPoint.mk (z n) (hv n)
    have hx : x ∈ lubinTateTorsion Ω hf n := (mem_lubinTateTorsion_ltPoly_iff n x).mpr (h0 n)
    have h1 := lubinTateLimitGalEquiv_apply hπ hf u hx
    have h2 : lubinTateLimitGalEquiv (Ω := Ω) hπ hf u = AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ) g :=
      e.apply_symm_apply _
    rw [h2, AlgEquiv.restrictNormalHom_apply, lubinTate_smul_val] at h1
    have h3 := hasSum_psEval' (lubinTateHom hπ hf hf (u : 𝒪[F])).toPowerSeries (fun _ : Unit => z n) fun _ => hv n
    change g (z n) = psEval _ (fun _ => z n) at h1
    rw [← (Finsupp.uniqueEquiv ()).symm.hasSum_iff, ← h1] at h3
    convert h3 using 1
    funext k
    simp [psTerm, PowerSeries.coeff, Finsupp.uniqueEquiv]

theorem map_commute {A B : Type} [CommRing A] [CommRing B] (h : A →+* B) (π : A) {q : ℕ} (hq : q ≠ 0)
    (φ : PowerSeries A) (hc : PowerSeries.C π * φ + φ ^ q =
      PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q) φ) :
    PowerSeries.C (h π) * PowerSeries.map h φ + PowerSeries.map h φ ^ q =
      PowerSeries.subst (PowerSeries.C (h π) * PowerSeries.X + PowerSeries.X ^ q)
        (PowerSeries.map h φ) := by
  have hsub : PowerSeries.HasSubst
      (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hq])
  have h2 := PowerSeries.map_subst hsub (h := h) φ
  rw [← hc] at h2
  change PowerSeries.map h _ = PowerSeries.subst (PowerSeries.map h _) _ at h2
  simpa only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X] using h2

end General

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable (l : ℕ) [Fact l.Prime]

@[instance_reducible]
def omRel : ValuativeRel (Om l) := ValuativeRel.ofValuation (NormedField.valuation (K := Om l))

attribute [local instance] omRel

theorem om_vle_iff (x y : Om l) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl

theorem omTop : IsValuativeTopology (Om l) := by
  have hc : (NormedField.valuation (K := Om l)).Compatible := Valuation.Compatible.ofValuation _
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := Om l))
    (fun {s} ↦ (NormedField.toValued (K := Om l)).is_topological_valuation s)

theorem padic_vle_iff (a b : ℚ_[l]) : a ≤ᵥ b ↔ ‖a‖ ≤ ‖b‖ := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [(valuation ℚ_[l]).vle_iff_le]
    simp
  · rw [(valuation ℚ_[l]).vle_iff_le, ← div_le_one (norm_pos_iff.mpr hb), ← norm_div,
      ← PadicRank.mem_integer_padic_iff, Valuation.mem_integer_iff, map_div₀,
      div_le_one₀ (zero_lt_iff.mpr ((valuation ℚ_[l]).ne_zero_iff.mpr hb))]

theorem omExt : ValuativeExtension ℚ_[l] (Om l) :=
  ⟨fun a b => by rw [om_vle_iff, padic_vle_iff, norm_algebraMap', norm_algebraMap']⟩

attribute [local instance] omTop omExt

variable {l}

theorem mem_OL_iff (K : FinExt l) (x : ↥K.1) : x ∈ OL K ↔ x ∈ 𝒪[↥K.1] := by
  haveI := K.2
  rw [Valuation.mem_integer_iff, ← isIntegral_iff ℚ_[l] ↥K.1 x]
  exact (RingEquiv.isIntegral_iff (PadicRank.padicIntEquivInteger l) (RingHom.ext fun _ => rfl) x)

def intEquiv (K : FinExt l) : 𝒪[↥K.1] ≃+* ↥(OL K) where
  toFun x := ⟨x.1, (mem_OL_iff K _).2 x.2⟩
  invFun x := ⟨x.1, (mem_OL_iff K _).1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem kur_eq : MaximalUnramifiedExtension l = maximalUnramifiedExtension ℚ_[l] (Om l) := by
  have hl : l.Prime := Fact.out
  haveI : CharP 𝓀[ℚ_[l]] l := by
    rw [CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue 𝒪[ℚ_[l]]),
      IsLocalRing.residue_eq_zero_iff]
    exact (GroundTheory.LocalField.Padic.irreducible_natCast_integer l).not_isUnit
  rw [maximalUnramifiedExtension_eq_adjoin, MaximalUnramifiedExtension]
  congr 1
  ext x
  rw [mem_unramifiedRoots_iff]
  refine exists_congr fun m => ?_
  rw [Ne, CharP.cast_eq_zero_iff _ l]
  exact ⟨fun h => h.2, fun h => ⟨Nat.pos_of_ne_zero (by rintro rfl; exact h.1 (dvd_zero l)), h⟩⟩

theorem resCard_eq (K : FinExt l) : haveI := K.2; resCard K = Nat.card 𝓀[↥K.1] := by
  haveI := K.2
  rw [card_residueField_eq_pow_residueDegree ℚ_[l] ↥K.1, GroundTheory.LocalField.Padic.card_residueField,
    resCard, K0, kur_eq, finrank_inf_maximalUnramified]

end GlobalTheory.PZ.LTExists

namespace GlobalTheory.PZ

open Formalism.BasicNotions Formalism.BasicNotions.Loc LTExists

attribute [local instance] omRel omTop omExt

theorem exists_ltData_of_irreducible (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K))
    (hπ : Irreducible π) :
    ∃ (χ : ↥(GK K) →* (↥K.1)ˣ) (z : ℕ → Om l), LTData K χ π z := by
  haveI := K.2
  obtain ⟨π, rfl⟩ := (intEquiv K).surjective π
  have hπ' : Irreducible π := (MulEquiv.irreducible_iff (intEquiv K).toMulEquiv).1 hπ
  obtain ⟨χ, z, h0, h1, hz, H⟩ := exists_data (Ω := Om l) hπ'
  refine ⟨(Units.map (𝒪[↥K.1]).subtype.toMonoidHom).comp
    (χ.comp (IntermediateField.fixingSubgroupEquiv K.1).toMonoidHom), z, hπ, h0, h1,
    fun n => by rw [resCard_eq]; exact hz n, fun g => ?_⟩
  obtain ⟨φ, c0, c1, hc, hs⟩ := H (IntermediateField.fixingSubgroupEquiv K.1 g)
  refine ⟨intEquiv K (χ (IntermediateField.fixingSubgroupEquiv K.1 g)), rfl,
    PowerSeries.map (intEquiv K).toRingHom φ, ⟨?_, ?_, ?_⟩, fun n => hs n⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, c0, map_zero]
  · rw [PowerSeries.coeff_map, c1]
    rfl
  · have hq := one_lt_card_residueField' ↥K.1
    have hr : Nat.card 𝓀[↥K.1] = resCard K := (resCard_eq K).symm
    rw [hr] at hc hq
    exact map_commute (intEquiv K).toRingHom π (by omega) φ hc

end GlobalTheory.PZ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalExactSequenceContinuityAllTheories
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage Filter Topology

namespace GlobalTheory.FundCont

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem l_ne : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem small_mul_mem (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]} {b : P.R.BdR}
    (hc : ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ))) (hb : (l : P.R.BdR) ^ k * b ∈ Lat AI M n) :
    qB P c * b ∈ Lat AI M n := by
  have h0 : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by
    have := (Fact.out : l.Prime).pos
    positivity
  have hz : ‖c / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p_pow, div_le_one h0]
    exact hc
  have := qB_mul_mem_Lat AI T ⟨_, hz⟩ hb
  convert this using 1
  rw [← mul_assoc, ← map_natCast (qB P), ← map_pow, ← map_mul]
  congr 2
  exact (div_mul_cancel₀ _ (pow_ne_zero _ l_ne)).symm

theorem large_mul_mem (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]} {b : P.R.BdR}
    (hc : ‖(l : ℚ_[l]) ^ k * c‖ ≤ 1) (hb : b ∈ Lat AI M (k + n)) :
    qB P c * b ∈ Lat AI M n := by
  rw [← pow_mul_mem_Lat_iff AI (k := k)]
  have := qB_mul_mem_Lat AI T ⟨_, hc⟩ hb
  convert this using 1
  simp only [map_mul, map_pow, map_natCast, mul_assoc]

theorem exists_pow_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, (l : ℝ) ^ (-(k : ℤ)) < ε :=
  PadicInt.exists_pow_neg_lt l hε

theorem exists_mul_le_one (c : ℚ_[l]) : ∃ k : ℕ, ‖(l : ℚ_[l]) ^ k * c‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_pow_lt (l := l) (ε := (‖c‖ + 1)⁻¹) (by positivity)
  refine ⟨k, ?_⟩
  rw [norm_mul, Padic.norm_p_pow]
  calc _ ≤ (‖c‖ + 1)⁻¹ * (‖c‖ + 1) := by gcongr; linarith
    _ = 1 := inv_mul_cancel₀ (by positivity)

variable {X : Type} [TopologicalSpace X]

theorem eventually_orbit (T : LocTied l P AI) {b : P.R.BdR} (hb : b ∈ FilB P 0) (M n : ℕ)
    {c : X → ℚ_[l]} (hc : Continuous c) {γ : X → GQ l} (hγ : Continuous γ) (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, qB P (c x) * P.actQdR (γ x) b - qB P (c x₀) * P.actQdR (γ x₀) b ∈ Lat AI M n := by
  obtain ⟨⟨k, hk⟩, -⟩ := bounded_and_eventually_sub_mem_Lat l P AI T b hb M n
  obtain ⟨j, hj⟩ := exists_mul_le_one (c x₀)
  obtain ⟨-, he⟩ := bounded_and_eventually_sub_mem_Lat l P AI T b hb M (j + n)
  have h0 : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by
    have := (Fact.out : l.Prime).pos
    positivity
  have t1 : Tendsto (fun x => (γ x₀)⁻¹ * γ x) (𝓝 x₀) (𝓝 1) := by
    have : Continuous fun x => (γ x₀)⁻¹ * γ x := continuous_const.mul hγ
    simpa using this.tendsto x₀
  filter_upwards [t1.eventually he, Metric.tendsto_nhds.1 (hc.tendsto x₀) _ h0] with x h1 h2
  rw [dist_eq_norm] at h2
  have h3 := act_mem_Lat AI (γ x) hk
  rw [map_mul, map_pow, map_natCast] at h3
  have h4 := small_mul_mem AI T h2.le h3
  have h5 := act_mem_Lat AI (γ x₀) h1
  rw [map_sub, ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left] at h5
  have h6 := large_mul_mem AI T hj h5
  convert add_mem h4 h6 using 1
  rw [map_sub]
  ring

def LatCont (h : X → P.R.BdR) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (n : ℕ) (x₀ : X), ∀ᶠ x in 𝓝 x₀, tD P ^ N * (h x - h x₀) ∈ Lat AI (N + 1) n

theorem latCont_const (b : P.R.BdR) : LatCont AI (fun _ : X => b) :=
  ⟨0, fun N _ n x₀ => Eventually.of_forall fun x => by simp⟩

theorem LatCont.add {h h' : X → P.R.BdR} (H : LatCont AI h) (H' : LatCont AI h') :
    LatCont AI (fun x => h x + h' x) := by
  obtain ⟨N₀, H⟩ := H
  obtain ⟨N₁, H'⟩ := H'
  refine ⟨max N₀ N₁, fun N hN n x₀ => ?_⟩
  filter_upwards [H N (le_of_max_le_left hN) n x₀, H' N (le_of_max_le_right hN) n x₀] with x a b
  convert add_mem a b using 1
  ring

theorem LatCont.sum {ι : Type} (s : Finset ι) (h : ι → X → P.R.BdR) (H : ∀ i, LatCont AI (h i)) :
    LatCont AI (fun x => ∑ i ∈ s, h i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using latCont_const AI 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (H i).add AI ih

theorem continuous_chi : Continuous fun g : GQ l => (P.χQ g : ℚ_[l]) := by
  obtain ⟨χ, h1, h2, -⟩ := exists_integral_cyclotomicChar l P
  simp only [← h1]
  have h3 : Continuous fun g => (χ g : ℤ_[l]) := Units.continuous_val.comp h2
  exact continuous_subtype_val.comp h3

theorem latCont_orbit (T : LocTied l P AI) (b : P.R.BdR)
    {c : X → ℚ_[l]} (hc : Continuous c) {γ : X → GQ l} (hγ : Continuous γ) :
    LatCont AI (fun x => qB P (c x) * P.actQdR (γ x) b) := by
  obtain ⟨a, ha⟩ := (P.PD (botExt l)).Fil_exh b
  refine ⟨(-a).toNat, fun N hN n x₀ => ?_⟩
  have hb : tD P ^ N * b ∈ FilB P 0 :=
    FilB_anti (by omega) (FilB_mul (FilB_pow tD_mem N) ha)
  have hc' : Continuous fun x => c x * ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹ :=
    hc.mul (((continuous_chi.comp hγ).pow N).inv₀ fun x => pow_ne_zero _ (Units.ne_zero _))
  have e : ∀ x, qB P (c x * ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹) * P.actQdR (γ x) (tD P ^ N * b) =
      tD P ^ N * (qB P (c x) * P.actQdR (γ x) b) := by
    intro x
    have h1 : qB P ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹ * qB P (P.χQ (γ x) : ℚ_[l]) ^ N = 1 := by
      rw [← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), map_one]
    rw [map_mul, map_mul, map_pow, act_tD, mul_pow]
    linear_combination (tD P ^ N * (qB P (c x) * P.actQdR (γ x) b)) * h1
  filter_upwards [eventually_orbit AI T hb (N + 1) n hc' hγ x₀] with x hx
  rwa [e, e, ← mul_sub] at hx

theorem tD_pow_not_mem (T : LocTied l P AI) (N : ℕ) : tD P ^ N ∉ FilB P ((N : ℤ) + 1) := by
  have hu : IsUnit (tD P) := by
    have := (P.PD (botExt l)).t_unit
    rw [P.period_datum_t_eq] at this
    exact this.map P.ιB
  induction N with
  | zero =>
    intro h
    apply (P.PD (botExt l)).not_mem_filtration_two
    rw [P.PD_ι, P.period_datum_t_eq]
    simpa using FilB_mul (tD_mem (P := P)) h
  | succ N ih =>
    intro h
    obtain ⟨y, hy, e⟩ := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 (botExt l) _ _).1 h
    rw [pow_succ'] at e
    apply ih
    rw [hu.mul_left_cancel e]
    exact_mod_cast hy

theorem continuous_of_latCont (T : LocTied l P AI) {c : X → ℚ_[l]}
    (H : LatCont AI (fun x => qB P (c x))) : Continuous c := by
  obtain ⟨N, H⟩ := H
  obtain ⟨n, hn⟩ : ∃ n, tD P ^ N ∉ Lat AI (N + 1) n := by
    by_contra h
    push Not at h
    exact tD_pow_not_mem AI T N (by exact_mod_cast mem_FilB_of_forall_Lat l P AI T (N + 1) _ h)
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt (l := l) hε
  filter_upwards [H N le_rfl (k + n) x₀] with x hx
  rw [dist_eq_norm]
  by_contra hlt
  push Not at hlt
  have h0 : 0 < ‖c x - c x₀‖ := hε.trans_le hlt
  apply hn
  have := large_mul_mem AI T (c := (c x - c x₀)⁻¹) (by
    rw [norm_mul, Padic.norm_p_pow, norm_inv, ← div_eq_mul_inv, div_le_one h0]
    exact hk.le.trans hlt) hx
  rwa [← map_sub, mul_left_comm, ← map_mul, inv_mul_cancel₀ (norm_pos_iff.1 h0), map_one,
    mul_one] at this

theorem contCore_of_tied (T : LocTied l P AI) (K : FinExt l) : contCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A k x β hβ x' f hf
  obtain ⟨-, hfd, hmt, htr, -⟩ := hO
  have hLL : ∀ (φ : A.V →ₗ[ℚ_[l]] ℚ_[l]) (v : A.V), Continuous fun c : LL => φ (c • v) := fun φ v =>
    IsModuleTopology.continuous_of_linearMap
      (φ ∘ₗ (LinearMap.toSpanSingleton LL A.V v).restrictScalars ℚ_[l])
  have hV : ∀ φ : A.V →ₗ[ℚ_[l]] ℚ_[l], Continuous φ := by
    intro φ
    let b := Module.finBasis LL A.V
    have : (φ : A.V → ℚ_[l]) = fun v => ∑ j, φ (b.coord j v • b j) := by
      funext v
      rw [← map_sum]
      simp [b.sum_repr]
    rw [this]
    exact continuous_finset_sum _ fun j _ =>
      (hLL φ (b j)).comp (IsModuleTopology.continuous_of_linearMap (b.coord j))
  have key : ∀ φ : A.V →ₗ[ℚ_[l]] ℚ_[l], Continuous fun g => φ (f g) := by
    intro φ
    let Φ : A.V ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] P.R.BdR :=
      (TensorProduct.lid ℚ_[l] P.R.BdR).toLinearMap ∘ₗ TensorProduct.map φ P.ιB.toLinearMap
    have hΦ : ∀ v b, Φ (v ⊗ₜ b) = qB P (φ v) * P.ιB b := by
      intro v b
      simp [Φ, Algebra.smul_def]
    have h1 : ∀ (y : A.V ⊗[ℚ_[l]] P.R.B) (i : Fin k), LatCont AI fun g => Φ (β i g • y) := by
      intro y i
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        simp only [TensorProduct.smul_tmul', hΦ]
        simpa using latCont_orbit AI T (P.ιB b) ((hLL φ v).comp (hβ i))
          (γ := fun _ => 1) continuous_const
      | add y y' ih ih' =>
        simp only [smul_add, map_add]
        exact ih.add AI ih'
    have h2 : ∀ y : A.V ⊗[ℚ_[l]] P.R.B, LatCont AI fun g => Φ (actVB (P.PD K) A.ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        have e : ∀ g : ↥(GK K), Φ (actVB (P.PD K) A.ρ g (v ⊗ₜ b)) =
            qB P (φ (A.ρ g v)) * P.actQdR (g : GQ l) (P.ιB b) := by
          intro g
          rw [← ιB_act, ← hΦ, ← P.PD_actB]
          rfl
        simp only [e]
        exact latCont_orbit AI T (P.ιB b) ((hV φ).comp (A.cont v)) continuous_subtype_val
      | add y y' ih ih' =>
        simp only [map_add]
        exact ih.add AI ih'
    apply continuous_of_latCont AI T
    have e : ∀ g, qB P (φ (f g)) =
        ∑ i, Φ (β i g • x i) + (Φ (actVB (P.PD K) A.ρ g x') + -Φ x') := by
      intro g
      have := congrArg Φ (hf g)
      rwa [hΦ, map_one, mul_one, map_add, map_sum, map_sub, sub_eq_add_neg] at this
    simp only [e]
    exact (LatCont.sum AI _ _ fun i => h1 (x i) i).add AI ((h2 x').add AI (latCont_const AI _))
  haveI : Module.Finite ℚ_[l] A.V := Module.Finite.trans LL A.V
  let b := Module.finBasis ℚ_[l] A.V
  have : f = fun g => ∑ j, algebraMap ℚ_[l] LL (b.coord j (f g)) • b j := by
    funext g
    simp [b.sum_repr]
  rw [this]
  haveI : ContinuousSMul LL A.V := IsModuleTopology.toContinuousSMul LL A.V
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  exact continuous_finset_sum _ fun j _ =>
    ((continuous_algebraMap ℚ_[l] LL).comp (key (b.coord j))).smul continuous_const

theorem fundamentalExactSequence_continuity_all_theories : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm6 D := fun D l _ K =>
  contCore_of_tied (D.locA l) (D.locT l) K

end GlobalTheory.FundCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeIndexGrowthStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1_lattice_index_growth_of_tateDuality_eulerChar : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  first | exact @GlobalTheory.EulerLevel.card_H1Q_eq | exact GlobalTheory.EulerLevel.card_H1Q_eq | (intros; apply GlobalTheory.EulerLevel.card_H1Q_eq <;> assumption)
end

