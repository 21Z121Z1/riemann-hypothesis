import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInfMaximalUnramifiedExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LubinTateCharacterContinuous
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup GlobalTheory.PZ.LTExist

namespace GlobalTheory.PMC.LTCont

section Abstract

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem pow_dvd_sub_one {π : 𝒪[K]} (hπ : Irreducible π) {z : ℕ → Ω} (hz0 : z 0 = 0) (hz1 : z 1 ≠ 0)
    (hz : ∀ n, algebraMap K Ω (π : K) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[K] = z n)
    {a : 𝒪[K]} {φ : PowerSeries 𝒪[K]} (h0 : PowerSeries.constantCoeff φ = 0)
    (h1 : PowerSeries.coeff 1 φ = a)
    (h2 : PowerSeries.C π * φ + φ ^ Nat.card 𝓀[K] =
      PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[K] :
        PowerSeries 𝒪[K]) φ) (n : ℕ)
    (h3 : HasSum (fun k => algebraMap K Ω ((PowerSeries.coeff k φ : 𝒪[K]) : K) * z n ^ k) (z n)) :
    π ^ n ∣ a - 1 := by
  have hf := isLubinTateSeries_ltPoly π
  have hit : ∀ m n, Polynomial.aeval (z (n + m)) ((ltPolyIter π m).map (algebraMap 𝒪[K] K)) = z n := by
    intro m
    induction m with
    | zero => intro n; simp [ltPolyIter_zero]
    | succ m ih =>
      intro n
      rw [ltPolyIter_succ, Polynomial.map_comp, Polynomial.aeval_comp,
        show n + (m + 1) = (n + 1) + m by ring, ih, aeval_ltPoly, hz]
  have hroot : ∀ n, Polynomial.aeval (z n) ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0 := by
    intro n
    have := hit n 0
    rwa [zero_add, hz0] at this
  have hval : ∀ n, valuation Ω (z n) < 1 := fun n =>
    valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n (hroot n)
  have hpoly : ((ltPoly π : Polynomial 𝒪[K]) : PowerSeries 𝒪[K]) =
      PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[K] := by
    simp [ltPoly, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow]
  have hφ : φ = (lubinTateHom hπ hf hf a).toPowerSeries := by
    refine eq_lubinTateHom_toPowerSeries hπ hf hf a h0 h1 ?_
    have hs : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
    rw [hpoly, ← h2, PowerSeries.subst_add hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs,
      powerSeries_subst_C_mul_X hs]
    rfl
  have := t2Space_of_isValuativeTopology Ω
  let x : ℕ → IdealPoint Ω (lubinTateFormalGroup hπ hf) := fun n => IdealPoint.mk (z n) (hval n)
  have hx : ∀ n, π • x (n + 1) = x n := fun n => by
    apply IdealPoint.ext
    rw [lubinTate_uniformizer_smul_val, psEval_polynomial, aeval_ltPoly]
    exact hz n
  have hxp : ∀ m n, π ^ m • x (n + m) = x n := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ m ih => intro n; rw [pow_succ, mul_smul, ← add_assoc, hx, ih]
  have hax : a • x n = x n := by
    apply IdealPoint.ext
    rw [lubinTate_smul_val, ← hφ]
    change psEval φ (fun _ => z n) = z n
    have h4 := hasSum_psEval' (K := K) (σ := Unit) φ (fun _ => z n) (fun _ => hval n)
    let ι : ℕ ≃ (Unit →₀ ℕ) := (Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)).symm
    rw [← ι.hasSum_iff] at h4
    refine h4.unique ?_
    convert h3 using 1
    funext k
    have hk : ι k = Finsupp.single () k := by
      ext
      simp [ι]
    simp only [Function.comp, psTerm, hk, Finsupp.prod_single_index, pow_zero]
    rfl
  by_cases ha : a - 1 = 0
  · rw [ha]; exact dvd_zero _
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  by_cases hm : n ≤ m
  · rw [hu]; exact Dvd.dvd.mul_left (pow_dvd_pow _ hm) _
  exfalso
  have h5 : (a - 1) • x n = 0 := by rw [sub_smul, hax, one_smul, sub_self]
  have h6 : π ^ m • x n = 0 := by
    have : π ^ m = (↑u⁻¹ : 𝒪[K]) * (a - 1) := by rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this, mul_smul, h5, smul_zero]
  obtain ⟨r, rfl⟩ : ∃ r, n = 1 + (r + m) := ⟨n - 1 - m, by omega⟩
  have h7 := hxp (r + m) 1
  rw [pow_add, mul_smul, h6, smul_zero] at h7
  exact hz1 (congrArg IdealPoint.val h7).symm

end Abstract

section Padic

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] omRel om_isValuativeTopology om_valuativeExtension finExt_finiteDimensional

theorem norm_sub_one_le {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ} {π : ↥(OL K)} {z : ℕ → Om l}
    (h : LTData K χ π z) (n : ℕ) (g : ↥(GK K)) (hg : (g : GQ l) (z n) = z n) :
    ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l) - 1‖ ≤ ‖((π : ↥K.1) : Om l)‖ ^ n := by
  obtain ⟨hπ, hz0, hz1, hz, hact⟩ := h
  obtain ⟨a, ha, φ, ⟨h0, h1, h2⟩, h3⟩ := hact g
  have h3 := h3 n
  rw [hg] at h3
  have hπ' : Irreducible ((intEquiv K).symm π) := (MulEquiv.irreducible_iff (intEquiv K).symm).mpr hπ
  obtain ⟨k0, k1, k2⟩ := map_endo (intEquiv K).symm.toRingHom
    (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) h0 h1 h2
  have hd := pow_dvd_sub_one (Ω := Om l) hπ' hz0 hz1 (by rw [card_residueField_eq]; exact hz) k0 k1
    (by rw [card_residueField_eq]; exact k2) n (by simp only [PowerSeries.coeff_map]; exact h3)
  obtain ⟨c, hc⟩ := hd
  have hc' := congrArg (fun y : 𝒪[↥K.1] => ((y : ↥K.1) : Om l)) hc
  have hcn : ‖((c : ↥K.1) : Om l)‖ ≤ 1 :=
    (GlobalTheory.EmbThroughCompletion.mem_OL_iff K _).mp ((mem_integer_iff K _).mp c.2)
  have e : (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l) - 1 = ((π : ↥K.1) : Om l) ^ n * ((c : ↥K.1) : Om l) := by
    rw [← ha]
    push_cast at hc'
    exact hc'
  rw [e, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) hcn

theorem norm_lt_one {K : FinExt l} {π : ↥(OL K)} (hπ : Irreducible π) : ‖((π : ↥K.1) : Om l)‖ < 1 := by
  have hπ' : Irreducible ((intEquiv K).symm π) := (MulEquiv.irreducible_iff (intEquiv K).symm).mpr hπ
  have h := valuation_algebraMap_lt_one_of_irreducible (L := Om l) hπ'
  rw [← map_one (valuation (Om l)), ← (valuation (Om l)).vlt_iff_lt] at h
  have h' : ¬ ((1 : Om l) ≤ᵥ ((π : ↥K.1) : Om l)) := h
  rw [om_vle_iff, norm_one] at h'
  exact not_le.mp h'

theorem continuous_char {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ} {π : ↥(OL K)} {z : ℕ → Om l}
    (h : LTData K χ π z) : Continuous (fun g : ↥(GK K) => ((χ g : (↥K.1)ˣ) : ↥K.1)) := by
  refine continuous_of_continuousAt_one ((Units.coeHom ↥K.1).comp χ) ?_
  rw [ContinuousAt, map_one, Topology.IsInducing.subtypeVal.tendsto_nhds_iff, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_lt_one h.1)
  let E := IntermediateField.adjoin ℚ_[l] ({z n} : Set (Om l))
  have : FiniteDimensional ℚ_[l] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic (z n)).isIntegral
  have hopen : IsOpen ((fun g : ↥(GK K) => (g : GQ l)) ⁻¹' (E.fixingSubgroup : Set (GQ l))) :=
    E.fixingSubgroup_isOpen.preimage continuous_subtype_val
  filter_upwards [hopen.mem_nhds (show (1 : ↥(GK K)) ∈ _ from E.fixingSubgroup.one_mem)] with g hg
  have hfix : (g : GQ l) (z n) = z n :=
    (IntermediateField.mem_fixingSubgroup_iff E _).mp hg _ (IntermediateField.mem_adjoin_simple_self _ _)
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (norm_sub_one_le h n g hfix) hn

end Padic

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1,
      Continuous (fun g : ↥(GK K) => ((χ g : (↥K.1)ˣ) : ↥K.1)) ∧
        Continuous (fun g : ↥(GK K) => ((ltChar τ₀ χ g : (↥LL.1)ˣ) : ↥LL.1)) := by
  intro l _ K LL χ π z h τ₀
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  refine ⟨continuous_char h, ?_⟩
  have hτ : Continuous τ₀ := τ₀.toLinearMap.continuous_of_finiteDimensional
  exact hτ.comp (continuous_char h)

end GlobalTheory.PMC.LTCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapAlgebraMapPowerSeriesEvalTwoGroups
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem map_algebraMap_powerSeriesEvalTwoGroups : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (τ : Type)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
    map (algebraMap R S) (at2 t u v) = at2 (map (algebraMap R S) t) (up S u) (up S v) := by
  intro R S _ _ _ d τ t u v hu hv
  have ha : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero (fun i => by cases i <;> simp [hu, hv])
  rw [at2, at2, map_subst ha]
  congr 1
  funext i
  cases i <;> rfl

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommute
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

namespace Katz

namespace CoefChange

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (r : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map r (at2 c u v) = at2 (map r c) (fun i => map r (u i)) (fun i => map r (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun j => by
    cases j with
    | inl i => exact hu i
    | inr i => exact hv i))]
  congr 1
  funext j
  cases j <;> rfl

theorem map_subst' (r : R →+* S) {σ : Type} [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    map r (subst a f) = subst (fun i => map r (a i)) (map r f) := by
  rw [map_subst (hasSubst_of_constantCoeff_zero ha)]

theorem map_inL (r : R →+* S) (f : MvPowerSeries (Fin d) R) : map r (inL f) = inL (map r f) := by
  unfold inL
  rw [map_subst' r _ (fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X r _

theorem map_inR (r : R →+* S) (f : MvPowerSeries (Fin d) R) : map r (inR f) = inR (map r f) := by
  unfold inR
  rw [map_subst' r _ (fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X r _

theorem inL_const {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (inL f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) hf

theorem inR_const {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (inR f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) hf

end CoefChange

open CoefChange in

theorem map_cob_swap_pull : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (S : Type) [CommRing S] (r : R →+* S), (∀ f, map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f)) ∧ (∀ c, map r (cob2 μ c) = cob2 (fun i => map r (μ i)) (map r c)) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, map r (Katz.swap c) = Katz.swap (map r c)) ∧ (∀ f : MvPowerSeries (Fin d) R, lin (map r f) = fun i => r (lin f i)) ∧ ∀ φ : Fin d → MvPowerSeries (Fin d) R, (∀ i, constantCoeff (φ i) = 0) → (∀ c, map r (pull2 φ c) = pull2 (fun i => map r (φ i)) (map r c)) ∧ ∀ f : MvPowerSeries (Fin d) R, map r (subst φ f) = subst (fun i => map r (φ i)) (map r f) := by
  intro R _ d μ hμ S _ r
  have hX : ∀ {τ : Type} (i : τ), constantCoeff (X i : MvPowerSeries τ R) = 0 :=
    fun i => constantCoeff_X i
  have hop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    unfold op at2
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (fun j => by
      cases j with
      | inl i => exact hu i
      | inr i => exact hv i)) (fun j => by
      cases j with
      | inl i => exact hu i
      | inr i => exact hv i) (hμ i)
  have mapop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      (fun i => map r (op μ u v i)) =
        op (fun i => map r (μ i)) (fun i => map r (u i)) (fun i => map r (v i)) := by
    intro u v hu hv
    funext i
    exact mvPowerSeriesMap_evalTwoGroups r (μ i) u v hu hv
  have mx1 : (fun i => map r ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x1 := by
    funext i; exact map_X r _
  have mx2 : (fun i => map r ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x2 := by
    funext i; exact map_X r _
  have mx3 : (fun i => map r ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x3 := by
    funext i; exact map_X r _
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold cob1
    rw [map_sub, map_sub, map_subst' r μ hμ, map_inL, map_inR]
  · intro c
    unfold cob2
    rw [map_sub, map_add, map_sub, mvPowerSeriesMap_evalTwoGroups r c _ _ h2 h3, mvPowerSeriesMap_evalTwoGroups r c _ _ (hop _ _ h1 h2) h3,
      mvPowerSeriesMap_evalTwoGroups r c _ _ h1 (hop _ _ h2 h3), mvPowerSeriesMap_evalTwoGroups r c _ _ h1 h2, mapop _ _ h1 h2,
      mapop _ _ h2 h3, mx1, mx2, mx3]
  · intro c
    unfold Katz.swap
    rw [mvPowerSeriesMap_evalTwoGroups r c _ _ (fun _ => hX _) (fun _ => hX _)]
    congr 1 <;> funext i <;> exact map_X r _
  · intro f
    funext i
    unfold lin
    rw [coeff_map]
  · intro φ hφ
    refine ⟨?_, fun f => map_subst' r φ hφ f⟩
    intro c
    unfold pull2
    rw [mvPowerSeriesMap_evalTwoGroups r c _ _ (fun i => inL_const (hφ i)) (fun i => inR_const (hφ i))]
    congr 1 <;> funext i
    · exact map_inL r (φ i)
    · exact map_inR r (φ i)

end Katz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecond

theorem map_formalGroupLawCoboundaryOne_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

end GlobalTheory.SmallSecond

namespace GlobalTheory.SmallSecond

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] {θ : B →+* O} {Θ : Q →+* C}

theorem map_up {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) :
    (fun i => map Θ (up Q μ' i)) = up C (fun i => map θ (μ' i)) := by
  funext i; ext α; simp [up, coeff_map, hΘ]

theorem map_formalGroupLawCoboundaryOne_square {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    map Θ (cob1 (up Q μ') f) = cob1 (up C (fun i => map θ (μ' i))) (map Θ f) := by
  rw [map_formalGroupLawCoboundaryOne_eq Θ _ (fun i => by simp [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
    coeff_zero_eq_constantCoeff_apply, hμ]), map_up hΘ]

theorem map_comb {σ ι : Type} [Fintype ι] (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) (fun i => map Θ (e i)) := by
  unfold comb
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map, map_mul, hΘ]

theorem ql_map {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : QL μ' ⊤ f) :
    QL (fun i => map θ (μ' i)) ⊤ (map Θ f) := by
  obtain ⟨h0, h1, h2⟩ := hf
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  · obtain ⟨b, -, hb⟩ := h1 i
    exact ⟨θ b, trivial, by simp only [lin, coeff_map] at hb ⊢; rw [hb, hΘ]⟩
  · rw [← map_formalGroupLawCoboundaryOne_square hΘ μ' hμ]
    intro α
    obtain ⟨b, -, hb⟩ := h2 α
    exact ⟨θ b, trivial, by rw [coeff_map, hb, hΘ]⟩

theorem formalGroupLawCoboundaryOne_map_eq_zero {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : In (RingHom.ker θ) (cob1 (up Q μ') f)) :
    cob1 (up C (fun i => map θ (μ' i))) (map Θ f) = 0 := by
  rw [← map_formalGroupLawCoboundaryOne_square hΘ μ' hμ]
  ext α
  obtain ⟨b, hb0, hb⟩ := hf α
  rw [coeff_map, hb, hΘ, RingHom.mem_ker.1 hb0, map_zero, map_zero]

end GlobalTheory.SmallSecond
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInvariantDerivationFormalGroupLawIterate
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LawDer

theorem map_pderiv_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries σ R) (s : σ) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv R s f) = MvPowerSeries.pderiv S s (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map,
    map_mul, map_add, map_natCast, map_one]

theorem map_atZero {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (H : MvPowerSeries (Fin d ⊕ Fin d) R) : map f (atZero H) = atZero (map f H) := by
  unfold atZero
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp))]
  congr 1
  funext s
  cases s <;> simp

theorem map_smul_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R)
    (H : MvPowerSeries σ R) : map f (a • H) = f a • map f H := by
  ext m
  simp [MvPowerSeries.coeff_map, MvPowerSeries.coeff_smul]

theorem map_invDer {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) (F : MvPowerSeries (Fin d) R) :
    map f (invDer μ u F) = invDer (fun i => map f (μ i)) (fun i => f (u i)) (map f F) := by
  unfold invDer
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul_coeffChange, map_atZero, map_pderiv_coeffChange, map_subst (hasSubst_of_constantCoeff_zero hμ)]

theorem map_invDer_iterate : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) →
    ∀ (u : Fin d → R) (k : ℕ) (F : MvPowerSeries (Fin d) R),
    map f ((invDer μ u)^[k] F) = (invDer (fun i => map f (μ i)) (fun i => f (u i)))^[k] (map f F) := by
  intro R S _ _ f d μ hμ u k F
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_invDer f μ hμ, ih]

end GlobalTheory.LawDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPowerSeriesFamilyToFractionsFormalGroupLawNat
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem constantCoeff_nmul_zero {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ n ih =>
    intro i
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0 := by
      intro j; cases j with
      | inl j => exact ih j
      | inr j => simp
    show constantCoeff ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1]
      (fun _ => 0) i) = 0
    rw [Function.iterate_succ_apply']
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

theorem up_nmul : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) → ∀ n : ℕ, up S (nmul μ n) = nmul (up S μ) n := by
  intro R S _ _ _ d μ hμ n
  induction n with
  | zero => funext i; simp [up, nmul]
  | succ n ih =>
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0 := by
      intro j; cases j with
      | inl j => exact constantCoeff_nmul_zero μ hμ n j
      | inr j => simp
    funext i
    show map (algebraMap R S) ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1]
      (fun _ => 0) i) = (fun v : Fin d → MvPowerSeries (Fin d) S => op (up S μ) v fun i => X i)^[n + 1]
      (fun _ => 0) i
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change map (algebraMap R S) (subst (Sum.elim (nmul μ n) fun i => X i) (μ i)) =
      subst (Sum.elim (nmul (up S μ) n) fun i => X i) (up S μ i)
    rw [map_subst (hasSubst_of_constantCoeff_zero h0), ← ih]
    congr 1
    funext j
    cases j with
    | inl j => rfl
    | inr j => simp

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectProjectionNaturalIdempotentReducedStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfectProjection_natural_idempotent_reduced : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Module.Finite k B] (π : A →ₐ[k] A) (π' : B →ₐ[k] B), ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : B, IsNilpotent (a - π' a)) ∧ ∀ a : B, ∃ b : B, π' a = π' b ^ p) → (∀ (f : A →ₐ[k] B) (a : A), f (π a) = π' (f a)) ∧ (∀ b, π' (π' b) = π' b) ∧ ∀ b, IsNilpotent (π' b) → π' b = 0 := by
  first | exact @GlobalTheory.PerfectProj.natural_idempotent_reduced | exact GlobalTheory.PerfectProj.natural_idempotent_reduced | (intros; apply GlobalTheory.PerfectProj.natural_idempotent_reduced <;> assumption)
end

