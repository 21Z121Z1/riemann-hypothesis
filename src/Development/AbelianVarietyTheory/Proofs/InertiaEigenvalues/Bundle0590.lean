import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0394
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureInverseInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.SatLattice

section abstract

variable {R : Type} [CommRing R] [IsDomain R] {π : R} (O : Subring R)

theorem pid_of_fact (hπ : Irreducible π) (hO : π ∈ O)
    (h4 : ∀ w ∈ O, w ≠ 0 → ∃ (k : ℕ) (v v' : R), v ∈ O ∧ v' ∈ O ∧ v * v' = 1 ∧ w = π ^ k * v) :
    IsPrincipalIdealRing O := by
  have hu : ∀ a : O, IsUnit (a : R) → IsUnit a := by
    intro a ha
    obtain ⟨k, v, v', hv, hv', h1, h2⟩ := h4 a a.2 ha.ne_zero
    rcases k with _ | k
    · refine IsUnit.of_mul_eq_one (⟨v', hv'⟩ : O) (Subtype.ext ?_)
      simp [h2, h1]
    · exfalso
      rw [h2, pow_succ', mul_assoc] at ha
      exact hπ.not_isUnit (isUnit_of_mul_isUnit_left ha)
  have hirr : Irreducible (⟨π, hO⟩ : O) := by
    refine ⟨fun h => hπ.not_isUnit (h.map O.subtype), fun a b hab => ?_⟩
    exact (hπ.isUnit_or_isUnit (congrArg Subtype.val hab)).imp (hu a) (hu b)
  have : IsDiscreteValuationRing O := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, ?_⟩
    intro x hx
    obtain ⟨k, v, v', hv, hv', h1, h2⟩ := h4 x x.2 (fun h => hx (Subtype.ext h))
    refine ⟨k, ⟨⟨v, hv⟩, ⟨v', hv'⟩, Subtype.ext h1, Subtype.ext (by simp [mul_comm v' v, h1])⟩, Subtype.ext ?_⟩
    simp [h2]
  infer_instance

theorem sat_pow (hπ : π ≠ 0) (h1 : ∀ w ∈ O, π ∣ w → ∃ v ∈ O, w = π * v) (n : ℕ) (x : R)
    (hx : π ^ n * x ∈ O) : x ∈ O := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    obtain ⟨v, hv, h⟩ := h1 _ hx ⟨π ^ n * x, by ring⟩
    refine ih ?_
    have : π ^ n * x = v := mul_left_cancel₀ hπ (by rw [← h]; ring)
    rwa [this]

def divSub {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (a : R) : Submodule O (Fin d → O) where
  carrier := {x | ∀ i, a ∣ (Y *ᵥ fun j => (x j : R)) i}
  zero_mem' i := by
    simp [Matrix.mulVec, dotProduct]
  add_mem' {x y} hx hy i := by
    have : (fun j => ((x + y) j : R)) = (fun j => (x j : R)) + fun j => (y j : R) := rfl
    rw [this, Matrix.mulVec_add]
    exact dvd_add (hx i) (hy i)
  smul_mem' c x hx i := by
    have : (fun j => ((c • x) j : R)) = (c : R) • fun j => (x j : R) := rfl
    rw [this, Matrix.mulVec_smul]
    exact Dvd.dvd.mul_left (hx i) _

theorem exists_basis_matrix [IsPrincipalIdealRing O] {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (a : R) (ha : a ≠ 0)
    (haO : a ∈ O) :
    ∃ P : Matrix (Fin d) (Fin d) R, (∀ i j, P i j ∈ O) ∧ P.det ≠ 0 ∧ (∀ i j, a ∣ (Y * P) i j) ∧
      ∀ x : Fin d → R, (∀ i, x i ∈ O) → (∀ i, a ∣ (Y *ᵥ x) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ x = P *ᵥ w := by
  set N := divSub O Y a with hN
  have hmem : ∀ v : Fin d → O, (⟨a, haO⟩ : O) • v ∈ N := by
    intro v i
    have : (fun j => (((⟨a, haO⟩ : O) • v) j : R)) = a • fun j => (v j : R) := rfl
    rw [this, Matrix.mulVec_smul]
    exact Dvd.intro _ rfl
  let f : (Fin d → O) →ₗ[O] N := LinearMap.codRestrict N ((⟨a, haO⟩ : O) • LinearMap.id) hmem
  have hf : Function.Injective f := by
    intro v w h
    funext i
    have := congrArg (fun z : N => ((z.1 i : O) : R)) h
    exact Subtype.ext (mul_left_cancel₀ ha this)
  have hr : Module.finrank O N = d := by
    apply le_antisymm
    · simpa using N.finrank_le
    · simpa using LinearMap.finrank_le_finrank_of_injective hf
  let b := Module.finBasisOfFinrankEq O N hr
  let P : Matrix (Fin d) (Fin d) R := Matrix.of fun i j => ((b j).1 i : R)
  have hspan : ∀ x : Fin d → R, (∀ i, x i ∈ O) → (∀ i, a ∣ (Y *ᵥ x) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ x = P *ᵥ w := by
    intro x hx hd
    let z : N := ⟨fun i => ⟨x i, hx i⟩, hd⟩
    refine ⟨fun j => (b.repr z j : R), fun j => (b.repr z j).2, funext fun i => ?_⟩
    have := congrArg (fun z : N => ((z.1 i : O) : R)) (b.sum_repr z)
    refine Eq.trans this.symm ?_
    rw [Submodule.coe_sum, Finset.sum_apply, AddSubmonoidClass.coe_finset_sum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨P, fun i j => ((b j).1 i).2, ?_, fun i j => (b j).2 i, hspan⟩
  have hcol : ∀ j : Fin d, ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ a • (Pi.single j 1 : Fin d → R) = P *ᵥ w := by
    intro j
    refine hspan _ (fun i => ?_) (fun i => ?_)
    · by_cases h : i = j
      · simp [h, haO]
      · simp [h]
    · rw [Matrix.mulVec_smul]
      exact Dvd.intro _ rfl
  choose w _ hw using hcol
  have hPQ : P * Matrix.of (fun i j => w j i) = a • (1 : Matrix (Fin d) (Fin d) R) := by
    ext i j
    have := congrFun (hw j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply] at this
    simp [Matrix.mul_apply, ← this, Matrix.one_apply]
  intro h0
  have := congrArg Matrix.det hPQ
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ ha this.symm

theorem lattice_abstract [IsPrincipalIdealRing O] (hπ : π ≠ 0) (hO : π ∈ O)
    (h1 : ∀ w ∈ O, π ∣ w → ∃ v ∈ O, w = π * v) {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (c : ℕ) (u : Rˣ)
    (hdet : Y.det = π ^ c * u) :
    ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) R), (∀ i j, P i j ∈ O) ∧ P.det ≠ 0 ∧ π ^ m • Y' = Y * P ∧
      (∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, π ^ n ∣ (Y *ᵥ v) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ π ^ m • v = π ^ n • (P *ᵥ w)) ∧
      ∀ w : Fin d → R, (∀ i, w i ∈ O) → (∀ i, π ∣ (Y' *ᵥ w) i) → ∀ i, π ∣ w i := by
  obtain ⟨P, hPO, hP, hdv, hspan⟩ := exists_basis_matrix O Y (π ^ c) (pow_ne_zero _ hπ) (O.pow_mem hO c)
  choose y hy using hdv
  have hY' : π ^ c • Matrix.of y = Y * P := by
    ext i j
    simp [hy]
  have key : ∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, π ^ n ∣ (Y *ᵥ v) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ π ^ c • v = π ^ n • (P *ᵥ w) := by
    intro v hv n hn
    choose z hz using hn
    have hz' : Y *ᵥ v = π ^ n • z := funext hz
    let x : Fin d → R := ((u⁻¹ : Rˣ) : R) • (Y.adjugate *ᵥ z)
    have hx : π ^ c • v = π ^ n • x := by
      have h := congrArg (fun t => ((u⁻¹ : Rˣ) : R) • (Y.adjugate *ᵥ t)) hz'
      simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, hdet] at h
      rw [smul_smul, mul_left_comm, Units.inv_mul, mul_one, smul_comm] at h
      exact h
    have hYx : Y *ᵥ x = π ^ c • z := by
      simp only [x, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, hdet]
      rw [smul_smul, mul_left_comm, Units.inv_mul, mul_one]
    obtain ⟨w, hw, hxw⟩ := hspan x (fun i => sat_pow O hπ h1 n _ (by
      have := congrFun hx i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      exact O.mul_mem (O.pow_mem hO c) (hv i))) (fun i => by rw [hYx]; exact Dvd.intro _ rfl)
    exact ⟨w, hw, by rw [hx, hxw]⟩
  refine ⟨c, P, Matrix.of y, hPO, hP, hY', key, fun w hw hd => ?_⟩
  obtain ⟨w', -, h⟩ := key (P *ᵥ w) (fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact O.sum_mem fun j _ => O.mul_mem (hPO i j) (hw j)) (c + 1) (fun i => by
    rw [Matrix.mulVec_mulVec, ← hY', Matrix.smul_mulVec, pow_succ]
    exact mul_dvd_mul_left _ (hd i))
  have h2 : P *ᵥ (w - π • w') = 0 := by
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine mul_left_cancel₀ (pow_ne_zero c hπ) ?_
    linear_combination this
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hP h2
  intro i
  exact ⟨w' i, sub_eq_zero.1 (congrFun h3 i)⟩

end abstract

theorem exists_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y1 : Matrix (Fin d) (Fin d) (WCb l)), Y1.det ≠ 0 → ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) ∧ P.det ≠ 0 ∧ (l : WCb l) ^ m • Y' = Y1 * P ∧ (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1 *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) ∧ ∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i := by
  intro l _ K bk d Y1 hY
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hirr : Irreducible (l : WCb l) := WittVector.irreducible l
  have : PerfectRing (Cb l) l := by
    refine PerfectRing.ofSurjective _ l fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
    obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
    obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
    exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
      simp [frobenius_def, div_pow, map_pow]⟩
  obtain ⟨c, u, hu⟩ := WittVector.exists_eq_pow_p_mul' Y1.det hY
  have := pid_of_fact bk.OE hirr (natCast_mem _ l) h4
  exact lattice_abstract bk.OE hirr.ne_zero (natCast_mem _ l) h1 Y1 c u hu

end GlobalTheory.SatLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiContractionDiscStep
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem norm_pow_mul_eq_of_norm_mul_eq {R : Type*} [NormedRing R] (E : R) (q : ℝ)
    (hE : ∀ y, ‖E * y‖ = q * ‖y‖) (h : ℕ) (y : R) : ‖E ^ h * y‖ = q ^ h * ‖y‖ := by
  induction h generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, ih, hE, pow_succ]; ring

theorem exists_discStep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∀ (ρ ρ' : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ρ' ^ l = ρ → ∀ (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (R' : Disc l (s X) ρ' →+* Disc l (s X) bk.ρ₀), IsDiscMap (RingHom.id A) R → IsDiscMap (RingHom.id A) R' → ∀ (U : κ → Disc l (s X) ρ) (C : ℝ), 0 ≤ C → Filter.Tendsto U Filter.cofinite (nhds 0) → (∀ j, R (U j) = V j) → (∀ j, ‖U j‖ ≤ C) → ∃ U' : κ → Disc l (s X) ρ', Filter.Tendsto U' Filter.cofinite (nhds 0) ∧ (∀ j, R' (U' j) = V j) ∧ ∀ j, (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ ≤ C := by
  intro l _ K bk A _ s ι tb φ hφ Φ hΦ κ c hc h V hV ρ ρ' hρ₀ hρ1 hρ' R R' hR hR' U C hC hU hRU hUC
  obtain ⟨-, -, ⟨hρ₀pos, hρ₀1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have hρpos : 0 < ρ := hρ₀pos.trans_le hρ₀
  have hρ'pos : 0 < ρ' := by
    rcases (show (0 : ℝ≥0) ≤ ρ' from zero_le).eq_or_lt with h0 | h0
    · rw [← h0, zero_pow (by omega)] at hρ'
      exact absurd hρ' hρpos.ne
    · exact h0
  have hρ'1 : ρ' < 1 := by
    by_contra hh
    push_neg at hh
    have h2 := one_le_pow₀ hh (n := l)
    rw [hρ'] at h2
    exact absurd hρ1 (not_lt.2 h2)
  have hρρ' : ρ ≤ ρ' := by rw [← hρ']; exact pow_le_of_le_one zero_le hρ'1.le (by omega)

  obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l A A φ (s X) (s X) ρ ρ' l hρ'pos (by rw [hφ]) hρ'.le
  have hc1 := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.2 A A (s X) (s X) ρ' bk.ρ₀ φ (RingHom.id A) Φ' R' hΦ' hR'
  have hc2 := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.2 A A (s X) (s X) bk.ρ₀ bk.ρ₀ (RingHom.id A) φ R Φ hR hΦ
  rw [RingHom.id_comp] at hc1
  rw [RingHom.comp_id] at hc2
  have hcomm : ∀ x, R' (Φ' x) = Φ (R x) := fun x => RingHom.congr_fun (hc1.unique hc2) x
  haveI : IsUltrametricDist (Disc l (s X) ρ') := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ').1
  haveI : NonarchimedeanAddGroup (Disc l (s X) ρ') := IsUltrametricDist.nonarchimedeanAddGroup

  have hUn : Filter.Tendsto (fun i => ‖U i‖) Filter.cofinite (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.1 hU
  have hTle : ∀ i j, ‖Φ' (U i) * toDisc l (s X) ρ' (c i j)‖ ≤ ‖U i‖ * ‖toDisc l (s X) ρ' (c i j)‖ := fun i j =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hΦ'.norm_le _) (norm_nonneg _))
  have hTle' : ∀ i j, ‖Φ' (U i) * toDisc l (s X) ρ' (c i j)‖ ≤ ‖U i‖ := fun i j =>
    (hTle i j).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_toDisc_le _))
  have hsum : ∀ j, Summable fun i => Φ' (U i) * toDisc l (s X) ρ' (c i j) := fun j =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (squeeze_zero_norm (fun i => hTle' i j) hUn)
  set Z : κ → Disc l (s X) ρ' := fun j => ∑' i, Φ' (U i) * toDisc l (s X) ρ' (c i j) with hZdef
  have hZC : ∀ j, ‖Z j‖ ≤ C := fun j =>
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun i => (hTle' i j).trans (hUC i)
  have hR'c : Continuous R' :=
    AddMonoidHomClass.continuous_of_bound R' 1 fun y => (hR'.norm_le y).trans (one_mul _).ge
  have hRZ : ∀ j, R' (Z j) = toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j := fun j => by
    have h1 := (hsum j).hasSum.map R' hR'c
    have h2 : (R' ∘ fun i => Φ' (U i) * toDisc l (s X) ρ' (c i j)) =
        fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j) := by
      funext i
      simp only [Function.comp_apply, map_mul, hcomm, hRU, hR'.ext, RingHom.id_apply]
    rw [h2] at h1
    exact h1.unique (hV j)

  have hsmall : ∀ r : ℝ, 0 < r → {j | r < ‖Z j‖}.Finite := by
    intro r hr
    have hF : {i | r < ‖U i‖}.Finite := by
      have := Filter.eventually_cofinite.1 (hUn.eventually (ge_mem_nhds hr))
      simpa only [not_le] using this
    obtain ⟨n, hn⟩ := GlobalTheory.T.norm_baseRingToClosedDisc_J_pow_small l K bk A s ρ' hρ'pos hρ'1 (r / (C + 1)) (by positivity)
    refine (hF.biUnion fun i _ => hc i n).subset ?_
    intro j hj
    by_contra hj'
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hj'
    refine (not_le.2 (show r < ‖Z j‖ from hj)) ?_
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr.le fun i => ?_
    by_cases hi : r < ‖U i‖
    · refine (hTle i j).trans ((mul_le_mul (hUC i) (hn _ (hj' i hi)) (norm_nonneg _) hC).trans ?_)
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    · exact (hTle' i j).trans (not_lt.1 hi)
  have hZ : Filter.Tendsto Z Filter.cofinite (nhds 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => Filter.eventually_cofinite.2 ((hsmall (ε / 2) (by linarith)).subset ?_)
    intro j hj
    simp only [Set.mem_setOf_eq, dist_zero_right, not_lt] at hj ⊢
    linarith

  obtain ⟨hnorm', hdiv'⟩ := GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι tb ρ' (hρ₀.trans hρρ') hρ'1
  obtain ⟨hnorm₀, -⟩ := GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι tb bk.ρ₀ le_rfl hρ₀1
  choose U' hU' using fun j => hdiv' R' hR' h (Z j) ⟨V j, hRZ j⟩
  have hq : (0 : ℝ) < (ρ' : ℝ) ^ (bk.Ep.natDegree * h) := by positivity
  have hnZ : ∀ j, ‖Z j‖ = (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ := fun j => by
    rw [hU' j, norm_pow_mul_eq_of_norm_mul_eq _ _ hnorm' h, pow_mul]
  refine ⟨U', ?_, ?_, fun j => (hnZ j).symm.trans_le (hZC j)⟩
  · have he : ∀ j, ‖U' j‖ = ((ρ' : ℝ) ^ (bk.Ep.natDegree * h))⁻¹ * ‖Z j‖ := fun j => by
      rw [hnZ j, inv_mul_cancel_left₀ hq.ne']
    refine squeeze_zero_norm (fun j => (he j).le) ?_
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hZ).const_mul ((ρ' : ℝ) ^ (bk.Ep.natDegree * h))⁻¹
  · intro j
    have h1 : toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * (R' (U' j) - V j) = 0 := by
      have h2 := hRZ j
      rw [hU' j, map_mul, map_pow, hR'.ext, RingHom.id_apply] at h2
      rw [mul_sub, h2, sub_self]
    have h3 := congrArg norm h1
    rw [norm_pow_mul_eq_of_norm_mul_eq _ _ hnorm₀ h, norm_zero] at h3
    have h4 : (0 : ℝ) < ((bk.ρ₀ : ℝ) ^ bk.Ep.natDegree) ^ h := by positivity
    exact sub_eq_zero.1 (norm_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left h4.ne'))

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTruncLogGalModFil
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BK

theorem exists_truncLog_gal_mod_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(GK K) → ℤ_[l]),
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) →
    ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K),
      aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t) ∈ Per.FilP l m := by
  intro l _ K bk C c hc m
  obtain ⟨M, q, hq1, hq2⟩ := GlobalTheory.T.exists_approx_root_eisenstein_away_prime l K bk m
  obtain ⟨N, r, hr⟩ := GlobalTheory.T.exists_mul_sub_prime_pow_dvd_E_pow l K bk M m q hq1
  obtain ⟨d, hd⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l m
  set w₀ : bk.S := ((l : bk.S) ^ M * X - q) * r with hw₀
  have hE : bk.E ∣ w₀ := by
    have e1 : (l : bk.S) ^ M * X - q = -(q - (l : bk.S) ^ M * X) := by ring
    rw [hw₀, e1]
    exact (dvd_neg.2 hq1).mul_right _
  set s' : bk.S := ∑ j ∈ Finset.range m, (-1) ^ j * ((m.factorial / (j + 1) : ℕ) : bk.S) * w₀ ^ (j + 1) *
    (l : bk.S) ^ (N * (m - (j + 1))) with hs'
  set s : bk.S := (bk.Ep.natDegree : bk.S) * PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d) * s' with hsdef
  refine ⟨m + N * m, s, ?_, fun g => ?_⟩
  · rw [hsdef]
    apply Dvd.dvd.mul_left
    apply Finset.dvd_sum
    intro j _
    exact ((hE.pow (Nat.succ_ne_zero j)).mul_left _).mul_right _

  set R := Per.AinfP l ⧸ Per.kerP l ^ m
  let qm : Per.AinfP l →+* R := Ideal.Quotient.mk _
  let ι : Per.Ainf l →+* Per.AinfP l := algebraMap (Per.Ainf l) (Per.AinfP l)
  have hev : ∀ x, Per.ev l m (aDp l x) = qm (ι x) := fun x => LogFun.ev_alg m (ι x)
  let I : Ideal R := (Per.kerP l).map qm
  have hI : I ^ m = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have hnil : ∀ x ∈ I, x ^ m = 0 := fun x hx => by
    have := Ideal.pow_mem_pow hx m
    rwa [hI, Ideal.mem_bot] at this
  have hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := fun n hn => by
    have := (GlobalTheory.RingBasics.isUnit_nat l n hn).map qm
    rwa [map_natCast] at this
  obtain ⟨lam, hlam⟩ : ∃ lam : R, (l : R) * lam = 1 := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map qm
    rw [map_natCast] at this
    exact this.exists_right_inv
  let f : bk.S →+* R := qm.comp (ι.comp bk.ev)
  let fσ : bk.S →+* R := qm.comp (ι.comp ((Per.σA (g : GQ l)).comp bk.ev))
  have hEm : ι (bk.ev bk.E) ∈ Per.kerP l := by
    have h0 : Per.θ l (bk.ev bk.E) = 0 := by
      have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact this
    first | exact GlobalTheory.RingIface.alg_mem_kerP _ h0 | exact GlobalTheory.RingIface.alg_mem_kerP h0
  have hfE : f bk.E ∈ I := Ideal.mem_map_of_mem _ hEm
  have hfσE : fσ bk.E ∈ I := by
    refine Ideal.mem_map_of_mem _ ?_
    have := GlobalTheory.RingBasics.ker_σ (g : GQ l) hEm
    rwa [Ideal.mem_comap, GlobalTheory.RingBasics.awayMap_algebraMap₂] at this
  have hdvd : ∀ (φ : bk.S →+* R), φ bk.E ∈ I → ∀ x : bk.S, bk.E ^ m ∣ x → φ x = 0 := by
    intro φ hφ x ⟨y, hy⟩
    rw [hy, map_mul, map_pow, hnil _ hφ, zero_mul]
  have hfr : f q * f r = (l : R) ^ N := by
    have := hdvd f hfE _ hr
    rw [map_sub, map_mul, map_pow, map_natCast] at this
    exact sub_eq_zero.1 this
  have hfσr : fσ q * fσ r = (l : R) ^ N := by
    have := hdvd fσ hfσE _ hr
    rw [map_sub, map_mul, map_pow, map_natCast] at this
    exact sub_eq_zero.1 this
  have hσq : fσ q = f q := by
    have h := GlobalTheory.T.eisensteinApproxRoot_galois_sub_mem_bdRFil l K bk m M q hq1 hq2 g
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, hev, map_sub, map_sub] at h
    exact sub_eq_zero.1 h
  have hlamN : (l : R) ^ N * lam ^ N = 1 := by rw [← mul_pow, hlam, one_pow]
  have hσr : fσ r = f r := by
    have hu : IsUnit (f q) := isUnit_iff_exists_inv.2 ⟨f r * lam ^ N, by rw [← mul_assoc, hfr, hlamN]⟩
    apply hu.mul_left_cancel
    rw [← hσq, hfσr, hσq, hfr]
  obtain ⟨e, hxe, he1, hlog⟩ := GlobalTheory.T.galois_factor_tilt_log_bdRPlus l C bk.flat (g : GQ l) (c g) (hc g)
  set τ : R := qm (ι (Per.tm e)) with hτ
  have hσX : fσ X = f X * τ := by
    change qm (ι (Per.σA (g : GQ l) (bk.ev X))) = qm (ι (bk.ev X)) * qm (ι (Per.tm e))
    rw [bk.ev_X, ← map_mul, ← map_mul]
    congr 2
    change Per.σA (g : GQ l) (WittVector.teichmuller l _) = _
    rw [GlobalTheory.RingIface.sigA_teich, hxe, map_mul]
  have hσC : ∀ w, fσ (PowerSeries.C w) = f (PowerSeries.C w) := fun w => by
    change qm (ι (Per.σA (g : GQ l) (bk.ev (PowerSeries.C w)))) = qm (ι (bk.ev (PowerSeries.C w)))
    rw [bk.ev_C, bk.gal_w]
  let T : R → R := fun a => ∑ j ∈ Finset.range m, (-1) ^ j * ((m.factorial / (j + 1) : ℕ) : R) * a ^ (j + 1)
  have hT : ∀ (φ : bk.S →+* R) (a : R), φ w₀ = a * (l : R) ^ N → φ s' = (l : R) ^ (N * m) * T a := by
    intro φ a ha
    simp only [hs', map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, ha, T, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : N * m = N * (j + 1) + N * (m - (j + 1)) := by
      rw [← mul_add]; congr 1; have := Finset.mem_range.1 hj; omega
    rw [hjm]
    ring
  set A : R := f w₀ * lam ^ N with hAdef
  set B : R := fσ w₀ * lam ^ N with hBdef
  have hA : f w₀ = A * (l : R) ^ N := by rw [hAdef]; linear_combination (-(f w₀)) * hlamN
  have hB' : fσ w₀ = B * (l : R) ^ N := by rw [hBdef]; linear_combination (-(fσ w₀)) * hlamN
  have hAI : A ∈ I := by
    obtain ⟨u, hu⟩ := hE
    rw [hAdef, hu, map_mul]
    exact I.mul_mem_right _ (I.mul_mem_right _ hfE)
  have hbI : τ - 1 ∈ I := by
    have := Ideal.mem_map_of_mem qm (LogFun.mu_mem he1)
    simpa [GlobalTheory.MemLoc.mu, hτ] using this
  have hB : B = A + (τ - 1) + A * (τ - 1) := by
    rw [hBdef, hAdef]
    simp only [hw₀, map_mul, map_sub, map_pow, map_natCast, hσX, hσq, hσr]
    linear_combination (τ - 1) * lam ^ N * hfr + (τ - 1) * hlamN
  have htr : T B = T A + T (τ - 1) := by
    rw [hB]
    exact LogAdd.trunc_add hR m I hI A (τ - 1) hAI hbI
  have hl := GlobalTheory.CrisIncl.factorial_mul_ev l e _ he1 hlog m
  have hl2 : (m.factorial : R) * Per.ev l m (aDp l (Per.zA l (c g)) * C.j C.t) = T (τ - 1) := by
    rw [hl]
    simp only [T, map_sum, map_mul, map_pow, map_sub, map_one, map_natCast, map_neg, hτ]
    rfl
  have hfC : (m.factorial : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) = (l : R) ^ m := by
    have := congrArg (f.comp (PowerSeries.C.comp (algebraMap ℤ_[l] (Wq l bk.a)))) hd
    simpa only [map_mul, map_natCast, map_pow, RingHom.comp_apply] using this
  have hfs' := hT f A hA
  have hfσs' := hT fσ B hB'
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
  have e1 : Per.ev l m (aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s)) = fσ s - f s := by
    rw [hev, map_sub, map_sub]; rfl
  have e2 : Per.ev l m ((l : Per.BdRp l) ^ (m + N * m) *
      (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t)) =
      (l : R) ^ (m + N * m) * ((bk.Ep.natDegree : R) * Per.ev l m (aDp l (Per.zA l (c g)) * C.j C.t)) := by
    simp only [map_mul, map_pow, map_natCast]; ring
  rw [map_sub, e1, e2]
  have e3 : fσ s = (bk.Ep.natDegree : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) * fσ s' := by
    rw [hsdef, map_mul, map_mul, map_natCast, hσC]
  have e4 : f s = (bk.Ep.natDegree : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) * f s' := by
    rw [hsdef, map_mul, map_mul, map_natCast]
  rw [e3, e4, hfs', hfσs']
  apply (hR _ m.factorial_ne_zero).mul_left_cancel
  rw [mul_zero]
  linear_combination ((bk.Ep.natDegree : R) * (l : R) ^ (N * m) * (T B - T A)) * hfC -
    ((l : R) ^ (m + N * m) * (bk.Ep.natDegree : R)) * hl2 + ((bk.Ep.natDegree : R) * (l : R) ^ (N * m) * (l : R) ^ m) * htr

end GlobalTheory.BSP.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthCokerOfSurjectiveModUniformizerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteLength_coker_of_surjective_mod_uniformizer : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → IsFiniteLength (A O K) F.coker) ∧ ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM) := by
  first | exact @GlobalTheory.BK.Hom.finiteLength_coker_of_generic | exact GlobalTheory.BK.Hom.finiteLength_coker_of_generic | (intros; apply GlobalTheory.BK.Hom.finiteLength_coker_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedCrystalFrobeniusCoordinatesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedCrystal_frobenius_coordinates : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)), IsCoord e V → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ r : ℕ, a.f t ^ r • (BK.hf g bk.E ^ S.a • V.v a g m - a.f t ^ k • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) = 0 := by
  first | exact @GlobalTheory.BSP.coord_frobenius | exact GlobalTheory.BSP.coord_frobenius | (intros; apply GlobalTheory.BSP.coord_frobenius <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureInverseInvariantStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_inverse_invariant : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ν.IsInvInvariant := by
  first | exact @GlobalTheory.CellDec.NA_isInvInvariant | exact GlobalTheory.CellDec.NA_isInvInvariant | (intros; apply GlobalTheory.CellDec.NA_isInvInvariant <;> assumption)
end

