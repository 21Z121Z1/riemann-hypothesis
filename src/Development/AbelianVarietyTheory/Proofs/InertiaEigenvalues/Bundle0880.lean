import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0874
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0073
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperator

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellDecompositionLatticeIntegralUnfolding
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell.CptMod

variable {E : Type} [Field E] [NumberField E]

theorem continuous_finGL_cpt {a : ℕ} : Continuous (finGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem exists_pLoc_ite {n : ℕ} (c : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ h : GL (Fin n) (Af E), ∀ w, GeneralLinearGroup.map (pLoc E w) h = if w ∈ T then c w else 1 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, fun w => by simp⟩
  | insert v T hvT ih =>
    obtain ⟨h, hh⟩ := ih
    refine ⟨locGL E n v (c v) * h, fun w => ?_⟩
    rw [map_mul, hh w]
    by_cases hw : w = v
    · subst hw
      rw [pLoc_locGL, if_neg hvT, if_pos (Finset.mem_insert_self _ _), mul_one]
    · rw [pLoc_locGL_of_ne hw, one_mul]
      simp [Finset.mem_insert, hw]

theorem isCompact_intGL (n : ℕ) :
    IsCompact {κ : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ GlobalTheory.LFun.KGL w n} := by
  convert GlobalTheory.isCompact_KGL E n using 1
  ext κ
  simp only [Set.mem_setOf_eq, GlobalTheory.LFun.KGL, GlobalTheory.CellDec.mem_GLint_iff_entries_cell, ← map_inv]
  constructor
  · intro h
    exact ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩
  · intro h v
    exact ⟨fun i j => h.1 i j v, fun i j => h.2 i j v⟩

theorem row_mul_inv {R : Type} [CommRing R] {n : ℕ} {A B : GL (Fin n) R} {i : Fin n}
    (h : (A : Matrix (Fin n) (Fin n) R) i = (B : Matrix (Fin n) (Fin n) R) i) :
    ((A * B⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i = (1 : Matrix (Fin n) (Fin n) R) i := by
  funext j
  rw [Units.val_mul, Matrix.mul_apply, h, ← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem row_last_unip_mul {R : Type} [CommRing R] {m : ℕ} {u : GL (Fin (m + 1)) R}
    (hu : u ∈ GlobalTheory.SmGL.unipB R (Fin (m + 1))) (k : GL (Fin (m + 1)) R) :
    ((u * k : GL (Fin (m + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) =
      (k : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
  funext j
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · rw [h2, one_mul]
  · intro i _ hi
    rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last i) hi), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem row_tl_mul {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {i : Fin n} (hl : ∀ w, l w i = 0) (g : GA E n) :
    ((GlobalTheory.CellDec.tl n ϖ l * g : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i = (g : Matrix (Fin n) (Fin n) (Ad E)) i := by
  have h0 : Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l = 0 := by
    ext w
    simp [hl w]
  funext j
  rw [GlobalTheory.CellDec.tl_eq_diagT, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul]
  simp only [h0, GlobalTheory.CellDec.adl_zero, map_one, Units.val_one, one_mul]

theorem compV_tl_eq_one {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {w : HeightOneSpectrum (𝓞 E)} (hw : l w = 0) :
    GlobalTheory.CellDec.compV E n w (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  rw [GlobalTheory.CellDec.compV_tl, hw]
  apply Units.ext
  rw [GlobalTheory.IwaCell.val_tD]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply]

theorem tl_mul_comm [IsTotallyComplex E] {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (hl : ∀ v ∈ T, l v = 0) {p : GA E n}
    (hp : ∀ w ∉ T, GlobalTheory.CellDec.compV E n w p = 1) :
    GlobalTheory.CellDec.tl n ϖ l * p = p * GlobalTheory.CellDec.tl n ϖ l := by
  apply ga_ext
  · simp [GlobalTheory.CellDec.tl, map_mul]
  · apply GlobalTheory.CellDec.GL_ext_pLoc
    intro w
    change GlobalTheory.CellDec.compV E n w (GlobalTheory.CellDec.tl n ϖ l * p) = GlobalTheory.CellDec.compV E n w (p * GlobalTheory.CellDec.tl n ϖ l)
    rw [map_mul, map_mul]
    by_cases hw : w ∈ T
    · rw [compV_tl_eq_one ϖ l (hl w hw), one_mul, mul_one]
    · rw [hp w hw, one_mul, mul_one]

end GlobalTheory.RSCell.CptMod

namespace GlobalTheory.RSCell.CptMod

open scoped Pointwise

theorem exists_isCompact_mod_NA : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : Set (GA E (m + 1))), IsCompact C →
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ GlobalTheory.JSW.mirS E T m, GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) →
    HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (m + 1)) ∧ (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ (x : ℝ) (g : GA E (m + 1)), g ∈ GlobalTheory.CellDec.C0 E (m + 1) T →
      GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
  intro E _ _ _ m T ϖ hϖ F l₀ U Φ J C hC hl0 hU hKT hN hsupp hΦ hΦs hJ horb
  set K₁ : Set (GA E (m + 1)) :=
    finGL E (m + 1) '' {κ | ∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ GlobalTheory.LFun.KGL w (m + 1)} with hK₁d
  set K₂ : Set (GA E (m + 1)) :=
    (fun u => infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) u)) '' tsupport Φ with hK₂d
  have hK₁ : IsCompact K₁ := (isCompact_intGL (m + 1)).image continuous_finGL_cpt
  have hK₂ : IsCompact K₂ := (show IsCompact (tsupport Φ) from hΦ).image_of_continuousOn
    (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn ((GlobalTheory.RSTheta.continuousOn_rowGL (Fin.last m)).mono hΦs))
  refine ⟨C * K₁ * K₂ * K₁, ((hC.mul hK₁).mul hK₂).mul hK₁, ?_⟩
  intro x g hg hB
  obtain ⟨u₁, hu₁, k, hk, rfl⟩ := hg
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 with ht
  have hrow : ((t * (u₁ * k) : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) =
      (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) := by
    rw [row_tl_mul ϖ l₀.1 hl0, row_last_unip_mul hu₁]
  set u : Fin (m + 1) → Cinf E := fun i => pInf E ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i) with hud
  set yf : Fin (m + 1) → Af E := fun i => pFin E ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i) with hyf
  set σ := infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) u) with hσ
  have hB1 := left_ne_zero_of_mul hB
  rw [enorm_ne_zero] at hB1
  unfold GlobalTheory.RSTheta.rsPsi GlobalTheory.ThetaPoisson.thetaFn at hB1
  rw [hrow] at hB1
  obtain ⟨hB2, hlat⟩ := mul_ne_zero_iff.1 hB1
  have hlat' : yf - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J := Set.mem_of_indicator_ne_zero hlat
  unfold GlobalTheory.RSTheta.rsInf at hB2
  obtain ⟨hB3, hΦu⟩ := mul_ne_zero_iff.1 hB2
  have hW : GlobalTheory.JSW.whit F (t * (u₁ * k) * σ⁻¹) ≠ 0 := left_ne_zero_of_mul hB3
  have hu_supp : u ∈ tsupport Φ := subset_tsupport _ (Function.mem_support.2 hΦu)
  have hunit : IsUnit (u (Fin.last m)) := GlobalTheory.RSTheta.isUnit_of_mem_rowSet (hΦs hu_supp)
  obtain ⟨κ, hκU, hκK, hκ1, hκrow⟩ := horb yf hlat'
  obtain ⟨hf, hhf⟩ := exists_pLoc_ite (fun w => GlobalTheory.CellDec.compV E (m + 1) w k) T
  set h := infGL E (m + 1) (GeneralLinearGroup.map (pInf E) k) * finGL E (m + 1) hf with hhd
  set kT := h⁻¹ * k with hkTd
  have hcV_inf : ∀ w (y : GL (Fin (m + 1)) (Cinf E)), GlobalTheory.CellDec.compV E (m + 1) w (infGL E (m + 1) y) = 1 := by
    intro w y
    change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (infGL E (m + 1) y)) = 1
    rw [pFin_infGL, map_one]
  have hcV_h : ∀ w, GlobalTheory.CellDec.compV E (m + 1) w h = if w ∈ T then GlobalTheory.CellDec.compV E (m + 1) w k else 1 := by
    intro w
    rw [hhd, map_mul, hcV_inf, GlobalTheory.CellDec.compV_finGL, hhf w, one_mul]
  have hinf_h : GeneralLinearGroup.map (pInf E) h = GeneralLinearGroup.map (pInf E) k := by
    rw [hhd, map_mul, pInf_infGL, pInf_finGL, mul_one]
  have hkT_inf : GeneralLinearGroup.map (pInf E) kT = 1 := by
    rw [hkTd, map_mul, map_inv, hinf_h, inv_mul_cancel]
  have hkT_T : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w kT = 1 := by
    intro w hw
    rw [hkTd, map_mul, map_inv, hcV_h, if_pos hw, inv_mul_cancel]
  have hkT_US : kT ∈ GlobalTheory.CellDec.US E (m + 1) T := GlobalTheory.CellDec.mem_US.2 fun w hw => by
    rw [hkTd, map_mul, map_inv, hcV_h, if_neg hw, inv_one, one_mul]
    exact GlobalTheory.CellDec.mem_US.1 hk w hw
  have hkT_fin : kT = finGL E (m + 1) (GeneralLinearGroup.map (pFin E) kT) := by
    conv_lhs => rw [← infGL_mul_finGL kT]
    rw [hkT_inf, map_one, one_mul]
  have hkT_K : ∀ w, GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) kT) ∈ GlobalTheory.LFun.KGL w (m + 1) := by
    intro w
    change GlobalTheory.CellDec.compV E (m + 1) w kT ∈ _
    by_cases hw : w ∈ T
    · rw [hkT_T w hw]
      exact one_mem _
    · exact GlobalTheory.CellDec.mem_US.1 hkT_US w hw
  set B := finGL E (m + 1) κ * σ with hBd
  have hrowB : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) =
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) := by
    funext j
    apply ad_ext
    · change (GeneralLinearGroup.map (pInf E) h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j =
        (GeneralLinearGroup.map (pInf E) B : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j
      rw [hinf_h, hBd, map_mul, pInf_finGL, one_mul, hσ, pInf_infGL, GlobalTheory.RSTheta.val_rowGL hunit,
        GlobalTheory.RSTheta.rowMat, Matrix.updateRow_self]
      rfl
    · apply IsDedekindDomain.FiniteAdeleRing.ext
      intro w
      change (GlobalTheory.CellDec.compV E (m + 1) w h : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
        (GlobalTheory.CellDec.compV E (m + 1) w B : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j
      rw [hcV_h, hBd, map_mul, GlobalTheory.CellDec.compV_finGL, hσ, hcV_inf, mul_one]
      split_ifs with hw
      · rw [hκrow w hw j]
        rfl
      · rw [hκ1 w hw]
  set p := h * B⁻¹ with hpd
  have hp_sup : ∀ w ∉ T, GlobalTheory.CellDec.compV E (m + 1) w p = 1 := by
    intro w hw
    rw [hpd, map_mul, map_inv, hcV_h, if_neg hw, hBd, map_mul, GlobalTheory.CellDec.compV_finGL, hκ1 w hw, hσ, hcV_inf,
      mul_one, inv_one, one_mul]
  have hp_mir : p ∈ GlobalTheory.JSW.mirS E T m := by
    refine ⟨fun w hw => hp_sup w hw, fun j => ?_⟩
    have e := congrFun (row_mul_inv hrowB) j
    rw [← hpd] at e
    rw [e, Matrix.one_apply]
    by_cases hj : j = Fin.last m
    · rw [if_pos hj.symm, if_pos hj]
    · rw [if_neg (Ne.symm hj), if_neg hj]
  have hcomm : kT * σ⁻¹ = σ⁻¹ * kT := by
    rw [hkT_fin, hσ, ← map_inv]
    exact (infGL_comm _ _).symm
  have hnorm : ‖GlobalTheory.JSW.whit F (t * (u₁ * k) * σ⁻¹)‖ = ‖GlobalTheory.JSW.whit F (p * t)‖ := by
    have e1 : t * (u₁ * k) * σ⁻¹ = (t * u₁ * t⁻¹) * (t * k * σ⁻¹) := by group
    rw [e1, hN _ (GlobalTheory.CellDec.tl_conj_mem ϖ l₀.1 hu₁)]
    have e2 : t * k * σ⁻¹ = t * h * σ⁻¹ * kT := by
      rw [mul_assoc (t * h), ← hcomm, hkTd]
      group
    rw [e2, hKT kT hkT_US hkT_inf hkT_T]
    have e3 : t * h * σ⁻¹ = t * p * finGL E (m + 1) κ := by
      rw [hpd, hBd]
      group
    rw [e3, hU κ hκU, tl_mul_comm ϖ l₀.1 l₀.2 hp_sup]
  have hWp : GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
    rw [← ht, ← norm_ne_zero_iff, ← hnorm, norm_ne_zero_iff]
    exact hW
  obtain ⟨u₂, hu₂, hu₂C⟩ := hsupp p hp_mir hWp
  refine ⟨u₂ * u₁⁻¹, mul_mem hu₂ (inv_mem hu₁), ?_⟩
  have e : u₂ * u₁⁻¹ * (u₁ * k) = u₂ * p * finGL E (m + 1) κ * σ * finGL E (m + 1) (GeneralLinearGroup.map (pFin E) kT) := by
    rw [← hkT_fin, hpd, hBd, hkTd]
    group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hu₂C ⟨κ, hκK, rfl⟩) ⟨u, hu_supp, rfl⟩) ⟨_, hkT_K, rfl⟩

end GlobalTheory.RSCell.CptMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumTermsInvariantPrincipalLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSumTerms_invariant_principalLevel : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ F ∈ B.formsC ψ, ∀ g : GA D T,
      (∀ (γ : GQ S) (y : Bridge.Gf S),
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
          (F (Bridge.ratF S γ * y)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g) ∧
      ∀ k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ, ∀ y : Bridge.Gf S,
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
          (F (y * k)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  first | exact @GlobalTheory.PrincClassSum.terms_inv | exact GlobalTheory.PrincClassSum.terms_inv | (intros; apply GlobalTheory.PrincClassSum.terms_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanLeftInvariant
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.JSW

theorem mspanR_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ F ∈ GlobalTheory.JSW.mspanR π,
    ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g := by
  intro E _ _ _ a π
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g}
      add_mem' := by
        intro F G hF hG γ g
        simp only [Pi.add_apply, hF γ g, hG γ g]
      zero_mem' := by intro γ g; rfl
      smul_mem' := by
        intro c F hF γ g
        simp only [Pi.smul_apply, hF γ g] }
  have hS : mspanR π ≤ S := by
    refine sInf_le ⟨?_, ?_, ?_⟩
    · intro φ hφ γ g
      exact (π.cusp φ hφ).1.left γ g
    · intro F hF h γ g
      show F (ratGL E a γ * g * h) = F (g * h)
      rw [mul_assoc]; exact hF γ (g * h)
    · intro F hF X _ ν _ k γ' _ γ g
      show (∫ x, k x * F (ratGL E a γ * g * infGL E a (γ' x)) ∂ν) = ∫ x, k x * F (g * infGL E a (γ' x)) ∂ν
      congr 1
      funext x
      rw [mul_assoc, hF γ (g * infGL E a (γ' x))]
  intro F hF
  exact hS hF

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperatorStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decaysAtShortRationalVectors_rapidKernelOperator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.ShortVecDecay.Decays F → GlobalTheory.ShortVecDecay.Decays (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  first | exact @GlobalTheory.RapidKernelDecay.decays_integral | exact GlobalTheory.RapidKernelDecay.decays_integral | (intros; apply GlobalTheory.RapidKernelDecay.decays_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.ReadExist

theorem exists_algCl {p : ℕ} [Fact p.Prime] {z : ℂ_[p]} (hz : IsAlgebraic ℚ_[p] z) :
    ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = z := by
  have h1 : IsIntegral (PadicAlgCl p) z := (hz.tower_top (PadicAlgCl p)).isIntegral
  have h2 : (minpoly (PadicAlgCl p) z).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible h1)
  exact minpoly.mem_range_of_degree_eq_one _ _ h2

theorem exists_factor_algCl {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) :
    ∃ b : F →+* PadicAlgCl p, ∀ x, algebraMap (PadicAlgCl p) ℂ_[p] (b x) = φ x := by
  have hex : ∀ x : F, ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = φ x := fun x => by
    apply exists_algCl
    have h1 : IsAlgebraic ℚ (φ x) := by
      have := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom
      simpa using this
    exact h1.tower_top ℚ_[p]
  choose f hf using hex
  have hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p]) :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_mul, hf, hf, hf]; exact map_mul φ x y
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_add, hf, hf, hf]; exact map_add φ x y

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_inv {x : K} (hx : x ≠ 0) : vV V x⁻¹ = - vV V x := by
  have h := vV_mul (V := V) hx (inv_ne_zero hx)
  have h1 : vV V (1 : K) = 0 := by simp [vV]
  rw [mul_inv_cancel₀ hx, h1] at h
  omega

theorem norm_lt_one_iff_vV_pos {C : Type} [NormedField C] (c : K →+* C)
    (hn : ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V K)) {y : K} (hy : y ≠ 0) :
    ‖c y‖ < 1 ↔ 0 < vV V y := by
  have key : ∀ x, ‖c x‖ ≤ 1 ↔ 0 ≤ vV V x := fun x =>
    (hn x).trans (Set.mem_range.trans (GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff (V := V) x))
  have h0 : 0 < ‖c y‖ := norm_pos_iff.2 ((map_ne_zero c).2 hy)
  have hi := key y⁻¹
  rw [map_inv₀, norm_inv, vV_inv hy, inv_le_one₀ h0] at hi
  constructor
  · intro h
    by_contra h'
    have := hi.2 (by omega)
    linarith
  · intro h
    by_contra h'
    have := hi.1 (not_lt.1 h')
    omega

end Val

theorem mem_iff_vLa_pos {F : Type} [Field F] [NumberField F] (la : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F)
    (hx : (x : F) ≠ 0) : x ∈ la.asIdeal ↔ 0 < vLa la (x : F) := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  have h0 : la.valuation F (x : F) ≠ 0 := (la.valuation F).ne_zero_iff.2 hx
  have e := WithZero.log_lt_log h0 one_ne_zero
  rw [WithZero.log_one] at e
  change _ ↔ 0 < -WithZero.log (la.valuation F (x : F))
  rw [← e]
  omega

theorem exists_isReading : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p])
    (T : CDVR) (io : F →+* T.Fr) (e : ℕ), OverLa (placeAt φ) T.V io e → T.FinRes →
    ∃ k : T.Fr →+* ℂ_[p], IsReading φ T io k := by
  intro p _ F _ _ φ T io e ho hT
  obtain ⟨q, hq, c, hn⟩ := GlobalTheory.DegenerateTest.exists_padic_embedding T.V hT

  have ha : ∀ x : 𝓞 F, ‖c (io (x : F))‖ < 1 ↔ x ∈ (placeAt φ).asIdeal := by
    intro x
    by_cases hx : (x : F) = 0
    · have hx' : x = 0 := by exact_mod_cast hx
      subst hx'
      simp
    rw [norm_lt_one_iff_vV_pos c hn ((map_ne_zero io).2 hx), ho.2, mem_iff_vLa_pos _ x hx]
    constructor
    · intro h
      exact pos_of_mul_pos_right h (by positivity)
    · intro h
      exact mul_pos (by exact_mod_cast ho.1) h

  have hqp : q = p := by
    have h1 := (ha (p : 𝓞 F)).2 (natCast_mem_placeAt φ)
    have e1 : c (io (((p : ℕ) : 𝓞 F) : F)) = algebraMap ℚ_[q] (PadicAlgCl q) (p : ℚ_[q]) := by simp
    rw [e1, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
    exact (Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).1 h1
  subst hqp
  obtain ⟨b, hb⟩ := exists_factor_algCl φ
  have hbn : ∀ x, ‖b x‖ = ‖φ x‖ := fun x => by
    rw [← hb, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  obtain ⟨g, hg⟩ := GlobalTheory.EmbThroughCompletion.exists_conj (c.comp io) b
    (GlobalTheory.EmbThroughCompletion.norm_lt_one_iff (placeAt φ) _ _ ha
      (fun x => by rw [hbn]; exact (mem_placeAt φ x).symm))
  refine ⟨(algebraMap (PadicAlgCl q) ℂ_[q]).comp ((g : PadicAlgCl q →+* PadicAlgCl q).comp c), ?_, ?_⟩
  · intro a
    simp only [RingHom.comp_apply]
    have := hg a
    simp only [RingHom.comp_apply] at this
    rw [RingHom.coe_coe, this, hb]
  · intro x
    simp only [RingHom.comp_apply]
    rw [← PadicComplex.coe_eq, PadicComplex.norm_extends, RingHom.coe_coe, ← PadicAlgCl.spectralNorm_eq,
      ← spectralNorm_eq_of_equiv g, PadicAlgCl.spectralNorm_eq, hn]
    rfl

end GlobalTheory.GeoTie.ReadExist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsFundamentalDomainRationalUpperUnitrianguStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isFundamentalDomain_rationalUpperUnitriangular : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (μ : Measure (GA E a)),
    ∃ 𝓕₀ : Set (GA E a), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ := by
  first | exact @GlobalTheory.CellDec.exists_isFundamentalDomain_NE | exact GlobalTheory.CellDec.exists_isFundamentalDomain_NE | (intros; apply GlobalTheory.CellDec.exists_isFundamentalDomain_NE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperatorStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_realChart_rapidKernelOperator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ∃ L : Lie E a →L[ℝ] ℂ, HasFDerivAt (chart (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) g) L (toL y.val) ∧ ∀ Z : Lie E a, L Z = ∫ x, k x * lieD (toL (((γ x)⁻¹).val * ((y⁻¹).val * Matrix.of Z) * (γ x).val)) G (g * infGL E a (y * γ x)) ∂ν := by
  first | exact @GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel | exact GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel | (intros; apply GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel <;> assumption)
end

