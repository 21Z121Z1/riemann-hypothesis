import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0596
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0473
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqStdPowerSeriesAtZero
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscPeriodBasisIsUnit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem breuilKisinDatumRadius_pos_and_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by
    have := bk.deg_pos
    positivity
  refine ⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_neg_of_pos he)

theorem wseed_Z_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ)
    (S' : Matrix (Fin d) (Fin d) (Ainf l)),
    Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) →
    (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  intro l _ K bk τ hτ d ρ _ s Y Z k S' hYS hW
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatumRadius_pos_and_lt_one bk
  have hu : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hu
  have hj0 : IsDiscMap bk.ev j0 := isDiscMap_map bk.ev hu
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨cD, hcD1, hcD2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (2 * s.N * d)

  set δ := Z.det with hδ
  have hdet : j0 δ * (s.W.det * bk.iA S'.det) =
      bk.iA (bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d)) := by
    have h1 := congrArg (fun M => bk.iA M.det) hYS
    simp only [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at h1
    have h2 : bk.iA Y.det = s.W.det * j0 δ := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hW j0 hj0, det_mul, hδ, RingHom.map_det,
        RingHom.mapMatrix_apply]
    rw [map_mul, h2] at h1
    have e : bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d) = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) ^ d := by
      rw [map_pow, map_natCast]; ring
    rw [e, ← h1]
    ring
  have hdvd : ∀ i, δ ∣ toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
    intro i
    have h3 := congrArg (cD i) hdet
    rw [hcD2, hcD1, TB.c_mul, map_mul (toDisc l (X : bk.S) bk.ρ₀)] at h3
    have hunit : IsUnit (toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (k * d))) := by
      rw [map_pow, map_natCast]; exact (isUnit_l_disc l _ _).pow _
    exact (hunit.dvd_mul_left).1 ⟨_, h3.symm⟩
  have hle : Ideal.span (Set.range fun i => TB.c i (τ ^ (2 * s.N * d))) ≤
      (Ideal.span {δ}).comap (toDisc l (X : bk.S) bk.ρ₀) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.2 (hdvd i)
  have hl := Ideal.mem_span_singleton.1 (hle hr)
  rw [map_pow, map_natCast] at hl
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_dvd_unit hl ((isUnit_l_disc l _ _).pow _)

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverage
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem setIntegral_eq_mass_mul_avg : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Per Γ Φ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ((μ 𝓕).toReal : ℂ) * avg Γ Φ := by
  intro G _ _ _ _ _ _ Γ hΓ mG hB μ 𝓕 hμ h𝓕 Φ hΦ
  obtain ⟨hd, K, hK, hcov⟩ := hΓ
  have e := hB.measurable_eq
  subst e
  letI : MeasurableSpace G := borel G
  haveI : Countable Γ := countable_of_discrete_addSubgroup Γ
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ h𝓕).ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.1.continuousOn
  have hb : ∀ x, ‖Φ x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    have := hC _ hk
    rwa [hΦ.2 γ hγ] at this
  have hint : IntegrableOn Φ 𝓕 μ :=
    Measure.integrableOn_of_bounded hfin hΦ.1.aestronglyMeasurable (M := C) (Filter.Eventually.of_forall hb)
  refine ⟨hne, hfin, hint, ?_⟩
  have hex := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov).1
  have hex' : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ₀, F₀, h⟩ := hex
    exact ⟨(μ₀, F₀), h⟩
  have hav : avg Γ Φ = ∫ x in hex'.choose.2, Φ x ∂hex'.choose.1 := by
    simp only [avg]
    rw [dif_pos hex']
  rw [hav]
  obtain ⟨hμ₀, hF₀, h1⟩ := hex'.choose_spec
  generalize hex'.choose = p at hμ₀ hF₀ h1 ⊢
  obtain ⟨μ₀, F₀⟩ := p
  simp only at hμ₀ hF₀ h1 ⊢
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul μ μ₀⟩
  have hac : μ ≪ μ₀ := hc ▸ Measure.smul_absolutelyContinuous
  have hF₀' : IsAddFundamentalDomain Γ F₀ μ := hF₀.mono hac
  have e1 : μ 𝓕 = μ F₀ := h𝓕.measure_eq hF₀'
  have e2 : ∫ x in 𝓕, Φ x ∂μ = ∫ x in F₀, Φ x ∂μ :=
    h𝓕.setIntegral_eq hF₀' fun g x => hΦ.2 g g.2 x
  rw [e1, e2, hc, Measure.restrict_smul, integral_smul_nnreal_measure, Measure.smul_apply, h1]
  simp [ENNReal.smul_def, NNReal.smul_def]

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOrthogonalityHolds
section
namespace GlobalTheory

theorem unramifiedOrthogonality_holds : ReciprocityTheory.Gal.UnramifiedOrthogonality :=
  GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTameStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_mem_filtration_zero_tame : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → ∃ b₁, IsCrisVal t ϖ D.toPhiMod R.jB m₀ b₁ ∧ ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b₁ - b₁ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.value_mem_filtration_zero | exact GlobalTheory.BKGal.value_mem_filtration_zero | (intros; apply GlobalTheory.BKGal.value_mem_filtration_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachIntegralComplexCocycleClassFinite
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.IntComplex

set_option maxHeartbeats 1000000 in

theorem ring_part (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) :
    let W := (HW l).W K s LL h
    (∃ w, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X}) ∧ ∃ b, W.X = letπ * b := by
  intro W
  obtain ⟨χ, -, -, hγ, hX, hQ, -, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  have hs : 1 ≤ s := h.1
  obtain ⟨-, -, -, -, -, hact, -⟩ := GlobalTheory.Cyc.XX_QQ_properties l ↥(OL LL) s hs
  obtain ⟨-, b, hb⟩ := hact (χ W.gam)
  refine ⟨⟨1 + W.X * fun _ => b, ?_, ?_⟩, ?_⟩
  · funext i
    change W.γ₀ W.gam (W.Q i) = (1 + W.X i * b) * W.Q i
    rw [hγ, hX, hQ, hb, mul_comm]
  · rw [add_sub_cancel_left]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  · obtain ⟨c, hc⟩ : (PowerSeries.X : PowerSeries ↥(OL LL)) ∣ GlobalTheory.Cyc.XX l ↥(OL LL) s := by
      rw [PowerSeries.X_dvd_iff, GlobalTheory.Cyc.XX]
      simp
    refine ⟨fun _ => c, ?_⟩
    funext i
    change W.X i = PowerSeries.X * c
    rw [hX, hc]

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2c D HW F := by
  intro D HW F l _ K s LL h T M hh hT _
  obtain ⟨h1, b, hb⟩ := ring_part D HW l K s LL h
  refine ⟨h1, fun y z hy hz hc => ?_⟩
  have hz' : z ∈ aN ((HW l).W K s LL h) T letπ := by
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨b • x, Submodule.smul_mem _ b hx, ?_⟩
    simp only [smulA, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hb, mul_smul]
  refine ⟨?_, fun h0 => ?_⟩
  · refine GlobalTheory.T.herrCocycle_poles_frobeniusQ_crystalline D HW F l K s LL h T hT (Multiset.replicate (mx M) 0) y z ?_ hz' hc
    rw [Multiset.map_replicate, Multiset.prod_replicate, pow_zero]
    exact hy
  · obtain ⟨m, hm⟩ := ((GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F l K s LL h T hT).1.2 ⟨(y, z), hc⟩).1 h0
    have hm1 : y = ((HW l).W K s LL h).φD T m - m := congrArg Prod.fst hm
    have hm2 : z = ((HW l).W K s LL h).γ T m - m := congrArg Prod.snd hm
    refine ⟨m, GlobalTheory.T.mem_wach_of_frobenius_gamma D HW F l K s LL h T hT (mx M) m ?_ ?_, hm1, hm2⟩
    · exact hm1 ▸ hy
    · exact hm2 ▸ hz'

end GlobalTheory.NL.IntComplex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqStdPowerSeriesAtZeroStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_eq_std_powerSeries_at_zero : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ i : Let K, Std (Di (HW l) h T i) (Lat C h T i 1) := by
  first | exact @GlobalTheory.NL.AtZero.lat_one_std | exact GlobalTheory.NL.AtZero.lat_one_std | (intros; apply GlobalTheory.NL.AtZero.lat_one_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section Entries

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_block_entry {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i j : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) x i j =
      if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (j : ℕ) ≤ m then x ⟨(i, j), h⟩ else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro t _ ht
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact ht (Subtype.ext (Prod.ext e1 e2))
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    have := t.2
    rw [← e1, ← e2]
    exact this

theorem posM_col_mul {n : ℕ} (x : UnipotentBlockColumnIndex a n n → R) (M : Matrix (Fin a) (Fin a) R)
    (h : ∀ k : Fin a, (k : ℕ) = n → ∀ j, M k j = (1 : Matrix (Fin a) (Fin a) R) k j) :
    posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) x * M = posM Subtype.val x := by
  simp only [posM, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht : ((t.1.2 : Fin a) : ℕ) = n := by have := t.2; omega
  ext i j
  by_cases hi : i = t.1.1
  · subst hi
    rw [Matrix.single_mul_apply_same, h _ ht, Matrix.one_apply, Matrix.single_apply]
    by_cases hj : t.1.2 = j <;> simp [hj]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi, Matrix.single_apply, if_neg]
    rintro ⟨e1, _⟩
    exact hi e1.symm

theorem sum_posM_col {n : ℕ} (x : UnipotentBlockColumnIndex a n n → R) :
    (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) x p.1 p.2) =
      ∑ t : UnipotentBlockColumnIndex a n n, if (t.1.1 : ℕ) + 1 = n then x t else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht : ((t.1.2 : Fin a) : ℕ) = n := by have := t.2; omega
  by_cases h : (t.1.1 : ℕ) + 1 = n
  · rw [if_pos h, Finset.sum_eq_single t.1]
    · simp
    · intro p _ hp
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact hp (Prod.ext e1.symm e2.symm)
    · intro hp
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩) hp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp2 := (Finset.mem_filter.1 hp).2
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    rw [e1, ← ht, e2]
    exact hp2.symm

end Entries

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem whittakerLaw_upperUnipotent_identityColumns (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g) (n : ℕ) :
    ∀ u : GL (Fin a) (Ad E), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) →
      (∀ i j : Fin a, n ≤ (j : ℕ) → i ≠ j → u.val i j = 0) →
      ∀ g : GA E a, f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g := by
  induction n with
  | zero =>
    intro u _ hd hc g
    have hu : u = 1 := by
      apply Units.ext
      ext i j
      by_cases h : i = j
      · subst h; simp [hd]
      · simp [hc i j (Nat.zero_le _) h, h]
    subst hu
    have hs : (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (1 : GL (Fin a) (Ad E)).val p.1 p.2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp2 := (Finset.mem_filter.1 hp).2
      have : p.1 ≠ p.2 := fun e => by rw [e] at hp2; omega
      simp [this]
    rw [hs, AddChar.map_zero_eq_one, one_mul, one_mul]
  | succ n ih =>
    intro u ht hd hc g
    by_cases hn : n = 0
    · subst hn
      refine ih u ht hd (fun i j _ hij => ?_) g
      rcases lt_or_gt_of_ne hij with h | h
      · exact hc i j (by have : (i : ℕ) < j := h; omega) hij
      · exact ht i j h
    set y : UnipotentBlockColumnIndex a n n → Ad E := fun t => u.val t.1.1 t.1.2 with hy
    have hrow : ∀ k : Fin a, (k : ℕ) = n → ∀ j, u.val k j = (1 : Matrix (Fin a) (Fin a) (Ad E)) k j := by
      intro k hk j
      by_cases h : k = j
      · subst h; simp [hd]
      · rw [Matrix.one_apply, if_neg h]
        rcases lt_or_gt_of_ne h with h' | h'
        · exact hc k j (by have : (k : ℕ) < j := h'; omega) h
        · exact ht k j h'
    have hval : ∀ i j, ((blkU y)⁻¹ * u).val i j = u.val i j - posM Subtype.val y i j := by
      intro i j
      have e : ((blkU y)⁻¹ * u).val = (1 - posM Subtype.val y) * u.val := rfl
      rw [e, sub_mul, one_mul, posM_col_mul y _ hrow, Matrix.sub_apply]
    have hz : ∀ i j : Fin a, ¬ ((i : ℕ) < n ∧ (j : ℕ) = n) → posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) y i j = 0 := by
      intro i j h
      rw [posM_block_entry, dif_neg]
      rintro ⟨h1, h2, h3⟩
      exact h ⟨h1, by omega⟩
    have e1 := ih ((blkU y)⁻¹ * u) ?_ ?_ ?_ g
    · have e2 : u * g = blkU y * (((blkU y)⁻¹ * u) * g) := by group
      rw [e2, hf n (by omega), e1, ← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [hval, Finset.sum_sub_distrib, sum_posM_col, dot, eLast]
      have hd2 : (∑ t : UnipotentBlockColumnIndex a n n, algebraMap E (Ad E) (if (t.1.1 : ℕ) + 1 = n then 1 else 0) * y t) =
          ∑ t : UnipotentBlockColumnIndex a n n, if (t.1.1 : ℕ) + 1 = n then y t else 0 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs <;> simp
      rw [hd2, add_sub_cancel]
    · intro i j hji
      rw [hval, ht i j hji, hz i j, sub_zero]
      rintro ⟨h1, h2⟩
      have : (j : ℕ) < i := hji
      omega
    · intro j
      rw [hval, hd, hz j j, sub_zero]
      rintro ⟨h1, h2⟩
      omega
    · intro i j hj hij
      rw [hval]
      by_cases hjn : (j : ℕ) = n
      · by_cases hin : (i : ℕ) < n
        · rw [posM_block_entry, dif_pos ⟨hin, by omega, by omega⟩, sub_eq_zero]
        · rw [hz i j (fun h => hin h.1), sub_zero]
          exact ht i j (by
            have : (j : ℕ) < i := by
              have : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
              omega
            exact this)
      · rw [hc i j (by omega) hij, hz i j (fun h => hjn h.2), sub_zero]

theorem tri_law (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g)
    (u : GL (Fin a) (Ad E)) (ht : ∀ i j : Fin a, j < i → u.val i j = 0) (hd : ∀ j : Fin a, u.val j j = 1) (g : GA E a) :
    f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g :=
  whittakerLaw_upperUnipotent_identityColumns ψ f hf a u ht hd (fun _ j h => absurd j.2 (by omega)) g

end GlobalTheory.CuspGeneric
end
end

