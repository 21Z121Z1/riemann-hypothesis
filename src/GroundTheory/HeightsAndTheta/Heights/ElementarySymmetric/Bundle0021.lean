import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartBergmanBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralOfBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensIntegrable
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.UpdateEraseSubset
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GraphEquiv
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DoubleSumEqZero
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DegreeOneCellEqChartUpdate
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0076
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.ArithNMInhabitants
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace NMPointZero

def line : Geo.HermLine (blockIdx fun _ : Unit ↦ 0) where
  a := 0
  h _ := 2
  pos _ _ := two_pos
  smul c z hc := by simp

theorem isSemipositiveRel (P0 P : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) :
    Geo.IsSemipositiveRel P0 P line := by
  refine ⟨contDiffOn_const, fun z _ w _ => ?_⟩
  simp [line, Geo.leviForm]

theorem isAmpleOnModel : IsAmpleOnModel (ι := blockIdx fun _ : Unit ↦ 0) unitPoint line.a := by
  intro e
  refine ⟨0, fun n _ => ⟨1, fun _ => 1, fun _ c _ => ?_, fun c _ => ⟨fun _ => 1, fun _ => one_mem _, ?_⟩⟩⟩
  · simp [unitPoint]
  · simp [unitPoint]

theorem isBoundedH_one :
    IsBoundedH (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) unitPoint
      (GroundTheory.Heights₂.Heights.Inter.hermZpow line ((1 : ℕ) : ℤ)) 1 (1 / 2) 1 := by
  intro dg dh g h z hg hh hd he _
  have hdd : dg = dh := by
    funext k
    have h1 := hd k
    simp [GroundTheory.Heights₂.Heights.Inter.hermZpow, line] at h1
    exact_mod_cast h1
  subst hdd
  have hgh : g - h = 0 := by
    refine form_eq_zero_of_unitPoint (δ := dg) ?_ ?_
    · exact ((geoMultiHomog_iff g dg).mp hg).sub ((geoMultiHomog_iff h dg).mp hh)
    · rw [map_sub, he, one_mul, sub_self]
  rw [sub_eq_zero.mp hgh]
  simp [GroundTheory.Heights₂.Heights.Inter.hermZpow, line]
  linarith [norm_nonneg (eval z (map (Int.castRingHom ℂ) h))]

def oneSystem : Geo.IntersectionSystem := fun _ _ _ _ _ _ _ => 1

end NMPointZero

theorem ArithNMLift.hyps_inhabited :
    Geo.IsArithVar (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) (0 + 1) ∧
      (⊥ : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) ≤ Geo.mCoordIdeal unitPoint ∧
      Geo.IsSemipositiveRel ⊥ (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) NMPointZero.line ∧
      Geo.IsConjInvariantH NMPointZero.line ∧
      IsAmpleOnModel (ι := blockIdx fun _ : Unit ↦ 0) unitPoint NMPointZero.line.a ∧
      (∃ m : ℕ, 1 ≤ m ∧ ∃ s ∈ Geo.chartLat (ι := blockIdx fun _ : Unit ↦ 0) unitPoint
          (GroundTheory.Heights₂.Heights.Inter.hermZpow NMPointZero.line m).a 1, s ≠ 0 ∧
        ∃ c : ℝ, c < 1 ∧ IsBoundedH (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) unitPoint
          (GroundTheory.Heights₂.Heights.Inter.hermZpow NMPointZero.line m) 1 c s) ∧
      (∀ (W : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) (e : ℕ), Geo.IsArithVar W (e + 1) →
        Geo.mCoordIdeal unitPoint ≤ W → e < 0 →
        ∀ (Ω' : Type) [Field Ω'] (y' : (Σ k, (blockIdx fun _ : Unit ↦ 0) k) → Ω'),
          Geo.mCoordIdeal y' = W → IsGenBySmallSections y' NMPointZero.line) := by
  refine ⟨unitPoint_isArithVar, bot_le, NMPointZero.isSemipositiveRel _ _, fun _ => rfl, NMPointZero.isAmpleOnModel,
    ⟨1, le_rfl, 1, fun c _ => ?_, one_ne_zero, 1 / 2, by norm_num, NMPointZero.isBoundedH_one⟩,
    fun _ e _ _ he => absurd he (Nat.not_lt_zero e)⟩
  simp [unitPoint]

theorem ArithNMSmallSection.hyps_inhabited :
    Geo.IsArithVar (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) (0 + 1) ∧
      (⊥ : Ideal (Geo.MRing (blockIdx fun _ : Unit ↦ 0))) ≤ Geo.mCoordIdeal unitPoint ∧
      Geo.IsSemipositiveRel ⊥ (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint) NMPointZero.line ∧
      Geo.IsConjInvariantH NMPointZero.line ∧
      IsAmpleOnModel (ι := blockIdx fun _ : Unit ↦ 0) unitPoint NMPointZero.line.a ∧
      0 < NMPointZero.oneSystem Unit (blockIdx fun _ : Unit ↦ 0)
        (Geo.mCoordIdeal unitPoint) (0 + 1) (fun _ => NMPointZero.line) :=
  ⟨unitPoint_isArithVar, bot_le, NMPointZero.isSemipositiveRel _ _, fun _ => rfl, NMPointZero.isAmpleOnModel,
    one_pos⟩

theorem AmpleOnModelRestrict.hyps_inhabited :
    Geo.mCoordIdeal (ι := ArakelovGeometry.GlobalTheory (Fin 2)) ProjLine.y ≤ Geo.mCoordIdeal (ι := ArakelovGeometry.GlobalTheory (Fin 2)) (fun _ => (1 : ℚ)) ∧
      IsAmpleOnModel (ι := ArakelovGeometry.GlobalTheory (Fin 2)) ProjLine.y ProjLine.fsLine1.a :=
  ⟨by rw [ProjLine.mCoordIdeal_y]; exact bot_le, isAmpleOnModel_projLine⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.BergmanLerpSelf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

lemma bergman_lerp_self {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (t : ℝ) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) :
    bergman (W.lerp W t) dV V n x = bergman W dV V n x := by
  simp only [bergman, sectionL2NormSq, ptNormSq, lerp_self_φ]

lemma bergman_nonneg {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) : 0 ≤ bergman W dV V n x :=
  Real.iSup_nonneg fun _ => div_nonneg (ptNormSq_nonneg W n _ x) (sectionL2NormSq_nonneg W dV n _)

theorem BergmanL1Convergence.proof (hL1 : L1Convergence.Statement)
    (hLoc : LocalBergmanBound.Statement) (hUnif : UniformBergmanBound.Statement)
    (hInt : IntegralOfBergman.Statement) (hBI : BergmanIntegrable.Statement)
    (hDI : BergmanDensIntegrable.Statement) : BergmanL1Convergence.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV hdim
  have := dV.isProb
  obtain ⟨C, hC⟩ := hUnif A L W W dV hW hW
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ D := fun n => by positivity
  set g : ℕ → X → ℝ := fun n x =>
    (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x with hg
  have hbound : ∀ n x, 0 ≤ g n x ∧ g n x ≤ C := fun n x => by
    refine ⟨mul_nonneg (inv_nonneg.2 (hpos n).le) (bergman_nonneg _ _ _ _ _), ?_⟩
    have h := hC (n + 1) (by omega) 0 ⟨le_rfl, zero_le_one⟩ (V (n + 1)) (hV _) x
    rw [bergman_lerp_self] at h
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ C
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm C (((n + 1 : ℕ) : ℝ) ^ D)]
  have hlim : ∀ (x : X) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ bergmanDens W dV x + ε := by
    intro x ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hLoc A L W dV hW V hV x ε hε)
    filter_upwards [h] with n hn
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ _
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm (bergmanDens W dV x + ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hmass : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∫ x, bergmanDens W dV x ∂dV.μ - ε ≤ ∫ x, g n x ∂dV.μ := by
    intro ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hdim ε hε)
    filter_upwards [h] with n hn
    have hI : ∫ x, g n x ∂dV.μ =
        (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * Module.finrank ℂ (V (n + 1)) := by
      rw [hg, integral_const_mul, hInt A L W dV (n + 1) (V (n + 1)) (hV _)]
    rw [hI, le_inv_mul_iff₀ (hpos n)]
    linarith [mul_comm (∫ x, bergmanDens W dV x ∂dV.μ - ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hgi : ∀ n, Integrable (g n) dV.μ := fun n =>
    (hBI A L W dV (n + 1) (V (n + 1)) (hV _)).const_mul _
  have h := hL1 dV.μ g (bergmanDens W dV) C hgi (hDI A L W dV) hbound hlim hmass
  exact (tendsto_add_atTop_iff_nat 1).1 h

theorem BergmanL1Convergence.full : BergmanL1Convergence.Statement :=
  BergmanL1Convergence.proof L1Convergence.proof
    (LocalBergmanBound.proof (ChartBergmanBound.proof PolydiscSubmean.proof ComplexTaylorTwo.proof))
    (UniformBergmanBound.proof PolydiscSubmean.proof ChartTaylorCover.proof)
    IntegralOfBergman.proof BergmanIntegrable.proof BergmanDensIntegrable.proof

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDoubleCechX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem DoubleCech.proof : GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DoubleCech.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DoubleCech.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq.proof

end GroundTheory.Heights₂.Heights.Swarm
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGeneratedCechTieX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cechD locPart cechCc cechZc mIdealOver chartRingOver quotPart
  secOver GeneratedV)

noncomputable section

namespace GeneratedCechTie

open HZeroRowPlaceData

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω}

theorem evMap_mul {I : ∀ k, Finset (ι k)} (hI : Good y I)
    (x x' : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) :
    evMap y I (x * x') = evMap y I x * evMap y I x' := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction x' using LocalizedModule.induction_on with
    | h m' t' =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
      obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective m'
      rw [LocalizedModule.mk_mul_mk, ← map_mul, evMap_mk y hI, evMap_mk y hI, evMap_mk y hI,
        Submonoid.coe_mul, map_mul, map_mul, mul_div_mul_comm]

theorem evMap_one {I : ∀ k, Finset (ι k)} (hI : Good y I) :
    evMap y I (1 : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) = 1 := by
  have h1 : (1 : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) =
      LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) 1) 1 := by
    rw [map_one, ← pow_zero (LocalizedModule.mk (1 : MRingOver S ι ⧸ mIdealOver S y) (1 : cellMon S I)),
      LocalizedModule.mk_pow, one_pow, one_pow]
  rw [h1, evMap_mk y hI]
  simp

theorem one_mem_locPart (T : Submonoid (MRingOver S ι)) :
    (1 : LocalizedModule T (MRingOver S ι ⧸ mIdealOver S y)) ∈
      locPart ι (quotPart S (mIdealOver S y)) T 0 := by
  have h1 : (1 : LocalizedModule T (MRingOver S ι ⧸ mIdealOver S y)) =
      LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) 1) 1 := by
    rw [map_one, ← pow_zero (LocalizedModule.mk (1 : MRingOver S ι ⧸ mIdealOver S y) (1 : T)),
      LocalizedModule.mk_pow, one_pow, one_pow]
  rw [h1]
  refine GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.mk_mem_locPart _ 1 0
    (GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.isMultiHomog_one _ fun _ => rfl) ?_
  refine Submodule.subset_span ⟨1, ⟨fun k => by simp, ?_⟩, rfl⟩
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.isMultiHomog_one _ fun k => by simp

theorem exists_cocycle {n : K → ℤ} {s : Ω} (hs : s ∈ secOver S y n) :
    ∃ z ∈ cechZc ι (quotPart S (mIdealOver S y)) n 0,
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → evMap y (chart c) (z (cell0 c)) = s := by
  have hs' : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver S y c := by
    intro c hc
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs c) hc
  have hlift : ∀ I : Cell K ι 0, Good y I.1 → ∃ w ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n,
      evMap y I.1 w = s := fun I hI =>
    exists_lift hI (fun k => Finset.min'_mem _ (I.2.1 k)) n
      (hs' _ fun k => hI k _ (Finset.min'_mem _ (I.2.1 k)))
  classical
  let z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0 := fun I =>
    if hI : Good y I.1 then (hlift I hI).choose else 0
  have hzC : ∀ I : Cell K ι 0, z I ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n := by
    intro I
    by_cases hI : Good y I.1
    · simp only [z, dif_pos hI]; exact (hlift I hI).choose_spec.1
    · simp only [z, dif_neg hI]; exact Submodule.zero_mem _
  have hzv : ∀ I : Cell K ι 0, Good y I.1 → evMap y I.1 (z I) = s := by
    intro I hI
    simp only [z, dif_pos hI]
    exact (hlift I hI).choose_spec.2
  have hzCc : z ∈ cechCc ι (quotPart S (mIdealOver S y)) n 0 :=
    Submodule.mem_pi.mpr fun I _ => hzC I
  have hzD : cechD S ι _ 0 z = 0 := by
    funext J
    by_cases hJ : Good y J.1
    · refine evMap_injOn y hJ n (cechD_mem_locPart n 0 hzCc J) (Submodule.zero_mem _) ?_
      have hconst : constD K ι Ω 0 (fun I => evMap y I.1 (z I)) J = constD K ι Ω 0 (fun _ => s) J :=
        CechPointVanish.constD_congr J.1 0 (fun I hIJ => hzv I fun k i hi => hJ k i (hIJ k hi)) J
          fun k => subset_refl _
      rw [evMap_cechD z J hJ, hconst, constD_const, Pi.zero_apply, map_zero]
    · unfold Good at hJ
      push Not at hJ
      obtain ⟨k, i, hi, hy0⟩ := hJ
      have := subsingleton_of_bad (S := S) hi hy0
      exact @Subsingleton.elim _ this _ _
  exact ⟨z, Submodule.mem_inf.mpr ⟨hzCc, hzD⟩, fun c hc => hzv (cell0 c) (good_chart hc)⟩

end GeneratedCechTie

open GeneratedCechTie HZeroRowPlaceData in

theorem GeneratedCechTie.proof : GeneratedCechTie.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y β _ hgen I
  obtain ⟨n, s, hs, hgen⟩ := hgen
  obtain ⟨c, rfl⟩ := degree_zero_cell_eq_chart I
  by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
  · choose z hz hzv using fun j => exists_cocycle (hs j)
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    have hcI : ∀ k, c k ∈ chart c k := fun k => Finset.mem_singleton_self _
    have hval : ∀ j, u j * (∏ k, y ⟨k, c k⟩ ^ (-β k)) * ∏ k, y ⟨k, c k⟩ ^ (-(-β) k) = u j := by
      intro j
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp only [Pi.neg_apply, neg_neg]
      rw [Finset.prod_congr rfl fun k _ => zpow_neg_mul_zpow_self (β k) (hc k), Finset.prod_const_one,
        mul_one]
    choose U hU hUv using fun j => exists_lift (good_chart hc) hcI (-β)
      (s := u j * ∏ k, y ⟨k, c k⟩ ^ (-β k)) (by rw [hval j]; exact hu j)
    refine ⟨n, z, U, hz, hU, ?_⟩
    let Z : Fin n → LocalizedModule (cellMon S (chart c)) (MRingOver S ι ⧸ mIdealOver S y) := fun j => z j (cell0 c)
    show ∑ j, U j * Z j = 1
    have hmem : ∑ j, U j * Z j ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S (chart c)) 0 := by
      refine Submodule.sum_mem _ fun j _ => ?_
      have h := GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.locPart_mul (hU j)
        (Submodule.mem_pi.mp (Submodule.mem_inf.mp (hz j)).1 (cell0 c) (Set.mem_univ _))
      rwa [neg_add_cancel] at h
    refine evMap_injOn y (good_chart hc) 0 hmem (one_mem_locPart _) ?_
    rw [evMap_one (good_chart hc), map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evMap_mul (good_chart hc), hUv j, show evMap y (chart c) (Z j) = s j from hzv j c hc]
    ring
  · push Not at hc
    obtain ⟨k, hk⟩ := hc
    have := subsingleton_of_bad (S := S) (I := chart c) (Finset.mem_singleton_self (c k)) hk
    exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, @Subsingleton.elim _ this _ _⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGeneratedNefFX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem GeneratedNefF.proof : GeneratedNefF.Statement := by
  intro F _ K _ _ ι _ _ I V a hI hgen W hW hVW
  have hgW : KH.GeneratedV F W a := GeneratedRestrict.proof F K ι V W a hVW hgen
  exact GeneratedProductNonneg.proof GeneratedRestrict.proof GeneratedEffectiveSection.proof
    F K ι I W 1 ![a] hI hW (Fin.forall_fin_one.mpr hgW)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PZCombLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem ZCombLimit.proof : GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedHilbertPolynomial.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial.proof))

end GroundTheory.Heights₂.Heights.Swarm
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsFlZArithVar
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

def FlZArithVar.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    IsArithVar (IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZIdeal Ψ N) (IndefiniteRowSideFullHecke.LowerBoundFree.Nine.dimFl Ψ N + 1)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsFlZIdealEqCoord
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def flZIncr (Ψ : Type) (N : ℕ) :
    (Σ q : Ψ × Fin (N - 1), IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZBlk Ψ N q) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨p.1, ⟨p.2.1.orderEmbOfFin p.2.2, (p.2.1.orderEmbOfFin p.2.2).strictMono⟩⟩

def FlZIdealEqCoord.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ),
    IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZIdeal Ψ N = mCoordIdeal (fun p => yFl Ψ N (flZIncr Ψ N p))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

