import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsCommonNaturalRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0144
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmEmbeddingsEqOneOfInert
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSkewHermitianLiftModUniformizer
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.SkewLift

open GlobalTheory.Hk3.CayleyPhase GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L]

theorem cT_cT (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {a b : Type} (M : Matrix a b L) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_mul_rect (σ : L →+* L) {a b c : Type} [Fintype b] (M : Matrix a b L) (N : Matrix b c L) :
    Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT, Matrix.mul_apply, map_sum, mul_comm]

theorem isIntM_sub' [Valued L (WithZero (Multiplicative ℤ))] {a b : Type} {M N : Matrix a b L} (hM : IsIntM M) (hN : IsIntM N) : IsIntM (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem skew_lift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z w a : ι → Fin n' → L),
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, w i r ∈ Formalism.UG.intL L) → (∀ i r, a i r ∈ Formalism.UG.intL L) →
    (∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (w j) +
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (w i) (z j))) →
    ∃ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) ∧ (∀ r s, C r s ∈ Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((C *ᵥ z i) r - ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w i) r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT herm ι _ _ z w a hz hw ha hdual hcong
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσσ := hU.1
  have hσv := hU.2.1
  have hhalf : (2 : L)⁻¹ ∈ Formalism.UG.intL L := by
    show Valued.v ((2 : L)⁻¹) ≤ 1
    rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJI : IsIntM J := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT
  have hcJ : Formalism.UG.cT σ J = J := cT_herm σ herm
  let B : Matrix (Fin n') ι L := fun r i => (J *ᵥ w i) r
  let Z : Matrix (Fin n') ι L := fun r j => z j r
  let A : Matrix ι (Fin n') L := fun i r => a i r
  let P : Matrix ι ι L := Formalism.UG.cT σ B * Z
  let C : Matrix (Fin n') (Fin n') L :=
    B * A - Formalism.UG.cT σ A * Formalism.UG.cT σ B + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * A)
  have hAZ : A * Z = 1 := by
    ext i j; rw [Matrix.mul_apply, Matrix.one_apply]; exact hdual i j
  have hAI : IsIntM A := fun i r => ha i r
  have hZI : IsIntM Z := fun r j => hz j r
  have hBI : IsIntM B := fun r i => by
    show (J *ᵥ w i) r ∈ Formalism.UG.intL L
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun s _ => mul_mem (hJI r s) (hw i s)
  have hPI : IsIntM P := isIntM_mul (isIntM_cT hσv hBI) hZI
  have hcC : Formalism.UG.cT σ C = -C := by
    simp only [C, cT_add, cT_sub, cT_smul, cT_mul_rect, cT_cT σ hσσ, hσhalf]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, smul_sub, neg_add, neg_sub]
  refine ⟨C, ?_, ?_, ?_⟩
  · intro r s
    have := congrFun (congrFun hcC s) r
    simpa [Formalism.UG.cT] using this
  · exact isIntM_add (isIntM_sub' (isIntM_mul hBI hAI) ((isIntM_mul (isIntM_cT hσv hAI) (isIntM_cT hσv hBI))))
      (isIntM_smul hhalf (isIntM_mul (isIntM_mul (isIntM_cT hσv hAI) (isIntM_sub' hPI (isIntM_cT hσv hPI))) hAI))
  · have hP : ∀ k i, P k i = Formalism.UG.hform σ J (w k) (z i) := by
      intro k i
      show ∑ r, σ (B r k) * z i r = _
      simp only [B, Formalism.UG.hform, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.mulVec, dotProduct, map_sum, map_mul, herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hσh : ∀ x y : Fin n' → L, σ (Formalism.UG.hform σ J x y) = Formalism.UG.hform σ J y x := by
      intro x y
      simp only [Formalism.UG.hform, map_sum, map_mul, hσσ, herm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hS : ∀ k i, DvdPow ϖ 1 ((P + Formalism.UG.cT σ P) k i) := by
      intro k i
      have e : (P + Formalism.UG.cT σ P) k i = Formalism.UG.hform σ J (z k) (w i) + Formalism.UG.hform σ J (w k) (z i) := by
        show P k i + σ (P i k) = _
        rw [hP, hP, hσh, add_comm]
      rw [e]; exact hcong k i
    have hCZ : C * Z = B - (2⁻¹ : L) • (Formalism.UG.cT σ A * (P + Formalism.UG.cT σ P)) := by
      have e1 : C * Z = B * (A * Z) - Formalism.UG.cT σ A * P + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * (A * Z)) := by
        simp only [C, P, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [e1, hAZ, Matrix.mul_one, Matrix.mul_one]
      have e2 : Formalism.UG.cT σ A * P = (2⁻¹ : L) • (Formalism.UG.cT σ A * P) + (2⁻¹ : L) • (Formalism.UG.cT σ A * P) := by
        rw [← add_smul]
        have : (2⁻¹ + 2⁻¹ : L) = 1 := by
          have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
          field_simp; norm_num
        rw [this, one_smul]
      rw [e2, Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]
      abel
    intro i r
    have e : (C *ᵥ z i) r - (J *ᵥ w i) r = (C * Z) r i - B r i := rfl
    rw [e, hCZ, Matrix.sub_apply, sub_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
    refine dvdPow_neg (dvdPow_sum _ _ fun k _ => ?_)
    rw [← mul_assoc]
    exact dvdPow_mul_int (hS k i) (mul_mem hhalf (isIntM_cT hσv hAI r k))

end GlobalTheory.Hk3.SkewLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdealMulHomMapMemMatrixHomLattice
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

noncomputable section

namespace GlobalTheory.TwU

theorem map_mem_homLat_of_mem_YYl : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), ∀ A ∈ TaylorLogMetric.YYl D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
  intro D P W Qq _ _ _ _ _ _ p hp ρ hA h1 k k' N N' a b hNa hNb

  have hsc : ∀ (c : D.host.E) (M : Matrix (Fin k') (Fin k) D.host.E), (∃ y : W, ρ c = algebraMap W Qq y) →
      M.map ρ ∈ homLat W (colSpan W a) (colSpan W b) → (c • M).map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
    rintro c M ⟨y, hy⟩ hM z hz
    have e : (c • M).map ρ = y • M.map ρ := by
      ext i j
      simp [Matrix.map_apply, map_mul, hy, Algebra.smul_def]
    rw [e, Matrix.smul_mulVec]
    exact (colSpan W b).smul_mem y (hM z hz)
  have hO : ∀ c : 𝓞 D.host.E, ∃ y : W, ρ (c : D.host.E) = algebraMap W Qq y := fun c =>
    (h1 c).imp fun y hy => hy.1

  have hAA : ∀ x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ y : W, ρ x = algebraMap W Qq y := by
    intro x hx
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
      ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩
    rw [hA] at hx'
    obtain ⟨s, hs, hsx⟩ := hx'
    obtain ⟨t, ht⟩ := Submodule.mem_one.1 hsx
    obtain ⟨ys, hys, hsP⟩ := h1 s
    obtain ⟨yt, hyt⟩ := hO t
    have hu : IsUnit ys := by
      have hmax : IsLocalRing.maximalIdeal W = Ideal.span {(p : W)} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hp
      by_contra hn
      have : ys ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal ys).2 hn
      rw [hmax, Ideal.mem_span_singleton] at this
      exact hs (hsP.2 this)
    refine ⟨hu.unit⁻¹ * yt, ?_⟩
    have e1 : ρ (algebraMap (𝓞 D.host.E) D.host.E t) = ρ (s : D.host.E) * ρ x := by
      rw [ht, Algebra.smul_def, map_mul]
    have e2 : algebraMap W Qq ys ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W Qq)]
      exact hu.ne_zero
    rw [map_mul, ← hyt]
    change _ = _ * ρ (t : D.host.E)
    rw [show ((t : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E t from rfl, e1, hys, ← mul_assoc, ← map_mul,
      IsUnit.val_inv_mul, map_one, one_mul]

  have hHom : ∀ A ∈ TaylorLogMetric.homL D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
    intro A hA'
    induction hA' using Submodule.span_induction with
    | mem A hA0 =>
      intro z hz
      rw [← hNa] at hz
      rw [← hNb]
      induction hz using Submodule.span_induction with
      | mem z hz0 =>
        obtain ⟨x, hx, rfl⟩ := hz0
        refine Submodule.subset_span ⟨A *ᵥ x, hA0 x hx, ?_⟩
        funext i
        simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hz hz'
      | smul c z _ hz => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hz
    | zero => rw [Matrix.map_zero _ (map_zero ρ)]; exact Submodule.zero_mem _
    | add A B _ _ hA hB => rw [Matrix.map_add _ (map_add ρ)]; exact Submodule.add_mem _ hA hB
    | smul c A _ hA => exact hsc (c : D.host.E) A (hO c) hA
  intro A hA'
  induction hA' using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA0, rfl⟩ := hB
    exact hsc c A (hAA c hc) (hHom A hA0)
  | zero => rw [Matrix.map_zero _ (map_zero ρ)]; exact Submodule.zero_mem _
  | add A B _ _ hA hB => rw [Matrix.map_add _ (map_add ρ)]; exact Submodule.add_mem _ hA hB
  | smul c A _ hA => exact hsc (c : D.host.E) A (hO c) hA

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScale
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem jointCD_of_large : ∀ eps ez A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L)
    (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D →
    (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointCD L HW := by
  intro eps ez A heps hez
  obtain ⟨x1, h1⟩ := GlobalTheory.T.roomy_of_large_scale eps 100 A heps le_rfl
  obtain ⟨x2, h2⟩ := GlobalTheory.T.eleven_le_inertOddPrimeImagQuadratic_large_scale ez hez
  refine ⟨max x1 x2, ?_⟩
  intro D L Pm HW he hZ hA hx hadm hfont hja i hin r ρ π hpt w hw
  have hR : Roomy L 100 := h1 D L Pm he hA (le_trans (le_max_left _ _) hx)
  have h11 : 11 ≤ D.nd.l i := h2 D L _ hZ (le_trans (le_max_right _ _) hx) Fact.out hin
  have hn2 := hin.ne_two
  have hj := hin.2.2.2
  refine ⟨GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw hin.1 hin.2.1 hin.2.2.1, ?_⟩
  intro Cx hG
  obtain ⟨ε, g, hg, hB⟩ := GlobalTheory.T.wordConditions_common_natural_representation L 100 HW i r ρ π w hw Cx hG hR hadm hfont hja hpt hin.1 hin.2.1 hin.2.2.1
  have hs := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D (D.nd.l i) hin.1 hin.2.1 hin.2.2.1).2
  have hm : (DV.frobG D (D.nd.l i)).1.2 = -1 := by
    refine (Int.units_eq_one_or _).resolve_left fun h => hj ?_
    rw [← hs, h]; rfl
  have hm' : ((DV.frobG D (D.nd.l i))⁻¹).1.2 = -1 := by
    change ((DV.frobG D (D.nd.l i)).1.2)⁻¹ = -1
    rw [hm]; rfl
  refine ⟨_, hB, GlobalTheory.T.thickLetterWord_hypotheses_of_common_conditions L HW i r ρ π w hw Cx hG _ hn2 hB, h11,
    GlobalTheory.T.twistedDualSizeWord_boxesAndSizes L 100 _ ε g _ hR hg, ?_⟩
  rcases GlobalTheory.T.twistedDualSizeWord_inert_dichotomy L 100 _ ε g _ _ hR hg h11 hm' with h | ⟨d, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨d, hd, GlobalTheory.T.alternatingWord_hypotheses_every_lattice_surjection L HW i r ρ π w hw Cx hG _ d h11 hB hd⟩

end GlobalTheory.HTW.RecS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointConditionsRangeBound
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem closingFamilyX : GlobalTheory.Published.FontaineBcris → Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D) (X : KillingConditions.HubData D), AdmissibleParameterJ.JumpBoundClosedForm D → AdmissibleParameterJ.AdmJ large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → GlobalTheory.PtCore.PtFam D X.r X.ρ → (∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i) → (∀ i, AbsIrreducibleDistinct D i (X.r i)) ∧ (∀ i, KillingConditions.RangeAD large₂ X.exc (D.nd.l i) → ∀ π, ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i (X.r i) π M0 h0 (X.cB i)) ∧ (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambDual (D := D) i (X.ρ i) π (X.dc i)) ∧ (∀ i π, EmbeddingTypes.H1fFiniteRankTorsion (D := D) i (X.ρ i) π (X.dc i))
:= by
  intro hF hK D HW F large₂ X hJ hA hP h41 hO hX hcB
  refine ⟨fun i => GlobalTheory.abs_irreducible_distinct_constituents D h41 hO i _ (hX.good i), fun i hR π => ?_,
    fun i hl π hπ => ?_, fun i π => GlobalTheory.Pass.ambient_h1f_of_local_finiteness hK D i _ π _ (hX.cont i π)⟩
  · exact GlobalTheory.BlockWindow.jointCond_TB_at_range D HW F large₂ (hJ large₂ hA) hP i _ π _ (fun h => hR.1 (Or.inl h))
      (fun h => hR.2.1 (Or.inl h)) (fun h => hR.2.1 (Or.inr h)) (hX.good i) (hcB i)
  · have hp := GlobalTheory.T.point_in_family_crystalline hF D X hX hA.1 i hl π hπ
    intro _ w hw _ C τ a
    have hd : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (X.r i π) (X.ρ i π) (D.nd.chi i) e := by
      obtain ⟨e, he⟩ := hp.dec
      exact ⟨e, fun g u => he g u⟩
    have := D.nd.lPrime i
    have := C.LL.2
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ C.LL _ _ (hp.crys w hw C π)).1
    exact (((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le (X.r i) (X.ρ i) π hd).2 hdr).2.2 τ a).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelBasisDeterminantAbsAtPlace
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.SatakeUnitDeterminantBasis

theorem detB : ∀ (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (T : GL3Columns.KFTie E O w), T.detB := by
  intro D Dx Tw E u μ O w T idl hp i hi c τ
  have hb := T.B_bas i hi c τ
  rw [O.dt_lat, hp.2.2.2.2]
  exact GlobalTheory.T.padic_norm_det_lattice_basis_eq_det_ideal_norm D _ (E.lam w) τ _ _ _ _ (O.lattice_integral_coordinates i) hb.1 hb.2.1 hb.2.2

end GlobalTheory.SatakeUnitDeterminantBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependentStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeModel_vacuumTranslate_classes_independent : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    iSupIndep (fun c : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = c ∧ w = ρ x s}) := by
  first | exact @GlobalTheory.Hk3.locVac_span_classes_indep | exact GlobalTheory.Hk3.locVac_span_classes_indep | (intros; apply GlobalTheory.Hk3.locVac_span_classes_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisorsStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localMatrix_doubleCoset_of_elementaryDivisors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram), IsIdemOf E v e → IsFrameAt V v h → ϖ ≠ 0 → DivG hc V e ϖ d g → ∃ k₁ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, (h⁻¹ * locMat hc V v g * h).1 = k₁.1 * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i)) * k₂.1 := by
  first | exact @GlobalTheory.PlaceDiv.double_coset_of_divG | exact GlobalTheory.PlaceDiv.double_coset_of_divG | (intros; apply GlobalTheory.PlaceDiv.double_coset_of_divG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationEqOfHeckeAgreementTwistLaws
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.LocSepTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpChar_zero_unr (w : PlE H) (χ : A.LP w) (hd : A.lpDim χ = 1) (hu : A.unr χ) :
    A.lpChar (A.lpZero w) χ = A.lpZero w := by
  have hu0 := A.lpZero_unr w
  have hc := A.unr_char _ _ hd hu0 hu
  have hcard := A.frobEig_card _ hc
  rw [A.lpDim_char _ _ hd, A.lpDim_zero] at hcard
  calc A.lpChar (A.lpZero w) χ = A.lpUnr w (A.frobEig (A.lpChar (A.lpZero w) χ)) := A.unr_eq_lpUnr _ hc
    _ = A.lpUnr w (A.frobEig (A.lpZero w)) := by rw [Multiset.card_eq_zero.mp hcard, A.frobEig_zero]
    _ = A.lpZero w := (A.unr_eq_lpUnr _ hu0).symm

theorem spehLoc_twist_of_laws (hC : GlobalTheory.RowTie.CharLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H)
    (hz : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  have hsum : ∀ a b : A.LP w, A.lpChar (A.lpSum a b) (A.locG χ w) =
      A.lpSum (A.lpChar a (A.locG χ w)) (A.lpChar b (A.locG χ w)) := fun a b => (hC w a b _ _ 0 hχ hχ).1
  have htw : ∀ (a : A.LP w) (s : ℝ), A.lpChar (A.lpTw a s) (A.locG χ w) = A.lpTw (A.lpChar a (A.locG χ w)) s :=
    fun a s => (hC w a a _ _ s hχ hχ).2.1
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact hz.symm
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, hsum, htw, A.locG_tw]

theorem isoLoc_twist_of_laws (hC : GlobalTheory.RowTie.CharLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H)
    (hz : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  induction S with
  | nil => exact hz.symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, spehLoc_twist_of_laws N A hC p χ w hz, (hC w _ _ _ _ 0 hχ hχ).1]

theorem isoLoc_append_one (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil =>
    change A.lpSum (spehLoc N A q w) (A.lpZero w) = A.lpSum (A.lpZero w) (spehLoc N A q w)
    exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

theorem heckePol_coeff (i : N.Loc) (x : N.X i) (w : PlE H) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ R.nV) :
    (heckePol N i x w).coeff (R.nV - k) =
      (-1 : N.O i) ^ k * ((normV w : ℕ) : N.O i) ^ (k * (k - 1) / 2) * ((N.hT i w k : N.X i → N.O i) x) := by
  unfold heckePol
  exact GlobalTheory.PtLocalEig.coeff_monic_poly_sum R.nV k hk1 hk2
    (fun k' => (-1 : N.O i) ^ k' * ((normV w : ℕ) : N.O i) ^ (k' * (k' - 1) / 2) * ((N.hT i w k' : N.X i → N.O i) x))

theorem main : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → GlobalTheory.RowTie.CharLaws D.nd D.naut →
    (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v →
      D.naut.locW i σ v = D.naut.locW i' σ v) →
    (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') →
    KillingConditions.LocalisationUniqueness D := by
  intro D M HT hC hW hmu
  unfold KillingConditions.LocalisationUniqueness
  intro i i' _ hj hw σ _ hA hA'
  by_contra hne
  obtain ⟨φ, hφ⟩ := HT.sameO i i' hj hw
  obtain ⟨Sig, hSig, x, hx⟩ := hA
  obtain ⟨Sig', hSig', x', hx'⟩ := hA'
  obtain ⟨v, k, hv, hv', hk1, hk2, hunit⟩ := HT.sep i i' φ hφ hj hw hne x x'
  obtain ⟨p, hp1, hp2⟩ := hx v hv
  obtain ⟨p', hp1', hp2'⟩ := hx' v hv'
  have hinj' : Function.Injective (iotaO D.nd D.naut i') := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i').injective.comp ((D.naut.iotaQ i').injective.comp
      (IsFractionRing.injective (D.nd.O i') (FractionRing (D.nd.O i'))))
  have hmuP : muPart D.nd D.naut i = muPart D.nd D.naut i' := by
    unfold muPart; rw [hmu i i' hj hw]
  have hz := lpChar_zero_unr D.nd D.naut v (D.naut.locG D.naut.etaTinv v) (D.naut.locG_dim _ v)
    (D.naut.etaTinv_def v).1
  have hpar : isoLoc D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) v =
      isoLoc D.nd D.naut (twistIso D.nd D.naut (Sig' ++ [muPart D.nd D.naut i']) D.naut.etaTinv) v := by
    rw [isoLoc_twist_of_laws D.nd D.naut hC _ _ v hz, isoLoc_twist_of_laws D.nd D.naut hC _ _ v hz,
      isoLoc_append_one, isoLoc_append_one, hSig.2.2 v hv.1, hSig'.2.2 v hv'.1, hW i i' σ v hv.1, hmuP]
  have hpp : p.map (φ : D.nd.O i →+* D.nd.O i') = p' := by
    apply Polynomial.map_injective (iotaO D.nd D.naut i') hinj'
    rw [Polynomial.map_map, hp1', ← hpar, ← hp1]
    congr 1
    exact RingHom.ext fun z => (hφ z).symm
  set n := D.R.nV - k
  have e1 : IsLocalRing.residue (D.nd.O i) (p.coeff n) =
      IsLocalRing.residue (D.nd.O i) ((heckePol D.nd i x v).coeff n) := by
    have := congrArg (fun P => Polynomial.coeff P n) hp2
    simpa only [Polynomial.coeff_map] using this
  have e2 : IsLocalRing.residue (D.nd.O i') (p'.coeff n) =
      IsLocalRing.residue (D.nd.O i') ((heckePol D.nd i' x' v).coeff n) := by
    have := congrArg (fun P => Polynomial.coeff P n) hp2'
    simpa only [Polynomial.coeff_map] using this
  have e3 := GlobalTheory.PtLocalEig.residue_map_equiv φ e1
  have hcp : φ (p.coeff n) = p'.coeff n := by
    rw [← hpp, Polynomial.coeff_map]; rfl
  have hφc : φ ((-1 : D.nd.O i) ^ k * ((normV v : ℕ) : D.nd.O i) ^ (k * (k - 1) / 2) *
      ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x)) = (-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2) *
      φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [hcp, e2, heckePol_coeff D.nd i x v k hk1 hk2, heckePol_coeff D.nd i' x' v k hk1 hk2, hφc] at e3
  have hq := GlobalTheory.PtLocalEig.normV_unit D i' v hv'.2.1
  have hc : IsUnit ((-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2)) :=
    ((isUnit_one.neg).pow k).mul (hq.pow _)
  have hdiff : IsLocalRing.residue (D.nd.O i')
      ((-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2) *
        (φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) - (D.nd.hT i' v k : D.nd.X i' → D.nd.O i') x')) = 0 := by
    rw [mul_sub, map_sub, e3, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hdiff
  exact hdiff (hc.mul hunit)

end GlobalTheory.LocSepTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hyperspecial_iff_gInt_of_suppAt_split : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ g : GA D V, SuppAt e V g → (g ∈ KsphC V ∅ ↔ GInt (Ov D v) (rho V π β g)) := by
  first | exact @GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt | exact GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt | (intros; apply GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmEmbeddingsEqOneOfInertStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_prod_cmEmbeddings_eq_one_of_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ≠ 2 → GL3Theta.InertK D p → ∀ z : D.host.E, z * D.host.conj z = 1 → ‖TaylorLogMetric.lamC lam (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z)‖ = 1 := by
  first | exact @GlobalTheory.normUnit_of_inert | exact GlobalTheory.normUnit_of_inert | (intros; apply GlobalTheory.normUnit_of_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricVectorTwoBlockProductExistsPermNeZeroStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricVector_twoBlockProduct_exists_perm_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), f ≠ 0 → IsParahoricVec χ (prod₂ σ₁ σ₂) f → ∃ w : Equiv.Perm (Fin (r + t)), f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 := by
  first | exact @GlobalTheory.ParahoricPerm.exists_perm_ne_zero | exact GlobalTheory.ParahoricPerm.exists_perm_ne_zero | (intros; apply GlobalTheory.ParahoricPerm.exists_perm_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ServedPrimePropertiesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.servedPrime_properties : ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p → HNeZero D.host p → hP D p ≠ 0 ∧ jacobiSym (-(D.host.d : ℤ)) p = -1 ∧ Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  first | exact @GlobalTheory.TwU.Served.served_facts | exact GlobalTheory.TwU.Served.served_facts | (intros; apply GlobalTheory.TwU.Served.served_facts <;> assumption)
end

