import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0275
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudesRelevantCellMonomialRep
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0235
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FullySplitStabilizers
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianMassFormula
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypothesesStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplifier_of_hypotheses : BranchingSupport.Hyps → GlobalTheory.CellAmp.AmpKF := by
  first | exact @GlobalTheory.AmpOrb.ampKF | exact GlobalTheory.AmpOrb.ampKF | (intros; apply GlobalTheory.AmpOrb.ampKF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalDataStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_one_side_of_good_local_data : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → OneSide W.z W.π (psiS D W.z) W.μG W.μW (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS' A.Φ' A.cN := by
  first | exact @GlobalTheory.AmpSides.oneSide_of_good | exact GlobalTheory.AmpSides.oneSide_of_good | (intros; apply GlobalTheory.AmpSides.oneSide_of_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudesRelevantCellMonomialRepStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudes_relevant_cell_monomial_rep : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A₀ : LocS W) (hA : GoodS D lam0 A₀) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'), 0 < θ → 0 < D.host.ka / gg D → ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ' : ℝ, 0 < θ' → ∀ νR, RMeas D W γ θ' νR → ∃ (g₀ : MatKR D.R.k D.R.rS) (μR ν₀ : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)) (s : ℂ), CellData (toBessel D τ w w' θ W lam0 A₀ hW hA hT hT') W.μG g₀ μR ν₀ ν ∧ ν₀ {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 ∧ (∀ l, DminN W.z W.z' γ l = DminN W.z W.z' g₀ l) ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → A.J νR γ = s • A.J ν₀ g₀ := by
  first | exact @GlobalTheory.CellRed.amp_at_monomial | exact GlobalTheory.CellRed.amp_at_monomial | (intros; apply GlobalTheory.CellRed.amp_at_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelProjectorOnLineStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModel_projector_on_line : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l → (∀ u ∈ DD σ w, l2SG ν (fun x => l (σ x u)) = ENNReal.ofReal (‖u‖ ^ 2 / d)) ∧ (∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x ∈ GG k r, Afun (psiGen k r z c) π μS σ w v ξ x = ⟪l v, ξ⟫_ℂ • l (σ x w)) ∧ ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, rconv μG (eFun μG σ w) W y = ((d : ℂ) * ∫ g, ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ ∂ν) • l (σ y w) := by
  first | exact @GlobalTheory.SgInf.ProjLine.projector_line | exact GlobalTheory.SgInf.ProjLine.projector_line | (intros; apply GlobalTheory.SgInf.ProjLine.projector_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockProjectionBessel
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellPieri

variable {k r : ℕ}

def withRep (L : LocBessel k r) (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (hR : R.IsDS L.ε mu) :
    LocBessel k r :=
  { L with lam := mu, hlam := hR.1, Hs := R.H, hsN := R.nacg, hsI := R.ips, hsC := R.cs, σ := R.σ, hσ := hR.2 }

theorem fdegHC_pos {n : ℕ} {lam : Fin n → ℝ} (hlam : StrictAnti lam) : 0 < fdegHC lam := by
  unfold fdegHC
  apply div_pos
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hlam hab).ne')
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    exact sub_pos.mpr (Nat.cast_lt.mpr (Finset.mem_filter.mp hb).2)

def coefR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (R : Rep k r) (v v' : R.H) (ξ : Wp) (ξ' : Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, R.σ g v'⟫_ℂ • ξ)

theorem amp_eq_orb (hH : Hyps) (hA : AmpKF) (hC : CellConv) (L : LocBessel k r) (R : Rep k r)
    (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H)
    [CompleteSpace L.Wp] [CompleteSpace L.Wq]
    (hR : R.IsDS L.ε mu) (hgap : GapAtLeast L.ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hcell : GapCell k r h)
    (hc : L.c ≠ 0) (hκ : L.κN ≠ ⊤) (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hl : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hl' : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))
    (hw : PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) (hD : CellData L μG γ μR νR ν) (v v' : R.H) (hv : R.KFin v) (hv' : R.KFin v')
    (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (coefR R v v' ξ ξ') γ) ν ∧
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) * (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ)) • amp R l l' w νR γ =
        OrbInt L (coefR R v v' ξ ξ') γ ν := by
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨-, -, -, -, hsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF k r L.ε mu R hR
  have hwK : R.KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw
  have hle : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, x ∈ R.TK := by
    intro x hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, w, hwK, rfl⟩
  have hD' : CellData (withRep L R mu hR) μG γ μR νR ν := hD
  obtain ⟨b, hb0, hb1, hb2⟩ := hC k r L h μG γ μR νR ν hκ hok hcell hD hD.2.2.1
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hOne : OnePlaceKF (withRep L R mu hR) h μG w l l' :=
    ⟨⟨hgap, hok, hc, hw, hG, fun x hx y hy => hl x (hsm x (hle x hx)) y (hle y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hle y hy)⟩,
      fun x hx y hy => hl x (hsm x (hle x hx)) y (hKT y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hKT y hy)⟩
  have h1 := hA hH.1 k r (withRep L R mu hR) h μG w l l' hOne γ μR νR ν hD' b hb0 hb1 hb2 v v' hv hv' ξ ξ'
  have h2 := (GlobalTheory.T.cell_data_support hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD').2 b hb0 (by linarith)
    hb2 v v' hv hv' ξ ξ'
  refine ⟨h2, ?_⟩
  obtain ⟨c, hc0, hc1⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r L.ε μG hG
  have hw0 : w ≠ 0 := by
    obtain ⟨P, -, hn, -⟩ := hw
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hf : (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) ≠ 0 := by
    rw [(hc1 mu R hR).1 w hw0]
    exact Complex.ofReal_ne_zero.mpr (mul_pos hc0 (fdegHC_pos hR.1.1)).ne'
  have h3 : (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • amp R l l' w νR γ =
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)⁻¹) • OrbInt L (coefR R v v' ξ ξ') γ ν := h1
  rw [mul_smul, h3, smul_smul, mul_inv_cancel₀ hf, one_smul]

theorem herm_inv {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {d : ℕ}
    (hρ : IsFRep ρ Γ d) {om : ι → ℂ} {a g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ GG k r) (hg : g ∈ GG k r) (hom : ρ a *ᵥ om = om) (x : ι → ℂ) :
    herm Γ (ρ (a⁻¹ * g) *ᵥ x) om = herm Γ (ρ g *ᵥ x) om := by
  obtain ⟨-, -, -, hmul, hinv, -⟩ := hρ
  obtain ⟨hai, h1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha
  have hm : a⁻¹ * g ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hai hg
  have e : ρ g = ρ a * ρ (a⁻¹ * g) := by
    rw [← hmul a ha _ hm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold herm
  rw [e]
  conv_rhs => rw [← hom]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hinv a ha]

theorem one_mem_UH : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  simp [UH]

theorem mem_Sset_of_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) : g ∈ Sset k r z := by
  refine ⟨g, hg, 1, ⟨one_mem_UH, fun a i _ => ?_, fun i j _ _ _ => ?_⟩, (Matrix.mul_one g).symm⟩ <;>
    exact Matrix.one_apply

theorem mem_Sset_of_N (z : Fin (2 * r + k + 1) → ℂ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Nset k r) : g ∈ Sset k r z :=
  ⟨1, ⟨one_mem_UH, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, g, hg,
    (Matrix.one_mul g).symm⟩

theorem herm_cell {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {d : ℕ}
    (hρ : IsFRep ρ Γ d) {om om' : ι → ℂ} {z z' : Fin (2 * r + k + 1) → ℂ}
    (hom : ∀ g ∈ Sset k r z, ρ g *ᵥ om = om) (hom' : ∀ g ∈ Sset k r z', ρ g *ᵥ om' = om')
    {a n γ n' a' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ GG k r)
    (ha : a ∈ UWset k r z) (hn : n ∈ Nset k r) (ha' : a' ∈ UWset k r z') (hn' : n' ∈ Nset k r) :
    a⁻¹ * n⁻¹ * γ * n' * a' ∈ GG k r ∧
      herm Γ (ρ (a⁻¹ * n⁻¹ * γ * n' * a') *ᵥ om') om = herm Γ (ρ γ *ᵥ om') om := by
  have mul : ∀ {x y}, x ∈ GG k r → y ∈ GG k r → x * y ∈ GG k r := fun hx hy => Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hx hy
  have hai := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha.1).1
  have hni := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hn.1).1
  have h1 := mul (mul hai hni) hγ
  have h2 := mul h1 hn'.1
  refine ⟨mul h2 ha'.1, ?_⟩
  rw [hρ.2.2.2.1 _ h2 _ ha'.1, hρ.2.2.2.1 _ h1 _ hn'.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hom' _ (mem_Sset_of_UW ha'), hom' _ (mem_Sset_of_N z' hn'), Matrix.mul_assoc,
    herm_inv hρ ha.1 (mul hni hγ) (hom _ (mem_Sset_of_UW ha)),
    herm_inv hρ hn.1 hγ (hom _ (mem_Sset_of_N z hn))]

theorem amp_pieri : Hyps → AmpKF → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  intro hH hA hC k r ι κ _ _ _ _ ρ Γ d L R RI io pr ep mu muI h μG om om' l l' lI lI' w wI κ₀ κ₁
  haveI := FiniteDimensional.complete ℂ L.Wp
  haveI := FiniteDimensional.complete ℂ L.Wq
  intro hR hgap hRI hok hcell hc hκ hG hρ hT hom hom' hl hl' hlI ⟨v, hv, hv0⟩ ⟨v', hv', hv0'⟩ hw hwI hκI γ μR νR ν hD
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  have hvs : v ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v hv
  have hvs' : v' ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v' hv'
  obtain ⟨hK, hsplit⟩ := GlobalTheory.KFinCoefSplit.kfin_coef_mul_split hKF k r ι κ ρ Γ d R RI io pr ep L.ε mu muI om om' v v' hR
    (fun I => (hRI I).1) hρ hT hv hv'
  obtain ⟨-, e0⟩ := amp_eq_orb hH hA hC L R mu h μG l l' w hR hgap hok hcell hc hκ hG hl hl' hw γ μR νR ν hD
    v v' hv hv' (l v) (l' v')
  have eI := fun I => amp_eq_orb hH hA hC L (RI I) (muI I) h μG (lI I) (lI' I) (wI I) (hRI I).1 (hRI I).2 hok hcell
    hc hκ hG (hlI I).1 (hlI I).2 (hwI I) γ μR νR ν hD _ _ (hK I).1 (hK I).2 (l v) (l' v')
  have hae := (GlobalTheory.T.cell_data_support hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD).1
  have hc0 : ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ ≠ 0 :=
    mul_ne_zero (inner_self_ne_zero.mpr hv0) (inner_self_ne_zero.mpr hv0')
  have horb : herm Γ (ρ γ *ᵥ om') om • OrbInt L (coefR R v v' (l v) (l' v')) γ ν =
      ∑ I, (ep I : ℂ) • OrbInt L (coefR (RI I) (∑ c, pr I c (tm R om v c)) (∑ c, pr I c (tm R om' v' c))
        (l v) (l' v')) γ ν := by
    unfold OrbInt
    simp only [← integral_smul]
    refine Eq.trans (integral_congr_ae ?_) (integral_finset_sum _ (fun I _ => (eI I).1.smul (ep I : ℂ)))
    filter_upwards [hae] with p hp
    obtain ⟨hm, he⟩ := herm_cell hρ hom hom' hD.1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hs := hsplit _ hm
    rw [he] at hs
    ext x
    simp only [besselIntg, coefR, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, map_smul, smul_smul, Pi.smul_apply,
      ← Finset.sum_smul]
    congr 1
    have key : ∀ (D A B C : ℂ) (e f : κ → ℂ), D * C = ∑ I, e I * f I →
        D * A * (B * C) = ∑ I, e I * A * (B * f I) := by
      intro D A B C e f hh
      rw [show D * A * (B * C) = D * C * (A * B) by ring, hh, Finset.sum_mul]
      exact Finset.sum_congr rfl fun I _ => by ring
    exact key _ _ _ _ _ _ hs
  apply smul_right_injective _ hc0
  simp only [Finset.smul_sum, smul_smul]
  rw [mul_comm, mul_assoc, mul_smul, e0, horb]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← (eI I).2, smul_smul, (hκI I v hvs).1, (hκI I v' hvs').2, inner_smul_left, inner_smul_right]
  congr 1
  simp only [RCLike.star_def]
  ring

end GlobalTheory.CellPieri

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory

theorem columnLevel_stabTriv :
    ∀ (D : D7) (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
      Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) := by
  intro D X hK u h γ hγ

  have hfin : IsOfFinOrder γ :=
    Formalism.L2.SG.PoincareInHH.Cut.gamFinKu_of X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) h γ hγ
  exact Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK h γ hγ hfin

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
section
noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.CovDom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  have := rank_base_space D.R
  simp only [Ranks.N, zero_mul, add_zero] at this
  omega

variable {D : D7} (X : HidaSetting D)

def ci : Fin (2 * D.R.rS + D.R.k + 1) ≃ Fin X.B.I.n := finCongr (X.n_eq.trans (rank_eq D)).symm

def crdH (y : (VS D).V) : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E := fun i => X.bas.repr y (ci X i)

def vecOf : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) →ₗ[D.host.E] (VS D).V :=
  X.bas.equivFun.symm.toLinearMap ∘ₗ (LinearEquiv.funCongrLeft D.host.E D.host.E (ci X).symm).toLinearMap

def Jc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E :=
  fun i j => (VS D).hT (X.bas (ci X i)) (X.bas (ci X j))

def Lc : Submodule (𝓞 D.host.E) (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :=
  (VS D).L0.comap ((vecOf X).restrictScalars (𝓞 D.host.E))

def Pc (u : D.what₂.Word) : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  Matrix.of fun i b => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.eX a) i) b

def fc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin D.R.rS) D.host.E :=
  Matrix.of fun i a => crdH X (X.fY a) i

def Tc (u : D.what₂.Word) : D.host.F := (((D.mem u).A.T : ℕ) : D.host.F)

def tauOf (D : D7) (w : InfinitePlace D.host.E) : D.what₂.Tau :=
  (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose

def Direct (D : D7) (w : InfinitePlace D.host.E) : Prop := w.embedding = embS D (tauOf D w)

def A0 {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  (C.Qi (tauOf D w) * (X.B.I.P (vOf X (tauOf D w)))⁻¹).submatrix id (ci X)

def Ac {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  if Direct D w then A0 X C w else (A0 X C w).map star

def sc (D : D7) (a : Fin D.R.rS) : ℝ := (2 * D.host.v) ^ (D.R.rS - (a : ℕ))

def trX {θ : ℝ} (C : Choice X θ) (x : X.B.I.Ginf) : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun τ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ)))

def cjw (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  if Direct D w then M else fun i j => star (M i j)

def Gm (D : D7) (y : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun w => cjw D w (y (tauOf D w))

end GlobalTheory.CovDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGramFibreOfHaar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.GramFibreRescale

theorem isFibreFamily_smul {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν B fib)
    (c d : ℝ≥0) (hd : d ≠ 0) :
    IsFibreFamily (c • μ) f ι U (d • ν) B (fun b => (c / d) • fib b) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc hU => ⟨fun b hb => ?_, ?_⟩⟩
  · rw [Measure.smul_apply, h1 b, smul_zero]
  · simp only [Measure.restrict_smul, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul,
      mul_div_cancel₀ _ hd, h2 φ hφ]
  · exact ((h3 φ hφ hc hU).1 b hb).smul_measure_nnreal
  · simp only [integral_smul_nnreal_measure]
    exact (h3 φ hφ hc hU).2.const_smul (c / d)

end GlobalTheory.GramFibreRescale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebraStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∃ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ ∧ IsGaugeSub {g | uMat g - 1 ∈ A} d μ := by
  first | exact @GlobalTheory.GaugeSubExists.exists_isGaugeSub | exact GlobalTheory.GaugeSubExists.exists_isGaugeSub | (intros; apply GlobalTheory.GaugeSubExists.exists_isGaugeSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendSpecialUnitaryRep
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUExt

variable {n : ℕ}

lemma one_mem_SUset (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
  refine ⟨?_, by simp⟩
  show Formalism.REAL.inUJ ε 1
  simp [Formalism.REAL.inUJ]

lemma mul_mem_SUset {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ SUset ε)
    (hb : b ∈ SUset ε) : a * b ∈ SUset ε := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, by rw [Matrix.det_mul, ha2, hb2, one_mul]⟩
  change Formalism.REAL.inUJ ε a at ha1
  change Formalism.REAL.inUJ ε b at hb1
  show Formalism.REAL.inUJ ε (a * b)
  unfold Formalism.REAL.inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha1, hb1]

lemma ne_zero_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma central_eq {ε : Fin n → Bool} (hn : 1 ≤ n) (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hrep : IsURepOn (SUset ε) π')
    (hc : ∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v)
    {g : Matrix (Fin n) (Fin n) ℂ} {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hgz : z⁻¹ • g ∈ SUset ε) (hgw : w⁻¹ • g ∈ SUset ε) :
    z ^ m • π' (z⁻¹ • g) = w ^ m • π' (w⁻¹ • g) := by
  have hz0 := ne_zero_of_norm_one hz
  have hw0 := ne_zero_of_norm_one hw
  set ζ := z * w⁻¹ with hζ
  have hkey : w⁻¹ • g = (ζ • (1 : Matrix (Fin n) (Fin n) ℂ)) * (z⁻¹ • g) := by
    rw [smul_mul_assoc, one_mul, smul_smul]
    congr 1
    rw [hζ]; field_simp
  have hζn : ζ ^ n = 1 := by
    have h1 := congrArg Matrix.det hkey
    rw [hgw.2, Matrix.det_mul, hgz.2, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at h1
    simpa using h1.symm
  have hζnorm : ‖ζ‖ = 1 := by rw [hζ, norm_mul, norm_inv, hz, hw]; simp
  have hζ1 : ζ • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε :=
    ⟨((GlobalTheory.T.unitary_to_special_unitary_local n hn ε).2.1 ζ hζnorm 1 (one_mem_SUset ε)).1,
      by rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, hζn, mul_one]⟩
  ext v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hkey, hrep.1.2 _ hζ1 _ hgz,
    ContinuousLinearMap.comp_apply, hc ζ hζn, smul_smul]
  congr 1
  rw [hζ, mul_zpow, _root_.inv_zpow, mul_left_comm, mul_inv_cancel₀ (zpow_ne_zero m hw0), mul_one]

open Classical in

def extRep (ε : Fin n → Bool) (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (g : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  if h : ∃ z : ℂ, ‖z‖ = 1 ∧ z⁻¹ • g ∈ SUset ε then h.choose ^ m • π' (h.choose⁻¹ • g) else 0

lemma extRep_eq {ε : Fin n → Bool} (hn : 1 ≤ n) (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hrep : IsURepOn (SUset ε) π')
    (hc : ∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v)
    {g : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} (hz : ‖z‖ = 1) (hg : z⁻¹ • g ∈ SUset ε) :
    extRep ε m π' g = z ^ m • π' (z⁻¹ • g) := by
  have h : ∃ z : ℂ, ‖z‖ = 1 ∧ z⁻¹ • g ∈ SUset ε := ⟨z, hz, hg⟩
  rw [extRep, dif_pos h]
  exact central_eq hn m π' hrep hc h.choose_spec.1 hz h.choose_spec.2 hg

theorem extends_to_U : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (m : ℤ) (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (SUset ε) π' →
    (∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v) →
    ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsURepOn (UJset ε) π := by
  intro n hn ε H _ _ m π' hrep hc
  have hS := GlobalTheory.T.unitary_to_special_unitary_local n hn ε
  have hE : Ext ε m π' (extRep ε m π') := by
    intro z hz g hg
    have hg' : z⁻¹ • (z • g) ∈ SUset ε := by
      rwa [smul_smul, inv_mul_cancel₀ (ne_zero_of_norm_one hz), one_smul]
    rw [extRep_eq hn m π' hrep hc hz hg', smul_smul, inv_mul_cancel₀ (ne_zero_of_norm_one hz), one_smul]
  refine ⟨extRep ε m π', hE, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · have h1 := hE 1 (by simp) 1 (one_mem_SUset ε)
    rw [one_smul] at h1
    rw [h1, _root_.one_zpow, one_smul, hrep.1.1]
  · intro a ha b hb
    obtain ⟨z, hz, a₀, ha₀, rfl, -⟩ := hS.1 a ha
    obtain ⟨w, hw, b₀, hb₀, rfl, -⟩ := hS.1 b hb
    have hab : z • a₀ * w • b₀ = (z * w) • (a₀ * b₀) := smul_mul_smul_comm z a₀ w b₀
    rw [hab, hE _ (by rw [norm_mul, hz, hw, one_mul]) _ (mul_mem_SUset ha₀ hb₀), hE z hz a₀ ha₀,
      hE w hw b₀ hb₀, hrep.1.2 a₀ ha₀ b₀ hb₀]
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul,
      mul_zpow]
    rw [mul_comm (w ^ m)]
  · intro g hg v
    obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := hS.1 g hg
    rw [hE z hz g₀ hg₀, ContinuousLinearMap.smul_apply, norm_smul, norm_zpow, hz, _root_.one_zpow, one_mul,
      hrep.2.1 g₀ hg₀ v]
  · intro v g hg
    obtain ⟨U, ζ, hUo, hgU, hζc, hζ⟩ := hS.2.2 g hg
    have hζc' : ContinuousOn ζ (UJset ε ∩ U) := hζc.mono Set.inter_subset_right
    have hne : ∀ x ∈ UJset ε ∩ U, ζ x ≠ 0 := fun x hx => ne_zero_of_norm_one (hζ x hx.2 hx.1).1
    have h1 : ContinuousOn (fun x => ζ x ^ m) (UJset ε ∩ U) :=
      hζc'.zpow₀ m (fun x hx => Or.inl (hne x hx))
    have h2 : ContinuousOn (fun x => (ζ x)⁻¹ • x) (UJset ε ∩ U) :=
      (hζc'.inv₀ hne).smul continuousOn_id
    have h3 : ContinuousOn (fun x => π' ((ζ x)⁻¹ • x) v) (UJset ε ∩ U) :=
      (hrep.2.2 v).comp h2 (fun x hx => (hζ x hx.2 hx.1).2)
    have hs : ContinuousOn (fun x => ζ x ^ m • π' ((ζ x)⁻¹ • x) v) (UJset ε ∩ U) := h1.smul h3
    have heq : Set.EqOn (fun x => extRep ε m π' x v) (fun x => ζ x ^ m • π' ((ζ x)⁻¹ • x) v)
        (UJset ε ∩ U) := by
      intro x hx
      simp only
      rw [extRep_eq hn m π' hrep hc (hζ x hx.2 hx.1).1 (hζ x hx.2 hx.1).2,
        ContinuousLinearMap.smul_apply]
    exact (continuousWithinAt_inter (hUo.mem_nhds hgU)).1 ((hs.congr heq) g ⟨hg, hgU⟩)

end GlobalTheory.SUExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantPowLeHaarWeightStatement
section
open NumberField Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_invariant_pow_le_haar_weight : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (r k TT : ℕ) (rd H : ℝ) (γ : PN.Pts E r), 0 < rd → (∀ a, 1 ≤ ∏ v : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2) → NDPt rd γ ≤ H → NGPt rd TT γ ^ (k - 1) ≤ H ^ (6 * (2 * r + 2)) * nPt rd k TT γ := by
  first | exact @GlobalTheory.HaarWeight.gram_pow_le_haar | exact GlobalTheory.HaarWeight.gram_pow_le_haar | (intros; apply GlobalTheory.HaarWeight.gram_pow_le_haar <;> assumption)
end

