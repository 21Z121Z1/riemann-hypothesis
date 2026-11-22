import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0385
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0386
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0387
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0330
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairSpaceMajorantIntegrableBigCell
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section
namespace GlobalTheory.BigConv

theorem good_point (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (hk : 1 ≤ k) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    ∃ μ₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k ∧
      0 < Formalism.QuantumDeterminants.Gf k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) := by
  obtain ⟨μs, -, hμ⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k r L.z L.z' hk L.hz.1 L.hz'.1 L.hz.2 L.hz'.2
  set τ := Formalism.QuantumDeterminants.Tz k r L.z * Formalism.QuantumDeterminants.Tz k r L.z' with hτ
  have hτ0 : 0 < τ := mul_pos L.hz.2 L.hz'.2
  set ζ : ℂ := ((τ + 1 : ℝ) : ℂ) with hζ
  have hn : τ < Complex.normSq ζ := by
    rw [hζ, Complex.normSq_ofReal]; nlinarith
  obtain ⟨hU, hzz⟩ := hμ ζ hn
  refine ⟨μs ζ, hU, ?_⟩
  have hmin := Formalism.QuantumDeterminants.big_cell_minors_holds k r L.z L.z' c (μs ζ) L.hz.1 L.hz'.1
  have hz := hmin.2.2 hc
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ L.hz.1 L.hz'.1, hzz] at hz
  have hr := hmin.1 (Fin.last r)
  set P := Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) ⟨r, by omega⟩ with hP
  have hP0 : P ≠ 0 := by
    have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
    rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) (Fin.last (r + 1)) = ζ * P := by
    unfold Formalism.QuantumDeterminants.zeta at hz
    rw [← hP] at hz
    have h2 := div_mul_cancel₀ (Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) (Fin.last (r + 1))) hP0
    rw [hz] at h2
    exact h2.symm
  unfold Formalism.QuantumDeterminants.Gf
  rw [hlast, ← hP, Complex.normSq_mul]
  have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
  nlinarith

open Formalism.FourierDecayAlt in

theorem conv_good (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hgap : GlobalTheory.CellAmp.GapCell k r h) (hκ : L.κN ≠ ⊤) (c : Fin r → ℂ)
    (μ₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hc : ∀ a, c a ≠ 0) (hμ₁ : μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k)
    (hG : 0 < Formalism.QuantumDeterminants.Gf k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁)) :
    ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧
      MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (Formalism.QuantumDeterminants.bigCell k r c μ₁) b) (Formalism.MainNotions.S.pairMeas L) := by
  have hg := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ₁ hc hμ₁
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg
  have hinv : (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ₁ = 1 := Matrix.nonsing_inv_mul _ hu
  have hZ := Formalism.QuantumDeterminants.bigCellZhat k r L.z L.z' c μ₁ L.hz.1 L.hz'.1
  set ζ := Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.bigCell k r c μ₁ *ᵥ L.z') L.z with hζ
  have hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁)) := by
    have hζ0 : ζ ≠ 0 := by
      intro h0
      have hmin := Formalism.QuantumDeterminants.big_cell_minors_holds k r L.z L.z' c μ₁ L.hz.1 L.hz'.1
      have hz := hmin.2.2 hc
      set P := Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) ⟨r, by omega⟩ with hP
      have hr := hmin.1 (Fin.last r)
      have hP0 : P ≠ 0 := by
        have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
        rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
      unfold Formalism.QuantumDeterminants.zeta at hz
      rw [← hP, ← hζ, h0, div_eq_zero_iff] at hz
      have hD : Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) (Fin.last (r + 1)) = 0 :=
        hz.resolve_right hP0
      unfold Formalism.QuantumDeterminants.Gf at hG
      rw [hD, ← hP] at hG
      have : 0 ≤ Complex.normSq P := Complex.normSq_nonneg _
      have := mul_pos L.hz.2 L.hz'.2
      simp at hG
      nlinarith
    refine ⟨1, fun a => if h : a.val < r then c ⟨a.val, h⟩ else ζ, fun a => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact hc _
      · exact hζ0
    · refine hZ.trans ?_
      ext i j
      rw [Matrix.diagonal_apply]
      show _ = if i = j then _ else _
      by_cases h : i = j
      · rw [if_pos h, if_pos h, h]
      · rw [if_neg h, if_neg h]
  have hR := GlobalTheory.AmpNorm.rStab_bigCell c μ₁ hc hg
  have hcd := GlobalTheory.CellAmp.Model.cellData_open L 0 _ hg hinv hG hmono hR
  exact GlobalTheory.CellMaj.cellConv k r L h 0 _ _ _ _ hκ hok hgap hcd hmono

theorem bigConv : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (Formalism.QuantumDeterminants.bigCell k r c μ) b) (Formalism.MainNotions.S.pairMeas L) := by
  intro k r L h hok hgap hκ hκ0 hcL c μ hc hμ
  obtain ⟨μ₁, hμ₁, hG⟩ := good_point k r L hok.1 c hc
  obtain ⟨b, hb0, hb1, hint⟩ := conv_good k r L h hok hgap hκ c μ₁ hc hμ₁ hG
  have hg₁ := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ₁ hc hμ₁
  have hg := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ hc hμ
  have hu₁ := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg₁
  set a := (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ with ha
  have haU : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hg₁) hg
  have hN := GlobalTheory.T.bigCell_quotient_normalises_unipotent k r c μ₁ μ hc hμ₁ hμ
  obtain ⟨C, hC, hmap⟩ := GlobalTheory.T.map_conj_unipotentHaar_eq_smul k r L hκ0 hκ a haU hN
  refine ⟨b, hb0, hb1, ?_⟩
  have e : Formalism.QuantumDeterminants.bigCell k r c μ₁ * a = Formalism.QuantumDeterminants.bigCell k r c μ := by
    rw [ha, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁]
  rw [← e]
  exact GlobalTheory.T.integrable_besselPairMajorant_mul_right k r L _ a b C hκ0 hκ hb0 hg₁ haU hC hmap hint

end GlobalTheory.BigConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealIntegralUnipotentBesselModelsCountableSubgroStatement
section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realIntegralUnipotent_besselModels_countable_subgroup : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u).Countable ∧
    (fun _ => Matrix.of.symm 1) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      GlobalTheory.DegVol.mulP m m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      (fun τ => Matrix.of.symm (Matrix.of (m τ))⁻¹) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    ∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ τ, Matrix.of (m τ) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  first | exact @GlobalTheory.CovGrp.cov_grp | exact GlobalTheory.CovGrp.cov_grp | (intros; apply GlobalTheory.CovGrp.cov_grp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowSameCosetScalarCorankOne
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam

namespace GlobalTheory.SnFamCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem frame_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ F) a = γ (frame F a) := by
  unfold mapLF
  rw [dif_pos hγ]
  induction a using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem Xflag_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF
  rw [dif_pos hγ]
  show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) =
    (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem orth_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (x : S.V)
    (hx : x ∈ orth S (Xsp (mapLF γ F))) : γ.symm x ∈ orth S (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro y hy
  have hy' : γ y ∈ Xsp (mapLF γ F) := by
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]; simpa using hy
  have := hx (γ y) hy'
  rw [← hγ y (γ.symm x)]
  simpa using this

end Gen

theorem conj_mem_NRat {D : D7} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : LFlag (VS D) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : n ∈ NRat F) : γ * n * γ⁻¹ ∈ NRat (mapLF γ F) := by
  obtain ⟨hn0, hn1, hn2⟩ := hn
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hn0) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ), ?_, ?_⟩
  · intro j x hx
    rw [Xflag_mapLF γ hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, hn1 j y hy, ?_⟩
    show γ (n y - y) = γ (n (γ.symm (γ y))) - γ y
    simp
  · intro x hx
    have h := hn2 _ (orth_mapLF γ hγ F x hx)
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]
    show γ.symm (γ (n (γ.symm x)) - x) ∈ Xsp F
    simpa using h

theorem scalar_of_same_coset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      nmlOf Y u u' t = nmlOf Y u u' t' → (Y.tO u u').s0 t t' = 1 ∧ (Y.tO u u').scal t t' := by
  intro D X Y u u' t t' hG hr hn
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hlat : Submodule.IsLattice D.host.E t.lam := hrow.2.1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := hrow.2.1.2.2.1
  have hLt : IsLift t.lam t.frame := t.rep.2.2.2.2.1
  have hLt' : IsLift t'.lam t'.frame := t'.rep.2.2.2.2.1
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]; exact hG
  have hone : ∀ {T : D.host.E} (F : LFlag (VS D) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
    fun F => ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j x _ => by simp, fun x _ => by simp⟩
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hn]; exact ⟨1, hone _, 1, hone _, by simp⟩
  obtain ⟨n, hn1, n', hn2, heq⟩ := hmem
  have hm : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame := conj_mem_NRat t.lin t.rep.2.2.1 _ n' hn2
  have hβ : t'.lin * t.lin⁻¹ = n * (t.lin * n' * t.lin⁻¹) := by rw [heq]; group
  have hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a) := by
    intro a
    unfold GTerm.frame
    rw [frame_mapLF t'.lin t'.rep.2.2.1, frame_mapLF t.lin t.rep.2.2.1, ← hβ]
    show t'.lin _ = t'.lin (t.lin.symm (t.lin _))
    simp
  have hTh := GlobalTheory.T.theta_cocycle_product_of_rational_unipotents D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  have hsc := GlobalTheory.T.pair_isScalar_in_unipotentRadical_doubleCoset D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  rw [← hβ] at hTh hsc
  have hs0 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t'.frame (t'.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF hLt hGv).2 hTh
  refine ⟨?_, ?_⟩
  · show s0T t t' = 1
    unfold s0T
    rw [if_pos ⟨hlam, hlam'⟩]
    exact hs0
  · show scalT t t'
    exact ⟨⟨hlam, hlam'⟩, hs0, hsc⟩

end GlobalTheory.SnFamCoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledLocalDualCoeffEqGlobalCoeff
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatXS

theorem scaled_local_coef_eq :
    ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (a : Fin D.R.rS) (x : (VS D).V), x ∈ G.fl.X → frFac Z.δ p a.castSucc * (locH Z p).h (baseChange₂ D p x) ((A p).es a) = (D.s.atP p).ιE (G.fl.coefX x a) := by
  intro D T G Z A hA p a x hx

  have hes : ∀ b : Fin D.R.rS, frFac Z.δ p b.castSucc * (locH Z p).h (baseChange₂ D p (G.fl.e b)) ((A p).es a) =
      if b = a then 1 else 0 := by
    intro b
    have h1 := (A p).h_es b a
    rw [hA p] at h1
    rw [← (locH Z p).h_smul_left]
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1
  have hunit : ∀ b : Fin D.R.rS, IsUnit (frFac Z.δ p b.castSucc) := by
    intro b
    have h1 := (A p).h_es b b
    rw [hA p] at h1
    rw [if_pos rfl, (locH Z p).h_smul_left] at h1
    exact isUnit_iff_exists_inv.mpr ⟨_, by simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1⟩
  have hzero : ∀ b : Fin D.R.rS, b ≠ a → (locH Z p).h (baseChange₂ D p (G.fl.e b)) ((A p).es a) = 0 := by
    intro b hb
    have h1 := hes b
    rw [if_neg hb] at h1
    exact (hunit b).mul_right_eq_zero.mp h1

  have hxs : x ∈ Submodule.span D.host.E (Set.range G.fl.e) := hx
  have hexp : x = ∑ b, G.fl.coefX x b • G.fl.e b := by
    have h2 := G.fl.e_indep.linearCombination_repr ⟨x, hxs⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h2
    simp only [Formalism.MainNotions.S.FlagG.coefX, dif_pos hxs]
    exact h2.symm

  have hsum : ∀ (s : Finset (Fin D.R.rS)) (v : Fin D.R.rS → Vp D p) (y : Vp D p),
      (locH Z p).h (∑ b ∈ s, v b) y = ∑ b ∈ s, (locH Z p).h (v b) y := by
    intro s v y
    induction s using Finset.induction_on with
    | empty => simpa using (locH Z p).h_zero_left y
    | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, (locH Z p).h_add_left, ih]
  have hbc : baseChange₂ D p x = ∑ b, (D.s.atP p).ιE (G.fl.coefX x b) • baseChange₂ D p (G.fl.e b) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => baseChange_smul₂ p _ _
  rw [hbc, hsum, Finset.mul_sum, Finset.sum_eq_single a]
  · rw [(locH Z p).h_smul_left, mul_left_comm, hes a, if_pos rfl, mul_one]
  · intro b _ hb
    rw [(locH Z p).h_smul_left, hzero b hb, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.RowLatXS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledUnitriangularChangeEqLocalImage
section
noncomputable section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrCoord

theorem frFac_mul_c {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T}
    {F0' : LFlag (VS D) D.R.rS T'} {FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G) (p : PlF D) (b : Fin (D.R.rS + 1)) :
    (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) * algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) = 1 := by
  have hu : IsUnit (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ)))) :=
    ((G.c p).isUnit.pow _).map _
  have he : (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) =
      Ring.inverse (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ)))) := by
    rw [map_pow]
    exact congrArg (fun x => Ring.inverse (x ^ (D.R.rS - (b : ℕ)))) (c.c_eq p).symm
  rw [he]
  exact Ring.inverse_mul_cancel _ hu

theorem step {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T}
    {F0' : LFlag (VS D) D.R.rS T'} {FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G) (p : PlF D) (N : G.GLV) (m : (G.S p).GLV)
    (hm : (placesOf Z).Ext p N m) (B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (v : Fin (D.R.rS + 1) → (VS D).V) (g : Fin (D.R.rS + 1) → G.V) (gl : Fin (D.R.rS + 1) → (G.S p).V)
    (hg : ∀ a, g a = c.e (v a))
    (hgl : ∀ a : Fin (D.R.rS + 1), algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (a : ℕ))) • gl a =
      (placesOf Z).bc p (g a))
    (hN : ∀ b, N (g b) = ∑ a, B a b • g a) (b : Fin (D.R.rS + 1)) :
    (c.c p).e (scaled Z p (fun b => ∑ a, B a b • v a) b) = m (gl b) := by
  have h1 : c.e (∑ a, B a b • v a) = N (g b) := by
    rw [hN b, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hg a]
  have h2 : (c.c p).e (scaled Z p (fun b => ∑ a, B a b • v a) b) =
      frFac Z.δ p b • (c.c p).e (baseChange₂ D p (∑ a, B a b • v a)) := (c.c p).e.map_smul _ _
  have h3 : m ((placesOf Z).bc p (g b)) = (placesOf Z).bc p (N (g b)) := hm (g b)
  have h4 : m (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • gl b) =
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) := m.map_smul _ _
  have h5 : (c.c p).e (baseChange₂ D p (∑ a, B a b • v a)) =
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) :=
    (c.compat p _).trans ((congrArg ((placesOf Z).bc p) h1).trans
      (h3.symm.trans ((congrArg m (hgl b).symm).trans h4)))
  have h6 : (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) •
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) =
      m (gl b) := by
    rw [smul_smul, frFac_mul_c c p b, one_smul]
  rw [h2, h5]
  exact h6

theorem scaled_coord : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (p : PlF D) (N : G.GLV) (m : (G.S p).GLV), (placesOf Z).Ext p N m → ∀ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, ((∀ b, N (G.f b) = ∑ a, B a b • G.f a) → ∀ b, (c.c p).e (scaled Z p (fun b => ∑ a, B a b • frame F0 a) b) = m ((G.S p).f b)) ∧ ((∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) → ∀ b, (c.c p).e (scaled Z p (fun b => ∑ a, B a b • frame F0' a) b) = m ((G.S p).f' b)) := by
  intro D Z T T' F0 F0' FP G c p N m hm B
  exact ⟨fun hN b => step c p N m hm B (frame F0) G.f (G.S p).f c.f_eq (G.f_eq p) hN b,
    fun hN b => step c p N m hm B (frame F0') G.f' (G.S p).f' c.f'_eq (G.f'_eq p) hN b⟩

end GlobalTheory.FrCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WlocExistsReal
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory

theorem wlocExists_real : WlocExists :=
  scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

end GlobalTheory
end

