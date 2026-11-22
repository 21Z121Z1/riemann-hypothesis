import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0137
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanTermANonneg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0076
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDimensionFormula
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0413
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairsAmplitudeBoundOfTypeBound
section
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc
namespace GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pairsDegOfType_holds : PairsDegOfType := by
  intro CH Ch Cp C hCH hCh hCp hC
  set Cc : ℝ := 21 + 4 * |CH| with hCcdef
  have hCc : 0 ≤ Cc := by positivity
  have hC0 : 0 ≤ C := by linarith
  refine ⟨max 1 (k2C0 (k2Cf C Ch Cc)), fun C' Cl Cg cb Cw cT CT C0 D large₂ X Y u h2 hH hTie tAt => ?_⟩
  have b1 : (1 : ℝ) ≤ Cl := le_trans (le_max_left _ _) h2
  have b5 : k2C0 (k2Cf C Ch Cc) ≤ Cl := le_trans (le_max_right _ _) h2
  have dAt : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 :=
    fun t ht => delta_pos_le_height_sq (PFHost_of_data D hH.1.2.1) large₂ hCH hC t ht
  have cAt := GlobalTheory.Core.Deg.sum_labels_one_record CH C' Cl Cg cb Cw cT CT C0 D large₂ X Y u b1 hH
  have pg := GlobalTheory.Core.Deg.pgC_le_two_at_record C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  obtain ⟨hΓ, hdim⟩ := kappa_off_diagonal_dim_form_C D X Y u hTie
  have hJ := JPosC_holds Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hTie
  obtain ⟨hL, -, -, -, hWd, -⟩ := hTie
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u
  have hI := Formalism.L2.SG.Closed.OOIntAllC_outright D X Y u u (Formalism.L2.SG.Closed.FoldOKC_outright D X Y u hL hWd)
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y u hL hWd) hF
  have hIrr := IrrVecC_holds D X Y u hF hI
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hmass : 0 ≤ massC Y u := Finset.sum_nonneg fun Λ _ => by unfold wRow; positivity
  have hK : 0 ≤ dpiC X u * massC Y u := mul_nonneg hdpi hmass
  set B := dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 with hB
  set g : GTu Y u × GTu Y u → ℝ := ((Y.tO u u).allPairs (Y.tO u u).degSet).indicator
    (fun p => ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖) with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => Set.indicator_nonneg (fun p _ => by positivity) p
  have hfin : ∀ s : Finset (GTu Y u × GTu Y u), ∑ p ∈ s, g p ≤ B := by
    intro s
    have : ∑ p ∈ s, g p = ∑ p ∈ s.filter (fun p => p ∈ (Y.tO u u).allPairs (Y.tO u u).degSet),
        ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ := by
      rw [Finset.sum_filter]
      rfl
    rw [this]
    exact fin_bound hC0 hCh (le_refl _) hK hIrr hJ tAt dAt cAt _ (fun p hp => (Finset.mem_filter.1 hp).2)
  have hsum : Summable g := summable_of_sum_le hg0 hfin
  have htsum : Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet) ≤ B :=
    tsum_le_of_sum_le' (mul_nonneg hK (sq_nonneg _)) hfin
  refine ⟨hsum, ?_⟩
  have hPg0 : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hdu : 0 ≤ duC X Y u := Nat.cast_nonneg _
  have hCf : 1 ≤ k2Cf C Ch Cc := by unfold k2Cf; nlinarith [sq_nonneg C, sq_nonneg Ch, sq_nonneg Cc]
  have hk : k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k := by
    have hL0 : 0 ≤ large₂.sc.L := by
      rw [← log_scale_eq_L]; exact Real.log_nonneg (by linarith [two_le_scale_b large₂ (D := D)])
    have hm6 : 0 ≤ (D.R.m : ℝ) ^ 6 * large₂.sc.L := mul_nonneg (by positivity) hL0
    have := hH.2.1
    calc k2C0 (k2Cf C Ch Cc) * (D.R.m : ℝ) ^ 6 * large₂.sc.L = k2C0 (k2Cf C Ch Cc) * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := by ring
      _ ≤ Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := mul_le_mul_of_nonneg_right b5 hm6
      _ = Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L := by ring
      _ ≤ _ := this
  have hA : (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 ≤ k2B D large₂ (k2Cf C Ch Cc) := by
    unfold k2B
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => kloostermanTermA_nonneg large₂ hC0 hCh hCc j)
      (Finset.sum_le_sum fun j hj => rank_contribution_le large₂ hC0 j hj) 2
  have hclose := final_bound_closes D large₂ (k2Cf C Ch Cc) hCf _ hdu hk
  have hGB : (Y.tO u u).Gam1 * B ≤ duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
    have e : (Y.tO u u).Gam1 * B =
        ((Y.tO u u).Gam1 * massC Y u * dpiC X u) * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
      rw [hB]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hdim (sq_nonneg _)
  calc PgC Y * ((Y.tO u u).Gam1 *
        Formalism.L2.SG.RowsOther.ampSum (Y.tO u u) ((Y.tO u u).allPairs (Y.tO u u).degSet))
      ≤ PgC Y * ((Y.tO u u).Gam1 * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htsum hΓ) hPg0
    _ ≤ PgC Y * (duC X Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2) :=
        mul_le_mul_of_nonneg_left hGB hPg0
    _ ≤ 2 * (duC X Y u * k2B D large₂ (k2Cf C Ch Cc)) :=
        mul_le_mul pg (mul_le_mul_of_nonneg_left hA hdu) (mul_nonneg hdu (sq_nonneg _)) (by norm_num)
    _ = 2 * duC X Y u * k2B D large₂ (k2Cf C Ch Cc) := by ring
    _ ≤ _ := hclose

end GlobalTheory.Core.Deg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfIteratedFiniteIntegralsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_integral_vanish_of_iterated_finite_integrals : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁] [LocallyCompactSpace G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [LocallyCompactSpace G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (A₁ B₁ R₁ : Subgroup G₁) (A₂ B₂ R₂ : Subgroup G₂), IsClosed (A₁ : Set G₁) → IsClosed (B₁ : Set G₁) → IsClosed (R₁ : Set G₁) → (∀ a ∈ A₁, ∀ b ∈ B₁, a * b = b * a) → (∃ e : (A₁ × B₁) ≃ₜ G₁, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A₁, ∀ b ∈ B₁, a * b ∈ R₁ → a ∈ R₁ ∧ b ∈ R₁) → IsClosed (A₂ : Set G₂) → IsClosed (B₂ : Set G₂) → IsClosed (R₂ : Set G₂) → (∀ a ∈ A₂, ∀ b ∈ B₂, a * b = b * a) → (∃ e : (A₂ × B₂) ≃ₜ G₂, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A₂, ∀ b ∈ B₂, a * b ∈ R₂ → a ∈ R₂ ∧ b ∈ R₂) → ∀ (μR₁ : Measure R₁) (μG₁ : Measure G₁) (ρ₁ : Measure (R₁.subgroupOf B₁)) (μ₁ : Measure B₁) (μR₂ : Measure R₂) (μG₂ : Measure G₂) (ρ₂ : Measure (R₂.subgroupOf B₂)) (μ₂ : Measure B₂), μR₁.IsHaarMeasure → μR₁.IsInvInvariant → μG₁.IsHaarMeasure → ρ₁.IsHaarMeasure → ρ₁.IsInvInvariant → μ₁.IsHaarMeasure → μ₁.IsMulRightInvariant → μR₂.IsHaarMeasure → μR₂.IsInvInvariant → μG₂.IsHaarMeasure → ρ₂.IsHaarMeasure → ρ₂.IsInvInvariant → μ₂.IsHaarMeasure → ∀ (K : Subgroup G₁) (C : Set G₁) (T : Finset G₁), K ≤ B₁ → IsCompact (K : Set G₁) → IsOpen ((K.subgroupOf B₁ : Subgroup B₁) : Set B₁) → IsCompact C → C ⊆ (B₁ : Set G₁) → (∀ q ∈ T, q ∈ B₁) → ∀ (F₁ : G₁ → ℂ) (F₂ : G₁ → G₂ → ℂ) (z : ℂ), IsQuotIntL1 μR₁ μG₁ F₁ z → (∀ h₁, IsQuotIntL1 μR₂ μG₂ (F₂ h₁) (F₁ h₁)) → (∀ h₁, ∀ k ∈ K, F₂ (h₁ * k) = F₂ h₁) → (∀ h₁, F₂ h₁ ≠ 0 → ∃ q ∈ T, ∃ r ∈ R₁, ∃ a ∈ A₁, ∃ k ∈ C, h₁ = r * a * q * k) → (∀ a ∈ A₁, ∀ a' ∈ A₂, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun (q₁ : B₁) (q₂ : B₂) => F₂ (a * q₁.1) (a' * q₂.1)) 0) → z = 0 := by
  first | exact @GlobalTheory.VanCore.vanish | exact GlobalTheory.VanCore.vanish | (intros; apply GlobalTheory.VanCore.vanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealStabilizerProductMeasureIsHaarOnSetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_stabilizer_product_measure_isHaarOnSet : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  first | exact @GlobalTheory.MuSHaar.muS_isHaarOnSet | exact GlobalTheory.MuSHaar.muS_isHaarOnSet | (intros; apply GlobalTheory.MuSHaar.muS_isHaarOnSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeEntriesMemSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchange_entries_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle), Continuous ψ →
  ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (J : Subgroup (GL (n ⊕ Fin c) k)) (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    xi ψ ν μ Φ.1 J b h' h ∈ SB (Matrix n n' k) := by
  first | exact @GlobalTheory.StepData.xi_mem_SB | exact GlobalTheory.StepData.xi_mem_SB | (intros; apply GlobalTheory.StepData.xi_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeUnipotentHaarIntegralPointsEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR.UnitVolN
open GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model

theorem mkNel_mem_KO_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (p : ℕ) (e : Ix n c p → k) :
    ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c) ↔ ∀ i, e i ∈ 𝒪[k] := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  constructor
  · rintro ⟨h1, -⟩ i
    have := congrFun (co_mkNel (k := k) p e) i
    rw [← this]
    exact h1 _ _
  · intro he
    have hent : ∀ r s, ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k).val r s ∈ 𝒪[k] := by
      intro r s
      change mkN p e r s ∈ 𝒪[k]
      simp only [mkN, Matrix.of_apply]
      split_ifs with h
      · exact he _
      · rw [Matrix.one_apply]; split_ifs
        · exact one_mem _
        · exact zero_mem _
    refine ⟨hent, fun i j => ?_⟩
    set g : GL (n ⊕ Fin c) k := ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) with hg
    have hdet : g.val.det = 1 := det_mkN p e
    have hinv : (g⁻¹).val = g.val.adjugate := by
      rw [Matrix.coe_units_inv, Matrix.inv_def, hdet]; simp
    let A : Matrix (n ⊕ Fin c) (n ⊕ Fin c) 𝒪[k] := fun r s => ⟨g.val r s, hent r s⟩
    have hA : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
    rw [hinv, ← hA, ← RingHom.map_adjugate]
    exact (A.adjugate i j).2

end GlobalTheory.HaarR.UnitVolN
end

open GlobalTheory.RootEx.VolN in

theorem GlobalTheory.HaarR.volN_KO_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), IsUnitVol ν → volN ν n c p {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = 1 := by
  intro k _ _ _ _ _ _ n _ _ c p h1 hp ν hν
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [volN_eq, MeasurableEquiv.map_apply]
  have : (coEquiv (k := k) (n := n) (c := c) p) ⁻¹' {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} =
      Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext e
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi]
    exact GlobalTheory.HaarR.UnitVolN.mkNel_mem_KO_iff p e
  rw [this, Measure.pi_pi]
  simp [hν.2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfPartHavePartParamsFirstChainMember
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw.LevelYZero
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem levS_congr {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L L' : LevDat D.host.E ℂ V.rank)
    (h : ∀ x, x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L ↔ x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L') :
    levS V β L = levS V β L' := by
  have e : Formalism.L2.DIV.lev D.sp.cm V.gram β L = Formalism.L2.DIV.lev D.sp.cm V.gram β L' := Subgroup.ext h
  unfold levS Lev.levG
  rw [e]

theorem principalRowLevelCharacter_trivial (k : GA D (Yc D 0)) : Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k = 1 := by
  unfold Lev.levChi Formalism.L2.DIV.levFn
  simp [LevCh.dat0, Lev.datY]
  exact Lev.subgroupCharExtension_one_apply _ _

theorem levS_datYt (t : T) : levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  refine levS_congr _ _ _ fun x => ?_
  show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
  unfold LevCh.datYt LevCh.dat0
  rw [Formalism.IndefR.Eqv.Act.mem_parLev_datY_noQ Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 R.Pg (R.Q t) R.triv R.chi
    (R.xiR t) (fun _ => 1) Lev.Frm.B x]
  rfl

theorem levChi_datYt (t : T) : Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  funext k
  rw [Formalism.IndefR.Eqv.Act.flag_character_eq_principal, principalRowLevelCharacter_trivial]
  unfold Lev.levChi Formalism.L2.DIV.levFn
  simp [LevCh.dat0, Lev.datY, Lev.flag1L, Lev.withP]
  exact Lev.subgroupCharExtension_one_apply _ _

theorem levChi_flat (t : T) (hr : D.R.r ≤ (stY R t 0).V.rank) (k : GA D (Yc D 0)) :
    Lev.levChi (flat (comR R t) (twR R t) 0 (stY R t 0) hr).V (flat (comR R t) (twR R t) 0 (stY R t 0) hr).β
      (flat (comR R t) (twR R t) 0 (stY R t 0) hr).L k = 1 := by
  unfold Lev.levChi Formalism.L2.DIV.levFn
  simp [flat, comR, twR, Lev.datY]
  exact Lev.subgroupCharExtension_one_apply _ _

open Classical in

theorem levS_flat_gen (Q : Finset (Pl D.host.E)) (hr : D.R.r ≤ (Yc D 0).rank)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    levS (Yc D 0) (R.βY 0) (Lev.datY (Yc D 0).rank D.R.r D.R.t 0 hr (R.Pg ∪ Q) ∅ ⟨trivAt R.Pg (R.Pg ∪ Q) D.R.r, 1⟩ χ ξ
      Lev.Frm.B) = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  have hbt : ∀ (κ : Type) [CommRing κ] (g : GL (Fin (Yc D 0).rank) κ), g ∈ blockTri (blkOf (n := (Yc D 0).rank) D.R.r D.R.t) := by
    intro κ _ g
    show (g : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) κ).BlockTriangular _
    intro i j hij
    have hi : i.val < D.R.r := lt_of_lt_of_le i.2 Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le
    have hj : j.val < D.R.r := lt_of_lt_of_le j.2 Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le
    simp [blkOf, hi, hj] at hij
  refine levS_congr _ _ _ fun x => ?_
  show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
  simp only [LevCh.dat0, Lev.datY, eq_self_iff_true, if_true, ite_true, parLev, Subgroup.mem_inf, Subgroup.mem_iInf, mem_parah]
  constructor
  · rintro ⟨⟨⟨⟨hU, hSt⟩, hPg⟩, -⟩, hT⟩
    refine ⟨⟨⟨⟨hU, hSt⟩, fun i hi => hPg i (Finset.mem_union_left _ hi)⟩, fun i hi => absurd hi (Finset.notMem_empty _)⟩, ?_⟩
    show _ ∈ (⊥ : Subgroup (G0 R.Pg D.R.r))
    rw [Subgroup.mem_bot]
    funext PP
    exact hT ⟨PP.1, Finset.mem_union_left _ PP.2⟩ PP.2
  · rintro ⟨⟨⟨⟨hU, hSt⟩, -⟩, -⟩, hT⟩
    refine ⟨⟨⟨⟨hU, hSt⟩, fun i _ => ⟨hSt, hbt _ _⟩⟩, fun i hi => absurd hi (Finset.notMem_empty _)⟩, fun PP hP => ?_⟩
    exact congrFun (Subgroup.mem_bot.1 (show _ ∈ (⊥ : Subgroup (G0 R.Pg D.R.r)) from hT)) ⟨PP.1, hP⟩

theorem levS_flat (t : T) (hr : D.R.r ≤ (stY R t 0).V.rank) :
    levS (flat (comR R t) (twR R t) 0 (stY R t 0) hr).V (flat (comR R t) (twR R t) 0 (stY R t 0) hr).β
      (flat (comR R t) (twR R t) 0 (stY R t 0) hr).L = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) :=
  levS_flat_gen R (R.Q t) hr _ _

end GlobalTheory.ChainTw.LevelYZero

namespace GlobalTheory.ChainTw

open LevelYZero in

theorem rowPar_of_chain : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → (∀ h : RangeX R, RChain R h) → RangeX R → RowPar R := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F _hG hch hX t c
  obtain ⟨htw, hst, -, -, -⟩ := hch hX t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨hr, -, hflat⟩ := hst 0 hm
  have hc : (comR R t).Is := htw.com
  have hS : (comR R t).S = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
    unfold Com.S GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl comR
    congr
  have hrk : (Yc D 0).rank = D.R.r := le_antisymm Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0)
  set s' := flat (comR R t) (twR R t) 0 (stY R t 0) hr with hs'
  have hJ' : levS s'.V s'.β s'.L = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := levS_flat R t hr
  have hχ' : Lev.levChi s'.V s'.β s'.L = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) :=
    funext fun k => (levChi_flat R t hr k).trans (principalRowLevelCharacter_trivial R k).symm
  have hJ : levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levS (Yc D 0) (R.βY 0) (R.dat0 R.triv) := levS_datYt R t
  have hχ : Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = Lev.levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) := levChi_datYt R t
  obtain ⟨hval, hHk, hconj⟩ := GlobalTheory.ConjVal.conj_values_hecke hP D (comR R t) hc 0 (Nat.zero_le _) s' hflat
  obtain ⟨-, hlat⟩ := GlobalTheory.ChainOnto.stabLoc_isParamFun_frameLat D (comR R t) hc 0 (Nat.zero_le _) s' hflat
  obtain ⟨hsph, hsph', -⟩ := GlobalTheory.ChainOntoSph.level_spherical_off_S D (comR R t) hc 0 (Nat.zero_le _) s' hflat
  have hmem : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c,
      u ∈ partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) := by
    intro u hu
    rw [hJ', hχ', hS]
    exact (Submodule.mem_inf.1 hu).1
  have hCC : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c,
      PiTensorProduct.lift u ∈ s'.CC (comR R t) := by
    intro u hu
    refine (mem_multT _ _ _ _ _).2 ?_
    erw [LinearEquiv.symm_apply_apply]
    exact ((mem_partFull _ _ _ _ _ _ _).1 (hmem u hu)).1

  have hkey : ∀ y : s'.CC (comR R t), PiTensorProduct.lift.symm (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈
      partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) → ∀ w,
      (∀ k ∈ levS s'.V s'.β s'.L, ∀ g, (fun g => conj (PiLocalization₂.val y w g)) (g * k) =
        (fun k => conj (Lev.levChi s'.V s'.β s'.L k)) k * (fun g => conj (PiLocalization₂.val y w g)) g) ∧
      (∀ P d Rr, Hecke₂ s'.V (levS s'.V s'.β s'.L) (fun k => conj (Lev.levChi s'.V s'.β s'.L k)) (comR R t).S P d Rr →
        heckeLin s'.V Rr (fun g => conj (PiLocalization₂.val y w g)) = c P d • (fun g => conj (PiLocalization₂.val y w g))) ∧
      (fun g => conj (PiLocalization₂.val y w g)) ∈ GlobalTheory.FinZeta.bddAut s'.V := by
    intro y hy w
    obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev⟩ := hval y w
    have hb : PiLocalization₂.val y w ∈ GlobalTheory.FinZeta.bddAut s'.V := ⟨hcont, hinv, C, hC⟩
    have heig := GlobalTheory.T.heckeOperator_inverseCoset_conj_eigenvalue D s'.V _ _ (comR R t).S hsph (PiLocalization₂.val y w) hb hlev c
      (fun P d Rr hR => val_hecke_of_mem_partFull y _ hy P d Rr hR w)
    refine ⟨fun k hk g => ?_, fun P d Rr hR => ?_, ?_⟩
    · show conj (PiLocalization₂.val y w (g * k)) = _
      rw [hlev k hk g, map_mul]
    · have h1 := heig P d Rr ((hHk P d Rr).2 hR)
      have h2 := hconj Rr (PiLocalization₂.val y w)
      rw [h2, h1]
      funext g
      simp
    · refine ⟨Complex.continuous_conj.comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
      · show conj (PiLocalization₂.val y w (γ * g)) = conj (PiLocalization₂.val y w g)
        rw [hinv γ hγ g]
      · simpa using hC g

  have hiff : ∀ y : s'.CC (comR R t), PiTensorProduct.lift.symm (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈
      partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) → ∀ w B, PiLocalization₂.val y w ≠ 0 →
      (ParFun (comR R t) s' (PiLocalization₂.val y w) B ↔
        GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B) := by
    intro y hy w B h0
    obtain ⟨hl, hh, -⟩ := hkey y hy w
    have hne : (fun g => conj (PiLocalization₂.val y w g)) ≠ 0 := by
      intro h
      apply h0
      funext g
      simpa using congrFun h g
    unfold ParFun
    rw [hlat, ← hS, ← hrk]
    exact GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph' hne hl hh B
  have hy : ∀ u (hu : u ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.rowPart R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c),
      PiTensorProduct.lift.symm (((⟨PiTensorProduct.lift u, hCC u hu⟩ : s'.CC (comR R t))) :
        SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ∈
      partFull (comR R t).θ s'.M (levS s'.V s'.β s'.L) (Lev.levChi s'.V s'.β s'.L) (comR R t).S
        (fun P d => c P (dualLab d)) := by
    intro u hu
    show PiTensorProduct.lift.symm (PiTensorProduct.lift u) ∈ _
    rw [LinearEquiv.symm_apply_apply]
    exact hmem u hu
  refine ⟨fun hne => ?_, fun u hu => ?_⟩
  · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set y : s'.CC (comR R t) := ⟨PiTensorProduct.lift u, hCC u hu⟩ with hydef
    have hl0 : (y : SmT s'.M →ₗ[ℂ] (GA D s'.V → ℂ)) ≠ 0 := by
      intro h
      exact hu0 (PiTensorProduct.lift.injective (h.trans (map_zero _).symm))
    obtain ⟨w, hw⟩ : ∃ w, PiLocalization₂.val y w ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact hl0 (LinearMap.ext hh)
    obtain ⟨hl, hh, hb⟩ := hkey y (hy u hu) w
    have hne' : (fun g => conj (PiLocalization₂.val y w g)) ≠ 0 := by
      intro h
      apply hw
      funext g
      simpa using congrFun h g
    obtain ⟨B, hB, -⟩ := GlobalTheory.FinZeta.ParamBound.exists_param_bounded D s'.V _ _ (comR R t).S hsph' _ hb hne' hl c hh
    refine ⟨B, (hiff y (hy u hu) w B hw).1 ?_⟩
    unfold ParFun
    rw [hlat]
    exact hB
  · have hu' : PiTensorProduct.lift u ∈ (stY R t 0).CC (comR R t) := by
      refine (mem_multT _ _ _ _ _).2 ?_
      erw [LinearEquiv.symm_apply_apply]
      show u ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv))
        (Lev.levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv))
      rw [hJ, hχ]
      exact ((mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 hu).1).1
    refine ⟨hu', fun hu0 B hB => ⟨?_, fun w hw => ?_⟩⟩
    · intro h
      apply hu0
      have h1 : PiTensorProduct.lift u = 0 := congrArg Subtype.val h
      exact PiTensorProduct.lift.injective (h1.trans (map_zero _).symm)
    · exact (hiff ⟨PiTensorProduct.lift u, hCC u hu⟩ (hy u hu) w B hw).2 hB

end GlobalTheory.ChainTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComponentParametersContainStringStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarComponent_parameters_contain_string : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s y, IsEigV R i t h s y → ∀ l : (R.cV i).W →ₗ[ℂ] ℂ, (fun g => l (R.extV i t y g)) ≠ 0 → ∀ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B → GlobalTheory.LFun.IsParamFunV (Vc D i) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (fun g => l (R.extV i t y g)) B := by
  first | exact @GlobalTheory.LiftParams.param_of_sysParam | exact GlobalTheory.LiftParams.param_of_sysParam | (intros; apply GlobalTheory.LiftParams.param_of_sysParam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerDualHalfDerivativeLinearFormStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_dualHalf_derivative_linear_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin A.rank) ℂ) (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ (Y * (dblDec A).qY.map (tauE D τ)) f) x = -(2 * Real.pi * Complex.I) * ((2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re : ℝ) : ℂ) * sch ψ A B ν 𝓨 f x := by
  first | exact @GlobalTheory.StdUnn.sch_dRho_dualHalf | exact GlobalTheory.StdUnn.sch_dRho_dualHalf | (intros; apply GlobalTheory.StdUnn.sch_dRho_dualHalf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalPartsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ), ∀ x ∈ grpAt (c.V j') (· ∈ v.gP), ∃ xs : Fin n → GA D (c.V j'), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) ∧ x = (List.ofFn xs).prod := by
  first | exact @GlobalTheory.LevelCut.grpAt_eq_prod_local | exact GlobalTheory.LevelCut.grpAt_eq_prod_local | (intros; apply GlobalTheory.LevelCut.grpAt_eq_prod_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevelStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrime_rational_coset_sameOrbit_iff_level : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k), AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → ∀ (b : L.β (s + 1)) (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ z z' : Sp X.E (R.N (s + 1)), (GlobalTheory.QPl.SameOrb ((W.T s R).lev (s + 1) 0 rfl).J (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔ ∃ κ ∈ (L.levQ (s + 1) b ⟨P.1, hQ⟩).H, ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 z - z') ∈ stdAt X.E (R.N (s + 1)) P.1) := by
  first | exact @GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level | exact GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level | (intros; apply GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level <;> assumption)
end

