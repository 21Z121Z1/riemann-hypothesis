import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFirstFlatMapSupportAtLevelPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_first_flatMap_support_at_level_place : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp1 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ (x : GA D (c.V (j + 1))), SuppAt Gi.q.e (c.V (j + 1)) x → flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (Gi.eg j) F)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, SuppAt Gi.q.e (c.V (j + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  first | exact @GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at | exact GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at | (intros; apply GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralsPositionOneEqCellSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PosOne
open scoped ENNReal

attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

section Scale
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k]

theorem isQuotInt_smul_measure {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {ν : Measure k} {μX : Measure (GL n k)}
    {μG : Measure (GL (n ⊕ Fin c) k)} {p : ℕ} {f : GL (n ⊕ Fin c) k → ℂ} {z : ℂ} (a : ℝ≥0∞)
    (h : IsQuotInt ν μX μG p f z) : IsQuotInt ν μX (a • μG) p f ((a.toReal : ℂ) * z) := by
  obtain ⟨F, hF, hf, hz⟩ := h
  refine ⟨F, hF, hf, ?_⟩
  rw [integral_smul_measure, hz, Complex.real_smul]

theorem isQuotInt_const_mul {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {ν : Measure k} {μX : Measure (GL n k)}
    {μG : Measure (GL (n ⊕ Fin c) k)} {p : ℕ} {f : GL (n ⊕ Fin c) k → ℂ} {z : ℂ} (b : ℂ)
    (h : IsQuotInt ν μX μG p f z) : IsQuotInt ν μX μG p (fun x => b * f x) (b * z) := by
  obtain ⟨F, hF, hf, hz⟩ := h
  refine ⟨fun x => b * F x, (SB _).smul_mem b hF, fun x => ?_, ?_⟩
  · dsimp only
    rw [hf x, ← integral_const_mul]
    congr 1
    funext g
    exact (integral_const_mul _ _).symm
  · rw [hz, integral_const_mul]

theorem app_smul {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V] (b : ℂ) (l : SB X →ₗ[ℂ] V)
    (f : X → ℂ) : app (b • l) f = b • app l f := by
  unfold app
  split_ifs <;> simp

theorem oneDbl_smul {n₀ n₁ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] {c : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] {ψ : AddChar k Circle} {ν : Measure k}
    {m₁ : Measure (GL n₁ k)} {G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)} {m₂ : Measure (GL n₂ k)}
    {G₂ : Measure (GL (n₂ ⊕ Fin c) k)} {μ₁ μ₂ : kˣ →* ℂˣ} {ρ : ℕ} {σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A}
    {T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} {F : A}
    {Φ₁ : Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ}
    {Φ₂ : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ} {z : ℂ} (a b : ℝ≥0∞)
    (h : OneDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁ Φ₂ z) :
    OneDbl ψ ν m₁ (a • G₁) m₂ (b • G₂) μ₁ μ₂ ρ σ T F Φ₁ Φ₂ ((a.toReal : ℂ) * ((b.toReal : ℂ) * z)) := by
  obtain ⟨w, hw, hz⟩ := h
  refine ⟨fun x => (b.toReal : ℂ) • w x, fun x Ψ => ?_, ?_⟩
  · exact isQuotInt_smul_measure b (hw x Ψ)
  · have := isQuotInt_smul_measure a (isQuotInt_const_mul (b.toReal : ℂ) hz)
    convert this using 2 with x
    rw [app_smul, smul_eq_mul]

theorem relIndex_mul_measure_KO {Y : Type} [Fintype Y] [DecidableEq Y] (G : Measure (GL Y k)) [G.IsHaarMeasure]
    (hK : G (KO k Y) = 1) (J : Subgroup (GL Y k)) (hJ : IsCO J) (hle : J ≤ KO k Y) :
    (J.relIndex (KO k Y) : ℝ≥0∞) * G J = 1 ∧ J.relIndex (KO k Y) ≠ 0 := by
  haveI : BorelSpace (GL Y k) := GlobalTheory.SplitFlip.borel_GL
  have hc : IsCompact (KO k Y : Set (GL Y k)) := GlobalTheory.SplitFlip.isCompact_KO
  haveI : CompactSpace (KO k Y) := isCompact_iff_compactSpace.1 hc
  have ho : IsOpen ((J.subgroupOf (KO k Y) : Subgroup (KO k Y)) : Set (KO k Y)) :=
    hJ.1.preimage continuous_subtype_val
  haveI : Finite (KO k Y ⧸ J.subgroupOf (KO k Y)) := Subgroup.quotient_finite_of_isOpen _ ho
  haveI : (J.subgroupOf (KO k Y)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨?_, Subgroup.FiniteIndex.index_ne_zero⟩
  rw [GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup J (KO k Y) hle hJ.1.measurableSet G, hK]

theorem rescale_one_eq {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (hc : 1 ≤ c) {ν : Measure k} (hν : IsUnitVol ν)
    (m : Measure (GL n k)) : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν (1 : GL (n ⊕ Fin c) k) m = m := by
  have h := GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one k n c 1 le_rfl hc ν hν
  have e : (((stabLat (1 : GL (n ⊕ Fin c) k)).subgroupOf (N k n c 1) : Subgroup (N k n c 1)) : Set (N k n c 1)) =
      {u : N k n c 1 | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
    ext u
    simp [Subgroup.mem_subgroupOf, mem_stabLat]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale
  rw [e, h, inv_one, one_smul]

end Scale

set_option maxHeartbeats 4000000 in

theorem comb_eq_sum_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ (ν : Measure k), IsUnitVol ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ), IsOpen (μ₁.ker : Set kˣ) → IsOpen (μ₂.ker : Set kˣ) →
  ∀ (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
    G₁ (KO k (n₁ ⊕ Fin (c + 1))) = 1 → G₂ (KO k (n₂ ⊕ Fin c)) = 1 →
  ∀ (L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1)) k)) (L₁ : Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : Level (GL (n₂ ⊕ Fin c) k)),
    IsCO L₁.J → IsCO L₂.J → L₁.J ≤ KO k _ → L₂.J ≤ KO k _ →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A), (∀ j : L₂.J, τ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) →
  ∀ (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)),
    HasTypes μ₁ L₀ L₁ P₁.1 → HasTypes μ₂ L₁ L₂ P₂.1 →
  ∀ (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (A₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (A₂ : Finset (GL (n₂ ⊕ Fin c) k)),
    Covers 1 L₁.J A₁ (fun h => GlobalTheory.StepData.flat ψ ν μ₁ P₁.1 α h) → (∀ γ ∈ A₁, Covers 1 L₂.J A₂ fun h => GlobalTheory.StepData.flat ψ ν μ₂ P₂.1 γ h) →
  ∀ (e₀ : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ), IsOneComb ψ ν (ρ + 1) L₀ α e₀ →
  ∀ (e₂ : GL (n₂ ⊕ Fin c) k → (GL (n₂ ⊕ Fin c) k →₀ ℂ)), (∀ β ∈ A₂, IsOneComb ψ ν ρ L₂ β (e₂ β)) →
  ∀ (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ),
    (∀ a ∈ e₀.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    comb e₀ z = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ))⁻¹ *
      ∑ γ ∈ A₁, ∑ β ∈ A₂, ((((m₁ (prX (Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (prX (Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) *
        comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F)) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ ho₁ ho₂ m₁ G₁ m₂ G₂ hm₁ hG₁ hm₂ hG₂ hK₁ hK₂
    L₀ L₁ L₂ hco₁ hco₂ hle₁ hle₂ A _ _ τ hτ T hT F hF P₁ P₂ hty₁ hty₂ α A₁ A₂ hcov₁ hcov₂ e₀ he₀ e₂ he₂ z hz
  haveI := hm₁
  haveI := hG₁
  haveI := hm₂
  haveI := hG₂
  have hne : ψ ≠ 1 := hcond.ne_one
  have hsd : IsSelfDual ψ ν := ((GlobalTheory.SplitWeil.selfDual_measure k ψ hψ hne).2.1 hcond ν).1 hν
  obtain ⟨⟨ρ₀, hρ₀⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₀ ⊕ Fin (c + 1 + 1)) (n₁ ⊕ Fin (c + 1)) μ₁ ho₁
  have hsm₀ := hsm ρ₀ hρ₀

  have hcomb : ∀ f : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ,
      comb (e₀.mapDomain (· * α⁻¹)) (fun g => f (g * α)) = comb e₀ f := by
    intro f
    unfold comb
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    simp only [inv_mul_cancel_right]
  have hsrc : SrcComb ψ ν (ρ + 1) ρ₀ (ρ₀ α P₁) (e₀.mapDomain (· * α⁻¹)) := by
    intro L hL
    have hP : ∀ j : L₀.J, ρ₀ (j : GL (n₀ ⊕ Fin (c + 1 + 1)) k) P₁ = (L₀.lam j : ℂ) • P₁ := fun j =>
      Subtype.ext ((hρ₀ _ _).trans (hty₁.1 j))
    rw [he₀ _ ρ₀ hsm₀ L hL P₁ hP, ← hcomb]
    congr 1
    funext g
    rw [map_mul, Module.End.mul_apply]
  have hsym : ∀ g ∈ (e₀.mapDomain (· * α⁻¹)).support,
      SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ g 1 (ρ₀ α P₁).1) P₂.1 (z (g * α)) := by
    intro g hg
    classical
    rw [Finsupp.mapDomain_support_of_injective (mul_left_injective α⁻¹)] at hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hg
    have e : om μ₁ (a * α⁻¹) 1 (ρ₀ α P₁).1 = om μ₁ (a * α⁻¹ * α) 1 P₁.1 := by
      rw [← hρ₀, ← hρ₀, map_mul ρ₀ (a * α⁻¹) α, Module.End.mul_apply]
    rw [e]
    simpa only [inv_mul_cancel_right] using hz a ha
  have h1 := GlobalTheory.T.positionOne_of_symmetricDoubleIntegral_finite k n₀ n₁ n₂ c ρ hcρ ψ hψ hne ν hsd μ₁ μ₂ ho₁ ho₂ m₁ G₁ m₂ G₂ A τ hτ T hT F ρ₀ hρ₀ (ρ₀ α P₁) P₂
    (e₀.mapDomain (· * α⁻¹)) hsrc (fun g => z (g * α)) hsym
  rw [hcomb, hρ₀] at h1

  obtain ⟨hi₁, hn₁⟩ := relIndex_mul_measure_KO G₁ hK₁ L₁.J hco₁ hle₁
  obtain ⟨hi₂, hn₂⟩ := relIndex_mul_measure_KO G₂ hK₂ L₂.J hco₂ hle₂
  set r₁ : ℝ≥0∞ := (L₁.J.relIndex (KO k (n₁ ⊕ Fin (c + 1))) : ℝ≥0∞) with hr₁
  set r₂ : ℝ≥0∞ := (L₂.J.relIndex (KO k (n₂ ⊕ Fin c)) : ℝ≥0∞) with hr₂
  haveI : (r₁ • G₁).IsHaarMeasure := Measure.IsHaarMeasure.smul G₁ (by simpa [hr₁] using hn₁) (by simp [hr₁])
  haveI : (r₂ • G₂).IsHaarMeasure := Measure.IsHaarMeasure.smul G₂ (by simpa [hr₂] using hn₂) (by simp [hr₂])
  have h2 := oneDbl_smul r₁ r₂ h1
  have hc : 1 ≤ c := by omega
  rw [← rescale_one_eq (n := n₁) (c := c + 1) (by omega) hν m₁, ← rescale_one_eq (n := n₂) hc hν m₂] at h2
  have h3 := (GlobalTheory.PosOne.oneDbl_iff_sum k n₀ n₁ n₂ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ ho₁ ho₂ m₁ (r₁ • G₁) m₂ (r₂ • G₂) L₁ L₂
    hco₁ hco₂ (by rw [Measure.smul_apply, smul_eq_mul, hi₁]) (by rw [Measure.smul_apply, smul_eq_mul, hi₂]) 1 1 A τ hτ T hT F hF
    P₁ P₂ hty₁.2 hty₂ α A₁ A₂ hcov₁ hcov₂ _).1 h2

  have hex : ∀ γ ∈ A₁, ∀ β ∈ A₂, toOne ν τ ρ (fun v => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) v)
      (τ β F) = comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F) := by
    intro γ _ β hβ
    refine he₂ β hβ A τ hτ _ ?_ F hF
    intro g hg v
    unfold app
    split_ifs with h₁ h₂
    · exact (hT.1 _).1 _ g hg v
    · simp
    · simp
  have hr : ((r₁.toReal : ℂ) * (r₂.toReal : ℂ)) = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ)) := by
    simp [hr₁, hr₂]
  have hr0 : ((L₁.J.relIndex (KO k (n₁ ⊕ Fin (c + 1))) : ℂ) * (L₂.J.relIndex (KO k (n₂ ⊕ Fin c)) : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn₁) (Nat.cast_ne_zero.2 hn₂)
  rw [← mul_assoc, hr] at h3
  rw [eq_inv_mul_iff_mul_eq₀ hr0, h3]
  refine Finset.sum_congr rfl fun γ hγ => Finset.sum_congr rfl fun β hβ => ?_
  rw [hex γ hγ β hβ]

end GlobalTheory.PosOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDoubleAbsoluteSumSobolevBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf.DoubleSum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem enorm_integral_le {α β : Type} [MeasurableSpace α] {μ : Measure α} {𝓕 : Set α} (h : μ 𝓕 = 1) (u : α → ℂ)
    (hu : ∀ a, ‖u a‖ = 1) (p : α → β) (f : β → ℂ) : ‖∫ a in 𝓕, u a * f (p a) ∂μ‖ₑ ≤ ⨆ w, ‖f w‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine (lintegral_mono (g := fun _ => ⨆ w, ‖f w‖ₑ) fun a => ?_).trans ?_
  · beta_reduce
    rw [enorm_mul, ← ofReal_norm (u a), hu, ENNReal.ofReal_one, one_mul]
    exact le_iSup (fun w => ‖f w‖ₑ) _
  · rw [setLIntegral_const, h, mul_one]

theorem rearrange (C₁ C₂ : ℝ≥0) (p s M : ℝ≥0∞) (hM : M ≠ ⊤) :
    p * ((C₁ + C₂) * s) * M = ((C₁ + C₂) * M.toNNReal : ℝ≥0) * p * s := by
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hM, ENNReal.coe_add]
  ring

section Source

variable {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)

theorem enorm_mixS_le (hψ : IsStdChar D ψ (-1)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) (w : WO S₀ T) :
    ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ ≤ ⨆ w, ‖f w‖ₑ := by
  simp only [HypDec.mixS, HypDec.integrandS_eq]
  exact enorm_integral_le v.covol.2.2 _ (fun _ => hψ.1.2.1 _) _ f

theorem mixS_add (hψ : IsStdChar D ψ (-1)) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (x : Mx D T.rank ρ) : d.mixS T ψ v.μ v.𝓕 (f + g) x = d.mixS T ψ v.μ v.𝓕 f x + d.mixS T ψ v.μ v.𝓕 g x := by
  funext w
  have h1 := d.integrableOn_mixS hψ.1.1 v.covol hf x w
  have h2 := d.integrableOn_mixS hψ.1.1 v.covol hg x w
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
  exact integral_add h1 h2

theorem mixS_smul (c : ℂ) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    d.mixS T ψ v.μ v.𝓕 (c • f) x = c • d.mixS T ψ v.μ v.𝓕 f x := by
  funext w
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

variable (T) in

def dualPt (ρ : ℕ) : Mx D ρ T.rank →+ Mx D T.rank ρ where
  toFun b := adj (incA D D.host.xi0⁻¹ • (b ⬝ giA T))
  map_zero' := by rw [Matrix.zero_mul, smul_zero, adj_zero]
  map_add' _ _ := by rw [Matrix.add_mul, smul_add, adj_add]

theorem continuous_dualPt : Continuous (dualPt T ρ) := by
  have h : Continuous fun b : Mx D ρ T.rank => (b ⬝ giA T : Mx D ρ T.rank) := continuous_id.matrix_mul continuous_const
  exact continuous_adj.comp (f := fun b : Mx D ρ T.rank => incA D D.host.xi0⁻¹ • (b ⬝ giA T : Mx D ρ T.rank))
    (continuous_matrix fun i j => continuous_const.mul (h.matrix_elem i j))

theorem infPart_cA {a : AE D} (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  have e : ∀ z : AE D, infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]
  rw [e, h, map_zero]

theorem dualPt_fin {b : Mx D ρ T.rank} (hb : b.map (infPart D) = 0) : (dualPt T ρ b).map (infPart D) = 0 := by
  have h : (b ⬝ giA T).map (infPart D) = 0 := by rw [Matrix.map_mul, hb, Matrix.zero_mul]
  funext i j
  refine infPart_cA (a := incA D D.host.xi0⁻¹ * (b ⬝ giA T) j i) ?_
  rw [map_mul, show infPart D ((b ⬝ giA T) j i) = 0 from congrFun (congrFun h j) i, mul_zero]

theorem symplO_dualPt (x : Mx D T.rank ρ) (b : Mx D ρ T.rank) :
    symplO S T (d.extX T x) (d.extY T (dualPt T ρ b)) = Algebra.trace (AF D.host.F) (AE D) (x ⬝ b).trace := by
  have h := d.hO_ext T x 0 0 (dualPt T ρ b) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS]
  congr 1
  rw [show dualPt T ρ b = adj (incA D D.host.xi0⁻¹ • (b ⬝ giA T)) from rfl, adj_adj, Matrix.smul_mul, trace_smul, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, Matrix.mul_assoc, giA_gA_cancel, trace_mul_comm]

end Source

section Target

variable {S T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (v : VolM D σ S.rank)

theorem enorm_mixT_le (hψ : IsStdChar D ψ (-1)) (f : WO S T → ℂ) (y : Mx D S.rank σ) (w : WO S T₀) :
    ‖d.mixT S ψ v.μ v.𝓕 f y w‖ₑ ≤ ⨆ w, ‖f w‖ₑ := by
  simp only [HypDec.mixT, HypDec.integrandT_eq]
  exact enorm_integral_le v.covol.2.2 _ (fun _ => hψ.1.2.1 _) _ f

theorem mixT_add (hψ : IsStdChar D ψ (-1)) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (y : Mx D S.rank σ) : d.mixT S ψ v.μ v.𝓕 (f + g) y = d.mixT S ψ v.μ v.𝓕 f y + d.mixT S ψ v.μ v.𝓕 g y := by
  funext w
  have h1 := d.integrableOn_mixT hψ.1.1 v.covol hf y w
  have h2 := d.integrableOn_mixT hψ.1.1 v.covol hg y w
  simp only [HypDec.mixT, HypDec.integrandT_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
  exact integral_add h1 h2

theorem mixT_smul (c : ℂ) (f : WO S T → ℂ) (y : Mx D S.rank σ) :
    d.mixT S ψ v.μ v.𝓕 (c • f) y = c • d.mixT S ψ v.μ v.𝓕 f y := by
  funext w
  simp only [HypDec.mixT, HypDec.integrandT_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

end Target

section Double

variable {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec T T₀ σ) (v : VolM D T.rank ρ)
  (v' : VolM D σ S₀.rank)

variable (ψ) in

def val (x : Mx D T.rank ρ) (y : Mx D S₀.rank σ) (f : WO S T → ℂ) : ℂ :=
  d'.mixT S₀ ψ v'.μ v'.𝓕 (d.mixS T ψ v.μ v.𝓕 f x) y 0

theorem val_extY (hψ : IsStdChar D ψ (-1)) (x : Mx D T.rank ρ) (y : Mx D S₀.rank σ) (b : Mx D ρ T.rank)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    val ψ d d' v v' x y (heisO ψ S T (d.extY T (dualPt T ρ b)) f) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (x ⬝ b).trace) * val ψ d d' v v' x y f := by
  rw [val, (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf).2.1, mixT_smul, symplO_dualPt]
  rfl

theorem val_incX (hψ : IsStdChar D ψ (-1)) (x : Mx D T.rank ρ) (y : Mx D S₀.rank σ) (ξ : Mx D σ S₀.rank)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    val ψ d d' v v' x y (heisO ψ S T (d.ext0 T (d'.incX S₀ ξ)) f) =
      ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * val ψ d d' v v' x y f := by
  rw [val, (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf).2.2.1,
    (GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ S₀ T T₀ σ d' v'.μ v'.𝓕 v'.covol _
      ((GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 S S₀ T ρ d v.μ v.𝓕 v.covol f hf x)).1,
    GlobalTheory.OrientedHeis.symplO_skew, d'.symplO_incX_incAdj]
  rfl

theorem ext_zero_incX_finite_part_zero {ξ : Mx D σ S₀.rank} (h : ξ.map (infPart D) = 0) :
    (d.ext0 T (d'.incX S₀ ξ)).map (infPart D) = 0 := by
  have h1 : (d'.incX S₀ ξ).map (infPart D) = 0 := by rw [HypDec.incX_apply, Matrix.map_mul, h, Matrix.mul_zero]
  rw [HypDec.matrixExtendByZero_apply, Matrix.map_mul, h1, Matrix.zero_mul]

theorem trace_nsmul {a b : ℕ} (n : ℕ) (x : Mx D a b) (z : Mx D b a) : (x ⬝ (n • z)).trace = ((n • x) ⬝ z).trace := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, Matrix.mul_add, Matrix.add_mul, trace_add, trace_add, ih]

end Double

theorem absSum₂_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (ρ σ : ℕ), ∃ k : ℕ, ∀ (S₀ T₀ : HSp D) (d : HypDec S S₀ ρ) (d' : HypDec T T₀ σ) (v : VolM D T.rank ρ) (v' : VolM D σ S₀.rank), ∀ K₀ ∈ nhds (0 : WO S T), ∃ C : ℝ≥0, ∀ n : ℕ, 0 < n → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → GlobalTheory.IndefiniteRowSideFullHecke.WordMatrixSeminorms.absSum₂ ψ d d' v.μ v.𝓕 v'.μ v'.𝓕 f ≤ C * (n : ℝ≥0∞) ^ k * supSob ψ θ k f := by
  intro D ψ hψ θ hθ S T ρ σ
  choose N hN using GlobalTheory.T.tsum_adelicMatrixSchwartzMajorant_rational_ne_top D θ hθ
  refine ⟨N T.rank ρ + N (S.rank - 2 * ρ) σ, fun S₀ T₀ d d' v v' K₀ hK₀ => ?_⟩
  have hr : S.rank - 2 * ρ = S₀.rank := by have := d.rank_add; omega
  rw [hr]
  set k := N T.rank ρ + N S₀.rank σ with hk
  have hmv := fun f hf => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 S S₀ T ρ d v.μ v.𝓕 v.covol f hf
  have c1 : Continuous fun b => d.extY T (dualPt T ρ b) := continuous_dualPt.matrix_mul continuous_const
  have c2 : Continuous fun ξ => d.ext0 T (d'.incX S₀ ξ) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨K, hK, hbox⟩ := GlobalTheory.T.character_annihilator_compact_box D ψ hψ ρ T.rank _
    (c1.continuousAt.preimage_mem_nhds (by rwa [map_zero, map_zero]))
  obtain ⟨K', hK', hbox'⟩ := GlobalTheory.T.character_annihilator_compact_box D ψ hψ σ S₀.rank _
    (c2.continuousAt.preimage_mem_nhds (by rwa [map_zero, map_zero]))
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.mixedCoordinate_decay_realEntries D ψ hψ θ hθ S S₀ T ρ d v k
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.bounded_functional_theta_estimate D ψ hψ θ hθ S T σ S₀.rank d'.jX d.p0 k
  have hM := ENNReal.mul_ne_top (hN T.rank ρ K hK) (hN S₀.rank σ K' hK')
  refine ⟨(C₁ + C₂) * ENNReal.toNNReal ((∑' x : ratMx D T.rank ρ, ENNReal.ofReal (maj θ K (N T.rank ρ) x)) *
    ∑' y : ratMx D S₀.rank σ, ENNReal.ofReal (maj θ K' (N S₀.rank σ) y)), fun n hn f hf hlev => ?_⟩
  refine (GlobalTheory.T.double_sum_weighted_bound D θ _ _ _ _ K K' (N T.rank ρ) (N S₀.rank σ) n hn ((C₁ + C₂) * supSob ψ θ k f)
    (fun x y => ‖val ψ d d' v v' x y f‖ₑ) (fun x y hne => ⟨hbox _ fun b hb hfin => ?_, hbox' _ fun ξ hξ hfin => ?_⟩)
    (fun x y => ?_) (fun x y => ?_)).trans (le_of_eq ?_)
  · have h := val_extY d d' v v' hψ x y (n • b) hf
    rw [map_nsmul, map_nsmul, hlev (d.extY T (dualPt T ρ b)) hb
      (by rw [HypDec.extY_apply, Matrix.map_mul, dualPt_fin hfin, Matrix.zero_mul]),
      trace_nsmul] at h
    exact (mul_eq_right₀ (enorm_ne_zero.1 hne)).1 h.symm
  · have h := val_incX d d' v v' hψ x y (n • ξ) hf
    rw [map_nsmul, map_nsmul, hlev (d.ext0 T (d'.incX S₀ ξ)) hξ (ext_zero_incX_finite_part_zero d d' hfin),
      trace_nsmul, AddChar.map_neg_eq_inv] at h
    exact inv_eq_one.1 ((mul_eq_right₀ (enorm_ne_zero.1 hne)).1 h.symm)
  · refine (mul_le_mul_left (enorm_mixT_le d' v' hψ _ _ _) _).trans ?_
    rw [ENNReal.iSup_mul]
    exact iSup_le fun w => (hC₁ f hf x w).trans (mul_le_mul_left le_self_add _)
  · refine (hC₂ (val ψ d d' v v' x y) y (fun f g hf hg => ?_) (fun c f _ => ?_) (fun f _ => ?_)
      (fun ξ f hf => val_incX d d' v v' hψ x y ξ hf) f hf).trans (mul_le_mul_left le_add_self _)
    · rw [val, mixS_add d v hψ hf hg, mixT_add d' v' hψ (hmv f hf x) (hmv g hg x)]
      rfl
    · rw [val, mixS_smul, mixT_smul]
      rfl
    · exact (enorm_mixT_le d' v' hψ _ _ _).trans (iSup_le fun w => enorm_mixS_le d v hψ f x w)
  · exact rearrange _ _ _ _ _ hM

end GlobalTheory.Unf.DoubleSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsOpenLevelCompleteSobolevStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunctions_open_level_complete_sobolev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∃ f ∈ thetaLevel ψ S T U, ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.ThetaComplete.complete | exact GlobalTheory.ThetaComplete.complete | (intros; apply GlobalTheory.ThetaComplete.complete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimePlaceMemOrConjGenusTypePlaceSetStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimePlace_mem_or_conj_genusTypePlaceSet : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (resS D.host.F Q s = 0 ↔ resS D.host.F PP (sigInt (instOf D) s) = 0) := by
  first | exact @GlobalTheory.CoverConj.cover | exact GlobalTheory.CoverConj.cover | (intros; apply GlobalTheory.CoverConj.cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesProductNotMemSqPlaceStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimes_product_not_mem_sq_place : ∀ (D : D7) (Q : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := by
  first | exact @GlobalTheory.TypePrimeUnif.prod_not_mem_sq | exact GlobalTheory.TypePrimeUnif.prod_not_mem_sq | (intros; apply GlobalTheory.TypePrimeUnif.prod_not_mem_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundUniformWindowAndParams
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem vanishingGramBound_uniformWindow_and_weightData : (VanishingGramTermsBoundWindow → ∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ (VanishingGramTermsBoundParams → Led1 VanishingGramTermsBound) := by
  refine ⟨fun h c => ?_, fun h => ?_⟩
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT c h1 h2
    refine ⟨max a b, fun C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u _ t r s d e => ?_⟩
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    exact H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s d e
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT h1 h2
    exact ⟨max a b, fun C' Cl hC' hCl D large₂ X Y hF hI u _ t r s n d e =>
      H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s n d e⟩

end GlobalTheory.Core.Deg
end

