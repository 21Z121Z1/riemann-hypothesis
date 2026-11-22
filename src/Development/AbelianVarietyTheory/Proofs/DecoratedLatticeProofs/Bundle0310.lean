import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TraceInverseGramConjSmulEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelIsometryHalfLatticeVolumeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapContractionSupportFinitelyManyCells
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.LocFlat.CellsContr

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem opE_const_mul {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (C : ℂ)
    (F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun z => C * F z) x₀ = C * opE ψ ν p F x₀ := by
  simp only [opE]
  rw [← integral_const_mul]
  congr 1; funext e; ring

theorem opEFJ_const_mul {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ₀ : (n' → k) → ℂ) (C : ℂ)
    (F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν p Φ₀ (fun z => C * F z) x₀ = C * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν p Φ₀ F x₀ := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ, opE_const_mul]
  rw [← integral_const_mul]
  congr 1; funext u; ring

theorem om_eq_const_mul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ' : kˣ →* ℂˣ)
    (x : GL a k) (y : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ' x y Φ = fun z => ((μ' (Matrix.GeneralLinearGroup.det x) : ℂ) * ((μ' (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ)) *
      om 1 1 y (om 1 x 1 Φ) z := by
  funext z
  simp [om, nabs]
  ring
end
end GlobalTheory.LocFlat.CellsContr

open GlobalTheory.LocFlat.CellsContr in

theorem GlobalTheory.LocFlat.contr_support_finite_cells :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k),
    IsSelfDual ψ ν → ∀ (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] (c ρ : ℕ), c + 1 = 2 * ρ → ∀ (μ μ' : kˣ →* ℂˣ) (J : Subgroup (GL (n₂ ⊕ Fin c) k)),
    IsOpen (J : Set (GL (n₂ ⊕ Fin c) k)) → ∀ (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k))
    (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (a : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (x : GL (n₁ ⊕ Fin (c + 1)) k),
    ∃ T : Finset (GL (n₂ ⊕ Fin c) k), ∀ y : GL (n₂ ⊕ Fin c) k,
      GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) (om μ a x Φ₁.1)) (GlobalTheory.LocFlat.flRow ψ ν ρ (om μ' x y Φ₂.1)) ≠ 0 →
      ∃ r ∈ R k n₂ c ρ, ∃ t ∈ T, ∃ j ∈ J, y = r * t * j := by
  intro k _ _ _ _ _ _ ψ hψc hψ1 ν hsd n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ μ μ' J hJ Φ₁ Φ₂ a x
  classical
  haveI : ν.IsAddHaarMeasure := hsd.1
  have hρ1 : 1 ≤ ρ := by omega
  have hρc : ρ ≤ c := by omega
  have hker : IsOpen (((1 : kˣ →* ℂˣ).ker : Subgroup kˣ) : Set kˣ) := by
    rw [MonoidHom.ker_one]; exact isOpen_univ
  let Φ₁' : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k) := ⟨om μ a x Φ₁.1, om_mem_SB μ a x Φ₁.2⟩

  obtain ⟨m, Ψ, Φ₀, hdec⟩ := (GlobalTheory.LocFlat.ContrSum.contr_flat_eq_sum k ψ hψc hψ1 ν hsd n₀ n₁ n₂ c ρ hcρ μ Φ₁' Φ₂).2.2.2.1

  let Φ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := ⟨om 1 x 1 Φ₂.1, om_mem_SB 1 x 1 Φ₂.2⟩
  have hav := fun i => (GlobalTheory.PosOne.avg_self_and_props k n₂ n₁ c ρ hρ1 hρc ψ hψc hψ1 ν hsd 1 hker Φ).2 (Φ₀ i)

  have hcov : ∀ i, ∃ T : Finset (GL (n₂ ⊕ Fin c) k), GlobalTheory.PosOne.Covers ρ J T fun h =>
      opE ψ ν ρ (om 1 1 h (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν 1 ρ (Φ₀ i).1 Φ.1)) := fun i =>
    GlobalTheory.PosOne.covers_opE_finite k n₂ n₁ c ρ hρ1 hρc ψ hψc hψ1 ν 1 hker J hJ ⟨_, (hav i).1⟩
  choose Ti hTi using hcov
  refine ⟨Finset.univ.biUnion Ti, fun y hy => ?_⟩
  obtain ⟨X, hX⟩ : ∃ X, GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁'.1)
      (GlobalTheory.LocFlat.flRow ψ ν ρ (om μ' x y Φ₂.1)) X ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (funext h)
  let Φ₂' : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := ⟨om μ' x y Φ₂.1, om_mem_SB μ' x y Φ₂.2⟩
  have hid := (GlobalTheory.LocFlat.ContrSum.contr_flat_eq_sum k ψ hψc hψ1 ν hsd n₀ n₁ n₂ c ρ hcρ μ Φ₁' Φ₂').2.2.2.2
    m Ψ Φ₀ hdec X
  have hX' := hX
  change GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁'.1) (GlobalTheory.LocFlat.flRow ψ ν ρ Φ₂'.1) X ≠ 0 at hX'
  rw [hid] at hX'
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX'
  have hi2 : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν ρ (Φ₀ i).1 (om μ' x y Φ₂.1) X.2 ≠ 0 := right_ne_zero_of_mul hi
  rw [om_eq_const_mul, opEFJ_const_mul] at hi2
  have hi3 : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν ρ (Φ₀ i).1 (om 1 1 y Φ.1) X.2 ≠ 0 := right_ne_zero_of_mul hi2
  have hne : opE ψ ν ρ (om 1 1 y (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν 1 ρ (Φ₀ i).1 Φ.1)) ≠ 0 := by
    rw [(hav i).2.1 y]
    intro h0
    exact hi3 (congrFun h0 X.2)
  obtain ⟨t, ht, hmk⟩ := (hTi i).2 y hne
  obtain ⟨r, hr, j, hj, hy'⟩ := (DoubleCoset.eq _ _ t y).1 hmk.symm
  exact ⟨r, hr, t, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩, j, hj, hy'⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntries
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf

theorem mixS_decay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (N : ℕ), ∃ C : ℝ≥0, ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ * ENNReal.ofReal ((1 + realSize θ x) ^ N) ≤ C * supSob ψ θ N f := by
  intro D ψ hψ θ hθ S S₀ T ρ d v N
  obtain ⟨k, τs, zs, K, hK⟩ := GlobalTheory.T.adelicMatrixRealSize_le_realSymplecticPairing_sum D θ T ρ
  choose Z hZ using fun i => GlobalTheory.T.dualDirection_derivative_mixedCoordinate_bound D ψ hψ θ hθ S S₀ T ρ d v (τs i) (zs i)
  have hsf := GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws D ψ hψ θ hθ S T
  choose Cd hCd using fun i => (hsf.2.1 (τs i) (Z i)).2
  induction N with
  | zero =>
    refine ⟨1, fun f hf x w => ?_⟩
    rw [pow_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_one, one_mul]
    have hs : supSob ψ θ 0 f = ⨆ w, ‖f w‖ₑ := GlobalTheory.Size.wordSum_zero _ _ _
    rw [hs]
    unfold HypDec.mixS
    calc _ ≤ ∫⁻ a in v.𝓕, ‖heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0‖ₑ ∂v.μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ _ in v.𝓕, (⨆ w, ‖f w‖ₑ) ∂v.μ := lintegral_mono fun a => by
          rw [d.integrandS_eq, enorm_mul]
          have h1 : ‖ψ (symplOH S T (d.extY T a) (d.extX T x))‖ₑ = 1 := by
            rw [← ofReal_norm_eq_enorm, hψ.1.2.1, ENNReal.ofReal_one]
          rw [h1, one_mul]
          exact le_iSup (fun w => ‖f w‖ₑ) _
      _ = _ := by rw [setLIntegral_const, v.covol.2.2, mul_one]
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C + K.toNNReal * ∑ i, C * Cd i, fun f hf x w => ?_⟩
    set R := realSize θ x with hRdef
    have hR0 : 0 ≤ R := realSize_nonneg θ x
    set M := d.mixS T ψ v.μ v.𝓕 f x w
    set s := supSob ψ θ (N + 1) f
    have hNs : supSob ψ θ N f ≤ s := GlobalTheory.Size.wordSum_mono (Nat.le_succ N) f
    have hpow : ENNReal.ofReal ((1 + R) ^ (N + 1)) =
        ENNReal.ofReal ((1 + R) ^ N) + ENNReal.ofReal R * ENNReal.ofReal ((1 + R) ^ N) := by
      rw [← ENNReal.ofReal_mul hR0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hA : ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N) ≤ C * s := (hC f hf x w).trans (by gcongr)
    have hRle : ENNReal.ofReal R ≤ K.toNNReal * ∑ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
        ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
      refine (ENNReal.ofReal_le_ofReal (hK x)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul' (Finset.sum_nonneg fun i _ => abs_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
      rfl
    have hi : ∀ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
        ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) ≤
        C * Cd i * s := fun i => by
      have hDf := GlobalTheory.OrientedHeis.theta_dRho hθ hψ (τs i) (Z i) hf
      rw [← mul_assoc, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (abs_nonneg _)]
      calc _ ≤ ‖d.mixS T ψ v.μ v.𝓕 (dRho (heisO ψ S T) θ (τs i) (Z i) f) x w‖ₑ * ENNReal.ofReal ((1 + R) ^ N) := by
            gcongr
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (hZ i f hf x w)
        _ ≤ C * supSob ψ θ N (dRho (heisO ψ S T) θ (τs i) (Z i) f) := hC _ hDf x w
        _ ≤ C * (Cd i * s) := by gcongr; exact hCd i N f hf
        _ = C * Cd i * s := (mul_assoc _ _ _).symm
    calc ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ (N + 1))
        = ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N) + ENNReal.ofReal R * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) := by
          rw [hpow, mul_add, mul_left_comm]
      _ ≤ C * s + (K.toNNReal * ∑ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
            ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re|) * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) :=
          add_le_add hA (by gcongr)
      _ ≤ C * s + K.toNNReal * ∑ i, (C * Cd i * s : ℝ≥0∞) := by
          rw [mul_assoc, Finset.sum_mul]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) zero_le)
      _ = _ := by
          push_cast
          rw [add_mul, mul_assoc, Finset.sum_mul]

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHalfPointTranslatesLastFrameRow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

theorem neg_wRow_half_rd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf p.e ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) ∧ ∀ i j, rd β γ₀ ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) i j = Sum.elim (fun _ => 0) (fun _ => -t j) i := by
  intro D k _ _ _ _ p n n'' _ _ _ _ S₀ A L W₀ o ζ β γ γ₀ hsum t
  have hes : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.neg_apply, wRow, Matrix.of_apply, mul_left_comm, mul_neg, hes, mul_neg]
  · set c : Fin S₀.rank → k := fun i => p.pr (ratV (vecB o ζ) i) with hc
    have hmap : Matrix.map (o.jB * -wRow p ζ β t : Mx D S₀.rank W₀.rank) p.pr = -vecMulVec c (t ᵥ* β.b') := by
      refine Matrix.ext fun a b => ?_
      rw [Matrix.map_apply, Matrix.mul_apply, map_sum, Matrix.neg_apply, vecMulVec_apply, hc]
      simp only [ratV, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.neg_apply, wRow, Matrix.of_apply, map_neg, p.pr_sec, mul_neg, mul_assoc]
      rfl
    have hcol : (γ₀.b' *ᵥ c) i = Sum.elim (fun _ => 0) (fun _ => 1) i := by
      have h := congrFun (congrFun γ₀.b'b i) (Sum.inr 0)
      rw [hsum, Matrix.mul_apply] at h
      simp only [fromCols_apply_inr, replicateCol_apply] at h
      refine h.trans ?_
      rcases i with i | i
      · simp
      · obtain rfl := Subsingleton.elim i 0
        simp
    rw [rd, hmap, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, β.b'b,
      Matrix.vecMul_one, Matrix.neg_apply, vecMulVec_apply, hcol]
    rcases i with i | i <;> simp

end GlobalTheory.FinPl.LineAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormSqThetaLocalDatumAtTwistPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
noncomputable section

namespace GlobalTheory.ThetaNormTwist

theorem normSq_thetaLocalDatum_at_twistPlace_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (f₀ : WO S T → ℂ) (m : Measure (WO S T)) (X : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) m X → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) → ∀ r : ℕ, r ≤ S.rank → r ≤ T.rank → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ (onHalf φ S T (frCo φ βS) (frCo φ βT) e (phiQ v r mu)) x → nrm2 m X x = zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (T.rank - r)))⁻¹ := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT f₀ m X hB hcov hfS hfT PP v φ e he hP hA r hrS hrT ξ mu hmu x hx
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  obtain ⟨⟨Tm, hTm⟩, hxall⟩ := hx
  have hxT := hxall Tm hTm
  have hco := (GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he (frCo φ βS) (frCo φ βT)).1
  let ν : Measure (Fv D.host.F v) := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  obtain ⟨hv0, hvT, hiso⟩ := GlobalTheory.PlaceIsometry.placeModel_isometry D ψ θ S T sS sT ΛS ΛT f₀ m X hB hcov v e he.1
    T.rank S.rank (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.mapCo φ S T (frCo φ βS) (frCo φ βT)) hco Tm hTm ν hν
  obtain ⟨hip, hSB⟩ := GlobalTheory.T.split_weil_phi_inner_product D PP v φ hP S.rank T.rank r hrS hrT ξ mu hmu ν hν

  obtain ⟨⟨a0, ha0, -, hmax, himg⟩, -⟩ :=
    GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hB.2.2.1 hB.2.2.2.1 hfS hfT v φ e he
  have hval : Valued.v (rdQ φ a0) = 1 := by
    obtain ⟨⟨a1, ha1, h1⟩, hle⟩ := hA
    exact le_antisymm (hle a0 ha0) (h1 ▸ hmax a1 ha1)
  rw [hval] at himg
  have key := hiso _ hSB _ hSB
  rw [himg, hip] at key
  rw [← GlobalTheory.PlaceTensor.onHalf_eq_pull] at key
  rw [← hxT] at key
  have hne : ((GlobalTheory.SplitWeil.volM ν (Fin T.rank) (Fin S.rank) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal : ℂ) ≠ 0 := by
    rw [← himg]
    exact_mod_cast ENNReal.toReal_ne_zero.mpr ⟨hv0, hvT⟩
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO m X x x = ((nrm2 m X x : ℝ) : ℂ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO nrm2
    rw [← integral_complex_ofReal]
    congr 1
    funext w
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [e2] at key
  push_cast at key
  have key2 := mul_left_cancel₀ hne key
  apply Complex.ofReal_injective
  rw [key2]
  push_cast
  ring

end GlobalTheory.ThetaNormTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOComb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockComb

theorem om_pureTensorO_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ sS sT BS BT (e : WO S T →₀ ℂ) (f₀ f : WO S T → ℂ) (x : ℂ), IsFinComb e → IsThetaFunO ψ S T f₀ → IsThetaFunO ψ S T f → ∀ b ∈ GfC S, ∀ b' ∈ GfC T, om (b, b') f = x • comb ψ S T e f₀ → ∀ P, ∀ a ∈ GinfC S, ∀ a' ∈ GinfC T, om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT f P) = x • comb ψ S T e (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) ∧ ∀ (N : Lat S) (N' : Lat T), Vac ψ S T N N' (fun _ => True) f₀ → Vac ψ S T N N' (fun _ => True) (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) := by
  intro D ψ θ S T χS χT om hθ hW sS sT BS BT e f₀ f x he hf₀ hf b hb b' hb' hfx P a ha a' ha'
  have hψ : IsStdChar D ψ (-1) := hW.std

  have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT b b'
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.one_mul]) f hf P
  have hth₀ : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f₀ P) :=
    (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT 1 1
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f₀ hf₀ P).1

  have hcomb : comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) =
      pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
    let q := e.support.equivFin
    have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
      (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
    have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
      intro g
      rw [← Finset.sum_coe_sort e.support]
      exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
    simp only [comb]
    rw [h1, h1]
    exact key
  refine ⟨?_, fun N N' hv => ?_⟩
  · have e1 : ((a * b, a' * b') : GA D S × GA D T) = (a, a') * (b, b') := rfl
    rw [e1, map_mul, Module.End.mul_apply, hfin.2, hfx, GlobalTheory.FiniteFock.pureTensorO_smul, ← hcomb, map_smul,
      GlobalTheory.FrComb.om_comb hW ha ha' he hth₀]
  · refine ⟨hW.om_pres _ _ hth₀, GlobalTheory.FrComb.latVac_om hW ha ha' hth₀ ?_⟩
    have fix : ∀ u ∈ latO S T (N : Set _) (N' : Set _) (fun _ => True), heisO ψ S T u f₀ = f₀ →
        heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT f₀ P := by
      intro u hu h0
      have := ((GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ f₀ hf₀).2 u (GlobalTheory.SplitScalar.latO_fin hu)).2 sS BS sT BT P
      rw [← this, h0]
    exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hv.2.1 u hu),
      fun e' he' u hu hh => fix u hu (hv.2.2 e' he' u hu hh)⟩

end GlobalTheory.FockComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OtherPlacesConvolutionFiniteAwayOrthogonal
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

namespace GlobalTheory.QVal.InnerSupp

variable {D : D7}

theorem placeIdem_self {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hαα : α * α = α := by
    apply RestrictedProduct.ext
    intro w
    change evalV D.host.F w (α * α) = evalV D.host.F w α
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, mul_one]
    · rw [h0 w hw, zero_mul]
  show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), α) = ((0 : Ainf D.host.F), α)
  rw [Prod.mk_mul_mk, mul_zero, hαα]

theorem idem_sq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) :
    (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨ε, hε, heq⟩ := q.above
  rw [heq, ← map_mul, placeIdem_self hε]

theorem support_aconv {G : Type} [AddMonoid G] (P : G → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b)) :
    ∀ l : List (G →₀ ℂ), (∀ c ∈ l, ∀ u ∈ c.support, P u) → ∀ u ∈ (aconv l).support, P u := by
  classical
  intro l
  induction l with
  | nil =>
    intro _ u hu
    have h := Finsupp.support_single_subset (show u ∈ (Finsupp.single (0 : G) (1 : ℂ)).support from hu)
    rw [Finset.mem_singleton] at h
    subst h
    exact h0
  | cons e l ih =>
    intro hl u hu
    have hu' : u ∈ (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).support := hu
    have h1 := Finsupp.support_sum hu'
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g, hg, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨h, hh, h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    subst h5
    exact hadd g h (hl e (List.mem_cons.2 (Or.inl rfl)) g hg)
      (ih (fun c hc => hl c (List.mem_cons.2 (Or.inr hc))) h hh)

theorem side {A T : HSp D} (E₀ : AE D) (hc : cA D E₀ = E₀) (hsq : E₀ * E₀ = E₀) (c₀ : WO A T →₀ ℂ)
    (l : List (WO A T →₀ ℂ)) (h₀ : ∀ x ∈ c₀.support, IsHalf E₀ x)
    (hl : ∀ c ∈ l, ∀ u ∈ c.support, (∀ a b, E₀ * u a b = 0) ∧ u.map (infPart D) = 0) :
    IsFinComb (aconv l) ∧ (∀ u ∈ (aconv l).support, IsHalf (1 - E₀) u) ∧
      ∀ x ∈ c₀.support, ∀ y ∈ (aconv l).support, symplO A T x y = 0 := by
  have key := support_aconv (fun u : WO A T => (∀ a b, E₀ * u a b = 0) ∧ u.map (infPart D) = 0)
    ⟨fun a b => by rw [Matrix.zero_apply, mul_zero], by ext a b; simp⟩
    (fun u u' hu hu' => ⟨fun a b => by rw [Matrix.add_apply, mul_add, hu.1 a b, hu'.1 a b, add_zero], by
      ext a b
      have e1 := congrFun (congrFun hu.2 a) b
      have e2 := congrFun (congrFun hu'.2 a) b
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.add_apply] at e1 e2 ⊢
      rw [(infPart D).map_add, e1, e2, add_zero]⟩) l hl
  have half : ∀ u ∈ (aconv l).support, IsHalf (1 - E₀) u := fun u hu a b => by
    rw [sub_mul, one_mul, (key u hu).1 a b, sub_zero]
  refine ⟨fun u hu => (key u hu).2, half, fun x hx y hy => ?_⟩
  exact GlobalTheory.HeisComb.symplO_half A T E₀ (1 - E₀) x y hc (by rw [mul_sub, mul_one, hsq, sub_self]) (h₀ x hx) (half y hy)

end GlobalTheory.QVal.InnerSupp

open GlobalTheory.QVal.InnerSupp in

theorem GlobalTheory.QVal.inner_supp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ ∀ x ∈ (Q 0).D₁.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)).support, symplO _ _ x y = 0) ∧ (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ ∀ x ∈ (Q 0).D₂.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)).support, symplO _ _ x y = 0) := by
  intro D ψ σ S r Q hinj
  have hv : ∀ i : Fin r, (Q 0).q.v ≠ (Q i.succ).q.v := fun i h => Fin.succ_ne_zero i (hinj h).symm
  obtain ⟨hc, -, horth⟩ := GlobalTheory.PlaceIdemFacts.idem_facts D (Q 0).k (Q 0).q
  have hsq := idem_sq (Q 0).q
  have kill : ∀ (i : Fin r) {m n : ℕ} (u : Mx D m n), IsHalf ((Q i.succ).q.e + cA D (Q i.succ).q.e) u →
      (∀ a b, ((Q 0).q.e + cA D (Q 0).q.e) * u a b = 0) ∧ u.map (infPart D) = 0 := by
    intro i m n u hu
    obtain ⟨-, hinf, -⟩ := GlobalTheory.PlaceIdemFacts.idem_facts D (Q i.succ).k (Q i.succ).q
    refine ⟨fun a b => ?_, (hinf (fun _ => True) trivial m n u hu).2⟩
    rw [← hu a b, ← mul_assoc, horth (Q i.succ).k (Q i.succ).q (hv i), zero_mul]
  refine ⟨side _ hc hsq (Q 0).D₁ _ (fun x hx => (Q 0).dat₁.1 x hx) ?_, side _ hc hsq (Q 0).D₂ _ (fun x hx => (Q 0).dat₂.1 x hx) ?_⟩
  · intro c hc' u hu
    simp only [List.mem_ofFn] at hc'
    obtain ⟨i, rfl⟩ := hc'
    exact kill i u ((Q i.succ).dat₁.1 u hu)
  · intro c hc' u hu
    simp only [List.mem_ofFn] at hc'
    obtain ⟨i, rfl⟩ := hc'
    exact kill i u ((Q i.succ).dat₂.1 u hu)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLinearRelationDensityOfUnfoldingStepsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_linear_relation_density_of_unfolding_steps : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (G : ∀ i, (t (s i)).CC j), (∀ s, (t s).Is) → (∀ i a, IsContAut (c.X j) (φ i a)) → ∀ (W W' : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W' S') (It' : PolF D W'.rank (c.V (j + 1)).rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT (c.M (j + 1))), GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) M' It' → (∀ P₁ P₂ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 (c.It j P₁ (It' P₂ v))) = 0) → ∀ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 v) = 0 := by
  first | exact @GlobalTheory.SeeSaw.perF_rel_of_steps | exact GlobalTheory.SeeSaw.perF_rel_of_steps | (intros; apply GlobalTheory.SeeSaw.perF_rel_of_steps <;> assumption)
end

