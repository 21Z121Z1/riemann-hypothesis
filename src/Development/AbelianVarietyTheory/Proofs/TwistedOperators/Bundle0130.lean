import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0243
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0096
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesIntegrableCoefficientProjector
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0062
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicPointExistsIsotropicReductionOfSmallS
section
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

noncomputable section

namespace GlobalTheory.DeepPoint

open Formalism.L2.SG.Pf.unitaryCongruence in

theorem kg_one (I : AutInst) (m : ℕ) : (1 : I.Gf) ∈ I.Kg m :=
  ⟨K_one I, fun y _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩

open Formalism.L2.SG.Pf.unitaryCongruence in

theorem kg_mul (I : AutInst) (m : ℕ) {x y : I.Gf} (hx : x ∈ I.Kg m) (hy : y ∈ I.Kg m) : x * y ∈ I.Kg m := by
  refine ⟨K_mul I hx.1 hy.1, fun v hv => ?_⟩
  obtain ⟨z, hz, hyz⟩ := hy.2 v hv
  obtain ⟨z', hz', hxz⟩ := hx.2 v hv
  refine ⟨I.fmat x *ᵥ z + z', add_mem (K_mv I hx.1 hz) hz', ?_⟩
  have e : (I.fmat (x * y) - 1) *ᵥ v = I.fmat x *ᵥ ((I.fmat y - 1) *ᵥ v) + (I.fmat x - 1) *ᵥ v := by
    rw [fmat_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.one_mulVec]
    abel
  rw [e, hyz, hxz, Matrix.mulVec_smul, smul_add]

open Formalism.L2.SG.Pf.unitaryCongruence in

theorem kg_inv (I : AutInst) (m : ℕ) {k : I.Gf} (hk : k ∈ I.Kg m) : k⁻¹ ∈ I.Kg m := by
  refine ⟨K_inv I hk.1, fun y hy => ?_⟩
  obtain ⟨z, hz, hkz⟩ := hk.2 y hy
  refine ⟨-(I.fmat k⁻¹ *ᵥ z), neg_mem (K_mv I (K_inv I hk.1) hz), ?_⟩
  have h1 : I.fmat k⁻¹ * I.fmat k = 1 := fmat_inv_mul I k
  have e : (I.fmat k⁻¹ - 1) *ᵥ y = -(I.fmat k⁻¹ *ᵥ ((I.fmat k - 1) *ᵥ y)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [e, hkz, Matrix.mulVec_smul, smul_neg]

theorem isIsot_span (I : AutInst) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : R ≠ ⊥)
    (hiso : ∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) :
    I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
  first
  | exact @_root_.GlobalTheory.HermitianFormLinearity.main
  | exact _root_.GlobalTheory.HermitianFormLinearity.main
  | (apply _root_.GlobalTheory.HermitianFormLinearity.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianFormLinearity.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianFormLinearity.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianFormLinearity.main ..)

theorem exists_step (I : AutInst) (x : I.GA) (q : ℕ) (hn : 1 ≤ I.n)
    (hrk : ∀ v, rkR (I.ε v) ≤ q) (hl : least I x < 1 / 2) :
    ∃ (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi : ℝ),
      IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R ∧ R ≠ ⊥ ∧ R ≤ stepLt I x (1 / 2) ∧
      R ≤ lamX I x ∧ 0 < hi ∧ largestSize (bas I) (frm I x) R ≤ hi ∧
      (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) ∧
      hi ≤ (2 * least I x) ^ ((1 : ℝ) / q) * lo ∧ hi ^ 2 ≤ (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  obtain ⟨⟨a, S, τ, hF⟩, -, hspec⟩ := GlobalTheory.PointFlag.flag_spec I x
  have hpiece := (hspec a S τ hF).1
  have ha0 := ((hspec a S τ hF).2 hn).1
  have hτ0 := ((hspec a S τ hF).2 hn).2
  obtain ⟨hS0, hSmono, hSlast, hτmono, hτ, -⟩ := hF
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (ha0.1 h) (not_le.2 hl)
    · exact h
  have hrkS : ∀ i : Fin (a + 1), (i : ℕ) ≤ rkK (S i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have := (hpiece i).2.1
      simp only [Fin.coe_castSucc] at ih
      simp only [Fin.val_succ]
      omega
  have haq : a ≤ q := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h1 := hrkS (Fin.last a)
    rw [hSlast] at h1
    have h2 := (GlobalTheory.FlagIso.flag_isotropic I x).2.1 v
    simp only [Fin.val_last] at h1
    exact h1.trans (h2.trans (hrk v))
  set τ' : ℕ → ℝ := fun i => if h : i < a then τ ⟨i, h⟩ else 1 / 2 with hτ'
  have hτ'pos : ∀ i ≤ a, 0 < τ' i := by
    intro i _
    simp only [hτ']
    split_ifs with h
    · exact (hτ ⟨i, h⟩).1
    · norm_num
  have hτ'lt : ∀ i < a, τ' i < τ' (i + 1) := by
    intro i hi
    simp only [hτ', dif_pos hi]
    split_ifs with h
    · exact hτmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    · exact (hτ ⟨i, hi⟩).2.1
  have hτ'a : τ' a = 1 / 2 := by simp [hτ']
  have hτ'0 : τ' 0 = least I x := by
    simp only [hτ', dif_pos (show 0 < a by omega)]
    exact hτ0 (by omega)
  obtain ⟨b, hb, hratio, hsq⟩ := GlobalTheory.exists_consecutive_ratio_le_rpow a q τ' ha haq hτ'pos hτ'lt hτ'a
  rw [hτ'0] at hratio hsq
  set i : Fin a := ⟨b, hb⟩ with hi_def
  have hib : τ' b = τ i := by simp [hτ', hb, i]
  refine ⟨S i.succ, τ' (b + 1), τ i, ?_, ?_, ?_, ?_, (hτ i).1, ?_, ?_, ?_, ?_⟩
  · rw [(hτ i).2.2.1]; exact (GlobalTheory.CountSteps.steps I x _ (hτ i).1).1
  · intro h
    have := hSmono (Fin.succ_pos i)
    rw [hS0, h] at this
    exact lt_irrefl _ this
  · rw [← hSlast]; exact hSmono.monotone (Fin.le_last _)
  · rw [(hτ i).2.2.1]; exact sSup_le fun N hN => hN.1
  · exact (hpiece i).2.2.1.le
  · intro N hN hNL
    by_cases hb1 : b + 1 < a
    · have eS : S i.succ = S (Fin.castSucc (⟨b + 1, hb1⟩ : Fin a)) := congrArg S (Fin.ext (by simp [i]))
      have e : τ' (b + 1) = τ ⟨b + 1, hb1⟩ := by simp [hτ', hb1]
      rw [e, eS]
      rw [eS] at hN
      exact (hpiece ⟨b + 1, hb1⟩).2.2.2.1 N hN hNL
    · have hba : b + 1 = a := by omega
      have e : τ' (b + 1) = 1 / 2 := by rw [hba, hτ'a]
      have eS : S i.succ = stepLt I x (1 / 2) := by
        rw [← hSlast]; exact congrArg S (Fin.ext (by simp [i, hba]))
      rw [e, eS]
      rw [eS] at hN
      exact (GlobalTheory.CountSteps.steps I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.1 N hN hNL
  · rw [← hib]
    have hpos := hτ'pos (b + 1) (by omega)
    rwa [div_le_iff₀ hpos] at hratio
  · rw [← hib]; exact hsq

theorem deep_point : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ I.n →
    (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset,
      ∃ k ∈ I.Kg g, ∃ (u : I.Ginf) (A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ),
        (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧
        (∀ v, uMat (u v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ m * x = γ * x * (u, k) ∧
        Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤
          (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  intro I x g q hg _ hn hrk hl
  obtain ⟨R, lo, hi, hsat, hR0, hRS, hRL, hhi, hlarge, hlo, hhl, hh2⟩ := exists_step I x q hn hrk hl
  have hisoR : ∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 :=
    fun y hy z hz => (GlobalTheory.FlagIso.flag_isotropic I x).1 y (hRS hy) z (hRS hz)
  have hperp : R ≤ perpIn I x R := fun y hy =>
    Submodule.subset_span ⟨hRL hy, fun s hs => hisoR s hs y hy⟩
  have hWiso : I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := isIsot_span I R hR0 hisoR
  refine ⟨_, hWiso, fun m hm => ?_⟩
  obtain ⟨⟨N, hN⟩, -, hsplit, hdense, -⟩ := GlobalTheory.UnipApprox.strong_approximation I _ hWiso
  have hU : {c : I.Gf | x.2⁻¹ * c * x.2 ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    have ho : IsOpen (I.Kg g) := I.topf_open g hg
    have hc : Continuous fun c : I.Gf => x.2⁻¹ * c * x.2 :=
      (continuous_const.mul continuous_id).mul continuous_const
    refine (ho.preimage hc).mem_nhds ?_
    show x.2⁻¹ * 1 * x.2 ∈ I.Kg g
    rw [mul_one, inv_mul_cancel]
    exact kg_one I g
  obtain ⟨γ, ⟨hγF, hγN⟩, hγU⟩ := hdense _ hU m hm
  have hm'N : γ⁻¹ * m ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
    rw [← hN] at hγN hm ⊢
    exact N.mul_mem (N.inv_mem hγN) hm
  have hν := (hsplit _ hm'N).1
  obtain ⟨γ', ⟨hγ'F, -⟩, hγ'K, A, Z, hAZ, heq, hbd, -⟩ :=
    GlobalTheory.SmallFund.small_fundamental_set I x g R lo hi _ hg hsat hR0 hperp hhi hlarge hlo hhl hh2 _ hν
  have hk : (x⁻¹ * γ' * x).2⁻¹ * (x.2⁻¹ * (γ⁻¹ * m).2 * x.2) ∈ I.Kg g :=
    kg_mul I g (kg_inv I g hγ'K) hγU
  refine ⟨γ * γ', Formalism.MainNotions.LeviCoordinates.rrg_mul_mem I hγF hγ'F, _, hk,
    (γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1, A, Z, hAZ, fun v => ?_, ?_, hbd⟩
  · have e : uMat (((γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1) v) =
        uMat ((γ'.1 v * x.1 v)⁻¹) * (uMat ((γ⁻¹ * m).1 v) * uMat (x.1 v)) := by
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_assoc]
      rfl
    rw [e, heq v]
    have e2 : uMat (γ'.1 v) * uMat (x.1 v) = uMat (γ'.1 v * x.1 v) := rfl
    have e3 : uMat ((γ'.1 v * x.1 v)⁻¹) * uMat (γ'.1 v * x.1 v) = 1 := by
      show uMat ((γ'.1 v * x.1 v)⁻¹ * (γ'.1 v * x.1 v)) = 1
      rw [inv_mul_cancel]
      rfl
    rw [e2, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat ((γ'.1 v * x.1 v)⁻¹)), e3, Matrix.one_mul]
  · have h2 : γ' * x * ((γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1,
        (x⁻¹ * γ' * x).2⁻¹ * (x.2⁻¹ * (γ⁻¹ * m).2 * x.2)) = (γ⁻¹ * m) * x := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul]
        group
      · simp only [Prod.snd_mul, Prod.snd_inv]
        group
    calc m * x = γ * ((γ⁻¹ * m) * x) := by group
      _ = γ * γ' * x * _ := by rw [← h2]; simp only [mul_assoc]

end GlobalTheory.DeepPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtEqInfMat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilDeriv

theorem compAt_mt_eq_infMat {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g) = infMat D.sp.cm.sig V.gram (θ τ) g := by
  ext i j
  simp only [compAt, Formalism.L2.Theta.mt, infMat, matHom, Matrix.map_apply]
  rfl

theorem om_dRho_infMat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (g : GA D S) (h : GA D T) τ z f, IsThetaFunO ψ S T f → om (g, h) (Datum.dRho (heisO ψ S T) θ τ z f) = Datum.dRho (heisO ψ S T) θ τ (infMat D.sp.cm.sig T.gram (θ τ) h * z * infMat D.sp.cm.sig S.gram (θ τ) g⁻¹) (om (g, h) f) := by
  intro D ψ S T χS χT om hW θ hθ g h τ z f hf
  rw [← compAt_mt_eq_infMat θ τ T h, ← compAt_mt_eq_infMat θ τ S g⁻¹]
  exact GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ z hf

end GlobalTheory.WeilDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  first | exact @GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | exact GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | (intros; apply GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesIntegrableCoefficientProjectorStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_integrableCoefficient_projector : ∀ X : ProvA, DiscreteSeriesPositivity X → CoverHaarIntegration X → DiscreteSeriesHighestVector X := by
  first | exact @GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity | exact GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity | (intros; apply GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace Matrix

namespace GlobalTheory.GelfandKazhdan

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_comp {π : Representation ℂ G V} (φ : G →* G) (hφ : Function.Surjective φ)
    (h : π.IsIrreducible) : Representation.IsIrreducible (π.comp φ : Representation ℂ G V) := by
  let E : Subrepresentation (π.comp φ : Representation ℂ G V) ≃o Subrepresentation π :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g, rfl⟩ := hφ g
        exact U.apply_mem_toSubmodule g hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation π) := h
  exact E.isSimpleOrder

variable [TopologicalSpace G]

theorem isAdmissible_comp {π : Representation ℂ G V} (φ : G →* G) (Φ : G ≃ₜ G) (hΦ : ∀ x, Φ x = φ x)
    (h : IsAdmissible π) : IsAdmissible (π.comp φ : Representation ℂ G V) := by
  have e0 : (φ : G → G) = Φ := funext fun x => (hΦ x).symm
  have hc : Continuous φ := e0 ▸ Φ.continuous
  have ho : IsOpenMap φ := e0 ▸ Φ.isOpenMap
  refine ⟨fun v => (h.1 v).preimage hc, fun K hKo hKc => ?_⟩
  have e : fixed (π.comp φ : Representation ℂ G V) K = fixed π (K.map φ) := by
    ext v
    constructor
    · rintro hv ⟨_, g, hg, rfl⟩
      exact hv ⟨g, hg⟩
    · intro hv g
      exact hv ⟨_, g.1, g.2, rfl⟩
  rw [e]
  exact h.2 _ (ho _ hKo) (hKc.image hc)

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]

theorem smoothTrace_comp {π : Representation ℂ G V} (φ : G →* G) (Φ : G ≃ₜ G) (hΦ : ∀ x, Φ x = φ x)
    (hμ : μ.map Φ = μ) (h : IsAdmissible π) {f : G → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) :
    smoothTrace (π.comp φ : Representation ℂ G V) μ (f ∘ Φ) = smoothTrace π μ f := by
  have h' := isAdmissible_comp φ Φ hΦ h
  unfold smoothTrace
  congr 1
  ext v
  refine eq_of_forall_dual fun l => ?_
  rw [h'.1.map_smoothOp (hf.comp_continuous Φ.continuous) (hc.comp_homeomorph Φ), h.1.map_smoothOp hf hc]
  conv_rhs => rw [← hμ]
  rw [Φ.measurableEmbedding.integral_map]
  simp [hΦ]

theorem smoothTrace_conj [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {π : Representation ℂ G V}
    (h : IsAdmissible π) {K : Subgroup G} (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (g : G) :
    smoothTrace π μ (fun x => f (g * x * g⁻¹)) = smoothTrace π μ f := by
  let Φ : G ≃ₜ G := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  let φ : G →* G := (MulAut.conj g).toMonoidHom
  have hΦ : ∀ x, Φ x = φ x := fun _ => rfl
  have hμ : μ.map Φ = μ :=
    ((measurePreserving_mul_right μ g⁻¹).comp (measurePreserving_mul_left μ g)).map_eq
  rw [← smoothTrace_comp φ Φ hΦ hμ h hf hc]
  refine (h.smoothTrace_eq_of_equiv (isAdmissible_comp φ Φ hΦ h).1 (hf.comp_continuous Φ.continuous)
    (hc.comp_homeomorph Φ) ho hK
    (LinearEquiv.ofLinear (π g) (π g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
      (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])) fun x v => ?_).symm
  change π g (π x v) = π (g * x * g⁻¹) (π g v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

end General

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.SplitFlip

theorem invTranspose_invTranspose (n : ℕ) (R : Type) [CommRing R] (g : GL (Fin n) R) :
    invTranspose n R (invTranspose n R g) = g :=
  Units.ext (transpose_transpose _)

theorem continuous_invTranspose (n : ℕ) (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (invTranspose n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem equiv_contra (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    Nonempty (Representation.Equiv (π.comp (invTranspose n k)) (contra π)) := by
  borelize k
  letI : MeasurableSpace (GL (Fin n) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  have hb : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
    intro U hU
    obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
    exact ⟨J, h1, isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩
  let μ : Measure (GL (Fin n) k) := haarVol (KO k (Fin n))
  haveI : μ.IsHaarMeasure := isHaarMeasure_haarVol isOpen_KO le_rfl
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_haar μ
  have := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have hinv := invTranspose_invTranspose n k
  have hcont := continuous_invTranspose n k
  let Ψ : GL (Fin n) k ≃ₜ* GL (Fin n) k :=
    { toFun := invTranspose n k, invFun := invTranspose n k, left_inv := hinv, right_inv := hinv,
      map_mul' := map_mul _, continuous_toFun := hcont, continuous_invFun := hcont }
  let Φ : GL (Fin n) k ≃ₜ GL (Fin n) k := Ψ.toHomeomorph
  have hΦ : ∀ x, Φ x = invTranspose n k x := fun _ => rfl
  have hμ : μ.map Φ = μ := by
    have : (μ.map Φ).IsHaarMeasure := Ψ.isHaarMeasure_map μ
    refine @eq_haarVol _ _ _ _ _ _ _ _ _ _ _ this _ isOpen_KO le_rfl ?_
    refine (Measure.map_apply (μ := μ) Φ.measurable isOpen_KO.measurableSet).trans ?_
    have e : Φ ⁻¹' (KO k (Fin n) : Set (GL (Fin n) k)) = KO k (Fin n) := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, mem_KO_iff]
      exact ⟨fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩, fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩⟩
    rw [e]
    exact haarVol_self isOpen_KO le_rfl
  obtain ⟨hca, hct⟩ := GlobalTheory.T.isAdmissible_contra_and_smoothTrace_inv _ μ hb V π ha
  let T : SB (GL (Fin n) k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => smoothTrace π μ φ.1
      map_add' := fun φ ψ => ha.smoothTrace_add φ.2.1 φ.2.2 ψ.2.1 ψ.2.2 isOpen_KO isCompact_KO
      map_smul' := fun c φ => ha.smoothTrace_smul φ.2.1 φ.2.2 isOpen_KO isCompact_KO c }
  have hT := GlobalTheory.T.transpose_invariant_of_conj_invariant_distribution_GL k (Fin n) T fun g φ ψ h => by
    change smoothTrace π μ ψ.1 = smoothTrace π μ φ.1
    rw [show ψ.1 = _ from funext h]
    exact smoothTrace_conj ha isOpen_KO isCompact_KO φ.2.1 φ.2.2 g
  refine GlobalTheory.T.nonempty_equiv_of_smoothTrace_eq_admissible _ μ hb V _ _ _ (isAdmissible_comp _ Φ hΦ ha) hca
    (isIrreducible_comp _ (fun g => ⟨_, hinv g⟩) hi)
    ((GlobalTheory.T.smoothContragredient_irreducible_and_reflexive _ hb V V π π ha ha).1 hi) fun f hf hc => ?_
  have h1 := hf.comp_continuous Φ.continuous
  have h2 := hc.comp_homeomorph Φ
  have h3 := smoothTrace_comp _ Φ hΦ hμ ha h1 h2
  rw [show (f ∘ Φ) ∘ Φ = f from funext fun x => congrArg f (hinv x)] at h3
  rw [h3, hct f hf hc]
  refine hT ⟨fun g => f g⁻¹, hf.comp_continuous continuous_inv, hc.comp_homeomorph (Homeomorph.inv _)⟩
    ⟨f ∘ Φ, h1, h2⟩ fun x y hxy => congrArg f ?_
  rw [eq_inv_iff_mul_eq_one]
  apply Units.ext
  change (x⁻¹).valᵀ * y.val = 1
  rw [hxy, ← transpose_mul, Units.mul_inv, transpose_one]

end GlobalTheory.GelfandKazhdan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCovBySubmodule
section
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.IrrSubquot

theorem exists_covBy_submodule {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M] :
    ∃ S T : Submodule R M, T ⋖ S := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  haveI := CompleteLattice.Iic_coatomic_of_compact_element (Submodule.singleton_span_isCompactElement (R := R) m)
  rcases IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Set.Iic (Submodule.span R {m})) with h0 | ⟨c, hc, -⟩
  · have h1 : (⊥ : Submodule R M) = Submodule.span R {m} := congrArg Subtype.val h0
    exact absurd (Submodule.mem_span_singleton_self m) (by rw [← h1]; simpa using hm)
  · refine ⟨Submodule.span R {m}, c.1, lt_of_le_of_ne c.2 fun h => hc.1 (Subtype.ext h), ?_⟩
    intro x h1 h2
    have := congrArg Subtype.val (hc.2 ⟨x, h2.le⟩ h1)
    exact h2.ne this

theorem exists_irreducible_subquotient : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), Nontrivial V → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (σ : Representation ℂ G Y), σ.IsIrreducible ∧ IsSubquotient σ ρ := by
  intro G _ V _ _ ρ hV
  haveI : Nontrivial ρ.asModule := hV
  obtain ⟨S, T, h⟩ := exists_covBy_submodule (R := MonoidAlgebra ℂ G) (M := ρ.asModule)
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have h' : e.symm T ⋖ e.symm S :=
    ⟨e.symm.lt_iff_lt.2 h.1, fun c h1 h2 => h.2 (c := e c) (by simpa using e.lt_iff_lt.2 h1)
      (by simpa using e.lt_iff_lt.2 h2)⟩
  refine ⟨_, _, _, subQuot (e.symm S) (e.symm T), isIrreducible_subQuot h', e.symm S,
    ⟨Submodule.mkQ _, fun g => ?_⟩, Submodule.mkQ_surjective _⟩
  ext x
  rfl

end GlobalTheory.IrrSubquot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfIndexEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain

theorem exists_intertwiner_of_index_eq {D : D7} (hP : ItPair D) (k : Fin D.R.m) (hk : ChainPar D k)
    (V W : HSp D) (a b : ℕ) (ha : a = k) (hb : b = k + 1)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (hθ : IsInfFam θ) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω f, IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  subst ha hb
  obtain ⟨It, -, hIt⟩ := hP k V W M M' θ ψ hθ hk
  exact ⟨It, hIt⟩

theorem innerIntertwiners_of_pair (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (hP : ItPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : StepsOK R) :
    ItYSt R := by
  intro k hk
  have hk0 : k < D.R.m := Nat.lt_of_succ_lt hk
  obtain ⟨It, hIt⟩ := exists_intertwiner_of_index_eq hP ⟨k, hk0⟩ (hC _) (Yc D k) (Yc D (k + 1))
    (min k D.R.m) (min (k + 1) D.R.m) (Nat.min_eq_left hk0.le) (Nat.min_eq_left hk.le)
    (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ
  refine ⟨It, fun t => ?_⟩
  obtain ⟨hω, hv⟩ := hS.1 t ⟨k, hk0⟩ hk
  exact hIt _ _ hω hv

end GlobalTheory.Chain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianStdIsometryOfRationalIsometryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianStdIsometry_of_rationalIsometry : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  first | exact @GlobalTheory.StdIsom.stdIsomSt_of_rationalSt | exact GlobalTheory.StdIsom.stdIsomSt_of_rationalSt | (intros; apply GlobalTheory.StdIsom.stdIsomSt_of_rationalSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMultMapRightTranslateFiniteAdelicNormalizerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMultMap_rightTranslate_finiteAdelic_normalizer : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (κ : GA D V), κ ∈ GfC V → (∀ k ∈ J, κ⁻¹ * k * κ ∈ J ∧ χ (κ⁻¹ * k * κ) = χ k) → ∀ T : MMap M, IsMultMap θ M J χ T → ∃ T' : MMap M, IsMultMap θ M J χ T' ∧ ∀ v, T' v = rTr V κ (T v) := by
  first | exact @GlobalTheory.isMultMap_rightTranslate_finite | exact GlobalTheory.isMultMap_rightTranslate_finite | (intros; apply GlobalTheory.isMultMap_rightTranslate_finite <;> assumption)
end

