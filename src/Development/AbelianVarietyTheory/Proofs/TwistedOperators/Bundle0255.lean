import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0236
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorMemSpanLocalHeisenbergTranslates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExpStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviModulusOne_linearReductive_exp_mul_exp : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) → GlobalTheory.LinRed.IsLinRed (mats (leviOne ε W)) ∧ ∀ g ∈ mats (leviOne ε W), ∃ X Y : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) ∧ (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ mats (leviOne ε W)) ∧ g = NormedSpace.exp X * NormedSpace.exp Y := by
  first | exact @GlobalTheory.LeviPolar.isLinRed_leviOne | exact GlobalTheory.LeviPolar.isLinRed_leviOne | (intros; apply GlobalTheory.LeviPolar.isLinRed_leviOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.Chain.LiftConv

theorem liftInteg_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.Chain.LiftInteg D :=
  fun hP D => liftInteg_of_growth hP D (GlobalTheory.T.thetaKernel_moderateGrowth_with_seminorms D)

end GlobalTheory.Chain.LiftConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeil
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.SiegelSet.ConeConv

theorem lintegral_Ici_rpow {b p : ℝ} (hb : 0 < b) (hp : p < 0) :
    ∫⁻ x, (Set.Ici b).indicator (fun x => ENNReal.ofReal (x ^ (p - 1))) x = ENNReal.ofReal (b ^ p / (-p)) := by
  rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici.symm]
  have hlt : p - 1 < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hlt hb)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x (hx : b < x) =>
      Real.rpow_nonneg (le_of_lt (lt_trans hb hx)) _)), integral_Ioi_rpow_of_lt hlt hb]
  congr 1
  have : p - 1 + 1 = p := by ring
  rw [this, div_neg, neg_div]

theorem mem_cone_cons {m : ℕ} {c x : ℝ} (y : Fin (m + 1) → ℝ) :
    (Fin.cons x y : Fin (m + 2) → ℝ) ∈ GlobalTheory.SiegelSet.cone (m + 2) c ↔
      (0 < x ∧ c * y 0 ≤ x) ∧ y ∈ GlobalTheory.SiegelSet.cone (m + 1) c := by
  simp only [GlobalTheory.SiegelSet.cone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hpos, hstep, hlast⟩
    refine ⟨⟨by simpa using hpos 0, by simpa using hstep 0 1 (by simp)⟩, fun i => by simpa using hpos i.succ,
      fun i j hij => by simpa using hstep i.succ j.succ (by simp [hij]),
      fun i hi => by simpa using hlast i.succ (by simp; omega)⟩
  · rintro ⟨⟨h0, h01⟩, hpos, hstep, hlast⟩
    refine ⟨fun i => Fin.cases (by simpa using h0) (fun i => by simpa using hpos i) i, fun i j hij => ?_,
      fun i hi => ?_⟩
    · induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        induction i using Fin.cases with
        | zero =>
          have : j = 0 := Fin.ext (by simpa using hij)
          subst this; simpa using h01
        | succ i => simpa using hstep i j (by simpa using hij)
    · induction i using Fin.cases with
      | zero => simp at hi
      | succ i => simpa using hlast i (by simpa using hi)

theorem mem_cone_one {c x : ℝ} (hc : 0 < c) :
    (fun _ => x : Fin 1 → ℝ) ∈ GlobalTheory.SiegelSet.cone 1 c ↔ c ≤ x := by
  simp only [GlobalTheory.SiegelSet.cone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, _, hlast⟩
    exact hlast 0 rfl
  · intro h
    refine ⟨fun _ => lt_of_lt_of_le hc h, fun i j hij => ?_, fun _ _ => h⟩
    exact absurd hij (by omega)

theorem lintegral_cone_lt_top {c : ℝ} (hc : 0 < c) : ∀ (m : ℕ) (a : ℕ → ℝ),
    (∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a i < 0) →
    ∫⁻ t, (GlobalTheory.SiegelSet.cone (m + 1) c).indicator
      (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) t < ⊤ := by
  intro m
  induction m with
  | zero =>
    intro a ha
    have ha0 : a 0 < 0 := by simpa using ha 0 le_rfl
    change ∫⁻ t : Fin 1 → ℝ, (GlobalTheory.SiegelSet.cone 1 c).indicator
      (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) t < ⊤
    have key := (MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) ℝ)).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
      (fun t : Fin 1 → ℝ => (GlobalTheory.SiegelSet.cone 1 c).indicator
        (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) t)
    refine lt_of_eq_of_lt key.symm ?_
    have : ∀ x : ℝ, (GlobalTheory.SiegelSet.cone 1 c).indicator
        (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm x)
        = (Set.Ici c).indicator (fun x => ENNReal.ofReal (x ^ (a 0 - 1))) x := by
      intro x
      have hx : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm x = fun _ => x := by
        funext i; simp [MeasurableEquiv.funUnique_symm_apply]
      rw [hx]
      by_cases h : c ≤ x
      · rw [Set.indicator_of_mem ((mem_cone_one hc).2 h), Set.indicator_of_mem (Set.mem_Ici.2 h)]
        simp
      · rw [Set.indicator_of_notMem (fun h' => h ((mem_cone_one hc).1 h')),
          Set.indicator_of_notMem (fun h' => h (Set.mem_Ici.1 h'))]
    simp_rw [this]
    rw [lintegral_Ici_rpow hc ha0]
    exact ENNReal.ofReal_lt_top
  | succ m ih =>
    intro a ha
    have ha0 : a 0 < 0 := by simpa using ha 0 (Nat.zero_le _)
    set a' : ℕ → ℝ := fun i => if i = 0 then a 0 + a 1 else a (i + 1) with ha'
    have hsum : ∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a' i < 0 := by
      intro k hk
      have h := ha (k + 1) (by omega)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
      rw [Finset.sum_range_succ']
      simp only [ha', if_pos, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false] at *
      linarith
    set K : ℝ≥0∞ := ENNReal.ofReal (c ^ a 0 / (-a 0))
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0
    rw [← (MeasurePreserving.symm _ (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0)).lintegral_comp_emb
      e.symm.measurableEmbedding, Measure.volume_eq_prod, ← lintegral_prod_swap]
    refine lt_of_le_of_lt (lintegral_prod_le _) ?_
    have hpt : ∀ y : Fin (m + 1) → ℝ, ∫⁻ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
        (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (e.symm (Prod.swap (y, x)))
        ≤ K * (GlobalTheory.SiegelSet.cone (m + 1) c).indicator
          (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a' i.val - 1))) y := by
      intro y
      have he : ∀ x, e.symm (Prod.swap (y, x)) = Fin.cons x y := by
        intro x; simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero'] <;> rfl
      simp_rw [he]
      by_cases hy : y ∈ GlobalTheory.SiegelSet.cone (m + 1) c
      · have hy0 : 0 < y 0 := hy.1 0
        have hb : 0 < c * y 0 := mul_pos hc hy0
        set T : ℝ≥0∞ := ∏ i : Fin (m + 1), ENNReal.ofReal (y i ^ (a (i.val + 1) - 1))
        have hfun : ∀ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
            (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (Fin.cons x y)
            = (Set.Ici (c * y 0)).indicator (fun x => ENNReal.ofReal (x ^ (a 0 - 1))) x * T := by
          intro x
          by_cases hx : c * y 0 ≤ x
          · rw [Set.indicator_of_mem ((mem_cone_cons y).2 ⟨⟨lt_of_lt_of_le hb hx, hx⟩, hy⟩),
              Set.indicator_of_mem (Set.mem_Ici.2 hx), Fin.prod_univ_succ]
            simp [T, Fin.val_succ]
          · rw [Set.indicator_of_notMem (fun h' => hx ((mem_cone_cons y).1 h').1.2),
              Set.indicator_of_notMem (fun h' => hx (Set.mem_Ici.1 h')), zero_mul]
        simp_rw [hfun]
        rw [lintegral_mul_const' _ _ (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top),
          lintegral_Ici_rpow hb ha0, Set.indicator_of_mem hy]
        apply le_of_eq
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        have hrest : ∏ j : Fin m, ENNReal.ofReal (y j.succ ^ (a (j.succ.val + 1) - 1))
            = ∏ j : Fin m, ENNReal.ofReal (y j.succ ^ (a' j.succ.val - 1)) :=
          Finset.prod_congr rfl fun j _ => by simp [ha', Fin.val_succ]
        have h1 : 0 ≤ (c * y 0) ^ a 0 / (-a 0) := div_nonneg (Real.rpow_nonneg hb.le _) (by linarith)
        have h2 : 0 ≤ c ^ a 0 / (-a 0) := div_nonneg (Real.rpow_nonneg hc.le _) (by linarith)
        have h0 : ENNReal.ofReal ((c * y 0) ^ a 0 / (-a 0)) * ENNReal.ofReal (y 0 ^ (a ((0 : Fin (m + 1)).val + 1) - 1))
            = K * ENNReal.ofReal (y 0 ^ (a' (0 : Fin (m + 1)).val - 1)) := by
          simp only [K, ha', Fin.val_zero, zero_add, if_true]
          rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2]
          congr 1
          rw [Real.mul_rpow hc.le hy0.le, show a 0 + a 1 - 1 = (a 1 - 1) + a 0 by ring, Real.rpow_add hy0]
          ring
        rw [hrest, ← mul_assoc, ← mul_assoc, h0]
      · have hz : ∀ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
            (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (Fin.cons x y) = 0 :=
          fun x => Set.indicator_of_notMem (fun h' => hy ((mem_cone_cons y).1 h').2) _
        simp_rw [hz, lintegral_zero]
        exact bot_le
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ih a' hsum)

theorem measurableSet_cone (r : ℕ) (c : ℝ) : MeasurableSet (GlobalTheory.SiegelSet.cone r c) := by
  simp only [GlobalTheory.SiegelSet.cone, Set.setOf_and, Set.setOf_forall]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_const.mul (measurable_pi_apply j)) (measurable_pi_apply i)).inter
     (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_le measurable_const (measurable_pi_apply i)))

end GlobalTheory.SiegelSet.ConeConv

open GlobalTheory.SiegelSet.ConeConv in

theorem GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top : ∀ (F : Type) [Field F] [NumberField F] (n r d : ℕ) {c : ℝ}, 0 < c →
    d < 2 * (n - r) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n r d c hc hd
  have hf : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos
  cases r with
  | zero =>
    simp only [GlobalTheory.SiegelSet.modulus, Finset.univ_eq_empty, Finset.prod_empty, mul_one, inv_one, ENNReal.ofReal_one,
      lintegral_const, one_mul]
    rw [Measure.restrict_apply MeasurableSet.univ]
    change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) _ < ⊤
    rw [Measure.pi_of_empty]
    simp only [Set.univ_inter]
    exact measure_lt_top _ _
  | succ m =>
    set f := Module.finrank ℚ F with hfdef
    set a : ℕ → ℝ := fun i => (f : ℝ) * d - 2 * f * ((n : ℝ) - 2 * i - 1) with hadef
    have closed : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), a i = f * (k + 1) * (d - 2 * n + 2 * (k + 1)) := by
      intro k
      induction k with
      | zero => rw [Finset.sum_range_one]; simp only [hadef]; push_cast; ring
      | succ k ih => rw [Finset.sum_range_succ, ih]; simp only [hadef]; push_cast; ring
    have hsum : ∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a i < 0 := by
      intro k hk
      rw [closed]
      have h1 : d + 2 * (k + 1) < 2 * n := by omega
      have h2 : (d : ℝ) + 2 * (k + 1) < 2 * n := by exact_mod_cast h1
      exact mul_neg_of_pos_of_neg (mul_pos hf (by positivity)) (by linarith)
    have hmeas := measurableSet_cone (m + 1) c
    rw [setLIntegral_congr_fun hmeas (g := fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) ?_,
      ← lintegral_indicator hmeas]
    · exact lintegral_cone_lt_top hc m a hsum
    intro t ht
    have hpos : ∀ i, 0 < t i := ht.1
    dsimp only
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => pow_nonneg (hpos i).le _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hpos i).le _)]
    congr 1
    unfold GlobalTheory.SiegelSet.modulus
    rw [← hfdef]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hti := hpos i
    rw [← Real.rpow_natCast, ← Real.rpow_intCast,
      show a i.val - 1 = ((f * d : ℕ) : ℝ) - ((2 * (f : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1 by
        simp only [hadef]; push_cast; ring,
      Real.rpow_sub hti, Real.rpow_sub hti, Real.rpow_one]
    field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorMemSpanLocalHeisenbergTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → x ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T (wAt (.inl v) w) f₀) := by
  first | exact @GlobalTheory.LocalSpan.mem_span_local | exact GlobalTheory.LocalSpan.mem_span_local | (intros; apply GlobalTheory.LocalSpan.mem_span_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeLieWordNormBoundStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_lieWord_normBound : LieBound := by
  first | exact @GlobalTheory.SepReal.lieBound | exact GlobalTheory.SepReal.lieBound | (intros; apply GlobalTheory.SepReal.lieBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatCoordScalarMul
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CentreAvg

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_finite

variable {n : ℕ}

theorem ujMat_scalarMul (ε : Fin n → Bool) (z : Circle) (g : SUJ ε) :
    ujMat ε (scalarMul ε (z, g)) = (z : ℂ) • suMat ε g := by
  rw [GlobalTheory.SqIntSU.scalarMul_apply, map_mul,
    show ujMat ε (GlobalTheory.SqIntSU.unitScalar ε z) = (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) from rfl,
    Matrix.smul_mul, Matrix.one_mul]
  rfl

theorem matCoord_scalarMul (ε : Fin n → Bool) (z : Circle) (g : SUJ ε) :
    GlobalTheory.Orb.matCoord (ujMat ε) (scalarMul ε (z, g)) = (z : ℂ) • GlobalTheory.Orb.matCoord (suMat ε) g := by
  funext i j
  simp only [GlobalTheory.Orb.matCoord, ujMat_scalarMul, Pi.smul_apply, Matrix.smul_apply]

theorem avg_mem_ccMat : ∀ (n : ℕ) (ε : Fin n → Bool) (m : ℤ) (f : UJ ε → ℂ), f ∈ CcMat (ujMat ε) →
    (fun g : SUJ ε => ∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar) ∈ CcMat (suMat ε) := by
  intro n ε m f hf
  obtain ⟨hc, Φ, hΦ, e⟩ := hf
  refine ⟨?_, fun x => ∫ z, (z : ℂ) ^ m * Φ ((z : ℂ) • x) ∂circleHaar, ?_, ?_⟩
  ·
    let W : Set (UJ ε) := (fun p : Circle × UJ ε => (GlobalTheory.SqIntSU.unitScalar ε p.1)⁻¹ * p.2) '' (Set.univ ×ˢ tsupport f)
    have hW : IsCompact W := (isCompact_univ.prod hc.isCompact).image
      (((GlobalTheory.SqIntSU.continuous_unitScalar ε).comp continuous_fst).inv.mul continuous_snd)
    have hT : IsCompact ((Subtype.val : SUJ ε → UJ ε) ⁻¹' W) :=
      (GlobalTheory.SqIntSU.isClosed_special ε).isClosedEmbedding_subtypeVal.isCompact_preimage hW
    refine HasCompactSupport.intro hT fun g hg => ?_
    have h0 : ∀ z : Circle, f (scalarMul ε (z, g)) = 0 := by
      intro z
      refine image_eq_zero_of_notMem_tsupport fun hz => hg ?_
      refine ⟨(z, scalarMul ε (z, g)), ⟨trivial, hz⟩, ?_⟩
      show (GlobalTheory.SqIntSU.unitScalar ε z)⁻¹ * (GlobalTheory.SqIntSU.unitScalar ε z * (g : UJ ε)) = g
      exact inv_mul_cancel_left _ _
    simp only [h0, zero_mul, integral_zero]
  · have hφ : Continuous fun z : Circle => (z : ℂ) ^ m := by
      have : (fun z : Circle => (z : ℂ) ^ m) = fun z : Circle => ((z ^ m : Circle) : ℂ) := by
        funext z; rw [Circle.coe_zpow]
      rw [this]
      exact continuous_subtype_val.comp (continuous_zpow m)
    have hφc : HasCompactSupport fun z : Circle => (z : ℂ) ^ m :=
      HasCompactSupport.intro isCompact_univ fun x hx => (hx (Set.mem_univ x)).elim
    have hO : @OpensMeasurableSpace Circle _ GlobalTheory.SqIntSU.circleBorelMS :=
      @BorelSpace.opensMeasurable Circle _ GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace
    exact @GlobalTheory.Orb.contDiff_integral_param Circle ℂ (Fin n → Fin n → ℂ) _ GlobalTheory.SqIntSU.circleBorelMS hO _ circleHaar _
      _ _ _ _ _ (fun z : Circle => (z : ℂ)) continuous_subtype_val _ hφ hφc
      (fun q : (Fin n → Fin n → ℂ) × ℂ => Φ (q.2 • q.1)) (hΦ.comp (contDiff_snd.smul contDiff_fst))
  · intro g
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [e, matCoord_scalarMul, mul_comm]

end GlobalTheory.CentreAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientDerivativeFormula
section
open scoped InnerProductSpace

noncomputable section

open Matrix

namespace GlobalTheory.MatCoefDeriv

variable {n : ℕ} {ε : Fin n → Bool}

theorem exp_inUJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet ε) (t : ℝ) :
    Formalism.REAL.inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hJJ := GlobalTheory.GKLie.Jm_mul_self ε
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_right_inv hJJ
  have hu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨_, _, hJJ, hJJ⟩, rfl⟩
  have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
  have hXh : Xᴴ = Formalism.REAL.Jm ε * (-X) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [hJinv]
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = _ := by rw [h1, mul_neg, neg_mul]
  have hc : ((t : ℂ) • X)ᴴ = Formalism.REAL.Jm ε * (-((t : ℂ) • X)) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [conjTranspose_smul, hXh, Complex.star_def, Complex.conj_ofReal]
    simp [smul_neg, mul_smul_comm, smul_mul_assoc]
  unfold Formalism.REAL.inUJ
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ hu, hJinv]
  have hcomm : Commute (-((t : ℂ) • X)) ((t : ℂ) • X) := (Commute.refl _).neg_left
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε *
        NormedSpace.exp ((t : ℂ) • X)
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [mul_assoc (Formalism.REAL.Jm ε * _) (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, mul_one, mul_assoc]
    _ = Formalism.REAL.Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Rd_coef {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hρ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ)
    {u : H} (hu : Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ u) (w : H)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : ∀ g, Formalism.REAL.inUJ ε g → f g = ⟪w, ρ g u⟫_ℂ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet ε)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Rd X f g = ⟪w, ρ g (PI.PhMeasCore.dsig ρ X u)⟫_ℂ := by
  set γ : ℝ → H := fun t => ρ (NormedSpace.exp ((t : ℂ) • X)) u with hγ
  let L : H →L[ℝ] ℂ := ((innerSL ℂ w).comp (ρ g)).restrictScalars ℝ
  have hfun : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) = fun t => L (γ t) := by
    funext t
    have he := exp_inUJ hX t
    rw [hf _ (by
      unfold Formalism.REAL.inUJ at hg he ⊢
      rw [conjTranspose_mul]
      calc _ = (NormedSpace.exp ((t : ℂ) • X))ᴴ * (gᴴ * Formalism.REAL.Jm ε * g) *
            NormedSpace.exp ((t : ℂ) • X) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hg, he])]
    rw [hρ.2 g hg _ he]
    rfl
  have hdiff : DifferentiableAt ℝ γ 0 := by
    have h := GlobalTheory.GKLie.differentiableAt_orbit hu hX
    have e : γ = fun t : ℝ => ρ (NormedSpace.exp (t • X)) u := by
      funext t; simp only [hγ, Complex.coe_smul]
    rw [e]; exact h
  unfold Formalism.REAL.Rd
  rw [hfun]
  show deriv (⇑L ∘ γ) 0 = _
  rw [(L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hdiff.hasDerivAt).deriv]
  rfl

theorem cpart1_eq (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart1 ε Z = (1 / 2 : ℂ) • (Z + PI.DSInfCharCap.thetaJ ε Z) := by
  simp [Formalism.REAL.cpart1, PI.DSInfCharCap.thetaJ, sub_eq_add_neg]

theorem cpart2_eq (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart2 ε Z = (1 / (2 * Complex.I)) • (Z - PI.DSInfCharCap.thetaJ ε Z) := by
  simp [Formalism.REAL.cpart2, PI.DSInfCharCap.thetaJ, sub_eq_add_neg]

theorem Eab_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ →
    ∀ u : H, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ u → ∀ (w : H) (f : Matrix (Fin n) (Fin n) ℂ → ℂ),
    (∀ g, Formalism.REAL.inUJ ε g → f g = ⟪w, ρ g u⟫_ℂ) → ∀ (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ),
    Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε a b f g =
      ⟪w, ρ g (PI.DSInfCharCap.dsigC ε ρ (Matrix.single a b 1) u)⟫_ℂ := by
  intro n ε H _ _ ρ hρ u hu w f hf a b g hg
  have h1 := Rd_coef hρ hu w hf (GlobalTheory.GKLie.cre_mem (ε := ε) (Matrix.single a b 1)) hg
  have h2 := Rd_coef hρ hu w hf (GlobalTheory.GKLie.cim_mem (ε := ε) (Matrix.single a b 1)) hg
  unfold Formalism.REAL.Eab Formalism.REAL.Ec PI.DSInfCharCap.dsigC
  rw [cpart1_eq, cpart2_eq]
  unfold GlobalTheory.GKLie.cre at h1
  unfold GlobalTheory.GKLie.cim at h2
  rw [h1, h2, map_add, map_smul, inner_add_right, inner_smul_right]

end GlobalTheory.MatCoefDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactSpanHighestWeightLineStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxCompactSpan_highestWeight_line : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → (∀ v, ContinuousOn (fun g => ρ g v) (Formalism.MainNotions.S.UJset ε)) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε ρ S → ∀ (Λ : Fin n → ℝ) (w : H), w ∈ S → w ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ w → (∀ a b : Fin n, a < b → ε a = ε b → ∀ x ∈ S, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ (Λ + Formalism.REAL.root a b) x → x = 0) → (∀ (μ : Fin n → ℝ) (x : H), x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε) → x ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ x → Formalism.MainNotions.S.CDom ε μ Λ) ∧ (∀ x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ x → ∃ c : ℂ, x = c • w) := by
  first | exact @GlobalTheory.KSpanHighest.kspan_highest | exact GlobalTheory.KSpanHighest.kspan_highest | (intros; apply GlobalTheory.KSpanHighest.kspan_highest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemConjugatePlacesProductIdealOfForallConjPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_conjugatePlacesProductIdeal_of_forall_conj_place : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E), (∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) → x ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
  first | exact @GlobalTheory.LiftLevel.InfMem.main | exact GlobalTheory.LiftLevel.InfMem.main | (intros; apply GlobalTheory.LiftLevel.InfMem.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaMapModelsOfNoPairingCoversStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noThetaMap_models_of_noPairing_covers : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q : ℕ) (T₁ : GrpData p q) (R₁ : DSRep T₁) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (c₁ : ℚ) (b₁ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (u₁ : kfin M τ → R₁.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → PairNo a₁ R₁ → NoLift M τ A pt := by
  first | exact @GlobalTheory.ArchRec.NoLiftTransfer.noLift_of_pairNo | exact GlobalTheory.ArchRec.NoLiftTransfer.noLift_of_pairNo | (intros; apply GlobalTheory.ArchRec.NoLiftTransfer.noLift_of_pairNo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noThetaTensorIntertwiner_lowerTowerMembers : ∀ (X : ProvA), DiscreteSeriesBlattner X → admQ5 X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → TensNo (fockAct1 _ _ (al.length + de.length + t - i) (ga.length + be.length - i)) (fockAct2 _ _ _ _) (X.ds _ _ (lamA al be ga de))) ∧ ((∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → i ≤ al.length + be.length → i ≤ ga.length + de.length → TensNo (fockAct2 (al.length + be.length - i) (ga.length + de.length - i) _ _) (fockAct1 _ _ _ _) (X.ds _ _ (lamA' t al be ga de))) := by
  first | exact @GlobalTheory.LowerTower.no_map_lower | exact GlobalTheory.LowerTower.no_map_lower | (intros; apply GlobalTheory.LowerTower.no_map_lower <;> assumption)
end

