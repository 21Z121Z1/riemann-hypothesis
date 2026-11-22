import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0558
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0034
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0530
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0548
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0559
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteLiftCommLevelPrimeOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftsAtLevel

variable {D : D7}

theorem combAt_mono {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) {S T : HSp D} {c : WO S T →₀ ℂ} (hc : CombAt P c) :
    CombAt P' c :=
  fun u hu a b => AllBij.idAt_mono h (hc u hu a b)

theorem comb_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hstd : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {c : WO S T →₀ ℂ} (hc : IsFinComb c) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (comb ψ S T c f) φ = comb ψ S T c (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  classical
  have e : ∀ g : WO S T → ℂ, comb ψ S T c g =
      ∑ i, c (c.support.equivFin.symm i) • heisO ψ S T (c.support.equivFin.symm i) g := by
    intro g
    unfold comb
    rw [← Finset.sum_coe_sort c.support]
    exact Fintype.sum_equiv c.support.equivFin _ _ (fun x => by simp)
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hstd hθ sS sT BS BT f hf c.support.card
    (fun i => c (c.support.equivFin.symm i)) (fun i => (c.support.equivFin.symm i : WO S T))
    (fun i => hc _ (c.support.equivFin.symm i).2) φ).1
  rw [e, e, key]

theorem vac_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {x : DefSp S} {y : DefSp T}
    {f₀ : WO S T → ℂ} (hvac : IsVacO ψ θ S T x.s y.s x.L y.L f₀) (P : Pl D → Prop)
    (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    Vac ψ S T x.L y.L P (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := by
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hvac.1 hvac.2.inf x.s x.B y.s y.B hvac.2.theta φ
  have hle : latO S T (x.L : Set _) (y.L : Set _) P ≤ latO S T (x.L : Set _) (y.L : Set _) fun _ => True :=
    GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  refine ⟨hth φ, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hu' := hle hu
    exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu' 2)) (hvac.2.lat.1 u hu') φ
  · have hu' := hle hu
    exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth u
      (GlobalTheory.VacGood.infPart_latO hu') (hvac.2.lat.2 e he u hu' hh) φ

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sOp_ram {ι : Type} {p : ι → SplitPt D k} (hinj : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ₀ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ₀ i) 1) (ε : 𝓀[k]ˣ) (i : ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', RamAt (β i') (Q i') φ) :
    IsContAut S (sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ) ∧
      ∀ i', RamAt (β i') (Q i') (sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ) := by
  obtain ⟨hbij, -, c, c', hc, -⟩ := GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n q (χ₀ i) (hχ i) _ rfl ε S (β i) (Q i)
  have hT : ∀ φ, sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) ε φ = AllBij.act (Finsupp.mapDomain (β i).gl c) φ :=
    fun φ => (hc φ).trans (AllBij.sum_rep_eq _ _ _)
  have hC := AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) c
  refine ⟨by rw [hT]; exact AllBij.isContAut_act _ hφ.1, fun i' => ?_⟩
  rcases eq_or_ne i' i with rfl | hne
  · exact hbij.mapsTo (hφ.2 i')
  · rw [hT]
    exact AllBij.ramAt_act _ _ _ (fun x hx g => AllBij.grpAt_comm S (fun e => hne (hinj e)) (hC x hx)
      (AllBij.gl_mem _ g)) (hφ.2 i')

theorem foldr_ram {ι : Type} {p : ι → SplitPt D k} (hinj : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ₀ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ₀ i) 1) (ε : ι → 𝓀[k]ˣ) (l : List ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', RamAt (β i') (Q i') φ) :
    IsContAut S (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) (ε i) φ') φ) ∧
      ∀ i', RamAt (β i') (Q i') (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ₀ i) (hχ i) q) (ε i) φ') φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact sOp_ram hinj β Q q χ₀ hχ (ε i) i ih

theorem isIdele_idele (p : SplitPt D k) (x : kˣ) : p.IsIdele x (p.idele x) := by
  unfold SplitPt.IsIdele
  rw [SplitPt.idele_val]
  ring

end Local

theorem chrPow_mul_neg (μ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) : chrPow μ a e * chrPow μ a (-e) = 1 := by
  simp only [chrPow, ← Circle.coe_mul, _root_.zpow_neg, mul_inv_cancel, Circle.coe_one]

end GlobalTheory.SeeSaw.LiftsAtLevel

namespace GlobalTheory.SeeSaw.LiftsAtLevel

open GlobalTheory.FinPl.ValDbl in

theorem pt_over {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {v : VCom c} {o : TDat c k ι} {t : Tup c} {w : VTup t} (hc : c.Is) (ht : t.Is) (hv : v.Is) (hVF : VForm v w)
    (hSh : ShapeOff v o) (j : ℕ) (hj : j < D.R.m) (α : t.Ch j) (γ : t.Ch (j + 1))
    (P : PolF D (c.X (j + 1)).rank (c.X j).rank) (i : ι) :
    ∃ f₀, Over c.ψ (o.β j i) (o.β (j + 1) i) (c.x j).L (c.x (j + 1)).L f₀ (phiOne (o.Q j i) (o.Q (j + 1) i))
      ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) := by
  have hk := ht.ker j hj α γ
  have hvac : IsVacO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).L (c.x (j + 1)).L (c.vac j) := hk.vac
  have hstd := hc.std
  have hxS := hc.x j hj.le
  have hxT := hc.x (j + 1) hj
  set f := pureTensorO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).B (c.x (j + 1)).B (c.vac j) P
    with hfdef
  have hfV : ∀ Pp, Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L Pp f := fun Pp => vac_pureTensorO hvac Pp P
  have hpt : (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P =
      comb c.ψ _ _ (w.dQ j α γ) (comb c.ψ _ _ (v.dG j) (comb c.ψ _ _ (v.dT j) f)) := by
    show pureTensorO c.ψ c.θ (c.X j) (c.X (j + 1)) (c.x j).s (c.x (j + 1)).s (c.x j).B (c.x (j + 1)).B
      (comb c.ψ _ _ (t.dd j α γ) (c.vac j)) P = _
    rw [comb_pureTensorO hstd hc.inf _ _ _ _ hvac.2.theta (c := t.dd j α γ) hk.fin P]
    exact hVF.dd j hj α γ f (hfV fun _ => True).1
  have hrep := hSh.rep j hj f (hfV _)
  have hpl : Places o.p o.I (· ∈ v.tP) :=
    ⟨hSh.pre.nodup, hSh.pre.all, hSh.pre.inj, hSh.pre.tP, fun i => (hSh.pre.char i).2⟩
  have hAC := (GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι o.p o.I (· ∈ v.tP) hpl (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ hstd
    (c.X j) (c.X (j + 1)) (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L hxS.sd hxT.sd
    (fun i => phiOne (o.Q j i) (o.Q (j + 1) i))).2.2
  have hdG : CombAt (fun x => ¬ x ∈ v.tP) (v.dG j) :=
    combAt_mono (fun x hx ht' => Finset.disjoint_left.1 hv.disj hx ht') (hv.atG j).2.1
  have hdQ : CombAt (fun x => ¬ x ∈ v.tP) (w.dQ j α γ) :=
    combAt_mono (fun x hx ht' => Finset.disjoint_left.1 hVF.disjT hx ht') ((hVF.atQ j).2.2 α γ)
  obtain ⟨hV1, hO1⟩ := hAC (v.dG j) hdG f (hfV _)
  obtain ⟨hV2, hO2⟩ := hAC (w.dQ j α γ) hdQ _ hV1
  have hO := hO2 _ (hO1 _ hrep)
  obtain ⟨g, hg, -⟩ := overAll_last hstd (fun i => (hSh.pre.char i).2) hSh.pre.inj o.I hSh.pre.nodup _ _
    (fun j' => vac_at ((hSh.pre.tP _).2 ⟨j', rfl⟩) hV2) hO i (hSh.pre.all i)
  exact ⟨g, hpt ▸ hg⟩

end GlobalTheory.SeeSaw.LiftsAtLevel

open GlobalTheory.SeeSaw.LiftsAtLevel in

theorem GlobalTheory.SeeSaw.liftS_of_exact : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom c) (o : TDat c k ι) (t : Tup c) (w : VTup t), LiftExact D → c.Is → t.Is → v.Is → VForm v w → ShapeOff v o → (∀ j, j < D.R.m → ∃ μ, IsWeilDatumO c.ψ _ _ μ μ (t.kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v) → LiftS o t := by
  intro D c k _ _ _ _ ι v o t w hLE hc ht hv hVF hSh hμ j hj α γ P φ hφ
  obtain ⟨μ, hW, hU⟩ := hμ j hj
  have hxS := hc.x j hj.le
  have hxT := hc.x (j + 1) hj
  have hk := ht.ker j hj α γ
  have hφ' : IsContAut (c.X j) φ ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ := hφ
  set F := (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P with hF
  have hOv := pt_over hc ht hv hVF hSh j hj α γ P
  have hlift : ∀ φ', (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) P φ' =
      liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ' F := fun φ' => rfl

  have hram : ∀ φ', (IsContAut (c.X j) φ' ∧ ∀ i, RamAt (o.β j i) (o.Q j i) φ') →
      liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ' F ∈ o.Ram (j + 1) := by
    intro φ' h'
    refine ⟨?_, fun i => ?_⟩
    · rw [← hlift]
      exact (GlobalTheory.SeeSaw.LiftSumProof.liftSum D c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) hxS hxT _ hk P).2.1 φ' h'.1
    · obtain ⟨f₀, hf₀⟩ := hOv i
      obtain ⟨c₀, -, H⟩ := GlobalTheory.T.ramifiedThetaLift_commutes_splitPlace_operators D k (o.p i) (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) o.q (o.χ i) (o.hχ i) c.ψ
        (c.X j) (c.X (j + 1)) hxS.cpt (c.x j).vol μ μ (t.kom j) hW (hU i) (hU i) (o.β j i) (o.β (j + 1) i) (o.Q j i)
        (o.Q (j + 1) i)
      exact (H _ _ f₀ F hf₀ φ' (h'.2 i)).1
  refine ⟨by rw [hlift]; exact hram φ hφ', fun η => ?_⟩

  have key : ∀ l : List ι, l.foldr (fun i φ' => sOp (o.β (j + 1) i) (o.Q (j + 1) i) o.q (resChar (o.χ i) (o.hχ i) o.q) (η i) φ')
        (liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕 φ F) =
      ((((resCard k : ℝ) ^ ((((c.X (j + 1)).rank : ℝ) - (c.X j).rank) / 2) : ℝ) : ℂ) ^ l.length) •
        liftT (t.kom j) (c.x j).vol.μ (c.x j).vol.𝓕
          (l.foldr (fun i φ' => sOp (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (η i) φ') φ) F := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldr_cons, List.length_cons]
      rw [ih, GlobalTheory.FinPl.ValDbl.sOp_smul]
      obtain ⟨e, -, hE⟩ := hLE k (o.p i) o.q (o.χ i) (o.hχ i)
      obtain ⟨f₀, hf₀⟩ := hOv i
      have hr := (foldr_ram hSh.pre.inj (o.β j) (o.Q j) o.q o.χ o.hχ η l hφ').2 i
      rw [hE (Fin (c.X (j + 1)).rank) (Fin (c.X j).rank) c.ψ (c.X j) (c.X (j + 1)) hxS.cpt (c.x j).vol μ μ (t.kom j) hW
        (hU i) (hU i) (o.β j i) (o.β (j + 1) i) (o.Q j i) (o.Q (j + 1) i) _ (isIdele_idele (o.p i) o.q.unit) _ _ f₀ F hf₀ _ hr
        (η i), mul_assoc, chrPow_mul_neg, mul_one, smul_smul, pow_succ]
      simp only [Fintype.card_fin]
  simp only [TDat.S, TDat.cL, hlift]
  exact key o.I
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantBesselSecondStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStep_integrand_leftInvariant_bessel_second : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (r * q₂) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  first | exact @GlobalTheory.DStepCell.LeftSecond.integ_left_second | exact GlobalTheory.DStepCell.LeftSecond.integ_left_second | (intros; apply GlobalTheory.DStepCell.LeftSecond.integ_left_second <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantFourierJacobiFirStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStep_integrand_leftInvariant_fourierJacobi_first : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (r * q₁) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  first | exact @GlobalTheory.DStepCell.LeftOne.main | exact GlobalTheory.DStepCell.LeftOne.main | (intros; apply GlobalTheory.DStepCell.LeftOne.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepSmallPairsValueAllGluedSplitPlacesProo
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VertexAllProof

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem over_self {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {p : SplitPt D k}
    {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] {α : Frame p S m'} {β : Frame p T m}
    {g f : WO S T → ℂ} {Φ : Matrix m m' k → ℂ} (h : Over ψ α β LS LT g Φ f) (hU : p.UnitAA)
    (ΛS : Submodule 𝒪[k] (m' → k)) (ΛT : Submodule 𝒪[k] (m → k)) (hLS : α.IsLat LS ΛS) (hLT : β.IsLat LT ΛT) :
    Over ψ α β LS LT g (latInd ΛS ΛT) g := by
  obtain ⟨hS, hT, hvac, -, ⟨Tm, hTm⟩, -⟩ := h
  have hE := GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p m m' S T α β LS LT hS hT hU ΛS ΛT hLS hLT
  refine ⟨hS, hT, hvac, GlobalTheory.T.indicator_hom_selfDual_components_schwartzBruhat D k p m m' S T α β LS LT hS hT ΛS ΛT hLS hLT, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
  have hv := hT'.vac
  rw [one_smul] at hv
  change g = T' (extFun α β (latInd ΛS ΛT))
  rw [hE, hv]

theorem overAll_nil {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type}
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}
    {LS : Lat S} {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type}
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}
    {LS : Lat S} {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ} {i : ι} {l : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: l) f f' ↔ ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' :=
  Iff.rfl

end GlobalTheory.FinPl.VertexAllProof

open GlobalTheory.FinPl.VertexAllProof in

theorem GlobalTheory.FinPl.vertexAll : ∀ D : D7, GlobalTheory.FinPl.VertexAll D := by
  intro D k _ _ _ _ ι p I P hPl q ψ χ hχ hc
  have hvg := fun i => GlobalTheory.T.gluedPlace_doubleStep_exact_signed_constant D k (p i) q ψ (χ i) (hχ i) (hc i)
  refine ⟨fun i => (hvg i).choose, fun i => (hvg i).choose_spec.1, ?_⟩
  intro n n' n'' _ _ _ _ _ _
  have hrc := fun i => (hvg i).choose_spec.2 n n' n''
  choose r e hr hre using hrc
  refine ⟨r, e, hr, ?_⟩
  intro σ B J B' s₁ s₂ l vL hunr a b a' M₀ M₁ M₂ _ _ _ hgl Ξ₁ Ξ₂ _ _
  have hP : ∀ i, P (p i).v := fun i => (hPl.mem _).2 ⟨i, rfl⟩
  have hmaps : ∀ (ls : List ι) (φ : GA D B.A → ℂ), a.Ram φ →
      a.Ram (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun i => (hvg i).choose) ls φ) := fun ls φ hφ =>
    (GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D k ι p q χ hχ (fun i => (hvg i).choose) n' B.A B.V₀ a hPl.inj ls).1.mapsTo hφ
  have hV : ∀ ls : List ι, ∀ Ξ₁' Ξ₂',
      OverAll ψ a.α₀ b.β M₀ M₁ (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) ls Ξ₁ Ξ₁' →
      OverAll ψ b.β a'.α₀ M₁ M₂ (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) ls Ξ₂ Ξ₂' →
      ∀ φ, a.Ram φ → hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ =
        (ls.map fun i => (r i : ℂ) * chrPow s₁.χW ((p i).idele q.unit) (e i)).prod •
          hand0 s₁ s₂ l vL (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun i => (hvg i).choose) ls φ) Ξ₁' Ξ₂' := by
    intro ls
    induction ls with
    | nil =>
      intro Ξ₁' Ξ₂' h1 h2 φ _
      rw [overAll_nil.1 h1, overAll_nil.1 h2, List.map_nil, List.prod_nil, one_smul]
      rfl
    | cons i ls ih =>
      intro Ξ₁' Ξ₂' h1 h2 φ hφ
      obtain ⟨g₁, hg₁, hΞ₁'⟩ := overAll_cons.1 h1
      obtain ⟨g₂, hg₂, hΞ₂'⟩ := overAll_cons.1 h2
      have ho₁ := over_self hΞ₁' (hgl i).1.unit _ _ (hgl i).1.lat (hgl i).2.2
      have ho₂ := over_self hΞ₂' (hgl i).1.unit _ _ (hgl i).2.2 (hgl i).2.1.lat
      obtain ⟨F, hF, hFP⟩ := (hmaps ls φ hφ).2 i
      have hv := hre i (a.P i) (b.Q i) (a'.P i) σ B J B' s₁ s₂ l vL (hunr _ (hP i)).1 (hunr _ (hP i)).2 (a.α i)
        (a.α₀ i) (b.β i) (a'.α i) (a'.α₀ i) (hgl i).1.sum (hgl i).2.1.sum M₀ M₁ M₁ M₂ g₁ g₁ Ξ₁' g₂ g₂ Ξ₂' ho₁ hΞ₁'
        ho₂ hΞ₂' F hF
      have hsop := ((GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n' q (χ i) (hχ i) _ rfl ((hvg i).choose) B.A (a.α i) (a.P i)).2.1 F hF).2
      rw [ih g₁ g₂ hg₁ hg₂ φ hφ, ← hFP, hv, ← hsop, hFP, smul_smul, List.map_cons, List.prod_cons, mul_comm]
      rfl
  intro Ξ₁' Ξ₂' h1 h2 φ hφ
  exact hV I Ξ₁' Ξ₂' h1 h2 φ hφ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlacedBesselPoints
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem oneBlock_lev {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : LevDat D.host.E ℂ V.rank)
    (hn : V.rank ≤ Λ.r) (hs : Λ.s = 0) (hQ : Λ.Q = ∅) (κ : GA D V) :
    (κ ∈ levS V β Λ ↔ κ ∈ GfC V ∧ Lev.finE V κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) β ∧
      Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) β Λ (Lev.finE V κ) ∈ Λ.P.H) ∧
    Lev.levChi V β Λ κ = ((Formalism.L2.DIV.ext1 Λ.P.H Λ.P.chi
      (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) β Λ (Lev.finE V κ)) : ℂˣ) : ℂ) := by
  refine ⟨⟨fun h => ?_, fun h => ⟨h.1, ?_⟩⟩, ?_⟩
  · have hl := mem_lev.1 h.2
    exact ⟨h.1, (mem_parLev.1 hl.1).2.1, hl.2⟩
  · refine mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ κ, h.2.1,
      fun PP _ => GlobalTheory.SeeConjRead.blockTri_blkOf_top _ hn _, fun PP hPP => ?_⟩, h.2.2⟩
    rw [hQ] at hPP
    exact absurd hPP (Finset.notMem_empty _)
  · unfold Lev.levChi levFn
    simp only [hs, hQ, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]

set_option maxHeartbeats 1000000 in

theorem exists_isAt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ u (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B → GlobalTheory.MiTop.Framed B → ∃ a₀ a, IsAt f B a₀ a := by
  intro D L hT Gi Gl Kc Yd cX ex W hW u f B hP hF
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.Core.Mi.PinModel.exists_transport_adelic_correction (W.S.tr u)
  obtain ⟨a, haf, hac, hSt⟩ := GlobalTheory.T.exists_central_adapted_element W hW u f B hP hF a₀ ha₀
  have hM := GlobalTheory.T.central_adapted_element_property W hW u f B hP a₀ ha₀ a haf hac hSt
  have hC := GlobalTheory.T.central_adapted_element_value W hW u f B hP a₀ ha₀ a haf hac hSt
  have hb : (show GA D (D.sp.Y 0) from f.g.b 0) ∈ GfC (D.sp.Y 0) := by
    obtain ⟨k, _, _, _, _, ι, v, o, n, G, pl, -, hv, ht, -⟩ := hP
    have h1 := hv.b 0
    rw [ht.b 0] at h1
    exact h1
  have hx : (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) ∈ GfC (D.sp.Y 0) :=
    (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff W.S.X W.Q.instEq _).1 (by simp)
  have htf : tOf f B a₀ a ∈ GfC (D.sp.Y 0) :=
    mul_mem (mul_mem (inv_mem hx) (GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o (mul_mem ha₀.1 haf))) hb
  have hn : (D.sp.Y 0).rank ≤ D.R.r := by
    rw [rank_eq W.S.X W.Q.instEq, W.S.X.n_eq]
  refine ⟨a₀, a, ha₀, haf, hac, htf, fun κ => ?_⟩
  rw [inv_inv]
  have h1 := GlobalTheory.FrameConj.levS_conj_frame (D.sp.Y 0) (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from GlobalTheory.LevZero.datZero W) (tOf f B a₀ a) htf κ
  generalize tOf f B a₀ a * κ * (tOf f B a₀ a)⁻¹ = y at h1 ⊢
  obtain ⟨h2, h3⟩ := oneBlock_lev (D.sp.Y 0) (GlobalTheory.LevZero.frAt f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from GlobalTheory.LevZero.datZero W) hn rfl rfl y
  have h4 : κ ∈ rJ W ↔ y ∈ levS (D.sp.Y 0) (GlobalTheory.LevZero.frAt f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from GlobalTheory.LevZero.datZero W) := h1.1
  have h5 : Lev.levChi (D.sp.Y 0) (GlobalTheory.LevZero.frAt f B a₀ a)
    (show LevDat D.host.E ℂ (D.sp.Y 0).rank from GlobalTheory.LevZero.datZero W) y = rChi W κ := h1.2
  rw [h2] at h4
  refine ⟨h4.trans ⟨fun h => (hM y h.1 h.2.1).2 h.2.2, fun h => ?_⟩, fun hk => ?_⟩
  · obtain ⟨hf, hs⟩ := (hSt y).2 ⟨h.1, h.2.1⟩
    exact ⟨hf, hs, (hM y hf hs).1 h⟩
  · obtain ⟨hf, hs, hp⟩ := h4.1 hk
    exact (hC y hf hs hp ((hM y hf hs).2 hp)).trans (h3.symm.trans h5)

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawBetweenBasePointsMovedPointsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_law_between_basePoints_movedPoints : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (κ₀ : TC.GA B (B.R.N i)) (κ₀' : TC.GA B (B.R.N (i + 1))), finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 = κ₀.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 = κ₀'.1 → ∃ (q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)), TC.PtOf (κ₀ * A.kb i α) q.1.1 ∧ TC.PtOf (κ₀' * A.kb (i + 1) γ) q'.1.1 ∧ cosetIn q = cosetIn (A.p0 i α) ∧ cosetIn q' = cosetIn (A.p0 (i + 1) γ) ∧ ∀ w : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)), (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) q q' w) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ) w) := by
  first | exact @GlobalTheory.AdForm.MovedLaw.moved_law | exact GlobalTheory.AdForm.MovedLaw.moved_law | (intros; apply GlobalTheory.AdForm.MovedLaw.moved_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_handedFunction_vanishing_period_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (f : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W f → ∀ r ∈ jacGrp J.d, r ∈ grpAt J.W P → (flatBF s (s.om (1, r) f) = 0 ↔ flatBF s f = 0)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (f : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V f → ∀ r ∈ besGrp B.d B.o, r ∈ grpAt B.V P → (handFB s vL Y (flatFB s (s.om (1, r) f)) = 0 ↔ handFB s vL Y (flatFB s f) = 0) := by
  first | exact @GlobalTheory.FlatRInv.vanish_invariant | exact GlobalTheory.FlatRInv.vanish_invariant | (intros; apply GlobalTheory.FlatRInv.vanish_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProofStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMapPreservesVacuum_proof : ∀ D : D7, GlobalTheory.FinPl.FlatVac D := by
  first | exact @GlobalTheory.FinPl.FlatVacuum.flatVac | exact GlobalTheory.FinPl.FlatVacuum.flatVac | (intros; apply GlobalTheory.FinPl.FlatVacuum.flatVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrSplitPlaceSecondCombinationsVacuumNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.foldr_splitPlaceSecondCombinations_vacuum_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) F → F ≠ 0 → (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F ≠ 0 := by
  first | exact @GlobalTheory.VacComb.foldr_comb_ne_zero | exact GlobalTheory.VacComb.foldr_comb_ne_zero | (intros; apply GlobalTheory.VacComb.foldr_comb_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceDoubleStepVanishTargetCoreLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedPlace_doubleStep_vanish_targetCoreLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), IsStdChar D ψ (-1) → UnrAt s₁ p.v → UnrAt s₂ p.v → ∀ (M₀ : Lat B.V₀) (M₁ : Lat J.W₀) (M : Lat B'.V₀) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)) (P : Pair k n') (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k], IsSelfDualC B.V₀ M₀ → IsSelfDualC J.W₀ M₁ → IsSelfDualC B'.V₀ M → GluedCore B M₀ q α α₀ P → β.IsLat M₁ Q.lat → IsSumFrame B'.o B'.ζ γ γ₀ → (γ₀.IsLat M (lastKer Λ) ∨ γ₀.IsLat M (lastPair q Λ).lat) → ∀ Ξ₁ Ξ₂, Vac ψ B.V₀ J.W₀ M₀ M₁ (· = p.v) Ξ₁ → Vac ψ J.W₀ B'.V₀ M₁ M (· = p.v) Ξ₂ → ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = 0 := by
  first | exact @GlobalTheory.FinPl.vertexGlued_vanish_lastLat | exact GlobalTheory.FinPl.vertexGlued_vanish_lastLat | (intros; apply GlobalTheory.FinPl.vertexGlued_vanish_lastLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoublingStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_form_of_doubling : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, HeckeForm D := by
  first | exact @GlobalTheory.Core.Rk.IP.heckeForm_of_doubling₂ | exact GlobalTheory.Core.Rk.IP.heckeForm_of_doubling₂ | (intros; apply GlobalTheory.Core.Rk.IP.heckeForm_of_doubling₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOSplitPlacesSchrodingerModelSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunO_splitPlaces_schrodingerModel_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), Vac ψ S T M M' (fun _ => True) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∀ Φ, IsSBHalf (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → IsThetaFunO ψ S T (T' Φ) := by
  first | exact @GlobalTheory.PlaceSumTheta.isThetaFunO_sum_placeModel | exact GlobalTheory.PlaceSumTheta.isThetaFunO_sum_placeModel | (intros; apply GlobalTheory.PlaceSumTheta.isThetaFunO_sum_placeModel <;> assumption)
end

