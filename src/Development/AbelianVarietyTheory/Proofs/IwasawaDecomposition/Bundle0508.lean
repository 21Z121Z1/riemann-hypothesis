import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0474
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0279
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0503
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0498
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepCharacterInverseTypeAtLiftsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_step_character_inverse_type_at_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.chr_mul_prod_topVal | exact GlobalTheory.Mem.Col2.AdT.chr_mul_prod_topVal | (intros; apply GlobalTheory.Mem.Col2.AdT.chr_mul_prod_topVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftIdentificationsOfLiftsComparison
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.LiftRd

theorem liftTie_of_lfT : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → DV.LamDef D → ∀ (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (jL : ∀ (i : Fin D.R.m) t, (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) → D.what₂.Mt (y.tup t) ((i : ℕ) + 1)) (t : LfT y F rep (Mt := fun μ j => ⟨D.what₂.Mt μ j⟩) jL ⟨fun j => ⟨D.what₂.Mj j⟩, D.what₂.MjLat, D.what₂.thetaP, D.what₂.isot⟩), ∃ (I : LiftIds (y.L F)) (mj : GlobalTheory.RealGeo.MjTie R F), LiftTie (y.L F) I ∧ (∀ i π, I.prtW i π = y.prtW F i (rep π)) ∧ (∀ i x, (I.jMj i x).1 = t.jMj i x) ∧ (∀ μ h i x, (I.jMt μ h i x).1 = t.jMt μ i x) ∧ ∀ i x, mj.eW i x = t.eW i x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y hI hB hU hLam rep jL t
  let I : LiftIds (y.L F) :=
    { jMj := fun i =>
        (LinearEquiv.ofInjective (t.jMj i) (t.jMj_inj i)).trans (LinearEquiv.ofEq _ _ (t.jMj_range i))
      jMt := fun μ hμ i =>
        (LinearEquiv.ofInjective (t.jMt μ i) (t.jMt_inj μ ((hU μ).1 hμ) i)).trans
          (LinearEquiv.ofEq _ _ (t.jMt_range μ ((hU μ).1 hμ) i))
      prtW := fun i π => y.prtW F i (rep π) }
  refine ⟨I, ⟨t.eW, t.eW_range, t.eW_norm, t.eW_lat⟩, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => rfl⟩
  refine ⟨fun i => GlobalTheory.HilbertLevels.holW R F y.tupT y.hm y.hTop y.hinj i, fun i x x' => t.jMj_ip i x x',
    fun μ hμ i x x' => t.jMt_ip μ ((hU μ).1 hμ) i x x', ?_, fun i π v => t.isot i π v,
    fun i π π' h => t.disj i π π' h, ?_⟩
  · intro μ hμ i x w _ hw hthC hgood
    exact t.theta μ ((hU μ).1 hμ) i x _ w hw hthC hgood
  · intro μ _ i π c h0 hc
    rw [hLam μ ((i : ℕ) + 1) (by omega) i.2 π h0]
    exact DV.lamTr_of_scalar D μ _ π c h0 hc

end GlobalTheory.Mem.R3.Rw.LiftRd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsCompatibleOtherLaterStagesOfSameChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem frame_eq_of_map_eq {D : D7} {V : HSp D} {n : ℕ} (P Q : principalLevelFrame.RowPsi V n) (h : P.ψ = Q.ψ) : P = Q := by
  cases P; cases Q; cases h; rfl

set_option maxHeartbeats 8000000 in

theorem lfT_of_same : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hs Φ rep Mt l jL t jL' hj
  obtain ⟨tup', tupT', _, _, _, _, _, ⟨ψY, _, _, _⟩, PW', ιW', _, _, _, _⟩ := y'
  obtain ⟨h1, h2, h3, h4⟩ := hs
  obtain rfl : tup' = (by with_unfolding_all exact (y.tup :)) := eq_of_heq h1
  obtain rfl : tupT' = (by with_unfolding_all exact (y.tupT :)) := eq_of_heq h2
  obtain rfl : ψY = (by with_unfolding_all exact (y.PY.ψ :)) := eq_of_heq h3
  have e4 : (fun i => (PW' i).ψ) = (by with_unfolding_all exact ((fun i => (y.PW i).ψ) :)) := eq_of_heq h4
  obtain rfl : PW' = fun i => rowPsi b (y.PW i) :=
    funext fun i => frame_eq_of_map_eq _ _ ((by with_unfolding_all exact ((congrFun e4 i) :)))
  obtain rfl : jL' = (by with_unfolding_all exact (jL :)) := eq_of_heq hj
  letI := alg b iK
  refine ⟨{
    eW := (by with_unfolding_all exact (t.eW :))
    eW_range := fun i => (by with_unfolding_all exact (((t.eW_range i).trans (by rw [wat_eq b R])) :))
    eW_norm := (by with_unfolding_all exact (t.eW_norm :))
    eW_lat := (by with_unfolding_all exact (t.eW_lat :))
    jMj := (by with_unfolding_all exact (t.jMj :))
    jMj_read := (by with_unfolding_all exact (t.jMj_read :))
    jMj_inj := (by with_unfolding_all exact (t.jMj_inj :))
    jMj_range := fun i => (by with_unfolding_all exact (((t.jMj_range i).trans (congrFun (lift_Wc b F y.tupT y.hm y.hTop y.hinj) i)) :))
    jMj_ip := (by with_unfolding_all exact (t.jMj_ip :))
    jMt := (by with_unfolding_all exact (t.jMt :))
    jMt_inj := (by with_unfolding_all exact (t.jMt_inj :))
    jMt_range := (by with_unfolding_all exact (t.jMt_range :))
    jMt_ip := (by with_unfolding_all exact (t.jMt_ip :))
    theta := fun μ hμ i x h w hw1 he hw2 => by
      have hw1' : ((by with_unfolding_all exact (w :)) : (y.L F).AmbW i) ∈ (toLiftReal R F y.tupT y.hm y.hTop y.hinj).MultW i := by
        rw [lift_MultW b F y.tupT y.hm y.hTop y.hinj]; exact (by with_unfolding_all exact (hw1 :))
      have hw2' : (y.L F).eW i ∘ₗ ((by with_unfolding_all exact (w :)) : (y.L F).AmbW i) ∈ (toLiftReal R F y.tupT y.hm y.hTop y.hinj).Wc i := by
        rw [lift_Wc b F y.tupT y.hm y.hTop y.hinj]; exact (by with_unfolding_all exact (hw2 :))
      exact (by with_unfolding_all exact ((t.theta ((μ)) ((hμ)) ((i)) ((x)) ((h)) ((w)) hw1' ((he)) hw2') : _))
    junk := (by with_unfolding_all exact (t.junk :))
    out := (by with_unfolding_all exact (t.out :))
    isot := fun i π v => by
      unfold Hd.prtW
      rw [isotL_eq a b]
      kexactB (t.isot i π v)
    disj := fun i π π' hne => by
      unfold Hd.prtW
      rw [isotL_eq a b]
      kexactB (t.disj i π π' hne)
    read := (by with_unfolding_all exact (t.read :)) }, (by with_unfolding_all exact ((HEq.refl t.eW) :)), (by with_unfolding_all exact ((HEq.refl t.jMt) :))⟩

end GlobalTheory.Mem.R3.Rw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_group_element_eq_level_component_bad_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ S.Uloc v → ∃ x ∈ S.U, ∀ (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep : SBof I a → ℕ) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P x g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LocSplice.main | exact GlobalTheory.Mem.Col2.AdT.LocSplice.main | (intros; apply GlobalTheory.Mem.Col2.AdT.LocSplice.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchTupleChartMemberChart
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

set_option maxHeartbeats 2000000 in
theorem match_idx : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∃ (c0f : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → (I.stp u I.mu0 i).Cl) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) ∧ (a = I.mu0 → ∀ β, t β = 1) ∧ ∀ β, ∃ c, GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β ∧ ∀ s : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) → (∀ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((t β)⁻¹ * s * t β) κ → ∃ κ0, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u I.mu0 i (c0f β) s κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr (c0f β).1 κ0) ∧ (∀ κ0, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u I.mu0 i (c0f β) s κ0 → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((t β)⁻¹ * s * t β) κ) := by
  intro B X I hI _hP l u a Q i hi h1 hm hQ
  by_cases ha : a = I.mu0
  · subst ha
    haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
    refine ⟨fun β => β.2.choose, fun _ => 1, fun _ => ⟨DecoF.base _ _ _ _ _, isPtOf_base _, rfl⟩,
      fun _ _ _ => map_one _, fun _ _ => rfl, fun β => ⟨β.2.choose, Subtype.ext β.2.choose_spec, fun s _ => ?_⟩⟩
    simp only [inv_one, one_mul, mul_one]
    exact ⟨fun κ hκ => ⟨κ, hκ, rfl⟩, fun κ0 hκ0 => ⟨κ0, hκ0⟩⟩
  · have key : ∀ β : Chart I u a i, ∃ (c0 : (I.stp u I.mu0 i).Cl) (t : GA B (B.R.N i)),
        (∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) ∧
        (∀ (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
          bc (prV (E := B.host.E) v) t = 1) ∧
        ∃ c, chartOf I u a i c = β ∧ ∀ s : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) →
          (∀ κ, LocMv I u a i c (t⁻¹ * s * t) κ → ∃ κ0, LocMv I u I.mu0 i c0 s κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr c0.1 κ0) ∧
          (∀ κ0, LocMv I u I.mu0 i c0 s κ0 → ∃ κ, LocMv I u a i c (t⁻¹ * s * t) κ) := by
      intro β
      obtain ⟨b0, x', hx1', hxg', hxc'⟩ := GlobalTheory.T.exists_conj_referenceChartIndex I hI l a i h1 hm (β.2.choose).1
      obtain ⟨c0, rfl, y, hy, hcos⟩ := GlobalTheory.T.exists_reference_class_matching_coupling_coset I hI l u a i h1 hm β.2.choose b0
      let x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal) := fun w => y w * x' w
      have hx1 : i + 1 = B.R.m → ∀ w, x w = y w := fun h w => by simp [x, hx1' h w]
      have hconj : ∀ g : GLG B.fields.E (B.R.N i) (B.primes X).vGs, (fun w => x w * g w * (x w)⁻¹) =
          y * (fun w => x' w * g w * (x' w)⁻¹ : GLG B.fields.E (B.R.N i) (B.primes X).vGs) * y⁻¹ := fun g => by
        funext w
        show y w * x' w * g w * (y w * x' w)⁻¹ = y w * (x' w * g w * (x' w)⁻¹) * (y w)⁻¹
        group
      have hxg : ∀ g : GLG B.fields.E (B.R.N i) (B.primes X).vGs, g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).grp ↔
          (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).grp := fun g => by
        rw [hxg' g, hconj g]
        constructor
        · intro h
          exact mul_mem (mul_mem hy h) (inv_mem hy)
        · intro h
          have h2 := mul_mem (mul_mem (inv_mem hy) h) hy
          simpa [mul_assoc] using h2
      have hxc : ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).grp),
          (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
          (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).chr g0 := fun g g0 h => by
        have hm' := (hxg' g.1).1 g.2
        rw [hxc' g ⟨_, hm'⟩ (fun w => rfl)]
        have : g0 = ⟨y, hy⟩ * ⟨_, hm'⟩ * (⟨y, hy⟩)⁻¹ := Subtype.ext ((funext h).trans (hconj g.1))
        rw [this, map_mul, map_mul, map_inv, mul_comm (_ * _), ← mul_assoc, inv_mul_cancel, one_mul]
      obtain ⟨t, ht_std, ht_off, ht_res⟩ := GlobalTheory.T.exists_unitaryAdelic_lift_typePrime_reductions I hI l u (B.R.N i) x
      refine ⟨c0, t, ht_std, ht_off, β.2.choose, Subtype.ext β.2.choose_spec, fun s hs => ⟨?_, ?_⟩⟩
      · intro κ hκ
        obtain ⟨hg, hco, hC0, hCQ⟩ := (GlobalTheory.T.localMove_classRep_iff_localConditions I hI u a i hi _ _ κ).1 hκ
        rw [GlobalTheory.T.localConditions_conj_unitary_keepsStdLattice I hI l u (B.R.N i) t s x _ ht_std (fun v hv => ht_off v (Or.inl hv)) ht_res] at hC0
        have hθ : κ.2.2 = 1 := Subtype.ext ((GlobalTheory.T.twistLocalCondition_conj_iff_frameChange_trivial I hI l u a Q hQ (B.R.N i) t s _ ht_off hs).1 hCQ)
        have hmem := (hxg κ.2.1.1).1 κ.2.1.2
        let κ0 : (I.stp u I.mu0 i).G c0.1 := (1, ⟨_, hmem⟩, 1)
        have hg0 : (I.stp u I.mu0 i).gam c0.1 κ0 = 1 := by
          show ufGL B.fields.E (B.R.N i) 1 = 1
          exact map_one _
        refine ⟨κ0, (GlobalTheory.T.localMove_classRep_iff_localConditions I hI u I.mu0 i hi _ _ κ0).2 ⟨hg0, ?_, hC0, ?_⟩, ?_⟩
        · refine (hcos κ κ0 hg hg0 hθ fun h => ?_).1 hco
          intro w
          show x w * κ.2.1.1 w * (x w)⁻¹ = y w * κ.2.1.1 w * (y w)⁻¹
          rw [hx1 h w]
        · intro P
          have h0 : P.1 ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := ColIn.twistPrimes_reference_tuple_eq_empty I ▸ P.2
          simp at h0
        · have ea : (I.stp u a i).chr (β.2.choose).1 κ = (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).chr κ.2.1 *
              (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).chr κ.2.2 := rfl
          have e0 : (I.stp u I.mu0 i).chr c0.1 κ0 = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).chr κ0.2.1 *
              (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).chr 1 := rfl
          refine ea.trans (Eq.trans ?_ e0.symm)
          rw [hθ, map_one, map_one, mul_one, mul_one]
          exact hxc κ.2.1 κ0.2.1 fun w => rfl
      · intro κ0 hκ0
        obtain ⟨hg, hco, hC0, -⟩ := (GlobalTheory.T.localMove_classRep_iff_localConditions I hI u I.mu0 i hi _ _ κ0).1 hκ0
        have hmem : (fun w => (x w)⁻¹ * κ0.2.1.1 w * x w) ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).grp := by
          have e1 : (fun w => x w * ((x w)⁻¹ * κ0.2.1.1 w * x w) * (x w)⁻¹) = κ0.2.1.1 := funext fun w => by group
          refine (hxg _).2 ?_
          rw [e1]
          exact κ0.2.1.2
        let κ : (I.stp u a i).G (β.2.choose).1 := (1, ⟨_, hmem⟩, 1)
        have hgk : (I.stp u a i).gam (β.2.choose).1 κ = 1 := by
          show ufGL B.fields.E (B.R.N i) 1 = 1
          exact map_one _
        have e : (fun w => x w * κ.2.1.1 w * (x w)⁻¹) = κ0.2.1.1 := by
          funext w
          show x w * ((x w)⁻¹ * κ0.2.1.1 w * x w) * (x w)⁻¹ = κ0.2.1.1 w
          group
        refine ⟨κ, (GlobalTheory.T.localMove_classRep_iff_localConditions I hI u a i hi _ _ κ).2 ⟨hgk, ?_, ?_, ?_⟩⟩
        · refine (hcos κ κ0 hgk hg rfl fun h => ?_).2 hco
          intro w
          show κ0.2.1.1 w = y w * ((x w)⁻¹ * κ0.2.1.1 w * x w) * (y w)⁻¹
          rw [hx1 h w]
          group
        · rw [GlobalTheory.T.localConditions_conj_unitary_keepsStdLattice I hI l u (B.R.N i) t s x _ ht_std (fun v hv => ht_off v (Or.inl hv)) ht_res, e]
          exact hC0
        · exact (GlobalTheory.T.twistLocalCondition_conj_iff_frameChange_trivial I hI l u a Q hQ (B.R.N i) t s _ ht_off hs).2 rfl
    exact ⟨fun β => (key β).choose, fun β => (key β).choose_spec.choose, fun β => (key β).choose_spec.choose_spec.1,
      fun β => (key β).choose_spec.choose_spec.2.1, fun h => absurd h ha, fun β => (key β).choose_spec.choose_spec.2.2⟩

end GlobalTheory.Mem.Col2.TC.ChTw.Match
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeeperLevelIffMatricesModPlaceSymmetricStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_deeperLevel_iff_matrices_mod_place_symmetric : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (k ∈ X.K2 ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) := by
  first | exact @GlobalTheory.Mem.GroupLoc.membership_iff_unipSym | exact GlobalTheory.Mem.GroupLoc.membership_iff_unipSym | (intros; apply GlobalTheory.Mem.GroupLoc.membership_iff_unipSym <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalizedWeylLatticeIffDetTwistedEval
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LocDictT

theorem eval_map_actP {K S ι : Type} [Field K] [CommRing S] [Fintype ι] {n : ℕ} (φ : K →+* S)
    (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (P : Pol K ι n) (y : ι → Matrix (Fin n) (Fin n) S) :
    MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ (actP lam g P)) =
      φ (detTwK lam g) * MvPolynomial.eval (fun k : ι × Fin n × Fin n =>
        (((((g k.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ) * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  have key : ((MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2)).comp
      ((MvPolynomial.map φ).comp (trAct g).toRingHom)) =
      (MvPolynomial.eval (fun k : ι × Fin n × Fin n =>
        (((((g k.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ) * y k.1) k.2.1 k.2.2)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, Formalism.GradedWeylDivisibility.blockAct, Matrix.mul_apply]
  unfold actP
  rw [LinearMap.smul_apply, MvPolynomial.smul_eq_C_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C]
  congr 1
  exact RingHom.congr_fun key P

theorem invTr_bc_inv_transpose {E K : Type} [Field E] [Field K] {n : ℕ} (φ : E →+* K) (Bm : GL (Fin n) E) :
    ((((inside₂ K n (bc φ Bm))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ = (Bm : Matrix (Fin n) (Fin n) E).map φ := by
  rfl

theorem iL_emb {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (Pl : Examples₂.EntPl (I.rec7 l Z)) (w : (I.rec7 l Z).what₂.places.Pl) (τ : (I.rec7 l Z).what₂.Tau) (x : B.fields.E) :
    Pl.iL w (B.fields.emb τ x) = TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ x := by
  refine (Pl.iL_lam w (B.fields.emb τ x)).trans ?_
  have h : TaylorLogMetric.embT (I.rec7 l Z) τ x = B.embLL (B.fields.emb τ x) := by
    rw [GlobalTheory.Pdv.FormsStd.embT_eq I l Z]
    rfl
  unfold TaylorLogMetric.tauEmb
  rw [h]
  rfl

theorem detPow_map {K S : Type} [Field K] [Field S] {n : ℕ} (φ : K →+* S) (g : GL (Fin n) K) (e : ℤ) :
    φ (detPow K n g e) = ((((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ).det ^ e := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  congr 1
  show φ (g : Matrix (Fin n) (Fin n) K).det = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose]
  rfl

theorem atBas_apply {D : D7} (P : Examples₂.EntPl D) (w : D.what₂.places.Pl) {N : ℕ}
    (M : D.what₂.Tau → Matrix (Fin N) (Fin N) (Cw D w)) (Q : MvPolynomial (GL3Theta.FrV D N) D.what₂.LL) (y : FrP D w N) :
    atBas P w M Q y = MvPolynomial.eval (fun k : GL3Theta.FrV D N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map (P.iL w) Q) := rfl

theorem final_eq {S T LL : Type} [Field S] [CommRing LL] [Fintype T] {N : ℕ} (φ : LL →+* S)
    (P : MvPolynomial (T × Fin N × Fin N) LL) (A g M y : T → Matrix (Fin N) (Fin N) S) (e : T → ℤ)
    (hM : ∀ τ, M τ = A τ * g τ) :
    (∏ τ, (g τ).det ^ e τ) * ((∏ τ, (A τ).det ^ e τ) *
      MvPolynomial.eval (fun k : T × Fin N × Fin N => (A k.1 * (g k.1 * y k.1)) k.2.1 k.2.2) (MvPolynomial.map φ P)) =
    (∏ τ, (M τ).det ^ e τ) * MvPolynomial.eval (fun k : T × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  simp only [hM, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_assoc]
  ring

theorem detTwisted_polyEval_mul_factor_eq_of_eq {S T LL : Type} [Field S] [CommRing LL] [Fintype T] {N : ℕ} (φ : LL →+* S)
    (P : MvPolynomial (T × Fin N × Fin N) LL) (A G g M y : T → Matrix (Fin N) (Fin N) S) (e e' : T → ℤ)
    (hA : ∀ τ, G τ = A τ) (he : ∀ τ, e' τ = e τ) (hM : ∀ τ, M τ = A τ * g τ) :
    (∏ τ, (g τ).det ^ e τ) * ((∏ τ, (A τ).det ^ e' τ) *
      MvPolynomial.eval (fun k : T × Fin N × Fin N => (G k.1 * (g k.1 * y k.1)) k.2.1 k.2.2) (MvPolynomial.map φ P)) =
    (∏ τ, (M τ).det ^ e τ) * MvPolynomial.eval (fun k : T × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  have h1 : G = A := funext hA
  have h2 : e' = e := funext he
  subst h1 h2
  exact final_eq φ P G g M y e' hM

set_option maxHeartbeats 1000000 in

theorem mem_locW_iff_delW : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))), (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ (fun y => (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * atBas Pl w (Bs u μ w (i + 1) c') (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) y) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N (i + 1)) (extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i))) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hLF i hi c' z
  obtain ⟨hlat, hloc⟩ := GlobalTheory.T.dualLattice_class_localization_eq_unimodularCompanion I hOk hPins l Z Y u μ w hLF (i + 1) hi c'
  haveI : Fact (B.places.resChar w).Prime := ⟨B.places.resChar_prime w⟩
  obtain ⟨Bm, hBm⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (B.places.resChar w) B.fields.E _ hlat.fg hlat.span_eq_top
  have hBmN : Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((O u μ).lat (i + 1) c').1 : Set (Fin ((I.rec7 l Z).R.N (i + 1)) → (I.rec7 l Z).host.E)) Bm := by
    intro x
    rw [hStd.lat u μ (i + 1) c']
    exact (hloc x).symm.trans (hBm x)
  rw [GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff B.fields.emb B.embLL B.places (I.rec7 l Z).plEq
    (fun w x hx => (I.rec7 l Z).val_eq w x hx)
    (lamT (B.hcW u) (i + 1)) (lamT (B.hcW u) (i + 1)) (fun _ => rfl) _ hlat w Bm hBm z]
  rw [GlobalTheory.T.mem_weylLatticeIntegralSpan_iff_padic_function B.embLL B.places w (Pl.iL w) (Pl.iL_int w) (lamT (B.hcW u) (i + 1)) _
    (((rhoVr B.fields.emb (lamT (B.hcW u) (i + 1))) Bm⁻¹) z).2]
  obtain ⟨n, hw, hn, hnat, hds⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  have hlam := GlobalTheory.Pdv.FormsStd.lamTG_eq I l Z l0 u μ
  have e : (fun τ => (lamT (B.hcW u) (i + 1) τ).natW) = extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
    funext τ r
    rw [← hlam]
    refine (hnat τ r).trans ?_
    congr 1
    funext τ' r'
    exact hw τ' r'
  have eds : ∀ τ, (lamT (B.hcW u) (i + 1) τ).detShift = -((I.rec7 l Z).chTw u μ).sDiv i τ := fun τ => by
    rw [← hlam]
    exact hds τ
  rw [e]
  choose g hg1 hg2 hg3 using fun τ => GlobalTheory.T.localBasis_and_embeddedBasis_differ_by_unimodular_integral (I.rec7 l Z) (Pl.lam w) τ _ Bm (Bs u μ w (i + 1) c' τ) hBmN
    (hBas u μ w (i + 1) hi c' τ)
  refine (GlobalTheory.T.weyl_lattice_dual_invariant_unit_iff _ _ _ _ g (∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) hg1 hg2 ?_ _).trans ?_
  · rw [norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, hg2, _root_.one_zpow]
  · apply iff_of_eq
    congr 1
    funext y
    have hM : ∀ τ, ((((vlBdF B.fields.emb fun _ => Bm)⁻¹ τ : GL (Fin (B.R.N (i + 1))) B.LL) :
        Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.LL)ᵀ).map (Pl.iL w) =
        (Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ) := by
      intro τ
      rw [show (vlBdF B.fields.emb fun _ => Bm)⁻¹ τ = (inside₂ _ _ (bc (B.fields.emb τ) Bm))⁻¹ from rfl,
        invTr_bc_inv_transpose]
      ext a b
      exact iL_emb I l Z Pl w τ _
    have hdet : Pl.iL w (detTwK (lamT (B.hcW u) (i + 1)) (vlBdF B.fields.emb fun _ => Bm)⁻¹) =
        ∏ τ, ((Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map
          (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ)).det ^ (lamT (B.hcW u) (i + 1) τ).detShift := by
      unfold detTwK
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [detPow_map]
      exact congrArg (fun M => Matrix.det M ^ (lamT (B.hcW u) (i + 1) τ).detShift) (hM τ)
    beta_reduce
    rw [GlobalTheory.WeylLocOnePlace.rhoVr_inv_coe]
    have hev := eval_map_actP (Pl.iL w) (lamT (B.hcW u) (i + 1)) (vlBdF B.fields.emb fun _ => Bm)⁻¹ z.1 (fun τ => g τ * y τ)
    beta_reduce at hev
    erw [hev]
    erw [atBas_apply, hdet]
    exact detTwisted_polyEval_mul_factor_eq_of_eq (Pl.iL w) z.1
      (fun τ => (Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ))
      (fun τ => ((((vlBdF B.fields.emb fun _ => Bm)⁻¹ τ : GL (Fin (B.R.N (i + 1))) B.LL) :
        Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.LL)ᵀ).map (Pl.iL w))
      g (Bs u μ w (i + 1) c') y (fun τ => -((I.rec7 l Z).chTw u μ).sDiv i τ)
      (fun τ => (lamT (B.hcW u) (i + 1) τ).detShift) hM eds hg3

end GlobalTheory.Mem.LocDictT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultREqReL
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem multR_eq_reL {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) :
    MultR R F = (by with_unfolding_all exact ((letI := alg (reL a Z) iK; MultR (real (reL a Z) R) (face (reL a Z) F)) :)) := (congrArg (fun m ↦ m R.θ (R.MY 0) (JR R F) (chiR R F)) (mult_eq (reL a Z) a))

set_option maxHeartbeats 4000000 in

theorem mvSee : MvSee := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R F X h t hs
  obtain ⟨h1, h2, σ, red, hA, ⟨hr, hB⟩, hC⟩ := hs
  have hB' := cast (congrArg (fun E : Submodule ℂ (MMap (MP R)) => ∀ k ∈ X.B.I.Kset, ∀ T ∈ E, ∀ (v : (MP R).Vec)
    (g : GA a.D (Yc a.D 0)), (T : MMap (MP R)) v (g * kap X h t k) =
      actL (Yc a.D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) ((T : MMap (MP R)) v) g) (multR_eq_reL a Z R F)) hB
  letI := alg (reL a Z) iK
  refine ⟨?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · kexactB h2
  · refine ⟨(by with_unfolding_all exact (σ :)), (by with_unfolding_all exact (red :)), ?_, ⟨?_, ?_⟩, ?_⟩
    · exact (by with_unfolding_all exact (hA :))
    · exact (by with_unfolding_all exact (hr :))
    · kexactB hB'
    · exact (by with_unfolding_all exact (hC :))

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvEvHolds
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem ep_eq_reL {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
    (R : RealDat a.D A Ks) (F : Face a.D A) :
    EP R F = (by with_unfolding_all exact ((letI := alg (reL a Z) iK; EP (real (reL a Z) R) (face (reL a Z) F)) :)) := (congrFun (eeat_eq (reL a Z) R) (R.levR F true))

set_option maxHeartbeats 4000000 in

theorem mvEv_holds : MvEv := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R F X h G t c hj
  exact (by with_unfolding_all exact ((cast (congrArg (fun E : Submodule ℂ (MMap (MP R)) =>
    EvalTieT (MP R) R.ν0 R.fd0 E X G (iotaX X h).toMulEquiv t c) (ep_eq_reL a Z R F)) hj) :))

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvRowJ
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Top.Bl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem mvRowJ : MvRowJ := by
  intro B C a Z G' _ _ Pl0 T A Ks _ _ iK R X h G t eE j hj
  exact (by with_unfolding_all exact (hj :))

end GlobalTheory.Mem.SRe

end
end

