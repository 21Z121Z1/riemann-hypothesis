import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0565
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0454
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAvgForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0299
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0298
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0491
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0563
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiamondTranslateSumEqZeroOfChartRepresentatives
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.DiaReduce

theorem conj_level {G ι : Type*} [Group G] (U : Subgroup G) (χ : U →* ℂˣ) (J : List ι) (f : ι → G) (x κ' : G) (κ : U)
    (hκ : κ.1 = (J.map f).prod * κ') (hc : x * κ' = κ' * x)
    (h1 : ∀ i, ∃ h : f i ∈ U, χ ⟨_, h⟩ = 1) (h2 : ∀ i, ∃ h : x⁻¹ * f i * x ∈ U, χ ⟨_, h⟩ = 1) :
    ∃ κ'' : U, κ.1 * x = x * κ''.1 ∧ χ κ'' = χ κ := by
  let K : Subgroup G := χ.ker.map U.subtype
  have hK : ∀ g, (∃ h : g ∈ U, χ ⟨_, h⟩ = 1) → g ∈ K := fun g ⟨h, h'⟩ => ⟨⟨g, h⟩, h', rfl⟩
  have hP : (J.map f).prod ∈ K := K.list_prod_mem fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact hK _ (h1 i)
  have hP' : (J.map f).prod ∈ K.comap (MulAut.conj x⁻¹).toMonoidHom := Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    have := hK _ (h2 i)
    simpa using this
  have hP'' : x⁻¹ * (J.map f).prod * x ∈ K := by simpa using hP'
  obtain ⟨m, hm, hm'⟩ := K.mul_mem hP'' (K.inv_mem hP)
  have hm1 : χ m = 1 := hm
  have hm2 : m.1 = x⁻¹ * (J.map f).prod * x * (J.map f).prod⁻¹ := hm'
  refine ⟨m * κ, ?_, by rw [map_mul, hm1, one_mul]⟩
  rw [Subgroup.coe_mul, hm2, hκ, mul_assoc, ← hc]
  group

variable {D : D7}

theorem real_le_off (V : HSp D) (P : Pl D → Prop) : GinfC V ≤ grpOff V P := by
  intro a ha
  rw [GinfC, MonoidHom.mem_ker] at ha
  rw [grpOff, GlobalTheory.FinPl.LocProd.mem_congGrp_entries]
  intro i j
  have h2 : finPart D (Formalism.L2.Theta.mt V a i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) ha
  rw [idOff, Ideal.mem_iInf]
  intro w
  rw [RingHom.mem_ker, Matrix.sub_apply, GlobalTheory.FinPl.compAt, RingHom.comp_apply, RingHom.map_sub, h2]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self, RingHom.map_zero]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero, sub_self, RingHom.map_zero]

theorem grpOff_anti (V : HSp D) {P P' : Pl D → Prop} (h : ∀ w, P' w → P w) : grpOff V P ≤ grpOff V P' := by
  apply GlobalTheory.FinPl.LocProd.congGrp_mono
  intro a ha
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at ha ⊢
  exact fun w hw => ha w (h w hw)

end GlobalTheory.AdForm.DiaReduce

open GlobalTheory.AdForm.DiaReduce in

theorem GlobalTheory.AdForm.DiaReduce.rd_laws {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hpins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (i : ℕ) (hi : i ≤ B.R.m) (φ) (hφ : φ ∈ (I.fm l u a).Fi i) (β : Ch i)
    (y : (I.chain l u a).Y i) (k : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (hk : k ∈ GinfC ((I.rec7 l Z).sp.X i)) :
    ∃ y' : (I.chain l u a).Y i, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ g, ∀ κ : A.U i β,
      A.rd θ i hi β φ y (γ * (g * k * κ.1)) = (A.chi i β κ : ℂ) * A.rd θ i hi β φ y' g := by
  let eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a i hi (A.bad i) (Ch i) (A.chOf i) (A.K i hi) eY
    ⟨A.kb i, hA.reads i hi⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  have laws := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
    (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
    (A.K i hi β).y (A.K i hi β).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF β) ⟨y.1, y.2⟩
  obtain ⟨hL, hK, hR, -⟩ := laws
  let z := GlobalTheory.AdForm.Model.trFr θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) k (eY y)
  refine ⟨eY.symm z, fun γ hγ g κ => ?_⟩
  obtain ⟨hκf, κ', hκ'⟩ := (hA.U i hi β κ.1).1 κ.2
  have hchi := hA.chi i hi β κ κ' hκ'
  have e1 := hL γ hγ (g * k * κ.1)
  have e2 := hK κ.1 hκf κ' hκ' (g * k)
  have e3 := hR k hk z (fun τ => rfl) g
  exact e1.trans (e2.trans (congrArg₂ (· * ·) (congrArg (fun x : ℂˣ => (x : ℂ)) hchi.symm) e3))

open GlobalTheory.AdForm.DiaReduce in

theorem GlobalTheory.AdForm.diaSum_eq_zero_of_reps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b y, (∀ (c : {c // A.chOf j c = b}) y', ∑ᶠ s, A.rd θ j hj b φ y' (A.h j b c * (β j i).gl (g s)) = 0) → ∀ x, ∑ᶠ s, A.rd θ j hj b φ y (x * (β j i).gl (g s)) = 0 := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj φ hφ i v _ g hg b y h0 x
  have hinj := GlobalTheory.AdForm.StdT.places_injective I hok hpins l Z u p β Q L hS
  obtain ⟨e, -⟩ := hS.1
  haveI : Finite ι := Finite.of_equiv _ e.symm
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨hst, hdec⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hok hpins l Z u a Ch A hA k ι p β Q L hS (Finset.univ.toList) (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.2 (Finset.mem_univ i)) j hj b
  obtain ⟨γ, hγ, c, r, hr, κ, hκ, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hok hpins l Z u a Ch A hA j hj b).1.dec x
  obtain ⟨g', hg', κ', hκ', hκe⟩ := hdec κ hκ
  obtain ⟨y', hy'⟩ := rd_laws I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b y r hr
  have hAt : ∀ i' t, (β j i').gl t ∈ grpAt ((I.rec7 l Z).sp.X j) (· = (p i').v) := fun i' t =>
    GlobalTheory.FinPl.FrameLat.gl_mem_grpAt (β j i') t
  have hcomm := ((GlobalTheory.FinPl.localComponents (I.rec7 l Z) (· = (p i).v)).2 ((I.rec7 l Z).sp.X j)).2.1
  have key : ∀ s, A.rd θ j hj b φ y (γ * (A.h j b c * r) * κ * (β j i).gl (g s)) =
      (A.chi j b ⟨κ, hκ⟩ : ℂ) * A.rd θ j hj b φ y' (A.h j b c * (β j i).gl (g s)) := by
    intro s
    obtain ⟨κ'', h1, h2⟩ := conj_level (A.U j b) (A.chi j b) Finset.univ.toList (fun i' => (β j i').gl (g' i'))
      ((β j i).gl (g s)) κ' ⟨κ, hκ⟩ hκe
      (hcomm _ (hAt i _) _ (grpOff_anti _ (fun w hw => ⟨i, hw⟩) hκ')) (fun i' => hst i' _ (hg' i')) (fun i' => by
        by_cases hi : i' = i
        · subst hi
          rw [← map_inv, ← map_mul, ← map_mul]
          refine hst i' _ ?_
          rw [mul_smul, mul_smul, hg, smul_comm (g' i') s, hg', ← hg, inv_smul_smul]
        · have hc := hcomm _ (hAt i (g s)) _ (GlobalTheory.FinPl.LocProd.grpAt_le_grpOff' _ _ _
            (fun w hw hw' => hi (hinj (hw.symm.trans hw'))) (hAt i' (g' i')))
          rw [mul_assoc, ← hc, inv_mul_cancel_left]
          exact hst i' _ (hg' i'))
    have hc := hcomm _ (hAt i (g s)) r (real_le_off _ _ hr)
    have h1' : κ * (β j i).gl (g s) = (β j i).gl (g s) * κ''.1 := h1
    have e1 : γ * (A.h j b c * r) * κ * (β j i).gl (g s) = γ * (A.h j b c * (β j i).gl (g s) * r * κ''.1) := by
      rw [mul_assoc, h1', mul_assoc (A.h j b c), hc]
      simp only [mul_assoc]
    rw [e1, hy' γ hγ, h2]
  simp only [key]
  rw [← mul_finsum' _ _ (Set.toFinite _), h0, mul_zero]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepSplitPlaceValuePeriodGroupInvaria
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DblInv

theorem val_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (S : Dbl2 ψ σ) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ)
    (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (Θ₁ : WO S.B.V S.J.W → ℂ) (Θ₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ)
    (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    S.val c₁ c₂ Θ₁ Θ₂ φ f g h₁ h₂ = S.val c₁ c₂ (S.s₁.om (g, h₁) Θ₁) (S.s₂.om (h₁, h₂) Θ₂) φ (rTrans h₂ f) 1 1 1 := by
  unfold Dbl2.val Dbl2.con
  have e3 : rTrans (1 : GA D S.B'.V) (rTrans h₂ f) = rTrans h₂ f := by funext x; simp [rTrans]
  rw [show ((1 : GA D S.B.V), (1 : GA D S.J.W)) = 1 from rfl, show ((1 : GA D S.J.W), (1 : GA D S.B'.V)) = 1 from rfl,
    map_one, map_one, e3]
  rfl

set_option maxHeartbeats 2000000 in

theorem val_inv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → Q.Typed f → ∀ g h₁ h₂, g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v) → h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v) → h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v) → ∀ a x y, ∀ r ∈ RFJ Q.k Q.n₁ (Q.c + 1 + 1) (σ + 1), ∀ j ∈ Q.L₁.J, ∀ r' ∈ R Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ j' ∈ Q.L₂.J, S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ (r * x * j)) (h₂ * Q.gl₂ (r' * y * j')) = S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ f₁ f₂ hvac φ f hφ hf hTy g h₁ h₂ hg hh₁ hh₂ a x y r hr j hj r' hr' j' hj'
  obtain ⟨⟨T₁, O₁, hT₁, hO₁, rfl⟩, ⟨T₂, O₂, hT₂, hO₂, rfl⟩⟩ := hvac
  have hcQ : Q.c + 1 + 1 = 2 * (σ + 1) := by have := Q.F.bes.1; omega
  obtain ⟨hψc, hψ1⟩ := GlobalTheory.T.addChar_conductor_integers_continuous_ne_one Q.k Q.ψk Q.cond
  have hsd : IsSelfDual Q.ψk Q.ν := ((GlobalTheory.SplitWeil.selfDual_measure Q.k Q.ψk hψc hψ1).2.1 Q.cond Q.ν).1 Q.unitVol
  obtain ⟨-, -, -, cm₀, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B.V _ Q.F.G₀ Q.gl₀ Q.loc₀
  obtain ⟨-, -, -, cm₁, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.J.W _ Q.F.G₁ Q.gl₁ Q.loc₁
  obtain ⟨-, -, -, cm₂, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B'.V _ Q.F.G₂ Q.gl₂ Q.loc₂
  have hT₁' := GlobalTheory.T.local_model_weil_operator_trivialAtPlace_isModel D Q.k Q.q ψ hψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil _ _ Q.F.G₀ Q.F.G₁ T₁ hT₁ g hg h₁ hh₁
  have hT₂' := GlobalTheory.T.local_model_weil_operator_trivialAtPlace_isModel D Q.k Q.q ψ hψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil _ _ Q.F.G₁ Q.F.G₂ T₂ hT₂ h₁ hh₁ h₂ hh₂
  have hf' : IsContAut S.B'.V (rTrans h₂ f) :=
    ⟨fun γ hγ x => by simp only [rTrans, mul_assoc]; exact hf.1 γ hγ _, hf.2.comp (continuous_mul_right h₂)⟩
  have hTy' : Q.Typed (rTrans h₂ f) := fun j => by
    funext x
    have := congrFun (hTy j) (x * h₂)
    simp only [rTrans, Pi.smul_apply] at this ⊢
    rw [mul_assoc, cm₂ j h₂ hh₂, ← mul_assoc, this]
  obtain ⟨A, τ, T, hsm, hτ, hmem, htri, hval, -⟩ :=
    GlobalTheory.T.splitPlace_doubleStep_trilinearForm_properties D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ _ _ hT₁' hT₂' φ hφ
  set F : A := ⟨rTrans h₂ f, hmem _ hf' hTy'⟩ with hFdef
  let Φa : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k →
      SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) :=
    fun x => ⟨om Q.μ₁ a x Q.Φ₁.1, om_mem_SB Q.μ₁ a x Q.Φ₁.2⟩
  let Φb : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k →
      SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
    fun x y => ⟨om Q.μ₂ x y Q.Φ₂.1, om_mem_SB Q.μ₂ x y Q.Φ₂.2⟩
  have d1 : comb ψ _ _ Q.D₁ (T₁ O₁) = T₁ Q.Φ₁ := (Q.dat₁.2 T₁ hT₁ O₁ Q.Φ₁ hO₁ rfl).symm
  have d2 : comb ψ _ _ Q.D₂ (T₂ O₂) = T₂ Q.Φ₂ := (Q.dat₂.2 T₂ hT₂ O₂ Q.Φ₂ hO₂ rfl).symm
  have KEY : ∀ x y, S.val c₁ c₂ (comb ψ _ _ Q.D₁ (T₁ O₁)) (comb ψ _ _ Q.D₂ (T₂ O₂)) φ f (g * Q.gl₀ a)
      (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) =
      S.val c₁ c₂ ((S.s₁.om (g, h₁) ∘ₗ T₁) (Φa x)) ((S.s₂.om (h₁, h₂) ∘ₗ T₂) (Φb x y)) φ (τ y F).1 1 1 1 := by
    intro x y
    rw [d1, d2, val_move]
    have m1 : S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) = S.s₁.om (Q.gl₀ a, Q.gl₁ x) * S.s₁.om (g, h₁) := by
      rw [← map_mul, Prod.mk_mul_mk, cm₀ a g hg, cm₁ x h₁ hh₁]
    have m2 : S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) = S.s₂.om (Q.gl₁ x, Q.gl₂ y) * S.s₂.om (h₁, h₂) := by
      rw [← map_mul, Prod.mk_mul_mk, cm₁ x h₁ hh₁, cm₂ y h₂ hh₂]
    have r : rTrans (h₂ * Q.gl₂ y) f = (τ y F).1 := by
      rw [hτ]; funext z; simp only [rTrans, hFdef]; rw [mul_assoc z (Q.gl₂ y) h₂, cm₂ y h₂ hh₂]
    rw [m1, m2, r, Module.End.mul_apply, Module.End.mul_apply]
    exact GlobalTheory.T.doubleStep_local_weil_action_line_characters_cancel D ψ hψ σ S Q _ _ hT₁' hT₂' c₁ c₂ φ _ a x y Q.Φ₁ (Φa x) Q.Φ₂ (Φb x y) rfl rfl
  have hFty : ∀ j : Q.L₂.J, τ (j : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) F = (Q.L₂.lam j : ℂ) • F := by
    intro j; apply Subtype.ext; rw [hτ, Submodule.coe_smul]; exact hTy' j
  rw [KEY, KEY]
  exact tensorVal_inv hcQ hψc hψ1 hsd Q.open₂ htri F Q.Φ₁ Q.Φ₂ Q.ty₁ Q.ty₂ hFty a x y hr hj hr' hj'
    (hval (Φa _) (Φb _ _) (τ _ F)) (hval (Φa x) (Φb x y) (τ y F))

end GlobalTheory.DblInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumBasePointsLawRationalTwistPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.ReadLaw

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem transport_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) (κ₀ : TC.GA B (B.R.N i)) (κ₀' : TC.GA B (B.R.N (i + 1))), finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 = κ₀.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 = κ₀'.1 → ∀ (q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)), TC.PtOf (κ₀ * A.kb i α) q.1.1 → TC.PtOf (κ₀' * A.kb (i + 1) γ) q'.1.1 → cosetIn q = cosetIn (A.p0 i α) → cosetIn q' = cosetIn (A.p0 (i + 1) γ) → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → A.xi i hi α γ z' = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) q q' (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) := by
  intro B X I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' κ₀ κ₀' hκ hκ' q q' hq hq' hc hc' z z' v hv hvh hact
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨d, hd, h1⟩ := GlobalTheory.AdForm.CongAtIdem.cong_at_idem ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))
    (rankN (I.rec7 l Z) i hi0) (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hA.idem
  have hd0 := GlobalTheory.Mem.Df.disjoint_vGs_Q I hok l a
  have hQ := GlobalTheory.Mem.Col2.ColIn.Q_subset_SQ I a
  have hb := hA.base i hi0 α
  have hb' := hA.base (i + 1) hi γ
  obtain ⟨M₀, hM₀, h2⟩ := GlobalTheory.AdForm.TwResid.xiAt_transport_tw I l hok u a i hi (A.b0 i α) (A.b0 (i + 1) γ)
    (A.p0 i α) q (A.p0 (i + 1) γ) q' (A.kb i α) κ₀ (A.kb (i + 1) γ) κ₀'
    (hb.1.of_extTo hQ hd0) hb.2 (hb'.1.of_extTo hQ hd0) hb'.2 hq hq' hc hc'
  obtain ⟨z₂, t, ht, hth, hv2⟩ := GlobalTheory.T.idempotentHalf_eq_rational_add_nsmul_standardHom ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) A.e _ hA.idem
    (d * M₀) (Nat.mul_pos hd hM₀) v hvh
  have hm : (z' + k • z₂).map (fun r => A.e * incA (I.rec7 l Z) r) =
      z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • z₂.map (fun r => A.e * incA (I.rec7 l Z) r) := by
    have e := map_add (((AddMonoidHom.mulLeft A.e).comp (incA (I.rec7 l Z)).toAddMonoidHom).mapMatrix) z' (k • z₂)
    rw [map_nsmul] at e
    exact e
  have hcong : (z' + k • z₂).map (fun r => A.e * incA (I.rec7 l Z) r) =
      actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + (d * M₀) • (-(k • t)) := by
    rw [hact, hm, hv2, smul_neg, smul_comm (d * M₀) k t, smul_add]
    abel
  have hc2 := h1 κ.1 κ'.1 κ₀ κ₀' hκ hκ' M₀ z (z' + k • z₂) (-(k • t)) (neg_mem (nsmul_mem ht k)) hcong
  have hx := h2 _ _ hc2
  have hw : IsHalf A.e (v - (d * M₀) • t) := fun r s => by
    rw [Matrix.sub_apply, Matrix.smul_apply, mul_sub, mul_smul_comm, hvh r s, hth r s]
  have hz2 : z₂.map (fun r => A.e * incA (I.rec7 l Z) r) = v - (d * M₀) • t := eq_sub_of_add_eq hv2.symm
  have hp := hper (z' + k • z₂) z' (v - (d * M₀) • t) (sub_mem hv (nsmul_mem ht _)) hw (by rw [hm, hz2])
  exact hp.symm.trans (congrArg B.embLL hx)

theorem law_read : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → (∀ (z₁ z₂ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), t ∈ stdHom _ _ → IsHalf A.e t → z₁.map (fun r => A.e * incA (I.rec7 l Z) r) = z₂.map (fun r => A.e * incA (I.rec7 l Z) r) + k • t → A.xi i hi α γ z₁ = A.xi i hi α γ z₂) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z z' : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = z'.map (fun r => A.e * incA (I.rec7 l Z) r) + k • v → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * A.xi i hi α γ z' = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * A.xi i hi α γ z := by
  intro B X I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' hr hr' x y hx hy z z' v hv hvh hact
  obtain ⟨κ₀, hκ₀⟩ := ((hA.U i (Nat.le_of_succ_le hi) α κ.1).1 κ.2).2
  obtain ⟨κ₀', hκ₀'⟩ := ((hA.U (i + 1) hi γ κ'.1).1 κ'.2).2
  obtain ⟨q, q', hq, hq', hc, hc', hlaw⟩ := GlobalTheory.T.finiteDatum_law_between_basePoints_movedPoints I hok hpins l Z u a Ch A hA i hi α γ κ κ' hr hr' x y hx hy κ₀.1 κ₀'.1 hκ₀.symm hκ₀'.symm
  have h2 := transport_base I hok hpins l Z u a Ch A hA i hi α γ k hk hper κ κ' κ₀.1 κ₀'.1 hκ₀.symm hκ₀'.symm q q' hq hq' hc hc' z z' v hv hvh hact
  rw [h2]
  exact hlaw _

end GlobalTheory.AdForm.ReadLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormKeepsAdelicLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.TransLaw

theorem trc_apply' {D : D7} {V : HSp D} (c : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc c f x = ∑ g ∈ c.support, c g * f (x * g) := by
  simp [trc, rTrans, Finset.sum_apply]

theorem list_prod_right {G : Type} [Group G] (F : G → ℂ) (L : List G) (hL : ∀ a ∈ L, ∀ z, F (z * a) = F z) (z : G) :
    F (z * L.prod) = F z := by
  induction L generalizing z with
  | nil => simp
  | cons a L ih =>
    rw [List.prod_cons, ← mul_assoc, ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (z * a), hL a List.mem_cons_self]

theorem list_prod_chi {G : Type} [Group G] (U : Subgroup G) (χ : U →* ℂˣ) (L : List G)
    (hL : ∀ a ∈ L, ∃ h : a ∈ U, χ ⟨a, h⟩ = 1) : ∃ h : L.prod ∈ U, χ ⟨_, h⟩ = 1 := by
  induction L with
  | nil => exact ⟨U.one_mem, χ.map_one⟩
  | cons a L ih =>
    obtain ⟨ha, hχa⟩ := hL a List.mem_cons_self
    obtain ⟨hP, hχP⟩ := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
    refine ⟨by rw [List.prod_cons]; exact U.mul_mem ha hP, ?_⟩
    have e : (⟨(a :: L).prod, by rw [List.prod_cons]; exact U.mul_mem ha hP⟩ : U) = ⟨a, ha⟩ * ⟨L.prod, hP⟩ := by
      apply Subtype.ext; simp [List.prod_cons]
    rw [e, map_mul, hχa, hχP, one_mul]

set_option maxHeartbeats 1000000 in
theorem rd_laws {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hpins : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is) (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ)
    (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j) (b : Ch j) (y : (I.chain l u a).Y j) :
    (∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ g, A.rd θ j hj b φ y (γ * g) = A.rd θ j hj b φ y g) ∧
    (∀ κ : A.U j b, ∀ g, A.rd θ j hj b φ y (g * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y g) ∧
    (∀ k ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ y' : (I.chain l u a).Y j,
      IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
      ∀ g, A.rd θ j hj b φ y (g * k) = A.rd θ j hj b φ y' g) := by
  let eY : (I.chain l u a).Y j ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) j hj :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a j hj (A.bad j) (Ch j) (A.chOf j) (A.K j hj) eY
    ⟨A.kb j, hA.reads j hj⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  obtain ⟨hL, hK, hR, -⟩ := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X j) (B.R.N j) (rankN (I.rec7 l Z) j hj)
      (gramN (I.rec7 l Z) j hj) rfl (B.T u) (I.rec7 l Z).R.f (A.bad j) (A.K j hj b).lev {c // A.chOf j c = b}
      (A.K j hj b).y (A.K j hj b).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF b) ⟨y.1, y.2⟩
  refine ⟨fun γ hγ g => hL γ hγ g, fun κ g => ?_, fun k hk y' hy g => hR k hk ⟨y'.1, y'.2⟩ hy g⟩
  obtain ⟨hκf, κ', hκ'⟩ := (hA.U j hj b κ.1).1 κ.2
  rw [hA.chi j hj b κ κ' hκ']
  exact hK κ.1 hκf κ' hκ' g

end GlobalTheory.AdForm.TransLaw

open GlobalTheory.AdForm.TransLaw in
set_option maxHeartbeats 2000000 in

theorem GlobalTheory.AdForm.trc_rd_laws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ b y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ (e : {e // A.chOf j e = b}), ∀ g ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ (κ : A.U j b) (y' : (I.chain l u a).Y j),
        IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) g) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
        trc c (A.rd θ j hj b φ y) (γ * (A.h j b e * g) * κ.1) = (A.chi j b κ : ℂ) * trc c (A.rd θ j hj b φ y') (A.h j b e) := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ K _ _ _ _ ι p β Q L hT j hj c hc φ hφ hinv b y γ hγ e g0 hg0 κ y' hy
  obtain ⟨hLy, hKy, hRy⟩ := rd_laws I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b y
  have hT' := hT
  obtain ⟨⟨eι, -⟩, -⟩ := hT'
  haveI : Fintype ι := Fintype.ofEquiv _ eι.symm
  obtain ⟨hstab, hdec⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hok hpins l Z u a Ch A hA K ι p β Q L hT Finset.univ.toList
    (Finset.nodup_toList _) (fun i => Finset.mem_toList.2 (Finset.mem_univ _)) j hj b
  obtain ⟨gs, hgs, κ', hκ'off, hκeq⟩ := hdec κ.1 κ.2
  set s := (Finset.univ.toList.map fun i => (β j i).gl (gs i)).prod with hs
  obtain ⟨hsU, hχs⟩ := list_prod_chi (A.U j b) (A.chi j b) (Finset.univ.toList.map fun i => (β j i).gl (gs i)) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hstab i (gs i) (hgs i))
  have hκ'U : κ' ∈ A.U j b := by
    have : κ' = s⁻¹ * κ.1 := by rw [hκeq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]; exact (A.U j b).mul_mem ((A.U j b).inv_mem hsU) κ.2
  have hχκ : A.chi j b κ = A.chi j b ⟨κ', hκ'U⟩ := by
    have e1 : κ = (⟨s, hsU⟩ : A.U j b) * ⟨κ', hκ'U⟩ := Subtype.ext hκeq
    rw [e1, map_mul, hχs, one_mul]
  set F := trc c (A.rd θ j hj b φ y) with hF

  have hcomm : ∀ g' ∈ c.support, κ' * g' = g' * κ' := fun g' hg' =>
    ((GlobalTheory.FinPlLoc.part_grp (fun x => ∃ i, x = (p i).v) ((I.rec7 l Z).sp.X j)).2.1 g' (hc g' hg') κ' hκ'off).symm

  have step1 : ∀ x, F (x * κ.1) = (A.chi j b κ : ℂ) * F (x * s) := by
    intro x
    rw [hF, trc_apply', trc_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun g' hg' => ?_
    rw [hκeq, ← mul_assoc, mul_assoc (x * s), hcomm g' hg', ← mul_assoc, hKy ⟨κ', hκ'U⟩, hχκ]
    ring

  have step2 : ∀ x, F (x * s) = F x := by
    intro x
    refine list_prod_right F _ ?_ x
    intro a' ha' z
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha'
    exact congrFun (hinv b y i (gs i) (hgs i)) z

  have step3 : F (γ * (A.h j b e * g0)) = trc c (A.rd θ j hj b φ y') (A.h j b e) := by
    rw [hF, trc_apply', trc_apply']
    refine Finset.sum_congr rfl fun g' hg' => ?_
    have hfin : g' ∈ GfC ((I.rec7 l Z).sp.X j) := GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hc g' hg')
    rw [mul_assoc γ, hLy γ hγ, mul_assoc, ← GlobalTheory.FinTranslate.comm_fin_real _ hfin hg0, ← mul_assoc,
      hRy g0 hg0 y' hy]
  rw [step1, step2, step3]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormValuesMemWeylModule
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.TransAct

set_option maxHeartbeats 1000000 in

theorem trc_val_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ e : (I.stp u a j).Cl, (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e ∈ ValC (Gr B.fields.emb B.embLL (B.R.N j)) (Col2.lamT (B.hcW u) j) := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj c hc φ hφ hinv e
  have hR := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hP l Z u a Ch A hA j hj (A.chOf j e)).1
  have key : ∀ g, (fun z : (I.chain l u a).Y j =>
      A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) ∈
      ValC (Gr B.fields.emb B.embLL (B.R.N j)) (Col2.lamT (B.hcW u) j) := by
    intro g
    obtain ⟨γ, hγ, e', g', hg', κ, hκ, hdec⟩ := hR.dec (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)
    let U : (I.rec7 l Z).what₂.Tau → GL (Fin (B.R.N j)) ℂ := fun τ =>
      ((Matrix.isUnit_iff_isUnit_det _).2 (RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) g' τ)).unit
    have hfun : (fun z : (I.chain l u a).Y j =>
        A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) =
        (A.chi j (A.chOf j e) ⟨κ, hκ⟩ : ℂ) • GlobalTheory.Mem.ColAd.lT (Gr B.fields.emb B.embLL (B.R.N j)) U (φ e'.1) := by
      funext z
      rw [hdec]
      exact (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hP l Z u a Ch A hA θ hθ j hj φ hφ).2 (A.chOf j e) z γ hγ e' g' hg' ⟨κ, hκ⟩
        (GlobalTheory.Mem.ColAd.frL (Gr B.fields.emb B.embLL (B.R.N j)) U z) (fun τ => rfl)
    rw [hfun]
    exact Submodule.smul_mem _ _ (GlobalTheory.Mem.ColAd.lT_mem _ _ U (hφ e'.1).1)
  have hsum : (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) =>
      trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e =
      ∑ g ∈ c.support, c g • (fun z : (I.chain l u a).Y j =>
        A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) := by
    funext z
    simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (key g)

end GlobalTheory.AdForm.TransAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_bound : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), ∀ j ρ h, GlobalTheory.FinPl.GoodBF (commOf (pk W) u (mkGeo m b₀)).ψ ((commOf (pk W) u (mkGeo m b₀)).B j ρ h) ((commOf (pk W) u (mkGeo m b₀)).J j ρ h) (N₁ j) (M₁ j ρ h) (N₁ (j + 1)) ((commOf (pk W) u (mkGeo m b₀)).x (j + 1)).L (PP.under (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.Fam.goodBF_of_normalFrames | exact GlobalTheory.Fam.goodBF_of_normalFrames | (intros; apply GlobalTheory.Fam.goodBF_of_normalFrames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobiStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneCoset_besselToFourierJacobi : ∀ D : D7, GlobalTheory.FinPl.OneCosetBF D := by
  first | exact @GlobalTheory.FinPl.oneCosetBF | exact GlobalTheory.FinPl.oneCosetBF | (intros; apply GlobalTheory.FinPl.oneCosetBF <;> assumption)
end

