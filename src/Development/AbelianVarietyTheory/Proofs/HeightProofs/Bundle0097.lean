import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0198
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0084
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.NumberFieldFamilies.RamifiedPrimesTrivialTuple
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicThetaSeriesComparisonIndepScalarsErrors
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt.Side

set_option maxHeartbeats 3200000 in

theorem exportTie_upd : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) kap lam err, Nonempty (GlobalTheory.SeriesTie.ExportTie s.YS s.v₀) → Nonempty (GlobalTheory.SeriesTie.ExportTie (s.upd kap lam err).YS (s.upd kap lam err).v₀) := by
  intro D nch s kap lam err ⟨Z⟩
  exact ⟨{
    ρ := Z.ρ
    good := Z.good
    pin := { Z.pin with }
    vec := Z.vec
    ν := Z.ν
    scalar := fun i j b => ⟨(Z.scalar i j b).ne, fun h => (Z.scalar i j b).norm h, fun h => (Z.scalar i j b).rat h⟩
    tie := Z.tie
    hecke := Z.hecke
    univ := Z.univ }⟩

end GlobalTheory.PlugPt.Side
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeParametersNumericaStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_constructedPoint_hostSize_numerical : EvP fun _ K => ∀ β : BPt K, GlobalTheory.FieldSize.HostSz β.D.host β.O.L.sc.L ∧ ∀ C, FieldTies β.D C → NumAtL β.O.L K.s.x := by
  first | exact @GlobalTheory.Plug.eventually_hostSize_and_numAt | exact GlobalTheory.Plug.eventually_hostSize_and_numAt | (intros; apply GlobalTheory.Plug.eventually_hostSize_and_numAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasExpOfLayer
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt

namespace GlobalTheory.ExpTiesOfLayer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hasExp_of_layer : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), HasExp (GlobalTheory.HeightCounting.NE hL) ∧ ∀ (E : NExt hL), (∀ K B f T w Z Wt p0 t nch n xd c, E K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.NE hL K B f T w Z Wt p0 t nch n xd c)) → HasExp E := by
  intro hL
  have hNE : HasExp (GlobalTheory.HeightCounting.NE hL) := by
    intro K B f T w Z Wt p0 t nch n xd c y
    have hg := c.row.grp
    refine ⟨⟨⟨⟨⟨y.ser.ex⟩, ⟨fun g => (hg.lvl0 g).symm, ?_⟩, ?_⟩⟩, PUnit.unit⟩⟩
    · intro i b u hu
      obtain ⟨x, hx, hx'⟩ := hg.psi0 u hu i b
      exact ⟨x, hx, hx'⟩
    · intro i j b a _
      rw [y.xd i ((j : ℕ) + 1) b (by omega) (by omega)]
      exact Set.mem_univ _
  exact ⟨hNE, fun E hE K B f T w Z Wt p0 t nch n xd c e => by
    obtain ⟨y⟩ := hE K B f T w Z Wt p0 t nch n xd c e
    exact hNE K B f T w Z Wt p0 t nch n xd c y⟩

end GlobalTheory.ExpTiesOfLayer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.LargeBaseRayCondition
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Plug.RayLarge

open Formalism.L2.Host

def raySet (hR : GlobalTheory.NT.RayField) (P : Pre) (M : ℕ) : Finset ℂ :=
  if h : M ≠ 0 then Classical.choose (GlobalTheory.RayOnto.exists_finset_containsRayField hR P M h) else ∅

theorem raySet_alg (hR : GlobalTheory.NT.RayField) (P : Pre) (M : ℕ) : ∀ z ∈ raySet hR P M, IsAlgebraic ℚ z := by
  unfold raySet
  split_ifs with h
  · exact (Classical.choose_spec (GlobalTheory.RayOnto.exists_finset_containsRayField hR P M h)).1
  · simp

def levels (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) : Finset ℕ :=
  Classical.choose (GlobalTheory.Plug.TwistLevels.levels_bounded P f Ξ)

def raySets (hR : GlobalTheory.NT.RayField) (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) : Finset ℂ :=
  (levels P f Ξ).biUnion (raySet hR P)

theorem raySets_alg (hR : GlobalTheory.NT.RayField) (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) :
    ∀ z ∈ raySets hR P f Ξ, IsAlgebraic ℚ z := by
  intro z hz
  obtain ⟨M, -, hz⟩ := Finset.mem_biUnion.1 hz
  exact raySet_alg hR P M z hz

theorem rayRec_of_has (hR : GlobalTheory.NT.RayField) {K : Ctx} (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T)
    (hH : ∀ z ∈ raySets hR X.B.toPre f (T.set f), ∃ x : X.B.LL, X.B.embLL x = z) : RayRec X.toD7 c.O.nch := by
  intro w Sp hSp
  have hspec := Classical.choose_spec (GlobalTheory.Plug.TwistLevels.levels_bounded X.B.toPre f (T.set f))
  have hM : X.B.host.g 0 * X.B.host.g 1 * ∏ q ∈ Sp.image (fun Q => Nat.card (kP Q)), q ∈ levels X.B.toPre f (T.set f) := by
    refine hspec.2 X.B rfl T HEq.rfl w Sp ?_
    intro P hP
    rcases hSp P hP with ⟨h1, -⟩ | ⟨hmu, hmem⟩
    · exact Or.inl h1
    · right
      have hw : w ∈ c.Wt := by_contra fun h => hmu (c.mu.off w h)
      rw [← (c.nch_Q w hw).1]
      exact hmem
  have hM0 := hspec.1 _ hM
  have hrs := (Classical.choose_spec (GlobalTheory.RayOnto.exists_finset_containsRayField hR X.B.toPre _ hM0)).2
  refine hrs X.B.LL X.B.embLL (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK X.toD7) ?_ ?_
  · ext x
    exact DFunLike.congr_fun X.B.embE_φ₀ _
  · intro z hz
    refine hH z (Finset.mem_biUnion.2 ⟨_, hM, ?_⟩)
    rw [raySet, dif_pos hM0]
    exact hz

end GlobalTheory.Plug.RayLarge

open GlobalTheory.Plug.RayLarge in

theorem GlobalTheory.Plug.largeBaseProperty_rayProperty : GlobalTheory.NT.RayField → ∀ (KP : ∀ B : Base, Fr B.toPre → Prop) (Q : V4.Slot), LargeBaseCondition KP Q RayPosition := by
  intro hR KP Q
  exact ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    ⟨0, fun K _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B f _ _ Ξ => raySets hR B f Ξ, by simp,
      fun B f _ _ Ξ => raySets_alg hR B f Ξ,
      fun B f T _ hH _ _ _ C W V S N G c _ => rayRec_of_has hR ⟨B, C, W, V, S, N, G⟩ f T c fun z hz => hH.2 z hz⟩⟩⟩⟩⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.LeafDepthAllRunUnconditional
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.RunDepth.leafDepth_all_run_unconditional : ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → C0 ≤ oc.C → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → LeafDepthGood N O ∧ LeafDepthRam N O ∧ LeafDepth2 N O ∧ LeafDepthLevel N O :=
  GlobalTheory.RunDepth.leafDepth_all_run GlobalTheory.ChF.colength_bound_split_place_chart
    GlobalTheory.ChF.hodgeTate_inclusion_chart GlobalTheory.ChF.unramified_companion_chart_characters
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RayClassFieldsInCoefficientFieldConstructedPoint
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem rayClassFields_in_coefficients : ∀ (K : Ctx) (β : BPt K), β.Is RayPosition → RayRec β.D β.O.ex.nch := by
  intro K β h
  obtain ⟨X, f, T, c, Y, hY, p, _, _, _, _, _, _, _, _, _⟩ := β
  change RayRec X.toD7 c.O.nch at h
  rw [← hY] at h
  exact h

end GlobalTheory.PlugPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightPsiChoiceTame
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PlugPt.sideW_chr : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Formalism.L2.Host.PsiChoiceCompatible (p.w.D p.Z) (sideW ν p).cf p.O.ex.nch (sideW ν p).tp ∧ (∀ v, (p.w.D p.Z).what₂.muAt v ≠ (p.w.D p.Z).what₂.mu0 → ((sideW ν p).tp.psi v).ValuesIn 0 (p.w.D p.Z).what₂.embLL) ∧ GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (sideW ν p).cf.W.om := by
  intro hL 𝒮 ν K p
  refine ⟨p.x.n.chrPsi, ?_, ?_⟩
  · intro v _
    show (p.x.n.tp.psi v).ValuesIn 0 _
    rw [p.x.n.psi]
    exact GlobalTheory.twDat_psi_valuesIn_LL p.B p.T p.x.coh v
  · have h := p.x.what₂.grp
    have hf := (GlobalTheory.Plug.wPt_frame 𝒮 K p).2.1
    show GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z).W.om
    rw [hf]
    exact types_of_true (D := p.w.D p.Z) _ h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightRaysOfRayRec
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX
  GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug.RaysW

theorem nonempty_heightOneSpectrum (L : Type) [Field L] [NumberField L] : Nonempty (HeightOneSpectrum (𝓞 L)) := by
  obtain ⟨P, hne, hP⟩ := (Ring.not_isField_iff_exists_prime (R := 𝓞 L)).1 (NumberField.RingOfIntegers.not_isField L)
  exact ⟨⟨P, hP, hne⟩⟩

theorem rays_of_rayRec : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (K : Ctx) (p : WPt 𝒮 K),
    RayRec (p.w.D p.Z) p.O.ex.nch → (sideW ν p).Rays := by
  intro hL 𝒮 ν K p hR t
  have hlev := p.x.what₂.r.z.lev
  have hmu := p.x.what₂.mu
  have hn := p.x.n.Q
  change R3.TupU p.w.I (R3.usedOf p.w.I p.T p.x.Wt) at t
  show GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField _ (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel p.x.what₂.r.z.R.toRealDat t)
  rcases (R3.mem_range_ixOf p.w.I).1 ⟨t, rfl⟩ with h0 | ⟨w, hw, hxi⟩
  ·
    obtain ⟨v⟩ := nonempty_heightOneSpectrum (p.w.D p.Z).what₂.LL
    refine hR ((p.w.D p.Z).plEq.symm v) _ fun P hP ↦ ?_
    have hram : ¬ (p.x.what₂.r.z.R.xiH t).UnrAt P := (hlev.is.Q_ram t P).2 (Or.inl hP)
    rw [hlev.xiH t, h0, p.w.ok.trueColumnChoices_heckeChar_reference_eq_one] at hram
    exact absurd (Formalism.L2.Fam.DivCQ.unrAt_one P) hram
  ·
    refine hR w _ fun P hP ↦ ?_
    have hram : ¬ (p.x.what₂.r.z.R.xiH t).UnrAt P := (hlev.is.Q_ram t P).2 (Or.inl hP)
    have hpl := (hlev.is.Q_pl t P hP).1
    by_cases hpd : (((p.w.D p.Z).host.pde * (p.w.D p.Z).host.pde' : ℕ) : 𝓞 (p.w.D p.Z).host.E) ∈ P.asIdeal
    · obtain ⟨q, hq, hc, -⟩ := hpl
      exact Or.inl ⟨hpd, hc ▸ hq⟩
    · right
      have hx : p.x.what₂.r.z.R.xiH t = p.T.xiTw p.f w := by
        rw [hlev.xiH t, hxi, p.w.C_eq]
      rw [hx] at hram
      have h1 : ¬ ((p.B.host.pde : ℕ) : 𝓞 p.B.host.E) ∈ P.asIdeal := fun h ↦ hpd (by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
      have h2 : ¬ ((p.B.host.pde' : ℕ) : 𝓞 p.B.host.E) ∈ P.asIdeal := fun h ↦ hpd (by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)

      have hδ : (if p.B.places.resChar w = p.B.host.pde then p.f.del' else p.f.del).UnrAt P := by
        split_ifs
        · exact p.f.isDel'.unr P h2
        · exact p.f.isDel.unr P h1
      have hψ : ¬ (p.T.psi w).UnrAt P := fun h ↦ hram (Formalism.L2.Host.HChar.UnrAt.mul hδ h)
      have hQ : P ∈ p.T.Q w := by
        by_contra hq
        exact hψ (((p.T.psi_is w).ram P).2 hq)
      refine ⟨fun hm ↦ ?_, (hn w hw).1 ▸ hQ⟩

      have e1 : p.T.xiTw p.f w = 1 := by
        rw [← hmu.tw w, ← hmu.on w hw]
        exact (congrArg p.w.I.xi hm).trans hmu.mu0
      rw [e1] at hram
      exact hram (Formalism.L2.Fam.DivCQ.unrAt_one P)

end GlobalTheory.Plug.RaysW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SmallFrameAtColumn
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2
  GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmallExact

theorem normDescent : ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (n : ℕ)
    (𝔓 : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E), (Ideal.absNorm 𝔓.asIdeal).Prime → 𝔓.asIdeal = Ideal.span {π} →
    π - 1 ∈ Ideal.span {(n : 𝓞 E)} → ∃ 𝔭 : HeightOneSpectrum (𝓞 K),
      𝔓.asIdeal.comap (algebraMap (𝓞 K) (𝓞 E)) = 𝔭.asIdeal ∧ Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal ∧
      ∃ α : 𝓞 K, 𝔭.asIdeal = Ideal.span {α} ∧ α - 1 ∈ Ideal.span {(n : 𝓞 K)} := by
  intro K E _ _ _ _ _ n 𝔓 π hp hπ hπ1
  haveI := 𝔓.isMaximal
  set q := 𝔓.asIdeal with hq
  set p := q.under (𝓞 K) with hpd
  haveI : p.IsMaximal := inferInstance
  have hrel : Ideal.relNorm (𝓞 K) q = p ^ q.inertiaDeg (𝓞 K) := Ideal.relNorm_eq_pow_of_isMaximal q p
  have hab : Ideal.absNorm q = Ideal.absNorm p ^ q.inertiaDeg (𝓞 K) := by
    rw [← map_pow Ideal.absNorm p, ← hrel, Ideal.absNorm_relNorm]
  have h := (Nat.Prime.pow_eq_iff hp).1 hab.symm
  have hne : p ≠ ⊥ := fun h0 => by
    have : Ideal.absNorm p = 0 := by rw [h0]; simp
    rw [this] at h
    exact hp.ne_zero h.1.symm
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, inferInstance, hne⟩
  refine ⟨𝔭, rfl, h.1.symm, Algebra.intNorm (𝓞 K) (𝓞 E) π, ?_, ?_⟩
  · change p = _
    calc p = p ^ q.inertiaDeg (𝓞 K) := by rw [h.2, pow_one]
      _ = Ideal.relNorm (𝓞 K) q := hrel.symm
      _ = _ := by rw [hπ, Ideal.relNorm_singleton]
  · exact Ideal.mem_span_singleton.2
      (GlobalTheory.RayDescent.dvd_intNorm_sub_one K E n π (Ideal.mem_span_singleton.1 hπ1))

theorem rayLe : ∀ (K E L Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra K E] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field Ω]
    [Algebra E Ω] [Algebra K Ω] [IsScalarTower K E Ω] (n : ℕ), 0 < n →
    GlobalTheory.FieldSize.IsRay L (Ideal.span {(n : 𝓞 K)}) → ∀ (R : IntermediateField E Ω) [NumberField R] [IsAbelianGalois E R],
    GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 E)}) → ∀ (j : L →ₐ[K] Ω) (x : L), j x ∈ R := by
  intro K E L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n hn hL R _ _ hR j x
  classical
  let b := Module.Free.chooseBasis K L
  let M' : IntermediateField E Ω := IntermediateField.adjoin E (Set.range fun i => j (b i))
  have hint : ∀ z ∈ Set.range (fun i => j (b i)), IsIntegral E z := by
    rintro _ ⟨i, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := K) (b i)).map j).tower_top
  haveI : FiniteDimensional E M' := IntermediateField.finiteDimensional_adjoin hint
  haveI : NumberField M' := NumberField.of_module_finite E M'
  have hmem : ∀ y, j y ∈ M' := by
    intro y
    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply K E Ω]
    exact mul_mem (M'.algebraMap_mem _) (IntermediateField.subset_adjoin E _ ⟨i, rfl⟩)
  let f : L →ₐ[K] M' :=
    { toFun := fun y => ⟨j y, hmem y⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' := fun y z => Subtype.ext (map_mul j y z)
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun y z => Subtype.ext (map_add j y z)
      commutes' := fun c => Subtype.ext (j.commutes c) }
  have hgen : ∀ (N : Type) [Field N] [Algebra E N] (g g' : M' →ₐ[E] N), (∀ y, g (f y) = g' (f y)) → g = g' := by
    intro N _ _ g g' hg
    refine IntermediateField.adjoin_algHom_ext E fun z hz => ?_
    obtain ⟨i, rfl⟩ := hz
    exact hg (b i)
  have hle : M' ≤ R := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split E Ω R M' ?_
    have hne : Ideal.span {(n : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hn.ne'
    refine (Ideal.finite_factors hne).subset ?_
    rintro 𝔓 ⟨hp, hsplR, hnot⟩
    by_contra hdvd
    apply hnot
    have hn𝔓 : (n : 𝓞 E) ∉ 𝔓.asIdeal := fun h =>
      hdvd (Ideal.dvd_iff_le.2 (Ideal.span_singleton_le_iff_mem _ |>.2 h))
    obtain ⟨π, hπ, hπ1⟩ := (GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff E R n hn hR 𝔓 hn𝔓).1 hsplR
    obtain ⟨𝔭, hover, hnorm, α, hα, hα1⟩ := normDescent K E n 𝔓 π hp hπ hπ1
    have hn𝔭 : (n : 𝓞 K) ∉ 𝔭.asIdeal := fun h => hn𝔓 (by
      rw [← hover, Ideal.mem_comap, map_natCast] at h
      exact h)
    have hsplL := (GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff K L n hn hL 𝔭 hn𝔭).2 ⟨α, hα, hα1⟩
    exact GlobalTheory.SplitCompositum.ncard_eq_finrank_of_generated K E L M' f hgen 𝔭 𝔓 hover hnorm hsplL
  exact hle (hmem x)

theorem rayLeC : ∀ (K E L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra K E] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (n : ℕ), 0 < n →
    GlobalTheory.FieldSize.IsRay L (Ideal.span {(n : 𝓞 K)}) → ∀ (φ : E →+* ℂ) (M : IntermediateField ℚ ℂ),
    GlobalTheory.Mem.Fld.IsRayFieldIn φ (GlobalTheory.Mem.Fld.natIdeal E n) M →
    ∃ j : L →+* ℂ, j.comp (algebraMap K L) = φ.comp (algebraMap K E) ∧ ∀ x, j x ∈ M := by
  intro K E L _ _ _ _ _ _ _ _ _ _ _ n hn hL φ M hM
  obtain ⟨hm, hNF, hray⟩ := hM
  letI := hNF
  letI : Algebra E M := GlobalTheory.Mem.Fld.algOf φ M hm
  letI : Algebra E ℂ := φ.toAlgebra
  letI : Algebra K ℂ := ((algebraMap E ℂ).comp (algebraMap K E)).toAlgebra
  haveI : IsScalarTower K E ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let R : IntermediateField E ℂ := M.toSubfield.toIntermediateField hm
  let e : M ≃ₐ[E] R :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : FiniteDimensional ℚ R := e.toRingEquiv.toRatAlgEquiv.toLinearEquiv.finiteDimensional
  haveI : NumberField R := NumberField.of_module_finite ℚ _
  have hR : GlobalTheory.Mem.Fld.IsRayField E R (GlobalTheory.Mem.Fld.natIdeal E n) := hray.of_algEquiv e
  haveI : IsAbelianGalois E R := hR.1
  let j : L →ₐ[K] ℂ := IsAlgClosed.lift
  have hsub := rayLe K E L ℂ n hn hL R hR.2 j
  exact ⟨(j : L →+* ℂ), j.comp_algebraMap, fun x => hsub x⟩

theorem smallHas_of_rayField : GlobalTheory.NT.RayField → ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T)
    (Z : w.Lt), SmallHas (w.D Z) (Fr.at (w.st Z) f) := by
  intro hRF B f T w Z
  have hLL0 : ∀ z ∈ B.fixedCoefficientFieldInComplex, z ∈ (Formalism.L2.Host.embLL0 (w.D Z)).fieldRange := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hKs : ∀ z ∈ B.KsC, z ∈ (Formalism.L2.Host.embLL0 (w.D Z)).fieldRange := fun z hz => hLL0 z (B.KsC_le_LL0C hz)
  refine ⟨w.val _ _ _ _ _ _, ?_, ?_⟩
  · have hN : GlobalTheory.Mem.Fld.modulus B.toPre ≠ 0 := GlobalTheory.Mem.Fld.modulus_ne_zero _
    have hray : w.δ.ray ≤ B.KsC := ((GlobalTheory.Mem.Fld.listField_le_iff _ _).1 (le_of_eq w.exact.symm)).2.2.1
    haveI := GlobalTheory.Mem.NormPrime.isTotallyComplex_K B.host
    have h0 : Ideal.span {((GlobalTheory.Mem.Fld.modulus B.toPre : ℕ) : 𝓞 B.host.K)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN
    obtain ⟨L, _, _, _, hab, hun, hgen, hart⟩ := hRF B.host.K _ h0
    obtain ⟨j, hj, hjM⟩ := rayLeC B.host.K B.host.E L (GlobalTheory.Mem.Fld.modulus B.toPre) (Nat.pos_of_ne_zero hN)
      ⟨hun, hgen, hart⟩ B.host.φ₀ w.δ.ray w.δ.isRay
    exact ⟨L, _, _, _, hab, ⟨hun, hgen, hart⟩, j, hj, fun x => hKs _ (hray (hjM x))⟩
  · intro k z hz
    have hg := B.host.g_prime k
    have hz' : z ∈ GlobalTheory.Mem.Fld.cycField (B.host.g k * (B.host.g k - 1)) :=
      GlobalTheory.Mem.Fld.mem_cycField (mul_ne_zero hg.ne_zero (by have := hg.two_le; omega)) hz
    have hle : GlobalTheory.Mem.Fld.cycField (B.host.g k * (B.host.g k - 1)) ≤ GlobalTheory.Mem.Fld.rootsField B.toPre := by
      fin_cases k
      · exact ((le_sup_right.trans le_sup_left).trans le_sup_left).trans le_sup_left
      · exact (le_sup_right.trans le_sup_left).trans le_sup_left
    exact hKs _ (B.rootsField_le_KsC (hle hz'))

end GlobalTheory.SmallExact

end
end

