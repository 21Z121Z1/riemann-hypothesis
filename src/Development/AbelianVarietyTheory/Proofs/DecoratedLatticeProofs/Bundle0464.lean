import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0446
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SettingNormaliser
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockDoubleCosetOperatorKeepsLevelCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerBlockDoubleCosetOperator_keeps_levelCharacter : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ (ξl : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι → ∀ (ϖ : (Fv D.host.F v)ˣ) (e : Blocks j D.R.t → ℤ) (R : Finset (GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v))) (d : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → (Fv D.host.F v)ˣ), GlobalTheory.ParHecke.IsReps (GlobalTheory.ZonalCellDecomposition.mtor ϖ e) R d → ∀ F : GA D s.V → ℂ, (∀ κ ∈ Lev.levG s.V s.β s.L, ∀ g, F (g * κ) = Lev.levChi s.V s.β s.L κ * F g) → ∀ κ ∈ Lev.levG s.V s.β s.L, ∀ g, ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * κ * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) = Lev.levChi s.V s.β s.L κ * ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
  first | exact @GlobalTheory.LowerBlockHecke.hecke_level | exact GlobalTheory.LowerBlockHecke.hecke_level | (intros; apply GlobalTheory.LowerBlockHecke.hecke_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottom
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LevNorm

open Formalism.BasicNotions.TH

theorem embA_injective {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) :
    Function.Injective (embA d o) := fun _ _ h =>
  congrArg Prod.fst (o.emb_injective (d.wittDecomp_anisotropicEmbedding_injective h))

theorem finf_sand {D : D7} {k n : ℕ} (p : Mx D k n) (m : Mx D n n) (j : Mx D n k) (hm : m.map (CenAct.finf D) = 1)
    (h : p ⬝ j = 1) : (p ⬝ (m ⬝ j)).map (CenAct.finf D) = 1 := by
  rw [← Matrix.mul_assoc, CenAct.map_sand p m j hm, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_GfC_of_embA {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {a : GA D A}
    (h : embA d o a ∈ GfC S) : a ∈ GfC A := by
  rw [embA_apply, CenAct.mem_GfC_iff] at h
  have h1 := finf_sand d.p0 _ d.j0 h d.p0_j0
  rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul] at h1
  have h2 := finf_sand o.pA _ o.jA h1 o.pA_jA
  rw [o.emb_jA, cancel₂ o.pA_jA, Matrix.one_mul] at h2
  exact (CenAct.mem_GfC_iff _ _).2 h2

theorem matches_differ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hρ : 1 ≤ D.R.rS)
    (u : D.what₂.Word) {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)
    {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {t t' : GA D (D.sp.Y 0)} (ht : Matches X h J χ t) (ht' : Matches X h J χ t') :
    ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ k ∈ J,
      t = ((iotaX X h).symm (1, X.xu u))⁻¹ * embA B.d B.o a * (iotaX X h).symm (1, X.xu u) * z * t' * k := by
  let j : X.B.I.Gf →* GA D (D.sp.Y 0) := ((iotaX X h).symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : ∀ x, iotaX X h (j x) = (1, x) := fun x => (iotaX X h).apply_symm_apply _
  have hjG : ∀ x, j x ∈ GfC (D.sp.Y 0) := fun x => (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h _).1 (by rw [hj])
  have hjJ : ∀ x, j x ∈ rowJ X h ↔ x ∈ X.K2 := fun x => by
    show (iotaX X h (j x)).1 = 1 ∧ (iotaX X h (j x)).2 ∈ X.K2 ↔ _
    rw [hj]
    exact and_iff_right rfl
  have hjχ : ∀ x, rowChi X h (j x) = star (X.chi2 x) := fun x => by
    show star (X.chi2 (iotaX X h (j x)).2) = _
    rw [hj]
  obtain ⟨y, hy⟩ : ∃ y, j y = t * t'⁻¹ := ⟨_, GlobalTheory.SeeConjRead.eq_symm_one X h _
    ((GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h _).2 (mul_mem ht.1 (inv_mem ht'.1)))⟩
  have e1 : ∀ x, t'⁻¹⁻¹ * (t'⁻¹ * j x * t') * t'⁻¹ = j x := fun x => by group
  have e2 : ∀ x, t⁻¹⁻¹ * (t'⁻¹ * j x * t') * t⁻¹ = j (y * x * y⁻¹) := fun x => by
    rw [map_mul, map_mul, map_inv, hy]; group
  have hJ : ∀ x, t'⁻¹ * j x * t' ∈ J ↔ x ∈ X.K2 := fun x => by rw [(ht'.2 _).1, e1, hjJ]
  obtain ⟨z, hz, w, hw, hw', k, hk, e⟩ := setting_normaliser X h hρ u y fun x =>
    ⟨by rw [← hJ, (ht.2 _).1, e2, hjJ], fun hx => by
      rw [← hjχ, ← hjχ, ← e2, (ht.2 _).2 ((hJ x).2 hx), ← (ht'.2 _).2 ((hJ x).2 hx), e1]⟩
  obtain ⟨a, ha⟩ := (B.tieH (j w)).2 (by rw [hj]; exact ⟨one_mem _, hw⟩)
  refine ⟨j z, hjG z, Subgroup.mem_center_iff.2 fun g => (iotaX X h).injective ?_, a,
    mem_GfC_of_embA B.d B.o (ha ▸ hjG w), Subgroup.mem_center_iff.2 fun b => embA_injective B.d B.o ((iotaX X h).injective ?_),
    t'⁻¹ * j k * t', (hJ k).2 hk, ?_⟩
  · rw [map_mul, map_mul, hj]
    exact Prod.ext (by simp) (Subgroup.mem_center_iff.1 hz _)
  · rw [map_mul, map_mul, map_mul, map_mul, ha, hj]
    exact Prod.ext (by simp) (hw' _ ((B.tieH _).1 ⟨b, rfl⟩).2).symm
  · show t = (j (X.xu u))⁻¹ * embA B.d B.o a * j (X.xu u) * j z * t' * (t'⁻¹ * j k * t')
    rw [ha]
    have e3 := congrArg j e
    rw [hy, map_mul, map_mul, map_mul, map_mul, map_inv] at e3
    calc t = t * t'⁻¹ * t' := by group
      _ = _ := by rw [e3]; group

end GlobalTheory.LevNorm

theorem GlobalTheory.MiTop.matches_differ_central : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → 1 ≤ D.R.rS → ∀ (u : D.what₂.Word) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ t ∈ GfC (D.sp.Y 0), ∀ t' ∈ GfC (D.sp.Y 0), Matches W.S.X W.Q.instEq (rJ W) (rChi W) t → Matches W.S.X W.Q.instEq (rJ W) (rChi W) t' → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ ∃ k ∈ rJ W, t = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o a * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * z * t' * k := by
  intro D L hT Gi Gl Kc Yd cX ex W _ hρ u B t _ t' _ ht ht'
  exact GlobalTheory.LevNorm.matches_differ W.S.X W.Q.instEq hρ u B ht ht'

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryIntegralityCongruence
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.TraceBwd

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colGroup_of_embX {s κ τ : ℕ} (S : SymData k s κ) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : embX (s + 1) g ∈ ((S.T (Fin τ)).lev 0 (s + 1) (Nat.zero_add _)).J) : g ∈ colGroup k κ (Fin τ) := by
  obtain ⟨h1, -, -⟩ := GlobalTheory.FirstVertexFrame.firstVertex_typeChain k S.ψ S.ϖ s (Fin τ) κ S.P
    (GlobalTheory.SymShape.sym_shape _ _ _ _ _ _ _ S.sym) S.μ S.tame (s + 1) (Nat.zero_add _)
  rw [← h1]
  refine ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, ?_⟩⟩
  · rw [one_mul]
    exact (le_sup_left : (embX (s + 1)).range ≤ R k _ (s + 1) 1) ⟨g, rfl⟩
  · rw [inv_one, one_mul, mul_one, one_mul]
    exact hg

theorem entries_of_colGroup {κ τ n : ℕ} (e : XIx (Fin κ) (Fin τ) 0 ≃ Fin n) (he : IsOrd xPos e) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : g ∈ colGroup k κ (Fin τ)) (a b : XIx (Fin κ) (Fin τ) 0) :
    g.val a b ∈ 𝒪[k] ∧ (e b ≤ e a → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1) := by
  have hp : ∀ c, colPos κ (Fin τ) c = (e c).val := fun c => by
    rw [he c]
    rcases c with (c | c) | c
    exacts [rfl, c.elim0, c.1.elim0]
  obtain ⟨_, ⟨g₀, rfl, rfl⟩, hu⟩ := hg
  refine ⟨(g₀.val a b).2, fun hab => ?_⟩
  have h1 : residue 𝒪[k] (g₀.val a b) = (1 : Matrix _ _ 𝓀[k]) a b := hu a b (by rw [hp, hp]; exact hab)
  have h2 : (1 : Matrix _ _ 𝓀[k]) a b = residue 𝒪[k] ((1 : Matrix _ _ 𝒪[k]) a b) := by
    simp only [Matrix.one_apply, apply_ite (residue 𝒪[k]), map_one, map_zero]
  rw [h2, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at h1
  have h3 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h1
  convert h3 using 2
  simp only [Matrix.one_apply]
  split_ifs <;> rfl

theorem exists_mat {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k V.rank Y) (e : Y ≃ Fin V.rank) (hβ : F.β = (1 : Matrix (Fin V.rank) (Fin V.rank) k).submatrix id e) (x : GA D V) :
    ∃ g : GL Y k, (mt V x).map q.pr = F.β * g.val * F.γ ∧ ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := by
  have hmul : ∀ y z : GA D V, y * z = 1 → (F.γ * (mt V y).map q.pr * F.β) * (F.γ * (mt V z).map q.pr * F.β) = 1 := fun y z h => by
    have h1 : mt V y * mt V z = 1 := by
      have h2 : mt V y * mt V z = mt V (y * z) := rfl
      rw [h2, h]
      rfl
    have h3 : (mt V y).map q.pr * (mt V z).map q.pr = 1 := by
      rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc _ = F.γ * ((mt V y).map q.pr * (F.β * F.γ) * (mt V z).map q.pr) * F.β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.βγ, Matrix.mul_one, h3, Matrix.mul_one, F.γβ]
  let g : GL Y k := ⟨_, _, hmul x x⁻¹ (mul_inv_cancel x), hmul x⁻¹ x (inv_mul_cancel x)⟩
  have hg : (mt V x).map q.pr = F.β * g.val * F.γ := by
    calc _ = (F.β * F.γ) * (mt V x).map q.pr * (F.β * F.γ) := by rw [F.βγ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [g, Matrix.mul_assoc]
  refine ⟨g, hg, fun a b => ?_⟩
  have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (e a)) b
  rw [hβ] at h2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm

end Loc

set_option maxHeartbeats 1000000 in

theorem pattern_of_traceAtG : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ κ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X 0), GlobalTheory.FamTrace.TraceAtG a κ → ∀ i : Fin a.n, ∀ r c : Fin ((I.rec7 l Z).sp.X 0).rank, ((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r c) < 1) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ κ hκ i r c
  obtain ⟨e, he, hβ⟩ := (ha.stdG i).1 0 (Nat.zero_le _)
  obtain ⟨g, hg, hgM⟩ := exists_mat (a.G i).q ((I.rec7 l Z).sp.X 0) _ e hβ κ
  obtain ⟨r, rfl⟩ := e.surjective r
  obtain ⟨c, rfl⟩ := e.surjective c
  have h := entries_of_colGroup e he g (colGroup_of_embX (a.G i).S g (hκ i g hg)) r c
  rw [hgM] at h
  refine ⟨h.1, fun hcr => ?_⟩
  have h1 : (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) (e r) (e c) =
      (1 : Matrix _ _ (a.G i).k) r c := by
    simp only [Matrix.one_apply, e.injective.eq_iff]
  rw [h1]
  exact h.2 hcr

end GlobalTheory.FamTrace.TraceBwd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.TopLevQ.moved_mat {k Z : Type} [Field k] [Fintype Z] [DecidableEq Z] {n : ℕ} (β : Matrix (Fin n) Z k) (γ : Matrix Z (Fin n) k) (hγβ : γ * β = 1) (x : Matrix Z Z k) (e : Z ≃ Fin n) : β * x * γ * β.submatrix id e.symm = β.submatrix id e.symm * x.submatrix e.symm e.symm := by
  rw [Matrix.submatrix_mul_equiv β x id e.symm e.symm, Matrix.mul_assoc (β * x)]
  have h1 : γ * β.submatrix id e.symm = (γ * β).submatrix id e.symm := by
    ext i j; simp [Matrix.mul_apply]
  rw [h1, hγβ]
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem GlobalTheory.TopLevQ.suppAt_conj {D : D7} {e : AE D} {V : HSp D} (g b : GA D V) (hg : Formalism.L2.Theta.SuppAt e V g) :
    Formalism.L2.Theta.SuppAt e V (b⁻¹ * g * b) := by
  have hm : ∀ x y : GA D V, Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := fun x y => by
    unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl
  have h1 : Formalism.L2.Theta.mt V b⁻¹ * Formalism.L2.Theta.mt V b = 1 := by
    rw [← hm, inv_mul_cancel]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have key : Formalism.L2.Theta.mt V (b⁻¹ * g * b) - 1 =
      Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b := by
    rw [hm, hm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have hg' : (e + (cA D) e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
    ext i j; exact hg i j
  have h2 : (e + (cA D) e) • (Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b) =
      Formalism.L2.Theta.mt V b⁻¹ * ((e + (cA D) e) • (Formalism.L2.Theta.mt V g - 1)) * Formalism.L2.Theta.mt V b := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hg'] at h2
  intro i j
  rw [key]
  exact congrFun (congrFun h2 i) j

theorem GlobalTheory.TopLevQ.blk_iff {K : Type} [Field K] [ValuativeRel K] {κ τ s n : ℕ}
    (e : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin n) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e)
    (x : Matrix (GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2)) (GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2)) K) :
    (∀ i j : Fin n, Formalism.L2.DIV.blk2 (κ + (s + 1)) j < Formalism.L2.DIV.blk2 (κ + (s + 1)) i →
      ValuativeRel.valuation K (x (e.symm i) (e.symm j)) < 1) ↔ GlobalTheory.StepData.MaxM x.toBlocks₂₁ := by
  have hlo : ∀ a : Fin κ ⊕ Fin (s + 1), (e (Sum.inl a)).val < κ + (s + 1) := by
    intro a; rw [he]; rcases a with a | a <;> simp [GlobalTheory.SymBridge.zPos] <;> omega
  have hhi : ∀ p : Fin (s + 2) × Fin τ, κ + (s + 1) ≤ (e (Sum.inr p)).val := by
    intro p; rw [he]; simp only [GlobalTheory.SymBridge.zPos]; exact Nat.le_add_right_of_le (Nat.le_add_right _ _)
  constructor
  · intro h p a
    have := h (e (Sum.inr p)) (e (Sum.inl a)) (by
      simp only [Formalism.L2.DIV.blk2, if_pos (hlo a), if_neg (Nat.not_lt.2 (hhi p))]; omega)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  · intro h i j hij
    have hj : j.val < κ + (s + 1) := by
      by_contra hc
      simp only [Formalism.L2.DIV.blk2, if_neg hc] at hij
      split_ifs at hij <;> omega
    have hi : ¬ i.val < κ + (s + 1) := by
      intro hc
      simp only [Formalism.L2.DIV.blk2, if_pos hc, if_pos hj] at hij
      omega
    obtain ⟨p, hp⟩ : ∃ p, e.symm i = Sum.inr p := by
      rcases hi' : e.symm i with a | p
      · exfalso; apply hi; have := hlo a; rw [← hi', Equiv.apply_symm_apply] at this; exact this
      · exact ⟨p, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a, e.symm j = Sum.inl a := by
      rcases hj' : e.symm j with a | p
      · exact ⟨a, rfl⟩
      · exfalso; have := hhi p; rw [← hj', Equiv.apply_symm_apply] at this; omega
    rw [hp, ha]
    exact h p a

theorem GlobalTheory.TopLevQ.mem_levS_iff {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (y : GA D V) :
    y ∈ levS V β L ↔ y ∈ GfC V ∧ ((Lev.finE V y ∈ Formalism.L2.DIV.St β ∧
        (∀ PP' ∈ L.Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V y) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
        ∀ PP' ∈ L.Q, Formalism.L2.DIV.redFn β PP' (Lev.finE V y) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 L.r)) ∧
        Formalism.L2.DIV.rTup β L (Lev.finE V y) ∈ L.P.H) := by
  show y ∈ GfC V ⊓ Subgroup.comap (Lev.finE V) (Formalism.L2.DIV.lev _ _ β L) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  show _ ∧ (_ ∈ Formalism.L2.DIV.parLev _ _ _ _ ∧ _) ↔ _
  rw [Formalism.L2.DIV.mem_parLev]
  simp only [GlobalTheory.LevSplit.finE_mem_UA, true_and]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSph
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TopVol
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

def datSph (W : RealPack ex) : LevDat (I.rec7 l Z).host.E ℂ (I.rec7 l Z).sp.X'.rank :=
  { datXP (pk W) (lvP W) W.P.A3.A.μ0 with Q := ∅ }

def levSph (W : RealPack ex) (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :=
  (Formalism.IndefR.Lev.levG _ (pk W).βX (datSph W)).comap (MulAut.conj x⁻¹).toMonoidHom

def levTw (W : RealPack ex) (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (t : W.P.T) : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :=
  (Formalism.IndefR.Lev.levG _ (pk W).βX (datXP (pk W) (lvP W) t)).comap (MulAut.conj x⁻¹).toMonoidHom

theorem mem_levSph {W : RealPack ex} {x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'} (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :
    h ∈ levSph W x ↔ x⁻¹ * h * x ∈ levS _ (pk W).βX (datSph W) := by
  simp [levSph, levS, MulAut.conj_apply]

theorem mem_levTw {W : RealPack ex} {x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'} {t : W.P.T} (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :
    h ∈ levTw W x t ↔ x⁻¹ * h * x ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t) := by
  simp [levTw, levS, MulAut.conj_apply]

end GlobalTheory.TopVol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LevGlue

theorem mem_levS_datY_single : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ Q → (∀ PP' ∈ Pg, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F)) → (∀ PP' ∈ Q, PP'.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) → PP' = PP) → ∀ (κ : GA D V), κ ∈ GfC V → (∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) → Lev.finE V κ ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1) → (κ ∈ levS V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) ↔ Lev.finE V κ ∈ Formalism.L2.DIV.St β ∧ Formalism.L2.DIV.redFn β PP (Lev.finE V κ) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) ∧ (Lev.finE V κ ∈ Formalism.L2.DIV.St β → Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) κ = (((ξ PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 (Formalism.L2.DIV.redFn β PP (Lev.finE V κ))))⁻¹ : ℂˣ) : ℂ)) := by
  intro D V β r t j hr Pg Q P χ ξ PP hPQ hPg hQ κ hκ hoff
  have hPgoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP => hoff PP' (hPg PP' hP) hSt
  have hQoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Q, PP' ≠ PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP hne => hoff PP' (fun e => hne (hQ PP' hP e)) hSt
  have hrt : Lev.finE V κ ∈ Formalism.L2.DIV.St β →
      Formalism.L2.DIV.rTup β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) (Lev.finE V κ) = 1 := by
    intro hSt
    funext PP'
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP'.1 _) = 1
    rw [hPgoff hSt _ PP'.2]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  refine ⟨⟨fun h => ?_, fun ⟨hSt, hP⟩ => ?_⟩, fun hSt => ?_⟩
  · have h' : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) := h
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev] at h'
    obtain ⟨_, ⟨_, hSt, _, hq⟩, _⟩ := h'
    exact ⟨hSt, hq PP hPQ⟩
  · show κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B)
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
    refine ⟨hκ, ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, ?_, ?_⟩, ?_⟩
    · intro PP' hP'
      rw [hPgoff hSt PP' hP']
      exact one_mem _
    · intro PP' hP'
      by_cases e : PP' = PP
      · rw [e]
        exact hP
      · rw [hQoff hSt PP' hP' e]
        exact one_mem _
    · rw [hrt hSt]
      exact one_mem _
  · simp only [Lev.levChi]
    congr 1
    simp only [Formalism.L2.DIV.levFn]
    rw [hrt hSt, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul]
    rw [Finset.prod_eq_one (fun PP' hP' => Finset.prod_eq_one fun c _ => by
      rw [hPgoff hSt PP' hP', Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]), one_mul]
    rw [Finset.prod_eq_single_of_mem (s := (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B).Q) PP hPQ fun PP' hP hne => by
      rw [hQoff hSt PP' hP hne, Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]]
    simp [Lev.datY]

end GlobalTheory.LevGlue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveSplitSupportInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.move_split_support_invariant : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → A.MoveAt θ i hi c₀ g h → ∀ e, IsSplitIdem (I.rec7 l Z) e → ∀ s s', SuppAt e _ s → SuppAt e _ s' → A.MoveAt θ i hi c₀ (s * g) (s' * h) := by
  first | exact @GlobalTheory.AdForm.SplitMove.moveAt_split | exact GlobalTheory.AdForm.SplitMove.moveAt_split | (intros; apply GlobalTheory.AdForm.SplitMove.moveAt_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedLatticeIndexZeroNormalFrameComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZero

set_option maxHeartbeats 1000000 in

theorem latV_normalFrame_zero_loc : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)), GlobalTheory.LevZero.LocAt G PP b β → ∀ (a : ℕ) (ha : 0 + a = G.s + 1) (Λ L : GlobalTheory.FinPl.Lat (c.V 0)), Formalism.L2.DIV.IsFrame β Λ → GlobalTheory.FinPl.Moves (c.V 0) b Λ L (· = G.q.v) → ∀ y : XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin a → G.k, (fun r => G.q.sec (((G.FY 0 a ha).β *ᵥ y) r)) ∈ GlobalTheory.FinPl.latV (c.V 0) L (· = G.q.v) ↔ (∀ z, y (Sum.inl z) ∈ 𝒪[G.k]) ∧ ∀ i : Fin a, ((((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹ * y (Sum.inr i)) ∈ 𝒪[G.k] := by
  intro D c v G PP b β hloc n hn Λ L hβ hmv y
  obtain rfl : n = G.s + 1 := by omega
  obtain ⟨e, -, hM⟩ := hloc.frame (G.s + 1) hn
  obtain ⟨B, hB1, hB2⟩ := GlobalTheory.LocMod.PinEx.exists_topFrame G.q hloc.idem (c.V 0) Λ β hβ
  have hb := GlobalTheory.LocMod.liftM_map β.val
  have h1 := hM _ hb
  have h2 := hB1 _ hb
  rw [GlobalTheory.LocMod.mt_one_gaMat, Matrix.one_mul] at h2
  rw [Matrix.map_mul, h2] at h1
  let ε := e.symm.trans (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hn)
  let X := (G.FY 0 (G.s + 1) hn).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn).val
  let P := (mt (c.V 0) b).map G.q.pr
  let Pi := (mt (c.V 0) b⁻¹).map G.q.pr
  have h1' : P * B.val = X.submatrix id ε := h1
  have hPPi : P * Pi = 1 := by
    change (mt (c.V 0) b).map G.q.pr * (mt (c.V 0) b⁻¹).map G.q.pr = 1
    rw [← Matrix.map_mul, ← GlobalTheory.LocMod.mt_mul_gaMat, mul_inv_cancel, GlobalTheory.LocMod.mt_one_gaMat,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hPiP : Pi * P = 1 := by
    change (mt (c.V 0) b⁻¹).map G.q.pr * (mt (c.V 0) b).map G.q.pr = 1
    rw [← Matrix.map_mul, ← GlobalTheory.LocMod.mt_mul_gaMat, inv_mul_cancel, GlobalTheory.LocMod.mt_one_gaMat,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : X = (P * B.val).submatrix id ε.symm := by
    rw [h1', submatrix_submatrix, Function.comp_id, Equiv.self_comp_symm, submatrix_id_id]
  let z := (((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn)⁻¹).val *ᵥ y
  have hw : (G.FY 0 (G.s + 1) hn).β *ᵥ y = (P * B.val) *ᵥ (z ∘ ε) := by
    have e1 : (G.FY 0 (G.s + 1) hn).β *ᵥ y = X *ᵥ z := by
      change _ = ((G.FY 0 (G.s + 1) hn).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn).val) *ᵥ
        ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn)⁻¹).val *ᵥ y)
      rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [e1, hX, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_id]
  have key : (fun r => G.q.sec (((G.FY 0 (G.s + 1) hn).β *ᵥ y) r)) =
      mt (c.V 0) b *ᵥ (fun r => G.q.sec ((Pi *ᵥ ((G.FY 0 (G.s + 1) hn).β *ᵥ y)) r)) := by
    rw [GlobalTheory.Core.Mi.LatMatch.mulVec_sec_split]
    change _ = fun r => G.q.sec ((P *ᵥ (Pi *ᵥ _)) r)
    rw [mulVec_mulVec, hPPi, one_mulVec]
  rw [key, ← hmv _ (fun i => GlobalTheory.FrameGlob.sec_mem_idAt G.q _), hB2, hw, mulVec_mulVec, mulVec_mulVec]
  have hB : (B⁻¹).val * Pi * (P * B.val) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPiP, Matrix.one_mul, Units.inv_mul]
  rw [hB, one_mulVec]
  have hz : ∀ w, z w = (GlobalTheory.LevZeroUp.scal (Fin D.R.t) G.S.ϖ w)⁻¹ * y w := by
    intro w
    change ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val *ᵥ y) w = _
    rw [GlobalTheory.LevZeroUp.bas_inv_val, mulVec_diagonal]
  have hall : (∀ i, (z ∘ ε) i ∈ 𝒪[G.k]) ↔ ∀ w, z w ∈ 𝒪[G.k] :=
    ⟨fun h w => by simpa using h (ε.symm w), fun h i => h _⟩
  rw [hall, Sum.forall]
  refine and_congr (forall_congr' fun w => ?_) (forall_congr' fun i => ?_)
  · rw [hz]
    simp [GlobalTheory.LevZeroUp.scal]
  · rw [hz]
    rfl

end GlobalTheory.LevZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumAtIdentityNonzeroConstantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVacuum_at_identity_nonzero_constant : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac 1 1 := by
  first | exact @GlobalTheory.AdForm.VacAllBase.moveT_one | exact GlobalTheory.AdForm.VacAllBase.moveT_one | (intros; apply GlobalTheory.AdForm.VacAllBase.moveT_one <;> assumption)
end

