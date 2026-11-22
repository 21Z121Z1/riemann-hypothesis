import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0519
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0520
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftWittIndexVanishingStatement
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
theorem _root_.GlobalTheory.T.theta_lift_witt_index_vanishing : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DoublingMethod → ∀ D : D7, SiegelWeilFock D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsFockVec ψ θ A B sA sB Φ → (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧ GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  first | exact @GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth | exact GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth | (intros; apply GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.RealTrue

theorem ontoUni_reindex {ι K : Type} [Group K] [TopologicalSpace K] {a b : ℕ} (h : a = b)
    {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) :
    OntoUni fun k τ => (r k τ).reindex (finCongr h) (finCongr h) := by
  subst h; simpa using hr

theorem ontoUni_one {ι K : Type} [Group K] [TopologicalSpace K] {a : ℕ}
    {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) (τ : ι) : r 1 τ = 1 := by
  have hm := hr.mul 1 1 τ
  rw [mul_one] at hm
  have hu := Matrix.mem_unitaryGroup_iff'.1 (hr.uni 1 τ)
  calc r 1 τ = (star (r 1 τ) * r 1 τ) * r 1 τ := by rw [hu, Matrix.one_mul]
    _ = star (r 1 τ) * (r 1 τ * r 1 τ) := Matrix.mul_assoc _ _ _
    _ = 1 := by rw [← hm, hu]

theorem inN_one {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    inN θ V (fun _ => 1) hn g τ = infM θ V hn g τ := by
  simp [inN, GlobalTheory.SeeSaw.inB, infM]

theorem valC_transport {ι : Type} [Fintype ι] {n : ℕ} {G G' : ι → Matrix (Fin n) (Fin n) ℂ} (h : G = G')
    (lam : ι → DomWeight n) (f : Formalism.L2.Forms.Frames G → ℂ) (hf : f ∈ ValC G lam) :
    (fun z : Formalism.L2.Forms.Frames G' => f ⟨z.1, z.2⟩) ∈ ValC G' lam := by
  subst h; exact hf

end GlobalTheory.RealTrue

open GlobalTheory.RealTrue in

theorem GlobalTheory.AdForm.realOf_is : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (realOf u R g s J).Is := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hJ hJO hEmb
  have hstd := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hOk hPins l Z R.ψ R.θ hX.std hX.inf
  have hm2 : 2 ≤ B.R.m := B.R.two_le_m
  have hgX : ∀ i, i ≤ B.R.m → ((I.rec7 l Z).sp.X i).gram = 1 := by
    intro i hi
    rcases Nat.lt_or_ge i B.R.m with h | h
    · exact (hstd.1 i h).gS
    · obtain rfl : i = B.R.m := le_antisymm hi h
      have := (hstd.1 (B.R.m - 1) (by omega)).gT
      rwa [show B.R.m - 1 + 1 = B.R.m by omega] at this
  have hrk : ∀ i, i < B.R.m → 0 < B.R.N i ∧ B.R.N i ≤ B.R.N (i + 1) := by
    intro i hi
    have h := (hstd.1 i hi).rk
    rw [rankN (I.rec7 l Z) i hi.le, rankN (I.rec7 l Z) (i + 1) hi] at h
    exact ⟨h.1, h.2.1.le⟩
  have huni : ∀ i (hi : i ≤ B.R.m), OntoUni fun k : GinfC ((I.rec7 l Z).sp.X i) => (realOf u R g s J).r i hi k.1 := by
    intro i hi
    have hB := (hX.xs i hi).2.1
    have := GlobalTheory.SeeSaw.ontoUni_inB (I.rec7 l Z) R.θ ((I.rec7 l Z).sp.X i) (g.x i).B hX.inf (fun τ => by
      rw [hB]; simp [gramAt, hgX i hi])
    exact ontoUni_reindex (rankN (I.rec7 l Z) i hi) this
  have huniT : OntoUni fun k : GinfC (I.rec7 l Z).sp.X' => (realOf u R g s J).rT k.1 := by
    have := GlobalTheory.SeeSaw.ontoUni_inB (I.rec7 l Z) R.θ (I.rec7 l Z).sp.X' (fun _ => 1) hX.inf (fun τ => by
      simp [gramAt, hstd.2.1])
    exact ontoUni_reindex (rankP (I.rec7 l Z)) this
  have hrT : ∀ k, (realOf u R g s J).rT k = infM R.θ _ (rankP (I.rec7 l Z)) k := fun k => funext fun τ => inN_one _ _ _ _ _
  have hone : ∀ τ, infM R.θ _ (rankP (I.rec7 l Z)) 1 τ = 1 := by
    intro τ
    have := ontoUni_one huniT τ
    rw [← hrT]; exact this
  have htr1 : ∀ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (I.rec7 l Z)) 1) z z := by
    intro z τ; rw [hone, Matrix.one_mul]
  have hJ1 : ∀ v, J v 1 = fun z => j v ⟨z.1, z.2⟩ := fun v => funext fun z => hJO v 1 (Subgroup.one_mem _) z z (htr1 z)
  have hG : gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z)) = fun _ => 1 := by
    funext τ; simp [gramC, gramP, hstd.2.1]
  refine ⟨huni, ?_, hrk, ?_, ?_, ?_, ?_⟩
  · exact huniT
  · intro i τ
    simp only [realOf]
    split_ifs with h
    · exact one_ne_zero
    · exact div_ne_zero h (hstd.2.2.2.1 τ)
  · intro i hi τ
    obtain ⟨Ch, _, A, hA, -⟩ := GlobalTheory.T.exists_tupleChain_adelicData I hOk hPins l Z u I.mu0
    obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_charExponent_infinity_kernel_shift I hOk hPins l Z u I.mu0 Ch A hA i hi
    exact Int.toNat_of_nonneg (he τ).2.2
  · intro v
    refine ⟨?_, fun k hk z z' hz => ?_⟩
    · show J v 1 ∈ ValC _ (sgT (D := I.rec7 l Z) u)
      rw [hJ1 v]
      have hm : j v ∈ ValC (gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z))) (sgT (D := I.rec7 l Z) u) := by
        rw [← hJ.range]; exact LinearMap.mem_range_self j v
      exact valC_transport hG _ _ hm
    · rw [hrT] at hz
      show J v k z' = J v 1 z
      rw [hJO v k hk z z' hz, hJO v 1 (Subgroup.one_mem _) z z (htr1 z)]
  · intro n hn
    subst hn
    have hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1 := by
      have := hrk (B.R.m - 1) (by omega)
      rw [show B.R.m - 1 + 1 = B.R.m by omega] at this
      omega
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common I hOk hPins l Z u hN
    refine ⟨hN, h1, h2, h3, ?_⟩
    intro k hk τ
    have hb := GlobalTheory.T.lastGroup_embedding_real_components_block_form I hOk hPins l Z u R.θ hX.inf _ hN hEmb k τ
    have hB := (hX.xs B.R.m le_rfl).2.1
    show GlobalTheory.BranchFormula.IsBlock hN (inN R.θ _ (g.x B.R.m).B (rankN (I.rec7 l Z) B.R.m le_rfl) ((g.oT B.R.m rfl).emb (k, 1)) τ) (inN R.θ _ (fun _ => 1) (rankP (I.rec7 l Z)) k τ) 1
    rw [hB]
    first
      | simpa only [inN_one] using hb
      | simpa [inN, GlobalTheory.SeeSaw.inB, infM] using hb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.Rows

open GlobalTheory.FinPl

section Gen

variable {D : D7}

theorem idAt_le {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → Q p) {z : AE D} (hz : z ∈ idAt D P) : z ∈ idAt D Q := by
  simp only [idAt, Submodule.mem_inf, idOff, Submodule.mem_iInf] at hz ⊢
  exact ⟨hz.1, fun w => hz.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem moves_mono {V : HSp D} {g : GA D V} {L : GlobalTheory.FinPl.Lat V} {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → Q p)
    (H : GlobalTheory.FinPl.Moves V g L L Q) : GlobalTheory.FinPl.Moves V g L L P := by
  intro y hy
  have hy' : ∀ i, y i ∈ idAt D Q := fun i => idAt_le h (hy i)
  rw [MovesSplit.mem_latV_iff_all V L P hy, MovesSplit.mem_latV_iff_all V L P (KOpen.supp_mulVec V P g hy),
    ← MovesSplit.mem_latV_iff_all V L Q hy', ← MovesSplit.mem_latV_iff_all V L Q (KOpen.supp_mulVec V Q g hy')]
  exact H y hy'

theorem st_iff (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : GlobalTheory.FinPl.Lat V) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ)
    (g : GA D V) : finE V g ∈ St β ↔ ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves V g Λ Λ (· = v) := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := D.host.E)
  rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
  exact forall_congr' fun v => (GlobalTheory.StMoves.moves_iff_stabLoc V Λ hfg v _).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1000000 in

theorem moves_of_stab (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    (Λ : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (t x : GA D V)
    {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (bas : GL Y k)
    (σ : Fin V.rank ≃ Y) (hM : MovedTo (ofSplit q) V t β ((F.β * bas.val).submatrix id σ))
    (m : GL Y k) (hm : (mt V x).map q.pr = F.β * m.val * F.γ) (hs : m ∈ stabLat bas) :
    GlobalTheory.FinPl.Moves V (t⁻¹ * x * t) Λ Λ (· = q.v) := by
  have h1 : (mt V t⁻¹).map q.pr * (mt V t).map q.pr = 1 := by
    rw [← Matrix.map_mul, ← LevRed.mt_mul', inv_mul_cancel, LevRed.mt_one', Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (mt V t).map q.pr * (mt V t⁻¹).map q.pr = 1 := by
    rw [← Matrix.map_mul, ← LevRed.mt_mul', mul_inv_cancel, LevRed.mt_one', Matrix.map_one _ (map_zero _) (map_one _)]
  let F' : GlobalTheory.LocMod.Frame k V.rank Y := ⟨(mt V t⁻¹).map q.pr * F.β, F.γ * (mt V t).map q.pr,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.β, F.βγ, Matrix.one_mul, h1],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((mt V t).map q.pr), h2, Matrix.one_mul, F.γβ]⟩
  have hM' : MovedTo (ofSplit q) V 1 β ((F'.β * bas.val).submatrix id σ) := by
    intro b hb
    have h3 : (mt V t).map q.pr * b.map q.pr = (F.β * bas.val).submatrix id σ := by
      rw [← Matrix.map_mul]; exact hM b hb
    have h4 : (F'.β * bas.val).submatrix id σ = (mt V t⁻¹).map q.pr * (F.β * bas.val).submatrix id σ := by
      show ((mt V t⁻¹).map q.pr * F.β * bas.val).submatrix id σ = _
      rw [Matrix.mul_assoc]
      rfl
    rw [h4, ← h3, ← Matrix.mul_assoc, h1, Matrix.one_mul, LevRed.mt_one', Matrix.one_mul]
    rfl
  have h0 : GlobalTheory.FinPl.Moves V 1 Λ Λ (· = q.v) := fun y _ => by rw [LevRed.mt_one', Matrix.one_mulVec]
  have hl := LevMoves.isLat_moved q hq V Λ Λ β hβ 1 h0 F' bas σ hM'
  obtain ⟨gl, g1, g2⟩ := GlobalTheory.GlEmbed.exists_gl D k q V _ F'.β F'.γ F'.βγ F'.γβ
  refine (GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes D k q V _ ⟨F'.β, F'.γ, F'.βγ, F'.γβ, gl, g1, g2⟩ Λ _ hΛ hl _).2 ?_
  have h5 : (mt V (t⁻¹ * x * t)).map q.pr = F'.β * m.val * F'.γ := by
    rw [LevRed.mt_mul', LevRed.mt_mul', Matrix.map_mul, Matrix.map_mul, hm]
    simp only [F', Matrix.mul_assoc]
  have h6 := (eq_coordHom_iff V q.pr F'.β F'.γ F'.βγ F'.γβ _ _).1 h5
  exact h6 ▸ LevMoves.smul_latOf hs

end Gen

section Loc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1000000 in

theorem red_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    (β : GL (Fin V.rank) (Lev.EAf D)) (t x : GA D V) {s : ℕ} (hs : s + 1 + 1 = D.R.m) (S : SymData k s D.R.k)
    (F : GlobalTheory.LocMod.Frame k V.rank (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (s + 1)))
    (e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) 0 ≃ Fin V.rank) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e)
    (hM : MovedTo (ofSplit q) V t β ((F.β * ((S.T (Fin D.R.t)).bas 0 (s + 1) (Nat.zero_add _)).val).submatrix id
      fun a => stdOrd (Fin D.R.k) (Fin D.R.t) 0 (s + 1) (Nat.zero_add _) (e.symm a)))
    (hr : D.R.r ≤ V.rank) (m : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (s + 1)) k)
    (hm : (mt V x).map q.pr = F.β * m.val * F.γ) (hst : finE V (t⁻¹ * x * t) ∈ St β) :
    (∃ z : S.P.J, ∀ (a b : Fin D.R.k ⊕ Fin (s + 1)) (a' b' : Fin D.R.r),
      a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ c : 𝓞 D.host.E,
        Ideal.Quotient.mk PP.asIdeal c = (upperLeftBlock hr (redFn β PP (finE V (t⁻¹ * x * t)))).val a' b' →
        valuation k ((z : GL (Fin D.R.k ⊕ Fin (s + 1)) k).val a b - (ofSplit q).pr (c : D.host.E)) < 1) ↔
      m ∈ ((S.T (Fin D.R.t)).lev 0 (s + 1) (Nat.zero_add _)).J := by
  obtain ⟨w, hw⟩ := hst
  rw [← hw, Formalism.L2.DIV.redFn_frGL]
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D _ q PP hq
  have h1 := RedLev.mul_moved (ofSplit q) hπ _ _ _ _ w hw hM
  have h3 := RedLev.conj_eq F ((S.T (Fin D.R.t)).bas 0 _ (Nat.zero_add _)) m
    (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 _ (Nat.zero_add _))) _
    ((congrArg (· * _) hm).symm.trans h1)
  have hk : D.R.k + (s + 1) = D.R.r := by
    unfold Ranks.r
    omega
  have hlt : ∀ i : Fin V.rank, i.val < D.R.r := fun i => by
    obtain ⟨i, rfl⟩ := e.surjective i
    rw [he, ← hk]
    rcases i with (i | i) | i
    · exact lt_of_lt_of_le i.2 (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left i.2 _
    · exact i.1.elim0
  have htri : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) w ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) :=
    Formalism.L2.DIV.mem_blockTri.2 fun i j h => by simp [Formalism.L2.DIV.blk2, hlt] at h
  have hpos : ∀ i, (e (.inl i)).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ i := fun i => by
    rw [he]
    rcases i with i | i <;> rfl
  let T := typeFrame S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (s + 1) (Nat.zero_add _))
  let g := (reGL (ixZero _ (Fin D.R.t))).symm (T.conj.symm m)
  have hg : ∀ i j, g.val i j = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (w.val (e (.inl i)) (e (.inl j))) :=
    fun i j => by
      have := congrFun (congrFun h3 (e (.inl i))) (e (.inl j))
      simp only [Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply, Matrix.map_apply] at this
      exact this
  have h6 : ∀ i j (c : 𝓞 D.host.E),
      Ideal.Quotient.mk PP.asIdeal c = Formalism.L2.DIV.resS D.host.F PP (w.val (e (.inl i)) (e (.inl j))) →
      valuation k (g.val i j - (ofSplit q).pr (c : D.host.E)) < 1 := fun i j c hc => by
    have h5 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E c) =
        (ofSplit q).pr (c : D.host.E) := hπ (incA D (c : D.host.E))
    rw [hg, ← h5, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, hc, sub_self]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨g', hg', e'⟩ := S.P.exists_of_congr z.2 (M := g.val) fun i j => by
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS D.host.F PP (w.val (e (.inl i)) (e (.inl j))))
      have h4 := hz i j ⟨_, hlt (e (.inl i))⟩ ⟨_, hlt (e (.inl j))⟩ (hpos i) (hpos j) c
        (by rw [Formalism.L2.DIV.upper_block_val_submatrix hr htri]; exact hc)
      have := Valuation.map_sub_lt _ (h6 i j c hc) h4
      rwa [sub_sub_sub_cancel_right] at this
    obtain rfl : g' = g := Units.ext e'
    exact hg'
  · intro hJ
    refine ⟨⟨g, hJ⟩, fun i j a' b' ha hb c hc => h6 i j c ?_⟩
    rw [Formalism.L2.DIV.upper_block_val_submatrix hr htri, Matrix.submatrix_apply] at hc
    have ea : Fin.castLE hr a' = e (.inl i) := Fin.ext (ha.trans (hpos i).symm)
    have eb : Fin.castLE hr b' = e (.inl j) := Fin.ext (hb.trans (hpos j).symm)
    rw [ea, eb] at hc
    exact hc

end Loc

section Real

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem mem_rJ_iff (W : RealPack ex) (y : GA D (Yc D 0)) (hy : y ∈ GfC (Yc D 0)) :
    (show GA D (D.sp.Y 0) from y) ∈ rJ W ↔ finE (Yc D 0) y ∈ St ((pk W).βY 0) ∧
      (fun PP : (pk W).Pg => upperLeftBlock (r_le_Y 0) (redFn ((pk W).βY 0) PP.1 (finE (Yc D 0) y))) ∈ (lvP W).H := by
  have hn : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Formalism.BasicNotions.Ranks.rankY]
  have key := (GlobalTheory.LevYZero.lev_datY_zero (Yc D 0) ((pk W).βY 0) _ D.R.r D.R.t (r_le_Y 0) hn (pk W).Pg (lvP W) (pk W).chi
    (fun _ => 1) rfl (finE (Yc D 0) y) (GlobalTheory.LevSplit.finE_mem_UA _ y)).1
  exact Iff.trans ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩ key

set_option maxHeartbeats 1000000 in

theorem main (W : RealPack ex) (hW : PkHyp W) (u : D.what₂.Word) (a : GeoAll W u) (ha : a.Is)
    (row : ∀ t, RowCh (pk W) (lvP W) u a.g t) (col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t)))
    (x : GA D (Yc D 0)) (hx : x ∈ GfC (Yc D 0)) :
    (show GA D (D.sp.Y 0) from (a.g.b 0)⁻¹ * x * a.g.b 0) ∈ rJ W ↔ InYLev a x := by
  obtain ⟨hV, hG⟩ := ha.tie row col
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hb : a.g.b 0 ∈ GfC (Yc D 0) := by
    have h1 := ha.vis.b 0
    rw [hV.b 0] at h1
    exact h1
  have hsd := hW.bot.hyp.2.2.2.1.lev.βY 0 hm
  have hΛ := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hsd
  obtain ⟨c, hβ, -⟩ := hsd
  have hoff := GlobalTheory.StMoves.moves_conj_iff x (hV.moves 0 hm (fun p => p ∉ a.v.gP) fun _ h => h)
  choose e he hM using fun i => hG.frame i 0 ((a.G i).s + 1) (Nat.zero_add _)
  have hex : ∀ i, ∃ m, (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m := fun i =>
    ⟨_, (eq_coordHom_iff _ (a.G i).q.pr _ _ ((a.G i).FY 0 _ (Nat.zero_add _)).βγ ((a.G i).FY 0 _ (Nat.zero_add _)).γβ x _).2 rfl⟩
  have hloc := fun i m (hmat : (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m) hst =>
    red_iff (a.G i).q (hG.idem i).1 (Yc D 0) ((pk W).βY 0) (a.g.b 0) x (a.G i).hs (a.G i).S _ (e i) (he i) (hM i) (r_le_Y 0) m hmat hst
  rw [mem_rJ_iff W _ (mul_mem (mul_mem (inv_mem hb) hx) hb), (hG.lev _).1]
  constructor
  · rintro ⟨hst, hred⟩
    refine ⟨hoff.1 (moves_mono (fun _ _ => trivial) ((movesLocal D _ _ hΛ _).2 ((st_iff _ _ _ hβ hΛ _).1 hst))), ?_⟩
    exact fun i m hmat => (hloc i m hmat hst).1 (hred i)
  · rintro ⟨h1, h2⟩
    have hst : finE (Yc D 0) ((a.g.b 0)⁻¹ * x * a.g.b 0) ∈ St ((pk W).βY 0) := by
      refine (st_iff _ _ _ hβ hΛ _).2 fun v => ?_
      by_cases hv : v ∈ a.v.gP
      · obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
        obtain ⟨m, hmat⟩ := hex i
        have hR : ((a.G i).S.T (Fin D.R.t)).Regular := GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _
        exact moves_of_stab (a.G i).q (hG.idem i).1 (Yc D 0) _ _ hβ hΛ (a.g.b 0) x _ _
          ((e i).symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 _ (Nat.zero_add _))) (hM i) m hmat
          ((hR.2.2 0 _ (Nat.zero_add _)).2.2 (h2 i m hmat))
      · exact moves_mono (fun p hp => by rw [hp]; exact hv) (hoff.2 h1)
    refine ⟨hst, fun i => ?_⟩
    obtain ⟨m, hmat⟩ := hex i
    exact (hloc i m hmat hst).2 (h2 i m hmat)

end Real

end GlobalTheory.FamTrace.Rows

theorem GlobalTheory.FamTrace.conj_mem_rows_iff : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ x ∈ GfC ((I.rec7 l Z).sp.Y 0), ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * x * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0) ∈ rJ W ↔ GlobalTheory.FamTrace.InYLev a x) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ x hx
  exact GlobalTheory.FamTrace.Rows.main W hA.pk u a ha row col x hx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

namespace GlobalTheory.TopVol.InKConj

variable {D : D7}

theorem idAt_le_of {P : Pl D → Prop} {v : Pl D} (hv : P v) : idAt D (· = v) ≤ idAt D P := by
  intro a ha
  rw [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun h => w.2 (h ▸ hv)⟩⟩

theorem moves_at {V : HSp D} {g : GA D V} {M : Lat V} {P : Pl D → Prop} (h : Moves V g M M P) {v : Pl D} (hv : P v) :
    Moves V g M M (· = v) := by
  intro y hy
  have hy' : ∀ i, y i ∈ idAt D P := fun i => idAt_le_of hv (hy i)
  rw [KOpen.mem_latV_iff V M _ y hy, KOpen.mem_latV_iff V M _ _ (KOpen.supp_mulVec V _ g hy),
    ← KOpen.mem_latV_iff V M P y hy', ← KOpen.mem_latV_iff V M P _ (KOpen.supp_mulVec V P g hy')]
  exact h y hy'

theorem conj_mem_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ M : Lat V) (Ld : LevDat D.host.E ℂ V.rank)
    (P : Pl D → Prop) (t κ : GA D V) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (ht : t ∈ GfC V)
    (hm : ∀ v, P v → Moves V t Λ M (· = v)) (hQ : Ld.Q = ∅)
    (hPg : ∀ PP ∈ Ld.Pg, ¬ P (PP.under (𝓞 D.host.F))) (hκ : InK V M P κ) :
    t⁻¹ * κ * t ∈ Lev.levG V β Ld := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := D.host.E)
  obtain ⟨hκf, hκ1⟩ := (KOpen.mem_grpAt_iff V P κ).1 hκ.1
  have hy : t⁻¹ * κ * t ∈ GfC V := (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem ht) hκf) ht
  have hproj : ∀ v, ¬ P v → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (t⁻¹ * κ * t) = 1 := fun v hv => by
    rw [map_mul, map_mul, hκ1 v hv, mul_one, map_inv, inv_mul_cancel]
  have hSt : Lev.finE V (t⁻¹ * κ * t) ∈ St β := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
    intro v
    by_cases hv : P v
    · rw [← GlobalTheory.StMoves.moves_iff_stabLoc V Λ hfg v]
      exact (GlobalTheory.StMoves.moves_conj_iff κ (hm v hv)).2 (moves_at hκ.2 hv)
    · rw [hproj v hv]; exact Subgroup.one_mem _
  have hred : ∀ PP ∈ Ld.Pg, redFn β PP (Lev.finE V (t⁻¹ * κ * t)) = 1 := fun PP hP =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt (hproj _ (hPg PP hP))
  refine ⟨hy, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hSt, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩⟩
  · rw [hred PP hP]; exact Subgroup.one_mem _
  · rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  · have e : rTup β Ld (Lev.finE V (t⁻¹ * κ * t)) = 1 := by
      funext PP
      show upperLeftBlock Ld.hr (redFn β PP.1 _) = 1
      rw [hred PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
    rw [e]; exact Subgroup.one_mem _

end GlobalTheory.TopVol.InKConj

namespace GlobalTheory.TopVol.InKConj

theorem inK_mem_levSph : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (J : QJ a t), J.Reads → ∀ κ, InK (I.rec7 l Z).sp.X' a.v.NT (fun p => ∃ i, (J.G i).q.v = p) κ → κ ∈ levSph W a.g.bT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat t J hJ κ hκ
  have hsd := W.Q.charW.base.lev.βX
  let row : ∀ t, RowCh (pk W) (lvP W) u a.g t := fun t =>
    { vP := fun _ _ => 0, vT := fun _ _ _ => 0
      sBF := fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepBF W.Q.stdChar _ _).some
      sFB := fun j σ h => (GlobalTheory.Unf.Inhab.nonempty_stepFB W.Q.stdChar _ _).some
      io := fun _ => 0, ioT := fun _ _ => 0 }
  let col := fun t : W.P.T => (GlobalTheory.Fam.Check.colCh_nonempty (D := I.rec7 l Z) (u := u) ((I.rec7 l Z).chTw u (W.P.I.tup t))).choose
  have tie := (ha.tie row col).1
  have hNT : a.v.NT = a.g.LT := tie.bT.2
  have hm : ∀ v, (fun p => ∃ i, (J.G i).q.v = p) v → Moves _ a.g.bT (pk W).ΛX a.v.NT (· = v) := fun v _ => by
    rw [hNT]; exact tie.movesT _
  rw [mem_levSph]
  exact conj_mem_levG _ (pk W).βX (pk W).ΛX a.v.NT (datSph W) _ a.g.bT κ (hsd.elim fun _ h => h.1)
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame _ _ _ _ _ hsd) ha.top.2.1 hm rfl
    (fun PP hP ⟨i, hi⟩ => GlobalTheory.Fam.qj_place_ne_lev W hW u a ha t J hJ i PP (Or.inr ((hW.lev.2.1 PP).1 hP)) hi) hκ

end GlobalTheory.TopVol.InKConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_scalar : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (pk W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (chrK W t)), ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2)), ∀ g, (ofSplit (a.Q PP ⟨t, hP⟩).q).IsLoc (a.Q PP ⟨t, hP⟩).FT g x → (a.g.bT⁻¹ * g * a.g.bT ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t) ↔ x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J) := by
  first | exact @GlobalTheory.TopLevQ.mem_levS_top_iff | exact GlobalTheory.TopLevQ.mem_levS_top_iff | (intros; apply GlobalTheory.TopLevQ.mem_levS_top_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_value : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (pk W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (chrK W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((pk W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  first | exact @GlobalTheory.QLevMid.level_at_place | exact GlobalTheory.QLevMid.level_at_place | (intros; apply GlobalTheory.QLevMid.level_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistChainLevelProduct_inverse_scalar_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ → t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧ t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  first | exact @GlobalTheory.QFinLaw.inverse_laws | exact GlobalTheory.QFinLaw.inverse_laws | (intros; apply GlobalTheory.QFinLaw.inverse_laws <;> assumption)
end

