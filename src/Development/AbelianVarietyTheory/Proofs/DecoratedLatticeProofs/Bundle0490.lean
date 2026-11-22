import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0475
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SharpMemRange
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0449
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0448
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0481
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharSymplecticFinitePartRestEqOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addChar_symplectic_finitePartRest_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplO S T ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r)) (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y'))) = 1 := by
  first | exact @GlobalTheory.FinRestComm.char_sympl_rest_eq_one | exact GlobalTheory.FinRestComm.char_sympl_rest_eq_one | (intros; apply GlobalTheory.FinRestComm.char_sympl_rest_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalTypeDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_local_type_data : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GlobalTheory.LevZero.PlacedBy f B v o G pl → GlobalTheory.LevZero.Bot (c := f.c) (GlobalTheory.BaseChain.com W) (GlobalTheory.LevZero.stZero W) (f.g.b 0) (fun PP => G (pl.symm PP)) := by
  first | exact @GlobalTheory.LevZero.bot_of_placedBy | exact GlobalTheory.LevZero.bot_of_placedBy | (intros; apply GlobalTheory.LevZero.bot_of_placedBy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiMapCarriesNormalFrameLines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColsXZeroNormal

theorem colsAt_xZero_of_normalFr : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.ColsAt ((y.bes j ρ h).lev (a.x j).vol).d (xZero ((y.jac j ρ h).lev (a.x (j + 1)).vol).d) (N j) (N (j + 1)) (PP.under (𝓞 D.host.F)) := by
  intro D ψ hψ a y βT PP l FY sc hN hx N M hNsd hNI hMsd hcore j ρ h
  rw [← l.under]
  intro i b hb
  rw [l.unit.2]
  have hs := l.hs
  have hdB : j + (2 * ρ + 1) = l.s + 1 := by omega
  have hdJ : j + 1 + 2 * ρ = l.s + 1 := by omega
  have hxi := GlobalTheory.ColsBFSplit.xi_unit l.q l.unit
  obtain ⟨hsc, -, hhz, hB, hJ, -⟩ := hN
  obtain ⟨m₀, m₁, h0, h1, hp⟩ := GlobalTheory.T.besselNormalFrame_isotropicColumns_pairing D l.k (ofSplit l.q) ρ ((y.bes j ρ h).lev (a.x j).vol)
    (XIx (Fin D.R.k) (Fin D.R.t) j) (2 * ρ + 1) (sc j) (l.FX j (by omega)) (FY j (2 * ρ + 1) hdB) (hB j ρ h (2 * ρ + 1) hdB) i
  obtain ⟨n₀, n₁, g0, g1, gp⟩ := GlobalTheory.T.fourierJacobiNormalFrame_isotropicColumns_pairing D l.k (ofSplit l.q) ρ ((y.jac j ρ h).lev (a.x (j + 1)).vol)
    (XIx (Fin D.R.k) (Fin D.R.t) (j + 1)) (2 * ρ) (sc j) ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol))
    (l.FX (j + 1) (by omega)) (FY (j + 1) (2 * ρ) hdJ) (hJ j ρ h (2 * ρ) hdJ) i
  have v0 : valuation l.k (sc j * (ofSplit l.q).xi ^ (ρ - i.val)) = 1 := by
    rw [map_mul, map_pow, hsc, hxi, one_pow, one_mul]
  have v1 : valuation l.k (sc j * (-(ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi) *
      (-1 / (ofSplit l.q).xi) ^ (ρ - 1 - i.val)) = 1 := by
    rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, Valuation.map_neg, map_one, hsc, hhz, hxi]
    simp
  have w1 : valuation l.k (sc j * ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi) *
      (-1 / (ofSplit l.q).xi) ^ (ρ - 1 - i.val)) = 1 := by
    rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, map_one, hsc, hhz, hxi]
    simp
  have eV := GlobalTheory.ColsBFSplit.line_crit l.q (FY j (2 * ρ + 1) hdB) (fun r => ((y.bes j ρ h).lev (a.x j).vol).d.e r i)
    (fun r => ((y.bes j ρ h).lev (a.x j).vol).d.e' r i) m₀ m₁ _ _ (hNsd j (by omega)) (hNI j _ hdB) v0 v1 h0 h1
    (GlobalTheory.T.wittHyperbolic_conj_pairing_eq_one D _ _ ρ ((y.bes j ρ h).lev (a.x j).vol).d i) hp b hb
  have eW := GlobalTheory.ColsBFSplit.line_crit l.q (FY (j + 1) (2 * ρ) hdJ) (fun r => ((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e r i)
    (fun r => ((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e' r i) n₀ n₁ _ _ (hNsd (j + 1) (by omega)) (hNI (j + 1) _ hdJ) v0 w1
    g0 g1 (GlobalTheory.T.wittHyperbolic_conj_pairing_eq_one D _ _ ρ ((y.jac j ρ h).lev (a.x (j + 1)).vol).d i) gp b hb
  exact eV.trans eW.symm

end GlobalTheory.ColsXZeroNormal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepKernelPreservesLevelRamifiedForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.KRamT

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia

section Entry
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

theorem tr_one {E K ι : Type} [Field E] [NumberField E] [Field K] [Fintype ι] {n : ℕ} (S : GStep E K n)
    (emb : ι → E →+* K) (σ : K →+* ℂ) (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  funext y
  simp only [GStep.tr, map_one, trFr_apply, inv_one, Units.val_one, map_one, one_mul]
  exact congrArg F (frMul_one emb σ y)

theorem ent_dia (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β}
    {b' : (I.stp u a (i + 1)).β} (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ) :
    ent I l u a i (((I.atIn u a).A i).dia b P s p) (((I.atIn u a).A (i + 1)).dia b' P s p') = ent I l u a i p p' := by
  unfold ent
  rw [(GlobalTheory.KerDia.RhoDia.rho_dia I l u a i b p b' p' P s).1, (GlobalTheory.KerDia.RhoDia.rho_dia I l u a i b p b' p' P s).2,
    GlobalTheory.DiaTheta.th_dia I l u a i b b' p p' P s]

theorem Kmap_stab (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (g : (I.stp u a (i + 1)).Stab c')
    (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ) (hf : f ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i)) :
    (I.stp u a (i + 1)).tr B.fields.emb B.embLL c'.1 g.1 ((I.chain l u a).Kmap i c c' f) = (I.chain l u a).Kmap i c c' f := by
  rw [GlobalTheory.KerDia.Kmap_eq]
  have e3 := GlobalTheory.T.kernelEntry_rationalEquivariance_transports I l hI u a i ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') 1 g.1 f
    (GlobalTheory.KerDia.sharp_mem_range I l u a i hi f hf)
  have hg : (I.stp u a (i + 1)).act c'.1 g.1 ((I.stp u a (i + 1)).rep c') = (I.stp u a (i + 1)).rep c' := g.2
  have h1 : (I.stp u a i).act c.1 1 ((I.stp u a i).rep c) = (I.stp u a i).rep c :=
    @one_smul _ _ _ (GStep.actD _ c.1) _
  rw [h1, hg, tr_one] at e3
  exact e3.symm

theorem K_mem_Fi (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) :
    ∀ φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i),
      (I.chain l u a).K i φ ∈ (I.stp u a (i + 1)).Fi B.fields.emb B.embLL (lamT (B.hcW u) (i + 1)) := by
  intro φ hφ c'
  let _ := (I.chain l u a).clsFin i
  have hK : (I.chain l u a).K i φ c' = ∑ c, (I.chain l u a).wt i c • (I.chain l u a).Kmap i c c' (φ c) := rfl
  rw [hK]
  refine ⟨Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _
    (GlobalTheory.AdForm.Keep.kmap_val I l u a i hi c c' _ (hφ c).1), fun g => ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Kmap_stab I l hI u a i hi c c' g _ (hφ c).1]

end Entry
end GlobalTheory.KRamT

namespace GlobalTheory.KRamT

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia

section Dia
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

theorem entry_dia (I : TC B X) (l : I.Laws) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (φ : ColT I l u a i) (hφ : φ ∈ (I.fm l u a).Fi i) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ)
    (L : (I.chain l u a).cls i) (c' : (I.chain l u a).cls (i + 1)) :
    (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).Kmap i ((I.fm l u a).dil i v s L) ((I.fm l u a).dil (i + 1) v s c')
      (φ ((I.fm l u a).dil i v s L))) =
    (I.chain l u a).Kmap i L c' ((I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) := by
  have hφ' : φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i) := hφ
  change (I.atIn u a).dilT B.fields.emb B.embLL (i + 1) v s c'
      ((I.chain l u a).Kmap i ((I.atIn u a).dil i v s L) ((I.atIn u a).dil (i + 1) v s c')
        (φ ((I.atIn u a).dil i v s L))) =
    (I.chain l u a).Kmap i L c' ((I.atIn u a).dilT B.fields.emb B.embLL i v s L (φ ((I.atIn u a).dil i v s L)))
  have hx : φ ((I.atIn u a).dil i v s L) ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) :=
    (hφ' ((I.atIn u a).dil i v s L)).1
  rw [Kmap_eq I l u a i _ _, Kmap_eq I l u a i L c']
  unfold AtIn.dilT AtIn.dil GStep.trTo
  have e1 := (I.stp u a i).mv_smul L.1 (((I.atIn u a).A i).diaPt v s L)
  have e2 := (I.stp u a (i + 1)).mv_smul c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')
  have e3 := GlobalTheory.T.kernelEntry_rationalEquivariance_transports I l hI u a i
    ((I.stp u a i).rep ((I.stp u a i).cl L.1 (((I.atIn u a).A i).diaPt v s L)))
    ((I.stp u a (i + 1)).rep ((I.stp u a (i + 1)).cl c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')))
    ((I.stp u a i).mv L.1 (((I.atIn u a).A i).diaPt v s L))
    ((I.stp u a (i + 1)).mv c'.1 (((I.atIn u a).A (i + 1)).diaPt v s c')) _
    (GlobalTheory.KerDia.sharp_mem_range I l u a i hi _ hx)
  unfold GStep.act at e3
  rw [e1, e2] at e3
  refine Eq.trans e3.symm ?_
  exact LinearMap.congr_fun (ent_dia I l u a i ((I.stp u a i).rep L) ((I.stp u a (i + 1)).rep c') v s) _

def dilEquiv (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ) :
    (I.chain l u a).cls i ≃ (I.chain l u a).cls i where
  toFun := (I.fm l u a).dil i v s
  invFun := (I.fm l u a).dil i v s⁻¹
  left_inv c := by rw [← (I.fm l u a).dil_mul, inv_mul_cancel, (I.fm l u a).dil_one]
  right_inv c := by rw [← (I.fm l u a).dil_mul, mul_inv_cancel, (I.fm l u a).dil_one]

theorem dia_K_eq (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ)
    (φ : ColT I l u a i) (c' : (I.chain l u a).cls (i + 1)) :
    (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).K i φ ((I.fm l u a).dil (i + 1) v s c')) =
      ∑ L ∈ @Finset.univ _ ((I.chain l u a).clsFin i), (I.chain l u a).wt i L • (I.fm l u a).dilT (i + 1) v s c'
        ((I.chain l u a).Kmap i ((I.fm l u a).dil i v s L) ((I.fm l u a).dil (i + 1) v s c') (φ ((I.fm l u a).dil i v s L))) := by
  letI := (I.chain l u a).clsFin i
  simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, map_sum, map_smul]
  refine (Equiv.sum_comp (dilEquiv I l u a i v s) _).symm.trans (Finset.sum_congr rfl fun L _ => ?_)
  have h : (I.chain l u a).wt i ((I.fm l u a).dil i v s L) = (I.chain l u a).wt i L := by
    unfold ColumnChain.wt
    rw [(I.fm l u a).dil_stab]
  show (I.chain l u a).wt i ((I.fm l u a).dil i v s L) • _ = _
  rw [h]
  rfl

end Dia

theorem kernel_keeps_ramT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ φ : ColT I l u a i, RamT i φ → RamT (i + 1) ((I.chain l u a).K i φ) := by
  intro B X I hI _ l _ u a i hi φ hR
  letI := (I.chain l u a).clsFin i
  refine ⟨K_mem_Fi I l hI u a i hi φ hR.1, fun v c' => ?_⟩
  letI := (I.atT l u a).FvFin v
  letI := (I.atT l u a).FvDec v
  have hsum : ∑ s : ((I.atT l u a).Fv v)ˣ,
      (fun L => (I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) = 0 := by
    funext L
    rw [Finset.sum_apply, ← finsum_eq_sum_of_fintype]
    exact hR.2 v L
  have hterm : ∀ s : ((I.atT l u a).Fv v)ˣ,
      (I.fm l u a).dilT (i + 1) v s c' ((I.chain l u a).K i φ ((I.fm l u a).dil (i + 1) v s c')) =
        (I.chain l u a).Klin i (fun L => (I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L))) c' := by
    intro s
    refine (dia_K_eq I l u a i v s φ c').trans ?_
    show _ = ∑ L, (I.chain l u a).wt i L • (I.chain l u a).Kmap i L c'
      ((I.fm l u a).dilT i v s L (φ ((I.fm l u a).dil i v s L)))
    exact Finset.sum_congr rfl fun L _ => congrArg ((I.chain l u a).wt i L • ·)
      (entry_dia I l hI u a i hi φ hR.1 v s L c')
  rw [finsum_eq_sum_of_fintype]
  simp only [hterm]
  rw [← Finset.sum_apply, ← map_sum, hsum, map_zero]
  rfl

end GlobalTheory.KRamT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesSplitUnramifiedQuotients
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.TwPlaces

variable {D : D7}

theorem absNorm_under_of_ne {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F))
    (hne : w ≠ w') : Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal = Ideal.absNorm w.asIdeal := by
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hne rfl h.symm
  rw [← GlobalTheory.LFun.SplitChart.absNorm_splitPrime τ, hτ]

theorem conjPrime_ne_of_mem {P : Finset (Pl D.host.E)} {e : AE D} (h : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    GlobalTheory.IdemSupport.cP PP ≠ PP := by
  classical
  have hinj := GlobalTheory.LevelPlaces.under_injOn h
  obtain ⟨⟨es, hes, rfl⟩, h0⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  intro hc
  have hd : ∀ Q ∈ P, GlobalTheory.IdemSupport.IsDelta Φ Q (es Q) := fun Q hQ =>
    GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hes Q hQ)
  have e1 : Φ (∑ Q ∈ P, es Q) PP = 1 := by
    rw [GlobalTheory.LevelPlaces.ev_sum, Finset.sum_eq_single PP (fun Q hQ hQP => (hd Q hQ).2.2 PP (Ne.symm hQP))
      (fun h => absurd hPP h), (hd PP hPP).2.1]
  have e2 : Φ (cA D (∑ Q ∈ P, es Q)) PP = 1 := by
    rw [map_sum, GlobalTheory.LevelPlaces.ev_sum, Finset.sum_eq_single PP ?_ (fun h => absurd hPP h)]
    · have := (GlobalTheory.IdemSupport.delta_conj hΦ (hd PP hPP)).2.1
      rwa [hc] at this
    · intro Q hQ hQP
      refine (GlobalTheory.IdemSupport.delta_conj hΦ (hd Q hQ)).2.2 PP fun hQc => hQP ?_
      have hv : Q.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) := by rw [← GlobalTheory.IdemSupport.under_cP Q, ← hQc]
      exact hinj (Finset.mem_coe.2 hQ) (Finset.mem_coe.2 hPP) hv
  have e3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) (∑ Q ∈ P, es Q) (cA D (∑ Q ∈ P, es Q)) PP
  rw [h0, GlobalTheory.IdemSupport.ev_zero, e1, e2, one_mul] at e3
  exact zero_ne_one e3

theorem exists_fin_of_mem {m i : ℕ} (hi : i ∈ Finset.Icc 1 m) : ∃ k : Fin m, (k : ℕ) + 1 = i := by
  rw [Finset.mem_Icc] at hi
  exact ⟨⟨i - 1, by omega⟩, by simp; omega⟩

end GlobalTheory.ChainTw.TwPlaces

open GlobalTheory.ChainTw.TwPlaces in

theorem GlobalTheory.ChainTw.twist_places : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → (∀ v, v ∈ c.S ↔ v ∈ w.S₀ ∨ ∃ PP ∈ w.Q, PP.under (𝓞 D.host.F) = v) ∧ (∀ PP ∈ w.Q, PP.under (𝓞 D.host.F) ∉ w.S₀) ∧ Set.InjOn (fun PP : Pl D.host.E => PP.under (𝓞 D.host.F)) w.Q ∧ (∀ PP ∈ w.Q, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (PP.under (𝓞 D.host.F)) ∧ Ideal.absNorm (PP.under (𝓞 D.host.F)).asIdeal = Ideal.absNorm PP.asIdeal ∧ ∃ PP' : Pl D.host.E, PP' ≠ PP ∧ (∀ P : Pl D.host.E, P.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) ↔ P = PP ∨ P = PP') ∧ Ideal.absNorm PP'.asIdeal = Ideal.absNorm PP.asIdeal ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP' = (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP)⁻¹) ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.UnrOff (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w.S₀ := by
  intro D c w hw
  classical
  obtain ⟨e, he⟩ := hw.com.split
  have hinj : Set.InjOn (fun PP : Pl D.host.E => PP.under (𝓞 D.host.F)) (c.Pg : Set (Pl D.host.E)) :=
    GlobalTheory.LevelPlaces.under_injOn he
  have hQ : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_right _ h
  have hPg : ∀ PP ∈ w.Pg, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_left _ h
  have hS : ∀ v, v ∈ c.S ↔ v ∈ w.S₀ ∨ ∃ PP ∈ w.Q, PP.under (𝓞 D.host.F) = v := by
    intro v
    simp only [Com.S, Twist.S₀, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_image, hw.union,
      Finset.mem_union]
    constructor
    · rintro ⟨PP, h | h, rfl⟩
      · exact Or.inl ⟨PP, h, rfl⟩
      · exact Or.inr ⟨PP, h, rfl⟩
    · rintro (⟨PP, h, rfl⟩ | ⟨PP, h, rfl⟩)
      · exact ⟨PP, Or.inl h, rfl⟩
      · exact ⟨PP, Or.inr h, rfl⟩
  have hnot : ∀ PP ∈ w.Q, PP.under (𝓞 D.host.F) ∉ w.S₀ := by
    intro PP hPP h
    simp only [Twist.S₀, Finset.coe_image, Set.mem_image, Finset.mem_coe] at h
    obtain ⟨PP₀, h0, he0⟩ := h
    have := hinj (Finset.mem_coe.2 (hPg PP₀ h0)) (Finset.mem_coe.2 (hQ PP hPP)) he0
    subst this
    exact Finset.disjoint_left.1 hw.disj h0 hPP
  have hsplit : ∀ PP ∈ c.Pg, Formalism.DivisionValues.conjPl PP ≠ PP := fun PP h => by
    rw [GlobalTheory.LevelPlaces.conjPl_eq_cP]; exact conjPrime_ne_of_mem he h
  have hres : ∀ PP ∈ w.Q, ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m,
      GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
    intro PP hPP i hi j hj
    obtain ⟨a, rfl⟩ := exists_fin_of_mem hi
    obtain ⟨b, rfl⟩ := exists_fin_of_mem hj
    obtain ⟨Ha, hca, hra⟩ := hw.com.res a
    obtain ⟨Hb, hcb, hrb⟩ := hw.com.res b
    have ra := hra PP (hQ PP hPP)
    have rb := hrb PP (hQ PP hPP)
    rw [hw.chiQ _ PP hPP, inv_inv] at ra rb
    exact GlobalTheory.T.heckeCharUnramifiedAt_quotient_same_residual D _ _ Ha Hb PP _ hca hcb ra rb
  have hre : ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, ResEta D (c.μ i * (c.μ j)⁻¹) 0 := by
    intro i hi j hj
    obtain ⟨-, ⟨η, hη⟩, hi'⟩ := hw.com.chars.2.2.2.2 i hi
    obtain ⟨-, -, hj'⟩ := hw.com.chars.2.2.2.2 j hj
    refine ⟨⟨η, hη⟩, fun η' hη' a => ?_⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hi' η' hη' a, hj' η' hη' a]
    simp
  refine ⟨hS, hnot, hinj.mono fun x hx => Finset.mem_coe.2 (hQ x (Finset.mem_coe.1 hx)), fun PP hPP => ?_, ?_⟩
  · have hne : Formalism.DivisionValues.conjPl PP ≠ PP := hsplit PP (hQ PP hPP)
    have hu : (Formalism.DivisionValues.conjPl PP).under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) := ParInv.under_conjPl PP
    refine ⟨GlobalTheory.LFun.ConjPlace.isSplit_of_ne hne.symm rfl hu, absNorm_under_of_ne hu.symm hne.symm,
      Formalism.DivisionValues.conjPl PP, hne, fun P => ⟨fun h => ?_, ?_⟩, ParInv.absNorm_conjPl' PP, fun i hi j hj => ?_⟩
    · rcases GlobalTheory.GridPlaces.eq_or_eq_conjP h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (h1.trans (ParInv.conjP_eq_conjPl' PP))
    · rintro (rfl | rfl)
      · rfl
      · exact hu
    · exact (GlobalTheory.T.unramified_conjugate_place_inverse_uniformizer_value D _ (hre i hi j hj) PP _ hu.symm hne.symm (hres PP hPP i hi j hj)).2
  · intro i hi j hj W hW
    by_cases hWS : W.under (𝓞 D.host.F) ∈ c.S
    · rcases (hS _).1 hWS with h | ⟨PP, hPP, hPPW⟩
      · exact absurd h hW
      · rcases GlobalTheory.GridPlaces.eq_or_eq_conjP hPPW.symm with h1 | h1
        · rw [h1]; exact hres PP hPP i hi j hj
        · have hne := hsplit PP (hQ PP hPP)
          rw [h1, ParInv.conjP_eq_conjPl']
          exact (GlobalTheory.T.unramified_conjugate_place_inverse_uniformizer_value D _ (hre i hi j hj) PP _ (ParInv.under_conjPl PP).symm hne.symm
            (hres PP hPP i hi j hj)).1
    · obtain ⟨a, rfl⟩ := exists_fin_of_mem hi
      obtain ⟨b, rfl⟩ := exists_fin_of_mem hj
      have hW' : W ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hWS
      exact (hw.com.unr a W hW').mul (hw.com.unr b W hW').inv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePointsLevelDatumEqLocalProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

open Classical in

theorem phiT_base_eq_prod : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) (α : Ch j) (γ : Ch (j + 1))
      (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E),
      B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z)) =
        (J.map fun i => phiOne (Q j i) (Q (j + 1) i) (rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z))))).prod := by
  intro B X I _ _ l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ j hj α γ z
  have hj0 : j ≤ B.R.m := Nat.le_of_succ_le hj
  obtain ⟨⟨e, he⟩, hS2⟩ := hS
  obtain ⟨hLj, hSj⟩ := hS2 j hj0
  obtain ⟨hLj', hSj'⟩ := hS2 (j + 1) hj
  have hG := GlobalTheory.T.phi_one_eq_one_iff_column_condition B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 (B.fields.conjO (X.piT u))
    (A.p0 j α).1.1.deco.2 (A.p0 (j + 1) γ).1.1.deco.2 (hA.base j hj0 α).2 (hA.base (j + 1) hj γ).2
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA j hj0 α P x hx r hr c hc)
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA (j + 1) hj γ P x hx r hr c hc)
    (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)
  have hLoc : ∀ i, (Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) ↔
      ColCond (e i).1 (B.fields.conjO (X.piT u)) (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) :=
    fun i => GlobalTheory.T.maps_rd_iff_colCond_toHom (p i) (e i).1 (he i) _ _ (β j i) (β (j + 1) i) (Q j i) (Q (j + 1) i) (L j) (L (j + 1)) _ hLj hLj'
      (hSj i).1 (hSj' i).1 (hSj i).2 (hSj' i).2 z
  have key : (∀ P : (B.primes X).vT u, ColCond P.1 (B.fields.conjO (X.piT u))
      (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) ↔
      ∀ i ∈ J, Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) := by
    refine ⟨fun h i _ => (hLoc i).2 (h (e i)), fun h P => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective P
    exact (hLoc i).1 (h i (hJ.all i))
  have hprod : ∀ (J' : List ι) (c : ι → Prop), (J'.map fun i => (if c i then (1 : ℂ) else 0)).prod =
      if ∀ i ∈ J', c i then 1 else 0 := by
    intro J' c
    induction J' with
    | nil => simp
    | cons i J' ih =>
      rw [List.map_cons, List.prod_cons, ih]
      by_cases h : c i <;> simp [h]
  have hv : ∀ x, Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 1 ∨
      Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 0 := by
    intro x
    unfold Formalism.L2.Col.phiT
    split_ifs <;> simp
  simp only [phiOne]
  rw [hprod]
  split_ifs with hc
  · rw [hG.2 (key.2 hc), map_one]
  · rcases hv (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z) with h1 | h0
    · exact absurd (key.1 (hG.1 h1)) hc
    · rw [h0, map_zero]

end GlobalTheory.PhiOneVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelCharacterRepsOnAdelicUnitaryPointsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevelCharacterReps_on_adelicUnitaryPoints : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i ≤ B.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} (K : LevelChart (I.rec7 l Z) T bad i hi stab lat), ∃ (U : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))) (chi : U →* ℂˣ) (h : cl → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)), (∀ g, g ∈ U ↔ g ∈ GfC _ ∧ ∃ κ : K.lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g) ∧ (∀ (g : U) (κ : K.lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 → chi g = K.lev.chi κ) ∧ (∀ c, h c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (h c) = (K.y c).1.1) := by
  first | exact @GlobalTheory.ChartLevRead.levData | exact GlobalTheory.ChartLevRead.levData | (intros; apply GlobalTheory.ChartLevRead.levData <;> assumption)
end

