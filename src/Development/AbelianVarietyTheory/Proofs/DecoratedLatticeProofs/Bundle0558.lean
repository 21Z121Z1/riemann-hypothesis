import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PolOfFnOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalMoveClassRepIffLocalConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceDoubleStepExactSignedConstant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0554
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0555
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodCharacterPrimitiveNormalFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCharacter_primitive_normalFrames : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.PrimAt ψ ((y.bes j ρ h).lev (a.x j).vol).d (N j) (PP.under (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.PrimNormal.prim_of_normal | exact GlobalTheory.PrimNormal.prim_of_normal | (intros; apply GlobalTheory.PrimNormal.prim_of_normal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainMoveCharactersEqRhoUpToBaseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainMove_characters_eq_rho_up_to_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}) x y, IsDetRoot _ (A.h i α c) x → IsDetRoot _ (A.h (i + 1) γ c') y → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) = (A.chr (i + 1) (A.xr i α) : ℂ) * (A.chr (i + 1) (A.xr (i + 1) γ) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * I.A.chiF (B.R.N i) (B.R.N (i + 1)) ((I.stp u a i).rep c.1).1.1.deco.1.N ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N := by
  first | exact @GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base | exact GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base | (intros; apply GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteStepSmallVectorFockVacuumSphericalStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteStep_smallVector_fockVacuum_spherical : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) ∧ IsSphOff ψ A H (frameLat A) (frameLat H) (under Z) f := by
  first | exact @GlobalTheory.Core.Rk.SmallVac.smallVec_vac_sph | exact GlobalTheory.Core.Rk.SmallVac.smallVec_vac_sph | (intros; apply GlobalTheory.Core.Rk.SmallVac.smallVec_vac_sph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantBesselSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepCell.LeftSecond

variable {D : D7}

theorem contAut_translate {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_of_mem_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  have hadd : ∀ {f g : GA D V → ℂ}, IsContAut V f → IsContAut V g → IsContAut V (f + g) := fun hf hg =>
    ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  have hsmul : ∀ {f : GA D V → ℂ}, IsContAut V f → ∀ c : ℂ, IsContAut V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact hsmul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact hadd hx hy
  | zero =>
    have h0 : IsContAut V (0 : GA D V → ℂ) := ⟨fun _ _ _ => rfl, continuous_const⟩
    simpa using h0
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact hadd (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact hsmul (h x) c

theorem theta_comb {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {P : Pl D → Prop}
    {e : WO S T →₀ ℂ} (he : CombAt P e) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T e f) :=
  (GlobalTheory.HeisComb.main D ψ S T).2.2.1 e f hf
    ((GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.1 e he).1 hψ

theorem integ_left_second : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (r * q₂) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f hf r hr q₁ q₂
  have hΦ₁ := theta_comb hc.std (hv.atG j).1 (theta_comb hc.std (hF.atQ j).1 h₁.1)
  have hΦ₂ := theta_comb hc.std (hv.atG (j + 1)).1 (theta_comb hc.std (hF.atQ (j + 1)).1 h₂.1)
  obtain ⟨J, χ, hle⟩ := ht.CC (j + 1 + 1) (by omega)
  have hfc : IsContAut (c.V (j + 1 + 1)) f := hf ▸ contAut_translate _ (contAut_of_mem_multT (hle G.2) x)
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => congrArg (w.ε j α g * ·) ?_
  exact (GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof D c.ψ σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sBF j (σ + 1) h)
    (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ hΦ₁ hΦ₂ (φ α) (hv.ram j _ (hφ α)).1 g q₁ q₂).2 f hfc r hr

end GlobalTheory.DStepCell.LeftSecond

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantFourierJacobiFir
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepCell.LeftOne

theorem vac_empty_comb {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {P : Pl D → Prop}
    {e : WO S T →₀ ℂ} (he : CombAt P e) {LS : Lat S} {LT : Lat T} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => False) f) : Vac ψ S T LS LT (fun _ => False) (comb ψ S T e f) :=
  ((GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.1 e he).2 LS LT f hf

theorem vac_empty {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT (fun _ => False) f := by
  have h := (GlobalTheory.DisjComb.main D ψ hψ S T (fun _ => True) (fun _ => False) (fun _ _ h => h)).2.2.2.2 LS LT f hS hT
  have e : (fun p : Pl D => True ∨ False) = fun _ => True := by funext p; simp
  rw [e] at h
  exact (h.1 hf).2

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (r * q₁) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv _ hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f _ r hr q₁ q₂
  have s0 := hv.sd j (by omega)
  have s1 := hv.sd (j + 1) (by omega)
  have s2 := hv.sd (j + 1 + 1) (by omega)
  have t₁ := (vac_empty_comb hc.std (hv.atG j).1 (vac_empty_comb hc.std (hF.atQ j).1 (vac_empty hc.std s0 s1 h₁))).1
  have t₂ := (vac_empty_comb hc.std (hv.atG (j + 1)).1
    (vac_empty_comb hc.std (hF.atQ (j + 1)).1 (vac_empty hc.std s1 s2 h₂))).1
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  have key := (GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ t₁ t₂ (φ α)
    (hv.ram j (φ α) (hφ α)).1 g q₁ q₂).1 r hr
  exact congrArg (fun z => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ z (rTrans q₂ f)) key

end GlobalTheory.DStepCell.LeftOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralAdaptedElementStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_adapted_element : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B → Framed B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ GlobalTheory.LevZero.StabAt f B a₀ a := by
  first | exact @GlobalTheory.LevZero.StabMatch.stab_match | exact GlobalTheory.LevZero.StabMatch.stab_match | (intros; apply GlobalTheory.LevZero.StabMatch.stab_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawBetweenBasePointsMovedPoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.MovedLaw

section Rat
open Formalism.L2.DIV Formalism.L2.Col
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def ratAt (F : Type) [Field F] [NumberField F] [Algebra F E] (n : ℕ) (P : HeightOneSpectrum (𝓞 E)) : Subgroup (GL (Fin n) (AfE F E)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap E (P.adicCompletion E))).range.comap
    (Matrix.GeneralLinearGroup.map (n := Fin n) (adAt F P))

theorem mem_ratAt_of {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} (M : Matrix (Fin n) (Fin n) E)
    (h : ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E _ (M r s)) : g ∈ ratAt F n P := by
  have e : (adAt F P).mapMatrix (g : Matrix (Fin n) (Fin n) (AfE F E)) = (algebraMap E (P.adicCompletion E)).mapMatrix M := by
    exact Matrix.ext h
  have hu : IsUnit ((adAt F P) (g : Matrix (Fin n) (Fin n) (AfE F E)).det) :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).map _
  rw [RingHom.map_det, e, ← RingHom.map_det] at hu
  have hM : M.det ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hu
    exact hu.ne_zero rfl
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hM, Units.ext e.symm⟩

theorem of_mem_ratAt {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} (h : g ∈ ratAt F n P) :
    ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s) := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, fun r s => (congrArg (fun z : GL (Fin n) (P.adicCompletion E) => z.1 r s) hγ).symm⟩

theorem ratAt_of_pt [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ Q) : g ∈ ratAt F n P :=
  mem_ratAt_of (Matrix.of fun i j => p.fr ⟨P, hP⟩ (Pi.single j 1) i) fun r s => h.fr ⟨P, hP⟩ r s

end Rat

section Step
open Formalism.L2.DIV Formalism.L2.Col
attribute [local instance] GlobalTheory.Mem.Col2.starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem fst_eq_one {u : B.Word} {a : I.ι} {j : ℕ} {b : (I.stp u a j).β} {g : (I.stp u a j).G b} (h : (I.stp u a j).gam b g = 1) :
    g.1 = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N j)).injective (h.trans (map_one _).symm))

theorem act_eq {u : B.Word} {a : I.ι} {j : ℕ} {b : (I.stp u a j).β} {g : (I.stp u a j).G b} (h : (I.stp u a j).gam b g = 1)
    (p : (I.stp u a j).D b) : ((I.stp u a j).act b g p).1.1 =
      ((1, g.2.1.1, g.2.2.1) : UF B.fields.E (B.R.N j) × GLG B.fields.E (B.R.N j) (B.primes X).vGs ×
        GLQ B.fields.E (B.R.N j) (I.Q a)) • p.1.1 := by
  show ((g.1, g.2.1.1, g.2.2.1) : UF B.fields.E (B.R.N j) × GLG B.fields.E (B.R.N j) (B.primes X).vGs ×
        GLQ B.fields.E (B.R.N j) (I.Q a)) • p.1.1 = _
  rw [fst_eq_one h]

theorem cosetIn_act_congr (hI : I.Ok) {u : B.Word} {a : I.ι} {j : ℕ} {b : (I.stp u a j).β} {g : (I.stp u a j).G b}
    (h : (I.stp u a j).gam b g = 1) {p p' : (I.stp u a j).D b} (e : cosetIn p = cosetIn p') :
    cosetIn ((I.stp u a j).act b g p) = cosetIn ((I.stp u a j).act b g p') := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  funext P
  have hex : ∃ t, AdT.LiftsInv I g P t := by
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · obtain ⟨t, ht⟩ := redGL_surjective (n := B.R.N j) P.1 (g.2.1.1 ⟨P.1, hP⟩)⁻¹
      refine ⟨t.1, t.2, fun _ x hx => ?_, fun hQ => absurd hQ (Finset.disjoint_left.1 hd hP)⟩
      rw [GlobalTheory.TopStep.redV_redGL t hx, ht]
    · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
      exact ⟨((g.2.2.1 ⟨P.1, hQ⟩)⁻¹).1, ((g.2.2.1 ⟨P.1, hQ⟩)⁻¹).2, fun h' => absurd h' hP, fun _ => rfl⟩
  obtain ⟨t, ht⟩ := hex
  ext z
  rw [AdT.cosetIn_act_of_liftsInv I hI u a j b g p P t h ht, AdT.cosetIn_act_of_liftsInv I hI u a j b g p' P t h ht, e]

end Step

section Main
open Formalism.L2.DIV Formalism.L2.Col
attribute [local instance] GlobalTheory.Mem.Col2.starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

set_option maxHeartbeats 1000000 in

theorem exists_move_of_reads (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (TC.GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → TC.GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → TC.GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : U (chOf c))
    (hx : x.1 ∈ UAd B.sp.cm (B.R.N i)) (hr : ∀ P ∈ I.Q a, x.1 ∈ ratAt B.host.F (B.R.N i) P) (p : (I.stp u a i).D c.1)
    (hp : TC.PtOf (k (chOf c)) p.1.1) (hc : cosetIn ((I.stp u a i).rep c) = cosetIn p) :
    ∃ g : (I.stp u a i).G c.1, (I.stp u a i).gam c.1 g = 1 ∧ TC.PtOf (x.1 * k (chOf c)) ((I.stp u a i).act c.1 g p).1.1 ∧
      cosetIn ((I.stp u a i).act c.1 g p) = cosetIn p ∧
      ((chi (chOf c) x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 g : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hy : TC.PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  have e : y c * x.1 * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x.1 * k (chOf c)) := by group
  have e' : x.1 * k (chOf c) = k (chOf c) * ((k (chOf c))⁻¹ * x.1 * k (chOf c)) := by group
  have hu : y c * x.1 * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    rw [e]
    exact mul_mem hy.uni (mul_mem (mul_mem (inv_mem hp.uni) hx) hp.uni)
  obtain ⟨q, hq⟩ := GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat B.sp.cm ((B.primes X).vT u) (B.primes X).vGs (I.Q a) _ hu fun P hP => by
    refine of_mem_ratAt ?_
    rw [e]
    exact mul_mem (ratAt_of_pt hy hP) (mul_mem (mul_mem (inv_mem (ratAt_of_pt hp hP)) (hr P hP)) (ratAt_of_pt hp hP))
  obtain ⟨g, h1, h2, h3⟩ := (hR.lev c x.1 q hq).1 x.2
  have hq' : TC.PtOf (y c * x.1 * k (chOf c)) ((I.stp u a i).act c.1 g ((I.stp u a i).rep c)).1.1 := h2 ▸ hq
  refine ⟨g, h1, ?_, ?_, hR.chr c x g h1 hq'⟩
  · rw [e, act_eq h1] at hq'
    obtain ⟨⟨k1, k2, k3, k4⟩, k5⟩ := GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm.conds_of_pts hy hq'
    rw [e', act_eq h1]
    exact GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm.pt_of_conds hp k1 k2 k3 k4 k5
  · rw [← cosetIn_act_congr hI h1 hc, h3, hc]

variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}

set_option maxHeartbeats 1000000 in

theorem exists_move (hI : I.Ok) (hA : A.Is) (j : ℕ) (hj : j ≤ B.R.m) (β : Ch j) (κ : A.U j β)
    (hr : ∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) j hj) κ.1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s))
    (κ₀ : TC.GA B (B.R.N j)) (h0 : finM _ (rankN (I.rec7 l Z) j hj) κ.1 = κ₀.1) :
    ∃ g : (I.stp u a j).G (A.b0 j β), (I.stp u a j).gam (A.b0 j β) g = 1 ∧
      TC.PtOf (κ₀ * A.kb j β) ((I.stp u a j).act (A.b0 j β) g (A.p0 j β)).1.1 ∧
      cosetIn ((I.stp u a j).act (A.b0 j β) g (A.p0 j β)) = cosetIn (A.p0 j β) ∧
      ((A.chi j β κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a j).chr (A.b0 j β) g : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  obtain ⟨c, rfl⟩ := hA.chOf_onto j hj β
  obtain ⟨x, hx⟩ := ((hA.U j hj _ κ.1).1 κ.2).2
  obtain rfl : κ₀ = x.1 := Units.ext (h0.symm.trans hx.symm)
  obtain ⟨hb, hc⟩ := hA.rep j hj c
  have hV : ((I.rec7 l Z).sp.X j).gram = 1 := hI.gram_X j
  have hJ : gramN (I.rec7 l Z) j hj = 1 := by
    unfold gramN
    rw [hV]
    simp
  have hu : x.1 ∈ UAd B.sp.cm (B.R.N j) := by
    have h := (((A.K j hj (A.chOf j c)).lev.U_eq x.1).1 x.2).1
    generalize x.1 = z at h ⊢
    rw [hJ] at h
    exact h
  rw [hA.chi j hj _ κ x hx, ← hb]
  exact exists_move_of_reads hI (hA.reads j hj) c x hu
    (fun P hP => by
      obtain ⟨M, hM⟩ := hr P hP
      exact mem_ratAt_of M (by rw [h0] at hM; exact hM))
    (A.p0 j (A.chOf j c)) ((hA.base j hj _).1.of_extTo (ColIn.Q_subset_SQ I a) hd) hc

set_option maxHeartbeats 1000000 in

theorem chr_root_eq (hI : I.Ok) (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X k))
    (hg : g ∈ GfC _) (y : TC.GA B (B.R.N k)) (hy : finM _ (rankN (I.rec7 l Z) k hk) g = y.1) (x : (AE (I.rec7 l Z))ˣ)
    (hx : IsDetRoot _ g x) (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u k) (hp : TC.PtOf y p) :
    (A.chr ((j : ℕ) + 1) x : ℂ)⁻¹ =
      B.embLL (muInvDet (X := B.fields) I.sel (rowSG (B.primes X) I.sel (I.tup a)) (mUof (R := B.R) I.Ch (I.tup a) j.1)
        (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) j.1) p.deco.1.N (frsF I.sel (I.tup a) p)) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hQ := ColIn.Q_subset_SQ I a
  have hd : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_of_subset_right hQ hlev.2.1
  obtain ⟨a', ha'⟩ := GlobalTheory.Mem.DetLift.exists_isDetLift B.R B.host (B.R.N k) _ hp.uni
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := GlobalTheory.DetRootRead.chr_at_detRoot (I.rec7 l Z) (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a) (hA.chr j)
    (Formalism.L2.Host.HChar.TrivOn.mul (I.C.isMu0 j).triv htw.2.1) _ _ _ _ hg hy _ hx a' ha'
  have hfac : KDq B.host (I.Q a) ≤ ((I.C.mu0 j * I.xi a).1.comp (Chr.finPartI B.host.E)).ker := fun b hb => by
    have e : (I.C.mu0 j).1 (Chr.finPartI B.host.E b) = 1 := reference_characters_factor_tame (I.Q a) I.C j hb
    have e' : (I.xi a).1 (Chr.finPartI B.host.E b) = 1 := (hlev.2.2 a).1 hb
    show (I.C.mu0 j).1 (Chr.finPartI B.host.E b) * (I.xi a).1 (Chr.finPartI B.host.E b) = 1
    rw [e, e', one_mul]
  have hp' : IsPtOf (host_cmData B.R B.host) y (extTo (I.Q a) p) := by
    rw [extTo_self hd]
    exact hp
  rw [GlobalTheory.LvT.Built.KMap.map_muInvDet_pt I hI a u j p, key, ← xiDet_eq I.SQ ((KDq_anti B.host hQ).trans hfac), xiDet,
    ← tildeQ_toDtQ hQ hfac, DetProj.toDtQ_detPt B.R B.host _ _ _ _ _ hQ p hlev.1,
    ← GlobalTheory.Mem.Col2.DetSpec.mk_eq_detPt B.R B.host _ _ _ _ _ _ _ a' (hlev.1.mono hQ) hp' ha', tildeQ_mk _ _ hfac]
  rfl

set_option maxHeartbeats 1000000 in

theorem chr_root_eq_prod (hI : I.Ok) (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m) (β : Ch k) (κ : A.U k β)
    (κ₀ : TC.GA B (B.R.N k)) (h0 : finM _ (rankN (I.rec7 l Z) k hk) κ.1 = κ₀.1) (x : (AE (I.rec7 l Z))ˣ) (hx : IsDetRoot _ κ.1 x)
    (g : (I.stp u a k).G (A.b0 k β)) (hg : (I.stp u a k).gam (A.b0 k β) g = 1)
    (hq : TC.PtOf (κ₀ * A.kb k β) ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1)
    (t : GLQ B.fields.E (B.R.N k) (rowSG (B.primes X) I.sel (I.tup a)))
    (ht : ∀ P, frsF I.sel (I.tup a) ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1 P =
      g.1.1 * (frsF I.sel (I.tup a) (A.p0 k β).1.1 P * (t P).1)) :
    (A.chr ((j : ℕ) + 1) x : ℂ)⁻¹ = B.embLL (∏ P : rowSG (B.primes X) I.sel (I.tup a),
      rhoS (R := B.R) I.Ch I.sel (I.tup a) j.1 P ((LinearEquiv.det (t P).1 : B.fields.Eˣ) : B.fields.E)) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  obtain ⟨hkA, hkAm, hxr⟩ := hA.kA k hk β
  have hκ := ((hA.U k hk β κ.1).1 κ.2).1
  have hfin : finM _ (rankN (I.rec7 l Z) k hk) (κ.1 * A.kA k β) = (κ₀ * A.kb k β).1 := by
    rw [GlobalTheory.RepLattice.finM_mul', h0, hkAm, Units.val_mul]
    rfl
  have e1 := chr_root_eq hI hA j k hk _ (mul_mem hκ hkA) _ hfin _ (GlobalTheory.TwistFinPart.isDetRoot_mul' _ _ _ _ _ hx hxr) _ hq
  have e2 := chr_root_eq hI hA j k hk _ hkA _ hkAm _ hxr _ ((hA.base k hk β).1.of_extTo (ColIn.Q_subset_SQ I a) hd)
  have hD := muDetLaw_chain (Pr := B.primes X) I.Ch I.sel (I.tup a) (I.cst a) j.1 (B.R.N k)
  rw [muAt_eq_muAtT I.Ch I.sel (I.tup a) (I.cst a) (muqTie_of_ok _ _ _ _ _ (hI.idx_ok a)) j.1 j.2] at hD
  have hN : ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1.deco.1.N = (A.p0 k β).1.1.deco.1.N := by
    rw [act_eq hg]
    exact Submodule.map_id _
  have hF : frsF I.sel (I.tup a) ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1 =
      fun P => frsF I.sel (I.tup a) (A.p0 k β).1.1 P * (t P).1 := funext fun P => by
    rw [ht P, fst_eq_one hg]
    exact one_mul _
  rw [hN, hF] at e1
  unfold muInvDet at e1 e2
  simp only [hD _ _ _, Finset.prod_mul_distrib] at e1
  rw [← mul_assoc, map_mul B.embLL, ← e2, map_mul, Circle.coe_mul, mul_inv, mul_comm] at e1
  exact mul_left_cancel₀ (inv_ne_zero (Circle.coe_ne_zero _)) e1

end Main

set_option maxHeartbeats 2000000 in

theorem moved_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (κ₀ : TC.GA B (B.R.N i)) (κ₀' : TC.GA B (B.R.N (i + 1))), finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 = κ₀.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 = κ₀'.1 → ∃ (q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)), TC.PtOf (κ₀ * A.kb i α) q.1.1 ∧ TC.PtOf (κ₀' * A.kb (i + 1) γ) q'.1.1 ∧ cosetIn q = cosetIn (A.p0 i α) ∧ cosetIn q' = cosetIn (A.p0 (i + 1) γ) ∧ ∀ w : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)), (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) q q' w) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ) w) := by
  intro B X I hI _ l Z u a Ch A hA i hi α γ κ κ' hr hr' x y hx hy κ₀ κ₀' h0 h0'
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨g, g1, g2, g3, g4⟩ := exists_move hI hA i hi0 α κ hr κ₀ h0
  obtain ⟨g', g1', g2', g3', g4'⟩ := exists_move hI hA (i + 1) hi γ κ' hr' κ₀' h0'
  refine ⟨_, _, g2, g2', g3, g3', fun w => ?_⟩
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨t, t', ht, ht', law⟩ := GlobalTheory.KerDia.Eqv.xiAt_law (Pr := B.primes X) hX hPr hI.sel_ok (hI.T_mem u) hI.g_mem (hI.idx_ok a)
    (hI.sharp a) hi (A.b0 i α) (A.b0 (i + 1) γ) g g' (A.p0 i α) (A.p0 (i + 1) γ)
  have e1 := chr_root_eq_prod hI hA ⟨i, hi⟩ i hi0 α κ κ₀ h0 x hx g g1 g2 t ht
  have e2 := chr_root_eq_prod hI hA ⟨i, hi⟩ (i + 1) hi γ κ' κ₀' h0' y hy g' g1' g2' t' ht'
  have key := congrArg B.embLL (law w)
  have hw : (g'.1.1.toLinearMap ∘ₗ w ∘ₗ g.1.1.symm.toLinearMap : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) = w := by
    rw [fst_eq_one g1, fst_eq_one g1']
    rfl
  simp only [unitInv_rho I.Ch I.sel (I.tup a) i _ _, Finset.prod_mul_distrib, Finset.prod_inv_distrib] at key
  rw [hw, map_mul, map_mul, map_inv₀, map_mul, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀] at key
  rw [g4, g4', e1, inv_eq_iff_eq_inv.1 e2]
  exact ((mul_comm _ _).trans key).trans (congrArg (· * _) (mul_comm _ _))

end GlobalTheory.AdForm.MovedLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceDoubleStepExactSignedConstantStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedPlace_doubleStep_exact_signed_constant : ∀ D : D7, GlobalTheory.FinPl.VertexExact D := by
  first | exact @GlobalTheory.FinPl.VertexExactCount.vertexExact | exact GlobalTheory.FinPl.VertexExactCount.vertexExact | (intros; apply GlobalTheory.FinPl.VertexExactCount.vertexExact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceDoubleStepVanishTargetCoreLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FinPl.vertexGlued_vanish_lastLat : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), IsStdChar D ψ (-1) → UnrAt s₁ p.v → UnrAt s₂ p.v → ∀ (M₀ : Lat B.V₀) (M₁ : Lat J.W₀) (M : Lat B'.V₀) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)) (P : Pair k n') (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k], IsSelfDualC B.V₀ M₀ → IsSelfDualC J.W₀ M₁ → IsSelfDualC B'.V₀ M → GluedCore B M₀ q α α₀ P → β.IsLat M₁ Q.lat → IsSumFrame B'.o B'.ζ γ γ₀ → (γ₀.IsLat M (lastKer Λ) ∨ γ₀.IsLat M (lastPair q Λ).lat) → ∀ Ξ₁ Ξ₂, Vac ψ B.V₀ J.W₀ M₀ M₁ (· = p.v) Ξ₁ → Vac ψ J.W₀ B'.V₀ M₁ M (· = p.v) Ξ₂ → ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = 0 := by
  intro D k _ _ _ _ p n n' n'' _ _ _ _ _ _ q ψ σ B J B' s₁ s₂ l vL hψ hs₁ hs₂ M₀ M₁ M α α₀ β γ γ₀ P Q Λ _ hM₀ hM₁ hM hG hβ hγ hγ₀ Ξ₁ Ξ₂ hΞ₁ hΞ₂ φ hφ
  obtain ⟨χ, hχ, -, -, hcond⟩ := (GlobalTheory.T.exists_splitPoint_frame_character D).2 k p |>.2 ψ hψ
  have hc := hcond hG.unit
  obtain ⟨ε, -, hV⟩ := GlobalTheory.T.doubleUnfoldingStep_at_glued_finite_place D k p q ψ χ hc hχ
  have hO := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D
  have h₁ := (hO k p n (n' ⊕ Fin 1) ψ hψ B.V₀ J.W₀ α₀ β M₀ M₁ hM₀ hM₁ Ξ₁ hΞ₁).2.2 hG.unit _ _ hG.lat hβ
  have hO₂ := hO k p (n'' ⊕ Fin 1) n ψ hψ J.W₀ B'.V₀ β γ₀ M₁ M hM₁ hM Ξ₂ hΞ₂
  refine (hV n n' n'' σ B J B' s₁ s₂ l vL hs₁ hs₂ α α₀ β γ γ₀ hG.sum hγ P P Q).2 Λ M₀ M₁ M₁ M Ξ₁ Ξ₁ Ξ₂ Ξ₂ h₁ ?_ φ hφ
  rcases hγ₀ with h | h
  · exact Or.inl (hO₂.2.2 hG.unit _ _ hβ h)
  · exact Or.inr (hO₂.2.2 hG.unit _ _ hβ h)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramifiedStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_diag_torus_integral_besselJacobi_unramified : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.InvStep.inv_int | exact GlobalTheory.FinPl.InvStep.inv_int | (intros; apply GlobalTheory.FinPl.InvStep.inv_int <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeesawDatumEqLatticePairOverVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeesaw_datum_eq_lattice_pair_over_vacuum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k] (Ψ : Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → ∀ u : WO A S, ∃ g, Over ψ β γ₀ LS LX g (phiOne (ε • Q) (lastPair q Λ)) (lastBi o o'' τ Ξ Φ₂ u) := by
  first | exact @GlobalTheory.LastTarget.lastTarget | exact GlobalTheory.LastTarget.lastTarget | (intros; apply GlobalTheory.LastTarget.lastTarget <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAtOneGluedPlaceStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPair_pairing_at_one_gluedPlace : ∀ D : D7, GlobalTheory.FinPl.SmallOne D := by
  first | exact @GlobalTheory.FinPl.smallOne | exact GlobalTheory.FinPl.smallOne | (intros; apply GlobalTheory.FinPl.smallOne <;> assumption)
end

