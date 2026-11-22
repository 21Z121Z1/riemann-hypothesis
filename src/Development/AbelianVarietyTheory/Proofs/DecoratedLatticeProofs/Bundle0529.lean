import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0491
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0520
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreQuotientLValues
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0516
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0459
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0512

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleColumnScalarAdelicFormContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RamCont

variable {D : D7}

theorem infM_mul' (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_mul θ V g h τ

theorem infM_fin' (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    infM θ V hn k τ = 1 := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

theorem continuous_infM' (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n) (τ : D.what₂.Tau) :
    Continuous fun g : GA D V => infM θ V hn g τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.continuous_infM θ hθ V τ

theorem pf_mul (V : HSp D) (g h : GA D V) :
    GlobalTheory.AdForm.RdLaw.pf V (g * h) = GlobalTheory.AdForm.RdLaw.pf V g * GlobalTheory.AdForm.RdLaw.pf V h := by
  apply Subtype.ext
  show GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V (g * h)) =
    GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V g) * GlobalTheory.AdForm.RdLaw.PGL D V.rank (matHom V h)
  rw [map_mul, map_mul]

theorem pf_inv (V : HSp D) (g : GA D V) : GlobalTheory.AdForm.RdLaw.pf V g⁻¹ = (GlobalTheory.AdForm.RdLaw.pf V g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pf_mul, inv_mul_cancel, GlobalTheory.AdForm.RdLaw.pf_one]

theorem pf_inv_mul_mem (V : HSp D) (g : GA D V) : (GlobalTheory.AdForm.RdLaw.pf V g)⁻¹ * g ∈ GinfC V := by
  rw [GlobalTheory.CentreTarget.mem_GinfC, ← pf_inv, GlobalTheory.CentreTarget.mt_mul, Matrix.map_mul, GlobalTheory.AdForm.RdLaw.mt_pf,
    GlobalTheory.AdForm.RdLaw.PM_map, GlobalTheory.AdForm.RdLaw.finPart_eps, RingHom.map_sub, RingHom.map_one,
    GlobalTheory.AdForm.RdLaw.finPart_eps, sub_self, zero_smul, add_zero, one_smul, ← Matrix.map_mul,
    ← GlobalTheory.CentreTarget.mt_mul, inv_mul_cancel]
  show (matHom V 1).1.map _ = 1
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem infM_mul_pf (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k d : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (k * ((GlobalTheory.AdForm.RdLaw.pf V d)⁻¹ * d)) τ = infM θ V hn k τ * infM θ V hn d τ := by
  rw [infM_mul' θ V hn k, infM_mul' θ V hn _ d, infM_fin' θ V hn _ (inv_mem (GlobalTheory.AdForm.RdLaw.pf_fin V d)), one_mul]

end GlobalTheory.AdForm.RamCont

namespace GlobalTheory.AdForm.RamCont

theorem rd_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b y, Continuous (A.rd θ j hj b φ y) := by
  classical
  intro B X I hI hPins l Z u a Ch A hA θ hθ j hj φ hφ b y
  obtain ⟨hreps, -, -⟩ := GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hI hPins l Z u a Ch A hA j hj b
  have hchi := GlobalTheory.T.continuous_chartLevelCharacters_adelic_tuple I hI hPins l Z u a Ch A hA j hj b
  obtain ⟨hval, hrd⟩ := GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hPins l Z u a Ch A hA θ hθ j hj φ hφ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X j).gram
  rw [continuous_iff_continuousAt]
  intro g0
  obtain ⟨γ, hγ, c, k, hk, κ, hκ, e0⟩ := hreps.dec g0
  obtain ⟨P, -, hP⟩ := hval c.1
  let V := (I.rec7 l Z).sp.X j
  let hn := rankN (I.rec7 l Z) j hj
  have hpc : Continuous fun g : GA (I.rec7 l Z) V => GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) :=
    (GlobalTheory.AdForm.RdLaw.continuous_pf V).comp (continuous_mul_left g0⁻¹)
  let p : GA (I.rec7 l Z) V → GfC V := fun g => ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), GlobalTheory.AdForm.RdLaw.pf_fin V _⟩
  have hp : Continuous p := hpc.subtype_mk _
  let O : Set (GA (I.rec7 l Z) V) := {g | GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b}
  have hO : IsOpen O := by
    have h1 := hreps.opn.preimage hp
    have e : O = p ⁻¹' (((A.U j b).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) := by
      ext g
      show GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b ↔ p g ∈ (A.U j b).subgroupOf (GfC V)
      rw [Subgroup.mem_subgroupOf]
    rw [e]; exact h1
  have hg0 : g0 ∈ O := by
    show GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g0) ∈ A.U j b
    rw [inv_mul_cancel, GlobalTheory.AdForm.RdLaw.pf_one]; exact one_mem _
  let G : GA (I.rec7 l Z) V → ℂ := fun g =>
    if h : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b then ((A.chi j b ⟨_, h⟩ : ℂˣ) : ℂ) else 0
  have hG : ContinuousAt G g0 := by
    have hc : ContinuousOn G O := by
      rw [continuousOn_iff_continuous_restrict]
      have e : (fun x : O => G x.1) = fun x : O => ((A.chi j b ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * x.1), x.2⟩ : ℂˣ) : ℂ) := by
        funext x
        exact dif_pos x.2
      show Continuous fun x : O => G x.1
      rw [e]
      exact hchi.comp ((hpc.comp continuous_subtype_val).subtype_mk _)
    exact hc.continuousAt (hO.mem_nhds hg0)
  let M : GA (I.rec7 l Z) V → (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ :=
    fun g τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ V hn k τ * infM θ V hn (g0⁻¹ * g) τ) * y.1 τ
  have hMu : ∀ g τ, IsUnit (M g τ).det := fun g τ => by
    simp only [M]
    erw [det_mul, det_mul]
    exact ((GlobalTheory.AdForm.RdVal.infM_unit θ V hn k τ).mul (GlobalTheory.AdForm.RdVal.infM_unit θ V hn _ τ)).mul (y.2 τ)
  have hM : ∀ τ, Continuous fun g =>
      (1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * M g τ := by
    intro τ
    have h1 : Continuous fun g : GA (I.rec7 l Z) V => infM θ V hn (g0⁻¹ * g) τ :=
      (continuous_infM' θ hθ V hn τ).comp (continuous_mul_left g0⁻¹)
    show Continuous fun g : GA (I.rec7 l Z) V => (1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * ((show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ V hn k τ * infM θ V hn (g0⁻¹ * g) τ) * y.1 τ)
    exact continuous_const.matrix_mul ((continuous_const.matrix_mul h1).matrix_mul continuous_const)
  let Φ : GA (I.rec7 l Z) V → ℂ := fun g =>
    (∏ τ, ((1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) τ * M g τ).det ^
      shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j) τ) *
    MvPolynomial.eval (fun q : (I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N j) × Fin ((I.rec7 l Z).R.N j) =>
      ((1 : (I.rec7 l Z).what₂.Tau → Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ) q.1 * M g q.1) q.2.1 q.2.2) P
  have hΦ : Continuous Φ := by
    refine Continuous.mul (continuous_finset_prod _ fun τ _ => ((hM τ).matrix_det).zpow₀ _ fun g => Or.inl ?_) ?_
    · rw [Pi.one_apply, one_mul]; exact (hMu g τ).ne_zero
    · exact (MvPolynomial.continuous_eval P).comp (continuous_pi fun q => (hM q.1).matrix_elem q.2.1 q.2.2)
  refine ContinuousAt.congr (f := fun g => ((A.chi j b ⟨κ, hκ⟩ : ℂˣ) : ℂ) * G g * Φ g)
    ((continuousAt_const.mul hG).mul hΦ.continuousAt) ?_
  filter_upwards [hO.mem_nhds hg0] with g hg
  have hU : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ A.U j b := hg
  have hδi : (GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g) ∈ GinfC V := pf_inv_mul_mem V _
  have hδf : GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ GfC V := GlobalTheory.AdForm.RdLaw.pf_fin V _
  have hκf : κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) ∈ GfC V := mul_mem (hreps.le hκ) hδf
  have eg : g = γ * (A.h j b c * (k * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)))) *
      (κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g)) := by
    have hc := Formalism.IndefR.Eqv.Act.comm_inf_fin hδi hκf
    calc g = g0 * (GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g) * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g))) := by group
      _ = γ * (A.h j b c * k) * ((κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g)) *
          ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g))) := by rw [e0]; group
      _ = γ * (A.h j b c * k) * (((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)) *
          (κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))) := by rw [hc]
      _ = _ := by group
  let y' : (I.chain l u a).Y j := ⟨M g, hMu g⟩
  have htr : IsTr (G := fun _ => 1) (infM θ V hn (k * ((GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g))⁻¹ * (g0⁻¹ * g)))) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [infM_mul_pf θ V hn k (g0⁻¹ * g) τ]
    rfl
  have key := hrd b y γ hγ c _ (mul_mem hk hδi) ⟨κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), mul_mem hκ hU⟩ y' htr
  rw [show A.rd θ j hj b φ y g = _ from (congrArg (A.rd θ j hj b φ y) eg).trans key]
  have e1 : (⟨κ * GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), mul_mem hκ hU⟩ : A.U j b) =
      ⟨κ, hκ⟩ * ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), hU⟩ := rfl
  have e2 : G g = ((A.chi j b ⟨GlobalTheory.AdForm.RdLaw.pf V (g0⁻¹ * g), hU⟩ : ℂˣ) : ℂ) := dif_pos hU
  have e3 : Φ g = φ c.1 y' := congrFun hP ⟨M g, hMu g⟩
  rw [e1, map_mul, Units.val_mul, e2, e3, mul_assoc]

end GlobalTheory.AdForm.RamCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistCombinationSplitsSinglePlaceVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPlaceSplit

variable {D : D7}

theorem coeff_mul_eq {G : Type} [AddMonoid G] (x y : AddMonoidAlgebra ℂ G) :
    (x * y).coeff = x.coeff.sum fun g a => y.coeff.sum fun h b => Finsupp.single (g + h) (a * b) := by
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single]

theorem aconv_eq_prod {G : Type} [AddCommMonoid G] (l : List (G →₀ ℂ)) :
    AddMonoidAlgebra.ofCoeff (aconv l) = (l.map AddMonoidAlgebra.ofCoeff).prod := by
  induction l with
  | nil =>
    apply AddMonoidAlgebra.ext
    rw [List.map_nil, List.prod_nil, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_ofCoeff]
    rfl
  | cons e l ih =>
    apply AddMonoidAlgebra.ext
    rw [List.map_cons, List.prod_cons, ← ih, coeff_mul_eq, AddMonoidAlgebra.coeff_ofCoeff,
      AddMonoidAlgebra.coeff_ofCoeff, AddMonoidAlgebra.coeff_ofCoeff]
    rfl

theorem support_prod_mem {G ι : Type} [AddCommMonoid G] (M : AddSubmonoid G) (s : Finset ι) (g : ι → G →₀ ℂ)
    (h : ∀ i ∈ s, ∀ y ∈ (g i).support, y ∈ M) :
    ∀ y ∈ (∏ i ∈ s, AddMonoidAlgebra.ofCoeff (g i)).coeff.support, y ∈ M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y hy
    rw [Finset.prod_empty, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single] at hy
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]
    exact M.zero_mem
  | insert a s ha ih =>
    intro y hy
    rw [Finset.prod_insert ha, coeff_mul_eq, AddMonoidAlgebra.coeff_ofCoeff] at hy
    obtain ⟨x, hx, hy2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
    obtain ⟨z, hz, hy3⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy2)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy3)]
    exact M.add_mem (h a (Finset.mem_insert_self a s) x hx)
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) z hz)

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO hO
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  unfold symplO hO
  simp

theorem comb_mul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AddMonoidAlgebra ℂ (WO S T))
    (h : ∀ x ∈ a.coeff.support, ∀ y ∈ b.coeff.support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (a * b).coeff f = comb ψ S T a.coeff (comb ψ S T b.coeff f) := by
  have hz : ∀ u, (0 : ℂ) • heisO ψ S T u f = 0 := fun u => zero_smul _ _
  have ha : ∀ u (r r' : ℂ), (r + r') • heisO ψ S T u f = r • heisO ψ S T u f + r' • heisO ψ S T u f :=
    fun u r r' => add_smul _ _ _
  rw [GlobalTheory.HeisComb.comb_comb, coeff_mul_eq, GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_sum_index (h := fun u (z : ℂ) => z • heisO ψ S T u f) hz ha]
  simp only [Finsupp.sum_sum_index (h := fun u (z : ℂ) => z • heisO ψ S T u f) hz ha, Finsupp.sum_single_index, zero_smul]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [GlobalTheory.WeilVacMove.heisO_heisO, symplOH, h x hx y hy, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem heisO_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (b : WO S T →₀ ℂ)
    (h : ∀ y ∈ b.support, symplO S T u y = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (comb ψ S T b f) = comb ψ S T b (heisO ψ S T u f) := by
  unfold comb
  rw [GlobalTheory.HeisComb.heisO_finset_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T u y = 0 := by unfold symplOH; rw [h y hy, mul_zero]
  rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, add_comm y u, h0, GlobalTheory.MixModel.symplOH_skew, h0, neg_zero]

theorem map_infPart_of_mxAt {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {y : Mx D m n} (hy : GlobalTheory.FinPl.MxAt P y) :
    y.map (infPart D) = 0 := by
  funext a b
  simp only [Matrix.map_apply, Matrix.zero_apply]
  exact (RingHom.mem_ker).1 (Submodule.mem_inf.1 (hy a b)).1

end GlobalTheory.TwistPlaceSplit

namespace GlobalTheory.TwistPlaceSplit

set_option maxHeartbeats 1000000 in

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ (i : Fin F.r) Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∃ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ ∧ comb c.ψ _ _ (w.eQ j) Ψ₁ = comb c.ψ _ _ ((F.Q i).eL j) f₁ := by
  intro D c v t w F hc hv hP j hj i Ψ₁ hΨ
  classical
  set v₀ := (F.Q i).q.v with hv₀def
  have hv₀ : v₀ ∈ w.Q := (hP.places v₀).2 ⟨i, rfl⟩

  have hat : ∀ i', ∀ u ∈ ((F.Q i').eL j).support, GlobalTheory.FinPl.MxAt (· = (F.Q i').q.v) u := by
    intro i' u hu
    have hs := (F.Q i').hs
    obtain ⟨d, hd⟩ : ∃ d, j + d = (F.Q i').s := ⟨(F.Q i').s - j, by omega⟩
    exact GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (F.Q i').q u (((F.Q i').eL_at j d hd).1 u hu)

  let M : AddSubmonoid (WO (c.V j) (c.V (j + 1))) :=
    { carrier := {y | (∀ x, GlobalTheory.FinPl.MxAt (· = v₀) x → symplO _ _ x y = 0) ∧ y.map (infPart D) = 0}
      add_mem' := fun {y y'} hy hy' => ⟨fun x hx => by rw [symplO_add_right, hy.1 x hx, hy'.1 x hx, add_zero], by
        rw [Matrix.map_add _ (map_add (infPart D)), hy.2, hy'.2, add_zero]⟩
      zero_mem' := ⟨fun x _ => symplO_zero_right _ _ x, by
        funext a b
        simp⟩ }
  have hM : ∀ i' ∈ Finset.univ.erase i, ∀ y ∈ ((F.Q i').eL j).support, y ∈ M := by
    intro i' hi' y hy
    have hne : v₀ ≠ (F.Q i').q.v := fun e => Finset.ne_of_mem_erase hi' (hP.inj e).symm
    exact ⟨fun x hx => GlobalTheory.FinPl.OverSwap.symplO_eq_zero_of_ne hne hx (hat i' y hy), map_infPart_of_mxAt (hat i' y hy)⟩
  set B := ∏ i' ∈ Finset.univ.erase i, AddMonoidAlgebra.ofCoeff ((F.Q i').eL j) with hB
  have hb : ∀ y ∈ B.coeff.support, y ∈ M := support_prod_mem M _ (fun i' => (F.Q i').eL j) hM
  have hprod : w.eQ j = (AddMonoidAlgebra.ofCoeff ((F.Q i).eL j) * B).coeff := by
    rw [hB, Finset.mul_prod_erase Finset.univ (fun i' => AddMonoidAlgebra.ofCoeff ((F.Q i').eL j)) (Finset.mem_univ i),
      ← Fin.prod_ofFn, hP.eQ j hj, ← AddMonoidAlgebra.coeff_ofCoeff (aconv _), aconv_eq_prod, List.map_ofFn]
    rfl

  have hmono : ∀ u ∈ latO (c.V j) (c.V (j + 1)) (v.N j : Set _) (v.N (j + 1) : Set _) (· = v₀),
      u ∈ latO (c.V j) (c.V (j + 1)) (v.N j : Set _) (v.N (j + 1) : Set _) (· ∈ w.Q) := by
    intro u hu
    refine AddSubgroup.closure_mono ?_ hu
    rintro x ⟨α, hα, hvα, rest⟩
    exact ⟨α, hα, fun v' hv' => hvα v' fun e => hv' (by rw [e]; exact hv₀), rest⟩
  refine ⟨comb c.ψ _ _ B.coeff Ψ₁, ⟨(GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 B.coeff Ψ₁ hΨ.1 (fun u hu => (hb u hu).2) hc.std,
    fun u hu => ?_, fun e he u hu hue => ?_⟩, ?_⟩
  · rw [heisO_comb _ _ _ _ _ (fun y hy => (hb y hy).1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt (AddSubgroup.nsmul_mem _ hu 2))),
      hΨ.2.1 u (hmono u hu)]
  · rw [heisO_comb _ _ _ _ _ (fun y hy => (hb y hy).1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu)), hΨ.2.2 e he u (hmono u hu) hue]
  · rw [hprod, comb_mul _ _ _ _ _ (fun x hx y hy => (hb y hy).1 x (hat i x (by rwa [AddMonoidAlgebra.coeff_ofCoeff] at hx))),
      AddMonoidAlgebra.coeff_ofCoeff]

end GlobalTheory.TwistPlaceSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreNormalizingFactorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistEulerFactors_restore_normalizingFactor : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ a : ℕ, GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) ≠ 0 ∧ GlobalTheory.LFun.dSfun D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) ((D.R.t : ℂ) / 2) = GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) * ((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.ChainTw.dSfun_twist_restore | exact GlobalTheory.ChainTw.dSfun_twist_restore | (intros; apply GlobalTheory.ChainTw.dSfun_twist_restore <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreQuotientLValuesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistEulerFactors_restore_quotientLValues : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, (∀ H H₀, IsHval c (c.S : Set _) k H → IsHval c w.S₀ k H₀ → H₀ = H * ∏ PP ∈ w.Q, blockL c k PP) ∧ ∃ H₀, H₀ ≠ 0 ∧ IsHval c w.S₀ k H₀ := by
  first | exact @GlobalTheory.ChainTw.EulerAtTwist.restore_hval | exact GlobalTheory.ChainTw.EulerAtTwist.restore_hval | (intros; apply GlobalTheory.ChainTw.EulerAtTwist.restore_hval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingOnlyBaseGramRationalPointsContribute
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Unf.cut_gram_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS vN x₀ Th hB hTh Ψ hΨ
  have lemR : ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := GlobalTheory.T.offBaseGram_termSum_invariant_rationalFlagUnipotent D ψ V V₀ W ρ d χV χW om om' hW hW' vS x₀ hB
  have lemQ : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := GlobalTheory.T.exists_centralValue_ne_one_of_gram_ne D ψ hW.std V V₀ W ρ d x₀
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨hH, hFD, h1⟩ := vN.unit

  have hBc : ∀ (c : skewA D ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∀ x,
      term ψ d W vS (om (d.nC c, 1) Φ) x = ψ (d.qS W c (rat x)) * term ψ d W vS Φ x := by
    intro c Φ hΦ x
    have h := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS Φ hΦ).1 x 0 1 c
    rw [d.nB_zero, Subgroup.coe_one, map_one, mul_one, mul_one] at h
    rw [h]
    simp only [Subgroup.coe_one, Units.val_one, Matrix.mul_one, Matrix.mul_zero]
    rfl
  have hsplit : ∀ g h : GA D V, om (g * h, 1) Ψ = om (g, 1) (om (h, 1) Ψ) := by
    intro g h
    rw [show ((g * h, (1 : GA D W)) : GA D V × GA D W) = (g, 1) * (h, 1) by simp, map_mul, Module.End.mul_apply]
  let F : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} → flagN d → ℂ :=
    fun i n => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) i.1
  let a : skewA D ρ → Matrix (Fin W.rank) (Fin ρ) D.host.E → ℂ :=
    fun c x => star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x))
  have hE : ∀ i c (n : flagN d), F i (⟨d.nC c, d.nC_mem_NFlag c⟩ * n) = a c i.1 * F i n := by
    intro i c n
    simp only [F, a, Subgroup.coe_mul]
    rw [hTh.cen c n.1 n.2, hsplit, hBc c _ (hW.om_pres _ _ hΨ)]
    ring

  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  have hT := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS
  obtain ⟨-, hM⟩ := GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D V V₀ ρ d
  obtain ⟨-, hcl, hnorm, K, hK, hKc⟩ := hM (centre d) (Or.inl rfl)
  have hdisc : DiscreteTopology (NFlagQ V d.e) :=
    DiscreteTopology.of_continuous_injective (f := fun γ : NFlagQ V d.e => (⟨γ.1.1, γ.2⟩ : GQ V))
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h)))
  have hcl' : IsClosed (((centre d).subgroupOf (flagN d) : Subgroup (flagN d)) : Set (flagN d)) := by
    rw [Subgroup.coe_subgroupOf]; exact hcl.preimage continuous_subtype_val
  have hcpt : ∃ K' : Set ((centre d).subgroupOf (flagN d)), IsCompact K' ∧
      ∀ m, ∃ γ ∈ (NFlagQ V d.e).subgroupOf ((centre d).subgroupOf (flagN d)), ∃ k ∈ K', m = γ * k := by
    let φ : centre d → (centre d).subgroupOf (flagN d) := fun c =>
      ⟨⟨c.1, (hM (centre d) (Or.inl rfl)).1 c.2⟩, Subgroup.mem_subgroupOf.2 c.2⟩
    have hφ : Continuous φ := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
    refine ⟨φ '' K, hK.image hφ, fun m => ?_⟩
    obtain ⟨γ, hγ, k, hk, e⟩ := hKc ⟨m.1.1, Subgroup.mem_subgroupOf.1 m.2⟩
    refine ⟨φ γ, ?_, φ k, ⟨k, hk, rfl⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hγ))
    · refine Subtype.ext (Subtype.ext ?_)
      change m.1.1 = γ.1 * k.1
      exact congrArg Subtype.val e
  have hmeas : ∀ i, Measurable (F i) := fun i =>
    (hTh.cont.mul ((hT Ψ hΨ).2.2.2.1 i.1 |>.comp (continuous_subtype_val.prodMk continuous_const))).measurable
  have hbd : ∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B := by
    obtain ⟨K, hK, hKc⟩ := (GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D V ρ d.e (isIsoSub_e d)).1
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hTh.cont.continuousOn
    obtain ⟨C, A, hCA⟩ := GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ
    refine ⟨M.toNNReal * (C * (height V 1 * quotHeight W 1) ^ A).toNNReal, fun n => ?_⟩
    have hTn : ‖Th n.1‖ₑ ≤ ENNReal.ofReal M := by
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hKc n
      rw [Subgroup.coe_mul, hTh.left γ.1 (Subgroup.mem_subgroupOf.1 hγ) γ.2 k.1 k.2, ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM k hk)
    have hS := hCA 1 1 n.1 n.2
    rw [mul_one] at hS
    calc ∑' i, ‖F i n‖ₑ = ‖Th n.1‖ₑ * ∑' i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀},
          ‖term ψ d W vS (om (n.1, 1) Ψ) i.1‖ₑ := by
          rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun i => enorm_mul _ _
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) :=
          mul_le_mul' hTn ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans hS)
      _ = _ := by rw [ENNReal.ofReal, ENNReal.ofReal, ← ENNReal.coe_mul]
  have hinv : ∀ γ ∈ NFlagQ V d.e, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n := by
    intro γ hγ n
    have hγ' := Subgroup.mem_subgroupOf.1 hγ
    simp only [F, Subgroup.coe_mul]
    rw [hTh.left γ.1 hγ' γ.2 n.1 n.2, hsplit, tsum_mul_left, tsum_mul_left,
      lemR γ.1 hγ' γ.2 _ (hW.om_pres _ _ hΨ)]
  have hcinv : ∀ c : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, ∀ γ ∈ NFlagQ V d.e, γ ∈ (centre d).subgroupOf (flagN d) → ∀ n,
      ∑' i : {i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} // id i = c}, F i.1 (γ * n) =
        ∑' i : {i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀} // id i = c}, F i.1 n := by
    intro c γ hγ hγM n
    refine tsum_congr fun i => ?_
    have hγ' := Subgroup.mem_subgroupOf.1 hγ
    obtain ⟨c', hc'⟩ := Subgroup.mem_subgroupOf.1 hγM
    simp only [F, Subgroup.coe_mul]
    rw [hTh.left γ.1 hγ' γ.2 n.1 n.2, hsplit]
    congr 1
    refine (hT _ (hW.om_pres _ _ hΨ)).2.1 γ.1 hγ' γ.2 i.1.1 i.1.1 ?_
    rw [blockX_of_fix d (mem_fixer.2 (hc' ▸ d.nC_jX c')), Matrix.mul_one]
  have heig : ∀ c : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, ∃ u ∈ (centre d).subgroupOf (flagN d), ∃ a : ℂ, a ≠ 1 ∧ ∀ i : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, id i = c →
      ∀ m ∈ (centre d).subgroupOf (flagN d), ∀ n, F i (m * u * n) = a * F i (m * n) := by
    intro c
    obtain ⟨c', hc'⟩ := lemQ c.1 c.2
    refine ⟨⟨d.nC c', d.nC_mem_NFlag c'⟩, Subgroup.mem_subgroupOf.2 ⟨c', rfl⟩, a c' c.1, hc', ?_⟩
    intro i hi m hm n
    subst hi
    obtain ⟨c'', hc''⟩ := Subgroup.mem_subgroupOf.1 hm
    have : m = ⟨d.nC c'', d.nC_mem_NFlag c''⟩ := Subtype.ext hc''.symm
    subst this
    rw [mul_assoc, hE, hE, hE]
    simp only [id]
    ring
  exact GlobalTheory.T.integral_tsum_normal_eigenfunctions_eq_zero (flagN d) vN.ν (NFlagQ V d.e) ((centre d).subgroupOf (flagN d)) j4 hdisc hnorm hcl' hcpt
    vN.𝓝 hFD (by rw [h1]; exact ENNReal.one_ne_top) _ _ id F hmeas hbd hinv hcinv heig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilShapeOfFrameMoves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem wShape_chain : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (ρ : ℕ) (h0 : 0 + 2 * ρ + 2 = D.R.m) (L : Lat (d.st 0).V), Formalism.L2.DIV.IsFrame (d.st 0).β (d.st 0).Λ → Moves (d.st 0).V (d.t 0) (d.st 0).Λ L (· = G.q.v) → WShape G.q (d.bes 0 ρ h0).d (d.bes 0 ρ h0).o (d.bes 0 ρ h0).ζ L (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹) (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (2 * ρ - i.1 + 1))⁻¹) ((((G.S.ϖ : G.kˣ) : G.k) ^ (ρ + 1))⁻¹) 1 (d.x 0).L := by
  intro D u d τ PP G ρ h0 L hβ hm
  exact GlobalTheory.T.frame_lattice_membership_criterion D u d τ PP G ρ h0 L (GlobalTheory.T.frame_vector_lattice_criterion D u d τ PP G (G.s + 1) (zero_add _) L hβ hm)

end GlobalTheory.Core.Mi.LatMatch
end

