import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0103
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEdge
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.DiffDual

variable {D : D7}

def TrInt (D : D7) (x : D.host.E) : Prop := ∀ o : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (x * o) = n

theorem mem_dI_iff (x : D.host.E) : x ∈ dI D ↔ TrInt D x := by
  rw [dI, Formalism.L2.Pj.dual_eq Formalism.IndefR.Fin.factPrincipalDatum D,
    FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) _ _ _)]
  constructor
  · intro h o
    obtain ⟨n, hn⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply] at hn
    rw [← hn]; simp
  · intro h b hb
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
    obtain ⟨n, hn⟩ := h o
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    rw [show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl, hn]; simp

theorem TrInt.mul {x : D.host.E} (h : TrInt D x) (o : 𝓞 D.host.E) : TrInt D (x * o) := fun o' => by
  obtain ⟨n, hn⟩ := h (o * o')
  exact ⟨n, by rw [mul_assoc]; simpa using hn⟩

theorem trInt_coe (o : 𝓞 D.host.E) : TrInt D (o : D.host.E) := fun o' => by
  have hi : IsIntegral ℤ ((o : D.host.E) * o') := o.isIntegral_coe.mul o'.isIntegral_coe
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hi)
  exact ⟨n, hn.symm⟩

theorem chi_tmul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {β : Af D.host.F}
    (hβ : β ∈ intAf D.host.F) {x : D.host.E} (hx : TrInt D x) : Conductor.chi ψ (β ⊗ₜ[D.host.F] x) = 1 := by
  rw [Conductor.chi, GlobalTheory.LatVac.trace_tmul]
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hβ
  rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
  have hi : IsIntegral ℤ (algebraMap D.host.F D.host.E (a : D.host.F)) :=
    a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  obtain ⟨n, hn⟩ := hx ⟨_, hi⟩
  exact ⟨n, by rw [Algebra.smul_def, mul_comm]; exact hn⟩

theorem chi_mul_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {x : D.host.E} (hx : TrInt D x)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    Conductor.chi ψ (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * z) = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact chi_tmul hψ hβ (hx.mul o)
  | zero => rw [mul_zero]; exact Conductor.chi_zero ψ
  | add y y' _ _ hy hy' => rw [mul_add, Conductor.chi_add, hy, hy', one_mul]
  | neg y _ hy =>
    have := Conductor.chi_add ψ (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * y) (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * -y)
    rwa [← mul_add, add_neg_cancel, mul_zero, Conductor.chi_zero, hy, one_mul, eq_comm] at this

theorem psiE_add (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) : psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  rw [psiE, psiE, psiE, map_add, ψ.map_add_eq_mul]

theorem psiE_zero (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  rw [psiE, map_zero, ψ.map_zero_eq_one]

theorem psiE_neg (ψ : AddChar (AF D.host.F) ℂ) (a : AE D) : psiE ψ (-a) = (psiE ψ a)⁻¹ := by
  rw [psiE, psiE, map_neg, ψ.map_neg_eq_inv]

theorem forward {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (v : Pl D) {s : AE D}
    (hs : s ∈ idV (dI D) v) : ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 := by
  induction hs using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, rfl⟩ := hy
    intro o ho
    have hinf : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a * o) = 0 := by
      rw [RingHom.map_mul, GlobalTheory.LatVac.infPart_pair, zero_mul]
    rw [Conductor.psiE_eq_chi ψ hinf, RingHom.map_mul, GlobalTheory.LatVac.finPart_pair]
    have e : α ⊗ₜ[D.host.F] a = ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) * (α ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e, mul_assoc]
    exact chi_mul_int hψ ((mem_dI_iff a).1 ha) (Conductor.mul_mem_int (Conductor.tmul_mem hα 1) ho.2)
  | zero => intro o _; rw [zero_mul, psiE_zero]
  | add x y _ _ hx hy => intro o ho; rw [add_mul, psiE_add, hx o ho, hy o ho, one_mul]
  | neg x _ hx => intro o ho; rw [neg_mul, psiE_neg, hx o ho, inv_one]

def lift (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E

theorem lift_tmul (α : Af D.host.F) (x : D.host.E) : lift D (α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 α ⊗ₜ[D.host.F] x := rfl

theorem finPart_lift (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (lift D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α x => rw [lift_tmul, GlobalTheory.LatVac.finPart_pair]
  | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]

theorem infPart_lift (z : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (lift D z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α x => rw [lift_tmul, GlobalTheory.LatVac.infPart_pair]
  | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy, add_zero]

theorem eq_lift {s : AE D} (h : infPart D s = 0) : s = lift D (finPart D s) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_sub, h, infPart_lift, sub_zero]
  · rw [RingHom.map_sub, finPart_lift, sub_self]

theorem lift_int_mem (v : Pl D) (hε : singleV D.host.F v 1 ∈ intAf D.host.F) {u : Af D.host.F ⊗[D.host.F] D.host.E}
    (hu : u ∈ intAE D) : lift D ((singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * u) ∈ idV (dI D) v := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, o, rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.mul_mem_intAf hε hβ, fun w hw => ?_, (o : D.host.E),
      (mem_dI_iff _).2 (trInt_coe o), lift_tmul _ _⟩
    rw [map_mul, Conductor.ev_ne hw, zero_mul]
  | zero => rw [mul_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add, map_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg, map_neg]; exact neg_mem hx

theorem backward {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (v : Pl D) {s : AE D}
    (hs : s ∈ idAt D (· = v)) (h : ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) : s ∈ idV (dI D) v := by
  have hs1 : infPart D s = 0 := hs.1
  have hinf : ∀ o, infPart D (s * o) = 0 := fun o => by
    rw [RingHom.map_mul, hs1, zero_mul]
  have hz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D s = finPart D s :=
    Conductor.idem_mul v _ fun w hw => (Submodule.mem_iInf _).1 hs.2 ⟨w, hw⟩
  obtain ⟨x, u, hu, e⟩ := Conductor.approx (finPart D s)
  have hε : singleV D.host.F v 1 ∈ intAf D.host.F := by
    have := Conductor.idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at this
  have hx : TrInt D x := fun o => by
    have h1 := h _ (Conductor.lift_mem v o)
    have e1 : singleV D.host.F v 1 ⊗ₜ[D.host.F] (o : D.host.E) =
        (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (o : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Conductor.psiE_eq_chi ψ (hinf _), RingHom.map_mul, GlobalTheory.LatVac.finPart_pair, e1, ← mul_assoc,
      mul_comm (finPart D s), hz, e, add_mul, Conductor.chi_add,
      Conductor.chi_int hψ (Conductor.mul_mem_int hu (Conductor.tmul_mem (GlobalTheory.LatVac.one_mem_intAf _) o)), mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one] at h1
    exact (Conductor.chi_rat hψ _).1 h1
  have hfin : finPart D s = singleV D.host.F v 1 ⊗ₜ[D.host.F] x +
      (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * u := by
    rw [← hz, e, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [eq_lift hs1, hfin, map_add]
  exact add_mem (AddSubgroup.subset_closure ⟨_, hε, fun w hw => Conductor.ev_ne hw, x, (mem_dI_iff x).2 hx,
    lift_tmul _ _⟩) (lift_int_mem v hε hu)

theorem idV_dI_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (v : Pl D),
    ∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 :=
  fun _ _ hψ v _ hs => ⟨fun h => forward hψ v h, backward hψ v hs⟩

end GlobalTheory.SeeSaw.DiffDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCFrameLat
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.AbsConv

open Filter Set GlobalTheory.Eis

theorem isSelfDualC_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem enorm_dblIntegrand {D : D7} {V : HSp D} (μ : (AE D)ˣ →* Circle) (E : GA D (dblSp V) → ℂ)
    (f₁ f₂ : GA D V → ℂ) (x : GA D V × GA D V) :
    ‖dblIntegrand V μ E f₁ f₂ x‖ₑ = ‖E (io V x)‖ₑ * (‖f₁ x.1‖ₑ * ‖f₂ x.2‖ₑ) := by
  simp only [dblIntegrand]
  simp_rw [← ofReal_norm_eq_enorm]
  rw [norm_mul, norm_mul, norm_mul, norm_inv, Circle.norm_coe, inv_one, mul_one, Complex.norm_conj,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem dblConv_of_growth {D : D7} {V : HSp D} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ)
    {m : Measure (GA D V)} (hm : m.IsHaarMeasure) {f₁ f₂ : GA D V → ℂ} (h₁ : GlobalTheory.Grow.RapidDec V f₁)
    (h₂ : GlobalTheory.Grow.RapidDec V f₂) {E : GA D (dblSp V) → ℂ} (hE : LeftInv (GQ (dblSp V)) E) (hc : Continuous E)
    {C : ℝ} {N : ℕ} (hb : ∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) :
    DblConv V μ m E f₁ f₂ := by
  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_dblIntegrand hμ hE h₁.1 h₂.1
  have hmeas : AEStronglyMeasurable (dblIntegrandQ V μ E f₁ f₂) ((autMeasure V m).prod (autMeasure V m)) := by
    have e' : dblIntegrandQ V μ E f₁ f₂ = dblIntegrand V μ E f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
      funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk hli _ _)
    rw [e']
    exact ((continuous_dblIntegrand hμ hc h₁.continuous h₂.continuous).measurable.comp
      (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
  have i₁ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₁ h₁ N
  have i₂ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₂ h₂ N
  set K : ℝ := max C 0 * 4 ^ N with hK
  have hK0 : 0 ≤ K := mul_nonneg (le_max_right _ _) (by positivity)
  refine ⟨hli, ((i₁.mul_prod i₂).const_mul K).mono' hmeas (Eventually.of_forall fun q => ?_)⟩
  obtain ⟨γ₁, hγ₁, e₁⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.1.out
  obtain ⟨γ₂, hγ₂, e₂⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.2.out
  have hinv : E (io V (q.1.out, q.2.out)) = E (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := by
    have e : io V (γ₁ * q.1.out, γ₂ * q.2.out) = io V (γ₁, γ₂) * io V (q.1.out, q.2.out) := by
      rw [← map_mul]; rfl
    rw [e, hE _ (io_mem_GQ V hγ₁ hγ₂)]
  have hq₁ := GlobalTheory.Grow.one_le_quotHeight V q.1.out
  have hq₂ := GlobalTheory.Grow.one_le_quotHeight V q.2.out
  have hx₁ := GlobalTheory.Grow.one_le_height V (γ₁ * q.1.out)
  have hx₂ := GlobalTheory.Grow.one_le_height V (γ₂ * q.2.out)
  have h3 : GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ≤
      4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) := by
    refine (GlobalTheory.Cont.HeightIo.height_io_le_mul V _ _).trans ?_
    nlinarith
  have h0 : 1 ≤ GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := GlobalTheory.Grow.one_le_height _ _
  have hEq : ‖E (io V (q.1.out, q.2.out))‖ ≤
      K * (GlobalTheory.Grow.quotHeight V q.1.out ^ N * GlobalTheory.Grow.quotHeight V q.2.out ^ N) := by
    rw [hinv]
    calc _ ≤ C * GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ^ N := hb _
      _ ≤ max C 0 * (4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out)) ^ N :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by linarith) h3 N) (pow_nonneg (by linarith) N)
            (le_max_right _ _)
      _ = _ := by rw [hK, mul_pow, mul_pow]; ring
  have hμ1 : ‖((μ (detA V q.2.out) : ℂ))⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  simp only [dblIntegrandQ, dblIntegrand, norm_mul, hμ1, mul_one, Complex.norm_conj]
  calc ‖E (io V (q.1.out, q.2.out))‖ * ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖
      ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ N * GlobalTheory.Grow.quotHeight V q.2.out ^ N) *
          ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖ := by gcongr
    _ = _ := by ring

theorem absConv_unfolded : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle),
    IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s,
    GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V),
    m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ →
    (∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 m → ∑' q : GlobalTheory.Eis.SiegelCosets V, ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖GlobalTheory.Eis.dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m ≠ ⊤) ∧
    GlobalTheory.Eis.DblConv V μ m (GlobalTheory.Eis.eis V φ) f₁ f₂ := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  have hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (isSelfDualC_frameLat V) ha
  have hS : SphConv V a := GlobalTheory.Eis.sphConv D V a hI
  have hσ : (V.rank : ℝ) / 2 < ((s.re : ℂ)).re := by simpa using hs
  have hconvS : ∀ g, EisConv V (sph V a (s.re : ℂ)) g := fun g => (((sphConv_iff hI).1 hS).1 _ hσ).2 g
  have h2 : ∀ g, sph V a (s.re : ℂ) g = (((hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) : ℝ) : ℂ) := fun g => by
    rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]; push_cast; rfl
  have hr0 : ∀ g, 0 ≤ (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g =>
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hn : ∀ g, ‖sph V a (s.re : ℂ) g‖ = (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g => by
    rw [h2, Complex.norm_real, Real.norm_of_nonneg (hr0 g)]
  have hsS : ∀ g, Summable fun q : SiegelCosets V =>
      ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ := fun g => hconvS g
  have heS : ∀ g, ‖eis V (sph V a (s.re : ℂ)) g‖ =
      ∑' q : SiegelCosets V, ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ := by
    intro g
    have e : eis V (sph V a (s.re : ℂ)) g = ((∑' q : SiegelCosets V,
        ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun q => by rw [hn]; exact h2 _
    rw [e, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := by
    haveI := t2Space_adeleRing' (F := D.host.F)
    exact hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  have hφS : ∀ g, ‖φ g‖ ≤ max C 0 * ‖sph V a (s.re : ℂ) g‖ := fun g =>
    (hC g).trans (by rw [hn]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hr0 g))
  have hsφ : ∀ y, Summable fun q : SiegelCosets V => ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y)‖ :=
    fun y => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hφS _) ((hsS y).mul_left _)
  have hle : ∀ y, ∑' q : SiegelCosets V, ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y)‖ ≤
      max C 0 * ‖eis V (sph V a (s.re : ℂ)) y‖ := fun y => by
    rw [heS, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun q => hφS _) (hsφ y) ((hsS y).mul_left _)
  obtain ⟨B, A, hB⟩ := hgrow
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have hSi : LeftInv (GQ (dblSp V)) (eis V (sph V a (s.re : ℂ))) := leftInv_eis (leftInv_of_mem h1 (sph_mem hI _))
  have hSc : Continuous (eis V (sph V a (s.re : ℂ))) := SphConv.continuous_eis hI (sph_mem hI _) hS hσ
  have hconv0 : DblConv V μ m (fun y => (((max C 0 * ‖eis V (sph V a (s.re : ℂ)) y‖ : ℝ)) : ℂ)) f₁ f₂ := by
    refine dblConv_of_growth hμ hm h₁ h₂ (C := max C 0 * B) (N := A) (fun γ hγ g => ?_)
      (Complex.continuous_ofReal.comp (continuous_const.mul hSc.norm)) (fun g => ?_)
    · beta_reduce
      rw [hSi γ hγ g]
    · rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _)), mul_assoc]
      exact mul_le_mul_of_nonneg_left (hB g) (le_max_right _ _)
  refine ⟨fun 𝓕 h𝓕 => ?_, ?_⟩
  · have hint := (hconv0.dblInt_eq h𝓕).1
    have hφc : Continuous φ := hφ.2.1
    have hmeas : ∀ q : SiegelCosets V, AEMeasurable (fun x =>
        ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ)
        ((m.prod m).restrict (𝓕 ×ˢ 𝓕)) := fun q =>
      (continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous
        h₂.continuous).measurable.enorm.aemeasurable
    rw [← lintegral_tsum hmeas]
    refine ne_top_of_le_ne_top hint.2.ne (lintegral_mono fun x => ?_)
    simp only [enorm_dblIntegrand]
    rw [ENNReal.tsum_mul_right]
    gcongr ?_ * _
    simp_rw [← ofReal_norm_eq_enorm]
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _)),
      ← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsφ _)]
    exact ENNReal.ofReal_le_ofReal (hle _)
  · refine dblConv_of_growth hμ hm h₁ h₂ (leftInv_eis (leftInv_of_mem hμ hφ)) (SphConv.continuous_eis hI hφ hS hs)
      (C := max C 0 * B) (N := A) fun g => ?_
    refine (norm_tsum_le_tsum_norm (hsφ g)).trans ((hle g).trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB g) (le_max_right _ _)

end GlobalTheory.Core.Rk.AbsConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratesSpanLastStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.SpanX

theorem itSpans_pk : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → GlobalTheory.Core.Mi.ItSpans ((pk W).MY (D.R.m - 1)) (pk W).MX (pk W).ItX := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W hP
  have hC := hP.bot.hyp.2.2.2.1
  have hok := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ _ hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX hC.chain.vY hC.chain.vX
  have hm : 0 < D.R.m := lt_of_lt_of_le two_pos D.R.two_le_m
  obtain ⟨hw, hv⟩ := hok.2 W.P.A3.A.μ0 ⟨D.R.m - 1, by omega⟩ rfl
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ ((pk W).MY (D.R.m - 1)) (pk W).MX (pk W).θ (pk W).ψ _ _
    ((pk W).ωX W.P.A3.A.μ0) ((pk W).vX W.P.A3.A.μ0) (pk W).ItX hC.models.inf hw hv (hC.chain.ItX W.P.A3.A.μ0)
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap ((pk W).ItX P) (Submodule.span ℂ
      {x | ∃ (P : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (y : (pk W).MX.Vec), KVecP (pk W).MX y ∧
        x = (pk W).ItX P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => GlobalTheory.Core.Mi.StepSpans.isKFin_of_mem_kfin _ _ (hy τ), rfl⟩
  exact hu'

end GlobalTheory.Core.Mi.SpanX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapMemValCTrue
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Core.Rk
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.ValLaw

open Formalism.L2.Ker
open GlobalTheory.GO.ChSrc (trueWt nuEnd sS sD polFn fnPol)
open Formalism.L2.Forms (fnOf shiftOf ValC CSpan)

variable {X : Fields} {R : Ranks}

theorem fnOf_one_apply {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Formalism.L2.Forms.Frames G) :
    fnOf G s 1 P y = (∏ τ, (y.1 τ).det ^ s τ) * MvPolynomial.eval (fun x => y.1 x.1 x.2.1 x.2.2) P := by
  simp [fnOf]

theorem jetMap_mem_VV (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m)
    (J : (DVar X.Tau (R.N i) (R.N (i + 1)) →₀ ℕ) → ℂ) (P : Pol ℂ X.Tau (R.N i)) (hP : P ∈ VV ℂ (trueWt hc i)) :
    jetMap J (nuEnd hc i) P ∈ VV ℂ (trueWt hc (i + 1)) := by
  have hN : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [add_mul]; omega
  refine GlobalTheory.JetPoint.jetMap_mem hN.le _ _ _ (fun ap => ?_) J
  refine GlobalTheory.SubstMem.substAdj_sharp_mem ℂ X.Tau _ _ hN _ _ (sD hc i) (sS hc i) _
    ⟨fun τ a => ?_, fun τ j hj => GlobalTheory.GO.ChSrc.trueWt_new hc hi τ j (not_lt.mpr hj), GlobalTheory.GO.ChSrc.nuEnd_cast hc hi⟩ ap _ hP
  have := GlobalTheory.GO.ChSrc.trueWt_old hc hi τ (Fin.castLE hN.le a) a.2
  simp only [Fin.val_castLE, Fin.eta] at this
  omega

theorem jetMap_zero_mul {ι : Type} [Fintype ι] {a b : ℕ} (J : (DVar ι a b →₀ ℕ) → ℂ) (n : ι → ℕ) (P : Pol ℂ ι a) :
    jetMap J 0 (P * ∏ τ, frDet ℂ a τ ^ n τ) = jetMap J n P := by
  simp [jetMap]

end GlobalTheory.Core.Rk.ValLaw

namespace GlobalTheory.Core.Rk.ValLaw

open Formalism.L2.Ker
open GlobalTheory.GO.ChSrc (trueWt nuEnd sS sD polFn fnPol)
open Formalism.L2.Forms (fnOf shiftOf ValC CSpan)

variable {X : Fields} {R : Ranks}

theorem kmap_mem_valC (I : ChainIn X.E X.K X.Tau R) (σ : X.K →+* ℂ) (h : I.Ok) (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m)
    (c : (I.S i).Cl) (c' : (I.S (i + 1)).Cl) (J : (DVar X.Tau (R.N i) (R.N (i + 1)) →₀ ℕ) → ℂ) (hJ : I.jet i c c' = jetMap J 0)
    (f : Fr X.emb σ (R.N i) → ℂ) (hf : f ∈ ValC (Gr X.emb σ (R.N i)) (trueWt hc i)) :
    (I.chain X.emb σ h hc).Kmap i c c' f ∈ ValC (Gr X.emb σ (R.N (i + 1))) (trueWt hc (i + 1)) := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hf
  rw [GlobalTheory.Pdv.FormsStd.cSpan_eq_VV] at hP
  have h1 : (I.chain X.emb σ h hc).sharp i (fnOf (Gr X.emb σ (R.N i)) (shiftOf (trueWt hc i)) 1 P) =
      polFn X σ _ (P * ∏ τ, frDet ℂ (R.N i) τ ^ nuEnd hc i τ) := by
    funext (y : Fr X.emb σ (R.N i))
    have hd : ∀ τ, MvPolynomial.eval (fun v : X.Tau × Fin (R.N i) × Fin (R.N i) => y.1 v.1 v.2.1 v.2.2)
        (frDet ℂ (R.N i) τ) = (y.1 τ).det := fun τ => by
      rw [frDet, RingHom.map_det]
      congr 1
      ext a b
      simp
    show (∏ τ, (y.1 τ).det ^ (I.chain X.emb σ h hc).sSharp i τ) * fnOf (Gr X.emb σ (R.N i)) (shiftOf (trueWt hc i)) 1 P y = _
    rw [GlobalTheory.GO.ChSrc.polFn_apply, MvPolynomial.eval_mul, MvPolynomial.eval_prod, fnOf_one_apply, ← mul_assoc,
      ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.eval_pow, hd, ← zpow_natCast, GlobalTheory.GO.ChSrc.nuEnd_cast hc hi, zpow_add₀ (isUnit_det_fr y τ).ne_zero,
      (GlobalTheory.LvT.Built.KMap.sSharp_eq I σ h hc hi τ).1, mul_comm]
    rfl
  refine Submodule.mem_map.2 ⟨(I.rho i c * I.rho' i c') • jetMap J (nuEnd hc i) P, ?_, ?_⟩
  · rw [GlobalTheory.Pdv.FormsStd.cSpan_eq_VV]
    exact Submodule.smul_mem _ _ (jetMap_mem_VV hc hi J P hP)
  funext (y : Fr X.emb σ (R.N (i + 1)))
  show _ = (I.rho i c * I.rho' i c') * ((∏ τ, (y.1 τ).det ^ (I.chain X.emb σ h hc).sDiv i τ)⁻¹ *
    polFn X σ _ (I.jet i c c' (fnPol X σ _ ((I.chain X.emb σ h hc).sharp i (fnOf (Gr X.emb σ (R.N i)) (shiftOf (trueWt hc i)) 1 P)))) y)
  rw [h1, GlobalTheory.GO.ChSrc.fnPol_polFn, hJ, jetMap_zero_mul, map_smul, Pi.smul_apply, smul_eq_mul, fnOf_one_apply,
    GlobalTheory.GO.ChSrc.polFn_apply]
  congr 1
  congr 1
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [(GlobalTheory.LvT.Built.KMap.sSharp_eq I σ h hc hi τ).2, ← zpow_neg, ← GlobalTheory.GO.ChSrc.trueWt_detShift_succ hc hi]
  rfl

end GlobalTheory.Core.Rk.ValLaw

namespace GlobalTheory.Core.Rk

end GlobalTheory.Core.Rk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaValueEdgeSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_value_edge_sum : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (x : G.S.P.J) (g : GL (Fin D.R.r) (kP PP)), G.Red x g → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = edgeSum (GlobalTheory.chainEdge D.R.k) g → ((G.S.P.lam x : ℂˣ) : ℂ) = (G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E)) : ℂ) := by
  first | exact @GlobalTheory.ChainChar.lam_eq_of_red | exact GlobalTheory.ChainChar.lam_eq_of_red | (intros; apply GlobalTheory.ChainChar.lam_eq_of_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.move_compact_level_invariant : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → A.MoveAt θ i hi c₀ g h → ∀ k ∈ GfC _, ∀ k' ∈ GfC _, Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) k (Formalism.L2.Col.stdLat B.fields.E _) → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) k' (Formalism.L2.Col.stdLat B.fields.E _) → A.MoveAt θ i hi c₀ (g * k) (h * k') := by
  first | exact @GlobalTheory.AdForm.StabMove.moveAt_mul_stab | exact GlobalTheory.AdForm.StabMove.moveAt_mul_stab | (intros; apply GlobalTheory.AdForm.StabMove.moveAt_mul_stab <;> assumption)
end

