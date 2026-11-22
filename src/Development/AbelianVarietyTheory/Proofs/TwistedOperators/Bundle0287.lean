import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsIrrOfEquiv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinIrr

private lemma act_mem_of_forall_upq_act_mem {p q : ℕ} (N : GKMod p q) (W : Submodule ℂ N.V)
    (h : ∀ Z ∈ upq p q, ∀ y ∈ W, N.act Z y ∈ W) : ∀ Z, ∀ y ∈ W, N.act Z y ∈ W := by
  intro Z y hy
  have hre := h _ (GlobalTheory.AdjDescent.re_mem_upq Z) y hy
  have him := h _ (GlobalTheory.AdjDescent.im_mem_upq Z) y hy
  have hZ := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = A at hZ hre
  generalize Complex.I • (Z - conjR Z) = B at hZ him
  rw [hZ, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  exact W.add_mem (W.smul_mem _ hre) (W.smul_mem _ him)

private lemma comm_act_of_comm_act_upq {p q : ℕ} (N : GKMod p q) (T : N.V →ₗ[ℂ] N.V)
    (h : ∀ Z ∈ upq p q, T ∘ₗ N.act Z = N.act Z ∘ₗ T) : ∀ Z, T ∘ₗ N.act Z = N.act Z ∘ₗ T := by
  intro Z
  have hre := h _ (GlobalTheory.AdjDescent.re_mem_upq Z)
  have him := h _ (GlobalTheory.AdjDescent.im_mem_upq Z)
  have hZ := GlobalTheory.AdjDescent.decomp Z
  generalize Z + conjR Z = A at hZ hre
  generalize Complex.I • (Z - conjR Z) = B at hZ him
  rw [hZ, map_add, map_smul, map_smul, LinearMap.comp_add, LinearMap.add_comp,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp, hre, him]

theorem absIrr_of_equiv {p q : ℕ} (N : GKMod p q) (hI : Formalism.MainNotions.SchurIrreducible.IrrGK N) (hA : Formalism.MainNotions.SchurIrreducible.AdmGK N)
    {G K : Type} [AddCommGroup K] [Module ℂ K] (a : G → Module.End ℂ K) (e : K ≃ₗ[ℂ] N.V)
    (h : ∀ Z ∈ upq p q, ∃ (g : G) (c : ℂ), ∀ x, e (a g x) = N.act Z (e x) + c • e x) : AbsIrr a := by
  have hy : ∀ Z ∈ upq p q, ∃ (g : G) (c : ℂ), ∀ x, N.act Z (e x) = e (a g x - c • x) := by
    intro Z hZ
    obtain ⟨g, c, hg⟩ := h Z hZ
    refine ⟨g, c, fun x => ?_⟩
    rw [map_sub, map_smul, hg, add_sub_cancel_right]
  refine ⟨fun W hW => ?_, fun T hT => ?_⟩
  · have hst : ∀ Z ∈ upq p q, ∀ y ∈ W.map (e : K →ₗ[ℂ] N.V), N.act Z y ∈ W.map (e : K →ₗ[ℂ] N.V) := by
      rintro Z hZ _ ⟨x, hx, rfl⟩
      obtain ⟨g, c, hg⟩ := hy Z hZ
      have hmem : a g x - c • x ∈ W := W.sub_mem (hW g x hx) (W.smul_mem c hx)
      have hout := Submodule.mem_map_of_mem (f := (e : K →ₗ[ℂ] N.V)) hmem
      simpa [hg] using hout
    rcases hI.2 _ (act_mem_of_forall_upq_act_mem N _ hst) with h0 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (e : K →ₗ[ℂ] N.V) x ∈ W.map (e : K →ₗ[ℂ] N.V) := Submodule.mem_map_of_mem hx
      rw [h0, Submodule.mem_bot] at hx'
      rw [Submodule.mem_bot]
      simpa using hx'
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (e : K →ₗ[ℂ] N.V) x ∈ W.map (e : K →ₗ[ℂ] N.V) := by rw [h1]; trivial
      obtain ⟨y, hyW, hyx⟩ := Submodule.mem_map.mp hx'
      have hxy : y = x := e.injective hyx
      exact hxy ▸ hyW
  · have hc : ∀ Z ∈ upq p q, ((e : K →ₗ[ℂ] N.V) ∘ₗ T ∘ₗ (e.symm : N.V →ₗ[ℂ] K)) ∘ₗ N.act Z =
        N.act Z ∘ₗ ((e : K →ₗ[ℂ] N.V) ∘ₗ T ∘ₗ (e.symm : N.V →ₗ[ℂ] K)) := by
      intro Z hZ
      obtain ⟨g, c, hg⟩ := hy Z hZ
      have hTg : ∀ x, T (a g x) = a g (T x) := fun x => LinearMap.congr_fun (hT g) x
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg, LinearEquiv.symm_apply_apply, map_sub, map_smul, hTg]
    obtain ⟨c, hc'⟩ := GlobalTheory.IrrTensor.schur N hI hA _ (comm_act_of_comm_act_upq N _ hc)
    refine ⟨c, LinearMap.ext fun x => e.injective ?_⟩
    have hx := LinearMap.congr_fun hc' (e x)
    simpa using hx

theorem absIrr_kFin : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ ≃ₗ[ℂ] R.U.H) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → Formalism.MainNotions.SchurIrreducible.IrrGK R.HK → Formalism.MainNotions.SchurIrreducible.AdmGK R.HK → IsKAct M τ a → AbsIrr fun X : lieAt V τ => a X := by
  intro D V S M τ p q T R φ m U a hM hI hA hK
  have hfin : ∀ x : kFin M τ, U x ∈ LinearMap.range R.ι := fun x =>
    LinearMap.mem_range.mpr ((hM.kfin x.1).mp x.2)
  have hequiv : ∃ e : kFin M τ ≃ₗ[ℂ] R.HK.V, ∀ y, R.ι (e y) = U y := by
    let f : kFin M τ →ₗ[ℂ] LinearMap.range R.ι :=
      LinearMap.codRestrict (LinearMap.range R.ι) ((U : M.H τ →ₗ[ℂ] R.U.H) ∘ₗ (kFin M τ).subtype) hfin
    have hf : ∀ y, (f y : R.U.H) = U y := fun y => rfl
    have hbij : Function.Bijective f := by
      constructor
      · intro x y hxy
        have hv : U x = U y := by rw [← hf, ← hf, hxy]
        exact Subtype.ext (U.injective hv)
      · rintro ⟨y, hy⟩
        have hk : U.symm y ∈ kFin M τ := by
          refine (hM.kfin _).mpr ?_
          rw [U.apply_symm_apply]
          exact LinearMap.mem_range.mp hy
        refine ⟨⟨U.symm y, hk⟩, Subtype.ext ?_⟩
        rw [hf]
        exact U.apply_symm_apply y
    let e2 := LinearEquiv.ofInjective R.ι R.ι_inj
    refine ⟨(LinearEquiv.ofBijective f hbij).trans e2.symm, fun y => ?_⟩
    have h3 := congrArg Subtype.val (e2.apply_symm_apply (f y))
    rw [LinearEquiv.ofInjective_apply, hf] at h3
    exact h3
  obtain ⟨e, hιe⟩ := hequiv
  refine absIrr_of_equiv R.HK hI hA (fun X : lieAt V τ => a X) e ?_
  intro Z hZ
  have hX : IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z) ∈ lieAt V τ := by
    rw [← hM.lie]
    exact ⟨Z, hZ, rfl⟩
  have hd : ∀ x : kFin M τ, dRep (M.rep τ) (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) (x : M.H τ) =
      (a (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) x : M.H τ) := fun x =>
    (hK.der _ hX x).deriv
  refine ⟨⟨_, hX⟩, (m : ℂ) / 2 * Z.trace, fun x => R.ι_inj ?_⟩
  show R.ι (e (a (IndefiniteRowSideFullHecke.BarMatrix.toFrame M τ (φ Z)) x)) = R.ι (R.HK.act Z (e x) + ((m : ℂ) / 2 * Z.trace) • e x)
  rw [hιe, ← hM.der Z hZ (e x) x (hιe x).symm, hd x]

end GlobalTheory.KFinIrr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.Adapted
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLoc

variable {D : D7}

def embAt (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau) (k : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  cmp θ τ (stabilizerEmbedding d (atTau θ Y τ k))

def mco {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (v₀ : M.H τ) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : ℂ :=
  ⟪M.rep τ g₀ v₀, M.rep τ g (M.rep τ g₀ v₀)⟫_ℂ

def ptY {Y : HSp D} {S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S') (τ : D.what₂.Tau) (u : Formalism.REAL.UJ (M₀.ε τ)) :
    Matrix (Fin Y.rank) (Fin Y.rank) ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M₀ τ (Formalism.MainNotions.S.umat u)

structure LocOK (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S')
    (M : DSModel V S) (τ : D.what₂.Tau) (q : ℝ) (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ)
    (εB : Fin V.rank → Bool) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ) (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : M₀.H τ) (c : ℂ) : Prop where

  unitA : IsUnit A

  gramA : Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ

  unitB : IsUnit B

  gramB : Bᴴ * Formalism.REAL.Jm εB * B = gramAt D V τ

  adapted : ∀ (y : Fin Y.rank → ℂ) (a : ℂ),
    eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2

  real : g₀ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)

  kfin : v₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ

  dec : DecayAt M τ v₀ v₀ (2 * V.rank ^ 2 + 1)

  sm : w ∈ M₀.sm τ

  ne : w ≠ 0

  cne : c ≠ 0

  act : ∀ b : M₀.H τ, ∫ u, mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u)) * ⟪b, M₀.rep τ (ptY M₀ τ u) w⟫_ℂ ∂(Formalism.REAL.muG (M₀.ε τ)) =
    c * ⟪b, w⟫_ℂ

  far : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => mco M τ g₀ v₀ (g * embAt θ d τ (ptY M₀ τ u))) (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖mco M τ g₀ v₀ (g * embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖c‖

  lip : ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖mco M τ g₀ v₀ (embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * ptY M₀ τ u)) -
      mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖mco M τ g₀ v₀ (embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * ptY M₀ τ u)) -
      mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤ Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹)

end GlobalTheory.PackLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModuleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaar_leftRightMul_adelicMatrices_module : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)), μ.IsAddHaarMeasure → ∀ (g : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det g) : ENNReal) ^ n * (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ m) • Measure.map (fun u : Mx D m n => (HMul.hMul (HMul.hMul g.val (u : Matrix (Fin m) (Fin n) (AE D))) a.val : Mx D m n)) μ := by
  first | exact @GlobalTheory.ModuLR.modu_lrMul | exact GlobalTheory.ModuLR.modu_lrMul | (intros; apply GlobalTheory.ModuLR.modu_lrMul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentMulIntegralOfUnitFactorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleIdempotent_mul_integral_of_unit_factor : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (u : 𝓞 D.host.F), u ∉ v.asIdeal → ∀ z : AE D, GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z ∈ intAt D (· = v) → GlobalTheory.FinPlLoc.idem D (· = v) * z ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.UnitAtPl.idem_mul_mem_of_unit | exact GlobalTheory.UnitAtPl.idem_mul_mem_of_unit | (intros; apply GlobalTheory.UnitAtPl.idem_mul_mem_of_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentSmulMemLatticeCompletionAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleIdempotent_smul_mem_latticeCompletionAtPlace : ∀ (D : D7) (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D) (z : Fin S.rank → AE D), z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (fun _ => True) → GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (· = v) := by
  first | exact @GlobalTheory.FinPlLoc.idem_smul_mem_latMul_at | exact GlobalTheory.FinPlLoc.idem_smul_mem_latMul_at | (intros; apply GlobalTheory.FinPlLoc.idem_smul_mem_latMul_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicPointRationalLatticeUnitaryModelIsoEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatDict
open Formalism.IndefR.Eqv.UI

theorem mem_hatL_iff (D : D7) (V : HSp D) (fr : Frames D V)
    (w : Fin V.rank → D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) :
    w ∈ Formalism.L2.Herm.hatL (F := D.host.F) fr.Λ ↔ w ∈ (instV fr).Lf := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf
  rw [Set.image_eq_range]
  rfl

theorem finE_brg (D : D7) (V : HSp D) (fr : Frames D V) (x : (instV fr).GA) :
    (Lev.finE V (brg fr x)).1 = (instV fr).fmat x.2 := by
  have hring : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E,
      Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) =
        Formalism.L2.SG.AdBridge.tauF (instV fr) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ((Lev.swapAE D).congr_arg (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
    | tmul a b => exact (Formalism.L2.SG.AdBridge.tauF_tmul (instV fr) a b).symm
    | add a b ha hb =>
      have e1 := _root_.map_add (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) a b
      rw [e1, RingHom.map_add, ha, hb]
      exact (RingHom.map_add _ _ _).symm
  rw [((brg_isBridge fr) x).2]
  ext i j
  simp only [Lev.finE, finHom, matHom, Formalism.UG.bc, Formalism.L2.SG.AdBridge.hmat, Formalism.L2.SG.AdBridge.ofHAFin,
    MonoidHom.comp_apply, Units.coe_map, Matrix.map_apply]
  exact hring _

theorem latAt_brg : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA), latAt fr.Λ (Formalism.IndefR.Eqv.UI.brg fr x) = GlobalTheory.Count.lamX (Formalism.IndefR.Eqv.UI.instV fr) x := by
  intro D V fr x
  unfold GlobalTheory.SepPer.latAt GlobalTheory.Count.lamX
  congr 1
  ext y
  rw [← map_inv (brg fr) x, finE_brg D V fr x⁻¹]
  exact mem_hatL_iff D V fr _

end GlobalTheory.LatDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointApplyOfEigen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.SplitEigen

theorem adjoint_apply_of_eigen {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A : Module.End ℂ H) (hA : Commute A (LinearMap.adjoint A)) (v : H) (μ : ℂ) (hv : A v = μ • v) :
    LinearMap.adjoint A v = starRingEnd ℂ μ • v := by
  set B : Module.End ℂ H := A - μ • 1 with hBdef
  have hBadj : LinearMap.adjoint B = LinearMap.adjoint A - starRingEnd ℂ μ • 1 := by
    rw [hBdef, map_sub, map_smulₛₗ]
    congr 2
    exact LinearMap.adjoint_id
  have hBv : B v = 0 := by
    rw [hBdef, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hv, sub_self]
  have hc : Commute B (LinearMap.adjoint B) := by
    rw [hBadj, hBdef]
    exact (hA.sub_right ((Commute.one_right A).smul_right _)).sub_left ((Commute.one_left _).smul_left _)
  have h0 : LinearMap.adjoint B v = 0 := by
    have e : inner ℂ (LinearMap.adjoint B v) (LinearMap.adjoint B v) = (0 : ℂ) := by
      rw [LinearMap.adjoint_inner_left]
      have : B (LinearMap.adjoint B v) = LinearMap.adjoint B (B v) := by
        rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
      rw [this, hBv, map_zero, inner_zero_right]
    exact inner_self_eq_zero.1 e
  rw [hBadj, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h0
  exact h0

theorem adjoin_scalar {M : Type} [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)) (X : Set M)
    (hS : ∀ b ∈ S, ∃ μ : ℂ, ∀ u ∈ X, b u = μ • u) : ∀ b ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∀ u ∈ X, b u = μ • u := by
  intro b hb
  induction hb using Algebra.adjoin_induction with
  | mem b hb => exact hS b hb
  | algebraMap r => exact ⟨r, fun u _ => Module.algebraMap_end_apply ℂ ℂ M r u⟩
  | add b b' _ _ ihb ihb' =>
    obtain ⟨μ, hμ⟩ := ihb
    obtain ⟨μ', hμ'⟩ := ihb'
    exact ⟨μ + μ', fun u hu => by rw [LinearMap.add_apply, hμ u hu, hμ' u hu, add_smul]⟩
  | mul b b' _ _ ihb ihb' =>
    obtain ⟨μ, hμ⟩ := ihb
    obtain ⟨μ', hμ'⟩ := ihb'
    exact ⟨μ * μ', fun u hu => by rw [Module.End.mul_apply, hμ' u hu, map_smul, hμ u hu, smul_smul, mul_comm]⟩

end GlobalTheory.SplitEigen

namespace GlobalTheory.SplitEigen

set_option maxHeartbeats 40000000 in

theorem label_scalar_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j A3.A.fam.μ0).H), GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0) h → ∀ (P : Pl D.host.E), GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → conjPl P ≠ P → ∀ d, GlobalTheory.Hk3.IsLab (Vc D j) P d → ∃ a : ℂ, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC hEx _hH _hGE j c h hh hN P hP hconj d _hd
  obtain ⟨hCoreF, -, -, hOnto, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have hCore := hCoreF hEx
  have hM := hCore.models
  obtain ⟨P0, hP0, rfl⟩ := (hOnto _ hP).2 hconj
  have hsplit := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hCore.lev hCore.fam hM).2 j A3.A.fam.μ0 h hh ⟨P0, hP0⟩
  have hK := RealDat3.kFormL_of (R := R) (F := F) hM

  have hop : ∀ k, k ≤ (Vc D j).rank → (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inl (⟨P0, hP0⟩, k))) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1)) := by
    intro k hk
    refine LinearMap.ext_on_range (hK j A3.A.fam.μ0).2 fun b => ?_
    rw [← CxData.jL_opL _ hK]
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (hsplit k hk _)

  have hT : ∀ k, k ≤ (Vc D j).rank → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
        cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k))) • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro k hk x hx
    have e1 := (U2.mem_eigPart.1 hx) (Sum.inl (⟨P0, hP0⟩, k))
    have e2 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (U2.liftHeckeOperators A3 (R.toCx3 F) j (Sum.inl (⟨P0, hP0⟩, k)) x) =
        h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) := by
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j A3.A.fam.μ0).H)) (LinearMap.congr_fun (hop k hk) x)).trans rfl
    rw [← e2, e1]
    exact Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j A3.A.fam.μ0).H) _ _

  have hD : ∀ k, k ≤ (Vc D j).rank → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      h (R.pl P0) (Finsupp.single (dualLab (splitLab (Vc D j).rank k)) 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
        starRingEnd ℂ (cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k)))) •
          (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro k hk x hx
    have ha : LinearMap.adjoint (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1)) =
        h (R.pl P0) (Finsupp.single (dualLab (splitLab (Vc D j).rank k)) 1) := by
      rw [hN.2 _ hP]
      congr 1
      rw [Finsupp.mapRange_single, star_one, GlobalTheory.Hk3.dualC, Finsupp.mapDomain_single]
    have hc : Commute (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1))
        (LinearMap.adjoint (h (R.pl P0) (Finsupp.single (splitLab (Vc D j).rank k) 1))) :=
      ha.symm ▸ hN.1 _ _ hP hP _ _
    exact (LinearMap.congr_fun ha _).symm.trans (adjoint_apply_of_eigen _ hc _ _ (hT k hk x hx))

  obtain ⟨a, ha, hae⟩ := GlobalTheory.SplitGen.gen_split (Vc D j) (R.pl P0) hconj _
    (GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D j)) (R.cV j).W) d
  have key := adjoin_scalar _ {u | ∃ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
      u = (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)} (by
    rintro b ⟨k, hk, rfl | rfl⟩
    · refine ⟨cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k))), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (GlobalTheory.DefiniteOps.hkF_eq (Vc D j) (R.pl P0) _ _).symm.trans ((hh _ hP _ _).symm.trans
        ((congrArg (R.HV j A3.A.fam.μ0).e (hT k hk x hx)).trans (map_smul _ _ _)))
    · refine ⟨starRingEnd ℂ (cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inl (⟨P0, hP0⟩, k)))), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (GlobalTheory.DefiniteOps.hkF_eq (Vc D j) (R.pl P0) _ _).symm.trans ((hh _ hP _ _).symm.trans
        ((congrArg (R.HV j A3.A.fam.μ0).e (hD k hk x hx)).trans (map_smul _ _ _)))) a ha
  obtain ⟨μ, hμ⟩ := key
  refine ⟨μ, fun x hx => (hM.HV j A3.A.fam.μ0).1 ?_⟩
  have hfix : ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D j) (R.pl P0), GlobalTheory.DefiniteOps.rtr (GlobalTheory.SplitHeckeAdj.fin (Vc D j)) (R.cV j).W k
      ((R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)) =
        (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) := by
    obtain ⟨n, hn⟩ := hCore.lev.βV j
    have hn' : IsBaseFrame (Vc D j) (R.βV j) (R.ΛV j) 1 := (one_pow n : (1 : ℕ) ^ n = 1) ▸ hn
    refine GlobalTheory.DefiniteOps.fixed_of_mem (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j A3.A.fam.μ0) hn' (R.pl P0) hP (R.cV j).coef.ρ _ ?_
    have hm := LinearMap.mem_range_self (R.HV j A3.A.fam.μ0).e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x)
    rw [(hM.HV j A3.A.fam.μ0).2.1] at hm
    exact hm
  exact (hh _ hP _ _).trans ((GlobalTheory.DefiniteOps.hkF_eq _ _ _ _).trans ((hae _ hfix).symm.trans
    ((hμ _ ⟨x, hx, rfl⟩).trans (map_smul _ _ _).symm)))

end GlobalTheory.SplitEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointInjOfParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjointInjectiveOfParts

theorem adjoint_inj_of_parts {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (T : H' →ₗ[ℂ] H) {ι : Type*}
    (P : ι → Submodule ℂ H) (s : ι → ℂ) (hs : ∀ c, s c ≠ 0)
    (hP : ∀ c, ∀ x ∈ P c, T (LinearMap.adjoint T x) = s c • x) {x : H} (hx : x ∈ ⨆ c, P c)
    (h0 : LinearMap.adjoint T x = 0) : x = 0 := by
  have hle : (⨆ c, P c) ≤ LinearMap.range T := by
    refine iSup_le fun c y hy => ⟨LinearMap.adjoint T ((s c)⁻¹ • y), ?_⟩
    rw [hP c _ ((P c).smul_mem _ hy), smul_smul, mul_inv_cancel₀ (hs c), one_smul]
  obtain ⟨w, rfl⟩ := hle hx
  have h1 : ⟪T w, T w⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

end GlobalTheory.AdjointInjectiveOfParts

open GlobalTheory.Hk3 in

theorem GlobalTheory.LiftRows.upInj_of_scal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → Scal R SF → UpInj R ∧ UpInjW R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hI SF hSF hScal
  obtain ⟨lam, κ, hκ, hl, hW, hE⟩ := hScal
  constructor
  · intro t
    refine (injective_iff_map_eq_zero _).2 fun x h0 => ?_
    obtain ⟨h, -, -, hsp, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
    refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.Th t) (fun c => EEc R SF c)
      (fun c => ((κ * ∏ i, lam i t c : ℝ) : ℂ))
      (fun c => Complex.ofReal_ne_zero.2 (mul_pos hκ (Finset.prod_pos fun i _ => hl i t c)).ne')
      (fun c x hx => hE t c x hx) ?_ h0
    rw [hsp]; trivial
  · intro i t x hx h0
    obtain ⟨h, -, -, -, hsp, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hI SF hSF i
    refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.thG i t) (fun c => Wcc R SF i c)
      (fun c => ((lam i t c : ℝ) : ℂ)) (fun c => Complex.ofReal_ne_zero.2 (hl i t c).ne')
      (fun c x hx => hW i t c x hx) ?_ h0
    rw [hsp]; exact ⟨x, hx⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryWittIsotropicCoordinateEqPairingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliaryWittIsotropicCoordinate_eq_pairing : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), c = 2 * ρ → IsAuxiliaryVectorWittDec a d → ∀ (i : Fin ρ) (hi : 2 * ρ - 1 - i.1 < c) (x : Fin B.rank → AE D), incA D ((-D.host.xi0) ^ (i.1 + 1)) * (d.pX *ᵥ x) i = ∑ k, ∑ l, cA D (incA D (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) * incA D (B.gram k l) * x l := by
  first | exact @GlobalTheory.AscFin.incA_neg_xi0_pow_mul_pX_mulVec_eq_sum | exact GlobalTheory.AscFin.incA_neg_xi0_pow_mul_pX_mulVec_eq_sum | (intros; apply GlobalTheory.AscFin.incA_neg_xi0_pow_mul_pX_mulVec_eq_sum <;> assumption)
end

