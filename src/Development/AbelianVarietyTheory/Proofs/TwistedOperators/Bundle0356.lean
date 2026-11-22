import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitesimalCharacterFactor
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0338
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviElementExists
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPowerDetAbsRealDiagonalTorus
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.HalfModTorus

open GlobalTheory.Doubling

theorem compFin_eq_one {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AE D) (h : finPart D y = 1) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E v y = 1 := by
  have h' : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y = 1 := h
  have e : GlobalTheory.AdelicU.compFin D.host.F D.host.E v y =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e, h', map_one]

theorem unitFin_eq_one {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (x : (AE D)ˣ) (h : finPart D (x : AE D) = 1) :
    unitFin D.host.F D.host.E v x = 1 :=
  Units.ext (compFin_eq_one v (x : AE D) h)

theorem compInf_eq {D : D7} (w : InfinitePlace D.host.F) (t' : GlobalTheory.AdelicU.EmbOver D.host.E w) (y : AE D) :
    GlobalTheory.AdelicU.infEmb t' (GlobalTheory.AdelicU.compInf D.host.F D.host.E w y) = GlobalTheory.AdelicU.infProj t' (infPart D y) := by
  have e : GlobalTheory.AdelicU.compInf D.host.F D.host.E w y =
      Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e]
  rfl

theorem absE_of_components {D : D7} (x : (AE D)ˣ) (c : NNReal)
    (hf : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x) = 1)
    (hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) (unitInf D.host.F D.host.E _ x) = c) :
    absE D.host.F D.host.E x = c ^ Fintype.card D.what₂.Tau := by
  have e1 : (∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x)) = 1 :=
    finprod_eq_one_of_forall_eq_one hf
  have e2 : (∏ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x)) = c ^ Fintype.card D.what₂.Tau := by
    rw [← (GlobalTheory.CMTypePlaces.places_bijective D).prod_comp
      (fun w => absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x))]
    simp only [hw, Finset.prod_const, Finset.card_univ]
  rw [absE_apply, e1, e2, mul_one]

theorem halfMod_torus : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (r n : ℕ) (t : Fin r → ℝ), (∀ i, 0 < t i) →
    ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 →
      (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n α = ∏ i, t i ^ (Module.finrank ℚ D.host.F * n) := by
  intro D θ hθ r n t ht α hfin hinf
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  haveI := hcm.1
  have hxv : ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D) = α.1.det := rfl
  have h1 : finPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D) = 1 := by
    rw [hxv, RingHom.map_det, RingHom.mapMatrix_apply, hfin, Matrix.det_one]
  have hf : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det α)) = 1 :=
    fun v => by rw [unitFin_eq_one v _ h1, map_one]
  have hdet : ∀ τ, θ τ (infPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D)) = ((∏ i, t i : ℝ) : ℂ) := by
    intro τ
    have e : θ τ (infPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D)) = (compAt θ τ α.1).det := by
      rw [hxv, ← RingHom.comp_apply, RingHom.map_det]
      rfl
    rw [e, hinf τ, Matrix.det_diagonal, Complex.ofReal_prod]
  have hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (unitInf D.host.F D.host.E _ (Matrix.GeneralLinearGroup.det α)) = ‖((∏ i, t i : ℝ) : ℂ)‖₊ ^ 2 := by
    intro τ
    let t' : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) :=
      ⟨tauE D τ, (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm⟩
    rw [absEw_eq_sq hcm t', ← hdet τ,
      GlobalTheory.AutFunCompare.isInfEmb_unique _ _ _ (hθ τ) (GlobalTheory.AdelicU.isInfEmb_infProj t')]
    exact congrArg (fun z : ℂ => ‖z‖₊ ^ 2) (compInf_eq _ t' _)
  have hcard : Fintype.card D.what₂.Tau = Module.finrank ℚ D.host.F := by
    rw [Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D), IsTotallyReal.finrank,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  have hP : 0 < ∏ i, t i := Finset.prod_pos fun i _ => ht i
  have habs : ((absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det α) : NNReal) : ℝ) =
      (∏ i, t i) ^ (2 * Module.finrank ℚ D.host.F) := by
    rw [absE_of_components _ _ hf hw, hcard, NNReal.coe_pow, NNReal.coe_pow, coe_nnnorm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hP, ← pow_mul]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod
  rw [habs, Finset.prod_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]
  congr 1
  push_cast
  ring

end GlobalTheory.HalfModTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

section LA

variable {ι Q : Type} [AddCommGroup Q] [Module ℂ Q]

def IsStab (ρ : ι → Module.End ℂ Q) (N : Submodule ℂ Q) : Prop := ∀ i, ∀ x ∈ N, ρ i x ∈ N

def HoweCond (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : Prop :=
  (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ Q), StrictMono N → (∀ k, IsStab ρ (N k) ∧ C ≤ N k) → m ≤ L) ∧
  ∀ N N' : Submodule ℂ Q, IsStab ρ N → C ≤ N → N ≠ ⊤ → IsStab ρ N' → C ≤ N' → N' ≠ ⊤ → N ⊔ N' ≠ ⊤

def rad (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : Submodule ℂ Q :=
  sSup {N | IsStab ρ N ∧ C ≤ N ∧ N ≠ ⊤}

theorem isStab_rad (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : IsStab ρ (rad ρ C) := by
  intro i
  have h : rad ρ C ≤ (rad ρ C).comap (ρ i) := by
    refine sSup_le fun N hN => ?_
    intro x hx
    exact le_sSup hN (hN.1 i x hx)
  exact fun x hx => h hx

def radAct (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (i : ι) : Module.End ℂ (Q ⧸ rad ρ C) :=
  (rad ρ C).mapQ (rad ρ C) (ρ i) fun x hx => isStab_rad ρ C i x hx

theorem radAct_mk (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (i : ι) (x : Q) :
    radAct ρ C i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ i x) := rfl

end LA

section Fock

variable {D : D7}

def actT (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eS : D.what₂.Tau → ℚ) (τ : D.what₂.Tau)
    (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) : Module.End ℂ (PolF D X.rank M.rank) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ((frSgn ε A).ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) + ((eS τ : ℂ) * Y.trace) • 1

def actS (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eT : D.what₂.Tau → ℚ) (τ : D.what₂.Tau)
    (Z : Matrix (Fin M.rank) (Fin M.rank) ℂ) : Module.End ℂ (PolF D X.rank M.rank) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ((frSgn ε A).ε τ) (B.ε τ) ((A.fr τ * Z * (A.fr τ)⁻¹).map (starRingEnd ℂ)) -
    ((eT τ : ℂ) * Z.trace) • 1

def coinv (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eT : D.what₂.Tau → ℚ) : Submodule ℂ (PolF D X.rank M.rank) :=
  Submodule.span ℂ {P | ∃ τ, ∃ Z ∈ lieAt M τ, ∃ P₀, P = actS ε A B eT τ Z P₀}

abbrev LieIx (X : HSp D) : Type := {x : D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ // x.2 ∈ lieAt X x.1}

end Fock

section LALemmas

theorem isStab_sup {ι Q : Type} [AddCommGroup Q] [Module ℂ Q] {ρ : ι → Module.End ℂ Q} {N N' : Submodule ℂ Q}
    (h : IsStab ρ N) (h' : IsStab ρ N') : IsStab ρ (N ⊔ N') := by
  intro i x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem_sup (h i y hy) (h' i z hz)

theorem rad_ne_top : ∀ (ι Q : Type) [AddCommGroup Q] [Module ℂ Q] (ρ : ι → Module.End ℂ Q) (C N₀ : Submodule ℂ Q),
  GlobalTheory.RealQuot.HoweCond ρ C → GlobalTheory.RealQuot.IsStab ρ N₀ → C ≤ N₀ → N₀ ≠ ⊤ → GlobalTheory.RealQuot.rad ρ C ≠ ⊤ := by
  intro ι Q _ _ ρ C N₀ hH hs hC hne
  obtain ⟨⟨L, hL⟩, hsum⟩ := hH
  let S : Set (Submodule ℂ Q) := {N | IsStab ρ N ∧ C ≤ N ∧ N ≠ ⊤}
  have wf : WellFounded (fun x y : S => y.1 < x.1) := by
    refine ⟨fun x => ?_⟩
    by_contra hx
    obtain ⟨f, -, hf⟩ := not_acc_iff_exists_descending_chain.1 hx
    have mono : StrictMono fun n => (f n).1 := strictMono_nat_of_lt_succ hf
    have := hL (L + 1) (fun k => (f k).1) (mono.comp Fin.val_strictMono) fun k => ⟨(f k).2.1, (f k).2.2.1⟩
    omega
  obtain ⟨M, -, hM⟩ := wf.has_min Set.univ ⟨⟨N₀, hs, hC, hne⟩, trivial⟩
  have hmax : ∀ N ∈ S, N ≤ M.1 := by
    intro N hN
    have hs' : M.1 ⊔ N ∈ S := ⟨isStab_sup M.2.1 hN.1, le_sup_of_le_left M.2.2.1,
      hsum _ _ M.2.1 M.2.2.1 M.2.2.2 hN.1 hN.2.1 hN.2.2⟩
    by_contra h
    exact hM ⟨_, hs'⟩ trivial (lt_of_le_of_ne le_sup_left fun e => h (e ▸ le_sup_right))
  have e : rad ρ C = M.1 := le_antisymm (sSup_le hmax) (le_sSup M.2)
  rw [e]
  exact M.2.2.2

theorem rad_le_ker : ∀ (ι Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (β : Q →ₗ[ℂ] Pi),
  (∀ i, β ∘ₗ ρ i = σ i ∘ₗ β) → C ≤ LinearMap.ker β → GlobalTheory.RealQuot.rad ρ C ≠ ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker β := by
  intro ι Q Pi _ _ _ _ ρ C σ β hi hk hrad hss
  by_contra hne
  have hKs : IsStab ρ (LinearMap.ker β) := fun i x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply, hx, map_zero]
  have hK : LinearMap.ker β ≠ ⊤ := fun h => hne (h ▸ le_top)
  have hTs : IsStab σ ((rad ρ C).map β) := by
    rintro i _ ⟨x, hx, rfl⟩
    exact ⟨ρ i x, isStab_rad ρ C i x hx, by rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply]⟩
  obtain ⟨N', hN's, hc⟩ := hss _ hTs
  have hUs : IsStab ρ (N'.comap β) := fun i x hx => by
    show β (ρ i x) ∈ N'
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply]
    exact hN's i _ hx
  have hCU : C ≤ N'.comap β := fun x hx => by
    show β x ∈ N'
    rw [LinearMap.mem_ker.1 (hk hx)]
    exact N'.zero_mem
  have hsup : rad ρ C ⊔ N'.comap β = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : β x ∈ (rad ρ C).map β ⊔ N' := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨t, ht, n, hn, htn⟩ := Submodule.mem_sup.1 h1
    obtain ⟨r, hr, rfl⟩ := ht
    have h2 : x - r ∈ N'.comap β := by
      show β (x - r) ∈ N'
      rw [map_sub, ← htn, add_sub_cancel_left]
      exact hn
    have h3 := Submodule.add_mem_sup hr h2
    rwa [add_sub_cancel] at h3
  by_cases hU : N'.comap β = ⊤
  · apply hne
    intro x hx
    have h1 : β x ∈ (rad ρ C).map β := ⟨x, hx, rfl⟩
    have h2 : β x ∈ N' := by
      have : x ∈ N'.comap β := hU ▸ Submodule.mem_top
      exact this
    have h3 : β x ∈ (rad ρ C).map β ⊓ N' := Submodule.mem_inf.2 ⟨h1, h2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h3
    exact h3
  · exact hrad (eq_top_iff.2 (hsup ▸ sup_le le_rfl (le_sSup ⟨hUs, hCU, hU⟩)))

end LALemmas

theorem hasInfExp_div : ∀ (D : D7) (α β : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a b : ℚ), HasInfExp D α τ a → HasInfExp D β τ b →
  HasInfExp D (β / α) τ (b - a) := by
  intro D α β τ a b hA hB
  obtain ⟨m, hm, ex, hα⟩ := hA
  obtain ⟨n, hn, -, hβ⟩ := hB
  refine ⟨n - m, by push_cast; rw [hm, hn]; ring, ex, fun θ hθ x h1 h2 => ?_⟩
  have eα := hα θ hθ x h1 h2
  have eβ := hβ θ hθ x h1 h2
  set w : ℂ := θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) with hw
  have hdiv : (((β / α) x : Circle) : ℂ) = ((β x : Circle) : ℂ) / ((α x : Circle) : ℂ) := by
    rw [MonoidHom.div_apply, Circle.coe_div]
  rw [hdiv, eα, eβ]
  rcases eq_or_ne w 0 with h0 | h0
  · have hm0 : m = 0 := by
      by_contra hm0
      have := eα
      rw [h0, _root_.zero_zpow _ hm0] at this
      exact Circle.coe_ne_zero _ this
    have hn0 : n = 0 := by
      by_contra hn0
      have := eβ
      rw [h0, _root_.zero_zpow _ hn0] at this
      exact Circle.coe_ne_zero _ this
    subst hm0 hn0
    simp
  · rw [zpow_sub₀ h0]

end GlobalTheory.RealQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorConvolutionAndLeftTranslateStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_convolution_and_leftTranslate : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth σ → ∀ f ∈ GlobalTheory.SplitWeil.SB G, ∀ f' ∈ GlobalTheory.SplitWeil.SB G, ∀ A B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f A → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f' B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (conv μ f f') (A ∘ₗ B) ∧ ∀ g : G, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (fun x => f' (g⁻¹ * x)) (σ g ∘ₗ B) := by
  first | exact @GlobalTheory.OpConv.isIntegralOp_conv_and_translate | exact GlobalTheory.OpConv.isIntegralOp_conv_and_translate | (intros; apply GlobalTheory.OpConv.isIntegralOp_conv_and_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianWittIndexLeNegativeSignature
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.WittSig

open Matrix
open scoped ComplexOrder

theorem cT_conj_eq {m k : Type} (M : Matrix m k ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, conjTranspose_apply]

theorem Jpq_conjTranspose (q p : ℕ) : (Formalism.UG.Jpq q p)ᴴ = Formalism.UG.Jpq q p := by
  simp [Formalism.UG.Jpq, fromBlocks_conjTranspose]

theorem le_of_isotropic {n : Type} [Fintype n] [DecidableEq n] {q p r : ℕ} (J : Matrix n n ℂ)
    (hS : Formalism.UG.HasSignature J q p) (X Y : Matrix n (Fin r) ℂ) (hxx : Xᴴ * J * X = 0)
    (hxy : Xᴴ * J * Y = 1) : r ≤ p := by
  obtain ⟨e, P, hP⟩ := hS
  rw [cT_conj_eq] at hP
  set Q : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ := (↑(P⁻¹) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) with hQdef
  have hPQ : (P : Matrix _ _ ℂ) * Q = 1 := by simp [Q]
  have hJ : J.reindex e e = Qᴴ * Formalism.UG.Jpq q p * Q := by
    rw [← hP]
    have h1 : Qᴴ * (P : Matrix _ _ ℂ)ᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
    calc J.reindex e e = (Qᴴ * (P : Matrix _ _ ℂ)ᴴ) * J.reindex e e * ((P : Matrix _ _ ℂ) * Q) := by
          rw [h1, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  set Z := Q * X.reindex e (Equiv.refl _) with hZdef
  set W := Q * Y.reindex e (Equiv.refl _) with hWdef
  have key : ∀ A B : Matrix n (Fin r) ℂ,
      (Q * A.reindex e (Equiv.refl _))ᴴ * Formalism.UG.Jpq q p * (Q * B.reindex e (Equiv.refl _)) = Aᴴ * J * B := by
    intro A B
    have : (Q * A.reindex e (Equiv.refl _))ᴴ * Formalism.UG.Jpq q p * (Q * B.reindex e (Equiv.refl _)) =
        (A.reindex e (Equiv.refl _))ᴴ * (Qᴴ * Formalism.UG.Jpq q p * Q) * B.reindex e (Equiv.refl _) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, ← hJ]
    ext i j
    simp [Matrix.mul_apply, Matrix.reindex_apply, conjTranspose_apply]
    rw [← Fintype.sum_sum_type (fun x => (∑ k, (starRingEnd ℂ) (A k i) * J k (e.symm x)) * B (e.symm x) j)]
    exact e.symm.sum_comp (fun x => (∑ k, (starRingEnd ℂ) (A k i) * J k x) * B x j)
  have hZZ : Zᴴ * Formalism.UG.Jpq q p * Z = 0 := by rw [hZdef, key, hxx]
  have hWZ : Wᴴ * Formalism.UG.Jpq q p * Z = 1 := by
    have h := key X Y
    rw [hxy, ← hZdef, ← hWdef] at h
    have h2 := congrArg conjTranspose h
    simpa [conjTranspose_mul, Jpq_conjTranspose, Matrix.mul_assoc] using h2
  let L : (Fin r → ℂ) →ₗ[ℂ] (Fin p → ℂ) := (Z.submatrix Sum.inr id).mulVecLin
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    set u := Z *ᵥ c with hu
    have hlow : ∀ i, u (Sum.inr i) = 0 := fun i => by
      have := congrFun hc i
      simpa [L, u, mulVec, dotProduct, submatrix] using this
    have h0 : star u ⬝ᵥ (Formalism.UG.Jpq q p *ᵥ u) = 0 := by
      have : star c ⬝ᵥ ((Zᴴ * Formalism.UG.Jpq q p * Z) *ᵥ c) = 0 := by rw [hZZ]; simp
      rw [← this, hu, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    have hup : (fun i => u (Sum.inl i)) = 0 := by
      rw [← dotProduct_star_self_eq_zero, ← h0]
      simp [Formalism.UG.Jpq, dotProduct, mulVec, Fintype.sum_sum_type, hlow, Matrix.one_apply]
    have hu0 : u = 0 := by
      funext x
      rcases x with i | i
      · exact congrFun hup i
      · exact hlow i
    calc c = (Wᴴ * Formalism.UG.Jpq q p * Z) *ᵥ c := by rw [hWZ, one_mulVec]
      _ = (Wᴴ * Formalism.UG.Jpq q p) *ᵥ u := by rw [hu, mulVec_mulVec]
      _ = 0 := by rw [hu0, mulVec_zero]
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

theorem wittIndex_le_neg {D : D7} (M : HSp D) {p : ℕ} {τ : D.what₂.Tau}
    (hS : Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) {r : ℕ}
    {Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E}
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf) : r ≤ p := by
  have hc := (GlobalTheory.AdelicU.isCMExt_host D).2.2.2 (tauE D τ)
  have hmap : ∀ {a b : ℕ} (A : Matrix (Fin M.rank) (Fin a) D.host.E)
      (B : Matrix (Fin M.rank) (Fin b) D.host.E),
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * M.gram * B).map (tauE D τ) =
        (A.map (tauE D τ))ᴴ * gramAt D M τ * B.map (tauE D τ) := by
    intro a b A B
    rw [Matrix.map_mul, Matrix.map_mul, gramAt]
    congr 2
    ext i j
    simp [Formalism.UG.cT, conjTranspose_apply, hc]
  apply le_of_isotropic (gramAt D M τ) hS (Xf.map (tauE D τ)) (Yf.map (tauE D τ))
  · rw [← hmap, hW.xx, Matrix.map_zero _ (map_zero _)]
  · rw [← hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.WittSig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwiseStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitePart_act_discreteSeriesHom_factorwise : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H), ∀ Φ ∈ homDS M ρ U, ∀ (g : GA D V) y, ρ (toInf V g : GA D V) (Φ y) = Φ fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  first | exact @GlobalTheory.TrAct.toInf_apply_homDS | exact GlobalTheory.TrAct.toInf_apply_homDS | (intros; apply GlobalTheory.TrAct.toInf_apply_homDS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitesimalCharacterFactorStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_character_factor : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε π → (∀ v, IsKFin ε π v → Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => π g v)) → ∀ χ : Fin n → ℂ, HasInfChar ε χ π → ∀ I : IndModule ε, I.Positive → ∀ Z, IsFactor ε I.ρ Z (kFinVec ε I.ρ) π → (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) := by
  first | exact @GlobalTheory.StdInfChar.genInfChar_of_isFactor | exact GlobalTheory.StdInfChar.genInfChar_of_isFactor | (intros; apply GlobalTheory.StdInfChar.genInfChar_of_isFactor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFiniteIndicatorSmulArchFunctionStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_finiteIndicator_smul_archFunction : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (B : Set (GFin D.sp.cm.sig V.gram)), MeasurableSet B → νF B ≠ ⊤ → ∀ (a : (∀ w, GArch D.sp.cm.sig V.gram w) → E), Integrable a (Measure.pi μa) → Integrable (fun g : GA D V => B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a fun w => projArch D.sp.cm.sig V.gram w g) μ ∧ ∫ g, B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a (fun w => projArch D.sp.cm.sig V.gram w g) ∂μ = (νF B).toReal • ∫ x, a x ∂Measure.pi μa := by
  first | exact @GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch | exact GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch | (intros; apply GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviElementExistsStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_levi_element_exists : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (α : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), (∀ i j, α.1 i j ∈ intLoc D.host.F D.host.E v) → (∀ i j, (α⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) → ∃ m : GLoc D.sp.cm.sig V.gram v, m ∈ stabLoc D.sp.cm.sig V.gram L v ∧ (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram m).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * α.1 := by
  first | exact @GlobalTheory.LeviIntegral.exists_stabLoc_mul_frame_of_isGood | exact GlobalTheory.LeviIntegral.exists_stabLoc_mul_frame_of_isGood | (intros; apply GlobalTheory.LeviIntegral.exists_stabLoc_mul_frame_of_isGood <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicFormMultMapValueStatement
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicForm_multMap_value : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : MMap M) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → (∀ v, Continuous (T v) ∧ (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, T v (g * k) = T v g) ∧ T v ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T v) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)) → (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) → ∀ v, IsAutFunSm θ V (T v) := by
  first | exact @GlobalTheory.EquivValues.isAutFunSm | exact GlobalTheory.EquivValues.isAutFunSm | (intros; apply GlobalTheory.EquivValues.isAutFunSm <;> assumption)
end

