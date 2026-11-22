import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0623
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescription
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0621
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalFunctionalEquationH1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsRestrictOpenBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section
namespace GlobalTheory.CompanionTheory.FormOpen

variable {K : Type} [CommRing K]

theorem mOm_bijective {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    {φ : A →+* B} (hφ : SemiHom (RingHom.id K) φ) (hb : Function.Bijective φ) (j : ℕ) :
    Function.Bijective (hφ.mOm j) := by
  let e : A ≃+* B := RingEquiv.ofBijective φ hb
  have he : ∀ a, e a = φ a := fun _ ↦ rfl
  have hψ : SemiHom (RingHom.id K) (e.symm : B →+* A) := fun r b ↦ by
    apply e.injective
    change e (e.symm (r • b)) = e (RingHom.id K r • e.symm b)
    rw [RingEquiv.apply_symm_apply, he, RingHom.id_apply, show φ (r • e.symm b) = _ from hφ r _,
      ← he, RingEquiv.apply_symm_apply, RingHom.id_apply]
  have hA : SemiHom (RingHom.id K) (RingHom.id A) := fun _ _ ↦ rfl
  have hB : SemiHom (RingHom.id K) (RingHom.id B) := fun _ _ ↦ rfl
  have l : Function.LeftInverse (hψ.mOm j) (hφ.mOm j) := fun x ↦
    (SemiHom.mOm_mOm (ρ := RingHom.id K) hφ hψ hA (fun a ↦ e.symm_apply_apply a) x).trans
      (hA.mOm_id (fun _ ↦ rfl) x)
  have r : Function.RightInverse (hψ.mOm j) (hφ.mOm j) := fun x ↦
    (SemiHom.mOm_mOm (ρ := RingHom.id K) hψ hφ hB (fun a ↦ e.apply_symm_apply a) x).trans
      (hB.mOm_id (fun _ ↦ rfl) x)
  exact ⟨l.injective, r.surjective⟩

variable {X : Scheme.{0}}

theorem app_map_eq (V : X.Opens) (h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.app V ≫ V.toScheme.presheaf.map (homOfLE h).op = V.topIso.inv := by
  simp only [Scheme.Opens.topIso, Scheme.Opens.ι_app, Scheme.Opens.toScheme_presheaf_map,
    Iso.op_inv, Functor.mapIso_inv, eqToIso.inv, ← Functor.map_comp, ← op_comp]
  rfl

theorem res_appSec_bijective (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens)
    (h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    Function.Bijective ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp
      (appSec q (V.ι ≫ q) V.ι V)) := by
  have e : ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp (appSec q (V.ι ≫ q) V.ι V) :
      Sec q V → Sec (V.ι ≫ q) ⊤) = V.topIso.inv.hom := by
    rw [← app_map_eq V h]; rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso V.topIso.inv

theorem formRes_formPull_open_bijective {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ) :
    Function.Bijective fun x : OmU q V a => formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V by simp) a
      (formPull (f := V.ι) rfl V a x) := by
  have h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have hγ : SemiHom (RingHom.id K) ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp
      (appSec q (V.ι ≫ q) V.ι V)) :=
    (semiHom_appSec rfl V).comp (SemiHom.of_algHom (Sec.res (V.ι ≫ q) h))
  have e : (fun x : OmU q V a => formRes (V.ι ≫ q) h a (formPull (f := V.ι) rfl V a x)) =
      hγ.mOm a := funext fun x ↦
    SemiHom.mOm_mOm (semiHom_appSec rfl V) (SemiHom.of_algHom (Sec.res (V.ι ≫ q) h)) hγ
      (fun _ ↦ rfl) x
  rw [e]
  exact mOm_bijective hγ (res_appSec_bijective q V h) a

end GlobalTheory.CompanionTheory.FormOpen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescriptionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_description : Ad3.R.D0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | exact GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvarianceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_integral_central_invariance : Ad3.R.G1a := by
  first | exact @GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts | exact GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts | (intros; apply GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescriptionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_invariance_of_description : Ad3.R.D0 → Ad3.R.G0 := by
  first | exact @GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain | exact GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain | (intros; apply GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G0
section
noncomputable section

open MeasureTheory
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.PuBnd

def Wt (N : ℕ) (h : M22) (x : Fin 2 → ℝ) : ℝ :=
  1 / (1 + ‖h‖ + |h 0 0 * x 0 + h 0 1 * x 1| + |h 1 0 * x 0 + h 1 1 * x 1|) ^ N

def Ew (k : ℕ) (D R : ℝ) : ℝ :=
  (|D| / R) ^ ((2 * (k : ℝ) - 1) / 2) * Real.exp (-(2 * Real.pi * |D| / R))

def V (k : ℕ) (σ T : ℝ) : ℝ := |T| ^ ((k : ℝ) - 1 - σ) * Real.exp (-(Real.pi * |T|))

def G0 (k : ℕ) (σ a b c d : ℝ) : ℝ :=
  |a| ^ (-2 - σ) / ((1 + |a|) ^ 2 * (1 + |b|) ^ 2) * V k σ ((d - c * b / a) / a)

def Gi (k : ℕ) (σ : ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  if |q.2.1| ≤ |q.1.1| then G0 k σ q.1.1 q.1.2 q.2.1 q.2.2 else 0

end GlobalTheory.CompanionTheory.PuBnd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G8FiniteAuxiliaryStatement
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.RegroupFin

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem map_phiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  simp [PhiU, GlobalTheory.Tw.Phi, GeneralLinearGroup.map, apply_ite f]

theorem map_thetaGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaGL n c g) = thetaGL n c' (GeneralLinearGroup.map f g) := by
  have h1 : ∀ x : GL (Fin n) R, GeneralLinearGroup.map f (invT n R x) = invT n S (GeneralLinearGroup.map f x) := by
    intro x
    apply Units.ext
    ext i j
    have e : (GeneralLinearGroup.map f x)⁻¹ = GeneralLinearGroup.map f x⁻¹ := (map_inv _ x).symm
    simp only [invT, MonoidHom.coe_mk, OneHom.coe_mk, e]
    rfl
  have h2 : GeneralLinearGroup.map f (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map f g) := by
    apply Units.ext
    ext i j
    exact h _
  have h3 : ∀ (T : Type) [CommRing T] (d : T →+* T) (x : GL (Fin n) T),
      thetaGL n d x = PhiU n T * invT n T (GeneralLinearGroup.map d x) * (PhiU n T)⁻¹ := fun _ _ _ _ => rfl
  rw [h3, h3, map_mul, map_mul, map_inv, map_phiU, h1, h2]

theorem evw_pv (v : PlF E) (w : Above v) (y : Gf E a b) : evw w (pv a b v y) = atW w.1 y := by
  refine Prod.ext ?_ ?_ <;> · apply Units.ext; ext i j; rfl

theorem cjv_spec (hc : CjEx) (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cjv v (projv v x) := by
  have h := hc E v
  unfold cjv
  rw [dif_pos h]
  exact h.choose_spec.2 x

theorem pv_thP (hc : CjEx) (v : PlF E) (y : Gf E a b) : pv a b v (thP E a b y) = thv a b v (pv a b v y) :=
  Prod.ext (map_thetaGL (projv v) _ (cjv v) (cjv_spec hc v) a y.1) (map_thetaGL (projv v) _ (cjv v) (cjv_spec hc v) b y.2)

theorem finprod_fibres {X Y : Type} (u : X → Y) (S : Set X) (hu : Set.InjOn u S) (F : X → ℂ) :
    ∏ᶠ w ∈ S, F w = ∏ᶠ v : Y, ∏ᶠ (w : {w : X // u w = v}) (_ : w.1 ∈ S), F w.1 := by
  set G : Y → ℂ := fun v => ∏ᶠ (w : {w : X // u w = v}) (_ : w.1 ∈ S), F w.1 with hG
  have hone : ∀ v, v ∉ u '' S → G v = 1 := by
    intro v hv
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    have hw : w.1 ∉ S := fun hw => hv ⟨w.1, hw, w.2⟩
    simp [hw]
  have hval : ∀ w ∈ S, G (u w) = F w := by
    intro w hw
    have hs : {i : {x : X // u x = u w} | i.1 ∈ S} = {⟨w, rfl⟩} := by
      ext i
      change i.1 ∈ S ↔ i = ⟨w, rfl⟩
      constructor
      · intro hi
        exact Subtype.ext (hu hi hw i.2)
      · rintro rfl
        exact hw
    have : G (u w) = ∏ᶠ i ∈ {i : {x : X // u x = u w} | i.1 ∈ S}, F i.1 := rfl
    rw [this, hs, finprod_mem_singleton]
  have h1 : ∏ᶠ v, G v = ∏ᶠ v ∈ u '' S, G v := by
    rw [← finprod_mem_univ]
    refine finprod_mem_inter_mulSupport_eq' _ _ _ fun v hv => ?_
    simp only [Set.mem_univ, true_iff]
    by_contra hn
    exact hv (hone v hn)
  rw [h1, finprod_mem_image hu]
  exact (finprod_mem_congr rfl hval).symm

theorem regroup_of_cjEx (hc : CjEx) : Regroup := by
  intro E _ _ _ a b S hS φ₁ φ₂ _ _ y
  have hinj : Set.InjOn (fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))) S := by
    intro u hu u' hu' h
    obtain ⟨x, -, hx⟩ := hS u
    exact (hx u ⟨hu, rfl⟩).trans (hx u' ⟨hu', h.symm⟩).symm
  unfold finFn
  rw [finprod_fibres _ S hinj]
  refine finprod_congr fun v => ?_
  unfold fv
  refine finprod_congr fun w => finprod_congr fun _ => ?_
  rw [evw_pv, ← pv_thP hc, evw_pv]

theorem regroup : Regroup := regroup_of_cjEx GlobalTheory.CompanionTheory.CjEx.cjEx

end GlobalTheory.CompanionTheory.RegroupFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GauIntegrable
section
noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval

def cat (A : M22) (y : Fin 2 → ℝ) : M23 := fun r => ![A r 0, A r 1, y r]

def fz (Φ : Sw) (A : M22) (ξ : Fin 2 → ℝ) : ℂ :=
  ∫ y : Fin 2 → ℝ, Φ (cat A y) * Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))

def gz (Φ : Sw) (h : M22) (ζ : ℝ) : ℂ :=
  ∫ z : Fin 2 → ℝ, Φ (Matrix.of.symm (Matrix.of h * blk z)) *
    Complex.exp (2 * Real.pi * Complex.I * ((ζ * z 0 + z 1 : ℝ) : ℂ))

def dualF (h : M22) (ζ : ℝ) : Fin 2 → ℝ :=
  ![(h 1 1 * ζ - h 1 0) / (Matrix.of h).det, (h 0 0 - h 0 1 * ζ) / (Matrix.of h).det]

def gau (ε ζ : ℝ) : ℝ := ε⁻¹ * Real.exp (-Real.pi * ζ ^ 2 / ε ^ 2)

def wt (a l ζ : ℝ) : ℝ := ((1 + |ζ - l| / a) ^ 2)⁻¹

lemma wt_nonneg (a l ζ : ℝ) : 0 ≤ wt a l ζ := inv_nonneg.2 (sq_nonneg _)

lemma gau_nonneg (ε ζ : ℝ) (hε : 0 < ε) : 0 ≤ gau ε ζ :=
  mul_nonneg (inv_nonneg.2 hε.le) (Real.exp_pos _).le

lemma gau_eq (ε ζ : ℝ) : gau ε ζ = ε⁻¹ * Real.exp (-(Real.pi / ε ^ 2) * ζ ^ 2) := by
  unfold gau; congr 2; ring

lemma gau_integrable (ε : ℝ) (hε : 0 < ε) : Integrable (gau ε) := by
  have : gau ε = fun ζ => ε⁻¹ * Real.exp (-(Real.pi / ε ^ 2) * ζ ^ 2) := funext (gau_eq ε)
  rw [this]
  exact (integrable_exp_neg_mul_sq (by positivity)).const_mul _

lemma gau_integral (ε : ℝ) (hε : 0 < ε) : ∫ ζ, gau ε ζ = 1 := by
  have : gau ε = fun ζ => ε⁻¹ * Real.exp (-(Real.pi / ε ^ 2) * ζ ^ 2) := funext (gau_eq ε)
  rw [this, integral_const_mul, integral_gaussian]
  have : Real.pi / (Real.pi / ε ^ 2) = ε ^ 2 := by
    field_simp
  rw [this, Real.sqrt_sq hε.le]
  field_simp

end GlobalTheory.CompanionTheory.Parseval
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianSchwartzBruhatStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_schwartz_bruhat : Ad3.R.GS := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists | exact GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSubquotientIffWhittakerQuotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_subquotient_iff_whittaker_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ A B : Subrepresentation ρ, B ≤ A → (IsGenericFor ψ (subQuot A B) ↔ ¬ A.toSubmodule ≤ B.toSubmodule ⊔ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff | exact GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff | (intros; apply GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricSumBelowThresholdStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_sum_below_threshold : ∀ (q s Y : ℝ), 1 < q → 0 < s → 0 < Y → (∑' n : ℤ, (if q ^ n ≤ Y then ENNReal.ofReal (q ^ (s * (n : ℝ))) else 0)) ≤ ENNReal.ofReal (Y ^ s / (1 - q ^ (-s))) := by
  first | exact @GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div | exact GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div | (intros; apply GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalFunctionalEquationH1Statement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_functional_equation_h1 : Ad3.R.B0 → Ad3.R.E2 → Ad3.R.H1 := by
  first | exact @GlobalTheory.CompanionTheory.HeckePartial.partial_functional_equation | exact GlobalTheory.CompanionTheory.HeckePartial.partial_functional_equation | (intros; apply GlobalTheory.CompanionTheory.HeckePartial.partial_functional_equation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFactsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_rankin_selberg_basic_facts : Ad3.R.B0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinQ.b0 | exact GlobalTheory.CompanionTheory.RankinQ.b0 | (intros; apply GlobalTheory.CompanionTheory.RankinQ.b0 <;> assumption)
end

