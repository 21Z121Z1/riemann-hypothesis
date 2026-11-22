import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.AlgebraMapArcSInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0067
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceFormIndependence
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormAnOnOrbit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobi
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicIndexSums
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FourierJacobiCoeffLinearBoundedSectionsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFunctionalFiniteIntegralityBound
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

section Lines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {c : Coeff l} {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
  {a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)} {th : a.D₀.P.L.Sec}
  {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {jj : ℤ} {n' : ℕ} {La c₁ : ℝ}

theorem CMIn.fin_Tl_ne_zero (s : CMIn a e th jj n' La c₁) : s.Tl.I ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := s.good
  exact h.1

theorem CMIn.fin_line_ne_zero (s : CMIn a e th jj n' La c₁) (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) :
    (s.line τ k).I ≠ 0 := by
  letI := H.starRing
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := s.good
  unfold CMIn.line
  cases s.kind τ k with
  | none => exact one_ne_zero
  | some m =>
    have h := s.L_good.2.2.2 m
    show (s.L.ℓ m).I ≠ 0
    revert h
    cases s.L.src m with
    | inl q => intro h; rw [show s.L.ℓ m = _ from h]; exact (h1 q.2).1.1
    | inr q => intro h; rw [show s.L.ℓ m = _ from h]; exact (h2 q.2).1.1

theorem CMIn.fin_count_valLine (s : CMIn a e th jj n' La c₁) (mo : ArcLt Dw →₀ ℕ) (n : ℕ)
    (w : HeightOneSpectrum (𝓞 K₁)) :
    FractionalIdeal.count K₁ w (s.valLine mo n).I =
      (n : ℤ) * (-FractionalIdeal.count K₁ w s.Tl.I) +
        ∑ x ∈ mo.support, (mo x : ℤ) * (-FractionalIdeal.count K₁ w (s.line x.1 x.2.2).I) := by
  classical
  have hT := s.fin_Tl_ne_zero
  have hL : ∀ v : ArcLt Dw, (s.line v.1 v.2.2).I ^ mo v ≠ 0 := fun v => pow_ne_zero _ (s.fin_line_ne_zero _ _)
  show FractionalIdeal.count K₁ w ((s.Tl.I⁻¹) ^ n * (∏ v : ArcLt Dw, (s.line v.1 v.2.2).I ^ mo v)⁻¹) = _
  rw [FractionalIdeal.count_mul K₁ w (pow_ne_zero _ (inv_ne_zero hT))
      (inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hL v)),
    FractionalIdeal.count_pow, FractionalIdeal.count_inv, FractionalIdeal.count_inv,
    FractionalIdeal.count_prod K₁ w _ _ (fun v _ => hL v)]
  congr 1
  rw [← Finset.sum_neg_distrib]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_) |>.trans ?_
  · rw [Finsupp.notMem_support_iff.mp hx]; simp
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [FractionalIdeal.count_pow]; ring

end Lines

theorem cfOf_fin_bound : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁), ModelsAt Xo c → Std d → 1 ≤ La → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ intAt Xo c a' n la, cfOf d.yF d.μ d.jj F ≠ 0 → -((w.asIdeal.ramificationIdx (𝓞 c.F) : ℝ) * beOf E n' (absA Dw a') la) ≤ (ordAt w (cfOf d.yF d.μ d.jj F) : ℝ) - (FractionalIdeal.count K₁ w (s.valLine d.μ n).I : ℝ) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s hM hS _ la w hlw a' n F hF hne
  obtain ⟨Z, gm, lam, A, Bm, ⟨hg0, hg⟩, hlam, ⟨hAB, hA⟩, hbd⟩ :=
    GlobalTheory.T.localArcIntegrality_of_cmNormalisedTrivialisation hK E H Dw l Xo c K₁ d n' La c₁ s hM hS la w hlw a' n
  obtain ⟨P, hPe, hPh⟩ := GlobalTheory.ArcQ.evR_arc_isHomogeneous hK.laws hK.laws2 E H Dw l Xo c (hK.ev E H Dw l Xo c)
    K₁ d a' n F hF.1
  set m : ℕ := w.asIdeal.ramificationIdx (𝓞 c.F) * mOf E n' la with hm
  have hC1 : (1 : ℝ) ≤ Z.r ^ (-(m : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact (one_le_inv₀ (pow_pos Z.r_pos _)).mpr (pow_le_one₀ Z.r_pos.le Z.r_lt.le)
  have hbd' := hbd F hF
  rw [← hPe, FinPf.arcNum_algebraMap] at hbd'
  have key := FinKey.coeff_bound finCore_holds basisChange_holds (GlobalTheory.ArcQ.FinSite.«ι» Z) Z.K₀ Z.res Z.S Z.S_disc Z.S_dense
    Z.S_units P (absA Dw a') hPh n gm hg0 lam (fun τ k => (hlam τ k).1) A Bm hAB _ hC1 hA hbd' d.μ d.jj
  have hcf : cfOf d.yF d.μ d.jj F = (P.coeff d.μ).coeff d.jj := by
    rw [cfOf, ← hPe, FinPf.arcNum_algebraMap]
  rw [hcf] at hne ⊢
  rw [GlobalTheory.ArcQ.FinSite.«norm_ι» Z _ hne, hg] at key
  simp only [Finsupp.prod, (hlam _ _).2] at key
  have hz := FinPf.zpow_bound Z.r Z.r_pos Z.r_lt _ _ n (absA Dw a') m d.μ.support d.μ
    (fun x => -FractionalIdeal.count K₁ w (s.line x.1 x.2.2).I) key
  rw [s.fin_count_valLine]
  simp only [beOf, hm] at hz ⊢
  push_cast at hz ⊢
  nlinarith [hz]

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcFunctionalVanishesLowFourierJacobi
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcKill

theorem eq_zero_of_eval_off {σ : Type} {P Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0)
    (h : ∀ x, MvPolynomial.eval x Q ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have : P * Q = 0 := MvPolynomial.funext fun x => by
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x Q = 0
    · rw [hx, mul_zero]
    · rw [h x hx, zero_mul]
  exact (mul_eq_zero.1 this).resolve_right hQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem coeff_eq_zero_of_invBl (S : Finset (ArcLt Dw →₀ ℕ)) (f : (ArcLt Dw →₀ ℕ) → ℂ)
    (h : ∀ x : ArcLt Dw → ℂ, InvBl x → ∑ mo ∈ S, f mo * ∏ v ∈ mo.support, x v ^ mo v = 0) : ∀ mo ∈ S, f mo = 0 := by
  classical
  let Q : MvPolynomial (ArcLt Dw) ℂ := ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)).det
  have hQe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x Q ≠ 0 ↔ InvBl x := fun x => by
    rw [map_prod, Finset.prod_ne_zero_iff]
    refine forall_congr' fun τ => ?_
    have : (MvPolynomial.eval x).mapMatrix (Matrix.of fun i k : Fin (Dw.mult τ) =>
        (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)) =
        Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩ := by
      ext i k : 2
      simp
    rw [RingHom.map_det, this]
    simp
  have hone : InvBl (Dw := Dw) fun v => (1 : Matrix (Fin (Dw.mult v.1)) (Fin (Dw.mult v.1)) ℂ) v.2.1 v.2.2 :=
    fun τ => (Matrix.det_one (n := Fin (Dw.mult τ)) (R := ℂ)).trans_ne one_ne_zero
  have hQ : Q ≠ 0 := fun h0 => (hQe _).2 hone (by rw [h0, map_zero])
  have hP : ∑ mo ∈ S, MvPolynomial.monomial mo (f mo) = 0 := eq_zero_of_eval_off hQ fun x hx => by
    rw [map_sum, ← h x ((hQe x).1 hx)]
    exact Finset.sum_congr rfl fun mo _ => MvPolynomial.eval_monomial
  intro mo hmo
  have := congrArg (MvPolynomial.coeff mo) hP
  rw [MvPolynomial.coeff_sum] at this
  simpa [MvPolynomial.coeff_monomial, hmo] using this

theorem cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Fam n' La c₁ d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, (∀ k, rdU U F k ∈ (U.X k).SSgt (laU U a' n k) c₁) → cfOf d.yF d.μ d.jj F = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ em r U a' n hfam hgood hunf hdom htv F hF hS
  obtain ⟨⟨hover, -, hpush⟩, ⟨s⟩⟩ := hfam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hmain⟩ := GlobalTheory.T.arcDatum_sectionValue_coeff_eq_fourierJacobi hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5
    E H Dw l Xo c K₁ d em r U s.ξ s.ν₀ a' n (hK.ev E H Dw l Xo c) hgood hunf hover s.tan hpush s.rk s.ξ_ne s.beta
    hdom htv
  have hν : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    have h1 := TraceFormIndependence.trace_re (U.X k) s.ν₀
    have h2 := s.tr
    rw [h1, ← Finset.mul_sum] at h2
    linarith
  have h0 : ∀ x, InvBl x → ajAt d em F x = 0 := fun x hx => by
    have := hmain F hF (hS k).1.1 x hx
    rw [(hS k).2 ξ' hiso _ hν _ (hfr x hx), mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_right (zpow_ne_zero _ hu)
  unfold cfOf
  by_cases hmo : d.μ ∈ (arcNum (evR Xo c F d.yF)).support
  · exact (map_eq_zero em).1 (coeff_eq_zero_of_invBl _
      (fun mo => em (((arcNum (evR Xo c F d.yF)).coeff mo).coeff d.jj)) h0 _ hmo)
  · rw [MvPolynomial.notMem_support_iff.1 hmo]
    rfl

end GlobalTheory.ArcKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataAtSplitIsotropicPoint
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM.Exist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_lift_fibre {R R₂ K : Type} [CommRing R] [CommRing R₂] [Field K] {B : GlobalTheory.CM.PAT H (Sp R)}
    {B₂ : GlobalTheory.CM.PAT H (Sp R₂)} {j : R →+* R₂} (m : SABMap B₂.t B.t (spMap j)) {f : R →+* K} {f₂ : R₂ →+* K}
    (hf : f₂.comp j = f) {P : Out.PolAV (Sp K)} {ψ : P.A.left ⟶ B.pol.A.left} (hψ : IsPolFibre f B.pol P ψ)
    (act : 𝓞 E → (P.A ⟶ P.A)) (hact : ∀ x, (act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left) :
    ∃ ψ₂ : P.A.left ⟶ B₂.pol.A.left, IsPolFibre f₂ B₂.pol P ψ₂ ∧
      ∀ x, (act x).left ≫ ψ₂ = ψ₂ ≫ (B₂.t.act.act x).left := by
  have hs : spMap f₂ ≫ spMap j = spMap f := (GlobalTheory.ArcId.sp_comp _ _).trans (congrArg spMap hf)
  have w : ψ ≫ B.t.G.hom = (P.A.hom ≫ spMap f₂) ≫ spMap j :=
    hψ.2.1.1.w.trans (by rw [Category.assoc, hs])
  obtain ⟨ψ₂, h₁, h₂⟩ : ∃ ψ₂ : P.A.left ⟶ B₂.t.G.left, ψ₂ ≫ m.φ = ψ ∧ ψ₂ ≫ B₂.t.G.hom = P.A.hom ≫ spMap f₂ :=
    ⟨_, m.cart.1.lift_fst _ _ w, m.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback P.A B₂.t.G (spMap f₂) ψ₂ := m.cart.cancel (hψ.2.1.congr hs.symm h₁.symm) h₂
  refine ⟨ψ₂, ⟨?_, g₂, ?_⟩, fun x => ?_⟩
  · exact H1.dim_unique P.A.hom P.smoothDim
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback g₂.1 B₂.dim)
      (eSec P.A (IsLocalRing.closedPoint K))
  · have e : LBIso (B₂.t.PP.L.pull ψ₂) (B.t.PP.L.pull ψ) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) ψ₂ h₁.symm
    exact LBIso.trans (pull_isLB B₂.t.PP.isLB _) (pull_isLB B.t.PP.isLB _) P.isLB e hψ.2.2
  · apply m.cart.1.hom_ext
    · have e := m.act x
      change ((act x).left ≫ ψ₂) ≫ m.φ = (ψ₂ ≫ (B₂.t.act.act x).left) ≫ m.φ
      rw [Category.assoc, Category.assoc, h₁, hact, e, ← Category.assoc, h₁]
    · rw [Category.assoc, Category.assoc, h₂, Over.w (B₂.t.act.act x), h₂, ← Category.assoc, Over.w (act x)]

theorem one_le_of_isIso {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    {U : Unf Xo c σ r} (hU : IsUnf U) {k : U.Comp} {ξ' : Fin r → E} (hξ : (U.X k).IsIso ξ') :
    1 ≤ Dw.p ∧ 1 ≤ Dw.q := by
  obtain ⟨τ⟩ : Nonempty (U.X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ ∈ (U.X k).Ψ
    · exact ⟨⟨τ, h⟩⟩
    · exact ⟨⟨_, by_contra fun h' => h (((U.X k).cmType τ).2 h')⟩⟩
  have h := IsotropicIndexSums.isotropicIndex_bounds (U.X k) hξ.2.1 hξ.2.2 τ
  have h1 := hU.1
  have h2 := (hU.2.1 k).1
  omega

theorem exists_cmIn_tie : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La₀ La c₁ : ℝ) (lam : Fin (r - 2) → Fin r → E) (n' : ℕ) (ν₀ : E), IsUnf U → l.A = 1 → 3 ≤ r → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La₀ (hX ▸ x) lam → La₀ ^ 2 ≤ La ^ 2 → 0 < n' → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (em : K₁ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (s : CMIn a e th jj n' La c₁), em.comp (algebraMap c.F K₁) = c.F.val.toRingHom ∧ s.ν₀ = ν₀ ∧ Comparison₂ Uw a em s.ξ k ξ' x := by
  intro hK E _ _ _ H Dw l Xo c _ _ r U Uw k ξ' x Xx hX 𝔄 La₀ La c₁ lam n' ν₀ hU hA hr hξ hx h𝔄 hΛ hS hLa hn hap hν hν₀
    hint htr
  letI := H.starRing
  have hg : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨hp, hq⟩ := one_le_of_isIso hU hξ
  have hpq : 3 ≤ Dw.p + Dw.q := hU.1 ▸ hr
  obtain ⟨A, gam, ξ, jj, DB, tyB, eB, hO, hξ0, hrk, hdvd, hbeta, hprim, hct, hab, hDp, hDq⟩ :=
    GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating E H Dw l Xo c _ r U Uw k ξ' x n' ν₀ hg hU hξ hx hap hν hν₀ hint
  obtain ⟨A', gam', ξ₁, eX, hO', hprim', hnorm', hξ₁, hbe', hab'⟩ :=
    GlobalTheory.ArcShift.exists_normAn_onOrbit E H Dw l Xo c _ r U Uw k ξ' x n' hg hU hξ hx hn A gam ξ hO hξ0 hrk hprim hct
  obtain ⟨tyB', eB', hB'⟩ := hab' DB ⟨tyB, eB, hab⟩
  have hrk' : Module.finrank (𝓞 E) A'.X = 1 := eX.finrank_eq.trans hrk
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_cm_lattice_data_abelianPart_split_point E H Dw l Xo c _ r U Uw k ξ' x Xx hX 𝔄 La₀ lam hg hU hξ hx h𝔄 hΛ hS A' gam' ξ₁ DB
    tyB' eB' hO' hrk' hDp hDq hB'
  obtain ⟨K, _, _, _, σ₁, ρ, X, ex, hσ₁, hρ, hhh, hex⟩ :=
    GlobalTheory.ArcCM.exists_cmObj_of_period hK E H l c DB _ tyB' _ hB'.2.2.2.2 Z (by omega) hB'.2.1 hA
  obtain ⟨aC, Λ, hΛA, φ, hφ, hφa, hlift⟩ := GlobalTheory.T.exists_complexArcDatum_cmFibre hK E H Dw l Xo c _ r U Uw k ξ' x (𝓞 K) X.B _ hg hU hA A' gam'
    ξ₁ DB tyB' eB' ex hO' hrk' (fun y y' => (hbe' y y').symm ▸ hdvd _ _) hprim' hB' hDp hDq hp hq hex
  subst hΛA
  have htau : TauCan aC.D₀ n' := (GlobalTheory.KappaAn.tauCan_iff_normAn E H Dw l c _ _ _ aC Λ.toGtAn₀ n').2 hnorm'
  let fC : aC.D₀.X ≃ₗ[𝓞 E] A.X := Λ.eX.symm.trans eX
  let ξC : Module.Dual ℤ aC.D₀.X := ξ.comp (fC.toLinearMap.restrictScalars ℤ)
  have htie := GlobalTheory.T.holomorphicArc_matches_frame_of_model_on_orbit hK E H Dw l Xo c _ r U Uw k ξ' x aC Λ.toGtAn₀ ξC hg hU hξ hx hA gam' ξ₁ hO'
    (fun y => by rw [hξ₁]; exact congrArg (fun z => ξ (eX z)) (Λ.eX.symm_apply_apply y)) hlift
  obtain ⟨K₂, _, _, _, i, σ₂, a, p, ψ, hσ₂, hbc, htau₂, hψ, hψa⟩ :=
    GlobalTheory.T.exists_cmArcData_descent_numberField hK E H Dw l c K σ₁ _ X.B aC φ n' hσ₁ hn hφ hφa htau
  obtain ⟨ρ₂, X₂, m, hρ₂, hh₂⟩ := GlobalTheory.ArcCM.exists_cmObj_baseChange hK E H K ρ σ₁ _ _ X K₂ i σ₂ hσ₂
  obtain ⟨ψ₂, hψ₂, hψa₂⟩ := exists_lift_fibre m (f₂ := algebraMap (𝓞 K₂) K₂) (RingHom.ext fun _ => rfl) hψ
    a.oa.onB.act hψa
  let f : aC.D₀.X ≃ₗ[𝓞 E] a.D₀.X := { p.xe with map_smul' := hbc.2.1 }
  let g : a.D₀.X ≃ₗ[𝓞 E] A.X := f.symm.trans fC
  have hem : σ₂.comp (algebraMap c.F K₂) = c.F.val.toRingHom := by
    rw [← hσ₁, ← hσ₂]
    exact RingHom.ext fun y => congrArg σ₂ (i.commutes y).symm
  have hbe : ∀ y z, a.be y z = A.be (g y) (g z) := fun y z => by
    obtain ⟨y, rfl⟩ := (Λ.eX.trans f).surjective y
    obtain ⟨z, rfl⟩ := (Λ.eX.trans f).surjective z
    refine (hbc.2.2.1 _ _).symm.trans ((Λ.be_eq _ _).trans ((hbe' _ _).trans ?_))
    simp [g, fC]
  have hhh₂ : ∀ j (τ : E →+* ℂ), ‖τ (X₂.hh j : E)‖ ≤ La ^ 2 := fun j τ => by
    rw [hh₂, hhh]; exact (hZ j τ).trans hLa
  have hρ' : σ₂ (ρ₂ : K₂) = H.rt0 := by rw [hρ₂, ← hρ, ← hσ₂]; rfl
  clear m hh₂
  generalize DB.p = p₁, DB.q = q₁ at X₂ hDp hDq hhh₂ ψ₂ hψ₂ hψa₂
  subst hDp hDq
  obtain ⟨e, th, s, hs, hsν⟩ := GlobalTheory.ArcCM.Letters.exists_cmIn hK E H Dw l c K₂ a ρ₂ σ₂ X₂ ψ₂ n' La c₁
    (ξ.comp (g.toLinearMap.restrictScalars ℤ)) ν₀ jj hp hq hpq hem hρ' hhh₂ hψ₂ hψa₂ hn htau₂
    (g.finrank_eq.trans hrk)
    (fun h => hξ0 (LinearMap.ext fun y => by
      obtain ⟨y, rfl⟩ := g.surjective y
      exact LinearMap.congr_fun h y))
    (GlobalTheory.ArcId.betaAt_comp g ξ hbe hbeta) htr
  refine ⟨K₂, _, _, _, σ₂, a, e, th, jj, s, hem, hsν, aC, p, ξC, hbc, fun y => ?_, htie⟩
  rw [hs]
  exact congrArg (fun z => ξ (fC z)) (f.symm_apply_apply y).symm

end GlobalTheory.ArcCM.Exist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffNeZeroOfFourierJacobiArcDatumStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_ne_zero_of_fourierJacobi_arcDatum : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Std d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → Comparison₂ Uw d.a em s.ξ k ξ' x → ∀ F ∈ sec Xo c a' n, (∀ k', (U.X k').IsBddSec (laU U a' n k') (rdU U F k')) → (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U F k) x ≠ 0 → ∃ mo : ArcLt Dw →₀ ℕ, cfOf d.yF mo d.jj F ≠ 0 := by
  first | exact @GlobalTheory.DerivativeDetermination.exists_cfOf_ne_zero | exact GlobalTheory.DerivativeDetermination.exists_cfOf_ne_zero | (intros; apply GlobalTheory.DerivativeDetermination.exists_cfOf_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SumCmArcFunctionalVanishesLowFourierJacobi
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

namespace GlobalTheory.ArcKill

theorem sum_cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (ι.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (La c₁ : ℝ), GoodEmb c (ι.comp (algebraMap c.F K₁)) → IsUnf U → Fam n' La c₁ d → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c) (f : ∀ k : U.Comp, Frame (U.X k).Ψ r → ℂ), (∀ i, F i ∈ sec Xo c a' n) → (∀ i k, (U.X k).IsBddSec (laU U a' n k) (rdU U (F i) k)) → (∀ k, f k ∈ (U.X k).SSgt (laU U a' n k) c₁) → (∀ k, ∀ x ∈ (U.X k).dom, f k x = ∑ i, a i * rdU U (F i) k x) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d ι r U a' n n' La c₁ hG hU hFam hDom hT m a F f hF hB hf hfe
  obtain ⟨⟨hob, -, hpush⟩, ⟨s⟩⟩ := hFam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hid⟩ :=
    GlobalTheory.T.arcDatum_sectionValue_coeff_eq_fourierJacobi hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5 E H Dw l Xo c K₁ d ι r U s.ξ s.ν₀ a' n
      (hK.ev E H Dw l Xo c) hG hU hob s.tan hpush s.rk s.ξ_ne s.beta hDom hT
  refine GlobalTheory.T.coeff_eq_zero_of_vanish_on_invertibleLetterBlocks E H Dw l Xo c K₁ d ι m a F fun x hx => ?_
  have hlin := GlobalTheory.T.fourierJacobi_coeff_linear_bounded_sections E r (U.X k) (laU U a' n k) m a (fun i => rdU U (F i) k) (f k) (fun i => hB i k)
    (hfe k) ξ' hiso (fun τ => (τ.1 s.ν₀).re) (fr x) (hfr x hx)
  have htr : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    rw [GlobalTheory.sum_re_cmType_eq_half_trace E r (U.X k) s.ν₀]
    exact s.tr
  have h0 := (hf k).2 ξ' hiso (fun τ => (τ.1 s.ν₀).re) htr (fr x) (hfr x hx)
  have hz : u₁ ^ d.jj ≠ 0 := zpow_ne_zero _ hu
  refine (mul_eq_zero.mp ?_).resolve_right hz
  rw [h0] at hlin
  rw [Finset.sum_mul]
  have : ∀ i, a i * ajAt d ι (F i) x * u₁ ^ d.jj =
      κ x * (a i * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U (F i) k) (fr x)) := by
    intro i
    rw [mul_assoc, hid (F i) (hF i) (hB i k) x hx]
    ring
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, ← hlin, mul_zero]

end GlobalTheory.ArcKill
end

