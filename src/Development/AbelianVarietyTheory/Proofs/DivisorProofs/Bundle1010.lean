import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0929
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupOfEventuallyPolynomial
section
set_option autoImplicit false

namespace GlobalTheory.CompHt

open Filter Topology
open scoped ENNReal

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
private lemma factorial_mul_div_pow_ennreal_eq_ofReal (D k m : ℕ) (hk : 1 ≤ k) :
    (D.factorial : ℝ≥0∞) * ((m : ℕ∞) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D =
      ENNReal.ofReal ((D.factorial : ℝ) * (m : ℝ) / (k : ℝ) ^ D) := by
  have hk' : (0 : ℝ) < (k : ℝ) ^ D := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  rw [ENNReal.ofReal_div_of_pos hk', ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity)]
  simp

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
private lemma tendsto_eval_div_pow_atTop_coeff_of_degree_le (Q : Polynomial ℝ) (D : ℕ) (hQ : Q.degree ≤ D) :
    Tendsto (fun y : ℝ => Q.eval y / y ^ D) atTop (𝓝 (Q.coeff D)) := by
  have hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D := by simp
  rcases hQ.lt_or_eq with hlt | heq
  · have hc : Q.coeff D = 0 := Polynomial.coeff_eq_zero_of_degree_lt hlt
    rw [hc]
    simpa using Polynomial.div_tendsto_zero_of_degree_lt Q (Polynomial.X ^ D) (by rw [hX]; exact hlt)
  · have hc : Q.leadingCoeff = Q.coeff D := by
      rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some heq]
    have := Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq Q (Polynomial.X ^ D) (by rw [hX, heq])
    simpa [hc] using this

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in

theorem _root_.GlobalTheory.CompHt.growth_of_eventually_eq_eval :
    ∀ (D a : ℕ) (h : ℕ → ℕ) (H : Polynomial ℚ), 1 ≤ a → (∀ᶠ n : ℕ in atTop, (h n : ℚ) = H.eval (n : ℚ)) →
      (H.degree ≤ D → ∀ δ : ℕ, (δ : ℚ) = (D.factorial : ℚ) * H.coeff D →
        _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = (a : ℝ≥0∞) ^ D * δ) ∧
      ((D : WithBot ℕ) < H.degree → _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = ⊤) := by
  intro D a h H ha hev
  set Q : Polynomial ℝ := H.map (algebraMap ℚ ℝ) with hQdef
  have hQdeg : Q.degree = H.degree := Polynomial.degree_map _ _

  have hak : Tendsto (fun k : ℕ => a * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k ha) tendsto_id
  have hakR : Tendsto (fun k : ℕ => ((a * k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hak

  have hval : ∀ᶠ k : ℕ in atTop, (h (a * k) : ℝ) = Q.eval ((a * k : ℕ) : ℝ) := by
    filter_upwards [hak.eventually hev] with k hk
    have hcast : ((a * k : ℕ) : ℝ) = algebraMap ℚ ℝ ((a * k : ℕ) : ℚ) := by simp
    rw [hQdef, Polynomial.eval_map, hcast, Polynomial.eval₂_at_apply, ← hk]
    simp

  set g : ℕ → ℝ := fun k => (D.factorial : ℝ) * (h (a * k) : ℝ) / (k : ℝ) ^ D with hg
  have hg_eq : ∀ᶠ k : ℕ in atTop, g k = (D.factorial : ℝ) * (a : ℝ) ^ D *
      (Q.eval ((a * k : ℕ) : ℝ) / ((a * k : ℕ) : ℝ) ^ D) := by
    filter_upwards [hval, eventually_ge_atTop 1] with k hk hk1
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    simp only [hg]
    rw [hk]
    push_cast
    field_simp
    ring
  have hlim : _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = limsup (fun k => ENNReal.ofReal (g k)) atTop := by
    unfold _root_.GlobalTheory.CompHt.growth
    refine limsup_congr ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact factorial_mul_div_pow_ennreal_eq_ofReal D k (h (a * k)) hk
  refine ⟨fun hdeg δ hδ => ?_, fun hdeg => ?_⟩
  · have hT : Tendsto g atTop (𝓝 ((D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D)) := by
      refine Tendsto.congr' (EventuallyEq.symm hg_eq) ?_
      exact ((tendsto_eval_div_pow_atTop_coeff_of_degree_le Q D (hQdeg ▸ hdeg)).comp hakR).const_mul _
    rw [hlim, (ENNReal.tendsto_ofReal hT).limsup_eq]
    have hc : (D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D = ((a ^ D * δ : ℕ) : ℝ) := by
      rw [hQdef, Polynomial.coeff_map]
      have : ((δ : ℚ) : ℝ) = ((D.factorial : ℚ) * H.coeff D : ℚ) := by rw [hδ]
      push_cast at this ⊢
      rw [this]
      simp only [eq_ratCast]
      ring
    rw [hc, ENNReal.ofReal_natCast]
    push_cast
    rfl
  · have hQdeg' : (D : WithBot ℕ) < Q.degree := hQdeg ▸ hdeg
    have hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D := by simp
    have hlc : 0 < Q.leadingCoeff := by
      by_contra hneg
      push_neg at hneg
      have hpos : 0 < Q.degree := lt_of_le_of_lt (by exact_mod_cast Nat.zero_le D) hQdeg'
      have hbot := (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos Q hpos hneg).comp hakR
      have hneg' := hbot.eventually (eventually_lt_atBot (0 : ℝ))
      obtain ⟨k, hk1, hk2⟩ := (hneg'.and hval).exists
      simp only [Function.comp_apply] at hk1
      rw [← hk2] at hk1
      exact absurd hk1 (not_lt.2 (Nat.cast_nonneg _))
    have hT : Tendsto g atTop atTop := by
      refine Tendsto.congr' (EventuallyEq.symm hg_eq) ?_
      refine Tendsto.const_mul_atTop (by positivity) ?_
      refine (Polynomial.div_tendsto_atTop_of_degree_gt Q (Polynomial.X ^ D) (by rw [hX]; exact hQdeg')
        (by simp) ?_).comp hakR |>.congr fun k => by simp
      simpa using hlc.le
    rw [hlim]
    exact (ENNReal.tendsto_ofReal_atTop.comp hT).limsup_eq

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.GalLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Datum

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

abbrev Comparison₂ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W)
    (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) : Prop :=
  Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L

abbrev ptAt (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) :
    PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f

structure VecData (f₀ f : WO (Vc D i) (Wc D i) → ℂ)
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) : Prop where
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f
  onb : ∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (B ρ) (pW D i ρ)
  theta : ∀ P, IsThetaFunO R.ψ (Vc D i) (Wc D i) (ptAt R i σ B f P)

def LiftData (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (H : HMod (Bridge.Gf (Vc D i) → c.W))
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) : Prop :=
  IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω ∧ VecData R i σ f₀ f B ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ B f) (deltaConj i σ) io ∧
    Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io
      (LinearMap.range (c.ext ∘ₗ H.e)) thP

def IsProjOf {c : CoefA (Vc D i)} {H : HMod (Bridge.Gf (Vc D i) → c.W)}
    (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ)))
    (th : H.H →ₗ[ℂ] (R.HW i σ).H) : Prop :=
  ∀ (x : H.H) (v : ∀ ρ, lowT (R.MW i σ) ρ),
    (R.HW i σ).e (th x) (fun ρ => v ρ) = R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict x) (PiTensorProduct.tprod ℂ v))

theorem isConjLift_iff (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (H : HMod (Bridge.Gf (Vc D i) → c.W))
    (th : H.H →ₗ[ℂ] (R.HW i σ).H) :
    IsConjLift R i σ μ' η' c H th ↔ ∃ ω f₀ f B io thP, LiftData R i σ μ' η' c H ω f₀ f B io thP ∧ IsProjOf R i σ thP th := by
  constructor
  · rintro ⟨ω, f₀, f, B, io, thP, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨ω, f₀, f, B, io, thP, ⟨h1, ⟨h2, h3, h4⟩, h5, h6⟩, h7⟩
  · rintro ⟨ω, f₀, f, B, io, thP, h, h7⟩
    exact ⟨ω, f₀, f, B, io, thP, h.1, h.2.1.vec, h.2.1.onb, h.2.1.theta, h.2.2.1, h.2.2.2, h7⟩

structure CoefAt (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) : Prop where
  coef : c.Is
  act : ∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE →
    ∀ v, c₁ (rhoVr (labLL D) (lamV D i) γE v) = c.ρ (γ : GA D (Vc D i)) (c₁ v)
  indep : LinearIndependent ℂ fun a => c₁ (bVV D.what₂.LL (lamV D i) a)
  span : Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL (lamV D i) a)) = ⊤
  pair : ∀ a b, inner ℂ (c₁ (bVV D.what₂.LL (lamV D i) a)) (c₁ (bVV D.what₂.LL (lamV D i) b)) =
    σ (pairVr (labLL D) (lamV D i) (gramV D i) (bVV D.what₂.LL (lamV D i) a) (bVV D.what₂.LL (lamV D i) b))

def PhaseFun (u : GA D (Wc D i) → ℂ) : Prop :=
  (∀ h, ‖u h‖ = 1) ∧ (∀ γ ∈ GQ (Wc D i), ∀ h, u (γ * h) = u h) ∧ (∀ g ∈ GinfC (Wc D i), ∀ h, u (h * g) = u h) ∧
    ∀ k ∈ levW R i, ∀ h, u (h * k) = u h

theorem phaseFun_one : PhaseFun R i (fun _ => 1) := ⟨fun _ => norm_one, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

abbrev IsLiftW (g : G) (k : GA D (Wc D i)) : Prop := Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k

def EtaVals : Prop :=
  ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.JoinChr.IsPlIdem D e P → ∀ x : (AE D)ˣ,
    (x : AE D) = Formalism.L2.JoinChr.locE D e (Formalism.L2.Host.unif P : D.host.Eˣ) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = ((R.eta x : Circle) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ)

end Datum

section Geo

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  (O : OMDat T.toCore R i Unit (fun _ => A.μ0))

def RepsAt (v₀ : (R.MW i (sg0 D A)).Vec) (h : O.Cl' () → GA D (Vc D i)) : Prop :=
  ∃ J' : Subgroup (Bridge.Gf (Vc D i)), RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) ∧
    PlaceEx R i A.μ0 h O.c0' ∧ ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ()) ∧
      ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x

abbrev actG (g : G) : T.R ((i : ℕ) + 1) →ₗ[T.Q.c.F] T.R ((i : ℕ) + 1) := actLev T.Q.c O.lev2 g

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))

def IsClassSum (h : O.Cl' () → GA D (Vc D i)) (x₀ : A.fam.amb.FL i A.μ0) {n : ℕ} (a : Fin n → D.what₂.LL)
    (f : Fin n → Cu T κ i) : Prop :=
  ∃ (x : O.Cl' () → VsV D i O.c'.F) (f' : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c'),
    Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x ∧ f' ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA (κ i)) (Vc D i).rank ∧
    IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ ()) (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) O.io x f' ∧
    IsBC O.hle f' (fun k => O.jL (a k)) (fun k => (f k : T.R ((i : ℕ) + 1)))

def EquivBy (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (u : GA D (Wc D i) → ℂ) : Prop :=
  ∀ g k, IsLiftW R i g k → ∀ (f : Cu T κ i) (h : GA D (Wc D i)),
    u h * phiC T hV (wtA (κ i)) (actG O g (f : T.R ((i : ℕ) + 1))) h =
      σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) * (u (h * k) * phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (h * k))

end Geo

def OneMapBaseRow : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.Char F → Nonempty (FWTie T R κ v₀) →
    ∀ i, OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i

def ReadingsExistRow : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ ∧ JEvBar T R κ

def ReadingsUnifRow : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ → JEvBar T R κ →
      EvInj T R v₀ → JUnif T R κ v₀

end GlobalTheory.GalLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealFormSpans
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.RealFormSpan

theorem jm_sq (n : ℕ) (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem jm_ct (n : ℕ) (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem inG_re (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1/2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)) := by
  unfold inG
  have h1 := jm_sq n ε
  have h2 := jm_ct n ε
  have h1' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
  simp only [Matrix.mul_assoc, h1, h1', Matrix.mul_one]
  have hs : star (1/2 : ℂ) = 1/2 := by simp
  rw [hs]
  module

theorem inG_im (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((-Complex.I/2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε)) := by
  unfold inG
  have h1 := jm_sq n ε
  have h2 := jm_ct n ε
  have h1' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]
  simp only [Matrix.mul_assoc, h1, h1', Matrix.mul_one]
  have hs : star (-Complex.I / 2) = Complex.I / 2 := by simp [Complex.conj_I]
  rw [hs]
  module

end GlobalTheory.RealFormSpan

open GlobalTheory.RealFormSpan in
theorem GlobalTheory.realForm_spans : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [AddCommGroup W] [Module ℂ W] (u : Fin n → Fin n → W), (∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∑ a, ∑ b, X a b • u a b = 0) → ∀ a b, u a b = 0 := by
  intro n ε W _ _ u h a b
  let f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] W :=
    { toFun := fun X => ∑ a, ∑ b, X a b • u a b
      map_add' := by intro X Y; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c X; simp [Finset.smul_sum, smul_smul] }
  have hZ : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z = (1/2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)
      + Complex.I • ((-Complex.I/2 : ℂ) • (Z + Jm ε * Zᴴ * Jm ε)) := by
    intro Z
    rw [smul_smul]
    have : Complex.I * (-Complex.I / 2) = (1/2 : ℂ) := by
      have := Complex.I_mul_I; linear_combination (-1/2:ℂ) * this
    rw [this, smul_sub, smul_add]
    rw [show ((1/2 : ℂ) • Z - (1/2:ℂ) • (Jm ε * Zᴴ * Jm ε) + ((1/2:ℂ) • Z + (1/2:ℂ) • (Jm ε * Zᴴ * Jm ε)))
      = ((1/2 : ℂ) + 1/2) • Z by rw [add_smul]; abel]
    norm_num
  have hf : ∀ Z, f Z = 0 := by
    intro Z
    have e1 := h _ (inG_re n ε Z)
    have e2 := h _ (inG_im n ε Z)
    change f _ = 0 at e1 e2
    rw [hZ Z, map_add, e1, map_smul, e2, smul_zero, add_zero]
  have := hf (Matrix.single a b 1)
  simpa [f, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentableOfZariskiSheafOpenChartsLarge
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem exists_represent_of_charts_large : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro F hsep hglue Ix U x hinj hopen hcov
  haveI hs : FunctorToTypes.Small.{0} F := GlobalTheory.T.small_of_separated_presheaf_open_charts F hsep Ix U x hopen hcov
  let G : Scheme.{0}ᵒᵖ ⥤ Type := FunctorToTypes.shrink.{0} F
  let e : ∀ T : Scheme.{0}, F.obj (op T) ≃ G.obj (op T) := fun T => equivShrink.{0} (F.obj (op T))
  have he : ∀ {Y T : Scheme.{0}} (a : Y ⟶ T) (y : G.obj (op T)),
      G.map a.op y = e Y (F.map a.op ((e T).symm y)) := fun a y => rfl
  have he' : ∀ {Y T : Scheme.{0}} (a : Y ⟶ T) (y : F.obj (op T)),
      G.map a.op (e T y) = e Y (F.map a.op y) := fun a y => by
    rw [he, Equiv.symm_apply_apply]
  have key := GlobalTheory.T.exists_universal_of_zariskiSheaf_openCharts G ?_ ?_ Ix U (fun i => e _ (x i)) ?_ ?_ ?_
  · obtain ⟨B, x₀, hx⟩ := key
    obtain ⟨x₁, rfl⟩ := (e B).surjective x₀
    have hx' : ∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₁ = y := by
      intro T y
      have h := hx T (e T y)
      simpa only [he', Equiv.apply_eq_iff_eq] using h
    exact ⟨B, x₁, hx', GlobalTheory.T.charts_representedFunctor_openCover F Ix U x hinj hopen hcov B x₁ hx'⟩
  · intro T y y' h
    obtain ⟨y, rfl⟩ := (e T).surjective y
    obtain ⟨y', rfl⟩ := (e T).surjective y'
    simp only [he', Equiv.apply_eq_iff_eq] at h
    rw [hsep T y y' h]
  · intro T J Z z y hz hc h
    obtain ⟨y₀, hy₀⟩ := hglue T J Z z (fun i => (e _).symm (y i)) hz hc (fun i k Y a b hab => by
      have h1 := h i k Y a b hab
      rw [he, he] at h1
      exact (e Y).injective h1)
    refine ⟨e T y₀, fun i => ?_⟩
    rw [he', hy₀, Equiv.apply_symm_apply]
  · intro i Y u u' h
    rw [he', he'] at h
    exact hinj i Y u u' ((e Y).injective h)
  · intro i T y
    obtain ⟨y, rfl⟩ := (e T).surjective y
    simp only [he', Equiv.apply_eq_iff_eq]
    exact hopen i T y
  · intro T y p
    obtain ⟨y, rfl⟩ := (e T).surjective y
    simp only [he', Equiv.apply_eq_iff_eq]
    exact hcov T y p

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffField
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiDetValues

set_option maxHeartbeats 1000000 in

theorem res_mem {D : D7} (S : Subfield ℂ) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq c χ)
    (hS : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ S)
    (P : Pl D.host.E) (ψ : (kP P)ˣ →* ℂˣ) (hψ : IsRes χ P ψ⁻¹) (u : (kP P)ˣ) : ((ψ u : ℂˣ) : ℂ) ∈ S := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have hnt : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.ext h
    rw [h0, map_zero] at ha
    exact u.ne_zero ha.symm
  have h4 := hψ a (Units.mk0 _ ha0) u rfl ha.symm
  have h5 := hc.2 P e he (Units.mk0 _ ha0) (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ ha0)) rfl
  have h6 := hS (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ ha0)) (by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add, RingHom.map_one, RingHom.map_mul, hinf,
      zero_mul, add_zero])
  rw [h5, ← h4, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at h6
  exact inv_mem_iff.1 h6

set_option maxHeartbeats 1000000 in

theorem chiC_mem_coeff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (g : G), ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL t i g
  have e0 : res T D.what₂.embLL = T.σ₀ := res_embLL T t.alg t.laws.pins.2.2.1
  have hσ : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.good_σ₀
  have hA := (t.chiR i D.what₂.embLL hσ).2.2.2.1
  have h : ((chiC R i g : ℂˣ) : ℂ) ∈ (res T D.what₂.embLL).fieldRange := by
    unfold chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy, -⟩ := hA x hx
    exact ⟨y, hy.symm⟩
  exact h

end GlobalTheory.ChiDetValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiInvolutionOfGaloisIsogenyDescentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_involution_of_galois_isogeny_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → ∀ c' : D.O, LBIso (P'.pull (lift (fst A' A' ≫ act'.act c') (snd A' A')).left) (P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c').unop)).left) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.rosati_of_descent | exact GlobalTheory.UPel.HT.Hecke.rosati_of_descent | (intros; apply GlobalTheory.UPel.HT.Hecke.rosati_of_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameElementSignAmbiguity
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem finiteQ (G : HTGroup p) : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C

theorem norm_sim (P : Pair G) :
    Algebra.norm ℚ (P.γ : G.C) * Algebra.norm ℚ (sh G P.γ) = (P.c : ℚ) ^ Module.finrank ℚ G.C := by
  haveI := finiteQ G
  have h := congrArg (Algebra.norm ℚ) P.sim
  rw [map_mul, map_mul, map_mul, Algebra.norm_algebraMap] at h
  have hb : Algebra.norm ℚ (P.β : G.C) ≠ 0 := (P.β.isUnit.map (Algebra.norm ℚ)).ne_zero
  apply mul_right_cancel₀ hb
  rw [← h]; ring

theorem c_eq_or_eq_neg : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P P' : Pair G), P'.γ = P.γ → P'.c = P.c ∨ P'.c = -P.c := by
  intro p _ G P P' hγ
  haveI := finiteQ G
  have h1 := norm_sim P
  have h2 := norm_sim P'
  rw [hγ, h1] at h2
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  rcases (pow_eq_pow_iff_of_ne_zero hN).1 h2.symm with h | ⟨h, _⟩
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg]))

end GlobalTheory.LKMid.Pair
end

