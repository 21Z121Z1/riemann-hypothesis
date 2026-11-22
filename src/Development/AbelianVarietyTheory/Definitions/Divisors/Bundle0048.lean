import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0013
import Formalism.RealPlaceAnalysis.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair

variable {k K : Type} [Field k] [Field K]

def AdjKlt (c : k →+* K) (n : ℕ) (T : Subring K) (S : Place c) (η : Forms c n) (φ : K →₀ ℚ) :
    Prop :=
  η ≠ 0 ∧ φ 0 = 0 ∧
  ∀ (Q : Subring K) (hQ : IsLocModel c Q) (t u : Q) (E : Place c), T ≤ Q →
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
    S.IsPrimeOf Q → E.IsPrimeOf Q → S.ord (t : K) = 1 → E.ord (u : K) = 1 →
    (∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring → P.disc η φ = 0) →
    -1 < E.disc η φ

namespace AdjKlt

variable {c : k →+* K} {n : ℕ} {T T' : Subring K} {S : Place c} {η : Forms c n} {φ : K →₀ ℚ}

theorem form_ne_zero (h : AdjKlt c n T S η φ) : η ≠ 0 := h.1

theorem apply_zero (h : AdjKlt c n T S η φ) : φ 0 = 0 := h.2.1

theorem lt_disc (h : AdjKlt c n T S η φ) {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q}
    {E : Place c} (hT : T ≤ Q)
    (hm : Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q))
    (hd : ringKrullDim Q = 2) (hS : S.IsPrimeOf Q) (hE : E.IsPrimeOf Q)
    (ht : S.ord (t : K) = 1) (hu : E.ord (u : K) = 1)
    (h0 : ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring → P.disc η φ = 0) :
    -1 < E.disc η φ :=
  h.2.2 Q hQ t u E hT hm hd hS hE ht hu h0

theorem mono (h : AdjKlt c n T S η φ) (hT : T ≤ T') : AdjKlt c n T' S η φ :=
  ⟨h.1, h.2.1, fun Q hQ t u E hQ' => h.2.2 Q hQ t u E (hT.trans hQ')⟩

def incl {Q : Subring K} {P : Place c} (h : P.Contains Q) : Q →+* P.ring :=
  Q.subtype.codRestrict P.ring fun q => h q q.2

theorem mem_maximalIdeal_iff (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0) :
    b ∈ IsLocalRing.maximalIdeal P.ring ↔ P.ord (b : K) ≠ 0 := by
  refine ⟨fun h h0 => h ?_, fun h hu => h (P.ord_eq_zero hu)⟩
  have h1 : (b : K)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h0]; rfl)
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))

theorem neighbour_ne {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q} {S E : Place c}
    (hm : Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q))
    (hd : ringKrullDim Q = 2) (hS : S.IsPrimeOf Q) (ht : S.ord (t : K) = 1)
    (hu : E.ord (u : K) = 1) : E ≠ S := by
  rintro rfl
  haveI := hQ.isLocalRing
  have h0 : E.ord (0 : K) = 0 := by simp [Place.ord]
  have hle : IsLocalRing.maximalIdeal Q ≤
      (IsLocalRing.maximalIdeal E.ring).comap (incl hS.1) := by
    rw [← hm, Ideal.span_le]
    rintro _ (h | h) <;> rw [h]
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (t : K) = 0 at h; rw [h, h0] at ht; omega).2 (by change E.ord (t : K) ≠ 0; omega)
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (u : K) = 0 at h; rw [h, h0] at hu; omega).2 (by change E.ord (u : K) ≠ 0; omega)
  have hb : Function.Bijective (incl hS.1) := by
    refine ⟨fun a b e => Subtype.ext (congrArg (fun z : E.ring => (z : K)) e), fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f f.2
    have hu : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact (mem_maximalIdeal_iff E _ hb0).1 (hle hn) hbo
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    refine ⟨⟨a, ha⟩ * g, Subtype.ext ?_⟩
    change a * (g : K) = f
    rw [← e, mul_assoc, hg', mul_one]
  have := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)
  rw [hd, IsPrincipalIdealRing.ringKrullDim_eq_one _ (IsDiscreteValuationRing.not_isField _)] at this
  exact absurd this (by decide)

end AdjKlt

variable {c : k →+* K} {n : ℕ} {T : Subring K} {η : Forms c n} {φ : K →₀ ℚ}

theorem adjKlt_of_lt_disc (S : Place c) (hη : η ≠ 0) (hφ : φ 0 = 0)
    (h : ∀ E : Place c, E.Contains T → E.ring ≠ S.ring → -1 < E.disc η φ) :
    AdjKlt c n T S η φ :=
  ⟨hη, hφ, fun _ hQ _ _ E hT hm hd hS hE ht hu _ =>
    h E (hE.1.mono hT) fun e => AdjKlt.neighbour_ne hQ hm hd hS ht hu (Place.ext e)⟩

example (S : Place c) : ¬ AdjKlt c n T S 0 φ := fun h => h.form_ne_zero rfl

example (S : Place c) : ¬ AdjKlt c n T S η (Finsupp.single 0 1) := fun h => by
  simpa using h.apply_zero

example (S : Place c) (hη : η ≠ 0) (hφ : φ 0 = 0) (hT : ∀ E : Place c, ¬ E.Contains T) :
    AdjKlt c n T S η φ :=
  adjKlt_of_lt_disc S hη hφ fun E hE _ => (hT E hE).elim

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.BlockPairCycPow
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published.CharAboveModel

namespace GlobalTheory.ExpFrame.Inhab

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]

theorem crysWith_cyc_pow (m : ℕ) : CrysWith (rk1 (cyc E Ω l ^ m)) fun _ => {-(m : ℤ)} := by
  have hc : Continuous (cyc E Ω l) :=
    (Continuous.units_map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
      ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp
        (continuous_subtype_val : Continuous fun z : ℤ_[l] => (z : ℚ_[l])))).comp (continuous_cycZ E Ω l)
  refine ⟨?_, ?_⟩
  · have h1 : Continuous (cyc E Ω l ^ m) := hc.pow m
    refine (Continuous.units_map _ ?_).comp h1
    exact continuous_pi fun i => continuous_pi fun j => by
      fin_cases i; fin_cases j
      simpa using continuous_id'
  rintro P AI ⟨T⟩ w A - O _ _ _ Bw -
  obtain ⟨hc, hm⟩ := GlobalTheory.HTW.Rec.Model.cycPowSum_crys_mult T Bw.Kw Bw.LL (fun _ : Fin 1 => -(m : ℤ))
  have hd := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T Bw.Kw Bw.LL _ _ hc).1
  have hM : IsModel Bw ((rk1 (cyc E Ω l ^ m)).comp (Dec (F := E) A).subtype) Bw.LL (powModel P Bw m) := by
    refine ⟨le_rfl, MonoidHom.ext fun g => ?_⟩
    have e := GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc P Bw.j (g : G E Ω) (Bw.e g : GQ l) (Bw.e_comm g)
    ext a c
    fin_cases a
    fin_cases c
    simp [powModel, rk1, mapRep, cycLL, P.PD_χ, e, cyc_eq_map_cycZ, Matrix.diagonal_pow]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Pi.pow_apply]
    rfl
  have hC : Bw.IsCrysE P Bw.LL (powModel P Bw m) := by
    rw [LocBridge.IsCrysE, repE_powModel]; exact hc
  have hD : Bw.IsdRE P Bw.LL (powModel P Bw m) := by
    rw [LocBridge.IsdRE, repE_powModel]
    have h2 : Module.finrank ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw)
        (matRep (GlobalTheory.HTW.Rec.Model.cycPowSum P Bw.Kw Bw.LL (fun _ : Fin 1 => -(m : ℤ))))) =
        Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin 1 → ↥Bw.LL.1) := hd
    simpa using h2
  refine ⟨⟨_, _, hM, hC⟩, fun τ LL' τ' hτ => ?_⟩
  let τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1 :=
    (LL'.1.val.comp τ').codRestrict Bw.LL.1.toSubalgebra fun x => Bw.LL_split _ x
  refine ⟨Bw.LL, _, hM, hD, τ₂, fun x => hτ x, fun n => ?_⟩
  rw [LocBridge.multE, repE_powModel, hm τ₂ n]
  simp only [List.ofFn_succ, List.ofFn_zero, Multiset.count_singleton, List.count_cons, List.count_nil]
  by_cases h : n = -(m : ℤ)
  · simp [h]
  · simp [h, Ne.symm h]

theorem blockPair_cyc_pow (m : ℕ) : BlockPair E Ω l 1 1 (fun _ _ => -(m : ℤ)) fun _ => -(m : ℤ) := by
  refine ⟨rk1 (cyc E Ω l ^ m), 0, 1, fun _ => cyc E Ω l ^ m, rfl, ?_, continuous_const, fun s => ?_, fun σ k => ?_⟩
  · simpa using crysWith_cyc_pow E Ω l m
  · simpa using crysWith_cyc_pow E Ω l m
  · have e : ((rk1 (cyc E Ω l ^ m) σ).val).charpoly = Polynomial.X - Polynomial.C (((cyc E Ω l ^ m) σ : (Qbar l)ˣ) : Qbar l) := by
      rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
      simp [rk1, Matrix.diagonal_pow]
    rw [e]
    simp [Matrix.charpoly]

end GlobalTheory.ExpFrame.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Divisor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Vanishing

namespace GlobalTheory.CuspDim

variable {k : Type} [CommRing k] {Z : Scheme.{0}}

section Growth

variable (p : Z ⟶ Sp k) (σ : k →+* ℂ) (O : Z.Opens)

def push : CxPts (O.ι ≫ p) σ → CxPts p σ := PtsOver.map O.ι rfl _

variable {p σ}

structure NcChart {D : ℕ} (y : CxPts p σ) (e : OpenPartialHomeomorph (CxPts p σ) (V D)) (S : Finset (Fin D)) : Prop where

  holo : ∀ (W : Z.Opens) (f : Γ(Z, W)), DifferentiableOn ℂ (ev p σ W f ∘ e.symm) (e.target ∩ e.symm ⁻¹' ptsIn p σ W)

  mem : y ∈ e.source

  centre : ∀ a ∈ S, e y a = 0

  bd : ∀ z ∈ e.source, z ∉ ptsIn p σ O ↔ ∃ a ∈ S, e z a = 0

def LogAt (D : ℕ) (φ : CxPts (O.ι ≫ p) σ → ℝ) (y : CxPts p σ) : Prop :=
  ∃ (e : OpenPartialHomeomorph (CxPts p σ) (V D)) (S : Finset (Fin D)), NcChart O y e S ∧ ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ᶠ z in comap (push p σ O) (𝓝 y), φ z ≤ C * (1 + ∑ a ∈ S, |Real.log ‖e (push p σ O z) a‖|) ^ N

def LogEq (W : Z.Opens) (b : Γ(Z, W)) (φ : CxPts (O.ι ≫ p) σ → ℝ) (y : CxPts p σ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ᶠ z in comap (push p σ O) (𝓝 y), φ z ≤ C * (1 + |Real.log ‖ev p σ W b (push p σ O z)‖|) ^ N

end Growth

section Metric

variable {q : Z ⟶ Sp k} {σ : k →+* ℂ} {A B : LB Z}

def IsoM (φ : Weight q σ A) (ψ : Weight q σ B) : Prop :=
  ∃ w : LB.Iso A B, w.IsGen ∧ ∀ (a : A.ι) (b : B.ι) (y : CxPts q σ), y ∈ ptsIn q σ (A.U a) → y ∈ ptsIn q σ (B.U b) →
    ψ.φ b y = φ.φ a y + Real.log (‖ev q σ _ (w.s (b, a)).val y‖ ^ 2)

def len (φ : Weight q σ B) (s : H0 q B ⊤) (y : CxPts q σ) : ℝ := φ.nsq (secVal q σ (GlobalTheory.CompHS.toSec s)) y

def Scales (φ : Weight q σ A) (ψ : Weight q σ B) (G : H0 q A ⊤ →ₗ[k] H0 q B ⊤) (c : CxPts q σ → ℝ) : Prop :=
  Function.Injective G ∧ ∀ s y, len ψ (G s) y = c y * len φ s y

end Metric

structure HidaSetting {k : Type} [Field k] (σ : k →+* ℂ) {Z : Scheme.{0}} (p : Z ⟶ Sp k) (D : ℕ) (Λ : Type) [AddCommGroup Λ] where

  smooth : SmoothOfRelativeDimension D p

  proj : IsProjOver p

  integral : IsIntegral Z

  O : Z.Opens

  divisor : ∀ x ∉ O, ∃ (W : Z.Opens) (b : Γ(Z, W)), IsAffineOpen W ∧ x ∈ W ∧ Z.basicOpen b = W ⊓ O

  nc : ∀ y ∉ ptsIn p σ O, ∃ (e : OpenPartialHomeomorph (CxPts p σ) (V D)) (S : Finset (Fin D)), NcChart O y e S

  ℒ : Λ → LB O.toScheme

  h : ∀ w, Weight (O.ι ≫ p) σ (ℒ w)

  mul : ∀ w w', IsoM ((h w).tens (h w')) (h (w + w'))

  u' : Λ

  u₁ : Λ

  S : ∀ n : ℕ, Submodule k (H0 (O.ι ≫ p) (ℒ (n • u')) ⊤)

  bdd : ∀ n, 1 ≤ n → ∀ f ∈ S n, ∃ C : ℝ, ∀ z, len (h (n • u')) f z ≤ C

  τ : H0 (O.ι ≫ p) (ℒ (u₁ - u')) ⊤

  τ_ne : τ ≠ 0

  τ_log : ∀ y ∉ ptsIn p σ O, LogAt O D (len (h (u₁ - u')) τ) y

  L : LB Z

  isLB : L.IsLB

  hL : Weight (O.ι ≫ p) σ (L.pull O.ι)

  ext : IsoM (h (3 • u₁ - 2 • u')) hL

  good : ∀ y ∉ ptsIn p σ O, ∀ i, y ∈ ptsIn p σ (L.U i) →
    LogAt O D (fun z => Real.exp (-hL.φ (fun _ => i) z)) y ∧ LogAt O D (fun z => Real.exp (hL.φ (fun _ => i) z)) y

end GlobalTheory.CuspDim
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
section
namespace GlobalTheory.BCT

structure Inputs : Prop where
  discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL
  bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  jacquetShalika : GlobalTheory.Published.JacquetShalika
  jacquetShalikaRigidity : GlobalTheory.Published.JacquetShalikaRigidity
  cohomologicalCsdTempered : GlobalTheory.Published.CohomologicalCsdTempered
  galoisRepOfPolarizedCuspidal : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  radfordShufflePolynomial : GlobalTheory.Published.RadfordShufflePolynomial
  clozelPurity : GlobalTheory.Published.ClozelPurity
  clozelCohomological : GlobalTheory.Published.ClozelCohomological
  localLanglandsGL : GlobalTheory.Published.LocalLanglandsGL
  heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter
  chebotarevDegreeOne : GlobalTheory.Published.ChebotarevDegreeOne
  cuspidalMultiplicityOne : GlobalTheory.Published.CuspidalMultiplicityOne
  residualSpectrumHilbertSum : GlobalTheory.Published.ResidualSpectrumHilbertSum
  heckeLEntireAndNonzeroAtOne : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne
  geometricLemma : GlobalTheory.Published.GeometricLemma
  borelCasselman : GlobalTheory.Published.BorelCasselman
  quadraticClassFieldTheory : GlobalTheory.Published.QuadraticClassFieldTheory
  hermitianLocalGlobal : GlobalTheory.Published.HermitianLocalGlobal

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
section
noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace GlobalTheory.GamMul

section Blocks

variable {R : Type} [CommRing R]

def put (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
      X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0

def eye (R : Type) [CommRing R] (n o₁ o₂ p : ℕ) : Matrix (Fin n) (Fin n) R :=
  put n o₁ o₂ (1 : Matrix (Fin p) (Fin p) R)

open Classical in

def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : GL (Fin n) R := if h : IsUnit M then h.unit else 1

def uni (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) : GL (Fin n) R := toGL (1 + put n o₁ o₂ X)

def dg (n o : ℕ) {p : ℕ} (g : GL (Fin p) R) : GL (Fin n) R :=
  toGL (1 - eye R n o o p + put n o o (g : Matrix (Fin p) (Fin p) R))

def shuf (R : Type) [CommRing R] (n m : ℕ) : GL (Fin n) R := toGL (eye R n 0 m (n - m) + eye R n (n - m) 0 m)

theorem toGL_val {n : ℕ} (g : GL (Fin n) R) : toGL (g : Matrix (Fin n) (Fin n) R) = g := by
  unfold toGL
  rw [dif_pos g.isUnit]
  exact Units.ext rfl

end Blocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mint [MeasurableSpace k] (μ : Measure k) {p q : ℕ} (F : Matrix (Fin p) (Fin q) k → ℂ) : ℂ :=
  ∫ x : Fin p → Fin q → k, F (Matrix.of x) ∂(Measure.pi fun _ => Measure.pi fun _ => μ)

def box (p q : ℕ) (c : kˣ) : Set (Matrix (Fin p) (Fin q) k) := {X | ∀ i j, valuation k (X i j) ≤ valuation k (c : k)}

def ad {m : ℕ} (s : ℂ) (g : GL (Fin m) k) : ℂ := (absPow k s (GeneralLinearGroup.det g) : ℂ)

def intA [MeasurableSpace k] (μ : Measure k) {n m : ℕ} (i : ℕ) (W : GL (Fin n) k → ℂ) (g : GL (Fin m) k) : ℂ :=
  mint μ fun X : Matrix (Fin i) (Fin m) k => W (dg n 0 g * uni n m 0 X)

def intD [MeasurableSpace k] (μ : Measure k) {n m : ℕ} (i : ℕ) (W : GL (Fin n) k → ℂ) (g : GL (Fin m) k) : ℂ :=
  mint μ fun Y : Matrix (Fin m) (Fin i) k => W (shuf k n m * dg n 0 g * uni n 0 (n - i) Y)

def IsCuspFun {n : ℕ} (ψ : AddChar k Circle) (W : GL (Fin n) k → ℂ) : Prop :=
  (∀ u ∈ unipB k (Fin n), ∀ g, W (u * g) = (ψ (superDiag u) : ℂ) * W g) ∧
  (∃ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) ∧ ∀ x ∈ K, ∀ g, W (g * x) = W g) ∧
  ∃ C : Set (GL (Fin n) k), IsCompact C ∧ ∀ g, W g ≠ 0 →
    ∃ z : kˣ, ∃ u ∈ unipB k (Fin n), ∃ c ∈ C, g = GeneralLinearGroup.scalar (Fin n) z * u * c

def IsCuspSpace {n : ℕ} (ψ : AddChar k Circle) (𝒲 : Submodule ℂ (GL (Fin n) k → ℂ)) : Prop :=
  ∀ W ∈ 𝒲, IsCuspFun ψ W ∧ ∀ x, (fun g => W (g * x)) ∈ 𝒲

def whMap {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (l : Module.Dual ℂ V) : V →ₗ[ℂ] (GL (Fin n) k → ℂ) :=
  LinearMap.pi fun g => l ∘ₗ π g

def FE [MeasurableSpace k] (μ : Measure k) (ψ : AddChar k Circle) {n m : ℕ} (𝒲 : Submodule ℂ (GL (Fin n) k → ℂ))
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin m) k) V) (i : ℕ) (c : ℂ) : Prop :=
  ∀ l : Module.Dual ℂ V, IsFunctional ψ⁻¹ τ l → ∀ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I →
    ∀ W ∈ 𝒲, ∀ v : V,
      I (fun g => intD μ (n - m - 1 - i) W g * ad (((n - m - 1 : ℕ) : ℂ) / 2) g * l (τ g v)) =
        c * I (fun g => intA μ i W g * ad (-((n - m - 1 : ℕ) : ℂ) / 2) g * l (τ g v))

def intJ [MeasurableSpace k] (μ : Measure k) {m m₁ m₂ : ℕ} (φ : GL (Fin m) k → ℂ) (a : GL (Fin m₁) k)
    (b : GL (Fin m₂) k) : ℂ :=
  mint μ fun x : Matrix (Fin m₂) (Fin m₁) k => φ (dg m 0 a * dg m m₁ b * uni m m₁ 0 x)

def intM [MeasurableSpace k] (μ : Measure k) {n m₁ m₂ : ℕ} (j : ℕ) (W : GL (Fin n) k → ℂ) (a : GL (Fin m₁) k)
    (b : GL (Fin m₂) k) : ℂ :=
  mint μ fun Y : Matrix (Fin m₁) (Fin j) k => W (dg n 0 b * (shuf k n m₁ * dg n 0 a * uni n 0 (n - j) Y))

def IsTest₂ {m₁ m₂ : ℕ} (ψ : AddChar k Circle) (F : GL (Fin m₁) k → GL (Fin m₂) k → ℂ) : Prop :=
  (∀ u ∈ unipB k (Fin m₁), ∀ a b, F (u * a) b = (ψ (superDiag u) : ℂ) * F a b) ∧
  (∀ u ∈ unipB k (Fin m₂), ∀ a b, F a (u * b) = (ψ (superDiag u) : ℂ) * F a b) ∧
  IsLocallyConstant (Function.uncurry F) ∧
  ∃ (C₁ : Set (GL (Fin m₁) k)) (C₂ : Set (GL (Fin m₂) k)), IsCompact C₁ ∧ IsCompact C₂ ∧ ∀ a b, F a b ≠ 0 →
    (∃ u ∈ unipB k (Fin m₁), ∃ c ∈ C₁, a = u * c) ∧ ∃ u ∈ unipB k (Fin m₂), ∃ c ∈ C₂, b = u * c

def IsAvg {m : ℕ} (m₁ m₂ : ℕ) (φ φ₀ : GL (Fin m) k → ℂ) : Prop :=
  ∃ (N : ℕ) (y : Fin N → Matrix (Fin m₂) (Fin m₁) k) (c : Fin N → ℂ), ∑ i, c i = 1 ∧
    ∀ g, φ₀ g = ∑ i, c i * φ (g * uni m m₁ 0 (y i))

def InCell {m m₁ m₂ : ℕ} (h : m₁ + m₂ = m) (φ : GL (Fin m) k → ℂ) : Prop :=
  ∃ C : Set (GL (Fin m) k), IsCompact C ∧ C ⊆ parabLower k (two (stdSum h)) ∧
    ∀ g, φ g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c

abbrev LowSp {m m₁ m₂ : ℕ} (h : m₁ + m₂ = m) {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m₁) k × GL (Fin m₂) k) V) : Type :=
  IndSpLower (two (stdSum h)) (σ.comp (leviTwo k (Fin m₁) (Fin m₂)).symm.toMonoidHom)

def lowInd {m m₁ m₂ : ℕ} (h : m₁ + m₂ = m) {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m₁) k × GL (Fin m₂) k) V) : Representation ℂ (GL (Fin m) k) (LowSp h σ) :=
  ind₂Lower (stdSum h) σ

def IsBump {m m₁ m₂ : ℕ} (h : m₁ + m₂ = m) {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m₁) k × GL (Fin m₂) k) V) (Λ : Set (Matrix (Fin m₁) (Fin m₂) k)) (v : V)
    (f : LowSp h σ) : Prop :=
  (∀ y ∈ Λ, f.1.1 (uni m 0 m₁ y) = v) ∧
    ∀ g, f.1.1 g ≠ 0 → ∃ p ∈ parabLower k (two (stdSum h)), ∃ y ∈ Λ, g = p * uni m 0 m₁ y

def vol [MeasurableSpace k] (μ : Measure k) {p q : ℕ} (Λ : Set (Matrix (Fin p) (Fin q) k)) : ℂ :=
  mint μ (Λ.indicator fun _ => 1)

def pairJ [MeasurableSpace k] (μ : Measure k) {m m₁ m₂ : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m₁) k × GL (Fin m₂) k) V) (l : Module.Dual ℂ V) (v : V) (φ : GL (Fin m) k → ℂ)
    (a : GL (Fin m₁) k) (b : GL (Fin m₂) k) : ℂ :=
  intJ μ φ a b * (ad (-(m₂ : ℂ) / 2) a * ad ((m₁ : ℂ) / 2) b) * l (σ (a, b) v)

def IsBiFun {m₁ m₂ : ℕ} (ψ : AddChar k Circle) {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m₁) k × GL (Fin m₂) k) V) (l : Module.Dual ℂ V) : Prop :=
  IsFunctional ψ (σ.comp (MonoidHom.inl _ _)) l ∧ IsFunctional ψ (σ.comp (MonoidHom.inr _ _)) l

end GlobalTheory.GamMul

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep Formalism.REAL

namespace GlobalTheory.WigAlg

def cx {E : Type} [Field E] {a : ℕ} {N : Type} [AddCommGroup N] [Module ℂ N] (τ : E →+* ℂ) (φ : Lie E a → N)
    (i j : Fin a) : N :=
  (1 / 2 : ℂ) • (φ (toL (Matrix.single i j (atEmb τ 1))) - Complex.I • φ (toL (Matrix.single i j (atEmb τ Complex.I))))

def tpr {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (A B : Fin n → Fin n → Module.End ℂ M) (p r : ℕ)
    (φ : Fin n → Fin n → M) : M :=
  ∑ x, ∑ y, ∑ z, epow A p x y (epow B r x z (φ y z))

end GlobalTheory.WigAlg

end
end

