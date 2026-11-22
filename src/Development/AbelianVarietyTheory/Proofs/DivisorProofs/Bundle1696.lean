import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaOfPolAV
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm
open GlobalTheory.CechPic (cls lam)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart moeb ChernIsFlat)
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.ThetaRR

section Scheme

variable {k : Type} [CommRing k] {S : Scheme.{0}}

def IsTheta (P : PPAS S) (L : LB P.A.left) : Prop :=
  ∃ hL : L.IsLB, Out.Rigidified P.A L ∧ Out.Sym P.A L ∧ Out.RelAmple P.A L ∧ Out.KTriv P.A L ∧
    P.c = lam (cls L hL) (fst P.A P.A) (snd P.A P.A)

def IsTheta.polAV {P : PPAS S} {L : LB P.A.left} (h : IsTheta P L) : Out.PolAV S :=
  ⟨P.A, P.isAb, P.g, P.smoothDim, L, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

def dbl (P : PPAS S) : P.A.left ⟶ P.A.left := (Out.mulA P.A 2).left

theorem dbl_hom (P : PPAS S) : dbl P ≫ P.A.hom = P.A.hom := Over.w _

theorem dbl_comp (P : PPAS S) (p : S ⟶ Sp k) : dbl P ≫ (P.A.hom ≫ p) = P.A.hom ≫ p := by
  rw [← Category.assoc, dbl_hom]

variable {p : S ⟶ Sp k}

def FramedCharts (P : PPAS S) (h : VMetric p (omega P.A) P.g) (L : HermLB (P.A.hom ≫ p)) : Prop :=
  ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
    (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ)
    (m : Pt (V 1) P.g → ℝ), y ∈ c.e.source ∧ Convex ℝ c.e.target ∧ IsPeriodChart h c τ ex ∧
      IsFramed L c.e.target τ ex j m ∧ IsDatum c.e.target τ (stdLat P.g) j m

def FlatCharts (P : PPAS S) (h : VMetric p (omega P.A) P.g) (L : HermLB (P.A.hom ≫ p)) : Prop :=
  ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
    (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ)
    (m : Pt (V 1) P.g → ℝ), y ∈ c.e.source ∧ Convex ℝ c.e.target ∧ IsPeriodChart h c τ ex ∧
      IsFramed L c.e.target τ ex j m ∧ IsDatum c.e.target τ (stdLat P.g) j m ∧
      ChernIsFlat c.e.target τ m

end Scheme

def Naturality : Prop :=
  BaseChange ∧ OneVector ∧ IsometryInv ∧ TranslationInv ∧ SymplecticInv ∧ CoverSum ∧ FlatAcyclic

variable {g : ℕ}

def actB (γ : IndefiniteRowSideFullHecke.SiegelReframe.Sp g) (s : symMat g) : symMat g := symPart (moeb γ (tauU s))

def sdens (τ Z : Matrix (Fin g) (Fin g) ℂ) : ℝ :=
  ((τ.map fun t => (t.im : ℂ))⁻¹ * Z * (τ.map fun t => (t.im : ℂ))⁻¹ * Z.map star).trace.re

example : sdens (g := 1) (Matrix.diagonal fun _ => Complex.I) 1 = 1 := by
  have e : ((Matrix.diagonal fun _ : Fin 1 => Complex.I).map fun t => (t.im : ℂ)) = 1 := by
    ext i j; fin_cases i; fin_cases j; simp
  simp [sdens, e]

variable (g) in

def IsUnivTorsion (s v : symMat g) (T : Ext (1 + 1)) : Prop :=
  ∃ (j : Fl g → Pt (symMat g) g → ℂ) (m : Pt (symMat g) g → ℝ),
    IsDatum (siegel g) tauU (stdLat g) j m ∧ ChernIsFlat (siegel g) tauU m ∧
      IsTorsionForm tauU (stdLat g) j m ![v] s T

variable (g) in

def IsHermFun (F : symMat g → symMat g → Ext (1 + 1)) : Prop :=
  ContinuousOn (fun x : symMat g × symMat g => F x.1 x.2) (siegel g ×ˢ univ) ∧
  ∀ s ∈ siegel g, (∃ t : ℝ, ∀ v, F s v ∅ = t) ∧ ∃ B : symMat g → symMat g → ℂ,
    (∀ (a : ℂ) v v' w, B (a • v + v') w = a * B v w + B v' w) ∧ (∀ v w, B w v = star (B v w)) ∧
      ∀ v, F s v Finset.univ = Complex.I * B v v

def IsInvFun (F : symMat g → symMat g → Ext (1 + 1)) (γ : IndefiniteRowSideFullHecke.SiegelReframe.Sp g) : Prop :=
  ∀ s ∈ siegel g, ∀ v, F (actB γ s) (fderiv ℂ (actB γ) s v) = F s v

end GlobalTheory.ThetaRR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSmoothVecOfIrreducibleUnitaryRepStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_smoothVec_of_irreducible_unitaryRep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ v, IsKFin ε σ v → Formalism.L2.Theta.SmoothVec {X | inG ε X} σ v := by
  first | exact @GlobalTheory.HdSmooth.kFinite_smoothVec | exact GlobalTheory.HdSmooth.kFinite_smoothVec | (intros; apply GlobalTheory.HdSmooth.kFinite_smoothVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentVectorsLift
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagTan

theorem le_preimage_of_trivSqZeroExt {L M : Type} [Field L] [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M]
    [IsCentralScalar L M] {T : Scheme.{0}} (φ : TrivSqZeroExt L M →+* L) (hφ : ∀ a, φ a = a.fst)
    (x : Sp (TrivSqZeroExt L M) ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  let q : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : (spMap φ) q = s := by
    refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
    change φ a ∈ (⊥ : Ideal L) ↔ a ∈ s.asIdeal
    rw [Ideal.mem_bot, hφ]
    constructor
    · intro ha
      refine s.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by
        rw [pow_two, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha rfl, TrivSqZeroExt.inr_mul_inr]]
      exact s.asIdeal.zero_mem
    · intro ha
      by_contra h0
      exact s.2.ne_top (s.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
  have h₁ : (spMap φ ≫ x) q ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem IsKS.sum_of_der : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K} (hy : KSIso (psiSet H) y)
    {ι : Type} [Fintype ι] {x : ι → (Sp (DualNumber K) ⟶ Xo.X)} (hx : ∀ a, GlobalTheory.FlagTan.IsTanX y (x a))
    {Mx : ι → HIx Dw (psiSet H) → K} (hM : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) y (x a) (Mx a))
    {x' : Sp (DualNumber K) ⟶ Xo.X} (hx' : GlobalTheory.FlagTan.IsTanX y x') (m : ι → K)
    (h : ∀ (O : Xo.X.Opens) (f : Γ(Xo.X, O)) (h' : ⊤ ≤ x' ⁻¹ᵁ O) (hc : ∀ a, ⊤ ≤ x a ⁻¹ᵁ O),
      (evalPt x' O h' f).snd = ∑ a, m a * (evalPt (x a) O (hc a) f).snd), GlobalTheory.FlagTan.IsKS (psiSet H) y x' (∑ a, m a • Mx a) := by
  intro E _ _ _ H Dw l Xo c K _ _ y hy ι _ x hx Mx hM x' hx' m h
  obtain ⟨X, -, hXy, hX⟩ := hy
  have ex : ∀ a, x a = spMap (dir c (Mx a)).toRingHom ≫ X := fun a => ((hX _ (hx a)).2 _).1 (hM a)
  refine ((hX x' hx').2 _).2 ?_
  obtain ⟨U, hU, hpU, -⟩ := Opens.isBasis_iff_nbhd.1 Xo.X.isBasis_affineOpens
    (Opens.mem_top (y.x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)))
  have hyU : ⊤ ≤ y.x ⁻¹ᵁ U := fun s _ => by
    have : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) := Subsingleton.elim _ _
    subst this
    exact hpU
  have hXU : ⊤ ≤ X ⁻¹ᵁ U :=
    le_preimage_of_trivSqZeroExt (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom (fun _ => rfl) X U
      (by rw [hXy]; exact hyU)
  have htan : ∀ z : Sp (DualNumber K) ⟶ Xo.X, IsTanX y z → ⊤ ≤ z ⁻¹ᵁ U := fun z hz =>
    le_preimage_of_trivSqZeroExt (red c K).toRingHom (fun _ => rfl) z U (by rw [hz.2]; exact hyU)
  have hev : ∀ (N : HIx Dw (psiSet H) → K) (z : Sp (DualNumber K) ⟶ Xo.X)
      (hz : z = spMap (dir c N).toRingHom ≫ X) (hzU : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(Xo.X, U)),
      evalPt z U hzU f = dir c N (evalPt X U hXU f) := by
    intro N z hz hzU f
    subst hz
    exact evalPt_spMap_comp _ X U hXU hzU f
  have hx'U := htan x' hx'
  have hcU : ∀ a, ⊤ ≤ x a ⁻¹ᵁ U := fun a => htan _ (hx a)
  set M'' : HIx Dw (psiSet H) → K := ∑ a, m a • Mx a
  have hzU : ⊤ ≤ (spMap (dir c M'').toRingHom ≫ X) ⁻¹ᵁ U := by
    intro s hs
    exact hXU (Set.mem_univ _)
  refine ext_evalPt hU hx'U hzU (RingHom.ext fun f => ?_)
  rw [hev M'' _ rfl hzU f]
  refine TrivSqZeroExt.ext ?_ ?_
  · have e1 := evalPt_spMap_comp (red c K).toRingHom x' U hx'U (by rw [hx'.2]; exact hyU) f
    have e2 := evalPt_spMap_comp (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom X U hXU
      (by rw [hXy]; exact hyU) f
    simp only [hx'.2, hXy] at e1 e2
    rw [fst_dir]
    exact e1.symm.trans e2
  · rw [h U f hx'U hcU, snd_dir]
    simp only [fun a => hev (Mx a) (x a) (ex a) (hcU a) f, snd_dir, M'', Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.FlagTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepContinuousGroupStatement
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwinerRep_continuous_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ f (w : WOF F E nS nT), Continuous fun p : GAF σ JS × GAF σ JT => (Om p f : WOF F E nS nT → ℂ) w := by
  first | exact @GlobalTheory.FinLatF.latRepF_cont | exact GlobalTheory.FinLatF.latRepF_cont | (intros; apply GlobalTheory.FinLatF.latRepF_cont <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepNormalizesHeisenbergFiniteStatement
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwinerRep_normalizes_heisenberg_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GfCF σ JT, ∀ (w₀ : WOF F E nS nT)
          (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ w₀ f →
          (Om (g, h) f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT g h w₀) (Om (g, h) f) := by
  first | exact @GlobalTheory.FinLatHeis.isLatRepF_heis | exact GlobalTheory.FinLatHeis.isLatRepF_heis | (intros; apply GlobalTheory.FinLatHeis.isLatRepF_heis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepSplitPlacePositiveScalarStatement
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwinerRep_splitPlace_positive_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h →
          ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
            (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
              ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) →
            ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ℓ (Om (g, h) f) = (r : ℂ) * ℓ f := by
  first | exact @GlobalTheory.FinLatF.isLatRepF_split | exact GlobalTheory.FinLatF.isLatRepF_split | (intros; apply GlobalTheory.FinLatF.isLatRepF_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepTrivialRealPointsStatement
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwinerRep_trivial_realPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT, ∀ f, Om (g, h) f = f := by
  first | exact @GlobalTheory.FinLatF.IsLatRepF.real_triv | exact GlobalTheory.FinLatF.IsLatRepF.real_triv | (intros; apply GlobalTheory.FinLatF.IsLatRepF.real_triv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.LevRowSucc

open GlobalTheory.AdIsom GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

variable {D : D7}

theorem mem_O_iff {w : Pl D.host.E} (a : Kw w) : a ∈ 𝒪[Kw w] ↔ Valued.v a ≤ 1 := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (Kw w)) Valued.v).le_one_iff_le_one

theorem inBasis_val {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).val i j = cpt w ((β⁻¹ * x * β).val (Fin.cast h i) (Fin.cast h j)) := by
  simp only [inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

theorem ent_of_KO {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (hx : inBasis h β w x ∈ KO (Kw w) (Fin n')) :
    (∀ i j, Valued.v (cpt w ((β⁻¹ * x * β).val i j)) ≤ 1) ∧ ∀ i j, Valued.v (cpt w ((β⁻¹ * x⁻¹ * β).val i j)) ≤ 1 := by
  subst h
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 hx
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := (mem_O_iff _).1 (h1 i j)
    rwa [inBasis_val] at this
  · have := (mem_O_iff _).1 (h2 i j)
    rwa [← map_inv, inBasis_val] at this

theorem KO_of_St {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) {x : GL (Fin n) (Lev.EAf D)}
    (hx : x ∈ St β) : inBasis h β w x ∈ KO (Kw w) (Fin n') := by
  subst h
  obtain ⟨z, rfl⟩ := hx
  have e1 : β⁻¹ * frGL β z * β = intGL D.host.F D.host.E _ z := by
    show β⁻¹ * (β * intGL D.host.F D.host.E _ z * β⁻¹) * β = _
    group
  have e2 : β⁻¹ * (frGL β z)⁻¹ * β = intGL D.host.F D.host.E _ z⁻¹ := by
    rw [← map_inv]
    show β⁻¹ * (β * intGL D.host.F D.host.E _ z⁻¹ * β⁻¹) * β = _
    group
  refine (mem_KO_iff _).2 ⟨fun i j => (mem_O_iff _).2 ?_, fun i j => (mem_O_iff _).2 ?_⟩
  · rw [inBasis_val, e1]
    exact (mem_OA _).1 (z.val _ _).2 w
  · rw [← map_inv, inBasis_val, e2]
    exact (mem_OA _).1 ((z⁻¹).val _ _).2 w

theorem idem_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (Lev.EAf D)}
    (hβ : IsFrame β Λ) {w : Pl D.host.E} {x : GL (Fin n) (Lev.EAf D)}
    (hx : ∀ i j, Valued.v (cpt w ((β⁻¹ * x * β).val i j)) ≤ 1) {y : Fin n → Lev.EAf D} (hy : y ∈ hat Λ) :
    idem w • (x.val *ᵥ y) ∈ hat Λ := by
  rw [mem_hat, hβ] at hy ⊢
  intro i
  have e : (β⁻¹).val *ᵥ (idem w • (x.val *ᵥ y)) = idem w • ((β⁻¹ * x * β).val *ᵥ ((β⁻¹).val *ᵥ y)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [e, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  rw [← mul_assoc]
  exact mul_mem ((idem_mul_mem_iff w _).2 (hx i j)) (hy j)

theorem hA_unitary {V : HSp D} {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ UA D.sp.cm V.gram)
    (a b : Fin V.rank → Lev.EAf D) : hA V (x.val *ᵥ a) (x.val *ᵥ b) = hA V a b := by
  have hx' : Formalism.UG.cT (cjA D) x.val * V.gram.map (inc D) * x.val = V.gram.map (inc D) := hx
  have e2 : ∀ u v : Fin V.rank → Lev.EAf D,
      Formalism.UG.hform (cjA D) (V.gram.map (inc D)) u v = (cjA D ∘ u) ⬝ᵥ (V.gram.map (inc D) *ᵥ v) := by
    intro u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : cjA D ∘ (x.val *ᵥ b) = (cjA D ∘ b) ᵥ* Formalism.UG.cT (cjA D) x.val := by
    funext i
    rw [Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [hA_eq, hA_eq, e2, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hx']

theorem transfer {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hsd : IsSelfDualC V Λ)
    {x : GL (Fin V.rank) (Lev.EAf D)} (hU : x ∈ UA D.sp.cm V.gram) {w : Pl D.host.E}
    (h : ∀ y ∈ hat Λ, idem w • ((x⁻¹).val *ᵥ y) ∈ hat Λ) {y : Fin V.rank → Lev.EAf D} (hy : y ∈ hat Λ) :
    idem (GlobalTheory.IdemSupport.cP w) • (x.val *ᵥ y) ∈ hat Λ := by
  rw [mem_hat_iff_of_selfDual hsd]
  intro z hz
  have e : z = x.val *ᵥ ((x⁻¹).val *ᵥ z) := by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  rw [hA_smul_right, cjA_idem, GlobalTheory.StdFrames.cP_cP, e, hA_unitary hU, ← hA_smul_left]
  exact (mem_hat_iff_of_selfDual hsd y).1 hy _ (h z hz)

theorem givenLevel_succ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (a : ℕ) :
    ∀ b, b ≠ 0 → givenLevel G t w (a + 1, b) = KO (Kw w) (Fin ((locGrid G t w).rank (a + 1, b)))
  | 0, h => absurd rfl h
  | _ + 1, _ => rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem prodLev_inf_UA {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hβ : IsFrame β Λ) (hsd : IsSelfDualC V Λ) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (hn : ∀ w, n' w = V.rank)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (hK : ∀ w, K w = KO (Kw w.1) (Fin (n' w))) :
    prodLev β P hn K ⊓ UA D.sp.cm V.gram = congLev D.sp.cm V.gram Λ ⊤ := by
  rw [congLev_top]
  have key : ∀ g ∈ prodLev β P hn K ⊓ UA D.sp.cm V.gram, ∀ (Q : Pl D.host.E), ∀ y ∈ hat Λ,
      idem Q • (g.val *ᵥ y) ∈ hat Λ := by
    rintro g hg Q y hy
    obtain ⟨hg, hU⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hA', hB'⟩ := Subgroup.mem_inf.1 hg
    have hA : ∀ w : P, (∀ i j, Valued.v (cpt w.1 ((β⁻¹ * g * β).val i j)) ≤ 1) ∧
        ∀ i j, Valued.v (cpt w.1 ((β⁻¹ * g⁻¹ * β).val i j)) ≤ 1 := fun w => by
      have := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hA' w)
      rw [hK] at this
      exact ent_of_KO _ β g w.1 this
    by_cases hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)
    · obtain ⟨w, hw, hQw⟩ := hQ
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP hQw with rfl | rfl
      · exact idem_smul_mem hβ (hA ⟨Q, hw⟩).1 hy
      · exact transfer hsd hU (fun y hy => idem_smul_mem hβ (hA ⟨w, hw⟩).2 hy) hy
    · push_neg at hQ
      have := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hB' Q) hQ)
      exact idem_smul_mem hβ (ent_of_KO _ β g Q this).1 hy
  ext x
  constructor
  · intro hx
    have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).2
      ⟨fun y hy => mem_hat_of_idem hsd.1.fg fun Q => key x hx Q y hy,
        fun y hy => mem_hat_of_idem hsd.1.fg fun Q => key x⁻¹ (inv_mem hx) Q y hy⟩
    obtain ⟨h1, h2⟩ := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).1 hS
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, ?_⟩
    intro y
    refine ⟨fun hy => h1 y hy, fun hy => ?_⟩
    have := h2 _ hy
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
    exact this
  · intro hx
    obtain ⟨hU, hst⟩ := Subgroup.mem_inf.1 hx
    have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).2
      ⟨fun y hy => (hst y).1 hy, fun y hy => (hst _).2 (by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]; exact hy)⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => ?_⟩, hU⟩
    · rw [Subgroup.mem_comap, hK]
      exact KO_of_St _ β w.1 hS
    · rw [Subgroup.mem_comap]
      exact KO_of_St _ β w' hS

end GlobalTheory.FunObj.LevRowSucc

namespace GlobalTheory.FunObj.GridChoice

open GlobalTheory.FunObj.LevRowSucc

theorem levRow_succ_inf_UA {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (i : ℕ) (h : i + 1 ≤ D.R.m) :
    S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram = G.levMax (.grid (i + 1) D.R.m) := by
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  rw [GridData.levMax]
  exact prodLev_inf_UA (S.B.isFrame (i + 1) D.R.m (by omega) h le_rfl)
    (G.isV (X := .grid (i + 1) D.R.m) ⟨h, le_rfl⟩ fun j e => by cases e).sd (locPl G t) _ _
    fun w => givenLevel_succ G t w.1 i D.R.m hm

end GlobalTheory.FunObj.GridChoice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionFramedPointsIsActionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_framedPoints_isAction : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) , R.toLevCh.Is A.μ0 → LawsJ T → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) := by
  first | exact @GlobalTheory.LevelActFromLevel.actLev_of_levIs | exact GlobalTheory.LevelActFromLevel.actLev_of_levIs | (intros; apply GlobalTheory.LevelActFromLevel.actLev_of_levIs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def outer (W : G.Weil) (M : Vol G) {t : T} {i j : ℕ} (d : PureT G (routeSmall t i j)) (F : Fn G (.grid i (j + 1)))
    (g₁ : GA D (G.V (.grid (i + 1) j))) : Fn G (.grid i j) := fun u =>
  W.kerA (.right i j) d.2 u g₁ * ∫ g in M.fd (.grid i (j + 1)), W.kerA (.down t i j) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))

theorem liftT_routeSmall (W : G.Weil) (M : Vol G) {t : T} {i j : ℕ} (τ : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    liftT W M (routeSmall t i j) τ F g₁ = τ.sum fun d c => c * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := by
  simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.SmallRoute
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowH1VanishesGeometricFibreAllStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundlePow_h1Vanishes_geometricFibre_all : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ))) → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) := by
  first | exact @GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all | exact GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all | (intros; apply GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all <;> assumption)
end

