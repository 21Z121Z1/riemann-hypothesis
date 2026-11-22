import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaDictionaryComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

section Ord

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {F : SFam g n ζ}

def OrdGe (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) ∧
    ∃ w : T.V, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def OrdEq (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (x : Ω) (a : ℕ) : Prop :=
  ∃ w : T.Vˣ, M.val (jK T.V ≫ ξ) x = algebraMap T.V (FractionRing T.V) (T.ϖ ^ a * w)

def ThroughU {X : Scheme.{0}} (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ X) (c : X ⟶ F.X) (T : Trait F) (ξ : Sp T.V ⟶ M.Z) : Prop :=
  ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ ξ₀ ≫ u₀ ≫ c = T.y

variable {M}

theorem OrdGe.mem_O {T : Trait F} {ξ : Sp T.V ⟶ M.Z} {x : Ω} {a : ℕ} (h : OrdGe M T ξ x a) :
    x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) :=
  h.1

theorem OrdEq.mem_O {T : Trait F} {ξ : Sp T.V ⟶ M.Z} {x : Ω} {a : ℕ} (h : OrdEq M T ξ x a) :
    x ∈ M.O ((jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V))) := by
  by_contra hx
  obtain ⟨w, hw⟩ := h
  rw [RatModel.val_of_notMem _ hx] at hw
  have h0 : (T.ϖ ^ a * (w : T.V)) = 0 :=
    IsFractionRing.injective T.V (FractionRing T.V) (by rw [← hw, map_zero])
  exact mul_ne_zero (pow_ne_zero _ T.irr.ne_zero) w.ne_zero h0

theorem OrdGe.mono {T : Trait F} {ξ : Sp T.V ⟶ M.Z} {x : Ω} {a b : ℕ} (h : OrdGe M T ξ x a) (hba : b ≤ a) :
    OrdGe M T ξ x b := by
  obtain ⟨hx, w, hw⟩ := h
  refine ⟨hx, T.ϖ ^ (a - b) * w, ?_⟩
  rw [hw, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hba]

theorem OrdGe.add {T : Trait F} {ξ : Sp T.V ⟶ M.Z} {x y : Ω} {a : ℕ} (hx : OrdGe M T ξ x a) (hy : OrdGe M T ξ y a) :
    OrdGe M T ξ (x + y) a := by
  obtain ⟨hx0, w, hw⟩ := hx
  obtain ⟨hy0, w', hw'⟩ := hy
  have hsp : ∀ v, (jK T.V ≫ ξ) v ⤳ (jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V)) := fun v => by
    rw [Subsingleton.elim v (IsLocalRing.closedPoint (FractionRing T.V))]
  refine ⟨Subalgebra.add_mem _ hx0 hy0, w + w', ?_⟩
  rw [RatModel.val_add hsp hx0 hy0, hw, hw', ← map_add, mul_add]

theorem OrdGe.mul {T : Trait F} {ξ : Sp T.V ⟶ M.Z} {x y : Ω} {a b : ℕ} (hx : OrdGe M T ξ x a) (hy : OrdGe M T ξ y b) :
    OrdGe M T ξ (x * y) (a + b) := by
  obtain ⟨hx0, w, hw⟩ := hx
  obtain ⟨hy0, w', hw'⟩ := hy
  have hsp : ∀ v, (jK T.V ≫ ξ) v ⤳ (jK T.V ≫ ξ) (IsLocalRing.closedPoint (FractionRing T.V)) := fun v => by
    rw [Subsingleton.elim v (IsLocalRing.closedPoint (FractionRing T.V))]
  refine ⟨Subalgebra.mul_mem _ hx0 hy0, w * w', ?_⟩
  rw [RatModel.val_mul hsp hx0 hy0, hw, hw', ← map_mul, pow_add]
  congr 1
  ring

variable (M)

def LocTuples {X : Scheme.{0}} (U₀ : M.Z.Opens) (u₀ : U₀.toScheme ⟶ X) (c : X ⟶ F.X) (φ : InvFun ℤ) (ι : ℕ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → Ω),
    (∀ k j, t k j ≠ 0) ∧ ∀ x : M.Z, ∃ k, ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ u₀ c T ξ →
      ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧
        (∀ j, OrdGe M T ξ (t k j) a) ∧ ∃ j, OrdEq M T ξ (t k j) a

end Ord

def TraitExtSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (T : Trait F) (f : V →+* T.V) (fK : FractionRing V →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧
        f.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap T.V _ (f a)) ∧ T.y = spMap fK ≫ y

def TraitUniqSt : Prop :=
  ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T T' : Trait F) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W] (f : T.V →+* W) (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W)
    (fK' : FractionRing T'.V →+* FractionRing W), GlobalTheory.Mum.Base W → IsDiscreteValuationRing W →
    Function.Injective f → Function.Injective f' → IsLocalHom f → IsLocalHom f' →
    (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) →
    spMap fK ≫ T.y = spMap fK' ≫ T'.y → ∀ (w : W) (m m' : ℕ), Irreducible w → Associated (f T.ϖ) (w ^ m) →
      Associated (f' T'.ϖ) (w ^ m') →
      ∃ e : T.D.toPre.X ≃+ T'.D.toPre.X, ∀ a b, (m : ℤ) * T.β a b = m' * T'.β (e a) (e b)

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop
open scoped ENNReal

namespace GlobalTheory.CovHt

def cost {K : Type} [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ) (t : (K →+* ℂ) → ℝ) : ℝ :=
  ((e.sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) + ∑ σ, t σ) / (Module.finrank ℚ K : ℝ)

example {K : Type} [Field K] [NumberField K] (s : ℝ) : cost (K := K) 0 (fun _ => s) = s := by
  have h : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  simp [cost, NumberField.Embeddings.card, h]

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7}
  (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def depthOn (Z : Comp Xo c) (G : WTZ E) (v : Rul Xo c → EReal) : EReal := ⨅ w ∈ latOn U Z G, v (w : Rul Xo c)

def smallL (Z : Comp Xo c) (G : WTZ E) (τ : ℕ) (t : ℝ) : Set (cuspOn U Z (τ • G)) :=
  {f | (∀ la, ∀ v ∈ (recVals Xo c).1 la, (τ : EReal) * depthOn U Z G v ≤ v (f : Rul Xo c)) ∧
    ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      ENNReal.ofReal (homN (U σ) x (τ • G) f ⟨y.1, y.2.1⟩) ^ 2 ≤
        ENNReal.ofReal (Real.exp (2 * τ * t)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ τ}

def volL (a : ℕ) (Z : Comp Xo c) (G : WTZ E) (t : ℝ) : ℝ≥0∞ :=
  countVol (dimFlag Dw) (Module.finrank ℚ c.F) a fun τ => (smallL U x V dict Z G τ t).encard

def FinBd (Z : Comp Xo c) (G : WTZ E) (a : ℕ) (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, (∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤) →
    (a : EReal) * depthOn U Z G v ≤ v θ + ((a * e la : ℝ) : EReal)

def NoBase (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, ∀ G' : WTZ E, ∀ f ∈ cuspOn U Z G', v f ≠ ⊤ → ∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤

def InfBd (Z : Comp Xo c) (G G₀ : WTZ E) (a : ℕ) (θ : Rul Xo c) (t : (c.F →+* ℂ) → ℝ) : Prop :=
  (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) ∧
  ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
    ENNReal.ofReal (homN (U σ) x G₀ θ ⟨y.1, y.2.1⟩) ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * a * t σ)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ a

def Carries (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (θ : Rul Xo c) : Prop :=
  θ ∈ secZ Xo c (exOf Dw ((8 : ℤ) • (u - u')) 0) ∧ genVal Z θ ≠ 0 ∧
    ∀ (k : ℕ), ∀ f ∈ cuspOn U Z ((8 * k) • wtOf Dw u' 0), θ ^ k * f ∈ cuspOn U Z ((8 * k) • wtOf Dw u 0)

def Mult (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (cc : ℝ) : Prop :=
  NoBase U Z (wtOf Dw u 0) ∧ ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ),
    Carries U Z u u' θ ∧ FinBd U Z (wtOf Dw u 0) 8 θ e ∧
    InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc

def l1 (u : AllWt.Weight Dw) : ℝ := ∑ τ, ∑ i, |(u τ i : ℝ)|

variable (E) in

def htEx (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) + 40 * ((padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ))

variable (Xo c) in

def HTCmp : Prop := ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal →
  ∀ v ∈ (recVals Xo c).1 la, ∃ w ∈ (htVals Xo c).1 la, ∀ (u : AllWt.Weight Dw), ∀ f ∈ secZ Xo c (exOf Dw u 0),
    w f ≤ v f + (((vLa la (p : c.F) : ℝ) * htEx E p * l1 u : ℝ) : EReal)

variable (l) in

def htCost (B : ℝ) : ℝ := ∑ᶠ p ∈ htPrimes l B, htEx E p * Real.log p

def WtGap (u : AllWt.Weight Dw) (g : ℝ) : Prop :=
  0 < g ∧ (∀ τ, StrictAnti (u τ)) ∧ ∀ τ (a b : Fin (Dw.p + Dw.q)), Dw.p ≤ (a : ℕ) → a ≠ b → g ≤ |(u τ a : ℝ) - u τ b|

def bndB (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  4 * (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (1 + (⨆ k : Psi H × Fin (Dw.p + Dw.q), |(u k.1 k.2 : ℝ)|) / g)

def errX (s : ℝ) (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  (Real.log (bndB u g) + s) * l1 u + (Dw.q : ℝ) * ∑ τ, ((⨆ i, (u τ i : ℝ)) - ⨅ i, (u τ i : ℝ))

def MeanGe (u : AllWt.Weight Dw) (B X : ℝ) : Prop :=
  ∃ sl : Comp Xo c → ℝ, (∀ Z, (sl Z : EReal) ≤ compVolSlope U x 8 (mixVals Xo c B) Z u) ∧
    -X ≤ (∑ᶠ Z, sl Z) / (Nat.card (Comp Xo c) : ℝ)

def MeanAll (s C : ℝ) : Prop := ∀ (u : AllWt.Weight Dw) (g : ℝ), WtGap u g → MeanGe U x u (bndB u g) (C * errX s u g)

end Generic

def ell (D : D7) : ℝ := Real.log D.host.rdE + |dlogL D 1|

section One

open MvPolynomial Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs

variable {D : D7} (Y : ShimX D.what₂.Tau)

def DeRhamMinusHodgeTateGoodPrimesAt : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ Y.lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau Y.N + 1 → ∀ Q : MvPolynomial (Vm D.what₂.Tau Y.N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) m →
    Y.arMix Sx R p ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * collapse D _ Q)) -
        Y.chern (chLie Y.j (k - 1) (Sum.inl τ) * collapse D _ Q) / ((p : ℝ) - 1))

def DeRhamHodgeTateDifferenceKilledAt : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau Y.N) ℝ,
    Y.arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) * (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

example (V : DivX D) (P : DIV.Align.PrinLev V) : LatticeTransfer.PointsLemma D V P ↔
    ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → DeRhamMinusHodgeTateGoodPrimesAt (V.shv S κ) := Iff.rfl

example (V : DivX D) (P : DIV.Align.PrinLev V) : WeightThresholdDefs.TrivialFlagIntersectionCond V P ↔
    ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → DeRhamHodgeTateDifferenceKilledAt (V.shv S κ) := Iff.rfl

end One

open GlobalTheory.Mean4O in

def SlopeSt : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) → GlobalTheory.Mean4.FewBad O.Y →
  GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.VolEq O.Y ∧ GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean.SlopeMean O.Y C

open GlobalTheory.ShFam in

def SrcSt : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ),
  N - j < j → j < N → 2 < D.R.f * (N - 1) → κ.primes.card ≤ 15 →
    MeanAll (Xo := s.Xo) (c := κ.c) (r := N) (fun σ => GlobalTheory.ThetaDictCompare.toU (s.U σ)) (xiR D) (ell D) C

def DeepSt : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ j → j < D.R.m →
  ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o →
    Y.d.l₂.M'.primeFactors.card ≤ 15 → MeanAll Y.U (xiR D) (ell D) C

section Obj

open GlobalTheory.Mean4 GlobalTheory.Mean4O Formalism.BasicNotions.DV

def OnObj (Q : ∀ (D : D7) (O : Setup D) (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H → Prop) : Prop :=
  ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H), Q D O A T H h

def NefAt {D : D7} {Y : ShimX D.what₂.Tau} (A : SlopeTestRemainingChoices Y) : Prop := ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (s : ℚ), IsRat Y u → 0 < s →
  WeightThresholdDefs.Dominant Y (A.sh u s) → NefCond Y B (A.sh u s) → Y.semipos (Y.Mbar B u s) → Y.nefFib (Y.Mbar B u s)

def SemiposAt {D : D7} {Y : ShimX D.what₂.Tau} (A : SlopeTestRemainingChoices Y) : Prop := ∀ Λ : ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ B : ℝ, 2 ≤ B →
  ∀ (u : Wt Y) (s : ℚ), IsRat Y u → Formalism.MainNotions.WeightThresholdDefs.supAbs Y u ≤ Λ → 0 < s → (s : ℝ) ≤ s₀ → WeightThresholdDefs.Dominant Y (A.sh u s) →
    NefCond Y B (A.sh u s) → Y.semipos (Y.Mbar B u s)

theorem NefAt.positive {D : D7} {Y : ShimX D.what₂.Tau} {A : SlopeTestRemainingChoices Y} (h : NefAt A) (hs : SemiposAt A) : Positive A :=
  fun Λ => have ⟨s₀, h₀, hs⟩ := hs Λ
    ⟨s₀, h₀, fun B hB u s hu hΛ h₁ h₂ hd hn =>
      ⟨hs B hB u s hu hΛ h₁ h₂ hd hn, h B hB u s hu h₁ hd hn (hs B hB u s hu hΛ h₁ h₂ hd hn)⟩⟩

open Filter Topology in

theorem semiposAt_of_famS {D : D7} {Y : ShimX D.what₂.Tau} {T : Real0 Y} {A : SlopeTestRemainingChoices Y} (hF : ∀ c, (T.F c).FamS)
    (hM : TieM T A) : SemiposAt A := fun Λ => by
  choose s₀ hs₀ K hK using fun c => hF c (Λ + ‖A.dir‖)
  obtain ⟨s₁, hs₁, hs1, hle⟩ : ∃ s₁ : ℝ, 0 < s₁ ∧ s₁ ≤ 1 ∧ ∀ c, s₁ ≤ s₀ c := by
    have : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 ∧ ∀ c, s ≤ s₀ c := by
      refine eventually_mem_nhdsWithin.and (Eventually.filter_mono nhdsWithin_le_nhds ?_)
      exact (eventually_le_nhds zero_lt_one).and (eventually_all.2 fun c => eventually_le_nhds (hs₀ c))
    exact this.exists
  refine ⟨s₁, hs₁, fun B hB u s hu hΛ hs hss hdom _ => ?_⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hL : 0 ≤ Λ := (Real.iSup_nonneg fun _ => abs_nonneg _).trans hΛ
  have a2 : ‖u‖ ≤ Λ := (pi_norm_le_iff_of_nonneg hL).2 fun τ => (pi_norm_le_iff_of_nonneg hL).2 fun i =>
    (le_ciSup (f := fun x : Rt D.what₂.Tau Y.N => |u x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)).trans hΛ
  have hn : ‖A.sh u s‖ ≤ Λ + ‖A.dir‖ := by
    have e : A.sh u s = u - (s : ℝ) • A.dir := by ext τ i; simp [SlopeTestRemainingChoices.sh]
    have a1 := norm_sub_le u ((s : ℝ) • A.dir)
    rw [norm_smul, Real.norm_of_nonneg hs'.le] at a1
    have a3 := mul_le_of_le_one_left (norm_nonneg A.dir) (hss.trans hs1)
    rw [e]; linarith
  have key := fun c σ => hK c (A.sh u s) hdom hn s hs' (hss.trans (hle c)) σ
  exact ((hM B hB u s hu hs).2 hdom fun c σ => (key c σ).1).2.2 fun c σ => (key c σ).2.1

def HtIntSt : Prop := OnObj fun _ _ _ _ H _ => HtInt H

def HtBdSt : Prop := OnObj fun _ _ _ _ H _ => HtBd H

def HtUpSt : Prop := OnObj fun _ _ A _ H _ => HtUp A H

def RegSt : Prop := OnObj fun _ _ _ T _ _ => ∀ c, (T.F c).InS

def TestSt : Prop := ∃ r : ℝ, OnObj fun D O _ _ _ _ => ∀ hh : Fn O.Y, GlobalTheory.FlagZ.IsHh D.what₂.Tau O.Y.N hh →
  ∀ Φ : ℝ → Fn O.Y, LimFam Φ → TestVal Φ hh r

def AntiSt : Prop := OnObj fun D O _ _ _ _ => ∀ hh : Fn O.Y, GlobalTheory.FlagZ.IsHh D.what₂.Tau O.Y.N hh →
  ∀ Φ : ℝ → Fn O.Y, LimFam Φ → Antisym Φ hh

structure Known₂ : Prop where
  int : HtIntSt
  bd : HtBdSt
  up : HtUpSt
  reg : RegSt
  test : TestSt
  anti : AntiSt

structure HypothesesH : Prop where
  sieg : GlobalTheory.Published.SiegelToroidalIntegral
  fan : GlobalTheory.Published.ToroidalChartsForFan
  charts : GlobalTheory.Published.ToroidalCharts
  deg : GlobalTheory.Published.ArDegree

def InputsSt : Prop := ∃ r Cf : ℝ, ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) → FewBad O.Y →
  ∃ (A : SlopeTestRemainingChoices O.Y) (Φ : ℝ → Fn O.Y) (hh : Fn O.Y), Inputs A Φ hh r Cf

end Obj

end GlobalTheory.CovHt

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KeyEven

def KeyOn {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (σ : L.L.Sec) (y : Fin x.P.g → (epsR R ⟶ G)) : Prop :=
  ∃ (φ : x.P.A.left ⟶ G.left) (he : eSec x.P.A ≫ φ = spMap f ≫ eSec G) (ψ : LB.Iso x.P.L (L.L.pull φ))
    (F : DualNumber R →+* DualNumber K),
    IsGrpPullback x.P.A G (spMap f) φ ∧ ψ.IsGen ∧
    LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap f) he L.L L.rig) ∧
    (∀ (j : (L.L.pull φ).ι) (i : x.P.L.ι) (h : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ L.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (σ.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (L.L.pull φ).U j ⊓ x.P.L.U i) from (ψ.s (j, i)).val) * resG _ inf_le_right (x.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap K _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x.v i).left ≫ φ = spMap F ≫ (y i).left

def HasUnif {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (L : LB G.left) : Prop :=
  ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V)))
    (U : Unif (IsLocalRing.maximalIdeal V) D A G), LBIso U.LG.L L

def UnifAlong {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ ξ : Sp V ⟶ S, (ξ ⁻¹' abLocus G).Nonempty → ∀ [IsCommMonObj ((Over.pullback ξ).obj G)],
      HasUnif ((Over.pullback ξ).obj G) (L.pull (pullback.fst G.hom ξ))

def PolOnAb {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) : Prop :=
  ∀ W : S.Opens, (W : Set S) ⊆ abLocus G →
    RelAmple ((Over.pullback W.ι).obj G) (L.pull (pullback.fst G.hom W.ι)) ∧
    KTriv ((Over.pullback W.ι).obj G) (L.pull (pullback.fst G.hom W.ι))

def NzFib {S : Scheme.{0}} {G : Over S} {L : LB G.left} (σ : L.Sec) : Prop :=
  ∀ s : S, ∃ z : G.left, G.hom z = s ∧ z ∈ nonzeroLocus σ

def KeyTrait (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn (FractionRing V))
      (y : Fin x.P.g → (epsR V ⟶ G)), IsSemiAbelian G → HasUnif G L.L → IsLieBasis y → NzFib σ →
      KeyOn (algebraMap V (FractionRing V)) x G L σ y →
      ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u

def KeyTraitU (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre),
    GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig → ∀ y : Fin x.P.g → (epsR V ⟶ G), IsLieBasis y →
    (∀ i, GlobalTheory.IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i)) →
    ∀ σ : U.LG.L.Sec, NzFib σ →
      GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull x.th U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) →
      ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u

def KeyLoc (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Algebra.FiniteType ℤ A]
    (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn (FractionRing A))
    (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → SmoothOfRelativeDimension x.P.g G.hom → IsOpen (abLocus G) →
    L.IsSymmetric → PolOnAb G L.L → UnifAlong G L.L → IsLieBasis y → NzFib σ →
    KeyOn (algebraMap A (FractionRing A)) x G L σ y →
    ∃ u : Aˣ, (κ (FractionRing A) x : FractionRing A) = algebraMap A (FractionRing A) u

def KeyGlob : Prop :=
  ∀ (S : Scheme.{0}) (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → IsIntegral S → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge G g) 4)

end GlobalTheory.KeyEven

end
end

