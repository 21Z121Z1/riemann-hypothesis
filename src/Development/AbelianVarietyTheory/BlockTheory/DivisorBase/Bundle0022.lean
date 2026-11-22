import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdaptedStandardBasis
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def IsThetaWt (la : Weight Dw) (n : ℕ) : Prop :=
  8 ∣ n ∧ (∀ τ, Antitone (la τ)) ∧
    (∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) < Dw.p → ((n / 2 : ℕ) : ℤ) ≤ la τ i) ∧
    (∀ τ (i : Fin (Dw.p + Dw.q)), Dw.p ≤ (i : ℕ) → la τ i ≤ -((n / 2 : ℕ) : ℤ)) ∧
    ∀ τ (i k : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (k : ℕ) = Dw.p → (n : ℤ) + 2 < la τ i - la τ k

abbrev thetaG (la : Weight Dw) (n : ℕ) : WTZ E := wtOf Dw la ((n / 2 : ℕ) : ℤ)

def what₂ (la : Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℕ := fun x => ((thetaG Dw la n).1 x).toNat

def size (la : Weight Dw) : ℝ := ∑ τ, ∑ i, |(la τ i : ℝ)|

def degree (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)

def width (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : ℕ := n + 2 * Finset.univ.sup fun τ : E →+* ℂ => a (τ, 0)

example (n : ℕ) (h : 8 ∣ n) :
    IsThetaWt Dw (fun _ i => if (i : ℕ) < Dw.p then ((n / 2 : ℕ) : ℤ) + 1 else -((n / 2 : ℕ) : ℤ) - 2) n := by
  refine ⟨h, fun τ i k hik => ?_, fun τ i hi => ?_, fun τ i hi => ?_, fun τ i k hi hk => ?_⟩
  · have : (i : ℕ) ≤ k := hik
    dsimp only
    split_ifs <;> omega
  · simp [hi]
  · simp [not_lt.2 hi]
  · dsimp only
    split_ifs <;> omega

end Weights

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

def Adapted (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (bad : ℕ) {n : ℕ} (Λ : GenLat E n) : Prop :=
  Λ.Unimod ∧ ∃ I : Ideal (𝓞 E), I ⊔ Ideal.span {(bad : 𝓞 E)} = ⊤ ∧
    (∀ P : Ideal (𝓞 E), P.IsPrime → I ≤ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P) ∧
    I • Λ.La ≤ stdLat E n ∧ I • stdLat E n ≤ Λ.La

def rootDisc (K : Type) [Field K] [NumberField K] : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (finrank ℚ K : ℝ))

variable (Xo : Moduli Dw l) (c : Coeff l)

def polyNorm {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : ℝ :=
  Real.sqrt (∑ s : c.F →+* ℂ, ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2)

variable (Dw) in

def harmRank (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : ℕ :=
  finrank ℚ c.F * finrank c.F (Submodule.span c.F
    (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)))

def IsShortPoly (B : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (Λ : GenLat E n) (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  P ∈ harmL c Λ a ∧ polyNorm c P ≤
    Real.sqrt (((harmRank Dw c a n : ℝ) + 3) / 4) * Real.sqrt (finrank ℚ c.F) * rootDisc c.F *
      Real.exp (13 * ((Dw.p + Dw.q : ℕ) : ℝ) * B * (degree Dw a : ℝ))

variable (Dw) in

def IsBeta {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β

def IsTheta (nab : NabV Xo c) (G : WTZ E) {n : ℕ} (Λ : GenLat E n) (β : c.F) (N : ℕ) (x₀ : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) : Prop :=
  f ∈ secZ Xo c (exZ Dw G) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k),
      ShortValAt Xo c nab (x0Dat (l := l) c x₀) Λ β N P y (evR Xo c f y)

def IsMemberData (bad : ℕ) (B : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (Λ : GenLat E n) (N : ℕ) (x₀ : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Adapted H bad Λ ∧ Λ.LevOK N l.M ∧ AdmX (l := l) false x₀ ∧ IsShortPoly c B a Λ P

def family (nab : NabV Xo c) (bad : ℕ) (B : ℝ) (la : Weight Dw) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (Λ : GenLat E n) (β : c.F) (N : ℕ) (x₀ : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F),
    IsMemberData c bad B (what₂ Dw la n) Λ N x₀ P ∧ IsBeta Dw c Λ β ∧
      IsTheta Xo c nab (thetaG Dw la n) Λ β N x₀ P f}

def Rational (nab : NabV Xo c) (bad : ℕ) (B : ℝ) (la : Weight Dw) (n : ℕ) : Prop :=
  ∀ (Λ : GenLat E n) (N : ℕ) (x₀ : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F),
    IsMemberData c bad B (what₂ Dw la n) Λ N x₀ P →
      (∃ β, IsBeta Dw c Λ β) ∧ ∀ β, IsBeta Dw c Λ β → ∃ f, IsTheta Xo c nab (thetaG Dw la n) Λ β N x₀ P f

variable {Xo c} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def SupLe (x : ℝ) (G : WTZ E) (Z : Comp Xo c) (σ : c.F →+* ℂ) (f : Rul Xo c) (A : ℝ) : Prop :=
  ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) x G f z ≤ Real.exp A

def ShortSpan (x : ℝ) (G : WTZ E) (S : Set (Rul Xo c)) (A A' : ℝ) : Prop :=
  (∀ f ∈ S, f ∈ cuspW Xo c U G) ∧
    (∀ f ∈ S, ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), SupLe U x G Z σ f A) ∧
    (∃ Na : ℕ, 0 < Na ∧ Real.log Na ≤ A' ∧
      ∀ f ∈ S, ∀ h : f ∈ cuspW Xo c U G, (Na • ⟨f, h⟩ : cuspW Xo c U G) ∈ latW U G) ∧
    ∀ Z : Comp Xo c, Submodule.span c.F ((fun f => GlobalTheory.FlatLine.idem Z * f) '' S) = cuspOn U Z G

theorem ShortSpan.mono {x : ℝ} {G : WTZ E} {S : Set (Rul Xo c)} {A A' B B' : ℝ} (h : ShortSpan U x G S A A')
    (hA : A ≤ B) (hA' : A' ≤ B') : ShortSpan U x G S B B' := by
  obtain ⟨h1, h2, ⟨Na, h3, h4, h5⟩, h6⟩ := h
  exact ⟨h1, fun f hf Z σ z hz => (h2 f hf Z σ z hz).trans (Real.exp_le_exp.2 hA), ⟨Na, h3, h4.trans hA', h5⟩, h6⟩

end Family

section Constants

variable (D : D7) (large₂ : SizeData₂ D)

def levelM (e : ℕ) : ℕ := D.host.g 0 * D.host.g 1 * 15 ^ e

def badM (M : ℕ) : ℕ := D.host.QS * D.host.q * D.host.d * M

def constB (M n w dg : ℕ) : ℝ :=
  Real.log M + Real.log (Ideal.absNorm D.host.ccK) + Real.log D.host.rdE +
    Real.log ((D.R.f : ℝ) * D.R.r * n * w * ((dg : ℝ) + 2))

def constP (B : ℝ) : ℝ := (D.R.f : ℝ) * D.R.r * (24 * B + Real.log Real.pi / 2)

def constG (K : Type) [Field K] [NumberField K] (B : ℝ) (p : ℕ) : ℝ :=
  constP D B + (3 * large₂.sc.L + 2 * (Real.log (finrank ℚ K) + Real.log (rootDisc K))) +
    2 * (D.R.f : ℝ) * D.R.r * (WeightAlgebra.lamStar D + 2 * Real.log p) + 31 * zBase large₂

def Page : Prop :=
  (∃ P : ParameterChoice' D large₂, Nonempty (ParamsT D large₂ P)) ∧ SizesAt large₂ ∧ 9 ≤ D.R.r ∧ 10 ≤ large₂.sc.L ∧
    Ideal.absNorm D.host.ccK ≤ D.host.d

end Constants

section Statement

variable (D : D7) (large₂ : SizeData₂ D)

def IsHostOf (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) : Prop :=
  H.d = D.host.d ∧ (H.rt : D.host.E) = D.host.sqrtMinusD ∧ H.rt0 = D.host.φ₀ D.host.sqrtMinusD

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

def Objects (j e : ℕ) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (nab : NabV Xo c) :
    Prop :=
  IsHostOf D H ∧ IsDatW D j Dw ∧
    (4 ≤ e ∧ l.M = levelM D e ∧ l.A = 1 ∧ Real.log l.M ≤ 30 * large₂.sc.L) ∧
    ((∀ y : D.what₂.O, D.what₂.embLL (D.what₂.OtoLL y) ∈ c.F) ∧ KPsiIn (Dw := Dw) c ∧ FnAlgClosed Xo c) ∧
    (∀ σ, GoodEmb c σ → IsUnf (U σ) ∧ ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧
    ∃ _ : StarRing (𝓞 D.host.E), IsNab Xo c nab

def InRange (Dw : Datum H) (la : Weight Dw) (n : ℕ) : Prop :=
  IsThetaWt Dw la n ∧ 8 * D.R.f * D.R.r + 4 ≤ n ∧ (D.R.f : ℝ) * D.R.r * n ≤ large₂.sc.b ∧ size Dw la ≤ large₂.sc.b ^ 2

def constBAt (l : Level H) (Dw : Datum H) (la : Weight Dw) (n : ℕ) : ℝ :=
  constB D l.M n (width (what₂ Dw la n) n) (degree Dw (what₂ Dw la n))

def Concl (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (nab : NabV Xo c)
    (la : Weight Dw) (n p : ℕ) : Prop :=
  Rational Xo c nab (badM D l.M) (constBAt D l Dw la n) la n ∧
    ShortSpan U (xiR D) (thetaG Dw la n) (family Xo c nab (badM D l.M) (constBAt D l Dw la n) la n)
      (constG D large₂ c.F (constBAt D l Dw la n) p * (size Dw la + n)) (31 * zBase large₂ * (size Dw la + n))

def GminAt (j : ℕ) : Prop :=
  ∀ (e : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (nab : NabV Xo c), Objects D large₂ j e Xo c U nab →
    ∀ (la : Weight Dw) (n : ℕ), InRange D large₂ Dw la n →
      ∀ p : ℕ, p = D.host.pde ∨ p = D.host.pde' → Concl D large₂ Xo c U nab la n p

end Statement

def Gmin : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D), Page D large₂ → ∀ j, 1 ≤ j → j < D.R.m → GminAt D large₂ j

def GminWithDefinite : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D), Page D large₂ → ∀ j, 1 ≤ j → j ≤ D.R.m → GminAt D large₂ j

theorem GminWithDefinite.gmin (h : GminWithDefinite) : Gmin := fun D large₂ hP j h1 h2 => h D large₂ hP j h1 h2.le

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.BadPlacesGoodCoefficients

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def badPlaces (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Formalism.L2.DIV.primesOf (((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F))

theorem mem_badPlaces (v : HeightOneSpectrum (𝓞 D.host.F)) :
    v ∈ badPlaces D ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  unfold badPlaces
  rw [Formalism.L2.DIV.mem_primesOf, and_iff_right]
  exact_mod_cast mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

def IsReadingPlaces (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  ∃ pb : Fin 2 → 𝓞 D.host.E, (∀ i, (pb i : D.host.E) ∈ D.host.K) ∧ IsTypePlaces (D := D) D.host.g pb Pg

def IsBelow {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (b : Pg ≃ LevelCuspCharacters.Sq D.host) : Prop :=
  ∀ PP : Pg, (b PP).2.1.asIdeal = PP.1.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))

def toG0 {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (b : Pg ≃ LevelCuspCharacters.Sq D.host)
    (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* Formalism.L2.DIV.kP PP.1) (x : LevelCuspCharacters.LevelGroup D.host) :
    Formalism.L2.DIV.G0 Pg D.R.r :=
  fun PP => Matrix.GeneralLinearGroup.map (φ PP).toRingHom (x (b PP))

def goodCoeff {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (b : Pg ≃ LevelCuspCharacters.Sq D.host)
    (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* Formalism.L2.DIV.kP PP.1)
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) : Formalism.L2.DIV.G0 Pg D.R.r →₀ ℂ :=
  Finsupp.mapDomain (toG0 b φ) (LevelCuspCharacters.goodIdem (H := D.host) om).coeff

def IsFrameAtG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Prop :=
  ∃ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ), IsBaseFrame V β Λ ((D.host.g 0 * D.host.g 1) ^ c)

def datR (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ)
    (fr : Lev.Frm) : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  datY V.rank D.R.r D.R.t 0 hr Pg ∅ P (fun _ _ => 1) (fun _ => 1) fr

def eLin (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (e : Formalism.L2.DIV.G0 L.Pg L.r →₀ ℂ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := eAct V β L e
  map_add' F G := by
    funext h
    simp only [eAct, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  map_smul' a F := by
    funext h
    simp only [eAct, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp

theorem rank_le_first_space_rank (D : D7) : D.R.r ≤ (D.sp.Y 0).rank := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Ranks.rankY]

theorem r_le_rank_Wc (D : D7) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : D.R.r ≤ (D.sp.W j).rank :=
  (D.sp.W_rank j h1 h2).ge

theorem rank_W_eq (D : D7) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (D.sp.W j).rank = (D.sp.Y 0).rank := by
  rw [D.sp.W_rank j h1 h2, D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Ranks.rankY]

section Parts

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}

def rowPart (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (β : GL (Fin (D.sp.Y 0).rank) (EAf D))
    (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ) (e : Formalism.L2.DIV.G0 Pg D.R.r →₀ ℂ)
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  EEpart θ M (levG (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B) : Set (GA D (D.sp.Y 0)))
    (levChi (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B))
    (eLin (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B) e) (badPlaces D) c

def formPart {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))) (β : GL (Fin (D.sp.W j).rank) (EAf D))
    (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ) (e : Formalism.L2.DIV.G0 Pg D.R.r →₀ ℂ)
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  Wpart θ j M (levG (D.sp.W j) β (datR _ (r_le_rank_Wc D h1 h2) Pg P Lev.Frm.A) : Set (GA D (D.sp.W j)))
    (levChi (D.sp.W j) β (datR _ (r_le_rank_Wc D h1 h2) Pg P Lev.Frm.A))
    (eLin (D.sp.W j) β (datR _ (r_le_rank_Wc D h1 h2) Pg P Lev.Frm.A) e) (badPlaces D) c

end Parts

def gramIn (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (EAf D) :=
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) β.val *
    V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * β.val

def Matched (V V' : HSp D) (h : V'.rank = V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) : Prop :=
  ∃ y : GL (Fin V'.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
    (∀ PP ∈ Pg, Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) y = 1) ∧
    gramIn V' (β' * Formalism.L2.DIV.intGL D.host.F D.host.E V'.rank y) = (gramIn V β).submatrix (Fin.cast h) (Fin.cast h)

example (V : HSp D) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (β : GL (Fin V.rank) (EAf D)) : Matched V V rfl Pg β β :=
  ⟨1, fun _ _ => map_one _, by rw [map_one, mul_one]; rfl⟩

def DimPartsFor
    (lv : ∀ (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), (∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ) →
      Formalism.L2.DIV.LevelP Pg D.R.r ℂ)
    (ok : ∀ (D : D7) (V V' : HSp D), V'.rank = V.rank → Finset (Formalism.L2.DIV.Pl D.host.E) →
      GL (Fin V.rank) (EAf D) → GL (Fin V'.rank) (EAf D) → Prop) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsReadingPlaces D Pg →
  ∀ (b : Pg ≃ LevelCuspCharacters.Sq D.host), IsBelow b →
  ∀ (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* Formalism.L2.DIV.kP PP.1)
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), LevelCuspCharacters.IsGeneratorFamily (H := D.host) om →
  ∀ (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ (M₀ : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (β₀ : GL (Fin (D.sp.Y 0).rank) (EAf D)), IsFrameAtG (D.sp.Y 0) β₀ →
  ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, ∃ d : ℕ,
    Module.rank ℂ (rowPart θ M₀ β₀ (lv D Pg ψ) (goodCoeff b φ om) c) = d ∧
    ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
      (M : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))) (β : GL (Fin (D.sp.W j).rank) (EAf D)),
      IsFrameAtG (D.sp.W j) β → ok D (D.sp.Y 0) (D.sp.W j) (rank_W_eq D h1 h2) Pg β₀ β →
      Module.rank ℂ (formPart θ h1 h2 M β (lv D Pg ψ) (goodCoeff b φ om) c) = d

def DimParts : Prop := DimPartsFor (fun D Pg ψ => Formalism.L2.DIV.P0 Pg D.R.r ψ) (fun _ _ _ _ _ _ _ => True)

def DimPartsMatched : Prop :=
  DimPartsFor (fun D Pg ψ => Formalism.L2.DIV.P0 Pg D.R.r ψ) (fun _ V V' h Pg β β' => Matched V V' h Pg β β')

def DimPartsPrincipal : Prop :=
  DimPartsFor (fun D Pg _ => Formalism.L2.DIV.LevelP.triv Pg D.R.r ℂ) (fun _ _ _ _ _ _ _ => True)

def DimPartsSharp : Prop := DimPartsFor (fun D Pg ψ => Formalism.L2.DIV.Psharp Pg D.R.r D.R.k ψ) (fun _ _ _ _ _ _ _ => True)

def DimPartsSharpSym : Prop :=
  DimPartsFor (fun D Pg ψ => Formalism.L2.DIV.PsharpSym Pg D.R.r D.R.rS D.R.k ψ) (fun _ _ _ _ _ _ _ => True)

theorem DimParts.matched (h : DimParts) : DimPartsMatched := by
  intro D L hP θ hθ Pg hPg b hb φ om hom ψ hψ M₀ β₀ hβ₀ c
  obtain ⟨d, h0, hj⟩ := h D L hP θ hθ Pg hPg b hb φ om hom ψ hψ M₀ β₀ hβ₀ c
  exact ⟨d, h0, fun j h1 h2 M β hβ _ => hj j h1 h2 M β hβ trivial⟩

example (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ) :
    (datR V hr Pg P Lev.Frm.A).P = P.conj ∧ (datR V hr Pg P Lev.Frm.B).P = P := ⟨rfl, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.BadPlacesGoodCoefficients

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt
open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
  (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def IsComplexData : Prop :=
  l.A = 1 ∧ ∀ σ, GoodEmb c σ → IsUnf (U σ) ∧
    (∃ Kf th hr, IsLevelK (V σ) l.M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictIsUnif (V σ) (dict σ) Kf th hr) ∧
    FinVol (V σ) ∧ ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D

def partLat (Z : Comp Xo c) (G : WTZ D.host.E) : Submodule (𝓞 c.F) (cuspW Xo c U G) :=
  (latOn U Z G).map ((Submodule.inclusion (cuspOn_le U Z G)).restrictScalars (𝓞 c.F))

def normRes (Z : Comp Xo c) (G : WTZ D.host.E) (σ : c.F →+* ℂ) (f : cuspOn U Z G) : ℝ :=
  petW U (xiR D) V dict G σ f

def degRes (Z : Comp Xo c) (G : WTZ D.host.E) : ℝ := deg (normRes U V dict Z G) (latOn U Z G)

def mass (Z : Comp Xo c) (σ : c.F →+* ℂ) : ℝ :=
  (muQ1 (V (goodOf c σ))
    (classesOver (V (goodOf c σ)) (dict (goodOf c σ)) (framesOn (U (goodOf c σ)) Z))).toReal

def Splits (G : WTZ D.host.E) : Prop :=
  (∀ F : cuspW Xo c U G, (F : Rul Xo c) = ∑ᶠ Z : Comp Xo c, FlatLine.idem Z * (F : Rul Xo c) ∧
    ∃ h : ∀ Z : Comp Xo c, FlatLine.idem Z * (F : Rul Xo c) ∈ cuspOn U Z G,
      (F ∈ latW U G ↔ ∀ Z, (⟨_, h Z⟩ : cuspOn U Z G) ∈ latOn U Z G)) ∧
  (iSupIndep (fun Z : Comp Xo c => cuspOn U Z G) ∧ ⨆ Z : Comp Xo c, cuspOn U Z G = cuspW Xo c U G) ∧
  iSupIndep (fun Z : Comp Xo c => partLat U Z G) ∧ ⨆ Z : Comp Xo c, partLat U Z G = latW U G

def Orthogonal (G : WTZ D.host.E) : Prop :=
  ∀ σ : c.F →+* ℂ,
    (∀ f : ∀ Z : Comp Xo c, cuspOn U Z G,
      petW U (xiR D) V dict G σ (∑ᶠ Z, (f Z : Rul Xo c)) ^ 2 = ∑ᶠ Z, normRes U V dict Z G σ (f Z) ^ 2) ∧
    ∀ (Z : Comp Xo c) (f : cuspOn U Z G),
      normRes U V dict Z G σ f ^ 2 = mass U V dict Z σ * normOn U (xiR D) V dict Z G σ f ^ 2

def Adds (G : WTZ D.host.E) : Prop :=
  (GoodW U (xiR D) V dict G ↔ ∀ Z, GoodOn U (xiR D) V dict Z G) ∧
  (GoodW U (xiR D) V dict G →
    (∀ Z, HasGram (normRes U V dict Z G)) ∧
    rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧
    degW U (xiR D) V dict G = ∑ᶠ Z : Comp Xo c, degRes U V dict Z G ∧
    (∀ Z, rankOn U Z G ≠ 0 → ∀ σ, 0 < mass U V dict Z σ) ∧
    degW U (xiR D) V dict G = ∑ᶠ Z : Comp Xo c, (degOn U (xiR D) V dict Z G -
      (rankOn U Z G : ℝ) / 2 * ((∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) / (finrank ℚ c.F : ℝ))))

def OrthSum : Prop :=
  ∀ (la : Weight Dw) (m : ℤ),
    Splits U (wtOf Dw la m) ∧ Orthogonal U V dict (wtOf Dw la m) ∧ Adds U V dict (wtOf Dw la m)

def ComponentSum : Prop :=
  ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → OrthSum U V dict

def ComponentSumDeep : Prop :=
  ∀ (D : D7) (j e : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
    (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
    InR D j → H.d = D.host.d → (H.rt : D.host.E) = D.host.sqrtMinusD → H.rt0 = D.host.φ₀ D.host.sqrtMinusD →
    IsDatW D j Dw → l.M = D.host.g 0 * D.host.g 1 * 15 ^ e → FnAlgClosed Xo c →
    IsComplexData U (fun _ => D.sp.W j) dict → OrthSum U (fun _ => D.sp.W j) dict

theorem ComponentSum.deep (h : ComponentSum) : ComponentSumDeep :=
  fun D _ _ H Dw l Xo c U dict _ _ _ _ _ _ _ hc => h D H Dw l Xo c _ U _ dict hc

theorem finite_comp : Finite (Comp Xo c) := CompFin.finite_comp Xo c

theorem partLat_le (Z : Comp Xo c) (G : WTZ D.host.E) : partLat U Z G ≤ latW U G := by
  rintro _ ⟨f, hf, rfl⟩
  exact (mem_latOn U).1 hf

theorem isComplexData_of_laws {T : Core D} (h : LawsM T) {j : ℕ} (hj : InR D j) :
    IsComplexData (T.U j) (T.V j) (T.dict j) :=
  ⟨h.pins.2.1.2, fun σ hσ => ⟨h.unf j hj σ hσ, by
    obtain ⟨th, hr, h1, h2⟩ := h.dictU j hj σ hσ
    exact ⟨T.Kf j σ, th, hr, h.pins.2.1.1 ▸ h.levelK j hj σ hσ, h1, h2⟩, h.finVol j hj σ hσ, h.xiAbs j hj σ hσ⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
end
end

