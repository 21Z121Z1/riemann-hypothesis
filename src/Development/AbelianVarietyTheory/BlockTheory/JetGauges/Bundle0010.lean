import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.ScaledBilinearLog
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledBilinearLog

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

section Bilinear

variable {S : Type} [CommRing S] {d : ℕ}

def IsLog (G : Germ.FGLaw S d) (ℓ : Germ.Pt S 1 d) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (ℓ i) = 0) ∧ TB.dLin ℓ = 1 ∧
    Germ.comp1 ℓ (G.add (Germ.pt S (n := 2) d 0) (Germ.pt S (n := 2) d 1)) =
      Germ.comp1 ℓ (Germ.pt S (n := 2) d 0) + Germ.comp1 ℓ (Germ.pt S (n := 2) d 1)

example [Algebra ℚ S] (h : TB.LogSt) (G : Germ.FGLaw S d) : ∃ ℓ, IsLog G ℓ := h S d G

def bilLog (ℓ : Germ.Pt S 1 d) (c : Matrix (Fin d) (Fin d) S) {n : ℕ} (P Q : Germ.Pt S n d) : Germ.PS S n d :=
  ∑ i : Fin d, ∑ j : Fin d, MvPowerSeries.C (c i j) * Germ.comp1 ℓ P i * Germ.comp1 ℓ Q j

def IsSymBal {O : Type} (act : O → Germ.Pt S 1 d) (bar : O → O) (c : Matrix (Fin d) (Fin d) S) : Prop :=
  (∀ u v : Fin d → S, dotProduct u (c.mulVec v) = dotProduct v (c.mulVec u)) ∧
  ∀ (a : O) (u v : Fin d → S),
    dotProduct ((TB.dLin (act a)).mulVec u) (c.mulVec v) =
      dotProduct u (c.mulVec ((TB.dLin (act (bar a))).mulVec v))

example (ℓ : Germ.Pt S 1 d) {n : ℕ} (P Q : Germ.Pt S n d) : bilLog ℓ 0 P Q = 0 := by
  simp [bilLog]

example {O : Type} (act : O → Germ.Pt S 1 d) (bar : O → O) : IsSymBal act bar 0 := by
  simp [IsSymBal]

end Bilinear

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]

def IsScaledBy (y : FrPt Xo c S) (C : ChartAt Xo c y) (ℓ : Germ.Pt S 1 C.d)
    (b : ℕ → Matrix (Fin C.d) (Fin C.d) S)
    (e' : ∀ m, FrTy y C.d C.x m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
    (u : Jet S (Fin 2 × Fin C.d) m) =
      psJet m (Germ.FB.expS S (-(bilLog ℓ (b m) (Germ.pt S (n := 2) C.d 0) (Germ.pt S (n := 2) C.d 1)))) ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m)
      (Formalism.L2.Pj.scaleGen (cφ ![jpt y C.d C.x m (0 : Fin 2), jpt y C.d C.x m (1 : Fin 2)]) (cε 2)
        (unitΓ u) (C.e m))

def SameFamilies (y : FrPt Xo c S) (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m) : Prop :=
  IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e'

def KeepsRig (y : FrPt Xo c S) (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m) : Prop :=
  LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)

def withFrames (y : FrPt Xo c S) (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m)
    (hf : SameFamilies y C e') (hr : KeepsRig y C e') : ChartAt Xo c y where
  d := C.d
  B := C.B
  uvec := C.uvec
  x := C.x
  e := e'
  wP := C.wP
  h := C.h
  chart := C.chart
  frame := hf
  prim := C.prim
  gauge := C.gauge
  rig0 := hr

example (y : FrPt Xo c S) (C : ChartAt Xo c y) : withFrames y C C.e C.frame C.rig0 = C := rfl

def IsTwist (y : FrPt Xo c S) (C : ChartAt Xo c y) (ℓ : Germ.Pt S 1 C.d)
    (b : ℕ → Matrix (Fin C.d) (Fin C.d) S)
    (e' : ∀ m, FrTy y C.d C.x m) : Prop :=
  b 0 = 0 ∧ (∀ m, IsSymBal C.B.A.act H.bar (b m)) ∧ IsScaledBy y C ℓ b e' ∧
    ∃ (hf : SameFamilies y C e') (hr : KeepsRig y C e'), FrTruncC y (withFrames y C e' hf hr)

def twistedSeries (y : FrPt Xo c S) (C : ChartAt Xo c y) (ℓ : Germ.Pt S 1 C.d)
    (b : Matrix (Fin C.d) (Fin C.d) S) (k : ℕ)
    (f : MvPowerSeries (Fin 1 × Fin C.d) S) : MvPowerSeries (Fin 1 × Fin C.d) S :=
  f * Germ.FB.expS S ((k : S) • bilLog ℓ b (Germ.pt S (n := 1) C.d 0) (C.B.A.act H.w0))

end Twist

def TwistExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (ℓ : Germ.Pt S 1 C.d), IsLog C.B.G ℓ →
      ∃ (b : ℕ → Matrix (Fin C.d) (Fin C.d) S) (e' : ∀ m, FrTy y C.d C.x m), IsTwist y C ℓ b e'

def TwistGerm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (ℓ : Germ.Pt S 1 C.d), IsLog C.B.G ℓ →
      ∀ (b : ℕ → Matrix (Fin C.d) (Fin C.d) S) (e' : ∀ m, FrTy y C.d C.x m), IsTwist y C ℓ b e' →
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
        (f : MvPowerSeries (Fin 1 × Fin C.d) S), IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
        ∃ g : MvPowerSeries (Fin 1 × Fin C.d) S, IsGerm y C.d C.x C.B.A.act e' C.wP k F g ∧
          ∀ D : ℕ, psJet D g = psJet D (twistedSeries y C ℓ (b D) k f)

def TwistStatement : Prop := TwistExists ∧ TwistGerm

end GlobalTheory.IndefiniteRowSideFullHecke.ScaledBilinearLog
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.UniformizationClosedSplit
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def PrimeToLevel (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) : Prop :=
  ((l.M' : ℕ) : 𝓞 c.F) ∉ la.asIdeal

def HasModel (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (b : O →+* T.V) (Y : Model Xo c β),
    (∀ x : O, algebraMap T.V T.Fr (b x) = io (β x)) ∧ Y.N3

def ClosedSplit (T : CDVR) (G : SAB H (Sp T.V)) : Prop :=
  ∃ S : SplitExt (Sp (IsLocalRing.ResidueField T.V)),
    S.IsGt ((Over.pullback (spMap (IsLocalRing.residue T.V))).obj G.G)

def HasUnif (T : CDVR) (G : SAB H (Sp T.V)) : Prop :=
  ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) G, P.TorsionIso

variable (Xo : Moduli Dw l) (c : Coeff l)

def ModelAt : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → HasModel Xo c T io

def UnifOfModel : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), HasModel Xo c T io →
    ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1), ClosedSplit T I.G → HasUnif T I.G

def UnifAt : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
      ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1), ClosedSplit T I.G → HasUnif T I.G

variable {Xo c}

theorem unifAt_of (h₁ : ModelAt Xo c) (h₂ : UnifOfModel Xo c) : UnifAt Xo c :=
  fun la hla T io e ho => h₂ T io (h₁ la hla T io e ho)

example {O : Type} [CommRing O] (T : CDVR) (b : O →+* T.V) (n : ℕ) (hn : ¬ IsUnit (n : T.V)) : ¬ IsUnit (n : O) :=
  fun h => hn (by simpa using h.map b)

theorem PrimeToLevel.not_mem_M {la : HeightOneSpectrum (𝓞 c.F)} (h : PrimeToLevel c la) :
    ((l.M : ℕ) : 𝓞 c.F) ∉ la.asIdeal := by
  intro hM
  apply h
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hM

end General

def Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ModelAt Xo c ∧ UnifOfModel Xo c

end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
end
end

