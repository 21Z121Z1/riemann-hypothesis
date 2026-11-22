import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalRingCardinality.DataParams

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GoodLiftPhase
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

section Interface

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}

def RatTest (X : CxData A) : Prop :=
  ∀ (j : Bs.J) (t : Bs.Tup), ∃ (n : ℕ) (l : Fin n → (X.W j →ₗ[ℂ] ℂ)),
    (∀ w : X.W j, (∀ k, l k w = 0) → w = 0) ∧
      ∀ (x : A.FL j t) (k : Fin n), ∃ a : K, l k (X.θ' j t (X.jL j t x)) = Bs.v0.embedding a

def KerRat (X : CxData A) : Prop :=
  ∀ (j : Bs.J) (t : Bs.Tup),
    LinearMap.ker (X.θ' j t) = Submodule.span ℂ {u | ∃ x : A.FL j t, X.jL j t x = u ∧ X.θ' j t u = 0}

def LevelRat (X : CxData A) (b : Bool) (V : ∀ j t, Submodule K (A.FL j t)) : Prop :=
  ∀ (j : Bs.J) (t : Bs.Tup), ∀ x ∈ V j t,
    ∃ y : Fin (X.dW b j) → K, X.θ' j t (X.jL j t x) = X.w0C b j (cpt Bs.v0.embedding y)

def withLift (X : CxData A) (θ : ∀ j t, X.FLC j t →ₗ[ℂ] X.W j) : CxData A := { X with θ' := θ }

end Interface

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def liftLvl (F : Face D A) (b : Bool) : Lvl D.what₂.LL G := A.fam.lvlA (F.lvl b).P (F.lvl b).ψ

def goodLift (F : Face D A) (b : Bool) (j : Fin D.R.m) (t : T) : Submodule D.what₂.LL (A.fam.amb.FL j t) :=
  LinearMap.range ((A.fam.L j t).S.gaOp (A.fam.L j t).r (goodAt (liftLvl F b).X (liftLvl F b).P (liftLvl F b).ψ))

def cxPhase (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : CxData A.fam.amb :=
  withLift (R.toCx F) fun j t =>
    Tw.map (E := (R.HV j t).H) (F := (R.HW j (sg0 D A)).H) (twAt D.what₂.embLL A.v0) (ph j • R.thG j t)

def LiftKerTest (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : Prop := RatTest (cxPhase R F ph)

def LiftKerSpan (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : Prop := KerRat (cxPhase R F ph)

def LiftBaseRat (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : Prop :=
  LevelRat (cxPhase R F ph) false (goodLift F false)

def LiftsRational (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) : Prop :=
  (∀ j, ‖ph j‖ = 1) ∧ LiftKerTest R F ph ∧ LiftBaseRat R F ph

theorem liftWeight_complexPoint_eq_twist (R : RealDat D A Ks) (F : Face D A) (b : Bool) (j : Fin D.R.m)
    (y : Fin (Module.finrank D.what₂.LL (R.WL F b j)) → D.what₂.LL) :
    Tw.out (s := twAt D.what₂.embLL A.v0) (E := (R.HW j (sg0 D A)).H) ((R.toCx F).w0C b j (cpt A.v0.embedding y)) =
      (R.FW j).j (sg0 D A) (∑ k, y k • R.bL F b j k) := by
  have hn : (((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)) * (((Real.sqrt (RealDat.nP F b))⁻¹ : ℝ) : ℂ) = 1 := by
    have h0 : 0 < RealDat.nP F b := by
      unfold RealDat.nP
      exact_mod_cast Nat.card_pos
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 h0).ne', Complex.ofReal_one]
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : (R.toCx F).w0C b j (cpt A.v0.embedding y) =
      ∑ k, A.v0.embedding (y k) • (R.toCx F).eW b j ((R.toCx F).bW b j A.v0 k) := by
    simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum, map_smul]
    rfl
  rw [h1, map_sum]
  have h2 : ∀ (s : Bool) (f : Fin (Module.finrank D.what₂.LL (R.WL F b j)) → Tw s (R.HW j (sg0 D A)).H),
      Tw.out (∑ k, f k) = ∑ k, Tw.out (f k) := fun _ _ => rfl
  refine (h2 _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [map_smulₛₗ]
  show cj (twAt D.what₂.embLL A.v0) (A.v0.embedding (y k)) •
    ((((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F b))⁻¹ : ℝ) : ℂ) •
      (R.FW j).j (sg0 D A) (R.bL F b j k))) = _
  rw [smul_smul (((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ)), hn, one_smul, R.emb0, cj_cj]
  congr 1
  exact (DFunLike.congr_fun hs (y k)).symm

theorem twMap_smul {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    (s : Bool) (c : ℂ) (f : E →ₗ[ℂ] E') : Tw.map s (c • f) = cj s c • Tw.map s f := by
  ext u
  show c • f (Tw.out u) = cj s (cj s c) • f (Tw.out u)
  rw [cj_cj]

theorem cxPhase_eq (R : RealDat D A Ks) (F : Face D A) (ph : Fin D.R.m → ℂ) :
    cxPhase R F ph = withLift (R.toCx F) fun j t => cj (twAt D.what₂.embLL A.v0) (ph j) • (R.toCx F).θ' j t :=
  congrArg (withLift (R.toCx F)) (funext fun j => funext fun t => twMap_smul _ (ph j) (R.thG j t))

end GlobalTheory.IndefiniteRowSideFullHecke.GoodLiftPhase

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.InfinityTypes
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Arith

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

abbrev pS : ℕ := ((Wc D i).sig (tauE D τ)).1

abbrev qS : ℕ := ((Wc D i).sig (tauE D τ)).2

abbrev eS : ℚ := (D.hc τ).e i

abbrev aP (a : ℕ) : ℕ := aPl D i (pS D i τ) τ a

abbrev aM (a : ℕ) : ℕ := aMi D i (pS D i τ) (qS D i τ) τ a

def centred (a : ℕ) : ℚ := Formalism.L2.NTheta.lamAt (D.hc τ) a + eS D i τ

def aPlusQ (a : ℕ) : ℚ := centred D i τ a - ((pS D i τ : ℚ) - ((a : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2

def dRowQ (c : ℕ) : ℚ := centred D i τ (pS D i τ + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2

def dShift : ℚ := ((pS D i τ : ℚ) - (qS D i τ : ℚ)) / 2 - eS D i τ - 1 / 2

def thetaWt (a : ℕ) : ℤ :=
  if a < pS D i τ then (aP D i τ a : ℤ)
  else if a < pS D i τ + D.R.t then 0
  else -(aM D i τ (qS D i τ - 1 - (a - (pS D i τ + D.R.t))) : ℤ)

def IsDataOf (w : IndefiniteWeightData.WeightData) : Prop :=
  w.k = D.R.k ∧ w.m = D.R.m ∧ w.t = D.R.t ∧ w.j = (i : ℕ) + 1 ∧ (w.e : ℚ) = eS D i τ ∧
    (∀ a : Fin (D.R.k - 1), (w.v (a + 2) : ℚ) = (D.hc τ).v a) ∧ ∀ a : Fin D.R.m, (w.b (a + 1) : ℚ) = (D.hc τ).b a

structure ArithAt : Prop where

  sig : pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1)

  rank : pS D i τ + qS D i τ = D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t

  aP_eq_rat : ∀ a < pS D i τ, (aP D i τ a : ℚ) = aPlusQ D i τ a

  aM_eq : ∀ c < qS D i τ, (aM D i τ (qS D i τ - 1 - c) : ℚ) = -dRowQ D i τ c

  aPlus_antitone : ∀ a b, a ≤ b → b < pS D i τ → aP D i τ b ≤ aP D i τ a

  aM_anti : ∀ a b, a ≤ b → b < qS D i τ → aM D i τ b ≤ aM D i τ a

  aPlus_pos : ∀ a < pS D i τ, 1 ≤ aP D i τ a

  aM_pos : ∀ a < qS D i τ, 1 ≤ aM D i τ a

  kap_plus : ∀ a : Fin (pS D i τ),
    (Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl a) : ℚ) =
      (aP D i τ a : ℚ) + ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ

  kap_minus : ∀ c : Fin (qS D i τ),
    (Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℚ) =
      -(aM D i τ (qS D i τ - 1 - c) : ℚ) - ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ

  d_int : ∃ z : ℤ, dShift D i τ = z

  lamPrime_eq : ∀ w : IndefiniteWeightData.WeightData, IsDataOf D i τ w → ∀ a < D.R.r + D.R.t,
    w.lamPrime (a + 1) = (thetaWt D i τ a : ℚ) + dShift D i τ

  coef_isLamPrime : Bridge.IsLamPrime (D := D) (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ) ((i : ℕ) + 1) τ

  coef_eq : ∀ a : Fin (Vc D i).rank,
    ((Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w a : ℚ) = (thetaWt D i τ a : ℚ) + dShift D i τ

end Arith

structure InfTypesAt {D : D7} {T : Type} (L : LevCh D T) (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) : Prop where

  mu : HasInfExp D (L.mu t ((i : ℕ) + 1)) τ (-eS D i τ)

  eta : HasInfExp D L.eta τ (1 / 2)

  chiV : HasInfExp D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 τ (-eS D i τ)

  chiW : HasInfExp D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 τ (-eS D i τ - 1 / 2)

def WeightsMatch : Prop :=
  (∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ArithAt D i τ) ∧
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), InfTypesAt R.toLevCh i t τ

def WeightsMatchLev : Prop :=
  (∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ArithAt D i τ) ∧
  ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 →
    ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), InfTypesAt L i t τ

example (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (h : pS D i τ + qS D i τ = D.R.r) :
    (∀ a : Fin (pS D i τ), Formalism.L2.NTheta.kapQ (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl a) =
      aPlusQ D i τ a + ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ) ∧
    ∀ c : Fin (qS D i τ), Formalism.L2.NTheta.kapQ (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) =
      dRowQ D i τ c - ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ := by
  have h' : (D.R.r : ℚ) = (pS D i τ : ℚ) + (qS D i τ : ℚ) := by exact_mod_cast h.symm
  refine ⟨fun a => ?_, fun c => ?_⟩
  · simp only [Formalism.L2.NTheta.kapQ, Sum.elim_inl, aPlusQ, centred, h']; ring
  · simp only [Formalism.L2.NTheta.kapQ, Sum.elim_inr, dRowQ, centred, h']; ring

example (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) :
    (pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1)) ∧ (Vc D i).rank = D.R.r + D.R.t := by
  have h := D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D τ)
  refine ⟨⟨?_, ?_⟩, D.sp.V_rank _ (Nat.le_add_left _ _) i.2⟩
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = _
    rw [h]; simp [Ranks.sigW]
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).2 = _
    rw [h]; rfl

end GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KappaLambdaEmbedding
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.KappaLambdaEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

variable (D) in

abbrev Eig : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

open Classical in

def badF : Finset (HeightOneSpectrum (𝓞 D.host.F)) := R.Pg.image fun PP => PP.under (𝓞 D.host.F)

def rowsAt (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ R.HE.H := (R.EEat P).comap R.HE.e

def rowPart (c : Eig D) : Submodule ℂ R.HE.H :=
  (partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badF R) c ⊓
    R.EEat R.triv).comap R.HE.e

def rowLabels : Set (Eig D) :=
  {c | (fun P d => c P (dualLab d)) ∈
    IxFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badF R) R.e0}

def liftPart (i : Fin D.R.m) (c : Eig D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (badF R) c ⊓
    R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e

def lamFull (i : Fin D.R.m) (t : T) (c : Eig D) : ℝ :=
  (LinearMap.trace ℂ (R.HW i (sg0 D A)).H
    (R.thG i t ∘ₗ LinearMap.adjoint (R.thG i t) ∘ₗ
      ((liftPart R F i c).starProjection : (R.HW i (sg0 D A)).H →ₗ[ℂ] (R.HW i (sg0 D A)).H))).re /
    (Module.finrank ℂ (liftPart R F i c) : ℝ)

def ScalarIdentity (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ t, ∀ c ∈ rowLabels R, (∀ i, 0 < lamFull R F i t c) ∧
    ∀ x ∈ rowPart R c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ * ∏ i, lamFull R F i t c : ℝ) : ℂ) • x

def datXP (t : T) (P : LevelP R.Pg D.R.r ℂ) : LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X R.Pg (R.Q t) P R.chi (R.xiR t) Frm.B

def scal (t : T) : (R.HX t).H →ₗ[ℂ] (SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) := R.cX.toMap R.prX ∘ₗ (R.HX t).e

def formsAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H where
  carrier := {x | ∀ v, HasType D.sp.X' R.βX (datXP R t P) (scal R t x v)}
  add_mem' := by
    intro x y hx hy v κ hκ h
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hx v κ hκ h, hy v κ hκ h, mul_add]
  zero_mem' := by
    intro v κ _ h
    simp
  smul_mem' := by
    intro a x hx v κ hκ h
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, hx v κ hκ h, smul_eq_mul]
    ring

def eX (t : T) : (GA D D.sp.X' → ℂ) →ₗ[ℂ] (GA D D.sp.X' → ℂ) :=
  gaL D.sp.X' R.βX (R.datXt t) R.eG (RealDat.eC (A := A) D.what₂.embLL)

def goodAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H :=
  formsAt R t P ⊓ ⨅ v : SmT R.MX,
    LinearMap.ker ((eX R t - LinearMap.id) ∘ₗ LinearMap.applyₗ v ∘ₗ scal R t)

def kerAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H := goodAt R t P ⊓ LinearMap.ker (R.Th t)

def quotAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HX t).H := goodAt R t P ⊓ (kerAt R t P)ᗮ

def iotaAt (t : T) (P : LevelP R.Pg D.R.r ℂ) : quotAt R t P →ₗ[ℂ] rowsAt R P :=
  ((rowsAt R P).orthogonalProjection : R.HE.H →ₗ[ℂ] rowsAt R P) ∘ₗ R.Th t ∘ₗ (quotAt R t P).subtype

def lamProdAt (P : LevelP R.Pg D.R.r ℂ) : ℝ :=
  ∏ᶠ c ∈ rowLabels R, (∏ i, lamFull R F i A.μ0 c) ^ Module.finrank ℂ ↥(rowPart R c ⊓ rowsAt R P)

def IsDetConst (P : LevelP R.Pg D.R.r ℂ) (κ : ℝ) : Prop :=
  0 < κ ∧ 0 < lamProdAt R F P ∧
    LinearMap.det (iotaAt R A.μ0 P ∘ₗ LinearMap.adjoint (iotaAt R A.μ0 P)) =
      ((κ ^ Module.finrank ℂ (rowsAt R P) * lamProdAt R F P : ℝ) : ℂ)

def RowTie (b : Bool) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)
    {n : ℕ} (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) (cOf : D.what₂.FT → Eig D) : Prop :=
  ∃ (uA : S.Amb D.what₂.mu0 →ₗ[ℂ] (R.HX A.μ0).H) (uE : EE →ₗ[ℂ] R.HE.H),
    (∀ x, ‖uA x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) ∧ LinearMap.range uA = formsAt R A.μ0 (R.levR F b) ∧
    (S.V0 D.what₂.mu0).map uA = goodAt R A.μ0 (R.levR F b) ∧
    (∀ y, ‖uE y‖ ^ 2 = RealDat.nP F b * ‖y‖ ^ 2) ∧ LinearMap.range uE = rowsAt R (R.levR F b) ∧
    (∀ x ∈ S.V0 D.what₂.mu0, uE (S.iota D.what₂.mu0 x) = R.Th A.μ0 (uA x)) ∧
    ∀ σ, cOf (ty σ) ∈ rowLabels R ∧ uE (bs σ) ∈ rowPart R (cOf (ty σ)) ∧
      ∀ i : Fin D.R.m, D.what₂.lamP D.what₂.mu0 ((i : ℕ) + 1) (ty σ) = lamFull R F i A.μ0 (cOf (ty σ))

def OneKappa (X : DivX D) : Prop :=
  ∀ e : D.what₂.LL →+* ℂ, InfinitePlace.mk e ≠ InfinitePlace.mk D.what₂.embLL → X.kapR e = X.kapR D.what₂.embLL

def DetConstAllLevels : Prop :=
  IsDetConst R F R.triv R.kap ∧ IsDetConst R F (R.levR F false) R.kap ∧ IsDetConst R F (R.levR F true) R.kap

def RecordConst : Prop :=
  ∀ cOf : D.what₂.FT → Eig D,
    (∀ X₀ : BaseLevelRowSide D, RowTie R F false X₀.s D.what₂.onb0 D.what₂.ft0 cOf → 0 < D.what₂.D0 → X₀.kap0 = R.kap) ∧
    (RowTie R F true (RowSide.sharp D) D.what₂.onb D.what₂.ft cOf → 0 < D.what₂.Drows →
      kapSharp D = R.kap ∧ ∀ X : DivX D, DV.KapRBase X →
        (∀ e : D.what₂.LL →+* ℂ, InfinitePlace.mk e = A.v0 → X.kapR e = (R.toCx F).κ (InfinitePlace.mk e)) ∧
        (OneKappa X → ∀ e : D.what₂.LL →+* ℂ, X.kapR e = (R.toCx F).κ (InfinitePlace.mk e)))

def KappaIdentityAt : Prop :=
  R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → R.IsThP → R.IsScal F →
    ScalarIdentity R F R.kap → DetConstAllLevels R F ∧ RecordConst R F

def KappaIdentity : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), KappaIdentityAt R F

example (t : T) : datXP R t R.triv = R.datXt t := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.KappaLambdaEmbedding

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LocalDataValues
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalDataValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLocalAt (V : HSp D) (PP : Pl D.host.E) (x : Bridge.Gf V) : Prop :=
  ∃ (e : AE D) (g : GA D V), Formalism.L2.NTheta.IsIdemAt e PP ∧ g ∈ GfC V ∧ SuppAt e V g ∧ x = (finHom V).rangeRestrict g

def IsCosetSys (V : HSp D) (J : Subgroup (Bridge.Gf V)) (PP : Pl D.host.E) (k : ℕ) (S : Finset (Bridge.Gf V)) : Prop :=
  ∃ α : GA D V, IsHeckeAt V PP k α ∧ Bridge.IsDC J ((finHom V).rangeRestrict α) S ∧ ∀ a ∈ S, IsLocalAt V PP a

def IsUnifIdele (PP : Pl D.host.E) (x : (AE D)ˣ) : Prop :=
  ∃ (e : AE D) (ϖ : 𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e PP ∧ ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2 ∧
    (x : AE D) = Formalism.L2.JoinChr.locE D e (ϖ : D.host.E)

def coefB (μ η : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (x : (AE D)ˣ) : ℂ :=
  ((μ x : Circle) : ℂ) * (((η x : Circle) : ℂ))⁻¹ * ((Real.sqrt (Nat.card (kP PP) : ℝ) : ℝ) : ℂ)

def ScalarsIn (μ η : (AE D)ˣ →* Circle) (PP : Pl D.host.E) {K : Type} [Field K] (σ : K →+* ℂ) : Prop :=
  ∀ x : (AE D)ˣ, IsUnifIdele PP x → ((μ x : Circle) : ℂ) ∈ σ.range ∧ coefB μ η PP x ∈ σ.range

def embKs (D : D7) (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL] : Ks →+* ℂ :=
  D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)

def RationalCharacterValues (C : Formalism.L2.Host.CharFrame D) {K : Type} [Field K] (σ : K →+* ℂ) : Prop :=
  (∀ j, (C.mu0 j).ValuesIn 0 σ) ∧ C.eta.ValuesIn (1 / 2) σ

section Stmt

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T) : Subgroup (Bridge.Gf (Vc D i)) := (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J

def ratForm (i : Fin D.R.m) (t : T) (x : A.fam.amb.FL i t) : Bridge.Gf (Vc D i) → (R.cV i).W :=
  (R.HV i t).e (R.jV i t x)

def KeepsAt (i : Fin D.R.m) (t : T) (PP : Pl D.host.E) (k : ℕ) : Prop :=
  ∃ TV : Module.End D.what₂.LL (A.fam.amb.FL i t), ∀ S, IsCosetSys (Vc D i) (levV R i t) PP k S →
    ∀ x, ratForm R i t (TV x) = Bridge.dcOp S (ratForm R i t x)

def KeepsRational : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ P ∈ A.ok t, ∀ k ≤ (Vc D i).rank, KeepsAt R i t (R.pl P) k

def ScalarsLL : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ P ∈ A.ok t, ScalarsIn (R.mu0 ((i : ℕ) + 1)) R.eta (R.pl P) D.what₂.embLL

def ScalarsKs : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ P ∈ A.ok t, ScalarsIn (R.mu0 ((i : ℕ) + 1)) R.eta (R.pl P) (embKs D Ks)

def TransferRational : Prop :=
  KeepsRational R ∧ ScalarsLL R ∧ (RationalCharacterValues R.C (embKs D Ks) → ScalarsKs R)

def LocalDataExist : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ P ∈ A.ok t,
    (∀ k ≤ (Vc D i).rank, ∃ S, IsCosetSys (Vc D i) (levV R i t) (R.pl P) k S) ∧ ∃ x, IsUnifIdele (R.pl P) x

def ScalarsTupleLL : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ P ∈ A.ok t, ScalarsIn (R.toLevCh.mu t ((i : ℕ) + 1)) R.eta (R.pl P) D.what₂.embLL

variable {R}

end Stmt

def TransferRationalAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → TransferRational R

end GlobalTheory.IndefiniteRowSideFullHecke.LocalDataValues

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealActionRational
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealActionRational

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def fockOf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (e : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) :
    WO (Vc D i) (Wc D i) → ℂ :=
  R.ptP i t (R.ioP i e w)

def levelForms (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Submodule ℂ (Bridge.Gf (Vc D i) → (R.cV i).W) :=
  Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ

def integrand (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : Bridge.Gf (Vc D i) → (R.cV i).W)
    (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)) (h : GA D (Vc D i)) : ℂ :=
  thetaKO (R.ωP i t) h g (fockOf R i t e ((R.cV i).ext f h))

structure RealActionAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop where

  act : ∀ u ∈ GinfC (Vc D i), ∀ (e : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W),
    R.ωP i t (u, 1) (fockOf R i t e w) = fockOf R i t e ((R.cV i).ρ u w)

  ratFin : ∀ γ ∈ GQ (Vc D i), ∀ γf ∈ GfC (Vc D i), finHom (Vc D i) γf = finHom (Vc D i) γ →
    ∀ h ∈ GfC (Vc D i), ∀ (g : GA D (Wc D i)) (e : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W),
      thetaKO (R.ωP i t) (γf * h) g (fockOf R i t e ((R.cV i).ρ γ w)) = thetaKO (R.ωP i t) h g (fockOf R i t e w)

  left : ∀ f ∈ levelForms R i t, ∀ (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)), ∀ γ ∈ GQ (Vc D i),
    ∀ h : GA D (Vc D i), integrand R i t f e g (γ * h) = integrand R i t f e g h

  right : ∀ f ∈ levelForms R i t, ∀ (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)), ∀ u ∈ GinfC (Vc D i),
    ∀ h : GA D (Vc D i), integrand R i t f e g (h * u) = integrand R i t f e g h

def RealActionFock : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → ∀ (i : Fin D.R.m) (t : T), RealActionAt R i t

example (R : RealDat D A Ks) (F : Face D A) (hR : R.Char F) (i : Fin D.R.m) (t : T) :
    LinearMap.range (R.HV i t).e = levelForms R i t :=
  (hR.models.HV i t).2.1

example (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (x : (R.HV i t).H) (e : LowT (R.MW i (sg0 D A)))
    (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    integrand R i t ((R.HV i t).e x) e g h = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i e (R.extV i t x h))) :=
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.RealActionRational

end
end

