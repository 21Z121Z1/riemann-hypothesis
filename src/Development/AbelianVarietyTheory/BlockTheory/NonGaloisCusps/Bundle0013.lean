import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.LocalRingCardinality.DataNChoice
import Formalism.LocalRingCardinality.Bundle0002
import Formalism.SharpRestriction.ParConsts

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DeterminantInTorus
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeterminantInTorus

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section One

variable (D : D7) (i : D.nd.Loc)

def IsRxBar (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i))) : Prop :=
  Continuous (fun g => ((r g : GL (Fin D.R.nV) (Qbar (D.nd.l i))) :
    Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i)))) ∧
  IsSSRep r ∧
  ∀ w, SplitOut D.nd i w → ∀ (B : ValuationSubring D.nd.Om) (σ : GE D.nd),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((r σ : GL (Fin D.R.nV) (Qbar (D.nd.l i))) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
      (heckePol D.nd i x w).map (iotaOQ D.nd D.naut i)

def CoeffLarge : Prop :=
  ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), IsRxBar D i x r →
    ∃ h : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ (g : GE D.nd) (a b : Fin D.R.nV),
      ((h * r g * h⁻¹ : GL (Fin D.R.nV) (Qbar (D.nd.l i))) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) a b ∈ (D.naut.iotaQ i).range

def IsRx (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin D.R.nV) (D.nd.O i)) : MatN D.nd i)) ∧
  IsSSRep (mapRep (toK D.nd i) r) ∧
  ∀ w, SplitOut D.nd i w → ∀ (B : ValuationSubring D.nd.Om) (σ : GE D.nd),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((r σ : GL (Fin D.R.nV) (D.nd.O i)) : MatN D.nd i).charpoly = heckePol D.nd i x w

def DetInT (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ g : GE D.nd, ∃ P : Polynomial (D.nd.T i), ∀ x : D.nd.X i,
    P.map (evT D.nd i x) = ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : MatN D.nd i).charpolyRev

def RxConcl : Prop :=
  ∃ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), (∀ x, IsRx D i x (r x)) ∧ DetInT D i r

def DetInTAll : Prop :=
  ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), (∀ x, IsRx D i x (r x)) → DetInT D i r

end One

def RxBar_at (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ r, IsRxBar D i x r

def RxDetInT_at (D : D7) : Prop :=
  ∀ i : D.nd.Loc, CoeffLarge D i → RxConcl D i

def RxDetInTF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x : ℝ, Fm.x1 < x → ∀ p : Fm.Ix x, RxDetInT_at (Fm.D x p)

def RxDetInT (C : FamClass) : Prop :=
  Closed C (fun Fm _ => RxDetInTF Fm)

theorem isRx_iff (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) :
    (∀ x, IsRx D i x (r x)) ↔ GoodR D.nd i r := Iff.rfl

end GlobalTheory.IndefiniteRowSideFullHecke.DeterminantInTorus

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

variable (D : D7)

abbrev TwDatum : Type :=
  Σ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k : ℕ), (D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)

def Twisted (w : D.what₂.places.Pl) : Prop := D.what₂.muAt w ≠ D.what₂.mu0

def SameBelow (w w' : D.what₂.places.Pl) : Prop :=
  ∀ x : ↥D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔ 0 ≤ D.what₂.places.val w' (x : D.what₂.LL)

def SamePair (w w' : D.what₂.places.Pl) : Prop :=
  SameBelow D w w' ∨ SameBelow D (D.what₂.places.conj w) w'

def LiesUnder (i : D.ntw.Tw) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : 𝓞 ↥D.LL0,
    (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) ↔
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)

def TwistedPlaceSettings (twI : D.what₂.places.Pl → D.ntw.Tw) : Prop :=
  (∀ w, Twisted D w → D.ntw.l (twI w) = D.what₂.places.resChar w ∧
    (LiesUnder D (twI w) w ∨ LiesUnder D (twI w) (D.what₂.places.conj w))) ∧
  ∀ w w', Twisted D w → Twisted D w' → SamePair D w w' → twI w = twI w'

def namedPrimes : Set ℕ :=
  {2, 3, 5, D.host.g 0, D.host.g 1, D.host.pde, D.host.pde'} ∪ Set.range fun u : D.what₂.Word => (D.mem u).A.T

variable {D}

def expDat (xd : ThData D) : IntegralHeckeForms.XD D := ⟨xd.xd0, xd.thetaBase_invariant_action⟩

def GoodDatum (xd : ThData D) (N0 : D.ntw.Tw → ℕ) (A : Finset (PlE D.host)) (t : TwDatum D) : Prop :=
  (∀ P ∈ t.2.1, ∀ P', IsConjPl D.host P P' → P' ∈ t.2.1) ∧
  (∀ P ∈ t.2.1, ∀ p ∈ namedPrimes D, P ∉ placesOver D.host.E p) ∧
  (∀ lam : D.ntw.abelian₂ t.1, (∑ δ, D.ntw.th t.1 ∅ lam δ) ≠ 0) ∧
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
    IntegralHeckeForms.FullRk D.nexp (expDat xd) t.1 j b (IntegralHeckeForms.SgJ D.nexp (expDat xd) t.1 j b)) ∧
  ∃ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat t.1 j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IntegralHeckeForms.BasisOf D.nexp t.1 j b (IntegralHeckeForms.SgJ D.nexp (expDat xd) t.1 j b) (S j b)) ∧
    ∀ a : ℤ, IsCoprime a (D.ntw.l t.1 : ℤ) →
      IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (expDat xd) N0 t.1 (((D.ntw.l t.1 : ℝ) ^ 2)⁻¹) S A t.2.1 t.2.2.1
        (t.2.2.2 ^ a)

def GoodSystem (xd : ThData D) (N0 : D.ntw.Tw → ℕ) (A : D.ntw.Tw → Finset (PlE D.host))
    (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  TwistedPlaceSettings D (fun w => (t w).1) ∧
  (∀ w, Twisted D w → GoodDatum xd N0 (A (t w).1) (t w)) ∧
  (∀ w w', Twisted D w → Twisted D w' → SamePair D w w' → t w = t w') ∧
  ∀ w w', Twisted D w → Twisted D w' → ¬ SamePair D w w' →
    ∀ P ∈ (t w).2.1, ∀ P' ∈ (t w').2.1, ∀ p : ℕ, p.Prime →
      ¬ (P ∈ placesOver D.host.E p ∧ P' ∈ placesOver D.host.E p)

def recorded (c : NChoice D) (w : D.what₂.places.Pl) : TwDatum D :=
  ⟨c.twI w, c.Q w, c.k' w, BlochKatoReduction.Gen.psiAt (c.sd w) (c.psi' w)⟩

def TwGoodAt (c : NChoice D) (xd : ThData D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  GoodSystem xd N0 (fun _ => ∅) (recorded c) ∧
  ∀ w, Twisted D w → D.what₂.places.conj w ≠ w → c.sd (D.what₂.places.conj w) = !c.sd w

def ExistsChoice (xd : ThData D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  (∃ twI, TwistedPlaceSettings D twI) ∧
  ∀ twI, TwistedPlaceSettings D twI → ∀ A : D.ntw.Tw → Finset (PlE D.host),
    ∃ t : D.what₂.places.Pl → TwDatum D, (∀ w, (t w).1 = twI w) ∧ GoodSystem xd N0 A t

def WithToricIntegralityConstant (D : D7) (P : (D.ntw.Tw → ℕ) → Prop) : Prop :=
  (∃ N0, BlochKatoReduction.adm9 D N0) ∧ ∀ N0, BlochKatoReduction.adm9 D N0 → P N0

def FamTwGood {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    WithToricIntegralityConstant (Fm.D x i) fun N0 => TwGoodAt (Fm.ex x hx i).nch (Fm.ex x hx i).xd N0

def FamExistsChoice {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    WithToricIntegralityConstant (Fm.D x i) fun N0 => ExistsChoice (Fm.ex x hx i).xd N0

def TwGoodClosed (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => FamTwGood Fm

def ExistsChoiceClosed (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => FamExistsChoice Fm

def Statement (𝒞 : FamClass) : Prop := ExistsChoiceClosed 𝒞 ∧ TwGoodClosed 𝒞

theorem samePair_conj (w : D.what₂.places.Pl) : SamePair D w (D.what₂.places.conj w) :=
  Or.inr fun _ => Iff.rfl

open NumberField IsDedekindDomain in
variable (D : _root_.Formalism.BasicNotions.D7) in
variable {D} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj (w : D.what₂.places.Pl) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D (D.what₂.places.conj w) ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted
  rw [_root_.Formalism.BasicNotions.Rows.Data.muAt_conj]

theorem TwistedPlaceSettings.inW1 {twI : D.what₂.places.Pl → D.ntw.Tw} (h : TwistedPlaceSettings D twI) {w : D.what₂.places.Pl}
    (hw : Twisted D w) : D.ntw.NonzeroIndexPlace (twI w) := by
  rcases (h.1 w hw).2 with h1 | h1
  · exact ⟨w, hw, h1⟩
  · exact ⟨_, (twisted_conj w).2 hw, h1⟩

theorem TwGoodAt.goodTw {c : NChoice D} {xd : ThData D} {N0 : D.ntw.Tw → ℕ} (h : TwGoodAt c xd N0)
    {w : D.what₂.places.Pl} (hw : Twisted D w) :
    ∃ S, IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (expDat xd) N0 (c.twI w) (((D.ntw.l (c.twI w) : ℝ) ^ 2)⁻¹) S ∅
      (c.Q w) (c.k' w) (BlochKatoReduction.Gen.psiAt (c.sd w) (c.psi' w)) := by
  obtain ⟨-, -, -, -, S, -, hS⟩ := h.1.2.1 w hw
  have := hS 1 isCoprime_one_left
  rw [zpow_one] at this
  exact ⟨S, this⟩

end GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PrimeTypeRows
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Twist

variable {Γ O : Type} [Group Γ] [CommRing O] {n : ℕ}

def twGL (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) : Γ →* GL (Fin n) O where
  toFun g := Units.map (Matrix.scalar (Fin n) : O →+* Matrix (Fin n) (Fin n) O).toMonoidHom (χ g) * r g
  map_one' := by simp
  map_mul' g h := by
    apply Units.ext
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [mul_assoc, mul_assoc, ← mul_assoc (Matrix.scalar (Fin n) _) (r g : Matrix (Fin n) (Fin n) O),
      (Matrix.scalar_commute _ (fun _ => Commute.all _ _) (r g : Matrix (Fin n) (Fin n) O)).eq, mul_assoc]

def charGL (χ : Γ →* Oˣ) : Γ →* GL (Fin 1) O := twGL 1 χ

theorem twGL_val (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) (g : Γ) :
    ((twGL r χ g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) =
      ((χ g : Oˣ) : O) • (r g : Matrix (Fin n) (Fin n) O) := by
  change Matrix.scalar (Fin n) ((χ g : Oˣ) : O) * (r g : Matrix (Fin n) (Fin n) O) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

end Twist

def sg (b : Bool) : ℚ := if b then 1 else -1

def lam {n : ℕ} (a : Fin n → ℤ) (s : Fin n) : ℚ := (a s : ℚ) + (((n : ℚ) - 1) / 2 - ((s : ℕ) : ℚ))

def wtJump {n : ℕ} (a : Fin n → ℤ) (b : Bool) (s : Fin n) : ℚ := ((n : ℚ) - 1) / 2 - sg b * lam a s

def IsRunWeight {n : ℕ} (p t : ℕ) (a : Fin n → ℤ) : Prop :=
  Antitone a ∧
  (∀ s s' : Fin n, p ≤ (s : ℕ) → (s : ℕ) < p + t → p ≤ (s' : ℕ) → (s' : ℕ) < p + t → a s = a s') ∧
  (∀ s s' : Fin n, (s : ℕ) < p → p ≤ (s' : ℕ) → a s' < a s) ∧
  (∀ s s' : Fin n, (s : ℕ) < p + t → p + t ≤ (s' : ℕ) → a s' < a s)

def sigPar {R : Ranks} (P : HCParam R) : Multiset ℚ :=
  Finset.univ.val.map P.v + Finset.univ.val.map fun i => -P.b i

def runPar (t : ℕ) (e : ℚ) : Multiset ℚ :=
  (Finset.Icc 1 t).val.map fun c : ℕ => -e + ((t : ℚ) - 1) / 2 - ((c : ℚ) - 1)

def fullPar {R : Ranks} (P : HCParam R) (j : Fin R.m) : Multiset ℚ := sigPar P + runPar R.t (P.e j)

section Dict

variable (D : D7)

def embAt (ρ : D.what₂.Tau) (b : Bool) : D.host.E →+* ℂ :=
  if b then D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)
  else (D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)).comp
    (D.host.conj : D.host.E →+* D.host.E)

def jF (i : D.nd.Loc) : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def ctr (i : D.nd.Loc) (ρ : D.what₂.Tau) : ℚ := (D.hc ρ).e (jF D i)

abbrev Emb (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Type :=
  Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

def cplx (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : Emb D i w hw) : D.host.E →+* ℂ :=
  (D.naut.iotaQC i).toRingHom.comp
    ((D.nbr i w hw).LL.1.val.toRingHom.comp (τ.toRingHom.comp (Br.cEw D.nbr i w hw)))

def JumpsAre (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {m : ℕ}
    (r : GE D.nd →* GL (Fin m) (D.nd.O i)) (τ : Emb D i w hw) (J : Multiset ℚ) : Prop :=
  (∀ y ∈ J, ∃ z : ℤ, y = (z : ℚ)) ∧
  ∀ z : ℤ, Br.jumpMult D.loc D.nbr i w hw r τ z = (J.count (z : ℚ) : ℤ)

def IsWeight (i : D.nd.Loc) (a : D.what₂.Tau → Fin D.R.nV → ℤ) : Prop :=
  ∀ ρ, IsRunWeight (D.R.sigW (D.nd.j i)).1 D.R.t (a ρ) ∧
    ∀ b, D.naut.infWt i (embAt D ρ b) =
      Finset.univ.val.map fun s => ((sg b * lam (a ρ) s : ℚ) : ℂ)

def ParamTie : Prop :=
  ∀ i ρ b, D.naut.infWt i (embAt D ρ b) =
    (fullPar (D.hc ρ) (jF D i)).map fun y => ((sg b * (y - 1 / 2) : ℚ) : ℂ)

def CharTie : Prop :=
  (∀ i ρ b, D.naut.infG (D.naut.muC i) (embAt D ρ b) = {((-(sg b * ctr D i ρ) : ℚ) : ℂ)}) ∧
  ∀ ρ b, D.naut.infG D.naut.etaTinv (embAt D ρ b) = {((-(sg b / 2) : ℚ) : ℂ)}

def WeightsAt (i : D.nd.Loc) (a : D.what₂.Tau → Fin D.R.nV → ℤ) (x : D.nd.X i)
    (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Prop :=
  ∀ (τ : Emb D i w hw) (ρ : D.what₂.Tau) (b : Bool), cplx D i w hw τ = embAt D ρ b →
    JumpsAre D i w hw r τ (Finset.univ.val.map (wtJump (a ρ) b)) ∧
    ({z : ℤ | Br.IsJumpW D.loc D.nbr i w hw r τ z}.ncard = D.R.nV ∧
      ∀ z : ℤ, Br.jumpMult D.loc D.nbr i w hw r τ z ≤ 1) ∧
    ∃ w₁ : ℤ,
      (∀ y : ℚ, (∃ s : Fin D.R.nV, (D.R.sigW (D.nd.j i)).1 ≤ (s : ℕ) ∧
          (s : ℕ) < (D.R.sigW (D.nd.j i)).1 + D.R.t ∧ y = wtJump (a ρ) b s) ↔
        ∃ z : ℤ, w₁ ≤ z ∧ z < w₁ + D.R.t ∧ y = (z : ℚ)) ∧
      ¬ Br.IsJumpW D.loc D.nbr i w hw r τ (w₁ - 1) ∧
      ¬ Br.IsJumpW D.loc D.nbr i w hw r τ (w₁ + D.R.t) ∧
      (x ∈ D.nd.Z i → ∀ z : ℤ,
        (∃ c, 1 ≤ c ∧ c ≤ D.R.t ∧ Br.IsJumpW D.loc D.nbr i w hw (charGL (D.nd.chi i c)) τ z) ↔
          (w₁ ≤ z ∧ z < w₁ + D.R.t))

def Crys_at : Prop :=
  ∀ (i : D.nd.Loc), (∀ k, D.nd.l i ≠ D.host.g k) →
  ∀ a, IsWeight D i a →
  ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
  ∀ (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.IsCrysW D.loc D.nbr i w hw r ∧ WeightsAt D i a x r w hw

def TypePrime_at : Prop :=
  ∀ (i : D.nd.Loc), (∃ k, D.nd.l i = D.host.g k) →
  ∀ a, IsWeight D i a →
  ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
  ∀ (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.IsdRW D.loc D.nbr i w hw r ∧ WeightsAt D i a x r w hw ∧
    ∀ P : D.naut.AV i, D.naut.ptV i P = some x →
      (Br.IsPotCrysW D.loc D.nbr i w hw r ↔ D.naut.mono0 (D.naut.locV i P w))

def Twisted_at : Prop :=
  ParamTie D → CharTie D →
  ∀ (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : Emb D i w hw) (ρ : D.what₂.Tau) (b : Bool), cplx D i w hw τ = embAt D ρ b →
    (∀ c, 1 ≤ c → c ≤ D.R.t → JumpsAre D i w hw (charGL (D.nd.chi i c)) τ
      {sg b * (ctr D i ρ + 1 / 2) + ((D.R.nV : ℚ) - 1) / 2 - ((D.R.t : ℚ) - 1) / 2 + ((c : ℚ) - 1)}) ∧
    ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
      JumpsAre D i w hw (twGL r (D.nd.chi i 1)⁻¹) τ
        ((fullPar (D.hc ρ) (jF D i)).map fun y => ((D.R.t : ℚ) - 1) / 2 - sg b * (y + ctr D i ρ)) ∧
      JumpsAre D i w hw (twGL r (D.nd.chi i 1)⁻¹) τ
        ((Finset.range D.R.t).val.map (fun c : ℕ => (c : ℚ)) +
          (sigPar (D.hc ρ)).map fun y => ((D.R.t : ℚ) - 1) / 2 - sg b * (y + ctr D i ρ)) ∧
      ∀ (s : Fin (D.R.k - 1)) (z : ℤ),
        (z : ℚ) = ((D.R.t : ℚ) - 1) / 2 - sg b * ((D.hc ρ).v s + ctr D i ρ) →
        (b = true → z < 0) ∧ (b = false → (D.R.t : ℤ) - 1 < z)

def Explicit_at : Prop :=
  ParamTie D →
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
  ∀ (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.IsdRW D.loc D.nbr i w hw r ∧
    ∀ (τ : Emb D i w hw) (ρ : D.what₂.Tau),
      (cplx D i w hw τ = embAt D ρ true →
        JumpsAre D i w hw r τ
          ((fullPar (D.hc ρ) (jF D i)).map fun p => ((D.R.nV : ℚ) - 1) / 2 + 1 / 2 - p) ∧
        (CharTie D → x ∈ D.nd.Z i → ∀ c, 1 ≤ c → c ≤ D.R.t → JumpsAre D i w hw (charGL (D.nd.chi i c)) τ
          {ctr D i ρ + 1 / 2 + (D.R.r : ℚ) / 2 + ((c : ℚ) - 1)})) ∧
      (cplx D i w hw τ = embAt D ρ false →
        JumpsAre D i w hw r τ
          ((fullPar (D.hc ρ) (jF D i)).map fun p => ((D.R.nV : ℚ) - 1) / 2 - 1 / 2 + p))

def PlaceTypeCondition : Prop := Crys_at D ∧ TypePrime_at D ∧ Twisted_at D ∧ Explicit_at D

end Dict

def AtF (S : D7 → Prop) {eps : ℝ} (Fm : FamP eps) : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, S (Fm.D x i)

def CrysF {eps : ℝ} (Fm : FamP eps) : Prop := AtF Crys_at Fm

def TypePrimeF {eps : ℝ} (Fm : FamP eps) : Prop := AtF TypePrime_at Fm

def RowF {eps : ℝ} (Fm : FamP eps) : Prop := AtF PlaceTypeCondition Fm

def CrysClosed (C : FamClass) : Prop := Closed C fun Fm _ => CrysF Fm

def TypePrimeClosed (C : FamClass) : Prop := Closed C fun Fm _ => TypePrimeF Fm

def RowClosed (C : FamClass) : Prop := Closed C fun Fm _ => RowF Fm

example : IsRunWeight (n := 4) 1 2 ![2, 0, 0, -1] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s s'; revert s s'; decide
  all_goals decide

example : ¬ IsRunWeight (n := 4) 1 2 ![2, 0, 0, 0] := by
  intro h
  exact absurd (h.2.2.2 1 3 (by decide) (by decide)) (by decide)

end GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstituentShape
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidualConstituentShape

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

section Loc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def cpol {Γ S : Type} [Group Γ] [CommRing S] {a : ℕ} (ρ : Γ →* GL (Fin a) S) (g : Γ) : S[X] :=
  ((ρ g : GL (Fin a) S) : Matrix (Fin a) (Fin a) S).charpoly

def IsPointRepBar (i : N.Loc) (x : N.X i) (ρ : GE N →* GL (Fin R.nV) (Qbar (N.l i))) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))) ∧
  IsSSRep ρ ∧
  ∀ w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    cpol ρ σ = (heckePol N i x w).map (iotaOQ N A i)

def EnlargementAt (i : N.Loc) : Prop :=
  ∀ ρ : N.X i → (GE N →* GL (Fin R.nV) (Qbar (N.l i))), (∀ x, IsPointRepBar N A i x (ρ x)) →
    (∃ L' : Loc.FinExt (N.l i), (∀ a : KK N i, A.iotaQ i a ∈ L'.1) ∧
      ∀ x, ∃ ρ' : GE N →* GL (Fin R.nV) ↥L'.1,
        (∃ P : GL (Fin R.nV) (Qbar (N.l i)), ∀ g,
          mapRep (algebraMap ↥L'.1 (Qbar (N.l i))) ρ' g = P * ρ x g * P⁻¹) ∧
        AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ'))) ∧
    ∀ x y g (k : ℕ), ‖(cpol (ρ x) g).coeff k‖ ≤ 1 ∧
      ‖(cpol (ρ x) g).coeff k - (cpol (ρ y) g).coeff k‖ < 1

def CoeffLarge (i : N.Loc) : Prop :=
  ∃ r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)), GoodR N i r ∧
    ∀ x W, IsIrrSub (mapRep (toK N i) (r x)) W → AbsIrrSub (mapRep (toK N i) (r x)) W

def ResidualSame (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ x y g, cpol (redRep N i (r x)) g = cpol (redRep N i (r y)) g

def ConstituentsOver (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) : Prop :=
  (∀ x, IsSS (repK N i r x) ∧ AbsIrrDistinct (repK N i r x)) ∧ ResidualSame N i r

def IsBlockComplement (i : N.Loc) (r₀ : GE N →* GL (Fin R.nV) (N.O i))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  ∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
    ∀ g v, e (((mapRep (toK N i) r₀ g : GL _ _) : Matrix _ _ _).mulVec v) =
      (((mapRep (toK N i) ρ g : GL _ _) : Matrix _ _ _).mulVec (e v).1,
        fun c : Fin R.t => toK N i ((N.chi i (c.1 + 1) g : (N.O i)ˣ) : N.O i) * (e v).2 c)

def ResidualShape (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  1 < R.r ∧ AbsIrrSub (redRep N i ρ) ⊤ ∧
    ∀ x g, cpol (redRep N i (r x)) g = cpol (redRep N i ρ) g *
      ∏ c ∈ Finset.Icc 1 R.t,
        (X - C (IsLocalRing.residue (N.O i) ((N.chi i c g : (N.O i)ˣ) : N.O i)))

def ResidualAtGood (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ x₀ ∈ N.Zgood i, (∃ ρ, IsBlockComplement N i (r x₀) ρ) ∧
    ∀ ρ, IsBlockComplement N i (r x₀) ρ → ResidualShape N i r ρ

end Loc

def TypePrimeSizes (D : D7) : Prop :=
  100 ≤ D.R.r ∧ (∀ k : Fin 2, 2 * D.R.r ≤ D.host.g k) ∧
    Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1))

def Constituents_at (D : D7) : Prop :=
  ∀ i : D.nd.Loc, EnlargementAt D.nd D.naut i ∧
    (CoeffLarge D.nd i → ∀ r, GoodR D.nd i r → ConstituentsOver D.nd i r)

def ResidualShape_at (D : D7) : Prop :=
  TypePrimeSizes D → ∀ i : D.nd.Loc, CoeffLarge D.nd i → ∀ r, GoodR D.nd i r → ResidualAtGood D.nd i r

def ConstituentsAndShape_at (D : D7) : Prop := Constituents_at D ∧ ResidualShape_at D

def ConstituentsAndShapeF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ConstituentsAndShape_at (Fm.D x i)

def ConstituentsAndShape (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => ConstituentsAndShapeF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.ResidualConstituentShape

end
end

