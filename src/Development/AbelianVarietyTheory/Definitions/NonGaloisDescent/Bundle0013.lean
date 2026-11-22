import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwAll

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)

def admissibleIndexBoundAllPowers (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, ABHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
      Formalism.MainNotions.BlochKatoReduction.Gen.PsiOk i A0 Q k' (ψ' ^ a) ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partAT bkP i Q k' (ψ' ^ a) eps' ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.partC N0 i Q k' (ψ' ^ a) eps' ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partD i Q k' (ψ' ^ a) eps' ∧
      partAB Y i F Q k' (ψ' ^ a) eps'

def goodTwistExistsAllCoprimePowers (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
    GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

def TwGoodAtAll (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → I.Ok (C.twI w) ∧ ∀ a : ℤ, IsCoprime a (D.ntw.l (C.twI w) : ℤ) →
    TwGoodOne D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w ^ a)

variable {Y} (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

def Ball (i : X.Tw) (j : ℕ) (b : Bool) (B : ℝ) : Set (Y.Fm i j b) :=
  {f | f ∈ T.FmUr i j b ∧ ∀ y, ‖T.ev i j b f y‖ ≤ B}

def SupBdd : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ f ∈ T.FmUr i j b, ∃ B, f ∈ Ball T i j b B

def GKeeps : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b g, ∀ f ∈ Ball T i j b 1,
  Y.actG i j b g f ∈ Ball T i j b 1

def HkKeeps : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ f ∈ Ball T i j b 1,
  Y.hkF i j b k P f ∈ Ball T i j b 1

def UnivBdd (E : ExpDat Y) : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M,
  (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q → Disjoint Q (X.S0 i) → Disjoint Q (Y.lev i j b a) →
  ∃ Xi : DelQM D.host (X.l i) Q M →₀ Y.Fm i j b,
    Y.thU i j b Q M a = Xi.sum (fun δ f => f ⊗ₜ[X.O i] AddMonoidAlgebra.single δ (1 : X.O i)) ∧
    ∀ δ, Xi δ ∈ Fm0 Y i j b ∧ Xi δ ∈ Submodule.span (X.O i) (Ball T i j b ((X.l i : ℝ) ^ c))

def TypeKept (E : ExpDat Y) : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k Q
  (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), TwOK i k Q ψ → UnrG ψ → ∀ a ∈ E.Dat0 i j b,
    Y.thPsi i j b k Q ψ a ⊆ ((((Fm0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) :
      Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b))

end GlobalTheory.TwAll
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
section
noncomputable section

namespace GlobalTheory.PendOf

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct Formalism.MainNotions.PairedCharacterCondition

structure TameOm (D : D7) where
  om : ∀ k : Fin 2, PlE D.host → Fb (D.host.g k) (D.host.g_prime k) → GE D.nd → ℂ
  om_one : ∀ k w x, x ≠ 0 → om k w x 1 = 1
  om_mul : ∀ k w x, x ≠ 0 → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    ∀ σ' ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), om k w x (σ * σ') = om k w x σ * om k w x σ'
  tameInertiaChar_mul_root : ∀ k w x y, x ≠ 0 → y ≠ 0 → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
    om k w (x * y) σ = om k w x σ * om k w y σ
  om_wild : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x, x ≠ 0 →
    ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), om k w x σ = 1
  om_open : ∀ k w x, x ≠ 0 → ∃ U : Subgroup (GE D.nd), IsOpen (U : Set (GE D.nd)) ∧
    ∀ σ ∈ U, σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → om k w x σ = 1
  om_inj : ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ x y, x ≠ 0 → y ≠ 0 → x ≠ y →
    ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), om k w x σ ≠ om k w y σ
  om_tg : ∀ k (v : D.nd.PlG k) x, x ≠ 0 →
    om k (D.naut.plGw k v) x (D.ntypes.tg k v) = D.ntypes.teichC k x

def LabIne {D : D7} (Ω : TameOm D) : Prop :=
  ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol L σ =
      ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map fun x => X - C (Ω.om k w x σ)).prod

def LabChar (D : D7) : Prop :=
  ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ (L χ : D.naut.LP w)
    (u : (ZMod (D.host.g k))ˣ), (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
    D.naut.lpDim χ = 1 → D.naut.items₂ k w χ = X - C (u : ZMod (D.host.g k)) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L ∧
    Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.lpChar L χ)) =
      (Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map
        (· * algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))

def IneRep (D : D7) : Prop :=
  ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    ∃ ρ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)) →* GL (Fin (D.naut.lpDim L)) ℂ,
      (∃ U : Subgroup (GE D.nd), IsOpen (U : Set (GE D.nd)) ∧
        ∀ σ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)), (σ : GE D.nd) ∈ U → ρ σ = 1) ∧
      ∀ σ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w)), D.naut.inePol L (σ : GE D.nd) =
        ((ρ σ : GL (Fin (D.naut.lpDim L)) ℂ) : Matrix (Fin (D.naut.lpDim L)) (Fin (D.naut.lpDim L)) ℂ).charpoly

def TameLP (D : D7) {w : PlE D.host} (L : D.naut.LP w) : Prop :=
  ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), σ ∈ wildSet D.nd (D.nd.plOm.1 w) →
    D.naut.inePol L σ = (X - 1) ^ D.naut.lpDim L

def LabDepth (D : D7) : Prop :=
  ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
    (D.naut.items₂ k w L).Monic ∧ ((D.naut.items₂ k w L).natDegree = D.naut.lpDim L ↔ TameLP D L)

def GenFam (D : D7) (γ : Fin 2 → PlE D.host → GE D.nd) : Prop :=
  (∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), TameGenAt (D.nd.plOm.1 w) (γ k w)

def LabGen (D : D7) : Prop :=
  ∃ γ : Fin 2 → PlE D.host → GE D.nd, GenFam D γ ∧
    ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ L : D.naut.LP w,
      (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.naut.inePol L (γ k w) =
        ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L)).map fun x => X - C (D.ntypes.teichC k x)).prod

def DepthZ (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k),
    TameLP D (D.naut.locV i PI w)

structure CenO (D : D7) where
  zO : ∀ i : D.nd.Loc,
    ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i]
      Module.End (D.nd.O i) (D.nd.Mt i)
  zO_comm : ∀ i z (f : D.nd.T i), zO i z * D.nd.act i f = D.nd.act i f * zO i z
  zO_act : ∀ i (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (D.what₂.jMt _ _ x) →
    D.nd.prMt i y = (zO i z).baseChange (KK D.nd i) (D.nd.prMt i x)

def ZLStable (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (z : MonoidAlgebra D.what₂.LL (G0g D.nd)), (∀ a, z * a = a * z) →
    ∀ x : D.what₂.MtL (D.nd.mu i) (D.nd.j i), ∃ y : D.what₂.MtL (D.nd.mu i) (D.nd.j i),
      D.what₂.jMt _ _ y =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef D.what₂.embLL z) (D.what₂.jMt _ _ x)

def CenInt (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (z : MonoidAlgebra ℤ (G0g D.nd)), (∀ a, z * a = a * z) →
    ∀ x ∈ GlobalTheory.EtaJoin.genSet D (D.nd.mu i) (D.nd.j i), ∃ y ∈ GlobalTheory.EtaJoin.lat D (D.nd.mu i) (D.nd.j i),
      D.what₂.jMt _ _ y =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (Int.castRingHom ℂ) z) (D.what₂.jMt _ _ x)

def OnMtPreservesTypeV (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (z : MonoidAlgebra ℂ (G0g D.nd)), ∀ F ∈ D.naut.typeV i PI,
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z F ∈ D.naut.typeV i PI

def typeSum (D : D7) (i : D.nd.Loc) (o : Option (D.nd.X i)) : Submodule ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
  ⨆ P ∈ {P | D.naut.ptV i P = o}, D.naut.typeV i P

structure Sec (D : D7) (i : D.nd.Loc) where

  Φ : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i) →+ D.what₂.Mt (D.nd.mu i) (D.nd.j i)
  inj : Function.Injective Φ
  semi : ∀ (k : KK D.nd i) v, Φ (k • v) = (D.naut.iotaQC i (D.naut.iotaQ i k)) • Φ v
  eig : ∀ x, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, Φ u ∈ typeSum D i (some x)
  split : ∀ y : D.what₂.MtL (D.nd.mu i) (D.nd.j i), D.what₂.jMt _ _ y - Φ (D.nd.prMt i y) ∈ typeSum D i none

def PrType (D : D7) : Prop :=
  ∀ i (PI : D.naut.AV i) (x : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ x ∈ D.naut.typeV i PI →
    (∀ p, D.naut.ptV i PI = some p → D.nd.prMt i x ∈ heckeEig (D.nd.T i) (D.nd.act i) p) ∧
    (D.naut.ptV i PI = none → D.nd.prMt i x = 0)

def ParSurj (D : D7) : Prop :=
  ∀ i x Sig, HasParamX D.nd D.naut i x Sig →
    ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w

def SerLL (D : D7) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]) (h : GL (Fin D.R.r) (ZMod (D.host.g k))),
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.ntypes.eSer k f).coeff h

def CoeffRingsHaveRootsOfUnity (D : D7) : Prop := ∀ i : D.nd.Loc, ∃ ζ : D.nd.O i, IsPrimitiveRoot ζ D.what₂.restRowsFiniteGroupCard

open Classical in

def SerEq (D : D7) (lz : ∀ k : Fin 2, LzData (D.host.g k)) : Prop :=
  ∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]),
    D.ntypes.eSer k f = ∑ τ : (lz k).Irr D.R.r, if (lz k).lab τ = f then (lz k).idem τ else 0

def mk {D : D7} (lz : ∀ k : Fin 2, LzData (D.host.g k)) (h1 : SerEq D lz) (h2 : SerLL D) (h3 : CoeffRingsHaveRootsOfUnity D)
    (Ω : TameOm D) (h4 : LabIne Ω) (h5 : LabChar D) (Z : CenO D) (h6 : ZLStable D) (h7 : PrType D)
    (h8 : ParSurj D) : Pend D where
  lz := lz
  eSer_eq := h1
  eSer_LL := h2
  zetaPrimitiveRoot := h3
  om := Ω.om
  om_one := Ω.om_one
  om_mul := Ω.om_mul
  tameInertiaChar_mul_root := Ω.tameInertiaChar_mul_root
  om_wild := Ω.om_wild
  om_open := Ω.om_open
  om_inj := Ω.om_inj
  om_tg := Ω.om_tg
  inertiaCharpoly_eigenvalues := h4
  inertiaCharpoly_character := h5
  zO := Z.zO
  zO_comm := Z.zO_comm
  zL_stable := h6
  zO_act := Z.zO_act
  prMt_type := h7
  Par_surj := h8
  kty i PI k v := {τ | ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v ((lz k).idem τ)) F ≠ 0}
  kty_spec _ _ _ _ _ := Iff.rfl

end GlobalTheory.PendOf

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
section
noncomputable section

namespace GlobalTheory.LiftLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

section Rec

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def ParUpRec (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
    (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) ≤ eigC N A i x

def DownMemRec (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
    (eigC N A i x).map (what₂.thetaP (N.mu i) (N.j i)) ≤ MjSig N A i Sig

def TypeNZRec (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ F ∈ eigC N A i x, what₂.thetaP (N.mu i) (N.j i) F = 0 → F = 0

def GoodPartRec (i : N.Loc) : Prop :=
  goodPartM N A i = ⨆ x ∈ ZgoodN N A i, ⨆ Sig ∈ {Sig | HasParamX N A i x Sig}, MjSig N A i Sig

def PtDet (i : N.Loc) : Prop :=
  ∀ P P' : A.AV i, (∀ w, IsSplitPl H w → A.locV i P w = A.locV i P' w) → A.ptV i P = A.ptV i P'

def LocCongr (i : N.Loc) : Prop :=
  ∀ Sig Sig' : List (Part A.CG), (∀ p ∈ Sig, 1 ≤ p.d) → (∀ p ∈ Sig', 1 ≤ p.d) →
    (∀ w, IsSplitPl H w → isoLoc N A Sig w = isoLoc N A Sig' w) →
    ∀ w, IsSplitPl H w → isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      isoLoc N A (twistIso N A (Sig' ++ [muPart N A i]) A.etaTinv) w

def ThetaPt (i : N.Loc) : Prop := ∀ σ P, AtM N A i σ → thetaOf N A i σ P → ∃ x, A.ptV i P = some x

def LabCompat (i : N.Loc) : Prop := ∀ σ Sig, HasParamW N A i σ Sig → (N.goodRow σ ↔ goodSig N A Sig)

def GoodParamX (i : N.Loc) : Prop := ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig → goodSig N A Sig

def AtMOfParam (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig → ∀ σ, HasParamW N A i σ Sig → AtM N A i σ

def PtAt (i : N.Loc) : Prop :=
  ∀ P : A.AV i, (∃ x : N.X i, ∀ w, SplitOut N i w → ∃ p : Polynomial (N.O i),
    p.map (iotaO N A i) = galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) ∧
    p.map (IsLocalRing.residue (N.O i)) = (heckePol N i x w).map (IsLocalRing.residue (N.O i))) → ∃ x, A.ptV i P = some x

def CharSum : Prop :=
  ∀ (w : PlE H) (a b χ : A.LP w) (s : ℝ), A.lpDim χ = 1 →
    A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ) ∧
    A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s ∧ A.lpChar (A.lpZero w) χ = A.lpZero w

end Rec

def RowSize (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ →
    ∀ w : PlE D.host, IsSplitPl D.host w → D.naut.unr (D.naut.locW i σ w) →
    ∀ α ∈ D.naut.frobEig (D.naut.locW i σ w),
      ‖α‖ < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)

def HeckeSplitOne (D : D7) : Prop :=
  ∀ ν ν' : D.naut.CG 1,
    (∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → D.naut.locG ν w = D.naut.locG ν' w) → ν = ν'

def ThetaOne (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∃ P, thetaOf D.nd D.naut i σ P

def LamPos (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT,
    (∀ f ∈ D.what₂.isot j σ, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = ((D.what₂.lamP μ j σ : ℝ) : ℂ) • f) ∧
    (D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ)

section Exp

open Formalism.MainNotions.IntegralHeckeForms

def CommG (D : D7) : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ (b : Bool), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g k P, HkIdx i k P →
    (D.nexp.actG i j b g).toLinearMap ∘ₗ D.nexp.hkF i j b k P = D.nexp.hkF i j b k P ∘ₗ (D.nexp.actG i j b g).toLinearMap

def IntRest (D : Formalism.BasicNotions.D7) (E : XD D) : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool),
    (∀ g, (D.nexp.Bsup i j b).map ((D.nexp.actG i j b g).toLinearMap.restrictScalars (D.ntw.O i)) ≤
      D.nexp.Bsup i j b) ∧
    Submodule.span (FractionRing (D.ntw.O i)) (Mall D.nexp i j b : Set (D.nexp.Fm i j b)) =
      Fm0 D.nexp i j b ∧
    (∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M, (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q →
      Disjoint Q (D.ntw.S0 i) → Disjoint Q (D.nexp.lev i j b a) →
      ((D.ntw.l i : D.ntw.O i) ^ c) • D.nexp.thU i j b Q M a ∈
        LinearMap.range ((Mall D.nexp i j b).subtype.rTensor _)) ∧
    (∀ k Q (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), TwOK i k Q ψ → UnrG ψ →
      ∀ a ∈ E.Dat0 i j b,
      D.nexp.thPsi i j b k Q ψ a ⊆
        ((((Fm0 D.nexp i j b).restrictScalars (D.ntw.O i)).baseChange (D.ntw.Ok i k) :
          Submodule (D.ntw.Ok i k) (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)) :
            Set (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)))

end Exp

end GlobalTheory.LiftLeaf
end
end

