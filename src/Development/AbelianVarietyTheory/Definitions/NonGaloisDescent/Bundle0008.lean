import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def SerLoc (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]),
    ∀ F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ',
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 → f = D.ntypes.labPar k σ' v

def TameOcc (D : D7) : Prop :=
  ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k), D.ntypes.cuspidal σ →
    Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
    ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
      Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod ∧
      ∃ φ : G D.host.E D.nd.Om,
        D.ntypes.rbar σ (D.nd.w i) (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) ^ D.host.g k

abbrev redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) :
    G D.host.E D.nd.Om →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)) :=
  mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ

def InjPrimeTo {A B : Type} [MonoidWithZero A] [Monoid B] (l : ℕ) (ι : A →* B) : Prop :=
  ∀ x y : A, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l → ι x = ι y → x = y

abbrev labSig (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) (k : Fin 2) (v : D.nd.PlG k) : (ZMod (D.host.g k))[X] :=
  D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

def TameFixed (D : D7) (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (k : Fin 2) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∀ v : D.nd.PlG k, ∃ ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i), InjPrimeTo (D.nd.l i) ι ∧
    Matrix.charpoly ((redF D i ρ (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D Sig k v)).map fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod ∧
    ∃ φ : G D.host.E D.nd.Om,
      redF D i ρ (φ * D.ntypes.tg k v * φ⁻¹) = redF D i ρ (D.ntypes.tg k v) ^ D.host.g k

def TameAnyAt (D : D7) (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (k : Fin 2) (w : PlE D.host) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∃ (v : D.nd.PlG k) (j : Fin D.R.m) (ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i))
    (e₁ e₂ : ℤ), (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧ InjPrimeTo (D.nd.l i) ι ∧
    Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D Sig k v)).map
        fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ e₁)).prod ∧
    D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) =
      ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i)
        (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
          ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))) ^ e₂

def FullLab (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k), (labSig D Sig k v).natDegree =
    D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

def TameSum (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)), (∃ x, HasParamX D.nd D.naut i x Sig) → FullLab D Sig →
    IsCuspIso D.nd D.naut Sig →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ →
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i Sig ρ k ∧
      ∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i Sig ρ k w

def WildOne (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (L : D.naut.LP (D.naut.plGw k v)),
    (D.naut.items₂ k _ L).natDegree = D.naut.lpDim L →
      ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.naut.inePol L s = (X - 1) ^ D.naut.lpDim L

def GalAway (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)),
      Continuous (fun g => ((r g : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i)))) ∧
      ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        D.naut.wdOf i r w = D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)

def FrobDense (D : D7) : Prop :=
  ∀ T : Set (PlE D.host), T.Finite → Dense {s : G D.host.E D.nd.Om | ∃ w : PlE D.host, w ∉ T ∧ IsSplitPl D.host w ∧
    ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) s}

def PointPar (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (π : D.naut.CG D.R.r), HasParamX D.nd D.naut i x [⟨D.R.r, π, 1⟩] →
    D.naut.csd π ∧ D.naut.ralg π

def RedVia (D : D7) (i : D.nd.Loc) (k : Fin 2)
    (ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i)) : Prop :=
  ∀ (p : (D.nd.O i)[X]) (s : Multiset (Fb (D.host.g k) (D.host.g_prime k))),
    p.map (iotaO D.nd D.naut i) = (s.map fun x => X - C (D.ntypes.teichC k x)).prod →
    p.map ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) = (s.map fun x => X - C (ι x)).prod

def IotaLoc (D : D7) : Prop :=
  ∀ i : D.nd.Loc, ∃ (B : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField B ≃+*
      Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i))),
    (∀ y : D.nd.O i, ∃ h : iotaO D.nd D.naut i y ∈ B,
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (κ (IsLocalRing.residue B ⟨_, h⟩)) = D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)) ∧
    ∀ k v x, ∃ h : D.ntypes.teichC k x ∈ B, D.ntypes.iota k v (D.nd.w i) x = κ (IsLocalRing.residue B ⟨_, h⟩)

def RowModel (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
    ∃ (i' : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i')),
      D.nd.w i' = D.nd.w i ∧ HasParamW D.nd D.naut i' σ [⟨D.R.r, π, 1⟩] ∧ D.naut.csd π ∧ D.naut.ralg π ∧
      IsRepOfSig D.nd D.naut i' [⟨D.R.r, π, 1⟩] ρ

def TwistInv (D : D7) : Prop :=
  (∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv = π) ∧
  ∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π

def CharLaws (D : D7) : Prop :=
  ∀ (w : PlE D.host) (a χ χ' : D.naut.LP w), D.naut.lpDim χ = 1 → D.naut.lpDim χ' = 1 →
    D.naut.lpChar (D.naut.lpChar a χ) χ' = D.naut.lpChar a (D.naut.lpChar χ χ') ∧
    D.naut.lpChar a (D.naut.lpUnr w {1}) = a

def MultOne (D : D7) : Prop :=
  ∀ (a : ℕ) (π π' : D.naut.CG a), 1 ≤ a → (∀ w, D.naut.locG π w = D.naut.locG π' w) → π = π'

def GoodBase (D : D7) : Prop := ∀ σ, D.nd.goodRow (D.what₂.ft0 σ)

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal

namespace GlobalTheory.TwSys

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsTameInertiaElementAtTwistPrime (i : X.Tw) (z : GE N) : Prop :=
  ∃ v ∈ X.pD i, ∃ A : ValuationSubring N.Om, IsPlaceOver A v ∧ z ∈ Ine (F := D.host.E) A ∧
    IsUnit (((X.delta i z : (X.O0 i)ˣ) : X.O0 i) ^ 2 - 1) ∧
    ∀ U : Subgroup (GE N), IsOpen (U : Set (GE N)) → U.Normal →
      ∃ n : ℕ, Nat.Coprime n (X.l i * Ideal.absNorm v.asIdeal) ∧ z ^ n ∈ U

def Over (P v : PlE D.host) : Prop := v = P ∨ IsConjPl D.host P v

def GoodChar (i : X.Tw) (M : ℕ) (P : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) : Prop :=
  IsOpen (d.ker : Set (GE N)) ∧ AntiHom X.cc d ∧ TrivAbove d (X.l i) ∧
    (∀ v, ¬ Over P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, d σ = 1) ∧
    (∀ v, Over P v → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ c, ∃ σ ∈ Ine (F := D.host.E) A, d σ = c)

def AdmFam (i : X.Tw) (M : ℕ) (H : Subgroup (GE N)) (S : Finset (PlE D.host))
    (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  IsOpen (H : Set (GE N)) ∧ H.Normal ∧
    (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → Ine (F := D.host.E) A ≤ H) ∧
    ∀ P, P ∉ S → IsSplitPl D.host P → DecV N P ≤ H → GoodChar X i M P (d P)

def SlopeTestRemainingChoices (i : X.Tw) (M : ℕ) (A : Finset (PlE D.host)) {ι : Type} (P : ι → PlE D.host)
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  (∀ q v, Over (P q) v → IsSplitPl D.host v ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E v = 1 ∧
      v ∉ X.S0 i ∧ v ∉ A ∧ normV v % (2 * X.l i ^ M) = 1) ∧
    (∀ q q', Over (P q) (P q') → q = q') ∧ ∀ q, GoodChar X i M (P q) (d q)

def Steps (i : X.Tw) (M : ℕ) (H : Subgroup (GE N)) (z : GE N) {R : ℕ} (P : Fin R ⊕ Fin R → PlE D.host)
    (d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  (∀ a (σ : GE N), IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ H) ∧
    ∀ a b (σ : GE N), IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ →
      d (.inl b) σ = Multiplicative.ofAdd (if a = b then 1 else 0)

def IsQ {ι : Type} (P : ι → PlE D.host) (Q : Finset (PlE D.host)) : Prop := ∀ v, v ∈ Q ↔ ∃ q, Over (P q) v

abbrev Del (i : X.Tw) (M : ℕ) (ι : Type) : Type := Multiplicative (ι → ZMod (X.l i ^ M))

abbrev abelian₂ (i : X.Tw) (M : ℕ) (ι : Type) : Type := MonoidAlgebra (X.O0 i) (Del X i M ι)

def delAll (i : X.Tw) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) :
    GE N →* Del X i M ι where
  toFun g := Multiplicative.ofAdd fun q => Multiplicative.toAdd (d q g)
  map_one' := by simp; rfl
  map_mul' g h := by simp only [map_mul, toAdd_mul]; rfl

open Classical in

def toLam (i : X.Tw) (M : ℕ) (ι : Type) : MvPolynomial ι (X.O0 i) →ₐ[X.O0 i] abelian₂ X i M ι :=
  MvPolynomial.aeval fun q => MonoidAlgebra.of (X.O0 i) (Del X i M ι) (Multiplicative.ofAdd (Pi.single q 1)) - 1

def repOn {G O Λ : Type} [Group G] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : G →* GL (Fin r) O) (κ : G →* Λˣ)
    (B : Type) [AddCommGroup B] [Module Λ B] : Representation Λ G (Fin r → B) where
  toFun g := ((κ g : Λˣ) : Λ) • matAct ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ))
  map_one' := by simp [matAct_one]
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, Matrix.map_mul, matAct_mul]
    rw [smul_mul_smul_comm]

variable {X} (bkP : BKPh X)

open Classical in

def bkOn (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ]
    (κ : GE N →* Λˣ) (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    (v : PlE D.host) : Submodule Λ (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) :=
  if hv : v ∈ placesOver D.host.E (X.l i) then
    Submodule.span Λ {x | ∃ (z : Z1 ((repOn ρ κ B).comp (DecV N v).subtype))
      (c : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin r → ↥(bkP.br i v hv).LL.1)
      (y : ↥(DecV N v) → Fin r → X.O0 i) (b : B),
      c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ) ∧
      (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) ∧
      (∀ g a, (z : ↥(DecV N v) → Fin r → B) g a = algebraMap (X.O0 i) Λ (y g a) • b) ∧
      x = Submodule.Quotient.mk z}
  else ⊥

def selOn (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ]
    (κ : GE N →* Λˣ) (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    (Q : Finset (PlE D.host)) : Submodule Λ (H1 (repOn ρ κ B)) :=
  Formalism.GaloisCohomology.SelAll (repOn ρ κ B) N.plOm
    (Formalism.GaloisCohomology.bkCond (repOn ρ κ B) N.plOm (X.l i) (Spl i ∪ ↑Q) (bkOn bkP i ρ κ B))

def delInv (i : X.Tw) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) :
    GE N →* (abelian₂ X i M ι)ˣ :=
  ((MonoidAlgebra.of (X.O0 i) (Del X i M ι)).toHomUnits.comp (delAll X i M d))⁻¹

def Computes (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))))
    (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)) : Prop :=
  ∃ e : ∀ (B : Type) [AddCommGroup B] [Module (abelian₂ X i M ι) B] [TopologicalSpace B] [DiscreteTopology B],
      (∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) →
      (↥(LinearMap.ker (matAct (M := B) Φ)) ≃ₗ[abelian₂ X i M ι] ↥(selOn bkP i (Tgl i s) (delInv i M d) B Q)),
    ∀ (B B' : Type) [AddCommGroup B] [Module (abelian₂ X i M ι) B] [TopologicalSpace B] [DiscreteTopology B]
      [AddCommGroup B'] [Module (abelian₂ X i M ι) B'] [TopologicalSpace B'] [DiscreteTopology B']
      (hB : ∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) (hB' : ∀ b : B', ∃ n : ℕ, (X.l i ^ n) • b = 0)
      (f : B →ₗ[abelian₂ X i M ι] B') (x : ↥(LinearMap.ker (matAct (M := B) Φ))) (x' : ↥(LinearMap.ker (matAct (M := B') Φ)))
      (z : Z1 (repOn (Tgl i s) (delInv i M d) B)) (z' : Z1 (repOn (Tgl i s) (delInv i M d) B')),
      (∀ c, x'.1 c = f (x.1 c)) → (∀ g c, z'.1 g c = f (z.1 g c)) →
      (e B hB x).1 = Submodule.Quotient.mk z → (e B' hB' x').1 = Submodule.Quotient.mk z'

def valE (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) (x : R) : ℝ≥0∞ :=
  ((IsDiscreteValuationRing.addVal R x : ℕ∞) : ℝ≥0∞) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ≥0∞)

def SelPoly (i : X.Tw) (s : X.Sig i) (M : ℕ) {ι : Type} [Fintype ι]
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (F : MvPolynomial ι (X.O0 i)) : Prop :=
  ∀ (k : ℕ) (u : ι → (X.Ok i k)ˣ) (ψ : GE N →* (X.Ok i k)ˣ), (∀ q, u q ^ (X.l i ^ M) = 1) →
    (∀ g, ψ g = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) →
    sLen bkP i s k Q ψ =
      valE (X.Ok i k) (X.l i) (MvPolynomial.eval₂ (phiK X i k) (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) F)

def GalHyp (i : X.Tw) (s : X.Sig i) : Prop :=
  IsotypicValuationAtRing bkP i s ∧ ValuationStabilityAtRing X i s ∧ SelfDual i s ∧ NoJump bkP i s ∧ True ∧ Gen.adm3 D ∧ 100 ≤ D.R.r

end GlobalTheory.TwSys

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob
section
noncomputable section

namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {D : D7} (i : D.nd.Loc)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def lenCob {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(C ⊓ (ReciprocityTheory.Gal.B1 (WKG M) : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

def InCut (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (f : GE D.nd → KOG (D.nd.O i) k) : Prop :=
  locFun i M w hw f ∈ Submodule.span (Br.OLL D.nbr i w hw) (GlobalTheory.Pass.cutCoc i w hw r Xs M)

end GlobalTheory.Cut

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MatKOSmulOne
section
noncomputable section

namespace GlobalTheory.Cut.Check

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Mat
variable {O : Type} [CommRing O] [IsDomain O] {k : ℕ}

theorem matKO_mk (A : Matrix (Fin k) (Fin k) O) (v : Fin k → FractionRing O) :
    matKO A (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O))).mulVec v) := rfl

theorem matKO_mul (A B : Matrix (Fin k) (Fin k) O) (x : KOG O k) :
    matKO (A * B) x = matKO A (matKO B x) := by
  induction x using Submodule.Quotient.induction_on with
  | H v => rw [matKO_mk, matKO_mk, matKO_mk, Matrix.mulVec_mulVec, Matrix.map_mul]

theorem matKO_smul_one (a : O) (x : KOG O k) :
    matKO (a • (1 : Matrix (Fin k) (Fin k) O)) x = a • x := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [matKO_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    funext j
    have : ∀ x, (a • (1 : Matrix (Fin k) (Fin k) O)) j x = if j = x then a else 0 := fun x => by
      simp [Matrix.one_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, this, Pi.smul_apply]
    simp [apply_ite, Algebra.smul_def]

theorem WKG_eq_matKO {Γ : Type} [Group Γ] (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) :
    WKG M g x = matKO (M g) x := by
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl
end Mat

variable {D : D7} (i : D.nd.Loc)

theorem mem_ccOff_of {Xs : Set (D.nd.X i)} {π : D.nd.X i} {f : D.nd.X i → D.nd.O i} (hf : f ∈ D.nd.T i)
    (h : ∀ x ∈ Xs, x ∉ D.nd.Z i → f x = 0) : f π ∈ ccOff i Xs π :=
  Ideal.subset_span ⟨f, hf, h, rfl⟩

theorem ccOff_univ (π : D.nd.X i) : ccOff i Set.univ π = ccAt (D.nd.T i) (D.nd.Z i) π := by
  apply le_antisymm
  · rw [ccOff, Ideal.span_le]
    rintro _ ⟨f, hf, h, rfl⟩
    refine Ideal.mem_map_of_mem ((Pi.evalRingHom (fun _ => D.nd.O i) π).comp (D.nd.T i).val.toRingHom)
      (x := (⟨f, hf⟩ : D.nd.T i)) ?_
    rw [ccIdeal, RingHom.mem_ker]
    funext y
    exact h y.1 trivial y.2
  · rw [ccAt, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [ccIdeal, RingHom.mem_ker] at hf
    exact mem_ccOff_of i f.2 fun x _ hx => congrFun hf ⟨x, hx⟩

theorem vccOff_univ (π : D.nd.X i) : vccOff i Set.univ π = D.nd.vcc i π := by
  rw [vccOff, ccOff_univ]; rfl

theorem ccOff_anti {Xs Xs' : Set (D.nd.X i)} (h : Xs ⊆ Xs') (π : D.nd.X i) : ccOff i Xs' π ≤ ccOff i Xs π :=
  Ideal.span_mono (by
    rintro _ ⟨f, hf, h0, rfl⟩
    exact ⟨f, hf, fun x hx => h0 x (h hx), rfl⟩)

theorem ccOff_eq_top {Xs : Set (D.nd.X i)} (h : ∀ x ∈ Xs, x ∈ D.nd.Z i) (π : D.nd.X i) : ccOff i Xs π = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact mem_ccOff_of i (f := 1) (one_mem _) fun x hx hz => absurd (h x hx) hz

theorem ccOff_ne_bot (Xs : Set (D.nd.X i)) {π : D.nd.X i} (hπ : π ∈ D.nd.Z i) : ccOff i Xs π ≠ ⊥ := by
  classical
  have key : ∀ x : D.nd.X i, ∃ f ∈ D.nd.T i, f π ≠ 0 ∧ (x ≠ π → f x = 0) := by
    intro x
    by_cases hx : x = π
    · exact ⟨1, one_mem _, one_ne_zero, fun h => absurd hx h⟩
    · obtain ⟨f, hf, hne⟩ := D.nd.T_sep i x π hx
      refine ⟨f - algebraMap _ _ (f x), sub_mem hf (Subalgebra.algebraMap_mem _ _), ?_, fun _ => ?_⟩
      · simpa [sub_eq_zero] using hne.symm
      · simp
  choose f hf h1 h2 using key
  have hm : (∏ x, f x) π ∈ ccOff i Xs π :=
    mem_ccOff_of i (prod_mem fun x _ => hf x) fun x _ hz => by
      rw [Finset.prod_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ x) (h2 x fun h => hz (h ▸ hπ))
  intro h
  rw [h, Ideal.mem_bot, Finset.prod_apply] at hm
  exact (Finset.prod_ne_zero_iff.2 fun x _ => h1 x) hm

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i) (Xs : Set (D.nd.X i))

theorem inR'_one : InR' D.nd r S 1 :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, by funext x; simp⟩

theorem inY_yg (γ : GE D.nd) : InY D.nd r S (yg D.nd r S γ) :=
  ⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one i r S, by simp⟩

theorem yg_eq (γ : GE D.nd) (x' : S.X') :
    yg D.nd r S γ x' = (rTwO D.nd i r (S.p x') γ - 1) * Eel D.nd S x' := by
  simp [yg, rTwO, twistM, sub_mul]

theorem cocW_unram {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) (hU : UnrOut i r Xs)
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) (v) (h1 : v ∉ placesOver D.host.E (D.nd.l i))
    (h2 : v ∉ D.nd.S i) (h3 : v ∉ D.nd.Q i) (γ) (hγ : γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) : c γ = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, -, h0, rfl⟩ := hc
    exact h0 _ (inY_yg i r S γ) fun x' hx => by rw [yg_eq, hU v h1 h2 h3 _ hx γ hγ]; simp
  | zero => rfl
  | add a b _ _ ha hb => simp [ha, hb]
  | smul a b _ hb => simp [hb]

theorem cocW_empty {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) :
    cocW i r S ∅ ψ = ⊥ := by
  rw [cocW, Submodule.span_eq_bot]
  rintro _ ⟨φ, -, h0, rfl⟩
  funext γ
  exact h0 _ (inY_yg i r S γ) fun x' hx => hx.elim

theorem cocW_mono {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) {Xs Xs' : Set (D.nd.X i)}
    (h : Xs ⊆ Xs') : cocW i r S Xs ψ ≤ cocW i r S Xs' ψ :=
  Submodule.span_mono (by
    rintro _ ⟨φ, h1, h0, rfl⟩
    exact ⟨φ, h1, fun y hy hz => h0 y hy fun x' hx => hz x' (h hx), rfl⟩)

theorem cocW_cocycle {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hψ : ∀ g, M g = (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • ψ fun x' => rO D.nd i r (S.p x') g)
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) (g h : GE D.nd) :
    c (g * h) = c g + WKG M g (c h) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, h1, -, rfl⟩ := hc
    have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g :=
      ⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩
    have e : yg D.nd r S (g * h) = yg D.nd r S g +
        (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
          ((fun x' => rO D.nd i r (S.p x') g) * yg D.nd r S h) := by
      funext x'
      simp only [yg, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, map_mul, mul_inv, Units.val_mul, mul_sub,
        smul_sub, Matrix.mul_smul, smul_smul, mul_assoc]
      abel
    have e2 : ∀ (a : D.nd.O i) (A : Matrix (Fin k) (Fin k) (D.nd.O i)) x, matKO (a • A) x = a • matKO A x := by
      intro a A x
      rw [← matKO_smul_one, ← matKO_mul, smul_mul_assoc, one_mul]
    simp only []
    rw [e, map_add, map_smul, h1 _ hg _ (inY_yg i r S h), WKG_eq_matKO, hψ, e2]
  | zero => simp
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb, map_add]; abel
  | smul a b _ hb => simp only [Pi.smul_apply, hb, map_smul, smul_add]

theorem cocW_quad {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) {v} (hq : QuadAt i r Xs v)
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) (γ) (hγ : γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    matKO (ψ fun x' => rO D.nd i r (S.p x') γ) (c γ) = c γ := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, h1, h0, rfl⟩ := hc
    have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') γ :=
      ⟨1, fun _ => 1, fun _ => γ, fun _ => one_mem _, by funext x; simp⟩
    have hn : InR' D.nd r S (-1) :=
      ⟨1, fun _ => -1, fun _ => 1, fun _ => neg_mem (one_mem _), by funext x; simp⟩
    have hY : InY D.nd r S ((fun x' => rO D.nd i r (S.p x') γ) * yg D.nd r S γ - yg D.nd r S γ) :=
      ⟨2, ![fun x' => rO D.nd i r (S.p x') γ, -1], fun _ => γ,
        fun j => by fin_cases j; exacts [hg, hn], by simp [Fin.sum_univ_two, sub_eq_add_neg]⟩
    have := h0 _ hY fun x' hx => by
      have hq' := hq _ hx γ hγ
      have e : ((fun x' => rO D.nd i r (S.p x') γ) * yg D.nd r S γ - yg D.nd r S γ) x' =
          (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • (((rO D.nd i r (S.p x') γ - 1) *
            (rO D.nd i r (S.p x') γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i))) *
              Eel D.nd S x') := by
        simp only [yg, Pi.sub_apply, Pi.mul_apply, mul_sub, sub_mul, smul_sub, Matrix.mul_smul, Matrix.smul_mul,
          smul_smul, Units.inv_mul, one_smul, mul_assoc, one_mul, mul_one]
        abel
      rw [e, hq']; simp
    rw [map_sub, sub_eq_zero, h1 _ hg _ (inY_yg i r S γ)] at this
    exact this
  | zero => simp
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb, map_add]
  | smul a b _ hb => simp only [Pi.smul_apply, hb, map_smul]

end GlobalTheory.Cut.Check

end
end

