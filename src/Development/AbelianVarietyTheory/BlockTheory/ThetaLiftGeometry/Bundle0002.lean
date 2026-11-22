import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.FrobeniusRankParts
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistedRepresentations

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

section Twist

variable {Γ : Type} [Group Γ] {O : Type} [CommRing O] {a : ℕ}

def twistRep (ρ : Γ →* GL (Fin a) O) (ξ : Γ →* Oˣ) : Γ →* GL (Fin a) O where
  toFun g := Units.map (Matrix.scalar (Fin a) : O →+* Matrix (Fin a) (Fin a) O).toMonoidHom (ξ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    ext1
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    have hc : ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) * Matrix.scalar (Fin a) (ξ h : O) =
        Matrix.scalar (Fin a) (ξ h : O) * ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) :=
      ((Matrix.scalar_commute (ξ h : O) (fun r => Commute.all _ r) _).eq).symm
    rw [mul_assoc, mul_assoc, ← mul_assoc (Matrix.scalar (Fin a) (ξ h : O)), ← hc, mul_assoc]

theorem twistRep_val (ρ : Γ →* GL (Fin a) O) (ξ : Γ →* Oˣ) (g : Γ) :
    ((twistRep ρ ξ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) =
      (ξ g : O) • ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) := by
  change Matrix.scalar (Fin a) (ξ g : O) * _ = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

end Twist

section Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def UnramOverTypePrimes (i : N.Loc) (ξ : G H.E N.Om →* (N.O i)ˣ) : Prop :=
  ∀ k : Fin 2, N.l i ≠ H.g k → ∀ w ∈ placesOver H.E (H.g k), ∀ B : ValuationSubring N.Om,
    IsPlaceOver (F := H.E) B w → ∀ σ ∈ Ine (F := H.E) B, ξ σ = 1

def IsRankPart (i : N.Loc) (x : N.X i) (ρ' : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ' g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
  IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ') ∧
  ∀ w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ' σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)) =
      heckePol N i x w

theorem IsRankPart.charpoly_frob {i : N.Loc} {x : N.X i} {ρ' : G H.E N.Om →* GL (Fin R.r) (N.O i)}
    (h : IsRankPart N i x ρ') {r : G H.E N.Om →* GL (Fin R.nV) (N.O i)} (hr : IsHeckeGalois N i x r)
    {w : PlE H} (hw : SplitOut N i w) {B : ValuationSubring N.Om} {σ : G H.E N.Om}
    (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    ((r σ : GL (Fin R.nV) (N.O i)) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).charpoly =
      ((ρ' σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)) := by
  rw [hr.2.2 w hw B σ hB hσ, h.2.2 w hw B σ hB hσ]

theorem mem_ZgoodN_of_param (A : NAut N) {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)}
    (hx : HasParamX N A i x Sig) (hg : goodSig N A Sig) : x ∈ ZgoodN N A i := by
  obtain ⟨P, hP, hBC⟩ := hx
  refine ⟨⟨P, hP, _, hBC, ?_⟩, Sig, ⟨P, hP, hBC⟩, hg⟩
  simp [twistIso, muPart]

end Local

def RhoOfGoodPoint (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)),
    x ∈ ZN D.nd D.naut i → HasParamX D.nd D.naut i x Sig → goodSig D.nd D.naut Sig →
    ∃ (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (ξ : G D.host.E D.nd.Om →* (D.nd.O i)ˣ),
      IsRepOfSig D.nd D.naut i Sig ρ ∧
      Continuous (fun g => ((ξ g : (D.nd.O i)ˣ) : D.nd.O i)) ∧
      UnramOverTypePrimes D.nd i ξ ∧
      IsRankPart D.nd i x (twistRep ρ ξ)

end GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistedRepresentations

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TameEigenvaluesTypePrimes
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

open Polynomial Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable (D : D7)

abbrev plBar (k : Fin 2) (v : D.nd.PlG k) : ValuationSubring D.nd.Om :=
  D.nd.plOm.1 (D.naut.plGw k v)

def Guard (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) : Prop :=
  D.nd.goodRow σ ∧ D.ntypes.cuspidal σ ∧ D.what₂.isot (D.nd.j i) σ ≠ ⊥ ∧ D.nd.l i ≠ D.host.g k

def IsFrobAtType (k : Fin 2) (v : D.nd.PlG k) (φ : G D.host.E D.nd.Om) : Prop :=
  IsFrob (F := D.host.E) (plBar D k v) (normV (D.naut.plGw k v)) φ

def IsWildAtType (k : Fin 2) (v : D.nd.PlG k) (s : G D.host.E D.nd.Om) : Prop :=
  ∀ y : D.nd.Om, y ≠ 0 → (plBar D k v).valuation (s y / y - 1) < 1

def TameEigenvalues (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
      Matrix (Fin D.R.r) (Fin D.R.r)
        (Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i)))).charpoly =
    ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
      X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod

def FrobConj (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k)
    (φ : G D.host.E D.nd.Om) : Prop :=
  D.ntypes.rbar σ (D.nd.w i) (φ * D.ntypes.tg k v * φ⁻¹) =
    D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) ^ D.host.g k

def TameGeneratorAtTypePrime : Prop :=
  ∀ (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2), Guard D σ i k → ∀ v : D.nd.PlG k,
    TameEigenvalues D σ i k v ∧ ∃ φ : G D.host.E D.nd.Om, IsFrobAtType D k v φ ∧ FrobConj D σ i k v φ

def TameAtTypePrimeStrong : Prop :=
  ∀ (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2), Guard D σ i k → ∀ v : D.nd.PlG k,
    (∀ s : G D.host.E D.nd.Om, IsWildAtType D k v s → D.ntypes.rbar σ (D.nd.w i) s = 1) ∧
    TameEigenvalues D σ i k v ∧
    ∀ φ : G D.host.E D.nd.Om, IsFrobAtType D k v φ → FrobConj D σ i k v φ

theorem exists_isFrobAtType (k : Fin 2) (v : D.nd.PlG k) : ∃ φ, IsFrobAtType D k v φ :=
  exists_isFrob (D.nd.plOm.2 _)

theorem tameGenerator_of_strong (h : TameAtTypePrimeStrong D) : TameGeneratorAtTypePrime D := by
  intro σ i k hg v
  obtain ⟨φ, hφ⟩ := exists_isFrobAtType D k v
  exact ⟨(h σ i k hg v).2.1, φ, hφ, (h σ i k hg v).2.2 φ hφ⟩

theorem root_ne_zero (σ : D.what₂.FT) (hσ : D.nd.goodRow σ) (k : Fin 2) (v : D.nd.PlG k) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ x ∈ Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v), x ≠ 0 := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rintro x hx rfl
  have h0 := ((hσ k).1.1 v).2.2
  have hr := (Polynomial.mem_roots'.mp hx).2
  rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at hr
  exact h0 ((map_eq_zero_iff _ (algebraMap (ZMod (D.host.g k)) _).injective).mp hr)

example (i : D.nd.Loc) : D.what₂.places.resChar (D.nd.w i) = D.nd.l i := D.nd.w_l i

end GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

end
end

