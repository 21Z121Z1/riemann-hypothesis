import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LevelIndexFourierCharacter

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BlockPolyLevelMove
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial

section Lattice

variable {E : Type} [Field E] [NumberField E]

def unitLat (E : Type) [Field E] [NumberField E] (n : ℕ) : GenLat E n := ⟨stdLat E n⟩

def blockLat {n₁ n₂ : ℕ} (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) : GenLat E (n₁ + n₂) :=
  ⟨Λ₁.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
    Λ₂.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁))⟩

example {n₁ n₂ : ℕ} (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (v : Fin (n₁ + n₂) → E) :
    v ∈ (blockLat Λ₁ Λ₂).La ↔
      (fun i => v (Fin.castAdd n₂ i)) ∈ Λ₁.La ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ Λ₂.La := Iff.rfl

example (n₁ n₂ : ℕ) : (blockLat (unitLat E n₁) (unitLat E n₂)).La = (unitLat E (n₁ + n₂)).La := by
  ext v
  change ((fun i => v (Fin.castAdd n₂ i)) ∈ stdLat E n₁ ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ stdLat E n₂) ↔
    v ∈ stdLat E (n₁ + n₂)
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left]
  exact ⟨fun h i => Fin.addCases (motive := fun i => v i ∈ (1 : Submodule (𝓞 E) E)) h.1 h.2 i,
    fun h => ⟨fun i => h _, fun j => h _⟩⟩

end Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def LatAdm (l : Level H) (bad : ℕ) {n : ℕ} (Λ : GenLat E n) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt l.M

def letL (Dw : Datum H) (n₁ n₂ : ℕ) (ℓ : LtN Dw n₁) : LtN Dw (n₁ + n₂) := ⟨ℓ.1, ℓ.2.1, Fin.castAdd n₂ ℓ.2.2⟩

def letR (Dw : Datum H) (n₁ n₂ : ℕ) (ℓ : LtN Dw n₂) : LtN Dw (n₁ + n₂) := ⟨ℓ.1, ℓ.2.1, Fin.natAdd n₁ ℓ.2.2⟩

def blockPoly {K : Type} [Field K] {n₁ n₂ : ℕ} (P₁ : MvPolynomial (LtN Dw n₁) K)
    (P₂ : MvPolynomial (LtN Dw n₂) K) : MvPolynomial (LtN Dw (n₁ + n₂)) K :=
  rename (letL Dw n₁ n₂) P₁ * rename (letR Dw n₁ n₂) P₂

def blockDat {K : Type} [Field K] {n₁ n₂ : ℕ} (w₁ : (Fin n₁ → LevQ Dw l) → K) (w₂ : (Fin n₂ → LevQ Dw l) → K) :
    (Fin (n₁ + n₂) → LevQ Dw l) → K :=
  fun q => w₁ (fun i => q (Fin.castAdd n₂ i)) * w₂ (fun j => q (Fin.natAdd n₁ j))

def levMap (l : Level H) (g : Dw.La →ₗ[𝓞 E] Dw.La) : LevQ Dw l →ₗ[𝓞 E] LevQ Dw l :=
  Submodule.mapQ _ _ g (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

def moveDat {K : Type} {n : ℕ} (g : Dw.La →ₗ[𝓞 E] Dw.La) (w : (Fin n → LevQ Dw l) → K) :
    (Fin n → LevQ Dw l) → K :=
  fun q => w (fun b => levMap l g (q b))

variable (Xo : Moduli Dw l) (c : Coeff l)

def IsBeta (Dw : Datum H) {l : Level H} (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β

def FreeOfLevel (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n), LatAdm l bad Λ →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), β ≠ 0 →
    ∀ (N N' : ℕ), Λ.LevOK N l.M → Λ.LevOK N' l.M →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v' : S),
      ShortValAt Xo c nab w Λ β N P y v → (ShortValAt Xo c nab w Λ β N' P y v' ↔ v' = v)

def BlockProduct (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₁ → LatAdm l bad Λ₂ →
    ∀ N : ℕ, Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
    (LatAdm l bad (blockLat Λ₁ Λ₂) ∧ (blockLat Λ₁ Λ₂).LevOK N l.M) ∧
    ∀ (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ) (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F),
      P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ →
      blockPoly P₁ P₂ ∈ harmL c (blockLat Λ₁ Λ₂) (a₁ + a₂) ∧
      ∀ (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F)
        (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v₁ v₂ v : S),
        ShortValAt Xo c nab w₁ Λ₁ 1 N P₁ y v₁ → ShortValAt Xo c nab w₂ Λ₂ 1 N P₂ y v₂ →
        (ShortValAt Xo c nab (blockDat w₁ w₂) (blockLat Λ₁ Λ₂) 1 N (blockPoly P₁ P₂) y v ↔ v = v₁ * v₂)

def BlockBeta (Dw : Datum H) {l : Level H} (c : Coeff l) (bad : ℕ) : Prop :=
  (∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₁ → LatAdm l bad Λ₂ →
    ∀ β₁ β₂ β : c.F, IsBeta Dw c Λ₁ β₁ → IsBeta Dw c Λ₂ β₂ →
      (IsBeta Dw c (blockLat Λ₁ Λ₂) β ↔ ∃ ζ : c.F, IsOfFinOrder ζ ∧ β = ζ * (β₁ * β₂))) ∧
  ∀ (n₁ n₂ : ℕ) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₂ →
    IsBeta Dw c (unitLat E n₁) 1 ∧
      ∀ β : c.F, IsBeta Dw c (blockLat (unitLat E n₁) Λ₂) β ↔ IsBeta Dw c Λ₂ β

def LevelMove (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n), LatAdm l bad Λ →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), β ≠ 0 →
    ∀ N : ℕ, Λ.LevOK N l.M →
    ∀ (g gA : Dw.La →ₗ[𝓞 E] Dw.La) (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S),
      levR (g, gA) y y' →
      ∀ v : S, ShortValAt Xo c nab (moveDat g w) Λ β N P y' v ↔ ShortValAt Xo c nab w Λ β N P y v

def LevelMoveClass (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n), LatAdm l bad Λ →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    ∀ (x₀ : Fin n → Dw.La) (β : c.F), β ≠ 0 →
    ∀ N : ℕ, Λ.LevOK N l.M →
    ∀ (g gA : Dw.La →ₗ[𝓞 E] Dw.La), (∀ u v : Dw.La, (l.M : ℤ) ∣ Dw.EF (g u) (g v) - Dw.EF u v) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), levR (g, gA) y y' →
      ∀ v : S, ShortValAt Xo c nab (x0Dat c x₀) Λ β N P y' v ↔
        ShortValAt Xo c nab (x0Dat c fun b => g (x₀ b)) Λ β N P y v

def ShortLaws [StarRing (𝓞 E)] : Prop :=
  (∀ nab : NabV Xo c, IsNab Xo c nab → ∀ bad : ℕ,
    FreeOfLevel Xo c nab bad ∧ BlockProduct Xo c nab bad ∧ LevelMove Xo c nab bad) ∧
  ∀ bad : ℕ, BlockBeta Dw c bad

end GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BlockProductLattices
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices

open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Lat

variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}

def blockLat (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) : GenLat E (n₁ + n₂) where
  La := Λ₁.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
    Λ₂.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁))

theorem mem_blockLat (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (v : Fin (n₁ + n₂) → E) :
    v ∈ (blockLat Λ₁ Λ₂).La ↔
      (fun j => v (Fin.castAdd n₂ j)) ∈ Λ₁.La ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ Λ₂.La := Iff.rfl

end Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def LatOK {n : ℕ} (bad M : ℕ) (Λ : GenLat E n) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt M

def blockDat {n₁ n₂ : ℕ} (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F) :
    (Fin (n₁ + n₂) → LevQ Dw l) → c.F :=
  fun q => w₁ (fun b => q (Fin.castAdd n₂ b)) * w₂ (fun b => q (Fin.natAdd n₁ b))

def blockPol {n₁ n₂ : ℕ} (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F) :
    MvPolynomial (LtN Dw (n₁ + n₂)) c.F :=
  rename (fun ℓ : LtN Dw n₁ => (⟨ℓ.1, ℓ.2.1, Fin.castAdd n₂ ℓ.2.2⟩ : LtN Dw (n₁ + n₂))) P₁ *
    rename (fun ℓ : LtN Dw n₂ => (⟨ℓ.1, ℓ.2.1, Fin.natAdd n₁ ℓ.2.2⟩ : LtN Dw (n₁ + n₂))) P₂

def IndepN [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  IsNab Xo c nab →
  ∀ (n : ℕ) (Λ : GenLat E n) (N N' : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F),
    LatOK bad l.M Λ → Λ.LevOK N l.M → Λ.LevOK N' l.M → P ∈ harmL c Λ a → β ≠ 0 →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v' : S),
      ShortValAt Xo c nab w Λ β N P y v → ShortValAt Xo c nab w Λ β N' P y v' → v = v'

def BlockHarm (Dw : Datum H) (c : Coeff l) (bad : ℕ) : Prop :=
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ)
    (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F),
    LatOK bad l.M Λ₁ → LatOK bad l.M Λ₂ → P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ →
      blockPol c P₁ P₂ ∈ harmL c (blockLat Λ₁ Λ₂) (a₁ + a₂)

def BlockVal [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  IsNab Xo c nab →
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N : ℕ) (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ)
    (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F)
    (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F) (β β₁ β₂ : c.F),
    LatOK bad l.M Λ₁ → LatOK bad l.M Λ₂ → Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
    P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ → β ≠ 0 → β₁ ≠ 0 → β₂ ≠ 0 →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v₁ v₂ : S),
      ShortValAt Xo c nab (blockDat c w₁ w₂) (blockLat Λ₁ Λ₂) β N (blockPol c P₁ P₂) y v →
      ShortValAt Xo c nab w₁ Λ₁ β₁ N P₁ y v₁ → ShortValAt Xo c nab w₂ Λ₂ β₂ N P₂ y v₂ →
        algebraMap c.F S β * v = (algebraMap c.F S β₁ * v₁) * (algebraMap c.F S β₂ * v₂)

def BlockBeta (Dw : Datum H) (c : Coeff l) (bad : ℕ) : Prop :=
  KPsiIn (Dw := Dw) c →
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N : ℕ),
    LatOK bad l.M Λ₁ → LatOK bad l.M Λ₂ → Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
      (∃ ζ : c.F, (∃ k : ℕ, 0 < k ∧ ζ ^ k = 1) ∧
        betaH (Dw := Dw) c (blockLat Λ₁ Λ₂) = ζ * (betaH (Dw := Dw) c Λ₁ * betaH (Dw := Dw) c Λ₂)) ∧
      (Λ₁.La = stdLat E n₁ → betaH (Dw := Dw) c (blockLat Λ₁ Λ₂) = betaH (Dw := Dw) c Λ₂)

def BlockProd [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  BlockHarm Dw c bad ∧ BlockVal Xo c nab bad ∧ BlockBeta Dw c bad

def LevMove [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  IsNab Xo c nab →
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La)
    (κ : LevQ Dw l ≃ₗ[𝓞 E] LevQ Dw l),
    LatOK bad l.M Λ → Λ.LevOK N l.M → P ∈ harmL c Λ a → β ≠ 0 →
    (∀ x : Dw.La, κ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (gM x)) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (v v' : S),
      levR (gM, gA) y y' →
      ShortValAt Xo c nab w Λ β N P y' v' →
      ShortValAt Xo c nab (fun q => w fun b => κ.symm (q b)) Λ β N P y v → v' = v

abbrev FunQ (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)

def funDat {n : ℕ} (φ : (Fin n → FunQ Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ∑ᶠ x : Fin n → FunQ Dw l, φ x * x0Dat c (fun b => qRep (x b)) q

def LevMoveFun [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  IsNab Xo c nab →
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (φ : (Fin n → FunQ Dw l) → c.F) (β : c.F) (k : Sim Dw) (κ' : FunQ Dw l ≃ₗ[𝓞 E] FunQ Dw l),
    LatOK bad l.M Λ → Λ.LevOK N l.M → P ∈ harmL c Λ a → β ≠ 0 →
    (l.M : ℤ) ∣ k.ν l.M - 1 →
    (∀ x : Dw.La, κ' (Submodule.Quotient.mk x) = Submodule.Quotient.mk (k.f l.M x)) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (v v' : S),
      levR (k.f l.M, k.f l.A) y y' →
      ShortValAt Xo c nab (funDat c φ) Λ β N P y' v' →
      ShortValAt Xo c nab (funDat c fun x => φ fun b => κ'.symm (x b)) Λ β N P y v → v' = v

def ShortLaws [StarRing (𝓞 E)] (nab : NabV Xo c) (bad : ℕ) : Prop :=
  IndepN Xo c nab bad ∧ BlockProd Xo c nab bad ∧ LevMove Xo c nab bad

end GlobalTheory.IndefiniteRowSideFullHecke.BlockProductLattices
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.NormFactorThetaValue
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation

attribute [local instance] Over.cartesianMonoidalCategory

section TwoLifts

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def IsTwoLifts (N : ℕ) {T : Over X} (s : LB.Sec (LPow A L.L 1 T)) (x₁ x₂ : T ⟶ A)
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  Odd N ∧ x₁ ^ (N ^ 2) = 1 ∧ x₂ ^ (N ^ 2) = 1 ∧
  ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]))
    (s₁ s₂ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (U₁ U₂ : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
    α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧ α.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) x₁ U₁ ∧ IsActOf A L.L ((N : ℤ) ^ 2) U₁ s₁ s₂ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) x₂ U₂ ∧ IsActOf A L.L ((N : ℤ) ^ 2) U₂ s₂ F

end TwoLifts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def InKer {n : ℕ} (N : ℕ) (Lm : Submodule (𝓞 E) (Fin n → E))
    (hN : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ Lm) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  (∀ j, a j ^ (N ^ 2) = 1) ∧
    ∀ (f : Lm →ₗ[𝓞 E] (Fin n → 𝓞 E)) (i : Fin n), ∏ j, a j ≫ Xo.univ.t.act.act (f ⟨_, hN j⟩ i) = 1

omit [NumberField E] [IsCMField E] in
theorem nsmul_single_mem_inter {n M N : ℕ} {Λ : Lat E n} (h : Λ.Admissible M N) (j : Fin n) :
    N • (Pi.single j 1 : Fin n → E) ∈ Λ.inter := by
  refine h.2.2 ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (single_mem_stdMod j)

omit [NumberField E] [IsCMField E] in
theorem nsmul_single_mem {n M N : ℕ} {Λ : Lat E n} (h : Λ.Admissible M N) (j : Fin n) :
    N • (Pi.single j 1 : Fin n → E) ∈ Λ.L := (nsmul_single_mem_inter h j).2

def InZ {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  InKer Xo N Λ.L (nsmul_single_mem h) a

def InKernelOfAdmissibleLattice {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  InKer Xo N Λ.inter (nsmul_single_mem_inter h) a

def ptRes {S k : Type} [CommRing S] [CommRing k] (x0 : Sp S ⟶ Xo.X) (ψ : S →+* k) :
    ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap ψ) rfl

def SplitsZ {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    {J : Type} (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  (∀ i, InZ Xo h (z i)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : S →+* k) (a : Fin n → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)),
      InZ Xo h a → ∃! i, ∀ j, a j = ptRes Xo x0 ψ ≫ z i j

def IsDivPt (N : ℕ) {T : Over Xo.X} (t t' : T ⟶ Xo.univ.t.G) : Prop :=
  t' ^ N = t ∧ KilledBy Xo (halfPart l N ^ 2) t'

def pairBox (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (k : ℤ)
    (P : MvPolynomial (LtN Dw n) c.F) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y k (F b) (colOf m b)

def normFactor {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (P : MvPolynomial (LtN Dw n) c.F) : c.F :=
  β⁻¹ * ((Λ.cardCenterZero (Dw.p + Dw.q) N : ℕ) : c.F)⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹

def SplitVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n N : ℕ} {Λ : Lat E n}
    (h : Λ.Admissible l.M N) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ∃ (r : ℕ) (z : Fin r → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (t' : (Fin n → NamedCl Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → NamedCl Dw l) → Fin r → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))),
    SplitsZ Xo h y.x z ∧
    (∀ t b, IsDivPt Xo N (levPtCl Xo y.x (t b)) (t' t b)) ∧
    (∀ t i b, IsTwoLifts Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (t' t b) (F t i b)) ∧
    v = algebraMap c.F S (normFactor c Λ N β P) *
      ∑ t ∈ levelIndex Dw l n, algebraMap c.F S (cf t) * ∑ i, pairBox Xo c nab y ((N : ℤ) ^ 2) P (F t i)

def LocVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n N : ℕ} {Λ : Lat E n}
    (h : Λ.Admissible l.M N) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S'),
    φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ SplitVal Xo c nab y' h β cf P (φ v)

def InRange {n : ℕ} (Λ : Lat E n) (β : c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Λ.InGenus ∧ Λ.StdAt l.M ∧ β ≠ 0 ∧ P ∈ harmLat Dw c a Λ

def ThVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (v : S) : Prop :=
  InRange c Λ β a P ∧ ∃ h : Λ.Admissible l.M N, LocVal Xo c nab y h β cf P v

def ThValFun (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (φ : (Fin n → ConjCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (v : S) : Prop :=
  ThVal Xo c nab y Λ N β (fourier c φ) a P v

def ThValPt (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (t : Fin n → NamedCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (v : S) : Prop :=
  ThVal Xo c nab y Λ N β (Set.indicator {t} 1) a P v

def KerClaims : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (h : Λ.Admissible l.M N), Λ.InGenus → Λ.StdAt l.M →
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (x0 : Sp k ⟶ Xo.X), x0 ≫ Xo.s = sOf c k →
      (∀ a : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), InKernelOfAdmissibleLattice Xo h a → InZ Xo h a ∧ ∀ j, a j ^ N = 1) ∧
      (∀ a : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ j, KilledBy Xo (halfPart l N) (a j)) → InZ Xo h a) ∧
      Nat.card {a : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G) // InKernelOfAdmissibleLattice Xo h a} = Λ.cardCenterZero (Dw.p + Dw.q) N

def ValTot (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n N : ℕ) (Λ : Lat E n) (β : c.F)
    (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F),
    InRange c Λ β a P → Λ.Admissible l.M N → ∃! v, ThVal Xo c nab y Λ N β cf a P v

def FreeOfN (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n N N' : ℕ) (Λ : Lat E n) (β : c.F)
    (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (v : S),
    Λ.Admissible l.M N' → ThVal Xo c nab y Λ N β cf a P v → ThVal Xo c nab y Λ N' β cf a P v

def StdAgrees (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (x : Fin n → Dw.La)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (v : S), P ∈ harmLat Dw c a (Lat.std E n) →
    (ThValPt Xo c nab y (Lat.std E n) l.M 1 (fun b => Submodule.Quotient.mk (x b)) a P v ↔
      ThValAt Xo c nab y x P v)

def SumOfTranslates (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n N : ℕ) (Λ : Lat E n) (β : c.F)
    (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → NamedCl Dw l) → S), (∀ t, ThValPt Xo c nab y Λ N β t a P (w t)) →
    ThVal Xo c nab y Λ N β cf a P (∑ t ∈ levelIndex Dw l n, algebraMap c.F S (cf t) * w t)

def IsSection (nab : NabV Xo c) : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c),
    (∀ (p : TRing c.F) (y : FrPt Xo c p.R), ThVal Xo c nab y Λ N β cf a P (f p y)) → f ∈ sec Xo c a n

def IsBlockSum {n₁ n₂ : ℕ} (Λ₁ : Lat E n₁) (Λ₂ : Lat E n₂) (Λ : Lat E (n₁ + n₂)) : Prop :=
  ∀ x, x ∈ Λ.L ↔ (fun b => x (Fin.castAdd n₂ b)) ∈ Λ₁.L ∧ (fun b => x (Fin.natAdd n₁ b)) ∈ Λ₂.L

def blockMul {n₁ n₂ : ℕ} (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F) :
    MvPolynomial (LtN Dw (n₁ + n₂)) c.F :=
  MvPolynomial.rename (fun ℓ : LtN Dw n₁ => (⟨ℓ.1, ℓ.2.1, Fin.castAdd n₂ ℓ.2.2⟩ : LtN Dw (n₁ + n₂))) P₁ *
    MvPolynomial.rename (fun ℓ : LtN Dw n₂ => (⟨ℓ.1, ℓ.2.1, Fin.natAdd n₁ ℓ.2.2⟩ : LtN Dw (n₁ + n₂))) P₂

def blockFun {X : Type} {n₁ n₂ : ℕ} (φ₁ : (Fin n₁ → X) → c.F) (φ₂ : (Fin n₂ → X) → c.F) :
    (Fin (n₁ + n₂) → X) → c.F :=
  fun x => φ₁ (fun b => x (Fin.castAdd n₂ b)) * φ₂ fun b => x (Fin.natAdd n₁ b)

def ProductClaim (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n₁ n₂ N : ℕ) (Λ₁ : Lat E n₁) (Λ₂ : Lat E n₂)
    (Λ : Lat E (n₁ + n₂)) (φ₁ : (Fin n₁ → ConjCl Dw l) → c.F) (φ₂ : (Fin n₂ → ConjCl Dw l) → c.F)
    (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ) (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F) (v₁ v₂ : S),
    IsBlockSum Λ₁ Λ₂ Λ → ThValFun Xo c nab y Λ₁ N 1 φ₁ a₁ P₁ v₁ → ThValFun Xo c nab y Λ₂ N 1 φ₂ a₂ P₂ v₂ →
      ThValFun Xo c nab y Λ N 1 (blockFun c φ₁ φ₂) (a₁ + a₂) (blockMul c P₁ P₂) (v₁ * v₂)

theorem one_inZ {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {T : Over Xo.X} :
    InZ Xo h (fun _ => (1 : T ⟶ Xo.univ.t.G)) := by
  refine ⟨fun _ => one_pow _, fun f i => Finset.prod_eq_one fun j _ => ?_⟩
  haveI := Xo.univ.t.act.hom (f ⟨_, nsmul_single_mem h j⟩ i)
  exact MonObj.one_comp _

end GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SplittingOfRoots
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplittingOfRoots

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def RootsExist : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (x : Fin n → Dw.La),
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
      (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y'.x))),
      φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧
      ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y'.s (levPt Xo y'.x (x b)) (F b)

def GeoExhaust {n : ℕ} (Λ : GenLat E n) (N : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {J : Type}
    (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  ∀ (k : Type) [Field k] (ψ : S →+* k) (g : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0), g.left = spMap ψ →
    ∀ a : Fin n → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G), InZh Xo Λ N a → ∃ i, ∀ b, a b = g ≫ z i b

def IsSplitBy {n : ℕ} (Λ : GenLat E n) (N : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo x0 z ∧ GeoExhaust Xo Λ N x0 z

def ZSplits : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.LevOK N l.M →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
      ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
        (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y'.x ⟶ Xo.univ.t.G)),
        φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ IsSplitBy Xo Λ N y'.x z

def RootsAndSplitting : Prop := RootsExist Xo c ∧ ZSplits Xo c

example (n : ℕ) : GenLat.LevOK (⟨stdLat E n⟩ : GenLat E n) l.M l.M := by
  refine ⟨l.odd, dvd_rfl, ?_⟩
  simp only [GenLat.Ln, inf_idem]
  exact Submodule.smul_le_right

example (Λ : GenLat E 0) (N : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) :
    GeoExhaust Xo Λ N x0 (fun (_ : Unit) (b : Fin 0) => b.elim0) :=
  fun _ _ _ _ _ _ _ => ⟨(), fun b => b.elim0⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SplittingOfRoots
end
end

