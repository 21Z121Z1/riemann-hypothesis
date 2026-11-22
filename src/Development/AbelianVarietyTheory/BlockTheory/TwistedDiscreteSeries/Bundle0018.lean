import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HolomorphicLowestType
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT

namespace GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def LowIrr (M : DSModel V S) : Prop :=
  ∀ τ, IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ))

end Model

def ModelLow : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), LowSm M ∧ LowIrr M

section Base

variable {D : D7}

abbrev pW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D τ)).1

abbrev qW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D τ)).2

theorem pW_add_qW (i : Fin D.R.m) (τ : D.what₂.Tau) : pW i τ + qW i τ = (Wc D i).rank :=
  sig_sum _ (D.sp.W_sig _) _

def blockIx (i : Fin D.R.m) (τ : D.what₂.Tau) : Fin (pW i τ) ⊕ Fin (qW i τ) ≃ Fin (Wc D i).rank :=
  finSumFinEquiv.trans (finCongr (pW_add_qW i τ))

def blockWeight₂ (i : Fin D.R.m) (τ : D.what₂.Tau) : Fin (Wc D i).rank → ℝ := fun a =>
  ((Formalism.L2.NTheta.kapW (D.hc τ) (pW i τ) (qW i τ) ((blockIx i τ).symm a) : ℤ) : ℝ)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (A) in

structure BaseHol : Prop where
  lab_eq : ∀ ρ : D.what₂.Tau, lab (sg0 D A) ρ = ρ
  labE_eq : ∀ ρ : D.what₂.Tau, labE (sg0 D A) ρ = tauE D ρ
  par_eq : ∀ (i : Fin D.R.m) (ρ : D.what₂.Tau), parAt (Wc D i) (sg0 D A) ρ =
    Formalism.L2.NTheta.holPar (pW i ρ) (qW i ρ) (Formalism.L2.NTheta.kapW (D.hc ρ) (pW i ρ) (qW i ρ))

def WeightIs (R : RealDat D A Ks) : Prop :=
  ∀ (i : Fin D.R.m) (τ : D.what₂.Tau),
    Formalism.QuantumDeterminants.lowK ((R.MW i (sg0 D A)).ε τ) ((R.MW i (sg0 D A)).lam τ) = blockWeight₂ i τ

end Base

def BaseWeight : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    BaseHol A ∧ (R.models_order → WeightIs R)

def LowType : Prop := ModelLow ∧ BaseWeight

end GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def sgn (e : Bool) : ℂ := if e then 1 else -1

def idx {n : ℕ} (ε : Fin n → Bool) : ℚ := ∑ a, if ε a then (1 : ℚ) else -1

def wtS {b : ℕ} (ε' : Fin b → Bool) (aT : ℚ) (e : Bool) : ℚ := (if e then -(idx ε' / 2) else idx ε' / 2) - aT

def wtT {a : ℕ} (ε : Fin a → Bool) (aS : ℚ) (e : Bool) : ℚ := (if e then idx ε / 2 else -(idx ε / 2)) + aS

def signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (g.submatrix (Subtype.val : {a // ε a = e} → Fin n) (Subtype.val : {a // ε a = e} → Fin n)).det

def elt {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ)

section Fock

variable {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def raiO (i : Fin b) (j : Fin a) : Module.End ℂ (PolF D b a) := by
  classical
  exact sgn (ε j) • (if ε' i = ε j then LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j))
    else -(MvPolynomial.pderiv (τ, i, j)).toLinearMap)

def lowO (i : Fin b) (j : Fin a) : Module.End ℂ (PolF D b a) := by
  classical
  exact sgn (ε j) • (if ε' i = ε j then (MvPolynomial.pderiv (τ, i, j)).toLinearMap
    else LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j)))

def fockS (X : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (PolF D b a) :=
  ∑ j, ∑ k, X j k • ∑ i, (raiO τ ε ε' i j * lowO τ ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0)

def fockT (Y : Matrix (Fin b) (Fin b) ℂ) : Module.End ℂ (PolF D b a) :=
  ∑ i, ∑ l, Y i l • ∑ j, (raiO τ ε ε' i j * lowO τ ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0)

def subst (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) : PolF D b a →ₐ[ℂ] PolF D b a := by
  classical
  exact MvPolynomial.aeval fun v : FVar D b a =>
    if v.1 = τ then
      ∑ l, ∑ m, (if ε' v.2.1 = ε v.2.2 then k l v.2.1 * g m v.2.2 else star (k l v.2.1 * g m v.2.2)) •
        MvPolynomial.X (τ, l, m)
    else MvPolynomial.X v

end Fock

section Clauses

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
  (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
  (τ : D.what₂.Tau) (aS aT : ℚ)

def TorusVac : Prop :=
  ∀ (t : Fin V.rank → ℝ) (t' : Fin W.rank → ℝ),
    ω (elt θ M τ (diagonal fun j => Complex.exp (Complex.I * t j)),
        elt θ M' τ (diagonal fun i => Complex.exp (Complex.I * t' i))) f =
      Complex.exp (Complex.I * (∑ j, (wtS (M'.ε τ) aT (M.ε τ j) : ℂ) * t j +
        ∑ i, (wtT (M.ε τ) aS (M'.ε τ i) : ℂ) * t' i)) • f

def CompactFock : Prop :=
  ∃ x y : Bool → ℤ, (∀ j, (x (M.ε τ j) : ℚ) = wtS (M'.ε τ) aT (M.ε τ j)) ∧
    (∀ i, (y (M'.ε τ i) : ℚ) = wtT (M.ε τ) aS (M'.ε τ i)) ∧
    ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ P : PolF D W.rank V.rank,
      ω (elt θ M τ h, elt θ M' τ k) (ptOf ψ θ M M' f P) =
        (signBlockDeterminant (M.ε τ) true h ^ x true * signBlockDeterminant (M.ε τ) false h ^ x false *
          (signBlockDeterminant (M'.ε τ) true k ^ y true * signBlockDeterminant (M'.ε τ) false k ^ y false)) •
          ptOf ψ θ M M' f (subst τ (M.ε τ) (M'.ε τ) (h.map (starRingEnd ℂ)) k P)

def LieFock : Prop :=
  (∀ X ∈ lieAt V τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptOf ψ θ M M' f P) z)
      (ptOf ψ θ M M' f (fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P -
        ((aT : ℂ) * X.trace) • P) z) 0) ∧
  ∀ Y ∈ lieAt W τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptOf ψ θ M M' f P) z)
      (ptOf ψ θ M M' f (fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P +
        ((aS : ℂ) * Y.trace) • P) z) 0

end Clauses

def VacChar (D : D7) : Prop :=
  ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacVec ψ θ M M' f →
      TorusVac θ M M' ω f τ aS aT ∧ CompactFock ψ θ M M' ω f τ aS aT ∧ LieFock ψ θ M M' ω f τ aS aT

end GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SignatureAndNodeGaps
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignatureAndNodeGaps

def NodeGapGe (D : D7) (h₀ : ℝ) : Prop :=
  ∀ (τ : D.what₂.Tau) (i : ℕ) (h : i + 1 < D.R.m),
    h₀ ≤ (((D.hc τ).b ⟨i + 1, h⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ)

def SizeRows (D : D7) (h₀ : ℝ) : Prop :=
  NodeGapGe D h₀ ∧
  2 * ((D.R.r + D.R.m * D.R.t : ℕ) : ℝ) ^ 3 + (D.R.t : ℝ) + 3 ≤ h₀ ∧
  1800 < D.R.r + D.R.m * D.R.t

def ChainParOfSizes : Prop :=
  ∀ (D : D7) (h₀ : ℝ), SizeRows D h₀ → ∀ k : Fin D.R.m, GlobalTheory.Chain.ChainPar D k

def SignatureAndGaps : Prop :=
  ∀ (D : D7) (h₀ : ℝ), SizeRows D h₀ → ∀ j : ℕ, j ≤ D.R.m → ∀ τ : D.what₂.Tau,
    ((parA (Ptw D) j τ).filter fun x => x.2 = false).card = (D.R.m - j) / 2 ∧
    ((parA (Ptw D) j τ).filter fun x => x.2 = true).card + (D.R.m - j) / 2 = D.R.r + j * D.R.t ∧
    ∀ x ∈ parA (Ptw D) j τ, ∀ y ∈ parA (Ptw D) j τ, x.2 ≠ y.2 → h₀ ≤ |((x.1 - y.1 : ℚ) : ℝ)|

example (D : D7) (h₀ : ℝ) (h : SizeRows D h₀) (τ : D.what₂.Tau) :
    2 * (1800 : ℝ) ^ 3 <
      (((D.hc τ).b ⟨0 + 1, D.R.two_le_m⟩ - (D.hc τ).b ⟨0, by have := D.R.two_le_m; omega⟩ : ℚ) : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h4 := h1 τ 0 D.R.two_le_m
  have h5 : (1800 : ℝ) < ((D.R.r + D.R.m * D.R.t : ℕ) : ℝ) := by exact_mod_cast h3
  have h6 : (1800 : ℝ) ^ 3 < ((D.R.r + D.R.m * D.R.t : ℕ) : ℝ) ^ 3 :=
    pow_lt_pow_left₀ h5 (by norm_num) (by norm_num)
  have h7 : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

end GlobalTheory.IndefiniteRowSideFullHecke.SignatureAndNodeGaps

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitaryAtAllRows
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces

def IsUnitaryRep {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ G H) : Prop :=
  ∀ (g : G) (x y : H), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

def pairAt (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

def csumAt (f f' : S.Cl → S.V) : ℂ := ∑ c, ((S.wt c : ℂ))⁻¹ * pairAt S σ (f c) (f' c)

def IsUnitaryAtAll {G : Type} [Group G] (r : Representation K G S.Forms) : Prop :=
  ∀ (σ : K →+* ℂ) (g : G) (f f' : S.Forms),
    csumAt S σ (r g f : S.Cl → S.V) (r g f' : S.Cl → S.V) = csumAt S σ (f : S.Cl → S.V) (f' : S.Cl → S.V)

theorem pairAt_smul (a b : K) (x y : S.V) :
    pairAt S σ (a • x) (b • y) = starRingEnd ℂ (σ a) * σ b * pairAt S σ x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem csumAt_smul (a b : K) (f f' : S.Cl → S.V) :
    csumAt S σ (a • f) (b • f') = starRingEnd ℂ (σ a) * σ b * csumAt S σ f f' := by
  simp only [csumAt, Pi.smul_apply, pairAt_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => by ring

theorem pairAt_eq (h : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) : pairAt S σ x y = σ (S.pair x y) := by
  conv_rhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  simp only [pairAt, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul,
    CSD.gramV, Matrix.of_apply, RingHom.id_apply, starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h, starRingEnd_apply]
  ring

end ClassSum

section Statement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowsUnitary (R : RealDat D A Ks) : Prop := IsUnitaryRep R.gE

def LiftsUnitary (R : RealDat D A Ks) : Prop := ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsUnitaryRep (R.gW i σ)

variable (A) in

def DefiniteUnitary : Prop :=
  (∀ t : T, IsUnitaryAtAll (A.MtildeCSD t) (A.leftGroupActionRight t)) ∧
    ∀ (i : Fin D.R.m) (t : T), IsUnitaryAtAll (A.MtCSD i t) (A.leftGroupActionLift i t)

def GroupUnitary (R : RealDat D A Ks) : Prop := RowsUnitary R ∧ LiftsUnitary R ∧ DefiniteUnitary A

end Statement

def FiniteGroupActsUnitarily : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → GroupUnitary R

example : ¬ IsUnitaryRep (G := ℂˣ) (H := ℂ) (Representation.ofDistribMulAction ℂ ℂˣ ℂ) := by
  intro h
  have := h (Units.mk0 2 two_ne_zero) 1 1
  simp [Units.smul_def] at this
  norm_num [map_ofNat] at this

example {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ G H)
    (h : IsUnitaryRep ρ) (g : G) (x : H) : ‖ρ g x‖ = ‖x‖ := by
  have := h g x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
  have h2 : ‖ρ g x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast this
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces
end
end

