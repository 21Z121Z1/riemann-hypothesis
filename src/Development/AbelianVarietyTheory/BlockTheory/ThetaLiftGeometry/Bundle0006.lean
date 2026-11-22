import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ShapeDegreeParity
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ShapeDegreeParity

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Classical

section Local

variable (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d]

def laSer (s : ZMod d) : MvPowerSeries (ZMod d) ℂ_[l] :=
  fun α => ∑ e ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if α = Finsupp.single (s - 2 * (e : ZMod d)) ((l ^ 2) ^ e) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

variable {d}

def laAt {σ : Type} (t : ZMod d → MvPowerSeries σ ℂ_[l]) (s : ZMod d) : MvPowerSeries σ ℂ_[l] :=
  MvPowerSeries.subst t (laSer l d s)

def degPar (ε : ℕ) (α : ZMod d →₀ ℕ) : ℕ := ∑ s : ZMod d, if s.val % 2 = ε then α s else 0

variable {l}

def CoefB (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop := CoefWf be

def InvB (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 →
    MvPowerSeries.rescale (fun s : ZMod d => if s.val % 2 = 0 then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) be = be

def DegB (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ α : ZMod d →₀ ℕ, (degPar 0 α = 0 ∨ degPar 1 α = 0 ∨ (degPar 0 α = 1 ∧ degPar 1 α = 1)) →
    MvPowerSeries.coeff α be = 0

def AddB (be : MvPowerSeries (ZMod d) ℂ_[l]) (ε : ℕ) : Prop :=
  let z : ZMod d → MvPowerSeries (ZMod d ⊕ ZMod d) ℂ_[l] := laAt l fun s => MvPowerSeries.X (Sum.inl s)
  let z'' : ZMod d → MvPowerSeries (ZMod d ⊕ ZMod d) ℂ_[l] := laAt l fun s => MvPowerSeries.X (Sum.inr s)
  SimeqW (MvPowerSeries.subst (fun s : ZMod d => if s.val % 2 = ε then z s + z'' s else z s) be)
    (MvPowerSeries.subst z be + MvPowerSeries.subst (fun s : ZMod d => if s.val % 2 = ε then z'' s else z s) be)

def IsBeta (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  CoefB be ∧ InvB be ∧ DegB be ∧ AddB be 0 ∧ AddB be 1

end Local

abbrev Lt (D : D7) : Type := Bool × HH D

abbrev Var (D : D7) (N N' : ℕ) : Type := Lt D × Fin N × Fin N'

def CaseA (D : D7) (l : ℕ) : Prop := 5 ≤ l ∧ InertK D l ∧ (IsResidueClassZero D l → Formalism.MainNotions.G.HEv D l)

def IsOrbReps (D : D7) (l : ℕ) (T : Finset (Lt D)) : Prop := ∀ z, ∃! r, r ∈ T ∧ ∃ e : ℕ, posPl D l r e = z

section Coord

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def rhoZ (z : Lt D) : D.host.E → ℂ_[l] := tauEmb D lam (tauPl D z)

def Oprime : Set ℂ_[l] := closure (Set.range fun a : 𝓞 D.host.K => tauK D lam (a : D.host.K))

def Ow (r : Lt D) (ε : ℕ) : Set (ZMod (nP D l) → ℂ_[l]) :=
  closure (Set.range fun a : 𝓞 D.host.E => fun s : ZMod (nP D l) =>
    if s.val % 2 = ε then rhoZ D lam (posPl D l r s.val) (a : D.host.E) else 0)

def IsOwBasis (r : Lt D) (M : Matrix (ZMod (nP D l)) (ZMod (nP D l)) ℂ_[l]) : Prop :=
  (∀ j, (fun s => M s j) ∈ Ow D lam r (j.val % 2)) ∧
  ∀ ε, ε < 2 → ∀ y ∈ Ow D lam r ε, ∃ c : ZMod (nP D l) → ℂ_[l],
    (∀ j, c j ∈ Oprime D lam) ∧ (∀ j, j.val % 2 ≠ ε → c j = 0) ∧ y = M.mulVec c

def CoordT (r : Lt D) : Prop :=
  (∃ M, IsOwBasis D lam r M) ∧
  ∀ M, IsOwBasis D lam r M → ‖M.det‖ = 1 ∧
    ∃ t : ZMod (nP D l) → MvPowerSeries (ZMod (nP D l)) ℂ_[l],
      (∀ s, IntegralW (t s) ∧ MvPowerSeries.constantCoeff (t s) = 0 ∧
        ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) (t s) = M s j) ∧
      ∀ s, laAt l t s = ∑ j, MvPowerSeries.C (M s j) *
        PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (ZMod (nP D l)) ℂ_[l]) (logF l)

def IsBases {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (P : Lt D → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  ∀ z, LocBasisW D (rhoZ D lam z) L (P z) ∧ ((P (posPl D l z 1)).map D.host.conj).transpose * P z = 1

def readIn {N N' : ℕ} (c : Lt D → ℂ_[l]) (P : Lt D → Matrix (Fin N) (Fin N) D.host.E)
    (P' : Lt D → Matrix (Fin N') (Fin N') D.host.E) (F : MvPowerSeries (Idx D N N') ℂ_[l]) :
    MvPowerSeries (Var D N N') ℂ_[l] :=
  linAt (fun (k : Idx D N N') (x : Var D N N') =>
    if tauPl D x.1 = k.1 then
      c x.1 * ((P' x.1).map (rhoZ D lam x.1)) k.2.1 x.2.2 * (((P x.1).map (rhoZ D lam x.1))⁻¹) x.2.1 k.2.2
    else 0) F

variable (l)

def zSer {N N' : ℕ} (x : Var D N N') : MvPowerSeries (Var D N N') ℂ_[l] :=
  laAt l (fun s : ZMod (nP D l) => MvPowerSeries.X ((posPl D l x.1 s.val, x.2) : Var D N N')) 0

variable {l}

def beSum (N N' : ℕ) (r : Lt D) (be : MvPowerSeries (ZMod (nP D l)) ℂ_[l]) : MvPowerSeries (Var D N N') ℂ_[l] :=
  ∑ a : Fin N, ∑ b : Fin N',
    MvPowerSeries.subst (fun s : ZMod (nP D l) => zSer D l ((posPl D l r s.val, a, b) : Var D N N')) be

def Shape {N N' : ℕ} (T : Finset (Lt D)) (be : Lt D → MvPowerSeries (ZMod (nP D l)) ℂ_[l]) (κ : Lt D → ℂ_[l])
    (Θ : MvPowerSeries (Var D N N') ℂ_[l]) : Prop :=
  ∃ U : MvPowerSeries (Var D N N') ℂ_[l], IntegralMv U ∧
    MvPowerSeries.subst (fun x : Var D N N' => MvPowerSeries.C (κ x.1) * zSer D l x) Θ =
      U * ∏ r ∈ T, expMv (-beSum D N N' r (be r))

end Coord

def CombShape (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), CaseA D l → Nat.Coprime (Ideal.absNorm cc) l →
    (∀ r, CoordT D lam r) ∧
    ∃ (ep : ℂ_[l]) (be : Lt D → MvPowerSeries (ZMod (nP D l)) ℂ_[l]),
      ep ∈ Wp l ∧ ‖ep‖ = 1 ∧ (∀ r, IsBeta (be r)) ∧
      ∀ T, IsOrbReps D l T →
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : Lt D → Matrix (Fin N) (Fin N) D.host.E) (P' : Lt D → Matrix (Fin N') (Fin N') D.host.E)
        (F : MvPowerSeries (Idx D N N') ℂ_[l]),
        admitted D N N' L L' → IsBases D lam L P → IsBases D lam L' P' → IsComb D (tor0 D cc δ) e lam L L' F →
        Shape D T be (fun _ => ep) (readIn D lam (fun _ => 1) P P' F)

def KerTie (D : D7) (T : Tor D) (e : FamE D) {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}
    (O : LiftObj D C) (i : ℕ) : Prop :=
  ∀ c c', IsKer D T e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')

def ThTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (O : LiftObj D (D.chTw u μ)) (i : ℕ)
    (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) : Prop :=
  ∃ (P : Lt D → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
    (P' : Lt D → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E)
    (c0 : Lt D → ℂ_[D.what₂.places.resChar w]),
    IsBases D (E.lam w) (O.lat i c).1 P ∧ IsBases D (E.lam w) (O.lat (i + 1) c').1 P' ∧
    (∀ z, ‖c0 z‖ = ‖lamC (E.lam w) (O.dgen (tauPl D z))‖) ∧
    E.Th u μ w i c c' = readIn D (E.lam w) c0 P P' (pSer D (E.lam w) (O.Th i c c'))

def KerShape (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ w : D.what₂.places.Pl, CaseA D (D.what₂.places.resChar w) →
    Nat.Coprime (Ideal.absNorm cc) (D.what₂.places.resChar w) →
    (∀ r, CoordT D (E.lam w) r) ∧
    ∃ be : Lt D → MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w],
      (∀ r, IsBeta (be r)) ∧
      ∀ T, IsOrbReps D (D.what₂.places.resChar w) T →
      ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), LevFree Dx u μ w →
      ∀ O : LiftObj D (D.chTw u μ), D.what₂.places.resChar w ∉ O.S →
      ∀ i, i < D.R.m → KerTie D (tor0 D cc δ) e O i →
      ∀ c c', ThTie E u μ w O i c c' →
        ∃ κ : Lt D → ℂ_[D.what₂.places.resChar w], (∀ z, ‖κ z‖ = 1) ∧ Shape D T be κ (E.Th u μ w i c c')

def StrA_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → vec22 D (tor0 D cc δ) e → int22 D (tor0 D cc δ) e →
    KerShape D Dx Tw E cc δ e

def StrA_nat (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) : Prop :=
  IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → KerShape D Dx Tw E cc δ (B.eNat χ)

def StrA_comb (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → int22 D (tor0 D cc δ) e → CombShape D cc δ e

end GlobalTheory.IndefiniteRowSideFullHecke.ShapeDegreeParity
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TeichmullerFactorisation
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.TeichmullerFactorisation

def laSer (l : ℕ) [Fact l.Prime] {σ : Type} (back : ℕ → σ) : MvPowerSeries σ ℂ_[l] :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (back e) (l ^ (2 * e)) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

def laZ (l d : ℕ) [Fact l.Prime] (s : ZMod d) : MvPowerSeries (ZMod d) ℂ_[l] :=
  laSer l fun e => s - 2 * (e : ZMod d)

def laZ2 (l d : ℕ) [Fact l.Prime] (s : ZMod d) (b : Bool) : MvPowerSeries (ZMod d × Bool) ℂ_[l] :=
  laSer l fun e => (s - 2 * (e : ZMod d), b)

section Beta

variable {l d : ℕ} [Fact l.Prime] [NeZero d]

def CoefProp (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop := GL3Theta.CoefWf be

def TeichInv (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 →
    MvPowerSeries.rescale (fun s : ZMod d => if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) be = be

def degEven (n : ZMod d →₀ ℕ) : ℕ := ∑ s : ZMod d, if Even s.val then n s else 0

def degOdd (n : ZMod d →₀ ℕ) : ℕ := ∑ s : ZMod d, if Even s.val then 0 else n s

def NoLowTerms (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ n : ZMod d →₀ ℕ, (degEven n = 0 ∨ degOdd n = 0 ∨ (degEven n = 1 ∧ degOdd n = 1)) → MvPowerSeries.coeff n be = 0

def BiaddAt (r : ℕ) (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  GL3Theta.SimeqW
    (MvPowerSeries.subst (fun s : ZMod d =>
      if s.val % 2 = r then laZ2 l d s false + laZ2 l d s true else laZ2 l d s false) be)
    (MvPowerSeries.subst (fun s : ZMod d => laZ2 l d s false) be +
      MvPowerSeries.subst (fun s : ZMod d => if s.val % 2 = r then laZ2 l d s true else laZ2 l d s false) be)

def BetaProps (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  CoefProp be ∧ TeichInv be ∧ NoLowTerms be ∧ BiaddAt 0 be ∧ BiaddAt 1 be

example : NoLowTerms (0 : MvPowerSeries (ZMod d) ℂ_[l]) ∧ TeichInv (0 : MvPowerSeries (ZMod d) ℂ_[l]) :=
  ⟨fun _ _ => by simp, fun _ _ => map_zero _⟩

example : ¬ NoLowTerms (MvPowerSeries.monomial (Finsupp.single (0 : ZMod 2) 1 + Finsupp.single 1 1) (1 : ℂ_[l])) := by
  intro h
  have := h (Finsupp.single (0 : ZMod 2) 1 + Finsupp.single 1 1) (Or.inr (Or.inr ⟨?_, ?_⟩))
  · simp at this
  all_goals
    have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    have hv : (1 : ZMod 2).val = 1 := rfl
    simp [degEven, degOdd, hu, Finset.sum_pair h01, hv, h01, h01.symm]

end Beta

section Local

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[l])

def embL (x : D.host.E) : D.what₂.Tau → ℂ_[l] × ℂ_[l] :=
  fun τ => (TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ x), TaylorLogMetric.lamC lam (TaylorLogMetric.embT D τ (D.host.conj x)))

def OEl : Set (D.what₂.Tau → ℂ_[l] × ℂ_[l]) := closure (Set.range fun a : 𝓞 D.host.E => embL D lam (a : D.host.E))

def latL {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Set (Fin N → D.what₂.Tau → ℂ_[l] × ℂ_[l]) :=
  closure ((fun x : Fin N → D.host.E => fun k => embL D lam (x k)) '' (L : Set (Fin N → D.host.E)))

def OrthoL {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (m : Fin N → Fin N → D.what₂.Tau → ℂ_[l] × ℂ_[l]) : Prop :=
  (∀ a, m a ∈ latL D lam L) ∧
  (∀ a a' τ, GL3Theta.hP (fun k => m a k τ) (fun k => m a' k τ) = if a = a' then 1 else 0) ∧
  ∀ y ∈ latL D lam L, ∃ c : Fin N → D.what₂.Tau → ℂ_[l] × ℂ_[l], (∀ a, c a ∈ OEl D lam) ∧
    y = fun k τ => ∑ a, c a τ * m a k τ

def letter (l : ℕ) (z : Bool × G.HH D) (s : ZMod (G.nP D l)) : Bool × G.HH D := posPl D l z s.val

def BasisO' (z : Bool × G.HH D) (r : ℕ) {k : ℕ} (om : Fin k → D.what₂.Tau → ℂ_[l] × ℂ_[l]) : Prop :=
  (∀ j, om j ∈ OEl D lam) ∧
  ∀ y ∈ OEl D lam, ∃! c : Fin k → ℂ_[l], (∀ j, c j ∈ Prod.fst '' GL3Theta.OKp D lam) ∧
    ∀ s : ZMod (G.nP D l), s.val % 2 = r →
      (y (tauPl D (letter D l z s))).1 = ∑ j, c j * (om j (tauPl D (letter D l z s))).1

def TypeCoords (z : Bool × G.HH D) (r : ℕ) : Prop :=
  ∀ (k : ℕ) (om : Fin k → D.what₂.Tau → ℂ_[l] × ℂ_[l]), BasisO' D lam z r om →
    ∃ t : ZMod (G.nP D l) → MvPowerSeries (Fin k) ℂ_[l],
      (∀ s, MvPowerSeries.constantCoeff (t s) = 0 ∧ GL3Theta.IntegralW (t s)) ∧
      (∃ J' : Matrix (Fin k) {s : ZMod (G.nP D l) // s.val % 2 = r} ℂ_[l], (∀ j s, J' j s ∈ GL3Theta.Wp l) ∧
        (Matrix.of fun (s : {s : ZMod (G.nP D l) // s.val % 2 = r}) (j : Fin k) =>
          MvPowerSeries.coeff (Finsupp.single j 1) (t s.1)) * J' = 1 ∧
        J' * (Matrix.of fun (s : {s : ZMod (G.nP D l) // s.val % 2 = r}) (j : Fin k) =>
          MvPowerSeries.coeff (Finsupp.single j 1) (t s.1)) = 1) ∧
      ∀ s : ZMod (G.nP D l), s.val % 2 = r →
        MvPowerSeries.subst t (laZ l (G.nP D l) s) =
          ∑ j, MvPowerSeries.C (om j (tauPl D (letter D l z s))).1 *
            PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin k) ℂ_[l]) (GL3Theta.logF l)

end Local

abbrev Var (D : D7) (N N' : ℕ) : Type := (Bool × G.HH D) × Fin N × Fin N'

def zOf (D : D7) (l : ℕ) [Fact l.Prime] {N N' : ℕ} (x : Var D N N') : MvPowerSeries (Var D N N') ℂ_[l] :=
  laSer l fun e => (letter D l x.1 (-(2 * (e : ZMod (G.nP D l)))), x.2)

def IsBasePts (D : D7) (l : ℕ) (T : Finset (Bool × G.HH D)) : Prop :=
  ∀ z, ∃! r, r ∈ T ∧ ∃ e : ℕ, posPl D l r e = z

def Factorises (D : D7) (l : ℕ) [Fact l.Prime] (T : Finset (Bool × G.HH D))
    (be : Bool × G.HH D → MvPowerSeries (ZMod (G.nP D l)) ℂ_[l]) {N N' : ℕ}
    (Θ : MvPowerSeries (Var D N N') ℂ_[l]) : Prop :=
  ∃ ε : Bool × G.HH D → ℂ_[l], (∀ z, ‖ε z‖ = 1) ∧
    ∃ U : MvPowerSeries (Var D N N') ℂ_[l], TaylorLogMetric.IntegralMv U ∧
      MvPowerSeries.subst (fun x : Var D N N' => MvPowerSeries.C (ε x.1) * zOf D l x) Θ =
        U * ∏ r ∈ T, TaylorLogMetric.expMv (-∑ a : Fin N, ∑ b : Fin N',
          MvPowerSeries.subst (fun s : ZMod (G.nP D l) => zOf D l ((letter D l r s, a, b) : Var D N N')) (be r))

def InertNotConj (D : D7) (l : ℕ) : Prop :=
  5 ≤ l ∧ (G.IsResidueClassZero D l ∨ G.IsSg D l) ∧ (G.IsResidueClassZero D l → G.HEv D l)

def CurveTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ TaylorLogMetric.IsChi D χ

def LevelTie {D : D7} (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ p ∈ O.S, (G.IsResidueClassZero D p ∨ G.IsSg D p) → (p = (D.mem u).A.T ∨ p = D.host.g 0 ∨ p = D.host.g 1 ∨ p ∈ Dx.Qp μ)

def SeriesTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ (m : Fin (D.R.N i) → Fin (D.R.N i) → D.what₂.Tau →
        ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w])
      (m' : Fin (D.R.N (i + 1)) → Fin (D.R.N (i + 1)) → D.what₂.Tau →
        ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w])
      (c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w]),
      OrthoL D (E.lam w) (O.lat i c).1 m ∧ OrthoL D (E.lam w) (O.lat (i + 1) c').1 m' ∧ (∀ τ, ‖c0 τ‖ = 1) ∧
      E.Th u μ w i c c' =
        linAt (fun (k : D.what₂.Tau × Fin (D.R.N (i + 1)) × Fin (D.R.N i)) (x : Var D (D.R.N i) (D.R.N (i + 1))) =>
          if tauPl D x.1 = k.1 then c0 k.1 * ((m' x.2.2 k.2.1 k.1).1 * (m x.2.1 k.2.2 k.1).2) else 0)
          (TaylorLogMetric.pSer D (E.lam w) (O.Th i c c'))

def Coords_at {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) : Prop :=
  ∀ w : D.what₂.places.Pl, InertNotConj D (D.what₂.places.resChar w) →
    Even (G.nP D (D.what₂.places.resChar w)) ∧
    ∀ z : Bool × G.HH D, TypeCoords D (E.lam w) z 0 ∧ TypeCoords D (E.lam w) z 1

def Shape_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  CurveTie D cc δ χ →
  ∀ w : D.what₂.places.Pl, InertNotConj D (D.what₂.places.resChar w) →
    Nat.Coprime (Ideal.absNorm cc) (D.what₂.places.resChar w) →
    ∃ be : Bool × G.HH D → MvPowerSeries (ZMod (G.nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w],
      (∀ z, BetaProps (be z)) ∧
      ∀ T : Finset (Bool × G.HH D), IsBasePts D (D.what₂.places.resChar w) T →
      ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)), LevFree Dx u μ w → LevelTie Dx u μ O →
      ∀ i, i < D.R.m → GL3Theta.liftTie D (TaylorLogMetric.tor0 D cc δ) (B.eNat χ) O i → SeriesTie E u μ O w i →
      ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
        Factorises D (D.what₂.places.resChar w) T be (E.Th u μ w i c c')

def InertStructure_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  Coords_at E ∧ Shape_at D Dx Tw E cc δ B χ

end GlobalTheory.IndefiniteRowSideFullHecke.TeichmullerFactorisation
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.VandermondeConjugatePrimes
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.VandermondeConjugatePrimes

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section Beta

variable {l : ℕ} [Fact l.Prime]

def zOf (l : ℕ) [Fact l.Prime] {σ : Type} (k : σ) : MvPowerSeries σ ℂ_[l] :=
  PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries σ ℂ_[l]) (logF l)

def beAt {σ : Type} (be : MvPowerSeries (Fin 2) ℂ_[l]) (a b : MvPowerSeries σ ℂ_[l]) : MvPowerSeries σ ℂ_[l] :=
  MvPowerSeries.subst ![a, b] be

def BeCoef (be : MvPowerSeries (Fin 2) ℂ_[l]) : Prop := CoefWf be

def BeInv (be : MvPowerSeries (Fin 2) ℂ_[l]) : Prop :=
  ∀ u : ℂ_[l], u ^ (l ^ 2 - 1) = 1 → MvPowerSeries.rescale ![u, (u ^ l)⁻¹] be = be

def BeVan (be : MvPowerSeries (Fin 2) ℂ_[l]) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, (n 0 = 0 ∨ n 1 = 0 ∨ (n 0 = 1 ∧ n 1 = 1)) → MvPowerSeries.coeff n be = 0

def BeBiadd (be : MvPowerSeries (Fin 2) ℂ_[l]) : Prop :=
  SimeqW (beAt be (zOf l 0 + zOf l 1) (zOf l 2) : MvPowerSeries (Fin 3) ℂ_[l])
      (beAt be (zOf l 0) (zOf l 2) + beAt be (zOf l 1) (zOf l 2)) ∧
    SimeqW (beAt be (zOf l 0) (zOf l 1 + zOf l 2) : MvPowerSeries (Fin 3) ℂ_[l])
      (beAt be (zOf l 0) (zOf l 1) + beAt be (zOf l 0) (zOf l 2))

def IsBe (be : MvPowerSeries (Fin 2) ℂ_[l]) : Prop := BeCoef be ∧ BeInv be ∧ BeVan be ∧ BeBiadd be

def expFactor (S : Type) [Fintype S] (N N' : ℕ) (be : MvPowerSeries (Fin 2) ℂ_[l]) (ep : ℂ_[l]) :
    MvPowerSeries (S × Fin N × Fin N') ℂ_[l] :=
  ∏ s : S, expMv (-(MvPowerSeries.C (2⁻¹ : ℂ_[l]) * ∑ a : Fin N, ∑ b : Fin N',
    beAt be (zOf l (s, a, b)) (MvPowerSeries.C ep * zOf l (s, a, b))))

def HasShape {S : Type} [Fintype S] {N N' : ℕ} (be : MvPowerSeries (Fin 2) ℂ_[l]) (ep : ℂ_[l])
    (Θ : MvPowerSeries (S × Fin N × Fin N') ℂ_[l]) : Prop :=
  ∃ κ : S → ℂ_[l], (∀ s, ‖κ s‖ = 1) ∧
    ∃ U : MvPowerSeries (S × Fin N × Fin N') ℂ_[l], IntegralMv U ∧
      MvPowerSeries.subst (fun x : S × Fin N × Fin N' => MvPowerSeries.C (κ x.1) * zOf l x) Θ =
        U * expFactor S N N' be ep

end Beta

def embAt (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (τ : D.what₂.Tau) {N : ℕ}
    (x : Fin N → D.host.E) : Fin N → ℂ_[l] × ℂ_[l] :=
  fun k => (lamC lam (embT D τ (x k)), lamC lam (embT D τ (D.host.conj (x k))))

def latAt (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Set (Fin N → ℂ_[l] × ℂ_[l]) :=
  closure (embAt D lam τ '' (L : Set (Fin N → D.host.E)))

def IsOrthoAt (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (b : Fin N → Fin N → ℂ_[l] × ℂ_[l]) : Prop :=
  BasisP D lam (latAt D lam τ L) b ∧ ∀ a a', hP (b a) (b a') = if a = a' then 1 else 0

def colMat {l : ℕ} [Fact l.Prime] {N : ℕ} (b : Fin N → Fin N → ℂ_[l] × ℂ_[l]) : Matrix (Fin N) (Fin N) ℂ_[l] :=
  Matrix.of fun k a => (b a k).1

open Classical in

def chgO (D : D7) {l : ℕ} [Fact l.Prime] {N N' : ℕ} (c0 : D.what₂.Tau → ℂ_[l])
    (b : D.what₂.Tau → Fin N → Fin N → ℂ_[l] × ℂ_[l]) (b' : D.what₂.Tau → Fin N' → Fin N' → ℂ_[l] × ℂ_[l])
    (k : D.what₂.Tau × Fin N' × Fin N) (x : (Bool × Formalism.MainNotions.G.HH D) × Fin N × Fin N') : ℂ_[l] :=
  if tauPl D x.1 = k.1 then c0 k.1 * colMat (b' k.1) k.2.1 x.2.2 * (colMat (b k.1))⁻¹ x.2.1 k.2.2 else 0

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

def CurveTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : IdE D → ℂ) : Prop :=
  IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ IsChi D χ

def LevelTie (Dx : DivX D) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) : Prop :=
  ∀ p ∈ O.S, p = (D.mem u).A.T ∨ p = D.host.g 0 ∨ p = D.host.g 1 ∨ p ∈ Dx.Qp μ

def KerTie {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ)
    {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) (i : ℕ) : Prop :=
  liftTie D (tor0 D cc δ) (B.eNat χ) O i

def SeriesTie (E : KerEnt D Dx Tw) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ))
    (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ (b : D.what₂.Tau → Fin (D.R.N i) → Fin (D.R.N i) →
        ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w])
      (b' : D.what₂.Tau → Fin (D.R.N (i + 1)) → Fin (D.R.N (i + 1)) →
        ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w])
      (c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w]),
      (∀ τ, IsOrthoAt D (E.lam w) τ (O.lat i c).1 (b τ)) ∧
      (∀ τ, IsOrthoAt D (E.lam w) τ (O.lat (i + 1) c').1 (b' τ)) ∧
      (∀ τ, ‖c0 τ‖ = 1) ∧
      E.Th u μ w i c c' = linAt (chgO D c0 b b') (pSer D (E.lam w) (O.Th i c c'))

def ConjPrime (D : D7) (cc : Ideal (𝓞 D.host.K)) (l : ℕ) : Prop :=
  5 ≤ l ∧ InertK D l ∧ IsFrobC D l ∧ Nat.Coprime (Ideal.absNorm cc) l

def ShapeAll (E : KerEnt D Dx Tw) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ)
    (w : D.what₂.places.Pl) (be : MvPowerSeries (Fin 2) ℂ_[D.what₂.places.resChar w])
    (ep : ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (O : LiftObj D (D.chTw u μ)), LevelTie Dx O → LevFree Dx u μ w →
    ∀ i < D.R.m, KerTie B χ O i → SeriesTie E O w i →
      ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), HasShape be ep (E.Th u μ w i c c')

def ThetaConj_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) : Prop :=
  CurveTie D cc δ χ → ∀ w : D.what₂.places.Pl, ConjPrime D cc (D.what₂.places.resChar w) →
    ∃ (be : MvPowerSeries (Fin 2) ℂ_[D.what₂.places.resChar w]) (ep : ℂ_[D.what₂.places.resChar w]),
      IsBe be ∧ ep ∈ Wp (D.what₂.places.resChar w) ∧ ‖ep‖ = 1 ∧ ShapeAll E B χ w be ep

def ThetaConjOne_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) : Prop :=
  CurveTie D cc δ χ → ∀ w : D.what₂.places.Pl, ConjPrime D cc (D.what₂.places.resChar w) →
    ∃ be : MvPowerSeries (Fin 2) ℂ_[D.what₂.places.resChar w], IsBe be ∧ ShapeAll E B χ w be 1

def Tied (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  CurveTie D cc δ χ ∧ (∀ u μ, LevelTie Dx (O u μ)) ∧ (∀ u μ, ∀ i < D.R.m, KerTie B χ (O u μ) i) ∧
    ∀ u μ w, ConjPrime D cc (D.what₂.places.resChar w) → LevFree Dx u μ w → ∀ i < D.R.m, SeriesTie E (O u μ) w i

def ThetaConjTied_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ)
    (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  Tied Dx Tw E cc δ B χ O → ∀ w : D.what₂.places.Pl, ConjPrime D cc (D.what₂.places.resChar w) →
    ∃ (be : MvPowerSeries (Fin 2) ℂ_[D.what₂.places.resChar w]) (ep : ℂ_[D.what₂.places.resChar w]),
      IsBe be ∧ ep ∈ Wp (D.what₂.places.resChar w) ∧ ‖ep‖ = 1 ∧
      ∀ u μ, LevFree Dx u μ w → ∀ i < D.R.m,
        ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), HasShape be ep (E.Th u μ w i c c')

end GlobalTheory.IndefiniteRowSideFullHecke.VandermondeConjugatePrimes
end
end

