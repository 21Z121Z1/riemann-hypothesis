import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.DualBasesOfSeries
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DualBasesOfSeries

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta
open Classical

def IntJets {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α : σ →₀ ℕ, ‖(α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F‖ ≤ 1

abbrev Var (D : D7) (N N' : ℕ) : Type := (Bool × HH D) × Fin N × Fin N'

def beForm (D : D7) {p : ℕ} [Fact p.Prime] (N N' : ℕ) (u' : HH D → ℂ_[p]) : MvPowerSeries (Var D N N') ℂ_[p] :=
  ∑ t : HH D, MvPowerSeries.C (u' t) * ∑ a : Fin N, ∑ b : Fin N',
    (MvPowerSeries.X ((false, t), a, b) : MvPowerSeries (Var D N N') ℂ_[p]) * MvPowerSeries.X ((true, t), a, b)

def HasShape (D : D7) {p : ℕ} [Fact p.Prime] {N N' : ℕ} (S : ℂ_[p]) (u' : HH D → ℂ_[p])
    (Θ : MvPowerSeries (Var D N N') ℂ_[p]) : Prop :=
  ∃ sg : MvPowerSeries (Var D N N') ℂ_[p], IntJets sg ∧
    Θ = expMv (-(MvPowerSeries.C S * beForm D N N' u')) * sg

abbrev Amb (D : D7) (p : ℕ) [Fact p.Prime] : Type := D.what₂.Tau → ℂ_[p] × ℂ_[p]

def embA (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.E) : Amb D p :=
  fun τ => (tauEmb D lam τ a, tauEmb D lam τ (D.host.conj a))

def conjA {D : D7} {p : ℕ} [Fact p.Prime] (x : Amb D p) : Amb D p := fun τ => (x τ).swap

def intA (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : Set (Amb D p) :=
  closure (Set.range fun a : 𝓞 D.host.E => embA D lam (a : D.host.E))

def latA (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Set (Fin N → Amb D p) :=
  closure ((fun (y : Fin N → D.host.E) (i : Fin N) => embA D lam (y i)) '' (L : Set (Fin N → D.host.E)))

def DualBases (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : Matrix (Fin N) (Fin N) (Amb D p)) : Prop :=
  (∀ a, (fun i => P i a) ∈ latA D lam L) ∧
  (∀ x ∈ latA D lam L, ∃ c : Fin N → Amb D p, (∀ a, c a ∈ intA D lam) ∧ x = fun i => ∑ a, c a * P i a) ∧
  ∀ a a', ∑ i, P i a * conjA (P i a') = if a = a' then 1 else 0

def atTau {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} (P : Matrix (Fin N) (Fin N) (Amb D p)) (τ : D.what₂.Tau) :
    Matrix (Fin N) (Fin N) ℂ_[p] :=
  P.map fun x => (x τ).1

def ellP (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    Submodule (PadicComplexInt p) ℂ_[p] :=
  (Submodule.span (PadicComplexInt p) {v : D.what₂.Tau → ℂ_[p] |
      ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), v = fun ρ => tauEmb D lam ρ a}).comap
    (LinearMap.single (PadicComplexInt p) (fun _ : D.what₂.Tau => ℂ_[p]) τ)

def IsGen (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : D.what₂.Tau → ℂ_[p]) : Prop :=
  ∀ τ, ellP D lam τ = Submodule.span (PadicComplexInt p) {g τ}

def chgD (D : D7) {p : ℕ} [Fact p.Prime] {N N' : ℕ} (g : D.what₂.Tau → ℂ_[p])
    (P : HH D → Matrix (Fin N) (Fin N) (Amb D p)) (P' : HH D → Matrix (Fin N') (Fin N') (Amb D p))
    (k : D.what₂.Tau × Fin N' × Fin N) (x : Var D N N') : ℂ_[p] :=
  if tauPl D x.1 = k.1 then
    g k.1 * atTau (P' x.1.2) k.1 k.2.1 x.2.2 * (atTau (P x.1.2) k.1)⁻¹ x.2.1 k.2.2
  else 0

def CurveTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop := IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ

def KerTie (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (idl : D.Dt ⧸ D.UO → IdE D)
    (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  ∀ u μ, ∀ i < D.R.m, liftTie D (tor0 D cc δ) (B.eNat (chiRec D idl)) (O u μ) i

def LevTie (D : D7) (Dx : DivX D) (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  ∀ u μ, ∀ q ∈ (O u μ).S,
    q = (D.mem u).A.T ∨ q ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) ∨ q ∈ Dx.Qp μ

def GenTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)
    (gen : ∀ w : D.what₂.places.Pl, D.what₂.Tau → ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ w, D.what₂.places.resChar w = D.host.d → IsGen D (E.lam w) (gen w)

def SeriesTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ))
    (gen : ∀ w : D.what₂.places.Pl, D.what₂.Tau → ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ u μ w, D.what₂.places.resChar w = D.host.d → LevFree Dx u μ w → ∀ i < D.R.m,
    ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ (P : HH D → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (Amb D (D.what₂.places.resChar w)))
      (P' : HH D → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) (Amb D (D.what₂.places.resChar w))),
      (∀ t, DualBases D (E.lam w) ((O u μ).lat i c).1 (P t)) ∧
      (∀ t, DualBases D (E.lam w) ((O u μ).lat (i + 1) c').1 (P' t)) ∧
      E.Th u μ w i c c' = linAt (chgD D (gen w) P P') (pSer D (E.lam w) ((O u μ).Th i c c'))

def ShapeD {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = D.host.d →
    ∃ (S : ℂ_[D.what₂.places.resChar w]) (u' : HH D → ℂ_[D.what₂.places.resChar w]),
      ‖S‖ ^ 2 ≤ (D.host.d : ℝ) ∧ (∀ t, ‖u' t‖ ≤ 1) ∧
      ∀ u μ, LevFree Dx u μ w → ∀ i < D.R.m,
        ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), HasShape D S u' (E.Th u μ w i c c')

def ShapeD_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (idl : D.Dt ⧸ D.UO → IdE D)
    (O : ∀ u μ, LiftObj D (D.chTw u μ))
    (gen : ∀ w : D.what₂.places.Pl, D.what₂.Tau → ℂ_[D.what₂.places.resChar w]) : Prop :=
  CurveTie D cc δ → RelDetPinned D idl → KerTie D B idl O → LevTie D Dx O → GenTie E gen → SeriesTie E O gen →
    ShapeD E

end GlobalTheory.IndefiniteRowSideFullHecke.DualBasesOfSeries
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.IntegralJetEntries
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries

def JetsIntegral {σ : Type} {l : ℕ} [Fact l.Prime] (F : MvPowerSeries σ ℂ_[l]) : Prop :=
  ∀ a : σ →₀ ℕ, ‖(a.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff a F‖ ≤ 1

def EntriesIntegral {Lt : Type} [DecidableEq Lt] (N₀ N₁ : ℕ) {l : ℕ} [Fact l.Prime]
    (F : MvPowerSeries (Lt × Fin N₀ × Fin N₁) ℂ_[l]) : Prop :=
  ∀ (P : MvPolynomial (KM.XZ Lt N₀ N₁) ℤ) (m : (Lt × ℕ × Fin N₀) →₀ ℕ),
    ‖MvPolynomial.coeff m (KM.applyAt0 N₀ N₁ l F P)‖ ≤ 1

def CurveTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ

def levPr {D : D7} (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Finset ℕ :=
  insert (D.mem u).A.T (({D.host.g 0, D.host.g 1} : Finset ℕ) ∪ Dx.Qp μ)

def LevTie {D : D7} (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  O.S = levPr Dx u μ

def perId (D : D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E)
    {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t}

def IsDataPlaces (D : D7) (cc : Ideal (𝓞 D.host.K)) (S : Finset ℕ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  letI := D.host.cmStar
  ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧
    ∃ q ∈ S, q.Prime ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ Nat.Coprime (Ideal.absNorm cc) q

def IsDatum (D : D7) (S : Finset ℕ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Φ : Formalism.L2.Col.HomE D.host.E N N' → ℂ) : Prop :=
  (∀ x y, y - x ∈ Formalism.L2.Col.mulLat c (Formalism.L2.Col.homAt SS L L') → Φ y = Φ x) ∧
  (∀ x, Φ x ≠ 0 → x ∈ Formalism.L2.Col.divLat c (Formalism.L2.Col.homAt SS L L')) ∧
  ∀ x, Φ x ∈ TaylorLogMetric.Qbar ∧
    ∀ (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]), p ∉ S → ‖TaylorLogMetric.lamC lam (Φ x)‖ ≤ 1

def xiKer (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : TaylorLogMetric.FamE D) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Φ : Formalism.L2.Col.HomE D.host.E N N' → ℂ) : TaylorLogMetric.VC D N N' → ℂ :=
  letI := D.host.cmStar
  Formalism.L2.Ker.thC (TaylorLogMetric.embT D) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (perId D cc) SS L L' c Φ (e N N' L L')

def XiTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : TaylorLogMetric.FamE D) {u : D.what₂.Word}
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (i : ℕ) : Prop :=
  ∃ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), IsDataPlaces D cc O.S SS ∧ 0 < c ∧
    ∀ (k : C.cls i) (k' : C.cls (i + 1)), ∃ Φ : Formalism.L2.Col.HomE D.host.E (D.R.N i) (D.R.N (i + 1)) → ℂ,
      IsDatum D O.S SS c (O.lat i k).1 (O.lat (i + 1) k').1 Φ ∧
      O.Th i k k' = xiKer D cc δ e SS c (O.lat i k).1 (O.lat (i + 1) k').1 Φ

def UnfTie (D : D7) {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (i : ℕ) : Prop :=
  ∀ k k' (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) (y' : C.Y (i + 1)),
    C.unf i k k' (fun y => GL3Theta.evFr D Q (O.frm i y)) y' =
      GL3Theta.applyAt0 D (GL3Theta.polD D O.dgen Q (O.frm (i + 1) y')) (O.Th i k k')

def IsRBasis (D : D7) {l : ℕ} [Fact l.Prime] (ρ : D.host.E → ℂ_[l]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (g : Matrix (Fin N) (Fin N) ℂ_[l]) : Prop :=
  g.det ≠ 0 ∧
    Submodule.span 𝓞_ℂ_[l] (Set.range fun a : Fin N => fun k => g k a) =
      Submodule.span 𝓞_ℂ_[l] ((fun (x : Fin N → D.host.E) k => ρ (x k)) '' (L : Set (Fin N → D.host.E)))

open Classical in

def coordCh (D : D7) {l : ℕ} [Fact l.Prime] {N N' : ℕ} (s : D.what₂.Tau → ℂ_[l])
    (g : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[l]) (g' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[l])
    (k : D.what₂.Tau × Fin N' × Fin N) (x : (Bool × HH D) × Fin N × Fin N') : ℂ_[l] :=
  if tauPl D x.1 = k.1 then s k.1 * g' k.1 k.2.1 x.2.2 * ((g k.1)⁻¹) x.2.1 k.2.2 else 0

def SerTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (i : ℕ)
    (k : (D.chTw u μ).cls i) (k' : (D.chTw u μ).cls (i + 1)) : Prop :=
  ∃ (c₀ : D.what₂.Tau → ℂ_[D.what₂.places.resChar w])
    (g : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ_[D.what₂.places.resChar w])
    (g' : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w]),
    (∀ τ, ‖c₀ τ‖ = 1) ∧
    (∀ τ, IsRBasis D (TaylorLogMetric.tauEmb D (E.lam w) τ) (O.lat i k).1 (g τ)) ∧
    (∀ τ, IsRBasis D (TaylorLogMetric.tauEmb D (E.lam w) τ) (O.lat (i + 1) k').1 (g' τ)) ∧
    E.Th u μ w i k k' =
      linAt (coordCh D (fun τ => c₀ τ * TaylorLogMetric.lamC (E.lam w) (O.dgen τ)) g g') (TaylorLogMetric.pSer D (E.lam w) (O.Th i k k'))

def Concl {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (i : ℕ) (k : (D.chTw u μ).cls i) (k' : (D.chTw u μ).cls (i + 1)) : Prop :=
  JetsIntegral (E.Th u μ w i k k') ∧
  EntriesIntegral (D.R.N i) (D.R.N (i + 1)) (E.Th u μ w i k k') ∧
  ∀ (I : KM.ColChoice (D.R.N (i + 1)) (nuD D u i)) (m : ((Bool × HH D) × ℕ × Fin (D.R.N i)) →₀ ℕ),
    ‖MvPolynomial.coeff m (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (E.Th u μ w i k k')
      (KM.Gxz (D.R.N i) (D.R.N (i + 1)) (nuD D u i) I))‖ ≤ 1

def JetInt_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  GL3Theta.InducedCMType D → GL3Theta.HostFieldConditions D → CurveTie D cc δ → TaylorLogMetric.IsChi D χ →
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)), LevTie Dx u μ O →
  ∀ i, i < D.R.m → XiTie D cc δ (B.eNat χ) O i → UnfTie D O i →
  ∀ w : D.what₂.places.Pl, LevFree Dx u μ w → D.what₂.places.resChar w ≠ D.host.d →
  ∀ k k', SerTie E u μ O w i k k' → Concl E u μ w i k k'

def JetIntKer_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  GL3Theta.InducedCMType D → GL3Theta.HostFieldConditions D → CurveTie D cc δ → TaylorLogMetric.IsChi D χ →
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)), LevTie Dx u μ O →
  ∀ i, i < D.R.m → GL3Theta.liftTie D (TaylorLogMetric.tor0 D cc δ) (B.eNat χ) O i →
  ∀ w : D.what₂.places.Pl, LevFree Dx u μ w → D.what₂.places.resChar w ≠ D.host.d →
  ∀ k k', SerTie E u μ O w i k k' → Concl E u μ w i k k'

def Translates_at (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  GL3Theta.InducedCMType D → GL3Theta.HostFieldConditions D → CurveTie D cc δ → TaylorLogMetric.IsChi D χ →
  ∀ (S : Finset ℕ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Φ : Formalism.L2.Col.HomE D.host.E N N' → ℂ), TaylorLogMetric.admitted D N N' L L' → IsDataPlaces D cc S SS → 0 < c →
    IsDatum D S SS c L L' Φ →
    GL3Theta.IsKer D (TaylorLogMetric.tor0 D cc δ) (B.eNat χ) S L L' (xiKer D cc δ (B.eNat χ) SS c L L' Φ)

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.IntegralJetsPairing
section
open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetsPairing

def HasIntJets {σ : Type} {p : ℕ} [Fact p.Prime] (f : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α : σ →₀ ℕ, ‖(α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α f‖ ≤ 1

def pairForm (D : D7) {p : ℕ} [Fact p.Prime] (N N' : ℕ) (u' : HH D → ℂ_[p]) :
    MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p] :=
  ∑ t : HH D, MvPowerSeries.C (u' t) *
    ∑ a : Fin N, ∑ b : Fin N', MvPowerSeries.X (((false, t), a, b) : (Bool × HH D) × Fin N × Fin N') *
      MvPowerSeries.X (((true, t), a, b) : (Bool × HH D) × Fin N × Fin N')

def CurveTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ TaylorLogMetric.IsChi D χ

def LevelTie {D : D7} (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ q ∈ O.S, q = (D.mem u).A.T ∨ q ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) ∨ q ∈ Dx.Qp μ

def DualBases (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : Bool × HH D → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  (∀ s, TaylorLogMetric.LocBasisW D (TaylorLogMetric.tauEmb D lam (tauPl D s)) L (P s)) ∧
  ∀ (t : HH D) (a a' : Fin N),
    ∑ k, P (false, t) k a * D.host.conj (P (true, t) k a') = if a = a' then 1 else 0

def IsLineGen (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (c : D.what₂.Tau → ℂ)
    (g : Bool × HH D → ℂ_[p]) : Prop :=
  ∀ s, ∃ ε : ℂ_[p], ‖ε‖ = 1 ∧ g s = ε * TaylorLogMetric.lamC lam (c (tauPl D s))

open Classical in

def chgCoef (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N N' : ℕ} (g : Bool × HH D → ℂ_[p])
    (P : Bool × HH D → Matrix (Fin N) (Fin N) D.host.E) (P' : Bool × HH D → Matrix (Fin N') (Fin N') D.host.E)
    (k : D.what₂.Tau × Fin N' × Fin N) (x : (Bool × HH D) × Fin N × Fin N') : ℂ_[p] :=
  if tauPl D x.1 = k.1 then
    g x.1 * TaylorLogMetric.tauEmb D lam (tauPl D x.1) (P' x.1 k.2.1 x.2.2) *
      TaylorLogMetric.tauEmb D lam (tauPl D x.1) ((P x.1)⁻¹ x.2.1 k.2.2)
  else 0

def SeriesTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∃ g : Bool × HH D → ℂ_[D.what₂.places.resChar w], IsLineGen D (E.lam w) O.dgen g ∧
    ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
      ∃ (P : Bool × HH D → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
        (P' : Bool × HH D → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E),
        DualBases D (E.lam w) (O.lat i c).1 P ∧ DualBases D (E.lam w) (O.lat (i + 1) c').1 P' ∧
        E.Th u μ w i c c' = linAt (chgCoef D (E.lam w) g P P') (TaylorLogMetric.pSer D (E.lam w) (O.Th i c c'))

def Shape {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∃ S : ℂ_[D.what₂.places.resChar w], ‖S‖ ≤ Real.sqrt (D.what₂.places.resChar w : ℝ) ∧
    ∃ u' : HH D → ℂ_[D.what₂.places.resChar w], (∀ t, ‖u' t‖ ≤ 1) ∧
      ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
        ∃ sg' : MvPowerSeries ((Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w],
          HasIntJets sg' ∧
          E.Th u μ w i c c' =
            TaylorLogMetric.expMv (-(MvPowerSeries.C S * pairForm D (D.R.N i) (D.R.N (i + 1)) u')) * sg'

def shapeD_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  GL3Theta.InducedCMType D → GL3Theta.HostFieldConditions D → CurveTie D cc δ χ →
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)), LevelTie Dx u μ O →
    ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = D.host.d → LevFree Dx u μ w →
      ∀ i, i < D.R.m → GL3Theta.liftTie D (TaylorLogMetric.tor0 D cc δ) (B.eNat χ) O i → SeriesTie E u μ O w i →
        Shape E u μ w i

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetsPairing
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.PolynomialIntegralityJets
section
open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets

open Formalism.BasicNotions Formalism.MainNotions

def jetAt {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) : ℂ_[p] :=
  (α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F

def JetsIntegral {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α, ‖jetAt F α‖ ≤ 1

def PolyIntegral {σ : Type*} {p : ℕ} [Fact p.Prime] (Q : MvPolynomial σ ℂ_[p]) : Prop :=
  ∀ β, ‖MvPolynomial.coeff β Q‖ ≤ 1

def FamTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ TaylorLogMetric.IsChi D χ

def LevelTie {D : D7} (Dx : DivX D) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  O.S = insert (D.mem u).A.T (({D.host.g 0, D.host.g 1} : Finset ℕ) ∪ Dx.Qp μ)

def KerTie {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    {u : D.what₂.Word} {μ : D.what₂.Tup} (O : GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ i, i < D.R.m → GL3Theta.liftTie D (TaylorLogMetric.tor0 D cc δ) (B.eNat χ) O i

def coordChange (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N N' : ℕ} (g : D.what₂.Tau → ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (k : D.what₂.Tau × Fin N' × Fin N) (x : (Bool × G.HH D) × Fin N × Fin N') : ℂ_[p] :=
  open Classical in
  if tauPl D x.1 = k.1 then
    g k.1 * ((P' k.1).map (TaylorLogMetric.tauEmb D lam k.1)) k.2.1 x.2.2 * (((P k.1).map (TaylorLogMetric.tauEmb D lam k.1))⁻¹) x.2.1 k.2.2
  else 0

def SerTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) : Prop :=
  ∃ P : ∀ j : ℕ, (D.chTw u μ).cls j → D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E,
    (∀ j, j ≤ D.R.m → ∀ c τ, TaylorLogMetric.LocBasisW D (TaylorLogMetric.tauEmb D (E.lam w) τ) (O.lat j c).1 (P j c τ)) ∧
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
      ∃ c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w], (∀ τ, ‖c0 τ‖ = 1) ∧
        E.Th u μ w i c c' =
          linAt (coordChange D (E.lam w) (fun τ => c0 τ * TaylorLogMetric.lamC (E.lam w) (O.dgen τ)) (P i c) (P (i + 1) c'))
            (TaylorLogMetric.pSer D (E.lam w) (O.Th i c c'))

def EntInt {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) : Prop :=
  ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    JetsIntegral (E.Th u μ w i c c') ∧
    (∀ P : MvPolynomial (KM.XZ (Bool × G.HH D) (D.R.N i) (D.R.N (i + 1))) ℤ,
      PolyIntegral (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (E.Th u μ w i c c') P)) ∧
    ∀ I : KM.ColChoice (D.R.N (i + 1)) (nuD D u i),
      PolyIntegral (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (E.Th u μ w i c c')
        (KM.Gxz (D.R.N i) (D.R.N (i + 1)) (nuD D u i) I))

def JetInt_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  FamTie D cc δ χ →
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), LevelTie Dx (O u μ) → KerTie B χ (O u μ) →
    ∀ w : D.what₂.places.Pl, LevFree Dx u μ w → D.what₂.places.resChar w ≠ D.host.d → SerTie E (O u μ) w →
      EntInt E u μ w

def CoefAlg_at (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  FamTie D cc δ χ → ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), KerTie B χ (O u μ) →
    ∀ i, i < D.R.m → ∀ c c' α, TaylorLogMetric.taylor D ((O u μ).Th i c c') α ∈ TaylorLogMetric.Qbar

theorem not_mem_S {D : D7} {Dx : DivX D} {u : D.what₂.Word} {μ : D.what₂.Tup} {O : GL3Theta.LiftObj D (D.chTw u μ)}
    (h : LevelTie Dx O) (w : D.what₂.places.Pl) : LevFree Dx u μ w ↔ D.what₂.places.resChar w ∉ O.S := by
  rw [h, LevFree]
  simp only [Finset.mem_insert, Finset.mem_union]
  tauto

theorem polyIntegral_applyAt0 {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime]
    (F : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (h : JetsIntegral F) (P : MvPolynomial (KM.XZ Lt N0 N1) ℤ) :
    PolyIntegral (KM.applyAt0 N0 N1 l F P) := by
  classical
  intro β
  unfold KM.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc, norm_mul]
    exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ _) (norm_nonneg _) (h _)
  · simp

example (p : ℕ) [hp : Fact p.Prime] :
    ¬ JetsIntegral (MvPowerSeries.monomial (Finsupp.single () 1) ((p : ℂ_[p])⁻¹) : MvPowerSeries Unit ℂ_[p]) := by
  intro h
  have h1 := h (Finsupp.single () 1)
  have h2 : ‖(p : ℂ_[p])‖ < 1 := by
    have : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h3 : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [jetAt, MvPowerSeries.coeff_monomial_same] at h1
  rw [Finsupp.prod_single_index (by simp)] at h1
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, norm_inv] at h1
  have h4 := norm_pos_iff.2 h3
  rw [inv_le_one₀ h4] at h1
  linarith

end GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets
end
end

