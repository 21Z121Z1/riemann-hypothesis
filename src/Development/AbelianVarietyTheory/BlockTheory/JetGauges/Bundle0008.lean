import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.FormalDegreeBessel.StatementG
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.HermitianCurvature.StatementB

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.CanonicalHarmonicGerms
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalHarmonicGerms

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def column {n : ℕ} (m : LtN Dw n →₀ ℕ) (b : Fin n) : Lt1 Dw →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => m ⟨ℓ.1, ℓ.2, b⟩

@[simp] theorem column_apply {n : ℕ} (m : LtN Dw n →₀ ℕ) (b : Fin n) (ℓ : Lt1 Dw) :
    column m b ℓ = m ⟨ℓ.1, ℓ.2, b⟩ := rfl

section Value

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

def canGerm (C : ChartAt Xo c y) (k : ℕ) (f : Germ.PS S 1 C.d) : Germ.PS S 1 C.d :=
  f * Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0)

def colVal (C : ChartAt Xo c y) (k : ℕ) (f : Germ.PS S 1 C.d) (α : Lt1 Dw →₀ ℕ) : S :=
  MvPowerSeries.constantCoeff (Germ.DmonOf C.B.G.F C.uvec α (canGerm C k f))

def chartVal (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F)
    (f : Fin n → Germ.PS S 1 C.d) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b : Fin n, colVal C k (f b) (column m b)

example (C : ChartAt Xo c y) (k n : ℕ) (f : Fin n → Germ.PS S 1 C.d) :
    chartVal C k (0 : MvPolynomial (LtN Dw n) c.F) f = 0 := by
  simp [chartVal]

end Value

def harmType (Dw : Datum H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Set (MvPolynomial (LtN Dw n) c.F) :=
  HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)

def ChartIndep (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)
    (C₁ C₂ : ChartAt Xo c y) (k n : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
    (f₁ : Fin n → Germ.PS S 1 C₁.d) (f₂ : Fin n → Germ.PS S 1 C₂.d),
    (∀ b, IsGerm y C₁.d C₁.x C₁.B.A.act C₁.e C₁.wP k (F b) (f₁ b)) →
    (∀ b, IsGerm y C₂.d C₂.x C₂.B.A.act C₂.e C₂.wP k (F b) (f₂ b)) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmType Dw c a n →
      chartVal C₁ k P f₁ = chartVal C₂ k P f₂

end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalHarmonicGerms
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.HarmonicChartValues
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev SecAt {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) : Type :=
  LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x))

def colSum {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S)
    (P : MvPolynomial (LtN Dw n) c.F) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b : Fin n, v b (colOf m b)

def chartVal [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
    (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S)
    (P : MvPolynomial (LtN Dw n) c.F) : S :=
  colSum c (fun b α => C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial α 1)) P

def sysVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) {n : ℕ}
    (F : Fin n → SecAt Xo c y k) (P : MvPolynomial (LtN Dw n) c.F) : S :=
  colSum c (fun b α => nab y (k : ℤ) (F b) α) P

def IsHarmonic {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
    ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
      (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0

def NabUnique : Prop :=
  ∀ [StarRing (𝓞 E)] (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k n : ℕ)
      (F : Fin n → SecAt Xo c y k) (P : MvPolynomial (LtN Dw n) c.F), IsHarmonic c P →
        sysVal Xo c nab y k F P = sysVal Xo c nab' y k F P

example {n : ℕ} (x : LtN Dw n) : IsHarmonic c (MvPolynomial.X x : MvPolynomial (LtN Dw n) c.F) := by
  classical
  intro τ i i'
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

end GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.PullbackGroupAction
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {S S' : Scheme.{0}}

abbrev pullGrp (f : S' ⟶ S) (G : Over S) : Over S' := (Over.pullback f).obj G

abbrev pullFst (f : S' ⟶ S) (G : Over S) : (pullGrp f G).left ⟶ G.left := pullback.fst G.hom f

theorem pullGrp_comm (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] : IsCommMonObj (pullGrp f G) :=
  inferInstance

def pullAct {O : Type} [CommRing O] (f : S' ⟶ S) {G : Over S} [GrpObj G] (A : OAct O G) :
    OAct O (pullGrp f G) where
  act a := (Over.pullback f).map (A.act a)
  hom a := by
    have := A.hom a
    infer_instance
  one := by rw [A.one, CategoryTheory.Functor.map_id]
  mul a b := by rw [A.mul, CategoryTheory.Functor.map_comp]
  add a b := by rw [A.add, CategoryTheory.Functor.map_mul]

theorem pullAct_fst {O : Type} [CommRing O] (f : S' ⟶ S) {G : Over S} [GrpObj G] (A : OAct O G) (a : O) :
    ((pullAct f A).act a).left ≫ pullFst f G = pullFst f G ≫ (A.act a).left := by
  exact pullback.lift_fst _ _ _

theorem eSec_pullFst (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec (pullGrp f G) ≫ pullFst f G = (show (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left from f) ≫ eSec G := by
  simp [eSec, pullFst]
  have h : pullback.fst (𝟙 S) f = pullback.snd (𝟙 S) f ≫ f := by simpa using pullback.condition (f := 𝟙 S) (g := f)
  refine (pullback.lift_fst _ _ _).trans ?_
  rw [← Category.assoc]
  exact congrArg (· ≫ _) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def HasPullWith {H : Host E} (t : SAB H S) (f : S' ⟶ S) (L' : RigLB (pullGrp f t.G)) : Prop :=
  ∃ (semi : IsSemiAbelian (pullGrp f t.G)) (cub : CubicalStr (pullGrp f t.G) L') (sym : L'.IsSymmetric)
    (adj : ∀ a : 𝓞 E,
      LBIso (cubeLB (pullGrp f t.G) ![fst _ _ ≫ (pullAct f t.act).act a, snd _ _] L'.L)
        (cubeLB (pullGrp f t.G) ![fst _ _, snd _ _ ≫ (pullAct f t.act).act (H.bar a)] L'.L))
    (prim : LBIso L'.L (cubeLB (pullGrp f t.G) ![𝟙 _, (pullAct f t.act).act H.w0] L'.L))
    (m : SABMap
      ({ G := pullGrp f t.G, semi := semi, act := pullAct f t.act, PP := L', cub := cub, sym := sym,
         adj := adj, prim := prim } : SAB H S') t f),
    m.φ = pullFst f t.G

def IsRigPull (f : S' ⟶ S) {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (L' : RigLB (pullGrp f G)) : Prop :=
  ∃ w : LB.Iso L'.L (L.L.pull (pullFst f G)), w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec (pullGrp f G)) (fun _ => 1)) L'.rig
      (rigPullOf (pullFst f G) f (eSec_pullFst f G) L.L L.rig)

def RigPullExists : Prop :=
  ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G),
    ∃ L' : RigLB (pullGrp f G), IsRigPull f L L'

def SABPull : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S)
    (L' : RigLB (pullGrp f t.G)), LBIso L'.L (t.PP.L.pull (pullFst f t.G)) → HasPullWith t f L'

def SABPullRig : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S)
    (L' : RigLB (pullGrp f t.G)), IsRigPull f t.PP L' → HasPullWith t f L'

def SABPullExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S),
    ∃ L' : RigLB (pullGrp f t.G), HasPullWith t f L'

example (h : SABPull) : SABPullRig :=
  fun E _ _ _ H S S' f t L' ⟨w, hw, _⟩ => h E H S S' f t L' ⟨w, hw⟩

example (h : SABPullRig) (h' : RigPullExists) : SABPullExists := fun E _ _ _ H S S' f t =>
  let ⟨L', hL⟩ := h' f t.G t.PP
  ⟨L', h E H S S' f t L' hL⟩

example {H : Host E} (t : SAB H S) (f : S' ⟶ S) (L' : RigLB (pullGrp f t.G)) (h : HasPullWith t f L') :
    LBIso L'.L (t.PP.L.pull (pullFst f t.G)) := by
  obtain ⟨_, _, _, _, _, m, hm⟩ := h
  obtain ⟨w, hw, _⟩ := m.lin
  rw [← hm]
  exact ⟨w, hw⟩

end GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.SideNormalisedGap
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap

open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU IsOrthProjOnto InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def dimV (k r : ℕ) : ℝ := 2 * (r : ℝ) + k + 1

def decExp (r : ℕ) (h : ℝ) : ℝ := h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))

def decConst (r : ℕ) (h : ℝ) : ℝ := Real.exp (h / (16 * ((r : ℝ) + 1)))

def dimN (k r : ℕ) : ℝ := (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2

def thrG (k r : ℕ) : ℝ := 4 * ((k : ℝ) + r) * ((r : ℝ) + 1)

def thrS (k r : ℕ) : ℝ := (dimV k r - 1) * dimN k r

def propExp (r : ℕ) : ℝ := 2 * ((r : ℝ) ^ 2 + r + 1)

def thrSS (k r : ℕ) : ℝ := 2 * propExp r * thrS k r + 1

def DecGap (k r : ℕ) (h : ℝ) : Prop := 120 * dimV k r * ((r : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤ h

def Size (k r : ℕ) (h : ℝ) : Prop :=
  DecGap k r h ∧ 16 * dimV k r ^ 5 * Real.sqrt (2 * ((r : ℝ) + 1)) ≤ h

def Thresholds (k r : ℕ) (a : ℝ) : Prop :=
  thrG k r < a / 2 ∧ thrS k r < a / 2 ∧ thrSS k r + thrG k r + 1 ≤ a ∧ thrS k r < a - 1

def mulP {k r : ℕ} (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

theorem measurable_mulP {k r : ℕ} : Measurable (mulP (k := k) (r := r)) := by
  unfold mulP
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  fun_prop

def muS {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) := (μW.prod μN).map mulP

section Side

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

def IsSide (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r)) : Prop :=
  1 ≤ k ∧
  (IsHCParam lam ∧ IsDSHpk k r ε lam σ ∧ GapAtLeast ε lam h) ∧
  IsLowUnitH k r ε lam σ w₀ ∧
  (inWb k r z ∧ 0 < Tz k r z) ∧
  c ≠ 0 ∧
  (IsHCParam u ∧ IsHCTypeW k r z u π) ∧
  (PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW ∧ PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN ∧
    PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) ∧
  (SigmaFinite ν ∧ PI.BesselPeriodGGP.IsQuotMeas μG (muS μW μN) ν)

def IsSideNormalised (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r)) : Prop :=
  IsSide k r ε lam h σ w₀ z c u π μW μN μG ν ∧ μW Set.univ = 1

def KFinDecay (k r : ℕ) (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ v v' : H, IsKFinHpk (k := k) (r := r) σ v → IsKFinHpk (k := k) (r := r) σ v' →
    ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪v', σ x v⟫_ℂ‖ ≤ C * gN x ^ (-a)

def wordSeminorm {k r : ℕ} (σ : Mat k r → (H →L[ℂ] H)) (Ws : List (List (Mat k r))) (w : H) : ℝ :=
  (Ws.map fun D => ‖dsigW (k := k) (r := r) σ D w‖).sum

end Side

def DecProj : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → DecGap k r h →
    ∀ (P : Mat k r) (E : H →L[ℂ] H), IsCayleyU k r ε P →
      IsOrthProjOnto E (lowKSub ε lam fun g => σ (P⁻¹ * g * P)) →
      ∀ κ X : Mat k r, κ ∈ UH (Hpk k r) → κ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ →
        InLieHpk k r X → Xᴴ = X →
        ‖E ∘L σ (κ * NormedSpace.exp X) ∘L E‖ ≤
          Real.exp (-(h / 8) * min (gN X ^ 2) (gN X / Real.sqrt (2 * ((r : ℝ) + 1))))

def DecLow : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → DecGap k r h →
    ∀ w₁ w₂ : H, IsLowUnitH k r ε lam σ w₁ → IsLowUnitH k r ε lam σ w₂ →
      ∀ x ∈ UH (Hpk k r),
        ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ decConst r h * dimV k r ^ (decExp r h / 2) * gN x ^ (-decExp r h)

def DecKFin : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → DecGap k r h →
    KFinDecay k r σ (decExp r h)

def DecSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ),
    IsHCParam lam → IsDSHpk k r ε lam σ → KFinDecay k r σ a →
    ∀ v₀ : H, IsKFinHpk (k := k) (r := r) σ v₀ →
      ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ D ∈ Ws, ∀ X ∈ D, InLieHpk k r X) ∧
        ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
          ‖⟪v₀, σ x w⟫_ℂ‖ ≤ C * wordSeminorm σ Ws w * gN x ^ (1 - a)

example : decExp 1 16 = 1 := by
  unfold decExp
  rw [show (2 * (((1 : ℕ) : ℝ) + 1)) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

example : dimN 1 1 = 5 ∧ thrG 1 1 = 16 ∧ thrS 1 1 = 15 ∧ thrSS 1 1 = 181 := by
  simp only [thrSS, thrS, thrG, dimN, dimV, propExp]; norm_num

example (k r : ℕ) : ∃ h, Size k r h :=
  ⟨max _ _, le_max_left _ _, le_max_right _ _⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap
end
end

