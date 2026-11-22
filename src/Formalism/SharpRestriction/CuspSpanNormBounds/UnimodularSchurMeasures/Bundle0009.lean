import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalL1StatementOfProjectors
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0005
import Formalism.FlagUnipotentLattices.HalfDeltaL1Bound
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0008
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0001

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfReduced
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

namespace BData

variable (X : BData)

def LowProj : Prop :=
  ∀ P : Mat X.k X.r, IsCayleyU X.k X.r (eps48 X.k X.r) P →
    IsDS (eps48 X.k X.r) (lam48 X.k X.r X.v X.b) (fun g => X.σ (P⁻¹ * g * P)) →
    ∃ E : X.H →L[ℂ] X.H,
      IsOrthProjOnto E (lowKSub (eps48 X.k X.r) (lam48 X.k X.r X.v X.b) (fun g => X.σ (P⁻¹ * g * P)))

def Repro (B : X.H → X.Vp) : Prop :=
  ∀ x ∈ X.G, Integrable (fun g => X.e (Matrix.of g) • X.W' B (x * Matrix.of g)) X.μG ∧
    rconv X.μG X.e (X.W' B) x = X.W' B x

def Exchange (B : X.H → X.Vp) : Prop :=
  ∀ χ, X.IsCut B χ →
    ∫ x, ⟪X.W' B (Matrix.of x), X.Wf B χ (Matrix.of x)⟫_ℂ ∂X.ν =
      ∫ x, ⟪rconv X.μG X.e (X.W' B) (Matrix.of x), X.Φ B χ (Matrix.of x)⟫_ℂ ∂X.ν

variable {X}

end BData

def StepsB2' : Prop :=
  ∀ X : BData, X.Hyp → X.LowSmooth ∧ X.SmoothCyc ∧ X.LowProj ∧
    ∀ B : X.H → X.Vp, X.IsFun B → X.CutStep B ∧ X.ProjectionSquareIntegrable B ∧ X.Repro B ∧ X.Exchange B

def StepsB2'' : Prop :=
  ∀ X : BData, X.Hyp → X.LowSmooth ∧ X.SmoothCyc ∧
    ∀ B : X.H → X.Vp, X.IsFun B → X.CutStep B ∧ X.ProjectionSquareIntegrable B ∧ X.Repro B ∧ X.Exchange B

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CechHodgeFiltration
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Obj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def ff_psi (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (X : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℂ) • ∫ kk, d30f ε lam σ w X kk ∂(Formalism.REAL.muK ε)

def ff_IsPsi (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ k X, k ∈ Formalism.REAL.Kset ε → Formalism.REAL.inP ε X → Ψ (k * NormedSpace.exp X) = σ k ∘L ff_psi ε lam σ w X

def ff_Data (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H)
    (h : ℝ) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam lam ∧ IsDS ε lam σ ∧ IsOrthProjOnto E (lowKSub ε lam σ) ∧ IsHighestUnit ε lam σ w ∧
    Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ 120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h

def ff_Sph (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ k₁ ∈ Formalism.REAL.Kset ε, ∀ k₂ ∈ Formalism.REAL.Kset ε, ∀ g ∈ UJset ε, Ψ (k₁ * g * k₂) = σ k₁ ∘L Ψ g ∘L σ k₂

def ff_Compr (ε : Fin n → Bool) (E : H →L[ℂ] H) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ g ∈ UJset ε, E ∘L Ψ g ∘L E = Ψ g

def ff_Eig (ε : Fin n → Bool) (c : ℕ → ℂ) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
    (∀ g ∈ UJset ε, F g = ⟪x, Ψ g y⟫_ℂ) ∧ ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = c k * F g

def ff_DSSum (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ (N : ℕ) (φ : Fin N → Formalism.REAL.UJ ε → ℂ), (∀ i, IsDSCoef ε (φ i)) ∧
    ∀ g : Formalism.REAL.UJ ε, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i, φ i g

end Obj

def FResId : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ff_psi ε lam σ w 0 = E

def FSph : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ∀ Ψ, ff_IsPsi ε lam σ w Ψ → ff_Sph ε σ Ψ

def FCompr : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ∀ Ψ, ff_IsPsi ε lam σ w Ψ → ff_Compr ε E Ψ

def FPsiEig (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ∀ Ψ, ff_IsPsi ε lam σ w Ψ → ff_Eig ε (χ n lam) Ψ

def FKFin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    FiniteDimensional ℂ (lowKSub ε lam σ) →
    ∀ Ψ, ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ∀ x y : H, IsKFinFunOn ε (fun g => ⟪x, Ψ g y⟫_ℂ)

def FDecay : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ff_psi ε lam σ w 0 = E → ∀ X, Formalism.REAL.inP ε X →
    ‖ff_psi ε lam σ w X‖ ≤ decBound (min (pOf ε) (qOf ε)) h X

def MatrixCoeffSquareIntegrable : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    (∀ X, Formalism.REAL.inP ε X → ‖ff_psi ε lam σ w X‖ ≤ decBound (min (pOf ε) (qOf ε)) h X) →
    ∀ Ψ, ff_IsPsi ε lam σ w Ψ → ∀ x y : H, Continuous (fun g : Formalism.REAL.UJ ε => ⟪x, Ψ (umat g) y⟫_ℂ) →
    MemLp (fun g : Formalism.REAL.UJ ε => ⟪x, Ψ (umat g) y⟫_ℂ) 2 (Formalism.REAL.muG ε)

def FSphUnique (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → Ψ 1 = E → ff_Eig ε (χ n lam) Ψ →
      ff_DSSum ε Ψ → ∀ g ∈ UJset ε, Ψ g = E ∘L σ g ∘L E

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnMeasurablePsi
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem cn_wt_nonneg {a : ℕ} (j : Fin a → ℕ) (f : ℕ) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) : 0 ≤ cn_wt j f t :=
  Finset.prod_nonneg fun x _ => by have := (ht.2 x).1; positivity

theorem cn_cnt_nonneg {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) {de : ℝ} (hde : 0 ≤ de) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) :
    0 ≤ cn_cnt j n0 f de t :=
  Finset.prod_nonneg fun r _ => by have := (cn_la_mem ht r).1; positivity

def cn_hT (f n0 j : ℕ) : ℝ → ℝ :=
  (Set.Ioo (0 : ℝ) (1 / 2)).indicator fun s : ℝ => s ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / s)

theorem cn_hT_nonneg (f n0 j : ℕ) (s : ℝ) : 0 ≤ cn_hT f n0 j s :=
  Set.indicator_nonneg (fun s hs => by have := hs.1; positivity) s

theorem cn_hT_of_mem (f n0 j : ℕ) {s : ℝ} (h0 : 0 < s) (h1 : s < 1 / 2) :
    cn_hT f n0 j s = s ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / s) :=
  Set.indicator_of_mem (show s ∈ Set.Ioo (0 : ℝ) (1 / 2) from ⟨h0, h1⟩) _

def cn_hL (f j : ℕ) (ts : ℝ) : ℝ → ℝ := (Set.Ico ts (1 / 2)).indicator fun s : ℝ => 2 * (f : ℝ) * j / s

theorem cn_hL_nonneg (f j : ℕ) {ts : ℝ} (h0 : 0 < ts) (s : ℝ) : 0 ≤ cn_hL f j ts s :=
  Set.indicator_nonneg (fun s hs => by have := lt_of_lt_of_le h0 hs.1; positivity) s

theorem cn_hL_of_mem (f j : ℕ) {ts s : ℝ} (h0 : ts ≤ s) (h1 : s < 1 / 2) : cn_hL f j ts s = 2 * (f : ℝ) * j / s :=
  Set.indicator_of_mem (show s ∈ Set.Ico ts (1 / 2) from ⟨h0, h1⟩) _

theorem cn_hL_measurable (f j : ℕ) (ts : ℝ) : Measurable (cn_hL f j ts) :=
  (measurable_const.div measurable_id).indicator measurableSet_Ico

theorem cn_dens_wt_le {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) :
    cn_dens j n0 f t * cn_wt j f t ≤ ∏ x, cn_hT f n0 (j x) (t x) := by
  have e1 : ∏ x, cn_hT f n0 (j x) (t x) = (∏ x, t x ^ (2 * j x * n0 * f)) * cn_wt j f t := by
    unfold cn_wt
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => cn_hT_of_mem f n0 (j x) (ht.2 x).1 (ht.2 x).2
  rw [e1]
  exact mul_le_mul_of_nonneg_right (cn_dens_le j n0 f ht) (cn_wt_nonneg j f ht)

theorem cn_int_hT_le (f n0 j : ℕ) (hf : 1 ≤ f) (hj : 1 ≤ j) (hn : 1 ≤ n0) : ∫ s, cn_hT f n0 j s ≤ 1 := by
  have h := (cn_int_tau f j n0 hf hj hn).2
  unfold cn_hT
  rw [h]
  have h1 : ((1 : ℝ) / 2) ^ (2 * j * n0 * f) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (1 : ℝ) ≤ n0 := by exact_mod_cast hn
  rw [div_le_one (by linarith)]
  linarith

theorem cn_int_dens_le {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (hf : 1 ≤ f) (hj : ∀ x, 1 ≤ j x) (hn : 1 ≤ n0) :
    ∫⁻ t in cn_Reg a, ENNReal.ofReal (cn_dens j n0 f t * cn_wt j f t) ≤ 1 := by
  have s1 : ∫⁻ t in cn_Reg a, ENNReal.ofReal (cn_dens j n0 f t * cn_wt j f t) ≤
      ∫⁻ t in cn_Reg a, ENNReal.ofReal (∏ x, cn_hT f n0 (j x) (t x)) :=
    setLIntegral_mono' (cn_measurableSet_Reg a) fun t ht => ENNReal.ofReal_le_ofReal (cn_dens_wt_le j n0 f ht)
  have s2 : ∫⁻ t in cn_Reg a, ENNReal.ofReal (∏ x, cn_hT f n0 (j x) (t x)) ≤
      ∫⁻ t : Fin a → ℝ, ENNReal.ofReal (∏ x, cn_hT f n0 (j x) (t x)) := setLIntegral_le_lintegral _ _
  have s3 := cn_lint_prod (fun x => cn_hT f n0 (j x)) (fun x => (cn_int_tau f (j x) n0 hf (hj x) hn).1)
    (fun x s => cn_hT_nonneg f n0 (j x) s)
  have s4 : ENNReal.ofReal (∏ x, ∫ s, cn_hT f n0 (j x) s) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Finset.prod_le_one (fun x _ => integral_nonneg (cn_hT_nonneg f n0 (j x)))
      fun x _ => cn_int_hT_le f n0 (j x) hf (hj x) hn)
  exact s1.trans (s2.trans (s3.le.trans s4))

def cn_Psi {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (de ts : ℝ) : (Fin a → ℝ) → ℝ≥0∞ := fun t =>
  ENNReal.ofReal (cn_cnt j n0 f de t) * ({t : Fin a → ℝ | ∀ x, ts ≤ t x}.indicator 1 t)

theorem cn_measurable_Psi {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (de ts : ℝ) : Measurable (cn_Psi j n0 f de ts) := by
  have hs : MeasurableSet {t : Fin a → ℝ | ∀ x, ts ≤ t x} := by
    have : {t : Fin a → ℝ | ∀ x, ts ≤ t x} = ⋂ x, {t : Fin a → ℝ | ts ≤ t x} := by
      ext t; simp
    rw [this]
    exact MeasurableSet.iInter fun x => measurableSet_le measurable_const (measurable_pi_apply x)
  exact (ENNReal.measurable_ofReal.comp (cn_measurable_cnt j n0 f de)).mul (measurable_one.indicator hs)

theorem cn_Psi_dens_le {a : ℕ} (j : Fin a → ℕ) (n0 f n q : ℕ) (de ts : ℝ) (hn : n0 + 2 * ∑ x, j x = n)
    (hq : ∑ x, j x ≤ q) (hde : 0 ≤ de) (hsm : de * q * n * f ≤ 1 / 100) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) :
    cn_Psi j n0 f de ts t * ENNReal.ofReal (cn_dens j n0 f t * cn_wt j f t) ≤
      2 * ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) := by
  unfold cn_Psi
  by_cases h2 : ∀ x, ts ≤ t x
  · rw [Set.indicator_of_mem (show t ∈ {t : Fin a → ℝ | ∀ x, ts ≤ t x} from h2), Pi.one_apply, mul_one,
      ← ENNReal.ofReal_mul (cn_cnt_nonneg j n0 f hde ht)]
    have e1 : ∏ x, cn_hL f (j x) ts (t x) = cn_wt j f t :=
      Finset.prod_congr rfl fun x _ => cn_hL_of_mem f (j x) (h2 x) (ht.2 x).2
    rw [e1, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (cn_cnt_dens_le j n0 f n q de hn hq hde hsm ht) (cn_wt_nonneg j f ht)
  · rw [Set.indicator_of_notMem (show t ∉ {t : Fin a → ℝ | ∀ x, ts ≤ t x} from h2)]
    simp

theorem cn_int_near_le {a : ℕ} (j : Fin a → ℕ) (n0 f n q : ℕ) (de ts : ℝ) (hn : n0 + 2 * ∑ x, j x = n)
    (hq : ∑ x, j x ≤ q) (hde : 0 ≤ de) (hsm : de * q * n * f ≤ 1 / 100) (h0 : 0 < ts) (h1 : ts ≤ 1 / 2) :
    ∫⁻ t in cn_Reg a, cn_Psi j n0 f de ts t * ENNReal.ofReal (cn_dens j n0 f t * cn_wt j f t) ≤
      2 * ENNReal.ofReal (∏ x, (2 * (f : ℝ) * j x * Real.log (1 / (2 * ts)))) := by
  have s1 : ∫⁻ t in cn_Reg a, cn_Psi j n0 f de ts t * ENNReal.ofReal (cn_dens j n0 f t * cn_wt j f t) ≤
      ∫⁻ t in cn_Reg a, 2 * ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) :=
    setLIntegral_mono' (cn_measurableSet_Reg a) fun t ht => cn_Psi_dens_le j n0 f n q de ts hn hq hde hsm ht
  have s2 : ∫⁻ t in cn_Reg a, 2 * ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) ≤
      ∫⁻ t : Fin a → ℝ, 2 * ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) := setLIntegral_le_lintegral _ _
  have hm : Measurable fun t : Fin a → ℝ => ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun x _ =>
      (cn_hL_measurable f (j x) ts).comp (measurable_pi_apply x))
  have s3 : ∫⁻ t : Fin a → ℝ, 2 * ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) =
      2 * ∫⁻ t : Fin a → ℝ, ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) := lintegral_const_mul _ hm
  have s4 := cn_lint_prod (fun x => cn_hL f (j x) ts) (fun x => (cn_int_log f (j x) ts h0 h1).1)
    (fun x s => cn_hL_nonneg f (j x) h0 s)
  have s5 : ∏ x, ∫ s, cn_hL f (j x) ts s = ∏ x, (2 * (f : ℝ) * j x * Real.log (1 / (2 * ts))) :=
    Finset.prod_congr rfl fun x _ => (cn_int_log f (j x) ts h0 h1).2
  rw [s5] at s4
  rw [s4] at s3
  exact s1.trans (s2.trans s3.le)

theorem cn_sum_types_le (q : ℕ) (T : ∀ J : ℕ, Composition J → ℝ≥0∞) (B : ℝ≥0∞)
    (h : ∀ J ∈ Finset.Icc 1 q, ∀ c, T J c ≤ B) : ∑ J ∈ Finset.Icc 1 q, ∑ c, T J c ≤ 2 ^ q * B := by
  calc ∑ J ∈ Finset.Icc 1 q, ∑ c, T J c ≤ ∑ J ∈ Finset.Icc 1 q, (Fintype.card (Composition J) : ℝ≥0∞) * B := by
        refine Finset.sum_le_sum fun J hJ => ?_
        refine le_trans (Finset.sum_le_sum fun c _ => h J hJ c) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        rfl
    _ = ((∑ J ∈ Finset.Icc 1 q, Fintype.card (Composition J) : ℕ) : ℝ≥0∞) * B := by
        rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ 2 ^ q * B := by
        refine mul_le_mul_left ?_ _
        have := Formalism.HermitianLatticeCounting.Final.S7.typeCount q
        exact_mod_cast this

namespace CSize

variable {X : CData} (S : CSize X)

theorem type_mass (hD : S.Density) {J : ℕ} (c : Composition J) (hJ1 : 1 ≤ J) (hJq : J ≤ X.qq) (hn0 : 1 ≤ X.I.n - 2 * J) :
    X.μ (S.str J c) ≤ ENNReal.ofReal (X.I.vol X.μf X.fund * S.kap J c) := by
  have h := hD J c hJ1 hJq (fun _ => 1) measurable_const
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ] at h
  refine h.trans (mul_le_of_le_one_right' ?_)
  exact cn_int_dens_le c.blocksFun _ _ (one_le_autInst_f X.I) c.one_le_blocksFun hn0

theorem compl_Mod_subset (hS : S.Strata) {C₁ : ℝ} (hts : cn_tauS X C₁ ≤ 1 / 2) :
    (S.Mod C₁)ᶜ ⊆ ⋃ J ∈ Finset.Icc 1 X.qq, ⋃ c ∈ (Finset.univ : Finset (Composition J)), S.str J c := by
  intro x hx
  have hx' : S.tau1 x < cn_tauS X C₁ := not_le.1 hx
  rcases hS.2.2.2.1 x with h0 | ⟨J, h1, h2, c, hc⟩
  · have := hS.2.2.2.2.1 x h0
    linarith
  · simp only [Set.mem_iUnion]
    exact ⟨J, Finset.mem_Icc.2 ⟨h1, h2⟩, c, Finset.mem_univ _, hc⟩

theorem compl_Mod_le (hS : S.Strata) (hD : S.Density) {C₁ : ℝ} (hts : cn_tauS X C₁ ≤ 1 / 2) (hn : 2 * X.qq + 1 ≤ X.I.n) :
    X.μ (S.Mod C₁)ᶜ ≤ ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J, ENNReal.ofReal (X.I.vol X.μf X.fund * S.kap J c) := by
  refine le_trans (measure_mono (S.compl_Mod_subset hS hts)) ?_
  refine le_trans (measure_biUnion_finset_le _ _) (Finset.sum_le_sum fun J hJ => ?_)
  refine le_trans (measure_biUnion_finset_le _ _) (Finset.sum_le_sum fun c _ => ?_)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hJ
  exact S.type_mass hD c h1 h2 (by omega)

theorem near_le (hS : S.Strata) (hD : S.Density) {εN δ : ℝ} (hN : S.NearCount εN δ) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    {C₁ : ℝ} (h0 : 0 < cn_tauS X C₁) (hts : cn_tauS X C₁ ≤ 1 / 2) (hn : 2 * X.qq + 1 ≤ X.I.n) (hδ : 0 ≤ δ)
    (hsm : δ * X.qq * X.I.n * X.I.f ≤ 1 / 100) :
    ∫⁻ x in S.Mod C₁, X.nearS εN x ∂X.μ ≤
      ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J,
        ENNReal.ofReal (fdegAll X.I X.σ X.w * (X.e 1).re) * (ENNReal.ofReal (X.I.vol X.μf X.fund * S.kap J c) *
          (2 * ENNReal.ofReal (∏ a, (2 * (X.I.f : ℝ) * c.blocksFun a * Real.log (1 / (2 * cn_tauS X C₁)))))) := by
  set M : ℝ≥0∞ := ENNReal.ofReal (fdegAll X.I X.σ X.w * (X.e 1).re) with hM
  set G : ∀ J : ℕ, Composition J → X.I.GA → ℝ≥0∞ := fun J c =>
    (S.str J c).indicator fun x => M * cn_Psi c.blocksFun (X.I.n - 2 * J) X.I.f δ (cn_tauS X C₁) (S.tau J c x) with hG
  have hGm : ∀ J c, Measurable (G J c) := fun J c =>
    (((cn_measurable_Psi _ _ _ _ _).comp (hS.2.2.1 J c)).const_mul M).indicator (hS.2.1 J c)
  have hpt : ∀ x ∈ S.Mod C₁, X.nearS εN x ≤ ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J, G J c x := by
    intro x hx
    rcases hS.2.2.2.1 x with hx0 | ⟨J, h1, h2, c, hc⟩
    · have := cn_nearS_le X hX εN x 0 fun T hT => by
        have : T = ∅ := Finset.eq_empty_of_forall_notMem fun γ hγ =>
          (hT γ hγ).2 (hN.1 x hx0 γ (hT γ hγ).1.1 (hT γ hγ).1.2)
        simp [this]
      simp only [ENNReal.ofReal_zero, mul_zero] at this
      exact le_trans this zero_le
    · have h3 := cn_nearS_le X hX εN x _ (hN.2 J c x hc)
      have h4 : G J c x = M * ENNReal.ofReal (cn_cnt c.blocksFun (X.I.n - 2 * J) X.I.f δ (S.tau J c x)) := by
        simp only [hG]
        rw [Set.indicator_of_mem hc]
        unfold cn_Psi
        rw [Set.indicator_of_mem (show S.tau J c x ∈ {t : Fin c.length → ℝ | ∀ a, cn_tauS X C₁ ≤ t a} from
          fun a => le_trans hx (hS.2.2.2.2.2.2 J c x hc a)), Pi.one_apply, mul_one]
      rw [← h4] at h3
      refine le_trans h3 ?_
      refine le_trans ?_ (Finset.single_le_sum (f := fun J => ∑ c : Composition J, G J c x) (fun _ _ => zero_le)
        (Finset.mem_Icc.2 ⟨h1, h2⟩))
      exact Finset.single_le_sum (f := fun c => G J c x) (fun _ _ => zero_le) (Finset.mem_univ c)
  calc ∫⁻ x in S.Mod C₁, X.nearS εN x ∂X.μ
      ≤ ∫⁻ x in S.Mod C₁, ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J, G J c x ∂X.μ :=
        setLIntegral_mono' (S.measurableSet_Mod hS C₁) hpt
    _ ≤ ∫⁻ x, ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J, G J c x ∂X.μ := setLIntegral_le_lintegral _ _
    _ = ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J, ∫⁻ x, G J c x ∂X.μ := by
        rw [lintegral_finsetSum _ fun J _ => Finset.measurable_sum _ fun c _ => hGm J c]
        exact Finset.sum_congr rfl fun J _ => lintegral_finsetSum _ fun c _ => hGm J c
    _ ≤ _ := by
        refine Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hJ
        simp only [hG]
        rw [lintegral_indicator (hS.2.1 J c),
          lintegral_const_mul M (show Measurable fun x => cn_Psi c.blocksFun (X.I.n - 2 * J) X.I.f δ (cn_tauS X C₁)
            (S.tau J c x) from (cn_measurable_Psi _ _ _ _ _).comp (hS.2.2.1 J c))]
        refine mul_le_mul_right ?_ _
        refine le_trans (hD J c h1 h2 _ (cn_measurable_Psi _ _ _ _ _)) (mul_le_mul_right ?_ _)
        exact cn_int_near_le c.blocksFun _ _ X.I.n X.qq δ _ (by rw [c.sum_blocksFun]; omega)
          (by rw [c.sum_blocksFun]; exact h2) hδ hsm h0 hts

end CSize

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndDiamOfKnown
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (P0 b1 Ydat)

def cnd_CovLe (Nmax : ℕ) (κ : ℝ) (P : ℝ → Prop) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V) (_ : FiniteDimensional ℝ V) (M : Submodule ℤ V),
    DiscreteTopology M ∧ Submodule.span ℝ (M : Set V) = ⊤ ∧ Module.finrank ℝ V ≤ Nmax ∧
    (∀ y ∈ Formalism.HadamardInequality.zdual M, y ≠ 0 → κ ≤ ‖y‖) ∧ ∀ R : ℝ, (∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ R) → P R

def cnd_Diam (X : CData) (Cq ρ ρ₀ : ℝ) : Prop :=
  cnd_CovLe (2 * X.I.n ^ 2 * X.I.f) (Real.sqrt (X.I.f : ℝ) / (2 * X.I.rd * ρ₀)) fun R₁ =>
    cnd_CovLe (2 * X.I.n ^ 2 * X.I.f) (Real.sqrt (X.I.f : ℝ) / (2 * X.I.rd * ρ₀)) fun R₂ =>
      ρ ≤ Cq * Real.sqrt (X.I.f : ℝ) * (X.g : ℝ) * (R₁ + R₂)

def CSize.DeepStepsQ {X : CData} (S : CSize X) (volK C Cq : ℝ) : Prop :=
  0 < volK ∧ X.I.vol X.μf X.fund / volK ≤ cn_Y X ^ (C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) ∧
    ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
      ∃ (a : ℕ) (τ : ℕ → ℝ), 1 ≤ a ∧ a ≤ X.qq ∧ (∀ i, 0 < τ i) ∧ τ (a + 1) = 1 / 2 ∧ τ 1 = S.tau1 x ∧
        ∀ b' : ℕ, 1 ≤ b' → b' ≤ a → ∃ (ρ : ℝ) (s : ℕ → ℝ) (mult : ℝ), 0 ≤ ρ ∧
          cnd_Diam X Cq ρ (τ b' / τ (b' + 1)) ∧ (∀ P, 0 ≤ s P) ∧
          |(X.kerD x).re| ≤ s 0 ^ 2 ∧
          (∀ P < P0 X.I.n X.qq X.I.f, s P ≤ ρ * Real.sqrt ((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) *
            (C * (X.I.n : ℝ) * (X.b ^ 2 + (P : ℝ) * (X.I.n : ℝ))) * s (P + 1)) ∧
          s (P0 X.I.n X.qq X.I.f) ^ 2 ≤ (4 / (1 / (C * (X.I.n : ℝ) * b1 X.I.n X.qq X.I.f X.b))) ^ (X.I.n ^ 2 * X.I.f) * mult *
            (X.Dc / volK) ∧
          mult ≤ (C * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f)

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CovolumeIndependentOfFundamentalDomain
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def LocFinF (X : CData) : Prop := IsLocallyFiniteMeasure X.μf

theorem rr_locFin_of_integrable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (e : G → ℂ) (hl : IsLocallyConstant e) (hi : Integrable e μ)
    (h1 : e 1 ≠ 0) : IsLocallyFiniteMeasure μ := by
  set U : Set G := e ⁻¹' {e 1} with hU
  have hUo : IsOpen U := hl.isOpen_fiber (e 1)
  have hUfin : μ U < ⊤ := by
    have hsub : U ⊆ {x | ‖e 1‖ ≤ ‖e x‖} := fun x hx => by
      have : e x = e 1 := hx
      simp [this]
    exact lt_of_le_of_lt (measure_mono hsub) (hi.measure_norm_ge_lt_top (norm_pos_iff.2 h1))
  refine ⟨fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' U, ?_, ?_⟩⟩
  · exact (hUo.preimage (continuous_const_mul x⁻¹)).mem_nhds (by simp [hU])
  · rw [measure_preimage_mul]; exact hUfin

theorem LocFinF_of_e (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.e 1 ≠ 0) : LocFinF X := by
  have hH : X.μf.IsHaarMeasure := hX.2.1.2.2.2.1
  have hadm := hX.1.2.2.2.2.2.2.1
  exact rr_locFin_of_integrable X.μf X.e hadm.1 hX.2.1.2.2.2.2.2.2.1 h1

example (X : CData) [SecondCountableTopology X.I.Gf] : BorelSpace X.I.GA := inferInstance
example (X : CData) : IsTopologicalGroup X.I.GA := inferInstance
example (X : CData) [SecondCountableTopology X.I.Gf] : SecondCountableTopology X.I.GA := inferInstance
theorem automorphic_L2_secondCountable (X : CData) [SecondCountableTopology X.I.Gf] : SecondCountableTopology X.L2 := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  infer_instance
example (X : CData) : IsLocallyFiniteMeasure (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)) := inferInstance
example (X : CData) : (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)).IsHaarMeasure := inferInstance
example (X : CData) : LocallyCompactSpace X.I.Ginf := inferInstance
example (X : CData) : BorelSpace X.I.Ginf := inferInstance
example (X : CData) : T2Space X.I.Ginf := inferInstance

theorem rr_muA_locFin (X : CData) (h : LocFinF X) : IsLocallyFiniteMeasure (X.I.muA X.μf) := by
  have : IsLocallyFiniteMeasure X.μf := h
  unfold AutInst.muA; infer_instance

theorem rr_muA_openPos (X : CData) [X.μf.IsHaarMeasure] : (X.I.muA X.μf).IsOpenPosMeasure := by
  unfold AutInst.muA; infer_instance

theorem covolume_independent_of_fundamental_domain (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulLeftInvariant] (fund fund' : Set I.GA)
    (h : I.IsFundDom (I.muA μf) fund) (h' : I.IsFundDom (I.muA μf) fund') : I.muA μf fund = I.muA μf fund' := by
  have : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  exact (rr_isFD (rr_FD_of I μf fund h)).measure_eq (rr_isFD (rr_FD_of I μf fund' h'))

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OperatorExistsOfUnitaryContinuous
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem pj_schurS (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : SchurS X :=
  pj_dens (muInf X) X.σs (pj_tensRep X hX).2.2.1
    (fun x y => (continuous_const.inner ((pj_tensRep X hX).2.2.2 x)).aestronglyMeasurable)
    (Submodule.span ℂ (Set.range X.tens)) hX.2.1.2.2.1.2.2 (fdegAll X.I X.σ X.w) (pj_fdegAll_pos D h1 X hX)
    (pj_schur_span D h1 X hX)

theorem projection_and_count_facts (D : Formalism.BasicNotions.D7) (h1 : adm1 D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (hph : Integrable (phOf X.I X.σ X.w) (muInf X)) (hR : RepA X) (hUm : UnimodF X) :
    X.ProjStep ∧ X.CountedStep :=
  pj_main D h1 X hX hph hR hUm (pj_sepF X hX) (pj_tensRep X hX) (pj_schurS D h1 X hX)

def StepsB' (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → RepA X ∧ UnimodF X ∧ X.CuspStep

theorem integrable_one_place_of_local (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) : MatrixCoefficientIntegrable D :=
  fun n ε lam hlam H _ _ _ σ hDS w hw h hg hh => (hloc n ε lam hlam H σ hDS w hw h hg hh).1

end Formalism.MainNotions.LeviCoordinates

end
end

