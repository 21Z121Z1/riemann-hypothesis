import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
import Formalism.ThetaLiftIndependence.Statement
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaussDensDefinite
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.GaussMean.Test

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.AutInhab

theorem lamX_one (I : AutInst) : lamX I (1, 1) = I.L := by
  refine le_antisymm (fun y hy => (I.L_dual y).2 fun z hz => ?_) (GlobalTheory.Count.Test.le_lamX_one I)
  exact ((GlobalTheory.PointLattice.lamX_selfDual I (1, 1)).2.2.2.1 y).1 hy z (GlobalTheory.Count.Test.le_lamX_one I hz)

theorem gaussDens_definite (n : ℕ) : gaussDens (fun _ : Fin n => true) (sgn ℝ false) = 0 := by
  have : (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps (fun _ => true) y ≤ t}, gauss y) =ᶠ[nhds (sgn ℝ false)]
      fun _ => 0 := by
    have h : Set.Iio (0 : ℝ) ∈ nhds (sgn ℝ false) := Iio_mem_nhds (by simp [sgn])
    filter_upwards [h] with t ht
    have : {y : Fin n → ℂ | qEps (fun _ => true) y ≤ t} = ∅ := by
      ext y
      have : 0 ≤ qEps (fun _ => true) y := Finset.sum_nonneg fun i _ => by simp
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht this
    simp [this]
  rw [gaussDens, this.deriv_eq]; simp

theorem disc_integral {t : ℝ} (ht : 0 < t) :
    ∫ y in {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t}, gauss y = Real.pi * (1 - Real.exp (-t)) := by
  have h1 : ∫ y in {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t}, gauss y =
      ∫ z : ℂ, (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) ‖z‖ := by
    have hm : MeasurableSet {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t} := by
      refine measurableSet_le ?_ measurable_const
      unfold qEps; fun_prop
    rw [← integral_indicator hm, ← (volume_preserving_funUnique (Fin 1) ℂ).integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Set.indicator, Set.mem_setOf_eq, Set.mem_Iic, qEps, gauss, Real.le_sqrt (norm_nonneg _) ht.le]
    simp
  rw [h1, integral_fun_norm_addHaar]
  have h2 : ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
      (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) y = (1 - Real.exp (-t)) / 2 := by
    have : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) •
      (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) y) =
        (Set.Iic (Real.sqrt t)).indicator (fun r => r * Real.exp (-r ^ 2)) := by
      funext y; simp only [Set.indicator]; split_ifs <;> simp
    rw [this, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic,
      ← intervalIntegral.integral_of_le (Real.sqrt_nonneg t)]
    have hd : ∀ x ∈ Set.uIcc 0 (Real.sqrt t),
        HasDerivAt (fun r : ℝ => -Real.exp (-r ^ 2) / 2) (x * Real.exp (-x ^ 2)) x := by
      intro x _
      have := (((hasDerivAt_pow 2 x).neg.exp).neg).div_const 2
      refine HasDerivAt.congr_deriv this ?_
      simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [Real.sq_sqrt ht.le]; simp; ring
  rw [h2]
  simp [Measure.real, Complex.volume_ball]
  ring

theorem gaussDens_circle : gaussDens (fun _ : Fin 1 => true) (sgn ℝ true) = Real.pi * Real.exp (-1) := by
  have : (fun t : ℝ => ∫ y in {y : Fin 1 → ℂ | qEps (fun _ => true) y ≤ t}, gauss y) =ᶠ[nhds 1]
      fun t => Real.pi * (1 - Real.exp (-t)) := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with t ht using disc_integral ht
  have hs : sgn ℝ true = 1 := by simp [sgn]
  rw [gaussDens, hs, this.deriv_eq]
  have := (((hasDerivAt_id (1 : ℝ)).neg.exp).const_sub 1).const_mul Real.pi
  simpa using this.deriv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isPerpInst_ofSigns (cm : Formalism.BasicNotions.CMData F E) {n : ℕ} (s : Bool) (ε : Fin n → Bool) :
    IsPerpInst (ofSigns cm (Fin.cons s ε : Fin (n + 1) → Bool)) (ofSigns cm ε) (RingEquiv.refl E) s
      (Pi.single (0 : Fin (n + 1)) (1 : E)) (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) 1 := by
  unfold IsPerpInst
  rw [lamX_one]
  refine ⟨fun _ => rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show star (Pi.single (0 : Fin (n + 1)) (1 : E)) ⬝ᵥ (signMat E (Fin.cons s ε : Fin (n + 1) → Bool) *ᵥ (Pi.single (0 : Fin (n + 1)) (1 : E))) = sgn E s
    simp [signMat, sgn, dotProduct, Fin.sum_univ_succ, Matrix.mulVec_diagonal]
  · show star (Pi.single (0 : Fin (n + 1)) (1 : E)) ᵥ* (signMat E (Fin.cons s ε : Fin (n + 1) → Bool) * (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0)) = 0
    funext j
    simp [signMat, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.diagonal_mul, (Fin.succ_ne_zero j).symm]
  · show (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0)ᴴ * signMat E (Fin.cons s ε : Fin (n + 1) → Bool) * (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) = (signMat E ε).map (RingEquiv.refl E)
    ext i j
    rw [Matrix.mul_apply]
    simp only [signMat, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.map_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · show (Pi.single (0 : Fin (n + 1)) (1 : E)) ∈ intLat E (n + 1)
    exact Submodule.subset_span ⟨0, by simp⟩
  · show ∀ y : Fin n → E, y ∈ intLat E n ↔ (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) *ᵥ y ∈ intLat E (n + 1)
    intro y
    have e : (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => if i = j.succ then (1 : E) else 0) *ᵥ (y : Fin n → E)
        = (Fin.cons 0 y : Fin (n + 1) → E) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Matrix.mulVec, dotProduct, (Fin.succ_ne_zero _).symm]
      · simp [Matrix.mulVec, dotProduct]
    rw [e, mem_intLat, mem_intLat, Fin.forall_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact ⟨fun h => ⟨zero_mem _, h⟩, fun h => h.2⟩

theorem exists_isPerpInst (n : ℕ) (s : Bool) :
    ∃ (I I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf),
      I.n = n + 1 ∧ IsPerpInst I I' e s x A xf := by
  obtain ⟨I, -⟩ := exists_signature 0 0
  exact ⟨_, _, _, _, _, _, rfl, isPerpInst_ofSigns I.cm s (fun _ : Fin n => true)⟩

theorem gaussSum_ne_zero {I I' : AutInst} {e : I'.E ≃+* I.E} {s : Bool} {x : Fin I.n → I.E}
    {A : Matrix (Fin I.n) (Fin I'.n) I.E} {xf : I.Gf} (h : IsPerpInst I I' e s x A xf) :
    gaussSum I (sgn I.E s) (1, xf) ≠ 0 := by
  intro h0
  have := ENNReal.tsum_eq_zero.1 h0 ⟨x, h.2.2.2.2.2.1, h.2.2.1⟩
  rw [ENNReal.ofReal_eq_zero] at this
  exact absurd this (not_le.2 (Finset.prod_pos fun v _ => gauss_pos _))

theorem const_agree (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) (hv : 0 < Formalism.HermitianLatticesTheory.vInv E)
    (hL : Formalism.HermitianLatticesTheory.lValEta E M ≠ 0) :
    meanConst E M * Formalism.HermitianLatticesTheory.massRatioRightSide E M *
      (2 ^ M * Real.pi ^ M / ((M - 1).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg E = 2 ^ (M * Formalism.HermitianLatticesTheory.fDeg E) := by
  unfold meanConst Formalism.HermitianLatticesTheory.massRatioRightSide
  have h2 : (0 : ℝ) < 2 * Formalism.HermitianLatticesTheory.vInv E := by positivity
  have hs : Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E) =
      (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h2.le]; congr 1; ring
  have hp : 0 < (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) / 2) := Real.rpow_pos_of_pos h2 _
  have hf : (0 : ℝ) < ((M - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have := Real.pi_pos
  rw [hs]
  simp only [mul_pow, div_pow, pow_mul]
  field_simp

end GlobalTheory.GaussMean.Test
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
section
noncomputable section

open scoped Classical

namespace GlobalTheory.LoopC

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev Fg (T : D.host.E) : Type := LFlag (hS D) D.R.rS T

abbrev Fb (u : D.what₂.Word) : Type := FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)

abbrev LatW : Type := Submodule (𝓞 D.host.E) (D.sp.X 0).V

def IsBase (u : D.what₂.Word) (F0 : Fb D u) : Prop := F0.e = D.sp.hypE ∧ F0.z = D.zmOf u

def seen {T : D.host.E} (F : Fg D T) (M : LatV D) : LatW D :=
  (M ⊔ toO (hS D) (Xsp F)).comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E))

def sat (L P : LatW D) : LatW D :=
  L ⊓ (Submodule.span D.host.E (P : Set (D.sp.X 0).V)).restrictScalars (𝓞 D.host.E)

def perpE (P : LatW D) : Submodule D.host.E (D.sp.X 0).V := ⨅ p ∈ P, LinearMap.ker ((D.sp.X 0).hT p)

def perpW (L P : LatW D) : LatW D := L ⊓ (perpE D P).restrictScalars (𝓞 D.host.E)

def idxW (A B : LatW D) : ℕ := Nat.card (A ⧸ B.comap A.subtype)

def rkW (P : LatW D) : ℕ := finrank D.host.E (Submodule.span D.host.E (P : Set (D.sp.X 0).V))

def detW (P : LatW D) : ℝ := latDetH (D.sp.X 0).hT P

def SubOK (L P : LatW D) (s : ℕ) (Q : ℝ) : Prop :=
  P ≤ L ∧ rkW D P = D.R.k - s ∧ 1 ≤ idxW D (sat D L P) P ∧ (idxW D (sat D L P) P : ℝ) ≤ Q ∧ detW D P ≤ Q

def N1 (Λ : LatV D) {T : D.host.E} (F : Fg D T) : Set ((hS D).V ≃ₗ[D.host.E] (hS D).V) :=
  {n | n ∈ NLam Λ F ∧ ∀ b, n (frame F b) = frame F b}

def YS : LatV D :=
  Submodule.span (𝓞 D.host.E)
    {y | ∃ (a : Fin D.R.rS) (x : D.host.E),
      x ∈ (ddS D ^ ((D.R.rS : ℤ) - (a : ℕ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧
        y = x • D.sp.hypF a}

def IsSplit {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) : Prop :=
  Λ = XS D F0 ⊔ (Λ ⊓ toO (hS D) (Wb D)) ⊔ YS D

def FixFr {T : D.host.E} (F : Fg D T) (n : (hS D).V ≃ₗ[D.host.E] (hS D).V) : Prop :=
  n ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT ∧ (∀ b, n (frame F b) = frame F b) ∧ ∀ x ∈ orth (hS D) (Xsp F), n x - x ∈ Xsp F

def FrSet (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D) : Set (Fg D T') :=
  {F' | IsTermF D Λ F F' ∧ ZEquiv (ZhatL F F') Z ∧ P ≤ seen D F (Thp Λ F F')}

def cntFr (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D) : ℕ∞ :=
  cntCl (FrSet D Λ F T' Z P) (TEqv D Λ F)

def ExSet (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D) : Set (Fg D T') :=
  {F' | IsLift Λ F' ∧ (∀ a, F'.fl.e a ∈ Λ) ∧ ZhatL F F' = Z ∧ P ≤ seen D F (Thp Λ F F')}

def FixSet (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D)
    (φ : P →ₗ[𝓞 D.host.E] (hS D).V) : Set (Fg D T') :=
  {F' | IsLift Λ F' ∧ (∀ a, F'.fl.e a ∈ Λ) ∧ ZhatL F F' = Z ∧
    ∀ (p : P) (b : Fin (D.R.rS + 1)), (hS D).hT (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) (frame F' b) = 0}

def IsWcomp (P : LatW D) (x : (hS D).V) (w : (D.sp.X 0).V) : Prop :=
  w ∈ perpE D P ∧ ∀ σ ∈ perpE D P, (hS D).hT (D.sp.iXY 0 σ) x = (D.sp.X 0).hT σ w

def Gmat (T T' : D.host.E) (Z : GramM D) : D.host.E :=
  leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) -
    T * T' * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS))

def rowMinor (Z : GramM D) (b₀ : Fin (D.R.rS + 1)) : D.host.E :=
  ((Z.submatrix Fin.castSucc id).submatrix id b₀.succAbove).det

def QOK (u u' : D.what₂.Word) (Z : GramM D) (Q : ℝ) : Prop :=
  1 ≤ Q ∧ D.host.rdE ^ (2 * D.R.f * D.R.rS) ≤ Q ∧
  (∃ b₀, rowMinor D Z b₀ ≠ 0 ∧ ∏ τ, ‖embS D τ (rowMinor D Z b₀)‖ ^ 2 ≤ Q) ∧
  Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z ≠ 0 ∧
  ∏ τ, ‖embS D τ (Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z)‖ ≤ Q

def fixB (s : ℕ) (N De Q : ℝ) : ℝ :=
  9 ^ (s * D.R.f) * (De ^ 2 * N ^ 2 * Q) ^ (s + s * D.R.rS) * Q ^ (2 * D.R.rS ^ 2)

def frB (s : ℕ) (N De Q : ℝ) : ℝ := N ^ (2 * D.R.rS) * De ^ D.R.rS * fixB D s N De Q

def glueSet (u : D.what₂.Word) (L' : LatW D) : Set (LatV D) :=
  {L | L.FG ∧ spanE (hS D) L = Wb D ∧ dualIn (hS D) L = L ∧ D.zmOf u ∈ L ∧
    (∀ c : D.host.E, c • D.zmOf u ∈ L → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) ∧
    L.comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E)) = L'}

end GlobalTheory.LoopC

end
end

