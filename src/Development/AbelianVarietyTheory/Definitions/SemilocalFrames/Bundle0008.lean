import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.RealPlaceAnalysis.StatementU
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Jet

def IsDer {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  GlRel E ∧ IsUnitary ε E ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∀ v : V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) ((∑ a, ∑ b, X a b • E a b v : V) : H) 0) ∧
    ∀ (v : V) (y : H), SmoothOnG ε (fun g => ⟪y, σ g (v : H)⟫_ℂ)

def at1 {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (G : Arr V n 1) (a b : Fin n) : V :=
  arrOf V n 1 G (fun _ => (a, b))

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem isDer_trivial {n : ℕ} (ε : Fin n → Bool) :
    IsDer ε (fun _ : Matrix (Fin n) (Fin n) ℂ => ContinuousLinearMap.id ℂ ℂ) ⊤ (fun _ _ => 0) := by
  unfold IsDer
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    simp
  · intro a b x y
    simp
  · intro X _ w
    simpa using hasDerivAt_const (0 : ℝ) (w : ℂ)
  · intro v y g₀ _
    exact ⟨Set.univ, fun _ => ⟪y, (v : ℂ)⟫_ℂ, isOpen_univ, Set.mem_univ _, contDiffOn_const,
      fun _ _ _ => rfl⟩

namespace StdDer

def act {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :=
  (stdRep y).toLinearMap.restrict (fun _ _ => Submodule.mem_top)

theorem act_coe {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (v : (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))) :
    (act y v : EuclideanSpace ℂ (Fin n)) = stdRep y v := rfl

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem isDer (n : ℕ) :
    IsDer (allPos n) stdRep ⊤ (fun a b => act (Matrix.single a b 1)) := by
  have hmul : ∀ x y : Matrix (Fin n) (Fin n) ℂ, act x * act y = act (x * y) := by
    intro x y
    ext w : 1
    apply Subtype.ext
    simp [act_coe, stdRep, map_mul]
  have hsub : ∀ x y : Matrix (Fin n) (Fin n) ℂ, act x - act y = act (x - y) := by
    intro x y
    ext w : 1
    apply Subtype.ext
    simp [act_coe, stdRep, map_sub]
  have hzero : act (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
    ext w : 1
    apply Subtype.ext
    simp [act_coe, stdRep]
  unfold IsDer
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    have key : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
        (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
      by_cases hbc : b = c <;> by_cases hda : d = a
      · subst hbc hda
        simp
      · subst hbc
        simp [hda]
      · subst hda
        simp [hbc]
      · simp [hbc, hda]
    rw [hmul, hmul, hsub, key, ← hsub]
    split_ifs <;> simp [hzero]
  · intro a b x y
    have hs : sgn (allPos n) a b = 1 := by simp [sgn, allPos]
    have hadj : ContinuousLinearMap.adjoint (stdRep (Matrix.single a b (1 : ℂ))) = stdRep (Matrix.single b a 1) := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      simp [stdRep, ← map_star, Matrix.star_eq_conjTranspose]
    rw [hs, Submodule.coe_inner, Submodule.coe_inner, act_coe, act_coe, ← hadj,
      ContinuousLinearMap.adjoint_inner_right]
    simp
  · intro X _ w
    have hX : X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp [Matrix.smul_single]
    have hsum : ((∑ a, ∑ b, X a b • act (Matrix.single a b (1 : ℂ)) w : (⊤ : Submodule ℂ _)) :
        EuclideanSpace ℂ (Fin n)) = stdRep X w := by
      rw [Submodule.coe_sum]
      conv_rhs => rw [hX, stdRep, map_sum, _root_.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Submodule.coe_sum, map_sum, _root_.sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Submodule.coe_smul, act_coe, map_smul, _root_.smul_apply, stdRep]
    have hfun : (fun t : ℝ => stdRep (NormedSpace.exp ((t : ℂ) • X)) (w : EuclideanSpace ℂ (Fin n))) =
        fun t : ℝ => NormedSpace.exp ((t : ℂ) • stdRep X) (w : EuclideanSpace ℂ (Fin n)) := by
      funext t
      simp only [stdRep]
      have key : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (NormedSpace.exp ((t : ℂ) • X)) =
          NormedSpace.exp (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) ((t : ℂ) • X)) := by
        rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
        exact ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.map_tsum).trans
          (tsum_congr fun k => by
            change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) _ = _
            rw [map_smul, map_pow])
      rw [key, map_smul]
    have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • stdRep X))
        (NormedSpace.exp ((0 : ℂ) • stdRep X) * stdRep X) 0 := hasDerivAt_exp_smul_const _ _
    have h2 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • stdRep X) (w : EuclideanSpace ℂ (Fin n)))
        (stdRep X w) ((0 : ℝ) : ℂ) := by
      simpa using h1.clm_apply (hasDerivAt_const (0 : ℂ) (w : EuclideanSpace ℂ (Fin n)))
    have h3 := h2.scomp (0 : ℝ) Complex.ofRealCLM.hasDerivAt
    simp only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at h3
    rw [hsum, hfun]
    exact h3
  · intro v y g₀ _
    refine ⟨Set.univ, fun g => ⟪y, stdRep g (v : EuclideanSpace ℂ (Fin n))⟫_ℂ, isOpen_univ, Set.mem_univ _, ?_,
      fun _ _ _ => rfl⟩
    have hF : (fun g : Matrix (Fin n) (Fin n) ℂ => ⟪y, stdRep g (v : EuclideanSpace ℂ (Fin n))⟫_ℂ) =
        fun g => ∑ i, (starRingEnd ℂ) (y i) * ∑ j, g i j * (v : EuclideanSpace ℂ (Fin n)) j := by
      funext g
      simp [PiLp.inner_apply, stdRep_apply, mul_comm]
    rw [hF]
    apply ContDiff.contDiffOn
    exact ContDiff.sum fun i _ => contDiff_const.mul
      (ContDiff.sum fun j _ => (contDiff_apply_apply ℝ ℂ i j).mul contDiff_const)

example {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (f : Fin n → Fin n → V) (a b : Fin n) :
    at1 (arrTo V n 1 (fun α => f (α 0).1 (α 0).2)) a b = f a b := rfl

end StdDer

end GlobalTheory.Jet
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

variable (D : D7) (large₂ : SizeData₂ D)

def HypZ (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ StandingNumericalData D C0 ∧ 1 ≤ C0

def MomIn (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (a : Fin (D.R.rS + 1)) (q : ℕ), (q : ℝ) ≤ Cq * (D.R.rS : ℝ) ^ 3 →
        ∫⁻ x, ENNReal.ofReal (lA D.R.k D.R.rS W.z (Matrix.of x) a ^ (2 * q)) *
            (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤
          ENNReal.ofReal (large₂.sc.b ^ (2 * C * D.R.m * q)) * l2SG W.νS A.Φ

def SchurSt (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ A : LocS W, GoodS D (lamD D τ) A →
      ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
        MMv D w w' A μsec ≤
          ENNReal.ofReal ((Tr D w * Tr D w') ^ (D.R.k - 1) *
            ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ) * volUn D.R.r * volUn (D.R.k - 1) /
              (A.deg * volUn D.R.k ^ 2 * (2 * D.host.v) ^ (2 * D.R.rS * D.R.k))) *
            large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2))

def ABSr (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S →
      ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR →
        DminN W.z W.z' γ D.R.rS ≠ 0 →
          Integrable (fun x => (innerSL ℂ (S.Φ' (Matrix.of x))).smulRight (S.Φ (γ * Matrix.of x))) νR ∧
          ‖S.J νR γ‖ ≤ lossP large₂.sc.b C D.R.m W.z W.z' γ p *
            (C / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) *
            (‖DminN W.z W.z' γ D.R.rS‖ ^ (D.R.k - 2 - D.R.rS))⁻¹

def DegVand : Prop :=
  ∀ (W : LocW D.R.k D.R.rS) (l₁ l₂ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A₁ A₂ : LocS W), GoodS D l₁ A₁ → GoodS D l₂ A₂ →
    A₂.deg * Formalism.MainNotions.S.vand l₁ = A₁.deg * Formalism.MainNotions.S.vand l₂

def LocIn (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ W, HypTT D w w' → GoodW D τ w w' θ W → ∀ A : LocS W, GoodS D (lamD D τ) A →
    MultOne W.z (psiS D W.z) A.σ W.π ∧ MultOne W.z' (psiS D W.z') A.σ W.π' ∧
      Decay A.σ (DD A.σ A.v0) (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 5)

def Big (Cl m₀ : ℝ) : Prop := D.host.rdE ≤ large₂.sc.b ∧ 1 ≤ Cl * D.R.m ∧ m₀ ≤ D.R.m

def BSch (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → ∀ A : LocS W, GoodS D (lamD D τ) A → 0 < Tr D w →
    ∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
      l2SG W.νS (fun g => A.B (A.σ g v)) * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 = l2SG W.νS A.Φ * (‖v‖₊ : ℝ≥0∞) ^ 2

def Sizes (Cl Cg CT : ℝ) : Prop :=
  1 < large₂.sc.L ∧ Real.log large₂.sc.b = large₂.sc.L ∧ Real.exp 1 < large₂.sc.b ∧ D.R.m = 2 * D.R.rS + 2 ∧
    D.R.r = 2 * D.R.rS + D.R.k + 1 ∧ Fintype.card D.what₂.Tau = D.R.f ∧ Cl ≤ D.R.m ∧ D.R.m ^ 4 ≤ D.R.k ∧
    1 ≤ D.host.v ∧ D.host.rdE = 2 * D.host.v ∧ D.host.ka = Real.pi / D.host.v ∧ 2 * D.host.v ≤ large₂.sc.b ∧
    1 ≤ gg D ∧ gg D ≤ large₂.sc.b ^ (2 * Cg) ∧ 8 ≤ Cg ∧ (D.R.k : ℝ) ≤ large₂.sc.b ^ Cg ∧
    (∀ w, Tr D w ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) ∧ (∀ w τ, 0 < Formalism.MainNotions.S.vand (uS D w τ) ∧ 0 < Tcrit D w τ) ∧
    ∀ τ (a c : Fin (2 * D.R.rS + D.R.k + 1)), a < c →
      Cl * D.R.k * (D.R.m : ℝ) ^ 4 < lamD D τ a - lamD D τ c

end GlobalTheory.Amp
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsSatFlagOne
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas.SatModel

open Formalism.MainNotions.S GlobalTheory.Count

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → E) (hy : y ∈ Submodule.span E (Λ : Set (Fin n → E))) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h
    · rw [mul_smul]; exact Λ.smul_mem _ h'
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb1 : algebraMap (𝓞 E) E b ≠ 0 := by simpa using hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have : (b * d) • (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b) • x = a • d • x := by
      rw [← algebraMap_smul E (b * d), ← algebraMap_smul E a, ← algebraMap_smul E d, smul_smul, smul_smul]
      congr 1
      rw [map_mul]; field_simp
    rw [this]; exact Λ.smul_mem _ h

theorem span_inf {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (W : Submodule E (Fin n → E)) :
    Submodule.span E ((Λ ⊓ W.restrictScalars (𝓞 E) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = W := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun y hy => hy.2
  · intro y hy
    obtain ⟨d, hd, h⟩ := exists_smul_mem Λ y (hΛ ▸ Submodule.mem_top)
    have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd
    have h1 : d • y ∈ Submodule.span E
        ((Λ ⊓ W.restrictScalars (𝓞 E) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      Submodule.subset_span ⟨h, (W.restrictScalars (𝓞 E)).smul_mem d hy⟩
    have h2 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ h1
    rwa [← algebraMap_smul E d, smul_smul, inv_mul_cancel₀ hd1, one_smul] at h2

theorem isSatFlag_inf (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hΛ : Submodule.span I.E (Λ : Set (Fin I.n → I.E)) = ⊤) {a : ℕ} (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule I.E (Fin I.n → I.E)) (h0 : W 0 = ⊥) (hm : Monotone W)
    (hr : ∀ i : Fin a, Module.finrank I.E (W i.succ) = Module.finrank I.E (W i.castSucc) + j i)
    (hi : ∀ x ∈ W (Fin.last a), ∀ y ∈ W (Fin.last a), Formalism.UG.hform (starRingEnd I.E) I.J x y = 0) :
    IsSatFlag I Λ j fun i => Λ ⊓ (W i).restrictScalars (𝓞 I.E) := by
  refine ⟨by simp [h0], fun i k h => inf_le_inf_left _ fun y hy => hm h hy, fun i => ?_, fun i y => ?_,
    fun x hx y hy => hi x hx.2 y hy.2⟩
  · unfold Formalism.HN.rkK
    rw [span_inf Λ hΛ, span_inf Λ hΛ, hr]
  · rw [span_inf Λ hΛ]; rfl

theorem exists_isSatFlag_one (I : AutInst) (x : Fin I.n → I.E) (hx : x ≠ 0)
    (hi : Formalism.UG.hform (starRingEnd I.E) I.J x x = 0) :
    ∃ S, IsSatFlag I I.L (fun _ : Fin 1 => 1) S := by
  refine ⟨_, isSatFlag_inf I I.L I.L_span _ ![⊥, I.E ∙ x] rfl ?_ ?_ ?_⟩
  · intro i k h
    fin_cases i <;> fin_cases k <;> simp_all
  · intro i
    fin_cases i
    change Module.finrank I.E (I.E ∙ x) = Module.finrank I.E (⊥ : Submodule I.E (Fin I.n → I.E)) + 1
    rw [finrank_span_singleton hx, finrank_bot]
  · intro y hy z hz
    change y ∈ I.E ∙ x at hy
    change z ∈ I.E ∙ x at hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have : Formalism.UG.hform (starRingEnd I.E) I.J (c • x) (d • x) =
        starRingEnd I.E c * d * Formalism.UG.hform (starRingEnd I.E) I.J x x := by
      simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [this, hi, mul_zero]

theorem cIw_one_one : cIw 1 1 (fun _ : Fin 1 => 1) = Real.pi := by
  have h : (2 : ℝ) ^ (-(1 / 2 : ℝ)) * 2 = 2 ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one (by norm_num)]; norm_num
  have hp : (2 : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) * 2 ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have e : cIw 1 1 (fun _ : Fin 1 => 1) =
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * Real.pi * (2 * Real.pi)) / (2 * Real.pi * 2 ^ (1 / 2 : ℝ)) := by
    simp [cIw, dimN, volU, sphV, Finset.filter_singleton]
  rw [e, div_eq_iff (by positivity)]
  calc _ = (2 : ℝ) ^ (-(1 / 2 : ℝ)) * 2 * (2 * Real.pi * Real.pi) := by ring
    _ = _ := by rw [h]; ring

theorem volU_pos (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  have := Real.pi_pos
  refine mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem cIw_pos (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : 0 < cIw p q j := by
  unfold cIw
  have := volU_pos
  refine div_pos (mul_pos (by positivity) (mul_pos (this _) (this _)))
    (mul_pos (mul_pos (Finset.prod_pos fun i _ => mul_pos (this _) (by positivity)) (this _)) (this _))

theorem rankFac_eq (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) :
    rankFac E (M + 1) = Formalism.HermitianLatticesTheory.massRatioRightSide E (M + 1) *
      (2 * Real.pi ^ (M + 1) / (M.factorial : ℝ) * 2 ^ M) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  have hv : 0 < Formalism.HermitianLatticesTheory.vInv E := by
    unfold Formalism.HermitianLatticesTheory.vInv
    have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
    positivity
  unfold rankFac Formalism.HermitianLatticesTheory.massRatioRightSide
  generalize Formalism.HermitianLatticesTheory.vInv E = v at hv
  generalize Formalism.HermitianLatticesTheory.fDeg E = f
  have hπ := Real.pi_pos
  have e1 : ((M.factorial : ℝ) * (v / Real.pi) ^ (M + 1)) * (2 * Real.pi ^ (M + 1) / (M.factorial : ℝ) * 2 ^ M)
      = (2 * v) ^ (M + 1) := by
    have : (M.factorial : ℝ) ≠ 0 := by positivity
    rw [div_pow, mul_pow]; field_simp; ring
  have e2 : (2 * v) ^ ((f : ℝ) * (((M + 1 : ℕ) : ℝ) - 1 / 2)) =
      ((2 * v) ^ (M + 1)) ^ f / Real.sqrt ((2 * v) ^ f) := by
    rw [Real.sqrt_eq_rpow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), ← Real.rpow_sub (by positivity)]
    congr 1; push_cast; ring
  rw [e2, ← e1, mul_pow, Nat.add_sub_cancel]
  ring

theorem finrank_span_image {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (s : Set (Fin n → E)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s)) =
      Module.finrank E (Submodule.span E s) := by
  letI : Algebra E ℂ := φ.toAlgebra
  obtain ⟨t, hts, hsp, hli⟩ := exists_linearIndependent E s
  haveI : Finite t := hli.finite
  haveI : Fintype t := Fintype.ofFinite t
  have hli' : LinearIndependent ℂ fun i : t => (algebraMap E ℂ ∘ (i : Fin n → E)) :=
    linearIndependent_algebraMap_comp_iff.2 hli
  have h1 := finrank_span_eq_card hli
  have h2 := finrank_span_eq_card hli'
  rw [Subtype.range_coe, hsp] at h1
  rw [h1, ← h2]
  suffices hs : Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s) =
      Submodule.span ℂ (Set.range fun i : t => (algebraMap E ℂ ∘ (i : Fin n → E))) by rw [hs]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span E t := hsp ▸ Submodule.subset_span hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    | zero =>
      have : (fun l : Fin n => φ ((0 : Fin n → E) l)) = 0 := by ext; simp
      simp only [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun l : Fin n => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext; simp
      simp only [this]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have : (fun l : Fin n => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext; simp
      simp only [this]; exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨i, hts i.2, rfl⟩

theorem finrank_flagAt (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (v : InfinitePlace I.F) (i : Fin (a + 1)) :
    Module.finrank ℂ (flagAt I S v i) = Formalism.HN.rkK (S i) := by
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hinj : Function.Injective (Matrix.mulVecLin (I.P v)⁻¹) :=
    Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
  have : flagAt I S v i = (Submodule.span ℂ ((fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S i : Set _))).map
      (Matrix.mulVecLin (I.P v)⁻¹) := by
    rw [Submodule.map_span, Set.image_image]; rfl
  rw [this, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, finrank_span_image]
  rfl

theorem isIsoFlag_flagAt (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (h : IsSatFlag I Λ j S) (v : InfinitePlace I.F) :
    IsIsoFlag (I.ε v) j (flagAt I S v) := by
  obtain ⟨h0, hm, hr, -, hi⟩ := h
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  refine ⟨by simp [flagAt, h0]; exact Matrix.mulVec_zero _, fun i k hik => Submodule.span_mono (Set.image_mono (hm hik)), fun i => ?_, ?_⟩
  · rw [finrank_flagAt, finrank_flagAt, hr]
  · have key : ∀ x ∈ S (Fin.last a), ∀ y ∈ S (Fin.last a),
        star ((I.P v)⁻¹ *ᵥ fun l => I.φ v (x l)) ⬝ᵥ
          (Formalism.REAL.Jm (I.ε v) *ᵥ ((I.P v)⁻¹ *ᵥ fun l => I.φ v (y l))) = 0 := by
      intro x hx y hy
      rw [← I.P_spec v, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
      have h1 := congrArg (I.φ v) (hi x hx y hy)
      rw [map_zero] at h1
      rw [← h1]
      simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
        Matrix.map_apply, starRingEnd_apply, I.cm.cmUnram.2.1, mul_assoc]
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨y, hy, rfl⟩ := hy; exact key x hx y hy
      | zero => simp
      | add y z _ _ h1 h2 => rw [Matrix.mulVec_add, dotProduct_add, h1, h2, add_zero]
      | smul c y _ h1 => rw [Matrix.mulVec_smul, dotProduct_smul, h1, smul_zero]
    | zero => simp
    | add x z _ _ h1 h2 => rw [star_add, add_dotProduct, h1, h2, add_zero]
    | smul c x _ h1 => rw [star_smul, smul_dotProduct, h1, smul_zero]

end GlobalTheory.FlagMeas.SatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.Deep

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

def frame (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  I.P v * uMat (x.1 v)

def crd (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (y : Fin I.n → I.E) : EuclideanSpace ℂ (Fin I.n) :=
  WithLp.toLp 2 ((frame I x v)⁻¹ *ᵥ fun i => I.φ v (y i))

def matX (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (Y : Matrix (Fin I.n) (Fin I.n) I.E) :
    Matrix (Fin I.n) (Fin I.n) ℂ :=
  (frame I x v)⁻¹ * Y.map (I.φ v) * frame I x v

def spanX (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin I.n)) :=
  Submodule.span ℂ (crd I x v '' (S : Set (Fin I.n → I.E)))

def act {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (y : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (M *ᵥ y.ofLp)

def IsProjOn {n : ℕ} (π : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (EuclideanSpace ℂ (Fin n))) : Prop :=
  πᴴ = π ∧ (∀ y, act π y ∈ W) ∧ ∀ y ∈ W, act π y = y

def SatX (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S

def SizesGe (I : AutInst) (x : I.GA) (B B' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo : ℝ) : Prop :=
  ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), B' < N → N ≤ B → lo ≤ Formalism.HN.sizeQ (bas I) (frm I x) N B'

def SizesLe (I : AutInst) (x : I.GA) (A A' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ) : Prop :=
  ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), A' ≤ N →
    Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A N → N ≠ A →
      Formalism.HN.sizeQ (bas I) (frm I x) A N ≤ hi

def Maps (I : AutInst) (Y : Matrix (Fin I.n) (Fin I.n) I.E) (A B : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  ∀ y ∈ A, Y *ᵥ y ∈ B

def omega (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) (ρ : ℝ) : Set I.GA :=
  {y | y.2 = x.2 ∧ ∃ A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ,
    (∀ v, Formalism.REAL.inG (I.ε v) (A v) ∧ Formalism.REAL.inG (I.ε v) (Z v)) ∧
    Real.sqrt (∑ v, Formalism.REAL.hs (A v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v)) ≤ ρ ∧
    (∀ v, uMat (y.1 v) = uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧
    ∀ s t : ℝ, ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA W ∧
      ∀ v, uMat (m v) * uMat (x.1 v) =
        uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • A v) * NormedSpace.exp ((t : ℂ) • Z v)}

def IsReps (B : RowsAut) (T : B.Hs →L[ℂ] B.I.L2 B.μf B.fund) (Fr : B.Hs → B.I.GA → ℂ) : Prop :=
  ∀ P : ℕ, ∀ u ∈ VP B P, GlobalTheory.Dec.IsContRep B (T u) (Fr u) ∧
    (∀ k ∈ B.I.Kg B.g, ∀ y, Fr u (y * (1, k)) = Fr u y) ∧
    ∀ (E : gInf B) (y : B.I.GA),
      HasDerivAt (fun t : ℝ => Fr u (y * ((fun v => expU (t • E v)), 1))) (Fr (dAct B E u) y) 0

def RepsExist : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → 1 ≤ B.g →
    ∀ T ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u) →
      ∃ Fr, IsReps B T Fr

def vv (B : RowsAut) {D : ℕ} (Fr : Fin D → B.Hs → B.I.GA → ℂ) (u : B.Hs) (y : B.I.GA) :
    EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 fun i => Fr i u y

end GlobalTheory.Deep
end
end

