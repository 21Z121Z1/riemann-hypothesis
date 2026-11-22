import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0018
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassClassEqWeightCount
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0155
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionBlockDiagEqHarishChandraGelfan
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantIntegrable
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory.Count.Majorant

theorem decE_le_exp (q : ℕ) (hq : 1 ≤ q) (h d : ℝ) (hh : 0 ≤ h) (hd : 0 ≤ d) :
    decE q h d ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q) * d)) := by
  have hs : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
  have hm : d / Real.sqrt q - 1 ≤ min (2 * d ^ 2) (d / Real.sqrt q) := by
    have h1 : d / Real.sqrt q ≤ d := div_le_self hd hs
    exact le_min (by nlinarith [sq_nonneg (d - 1 / 4)]) (by linarith)
  have key : h / (8 * Real.sqrt q) * d = h / 8 * (d / Real.sqrt q) := by
    rw [div_mul_eq_mul_div, div_mul_div_comm]
  have hmul := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ h / 8)
  unfold GlobalTheory.Count.decE
  rw [← Real.exp_add, Real.exp_le_exp, key]
  nlinarith [hmul]

theorem dOp_eq_zero {n : ℕ} (ε : Fin n → Bool) (h0 : rkR ε = 0) (g : UJ ε) : dOp (uMat g) = 0 := by
  have hall : (∀ a, ε a = false) ∨ (∀ a, ε a = true) := by
    unfold GlobalTheory.Count.rkR at h0
    rcases Nat.min_eq_zero_iff.mp h0 with h1 | h1
    · left
      intro a
      have ha : a ∉ univ.filter (fun a => ε a = true) := by
        rw [Finset.card_eq_zero.mp h1]; simp
      simpa using ha
    · right
      intro a
      have ha : a ∉ univ.filter (fun a => ε a = false) := by
        rw [Finset.card_eq_zero.mp h1]; simp
      simpa using ha
  have hJ : Jm ε = 1 ∨ Jm ε = -1 := by
    rcases hall with hf | ht
    · right
      ext i j
      by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, hf, hij]
    · left
      ext i j
      by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, ht, hij]
  have hg : inUJ ε (uMat g) := g.2
  have hu : uMat g ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    unfold inUJ at hg
    rcases hJ with hJ | hJ <;> rw [hJ] at hg <;> simpa using hg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold GlobalTheory.Count.dOp
    have hle : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (uMat g))‖ ≤ 0 :=
      ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => by simp [EuclideanSpace.norm_eq]
    rw [le_antisymm hle (norm_nonneg _), Real.log_zero]
  · have hP0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by simp [inP, inG]
    obtain ⟨hb0, hb1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn hu hP0
    rw [NormedSpace.exp_zero, mul_one] at hb0 hb1
    have hs0 : hs (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [hs]
    rw [hs0, Real.sqrt_zero] at hb1
    nlinarith [Real.sqrt_pos.mpr (two_pos : (0 : ℝ) < 2)]

theorem majorant_integrable : ∀ (n : ℕ) (ε : Fin n → Bool) (h s : ℝ), 0 ≤ h → (rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h) → Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) := by
  intro n ε h s hh hcase
  obtain ⟨C, -, hC⟩ := GlobalTheory.T.haar_ball_growth_unitaryJ n ε
  have hcont : Continuous (fun g : UJ ε => dOp (uMat g)) :=
    (GlobalTheory.Count.Cartan.cartan_distances n ε).2.2.2.2
  have hmeas : Measurable (fun g : UJ ε => dOp (uMat g)) := hcont.measurable
  have hdec : Continuous (decE (rkR ε) h) := by
    unfold GlobalTheory.Count.decE
    fun_prop
  have hint_meas : AEStronglyMeasurable
      (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) :=
    ((hdec.comp hcont).mul (Real.continuous_exp.comp (continuous_const.mul hcont))).aestronglyMeasurable
  by_cases hq : rkR ε = 0
  · have hz : ∀ g : UJ ε, dOp (uMat g) = 0 := fun g => dOp_eq_zero ε hq g
    have hI := GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε)
      (4 * n * rkR ε + 1) C hmeas (fun g => by simp [hz g]) hC (by linarith)
    refine hI.congr (ae_of_all _ fun g => ?_)
    simp [hz g, GlobalTheory.Count.decE]
  · have hq1 : 1 ≤ rkR ε := Nat.one_le_iff_ne_zero.mpr hq
    have hlt : 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h := hcase.resolve_left hq
    have hrk : rkR ε ≤ n := by
      unfold GlobalTheory.Count.rkR
      exact (min_le_left _ _).trans ((Finset.card_le_univ _).trans (Fintype.card_fin n).le)
    have hn : 1 ≤ n := hq1.trans hrk
    have hpos : ∀ g : UJ ε, 0 ≤ dOp (uMat g) := fun g =>
      ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).1
    have hsq : 0 < Real.sqrt (rkR ε) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hq)
    have hab : (4 * n * rkR ε : ℝ) < h / (8 * Real.sqrt (rkR ε)) - s := by
      have : s + 4 * n * rkR ε < h / (8 * Real.sqrt (rkR ε)) :=
        (lt_div_iff₀ (by linarith : (0 : ℝ) < 8 * Real.sqrt (rkR ε))).mpr (by linarith)
      linarith
    have hI := (GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε)
      (h / (8 * Real.sqrt (rkR ε)) - s) C hmeas hpos hC hab).const_mul (Real.exp (h / 8))
    refine hI.mono' hint_meas (ae_of_all _ fun g => ?_)
    have hd := hpos g
    have hE := decE_le_exp (rkR ε) hq1 h (dOp (uMat g)) hh hd
    have hnn : 0 ≤ decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g)) := by
      unfold GlobalTheory.Count.decE
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))
        ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt (rkR ε)) * dOp (uMat g))) *
            Real.exp (s * dOp (uMat g)) := mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le
      _ = Real.exp (h / 8) * Real.exp (-((h / (8 * Real.sqrt (rkR ε)) - s) * dOp (uMat g))) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

end GlobalTheory.Count.Majorant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassClassEqWeightCountStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_class_eq_weight_count_alt : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat f f' ∈ c1 → (∃ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t ∧ H.Zhat t.f t.f' ∈ c1) → ∃ w : ℝ, 0 < w ∧ w ≤ P.Hp ^ (3 * (r + 1) ^ 2) ∧ (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : R.RT d.1, (if ¬ LocNG.BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (LocNG.mu P t.1) else 0)) = ENNReal.ofReal w * ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (({Λ | LocNG.IsTermOver P d.1 (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} : Set (Submodule M.L.O V)).encard : ℝ≥0∞) := by
  first | exact @GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count | exact GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count | (intros; apply GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassPairingClassBounds
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

theorem tsum_subtype_and_eq_ite {α : Type*} (S : Set α) (p q : α → Prop) (f : α → ℝ≥0∞)
    (h : ∀ t ∈ S, p t ↔ q t) :
    (∑' t : {t // t ∈ S ∧ p t}, f t.1) = ∑' t : S, (if q t.1 then f t.1 else 0) := by

  have hL : (∑' t : {t // t ∈ S ∧ p t}, f t.1) = ∑' t, ({t | t ∈ S ∧ p t} : Set α).indicator f t :=
    tsum_subtype {t | t ∈ S ∧ p t} f
  have hR : (∑' t : S, (if q t.1 then f t.1 else 0)) =
      ∑' t, S.indicator (fun t => if q t then f t else 0) t :=
    tsum_subtype S (fun t => if q t then f t else 0)
  rw [hL, hR]
  refine tsum_congr fun t => ?_
  by_cases hS : t ∈ S
  · have hpq := h t hS
    rw [Set.indicator_of_mem hS]
    by_cases hq : q t
    · rw [if_pos hq, Set.indicator_of_mem (show t ∈ {t | t ∈ S ∧ p t} from ⟨hS, hpq.2 hq⟩)]
    · rw [if_neg hq]
      exact Set.indicator_apply_eq_zero.mpr fun hm => absurd (hpq.1 hm.2) hq
  · rw [Set.indicator_apply_eq_zero.mpr fun hm => absurd hm.1 hS,
      Set.indicator_apply_eq_zero.mpr fun hm => absurd hm hS]

theorem mass_pairingClass_bounds : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), (∃ t0 : Term V M r, LocNG.IsTermOver P d0 t0) → ∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat t.f t.f' ∈ c1 → ∀ g : ℝ≥0∞, g = (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : R.RT d.1, (if ¬ LocNG.BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (LocNG.mu P t.1) else 0)) → 0 < g ∧ g ≠ ⊤ ∧ (P.PrimeTo → LocNG.nn R d0 = g) ∧ LocNG.nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hdim hrel R d0 hd0 d t hdt Y0 c1 hc1 ht g hg
  obtain ⟨t0, ht0⟩ := hd0

  let Cl : Term V M r → Prop := fun t' => ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t'.f j = ∑ i, A i j • s (t.f i)) ∧ ∀ j, t'.f' j = ∑ i, A' i j • s (t.f' i)

  have hCl : ∀ (d' : LocNG.Datum P) (t' : Term V M r), LocNG.IsTermOver P d' t' →
      (H.Zhat t'.f t'.f' ∈ c1 ↔ Cl t') := fun d' t' h' =>
    GlobalTheory.T.term_over_relation_uniqueness M hM H r k P hdim hrel d d' t t' hdt h' Y0 c1 hc1 ht

  have hg' : g = ∑' d' : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d'.1) *
      ∑' t' : {t' // t' ∈ R.RT d'.1 ∧ ¬ LocNG.BBne (H := H) t' ∧ Cl t'},
        ENNReal.ofReal (LocNG.mu P t'.1) := by
    rw [hg]
    refine tsum_congr fun d' => ?_
    congr 1
    have e := tsum_subtype_and_eq_ite (R.RT d'.1) (fun t' => ¬ LocNG.BBne (H := H) t' ∧ Cl t')
      (fun t' => ¬ LocNG.BBne (H := H) t' ∧ H.Zhat t'.f t'.f' ∈ c1)
      (fun t' => ENNReal.ofReal (LocNG.mu P t'))
      (fun t' ht' => and_congr_right fun _ => (hCl d'.1 t' ((R.hRT d'.1).1 ht')).symm)
    convert e.symm
  obtain ⟨hne, hle, hprime, hpos⟩ :=
    GlobalTheory.T.hermitian_total_mass_le_generic_mass M hM H r k P hk hdim hrel R d0 d t hdt Cl (fun _ => Iff.rfl) g hg'
  exact ⟨pos_iff_ne_zero.mpr (hpos ⟨t0, ht0⟩), hne, hprime, hle⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.MeanDual

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def invT (g : MatInf E j) : MatInf E j := fun w a b => (Matrix.of (g w))⁻¹ b a

def trDual (Λ : Submodule (𝓞 E) (Fin j → E)) : Submodule (𝓞 E) (Fin j → E) where
  carrier := {y | ∀ x ∈ Λ, ∃ z : ℤ, Algebra.trace ℚ E (x ⬝ᵥ y) = 2 * (z : ℚ)}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z, hz⟩ := ha x hx
    obtain ⟨z', hz'⟩ := hb x hx
    exact ⟨z + z', by rw [dotProduct_add, map_add, hz, hz']; push_cast; ring⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c y hy x hx
    obtain ⟨z, hz⟩ := hy (c • x) (Λ.smul_mem c hx)
    refine ⟨z, ?_⟩
    rw [← hz, dotProduct_smul, smul_dotProduct]

theorem mem_trDual {Λ : Submodule (𝓞 E) (Fin j → E)} {y : Fin j → E} :
    y ∈ trDual E j Λ ↔ ∀ x ∈ Λ, ∃ z : ℤ, Algebra.trace ℚ E (x ⬝ᵥ y) = 2 * (z : ℚ) := Iff.rfl

theorem of_invT (g : MatInf E j) (w : InfinitePlace E) :
    Matrix.of (invT E j g w) = ((Matrix.of (g w))⁻¹)ᵀ := rfl

theorem of_mul (g h : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((g * h) w) = Matrix.of (g w) * Matrix.of (h w) := rfl

theorem matInf_ext {g h : MatInf E j} (H : ∀ w, Matrix.of (g w) = Matrix.of (h w)) : g = h :=
  funext fun w => Matrix.of.injective (H w)

theorem detNorm_pos_iff (g : MatInf E j) :
    0 < detNorm E j g ↔ ∀ w, (Matrix.of (g w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

theorem invT_mul (g h : MatInf E j) : invT E j (g * h) = invT E j g * invT E j h := by
  apply matInf_ext
  intro w
  rw [of_invT, of_mul, of_mul, of_invT, of_invT, Matrix.mul_inv_rev, Matrix.transpose_mul]

theorem detNorm_invT_pos_iff (g : MatInf E j) :
    0 < detNorm E j (invT E j g) ↔ 0 < detNorm E j g := by
  simp only [detNorm_pos_iff, of_invT, Matrix.det_transpose, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', ne_eq, inv_eq_zero]

theorem invT_invT {g : MatInf E j} (hg : 0 < detNorm E j g) : invT E j (invT E j g) = g := by
  apply matInf_ext
  intro w
  rw [of_invT, of_invT, ← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 ((detNorm_pos_iff E j g).1 hg w))]

theorem detNorm_mul (g h : MatInf E j) : detNorm E j (g * h) = detNorm E j g * detNorm E j h := by
  unfold detNorm
  simp only [of_mul, Matrix.det_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]

theorem continuous_detNorm :
    Continuous (fun g : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j g) := by
  unfold detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  refine Continuous.pow (Continuous.norm ?_) 2
  exact Continuous.matrix_det (A := fun g : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (g w))
    (continuous_apply w)

theorem measurableSet_detNorm_pos : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
  (isOpen_lt continuous_const (continuous_detNorm E j)).measurableSet

end GlobalTheory.MeanDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulLeft
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.HaarLeftInv

def leftMat {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) :
    Matrix (Fin j) (Fin j) ℂ →ₗ[ℝ] Matrix (Fin j) (Fin j) ℂ where
  toFun T := A * T
  map_add' S T := Matrix.mul_add _ _ _
  map_smul' c T := by simp

theorem det_leftMat {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (leftMat A) = (‖A.det‖ ^ 2) ^ j := by
  have h := (GlobalTheory.TwoSidedJac.real_jacobians).1 j j A 1 (leftMat A) (fun T => by
    show A * T = A * T * 1
    rw [Matrix.mul_one])
  rw [h, Matrix.det_one, norm_one, one_pow, mul_one, ← pow_mul]

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def leftMul (a : MatInf E j) :
    (InfinitePlace E → Fin j → Fin j → ℂ) →ₗ[ℝ] (InfinitePlace E → Fin j → Fin j → ℂ) :=
  LinearMap.pi fun w => (show (Fin j → Fin j → ℂ) →ₗ[ℝ] (Fin j → Fin j → ℂ) from
    leftMat (Matrix.of (a w))).comp (LinearMap.proj w)

theorem det_leftMul (a : MatInf E j) : LinearMap.det (leftMul E j a) = detNorm E j a ^ j := by
  calc LinearMap.det (leftMul E j a)
      = ∏ w, LinearMap.det (leftMat (Matrix.of (a w))) := LinearMap.det_pi _
    _ = ∏ w, (‖(Matrix.of (a w)).det‖ ^ 2) ^ j := by simp only [det_leftMat]
    _ = (∏ w, ‖(Matrix.of (a w)).det‖ ^ 2) ^ j := Finset.prod_pow _ _ _
    _ = detNorm E j a ^ j := by rfl

theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  unfold detNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl
  rw [hw, Matrix.det_mul, norm_mul, mul_pow]

theorem continuous_detNorm :
    Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x) := by
  unfold detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  exact ((Continuous.matrix_det (continuous_apply w)).norm).pow 2

theorem isAddHaar_volume : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure := by
  have : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem measurePreserving_mul_left : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (a : MatInf E j), 0 < detNorm E j a → MeasurableEmbedding (fun g : MatInf E j => a * g) ∧ MeasurePreserving (fun g : MatInf E j => a * g) (haarGL E j) (haarGL E j) := by
  intro E _ _ j a ha
  have : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    isAddHaar_volume E j
  have hdet0 : LinearMap.det (leftMul E j a) ≠ 0 := by
    rw [det_leftMul]
    exact pow_ne_zero _ ha.ne'
  have hemb : MeasurableEmbedding ⇑(leftMul E j a) :=
    ((LinearMap.toContinuousLinearMap (leftMul E j a)).toContinuousLinearEquivOfDetNeZero
      hdet0).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpos : 0 < (detNorm E j a)⁻¹ ^ j := pow_pos (inv_pos.mpr ha) j
  have hmap : Measure.map (leftMul E j a) (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) =
      ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, det_leftMul, ← inv_pow,
      abs_of_pos hpos]
  have hc0 : ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have hctop : ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hρ : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ =>
      ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((continuous_detNorm E j).measurable.inv).pow_const j).ennreal_ofReal
  have hρf : ∀ x : InfinitePlace E → Fin j → Fin j → ℂ,
      ENNReal.ofReal ((detNorm E j (leftMul E j a x))⁻¹ ^ j) =
        ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) * ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    intro x
    have hx : detNorm E j (leftMul E j a x) = detNorm E j a * detNorm E j x := detNorm_mul E j a x
    rw [hx, mul_inv, mul_pow, ENNReal.ofReal_mul hpos.le]
  have hV : Measure.map (leftMul E j a)
      ((volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).withDensity
        fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)) =
      (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).withDensity
        fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, withDensity_apply _ (hemb.measurable hs),
      withDensity_apply _ hs]
    calc ∫⁻ x in ⇑(leftMul E j a) ⁻¹' s, ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)
        = (ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j))⁻¹ *
            ∫⁻ x in ⇑(leftMul E j a) ⁻¹' s,
              ENNReal.ofReal ((detNorm E j (leftMul E j a x))⁻¹ ^ j) := by
          simp_rw [hρf]
          rw [lintegral_const_mul' _ _ hctop, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop,
            one_mul]
      _ = (ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j))⁻¹ *
            ∫⁻ y in s, ENNReal.ofReal ((detNorm E j y)⁻¹ ^ j) ∂(Measure.map (leftMul E j a) volume) := by
          rw [setLIntegral_map hs hρ hemb.measurable]
      _ = ∫⁻ y in s, ENNReal.ofReal ((detNorm E j y)⁻¹ ^ j) := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  exact ⟨hemb, hemb.measurable, hV⟩

end GlobalTheory.HaarLeftInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingTriangularShear
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem measurePreserving_layer_shear (d : ℕ) (p : Fin d → Prop) [DecidablePred p]
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hf : Measurable f)
    (h : ∀ x y i, ¬ p i → (∀ k, p k → x k = y k) → f x i = f y i) :
    MeasurePreserving (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i)
      (volume : Measure (Fin d → ℝ)) volume := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p with he
  have he_mp : MeasurePreserving e volume volume :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p

  let G : (Subtype p → ℝ) → ({i // ¬ p i} → ℝ) := fun a i => f (e.symm (a, 0)) i
  have hG : Measurable G := by
    refine measurable_pi_lambda _ (fun i => ?_)
    exact (measurable_pi_apply (i : Fin d)).comp
      (hf.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))

  have hΨ : MeasurePreserving
      (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (f := id) (g := fun a b => b + G a)
      (MeasurePreserving.id volume) (measurable_snd.add (hG.comp measurable_fst))
      (Filter.Eventually.of_forall fun a => (measurePreserving_add_right volume (G a)).map_eq)
  have key : (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i) =
      e.symm ∘ (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1)) ∘ e := by
    funext x i
    have hx : ∀ k, p k → x k = e.symm ((e x).1, 0) k := fun k hk => by simp [e, hk]
    by_cases hi : p i
    · simp [e, hi]
    · simp [e, G, hi, h x _ i hi hx]
  rw [key]
  exact (MeasurePreserving.symm e he_mp).comp (hΨ.comp he_mp)

theorem measurePreserving_triangular_shear (d : ℕ) (deg : Fin d → ℕ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hf : Measurable f)
    (h : ∀ x y i, (∀ k, deg k < deg i → x k = y k) → f x i = f y i) :
    MeasurePreserving (fun x => x + f x) (volume : Measure (Fin d → ℝ)) volume := by

  let U : ℕ → (Fin d → ℝ) → (Fin d → ℝ) := fun n x i => if n ≤ deg i then x i + f x i else x i
  have hS : ∀ n, MeasurePreserving
      (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) volume volume :=
    fun n => measurePreserving_layer_shear d (fun i => deg i ≠ n) f hf
      (fun x y i hi hxy => h x y i (fun k hk => hxy k (by omega)))
  have hstep : ∀ n, U n =
      (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) ∘ U (n + 1) := by
    intro n
    funext x i
    by_cases hin : deg i = n
    · have hfx : f (U (n + 1) x) i = f x i :=
        h _ _ i (fun k hk => by simp only [U]; rw [if_neg (by omega)])
      simp only [Function.comp_apply, hfx]
      simp only [U]
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    · simp only [Function.comp_apply, U]
      rw [if_pos hin]
      by_cases h2 : n ≤ deg i
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  have hN : ∀ n, Finset.univ.sup deg < n → U n = id := by
    intro n hn
    funext x i
    have hi : deg i ≤ Finset.univ.sup deg := Finset.le_sup (Finset.mem_univ i)
    simp only [U, id]
    rw [if_neg (by omega)]
  have hU : ∀ k n, Finset.univ.sup deg < n + k → MeasurePreserving (U n) volume volume := by
    intro k
    induction k with
    | zero =>
      intro n hn
      rw [hN n (by omega)]
      exact MeasurePreserving.id _
    | succ k ih =>
      intro n hn
      rw [hstep n]
      exact (hS n).comp (ih (n + 1) (by omega))
  have h0 : U 0 = fun x => x + f x := by
    funext x i
    simp [U]
  rw [← h0]
  exact hU (Finset.univ.sup deg + 1) 0 (by omega)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionBlockDiagEqHarishChandraGelfanStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicInduction_blockDiag_eq_harishChandra_gelfandGraev : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i k : ℕ) (ρ : Gn g i → ℂ), i ≤ k → IsClass ρ → ∀ h : Gn g k, indR ψ i (k + 1) ρ (diag1 h (k + 1)) = hc i (k - i) ρ (gg ψ (k - i)) k h := by
  first | exact @GlobalTheory.GLm.indR_diag1_eq_hc_gg | exact GlobalTheory.GLm.indR_diag1_eq_hc_gg | (intros; apply GlobalTheory.GLm.indR_diag1_eq_hc_gg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHypsStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.momentPieriNumerics_of_sizeHyps : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ (τ : D.what₂.Tau) (w : D.what₂.Word) (U : ℕ → ℝ), (∀ i : Fin D.R.k, U (i.val + 1) = uS D w τ i) → Num D.R.k D.R.rS (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) ∧ GapCell D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) ∧ PI.BesselPeriodGGP.eps48 D.R.k D.R.rS = epsSH D.R := by
  first | exact @GlobalTheory.SizeNum.num_of_size | exact GlobalTheory.SizeNum.num_of_size | (intros; apply GlobalTheory.SizeNum.num_of_size <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardRealGeneratedIdealsLeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_realGenerated_ideals_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ Y : ℝ, 1 ≤ Y → {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.Finite ∧ (({𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.ncard : ℕ) : ℝ) ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.RealIdealCount.ncard_real_ideals_le | exact GlobalTheory.RealIdealCount.ncard_real_ideals_le | (intros; apply GlobalTheory.RealIdealCount.ncard_real_ideals_le <;> assumption)
end

