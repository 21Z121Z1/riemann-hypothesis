import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFrameFirstColumnRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.DepFrame

variable {E : Type} [Field E] {n ρ : ℕ}

def FirstRel (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) : Prop :=
  (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
    ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0

theorem mulVec_apply_eq_zero_of_upper {u : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) {a : Fin ρ → E} {i : Fin ρ}
    (ha : ∀ k, i ≤ k → a k = 0) : (u *ᵥ a) i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with h | h
  · simp [hu i k h]
  · simp [ha k h]

theorem mulVec_apply_eq_of_upper {u : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) (hd : ∀ i, u i i = 1) {a : Fin ρ → E} {j : Fin ρ}
    (ha : ∀ i, j < i → a i = 0) : (u *ᵥ a) j = a j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp [hd]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · simp [hu j k h]
    · simp [ha k h]
  · simp

theorem sum_smul_transpose (x : Matrix (Fin n) (Fin ρ) E) (a : Fin ρ → E) :
    ∑ i, a i • x.transpose i = x *ᵥ a := by
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem not_linearIndependent_iff_exists (x : Matrix (Fin n) (Fin ρ) E) :
    ¬ LinearIndependent E x.transpose ↔ ∃ j, FirstRel x j := by
  classical
  have key : LinearIndependent E xᵀ ↔ ∀ g : Fin ρ → E, x *ᵥ g = 0 → ∀ i, g i = 0 := by
    refine (Fintype.linearIndependent_iff (R := E)
      (v := (fun i => xᵀ i : Fin ρ → Fin n → E))).trans ?_
    simp only [sum_smul_transpose]
  rw [key]
  constructor
  · intro h
    push_neg at h
    obtain ⟨g, hg, i₀, hi₀⟩ := h
    let S : Finset (Fin ρ) := Finset.univ.filter fun j =>
      ∃ a : Fin ρ → E, a j ≠ 0 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0
    have hlast : ∀ b : Fin ρ → E, x *ᵥ b = 0 → ∀ i, b i ≠ 0 → ∃ k ∈ S, b k ≠ 0 := by
      intro b hb i hi
      let T : Finset (Fin ρ) := Finset.univ.filter fun k => b k ≠ 0
      have hT : T.Nonempty := ⟨i, by simp [T, hi]⟩
      have hk : T.max' hT ∈ T := Finset.max'_mem T hT
      have hbk : b (T.max' hT) ≠ 0 := by simpa [T] using hk
      refine ⟨T.max' hT, ?_, hbk⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨b, hbk, fun l hl => ?_, hb⟩
      by_contra hne
      have : l ≤ T.max' hT := T.le_max' l (by simp [T, hne])
      exact absurd hl (not_lt.mpr this)
    obtain ⟨k, hkS, -⟩ := hlast g hg i₀ hi₀
    have hS : S.Nonempty := ⟨k, hkS⟩
    have hjS : S.min' hS ∈ S := Finset.min'_mem S hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
    obtain ⟨a, haj, hagt, hax⟩ := hjS
    refine ⟨S.min' hS, ?_, ?_⟩
    · intro b hb hbx
      by_contra hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      obtain ⟨k, hkS, hbk⟩ := hlast b hbx i hi
      have hkj : k < S.min' hS := by
        by_contra h
        exact hbk (hb k (not_lt.mp h))
      exact absurd (S.min'_le k hkS) (not_le.mpr hkj)
    · refine ⟨(a (S.min' hS))⁻¹ • a, by simp only [Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ haj, fun i hi => by simp [hagt i hi], ?_⟩
      rw [Matrix.mulVec_smul, hax, smul_zero]
  · rintro ⟨j, -, a, haj, -, hax⟩ h
    have := h a hax j
    rw [haj] at this
    exact one_ne_zero this

theorem firstRel_unique (x : Matrix (Fin n) (Fin ρ) E) {j j' : Fin ρ}
    (h : FirstRel x j) (h' : FirstRel x j') : j = j' := by
  have key : ∀ {j j' : Fin ρ}, FirstRel x j → FirstRel x j' → ¬ j < j' := by
    rintro j j' ⟨-, a, haj, hagt, hax⟩ ⟨h1, -⟩ hlt
    have h0 := h1 a (fun i hi => hagt i (lt_of_lt_of_le hlt hi)) hax
    simp [h0] at haj
  rcases lt_trichotomy j j' with hl | he | hg
  · exact absurd hl (key h h')
  · exact he
  · exact absurd hg (key h' h)

theorem firstRel_mul (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) {u v : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) (hv : ∀ i k, k < i → v i k = 0) (hvd : ∀ i, v i i = 1)
    (huv : u * v = 1) (hvu : v * u = 1) (h : FirstRel x j) : FirstRel (x * u) j := by
  obtain ⟨h1, a, haj, hagt, hax⟩ := h
  have hmv : ∀ b, (x * u) *ᵥ b = x *ᵥ (u *ᵥ b) := fun b => (Matrix.mulVec_mulVec b x u).symm
  refine ⟨fun b hb hbx => ?_, v *ᵥ a, ?_, fun i hi => ?_, ?_⟩
  · have hub : u *ᵥ b = 0 :=
      h1 _ (fun i hi => mulVec_apply_eq_zero_of_upper hu (fun k hk => hb k (le_trans hi hk)))
        (by rw [← hmv]; exact hbx)
    calc b = (v * u) *ᵥ b := by rw [hvu, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hub, Matrix.mulVec_zero]
  · rw [mulVec_apply_eq_of_upper hv hvd hagt, haj]
  · exact mulVec_apply_eq_zero_of_upper hv (fun k hk => hagt k (lt_of_lt_of_le hi hk))
  · rw [hmv, Matrix.mulVec_mulVec a u v, huv, Matrix.one_mulVec, hax]

theorem firstRel_mul_iff (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E)
    (hd : ∀ i, u i i = 1) (hu : ∀ i k, k < i → u i k = 0) :
    FirstRel x j ↔ FirstRel (x * u) j := by
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i k h => hu i k h)]
    simp [hd]
  have hunit : IsUnit u.det := by rw [hdet]; exact isUnit_one
  letI : Invertible u := Matrix.invertibleOfIsUnitDet u hunit
  have huv : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u hunit
  have hvu : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u hunit
  have hv : ∀ i k, k < i → u⁻¹ i k = 0 := fun i k h =>
    Matrix.blockTriangular_inv_of_blockTriangular (b := id) (fun i k h => hu i k h) h
  have hvd : ∀ i, u⁻¹ i i = 1 := by
    intro i
    have e := congrFun (congrFun hvu i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
    · simpa [hd] using e
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [hv i k h]
      · simp [hu k i h]
    · simp
  constructor
  · exact firstRel_mul x j hu hv hvd huv hvu
  · intro h
    have := firstRel_mul (x * u) j hv hu hd hvu huv h
    rwa [Matrix.mul_assoc, huv, Matrix.mul_one] at this

theorem dependent_frame_first_relation : ∀ (E : Type) [Field E] (n ρ : ℕ) (x : Matrix (Fin n) (Fin ρ) E), (¬ LinearIndependent E x.transpose ↔ ∃ j : Fin ρ, (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ∧ (∀ j j' : Fin ρ, ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) → ((∀ a : Fin ρ → E, (∀ i, j' ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j' = 1 ∧ (∀ i, j' < i → a i = 0) ∧ x *ᵥ a = 0) → j = j') ∧ ∀ (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E), (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → (((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ↔ ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → (x * u) *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ (x * u) *ᵥ a = 0)) := by
  intro E _ n ρ x
  exact ⟨not_linearIndependent_iff_exists x, fun j j' h h' => firstRel_unique x h h',
    fun j u hd hu => firstRel_mul_iff x j u hd hu⟩

end GlobalTheory.DepFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.LastSteps

variable {D : D7}

theorem flagN_rank_zero {S S₀ : HSp D} (d : HypDec S S₀ 0) {n : GA D S} (hn : n ∈ flagN d) : n = 1 := by
  have hle : flagN d ≤ ⊥ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨-, hg⟩
    have hcol : ∀ i : Fin S.rank, ∀ k, subOne S g k i = 0 := by
      intro i k
      obtain ⟨a, ha⟩ := hg (Pi.single i 1) (Subsingleton.elim _ _)
      have h1 := congrFun ha k
      have hr : ratV (D := D) (Pi.single i (1 : D.host.E)) = Pi.single i 1 := by
        funext j; by_cases h : j = i <;> simp [ratV, Pi.single_apply, h]
      rw [hr] at h1
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
    have hm : (matHom S g).1 = 1 := by
      have : subOne S g = 0 := by ext k i; exact hcol i k
      simpa [subOne, sub_eq_zero] using this
    have : matHom S g = 1 := Units.ext hm
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  exact Subgroup.mem_bot.1 (hle hn)

theorem per_rank_zero (B : BesLev D 0) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ f = ∫ h in B.vA.𝓕, φ h * f (embA B.d B.o h) ∂B.vA.μ := by
  unfold BesLev.per besPer
  congr 1; funext h
  have e : ∀ n : flagN B.d, besFun ψ 1 B.d B.o B.ζ φ f h n = φ h * f (embA B.d B.o h) := by
    intro n
    have hp : ∀ m, psiBes ψ B.d 1 (vecB B.o B.ζ) m = 1 := fun m => by
      simp [psiBes, simpleSum, upSum, dotProduct, psiE]
    rw [besFun, flagN_rank_zero B.d n.2, one_mul, hp, star_one, mul_one]
  simp_rw [e]
  rw [setIntegral_const]
  simp [Measure.real, B.vN.unit.2.2]

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem swap_bdd {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y] (μ : Measure X) (ν : Measure Y)
    (s : Set X) (t : Set Y) (hs : μ s < ⊤) (ht : ν t < ⊤) (f : X → Y → ℂ) (hf : Continuous (Function.uncurry f))
    (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C) :
    ∫ x in s, ∫ y in t, f x y ∂ν ∂μ = ∫ y in t, ∫ x in s, f x y ∂μ ∂ν := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  have : IsFiniteMeasure (ν.restrict t) := isFiniteMeasure_restrict.2 ht.ne
  exact integral_integral_swap (Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun p => hC p.1 p.2))

theorem om_bdd {S T A T₀ : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χ χ' om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hA : CoCpt A) (hT : CoCpt T₀) (a : GA D A →* GA D S)
    (b : GA D T₀ →* GA D T) (ha : Continuous a) (hb : Continuous b) (ha' : ∀ γ ∈ GQ A, a γ ∈ GQ S)
    (hb' : ∀ γ ∈ GQ T₀, b γ ∈ GQ T) :
    Continuous (fun p : GA D A × GA D T₀ => om (a p.1, b p.2) f 0) ∧ ∃ C : ℝ, ∀ x y, ‖om (a x, b y) f 0‖ ≤ C := by
  have t0 := EvalCont.tame_om hom hf hA hT a b ha hb ha' hb'
  refine ⟨?_, ?_⟩
  · have := t0.1.comp ((continuous_const (y := (1 : GA D T))).prodMk
      (continuous_id.prodMk (continuous_const (y := (0 : WO S T)))))
    simpa [Function.comp_def] using this
  · obtain ⟨C, hC⟩ := t0.2 1
    exact ⟨C, fun x y => by simpa using hC.self_of_nhds ((x, y), 0)⟩

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps

open EvalCont

theorem bound_mul {x y : ℂ} {C C' : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C') : ‖x * y‖ ≤ C * C' := by
  rw [norm_mul]; exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

theorem triple {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] [BorelSpace X] [BorelSpace Y] [BorelSpace Z] [SecondCountableTopology X]
    [SecondCountableTopology Y] [SecondCountableTopology Z] (μ : Measure X) (ν : Measure Y) (κ : Measure Z)
    (s : Set X) (u : Set Y) (w : Set Z) (hs : μ s < ⊤) (hu : ν u < ⊤) (hw : κ w < ⊤)
    (φ : X → ℂ) (F : Z → ℂ) (a : X → Y → ℂ) (b : Y → Z → ℂ) (hφ : Continuous φ) (hF : Continuous F)
    (ha : Continuous fun p : X × Y => a p.1 p.2) (hb : Continuous fun p : Y × Z => b p.1 p.2)
    {Cφ CF Ca Cb : ℝ} (hCφ : ∀ x, ‖φ x‖ ≤ Cφ) (hCF : ∀ z, ‖F z‖ ≤ CF) (hCa : ∀ x y, ‖a x y‖ ≤ Ca)
    (hCb : ∀ y z, ‖b y z‖ ≤ Cb) :
    ∫ x in s, φ x * ∫ y in u, a x y * ∫ z in w, b y z * F z ∂κ ∂ν ∂μ =
      ∫ z in w, F z * ∫ y in u, b y z * ∫ x in s, φ x * a x y ∂μ ∂ν ∂κ := by
  have : FirstCountableTopology Y := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  set c : Y → ℂ := fun y => ∫ z in w, b y z * F z ∂κ with hc
  set m : Y → ℂ := fun y => ∫ x in s, φ x * a x y ∂μ with hm
  have hcC : Continuous c :=
    Tame.continuous_integral _ _ hw (F := fun y z => b y z * F z) (tame_of_bounded (C := Cb * CF)
      (hb.mul (hF.comp continuous_snd)) fun y z => bound_mul (hCb y z) (hCF z))
  have hcB : ∀ y, ‖c y‖ ≤ Cb * CF * κ.real w := fun y =>
    norm_setIntegral_le_of_norm_le_const hw fun z _ => bound_mul (hCb y z) (hCF z)
  have hmC : Continuous m :=
    Tame.continuous_integral _ _ hs (F := fun y x => φ x * a x y) (tame_of_bounded (C := Cφ * Ca)
      ((hφ.comp continuous_snd).mul (ha.comp continuous_swap)) fun y x => bound_mul (hCφ x) (hCa x y))
  have hmB : ∀ y, ‖m y‖ ≤ Cφ * Ca * μ.real s := fun y =>
    norm_setIntegral_le_of_norm_le_const hs fun x _ => bound_mul (hCφ x) (hCa x y)
  calc ∫ x in s, φ x * ∫ y in u, a x y * c y ∂ν ∂μ
      = ∫ x in s, ∫ y in u, φ x * (a x y * c y) ∂ν ∂μ := by
        congr 1; funext x; rw [integral_const_mul]
    _ = ∫ y in u, ∫ x in s, φ x * (a x y * c y) ∂μ ∂ν := by
        refine swap_bdd _ _ _ _ hs hu _ ?_ (Cφ * (Ca * (Cb * CF * κ.real w))) fun x y =>
          bound_mul (hCφ x) (bound_mul (hCa x y) (hcB y))
        exact (hφ.comp continuous_fst).mul (ha.mul (hcC.comp continuous_snd))
    _ = ∫ y in u, m y * c y ∂ν := by
        congr 1; funext y; rw [hm]; dsimp only; rw [← integral_mul_const]; congr 1; funext x; ring
    _ = ∫ y in u, ∫ z in w, m y * (b y z * F z) ∂κ ∂ν := by
        congr 1; funext y; rw [hc]; dsimp only; rw [integral_const_mul]
    _ = ∫ z in w, ∫ y in u, m y * (b y z * F z) ∂ν ∂κ := by
        refine swap_bdd _ _ _ _ hu hw _ ?_ (Cφ * Ca * μ.real s * (Cb * CF)) fun y z =>
          bound_mul (hmB y) (bound_mul (hCb y z) (hCF z))
        exact (hmC.comp continuous_fst).mul (hb.mul (hF.comp continuous_snd))
    _ = ∫ z in w, F z * ∫ y in u, b y z * m y ∂ν ∂κ := by
        congr 1; funext z; rw [← integral_const_mul]; congr 1; funext y; ring

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps

open EvalCont in

theorem lastLaw : ∀ D : D7, LastLaw D := by
  intro D ψ T B t φ Φ₁ Φ₂ F hφ hF hΦ₁ hΦ₂
  obtain ⟨-, iA2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨-, iS2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D t.J.W
  obtain ⟨-, iT2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have : BorelSpace (GA D B.A) := ⟨rfl⟩
  have : BorelSpace (GA D t.J.W) := ⟨rfl⟩
  have : BorelSpace (GA D T) := ⟨rfl⟩
  obtain ⟨Cφ, hCφ⟩ := bounded_of_contAut B.cpt hφ
  obtain ⟨CF, hCF⟩ := bounded_of_contAut t.cptT hF
  obtain ⟨ha, Ca, hCa⟩ := om_bdd t.s.weil hΦ₁ B.cpt t.cptS (embA B.d B.o) (MonoidHom.id _)
    (B.d.continuous_embed.comp (continuous_embL B)) continuous_id
    (fun γ hγ => B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))) (fun γ hγ => hγ)
  obtain ⟨hb, Cb, hCb⟩ := om_bdd t.weil hΦ₂ t.cptS t.cptT (MonoidHom.id _) (MonoidHom.id _) continuous_id continuous_id
    (fun γ hγ => hγ) (fun γ hγ => hγ)
  simp only [MonoidHom.id_apply] at ha hCa hb hCb
  have e1 : ∀ h₀, t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ₂) Φ₁ (embA B.d B.o h₀) =
      ∫ h in t.s.vW.𝓕, t.s.om (embA B.d B.o h₀, h) Φ₁ 0 * ∫ h' in t.vT.𝓕, t.om (h, h') Φ₂ 0 * F h' ∂t.vT.μ ∂t.s.vW.μ :=
    fun h₀ => rfl
  rw [per_rank_zero]
  simp_rw [e1]
  exact triple B.vA.μ t.s.vW.μ t.vT.μ B.vA.𝓕 t.s.vW.𝓕 t.vT.𝓕 (vol_lt_top B.cpt B.vA) (vol_lt_top t.cptS t.s.vW)
    (vol_lt_top t.cptT t.vT) φ F (fun x y => t.s.om (embA B.d B.o x, y) Φ₁ 0) (fun y z => t.om (y, z) Φ₂ 0) hφ.2 hF.2
    ha hb hCφ hCF hCa hCb

end GlobalTheory.Unf.LastSteps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleSumWeightedBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
noncomputable section
variable {D : D7}

namespace GlobalTheory.Unf.DoubleSum

theorem realSize_nsmul (θ : InfFam D) {m k : ℕ} (n : ℕ) (x : Mx D m k) :
    realSize θ (n • x) = n * realSize θ x := by
  unfold realSize
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  have : compAt θ τ (n • x) i j = (n : ℂ) * compAt θ τ x i j := by
    simp only [compAt, Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  rw [this, norm_mul, Complex.norm_natCast]

theorem pointwise (θ : InfFam D) {a b c e : ℕ} (K : Set (Mx D a b)) (K' : Set (Mx D c e)) (N N' n : ℕ) (hn : 0 < n)
    (B : ℝ≥0∞) (F : ratMx D a b → ratMx D c e → ℝ≥0∞)
    (hF : ∀ x y, F x y ≠ 0 → InBox K (n • (x : Mx D a b)) ∧ InBox K' (n • (y : Mx D c e)))
    (h1 : ∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (x : Mx D a b)) ^ (N + N')) ≤ B)
    (h2 : ∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (y : Mx D c e)) ^ (N + N')) ≤ B) (x : ratMx D a b) (y : ratMx D c e) :
    F x y ≤ (n : ℝ≥0∞) ^ (N + N') * B * (ENNReal.ofReal (maj θ K N (n • (x : Mx D a b))) *
      ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e)))) := by
  by_cases h0 : F x y = 0
  · rw [h0]; exact bot_le
  obtain ⟨hx, hy⟩ := hF x y h0
  set s := 1 + realSize θ (x : Mx D a b) with hs
  set t := 1 + realSize θ (y : Mx D c e) with ht
  have s1 : 1 ≤ s := by have := realSize_nonneg θ (x : Mx D a b); linarith
  have t1 : 1 ≤ t := by have := realSize_nonneg θ (y : Mx D c e); linarith
  set M := max s t with hM
  have M1 : 1 ≤ M := le_trans s1 (le_max_left _ _)
  have Mpos : 0 < M := by linarith
  have hFM : F x y * ENNReal.ofReal (M ^ (N + N')) ≤ B := by
    rcases le_total s t with h | h
    · rw [hM, max_eq_right h]; exact h2 x y
    · rw [hM, max_eq_left h]; exact h1 x y
  have hMp : 0 < M ^ (N + N') := pow_pos Mpos _
  have hF' : F x y ≤ B * ENNReal.ofReal ((M ^ (N + N'))⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hMp, ← div_eq_mul_inv]
    exact ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hMp)) (Or.inl ENNReal.ofReal_ne_top) |>.2 hFM
  refine hF'.trans ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : 1 + realSize θ (n • (x : Mx D a b)) ≤ n * M := by
    rw [realSize_nsmul]
    have := realSize_nonneg θ (x : Mx D a b)
    calc 1 + n * realSize θ (x : Mx D a b) ≤ n * s := by rw [hs]; nlinarith
      _ ≤ n * M := by gcongr; exact le_max_left _ _
  have hny : 1 + realSize θ (n • (y : Mx D c e)) ≤ n * M := by
    rw [realSize_nsmul]
    have := realSize_nonneg θ (y : Mx D c e)
    calc 1 + n * realSize θ (y : Mx D c e) ≤ n * t := by rw [ht]; nlinarith
      _ ≤ n * M := by gcongr; exact le_max_right _ _
  have px : 0 < 1 + realSize θ (n • (x : Mx D a b)) := by have := realSize_nonneg θ (n • (x : Mx D a b)); linarith
  have py : 0 < 1 + realSize θ (n • (y : Mx D c e)) := by have := realSize_nonneg θ (n • (y : Mx D c e)); linarith
  have key : (M ^ (N + N'))⁻¹ ≤ (n : ℝ) ^ (N + N') * (((1 + realSize θ (n • (x : Mx D a b))) ^ N)⁻¹ *
      ((1 + realSize θ (n • (y : Mx D c e))) ^ N')⁻¹) := by
    have e1 : ((n * M) ^ N)⁻¹ ≤ ((1 + realSize θ (n • (x : Mx D a b))) ^ N)⁻¹ :=
      inv_anti₀ (pow_pos px _) (pow_le_pow_left₀ px.le hnx _)
    have e2 : ((n * M) ^ N')⁻¹ ≤ ((1 + realSize θ (n • (y : Mx D c e))) ^ N')⁻¹ :=
      inv_anti₀ (pow_pos py _) (pow_le_pow_left₀ py.le hny _)
    have npos : (0 : ℝ) < n := by linarith
    calc (M ^ (N + N'))⁻¹ = (n : ℝ) ^ (N + N') * (((n * M) ^ N)⁻¹ * ((n * M) ^ N')⁻¹) := by
          rw [mul_pow, mul_pow, pow_add, pow_add]; field_simp
      _ ≤ _ := by gcongr
  unfold maj
  rw [if_pos hx, if_pos hy, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    show (n : ℝ≥0∞) ^ (N + N') = ENNReal.ofReal ((n : ℝ) ^ (N + N')) by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast],
    mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
  gcongr

end GlobalTheory.Unf.DoubleSum

end

theorem GlobalTheory.Unf.doubleSum_le_maj : ∀ (D : D7) (θ : InfFam D) (a b c e : ℕ) (K : Set (Mx D a b)) (K' : Set (Mx D c e)) (N N' n : ℕ), 0 < n → ∀ (B : ℝ≥0∞) (F : ratMx D a b → ratMx D c e → ℝ≥0∞), (∀ x y, F x y ≠ 0 → InBox K (n • (x : Mx D a b)) ∧ InBox K' (n • (y : Mx D c e))) → (∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (x : Mx D a b)) ^ (N + N')) ≤ B) → (∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (y : Mx D c e)) ^ (N + N')) ≤ B) → ∑' x, ∑' y, F x y ≤ (n : ℝ≥0∞) ^ (N + N') * B * ((∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N x)) * ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' y)) := by
  intro D θ a b c e K K' N N' n hn B F hF h1 h2
  have hinj : Function.Injective (fun x : ratMx D a b => n • x) := by
    intro u v huv
    obtain ⟨γ, hγ⟩ := u.2; obtain ⟨δ, hδ⟩ := v.2
    have e1 : ((n • u : ratMx D a b) : Mx D a b) = n • (u : Mx D a b) := AddSubgroup.coe_nsmul _ _ _
    have e2 : ((n • v : ratMx D a b) : Mx D a b) = n • (v : Mx D a b) := AddSubgroup.coe_nsmul _ _ _
    have h := congrArg Subtype.val huv
    simp only at h
    rw [e1, e2] at h
    apply Subtype.ext
    have hr : rat (n • γ) = rat (n • δ) := by
      have r1 : rat (n • γ) = n • rat γ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      have r2 : rat (n • δ) = n • rat δ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      rw [r1, r2]
      have hγ' : rat γ = (u : Mx D a b) := hγ
      have hδ' : rat δ = (v : Mx D a b) := hδ
      rw [hγ', hδ']; exact h
    have hγδ : γ = δ := by
      have := rat_injective hr
      funext i j
      have hij := congrFun (congrFun this i) j
      simp only [Matrix.smul_apply, nsmul_eq_mul] at hij
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)) hij
    have hγ' : rat γ = (u : Mx D a b) := hγ
    have hδ' : rat δ = (v : Mx D a b) := hδ
    rw [← hγ', ← hδ', hγδ]
  have hinj' : Function.Injective (fun y : ratMx D c e => n • y) := by
    intro u v huv
    obtain ⟨γ, hγ⟩ := u.2; obtain ⟨δ, hδ⟩ := v.2
    have e1 : ((n • u : ratMx D c e) : Mx D c e) = n • (u : Mx D c e) := AddSubgroup.coe_nsmul _ _ _
    have e2 : ((n • v : ratMx D c e) : Mx D c e) = n • (v : Mx D c e) := AddSubgroup.coe_nsmul _ _ _
    have h := congrArg Subtype.val huv
    simp only at h
    rw [e1, e2] at h
    apply Subtype.ext
    have hr : rat (n • γ) = rat (n • δ) := by
      have r1 : rat (n • γ) = n • rat γ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      have r2 : rat (n • δ) = n • rat δ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      rw [r1, r2]
      have hγ' : rat γ = (u : Mx D c e) := hγ
      have hδ' : rat δ = (v : Mx D c e) := hδ
      rw [hγ', hδ']; exact h
    have hγδ : γ = δ := by
      have := rat_injective hr
      funext i j
      have hij := congrFun (congrFun this i) j
      simp only [Matrix.smul_apply, nsmul_eq_mul] at hij
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)) hij
    have hγ' : rat γ = (u : Mx D c e) := hγ
    have hδ' : rat δ = (v : Mx D c e) := hδ
    rw [← hγ', ← hδ', hγδ]
  have hx : ∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N (n • (x : Mx D a b))) ≤
      ∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N x) := by
    have := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun x : ratMx D a b => ENNReal.ofReal (maj θ K N x))
    simpa only [AddSubgroup.coe_nsmul] using this
  have hy : ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e))) ≤
      ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' y) := by
    have := ENNReal.tsum_comp_le_tsum_of_injective hinj' (fun y : ratMx D c e => ENNReal.ofReal (maj θ K' N' y))
    simpa only [AddSubgroup.coe_nsmul] using this
  calc ∑' x, ∑' y, F x y ≤ ∑' (x : ratMx D a b), ∑' (y : ratMx D c e), (n : ℝ≥0∞) ^ (N + N') * B * (ENNReal.ofReal (maj θ K N (n • (x : Mx D a b))) *
        ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e)))) :=
        ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun y =>
          GlobalTheory.Unf.DoubleSum.pointwise θ K K' N N' n hn B F hF h1 h2 x y
    _ = (n : ℝ≥0∞) ^ (N + N') * B * ((∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N (n • (x : Mx D a b)))) *
        ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e)))) := by
        simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ ≤ _ := by gcongr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicTraceCharacterSplitSectionNeOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicTraceCharacter_splitSection_ne_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ a : k, GlobalTheory.MixPer.psiE ψ (p.sec a) ≠ 1 := by
  first | exact @GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one | exact GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one | (intros; apply GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunctionStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_borelSphericalFunction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ), (∀ i, γ i ≠ 0) → ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k γ ψ := by
  first | exact @GlobalTheory.BorelSphExist.exists_isBorelSph | exact GlobalTheory.BorelSphExist.exists_isBorelSph | (intros; apply GlobalTheory.BorelSphExist.exists_isBorelSph <;> assumption)
end

