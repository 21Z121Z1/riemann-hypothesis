import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusId

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorOpContinuousOn
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
open Formalism.REAL (qdet GlRel IsHW)

noncomputable section

namespace GlobalTheory.TensorDualStd

section General

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k : ℕ}

def tensorOp (C : Matrix (Fin k) (Fin k) ℂ) (A : V →L[ℂ] V) :
    PiLp 2 (fun _ : Fin k => V) →L[ℂ] PiLp 2 (fun _ : Fin k => V) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 fun c => ∑ d, C c d • A (y d)
      map_add' := fun x y => by
        ext c
        simp [Finset.sum_add_distrib]
      map_smul' := fun a x => by
        ext c
        simp [Finset.smul_sum, smul_smul, mul_comm] }

theorem tensorOp_apply (C : Matrix (Fin k) (Fin k) ℂ) (A : V →L[ℂ] V) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    tensorOp C A y c = ∑ d, C c d • A (y d) := rfl

theorem tensorOp_one : tensorOp (1 : Matrix (Fin k) (Fin k) ℂ) (1 : V →L[ℂ] V) = 1 := by
  ext y c
  simp [tensorOp_apply, Matrix.one_apply]

theorem tensorOp_mul (C D : Matrix (Fin k) (Fin k) ℂ) (A B : V →L[ℂ] V) :
    tensorOp (C * D) (A.comp B) = (tensorOp C A).comp (tensorOp D B) := by
  ext y c
  simp only [tensorOp_apply, ContinuousLinearMap.comp_apply, Matrix.mul_apply, Finset.sum_smul, map_sum,
    map_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem tensorOp_norm {C : Matrix (Fin k) (Fin k) ℂ} (hC : ∀ d e, ∑ c, star (C c d) * C c e = if d = e then 1 else 0)
    {A : V →L[ℂ] V} (hA : ∀ v, ‖A v‖ = ‖v‖) (y : PiLp 2 (fun _ : Fin k => V)) : ‖tensorOp C A y‖ = ‖y‖ := by
  have h1 : inner ℂ (tensorOp C A y) (tensorOp C A y) = inner ℂ y y := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    calc ∑ c, inner ℂ (tensorOp C A y c) (tensorOp C A y c)
        = ∑ c, ∑ d, ∑ e, (star (C c d) * C c e) * inner ℂ (A (y d)) (A (y e)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [tensorOp_apply, sum_inner]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [inner_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [inner_smul_left, inner_smul_right, mul_assoc]
          rfl
      _ = ∑ d, ∑ e, (∑ c, star (C c d) * C c e) * inner ℂ (A (y d)) (A (y e)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ d, inner ℂ (y d) (y d) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          simp only [hC, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hA]
  rw [@norm_eq_sqrt_re_inner ℂ, h1, ← @norm_eq_sqrt_re_inner ℂ]

theorem tensorOp_continuousOn {X : Type} [TopologicalSpace X] {s : Set X} {C : X → Matrix (Fin k) (Fin k) ℂ}
    {A : X → (V →L[ℂ] V)} (hC : ∀ c d, Continuous fun x => C x c d) (hA : ContinuousOn A s) :
    ContinuousOn (fun x => tensorOp (C x) (A x)) s := by
  rw [continuousOn_clm_apply]
  intro y
  have h : ContinuousOn (fun x => fun c => ∑ d, C x c d • A x (y d)) s := by
    refine continuousOn_pi.2 fun c => continuousOn_finsetSum _ fun d _ => ?_
    exact (hC c d).continuousOn.smul (hA.clm_apply continuousOn_const)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin k => V)).comp_continuousOn h

end General

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem herm_inv {h : Mx k r} (hh : h ∈ UWset k r z) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ v) (h *ᵥ w) = herm (Hpk k r) v w := by
  have e : hᴴ * Hpk k r * h = Hpk k r := hh.1
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]

theorem inWb_mulVec {h : Mx k r} (hh : h ∈ UWset k r z) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (h *ᵥ v) := by
  rw [Qx8.inWb_iff] at hv ⊢
  intro c
  have hc := hh.2.1 c
  constructor
  · rw [← Qx8.coord_e (h *ᵥ v) c, ← hc.2, herm_inv hh, Qx8.coord_e]
    exact (hv c).1
  · rw [← Qx8.coord_es (h *ᵥ v) c, ← hc.1, herm_inv hh, Qx8.coord_es]
    exact (hv c).2

theorem expand {B : Fin k → Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hB : IsFrameOf k r [z] B) {h : Mx k r} (hh : h ∈ UWset k r z) (d : Fin k) :
    h *ᵥ B d = ∑ c, herm (Hpk k r) (h *ᵥ B d) (B c) • B c := by
  refine HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB (inWb_mulVec hh (hB.1 d)) ?_
  have h1 := herm_inv hh (B d) z
  rw [hh.2.2] at h1
  rw [h1]
  exact hB.2.2 d z (by simp)

def dualMat (k r : ℕ) (B : Fin k → Fin (2 * r + k + 1) → ℂ) (h : Mx k r) : Matrix (Fin k) (Fin k) ℂ :=
  fun c d => star (herm (Hpk k r) (h *ᵥ B d) (B c))

end GlobalTheory.TensorDualStd

open GlobalTheory.TensorDualStd in

theorem GlobalTheory.tensor_dual_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → ∃ πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V))), IsRepW k r z πt ∧ (∀ h ∈ UWset k r z, ∀ v, ‖πt h v‖ = ‖v‖) ∧ (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d)) := by
  intro V _ _ _ k r z π B hz hT hπ hn hB
  refine ⟨fun h => tensorOp (dualMat k r B h) (π h), ⟨⟨?_, ?_⟩, ?_⟩, ?_, fun h _ y c => rfl⟩
  · have h1 : dualMat k r B 1 = 1 := by
      ext c d
      simp only [dualMat, Matrix.one_mulVec, hB.2.1, Matrix.one_apply]
      by_cases h : c = d
      · simp [h]
      · simp [h, Ne.symm h]
    simp only [h1, hπ.1.1]
    exact tensorOp_one
  · intro a ha b hb
    have h1 : dualMat k r B (a * b) = dualMat k r B a * dualMat k r B b := by
      ext c d
      simp only [dualMat, Matrix.mul_apply]
      rw [← Matrix.mulVec_mulVec]
      conv_lhs => rw [expand hz hT hB hb d, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
      rw [HermitianFormSums.herm_lsum, star_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [star_mul]
    simp only [h1, hπ.1.2 a ha b hb]
    exact tensorOp_mul _ _ _ _
  · refine tensorOp_continuousOn (fun c d => ?_) hπ.2
    unfold dualMat herm
    fun_prop
  · intro h hh v
    refine tensorOp_norm (fun d e => ?_) (hn h hh) v
    simp only [dualMat, star_star]
    rw [← HermitianFormSums.herm_comb hB, ← expand hz hT hB hh, ← expand hz hT hB hh, herm_inv hh, hB.2.1]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapZeroOfContraction
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

open Matrix in

theorem _root_.GlobalTheory.WigSh.wigMap_zero_of_contraction : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (V₂ →L[ℂ] V₂)) (φ : V₂ →L[ℂ] V₁), (∀ v, ‖φ v‖ ≤ ‖v‖) → (∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, ∀ v, φ (π₂ h v) = π₁ h (φ v)) → _root_.GlobalTheory.WigSh.WigMap k r z π₂ π₁ 0 (fun _ => φ) := by
  intro V₁ _ _ V₂ _ _ k r z π₁ π₂ φ hφ heqv
  refine ⟨⟨1, fun _ => 1, fun _ => φ, fun _ => by simp, fun ω => by simp⟩,
    fun h hh ω => ?_, fun t ω => by simp, fun ω _ _ => ?_⟩
  · ext v
    exact heqv h hh v
  · have hle : ‖φ‖ ≤ 1 := φ.opNorm_le_bound zero_le_one (fun v => by simpa using hφ v)
    rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) hle

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordLDecompositionNfSpan
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.WordL

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem mem_of_bmon (d : Q.NFData P A) {b : A} (hb : b ∈ bmon d) : b ∈ nfSpan d ∅ 0 0 0 :=
  Submodule.subset_span ⟨b, hb, [], rfl, by simp, by simp⟩

theorem span_eq (d : Q.NFData P A) : nfSpan d ∅ 0 0 0 = Submodule.span ℂ (bmon d : Set A) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨b, hb, H, hH, -, rfl⟩
    rw [List.length_eq_zero_iff.mp hH]
    simpa using Submodule.subset_span (R := ℂ) (s := (bmon d : Set A)) hb
  · exact Submodule.span_le.mpr fun b hb => mem_of_bmon d hb

theorem span_mul (d : Q.NFData P A) {x y : A} (hx : x ∈ nfSpan d ∅ 0 0 0) (hy : y ∈ nfSpan d ∅ 0 0 0) :
    x * y ∈ nfSpan d ∅ 0 0 0 := by
  rw [span_eq] at *
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact (bmon d).mul_mem ha hb

theorem kappa_mem (d : Q.NFData P A) (f : M.Ty P → ℂ) : d.κ f ∈ nfSpan d ∅ 0 0 0 :=
  mem_of_bmon d (Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩))))

theorem zbi_mem (d : Q.NFData P A) : d.L.ζbi ∈ nfSpan d ∅ 0 0 0 :=
  mem_of_bmon d (Submonoid.subset_closure (Or.inl (Or.inl (Or.inl (by simp)))))

variable {S : Type} [Fintype S] [DecidableEq S]

def BMat (d : Q.NFData P A) (E : SlopeTestRemainingChoices S A) : Prop := ∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0

theorem BMat.mul {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E * F) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Submodule.sum_mem _ fun k _ => span_mul d (hE i k) (hF k j)

theorem BMat.add {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E + F) :=
  fun i j => add_mem (hE i j) (hF i j)

theorem BMat.sub {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E - F) :=
  fun i j => sub_mem (hE i j) (hF i j)

theorem BMat.smul {d : Q.NFData P A} {E : SlopeTestRemainingChoices S A} (c : ℂ) (hE : BMat d E) : BMat d (c • E) :=
  fun i j => Submodule.smul_mem _ c (hE i j)

theorem bMat_io {d : Q.NFData P A} {a : A} (ha : a ∈ nfSpan d ∅ 0 0 0) : BMat d (io a : SlopeTestRemainingChoices S A) := fun i j => by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact zero_mem _

theorem io_add (a b : A) : (io (a + b) : SlopeTestRemainingChoices S A) = io a + io b := map_add (Matrix.scalar (Ix S)) a b

theorem io_mul (a b : A) : (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b := map_mul (Matrix.scalar (Ix S)) a b

theorem inv_subset {r : ℕ} (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) :
    ∀ Y ∈ (ofWord L st w).inv, Y ∈ st.inv := by
  induction w with
  | nil => exact fun Y hY => hY
  | cons l w ih =>
    intro Y hY
    by_cases hp : l.plus
    · have e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e] at hY
      exact ih Y hY.1
    · have e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e] at hY
      exact ih Y hY.1

theorem comm_id {R : Type*} [Ring R] (l K E α β γ : R) (h1 : β * l = l * β) (h2 : β * K = K * β)
    (h3 : α * K = K * α) :
    α * ((l + K * E) * β - β * (l + K * E)) * γ = K * (α * (E * β - β * E) * γ) := by
  have : (l + K * E) * β - β * (l + K * E) = K * (E * β - β * E) := by
    rw [mul_add, h1, ← mul_assoc β K, h2]; noncomm_ring
  rw [this, ← mul_assoc α K, h3]; simp only [mul_assoc]

end

theorem word_l_shape : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).l L Y = io (d.L.l0 Y) + kapL d.L * E := by
  intro P A _ _ _ _ d hd L st s hT S _ _ w hA Y hY hY1
  obtain ⟨hk, h0⟩ := GlobalTheory.T.frameStart_constants_normalForm_empty_word P A d hd L st s hT
  obtain ⟨E0, hE0, e0⟩ := h0 Y (inv_subset L st w Y hY)
  obtain ⟨hH, hS, -⟩ := hT
  obtain ⟨-, -, -, -, -, -, -, s1, s2, s3, -, s4, s5⟩ := hS
  have hkap : (kapL L : SlopeTestRemainingChoices S A) = kapL d.L := by simp only [kapL, s1, s2, s4]
  have htz : (tz L : SlopeTestRemainingChoices S A) = tz d.L := by simp only [tz, s3, s5]
  have hl0 : (st.frame : FrameData S A).l L Y = io (d.L.l0 Y) + kapL d.L * io E0 := by
    show io (L.l0 Y) + io (L.ζb * L.ζi * L.GGi) * io (st.ee Y) =
      io (d.L.l0 Y) + io (d.L.ζb * d.L.ζi * d.L.GGi) * io E0
    rw [← io_mul, ← io_add, e0, io_add, io_mul]
  have hsh := (Formalism.FourierDecayAlt.P.l_shape A S P.r L st w hH.starLev hH.start hA).2.2 Y hY hY1
  rw [hl0, hkap, htz] at hsh
  have hc := hd.2.2.1.2.1
  have cζb : ∀ f, Commute (d.κ f) d.L.ζb := fun f => hc f _ (by simp [LevelData.fns])
  have cζi : ∀ f, Commute (d.κ f) d.L.ζi := fun f => hc f _ (by simp [LevelData.fns])
  have cG : ∀ f, Commute (d.κ f) d.L.GGi := fun f => hc f _ (by simp [LevelData.fns])
  have cn : ∀ f, Commute (d.κ f) d.L.nab := fun f => hc f _ (by simp)
  have cio : ∀ (a : A), (∀ f, Commute (d.κ f) a) → ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * io a = io a * α := by
    intro a ha α hα
    refine (Formalism.FourierDecayAlt.P.TLA.L1.io_comm fun i j => ?_).symm.eq
    obtain ⟨f, hf⟩ := hk _ (hα i j)
    rw [← hf]; exact (ha f).symm
  have cK : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * kapL d.L = kapL d.L * α :=
    cio _ fun f => ((cζb f).mul_right (cζi f)).mul_right (cG f)
  have cl : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * io (d.L.l0 Y) = io (d.L.l0 Y) * α :=
    cio _ fun f => (cn f).neg_right.sub_right
      ((show Commute (d.κ f) (algebraMap ℂ A (Y + 1 / 2)) from (Algebra.commutes _ _).symm).mul_right
        ((cζb f).mul_right (cG f)))
  have hB : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → BMat d α := by
    intro α hα i j
    obtain ⟨f, hf⟩ := hk _ (hα i j)
    rw [← hf]; exact kappa_mem d f
  have hE : BMat d (io E0 : SlopeTestRemainingChoices S A) := bMat_io hE0
  have key : ∀ M ∈ TL.dSpan st (io (d.L.l0 Y) + kapL d.L * io E0 : SlopeTestRemainingChoices S A) (kapL d.L) (tz d.L),
      ∃ E : SlopeTestRemainingChoices S A, BMat d E ∧ M = kapL d.L * E := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨α, β, γ, h1, h2, h3, rfl⟩ | ⟨γ, h, rfl | rfl⟩
      · exact ⟨_, ((hB α h1).mul ((hE.mul (hB β h2)).sub ((hB β h2).mul hE))).mul (hB γ h3),
          comm_id _ _ _ _ _ _ (cl β h2) (cK β h2) (cK α h1)⟩
      · exact ⟨γ, hB γ h, rfl⟩
      · exact ⟨tz d.L * γ, (bMat_io (Submodule.smul_mem _ _ (zbi_mem d))).mul (hB γ h), mul_assoc _ _ _⟩
    | zero => exact ⟨0, fun _ _ => zero_mem _, (mul_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨E, hE, rfl⟩ := hx
      obtain ⟨F, hF, rfl⟩ := hy
      exact ⟨E + F, hE.add hF, (mul_add _ _ _).symm⟩
    | smul c x _ hx =>
      obtain ⟨E, hE, rfl⟩ := hx
      exact ⟨c • E, hE.smul c, (mul_smul_comm _ _ _).symm⟩
  obtain ⟨E, hE', e⟩ := key _ hsh
  refine ⟨io E0 + E, hE.add hE', ?_⟩
  rw [sub_eq_iff_eq_add.mp e, mul_add]
  abel

end GlobalTheory.HatNF.WordL
end

