import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterLiftOfParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExistsAndVectorEqSmulTranslate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTypeOfIrreducibleStable
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
namespace GlobalTheory

theorem isType_of_irreducible_stable : ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (Y →L[ℂ] Y)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (S : Submodule ℂ Y) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → Stab (EB π B) S → S ≠ ⊥ → (∀ S' : Submodule ℂ Y, S' ≤ S → Stab (EB π B) S' → S' = ⊥ ∨ S' = S) → (∀ (w : ℂ), ∀ y ∈ S, qdet (EB π B) w y = (∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • y) → ∃ πS : Mx k r → (S →L[ℂ] S), IsType k r z πS u ∧ ∀ h ∈ UWset k r z, ∀ y : S, ((πS h y : S) : Y) = π h y := by
  intro Y _ _ _ k r z π B S u hz hT hπ hn hB hS hne hirr hcap
  have hst : ∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S :=
    Formalism.FourierDecayAlt.P.lie_stabilizer Y k r z π B hz hT hπ hB S hS
  have hfr0 : ∀ {m : ℕ} (C : Fin m → (Fin (2 * r + k + 1) → ℂ)), IsFrameOf k r [z] C → IsFrameOf k r [z, 0] C := by
    intro m C hC
    refine ⟨hC.1, hC.2.1, fun a v hv => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hC.2.2 a _ (by simp)
    · simp [herm]
  let πS : Mx k r → (S →L[ℂ] S) := fun h => (S.orthogonalProjection).comp ((π h).comp S.subtypeL)
  have hcoe : ∀ h ∈ UWset k r z, ∀ y : S, ((πS h y : S) : Y) = π h y := by
    intro h hh y
    have := Submodule.orthogonalProjection_mem_subspace_eq_self (K := S) ⟨π h y, hst h hh y y.2⟩
    exact congrArg Subtype.val this
  have hrep : IsRepW k r z πS := by
    refine ⟨⟨?_, fun a _ b hb => ?_⟩, ?_⟩
    · ext y
      simp [πS, hπ.1.1]
    · ext y
      have h1 := hcoe b hb y
      simp only [πS, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at h1 ⊢
      rw [h1, hπ.1.2 a ‹_› b hb]
      rfl
    · exact continuousOn_const.clm_comp (hπ.2.clm_comp continuousOn_const)
  refine ⟨πS, ⟨Submodule.nontrivial_iff_ne_bot.2 hne, hrep.1, hrep.2, ?_, ?_, ?_⟩, hcoe⟩
  · intro h hh v
    rw [Submodule.coe_norm, Submodule.coe_norm, hcoe h hh, hn h hh]
  · intro S'' hS''
    have hstab : Stab (EB π B) (S''.map S.subtype) := by
      refine Formalism.FourierDecayAlt.P.stabilizer_lie_algebra Y k r k z 0 π B hπ (hfr0 B hB) _ ?_
      rintro h hh - _ ⟨y, hy, rfl⟩
      exact ⟨πS h y, hS'' h hh y hy, hcoe h hh y⟩
    rcases hirr _ (Submodule.map_subtype_le S S'') hstab with h | h
    · left
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_subtype_top])
  · intro B' hB' w v
    rw [(Formalism.FourierDecayAlt.P.frame_general_linear S k r k z πS B' hrep hB').2 w v]
    apply Subtype.ext
    have h1 := GlobalTheory.intertwiner_EB_of_stabiliser S Y k r k z 0 πS π S.subtypeL B' hrep hπ (hfr0 B' hB') (fun h hh _ v => hcoe h hh v)
    have h2 := GlobalTheory.qminor_intertwine Y S k k (EB π B') (EB πS B') S.subtype h1 id id w v
    have h3 := GlobalTheory.capelli_det_frame_indep Y k r z π B B' hz hT hπ hB hB' w
    refine h2.trans ?_
    have h4 := hcap w v v.2
    rw [h3] at h4
    exact h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LetterColMemNormalFormProductSpan
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.LetterEntries

open Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.TLA

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

omit [StarModule ℂ A] in

theorem gen_mem (d : Q.NFData P A) {T : Set A} {b X : A} (hb : b ∈ bmon d) (hX : X ∈ T) :
    b * d.L.Di * X ∈ nfSpan d T 1 0 1 :=
  Submodule.subset_span ⟨b, hb, [X], rfl, by simpa using hX, by simp⟩

omit [StarModule ℂ A] in

theorem bounded_induction (d : Q.NFData P A) (N : Submodule ℂ A) (hN : ∀ b ∈ bmon d, b ∈ N) {E : A}
    (hE : E ∈ nfSpan d ∅ 0 0 0) : E ∈ N := by
  refine (Submodule.span_le.mpr ?_ : nfSpan d ∅ 0 0 0 ≤ N) hE
  rintro x ⟨b, hb, H, hH, -, rfl⟩
  rw [List.length_eq_zero_iff] at hH
  subst hH
  simpa using hN b hb

omit [StarModule ℂ A] in
theorem bounded_mul_mem (d : Q.NFData P A) {T : Set A} {E b X : A} (hE : E ∈ nfSpan d ∅ 0 0 0) (hb : b ∈ bmon d)
    (hX : X ∈ T) : E * (b * d.L.Di * X) ∈ nfSpan d T 1 0 1 := by
  refine bounded_induction d ((nfSpan d T 1 0 1).comap (LinearMap.mulRight ℂ (b * d.L.Di * X))) ?_ hE
  intro c hc
  have := gen_mem d (mul_mem hc hb) hX
  simpa [mul_assoc] using this

omit [StarModule ℂ A] in
theorem bounded_comm (d : Q.NFData P A) {E f : A} (hE : E ∈ nfSpan d ∅ 0 0 0) (hf : ∀ b ∈ bmon d, Commute b f) :
    f * E = E * f := by
  have := bounded_induction d (LinearMap.ker (LinearMap.mulLeft ℂ f - LinearMap.mulRight ℂ f))
    (fun b hb => by simp [(hf b hb).eq]) hE
  simpa [sub_eq_zero] using this

variable {S : Type} [Fintype S] [DecidableEq S]

omit [StarModule ℂ A] [StarRing A] in
theorem io_mem {N : Submodule ℂ A} {a : A} (ha : a ∈ N) (e e' : Ix S) : (io a : SlopeTestRemainingChoices S A) e e' ∈ N := by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact N.zero_mem

omit [StarModule ℂ A] [StarRing A] in
theorem col_mem {N : Submodule ℂ A} {s X k V W : A} {E : SlopeTestRemainingChoices S A} (h1 : s * (X * V + W) ∈ N)
    (h2 : ∀ e e', s * k * E e e' * V ∈ N) (e e' : Ix S) :
    (io s * ((io X + io k * E) * io V + io W) : SlopeTestRemainingChoices S A) e e' ∈ N := by
  have key : io s * ((io X + io k * E) * io V + io W) =
      (io (s * (X * V + W)) : SlopeTestRemainingChoices S A) + io (s * k) * E * io V := by
    simp only [io, map_mul, map_add]; noncomm_ring
  rw [key, Matrix.add_apply]
  refine N.add_mem (io_mem h1 e e') ?_
  have : (io (s * k) * E * io V : SlopeTestRemainingChoices S A) e e' = s * k * E e e' * V := by
    simp [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [this]
  exact h2 e e'

theorem letterCol_mem : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s →
    ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (l : Letter ℂ S) (w : List (Letter ℂ S)), admitted st (l :: w) →
    ∀ i e e', TL.letterCol L st l w i e e' ∈ nfSpan d (hats d.L) 1 0 1 := by
  intro P A _ _ _ _ d hd0 L st s hT S _ _ l w hA i e e'
  obtain ⟨hnd, hre, hpt, hpw⟩ := hA
  have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
    List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
  have hpw' := List.pairwise_cons.mp hpw
  have hAw : admitted st w :=
    ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
  obtain ⟨p0, p1, pm1, -, -⟩ := hpt l (by simp)
  have hd := hpw'.1
  have m0 : l.pt ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p0 (fun l' hl' =>
    ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
  have m1 : l.pt + 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p1 (fun l' hl' =>
    ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
  have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ pm1 (fun l' hl' =>
    ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
  have hr : star l.pt = l.pt := hre l (by simp)
  obtain ⟨-, hb, -⟩ := GlobalTheory.T.hatLetters_pass_Di_gI_boundedFactors P A d hd0
  obtain ⟨ep, epb, ec, eci, ecb, ecbi, eζ, eζi, eζb, eζbi, eG, eGi, -⟩ := hT.2.1
  have eT : L.Tprod l.pt = d.L.Tprod l.pt := by
    unfold LevelData.Tprod LevelData.Tl; rw [ep, ec, eci]
  have eTv : L.Tvprod l.pt = d.L.Tvprod l.pt := by
    unfold LevelData.Tvprod LevelData.Tvl; rw [epb, ecb, ecbi]
  have eA : L.Ar l.pt = d.L.Ar l.pt := by unfold LevelData.Ar; rw [eT]
  have eB : L.Br l.pt = d.L.Br l.pt := by unfold LevelData.Br; rw [eT]
  have eAv : L.Avr l.pt = d.L.Avr l.pt := by unfold LevelData.Avr; rw [eTv]
  have eBv : L.Bvr l.pt = d.L.Bvr l.pt := by unfold LevelData.Bvr; rw [eTv]
  have hβ : d.L.D * d.L.Dbi ∈ bmon d := Submonoid.subset_closure (by simp [bset])
  have i1 : 1 * d.L.Di * d.L.Dr = d.L.ζi := by
    rw [one_mul, LevelData.Di, mul_assoc, Dri_Dr, mul_one]
  have i2 : d.L.D * d.L.Dbi * d.L.Di * d.L.Drb = d.L.ζbi := by
    have : d.L.Di * d.L.D = 1 := by
      rw [LevelData.D, ← mul_assoc, ← one_mul d.L.Di, i1, d.L.ζi_ζ]
    rw [(hb _ hβ).2.1.eq, ← mul_assoc, this, one_mul, LevelData.Dbi, mul_assoc, Drbi_Drb, mul_one]
  have j1 : d.L.ζi * d.L.Ar l.pt = 1 * d.L.Di * d.L.Ahat l.pt := by
    rw [LevelData.Ahat, ← mul_assoc, i1]
  have j2 : d.L.ζbi * d.L.Avr l.pt = d.L.D * d.L.Dbi * d.L.Di * d.L.Ahatv l.pt := by
    rw [LevelData.Ahatv, ← mul_assoc, i2]
  have hA1 : d.L.Ahat l.pt ∈ hats d.L := by simp [hats]
  have hA2 : d.L.Ahatv l.pt ∈ hats d.L := by simp [hats]
  have hR1 : d.L.R0 l.pt ∈ hats d.L := by simp [hats]
  have hR2 : d.L.R0v l.pt ∈ hats d.L := by simp [hats]
  unfold TL.letterCol
  by_cases hp : l.plus
  · simp only [hp, if_true]
    fin_cases i
    · refine io_mem (a := TL.aP L l.pt) ?_ e e'
      rw [TL.aP, eζi, eA, j1]
      exact gen_mem d (one_mem _) hA1
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      obtain ⟨E, hE, hl⟩ := GlobalTheory.T.word_l_decomposition_nf_span P A d hd0 L st s hT S w hAw l.pt m0 m1
      rw [hl, eζbi, eG, eA, eB, kapL]
      refine col_mem ?_ (fun f f' => ?_) e e'
      · have := gen_mem d hβ hR1
        rwa [LevelData.R0, ← mul_assoc, ← mul_assoc, i2] at this
      · rw [ColumnLift.s1p, bounded_comm d (hE f f') (fun b h => (hb b h).1 _ (by simp [LevelData.fns])), mul_assoc, j1]
        exact bounded_mul_mem d (hE f f') (one_mem _) hA1
  · simp only [hp, Bool.false_eq_true, if_false]
    fin_cases i
    · refine io_mem (a := TL.aM L l.pt) ?_ e e'
      rw [TL.aM, eζbi, eAv, j2]
      exact gen_mem d hβ hA2
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      obtain ⟨E, hE, hl⟩ := GlobalTheory.T.word_m_decomposition_self_adjoint P A d hd0 L st s hT S w hAw l.pt m0 hr mm1
      rw [hl, eζi, eG, eAv, eBv]
      refine col_mem ?_ (fun f f' => ?_) e e'
      · have := gen_mem d (one_mem _) hR2
        rwa [LevelData.R0v, ← mul_assoc, ← mul_assoc, i1] at this
      · rw [ColumnLift.s1m, bounded_comm d (hE f f') (fun b h => (hb b h).1 _ (by simp [LevelData.fns])), mul_assoc, j2]
        exact bounded_mul_mem d (hE f f') hβ hA2

end GlobalTheory.HatNF.LetterEntries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormAdjointApplyOfNormPreserving
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem norm_adjoint_apply_of_norm_preserving {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (P : V →L[ℂ] V) (hP : ∀ v, ‖P v‖ = ‖v‖) (v : V) :
    ‖ContinuousLinearMap.adjoint P v‖ = ‖v‖ := by
  let L : V →ₗᵢ[ℂ] V := ⟨(P : V →ₗ[ℂ] V), hP⟩
  have hsurj : Function.Surjective (P : V →ₗ[ℂ] V) :=
    LinearMap.surjective_of_injective (f := (P : V →ₗ[ℂ] V)) L.injective
  obtain ⟨u, rfl⟩ := hsurj v
  have h1 : ContinuousLinearMap.adjoint P (P u) = u := by
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact L.inner_map_map u w
  change ‖ContinuousLinearMap.adjoint P (P u)‖ = ‖P u‖
  rw [h1, hP]

theorem norm_adjoint_of_intertwine {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (P : V →L[ℂ] V) (Q : U →L[ℂ] U) (A A' : U →L[ℂ] V) (hQ : ∀ v, ‖Q v‖ = ‖v‖)
    (h : A'.comp Q = P.comp A) (v : V) :
    ‖ContinuousLinearMap.adjoint A' v‖ = ‖ContinuousLinearMap.adjoint A (ContinuousLinearMap.adjoint P v)‖ := by
  rw [← norm_adjoint_apply_of_norm_preserving Q hQ]
  have h1 := congrArg (fun T : U →L[ℂ] V => ContinuousLinearMap.adjoint T v) h
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] at h1
  rw [h1]

theorem norm_adjoint_real_pow_smul {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (A : U →L[ℂ] V) (t : ℝ) (d : ℕ) (v : V) :
    ‖ContinuousLinearMap.adjoint (((t : ℂ) ^ d) • A) v‖ ^ 2 =
      (t ^ 2) ^ d * ‖ContinuousLinearMap.adjoint A v‖ ^ 2 := by
  rw [LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply, norm_smul, mul_pow]
  congr 1
  rw [RCLike.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, mul_comm, pow_mul, sq_abs]

theorem lower_bound_spreads :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (πp : Mx (n + 1) r → (Vp →L[ℂ] Vp)) (πm : Mx (n + 1) r → (Vm →L[ℂ] Vm)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (Ap : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vm →L[ℂ] V)) (n₀ : ℕ) (b : ℝ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πp h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πm h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → GlobalTheory.WigSh.WigMap (n + 1) r z πp π n₀ Ap → GlobalTheory.WigSh.WigMap (n + 1) r z πm π n₀ Am → (∀ v : V, ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap (B (Fin.last n))) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am (B (Fin.last n))) v‖ ^ 2)) → ∀ ω, inWb (n + 1) r ω → herm (Hpk (n + 1) r) ω z = 0 → ∀ v : V, (herm (Hpk (n + 1) r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ Vp _ _ _ Vm _ _ _ n r z π πp πm B Ap Am n₀ b hz hT hπ hπp hπm hB hAp hAm hlow ω hω hωz v
  obtain ⟨t, h, hh, -, hre, rfl⟩ :=
    (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).2 B hB ω hω hωz
  rw [hre, hAp.2.2.1, hAm.2.2.1, norm_adjoint_real_pow_smul, norm_adjoint_real_pow_smul,
    norm_adjoint_of_intertwine (π h) (πp h) _ _ (hπp h hh) (hAp.2.1 h hh _),
    norm_adjoint_of_intertwine (π h) (πm h) _ _ (hπm h hh) (hAm.2.1 h hh _)]
  have h1 := hlow (ContinuousLinearMap.adjoint (π h) v)
  rw [norm_adjoint_apply_of_norm_preserving (π h) (hπ h hh)] at h1
  have h2 : (0 : ℝ) ≤ (t ^ 2) ^ n₀ := by positivity
  calc _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormProductSpanLeftMulClosed
section
namespace GlobalTheory.HatNF.SpanMul

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem gen_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {b : A} (hb : b ∈ bmon d) (H : List A)
    (hl : H.length = n) (hT : ∀ h ∈ H, h ∈ T) :
    b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod ∈ nfSpan d T i j n :=
  Submodule.subset_span ⟨b, hb, H, hl, hT, rfl⟩

theorem map_mem (d : Q.NFData P A) (T : Set A) (i j n : ℕ) (f : A →ₗ[ℂ] A) (S : Submodule ℂ A)
    (h : ∀ b ∈ bmon d, ∀ H : List A, H.length = n → (∀ h ∈ H, h ∈ T) →
      f (b * d.L.Di ^ i * TL.gI d.L ^ j * H.prod) ∈ S) :
    ∀ x ∈ nfSpan d T i j n, f x ∈ S := by
  have : nfSpan d T i j n ≤ S.comap f := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hl, hT, rfl⟩
    exact h b hb H hl hT
  exact fun x hx => this hx

theorem bdd_mul (d : Q.NFData P A) (T : Set A) (i j n : ℕ) {b : A} (hb : b ∈ bmon d) :
    ∀ x ∈ nfSpan d T i j n, b * x ∈ nfSpan d T i j n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ b) _ ?_
  intro b' hb' H hl hT
  have := gen_mem d T i j n ((bmon d).mul_mem hb hb') H hl hT
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem di_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di) (T : Set A) (i j n : ℕ) :
    ∀ x ∈ nfSpan d T i j n, d.L.Di * x ∈ nfSpan d T (i + 1) j n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ d.L.Di) _ ?_
  intro b hb H hl hT
  have := gen_mem d T (i + 1) j n hb H hl hT
  rw [pow_succ', ← mul_assoc b, (hD b hb).eq] at this
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem gi_mul (d : Q.NFData P A) (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L))
    (hDG : Commute d.L.Di (TL.gI d.L)) (T : Set A) (i j n : ℕ) :
    ∀ x ∈ nfSpan d T i j n, TL.gI d.L * x ∈ nfSpan d T i (j + 1) n := by
  refine map_mem d T i j n (LinearMap.mulLeft ℂ (TL.gI d.L)) _ ?_
  intro b hb H hl hT
  have := gen_mem d T i (j + 1) n hb H hl hT
  rw [pow_succ', ← mul_assoc (b * _), ((hG b hb).mul_left (hDG.pow_left i)).eq] at this
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using this

theorem di_pow_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di) (T : Set A) (i j n k : ℕ) :
    ∀ x ∈ nfSpan d T i j n, d.L.Di ^ k * x ∈ nfSpan d T (i + k) j n := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact di_mul d hD T _ j n _ ih

theorem gi_pow_mul (d : Q.NFData P A) (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L))
    (hDG : Commute d.L.Di (TL.gI d.L)) (T : Set A) (i j n k : ℕ) :
    ∀ x ∈ nfSpan d T i j n, TL.gI d.L ^ k * x ∈ nfSpan d T i (j + k) n := by
  intro x hx
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact gi_mul d hG hDG T i _ n _ ih

theorem one_letter_mul (d : Q.NFData P A) (hD : ∀ b ∈ bmon d, Commute b d.L.Di)
    (hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L)) (hDG : Commute d.L.Di (TL.gI d.L)) (T T' : Set A)
    (i₀ j₀ n i j : ℕ) (u : A) (hu : ∀ X ∈ T', X * u ∈ nfSpan d T i₀ j₀ n) :
    ∀ x ∈ nfSpan d T' i j 1, x * u ∈ nfSpan d T (i₀ + i) (j₀ + j) n := by
  refine map_mem d T' i j 1 (LinearMap.mulRight ℂ u) _ ?_
  intro b hb H hl hT
  obtain ⟨X, rfl⟩ := List.length_eq_one_iff.1 hl
  have := bdd_mul d T _ _ n hb _ (di_pow_mul d hD T _ _ n i _
    (gi_pow_mul d hG hDG T _ _ n j _ (hu X (hT X (by simp)))))
  simpa only [LinearMap.mulRight_apply, mul_assoc, List.prod_cons, List.prod_nil, mul_one] using this

theorem mul_prod (d : Q.NFData P A) (T : Set A) (i j m : ℕ) (H : List A) (hT : ∀ h ∈ H, h ∈ T) :
    ∀ x ∈ nfSpan d T i j m, x * H.prod ∈ nfSpan d T i j (H.length + m) := by
  refine map_mem d T i j m (LinearMap.mulRight ℂ H.prod) _ ?_
  intro b hb H' hl hT'
  have := gen_mem d T i j (H.length + m) hb (H' ++ H) (by simp [hl, add_comm]) (by
    intro h hh
    rcases List.mem_append.1 hh with h1 | h1
    · exact hT' h h1
    · exact hT h h1)
  simpa only [LinearMap.mulRight_apply, mul_assoc, List.prod_append] using this

theorem span_mul : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ T : Set A, (∀ i j n, ∀ x ∈ nfSpan d T i j n, (∀ b ∈ bmon d, b * x ∈ nfSpan d T i j n) ∧ d.L.Di * x ∈ nfSpan d T (i + 1) j n ∧ TL.gI d.L * x ∈ nfSpan d T i (j + 1) n) ∧ ∀ a : ℕ, (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ i j n, ∀ X ∈ hats d.L, ∀ x ∈ nfSpan d T i j n, X * x ∈ nfSpan d T i (j + a) (n + 1) := by
  intro P A _ _ _ _ d hd T
  have h1 := GlobalTheory.T.hatLetter_mul_boundedFactor_mem_normalFormSpan P A d hd
  obtain ⟨h2, h3, hDG⟩ := GlobalTheory.T.hatLetters_pass_Di_gI_boundedFactors P A d hd
  have hD : ∀ b ∈ bmon d, Commute b d.L.Di := fun b hb => (h3 b hb).2.1
  have hG : ∀ b ∈ bmon d, Commute b (TL.gI d.L) := fun b hb => (h3 b hb).2.2.1
  refine ⟨fun i j n x hx => ⟨fun b hb => bdd_mul d T i j n hb x hx, di_mul d hD T i j n x hx,
    gi_mul d hG hDG T i j n x hx⟩, ?_⟩
  intro a ha i j n X hX
  refine map_mem d T i j n (LinearMap.mulLeft ℂ X) _ ?_
  intro b hb H hl hT
  have e1 : ∀ k, X * b * d.L.Di ^ k ∈ nfSpan d (hats d.L) k 0 1 := by
    intro k
    induction k with
    | zero => simpa using h1 X hX b hb
    | succ k ih =>
      have := one_letter_mul d hD hG hDG _ _ 1 0 1 k 0 _ (fun Y hY => (h2 Y hY).1) _ ih
      rw [pow_succ, ← mul_assoc, add_comm k 1]
      exact this
  have e2 : ∀ k, X * b * d.L.Di ^ i * TL.gI d.L ^ k ∈ nfSpan d (hats d.L) i k 1 := by
    intro k
    induction k with
    | zero => simpa using e1 i
    | succ k ih =>
      have := one_letter_mul d hD hG hDG _ _ 0 1 1 i k _ (fun Y hY => (h2 Y hY).2) _ ih
      rw [zero_add] at this
      rw [pow_succ, ← mul_assoc, add_comm k 1]
      exact this
  have e3 := one_letter_mul d hD hG hDG T _ 0 a (H.length + 1) i j H.prod
    (fun Y hY => mul_prod d T 0 a 1 H hT Y (ha Y hY)) _ (e2 j)
  rw [zero_add, hl, add_comm a j] at e3
  simpa only [LinearMap.mulLeft_apply, mul_assoc] using e3

end GlobalTheory.HatNF.SpanMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PullAlValueIntegralPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pullAl_value_integral_point :
    Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)), PullAl D F oa a k N s s' → ∀ (χ : D.toPre.X) (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) (r : ℚ), (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m ≫ oa.onB.act a).left ≫ DegPre.famφB D.toPre (χ) i) (DegPre.famε (k))), G₀.IsGen ∧ ∃ x : F, v x = ((r : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s.s χ) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m ≫ oa.onB.act a)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) → (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m).left ≫ DegPre.famφB D.toPre (star a • χ) i) (DegPre.famε (k * N))), G₀.IsGen ∧ ∃ x : F, v x = ((r : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s'.s (star a • χ)) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) := by
  intro hLaws V _ _ _ ϖ hϖ D Q _ F _ _ _ v hv O _ _ _ oa w0 hw a N k hN _ haa s s' hpull χ m r ⟨G₀, hG₀, x, hx, hval⟩
  have hL := D.toPre.P.isLB
  obtain ⟨u, hu, hcorr, hrel⟩ := hpull.1 χ
  obtain ⟨n, ψ, δ, eB, heB, hform, ve⟩ :=
    pullGen_one hLaws.globalFns D F oa w0 hw a N hN (by rw [mul_comm]; exact haa) k χ u hu hcorr
  have hform' : FormEq (Sum.elim (fun i => (m ≫ oa.onB.act a).left ≫ DegPre.famφB D.toPre χ i)
      (fun i => m.left ≫ ψ i)) (Sum.elim (DegPre.famε k) δ)
      (fun i => m.left ≫ DegPre.famφB D.toPre (star a • χ) i) (DegPre.famε (k * N)) := fun U _ h => by
    refine Eq.trans ?_ (hform U (fun q => h (m.left ≫ q)))
    refine Finset.prod_congr rfl ?_
    rintro (i | i) -
    · simp only [Sum.elim_inl, Over.comp_left, Category.assoc]
    · rfl
  obtain ⟨G₁, hG₁, vG⟩ := exists_gen hL hform'
    (LB.mulGen D.toPre.P.L _ _ _ _ G₀ (LB.pullGen D.toPre.P.L _ _ eB m.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hG₀ (DVR.pullGen_isGen _ _ _ _ heB _))
  refine ⟨G₁, hG₁, x, hx, fun z J hJ => ?_⟩
  have H := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _
    (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J hJ
  have e₁ : (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left ≫ (aF D F oa a).left =
      (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m ≫ oa.onB.act a)).left := by
    rw [← Over.comp_left, aF, comp_lift, lift_fst, ← Category.assoc, lift_snd, Category.assoc]
  have e₂ : (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left ≫ (DegPre.prB D.toPre F).left =
      (TWM.ιS hϖ hv).left ≫ m.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  rw [H, e₁, hval z J hJ, ve _ _ z J hJ, e₂, vG _ _ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul, _root_.mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureIntegralRmulBesselGroupStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_integral_rmul_besselGroup : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F : Mx k r → ℂ), SideG k r z π u μW μN μG νq → ContinuousOn F (GG k r) → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x) → Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) νq → ∀ g ∈ GG k r, ∫ x, F ((Matrix.of x) * g) ∂νq = ∫ x, F (Matrix.of x) ∂νq := by
  first | exact @GlobalTheory.quot_integral_rmul | exact GlobalTheory.quot_integral_rmul | (intros; apply GlobalTheory.quot_integral_rmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBoundedStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ f : M.Ty P → ℂ, PtAdj P Bs (d.κ f) ∧ PtB P Bs (d.κ f) := by
  first | exact @GlobalTheory.HatNF.kappa_ptAdj_ptB | exact GlobalTheory.HatNF.kappa_ptAdj_ptB | (intros; apply GlobalTheory.HatNF.kappa_ptAdj_ptB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrepStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_raw_of_frep : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ I c y, (RI I).KFin y → R.KFin (io I c y)) ∧ (∀ I c x, R.KFin x → (RI I).KFin (pr I c x)) ∧ (∀ I c, ∀ y ∈ (RI I).TK, io I c y ∈ R.TK) ∧ (∀ I c, ∀ x ∈ R.TK, pr I c x ∈ (RI I).TK) := by
  first | exact @GlobalTheory.tensor_decomposition_kfinite | exact GlobalTheory.tensor_decomposition_kfinite | (intros; apply GlobalTheory.tensor_decomposition_kfinite <;> assumption)
end

