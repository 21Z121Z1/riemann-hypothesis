import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0122
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockSource
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetOnStableSubspaceExpSmul
section
open Matrix

namespace GlobalTheory.FlagMeas

theorem detOn_exp_smul : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)),
    (∀ y ∈ V, A *ᵥ y ∈ V) → ∃ c : ℝ, ∀ t : ℝ,
      GlobalTheory.FlagMeas.detOn (NormedSpace.exp (t • A)) V = Real.exp (t * c) := by
  intro n A V hA
  have hA' : ∀ y ∈ V, Matrix.toLin' A y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hA y hy
  set f : V →ₗ[ℂ] V := (Matrix.toLin' A).restrict hA' with hf
  set b := Module.finBasis ℂ V with hb
  set B := LinearMap.toMatrixAlgEquiv b f with hB
  refine ⟨(B.trace).re, fun t => ?_⟩
  have hts : t • A = (t : ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [hts]
  set s : ℂ := (t : ℂ) with hs
  have hpowA : ∀ (k : ℕ) (v : V), (s • A) ^ k *ᵥ (v : Fin n → ℂ) = (((s • f) ^ k) v : Fin n → ℂ) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih, Module.End.mul_apply]
      simp [hf, LinearMap.restrict_apply, Matrix.toLin'_apply, Matrix.smul_mulVec]
  have hpowB : ∀ k : ℕ, Matrix.toLinAlgEquiv b ((s • B) ^ k) = (s • f) ^ k := by
    intro k
    rw [map_pow, map_smul, hB, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
  have key : ∀ v : V, NormedSpace.exp (s • A) *ᵥ (v : Fin n → ℂ) =
      ((Matrix.toLinAlgEquiv b (NormedSpace.exp (s • B))) v : Fin n → ℂ) := by
    intro v
    open scoped Matrix.Norms.Operator in
    have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • A)
    open scoped Matrix.Norms.Operator in
    have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • B)
    let g1 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
      LinearMap.applyₗ (v : Fin n → ℂ) ∘ₗ Matrix.toLin'.toLinearMap
    let g2 : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
      V.subtype ∘ₗ LinearMap.applyₗ v ∘ₗ (Matrix.toLinAlgEquiv b).toLinearMap
    have h1' := h1.map g1 (LinearMap.continuous_of_finiteDimensional g1)
    have h2' := h2.map g2 (LinearMap.continuous_of_finiteDimensional g2)
    have heq : (g1 ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (s • A) ^ k) =
        (g2 ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (s • B) ^ k) := by
      funext k
      simp only [Function.comp_apply, map_smul, g1, g2, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        LinearEquiv.coe_coe, Matrix.toLin'_apply, AlgEquiv.toLinearMap_apply, Submodule.subtype_apply]
      rw [hpowA, hpowB]
    rw [heq] at h1'
    exact h1'.unique h2'
  have hstab : ∀ y ∈ V, Matrix.toLin' (NormedSpace.exp (s • A)) y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply, key ⟨y, hy⟩]; exact Submodule.coe_mem _
  have hres : (Matrix.toLin' (NormedSpace.exp (s • A))).restrict hstab =
      Matrix.toLinAlgEquiv b (NormedSpace.exp (s • B)) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [LinearMap.restrict_coe_apply, Matrix.toLin'_apply]
    exact key v
  rw [detOn, dif_pos hstab, hres]
  show ‖LinearMap.det (Matrix.toLin b b (NormedSpace.exp (s • B)))‖ = _
  rw [LinearMap.det_toLin, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, smul_eq_mul, Complex.norm_exp, hs,
    Complex.re_ofReal_mul]

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseRangeFiniteVectorsDiscreteSeries
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section
namespace GlobalTheory.AnalyticDense
open GlobalTheory.FockTensor

theorem inner_orbit_eq_zero {p q : ℕ} {T : GrpData p q} (D : DSRep T) {Y : Mat p q}
    (hY : Y ∈ upq p q) (y : D.HK.V) {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (w : D.U.H) (hw : ∀ v, inner ℂ w (D.ι v) = 0) (t : ℝ) :
    inner ℂ w (D.U.π (T.expt (t • Y)) (D.ι y)) = 0 := by

  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ → ℂ, g = fun k s =>
      inner ℂ w (D.U.π (T.expt (s • Y)) (D.ι ((D.HK.act Y ^ k) y))) := ⟨_, rfl⟩
  have hd : ∀ k s, HasDerivAt (g k) (g (k + 1) s) s := by
    intro k s
    have h1 := hasDerivAt_orbit D.U hY (D.der Y hY ((D.HK.act Y ^ k) y)) s
    have h2 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    have e : (D.HK.act Y ^ (k + 1)) y = D.HK.act Y ((D.HK.act Y ^ k) y) := by
      rw [pow_succ']; rfl
    subst hg
    simp only [e]
    exact h2

  have hb' : ∀ k s, ‖g k s‖ ≤ (‖w‖ * C) * ρ ^ k * (k.factorial : ℝ) := by
    intro k s
    subst hg
    calc ‖inner ℂ w (D.U.π (T.expt (s • Y)) (D.ι ((D.HK.act Y ^ k) y)))‖
        ≤ ‖w‖ * ‖D.U.π (T.expt (s • Y)) (D.ι ((D.HK.act Y ^ k) y))‖ := norm_inner_le_norm _ _
      _ = ‖w‖ * ‖D.ι ((D.HK.act Y ^ k) y)‖ := by rw [D.U.isom]
      _ ≤ ‖w‖ * (C * ρ ^ k * (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left (hb k) (norm_nonneg w)
      _ = ‖w‖ * C * ρ ^ k * (k.factorial : ℝ) := by ring

  have h0 : ∀ k, g k 0 = 0 := by
    intro k
    subst hg
    simp only [zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply]
    exact hw _
  have key := GlobalTheory.FactorialJet.eq_zero_of_factorial_bound ℂ g (‖w‖ * C) ρ
    (mul_nonneg (norm_nonneg w) hC) hρ hd hb' h0 0 t
  subst hg
  simpa using key

theorem orbit_mem_closure {p q : ℕ} {T : GrpData p q} (D : DSRep T) {Y : Mat p q}
    (hY : Y ∈ upq p q)
    (hb : ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (t : ℝ) (x : D.U.H) (hx : x ∈ (LinearMap.range D.ι).topologicalClosure) :
    D.U.π (T.expt (t • Y)) x ∈ (LinearMap.range D.ι).topologicalClosure := by

  have hsub : LinearMap.range D.ι ≤ (LinearMap.range D.ι).topologicalClosure.comap
      ((D.U.π (T.expt (t • Y)) : D.U.H →L[ℂ] D.U.H) : D.U.H →ₗ[ℂ] D.U.H) := by
    intro z hz
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hz
    obtain ⟨C, ρ, hC, hρ, hk⟩ := hb v
    rw [Submodule.mem_comap, ← Submodule.orthogonal_orthogonal_eq_closure,
      Submodule.mem_orthogonal]
    intro u hu
    rw [ContinuousLinearMap.coe_coe]
    exact inner_orbit_eq_zero D hY v hC hρ hk u
      (fun z => (Submodule.mem_orthogonal' _ _).1 hu _ (LinearMap.mem_range_self _ z)) t
  have hcl : IsClosed (((LinearMap.range D.ι).topologicalClosure.comap
      ((D.U.π (T.expt (t • Y)) : D.U.H →L[ℂ] D.U.H) : D.U.H →ₗ[ℂ] D.U.H) :
        Submodule ℂ D.U.H) : Set D.U.H) :=
    (Submodule.isClosed_topologicalClosure _).preimage (D.U.π _).continuous
  exact Submodule.topologicalClosure_minimal _ hsub hcl hx

theorem dense_range_of_factorial_bound : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q)
    (D : DSRep T), Nontrivial D.HK.V →
    (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) →
    Dense (Set.range D.ι) := by
  intro p q hpq T D hnt hb

  have hgen : ∀ g ∈ T.expt '' upq p q, ∀ x ∈ (LinearMap.range D.ι).topologicalClosure,
      D.U.π g x ∈ (LinearMap.range D.ι).topologicalClosure ∧
      D.U.π g⁻¹ x ∈ (LinearMap.range D.ι).topologicalClosure := by
    rintro _ ⟨Y, hY, rfl⟩ x hx
    have hneg : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have h := T.expt_add Y hY (-1) 1
      have e : ((-1 : ℝ) + 1) = 0 := by norm_num
      rw [e, zero_smul, T.expt_zero, one_smul] at h
      exact (eq_inv_of_mul_eq_one_left h.symm).symm
    refine ⟨?_, ?_⟩
    · have h1 := orbit_mem_closure D hY (hb Y hY) 1 x hx
      rwa [one_smul] at h1
    · rw [hneg]
      exact orbit_mem_closure D hY (hb Y hY) (-1) x hx

  have hall : ∀ g : T.G, ∀ x ∈ (LinearMap.range D.ι).topologicalClosure,
      D.U.π g x ∈ (LinearMap.range D.ι).topologicalClosure ∧
      D.U.π g⁻¹ x ∈ (LinearMap.range D.ι).topologicalClosure := by
    intro g
    have hg : g ∈ Subgroup.closure (T.expt '' upq p q) := by
      rw [(GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hpq T).1]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem a ha => exact hgen a ha
    | one =>
      intro x hx
      rw [inv_one, map_one, ContinuousLinearMap.one_apply]
      exact ⟨hx, hx⟩
    | mul a b _ _ ha hb' =>
      intro x hx
      refine ⟨?_, ?_⟩
      · rw [map_mul, ContinuousLinearMap.mul_apply]
        exact (ha _ (hb' x hx).1).1
      · rw [mul_inv_rev, map_mul, ContinuousLinearMap.mul_apply]
        exact (hb' _ (ha x hx).2).2
    | inv a _ ha =>
      intro x hx
      rw [inv_inv]
      exact ⟨(ha x hx).2, (ha x hx).1⟩

  rcases D.3 _ (Submodule.isClosed_topologicalClosure _) (fun g x hx => (hall g x hx).1) with h | h
  · exfalso
    obtain ⟨v, hv⟩ := exists_ne (0 : D.HK.V)
    have h1 : D.ι v ∈ (LinearMap.range D.ι).topologicalClosure :=
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ v)
    rw [h, Submodule.mem_bot] at h1
    exact hv (D.9 (h1.trans (map_zero D.ι).symm))
  · have e : ((LinearMap.range D.ι : Submodule ℂ D.U.H) : Set D.U.H) = Set.range D.ι := by
      ext z
      simp
    rw [← e]
    exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

end GlobalTheory.AnalyticDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsometryIntertwinerOfDerivedAction
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FockTensor

private theorem J_pi_expt_iota_eq {p q : ℕ} {T : GrpData p q} (D : DSRep T) (πU : URep T)
    (E : D.HK.V →ₗ[ℂ] πU.H) (J : D.U.H →L[ℂ] πU.H) (hJ : ∀ y, J (D.ι y) = E y)
    (hder : ∀ Y ∈ upq p q, ∀ y, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E y))
      (E (D.HK.act Y y)) 0)
    (hn : ∀ y, ‖E y‖ = ‖D.ι y‖) (hJn : ∀ x, ‖J x‖ = ‖x‖)
    (hb : ∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    {Y : Mat p q} (hY : Y ∈ upq p q) (y : D.HK.V) (t : ℝ) :
    J (D.U.π (T.expt (t • Y)) (D.ι y)) = πU.π (T.expt (t • Y)) (E y) := by
  obtain ⟨C, ρ, hC, hρ, hk⟩ := hb Y hY y
  set A := D.HK.act Y with hA
  have hpow : ∀ k : ℕ, (A ^ (k + 1)) y = A ((A ^ k) y) := fun k => by
    rw [pow_succ', Module.End.mul_apply]
  let g : ℕ → ℝ → πU.H := fun k s =>
    πU.π (T.expt (s • Y)) (E ((A ^ k) y)) - J (D.U.π (T.expt (s • Y)) (D.ι ((A ^ k) y)))
  have key : ∀ k s, g k s = 0 := by
    refine GlobalTheory.T.eq_zero_of_factorial_bound_of_vanish_at_zero πU.H g (2 * C) ρ (by linarith) hρ ?_ ?_ ?_
    · intro k s
      have h1 := hasDerivAt_orbit πU hY (hder Y hY ((A ^ k) y)) s
      have h2 := hasDerivAt_orbit D.U hY (D.11 Y hY ((A ^ k) y)) s
      have h3 := (J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2
      have h4 := h1.sub h3
      have hsucc : g (k + 1) s = πU.π (T.expt (s • Y)) (E (A ((A ^ k) y))) -
          J (D.U.π (T.expt (s • Y)) (D.ι (A ((A ^ k) y)))) := by
        simp only [g, hpow]
      rw [hsucc]
      exact h4
    · intro k s
      have e1 : ‖πU.π (T.expt (s • Y)) (E ((A ^ k) y))‖ = ‖D.ι ((A ^ k) y)‖ := by
        rw [πU.6, hn]
      have e2 : ‖J (D.U.π (T.expt (s • Y)) (D.ι ((A ^ k) y)))‖ = ‖D.ι ((A ^ k) y)‖ := by
        rw [hJn, D.U.6]
      calc ‖g k s‖ ≤ ‖πU.π (T.expt (s • Y)) (E ((A ^ k) y))‖ +
            ‖J (D.U.π (T.expt (s • Y)) (D.ι ((A ^ k) y)))‖ := norm_sub_le _ _
        _ = 2 * ‖D.ι ((A ^ k) y)‖ := by rw [e1, e2]; ring
        _ ≤ 2 * (C * ρ ^ k * (k.factorial : ℝ)) := by gcongr; exact hk k
        _ = 2 * C * ρ ^ k * (k.factorial : ℝ) := by ring
    · intro k
      simp only [g, zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply, hJ, sub_self]
  have h0 := key 0 t
  simp only [g, pow_zero, Module.End.one_apply] at h0
  exact (sub_eq_zero.mp h0).symm

theorem exists_isometry_intertwiner_of_derived :
    ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (D : DSRep T) (πU : URep T) (E : D.HK.V →ₗ[ℂ] πU.H), Dense (Set.range D.ι) → (∀ y, ‖E y‖ = ‖D.ι y‖) → (∀ Y ∈ upq p q, ∀ y, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E y)) (E (D.HK.act Y y)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ j : D.U.H →ₗᵢ[ℂ] πU.H, (∀ y, j (D.ι y) = E y) ∧ ∀ g x, j (D.U.π g x) = πU.π g (j x) := by
  intro p q hpq T D πU E hd hn hder hb
  let J : D.U.H →L[ℂ] πU.H := E.extendOfNorm D.ι
  have hJ : ∀ y, J (D.ι y) = E y := fun y =>
    LinearMap.extendOfNorm_eq hd ⟨1, fun x => by rw [hn, one_mul]⟩ y
  have hJn : ∀ x, ‖J x‖ = ‖x‖ := by
    have hfun := Continuous.ext_on hd (f := fun x => ‖J x‖) (g := fun x => ‖x‖)
      J.continuous.norm continuous_norm (by
        rintro _ ⟨y, rfl⟩
        show ‖J (D.ι y)‖ = ‖D.ι y‖
        rw [hJ, hn])
    exact fun x => congrFun hfun x
  have hexp : ∀ Y ∈ upq p q, ∀ x, J (D.U.π (T.expt Y) x) = πU.π (T.expt Y) (J x) := by
    intro Y hY
    have hfun := Continuous.ext_on hd (f := fun x => J (D.U.π (T.expt Y) x))
      (g := fun x => πU.π (T.expt Y) (J x))
      (J.continuous.comp (D.U.π (T.expt Y)).continuous)
      ((πU.π (T.expt Y)).continuous.comp J.continuous) (by
        rintro _ ⟨y, rfl⟩
        have h := J_pi_expt_iota_eq D πU E J hJ hder hn hJn hb hY y 1
        simp only [one_smul] at h
        show J (D.U.π (T.expt Y) (D.ι y)) = πU.π (T.expt Y) (J (D.ι y))
        rw [hJ]
        exact h)
    exact fun x => congrFun hfun x
  have cancelU : ∀ (a : T.G) (z : πU.H), πU.π a⁻¹ (πU.π a z) = z := by
    intro a z
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have cancelD : ∀ (a : T.G) (z : D.U.H), D.U.π a (D.U.π a⁻¹ z) = z := by
    intro a z
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let S : Subgroup T.G :=
    { carrier := {a | ∀ x, J (D.U.π a x) = πU.π a (J x)}
      one_mem' := by
        simp only [Set.mem_setOf_eq, map_one, ContinuousLinearMap.one_apply, implies_true]
      mul_mem' := by
        intro a b ha hb' x
        simp only [Set.mem_setOf_eq] at ha hb'
        simp only [map_mul, ContinuousLinearMap.mul_apply]
        rw [ha, hb']
      inv_mem' := by
        intro a ha x
        simp only [Set.mem_setOf_eq] at ha
        have h1 := ha (D.U.π a⁻¹ x)
        rw [cancelD] at h1
        rw [h1, cancelU] }
  have hle : Subgroup.closure (T.expt '' upq p q) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨Y, hY, rfl⟩
    exact hexp Y hY
  have hall : ∀ a : T.G, a ∈ S := fun a =>
    hle ((GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hpq T).1 ▸ Subgroup.mem_top a)
  refine ⟨{ toLinearMap := J.toLinearMap, norm_map' := hJn }, hJ, ?_⟩
  intro a x
  exact hall a x

end GlobalTheory.FockTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactDetSqrtCoverMaxCompactStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_detSqrtCover_maxCompact : ∀ (p q : ℕ) (T : GrpData p q), IsCompact T.Kset := by
  first | exact @GlobalTheory.PolarU.isCompact_Kset | exact GlobalTheory.PolarU.isCompact_Kset | (intros; apply GlobalTheory.PolarU.isCompact_Kset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.SmallerSource

theorem discrete_series_gk_admissible_irreducible (X : ProvA) (h5 : admQ5 X) {r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) :
    AdmGK (X.ds r s lam).HK ∧ IrrGK (X.ds r s lam).HK := by
  obtain ⟨hU, -, -⟩ := h5 r s hrs
  set D := X.ds r s lam
  exact (hU D.U ⟨D.nontriv, D.irred⟩).2.2 D.HK D.ι ⟨D.ι_inj, D.ι_range, D.der⟩

theorem cPair_sub {p q i : ℕ} (hp : i ≤ p) (hq : i ≤ q) : cPair (p - i) (q - i) = cPair p q := by
  unfold cPair
  rw [Nat.cast_sub hp, Nat.cast_sub hq]
  ring

theorem intw_eq_zero (X : ProvA) (h2 : admH2 X) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam))
    (MM : GKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam).HK.V)
    (hf : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK f) : f = 0 := by
  by_contra hf0

  have hAI := discrete_series_gk_admissible_irreducible X h5 hrs lam
  have hI : Intw MM (X.ds r s lam).HK f := (isIntw_iff (X.fock p q r s) MM _ f).1 hf
  obtain ⟨hfin, -, hcone⟩ := hD r s lam hlam

  have hex : ∃ v, IsHW (X.ds r s lam).HK.act (blattner lam) v := by
    have hne : hwSub (X.ds r s lam).HK.act (blattner lam) ≠ ⊥ := by
      intro h
      rw [h] at hfin
      simp at hfin
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨v, hv0, hv⟩

  have hmin : ∀ ν w, IsHW (X.ds r s lam).HK.act ν w →
      degW (cPair p q) (blattner lam) ≤ degW (cPair p q) ν :=
    GlobalTheory.T.degW_blattner_le_of_blattnerCone r s (X.ds r s lam).HK lam (cPair p q) θ hcone hsign

  obtain ⟨⟨μ, P, hPJ, hP1, hP2, hfP⟩, -⟩ :=
    GlobalTheory.T.fock_minimal_KType_second_member p q r s MM (X.ds r s lam).HK f hAI.2 hAI.1 hI hf0 (blattner lam) hex hmin

  have hbot := ((h2 p q r s).2.2.2.2.1 μ (blattner lam)).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 μ ⊓ hwSub (X.fock p q r s).act2 (blattner lam) ⊓
      Submodule.span ℂ (X.fock p q r s).J := by
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hP1.2, hP2.2⟩, ?_⟩
    rw [J_eq (X.fock p q r s)]
    exact Submodule.subset_span hPJ
  rw [hbot] at hmem
  exact hP1.1 ((Submodule.mem_bot ℂ).1 hmem)

theorem no_map_smaller_source :
    ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  intro X _ h2 hD h5
  unfold ArchimedeanRallisFifth ARv DataAR DataARm
  constructor
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, -, hlam', -, hs'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
    have hno := ((GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi1).2.2 hne hip hiq).1
    refine intw_eq_zero X h2 hD h5 (by omega) (lamA' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, hlam', -, hs'⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
    have hno := ((GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi1).2.2 hne hip hiq).2
    refine intw_eq_zero X h2 hD h5 (by omega) (lamM' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'

end GlobalTheory.SmallerSource
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockSourceStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_invariant_pairing_smaller_fock_source : ∀ X : ProvA, admQ5 X → ArchimedeanRallisFifth X → ∀ (t : ℕ) (al be ga de : List ℚ), DataAR t al be ga de → (∀ e ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |e|) → ∀ i : ℕ, 1 ≤ i → i ≤ al.length + be.length → i ≤ ga.length + de.length → ∀ b : Pol (al.length + be.length - i) (ga.length + de.length - i) _ _ →ₗ[ℂ] (X.ds _ _ (lamA' t al be ga de)).HK.V →ₛₗ[starRingEnd ℂ] ℂ, (∀ Z ∈ upq _ _, ∀ P y, b (fockAct2 _ _ _ _ Z P) y + b P ((X.ds _ _ (lamA' t al be ga de)).HK.act Z y) = 0) → b = 0 := by
  first | exact @GlobalTheory.NoInvPairing.no_pairing_smaller_source | exact GlobalTheory.NoInvPairing.no_pairing_smaller_source | (intros; apply GlobalTheory.NoInvPairing.no_pairing_smaller_source <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexTwoBlockParahoricConjTorusDiagElementStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_twoBlockParahoric_conj_torusDiagElement : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℝ) := by
  first | exact @GlobalTheory.ParIdx.relIndex_parahoric_conj_mtor | exact GlobalTheory.ParIdx.relIndex_parahoric_conj_mtor | (intros; apply GlobalTheory.ParIdx.relIndex_parahoric_conj_mtor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
section
noncomputable section

open Classical

namespace GlobalTheory.LevelVecNorm

def locH {E : Type} [Field E] [NumberField E] (Pg : Finset (Formalism.L2.DIV.Pl E)) {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP.1))) (PP : Formalism.L2.DIV.Pl E) :
    Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP)) :=
  if h : PP ∈ Pg then Hl ⟨PP, h⟩ else ⊤

open Classical in

def suppInd {k : Type} [CommRing k] (r : ℕ) {b a : ℕ} (H : Subgroup (GL (Fin r) k)) (z : Matrix (Fin b) (Fin a) k) : ℝ :=
  if Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z then 1 else 0

end GlobalTheory.LevelVecNorm

end
end

