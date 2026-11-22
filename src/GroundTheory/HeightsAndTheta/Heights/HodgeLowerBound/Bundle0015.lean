import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTwinFlagGenPtScale
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

namespace FlagGenericPointScale

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {R : Type} [CommRing R]

def scaleHom (D : ComponentData II Ψ K ι Ω E) (s : K ⊕ (Ψ × Fin (D.N - 1)) → R) :
    MvPolynomial (GV D) R →ₐ[R] MvPolynomial (GV D) R :=
  aeval (Sum.elim (fun β => C (s β) * X (Sum.inl β)) (fun g => X (Sum.inr g)))

omit [DecidableEq Ψ] in
theorem scaleHom_X_inl (D : ComponentData II Ψ K ι Ω E) (s : K ⊕ (Ψ × Fin (D.N - 1)) → R) (β) :
    scaleHom D s (X (Sum.inl β)) = C (s β) * X (Sum.inl β) := by
  simp [scaleHom]

omit [DecidableEq Ψ] in
theorem scaleHom_X_inr (D : ComponentData II Ψ K ι Ω E) (s : K ⊕ (Ψ × Fin (D.N - 1)) → R) (g) :
    scaleHom D s (X (Sum.inr g)) = X (Sum.inr g) := by
  simp [scaleHom]

omit [DecidableEq Ψ] in
theorem scaleHom_C (D : ComponentData II Ψ K ι Ω E) (s : K ⊕ (Ψ × Fin (D.N - 1)) → R) (c : R) :
    scaleHom D s (C c) = C c := by
  simp [scaleHom]

omit [DecidableEq Ψ] in

theorem scaleHom_scaleHom (D : ComponentData II Ψ K ι Ω E) (s t : K ⊕ (Ψ × Fin (D.N - 1)) → R)
    (h : ∀ β, t β * s β = 1) (p : MvPolynomial (GV D) R) : scaleHom D s (scaleHom D t p) = p := by
  have : (scaleHom D s).comp (scaleHom D t) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    rintro (β | g)
    · simp only [AlgHom.comp_apply, scaleHom_X_inl, map_mul, scaleHom_C, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, h, C_1, one_mul]
    · simp [scaleHom_X_inr]
  exact AlgHom.congr_fun this p

omit [DecidableEq Ψ] in

theorem scaleHom_genPtR {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) (x : (Σ k, ι k) → R)
    (V : WedgeVals Pl R) (α : K ⊕ (Ψ × Fin (D.N - 1)) → R) (j : Σ k, Pl.ιY k) :
    scaleHom D α (genPtR Pl x V j) =
      genPtR Pl (fun p => α (Sum.inl p.1) * x p) (fun q m c => α (Sum.inr q) * V q m c) j := by
  rcases j with ⟨k | q, t⟩
  · show scaleHom D α (X (Sum.inl (Sum.inl k)) * C (x ⟨k, t⟩)) =
      X (Sum.inl (Sum.inl k)) * C (α (Sum.inl k) * x ⟨k, t⟩)
    rw [map_mul, scaleHom_X_inl, scaleHom_C, C_mul, mul_assoc]
    exact mul_left_comm _ _ _
  · show scaleHom D α (X (Sum.inl (Sum.inr q)) * ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
        (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c)) =
      X (Sum.inl (Sum.inr q)) * ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
        (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (α (Sum.inr q) * V q t c)
    have hs : (∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
        (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (α (Sum.inr q) * V q t c) :
          MvPolynomial (GV D) R) =
        C (α (Sum.inr q)) * ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
          (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [C_mul, mul_left_comm]
    have hterm : ∀ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
        scaleHom D α ((∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c)) =
          (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c) := fun c => by
      rw [map_mul, map_prod, scaleHom_C]
      simp only [scaleHom_X_inr]
    rw [hs, map_mul, scaleHom_X_inl, map_sum, Finset.sum_congr rfl fun c _ => hterm c, mul_assoc]
    exact mul_left_comm _ _ _

end FlagGenericPointScale

open FlagGenericPointScale in

theorem FlagGenericPointScale.proof : FlagGenericPointScale.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl R _ x V α hα F
  have key : aeval (genPtR Pl (fun p => α (Sum.inl p.1) * x p) (fun q m c => α (Sum.inr q) * V q m c)) F =
      scaleHom D α (aeval (genPtR Pl x V) F) := by
    have := comp_aeval_apply (f := genPtR Pl x V) ((scaleHom D α).restrictScalars ℤ) F
    rw [AlgHom.restrictScalars_apply] at this
    rw [this]
    exact congrArg (fun f => aeval f F) (funext fun j => by
      rw [AlgHom.restrictScalars_apply, scaleHom_genPtR])
  rw [key]
  let t : K ⊕ (Ψ × Fin (D.N - 1)) → R := fun β => ((hα β).unit⁻¹ : Rˣ)
  have ht : ∀ β, α β * t β = 1 := fun β => (hα β).mul_val_inv
  constructor
  · intro h0
    rw [← scaleHom_scaleHom D t α ht (aeval (genPtR Pl x V) F), h0, map_zero]
  · intro h0
    rw [h0, map_zero]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTwinFlagGenPtValue
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

namespace FlagGenericPointValue

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem isValueAt_zero (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt y 0 z 0 := by
  simpa using isValueAt_intCast y z 0

theorem isValueAt_sum {α : Type*} (s : Finset α) {f : α → Ω} {g : α → ℂ}
    (h : ∀ a ∈ s, IsValueAt y (f a) z (g a)) : IsValueAt y (∑ a ∈ s, f a) z (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_zero y z
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact isValueAt_add (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

variable {σ : Type}

theorem valPoly_X (s : σ) : ValPoly y z (X s : MvPolynomial σ Ω) (X s) := by
  classical
  intro μ
  rw [coeff_X, coeff_X]
  split_ifs
  · simpa using isValueAt_intCast y z 1
  · exact isValueAt_zero y z

theorem valPoly_C {a : Ω} {v : ℂ} (h : IsValueAt y a z v) :
    ValPoly y z (C a : MvPolynomial σ Ω) (C v) := by
  classical
  intro μ
  rw [coeff_C, coeff_C]
  split_ifs
  · exact h
  · exact isValueAt_zero y z

omit [Fintype K] in

theorem valPoly_add {A A' : MvPolynomial σ Ω} {B B' : MvPolynomial σ ℂ} (h : ValPoly y z A B)
    (h' : ValPoly y z A' B') : ValPoly y z (A + A') (B + B') := fun μ => by
  rw [coeff_add, coeff_add]
  exact isValueAt_add (h μ) (h' μ)

theorem valPoly_mul {A A' : MvPolynomial σ Ω} {B B' : MvPolynomial σ ℂ} (h : ValPoly y z A B)
    (h' : ValPoly y z A' B') : ValPoly y z (A * A') (B * B') := fun μ => by
  classical
  rw [coeff_mul, coeff_mul]
  exact isValueAt_sum _ fun p _ => isValueAt_mul (h p.1) (h' p.2)

theorem valPoly_one : ValPoly y z (1 : MvPolynomial σ Ω) 1 := by
  simpa using valPoly_C (σ := σ) (isValueAt_intCast y z 1)

theorem valPoly_zero : ValPoly y z (0 : MvPolynomial σ Ω) 0 := fun μ => by
  simpa using isValueAt_zero y z

theorem valPoly_sum {α : Type*} (s : Finset α) {A : α → MvPolynomial σ Ω} {B : α → MvPolynomial σ ℂ}
    (h : ∀ a ∈ s, ValPoly y z (A a) (B a)) : ValPoly y z (∑ a ∈ s, A a) (∑ a ∈ s, B a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valPoly_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact valPoly_add (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem valPoly_prod {α : Type*} (s : Finset α) {A : α → MvPolynomial σ Ω} {B : α → MvPolynomial σ ℂ}
    (h : ∀ a ∈ s, ValPoly y z (A a) (B a)) : ValPoly y z (∏ a ∈ s, A a) (∏ a ∈ s, B a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valPoly_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact valPoly_mul (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem proof : FlagGenericPointValue.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl z x x' V V' hx hV j
  obtain ⟨k | q, t⟩ := j
  · exact valPoly_mul (valPoly_X _) (valPoly_C (hx _))
  · exact valPoly_mul (valPoly_X _) (valPoly_sum _ fun c _ =>
      valPoly_mul (valPoly_prod _ fun a _ => valPoly_X _) (valPoly_C (hV q t c)))

end FlagGenericPointValue

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTwinFlagGenericPoint
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Cardinal

theorem FlagGenericPoint.proof : FlagGenericPoint.Statement := by
  intro K _ ι _ P d hP
  obtain ⟨_, ⟨hprime, -, hrel⟩, hhor, -⟩ := hP
  have := hprime
  let Q := MRing ι ⧸ P
  let F := FractionRing Q
  have hQ : Function.Injective (algebraMap ℤ Q) := by
    have e : algebraMap ℤ Q = (Ideal.Quotient.mk P).comp C := RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    have hn0 : (C n : MRing ι) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hn
    have hn' : n ∈ P.comap (C : ℤ →+* MRing ι) := hn0
    rw [IsHorizontal] at hhor
    rw [hhor] at hn'
    exact (Ideal.mem_bot).mp hn'
  have : CharZero Q := charZero_of_injective_algebraMap hQ
  have : CharZero F := charZero_of_injective_algebraMap (R := Q) (IsFractionRing.injective Q F)
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (mk_int.le.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := HilbertSamuel.exists_ringHom_complex_of_charZero F hcard
  let φ : MRing ι →+* ℂ := (ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P)
  have hker : ∀ f, φ f = 0 ↔ f ∈ P := by
    intro f
    have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
      ψ.injective.comp (IsFractionRing.injective Q F)
    rw [show φ f = (ψ.comp (algebraMap Q F)) (Ideal.Quotient.mk P f) from rfl,
      map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]
  let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
  have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ f := by
    intro f
    have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · exact RingHom.congr_fun
          (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C) (φ.comp C)) r
      · simp [z]
    exact RingHom.congr_fun h f
  refine ⟨z, ⟨fun k => ?_, fun f hf => ?_⟩, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hrel k
    exact ⟨i, fun h => hi ((hker _).mp h)⟩
  · rw [hev]
    exact (hker f).mpr hf
  · exact (hker f).mp (by rw [← hev]; exact hf)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTwinFlagPolyValue
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

namespace FlagPolynomialValue

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isValueAt_zero (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt y (0 : Ω) z (0 : ℂ) := by
  simpa using isValueAt_intCast y z 0

theorem isValueAt_sum {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {α : Type} (s : Finset α) (f : α → Ω)
    (g : α → ℂ) (h : ∀ a ∈ s, IsValueAt y (f a) z (g a)) :
    IsValueAt y (∑ a ∈ s, f a) z (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_zero y z
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact isValueAt_add (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

omit [Fintype K] in

theorem valPoly_add {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {σ : Type} {P P' : MvPolynomial σ Ω}
    {Q Q' : MvPolynomial σ ℂ} (h : ValPoly y z P Q) (h' : ValPoly y z P' Q') :
    ValPoly y z (P + P') (Q + Q') := fun μ => by
  rw [coeff_add, coeff_add]; exact isValueAt_add (h μ) (h' μ)

theorem valPoly_mul {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {σ : Type} {P P' : MvPolynomial σ Ω}
    {Q Q' : MvPolynomial σ ℂ} (h : ValPoly y z P Q) (h' : ValPoly y z P' Q') :
    ValPoly y z (P * P') (Q * Q') := fun μ => by
  classical
  rw [coeff_mul, coeff_mul]
  exact isValueAt_sum _ _ _ fun x _ => isValueAt_mul (h x.1) (h' x.2)

theorem valPoly_intC (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) {σ : Type} (n : ℤ) :
    ValPoly y z (C (n : Ω) : MvPolynomial σ Ω) (C (n : ℂ)) := fun μ => by
  classical
  rw [coeff_C, coeff_C]
  split_ifs
  · exact isValueAt_intCast y z n
  · exact isValueAt_zero y z

theorem proof : FlagPolynomialValue.Statement := by
  intro K _ ι _ Ω _ y z σ κ A B hAB F
  induction F using MvPolynomial.induction_on with
  | C n =>
    have h := valPoly_intC y z (σ := σ) n
    simp only [aeval_C, map_intCast] at h ⊢
    simpa using h
  | add p q hp hq =>
    rw [map_add, map_add]; exact valPoly_add hp hq
  | mul_X p j hp =>
    rw [map_mul, map_mul, aeval_X, aeval_X]; exact valPoly_mul hp (hAB j)

end FlagPolynomialValue

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTwinFlagSpec
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

namespace FlagSpectrum

theorem proof (h₁ : FlagPolynomialValue.Statement) (h₂ : FlagGenericPointValue.Statement)
    (h₃ : FlagGenericPointScale.Statement) : FlagSpectrum.Statement := by
  classical
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl P h u hu
  set z := IndefiniteRowSideFullHecke.LowerBoundFree.zPart P u with hzdef
  have hz : z ∈ mcPts (mCoordIdeal D.y) := hu.1
  choose ch f bfr G lam hfr hdom hdet hlam hpl using hu.2
  refine ⟨bfr, fun τ => (hfr τ).2.2.2.1, fun F hF => ?_⟩
  choose c0 hc0 using hz.1
  have hy0 : ∀ p : Σ k, ι k, z p ≠ 0 → D.y p ≠ 0 := by
    intro p hp hy
    apply hp
    have := eval_eq_zero_of_mem_mcPts hz
      (mem_mCoordIdeal_of_aeval_eq_zero D.y (isMultiHomog_X_single p) (by simpa using hy))
    simpa using this
  have hseg : ∀ τ k, D.y ⟨k, ch τ k⟩ ≠ 0 := fun τ k =>
    Finset.prod_ne_zero_iff.1 (hfr τ).1 k (Finset.mem_univ _)
  let α : K ⊕ (Ψ × Fin (D.N - 1)) → Ω := Sum.elim (fun k => (D.y ⟨k, c0 k⟩)⁻¹)
    (fun q => IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor D.y (ch q.1) P.b)
  have hαu : ∀ β, IsUnit (α β) := by
    rintro (k | q)
    · exact (inv_ne_zero (hy0 _ (hc0 k))).isUnit
    · exact (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hseg q.1 k)).isUnit
  let x : (Σ k, ι k) → Ω := fun p => α (Sum.inl p.1) * D.y p
  let V : WedgeVals Pl Ω := fun q m cc => α (Sum.inr q) * wedgeVals Pl bfr q m cc
  have hP : aeval (genPtR Pl x V) F = 0 := (h₃ Pl D.y (wedgeVals Pl bfr) α hαu F).2 hF
  let x' : (Σ k, ι k) → ℂ := fun p => z p / z ⟨p.1, c0 p.1⟩
  let V' : WedgeVals Pl ℂ := fun q m cc => valAt D.y (V q m cc) z
  have hx : ∀ p, IsValueAt D.y (x p) z (x' p) := by
    intro p
    refine ⟨fun k => if k = p.1 then 1 else 0, X p, X ⟨p.1, c0 p.1⟩, isMultiHomog_X_single p,
      isMultiHomog_X_single (⟨p.1, c0 p.1⟩ : Σ k, ι k), by simpa using hy0 _ (hc0 p.1), ?_,
      by simpa using hc0 p.1, by simp [x']⟩
    simp only [aeval_X, x, α, Sum.elim_inl]
    field_simp [hy0 _ (hc0 p.1)]
  have hVeq : ∀ τ (i : Fin (D.N - 1)) (m : Fin (Pl.M τ i)) (cc : Fin ((i : ℕ) + 1) → Fin D.N),
      V (τ, i) m cc = P.gen τ (stepTw i) (Fin.cast (h.M_eq τ i) m) (bfr τ ∘ cc) *
        IndefiniteRowSideFullHecke.LowerBoundFree.twistFactor D.y (ch τ) P.b := by
    intro τ i m cc
    simp only [V, α, wedgeVals, Sum.elim_inr]
    rw [h.gen_eq]
    exact mul_comm _ _
  have hV : ∀ q m cc, IsValueAt D.y (V q m cc) z (V' q m cc) := by
    rintro ⟨τ, i⟩ m cc
    obtain ⟨v, ⟨W, hW, -⟩, -⟩ := hpl τ (stepTw i) (Fin.cast (h.M_eq τ i) m)
    obtain ⟨-, v0, hv0, -⟩ := hW cc
    rw [← hVeq] at hv0
    show IsValueAt D.y (V (τ, i) m cc) z (valAt D.y (V (τ, i) m cc) z)
    rw [valAt_eq hz hv0]
    exact hv0
  have hQ := h₁ D.y z (genPtR Pl x V) (genPtR Pl x' V') (h₂ Pl z x x' V V' hx hV) F
  have hQ0 : aeval (genPtR Pl x' V') F = 0 := by
    ext μ
    have hμ := hQ μ
    rw [hP, coeff_zero] at hμ
    rw [coeff_zero]
    exact isValueAt_zero hz hμ
  let w : GV D.toComponentData → ℂ :=
    Sum.elim (Sum.elim (fun k => z ⟨k, c0 k⟩)
      (fun q => lam q.1 (stepTw q.2) * ∏ k, z ⟨k, ch q.1 k⟩ ^ P.b k)) (fun t => G t.1 t.2.2 t.2.1)
  have key : ∀ j, eval w (genPtR Pl x' V' j) = u (varMap h j) := by
    rintro ⟨k | ⟨τ, i⟩, t⟩
    · show eval w (X (Sum.inl (Sum.inl k)) * C (x' ⟨k, t⟩)) = z ⟨k, t⟩
      rw [eval_mul, eval_X, eval_C]
      simp only [w, x', Sum.elim_inl]
      field_simp [hc0 k]
    · obtain ⟨v, ⟨W, hW, hv⟩, hwv⟩ := hpl τ (stepTw i) (Fin.cast (h.M_eq τ i) t)
      refine Eq.trans ?_ hwv.symm
      show eval w (X (Sum.inl (Sum.inr (τ, i))) * ∑ cc : Fin ((i : ℕ) + 1) → Fin D.N,
        (∏ a, X (Sum.inr (τ, headIdx (step_le i) a, cc a))) * C (V' (τ, i) t cc)) = _
      rw [hv, eval_mul, eval_X, eval_sum]
      simp only [eval_mul, eval_prod, eval_X, eval_C, w, Sum.elim_inl, Sum.elim_inr]
      rw [mul_assoc]
      congr 1
      rw [mul_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun cc _ => ?_
      obtain ⟨-, v0, hv0, hWv⟩ := hW cc
      have hV0 : V' (τ, i) t cc = v0 := valAt_eq hz (by convert hv0 using 1; exact hVeq τ i t cc)
      rw [hWv, hV0]
      simp only [IndefiniteRowSideFullHecke.LowerBoundFree.firstCols, headIdx]
      rw [show IndefiniteRowSideFullHecke.LowerBoundFree.zPart P u = z from rfl]
      exact mul_assoc _ _ _
  have hev : eval u (map (Int.castRingHom ℂ) (forget h F)) = eval w (aeval (genPtR Pl x' V') F) := by
    have hh : (eval u).comp ((map (Int.castRingHom ℂ)).comp (forget h).toRingHom) =
        (eval w).comp (aeval (genPtR Pl x' V')).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp
      · intro j
        simp [forget, key]
    exact RingHom.congr_fun hh F
  rw [hev, hQ0, map_zero]

end FlagSpectrum

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelUnitSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

open Classical in

def MuModelUnitSection.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (H : HodgeData D.toComponentData), (∀ τ, H.F τ = D.F τ) →
    ∃ (bf bg : MuBlocks D → ℕ) (f g : MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ),
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg ∧
      f ∉ (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ)) ∧
      g ∉ (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ)) ∧
      (∀ k, (bf k : ℤ) - bg k = muDeg D k - Sum.elim H.aMu (0 : Ψ ⊕ Ψ → ℤ) k) ∧
      ∀ W : Ideal (MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ), W.IsPrime →
        (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ)) ≤ W →
        GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W →
        ∃ u v : MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ, u ∉ W ∧ v ∉ W ∧
          u * f - v * g ∈ (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

