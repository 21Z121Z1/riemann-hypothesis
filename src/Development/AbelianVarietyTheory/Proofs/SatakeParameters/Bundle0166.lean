import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdicCompletionCongruenceSubgroupsOpenCompactSmal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0151
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdicCompletionCongruenceSubgroupsOpenCompactSmalStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_congruenceSubgroups_open_compact_small : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a l : ℕ), l.Prime → (l : 𝓞 E) ∈ w.asIdeal → (∀ m : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) ∧ IsCompact (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E)))) ∧ ∀ N ∈ nhds (1 : GL (Fin a) (w.adicCompletion E)), ∀ᶠ m : ℕ in Filter.atTop, (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) ⊆ N := by
  first | exact @GlobalTheory.CongOpenSmall.congruence_open_compact_small | exact GlobalTheory.CongOpenSmall.congruence_open_compact_small | (intros; apply GlobalTheory.CongOpenSmall.congruence_open_compact_small; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTypeClosurePreservedByArchCompactIntertwStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.Published GlobalTheory.IdemAdj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_typeClosure_preserved_by_archCompact_intertwiner : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) (U : Submodule ℂ π.V), FiniteDimensional ℂ U → (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) → ∀ f : π.V →ₗ[ℂ] π.V, (∀ k, ∀ u ∈ U, f (cptOn π k u) = cptOn π k (f u)) → ∀ u ∈ U, (∀ g, (fun k : Kinf E a => (cptRep E a k u.1).1 g) ∈ AutFin.coeffSpan ρ₀) → ∀ g, (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) ∈ AutFin.coeffSpan ρ₀ := by
  first | exact @GlobalTheory.IdemAdj.typeClosure_of_intertwine | exact GlobalTheory.IdemAdj.typeClosure_of_intertwine | (intros; apply GlobalTheory.IdemAdj.typeClosure_of_intertwine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIntegralPreimageLeSumTransposeImage
section
open Matrix

namespace GlobalTheory.LatticeDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int_iff (a : L) : a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1 := Iff.rfl

theorem mulVec_int {m n : ℕ} (A : Matrix (Fin m) (Fin n) L) (u : Fin n → L)
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hu : ∀ i, u i ∈ Formalism.UG.intL L) :
    ∀ i, (A *ᵥ u) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hu j)

theorem one_dim (e z : L)
    (h : ∀ c : L, c ∈ Formalism.UG.intL L → e * c ∈ Formalism.UG.intL L → c * z ∈ Formalism.UG.intL L) :
    ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧ z = a + e * b := by
  by_cases he : e ∈ Formalism.UG.intL L
  · refine ⟨z, 0, ?_, Subring.zero_mem _, by simp⟩
    simpa using h 1 (Subring.one_mem _) (by simpa using he)
  · have he0 : e ≠ 0 := by
      rintro rfl
      exact he (Subring.zero_mem _)
    have hlt : 1 < Valued.v e := not_le.mp ((mem_int_iff e).not.mp he)
    have hinv : e⁻¹ ∈ Formalism.UG.intL L := by
      rw [mem_int_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hlt.le
    refine ⟨0, e⁻¹ * z, Subring.zero_mem _, h _ hinv ?_, ?_⟩
    · rw [mul_inv_cancel₀ he0]; exact Subring.one_mem _
    · field_simp
      simp

theorem diag_case {m n : ℕ} (d : Fin m → L) (z : Fin n → L)
    (h : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) →
      (∀ i, ((Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0)) *ᵥ u) i
        ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) :
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
      z = l + (Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0))ᵀ *ᵥ w := by
  have key : ∀ k : Fin n, ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧
      z k = a + (if hk : (k : ℕ) < m then d ⟨k, hk⟩ else 0) * b := by
    intro k
    apply one_dim
    intro c hc hec
    have := h (Pi.single k c) ?_ ?_
    · simpa [Pi.single_apply] using this
    · intro i
      by_cases hi : i = k
      · subst hi; simpa using hc
      · simp [hi]
    · intro j
      rw [Matrix.mulVec_single]
      by_cases hj : (k : ℕ) = (j : ℕ)
      · have hk : (k : ℕ) < m := hj ▸ j.2
        have : (⟨k, hk⟩ : Fin m) = j := Fin.ext hj
        rw [dif_pos hk, this] at hec
        simpa [hj] using hec
      · simp [hj]
  choose a b ha hb hz using key
  refine ⟨a, fun j => if hj : (j : ℕ) < n then b ⟨j, hj⟩ else 0, ha, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact hb _
    · exact Subring.zero_mem _
  · funext k
    rw [hz k, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hk : (k : ℕ) < m
    · rw [dif_pos hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]
      · simp
      · intro j _ hj
        have : (k : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e.symm)
        simp [this]
      · simp
    · rw [dif_neg hk, zero_mul]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (k : ℕ) ≠ (j : ℕ) := fun e => hk (e ▸ j.2)
      simp [this]

theorem dual_subset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (x : Matrix (Fin m) (Fin n) L)
    (z : Fin n → L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) →
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ z = l + xᵀ *ᵥ w := by
  intro L _ _ m n x z h
  obtain ⟨P, P', Q, Q', d, hP, hP', hQ, hQ', hPP, hQQ, hx⟩ := GlobalTheory.T.smithNormalForm_discreteValuationField L m n x
  set D : Matrix (Fin m) (Fin n) L :=
    Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) with hD
  have hPP' : P' * P = 1 := mul_eq_one_comm.mp hPP
  have hQQ' : Q' * Q = 1 := mul_eq_one_comm.mp hQQ
  obtain ⟨l, w, hl, hw, hz⟩ := diag_case d (Q'ᵀ *ᵥ z) (by
    intro s hs hDs
    have h1 := h (Q' *ᵥ s) (mulVec_int _ _ hQ' hs) (by
      have : x *ᵥ (Q' *ᵥ s) = P *ᵥ (D *ᵥ s) := by
        rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P * D), hQQ, Matrix.mul_one]
      rw [this]
      exact mulVec_int _ _ hP hDs)
    have h2 : ∑ i, s i * (Q'ᵀ *ᵥ z) i = ∑ i, (Q' *ᵥ s) i * z i := by
      change s ⬝ᵥ (Q'ᵀ *ᵥ z) = (Q' *ᵥ s) ⬝ᵥ z
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h2]
    exact h1)
  refine ⟨Qᵀ *ᵥ l, P'ᵀ *ᵥ w, mulVec_int _ _ (fun i j => hQ j i) hl,
    mulVec_int _ _ (fun i j => hP' j i) hw, ?_⟩
  have h3 : z = Qᵀ *ᵥ (Q'ᵀ *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hQQ', Matrix.transpose_one, Matrix.one_mulVec]
  have h4 : xᵀ *ᵥ (P'ᵀ *ᵥ w) = Qᵀ *ᵥ (Dᵀ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hx,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
  rw [h4, ← Matrix.mulVec_add, ← hz]
  exact h3

end GlobalTheory.LatticeDuality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DualSplitRel

open Formalism.L2.NTheta GlobalTheory.SplitPlace

section Abstract

variable {G : Type} [Group G]

theorem coset_mul [DecidableEq G] {K : Set G} {z α : G} {R : Finset G} (hz : ∀ k ∈ K, k * z = z * k)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    (∀ γ ∈ R.image (· * z), ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * (α * z) * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * (α * z) * k₂) → ∃! γ, γ ∈ R.image (· * z) ∧ γ⁻¹ * x ∈ K := by
  have conj : ∀ k ∈ K, z⁻¹ * k * z = k := fun k hk => by rw [mul_assoc, hz k hk, inv_mul_cancel_left]
  have conj' : ∀ k ∈ K, z * k * z⁻¹ = k := fun k hk => by rw [← hz k hk, mul_inv_cancel_right]
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨k₁, a₁, k₂, a₂, rfl⟩ := h1 δ hδ
    refine ⟨k₁, a₁, k₂, a₂, ?_⟩
    simp only [mul_assoc, hz k₂ a₂]
  · rintro _ ⟨k₁, a₁, k₂, a₂, rfl⟩
    have ex : k₁ * (α * z) * k₂ = k₁ * α * k₂ * z := by
      simp only [mul_assoc, hz k₂ a₂]
    obtain ⟨γ, ⟨hγ, hw⟩, hu⟩ := h2 (k₁ * α * k₂) ⟨k₁, a₁, k₂, a₂, rfl⟩
    refine ⟨γ * z, ⟨Finset.mem_image_of_mem _ hγ, ?_⟩, ?_⟩
    · have := conj _ hw
      rw [ex]
      convert hw using 1
      rw [← this]
      group
    · rintro _ ⟨hm, hw'⟩
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hm
      rw [hu δ ⟨hδ, ?_⟩]
      have := conj' _ hw'
      rw [ex] at this hw'
      convert hw' using 1
      rw [← this]
      group

theorem coset_one (K : Subgroup G) :
    (∀ γ ∈ ({1} : Finset G), ∃ k₁ ∈ (K : Set G), ∃ k₂ ∈ (K : Set G), γ = k₁ * 1 * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ (K : Set G), ∃ k₂ ∈ (K : Set G), x = k₁ * 1 * k₂) →
        ∃! γ, γ ∈ ({1} : Finset G) ∧ γ⁻¹ * x ∈ (K : Set G) := by
  refine ⟨fun γ hγ => ⟨1, one_mem K, 1, one_mem K, by simpa using hγ⟩, ?_⟩
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using mul_mem ha hb⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩

theorem eq_scalar {B n : Type} [CommRing B] [Fintype n] [DecidableEq n] (b : GL n B) {m : Matrix n n B} {c : B}
    (h : (b⁻¹).1 * m * b.1 = Matrix.scalar n c) : m = Matrix.scalar n c := by
  have h1 : m = b.1 * ((b⁻¹).1 * m * b.1) * (b⁻¹).1 := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [h1, h, ← (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem scalar_parts {A B n : Type} [CommRing A] [CommRing B] [Fintype n] [DecidableEq n] (π : A →+* B) (t : B → A) (E c : A)
    (h3 : ∀ x, t (π x) = E * x) (m : Matrix n n A) (h5 : m.map π = Matrix.scalar n (π c)) :
    E • m = (E * c) • (1 : Matrix n n A) := by
  refine Matrix.ext fun i j => ?_
  have h8 : π (m i j) = π (c * (1 : Matrix n n A) i j) := by
    refine (congrFun (congrFun h5 i) j).trans ?_
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Matrix.one_apply]
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc, ← h3, ← h3, h8]

end Abstract

section Divisors

variable {R : Type} [CommRing R] {n : ℕ}

theorem dv_scalar {Λ : (Fin n → R) → Prop} {O : R → Prop} {e c : R} {u u' : Fin n → R} {A Z : Matrix (Fin n) (Fin n) R}
    (hz : e • Z = (e * c) • (1 : Matrix (Fin n) (Fin n) R)) (hu : ∀ i, u' i = c * u i)
    (h : GlobalTheory.DivDual.Dv Λ O e u A) : GlobalTheory.DivDual.Dv Λ O e u' (A * Z) := by
  obtain ⟨B, b1, b2, b3, b4⟩ := h
  have core : ∀ y, e • (A * Z).mulVec y = c • e • A.mulVec y := fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.smul_mulVec, hz, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, mul_comm]
  have core2 : ∀ w : Fin n → R, e • B.mulVec (fun i => u' i * w i) = c • e • B.mulVec (fun i => u i * w i) := fun w => by
    have : (fun i => u' i * w i) = c • fun i => u i * w i := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, hu, mul_assoc]
    rw [this, Matrix.mulVec_smul, smul_comm]
  refine ⟨B, b1, b2, fun y hy => ?_, fun w hw => ?_⟩
  · obtain ⟨w, hw, e1⟩ := b3 y hy
    exact ⟨w, hw, by rw [core, core2, e1]⟩
  · obtain ⟨y, hy, e1⟩ := b4 w hw
    exact ⟨y, hy, by rw [core, core2, e1]⟩

end Divisors

variable {D : D7}

theorem exists_idem {P : Pl D.host.E} (hP : conjPl P ≠ P) : ∃ e : AE D, IsIdemAt e P := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  rcases h with ⟨h, -⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact ⟨e, h⟩
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem idem_unique {P : Pl D.host.E} {e e' f' : AE D} (he : IsIdemAt e P) (h : IsPrimeIdem P e' f') :
    f' = e + cA D e := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨hd, ε, hε, h1⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ (f := e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨hd', ε', hε', h1'⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  rw [h1, h1', GlobalTheory.IdemSupport.placeIdem_unique hε' hε]

theorem hyp_eq_locPart {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) (V : HSp D) :
    hyp V P = locPart V (KsphC V ∅) e := by
  refine Set.ext fun k => ⟨?_, fun h => ⟨h.1, e, e + cA D e, Or.inl ⟨he, rfl⟩, h.2⟩⟩
  rintro ⟨h1, e', f', h2, h3⟩
  rw [idem_unique he h2] at h3
  exact ⟨h1, h3⟩

theorem exists_central {e : AE D} (he : IsSplitIdem D e) (V : HSp D) {ϖ : D.host.E} (h0 : ϖ ≠ 0) :
    ∃ z : GA D V, SuppAt e V z ∧ (∀ k, SuppAt e V k → k * z = z * k) ∧
      finPart D e • fm V z = (finPart D e * finPart D (incA D ϖ⁻¹)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (RF D)) := by
  obtain ⟨v, π, s, h1, h2, h3, h4, -⟩ := GlobalTheory.SplitCoord.exists_coord e he
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis V e v π s he.1 h2 h3 h4 (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2
  obtain ⟨hex, hinj⟩ := comp_bij (V := V) (B := B) he h1 h2
  have hu : ∀ x : D.host.E, x ≠ 0 → π (finPart D (incA D x)) ≠ 0 := fun x hx h => by
    have := congrArg π (congrArg (finPart D) (congrArg (incA D) (mul_inv_cancel₀ hx)))
    rw [map_mul, map_mul, map_mul, h, zero_mul, map_one, map_one, map_one] at this
    exact zero_ne_one this
  let t : (Fv D.host.F v)ˣ := Units.mk0 _ (hu _ (inv_ne_zero h0))
  let a : GL (Fin V.rank) (Fv D.host.F v) := Units.map (Matrix.scalar (Fin V.rank)).toMonoidHom t
  have ha : a.1 = Matrix.scalar (Fin V.rank) (π (finPart D (incA D ϖ⁻¹))) := rfl
  obtain ⟨z, hs, hz⟩ := hex a
  refine ⟨z, hs, fun k hk => hinj _ _ (suppAt_mul hk hs) (suppAt_mul hs hk) ?_, ?_⟩
  · rw [map_mul, map_mul, hz]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, ha]
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq.symm
  · have h6 := comp_val (V := V) (π := π) (B := B) z
    rw [hz, ha] at h6
    exact scalar_parts π (fun w => finPart D (s w)) _ _ h3 _ (eq_scalar B h6.symm)

theorem divAt_mul {e : AE D} {V : HSp D} {ϖ : D.host.E} (h0 : ϖ ≠ 0) {z g : GA D V} {d : List ℤ}
    (hz : finPart D e • fm V z = (finPart D e * finPart D (incA D ϖ⁻¹)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (RF D)))
    (h : DivAt V e ϖ d g) : DivAt V e ϖ (d.map (· - 1)) (g * z) := by
  rw [GlobalTheory.DivDual.divAt_iff] at h ⊢
  obtain ⟨hd, h⟩ := h
  refine ⟨by simpa using hd, ?_⟩
  rw [show finMat D.sp.cm.sig V.gram (g * z) = fm V g * fm V z from fm_mul V g z]
  refine dv_scalar hz (fun i => ?_) h
  have hi : i.1 < d.length := by rw [hd]; exact i.2
  have gd : (d.map (· - 1)).getD i.1 0 = d.getD i.1 0 - 1 := by
    simp [List.getD_eq_getElem _ _ hi, hi]
  rw [gd, zpow_sub_one₀ h0, mul_comm, RingHom.map_mul, RingHom.map_mul]

theorem label_shift {n j : ℕ} (hj : j ≤ n) : (dualLab (splitLab n j)).map (· - 1) = splitLab n (n - j) := by
  simp [dualLab, splitLab, Nat.sub_sub_self hj]

theorem label_shift_zero (n : ℕ) : (List.replicate n (0 : ℤ)).map (· - 1) = splitLab n n := by
  simp [splitLab]

theorem sphOp_of {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) {V : HSp D} {d : List ℤ} (hd : d.Pairwise fun a b => b ≤ a) {α : GA D V}
    (hα : SuppAt e V α) (hD : DivAt V e (ϖ : D.host.E) d α) {R : Finset (GA D V)} (hR : ∀ γ ∈ R, SuppAt e V γ)
    (hc : IsCosetRep V (locPart V (KsphC V ∅) e) α R) : SphOp V P d R :=
  ⟨e, e + cA D e, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), Or.inl ⟨he, rfl⟩, h1, h2, hd,
    fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hD, hR, hc⟩

theorem dual_rel : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), conjPl P ≠ P → ∀ j, j ≤ V.rank → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (dualLab (splitLab V.rank j)) 1) (opOf π P (Finsupp.single (splitLab V.rank V.rank) 1) u) = opOf π P (Finsupp.single (splitLab V.rank (V.rank - j)) 1) u := by
  classical
  intro D V P hP j hj M _ _ π u hu
  obtain ⟨e, he⟩ := exists_idem hP
  obtain ⟨-, ϖ, -, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
  have h0 : (ϖ : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
  obtain ⟨z, hs, hc, hz⟩ := exists_central he.1 V h0
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  have hKl : locPart V (KsphC V ∅) e = (K : Set (GA D V)) := (hyp_eq_locPart he V).symm.trans hK
  have hKz : ∀ k ∈ locPart V (KsphC V ∅) e, k * z = z * k := fun k hk => hc k hk.2
  obtain ⟨-, hrep, hH⟩ := GlobalTheory.SplitPlace.split_local V P e he
  obtain ⟨α, hα⟩ := (hH ϖ h1 h2).1 j hj
  obtain ⟨R, r1, r2⟩ := hrep α hα.2.1
  have hDα : DivAt V e (ϖ : D.host.E) (dualLab (splitLab V.rank j)) α := by
    have := (GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0
      (GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V P e ϖ j α he h1 h2 hj hα)).1
    rwa [inv_inv] at this
  have c1 := (GlobalTheory.SphLabelOps.label_operators V P).1
  have shift : ∀ {d : List ℤ} {g : GA D V} {R' : Finset (GA D V)}, SuppAt e V g → DivAt V e (ϖ : D.host.E) d g →
      (∀ γ ∈ R', SuppAt e V γ) → IsCosetRep V (locPart V (KsphC V ∅) e) g R' →
      (d.map (· - 1)).Pairwise (fun a b => b ≤ a) → SphOp V P (d.map (· - 1)) (R'.image (· * z)) := by
    intro d g R' sg dg sR hr hp
    obtain ⟨a, b⟩ := coset_mul hKz (fun γ hγ => (hr.1 γ hγ).2) hr.2
    have sup : ∀ γ ∈ R'.image (· * z), SuppAt e V γ := fun γ hγ => by
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
      exact suppAt_mul (sR δ hδ) hs
    exact sphOp_of he h1 h2 hp (suppAt_mul sg hs) (divAt_mul h0 hz dg) sup
      ⟨fun γ hγ => ⟨mem_GfC he.1 (sup γ hγ), a γ hγ⟩, b⟩
  have one : IsCosetRep V (locPart V (KsphC V ∅) e) 1 {1} := by
    have := coset_one K
    rw [← hKl] at this
    refine ⟨fun γ hγ => ⟨?_, this.1 γ hγ⟩, this.2⟩
    rw [Finset.mem_singleton.1 hγ]
    exact one_mem _
  have S0 := shift (GlobalTheory.SplitHecke.suppAt_one V)
    (GlobalTheory.SphLabelOps.divAt_one V he.1.1 (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem (Or.inl ⟨he, rfl⟩)) (ϖ : D.host.E))
    (fun γ hγ => by rw [Finset.mem_singleton.1 hγ]; exact GlobalTheory.SplitHecke.suppAt_one V) one
    (by rw [label_shift_zero]; simp [splitLab, List.pairwise_append, List.pairwise_replicate])
  rw [label_shift_zero] at S0
  have S1 : SphOp V P (dualLab (splitLab V.rank j)) R := sphOp_of he h1 h2
    (by simp [dualLab, splitLab, List.pairwise_append, List.pairwise_replicate]) hα.2.1 hDα r1 r2
  have S2 := shift hα.2.1 hDα r1 r2
    (by rw [label_shift hj]; simp [splitLab, List.pairwise_append, List.pairwise_replicate])
  rw [label_shift hj] at S2
  have fixw : ∀ k ∈ hyp V P, π k (π z u) = π z u := fun k hk => by
    have hk' : k ∈ locPart V (KsphC V ∅) e := by rw [← hyp_eq_locPart he V]; exact hk
    have := congrArg (fun g => π g u) (hKz k hk')
    simp only [map_mul, Module.End.mul_apply, hu k hk] at this
    exact this
  have inj : Function.Injective (· * z : GA D V → GA D V) := mul_left_injective z
  have A := (c1 _ _ S0).2 M π u hu
  have Bq := (c1 _ _ S1).2 M π _ fixw
  have C := (c1 _ _ S2).2 M π u hu
  rw [← A, ← C, Finset.sum_image inj.injOn, Finset.sum_image inj.injOn, Finset.sum_singleton, one_mul, ← Bq]
  exact Finset.sum_congr rfl fun γ _ => by rw [map_mul, Module.End.mul_apply]

end GlobalTheory.DualSplitRel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequalityStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (V X J I : Type) [AddCommGroup V] [Module ℂ V] [Fintype I] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ), (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) → ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → ∀ (v : I → V) (η : I → J → ℂ), (∀ i j, T j (v i) = η i j • v i) → ∀ ε : ℝ, (∀ x, ‖ι.symm (ev x (v₀ + ∑ i, v i))‖ ≤ ε) → ∃ (s : Finset (J → Qbar l)) (c : (J → Qbar l) → Qbar l), (∀ z ∈ s, ∃ i, z = fun j => ι.symm (η i j)) ∧ ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (θ j)) P - ∑ z ∈ s, c z * MvPolynomial.aeval z P‖ ≤ ε := by
  first | (exact @GlobalTheory.Cong.eigen_small_sub_finite_approx) | (exact GlobalTheory.Cong.eigen_small_sub_finite_approx) | (intros; apply GlobalTheory.Cong.eigen_small_sub_finite_approx  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteRepresentativesModUniformizerPowStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_representatives_mod_uniformizerPow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
  Formalism.UG.IsUnramInv ϖ σ q → ∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧
    ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K := by
  first | exact @GlobalTheory.UnramReps.exists_reps_mod_pow | exact GlobalTheory.UnramReps.exists_reps_mod_pow | (intros; apply GlobalTheory.UnramReps.exists_reps_mod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepresentativesMulInvIntegralStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_representatives_mul_inv_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (n n' : ℕ) (a : GL (Fin n) L) (x : Matrix (Fin n') (Fin n) L),
  (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ y ∈ Y, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
  first | exact @GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv | exact GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv | (intros; apply GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntGramOfFixed
section
noncomputable section
namespace GlobalTheory.Hk3.HoweDuality

theorem exists_int_gram_of_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∃ w : M, w ≠ 0 ∧ (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) ∧
      w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs0 hs hspan x hw
  obtain ⟨hne, hfx⟩ := GlobalTheory.T.heisenbergTranslate_fixed_integralUnitary L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs x hw
  have Hph : ∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (∀ i j, (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) i j ∈ Formalism.UG.intL L) →
      ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) = 1 := by
    intro h hh hint
    have e := congrArg (fun T : Module.End ℂ M => T s) (hP.rho_mul x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hs _ hint, add_sub_cancel, hfx h hh hint] at e
    have e2 : (ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) - 1) • ρ x s = 0 := by
      rw [sub_smul, one_smul, ← e, sub_self]
    rcases smul_eq_zero.1 e2 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hne
  exact GlobalTheory.T.exists_integral_gram_of_phase_conditions L ϖ σ q δ n n' JS ψ hP.unr hP.odd hP.intS hP.hermS hP.delta hP.psi_int hP.psi_ne x
    (GlobalTheory.T.cayleyTransform_trivial_phase_skewHermitian L ϖ σ q δ n n' JS JT ψ hP.unr hP.odd hP.intS hP.intT hP.hermS hP.hermT hP.delta hP.psi_int x Hph)
end GlobalTheory.Hk3.HoweDuality
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLimitDvdUniformizerPowCauchyStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ a : ℕ → L, (∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (a (k + 1) - a k)) →
    ∃ b : L, ∀ k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (b - a k) := by
  first | exact @GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow | exact GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow | (intros; apply GlobalTheory.Hk3.IntWittBase.exists_limit_dvdPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmithNormalFormGeneratorsExactOrdersStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smithNormalForm_generators_exactOrders : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
  ∀ (n : ℕ) (a : GL (Fin n) L), ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
    (∀ k, 1 ≤ e k) ∧ (∀ i k, M i k ∈ Formalism.UG.intL L) ∧ (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) ∧ (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧ (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) := by
  first | exact @GlobalTheory.Hk3.snf_generators | exact GlobalTheory.Hk3.snf_generators | (intros; apply GlobalTheory.Hk3.snf_generators <;> assumption)
end

