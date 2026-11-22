import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0155
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionIsotropicFlag

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagsConjugateOfSameAdaptedModels
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlagConj

section Linear

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem exists_unitary_of_gram {κ : Type} [Fintype κ] [DecidableEq κ] (hκ : Fintype.card κ = n)
    (J : Matrix (Fin n) (Fin n) E) (B B' : Matrix (Fin n) κ E) (G G' : Matrix κ κ E) (hG : G' * G = 1)
    (hB : Bᴴ * J * B = G) (hB' : B'ᴴ * J * B' = G) :
    ∃ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E)ᴴ * J * γ = J ∧ (γ : Matrix (Fin n) (Fin n) E) * B = B' := by
  have e : κ ≃ Fin n := Fintype.equivFinOfCardEq hκ
  have h1 : G' * Bᴴ * J * B = 1 := by rw [← hG, ← hB]; simp only [Matrix.mul_assoc]
  have h2 : G' * B'ᴴ * J * B' = 1 := by rw [← hG, ← hB']; simp only [Matrix.mul_assoc]
  generalize G' * Bᴴ * J = C at h1
  generalize G' * B'ᴴ * J = C' at h2
  have h3 : B * C = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  have h4 : B' * C' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h2
  refine ⟨⟨B' * C, B * C', ?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, h1, Matrix.one_mul, h4]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C', h2, Matrix.one_mul, h3]
  · change (B' * C)ᴴ * J * (B' * C) = J
    calc (B' * C)ᴴ * J * (B' * C) = Cᴴ * (B'ᴴ * J * B') * C := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B * C)ᴴ * J * (B * C) := by
          rw [hB', ← hB]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by rw [h3, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · change B' * C * B = B'
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]

def cat {a : ℕ} {j : Fin a → ℕ} (T : ∀ i, Matrix (Fin n) (Fin (j i)) E) :
    Matrix (Fin n) (Σ i, Fin (j i)) E := Matrix.of fun r p => T p.1 r p.2

theorem gram_adapted {a m : ℕ} {j : Fin a → ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J)
    (J₀ : Matrix (Fin m) (Fin m) E) (T T' : ∀ i, Matrix (Fin n) (Fin (j i)) E) (T₀ : Matrix (Fin n) (Fin m) E)
    (h1 : ∀ i k, (T i)ᴴ * J * T k = 0 ∧ (T' i)ᴴ * J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * J * T' k = 0))
    (h2 : ∀ i, (T i)ᴴ * J * T' i = 1 ∧ (T i)ᴴ * J * T₀ = 0 ∧ (T' i)ᴴ * J * T₀ = 0)
    (h3 : T₀ᴴ * J * T₀ = J₀) :
    (fromCols (fromCols (cat T) (cat T')) T₀)ᴴ * J * fromCols (fromCols (cat T) (cat T')) T₀ =
      fromBlocks (fromBlocks 0 1 1 0) 0 0 J₀ := by
  have sw : ∀ {α β : Type} (A : Matrix (Fin n) α E) (B : Matrix (Fin n) β E),
      Bᴴ * J * A = (Aᴴ * J * B)ᴴ := by
    intro α β A B
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  have a11 : (cat T)ᴴ * J * cat T = 0 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    exact congrFun (congrFun (h1 i k).1 s) t
  have a22 : (cat T')ᴴ * J * cat T' = 0 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    exact congrFun (congrFun (h1 i k).2.1 s) t
  have a12 : (cat T)ᴴ * J * cat T' = 1 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    by_cases h : i = k
    · subst h
      refine (congrFun (congrFun (h2 i).1 s) t).trans ?_
      simp [Matrix.one_apply]
    · refine (congrFun (congrFun ((h1 i k).2.2 h) s) t).trans ?_
      simp [Matrix.one_apply, h]
  have a13 : (cat T)ᴴ * J * T₀ = 0 := by
    ext ⟨i, s⟩ t
    exact congrFun (congrFun (h2 i).2.1 s) t
  have a23 : (cat T')ᴴ * J * T₀ = 0 := by
    ext ⟨i, s⟩ t
    exact congrFun (congrFun (h2 i).2.2 s) t
  have a21 : (cat T')ᴴ * J * cat T = 1 := by rw [sw, a12, Matrix.conjTranspose_one]
  have a31 : T₀ᴴ * J * cat T = 0 := by rw [sw, a13, Matrix.conjTranspose_zero]
  have a32 : T₀ᴴ * J * cat T' = 0 := by rw [sw, a23, Matrix.conjTranspose_zero]
  ext ((p | p) | p) ((q | q) | q)
  · exact congrFun (congrFun a11 p) q
  · exact congrFun (congrFun a12 p) q
  · exact congrFun (congrFun a13 p) q
  · exact congrFun (congrFun a21 p) q
  · exact congrFun (congrFun a22 p) q
  · exact congrFun (congrFun a23 p) q
  · exact congrFun (congrFun a31 p) q
  · exact congrFun (congrFun a32 p) q
  · exact congrFun (congrFun h3 p) q

theorem exists_unitary_adapted {a m : ℕ} {j : Fin a → ℕ} (hn : n = m + 2 * ∑ i, j i)
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (J₀ : Matrix (Fin m) (Fin m) E) (hJ₀ : J₀.det ≠ 0)
    (T T' U U' : ∀ i, Matrix (Fin n) (Fin (j i)) E) (T₀ U₀ : Matrix (Fin n) (Fin m) E)
    (h1 : ∀ i k, (T i)ᴴ * J * T k = 0 ∧ (T' i)ᴴ * J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * J * T' k = 0))
    (h2 : ∀ i, (T i)ᴴ * J * T' i = 1 ∧ (T i)ᴴ * J * T₀ = 0 ∧ (T' i)ᴴ * J * T₀ = 0)
    (h3 : T₀ᴴ * J * T₀ = J₀)
    (g1 : ∀ i k, (U i)ᴴ * J * U k = 0 ∧ (U' i)ᴴ * J * U' k = 0 ∧ (i ≠ k → (U i)ᴴ * J * U' k = 0))
    (g2 : ∀ i, (U i)ᴴ * J * U' i = 1 ∧ (U i)ᴴ * J * U₀ = 0 ∧ (U' i)ᴴ * J * U₀ = 0)
    (g3 : U₀ᴴ * J * U₀ = J₀) :
    ∃ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E)ᴴ * J * γ = J ∧
      (∀ i, (γ : Matrix (Fin n) (Fin n) E) * T i = U i) ∧ (∀ i, (γ : Matrix (Fin n) (Fin n) E) * T' i = U' i) ∧
      (γ : Matrix (Fin n) (Fin n) E) * T₀ = U₀ := by
  obtain ⟨γ, hγ, hB⟩ := exists_unitary_of_gram
    (κ := ((Σ i, Fin (j i)) ⊕ (Σ i, Fin (j i))) ⊕ Fin m) (by simp [hn]; ring) J _ _ _
    (fromBlocks (fromBlocks 0 1 1 0) 0 0 J₀⁻¹)
    (by simp [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ₀)])
    (gram_adapted J hJ J₀ T T' T₀ h1 h2 h3) (gram_adapted J hJ J₀ U U' U₀ g1 g2 g3)
  refine ⟨γ, hγ, fun i => ?_, fun i => ?_, ?_⟩
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inl (Sum.inl ⟨i, s⟩))
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inl (Sum.inr ⟨i, s⟩))
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inr s)

end Linear

theorem unitary_map {E A : Type} [CommRing E] [CommRing A] {n : ℕ} (σ : E →+* E) (s : A →+* A) (φ : E →+* A)
    (h : ∀ e, s (φ e) = φ (σ e)) (J g : Matrix (Fin n) (Fin n) E) (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT s (g.map φ) * J.map φ * g.map φ = J.map φ := by
  have e : Formalism.UG.cT s (g.map φ) = (Formalism.UG.cT σ g).map φ := by
    ext i k
    simp [Formalism.UG.cT, h]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hg]

theorem exists_point (I : AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    ∃ a : I.GA,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hφ : ∀ v e, starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
    fun v e => (I.cm.cmUnram.2.1 (I.φ v) e).symm
  have hf : ∀ e, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by
    intro e
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  have hPP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  let u : ∀ v : InfinitePlace I.F, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Formalism.UG.bc (I.φ v) γ * (I.P_unit v).unit
  have hu : ∀ v, (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [u, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hPu : ∀ v, I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    rw [hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hU : ∀ v, u v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    change (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * Formalism.REAL.Jm (I.ε v) *
      (u v : Matrix (Fin I.n) (Fin I.n) ℂ) = Formalism.REAL.Jm (I.ε v)
    have h := unitary_map _ _ (I.φ v) (hφ v) I.J _ hγ
    have hc : Formalism.UG.cT (starRingEnd ℂ) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp [Formalism.UG.cT]
    rw [hc] at h
    rw [← I.P_spec v]
    calc (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) *
          (u v : Matrix (Fin I.n) (Fin I.n) ℂ)
        = (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ))ᴴ * I.J.map (I.φ v) *
          (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (I.P v)ᴴ * (((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
          rw [hPu]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h]
  have hF : Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    unitary_map _ _ _ hf I.J _ hγ
  exact ⟨(fun v => ⟨u v, hU v⟩, ⟨_, hF⟩), hu, rfl⟩

theorem mem_ratIso (I : AutInst) (γ : GL (Fin I.n) I.E) (N : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (z : Fin I.n → I.E) :
    z ∈ GlobalTheory.PointEquivariance.ratIso I γ N ↔ ∃ y ∈ N, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y = z := Iff.rfl

theorem conjugate_of_isAdapted : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (xf' : I.Gf) (S' : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (U U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf' j S' Λ x₀ U U' U₀ → ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, γ.2 * xf = xf' * k ∧ ∀ g : I.Ginf, sizesAt I xf' S' (γ.1 * g) = sizesAt I xf S g := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ _ ⟨_, hn, _, h1, h2, h3, h4, h5⟩ xf' S' U U' U₀ ⟨_, _, _, g1, g2, g3, g4, g5⟩
  have hcT : ∀ M : Matrix (Fin I.n) (Fin I.n) I.E, Formalism.UG.cT (starRingEnd I.E) M = Mᴴ := fun M => rfl
  have hJ : I.Jᴴ = I.J := (hcT _).symm.trans I.J_herm
  have hJ₀ : (I₀.J.map e).det ≠ 0 := by
    have := RingHom.map_det (e : I₀.E →+* I.E) I₀.J
    change e _ = (I₀.J.map e).det at this
    rw [← this]
    exact (map_ne_zero e).2 I₀.J_det
  obtain ⟨γ, hγ, c1, c2, c3⟩ := exists_unitary_adapted hn I.J hJ _ hJ₀ T T' U U' T₀ U₀ h1 h2 h3 g1 g2 g3
  have hγ' : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := hγ
  obtain ⟨c, hc1, hc2⟩ := exists_point I γ hγ'
  have d1 : ∀ u : ∀ i, Fin (j i) → I.E,
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ ∑ i, T i *ᵥ u i = ∑ i, U i *ᵥ u i := by
    intro u
    simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, c1]
  have d2 : ∀ u : ∀ i, Fin (j i) → I.E,
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ ∑ i, T' i *ᵥ u i = ∑ i, U' i *ᵥ u i := by
    intro u
    simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, c2]
  have hS : ∀ k, S' k = GlobalTheory.PointEquivariance.ratIso I γ (S k) := by
    intro k
    ext z
    rw [g5, mem_ratIso]
    constructor
    · rintro ⟨u, p1, p2, rfl⟩
      exact ⟨_, (h5 k _).2 ⟨u, p1, p2, rfl⟩, d1 u⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, p1, p2, rfl⟩ := (h5 k y).1 hy
      exact ⟨u, p1, p2, d1 u⟩
  have hL : lamX I (c * (1, xf)) = lamX I (1, xf') := by
    rw [GlobalTheory.PointEquivariance.lamX_rat I _ c γ hc2]
    ext z
    rw [g4, mem_ratIso]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, u', w, p1, p2, p3, rfl⟩ := (h4 y).1 hy
      refine ⟨u, u', w, p1, p2, p3, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_add, d1, d2, Matrix.mulVec_mulVec, c3]
    · rintro ⟨u, u', w, p1, p2, p3, rfl⟩
      refine ⟨_, (h4 _).2 ⟨u, u', w, p1, p2, p3, rfl⟩, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_add, d1, d2, Matrix.mulVec_mulVec, c3]
  refine ⟨c, ⟨γ, hγ', hc1, hc2⟩, xf'⁻¹ * (c.2 * xf), ?_, (mul_inv_cancel_left _ _).symm, fun g => ?_⟩
  · have := (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I (1, xf') (((1, xf') : I.GA)⁻¹ * (c * (1, xf)))).2
      (by rw [mul_inv_cancel_left, hL])
    exact this
  · funext i
    have hfr : frm I (c.1 * g, xf') = frm I (c * (g, xf)) := rfl
    unfold sizesAt
    rw [hfr, hS, hS]
    exact GlobalTheory.PointEquivariance.sizeQ_eq _ _ _ _ (GlobalTheory.PointEquivariance.zl_ratIso I (g, xf) c γ hc1)
      (GlobalTheory.PointEquivariance.rkK_ratIso I γ) _ _

end GlobalTheory.FlagConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussDensSphere
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Sphere

private theorem norm_toLp_eq_sqrt_sum_norm_sq (n : ℕ) (y : Fin (n + 1) → ℂ) :
    ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin (n + 1)))‖ = Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
  simp [EuclideanSpace.norm_eq]

private theorem volume_complex_unit_ball_toReal (n : ℕ) :
    (volume {y : Fin (n + 1) → ℂ | Real.sqrt (∑ i, ‖y i‖ ^ 2) < 1}).toReal =
      Real.pi ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hset : {y : Fin (n + 1) → ℂ | Real.sqrt (∑ i, ‖y i‖ ^ 2) < 1} =
      {y : Fin (n + 1) → ℂ | ∑ i, ‖y i‖ ^ (2 : ℝ) < 1} := by
    ext y
    simp only [Set.mem_setOf_eq, Real.rpow_two]
    rw [Real.sqrt_lt' one_pos, one_pow]
  rw [hset, Complex.volume_sum_rpow_lt_one (Fin (n + 1)) (by norm_num : (1 : ℝ) ≤ 2)]
  have h2 : (2 : ℝ) / 2 + 1 = 2 := by norm_num
  have h3 : 2 * (Fintype.card (Fin (n + 1)) : ℝ) / 2 + 1 = ((n + 1 : ℕ) : ℝ) + 1 := by
    simp only [Fintype.card_fin]; push_cast; ring
  rw [h2, h3, Real.Gamma_two, Real.Gamma_nat_eq_factorial, mul_one, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

theorem integral_radial (n : ℕ) (f : ℝ → ℝ) :
    ∫ y : Fin (n + 1) → ℂ, f (Real.sqrt (∑ i, ‖y i‖ ^ 2)) =
      2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) * ∫ r in Set.Ioi (0 : ℝ), r ^ (2 * n + 1) * f r := by

  let e := MeasurableEquiv.toLp 2 (Fin (n + 1) → ℂ)
  let μ : Measure (EuclideanSpace ℂ (Fin (n + 1))) := (volume : Measure (Fin (n + 1) → ℂ)).map e
  haveI : μ.IsAddHaarMeasure := by
    have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℂ)).symm.isAddHaarMeasure_map
      (volume : Measure (Fin (n + 1) → ℂ))
    exact h
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) = 2 * (n + 1) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hball : μ.real (Metric.ball 0 1) = Real.pi ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    rw [Measure.real, MeasurableEquiv.map_apply, ← volume_complex_unit_ball_toReal n]
    congr 2
    ext y
    simp [e, norm_toLp_eq_sqrt_sum_norm_sq]
  have key := integral_fun_norm_addHaar μ f
  rw [integral_map_equiv] at key
  simp only [e, MeasurableEquiv.toLp_apply, norm_toLp_eq_sqrt_sum_norm_sq] at key
  rw [key, hdim, hball, show 2 * (n + 1) - 1 = 2 * n + 1 by omega, nsmul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  rw [Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem ball_integral (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ y in {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}, gauss y =
      2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) *
        ∫ r in (0 : ℝ)..Real.sqrt t, r ^ (2 * n + 1) * Real.exp (-r ^ 2) := by
  have hq (y : Fin (n + 1) → ℂ) : qEps (allPos (n + 1)) y = ∑ i, ‖y i‖ ^ 2 := by
    simp [qEps, allPos]
  have hmeas : MeasurableSet {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t} := by
    simp only [hq]
    exact measurableSet_le (by fun_prop) measurable_const

  have hind : {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}.indicator gauss =
      fun y => (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2))
        (Real.sqrt (∑ i, ‖y i‖ ^ 2)) := by
    funext y
    have hs : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
    by_cases hy : ∑ i, ‖y i‖ ^ 2 ≤ t
    · have hy' : Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt t := Real.sqrt_le_sqrt hy
      rw [Set.indicator_of_mem (by simpa [hq] using hy), Set.indicator_of_mem (show Real.sqrt (∑ i, ‖y i‖ ^ 2) ∈ Set.Iic (Real.sqrt t) from hy'),
        Real.sq_sqrt hs, gauss]
    · have hy' : ¬ Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt t := by
        intro h
        exact hy ((Real.sqrt_le_sqrt_iff ht.le).mp h)
      rw [Set.indicator_of_notMem (by simpa [hq] using hy), Set.indicator_of_notMem (show Real.sqrt (∑ i, ‖y i‖ ^ 2) ∉ Set.Iic (Real.sqrt t) from hy')]
  rw [← integral_indicator hmeas, hind,
    integral_radial n ((Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2))),
    intervalIntegral.integral_of_le (Real.sqrt_nonneg t)]
  congr 1
  have hfun : (fun r : ℝ => r ^ (2 * n + 1) *
      (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) r) =
      (Set.Iic (Real.sqrt t)).indicator (fun r => r ^ (2 * n + 1) * Real.exp (-r ^ 2)) := by
    funext r
    by_cases hr : r ∈ Set.Iic (Real.sqrt t)
    · simp [Set.indicator_of_mem hr]
    · simp [Set.indicator_of_notMem hr]
  rw [hfun, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]

theorem gaussDens_sphere (n : ℕ) :
    gaussDens (allPos (n + 1)) 1 = Real.pi ^ (n + 1) * Real.exp (-1) / (n.factorial : ℝ) := by
  set C : ℝ := 2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) with hC
  set h : ℝ → ℝ := fun r => r ^ (2 * n + 1) * Real.exp (-r ^ 2) with hh

  have hF : (fun t : ℝ => ∫ y in {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}, gauss y) =ᶠ[nhds 1]
      fun t => C * ∫ r in (0 : ℝ)..Real.sqrt t, h r := by
    filter_upwards [lt_mem_nhds one_pos] with t ht using ball_integral n ht
  have hcont : Continuous h := by rw [hh]; fun_prop
  have h1 := (hcont.integral_hasStrictDerivAt 0 (Real.sqrt 1)).hasDerivAt
  have h2 := Real.hasDerivAt_sqrt (one_ne_zero : (1 : ℝ) ≠ 0)
  have hd := (h1.comp (1 : ℝ) h2).const_mul C
  rw [gaussDens]
  refine (hF.deriv_eq.trans hd.deriv).trans ?_
  simp only [hh, hC, Real.sqrt_one, one_pow, one_mul]
  field_simp
  try ring

end GlobalTheory.GaussMean.Sphere
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

variable {k r : ℕ}

def oneM (k r : ℕ) : Mt k r := fun i j => (1 : Mat k r) i j

def nbd (k r : ℕ) (j : ℕ) : Set (Mt k r) := Metric.closedBall (oneM k r) (1 / ((j : ℝ) + 1))

def avgR {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℝ Wp] (μ : Measure (Mt k r)) (j : ℕ)
    (g : Mt k r → Wp) (x : Mt k r) : Wp :=
  ((μ (nbd k r j)).toReal)⁻¹ • ∫ y in nbd k r j, g (rmulM (Matrix.of x) y) ∂μ

theorem isCompact_nbd (j : ℕ) : IsCompact (nbd k r j) := by
  unfold nbd
  exact isCompact_closedBall _ _

theorem oneM_mem_nbd (j : ℕ) : oneM k r ∈ nbd k r j := by
  unfold nbd
  exact Metric.mem_closedBall_self (by positivity)

private lemma single_mem_inWb_and_Tz_pos (k r : ℕ) :
    Formalism.QuantumDeterminants.inWb k r (Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) ∧
      0 < Formalism.QuantumDeterminants.Tz k r (Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) := by
  constructor
  · intro i hi
    have hne : i ≠ ⟨r + k, by omega⟩ := by
      rintro rfl
      simp at hi
    simp [hne]
  · simp only [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.Hpk, dotProduct, mulVec, Pi.single_apply,
      Pi.star_apply, Complex.re_sum, neg_pos]
    rw [Finset.sum_eq_single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1))]
    · have h1 : ¬ (r + k < r) := by omega
      simp [h1, Finset.sum_ite_eq']
    · intro b _ hb
      simp [hb]
    · simp

theorem gg_closedSub (k r : ℕ) : IsClosedSub k r (GG k r) :=
  (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r _ (single_mem_inWb_and_Tz_pos k r).1 (single_mem_inWb_and_Tz_pos k r).2).1

theorem haar_compact_lt_top {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) {C : Set (Mt k r)}
    (hC : IsCompact C) : μ C < ⊤ :=
  (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r (GG k r) μ (gg_closedSub k r) hμ).1 C hC

theorem nbd_pos {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) (j : ℕ) : 0 < μ (nbd k r j) := by
  have h1 : Matrix.of (oneM k r) = (1 : Mat k r) := by
    ext a b
    simp [oneM]
  have hone : Matrix.of (oneM k r) ∈ GG k r := by
    rw [h1]
    exact (gg_closedSub k r).2.2.1
  have hU := (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r (GG k r) μ (gg_closedSub k r) hμ).2
    (Metric.ball (oneM k r) (1 / ((j : ℝ) + 1))) Metric.isOpen_ball
    ⟨oneM k r, Metric.mem_ball_self (by positivity), hone⟩
  unfold nbd
  exact lt_of_lt_of_le hU (measure_mono Metric.ball_subset_closedBall)

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolSkewLayerLeStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_invVol_skew_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) (N.Gam Λ ⊓ N.ZI) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.WtSkew.invVol_skew_le | exact GlobalTheory.DegCnt.WtSkew.invVol_skew_le | (intros; apply GlobalTheory.DegCnt.WtSkew.invVol_skew_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolTopLayerLeStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermFramePairNormalForm_invVol_top_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊔ N.R1) (N.Gam Λ ⊔ N.R1) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.invVol_top_layer_le | exact GlobalTheory.DegCnt.invVol_top_layer_le | (intros; apply GlobalTheory.DegCnt.invVol_top_layer_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarOnBesselSubgroupProdMapStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHaarOn_besselSubgroup_prod_map : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → IsHaarOn (Nset k r) μN → IsHaarOn (Sset k r z) ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
  first | exact @GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map | exact GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map | (intros; apply GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTotallyIsotropicFlagComplexifiedSaturatedFlagStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallyIsotropicFlag_complexified_saturatedFlag : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I Λ j S → ∀ v, IsIsoFlag (I.ε v) j (flagAt I S v) := by
  first | exact @GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag | exact GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag | (intros; apply GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroup
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem isUnimod_GG : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  intro k r μ hμ
  obtain ⟨hG, h⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hM, hR⟩ := h μ hμ
  refine ⟨fun s hs => hR s hs, ?_⟩
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf measurable_invM]
  exact GlobalTheory.HaarInversion.lintegral_inv_eq _ (GG k r) μ hG hM hR f hf

end GlobalTheory.SgInf

example : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := GlobalTheory.SgInf.isUnimod_GG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroupStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_splitTorus_iwasawa_unitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), IsIsoC ε W → ∃ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm ∧ (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) ∧ (∀ s, dOp (umat (a s)) ≤ |s|) ∧ (∀ s, ∀ m ∈ NW ε W, a s * m * (a s)⁻¹ ∈ NW ε W ∧ |s| ≤ dOp (umat (m * a s))) ∧ (∀ m ∈ NW ε W, Filter.Tendsto (fun s => a s * m * (a s)⁻¹) Filter.atBot (nhds 1)) ∧ ∀ g : UJ ε, ∃ k : UJ ε, umat k ∈ Kset ε ∧ ∀ s, a s * g * (k⁻¹ * a s * k)⁻¹ * g⁻¹ ∈ NW ε W := by
  first | exact @GlobalTheory.IsoTorus.split_torus | exact GlobalTheory.IsoTorus.split_torus | (intros; apply GlobalTheory.IsoTorus.split_torus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionIsotropicFlagStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_isotropic_flag : ∀ (k r : ℕ), ∀ g ∈ GG k r, ∃ n ∈ Nset k r, ∃ a : Fin r → ℝ, (∀ b, 0 < a b) ∧ ∃ m ∈ UH (Hb k), ∃ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), g = n * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m * κ := by
  first | exact @GlobalTheory.Amp.Iwa.iwasawa | exact GlobalTheory.Amp.Iwa.iwasawa | (intros; apply GlobalTheory.Amp.Iwa.iwasawa <;> assumption)
end

