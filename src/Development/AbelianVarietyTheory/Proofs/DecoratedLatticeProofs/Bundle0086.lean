import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0084
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentMatrixPiIffForallEval
section
open Matrix

namespace GlobalTheory.BesselChar

theorem unip_pi_iff {ι S : Type} [Fintype ι] [DecidableEq ι] [CommRing S] {n ρ : ℕ}
    (E : Matrix (Fin n) (Fin ρ) (ι → S)) (K : Matrix (Fin ρ) (Fin n) (ι → S))
    (M : Matrix (Fin n) (Fin n) (ι → S)) :
    GlobalTheory.BesselChar.Unip E K M ↔ ∀ i, GlobalTheory.BesselChar.Unip (E.map (Pi.evalRingHom (fun _ => S) i))
      (K.map (Pi.evalRingHom (fun _ => S) i)) (M.map (Pi.evalRingHom (fun _ => S) i)) := by
  constructor
  · rintro ⟨⟨T, hT, e⟩, h2⟩ i
    set φ := Pi.evalRingHom (fun _ => S) i
    refine ⟨⟨T.map φ, fun j l hjl => by simp [Matrix.map_apply, hT j l hjl], ?_⟩, fun y hy => ?_⟩
    · have := congrArg (fun X => X.map φ) e
      simpa only [Matrix.map_mul, Matrix.map_add _ (map_add φ)] using this
    · let y' : Fin n → ι → S := fun k => Pi.single i (y k)
      have hy' : K *ᵥ y' = 0 := by
        funext j i'
        by_cases hi : i' = i
        · subst hi
          have h1 := congr_fun (mulVec_map φ K y') j
          have h0 : (fun k => φ (y' k)) = y := by
            funext k; simp [φ, y']
          rw [h0, hy] at h1
          simpa [φ] using h1.symm
        · show (∑ k, K j k * y' k) i' = 0
          rw [Finset.sum_apply]
          refine Finset.sum_eq_zero fun k _ => ?_
          simp [y', Pi.single_apply, hi]
      obtain ⟨a, ha⟩ := h2 y' hy'
      refine ⟨fun l => φ (a l), ?_⟩
      have h0 : (fun k => φ (y' k)) = y := by
        funext k; simp [φ, y']
      have h1 := mulVec_map φ M y'
      have h3 := mulVec_map φ E a
      rw [h0] at h1
      rw [h1, h3, ha]
      funext k
      simp only [Pi.add_apply, map_add]
      rw [show φ (y' k) = y k from congr_fun h0 k]
  · intro h
    choose hc hv using h
    choose T hT e using hc
    refine ⟨⟨Matrix.of fun j l i => T i j l, fun j l hjl => by funext i; exact hT i j l hjl, ?_⟩, fun y hy => ?_⟩
    · ext k l i
      have h1 := congr_fun (congr_fun (e i) k) l
      have hT' : (Matrix.of fun j l i => T i j l).map (Pi.evalRingHom (fun _ => S) i) = T i := by
        ext j l; rfl
      have h2 : ((M * E).map (Pi.evalRingHom (fun _ => S) i)) k l
          = ((E + E * Matrix.of fun j l i => T i j l).map (Pi.evalRingHom (fun _ => S) i)) k l := by
        rw [Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hT']
        exact h1
      simpa using h2
    · have hyi : ∀ i, K.map (Pi.evalRingHom (fun _ => S) i) *ᵥ (fun k => y k i) = 0 := by
        intro i
        have := mulVec_map (Pi.evalRingHom (fun _ => S) i) K y
        refine this.trans ?_
        rw [hy]; rfl
      choose a ha using fun i => hv i _ (hyi i)
      refine ⟨fun l i => a i l, ?_⟩
      funext k i
      have h1 := congr_fun (mulVec_map (Pi.evalRingHom (fun _ => S) i) M y) k
      have h3 := congr_fun (mulVec_map (Pi.evalRingHom (fun _ => S) i) E (fun l i => a i l)) k
      have h4 := congr_fun (ha i) k
      simp only [Pi.evalRingHom_apply] at h1 h3
      show (M *ᵥ y) k i = y k i + (E *ᵥ fun l i => a i l) k i
      rw [← h1, ← h3, h4]
      rfl

end GlobalTheory.BesselChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentRealPlaceIffFrameUnipotentRadical
section
open Matrix NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RealUnipFrame

variable {n ρ : ℕ}

theorem mem_span_image_iff (g : Fin ρ → Fin n → ℂ) (S : Set (Fin ρ)) (w : Fin n → ℂ) :
    w ∈ Submodule.span ℂ (g '' S) ↔ ∃ t : Fin ρ → ℂ, (∀ b, b ∉ S → t b = 0) ∧ ∑ b, t b • g b = w := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 h
    refine ⟨l, fun b hb => ?_, ?_⟩
    · by_contra h0
      exact hb (hl (Finsupp.mem_support_iff.2 h0))
    · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i; simp
  · rintro ⟨t, ht, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ S
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [ht b hb, zero_smul]; exact Submodule.zero_mem _

theorem mem_span_image_mulVec (Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (g : Fin ρ → Fin n → ℂ)
    (S : Set (Fin ρ)) (w : Fin n → ℂ) :
    Q *ᵥ w ∈ Submodule.span ℂ ((fun b => Q *ᵥ g b) '' S) ↔ w ∈ Submodule.span ℂ (g '' S) := by
  rw [mem_span_image_iff, mem_span_image_iff]
  have hinj : ∀ u u' : Fin n → ℂ, Q *ᵥ u = Q *ᵥ u' → u = u' := by
    intro u u' h
    have := congrArg (P *ᵥ ·) h
    simpa only [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec] using this
  have hsum : ∀ t : Fin ρ → ℂ, ∑ b, t b • Q *ᵥ g b = Q *ᵥ ∑ b, t b • g b := by
    intro t
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  refine exists_congr fun t => and_congr Iff.rfl ?_
  rw [hsum]
  exact ⟨hinj _ _, fun h => by rw [h]⟩

end GlobalTheory.RealUnipFrame

namespace GlobalTheory.RealUnipFrame

variable {n ρ : ℕ}

theorem cols_iff (f : Fin ρ → Fin n → ℂ) (d : Fin ρ → ℂ) (hd : ∀ a, d a ≠ 0) (N : Matrix (Fin n) (Fin n) ℂ) :
    (∃ T : Matrix (Fin ρ) (Fin ρ) ℂ, GlobalTheory.BesselChar.StrictUp T ∧
      N * Matrix.of (fun k a => d a * f a k) = Matrix.of (fun k a => d a * f a k) + Matrix.of (fun k a => d a * f a k) * T) ↔
    ∀ i : Fin ρ, (N - 1) *ᵥ f i ∈ Submodule.span ℂ (f '' {b | b.1 < i.1}) := by
  have e1 : ∀ i k, d i * (N *ᵥ f i) k = ∑ j, N k j * (d i * f i j) := by
    intro i k
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · rintro ⟨T, hT, h⟩ i
    rw [mem_span_image_iff]
    refine ⟨fun j => d j * T j i / d i, fun j hj => ?_, ?_⟩
    · have : i ≤ j := by
        simp only [Set.mem_setOf_eq, not_lt] at hj
        exact Fin.le_def.2 hj
      show d j * T j i / d i = 0
      rw [hT j i this]; simp
    · funext k
      have hk := congrFun (congrFun h k) i
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply] at hk
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      have hdi := hd i
      have key : d i * (N *ᵥ f i) k = d i * f i k + ∑ j, d j * T j i * f j k := by
        have e2 : ∑ j, d j * T j i * f j k = ∑ j, d j * f j k * T j i :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [e1, hk, e2]
      have e4 : ∑ x, d x * T x i / d i * f x k = (∑ j, d j * T j i * f j k) / d i := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e4, div_eq_iff hdi]
      linear_combination -key
  · intro h
    choose t ht hts using fun i => (mem_span_image_iff f _ _).1 (h i)
    refine ⟨Matrix.of fun j i => d i * t i j / d j, fun j i hij => ?_, ?_⟩
    · have : ¬ j.1 < i.1 := by rw [Fin.le_def] at hij; omega
      simp [ht i j (by simpa using this)]
    · ext k i
      have hk := congrFun (hts i) k
      rw [Finset.sum_apply] at hk
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at hk
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply]
      have e3 : ∑ j, d j * f j k * (d i * t i j / d j) = d i * ∑ j, t i j * f j k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have := hd j
        field_simp
      rw [← e1, e3, hk]
      ring

theorem colspan_iff (f : Fin ρ → Fin n → ℂ) (d : Fin ρ → ℂ) (hd : ∀ a, d a ≠ 0) (N : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin n → ℂ) :
    (∃ a, N *ᵥ y = y + Matrix.of (fun k a => d a * f a k) *ᵥ a) ↔
      (N - 1) *ᵥ y ∈ Submodule.span ℂ (f '' {b | b.1 < ρ}) := by
  have hE : ∀ a : Fin ρ → ℂ, Matrix.of (fun k a => d a * f a k) *ᵥ a = ∑ b, (a b * d b) • f b := by
    intro a; funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => by ring
  rw [mem_span_image_iff, Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun b => a b * d b, fun b hb => absurd b.2 (by simpa using hb), ?_⟩
    rw [← hE, ha, add_sub_cancel_left]
  · rintro ⟨t, -, ht⟩
    refine ⟨fun b => t b / d b, ?_⟩
    rw [hE]
    have : ∀ b, t b / d b * d b = t b := fun b => div_mul_cancel₀ _ (hd b)
    simp only [this, ht, add_sub_cancel]

end GlobalTheory.RealUnipFrame

namespace GlobalTheory.RealUnipFrame

open Formalism.L2.SG.HidaSetting

variable {n ρ : ℕ}

theorem conj_sub_mulVec (Q P N : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (w : Fin n → ℂ) :
    (Q * N * P - 1) *ᵥ (Q *ᵥ w) = Q *ᵥ ((N - 1) *ᵥ w) := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hPQ, Matrix.mul_one]

theorem hJ_frame (ε : Fin n → Bool) (P Q Jc : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1)
    (hspec : Pᴴ * Jc * P = Formalism.REAL.Jm ε) (f y : Fin n → ℂ) :
    hJ ε (Q *ᵥ f) (Q *ᵥ y) = star f ⬝ᵥ (Jc *ᵥ y) := by
  unfold hJ
  rw [← hspec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPQ, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, hPQ,
    Matrix.conjTranspose_one, Matrix.one_mulVec]

theorem emb_hform (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (x z : Fin I.n → I.E) :
    I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x z) =
      star (fun i => I.φ v (x i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun i => I.φ v (z i)) := by
  rw [← Formalism.MainNotions.BridgeUnipRad.hform_eq]
  simp only [Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, starRingEnd_apply,
    Formalism.MainNotions.BridgeUnipRad.emb_star]

theorem perp_mulVec (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (y : Fin I.n → ℂ) :
    (Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v) *ᵥ y =
      fun a => starRingEnd ℂ (I.φ v (c a)) * (star (fun i => I.φ v (x a i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ y)) := by
  funext a
  rw [Matrix.map_mul]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, map_mul, starRingEnd_apply, Formalism.MainNotions.BridgeUnipRad.emb_star,
    Pi.star_apply, star_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.RealUnipFrame

namespace GlobalTheory.RealUnipFrame

open Formalism.L2.SG.HidaSetting

theorem unip_iff_inN : ∀ (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) →
    ∀ (N : Matrix (Fin I.n) (Fin I.n) ℂ), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (I.φ v))
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) N ↔
      Formalism.L2.SG.HidaSetting.InN (I.ε v) (fun a => Formalism.L2.SG.HidaSetting.rv I v (x a)) (Formalism.L2.SG.HidaSetting.rv I v z)
        ((I.P v)⁻¹ * N * I.P v) := by
  intro I v ρ x c z hc hz N
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPQ : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hQP : (I.P v)⁻¹ * I.P v = 1 := Matrix.nonsing_inv_mul _ hu
  set f : Fin ρ → Fin I.n → ℂ := fun a k => I.φ v (x a k) with hf
  set d : Fin ρ → ℂ := fun a => I.φ v (c a) with hdd
  have hd : ∀ a, d a ≠ 0 := fun a => (map_ne_zero (I.φ v)).2 (hc a)
  have hE : (Matrix.of fun k a => c a * x a k).map (I.φ v) = Matrix.of fun k a => d a * f a k := by
    ext k a; simp [hf, hdd]
  have hrv : ∀ w : Fin I.n → I.E, rv I v w = (I.P v)⁻¹ *ᵥ fun i => I.φ v (w i) := fun _ => rfl
  have hrx : (fun a => rv I v (x a)) = fun b => (I.P v)⁻¹ *ᵥ f b := rfl
  have hspan : ∀ (w : Fin I.n → ℂ) (S : Set (Fin ρ)),
      ((I.P v)⁻¹ * N * I.P v - 1) *ᵥ ((I.P v)⁻¹ *ᵥ w) ∈ Submodule.span ℂ ((fun a => rv I v (x a)) '' S) ↔
        (N - 1) *ᵥ w ∈ Submodule.span ℂ (f '' S) := by
    intro w S
    rw [conj_sub_mulVec _ _ _ hPQ, hrx]
    exact mem_span_image_mulVec _ _ hPQ f S _
  have hperp : ∀ y : Fin I.n → ℂ,
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) *ᵥ y = 0 ↔
        ∀ a, hJ (I.ε v) (rv I v (x a)) ((I.P v)⁻¹ *ᵥ y) = 0 := by
    intro y
    rw [perp_mulVec]
    simp only [hrv, hJ_frame (I.ε v) (I.P v) _ (I.J.map (I.φ v)) hPQ (I.P_spec v)]
    constructor
    · intro h a
      have := congrFun h a
      exact (mul_eq_zero.1 this).resolve_left ((map_ne_zero _).2 (hd a))
    · intro h
      funext a
      simp [h a]
  unfold GlobalTheory.BesselChar.Unip InN InS spanLt
  rw [hE, cols_iff f d hd N]
  have hB : (∀ y, ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) *ᵥ y = 0 →
        ∃ a, N *ᵥ y = y + (Matrix.of fun k a => d a * f a k) *ᵥ a) ↔
      ∀ y, (∀ a, hJ (I.ε v) (rv I v (x a)) y = 0) →
        ((I.P v)⁻¹ * N * I.P v - 1) *ᵥ y ∈ Submodule.span ℂ ((fun a => rv I v (x a)) '' {b | b.1 < ρ}) := by
    constructor
    · intro h y' hy'
      have hy : y' = (I.P v)⁻¹ *ᵥ (I.P v *ᵥ y') := by rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
      rw [hy] at hy' ⊢
      rw [hspan, ← colspan_iff f d hd]
      exact h _ ((hperp _).2 hy')
    · intro h y hy
      rw [colspan_iff f d hd, ← hspan]
      exact h _ ((hperp y).1 hy)
  rw [hB]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun a => (hspan (f a) _).2 (h1 a), ?_⟩, h2⟩
    refine h2 _ fun a => ?_
    rw [hrv, hrv, hJ_frame (I.ε v) (I.P v) _ (I.J.map (I.φ v)) hPQ (I.P_spec v), ← emb_hform, hz a, map_zero]
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨fun a => (hspan (f a) _).1 (h1 a), h2⟩

end GlobalTheory.RealUnipFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryFiniteDatumBoundedLevelSizeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_entry_finite_datum_bounded_level_size : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  first | exact @GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp | exact GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp | (intros; apply GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixUnitDerivativeDiscreteSeriesMatrixCoeffStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixUnitDerivative_discreteSeriesMatrixCoeff : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (a b : Ix p q) (v : R.HK.V) (w : R.U.H), ∀ g ∈ UJset ε, Formalism.REAL.Eab ε (e a) (e b) (fun x => inner ℂ w (σ x (R.ι v))) g = inner ℂ w (σ g (R.ι (R.HK.act (Eab a b) v))) := by
  first | exact @GlobalTheory.CoeffEab.eab_coeff | exact GlobalTheory.CoeffEab.eab_coeff | (intros; apply GlobalTheory.CoeffEab.eab_coeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotSqDvdOfRationalPrimeSplitsCompletelyStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_sq_dvd_of_rationalPrimeSplitsCompletely : ∀ (E : Type) [Field E] [NumberField E] (T : ℕ), T.Prime → GlobalTheory.St.G.SplitsIn E T → ∀ w : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ w.asIdeal → ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} := by
  first | exact @GlobalTheory.St.G.SplitUnram.not_sq_dvd_of_splitsIn | exact GlobalTheory.St.G.SplitUnram.not_sq_dvd_of_splitsIn | (intros; apply GlobalTheory.St.G.SplitUnram.not_sq_dvd_of_splitsIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondGelfandInvariantValueEqStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondGelfandInvariant_value_eq : ∀ (n : ℕ) (lam : Fin n → ℂ), GlobalTheory.Dec.gelfVal lam 2 = ∑ a, lam a ^ 2 - ((rhoSq n : ℚ) : ℂ) := by
  first | exact @GlobalTheory.GelfandTwo.gelfVal_two | exact GlobalTheory.GelfandTwo.gelfVal_two | (intros; apply GlobalTheory.GelfandTwo.gelfVal_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumEqGenVal
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTransfer

theorem mtor_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    (mtor ϖ (-e) : GL (A ⊕ D) k) = (mtor ϖ e)⁻¹ := by
  unfold mtor torusElt
  rw [← map_inv]
  congr 1
  funext i
  rcases i with i | i <;> simp [_root_.zpow_neg]

theorem sum_eq_genVal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ) (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → ∀ (s : Finset D) (R : Finset (GL (A ⊕ D) k)) (d : GL (A ⊕ D) k → kˣ), IsReps (mtor ϖ (-indic s)) R d → ∑ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * mtor ϖ (-indic s)) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b ⟨datum ξ⁻¹, hΦ⟩ x := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ ξ μS μT hξ hμ W hW hΦ X _ _ ρ x B hx X' _ _ ρ' b hb s R d hR
  set g : GL (A ⊕ D) k := mtor ϖ (indic s) with hg
  have hginv : (mtor ϖ (-indic s) : GL (A ⊕ D) k) = g⁻¹ := mtor_neg ϖ (indic s)
  rw [hginv] at hR ⊢
  set Φ : W := ⟨datum ξ⁻¹, hΦ⟩ with hΦdef

  have h1 : ∀ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = b Φ (ρ g x) := by
    intro j hj
    obtain ⟨hjJ, hdj⟩ := hR.1 j hj
    have hjiJ : j⁻¹ ∈ parahoric k A D := inv_mem hjJ
    have hne := (GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j⁻¹ hjiJ).1
    have hprod := (GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j hjJ).2 (d j) (Units.mk0 _ hne) hdj rfl
    have hx1 : ρ j⁻¹ x = (ξ (Units.mk0 _ hne) : ℂ) • x := hx.1 j⁻¹ hjiJ (Units.mk0 _ hne) rfl
    have he := hb (j * g⁻¹) 1 Φ (ρ (g * j⁻¹) x)
    have hone : (j * g⁻¹) * (g * j⁻¹) = 1 := by group
    rw [← Module.End.mul_apply, ← map_mul, hone, map_one, Module.End.one_apply, map_one, Module.End.one_apply,
      map_mul, Module.End.mul_apply, hx1, map_smul, map_smul] at he
    rw [show (⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) = ⟨omTwo μS μT (j * g⁻¹) 1 Φ, hW _ _ Φ Φ.2⟩ from rfl,
      he, smul_smul, hprod, one_smul]

  have htame : IsTame ξ⁻¹ := fun y hy => by simp [hξ y hy]
  have hunr : IsUnram (μT⁻¹ * ξ) := fun y hy => by
    have := hμ y hy
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at this ⊢
    rw [← inv_inv (ξ y), ← mul_inv, this, inv_one]
  have h2 : ∀ j ∈ parahoric k A D, ∀ dd : kˣ, (dd : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      ∀ z, b Φ (ρ j z) = (ξ dd : ℂ) • b Φ z := by
    intro j hj dd hdd z
    have hom : omTwo μS μT j (1 : GL (A ⊕ D') k) (datum ξ⁻¹) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • datum ξ⁻¹ := by
      have := GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric k A D D' ξ⁻¹ (μT⁻¹ * ξ) htame hunr j hj dd hdd
      rw [show μT⁻¹ * ξ * ξ⁻¹ = μT⁻¹ by rw [mul_assoc, mul_inv_cancel, mul_one]] at this
      unfold omTwo
      rw [this]
      funext y
      simp
    have he := hb j 1 Φ z
    have hsub : (⟨omTwo μS μT j 1 Φ, hW j 1 Φ Φ.2⟩ : W) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • Φ := Subtype.ext hom
    rw [hsub, map_smul, LinearMap.smul_apply, map_one, Module.End.one_apply] at he
    rw [← he, smul_smul]
    simp

  obtain ⟨R'', d'', hR''⟩ := (GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps k A D).1 g
  have hcard := (GlobalTheory.T.card_parahoricDoubleCosetReps_inv_eq k A D g R'' R d'' d hR'' hR).1
  have hT := hx.2.2 s R'' d'' hR''
  have hsum2 : genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b Φ x = R''.card • b Φ (ρ g x) := by
    rw [← map_smul, hT, map_sum, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hjJ, hdj⟩ := hR''.1 j hj
    rw [map_smul, show (mtor ϖ (indic s) : GL (A ⊕ D) k) = g from rfl, map_mul, Module.End.mul_apply,
      h2 j hjJ (d'' j) hdj, smul_smul]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_const, hsum2, hcard]

end GlobalTheory.ParHeckeTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySatakeTransformEqOfBaseChangeSatakeParame
section
noncomputable section

namespace GlobalTheory.SatBc

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem satU_eq_of_bcParam_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂˣ,
      GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α' →
      ∀ φ ∈ Hecke ℂ (KU σ n), SatU ϖ q φ (fun i => (α i : ℂ)) = SatU ϖ q φ (fun i => (α' i : ℂ)) := by
  intro L _ _ _ ϖ σ q n hU α α' e φ hφ
  have e1 := congrArg (Multiset.map fun z : ℂˣ => (z : ℂ)) (add_right_cancel e)
  refine GlobalTheory.eq_of_perm_inv_invariant_of_multiset_eq _ (SatU ϖ q φ)
    (fun γ hγ => GlobalTheory.SatakeWeyl.satWeyl L ϖ σ q n (n / 2) hU (by omega) (by omega) γ hγ φ hφ) _ _
    (fun i => (α i).ne_zero) ?_
  simpa [Multiset.map_map, Function.comp_def] using e1

end GlobalTheory.SatBc
end
end

