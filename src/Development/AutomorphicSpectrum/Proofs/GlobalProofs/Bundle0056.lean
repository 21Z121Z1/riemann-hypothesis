import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0047
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0566
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0055

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditiveStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derived_action_additive : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧ ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutatorStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derived_action_commutator : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowthStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_lie_word_growth : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Q : M → M → ℂ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hpos : ∀ x, x ≠ 0 → 0 < (Q x x).re) {d : ℕ} (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (A : ℝ) (hA : 0 ≤ A) (hs : ∀ i x, |2 * (Q (X i x) x).re| ≤ A * (Q x x).re) (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V), ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V, Real.sqrt (Q ((l.map X).prod u) ((l.map X).prod u)).re ≤ C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q u u).re := by
  first | exact @GlobalTheory.CompanionTheory.HCForm.nelson_form | exact GlobalTheory.CompanionTheory.HCForm.nelson_form | (intros; apply GlobalTheory.CompanionTheory.HCForm.nelson_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HolomorphicLocalSectionsCompatible
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem gagaSections_pure : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (D : ℕ), IsProper s → SmoothOfRelativeDimension D s → ∀ (L : LB X), L.IsLB → ∀ h : L.ι → (Sp ℂ ⟶ X) → ℂ, (∀ (i : L.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ L.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B) → (∀ (i j : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) → h i x = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * h j x) → ∃ σ : L.Sec, ∀ (i : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ L.U i → valAt' x (L.U i) (σ.f i) = h i x := by
  intro X s D hp hs L hL h hh hg
  obtain ⟨σ, hσ, e⟩ := GlobalTheory.T.holomorphic_gluing_local_functions X s D hs (AnRead.all s (RingHom.id ℂ) D) L hL h hh hg
  obtain ⟨t, ht⟩ := GlobalTheory.T.analytic_section_is_algebraic X s D hs hp (AnRead.all s (RingHom.id ℂ) D) L hL σ hσ
  refine ⟨t, fun i x hx hU => ?_⟩
  have hx' : x ≫ s = spMap (RingHom.id ℂ) := by
    rw [hx, spMap]; exact (by simp)
  let y : CxPts s (RingHom.id ℂ) := ⟨x, hx'⟩
  have hy : y ∈ ptsIn s (RingHom.id ℂ) (L.U i) := hU
  have h1 := e i y hy
  rw [← ht] at h1
  exact h1

end GlobalTheory.CompanionTheory.Gaga
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBound
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isSmoothVec_add {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) :
    IsSmoothVec G π (u + v) := by
  obtain ⟨F, hF, hF'⟩ := hu
  obtain ⟨K, hK, hK'⟩ := hv
  exact ⟨fun z => F z + K z, hF.add hK, fun z hz => by rw [map_add, hF' z hz, hK' z hz]⟩

theorem isSmoothVec_smul (c : ℂ) {v : H} (hv : IsSmoothVec G π v) :
    IsSmoothVec G π (c • v) := by
  obtain ⟨F, hF, hF'⟩ := hv
  exact ⟨fun z => c • F z, hF.const_smul c, fun z hz => by rw [map_smul, hF' z hz]⟩

theorem isSmoothVec_zero : IsSmoothVec G π (0 : H) :=
  ⟨fun _ => 0, contDiff_const, fun z _ => map_zero _⟩

theorem isSmoothVec_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → H)
    (hf : ∀ i, IsSmoothVec G π (f i)) : IsSmoothVec G π (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSmoothVec_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSmoothVec_add (isSmoothVec_smul _ (hf a)) ih

variable {d : ℕ} {b : Fin d → Matrix (Fin n) (Fin n) ℂ}

theorem word_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {w : H} (hw : IsSmoothVec G π w) :
    IsSmoothVec G π (p.foldr (fun i w => dRep π (b i) w) w) := by
  induction p with
  | nil => exact hw
  | cons i p ih => exact (hasDerivAt_dRep_and_isSmoothVec hG hrep ih (hb i)).2

theorem list_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ HCSS.lieOf G) {v : H}
    (hv : IsSmoothVec G π v) : IsSmoothVec G π (l.foldr (dRep π) v) := by
  induction l with
  | nil => exact hv
  | cons X l ih =>
    exact (hasDerivAt_dRep_and_isSmoothVec hG hrep
      (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) (hl X List.mem_cons_self)).2

theorem word_add (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {u v : H} (hu : IsSmoothVec G π u)
    (hv : IsSmoothVec G π v) :
    p.foldr (fun i w => dRep π (b i) w) (u + v) =
      p.foldr (fun i w => dRep π (b i) w) u + p.foldr (fun i w => dRep π (b i) w) v := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (SmoothLin.dRep_linear hG hrep (word_smooth hG hrep hb p hu)
      (word_smooth hG hrep hb p hv) (hb i) (hb i)).2.1

theorem word_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) (c : ℂ) {v : H}
    (hv : IsSmoothVec G π v) :
    p.foldr (fun i w => dRep π (b i) w) (c • v) =
      c • p.foldr (fun i w => dRep π (b i) w) v := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (SmoothLin.dRep_linear hG hrep (word_smooth hG hrep hb p hv)
      (word_smooth hG hrep hb p hv) (hb i) (hb i)).2.2 c

theorem word_sum (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) (p : List (Fin d)) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → H) (hf : ∀ i, IsSmoothVec G π (f i)) :
    p.foldr (fun i w => dRep π (b i) w) (∑ j ∈ s, c j • f j) =
      ∑ j ∈ s, c j • p.foldr (fun i w => dRep π (b i) w) (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := word_smul hG hrep hb p (0 : ℂ) (isSmoothVec_zero (G := G) (π := π) (H := H))
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      word_add hG hrep hb p (isSmoothVec_smul _ (hf a)) (isSmoothVec_sum s c f hf),
      word_smul hG hrep hb p _ (hf a), ih]

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem prod_mnorm_nonneg (l : List (Matrix (Fin n) (Fin n) ℂ)) : 0 ≤ (l.map mnorm).prod := by
  induction l with
  | nil => simp
  | cons X l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_nonneg (mnorm_nonneg X) ih

theorem mixed_bound (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π)
    (hb : ∀ i, b i ∈ HCSS.lieOf G)
    (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i))
    (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w →
      dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w)
    {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ l : List (Fin d),
      ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ HCSS.lieOf G) (p : List (Fin d)) :
    ‖p.foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖ ≤
      C ^ (p.length + l.length + 1) * (p.length + l.length).factorial * D ^ l.length *
        (l.map mnorm).prod := by
  induction l generalizing p with
  | nil => simpa using hbound p
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ HCSS.lieOf G := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hX : X ∈ HCSS.lieOf G := hl X List.mem_cons_self
    have hw : IsSmoothVec G π (l.foldr (dRep π) v) := list_smooth hG hrep l hl' hv
    obtain ⟨r, hr⟩ := hsp X hX
    have e1 : dRep π X (l.foldr (dRep π) v) =
        ∑ i, (r i : ℂ) • dRep π (b i) (l.foldr (dRep π) v) := by
      rw [hr]
      exact hexp r _ hw
    have hsm : ∀ i, IsSmoothVec G π (dRep π (b i) (l.foldr (dRep π) v)) := fun i =>
      (hasDerivAt_dRep_and_isSmoothVec hG hrep hw (hb i)).2
    have e2 : p.foldr (fun i w => dRep π (b i) w) (dRep π X (l.foldr (dRep π) v)) =
        ∑ i, (r i : ℂ) • (p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v) := by
      rw [e1, word_sum hG hrep hb p _ _ _ hsm]
      simp [List.foldr_append]
    have hih : ∀ i, ‖(p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖ ≤
        C ^ (p.length + (l.length + 1) + 1) * (p.length + (l.length + 1)).factorial *
          D ^ l.length * (l.map mnorm).prod := by
      intro i
      have h := ih hl' (p ++ [i])
      rw [List.length_append, List.length_singleton,
        show p.length + 1 + l.length = p.length + (l.length + 1) by omega] at h
      exact h
    have hK : 0 ≤ C ^ (p.length + (l.length + 1) + 1) * (p.length + (l.length + 1)).factorial *
        D ^ l.length * (l.map mnorm).prod :=
      mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC.le _) (Nat.cast_nonneg _))
        (pow_nonneg hD0 _)) (prod_mnorm_nonneg l)
    have hsum : ∑ i, |r i| ≤ D * mnorm X := by
      rw [hr]
      exact hD r
    show ‖p.foldr (fun i w => dRep π (b i) w) (dRep π X (l.foldr (dRep π) v))‖ ≤ _
    rw [e2]
    calc ‖∑ i, (r i : ℂ) • (p ++ [i]).foldr (fun i w => dRep π (b i) w) (l.foldr (dRep π) v)‖
        ≤ ∑ i, |r i| * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) := by
          refine norm_sum_le_of_le _ fun i _ => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hih i) (abs_nonneg _)
      _ = (∑ i, |r i|) * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (D * mnorm X) * (C ^ (p.length + (l.length + 1) + 1) *
            (p.length + (l.length + 1)).factorial * D ^ l.length * (l.map mnorm).prod) :=
          mul_le_mul_of_nonneg_right hsum hK
      _ = _ := by
          simp only [List.length_cons, List.map_cons, List.prod_cons]
          ring

theorem wordBound_of_basis {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ}
    (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G)
    (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i))
    (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w →
      dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w)
    {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ l : List (Fin d),
      ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial) :
    WordBound G π v := by
  have hD1 : (1 : ℝ) ≤ D + 1 := by linarith
  refine ⟨C * (D + 1), by positivity, fun l hl => ?_⟩
  have h := mixed_bound hG hrep hb hsp D hD0 hD hexp hv C hC hbound l hl []
  simp only [List.foldr_nil, List.length_nil, Nat.zero_add] at h
  refine h.trans ?_
  have hP := prod_mnorm_nonneg l
  have hpow : D ^ l.length ≤ (D + 1) ^ (l.length + 1) :=
    (pow_le_pow_left₀ hD0 (by linarith) _).trans (pow_le_pow_right₀ hD1 (Nat.le_succ _))
  have hCk : 0 ≤ C ^ (l.length + 1) := pow_nonneg hC.le _
  have hf : (0 : ℝ) ≤ l.length.factorial := Nat.cast_nonneg _
  rw [mul_pow]
  calc C ^ (l.length + 1) * l.length.factorial * D ^ l.length * (l.map mnorm).prod
      = (C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod) * D ^ l.length := by ring
    _ ≤ (C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod) *
          (D + 1) ^ (l.length + 1) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hCk hf) hP)
    _ = _ := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaFunctionalEquation
section
noncomputable section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.CompanionTheory.PartialZeta
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {F : Type} [Field F] [NumberField F]

theorem coeff_inv_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (J : (Ideal (𝓞 F))⁰) :
    ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) = ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) := by
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have h1 := coeff_inv_mul_coeff F (classHecke ψ) (standardOpenSubgroup_le_ker ψ) J hJ
  rw [coeff_classHecke ψ J hJ] at h1
  have h2 : ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 J)) = 1 := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, inv_mul_cancel, ofMul_one, AddChar.map_zero_eq_one]
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)

def zetaOfClass (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).continuedLFunction s

def zetaOfClassInv (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).continuedLFunction s

theorem isPartialZeta_of_indicator {ι : Type} [Fintype ι] (χ : ι → HeckeCharacter F) (c : ι → ℂ)
    (C : ClassGroup (𝓞 F)) (hU : ∀ i, standardOpenSubgroup F ≤ (χ i).toIdele.ker)
    (horth : ∀ J : (Ideal (𝓞 F))⁰,
      (ClassGroup.mk0 J = C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 1) ∧
      (ClassGroup.mk0 J ≠ C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 0)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (fun s => ∑ i, c i * (χ i).continuedLFunction s) := by
  classical
  refine ⟨?_, fun s hs => ?_⟩
  · exact DifferentiableOn.fun_sum fun i _ => (differentiableOn_continuedLFunction F (χ i) (hU i)).const_mul (c i)
  · have h1 : HasSum (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)))
        (∑ i, c i * (χ i).continuedLFunction s) := by
      refine hasSum_sum fun i _ => ?_
      rw [(χ i).continuedLFunction_eq hs]
      exact ((χ i).hasSum_LFunction hs).mul_left (c i)
    have hfac : ∀ I : Ideal (𝓞 F),
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) =
          (∑ i, c i * (χ i).coeff I) * (Ideal.absNorm I : ℂ) ^ (-s) := fun I => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    let g : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} → Ideal (𝓞 F) :=
      fun J => (J.1 : Ideal (𝓞 F))
    have hg : Function.Injective g := fun a b hab =>
      Subtype.ext (Subtype.ext hab)
    have hsupp : ∀ I ∉ Set.range g,
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) = 0 := by
      intro I hI
      by_cases hbot : I = ⊥
      · subst hbot
        simp
      · let J : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hbot⟩
        have hJ : ClassGroup.mk0 J ≠ C := fun h => hI ⟨⟨J, h⟩, rfl⟩
        rw [hfac, show I = (J : Ideal (𝓞 F)) from rfl, (horth J).2 hJ, zero_mul]
    have h2 := (hg.hasSum_iff hsupp).2 h1
    have h3 : (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s))) ∘ g =
        fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
          ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s) := funext fun J => by
      simp only [Function.comp_apply]
      rw [hfac, show g J = (J.1 : Ideal (𝓞 F)) from rfl, (horth J.1).1 J.2, one_mul]
    rw [h3] at h2
    exact h2

theorem card_classGroup_ne_zero : (Fintype.card (ClassGroup (𝓞 F)) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem isPartialZeta_zetaOfClass (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClass C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => classHecke ψ) _ C (fun ψ => standardOpenSubgroup_le_ker ψ) fun J => ?_
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if ClassGroup.mk0 J = C then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_classHecke ψ J hJ]
    ring_nf
  rw [e]
  constructor
  · intro h
    rw [if_pos h, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [if_neg h, mul_zero]

theorem isPartialZeta_zetaOfClassInv (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClassInv C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => (classHecke ψ)⁻¹) _ C
    (fun ψ => standardOpenSubgroup_le_ker_inv F _ (standardOpenSubgroup_le_ker ψ)) fun J => ?_
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if C = ClassGroup.mk0 J then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_inv_classHecke ψ J, mul_assoc]
  rw [e]
  constructor
  · intro h
    rw [if_pos h.symm, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [if_neg (Ne.symm h), mul_zero]

theorem functionalEquation_classHecke [IsTotallyReal F] (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (D : (Ideal (𝓞 F))⁰) (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * (classHecke ψ).continuedLFunction s =
      ψ (Additive.ofMul (ClassGroup.mk0 D)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * ((classHecke ψ)⁻¹).continuedLFunction (1 - s)) := by
  have hU := standardOpenSubgroup_le_ker ψ
  have h := fe_of_parts F (classHecke ψ) (discrNormConductor_eq_dF_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ (standardOpenSubgroup_le_ker_inv F _ hU))
    (rootNumber_eq_coeff_different F _ hU) s h1 h2
  rw [← hD, coeff_classHecke ψ _ (nonZeroDivisors.coe_ne_zero D)] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂

theorem GlobalTheory.CompanionTheory.Hypotheses₂.partialZetaFunctionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation := by
  intro F _ _ _ C C' D hD hC
  refine ⟨GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClass C, GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClassInv C',
    GlobalTheory.CompanionTheory.Hypotheses₂.isPartialZeta_zetaOfClass C, GlobalTheory.CompanionTheory.Hypotheses₂.isPartialZeta_zetaOfClassInv C', fun s h1 h2 => ?_⟩
  rw [GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClass, GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClassInv, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have h := GlobalTheory.CompanionTheory.Hypotheses₂.functionalEquation_classHecke ψ D hD s h1 h2
  have e : ψ (Additive.ofMul C⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 D)) = ψ (Additive.ofMul C') := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, ← hC, inv_mul_cancel_left]
  calc _ = ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F *
          (GlobalTheory.CompanionTheory.PartialZeta.classHecke ψ).continuedLFunction s) := by ring
    _ = _ := by
      rw [h, ← e]
      ring
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowthStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_hermitian_form_growth : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (Q : H → H → ℂ) (Mb a : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) (hgrow : ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H), (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤ Real.exp (a * |t| * mnorm X) * (Q x x).re) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {x : H} (hx : IsSmoothVec G π x), |2 * (Q (dRep π X x) x).re| ≤ a * mnorm X * (Q x x).re := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le <;> assumption)
end

