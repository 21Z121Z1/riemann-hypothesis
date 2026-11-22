import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OkLinearTorsionCorrespondenceMapsLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaConj

theorem rationalLatticePoint_add {Λ : AddSubgroup ℂ} {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, h⟩ := hx
  obtain ⟨n, hn, h'⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have : ((m * n : ℕ) : ℂ) * (x + y) = n • ((m : ℂ) * x) + m • ((n : ℂ) * y) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [this]
  exact add_mem (nsmul_mem h n) (nsmul_mem h' m)

theorem rationalLatticePoint_neg {Λ : AddSubgroup ℂ} {x : ℂ} (hx : InRationalLattice Λ x) : InRationalLattice Λ (-x) := by
  obtain ⟨m, hm, h⟩ := hx
  exact ⟨m, hm, by rw [mul_neg]; exact neg_mem h⟩

theorem rationalLatticePoint_div_natCast {Λ : AddSubgroup ℂ} {w : ℂ} (hw : w ∈ Λ) {m : ℕ} (hm : 0 < m) : InRationalLattice Λ (w / m) := by
  refine ⟨m, hm, ?_⟩
  have : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [mul_div_cancel₀ _ this]; exact hw

theorem Good.embV_nsmul {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ} (k : ℕ)
    (A : Matrix (Fin N') (Fin N) D.host.E) : embV D T (k • A) = (k : ℂ) • embV D T A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact map_nsmul (h.embHom N N') k A

theorem Good.embV_sum {D : D7} {T : Tor D} (h : Good D T) {N N' r : ℕ} (a : Fin r → D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    embV D T (∑ j, a j • b j) = ∑ j, D.host.φ₀ (a j : D.host.E) • embV D T (b j) := by
  have := map_sum (h.embHom N N') (fun j => a j • b j) Finset.univ
  refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
  exact h.embV_smul _ _

theorem Good.smul_embV_mem {D : D7} {T : Tor D} (h : Good D T) {N N' : ℕ}
    {Y : Set (Matrix (Fin N') (Fin N) D.host.E)} {w : ℂ} (hw : w ∈ T.abelian₂)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ AddSubgroup.closure Y) :
    w • embV D T y ∈ LaS D T Y := by
  change w • h.embHom N N' y ∈ _
  induction hy using AddSubgroup.closure_induction with
  | mem x hx => exact AddSubgroup.subset_closure ⟨w, hw, x, hx, rfl⟩
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

theorem corr_lattice : ∀ (D : D7) (T T' : Tor D), Good D T → Good D T' → (∀ a : 𝓞 D.host.K, ∀ w ∈ T.abelian₂, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ T.abelian₂) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.Orthonormal D b → ∀ (S : ℂ → ℂ → Prop), (∀ t, InRationalLattice T.abelian₂ t → ∃ t', S t t') → (∀ t t₁ t₂, S t t₁ → S t t₂ → t₁ - t₂ ∈ T'.abelian₂) → (∀ t t' u u', S t t' → S u u' → S (t + u) (t' + u')) → (∀ (a : 𝓞 D.host.K) t t', S t t' → S (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t) (D.host.φ₀ (((a : D.host.K) : D.host.E)) * t')) → (∀ (m : ℕ) t t', S t t' → (m : ℂ) * t ∈ T.abelian₂ → (m : ℂ) * t' ∈ T'.abelian₂) → ∀ (n k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < n → 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧ x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧ ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y) ∧ ∀ c c' : Fin r → ℂ, (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) → ∑ j, c j • embV D T (b j) ∈ LaS D T Y → ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
  intro D T T' hT hT' hO N N' r b hb S hex huniq hadd hmul hint n k Y hn hk hkn hC
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hS0 : S 0 0 := by
    obtain ⟨t', ht'⟩ := hex 0 ⟨1, one_pos, by simp⟩
    simpa using hmul 0 _ _ ht'
  have hneg : ∀ t t', S t t' → S (-t) (-t') := fun t t' h => by
    simpa using hmul (-1) _ _ h
  have first : ∀ x ∈ LaS D T Y, ∃ c c' : Fin r → ℂ, (∀ j, InRationalLattice T.abelian₂ (c j)) ∧
      x = ∑ j, c j • embV D T (b j) ∧ (∀ j, S (c j / (n : ℂ)) (c' j / (n : ℂ))) ∧
      ∑ j, c' j • embV D T' (b j) ∈ LaS D T' Y := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, y, hy, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hC.1 y hy
      obtain ⟨u', hu'⟩ := hex _ (rationalLatticePoint_div_natCast hw (Nat.mul_pos hn hk))
      have hnk : ((n * k : ℕ) : ℂ) * u' ∈ T'.abelian₂ := by
        refine hint _ _ _ hu' ?_
        rw [mul_div_cancel₀ _ (by push_cast; exact mul_ne_zero hn0 hk0)]; exact hw
      have e1 := hT.embV_sum (fun j => (a j : D.host.K)) b
      have e2 := hT'.embV_sum (fun j => (a j : D.host.K)) b
      rw [← ha, hT.embV_nsmul] at e1
      rw [← ha, hT'.embV_nsmul] at e2
      refine ⟨fun j => D.host.φ₀ ((a j : D.host.K) : D.host.E) * w / k,
        fun j => n * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u'),
        fun j => rationalLatticePoint_div_natCast (hO _ _ hw) hk, ?_, fun j => ?_, ?_⟩
      · have : w • embV D T y = (w / k) • ((k : ℂ) • embV D T y) := by
          rw [smul_smul, div_mul_cancel₀ _ hk0]
        rw [this, e1, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]; congr 1; ring
      · have := hmul (a j) _ _ hu'
        convert this using 1
        · push_cast; field_simp
        · field_simp
      · have : ∑ j, ((n : ℂ) * (D.host.φ₀ ((a j : D.host.K) : D.host.E) * u')) • embV D T' (b j)
            = (((n * k : ℕ) : ℂ) * u') • embV D T' y := by
          have h2 : (((n * k : ℕ) : ℂ) * u') • embV D T' y
              = ((n : ℂ) * u') • ((k : ℂ) • embV D T' y) := by
            rw [smul_smul]; congr 1; push_cast; ring
          rw [h2, e2, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul]; congr 1; ring
        rw [this]
        exact AddSubgroup.subset_closure ⟨_, hnk, y, hy, rfl⟩
    | zero =>
      refine ⟨0, 0, fun j => ⟨1, one_pos, by simp⟩, by simp, fun j => by simpa using hS0, ?_⟩
      simp
    | add x y _ _ hx hy =>
      obtain ⟨c, c', h1, h2, h3, h4⟩ := hx
      obtain ⟨d, d', g1, g2, g3, g4⟩ := hy
      refine ⟨c + d, c' + d', fun j => rationalLatticePoint_add (h1 j) (g1 j), ?_, fun j => ?_, ?_⟩
      · rw [h2, g2, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, add_smul]
      · simp only [Pi.add_apply, add_div]; exact hadd _ _ _ _ (h3 j) (g3 j)
      · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; exact add_mem h4 g4
    | neg x _ hx =>
      obtain ⟨c, c', h1, h2, h3, h4⟩ := hx
      refine ⟨-c, -c', fun j => rationalLatticePoint_neg (h1 j), ?_, fun j => ?_, ?_⟩
      · rw [h2, ← Finset.sum_neg_distrib]; simp only [Pi.neg_apply, neg_smul]
      · simp only [Pi.neg_apply, neg_div]; exact hneg _ _ (h3 j)
      · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]; exact neg_mem h4
  refine ⟨first, fun c c' hS hc => ?_⟩
  obtain ⟨d, d', -, h2, h3, h4⟩ := first _ hc
  have hcd : c = d := by
    funext j
    rw [← hT.coordB_sum hb c j, h2, hT.coordB_sum hb]
  subst hcd
  obtain ⟨m, hm⟩ := hkn
  have key : ∀ j, (c' j - d' j) • embV D T' (b j) ∈ LaS D T' Y := fun j => by
    have h5 := nsmul_mem (huniq _ _ _ (hS j) (h3 j)) m
    have h6 := hT'.smul_embV_mem h5 (hC.2 j)
    rw [hT'.embV_nsmul, smul_smul] at h6
    convert h6 using 2
    have hm' : (n : ℂ) = k * m := by rw [hm]; push_cast; rfl
    rw [nsmul_eq_mul, ← sub_div, mul_right_comm, mul_comm (m : ℂ), ← hm', mul_div_cancel₀ _ hn0]
  have : ∑ j, c' j • embV D T' (b j)
      = ∑ j, d' j • embV D T' (b j) + ∑ j, (c' j - d' j) • embV D T' (b j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_smul]; congr 1; ring
  rw [this]
  exact add_mem h4 (sum_mem fun j _ => key j)

end GlobalTheory.ThetaConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalProductThetaMemThetaSpaceStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalProductTheta_mem_thetaSpace : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  first | exact @GlobalTheory.OrthoProdTheta.pullB_mem_ThSp | exact GlobalTheory.OrthoProdTheta.pullB_mem_ThSp | (intros; apply GlobalTheory.OrthoProdTheta.pullB_mem_ThSp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalRealBasisComplexCoordinatesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormal_realBasis_complex_coordinates : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ i j, coordB D (tor0 D cc δ) b i (embV D (tor0 D cc δ) (b j)) = if i = j then 1 else 0) ∧ ∀ z : VC D N N', z = ∑ j, coordB D (tor0 D cc δ) b j z • embV D (tor0 D cc δ) (b j) := by
  first | exact @GlobalTheory.OrthoCoord.orthonormal_coord | exact GlobalTheory.OrthoCoord.orthonormal_coord | (intros; apply GlobalTheory.OrthoCoord.orthonormal_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalTransitionDetMulConjEqOneStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalTransition_det_mul_conj_eq_one : ∀ (D : D7), admG1 D → ∀ (N N' r : ℕ) (b₀ b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b₀ → OnB D b → (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) * D.host.conj (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) = 1 := by
  first | exact @GlobalTheory.NormSum.det_onB_mul_conj | exact GlobalTheory.NormSum.det_onB_mul_conj | (intros; apply GlobalTheory.NormSum.det_onB_mul_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinValuesAtZero
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RankinZero

lemma ch_bdd {M : ℕ} (ξ : DirichletCharacter ℂ M) : ∃ C : ℝ, ∀ x, ‖ch ξ x‖ ≤ C :=
  ⟨1, fun x => DirichletCharacter.norm_le_one ξ _⟩

lemma lseries_Vo (l : ℕ) (hl : 0 < l) (t : ℂ) (h b : ℕ → ℂ) (hb : ∀ n, n ≠ 0 → b (l * n) = t * b n)
    (W : ℂ) :
    LSeries (fun n => conj (Vo l h n) * b n) W = t / (l : ℂ) ^ W * LSeries (fun n => conj (h n) * b n) W := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hinj : Function.Injective (fun m : ℕ => l * m) := fun a c hac => Nat.eq_of_mul_eq_mul_left hl hac
  have hsupp : Function.support (LSeries.term (fun n => conj (Vo l h n) * b n) W) ⊆ Set.range (fun m : ℕ => l * m) := by
    intro n hn
    by_cases hd : l ∣ n
    · obtain ⟨m, rfl⟩ := hd
      exact ⟨m, rfl⟩
    · exfalso
      apply hn
      simp [LSeries.term, Vo, hd]
  unfold LSeries
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  congr 1
  funext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [LSeries.term]
  · have hm0 : m ≠ 0 := hm.ne'
    have hlm : l * m ≠ 0 := Nat.mul_ne_zero hl.ne' hm0
    rw [LSeries.term_of_ne_zero hlm, LSeries.term_of_ne_zero hm0]
    have hV : Vo l h (l * m) = h m := by
      simp [Vo, Nat.mul_div_cancel_left m hl]
    rw [hV, hb m hm0]
    push_cast
    rw [natCast_mul_natCast_cpow]
    ring

end GlobalTheory.EisM.RankinZero

namespace GlobalTheory.EisM

theorem rankin_values_at_zero : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (c₀ : ℂ), 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → Prim (2 * e + 1) N χ g → Wt (N * l) ρ → (∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) → φ ≠ 1 → MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)) → ∃ P : ℂ, P ≠ 0 ∧ pet (2 * e + 1) ρ (qs fun n => conj (g n)) (fun τ => qs (eis e c₀ (ch ψ) (ch θ)) τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) = P ∧ pet (2 * e + 1) ρ (qs (Vo l fun n => conj (g n))) (fun τ => qs (eis e c₀ (ch ψ) (ch θ)) τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) = θ l / (l : ℂ) ^ (2 * e) * P := by
  intro e N l χ θ ψ φ g ρ c₀ he hN hl hlN hg hρ hφ hφ1 hb
  haveI : Fact l.Prime := ⟨hl⟩
  have hLpos : 0 < N * l := Nat.mul_pos hN hl.pos
  have hNL : N ∣ N * l := dvd_mul_right N l
  set b := eis e c₀ (ch ψ) (ch θ) with hbdef
  set h : ℕ → ℂ := fun n => conj (g n) with hhdef
  set Φ := latF (N * l) (fun _ => 1) φ with hΦdef
  have hCFg : CF (2 * e + 1) N (ch χ) g := hg.cf
  have hCFh0 : CF (2 * e + 1) N (ch χ⁻¹) h := (GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char (2 * e + 1) N χ g).1 hCFg
  have hCFh : CF (2 * e + 1) (N * l) (ch χ⁻¹) h :=
    (GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) N (ch χ⁻¹)).2.2.2.2.2 (N * l) h hNL hCFh0
  have hCFVh : CF (2 * e + 1) (N * l) (ch χ⁻¹) (Vo l h) :=
    (GlobalTheory.T.coeffHeckeVOperator_raises_level (2 * e + 1) N l (ch χ⁻¹) h hl.pos).2 hCFh0
  obtain ⟨hPolyb, hbbd, -⟩ := GlobalTheory.T.coeffEisensteinSeriesTwisted_qExpansion_double e c₀ (ch ψ) (ch θ) (RankinZero.ch_bdd ψ) (RankinZero.ch_bdd θ)
  have hΦbd : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C := by
    refine ⟨1, fun x => ?_⟩
    simp only [hΦdef, latF]
    split_ifs
    · simpa using DirichletCharacter.norm_le_one φ _
    · simp

  have hmult : ∀ d : ℤ, IsCoprime d ((N * l : ℕ) : ℤ) →
      (fun d => ch ψ d * ch θ d) d = ch φ d * ch χ⁻¹ d := by
    intro d hd
    have hd' : IsCoprime d ((N : ℤ) * l) := by push_cast at hd; exact hd
    have hdN : IsCoprime d (N : ℤ) := hd'.of_mul_right_left
    obtain ⟨u, v, huv⟩ := hdN
    have hunit : IsUnit (d : ZMod N) := by
      have h1 := congrArg (Int.cast : ℤ → ZMod N) huv
      push_cast at h1
      rw [ZMod.natCast_self, mul_zero, add_zero] at h1
      exact ⟨⟨(d : ZMod N), (u : ZMod N), by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    have hχ : χ (d : ZMod N) ≠ 0 := (hunit.map χ).ne_zero
    show ch ψ d * ch θ d = ch φ d * ch χ⁻¹ d
    rw [hφ d]
    simp only [ch, MulChar.mul_apply, MulChar.inv_apply_eq_inv']
    field_simp

  have hLφ : (fun n : ℕ => φ n) = fun n : ℕ => χ n * ψ n * θ n := by
    funext n
    have := hφ (n : ℤ)
    simp only [ch, Int.cast_natCast, MulChar.mul_apply] at this
    rw [this]
    ring
  have hψmul : ∀ m n : ℕ, ψ ((m * n : ℕ) : ZMod l) = ψ (m : ZMod l) * ψ (n : ZMod l) := by
    intro m n; push_cast; exact map_mul ψ _ _
  have hθmul : ∀ m n : ℕ, θ ((m * n : ℕ) : ZMod N) = θ (m : ZMod N) * θ (n : ZMod N) := by
    intro m n; push_cast; exact map_mul θ _ _
  have hnorm : ∀ n : ℕ, ‖χ (n : ZMod N)‖ ≤ 1 ∧ ‖ψ (n : ZMod l)‖ ≤ 1 ∧ ‖θ (n : ZMod N)‖ ≤ 1 :=
    fun n => ⟨DirichletCharacter.norm_le_one χ _, DirichletCharacter.norm_le_one ψ _,
      DirichletCharacter.norm_le_one θ _⟩
  have hhecke : ∀ m n : ℕ, 0 < m → 0 < n → g m * g n =
      ∑ δ ∈ (Nat.gcd m n).divisors, χ (δ : ZMod N) * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2) := by
    have := (GlobalTheory.T.depletedCuspEigenform_heckeRelations (2 * e + 1) N χ g (by omega) hN hg).2.2
    simpa using this
  have hsum : ∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t) :=
    fun t ht => (GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) N (ch χ) g (by omega) hCFg).2.2.1 t ht
  have hbform : ∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal,
      ψ (p.1 : ZMod l) * (p.1 : ℂ) ^ (e - 1) * θ (p.2 : ZMod N) := by
    intro n hn
    simp [hbdef, eis, ch, hn]

  have hbl : ∀ n, n ≠ 0 → b (l * n) = θ (l : ZMod N) * b n := by
    have hψ0 : ∀ x : ℤ, (l : ℤ) ∣ x → ch ψ x = 0 := by
      intro x hx
      simp only [ch]
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd x l).mpr hx]
      exact MulChar.map_zero ψ
    have hθl : ∀ y : ℤ, ch θ ((l : ℤ) * y) = ch θ (l : ℤ) * ch θ y := by
      intro y; simp only [ch]; push_cast; exact map_mul θ _ _
    intro n hn
    have := (GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV e l c₀ (ch θ (l : ℤ)) (ch ψ) (ch θ) hl).1 hψ0 hθl n hn
    simpa [ch] using this

  have hI : ∀ s : ℝ, 0 < s →
      pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) =
        ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ) *
          (LSeries (fun n => ψ (n : ZMod l) * g n) ((e + 1 : ℝ) + s : ℝ) *
            LSeries (fun n => θ (n : ZMod N) * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ)) := by
    intro s hs
    rw [GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ h b s he hs hLpos hNL hρ hφ1 hCFh hb hmult hbbd]
    have hd := GlobalTheory.T.rankin_dirichlet_series_identity_hecke e (fun n => χ (n : ZMod N)) (fun n => ψ (n : ZMod l)) (fun n => θ (n : ZMod N)) g s he hs
      hψmul hθmul hnorm hhecke hsum b hbform
    have hgb : (fun n => conj (h n) * b n) = fun n => g n * b n := by
      funext n; simp [hhdef]
    rw [hgb, hLφ, ← hd.2]
    ring

  have hI' : ∀ s : ℝ, 0 < s →
      pet (2 * e + 1) ρ (qs (Vo l h)) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) =
        θ (l : ZMod N) / (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ) *
          pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) := by
    intro s hs
    rw [GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ (Vo l h) b s he hs hLpos hNL hρ hφ1 hCFVh hb hmult hbbd,
      GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ h b s he hs hLpos hNL hρ hφ1 hCFh hb hmult hbbd,
      RankinZero.lseries_Vo l hl.pos _ h b hbl]
    ring

  have hlim := GlobalTheory.T.rankinIntegral_tendsto_at_zero (2 * e + 1) (e + 1) (N * l) (N * l) N χ⁻¹ Φ ρ h b (by omega) (by omega) hLpos hLpos hNL
    hρ hCFh hPolyb hΦbd
  have hlim' := GlobalTheory.T.rankinIntegral_tendsto_at_zero (2 * e + 1) (e + 1) (N * l) (N * l) N χ⁻¹ Φ ρ (Vo l h) b (by omega) (by omega) hLpos hLpos
    hNL hρ hCFVh hPolyb hΦbd
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  obtain ⟨-, v₁, hv₁, hL₁⟩ := GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N l χ ψ g ((e : ℝ) + 1) (odd_two_mul_add_one e) hN hl.pos hg
    (by push_cast; linarith)
  obtain ⟨-, v₂, hv₂, hL₂⟩ := GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N N χ θ g (2 * (e : ℝ)) (odd_two_mul_add_one e) hN hN hg
    (by push_cast; linarith)
  have hΓ : Tendsto (fun s : ℝ => ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun s : ℝ => ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ)) 0 := by
      apply Complex.continuous_ofReal.continuousAt.comp
      apply ContinuousAt.div
      · apply ContinuousAt.comp (g := Real.Gamma) _ (continuous_const.add continuous_id).continuousAt
        refine (Real.differentiableAt_Gamma fun m hm => ?_).continuousAt
        have := m.cast_nonneg (α := ℝ)
        have hm' : 2 * (e : ℝ) + 0 = -(m : ℝ) := hm
        linarith
      · exact (Real.continuousAt_const_rpow (by positivity)).comp (continuous_const.add continuous_id).continuousAt
      · positivity
    simpa using hc.tendsto
  set P : ℂ := ((Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) : ℝ) : ℂ) * (v₁ * v₂) with hPdef
  have hprod : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs h)
      (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 P) := by
    refine (hΓ.mul (hL₁.mul hL₂)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hI s hs).symm
  have hP0 := tendsto_nhds_unique hlim hprod
  have hPne : P ≠ 0 := by
    have hΓpos : 0 < Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) :=
      div_pos (Real.Gamma_pos_of_pos (by linarith)) (by positivity)
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hΓpos.ne') (mul_ne_zero hv₁ hv₂)
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hcp : Tendsto (fun s : ℝ => θ (l : ZMod N) / (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) (𝓝[>] 0)
      (𝓝 (θ (l : ZMod N) / (l : ℂ) ^ (2 * e))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun s : ℝ => (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).const_cpow (Or.inl hl0)
    have h0 : (l : ℂ) ^ (((2 * (e : ℝ) + 0 : ℝ)) : ℂ) = (l : ℂ) ^ (2 * e) := by
      rw [show (((2 * (e : ℝ) + 0 : ℝ)) : ℂ) = ((2 * e : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
    have h1 : Tendsto (fun s : ℝ => (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) (𝓝 0) (𝓝 ((l : ℂ) ^ (2 * e))) := by
      rw [← h0]; exact hc.tendsto 0
    exact tendsto_const_nhds.div h1 (pow_ne_zero _ hl0)
  have hlimP : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs h)
      (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 P) := hprod
  have hprod' : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs (Vo l h))
      (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0)
      (𝓝 (θ (l : ZMod N) / (l : ℂ) ^ (2 * e) * P)) := by
    refine (hcp.mul hlimP).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hI' s hs).symm
  exact ⟨P, hPne, hP0, tendsto_nhds_unique hlim' hprod'⟩

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembershipStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoints_integralPoints_membership : ∀ (D : D7) (N : ℕ), (∀ g : GA D N, g ∈ ratG D N ↔ ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ k : GA D N, k ∈ intG D N ↔ IntG D (k : GL (Fin N) (AE D))) ∧ (∀ γ : Matrix (Fin N) (Fin N) D.host.E, γ * (γ.map D.host.conj).transpose = 1 → ∃ g : GA D N, IsRat D (g : GL (Fin N) (AE D)) γ) ∧ (∀ (g : GA D N) γ, IsRat D (g : GL (Fin N) (AE D)) γ → γ * (γ.map D.host.conj).transpose = 1) ∧ Function.Injective (inc D) := by
  first | exact @GlobalTheory.NormSum.mem_ratG_intG | exact GlobalTheory.NormSum.mem_ratG_intG | (intros; apply GlobalTheory.NormSum.mem_ratG_intG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralCharImEqZero
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical Pointwise

namespace GlobalTheory.UnitaryTheta

theorem setIntegral_mul_char_eq_zero {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V)
    (hF : IsAddFundamentalDomain Λ Fd μ) (f : V → ℂ) (hf : ∀ x y, f (x + y) = f x * f y)
    (hΛ : ∀ y ∈ Λ, f y = 1) (t : V) (ht : f t = -1) : ∫ z in Fd, f z ∂μ = 0 := by
  have hq : MeasurePreserving (fun x => t + x) μ μ := measurePreserving_add_left μ t
  have hF' : IsAddFundamentalDomain Λ ((fun x => t + x) ⁻¹' Fd) μ :=
    hF.preimage_of_equiv hq.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by simp [AddSubgroup.vadd_def, add_left_comm])
  have h1 : ∫ z in (fun x => t + x) ⁻¹' Fd, f z ∂μ = ∫ z in Fd, f z ∂μ :=
    hF'.setIntegral_eq hF (fun g x => by simp [AddSubgroup.vadd_def, hf, hΛ g g.2])
  have h2 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = ∫ z in Fd, f z ∂μ :=
    hq.setIntegral_preimage_emb (measurableEmbedding_addLeft t) f Fd
  have h3 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = - ∫ z in Fd, f z ∂μ := by
    simp only [hf, ht, neg_one_mul, integral_neg, h1]
  linear_combination (h3 - h2) / 2

theorem setIntegral_char_im_eq_zero :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ v : V, v ≠ 0 → (∀ y ∈ Λ, ∃ m : ℤ, (H v y).im = m) → ∫ z in Fd, cexp (2 * π * I * ((H v z).im : ℂ)) ∂μ = 0 := by
  intro V _ _ _ _ _ μ _ H hH Λ _ Fd hF v hv hint
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  have hpos := hH.2 v hv
  set r : ℝ := (H v v).re with hr
  refine setIntegral_mul_char_eq_zero μ Λ Fd hF (fun z => cexp (2 * π * I * ((H v z).im : ℂ)))
    (fun x y => ?_) (fun y hy => ?_) (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v) ?_
  · simp only [map_add, add_im, ofReal_add, mul_add, Complex.exp_add]
  · obtain ⟨m, hm⟩ := hint y hy
    simp only [hm, ofReal_intCast]
    rw [mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I m
  · have e : (H v (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v)).im = 1 / 2 := by
      rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, conj_ofReal, conj_I]
      simp only [mul_im, mul_re, ofReal_re, ofReal_im, neg_re, neg_im, I_re, I_im, ← hr]
      field_simp
      ring
    simp only [e]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring

end GlobalTheory.UnitaryTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignedTranslationAddSelfDualLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem al_add (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N'))
    (h1 : ∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) (h2 : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m)
    (h3 : ∀ x ∈ A, w0 D • x ∈ A) : ∀ x ∈ A, ∀ y ∈ A, al D T (x + y) =
      al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) := by
  intro x hx y hy
  obtain ⟨a, ha⟩ := h2 x hx
  obtain ⟨c, hc⟩ := h2 y hy
  obtain ⟨b, hb⟩ := h1 x hx y hy
  obtain ⟨k, hk⟩ := h1 _ (h3 x hx) y hy
  have hal : ∀ z : VC D N N', ∀ m : ℤ, qH D T z = m → al D T z = (-1 : ℂ) ^ m := by
    intro z m hm
    have e : al D T z = (-1 : ℂ) ^ (round (qH D T z)) := rfl
    rw [e, hm, round_intCast]
  have hk' : Real.sqrt D.host.d * (Hf D T x y).re = 2 * k - b := by
    rw [Hf_smul_left] at hk
    rw [← hk, ← hb]
    simp [w0, Complex.mul_im]
    ring
  have hs : qH D T (x + y) = ((a + c + (2 * k - b) : ℤ) : ℝ) := by
    push_cast
    rw [← ha, ← hc, ← hk']
    simp only [qH, Hf_add_left, Hf_add_right, Complex.add_re, Hf_re_swap D T x y]
    ring
  have he : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) = (-1 : ℂ) ^ (-b) := by
    rw [hb, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  rw [hal _ _ hs, hal _ _ ha, hal _ _ hc, he, sub_eq_add_neg, zpow_add₀ hn, zpow_add₀ hn, zpow_add₀ hn,
    zpow_mul]
  simp

end GlobalTheory.GalTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeriesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorCoeff_conjugateSeries : ∀ (D : D7) (N N' : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D N N' → ℂ), Differentiable ℂ (fnConj D M ρ G) → fnConj D M ρ G ≠ 0 → (∀ α, taylor D (fnConj D M ρ G) α = cj M ρ (taylor D G α)) ∧ (CoefIn D G M → ∀ (n : D.what₂.Tau → ℕ) (T : Tup D N N' n), GL3Theta.applyAt0 D (minorPol D T) G ∈ M ∧ cj M ρ (GL3Theta.applyAt0 D (minorPol D T) G) = GL3Theta.applyAt0 D (minorPol D T) (fnConj D M ρ G)) := by
  first | exact @GlobalTheory.ConjSeries.taylor_fnConj | exact GlobalTheory.ConjSeries.taylor_fnConj | (intros; apply GlobalTheory.ConjSeries.taylor_fnConj <;> assumption)
end

