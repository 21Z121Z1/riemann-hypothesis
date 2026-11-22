import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0204
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0185
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0186
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelMatrixSkewCoordinatesRationalAut
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovSkew

theorem herm_esI {k r : ℕ} (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (esI k r a)) = u (eI k r a) := by
  have ha := a.2
  have ht : WeylGroupFacts.tau k r (esI k r a) = eI k r a := by
    have h1 : (esI k r a).val < r ∨ r + k < (esI k r a).val := Or.inr (by simp only [esI]; omega)
    apply Fin.ext; unfold WeylGroupFacts.tau; dsimp only; rw [if_pos h1]; simp only [esI, eI]; omega
  have hs : WeylGroupFacts.sgn k r (esI k r a) = 1 := if_neg (by simp only [esI]; omega)
  unfold herm bvec
  rw [← Pi.single_star, star_one, single_one_dotProduct]
  simp only [mulVec, dotProduct, WeylGroupFacts.hpk_row, ht, hs]
  simp

theorem sum_eI_apply {k r : ℕ} (c : Fin r → ℂ) (a : Fin r) :
    (∑ b, c b • bvec (eI k r b)) (eI k r a) = c a := by
  simp [Finset.sum_apply, Rad.bvec_apply, Rad.eI_inj]

theorem coords_skew : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → q.1 = 0 → q.2.1 = 0 → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') ∧ (∀ p : {p : UT r // N.j ≤ p.1.1.val}, q.2.2.1 p = ((ρ ^ ((r - p.1.1.1.val) + (r - p.1.1.2.val)) : ℝ) : ℂ) * σ (H.B (s (N.ist p.1.1.2)) (N.ist p.1.1.1))) ∧ ∀ a : {a : Fin r // N.j ≤ a.val}, q.2.2.2 a = ρ ^ (2 * (r - a.1.val)) * (σ (H.B (s (N.ist a.1)) (N.ist a.1))).im := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF s q hq hq1 hq2
  obtain ⟨hr, -, -, -, -, he, hi, -⟩ := hF
  have he1 : ∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) := fun a => (he a).1
  have ht : ∀ n : ℕ, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (pow_pos hρ n).ne'
  set S : Matrix (Fin r) (Fin r) ℂ := skewM (Swap.extS r N.j q.2.2).1 (Swap.extS r N.j q.2.2).2 with hSdef
  have hM : crd k r N.j β q = pEl k r 0 S := by
    rw [RefCovTop.crd_of_zero β q hq1, Swap.pTop_eq, pOf, hq2, map_zero]
  have hS0 : ∀ a b : Fin r, ¬ N.j ≤ a.val → S a b = 0 := fun a b ha => Swap.skew_ext_zero q.2.2 a b ha
  have hcol : ∀ b : Fin r, pEl k r 0 S *ᵥ bvec (esI k r b) = bvec (esI k r b) + ∑ a, S a b • bvec (eI k r a) := by
    intro b
    rw [((Rad.radical k r).1 0 S).2.2.1 b]
    simp [herm]
  have hsb : ∀ b : Fin r, N.j ≤ b.val → Φ (s (N.ist b)) =
      (((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) • (bvec (esI k r b) + ∑ a, S a b • bvec (eI k r a)) := by
    intro b hb; rw [← hq, hM, hi b hb, mulVec_smul, hcol]
  have hB : ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → σ (H.B (s (N.ist b)) (N.ist a)) =
      (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * ((((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) * S a b) := by
    intro a b ha hb
    rw [← hr.2.2.1, hsb b hb, hi a ha, RealMat.herm_smul_right, herm_esI, Pi.smul_apply, Pi.add_apply, sum_eI_apply,
      Rad.bvec_apply, if_neg (Rad.eI_ne_esI a b), zero_add, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  refine ⟨fun b hb => ?_, fun p => ?_, fun a => ?_⟩
  · have hΦy : Φ (s (N.ist b) - N.ist b) = ∑ a, ((((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) * S a b) • bvec (eI k r a) := by
      rw [RealMat.phi_sub hr, hsb b hb, hi b hb, smul_add, add_sub_cancel_left, Finset.smul_sum]
      simp_rw [smul_smul]
    have hproj : NFGeom.proj N (s (N.ist b) - N.ist b) = s (N.ist b) - N.ist b := by
      apply RealMat.phi_inj hr
      rw [NFGeom.proj_apply, RealMat.phi_sum hr, hΦy, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs with ha
      · rw [hr.2.1, he1, ← hr.2.2.1, hΦy, hi a ha, RealMat.herm_smul_right, herm_esI, sum_eI_apply, smul_smul]
        congr 1
        rw [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv, mul_comm, ← mul_assoc,
          mul_inv_cancel₀ (ht _), one_mul]
      · rw [hS0 a b ha, mul_zero, zero_smul]
    rw [← hproj]; exact NFGeom.proj_mem N _
  · obtain ⟨⟨⟨a, b⟩, hab⟩, ha⟩ := p
    have hab' : a < b := hab
    have ha' : N.j ≤ a.val := ha
    have hb : N.j ≤ b.val := le_trans ha' (le_of_lt hab')
    simp only
    rw [hB a b ha' hb]
    have hSab : S a b = q.2.2.1 ⟨⟨(a, b), hab⟩, ha⟩ := by
      simp [hSdef, skewM, hab', Swap.extS, Swap.extZ, ha']
    rw [hSab, pow_add, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv]
    have h1 := ht (r - a.val)
    have h2 := ht (r - b.val)
    field_simp
  · obtain ⟨a, ha⟩ := a
    simp only
    rw [hB a a ha ha]
    have hSaa : S a a = ((q.2.2.2 ⟨a, ha⟩ : ℝ) : ℂ) * Complex.I := by
      simp [hSdef, skewM, Swap.extS, Swap.extZ, ha]
    rw [hSaa]
    have e : ((((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * ((((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * (((q.2.2.2 ⟨a, ha⟩ : ℝ) : ℂ) * Complex.I))) =
        (((ρ ^ (r - a.val))⁻¹ * ((ρ ^ (r - a.val))⁻¹ * q.2.2.2 ⟨a, ha⟩) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, Complex.mul_I_im, Complex.ofReal_re, two_mul, pow_add]
    have h1 : ρ ^ (r - a.val) ≠ 0 := (pow_pos hρ _).ne'
    field_simp

end GlobalTheory.DegVol.RefCovSkew
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRegularDoubleCosetPolynomialProperness
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.PolyProper

variable {k r : ℕ}

theorem gram_det_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hermitian_pos_facts_hold k r).2.1

theorem mul_mem {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (unitary_group_holds _ _ gram_det_unit).2.1 g hg h hh

theorem inv_mem {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).2

theorem det_unit {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).1

theorem mem_of_S {z : Fin (2 * r + k + 1) → ℂ} {s : Mat k r} (hs : s ∈ Sset k r z) : s ∈ GG k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact mul_mem hh.1 hm.1

theorem inv_eq {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [Matrix.mul_assoc (Hpk k r), Matrix.mul_assoc (Hpk k r), h]
  exact (hermitian_pos_facts_hold k r).2.1

theorem left_bound (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)) (hz : inWb k r z)
    (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (hC : IsCompact C)
    (hCr : C ⊆ Greg k r z z') :
    ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z',
      opn s ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  obtain ⟨C1, h1⟩ := GlobalTheory.T.siegel_region_norm_bound k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C2, h2⟩ := GlobalTheory.T.isometry_opNorm_bounded_by_two_frames k r z z' C hz hz' hT hT' hC
    (fun γ hγ => ⟨(hCr hγ).1, (hCr hγ).2.2⟩)
  obtain ⟨hN1, -, -, -, hN5, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  refine ⟨C2 * (max 1 C1) ^ 2, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hx1 : 1 ≤ opn (s * γ * s'⁻¹) := (hN1 _ hxG).2
  have hxs : (s * γ * s'⁻¹) * s' = s * γ := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_unit hs'G), Matrix.mul_one]
  have h1' := h1 γ hγ s hs s' hs'
  have h5 := hN5 (s * γ * s'⁻¹)
  set X := opn (s * γ * s'⁻¹) with hX
  have hp1 : 1 ≤ X ^ (r * (r + 1)) := one_le_pow₀ hx1
  have hm1 : (1 : ℝ) ≤ max 1 C1 := le_max_left _ _
  have hle : C1 * X ^ (r * (r + 1)) ≤ max 1 C1 * X ^ (r * (r + 1)) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hQ1 : 1 ≤ max 1 C1 * X ^ (r * (r + 1)) := one_le_mul_of_one_le_of_one_le hm1 hp1
  have hB : 1 ≤ X * (max 1 C1 * X ^ (r * (r + 1))) := one_le_mul_of_one_le_of_one_le hx1 hQ1
  have key := h2 γ hγ s hsG (X * (max 1 C1 * X ^ (r * (r + 1)))) hB (by
    rintro (a | b)
    · show eucl (s *ᵥ fvec k r z a) ≤ _
      refine ((h1' a).1.trans hle).trans ?_
      exact le_mul_of_one_le_left (by linarith) hx1
    · show eucl (s *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _
      rw [Matrix.mulVec_mulVec, ← hxs, ← Matrix.mulVec_mulVec]
      refine (h5 _).trans ?_
      exact mul_le_mul_of_nonneg_left ((h1' b).2.trans hle) (by linarith))
  refine key.trans (le_of_eq ?_)
  ring

theorem poly_proper : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', max (opn s) (opn s') ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  intro k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C1, h1⟩ := left_bound z z' C hz hz' hT hT' hC hCr
  have hcont : Continuous fun g : Mat k r => Hpk k r * gᴴ * Hpk k r :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hCr' : (fun g : Mat k r => Hpk k r * gᴴ * Hpk k r) '' C ⊆ Greg k r z' z := by
    rintro _ ⟨γ, hγ, rfl⟩
    have hγG : γ ∈ GG k r := (hCr hγ).1
    show Hpk k r * γᴴ * Hpk k r ∈ _
    rw [← inv_eq hγG]
    exact (GlobalTheory.T.besselZhat_inv_and_regular_iff k r z z' γ hγG).2.1 (hCr hγ)
  obtain ⟨C2, h2⟩ := left_bound z' z _ hz' hz hT' hT (hC.image hcont) hCr'
  obtain ⟨hN1, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  refine ⟨max 1 (max C1 C2), le_max_left _ _, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hinv : s' * γ⁻¹ * s⁻¹ = (s * γ * s'⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (det_unit hs'G),
      Matrix.mul_assoc]
  have ha := h1 γ hγ s hs s' hs'
  have hb := h2 γ⁻¹ ⟨γ, hγ, (inv_eq hγG).symm⟩ s' hs' s hs
  rw [hinv, (hN1 _ hxG).1] at hb
  have hp : 0 ≤ opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := pow_nonneg (opn_nonneg _) _
  refine max_le (ha.trans ?_) (hb.trans ?_)
  · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hp
  · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hp

end GlobalTheory.SgInf.PolyProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BiorthogonalBlockFramesTriangularStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biorthogonal_block_frames_triangular : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (T U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (T' U' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ), Biorth r m T T' → Biorth r m U U' → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → U' b *ᵥ y = 0) → (∀ b, (U' b * T b) * (T' b * U b) = 1) ∧ ∀ c, ∀ Y ∈ lowers W c, ∀ b, U' b * Y * U (b + c + 1) = (U' b * T b) * (T' b * Y * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) := by
  first | exact @GlobalTheory.RadCov.blockFrames_triangular | exact GlobalTheory.RadCov.blockFrames_triangular | (intros; apply GlobalTheory.RadCov.blockFrames_triangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistableStatement
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFlag_exists_unique_semistable : ∀ (I : AutInst) (x : I.GA), (∃ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ) ∧ (∀ (a a' : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (j' : Fin a' → ℕ) (τ' : Fin a' → ℝ), HasType I x j τ → HasType I x j' τ' → ∃ h : a = a', (∀ i, j i = j' (Fin.cast h i)) ∧ ∀ i, τ i = τ' (Fin.cast h i)) ∧ ∀ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i : Fin a, S i.castSucc = stepLt I x (τ i) ∧ rkK (S i.castSucc) < rkK (S i.succ) ∧ largestSize (bas I) (frm I x) (S i.succ) = τ i ∧ (∀ N, S i.castSucc < N → N ≤ lamX I x → τ i ≤ sizeQ (bas I) (frm I x) N (S i.castSucc)) ∧ ∀ N, S i.castSucc ≤ N → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (S i.succ) N → N ≠ S i.succ → sizeQ (bas I) (frm I x) (S i.succ) N ≤ τ i) ∧ (1 ≤ I.n → (a = 0 ↔ 1 / 2 ≤ least I x) ∧ ∀ h : 0 < a, τ ⟨0, h⟩ = least I x) := by
  first | exact @GlobalTheory.PointFlag.flag_spec | exact GlobalTheory.PointFlag.flag_spec | (intros; apply GlobalTheory.PointFlag.flag_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.FlagIso

theorem exists_extension {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ P : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤)
    (hsat : ∀ c : O, c ≠ 0 → ∀ v ∈ Λ, c • v ∈ P → v ∈ P) (f : V →ₗ[K] K)
    (hf : ∀ z ∈ P, f z ∈ (algebraMap O K).range) :
    ∃ g : V →ₗ[K] K, (∀ z ∈ Λ, g z ∈ (algebraMap O K).range) ∧ ∀ z ∈ Λ, z ∈ P → g z = f z := by
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := fun s => by
        have := isLocalizedModule_id (nonZeroDivisors O) V K
        exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
      surj := fun y => by
        have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
        obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
        rw [Submodule.span_eq] at hs
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := P.comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c (nonZeroDivisors.coe_ne_zero c) v v.2 h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  have hu : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O K) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors O) (Algebra.linearMap O K) x
  let g : V →ₗ[K] K := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype
        (f.restrictScalars O ∘ₗ Λ.subtype ∘ₗ π) hu)
  have hg : ∀ y : Λ, g y = f (π y) := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hu y
  refine ⟨g, fun z hz => ?_, fun z hz hP => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact hf _ (hπ _)
  · rw [hg ⟨z, hz⟩, hπ' ⟨z, hz⟩ hP]

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def hR (x : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun y := Formalism.UG.hform (starRingEnd E) J x y
  map_add' y z := by simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_apply (x y : Fin n → E) : hR J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hform_star (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (x y : Fin n → E) :
    star (Formalism.UG.hform (starRingEnd E) J x y) = Formalism.UG.hform (starRingEnd E) J y x := by
  have h : ∀ i j, star (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    exact this
  simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_hR_eq (hJ : J.det ≠ 0) (g : (Fin n → E) →ₗ[E] E) : ∃ y, hR J y = g := by
  refine ⟨star ((fun j => g (Pi.single j 1)) ᵥ* J⁻¹), ?_⟩
  ext j
  have h1 : ((fun j => g (Pi.single j 1)) ᵥ* J⁻¹) ᵥ* J = fun j => g (Pi.single j 1) := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.vecMul_one]
  have h2 := congrFun h1 j
  simp only [LinearMap.comp_apply, LinearMap.single_apply, hR_apply]
  rw [← h2]
  simp only [Formalism.UG.hform, starRingEnd_apply, Pi.star_apply, star_star]
  simp [Pi.single_apply, Matrix.vecMul, dotProduct]

end Form

theorem star_mem_range {E : Type} [Field E] [StarRing E] {a : E}
    (h : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨⟨_, map_isIntegral_int (starRingEnd E) b.isIntegral_coe⟩, rfl⟩

theorem card_le_of_isotropic {n k : ℕ} (ε : Fin n → Bool) (u : Fin k → Fin n → ℂ)
    (hu : LinearIndependent ℂ u) (hiso : ∀ i j, star (u i) ⬝ᵥ (Jm ε *ᵥ u j) = 0) (b : Bool) :
    k ≤ (univ.filter fun a => ε a = b).card := by
  let T : (Fin k → ℂ) →ₗ[ℂ] ({a // ε a = b} → ℂ) :=
    LinearMap.funLeft ℂ ℂ Subtype.val ∘ₗ Fintype.linearCombination ℂ u
  have hT : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h0 : star (∑ i, c i • u i) ⬝ᵥ (Jm ε *ᵥ ∑ i, c i • u i) = 0 := by
      simp only [star_sum, star_smul, sum_dotProduct, Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul,
        smul_dotProduct, dotProduct_smul, hiso, smul_zero, Finset.sum_const_zero]
    have h1 : ∀ a, ε a = b → (∑ i, c i • u i) a = 0 := fun a ha => congrFun hc ⟨a, ha⟩
    have h3 : ∑ i, c i • u i = 0 := by
      generalize ∑ i, c i • u i = w at h0 h1
      have h2 : star w ⬝ᵥ (Jm ε *ᵥ w) = (if b then -1 else 1) * (star w ⬝ᵥ w) := by
        simp only [dotProduct, Jm, Matrix.mulVec_diagonal, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : ε a = b
        · simp [h1 a ha]
        · cases b <;> simp_all
      rw [h2] at h0
      have h4 : star w ⬝ᵥ w = 0 := by cases b <;> simpa using h0
      open ComplexOrder in exact dotProduct_star_self_eq_zero.1 h4
    funext i
    exact Fintype.linearIndependent_iff.1 hu c h3 i
  have := LinearMap.finrank_le_finrank_of_injective hT
  simpa [Fintype.card_subtype] using this

variable (I : AutInst)

theorem rkK_le_rkR (S : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hS : ∀ y ∈ S, ∀ z ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) (v : InfinitePlace I.F) :
    rkK S ≤ rkR (I.ε v) := by
  obtain ⟨b, hbS, -, hb⟩ := Submodule.exists_fun_fin_finrank_span_eq I.E (S : Set (Fin I.n → I.E))
  letI : Algebra I.E ℂ := (I.φ v).toAlgebra
  have h1 : LinearIndependent ℂ (fun i => (I.φ v) ∘ b i) :=
    (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 hb
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPi : ∀ w : Fin I.n → ℂ, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  have h2 : LinearIndependent ℂ (fun i => (I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b i)) := by
    apply LinearIndependent.of_comp (Matrix.mulVecLin (I.P v))
    simpa [Function.comp_def, hPi] using h1
  have h3 : ∀ i j, star ((I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b i)) ⬝ᵥ
      (Jm (I.ε v) *ᵥ ((I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b j))) = 0 := by
    intro i j
    rw [← I.P_spec v, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPi, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec, hPi]
    have h4 := congrArg (I.φ v) (hS _ (hbS i) _ (hbS j))
    rw [map_zero] at h4
    rw [← h4]
    simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_apply, I.cm.cmUnram.2.1, dotProduct,
      Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, Function.comp_apply, Matrix.map_apply]
  exact le_min (card_le_of_isotropic _ _ h2 h3 true) (card_le_of_isotropic _ _ h2 h3 false)

theorem mem_perpIn (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) (y : Fin I.n → I.E) :
    y ∈ perpIn I x S ↔ y ∈ lamX I x ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨zero_mem _, fun s _ => map_zero (hR I.J s)⟩
  | add y z _ _ hy hz =>
    exact ⟨add_mem hy.1 hz.1, fun s hs => by
      rw [← hR_apply, map_add, hR_apply, hR_apply, hy.2 s hs, hz.2 s hs, add_zero]⟩
  | smul c y _ hy =>
    exact ⟨Submodule.smul_mem _ _ hy.1, fun s hs => by
      rw [← hR_apply, LinearMap.map_smul_of_tower, hR_apply, hy.2 s hs, smul_zero]⟩

theorem hform_span (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) {y s : Fin I.n → I.E}
    (hy : y ∈ Submodule.span I.E (perpIn I x S : Set (Fin I.n → I.E))) (hs : s ∈ S) :
    Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  have : Submodule.span I.E (perpIn I x S : Set (Fin I.n → I.E)) ≤ LinearMap.ker (hR I.J s) :=
    Submodule.span_le.2 fun z hz => ((mem_perpIn I x S z).1 hz).2 s hs
  exact this hy

theorem flag_isotropic : ∀ (I : AutInst) (x : I.GA), (∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2), Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) ∧ (∀ v, rkK (stepLt I x (1 / 2)) ≤ rkR (I.ε v)) ∧ ∀ R : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → ∀ y ∈ Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)), (∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ y' ∈ perpIn I x R, y - y' ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := by
  intro I x
  obtain ⟨-, -, hd1, hd2⟩ := GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
  have hiso : ∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2),
      Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 := by
    intro y hy z hz
    obtain ⟨-, -, h1, h2, -⟩ := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2) (by norm_num)
    obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2)⁻¹ (by norm_num)
    have h4 := h3 (h2 (1 / 2)⁻¹ (by norm_num) (h1 hz))
    rw [← (hd1 (1 / 2) (by norm_num)).2] at h4
    exact ((mem_perpIn I x _ z).1 h4).2 y hy
  refine ⟨hiso, rkK_le_rkR I _ hiso, fun R hR hRR y hy hint => ?_⟩
  obtain ⟨-, -, hpp, -⟩ := hd2 R R hR hR le_rfl
  obtain ⟨g, hg, hgf⟩ := exists_extension (lamX I x) (perpIn I x R) hfg hspan
    (fun c hc v hv h => by
      refine (mem_perpIn I x R v).2 ⟨hv, fun s hs => ?_⟩
      have h1 := ((mem_perpIn I x R _).1 h).2 s hs
      rw [← hR_apply, LinearMap.map_smul_of_tower] at h1
      exact (smul_eq_zero.1 h1).resolve_left hc)
    (FlagIso.hR I.J y) (fun z hz => by
      rw [hR_apply, ← hform_star _ I.J_herm]
      exact star_mem_range (hint z hz))
  obtain ⟨y', rfl⟩ := exists_hR_eq I.J I.J_det g
  have hy' : y' ∈ lamX I x := (hdual y').2 fun z hz => by
    rw [← hform_star _ I.J_herm]
    exact star_mem_range (hg z hz)
  have heq : ∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y' =
      Formalism.UG.hform (starRingEnd I.E) I.J z y := fun z hz => by
    rw [← hform_star _ I.J_herm, ← hform_star _ I.J_herm y]
    exact congrArg star (hgf z ((mem_perpIn I x R z).1 hz).1 hz)
  refine ⟨y', (mem_perpIn I x R y').2 ⟨hy', fun s hs => ?_⟩, ?_⟩
  · rw [heq s (hRR hs)]
    exact hform_span I x R hy hs
  · have h1 : y - y' ∈ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 I.E)) I.E _ _ h1
    rw [Submodule.span_eq] at hc
    have hc' : (c : 𝓞 I.E) • (y - y') ∈ lamX I x := hc
    have h2 : (c : 𝓞 I.E) • (y - y') ∈ R := by
      rw [← hpp]
      refine (mem_perpIn I x _ _).2 ⟨hc', fun s hs => ?_⟩
      rw [← hR_apply, LinearMap.map_smul_of_tower, map_sub, hR_apply, hR_apply, heq s hs, sub_self, smul_zero]
    have hc0 : algebraMap (𝓞 I.E) I.E c ≠ 0 := by
      simpa using nonZeroDivisors.coe_ne_zero c
    have h3 := Submodule.smul_mem (Submodule.span I.E (R : Set (Fin I.n → I.E)))
      (algebraMap (𝓞 I.E) I.E c)⁻¹ (Submodule.subset_span h2)
    rwa [← algebraMap_smul I.E (c : 𝓞 I.E), smul_smul, inv_mul_cancel₀ hc0, one_smul] at h3

end GlobalTheory.FlagIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLatticeQuotPrimeStatement
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lattice_quot_prime : ∀ (I : AutInst) (p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)), p.Prime → Ideal.absNorm w.asIdeal = p → Nat.card (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf))) = p ^ I.n := by
  first | exact @GlobalTheory.AdelicLattice.card_quot_extId | exact GlobalTheory.AdelicLattice.card_quot_extId | (intros; apply GlobalTheory.AdelicLattice.card_quot_extId <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellPointBlockEndsLeadingMinorsStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cellPoint_blockEnds_leadingMinors : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → RelPt D z z' γ p → (∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p)) ∧ (ptBlockEnds p).Nodup ∧ (∀ l ∈ ptBlockEnds p, 1 ≤ l ∧ l ≤ D.R.rS + 1) ∧ D.R.rS + 1 ∈ ptBlockEnds p ∧ DminN z z' γ 0 = 1 ∧ 0 < Gf D.R.k D.R.rS z z' γ ∧ Gf D.R.k D.R.rS z z' γ ≤ ‖DminN z z' γ (D.R.rS + 1)‖ ^ 2 ∧ ∀ b C C₂ : ℝ, 1 ≤ b → 0 ≤ C → C ≤ C₂ → 1 ≤ lossV b C D.R.m z z' γ p ∧ lossV b C D.R.m z z' γ p ≤ lossV b C₂ D.R.m z z' γ p ∧ 1 ≤ lossP b C D.R.m z z' γ p ∧ lossP b C D.R.m z z' γ p ≤ lossP b C₂ D.R.m z z' γ p := by
  first | exact @GlobalTheory.Amp.PtMinor.blockEnds_minors | exact GlobalTheory.Amp.PtMinor.blockEnds_minors | (intros; apply GlobalTheory.Amp.PtMinor.blockEnds_minors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructureStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmField_splitCompletely_place_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (p : ℕ), p.Prime → SplitsIn E p → ({v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)), (p : 𝓞 F) ∈ v.asIdeal → Nat.card (kv F v) = p ∧ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {(p : v.adicCompletionIntegers F)} ∧ ∃ sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F, (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) ∧ ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a) := by
  first | exact @GlobalTheory.St.G.SplitPrime.split_place | exact GlobalTheory.St.G.SplitPrime.split_place | (intros; apply GlobalTheory.St.G.SplitPrime.split_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagFlagAdaptedLatticeBasisStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnBlocksSpanFlag_flagAdaptedLatticeBasis : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ v, SpansFlag (fun i => (I.P v)⁻¹ * (T i).map (I.φ v)) (flagAt I S v) := by
  first | exact @GlobalTheory.LeviIso.spansFlag_flagAt | exact GlobalTheory.LeviIso.spansFlag_flagAt | (intros; apply GlobalTheory.LeviIso.spansFlag_flagAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagOfBlockTriangularStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnBlocksSpanFlag_of_block_triangular : ∀ (n a : ℕ) (j : Fin a → ℕ) (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ k i, i < k → p k i = 0 ∧ q k i = 0) → (∀ i, A i = ∑ k, B k * p k i) → (∀ i, B i = ∑ k, A k * q k i) → SpansFlag A W → SpansFlag B W := by
  first | exact @GlobalTheory.LeviIso.spansFlag_of_triangular | exact GlobalTheory.LeviIso.spansFlag_of_triangular | (intros; apply GlobalTheory.LeviIso.spansFlag_of_triangular <;> assumption)
end

