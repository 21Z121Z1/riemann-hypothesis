import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0223
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjStabilizersSelfDualLatticesUnramified
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SelfDualStabConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_sq_conj_sub (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (x : 𝓞 E) (d : 𝓞 F), d ∉ v.asIdeal ∧ algebraMap F E d = ((x : E) - σ x) ^ 2 := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have := v.isMaximal
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (E ≃ₐ[F] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcard
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => GlobalTheory.LFun.InertChart.conj_ne h fun x => congrArg (fun t : E ≃ₐ[F] E => t x) hs
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, s • x - x ∉ Q := by
    by_contra hn
    push Not at hn
    have hs : s ∈ Q.inertia (E ≃ₐ[F] E) := AddSubgroup.mem_inertia.2 hn
    rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
    exact hs1 hs
  have hfix : ∀ t : E ≃ₐ[F] E, t (((x : E) - σ x) ^ 2) = ((x : E) - σ x) ^ 2 := fun t => by
    have hc : Nat.card (E ≃ₐ[F] E) = 2 := (IsGalois.card_aut_eq_finrank F E).trans h.2.2.1
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hc
    by_cases ht : t = 1
    · rw [ht]; rfl
    · rw [(hu t ht).trans (hu s hs1).symm]
      change σ _ = _
      rw [map_pow, map_sub, hσ]; ring
  obtain ⟨d, hd⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  have e : (((s • x - x) ^ 2 : 𝓞 E) : E) = ((x : E) - σ x) ^ 2 := by
    change (σ x - (x : E)) ^ 2 = _
    ring
  have hi : IsIntegral ℤ d := by
    rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, hd, ← e]
    exact RingOfIntegers.isIntegral_coe _
  refine ⟨x, ⟨d, hi⟩, fun hm => hx (hQ.isPrime.mem_of_pow_mem 2 ?_), hd⟩
  have : (s • x - x) ^ 2 = algebraMap (𝓞 F) (𝓞 E) ⟨d, hi⟩ := RingOfIntegers.ext (e.trans hd.symm)
  rw [this]
  rwa [hQv.over] at hm

def conjInt (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : intLoc F E v →+* intLoc F E v :=
  (sigR (Fv F v) σ).restrict _ _ fun _ => sigR_mem_intLoc σ

theorem exists_isUnit_sub_conj (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E))
    (v : HeightOneSpectrum (𝓞 F)) : ∃ ω : intLoc F E v, IsUnit (ω - conjInt σ v ω) := by
  obtain ⟨x, d, hd, e⟩ := exists_sq_conj_sub h hU v
  have hd0 : (d : F) ≠ 0 := fun h0 => hd (by
    rw [show d = 0 from RingOfIntegers.coe_injective (by simpa using h0)]; exact zero_mem _)
  have ha : algebraMap F (Fv F v) (d : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : v.valuation F (d : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 hd
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (d : F)⁻¹
    exact le_of_eq (h2.trans (by rw [map_inv₀, h1, inv_one]))
  refine ⟨⟨_, tmul_mem_intLoc (one_mem _) x⟩, (isUnit_pow_iff two_ne_zero).1
    (IsUnit.of_mul_eq_one ⟨_, tmul_mem_intLoc ha 1⟩ (Subtype.ext ?_))⟩
  change (inclR (Fv F v) (x : E) - inclR (Fv F v) (σ x)) ^ 2 * (algebraMap F (Fv F v) (d : F)⁻¹ ⊗ₜ[F] (1 : E)) = 1
  rw [← map_sub, ← map_pow, ← e, Algebra.algebraMap_eq_smul_one (d : F)⁻¹, TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one]
  change inclR (Fv F v) _ * inclR (Fv F v) _ = 1
  rw [← map_mul, ← map_mul, mul_inv_cancel₀ hd0, map_one, map_one]

theorem exists_norm (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    {n : ℕ} {B : Matrix (Fin n) (Fin n) (intLoc F E v)} (hB : cT (conjInt σ v) B = B) (hu : IsUnit B) :
    ∃ u : GL (Fin n) (intLoc F E v), cT (conjInt σ v) u.1 * u.1 = B := by
  let O := intLoc F E v
  let _ := (GlobalTheory.Orb.intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) O := GlobalTheory.Orb.finite_intLocMap v
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing (v.adicCompletionIntegers F) O
  let s : O →+* O := conjInt σ v
  have hs : ∀ y : O, s (s y) = y := fun y =>
    Subtype.ext (GlobalTheory.Doubling.sigR_invol (GlobalTheory.LFun.InertChart.conj_conj h) y.1)
  have hk : ∀ c, s (algebraMap (v.adicCompletionIntegers F) O c) = algebraMap (v.adicCompletionIntegers F) O c :=
    fun c => Subtype.ext (by
      change sigR (Fv F v) σ ((c : Fv F v) ⊗ₜ[F] (1 : E)) = (c : Fv F v) ⊗ₜ[F] (1 : E)
      simp [sigR])
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).map (algebraMap (v.adicCompletionIntegers F) O)
  have hI : I ≤ I.comap s := Ideal.map_le_iff_le_comap.2 fun c hc => by
    rw [Ideal.mem_comap, Ideal.mem_comap, hk]
    exact Ideal.mem_map_of_mem _ hc
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hs
    (GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X O I s hs (fun y hy => hI hy) (exists_isUnit_sub_conj h hU v)) hB hu
  have h2 : IsUnit (Polynomial.aeval B p) := isUnit_of_mul_isUnit_right (hp ▸ hu)
  exact ⟨h2.unit, hp⟩

theorem cT_mul {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} (P Q : Matrix (Fin n) (Fin n) A) :
    cT s (P * Q) = cT s Q * cT s P := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} : cT s (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem exists_orthonormal_frame (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} (hL : IsSelfDualAt σ J L v) :
    ∃ b : GL (Fin n) (Fv F v ⊗[F] E), cT (sigR _ σ) b.1 * JR (Fv F v) J * b.1 = 1 ∧
      ∀ y, (∀ i, y i ∈ intLoc F E v) ↔ b.1 *ᵥ y ∈ latLoc F L v := by
  obtain ⟨a₀, ha₀⟩ := Frames.exists_isLatticeFrame (F := F) L
  have ha := ha₀ v
  generalize bc (compFin F E v) a₀ = a at ha
  have hσ := GlobalTheory.Doubling.sigR_invol (R := Fv F v) (GlobalTheory.LFun.InertChart.conj_conj h)
  have hJu : IsUnit (JR (F := F) (Fv F v) J) := (Matrix.isUnit_iff_isUnit_det _).2 (GlobalTheory.Doubling.isUnit_det_JR hJ.2)
  have hJh : cT (sigR _ σ) (JR (F := F) (Fv F v) J) = JR (Fv F v) J := by
    ext i j; exact congrArg (fun x => (1 : Fv F v) ⊗ₜ[F] x) (hJ.1 i j)
  have hau : IsUnit (cT (sigR _ σ) a.1) := IsUnit.of_mul_eq_one (cT (sigR _ σ) (a⁻¹).1) (by
    rw [← cT_mul, Units.inv_mul, cT_one])
  obtain ⟨H, hH⟩ := (hau.mul hJu).mul a.isUnit
  obtain ⟨h1, h2⟩ := GlobalTheory.StdUnn.Unimod.gram_int (sigR _ σ) (intLoc F E v) (fun _ => sigR_mem_intLoc σ)
    (JR (Fv F v) J) a.1 (a⁻¹).1 (H⁻¹).1 (fun y => y ∈ latLoc F L v) a.mul_inv (hH ▸ H.mul_inv) ha
    (fun y => SetLike.ext_iff.1 hL y)
  let ι := (intLoc F E v).subtype
  have hinj : ∀ {M N : Matrix (Fin n) (Fin n) (intLoc F E v)}, M.map ι = N.map ι → M = N :=
    fun e => Matrix.map_injective Subtype.val_injective e
  have hcT : ∀ M : Matrix (Fin n) (Fin n) (intLoc F E v), (cT (conjInt σ v) M).map ι = cT (sigR _ σ) (M.map ι) :=
    fun _ => rfl
  let B : Matrix (Fin n) (Fin n) (intLoc F E v) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let B' : Matrix (Fin n) (Fin n) (intLoc F E v) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have eB : B.map ι = cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1 := rfl
  obtain ⟨u, hu⟩ := exists_norm h hU v (B := B)
    (hinj (by rw [hcT, eB, cT_mul, cT_mul, hJh, GlobalTheory.UnitaryDoubleCoset.cT_cT hσ, Matrix.mul_assoc]))
    (IsUnit.of_mul_eq_one B' (hinj (by
      rw [Matrix.map_mul, eB, ← hH, Matrix.map_one _ (map_zero ι) (map_one ι)]; exact H.mul_inv)))
  have hu' : cT (sigR _ σ) (bc ι u).1 * (bc ι u).1 = cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1 := by
    rw [← eB, ← hu, Matrix.map_mul]; rfl
  have hm : ∀ (k : GL (Fin n) (intLoc F E v)) (y : Fin n → Fv F v ⊗[F] E), (∀ i, y i ∈ intLoc F E v) →
      ∀ i, ((bc ι k).1 *ᵥ y) i ∈ intLoc F E v := fun k y hy i => by
    rw [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (k.1 i j).2 (hy j)
  refine ⟨a * (bc ι u)⁻¹, ?_, fun y => ?_⟩
  · have : cT (sigR _ σ) (a * (bc ι u)⁻¹).1 * JR (Fv F v) J * (a * (bc ι u)⁻¹).1 =
        cT (sigR _ σ) ((bc ι u)⁻¹).1 * (cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1) * ((bc ι u)⁻¹).1 := by
      simp only [Units.val_mul, cT_mul, Matrix.mul_assoc]
    rw [this, ← hu', ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul, Units.mul_inv]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha]
    refine ⟨fun hy => by rw [← map_inv]; exact hm _ y hy, fun hy => ?_⟩
    have := hm u _ hy
    rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this

theorem exists_conj_stabLoc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    IsHermND σ J → ∀ (L L' : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → Submodule.IsLattice E L' →
    ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt σ J L v → IsSelfDualAt σ J L' v →
    ∃ g : GLoc σ J v, ∀ k : GLoc σ J v, k ∈ stabLoc σ J L' v ↔ g⁻¹ * k * g ∈ stabLoc σ J L v := by
  intro F E _ _ _ _ _ σ h hU n J hJ L L' _ _ v hL hL'
  obtain ⟨b, hb, fb⟩ := exists_orthonormal_frame h hU hJ L hL
  obtain ⟨c, hc, fc⟩ := exists_orthonormal_frame h hU hJ L' hL'
  have hg : cT (sigR _ σ) (c * b⁻¹).1 * JR (Fv F v) J * (c * b⁻¹).1 = JR (Fv F v) J := by
    have : cT (sigR _ σ) (c * b⁻¹).1 * JR (Fv F v) J * (c * b⁻¹).1 =
        cT (sigR _ σ) (b⁻¹).1 * (cT (sigR _ σ) c.1 * JR (Fv F v) J * c.1) * (b⁻¹).1 := by
      simp only [Units.val_mul, cT_mul, Matrix.mul_assoc]
    rw [this, hc, ← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul,
      Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let g : GLoc σ J v := ⟨c * b⁻¹, hg⟩
  have eg : matHom _ σ J g = c * b⁻¹ := rfl
  have hm : ∀ y, y ∈ latLoc F L v ↔ (matHom _ σ J g).1 *ᵥ y ∈ latLoc F L' v := fun y => by
    rw [eg, Units.val_mul, ← Matrix.mulVec_mulVec, ← fc, fb, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hact : ∀ (p q : GLoc σ J v) y,
      (matHom _ σ J p).1 *ᵥ ((matHom _ σ J q).1 *ᵥ y) = (matHom _ σ J (p * q)).1 *ᵥ y := fun p q y => by
    rw [Matrix.mulVec_mulVec, map_mul, Units.val_mul]
  refine ⟨g, fun k => ?_⟩
  rw [mem_stabLoc, mem_stabLoc]
  refine ⟨fun hk y => ?_, fun hk y => ?_⟩
  · rw [hm, hm, hk, hact, hact, ← mul_assoc, mul_inv_cancel_left]
  · have := hk ((matHom _ σ J g⁻¹).1 *ᵥ y)
    rwa [hm, hm, hact, hact, hact, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec, mul_assoc,
      mul_inv_cancel_right, mul_inv_cancel_left] at this

end GlobalTheory.SelfDualStabConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanIn
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CartanPt

variable {R : Type} [CommRing R] {n : ℕ}

theorem block_matrix_map {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4; rw [← Matrix.fromBlocks_map]; rfl

theorem blkJ_mul : (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  have h : Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) R) 0 0 (-1) = (-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]
  rw [h]
  change -((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = _
  rw [Matrix.submatrix_one_equiv]

theorem blkJ_transpose : (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0)ᵀ = -blk4 0 1 (-1) 0 := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.transpose_neg]
  change _ = (-(Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)).submatrix _ _
  rw [Matrix.fromBlocks_neg, neg_zero, neg_neg]

theorem blkJ_map {S : Type} [CommRing S] (f : R →+* S) :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map f = blk4 0 1 (-1) 0 := by
  rw [block_matrix_map, Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f) (map_one f),
    Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]

def mixJ (n : ℕ) (a j : R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  a • (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) + j • blk4 0 1 (-1) 0

theorem mixJ_mul (a j a' j' : R) :
    mixJ n a j * mixJ n a' j' = mixJ n (a * a' - j * j') (a * j' + j * a') := by
  simp only [mixJ, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, blkJ_mul]
  module

theorem mixJ_one : mixJ n (1 : R) 0 = 1 := by simp [mixJ]

theorem mixJ_J : mixJ n (0 : R) 1 = blk4 0 1 (-1) 0 := by simp [mixJ]

theorem mixJ_map {S : Type} [CommRing S] (f : R →+* S) (a j : R) :
    (mixJ n a j).map f = mixJ n (f a) (f j) := by
  unfold mixJ
  rw [← blkJ_map f, ← Matrix.map_one f (map_zero f) (map_one f)]
  ext p q
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]

theorem mixJ_transpose (a j : R) : (mixJ n a j)ᵀ = mixJ n a (-j) := by
  simp [mixJ, Matrix.transpose_add, Matrix.transpose_smul, blkJ_transpose]

theorem cT_mixJ (σ : R →+* R) (a j : R) : Formalism.UG.cT σ (mixJ n a j) = mixJ n (σ a) (-σ j) := by
  rw [Formalism.UG.cT, mixJ_map, mixJ_transpose]

theorem phase (A B t : ℂ) (hB : B ≠ 0) (h1 : A * B * conj B = t) (h2 : A * conj A = 4) :
    A * (1 / 2) = t / (‖t‖ : ℂ) := by
  have hA : ‖A‖ = 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖A‖ ^ 2 = 2 ^ 2 := by
      have : ‖A‖ ^ 2 = 4 := by exact_mod_cast h2
      linarith
    exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 h3
  have hn : (‖B‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hB
  have ht : ‖t‖ = 2 * ‖B‖ ^ 2 := by
    rw [← h1, norm_mul, norm_mul, Complex.norm_conj, hA]; ring
  rw [ht, ← h1, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp

theorem four_iff {S : Type} [CommRing S] (f : R →+* S) (z : R) : f (z - 4) = 0 ↔ f z = 4 := by
  rw [map_sub, map_ofNat, sub_eq_zero]

theorem four_left {S : Type} [CommRing S] (f : R →+* S) {e : R} (z : R) (h : f e = 0) : f (e * (z - 4)) = 0 := by
  rw [map_mul, h, zero_mul]

theorem four_right {S : Type} [CommRing S] (f : R →+* S) (e : R) {z : R} (h : f z = 4) : f (e * (z - 4)) = 0 := by
  rw [map_mul, (four_iff f z).2 h, mul_zero]

theorem alg_phase (c : R →+* R) (hc : ∀ z, c (c z) = z) {e h m : R} {u ε : Rˣ} (he : e * e = e) (hce : c e = e)
    (hε : (ε : R) * u * c u = m) (hm : c m = -m) (hh : 2 * h = 1) (h4 : e * (ε * c ε - 4) = 0) :
    e * (e * ε * h) = e * ε * h ∧ (e * ε * h) * (e * ε * h) = -e ∧ c (e * ε * h) = -(e * ε * h) := by
  have hcε : c ε = -(ε : R) := by
    rw [← hε, map_mul, map_mul, hc] at hm
    have hu : IsUnit ((u : R) * c u) := u.isUnit.mul (u.isUnit.map c)
    refine hu.mul_right_cancel ?_
    linear_combination hm
  have hch : c h = h := by
    have := congrArg c hh
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination h * this - c h * hh
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ((ε : R) * h) * he
  · linear_combination ((ε : R) ^ 2 * h ^ 2) * he + (e * ε * h ^ 2) * hcε - h ^ 2 * h4 - e * (2 * h + 1) * hh
  · rw [map_mul, map_mul, hce, hcε, hch]; ring

theorem cx_phase (c : R →+* R) (φ : R →+* ℂ) (hφ : ∀ z, φ (c z) = conj (φ z)) {e h m : R} {u ε : Rˣ} (he : φ e = 1)
    (hε : (ε : R) * u * c u = m) (hh : 2 * h = 1) (h4 : φ (ε * c ε) = 4) :
    φ (e * ε * h) = φ m / (‖φ m‖ : ℂ) := by
  have e1 : φ h = 1 / 2 := by
    have := congrArg φ hh
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination (1 / 2) * this
  rw [map_mul, map_mul, he, one_mul, e1]
  refine phase _ (φ u) _ (u.isUnit.map φ).ne_zero ?_ ?_
  · rw [← hφ, ← map_mul, ← map_mul, hε]
  · rw [← hφ, ← map_mul, h4]

theorem mixJ_real (φ : R →+* ℂ) {e j : R} (he : φ e = 1) :
    (mixJ n (1 - e) j).map φ = φ j • blk4 0 1 (-1) 0 := by
  rw [mixJ_map, map_sub, map_one, he, sub_self, mixJ, zero_smul, zero_add]

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

omit [NumberField F] [NumberField E] in
theorem sigR_sigR (A : Type) [CommRing A] [Algebra F A] (hσ : ∀ x, σ (σ x) = x) (z : A ⊗[F] E) :
    sigR A σ (sigR A σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[F] σ (σ x) = _
    rw [hσ]

omit [NumberField E] in
theorem sigR_compInf (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    sigR w.Completion σ (compInf F E w z) = compInf F E w (sigR (AF F) σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x => rfl

omit [NumberField F] [NumberField E] in
theorem incl_half [CharZero E] (A : Type) [CommRing A] [Algebra F A] : 2 * inclR (F := F) (E := E) A (1 / 2) = 1 := by
  rw [← map_ofNat (inclR (F := F) (E := E) A) 2, ← map_mul]
  norm_num

theorem exists_point (n : ℕ) {e j : AF F ⊗[F] E} (hee : e * e = e) (hej : e * j = j) (hjj : j * j = -e)
    (hce : sigR (AF F) σ e = e) (hcj : sigR (AF F) σ j = -j) (hef : ∀ v, compFin F E v e = 0) :
    ∃ k ∈ levelAll σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) (stdLattice E (n + n)) 1,
      (AdelicU.matHom _ σ _ k).1 = mixJ n (1 - e) j := by
  have hkk : mixJ n (1 - e) j * mixJ n (1 - e) j = 1 := by
    rw [mixJ_mul, ← mixJ_one]
    congr 1
    · linear_combination hee - hjj
    · linear_combination (-2) * hej
  have hcT : Formalism.UG.cT (sigR (AF F) σ) (mixJ n (1 - e) j) = mixJ n (1 - e) j := by
    rw [cT_mixJ, map_sub, map_one, hce, hcj, neg_neg]
  let kU : GL (Fin (n + n)) (AF F ⊗[F] E) := ⟨mixJ n (1 - e) j, mixJ n (1 - e) j, hkk, hkk⟩
  have hmem : kU ∈ HR (AF F) σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) := by
    change Formalism.UG.cT (sigR (AF F) σ) (mixJ n (1 - e) j) * (blk4 0 1 (-1) 0).map (inclR (AF F)) * mixJ n (1 - e) j =
      (blk4 0 1 (-1) 0).map (inclR (AF F))
    rw [hcT, blkJ_map, ← mixJ_J, mixJ_mul, mixJ_mul]
    congr 1
    · linear_combination 2 * hej
    · linear_combination hee - hjj
  let k : GAd σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) := (⟨kU, hmem⟩ : HR (AF F) σ _)
  refine ⟨k, mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩, rfl⟩
  · have h : (AdelicU.matHom _ σ _ (proj σ _ v k)).1 = 1 := by
      change (mixJ n (1 - e) j).map (compFin F E v) = 1
      rw [mixJ_map, map_sub, map_one, hef, sub_zero, ← hej, map_mul, hef, zero_mul, mixJ_one]
    refine mem_stabLoc.2 fun y => ?_
    rw [h, Matrix.one_mulVec]
  · rw [mem_stabArch, map_one, inv_one, one_mul, mul_one]
    change Formalism.UG.cT (sigR w.Completion σ) ((mixJ n (1 - e) j).map (compInf F E w)) * 1 *
      (mixJ n (1 - e) j).map (compInf F E w) = 1
    rw [Matrix.mul_one]
    nth_rewrite 1 [mixJ_map]
    rw [cT_mixJ, sigR_compInf, sigR_compInf, hcj, map_neg, neg_neg, map_sub (sigR (AF F) σ), map_one, hce,
      ← mixJ_map, ← Matrix.map_mul, hkk, Matrix.map_one _ (map_zero _) (map_one _)]

end Adelic

theorem real_four (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (z : AE D)
    (hz : ∀ w, compInf D.host.F D.host.E w z = 4) (τ : D.what₂.Tau) : ((θ τ).comp (infPart D)) z = 4 :=
  (four_iff ((θ τ).comp (infPart D)) z).1
    (((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (z - 4)).1
      (fun w => (four_iff (compInf D.host.F D.host.E w) z).2 (hz w)) τ)

theorem idem_four (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) {e z : AE D} (he : finPart D e = 0)
    (hz : ∀ τ, ((θ τ).comp (infPart D)) z = 4) : e * (z - 4) = 0 :=
  (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _
    (fun τ => four_right ((θ τ).comp (infPart D)) e (hz τ)) (four_left (finPart D) z he)

theorem cA_skew (D : D7) (μ : D.host.E) (hμ : IsSkew μ) : cA D (incA D μ) = -incA D μ :=
  (show cA D (incA D μ) = incA D (star μ) from rfl).trans ((congrArg (incA D) hμ.2).trans ((incA D).map_neg μ))

theorem cA_cA (D : D7) (z : AE D) : cA D (cA D z) = z := sigR_sigR D.sp.cm.sig _ (fun x => star_star x) z

theorem exists_phase_adele (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (μ : D.host.E) (hμ : IsSkew μ) :
    ∃ e j : AE D, e * e = e ∧ e * j = j ∧ j * j = -e ∧ cA D e = e ∧ cA D j = -j ∧
      (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ τ, ((θ τ).comp (infPart D)) e = 1) ∧
      ∀ τ, ((θ τ).comp (infPart D)) j = tauE D τ μ / (‖tauE D τ μ‖ : ℂ) := by
  obtain ⟨e, hee, hce, hef, -, hfp, hip⟩ := GlobalTheory.StdUnn.realIdem_exists D
  obtain ⟨-, L2, L3, -⟩ := GlobalTheory.StdUnn.RealComp.real_components D θ hθ
  obtain ⟨u, ε, hεu, -, hε4⟩ := GlobalTheory.StdUnn.exists_scal_real D μ hμ 1
  have h4 := real_four D θ hθ _ hε4
  have hh : 2 * incA D (1 / 2) = 1 := incl_half _
  have h := alg_phase (cA D) (cA_cA D) hee hce hεu (cA_skew D μ hμ) hh (idem_four D θ hθ hfp h4)
  have he1 : ∀ τ, ((θ τ).comp (infPart D)) e = 1 := fun τ => (congrArg (θ τ) hip).trans (θ τ).map_one
  refine ⟨e, _, hee, h.1, h.2.1, hce, h.2.2, hef, he1, fun τ => ?_⟩
  have h2 : ((θ τ).comp (infPart D)) (incA D μ) = tauE D τ μ := L3 μ τ
  exact (cx_phase (cA D) ((θ τ).comp (infPart D)) (fun z => L2 z τ) (he1 τ) hεu hh (h4 τ)).trans
    (congrArg (fun t : ℂ => t / (‖t‖ : ℂ)) h2)

theorem exists_mem_K_compAt_eq_stdInv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (n : ℕ) (μ : D.host.E), IsSkew μ →
    ∃ k ∈ K D n, ∀ τ, compAt θ τ (mat k) = stdInv n μ τ := by
  intro D θ hθ n μ hμ
  obtain ⟨e, j, hee, hej, hjj, hce, hcj, hef, he1, hj⟩ := exists_phase_adele D θ hθ μ hμ
  obtain ⟨k, hk, hmat⟩ := exists_point D.sp.cm.sig n hee hej hjj hce hcj hef
  refine ⟨k, hk, fun τ => ?_⟩
  have h0 : mat (D := D) (n := n) k = mixJ n (1 - e) j := hmat
  have h1 : compAt θ τ (mixJ n (1 - e) j) = (mixJ n (1 - e) j).map ((θ τ).comp (infPart D)) := rfl
  rw [h0, h1, mixJ_real _ (he1 τ), hj]
  rfl

end GlobalTheory.CartanPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealPlacesIdempotentExtensionAdelesStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realPlacesIdempotent_extensionAdeles : ∀ D : D7, ∃ e : AE D, e * e = e ∧ cA D e = e ∧ (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ w, compInf D.host.F D.host.E w e = 1) ∧ finPart D e = 0 ∧ infPart D e = 1 := by
  first | exact @GlobalTheory.StdUnn.realIdem_exists | exact GlobalTheory.StdUnn.realIdem_exists | (intros; apply GlobalTheory.StdUnn.realIdem_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTraceZeroLocalNormMulIntegralUnitStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceZero_localNorm_mul_integralUnit : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ IntA (ε : AE D) ∧ IntA ((ε⁻¹ : (AE D)ˣ) : AE D) := by
  first | exact @GlobalTheory.StdUnn.SkewNorm.exists_skew_norm_mul_unit | exact GlobalTheory.StdUnn.SkewNorm.exists_skew_norm_mul_unit | (intros; apply GlobalTheory.StdUnn.SkewNorm.exists_skew_norm_mul_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryIsometryIsotropicFrameLocalRingStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryIsometry_isotropicFrame_localRing : ∀ (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O), (∀ x, s (s x) = x) → (∃ τ : O, τ + s τ = 1) → (∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u) → ∀ (n r : ℕ) (Q : Matrix (Fin n) (Fin n) O), Formalism.UG.cT s Q = Q → IsUnit Q → ∀ C C' : Matrix (Fin n) (Fin r) O, (∃ L : Matrix (Fin r) (Fin n) O, L * C = 1) → (∃ L : Matrix (Fin r) (Fin n) O, L * C' = 1) → Formalism.UG.cT s C * Q * C = 0 → Formalism.UG.cT s C' * Q * C' = 0 → ∃ k : GL (Fin n) O, Formalism.UG.cT s k.1 * Q * k.1 = Q ∧ k.1 * C = C' := by
  first | exact @GlobalTheory.WittFrame.exists_isometry_frame | exact GlobalTheory.WittFrame.exists_isometry_frame | (intros; apply GlobalTheory.WittFrame.exists_isometry_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmTypeStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extensionAdele_realComponents_cmType : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ z : AE D, (∀ w, compInf D.host.F D.host.E w z = 0) ↔ ∀ τ, θ τ (infPart D z) = 0) ∧ (∀ z τ, θ τ (infPart D (cA D z)) = conj (θ τ (infPart D z))) ∧ (∀ x τ, θ τ (infPart D (incA D x)) = tauE D τ x) ∧ (∀ z : AE D, (∀ τ, θ τ (infPart D z) = 0) → finPart D z = 0 → z = 0) := by
  first | exact @GlobalTheory.StdUnn.RealComp.real_components | exact GlobalTheory.StdUnn.RealComp.real_components | (intros; apply GlobalTheory.StdUnn.RealComp.real_components <;> assumption)
end

