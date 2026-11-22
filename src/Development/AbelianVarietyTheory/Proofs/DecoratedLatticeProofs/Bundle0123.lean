import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IwaFlag

variable {D : D7}

theorem cA_mem_idAt' {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  obtain ⟨ε, -, hc, -, hε, -⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1
  rw [hε] at h ⊢
  have := congrArg (cA D) h
  rwa [map_mul, hc] at this

theorem mul_left_mem {R : Type} [CommRing R] {I : Ideal R} {l m k : ℕ} (A : Matrix (Fin l) (Fin m) R)
    {M : Matrix (Fin m) (Fin k) R} (h : ∀ i j, M i j ∈ I) (i : Fin l) (j : Fin k) : (A * M) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (h x j)

theorem mul_right_mem {R : Type} [CommRing R] {I : Ideal R} {l m k : ℕ} {M : Matrix (Fin l) (Fin m) R}
    (B : Matrix (Fin m) (Fin k) R) (h : ∀ i j, M i j ∈ I) (i : Fin l) (j : Fin k) : (M * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (h i x)

end GlobalTheory.IwaFlag

namespace GlobalTheory.IwaFlag

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem flag_stab : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S g ⬝ d.jX = d.jX ⬝ a) → ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), g = n * d.levi t * d.emb0 γ := by
  intro D S S₀ ρ d v g hg ⟨a, hup, hgX⟩
  have hG' : ∀ i j, (mt S g - 1) i j ∈ idAt D (· = v) := fun i j => by
    rw [Matrix.sub_apply]; exact (mem_congGrp_iff S (idAt D (· = v)) g).1 hg i j

  have hba : (adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ d.jX)) * a = 1 := by
    have h1 : adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ (mt S g ⬝ d.jX)) = 1 := by
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)), mt_unitary]
      exact d.gram_YX
    rw [hgX] at h1
    simpa only [Matrix.mul_assoc] using h1
  have hab : a * (adj (mt S g ⬝ d.jY) ⬝ (gA S ⬝ d.jX)) = 1 := mul_eq_one_comm.1 hba
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin ρ) (AE D), A.1 = a := ⟨⟨a, _, hab, hba⟩, rfl⟩

  have hdet : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hba
  rw [Matrix.det_of_upperTriangular (M := a) (fun ⦃i j⦄ h => hup i j h)] at hdet
  have hu : ∀ i, IsUnit (a i i) := fun i =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun k => a k k) (Finset.mem_univ i)) hdet
  obtain ⟨t, ht1, htinv⟩ : ∃ t : GL (Fin ρ) (AE D), t.1 = diagonal (fun i => a i i) ∧
      (t⁻¹).1 = diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) :=
    ⟨⟨diagonal (fun i => a i i), diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)),
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.mul_val_inv, diagonal_one],
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.val_inv_mul, diagonal_one]⟩, rfl, rfl⟩
  have ht_diag : ∀ i j, i ≠ j → t.1 i j = 0 := fun i j h => by rw [ht1]; exact diagonal_apply_ne _ h

  have hAt : (A * t⁻¹).1 =
      a * diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) := by
    rw [Units.val_mul A t⁻¹, htinv, hA]
  have hUX : A * t⁻¹ ∈ UX D ρ := fun i j =>
    ⟨fun h => by rw [hAt, mul_diagonal, hup i j h, zero_mul],
      by rw [hAt, mul_diagonal]; exact IsUnit.mul_val_inv (hu i)⟩
  have hR' : mt S (g * (d.levi t)⁻¹) ⬝ d.jX = d.jX ⬝ (A * t⁻¹).1 := by
    rw [Units.val_mul A t⁻¹, hA, ← map_inv d.levi t, mt_mul, Matrix.mul_assoc, d.levi_jX]
    simpa only [Matrix.mul_assoc] using congrArg (fun M : Mx D S.rank ρ => M ⬝ (t⁻¹).1) hgX
  have hR : g * (d.levi t)⁻¹ ∈ GlobalTheory.Unf.Rgrp S (rat d.e) := ⟨A * t⁻¹, hUX, hR'⟩
  rw [GlobalTheory.Unf.Rgrp_eq d] at hR
  obtain ⟨n, hn, γ, hnγ⟩ := ((flag_jacobi_structure D S S₀ ρ d).2.2.2.1 _).1 hR

  have hcomm : d.levi t * d.emb0 γ = d.emb0 γ * d.levi t := by
    refine d.ga_ext ?_ ?_ ?_
    · rw [GlobalTheory.MixModel.mt_mul S (d.levi t) (d.emb0 γ), GlobalTheory.MixModel.mt_mul S (d.emb0 γ) (d.levi t), Matrix.mul_assoc, Matrix.mul_assoc,
        d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
    · rw [GlobalTheory.MixModel.mt_mul S (d.levi t) (d.emb0 γ), GlobalTheory.MixModel.mt_mul S (d.emb0 γ) (d.levi t), Matrix.mul_assoc, Matrix.mul_assoc,
        d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
    · rw [GlobalTheory.MixModel.mt_mul S (d.levi t) (d.emb0 γ), GlobalTheory.MixModel.mt_mul S (d.emb0 γ) (d.levi t), Matrix.mul_assoc, Matrix.mul_assoc,
        d.wittDecomp_anisotropicEmbedding_inclY, d.levi_jY, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY]
  have hgfac : g = n * d.levi t * d.emb0 γ := by
    rw [mul_assoc, hcomm, ← mul_assoc, ← hnγ, inv_mul_cancel_right]

  have hmtγ : mt S₀ γ = d.p0 ⬝ (mt S g ⬝ d.j0) := by
    have e1 : mt S (g * (d.levi t)⁻¹) ⬝ d.j0 = mt S g ⬝ d.j0 := by
      rw [← map_inv d.levi t, mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]
    have e2 : d.p0 ⬝ (mt S (n * d.emb0 γ) ⬝ d.j0) = mt S₀ γ := by
      rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc,
        GlobalTheory.Unf.flagUnipotent_anisotropic_projection_eq_one d hn, Matrix.one_mul]
    rw [← e2, ← hnγ, e1]
  have hγ : γ ∈ grpAt S₀ (· = v) := (mem_congGrp_iff S₀ _ γ).2 fun i j => by
    have e : mt S₀ γ - 1 = d.p0 ⬝ ((mt S g - 1) ⬝ d.j0) := by
      rw [hmtγ, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.p0_j0]
    rw [← Matrix.sub_apply, e]
    exact mul_left_mem _ (mul_right_mem _ hG') i j

  have haI : ∀ i j, (a - 1) i j ∈ idAt D (· = v) := by
    have e : a - 1 = d.pX ⬝ ((mt S g - 1) ⬝ d.jX) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.pX_jX, hgX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    intro i j
    rw [e]
    exact mul_left_mem _ (mul_right_mem _ hG') i j
  have ht1I : ∀ i j, (t.1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [ht1, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply] at this
      rwa [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have htiI : ∀ i j, ((t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [htinv, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
      rw [diagonal_apply_eq, Matrix.one_apply_eq]
      have e : (((hu i).unit⁻¹ : (AE D)ˣ) : AE D) - 1 = -((((hu i).unit⁻¹ : (AE D)ˣ) : AE D) * (a i i - 1)) := by
        rw [mul_sub, IsUnit.val_inv_mul (hu i)]; ring
      rw [e]
      exact (idAt D (· = v)).neg_mem (Ideal.mul_mem_left _ _ this)
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have hadjI : ∀ i j, (adj (t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [← adj_one, ← adj_sub]
    exact cA_mem_idAt' (htiI j i)
  have hlevI : d.levi t ∈ grpAt S (· = v) := by
    have e : mt S (d.levi t) - 1 = d.jX ⬝ (t.1 - 1) ⬝ d.pX + d.jY ⬝ (adj (t⁻¹).1 - 1) ⬝ d.pY := by
      rw [d.mt_levi, ← d.sum_eq_one]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      abel
    refine (mem_congGrp_iff S _ _).2 fun i j => ?_
    rw [← Matrix.sub_apply, e, Matrix.add_apply]
    exact add_mem (mul_right_mem _ (mul_left_mem _ ht1I) i j) (mul_right_mem _ (mul_left_mem _ hadjI) i j)
  have hnI : n ∈ grpAt S (· = v) := by
    have e : n = g * (d.levi t * d.emb0 γ)⁻¹ := eq_mul_inv_of_mul_eq ((mul_assoc _ _ _).symm.trans hgfac.symm)
    rw [e]
    exact mul_mem hg (inv_mem (mul_mem hlevI (wittCoreEmbedding_preserves_supportedUnitarySubgroup d hγ)))
  exact ⟨n, hn, hnI, t, ht_diag, hlevI, γ, hγ, hgfac⟩

end GlobalTheory.IwaFlag

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentRadicalSurjectsUnitriangularCharact
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem fourierBesselBasePoint_castSucc_column (i : Fin B.V.rank) (j : Fin σ) : x0 B i (Fin.castSucc j) = B.d.jX i j := by
  simp [x0, xLast, Fin.snoc_castSucc]

theorem fourierBesselBasePoint_last_column (i : Fin B.V.rank) : x0 B i (Fin.last σ) = (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) i := by
  simp [x0, xLast, Fin.snoc_last]

theorem mul_fourierBesselBasePoint_castSucc_column {m : ℕ} (M : Mx D m B.V.rank) (i : Fin m) (j : Fin σ) :
    (M ⬝ x0 B) i (Fin.castSucc j) = (M ⬝ B.d.jX) i j := by
  simp only [Matrix.mul_apply, fourierBesselBasePoint_castSucc_column]

theorem mul_fourierBesselBasePoint_last_column {m : ℕ} (M : Mx D m B.V.rank) (i : Fin m) :
    (M ⬝ x0 B) i (Fin.last σ) = (M *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, fourierBesselBasePoint_last_column]

theorem fourierBesselBasePoint_mul_eq (U : Mx D (σ + 1) (σ + 1)) (i : Fin B.V.rank) (j : Fin (σ + 1)) :
    (x0 B ⬝ U) i j = ∑ k : Fin σ, B.d.jX i k * U (Fin.castSucc k) j +
      (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) i * U (Fin.last σ) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [fourierBesselBasePoint_castSucc_column, fourierBesselBasePoint_last_column]

theorem besselAnisotropicEmbedding_fixes_basePoint (h : GA D B.A) : mt B.V (embA B.d B.o h) ⬝ x0 B = x0 B := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [mul_fourierBesselBasePoint_last_column, fourierBesselBasePoint_last_column, embA_apply, Matrix.mulVec_mulVec, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, vecB, ratV_mulVec,
      Matrix.mulVec_mulVec (ratV B.ζ), show rat B.o.iB = B.o.jB from rfl, B.o.emb_jB, mt_one, Matrix.mul_one]
  · rw [mul_fourierBesselBasePoint_castSucc_column, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, fourierBesselBasePoint_castSucc_column]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem upSum_succ (U : Mx D (σ + 1) (σ + 1)) :
    upSum U = upSum (fun i j : Fin σ => U (Fin.castSucc i) (Fin.castSucc j)) +
      ell D σ ⬝ᵥ (fun i => U (Fin.castSucc i) (Fin.last σ)) := by
  have h1 : ∀ j : Fin σ, ¬ (j.1 = σ + 1) := fun j => by omega
  have h2 : ¬ (σ = σ + 1) := by omega
  simp only [upSum, ell, dotProduct, Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last, h1, h2, if_false,
    Finset.sum_const_zero, add_zero, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : σ = i.1 + 1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem besselFlagProjection_mul_fourierBesselBasePoint_apply (i : Fin σ) (k : Fin (σ + 1)) : (B.d.pX ⬝ x0 B) i k = if k = Fin.castSucc i then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [mul_fourierBesselBasePoint_last_column, Matrix.mulVec_mulVec, B.d.pX_j0, Matrix.zero_mulVec, if_neg (Fin.castSucc_lt_last i).ne']
    rfl
  · rw [mul_fourierBesselBasePoint_castSucc_column, B.d.pX_jX, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e).symm)]

theorem besselFlagProjection_mul_basePoint_mul_apply (U : Mx D (σ + 1) (σ + 1)) (i : Fin σ) (k : Fin (σ + 1)) :
    (B.d.pX ⬝ (x0 B ⬝ U)) i k = U (Fin.castSucc i) k := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply]
  simp only [besselFlagProjection_mul_fourierBesselBasePoint_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem simpleSum_eq_upSum {n : GA D B.V} {U : Mx D (σ + 1) (σ + 1)} (e : mt B.V n ⬝ x0 B = x0 B ⬝ U) :
    simpleSum B.d (vecB B.o B.ζ) n = upSum U := by
  have hb : blockX B.d n = fun i j : Fin σ => U (Fin.castSucc i) (Fin.castSucc j) := by
    ext i j
    have h := mul_fourierBesselBasePoint_castSucc_column B (B.d.pX ⬝ mt B.V n) i j
    rw [Matrix.mul_assoc, Matrix.mul_assoc] at h
    rw [blockX, ← besselFlagProjection_mul_basePoint_mul_apply B U i, ← e, h]
  have hc : coefX B.d (vecB B.o B.ζ) n = fun i => U (Fin.castSucc i) (Fin.last σ) := by
    ext i
    have h := mul_fourierBesselBasePoint_last_column B (B.d.pX ⬝ mt B.V n) i
    rw [Matrix.mul_assoc] at h
    rw [coefX, ← besselFlagProjection_mul_basePoint_mul_apply B U i, ← e, h, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [simpleSum, hb, hc, upSum_succ]

theorem psiBes_eq_psiUni (ψ : AddChar (AF D.host.F) ℂ) {n : GA D B.V} (h : GA D B.A) (u : UX D (σ + 1))
    (e : mt B.V (n * embA B.d B.o h) ⬝ x0 B = x0 B ⬝ u.1.1) :
    psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u.1 := by
  rw [mt_mul, Matrix.mul_assoc, besselAnisotropicEmbedding_fixes_basePoint] at e
  rw [psiBes, simpleSum_eq_upSum B e, map_one, one_mul, psiUni]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem vecB_ne : vecB B.o B.ζ ≠ 0 := by
  have hζ : B.ζ ≠ 0 := fun h => B.line.2 (by rw [h]; simp)
  intro h
  apply hζ
  have := congrArg (B.o.qB *ᵥ ·) h
  simpa [vecB, Matrix.mulVec_mulVec, B.o.qB_iB] using this

theorem exists_form : ∃ r₀ : Fin B.V₀.rank → D.host.E, ratV r₀ ⬝ᵥ ratV (vecB B.o B.ζ) = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, vecB B.o B.ζ k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact vecB_ne B (funext hc)
  refine ⟨Pi.single k (vecB B.o B.ζ k)⁻¹, ?_⟩
  rw [dotProduct, Finset.sum_eq_single k]
  · simp only [ratV, Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ hk, map_one]
  · intro l _ hl
    simp only [ratV, Pi.single_eq_of_ne hl, map_zero, zero_mul]
  · exact fun h => absurd (Finset.mem_univ k) h

theorem vecMulVec_mulVec' {m k : ℕ} (w : Fin m → AE D) (r v : Fin k → AE D) (hr : r ⬝ᵥ v = 1) :
    vecMulVec w r *ᵥ v = w := by
  ext i
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum] at hr ⊢
  rw [hr, mul_one]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

def blk (U : Mx D (σ + 1) (σ + 1)) : Mx D σ σ := fun i j => U (Fin.castSucc i) (Fin.castSucc j)

theorem det_blk {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    (blk U).det = 1 := by
  have hT : (blk U).BlockTriangular id := fun i j h => (hU _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h)
  rw [Matrix.det_of_upperTriangular hT]
  exact Finset.prod_eq_one fun i _ => (hU (Fin.castSucc i) (Fin.castSucc i)).2

def blkU {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    GL (Fin σ) (AE D) :=
  Matrix.nonsingInvUnit (blk U) (by rw [det_blk hU]; exact isUnit_one)

theorem blkU_val {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    (blkU hU).1 = blk U := rfl

theorem blkU_mem {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    blkU hU ∈ upperUni σ (AE D) := fun i j =>
  ⟨fun h => (hU (Fin.castSucc i) (Fin.castSucc j)).1 (Fin.castSucc_lt_castSucc_iff.2 h),
    (hU (Fin.castSucc i) (Fin.castSucc i)).2⟩

def blkQ (γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E) : Matrix (Fin σ) (Fin σ) D.host.E :=
  fun i j => γ (Fin.castSucc i) (Fin.castSucc j)

theorem blk_rat (γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E) : blk (rat γ : Mx D (σ + 1) (σ + 1)) = rat (blkQ γ) := rfl

theorem blkU_rat {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1)
    {γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E} (hγ : rat γ = U) :
    (blkU hU).1 ∈ ratMx D σ σ ∧ ((blkU hU)⁻¹).1 ∈ ratMx D σ σ := by
  have ha1 : (blkU hU).1 = rat (blkQ γ) := by rw [blkU_val, ← hγ, blk_rat]
  have hdet : (blkQ γ).det = 1 := by
    apply incA_injective
    rw [map_one, RingHom.map_det]
    have e : (incA D).mapMatrix (blkQ γ) = blk U := by rw [← hγ, blk_rat]; rfl
    rw [e, det_blk hU]
  have e : rat (blkQ γ)⁻¹ ⬝ (blkU hU).1 = 1 := by
    rw [ha1, ← rat_mul, Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one), rat_one]
  refine ⟨by rw [ha1]; exact rat_mem _, ?_⟩
  have hinv : ((blkU hU)⁻¹).1 = rat (blkQ γ)⁻¹ := by
    calc ((blkU hU)⁻¹).1 = (rat (blkQ γ)⁻¹ ⬝ (blkU hU).1) ⬝ ((blkU hU)⁻¹).1 := by rw [e, Matrix.one_mul]
      _ = rat (blkQ γ)⁻¹ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hinv]; exact rat_mem _

theorem rat_vecMulVec {m k : ℕ} (w : Fin m → D.host.E) (r : Fin k → D.host.E) :
    (rat (vecMulVec w r) : Mx D m k) = vecMulVec (ratV w) (ratV r) := by
  ext i j
  simp only [rat, Matrix.map_apply, vecMulVec_apply, ratV, map_mul]

theorem besselFlagElement_mul_basePoint_eq_basePoint_mul {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1)
    (a : GL (Fin σ) (AE D)) (ha : a.1 = blk U) (b : Mx D σ B.V₀.rank)
    (hbz : a.1 *ᵥ (b *ᵥ ratV (vecB B.o B.ζ)) = fun i => U (Fin.castSucc i) (Fin.last σ)) :
    mt B.V (B.d.levi a * B.d.nB b) ⬝ x0 B = x0 B ⬝ U := by
  have hX : mt B.V (B.d.levi a * B.d.nB b) ⬝ B.d.jX = B.d.jX ⬝ a.1 := by
    rw [mt_mul, Matrix.mul_assoc, B.d.nB_jX, B.d.levi_jX]
  have h0 : mt B.V (B.d.levi a * B.d.nB b) ⬝ B.d.j0 = B.d.j0 + B.d.jX ⬝ (a.1 ⬝ b) := by
    rw [mt_mul, Matrix.mul_assoc, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, B.d.levi_jX,
      Matrix.mul_assoc]
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [mul_fourierBesselBasePoint_last_column, fourierBesselBasePoint_mul_eq, Matrix.mulVec_mulVec, h0, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hbz, Pi.add_apply, (hU (Fin.last σ) (Fin.last σ)).2, mul_one]
    exact add_comm _ _
  · rw [mul_fourierBesselBasePoint_castSucc_column, fourierBesselBasePoint_mul_eq, hX, (hU (Fin.last σ) (Fin.castSucc j)).1 (Fin.castSucc_lt_last j), mul_zero, add_zero,
      Matrix.mul_apply, ha]
    rfl

theorem exists_flag (u : UX D (σ + 1)) :
    ∃ n ∈ flagN B.d, mt B.V n ⬝ x0 B = x0 B ⬝ u.1.1 ∧ (u ∈ UXQ D (σ + 1) → n ∈ GQ B.V) := by
  have hU : ∀ i j : Fin (σ + 1), (j < i → u.1.1 i j = 0) ∧ u.1.1 i i = 1 := u.2
  obtain ⟨r₀, hr⟩ := exists_form B
  obtain ⟨c, hc⟩ : ∃ c : Fin σ → AE D, c = fun i => u.1.1 (Fin.castSucc i) (Fin.last σ) := ⟨_, rfl⟩
  have hbz : (blkU hU).1 *ᵥ (vecMulVec (((blkU hU)⁻¹).1 *ᵥ c) (ratV r₀) *ᵥ ratV (vecB B.o B.ζ)) = c := by
    rw [vecMulVec_mulVec' _ _ _ hr, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hc] at hbz
  refine ⟨_, mul_mem (B.d.levi_mem_NFlag (blkU_mem hU)) (B.d.nB_mem_NFlag _),
    besselFlagElement_mul_basePoint_eq_basePoint_mul B hU (blkU hU) (blkU_val hU) _ hbz, fun hq => ?_⟩
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 hq.1
  have hr' := blkU_rat hU hγ
  have hc' : c = ratV (fun i => γ (Fin.castSucc i) (Fin.last σ)) := by
    rw [hc]; ext i; simp only [ratV, ← hγ, rat, Matrix.map_apply]
  obtain ⟨δ, hδ⟩ := mem_ratMx.1 hr'.2
  have hbq : vecMulVec (((blkU hU)⁻¹).1 *ᵥ c) (ratV r₀) ∈ ratMx D σ B.V₀.rank := by
    rw [← hδ, hc', ← ratV_mulVec, ← rat_vecMulVec]
    exact rat_mem _
  rw [hc] at hbq
  exact mul_mem (B.d.levi_mem_GQ hr'.1 hr'.2) (B.d.nB_mem_GQ hbq)

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB

theorem uniRad_surj_psi : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ u : UX D (σ + 1), ∃ n ∈ flagN B.d, mt B.V n ⬝ x0 B = x0 B ⬝ u.1.1 ∧ (u ∈ UXQ D (σ + 1) → n ∈ GQ B.V)) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ), ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (u : UX D (σ + 1)), mt B.V (n * embA B.d B.o h) ⬝ x0 B = x0 B ⬝ u.1.1 → psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u.1 :=
  fun _ _ B => ⟨UniRad.exists_flag B, fun ψ _ _ h u e => UniRad.psiBes_eq_psiUni B ψ h u e⟩

end GlobalTheory.Unf.FB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointRationalWithRationalLeftIn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

def x0Mat (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun k => Fin.snoc (α := fun _ => D.host.E) (B.d.e k) ((B.d.i₀ *ᵥ vecB B.o B.ζ) k)

theorem rat_x0Mat (B : BesLev D σ) : rat (x0Mat B) = x0 B := by
  refine Matrix.ext fun k j => ?_
  refine Fin.lastCases ?_ (fun b => ?_) j
  · simp [x0Mat, x0, xLast, rat, HypDec.j0, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  · simp [x0Mat, x0, xLast, rat, HypDec.jX]

def besselBasePointLevelNorm (B : BesLev D σ) : D.host.E := star (vecB B.o B.ζ) ⬝ᵥ B.V₀.gram *ᵥ vecB B.o B.ζ

theorem besselBasePointLevelNorm_eq_gram_form (B : BesLev D σ) : besselBasePointLevelNorm B = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
  rw [besselBasePointLevelNorm, vecB, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    B.o.isoB]

theorem besselBasePointLevelNorm_ne_zero (B : BesLev D σ) : besselBasePointLevelNorm B ≠ 0 := by
  rw [besselBasePointLevelNorm_eq_gram_form]; exact B.line.2

def besselBasePointLeftInverse (B : BesLev D σ) : Matrix (Fin (σ + 1)) (Fin B.V.rank) D.host.E :=
  Matrix.of (Fin.snoc (α := fun _ => Fin B.V.rank → D.host.E) (fun a => B.d.qX a)
    ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))))

theorem besselLevelDatum_qX_dot_e_eq_one (B : BesLev D σ) : B.d.qX * B.d.e = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact B.d.pX_jX)

theorem wittDecomposition_projectionX_mul_anisotropicInclusion_eq_zero (B : BesLev D σ) : B.d.qX * B.d.i₀ = 0 :=
  rat_injective (by rw [rat_mul, rat_zero]; exact B.d.pX_j0)

theorem wittDecomposition_projectionZero_mul_e_eq_zero (B : BesLev D σ) : B.d.q0 * B.d.e = 0 :=
  rat_injective (by rw [rat_mul, rat_zero]; exact B.d.p0_jX)

theorem wittDecomposition_projectionZero_mul_anisotropicInclusion_eq_one (B : BesLev D σ) : B.d.q0 * B.d.i₀ = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact B.d.p0_j0)

theorem besselBasePointLeftInverse_mul_snocMatrix (B : BesLev D σ) : besselBasePointLeftInverse B * x0Mat B = 1 := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · have h : ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))) ⬝ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = 1 := by
      rw [smul_dotProduct, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc, wittDecomposition_projectionZero_mul_anisotropicInclusion_eq_one, Matrix.mul_one,
        ← Matrix.dotProduct_mulVec, smul_eq_mul]
      exact inv_mul_cancel₀ (besselBasePointLevelNorm_ne_zero B)
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last]
    exact h
  · have h : ((besselBasePointLevelNorm B)⁻¹ • (star (vecB B.o B.ζ) ᵥ* (B.V₀.gram * B.d.q0))) ᵥ* B.d.e = 0 := by
      rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc, wittDecomposition_projectionZero_mul_e_eq_zero, Matrix.mul_zero, Matrix.vecMul_zero, smul_zero]
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last b).symm]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc]
    exact congrFun h b
  · have h : B.d.qX *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = 0 := by
      rw [Matrix.mulVec_mulVec, wittDecomposition_projectionX_mul_anisotropicInclusion_eq_zero, Matrix.zero_mulVec]
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last a)]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc]
    exact congrFun h a
  · rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Fin.castSucc_inj]
    rw [← Matrix.one_apply (α := D.host.E) (i := a) (j := b), ← besselLevelDatum_qX_dot_e_eq_one B, Matrix.mul_apply]
    simp only [besselBasePointLeftInverse, x0Mat, Matrix.of_apply, Fin.snoc_castSucc]

theorem fourierBesselBasePoint_rational_with_rational_leftInverse : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ),
    (∃ P ∈ ratMx D (σ + 1) B.V.rank, P ⬝ x0 B = 1) ∧ x0 B ∈ ratMx D B.V.rank (σ + 1) := fun _ _ B =>
  ⟨⟨rat (besselBasePointLeftInverse B), rat_mem _, by rw [← rat_x0Mat, ← rat_mul, besselBasePointLeftInverse_mul_snocMatrix, rat_one]⟩, rat_x0Mat B ▸ rat_mem _⟩

end GlobalTheory.Unf.FB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_measure_unitriangular_coordinates : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (vU : VolU D ρ) (ν₀ : Measure (radX J.d)) (𝓝₀ : Set (radX J.d)), ν₀.IsHaarMeasure → IsFundamentalDomain ((GQ J.W).subgroupOf (radX J.d)) 𝓝₀ ν₀ → ν₀ 𝓝₀ = 1 → IsClosed ((radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)) : Set (GA D J.W)) ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsHaarMeasure ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsInvInvariant ∧ J.μR.IsInvInvariant ∧ ∀ F : GA D J.W → ENNReal, Measurable F → ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ u, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1) ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) ∂vU.ν := by
  first | exact @GlobalTheory.JacMeas.jac_measure | exact GlobalTheory.JacMeas.jac_measure | (intros; apply GlobalTheory.JacMeas.jac_measure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramMatrixOfColumnsUnitriangularConjEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMatrixOfColumns_unitriangular_conj_eq : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → uᴴ * gramQ W x₀ * u = gramQ W x₀ := by
  first | exact @GlobalTheory.Unf.gramQ_unitri | exact GlobalTheory.Unf.gramQ_unitri | (intros; apply GlobalTheory.Unf.gramQ_unitri <;> assumption)
end

