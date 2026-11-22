import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0751
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0383
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgHomEqOrConj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0204
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdDetHermitianSquarePowNonne
section
set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

namespace GlobalTheory.PointFormSign.TopPos

open GlobalTheory.GoodMetric.LinSubst

variable {n : ℕ}

def pairForm (u v : Fin n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ p : Fin n × Fin n, C (u p.1 * starRingEnd ℂ (v p.2)) * X p

theorem topCoeff_prod_pairForm_fin (k : ℕ) :
    ∃ D : (Fin k → Fin n → ℂ) → ℂ, ∀ u v : Fin k → Fin n → ℂ,
      topCoeff (∏ j, pairForm (u j) (v j)) = D u * starRingEnd ℂ (D v) := by
  by_cases hk : k = n
  · subst hk
    refine ⟨fun u => (Matrix.of u).det, fun u v => ?_⟩
    simp only [pairForm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
    rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin k) (fun _ => Fin k)).symm.sum_comp,
      Fintype.sum_prod_type]
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    simp_rw [topCoeff_prod_X_pair]
    have key : ∀ (c d : Fin k → Fin k),
        (∏ i, u i (c i) * starRingEnd ℂ (v i (d i))) * ((rowSel c).det * (rowSel d).det) =
        ((∏ i, (Matrix.of u) i (c i)) * (rowSel c).det) *
        ((∏ i, ((Matrix.of v).map (starRingEnd ℂ)) i (d i)) * (rowSel d).det) := by
      intro c d
      simp only [Matrix.of_apply, Matrix.map_apply, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => key c d, ← Finset.sum_mul_sum,
      sum_prod_mul_det_rowSel, sum_prod_mul_det_rowSel, RingHom.map_det]
    rfl
  · refine ⟨fun _ => 0, fun u v => ?_⟩
    simp only [pairForm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
    simp [topCoeff_prod_X_of_ne hk]

theorem topCoeff_prod_pairForm (J : Type) [Fintype J] :
    ∃ D : (J → Fin n → ℂ) → ℂ, ∀ u v : J → Fin n → ℂ,
      topCoeff (∏ j, pairForm (u j) (v j)) = D u * starRingEnd ℂ (D v) := by
  obtain ⟨D, hD⟩ := topCoeff_prod_pairForm_fin (n := n) (Fintype.card J)
  let e := (Fintype.equivFin J).symm
  refine ⟨fun u => D (u ∘ e), fun u v => ?_⟩
  rw [← hD, ← e.prod_comp]
  rfl

theorem factorial_mul_det {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    (m.factorial : R) * M.det = ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (σ i) (τ i) := by
  rw [Finset.sum_comm]
  have h (τ : Equiv.Perm (Fin m)) : ∑ σ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (σ i) (τ i) = M.det := by
    have h1 := Matrix.det_permute' τ M
    rw [Matrix.det_apply'] at h1
    have h2 : ((Equiv.Perm.sign τ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    calc _ = ((Equiv.Perm.sign τ : ℤ) : R) * ∑ σ : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, (M.submatrix id τ) (σ i) i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp only [Matrix.submatrix_apply, id]
          ring
      _ = M.det := by rw [h1, ← mul_assoc, h2, one_mul]
  simp_rw [h]
  simp [Fintype.card_perm]

theorem sqPoly_apply {m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (i j : Fin m) :
    sqPoly T i j = ∑ k, pairForm (fun a => T (coordVec a) i k) (fun a => T (coordVec a) j k) := by
  simp only [sqPoly, pairForm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
    Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm (γ := Fin r)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (γ := Fin r)]
  rfl

theorem factorial_mul_det_sqPoly {m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    C (m.factorial : ℂ) * (sqPoly T).det = ∑ k : Fin m → Fin r, ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
      C (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
        ∏ i, pairForm (fun a => T (coordVec a) (σ i) (k i)) (fun a => T (coordVec a) (τ i) (k i)) := by
  rw [map_natCast, factorial_mul_det]
  simp_rw [sqPoly_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin m → Fin r)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm (γ := Fin m → Fin r)]
  simp only [map_mul, map_intCast]

theorem topCoeff_prod_det_nonneg {B : Type} [Fintype B] (m r : B → ℕ)
    (T : ∀ b, V n →ₗ[ℂ] Matrix (Fin (m b)) (Fin (r b)) ℂ) :
    0 ≤ topCoeff (∏ b, (sqPoly (T b)).det) := by
  classical
  obtain ⟨D, hD⟩ := topCoeff_prod_pairForm (n := n) (Σ b, Fin (m b))
  have h : (∏ b, ((m b).factorial : ℂ)) * topCoeff (∏ b, (sqPoly (T b)).det) =
      ∑ k : ∀ b, Fin (m b) → Fin (r b),
        (∑ σ : ∀ b, Equiv.Perm (Fin (m b)), (∏ b, ((Equiv.Perm.sign (σ b) : ℤ) : ℂ)) *
          D fun j a => T j.1 (coordVec a) (σ j.1 j.2) (k j.1 j.2)) *
        starRingEnd ℂ (∑ σ : ∀ b, Equiv.Perm (Fin (m b)), (∏ b, ((Equiv.Perm.sign (σ b) : ℤ) : ℂ)) *
          D fun j a => T j.1 (coordVec a) (σ j.1 j.2) (k j.1 j.2)) := by
    rw [← topCoeff_C_mul, map_prod, ← Finset.prod_mul_distrib]
    simp_rw [factorial_mul_det_sqPoly]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul, ← Fintype.prod_sigma', hD, Finset.prod_mul_distrib]
    simp only [map_mul, map_prod, map_intCast]
    ring
  have h0 : 0 ≤ (∏ b, ((m b).factorial : ℂ)) * topCoeff (∏ b, (sqPoly (T b)).det) := by
    rw [h]
    exact Finset.sum_nonneg fun k _ => mul_star_self_nonneg _
  have hN : (0 : ℝ) < ∏ b, ((m b).factorial : ℝ) :=
    Finset.prod_pos fun b _ => by exact_mod_cast Nat.factorial_pos _
  have e : (∏ b, ((m b).factorial : ℂ)) = ((∏ b, ((m b).factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [e] at h0
  have h1 : (0 : ℂ) ≤ (((∏ b, ((m b).factorial : ℝ))⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.2 (inv_nonneg.2 hN.le)
  have h2 := mul_nonneg h1 h0
  rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hN.ne', Complex.ofReal_one, one_mul] at h2

end GlobalTheory.PointFormSign.TopPos

theorem GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg {n : ℕ} {κ : Type} [Fintype κ] (m r e : κ → ℕ)
    (T : ∀ t, V n →ₗ[ℂ] Matrix (Fin (m t)) (Fin (r t)) ℂ) :
    0 ≤ topCoeff (∏ t, (sqPoly (T t)).det ^ e t) := by
  have h := TopPos.topCoeff_prod_det_nonneg (B := Σ t, Fin (e t)) (fun b => m b.1) (fun b => r b.1) fun b => T b.1
  rw [Fintype.prod_sigma] at h
  refine h.trans_eq (congrArg topCoeff (Finset.prod_congr rfl fun t _ => ?_))
  exact (Finset.prod_const (s := Finset.univ) (sqPoly (T t)).det).trans (by rw [Finset.card_univ, Fintype.card_fin])
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivOutsideListProd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftStandardGroup

open ReciprocityTheory.Aut

def bz (r n p : ℕ) (γ : GL (Fin r) (ZMod p)) : Matrix (Fin n) (Fin n) ℤ := fun a b =>
  if hab : a.val < r ∧ b.val < r then
    ((((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val : ℕ) : ℤ)
  else if a = b then 1 else 0

theorem bz_map_zmod (r t p : ℕ) [Fact p.Prime] (γ : GL (Fin r) (ZMod p)) :
    (bz r (r + t) p γ).map (Int.cast : ℤ → ZMod p) = GlobalTheory.SerSys.BlockLift.bm r t γ := by
  ext a b
  rw [GlobalTheory.SerSys.BlockLift.bm_apply]
  simp only [Matrix.map_apply, bz]
  split_ifs <;> simp [ZMod.natCast_zmod_val]

theorem bz_det_ne (r t p : ℕ) [Fact p.Prime] (γ : GL (Fin r) (ZMod p)) :
    (((bz r (r + t) p γ).det : ℤ) : ZMod p) ≠ 0 := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.SerSys.BlockLift.bm_isUnit r t γ)
  intro h0
  have e : (((bz r (r + t) p γ).det : ℤ) : ZMod p) = (GlobalTheory.SerSys.BlockLift.bm r t γ).det := by
    rw [← bz_map_zmod]
    exact RingHom.map_det (Int.castRingHom (ZMod p)) _
  rw [e] at h0
  exact hu.ne_zero h0

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem val_intCast_le_one (s : SplitPlace L) (m : ℤ) :
    Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) ≤ 1 := by
  have h := s.split_le_one (m : 𝓞 L)
  simpa using h

theorem val_intCast_eq_one (s : SplitPlace L) {p : ℕ} [Fact p.Prime]
    (hp : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L))) < 1) (m : ℤ) (hm : (m : ZMod p) ≠ 0) :
    Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  set u : ℤ := (((m : ZMod p)⁻¹).val : ℤ) with hu
  have h1 : (((m * u - 1 : ℤ)) : ZMod p) = 0 := by
    rw [hu]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_inv_cancel₀ hm, sub_self]
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h1
  have e : ((m : s.v.adicCompletion (maximalRealSubfield L)) * (u : s.v.adicCompletion (maximalRealSubfield L))) =
      1 + (p : s.v.adicCompletion (maximalRealSubfield L)) * (c : s.v.adicCompletion (maximalRealSubfield L)) := by
    have : (m * u : ℤ) = 1 + (p : ℤ) * c := by linarith
    exact_mod_cast this
  have h2 : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L)) * (c : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hp (val_intCast_le_one s c)
  have h3 : Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L)) * (u : s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
    rw [e]
    exact Valuation.map_one_add_of_lt _ h2
  apply le_antisymm (val_intCast_le_one s m)
  by_contra hlt
  push_neg at hlt
  have h4 := mul_lt_one_of_lt_of_le hlt (val_intCast_le_one s u)
  rw [← map_mul, h3] at h4
  exact lt_irrefl _ h4

end Local

end GlobalTheory.LiftStandardGroup

end

namespace GlobalTheory.LiftStandardGroup

open ReciprocityTheory.Aut

section Local2

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem loc_eq_one_of_ne {n : ℕ} (s' : SplitPlace L) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (h : s'.v ≠ v)
    {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside {v} x) : s'.loc n x = 1 := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  have hc : compAt L s'.v (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b - (1 : Matrix (Fin n) (Fin n) (AL L)) a b) = 0 := by
    have := congrFun (congrFun (hx s'.v (by simpa using h)) a) b
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h0 := GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s' _ hc
  rw [map_sub, sub_eq_zero] at h0
  show s'.proj (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b) =
    (1 : Matrix (Fin n) (Fin n) (s'.v.adicCompletion (maximalRealSubfield L))) a b
  rw [h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem exists_local (s : SplitPlace L) (r t p : ℕ) [Fact p.Prime]
    (hp : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L))) < 1) (γ : GL (Fin r) (ZMod p)) :
    ∃ x : Formalism.AUTREP.GAf L (r + t), TrivOutside {s.v} x ∧ x ∈ Umax L (r + t) ∧
      GlobalTheory.PendOf.IsLiftAt s r p γ (s.loc (r + t) x) := by
  set M : Matrix (Fin (r + t)) (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)) :=
    (bz r (r + t) p γ).map (Int.cast : ℤ → s.v.adicCompletion (maximalRealSubfield L)) with hM
  have hdetM : M.det = (((bz r (r + t) p γ).det : ℤ) : s.v.adicCompletion (maximalRealSubfield L)) :=
    (RingHom.map_det (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) _).symm
  have hv : Valued.v M.det = 1 := by
    rw [hdetM]; exact val_intCast_eq_one s hp _ (bz_det_ne r t p γ)
  have hne : M.det ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  set h : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M hne with hh
  have hval : (h : Matrix (Fin (r + t)) (Fin (r + t)) _) = M := rfl
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc L (r + t) s h
  have hint : ∀ a b, Valued.v (M a b) ≤ 1 := fun a b => by
    rw [hM, Matrix.map_apply]; exact val_intCast_le_one s _
  have hinvint : ∀ a b, Valued.v ((M⁻¹ : Matrix (Fin (r + t)) (Fin (r + t)) _) a b) ≤ 1 := by
    intro a b
    have hadj : M.adjugate = ((bz r (r + t) p γ).adjugate).map (Int.cast : ℤ → s.v.adicCompletion (maximalRealSubfield L)) :=
      (RingHom.map_adjugate (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) _).symm
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, hadj, Matrix.map_apply, smul_eq_mul, map_mul, map_inv₀, hv,
      inv_one, one_mul]
    exact val_intCast_le_one s _
  refine ⟨x, hx1, ?_, ?_⟩
  · refine GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s x hx1 ?_ ?_
    · intro a b; rw [hx2, hval]; exact hint a b
    · intro a b; rw [map_inv, hx2, Matrix.coe_units_inv, hval]; exact hinvint a b
  · intro a b
    rw [hx2, hval, hM]
    by_cases hab : a.val < r ∧ b.val < r
    · rw [dif_pos hab, Matrix.map_apply]
      simp [bz, dif_pos hab]
    · rw [dif_neg hab, Matrix.map_apply]
      simp only [bz, dif_neg hab]
      split_ifs <;> simp

end Local2

end GlobalTheory.LiftStandardGroup

namespace GlobalTheory.LiftStandardGroup

open ReciprocityTheory.Aut

theorem list_prod_map_eq {ι G : Type} [Monoid G] (f : ι → G) (a : ι) :
    ∀ l : List ι, l.Nodup → a ∈ l → (∀ b ∈ l, b ≠ a → f b = 1) → (l.map f).prod = f a
  | [], _, hm, _ => absurd hm List.not_mem_nil
  | b :: l, hnd, hm, h1 => by
    rw [List.map_cons, List.prod_cons]
    by_cases hb : b = a
    · subst hb
      rw [List.prod_eq_one, mul_one]
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
      exact h1 c (List.mem_cons_of_mem _ hc) (fun e => (List.nodup_cons.1 hnd).1 (e ▸ hc))
    · rw [h1 b (by simp) hb, one_mul]
      exact list_prod_map_eq f a l (List.nodup_cons.1 hnd).2 ((List.mem_cons.1 hm).resolve_left (Ne.symm hb))
        (fun c hc => h1 c (List.mem_cons_of_mem _ hc))

theorem trivOutside_list_prod {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} :
    ∀ l : List (Formalism.AUTREP.GAf L n), (∀ x ∈ l, TrivOutside T x) → TrivOutside T l.prod
  | [], _ => by rw [List.prod_nil]; exact GlobalTheory.HeckeStdFacts.triv_one
  | x :: l, h => by
    rw [List.prod_cons]
    exact GlobalTheory.HeckeStdFacts.triv_mul (h x (by simp)) (trivOutside_list_prod l fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem main : ∀ (D : D7) (n : ℕ), D.R.r ≤ n → ∃ Lf : G0g D.nd → Formalism.AUTREP.GAf D.host.E n,
    GlobalTheory.PendOf.IsTypeGroupBlockLift D n Lf ∧ ∀ g, Lf g ∈ ReciprocityTheory.Aut.Umax D.host.E n := by
  intro D n hn
  classical
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  choose s hs using fun kv : (Σ k : Fin 2, D.nd.PlG k) => GlobalTheory.FixedPlaceOverType.exists_splitPlace_w_plGw D kv.1 kv.2
  have hp : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      Valued.v (((D.host.g kv.1 : ℕ) : (s kv).v.adicCompletion (maximalRealSubfield D.host.E))) < 1 := by
    intro kv
    have h0 : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := D.naut.plGw_over kv.1 kv.2
    rw [← hs kv] at h0
    have h1 := ((s kv).split_mem_ideal _).1 h0
    simpa using h1
  have hloc : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (γ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))),
      ∃ x : Formalism.AUTREP.GAf D.host.E (D.R.r + t), TrivOutside {(s kv).v} x ∧ x ∈ Umax D.host.E (D.R.r + t) ∧
        GlobalTheory.PendOf.IsLiftAt (s kv) D.R.r (D.host.g kv.1) γ ((s kv).loc (D.R.r + t) x) := by
    intro kv γ
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    exact exists_local (s kv) D.R.r t (D.host.g kv.1) (hp kv) γ
  choose x hx1 hx2 hx3 using hloc
  have hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv).v) :=
    GlobalTheory.PlaceInj.splitPlace_v_injective D (fun k v => s ⟨k, v⟩) (fun k v => hs ⟨k, v⟩)
  have hgPl : ∀ kv, (s kv).v ∈ GlobalTheory.PendOf.gPl D := by
    intro kv
    refine ⟨kv, ?_⟩
    show _ = _
    rw [← hs kv]
    exact (s kv).w_under
  refine ⟨fun g => ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map (fun kv => x kv (g kv))).prod,
    fun g => ⟨?_, ?_⟩, fun g => ?_⟩
  · apply trivOutside_list_prod
    intro y hy
    obtain ⟨kv, -, rfl⟩ := List.mem_map.1 hy
    intro w hw
    exact hx1 kv (g kv) w (fun e => hw (by rw [Set.mem_singleton_iff.1 e]; exact hgPl kv))
  · intro kv s' hs'
    have e : s' = s kv := GlobalTheory.SplitPlaceExt.eq_of_w_eq D.host.E (s kv) s' (hs'.trans (hs kv).symm)
    subst e
    rw [map_list_prod, List.map_map]
    rw [list_prod_map_eq _ kv _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _))]
    · exact hx3 kv (g kv)
    · intro kv' _ hne
      exact loc_eq_one_of_ne (s kv) (fun e => hne (hinj e.symm)) (hx1 kv' (g kv'))
  · apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨kv, -, rfl⟩ := List.mem_map.1 hy
    exact hx2 kv (g kv)

end GlobalTheory.LiftStandardGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistOfPlaceInWeightSetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_of_place_in_weight_set : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ a : (w.D Z).nd.Loc, (w.D Z).ntw.NonzeroIndexPlace ((w.D Z).ntw.twOf a) := by
  first | exact @GlobalTheory.HeightCounting.InW1TwistAtMember.inW1_twOf_atMem | exact GlobalTheory.HeightCounting.InW1TwistAtMember.inW1_twOf_atMem | (intros; apply GlobalTheory.HeightCounting.InW1TwistAtMember.inW1_twOf_atMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistReadingInducesSideEmbeddingFixedField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem mem_range_map_iff_of_isLocalHom {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) [IsLocalHom f] (hf : Function.Injective f) (t : FractionRing A) :
    IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t ∈ (algebraMap B (FractionRing B)).range ↔
      t ∈ (algebraMap A (FractionRing A)).range := by
  have hmap : ∀ a : A, IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf (algebraMap A _ a) =
      algebraMap B _ (f a) := fun a => by simp [IsFractionRing.map]
  constructor
  · rintro ⟨c, hc⟩
    by_cases ht : t = 0
    · exact ⟨0, by rw [ht, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger A t with ⟨a, ha⟩ | ⟨m, hm⟩
    · exact ⟨a, ha⟩
    · have h1 : IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t *
          IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      rw [← hc, ← hm, hmap, ← map_mul] at h1
      have h2 : c * f m = 1 := IsFractionRing.injective B (FractionRing B) (by rw [h1, map_one])
      have hu : IsUnit m := (isUnit_map_iff f m).1 (IsUnit.of_mul_eq_one_right c h2)
      refine ⟨((hu.unit⁻¹ : Aˣ) : A), ?_⟩
      rw [← inv_inv t, ← hm]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul]
      simp
  · rintro ⟨a, rfl⟩
    exact ⟨f a, (hmap a).symm⟩

end GlobalTheory.LevCmp

namespace GlobalTheory.LevCmp

theorem reading_sidePl_emb : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), GlobalTheory.HeightCounting.SidePl D v i b ∧ (∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x))) ∧ ∀ (h : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp ((algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))))) (x : ↥D.LL0), ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) h (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := by
  intro D i k b v ρ
  haveI := GlobalTheory.TwistChoice.isLocalHom_phiK i k
  haveI := ρ.loc
  have hinj : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp (BlochKatoReduction.Gen.phiK D.ntw i k)) :=
    ρ.inj.comp ((D.ntw.Ok_inj i k).comp (D.ntw.O_inj i))
  have hmap : ∀ a : D.ntw.O0 i, IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) hinj
      (algebraMap _ _ a) = algebraMap ρ.Oe _ (algebraMap _ ρ.Oe (BlochKatoReduction.Gen.phiK D.ntw i k a)) := fun a => by
    simp [IsFractionRing.map]
  have key : ∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) =
      IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) hinj
        (GlobalTheory.TwistChoice.sideEmb i b x) := by
    intro x
    obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 i) (GlobalTheory.TwistChoice.sideEmb i b x)
    have hz0 : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
    have hside : GlobalTheory.TwistChoice.sideEmb i b x * algebraMap _ (FractionRing (D.ntw.O0 i)) z =
        algebraMap _ (FractionRing (D.ntw.O0 i)) y := by
      rw [← hyz, div_mul_cancel₀ _ hz0]
    have h1 := ρ.emb_side x y z hside
    have hz' : algebraMap ρ.Oe (FractionRing ρ.Oe) (algebraMap _ ρ.Oe (BlochKatoReduction.Gen.phiK D.ntw i k z)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), ← RingHom.comp_apply,
        map_eq_zero_iff _ hinj]
      exact nonZeroDivisors.ne_zero hz
    rw [← hyz, map_div₀, hmap, hmap, eq_div_iff hz']
    exact h1
  have hside : ∀ x : ↥D.LL0, GlobalTheory.TwistChoice.sideEmb i b x =
      (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := fun x => by
    cases b <;> rfl
  refine ⟨fun x => ?_, fun x => ?_, fun h x => ?_⟩
  · rw [ρ.emb_w, key, ← hside]
    exact mem_range_map_iff_of_isLocalHom _ hinj _
  · rw [key]
    obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 i) (GlobalTheory.TwistChoice.sideEmb i b x)
    have e : GlobalTheory.SeriesTie.sideEmb D.ntw i b x = IsFractionRing.map (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) (GlobalTheory.TwistChoice.sideEmb i b x) := by
      cases b <;> rfl
    rw [e, ← hyz]
    simp [map_div₀, IsFractionRing.map, NX.toKk, BlochKatoReduction.Gen.phiK]
  · rw [key, ← hside]
    rfl

end GlobalTheory.LevCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceWeightPositiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_place_weight_positive : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → 0 < (w.D Z).what₂.lamP ((w.D Z).what₂.muTw v) j σ := by
  first | exact @GlobalTheory.Mem.LamPosTw.eigenvalue_twistedWeight_pos | exact GlobalTheory.Mem.LamPosTw.eigenvalue_twistedWeight_pos | (intros; apply GlobalTheory.Mem.LamPosTw.eigenvalue_twistedWeight_pos <;> assumption)
end

