import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0049
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosurePointsIsGroup
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in

theorem ptsGroup_map_ev {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (φ : A →ₐ[ℚ] B) (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι A) :
    φ (ev f g) = ev f (g.map φ) := by
  unfold ev
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem ptsGroup_generic_map {R : Type} [CommRing R] [Algebra ℚ R] (g : Matrix ι ι R) :
    (Matrix.mvPolynomialX ι ι ℚ).map (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)) = g := by
  ext i j
  simp [Matrix.mvPolynomialX]

theorem ptsGroup_ev_adjugate {R : Type} [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι R) : ev (ev f (Matrix.mvPolynomialX ι ι ℚ).adjugate) g = ev f g.adjugate := by
  have h := ptsGroup_map_ev (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2)) f
    (Matrix.mvPolynomialX ι ι ℚ).adjugate
  have h2 := AlgHom.map_adjugate (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2))
    (Matrix.mvPolynomialX ι ι ℚ)
  simp only [AlgHom.mapMatrix_apply] at h2
  rw [h2, ptsGroup_generic_map] at h
  exact h

theorem ptsGroup_ev_det {R : Type} [CommRing R] [Algebra ℚ R]
    (g : Matrix ι ι R) : ev ((Matrix.mvPolynomialX ι ι ℚ).det - 1) g = g.det - 1 := by
  have h2 := AlgHom.map_det (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => g ij.1 ij.2))
    (Matrix.mvPolynomialX ι ι ℚ)
  simp only [AlgHom.mapMatrix_apply] at h2
  rw [ptsGroup_generic_map] at h2
  unfold ev
  rw [map_sub, map_one, h2]

theorem ptsGroup_ev_one (R : Type) [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ) :
    ev f (1 : Matrix ι ι R) = algebraMap ℚ R (ev f (1 : Matrix ι ι ℚ)) := by
  have h := ptsGroup_map_ev (Algebra.ofId ℚ R) f (1 : Matrix ι ι ℚ)
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h.symm

theorem ptsGroup_ev_mul {R : Type} [CommRing R] [Algebra ℚ R] (f : MvPolynomial (ι × ι) ℚ)
    (x y : Matrix ι ι R) :
    MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => x ij.1 ij.2) (fun ij : ι × ι => y ij.1 ij.2))
      (ev f ((Matrix.of fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ)) *
        (Matrix.of fun i j => (MvPolynomial.X (Sum.inr (i, j)) : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ)))) =
      ev f (x * y) := by
  rw [ptsGroup_map_ev]
  congr 1
  ext i j
  simp [Matrix.mul_apply]

theorem pts_group : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ∀ (R : Type) [CommRing R] [Algebra ℚ R], (1 : Matrix ι ι R) ∈ pts Γ R ∧ (∀ x ∈ pts Γ R, ∀ y ∈ pts Γ R, x * y ∈ pts Γ R) ∧ (∀ x ∈ pts Γ R, x.adjugate ∈ pts Γ R) ∧ ∀ x ∈ pts Γ R, x.det = 1 := by
  intro ι _ _ Γ hΓ R _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    have h1 := hf 1 hΓ.one_mem
    rw [ptsGroup_ev_one] at h1 ⊢
    rw [(map_eq_zero_iff _ (algebraMap ℚ ℂ).injective).1 h1, map_zero]
  · intro x hx y hy f hf
    rw [← ptsGroup_ev_mul]
    refine GlobalTheory.T.aeval_sum_elim_eq_zero_of_mem_pts' ι Γ hΓ.aut_mem _ ?_ R x hx y hy
    intro g hg h hh
    rw [ptsGroup_ev_mul]
    exact hf _ (hΓ.mul_mem g hg h hh)
  · intro x hx f hf
    rw [← ptsGroup_ev_adjugate]
    refine hx _ ?_
    intro g hg
    rw [ptsGroup_ev_adjugate]
    exact hf _ (hΓ.adj_mem g hg)
  · intro x hx
    rw [← sub_eq_zero, ← ptsGroup_ev_det]
    refine hx _ ?_
    intro g hg
    rw [ptsGroup_ev_det, hΓ.det_eq g hg, sub_self]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsUnionSupPowersEqTopAtPlaces
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem sUnits_union_sup_finPow_eq_top :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → AdmP p F S → Disjoint S T → (∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F))) → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ := by
  intro p F _ _ _ S T hp hS hST hA
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS.1
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  have key : ∀ v ∈ T, ∃ w ∈ sUnits F S,
      w⁻¹ * (a * x) ∈ powSub p (algebraMap F (v.adicCompletion F)) ∧
        ∀ v' ∈ T, v' ≠ v → w ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
    intro v hv
    obtain ⟨u, hu, hnu, hu'⟩ := hA v hv
    obtain ⟨k, r, hr⟩ := GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit p F v (algebraMap F (v.adicCompletion F) (u : F))
      (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)) hp (hS.2 v (hTS v hv))
      (by rw [hval]; exact (mem_sUnits F S u).1 hu v (hTS v hv))
      (by rw [hval]; exact hy v hv) (fun r h => hnu ⟨r, h⟩)
    refine ⟨u ^ k, pow_mem hu k, ⟨r, ?_⟩, fun v' hv' hne => pow_mem (hu' v' hv' hne) k⟩
    have hu0 : algebraMap F (v.adicCompletion F) (u : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, hr, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
      map_pow, inv_mul_cancel_left₀ (pow_ne_zero k hu0)]
  choose! w hwS hw1 hw2 using key
  have huU : ∏ v ∈ T, w v ∈ sUnits F (S ∪ T) := by
    refine prod_mem fun t ht => ?_
    rw [mem_sUnits]
    intro v hv
    exact (mem_sUnits F S _).1 (hwS t ht) v fun h => hv (Finset.mem_union_left _ h)
  have hsq : (∏ v ∈ T, w v)⁻¹ * (a * x) ∈ finPow p F T := by
    simp only [finPow, Subgroup.mem_iInf]
    intro v hv
    rw [← Finset.mul_prod_erase T w hv, mul_inv, mul_right_comm]
    refine mul_mem (hw1 v hv) (inv_mem (prod_mem fun t ht => ?_))
    exact hw2 t (Finset.mem_of_mem_erase ht) v hv (Finset.ne_of_mem_erase ht).symm
  have hx : x = ((∏ v ∈ T, w v) * a⁻¹) * ((∏ v ∈ T, w v)⁻¹ * (a * x)) := by
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, inv_mul_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup (mul_mem huU (inv_mem haU)) hsq

end GlobalTheory.CNorm
end

