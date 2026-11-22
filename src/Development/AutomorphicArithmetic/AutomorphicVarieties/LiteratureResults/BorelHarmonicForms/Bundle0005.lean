import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SmForm
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.smForm :
    UpperTheory.V.Lit.Bor.SmForm := by
  intro E _ _ _ a Ξ r H G hH hG X x hx y hy
  set c : ℂ := ((2 * r * ell E a (toL X.1) : ℝ) : ℂ) with hc
  have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
  obtain ⟨h1, h2⟩ := UpperTheory.V.Lit.Bor.tformAdj (Sm E a) Ξ.d H (sqSub E a r) G (Ξ.dmat (toL X.1)) (Ξ.dmat (toL X.1))
    (lie E a (toL X.1)) (-lie E a (toL X.1) - c • 1)
  have hX : star X.1 = X.1 := X.2
  have e1 := h1 (by have := hG.adj X.1; rwa [hX] at this) x y
  have e2 := h2 (fun φ hφ ψ hψ => by
    have := hH.skew (toL X.1) φ hφ ψ hψ
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_neg,
      LinearMap.map_smulₛₗ, hcc, smul_eq_mul]
    rw [← hc] at this
    linear_combination this) x hx y hy
  have e3 : smLie Ξ (toL X.1) y = smA Ξ (toL X.1) y + smB Ξ (toL X.1) y := by
    simp [smB]
  have e4 : smAdj Ξ r (toL X.1) x = smB Ξ (toL X.1) x +
      (-lie E a (toL X.1) - c • (1 : Module.End ℂ (Sm E a))).rTensor _ x := by
    rw [smAdj, adj_apply, smA_apply, LinearMap.rTensor_sub, LinearMap.rTensor_neg, LinearMap.rTensor_smul,
      Module.End.one_eq_id, LinearMap.rTensor_id, ← algebraMap_smul ℂ (2 * r * ell E a (toL X.1)) x]
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [show algebraMap ℝ ℂ (2 * r * ell E a (toL X.1)) = c from rfl]
    abel
  rw [e3, e4, map_add, map_add, LinearMap.add_apply, smA_apply, smB_apply, e1, e2, add_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SqUniq
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct
open Formalism.L2.Host GlobalTheory.UnitaryBC

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem chi_split {χ : HChar E} {s : ℝ} (h : χ.IsAbsPow s) :
    ((chiDet a χ (splitCentre E a 1) : ℂˣ) : ℂ) = ((Real.exp ((a : ℝ) * s * Fintype.card (E →+* ℂ)) : ℝ) : ℂ) := by
  have e : chiDet a χ (splitCentre E a 1) = chiInf χ (GeneralLinearGroup.det
      (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ)))) :=
    congrArg χ.1 (det_infGL _)
  rw [e, GlobalTheory.CuspRep.InfType.chiInf_eq χ (fun σ => σ) (fun _ z => ((‖z‖ : ℝ) : ℂ) ^ (s : ℂ)) (fun σ z hz =>
    ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_norm).continuousAt continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 hz))) h.2.2]
  have d : ((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ))) : (Cinf E)ˣ) : Cinf E) =
      ((expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ) : (Cinf E)ˣ) : Cinf E) ^ a := by
    simp [Matrix.det_diagonal]
  have c : ∀ σ : E →+* ℂ, ‖coord σ (((expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ) : (Cinf E)ˣ) : Cinf E) ^ a)‖ =
      Real.exp a := fun σ => by
    have c1 : coord σ (fun _ : InfinitePlace E => ((1 : ℝ) : ℂ)) = 1 := map_one (coord σ)
    rw [map_pow, norm_pow, GlobalTheory.CuspRep.InfType.coord_expU, c1, Complex.norm_exp, Complex.one_re, Real.exp_one_pow]
  simp only [d, c]
  rw [← Complex.ofReal_cpow (Real.exp_pos _).le, ← Real.exp_mul, Finset.prod_const, Finset.card_univ,
    ← Complex.ofReal_pow, ← Real.exp_nat_mul, mul_comm]

omit [IsTotallyComplex E] in
private theorem absPow_uniq {χ χ' : HChar E} {s : ℝ} (h : χ.IsAbsPow s) (h' : χ'.IsAbsPow s) : χ = χ' := by
  rw [← mul_inv_eq_one]
  refine GlobalTheory.DiscSpec.Model.eq_one_of_isAbsPow ⟨fun v x hx => ?_, fun v => ?_, fun k => ?_⟩
  · rw [HChar.loc_mul, HChar.loc_inv, h.1 v x hx, h'.1 v x hx, inv_one, mul_one]
  · have : χ.val v = χ'.val v := Units.ext ((h.2.1 v).trans (h'.2.1 v).symm)
    rw [HChar.val_mul, HChar.val_inv, this, mul_inv_cancel]; simp
  · have : χ.inf k = χ'.inf k := Units.ext ((h.2.2 k).trans (h'.2.2 k).symm)
    rw [HChar.inf_mul, HChar.inf_inv, this, mul_inv_cancel]; simp

end

theorem UpperTheory.V.Lit.Bor.sqUniq :
    UpperTheory.V.Lit.Bor.SqUniq := by
  rintro E _ _ _ a ha r χ ⟨⟨s, hs⟩, htw⟩ φ hφ ⟨s', χ', hs', hsq⟩
  have hfun : ∀ ν : HChar E, (mulChi a ν φ).1 = fun g => ((chiDet a ν g : ℂˣ) : ℂ) * φ.1 g := fun ν =>
    funext fun g => by rw [mulChi_apply, mul_comm]
  by_cases h0 : ∀ g, φ.1 g = 0
  · rw [hfun]
    simpa only [h0, mul_zero] using hsq
  obtain ⟨g, hg⟩ := not_forall.1 h0
  have hz : lie E a (oneL E a) (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ := by
    rw [htw, hφ, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, map_zero, zero_smul]
  have h1 := aInv E a _ _ hz 1 g
  have h2 := hsq.1 1 g
  have h3 := aInv E a _ _ hφ 1 g
  simp only [hfun, zero_mul, Complex.exp_zero, one_mul, map_mul, Units.val_mul, h3] at h1 h2
  have key : ∀ x y : ℂ, y ≠ 0 → x * y * (Complex.exp (-(r : ℂ) * (1 : ℝ)) * φ.1 g) = y * φ.1 g →
      x = (Complex.exp (-(r : ℂ) * (1 : ℝ)))⁻¹ := fun x y hy h =>
    eq_inv_of_mul_eq_one_left (mul_right_cancel₀ (mul_ne_zero hy hg) (by linear_combination h))
  have h4 := (key _ _ (Units.ne_zero _) h1).trans (key _ _ (Units.ne_zero _) h2).symm
  rw [chi_split hs, chi_split hs', Complex.ofReal_inj, Real.exp_eq_exp] at h4
  have hc : (Fintype.card (E →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain rfl : s = s' := mul_left_cancel₀ ha' (mul_right_cancel₀ hc h4)
  rw [hfun, absPow_uniq hs hs']
  exact hsq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem sum_coord_re {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (z : Cinf E) :
    ∑ τ : E →+* ℂ, coord τ z = ((2 * ∑ w : InfinitePlace E, (z w).re : ℝ) : ℂ) := by
  have h := congrArg Multiplicative.toAdd
    (GlobalTheory.GKCoh.Tests.prod_coord (M := Multiplicative ℂ) Multiplicative.ofAdd z)
  simp only [toAdd_prod, toAdd_mul, toAdd_ofAdd, Complex.add_conj] at h
  rw [h, Finset.mul_sum, Complex.ofReal_sum]

theorem UpperTheory.V.Lit.Bor.twEx :
    UpperTheory.V.Lit.Bor.TwEx := by
  intro E _ _ _ a _ r
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (r / (2 * ((a : ℝ) * Fintype.card (InfinitePlace E))))
  refine ⟨_, ⟨_, hν⟩, fun X φ => ?_⟩
  rw [lie_mulChi, GlobalTheory.CuspRep.AlgExpo.dchi_eq_sum]
  simp only [(GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 _ hν, ← Finset.mul_sum]
  rw [sum_coord_re, ← Complex.ofReal_mul]
  have e : ell E a X = (∑ w : InfinitePlace E, ((Matrix.of X).trace w).re) /
      ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
    simp [ell, Matrix.trace]
  rw [e]
  congr 4
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.XiSchur
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.xiSchur :
    UpperTheory.V.Lit.Bor.XiSchur := by
  intro E _ _ _ a Ξ
  refine ⟨fun X Y => GlobalTheory.AlgInfChar.dmat_bracket Ξ X Y, fun P hP => ?_⟩
  rcases subsingleton_or_nontrivial (Fin Ξ.d → ℂ) with h | h
  · exact ⟨0, Matrix.ext fun i => congrFun (Subsingleton.elim (α := Fin Ξ.d → ℂ) _ _)⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ))
  have hs : Stab (eEnd Ξ) (Module.End.eigenspace (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ)) c) := by
    intro τ i j w hw
    have hcm : Commute P (eL Ξ.dmat τ i j) := ((hP _).sub_right ((hP _).smul_right _)).smul_right _
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
    rw [eEnd, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hcm.eq, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  have ht := ((algIrr E a Ξ).2 _ hs).resolve_left hc
  refine ⟨c, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  have hv : v ∈ Module.End.eigenspace (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ)) c := by
    rw [ht]; trivial
  rw [Module.End.mem_eigenspace_iff.1 hv, map_smul, Matrix.toLin'_one]
  rfl
end

