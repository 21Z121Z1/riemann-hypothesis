import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignature
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SkewUnit

theorem isUnit_det_of_isSkew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d : ℕ) (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s → IsUnit W.J.det := by
  intro F E _ _ _ _ _ σ B d W r s hW
  exact isUnit_iff_ne_zero.2 (GlobalTheory.SkewDet.det_ne_zero_of_isSkew F E σ B d r s W hW)

end GlobalTheory.SkewUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivSplitCentre
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CuspRep.SplitDeriv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem hasDerivAt_scalar_exp :
    HasDerivAt (fun t : ℝ =>
      toL (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))).val)
      (fun i j => if i = j then (1 : Cinf E) else 0) 0 := by
  rw [hasDerivAt_pi]; intro i
  rw [hasDerivAt_pi]; intro j
  rw [hasDerivAt_pi]; intro w
  by_cases h : i = j
  · subst h
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have h2 := h1.cexp
    simpa [toL, Matrix.scalar_apply, Matrix.diagonal_apply, expU] using h2
  · simpa [toL, Matrix.scalar_apply, Matrix.diagonal_apply, h] using hasDerivAt_const (0 : ℝ) (0 : ℂ)

open GlobalTheory.UnitaryBC in

theorem hasDerivAt_splitCentre (ψ : Sm E a) (g : GA E a) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ψ.1 (g * splitCentre E a t))
      ((lie E a (fun i j => if i = j then (1 : Cinf E) else 0) ψ).1 (g * splitCentre E a s)) s := by
  have h0 : Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext i j w
    by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, expU, Matrix.one_apply, h]
  have h := hasDerivAt_curve ψ (g * splitCentre E a s)
    (fun t => Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)))
    _ h0 hasDerivAt_scalar_exp
  have h' := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h)
  rw [lie_apply]
  refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  change ψ.1 (g * splitCentre E a t) = ψ.1 (g * splitCentre E a s * splitCentre E a (t - s))
  rw [mul_assoc, ← splitCentre_add, add_sub_cancel]

end GlobalTheory.CuspRep.SplitDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeForcedLambdaStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_shape_forced_lambda : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → (∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => (κ : ℚ) / 2) μ' → μ' = GlobalTheory.RealLift.lam P Q R S κ) ∧ ∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P' Q' R S (fun _ => -((κ : ℚ) / 2)) μ' → (fun c => μ' c + (κ : ℚ) / 2) = GlobalTheory.RealLift.lam P Q R S κ := by
  first | exact @GlobalTheory.RealLift.jointShape_halfKappa | exact GlobalTheory.RealLift.jointShape_halfKappa | (intros; apply GlobalTheory.RealLift.jointShape_halfKappa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LandherrStandardDefiniteHermitianCmField
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LandherrStd

open GroundTheory.Global.SemiLocal
open scoped GroundTheory.Global.SemiLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_pos (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (u : HeightOneSpectrum (𝓞 E))
    [u.asIdeal.LiesOver v.asIdeal] :
    0 < Module.finrank (v.adicCompletion (maximalRealSubfield E)) (u.adicCompletion E) := by
  rw [finrank_eq_ramificationIdx_mul_inertiaDeg E v u]
  exact Nat.mul_pos (Ideal.ramificationIdx_pos u.asIdeal _) (Ideal.inertiaDeg_pos _ _)

theorem det_map' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) : (M.map f).det = f M.det :=
  (RingHom.map_det f M).symm

theorem exists_sq_sub_mul_sq (hU : Unr E) (θ : E) (hθ0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)
    (d : maximalRealSubfield E) (hd : (d : E) = θ * θ) (a : maximalRealSubfield E)
    (hloc : ∀ w : Pl E, ¬ IsSplitAt w → ∃ z : w.adicCompletion E,
      algebraMap E (w.adicCompletion E) (a : E) = cj w z * z)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ x y : v.adicCompletion (maximalRealSubfield E),
      algebraMap _ (v.adicCompletion (maximalRealSubfield E)) a =
        x ^ 2 - algebraMap _ (v.adicCompletion (maximalRealSubfield E)) d * y ^ 2 := by
  set Fv := v.adicCompletion (maximalRealSubfield E)
  haveI : CharZero Fv :=
    charZero_of_injective_algebraMap (algebraMap (maximalRealSubfield E) Fv).injective
  have hd0 : d ≠ 0 := fun h => mul_ne_zero hθ0 hθ0 (hd.symm.trans (by rw [h]; rfl))
  by_cases hsq : IsSquare (algebraMap _ Fv d)
  · exact GlobalTheory.Published.HasseNormSt.of_isSquare ((_root_.map_ne_zero _).2 hd0) hsq _
  obtain ⟨w, hw⟩ := (GlobalTheory.QNorm.places_over (maximalRealSubfield E) E).2.1 v
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, HeightOneSpectrum.under_asIdeal]⟩
  set ι := completionMap v w with hιdef
  have hι : ∀ x : maximalRealSubfield E,
      ι (algebraMap _ Fv x) = algebraMap E (w.adicCompletion E) (x : E) := by
    intro x
    rw [hιdef, completionMap_algebraMap, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E]
    rfl
  set t := algebraMap E (w.adicCompletion E) θ with htdef
  have ht2 : t * t = ι (algebraMap _ Fv d) := by rw [hι, hd, map_mul]
  have hnot : ∀ s : Fv, t ≠ ι s := by
    intro s hs
    apply hsq
    refine ⟨s, ι.injective ?_⟩
    rw [← ht2, map_mul, hs]
  have hsm : ∀ (s : Fv) (y : w.adicCompletion E), s • y = ι s * y := fun s y => Algebra.smul_def s y
  have hli : LinearIndependent Fv ![(1 : w.adicCompletion E), t] := by
    rw [LinearIndependent.pair_iff]
    intro s r h
    rw [hsm, hsm, mul_one] at h
    by_cases hr : r = 0
    · subst hr
      rw [map_zero, zero_mul, add_zero] at h
      exact ⟨ι.injective (by rw [h, map_zero]), rfl⟩
    · exfalso
      apply hnot (-s / r)
      have hr' : ι r ≠ 0 := (_root_.map_ne_zero ι).2 hr
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
  have hsum := sum_finrank_eq E v
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at hsum
  have hle : Module.finrank Fv (w.adicCompletion E) ≤ 2 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun u : PlacesOver E v =>
      Module.finrank Fv (u.1.adicCompletion E)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨w, inferInstance⟩)
  haveI : Module.Finite Fv (w.adicCompletion E) := Module.finite_of_finrank_pos (finrank_pos v w)
  have hge : 2 ≤ Module.finrank Fv (w.adicCompletion E) := by
    simpa using hli.fintype_card_le_finrank
  have h2 : Module.finrank Fv (w.adicCompletion E) = 2 := le_antisymm hle hge
  have hns : ¬ IsSplitAt w := by
    rintro ⟨u, hne, hu⟩
    haveI : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, ← hu, HeightOneSpectrum.under_asIdeal]⟩
    have hpos := finrank_pos v u
    have hne' : (⟨u, inferInstance⟩ : PlacesOver E v) ≠ ⟨w, inferInstance⟩ :=
      fun h => hne (congrArg Subtype.val h)
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun u : PlacesOver E v =>
      Module.finrank Fv (u.1.adicCompletion E))
      (Finset.subset_univ {(⟨u, inferInstance⟩ : PlacesOver E v), ⟨w, inferInstance⟩})
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hne', hsum] at this
    have key : Module.finrank Fv (u.adicCompletion E) + Module.finrank Fv (w.adicCompletion E) ≤ 2 := this
    rw [h2] at key
    have hpos' : 0 < Module.finrank Fv (u.adicCompletion E) := hpos
    omega
  obtain ⟨z, hz⟩ := hloc w hns
  have hcc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hns).1
  have hcj : ∀ s : Fv, cj w (ι s) = ι s := by
    have h := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      ((GlobalTheory.ConjAtPlace.main E hU w).1.comp (continuous_completionMap v w))
      (continuous_completionMap v w) (funext fun x => ?_)
    · exact fun s => congrFun h s
    · simp only [Function.comp_apply]
      rw [← hιdef, hι, hcc]
      congr 1
      exact (IsCMField.complexConj E).commutes x
  have hct : cj w t = -t := by rw [htdef, hcc, hθ, map_neg]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hzb : z = ι (b.repr z 0) + ι (b.repr z 1) * t := by
    conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two]
    simp [b, hsm]
  obtain ⟨A, C, hAC⟩ : ∃ A C : Fv, z = ι A + ι C * t := ⟨_, _, hzb⟩
  refine ⟨A, C, ι.injective ?_⟩
  rw [hι, hz, hAC, map_add, map_mul, hcj, hcj, hct, map_sub, map_mul, map_pow, map_pow, ← ht2]
  ring

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
    (H : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H →
    (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) →
    (∀ w : Pl E, ¬ IsSplitAt w → ∃ g : Matrix (Fin n) (Fin n) (w.adicCompletion E),
      H.map (algebraMap E (w.adicCompletion E)) = cT (cj w) g * g) →
    ∃ h : GL (Fin n) E, H = cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * h.val := by
  intro E _ _ _ hU n H hH hτ hw
  have hG' : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (H a b) = H b a := fun a b => by
    have := congrFun (congrFun hH b) a
    simpa [cT, ReciprocityTheory.ChartRestriction.G.FD.cc] using this
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc ((1 : Matrix (Fin n) (Fin n) E) a b) =
      (1 : Matrix (Fin n) (Fin n) E) b a := by
    intro a b
    by_cases h : a = b
    · subst h
      simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), ReciprocityTheory.ChartRestriction.G.FD.cc]
  have hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧
      H.map τ = Qᵀ * (1 : Matrix (Fin n) (Fin n) E).map τ * Q.map (starRingEnd ℂ) := by
    intro τ
    obtain ⟨Q, hQ, hQe⟩ := hτ τ
    refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
    · rw [det_map']
      exact (_root_.map_ne_zero _).2 hQ
    · have h1 : (Q.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Q := by
        ext i j
        simp
      rw [hQe, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.mul_one, h1]
      rfl
  have hd : H.det ≠ 0 := by
    obtain ⟨Q, hQ, hQe⟩ := hτ (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    intro h0
    have h1 := congrArg Matrix.det hQe
    rw [det_map', h0, map_zero, Matrix.det_mul] at h1
    have h2 : (cT (starRingEnd ℂ) Q).det = starRingEnd ℂ Q.det := by
      unfold cT
      rw [Matrix.det_transpose, det_map']
    rw [h2] at h1
    exact mul_ne_zero ((_root_.map_ne_zero _).2 hQ) hQ h1.symm
  have hd1 : (1 : Matrix (Fin n) (Fin n) E).det ≠ 0 := by simp
  obtain ⟨P, hP, hPe⟩ : ∃ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 ∧
      H = Pᵀ * 1 * P.map ReciprocityTheory.ChartRestriction.G.FD.cc := by
    refine GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt E n 1 H hG hG' hd1 hd hs ?_
    have hm : (1 : Matrix (Fin n) (Fin n) E).det / H.det ∈ maximalRealSubfield E := by
      rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
      exact congrArg₂ (· / ·) (GlobalTheory.Published.cc_det_of_herm hG) (GlobalTheory.Published.cc_det_of_herm hG')
    let a : maximalRealSubfield E := ⟨_, hm⟩
    obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
    obtain ⟨d, hdθ⟩ := GlobalTheory.Published.exists_sq_real hθ
    have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (hdθ.symm.trans (congrArg Subtype.val h))
    have ha0 : a ≠ 0 := fun h => div_ne_zero hd1 hd (congrArg Subtype.val h)
    have hloc : ∀ w : Pl E, ¬ IsSplitAt w → ∃ z : w.adicCompletion E,
        algebraMap E (w.adicCompletion E) (a : E) = cj w z * z := by
      intro w hns
      obtain ⟨g, hg⟩ := hw w hns
      have h1 := congrArg Matrix.det hg
      rw [det_map', Matrix.det_mul] at h1
      have h2 : (cT (cj w) g).det = cj w g.det := by
        unfold cT
        rw [Matrix.det_transpose, det_map']
      rw [h2] at h1
      refine ⟨g.det⁻¹, ?_⟩
      change algebraMap E (w.adicCompletion E) ((1 : Matrix (Fin n) (Fin n) E).det / H.det) = _
      rw [Matrix.det_one, one_div, map_inv₀, h1, map_inv₀, mul_inv]
    obtain ⟨x, y, hxy⟩ := GlobalTheory.QNorm.hasseNormSt (maximalRealSubfield E) d a hd0 ha0
      (fun ρ => by
        let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
        have h1 : τ (a : E) = (Complex.ofRealHom.comp ρ) a :=
          ComplexEmbedding.lift_algebraMap_apply E _ a
        have h2 : 0 < (τ (a : E)).re := GlobalTheory.Published.Landherr.re_det_div_pos hd1 τ (hs τ)
        rw [h1] at h2
        exact ⟨√(ρ a), 0, by rw [Real.sq_sqrt (le_of_lt (by simpa using h2))]; ring⟩)
      (fun v => exists_sq_sub_mul_sq hU θ h0 hθ d hdθ a hloc v)
    refine ⟨x + y * θ, ?_⟩
    have h1 := congrArg (Subtype.val : maximalRealSubfield E → E) hxy
    have h2 : IsCMField.complexConj E θ = -θ := hθ
    simp [a, hdθ] at h1
    simp only [Matrix.det_one, one_div, ReciprocityTheory.ChartRestriction.G.FD.cc, map_add, map_mul,
      IsCMField.complexConj_apply_eq_self, h2]
    linear_combination h1
  have hPc : (P.map ReciprocityTheory.ChartRestriction.G.FD.cc).det ≠ 0 := by
    rw [show (P.map ReciprocityTheory.ChartRestriction.G.FD.cc) = P.map (IsCMField.complexConj E).toRingEquiv.toRingHom from rfl,
      det_map']
    exact (_root_.map_ne_zero _).2 hP
  let u : GL (Fin n) E := ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hPc)).unit
  refine ⟨u, ?_⟩
  have hu : (u : Matrix (Fin n) (Fin n) E) = P.map ReciprocityTheory.ChartRestriction.G.FD.cc := rfl
  rw [hu, hPe, Matrix.mul_one]
  congr 1
  ext i j
  simp [cT, ReciprocityTheory.ChartRestriction.G.FD.cc]

end GlobalTheory.LandherrStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesLeftStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → ∀ M : Matrix (Fin n) (Fin n) (AE F E),
    Set.Finite {w : Pl F | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w} := by
  first | exact @GlobalTheory.AdelMatLat.almost_all_stable | exact GlobalTheory.AdelMatLat.almost_all_stable | (intros; apply GlobalTheory.AdelMatLat.almost_all_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRight
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open Matrix
namespace GlobalTheory.AdelMatLatRight

open NumberField IsDedekindDomain in
open Matrix in

theorem _root_.GlobalTheory.AdelMatLatRight.transpose_mem_latAtV {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (w : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) :
    ∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y w, γᵀ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Y X w := by
  intro γ hγ
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV at hγ ⊢
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, x, hx, ?_⟩
    rw [transpose_smul]
    congr 1
    ext i j
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, vecMulVec_apply, mul_comm]
  | zero => simpa using zero_mem _
  | add u v _ _ hu hv => simpa [transpose_add] using add_mem hu hv
  | neg u _ hu => simpa [transpose_neg] using neg_mem hu

theorem almost_all_stable_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : Spc F E n) (Y : Spc F E d), Y.L.IsLattice E → ∀ N : Matrix (Fin d) (Fin d) (AE F E),
    Set.Finite {w : Pl F | ¬ ∀ γ ∈ latAtV X Y w, γ * Matrix.transpose N ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hY N
  refine (GlobalTheory.AdelMatLat.almost_all_stable F E d n Y X hY N).subset fun w hw h => hw fun γ hγ => ?_
  have h1 := transpose_mem_latAtV Y X w _ (h _ (transpose_mem_latAtV X Y w γ hγ))
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at h1

end GlobalTheory.AdelMatLatRight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecondStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieFirst_of_lieSecond' : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := by
  first | exact @GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond | exact GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond | (intros; apply GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqRightTranslateStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_norm_sq_right_translate : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ) (h : GL (Fin d) k),
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ (Y * (GlobalTheory.SplitFlip.invT h).1)‖ₑ ^ 2 ∂ν =
        ‖GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (a : ℂ)‖ₑ * ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.SplitFlip.lintegral_mul_invT_sq | exact GlobalTheory.SplitFlip.lintegral_mul_invT_sq | (intros; apply GlobalTheory.SplitFlip.lintegral_mul_invT_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqSchwartzPosFiniteStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_norm_sq_schwartz_pos_finite : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ SB (Matrix (Fin a) (Fin d) k) → Φ ≠ 0 →
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ 0 ∧ ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  first | exact @GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top | exact GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top | (intros; apply GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitaryStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_smooth_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ t : E →ₐ[F] Fv F v, GlobalTheory.SmGL.IsSmoothChar (chrW X.ν t) ∧ GlobalTheory.SmGL.IsUnitaryChar (chrW X.ν t) := by
  first | exact @GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary | exact GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary | (intros; apply GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearOperatorL2IsometryStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_linear_operator_l2_isometry : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (T : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ),
    (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
    (∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v), ∀ c : ℂ, T (c • φ + φ') = c • T φ + T φ') →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    (∀ φ ∈ SB (κ → Fv F v), ∫⁻ y, ‖T φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v),
      ∫ x, T φ₁ x * starRingEnd ℂ (T (fun y => starRingEnd ℂ (φ₂ y)) x) ∂μ = ∫ x, φ₁ x * φ₂ x ∂μ := by
  first | exact @GlobalTheory.PolarSB.pairing_eq | exact GlobalTheory.PolarSB.pairing_eq | (intros; apply GlobalTheory.PolarSB.pairing_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalForm
section
open ValuativeRel Matrix

namespace GlobalTheory

theorem rank_frame_exists :
    ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (X : Matrix A D K), ∃ (H : Matrix (Fin X.rank) A K) (Q : Matrix D (Fin X.rank) K),
        H * X * Q = 1 := by
  intro K _ A D _ _ _ _ X
  classical
  let V := LinearMap.range X.mulVecLin
  let b : Module.Basis (Fin X.rank) K V := Module.finBasis K V
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := V) b.equivFun.toLinearMap
  have hpre : ∀ i, ∃ v : D → K, X *ᵥ v = ((b i : V) : A → K) := fun i => by
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (b i).2
    exact ⟨v, hv⟩
  choose q hq using hpre
  refine ⟨LinearMap.toMatrix' g, Matrix.of fun d i => q i d, ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
    Matrix.one_mulVec]
  have hcol : (Matrix.of fun d i => q i d).col j = q j := by
    ext d; simp [Matrix.col]
  rw [hcol, hq j, LinearMap.toMatrix'_mulVec]
  have := congrArg (fun f => f (b j)) hg
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearEquiv.coe_coe] at this
  rw [this]
  ext k
  rw [Module.Basis.equivFun_self]
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

end GlobalTheory
end

