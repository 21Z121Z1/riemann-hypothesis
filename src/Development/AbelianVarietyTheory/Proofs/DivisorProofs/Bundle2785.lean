import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCochainsEqDeRhamCochainsSmoothLif
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmOrderUniformizationEndomorphisms
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FilCx

theorem fil_eq_iSup_eigenspace_bar : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)), c ≠ ⊥ → ∀ (𝔠 : FracId (FR E)) (L : Set E) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
      (α : orderC c → (X.A ⟶ X.A)) [∀ a, IsMonHom (α a)],
      (∀ (a : orderC c) w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α a) →
      Fil X.A = ⨆ i, ⨅ a : orderC c,
        Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) := by
  intro hPC hADR E _ _ _ I _ φ hφ c hc 𝔠 L X U α _ hα
  obtain ⟨ε, hpc⟩ := hPC
  set g := Module.finrank ℚ (FR E) with hg
  have hLB : (X.diag U.c).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (X.isLB U.c) _ _
  obtain ⟨P, hspan, hdim, hlie, hend, -⟩ := hpc X.A g X.ab X.dim (X.diag U.c) hLB U.u
  clear hpc
  have hLE : LieExact X.A := (hADR.2.1 ℂ X.A g X.ab X.dim).1
  obtain ⟨Q, hQker, hQP, hFdim⟩ :=
    GlobalTheory.T.hodge_projection_from_lattice (HdR X.A) g U.u.Λ P (Fil X.A) hspan hdim U.u.full (GlobalTheory.T.lattice_combination_in_hodge_filtration X.A X.ab _ g U.u P hLE hlie)
  let M : orderC c → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a ↦
    LinearMap.pi fun j ↦ (φ (U.e j) (a : E)) • LinearMap.proj j
  have hM : ∀ a w, M a w = fun j ↦ φ (U.e j) (a : E) * w j := fun a w ↦ by ext j; simp [M]
  have hMΛ : ∀ (a : orderC c) (x : U.u.Λ), (fun j ↦ φ (U.e j) (a : E) * (x : Fin g → ℂ) j) ∈ U.u.Λ := by
    intro a x
    rw [← U.u.ker, hα a, (U.u.ker x).2 x.2]
    simp
  have hT : ∀ (a : orderC c) (x y : U.u.Λ), (y : Fin g → ℂ) = (fun j ↦ φ (U.e j) (a : E) * (x : Fin g → ℂ) j) →
      push (dp0 ℂ) (𝟙 _) (α a) (P x) = P y := by
    intro a x y hy
    exact hend (α a) (M a) (fun w ↦ by rw [hM]; exact hα a w) x y (by rw [hy, hM])
  have hbar : ∀ σ : E →+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ = ComplexEmbedding.conjugate σ := fun σ ↦ by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
  have hnreal : ∀ σ : E →+* ℂ, ¬ ComplexEmbedding.IsReal σ := fun σ h ↦
    (NumberField.InfinitePlace.isComplex_mk_iff (φ := σ)).1 (NumberField.IsTotallyComplex.isComplex _) h
  have hsep : ∀ (i : I) (j : Fin g), ∃ a : orderC c, φ (U.e j) (a : E) ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) (a : E) := by
    intro i j
    by_contra h
    push_neg at h
    have h1 := GlobalTheory.CMExtend.ringHom_ext_orderC hc _ _ h
    rw [hbar] at h1
    obtain ⟨k, -, hk⟩ := hφ (φ (U.e j))
    have e1 := hk (U.e j) (Or.inl rfl)
    have e2 := hk i (Or.inr h1)
    rw [e1, ← e2] at h1
    exact hnreal _ h1.symm
  have hinj : Function.Injective fun (i : I) (a : orderC c) ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) (a : E) := by
    intro i i' h
    have h1 := GlobalTheory.CMExtend.ringHom_ext_orderC hc _ _ (fun a ↦ congrFun h a)
    rw [hbar, hbar] at h1
    have h2 : φ i = φ i' := by
      ext x
      simpa [ComplexEmbedding.conjugate_coe_eq] using congrArg (starRingEnd ℂ) (RingHom.congr_fun h1 x)
    obtain ⟨k, -, hk⟩ := hφ (φ i)
    exact (hk i (Or.inl rfl)).trans (hk i' (Or.inl h2)).symm
  have hcomm : ∀ a b : orderC c, Commute (push (dp0 ℂ) (𝟙 _) (α a)) (push (dp0 ℂ) (𝟙 _) (α b)) := by
    intro a b
    refine LinearMap.ext_on_range hspan fun x ↦ ?_
    simp only [Module.End.mul_apply]
    rw [hT b x ⟨_, hMΛ b x⟩ rfl, hT a x ⟨_, hMΛ a x⟩ rfl, hT a _ ⟨_, hMΛ a ⟨_, hMΛ b x⟩⟩ rfl,
      hT b _ ⟨_, hMΛ b ⟨_, hMΛ a x⟩⟩ rfl]
    congr 1
    ext j
    simp only
    ring
  have hpos : 0 < g := Module.finrank_pos
  haveI : FiniteDimensional ℂ (HdR X.A) := Module.finite_of_finrank_pos (by rw [hdim]; omega)
  have hEdim : Module.finrank ℂ (HdR X.A) = Module.finrank ℚ E := by
    rw [hdim, ← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]

  let Φ : E →+* (Fin g → ℂ) := Pi.ringHom fun j ↦ φ (U.e j)
  let L' : AddSubgroup E := AddSubgroup.comap Φ.toAddMonoidHom U.u.Λ.toAddSubgroup
  let jL : L' →+ U.u.Λ :=
    { toFun := fun x ↦ ⟨Φ x, x.2⟩
      map_zero' := by ext; simp
      map_add' := fun x y ↦ by ext; simp }
  have hone : ∀ i, 1 ≤ Module.finrank ℂ (⨅ a : orderC c,
      Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) : Submodule ℂ (HdR X.A)) := by
    intro i
    refine le_of_eq (GlobalTheory.T.cm_representation_eigen_decomposition E (orderC c) (GlobalTheory.CMExtend.exists_natMul_mem_orderC hc) L' ?_ (HdR X.A)
      (P.comp jL) ?_ hEdim (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a)) ?_ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i))).symm
    · intro a ha x hx
      show Φ (a * x) ∈ U.u.Λ
      have e : Φ (a * x) = fun j ↦ φ (U.e j) a * (Φ x) j := by rw [map_mul]; rfl
      rw [e]; exact hMΛ ⟨a, ha⟩ ⟨Φ x, hx⟩
    · refine eq_top_mono (Submodule.span_mono ?_) hspan
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, -, hx⟩ := (U.lat y).1 y.2
      have hxy : Φ x = y := by
        rw [hx]; funext j; simp only [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, Pi.zero_apply, zero_mul, add_zero]; rfl
      have hmem : x ∈ L' := by
        show Φ x ∈ U.u.Λ
        rw [hxy]; exact y.2
      refine ⟨⟨x, hmem⟩, ?_⟩
      show P (jL ⟨x, hmem⟩) = P y
      congr 1
      exact Subtype.ext hxy
    · intro a x y hy
      refine hT a (jL x) (jL y) ?_
      show Φ y = fun j ↦ φ (U.e j) a * (Φ x) j
      rw [hy, map_mul]; rfl
  have hle : (⨆ i, ⨅ a : orderC c,
      Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a)) ≤ Fil X.A := by
    refine iSup_le fun i ↦ ?_
    rw [← hQker]
    exact GlobalTheory.T.hodge_projection_eigenvalue_compat (HdR X.A) g U.u.Λ P hspan Q hQP (orderC c) (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a))
      (fun a j ↦ φ (U.e j) (a : E)) hMΛ hT (fun a ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) (fun j ↦ hsep i j)
  have hge := GlobalTheory.T.card_le_finrank_sup_eigenspaces (HdR X.A) (orderC c) (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a)) hcomm I _ hinj hone
  have hcard : Fintype.card I = g := by rw [Fintype.card_congr U.e.symm, Fintype.card_fin]
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hFdim, ← hcard]; exact hge)).symm

end GlobalTheory.FilCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodTranscendenceRelation
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CMEigen

theorem exists_algebraic_eigenvectors : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (U : Unif φ L 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ) (hp : X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p),
    IsCMType φ →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧ a i ≠ 0) →
    (∀ b : E, (∀ x ∈ L, b * x ∈ L) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
      ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
    (∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left) →
    ∃ (y₀ : I → HdR X₀.A) (yv : I → HdR X.A) (w : I → ℂ), ∀ i,
      y₀ i ≠ 0 ∧ (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr (y₀ i) (yv i) ∧ U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧
        IsAlgebraic ℚ (w i / a i) := by
  intro hPC hD _hDC E _ _ _ I _ φ L 𝔠 X₀ X p U v₀ v a hp _hφ hva hex hdesc
  obtain ⟨P, hspan, hP⟩ := GlobalTheory.T.cm_de_rham_period_map_equivariant hPC E I φ L 𝔠 X U
  obtain ⟨b, hbL, hbprim⟩ := GlobalTheory.T.exists_primitive_lattice_multiplier E I φ L 𝔠 X U
  obtain ⟨α, hαm, hα⟩ := hex b hbL
  haveI := hαm
  obtain ⟨α₀, hα₀m, hα₀⟩ := hdesc b α hα
  haveI := hα₀m
  obtain ⟨hf, heig⟩ := GlobalTheory.T.generator_minpoly_eigenvalue_compat E (HdR X.A) P hspan b (push (dp0 ℂ) (𝟙 _) α) (hP b α hα) hbprim
  have hE₀ : LieExact X₀.A := (hD.2.1 Qb X₀.A _ X₀.ab X₀.dim).1
  have hE : LieExact X.A := (hD.2.1 ℂ X.A _ X.ab X.dim).1
  obtain ⟨hBC, hF⟩ := hD.2.2.1 Qb X₀.A _ X₀.ab X₀.dim ℂ X.A p hp.grp
  let D : (Fin (Module.finrank ℚ (FR E)) → ℂ) →L[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ φ (U.e j) b • ContinuousLinearMap.proj j
  have hDz : ∀ z, D z = fun j ↦ φ (U.e j) b * z j := fun z ↦ by
    funext j; simp [D]
  have hD' : ∀ z, U.u.ex (D z) = U.u.ex z ≫ α := fun z ↦ by rw [hDz]; exact hα z
  have key : ∀ i, ∃ (y₀ : HdR X₀.A) (yv : HdR X.A), y₀ ≠ 0 ∧
      (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr y₀ yv ∧ U.IsCMVec i yv (a i) := by
    intro i
    obtain ⟨hLC, hdiff, ha⟩ := hva i
    obtain ⟨Q, c, hQ, hQ1⟩ := GlobalTheory.T.minimal_polynomial_linear_factor_split E b (φ i)
    obtain ⟨h₀, hh₀⟩ := hE₀.2 (v₀ i).hom (v₀ i).isTangent
    obtain ⟨h, hh⟩ := hBC.exists h₀
    have hlie : IsLieImage h (v i).hom := IsLieImage.baseChange (hφ := hp.grp) hF hE hh hLC hh₀
    have hcorr := GlobalTheory.T.de_rham_correspondence_polynomial Qb ℂ (algebraMap Qb ℂ) X₀.A X.A _ p (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp) α₀ α hα₀.symm h₀ h hh Q
    have hDw : D (Pi.single (U.e.symm i) (a i)) = φ i b • Pi.single (U.e.symm i) (a i) := by
      rw [hDz]
      funext j
      by_cases hj : j = U.e.symm i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    obtain ⟨v', hv'1, hv'2⟩ := GlobalTheory.T.lie_image_polynomial_endomorphism X.A (X.diag U.c) _ U.u α D hD' h (v i).hom _ (φ i b) hlie hdiff hDw
      (Q.map (algebraMap Qb ℂ))
    rw [hQ1, one_smul] at hv'2
    have hTy : push (dp0 ℂ) (𝟙 _) α (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) (Q.map (algebraMap Qb ℂ)) h) =
        φ i b • Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) (Q.map (algebraMap Qb ℂ)) h := by
      have e1 := congrArg (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α)) hQ
      rw [map_mul, map_mul, hf, mul_zero, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at e1
      have e2 := LinearMap.congr_fun e1 h
      rw [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply, sub_eq_zero] at e2
      simpa [Algebra.algebraMap_eq_smul_one] using e2
    refine ⟨_, _, ?_, hcorr, fun a' α' _ hα' ↦ heig (φ i) a' _ (hP a' α' hα') _ hTy, v', hv'1, hv'2⟩
    intro h0
    rw [h0] at hcorr
    have hz : (GlobalTheory.Published.AbelianDeRham.bcMor hp.grp).Corr 0 0 := fun c ↦ by simp
    have hy0 := hBC.unique hcorr hz
    rw [hy0] at hv'1
    have hv1 : v' = 1 := (hE.1 0).unique hv'1 (isLieImage_one_iff.2 (zero_mem _))
    rw [hv1] at hv'2
    have := GlobalTheory.ArchMetricCompare.eq_zero_of_isDiff U.u hv'2
    exact ha (by simpa using congrFun this (U.e.symm i))
  choose y₀ yv hy using key
  exact ⟨y₀, yv, a, fun i ↦ ⟨(hy i).1, (hy i).2.1, (hy i).2.2, (hva i).2.2,
    by rw [div_self (hva i).2.2]; exact isAlgebraic_one⟩⟩

end GlobalTheory.CMEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodsAlgebraicNonzero
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenFunctional

theorem mul_comm_of_rank_coker {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (c : K)
    (hrk : Module.rank K (V ⧸ LinearMap.range (T - c • 1)) ≤ 2)
    (hdis : Disjoint (LinearMap.ker (T - c • 1)) (LinearMap.range (T - c • 1)))
    (y₀ : V) (hy : y₀ ≠ 0) (hTy : T y₀ = c • y₀) (f f' : Module.Dual K V) (hf0 : f y₀ = 0) (hf'0 : f' y₀ = 0)
    (hf : ∀ x, f (T x) = c * f x) (hf' : ∀ x, f' (T x) = c * f' x) (x y : V) :
    f x * f' y = f y * f' x := by
  set W := LinearMap.range (T - c • 1) with hW
  have vanish : ∀ (g : Module.Dual K V), (∀ x, g (T x) = c * g x) → ∀ w ∈ W, g w = 0 := by
    rintro g hg w ⟨v, rfl⟩
    simp [hg, smul_eq_mul]
  have hyW : y₀ ∉ W := by
    intro h
    have hk : y₀ ∈ LinearMap.ker (T - c • 1) := by simp [hTy]
    exact hy ((Submodule.disjoint_def.1 hdis) y₀ hk h)
  by_contra hD
  have hD' : f x * f' y - f y * f' x ≠ 0 := sub_ne_zero.2 hD
  have hli : LinearIndependent K ![W.mkQ y₀, W.mkQ x, W.mkQ y] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    replace hg : g 0 • y₀ + g 1 • x + g 2 • y ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul] using hg
    have e1 := vanish f hf _ hg
    have e2 := vanish f' hf' _ hg
    simp only [map_add, map_smul, smul_eq_mul, hf0, hf'0, mul_zero, zero_add] at e1 e2
    have hb : g 1 = 0 := by
      have : g 1 * (f x * f' y - f y * f' x) = 0 := by linear_combination f' y * e1 - f y * e2
      exact (mul_eq_zero.1 this).resolve_right hD'
    have hc : g 2 = 0 := by
      have : g 2 * (f x * f' y - f y * f' x) = 0 := by linear_combination f x * e2 - f' x * e1
      exact (mul_eq_zero.1 this).resolve_right hD'
    rw [hb, hc, zero_smul, zero_smul, add_zero, add_zero] at hg
    have ha : g 0 = 0 := by
      by_contra ha
      exact hyW ((W.smul_mem_iff ha).1 hg)
    intro j; fin_cases j <;> assumption
  have := hli.cardinal_lift_le_rank
  simp only [Cardinal.mk_fintype, Fintype.card_fin, Nat.cast_ofNat, Cardinal.lift_ofNat] at this
  have h3 : (3 : Cardinal) ≤ 2 := by
    have := this.trans (Cardinal.lift_le.2 hrk)
    simpa using this
  norm_num at h3

end GlobalTheory.EigenFunctional

namespace GlobalTheory.EigenFunctional

theorem mul_comm_of_eigen : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
      (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
      (U : Unif φ L 0 X), IsCMType φ → X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    ∀ (i : I) (y₀ : HdR X₀.A), y₀ ≠ 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        act (dp0 Qb) (𝟙 _) X₀.rm b y₀ = β • y₀) →
    ∀ f f' : Module.Dual Qb (HdR X₀.A), f y₀ = 0 → f' y₀ = 0 →
      (∀ (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
        ∀ x, f (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f x ∧ f' (act (dp0 Qb) (𝟙 _) X₀.rm b x) = β * f' x) →
      ∀ x y, f x * f' y = f y * f' x := by
  intro hPC hDR E _ _ _ I _ φ L 𝔠 X₀ X p U hcm hp i y₀ hy0 hy f f' hf0 hf'0 hff x y
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.cm_type_separating_integer E I φ hcm i
  have halg : IsAlgebraic ℚ (φ i ((b₀ : FR E) : E)) := by
    have h1 : IsIntegral ℤ (φ i ((b₀ : FR E) : E)) :=
      ((b₀.2.map (algebraMap (FR E) E).toIntAlgHom).map (φ i).toIntAlgHom)
    exact (h1.tower_top (A := ℚ)).isAlgebraic
  let β₀ : Qb := ⟨φ i ((b₀ : FR E) : E), mem_algebraicClosure_iff.2 halg⟩
  have hβ : algebraMap Qb ℂ β₀ = φ i ((b₀ : FR E) : E) := rfl
  obtain ⟨hC1, hC2⟩ := GlobalTheory.T.cm_de_rham_eigenspace_corank_le_two hPC hDR E I φ L 𝔠 X U hcm i b₀ hb₀
  rw [← hβ] at hC1 hC2
  obtain ⟨hQ1, hQ2⟩ := GlobalTheory.T.algebraic_endomorphism_corank_de_rham hDR (FR E) 𝔠 X₀ X p hp b₀ β₀ hC1 hC2
  exact mul_comm_of_rank_coker _ β₀ hQ1 hQ2 y₀ hy0 (hy b₀ β₀ hβ) f f' hf0 hf'0
    (fun z ↦ (hff b₀ β₀ hβ z).1) (fun z ↦ (hff b₀ β₀ hβ z).2) x y

end GlobalTheory.EigenFunctional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValueStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) (D : Type) [CommRing D] [Algebra R D] (φ ψ : G.A n →ₐ[R] D), Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) = d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) - ((fv d.f (G.A n) D (toConv φ * toConv ψ).ofConv (t.y n) + (toConv φ * toConv ψ).ofConv (d.h n)) - (fv d.f (G.A n) D φ (t.y n) + φ (d.h n)) - (fv d.f (G.A n) D ψ (t.y n) + ψ (d.h n))) := by
  first | exact @GlobalTheory.PtExt.Dat.lift_coc | exact GlobalTheory.PtExt.Dat.lift_coc | (intros; apply GlobalTheory.PtExt.Dat.lift_coc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelSubbundleIsVB
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite
open GlobalTheory.LB (exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.VB

variable {X : Scheme.{0}}

theorem isFrame_of_injective_of_local {F : X.Modules} {U : X.Opens} {ι : Type} [Fintype ι]
    {e : ι → Γ(F, U)}
    (inj : ∀ (V : X.Opens) (h : V ≤ U),
      Function.Injective (Fintype.linearCombination Γ(X, V) fun i => resM F h (e i)))
    (loc : ∀ (V : X.Opens) (h : V ≤ U) (s : Γ(F, V)) (x : X), x ∈ V →
      ∃ (W : X.Opens) (h' : W ≤ V), x ∈ W ∧ ∃ a : ι → Γ(X, W),
        Fintype.linearCombination Γ(X, W) (fun i => resM F (h'.trans h) (e i)) a = resM F h' s) :
    IsFrame e := by
  refine fun V h => ⟨inj V h, fun s => ?_⟩
  choose W hW hx a ha using fun x : V => loc V h s x x.2
  have hc : V ≤ iSup W := fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
  have key (x y : V) : (fun i => resG X (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) =
      fun i => resG X (inf_le_right : W x ⊓ W y ≤ W y) (a y i) := by
    apply inj _ (inf_le_left.trans ((hW x).trans h))
    rw [← resM_linearCombination e ((hW x).trans h), ← resM_linearCombination e ((hW y).trans h),
      ha, ha, resM_resM, resM_resM]
  choose b hb' using fun i => exists_fun_of_cover W hW hc (fun x => a x i)
    fun x y => congrFun (key x y) i
  refine ⟨b, sec_ext_of_cover W hW hc fun x => ?_⟩
  rw [resM_linearCombination, ← ha x]
  exact congrArg _ (funext fun i => hb' i x)

theorem isFrame_cokernel_π {G E : X.Modules} (i : G ⟶ E) [Mono i] {U : X.Opens} {l m : ℕ}
    {e : Fin (l + m) → Γ(E, U)} {f : Fin l → Γ(G, U)} (he : IsFrame e) (hf : IsFrame f)
    (hi : ∀ j, i.app U (f j) = e (Fin.castAdd m j)) :
    IsFrame fun k : Fin m => (cokernel.π i).app U (e (Fin.natAdd l k)) := by
  have hex (V : X.Opens) := GlobalTheory.QCoh.exact_app_of_exact_of_mono (ShortComplex.exact_cokernel i) V

  have hzero (V : X.Opens) (h : V ≤ U) (j : Fin l) :
      (cokernel.π i).app V (resM E h (e (Fin.castAdd m j))) = 0 := by
    rw [← hi, ← app_resM]
    exact (hex V _).2 ⟨_, rfl⟩
  refine isFrame_of_injective_of_local (fun V h => ?_) (fun V h s x hx => ?_)
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    simp only [Fintype.linearCombination_apply, ← app_resM, ← Scheme.Modules.Hom.app_smul,
      ← map_sum] at ha
    obtain ⟨g, hg⟩ := ((hex V _).1 ha)
    obtain ⟨b, rfl⟩ := (hf V h).2 g
    simp only [Fintype.linearCombination_apply, map_sum, Scheme.Modules.Hom.app_smul,
      app_resM, hi] at hg
    have h0 : Fintype.linearCombination Γ(X, V) (fun j => resM E h (e j))
        (Fin.append (-b) a) = 0 := by
      rw [Fintype.linearCombination_apply, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul,
        Finset.sum_neg_distrib, hg, neg_add_cancel]
    have h1 := (he V h).1 (h0.trans (map_zero _).symm)
    funext k
    have := congrFun h1 (Fin.natAdd l k)
    rwa [Fin.append_right] at this
  · obtain ⟨W, hWV, hxW, t, ht⟩ := exists_app_eq_of_epi (cokernel.π i) s hx
    obtain ⟨a, rfl⟩ := (he W (hWV.trans h)).2 t
    refine ⟨W, hWV, hxW, fun k => a (Fin.natAdd l k), ?_⟩
    rw [← ht, Fintype.linearCombination_apply, Fintype.linearCombination_apply, Fin.sum_univ_add,
      map_add, map_sum, map_sum]
    simp only [Scheme.Modules.Hom.app_smul, hzero, smul_zero, Finset.sum_const_zero, zero_add,
      app_resM]

theorem isVB_cokernel_of_frames : ∀ (X : Scheme.{0}) (G E : X.Modules) (i : G ⟶ E) (n l : ℕ)
    (hl : l ≤ n), Mono i → (∀ x : X, ∃ (U : X.Opens) (e : Fin n → Γ(E, U)) (f : Fin l → Γ(G, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame e ∧ GlobalTheory.VB.IsFrame f ∧ ∀ j, i.app U (f j) = e (Fin.castLE hl j)) →
    GlobalTheory.VB.IsVB (cokernel i) (n - l) := by
  intro X G E i n l hl _ H
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [Nat.add_sub_cancel_left]
  intro x
  obtain ⟨U, e, f, hx, he, hf, hi⟩ := H x
  exact ⟨U, _, hx, isFrame_cokernel_π i he hf fun j => (hi j).trans (congrArg e (Fin.ext rfl))⟩

end GlobalTheory.VB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinatorialTangentPointCondition
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.FramedPointCoeffs

open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj MonObj

theorem coeffs_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (S : Type) [Field S] [Algebra c.F S] (P : FrPt Xo c S) (σ : E →+* ℂ)
    (a a' : Fin (Dw.mult σ) → S) (w : Sp (DualNumber S) ⟶ Z.t.G.left),
    IsCombAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) ((frameOf Z P).v σ) a w →
    IsCombAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) ((frameOf Z P).v σ) a' w → a = a' := by
  intro E _ _ _ H Dw l Xo c O _ β Z S _ _ P σ a a' w ha ha'
  have hw : Formalism.L2.Pj.IsTanAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) w :=
    GlobalTheory.ShFam.Pad.Guard.comb_tan ((frameOf Z P).tan σ) ha
  have hv : ∀ i, IsEigV (actR (x0 := GlobalTheory.AllWt.ptF P ≫ Z.j) (S := S) Z.t.act) (embK c σ)
      (GlobalTheory.EigLetters.tvG ((frameOf Z P).tan σ i)) := by
    intro i b
    apply tanM_ext
    apply Over.OverMorphism.ext
    exact (frameOf Z P).eig σ i b
  have h1 := (GlobalTheory.EigLetters.combG_iff ((frameOf Z P).v σ) ((frameOf Z P).tan σ) a hw).1 ha
  have h2 : IsEigV (actR (x0 := GlobalTheory.AllWt.ptF P ≫ Z.j) (S := S) Z.t.act) (embK c σ)
      (GlobalTheory.EigLetters.tvG hw) := by
    rw [h1]
    exact GlobalTheory.EigLetters.eig_combG σ _ hv a
  have he : ∀ b : 𝓞 E, w ≫ (Z.t.act.act b).left =
      spMap (epsMul (algebraMap c.F S (embK c σ b))) ≫ w := by
    intro b
    exact congrArg (fun V => (tv V).left) (h2 b)
  exact ((frameOf Z P).basis σ w hw he).unique ha ha'

end GlobalTheory.FramedPointCoeffs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCochainsEqDeRhamCochainsSmoothLifStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift : (∀ (D : Data) (Λ : Lift D), (∀ k, ∃! w, Λ.Res1 k w) ∧ (∀ w, ∃! k, Λ.Res1 k w) ∧ ∀ k w, Λ.Res1 k w → (k ∈ ((KK D.κ D.t).res Λ.L).Z1 ↔ w ∈ cechDeRhamTotalCocyclesOne (OAff D.s)) ∧ ((∃ g, ((KK D.κ D.t).res Λ.L).D0 g = k) ↔ ∃ g, dTot0 (OAff D.s) g = w)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ k, ∃! w, Λ.Res2 k w) ∧ (∀ w, ∃! k, Λ.Res2 k w) ∧ ∀ k w, Λ.Res2 k w → (k ∈ ((KK D.κ D.t).res Λ.L).Z2 ↔ w ∈ cechDeRhamTotalCocyclesTwo (OAff D.s)) ∧ ((∃ g, ((KK D.κ D.t).res Λ.L).D1 g = k) ↔ ∃ g, dTot1 (OAff D.s) g = w) := by
  first | exact @GlobalTheory.PDForm.lift_res_bij | exact GlobalTheory.PDForm.lift_res_bij | (intros; apply GlobalTheory.PDForm.lift_res_bij <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFibreExponential_kernel_full_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e → ∃ Λ : Submodule ℤ (Fin g → ℂ), DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ z, e z = 1 ↔ z ∈ Λ := by
  first | exact @GlobalTheory.ExpKernel.kernel_isFullLattice | exact GlobalTheory.ExpKernel.kernel_isFullLattice | (intros; apply GlobalTheory.ExpKernel.kernel_isFullLattice <;> assumption)
end

