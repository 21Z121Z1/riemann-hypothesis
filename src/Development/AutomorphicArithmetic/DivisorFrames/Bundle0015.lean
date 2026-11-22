import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsInvariantPosDefHermitianFormAutFormUnitary
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory in
theorem UpperTheory.exists_invariant_posDef_hermitian_form_autForm_unitary :
    ∀ (D : D7) [IsCMField D.host.E] (V : HSp D), V.SigOK → V.IsPosDef → ∀ (j : UA D.host.E V.rank ≃ₜ* GA D V),
        (∀ x, x ∈ ratU D.host.E V.rank ↔ j x ∈ GQ V) →
        ∃ B : (UA D.host.E V.rank → ℂ) →ₗ⋆[ℂ] (UA D.host.E V.rank → ℂ) →ₗ[ℂ] ℂ, (∀ φ, IsAutFormU φ → φ ≠ 0 → 0 < (B φ φ).re) ∧
          ∀ k ∈ finU D.host.E V.rank, ∀ φ ψ, IsAutFormU φ → IsAutFormU ψ →
            B (RU D.host.E V.rank k φ) (RU D.host.E V.rank k ψ) = B φ ψ := by
  intro D _ V hs hp j hj
  classical
  obtain ⟨h1, h2, h3, h4, h5, _h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (GA D V), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨hR, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact V (fun τ => GlobalTheory.RepsObj.gramAt_posDef hp hs τ)

  let N : Submodule ℂ (UA D.host.E V.rank → ℂ) :=
    { carrier := {φ | Continuous φ ∧ ∀ γ ∈ ratU D.host.E V.rank, ∀ g, φ (γ * g) = φ g}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun γ hγ g => by simp [ha.2 γ hγ g, hb.2 γ hγ g]⟩
      zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun γ hγ g => by simp [ha.2 γ hγ g]⟩ }
  have hAN : ∀ φ, IsAutFormU φ → φ ∈ N := fun φ h => ⟨h.cont, h.left⟩
  have hRN : ∀ k, ∀ φ ∈ N, RU D.host.E V.rank k φ ∈ N := by
    intro k φ h
    refine ⟨h.1.comp (continuous_mul_const k), fun γ hγ g => ?_⟩
    show φ (γ * g * k) = φ (g * k)
    rw [mul_assoc, h.2 γ hγ]
  have hLC : ∀ x ∈ N, Continuous (fun g => x (j.symm g)) ∧
      ∀ γ ∈ GQ V, ∀ g, x (j.symm (γ * g)) = x (j.symm g) := by
    intro x hx
    refine ⟨hx.1.comp j.symm.continuous, fun γ hγ g => ?_⟩
    rw [map_mul]
    exact hx.2 _ ((hj _).2 (by rwa [j.apply_symm_apply])) _
  have hI : ∀ x ∈ N, ∀ y ∈ N, IntegrableOn (fun g => star (x (j.symm g)) * y (j.symm g)) 𝓕 μ := by
    intro x hx y hy
    exact GlobalTheory.MultPetersson.integrableOn_star_mul μ 𝓕 C hμ h𝓕 hC hcov (hLC x hx).1 (hLC y hy).1 (hLC x hx).2
      (hLC y hy).2
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl N
  let P : (UA D.host.E V.rank → ℂ) →ₗ[ℂ] N := Submodule.projectionOnto N q hq
  have hPN : ∀ T, ((P T : N) : UA D.host.E V.rank → ℂ) ∈ N := fun T => (P T).2
  have hPid : ∀ T ∈ N, ((P T : N) : UA D.host.E V.rank → ℂ) = T := fun T hT =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨T, hT⟩)
  let F : (UA D.host.E V.rank → ℂ) → (UA D.host.E V.rank → ℂ) → ℂ := fun x y =>
    ∫ g in 𝓕, star ((P x).1 (j.symm g)) * (P y).1 (j.symm g) ∂μ
  let B : (UA D.host.E V.rank → ℂ) →ₗ⋆[ℂ] (UA D.host.E V.rank → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F
    (fun x x' y => by
      simp only [F, map_add, Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x') _ (hPN y))]
      congr 1
      funext g
      simp only [Pi.add_apply, star_add, add_mul])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply]
      ring)
    (fun x y y' => by
      simp only [F, map_add, Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x) _ (hPN y'))]
      congr 1
      funext g
      simp only [Pi.add_apply, mul_add])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring)
  have hB : ∀ x ∈ N, ∀ y ∈ N, B x y = ∫ g in 𝓕, star (x (j.symm g)) * y (j.symm g) ∂μ := by
    intro x hx y hy
    show F x y = _
    simp only [F, hPid x hx, hPid y hy]
  refine ⟨B, ?_, ?_⟩
  · intro T hT' h0
    have hT := hAN T hT'
    rw [hB _ hT _ hT]
    have hre : ∫ g in 𝓕, star (T (j.symm g)) * T (j.symm g) ∂μ = ((∫ g in 𝓕, ‖T (j.symm g)‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext g
      rw [Complex.star_def, Complex.conj_mul']
      push_cast
      rfl
    rw [hre, Complex.ofReal_re]
    have hnn : 0 ≤ ∫ g in 𝓕, ‖T (j.symm g)‖ ^ 2 ∂μ := integral_nonneg fun g => by positivity
    refine lt_of_le_of_ne hnn fun hz => h0 ?_
    have hi : IntegrableOn (fun g => ‖T (j.symm g)‖ ^ 2) 𝓕 μ := by
      have := (hI T hT T hT).norm
      have e2 : (fun g => ‖star (T (j.symm g)) * T (j.symm g)‖) = fun g => ‖T (j.symm g)‖ ^ 2 := by
        funext g
        rw [norm_mul, norm_star, sq]
      rw [e2] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi).1 hz.symm
    have := GlobalTheory.SchurConst.eq_zero_of_ae μ 𝓕 hμ h𝓕 (fun g => T (j.symm g)) (hLC T hT).1 (hLC T hT).2 (by
      filter_upwards [hae] with g hg
      simpa using hg)
    funext x
    have h := congrFun this (j x)
    simpa using h
  · intro k _hk T T' hT0 hT0'
    have hT := hAN T hT0
    have hT' := hAN T' hT0'
    rw [hB _ (hRN k T hT) _ (hRN k T' hT'), hB _ hT _ hT']
    haveI := h5
    haveI := h4
    haveI := h2
    haveI := h7
    haveI := hR
    have hmap : Measure.map (fun g => g * j k) μ = μ := map_mul_right_eq_self μ (j k)
    have hh : ∀ x : UA D.host.E V.rank → ℂ, ∀ g, RU D.host.E V.rank k x (j.symm g) = x (j.symm (g * j k)) := by
      intro x g
      rw [map_mul, j.symm_apply_apply]
      rfl
    simp only [hh]
    have hinv : ∀ γ ∈ GQ V, ∀ g, (fun g => star (T (j.symm g)) * T' (j.symm g)) (γ * g) =
        (fun g => star (T (j.symm g)) * T' (j.symm g)) g := by
      intro γ hγ g
      simp only [(hLC T hT).2 γ hγ, (hLC T' hT').2 γ hγ]
    exact (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 (j k) hmap _ hinv (hI T hT T' hT')).2
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalNablaTAndContinuousWtOp
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

private theorem fd_dw (n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) := by
  obtain ⟨b, ⟨-, hb, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ n n ν
  have : Finite (Formalism.GradedWeylDivisibility.ssIdx n n ν) := (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  rw [← hb]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range b)

private theorem cont_rowAct (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    ∀ ℓ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      Continuous fun g : Matrix (Fin n) (Fin n) ℂ => ℓ (Formalism.GradedWeylDivisibility.rowAct ℂ g f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro ℓ
    simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.algHom_C]
    exact continuous_const
  | add p q hp hq =>
    intro ℓ
    simp only [map_add]
    exact (hp ℓ).add (hq ℓ)
  | mul_X p v hp =>
    intro ℓ
    have e : ∀ g : Matrix (Fin n) (Fin n) ℂ, ℓ (Formalism.GradedWeylDivisibility.rowAct ℂ g (p * MvPolynomial.X v)) =
        ∑ b : Fin n, g v.1 b * (ℓ ∘ₗ LinearMap.mulRight ℂ (MvPolynomial.X (b, v.2))) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) := by
      intro g
      have h1 : Formalism.GradedWeylDivisibility.rowAct ℂ g (MvPolynomial.X v : MvPolynomial (Fin n × Fin n) ℂ) =
          ∑ b : Fin n, MvPolynomial.C (g v.1 b) * MvPolynomial.X (b, v.2) := by
        simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, h1, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
      rfl
    simp only [e]
    refine continuous_finset_sum _ fun b _ => ?_
    exact (continuous_id.matrix_elem v.1 b).mul (hp _)

private theorem cont_rep (n : ℕ) (ν : Fin n → ℕ) (ℓ : Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ)
    (u : Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) :
    Continuous fun g : GL (Fin n) ℂ => ℓ (Formalism.UG.dualWeylRep ℂ n n ν g u) := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend ℓ
  have e : ∀ g : GL (Fin n) ℂ, ℓ (Formalism.UG.dualWeylRep ℂ n n ν g u) =
      L (Formalism.GradedWeylDivisibility.rowAct ℂ ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ)) := by
    intro g
    rw [← hL, LinearMap.comp_apply, Submodule.subtype_apply, Formalism.UG.dualWeylRep_apply]
    rfl
  simp only [e]
  exact (cont_rowAct n _ L).comp Units.continuous_coe_inv

private theorem cont_multi {X ι : Type} [TopologicalSpace X] [Fintype ι] [DecidableEq ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (m : MultilinearMap ℂ V ℂ) (F : ∀ i, X → V i) (hF : ∀ i (ℓ : V i →ₗ[ℂ] ℂ), Continuous fun x => ℓ (F i x)) :
    Continuous fun x => m fun i => F i x := by
  let b := fun i => Module.finBasis ℂ (V i)
  have e : ∀ x, (m fun i => F i x) = ∑ r : ∀ i, Fin (Module.finrank ℂ (V i)),
      (∏ i, (b i).coord (r i) (F i x)) • m fun i => b i (r i) := by
    intro x
    have h1 : (fun i => F i x) = fun i => ∑ j, (b i).coord j (F i x) • b i j := by
      funext i
      simp only [Module.Basis.coord_apply, Module.Basis.sum_repr]
    rw [h1, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
  simp only [e]
  refine continuous_finset_sum _ fun r _ => ?_
  exact (continuous_finset_prod _ fun i _ => hF i _).smul continuous_const

theorem UpperTheory.finiteDimensional_nablaT_and_continuous_wtOp :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ),
        FiniteDimensional ℂ (NablaT ℂ n mu) ∧ ∀ (ℓ : NablaT ℂ n mu →ₗ[ℂ] ℂ) (u : NablaT ℂ n mu),
          Continuous fun g : ι → GL (Fin n) ℂ => ℓ (wtOp ℂ n mu sh g u) := by
  intro n ι _ _ mu sh
  haveI : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) := fun τ => fd_dw n _
  refine ⟨Module.Finite.of_basis (Basis.piTensorProduct fun τ => Module.finBasis ℂ _), fun ℓ u => ?_⟩
  have h1 : Continuous fun g : ι → GL (Fin n) ℂ => ℓ (GlobalTheory.ExpFrame.grp ℂ n mu g u) := by
    induction u using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [map_smul, GlobalTheory.SemilinTransport.grp_tprod]
      refine Continuous.const_smul ?_ c
      exact cont_multi (ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ))
        (fun τ (g : ι → GL (Fin n) ℂ) => Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ))
        (fun τ l => (cont_rep n _ l (x τ)).comp (continuous_apply τ))
    | add a b ha hb =>
      simp only [map_add]
      exact ha.add hb
  simp only [wtOp_apply, map_smul]
  have h2 : Continuous fun g : ι → GL (Fin n) ℂ =>
      (∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) := by
    refine continuous_finset_prod _ fun τ _ => ?_
    refine Continuous.zpow ?_ _
    exact Matrix.GeneralLinearGroup.continuous_det.comp (continuous_apply τ)
  exact (Units.continuous_val.comp h2).smul h1
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.IsAutFormUOfVectorValuedInvariant
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

theorem UpperTheory.isAutFormU_of_vectorValued_invariant :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (R : UA E n →* Module.End ℂ M),
        (∀ k ∈ finU E n, R k = 1) → (∀ (ℓ : M →ₗ[ℂ] ℂ) (u : M), Continuous fun g => ℓ (R g u)) →
        ∀ F1 : UA E n → M, (∀ γ ∈ ratU E n, ∀ g, F1 (γ * g) = R γ (F1 g)) → (∀ x ∈ infU E n, ∀ g, F1 (g * x) = F1 g) →
        (∀ᶠ y in nhds (1 : UA E n), ∀ g, F1 (g * y) = F1 g) → ∀ ℓ : M →ₗ[ℂ] ℂ, IsAutFormU fun g => ℓ (R g⁻¹ (F1 g)) := by
  intro E _ _ _ n M _ _ _ R hfin hcont F1 hrat hinf hev ℓ
  have hRU : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro g₀
    have h1 : Continuous fun g : UA E n => ℓ (R g⁻¹ (F1 g₀)) := (hcont ℓ (F1 g₀)).comp continuous_inv
    refine h1.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA E n => g₀⁻¹ * g) (nhds g₀) (nhds 1) := by
      have : Continuous fun g : UA E n => g₀⁻¹ * g := continuous_const.mul continuous_id
      have h2 := this.tendsto g₀
      rwa [inv_mul_cancel] at h2
    filter_upwards [ht.eventually hev] with g hg
    have := hg g₀
    rw [mul_inv_cancel_left] at this
    rw [this]
  · intro γ hγ g
    rw [hrat γ hγ g, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  · set φ : UA E n → ℂ := fun g => ℓ (R g⁻¹ (F1 g)) with hφ
    let S : Subgroup (finU E n) :=
      { carrier := {k : finU E n | RU E n k φ = φ}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    refine S.isOpen_of_mem_nhds (g := 1) ?_
    have ht : Filter.Tendsto (fun k : finU E n => (k : UA E n)) (nhds 1) (nhds 1) :=
      continuous_subtype_val.tendsto (1 : finU E n)
    filter_upwards [ht.eventually hev] with k hk
    show RU E n k φ = φ
    funext g
    rw [hRU]
    simp only [hφ]
    rw [hk g, mul_inv_rev, map_mul, hfin _ ((finU E n).inv_mem k.2), one_mul]
  · let L : (M →ₗ[ℂ] ℂ) →ₗ[ℂ] (UA E n → ℂ) :=
      { toFun := fun ℓ' g => ℓ' (R g⁻¹ (F1 g))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨ℓ ∘ₗ R (k : UA E n)⁻¹, ?_⟩
    funext g
    show ℓ (R (k : UA E n)⁻¹ (R g⁻¹ (F1 g))) = RU E n k _ g
    rw [hRU, hinf _ k.2 g, mul_inv_rev, map_mul, Module.End.mul_apply]
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.LevChiEqOneOfGoodPlace
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.hecke_offprime_preimage {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hβ : ∃ c : ℕ, Formalism.IndefR.Lev.IsBaseFrame V β Λ (1 ^ c)) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ v ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP v) :
    ∀ k ∈ GlobalTheory.Hk3.hyp V v, ∃ h : (Formalism.L2.Theta.finHom V).rangeRestrict k ∈ (levEnv V β L).J,
      (levEnv V β L).χ ⟨_, h⟩ = 1 := by
  refine hβ.elim fun c hc => ?_
  have hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (Formalism.IndefR.Lev.flag1L L) hc').2 v e f' he h1 hoff
  rintro a ⟨ha, e, f', he, hs⟩
  have hm := ((hl e f' he).1 a hs).2 ha
  exact ⟨hm.2, Units.ext ((hl e f' he).2.1 a hm hs)⟩

theorem UpperTheory.levChi_eq_one_of_good_place :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (v : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good p.R.toRealDat t v →
        ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D j) v, ∃ h : (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k ∈ levJ p j t, levChi p j t ⟨_, h⟩ = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t v hv
  exact UpperTheory.hecke_offprime_preimage (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) (p.charW.base.lev.βV j) v hv
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.VectorValuedAutFormEquivariantInfiniteComponent
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.infinite_matrix_rational {D : D7} {V : HSp D}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (h : GA D V) (γ₀ : GL (Fin V.rank) D.host.E)
    (e : matHom V h = Matrix.GeneralLinearGroup.map (incA D) γ₀) (τ : D.what₂.Tau) :
    Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) h =
      (Matrix.GeneralLinearGroup.map (tauE D τ) γ₀ : GL (Fin V.rank) ℂ).val := by
  have e' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat _ D.sp.cm.sig V.gram h = Matrix.GeneralLinearGroup.map (incA D) γ₀ := e
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [e']
  ext a b
  change θ τ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] γ₀.val a b)) = tauE D τ (γ₀.val a b)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  exact (hθ τ).1 _

private theorem UpperTheory.exists_conjugate_embedding {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (σ ε : E →+* ℂ)
    (hε : ε = σ ∨ ε = ComplexEmbedding.conjugate σ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ∃ B : GL (Fin n) ℂ, ∀ (x : UA E n) (γ₀ : GL (Fin n) E),
      (Matrix.GeneralLinearGroup.map σ γ₀ : GL (Fin n) ℂ).val = A * (cEmb σ x : Matrix (Fin n) (Fin n) ℂ) * A⁻¹ →
      Matrix.GeneralLinearGroup.map ε γ₀ = B * cEmb ε x * B⁻¹ := by
  obtain ⟨B, rfl⟩ := hA
  have key : ∀ (x : UA E n) (γ₀ : GL (Fin n) E),
      (Matrix.GeneralLinearGroup.map σ γ₀ : GL (Fin n) ℂ).val =
        B.val * (cEmb σ x : Matrix (Fin n) (Fin n) ℂ) * (B.val)⁻¹ →
      Matrix.GeneralLinearGroup.map σ γ₀ = B * cEmb σ x * B⁻¹ := fun x γ₀ h => by
    apply Units.ext
    rw [h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  rcases hε with rfl | rfl
  · exact ⟨B, key⟩
  · refine ⟨Matrix.GeneralLinearGroup.map (starRingEnd ℂ) B, fun x γ₀ h => ?_⟩
    have h1 := congrArg (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) (key x γ₀ h)
    rw [map_mul, map_mul, map_inv] at h1
    have h2 : Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (cEmb σ x) = cEmb (ComplexEmbedding.conjugate σ) x := by
      ext a b
      exact (GlobalTheory.DefiniteBC.coord_conjugate σ _).symm
    rw [h2] at h1
    rw [← h1]
    ext a b
    rfl

private theorem UpperTheory.weight_operator_conjugate {n : ℕ} {ι : Type} [Fintype ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)
    (B C G : ι → GL (Fin n) ℂ) (h : G = B * C * B⁻¹) (u : NablaT ℂ n mu) :
    wtOp ℂ n mu sh B⁻¹ (wtOp ℂ n mu sh G u) = wtOp ℂ n mu sh C (wtOp ℂ n mu sh B⁻¹ u) := by
  classical
  rw [h, ← Module.End.mul_apply, ← wtOp_mul, ← mul_assoc, inv_mul_cancel_left, wtOp_mul]
  rfl

private theorem UpperTheory.monoidHom_kernel_invariance {G H K : Type} [Monoid G] [Monoid H] [Monoid K] (j : G →* H) (φ : H →* K)
    (g x : G) (h : H) (hx : φ (j x) = 1) : φ (j (g * x) * h) = φ (j g * h) := by
  simp only [map_mul, hx, mul_one]

theorem UpperTheory.vectorValued_autForm_equivariant_infinite_component :
    ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
        (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V), IsInfFam θ → GlobalTheory.DefTransfer.IsTransfer V θ j h₀ →
        ∀ (emb : D.what₂.Tau → (D.host.E →+* ℂ)), (∀ τ, emb τ = tauE D τ ∨ emb τ = ComplexEmbedding.conjugate (tauE D τ)) →
        ∀ (mu : D.what₂.Tau → ℕ → ℕ) (sh : D.what₂.Tau → ℤ) (Fm : Bridge.Gf V → NablaT ℂ V.rank mu), Fm ≠ 0 →
        (∀ (γ : GQ V) (γ₀ : GL (Fin V.rank) D.host.E), matHom V γ = Matrix.GeneralLinearGroup.map (incA D) γ₀ → ∀ g,
          Fm (Bridge.ratF V γ * g) = wtOp ℂ V.rank mu sh (fun τ => Matrix.GeneralLinearGroup.map (emb τ) γ₀) (Fm g)) →
        (∀ᶠ κ in nhds (1 : GA D V), ∀ g, Fm (g * (finHom V).rangeRestrict κ) = Fm g) →
        ∃ F1 : UA D.host.E V.rank → NablaT ℂ V.rank mu, F1 ≠ 0 ∧
          (∀ γ ∈ ratU D.host.E V.rank, ∀ g, F1 (γ * g) = wtOp ℂ V.rank mu sh (fun τ => cEmb (emb τ) γ) (F1 g)) ∧
          (∀ x ∈ infU D.host.E V.rank, ∀ g, F1 (g * x) = F1 g) ∧ (∀ᶠ y in nhds (1 : UA D.host.E V.rank), ∀ g, F1 (g * y) = F1 g) ∧
          ∃ A : Module.End ℂ (NablaT ℂ V.rank mu), ∀ x, F1 x = A (Fm ((finHom V).rangeRestrict (j x * h₀))) := by
  intro D _ V θ j h₀ hθ hT emb hemb mu sh Fm hF hrat hlev
  classical
  obtain ⟨-, hQ, -, hI, ⟨A, hA, hAe⟩, -⟩ := hT
  choose B hB using fun τ => UpperTheory.exists_conjugate_embedding (tauE D τ) (emb τ) (hemb τ) (A τ) (hA τ)
  refine ⟨fun x => wtOp ℂ V.rank mu sh B⁻¹ (Fm ((finHom V).rangeRestrict (j x * h₀))), ?_, ?_, ?_, ?_, _, fun _ => rfl⟩
  · intro h0
    apply hF
    funext g
    obtain ⟨k, rfl⟩ := (finHom V).rangeRestrict_surjective g
    have h1 := congrArg (wtOp ℂ V.rank mu sh B) (congrFun h0 (j.symm (k * h₀⁻¹)))
    simp only [ContinuousMulEquiv.apply_symm_apply, inv_mul_cancel_right, Pi.zero_apply, map_zero] at h1
    rw [← Module.End.mul_apply, ← wtOp_mul, mul_inv_cancel, wtOp_one] at h1
    exact h1
  · intro γ hγ g
    have hj : j γ ∈ GQ V := (hQ γ).1 hγ
    obtain ⟨γ₀, -, e⟩ := id hj
    have e' : matHom V (j γ) = Matrix.GeneralLinearGroup.map (incA D) γ₀ := e.symm
    have h1 := hrat ⟨j γ, hj⟩ γ₀ e' ((finHom V).rangeRestrict (j g * h₀))
    have h2 : (finHom V).rangeRestrict (j (γ * g) * h₀) =
        Bridge.ratF V ⟨j γ, hj⟩ * (finHom V).rangeRestrict (j g * h₀) := by
      have h4 : j (γ * g) * h₀ = j γ * (j g * h₀) := by rw [map_mul, mul_assoc]
      exact (congrArg (finHom V).rangeRestrict h4).trans (map_mul (finHom V).rangeRestrict _ _)
    have h3 : (fun τ => Matrix.GeneralLinearGroup.map (emb τ) γ₀) = B * (fun τ => cEmb (emb τ) γ) * B⁻¹ := by
      funext τ
      exact hB τ γ γ₀ ((UpperTheory.infinite_matrix_rational θ hθ _ γ₀ e' τ).symm.trans (hAe τ γ))
    exact (congrArg (wtOp ℂ V.rank mu sh B⁻¹) ((congrArg Fm h2).trans h1)).trans
      (UpperTheory.weight_operator_conjugate mu sh B _ _ h3 _)
  · intro x hx g
    have hj : finHom V (j x) = 1 := (hI x).1 hx
    have h1 : (finHom V).rangeRestrict (j x) = 1 := Subtype.ext hj
    exact congrArg (fun z => wtOp ℂ V.rank mu sh B⁻¹ (Fm z))
      (UpperTheory.monoidHom_kernel_invariance j.toMulEquiv.toMonoidHom (finHom V).rangeRestrict g x h₀ h1)
  · have hc : Continuous fun y : UA D.host.E V.rank => h₀⁻¹ * j y * h₀ :=
      (continuous_const.mul j.continuous).mul continuous_const
    have ht : Filter.Tendsto (fun y : UA D.host.E V.rank => h₀⁻¹ * j y * h₀) (nhds 1) (nhds 1) := by
      exact hc.tendsto' 1 1 (by simp only [map_one, mul_one, inv_mul_cancel])
    filter_upwards [ht.eventually hlev] with y hy g
    have h1 : j (g * y) * h₀ = j g * h₀ * (h₀⁻¹ * j y * h₀) := by
      rw [map_mul]
      group
    exact congrArg (wtOp ℂ V.rank mu sh B⁻¹) ((congrArg Fm ((congrArg (finHom V).rangeRestrict h1).trans
      (map_mul (finHom V).rangeRestrict _ _))).trans (hy _))
end

