import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
import GroundTheory.PAdicHodge.Bundle0010
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import GroundTheory.PAdicHodge.BdRLattice
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelDecomposition
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenUnramifiedCharacterPeriod
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

open GroundTheory.LocalField GroundTheory.PAdicHodge GroundTheory.PAdicHodge.EigenWitt GroundTheory.PAdicHodge.EigenChar

theorem exists_pow_eigenvector_of_unramified_units {l : ℕ} [Fact l.Prime]
    (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E]
    (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ) (hψ : Continuous ψ)
    (hI : ∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) :
    ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
      σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x := by
  have := isSepClosure_padicAlgCl (p := l) (L := E)
  obtain ⟨σ₀, hσ₀⟩ := unramifiedDegree_surjective (K := E) (Ω := PadicAlgCl l)
    (Multiplicative.ofAdd 1)
  set w : ℤ_[l]ˣ := ψ σ₀ with hwdef
  obtain ⟨f, hf, hq⟩ := exists_card_residueField_eq_pow (p := l) (L := E)
  obtain ⟨b, hb, hbσ⟩ := exists_unit_aInf_eigen (K := E) w
  set cA := wittToAInf (b : WittVector l (Fpbar l)) with hcA
  have hcu : IsUnit cA := b.isUnit.map _
  set θ := WittVector.fontaineTheta (normInteger ℂ_[l]) l
  set xc : ℂ_[l] := ((θ cA : normInteger ℂ_[l]) : ℂ_[l]) with hxcdef
  have hxc : xc ≠ 0 := by
    have h1 : θ cA ≠ 0 := (hcu.map θ).ne_zero
    exact fun h => h1 (Subtype.ext h)
  choose z hz using hbσ
  have hxcσ : ∀ σ, σ • xc = algebraMap ℚ_[l] ℂ_[l] (z σ) * xc := fun σ => by
    rw [hxcdef, ← AInf.fontaineTheta_gal_smul, hz σ, map_mul, Subring.coe_mul,
      fontaineTheta_padicIntToWitt]
  have hz₀ : (z σ₀ : ℚ_[l]) = ((w : ℤ_[l]) : ℚ_[l]) ^ f := by
    have h1 := gal_smul_twist_of_degree_one hb hq hσ₀
    rw [← hcA, hz σ₀] at h1
    have h2 := hcu.mul_left_inj.1 h1
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[l]) : ℂ_[l])) h2
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    rw [← PadicInt.coe_pow]
    exact algebraMap_padic_cp_injective h3
  have hzI : ∀ σ, unramifiedDegree E (PadicAlgCl l) σ = 1 → (z σ : ℚ_[l]) = 1 := fun σ hσ => by
    have h1 := gal_smul_twist_of_inertia (b : WittVector l (Fpbar l)) hσ
    rw [← hcA, hz σ] at h1
    have h2 : IsPerfectoidField.padicIntToWitt l (z σ) * cA =
        IsPerfectoidField.padicIntToWitt l 1 * cA := by
      rw [h1, map_one, one_mul]
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[l]) : ℂ_[l])) (hcu.mul_left_inj.1 h2)
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    have := algebraMap_padic_cp_injective h3
    rw [this, PadicInt.coe_one]
  obtain ⟨χ, hχc, hχ⟩ := exists_eigenChar hxc (fun σ => ⟨_, hxcσ σ⟩)
  have hχeq : ∀ σ, ((χ σ : ℚ_[l]ˣ) : ℚ_[l]) = (z σ : ℚ_[l]) := fun σ =>
    eq_of_mul_eq hxc ((hχ σ).symm.trans (hxcσ σ))
  have hψne : ∀ σ, ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) ≠ 0 := fun σ => by
    intro h
    exact (ψ σ).ne_zero (Subtype.ext (h.trans PadicInt.coe_zero.symm))
  let ρC : Gal(PadicAlgCl l/E) →* ℂ_[l] :=
    { toFun := fun σ => algebraMap ℚ_[l] ℂ_[l]
        ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * ((χ σ⁻¹ : ℚ_[l]ˣ) : ℚ_[l]))
      map_one' := by simp
      map_mul' := fun a c => by
        simp only [mul_inv_rev, map_mul, Units.val_mul, PadicInt.coe_mul, mul_pow]
        ring }
  have hρC : Continuous ρC := by
    have hc1 : Continuous fun σ : Gal(PadicAlgCl l/E) => (((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
      have hu : Continuous fun σ : Gal(PadicAlgCl l/E) => ((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) :=
        (Units.continuous_val (M := ℤ_[l])).comp hψ
      exact (continuous_subtype_val : Continuous (fun y : ℤ_[l] => (y : ℚ_[l]))).comp hu
    have hc2 : Continuous fun σ : Gal(PadicAlgCl l/E) => ((χ σ⁻¹ : ℚ_[l]ˣ) : ℚ_[l]) :=
      Units.continuous_val.comp (hχc.comp continuous_inv)
    exact isometry_algebraMap_padic_cp.continuous.comp ((hc1.pow f).mul hc2)
  have hρval : ∀ σ, ρC σ = algebraMap ℚ_[l] ℂ_[l]
      ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * (z σ : ℚ_[l])⁻¹) := fun σ => by
    change algebraMap ℚ_[l] ℂ_[l] _ = _
    rw [map_inv, Units.val_inv_eq_inv_val, hχeq]
  have hall := eq_one_of_degree_one ρC hρC hσ₀
    (by rw [hρval, hz₀, ← hwdef, mul_inv_cancel₀ (pow_ne_zero _ (hψne σ₀)), map_one])
    (fun σ hσ => by rw [hρval, hzI σ hσ, hI σ hσ, Units.val_one, PadicInt.coe_one, one_pow, inv_one,
      mul_one, map_one])
  refine ⟨f, hf, xc, hxc, fun σ => ?_⟩
  have h1 : (((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * (z σ : ℚ_[l])⁻¹ = 1 :=
    algebraMap_padic_cp_injective (by rw [map_one, ← hρval]; exact hall σ)
  have hz0 : (z σ : ℚ_[l]) ≠ 0 := by
    intro h
    rw [h, inv_zero, mul_zero] at h1
    exact zero_ne_one h1
  rw [hxcσ σ, (mul_inv_eq_one₀ hz0).1 h1]

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem hom_eq_zero_of_affineOpens {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (U : X.affineOpens) (s : Γ(M, (U : X.Opens))), φ.app (U : X.Opens) s = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  rw [Scheme.Modules.Hom.zero_app]
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  have key : ∀ s : Γ(M, U), φ.app U s = 0 := by
    intro s
    refine TopCat.Sheaf.eq_of_locally_eq' F
      (fun i : {V : X.affineOpens // (V : X.Opens) ≤ U} => (i.1 : X.Opens)) U
      (fun i => homOfLE i.2) ?_ _ _ ?_
    · refine fun x (hx : x ∈ U) => ?_
      obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    · intro i
      have hnat := ConcreteCategory.congr_hom
        ((Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE i.2).op) s
      simp only [ConcreteCategory.comp_apply] at hnat
      have h2 : N.presheaf.map (homOfLE i.2).op (φ.app U s) = 0 := by
        rw [← h i.1 (M.presheaf.map (homOfLE i.2).op s)]
        exact hnat.symm
      exact h2.trans (map_zero _).symm
  ext s
  simp [key s]

theorem le_iff_secs_subset {X : Scheme.{0}} {E : X.Modules} (S T : Subobject E) :
    S ≤ T ↔ ∀ U : X.affineOpens, secs S (U : X.Opens) ⊆ secs T (U : X.Opens) := by
  unfold GlobalTheory.CompanionTheory.GE.secs
  constructor
  · intro hST U x hx
    obtain ⟨s, rfl⟩ := hx
    refine ⟨(Subobject.ofLE S T hST).app (U : X.Opens) s, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.ofLE_arrow]
  · intro h
    have hzero : S.arrow ≫ cokernel.π T.arrow = 0 := by
      apply GlobalTheory.CompanionTheory.GE.hom_eq_zero_of_affineOpens
      intro U s
      obtain ⟨t, ht⟩ := h U (Set.mem_range_self s)
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ← ht,
        ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition,
        Scheme.Modules.Hom.zero_app, AddCommGrpCat.zero_apply]
    exact Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow hzero)
      (Abelian.monoLift_comp _ _ _)

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNearPowerExists
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.TopNil

theorem exists_thB_wB {l : ℕ} [Fact l.Prime] (y : ℂ_[l]) (hy : ‖y‖ ≤ 1) :
    ∃ a, thB l (wB l a) = y := by
  obtain ⟨a, ha⟩ := GroundTheory.PAdicHodge.IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l
    ⟨y, GroundTheory.PAdicHodge.mem_normInteger.2 hy⟩
  refine ⟨a, ?_⟩
  have h := GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus
    (K := ℂ_[l]) l a
  rw [ha] at h
  exact h

theorem near_tch_pow {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)) (hS : ∀ a, wB l a ∈ S)
    (ϖ : Formalism.Per6.BdRp l) (hϖ : thB l ϖ ≠ 0) (x : Tl l) (hx : ‖thB l (tch l x)‖ < 1) :
    ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (tch l x ^ M) := by
  set c : ℂ_[l] := thB l (tch l x) with hc
  have hpos : 0 < ‖thB l ϖ‖ := norm_pos_iff.2 hϖ
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hx
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  have hle : ‖c‖ ^ (N + 1) ≤ ‖thB l ϖ‖ := by
    rw [pow_succ]
    calc ‖c‖ ^ N * ‖c‖ ≤ ‖c‖ ^ N * 1 :=
          mul_le_mul_of_nonneg_left hx.le (pow_nonneg (norm_nonneg _) _)
      _ = ‖c‖ ^ N := mul_one _
      _ ≤ ‖thB l ϖ‖ := hN.le
  have hy : ‖c ^ (N + 1) / thB l ϖ‖ ≤ 1 := by
    rw [norm_div, norm_pow, div_le_one hpos]
    exact hle
  obtain ⟨a, ha⟩ := exists_thB_wB _ hy
  refine ⟨wB l a, hS a, ?_⟩
  rw [pow_one, FB, pow_one, RingHom.mem_ker, map_sub, map_pow, map_mul, ha, ← hc]
  field_simp
  simp

theorem main : ∀ {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)), (∀ a, wB l a ∈ S) →
    ∀ (ϖ : Formalism.Per6.BdRp l), thB l ϖ ≠ 0 → ∀ x : Tl l, ‖thB l (tch l x)‖ < 1 →
      ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (tch l x ^ M) :=
  fun S hS ϖ hϖ x hx => near_tch_pow S hS ϖ hϖ x hx

end GlobalTheory.CompanionTheory.LTPer.TopNil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPropertiesResidue
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem uniformiser_facts : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    2 ≤ qOf π ∧ l ∣ qOf π ∧ π ∣ (l : ↥(OL K)) ∧
      ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 ∧ ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
  intro l _ K π hπ
  obtain ⟨⟨⟨hD, hV, -⟩, -⟩, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l K
  have hlp : l.Prime := Fact.out
  have hi : Algebra.IsIntegral ℤ_[l] ↥(OL K) := integralClosure.AlgebraIsIntegral
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL K)) := by
    intro a b hab
    have h1 : algebraMap ℤ_[l] ↥K.1 a = algebraMap ℤ_[l] ↥K.1 b := congrArg Subtype.val hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1 b] at h1
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] ↥K.1).injective h1)
  have hf : FaithfulSMul ℤ_[l] ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hl : ¬ IsUnit ((l : ℕ) : ↥(OL K)) := by
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] ↥(OL K))] at hu
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_map_unit _ _ hu)
  have hdvd : π ∣ ((l : ℕ) : ↥(OL K)) := by
    have hm : ((l : ℕ) : ↥(OL K)) ∈ IsLocalRing.maximalIdeal ↥(OL K) := hl
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have hle : Ideal.span {((l : ℕ) : ↥(OL K)) ^ 1} ≤ Ideal.span {π} := by
    rw [pow_one, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hfinQ : Finite (↥(OL K) ⧸ Ideal.span {π}) := by
    have := hfin 1
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have hnt : Nontrivial (↥(OL K) ⧸ Ideal.span {π}) := by
    refine Ideal.Quotient.nontrivial_iff.2 ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hπ.not_isUnit
  have h2 : 2 ≤ qOf π := Finite.one_lt_card
  have hord : addOrderOf (1 : ↥(OL K) ⧸ Ideal.span {π}) = l := by
    have h1 : (1 : ↥(OL K) ⧸ Ideal.span {π}) ≠ 0 := by
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {π})), Ne, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
    refine addOrderOf_eq_prime ?_ h1
    rw [nsmul_one, ← map_natCast (Ideal.Quotient.mk (Ideal.span {π})),
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hq : l ∣ qOf π := by
    have := addOrderOf_dvd_natCard (1 : ↥(OL K) ⧸ Ideal.span {π})
    rwa [hord] at this
  have hl0 : ((l : ℕ) : ↥(OL K)) ≠ 0 := by
    intro h
    have h2 := congrArg (fun x : ↥(OL K) => (x : ↥K.1)) h
    simp only [ZeroMemClass.coe_zero, SubringClass.coe_natCast] at h2
    exact hlp.ne_zero (by exact_mod_cast h2)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hπ
  have he : e ≠ 0 := by
    rintro rfl
    apply hl
    rw [pow_zero] at hu
    exact IsUnit.of_mul_eq_one _ hu
  have hnorm : ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
    intro μ
    rw [PadicComplex.norm_extends]
    have hint : ∀ x : ↥(OL K), ‖μ (x : ↥K.1)‖ ≤ 1 := by
      intro x
      rw [← GlobalTheory.isIntegral_padicInt_iff_norm_le_one]
      exact (x.2 : IsIntegral ℤ_[l] (x : ↥K.1)).map (μ.restrictScalars ℤ_[l])
    have hpow : (π : ↥K.1) ^ e = (l : ↥K.1) * ((u : ↥(OL K)) : ↥K.1) := by
      have := congrArg (fun x : ↥(OL K) => (x : ↥K.1)) hu
      simpa using this.symm
    have h3 : ‖μ (π : ↥K.1)‖ ^ e < 1 := by
      rw [← norm_pow, ← map_pow, hpow, map_mul, norm_mul, map_natCast,
        ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) Padic.norm_p_lt_one (hint _)
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 h3
  exact ⟨h2, hq, hdvd, hnorm K.1.val, hnorm⟩

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WBMemLatS
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

def latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) : Subring (Formalism.Per6.BdRp l) :=
  Subring.closure (Set.range (wB l) ∪ (rB l) '' {x | x ∈ K' ∧ IsIntegral ℤ_[l] x})

theorem wB_mem_latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) (a : Wl l) :
    wB l a ∈ latS K' :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem rB_mem_latS {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) {x : Om l}
    (hx : x ∈ K') (hi : IsIntegral ℤ_[l] x) : rB l x ∈ latS K' :=
  Subring.subset_closure (Or.inr ⟨x, ⟨hx, hi⟩, rfl⟩)

theorem ker_thB_eq {l : ℕ} [Fact l.Prime] :
    RingHom.ker (thB l) = IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) :=
  (GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l)).symm

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelDecompositionStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_kernel_decomposition : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → KerOne → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E w g k → ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)) (K : Fin N → Mat n → (E.V →L[ℂ] E.V)), (∀ i, IsKer μ E (w₁ i) g (K i)) ∧ (haveI := FiniteDimensional.complete ℂ E.V; ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) = ∑ i, c i • K i y) ∧ ∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.KerAdj.kernel_adjoint | exact GlobalTheory.CompanionTheory.WaveMult.KerAdj.kernel_adjoint | (intros; apply GlobalTheory.CompanionTheory.WaveMult.KerAdj.kernel_adjoint <;> assumption)
end

