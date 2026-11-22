import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import GroundTheory.GlobalFields.TateThesis.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightSpacesSpan
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RealCount.TorusSpan

open PositivityTheory.RgBcC Module.End

variable {n : ℕ}

theorem diag_mem (t : Fin n → Circle) :
    diagonal (fun a => (t a : ℂ)) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  simp [Complex.mul_conj]

def torus : (Fin n → Circle) →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun t := ⟨diagonal fun a => (t a : ℂ), diag_mem t⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp [diagonal_mul_diagonal])

theorem continuous_torus : Continuous (torus (n := n)) := by
  apply Continuous.subtype_mk
  apply Continuous.matrix_diagonal
  exact continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)

variable (E : KMod n)

theorem inner_rho (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : E.V) : ⟪E.ρ k x, E.ρ k y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩ : E.V →ₗᵢ[ℂ] E.V).inner_map_map x y

theorem rho_inv_apply (k : Matrix.unitaryGroup (Fin n) ℂ) (y : E.V) : E.ρ k (E.ρ k⁻¹ y) = y := by
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]

theorem inner_rho_left (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : E.V) :
    ⟪E.ρ k x, y⟫_ℂ = ⟪x, E.ρ k⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← rho_inv_apply E k y]
  exact inner_rho E k x _

end GlobalTheory.CompanionTheory.RealCount.TorusSpan

namespace GlobalTheory.CompanionTheory.RealCount.TorusSpan

open PositivityTheory.RgBcC Module.End

theorem jointEig_top {V I : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (T : I → V →ₗ[ℂ] V) (hc : ∀ i k, Commute (T i) (T k))
    (hadj : ∀ i, ∃ k, ∀ x y, ⟪T i x, y⟫_ℂ = ⟪x, T k y⟫_ℂ) :
    ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) = ⊤ := by
  choose s hs using hadj
  have hs' : ∀ i x y, ⟪T (s i) x, y⟫_ℂ = ⟪x, T i y⟫_ℂ := fun i x y => by
    rw [← inner_conj_symm, ← hs, inner_conj_symm]
  let H : I ⊕ I → V →ₗ[ℂ] V := Sum.elim (fun i => T i + T (s i)) (fun i => Complex.I • (T i - T (s i)))
  have hH : ∀ i, (H i).IsSymmetric := by
    rintro (i | i) x y
    · simp only [H, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right, hs i, hs' i]
      ring
    · simp only [H, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, hs i, hs' i, Complex.conj_I]
      ring
  have hT : ∀ i k, Commute (H i) (T k) := by
    rintro (i | i) k
    · exact (hc _ _).add_left (hc _ _)
    · exact ((hc _ _).sub_left (hc _ _)).smul_left _
  have hHc : ∀ i k, Commute (H i) (H k) := by
    rintro i (k | k)
    · exact (hT _ _).add_right (hT _ _)
    · exact ((hT _ _).sub_right (hT _ _)).smul_right _
  have h := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hH (fun i k _ => hHc i k)
  rw [eq_top_iff, ← h]
  refine iSup_le fun χ => le_iSup_of_le (fun i => (χ (.inl i) - Complex.I * χ (.inr i)) / 2) fun x hx => ?_
  simp only [Submodule.mem_iInf, mem_eigenspace_iff] at hx ⊢
  intro i
  have h1 : T i x + T (s i) x = χ (.inl i) • x := hx (.inl i)
  have h2 : Complex.I • (T i x - T (s i) x) = χ (.inr i) • x := hx (.inr i)
  have h3 : T i x - T (s i) x = -(Complex.I * χ (.inr i)) • x := by
    rw [neg_smul, mul_smul, ← h2, smul_smul, Complex.I_mul_I]; simp
  have h4 : (2 : ℂ) • T i x = (χ (.inl i) - Complex.I * χ (.inr i)) • x := by
    rw [sub_eq_add_neg, add_smul, ← h1, ← h3, two_smul]; abel
  rw [div_eq_inv_mul, mul_smul, ← h4, smul_smul]; simp

variable {n : ℕ} (E : KMod n)

def rhoT (t : Fin n → Circle) : E.V →ₗ[ℂ] E.V := ((E.ρ (torus t) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V)

theorem span_V : ⨆ χ : (Fin n → Circle) → ℂ, ⨅ t, eigenspace (rhoT E t) (χ t) = ⊤ := by
  apply jointEig_top
  · intro s t
    have h : torus s * torus t = torus t * torus s := by rw [← map_mul, ← map_mul, mul_comm]
    refine LinearMap.ext fun x => ?_
    simp only [rhoT, Module.End.mul_apply, ContinuousLinearMap.coe_coe]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, h, map_mul, ContinuousLinearMap.mul_apply]
  · intro t
    refine ⟨t⁻¹, fun x y => ?_⟩
    simp only [rhoT, ContinuousLinearMap.coe_coe]
    rw [inner_rho_left, map_inv torus t]

theorem exists_weight {χ : (Fin n → Circle) → ℂ} {v : E.V}
    (hv : v ∈ ⨅ t, eigenspace (rhoT E t) (χ t)) (hv0 : v ≠ 0) :
    ∃ μ : Fin n → ℤ, ∀ t, E.ρ (torus t) v = (∏ a, (t a : ℂ) ^ μ a) • v := by
  have hχ : ∀ t, E.ρ (torus t) v = χ t • v := fun t =>
    mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv t)
  have hmul : ∀ s t, χ (s * t) = χ s * χ t := by
    intro s t
    have h := hχ (s * t)
    rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hχ t, map_smul, hχ s, smul_smul] at h
    rw [← smul_left_injective ℂ hv0 h, mul_comm]
  have hone : χ 1 = 1 := by
    have h := hχ 1
    rw [map_one, map_one, ContinuousLinearMap.one_apply] at h
    exact (smul_left_injective ℂ hv0 (h.symm.trans (one_smul ℂ v).symm))
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  have hform : ∀ t, χ t = ⟪v, E.ρ (torus t) v⟫_ℂ / ⟪v, v⟫_ℂ := by
    intro t
    rw [hχ, inner_smul_right, mul_div_assoc, div_self hvv, mul_one]
  have hcont : Continuous χ := by
    have : χ = fun t => ⟪v, E.ρ (torus t) v⟫_ℂ / ⟪v, v⟫_ℂ := funext hform
    rw [this]
    exact (continuous_const.inner ((E.cont.comp continuous_torus).clm_apply continuous_const)).div_const _
  let χM : (Fin n → Circle) →* ℂ := ⟨⟨χ, hone⟩, hmul⟩
  have hc : ∀ a, ∃ m : ℤ, ∀ z : Circle, χ (Pi.mulSingle a z) = (z : ℂ) ^ m := by
    intro a
    let f : Circle →* ℂˣ := (χM.comp (MonoidHom.mulSingle _ a)).toHomUnits
    have hf : Continuous f := by
      have hs : Continuous fun z : Circle => (Pi.mulSingle a z : Fin n → Circle) := by
        refine continuous_pi fun j => ?_
        rcases eq_or_ne j a with rfl | h
        · simp only [Pi.mulSingle_eq_same]; exact continuous_id'
        · simpa [Pi.mulSingle_eq_of_ne h] using continuous_const
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · show Continuous fun z => χ (Pi.mulSingle a z)
        exact hcont.comp hs
      have : (fun z => (((f z)⁻¹ : ℂˣ) : ℂ)) = fun z => χ (Pi.mulSingle a z⁻¹) := by
        funext z; rw [← map_inv]; rfl
      rw [this]; exact hcont.comp (hs.comp continuous_inv)
    obtain ⟨m, hm, -⟩ := GroundTheory.Global.existsUnique_circle_zpow ⟨f, hf⟩
    exact ⟨m, hm⟩
  choose μ hμ using hc
  refine ⟨μ, fun t => ?_⟩
  rw [hχ]
  congr 1
  conv_lhs => rw [← Finset.univ_prod_mulSingle t]
  change χM (∏ a, Pi.mulSingle a (t a)) = _
  rw [map_prod]
  exact Finset.prod_congr rfl fun a _ => hμ a (t a)

end GlobalTheory.CompanionTheory.RealCount.TorusSpan

namespace GlobalTheory.CompanionTheory.RealCount.TorusSpan

open PositivityTheory.RgBcC Module.End

variable {n : ℕ}

theorem exists_torus (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z) :
    ∃ t : Fin n → Circle, torus t = k ∧ ∀ a, (t a : ℂ) = z a := by
  have hn : ∀ a, ‖z a‖ = 1 := by
    intro a
    have h1 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 k.2) a) a
    rw [hk, Matrix.star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal] at h1
    simp only [diagonal_apply_eq, one_apply_eq, Pi.star_apply, Complex.star_def] at h1
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
    have h2 : ‖z a‖ ^ 2 = 1 := by exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  refine ⟨fun a => ⟨z a, mem_sphere_zero_iff_norm.2 (hn a)⟩, Subtype.ext ?_, fun a => rfl⟩
  rw [hk]
  rfl

end GlobalTheory.CompanionTheory.RealCount.TorusSpan

namespace GlobalTheory.CompanionTheory.RealCount.Tope

open PositivityTheory.RgBcC Module.End GlobalTheory.CompanionTheory.RealCount.TorusSpan

theorem iSup_wtDual_eq_top {n : ℕ} (E : KMod n) : (⨆ μ, wtDual E μ) = ⊤ := by
  haveI := FiniteDimensional.complete ℂ E.V
  rw [eq_top_iff]
  intro ξ _
  obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℂ E.V).surjective ξ
  have hv : v ∈ (⊤ : Submodule ℂ E.V) := trivial
  rw [← span_V E] at hv
  refine Submodule.iSup_induction _ (motive := fun v => InnerProductSpace.toDual ℂ E.V v ∈ ⨆ μ, wtDual E μ) hv
    ?_ ?_ ?_
  · intro χ v hv
    by_cases hv0 : v = 0
    · subst hv0; simp
    obtain ⟨μ, hμ⟩ := exists_weight E hv hv0
    refine Submodule.mem_iSup_of_mem (-μ) ?_
    intro k z hk
    obtain ⟨t, rfl, htz⟩ := exists_torus k z hk
    ext w
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply_apply,
      InnerProductSpace.toDual_apply_apply, ← inner_rho_left, hμ, inner_smul_left, smul_eq_mul]
    congr 1
    rw [map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← htz, map_zpow₀, ← Circle.coe_inv_eq_conj, ← Circle.coe_zpow, ← Circle.coe_zpow, _root_.inv_zpow', Pi.neg_apply]
  · simp
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

end GlobalTheory.CompanionTheory.RealCount.Tope
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharZeroDimSupport
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem interNumRed_eq_one_of_eq_singleton {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    [Algebra K Γ(X, ⊤)] (hp : IsProjOver (strHom K X)) (Z : Closeds X) {w : X}
    (hZ : (Z : Set X) = {w}) (P : Fin 0 → LB X) : interNumRed K Z P = 1 := by
  letI := algebraΓAlong K (redι Z)
  have hk := appTop_algebraMap_along K (redι Z)
  have hX : IsProper (strHom K X) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hrange : Set.range (redι Z) = {w} := (range_redι Z).trans hZ

  have hsub : Subsingleton (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    refine ⟨fun a b => (redι Z).isEmbedding.injective ?_⟩
    have ha : redι Z a = w := by
      have : redι Z a ∈ Set.range (redι Z) := ⟨a, rfl⟩
      rwa [hrange] at this
    have hb : redι Z b = w := by
      have : redι Z b ∈ Set.range (redι Z) := ⟨b, rfl⟩
      rwa [hrange] at this
    rw [ha, hb]
  have hne : Nonempty (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    have : w ∈ Set.range (redι Z) := by rw [hrange]; rfl
    obtain ⟨a, -⟩ := this
    exact ⟨a⟩
  obtain ⟨p⟩ := hne
  have hAff : IsAffine (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := ⊤) trivial
    have hUt : U = ⊤ := top_le_iff.1 fun q _ => (Subsingleton.elim q p) ▸ hpU
    subst hUt
    haveI : IsAffine (⊤ : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens).toScheme := hU
    exact IsAffine.of_isIso (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.topIso.inv
  haveI : Nonempty (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := ⟨p⟩
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    isIntegral_red (hZ ▸ isIrreducible_singleton)
  have hpr : IsProper (strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom hk]
    infer_instance
  haveI : IsFinite (strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : Module.Finite K Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    have hf := IsFinite.finite_app (strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ⊤
      (isAffineOpen_top _)
    have hi : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    have hc := hf.comp hi
    have e : algebraMap K Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) =
        ((strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme).app ⊤).hom.comp
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom :=
      RingHom.ext (algebraMap_eq_strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)
    rw [← RingHom.finite_algebraMap, e]
    exact hc
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤))
  have e1 : interNumRed K Z P =
      chi K (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    change interNumOn K (redι Z) P = _
    exact (interNumOn_eq_interNum_pull hk isEmptyElim).trans (interNum_of_isEmpty K _ _)
  rw [e1, chi_structureModule_of_isAffine]
  have e2 := (LinearEquiv.ofBijective (Algebra.linearMap K
    Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤)) hbij).finrank_eq
  rw [← e2]
  simp

theorem chi_eq_ncard_support : ∀ {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)], IsProjOver (strHom K X) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (0 : ℕ) → (∀ x : X, Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) ≤ 1) → chi K F = ((support F).ncard : ℤ) ∧ ∀ x ∈ support F, IsClosed ({x} : Set X) := by
  intro K _ _ X _ hp F _ hd hlen
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  have hdim0 : ∀ w ∈ support F,
      topologicalKrullDim (closure ({w} : Set X)) = ((0 : ℕ) : WithBot ℕ∞) := by
    intro w hw
    have hle := (GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.dim_closure_le_suppDim hw).trans hd
    have hne : topologicalKrullDim (closure ({w} : Set X)) ≠ ⊥ := by
      rw [Ne, topologicalKrullDim_eq_bot_iff]
      exact not_isEmpty_of_nonempty (α := (closure ({w} : Set X) : Set X))
        (h := ⟨⟨w, subset_closure rfl⟩⟩)
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
    rw [← ha] at hle ⊢
    have : a ≤ 0 := by exact_mod_cast hle
    have : a = 0 := le_antisymm this bot_le
    subst this
    rfl
  have hcl : ∀ x ∈ support F, IsClosed ({x} : Set X) := by
    intro x hx
    refine isClosed_of_closure_subset fun y hy => ?_
    have hys : y ∈ support F :=
      (isClosed_support F).closure_subset_iff.2 (Set.singleton_subset_iff.2 hx) hy
    exact (GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.eq_of_mem_closure hd (hdim0 y hys) x hx hy).symm
  have hfin : (support F).Finite := by
    obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_support F)
    rw [hS]
    refine hSf.sUnion fun t ht => ?_
    have hg := (hSi t ht).isGenericPoint_genericPoint_closure
    have hgt : (hSi t ht).genericPoint ∈ t := by
      have := hg.mem
      rwa [(hSc t ht).closure_eq] at this
    have hgs : (hSi t ht).genericPoint ∈ support F := by
      rw [hS]
      exact ⟨t, ht, hgt⟩
    have e : t = {(hSi t ht).genericPoint} := by
      have := hg.def
      rw [(hSc t ht).closure_eq, (hcl _ hgs).closure_eq] at this
      exact this.symm
    rw [e]
    exact Set.finite_singleton _
  refine ⟨?_, hcl⟩
  have hP : ∀ i : Fin 0, ((finZeroElim : Fin 0 → LB X) i).IsLB := isEmptyElim
  have h := GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.interNum_eq_sum_length_mul_interNumRed K X hp (Fin 0)
    finZeroElim hP F (by simpa using hd) hfin.toFinset (fun w hw _ => hfin.mem_toFinset.2 hw)
  rw [interNum_of_isEmpty] at h
  rw [h, Set.ncard_eq_toFinset_card _ hfin, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hws : w ∈ support F := hfin.mem_toFinset.1 hw
  have hlen1 : Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) = 1 := by
    refine le_antisymm (hlen w) (ENat.one_le_iff_ne_zero.2 fun h0 => ?_)
    have := Module.length_eq_zero_iff.1 h0
    exact (mem_support_iff.1 hws).exists_pair_ne.elim fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)
  rw [hlen1, interNumRed_eq_one_of_eq_singleton hp _ (w := w) (hcl w hws).closure_eq]
  simp

end GlobalTheory.CompanionTheory.KoszulCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightInInvariantSubmodule
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.HwStable

variable {n : ℕ}

theorem weight_shift_real {V : Type} [AddCommGroup V] [Module ℂ V] {K : Fin n → Fin n → Module.End ℂ V}
    (hg : Formalism.REAL.GlRel K) (μ : Fin n → ℝ) {v : V}
    (hv : ∀ c, K c c v = ((μ c : ℝ) : ℂ) • v) {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    K c c (K a b v) =
      ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • K a b v := by
  have e : K c c (K a b v) = K a b (K c c v) +
      ((if c = a then K c b else 0) - (if b = c then K a c else 0)) v := by
    rw [← hg c c a b]
    simp [Module.End.mul_apply]
  rw [e, hv c, map_smul]
  by_cases h1 : c = a
  · subst h1
    have h2 : ¬ b = c := fun h => hab h.symm
    have h3 : ¬ c = b := hab
    simp only [↓reduceIte, h2, h3, LinearMap.sub_apply, LinearMap.zero_apply]
    push_cast
    module
  · by_cases h2 : c = b
    · subst h2
      simp only [↓reduceIte, h1, LinearMap.sub_apply, LinearMap.zero_apply]
      push_cast
      module
    · have h3 : ¬ b = c := fun h => h2 h.symm
      simp only [↓reduceIte, h1, h2, h3, sub_zero, LinearMap.zero_apply, add_zero]

section Main

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  {G : Fin n → Fin n → Module.End ℂ H} {N : Submodule ℂ H}

def diagOn (G : Fin n → Fin n → Module.End ℂ H) (N : Submodule ℂ H)
    (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (c : Fin n) : Module.End ℂ N :=
  (G c c).restrict (hst c c)

theorem diagOn_symm (hs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (c : Fin n) : (diagOn G N hst c).IsSymmetric := by
  intro x y
  exact hs c c x.1 y.1

theorem diag_commute (hg : Formalism.REAL.GlRel G) (i j : Fin n) : Commute (G i i) (G j j) := by
  have h := hg i i j j
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · have h' : ¬ j = i := fun h => hij h.symm
    rw [if_neg hij, if_neg h', sub_zero] at h
    exact sub_eq_zero.1 h

theorem diagOn_commute (hg : Formalism.REAL.GlRel G) (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (i j : Fin n) :
    Commute (diagOn G N hst i) (diagOn G N hst j) := by
  have h : G i i * G j j = G j j * G i i := diag_commute hg i j
  show diagOn G N hst i * diagOn G N hst j = diagOn G N hst j * diagOn G N hst i
  ext x
  have := congrArg (fun f : Module.End ℂ H => f x.1) h
  simpa [diagOn, Module.End.mul_apply] using this

def wts (G : Fin n → Fin n → Module.End ℂ H) (N : Submodule ℂ H) : Set (Fin n → ℝ) :=
  {μ | ∃ v ∈ N, v ≠ 0 ∧ ∀ c, G c c v = ((μ c : ℝ) : ℂ) • v}

theorem wts_nonempty (hg : Formalism.REAL.GlRel G) (hs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hN : N ≠ ⊥) (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) : (wts G N).Nonempty := by
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (fun c => diagOn_symm hs hst c)
    (fun i j _ => diagOn_commute hg hst i j)
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  obtain ⟨χ, hχ⟩ : ∃ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (diagOn G N hst c) (χ c)) ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    rw [iSup_congr hcon, iSup_bot] at htop
    exact bot_ne_top htop
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hev : ∀ c, diagOn G N hst c x = χ c • x := fun c =>
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx c)
  have hre : ∀ c, (((χ c).re : ℝ) : ℂ) = χ c := fun c => by
    have hE : Module.End.HasEigenvalue (diagOn G N hst c) (χ c) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hev c), hx0⟩
    exact Complex.conj_eq_iff_re.1 ((diagOn_symm hs hst c).conj_eigenvalue_eq_self hE)
  refine ⟨fun c => (χ c).re, x.1, x.2, fun h => hx0 (Subtype.ext h), fun c => ?_⟩
  rw [hre c]
  exact congrArg Subtype.val (hev c)

theorem wts_finite (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) : (wts G N).Finite := by
  have hfa : ∀ a, Set.Finite {r : ℝ | Module.End.HasEigenvalue (diagOn G N hst a) ((r : ℝ) : ℂ)} := fun a =>
    (Module.End.finite_hasEigenvalue _).preimage (Function.Injective.injOn Complex.ofReal_injective)
  refine (Set.Finite.pi' hfa).subset ?_
  rintro μ ⟨v, hv, h0, hw⟩ a
  exact Module.End.hasEigenvalue_of_hasEigenvector (x := (⟨v, hv⟩ : N))
    ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext (hw a)), fun h => h0 (congrArg Subtype.val h)⟩

end Main

theorem exists_highest_of_stable : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (G : Fin n → Fin n → Module.End ℂ H), Formalism.REAL.GlRel G →
    (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ N : Submodule ℂ H, N ≠ ⊥ →
    (∀ a b, ∀ w ∈ N, G a b w ∈ N) →
    ∃ (μ : Fin n → ℝ) (v : H), v ∈ N ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) G μ v := by
  intro n H _ _ _ G hg hs N hN hst
  have hfin := wts_finite hst
  obtain ⟨μ, hμ, hmax⟩ := hfin.toFinset.exists_max_image (fun ν => toLex ν)
    (by simpa using wts_nonempty hg hs hN hst)
  obtain ⟨v, hvN, hv0, hw⟩ := hfin.mem_toFinset.1 hμ
  refine ⟨μ, v, hvN, hv0, hw, fun a b hab _ => ?_⟩
  by_contra hne
  let μ' : Fin n → ℝ := fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)
  have hlt : toLex μ < toLex μ' := by
    refine ⟨a, fun j hj => ?_, ?_⟩
    · have h1 : j ≠ a := ne_of_lt hj
      have h2 : j ≠ b := ne_of_lt (lt_trans hj hab)
      show μ j = μ j + (if j = a then 1 else 0) - (if j = b then 1 else 0)
      simp [h1, h2]
    · show μ a < μ a + (if a = a then 1 else 0) - (if a = b then 1 else 0)
      simp [ne_of_lt hab]
  have hin : μ' ∈ wts G N :=
    ⟨G a b v, hst a b v hvN, hne, fun c => weight_shift_real hg μ hw (ne_of_lt hab) c⟩
  exact not_le.2 hlt (hmax μ' (hfin.mem_toFinset.2 hin))

end GlobalTheory.CompanionTheory.RealCountG.HwStable
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocalStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_kazhdan_local : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k := by
  first | exact @GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | exact GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | (intros; apply GlobalTheory.CompanionTheory.GenGK.gkLocal_gen <;> assumption)
end

