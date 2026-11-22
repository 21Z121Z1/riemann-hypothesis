import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0088

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelMat
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat

theorem exists_ext (K : Type) [Field K] [NumberField K] (τ : 𝓞 K →+* ℂ) :
    ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ := by
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    have h : Function.Injective (τ.comp (algebraMap ℤ (𝓞 K))) := RingHom.injective_int _
    rw [RingHom.injective_iff_ker_eq_bot] at h
    exact (RingHom.comap_ker τ (algebraMap ℤ (𝓞 K))).trans h
  refine ⟨IsFractionRing.lift (A := 𝓞 K) (K := K) (L := ℂ) (g := τ) hinj, ?_⟩
  ext x
  exact IsFractionRing.lift_algebraMap (K := K) hinj x

theorem ext_unique (K : Type) [Field K] [NumberField K] {σ σ' : K →+* ℂ}
    (h : σ.comp (algebraMap (𝓞 K) K) = σ'.comp (algebraMap (𝓞 K) K)) : σ = σ' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K)) h

theorem unitary_of_norm {N : ℕ} (W : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ y : Fin N → ℂ, Real.sqrt (∑ i, ‖W.mulVec y i‖ ^ 2) = Real.sqrt (∑ i, ‖y i‖ ^ 2)) :
    W ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have h1 : ∀ y : EuclideanSpace ℂ (Fin N), ‖Matrix.toEuclideanLin W y‖ = ‖y‖ := fun y => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact h y.ofLp
  have h2 := (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin W)).1 h1
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := h2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [EuclideanSpace.inner_single_left] at this
  simp only [PiLp.inner_apply] at this
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.toEuclideanLin, mul_comm, eq_comm] using this

theorem exists_unitary {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (h : ∀ x : Fin N → ℂ, GlobalTheory.ChowHt.frameNorm B (fun j => (starRingEnd ℂ) (x j)) = GlobalTheory.ChowHt.frameNorm A x) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, B = A.map (starRingEnd ℂ) * U := by
  have hW : B⁻¹ * A.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    refine unitary_of_norm _ fun y => ?_
    have := h (A.mulVec fun j => (starRingEnd ℂ) (y j))
    unfold GlobalTheory.ChowHt.frameNorm at this
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.one_mulVec] at this
    have e : (fun j => (starRingEnd ℂ) (A.mulVec (fun j => (starRingEnd ℂ) (y j)) j)) =
        (A.map (starRingEnd ℂ)).mulVec y := by
      funext j
      simp [Matrix.mulVec, dotProduct]
    rw [e, Matrix.mulVec_mulVec] at this
    simpa using this
  refine ⟨star (B⁻¹ * A.map (starRingEnd ℂ)), Unitary.star_mem hW, ?_⟩
  have h1 := Matrix.mem_unitaryGroup_iff.1 hW
  calc B = B * ((B⁻¹ * A.map (starRingEnd ℂ)) * star (B⁻¹ * A.map (starRingEnd ℂ))) := by rw [h1, mul_one]
    _ = _ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB.isUnit, Matrix.one_mul]

theorem exists_P {K : Type} [Field K] {N m : ℕ} (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) :
    ∃ (r : ℕ) (e : Fin m ≃ Fin N ⊕ Fin r) (P : Matrix (Fin m) (Fin m) K), P.det ≠ 0 ∧
      g * P = (Matrix.fromCols (1 : Matrix (Fin N) (Fin N) K) (0 : Matrix (Fin N) (Fin r) K)).submatrix id e := by
  have hs : LinearMap.range g.mulVecLin = ⊤ := by
    rw [Matrix.range_mulVecLin]; exact hg
  obtain ⟨s, hs'⟩ := LinearMap.exists_rightInverse_of_surjective _ hs
  have hs2 : ∀ x, g.mulVecLin (s x) = x := fun x => LinearMap.congr_fun hs' x
  set r := Module.finrank K (LinearMap.ker g.mulVecLin) with hr
  have hdim : N + r = m := by
    have := LinearMap.finrank_range_add_finrank_ker g.mulVecLin
    rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at this
    exact this
  let e : Fin m ≃ Fin N ⊕ Fin r := (finCongr hdim.symm).trans finSumFinEquiv.symm
  let c : (Fin r → K) ≃ₗ[K] LinearMap.ker g.mulVecLin := (Module.finBasis K _).equivFun.symm
  let φ : (Fin m → K) →ₗ[K] (Fin m → K) :=
    s ∘ₗ LinearMap.funLeft K K (fun i => e.symm (Sum.inl i)) +
      (LinearMap.ker g.mulVecLin).subtype ∘ₗ c.toLinearMap ∘ₗ LinearMap.funLeft K K (fun i => e.symm (Sum.inr i))
  have hφ : ∀ v, φ v = s (fun i => v (e.symm (Sum.inl i))) + (c (fun i => v (e.symm (Sum.inr i))) : Fin m → K) :=
    fun v => rfl
  have hgφ : ∀ v, g.mulVecLin (φ v) = fun i => v (e.symm (Sum.inl i)) := fun v => by
    rw [hφ, map_add, hs2, LinearMap.mem_ker.1 (c _).2, add_zero]
  refine ⟨r, e, LinearMap.toMatrix' φ, ?_, ?_⟩
  · intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [LinearMap.toMatrix'_mulVec] at hv0
    have h1 : (fun i => v (e.symm (Sum.inl i))) = 0 := by rw [← hgφ, hv0, map_zero]
    have h2 : (fun i => v (e.symm (Sum.inr i))) = 0 := by
      rw [hφ, h1, map_zero, zero_add] at hv0
      exact c.map_eq_zero_iff.1 (Subtype.ext hv0)
    refine hv (funext fun a => ?_)
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    rcases a with i | i
    · exact congrFun h1 i
    · exact congrFun h2 i
  · ext j a
    have := congrFun (hgφ (Pi.single a 1)) j
    rw [Matrix.mulVecLin_apply, ← LinearMap.toMatrix'_mulVec φ, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
    rw [show (g * LinearMap.toMatrix' φ) j a = _ from this]
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    rcases a with i | i <;> simp [Pi.single_apply, Matrix.one_apply]

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat

theorem PositivityTheory.Xgn.t_xgz_height_r_vol_up_model_mat : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame Nm L b g A → ∃ Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, (∀ σ, (Mt σ).det ≠ 0) ∧ (∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U) ∧ ∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2 := by
  intro K V _ _ _ _ _ Nm L N m b g A hF
  obtain ⟨r, e, P, hP, hgP⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_P g hF.full
  choose ext hext using PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_ext K
  have hu : ∀ σ : K →+* ℂ, ext (σ.comp (algebraMap (𝓞 K) K)) = σ := fun σ =>
    PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.ext_unique K (hext _)
  have hc : ∀ τ, ext ((starRingEnd ℂ).comp τ) = (starRingEnd ℂ).comp (ext τ) := fun τ =>
    PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.ext_unique K (by rw [hext, RingHom.comp_assoc, hext])
  refine ⟨fun τ => P.map (ext τ) * (Matrix.fromBlocks (A (ext τ)) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e,
    fun τ => ?_, fun τ => ?_, fun σ x => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    refine mul_ne_zero ?_ (hF.herm _)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hP
  · obtain ⟨U, hU, hB⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_unitary (A (ext τ))
      (A ((starRingEnd ℂ).comp (ext τ))) (hF.herm _) (hF.herm _) (hF.conj _)
    refine ⟨(Matrix.fromBlocks U 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
      rw [Matrix.star_eq_conjTranspose] at hU ⊢
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply]
      simp [hU]
    · simp only []
      rw [hc, hB, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
        Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_map]
      simp
  · simp only [hu]
    have key : g.map σ * (P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e) =
        (Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ)).submatrix id e := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, hgP, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
        Matrix.fromCols_map, Matrix.fromCols_mul_fromBlocks]
      simp
    have k2 : ∀ a, ∑ k, (P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e) k a *
        ∑ j, σ (g j k) * x j = ∑ j, Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ) j (e a) * x j := by
      intro a
      generalize P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e = M at key
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := congrFun (congrFun key j) a
      rw [Matrix.submatrix_apply, id, Matrix.mul_apply] at this
      rw [← this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.map_apply]; ring
    simp only [k2]
    rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Equiv.sum_comp e (fun a => ‖∑ j, Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ) j a * x j‖ ^ 2),
      Fintype.sum_sum_type]
    simp
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelModel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model

theorem exists_comb {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {N m : ℕ} (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) (v : V) :
    ∃ c : Fin m → K, ev v = ∑ k, algebraMap K Ω (c k) * ev (∑ j, g j k • b j) := by
  have hmem : (⇑(b.repr v) : Fin N → K) ∈ Submodule.span K (Set.range g.col) := by
    rw [hg]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  refine ⟨c, ?_⟩
  have hv : v = ∑ k, c k • ∑ j, g j k • b j := by
    conv_lhs => rw [← b.sum_repr v]
    rw [← hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    rfl
  rw [hv]
  simp only [map_sum, map_smul, Algebra.smul_def]

theorem closure_eq_top {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {m : ℕ} (t : Fin m → Ω)
    (ht : ∀ v, ∃ c : Fin m → K, ev v = ∑ k, algebraMap K Ω (c k) * t k) (i : Fin m) (hi : t i ≠ 0)
    (hr : IntermediateField.adjoin K {a : Ω | ∃ v w, a = ev v / ev w} = ⊤) :
    Subfield.closure (Set.range (algebraMap (𝓞 K) Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤ := by
  set F := Subfield.closure (Set.range (algebraMap (𝓞 K) Ω) ∪ {x | ∃ i j, x = t j / t i}) with hF
  have hK : ∀ x : K, algebraMap K Ω x ∈ F := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    rw [map_div₀]
    have e : ∀ y : 𝓞 K, algebraMap K Ω (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) Ω y :=
      fun y => (IsScalarTower.algebraMap_apply (𝓞 K) K Ω y).symm
    rw [e, e]
    exact div_mem (Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) (Subfield.subset_closure (Or.inl ⟨b, rfl⟩))
  have key : ∀ u, ev u / t i ∈ F := by
    intro u
    obtain ⟨c, hc⟩ := ht u
    rw [hc, Finset.sum_div]
    refine sum_mem fun k _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (hK (c k)) (Subfield.subset_closure (Or.inr ⟨i, k, rfl⟩))
  have hS : {a : Ω | ∃ v w, a = ev v / ev w} ⊆ (F.toIntermediateField hK : Set Ω) := by
    rintro _ ⟨v, w, rfl⟩
    show ev v / ev w ∈ F
    rw [← div_div_div_cancel_right₀ hi (ev v) (ev w)]
    exact div_mem (key v) (key w)
  have hle := (IntermediateField.adjoin_le_iff).2 hS
  rw [hr] at hle
  exact eq_top_iff.2 fun x _ => hle (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField K Ω))

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelNef
section
namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel

theorem isNef_of_small {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (L : HermLB p) (hs : L.SemiPos D) {ι : Type} [Finite ι] (u : ι → L.B.Sec) (hu : ∀ i, u i ∈ L.smallSec)
    (hg : ⨆ i, nonzeroLocus (u i) = ⊤) : L.IsNef D where
  semiPos := hs
  vertical := GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX L (isGenerated_of_finite u hg)
  horizontal Z i _ _ _ hc hd := by
    have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
    have hm : i (genericPoint Z) ∈ ⨆ a, nonzeroLocus (u a) := by rw [hg]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.1 hm
    have hgen : genericPoint Z ∈ nonzeroLocus (GlobalTheory.secPull (u a) i) := by
      rw [GlobalTheory.nonzeroLocus_secPull]; exact ha
    have h0 : ∀ σ (y : CxPts (i ≫ p) σ), y ∈ ptsIn _ σ (nonzeroLocus (GlobalTheory.secPull (u a) i)) := fun σ y => by
      refine mem_ptsIn.2 ?_
      have key : ∀ y : Sp ℂ ⟶ Z, y (IsLocalRing.closedPoint ℂ) = genericPoint Z := fun y =>
        GlobalTheory.HtSelfInter.eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero
      rw [key]
      exact hgen
    refine ⟨_, isRatSec_ratOfSec _ hgen, ?_⟩
    rw [HermLB.curveDeg_sec i (u a) hgen h0]
    refine sub_nonneg.2 (le_trans (b := 0) ?_ ?_)
    · refine finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun σ =>
        finsum_induction (· ≤ (0 : ℝ)) le_rfl (fun _ _ => add_nonpos) fun y => ?_
      refine div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos ?_ (hu a σ _)) zero_le_two
      unfold Weight.nsq
      positivity
    · exact finsum_nonneg fun z =>
        mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg z)) (Real.log_natCast_nonneg _)

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
  {M : RatModel (𝓞 K) Ω}

theorem const_val {σ : K →+* ℂ} {y : Sp ℂ ⟶ M.Z} (hy : y ≫ M.s = spMap (σ.comp (algebraMap (𝓞 K) K))) (a : K) :
    algebraMap K Ω a ∈ M.O (y (IsLocalRing.closedPoint ℂ)) ∧ M.val y (algebraMap K Ω a) = σ a := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hr := range_eq_singleton y (IsLocalRing.closedPoint ℂ)
  have hq0 : algebraMap (𝓞 K) K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have hσq : σ (algebraMap (𝓞 K) K q) ≠ 0 := (map_ne_zero σ).2 hq0
  have hv := fun c => val_algebraMap hy c
  have hu : IsUnit (⟨algebraMap (𝓞 K) Ω q, Subalgebra.algebraMap_mem _ q⟩ :
      M.O (y (IsLocalRing.closedPoint ℂ))) := (val_ne_zero_iff hr _).1 (by rw [hv]; exact hσq)
  obtain ⟨h0, hi⟩ := (isUnit_O_iff _).1 hu
  dsimp only at h0 hi
  have e : algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) =
      algebraMap (𝓞 K) Ω p * (algebraMap (𝓞 K) Ω q)⁻¹ := by
    rw [map_div₀, div_eq_mul_inv, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hm : algebraMap (𝓞 K) Ω p * (algebraMap (𝓞 K) Ω q)⁻¹ ∈ M.O (y (IsLocalRing.closedPoint ℂ)) :=
    mul_mem (Subalgebra.algebraMap_mem _ p) hi
  rw [e]
  refine ⟨hm, ?_⟩
  have h1 := val_mul (specializes_of_range_eq hr) hm (Subalgebra.algebraMap_mem _ q)
  rw [inv_mul_cancel_right₀ h0, hv, hv] at h1
  rw [map_div₀, eq_div_iff hσq]
  exact h1.symm

theorem exists_coord {σ : K →+* ℂ} {y : Sp ℂ ⟶ M.Z} (hy : y ≫ M.s = spMap (σ.comp (algebraMap (𝓞 K) K)))
    (ev : V →ₗ[K] Ω) (c : Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) {S : Set V} (hS : Submodule.span K S = ⊤)
    (hc : ∀ v ∈ S, ev v / c ∈ M.O (y (IsLocalRing.closedPoint ℂ))) :
    ∃ x : Fin N → ℂ, ∀ v, M.val y (ev v / c) = ∑ j, σ (b.repr v j) * x j := by
  have hr := specializes_of_range_eq (range_eq_singleton y (IsLocalRing.closedPoint ℂ))
  have hsm : ∀ (a : K) v, ev (a • v) / c = algebraMap K Ω a * (ev v / c) := fun a v => by
    rw [map_smul, Algebra.smul_def, mul_div_assoc]
  have hall : ∀ v, ev v / c ∈ M.O (y (IsLocalRing.closedPoint ℂ)) := fun v => by
    have hv : v ∈ Submodule.span K S := hS ▸ trivial
    induction hv using Submodule.span_induction with
    | mem _ h => exact hc _ h
    | zero => rw [map_zero, zero_div]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add, add_div]; exact add_mem ha hb
    | smul a v _ hv => rw [hsm]; exact mul_mem (const_val hy a).1 hv
  let ℓ : V →+ ℂ :=
    { toFun := fun v => M.val y (ev v / c)
      map_zero' := by rw [map_zero, zero_div]; exact val_zero y
      map_add' := fun a b => by rw [map_add, add_div]; exact val_add hr (hall a) (hall b) }
  refine ⟨fun j => ℓ (b j), fun v => ?_⟩
  change ℓ v = _
  conv_lhs => rw [← b.sum_repr v, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change M.val y _ = _
  rw [hsm, val_mul hr (const_val hy _).1 (hall _), (const_val hy _).2]
  rfl

omit [NumberField K] in

theorem mem_O_of_span [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (ev : V →ₗ[K] Ω) (c : Ω) {z : M.Z} {S : Set V}
    (hc : ∀ v ∈ S, ev v / c ∈ M.O z) {v : V} (hv : v ∈ Submodule.span (𝓞 K) S) : ev v / c ∈ M.O z := by
  induction hv using Submodule.span_induction with
  | mem _ h => exact hc _ h
  | zero => rw [map_zero, zero_div]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add, add_div]; exact add_mem ha hb
  | smul a v _ hv =>
    rw [← algebraMap_smul K a v, map_smul, Algebra.smul_def, mul_div_assoc, ← IsScalarTower.algebraMap_apply]
    exact mul_mem (Subalgebra.algebraMap_mem _ a) hv

omit [NumberField K] in

theorem exists_isUnit (ev : V →ₗ[K] Ω) (c : Ω) {z : M.Z} {ι : Type} (w : ι → V)
    (hc : ∀ i, ev (w i) / c ∈ M.O z) {v : V} (hv : v ∈ Submodule.span ℤ (Set.range w)) (h : ev v / c ∈ M.O z)
    (hu : IsUnit (⟨_, h⟩ : M.O z)) : ∃ i, IsUnit (⟨_, hc i⟩ : M.O z) := by
  by_contra hn
  have key : ∃ a ∈ IsLocalRing.maximalIdeal (M.O z), (a : Ω) = ev v / c := by
    clear hu h
    induction hv using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact ⟨⟨_, hc i⟩, fun h => hn ⟨i, h⟩, rfl⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha, ea⟩ := ha
      obtain ⟨b', hb, eb⟩ := hb
      exact ⟨a' + b', add_mem ha hb, by rw [map_add, add_div, ← ea, ← eb]; rfl⟩
    | smul n a _ ha =>
      obtain ⟨a', ha, ea⟩ := ha
      refine ⟨n • a', zsmul_mem ha n, ?_⟩
      rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul, mul_div_assoc, ← ea]
      simp
  obtain ⟨a, ha, ea⟩ := key
  obtain rfl : a = ⟨_, h⟩ := Subtype.ext ea
  exact ha hu

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

theorem PositivityTheory.Xgn.t_xgz_height_r_vol_up_model_nef : Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), IsFrame Nm L b g A → IsShortGen Nm L w abelian₂ → GlobalTheory.DegVal.GenRatios ev → Real.log abelian₂ ≤ t → ∀ (M : GlobalTheory.ZH.RatModel (𝓞 K) Ω), M.IsNm (fun k => ev (∑ j, g j k • b j)) → IsProjOver M.s → GlobalTheory.IsArithVar M.s d → ∀ (H : ReciprocityTheory.ChartRestriction.G.Semi.LB M.Z) (hH : H.IsLB) (e : H.ι → Ω), M.GenTriv H e → ∀ (s : Fin m → H.Sec), (∀ k, M.HasVal e (s k) (ev (∑ j, g j k • b j))) → ∀ (hs : ⨆ k, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) (hdet : ∀ σ, (Mt σ).det ≠ 0) (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U), (∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2) → ((GlobalTheory.HermLB.fs M.s hH s hs Mt hdet hc).shift (fun _ => t) (fun _ => rfl)).IsNef d := by
  intro _ K V Ω _ _ _ _ _ _ _ _ _ Nm L ev d N m b g A n w abelian₂ t hF hW _ ht M _ _ hX H hH e he s hv hs Mt hdet hc hMt
  have hreg : ∀ l, ∀ z ∈ H.U l, ∀ v ∈ L, ev v / e l ∈ M.O z := fun l z hz v hvL => by
    refine PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.mem_O_of_span ev _ ?_ (hF.span ▸ hvL)
    rintro _ ⟨k, rfl⟩
    rw [← hv k l ⟨z, hz⟩]
    exact GlobalTheory.ZH.RatModel.valF_mem_O hz _
  have hwL : ∀ i, w i ∈ L := fun i => (hW.gen _).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hcL : ∀ k, (∑ j, g j k • b j) ∈ L := fun k => hF.span ▸ Submodule.subset_span ⟨k, rfl⟩
  choose u hu using fun i => he.exists_sec_hasVal (ev (w i)) fun l z hz => hreg l z hz _ (hwL i)
  refine PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.isNef_of_small hX _
    ((GlobalTheory.HermLB.semiPos_fs hH s hs Mt hdet hc).shift _ _) u (fun i σ' y => ?_) ?_
  · obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = σ' :=
      ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp σ'⟩
    have hl := GlobalTheory.CxPts.mem_pick hH y
    generalize GlobalTheory.CxPts.pick hH y = l at hl
    have hz := GlobalTheory.CxPts.mem_ptsIn.1 hl
    have hspan : Submodule.span K (L : Set V) = ⊤ := by
      have h2 := congrArg (Submodule.map b.equivFun.symm.toLinearMap) hF.full
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h2
      refine eq_top_iff.2 (h2.ge.trans (Submodule.span_mono ?_))
      rintro _ ⟨k, rfl⟩
      change b.equivFun.symm (g.col k) ∈ L
      rw [Module.Basis.equivFun_symm_apply]
      exact hcL k
    obtain ⟨x, hx⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.exists_coord y.2 ev (e l) b hspan (hreg l _ hz)
    have hr : Set.range y.1 ⊆ H.U l := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 hl
    have hval : ∀ (a : H.Sec) v, M.HasVal e a (ev v) →
        valR y.1 (H.U l) (a.f l) = ∑ j, σ (b.repr v j) * x j := fun a v ha =>
      (GlobalTheory.ZH.RatModel.val_eq hr (ha l ⟨_, hz⟩)).symm.trans (hx v)
    have hsk : ∀ k, valR y.1 (H.U l) ((s k).f l) = ∑ j, σ (g j k) * x j := fun k => by
      rw [hval _ _ (hv k)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [b.repr_sum_self]
    have hpos := (GlobalTheory.Weight.noCommonZero_combVal (p := M.s) (σ := σ.comp (algebraMap (𝓞 K) K)) hs
      (hdet (σ.comp (algebraMap (𝓞 K) K)))).sum_pos hl
    have hφ : ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * valR y.1 (H.U l) ((s k).f l)‖ ^ 2 =
        GlobalTheory.Adelic.archSize (A σ) x ^ 2 := by
      simp only [hsk]; exact hMt σ x
    have hpos' : 0 < GlobalTheory.Adelic.archSize (A σ) x ^ 2 := by
      rw [← hφ]
      simp only [GlobalTheory.Weight.combVal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hpos
      exact hpos
    have hle := GlobalTheory.Adelic.norm_pairing_le (hF.herm σ) (fun j => σ (b.repr (w i) j)) x
    rw [hF.norm, ← hval _ _ (hu i)] at hle
    have hS : 0 ≤ GlobalTheory.Adelic.archSize (A σ) x := Real.sqrt_nonneg _
    have hLam : abelian₂ ≤ Real.exp t :=
      (Real.log_le_iff_le_exp (lt_of_lt_of_le one_pos hW.one_le)).1 ht
    have hle2 := hle.trans (mul_le_mul_of_nonneg_right ((hW.le i σ).trans hLam) hS)
    refine le_of_eq_of_le (((GlobalTheory.HermLB.fs M.s hH s hs Mt hdet hc).nsq_shift (fun _ => t) (fun _ => rfl) _ y).trans
      (congrArg (· * _) (GlobalTheory.Weight.nsq_eq _ (GlobalTheory.CxPts.secVal_mem (u i)) hl))) ?_
    have e1 : ((GlobalTheory.HermLB.fs M.s hH s hs Mt hdet hc).φ (σ.comp (algebraMap (𝓞 K) K))).φ l y =
        Real.log (GlobalTheory.Adelic.archSize (A σ) x ^ 2) := by
      rw [← hφ]; exact GlobalTheory.Weight.fsBasis_φ hH s hs _ (hdet _) l y
    rw [e1, Real.exp_neg, Real.exp_log hpos', Real.exp_neg, mul_assoc, ← mul_inv, ← div_eq_mul_inv,
      div_le_one (by positivity), two_mul, Real.exp_add, ← sq, ← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (norm_nonneg _) hle2 2
  · refine eq_top_iff.2 fun z _ => ?_
    have hm : z ∈ ⨆ k, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s k) := by rw [hs]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hk
    have hz : z ∈ H.U l := M.Z.basicOpen_le _ hl
    have h1 := (GlobalTheory.ZH.RatModel.isUnit_valF_iff hz _).2 hl
    obtain ⟨i, hi⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.exists_isUnit ev (e l) w
      (fun i => hreg l z hz _ (hwL i)) ((hW.gen _).1 (hcL k)) (hreg l z hz _ (hcL k))
      (by convert h1 using 2; exact (hv k l ⟨z, hz⟩).symm)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨l,
      (GlobalTheory.ZH.RatModel.isUnit_valF_iff hz _).1 ?_⟩⟩
    convert hi using 2
    exact hu i l ⟨z, hz⟩
end

