import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeArithVolumeOfFrequentlySmallSectionsLowerStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_arithVolume_of_frequently_smallSections_lower : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (a : ℝ), (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (L.pow N).smallSec.Finite ∧ (a / (D + 1).factorial - ε) * (N : ℝ) ^ (D + 1) ≤ Real.log ((L.pow N).smallSec.ncard : ℝ)) → (a : EReal) ≤ arVol L D := by
  first | exact @GlobalTheory.VolBr.le_arVol_of_frequently_le | exact GlobalTheory.VolBr.le_arVol_of_frequently_le | (intros; apply GlobalTheory.VolBr.le_arVol_of_frequently_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.HeightExists

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Twist GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.QCoh

attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra

variable {k K σ : Type} [Field k] [Field K] [Algebra k K]

def coeffMap (l : K →ₗ[k] k) (g : MvPolynomial σ K) : MvPolynomial σ k :=
  ∑ a ∈ g.support, monomial a (l (coeff a g))

theorem coeff_coeffMap (l : K →ₗ[k] k) (g : MvPolynomial σ K) (a : σ →₀ ℕ) :
    coeff a (coeffMap l g) = l (coeff a g) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem isHomogeneous_coeffMap (l : K →ₗ[k] k) {g : MvPolynomial σ K} {d : ℕ} (hg : g.IsHomogeneous d) :
    (coeffMap l g).IsHomogeneous d := fun a ha =>
  hg fun h => ha (by rw [coeff_coeffMap, h, map_zero])

theorem mem_map_of_coeffMap {I : Ideal (MvPolynomial σ k)} {g : MvPolynomial σ K}
    (h : ∀ l : K →ₗ[k] k, coeffMap l g ∈ I) :
    g ∈ I.map (MvPolynomial.map (algebraMap k K) : MvPolynomial σ k →+* MvPolynomial σ K) := by
  classical
  let b := Module.Basis.ofVectorSpace k K
  let s := g.support.biUnion fun a => (b.repr (coeff a g)).support
  have e : g = ∑ i ∈ s, C (b i) * map (algebraMap k K) (coeffMap (b.coord i) g) := by
    ext a
    simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_coeffMap]
    have hs : (b.repr (coeff a g)).support ⊆ s := by
      by_cases ha : a ∈ g.support
      · exact Finset.subset_biUnion_of_mem (fun a => (b.repr (coeff a g)).support) ha
      · simp [notMem_support_iff.1 ha]
    conv_lhs => rw [← b.linearCombination_repr (coeff a g),
      Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hs _ (by simp)]
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]; rfl
  rw [e]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))

theorem le_of_ringKrullDim_coneIdeal {N D e : ℕ} (y : Fin N → K) (hD : Algebra.trdeg k K = D)
    (he : ringKrullDim (MvPolynomial (Fin N) k ⧸ coneIdeal k y) = (e + 1 : ℕ)) : e ≤ D := by
  have := isPrime_coneIdeal (K := k) y
  obtain ⟨d, h1, h2⟩ := exists_ringKrullDim_eq_and_trdeg_eq k (MvPolynomial (Fin N) k ⧸ coneIdeal k y)
  obtain rfl : d = e + 1 := by exact_mod_cast h1.symm.trans he
  have h3 := trdeg_le_of_injective (Ideal.kerLiftAlg (coneMap k y)) (Ideal.kerLiftAlg_injective _)
  rw [← trdeg_add_eq k K (A := Polynomial K), Polynomial.trdeg_of_isDomain, hD] at h3
  have h4 : ((e + 1 : ℕ) : Cardinal.{0}) ≤ ((D + 1 : ℕ) : Cardinal.{0}) := by
    rw [← h2, Nat.cast_add, Nat.cast_one]; exact h3
  have : e + 1 ≤ D + 1 := by exact_mod_cast h4
  omega

end Algebra

variable {k : Type} [Field k] (S : LinSys k)

theorem chartEval_eq_zero {g : MvPolynomial (Fin S.N) k} {d : ℕ} (hg : g.IsHomogeneous d) (h : g ∈ S.imageIdeal)
    (i : S.L.ι) {W : S.Y.Opens} (hle : W ≤ S.L.U i) : chartEval k S.b i hle g = 0 := by
  have e : resG _ hle (zfun (S.form hg) i) = 0 := by
    rw [(S.mem_imageIdeal_iff hg).1 h]
    exact (congrArg _ (zfun_zero i)).trans (map_zero _)
  rwa [LinSys.form, zfun_formSec, resG_chartEval] at e

theorem coeffMap_mem_imageIdeal (E : Type) [Field E] [Algebra k E] {g : MvPolynomial (Fin S.N) E} {d : ℕ}
    (hg : g.IsHomogeneous d) (h : g ∈ (S.baseChange E).imageIdeal) (l : E →ₗ[k] k) :
    coeffMap l g ∈ S.imageIdeal := by
  refine (S.mem_imageIdeal_iff (isHomogeneous_coeffMap l hg)).2 (zglobal_ext fun i => ?_)
  rw [zfun_zero, LinSys.form, zfun_formSec]
  refine S.Y.sheaf.eq_of_locally_eq' (fun W : {W : S.Y.affineOpens // W.1 ≤ S.L.U i} => W.1.1) _
    (fun W => homOfLE W.2) (fun y hy => ?_) _ _ fun W => ?_
  · obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := S.L.U i) (x := y) hy
    exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hx⟩
  obtain ⟨⟨W, hW⟩, hle⟩ := W
  have H := S.isPullback_baseChange E
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W) le_top le_top
    (UY := S.bcFst E ⁻¹ᵁ W) (by simp)).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hW)
  have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top)
      (CommRingCat.ofHom (algebraMap k E)) ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl)
      ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
        (S.baseChange E).str.appLE ⊤ (S.bcFst E ⁻¹ᵁ W) le_top) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  obtain ⟨Λ, hΛ⟩ := IndepBaseChange.exists_contract po' l
  have hle' : S.bcFst E ⁻¹ᵁ W ≤ (S.baseChange E).L.U fun _ => i :=
    fun y hy => Set.mem_iInter.2 fun _ => hle hy
  have e := (eval₂_eq _ _ _).symm.trans (chartEval_eq_zero (S.baseChange E) hg h (fun _ => i) hle')
  have e' : ∀ j, resG (S.baseChange E).Y hle' (((S.baseChange E).b j).f fun _ => i) =
      ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom (resG S.Y hle ((S.b j).f i)) := fun j => by
    have a := (S.bcFst E).appLE_map (U := S.L.U i) (V := (S.baseChange E).L.U fun _ => i)
      (fun y hy => Set.mem_iInter.1 hy PUnit.unit) (homOfLE hle').op
    have b := (S.bcFst E).map_appLE (U := W) (V := S.bcFst E ⁻¹ᵁ W) le_rfl (homOfLE hle).op
    exact congrArg (fun g => g.hom ((S.b j).f i)) (a.trans b.symm)
  have e₂ := congrArg Λ e
  rw [map_zero, map_sum] at e₂
  refine (resG_chartEval k S.b i le_rfl hle _).trans (Eq.trans ?_ (e₂.trans (map_zero _).symm))
  rw [coeffMap, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [chartEval, eval₂Hom_monomial]
  refine Eq.trans (hΛ (coeff a g) (a.prod fun j n => resG S.Y hle ((S.b j).f i) ^ n)).symm (congrArg Λ ?_)
  refine congrArg₂ (· * ·) rfl ?_
  refine (map_prod ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom _ _).trans
    (Finset.prod_congr rfl fun j _ => ?_)
  exact (map_pow _ _ _).trans (congrArg (· ^ _) (e' j).symm)

theorem del_eq_zero (hp : IsProjOver S.str) (s : Fin S.D → S.L.Sec) (hs : ∀ y, ∃ i, y ∈ nonzeroLocus (s i)) :
    S.del = 0 := by
  have := isNoetherian_of_isProjOver hp
  have key := CutDegree.interNum_eq_sum_length S.str hp S.isLB S.chartAt S.mem_chartAt ∅ (by simp) (List.ofFn s)
    (structureModule S.Y) (fun x _ hx => by
      obtain ⟨i, hi⟩ := hs x
      exact (hx _ (List.mem_ofFn.2 ⟨i, rfl⟩) hi).elim) (by simp)
  have e : topSelfIntersection k S.L S.D = topSelfIntersection k S.L (List.ofFn s).length := by rw [List.length_ofFn]
  rw [LinSys.del, e, topSelf_def]
  exact key

variable {S}

theorem isIntegral (h : S.IsVariety) : IsIntegral S.Y := by
  have := h.smooth
  have := h.conn
  have : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  have := geometricallyIntegral_of_smooth S.str
  exact GeometricallyIntegral.isIntegral_of_subsingleton S.str

theorem exists_generic (h : S.IsVariety) : ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra k Ω) (x : S.Pt Ω),
    IsGenericPoint (ptOf x.1) Set.univ ∧ Algebra.trdeg k Ω = S.D := by
  have := isIntegral h
  have hg := genericPoint_spec S.Y
  refine ⟨S.Y.residueField (genericPoint S.Y), inferInstance, (S.baseHom (resPt _)).toAlgebra,
    ⟨resPt _, S.comp_str _⟩, by rw [ptOf_resPt]; exact hg, ?_⟩
  exact (residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth _
    fun y hy => (hy.antisymm (hg.specializes trivial)).eq).2

theorem map_imageIdeal (h : S.IsVariety) (E : Type) [Field E] [Algebra k E] :
    S.imageIdeal.map (MvPolynomial.map (algebraMap k E) : MvPolynomial (Fin S.N) k →+* MvPolynomial (Fin S.N) E) =
      (S.baseChange E).imageIdeal := by
  refine le_antisymm ?_ (Ideal.span_le.2 ?_)
  · have := isIntegral (h.baseChange E)
    obtain ⟨Ω, _, _, x, hx, -⟩ := exists_generic (h.baseChange E)
    let : Algebra k Ω := ((algebraMap E Ω).comp (algebraMap k E)).toAlgebra
    have : IsScalarTower k E Ω := .of_algebraMap_eq' rfl
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange E x.1
    rw [imageIdeal_eq_coneIdeal_of_generic E Ω _ x hx c _ hc e]
    refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
    rintro g ⟨d, hg, h0⟩
    refine (mem_coneIdeal_of_isHomogeneous _ (hg.map (algebraMap k E))).2 ?_
    have h1 := S.eval₂_coords_eq_zero (LinSys.toBase x).1 ((S.mem_imageIdeal_iff hg).2 h0)
    rw [LinSys.baseHom_ptOver] at h1
    exact (aeval_map_algebraMap E _ g).trans h1
  · rintro g ⟨d, hg, h0⟩
    exact mem_map_of_coeffMap
      (coeffMap_mem_imageIdeal S E hg (((S.baseChange E).mem_imageIdeal_iff hg).2 h0))

theorem isPrime_imageIdeal (h : S.IsVariety) : S.imageIdeal.IsPrime := by
  have := isIntegral h
  obtain ⟨Ω, _, _, x, hx, -⟩ := exists_generic h
  rw [imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm]
  exact isPrime_coneIdeal _

theorem del_eq_zero_of_lt [Infinite k] (hp : IsProjOver S.str) (hb : S.BasePointFree) {e δ : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin S.N) k} (hf : IsChowFormInt S.imageIdeal e δ f) (he : e < S.D) :
    S.del = 0 := by
  obtain ⟨u, hu⟩ : ∃ u, eval u f ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf.ne_zero (MvPolynomial.funext fun u => by rw [hc, map_zero])
  refine del_eq_zero S hp (fun i => if hi : (i : ℕ) < e + 1 then S.comb fun j => u (⟨i, hi⟩, j) else 0) fun y => ?_
  by_contra hc
  push Not at hc
  let Ω := AlgebraicClosure (S.Y.residueField y)
  let x : Sp Ω ⟶ S.Y := spMap (algebraMap (S.Y.residueField y) Ω) ≫ resPt y
  have hx : ptOf x = y := (ptOf_spMap_comp _ _).trans (ptOf_resPt y)
  let : Algebra k Ω := (S.baseHom x).toAlgebra
  have h1 := (hf.zero_iff_of_isAlgClosed S.isHomogeneous_imageIdeal fun p => algebraMap k Ω (u p)).2
    ⟨S.coords x, hb.coords_ne_zero x, fun g hg => S.eval₂_coords_eq_zero x hg, fun i => by
      have h2 := hc ⟨i, by omega⟩
      rw [dif_pos i.2, ← hx, ← S.val_ne_zero_iff, not_not, S.val_comb] at h2
      exact h2⟩
  exact hu ((map_eq_zero (algebraMap k Ω)).1 ((aeval_algebraMap_apply Ω u f).symm.trans h1))

theorem ringKrullDim_imageIdeal [CharZero k] (h : S.IsVariety) (hb : S.BasePointFree) (hd : S.del ≠ 0) :
    ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = (S.D + 1 : ℕ) := by
  have := isIntegral h
  have hp := isPrime_imageIdeal h
  obtain ⟨Ω, _, _, x, hx, hD⟩ := exists_generic h
  have hI := imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero x.1)
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ S.isHomogeneous_imageIdeal (i := j)
    fun hX => hj (by simpa using S.eval₂_coords_eq_zero x.1 hX)
  obtain ⟨f, hf⟩ := ChowExists.exists_isChowFormInt hp S.isHomogeneous_imageIdeal he
  obtain rfl : e = S.D := le_antisymm (le_of_ringKrullDim_coneIdeal _ hD (hI ▸ he))
    (not_lt.1 fun hlt => hd (del_eq_zero_of_lt h.proj hb hf hlt))
  exact he

theorem exists_isChowForm [CharZero k] (h : S.IsVariety) (hb : S.BasePointFree) (hd : S.del ≠ 0) :
    ∃ f, IsChowForm S.imageIdeal S.D (hilbertDegree S.imageIdeal) f :=
  ChowExists.exists_isChowForm S.isHomogeneous_imageIdeal
    (by rw [map_imageIdeal h]; exact isPrime_imageIdeal (h.baseChange _)) (ringKrullDim_imageIdeal h hb hd)

theorem exists_isHeight : ∀ (F : Type) [Field F] [NumberField F] (T : HermSys F),
    T.IsAlgebraicData → 0 < T.del → ∃ h, T.IsHeight h := fun _ _ _ T h hd =>
  have ⟨_, hf⟩ := exists_isChowForm h.variety h.bpf hd.ne'
  ⟨_, T.isHeight_of_isChowForm hf⟩

end GlobalTheory.Adelic.HeightExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlobalSectionsDimNefPowTensorAmpleIsBiStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbH0_nef_pow_tens_ample_le_mul_pow_dim : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] (Z : Scheme.{0}) [Algebra F Γ(Z, ⊤)] (d : ℕ), IsProjOver (strHom F Z) → topologicalKrullDim Z ≤ d → ∀ L A : LB Z, IsNef F L → IsAmpleLB A → ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ C * (m : ℝ) ^ d := by
  first | exact @GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO | exact GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO | (intros; apply GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberAmpleConsNefNonnegStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_ample_cons_nef_nonneg : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) → ∀ A : LB X, IsAmpleLB A → (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) := by
  first | exact @GlobalTheory.interNum_cons_ample_nef_nonneg | exact GlobalTheory.interNum_cons_ample_nef_nonneg | (intros; apply GlobalTheory.interNum_cons_ample_nef_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberNonnegOfAmpleStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_nonneg_of_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F P := by
  first | exact @GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver | exact GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver | (intros; apply GlobalTheory.interNum_nonneg_of_isAmpleLB_of_isProjOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqOfWeylAntisymmetrizationEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem linForm_eq_of_antisymm_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  intro ι _ m L hL Q Q' h
  have sq : ∀ u : ℤˣ, ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
    intro u
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have key : ∀ P : MvPolynomial (Root m) ℝ,
      L (antisymm P) = (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) * L P := by
    intro P
    simp only [GlobalTheory.GoodMetric.antisymm, map_sum, map_zsmul]
    rw [Finset.sum_congr rfl (fun w _ => by
      rw [GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks ι m L hL w P, zsmul_eq_mul, ← mul_assoc, sq, one_mul])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ∀ τ, Equiv.Perm (Fin (m τ)))).ne'
  have e := congrArg L h
  rw [key, key] at e
  exact mul_left_cancel₀ hc e

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDetPowIntegerMatricesFinite
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.GJInt

theorem det_blk {k : Type} [Field k] {n : ℕ} (x : k) (u v : Fin n → k) (M : Matrix (Fin n) (Fin n) k) :
    (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det =
      x * M.det + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det := by
  rw [det_succ_row_zero, det_succ_row_zero (Matrix.of _), Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Matrix.submatrix]
  exact Or.inl rfl

theorem mem_intM_blk {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (x : k) (u v : Fin n → k) (M : Matrix (Fin n) (Fin n) k) :
    Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))) ∈ intM k (Fin (n + 1)) (Fin (n + 1)) ↔
      x ∈ 𝒪[k] ∧ (∀ j, u j ∈ 𝒪[k]) ∧ (∀ i, v i ∈ 𝒪[k]) ∧ M ∈ intM k (Fin n) (Fin n) := by
  simp only [intM, Set.mem_setOf_eq, Fin.forall_fin_succ, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, forall_and]
  tauto

theorem det_mem_int {k : Type} [Field k] [ValuativeRel k] {n : ℕ} {X : Matrix (Fin n) (Fin n) k}
    (hX : X ∈ intM k (Fin n) (Fin n)) : X.det ∈ 𝒪[k] := by
  have h1 := (𝒪[k].subtype).map_det (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k]))
  have h2 : (𝒪[k].subtype).mapMatrix (fun i j => (⟨X i j, hX i j⟩ : 𝒪[k])) = X := by ext; rfl
  rw [h2] at h1
  rw [← h1]
  exact SetLike.coe_mem _

theorem intdet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (n : ℕ) (s : ℝ), -1 < s →
    ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
  intro k _ _ _ _ _ _ μ _ n s hs
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hOm : MeasurableSet (𝒪[k] : Set k) := GlobalTheory.SplitWeil.Model.isOpen_int.measurableSet
  have hO : μ (𝒪[k] : Set k) ≠ ⊤ := GlobalTheory.SplitWeil.Model.isCompact_int.measure_lt_top.ne
  set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP
  show ∫⁻ X, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ∂(volM μ (Fin n) (Fin n)) < ⊤
  rcases le_or_gt 0 s with hs0 | hs0
  · have hb : ∀ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) X ≤
        (intM k (Fin n) (Fin n)).indicator 1 X := by
      intro X
      by_cases hX : X ∈ intM k (Fin n) (Fin n)
      · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX]
        have hdet := det_mem_int hX
        simp only [P, Pi.one_apply]
        split_ifs with h
        · rcases hs0.eq_or_lt with h0 | h0
          · simp [← h0]
          · simp [ENNReal.zero_rpow_of_pos h0]
        · exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.2 (GlobalTheory.SplitWeil.Model.nabs_le_one _ hdet)) hs0
      · simp [Set.indicator_of_notMem hX]
    have hint : intM k (Fin n) (Fin n) = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (𝒪[k] : Set k) : Set (Fin n → Fin n → k)) := by
      ext X; exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    have hm : MeasurableSet (intM k (Fin n) (Fin n)) := by
      rw [hint]; exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hOm
    calc _ ≤ ∫⁻ X, (intM k (Fin n) (Fin n)).indicator 1 X ∂(volM μ (Fin n) (Fin n)) := lintegral_mono hb
      _ = volM μ (Fin n) (Fin n) (intM k (Fin n) (Fin n)) := lintegral_indicator_one hm
      _ < ⊤ := by
        rw [hint, volM]; erw [Measure.pi_pi]
        simp only [Measure.pi_pi]
        exact ENNReal.prod_lt_top fun _ _ => ENNReal.prod_lt_top fun _ _ => hO.lt_top
  · set K : ℝ≥0∞ := ∫⁻ x, (𝒪[k] : Set k).indicator P x ∂μ + μ (𝒪[k] : Set k) with hK
    have hKt : K ≠ ⊤ := ENNReal.add_ne_top.2 ⟨(GlobalTheory.T.lintegral_abs_pow_integers_finite k μ s hs).ne, hO⟩
    induction n with
    | zero =>
      calc _ ≤ ∫⁻ X, 1 ∂(volM μ (Fin 0) (Fin 0)) := lintegral_mono fun X => ?_
        _ < ⊤ := by rw [lintegral_one, volM]; erw [Measure.pi_univ]; simp
      by_cases hX : X ∈ intM k (Fin 0) (Fin 0)
      · rw [Set.indicator_of_mem hX]
        simp [P, GlobalTheory.SplitWeil.Model.nabs_one]
      · simp [Set.indicator_of_notMem hX]
    | succ n ih =>
      let U : Set (Fin n → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
      have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => hOm
      have hUv : (Measure.pi fun _ : Fin n => μ) U = μ 𝒪[k] ^ n := by simp [U, Measure.pi_pi]
      have hUt : μ 𝒪[k] ^ n ≠ ⊤ := ENNReal.pow_ne_top hO
      set I := fun M : Matrix (Fin n) (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun Y => P Y.det) M with hI
      have inner : ∀ M v u, ∫⁻ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
          (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) ∂μ ≤
          U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u := by
        intro M v u
        by_cases h : u ∈ U ∧ v ∈ U ∧ M ∈ intM k (Fin n) (Fin n)
        · obtain ⟨hu, hv, hM⟩ := h
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hv]
          simp only [I, Set.indicator_of_mem hM]
          have he : ∀ x, (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
              (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))) =
              (𝒪[k] : Set k).indicator (fun y => P (M.det * y + (Matrix.of (Fin.cons (Fin.cons 0 u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))).det)) x := by
            intro x
            by_cases hx : x ∈ (𝒪[k] : Set k)
            · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((mem_intM_blk x u v M).2 ⟨hx, fun j => hu j trivial, fun i => hv i trivial, hM⟩), det_blk, mul_comm x]
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((mem_intM_blk x u v M).1 h).1)]
          simp_rw [he]
          refine (GlobalTheory.T.lintegral_affine_abs_pow_bound k μ s hs0 M.det _).trans (le_of_eq ?_)
          rw [mul_comm]
        · rw [show (fun x => (intM k (Fin (n + 1)) (Fin (n + 1))).indicator (fun Y => P Y.det)
              (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))) = fun _ => 0 from ?_]
          · simp
          funext x
          refine Set.indicator_of_notMem (fun hx => h ?_) _
          obtain ⟨_, hu, hv, hM⟩ := (mem_intM_blk x u v M).1 hx
          exact ⟨fun j _ => hu j, fun i _ => hv i, hM⟩
      calc _ ≤ _ := GlobalTheory.T.lintegral_matrix_first_row_column k μ n _
        _ ≤ ∫⁻ M, ∫⁻ v, ∫⁻ u, U.indicator (fun _ => U.indicator (fun _ => K * I M) v) u
              ∂(Measure.pi fun _ : Fin n => μ) ∂(Measure.pi fun _ : Fin n => μ) ∂(volM μ (Fin n) (Fin n)) :=
            lintegral_mono fun M => lintegral_mono fun v => lintegral_mono fun u => inner M v u
        _ = ∫⁻ M, K * I M * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) ∂(volM μ (Fin n) (Fin n)) := by
            refine lintegral_congr fun M => ?_
            simp_rw [lintegral_indicator_const hU, hUv]
            rw [lintegral_mul_const' _ _ hUt, lintegral_indicator_const hU, hUv, mul_assoc]
        _ = K * (∫⁻ M, I M ∂(volM μ (Fin n) (Fin n))) * (μ 𝒪[k] ^ n * μ 𝒪[k] ^ n) := by
            rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hUt hUt), lintegral_const_mul' _ _ hKt]
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hKt.lt_top ih) (ENNReal.mul_lt_top hUt.lt_top hUt.lt_top)

end GlobalTheory.GJInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfHeisenbergInvariantNormsStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_eq_of_heisenbergInvariant_norms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ), ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f f' : BBF σ JS JT ξ₀ ψ,
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : BBF σ JS JT ξ₀ ψ →L[ℂ] H),
        (∀ w g, ‖Φ (rhoBF σ JS JT ξ₀ ψ hψ w g)‖ = ‖Φ g‖) → ‖Φ f'‖ = ‖Φ f‖) →
      ∫⁻ w in 𝓕, ‖f'.1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f.1 w‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.RealWeilF.lintegral_eq_of_normsF | exact GlobalTheory.RealWeilF.lintegral_eq_of_normsF | (intros; apply GlobalTheory.RealWeilF.lintegral_eq_of_normsF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvPowAddNormSqComplexSpaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_inv_pow_add_normSq_complexSpace : ∀ (n m : ℕ) (a : ℝ), 0 < a → ∫⁻ v : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖v i‖ ^ 2) ^ (n + m + 1))⁻¹) = ENNReal.ofReal (Real.pi ^ n * m.factorial / ((n + m).factorial * a ^ (m + 1))) := by
  first | exact @GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq | exact GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq | (intros; apply GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MuExist

def nsUnits (E : Type) [Field E] [NumberField E] [IsCMField E] : Subgroup (Neutral.B1.Ideles E) :=
  Subgroup.closure {x | ∃ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ GlobalTheory.UnitaryBC.IsSplitAt w ∧
    Valued.v (u : w.adicCompletion E) = 1 ∧ x = Neutral.B1.localIdele E w u}

theorem localIdele_mem_nsUnits {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (u : (w.adicCompletion E)ˣ) (hw : ¬ GlobalTheory.UnitaryBC.IsSplitAt w) (hu : Valued.v (u : w.adicCompletion E) = 1) :
    Neutral.B1.localIdele E w u ∈ nsUnits E :=
  Subgroup.subset_closure ⟨w, u, hw, hu, rfl⟩

end GlobalTheory.MuExist
end
end

