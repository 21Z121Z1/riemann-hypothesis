import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEliminationFormGeneralLinearFormsCone
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem exists_elim_form_of_field : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime → (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) → ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K) (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 → (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  intro F _ _ D N d I g hD hI hhom hdim hg hgI
  obtain ⟨Q, hQ0, -, hQ⟩ := GlobalTheory.HSElim.exists_elim_form F D N d I g hD hI hhom hdim hg hgI
  refine ⟨Q, hQ0, ?_⟩
  intro K _ _ s y hy hyI hyg hlin
  classical
  let ey : Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun j => Sum.inr (Sum.inl j)
  let ez : Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun j => Sum.inr (Sum.inr j)
  let gens : Set (MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F) :=
    ((rename ey) '' (I : Set _) ∪ {rename ey g}) ∪
    (Set.range (fun i : Fin D => ∑ j, X (Sum.inl (i, j)) * X (ey j)) ∪ {∑ j, X (ez j) * X (ey j) - 1})
  let f := rename (Sum.inl : Fin D × Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) Q
  have hclos : ∀ x : (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) → AlgebraicClosure F,
      (∀ p ∈ Ideal.span gens, aeval x p = 0) → aeval x f = 0 := by
    intro x hx
    have h' : ∀ p ∈ gens, aeval x p = 0 := fun p hp => hx p (Ideal.subset_span hp)
    have hz : ∑ j, x (ez j) * x (ey j) = 1 := by
      have := h' _ (Or.inr (Or.inr rfl))
      simpa [sub_eq_zero] using this
    have hy0 : (fun j => x (ey j)) ≠ 0 := by
      intro h0
      have : ∑ j, x (ez j) * x (ey j) = 0 := by
        simp [show ∀ j, x (ey j) = 0 from fun j => congrFun h0 j]
      rw [hz] at this
      exact one_ne_zero this
    simp only [f, aeval_rename]
    exact hQ (AlgebraicClosure F) (fun i j => x (Sum.inl (i, j))) (fun j => x (ey j)) hy0
      (fun a ha => by
        have := h' _ (Or.inl (Or.inl ⟨a, ha, rfl⟩))
        simpa [aeval_rename, Function.comp_def] using this)
      (by
        have := h' _ (Or.inl (Or.inr rfl))
        simpa [aeval_rename, Function.comp_def] using this)
      (fun i => by
        have := h' _ (Or.inr (Or.inl ⟨i, rfl⟩))
        simpa using this)
  obtain ⟨j0, hj0⟩ : ∃ j0, y j0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy (funext hcon)
  let z : Fin N → K := fun j => if j = j0 then (y j0)⁻¹ else 0
  let x0 : (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) → K := Sum.elim (fun p => s p.1 p.2) (Sum.elim y z)
  have hx0 : ∀ p ∈ Ideal.span gens, aeval x0 p = 0 := by
    intro p hp
    have hle : Ideal.span gens ≤ RingHom.ker (aeval x0 : MvPolynomial _ F →ₐ[F] K) := by
      rw [Ideal.span_le]
      rintro q ((⟨a, ha, rfl⟩ | rfl) | (⟨i, rfl⟩ | rfl))
      · simpa [aeval_rename, Function.comp_def, x0, ey] using hyI a ha
      · simpa [aeval_rename, Function.comp_def, x0, ey] using hyg
      · simpa [x0, ey] using hlin i
      · simp [x0, ey, ez, z, hj0]
    exact hle hp
  have := GlobalTheory.T.vanish_transfer_of_vanish_over_algebraicClosure F ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) (Ideal.span gens) f hclos K x0 hx0
  simpa [f, aeval_rename, Function.comp_def, x0] using this

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormFiniteFibresBirationalLinearSystem
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BirFiniteFibre

open GlobalTheory.Points

theorem aeval_smul_of_isHomogeneous {F K σ : Type} [CommRing F] [CommRing K] [Algebra F K] {d : ℕ}
    {p : MvPolynomial σ F} (hp : p.IsHomogeneous d) (c : K) (y : σ → K) :
    aeval (c • y) p = c ^ d * aeval y p := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

theorem compactSpace_Y {F : Type} [Field F] (S : LinSys F) (h : S.IsVariety) : CompactSpace S.Y := by
  obtain ⟨n, i, hi, e⟩ := h.proj
  have := isProper_str F n
  have : IsProper S.str := e ▸ inferInstance
  exact ⟨by simpa using QuasiCompact.isCompact_preimage (f := S.str) Set.univ isOpen_univ isCompact_univ⟩

theorem exists_finset_separating {F : Type} [Field F] (S : LinSys F) (h : S.IsVariety) (W : S.Y.Opens)
    (hW : IsAffineOpen W) : ∃ s : Finset Γ(S.Y, W), ∀ (K : Type) [Field K] [Algebra F K] (x x' : S.Pt K),
      ptOf x.1 ∈ W → ptOf x'.1 ∈ W → (∀ a ∈ s, valR x.1 W a = valR x'.1 W a) → x = x' := by
  obtain ⟨n, i, hi, e⟩ := h.proj
  have := isProper_str F n
  have : IsProper S.str := e ▸ inferInstance
  have hle : W ≤ S.str ⁻¹ᵁ ⊤ := le_top
  have hft : (S.str.appLE ⊤ W hle).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) S.str inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ hle
  letI := (S.str.appLE ⊤ W hle).hom.toAlgebra
  obtain ⟨s, hs⟩ : Algebra.FiniteType Γ(Sp F, ⊤) Γ(S.Y, W) := hft
  refine ⟨s, fun K _ _ x x' hx hx' H => Subtype.ext ?_⟩
  have h1 := (le_iff_ptOf_mem _ _).2 hx
  have h2 := (le_iff_ptOf_mem _ _).2 hx'
  refine ext_of_valR hW h1 h2 fun f => ?_
  have hf : f ∈ Algebra.adjoin Γ(Sp F, ⊤) (s : Set Γ(S.Y, W)) := hs ▸ Algebra.mem_top
  induction hf using Algebra.adjoin_induction with
  | mem a ha => exact H a ha
  | algebraMap r =>
    exact (valR_appLE x.1 S.str hle h1 r).trans
      ((congrArg (fun q => valR q ⊤ r) (x.2.trans x'.2.symm)).trans (valR_appLE x'.1 S.str hle h2 r).symm)
  | add a b _ _ ha hb => rw [valR_add _ _ h1, valR_add _ _ h2, ha, hb]
  | mul a b _ _ ha hb => rw [valR_mul _ _ h1, valR_mul _ _ h2, ha, hb]

theorem exists_form_finite_fibres : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → ∃ (d : ℕ) (g : MvPolynomial (Fin S.N) F), g.IsHomogeneous d ∧ g ∉ S.imageIdeal ∧ ∀ (K : Type) [Field K] [Algebra F K] (y : Fin S.N → K), {x : S.Pt K | aeval (S.coords x.1) g ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y}.Finite := by
  intro F _ S hV hb hB
  classical
  haveI := compactSpace_Y S hV
  haveI := HeightExists.isPrime_imageIdeal hV
  have hcov : ∀ y : S.Y, ∃ W : S.Y.Opens, IsAffineOpen W ∧ y ∈ W := fun y => by
    obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
    exact ⟨W, hW, hy⟩
  choose W hW hy using hcov
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set S.Y)) (fun y => (W y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  choose s hs using fun z => exists_finset_separating S hV (W z) (hW z)
  choose d P Q hP hQ hQI _ hval using fun z a => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F S hV hb hB (W z) a
  refine ⟨∑ z ∈ t, ∑ a ∈ s z, d z a, ∏ z ∈ t, ∏ a ∈ s z, Q z a, ?_, ?_, fun K _ _ y => ?_⟩
  · exact IsHomogeneous.prod _ _ _ fun z _ => IsHomogeneous.prod _ _ _ fun a _ => hQ z a
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨z, -, hz⟩
    rw [Ideal.IsPrime.prod_mem_iff] at hz
    obtain ⟨a, -, ha⟩ := hz
    exact hQI z a ha
  · have key : ∀ z ∈ t, ∀ a ∈ s z, ∀ x : S.Pt K, ptOf x.1 ∈ W z →
        aeval (S.coords x.1) (∏ z ∈ t, ∏ a ∈ s z, Q z a) ≠ 0 → (∃ c : K, S.coords x.1 = c • y) →
        valR x.1 (W z) a = aeval y (P z a) / aeval y (Q z a) := by
      rintro z hz a ha x hx hg ⟨c, hc⟩
      have h1 : aeval (S.coords x.1) (Q z a) ≠ 0 := by
        rw [map_prod, Finset.prod_ne_zero_iff] at hg
        have := hg z hz
        rw [map_prod, Finset.prod_ne_zero_iff] at this
        exact this a ha
      have h2 := hval z a K x hx
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hb.coords_ne_zero x.1 (hc.trans (zero_smul _ _))
      rw [hc, aeval_smul_of_isHomogeneous (hQ z a)] at h1 h2
      rw [aeval_smul_of_isHomogeneous (hP z a), mul_left_comm] at h2
      rw [eq_div_iff (right_ne_zero_of_mul h1)]
      exact mul_left_cancel₀ (pow_ne_zero _ hc0) h2
    refine (t.finite_toSet.biUnion (t := fun z => {x : S.Pt K | ptOf x.1 ∈ W z ∧
      aeval (S.coords x.1) (∏ z ∈ t, ∏ a ∈ s z, Q z a) ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y})
      fun z hz => Set.Subsingleton.finite fun x hx x' hx' => ?_).subset fun x hx => ?_
    · exact hs z K x x' hx.1 hx'.1 fun a ha =>
        (key z hz a ha x hx.1 hx.2.1 hx.2.2).trans (key z hz a ha x' hx'.1 hx'.2.1 hx'.2.2).symm
    · obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (ptOf x.1)))
      exact Set.mem_iUnion₂.2 ⟨z, hz, hxz, hx⟩

end GlobalTheory.BirFiniteFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOutsideImageIdealVanishingOnBoundary
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BoundaryForm

theorem exists_local_fun {Y : Scheme.{0}} [IrreducibleSpace Y] (Z : TopologicalSpace.Closeds Y) (hZ : Z ≠ ⊤) (y : Y) :
    ∃ (W : Y.Opens) (a : Γ(Y, W)), y ∈ W ∧ a ≠ 0 ∧ ∀ z ∈ Y.basicOpen a, z ∉ Z := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hne : ((Z : Set Y)ᶜ).Nonempty := Set.nonempty_compl.2 fun h => hZ (SetLike.coe_injective h)
  obtain ⟨z, hzW, hzZ⟩ := nonempty_preirreducible_inter W.isOpen Z.isClosed.isOpen_compl ⟨y, hy⟩ hne
  obtain ⟨a, ha, hz⟩ := IsAffineOpen.exists_basicOpen_le hW (V := Z.compl) ⟨z, hzZ⟩ hzW
  refine ⟨W, a, hy, ?_, fun w hw => ha hw⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hz
  exact hz

theorem exists_form_vanishing : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∃ (d : ℕ) (g : MvPolynomial (Fin T.N) F), g.IsHomogeneous d ∧ g ∉ T.imageIdeal ∧
      ∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0 := by
  intro F _ _ T hG hB
  have hV := hG.alg.variety
  have := HeightExists.isIntegral hV
  have := isNoetherian_of_isProjOver hV.proj
  have hp := HeightExists.isPrime_imageIdeal hV
  choose W a hy ha hz using exists_local_fun T.bd hG.bd_ne
  choose d P Q hP _ _ hPn hval using fun y => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F T.toLinSys hV hG.alg.bpf hB (W y) (a y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set T.Y)) (fun y => (W y).isOpen)
    fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩
  refine ⟨∑ y ∈ s, d y, ∏ y ∈ s, P y, IsHomogeneous.prod s P d fun y _ => hP y, fun h => ?_, fun K _ _ x hx => ?_⟩
  · obtain ⟨y, -, h⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hPn y (ha y) h
  · obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ (ptOf x.1)))
    rw [map_prod]
    refine Finset.prod_eq_zero hys ?_
    have h0 : valR x.1 (W y) (a y) = 0 := by
      by_contra h
      exact hz y _ ((valR_ne_zero_iff x.1 hxy _).1 h) hx
    rw [← hval y K x hxy, h0, zero_mul]

end GlobalTheory.BoundaryForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCharpolyEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionEll

theorem exists_GL_charpoly_eq : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := by
  intro E _ _ n P hP
  obtain ⟨hm, hn, -, hr⟩ := hP
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : P.coeff 0 ≠ 0 := by
    intro h
    have hroot : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots (hm.map τ).ne_zero, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h, map_zero]
    have := hr τ 0 hroot
    simp at this
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) E, N.charpoly = P := by
    subst hn
    exact ⟨_, (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero)).trans
      (AdjoinRoot.minpoly_powerBasis_gen_of_monic hm)⟩
  have hd : IsUnit N.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hN]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0)
  exact ⟨((Matrix.isUnit_iff_isUnit_det N).mpr hd).unit, hN⟩

end GlobalTheory.CompanionEll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeightStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harmonic_highest_weight : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → ∀ (μ : Formalism.BasicNotions.TH.Ix R S → ℚ) (w : M.V), Formalism.BasicNotions.TH.IsHW M.act μ w → ∃ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec x (fun c => μ c - t) f := by
  first | exact @GlobalTheory.HarmLift.harm_lift | exact GlobalTheory.HarmLift.harm_lift | (intros; apply GlobalTheory.HarmLift.harm_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasNonzeroSecPowOfAmpleSubAmpleStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hasNonzeroSec_pow_of_ample_sub_ample' : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsAmpleLB B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  first | exact @GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample | exact GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample | (intros; apply GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndefiniteUnitaryLieAlgAddISmulEq
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem jm_conjTranspose (p q : ℕ) : (Formalism.BasicNotions.TH.Jm p q)ᴴ = Formalism.BasicNotions.TH.Jm p q := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_conjTranspose]
  simp

theorem jm_mul_self (p q : ℕ) : Formalism.BasicNotions.TH.Jm p q * Formalism.BasicNotions.TH.Jm p q = 1 := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem upq_span (p q : ℕ) (Z : Mat p q) : ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  obtain ⟨J, hJ⟩ : ∃ J, J = Formalism.BasicNotions.TH.Jm p q := ⟨_, rfl⟩
  have hJh : Jᴴ = J := hJ ▸ jm_conjTranspose p q
  have hJJ : J * J = 1 := hJ ▸ jm_mul_self p q
  refine ⟨(1/2 : ℂ) • (Z - J * Zᴴ * J), ?_, (-(Complex.I / 2)) • (Z + J * Zᴴ * J), ?_, ?_⟩
  · show _ = _
    rw [← hJ]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp [star_div₀]
    rw [this]
    module
  · show _ = _
    rw [← hJ]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [star_div₀]; ring
    rw [this]
    module
  · rw [smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]; ring
    rw [this]
    module

end GlobalTheory.HoweD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Chart (σ : E →ₐ[F] E) (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (v : Pl F) {L : Type} [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (JS : GL (Fin a') L)
    (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
    (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
    (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
    (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J) : Prop :=
  Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
  JS ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
  (∀ i j, σL ((JS : Matrix (Fin a') (Fin a') L) i j) = (JS : Matrix (Fin a') (Fin a') L) j i) ∧
  (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
  (Valued.v δ = 1 ∧ σL δ = -δ) ∧
  (∀ z ∈ Formalism.UG.intL L, σL z = z → ψL z = 1) ∧
  (∃ z ∈ Formalism.UG.intL L, σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
  (∀ x, At (evFin F v) (κ x)) ∧
  (∀ γ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) γ → ∃ x, κ x = γ) ∧
  (∀ x, (∀ i j, x i j ∈ Formalism.UG.intL L) ↔ κ x ∈ latAtV G.V' G.W v) ∧
  (∀ x y, ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) =
    B.ψ (⅟(2 : AF F) * symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (κ x) (κ y))) ∧
  (∀ g h x, actAB (cA σ) (ιS g, ιT h) (κ x) =
    κ (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
      (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L))) ∧
  (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) ∧ (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) ∧
  (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L),
    (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) → ιS g ∈ GlobalTheory.InertSph.KAt σ G.V' v) ∧
  (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
    (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ιT h ∈ GlobalTheory.InertSph.KAt σ G.W v)

end GlobalTheory.InertBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGeneratedStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_joint_shape_generated : ∀ (P Q R S : ℕ) (x t : ℚ) (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V), GlobalTheory.RealLift.IsLift x t M pr → Nontrivial M.V → ∃ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => x) μ' ∧ GlobalTheory.RealLift.GenBy M (fun c => μ' c + t) := by
  first | exact @GlobalTheory.RealLift.GenLift.genBy_of_isLift | exact GlobalTheory.RealLift.GenLift.genBy_of_isLift | (intros; apply GlobalTheory.RealLift.GenLift.genBy_of_isLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianSkewHermitianCompletionTensorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrangian_skewHermitian_completionTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F), IsField (Fv F v ⊗[F] E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Even n → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 →
    (∃ x : Fv F v ⊗[F] E, (1 : Fv F v) ⊗ₜ[F] J.det = x * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ x) →
    ∃ Cy : Matrix (Fin n) (Fin (n / 2)) (Fv F v ⊗[F] E),
      IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) J) Cy := by
  first | exact @GlobalTheory.SkewLagr.exists_isLagr_tensor | exact GlobalTheory.SkewLagr.exists_isLagr_tensor | (intros; apply GlobalTheory.SkewLagr.exists_isLagr_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalLiftSectionsOnClosedSubschemeStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_lift_sectionsOnClosedSubscheme : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (I : Y.IdealSheafData) (g : sectionsOnClosedSubscheme p B I) (y : Y), ∃ (W : Y.Opens) (_ : y ∈ W) (b : Vanishing.H0 p B W), ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ W) (j : (B.pull I.subschemeι).ι) (hj : z ∈ (B.pull I.subschemeι).U j), Vanishing.H0.germ j z (TopologicalSpace.Opens.mem_top z) hj g = (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) b) := by
  first | exact @GlobalTheory.Vanishing.exists_local_lift_H0On | exact GlobalTheory.Vanishing.exists_local_lift_H0On | (intros; apply GlobalTheory.Vanishing.exists_local_lift_H0On <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSectionConjStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_section_valuation_eq_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ u : Pl E, u ∉ S → ∃ w ∈ S, ∀ x : E, u.valuation E x = w.valuation E (IsCMField.complexConj E x) := by
  first | exact @GlobalTheory.BCT.exists_mem_section_conj | exact GlobalTheory.BCT.exists_mem_section_conj | (intros; apply GlobalTheory.BCT.exists_mem_section_conj <;> assumption)
end

