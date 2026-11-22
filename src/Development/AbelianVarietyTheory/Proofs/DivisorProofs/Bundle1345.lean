import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import GroundTheory.LocalFields.LocalFourierHaar
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionDistribHaarCharEqAbsHalfSq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ModAbs

theorem ordL_eq_ord {E : Type} [Field E] [NumberField E] (w : Pl E) {x : w.adicCompletion E} (hx : x ≠ 0) :
    ordL x = GroundTheory.LocalField.ord x := by
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord hx
  have hv : Valued.v x ≠ 0 := (Valued.v).ne_zero_iff.2 hx
  unfold ordL
  rw [dif_neg hv]
  have : WithZero.unzero hv = Multiplicative.ofAdd (-GroundTheory.LocalField.ord x) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h2]
    rfl
  rw [this, toAdd_ofAdd, neg_neg]

theorem haar_eq_absHalf_sq : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) (hx : x ≠ 0), (((MeasureTheory.distribHaarChar (w.adicCompletion E) (Units.mk0 x hx) : NNReal) : ℝ) : ℂ) = absHalf w x ^ 2 := by
  intro E _ _ w x hx
  have h1 := GroundTheory.LocalField.distribHaarChar_eq_modulus (K := w.adicCompletion E) (Units.mk0 x hx)
  have h3 : (GroundTheory.LocalField.residueCard (w.adicCompletion E)) = Ideal.absNorm w.asIdeal :=
    GroundTheory.Global.residueCard_adicCompletion
  rw [h1, Units.val_mk0, GroundTheory.LocalField.modulus_of_ne_zero hx, h3]
  unfold absHalf
  rw [ordL_eq_ord w hx]
  have hq : (0 : ℝ) ≤ ((qV E w : ℕ) : ℝ) ^ (-GroundTheory.LocalField.ord x) := zpow_nonneg (Nat.cast_nonneg _) _
  rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  simp [qV]

end GlobalTheory.ModAbs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicMorseExistsSectionAmpleSubGeneratedStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_morse_exists_section_ample_sub_generated : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  first | exact @GlobalTheory.exists_sec_of_ample_sub_generated | exact GlobalTheory.exists_sec_of_ample_sub_generated | (intros; apply GlobalTheory.exists_sec_of_ample_sub_generated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingMapDetFiltrationWithSymbols
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.FiltDet

theorem alt_linComb {E A' : Type} [Field E] [AddCommGroup A'] [Module E A'] {d : ℕ}
    (ω : A' [⋀^Fin d]→ₗ[E] E) (z : Fin d → A') (N : Fin d → Fin d → E) :
    ω (fun j => Fintype.linearCombination E z (N j)) = (Matrix.of N).det * ω z := by
  classical
  have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun E (Fin d))
    (ω.compLinearMap (Fintype.linearCombination E z))
  have e1 : (fun i => Fintype.linearCombination E z (Pi.basisFun E (Fin d) i)) = z := by
    funext i; simp [Fintype.linearCombination_apply_single]
  have h2 : ω (fun j => Fintype.linearCombination E z (N j)) =
      (ω.compLinearMap (Fintype.linearCombination E z)) N := rfl
  rw [h2, h, AlternatingMap.smul_apply, Pi.basisFun_det,
    AlternatingMap.compLinearMap_apply, e1, smul_eq_mul, mul_comm]
  rfl

theorem det_filtration_symbols : ∀ (E A' : Type) [Field E] [AddCommGroup A'] [Module E A'] (r d : ℕ) (I : Fin r → Type) [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)] (U : ℕ → Submodule E A') (sym : ∀ a : Fin r, U a →ₗ[E] (I a → E)), (∀ a < r, U (a + 1) ≤ U a) → (∀ (a : Fin r) (x : U a), sym a x = 0 ↔ x.1 ∈ U (a + 1)) → ∀ (ix : (Σ a, I a) ↪ Fin d) (J : Finset (Fin d)) (v : Fin d → A') (hv : ∀ q, v (ix q) ∈ U q.1), (∀ k ∈ J, k ∉ Set.range ix ∧ v k ∈ U r) → ∀ [FiniteDimensional E (U r)], Module.finrank E (U r) ≤ J.card → ∀ (z : Fin d → A') (hz : ∀ q, z (ix q) ∈ U q.1), (∀ q, sym q.1 ⟨z (ix q), hz q⟩ = Pi.single q.2 1) → (∀ k, k ∉ Set.range ix → z k = v k) → ∀ ω : A' [⋀^Fin d]→ₗ[E] E, ω v = (∏ a, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det) * ω z := by
  intro E A' _ _ _ r d I _ _ U sym hdec hsym ix J v hv hJ _ hcard z hz hzs hzv ω
  classical

  have step : ∀ (a : Fin r) (x : A') (hx : x ∈ U a),
      x - ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U (a + 1) := by
    intro a x hx
    have hzs' : ∀ i, sym a ⟨z (ix ⟨a, i⟩), hz ⟨a, i⟩⟩ = Pi.single i 1 := fun i => hzs ⟨a, i⟩
    have hmem : ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U a :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz ⟨a, i⟩)
    have hy : x - ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U a := Submodule.sub_mem _ hx hmem
    refine (hsym a ⟨_, hy⟩).1 ?_
    have : (⟨_, hy⟩ : U a) = ⟨x, hx⟩ - ∑ i, sym a ⟨x, hx⟩ i • ⟨z (ix ⟨a, i⟩), hz ⟨a, i⟩⟩ := by
      ext; simp
    rw [this, map_sub, map_sum]
    simp only [map_smul, hzs']
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨β, hβix, hβout⟩ : ∃ β : Fin d → ℕ, (∀ q, β (ix q) = q.1) ∧
      (∀ k, k ∉ Set.range ix → β k = r) := by
    refine ⟨fun k => if h : k ∈ Set.range ix then ((Classical.choose h).1 : ℕ) else r, ?_, ?_⟩
    · intro q
      have h : ix q ∈ Set.range ix := ⟨q, rfl⟩
      simp only [dif_pos h]
      rw [ix.injective (Classical.choose_spec h)]
    · intro k hk; simp only [dif_neg hk]
  have hβle : ∀ k, β k ≤ r := by
    intro k
    by_cases hk : k ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hk; rw [hβix]; exact q.1.isLt.le
    · rw [hβout k hk]
  have conv : ∀ (S : Set (Fin d)) (x : A'), x ∈ Submodule.span E (z '' S) →
      ∃ c : Fin d → E, (∀ k ∉ S, c k = 0) ∧ Fintype.linearCombination E z c = x := by
    intro S x hx
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hx
    refine ⟨l, fun k hk => (Finsupp.mem_supported' E l).1 hl k hk, ?_⟩
    rw [Fintype.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  by_cases hli : LinearIndependent E (fun k : J => v k)
  swap
  · have h1 : ¬ LinearIndependent E v := fun h => hli (h.comp _ Subtype.val_injective)
    have h2 : ¬ LinearIndependent E z := by
      intro h; apply hli
      have : (fun k : J => v k) = z ∘ Subtype.val := by
        funext k; exact (hzv k.1 (hJ k.1 k.2).1).symm
      rw [this]; exact h.comp _ Subtype.val_injective
    rw [ω.map_linearDependent v h1, ω.map_linearDependent z h2, mul_zero]
  have hspan : U r ≤ Submodule.span E (Set.range fun k : J => v k) := by
    have hle : Submodule.span E (Set.range fun k : J => v k) ≤ U r := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact (hJ k.1 k.2).2
    refine (Submodule.eq_of_le_of_finrank_le hle ?_).ge
    rw [finrank_span_eq_card hli, Fintype.card_coe]; exact hcard
  have hdown : ∀ n a, a + n = r → U a ≤ Submodule.span E (z '' {k | a ≤ β k}) := by
    intro n
    induction n with
    | zero =>
      intro a ha
      obtain rfl : a = r := by omega
      refine hspan.trans (Submodule.span_mono ?_)
      rintro _ ⟨k, rfl⟩
      refine ⟨k.1, ?_, hzv k.1 (hJ k.1 k.2).1⟩
      simp [hβout k.1 (hJ k.1 k.2).1]
    | succ n ih =>
      intro a ha x hx
      have har : a < r := by omega
      have key := step ⟨a, har⟩ x hx
      have hy := ih (a + 1) (by omega) key
      have hmono : Submodule.span E (z '' {k | a + 1 ≤ β k}) ≤
          Submodule.span E (z '' {k | a ≤ β k}) :=
        Submodule.span_mono (Set.image_mono fun k hk => by
          simp only [Set.mem_setOf_eq] at hk ⊢; omega)
      have hsum : ∑ i, sym ⟨a, har⟩ ⟨x, hx⟩ i • z (ix ⟨⟨a, har⟩, i⟩) ∈
          Submodule.span E (z '' {k | a ≤ β k}) := by
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨ix ⟨⟨a, har⟩, i⟩, ?_, rfl⟩)
        simp [hβix]
      have := Submodule.add_mem _ (hmono hy) hsum
      simpa using this
  have hcol : ∀ q : (Σ a, I a), ∃ col : Fin d → E, Fintype.linearCombination E z col = v (ix q) ∧
      (∀ k, β k < q.1 → col k = 0) ∧
      ∀ i, col (ix ⟨q.1, i⟩) = sym q.1 ⟨v (ix q), hv q⟩ i := by
    rintro ⟨a, i'⟩
    have key := step a (v (ix ⟨a, i'⟩)) (hv ⟨a, i'⟩)
    have hy := hdown (r - (a + 1)) (a + 1) (by omega) key
    obtain ⟨c, hc0, hcL⟩ := conv _ _ hy
    refine ⟨c + ∑ i, sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i • Pi.single (ix ⟨a, i⟩) 1, ?_, ?_, ?_⟩
    · rw [map_add, map_sum, hcL]
      simp only [map_smul, Fintype.linearCombination_apply_single, one_smul]
      abel
    · intro k hk
      have hk' : β k < a := hk
      have h1 : c k = 0 := hc0 k (by simp only [Set.mem_setOf_eq, not_le]; omega)
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, h1, zero_add]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hne : k ≠ ix ⟨a, i⟩ := by
        rintro rfl; rw [hβix] at hk'; exact lt_irrefl _ hk'
      simp [Pi.single_apply, hne]
    · intro i
      have h1 : c (ix ⟨a, i⟩) = 0 := hc0 _ (by simp [hβix])
      simp [h1, Finset.sum_apply, Pi.single_apply, Sigma.mk.inj_iff]
  choose col hcolL hcol0 hcoldiag using hcol
  obtain ⟨N, hNix, hNout⟩ : ∃ N : Matrix (Fin d) (Fin d) E, (∀ q, N (ix q) = col q) ∧
      (∀ k, k ∉ Set.range ix → N k = Pi.single k 1) := by
    refine ⟨Matrix.of fun k => if h : k ∈ Set.range ix then col (Classical.choose (Set.mem_range.1 h))
      else Pi.single k 1, ?_, ?_⟩
    · intro q
      have h : ix q ∈ Set.range ix := ⟨q, rfl⟩
      funext j
      simp only [Matrix.of_apply, dif_pos h]
      rw [ix.injective (Classical.choose_spec (Set.mem_range.1 h))]
    · intro k hk; funext j; simp only [Matrix.of_apply, dif_neg hk]
  have hNL : ∀ j, Fintype.linearCombination E z (N j) = v j := by
    intro j
    by_cases hj : j ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hj; rw [hNix]; exact hcolL q
    · rw [hNout j hj, Fintype.linearCombination_apply_single, one_smul]; exact hzv j hj
  have hBT : N.BlockTriangular β := by
    intro i j hij
    by_cases hi : i ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hi; rw [hNix]; exact hcol0 q j (by rw [hβix] at hij; exact hij)
    · rw [hNout i hi, Pi.single_apply, if_neg]; rintro rfl; exact lt_irrefl _ hij
  have hdet : N.det = ∏ a : Fin r,
      (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det := by
    rw [hBT.det]
    have himg : Finset.image β Finset.univ ⊆ Finset.range (r + 1) := by
      intro b hb
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hb
      simp only [Finset.mem_range]; have := hβle k; omega
    rw [Finset.prod_subset himg ?_]
    · rw [Finset.prod_range_succ]
      have hlast : (N.toSquareBlock β r).det = 1 := by
        have : N.toSquareBlock β r = 1 := by
          ext ⟨i, hi⟩ ⟨j, hj⟩
          have hi' : i ∉ Set.range ix := by
            rintro ⟨q, rfl⟩; rw [hβix] at hi; have := q.1.isLt; omega
          rw [Matrix.toSquareBlock_def, Matrix.of_apply, hNout i hi', Pi.single_apply,
            Matrix.one_apply]
          simp only [Subtype.mk.injEq, eq_comm]
        rw [this, Matrix.det_one]
      rw [hlast, mul_one, ← Fin.prod_univ_eq_prod_range (fun x => (N.toSquareBlock β x).det) r]
      refine Finset.prod_congr rfl fun a _ => ?_
      have hinj : Function.Injective
          (fun i : I a => (⟨ix ⟨a, i⟩, hβix _⟩ : {k // β k = (a : ℕ)})) := by
        intro i i' h
        simp only [Subtype.mk.injEq, ix.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq,
          true_and] at h
        exact h
      have hsurj : Function.Surjective
          (fun i : I a => (⟨ix ⟨a, i⟩, hβix _⟩ : {k // β k = (a : ℕ)})) := by
        rintro ⟨k, hk⟩
        by_cases hkr : k ∈ Set.range ix
        · obtain ⟨⟨b, i⟩, rfl⟩ := hkr
          rw [hβix] at hk
          have hab : b = a := Fin.ext hk
          subst hab
          exact ⟨i, rfl⟩
        · rw [hβout k hkr] at hk; have := a.isLt; omega
      let e := Equiv.ofBijective _ ⟨hinj, hsurj⟩
      show (N.toSquareBlock β a).det = _
      rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose]
      congr 1
      ext i i'
      show N (ix ⟨a, i'⟩) (ix ⟨a, i⟩) = _
      rw [hNix]
      exact hcoldiag ⟨a, i'⟩ i
    · intro b _ hb
      haveI : IsEmpty {i // β i = b} :=
        ⟨fun ⟨i, hi⟩ => hb (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)⟩
      exact Matrix.det_isEmpty
  have hv' : v = fun j => Fintype.linearCombination E z (N j) := funext fun j => (hNL j).symm
  rw [show ω v = ω (fun j => Fintype.linearCombination E z (N j)) from congrArg _ hv',
]
  refine (alt_linComb ω z N).trans ?_
  rw [← hdet]
  rfl

end GlobalTheory.FiltDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleTopSelfIntersectionPosStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_lineBundle_top_selfIntersection_pos : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X = (d : ℕ) → ∀ A : LB X, IsAmpleLB A → 0 < topSelfIntersection k A d := by
  first | exact @GlobalTheory.AmplePos.topSelf_pos | exact GlobalTheory.AmplePos.topSelf_pos | (intros; apply GlobalTheory.AmplePos.topSelf_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchUnipotentRadicalMemStatement
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.TorFin
open GlobalTheory.Orb (archMat)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_unipotent_radical_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x : Fin n → E) (w : InfinitePlace F) (τ : EmbOver E w) (y : GArch σ J w), archMat σ J τ y - 1 ∈ nilRad (J.map τ.1) (fun i => τ.1 (x i)) → embArch σ J w y ∈ unipRad σ J (Matrix.of fun i (_ : Fin 1) => x i) := by
  first | exact @GlobalTheory.TorFin.embArch_mem_unipRad_of_nilRad | exact GlobalTheory.TorFin.embArch_mem_unipRad_of_nilRad | (intros; apply GlobalTheory.TorFin.embArch_mem_unipRad_of_nilRad <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithGlobalMaximumPrincipleOffDivisorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_global_maximum_principle_off_divisor : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ρ ≤ P.nu 0 1 σ y s → P.nu N 0 σ y f ≤ R) → f ∈ P.Bl N 0 (Real.exp (δ * N) * R) := by
  first | exact @GlobalTheory.VolBr.max_principle_global | exact GlobalTheory.VolBr.max_principle_global | (intros; apply GlobalTheory.VolBr.max_principle_global <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendstoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a b M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => P.lc (m * a) (m * b) (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α / (D + 1).factorial + ((D + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  first | exact @GlobalTheory.VolBr.lc_tendsto_of_rep | exact GlobalTheory.VolBr.lc_tendsto_of_rep | (intros; apply GlobalTheory.VolBr.lc_tendsto_of_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjectionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersectionCalculus_of_form_mixed_projection : GlobalTheory.Published.ArFormExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.HeightProjection → GlobalTheory.Published.ArCalc := by
  first | exact @GlobalTheory.Published.arCalc_of_form_mix_projection | exact GlobalTheory.Published.arCalc_of_form_mix_projection | (intros; apply GlobalTheory.Published.arCalc_of_form_mix_projection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSmallSectionsEncardMulLeFiniteLevelStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_small_sections_encard_mul_le_finite_level : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ), (P.Bl N m 1).Finite → (P.Bl N m 1).encard * (P.Bl 0 (b * N) 1).encard ≤ {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2}.encard * (P.Bl 0 (b * N + m) 2).encard := by
  first | exact @GlobalTheory.VolBr.encard_mul_le_at_level | exact GlobalTheory.VolBr.encard_mul_le_at_level | (intros; apply GlobalTheory.VolBr.encard_mul_le_at_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicRepIsobaricDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HostBC

theorem spehSat_eq (q d : ℕ) (B : Multiset ℂˣ) : GlobalTheory.SphGal.spehSat q d B =
    ∑ k : Fin d, B.map (fun z : ℂˣ => (z : ℂ) * (q : ℂ) ^ (((d : ℂ) - 1) / 2 - (k : ℕ))) := by
  unfold GlobalTheory.SphGal.spehSat
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => Multiset.map_congr rfl fun z _ => ?_
  have hk : ((k.rev : ℕ) : ℂ) = d - (k + 1) := by
    rw [Fin.val_rev, Nat.cast_sub (Nat.succ_le_of_lt k.2)]
    push_cast
    rfl
  simp only [Fin.revPerm_apply, hk]
  congr 2
  ring

theorem bcPar_eq (n : ℕ) (α : Fin (n / 2) → ℂˣ) :
    bcPar n (fun i => (α i : ℂ)) = (GlobalTheory.LGrp.bcParam n α).map (fun z : ℂˣ => (z : ℂ)) := by
  simp [bcPar, GlobalTheory.LGrp.bcParam, Multiset.map_add, Multiset.map_map, Function.comp_def, Multiset.map_replicate]

end GlobalTheory.HostBC

namespace GlobalTheory.HostBC

open GlobalTheory.DiscSpec GlobalTheory.DefiniteBC

theorem sum_map_val {c : ℕ} (q : ℕ) (d : Fin c → ℕ) (B S : Fin c → Multiset ℂˣ)
    (h : ∀ i, ∑ k : Fin (d i), (B i).map (fun z : ℂˣ => (z : ℂ) * (q : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
      (S i).map (fun z : ℂˣ => (z : ℂ))) :
    (∑ i, S i).map (fun z : ℂˣ => (z : ℂ)) = ∑ i, GlobalTheory.SphGal.spehSat q (d i) (B i) := by
  refine (map_sum (Multiset.mapAddMonoidHom fun z : ℂˣ => (z : ℂ)) _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [spehSat_eq, h]
  rfl

end GlobalTheory.HostBC

namespace GlobalTheory.HostBC

open GlobalTheory.DiscSpec GlobalTheory.DefiniteBC

theorem baseChange_speh : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.DiscreteSpectrumGL →
    ∀ (D : D7) (n : ℕ),
    haveI := host_isCMField D.host
    ∀ U : Submodule ℂ (UA D.host.E n → ℂ), IsAutRepU U →
    ∃ (r : ℕ) (m d : Fin r → ℕ) (π : ∀ i, CuspSub D.host.E (m i)),
      (∀ i, 1 ≤ m i ∧ 1 ≤ d i ∧ (π i).IsCsd) ∧ ∑ i, m i * d i = n ∧
      (∀ (τ : D.host.E →+* ℂ) (lam : DomWeight n), HasWeightAt U τ lam → ∃ A A' : Fin r → Multiset ℂ,
        (∀ i, (π i).HasInfChar τ (A i) ∧ (π i).HasInfChar (ComplexEmbedding.conjugate τ) (A' i)) ∧
        ∑ i, GlobalTheory.SphGal.spehInf (d i) (A i) = infOfWeight lam ∧
        ∑ i, GlobalTheory.SphGal.spehInf (d i) (A' i) = (infOfWeight lam).map fun z => -z) ∧
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), IsUnramU U P → ∃ B : Fin r → Multiset ℂˣ,
        (∀ i, GlobalTheory.LFun.HasSatGL P ((π i).locRep P) (B i)) ∧
        (Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal →
          ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X)
            (ρ : Representation ℂ (GL (Fin n) (P.adicCompletion D.host.E)) X),
            IsCompAlong U (locU n P) ((cLoc P).comp (locU n P).subtype) ρ ∧ ∃ Bs : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL P ρ Bs ∧
              Bs.map (fun b : ℂˣ => (b : ℂ)) = ∑ i, GlobalTheory.SphGal.spehSat (Formalism.ConjugateSelfDual.normV P) (d i) (B i)) ∧
        (Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal →
          ∀ (σ : P.adicCompletion D.host.E →+* P.adicCompletion D.host.E) (ϖ : P.adicCompletion D.host.E) (q : ℕ),
            IsConjAt P σ → IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, HasSatAt U P σ ϖ q α →
              bcPar n (fun i => (α i : ℂ)) = ∑ i, GlobalTheory.SphGal.spehSat (Formalism.ConjugateSelfDual.normV P) (d i) (B i)) := by
  intro hNT hMW D n
  haveI := host_isCMField D.host
  intro U hU
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp,
      fun τ lam _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, by simp [infOfWeight], by simp [infOfWeight]⟩,
      fun Pl _ => ⟨Fin.elim0, fun i => i.elim0, fun _ => ?_, fun _ s ϖ q _ _ α _ => by simp [bcPar]⟩⟩
    have hT := GlobalTheory.LFun.Model.hasSatGL_trivial Pl 0
    have h0 : GlobalTheory.LFun.seg Pl 1 0 = 0 := Multiset.card_eq_zero.1 hT.card
    obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 hU.ne_bot
    have hone : ∀ x : UA D.host.E 0, x = 1 := fun x => Subtype.ext (Subsingleton.elim _ _)
    refine ⟨ℂ, _, _, Representation.trivial ℂ _ ℂ, ⟨(SmIrr.triv _).irred, LinearMap.toSpanSingleton ℂ _ φ,
      fun e => hφ0 (by simpa using LinearMap.congr_fun e 1), fun v => Submodule.smul_mem _ _ hφ, fun x v => ?_⟩,
      _, hT, by simp [h0]⟩
    rw [hone x.1]
    simp
  obtain ⟨c, N, h, V, σ, m, bc⟩ := hNT D.host.E (host_unramified D.host) n hn U hU
  choose a d P hPu hPn hPs using fun i => (hMW D.host.E (N i) (bc.pos i)).1 (V i) (bc.discrete i)
  have hNad : ∀ i, d i * a i = N i := fun i => (hPs i).mul_eq
  have hc : ∀ i, HasSpehComp (V i) (P i) (d i) := fun i =>
    (hMW D.host.E (N i) (bc.pos i)).2.2.2.2 (V i) (bc.discrete i) _ _ (P i) (hPn i) (hPs i)
  have hpos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i := fun i => by
    have h1 := bc.pos i
    rw [← hNad i] at h1
    exact ⟨Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at h1, Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at h1⟩
  choose ρ σ' hρ hσ' using fun i w => (hc i).exLoc w
  have hsp : ∀ i w, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ :=
    fun i w => (hc i).loc w (ρ i w) (σ i w) (hρ i w) (bc.loc i w)
  choose A hA1 hA2 using fun i τ => (hc i).inf τ
  have hmA : ∀ i τ, m i τ = GlobalTheory.SphGal.spehInf (d i) (A i τ) := fun i τ =>
    GlobalTheory.BcSpehProof.hasInfCharGL_unique (bc.discrete i).ne_bot (bc.inf i τ) (hA2 i τ)
  refine ⟨c, a, d, P, fun i => ⟨(hpos i).1, (hpos i).2,
    isCsd_of_isSpehOf hMW (bc.pos i) (bc.discrete i) (bc.csd i) (hPn i) (hPs i)⟩, ?_, ?_, ?_⟩
  · rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [← hNad i, mul_comm]
  · intro τ lam hl
    refine ⟨(A · τ), (A · (ComplexEmbedding.conjugate τ)), fun i => ⟨hA1 i τ, hA1 i _⟩, ?_, ?_⟩
    · rw [← bc.weight τ lam hl]
      exact Finset.sum_congr rfl fun i _ => (hmA i τ).symm
    · rw [← infOfWeight_dual, ← bc.weight _ _ (hasWeightAt_conjugate hn hl)]
      exact Finset.sum_congr rfl fun i _ => (hmA i _).symm
  · intro Pl hUn
    obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 (bc.unram Pl hUn)
    obtain ⟨S, hS, hfS⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (π := fun i => (σ i Pl).ρ) (fun i => (σ i Pl).smooth)
      (fun i => (σ i Pl).irred) hf hf0
    choose B hB hBS using fun i => GlobalTheory.SatInd.exists_sat_of_isSpeh (hpos i).2 (ρ i Pl).smooth (ρ i Pl).irred
      (hsp i Pl) (hS i)
    have key : (∑ i, S i).map (fun z : ℂˣ => (z : ℂ)) =
        ∑ i, GlobalTheory.SphGal.spehSat (Formalism.ConjugateSelfDual.normV Pl) (d i) (B i) := by
      rw [GlobalTheory.BlockVal.normV_eq_absNorm]
      exact sum_map_val _ d B S hBS
    refine ⟨B, fun i => (CG.hasSat_mk _ _ _).1 ((GlobalTheory.BcSpehCompare.hasSat_iff (hρ i Pl) _).2 (hB i)), fun hne => ?_,
      fun _ s ϖ q hs hUI α hα => ?_⟩
    · have hsplit : IsSplitAt Pl := isSplitAt_of_isSplitPl ((GlobalTheory.HeckeTieCompare.isSplitPl_iff Pl).2 hne)
      have hcomp := bc.split Pl hsplit
      have hsm : GlobalTheory.PRep.IsSmooth (locProd h Pl (σ · Pl)) := GlobalTheory.SmGL.isSmooth_parInd _ _
      obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible hsm hcomp.1 (bc.unram Pl hUn)
      refine ⟨_, _, _, _, hcomp, T, hT, ?_⟩
      rw [(hT.2 f hf hf0).unique hfS, key]
    · have hs' : ∀ x : D.host.E, s (algebraMap _ _ x) = algebraMap _ _ (IsCMField.complexConj D.host.E x) := hs
      have hI := bc.inert Pl s ϖ q hs' hUI α hα
      rw [bcPar_eq, (hI.2 f hf hf0).unique hfS, key]

end GlobalTheory.HostBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsoLocalUnitsCompOfPullbackSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections : ∀ (X Y' Y : Scheme.{0}) (b' : Y' ⟶ X) (β : Y ⟶ Y') (b : Y ⟶ X), β ≫ b' = b → ∀ (A : LB X) (H' : LB Y') (H : LB Y) (w' : LB.Iso H' (A.pull b')) (v : LB.Iso H (H'.pull β)) (w : LB.Iso H (A.pull b)) (ι : Type) (s : ι → LB.Sec A) (s' : ι → LB.Sec H') (s'' : ι → LB.Sec H), (∀ j, Rel b' w' (s j) (s' j)) → (∀ j, Rel β v (s' j) (s'' j)) → (∀ j, Rel b w (s j) (s'' j)) → (⨆ j, nonzeroLocus (s'' j) = ⊤) → ∀ z k k' k'', b z ∈ A.U k → β z ∈ H'.U k' → z ∈ H.U k'' → Geo.Tor.gw w (𝟙 _) z k k'' = Geo.Tor.gw w' β z k k' * Geo.Tor.gw v (𝟙 _) z k' k'' := by
  first | exact @GlobalTheory.FormalAlg.gw_comp_of_rel | exact GlobalTheory.FormalAlg.gw_comp_of_rel | (intros; apply GlobalTheory.FormalAlg.gw_comp_of_rel <;> assumption)
end

