import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Inhabit
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPieceDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

namespace PieceDegreeAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [Algebra F Ω]

def rels (y : (Σ k, ι k) → Ω) (s : F →+* ℂ) : Set (MvPolynomial (Σ k, ι k) ℂ) :=
  {f | ∃ (d : K → ℕ) (g h : MRing ι) (θ : F), IsMultiHomog g d ∧ IsMultiHomog h d ∧
    aeval y g = algebraMap F Ω θ * aeval y h ∧
    f = MvPolynomial.map (Int.castRingHom ℂ) g - C (s θ) * MvPolynomial.map (Int.castRingHom ℂ) h}

def pieceIdeal (y : (Σ k, ι k) → Ω) (s : F →+* ℂ) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℂ)) ⊔ Ideal.span (rels y s)

omit [Fintype K] in

theorem zero_pieceIdeal_iff (y : (Σ k, ι k) → Ω) (s : F →+* ℂ) (z : (Σ k, ι k) → ℂ) :
    (∀ f ∈ pieceIdeal y s, eval z f = 0) ↔
      (∀ f ∈ mCoordIdeal y, eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0) ∧ LiesOver y s z := by
  have key : ∀ I : Ideal (MvPolynomial (Σ k, ι k) ℂ), (∀ f ∈ I, eval z f = 0) ↔ I ≤ RingHom.ker (eval z) :=
    fun I => ⟨fun h f hf => RingHom.mem_ker.2 (h f hf), fun h f hf => RingHom.mem_ker.1 (h hf)⟩
  rw [key, pieceIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le]
  apply and_congr
  · exact ⟨fun h f hf => RingHom.mem_ker.1 (Ideal.mem_comap.1 (h hf)),
      fun h f hf => Ideal.mem_comap.2 (RingHom.mem_ker.2 (h f hf))⟩
  · constructor
    · intro h d g g' θ hg hg' hgg
      have := h ⟨d, g, g', θ, hg, hg', hgg, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, eval_C] at this
      exact sub_eq_zero.1 this
    · rintro h f ⟨d, g, g', θ, hg, hg', hgg, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, eval_C]
      exact sub_eq_zero.2 (h d g g' θ hg hg' hgg)

omit [Fintype K] in

theorem pieceIdeal_map (y : (Σ k, ι k) → Ω) (s : F →+* ℂ) (τ : ℂ ≃+* ℂ) :
    (pieceIdeal y s).map (MvPolynomial.map (τ : ℂ →+* ℂ)) = pieceIdeal y ((τ : ℂ →+* ℂ).comp s) := by
  have hint : (τ : ℂ →+* ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  have hmm : ∀ g : MRing ι, MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map (Int.castRingHom ℂ) g) = MvPolynomial.map (Int.castRingHom ℂ) g := by
    intro g
    rw [MvPolynomial.map_map, hint]
  rw [pieceIdeal, pieceIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_span]
  congr 1
  · congr 1
    exact RingHom.ext hmm
  · congr 1
    ext f
    constructor
    · rintro ⟨_, ⟨d, g, g', θ, hg, hg', hgg, rfl⟩, rfl⟩
      refine ⟨d, g, g', θ, hg, hg', hgg, ?_⟩
      rw [map_sub, map_mul, map_C, hmm, hmm]
      rfl
    · rintro ⟨d, g, g', θ, hg, hg', hgg, rfl⟩
      refine ⟨_, ⟨d, g, g', θ, hg, hg', hgg, rfl⟩, ?_⟩
      rw [map_sub, map_mul, map_C, hmm, hmm]
      rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem radical_map_conj (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (τ : ℂ ≃+* ℂ) :
    (I.map (MvPolynomial.map (τ : ℂ →+* ℂ))).radical = I.radical.map (MvPolynomial.map (τ : ℂ →+* ℂ)) := by
  have hinj : Function.Injective (MvPolynomial.map (σ := Σ k, ι k) (τ : ℂ →+* ℂ)) := map_injective _ τ.injective
  refine (Ideal.map_radical_of_surjective (map_surjective _ τ.surjective) ?_).symm
  rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
  exact bot_le

theorem exists_ringEquiv_comp [NumberField F] (sg sg' : F →+* ℂ) :
    ∃ τ : ℂ ≃+* ℂ, (τ : ℂ →+* ℂ).comp sg = sg' := by
  have hc : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  have hΩ : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  have h1 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg.toAlgebra hc hΩ
  have h2 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg'.toAlgebra hc hΩ
  obtain ⟨τ, hτ⟩ := @GroundTheory.Global.exists_ringEquiv_extend_of_trdeg_eq ℂ _ _ F F _ _ sg.toAlgebra sg'.toAlgebra
    (RingEquiv.refl F) (h1.trans h2.symm)
  exact ⟨τ, RingHom.ext fun a => hτ a⟩

theorem piece_open [NumberField F] {y : (Σ k, ι k) → Ω}
    (hex : ∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) (s : F →+* ℂ) :
    ∀ z ∈ mcPts (mCoordIdeal y), (∀ f ∈ pieceIdeal y s, eval z f = 0) →
      ∀ᶠ z' in 𝓝 z, z' ∈ mcPts (mCoordIdeal y) → ∀ f ∈ pieceIdeal y s, eval z' f = 0 := by
  intro z hz hzI
  have hzs : LiesOver y s z := ((zero_pieceIdeal_iff y s z).1 hzI).2
  let U : Set ((Σ k, ι k) → ℂ) := ⋃ s' ∈ ({s}ᶜ : Set (F →+* ℂ)), {z | LiesOver y s' z}
  have hU : IsClosed U :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun s' _ => EmbeddingWeight.isClosed_liesOver y s'
  have hzU : z ∉ U := by
    simp only [U, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, not_exists]
    intro s' hs' h'
    exact hs' ((hex z hz).unique h' hzs)
  filter_upwards [hU.isOpen_compl.mem_nhds hzU] with z' hz' hz'P
  obtain ⟨s', hs', -⟩ := hex z' hz'P
  have hss : s' = s := by
    by_contra hne
    exact hz' (Set.mem_biUnion (x := s') hne hs')
  subst hss
  exact (zero_pieceIdeal_iff y s' z').2 ⟨hz'P.2, hs'⟩

end PieceDegreeAlt

open PieceDegreeAlt

theorem PieceDegree.proof (hI : PieceIntegral.Statement) (hC : ConjIntNum.Statement) :
    PieceDegree.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D L sg sg' hP _ hL hex
  classical
  have hint : ∀ s : F →+* ℂ,
      ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)) =
        NumbersDVR.intNum ℂ (pieceIdeal y s).radical (fun j => (L j).a) := by
    intro s
    rw [← hI K ι (mCoordIdeal y) D L (pieceIdeal y s) hP hL le_sup_left (piece_open hex s)]
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) fun z hz => ?_
    have hiff : z ∈ {z | LiesOver y s z} ↔ z ∈ {z | ∀ f ∈ pieceIdeal y s, eval z f = 0} := by
      simp only [Set.mem_ofPred_eq, zero_pieceIdeal_iff]
      exact ⟨fun h => ⟨hz.2, h⟩, fun h => h.2⟩
    by_cases h : LiesOver y s z
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.1 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.2 h'))]
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_comp sg sg'
  rw [hint, hint, ← hτ, ← pieceIdeal_map y sg τ, radical_map_conj]
  exact congrArg (fun x : ℤ => (x : ℝ)) (hC K ι ℂ τ (pieceIdeal y sg).radical D (fun j => (L j).a)).symm

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameBasePtFree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameBasePtFree

theorem linForm_projMat {κ : Type} [Fintype κ] {D : ℕ} (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [linForm, projMat]
  generalize e k = q
  obtain ⟨⟨⟩, j⟩ := q
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem rename_mem_span {κ : Type} {D : ℕ} (e : Fin (D + 1) → Ix κ) {h : MvPolynomial (Fin (D + 1)) ℤ} {n : ℕ}
    (hh : h.IsHomogeneous n) (hn : 0 < n) :
    rename e h ∈ Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
  have h1 : h ∈ Ideal.span ((X : Fin (D + 1) → MvPolynomial (Fin (D + 1)) ℤ) '' Set.univ) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push Not at hcon
    have hm0 : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    have := hh (mem_support_iff.mp hm)
    rw [hm0, map_zero] at this
    omega
  have h2 := Ideal.mem_map_of_mem (rename e : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial (Ix κ) ℤ) h1
  rw [Ideal.map_span, Set.image_image, Set.image_univ] at h2
  simpa [rename_X] using h2

theorem pow_mem (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) (x : Ix κ → Ω)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame x e) (p : Ix κ) :
    ∃ N : ℕ, (X p : MvPolynomial (Ix κ) ℤ) ^ N ∈
      coordIdeal ℤ x ⊔ Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
  obtain ⟨q, hmon, hq⟩ := hfr.integral p
  set N := q.natDegree with hNdef
  have hcoef : ∀ j, ∃ f : MvPolynomial (Fin (D + 1)) ℤ,
      coneMap ℤ (x ∘ e) f = ((q.coeff j : coneRing ℤ (x ∘ e)) : Polynomial Ω) :=
    fun j => (q.coeff j).2
  choose f hf using hcoef
  set F : MvPolynomial (Ix κ) ℤ := X p ^ N +
      ∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j with hFdef
  have hFh : F.IsHomogeneous N := by
    refine (isHomogeneous_X_pow p N).add (IsHomogeneous.sum _ _ _ fun j hj => ?_)
    have hj' : N - j + j = N := Nat.sub_add_cancel (Finset.mem_range.mp hj).le
    have := ((homogeneousComponent_isHomogeneous (N - j) (f j)).rename_isHomogeneous (f := e)).mul
      (isHomogeneous_X_pow p j)
    rwa [hj'] at this
  have hFx : aeval x F = 0 := by
    have h0 := congrArg (fun r : Polynomial Ω => r.coeff N) hq
    simp only [Polynomial.coeff_zero] at h0
    rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.coeff_add,
      Polynomial.finsetSum_coeff] at h0
    rw [← h0, hFdef, map_add, map_sum]
    congr 1
    · rw [Polynomial.eval₂_X_pow, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul_X_pow, if_pos rfl,
        map_pow, aeval_X]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : j ≤ N := (Finset.mem_range.mp hj).le
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, mul_pow, ← Polynomial.C_pow,
        ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos hjN, Polynomial.coeff_mul_C]
      rw [map_mul, map_pow, aeval_X, aeval_rename]
      have : algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω) (q.coeff j) = coneMap ℤ (x ∘ e) (f j) := (hf j).symm
      rw [this, coeff_coneMap]
  have hFP : F ∈ coordIdeal ℤ x := mem_coordIdeal_of_isHomogeneous ℤ x hFh hFx
  refine ⟨N, ?_⟩
  have hsum : (∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j) ∈
      Ideal.span (Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ)) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    have hjN : j < N := Finset.mem_range.mp hj
    exact rename_mem_span e (homogeneousComponent_isHomogeneous (N - j) (f j)) (by omega)
  have : (X p : MvPolynomial (Ix κ) ℤ) ^ N =
      F - ∑ j ∈ Finset.range N, rename e (homogeneousComponent (N - j) (f j)) * X p ^ j := by
    rw [hFdef]; ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hsum)

end ProjFrameBasePtFree

open ProjFrameBasePtFree in

theorem ProjFrameBasePtFree.proof : ProjFrameBasePtFree.Statement := by
  intro D Ω _ _ κ _ x e hfr k₂ i
  obtain ⟨N, hN⟩ := pow_mem D Ω κ x e hfr ⟨(), i ()⟩
  refine ⟨N, ?_⟩
  have hspan : (Set.range fun j : GlobalTheory (Fin (D + 1)) k₂ =>
      linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨k₂, j⟩) =
      Set.range fun k => (X (e k) : MvPolynomial (Ix κ) ℤ) := by
    cases k₂
    ext
    simp [linForm_projMat]
  rw [hspan, Fintype.prod_unique]
  exact hN

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace QuotPartGraded

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

def blockWeight (ι : K → Type) : (Σ k, ι k) → (K → ℤ) := fun x => Pi.single x.1 1

theorem blockWeight_apply (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = ∑ i, (d ⟨k, i⟩ : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • blockWeight ι i) (by intro i; simp),
    Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

theorem isMultiHomog_iff (p : MRingOver S ι) (a : K → ℕ) :
    IsMultiHomog p a ↔ IsWeightedHomogeneous (blockWeight ι) p (fun k => (a k : ℤ)) := by
  unfold IsMultiHomog
  constructor
  · intro h d hd
    funext k
    rw [blockWeight_apply]
    have := h d (mem_support_iff.2 hd) k
    exact_mod_cast this
  · intro h m hm k
    have := congrFun (h (mem_support_iff.1 hm)) k
    rw [blockWeight_apply] at this
    exact_mod_cast this

theorem nonneg_of_isWeightedHomogeneous {p : MRingOver S ι} {c : K → ℤ}
    (hp : IsWeightedHomogeneous (blockWeight ι) p c) (h0 : p ≠ 0) : ∀ k, 0 ≤ c k := by
  obtain ⟨d, hd⟩ := ne_zero_iff.1 h0
  intro k
  rw [← hp hd, blockWeight_apply]
  positivity

theorem span_eq (c : K → ℤ) :
    Submodule.span S {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)} =
      weightedHomogeneousSubmodule S (blockWeight ι) c := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro p ⟨hc, hp⟩
    rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
    have h' := (isMultiHomog_iff p _).1 hp
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rwa [hcc] at h'
  · intro p hp
    by_cases h0 : p = 0
    · rw [h0]; exact Submodule.zero_mem _
    · apply Submodule.subset_span
      have hc := nonneg_of_isWeightedHomogeneous hp h0
      refine ⟨hc, (isMultiHomog_iff p _).2 ?_⟩
      have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
      rw [hcc]
      exact hp

theorem quotPart_eq (V : Ideal (MRingOver S ι)) (c : K → ℤ) :
    KH.quotPart S V c =
      (weightedHomogeneousSubmodule S (blockWeight ι) c).map (Ideal.Quotient.mkₐ S V).toLinearMap := by
  rw [KH.quotPart, ← span_eq, Submodule.map_span]
  rfl

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous {V : Ideal (MRingOver S ι)} (hV : IsMultiHomogIdeal V) :
    V.IsHomogeneous (weightedHomogeneousSubmodule S (blockWeight ι)) := by
  obtain ⟨T, hT, rfl⟩ := hV
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨fun k => (a k : ℤ), (isMultiHomog_iff f a).1 ha⟩

end QuotPartGraded

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem QuotPartGraded.proof : QuotPartGraded.Statement := by
  intro S _ K _ ι _ V hV
  have hq := QuotPartGraded.quotPart_eq (S := S) (ι := ι) V
  refine ⟨?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv hsum
      have hlift : ∀ c, ∃ p : MRingOver S ι, c ∈ s →
          (p ∈ weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι) c ∧
            Ideal.Quotient.mk V p = v c) := by
        intro c
        by_cases hc : c ∈ s
        · have h1 := hv c hc
          rw [hq] at h1
          obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.1 h1
          exact ⟨y, fun _ => ⟨hy, hyv⟩⟩
        · exact ⟨0, fun h => absurd h hc⟩
      choose p hp using hlift
      have hsumV : ∑ c ∈ s, p c ∈ V := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hsum]
        exact Finset.sum_congr rfl fun c hc => (hp c hc).2
      intro c hc
      have hcomp := weightedHomogeneousComponent_mem_of_mem S (QuotPartGraded.blockWeight ι)
        (QuotPartGraded.isHomogeneous hV) hsumV c
      rw [map_sum, Finset.sum_eq_single c] at hcomp
      · rw [← (hp c hc).2, Ideal.Quotient.eq_zero_iff_mem]
        rwa [weightedHomogeneousComponent_eq_self (hp c hc).1] at hcomp
      · intro d hd hdc
        exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne c (hp d hd).1 (Ne.symm hdc)
      · intro h
        exact absurd hc h
    · have htop := (DirectSum.Decomposition.isInternal
        (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι))).submodule_iSup_eq_top
      rw [show KH.quotPart S V = fun c => (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι) c).map
          (Ideal.Quotient.mkₐ S V).toLinearMap from funext hq]
      rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective S V
  · intro a c p m hp hm
    rw [hq] at hm ⊢
    obtain ⟨q, hq', rfl⟩ := Submodule.mem_map.1 hm
    refine Submodule.mem_map.2 ⟨p * q, ?_, ?_⟩
    · have := ((QuotPartGraded.isMultiHomog_iff p a).1 hp).mul hq'
      rw [mem_weightedHomogeneousSubmodule, add_comm]
      exact this
    · simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
      rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RealFormsOnPoints.proof (hN : ComplexFormsOnPoints.Statement)
    (hB : IndependentModBaseChange.Statement) : RealFormsOnPoints.Statement := by
  intro K _ ι _ Ω _ y d e r g hP hg hli c hc
  obtain ⟨_, ⟨hprime, -, hrel⟩, -, -⟩ := hP

  have hZ : LinearIndependent ℤ (fun i => Ideal.Quotient.mk (mCoordIdeal y) (g i)) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro n hn
    apply hli n
    have hmem : ∑ i, n i • g i ∈ mCoordIdeal y := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_zsmul] using hn
    have h0 : mConeMap y (∑ i, n i • g i) = 0 := hmem
    have hsum : mConeMap y (∑ i, n i • g i) =
        MvPolynomial.C (∑ i, n i • aeval y (g i)) * ∏ k, MvPolynomial.X k ^ e k := by
      rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ProjLine.mConeMap_eq_of_isMultiHomog y (hg i), map_zsmul, smul_mul_assoc]
    rw [hsum] at h0
    have hX : (∏ k, MvPolynomial.X k ^ e k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact (MvPolynomial.C_eq_zero).mp ((mul_eq_zero.mp h0).resolve_right hX)

  have hC := hB _ (mCoordIdeal y) r g hZ
  set I := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℂ)) with hI

  have hF : (∑ i, (c i : ℂ) • MvPolynomial.map (Int.castRingHom ℂ) (g i)) ∈ I := by
    refine hN K ι _ hprime hrel _ fun z hz => ?_
    rw [map_sum]
    simpa only [smul_eval] using hc z hz
  rw [Fintype.linearIndependent_iff] at hC
  funext i
  have h := hC (fun i => (c i : ℂ)) (by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hF
    rw [← hF, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]) i
  exact_mod_cast h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace ResolutionMixedIntegral

theorem proof (hB : ResolutionMixedBridge.Statement) (hI : ResolutionInterpIntegral.Statement) :
    ResolutionMixedIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  rw [hI D Ω κ d m₁ hm₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hM : ∀ j : Fin D, IsSmoothMetric (if j.val < i then m₁ else d.m) := fun j => by
    split_ifs
    · exact hm₁
    · exact d.smooth
  have hpot : mixPot d.m m₁ D i = fun j z => Real.log ((if j.val < i then m₁ else d.m).ρ z) := by
    funext j z
    unfold mixPot
    split_ifs <;> rfl
  have hres : (fun j : Fin D => resPot d (if j.val < i then m₁ else d.m)) =
      fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m := by
    funext j
    split_ifs <;> rfl
  rw [hpot, hB D Ω κ d (fun j => if j.val < i then m₁ else d.m) m₁ hM hm₁, hres]

end ResolutionMixedIntegral

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedRestrict
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedRestrict.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V W : Ideal (MRingOver S ι)) (a : K → ℤ),
    V ≤ W → KH.GeneratedV S V a → KH.GeneratedV S W a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

