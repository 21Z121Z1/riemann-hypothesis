import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisDD
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecWOfMatrix
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplRed

open GlobalTheory.WachTensor

private theorem tensorProduct_map_algHom_smul {O A M N : Type} [CommRing O] [CommRing A] [Algebra O A]
    [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : A →ₐ[O] A) (g : M →ₗ[O] N) (r : A) (x : A ⊗[O] M) :
    TensorProduct.map f.toLinearMap g (r • x) = f r • TensorProduct.map f.toLinearMap g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, smul_eq_mul,
      smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

private theorem coeffs_eq_of_sum_smul_eq_of_span_eq {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (B : Module.Basis (Fin n) R M) (c : Fin n → M) (hc : Submodule.span R (Set.range c) = ⊤)
    {v w : Fin n → R} (hvw : ∑ i, v i • c i = ∑ i, w i • c i) : v = w := by
  have hs : Function.Surjective (Fintype.linearCombination R c) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hc]
  have hi : Function.Injective (B.equivFun.toLinearMap ∘ₗ Fintype.linearCombination R c) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (B.equivFun.surjective.comp hs)
  apply hi
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Fintype.linearCombination_apply, hvw]

theorem decW_of_matrix (S : Sit) (E : S.Comparison₂)
    (h : ∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) S.W.EE),
      (∀ y : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (y i) = y i) →
        ∃ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) ∧
          ∀ i, ∃ e, y i - (∑ k, E.ioE (Pm i k) * S.φR (z k) - z i) = E.ioE e) ∧
      (∀ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) →
        (∀ i, ∃ e, ∑ k, E.ioE (Pm i k) * S.φR (z k) - z i = E.ioE e) →
          ∀ i, ∃ e, z i = E.ioE e)) : DecW S E := by
  unfold DecW
  intro T
  have memH : ∀ x, x ∈ Htl S T ↔ ∀ g ∈ Hker S, TWact (S.gR g) T g x = x := fun x => Iff.rfl
  have hH : ∀ g ∈ Hker S, S.W.resΓ g = 1 := fun g hg => MonoidHom.mem_ker.1 hg

  by_cases hsub : Subsingleton (TW S.RW T)
  · have key : ∀ x : TW S.RW T, x ∈ LinearMap.range (E.jD T) := fun x => ⟨0, Subsingleton.elim _ _⟩
    exact ⟨fun y _ => ⟨0, (Htl S T).zero_mem, key _⟩, fun z _ _ => key z⟩
  have : Nontrivial (TW S.RW T) := not_subsingleton_iff_nontrivial.1 hsub
  have : Nontrivial S.RW := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact hsub (Module.subsingleton S.RW _)
  have : Nontrivial S.O := RingHom.domain_nontrivial (algebraMap S.O S.RW)
  have : Nontrivial S.W.EE := RingHom.domain_nontrivial E.ioE.toRingHom
  have : Module.Free S.O ↥T.L.T := T.L.free
  have : Module.Finite S.O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg

  have bW : Module.Basis (Fin (Module.finrank S.O ↥T.L.T)) S.RW (TW S.RW T) :=
    (Module.finBasis S.O ↥T.L.T).baseChange S.RW
  have hr : 0 < Module.finrank S.O ↥T.L.T := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (TW S.RW T)
    exact hxy (bW.repr.injective (Finsupp.ext fun i => absurd i.isLt (by omega)))
  have hdr := (S.W.DD_free T).2
  have : Module.Free S.W.EE (S.W.DD T) := (S.W.DD_free T).1
  have : Module.Finite S.W.EE (S.W.DD T) := Module.finite_of_finrank_pos (by rw [hdr]; exact hr)
  obtain ⟨d, ⟨bD⟩, ⟨bW'⟩⟩ : ∃ d, Nonempty (Module.Basis (Fin d) S.W.EE (S.W.DD T)) ∧
      Nonempty (Module.Basis (Fin d) S.RW (TW S.RW T)) :=
    ⟨_, ⟨Module.finBasis _ _⟩, ⟨bW.reindex (finCongr hdr.symm)⟩⟩

  have hexp : ∀ x : S.W.DD T, E.jD T x = ∑ i, E.ioE (bD.repr x i) • E.jD T (bD i) := by
    intro x
    conv_lhs => rw [← bD.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => E.jD_smul T _ _
  have hspan : Submodule.span S.RW (Set.range fun i => E.jD T (bD i)) = ⊤ := by
    rw [eq_top_iff, ← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hexp x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hinj : ∀ v w : Fin d → S.RW, ∑ i, v i • E.jD T (bD i) = ∑ i, w i • E.jD T (bD i) → v = w :=
    fun v w hvw => coeffs_eq_of_sum_smul_eq_of_span_eq bW' _ hspan hvw
  have hsurj : ∀ y : TW S.RW T, ∃ v : Fin d → S.RW, y = ∑ i, v i • E.jD T (bD i) := by
    intro y
    have hy : y ∈ Submodule.span S.RW (Set.range fun i => E.jD T (bD i)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun S.RW).1 hy
    exact ⟨v, hv.symm⟩

  have actS : ∀ g (r : S.RW) (x : TW S.RW T),
      TWact (S.gR g) T g (r • x) = S.gR g r • TWact (S.gR g) T g x :=
    fun g r x => tensorProduct_map_algHom_smul (S.gR g) (T.actT g) r x
  have mapS : ∀ (r : S.RW) (x : TW S.RW T), TWmap S.φR T (r • x) = S.φR r • TWmap S.φR T x :=
    fun r x => tensorProduct_map_algHom_smul S.φR LinearMap.id r x
  have hfix : ∀ g ∈ Hker S, ∀ x, TWact (S.gR g) T g (E.jD T x) = E.jD T x := by
    intro g hg x
    rw [← E.jD_act, hH g hg, S.W.γD_one]
  have hact : ∀ g ∈ Hker S, ∀ v : Fin d → S.RW,
      TWact (S.gR g) T g (∑ i, v i • E.jD T (bD i)) = ∑ i, S.gR g (v i) • E.jD T (bD i) := by
    intro g hg v
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [actS, hfix g hg]
  have hinv : ∀ v : Fin d → S.RW,
      (∑ i, v i • E.jD T (bD i)) ∈ Htl S T ↔ ∀ i, ∀ g ∈ Hker S, S.gR g (v i) = v i := by
    intro v
    rw [memH]
    constructor
    · intro hv i g hg
      exact congrFun (hinj _ _ ((hact g hg v).symm.trans (hv g hg))) i
    · intro hv g hg
      rw [hact g hg v]
      exact Finset.sum_congr rfl fun i _ => by rw [hv i g hg]
  have hk : ∀ k, TWmap S.φR T (E.jD T (bD k)) =
      ∑ i, E.ioE (bD.repr (S.W.φD T (bD k)) i) • E.jD T (bD i) := fun k => by
    rw [← E.jD_φ]
    exact hexp _
  have hφ : ∀ z : Fin d → S.RW, TWmap S.φR T (∑ k, z k • E.jD T (bD k)) =
      ∑ i, (∑ k, E.ioE (bD.repr (S.W.φD T (bD k)) i) * S.φR (z k)) • E.jD T (bD i) := by
    intro z
    rw [map_sum]
    simp only [mapS, hk, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  have hrng : ∀ v : Fin d → S.RW,
      (∑ i, v i • E.jD T (bD i)) ∈ LinearMap.range (E.jD T) ↔ ∀ i, ∃ e, v i = E.ioE e := by
    intro v
    constructor
    · rintro ⟨x, hx⟩
      rw [hexp] at hx
      have hv := hinj _ _ hx
      exact fun i => ⟨bD.repr x i, (congrFun hv i).symm⟩
    · intro hv
      choose e he using hv
      refine ⟨∑ i, e i • bD i, ?_⟩
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [E.jD_smul, he i]

  obtain ⟨h1, h2⟩ := h d (Matrix.of fun i k => bD.repr (S.W.φD T (bD k)) i)
  simp only [Matrix.of_apply] at h1 h2
  refine ⟨fun y hy => ?_, fun z hz hφz => ?_⟩
  · obtain ⟨v, rfl⟩ := hsurj y
    obtain ⟨z, hzH, hz⟩ := h1 v ((hinv v).1 hy)
    refine ⟨∑ i, z i • E.jD T (bD i), (hinv z).2 hzH, ?_⟩
    rw [hφ z, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    simp only [← sub_smul]
    exact (hrng _).2 hz
  · obtain ⟨u, rfl⟩ := hsurj z
    have hu := (hinv u).1 hz
    rw [hφ u, ← Finset.sum_sub_distrib] at hφz
    simp only [← sub_smul] at hφz
    exact (hrng u).2 (h2 u hu ((hrng _).1 hφz))

end GlobalTheory.DecomplRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAbove
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.JumpWin

theorem finset_of_rat (F : Finset ℚ) (n N : ℕ) (P : ℤ → Prop) (hF : F.card ≤ n)
    (hP : ∀ a, P a → (a : ℚ) ∈ F ∧ -(N : ℤ) ≤ a ∧ a ≤ N) :
    ∃ U : Finset ℤ, U.card ≤ n ∧ (∀ u ∈ U, -(N : ℤ) ≤ u ∧ u ≤ N) ∧ ∀ a, P a → a ∈ U := by
  classical
  refine ⟨(F.image fun q => ⌊q⌋).filter (fun u => -(N : ℤ) ≤ u ∧ u ≤ N), ?_, ?_, ?_⟩
  · exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans hF)
  · intro u hu
    exact (Finset.mem_filter.1 hu).2
  · intro a ha
    obtain ⟨h1, h2⟩ := hP a ha
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(a : ℚ), h1, Int.floor_intCast a⟩, h2⟩

variable {D : D7}

open AdmissibleParameterJ

theorem JW_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : JW D up j ρ ⊆ JJ D up j ρ := by
  intro q hq
  cases up <;> simp only [JW, cloudT, lowT, JJ, Jp, Jm, reflS, Bool.false_eq_true, if_true, if_false,
    Set.mem_union, Set.mem_setOf_eq] at hq ⊢ <;> tauto

theorem exists_finset_JW (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) :
    ∃ F : Finset ℚ, F.card ≤ D.R.r ∧ ∀ q ∈ JW D up j ρ, q ∈ F := by
  classical
  let cl : Finset ℚ := Finset.univ.image (fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D)
  let lw : Finset ℚ := Finset.univ.image (fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D)
  have hcard : (cl ∪ lw).card ≤ D.R.r := by
    have h1 : cl.card ≤ D.R.k - 1 := Finset.card_image_le.trans (by simp)
    have h2 : lw.card ≤ D.R.m := Finset.card_image_le.trans (by simp)
    have hk := D.R.m_add_three_le_k
    have : (cl ∪ lw).card ≤ cl.card + lw.card := Finset.card_union_le _ _
    simp only [Ranks.r]
    omega
  have hmem : ∀ q, q ∈ cloudJ D j ρ ∪ lowJ D j ρ → q ∈ cl ∪ lw := by
    intro q hq
    rcases hq with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  cases up
  · refine ⟨(cl ∪ lw).image (AdmissibleParameterJ.refl D), Finset.card_image_le.trans hcard, ?_⟩
    intro q hq
    have hq' : AdmissibleParameterJ.refl D q ∈ cloudJ D j ρ ∪ lowJ D j ρ := by
      simpa only [JW, cloudT, lowT, reflS, Bool.false_eq_true, if_false, Set.mem_union,
        Set.mem_setOf_eq] using hq
    refine Finset.mem_image.2 ⟨AdmissibleParameterJ.refl D q, hmem _ hq', ?_⟩
    simp only [AdmissibleParameterJ.refl]; ring
  · refine ⟨cl ∪ lw, hcard, ?_⟩
    intro q hq
    exact hmem q (by simpa only [JW, cloudT, lowT, if_true] using hq)

theorem zero_not_mem_JW (L : SizeData₂ D) (hc : jcCondition L) (up : Bool) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) : (0 : ℚ) ∉ JW D up j ρ := by
  obtain ⟨hlow, -, hcl, h0⟩ := hc j hj1 hj2 ρ
  cases up
  · intro h
    simp only [JW, cloudT, lowT, reflS, Bool.false_eq_true, if_false, Set.mem_union,
      Set.mem_setOf_eq] at h
    have ht : (0 : ℚ) ≤ (D.R.t : ℚ) := Nat.cast_nonneg _
    rcases h with h | h
    · have := hcl _ h
      simp only [AdmissibleParameterJ.refl] at this
      linarith
    · rcases hlow _ h with ⟨-, h'⟩ | ⟨h', -⟩
      · simp only [AdmissibleParameterJ.refl] at h'
        linarith
      · simp only [AdmissibleParameterJ.refl] at h'
        linarith
  · simpa only [JW, cloudT, lowT, if_true] using h0

theorem natAbs_le_of_mem_JJ (L : SizeData₂ D) (he : JumpAbsoluteBound L) (up : Bool) (j : ℕ) (hj1 : 1 ≤ j)
    (hj2 : j ≤ D.R.m) (ρ : D.what₂.Tau) (a : ℤ) (ha : (a : ℚ) ∈ JJ D up j ρ) :
    a.natAbs ≤ ⌊2 * L.sc.b⌋₊ := by
  have h1 := he.1 j hj1 hj2 ρ up _ ha
  have h2 : |((a : ℚ) : ℝ)| ≤ 2 * L.sc.b := by
    have := he.2.1; have := he.2.2.2; linarith
  apply Nat.le_floor
  have : ((a.natAbs : ℕ) : ℝ) = |((a : ℚ) : ℝ)| := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  rw [this]; exact h2

end GlobalTheory.JumpWin

open GlobalTheory.JumpWin AdmissibleParameterJ in

theorem GlobalTheory.jumps_WpO_T2O_window : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → AdmissibleParameterJ.DualCloudSizes L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1), ∀ M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i), (M = WpO D.nd i ρ π ∨ M = T2O D.nd i ρ π) → (∃ U : Finset ℤ, U.card ≤ D.R.r ∧ (∀ u ∈ U, -((⌊2 * L.sc.b⌋₊ + 1 : ℕ) : ℤ) ≤ u ∧ u ≤ (⌊2 * L.sc.b⌋₊ + 1 : ℕ)) ∧ ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a → a ∈ U) ∧ ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ 0 := by
  intro D L ep hA _hb hc he hf i r ρ π hr hπ hdec w hw C τ M hM
  classical
  obtain ⟨g, ρ', -, -, hT⟩ := hA i r hr w hw C τ
  have hj := D.nd.j_range i
  have hW := hT ρ π hπ hdec
  generalize decide (TypeU D ep g) = up at hW
  obtain ⟨F, hFc, hFm⟩ := exists_finset_JW up (D.nd.j i) ρ'
  rcases hM with rfl | rfl
  · refine ⟨finset_of_rat F D.R.r (⌊2 * L.sc.b⌋₊ + 1) _ hFc ?_, ?_⟩
    · intro a ha
      have hq := ((hW a).1).1 ha
      have hn := natAbs_le_of_mem_JJ L he up _ hj.1 hj.2 ρ' a (JW_sub_JJ up _ ρ' hq)
      refine ⟨hFm _ hq, ?_, ?_⟩ <;> push_cast <;> omega
    · intro h0
      have := ((hW 0).1).1 h0
      exact zero_not_mem_JW L hc up _ hj.1 hj.2 ρ' (by simpa using this)
  · refine ⟨finset_of_rat (F.image fun q => -q - 1) D.R.r (⌊2 * L.sc.b⌋₊ + 1) _
      (Finset.card_image_le.trans hFc) ?_, ?_⟩
    · intro a ha
      have hq : -(a : ℚ) - 1 ∈ JW D up (D.nd.j i) ρ' := ((hW a).2.2.1).1 ha
      have hq' : (((-a - 1 : ℤ)) : ℚ) ∈ JW D up (D.nd.j i) ρ' := by push_cast; exact hq
      have hn := natAbs_le_of_mem_JJ L he up _ hj.1 hj.2 ρ' _ (JW_sub_JJ up _ ρ' hq')
      refine ⟨Finset.mem_image.2 ⟨_, hFm _ hq, by ring⟩, ?_, ?_⟩ <;> push_cast <;> omega
    · intro h0
      have := ((hW 0).2.2.1).1 h0
      exact (hf _ hj.1 hj.2 ρ').2.2.1 up (by simpa using this)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_frobenius_split_places : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc), Dense {σ : GE N | ∃ w, SplitOut N i w ∧ ∃ B : ValuationSubring N.Om, Formalism.ConjugateSelfDual.IsPlaceOver (F := H.E) B w ∧ Formalism.ConjugateSelfDual.IsFrob (F := H.E) B (Formalism.ConjugateSelfDual.normV w) σ} := by
  first | exact @GlobalTheory.FrobDense.dense_frob | exact GlobalTheory.FrobDense.dense_frob | (intros; apply GlobalTheory.FrobDense.dense_frob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonRootSubOneIsPseudoUniformizerTiltStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilonRoot_sub_one_isPseudoUniformizer_tilt : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), ¬ IsUnit (AI.εroot s - 1) ∧ ∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ (AI.εroot s - 1) ^ m := by
  first | exact @GlobalTheory.WeakClosed.TiltUnif.main | exact GlobalTheory.WeakClosed.TiltUnif.main | (intros; apply GlobalTheory.WeakClosed.TiltUnif.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfComm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.ResComm

theorem comm_span {Λ M C : Type} [CommRing Λ] [AddCommGroup M] [Module Λ M] [AddCommGroup C] (S : Set (Module.End Λ M))
    (φ : M →+ C) (h : ∀ A ∈ S, ∀ B ∈ S, ∀ m, φ (A (B m)) = φ (B (A m))) :
    ∀ A ∈ Submodule.span Λ S, ∀ B ∈ Submodule.span Λ S, ∀ m, φ (A (B m)) = φ (B (A m)) := by

  have key : ∀ A ∈ S, ∀ B ∈ Submodule.span Λ S, ∀ m, φ (A (B m)) = φ (B (A m)) := by
    intro A hA B hB
    induction hB using Submodule.span_induction with
    | mem B hB => exact h A hA B hB
    | zero => intro m; simp
    | add B₁ B₂ _ _ h₁ h₂ => intro m; simp [h₁, h₂]
    | smul c B _ hB' =>
      intro m
      simp only [LinearMap.smul_apply, ← map_smul]
      exact hB' (c • m)
  intro A hA B hB
  induction hA using Submodule.span_induction with
  | mem A hA => exact key A hA B hB
  | zero => intro m; simp
  | add A₁ A₂ _ _ h₁ h₂ => intro m; simp [h₁, h₂]
  | smul c A _ hA' =>
    intro m
    simp only [LinearMap.smul_apply, ← map_smul]
    exact hA' (c • m)

theorem act_add {O Λ K : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (P Q : Matrix (Fin r) (Fin r) O) :
    matAct (M := K) ((P + Q).map (algebraMap O Λ)) =
      matAct (P.map (algebraMap O Λ)) + matAct (Q.map (algebraMap O Λ)) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp [matAct, add_smul, Finset.sum_add_distrib]

theorem act_smul {O Λ K : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (c : O) (P : Matrix (Fin r) (Fin r) O) :
    matAct (M := K) ((c • P).map (algebraMap O Λ)) = algebraMap O Λ c • matAct (P.map (algebraMap O Λ)) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp [matAct, mul_smul, Finset.smul_sum]

theorem act_congr {O Λ K : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ] [Algebra O Λ]
    [IsLocalHom (algebraMap O Λ)] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (hm : ∀ x ∈ IsLocalRing.maximalIdeal Λ, ∀ k : K, x • k = 0) (P Q : Matrix (Fin r) (Fin r) O)
    (h : P.map (IsLocalRing.residue O) = Q.map (IsLocalRing.residue O)) :
    matAct (M := K) (P.map (algebraMap O Λ)) = matAct (Q.map (algebraMap O Λ)) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [matAct, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_

  have hPQ : P i j - Q i j ∈ IsLocalRing.maximalIdeal O := by
    have e := congrFun (congrFun h i) j
    simp only [Matrix.map_apply] at e
    exact Ideal.Quotient.eq.mp e
  have hΛ : algebraMap O Λ (P i j - Q i j) ∈ IsLocalRing.maximalIdeal Λ :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu =>
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hPQ) (isUnit_of_map_unit (algebraMap O Λ) _ hu))
  have e := hm _ hΛ (v j)
  rwa [map_sub, sub_smul, sub_eq_zero] at e

private theorem matAct_single {O Λ K : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (a b : Fin r) (v : Fin r → K) :
    matAct (M := K) ((Matrix.of fun i j => if i = a ∧ j = b then (1 : O) else 0).map (algebraMap O Λ)) v =
      Pi.single a (v b) := by
  funext i
  simp only [matAct, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply, Matrix.of_apply]
  by_cases hi : i = a
  · subst hi
    simp [apply_ite (algebraMap O Λ), ite_smul]
  · simp [hi]

private theorem matAct_of_span_residue_spans {Γ O Λ K : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ]
    [Algebra O Λ] [IsLocalHom (algebraMap O Λ)] [AddCommGroup K] [Module Λ K] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (hm : ∀ x ∈ IsLocalRing.maximalIdeal Λ, ∀ k : K, x • k = 0)
    (hsp : Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g =>
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤)
    (P : Matrix (Fin r) (Fin r) O) :
    matAct (M := K) (P.map (algebraMap O Λ)) ∈ Submodule.span Λ (Set.range fun g =>
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ))) := by

  have lift : ∀ X : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O),
      ∃ P' : Matrix (Fin r) (Fin r) O, P'.map (IsLocalRing.residue O) = X := fun X =>
    ⟨X.map (Function.surjInv IsLocalRing.residue_surjective), by
      ext i j; simp [Function.surjInv_eq IsLocalRing.residue_surjective]⟩

  suffices H : ∀ X ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g =>
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)),
      ∀ P : Matrix (Fin r) (Fin r) O, P.map (IsLocalRing.residue O) = X →
        matAct (M := K) (P.map (algebraMap O Λ)) ∈ Submodule.span Λ (Set.range fun g =>
          matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ))) by
    exact H _ (by rw [hsp]; exact Submodule.mem_top) P rfl
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨g, rfl⟩ := hX
    intro P hP
    rw [act_congr (K := K) hm P _ hP]
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    intro P hP
    have hP0 : P.map (IsLocalRing.residue O) = (0 : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O) := by
      rw [hP]; ext i j; simp
    rw [act_congr (K := K) hm P 0 hP0]
    have h0 : matAct (M := K) ((0 : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)) = 0 := by
      refine LinearMap.ext fun v => funext fun i => ?_
      simp [matAct]
    rw [h0]
    exact Submodule.zero_mem _
  | add X Y _ _ hX hY =>
    intro P hP
    obtain ⟨P₁, hP₁⟩ := lift X
    have hP₂ : (P - P₁).map (IsLocalRing.residue O) = Y := by
      have e : (P - P₁).map (IsLocalRing.residue O) =
          P.map (IsLocalRing.residue O) - P₁.map (IsLocalRing.residue O) := by
        ext i j; simp
      rw [e, hP, hP₁, add_sub_cancel_left]
    have e : P = P₁ + (P - P₁) := by abel
    rw [e, act_add]
    exact Submodule.add_mem _ (hX P₁ hP₁) (hY _ hP₂)
  | smul c X _ hX =>
    intro P hP
    obtain ⟨P₁, hP₁⟩ := lift X
    obtain ⟨c₀, rfl⟩ := IsLocalRing.residue_surjective c
    have h' : P.map (IsLocalRing.residue O) = (c₀ • P₁).map (IsLocalRing.residue O) := by
      rw [hP, ← hP₁]; ext i j; simp
    rw [act_congr (K := K) hm P _ h', act_smul]
    exact Submodule.smul_mem _ _ (hX P₁ hP₁)

private theorem matAct_rep {Γ O Λ K : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K]
    [Module Λ K] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ) (κ : Γ →* Λˣ) (g : Γ) (m : Fin r → K) :
    repOn (twGL ρ χ) κ K g m = ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) •
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)) m := by
  have e : (((twGL ρ χ) g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) =
      (((χ g)⁻¹ : Oˣ) : O) • ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) := by
    simp [twGL, scalGL, Matrix.smul_eq_diagonal_mul]
  show ((κ g : Λ) • matAct (M := K) ((((twGL ρ χ) g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map
    (algebraMap O Λ))) m = _
  rw [e, act_smul, smul_smul]
  rfl

theorem eq_zero_of_comm : ∀ (Γ O Λ K C : Type) [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ] [Algebra O Λ] [IsLocalHom (algebraMap O Λ)] [AddCommGroup K] [Module Λ K] [AddCommGroup C] (r : ℕ) (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ) (κ : Γ →* Λˣ), 2 ≤ r → (∀ x ∈ IsLocalRing.maximalIdeal Λ, ∀ k : K, x • k = 0) → Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → ∀ φ : (Fin r → K) →+ C, (∀ g h m, φ (repOn (twGL ρ χ) κ K g (repOn (twGL ρ χ) κ K h m)) = φ (repOn (twGL ρ χ) κ K h (repOn (twGL ρ χ) κ K g m))) → φ = 0 := by
  intro Γ O Λ K C _ _ _ _ _ _ _ _ _ _ r ρ χ κ hr hm hsp φ hφ

  have hunit : ∀ g, IsUnit ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) := fun g =>
    (κ g).isUnit.mul (((χ g)⁻¹).isUnit.map _)
  have hcomm : ∀ A ∈ Set.range fun g =>
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)),
      ∀ B ∈ Set.range fun g =>
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)),
      ∀ m, φ (A (B m)) = φ (B (A m)) := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ m
    obtain ⟨w, hw⟩ : ∃ w : Λ, ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) *
        ((κ h : Λ) * algebraMap O Λ (((χ h)⁻¹ : Oˣ) : O)) * w = 1 :=
      ⟨(((hunit g).mul (hunit h)).unit⁻¹ : Λˣ), by simp⟩
    have e := hφ g h (w • m)
    simp only [matAct_rep, map_smul, smul_smul] at e
    have e1 : w * ((κ h : Λ) * algebraMap O Λ (((χ h)⁻¹ : Oˣ) : O)) *
        ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) = 1 := by linear_combination hw
    have e2 : w * ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) *
        ((κ h : Λ) * algebraMap O Λ (((χ h)⁻¹ : Oˣ) : O)) = 1 := by linear_combination hw
    rw [e1, e2, one_smul, one_smul] at e
    exact e

  have hall : ∀ (P Q : Matrix (Fin r) (Fin r) O) (m : Fin r → K),
      φ (matAct (M := K) (P.map (algebraMap O Λ)) (matAct (M := K) (Q.map (algebraMap O Λ)) m)) =
        φ (matAct (M := K) (Q.map (algebraMap O Λ)) (matAct (M := K) (P.map (algebraMap O Λ)) m)) :=
    fun P Q => comm_span _ φ hcomm _ (matAct_of_span_residue_spans ρ hm hsp P) _ (matAct_of_span_residue_spans ρ hm hsp Q)

  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  have hsingle : ∀ (a : Fin r) (x : K), φ (Pi.single a x) = 0 := by
    intro a x
    obtain ⟨b, hb⟩ := exists_ne a
    have e := hall (Matrix.of fun i j => if i = a ∧ j = b then (1 : O) else 0)
      (Matrix.of fun i j => if i = b ∧ j = b then (1 : O) else 0) (Pi.single b x)
    simp only [matAct_single] at e
    simpa [Pi.single_eq_of_ne hb] using e
  refine AddMonoidHom.ext fun m => ?_
  rw [← Finset.univ_sum_single m, map_sum]
  simp [hsingle]

end GlobalTheory.ResComm
end

