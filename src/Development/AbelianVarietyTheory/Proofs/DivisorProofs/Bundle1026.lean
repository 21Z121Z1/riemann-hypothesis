import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem rat_mem_adicCompletionIntegers_eventually (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le ?_
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} (b : Module.Basis κ ℚ C) (v : HeightOneSpectrum ℤ)

theorem repr_tmul_apply (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

theorem eq_sum_tmul [Fintype κ] (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

theorem isIntB_mul_star_eventually : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (σ : C →+* Cᵐᵒᵖ) (κ : Type)
    (b : Module.Basis κ ℚ C), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) ∧
      (∀ y, IsIntB v b y → IsIntB v b (starT σ (v.adicCompletion ℚ) y).unop) := by
  intro C _ _ _ σ κ b
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (σ (b t.1)).unop t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (hc.and hs)
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨hcv, hsv⟩ := hv
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_⟩
  · rw [eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : κ → (v.adicCompletion ℚ ⊗[ℚ] C)ᵐᵒᵖ), (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : v.adicCompletion ℚ ⊗[ℚ] C ≃+ _).symm f Finset.univ
    rw [eq_sum_tmul b v y, map_sum, hu, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply]
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.AdicSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegral
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem eventually_int_of_isCompact {p : ℕ} (K : Set (AfP p)) (hK : IsCompact K) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ K, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ := by
  obtain ⟨s, hs⟩ := hK.elim_directed_cover
    (fun s : Finset (AwayP p) => {z : AfP p | ∀ v ∉ s, AfP.eval v z ∈ v.1.adicCompletionIntegers ℚ})
    (fun s => RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ s))
    (fun y _ => by
      have h : {v : AwayP p | ¬ AfP.eval v y ∈ v.1.adicCompletionIntegers ℚ}.Finite := y.2
      refine Set.mem_iUnion.2 ⟨h.toFinset, fun v hv => ?_⟩
      by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc))
    (fun s t => ⟨s ∪ t, fun y hy v hv => hy v fun h => hv (Finset.mem_union_left _ h),
      fun y hy v hv => hy v fun h => hv (Finset.mem_union_right _ h)⟩)
  rw [Filter.eventually_cofinite]
  refine (s.finite_toSet).subset fun v hv => ?_
  by_contra hvs
  exact hv fun a ha => hs ha v hvs

theorem repr_map_eval {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (y : AfP p ⊗[ℚ] G.C)
    (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) y) i =
      AfP.eval v ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    simp only [basV, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem cptInt : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), piV G v '' Ω ⊆ IntV G v := by
  intro p _ G Ω hΩ
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  set bA := Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C) with hbA
  have hrep : ∀ i, Continuous (fun y : AfP p ⊗[ℚ] G.C => bA.repr y i) := fun i => by
    have := IsModuleTopology.continuous_of_linearMap (R := AfP p) (bA.coord i)
    exact this
  have hg1 : Continuous (fun g : G.GAf => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hg2 : Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hg3 : Continuous (fun g : G.GAf => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  have hg4 : Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  have h1 := Filter.eventually_all.2 fun i => eventually_int_of_isCompact _ (hΩ.image ((hrep i).comp hg1))
  have h2 := Filter.eventually_all.2 fun i => eventually_int_of_isCompact _ (hΩ.image ((hrep i).comp hg2))
  have h3 := eventually_int_of_isCompact _ (hΩ.image hg3)
  have h4 := eventually_int_of_isCompact _ (hΩ.image hg4)
  filter_upwards [h1, h2, h3, h4] with v hv1 hv2 hv3 hv4
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have e : ((((piV G v g : Gv G v) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
          (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := rfl
    rw [e, repr_map_eval]
    exact hv1 i _ ⟨g, hg, rfl⟩
  · have e : (((((piV G v g : Gv G v) : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
        Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
          ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := rfl
    rw [e, repr_map_eval]
    exact hv2 i _ ⟨g, hg, rfl⟩
  · exact hv3 _ ⟨g, hg, rfl⟩
  · exact hv4 _ ⟨g, hg, rfl⟩

end GlobalTheory.OrbFinAf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

theorem ratCast_mem_intV_eventually (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2.mono fun _ hv => hv
  exact (Subtype.val_injective.tendsto_cofinite).eventually h

variable {p : ℕ} [Fact p.Prime]

theorem basV_repr_tmul (G : HTGroup p) (v : AwayP p) (r : Qv v) (c : G.C) (k : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (r ⊗ₜ c) k = r * algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c k) := by
  simp [basV, Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_tmul (G : HTGroup p) (v : AwayP p) (y : Qv v ⊗[ℚ] G.C) :
    y = ∑ i, (basV G v).repr y i ⊗ₜ (Module.finBasis ℚ G.C i) := by
  conv_lhs => rw [← (basV G v).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basV, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem isIntV_of_eq_sum (G : HTGroup p) (v : AwayP p) {ι : Type*} (s : Finset ι) (r : ι → Qv v) (c : ι → G.C)
    (hr : ∀ i ∈ s, r i ∈ v.1.adicCompletionIntegers ℚ)
    (hc : ∀ i ∈ s, ∀ k, algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr (c i) k) ∈ v.1.adicCompletionIntegers ℚ) :
    IsIntV G v (∑ i ∈ s, r i ⊗ₜ c i) := by
  intro k
  rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  exact sum_mem fun i hi => by rw [basV_repr_tmul]; exact mul_mem (hr i hi) (hc i hi k)

theorem intV_order_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v 1 ∧ (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) ∧ (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) := by
  intro p _ G
  set b := Module.finBasis ℚ G.C
  have H := ((Filter.eventually_all.2 fun k => ratCast_mem_intV_eventually p (b.repr 1 k)).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun k =>
      ratCast_mem_intV_eventually p (b.repr (b i * b j) k))).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k =>
      ratCast_mem_intV_eventually p (b.repr (G.star (b i)).unop k))
  refine H.mono fun v ⟨⟨h1, hm⟩, hs⟩ => ⟨?_, ?_, ?_⟩
  · intro k
    rw [Algebra.TensorProduct.one_def, basV_repr_tmul, one_mul]
    exact h1 k
  · intro y z hy hz
    have e : y * z = ∑ ij : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
        ((basV G v).repr y ij.1 * (basV G v).repr z ij.2) ⊗ₜ (b ij.1 * b ij.2) := by
      conv_lhs => rw [eq_sum_tmul G v y, eq_sum_tmul G v z]
      rw [Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
      simp only [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    rw [e]
    exact isIntV_of_eq_sum G v _ _ _ (fun ij _ => mul_mem (hy ij.1) (hz ij.2)) (fun ij _ k => hm ij.1 ij.2 k)
  · intro y hy
    have e : (starT G.star (Qv v) y).unop = ∑ i, (basV G v).repr y i ⊗ₜ (G.star (b i)).unop := by
      conv_lhs => rw [eq_sum_tmul G v y]
      rw [map_sum, ← MulOpposite.opAddEquiv_symm_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => starT_tmul G.star (Qv v) _ _
    rw [e]
    exact isIntV_of_eq_sum G v _ _ _ (fun i _ => hy i) (fun i _ k => hs i k)

end GlobalTheory.OrbFinAf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMem
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

open scoped RestrictedProduct

namespace GlobalTheory.OrbFinAf

section General

variable {C : Type} [Ring C] [Algebra ℚ C] {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ C)
  {R : Type} [CommRing R] [Algebra ℚ R] (S : Subring R)

theorem repr_mul_mem (hc : ∀ i j k, algebraMap ℚ R (b.repr (b i * b j) k) ∈ S)
    {y y' : R ⊗[ℚ] C} (hy : ∀ i, (Algebra.TensorProduct.basis R b).repr y i ∈ S)
    (hy' : ∀ i, (Algebra.TensorProduct.basis R b).repr y' i ∈ S) (k : ι) :
    (Algebra.TensorProduct.basis R b).repr (y * y') k ∈ S := by
  set B := Algebra.TensorProduct.basis R b
  have hB : ∀ i j, B.repr (B i * B j) k = algebraMap ℚ R (b.repr (b i * b j) k) := by
    intro i j
    simp [B, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
  rw [← B.sum_repr y, ← B.sum_repr y', Finset.sum_mul_sum]
  simp only [smul_mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, hB]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.mul_mem (S.mul_mem (hy i) (hy' j)) (hc i j k)

end General

theorem eventually_rat_mem (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h := (show Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] from
    algebraMap ℚ (AfP p) q).2
  filter_upwards [h] with v hv
  have e : (AfP.eval v) (algebraMap ℚ (AfP p) q) = algebraMap ℚ (Qv v) q := (AfP.eval v).commutes q
  rw [← e]
  exact hv

theorem mul_mem_IntV_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v := by
  intro p _ G
  have hall : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i j k,
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) ∈ v.1.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_rat_mem p _
  filter_upwards [hall] with v hv
  intro a ha a' ha'
  obtain ⟨h1, h2, h3, h4⟩ := ha
  obtain ⟨h1', h2', h3', h4'⟩ := ha'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have := repr_mul_mem (Module.finBasis ℚ G.C) (v.1.adicCompletionIntegers ℚ).toSubring hv h1 h1' k
    simpa [IsIntV, basV] using this
  · intro k
    have := repr_mul_mem (Module.finBasis ℚ G.C) (v.1.adicCompletionIntegers ℚ).toSubring hv h2' h2 k
    simpa [IsIntV, basV, _root_.mul_inv_rev] using this
  · have := (v.1.adicCompletionIntegers ℚ).mul_mem _ _ h3 h3'
    simpa using this
  · have := (v.1.adicCompletionIntegers ℚ).mul_mem _ _ h4' h4
    simpa [_root_.mul_inv_rev] using this

end GlobalTheory.OrbFinAf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOneTmulAdicIntegralCoords
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem exists_finset_isIntB_one_tmul (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type)
    (b : Module.Basis κ ℚ M) (x : M) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] x) := by
  have hfin : (⋃ i ∈ ((b.repr x).support : Set κ), HeightOneSpectrum.Support ℤ (b.repr x i)).Finite :=
    (b.repr x).support.finite_toSet.biUnion fun i _ => HeightOneSpectrum.Support.finite ℤ (b.repr x i)
  refine ⟨hfin.toFinset, fun v hv i => ?_⟩
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  by_cases hi : b.repr x i = 0
  · rw [hi, map_zero]; exact zero_mem _
  · have h1 : v ∉ HeightOneSpectrum.Support ℤ (b.repr x i) := fun h =>
      hv (hfin.mem_toFinset.2 (Set.mem_biUnion (Finsupp.mem_support_iff.2 hi) h))
    have h2 : v.valuation ℚ (b.repr x i) ≤ 1 := not_lt.1 h1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h3 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (b.repr x i)
    rw [← h3] at h2
    convert h2 using 2
    rfl

end GlobalTheory.AdicSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SchANonzero

theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

def intPts (F : Type) [Field F] [NumberField F] (κ : Type) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  Set.pi Set.univ fun _ => {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem isOpen_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsOpen (intPts F κ) :=
  isOpen_set_pi Set.finite_univ fun _ _ =>
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)

theorem isCompact_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsCompact (intPts F κ) :=
  isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral F

theorem isClosed_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsClosed (intPts F κ) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  exact (isCompact_intPts F κ).isClosed

theorem indicator_intPts_mem_SB (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (intPts F κ).indicator (1 : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_intPts F κ) (isClosed_intPts F κ)
    fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ intPts F κ
  · exact ⟨intPts F κ, isOpen_intPts F κ, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨(intPts F κ)ᶜ, (isClosed_intPts F κ).isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem exists_mem_schA_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ φ ∈ schA F κ, φ 0 ≠ 0 := by
  intro F _ _ κ _
  classical
  obtain ⟨f, hf⟩ := exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)
  refine ⟨pureA F f ((intPts F κ).indicator 1), Submodule.subset_span ⟨f, _, indicator_intPts_mem_SB F κ, rfl⟩, ?_⟩
  have h0 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ intPts F κ := fun i _ v => by
    show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
    exact zero_mem (v.adicCompletionIntegers F)
  simp only [pureA]
  rw [Set.indicator_of_mem h0]
  have hz : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  rw [hz, hf]
  simp

end GlobalTheory.SchANonzero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicUnitCarryingFormToNormMultipleStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnit_carrying_form_to_normMultiple : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.C) (M : Type) [Field M] [NumberField M] (j : M →+* G.C) (σ : M →+* M), (∀ y : M, β * sh G (j y) = j (σ y) * β) → ∀ (a : M) (u : (AfP p ⊗[ℚ] M)ˣ), (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a → ∃ U : (AfP p ⊗[ℚ] G.C)ˣ, (U : AfP p ⊗[ℚ] G.C) * inC G (AfP p) β * (starT G.star (AfP p) U).unop = inC G (AfP p) (j a * β) ∧ ∀ y : G.C, (∀ m : M, y * j m = j m * y) → inC G (AfP p) y * U = U * inC G (AfP p) y := by
  first | (exact @GlobalTheory.adelic_norm_move) | (exact GlobalTheory.adelic_norm_move) | (intros; apply GlobalTheory.adelic_norm_move  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCoverStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_etale_pullback_coordinates_goodCover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (D δ : ℕ) (U : X.Opens), GlobalTheory.CoverDeg.GoodCover p π D δ U → ∀ (W : X.Opens) (x : Fin D → Γ(X, W)), IsAffineOpen W → (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale → ∀ z : Y, π z ∈ U → π z ∈ W → ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W, (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  first | exact @GlobalTheory.CoverDeg.etale_pullback_coords | exact GlobalTheory.CoverDeg.etale_pullback_coords | (intros; apply GlobalTheory.CoverDeg.etale_pullback_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicNumbersExtensionConjVacuumNormSqStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicNumbers_extension_conj_vacuum_normSq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (ρ : M →ₐ[ℚ] ℂ), TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → ∃ ρ' : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, (∀ x ∈ M, x ∈ TaylorLogMetric.Qbar ∧ StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ' x = StandardLatticesGL3.cj M ρ x) ∧ TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ' (TaylorLogMetric.lamOf D cc dl) = TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl) ∧ 0 < TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)) ∧ ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (L₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L₀ → StandardLatticesGL3.SD D L₀' → Even (a * b) → ∀ F F₀ : TaylorLogMetric.VC D a b → ℂ, StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L₀ L₀' F₀ → TaylorLogMetric.CoefIn D F₀ M → TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ') (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ') L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ' F) = TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ) L₀ L₀') (TaylorLogMetric.fnConj D M ρ F₀) := by
  first | exact @GlobalTheory.ConjVacuumNorm.exists_extension_normSq_eq | exact GlobalTheory.ConjVacuumNorm.exists_extension_normSq_eq | (intros; apply GlobalTheory.ConjVacuumNorm.exists_extension_normSq_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProductStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_lift_unitaryGroupProduct : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∃ L : (D.what₂.Tau → Mt V.rank) → GA D V, (∀ u ∈ UG (gramAt D V), L u ∈ GinfC V ∧ ∀ τ, archM V (θ τ) (L u) = u τ) ∧ (∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), L (u * u') = L u * L u') ∧ ContinuousOn L (UG (gramAt D V)) ∧ (∀ g, (fun τ => archM V (θ τ) g) ∈ UG (gramAt D V)) ∧ (∀ u ∈ GinfC V, L (fun τ => archM V (θ τ) u) = u) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ g = L (Pi.mulSingle τ g)) ∧ (∀ g, ∃ a ∈ GfC V, ∃ u ∈ GinfC V, g = a * u) ∧ (∀ a ∈ GfC V, ∀ u ∈ GinfC V, a * u = u * a) ∧ ∀ τ, (gramAt D V τ).IsHermitian ∧ (gramAt D V τ).det ≠ 0 := by
  first | exact @GlobalTheory.RealLift.exists_real_lift | exact GlobalTheory.RealLift.exists_real_lift | (intros; apply GlobalTheory.RealLift.exists_real_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCoStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_etaleCoordinates_finiteFreeEtaleCover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (x : X) (U₁ U₂ : X.Opens), IsAffineOpen U₁ → x ∈ U₁ → (∃ t : Fin D → Γ(X, U₁), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t).Etale) → IsAffineOpen U₂ → x ∈ U₂ → IsAffineOpen (π ⁻¹ᵁ U₂) → (π.app U₂).hom.Etale → (π.app U₂).hom.Finite → (letI := (π.app U₂).hom.toAlgebra; Module.Free Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) ∧ Module.finrank Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) = δ) → ∃ U : X.Opens, x ∈ U ∧ GlobalTheory.CoverDeg.GoodCover p π D δ U := by
  first | exact @GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover | exact GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover | (intros; apply GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharsOfTameLpDim
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameInertiaChars

theorem exists_basis_eigen {n : ℕ} {Γ : Type} (f : Γ → Module.End ℂ (Fin n → ℂ))
    (hs : ∀ g, (f g).IsSemisimple) (hc : ∀ g k, Commute (f g) (f k)) :
    ∃ B : Module.Basis (Fin n) ℂ (Fin n → ℂ), ∀ j g, ∃ c : ℂ, f g (B j) = c • B j := by
  have h1 := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun g k _ => hc g k) fun g => Module.End.iSup_maxGenEigenspace_eq_top _
  simp only [fun g => (hs g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
  let T : Set (Fin n → ℂ) := {v | ∀ g, ∃ c : ℂ, f g v = c • v}
  have h2 : ⊤ ≤ Submodule.span ℂ T := by
    rw [← h1]
    exact iSup_le fun χ v hv => Submodule.subset_span fun g =>
      ⟨χ g, Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv g)⟩
  let B := Module.Basis.ofSpan h2
  have h3 := Module.Basis.ofSpan_subset h2
  refine ⟨B.reindex (B.indexEquiv (Pi.basisFun ℂ (Fin n))), fun j => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact h3 ⟨_, rfl⟩

theorem charpoly_of_basis {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (B : Module.Basis (Fin n) ℂ (Fin n → ℂ))
    (c : Fin n → ℂ) (hB : ∀ j, f (B j) = c j • B j) : f.charpoly = ∏ j, (X - C (c j)) := by
  rw [← LinearMap.charpoly_toMatrix f B, ← Matrix.charpoly_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, hB, map_smul, B.repr_self, Matrix.diagonal_apply]
  by_cases e : i = j
  · subst e; simp
  · simp [Finsupp.single_apply, Ne.symm e, e]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.TameInertiaChars

end
end

