import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageComponentwiseSubgroupEqProd
section
open Filter GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.AvgRestr

private lemma mem_rStab_iff_forall_mul_right_invariant {H : Type} [Group H] (u : H → ℂ) (k : H) :
    k ∈ rStab u ↔ ∀ x, u (x * k) = u x := Iff.rfl

private lemma avg_eq_inv_index_mul_finsum_rStab_quotient {H : Type} [Group H] (u : H → ℂ) :
    avg u = ((rStab u).index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ rStab u, u q.out := rfl

lemma apply_out {H : Type} [Group H] (u : H → ℂ) (x : H) : u ((x : H ⧸ rStab u).out) = u x := by
  have h : ((x : H ⧸ rStab u).out)⁻¹ * x ∈ rStab u :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (x : H ⧸ rStab u))
  have h2 := (mem_rStab_iff_forall_mul_right_invariant u _).mp h ((x : H ⧸ rStab u).out)
  rw [mul_inv_cancel_left] at h2
  exact h2.symm

private lemma rStab_comp_eq_comap_of_surjective {A B : Type} [Group A] [Group B] (π : A →* B)
    (hπ : Function.Surjective π) (v : B → ℂ) : rStab (v ∘ π) = (rStab v).comap π := by
  ext k
  rw [Subgroup.mem_comap, mem_rStab_iff_forall_mul_right_invariant, mem_rStab_iff_forall_mul_right_invariant]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hπ y
    have h2 := h x
    simpa [Function.comp, map_mul] using h2
  · intro h x
    simp only [Function.comp_apply, map_mul]
    exact h (π x)

private lemma bijective_quotient_comap_of_surjective {A B : Type} [Group A] [Group B] (π : A →* B)
    (hπ : Function.Surjective π) (S : Subgroup B) :
    Function.Bijective (fun q : A ⧸ S.comap π => ((π q.out : B) : B ⧸ S)) := by
  constructor
  · intro q q' h
    have h2 := QuotientGroup.eq.mp h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_comap,
      map_mul, map_inv]
    exact h2
  · intro z
    obtain ⟨a, ha⟩ := hπ z.out
    refine ⟨(a : A ⧸ S.comap π), ?_⟩
    have h2 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : A ⧸ S.comap π))
    rw [Subgroup.mem_comap, map_mul, map_inv] at h2
    show ((π (a : A ⧸ S.comap π).out : B) : B ⧸ S) = z
    rw [← QuotientGroup.out_eq' z, ← ha, QuotientGroup.eq]
    exact h2

theorem avg_comp_surj {A B : Type} [Group A] [Group B] (π : A →* B) (hπ : Function.Surjective π) (v : B → ℂ) :
    avg (v ∘ π) = avg v := by
  rw [avg_eq_inv_index_mul_finsum_rStab_quotient, avg_eq_inv_index_mul_finsum_rStab_quotient, rStab_comp_eq_comap_of_surjective π hπ v]
  let e := Equiv.ofBijective _ (bijective_quotient_comap_of_surjective π hπ (rStab v))
  have hidx : ((rStab v).comap π).index = (rStab v).index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact Nat.card_congr e
  rw [hidx]
  congr 1
  refine (finsum_congr ?_).trans (finsum_comp_equiv e (f := fun z : B ⧸ rStab v => v z.out))
  intro q
  exact (apply_out v (π q.out)).symm

private lemma bijective_pi_quotient_to_quotient_pi {J : Type} (M : J → Type) [∀ j, Group (M j)] (R : ∀ j, Subgroup (M j)) :
    Function.Bijective
      (fun q : (∀ j, M j) ⧸ Subgroup.pi Set.univ R => fun j => ((q.out j : M j) : M j ⧸ R j)) := by
  constructor
  · intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_pi]
    intro j _
    have h2 := QuotientGroup.eq.mp (congrFun h j)
    simpa only [Pi.mul_apply, Pi.inv_apply] using h2
  · intro z
    refine ⟨(((fun j => (z j).out) : ∀ j, M j) : (∀ j, M j) ⧸ Subgroup.pi Set.univ R), ?_⟩
    funext j
    have hm := QuotientGroup.eq.mp
      (QuotientGroup.out_eq' ((((fun j => (z j).out) : ∀ j, M j)) : (∀ j, M j) ⧸ Subgroup.pi Set.univ R))
    have hj := (Subgroup.mem_pi _).mp hm j (Set.mem_univ j)
    simp only [Pi.mul_apply, Pi.inv_apply] at hj
    show ((_ : M j) : M j ⧸ R j) = z j
    rw [← QuotientGroup.out_eq' (z j), QuotientGroup.eq]
    exact hj

theorem avg_pi {J : Type} [Fintype J] (M : J → Type) [∀ j, Group (M j)] (v : ∀ j, M j → ℂ)
    (hv : ∀ j, (rStab (v j)).index ≠ 0) :
    avg (fun x : (∀ j, M j) => ∏ j, v j (x j)) = ∏ j, avg (v j) := by
  classical
  haveI : ∀ j, (rStab (v j)).FiniteIndex := fun j => ⟨hv j⟩
  haveI : ∀ j, Fintype (M j ⧸ rStab (v j)) := fun j => Fintype.ofFinite _
  let S : Subgroup (∀ j, M j) := Subgroup.pi Set.univ (fun j => rStab (v j))
  have hS : S ≤ rStab (fun x : (∀ j, M j) => ∏ j, v j (x j)) := by
    intro k hk
    rw [mem_rStab_iff_forall_mul_right_invariant]
    intro x
    refine Finset.prod_congr rfl (fun j _ => ?_)
    exact (mem_rStab_iff_forall_mul_right_invariant (v j) (k j)).mp ((Subgroup.mem_pi _).mp hk j (Set.mem_univ j)) (x j)
  let e := Equiv.ofBijective _ (bijective_pi_quotient_to_quotient_pi M (fun j => rStab (v j)))
  have hidx : S.index = ∏ j, (rStab (v j)).index := by
    rw [Subgroup.index_eq_card, Nat.card_congr e, Nat.card_pi]
    simp only [Subgroup.index_eq_card]
  have hS0 : S.index ≠ 0 := by
    rw [hidx]; exact Finset.prod_ne_zero_iff.mpr (fun j _ => hv j)
  have hsum : (∑ᶠ q : (∀ j, M j) ⧸ S, ∏ j, v j (q.out j)) = ∏ j, ∑ᶠ q : M j ⧸ rStab (v j), v j q.out := by
    have h1 : ∀ q : (∀ j, M j) ⧸ S, ∏ j, v j (q.out j) = ∏ j, v j ((e q j).out) := by
      intro q
      refine Finset.prod_congr rfl (fun j _ => ?_)
      exact (apply_out (v j) (q.out j)).symm
    rw [finsum_congr h1]
    refine (finsum_comp_equiv e (f := fun z : (∀ j, M j ⧸ rStab (v j)) => ∏ j, v j (z j).out)).trans ?_
    rw [finsum_eq_sum_of_fintype]
    simp only [finsum_eq_sum_of_fintype]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [GlobalTheory.BCT.avg_eq_of_le_rStab _ _ S hS hS0]
  simp only [avg_eq_inv_index_mul_finsum_rStab_quotient]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Nat.cast_prod, ← hidx, hsum]

theorem avg_restrProd : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (u : ∀ i, KH i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ i, (rStab (u i)).index ≠ 0) → (∀ᶠ i in cofinite, ∀ k, u i k = 1) → avg (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) = ∏ᶠ i, avg (u i) := by
  intro ι G _ H _ p K KH hK u happ hu h1
  classical
  have hs := Filter.eventually_cofinite.mp h1
  let T := hs.toFinset
  let π : K →* ∀ j : T, KH j :=
    MonoidHom.pi (fun j : T => ((p j).comp K.subtype).codRestrict (KH j) (fun k => (hK k).1 k.2 j))
  have hπ : Function.Surjective π := by
    intro y
    let y' : ∀ i, H i := fun i => if h : i ∈ T then ((y ⟨i, h⟩ : KH i) : H i) else 1
    have hy' : ∀ i, y' i ∈ KH i := by
      intro i
      simp only [y']
      split_ifs with h
      · exact (y ⟨i, h⟩).2
      · exact (KH i).one_mem
    obtain ⟨x, hx⟩ := happ y' (Filter.Eventually.of_forall hy')
    have hxK : x ∈ K := (hK x).2 (fun i => by rw [hx i]; exact hy' i)
    refine ⟨⟨x, hxK⟩, ?_⟩
    funext j
    apply Subtype.ext
    change p (j : ι) x = ((y j : KH (j : ι)) : H (j : ι))
    rw [hx]
    simp [y', j.2]
  have hfun : (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) =
      (fun y : (∀ j : T, KH j) => ∏ j : T, u j (y j)) ∘ π := by
    funext k
    rw [Function.comp_apply, finprod_eq_prod_of_mulSupport_subset _ (s := T)]
    · exact (Finset.prod_coe_sort T (fun i => u i ⟨p i k, (hK k).1 k.2 i⟩)).symm
    · intro i hi
      simp only [Finset.mem_coe, T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro hall
      exact (Function.mem_mulSupport.mp hi) (hall _)
  rw [hfun, avg_comp_surj π hπ]
  refine (avg_pi (fun j : T => (KH j : Type)) (fun j => u j) (fun j => hu j)).trans ?_
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
  · exact Finset.prod_coe_sort T (fun i => avg (u i))
  · intro i hi
    simp only [Finset.mem_coe, T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro hall
    apply Function.mem_mulSupport.mp hi
    have hc : u i = fun _ => 1 := funext hall
    rw [hc]
    exact (GlobalTheory.AvgLin.avg_linear_translate_const _ (u i) (u i) 1 1 (hu i) (hu i)).2.2.2

end GlobalTheory.AvgRestr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageRestrictedProductMaxCompactProd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AvgRestr

theorem apply_out_mk {G : Type} [Group G] (u : G → ℂ) (x : G) :
    u ((QuotientGroup.mk x : G ⧸ rStab u).out) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
  rw [hk]
  exact k.2 x

theorem avg_pi_comp {H : Type} [Group H] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (π : H →* ∀ i, G i) (hπ : Function.Surjective π) (u : ∀ i, G i → ℂ) (hu : ∀ i, (rStab (u i)).index ≠ 0) :
    avg (fun k => ∏ i, u i (π k i)) = ∏ i, avg (u i) := by
  set P : Subgroup (∀ i, G i) := Subgroup.pi Set.univ fun i => rStab (u i) with hP
  set R : Subgroup H := P.comap π with hRdef
  have hPi : P.index = ∏ i, (rStab (u i)).index := by
    simp_rw [hP, Subgroup.index, ← Nat.card_pi]
    refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
    rw [QuotientGroup.leftRel_pi]
  have hRi : R.index = ∏ i, (rStab (u i)).index := by
    rw [hRdef, Subgroup.index_comap_of_surjective _ hπ, hPi]
  have hR0 : R.index ≠ 0 := by rw [hRi]; exact Finset.prod_ne_zero_iff.2 fun i _ => hu i
  have hRle : R ≤ rStab (fun k => ∏ i, u i (π k i)) := by
    intro k hk x
    have hk' : ∀ i, π k i ∈ rStab (u i) := fun i => ((Subgroup.mem_pi _).1 hk) i (Set.mem_univ i)
    simp only [map_mul, Pi.mul_apply]
    exact Finset.prod_congr rfl fun i _ => hk' i (π x i)
  rw [avg_eq_of_le_rStab H _ R hRle hR0]
  haveI : R.FiniteIndex := ⟨hR0⟩
  haveI : ∀ i, (rStab (u i)).FiniteIndex := fun i => ⟨hu i⟩
  haveI : Fintype (H ⧸ R) := Fintype.ofFinite _
  haveI : ∀ i, Fintype (G i ⧸ rStab (u i)) := fun i => Fintype.ofFinite _
  let e : H ⧸ R → ∀ i, G i ⧸ rStab (u i) := fun q i => QuotientGroup.mk (π q.out i)
  have he : Function.Bijective e := by
    constructor
    · intro q q' hq
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      apply QuotientGroup.eq.2
      show π (q.out⁻¹ * q'.out) ∈ P
      refine (Subgroup.mem_pi _).2 fun i _ => ?_
      have := QuotientGroup.eq.1 (congrFun hq i)
      simpa [map_mul, map_inv] using this
    · intro x
      obtain ⟨k, hk⟩ := hπ fun i => (x i).out
      refine ⟨QuotientGroup.mk k, funext fun i => ?_⟩
      obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul R k
      have hr' : π r ∈ P := r.2
      show (QuotientGroup.mk (π (QuotientGroup.mk k : H ⧸ R).out i) : G i ⧸ rStab (u i)) = x i
      rw [hr, map_mul, Pi.mul_apply, hk]
      conv_rhs => rw [← QuotientGroup.out_eq' (x i)]
      apply QuotientGroup.eq.2
      simpa using ((Subgroup.mem_pi _).1 hr') i (Set.mem_univ i)
  have hsum : ∑ᶠ q : H ⧸ R, ∏ i, u i (π q.out i) = ∏ i, ∑ᶠ q : G i ⧸ rStab (u i), u i q.out := by
    rw [finsum_eq_sum_of_fintype]
    simp_rw [finsum_eq_sum_of_fintype]
    rw [Fintype.prod_sum]
    exact Fintype.sum_bijective e he _ _ fun q => Finset.prod_congr rfl fun i _ => (apply_out_mk (u i) _).symm
  rw [hsum, hRi]
  simp only [avg]
  rw [Finset.prod_mul_distrib]
  push_cast
  rw [Finset.prod_inv_distrib]

end GlobalTheory.AvgRestr

namespace GlobalTheory.AvgRestr

theorem avg_restr_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)),
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ),
    (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) →
    avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      ∏ᶠ v, avg (u v) := by
  intro X V Y _ _ _ _ pf K hX u hu hev
  obtain ⟨S, hS⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually hev
  set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg
  let π : Kg →* ∀ v : S, K v.1 := MonoidHom.pi fun v =>
    ((pf v.1).comp Kg.subtype).codRestrict (K v.1) fun k => Subgroup.mem_iInf.1 k.2 v.1
  have hπ : Function.Surjective π := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    have hz : ∀ v, z v ∈ K v := fun v => by
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z (Eventually.of_forall hz)
    have hxK : x ∈ Kg := Subgroup.mem_iInf.2 fun v => by
      show pf v x ∈ K v
      rw [hx v]; exact hz v
    refine ⟨⟨x, hxK⟩, funext fun v => Subtype.ext ?_⟩
    show pf v.1 x = (y v : Y v.1)
    rw [hx v.1]
    simp [z, v.2]
  have hF : (fun k : Kg => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      fun k => ∏ v : S, u v.1 (π k v) := by
    funext k
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv (hS v h _),
      ← Finset.prod_coe_sort S]
    rfl
  have hA : ∏ᶠ v, avg (u v) = ∏ v : S, avg (u v.1) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv ?_,
      ← Finset.prod_coe_sort S]
    have hc : u v = fun _ => 1 := funext (hS v h)
    rw [hc]
    exact (GlobalTheory.AvgLin.avg_linear_translate_const _ (fun _ : K v => (1 : ℂ)) (fun _ => 1) 1 1
      (by rw [← hc]; exact hu v) (by rw [← hc]; exact hu v)).2.2.2
  rw [hF, hA]
  exact avg_pi_comp π hπ (fun v : S => u v.1) fun v => hu v.1

end GlobalTheory.AvgRestr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarCharMulConjEqAbs
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ImaginaryModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases hx : ∃ x, σ x ≠ x
  · obtain ⟨x, hx⟩ := hx
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sig_sig h]; ring
  · push_neg at hx
    exfalso
    have hr : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := h.2.2.2 τ x
      rw [hx x] at this
      exact this.symm
    exact InfinitePlace.isComplex_mk_iff.1 (h.2.1.isComplex _) hr

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => simp [cA, sigR]

section Iso

variable (σ : E →ₐ[F] E) [IsTopologicalRing (AE F E)]

def splitIm (hσ : ∀ x, σ (σ x) = x) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) : (imA σ × imA σ) ≃ₜ+ AE F E where
  toFun p := (p.1 : AE F E) + inclR (F := F) (AF F) δ * p.2
  invFun z := (⟨inclR (F := F) (AF F) (2⁻¹ : E) * (z - cA σ z), by
      rw [mem_imA, map_mul, map_sub, cA_inclR, cA_cA σ hσ, map_inv₀ σ 2, map_ofNat σ 2]; ring⟩,
    ⟨inclR (F := F) (AF F) (2⁻¹ : E) * inclR (F := F) (AF F) δ⁻¹ * (z + cA σ z), by
      rw [mem_imA, map_mul, map_mul, map_add, cA_inclR, cA_inclR, cA_cA σ hσ, map_inv₀ σ 2, map_inv₀ σ δ,
        map_ofNat σ 2, hδ, inv_neg, map_neg]; ring⟩)
  left_inv p := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AE F E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    have hz : cA σ (x + inclR (F := F) (AF F) δ * y) = -x + inclR (F := F) (AF F) δ * y := by
      rw [map_add, map_mul, hx, hy, cA_inclR, hδ, map_neg]; ring
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show inclR (F := F) (AF F) (2⁻¹ : E) * ((x + inclR (F := F) (AF F) δ * y) - cA σ (x + inclR (F := F) (AF F) δ * y)) = x
      rw [hz]; linear_combination x * hh
    · show inclR (F := F) (AF F) (2⁻¹ : E) * inclR (F := F) (AF F) δ⁻¹ *
        ((x + inclR (F := F) (AF F) δ * y) + cA σ (x + inclR (F := F) (AF F) δ * y)) = y
      rw [hz]
      linear_combination (y * inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹) * hh + y * hc
  right_inv z := by
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AE F E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    show inclR (F := F) (AF F) (2⁻¹ : E) * (z - cA σ z) + inclR (F := F) (AF F) δ *
      (inclR (F := F) (AF F) (2⁻¹ : E) * inclR (F := F) (AF F) δ⁻¹ * (z + cA σ z)) = z
    linear_combination z * hh + inclR (F := F) (AF F) (2⁻¹ : E) * (z + cA σ z) * hc
  map_add' p q := by
    show ((p.1 + q.1 : imA σ) : AE F E) + _ * ((p.2 + q.2 : imA σ) : AE F E) = _
    push_cast; ring
  continuous_toFun := by
    exact (continuous_subtype_val.comp continuous_fst).add
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    have hc := continuous_cA σ
    exact (Continuous.subtype_mk (continuous_const.mul (continuous_id.sub hc)) _).prodMk
      (Continuous.subtype_mk (continuous_const.mul (continuous_id.add hc)) _)

theorem splitIm_apply (hσ : ∀ x, σ (σ x) = x) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) (p : imA σ × imA σ) :
    splitIm σ hσ δ hδ0 hδ p = (p.1 : AE F E) + inclR (F := F) (AF F) δ * p.2 := rfl

end Iso

variable (F E) in

def scal [IsTopologicalRing (AE F E)] : AE F E ≃ₜ+ Matrix (Fin 1) (Fin 1) (AE F E) where
  toFun z := Matrix.of fun _ _ => z
  invFun M := M 0 0
  left_inv z := rfl
  right_inv M := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    rfl
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_pi fun _ => continuous_id
  continuous_invFun := (continuous_apply 0).comp (continuous_apply 0)

theorem addEquivAddHaarChar_imA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ →
    ∀ [IsTopologicalRing (AE F E)] [LocallyCompactSpace (imA σ)] [MeasurableSpace (imA σ)] [BorelSpace (imA σ)]
      (l : (AE F E)ˣ) (L : imA σ ≃ₜ+ imA σ), (∀ b, (L b : AE F E) = l * cA σ l * b) → addEquivAddHaarChar L = absE F E l := by
  intro F E _ _ _ _ _ σ B hB _ _ _ _ l L hL
  have hcm := hB.cm
  haveI : IsTotallyReal F := hcm.1
  have hσ := sig_sig hcm
  obtain ⟨δ, hδ0, hδ⟩ := exists_anti hcm
  obtain ⟨-, hlc, hsc, ht2⟩ := topAE F E
  letI : MeasurableSpace (AE F E) := borel _
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin 1) (Fin 1) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 1 → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → AE F E))
  letI : MeasurableSpace (Matrix (Fin 1) (Fin 1) (AE F E)) := borel _
  haveI : BorelSpace (Matrix (Fin 1) (Fin 1) (AE F E)) := ⟨rfl⟩
  set Φ := splitIm σ hσ δ hδ0 hδ
  set M : AE F E ≃ₜ+ AE F E := (Φ.symm.trans (GlobalTheory.ModuLR.prodCE L L)).trans Φ
  set a : (AE F E)ˣ := l * GlobalTheory.Doubling.conjUnit σ l
  have ha : (a : AE F E) = l * cA σ l := by
    show (l : AE F E) * sigR (AF F) σ l = _
    rw [cA_eq_sigR]
  have hM : ∀ z, M z = a * z := by
    intro z
    obtain ⟨p, rfl⟩ := Φ.surjective z
    show Φ (GlobalTheory.ModuLR.prodCE L L (Φ.symm (Φ p))) = a * Φ p
    rw [ContinuousAddEquiv.symm_apply_apply, GlobalTheory.ModuLR.prodCE_apply, splitIm_apply, splitIm_apply, hL, hL, ha]
    ring
  set g : GL (Fin 1) (AE F E) := Units.map (Matrix.scalar (Fin 1) : AE F E →+* _).toMonoidHom a
  have hg : Matrix.GeneralLinearGroup.det g = a := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    rfl
  have hT : ((scal F E).symm.trans M).trans (scal F E) = GlobalTheory.ModuLR.lrCE g 1 := by
    ext u i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    show M (u 0 0) = (((g : Matrix (Fin 1) (Fin 1) (AE F E)) * u * 1 : Matrix (Fin 1) (Fin 1) (AE F E)) 0 0)
    rw [hM, Matrix.mul_one, Matrix.mul_apply, Fin.sum_univ_one]
    rfl
  have h1 : addEquivAddHaarChar M = absE F E a := by
    have := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (scal F E) M
    rw [← this, hT]
    rw [GlobalTheory.ModuLR.chi_lr F E 1 1 g 1, hg, map_one, map_one]
    simp
  haveI : SecondCountableTopology (imA σ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : T2Space (imA σ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (imA σ × imA σ) := Prod.borelSpace
  have h2 : addEquivAddHaarChar M = addEquivAddHaarChar L * addEquivAddHaarChar L := by
    rw [GlobalTheory.ModuLR.addEquivAddHaarChar_transport Φ, GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE]
  have h3 : absE F E a = absE F E l * absE F E l := by
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit]
  exact (mul_self_inj (by positivity) (by positivity)).1 (h2.symm.trans (h1.trans h3))

end GlobalTheory.ImaginaryModulus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureUniqueSigmaCompactNormalisedCompactOp
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

theorem haar_unique_of_sigmaCompact_normalised :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (K : ℕ → Set G), (∀ j, IsCompact (K j) ∧ MeasurableSet (K j)) → (⋃ j, K j) = Set.univ →
    ∀ (s : Set G) (c : ENNReal), IsOpen s → IsCompact s → s.Nonempty → ν s = c * μ s → ν = c • μ := by
  intro G _ _ _ _ _ _ μ ν _ _ _ K hK hcov s c hso hsc hsn hνs
  have key : ∀ A : Set G, IsCompact (closure A) →
      ν A = (Measure.haarScalarFactor ν μ : ENNReal) * μ A := fun A hA => by
    have := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν μ hA
    rw [this, ENNReal.smul_def, smul_eq_mul]
  have hs0 : μ s ≠ 0 := (hso.measure_pos μ hsn).ne'
  have hstop : μ s ≠ ⊤ := hsc.measure_lt_top.ne
  have hc : c = (Measure.haarScalarFactor ν μ : ENNReal) := by
    have h1 := key s (hsc.closure_of_subset subset_rfl)
    rw [hνs] at h1
    exact (ENNReal.mul_left_inj hs0 hstop).mp h1
  subst hc
  ext A hA
  let B : ℕ → Set G := fun j => A ∩ Set.accumulate K j
  have hBmono : Monotone B := fun i j hij => Set.inter_subset_inter_right _ (Set.monotone_accumulate hij)
  have hBcl : ∀ j, IsCompact (closure (B j)) := fun j =>
    (isCompact_accumulate (fun i => (hK i).1) j).closure_of_subset Set.inter_subset_right
  have hBU : (⋃ j, B j) = A := by
    simp only [B, ← Set.inter_iUnion, Set.iUnion_accumulate, hcov, Set.inter_univ]
  rw [← hBU, hBmono.measure_iUnion, hBmono.measure_iUnion]
  simp only [Measure.smul_apply, smul_eq_mul]
  exact iSup_congr fun j => key _ (hBcl j)

end GlobalTheory
end

