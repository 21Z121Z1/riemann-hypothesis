import Formalism.FockGram.Bundle0001

-- bundled from Formalism.FockGram.FockGramProofs.DetSymPow
section
open Finset Matrix MvPolynomial

noncomputable section

namespace Formalism.E

section SlopeTestRemainingChoices

variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

def spLin (A : Matrix σ σ R) (i : σ) : MvPolynomial σ R := ∑ j, C (A i j) * X j

def spRow (A : Matrix σ σ R) (s : Multiset σ) : MvPolynomial σ R := (s.map (spLin A)).prod

def spHom (A : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := aeval (spLin A)

end SlopeTestRemainingChoices

section Field

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K] [CharZero K]

end Field

def genMat (σ : Type*) : Matrix σ σ (MvPolynomial (σ × σ) ℤ) := Matrix.of fun i j => X (i, j)

end Formalism.E
end
end

-- bundled from Formalism.FockGram.FockGramProofs.FockHerm
section
open MvPolynomial

namespace Formalism.E

theorem fischerInnerConjSymm_holds : FockHerm := by
  intro R τ _ _ f g
  classical
  unfold Formalism.E.fock
  rw [star_sum]
  have hf : ∀ m ∉ f.support, f.coeff m = 0 := fun m h => by simpa using h
  have hg : ∀ m ∉ g.support, g.coeff m = 0 := fun m h => by simpa using h
  have e1 : ∑ m ∈ f.support, star (f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)) =
      ∑ m ∈ f.support ∪ g.support, star (f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)) :=
    Finset.sum_subset Finset.subset_union_left (fun m _ hm => by simp [hf m hm])
  have e2 : ∑ m ∈ g.support, g.coeff m * star (f.coeff m) * (Formalism.A.mfact m : R) =
      ∑ m ∈ f.support ∪ g.support, g.coeff m * star (f.coeff m) * (Formalism.A.mfact m : R) :=
    Finset.sum_subset Finset.subset_union_right (fun m _ hm => by simp [hg m hm])
  rw [e1, e2]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [star_mul, mul_comm, mul_left_comm]

end Formalism.E
end

-- bundled from Formalism.FockGram.FockGramProofs.FockPerm
section
open Finset Matrix MvPolynomial

noncomputable section

namespace Formalism.E
namespace FockPermanent

variable {R τ : Type*} [CommRing R]

def bil (f g : MvPolynomial τ R) : R :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (Formalism.A.mfact m : R)

lemma bil_eq_of_subset {f g : MvPolynomial τ R} {S : Finset (τ →₀ ℕ)} (h : f.support ⊆ S) :
    bil f g = ∑ m ∈ S, f.coeff m * g.coeff m * (Formalism.A.mfact m : R) :=
  Finset.sum_subset h (fun m _ hm => by
    have : f.coeff m = 0 := by simpa using hm
    simp [this])

lemma bil_add_left (f f' g : MvPolynomial τ R) : bil (f + f') g = bil f g + bil f' g := by
  classical
  rw [bil_eq_of_subset (S := f.support ∪ f'.support) support_add,
    bil_eq_of_subset (S := f.support ∪ f'.support) subset_union_left,
    bil_eq_of_subset (S := f.support ∪ f'.support) subset_union_right, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

lemma bil_add_right (f g g' : MvPolynomial τ R) : bil f (g + g') = bil f g + bil f g' := by
  rw [bil, bil, bil, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

lemma deg1 (d : τ →₀ ℕ) (h : d.degree = 1) : ∃ k, d = Finsupp.single k 1 := by
  classical
  have hc : Multiset.card (Finsupp.toMultiset d) = 1 := by
    rw [Finsupp.card_toMultiset, Finsupp.sum]; exact h
  obtain ⟨k, hk⟩ := Multiset.card_eq_one.mp hc
  refine ⟨k, ?_⟩
  calc d = Multiset.toFinsupp (Finsupp.toMultiset d) := (Finsupp.toMultiset_toFinsupp d).symm
    _ = _ := by rw [hk]; simp

lemma lin_repr (x : MvPolynomial τ R) (hx : x.IsHomogeneous 1) :
    x = ∑ k ∈ x.vars, C (x.coeff (Finsupp.single k 1)) * X k := by
  classical
  ext n
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_X]
  by_cases h0 : x.coeff n = 0
  · rw [h0]; symm
    apply sum_eq_zero
    intro k _
    split_ifs with h
    · rw [h, h0, mul_one]
    · rw [mul_zero]
  · have hd : n.degree = 1 := by
      by_contra hd; exact h0 (hx.coeff_eq_zero hd)
    obtain ⟨k, rfl⟩ := deg1 n hd
    rw [sum_eq_single k]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro h; exact hb (Finsupp.single_left_injective one_ne_zero h)
    · intro hk; exfalso; apply hk
      rw [mem_vars]
      exact ⟨Finsupp.single k 1, mem_support_iff.mpr h0, by simp⟩

lemma pderiv_lin (z : MvPolynomial τ R) (hz : z.IsHomogeneous 1) (k : τ) :
    pderiv k z = C (z.coeff (Finsupp.single k 1)) := by
  classical
  ext m
  rw [coeff_pderiv, coeff_C]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg (Ne.symm hm), hz.coeff_eq_zero, zero_mul]
    rw [map_add, Finsupp.degree_single]
    intro h; apply hm
    rw [← Finsupp.degree_eq_zero_iff]; omega

end FockPermanent

end Formalism.E
end
end

-- bundled from Formalism.FockGram.FockGramProofs.FockSesq
section
open Finset MvPolynomial

namespace Formalism.E

section
variable {R τ : Type*} [CommRing R] [StarRing R]

theorem fock_eq_sum_of_subset (f g : MvPolynomial τ R) (s : Finset (τ →₀ ℕ))
    (h : f.support ⊆ s) :
    fock f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R) := by
  classical
  unfold fock
  refine Finset.sum_subset h ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fock_add_left (f f' g : MvPolynomial τ R) : fock (f + f') g = fock f g + fock f' g := by
  classical
  rw [fock_eq_sum_of_subset (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fock_eq_sum_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    fock_eq_sum_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)

theorem fock_smul_left (c : R) (f g : MvPolynomial τ R) : fock (c • f) g = c * fock f g := by
  classical
  rw [fock_eq_sum_of_subset (c • f) g f.support MvPolynomial.support_smul,
    fock_eq_sum_of_subset f g f.support (Finset.Subset.refl _), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)

theorem fock_add_right (f g g' : MvPolynomial τ R) : fock f (g + g') = fock f g + fock f g' := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add, star_add]; ring)

theorem fock_smul_right (c : R) (f g : MvPolynomial τ R) :
    fock f (c • g) = star c * fock f g := by
  unfold fock
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by
    rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
    ring)

end

theorem existsSesqForm : FockSesq := by
  intro R τ _ _
  exact ⟨LinearMap.mk₂'ₛₗ (RingHom.id R) (starRingEnd R) (fun f g => fock f g)
    (fun f f' g => fock_add_left f f' g) (fun c f g => by rw [fock_smul_left]; rfl)
    (fun f g g' => fock_add_right f g g') (fun c f g => by rw [fock_smul_right]; rfl),
    fun f g => rfl⟩

end Formalism.E
end

-- bundled from Formalism.FockGram.FockGramProofs.HermDualOf
section
open Matrix LinearMap Module

noncomputable section

namespace Formalism.E

private theorem mem_hdual_span_iff_forall_pairing_mem_range {S K V ι : Type} [CommRing S] [Field K] [StarRing K]
    [Algebra S K] [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower S K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (b : ι → V)
    (hstar : ∀ s : S, star (algebraMap S K s) ∈ Set.range (algebraMap S K)) (x : V) :
    x ∈ hdual B (Submodule.span S (Set.range b)) ↔
      ∀ i, B (b i) x ∈ Set.range (algebraMap S K) := by
  simp only [hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Submodule.mem_one, Set.mem_range]
  constructor
  · intro h i
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact h i
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨p, hp⟩ := hy
      obtain ⟨q, hq⟩ := hz
      exact ⟨p + q, by rw [map_add, hp, hq, map_add, LinearMap.add_apply]⟩
    | smul s y _ hy =>
      obtain ⟨p, hp⟩ := hy
      obtain ⟨t, ht⟩ := hstar s
      refine ⟨t * p, ?_⟩
      rw [map_mul, ht, hp, ← algebraMap_smul K s y, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, starRingEnd_apply]

private theorem eq_zero_of_gram_det_ne_zero_of_pairing_basis_eq_zero {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (B : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V)
    (hG : (Matrix.of fun i j => B (b i) (b j)).det ≠ 0) (z : V) (hz : ∀ i, B (b i) z = 0) :
    z = 0 := by
  have hc : (Matrix.of fun i j => B (b i) (b j)) *ᵥ (fun j => b.repr z j) = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← hz i]
    conv_rhs => rw [← b.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hv := Matrix.eq_zero_of_mulVec_eq_zero hG hc
  exact b.forall_coord_eq_zero_iff.1 fun i => by simpa [Basis.coord_apply] using congrFun hv i

private theorem isUnit_algebraNorm_int_iff_isUnit {S : Type} [CommRing S] [Module.Free ℤ S]
    [Module.Finite ℤ S] (x : S) : IsUnit (Algebra.norm ℤ x) ↔ IsUnit x := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det]
  constructor
  · intro hu
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
    exact isUnit_iff_exists_inv.2 ⟨y, by simpa using hy⟩
  · intro hu
    exact hu.map (Algebra.lmul ℤ S)

theorem hermDual_of (h : SubIndexNorm) : HermDual := by
  intro S K V ι _ _ _ _ _ _ _ _ _ _ B b hinj hstar
  have hL := mem_hdual_span_iff_forall_pairing_mem_range B b hstar
  have part1 : Submodule.span S (Set.range b) ≤ hdual B (Submodule.span S (Set.range b)) ↔
      ∀ i j, B (b i) (b j) ∈ Set.range (algebraMap S K) := by
    constructor
    · intro hle i j
      exact (hL _).1 (hle (Submodule.subset_span ⟨j, rfl⟩)) i
    · intro hG
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (hL _).2 fun i => hG i j
  refine ⟨part1, ?_⟩
  intro _ _ GS hGS hdet
  have hLle := part1.2 fun i j => ⟨GS i j, (hGS i j).symm⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Submodule S V, L = Submodule.span S (Set.range b) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : Submodule S V, M = hdual B L := ⟨_, rfl⟩
  rw [← hLdef] at hLle ⊢
  rw [← hMdef] at hLle ⊢
  have hmemM : ∀ x, x ∈ M ↔ ∀ i, B (b i) x ∈ Set.range (algebraMap S K) := by
    rw [hMdef, hLdef]
    exact hL
  obtain ⟨G, hG⟩ : ∃ G : Matrix ι ι K, G = Matrix.of fun i j => B (b i) (b j) := ⟨_, rfl⟩
  have hGij : ∀ i j, G i j = B (b i) (b j) := fun i j => by rw [hG]; rfl
  have hGdet : G.det = algebraMap S K GS.det := by
    have e : G = (algebraMap S K).mapMatrix GS := by
      ext i j
      rw [hGij, hGS]
      rfl
    rw [e, RingHom.map_det]
  have hGdet0 : G.det ≠ 0 := by
    rw [hGdet]
    exact fun h0 => hdet (hinj (by rw [h0, map_zero]))
  have hnd := eq_zero_of_gram_det_ne_zero_of_pairing_basis_eq_zero B b (hG ▸ hGdet0)
  obtain ⟨d, hd⟩ : ∃ d : ι → V, ∀ k, d k = ∑ j, G⁻¹ j k • b j := ⟨_, fun k => rfl⟩
  have hBd : ∀ i k, B (b i) (d k) = if i = k then 1 else 0 := by
    intro i k
    have e := congrFun (congrFun (Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.2 hGdet0)) i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    rw [← e, hd, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, hGij, mul_comm]
  have hdM : ∀ k, d k ∈ M := fun k => (hmemM _).2 fun i =>
    ⟨if i = k then 1 else 0, by rw [hBd]; split_ifs <;> simp⟩
  obtain ⟨dM, hdM'⟩ : ∃ dM : ι → M, ∀ k, (dM k : V) = d k :=
    ⟨fun k => ⟨d k, hdM k⟩, fun k => rfl⟩
  have hBsum : ∀ (g : ι → S) i, B (b i) (∑ k, g k • d k) = algebraMap S K (g i) := by
    intro g i
    rw [map_sum]
    simp_rw [LinearMap.map_smul_of_tower, hBd]
    simp [Algebra.smul_def]
  have hliD : LinearIndependent S dM := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' : ∑ k, g k • d k = 0 := by
      have e := congrArg Subtype.val hg
      rw [Submodule.coe_sum] at e
      simpa [Submodule.coe_smul, hdM'] using e
    have e := hBsum g i
    rw [hg', map_zero] at e
    exact hinj (by rw [← e, map_zero])
  have hspD : ⊤ ≤ Submodule.span S (Set.range dM) := by
    rintro ⟨x, hx⟩ -
    choose s hs using (hmemM x).1 hx
    have hxe : x = ∑ k, s k • d k := by
      refine sub_eq_zero.1 (hnd _ fun i => ?_)
      rw [map_sub, hBsum, hs, sub_self]
    have e : (⟨x, hx⟩ : M) = ∑ k, s k • dM k := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, hdM']
      exact hxe
    rw [e]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨bD, hbD⟩ : ∃ bD : Basis ι S M, ∀ k, bD k = dM k :=
    ⟨Basis.mk hliD hspD, fun k => Basis.mk_apply _ _ _⟩
  have hbM : ∀ j, b j ∈ M := fun j => (hmemM _).2 fun i => ⟨GS i j, (hGS i j).symm⟩
  obtain ⟨bM, hbM'⟩ : ∃ bM : ι → M, ∀ j, (bM j : V) = b j :=
    ⟨fun j => ⟨b j, hbM j⟩, fun j => rfl⟩
  have hliB : LinearIndependent S bM := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hg' : ∑ k, algebraMap S K (g k) • b k = 0 := by
      have e := congrArg Subtype.val hg
      rw [Submodule.coe_sum] at e
      simpa [Submodule.coe_smul, hbM', algebraMap_smul] using e
    have e := Fintype.linearIndependent_iff.1 b.linearIndependent _ hg' j
    exact hinj (by rw [e, map_zero])
  obtain ⟨bN, hbN⟩ : ∃ bN : Basis ι S (Submodule.span S (Set.range bM)), ∀ j, (bN j : M) = bM j :=
    ⟨Basis.span hliB, fun j => congrArg Subtype.val (Basis.span_apply hliB j)⟩
  have key := h S M ι bD (Submodule.span S (Set.range bM)) bN
  have hbexp : ∀ j, bM j = ∑ k, GS k j • bD k := by
    intro j
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, hbD, hdM', hbM']
    refine (sub_eq_zero.1 (hnd _ fun i => ?_))
    rw [map_sub, hGS, show B (b i) (∑ k, GS k j • d k) = algebraMap S K (GS i j) from
      hBsum (fun k => GS k j) i, sub_self]
  have hdetS : bD.det (fun i => (bN i : M)) = GS.det := by
    rw [Basis.det_apply]
    congr 1
    ext i j
    rw [Basis.toMatrix_apply, hbN, hbexp, bD.repr_sum_self]
  have hspanN : ∀ x : M, x ∈ Submodule.span S (Set.range bM) ↔ (x : V) ∈ L := by
    intro x
    have e : Submodule.map M.subtype (Submodule.span S (Set.range bM)) = L := by
      rw [Submodule.map_span, ← Set.range_comp, hLdef]
      congr 2
      funext j
      exact hbM' j
    rw [← e, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hidx : L.toAddSubgroup.relIndex M.toAddSubgroup = (Algebra.norm ℤ GS.det).natAbs := by
    rw [← hdetS, ← key]
    have hsub : L.toAddSubgroup.addSubgroupOf M.toAddSubgroup =
        (Submodule.span S (Set.range bM)).toAddSubgroup := by
      ext x
      rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
        hspanN]
    rw [AddSubgroup.relIndex, hsub]
    rfl
  refine ⟨hidx, ?_⟩
  rw [← isUnit_algebraNorm_int_iff_isUnit, Int.isUnit_iff_natAbs_eq, ← hidx, AddSubgroup.relIndex_eq_one,
    Submodule.toAddSubgroup_le]
  exact ⟨fun e => e.le, fun hle => le_antisymm hle hLle⟩

end Formalism.E
end
end

-- bundled from Formalism.FockGram.FockGramProofs.HermitianTensorMulHermitian
section
open Matrix LinearMap Module TensorProduct

noncomputable section
namespace Formalism.E

theorem hermitian_tensor_mul_apply : HTmulApply := by
  intro R M₁ M₂ _ _ _ _ _ _ B₁ B₂ x₁ y₁ x₂ y₂
  simp [htmul, tensorFunctional]

example {R M₁ M₂ : Type} [CommRing R] [StarRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R)
    (a : R) (z w : M₁ ⊗[R] M₂) :
    htmul B₁ B₂ (a • z) w = star a * htmul B₁ B₂ z w ∧ htmul B₁ B₂ z (a • w) = a * htmul B₁ B₂ z w := by
  simp [starRingEnd_apply]

theorem hermitian_tensor_mul_gram : HTmulGram := by
  intro R M₁ M₂ ι₁ ι₂ _ _ _ _ _ _ _ _ _ _ B₁ B₂ v₁ v₂
  have h : sgram (htmul B₁ B₂) (fun p : ι₁ × ι₂ => v₁ p.1 ⊗ₜ[R] v₂ p.2) =
      Matrix.kroneckerMap (· * ·) (sgram B₁ v₁) (sgram B₂ v₂) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [sgram, htmul, tensorFunctional]
  refine ⟨h, ?_⟩
  rw [h]
  exact Matrix.det_kronecker _ _

theorem hermitian_tensor_mul_hermitian : HTmulHerm := by
  intro R M₁ M₂ _ _ _ _ _ _ B₁ B₂ h₁ h₂
  rw [LinearMap.isSymm_def] at *
  intro z w
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ x₂ =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul y₁ y₂ =>
      simp only [htmul, tensorFunctional] at *
      simp [← h₁ x₁ y₁, ← h₂ x₂ y₂, starRingEnd_apply, mul_comm]
    | add a b ha hb => simp_all
  | add a b ha hb => simp_all

example {R M : Type} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
    (B : M →ₗ⋆[R] M →ₗ[R] R) : B.IsSymm ↔ ∀ x y, star (B x y) = B y x := by
  simp [LinearMap.isSymm_def, starRingEnd_apply]

example (n : ℤ) : star n = n := rfl

end Formalism.E
end
end

