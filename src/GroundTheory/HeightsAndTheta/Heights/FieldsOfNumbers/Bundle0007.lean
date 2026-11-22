import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBase
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Point

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

def blockMonomial (i : ∀ k, ι k) (m : K → ℕ) : MRing ι F :=
  ∏ k, X ⟨k, i k⟩ ^ m k

omit [∀ k, Fintype (ι k)] in

theorem blockMonomial_isMultiHomog (i : ∀ k, ι k) (m : K → ℕ) :
    IsMultiHomog (blockMonomial (F := F) i m) m := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MRing ι F) ^ m k) (fun k => m k • blockWeight ι ⟨k, i k⟩)
    (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, i k⟩).pow (m k))
  have hm : (∑ k, m k • blockWeight ι ⟨k, i k⟩) = m := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hm] at h
  exact h

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem blockMonomial_add (i : ∀ k, ι k) (m n : K → ℕ) :
    blockMonomial (F := F) i (m + n) = blockMonomial i m * blockMonomial i n := by
  simp [blockMonomial, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem blockMonomial_mk_ne_zero (P : Ideal (MRing ι F)) [P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ P) (m : K → ℕ) :
    Ideal.Quotient.mk P (blockMonomial i m) ≠ 0 := by
  unfold blockMonomial
  rw [map_prod, Finset.prod_ne_zero_iff]
  intro k _
  rw [map_pow]
  refine pow_ne_zero _ ?_
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact hi k

end Point

theorem IntNumBase.proof (h1 : MixedDiffConst.Statement.{u}) : IntNumBase.Statement.{u} := by
  intro F _ K _ _ ι _ P hP hrel
  have := hP.isPrime

  have hev : ∀ᶠ m in Filter.atTop, hilbFn P m = intNum F P (n := 0) ![] := by
    have h0 : relDim P = ((0 : ℕ) : WithBot (WithTop ℤ)) := by rw [hrel]; rfl
    filter_upwards [(h1 F K ι P hP.multiHomog hP.relevant 0 h0).1 ![]] with m hm
    simpa [mixedDiff] using hm
  set c := intNum F P (n := 0) ![] with hc
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp hev
  choose i hi using hP.relevant
  set A := MRing ι F ⧸ P
  set L := FractionRing A
  let xm : (K → ℕ) → L := fun m => algebraMap A L (Ideal.Quotient.mk P (blockMonomial i m))
  have hxm : ∀ m, xm m ≠ 0 := fun m => by
    simp only [xm, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    exact blockMonomial_mk_ne_zero P i hi m
  have hxm_add : ∀ m n, xm (m + n) = xm m * xm n := fun m n => by
    simp only [xm, blockMonomial_add, map_mul]

  let φ : (K → ℕ) → A →ₗ[F] L := fun m =>
    (LinearMap.mulRight F (xm m)⁻¹).comp (IsScalarTower.toAlgHom F A L).toLinearMap
  have hφ : ∀ m a, φ m a = algebraMap A L a / xm m := fun m a => by
    simp [φ, div_eq_mul_inv]
  have hφinj : ∀ m, Function.Injective (φ m) := fun m a b hab => by
    rw [hφ, hφ, div_left_inj' (hxm m)] at hab
    exact IsFractionRing.injective A L hab
  let U : (K → ℕ) → Submodule F L := fun m => (gradedPiece P m).map (φ m)
  have memU : ∀ m y, y ∈ U m ↔ ∃ f : MRing ι F, IsMultiHomog f m ∧
      y = algebraMap A L (Ideal.Quotient.mk P f) / xm m := fun m y => by
    simp only [U, gradedPiece, Submodule.mem_map, hφ]
    constructor
    · rintro ⟨a, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨f, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hf, rfl⟩, rfl⟩
  have hfinU : ∀ m, FiniteDimensional F (U m) := fun m => by
    have := ((GradedFinite.proof.{u}) F K ι P m).1
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (hφinj m) _)
  have hrankU : ∀ m, Module.finrank F (U m) = Module.finrank F (gradedPiece P m) := fun m =>
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (hφinj m) _)).symm
  have hmono : ∀ m n, m ≤ n → U m ≤ U n := fun m n hmn y hy => by
    obtain ⟨f, hf, rfl⟩ := (memU m y).mp hy
    refine (memU n _).mpr ⟨f * blockMonomial i (n - m), ?_, ?_⟩
    · have := hf.mul (blockMonomial_isMultiHomog (F := F) i (n - m))
      rwa [add_tsub_cancel_of_le hmn] at this
    · have hn : xm n = xm m * xm (n - m) := by rw [← hxm_add, add_tsub_cancel_of_le hmn]
      rw [hn, map_mul, map_mul]
      exact (mul_div_mul_right _ _ (hxm (n - m))).symm
  have hmul : ∀ m n y z, y ∈ U m → z ∈ U n → y * z ∈ U (m + n) := fun m n y z hy hz => by
    obtain ⟨f, hf, rfl⟩ := (memU m y).mp hy
    obtain ⟨g, hg, rfl⟩ := (memU n z).mp hz
    refine (memU _ _).mpr ⟨f * g, hf.mul hg, ?_⟩
    rw [hxm_add, map_mul, map_mul]
    exact div_mul_div_comm _ _ _ _

  let N : K → ℕ := fun k => (M0 k).toNat
  have hrankc : ∀ n, N ≤ n → (Module.finrank F (U n) : ℤ) = c := fun n hn => by
    rw [hrankU, ← ((GradedFinite.proof.{u}) F K ι P n).2]
    refine hM0 _ fun k => ?_
    exact (Int.self_le_toNat (M0 k)).trans (by exact_mod_cast hn k)
  have hstab : ∀ m, U m ≤ U N := fun m => by
    have hN : U N = U (m ⊔ N) := by
      have := hfinU (m ⊔ N)
      refine Submodule.eq_of_le_of_finrank_eq (hmono _ _ le_sup_right) ?_
      have h1 := hrankc N le_rfl
      have h2 := hrankc (m ⊔ N) le_sup_right
      exact_mod_cast h1.trans h2.symm
    rw [hN]
    exact hmono _ _ le_sup_left

  have hone : (1 : L) ∈ U N := by
    refine hstab 0 ((memU 0 1).mpr ⟨1, isWeightedHomogeneous_one F _, ?_⟩)
    have : xm 0 = 1 := by simp [xm, blockMonomial]
    rw [this, map_one, map_one, div_one]
  let S : Subalgebra F L := (U N).toSubalgebra hone fun y z hy hz => hstab _ (hmul _ _ _ _ hy hz)
  have : FiniteDimensional F S := hfinU N
  let E : IntermediateField F L := S.toIntermediateField fun y hy =>
    S.inv_mem_of_algebraic (x := ⟨y, hy⟩) ((IsIntegral.of_finite F (⟨y, hy⟩ : S)).map S.val).isAlgebraic
  have hEq : homFracDegZero P = E := by
    apply le_antisymm
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x ⟨b, f, g, hf, hg, hgP, rfl⟩
      have hfU : algebraMap A L (Ideal.Quotient.mk P f) / xm b ∈ E :=
        hstab b ((memU b _).mpr ⟨f, hf, rfl⟩)
      have hgU : algebraMap A L (Ideal.Quotient.mk P g) / xm b ∈ E :=
        hstab b ((memU b _).mpr ⟨g, hg, rfl⟩)
      have hg0 : algebraMap A L (Ideal.Quotient.mk P g) ≠ 0 := by
        rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
        exact hgP
      have heq : algebraMap A L (Ideal.Quotient.mk P f) / algebraMap A L (Ideal.Quotient.mk P g) =
          algebraMap A L (Ideal.Quotient.mk P f) / xm b *
            (algebraMap A L (Ideal.Quotient.mk P g) / xm b)⁻¹ := by
        rw [inv_div, div_mul_div_comm, mul_comm (xm b), mul_div_mul_right _ _ (hxm b)]
      rw [SetLike.mem_coe, heq]
      exact E.mul_mem hfU (E.inv_mem hgU)
    · intro y hy
      obtain ⟨f, hf, rfl⟩ := (memU N y).mp hy
      exact IntermediateField.subset_adjoin _ _
        ⟨N, f, blockMonomial i N, hf, blockMonomial_isMultiHomog i N,
          fun h => blockMonomial_mk_ne_zero P i hi N (Ideal.Quotient.eq_zero_iff_mem.mpr h), rfl⟩
  have hES : Subalgebra.toSubmodule E.toSubalgebra = U N := rfl
  let e : E ≃ₗ[F] U N := LinearEquiv.ofEq _ _ hES
  rw [hEq]
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq]
  exact (hrankc N le_rfl).symm

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPNProduct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

section Product

variable {K : Type}

def prodFn (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) : (Option K → ℤ) → ℤ :=
  fun m => A (fun k => m (some k)) * B (m none)

def diff1 (g : ℤ → ℤ) : ℤ → ℤ := fun t => g t - g (t - 1)

theorem backwardDifference_apply (g : ℤ → ℤ) (t : ℤ) : diff1 g t = g t - g (t - 1) := rfl

theorem pullDeg_some (c : K → ℤ) (k : K) :
    pullDeg Function.Embedding.some c (some k) = c k :=
  (Function.Embedding.some (α := K)).injective.extend_apply c 0 k

theorem pullDeg_none (c : K → ℤ) : pullDeg Function.Embedding.some c none = 0 := by
  unfold pullDeg
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨a, h⟩
    exact Option.some_ne_none a h

theorem diffStep_pull (c : K → ℤ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    diffStep (pullDeg Function.Embedding.some c) (prodFn A B) = prodFn (diffStep c A) B := by
  funext m
  have h1 : (fun k => (m - pullDeg Function.Embedding.some c) (some k)) =
      (fun k => m (some k)) - c := by
    funext k
    simp [pullDeg_some]
  have h2 : (m - pullDeg Function.Embedding.some c) none = m none := by
    simp [pullDeg_none]
  unfold diffStep prodFn
  rw [h1, h2]
  ring

theorem diffStep_newBlock (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    diffStep (newBlockDeg : Option K → ℤ) (prodFn A B) = prodFn A (diff1 B) := by
  funext m
  have h1 : (fun k => (m - (newBlockDeg : Option K → ℤ)) (some k)) = fun k => m (some k) := by
    funext k
    simp [newBlockDeg]
  have h2 : (m - (newBlockDeg : Option K → ℤ)) none = m none - 1 := by
    simp [newBlockDeg]
  unfold diffStep prodFn diff1
  rw [h1, h2]
  ring

theorem foldr_pull (L : List (K → ℤ)) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    (L.map (pullDeg Function.Embedding.some)).foldr diffStep (prodFn A B) =
      prodFn (L.foldr diffStep A) B := by
  induction L with
  | nil => rfl
  | cons c L ih => simp only [List.map_cons, List.foldr_cons, ih, diffStep_pull]

theorem foldr_newBlock (j : ℕ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    (List.replicate j (newBlockDeg : Option K → ℤ)).foldr diffStep (prodFn A B) =
      prodFn A (diff1^[j] B) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, diffStep_newBlock,
      Function.iterate_succ_apply']

theorem mixedDiff_prodFn {m r : ℕ} (cs : Fin r → K → ℤ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    mixedDiff (Fin.append (fun _ : Fin m => (newBlockDeg : Option K → ℤ))
        (fun i => pullDeg Function.Embedding.some (cs i))) (prodFn A B) =
      prodFn (mixedDiff cs A) (diff1^[m] B) := by
  have h : List.ofFn (fun i => pullDeg Function.Embedding.some (cs i)) =
      (List.ofFn cs).map (pullDeg Function.Embedding.some) := by
    rw [List.map_ofFn]
    rfl
  unfold mixedDiff
  rw [List.ofFn_fin_append, List.foldr_append, List.ofFn_const, h, foldr_pull, foldr_newBlock]

theorem tendsto_restrict :
    Tendsto (fun m : Option K → ℤ => fun k => m (some k)) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨fun o => Option.elim o 0 b, fun _ ha k => ha (some k)⟩

theorem eventually_none_ge (a : ℤ) : ∀ᶠ m : Option K → ℤ in atTop, a ≤ m none :=
  (eventually_ge_atTop (fun _ : Option K => a)).mono fun _ hm => hm none

theorem eventualValue_eq {f : (Option K → ℤ) → ℤ} {c : ℤ} (hf : ∀ᶠ m in atTop, f m = c) :
    eventualValue f = c := by
  have h : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨c, hf⟩
  unfold eventualValue
  rw [dif_pos h]
  obtain ⟨m, h1, h2⟩ := (h.choose_spec.and hf).exists
  exact h1.symm.trans h2

end Product

section Binomial

theorem iter_projSpaceHilb (N : ℕ) : ∀ j : ℕ, j ≤ N → ∀ s : ℕ,
    diff1^[j] (projSpaceHilb N) ((s : ℤ) + j) = (((s + N).choose (N - j) : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro _ s
    simp [projSpaceHilb]
  | succ j ih =>
    intro hj s
    have e1 : (s : ℤ) + ((j + 1 : ℕ) : ℤ) = ((s + 1 : ℕ) : ℤ) + j := by push_cast; ring
    have e2 : (s : ℤ) + ((j + 1 : ℕ) : ℤ) - 1 = (s : ℤ) + j := by push_cast; ring
    rw [Function.iterate_succ_apply', backwardDifference_apply, e2, e1, ih (by omega), ih (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, N - j = k + 1 := ⟨N - (j + 1), by omega⟩
    have hk' : N - (j + 1) = k := by omega
    rw [hk, hk', show s + 1 + N = (s + N) + 1 by omega, Nat.choose_succ_succ']
    push_cast
    ring

theorem backwardDifference_eq_zero_of_eventually_const {g : ℤ → ℤ} {a c : ℤ} (h : ∀ s : ℕ, g (s + a) = c) (s : ℕ) :
    diff1 g (s + (a + 1)) = 0 := by
  rw [backwardDifference_apply, show (s : ℤ) + (a + 1) = ((s + 1 : ℕ) : ℤ) + a by push_cast; ring,
    show ((s + 1 : ℕ) : ℤ) + a - 1 = (s : ℤ) + a by push_cast; ring, h, h, sub_self]

theorem iter_projSpaceHilb_top (N : ℕ) (t : ℤ) (ht : (N : ℤ) ≤ t) :
    diff1^[N] (projSpaceHilb N) t = 1 := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + N := ⟨(t - N).toNat, by omega⟩
  rw [iter_projSpaceHilb N N le_rfl s, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]

theorem iter_projSpaceHilb_high (N : ℕ) : ∀ i s : ℕ,
    diff1^[N + 1 + i] (projSpaceHilb N) ((s : ℤ) + ((N + 1 + i : ℕ) : ℤ)) = 0 := by
  intro i
  induction i with
  | zero =>
    intro s
    have hN : ∀ s : ℕ, diff1^[N] (projSpaceHilb N) ((s : ℤ) + (N : ℤ)) = 1 := fun s =>
      iter_projSpaceHilb_top N _ (by omega)
    have e : (s : ℤ) + ((N + 1 + 0 : ℕ) : ℤ) = s + ((N : ℤ) + 1) := by push_cast; ring
    rw [e, show N + 1 + 0 = N + 1 from rfl, Function.iterate_succ_apply']
    exact backwardDifference_eq_zero_of_eventually_const hN s
  | succ i ih =>
    intro s
    rw [show N + 1 + (i + 1) = (N + 1 + i) + 1 by omega, Function.iterate_succ_apply',
      Nat.cast_add_one]
    exact backwardDifference_eq_zero_of_eventually_const ih s

theorem iter_projSpaceHilb_above (N j : ℕ) (hj : N < j) (t : ℤ) (ht : (j : ℤ) ≤ t) :
    diff1^[j] (projSpaceHilb N) t = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = N + 1 + i := ⟨j - (N + 1), by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + ((N + 1 + i : ℕ) : ℤ) :=
    ⟨(t - ((N + 1 + i : ℕ) : ℤ)).toNat, by omega⟩
  exact iter_projSpaceHilb_high N i s

end Binomial

theorem ProductWithProjectiveSpace.proof (h1 : MixedDiffConst.Statement.{u})
    (h2 : HilbAddBlock.Statement.{u}) : ProductWithProjectiveSpace.Statement.{u} := by
  intro F _ K _ _ ι _ P hP e N r m he hrm cs
  have hH : hilbFn (addBlockPrime N P) = prodFn (hilbFn P) (projSpaceHilb N) := by
    funext x
    exact h2 F K ι P N x
  unfold intNum
  rw [hH, mixedDiff_prodFn]
  have hlim := tendsto_restrict (K := K)
  rcases lt_trichotomy m N with hmN | hmN | hmN
  · rw [if_neg hmN.ne]
    apply eventualValue_eq
    have hz := (h1 F K ι P hP.multiHomog hP.relevant e he).2 r (by omega) cs
    filter_upwards [hlim.eventually hz] with x hx
    simp only [prodFn]
    rw [hx, zero_mul]
  · subst hmN
    rw [if_pos rfl]
    obtain rfl : r = e := by omega
    apply eventualValue_eq
    have hc := (h1 F K ι P hP.multiHomog hP.relevant r he).1 cs
    filter_upwards [hlim.eventually hc, eventually_none_ge (m : ℤ)] with x hx hn
    simp only [prodFn]
    rw [hx, iter_projSpaceHilb_top m _ hn, mul_one]
    rfl
  · rw [if_neg hmN.ne']
    apply eventualValue_eq
    filter_upwards [eventually_none_ge (m : ℤ)] with x hn
    simp only [prodFn]
    rw [iter_projSpaceHilb_above N m hmN _ hn, mul_zero]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameMultiProjPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace RenameMultiProjPrime

variable {S K' : Type} [DecidableEq S] [DecidableEq K'] {κ : S → Type} {ι' : K' → Type} (E : S ≃ K')
  (σ : (Σ s, κ s) ≃ (Σ k', ι' k'))

theorem weight_mapDomain (hσ : ∀ v, (σ v).1 = E v.1) (d : (Σ s, κ s) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain σ d) =
      Finsupp.weight (blockWeight κ) d ∘ E.symm := by
  induction d using Finsupp.induction_linear with
  | zero => funext k; simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg]
    rfl
  | single v n =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    funext k
    simp only [blockWeight, hσ, Function.comp_apply, Pi.smul_apply, Pi.single_apply,
      Equiv.symm_apply_eq, smul_eq_mul]

theorem rename_weightedHomogeneousComponent {R : Type u} [CommRing R]
    (hσ : ∀ v, (σ v).1 = E v.1) (b : S → ℕ) (f : MRing κ R) :
    rename σ (weightedHomogeneousComponent (blockWeight κ) b f) =
      weightedHomogeneousComponent (blockWeight ι') (b ∘ E.symm) (rename σ f) := by
  classical
  ext m
  have hm : m = Finsupp.mapDomain σ (Finsupp.mapDomain σ.symm m) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  rw [hm, coeff_weightedHomogeneousComponent, coeff_rename_mapDomain _ σ.injective,
    coeff_rename_mapDomain _ σ.injective, coeff_weightedHomogeneousComponent,
    weight_mapDomain E σ hσ]
  have hiff : Finsupp.weight (blockWeight κ) (Finsupp.mapDomain σ.symm m) ∘ E.symm = b ∘ E.symm ↔
      Finsupp.weight (blockWeight κ) (Finsupp.mapDomain σ.symm m) = b :=
    E.symm.surjective.injective_comp_right.eq_iff
  simp only [hiff]

end RenameMultiProjPrime

theorem RenameMultiProjPrime.proof : RenameMultiProjPrime.Statement.{u} := by
  intro R _ S K' _ _ κ ι' E σ hσ P hP
  refine ⟨?_, ?_, ?_⟩
  · have := hP.isPrime
    exact Ideal.comap_isPrime _ _
  · intro f hf b
    rw [Ideal.mem_comap] at hf ⊢
    rw [RenameMultiProjPrime.rename_weightedHomogeneousComponent (R := R) E σ hσ b f]
    exact hP.multiHomog _ hf _
  · intro s
    obtain ⟨i', hi'⟩ := hP.relevant (E s)
    obtain ⟨⟨s', i⟩, hv⟩ : ∃ v, σ v = ⟨E s, i'⟩ := σ.surjective _
    have hs : s' = s := E.injective (by simpa [hv] using (hσ ⟨s', i⟩).symm)
    subst hs
    refine ⟨i, ?_⟩
    rw [Ideal.mem_comap, rename_X, hv]
    exact hi'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsContractRelDimLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ContractRelDimLe.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → relDim (contractPrime j P') ≤ relDim P'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivSupport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivCycleSupport.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ (c : K → ℕ) (f : MRing ι F), IsMultiHomog f c → f ∉ P →
    ∀ W : Ideal (MRing ι F), divCycle P f W ≠ 0 → IsMultiProjPrime W ∧ relDim W = (n : ℕ)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

