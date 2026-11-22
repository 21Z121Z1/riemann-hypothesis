import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0117
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0118
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0120

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsForallEqPowOfPowEqSelf
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertiaEigenvalues.FrobPow

open Polynomial

theorem eq_of_pow_eq_self_of_map_eq {O k : Type} [CommRing O] [IsDomain O] [Field k]
    (φ : O →+* k) (q : ℕ) (hq : (q : k) = 0) {y z : O} (hy : y ^ q = y) (hz : z ^ q = z)
    (h : φ y = φ z) : y = z := by
  have h1 := Commute.geom_sum₂_mul (Commute.all y z) q
  rw [hy, hz] at h1
  have h2 : ((∑ i ∈ Finset.range q, y ^ i * z ^ (q - 1 - i)) - 1) * (y - z) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    have h4 := congrArg φ h3
    simp only [map_sub, map_sum, map_mul, map_pow, map_one, map_zero, h] at h4
    rw [geom_sum₂_self, hq, zero_mul, zero_sub, neg_eq_zero] at h4
    exact one_ne_zero h4
  · exact sub_eq_zero.1 h3

theorem exists_forall_eq_pow_of_pow_eq_self (l : ℕ) [Fact l.Prime] {O k : Type} [CommRing O]
    [IsDomain O] [Field k] [CharP k l] (φ : O →+* k) (τ : O →+* O)
    (hτ : ∀ x, φ x = 0 → φ (τ x) = 0) (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ, ∀ x : O, x ^ l ^ n = x → τ x = x ^ l ^ a := by
  classical
  have hl : l.Prime := Fact.out
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.one_lt
  let S : Set O := {x | x ^ l ^ n = x}
  have hmon : ∀ (A : Type) [CommRing A] [Nontrivial A], (X ^ l ^ n - X : A[X]).Monic := by
    intro A _ _
    apply Monic.sub_of_left (monic_X_pow _)
    rw [degree_X, degree_X_pow]
    exact_mod_cast hq
  have hS : S.Finite := by
    refine (X ^ l ^ n - X : O[X]).roots.toFinset.finite_toSet.subset fun x hx => ?_
    have hx' : x ^ l ^ n = x := hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [mem_roots (hmon O).ne_zero]
    simp [hx']
  have hint : ∀ x ∈ S, IsIntegral ℤ x := by
    intro x hx
    have hx' : x ^ l ^ n = x := hx
    exact ⟨X ^ l ^ n - X, hmon ℤ, by simp [hx']⟩
  have hfin : Module.Finite ℤ (Algebra.adjoin ℤ S) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hS hint
  let ι : Algebra.adjoin ℤ S →+* O := (Algebra.adjoin ℤ S).val.toRingHom
  obtain ⟨a, ha⟩ := GlobalTheory.exists_forall_eq_pow_of_ker_le l (Algebra.adjoin ℤ S) k (φ.comp ι)
    (φ.comp (τ.comp ι)) (fun x hx => hτ _ hx)
  refine ⟨a, fun x hx => ?_⟩
  have h1 : φ (τ x) = φ x ^ l ^ a := ha ⟨x, Algebra.subset_adjoin hx⟩
  refine eq_of_pow_eq_self_of_map_eq φ (l ^ n) ?_ ?_ ?_ ?_
  · rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn.ne']
  · rw [← map_pow, hx]
  · rw [← pow_mul, mul_comm, pow_mul, hx]
  · rw [h1, map_pow]

theorem exists_gal_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) (σ : GQ l) :
    ∃ a : ℕ, ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a := by
  have hl : l.Prime := Fact.out
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.one_lt
  let v : Valuation (Om l) NNReal := (PadicAlgCl.valued l).v
  have hv : ∀ x : Om l, v (σ x) = v x := fun x =>
    NNReal.eq (spectralNorm_eq_of_equiv σ x).symm
  let O : ValuationSubring (Om l) := v.valuationSubring
  have hO : ∀ x : Om l, x ∈ O ↔ v x ≤ 1 := fun x => Iff.rfl
  have hm : ∀ x : O, IsLocalRing.residue O x = 0 ↔ v x < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff _ v
  have hch : CharP (IsLocalRing.ResidueField O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl).2 ?_
    rw [← map_natCast (IsLocalRing.residue O), hm]
    have : v (l : Om l) = 1 / (l : NNReal) := PadicAlgCl.valuation_p l
    rw [SubringClass.coe_natCast, this, one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  let τ : O →+* O := (σ : Om l →+* Om l).restrict O O (fun x hx => by
    rw [hO] at hx ⊢
    exact (hv x).trans_le hx)
  have hτ : ∀ x : O, ((τ x : O) : Om l) = σ x := fun x => rfl
  obtain ⟨a, ha⟩ := exists_forall_eq_pow_of_pow_eq_self l (IsLocalRing.residue O) τ
    (fun x hx => by rw [hm] at hx ⊢; rw [hτ, hv]; exact hx) n hn
  refine ⟨a, fun x hx => ?_⟩
  have hxO : x ∈ O := by
    rw [hO]
    by_contra h
    have h' : 1 < v x := not_le.1 h
    have h2 : v x ^ 1 < v x ^ l ^ n := pow_lt_pow_right₀ h' hq
    rw [← map_pow, ← map_pow, hx, pow_one] at h2
    exact lt_irrefl _ h2
  have h3 := ha ⟨x, hxO⟩ (Subtype.ext (by simpa using hx))
  have h4 := congrArg (fun y : O => (y : Om l)) h3
  simpa [hτ] using h4

end GlobalTheory.InertiaEigenvalues.FrobPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveTorusClassesOfIdempotentDecomposi
section
noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.TorusPts

section Ring

variable {A : Type} [CommRing A] {I : Type} [Fintype I]

def tt (f h c d : I → A) : A := 1 + ∑ i, ((c i - 1) * f i + (d i - 1) * h i)

theorem f_mul_tt (f h c d : I → A) (hf : ∀ i, f i * f i = f i) (hff : ∀ i j, i ≠ j → f i * f j = 0)
    (hfh : ∀ i j, f i * h j = 0) (j : I) : f j * tt f h c d = c j * f j := by
  classical
  unfold tt
  rw [mul_add, Finset.mul_sum, Finset.sum_eq_single j]
  · linear_combination (c j - 1) * hf j + (d j - 1) * hfh j j
  · intro i _ hi
    linear_combination (c i - 1) * hff j i hi.symm + (d i - 1) * hfh j i
  · simp

theorem tt_swap (f h c d : I → A) : tt f h c d = tt h f d c := by
  unfold tt
  congr 1
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

theorem tt_mul (f h c d c' d' : I → A) (hf : ∀ i, f i * f i = f i) (hff : ∀ i j, i ≠ j → f i * f j = 0)
    (hh : ∀ i, h i * h i = h i) (hhh : ∀ i j, i ≠ j → h i * h j = 0)
    (hfh : ∀ i j, f i * h j = 0) : tt f h c d * tt f h c' d' = tt f h (c * c') (d * d') := by
  have h1 := f_mul_tt f h c' d' hf hff hfh
  have h2 := f_mul_tt h f d' c' hh hhh (fun i j => by rw [mul_comm]; exact hfh j i)
  rw [← tt_swap] at h2
  have h3 : tt f h c d * tt f h c' d' =
      tt f h c' d' + ∑ i, ((c i - 1) * (f i * tt f h c' d') + (d i - 1) * (h i * tt f h c' d')) := by
    conv_lhs => arg 1; unfold tt
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3]
  simp only [h1, h2]
  unfold tt
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.mul_apply]; ring

theorem tt_one (f h : I → A) : tt f h 1 1 = 1 := by simp [tt]

end Ring

theorem isIntegral_idem {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {f : A} (hf : f * f = f) :
    IsIntegral O f := by
  nontriviality O
  refine ⟨X ^ 2 - X, ?_, ?_⟩
  · monicity!
  · simp [pow_two, hf]

theorem isIntegral_of_mul_idem {K : UQ} (B : InvAlg K) {f : B.A} (hf : f * f = f) (h0 : f ≠ 0) (x : K.E)
    (hx : IsIntegral K.O (algebraMap K.E B.A x * f)) : IsIntegral K.O x := by
  let J : Ideal B.A := Ideal.span {1 - f}
  have hJ : J ≠ ⊤ := by
    intro h
    have : (1 : B.A) ∈ J := h ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 this
    apply h0
    linear_combination (-f) * hr - r * hf
  haveI : Nontrivial (B.A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  let φ : K.E →ₐ[K.O] B.A ⧸ J := (Ideal.Quotient.mkₐ K.O J).comp (IsScalarTower.toAlgHom K.O K.E B.A)
  have hinj : Function.Injective φ := φ.toRingHom.injective
  rw [← isIntegral_algHom_iff φ hinj]
  have h1 := hx.map (Ideal.Quotient.mkₐ K.O J)
  have h2 : Ideal.Quotient.mkₐ K.O J (algebraMap K.E B.A x * f) = φ x := by
    show Ideal.Quotient.mk J _ = Ideal.Quotient.mk J (algebraMap K.E B.A x)
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.2 ⟨-algebraMap K.E B.A x, by ring⟩
  rwa [h2] at h1

theorem le_of_isIntegral {K : UQ} {a : K.O} (ha : K.Small a) (n m : ℕ)
    (h : IsIntegral K.O (((algebraMap K.O K.E a) ^ n)⁻¹ * (algebraMap K.O K.E a) ^ m)) : n ≤ m := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff).1 h
  have ha0 : algebraMap K.O K.E a ≠ 0 := by
    simpa using ha.1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have h1 : algebraMap K.O K.E (a * (a ^ d * r)) = algebraMap K.O K.E 1 := by
    simp only [map_mul, map_pow, map_one, hr]
    field_simp
    ring
  have h2 := IsFractionRing.injective K.O K.E h1
  exact ha.2.1 (IsUnit.of_mul_eq_one _ h2)

theorem torus_points : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e : ι → B.A) (S : Finset ι) (a : K.O), K.Small a → IsPre B e S → ∀ k : ℕ, ∃ f : ({i // i ∉ S} → Fin (k + 1)) → B.T ⧸ (intUnits K.O B.A).subgroupOf B.T, Function.Injective f ∧ ∀ n, IsIntegral K.O ((((Quotient.out (f n) : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) := by
  intro K B ι _ e S a ha hP k
  classical
  obtain ⟨hC, hP⟩ := hP
  choose F hFi hF0 _ _ hFS using hP
  let f : {i // i ∉ S} → B.A := fun i => F i
  let h : {i // i ∉ S} → B.A := fun i => B.σ (F i)
  have hf : ∀ i, f i * f i = f i := fun i => hFi i
  have hh : ∀ i, h i * h i = h i := fun i => by
    show B.σ _ * B.σ _ = B.σ _
    rw [← map_mul, hFi i]
  have hfe : ∀ i, f i = f i * e i := fun i => by
    rw [(hFS i i.2).2]
    linear_combination -(hf i) - (hFS i i.2).1
  have hhe : ∀ i, h i = h i * e i := fun i => by
    rw [(hFS i i.2).2]
    linear_combination -(hh i) - (hFS i i.2).1
  have hee : ∀ i j : {i // i ∉ S}, i ≠ j → e i * e j = 0 := fun i j hij =>
    hC.ortho (fun h => hij (Subtype.ext h))
  have hff : ∀ i j, i ≠ j → f i * f j = 0 := fun i j hij => by
    rw [hfe i, hfe j]; linear_combination f i * f j * hee i j hij
  have hhh : ∀ i j, i ≠ j → h i * h j = 0 := fun i j hij => by
    rw [hhe i, hhe j]; linear_combination h i * h j * hee i j hij
  have hfh : ∀ i j, f i * h j = 0 := fun i j => by
    by_cases hij : i = j
    · subst hij; exact (hFS i i.2).1
    · rw [hfe i, hhe j]; linear_combination f i * h j * hee i j hij
  set α : K.E := algebraMap K.O K.E a with hα
  have hα0 : α ≠ 0 := by simpa [hα] using ha.1
  let c : ({i // i ∉ S} → Fin (k + 1)) → {i // i ∉ S} → B.A := fun n i => algebraMap K.E B.A (α ^ (n i : ℕ))
  let d : ({i // i ∉ S} → Fin (k + 1)) → {i // i ∉ S} → B.A := fun n i => algebraMap K.E B.A (α ^ (n i : ℕ))⁻¹
  have hcd : ∀ n, c n * d n = 1 := fun n => by
    funext i
    show algebraMap K.E B.A _ * algebraMap K.E B.A _ = 1
    rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hα0), map_one]
  have hinv : ∀ n, tt f h (c n) (d n) * tt f h (d n) (c n) = 1 := fun n => by
    rw [tt_mul f h _ _ _ _ hf hff hh hhh hfh, hcd, mul_comm (d n), hcd, tt_one]
  have hσ : ∀ n, B.σ (tt f h (c n) (d n)) = tt f h (d n) (c n) := fun n => by
    rw [tt_swap f h (d n)]
    unfold tt
    have hcα : K.c α = α := ha.2.2
    simp only [map_add, map_one, map_sum, map_mul, map_sub, c, d, f, h, B.σ_σ, B.σ_alg, map_inv₀, map_pow, hcα]
  let u : ({i // i ∉ S} → Fin (k + 1)) → B.Aˣ := fun n =>
    ⟨tt f h (c n) (d n), tt f h (d n) (c n), hinv n, by rw [mul_comm]; exact hinv n⟩
  let t : ({i // i ∉ S} → Fin (k + 1)) → B.T := fun n => ⟨u n, by
    show tt f h (c n) (d n) * B.σ (tt f h (c n) (d n)) = 1
    rw [hσ, hinv]⟩
  have hαA : algebraMap K.O B.A a = algebraMap K.E B.A α := IsScalarTower.algebraMap_apply _ _ _ _
  have hia : IsIntegral K.O (algebraMap K.E B.A α) := hαA ▸ isIntegral_algebraMap
  have key : ∀ n m, ((t n)⁻¹ * t m) ∈ (intUnits K.O B.A).subgroupOf B.T → ∀ i, (n i : ℕ) ≤ m i := by
    intro n m hnm i
    have h1 : IsIntegral K.O (tt f h (d n) (c n) * tt f h (c m) (d m)) := hnm.1
    rw [tt_mul f h _ _ _ _ hf hff hh hhh hfh] at h1
    have h2 := (isIntegral_idem (O := K.O) (hf i)).mul h1
    rw [f_mul_tt f h _ _ hf hff hfh] at h2
    apply le_of_isIntegral ha
    apply isIntegral_of_mul_idem B (hf i) (hF0 i)
    rw [map_mul]
    exact h2
  refine ⟨fun n => QuotientGroup.mk (t n), ?_, ?_⟩
  · intro n m hnm
    funext i
    exact Fin.ext (le_antisymm (key n m (QuotientGroup.eq.1 hnm) i) (key m n (QuotientGroup.eq.1 hnm.symm) i))
  · intro n
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) (t n)
    show IsIntegral K.O (((((QuotientGroup.mk (t n) : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T).out : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)
    rw [hw, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, mul_assoc]
    refine IsIntegral.mul w.2.2 ?_
    show IsIntegral K.O (tt f h (d n) (c n) * _)
    rw [hαA]
    unfold tt
    rw [add_mul, Finset.sum_mul]
    refine IsIntegral.add (by rw [one_mul]; exact hia.pow k) (IsIntegral.sum _ fun i _ => ?_)
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (n i).2)
    have h1 : d n i * algebraMap K.E B.A α ^ k = algebraMap K.E B.A α ^ r := by
      have := congrFun (hcd n) i
      simp only [Pi.mul_apply, Pi.one_apply, c, map_pow] at this
      generalize (n i : ℕ) = j at hr this
      rw [hr, pow_add]
      linear_combination algebraMap K.E B.A α ^ r * this
    have h2 : ((d n i - 1) * f i + (c n i - 1) * h i) * algebraMap K.E B.A α ^ k =
        (algebraMap K.E B.A α ^ r - algebraMap K.E B.A α ^ k) * f i +
          (algebraMap K.E B.A α ^ (n i : ℕ) - 1) * h i * algebraMap K.E B.A α ^ k := by
      rw [← h1]; simp only [c, map_pow]; ring
    rw [h2]
    exact (((hia.pow r).sub (hia.pow k)).mul (isIntegral_idem (hf i))).add
      ((((hia.pow _).sub isIntegral_one).mul (isIntegral_idem (hh i))).mul (hia.pow k))

end GlobalTheory.UnitLemma.TorusPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixGamma
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

noncomputable section

namespace GlobalTheory.WachTie

theorem exists_matrix_gamma : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∃ Gm : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧, (∀ i, ∃ B : Matrix (Fin r) (Fin r) O⟦X⟧, Gm i = 1 + (X : O⟦X⟧) • B) ∧ (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (Gm i m k) : LetA O n) • (b m : W.DD T)) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF _ hb
  classical
  obtain ⟨-, hinv, -, -, -, hs, hX, -⟩ := hF
  have hsm : ∀ (g : W.Gam) (a : LetA O n) (x : W.DD T),
      W.γD T g (a • x) = letγ (W.γ₀ g) a • W.γD T g x := fun g a x => by
    have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
    rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
    exact this
  have hXj : (X : O⟦X⟧) ∣ j X := by
    have h1 : (1 : W.Gam) ∈ W.DelF := (W.DelF_def 1).2 ⟨1, one_pos, one_pow _⟩
    have h2 : R.s ≠ 0 := by rw [hs]; exact (Finset.card_pos.2 ⟨1, h1⟩).ne'
    exact (dvd_pow_self _ h2).trans hX.symm.dvd
  let z : Fin r → ↥(W.N T) := fun k => ⟨W.γD T W.gam (b k : W.DD T), W.N_Γ T _ _ (b k).2⟩
  have hexp : ∀ y : ↥(W.N T), (y : W.DD T) = ∑ m, b.repr y m • (b m : W.DD T) := fun y => by
    conv_lhs => rw [← b.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hc : ∀ k m i, ∃ c, j c = b.repr (z k) m i := by
    intro k m i
    refine (hinv _).2 fun δ hδ => ?_
    have h1 : W.γD T δ (z k : W.DD T) = z k := by
      change W.γD T δ (W.γD T W.gam (b k : W.DD T)) = W.γD T W.gam (b k : W.DD T)
      rw [← W.γD_mul, mul_comm, W.γD_mul, (hb k).2 δ hδ]
    have h2 : z k = ∑ m, letγ (W.γ₀ δ) (b.repr (z k) m) • b m := by
      apply Subtype.ext
      rw [← h1]
      conv_lhs => rw [hexp (z k)]
      simp only [map_sum, hsm, Submodule.coe_sum, Submodule.coe_smul]
      exact Finset.sum_congr rfl fun m _ => by rw [(hb m).2 δ hδ]
    have h3 : b.repr (z k) m = letγ (W.γ₀ δ) (b.repr (z k) m) := by
      conv_lhs => rw [h2]
      rw [b.repr_sum_self]
    exact (congrFun h3 i).symm
  choose c hc using hc
  refine ⟨fun i => Matrix.of fun m k => c k m i, fun i => ?_, fun k => ?_⟩
  · have hd : ∀ m k, (X : O⟦X⟧) ∣ c k m i - (1 : Matrix (Fin r) (Fin r) O⟦X⟧) m k := by
      intro m k
      obtain ⟨y, hy, hy'⟩ := W.N_π T W.gam _ (b k).2
      have h1 : z k - b k = (letπ : LetA O n) • (⟨y, hy⟩ : ↥(W.N T)) := Subtype.ext hy'
      have h2 := congrArg (fun w => b.repr w m i) h1
      simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, Pi.sub_apply,
        smul_eq_mul, Pi.mul_apply, b.repr_self, letπ] at h2
      rw [X_dvd_iff, ← constantCoeff_algHom j hXj, ← X_dvd_iff, map_sub, hc]
      have h3 : j ((1 : Matrix (Fin r) (Fin r) O⟦X⟧) m k) =
          (Finsupp.single k (1 : LetA O n) : Fin r →₀ LetA O n) m i := by
        by_cases h : m = k
        · subst h; simp
        · rw [Matrix.one_apply_ne h, Finsupp.single_eq_of_ne h]; simp
      rw [h3, h2]
      exact dvd_mul_right _ _
    choose d hd using hd
    refine ⟨Matrix.of d, ?_⟩
    ext1 m k
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← hd]; ring
  · simp only [Matrix.of_apply, hc]
    exact hexp (z k)

end GlobalTheory.WachTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlusElementEtaNormNegOne
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem exists_plus_eta_norm_neg_one : ∀ (K : UQ) (B : InvAlg K) (f : B.A), IsIdempotentElem f → f ≠ 0 →
    (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) → B.σ f = f →
    ∃ y : B.A, B.Plus y ∧ y * (1 - f) = 1 - f ∧ K.eta (Algebra.norm K.E y) = -1 := by
  first
  | exact @_root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm
  | exact _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm
  | (apply _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm ..)

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveElementStabilizerFinsetStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_element_stabilizer_finset : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by
  first | exact @GlobalTheory.stab_finset_eq_stab_primitive | exact GlobalTheory.stab_finset_eq_stab_primitive | (intros; apply GlobalTheory.stab_finset_eq_stab_primitive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegreeStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (k : ℕ), 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ := by
  first | exact @GlobalTheory.exists_fixed_dvd_deg | exact GlobalTheory.exists_fixed_dvd_deg | (intros; apply GlobalTheory.exists_fixed_dvd_deg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualMeasuresAndAbsKScaleStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_measures_and_absK_scale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → Nonempty (A.Meas ψ) ∧ ∀ (m : A.Meas ψ) (x : A.Kˣ), m.μL x = ENNReal.ofReal (A.absK x) • m.μL 1 := by
  first | exact @GlobalTheory.JR.exists_meas_and_scale | exact GlobalTheory.JR.exists_meas_and_scale | (intros; apply GlobalTheory.JR.exists_meas_and_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveValuationIsIntegralIffNonnegStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧ ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
  first | exact @GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff | exact GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff | (intros; apply GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformizerCompatibleUnramifiedExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ π : K.O, ∃ π' : K'.O, algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) ∧ IsLocalRing.maximalIdeal K.O = Ideal.span {π} ∧ IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_unif | exact GlobalTheory.UnitLemma.Unr.exists_unif | (intros; apply GlobalTheory.UnitLemma.Unr.exists_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatWachLetterRingCompletionOfDenseSaturatedStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_wachLetterRing_completion_of_dense_saturated : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (p : ℕ) (E : Type) [CommRing E] [Algebra (LetA O n) E], IsUnit (algebraMap (LetA O n) E letπ) → IsAdicComplete (Ideal.span {(p : E)}) E → (∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k}) → (∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} → ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) → Module.Flat (LetA O n) E := by
  first | exact @GlobalTheory.flat_letA_of_dense_sat | exact GlobalTheory.flat_letA_of_dense_sat | (intros; apply GlobalTheory.flat_letA_of_dense_sat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GalExtCContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertiaEigenvalues

variable {l : ℕ} [Fact l.Prime]

theorem norm_galAlgCl (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv g x).symm

theorem isometry_galAlgCl (g : GQ l) : Isometry (g : Om l → Om l) :=
  AddMonoidHomClass.isometry_of_norm g (norm_galAlgCl g)

noncomputable def galExtC (g : GQ l) : PadicComplex l ≃+* PadicComplex l :=
  UniformSpace.Completion.mapRingEquiv g.toRingEquiv (isometry_galAlgCl g).continuous
    (isometry_galAlgCl g.symm).continuous

theorem galExtC_coe (g : GQ l) (x : Om l) :
    galExtC g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l) :=
  UniformSpace.Completion.map_coe (isometry_galAlgCl g).uniformContinuous x

theorem galExtC_continuous (g : GQ l) : Continuous (galExtC g) :=
  UniformSpace.Completion.continuous_map

theorem norm_galExtC (g : GQ l) (y : PadicComplex l) : ‖galExtC g y‖ = ‖y‖ := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (galExtC_continuous g).norm continuous_norm
  | ih x => rw [galExtC_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_galAlgCl]

theorem galExtC_mul (g h : GQ l) : galExtC (g * h) = galExtC g * galExtC h := by
  ext y
  change galExtC (g * h) y = galExtC g (galExtC h y)
  induction y using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (galExtC_continuous _) ((galExtC_continuous g).comp (galExtC_continuous h))
  | ih x => rw [galExtC_coe, galExtC_coe, galExtC_coe, AlgEquiv.mul_apply]

noncomputable def galActC (l : ℕ) [Fact l.Prime] : GQ l →* (PadicComplex l ≃+* PadicComplex l) :=
  MonoidHom.mk' galExtC galExtC_mul

theorem isActC_galActC (l : ℕ) [Fact l.Prime] : IsActC (galActC l) :=
  ⟨galExtC_coe, norm_galExtC⟩

theorem exists_isActC :
    ∀ (l : ℕ) [Fact l.Prime], ∃ act : GQ l →* (PadicComplex l ≃+* PadicComplex l), IsActC act :=
  fun l _ => ⟨galActC l, isActC_galActC l⟩

end GlobalTheory.InertiaEigenvalues
end

