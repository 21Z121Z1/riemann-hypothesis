import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductLeadingTerm
section
open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI.PhiLead
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem prodL_single (f : ι → V →+ V) (h : ι → ι → V →+ K) (j : ι) (vs : List V) :
    prodL f h vs {j} = ((-1 : ℤ) ^ vs.length) • (vs.map (fun v => ExteriorAlgebra.ι K (f j v))).prod := by
  induction vs with
  | nil => simp [prodL, oneC]
  | cons v vs ih =>
    have e : prodL f h (v :: vs) = Lop f h v (prodL f h vs) := rfl
    rw [e]
    simp only [Lop, Finset.singleton_nonempty, dite_true, Finset.min'_singleton, Finset.erase_singleton,
      Finset.not_nonempty_empty, dite_false, add_zero, Finset.card_singleton, ih, List.length_cons,
      List.map_cons, List.prod_cons, pow_succ]
    rw [mul_smul_comm, smul_smul]
    ring_nf

theorem alt_single (f : ι → V →+ V) (h : ι → ι → V →+ K) (a : ℕ) (v : Fin a → V) (j : ι) :
    alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
  have key : ∀ σ : Equiv.Perm (Fin a), prodL f h (List.ofFn (v ∘ σ)) {j} =
      ((-1 : ℤ) ^ a * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
    intro σ
    rw [prodL_single, List.length_ofFn, List.map_ofFn]
    have h1 : (List.ofFn ((fun v => ExteriorAlgebra.ι K (f j v)) ∘ v ∘ σ)).prod =
        ExteriorAlgebra.ιMulti K a ((fun k => f j (v k)) ∘ σ) := by
      rw [ExteriorAlgebra.ιMulti_apply]; rfl
    rw [h1, AlternatingMap.map_perm, mul_smul]
    simp [Units.smul_def]
  simp only [alt, Finset.sum_apply, Pi.smul_apply, key, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have hs : ∀ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ((-1 : ℤ) ^ a * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) = (-1 : ℤ) ^ a := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> simp [hσ]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

theorem gamma_iMulti (p : ℕ) (g : V →+ V) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V)
    (hγ : IsGamma p g γ) (a : ℕ) (v : Fin a → V) :
    γ (ExteriorAlgebra.ιMulti K a v) = ExteriorAlgebra.ιMulti K a (fun k => g (v k)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.mpr (funext fun k => hγ.2 (v k))

theorem leading_term : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (j : ι), alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k))) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (j : ι) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V), IsPhi p f h Φ → IsGamma p (f j) γ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, Φ x {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x := by
  intro K _ V _ _ ι _ p f h
  refine ⟨fun a v j => alt_single f h a v j, ?_⟩
  intro Φ j γ hΦ hγ a x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    have hg : γ (b • ExteriorAlgebra.ιMulti K a v) = b ^ p • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
      rw [Algebra.smul_def, map_mul, hγ.1, gamma_iMulti p (f j) γ hγ, ← Algebra.smul_def]
    rw [hΦ, Pi.smul_apply, alt_single, hg, smul_comm]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy, smul_add]
  | neg x _ hx => simp [hx, smul_neg]
end GlobalTheory.DI.PhiLead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeltaCupProduct
section
open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI

section CupDelta

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem sum_alt_filter_lt_le (F : Finset ι → E) (u : Finset ι) :
    ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (F (u.filter (· < j)) + F (u.filter (· ≤ j))) =
      F ∅ - (-1 : ℤ) ^ u.card • F u := by
  induction u using Finset.induction_on_max with
  | empty => simp
  | insert m u hm ih =>
    have hmu : m ∉ u := fun h => lt_irrefl m (hm m h)
    rw [Finset.sum_insert hmu]
    rw [Finset.sum_congr rfl (g := fun j => (-1 : ℤ) ^ (u.filter (· < j)).card •
        (F (u.filter (· < j)) + F (u.filter (· ≤ j)))) (fun j hj => by
      rw [Finset.filter_insert, if_neg (not_lt.2 (hm j hj).le), Finset.filter_insert,
        if_neg (not_le.2 (hm j hj))]), ih]
    have e1 : (insert m u).filter (· < m) = u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxm⟩
        · exact absurd hxm (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hm x hx⟩
    have e2 : (insert m u).filter (· ≤ m) = insert m u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · exact fun h => h.1
      · rintro (rfl | hx)
        · exact ⟨Or.inl rfl, le_rfl⟩
        · exact ⟨Or.inr hx, (hm x hx).le⟩
    rw [e1, e2, Finset.card_insert_of_notMem hmu, pow_succ, smul_add, mul_neg_one, neg_smul]
    abel

theorem delta_cup_eq : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (Φ : E →+ (Finset ι → E)) (c : Finset ι → E), (∀ x, Φ x ∅ = 0) → c ∅ = 0 → ∀ u,
    delta (cup Φ c) u = cup Φ (delta c) u + ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card •
      delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) := by
  intro ι _ E _ Φ c hΦ hc u

  have sL : ∀ {i j : ι}, i < j → cubeSign u i = cubeSign (u.filter (· ≤ j)) i := by
    intro i j hij
    have : (u.filter (· ≤ j)).filter (· < i) = u.filter (· < i) := by
      ext x; simp only [Finset.mem_filter]; grind
    unfold cubeSign; rw [this]
  have sR : ∀ {i j : ι}, j < i → cubeSign u i =
      (-1 : ℤ) ^ (u.filter (· < j)).card * cubeSign (u.filter (j ≤ ·)) i := by
    intro i j hji
    have hd : Disjoint (u.filter (· < j)) ((u.filter (j ≤ ·)).filter (· < i)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact absurd h1.2 (not_lt.2 h2.1.2)
    have : u.filter (· < i) = u.filter (· < j) ∪ (u.filter (j ≤ ·)).filter (· < i) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_union]; grind
    unfold cubeSign; rw [← pow_add, ← Finset.card_union_of_disjoint hd, this]

  have hL : delta (cup Φ c) u = ∑ j ∈ u, ∑ i ∈ u.erase j,
      cubeSign u i • Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) := by
    simp only [delta, cup, Finset.smul_sum]
    exact Finset.sum_comm' (fun i j => by simp only [Finset.mem_erase]; tauto)

  have key : ∀ j ∈ u, Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) +
      (-1 : ℤ) ^ (u.filter (· < j)).card • delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) =
      ∑ i ∈ u.erase j,
        cubeSign u i • Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) +
      (-1 : ℤ) ^ (u.filter (· < j)).card • (Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) +
        Φ (c (u.filter (· ≤ j))) (u.filter (j < ·))) := by
    intro j hj
    have eL : (u.erase j).filter (· < j) = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eG : (u.erase j).filter (fun x => ¬ x < j) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eLeL : (u.filter (· ≤ j)).filter (· < j) = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter]; grind
    have eLeJ : (u.filter (· ≤ j)).filter (fun x => ¬ x < j) = {j} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; grind
    have eGeG : (u.filter (j ≤ ·)).filter (j < ·) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter]; grind
    have eGeJ : (u.filter (j ≤ ·)).filter (fun x => ¬ j < x) = {j} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; grind
    have eLeE : (u.filter (· ≤ j)).erase j = u.filter (· < j) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind
    have eGeE : (u.filter (j ≤ ·)).erase j = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase]; grind

    rw [← Finset.sum_filter_add_sum_filter_not (u.erase j) (· < j), eL, eG]

    have h1 : Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) =
        ∑ i ∈ u.filter (· < j), cubeSign (u.filter (· ≤ j)) i •
          Φ (c ((u.filter (· ≤ j)).erase i)) (u.filter (j ≤ ·)) +
        (-1 : ℤ) ^ (u.filter (· < j)).card • Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) := by
      simp only [delta, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
      rw [← Finset.sum_filter_add_sum_filter_not (u.filter (· ≤ j)) (· < j), eLeL, eLeJ,
        Finset.sum_singleton, eLeE]
      congr 2
      unfold cubeSign; rw [eLeL]

    have h2 : delta (Φ (c (u.filter (· ≤ j)))) (u.filter (j ≤ ·)) =
        ∑ i ∈ u.filter (j < ·), cubeSign (u.filter (j ≤ ·)) i •
          Φ (c (u.filter (· ≤ j))) ((u.filter (j ≤ ·)).erase i) +
        Φ (c (u.filter (· ≤ j))) (u.filter (j < ·)) := by
      simp only [delta]
      rw [← Finset.sum_filter_add_sum_filter_not (u.filter (j ≤ ·)) (j < ·), eGeG, eGeJ,
        Finset.sum_singleton, eGeE, cubeSign_eq_one_of_forall_le (by simp), one_smul]
    rw [h1, h2, smul_add, Finset.smul_sum]
    have hA : ∑ i ∈ u.filter (· < j), cubeSign u i •
          Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) =
        ∑ i ∈ u.filter (· < j), cubeSign (u.filter (· ≤ j)) i •
          Φ (c ((u.filter (· ≤ j)).erase i)) (u.filter (j ≤ ·)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hij : i < j := (Finset.mem_filter.1 hi).2
      rw [sL hij, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (s := u.filter (j ≤ ·)) (by simp [hij])]
    have hB : ∑ i ∈ u.filter (j < ·), cubeSign u i •
          Φ (c ((u.erase i).filter (· ≤ j))) ((u.erase i).filter (j ≤ ·)) =
        ∑ i ∈ u.filter (j < ·), (-1 : ℤ) ^ (u.filter (· < j)).card •
          cubeSign (u.filter (j ≤ ·)) i • Φ (c (u.filter (· ≤ j))) ((u.filter (j ≤ ·)).erase i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hji : j < i := (Finset.mem_filter.1 hi).2
      rw [sR hji, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (s := u.filter (· ≤ j)) (by simp [hji]), mul_smul]
    rw [hA, hB]
    simp only [smul_add]
    abel

  have tele := sum_alt_filter_lt_le (fun s => Φ (c s) (u \ s)) u
  simp only [Finset.sdiff_self, hΦ, Finset.sdiff_empty, hc, map_zero, Pi.zero_apply, smul_zero,
    sub_zero] at tele
  have hT : ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (Φ (c (u.filter (· < j))) (u.filter (j ≤ ·)) +
      Φ (c (u.filter (· ≤ j))) (u.filter (j < ·))) = 0 := by
    rw [← tele]
    refine Finset.sum_congr rfl fun j _ => ?_
    have a1 : u \ u.filter (· < j) = u.filter (j ≤ ·) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; grind
    have a2 : u \ u.filter (· ≤ j) = u.filter (j < ·) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; grind
    rw [a1, a2]
  rw [hL]
  show _ = ∑ j ∈ u, Φ (delta c (u.filter (· ≤ j))) (u.filter (j ≤ ·)) + _
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl key, Finset.sum_add_distrib, hT, add_zero]

end CupDelta

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqQuotientCharpolyPow
section
open scoped TensorProduct nonZeroDivisors
open Polynomial

namespace GlobalTheory.NilpFiltration

theorem charpoly_eq_of_intertwine {K : Type} [Field K] {A B : Type} [AddCommGroup A] [Module K A]
    [FiniteDimensional K A] [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    (φ : A ≃ₗ[K] B) (f : Module.End K A) (g : Module.End K B) (h : ∀ a, φ (f a) = g (φ a)) :
    LinearMap.charpoly f = LinearMap.charpoly g := by
  rw [← LinearEquiv.charpoly_conj φ f]
  congr 1
  ext b
  rw [LinearEquiv.conj_apply_apply, h, LinearEquiv.apply_symm_apply]

theorem charpoly_eq_quotient_charpoly_pow_succ (K : Type) [Field K] : ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module K X]
    [FiniteDimensional K X] (t T : Module.End K X) (_ : Commute t T) (_ : t ^ (n + 1) = 0)
    (_ : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ n))
    (hT : LinearMap.range t ≤ (LinearMap.range t).comap T),
    LinearMap.charpoly T =
      (LinearMap.charpoly ((LinearMap.range t).mapQ (LinearMap.range t) T hT)) ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro X _ _ _ t T _ he _ hT
    have ht : t = 0 := by simpa using he
    subst ht
    rw [pow_one]
    have hinj : Function.Injective (LinearMap.range (0 : Module.End K X)).mkQ := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ, LinearMap.range_zero]
    refine charpoly_eq_of_intertwine
      (LinearEquiv.ofBijective _ ⟨hinj, Submodule.mkQ_surjective _⟩) T _ (fun x => ?_)
    rfl
  | succ n ih =>
    intro X _ _ _ t T hc he hk hT
    have htY : ∀ x ∈ LinearMap.range t, t x ∈ LinearMap.range t := fun x _ => LinearMap.mem_range_self t x
    have hTY : ∀ x ∈ LinearMap.range t, T x ∈ LinearMap.range t := fun x hx => hT hx
    set Y := LinearMap.range t with hYdef
    set t' := t.restrict htY with ht'
    set T' := T.restrict hTY with hT'def
    have hcomm : ∀ x, t (T x) = T (t x) := fun x => LinearMap.congr_fun hc.eq x
    have hc' : Commute t' T' := by
      show t' * T' = T' * t'
      ext x
      simp only [Module.End.mul_apply, t', T', LinearMap.restrict_coe_apply]
      exact hcomm x
    have hpow : ∀ k (x : Y), ((t' ^ k) x : X) = (t ^ k) x := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ihk =>
        intro x
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply,
          LinearMap.restrict_coe_apply, ihk]
    have he' : t' ^ (n + 1) = 0 := by
      ext x
      obtain ⟨y, hy⟩ := x.2
      rw [hpow, LinearMap.zero_apply, ZeroMemClass.coe_zero, ← hy, ← Module.End.mul_apply, ← pow_succ, he,
        LinearMap.zero_apply]
    have hk' : ∀ x : Y, t' x = 0 → x ∈ LinearMap.range (t' ^ n) := by
      intro x hx
      have hx' : t x = 0 := by
        have := congrArg Subtype.val hx
        simpa [t', LinearMap.restrict_coe_apply] using this
      obtain ⟨z, hz⟩ := hk x hx'
      refine ⟨⟨t z, LinearMap.mem_range_self t z⟩, Subtype.ext ?_⟩
      rw [hpow, ← Module.End.mul_apply, ← pow_succ, hz]
    have hT' : LinearMap.range t' ≤ (LinearMap.range t').comap T' := by
      rintro y ⟨x, rfl⟩
      show T' (t' x) ∈ LinearMap.range t'
      exact ⟨T' x, by rw [← Module.End.mul_apply, hc'.eq, Module.End.mul_apply]⟩
    have hmain : LinearMap.charpoly T = LinearMap.charpoly T' * LinearMap.charpoly (Y.mapQ Y T hT) :=
      GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ Y T hTY
    let f : X →ₗ[K] Y ⧸ LinearMap.range t' := (LinearMap.range t').mkQ ∘ₗ t.rangeRestrict
    have hf : ∀ x, f x = Submodule.Quotient.mk (⟨t x, LinearMap.mem_range_self t x⟩ : Y) := fun x => rfl
    have hsurj : Function.Surjective f :=
      (Submodule.mkQ_surjective _).comp t.surjective_rangeRestrict
    have hker : LinearMap.ker f = Y := by
      ext x
      rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero]
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨w, hw⟩ := y.2
        have h1 : t (x - t w) = 0 := by
          have := congrArg Subtype.val hy
          simp only [t', LinearMap.restrict_coe_apply] at this
          rw [map_sub, ← this, hw, sub_self]
        obtain ⟨z, hz⟩ := hk _ h1
        have h2 : x - t w ∈ Y := by
          rw [← hz, pow_succ', Module.End.mul_apply]
          exact LinearMap.mem_range_self t _
        have h3 := Y.add_mem h2 (LinearMap.mem_range_self t w)
        rwa [sub_add_cancel] at h3
      · rintro ⟨w, rfl⟩
        exact ⟨⟨t w, LinearMap.mem_range_self t w⟩, rfl⟩
    let φ : (X ⧸ Y) ≃ₗ[K] Y ⧸ LinearMap.range t' :=
      (Submodule.quotEquivOfEq Y (LinearMap.ker f) hker.symm).trans (f.quotKerEquivOfSurjective hsurj)
    have hφ : ∀ x, φ (Submodule.Quotient.mk x) = f x := fun x => rfl
    have hq : LinearMap.charpoly (Y.mapQ Y T hT) = LinearMap.charpoly ((LinearMap.range t').mapQ (LinearMap.range t') T' hT') := by
      refine charpoly_eq_of_intertwine φ _ _ (fun a => ?_)
      induction a using Submodule.Quotient.induction_on with
      | H x =>
        rw [Submodule.mapQ_apply, hφ, hφ, hf, hf, Submodule.mapQ_apply]
        congr 1
        exact Subtype.ext (hcomm x)
    rw [hmain, ih Y t' T' hc' he' hk' hT', ← hq, ← pow_succ]

theorem charpoly_eq_charpoly_mapQ_pow : ∀ (K : Type) [Field K] (X : Type) [AddCommGroup X] [Module K X]
    [FiniteDimensional K X]
    (t T : Module.End K X) (_ : Commute t T) (e : ℕ) (_ : 0 < e) (_ : t ^ e = 0)
    (_ : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ (e - 1)))
    (hT : LinearMap.range t ≤ (LinearMap.range t).comap T),
    LinearMap.charpoly T = (LinearMap.charpoly ((LinearMap.range t).mapQ (LinearMap.range t) T hT)) ^ e := by
  intro K _ X _ _ _ t T hc e he0 he hk hT
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0.ne'
  exact charpoly_eq_quotient_charpoly_pow_succ K n X t T hc he (by simpa using hk) hT

end GlobalTheory.NilpFiltration
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionRestrictClopenFactorizationStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedImmersion_restrict_clopen_factorization : ∀ {X Z₁ : Scheme.{0}} (i : Z₁ ⟶ X), IsClosedImmersion i → ∀ (U : X.Opens), IsClosed (U : Set X) → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), ((∃ z : T ⟶ Z, z ≫ j = g) ↔ (∃ y : T ⟶ Z₁, y ≫ i = g) ∧ Set.range g.base ⊆ (U : Set X)) := by
  first | (exact @GlobalTheory.clopen_cut_closedImmersion) | (exact GlobalTheory.clopen_cut_closedImmersion) | (intros; apply GlobalTheory.clopen_cut_closedImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSpanOfWeightedHomogeneousRelationQuasiReStatement
section
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular : ∀ {R : Type} [CommRing R] {n : ℕ} (z : Fin n → R) (w : Fin n → ℕ), (∀ i, 1 ≤ w i) →
    IsQuasiRegularSeq R z → ∀ (D : ℕ) (F : MvPolynomial (Fin n) R),
    F.IsWeightedHomogeneous w D → MvPolynomial.eval z F = 0 →
    ∀ α : Fin n →₀ ℕ, F.coeff α ∈ Ideal.span (Set.range z) := by
  first | exact @GlobalTheory.weightedRelation_coeff_mem_span | exact GlobalTheory.weightedRelation_coeff_mem_span | (intros; apply GlobalTheory.weightedRelation_coeff_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoequifiberedGeneratedSubalgebraQuasiCoherentStatement
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j)))), (∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) → (subNat F α V T).Coequifibered := by
  first | exact @GlobalTheory.QcSub.coequifibered_subNat | exact GlobalTheory.QcSub.coequifibered_subNat | (intros; apply GlobalTheory.QcSub.coequifibered_subNat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelTorsionOfFiniteLengthModElement
section
open IsLocalRing

namespace GlobalTheory

theorem exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot
    (R : Type) [CommRing R] [IsLocalRing R] (f : R)
    (hdim : 1 ≤ ringKrullDim (R ⧸ Ideal.span {f})) :
    ∃ P : Ideal R, P.IsPrime ∧ f ∈ P ∧ P ≠ maximalIdeal R := by
  by_contra! hne
  have h0 : Ring.KrullDimLE 0 (R ⧸ Ideal.span {f}) := by
    refine Ring.krullDimLE_zero_iff.mpr fun Q hQ => ?_
    have hc : Q.comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R := by
      refine hne _ (Ideal.comap_isPrime _ _) ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
      exact Q.zero_mem
    have hmax := (maximalIdeal.isMaximal R).map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
      (by rw [← hc]; exact Ideal.comap_mono bot_le)
    rwa [← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hmax
  have := (Ring.krullDimLE_iff (n := 0)).mp h0
  have h10 := hdim.trans this
  norm_num at h10

theorem cokernel_torsion_of_finiteLength_mod : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (f : R), 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) → ∀ (A B : Type) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Module.Finite R B] (ψ : A →ₐ[R] B), (∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c) → ∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range := by
  intro R _ _ _ f hdim A B _ _ _ _ _ ψ ⟨k, hk⟩
  obtain ⟨P, hP, hfP, hPm⟩ := exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot R f hdim

  obtain ⟨x, hxk, hxP⟩ : ∃ x ∈ maximalIdeal R ^ k, x ∉ P := by
    by_contra! h
    have hle : maximalIdeal R ≤ P := hP.le_of_pow_le h
    exact hPm (le_antisymm (le_maximalIdeal hP.ne_top) hle)
  set N : Submodule R B := LinearMap.range ψ.toLinearMap
  set I : Ideal R := Ideal.span {f}
  let φ : Module.End R (B ⧸ N) := algebraMap R (Module.End R (B ⧸ N)) x
  have hφ : LinearMap.range φ ≤ I • ⊤ := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective N c
    obtain ⟨a, c', hac⟩ := hk x hxk b
    have : φ (Submodule.Quotient.mk b) = f • Submodule.Quotient.mk c' := by
      simp only [φ, Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, hac]
      have ha0 : Submodule.Quotient.mk (p := N) (ψ a) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨a, rfl⟩
      rw [Submodule.Quotient.mk_add, ha0, zero_add]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) Submodule.mem_top
  obtain ⟨p, hmon, -, hcoeff, hzero⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R φ I hφ
  refine ⟨p.eval x, ?_, ?_⟩
  · intro h0
    apply hxP
    apply hP.mem_of_pow_mem p.natDegree
    have hs : p.eval x ∈ P := h0 ▸ P.zero_mem
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul] at hs
    refine (P.add_mem_iff_right ?_).mp hs
    refine P.sum_mem fun i hi => P.mul_mem_right _ ?_
    have hi' : 0 < p.natDegree - i := Nat.sub_pos_of_lt (Finset.mem_range.mp hi)
    have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hfP
    exact hIP (Ideal.pow_le_self hi'.ne' (hcoeff i))
  · intro b
    have h1 : (Polynomial.aeval φ p) (Submodule.Quotient.mk b) = 0 := by rw [hzero]; rfl
    rw [show φ = algebraMap R _ x from rfl, Polynomial.aeval_algebraMap_apply,
      Module.algebraMap_end_apply, Polynomial.aeval_def] at h1
    change Polynomial.eval x p • Submodule.Quotient.mk (p := N) b = 0 at h1
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, ha⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMultiplierEqConstSmulGeneratorStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_multiplier_eq_const_smul_generator_alt : ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ f ∈ V, rd f ∈ R) → (∀ f ∈ V', rd f ∈ R) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h h' : B, h ∈ R → h' ∈ R → h * h' = 1 → (∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A))) → ∀ T : V →ₗ[K] V', T ≠ 0 → (∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  first | exact @GlobalTheory.commuting_multiplier_eq_const_smul_generator | exact GlobalTheory.commuting_multiplier_eq_const_smul_generator | (intros; apply GlobalTheory.commuting_multiplier_eq_const_smul_generator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingSemisimpleEigenspacesSpan
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem iSup_jointEigenspace_eq_top_of_separable : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : Type) [AddCommGroup V] [Module C V] [FiniteDimensional C V] (I : Type) (T : I → Module.End C V), (∀ a b, Commute (T a) (T b)) → (∀ a, ∃ f : Polynomial C, f.Separable ∧ Polynomial.aeval (T a) f = 0) → (⨆ χ : I → C, ⨅ a : I, Module.End.eigenspace (T a) (χ a)) = ⊤ := by
  intro C _ _ V _ _ _ I T hc hs
  have hmax : ∀ a μ, (T a).maxGenEigenspace μ = (T a).eigenspace μ := by
    intro a μ
    obtain ⟨f, hf, h0⟩ := hs a
    exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hcomm : Pairwise fun i j => Commute (T i) (T j) := fun i j _ => hc i j
  have hdiag : ∀ a, ⨆ μ, (T a).maxGenEigenspace μ = ⊤ := fun a =>
    Module.End.iSup_maxGenEigenspace_eq_top (T a)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T hcomm hdiag
  simpa only [hmax] using htop

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugationDerivCutoffPolynomialMemUnitarySpanStatement
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugationDerivCutoffPolynomial_mem_unitarySpan : ∀ {n : ℕ} (ε : Fin n → Bool) (Z : GlobalTheory.PsCo.Pc1.Mat n) (H : ℝ → ℝ) (P : GlobalTheory.PsCo.Pc1.Poly n), GlobalTheory.PsCo.Pc1.IsCutFn H → GlobalTheory.PsCo.Pc1.adBas ε Z H P ∈ GlobalTheory.PsCo.Pc1.AdSpanM ε := by
  first | exact @GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM | exact GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM | (intros; apply GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterCocycleTrivialNearZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_character_cocycle_trivial_near_zero : ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  first | exact @GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero | exact GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero | (intros; apply GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoefficientStatement
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_matrix_coefficient : ∀ (n : ℕ) (g g' : Sch (Fin n)), Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by
  first | exact @GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun | exact GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun | (intros; apply GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun <;> assumption)
end

