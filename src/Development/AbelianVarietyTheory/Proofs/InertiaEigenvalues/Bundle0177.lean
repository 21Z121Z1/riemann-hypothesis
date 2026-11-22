import Mathlib
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0165
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0166
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0036
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeInfSubspaceBaseChangeDvr
section
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory.LatticeInterBaseChange

end GlobalTheory.LatticeInterBaseChange

namespace GlobalTheory.LatticeInterBaseChange

end GlobalTheory.LatticeInterBaseChange

namespace GlobalTheory.LatticeInterBaseChange

open NumberField IsDedekindDomain Module in
private theorem exists_functional_comp_eq {K F : Type} [Field K] [Field F] (e : K →+* F)
    {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module F V']
    (iV : V →ₛₗ[e] V') {ι : Type} (b : Basis ι K V)
    (hli : LinearIndependent F (fun a => iV (b a))) (φ : V →ₗ[K] K) :
    ∃ ψ : V' →ₗ[F] F, ∀ v, ψ (iV v) = e (φ v) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Basis.span hli).constr F (fun a => e (φ (b a))))
  let f₁ : V →ₛₗ[e] F := g.comp iV
  let f₂ : V →ₛₗ[e] F :=
    { toFun := fun v => e (φ v)
      map_add' := fun v w => by simp
      map_smul' := fun t v => by simp }
  have hf : f₁ = f₂ := by
    refine b.ext fun a => ?_
    have h := LinearMap.congr_fun hg (Basis.span hli a)
    rw [Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Basis.span_apply] at h
    exact h
  exact ⟨g, fun v => LinearMap.congr_fun hf v⟩

open NumberField IsDedekindDomain Module in
private theorem exists_integral_inverse_coefficients {K : Type} [Field K] [NumberField K] {n : ℕ}
    (c : Fin n → K) :
    ∃ β : Fin n → K, (∀ j k, ∃ r : 𝓞 K, (r : K) = β j * c k) ∧
      ∀ k, c k * ∑ j, β j * c j = c k := by
  classical
  by_cases hc : ∀ k, c k = 0
  · exact ⟨0, fun j k => ⟨0, by simp⟩, fun k => by simp [hc k]⟩
  push_neg at hc
  obtain ⟨k₀, hk₀⟩ := hc
  let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanFinset (𝓞 K) Finset.univ c
  have hIc : (I : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) (Set.range c) := by
    change Submodule.span (𝓞 K) (c '' ((Finset.univ : Finset (Fin n)) : Set (Fin n))) = _
    rw [Finset.coe_univ, Set.image_univ]
  have hI : I ≠ 0 := by
    intro h
    exact hk₀ ((FractionalIdeal.spanFinset_eq_zero.1 h) k₀ (Finset.mem_univ _))
  have h1 : (1 : K) ∈ (I : Submodule (𝓞 K) K) *
      ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have key : ∃ β : Fin n → K,
      (∀ j, β j ∈ ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)) ∧
        (1 : K) = ∑ j, β j * c j := by
    refine Submodule.mul_induction_on (C := fun z => ∃ β : Fin n → K,
      (∀ j, β j ∈ ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)) ∧
        z = ∑ j, β j * c j) h1 ?_ ?_
    · intro m hm y hy
      rw [hIc, Submodule.mem_span_range_iff_exists_fun] at hm
      obtain ⟨r, rfl⟩ := hm
      refine ⟨fun j => r j • y, fun j => Submodule.smul_mem _ (r j) hy, ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Algebra.smul_def]
      ring
    · rintro x y ⟨β, hβ, rfl⟩ ⟨β', hβ', rfl⟩
      exact ⟨β + β', fun j => add_mem (hβ j) (hβ' j),
        by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]⟩
  obtain ⟨β, hβI, hβ1⟩ := key
  refine ⟨β, fun j k => ?_, fun k => by rw [← hβ1, mul_one]⟩
  have hck : c k ∈ I := by
    rw [← FractionalIdeal.mem_coe, hIc]
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
    ((FractionalIdeal.mem_inv_iff hI).1 (FractionalIdeal.mem_coe.1 (hβI j)) (c k) hck)
  exact ⟨r, hr⟩

open NumberField IsDedekindDomain Module in
private theorem mem_span_image_inf_ker {K F R : Type} [Field K] [NumberField K] [Field F]
    [CommRing R] [Algebra R F] (e : K →+* F) {V V' : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module F V'] [Module R V']
    [IsScalarTower R F V'] (iV : V →ₛₗ[e] V')
    (he : ∀ a : 𝓞 K, e (a : K) ∈ (algebraMap R F).range) (φ : V →ₗ[K] K) (ψ : V' →ₗ[F] F)
    (hψ : ∀ v, ψ (iV v) = e (φ v)) (A : Submodule (𝓞 K) V) {x : V'}
    (hx : x ∈ Submodule.span R (iV '' (A : Set V))) (h0 : ψ x = 0) :
    x ∈ Submodule.span R
      (iV '' ((A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V)) := by
  obtain ⟨n, r, g, hxg⟩ := Submodule.mem_span_set'.1 hx
  choose a ha hag using fun i => (g i).2
  obtain ⟨β, hβint, hβ⟩ := exists_integral_inverse_coefficients (fun i => φ (a i))
  choose ρ hρ using hβint
  beta_reduce at hρ hβ
  have hρs : ∀ j k, (ρ j k) • a j = (β j * φ (a k)) • a j := by
    intro j k
    rw [← hρ j k, ← algebraMap_smul K (ρ j k) (a j)]
  let w : Fin n → V := fun k => a k - ∑ j, (ρ j k) • a j
  have hwA : ∀ k, w k ∈ A := fun k =>
    sub_mem (ha k) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (ha j))
  have hwφ : ∀ k, φ (w k) = 0 := by
    intro k
    have h := hβ k
    rw [Finset.mul_sum] at h
    simp only [w, map_sub, map_sum, hρs, map_smul, smul_eq_mul]
    rw [sub_eq_zero]
    conv_lhs => rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∑ k, algebraMap R F (r k) * e (φ (a k)) = 0 := by
    rw [← h0, ← hxg, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hag k, ← algebraMap_smul F (r k) (iV (a k)), LinearMap.map_smul, smul_eq_mul, hψ]
  have hiw : ∀ k, iV (w k) = iV (a k) - ∑ j, (e (β j) * e (φ (a k))) • iV (a j) := by
    intro k
    simp only [w, map_sub, map_sum, hρs, LinearMap.map_smulₛₗ, map_mul]
  have hx' : x = ∑ k, r k • iV (w k) := by
    simp only [hiw, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
    have h2 : ∑ k, ∑ j, r k • (e (β j) * e (φ (a k))) • iV (a j) = 0 := by
      have h3 : ∀ k j, r k • (e (β j) * e (φ (a k))) • iV (a j) =
          (e (β j) * (algebraMap R F (r k) * e (φ (a k)))) • iV (a j) := by
        intro k j
        rw [← algebraMap_smul F (r k), smul_smul]
        congr 1
        ring
      simp only [h3]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_smul, ← Finset.mul_sum, key, mul_zero, zero_smul]
    rw [h2, sub_zero, ← hxg]
    exact Finset.sum_congr rfl fun k _ => by rw [hag k]
  rw [hx']
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨w k, Submodule.mem_inf.2 ⟨hwA k, LinearMap.mem_ker.2 (hwφ k)⟩, rfl⟩)

open NumberField IsDedekindDomain Module in

theorem _root_.GlobalTheory.LatticeInterBaseChange.span_inf_baseChange : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (A : Submodule (𝓞 K) V) (U : Submodule K V), Submodule.span O (iV '' ((A ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V)) = Submodule.span O (iV '' (A : Set V)) ⊓ (Submodule.span (FractionRing O) (iV '' (U : Set V))).restrictScalars O := by
  intro K _ _ O _ _ _ e V V' _ _ _ _ _ _ _ _ _ iV ι b hli he A U
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨v, (Submodule.mem_inf.1 hv).1, rfl⟩,
      Submodule.subset_span ⟨v, (Submodule.mem_inf.1 hv).2, rfl⟩⟩
  · intro x hx
    obtain ⟨hxA, hxU⟩ := Submodule.mem_inf.1 hx
    classical
    let bQ := Module.finBasis K (V ⧸ U)
    let f : Fin (Module.finrank K (V ⧸ U)) → V →ₗ[K] K := fun j => (bQ.coord j).comp U.mkQ
    have hU : ∀ v, v ∈ U ↔ ∀ j, f j v = 0 := by
      intro v
      simp only [f, LinearMap.comp_apply, Basis.coord_apply, Submodule.mkQ_apply]
      constructor
      · intro h j
        rw [(Submodule.Quotient.mk_eq_zero U).2 h, map_zero, Finsupp.zero_apply]
      · intro h
        exact (Submodule.Quotient.mk_eq_zero U).1
          ((LinearEquiv.map_eq_zero_iff bQ.repr).1 (Finsupp.ext h))
    choose ψ hψ using fun j => exists_functional_comp_eq e iV b hli (f j)
    have hψx : ∀ j, ψ j x = 0 := by
      intro j
      have hle : Submodule.span (FractionRing O) (iV '' (U : Set V)) ≤ LinearMap.ker (ψ j) := by
        rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, hψ, (hU v).1 hv j, map_zero]
      exact hle hxU
    have claim : ∀ s : Finset (Fin (Module.finrank K (V ⧸ U))), ∀ (A' : Submodule (𝓞 K) V) (y : V'),
        y ∈ Submodule.span O (iV '' (A' : Set V)) → (∀ j ∈ s, ψ j y = 0) →
        y ∈ Submodule.span O (iV '' ((A' ⊓ ⨅ j ∈ s, (LinearMap.ker (f j)).restrictScalars (𝓞 K) :
          Submodule (𝓞 K) V) : Set V)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro A' y hy _
        simpa using hy
      | insert j s hj ih =>
        intro A' y hy h0
        have h1 := mem_span_image_inf_ker e iV he (f j) (ψ j) (hψ j) A' hy
          (h0 j (Finset.mem_insert_self j s))
        have h2 := ih _ y h1 fun i hi => h0 i (Finset.mem_insert_of_mem hi)
        refine Submodule.span_mono (Set.image_mono ?_) h2
        intro v hv
        simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.mem_iInf,
          Submodule.restrictScalars_mem, LinearMap.mem_ker, Finset.mem_insert] at hv ⊢
        refine ⟨hv.1.1, fun i hi => ?_⟩
        rcases hi with rfl | hi
        · exact hv.1.2
        · exact hv.2 i hi
    have hfin := claim Finset.univ A x hxA fun j _ => hψx j
    refine Submodule.span_mono (Set.image_mono ?_) hfin
    intro v hv
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.mem_iInf,
      Submodule.restrictScalars_mem, LinearMap.mem_ker, Finset.mem_univ, forall_const] at hv ⊢
    exact ⟨hv.1, (hU v).2 hv.2⟩

end GlobalTheory.LatticeInterBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod
section
open PowerSeries GlobalTheory.BK Function Finset

namespace GlobalTheory.BK.OrbitBound

variable {e : ℕ} (u : ZMod e)

theorem iter_mul (n : ℕ) (x : ZMod e) : (fun y => u * y)^[n] x = u ^ n * x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply, ih, pow_succ, mul_assoc]

noncomputable def orb (x : ZMod e) : Finset (ZMod e) :=
  (range (minimalPeriod (fun y => u * y) x)).image fun k => u ^ k * x

variable {a : ℕ} (ha : 0 < a) (hu : u ^ a = 1)
include ha hu

theorem mp_pos (x : ZMod e) : 0 < minimalPeriod (fun y => u * y) x :=
  IsPeriodicPt.minimalPeriod_pos ha (by
    change (fun y => u * y)^[a] x = x
    rw [iter_mul, hu, one_mul])

theorem pow_mp_mul (x : ZMod e) : u ^ minimalPeriod (fun y => u * y) x * x = x := by
  rw [← iter_mul]; exact iterate_minimalPeriod

theorem pow_mp_mul_mul (x : ZMod e) (k : ℕ) :
    u ^ (minimalPeriod (fun y => u * y) x * k) * x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, mul_assoc, pow_mp_mul u ha hu x, ih]

theorem mp_sub_dvd (x y : ZMod e) : minimalPeriod (fun z => u * z) (x - y) ∣
    minimalPeriod (fun z => u * z) x * minimalPeriod (fun z => u * z) y := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (fun z => u * z)^[_] (x - y) = x - y
  rw [iter_mul, mul_sub, pow_mp_mul_mul u ha hu x, mul_comm (minimalPeriod _ x),
    pow_mp_mul_mul u ha hu y]

theorem mp_sub_pow_dvd (x : ZMod e) (k : ℕ) : minimalPeriod (fun z => u * z) (x - u ^ k * x) ∣
    minimalPeriod (fun z => u * z) x := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (fun z => u * z)^[_] (x - u ^ k * x) = x - u ^ k * x
  rw [iter_mul, mul_sub, mul_left_comm, pow_mp_mul u ha hu x]

theorem isUnit_u : IsUnit u :=
  have h : u * u ^ (a - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel ha, hu]
  ⟨⟨u, u ^ (a - 1), h, by rw [mul_comm]; exact h⟩, rfl⟩

theorem card_orb (x : ZMod e) : (orb u x).card = minimalPeriod (fun y => u * y) x := by
  rw [orb, card_image_of_injOn, card_range]
  rw [coe_range]
  intro i hi j hj h
  refine iterate_injOn_Iio_minimalPeriod hi hj ?_
  simp only [iter_mul]
  exact h

theorem mem_orb (x : ZMod e) (n : ℕ) : u ^ n * x ∈ orb u x := by
  refine mem_image.2 ⟨n % minimalPeriod (fun y => u * y) x, mem_range.2 (Nat.mod_lt _ (mp_pos u ha hu x)), ?_⟩
  show u ^ (n % _) * x = u ^ n * x
  rw [← iter_mul, ← iter_mul]
  exact iterate_mod_minimalPeriod_eq

omit ha hu in
theorem orb_subset {Sig : Finset (ZMod e)} (hcl : ∀ c ∈ Sig, u * c ∈ Sig) {x : ZMod e}
    (hx : x ∈ Sig) : orb u x ⊆ Sig := by
  have key : ∀ k : ℕ, u ^ k * x ∈ Sig := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ', mul_assoc]; exact hcl _ ih
  intro z hz
  obtain ⟨k, -, rfl⟩ := mem_image.1 hz
  exact key k

theorem four_mp_le (Sig : Finset (ZMod e)) (N : ℕ) (hcl : ∀ c ∈ Sig, u * c ∈ Sig) (h0 : (0 : ZMod e) ∈ Sig)
    (hN : Sig.card ≤ N) (h2 : 2 ≤ N) {x y : ZMod e} (hx : x ∈ Sig) (hy : y ∈ Sig) :
    4 * minimalPeriod (fun z => u * z) (x - y) ≤ N ^ 2 := by
  classical
  by_cases hyo : y ∈ orb u x
  · obtain ⟨k, -, rfl⟩ := mem_image.1 hyo
    have hle := Nat.le_of_dvd (mp_pos u ha hu x) (mp_sub_pow_dvd u ha hu x k)
    by_cases hx0 : x = 0
    · have h1 : minimalPeriod (fun y => u * y) x = 1 :=
        minimalPeriod_eq_one_iff_isFixedPt.2 (by simp [IsFixedPt, hx0])
      nlinarith
    · have hn0 : (0 : ZMod e) ∉ orb u x := by
        intro h
        obtain ⟨j, -, hj⟩ := mem_image.1 h
        exact hx0 (((isUnit_u u ha hu).pow j).mul_right_eq_zero.1 hj)
      have hsub : insert 0 (orb u x) ⊆ Sig := insert_subset h0 (orb_subset u hcl hx)
      have hc := card_le_card hsub
      rw [card_insert_of_notMem hn0, card_orb u ha hu] at hc
      nlinarith
  · have hdisj : Disjoint (orb u x) (orb u y) := by
      rw [disjoint_left]
      intro z hz1 hz2
      obtain ⟨i, -, rfl⟩ := mem_image.1 hz1
      obtain ⟨j, hj, hji⟩ := mem_image.1 hz2
      apply hyo
      have hy' : y = u ^ (minimalPeriod (fun z => u * z) y - j + i) * x := by
        rw [pow_add, mul_assoc, ← hji, ← mul_assoc, ← pow_add,
          Nat.sub_add_cancel (le_of_lt (mem_range.1 hj)), pow_mp_mul u ha hu y]
      rw [hy']
      exact mem_orb u ha hu x _
    have hsub : orb u x ∪ orb u y ⊆ Sig := union_subset (orb_subset u hcl hx) (orb_subset u hcl hy)
    have hc := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_orb u ha hu, card_orb u ha hu] at hc
    have hle := Nat.le_of_dvd (Nat.mul_pos (mp_pos u ha hu x) (mp_pos u ha hu y)) (mp_sub_dvd u ha hu x y)
    set m1 := minimalPeriod (fun z => u * z) x
    set m2 := minimalPeriod (fun z => u * z) y
    have h4 : 4 * (m1 * m2) ≤ (m1 + m2) ^ 2 := by
      zify; nlinarith [sq_nonneg ((m1 : ℤ) - m2)]
    have h5 : (m1 + m2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (hc.trans hN) 2
    omega

end GlobalTheory.BK.OrbitBound

namespace GlobalTheory.BK

open OrbitBound in

theorem maxPeriod_bounds : ∀ (l e a : ℕ), l.Prime → 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (N : ℕ),
    (∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig) → (0 : ZMod e) ∈ Sig → Sig.card ≤ N → 2 ≤ N →
    1 ≤ maxPeriod l Sig ∧ 4 * maxPeriod l Sig ≤ N ^ 2 ∧ ∀ c ∈ Sig, frobPeriod l c ≤ maxPeriod l Sig := by
  intro l e a _ ha hea Sig N hcl h0 hN h2
  have hu : (l : ZMod e) ^ a = 1 := by
    rw [← Nat.cast_pow, ← hea]
    push_cast
    rw [ZMod.natCast_self, zero_add]
  have h00 : ((0 : ZMod e), (0 : ZMod e)) ∈ Sig ×ˢ Sig := mem_product.2 ⟨h0, h0⟩
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (Nat.succ_le_of_lt (mp_pos (l : ZMod e) ha hu ((0 : ZMod e) - 0)))
      (Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2)) h00)
  · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup (Sig ×ˢ Sig) ⟨_, h00⟩
      (fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
    unfold maxPeriod
    rw [hpe]
    exact four_mp_le (l : ZMod e) ha hu Sig N hcl h0 hN h2 (mem_product.1 hp).1 (mem_product.1 hp).2
  · intro c hc
    have := Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
      (mem_product.2 ⟨hc, h0⟩ : (c, (0 : ZMod e)) ∈ Sig ×ˢ Sig)
    simp only [sub_zero] at this
    exact this

end GlobalTheory.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacterStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_virtual_character : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (f : WD h → ℂˣ), (∀ x y, f (x.lpSum y) = f x * f y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y) → ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (a : ∀ i, WDRep h (Fin (d i) → ℂ)) (c : ι → ℤ), (∀ σ, ∑ i, (c i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ) = 0) → ∏ i, f (WD.mk (a i)) ^ c i = 1 := by
  first | exact @GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero | exact GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero | (intros; apply GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardFibreStableLatticePairProjectionStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_fibre_stableLatticePairProjection : ∀ (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ y : LatPair O E g₁ g₂, ((latProj O E g₁ g₂ ⁻¹' {y}).ncard : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  first | exact @GlobalTheory.UnitLemma.ncard_fibre_latProj | exact GlobalTheory.UnitLemma.ncard_fibre_latProj | (intros; apply GlobalTheory.UnitLemma.ncard_fibre_latProj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMemCyclotomicLayerPrimeRpowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_mem_cyclotomic_layer_prime_rpow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (j : ℕ), 1 ≤ j → ∀ x : Om l, x ∈ Ks K j → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ ((n : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  first | exact @GlobalTheory.Cyc.norm_of_mem_Ks | exact GlobalTheory.Cyc.norm_of_mem_Ks | (intros; apply GlobalTheory.Cyc.norm_of_mem_Ks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGlOrbitEqFourierEtaleKProdStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourier_glOrbit_eq_fourier_etaleKProd : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ f' : Gl r F → ℂ, IsTest f' → ∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c) := by
  first | exact @GlobalTheory.JR.LinDesc.fourG_act_pt_eq_fourK | exact GlobalTheory.JR.LinDesc.fourG_act_pt_eq_fourK | (intros; apply GlobalTheory.JR.LinDesc.fourG_act_pt_eq_fourK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulPhiMemMM
section
open GlobalTheory.BK PowerSeries

namespace GlobalTheory.BK

theorem PhiMod.pow_smul_phi_mem_MM (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (η : ℕ)
    (h : ∀ m ∈ P.L, E K l e ^ η • m ∈ P.M) :
    ∀ m ∈ P.MM, (l : K) ^ η • P.phi m ∈ P.MM := by
  intro m hm
  have h1 : E K l e ^ η • m ∈ P.Mext (S O K e) :=
    P.smul_mem_Mext_of_basis (fun i => h _ (P.phi_mem_L (P.bas_mem_M i))) (A_le_S l e) hm
  have h2 := P.phi_mem_ext (fun _ => frob_mem_S l) h1
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  have h3 := (P.ext (S O K e)).smul_mem (⟨c ^ η, pow_mem hc η⟩ : S O K e) h2
  rw [Subalgebra.smul_def, P.phi_smul, smul_smul, map_pow, ← mul_pow, hcE] at h3
  have h4 : ((l : K⟦X⟧) ^ η) • P.phi m = (l : K) ^ η • P.phi m := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rwa [h4] at h3

end GlobalTheory.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesEqCOfSubstFixedNotRootOfUnityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity : ∀ (L : Type) [Field L] (y : PowerSeries L), PowerSeries.constantCoeff y = 0 → (∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) → ∀ a : PowerSeries L, (PowerSeries.subst y a : PowerSeries L) = a → a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  first | exact @GlobalTheory.powerSeries_eq_C_of_subst_eq_self | exact GlobalTheory.powerSeries_eq_C_of_subst_eq_self | (intros; apply GlobalTheory.powerSeries_eq_C_of_subst_eq_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PseudoCharacterApplyIdempotentNatLe
section
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

section
variable {M A : Type*} [Monoid M] [CommRing A]

theorem alt_const_idem (T : M → A) (e : M) (he : e * e = e) :
    ∀ n : ℕ, alt T n (fun _ => e) = ∏ i ∈ Finset.range n, (T e - (i : A))
  | 0 => by simp [alt]
  | n + 1 => by
    have h1 : Fin.tail (fun _ : Fin (n + 1) => e) = fun _ : Fin n => e := rfl
    have h2 : ∀ i : Fin n, Function.update (fun _ : Fin n => e) i e = fun _ => e := by
      intro i; exact Function.update_eq_self i (fun _ : Fin n => e)
    rw [alt, h1]
    simp only [he, h2, alt_const_idem T e he n, Finset.prod_range_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

theorem alt_idem_last (T : M → A) (e y : M) (he : e * e = e) (hy : e * y = y) (h0 : T e = 0) :
    ∀ n : ℕ, alt T (n + 1) (fun i => if i.val = n then y else e)
      = (-1) ^ n * (n.factorial : A) * T y
  | 0 => by simp [alt]
  | n + 1 => by
    have h1 : Fin.tail (fun i : Fin (n + 1 + 1) => if i.val = n + 1 then y else e)
        = fun i : Fin (n + 1) => if i.val = n then y else e := by
      funext i; simp [Fin.tail]
    have h2 : ∀ i : Fin (n + 1), Function.update (fun i : Fin (n + 1) => if i.val = n then y else e) i
        (e * (if i.val = n then y else e)) = fun i => if i.val = n then y else e := by
      intro i
      have : e * (if i.val = n then y else e) = (if i.val = n then y else e) := by
        split_ifs <;> assumption
      rw [this]
      exact Function.update_eq_self i (fun i : Fin (n + 1) => if i.val = n then y else e)
    have h3 : (if ((0 : Fin (n + 1 + 1)) : ℕ) = n + 1 then y else e) = e := by simp
    rw [alt, h1, h3, h0]
    simp only [h2, alt_idem_last T e y he hy h0 n, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.factorial_succ]
    push_cast
    ring

end

theorem isPsChar_idempotent : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ e : R, IsIdempotentElem e → (∃ m : ℕ, m ≤ d ∧ T e = m) ∧ (T e = 0 → ∀ y : R, T (e * y) = 0) := by
  intro k R _ _ _ _ d T hT e he
  have he' : e * e = e := he
  refine ⟨?_, fun h0 y => ?_⟩
  · have h := hT.alt_eq_zero (fun _ => e)
    rw [alt_const_idem _ e he', Finset.prod_eq_zero_iff] at h
    obtain ⟨m, hm, h⟩ := h
    exact ⟨m, Nat.lt_succ_iff.mp (Finset.mem_range.mp hm), sub_eq_zero.mp h⟩
  · have h := hT.alt_eq_zero (fun i => if i.val = d then e * y else e)
    rw [alt_idem_last (fun x => T x) e (e * y) he' (by rw [← mul_assoc, he']) h0 d] at h
    have h1 : ((-1 : k) ^ d * (d.factorial : k)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr d.factorial_ne_zero)
    exact (mul_eq_zero.mp h).resolve_left h1

end GlobalTheory.PsChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomTiltMapTiltFrobeniusIntegerPowerStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [CharP F l] [PerfectRing F l]
    (ι : Fl l →+* F) (k : ℤ) (x : Fl l), ι (GlobalTheory.PSer.pw k x) = GlobalTheory.PMonE.pw l k (ι x) := by
  first | exact @GlobalTheory.PSer.map_pw_eq_pw | exact GlobalTheory.PSer.map_pw_eq_pw | (intros; apply GlobalTheory.PSer.map_pw_eq_pw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparatedRootsAdditivePolyStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separated_roots_additive_poly : ∀ (l : ℕ) [Fact l.Prime] (E M h : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), M + h ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a (M + h)‖ = 1 → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ∃ Z : Finset ℂ_[l], l ^ h ≤ Z.card ∧ (∀ W ∈ Z, ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = 0) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  first | exact @GlobalTheory.separated_roots_additive_poly | exact GlobalTheory.separated_roots_additive_poly | (intros; apply GlobalTheory.separated_roots_additive_poly <;> assumption)
end

