import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicIrreducibleInjectRegularCharacterOrbits
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.PrimeLabOrbit

variable {g : ℕ} [hg : Fact g.Prime]

theorem aeval_pow_frob {K : Type} [Field K] [Algebra (ZMod g) K] (n : ℕ) (Q : (ZMod g)[X]) (y : K) :
    aeval (y ^ g ^ n) Q = (aeval y Q) ^ g ^ n := by
  haveI : CharP K g := (Algebra.charP_iff (ZMod g) K g).1 (ZMod.charP g)
  haveI : ExpChar K g := ExpChar.prime hg.out
  rw [← iterateFrobenius_def g n y, ← iterateFrobenius_def g n (aeval y Q), aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

theorem frob_injective {K : Type} [Field K] [Algebra (ZMod g) K] (n : ℕ) :
    Function.Injective (fun y : K => y ^ g ^ n) := by
  haveI : CharP K g := (Algebra.charP_iff (ZMod g) K g).1 (ZMod.charP g)
  haveI : ExpChar K g := ExpChar.prime hg.out
  intro a b h
  apply (iterateFrobenius K g n).injective
  simpa only [iterateFrobenius_def] using h

theorem card_le_of_gen_fixed {L : Type} [Field L] [Algebra (ZMod g) L] [Fintype L] {k : ℕ} (hk : 0 < k) {x : L}
    (hgen : ∀ y : L, ∃ Q : (ZMod g)[X], aeval x Q = y) (hx : x ^ g ^ k = x) : Fintype.card L ≤ g ^ k := by
  have hq : 1 < g ^ k := Nat.one_lt_pow hk.ne' hg.out.one_lt
  set f : L[X] := X ^ (g ^ k) - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L hq
  have hfix : ∀ y : L, y ^ g ^ k = y := by
    intro y
    obtain ⟨Q, rfl⟩ := hgen y
    rw [← aeval_pow_frob, hx]
  have hsub : (Finset.univ : Finset L) ⊆ f.roots.toFinset := by
    intro y _
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, hf, eval_sub, eval_pow, eval_X, hfix y, sub_self]
  calc Fintype.card L = (Finset.univ : Finset L).card := Finset.card_univ.symm
    _ ≤ f.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := card_roots' f
    _ = g ^ k := FiniteField.X_pow_card_sub_X_natDegree_eq L hq

section adjoin

variable {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P)
include hP

theorem finrank_adjoin : haveI := Fact.mk hP.2.1; Module.finrank (ZMod g) (AdjoinRoot P) = d := by
  haveI := Fact.mk hP.2.1
  rw [(AdjoinRoot.powerBasis hP.1.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hP.2.2.2]

theorem adjoin_gen : ∀ y : AdjoinRoot P, ∃ Q : (ZMod g)[X], aeval (AdjoinRoot.root P) Q = y := by
  intro y
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective y
  exact ⟨Q, AdjoinRoot.aeval_eq Q⟩

theorem le_of_dvd {k : ℕ} (hk : 0 < k) (hdvd : P ∣ X ^ (g ^ k) - X) : d ≤ k := by
  haveI := Fact.mk hP.2.1
  haveI : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.1.ne_zero).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot P) = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, finrank_adjoin hP]
  have hx : (AdjoinRoot.root P) ^ g ^ k = AdjoinRoot.root P := by
    obtain ⟨R, hR⟩ := hdvd
    have h0 : aeval (AdjoinRoot.root P) (X ^ (g ^ k) - X : (ZMod g)[X]) = 0 := by
      rw [hR, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
    rw [map_sub, map_pow, aeval_X, sub_eq_zero] at h0
    exact h0
  have := card_le_of_gen_fixed (L := AdjoinRoot P) (x := AdjoinRoot.root P) hk (adjoin_gen hP) hx
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right hg.out.one_lt).1 this

end adjoin

variable {K : Type} [Field K] [Algebra (ZMod g) K]

theorem exists_unit_root {d : ℕ} (hd : 0 < d) (hK : Module.finrank (ZMod g) K = d) {P : (ZMod g)[X]}
    (hP : IsPrimeLab d P) : ∃ u : Kˣ, aeval (u : K) P = 0 := by
  haveI := Fact.mk hP.2.1
  haveI : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.1.ne_zero).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite _
  have hc : Fintype.card (AdjoinRoot P) = Fintype.card K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), Module.card_eq_pow_finrank (K := ZMod g) (V := K),
      finrank_adjoin hP, hK]
  let φ := FiniteField.algEquivOfCardEq g hc
  have hr : aeval (φ (AdjoinRoot.root P)) P = 0 := by
    rw [show φ (AdjoinRoot.root P) = φ.toAlgHom (AdjoinRoot.root P) from rfl, aeval_algHom_apply,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hne : φ (AdjoinRoot.root P) ≠ 0 := by
    intro h0
    rw [h0, aeval_def, eval₂_at_zero] at hr
    exact hP.2.2.1 ((algebraMap (ZMod g) K).injective (hr.trans (map_zero _).symm))
  exact ⟨Units.mk0 _ hne, hr⟩

theorem orbit_regular {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P) {u : K} (hu : aeval u P = 0) :
    ∀ i j, i < d → j < d → u ^ g ^ i = u ^ g ^ j → i = j := by
  have key : ∀ i j, i < j → j < d → u ^ g ^ i = u ^ g ^ j → False := by
    intro i j hij hj h
    have hk : 0 < j - i := Nat.sub_pos_of_lt hij
    have hfix : u ^ g ^ (j - i) = u := by
      apply frob_injective (g := g) (K := K) i
      simp only
      rw [h, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
    have hmin : P = minpoly (ZMod g) u := minpoly.eq_of_irreducible_of_monic hP.2.1 hu hP.1
    have hdvd : P ∣ X ^ (g ^ (j - i)) - X := by
      rw [hmin]
      apply minpoly.dvd
      rw [map_sub, map_pow, aeval_X, hfix, sub_self]
    have := le_of_dvd hP hk hdvd
    omega
  intro i j hi hj h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (key i j hij hj h).elim
  · exact hij
  · exact (key j i hij hi h.symm).elim

theorem primeLab_to_regularChar : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d → ∃ c : (ZMod g)[X] → (Kˣ →* ℂˣ), (∀ P, IsPrimeLab d P → IsRegularChar g d (c P)) ∧
      ∀ P P', IsPrimeLab d P → IsPrimeLab d P' → (∃ i < d, c P' = c P ^ g ^ i) → P = P' := by
  intro g _ d hd K _ _ hK
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  let e : Kˣ ≃* (Kˣ →* ℂˣ) := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Kˣ ℂ).some.symm
  let c : (ZMod g)[X] → (Kˣ →* ℂˣ) := fun P =>
    if h : ∃ u : Kˣ, aeval (u : K) P = 0 then e h.choose else 1
  have hc : ∀ P, IsPrimeLab d P → ∃ u : Kˣ, aeval (u : K) P = 0 ∧ c P = e u := by
    intro P hP
    have h := exists_unit_root hd hK hP
    exact ⟨h.choose, h.choose_spec, dif_pos h⟩
  refine ⟨c, fun P hP => ?_, fun P P' hP hP' ⟨i, hi, h⟩ => ?_⟩
  · obtain ⟨u, hu, hcu⟩ := hc P hP
    intro i j hi hj h
    rw [hcu, ← map_pow, ← map_pow] at h
    have h' := congrArg Units.val (e.injective h)
    simp only [Units.val_pow_eq_pow_val] at h'
    exact orbit_regular hP hu i j hi hj h'
  · obtain ⟨u, hu, hcu⟩ := hc P hP
    obtain ⟨u', hu', hcu'⟩ := hc P' hP'
    rw [hcu, hcu', ← map_pow] at h
    have h' := congrArg Units.val (e.injective h)
    simp only [Units.val_pow_eq_pow_val] at h'
    have hr : aeval (u' : K) P = 0 := by rw [h', aeval_pow_frob, hu, zero_pow (pow_ne_zero _ (Fact.out : g.Prime).ne_zero)]
    rw [minpoly.eq_of_irreducible_of_monic hP.2.1 hr hP.1, minpoly.eq_of_irreducible_of_monic hP'.2.1 hu' hP'.1]

end GlobalTheory.PrimeLabOrbit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardMonicNatDegreeCoeffZeroNeZero
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GrPolys

theorem monic_deg_equiv_card (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} = g ^ n ∧
      Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := by
  have e : {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} ≃ (Fin n → ZMod g) :=
    (monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · haveI : Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n} := Finite.of_equiv _ e.symm
    exact Set.toFinite _

theorem zero_part_eq (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n) :
    {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0} =
      (fun h => X * h) '' {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n - 1} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hm, hd, h0⟩
    obtain ⟨h, rfl⟩ := X_dvd_iff.mpr h0
    have hmh : h.Monic := Monic.of_mul_monic_left monic_X hm
    refine ⟨h, ⟨hmh, ?_⟩, rfl⟩
    rw [natDegree_X_mul hmh.ne_zero] at hd
    omega
  · rintro ⟨h, ⟨hm, hd⟩, rfl⟩
    refine ⟨monic_X.mul hm, ?_, ?_⟩
    · rw [natDegree_X_mul hm.ne_zero]; omega
    · simp [mul_coeff_zero]

end GlobalTheory.GrPolys

theorem GlobalTheory.GrPolys.card_monic_coeff_zero_ne_zero :
    ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → Set.ncard {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} = g ^ n - g ^ (n - 1) ∧ Set.Finite {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0} := by
  intro g _ n hn
  obtain ⟨hcS, hfS⟩ := GlobalTheory.GrPolys.monic_deg_equiv_card g n
  obtain ⟨hcT, hfT⟩ := GlobalTheory.GrPolys.monic_deg_equiv_card g (n - 1)
  set S := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n}
  set A := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0}
  set B := {f : (ZMod g)[X] | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 = 0}
  have hAS : A ⊆ S := fun f hf => ⟨hf.1, hf.2.1⟩
  have hBS : B ⊆ S := fun f hf => ⟨hf.1, hf.2.1⟩
  have hfA : A.Finite := hfS.subset hAS
  have hfB : B.Finite := hfS.subset hBS
  have hU : A ∪ B = S := by
    ext f
    simp only [A, B, S, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hD : Disjoint A B := by
    rw [Set.disjoint_left]
    intro f hA hB
    exact hA.2.2 hB.2.2
  have hB : B.ncard = g ^ (n - 1) := by
    rw [show B = _ from GlobalTheory.GrPolys.zero_part_eq g n hn, Set.ncard_image_of_injective _
      (fun a b h => mul_left_cancel₀ X_ne_zero h), hcT]
  have := Set.ncard_union_eq hD hfA hfB
  rw [hU, hcS, hB] at this
  exact ⟨by omega, hfA⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOfQBMemLat
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

theorem norm_le_of_qB_mem_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M n : ℕ) (hM : 1 ≤ M) (z : ℚ_[l]) (hz : qB P z ∈ Lat AI M n) :
    ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  let J : ThetaL P AI := GlobalTheory.ThetaTie.thetaL T
  obtain ⟨a, ha⟩ := hz
  have hq : ∀ c : ℚ_[l], ‖J.θ (qB P c)‖ = ‖c‖ := by
    intro c
    have e : qB P c = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) c) :=
      IsScalarTower.algebraMap_apply _ _ _ c
    rw [e, J.θ_Om]
    exact (PadicComplex.norm_extends _ _).trans (PadicAlgCl.norm_extends _ _)
  have h1 := FilB_anti (P := P) (a := 1) (b := (M : ℤ)) (by exact_mod_cast hM) ha
  have h0 := FilB_anti (P := P) (a := 0) (b := 1) (by norm_num) h1
  have hk := (J.θ_ker _ h0).2 h1
  have hadd := J.θ_add _ h0 _ (io_mem AI (((l : ℕ) : Ainf l) ^ n * a))
  rw [sub_add_cancel, hk, zero_add] at hadd
  have e2 : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    simp only [map_mul, map_pow, map_natCast]
  rw [e2, J.θ_mul _ (qB_mem _) _ (io_mem AI a)] at hadd
  rw [← hq z, hadd, norm_mul, hq, Padic.norm_p_pow]
  exact mul_le_of_le_one_right (by positivity) (J.θ_int a)

end GlobalTheory.ExpImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtRho1OfMemIdealPower
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem exists_map_eq_of_mem_sq_sup_pow {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (l N : ℕ) (π : A) (z u : B) (hπ : φ π = z) (hu : (l : B) = z * u) (a : A)
    (ha : a ∈ Ideal.span {(l : A) ^ 2} ⊔ (Ideal.span {(l : A), π}) ^ N) :
    ∃ x y : B, φ a = (l : B) ^ 2 * x + z ^ N * y := by
  have hsub : Ideal.span {(l : B), z} ≤ Ideal.span {z} := by
    rw [Ideal.span_le]
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · rw [SetLike.mem_coe, hu]
      exact Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self z)
    · exact Ideal.mem_span_singleton_self z
  have hmap : Ideal.map φ (Ideal.span {(l : A) ^ 2} ⊔ (Ideal.span {(l : A), π}) ^ N) ≤
      Ideal.span {(l : B) ^ 2, z ^ N} := by
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_pair]
    simp only [map_pow, map_natCast, hπ]
    refine sup_le (Ideal.span_mono (by simp)) ?_
    calc Ideal.span {(l : B), z} ^ N ≤ Ideal.span {z} ^ N := Ideal.pow_right_mono hsub N
      _ = Ideal.span {z ^ N} := Ideal.span_singleton_pow z N
      _ ≤ _ := Ideal.span_mono (by simp)
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp (hmap (Ideal.mem_map_of_mem φ ha))
  exact ⟨x, y, by rw [← hxy]; ring⟩

theorem norm_kap_lt_rho1_of_mem_sq_sup_pow :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (j n f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (ζ : OC l), 1 ≤ j → IsPrimitiveRoot (ζ : PadicComplex l) (l ^ j) → φ letπ = (ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ∀ a ∈ Ideal.span {((l : ℕ) : LetA ↥(OL LL) n) ^ 2} ⊔ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) n), letπ}) ^ (l ^ j), ∀ k, ‖kap o (φ a) k‖ < rho1 l := by
  intro l _ LL j n f o φ ζ hj hζ hφ a ha k
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hζn : ‖(ζ : PadicComplex l) - 1‖ =
      (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) :=
    norm_primitiveRoot_sub_one l j hj _ hζ
  have hlnorm : ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := norm_natCast_prime_padicComplex l
  have hz0 : (ζ : PadicComplex l) - 1 ≠ 0 := by
    rw [← norm_pos_iff, hζn]
    positivity
  have hle : ‖(l : PadicComplex l)‖ ≤ ‖(ζ : PadicComplex l) - 1‖ := by
    rw [hlnorm, hζn, ← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le hl.le
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ (j - 1) := one_le_pow₀ hl.le
    have h2 : (1 : ℝ) ≤ (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1) := by nlinarith
    rw [neg_div, neg_le_neg_iff, div_le_one (by linarith)]
    exact h2
  let u : OC l := ⟨(l : PadicComplex l) / ((ζ : PadicComplex l) - 1), by
    rw [mem_OC, norm_div]
    exact div_le_one_of_le₀ hle (norm_nonneg _)⟩
  have hu : ((l : ℕ) : OC l) = (ζ - 1) * u := by
    apply Subtype.ext
    push_cast
    change (l : PadicComplex l) =
      ((ζ : PadicComplex l) - 1) * ((l : PadicComplex l) / ((ζ : PadicComplex l) - 1))
    field_simp
  have huO : ((l : ℕ) : OCO LL) =
      ((ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * (u ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hu,
      ← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]
  obtain ⟨x, y, hxy⟩ := exists_map_eq_of_mem_sq_sup_pow φ l (l ^ j) letπ _ _ hφ huO a ha
  have e1 : ((l : ℕ) : OCO LL) ^ 2 = (((l : ℕ) : OC l) ^ 2) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_pow, map_natCast]
  have e2 : ((ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) ^ (l ^ j) =
      ((ζ - 1) ^ (l ^ j)) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
  rw [hxy, kap_add, e1, e2, kap_tmul_one_mul, kap_tmul_one_mul]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    push_cast
    rw [norm_pow, hlnorm]
    calc ((l : ℝ)⁻¹) ^ 2 * ‖kap o x k‖ ≤ ((l : ℝ)⁻¹) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (norm_kap_le o x k) (by positivity)
      _ = (l : ℝ) ^ (-(2 : ℝ)) := by
          rw [mul_one, inv_pow, Real.rpow_neg (by positivity)]
          norm_cast
      _ < rho1 l := by
          unfold rho1
          rw [Real.rpow_lt_rpow_left_iff hl]
          have h3 : -1 ≤ -(1 : ℝ) / ((l : ℝ) - 1) := by
            rw [neg_div, neg_le_neg_iff, div_le_one hq]
            linarith
          linarith
  · rw [norm_mul]
    push_cast
    rw [norm_pow, hζn]
    calc ((l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)))) ^ (l ^ j) * ‖kap o y k‖
        ≤ ((l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)))) ^ (l ^ j) * 1 :=
          mul_le_mul_of_nonneg_left (norm_kap_le o y k) (by positivity)
      _ = (l : ℝ) ^ (-(l : ℝ) / ((l : ℝ) - 1)) := by
          rw [mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1
          have hp : (0 : ℝ) < (l : ℝ) ^ (j - 1) := by positivity
          have hpow : ((l ^ j : ℕ) : ℝ) = (l : ℝ) * (l : ℝ) ^ (j - 1) := by
            rw [Nat.cast_pow, ← pow_succ']
            congr 1
            omega
          rw [hpow]
          field_simp
      _ < rho1 l := by
          unfold rho1
          rw [Real.rpow_lt_rpow_left_iff hl, div_lt_div_iff_of_pos_right hq]
          linarith

end GlobalTheory.Cyc.Decomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicative
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem actMat_props {Z O N C : Type} [CommRing Z] [CommRing O] [Algebra Z O] [AddCommGroup N]
    [Module O N] [Module Z N] (hs : ∀ (x : Z) (t : N), x • t = algebraMap Z O x • t)
    [CommRing C] (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N)
    (A : O → Matrix (Fin d) (Fin d) C) (hA : ∀ a i j, A a i j = φ (b.repr (a • b j) i)) :
    (∀ a a', A (a + a') = A a + A a') ∧ (∀ (x : Z) a, A (x • a) = φ x • A a) ∧ A 1 = 1 ∧
      ∀ a a', A (a * a') = A a * A a' := by
  have hc : ∀ (a : O) (x : Z) (t : N), a • (x • t) = x • (a • t) := by
    intro a x t
    rw [hs, hs, smul_smul, smul_smul, mul_comm]
  refine ⟨fun a a' => ?_, fun x a => ?_, ?_, fun a a' => ?_⟩
  · ext i j
    simp only [hA, Matrix.add_apply, add_smul, map_add, Finsupp.add_apply]
  · ext i j
    have hx : (x • a) • b j = x • (a • b j) := by
      rw [Algebra.smul_def, mul_smul, ← hs]
    simp only [hA, Matrix.smul_apply, hx, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  · ext i j
    rw [hA, one_smul, Module.Basis.repr_self]
    by_cases h : i = j
    · subst h
      simp
    · simp [Finsupp.single_apply, Matrix.one_apply, h, Ne.symm h]
  · ext i j
    rw [Matrix.mul_apply, hA, mul_smul]
    conv_lhs => rw [← b.sum_repr (a' • b j)]
    rw [Finset.smul_sum]
    simp only [hc, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_mul, hA]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable {l : ℕ} [Fact l.Prime]

theorem lamMul_lam_add {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (x y : OCO LL) :
    lam o A (x + y) = lam o A x + lam o A y := by
  simp only [lam, kap_add, add_smul, Finset.sum_add_distrib]

theorem lamMul_lam_zero {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) :
    lam o A 0 = 0 := by
  simp only [lam, kap_zero, zero_smul, Finset.sum_const_zero]

theorem lam_mul_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), IsMat K LL T M A → (∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a) ∧ A 1 = 1 ∧ (∀ a b, A (a * b) = A a * A b) ∧ ∀ x y : OCO LL, lam o A (x * y) = lam o A x * lam o A y := by
  intro l _ K LL T d f M A o h
  letI := zlMod LL T
  obtain ⟨b, -, hA⟩ := h
  let φ : ℤ_[l] →+* PadicComplex l := (algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom
  have hφ : ∀ x, φ x = zC x := fun _ => rfl
  obtain ⟨Pa, Ps, P1, Pm⟩ := actMat_props (Z := ℤ_[l]) (O := ↥(OL LL)) (N := ↥T.L.T)
    (fun _ _ => rfl) φ b A (fun a i j => hA a i j)
  have hsum : ∀ a, A a = ∑ k, zC (o.repr a k) • A (o k) := by
    intro a
    have e := map_sum (AddMonoidHom.mk' A Pa) (fun k => o.repr a k • o k) Finset.univ
    simp only [AddMonoidHom.mk'_apply, o.sum_repr] at e
    rw [e]
    simp only [Ps, hφ]
  have ht : ∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a := by
    intro c a
    rw [hsum a, Finset.smul_sum]
    simp only [lam, kap_tmul, mul_smul]
  refine ⟨ht, P1, Pm, fun x y => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp [lamMul_lam_zero]
  | tmul c a =>
    induction y using TensorProduct.induction_on with
    | zero => simp [lamMul_lam_zero]
    | tmul c' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, ht, ht, ht, Pm, smul_mul_smul_comm]
      rfl
    | add y₁ y₂ h₁ h₂ => rw [mul_add, lamMul_lam_add, lamMul_lam_add, h₁, h₂, mul_add]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, lamMul_lam_add, lamMul_lam_add, h₁, h₂, add_mul]

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmer
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.ResidualSelmer

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → NoChiOff i r Xs → ∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → ∃ η : Fin D.R.nV → KK D.nd i, ∃ γ : GE D.nd, ((yg D.nd r S γ x').map (toK D.nd i)).mulVec η ≠ 0 := by
  intro D i r ρ π Xs S _ hG _ hN x' hx hZ
  have hrank : ((Eel D.nd S x').map (toK D.nd i)).rank = 1 := hG.2.2.2.2.2.2.2.2.2.2.1.1 x'
  by_contra hcon
  push Not at hcon
  have h0 : ∀ η : Fin D.R.nV → KK D.nd i, ((Eel D.nd S x').map (toK D.nd i)).mulVec η = 0 := by
    intro η
    apply hN _ hx hZ
    intro g
    have h := hcon η g
    have hy : yg D.nd r S g x' = rTwO D.nd i r (S.p x') g * Eel D.nd S x' - Eel D.nd S x' := by
      unfold yg
      rw [← Matrix.smul_mul]
      rfl
    rw [hy, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.sub_mulVec, sub_eq_zero,
      ← Matrix.mulVec_mulVec] at h
    exact h
  have hz : ((Eel D.nd S x').map (toK D.nd i)).mulVecLin = 0 := LinearMap.ext h0
  unfold Matrix.rank at hrank
  rw [hz, LinearMap.range_zero, finrank_bot] at hrank
  exact zero_ne_one hrank

end GlobalTheory.Cut.ResidualSelmer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulAddStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.repr_smul_add : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (c : k) (z z' : G → Fin A.m → k) (b g b' g' : ZMod n → Vc k A.m), Repr F A z b g → Repr F A z' b' g' → Repr F A (c • z + z') (c • b + b') (c • g + g') := by
  first | exact @GlobalTheory.TopSteps.Repr.smul_add | exact GlobalTheory.TopSteps.Repr.smul_add | (intros; apply GlobalTheory.TopSteps.Repr.smul_add <;> assumption)
end

