import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentsOfConeIntegralEquation
section
open MvPolynomial

namespace GlobalTheory

theorem coeff_eval₂_C_mul_X {F K : Type} [Field F] [Field K] (φ : F →+* K) {r : ℕ} (w : Fin r → K)
    (p : MvPolynomial (Fin r) F) (d : ℕ) :
    (MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) p).coeff d
      = MvPolynomial.eval₂ φ w (homogeneousComponent d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have hprod : (u.prod fun i k => (Polynomial.C (w i) * Polynomial.X : Polynomial K) ^ k)
        = Polynomial.C (u.prod fun i k => w i ^ k) * Polynomial.X ^ (Finsupp.degree u) := by
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
        Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
    have hcomp : homogeneousComponent d (monomial u a)
        = if Finsupp.degree u = d then monomial u a else 0 := by
      ext v
      rw [coeff_homogeneousComponent]
      by_cases hd : Finsupp.degree u = d
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
    rw [eval₂_monomial, hprod, hcomp, ← mul_assoc, RingHom.comp_apply, ← map_mul,
      Polynomial.coeff_C_mul_X_pow]
    by_cases h : Finsupp.degree u = d
    · subst h
      simp [eval₂_monomial]
    · have h' : d ≠ Finsupp.degree u := fun e => h e.symm
      simp [h, h']
  | add p q hp hq =>
    simp only [eval₂_add, Polynomial.coeff_add, map_add, hp, hq]

theorem homogeneous_components_of_integral_equation (F K : Type) [Field F] [Field K] (φ : F →+* K)
    (r e m : ℕ) (w : Fin r → K) (τ : K) (b : Fin m → MvPolynomial (Fin r) F)
    (h : (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ)
      (fun i => Polynomial.C (w i) * Polynomial.X) (b k) *
        (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0) :
    ∃ a : Fin m → MvPolynomial (Fin r) F, (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧
      τ ^ m + ∑ k, MvPolynomial.eval₂ φ w (a k) * τ ^ (k : ℕ) = 0 := by
  refine ⟨fun k => homogeneousComponent (e * (m - k)) (b k),
    fun k => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hc := congrArg (fun P : Polynomial K => P.coeff (e * m)) h
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
  have hpow : ∀ n : ℕ, (Polynomial.C τ * Polynomial.X ^ e) ^ n
      = Polynomial.C (τ ^ n) * Polynomial.X ^ (e * n) := by
    intro n
    rw [mul_pow, ← pow_mul, map_pow]
  have hterm : ∀ k : Fin m, (MvPolynomial.eval₂ (Polynomial.C.comp φ)
      (fun i => Polynomial.C (w i) * Polynomial.X) (b k) *
        (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ)).coeff (e * m)
      = MvPolynomial.eval₂ φ w (homogeneousComponent (e * (m - k)) (b k)) * τ ^ (k : ℕ) := by
    intro k
    have hle : e * (k : ℕ) ≤ e * m := Nat.mul_le_mul_left e k.is_lt.le
    rw [hpow, ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos hle, Polynomial.coeff_mul_C,
      ← Nat.mul_sub, coeff_eval₂_C_mul_X]
  rw [hpow, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
  simpa only [hterm] using hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfaceDiffIsPreirreducibleOfNoSplitting
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_prime_factor_mem_prime_ideal_ufd {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I : Ideal R) [hI : I.IsPrime] (a : R) (ha : a ≠ 0)
    (haI : a ∈ I) : ∃ u : R, Prime u ∧ u ∣ a ∧ u ∈ I := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl ha
  | h₂ x hx => exact absurd (I.eq_top_of_isUnit_mem haI hx) hI.ne_top
  | h₃ a p ha' hp ih =>
    rcases hI.mem_or_mem haI with h | h
    · exact ⟨p, hp, dvd_mul_right _ _, h⟩
    · obtain ⟨u, hu, hua, huI⟩ := ih (right_ne_zero_of_mul ha) h
      exact ⟨u, hu, dvd_mul_of_dvd_right hua _, huI⟩

theorem hypersurface_diff_isPreirreducible (Ω : Type) [Field Ω] [IsAlgClosed Ω] (σ : Type) [Finite σ]
    (f g : MvPolynomial σ Ω) (D : ℕ) (hf0 : f ≠ 0) (hfD : f.totalDegree ≤ D)
    (hno : ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧
      ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧
        MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0)) :
    IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) := by
  intro U V hU hV ⟨p, hpS, hpU⟩ ⟨q, hqS, hqV⟩
  have hfp : f ∈ p.asIdeal := by simpa using hpS.1
  have hgp : g ∉ p.asIdeal := by simpa using hpS.2
  obtain ⟨u, hu, huf, hup⟩ := exists_prime_factor_mem_prime_ideal_ufd p.asIdeal f hf0 hfp
  obtain ⟨v, rfl⟩ := huf
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := right_ne_zero_of_mul hf0
  have hdeg := MvPolynomial.totalDegree_mul_of_isDomain hu0 hv0

  have hgrad : g ∉ (Ideal.span {u}).radical := by
    intro hg
    apply hgp
    have : (Ideal.span {u}).radical ≤ p.asIdeal :=
      (Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr hup)).trans
        p.isPrime.radical.le
    exact this hg
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω)] at hgrad
  simp only [MvPolynomial.mem_vanishingIdeal_iff, not_forall] at hgrad
  obtain ⟨P, hP, hPg⟩ := hgrad
  have hPu : MvPolynomial.eval P u = 0 := by
    have := hP u (Ideal.mem_span_singleton_self u)
    simpa [MvPolynomial.aeval_eq_eval] using this
  have hPg' : MvPolynomial.eval P g ≠ 0 := by simpa [MvPolynomial.aeval_eq_eval] using hPg

  have hvg : g ∈ (Ideal.span {v}).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω)]
    intro Q hQ
    have hQv : MvPolynomial.eval Q v = 0 := by
      have := hQ v (Ideal.mem_span_singleton_self v)
      simpa [MvPolynomial.aeval_eq_eval] using this
    by_contra hQg
    apply hno
    refine ⟨u, v, by omega, by omega, rfl, P, Q, hPu, hPg', hQv, ?_⟩
    simpa [MvPolynomial.aeval_eq_eval] using hQg

  have hprime : (Ideal.span {u}).IsPrime := (Ideal.span_singleton_prime hu0).mpr hu
  let x : PrimeSpectrum (MvPolynomial σ Ω) := ⟨Ideal.span {u}, hprime⟩
  have key : ∀ y ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g},
      y ∈ closure ({x} : Set _) := by
    intro y hy
    have hfy : u * v ∈ y.asIdeal := by simpa using hy.1
    have hgy : g ∉ y.asIdeal := by simpa using hy.2
    rw [← PrimeSpectrum.le_iff_mem_closure]
    show Ideal.span {u} ≤ y.asIdeal
    rw [Ideal.span_singleton_le_iff_mem]
    rcases y.isPrime.mem_or_mem hfy with h | h
    · exact h
    · exfalso; apply hgy
      have : (Ideal.span {v}).radical ≤ y.asIdeal :=
        (Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr h)).trans
          y.isPrime.radical.le
      exact this hvg
  have hxS : x ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} := by
    constructor
    · simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
      exact Ideal.mem_span_singleton.mpr (dvd_mul_right u v)
    · simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
      intro hg
      exact hgp (((Ideal.span_singleton_le_iff_mem _).mpr hup) hg)
  have hxU : x ∈ U := by
    have := key p hpS
    rw [mem_closure_iff] at this
    obtain ⟨z, hzU, hz⟩ := this U hU hpU
    rw [Set.mem_singleton_iff.mp hz] at hzU; exact hzU
  have hxV : x ∈ V := by
    have := key q hqS
    rw [mem_closure_iff] at this
    obtain ⟨z, hzV, hz⟩ := this V hV hqV
    rw [Set.mem_singleton_iff.mp hz] at hzV; exact hzV
  exact ⟨x, hxS, hxU, hxV⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEq
section
namespace GlobalTheory.InfimumSupPowerIdeal

theorem iInf_sup_pow_eq (C : Type) [CommRing C] (J : Ideal C) (hJ : IsAdicComplete J C)
    (u : ℕ → Ideal C) (hu : ∀ e : ℕ, u e = u (e + 1) ⊔ J ^ (e + 1)) (e : ℕ) :
    (⨅ l : ℕ, u l) ⊔ J ^ (e + 1) = u e := by

  have hsm : ∀ m : ℕ, (J ^ m • ⊤ : Submodule C C) = J ^ m := fun m => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]

  have hanti : Antitone u := antitone_nat_of_succ_le fun k => by
    rw [hu k]; exact le_sup_left
  have hJle : ∀ k, J ^ (k + 1) ≤ u k := fun k => by
    rw [hu k]; exact le_sup_right
  apply le_antisymm
  · exact sup_le (iInf_le u e) (hJle e)
  · intro x hx

    have step : ∀ (k : ℕ) (a : u k), ∃ b : u (k + 1), (a : C) - b ∈ J ^ (k + 1) := by
      intro k a
      have ha : (a : C) ∈ u (k + 1) ⊔ J ^ (k + 1) := by rw [← hu k]; exact a.2
      obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1 ha
      refine ⟨⟨b, hb⟩, ?_⟩
      have : (a : C) - b = c := by rw [← hbc]; ring
      rw [this]; exact hc
    choose g hg using step
    let s : ∀ n : ℕ, u (e + n) := fun n =>
      Nat.rec (motive := fun n => ↥(u (e + n))) ⟨x, hx⟩ (fun n a => g (e + n) a) n
    have hs0 : (s 0 : C) = x := rfl
    have hss : ∀ n, (s n : C) - s (n + 1) ∈ J ^ (e + n + 1) := fun n => hg (e + n) (s n)
    have hchain : ∀ m n, m ≤ n → (s m : C) - s n ∈ J ^ (e + m + 1) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have h1 : (s n : C) - s (n + 1) ∈ J ^ (e + m + 1) :=
          Ideal.pow_le_pow_right (by omega) (hss n)
        have hsum : (s m : C) - s (n + 1) = ((s m : C) - s n) + ((s n : C) - s (n + 1)) := by ring
        rw [hsum]; exact add_mem ih h1

    obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ.toIsPrecomplete (f := fun n => (s n : C)) (by
      intro m n hmn
      rw [hsm, SModEq.sub_mem]
      exact Ideal.pow_le_pow_right (by omega) (hchain m n hmn))
    have hL' : ∀ n, (s n : C) - L ∈ J ^ n := fun n => by
      have h := hL n
      rw [hsm, SModEq.sub_mem] at h
      exact h

    have hLu : L ∈ ⨅ l, u l := by
      rw [Submodule.mem_iInf]
      intro l
      have h1 : (s (l + 1) : C) ∈ u l := hanti (by omega : l ≤ e + (l + 1)) (s (l + 1)).2
      have h2 : (s (l + 1) : C) - L ∈ u l := hJle l (hL' (l + 1))
      have h3 := Submodule.sub_mem _ h1 h2
      rwa [sub_sub_cancel] at h3

    have hxL : x - L ∈ J ^ (e + 1) := by
      have h1 : (s 0 : C) - s (e + 1) ∈ J ^ (e + 1) := by simpa using hchain 0 (e + 1) (by omega)
      have hsum : x - L = ((s 0 : C) - s (e + 1)) + ((s (e + 1) : C) - L) := by rw [hs0]; ring
      rw [hsum]; exact add_mem h1 (hL' (e + 1))
    exact Submodule.mem_sup.2 ⟨L, hLu, x - L, hxL, by ring⟩

end GlobalTheory.InfimumSupPowerIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupStableInfTypeSpace
section
namespace GlobalTheory

open Classical in

theorem iSup_stable_inf_typeSpace {G E C : Type} [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* ℂˣ) (U : C → Submodule ℂ E) (S : C → Prop)
    (hU : ∀ c g, (U c).map (ρ g) ≤ U c) :
    (⨆ (c : C) (_ : S c), U c) ⊓
        (⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) =
      ⨆ (c : C) (_ : S c), U c ⊓
        (⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) := by
  set K : Submodule ℂ E :=
    ⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id) with hK
  have memK : ∀ x, x ∈ K ↔ ∀ h : P, ρ (h : G) x = ((ψ h : ℂˣ) : ℂ) • x := by
    intro x
    simp [hK, Submodule.mem_iInf, sub_eq_zero]
  have hc : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let T : E →ₗ[ℂ] E :=
    (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G)
  have hT : ∀ x, T x = (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G) x := by
    intro x
    simp only [T, LinearMap.smul_apply, LinearMap.sum_apply]
  have h1 : ∀ x ∈ K, T x = x := by
    intro x hx
    rw [hT]
    have : ∀ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G) x = x := by
      intro h
      rw [(memK x).1 hx h, smul_smul, Units.inv_mul, one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : ∀ x, T x ∈ K := by
    intro x
    rw [memK]
    intro k
    rw [hT, map_smul, smul_comm]
    congr 1
    rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ ?_
    intro h
    simp only [Equiv.coe_mulLeft, map_smul, map_mul, Subgroup.coe_mul, Module.End.mul_apply,
      smul_smul]
    congr 1
    rw [← Units.val_mul, mul_inv_rev, mul_comm (ψ h)⁻¹, mul_inv_cancel_left]
  have h3 : ∀ c, ∀ x ∈ U c, T x ∈ U c := by
    intro c x hx
    rw [hT]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun h _ =>
      Submodule.smul_mem _ _ (hU c h (Submodule.mem_map_of_mem hx)))
  apply le_antisymm
  · rintro x ⟨hx, hxK⟩
    have hle : (⨆ (c : C) (_ : S c), U c) ≤ (⨆ (c : C) (_ : S c), U c ⊓ K).comap T := by
      refine iSup₂_le fun c hc y hy => ?_
      exact (le_iSup₂_of_le (f := fun (c : C) (_ : S c) => U c ⊓ K) c hc le_rfl)
        (show T y ∈ U c ⊓ K from ⟨h3 c y hy, h2 y⟩)
    have := hle hx
    rwa [Submodule.mem_comap, h1 x hxK] at this
  · exact iSup₂_le fun c hc => inf_le_inf_right _
      (le_iSup₂_of_le (f := fun (c : C) (_ : S c) => U c) c hc le_rfl)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapIdealTopOfIsAffine
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem IdealSheafData.ideal_comap_top_of_isAffine (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) :
    (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  apply le_antisymm
  · have hle : J.comap f ≤ Scheme.IdealSheafData.ofIdealTop
        (Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩)) := by
      rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
      intro j hj
      rw [Ideal.mem_comap, Scheme.IdealSheafData.ofIdealTop_ideal]
      have h1 : (X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ (⊤ : Y.Opens) ≤ ⊤)).op) = 𝟙 _ :=
        X.presheaf.map_id _
      rw [h1]
      erw [CommRingCat.hom_id, Ideal.map_id]
      exact Ideal.mem_map_of_mem _ hj
    have := hle ⟨⊤, isAffineOpen_top X⟩
    simpa using this
  · rw [Ideal.map_le_iff_le_comap]
    intro j hj
    rw [Ideal.mem_comap, Scheme.IdealSheafData.comap, Scheme.Hom.ker_apply, RingHom.mem_ker]
    have hj' : J.subschemeι.appTop.hom j = 0 := by
      have := hj
      rw [← J.ker_subschemeι, Scheme.Hom.ker_apply, RingHom.mem_ker] at this
      exact this
    have hc := congrArg (fun g => g.hom j)
      (congrArg Scheme.Hom.appTop (pullback.condition (f := f) (g := J.subschemeι)))
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hc
    change (pullback.fst f J.subschemeι).appTop.hom (f.appTop.hom j) = 0
    rw [hc, hj', map_zero]

example : ∀ (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (J : Y.IdealSheafData), (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩) :=
  fun X Y _ _ f J => IdealSheafData.ideal_comap_top_of_isAffine X Y f J

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEq
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem idem_germ_eq_of_isUnit_iff {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : a * a = a) (hb : b * b = b) (h : IsUnit a ↔ IsUnit b) : a = b := by
  have key : ∀ c : R, c * c = c → (IsUnit c → c = 1) ∧ (¬ IsUnit c → c = 0) := by
    intro c hc
    refine ⟨fun hu => ?_, fun hn => ?_⟩
    · obtain ⟨u, rfl⟩ := hu
      have : (u : R) * u = u * 1 := by rw [mul_one]; exact hc
      exact (Units.mul_right_inj u).mp this
    · rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h1 | h1
      · exact absurd h1 hn
      · have : (1 - c) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
        obtain ⟨u, hu⟩ := h1
        rw [← hu] at this
        simpa using this
  by_cases hau : IsUnit a
  · rw [(key a ha).1 hau, (key b hb).1 (h.mp hau)]
  · rw [(key a ha).2 hau, (key b hb).2 (fun hbu => hau (h.mpr hbu))]

theorem idempotent_eq_of_basicOpen_eq : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' →
    X.basicOpen e = X.basicOpen e' → e = e' := by
  intro X e e' he he' hb
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e e' (fun x hx => ?_)
  change X.presheaf.germ ⊤ x hx e = X.presheaf.germ ⊤ x hx e'
  apply idem_germ_eq_of_isUnit_iff (R := X.presheaf.stalk x)
  · rw [← map_mul, he]
  · rw [← map_mul, he']
  · rw [← X.mem_basicOpen e x hx, ← X.mem_basicOpen e' x hx, hb]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsAlt
section
open scoped TensorProduct

namespace GlobalTheory.ValuativeQuotient

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem main : ∀ (V K B : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing B] [Algebra V B] (JK : Ideal (K ⊗[V] B)),
    ∃! J : Ideal B, Module.Flat V (B ⧸ J) ∧
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) = JK := by
  intro V K B _ _ _ _ _ _ _ _ JK
  have hloc := IsLocalization.tensorRight (S := B) K (nonZeroDivisors V)
  set M := Algebra.algebraMapSubmonoid B (nonZeroDivisors V) with hM
  have hmap : ∀ I : Ideal B,
      I.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) =
        I.map (algebraMap B (K ⊗[V] B)) := fun I => rfl
  have hsmul : ∀ (J : Ideal B) (v : V) (b : B),
      v • Ideal.Quotient.mk J b = Ideal.Quotient.mk J (algebraMap V B v * b) := by
    intro J v b
    rw [← Algebra.smul_def, ← Ideal.Quotient.mkₐ_eq_mk V, map_smul]
  have hflat : ∀ J : Ideal B, Module.Flat V (B ⧸ J) ↔ ∀ m ∈ M, ∀ b : B, m * b ∈ J → b ∈ J := by
    intro J
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
    constructor
    · rintro h m ⟨v, hv, rfl⟩ b hb
      have h0 := h (Ideal.Quotient.mk J b) ((Submodule.mem_torsion_iff _).mpr
        ⟨⟨v, hv⟩, by
          show v • Ideal.Quotient.mk J b = 0
          rw [hsmul, Ideal.Quotient.eq_zero_iff_mem]
          exact hb⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    · intro h x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨⟨v, hv⟩, hvb⟩ := (Submodule.mem_torsion_iff _).mp hx
      change v • Ideal.Quotient.mk J b = 0 at hvb
      rw [hsmul, Ideal.Quotient.eq_zero_iff_mem] at hvb
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h _ ⟨v, hv, rfl⟩ b hvb)
  refine ⟨JK.comap (algebraMap B (K ⊗[V] B)), ⟨?_, ?_⟩, ?_⟩
  · rw [hflat]
    intro m hm b hb
    rw [Ideal.mem_comap, map_mul] at hb
    exact (Ideal.unit_mul_mem_iff_mem JK (IsLocalization.map_units (K ⊗[V] B) ⟨m, hm⟩)).mp hb
  · rw [hmap]
    exact IsLocalization.map_comap M (K ⊗[V] B) JK
  · rintro J' ⟨hJ'f, hJ'⟩
    rw [hmap] at hJ'
    rw [hflat] at hJ'f
    apply le_antisymm
    · rw [← hJ']
      exact Ideal.le_comap_map
    · intro b hb
      rw [Ideal.mem_comap, ← hJ', IsLocalization.mem_map_algebraMap_iff M] at hb
      obtain ⟨⟨x, m⟩, hxm⟩ := hb
      rw [← map_mul, IsLocalization.eq_iff_exists M] at hxm
      obtain ⟨c, hc⟩ := hxm
      apply hJ'f (c * m) (M.mul_mem c.2 m.2)
      have : (c : B) * (m : B) * b = c * x.1 := by rw [← hc]; ring
      rw [this]
      exact J'.mul_mem_left _ x.2

end GlobalTheory.ValuativeQuotient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisLast
section
namespace GlobalTheory.IsotropicVectorExistence

theorem key {z : ℂ} (k : ℕ) (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * (z ^ (2 ^ k) + 1) := by
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]; ring
    have h2 : (3 / 2 : ℝ) ≤ ‖z ^ (2 ^ k) + 1‖ := by
      have h3 : (2 : ℂ) = (z ^ (2 ^ k) + 1) - (z ^ (2 ^ k) - 1) := by ring
      have h4 : ‖(2 : ℂ)‖ ≤ ‖z ^ (2 ^ k) + 1‖ + ‖z ^ (2 ^ k) - 1‖ := by
        rw [h3]; exact norm_sub_le _ _
      have h5 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have h6 := h (2 ^ k)
      linarith
    rw [e, norm_mul, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖z ^ (2 ^ k) - 1‖ * ‖z ^ (2 ^ k) + 1‖ :=
        mul_le_mul ih h2 (by norm_num) (norm_nonneg _)

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ (by positivity)] at hk
  have a := key k h
  have b := h (2 ^ k)
  nlinarith

end GlobalTheory.IsotropicVectorExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisRest
section
namespace GlobalTheory.HermitianEigenvalueInequality

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), ∀ x ∈ Submodule.span E (↑L : Set (Fin n → E)), ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by
  intro E _ _ n L x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (y + z) = d₂ • (d₁ • y) + d₁ • (d₂ • z) := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem _ h₁) (L.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(b : NumberField.RingOfIntegers E) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hd, ?_⟩
    have e : ((b : NumberField.RingOfIntegers E) * d) • (c • y) = a • (d • y) := by
      simp only at hab
      rw [← algebraMap_smul E ((b : NumberField.RingOfIntegers E) * d), ← algebraMap_smul E a,
        ← algebraMap_smul E d, smul_smul, smul_smul, map_mul, ]
      congr 1
      rw [← hab]
      ring
    rw [e]
    exact L.smul_mem _ h

end GlobalTheory.HermitianEigenvalueInequality
end

