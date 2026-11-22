import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0048
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsIntegralZpowOfPowEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem isIntegral_of_pow_eq_one {F : Type} [Field F] {z : F} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) :
    IsIntegral ℤ z := by
  refine IsIntegral.of_pow hN ?_
  rw [hz]
  exact isIntegral_one

theorem isIntegral_zpow_of_pow_eq_one {F : Type} [Field F] {z : F} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) (a : ℤ) :
    IsIntegral ℤ (z ^ a) := by

  refine GlobalTheory.PlaceInt.isIntegral_of_pow_eq_one hN ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm a, zpow_mul, zpow_natCast, hz, one_zpow]

private theorem isIntegral_int_ringHom_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a : A}
    (h : IsIntegral ℤ a) : IsIntegral ℤ (f a) :=
  h.map f.toIntAlgHom

theorem datum_isIntegral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ ph ψ x₀, d.PhiPin ph ψ x₀ → ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ x₀ hpin x0 q
  obtain ⟨-, hM, -, -, hII, -⟩ := id hd
  obtain ⟨hloc, hsupp, hequi, hone, hspan0, hsum⟩ := hpin
  have hpd : 0 < d.pd := by
    rcases Nat.eq_zero_or_pos d.pd with h | h
    · have h3 := d.l₂.three_le
      rw [hM, h, mul_zero] at h3
      omega
    · exact h

  have hI : d.I ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot, sup_bot_eq] at hII
    exact bot_ne_top hII
  have : Finite (𝓞 E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot d.I hI
  have := Dw.fin
  have := Dw.proj
  obtain ⟨eI⟩ := GlobalTheory.HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I (Dw.p + Dw.q) Dw.rank
  have : Finite (LaI Xo c d) := Finite.of_equiv _ eI.symm.toEquiv
  have : Finite (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) :=
    Finite.of_injective (fun e : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d => (e : LaI Xo c d → LaI Xo c d))
      (fun a b h => LinearEquiv.ext (congrFun h))

  have hph : ∀ x, IsIntegral ℤ (ph x) := by
    intro x
    by_cases h0 : ph x = 0
    · rw [h0]
      exact isIntegral_zero
    have hspan := hsupp x h0
    obtain ⟨-, htrans, adj, -, hadj⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
    let pad : (Fin n → LaJ Xo c d) → Fin (Dw.p + Dw.q) → LaJ Xo c d :=
      fun z i => if h : i.val < n then z ⟨i.val, h⟩ else 0
    have hpadv : ∀ z i (h : i.val < n), pad z i = z ⟨i.val, h⟩ := fun z i h => dif_pos h
    have hpad : ∀ z : Fin n → LaJ Xo c d, Submodule.span (𝓞 E) (z '' {b | b.val < Dw.p + Dw.q}) = ⊤ →
        Submodule.span (𝓞 E) (Set.range (pad z)) = ⊤ := by
      intro z hz
      rw [eq_top_iff, ← hz]
      apply Submodule.span_mono
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, hpadv z _ b.isLt⟩
    obtain ⟨g, hg, -⟩ := htrans (pad x₀) (pad x) (hpad x₀ hspan0) (hpad x hspan)
    have h1 := hequi (adj g) g ((hadj (adj g) g).mpr rfl) x₀
    rw [hone, _root_.mul_one] at h1
    have h2 : ph x = ph (fun b => g (x₀ b)) := by
      apply hloc
      intro b hb
      have hb' := hg ⟨b.val, hb⟩
      rw [hpadv x₀ _ b.isLt, hpadv x _ b.isLt] at hb'
      exact hb'.symm
    rw [h2, h1]
    obtain ⟨m, hm, hpow⟩ :=
      isOfFinOrder_iff_pow_eq_one.mp (ψ.isOfFinOrder (isOfFinOrder_of_finite (adj g))).inv
    refine GlobalTheory.PlaceInt.isIntegral_of_pow_eq_one hm ?_
    rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]

  have hz : IsIntegral ℤ (zetaM c ^ pairL (l := l) x0 (fun b => levRep (q b))) :=
    GlobalTheory.PlaceInt.isIntegral_zpow_of_pow_eq_one (N := l.M) (by have := l.three_le; omega)
      (GlobalTheory.DatumInverseCharacter.root_pow c dvd_rfl) _

  have hφ : IsIntegral ℤ (d.φδ q) := by
    have he : IsIntegral ℤ (d.eF (d.φδ q)) := by
      rw [hsum q]
      refine finsum_induction (fun y => IsIntegral ℤ y) isIntegral_zero
        (fun a b ha hb => ha.add hb) (fun x => ?_)
      refine (isIntegral_int_ringHom_apply d.eF.toRingHom (hph x)).mul ?_
      exact GlobalTheory.PlaceInt.isIntegral_zpow_of_pow_eq_one hpd
        (GlobalTheory.DatumInverseCharacter.root_pow d.c₂ (Dvd.intro_left _ hM.symm)) _
    have hb := isIntegral_int_ringHom_apply d.eF.symm.toRingHom he
    simpa using hb
  exact isIntegral_int_ringHom_apply d.eF.toRingHom (hz.mul hφ)

end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPrincipalIdealRingLoc
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PlaceInt.LocBasis
open NumberField Module
open scoped nonZeroDivisors

theorem exists_basis_up_to {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A] [Algebra A E]
    [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : ℕ} (L : Submodule O (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ (s : S) (b : Fin n → Fin n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (Fin n → E) := Submodule.span A (L : Set (Fin n → E)) with hM
  have : Submodule.IsLattice E M :=
    { fg := by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = n := by
    simpa using Submodule.IsLattice.finrank_of_pi E M
  let c : Basis (Fin n) A M := Module.finBasisOfFinrankEq A M hrk
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : Fin n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (Fin n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : Fin n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis (Fin n) A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : Fin n → E) = (t i : O) • (c i : Fin n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : Fin n → Fin n → E := fun i => (c' i : Fin n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

def primeTo (R : Type) [CommRing R] (m : ℕ) : Submonoid R where
  carrier := {x | ∃ k : ℕ, k ≠ 0 ∧ Nat.Coprime k m ∧ x = (k : R)}
  one_mem' := ⟨1, one_ne_zero, Nat.coprime_one_left m, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha0, ha, rfl⟩ ⟨b, hb0, hb, rfl⟩
    exact ⟨a * b, mul_ne_zero ha0 hb0, Nat.Coprime.mul_left ha hb, by simp⟩

theorem exists_prime_mem {R : Type} [CommRing R] (Q : Ideal R) (hQ : Q.IsPrime) (a : ℕ) (ha : a ≠ 0)
    (h : (a : R) ∈ Q) : ∃ p : ℕ, p.Prime ∧ (p : R) ∈ Q := by
  induction a using induction_on_primes with
  | zero => exact absurd rfl ha
  | one => exact absurd ((Ideal.eq_top_iff_one Q).2 (by simpa using h)) hQ.ne_top
  | prime_mul p a hp ih =>
    rw [Nat.cast_mul] at h
    rcases hQ.mem_or_mem h with h | h
    · exact ⟨p, hp, h⟩
    · exact ih (by rintro rfl; simp at ha) h

theorem isPrincipalIdealRing_loc (E : Type) [Field E] [NumberField E] (m : ℕ) (hm : 0 < m)
    (hS : primeTo (𝓞 E) m ≤ (𝓞 E)⁰) (A : Type) [CommRing A] [IsDomain A] [Algebra (𝓞 E) A]
    [IsLocalization (primeTo (𝓞 E) m) A] : IsPrincipalIdealRing A := by
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain (𝓞 E) hS A
  have hinj : Function.Injective (algebraMap (𝓞 E) A) := IsLocalization.injective A hS
  have hm0 : (m : A) ≠ 0 := by
    rw [← map_natCast (algebraMap (𝓞 E) A), map_ne_zero_iff _ hinj]
    exact_mod_cast hm.ne'
  have hI : (Ideal.span {(m : A)}) ≠ 0 := by simpa using hm0
  apply IsPrincipalIdealRing.of_finite_primes
  apply (((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset
  intro P hP
  have hP' : P.IsPrime := hP
  by_cases hb : P = ⊥
  · exact Or.inl hb
  refine Or.inr ⟨⟨P, hP', hb⟩, ?_, rfl⟩
  set Q := P.comap (algebraMap (𝓞 E) A) with hQ
  have hQb : Q ≠ ⊥ := by
    intro h
    apply hb
    rw [← IsLocalization.map_under (primeTo (𝓞 E) m) A P]
    change Q.map _ = ⊥
    rw [h, Ideal.map_bot]
  have h1 : ((Ideal.absNorm Q : ℕ) : A) ∈ P := by
    have := Ideal.absNorm_mem Q
    rw [hQ, Ideal.mem_comap, map_natCast] at this
    exact this
  obtain ⟨p, hp, hpP⟩ := exists_prime_mem P hP' _ (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) h1
  have hpm : p ∣ m := by
    by_contra hn
    have hu := IsLocalization.map_units A (⟨(p : 𝓞 E), p, hp.ne_zero, (Nat.Prime.coprime_iff_not_dvd hp).2 hn,
      rfl⟩ : primeTo (𝓞 E) m)
    simp only [map_natCast] at hu
    exact hP'.ne_top (Ideal.eq_top_of_isUnit_mem _ hpP hu)
  obtain ⟨c, rfl⟩ := hpm
  simp only [Set.mem_setOf_eq, Ideal.dvd_span_singleton, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.PlaceInt.LocBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.LocBasis

theorem exists_matrix_primeTo : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), 0 < N → L ≤ stdLat E n → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ L → ∀ m : ℕ, 0 < m → ∃ (k₁ : ℕ) (g : Matrix (Fin n) (Fin n) (𝓞 E)), Nat.Coprime k₁ m ∧ g.det ≠ 0 ∧ (∀ v ∈ stdLat E n, (g.map (algebraMap (𝓞 E) E)).mulVec v ∈ L) ∧ ∀ w ∈ L, ∃ v ∈ stdLat E n, (k₁ : E) • w = (g.map (algebraMap (𝓞 E) E)).mulVec v := by
  intro E _ _ n L N hN hle hNL m hm
  classical
  have hmem : ∀ v : Fin n → E, v ∈ stdLat E n ↔ ∃ u : Fin n → 𝓞 E, v = fun i => algebraMap (𝓞 E) E (u i) := fun v => by
    simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    constructor
    · intro h
      choose u hu using h
      exact ⟨u, funext fun i => (hu i).symm⟩
    · rintro ⟨u, rfl⟩ i
      exact ⟨u i, rfl⟩
  have hS : primeTo (𝓞 E) m ≤ nonZeroDivisors (𝓞 E) := by
    rintro _ ⟨k, hk, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)
  let A := Localization.subalgebra E (primeTo (𝓞 E) m) hS
  have : IsPrincipalIdealRing A := isPrincipalIdealRing_loc E m hm hS A
  have hstd : (stdLat E n).FG := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  have hfg : L.FG := hstd.of_le hle
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : (Pi.basisFun E (Fin n) i) ∈ stdLat E n :=
      (hmem _).2 ⟨Pi.single i 1, funext fun j => by by_cases h : j = i <;> simp [h, Pi.single_apply]⟩
    have h2 := hNL (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1)
    have h3 := Submodule.smul_mem (Submodule.span E (L : Set (Fin n → E))) (N : E)⁻¹ (Submodule.subset_span h2)
    rwa [← algebraMap_smul E (N : 𝓞 E), smul_smul, map_natCast, inv_mul_cancel₀ hN0, one_smul] at h3
  obtain ⟨⟨_, k, hk0, hk, rfl⟩, b, hli, hb, hw⟩ := exists_basis_up_to (A := A) (primeTo (𝓞 E) m) L hfg hsp
  choose u hu using fun j => (hmem (b j)).1 (hle (hb j))
  let g : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun i j => u j i
  have hg : ∀ a : Fin n → 𝓞 E, (g.map (algebraMap (𝓞 E) E)).mulVec (fun i => algebraMap (𝓞 E) E (a i)) =
      ∑ j, a j • b j := fun a => by
    funext i
    simp only [Matrix.mulVec, dotProduct, g, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu j, Algebra.smul_def, mul_comm]
  refine ⟨k, g, hk, ?_, ?_, ?_⟩
  · have hcol : (g.map (algebraMap (𝓞 E) E)).col = b := by
      funext j i
      rw [hu j]; rfl
    have hunit : IsUnit (g.map (algebraMap (𝓞 E) E)) :=
      Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
    intro h0
    have := ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
    apply this
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · intro v hv
    obtain ⟨a, rfl⟩ := (hmem v).1 hv
    rw [hg]
    exact Submodule.sum_mem _ fun j _ => L.smul_mem _ (hb j)
  · intro w hwL
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw w hwL)
    refine ⟨_, (hmem _).2 ⟨a, rfl⟩, ?_⟩
    rw [hg, ha]
    change _ = (k : 𝓞 E) • w
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
end GlobalTheory.PlaceInt.LocBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecomposition
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

namespace IsotropicPrimary

theorem exists_primary_complement (Z : Type) [CommGroup Z] [Finite Z] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ P Q : Subgroup Z, (∀ u, u ∈ P ↔ ∃ j : ℕ, u ^ (ℓ ^ j) = 1) ∧ Nat.Coprime (Nat.card Q) ℓ ∧
      (Function.Bijective fun y : P × Q => (y.1 : Z) * (y.2 : Z)) ∧
      Nat.card P = ℓ ^ (Nat.card Z).factorization ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨S⟩ : Nonempty (Sylow ℓ Z) := inferInstance
  haveI : (S : Subgroup Z).Normal := Subgroup.normal_of_isMulCommutative _
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime (N := (S : Subgroup Z)) S.card_coprime_index
  refine ⟨S, Q, fun u => ⟨fun hu => ?_, fun hu => ?_⟩, ?_, hQ, S.card_eq_multiplicity⟩
  · obtain ⟨k, hk⟩ := S.isPGroup' ⟨u, hu⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · obtain ⟨j, hj⟩ := hu
    have hp : IsPGroup ℓ (Subgroup.zpowers u) :=
      IsPGroup.of_card_dvd_pow (n := j) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hj)
    obtain ⟨T, hT⟩ := hp.exists_le_sylow
    letI := Sylow.unique_of_normal S ‹_›
    have hTS : T = S := Subsingleton.elim _ _
    subst hTS
    exact hT (Subgroup.mem_zpowers u)
  · rw [← hQ.symm.index_eq_card]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 S.not_dvd_index)

theorem epi_spMap_of_fields {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  letI : Algebra K k := β.toAlgebra
  have hff : (CommRingCat.ofHom β).hom.FaithfullyFlat := by
    change Module.FaithfullyFlat K k
    infer_instance
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom β)).2 hff
  exact Flat.epi_of_flat_of_surjective _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def zhSubgroup (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ) (hN : 0 < N) (T : Over Xo.X) :
    Subgroup (Fin n → (T ⟶ Xo.univ.t.G)) :=
  have hone : InZh Xo Λ N (1 : Fin n → (T ⟶ Xo.univ.t.G)) := by
    refine ⟨fun b => one_pow _, fun mu _ cm _ i => List.prod_eq_one fun x hx => ?_⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    have := Xo.univ.t.act.hom (cm i j)
    exact MonObj.one_comp _
  have hpow : ∀ (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → ∀ k : ℕ, InZh Xo Λ N (a ^ k) := by
    intro a ha k
    induction k with
    | zero => rw [pow_zero]; exact hone
    | succ k ih => rw [pow_succ]; exact ZhStable.inZh_mul Xo Λ N _ _ ih ha
  { carrier := {a | InZh Xo Λ N a}
    one_mem' := hone
    mul_mem' := fun {a a'} ha ha' => ZhStable.inZh_mul Xo Λ N a a' ha ha'
    inv_mem' := fun {a} ha => by
      have h1 : a ^ (N ^ 2) = 1 := funext ha.1
      have h2 : a⁻¹ = a ^ (N ^ 2 - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (pow_pos hN 2), h1]
      change InZh Xo Λ N a⁻¹
      rw [h2]
      exact hpow a ha _ }

theorem enumeration_bijective (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X)
    {n : ℕ} (Λ : GenLat E n) {N : ℕ} (hΛ : Λ.Unimod) (hN : 0 < N)
    (hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (hz : ∀ i, InZh Xo Λ N (z i))
    (hinj : GeoInj Xo x z) : Function.Injective z ∧ ∀ a, InZh Xo Λ N a → ∃ i, z i = a := by
  refine ⟨fun i j hij => ?_, fun a ha => ?_⟩
  · let g : ptO Xo (spMap (RingHom.id K) ≫ x) ⟶ ptO Xo x := Over.homMk (spMap (RingHom.id K)) rfl
    refine hinj K (RingHom.id K) g rfl ?_
    show (fun b => g ≫ z i b) = fun b => g ≫ z j b
    rw [hij]
  · let ψ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
    let g : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
    have hw : ∀ i, InZh Xo Λ N (fun b => g ≫ z i b) := fun i => ZhStable.inZh_comp Xo Λ N g (z i) (hz i)
    obtain ⟨i, hi⟩ := IsotropicEnum.exists_eq_of_isAlgClosed Xo (spMap ψ ≫ x) Λ hΛ hN hle
      (fun i b => g ≫ z i b) hw (hinj (AlgebraicClosure K) ψ g rfl) (fun b => g ≫ a b)
      (ZhStable.inZh_comp Xo Λ N g a ha)
    refine ⟨i, funext fun b => ?_⟩
    haveI := epi_spMap_of_fields ψ
    have hb := congrArg CommaMorphism.left (congrFun hi b)
    simp only [Over.comp_left] at hb
    exact Over.OverMorphism.ext ((cancel_epi (spMap ψ)).1 hb)

end IsotropicPrimary

open IsotropicPrimary in

theorem isotropic_primary_decomposition :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x z → ∃ (J J' : Type) (_ : Fintype J) (_ : Fintype J') (a : J → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (a' : J' → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (σ : J × J' ≃ Fin (Λ.zCard N (Dw.p + Dw.q))), Function.Injective a ∧ (∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) ∧ (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ i b, a' i b ^ m = 1 ∧ a' i b ^ (N ^ 2) = 1) ∧ (∀ i i' b, z (σ (i, i')) b = a i b * a' i' b) ∧ Fintype.card J = ℓ ^ (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ := by
  intro E _ _ _ H Dw l Xo K _ x n Λ N M ℓ hΛ hlev hℓ z hz hinj
  have hN : 0 < N := hlev.1.pos
  have hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := hlev.2.2.trans inf_le_left
  obtain ⟨hzinj, hzon⟩ := enumeration_bijective Xo x Λ hΛ hN hle z hz hinj
  let e : Fin (Λ.zCard N (Dw.p + Dw.q)) → zhSubgroup Xo Λ N hN (ptO Xo x) := fun i => ⟨z i, hz i⟩
  have he : Function.Bijective e :=
    ⟨fun i j h => hzinj (congrArg Subtype.val h), fun u => by
      obtain ⟨i, hi⟩ := hzon u.1 u.2
      exact ⟨i, Subtype.ext hi⟩⟩
  haveI : Finite (zhSubgroup Xo Λ N hN (ptO Xo x)) := Finite.of_surjective e he.2
  obtain ⟨P, Q, hP, hQ, hPQ, hcard⟩ := exists_primary_complement (zhSubgroup Xo Λ N hN (ptO Xo x)) ℓ hℓ
  refine ⟨P, Q, Fintype.ofFinite _, Fintype.ofFinite _, fun p => ((p : zhSubgroup Xo Λ N hN (ptO Xo x)) : Fin n → _),
    fun q => ((q : zhSubgroup Xo Λ N hN (ptO Xo x)) : Fin n → _),
    (Equiv.ofBijective _ hPQ).trans (Equiv.ofBijective e he).symm, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p p' h => Subtype.ext (Subtype.ext h)
  · intro u
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨(p : zhSubgroup Xo Λ N hN (ptO Xo x)).2, fun b => ?_⟩
      obtain ⟨j, hj⟩ := (hP _).1 p.2
      refine ⟨j, ?_⟩
      have := congrArg (fun w : zhSubgroup Xo Λ N hN (ptO Xo x) => w.1 b) hj
      simpa using this
    · rintro ⟨hu, hpow⟩
      choose j hj using hpow
      refine ⟨⟨⟨u, hu⟩, (hP _).2 ⟨∑ b, j b, Subtype.ext (funext fun b => ?_)⟩⟩, rfl⟩
      obtain ⟨c, hc⟩ : ℓ ^ j b ∣ ℓ ^ (∑ b, j b) :=
        pow_dvd_pow ℓ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
      simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply]
      rw [hc, pow_mul, hj b, one_pow]
  · refine ⟨Nat.card Q, hQ, fun i b => ⟨?_, ((i : zhSubgroup Xo Λ N hN (ptO Xo x)).2 : InZh Xo Λ N _).1 b⟩⟩
    have := congrArg (fun w : Q => (w : zhSubgroup Xo Λ N hN (ptO Xo x)).1 b) (pow_card_eq_one' (G := Q) (x := i))
    simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply] at this
    exact this
  · intro i i' b
    have h1 : e ((Equiv.ofBijective e he).symm ((i : zhSubgroup Xo Λ N hN (ptO Xo x)) * (i' : zhSubgroup Xo Λ N hN (ptO Xo x)))) =
        (i : zhSubgroup Xo Λ N hN (ptO Xo x)) * (i' : zhSubgroup Xo Λ N hN (ptO Xo x)) :=
      Equiv.ofBijective_apply_symm_apply e he _
    simp only [Equiv.trans_apply, Equiv.ofBijective_apply]
    exact congrFun (congrArg Subtype.val h1) b
  · rw [@Fintype.card_eq_nat_card P (Fintype.ofFinite P), hcard, ← Nat.card_eq_of_bijective e he, Nat.card_fin]

end GlobalTheory
end
end

