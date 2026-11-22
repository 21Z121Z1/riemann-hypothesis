import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAwayOfFlatLift
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftAway

theorem mul_eq_zero_of_mem_map {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    {I : Ideal R} (hI : I ^ 2 = 0) {u v : S} (hu : u ∈ I.map (algebraMap R S))
    (hv : v ∈ I.map (algebraMap R S)) : u * v = 0 := by
  have h := Ideal.mul_mem_mul hu hv
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  exact h

theorem frac_add {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B'] {a : B} {y z : B'}
    (hy : ∃ (n : ℕ) (b : B), y * algebraMap B B' a ^ n = algebraMap B B' b)
    (hz : ∃ (n : ℕ) (b : B), z * algebraMap B B' a ^ n = algebraMap B B' b) :
    ∃ (n : ℕ) (b : B), (y + z) * algebraMap B B' a ^ n = algebraMap B B' b := by
  obtain ⟨n, b, hb⟩ := hy
  obtain ⟨m, c, hc⟩ := hz
  refine ⟨n + m, b * a ^ m + c * a ^ n, ?_⟩
  rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hb, ← hc]
  ring

theorem isLocalization_away_of_flat_lift (R B B' B₀ B₀' : Type) [CommRing R] [CommRing B]
    [CommRing B'] [CommRing B₀] [CommRing B₀'] [Algebra R B] [Algebra R B'] [Algebra B B']
    [IsScalarTower R B B'] [Algebra B₀ B₀'] (I : Ideal R) (hI : I ^ 2 = 0)
    (hflat : Module.Flat R B') (p : B →+* B₀) (p' : B' →+* B₀') (hp : Function.Surjective p)
    (hp' : Function.Surjective p') (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B))
    (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B'))
    (hcomm : ∀ b, p' (algebraMap B B' b) = algebraMap B₀ B₀' (p b)) (a : B)
    (hloc : IsLocalization.Away (p a) B₀') : IsLocalization.Away a B' := by
  haveI := hloc
  haveI := hflat
  set φ := algebraMap B B' with hφ
  have hφs : ∀ (r : R) (b : B), φ (r • b) = r • φ b := fun r b => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, ← IsScalarTower.algebraMap_apply]

  have hunit : IsUnit (φ a) := by
    have hu : IsUnit (p' (φ a)) := by
      rw [hcomm]; exact IsLocalization.Away.algebraMap_isUnit (p a)
    obtain ⟨v, hv⟩ := hp' (↑hu.unit⁻¹ : B₀')
    have hn : φ a * v - 1 ∈ I.map (algebraMap R B') := by
      rw [← hker', map_sub, map_mul, hv, map_one, IsUnit.mul_val_inv, sub_self]
    have h2 := mul_eq_zero_of_mem_map hI hn hn
    refine isUnit_iff_exists_inv.mpr ⟨v * (1 - (φ a * v - 1)), ?_⟩
    linear_combination (-1 : B') * h2

  have lift0 : ∀ y : B', ∃ (n : ℕ) (b : B), y * φ a ^ n - φ b ∈ I.map (algebraMap R B') := by
    intro y
    obtain ⟨⟨z, s, hs⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (p a)) (p' y)
    obtain ⟨n, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := hp z
    refine ⟨n, b, ?_⟩
    dsimp only at hz
    rw [← hker', map_sub, map_mul, map_pow, hcomm, hcomm, ← map_pow, hz, sub_self]
  have fracI : ∀ i ∈ I, ∀ y : B', ∃ (n : ℕ) (b : B),
      algebraMap R B' i * y * φ a ^ n = φ b := by
    intro i hi y
    obtain ⟨n, b, hb⟩ := lift0 y
    refine ⟨n, algebraMap R B i * b, ?_⟩
    have h0 := mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem (algebraMap R B') hi) hb
    rw [map_mul, hφ, ← IsScalarTower.algebraMap_apply]
    linear_combination h0
  have fracMem : ∀ z ∈ I.map (algebraMap R B'), ∃ (n : ℕ) (b : B), z * φ a ^ n = φ b := by
    intro z hz
    change z ∈ Submodule.span B' (algebraMap R B' '' I) at hz
    have key : ∀ c : B', ∃ (n : ℕ) (b : B), (c * z) * φ a ^ n = φ b := by
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        intro c
        obtain ⟨n, b, hb⟩ := fracI i hi c
        exact ⟨n, b, by rw [← hb]; ring⟩
      | zero => intro c; exact ⟨0, 0, by simp⟩
      | add x y _ _ hx hy => intro c; rw [mul_add]; exact frac_add (hx c) (hy c)
      | smul d x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx (c * d)
    simpa using key 1
  have surj : ∀ y : B', ∃ (n : ℕ) (b : B), y * φ a ^ n = φ b := by
    intro y
    obtain ⟨n, b, hb⟩ := lift0 y
    obtain ⟨m, c, hc⟩ := fracMem _ hb
    refine ⟨n + m, c + b * a ^ m, ?_⟩
    rw [map_add, map_mul, map_pow, ← hc]
    ring

  have kerI : ∀ x : B, φ x = 0 → ∃ n : ℕ, a ^ n * x ∈ I.map (algebraMap R B) := by
    intro x hx
    have h : algebraMap B₀ B₀' (p x) = 0 := by rw [← hcomm, hx, map_zero]
    obtain ⟨⟨s, hs⟩, h2⟩ :=
      (IsLocalization.map_eq_zero_iff (M := Submonoid.powers (p a)) (S := B₀') (p x)).mp h
    obtain ⟨n, rfl⟩ := hs
    refine ⟨n, (hker _).mp ?_⟩
    rw [map_mul, map_pow]
    exact h2
  have core : ∀ x ∈ I.map (algebraMap R B), φ x = 0 → ∃ N : ℕ, a ^ N * x = 0 := by
    intro x hxI hx
    change x ∈ Submodule.span B (algebraMap R B '' I) at hxI
    obtain ⟨k, c, g, rfl⟩ := Submodule.mem_span_set'.mp hxI
    choose i hi hgi using fun j => (g j).2
    have hrel : ∑ j, i j • φ (c j) = 0 := by
      rw [← hx, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, map_mul, Algebra.smul_def, ← hgi j, hφ,
        IsScalarTower.algebraMap_apply R B B', mul_comm]
    obtain ⟨l, A, y, hy, hA⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := R) (M := B') (f := i) (x := fun j => φ (c j)) hrel
    choose m d hd using fun j => surj (y j)
    obtain ⟨M, hMdef⟩ : ∃ M, M = ∑ j, m j := ⟨_, rfl⟩
    have hMle : ∀ j, m j ≤ M := fun j => hMdef ▸
      Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ j)
    have hM : ∀ j, y j * φ a ^ M = φ (d j * a ^ (M - m j)) := by
      intro j
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (hMle j)
      rw [ht, Nat.add_sub_cancel_left, map_mul, map_pow, ← hd j, pow_add]
      ring
    have he : ∀ q, φ (c q * a ^ M - ∑ j, A q j • (d j * a ^ (M - m j))) = 0 := by
      intro q
      rw [map_sub, map_mul, map_pow, map_sum]
      simp_rw [hφs, ← hM]
      rw [show φ (c q) = ∑ j, A q j • y j from hy q, Finset.sum_mul]
      simp [smul_mul_assoc]
    choose n' hn' using fun q => kerI _ (he q)
    obtain ⟨N, hNdef⟩ : ∃ N, N = ∑ q, n' q := ⟨_, rfl⟩
    have hNle : ∀ q, n' q ≤ N := fun q => hNdef ▸
      Finset.single_le_sum (fun q _ => Nat.zero_le (n' q)) (Finset.mem_univ q)
    have hz : ∀ q, algebraMap R B (i q) *
        (a ^ N * (c q * a ^ M - ∑ j, A q j • (d j * a ^ (M - m j)))) = 0 := by
      intro q
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (hNle q)
      rw [ht, pow_add, mul_comm (a ^ n' q), mul_assoc, mul_left_comm,
        mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem _ (hi q)) (hn' q), mul_zero]
    refine ⟨N + M, ?_⟩
    have step : ∀ q, a ^ (N + M) * (c q • (g q : B)) =
        ∑ j, algebraMap R B (i q * A q j) * (a ^ N * (d j * a ^ (M - m j))) := by
      intro q
      have h1 := hz q
      rw [← hgi q, smul_eq_mul]
      simp_rw [map_mul, Algebra.smul_def] at h1 ⊢
      rw [mul_sub, mul_sub, sub_eq_zero, Finset.mul_sum, Finset.mul_sum] at h1
      calc a ^ (N + M) * (c q * algebraMap R B (i q))
          = algebraMap R B (i q) * (a ^ N * (c q * a ^ M)) := by ring
        _ = ∑ j, algebraMap R B (i q) * (a ^ N * (algebraMap R B (A q j) * (d j * a ^ (M - m j)))) := h1
        _ = _ := Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.mul_sum, Finset.sum_congr rfl fun q _ => step q, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_mul, ← map_sum, hA j, map_zero, zero_mul]
  have kerAll : ∀ x : B, φ x = 0 → ∃ N : ℕ, a ^ N * x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := kerI x hx
    obtain ⟨N, hN⟩ := core _ hn (by rw [map_mul, hx, mul_zero])
    exact ⟨N + n, by rw [pow_add, mul_assoc, hN]⟩
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    exact (map_pow φ a n).symm ▸ hunit.pow n
  · intro y
    obtain ⟨n, b, hb⟩ := surj y
    exact ⟨(b, ⟨a ^ n, n, rfl⟩), by simpa only [map_pow] using hb⟩
  · intro x y hxy
    obtain ⟨n, hn⟩ := kerAll (x - y) (by rw [map_sub, hxy, sub_self])
    exact ⟨⟨a ^ n, n, rfl⟩, by rw [← sub_eq_zero, ← mul_sub]; exact hn⟩

end GlobalTheory.LiftAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefPow

theorem height_pow (HE : GlobalTheory.Published.ArExists) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {x : X} (hx : IsAlgPt x) (L : HermLB p) (n : ℕ)
    {h h' : X → ℝ} (H : L.IsArithHeight h) (H' : (L.pow n).IsArithHeight h') : h' x = n * h x := by
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  let ht (L : HermLB p) : ℝ := (hex L).choose x
  have hht {L : HermLB p} {h : X → ℝ} (H : L.IsArithHeight h) : ht L = h x :=
    congrFun ((hex L).choose_spec.unique hX H) x
  have hiso {L M : HermLB p} (e : L.Isometric M) : ht L = ht M :=
    (hht (e.isArithHeight hX (hex L).choose_spec)).symm
  have hadd (L M : HermLB p) : ht (L.tens M) = ht L + ht M :=
    PtHtComb.height_tens hX (hex L).choose_spec (hex M).choose_spec (hex _).choose_spec hx
  let F₀ : HermLB.IsomClass p → ℝ := Quotient.lift (s := HermLB.isometrySetoid p) ht fun L M e => hiso e
  let F : HermLB.IsomClass p →+ ℝ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨M⟩
    exact hadd L M)
  have hF (L : HermLB p) : F L.icls = ht L := rfl
  rw [← hht H', ← hht H, ← hF, ← hF, HermLB.icls_pow, map_nsmul, nsmul_eq_mul]

theorem isNef_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (n : ℕ), M.IsNef D → (M.pow n).IsNef D := by
  intro HC k _ X _ p D hX M n N
  have HE := HC.arExists
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨h₀, H₀⟩ := hex (HermLB.triv p)
    have H : (M.pow 0).IsArithHeight h₀ := M.isometric_pow_zero.symm.isArithHeight hX H₀
    have T := (H₀.isNef_iff hX).1 (HermLB.isNef_triv p D)
    exact (H.isNef_iff hX).2 ⟨N.semiPos.pow 0, T.2⟩
  · have : Module.Finite ℤ k := hX.finite
    refine ⟨N.semiPos.pow n, (nefFib_pow_iff k X p hX.isProjOver M n hn).2 N.vertical,
      fun Z i _ _ _ hc hd => ?_⟩
    obtain ⟨h, H⟩ := hex M
    obtain ⟨h', H'⟩ := hex (M.pow n)
    obtain ⟨r, hr⟩ := exists_isRatSec ((M.pow n).restr i).isLB
    obtain ⟨r₀, hr₀, h0⟩ := N.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    rw [← H'.point Z i hc hd r hr, height_pow HE hX (HtSelfInter.isAlgPt_genericPoint i hc hd) M n H H',
      H.point Z i hc hd r₀ hr₀]
    exact mul_nonneg (Nat.cast_nonneg _) h0

example : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (n : ℕ), M.IsNef D → (M.pow n).IsNef D := isNef_pow

end GlobalTheory.NefPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.DivSec

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {e : ℕ}

section Transport

variable {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (h : X ≃ₜ CxPts p σ)

def ChartsAlg : Prop := ∀ j, ∃ c : AlgChart p σ e, A.chart j = h.transOpenPartialHomeomorph c.finChart

variable {A h} (hA : ChartsAlg A h)

def algAtlas : FinHolAtlas e (CxPts p σ) where
  n := A.n
  chart j := (hA j).choose.finChart
  cover y := (A.cover (h.symm y)).imp fun j hj => by
    rw [(hA j).choose_spec, Homeomorph.transOpenPartialHomeomorph_source] at hj
    simpa using hj
  holo _ _ := AlgChart.analyticOnNhd_trans _ _

theorem isAlgAtlas_algAtlas : IsAlgAtlas (algAtlas hA) := fun _ => ⟨_, rfl⟩

theorem chart_eq (j : Fin A.n) :
    A.chart j = h.transOpenPartialHomeomorph ((algAtlas hA).chart j) := (hA j).choose_spec

theorem holoOn_comp_iff {S : Set (CxPts p σ)} {g : CxPts p σ → ℂ} :
    A.HoloOn (h ⁻¹' S) (g ∘ h) ↔ (algAtlas hA).HoloOn S g := by
  refine forall_congr' fun j => ?_
  rw [chart_eq hA j, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Homeomorph.transOpenPartialHomeomorph_target]
  have e1 : (g ∘ h) ∘ (h.symm ∘ ((algAtlas hA).chart j).symm) = g ∘ ((algAtlas hA).chart j).symm := by
    funext v; simp
  have e2 : (h.symm ∘ ((algAtlas hA).chart j).symm) ⁻¹' (h ⁻¹' S) = ((algAtlas hA).chart j).symm ⁻¹' S := by
    ext v; simp
  rw [e1, e2]

theorem smoothOn_comp_iff {S : Set (CxPts p σ)} {g : CxPts p σ → ℝ} :
    A.SmoothOn (h ⁻¹' S) (g ∘ h) ↔ (algAtlas hA).SmoothOn S g := by
  refine forall_congr' fun j => ?_
  rw [chart_eq hA j, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Homeomorph.transOpenPartialHomeomorph_target]
  have e1 : (g ∘ h) ∘ (h.symm ∘ ((algAtlas hA).chart j).symm) = g ∘ ((algAtlas hA).chart j).symm := by
    funext v; simp
  have e2 : (h.symm ∘ ((algAtlas hA).chart j).symm) ⁻¹' (h ⁻¹' S) = ((algAtlas hA).chart j).symm ⁻¹' S := by
    ext v; simp
  rw [e1, e2]

theorem isCompatChart_trans {ψ : OpenPartialHomeomorph (CxPts p σ) (Fin e → ℂ)}
    (hψ : IsCompatChart (algAtlas hA) ψ) : IsCompatChart A (h.transOpenPartialHomeomorph ψ) := fun j => by
  obtain ⟨h1, h2⟩ := hψ j
  rw [chart_eq hA j]
  simp only [Homeomorph.transOpenPartialHomeomorph_symm_apply, Homeomorph.transOpenPartialHomeomorph_apply,
    Homeomorph.transOpenPartialHomeomorph_target, Homeomorph.transOpenPartialHomeomorph_source]
  constructor
  · have e1 : (ψ ∘ h) ∘ (h.symm ∘ ((algAtlas hA).chart j).symm) = ψ ∘ ((algAtlas hA).chart j).symm := by
      funext v; simp
    have e2 : (h.symm ∘ ((algAtlas hA).chart j).symm) ⁻¹' (h ⁻¹' ψ.source) =
        ((algAtlas hA).chart j).symm ⁻¹' ψ.source := by
      ext v; simp
    rw [e1, e2]; exact h1
  · have e1 : (((algAtlas hA).chart j) ∘ h) ∘ (h.symm ∘ ψ.symm) = ((algAtlas hA).chart j) ∘ ψ.symm := by
      funext v; simp
    have e2 : (h.symm ∘ ψ.symm) ⁻¹' (h ⁻¹' ((algAtlas hA).chart j).source) =
        ψ.symm ⁻¹' ((algAtlas hA).chart j).source := by
      ext v; simp
    rw [e1, e2]; exact h2

theorem isPotential_pullback {L : LocPot (CxPts p σ)} (hL : IsPotential (algAtlas hA) L) :
    IsPotential A (L.pullback h h.continuous) := by
  refine ⟨fun x => (smoothOn_comp_iff hA).2 (hL.1 (h x)), fun x x' y hy => ?_⟩
  obtain ⟨W, hW, hyW, G, hG, e⟩ := hL.2 (h x) (h x') (h y) hy
  refine ⟨h ⁻¹' W, hW.preimage h.continuous, hyW, G ∘ h, (holoOn_comp_iff hA).2 hG, fun z hz => ?_⟩
  exact e (h z) ⟨⟨hz.1.1, hz.1.2⟩, hz.2⟩

theorem isSection_pullback {L : LocPot (CxPts p σ)} {s : CxPts p σ → CxPts p σ → ℂ}
    (hs : IsSection (algAtlas hA) L s) :
    IsSection A (L.pullback h h.continuous) (fun x z => s (h x) (h z)) :=
  ⟨fun x => (holoOn_comp_iff hA (g := s (h x))).2 (hs.1 (h x)),
    fun x x' y hy => hs.2 (h x) (h x') (h y) hy⟩

theorem isSNC_pullback {L : LocPot (CxPts p σ)} {s : CxPts p σ → CxPts p σ → ℂ} {r : ℕ} {m : Fin r → ℕ}
    {W : Fin r → Set (CxPts p σ)} (hs : IsSNC (algAtlas hA) L s m W) :
    IsSNC A (L.pullback h h.continuous) (fun x z => s (h x) (h z)) m (fun k => h ⁻¹' W k) := fun x => by
  obtain ⟨ψ, hc, hx, hsub, τ, hinj, hW, u, hu, hu0, he⟩ := hs (h x)
  refine ⟨h.transOpenPartialHomeomorph ψ, isCompatChart_trans hA hc, hx, fun z hz => hsub hz, τ, hinj,
    fun k => ?_, u ∘ h, ?_, fun z hz => hu0 (h z) hz, fun z hz => he (h z) hz⟩
  · ext z
    have := Set.ext_iff.1 (hW k) (h z)
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using this
  · have := (holoOn_comp_iff hA (S := ψ.source) (g := u)).2 hu
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using this

end Transport

section Data

variable {d m : ℕ} {R : AnRead p σ d} {C : Fin m → Closeds Y} {n : Fin m → CxPts p σ → ℝ}
  (hn : ∀ i, IsDivNorm R (C i) (n i))

def eqV (i : Fin m) (y : CxPts p σ) : Y.affineOpens := ((hn i).2 y).choose

def eqT (i : Fin m) (y : CxPts p σ) : Γ(Y, (eqV hn i y).1) := ((hn i).2 y).choose_spec.choose

def eqF (i : Fin m) (y : CxPts p σ) : CxPts p σ → ℝ := ((hn i).2 y).choose_spec.choose_spec.choose

theorem eq_spec (i : Fin m) (y : CxPts p σ) :
    y ∈ ptsIn p σ (eqV hn i y).1 ∧
      (Scheme.IdealSheafData.vanishingIdeal (C i)).ideal (eqV hn i y) = Ideal.span {eqT hn i y} ∧
      R.SmoothOn (ptsIn p σ (eqV hn i y).1) (eqF hn i y) ∧
      ∀ z ∈ ptsIn p σ (eqV hn i y).1, n i z ^ 2 = ‖ev p σ (eqV hn i y).1 (eqT hn i y) z‖ ^ 2 * Real.exp (-eqF hn i y z) :=
  ((hn i).2 y).choose_spec.choose_spec.choose_spec

def divPot : LocPot (CxPts p σ) where
  U y := ⋂ i, ptsIn p σ (eqV hn i y).1
  isOpen_U y := isOpen_iInter_of_finite fun i => isOpen_ptsIn _
  mem_U y := Set.mem_iInter.2 fun i => (eq_spec hn i y).1
  φ y z := ∑ i, eqF hn i y z / 2

def divSec (y z : CxPts p σ) : ℂ := ∏ i, ev p σ (eqV hn i y).1 (eqT hn i y) z

theorem mem_eqV {y z : CxPts p σ} (hz : z ∈ (divPot hn).U y) (i : Fin m) : z ∈ ptsIn p σ (eqV hn i y).1 :=
  Set.mem_iInter.1 hz i

theorem norm_divSec_mul {y z : CxPts p σ} (hz : z ∈ (divPot hn).U y) :
    ‖divSec hn y z‖ * Real.exp (-(divPot hn).φ y z) = ∏ i, n i z := by
  have h1 : ∀ i, n i z = ‖ev p σ (eqV hn i y).1 (eqT hn i y) z‖ * Real.exp (-eqF hn i y z / 2) := fun i => by
    have e := (eq_spec hn i y).2.2.2 z (mem_eqV hn hz i)
    have h0 := ((hn i).1 z).1
    have hx : Real.exp (-eqF hn i y z) = Real.exp (-eqF hn i y z / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hx, ← mul_pow] at e
    exact (pow_left_inj₀ h0 (by positivity) two_ne_zero).1 e
  simp only [divSec, divPot, norm_prod, h1]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem divSec_eq_zero_iff (y : CxPts p σ) : divSec hn y y = 0 ↔ ∃ i, LiesIn y (C i) := by
  simp only [divSec, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  exact exists_congr fun i => ev_eq_zero_iff (eq_spec hn i y).2.1 (eq_spec hn i y).1

end Data

section Sec

variable {d m : ℕ} {R : AnRead p σ d} {C : Fin m → Closeds Y} {n : Fin m → CxPts p σ → ℝ}
  (hn : ∀ i, IsDivNorm R (C i) (n i))

theorem holoOn_divSec (y : CxPts p σ) : R.HoloOn ((divPot hn).U y) (divSec hn y) := fun j => by
  have h : ∀ i, DifferentiableOn ℂ
      (fun v => ev p σ (eqV hn i y).1 (eqT hn i y) ((R.chart j).e.symm v))
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' (divPot hn).U y) := fun i =>
    (R.holoOn_ev _ (eqT hn i y) j).mono fun v hv => ⟨hv.1, mem_eqV hn hv.2 i⟩
  have key : ∀ s : Finset (Fin m), DifferentiableOn ℂ
      (fun v => ∏ i ∈ s, ev p σ (eqV hn i y).1 (eqT hn i y) ((R.chart j).e.symm v))
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' (divPot hn).U y) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using differentiableOn_const (1 : ℂ)
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h a).mul ih
  refine (key Finset.univ).congr fun v _ => ?_
  simp [divSec]

theorem isSection_divSec {B : FinHolAtlas d (CxPts p σ)} (hB : IsAlgAtlas B) :
    IsSection B (divPot hn) (divSec hn) :=
  ⟨fun y => (hB.holoOn_iff R ((divPot hn).isOpen_U y)).2 (holoOn_divSec hn y),
    fun _ _ _ hz => by rw [norm_divSec_mul hn hz.1, norm_divSec_mul hn hz.2]⟩

end Sec

end GlobalTheory.DivSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialTransportHomeomorph
section
namespace PotentialityTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.CarriedPot

theorem isPotential_tAtlas_pullback : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : LocPot X), IsPotential A P →
      IsPotential (tAtlas A h) (P.pullback h.symm h.symm.continuous) := by
  intro e X X' _ _ A h P hP
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have hs := hP.1 (h.symm x) j
    have e₁ : (P.pullback h.symm h.symm.continuous).φ x ∘ ((tAtlas A h).chart j).symm =
        P.φ (h.symm x) ∘ (A.chart j).symm := funext fun w => by
      simp only [Function.comp_apply, tAtlas_symm, LocPot.pullback, Homeomorph.symm_apply_apply]
    have e₂ : ((tAtlas A h).chart j).target ∩ ((tAtlas A h).chart j).symm ⁻¹'
          (P.pullback h.symm h.symm.continuous).U x =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U (h.symm x) := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage, tAtlas_target, tAtlas_symm, LocPot.pullback,
        Homeomorph.symm_apply_apply]
    rw [e₁, e₂]
    exact hs
  · obtain ⟨W, hW, hyW, G, hG, hd⟩ := hP.2 (h.symm x) (h.symm x') (h.symm y) hy
    refine ⟨h.symm ⁻¹' W, hW.preimage h.symm.continuous, hyW, G ∘ h.symm, fun j => ?_, fun z hz => ?_⟩
    · have hs := hG j
      have e₁ : (G ∘ h.symm) ∘ ((tAtlas A h).chart j).symm = G ∘ (A.chart j).symm := funext fun w => by
        simp only [Function.comp_apply, tAtlas_symm, Homeomorph.symm_apply_apply]
      have e₂ : ((tAtlas A h).chart j).target ∩ ((tAtlas A h).chart j).symm ⁻¹' (h.symm ⁻¹' W) =
          (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_preimage, tAtlas_target, tAtlas_symm,
          Homeomorph.symm_apply_apply]
      rw [e₁, e₂]
      exact hs
    · exact hd (h.symm z) hz

end GlobalTheory.CompanionTheory.CarriedPot

end

end PotentialityTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.isPotential_transport_homeomorph : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : LocPot X), IsPotential A P → IsPotential (tAtlas A h) (P.pullback h.symm h.symm.continuous) := by
  first | exact @PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback | exact PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback | (intros; apply PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedComplexPointsOpenVarietyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreconnected_complexPoints_open_variety : ∀ (F : Type) [Field F] [NumberField F] (B : GlobalTheory.ProjVar.Var F) (e : F →+* ℂ) (W : B.X.Opens), IsPreconnected (GlobalTheory.CxPts.ptsIn B.str e W) := by
  first | exact @GlobalTheory.CxConn.isPreconnected_ptsIn | exact GlobalTheory.CxConn.isPreconnected_ptsIn | (intros; apply GlobalTheory.CxConn.isPreconnected_ptsIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfThetaConstantsAndFirstJetsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ : I → K) (J : I → Fin g → K), ThJet x hg m pt ϑ J → IsThetaPt x.P m pt fun i => fnOf (ϑ i) := by
  first | exact @GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet | exact GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet | (intros; apply GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet <;> assumption)
end

