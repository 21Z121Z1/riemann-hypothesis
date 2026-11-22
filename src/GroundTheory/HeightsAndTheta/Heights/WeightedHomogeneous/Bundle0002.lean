import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField Matrix
open scoped ComplexOrder

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def latticeDual {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K) (Fin m → K) where
  carrier := {φ | ∀ v ∈ L, φ ⬝ᵥ v ∈ Set.range (algebraMap (𝓞 K) K)}
  add_mem' := by
    intro φ ψ hφ hψ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    obtain ⟨b, hb⟩ := hψ v hv
    exact ⟨a + b, by rw [map_add, ha, hb, add_dotProduct]⟩
  zero_mem' := fun v _ ↦ ⟨0, by rw [map_zero, zero_dotProduct]⟩
  smul_mem' := by
    intro c φ hφ v hv
    obtain ⟨a, ha⟩ := hφ v hv
    exact ⟨c * a, by rw [map_mul, ha, smul_dotProduct, Algebra.smul_def]⟩

structure IsDualBasis {m N : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (φ : Fin (N + 1) → Fin m → K) : Prop where
  independent : LinearIndependent ℤ φ
  span_eq : Submodule.span ℤ (Set.range φ) = (latticeDual L).restrictScalars ℤ

def latticeForm {m : ℕ} (φ : Fin m → K) : MvPolynomial (Fin m) K := ∑ j, C (φ j) * X j

def latticeMap {m N : ℕ} (φ : Fin (N + 1) → Fin m → K) :
    MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ →+* MvPolynomial (Fin m) K :=
  eval₂Hom (Int.castRingHom _) fun v ↦ latticeForm (φ v.2)

def latticeIdeal {m N : ℕ} (φ : Fin (N + 1) → Fin m → K) :
    Ideal (MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ) :=
  RingHom.ker (latticeMap φ)

abbrev LatticeField (K : Type*) [Field K] (r : ℕ) : Type _ := FractionRing (MvPolynomial (Fin r) K)

def latticeCoord {r N : ℕ} (φ : Fin (N + 1) → Fin (r + 1) → K) :
    Coord (fun _ : Unit ↦ N) → LatticeField K r :=
  fun v ↦ algebraMap (MvPolynomial (Fin r) K) (LatticeField K r)
    (C (φ v.2 0) + ∑ j : Fin r, C (φ v.2 j.succ) * X j)

def latticePoint {R : Type*} [CommRing R] {m N : ℕ} (φ : Fin (N + 1) → Fin m → K) (σ : K →+* R)
    (w : Fin m → R) : Cone (fun _ : Unit ↦ N) R :=
  fun _ b ↦ ∑ j, σ (φ b j) * w j

def LatticeMetricAgrees {r N : ℕ} (φ : Fin (N + 1) → Fin (r + 1) → K) (F : HermLattice K (r + 1))
    (A : HermLine (fun _ : Unit ↦ N)) : Prop :=
  ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
    A.metric (latticePoint φ σ w) = Real.sqrt (star w ⬝ᵥ (F.metric σ *ᵥ w)).re

def oneBlockForms {e r : ℕ} (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    Fin (oneBlockSize e r + 1) → Fin (r + 1) → K :=
  fun p ↦ Pi.single (oneBlockIndex e r p).2 ((om (oneBlockIndex e r p).1 : 𝓞 K) : K)

theorem linearIndependent_int_single (m : ℕ) :
    LinearIndependent ℤ (fun j : Fin m ↦ (Pi.single j (1 : ℚ) : Fin m → ℚ)) := by
  have h : LinearIndependent ℚ (fun j : Fin m ↦ (Pi.single j (1 : ℚ) : Fin m → ℚ)) := by
    have e : (fun j : Fin m ↦ (Pi.single j (1 : ℚ) : Fin m → ℚ)) = ⇑(Pi.basisFun ℚ (Fin m)) := by
      funext j
      exact (Pi.basisFun_apply _ _ j).symm
    rw [e]
    exact (Pi.basisFun ℚ (Fin m)).linearIndependent
  exact h.restrict_scalars' ℤ

theorem ratStandard_isDualBasis (r : ℕ) :
    IsDualBasis (HermLattice.standard ℚ (r + 1)).lattice
      (fun j : Fin (r + 1) ↦ (Pi.single j (1 : ℚ) : Fin (r + 1) → ℚ)) := by
  refine ⟨linearIndependent_int_single _, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩ v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨if j = i then 1 else 0, ?_⟩
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, dotProduct_add]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨c * a, by rw [map_mul, ha, dotProduct_smul, Algebra.smul_def]⟩
  · intro φ hφ
    have hj : ∀ j, ∃ a : ℤ, φ j = a := by
      intro j
      obtain ⟨a, ha⟩ := hφ (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)
      refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
      have h1 : φ ⬝ᵥ (Pi.single j 1 : Fin (r + 1) → ℚ) = φ j := by simp
      rw [← h1, ← ha]
      have := (Rat.ringOfIntegersEquiv.symm_apply_apply a)
      conv_lhs => rw [← this]
      simp
    choose a ha using hj
    have hsum : φ = ∑ j, a j • (Pi.single j (1 : ℚ) : Fin (r + 1) → ℚ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply, ha]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem ratStandard_latticeMetricAgrees (r : ℕ) :
    LatticeMetricAgrees (fun j : Fin (r + 1) ↦ (Pi.single j (1 : ℚ) : Fin (r + 1) → ℚ))
      (HermLattice.standard ℚ (r + 1)) (HermLine.standard (fun _ : Unit ↦ r)) := by
  intro σ w _
  change ∏ _u : Unit, l2Norm (latticePoint _ σ w ()) =
    Real.sqrt (star w ⬝ᵥ ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) *ᵥ w)).re
  rw [Fintype.prod_unique, l2Norm, one_mulVec]
  congr 1
  have h1 : ∀ p, latticePoint (fun j : Fin (r + 1) ↦ (Pi.single j (1 : ℚ) : Fin (r + 1) → ℚ)) σ w () p =
      w p := by
    intro p
    simp [latticePoint, Pi.single_apply]
  simp only [h1]
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

def ratDoubled (r : ℕ) : HermLattice ℚ (r + 1) where
  lattice := Submodule.span (𝓞 ℚ) (Set.range fun j : Fin (r + 1) ↦ (Pi.single j 2 : Fin (r + 1) → ℚ))
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq := by
    rw [Submodule.span_span_of_tower, eq_top_iff]
    intro v _
    have hv : v = ∑ j, (v j / 2) • (Pi.single j 2 : Fin (r + 1) → ℚ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  metric := fun _ ↦ 1
  posDef := fun _ ↦ Matrix.PosDef.one
  conj := fun _ ↦ by simp

theorem ratDoubled_isDualBasis (r : ℕ) :
    IsDualBasis (ratDoubled r).lattice
      (fun j : Fin (r + 1) ↦ (Pi.single j (1 / 2 : ℚ) : Fin (r + 1) → ℚ)) := by
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrFun hg i
    simpa [Finset.sum_apply, Pi.single_apply] using this
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩ v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨if j = i then 1 else 0, ?_⟩
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, dotProduct_add]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨c * a, by rw [map_mul, ha, dotProduct_smul, Algebra.smul_def]⟩
  · intro φ hφ
    have hj : ∀ j, ∃ a : ℤ, φ j = a / 2 := by
      intro j
      obtain ⟨a, ha⟩ := hφ (Pi.single j 2) (Submodule.subset_span ⟨j, rfl⟩)
      refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
      have h1 : φ ⬝ᵥ (Pi.single j 2 : Fin (r + 1) → ℚ) = φ j * 2 := by simp
      have h2 : algebraMap (𝓞 ℚ) ℚ a = (Rat.ringOfIntegersEquiv a : ℤ) := by
        have := Rat.ringOfIntegersEquiv.symm_apply_apply a
        conv_lhs => rw [← this]
        simp
      rw [h1, h2] at ha
      linarith
    choose a ha using hj
    have hsum : φ = ∑ j, a j • (Pi.single j (1 / 2 : ℚ) : Fin (r + 1) → ℚ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply, ha, div_eq_mul_inv]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem ratDoubled_latticeMetricAgrees (r : ℕ) :
    LatticeMetricAgrees (fun j : Fin (r + 1) ↦ (Pi.single j (1 / 2 : ℚ) : Fin (r + 1) → ℚ))
      (ratDoubled r) ((HermLine.standard (fun _ : Unit ↦ r)).scale 2 two_pos) := by
  intro σ w _
  change 2 * ∏ _u : Unit, l2Norm (latticePoint _ σ w ()) =
    Real.sqrt (star w ⬝ᵥ ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) *ᵥ w)).re
  have h1 : latticePoint (fun j : Fin (r + 1) ↦ (Pi.single j (1 / 2 : ℚ) : Fin (r + 1) → ℚ)) σ w () =
      fun p ↦ (1 / 2 : ℂ) * w p := by
    funext p
    have h0 : σ (1 / 2) = 1 / 2 := by
      rw [eq_ratCast σ (1 / 2)]
      norm_num
    change ∑ j, σ ((Pi.single p (1 / 2 : ℚ) : Fin (r + 1) → ℚ) j) * w j = _
    rw [Finset.sum_eq_single p (fun j _ hj ↦ by simp [hj]) (by simp),
      Pi.single_eq_same, h0]
  rw [Fintype.prod_unique, h1, vectorL2Norm_const_mul, one_mulVec]
  have h2 : l2Norm w = Real.sqrt (star w ⬝ᵥ w).re := by
    rw [l2Norm]
    congr 1
    rw [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [← h2]
  simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

def funFieldEquiv (P : ArithVariety n) : P.FunField ≃+* FunField P :=
  (IsLocalization.algEquiv (nonZeroDivisors (CoordRing P)) P.FunField (FunField P)).toRingEquiv

omit [Fintype ι] in
theorem funFieldEquiv_algebraMap (P : ArithVariety n) (r : CoordRing P) :
    funFieldEquiv P (algebraMap (CoordRing P) P.FunField r) =
      algebraMap (CoordRing P) (FunField P) r :=
  (IsLocalization.algEquiv (nonZeroDivisors (CoordRing P)) P.FunField (FunField P)).commutes r

omit [Fintype ι] in

theorem funFieldEquiv_mkF (P : ArithVariety n) (f : MvPolynomial (Coord n) ℤ) :
    funFieldEquiv P (P.mkF f) = val P f :=
  funFieldEquiv_algebraMap P _

omit [Fintype ι] in

theorem funFieldEquiv_mkF_X (P : ArithVariety n) (v : Coord n) :
    funFieldEquiv P (P.mkF (X v)) = genPt P v :=
  funFieldEquiv_mkF P _

omit [Fintype ι] in

theorem funFieldEquiv_chartCoord (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (v : Coord n) :
    funFieldEquiv P (P.chartCoord c v) = genPt P v / genPt P ⟨v.1, c v.1⟩ := by
  rw [ArithVariety.chartCoord, map_div₀, funFieldEquiv_mkF_X, funFieldEquiv_mkF_X]

omit [Fintype ι] in

theorem funFieldEquiv_image_chartRing (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) :
    funFieldEquiv P '' (P.chartRing c : Set P.FunField) = (chartRing P c : Set (FunField P)) := by
  have hmap := RingHom.map_closure (funFieldEquiv P).toRingHom (Set.range (P.chartCoord c))
  have hrange : (funFieldEquiv P).toRingHom '' Set.range (P.chartCoord c) =
      Set.range fun p : Coord n ↦ genPt P p / genPt P ⟨p.1, c p.1⟩ := by
    rw [← Set.range_comp]
    congr 1
    funext v
    exact funFieldEquiv_chartCoord P c v
  rw [hrange] at hmap
  rw [chartRing, ReciprocityTheory.ChartRestriction.G.Geo.chartRingZ, Algebra.adjoin_int, ← hmap]
  rfl

omit [Fintype ι] in

theorem funFieldEquiv_mem_chartRing_iff (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1))
    (x : P.FunField) : funFieldEquiv P x ∈ chartRing P c ↔ x ∈ P.chartRing c := by
  rw [← SetLike.mem_coe, ← funFieldEquiv_image_chartRing]
  exact (funFieldEquiv P).injective.mem_set_image

theorem funFieldEquiv_chartPow (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) :
    funFieldEquiv P (P.chartPow c a) = chartPow P c a := by
  rw [ArithVariety.chartPow, chartPow, map_prod]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [map_zpow₀, funFieldEquiv_mkF_X]

theorem chartPow_neg (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) :
    chartPow P c (-a) = (chartPow P c a)⁻¹ := by
  rw [chartPow, chartPow, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [Pi.neg_apply, zpow_neg]

theorem funFieldEquiv_div_chartPow (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ)
    (x : P.FunField) :
    funFieldEquiv P (x / P.chartPow c a) = funFieldEquiv P x * chartPow P c (-a) := by
  rw [map_div₀, funFieldEquiv_chartPow, chartPow_neg, div_eq_mul_inv]

omit [Fintype ι] in

theorem isOfDegree_iff (P : ArithVariety n) (a : ι → ℤ) (x : P.FunField) :
    P.IsOfDegree a x ↔ IsHomogOfDeg P a (funFieldEquiv P x) := by
  constructor
  · rintro ⟨f, g, df, dg, hf, hg, hd, hgP, hx⟩
    refine ⟨f, g, df, dg, hf, hg, hgP, hd, ?_⟩
    rw [hx, map_div₀, funFieldEquiv_mkF, funFieldEquiv_mkF]
  · rintro ⟨f, g, df, dg, hf, hg, hgP, hd, hx⟩
    refine ⟨f, g, df, dg, hf, hg, hd, hgP, (funFieldEquiv P).injective ?_⟩
    rw [hx, map_div₀, funFieldEquiv_mkF, funFieldEquiv_mkF]

def GenSystem.ofIsHomogGenerators {P : ArithVariety n} {r : ℕ}
    {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ} (h : P.IsHomogGenerators G δ) :
    GenSystem P where
  r := r
  f := G
  δ := δ
  homog := h.homog
  span_eq := h.span_eq

omit [Fintype ι] in

theorem GenSystem.isHomogGenerators {P : ArithVariety n} (Γ : GenSystem P) :
    P.IsHomogGenerators Γ.f Γ.δ :=
  ⟨Γ.homog, Γ.span_eq⟩

def genSystemEquiv (P : ArithVariety n) :
    GenSystem P ≃ Σ r : ℕ, {p : (Fin r → MvPolynomial (Coord n) ℤ) × (Fin r → ι → ℕ) //
      P.IsHomogGenerators p.1 p.2} where
  toFun Γ := ⟨Γ.r, (Γ.f, Γ.δ), Γ.isHomogGenerators⟩
  invFun p := GenSystem.ofIsHomogGenerators p.2.2
  left_inv _ := rfl
  right_inv _ := rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

