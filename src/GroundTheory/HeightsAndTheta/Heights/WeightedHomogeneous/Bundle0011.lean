import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PAddHeightsridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace AddBlockBridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false

abbrev ConeField (ι Ω : Type) [Field Ω] : Type := FractionRing (MvPolynomial ι Ω)

def constMap (ι : Type) : Ω →+* ConeField ι Ω :=
  (algebraMap (MvPolynomial ι Ω) (ConeField ι Ω)).comp C

theorem constMap_injective : Function.Injective (constMap (Ω := Ω) ι) :=
  (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω)).comp (C_injective _ _)

def varT (k : ι) : ConeField ι Ω := algebraMap (MvPolynomial ι Ω) (ConeField ι Ω) (X k)

theorem varT_ne_zero (k : ι) : varT (Ω := Ω) k ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω))).mpr (X_ne_zero k)

def coneHom (y : Coord n → Ω) : MvPolynomial (Coord n) ℤ →+* ConeField ι Ω :=
  (algebraMap (MvPolynomial ι Ω) (ConeField ι Ω)).comp (Geo.mConeMap (ι := blockIdx n) y).toRingHom

theorem coneHom_apply (y : Coord n → Ω) (f : MvPolynomial (Coord n) ℤ) :
    coneHom y f = algebraMap (MvPolynomial ι Ω) (ConeField ι Ω) (Geo.mConeMap (ι := blockIdx n) y f) := rfl

theorem coneHom_X (y : Coord n → Ω) (v : Coord n) : coneHom y (X v) = constMap ι (y v) * varT v.1 := by
  rw [coneHom_apply]
  simp [Geo.mConeMap, constMap, varT]

theorem mem_mCoordIdeal_iff (y : Coord n → Ω) (f : MvPolynomial (Coord n) ℤ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ coneHom y f = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, coneHom_apply,
    map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω))]

theorem coneHom_of_homog (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    coneHom y f = constMap ι (aeval y f) * ∏ k, varT k ^ δ k := by
  have h1 : Geo.mConeMap (ι := blockIdx n) y f =
      eval₂ (Int.castRingHom (MvPolynomial ι Ω)) (fun v : Coord n ↦ X v.1 * C (y v)) f := by
    simp only [Geo.mConeMap, aeval_def]
    congr 1
    funext v
    exact mul_comm _ _
  have h2 : (C (aeval y f) : MvPolynomial ι Ω) =
      eval₂ (Int.castRingHom (MvPolynomial ι Ω)) (fun v : Coord n ↦ C (y v)) f := by
    rw [aeval_def, algebraMap_int_eq, eval₂_comp_left]
    congr 1
  rw [coneHom_apply, h1, eval₂_scale_of_isWeightedHomogeneous (fun k ↦ (X k : MvPolynomial ι Ω)) _ hf, ← h2,
    mul_comm, map_mul, map_prod]
  simp only [map_pow]
  rfl

variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)

def coordHom : P.CoordRing →+* ConeField ι Ω :=
  Ideal.Quotient.lift P.ideal (coneHom y) fun f hf ↦ by
    rw [hP] at hf
    exact (mem_mCoordIdeal_iff y f).mp hf

theorem coordHom_injective : Function.Injective (coordHom P y hP) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ fun f hf ↦ by
    rw [hP]
    exact (mem_mCoordIdeal_iff y f).mpr (RingHom.mem_ker.mp hf)

def funHom : P.FunField →+* ConeField ι Ω := IsFractionRing.lift (coordHom_injective P y hP)

theorem funHom_mkF (f : MvPolynomial (Coord n) ℤ) : funHom P y hP (P.mkF f) = coneHom y f := by
  simp only [funHom, ArithVariety.mkF, RingHom.comp_apply, IsFractionRing.lift_algebraMap, coordHom,
    Ideal.Quotient.lift_mk]

include hP in

theorem ne_zero_of_isLive {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) : y ⟨k, c k⟩ ≠ 0 := by
  intro hy
  apply hc k
  rw [hP, mem_mCoordIdeal_iff, coneHom_X, hy, map_zero, zero_mul]

theorem funHom_chartCoord (c : (k : ι) → Fin (n k + 1)) (v : Coord n) :
    funHom P y hP (P.chartCoord c v) = constMap ι (y v / y ⟨v.1, c v.1⟩) := by
  rw [ArithVariety.chartCoord, map_div₀, funHom_mkF, funHom_mkF, coneHom_X, coneHom_X, map_div₀,
    mul_div_mul_right _ _ (varT_ne_zero v.1)]

theorem funHom_chartPow (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) :
    funHom P y hP (P.chartPow c a) = (∏ k, constMap ι (y ⟨k, c k⟩) ^ a k) * ∏ k, varT k ^ a k := by
  rw [ArithVariety.chartPow, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [map_zpow₀, funHom_mkF, coneHom_X, mul_zpow]

theorem exists_chartRing (c : (k : ι) → Fin (n k + 1)) {r : Ω}
    (hr : r ∈ Geo.chartRingZ (ι := blockIdx n) y c) :
    ∃ η ∈ P.chartRing c, funHom P y hP η = constMap ι r := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨P.chartCoord c p, Subring.subset_closure ⟨p, rfl⟩, funHom_chartCoord P y hP c p⟩
  | algebraMap z =>
    exact ⟨(z : P.FunField), intCast_mem _ z, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨η, hη, he⟩ := hx
    obtain ⟨η', hη', he'⟩ := hx'
    exact ⟨η + η', add_mem hη hη', by rw [map_add, map_add, he, he']⟩
  | mul x x' _ _ hx hx' =>
    obtain ⟨η, hη, he⟩ := hx
    obtain ⟨η', hη', he'⟩ := hx'
    exact ⟨η * η', mul_mem hη hη', by rw [map_mul, map_mul, he, he']⟩

theorem funHom_of_reads {a : ι → ℤ} (t : IntegralSection P a) {s : Ω} (ht : P.Reads y a s t.toFun) :
    funHom P y hP t.toFun = constMap ι s * ∏ k, varT k ^ a k := by
  have hden : P.mkF t.den ≠ 0 := fun h ↦ t.den_not_mem ((P.mkF_eq_zero_iff _).mp h)
  have hnum : P.mkF t.num = t.toFun * P.mkF t.den := by
    rw [IntegralSection.toFun, div_mul_cancel₀ _ hden]
  have hval : aeval y t.num = s * aeval y t.den :=
    (ht t.num t.den t.numDeg t.denDeg t.num_isHomogeneous t.den_isHomogeneous
      (fun k ↦ by have := t.deg_eq k; omega)).mpr hnum
  have hden' : funHom P y hP (P.mkF t.den) ≠ 0 := (map_ne_zero_iff _ (funHom P y hP).injective).mpr hden
  rw [funHom_mkF, coneHom_of_homog y t.den_isHomogeneous] at hden'
  have hc : constMap ι (aeval y t.den) ≠ 0 := left_ne_zero_of_mul hden'
  have hp : ∏ k, varT (Ω := Ω) k ^ t.denDeg k ≠ 0 := right_ne_zero_of_mul hden'
  have hPa : ∏ k, varT (Ω := Ω) k ^ a k = (∏ k, varT k ^ t.numDeg k) / ∏ k, varT k ^ t.denDeg k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← t.deg_eq k, zpow_sub₀ (varT_ne_zero k), zpow_natCast, zpow_natCast]
  rw [IntegralSection.toFun, map_div₀, funHom_mkF, funHom_mkF, coneHom_of_homog y t.num_isHomogeneous,
    coneHom_of_homog y t.den_isHomogeneous, hval, map_mul, hPa]
  field_simp

end AddBlockBridge

theorem AddBlockBridge.scale_injective {σ L : Type} [Field L] (w : σ → L) (hw : ∀ o, w o ≠ 0) :
    Function.Injective (aeval fun o ↦ C (w o) * X o : MvPolynomial σ L →ₐ[L] MvPolynomial σ L) := by
  have h : ((aeval fun o ↦ C (w o)⁻¹ * X o : MvPolynomial σ L →ₐ[L] MvPolynomial σ L).comp
      (aeval fun o ↦ C (w o) * X o)) = AlgHom.id L _ := by
    refine algHom_ext fun o ↦ ?_
    simp only [AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hw o), C_1, one_mul]
  exact Function.LeftInverse.injective (g := aeval fun o ↦ C (w o)⁻¹ * X o) fun p ↦ by
    simpa using congrArg (fun φ ↦ φ p) h

open AddBlockBridge in

theorem AddBlockBridge.proof (hCLS : ChartLatSection.Statement) : AddBlockBridge.Statement := by
  intro ι _ _ n Ω _ y P a m x' hP hx' hgen
  have hsec : ∀ j, ∃ t : IntegralSection P a, P.Reads y a (x' j) t.toFun := fun j ↦ by
    obtain ⟨t, ht⟩ := (hCLS ι n Ω y P a 1 (x' j) hP).mp (hx' j)
    refine ⟨t.cast (one_smul ℕ a), ?_⟩
    rw [show P.Reads y a = P.Reads y ((1 : ℕ) • a) by rw [one_smul]]
    exact ht
  choose t ht using hsec
  have hval : ∀ j, funHom P y hP (t j).toFun = constMap ι (x' j) * ∏ k, varT k ^ a k :=
    fun j ↦ funHom_of_reads P y hP (t j) (ht j)

  have hquot : ∀ c, P.IsLive c → ∀ j, funHom P y hP ((t j).toFun / P.chartPow c a) =
      constMap ι (x' j * ∏ k, y ⟨k, c k⟩ ^ (-a k)) := by
    intro c hc j
    have hy : ∀ k, constMap ι (y ⟨k, c k⟩) ≠ 0 := fun k ↦
      (map_ne_zero_iff _ constMap_injective).mpr (ne_zero_of_isLive P y hP hc k)
    have hT : ∏ k, varT (Ω := Ω) k ^ a k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (varT_ne_zero k)
    have hY : ∏ k, constMap ι (y ⟨k, c k⟩) ^ a k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hy k)
    have e : ∏ k, constMap ι (y ⟨k, c k⟩ ^ (-a k)) = (∏ k, constMap ι (y ⟨k, c k⟩) ^ a k)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [map_zpow₀, zpow_neg]
    rw [map_div₀, hval, funHom_chartPow, map_mul, map_prod, e]
    field_simp
  have hmem : ∀ c, P.IsLive c → ∀ j, (t j).toFun / P.chartPow c a ∈ P.chartRing c := by
    intro c hc j
    have hm := hx' j c (ne_zero_of_isLive P y hP hc)
    simp only [Nat.cast_one, one_mul] at hm
    obtain ⟨η, hη, he⟩ := exists_chartRing P y hP c hm
    rwa [(funHom P y hP).injective ((hquot c hc j).trans he.symm)]
  have hgen' : ∀ c, P.IsLive c → ∃ u : Fin (m + 1) → P.FunField, (∀ j, u j ∈ P.chartRing c) ∧
      ∑ j, u j * ((t j).toFun / P.chartPow c a) = 1 := by
    intro c hc
    obtain ⟨u, hu, hsum⟩ := hgen c (ne_zero_of_isLive P y hP hc)
    choose v hv hve using fun j ↦ exists_chartRing P y hP c (hu j)
    refine ⟨v, hv, (funHom P y hP).injective ?_⟩
    rw [map_sum, map_one, ← map_one (constMap (Ω := Ω) ι), ← hsum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_mul, hve j, hquot c hc j]
  let D : AddBlockData P :=
    { deg := a
      size := m
      elt := fun j ↦ (t j).toFun
      elt_deg := fun j ↦ ⟨(t j).num, (t j).den, (t j).numDeg, (t j).denDeg, (t j).num_isHomogeneous,
        (t j).den_isHomogeneous, (t j).deg_eq, (t j).den_not_mem, rfl⟩
      chart_mem := hmem
      generating := hgen' }

  let w : Option ι → ConeField ι Ω := fun o ↦ o.elim (∏ k, varT k ^ a k) varT
  have hw : ∀ o, w o ≠ 0 := by
    rintro (_ | k)
    · exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (varT_ne_zero k)
    · exact varT_ne_zero k
  let σ : MvPolynomial (Option ι) (ConeField ι Ω) →ₐ[ConeField ι Ω] MvPolynomial (Option ι) (ConeField ι Ω) :=
    aeval fun o ↦ C (w o) * X o
  have hcomp : (map (funHom P y hP)).comp D.extMap = σ.toRingHom.comp
      ((map (constMap ι)).comp (Geo.mConeMap (ι := blockIdx D.extSizes) (D.plusCoord y x')).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) fun v ↦ ?_
    rcases v with ⟨_ | k, i⟩
    · simp [D, σ, w, AddBlockData.extMap, AddBlockData.extVal, Geo.mConeMap, AddBlockData.plusCoord]
      rw [show (funHom P y hP) (t i).toFun = _ from hval i, map_mul, map_prod]
      ring
    · simp [D, σ, w, AddBlockData.extMap, AddBlockData.extVal, Geo.mConeMap, AddBlockData.plusCoord,
        funHom_mkF, coneHom_X]
      ring
  have hread : D.BlockReading y x' :=
    { ideal_eq := hP
      ext_eq := by
        ext f
        rw [AddBlockData.extIdeal, Geo.mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker]
        have hf := congrArg (fun ψ ↦ ψ f) hcomp
        simp only [RingHom.comp_apply] at hf
        constructor
        · intro h
          rw [h, map_zero] at hf
          have h2 := scale_injective w hw (hf.symm.trans (map_zero σ).symm)
          exact map_injective _ constMap_injective (h2.trans (map_zero _).symm)
        · intro h
          refine map_injective _ (funHom P y hP).injective ?_
          rw [hf, map_zero]
          simp [h]
      reads := ht }
  exact ⟨D, rfl, rfl, hread⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PChartLatSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace ChartLatSection

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]

theorem mConeMap_form (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    Geo.mConeMap (ι := blockIdx n) y f = C (aeval y f) * ∏ k, (X k : MvPolynomial ι Ω) ^ δ k := by
  have hg := (geoMultiHomog_iff f δ).mpr hf
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [Geo.mConeMap, aeval_monomial, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  have hX : (∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ m p) = ∏ k, (X k : MvPolynomial ι Ω) ^ δ k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX, MvPolynomial.algebraMap_apply]
  ring

theorem form_mem_iff (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    f ∈ Geo.mCoordIdeal (ι := blockIdx n) y ↔ aeval y f = 0 := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_form y hf]
  constructor
  · intro h
    have hM : (∏ k, (X k : MvPolynomial ι Ω) ^ δ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    exact C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)
  · intro h
    rw [h, C_0, zero_mul]

omit [Fintype ι] [DecidableEq ι] in

theorem aeval_eq_zero_of_mem (y : Coord n → Ω) {f : MvPolynomial (Coord n) ℤ}
    (hf : f ∈ Geo.mCoordIdeal (ι := blockIdx n) y) : aeval y f = 0 := by
  have h1 : (aeval (fun _ : ι => (1 : Ω))).toRingHom.comp
      (Geo.mConeMap (ι := blockIdx n) y).toRingHom = (aeval y : _ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) (fun v => by simp [Geo.mConeMap])
  have h2 := congrArg (fun φ : _ →+* _ => φ f) h1
  have h3 : Geo.mConeMap (ι := blockIdx n) y f = 0 := RingHom.mem_ker.mp hf
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3, map_zero] at h2
  rw [← h2]

omit [DecidableEq ι] in

theorem aeval_chartMonomial (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    aeval y (chartMonomial c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [chartMonomial, map_prod]

theorem coord_notMem_iff (y : Coord n → Ω) {P : ArithVariety n}
    (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (p : Coord n) :
    (X p : MvPolynomial (Coord n) ℤ) ∉ P.ideal ↔ y p ≠ 0 := by
  rw [hP, form_mem_iff y (isWeightedHomogeneous_X ℤ (coordDeg n) p), aeval_X]

theorem exists_form_of_mem_chartRingZ (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω} (hx : x ∈ Geo.chartRingZ (ι := blockIdx n) y c) :
    ∃ (δ : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) e δ ∧
      aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  have hpow : ∀ δ₁ δ₂ : ι → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [Geo.chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨coordDeg n p, X p, isWeightedHomogeneous_X ℤ _ p, ?_⟩
    have h1 : ∏ k, y ⟨k, c k⟩ ^ coordDeg n p k = y ⟨p.1, c p.1⟩ := by
      rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [coordDeg, hk])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [coordDeg]
    rw [aeval_X, h1, div_mul_cancel₀ _ (hc p.1)]
  | algebraMap r =>
    exact ⟨0, C r, isWeightedHomogeneous_C _ _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * chartMonomial c δ₂ + e₂ * chartMonomial c δ₁,
      (h₁.mul (isWeightedHomogeneous_chartMonomial c δ₂)).add ?_, ?_⟩
    · rw [add_comm δ₁]
      exact h₂.mul (isWeightedHomogeneous_chartMonomial c δ₁)
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_chartMonomial, aeval_chartMonomial, hpow]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * e₂, h₁.mul h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring

theorem exists_chartForm (y : Coord n → Ω) (a : ι → ℤ) (τ : ℕ) {s : Ω}
    (hs : s ∈ Geo.chartLat (ι := blockIdx n) y a τ) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (d δ : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) e δ ∧
      (∀ k, (δ k : ℤ) = (τ • a) k + d k) ∧ aeval y e = s * ∏ k, y ⟨k, c k⟩ ^ d k := by
  have hx : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ Geo.chartRingZ (ι := blockIdx n) y c := hs c hc
  obtain ⟨δ', e', he', hv'⟩ := exists_form_of_mem_chartRingZ y c hc hx
  set ex : ι → ℕ := fun k => ((τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs).toNat with hex
  have hexk : ∀ k, (ex k : ℤ) = (τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs := fun k => by
    rw [hex]
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨fun k => δ' k + ((τ : ℤ) * a k).natAbs, δ' + ex, e' * chartMonomial c ex,
    he'.mul (isWeightedHomogeneous_chartMonomial c ex), fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_add, hexk k]
    ring
  · rw [map_mul, hv', aeval_chartMonomial, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 := hc k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0, hexk k]
    congr 1
    push_cast
    ring

end ChartLatSection

open ChartLatSection in

theorem ChartLatSection.proof : ChartLatSection.Statement := by
  intro ι _ _ n Ω _ y P a τ s hP
  constructor
  · intro hs
    obtain ⟨c₀, hc₀⟩ := P.exists_chart
    have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (coord_notMem_iff y hP _).mp (hc₀ k)
    obtain ⟨d₀, δ₀, e₀, he₀, hδ₀, hv₀⟩ := exists_chartForm y a τ hs c₀ hy₀
    have hm₀ : ∏ k, y ⟨k, c₀ k⟩ ^ d₀ k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hy₀ k)
    have hden : chartMonomial c₀ d₀ ∉ P.ideal := by
      rw [hP, form_mem_iff y (isWeightedHomogeneous_chartMonomial c₀ d₀), aeval_chartMonomial]
      exact hm₀
    refine ⟨⟨e₀, chartMonomial c₀ d₀, δ₀, d₀, he₀, isWeightedHomogeneous_chartMonomial c₀ d₀,
      fun k => by rw [hδ₀ k]; ring, hden, fun c hc => ?_⟩, ?_⟩
    · have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (coord_notMem_iff y hP _).mp (hc k)
      obtain ⟨d, δ, e, he, hδ, hv⟩ := exists_chartForm y a τ hs c hyc
      refine ⟨d, e, ⟨δ, he, hδ⟩, ?_⟩
      have hdeg : d₀ + δ = δ₀ + d := by
        funext k
        have h1 := hδ k
        have h2 := hδ₀ k
        simp only [Pi.add_apply]
        omega
      have hhom : IsWeightedHomogeneous (coordDeg n)
          (chartMonomial c₀ d₀ * e - e₀ * chartMonomial c d) (d₀ + δ) := by
        refine ((isWeightedHomogeneous_chartMonomial c₀ d₀).mul he).sub ?_
        rw [hdeg]
        exact he₀.mul (isWeightedHomogeneous_chartMonomial c d)
      rw [hP, form_mem_iff y hhom, map_sub, map_mul, map_mul, hv, hv₀, aeval_chartMonomial,
        aeval_chartMonomial]
      ring
    · intro g h δg δh hg hh hd
      have hmk : P.mkF (chartMonomial c₀ d₀) ≠ 0 := by
        rw [Ne, P.mkF_eq_zero_iff]
        exact hden
      have hdeg : δg + d₀ = δ₀ + δh := by
        funext k
        have h1 := hd k
        have h2 := hδ₀ k
        simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h1 h2 ⊢
        omega
      have hhom : IsWeightedHomogeneous (coordDeg n) (g * chartMonomial c₀ d₀ - e₀ * h) (δg + d₀) := by
        refine (hg.mul (isWeightedHomogeneous_chartMonomial c₀ d₀)).sub ?_
        rw [hdeg]
        exact he₀.mul hh
      have key : P.mkF g = P.mkF e₀ / P.mkF (chartMonomial c₀ d₀) * P.mkF h ↔
          g * chartMonomial c₀ d₀ - e₀ * h ∈ P.ideal := by
        rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, sub_eq_zero, div_mul_eq_mul_div,
          eq_div_iff hmk]
      show _ ↔ P.mkF g = P.mkF e₀ / P.mkF (chartMonomial c₀ d₀) * P.mkF h
      rw [key, hP, form_mem_iff y hhom, map_sub, map_mul, map_mul, hv₀, aeval_chartMonomial,
        sub_eq_zero]
      constructor
      · intro h1
        rw [h1]
        ring
      · intro h1
        apply mul_right_cancel₀ hm₀
        linear_combination h1
  · rintro ⟨t, ht⟩
    have hyP : ∀ f ∈ P.ideal, aeval y f = 0 := fun f hf => aeval_eq_zero_of_mem y (hP ▸ hf)
    have hG : aeval y t.den ≠ 0 := by
      intro h0
      exact t.den_not_mem (by rw [hP, form_mem_iff y t.den_isHomogeneous]; exact h0)
    have hmk : P.mkF t.den ≠ 0 := by
      rw [Ne, P.mkF_eq_zero_iff]
      exact t.den_not_mem
    have hread : aeval y t.num = s * aeval y t.den := by
      refine (ht t.num t.den t.numDeg t.denDeg t.num_isHomogeneous t.den_isHomogeneous
        (fun k => by have := t.deg_eq k; linarith)).mpr ?_
      show P.mkF t.num = P.mkF t.num / P.mkF t.den * P.mkF t.den
      rw [div_mul_cancel₀ _ hmk]
    have hs : s = aeval y t.num / aeval y t.den := by
      rw [hread, mul_div_assoc, div_self hG, mul_one]
    have hmem := t.value_mem_chartLat y hyP hG
    rw [← hs] at hmem
    intro c hc
    have h := hmem c hc
    have he : ∀ k, -(((1 : ℕ) : ℤ) * (τ • a) k) = -((τ : ℤ) * a k) := fun k => by
      simp
    simp only [he] at h
    exact h

end

end GroundTheory.Heights₂.Heights
end

