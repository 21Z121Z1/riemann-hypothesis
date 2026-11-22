import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

theorem snc_eval_zero {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set X}
    (h : IsSNC A L s m W) {k : Fin r} {x : X} (hx : x ∈ W k) (hm : m k ≠ 0) : s x x = 0 := by
  obtain ⟨ψ, -, hxs, -, σ, -, hW, u, -, -, hs⟩ := h x
  have hx' : x ∈ W k ∩ ψ.source := ⟨hx, hxs⟩
  rw [hW k] at hx'
  obtain ⟨-, i, hσ, hψ⟩ := hx'
  rw [hs x hxs]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [hσ, hψ, hm]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_divSupp_of_eval {P : Ideal (MRing ι)} {s : MRing ι} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) (h0 : eval z (map (Int.castRingHom ℂ) s) = 0) :
    ∃ W' ∈ divSupp P s, IsHorizontal W' ∧ z ∈ mcPts W' := by
  classical
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hφ : ∀ f, φ f = eval z (map (Int.castRingHom ℂ) f) := fun f => rfl
  haveI hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    rw [sup_le_iff, Ideal.span_le, Set.singleton_subset_iff]
    refine ⟨fun f hf => ?_, ?_⟩
    · rw [RingHom.mem_ker, hφ]
      exact hz.2 f hf
    · show s ∈ RingHom.ker φ
      rw [RingHom.mem_ker, hφ]
      exact h0
  obtain ⟨W', hW', hW'le⟩ := Ideal.exists_minimalPrimes_le hle
  have hmem : ∀ f ∈ W', eval z (map (Int.castRingHom ℂ) f) = 0 := fun f hf => by
    have := hW'le hf
    rwa [RingHom.mem_ker, hφ] at this
  refine ⟨W', ⟨hW', ?_⟩, ?_, ⟨hz.1, hmem⟩⟩
  · intro k
    obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, fun hX => hi (by simpa using hmem _ hX)⟩
  · show Ideal.comap _ W' = ⊥
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap] at hn
    rw [Ideal.mem_bot]
    have := hmem _ hn
    simpa using this

theorem proj_ne_zero_of_snc {P J : Ideal (MRing ι)} {e n : ℕ} (R : AnLogRes P J e) {A : HermLine ι}
    {s : MRing ι} {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set R.X}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hsnc : IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W)
    (hΨ : ∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) {k : Fin r} (hm : m k ≠ 0)
    {x : R.X} (hx : x ∈ W k) : Ψ (segre (R.lift x x)) ≠ 0 := by
  have h0 := snc_eval_zero hsnc hx hm
  have hz : R.lift x x ∈ mcPts P := R.mem x x (R.mem_U x)
  obtain ⟨W', hW', hh, hzW⟩ := exists_divSupp_of_eval hz h0
  exact hΨ W' hW' hh _ hzW

theorem divPushFibre_of (h1 : DivPushResSideStatement) (h2 : DivPushPointStatement) :
    DivPushFibreStatement := by
  unfold DivPushResSideStatement at h1
  unfold DivPushPointStatement at h2
  unfold DivPushFibreStatement
  intro K _ ι _ P J n R L B B₁ s r m W BW Ψ hAr hLs hBs hB1s hB1a hsec hsnc hHolo hΨ
  have hclosed : ∀ k, IsClosed (W k) := by
    intro k
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨ψ, -, hxs, -, σ, -, hW, -⟩ := hsnc x
    refine ⟨ψ.source ∩ {y | ∀ i, σ k = some i → ψ y i ≠ 0}, ?_, ?_, ?_⟩
    · rintro y ⟨hys, hy⟩ hyW
      have hyy : y ∈ W k ∩ ψ.source := ⟨hyW, hys⟩
      rw [hW k] at hyy
      obtain ⟨-, i, hi, h0⟩ := hyy
      exact hy i hi h0
    · cases hσ : σ k with
      | none =>
        have e : ψ.source ∩ {y | ∀ i, (none : Option (Fin (n + 1))) = some i → ψ y i ≠ 0} =
            ψ.source := by
          ext y
          simp
        rw [e]
        exact ψ.open_source
      | some i0 =>
        have e : ψ.source ∩ {y | ∀ i, some i0 = some i → ψ y i ≠ 0} =
            ψ.source ∩ (fun y => ψ y i0) ⁻¹' {0}ᶜ := by
          ext y
          simp
        rw [e]
        exact ((continuous_apply i0).comp_continuousOn ψ.continuousOn).isOpen_inter_preimage
          ψ.open_source isOpen_compl_singleton
    · refine ⟨hxs, fun i hi h0 => hx ?_⟩
      have hxx : x ∈ {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0} := ⟨hxs, i, hi, h0⟩
      rw [← hW k] at hxx
      exact hxx.1
  have hres : ∀ k, m k ≠ 0 → _ := fun k hmk =>
    h1 K ι P J n R L B₁ Ψ (W k) (BW k) hAr hLs hB1s hB1a (hclosed k) (hHolo k)
      (fun x hx => proj_ne_zero_of_snc R hsnc hΨ hmk hx)
  have hint : ∀ k ∈ Finset.univ, Integrable (fun y => (m k : ℝ) * divFib R L B₁ Ψ (BW k) y) := by
    intro k _
    by_cases hmk : m k = 0
    · simp [hmk]
    · exact ((hres k hmk).1).const_mul _
  have step : ∀ k ∈ Finset.univ, (m k : ℝ) * mInt (BW k)
      (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
      ((fun x => Real.log (B₁.h (R.lift x x))) ∘ Subtype.val) =
        ∫ y, (m k : ℝ) * divFib R L B₁ Ψ (BW k) y := by
    intro k _
    by_cases hmk : m k = 0
    · simp [hmk]
    · rw [integral_const_mul, (hres k hmk).2]
  rw [Finset.sum_congr rfl step,
    ← integral_finset_sum Finset.univ (f := fun k y => (m k : ℝ) * divFib R L B₁ Ψ (BW k) y) hint]
  apply integral_congr_ae
  filter_upwards [h2 K ι P J n R L B B₁ s r m W BW Ψ hAr hLs hBs hB1s hB1a hsec hsnc hHolo hΨ]
    with y hy
  simpa using hy

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushC
section
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def projOfForms {e r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) where
  toFun w j := if h : (j : ℕ) < r then ∑ t, (L ⟨j, h⟩ t : ℂ) * w t else 0
  map_add' := by
    intro w w'
    funext j
    simp only [Pi.add_apply]
    split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c w
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [Finset.mul_sum, mul_left_comm]

theorem isGoodProj_of_intOver {P : Ideal (MRing ι)} (hK : Nonempty K) (hhom : IsMultiHomogIdeal P)
    {e r : ℕ} (hr : r ≤ e + 1) (L : Fin r → ((k : K) → ι k) → ℚ)
    (hL : ∀ t, IntOver ℚ (forms (segQ P) L) (segQ P t)) :
    IsGoodProj P (projOfForms (e := e) L) := by
  intro z hz hΨ
  obtain ⟨k0⟩ := hK
  choose i1 hi1 using hz.1
  have hs : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi1 k
  obtain ⟨p, hpm, hp⟩ := hL i1
  let g0 : MvPolynomial (Fin r) ℚ →+* ℂ := eval₂Hom (algebraMap ℚ ℂ) 0
  have key : ∀ c : ℂ, c ≠ 0 → Polynomial.eval (c * segre z i1) (p.map g0) = 0 := by
    intro c hc
    have hzc := scaleBlock_mem_zeroLocus P hhom k0 hc hz
    have hv : ∀ t, evQ P _ hzc (segQ P t) = c * segre z t := by
      intro t
      rw [segQ, evQ_mk, segMon, eval₂_prod]
      simp only [eval₂_X, scaleBlock, Finset.prod_mul_distrib, segre]
      congr 1
      simp
    have hforms : ∀ j, evQ P _ hzc (forms (segQ P) L j) = 0 := by
      intro j
      have hΨj := congrFun hΨ ⟨j.1, by omega⟩
      simp only [projOfForms, LinearMap.coe_mk, AddHom.coe_mk, dif_pos j.2, Fin.eta,
        Pi.zero_apply] at hΨj
      simp only [forms, map_sum, map_rat_smul, hv, Rat.smul_def]
      rw [show ∑ t, (L j t : ℂ) * (c * segre z t) = c * ∑ t, (L j t : ℂ) * segre z t by
        rw [Finset.mul_sum]; congr 1; funext t; ring, hΨj, mul_zero]
    have hcomp : (evQ P _ hzc).comp
        ((aeval (forms (segQ P) L) : MvPolynomial (Fin r) ℚ →ₐ[ℚ] _) :
          MvPolynomial (Fin r) ℚ →+* _) = g0 := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [g0]
      · intro j
        simp [g0, hforms]
    have := congrArg (evQ P _ hzc) hp
    rw [Polynomial.hom_eval₂, hcomp, hv, map_zero] at this
    rw [Polynomial.eval_map]
    exact this
  have hinf : {x : ℂ | (p.map g0).IsRoot x}.Infinite := by
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    have hx0 : x ≠ 0 := hx
    have := key (x / segre z i1) (div_ne_zero hx0 hs)
    rw [div_mul_cancel₀ x hs] at this
    exact this
  exact (hpm.map g0).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ hinf)

theorem evalAlgHom_comp_aeval_forms {F : Type} (Q : F → Ideal (MRing ι))
    {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ) (W : F) :
    (Pi.evalAlgHom ℚ (fun W : F => MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal (Q W)) W).comp
        (aeval (forms (fun t W => segQ (Q W) t) L)) = aeval (forms (segQ (Q W)) L) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [forms]

theorem divPushCommonProj : DivPushCommonProjStatement := by
  intro K _ ι _ P n A s hP hs
  classical
  let F := ((divSupp_finite P s).subset (fun _ h => h.1) :
    {W' | W' ∈ divSupp P s ∧ IsHorizontal W'}.Finite).toFinset
  have hAr : ∀ W : F, IsArithVar W.1 (n + 1) := fun W => by
    have h := W.2
    rw [Set.Finite.mem_toFinset] at h
    exact (divSuppArith K ι P (n + 1) A s W.1 hP hs h.1).1 h.2
  let v : ((k : K) → ι k) → ∀ W : F, MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal W.1 :=
    fun t W => segQ W.1 t
  obtain ⟨r, hr, L, hL⟩ := exists_linear_normalization (k := ℚ) v (n + 1) (by
    intro r L hrL hind
    have hW : ∀ W : F, ∃ p : MvPolynomial (Fin r) ℚ,
        aeval (forms (segQ W.1) L) p = 0 ∧ p ≠ 0 := by
      intro W
      have h := forms_not_algebraicIndependent W.1 n (hAr W) hrL L
      rw [algebraicIndependent_iff] at h
      push Not at h
      exact h
    choose G hG0 hGne using hW
    have hQ : (∏ W : F, G W) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W _ => hGne W
    refine hQ ((algebraicIndependent_iff.mp hind) _ ?_)
    funext W
    have h1 := DFunLike.congr_fun (evalAlgHom_comp_aeval_forms (fun W : F => W.1) L W) (∏ W : F, G W)
    simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply] at h1
    rw [Pi.zero_apply]
    refine h1.trans ?_
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ W) (hG0 W))
  refine ⟨projOfForms L, fun W hW hH => ?_⟩
  have hWF : W ∈ F := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨hW, hH⟩
  have hA := hAr ⟨W, hWF⟩
  refine isGoodProj_of_intOver hA.1 hA.2.1.2.1 hr L fun t => ?_
  obtain ⟨p, hpm, hp⟩ := hL t
  refine ⟨p, hpm, ?_⟩
  have h1 := congrArg
    ((Pi.evalAlgHom ℚ (fun W : F => MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal W.1) ⟨W, hWF⟩ :
      (∀ W : F, MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal W.1) →+* MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal W)) hp
  rw [Polynomial.hom_eval₂, map_zero, ← AlgHom.comp_toRingHom,
    evalAlgHom_comp_aeval_forms (fun W : F => W.1) L ⟨W, hWF⟩] at h1
  exact h1

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

