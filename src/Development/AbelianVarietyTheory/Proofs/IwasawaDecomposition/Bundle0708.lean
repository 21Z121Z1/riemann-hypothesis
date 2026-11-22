import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0862
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PoincareNormCoordinateVectorMulLengthLeFive
section
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.PoinLen

theorem mem_castLE_iff {n a : ℕ} (ha : a ≤ n) (k : Fin n) :
    k ∈ Finset.univ.map (Fin.castLEEmb ha) ↔ k.val < a := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 h
    simp
  · intro h
    exact Finset.mem_map.2 ⟨⟨k.val, h⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

theorem gnorm_poincareGram_single {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) :
    GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a z) (Pi.single k 1) =
      √(if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (z k) ^ 2)) else 1 / 2) := by
  rw [GlobalTheory.HermFrame.gnorm, GlobalTheory.HermFrame.form_single, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram, diagonal_apply_eq]
  simp only [Complex.ofReal_re]

theorem sqrt_two_mul_pi_le : √(2 * Real.pi ^ 2) ≤ 5 := by
  rw [show (5:ℝ) = √(5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

theorem gnorm_mul_poinWt_le_five : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
    v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → ∀ k : Fin n,
    GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a v.ofLp) (Pi.single k 1) *
      GlobalTheory.GoodMetric.poinWt (Finset.univ.map (Fin.castLEEmb ha)) v k ≤ 5 := by
  intro n a ha ρ hρ v hv k
  rw [gnorm_poincareGram_single, GlobalTheory.GoodMetric.poinWt]
  by_cases hk : k.val < a
  · rw [if_pos hk, if_pos ((mem_castLE_iff ha k).2 hk)]
    have h0 : v.ofLp k ≠ 0 := by
      have := hv.2 ⟨k.val, hk⟩
      simpa [Fin.castLE] using this
    have h1 : ‖v.ofLp k‖ < 1 := lt_of_lt_of_le (hv.1 k) (by linarith)
    have ht := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos h0 h1
    have hx : 0 < ‖v.ofLp k‖ := norm_pos_iff.2 h0
    have hlog : |Real.log ‖v.ofLp k‖| = 2 * Real.pi * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) := by
      rw [abs_of_neg (Real.log_neg hx h1), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]
      field_simp
    change √(1 / (2 * (‖v.ofLp k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) ^ 2))) *
      (‖v.ofLp k‖ * |Real.log ‖v.ofLp k‖|) ≤ 5
    rw [hlog]
    set x := ‖v.ofLp k‖
    set t := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k)
    have hB : 0 ≤ x * (2 * Real.pi * t) := by positivity
    rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (by positivity)]
    convert sqrt_two_mul_pi_le using 2
    field_simp
  · rw [if_neg hk, if_neg (fun h => hk ((mem_castLE_iff ha k).1 h)), mul_one]
    calc √(1 / 2 : ℝ) ≤ √1 := Real.sqrt_le_sqrt (by norm_num)
      _ ≤ 5 := by rw [Real.sqrt_one]; norm_num

end GlobalTheory.PoinLen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCell
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isCell_face_of_isFaceCut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ)
    (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell H.bar ψ (fun j => v (s j)) := by
  intro E _ _ _ H q ψ hψ X _ _ _ _ hX hD m v hv m' s h hcut
  have hP := hψ X hX
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hv.strict
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓpos : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos hNr e2) e1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hD ℓ (-h) hℓpos
  obtain ⟨S, hS, hcov⟩ := hP.finite
  obtain ⟨b, hb⟩ : ∃ b : ℕ, ∀ γ ∈ S, ψ.evalZ γ ≤ b := by
    refine ⟨⌈∑ γ ∈ hS.toFinset, |ψ.evalZ γ|⌉₊, fun γ hγ => ?_⟩
    refine le_trans ?_ (Nat.le_ceil _)
    exact le_trans (le_abs_self _)
      (Finset.single_le_sum (f := fun γ => |ψ.evalZ γ|) (fun _ _ => abs_nonneg _) (hS.mem_toFinset.2 hγ))
  set K : ℕ := C * (1 + N * b) + 1 with hK
  have hKpos : 0 < K := Nat.succ_pos _

  have gen : ∀ u ∈ balForms H.bar X, (∀ y, 0 ≤ u y y) → ψ.evalZ u ≤ b →
      (0 ≤ h u ∧ (ℓ u : ℝ) = N * ψ.evalZ u) ∨
        (0 : ℝ) < K * (ℓ u : ℝ) + h u - K * N * ψ.evalZ u := by
    intro u hu hp hub
    by_cases heq : (ℓ u : ℝ) = N * ψ.evalZ u
    · left
      obtain ⟨k, c, hk, hc⟩ := h3 u hu hp heq.symm
      have e1 : (k : ℤ) * h u = ∑ i, (c i : ℤ) * h (v i) := by
        have := congrArg h hc
        simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
      have hnn : 0 ≤ (k : ℤ) * h u := e1 ▸ Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (hcut.1 i)
      exact ⟨(mul_nonneg_iff_of_pos_left (by exact_mod_cast hk)).1 hnn, heq⟩
    · right
      obtain ⟨n, hn⟩ := hP.integral u hu hp
      have hle : (N : ℝ) * ψ.evalZ u ≤ ℓ u := h2 u hu hp
      have hlt : (N : ℝ) * ψ.evalZ u < ℓ u := lt_of_le_of_ne hle (Ne.symm heq)
      rw [hn] at hlt hub ⊢
      have hint : (N : ℤ) * n + 1 ≤ ℓ u := by
        have : (((N : ℤ) * n : ℤ) : ℝ) < ℓ u := by push_cast; exact hlt
        exact_mod_cast this
      have hint' : (N : ℝ) * n + 1 ≤ ℓ u := by exact_mod_cast hint
      have hCu : -h u ≤ C * ℓ u := by simpa using hC u hu hp
      have hCu' : -(h u : ℝ) ≤ C * ℓ u := by exact_mod_cast hCu
      have hKr : (K : ℝ) = C * (1 + N * b) + 1 := by rw [hK]; push_cast; ring
      have hCN : (0 : ℝ) ≤ C * N := by positivity
      have a1 : (K - C : ℝ) * 1 ≤ (K - C) * (ℓ u - N * n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by rw [hKr]; have : (0 : ℝ) ≤ C * N * b := by positivity
                                                    nlinarith)
      have a2 : (C * N : ℝ) * n ≤ C * N * b := mul_le_mul_of_nonneg_left hub hCN
      rw [hKr] at a1 ⊢
      nlinarith

  have core : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      ((K * N : ℕ) : ℝ) * ψ.evalZ β ≤ ((K • ℓ + h) β : ℤ) ∧
        (((K * N : ℕ) : ℝ) * ψ.evalZ β = ((K • ℓ + h) β : ℤ) → h β = 0) := by
    intro β hβ hp
    have hR : toReal β ∈ psdCone H.bar X := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (by simp [hβ])
        (by simp [hp]) (by simp)
    obtain ⟨e, mm, γ, c, hγ, hγS, hc, hsum⟩ := hcov (toReal β) hR
    set u : Fin mm → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hu
    have hβu : toReal β = ∑ i, c i • toReal (u i) := LinearMap.ext₂ fun a b => by
      have := LinearMap.congr_fun₂ hsum (e.symm a) (e.symm b)
      simpa [LinearMap.sum_apply, u] using this
    have hlin : ψ.LinearOn u := (linearOn_pull_iff e.symm.surjective).2 hγ.linear
    have hψβ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (u i) := by
      rw [← evalR_toReal, hβu, (linearOn_iff ψ u).1 hlin c hc]
    have hℓβ := apply_eq_of_toReal_eq hβu ℓ
    have hhβ := apply_eq_of_toReal_eq hβu h
    have hT : (((K • ℓ + h) β : ℤ) : ℝ) - ((K * N : ℕ) : ℝ) * ψ.evalZ β =
        ∑ i, c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, Nat.cast_mul]
      rw [hℓβ, hhβ, hψβ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hg : ∀ i, (0 ≤ h (u i) ∧ (ℓ (u i) : ℝ) = N * ψ.evalZ (u i)) ∨
        (0 : ℝ) < K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i) := fun i =>
      gen (u i) (pull_mem _ (hγ.mem i)) (fun y => hγ.nonneg i _)
        (by rw [hu, evalZ_pull ψ e.symm.surjective]; exact hb _ (hγS i))
    have hterm : ∀ i, 0 ≤ c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) := fun i => by
      refine mul_nonneg (hc i) ?_
      rcases hg i with ⟨h0, he⟩ | hpos
      · rw [he]
        have : (0 : ℝ) ≤ h (u i) := by exact_mod_cast h0
        nlinarith
      · exact hpos.le
    refine ⟨?_, fun heq => ?_⟩
    · have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hterm i
      linarith
    · have h0 : ∑ i, c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) = 0 := by
        rw [← hT, heq, sub_self]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i).1 h0
      have : (h β : ℝ) = 0 := by
        rw [hhβ]
        refine Finset.sum_eq_zero fun i hi => ?_
        rcases eq_or_ne (c i) 0 with hci | hci
        · rw [hci, zero_mul]
        · have hTi := (mul_eq_zero.1 (hz i hi)).resolve_left hci
          rcases hg i with ⟨-, he⟩ | hpos
          · rw [he] at hTi
            have : (h (u i) : ℝ) = 0 := by linarith
            rw [this, mul_zero]
          · exact absurd hTi hpos.ne'
      exact_mod_cast this
  refine ⟨fun j => hv.mem _, fun j => hv.nonneg _, linearOn_comp hv.linear s, K * N, K • ℓ + h,
    Nat.mul_pos hKpos hN, fun i => ?_, fun β hβ hp => (core β hβ hp).1, fun β hβ hp heq => ?_⟩
  · have hz : h (v (s i)) = 0 := (hcut.2 _).2 ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hz, add_zero, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul]
    rw [h1]; ring
  · have hh := (core β hβ hp).2 heq
    have hℓ : (N : ℝ) * ψ.evalZ β = ℓ β := by
      have e1 := heq
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hh, add_zero, Int.cast_mul,
        Int.cast_natCast, Nat.cast_mul] at e1
      have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
      have : (K : ℝ) * (N * ψ.evalZ β - ℓ β) = 0 := by linarith
      linarith [(mul_eq_zero.1 this).resolve_left hKr.ne']
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp hℓ
    have e1 : (k : ℤ) * h β = ∑ j, (c j : ℤ) * h (v j) := by
      have := congrArg h hc
      simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    rw [hh, mul_zero] at e1
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (Int.natCast_nonneg (c j)) (hcut.1 j)).1 e1.symm
    have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := fun j hj => by
      have hne : h (v j) ≠ 0 := fun h0 => hj ((hcut.2 j).1 h0)
      have := (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_right hne
      exact_mod_cast this
    refine ⟨k, fun i => c (s i), hk, ?_⟩
    rw [hc]
    classical
    rw [← Finset.sum_map Finset.univ s (fun j => c j • v j)]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    rw [hc0 j fun ⟨i, hi⟩ => hj (by simp [← hi]), zero_smul]

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyhedralPolarisationFaceCutIsCell
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.FaceCutCell

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {ψ : InvFun (𝓞 E)}
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]

omit [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] in

theorem apply_eq_sum_of_toReal {m : ℕ} {β : LinearMap.BilinForm ℤ X} {u : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hβ : toReal β = ∑ i, c i • toReal (u i)) (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (F β : ℝ) = ∑ i, c i * (F (u i) : ℝ) := by
  have h := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) Function.injective_id F
    (β := Fin.cons β u) (c := Fin.cons (-1) c) (by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, neg_smul, one_smul, hβ, neg_add_cancel])
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  linarith

theorem est_at {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hstr : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i)
    (hle : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β ≤ ℓ β)
    (hγ : ∀ j, 0 ≤ h (γ j)) {C : ℕ} (hC : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β)
    {u : LinearMap.BilinForm ℤ X} (hu : u ∈ balForms H.bar X) (hp : ∀ y, 0 ≤ u y y) (n : ℤ) (hn : ψ.evalZ u = n)
    {B0 L : ℝ} (hb : N * ψ.evalZ u ≤ B0) (hB0 : 0 ≤ B0) (hL : C * (B0 + 1) + C ≤ L) :
    L * (N * ψ.evalZ u) ≤ L * ℓ u + h u := by
  by_cases he : (N : ℝ) * ψ.evalZ u = ℓ u
  · obtain ⟨k, c, hk, hc⟩ := hstr u hu hp he
    have e3 : h (k • u) = ∑ i, (c i : ℤ) * h (γ i) := by
      rw [hc, map_sum]; simp only [map_nsmul, nsmul_eq_mul]
    have h2 : 0 ≤ ∑ i, (c i : ℤ) * h (γ i) := Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hγ i)
    rw [← e3, map_nsmul, nsmul_eq_mul] at h2
    have h3 : 0 ≤ h u := by
      by_contra hneg
      push_neg at hneg
      have : (k : ℤ) * h u < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hk) hneg
      linarith
    have h4 : (0 : ℝ) ≤ h u := by exact_mod_cast h3
    rw [he]
    linarith
  · have hlt : (N : ℝ) * ψ.evalZ u < ℓ u := lt_of_le_of_ne (hle u hu hp) he
    rw [hn] at hlt hb ⊢
    have h1 : (N : ℤ) * n < ℓ u := by exact_mod_cast hlt
    have h2 : ((N : ℤ) * n + 1 : ℤ) ≤ ℓ u := h1
    have h3 : (N : ℝ) * n + 1 ≤ ℓ u := by exact_mod_cast h2
    have h5 := hC u hu hp
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    have hLC : (0 : ℝ) ≤ L - C := by nlinarith [mul_nonneg hC0 hB0]
    nlinarith [mul_nonneg hLC (show (0 : ℝ) ≤ ℓ u - N * n - 1 by linarith),
      mul_nonneg hC0 (show (0 : ℝ) ≤ B0 - N * n by linarith), mul_nonneg hC0 hB0]

theorem isCell_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (X : Type)
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X], IsPolyFanOn H.bar ψ X → Dominates H.bar X →
    ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i)) := by
  intro E _ _ _ H ψ X _ _ _ hP hD m m' γ s h hγ hf
  refine ⟨fun i => hγ.mem _, fun i y => hγ.nonneg _ y, linearOn_comp hγ.linear s, ?_⟩
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have hpos : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have e3 : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos (by exact_mod_cast hN) e2) e1
    exact_mod_cast e3
  obtain ⟨C, hC⟩ := hD ℓ (-h) hpos
  have hC' : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β := fun β hβ hp => by
    have e1 := hC β hβ hp
    simp only [LinearMap.neg_apply] at e1
    exact_mod_cast e1
  obtain ⟨S, hS, hcov⟩ := hP.finite
  obtain ⟨B1, hB1⟩ := (hS.image fun τ => (N : ℝ) * ψ.evalZ τ).bddAbove
  set B0 := max B1 0 with hB0def
  have hB0nn : (0 : ℝ) ≤ B0 := le_max_right _ _
  have hB0 : ∀ τ ∈ S, (N : ℝ) * ψ.evalZ τ ≤ B0 := fun τ hτ => (hB1 ⟨τ, hτ, rfl⟩).trans (le_max_left _ _)
  have est : ∀ L : ℝ, C * (B0 + 1) + C ≤ L → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      L * (N * ψ.evalZ β) ≤ L * ℓ β + h β := by
    intro L hL β hβ hp
    have hmem : toReal β ∈ psdCone H.bar X := by
      have e1 := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1]
        (fun i => by fin_cases i; simpa using hβ) (fun i y => by fin_cases i; simpa using hp y)
        (fun i => by fin_cases i; simp)
      simpa using e1
    obtain ⟨e, k, τ, c, hτ, hτS, hc, hdec⟩ := hcov _ hmem
    let u : Fin k → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (τ i)
    have hu : IsCell H.bar ψ u := isCell_pull_equiv hτ e.symm
    have hβu : toReal β = ∑ i, c i • toReal (u i) := LinearMap.ext₂ fun a b => by
      have e1 := LinearMap.congr_fun₂ hdec (e.symm a) (e.symm b)
      simpa [u, LinearMap.sum_apply] using e1
    have hψ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (u i) := by
      rw [← evalR_toReal, hβu]
      exact (linearOn_iff ψ u).1 hu.linear c hc
    have hℓ := apply_eq_sum_of_toReal hβu ℓ
    have hh := apply_eq_sum_of_toReal hβu h
    have hterm : ∀ i, L * (N * ψ.evalZ (u i)) ≤ L * ℓ (u i) + h (u i) := fun i => by
      obtain ⟨n, hn⟩ := hP.integral _ (hu.mem i) (hu.nonneg i)
      refine est_at h3 h2 hf.1 hC' (hu.mem i) (hu.nonneg i) n hn ?_ hB0nn hL
      rw [show ψ.evalZ (u i) = ψ.evalZ (τ i) from evalZ_pull ψ e.symm.surjective _]
      exact hB0 _ (hτS i)
    rw [hψ, hℓ, hh]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have e1 := mul_le_mul_of_nonneg_left (hterm i) (hc i)
    convert e1 using 1 <;> ring
  obtain ⟨K, hK⟩ := exists_nat_ge (C * (B0 + 1) + C + 1 : ℝ)
  have hK1 : C * (B0 + 1) + C ≤ (K : ℝ) - 1 := by linarith
  have hK0 : C * (B0 + 1) + C ≤ (K : ℝ) := by linarith
  have hCB : (0 : ℝ) ≤ C * (B0 + 1) + C :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Nat.cast_nonneg _)
  have hKpos : 0 < K := by exact_mod_cast (show (0 : ℝ) < K by linarith)
  refine ⟨K * N, (K : ℤ) • ℓ + h, Nat.mul_pos hKpos hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · have h0 : h (γ (s i)) = 0 := (hf.2 _).2 ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, h0, add_zero, smul_eq_mul]
    push_cast
    rw [h1]
    ring
  · have e1 := est K hK0 β hβ hp
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    linarith
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at he
    push_cast at he
    have e1 := est (K - 1) hK1 β hβ hp
    have e2 := h2 β hβ hp
    have heq : (N : ℝ) * ψ.evalZ β = ℓ β := by nlinarith
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp heq
    have hh0 : h β = 0 := by
      have e4 : (h β : ℝ) = 0 := by nlinarith
      exact_mod_cast e4
    have e3 : h (k • β) = ∑ i, (c i : ℤ) * h (γ i) := by
      rw [hc, map_sum]; simp only [map_nsmul, nsmul_eq_mul]
    have hsum : ∑ i, (c i : ℤ) * h (γ i) = 0 := by
      rw [← e3, map_nsmul, hh0, smul_zero]
    have hz : ∀ j, (c j : ℤ) * h (γ j) = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hf.1 i)).1 hsum j
        (Finset.mem_univ _)
    refine ⟨k, fun i => c (s i), hk, hc.trans ?_⟩
    refine (Fintype.sum_of_injective s s.injective _ _ (fun j hj => ?_) fun i => rfl).symm
    have hne : h (γ j) ≠ 0 := fun h0 => hj ((hf.2 j).1 h0)
    have hcj : c j = 0 := by
      rcases mul_eq_zero.1 (hz j) with h' | h'
      · exact_mod_cast h'
      · exact absurd h' hne
    simp [hcj]

example : IsCell id (InvFun.minVal ℤ) ![mulForm] := isCone_mulForm.isCell

end GlobalTheory.PolFan.FaceCutCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalPolarizationOfMumfordBundleSiegelFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarization_of_mumfordBundle_siegelFibre : ∀ (o : Type) [CommRing o] (ζ : o) (g n : ℕ) (F : SFam g n ζ) (K : Type) [Field K] (y : Sp K ⟶ F.X) (B : Over (Sp K)) [GrpObj B] (α : B.left ⟶ F.univ.A.left) (α₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A y α → IsSquare α α₂ → ∀ L : LB B.left, L.IsLB → Rigidified B L → Out.Sym B L → LBIso (abelian₂ B L) (F.univ.P.pull α₂) → IsAbelianScheme B ∧ RelAmple B L ∧ KTriv B L := by
  first | exact @GlobalTheory.SiegFibrePol.polAV_of_lam_univ | exact GlobalTheory.SiegFibrePol.polAV_of_lam_univ | (intros; apply GlobalTheory.SiegFibrePol.polAV_of_lam_univ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhere
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProperOfAbelianFibres
open IsLocalRing

theorem apply_genericPoint_of_flat {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    [Flat f] : f (genericPoint X) = genericPoint Y := by
  obtain ⟨x', hx', hfx'⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint X)))
  refine (Specializes.antisymm ?_ ?_).eq
  · rw [← hfx']
    exact (genericPoint_specializes x').map f.continuous
  · exact genericPoint_specializes _

theorem isProper_dvr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V]
    [IsDomain V] [IsLocalRing V] (hW : GlobalTheory.LN.CDvr V) (t : SAB H (Sp V)) (hP : GlobalTheory.LN.PolAt t (jK V))
    (hab : abLocus t.G = Set.univ) : IsProper t.G.hom := by
  haveI := hW.1
  haveI := hW.2.2
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have ht : ∀ z, z ∈ abLocus t.G := fun z => hab ▸ Set.mem_univ z
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H V hW t hP (GlobalTheory.GoodTrait.splitOver_of_abLocus t.G t.semi ht)
  have hmax : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (V ⧸ maximalIdeal V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (V ⧸ maximalIdeal V ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick V (maximalIdeal V) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom
  exact (GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ V hW.2.1 P.D P.A t.G t.semi P.U hs).proper

theorem isProper_of_polAt_of_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) →
    abLocus t.G = Set.univ → IsProper t.G.hom := by
  intro E _ _ _ H R _ _ _ _ t hP hab
  haveI : IsSemiAbelian t.G := t.semi
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  haveI := t.semi.smooth
  haveI : IsIntegral t.G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian t.G
  refine GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint R t.G.left t.G.hom ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* V, spMap φ = y := ⟨(Spec.preimage y).hom, by simp [spMap]⟩

  let p₀ : Sp K := (⊥ : PrimeSpectrum K)
  have h₁ : x p₀ = genericPoint t.G.left := hx ⟨p₀, rfl⟩
  have h₂ : (x ≫ t.G.hom) p₀ = (⊥ : PrimeSpectrum R) := by
    rw [Scheme.Hom.comp_apply, h₁, apply_genericPoint_of_flat]
    exact genericPoint_eq_bot_of_affine (CommRingCat.of R)
  rw [hxy] at h₂
  have h₃ : Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) = ⊥ := congrArg PrimeSpectrum.asIdeal h₂
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) := by simp [ha]
    rw [h₃] at this
    simpa using this
  haveI : CharZero V := charZero_of_injective_ringHom hinj

  obtain ⟨tV, ⟨m⟩⟩ := exists_sab (spMap φ) t
  have hinj' : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hinj
  let ψ : FractionRing R →+* FractionRing V := IsFractionRing.lift hinj'
  have hg : spMap ψ ≫ jK R = jK V ≫ spMap φ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [ψ, IsFractionRing.lift_algebraMap]
  have hPV : GlobalTheory.LN.PolAt tV (jK V) := GlobalTheory.DatUniq.polAt_pull m hP (jK V) (spMap ψ) hg
  have habV : abLocus tV.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi m.cart.1 z).1 (hab ▸ Set.mem_univ _)
  have hpV : IsProper tV.G.hom := isProper_dvr V ⟨inferInstance, inferInstance, inferInstance⟩ tV hPV habV

  let xV : Sp K ⟶ tV.G.left := m.cart.1.lift x (spMap (algebraMap V K)) hxy
  have hE : ValuativeCriterion.Existence tV.G.hom := by
    have h : UniversallyClosed tV.G.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq tV.G.hom :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨by simp [xV, spMap]⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  refine ⟨l.l ≫ m.cm.F, ?_⟩
  rw [← Category.assoc]
  have := l.fac_left
  change spMap (algebraMap V K) ≫ l.l = xV at this
  rw [this]
  exact m.cart.1.lift_fst _ _ _

end GlobalTheory.ProperOfAbelianFibres
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoordsIntegralOfPartOfIntBasisStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realConeCoords_integral_of_partOfIntBasis : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i, u i ∈ balForms (id : ℤ → ℤ) X), IsPartOfBasis (fun i => (⟨u i, hu i⟩ : balForms (id : ℤ → ℤ) X)) → ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z := by
  first | exact @GlobalTheory.cone_coords_int_of_isPartOfBasis | exact GlobalTheory.cone_coords_int_of_isPartOfBasis | (intros; apply GlobalTheory.cone_coords_int_of_isPartOfBasis <;> assumption)
end

