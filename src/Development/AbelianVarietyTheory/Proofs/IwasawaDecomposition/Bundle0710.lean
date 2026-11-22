import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0693
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0020
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0695
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.StarCover

theorem exists_points {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) :
    ∃ (n : ℕ) (p : Fin n → X × X), ∀ r : Fin m → ℝ,
      (∀ k, ∑ j, r j * (γ j (p k).1 (p k).2 : ℝ) = 0) → ∀ x y, ∑ j, r j * (γ j x y : ℝ) = 0 := by
  classical
  let S : X × X → (Fin m → ℚ) := fun q j => (γ j q.1 q.2 : ℚ)
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range S)
  obtain ⟨n, f, hf⟩ := (hli.setFinite).fin_embedding
  have hfb : ∀ k, f k ∈ b := fun k => hf ▸ Set.mem_range_self k
  have hpre : ∀ k, ∃ q, S q = f k := fun k => hbS (hfb k)
  let p : Fin n → X × X := fun k => (hpre k).choose
  have hp : ∀ k, S (p k) = f k := fun k => (hpre k).choose_spec
  refine ⟨n, p, fun r hr x y => ?_⟩
  have hmem : S (x, y) ∈ Submodule.span ℚ (Set.range f) := by
    rw [hf, hspan]; exact Submodule.subset_span ⟨(x, y), rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
  have hj : ∀ j, (γ j x y : ℝ) = ∑ k, (c k : ℝ) * (γ j (p k).1 (p k).2 : ℝ) := fun j => by
    have := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hp, S] at this
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) this
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at h2
    exact h2.symm
  calc ∑ j, r j * (γ j x y : ℝ) = ∑ k, (c k : ℝ) * ∑ j, r j * (γ j (p k).1 (p k).2 : ℝ) := by
        simp only [hj, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := by simp [hr]

end GlobalTheory.StarCover

namespace GlobalTheory.StarCover
open GlobalTheory.MinkWeylReal

theorem dotR_comb {n m : ℕ} (a : Fin n → ℚ) (u : Fin m → Fin n → ℚ) (r : Fin m → ℝ) :
    dotR a (∑ j, r j • castR (u j)) = ∑ j, r j * ((a ⬝ᵥ u j : ℚ) : ℝ) := by
  simp only [dotR, castR, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Rat.cast_sum, Rat.cast_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_rcone_image {n m : ℕ} (u : Fin m → Fin n → ℚ) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) :
    ∑ j, r j • castR (u j) ∈ rcone (Finset.univ.image u) := by
  classical
  refine ⟨fun y => ∑ j ∈ Finset.univ.filter (fun j => u j = y), r j,
    fun y _ => Finset.sum_nonneg fun j _ => hr j, ?_⟩
  symm
  refine Finset.sum_image' _ fun j _ => ?_
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

theorem exists_of_mem_rcone_image {n m : ℕ} (u : Fin m → Fin n → ℚ) (x : Fin n → ℝ)
    (hx : x ∈ rcone (Finset.univ.image u)) :
    ∃ r : Fin m → ℝ, (∀ j, 0 ≤ r j) ∧ x = ∑ j, r j • castR (u j) := by
  classical
  obtain ⟨c, hc, rfl⟩ := hx
  let k : Fin m → ℝ := fun j => ((Finset.univ.filter (fun i => u i = u j)).card : ℝ)
  have hk : ∀ j, 0 < k j := fun j => by
    simp only [k, Nat.cast_pos, Finset.card_pos]
    exact ⟨j, by simp⟩
  refine ⟨fun j => c (u j) / k j, fun j => div_nonneg (hc _ (by simp)) (hk j).le, ?_⟩
  refine Finset.sum_image' _ fun j _ => ?_
  have : ∀ i ∈ Finset.univ.filter (fun i => u i = u j), (c (u i) / k i) • castR (u i) = (c (u j) / k j) • castR (u j) :=
    fun i hi => by
      have hi' := (Finset.mem_filter.mp hi).2
      have hki : k i = k j := by simp only [k, hi']
      rw [hi', hki]
  rw [Finset.sum_congr rfl this, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  change c (u j) = k j * (c (u j) / k j)
  field_simp [(hk j).ne']

end GlobalTheory.StarCover

namespace GlobalTheory.StarCover
open GlobalTheory.MinkWeylReal

theorem toReal_apply' {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (x y : X) :
    toReal β x y = (β x y : ℝ) := by simp [toReal]

theorem comb_apply {X : Type} [AddCommGroup X] {m : ℕ} (r : Fin m → ℝ) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (x y : X) : (∑ j, r j • toReal (γ j)) x y = ∑ j, r j * (γ j x y : ℝ) := by
  simp [LinearMap.sum_apply, toReal_apply']

theorem castR_mem_rcone {n m : ℕ} (u : Fin m → Fin n → ℚ) (j : Fin m) :
    castR (u j) ∈ rcone (Finset.univ.image u) := by
  classical
  refine ⟨fun y => if y = u j then 1 else 0, fun y _ => by dsimp only; split_ifs <;> norm_num, ?_⟩
  simp [ite_smul]

end GlobalTheory.StarCover

namespace GlobalTheory.StarCover
open GlobalTheory.MinkWeylReal

theorem star_cover : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) →
    v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
      IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j)) := by
  classical
  intro X _ m γ v B hsym hpsd hv0 ⟨c, hc, hvc⟩ ⟨t, ht, hBt⟩
  obtain ⟨n, p, hp⟩ := exists_points γ
  set u : Fin m → Fin n → ℚ := fun j k => (γ j (p k).1 (p k).2 : ℚ) with hu
  set T := Finset.univ.image u with hT
  obtain ⟨A, hA⟩ := minkR T
  have hcomb : ∀ r : Fin m → ℝ, (∑ j, r j • castR (u j)) = fun k => ∑ j, r j * (γ j (p k).1 (p k).2 : ℝ) :=
    fun r => by funext k; simp [castR, u, Finset.sum_apply]
  have hv_app : ∀ x y, (v x y : ℝ) = ∑ j, c j * (γ j x y : ℝ) := fun x y => by
    rw [← toReal_apply', hvc, comb_apply]
  have hB_app : ∀ x y, B x y = ∑ j, t j * (γ j x y : ℝ) := fun x y => by rw [hBt, comb_apply]
  set Ev : Fin n → ℝ := ∑ j, c j • castR (u j) with hEv
  set EB : Fin n → ℝ := ∑ j, t j • castR (u j) with hEB
  have hEvT : Ev ∈ rcone T := mem_rcone_image u c hc
  have hEBT : EB ∈ rcone T := mem_rcone_image u t ht
  have hAv : ∀ a ∈ A, 0 ≤ dotR a Ev := (hA Ev).mp hEvT
  have hAB : ∀ a ∈ A, 0 ≤ dotR a EB := (hA EB).mp hEBT
  have hAu : ∀ a ∈ A, ∀ j, 0 ≤ a ⬝ᵥ u j := fun a ha j => by
    have := (hA _).mp (castR_mem_rcone u j) a ha
    rw [dotR_castR] at this
    exact_mod_cast this

  have hne : (A.filter fun a => 0 < dotR a Ev).Nonempty := by
    by_contra hno
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hno
    have hneg : (-1 : ℝ) • Ev ∈ rcone T := (hA _).mpr fun a ha => by
      rw [dotR_smul]; have := hno ha; push_neg at this; linarith
    obtain ⟨r, hr, hrEq⟩ := exists_of_mem_rcone_image u _ hneg
    have hzero : ∀ x y, ∑ j, (r j + c j) * (γ j x y : ℝ) = 0 := hp _ fun k => by
      have := congrFun hrEq k
      rw [hcomb r, hEv, hcomb c] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      simp only [add_mul, Finset.sum_add_distrib]; linarith
    have hvyy : ∀ y, v y y = 0 := fun y => by
      have h1 := hzero y y
      have h2 : ∀ j, 0 ≤ (γ j y y : ℝ) := fun j => by exact_mod_cast hpsd j y
      have h3 : ∑ j, c j * (γ j y y : ℝ) ≤ ∑ j, (r j + c j) * (γ j y y : ℝ) :=
        Finset.sum_le_sum fun j _ => by nlinarith [hr j, h2 j]
      have h4 : 0 ≤ ∑ j, c j * (γ j y y : ℝ) := Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (h2 j)
      have : (v y y : ℝ) = 0 := by rw [hv_app]; linarith
      exact_mod_cast this
    have hvs : ∀ x y, v x y = v y x := fun x y => by
      have : (v x y : ℝ) = v y x := by
        rw [hv_app, hv_app]; exact Finset.sum_congr rfl fun j _ => by rw [hsym j x y]
      exact_mod_cast this
    apply hv0
    refine LinearMap.ext₂ fun x y => ?_
    have := hvyy (x + y)
    simp only [map_add, LinearMap.add_apply, hvyy x, hvyy y, hvs y x] at this
    simp only [LinearMap.zero_apply]; omega
  obtain ⟨a, haF, hamin⟩ := Finset.exists_min_image _ (fun a => dotR a EB / dotR a Ev) hne
  obtain ⟨haA, hapos⟩ := Finset.mem_filter.mp haF
  set ts := dotR a EB / dotR a Ev with hts
  have hts0 : 0 ≤ ts := div_nonneg (hAB a haA) hapos.le
  have hB'T : EB - ts • Ev ∈ rcone T := (hA _).mpr fun a' ha' => by
    rw [dotR_sub, dotR_smul]
    by_cases hpos : 0 < dotR a' Ev
    · have := hamin a' (Finset.mem_filter.mpr ⟨ha', hpos⟩)
      rw [le_div_iff₀ hpos] at this
      linarith
    · push_neg at hpos; nlinarith [hAB a' ha']
  have hB'a : dotR a (EB - ts • Ev) = 0 := by
    rw [dotR_sub, dotR_smul, hts]; field_simp; ring
  obtain ⟨d, hd, hdEq⟩ := exists_of_mem_rcone_image u _ hB'T
  have hdz : ∀ j, d j * ((a ⬝ᵥ u j : ℚ) : ℝ) = 0 := by
    have := hB'a; rw [hdEq, dotR_comb] at this
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hd j)
      (by exact_mod_cast hAu a haA j))).mp this j (Finset.mem_univ j)
  obtain ⟨N, hN, z, hz⟩ := GordanGenProof.exists_int_multiple a
  let w : (X × X) →₀ ℤ := ∑ k, Finsupp.single (p k) (z k)
  let h := linW w
  have hh : ∀ β : LinearMap.BilinForm ℤ X, h β = ∑ k, z k * β (p k).1 (p k).2 := fun β => by
    simp only [h, linW_apply, w]
    rw [← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by ring)]
    simp [Finsupp.sum_single_index]
  have hzk : ∀ k, (z k : ℝ) = (N : ℝ) * (a k : ℝ) := fun k => by
    have := congrFun hz k
    simp only [GordanCones.toQ, Pi.smul_apply, smul_eq_mul] at this
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) this
    simpa using h2
  have hhR : ∀ β : LinearMap.BilinForm ℤ X, (h β : ℝ) = N * dotR a (fun k => (β (p k).1 (p k).2 : ℝ)) := fun β => by
    rw [hh]; push_cast; simp only [hzk, dotR, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hhγ : ∀ j, (h (γ j) : ℝ) = N * ((a ⬝ᵥ u j : ℚ) : ℝ) := fun j => by
    rw [hhR, ← dotR_castR]; congr 2
  have hhv : (h v : ℝ) = N * dotR a Ev := by
    rw [hhR]; congr 2; funext k; rw [hEv, hcomb c]; exact hv_app _ _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set Z := Finset.univ.filter fun j => h (γ j) = 0 with hZ
  let s : Fin Z.card ↪ Fin m := (Z.orderEmbOfFin rfl).toEmbedding
  have hsZ : ∀ j, j ∈ Set.range s ↔ j ∈ Z := fun j => by
    have := Finset.range_orderEmbOfFin Z rfl
    simp only [s, RelEmbedding.coe_toEmbedding]; rw [this]; rfl
  refine ⟨Z.card, s, h, ⟨fun j => ?_, fun j => ?_⟩, ?_, ?_⟩
  · have : (0 : ℝ) ≤ h (γ j) := by rw [hhγ]; exact mul_nonneg hNR.le (by exact_mod_cast hAu a haA j)
    exact_mod_cast this
  · rw [hsZ]; simp [Z]
  · have : (0 : ℝ) < h v := by rw [hhv]; exact mul_pos hNR hapos
    exact_mod_cast this
  · have hdZ : ∀ j, j ∉ Z → d j = 0 := fun j hj => by
      have hne' : h (γ j) ≠ 0 := by simpa [Z] using hj
      have : ((a ⬝ᵥ u j : ℚ) : ℝ) ≠ 0 := fun h0 => hne' (by
        have := hhγ j; rw [h0, mul_zero] at this; exact_mod_cast this)
      exact (mul_eq_zero.mp (hdz j)).resolve_right this
    have hsum : ∀ F : Fin m → (X →ₗ[ℤ] X →ₗ[ℤ] ℝ), ∑ i, d (s i) • F (s i) = ∑ j, d j • F j := fun F => by
      calc ∑ i, d (s i) • F (s i) = ∑ j ∈ Finset.univ.map s, d j • F j := (Finset.sum_map Finset.univ s (fun j => d j • F j)).symm
        _ = ∑ j ∈ Z, d j • F j := by
          congr 1; ext j; rw [← hsZ]; simp
        _ = ∑ j, d j • F j := Finset.sum_subset (Finset.subset_univ Z) (fun j _ hj => by rw [hdZ j hj, zero_smul])
    have hexp : ∀ e : X × X, ∑ j, (t j - ts * c j - d j) * (γ j e.1 e.2 : ℝ) =
        ∑ j, t j * (γ j e.1 e.2 : ℝ) - ts * ∑ j, c j * (γ j e.1 e.2 : ℝ) - ∑ j, d j * (γ j e.1 e.2 : ℝ) := fun e => by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have key : ∀ x y, ∑ j, (t j - ts * c j - d j) * (γ j x y : ℝ) = 0 := hp _ fun k => by
      have := congrFun hdEq k
      rw [hEB, hEv, hcomb, hcomb, hcomb] at this
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [hexp (p k)]; linarith
    refine ⟨Fin.cons ts fun i => d (s i), fun i => Fin.cases hts0 (fun i => hd _) i, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hsum (fun j => toReal (γ j))]
    refine LinearMap.ext₂ fun x y => ?_
    have k1 := key x y
    rw [hexp (x, y)] at k1
    rw [hB_app]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, toReal_apply', hv_app, comb_apply]
    linarith

end GlobalTheory.StarCover

example : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) → v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j)) := GlobalTheory.StarCover.star_cover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowReadingsSameRowsIdentifyDefiniteForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.R3.Rw.JmtUp

theorem agree {D : D7} {T : Type} {W : Type} [AddCommGroup W] [Module ℂ W] (U U' : D.what₂.Tup → Prop) {n : Fin D.R.m → T → ℕ}
    (tup tup' : T → D.what₂.Tup) (e1 : HEq tup' tup)
    (eM : ∀ (i : Fin D.R.m) t, (Fin (n i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (eM' : ∀ (i : Fin D.R.m) t, (Fin (n i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup' t) ((i : ℕ) + 1)) (e2 : HEq eM' eM)
    (i : Fin D.R.m) (val : ∀ t, (Fin (n i t) → D.what₂.LL) → W)
    (g : ∀ μ, U μ → D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] W) (g' : ∀ μ, U' μ → D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] W)
    (hs : ∀ t, Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t (Pi.single k 1))) = ⊤)
    (hg : ∀ t h y, g (tup t) h (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t y)) = val t y)
    (hg' : ∀ t h y, g' (tup' t) h (D.what₂.jMt (tup' t) ((i : ℕ) + 1) (eM' i t y)) = val t y)
    (μ : D.what₂.Tup) (τ : T) (hτ : tup τ = μ) (h : U μ) (h' : U' μ) (x : D.what₂.Mt μ ((i : ℕ) + 1)) : HEq (g' μ h' x) (g μ h x) := by
  cases e1
  cases e2
  subst hτ
  refine heq_of_eq (LinearMap.congr_fun (LinearMap.ext_on_range (hs τ) fun k => ?_) x)
  rw [hg, hg']

section Side

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

abbrev Val (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0) (i : Fin D.R.m) : Type :=
  GA D ((toLiftReal R F Y.tupT Y.hm Y.hTop Y.hinj).V i) → (toLiftReal R F Y.tupT Y.hm Y.hTop Y.hinj).TauV i

noncomputable def gOf (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0) (i : Fin D.R.m) (μ : D.what₂.Tup) (h : Used0 D μ) :
    D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] Val Y i := (Submodule.subtype _).comp (Y.IL.jMt μ h i).toLinearMap

theorem side (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0) (i : Fin D.R.m) (U : D.what₂.Tup → Prop) (tup : T → D.what₂.Tup) (e1 : HEq Y.tup tup)
    (eM : ∀ (i : Fin D.R.m) t, (Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (e2 : HEq Y.eMt eM) (g : ∀ μ, U μ → D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] Val Y i)
    (hs : ∀ t, Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t (Pi.single k 1))) = ⊤)
    (hg : ∀ t h y, g (tup t) h (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t y)) =
      R.extV i t (R.jV i t (GlobalTheory.Mem.R3.liftForm A3.A F.P0 F.ψ0 i t y)))
    (μ : D.what₂.Tup) (τ : T) (hτ : tup τ = μ) (h : U μ) (h' : Used0 D μ) (x : D.what₂.Mt μ ((i : ℕ) + 1)) :
    HEq (gOf Y i μ h' x) (g μ h x) :=
  agree U (Used0 D) tup Y.tup e1 eM Y.eMt e2 i _ g (gOf Y i) hs hg (fun t h y => Y.mtRead i t h y) μ τ hτ h h' x

end Side

theorem jMt_rowsSame : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1 := by
  intro K B f T w Z Wt S' N h p0 t p0' t' hs μ hμ hμ' i x
  have H := side t'.r.Y ((by with_unfolding_all exact (i :)))
  have a1 := hs.tup
  have a2 := hs.eMt
  cases t' with | mk hX' r' exAt' inGeo' grpAt' grp' mu' exact' untw' emt0' emt' etaF' rowInt' idx' => ?_
  cases r' with | mk z' holds' Y' ZZ' tupix' => ?_
  cases z' with | mk Xg' tr' core' alg_eq' R' cG' geo' pins' lev' idG' good' muz' le' ks' => ?_
  rename_i alg'
  have e1 : Xg' = t.r.z.Xg := hs.Xg
  have e2 : tr' = t.r.z.tr := hs.tr
  subst e1 e2
  have e3 : core' = R3.Tr.coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) t.r.z.core := eq_of_heq hs.core
  subst e3
  have e4 : alg' = t.r.z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.D Z).what₂.embLL.injective
    exact (alg_eq' y).trans (t.r.z.alg_eq y).symm
  subst e4
  have e5 : R' = R3.Tr.real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.R := eq_of_heq hs.R
  subst e5
  have e6 : cG' = t.r.z.cG := eq_of_heq hs.cG
  subst e6
  exact (by with_unfolding_all exact ((H ((by with_unfolding_all exact ((Formalism.IndefR.RecTie.Used0 (w.D Z)) :))) ((by with_unfolding_all exact (t.r.Y.tup :))) ((by with_unfolding_all exact (a1 :))) ((by with_unfolding_all exact (t.r.Y.eMt :))) ((by with_unfolding_all exact (a2 :))) ((by with_unfolding_all exact ((gOf t.r.Y i) :)))
    ((by with_unfolding_all exact ((fun τ => (t.r.Y.formsL i τ).span) :))) ((by with_unfolding_all exact ((t.r.Y.mtRead i) :))) ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact ((t.r.Y.tupT μ) :))) ((by with_unfolding_all exact ((t.r.Y.tupTie μ hμ) :))) ((by with_unfolding_all exact (hμ :)))
    ((by with_unfolding_all exact (hμ' :))) ((by with_unfolding_all exact (x :)))) :))

end GlobalTheory.Mem.R3.Rw.JmtUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimplicialLabellingOfBarycentricStageZeroStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab φ : InvFun O), IsCarrierDim bar q ψ lab → IsBaryStage bar q ψ lab φ 0 → SimpLab bar q φ lab := by
  first | exact @GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero | exact GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero | (intros; apply GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecOfAnypoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.CarrySpec

theorem upper_mul {n : ℕ} {R : Type} [CommRing R] {M N : Matrix (Fin n) (Fin n) R}
    (hM : ∀ a i, i < a → M a i = 0) (hN : ∀ a i, i < a → N a i = 0) :
    (∀ a i, i < a → (M * N) a i = 0) ∧ ∀ i, (M * N) i i = M i i * N i i := by
  first
  | exact @_root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul
  | exact _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul
  | (apply _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul ..)

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (ρ : R →+* R') (ψ : R' →+* R'') :
    spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by
  simp [spMap, Spec.map_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {f'' : EigFrame Z φ'' x''} {ρ : R →+* R'} {ψ : R' →+* R''}
    (h1 : f.IsMap ρ f') (h2 : f'.IsMap ψ f'') : f.IsMap (ψ.comp ρ) f'' := fun τ i => by
  rw [h2 τ i, h1 τ i, GlobalTheory.ShFam.CarriesAt.spMap_dualMap_comp, Category.assoc]

theorem tri_of_co {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X}
    {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'} (hf : f.IsMap ψ f')
    (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ)
    (hu : ∀ τ a i, i < a → f'.co g τ a i = 0) (hd : ∀ τ i, f'.co g τ i i = t τ i) : f.Tri ψ g t :=
  ⟨hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, hd τ i, fun k hk => hu τ k i hk, by
    have := f'.co_spec g τ i
    rwa [funext (hf τ)] at this⟩⟩

theorem tri_spec {R V L k : Type} [CommRing R] [CommRing V] [CommRing L] [CommRing k]
    {φ₁ : c.F →+* R} {x₁ : Sp R ⟶ Z.X} (f : EigFrame Z φ₁ x₁) (ρ : R →+* V) (ν : V →+* L)
    (hν : Function.Injective ν) (r : V →+* k) {φV : c.F →+* V} {xV : Sp V ⟶ Z.X} (hxV : xV = spMap ρ ≫ x₁)
    (gV : EigFrame Z φV xV) {φL : c.F →+* L} {xL : Sp L ⟶ Z.X} (gL : EigFrame Z φL xL)
    (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (hL : gV.Tri ν gL tL)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (hfL : f.Tri (ν.comp ρ) gL t')
    {φk : c.F →+* k} {xk : Sp k ⟶ Z.X} (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ)
    (hk : gV.Tri r gk tk) : ∃ t'' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri (r.comp ρ) gk t'' := by
  have hφV : φV = ρ.comp φ₁ := RingHom.ext fun a => hν (by
    have := RingHom.congr_fun (hL.2.1.symm.trans hfL.2.1) a
    simpa using this)
  obtain ⟨h, hh⟩ := EigFrame.exists_isMap f ρ hφV hxV
  obtain ⟨gVL, hgVL⟩ := EigFrame.exists_isMap gV ν hL.2.1 hL.1
  obtain ⟨hLf, hhL⟩ := EigFrame.exists_isMap h ν hL.2.1 hL.1
  have hfhL : f.IsMap (ν.comp ρ) hLf := isMap_comp hh hhL

  have hA : ∀ τ, (∀ a i, i < a → h.co gV τ a i = 0) := fun τ a i hia => by
    obtain ⟨hU, -⟩ := EigFrame.Tri.co τ hfL hfhL
    obtain ⟨hW, -⟩ := EigFrame.Tri.co τ hL hgVL
    have hmap := EigFrame.IsMap.co τ hhL hgVL hL.1
    have hmul := EigFrame.co_mul hLf gVL gL τ
    have hWu := EigFrame.isUnit_det_co gVL gL τ
    set W := gVL.co gL τ
    have hWt : W.BlockTriangular id := fun a b h => hW a b h
    letI := Matrix.invertibleOfIsUnitDet W hWu
    have hWi : W⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hWt
    have hM : hLf.co gVL τ = hLf.co gL τ * W⁻¹ := by
      rw [← hmul, Matrix.mul_nonsing_inv_cancel_right _ _ hWu]
    have hP : (hLf.co gL τ * W⁻¹).BlockTriangular id :=
      Matrix.BlockTriangular.mul (fun a b h => hU a b h) hWi
    apply hν
    have := hP hia
    rw [← hM, hmap, Matrix.map_apply] at this
    rw [this, map_zero]
  have hAd : ∀ τ i, IsUnit (h.co gV τ i i) := fun τ i => by
    have hdet := EigFrame.isUnit_det_co h gV τ
    rw [Matrix.det_of_upperTriangular (fun a b hab => hA τ a b hab)] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => h.co gV τ j j) (Finset.mem_univ i)) hdet

  obtain ⟨hkf, hhk⟩ := EigFrame.exists_isMap h r hk.2.1 hk.1
  obtain ⟨gVk, hgVk⟩ := EigFrame.exists_isMap gV r hk.2.1 hk.1
  have hfhk : f.IsMap (r.comp ρ) hkf := isMap_comp hh hhk
  have hco : ∀ τ, hkf.co gk τ = (h.co gV τ).map r * gVk.co gk τ := fun τ => by
    rw [← EigFrame.IsMap.co τ hhk hgVk hk.1, EigFrame.co_mul]
  have key : ∀ τ, (∀ a i, i < a → hkf.co gk τ a i = 0) ∧ ∀ i, hkf.co gk τ i i = r (h.co gV τ i i) * tk τ i := by
    intro τ
    obtain ⟨hN, hNd⟩ := EigFrame.Tri.co τ hk hgVk
    have hm := upper_mul (M := (h.co gV τ).map r) (fun a i hia => by rw [Matrix.map_apply, hA τ a i hia, map_zero]) hN
    rw [hco]
    exact ⟨hm.1, fun i => by rw [hm.2, Matrix.map_apply, hNd]⟩
  refine ⟨fun τ i => ((hAd τ i).map r).unit * tk τ i, tri_of_co hfhk ?_ ?_ _ (fun τ => (key τ).1) fun τ i => ?_⟩
  · rw [hk.1, hxV, spMap_comp, Category.assoc]
  · rw [hk.2.1, hφV, RingHom.comp_assoc]
  · rw [(key τ).2, Units.val_mul, IsUnit.unit_spec]

end GlobalTheory.CarrySpec

namespace GlobalTheory.CarrySpec

open MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem spec_of_anypoint (hany : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t') : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V _ _ L _ ν hν k _ r _ q φV xV hxV gV φL xL gL tL hL hcar φk xk gk tk hk
  set y₀ := q (IsLocalRing.closedPoint V)
  set ρ := (Scheme.stalkClosedPointTo (R := CommRingCat.of V) q).hom
  have hq : spMap ρ ≫ stalkPt C.Y y₀ = q := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of V) q
  obtain ⟨φ₁, f, t, hf, -⟩ := C.gr_spec y₀
  have hpL : spMap ν ≫ q = spMap (ν.comp ρ) ≫ stalkPt C.Y y₀ :=
    (congrArg (spMap ν ≫ ·) hq).symm.trans (by rw [spMap_comp, Category.assoc])
  obtain ⟨t', hfL⟩ := hany E H Dw l Xo c O β Z F e C L φL xL gL (spMap ν ≫ q) hcar y₀ (ν.comp ρ) φ₁ f t hpL hf
  have hxV' : xV = spMap ρ ≫ (stalkPt C.Y y₀ ≫ C.π ≫ genι Z) :=
    hxV.trans ((congrArg (· ≫ C.π ≫ genι Z) hq).symm.trans (Category.assoc _ _ _))
  obtain ⟨t'', htri⟩ := tri_spec f ρ ν hν r hxV' gV gL tL hL t' hfL gk tk hk
  exact ⟨y₀, r.comp ρ, φ₁, f, t, t'',
    (congrArg (spMap r ≫ ·) hq).symm.trans (by rw [spMap_comp, Category.assoc]), hf, htri⟩

end GlobalTheory.CarrySpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkMapInjectiveBirationalStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_map_injective_birational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → ∀ z : Z.X, Function.Injective (π.stalkMap z).hom ∧ ∀ b : Z.X.presheaf.stalk z, ∃ a s : X.X.presheaf.stalk (π z), (π.stalkMap z).hom s ≠ 0 ∧ (π.stalkMap z).hom s * b = (π.stalkMap z).hom a := by
  first | exact @GlobalTheory.ChartBir.stalkMap_birational | exact GlobalTheory.ChartBir.stalkMap_birational | (intros; apply GlobalTheory.ChartBir.stalkMap_birational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrictlyConcavePolFanConeRealFormsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictlyConcave_polFan_cone_real_forms : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → IsCone (id : ℤ → ℤ) φ u → StrictWith (id : ℤ → ℤ) φ N (linW w) u → (∀ B ∈ rcone u, (N : ℝ) * evalR φ B = evalW w B) ∧ ∀ B ∈ psdCone (id : ℤ → ℤ) X, (N : ℝ) * evalR φ B ≤ evalW w B ∧ ((N : ℝ) * evalR φ B = evalW w B → B ∈ rcone u) := by
  first | exact @GlobalTheory.PolCell.strictWith_real | exact GlobalTheory.PolCell.strictWith_real | (intros; apply GlobalTheory.PolCell.strictWith_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharEqOfEqOnTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionChar_eq_of_eq_on_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q : ℕ), q ≠ 0 → ∀ c c' : TorsChar t x q, (∀ w : Over.mk (spMap (algebraMap ↥(intO C) ↥(intO C)) ≫ x) ⟶ t.G, w ^ q = 1 → c.χ ↥(intO C) w = c'.χ ↥(intO C) w) → ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c.χ B w = c'.χ B w := by
  first | exact @GlobalTheory.CharUniq.char_unique | exact GlobalTheory.CharUniq.char_unique | (intros; apply GlobalTheory.CharUniq.char_unique <;> assumption)
end

