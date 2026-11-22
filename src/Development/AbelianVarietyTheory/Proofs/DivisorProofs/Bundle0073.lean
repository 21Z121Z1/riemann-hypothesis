import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRealCoordinateBasis
section
open Module

theorem GlobalTheory.exists_zlattice_basis_realCoord_integral : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∃ (n : ℕ) (b : Fin n → Λ) (c : Fin n → (Fin g → ℂ) →ₗ[ℝ] ℝ),
      (∀ v, ∑ i, c i v • ((b i : Λ) : Fin g → ℂ) = v) ∧
      ∀ (φ : Λ →+ (Fin g → ℂ)) (x : Λ), ∑ i, c i (x : Fin g → ℂ) • φ (b i) = φ x := by
  intro g Λ hd hs
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let bZ0 := Module.Free.chooseBasis ℤ Λ
  let bZ := bZ0.reindex (Fintype.equivFin _)
  let bR := bZ.ofZLatticeBasis ℝ Λ
  refine ⟨_, fun i => bZ i, fun i => bR.coord i, ?_, ?_⟩
  · intro v
    have h := bR.sum_repr v
    conv_rhs => rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [bR]
  · intro φ x
    have hx : ∀ i, bR.coord i (x : Fin g → ℂ) = ((bZ.repr x i : ℤ) : ℝ) := by
      intro i
      simp [bR, Module.Basis.ofZLatticeBasis_repr_apply]
    simp_rw [hx]
    conv_rhs => rw [← bZ.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul, map_zsmul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeShiftedCutoffSummable
section
noncomputable section

namespace GlobalTheory.LatticeSchwartz

theorem summable_one_add_norm_inv_pow' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ}
    (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

theorem term_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h f : SchwartzMap V ℂ) (k N j m : ℕ) (x l : V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ m f (x - l)‖ ≤
      (2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
      (2 ^ N * (Finset.Iic (N, m)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f) *
      ((1 + ‖l‖)⁻¹) ^ N := by
  have hA := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, j)) le_rfl le_rfl h x
  have hB := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, m)) le_rfl le_rfl f (x - l)
  have hc : 1 + ‖l‖ ≤ (1 + ‖x‖) * (1 + ‖x - l‖) := by
    have : ‖l‖ ≤ ‖x‖ + ‖x - l‖ := by
      calc ‖l‖ = ‖x - (x - l)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - l‖ := norm_sub_le _ _
    nlinarith [norm_nonneg x, norm_nonneg (x - l)]
  have hc0 : 0 < 1 + ‖l‖ := by positivity
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
  set P := ‖iteratedFDeriv ℝ j h x‖
  set Q := ‖iteratedFDeriv ℝ m f (x - l)‖
  have hP : 0 ≤ P := norm_nonneg _
  have hQ : 0 ≤ Q := norm_nonneg _
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖x‖ ^ k * P * Q * (1 + ‖l‖) ^ N
      ≤ (1 + ‖x‖) ^ k * P * Q * ((1 + ‖x‖) * (1 + ‖x - l‖)) ^ N := by gcongr
    _ = ((1 + ‖x‖) ^ (k + N) * P) * ((1 + ‖x - l‖) ^ N * Q) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := by gcongr

theorem summable_seminorm_mul_comp_sub : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h x * f (x - l)) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  intro V _ _ _ Λ _ _ h f _ u hu k n
  set N := Module.finrank ℤ Λ + 1 with hN
  have hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N :=
    summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)
  set D : ℕ → ℝ := fun j => (n.choose j : ℝ) *
      ((2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
      (2 ^ N * (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by
    have h1 : 0 ≤ (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h := apply_nonneg _ _
    have h2 : 0 ≤ (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f := apply_nonneg _ _
    positivity
  set C := ∑ j ∈ Finset.range (n + 1), D j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => hD0 j
  refine Summable.of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_) (hw.mul_left C)
  refine SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) fun x => ?_
  have hul : (u l : V → ℂ) = fun y => h y * f (y - l) := funext (hu l)
  rw [hul]
  have hg : ContDiff ℝ n (fun y : V => f (y - (l : V))) :=
    (f.smooth n).comp (contDiff_id.sub contDiff_const)
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (h.smooth n) hg x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_sub] at hL
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h y * f (y - l)) x‖
      ≤ ‖x‖ ^ k * ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖ := by
        gcongr
    _ = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ Finset.range (n + 1), D j * ((1 + ‖(l : V)‖)⁻¹) ^ N := by
        refine Finset.sum_le_sum fun j _ => ?_
        have ht := term_le h f k N j (n - j) x l
        have hch : (0 : ℝ) ≤ n.choose j := Nat.cast_nonneg _
        calc (n.choose j : ℝ) *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖)
            ≤ (n.choose j : ℝ) * ((2 ^ (k + N) * (Finset.Iic (k + N, j)).sup
                (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
              (2 ^ N * (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f) *
              ((1 + ‖(l : V)‖)⁻¹) ^ N) := mul_le_mul_of_nonneg_left ht hch
          _ = D j * ((1 + ‖(l : V)‖)⁻¹) ^ N := by rw [hD]; ring
    _ = C * ((1 + ‖l‖)⁻¹) ^ N := by rw [hC, Finset.sum_mul]; rfl

end GlobalTheory.LatticeSchwartz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeTranslatesCutoffSummable
section
open SchwartzMap

noncomputable section

namespace GlobalTheory.SchwartzTranslateSum

theorem summable_one_add_norm_inv_pow' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] {N : ℕ}
    (hN : Module.finrank ℤ Λ < N) : Summable fun z : Λ => ((1 + ‖z‖)⁻¹) ^ N := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv Λ N hN).add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

theorem summable_seminorm_mul_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (h f : SchwartzMap V ℂ) (hh : HasCompactSupport h)
    (u : Λ → SchwartzMap V ℂ) (hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x) (k n : ℕ) :
    Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall (0 : V)
  set N := Module.finrank ℤ Λ + 1 with hNdef
  have hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N :=
    summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)
  set S := (Finset.Iic (k + N, n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f
    with hSdef
  set A := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h
    with hAdef
  set R' := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set D := (1 + R') ^ N * 2 ^ (k + N) * S with hDdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  have hD0 : 0 ≤ D := by positivity
  clear_value D A S R' N
  refine (hw.mul_left (A * D)).of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_)
  refine SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) (fun x => ?_)
  have hfun : (u l : V → ℂ) = fun y => h (y + l) * f y := funext (hu l)
  rw [hfun]
  have hsh : ContDiff ℝ n (fun y => h (y + (l : V))) :=
    ((h.smooth ⊤).of_le (by exact_mod_cast le_top)).comp (contDiff_id.add contDiff_const)
  have hsf : ContDiff ℝ n (f : V → ℂ) := (f.smooth ⊤).of_le (by exact_mod_cast le_top)
  have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hsh hsf x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_add_right] at hleib
  by_cases hx : x + (l : V) ∈ tsupport h
  · have hxl : ‖x + (l : V)‖ ≤ R' := by
      have := hR hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (hR'def ▸ le_max_left _ _)
    have hl : 1 + ‖l‖ ≤ (1 + R') * (1 + ‖x‖) := by
      have : ‖(l : V)‖ ≤ ‖x + (l : V)‖ + ‖x‖ := by
        calc ‖(l : V)‖ = ‖(x + (l : V)) - x‖ := by simp
          _ ≤ ‖x + (l : V)‖ + ‖x‖ := norm_sub_le _ _
      have hn' : ‖l‖ = ‖(l : V)‖ := rfl
      nlinarith [norm_nonneg x]
    have hB : ∀ m ≤ n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ ≤ D * ((1 + ‖l‖)⁻¹) ^ N := by
      intro m hm
      have h1 := one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, n)) (k := k + N) (n := m)
        le_rfl hm f x
      have h1' : (1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖ ≤ 2 ^ (k + N) * S := by rw [hSdef]; exact h1
      have hpos : 0 < (1 + ‖l‖) ^ N := by positivity
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ * (1 + ‖l‖) ^ N
          ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ m f x‖ * ((1 + R') * (1 + ‖x‖)) ^ N := by
            gcongr
            linarith [norm_nonneg x]
        _ = (1 + R') ^ N * ((1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖) := by
            rw [mul_pow, pow_add]; ring
        _ ≤ (1 + R') ^ N * (2 ^ (k + N) * S) := by gcongr
        _ = D := by rw [hDdef]; ring
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖
        ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i h (x + l)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i h (x + l)‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h *
            (D * ((1 + ‖l‖)⁻¹) ^ N) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul (mul_le_mul_of_nonneg_left
              (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ h i _) (by positivity))
              (hB _ (Nat.sub_le _ _)) (by positivity) (by positivity)
      _ = A * D * ((1 + ‖l‖)⁻¹) ^ N := by
            rw [hAdef, Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
  · have hz : ∀ i, iteratedFDeriv ℝ i h (x + l) = 0 := fun i =>
      Function.notMem_support.1 fun hm => hx (support_iteratedFDeriv_subset i hm)
    simp only [hz, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] at hleib
    have : ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖ = 0 :=
      le_antisymm hleib (norm_nonneg _)
    rw [this, mul_zero]
    exact mul_nonneg (mul_nonneg hA0 hD0) (by positivity)

end GlobalTheory.SchwartzTranslateSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorPairingOneIdealMultiple
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_section_of_fractionalIdeal_values {F V : Type} [Field F] [NumberField F]
    [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L)
    (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) {v : V} (K : FractionalIdeal (𝓞 F)⁰ F)
    (hK : K ≠ 0) (hKL : ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) :
    ∃ w : V, B w v = 1 ∧ ∀ t ∈ K, t • w ∈ L := by
  have hmul : K * K⁻¹ = 1 := mul_inv_cancel₀ hK
  have key : ∀ s ∈ K * K⁻¹, ∃ w : V, B w v = s ∧ ∀ t ∈ K, t • w ∈ L := by
    intro s hs
    refine FractionalIdeal.mul_induction_on hs ?_ ?_
    · intro k hk k' hk'
      obtain ⟨z, hz, rfl⟩ := (hKL k).1 hk
      refine ⟨k' • z, by simp [mul_comm], fun t ht => ?_⟩
      have h1 : t * k' ∈ K * K⁻¹ := FractionalIdeal.mul_mem_mul ht hk'
      rw [hmul, FractionalIdeal.mem_one_iff] at h1
      obtain ⟨r, hr⟩ := h1
      rw [smul_smul, ← hr]
      exact hLsmul r z hz
    · rintro x y ⟨w, hw, hw'⟩ ⟨u, hu, hu'⟩
      refine ⟨w + u, by simp [hw, hu], fun t ht => ?_⟩
      rw [smul_add]
      exact hLadd _ (hw' t ht) _ (hu' t ht)
  refine key 1 ?_
  rw [hmul]
  exact FractionalIdeal.one_mem_one _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra
section
open PowerSeries

namespace GlobalTheory

theorem inv_mulVec_coord_eq_zero_of_adapted_columns_injective {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (hφ : Function.Injective φ) (n : ℕ) (W : Submodule K (Fin n → K))
    (g : (Matrix (Fin n) (Fin n) R)ˣ)
    (hg : ∀ j : Fin n, (j : ℕ) < Module.finrank K W →
      (fun a => φ ((g : Matrix (Fin n) (Fin n) R) a j)) ∈ W)
    (y : Fin n → R) (hy : (fun a => φ (y a)) ∈ W)
    (a : Fin n) (ha : Module.finrank K W ≤ (a : ℕ)) :
    (((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).mulVec y) a = 0 := by
  classical
  have hr : Module.finrank K W ≤ n := by
    have := Submodule.finrank_le W
    simpa using this
  set r := Module.finrank K W with hrdef
  let G : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) R).map φ
  let H : Matrix (Fin n) (Fin n) K := ((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).map φ
  have hHG : H * G = 1 := by
    calc H * G = (RingHom.mapMatrix φ) (((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R)) :=
          ((RingHom.mapMatrix φ).map_mul _ _).symm
      _ = 1 := by rw [Units.inv_mul, map_one]
  let e : Fin r → (Fin n → K) := fun i => Pi.single (Fin.castLE hr i) 1
  let v : Fin r → (Fin n → K) := fun i => fun b => G b (Fin.castLE hr i)
  have hHv : ∀ i, H.mulVec (v i) = e i := by
    intro i
    have : v i = G.mulVec (Pi.single (Fin.castLE hr i) 1) := by
      ext b; simp [v, Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
  have hcomp : (Matrix.toLin' H) ∘ v = e := by
    funext i; simp only [Function.comp_apply, Matrix.toLin'_apply, hHv]
  have hli : LinearIndependent K v := by
    apply LinearIndependent.of_comp (Matrix.toLin' H)
    rw [hcomp]
    exact (Pi.linearIndependent_single_one (Fin n) K).comp _ (Fin.castLE_injective hr)
  have hle : Submodule.span K (Set.range v) ≤ W := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact hg (Fin.castLE hr i) (by simp)
  have heq : Submodule.span K (Set.range v) = W := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hy' : (fun b => φ (y b)) ∈ Submodule.span K (Set.range v) := heq ▸ hy
  have hmap : H.mulVec (fun b => φ (y b)) ∈ Submodule.span K (Set.range e) := by
    have := Submodule.mem_map_of_mem (f := Matrix.toLin' H) hy'
    rw [Submodule.map_span, ← Set.range_comp, hcomp, Matrix.toLin'_apply] at this
    exact this
  have hker : Submodule.span K (Set.range e) ≤ LinearMap.ker (LinearMap.proj a) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, e]
    apply Pi.single_eq_of_ne
    intro h
    have : ((Fin.castLE hr i : Fin n) : ℕ) = a := by rw [h]
    simp at this
    omega
  have h0 : (H.mulVec (fun b => φ (y b))) a = 0 := hker hmap
  have hcoe : φ ((((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).mulVec y) a) =
      (H.mulVec (fun b => φ (y b))) a := by
    rw [RingHom.map_mulVec]
    rfl
  rw [h0] at hcoe
  exact (injective_iff_map_eq_zero φ).mp hφ _ hcoe

theorem adapted_coords_vanish (F : Type) [Field F] (n : ℕ)
    (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
    (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ)
    (hg : ∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W)
    (y : Fin n → PowerSeries F) (hy : (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W)
    (a : Fin n) (ha : Module.finrank (LaurentSeries F) W ≤ (a : ℕ)) :
    (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 :=
  inv_mulVec_coord_eq_zero_of_adapted_columns_injective (HahnSeries.ofPowerSeries ℤ F) HahnSeries.ofPowerSeries_injective n W g hg y hy a ha

theorem adapted_coords_vanish_stmt : ∀ (F : Type) [Field F] (n : ℕ) (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ), (∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W) → ∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W → ∀ a : Fin n, Module.finrank (LaurentSeries F) W ≤ (a : ℕ) → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 :=
  fun F _ n W g hg y hy a ha => adapted_coords_vanish F n W g hg y hy a ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeAddMulLogSqOfLeAddMulLog
section
open Filter Topology

namespace GlobalTheory

theorem le_add_mul_log_sq_of_le_add_mul_log :
    ∀ (α β r s : ℝ), 0 ≤ α → 0 ≤ β → 1 ≤ r → r ≤ s → s ≤ α + β * Real.log r →
      s ≤ α + β * Real.log ((α + 2 * β + 1) ^ 2) := by
  intro α β r s hα hβ hr hrs hs
  have hr0 : 0 < r := by linarith
  set t := Real.sqrt r with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg r
  have htt : t * t = r := Real.mul_self_sqrt hr0.le
  have ht1 : 1 ≤ t := by
    by_contra h
    push_neg at h
    nlinarith
  have htpos : 0 < t := by linarith
  have hlog : Real.log r ≤ 2 * t - 2 := by
    have h1 : Real.log r = 2 * Real.log t := by
      rw [← htt, Real.log_mul htpos.ne' htpos.ne']; ring
    have h2 := Real.log_le_sub_one_of_pos htpos
    linarith
  have hle : t ≤ α + 2 * β + 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_left h htpos, mul_nonneg hα (sub_nonneg.mpr ht1),
      mul_le_mul_of_nonneg_left hlog hβ]
  have hrc : r ≤ (α + 2 * β + 1) ^ 2 := by
    rw [← htt]; nlinarith
  have hl : Real.log r ≤ Real.log ((α + 2 * β + 1) ^ 2) := Real.log_le_log hr0 hrc
  nlinarith [mul_le_mul_of_nonneg_left hl hβ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMulSetIntegralImage2OfForallLe
section
open MeasureTheory

namespace GlobalTheory

theorem le_mul_setIntegral_image2_of_forall_le (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : ℕ)
    (Θ : (Fin N → ℝ) → G) (Q : Set (Fin N → ℝ)) (B : Set G) (K : ℝ)
    (hΘ : Continuous Θ) (hQ : IsCompact Q) (hB : IsCompact B) (hB1 : B ∈ nhds (1 : G))
    (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : G → ℝ) (a : ℝ), Continuous F → (∀ g, 0 ≤ F g) →
      (∀ x ∈ B, a ≤ K * ∫ t in Q, F (Θ t * x)) →
      a ≤ C * ∫ x in Set.image2 (fun t b => Θ t * b) Q B, F x ∂μ := by
  have hBfin : μ B ≠ ⊤ := hB.measure_lt_top.ne
  have hQfin : (volume : Measure (Fin N → ℝ)) Q ≠ ⊤ := hQ.measure_lt_top.ne
  have hBpos : 0 < μ.real B :=
    ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds μ hB1).ne' hBfin
  refine ⟨K * (volume : Measure (Fin N → ℝ)).real Q / μ.real B, by positivity, ?_⟩
  intro F a hF hF0 ha
  set Ω : Set G := Set.image2 (fun t b => Θ t * b) Q B with hΩdef
  have hΩ : IsCompact Ω := by
    rw [hΩdef, ← Set.image_prod]
    exact (hQ.prod hB).image (by fun_prop)
  have hFΩ : IntegrableOn F Ω μ := hF.continuousOn.integrableOn_compact hΩ
  have hstep : ∀ t ∈ Q, ∫ x in B, F (Θ t * x) ∂μ ≤ ∫ x in Ω, F x ∂μ := by
    intro t ht
    rw [← (measurePreserving_mul_left μ (Θ t)).setIntegral_image_emb
      (measurableEmbedding_mulLeft (Θ t)) F B]
    refine setIntegral_mono_set hFΩ (Filter.Eventually.of_forall hF0) ?_
    refine HasSubset.Subset.eventuallyLE ?_
    rintro _ ⟨b, hb, rfl⟩
    exact Set.mem_image2_of_mem ht hb
  have hint : Integrable (Function.uncurry fun (x : G) (t : Fin N → ℝ) => F (Θ t * x))
      ((μ.restrict B).prod (volume.restrict Q)) := by
    rw [Measure.prod_restrict]
    refine ContinuousOn.integrableOn_compact (hB.prod hQ) ?_
    exact (by fun_prop : Continuous fun p : G × (Fin N → ℝ) => F (Θ p.2 * p.1)).continuousOn
  have h1 : μ.real B * a ≤ ∫ x in B, K * ∫ t in Q, F (Θ t * x) ∂volume ∂μ := by
    have hc : μ.real B * a = ∫ _x in B, a ∂μ := by simp
    rw [hc]
    refine setIntegral_mono_on (integrableOn_const hBfin) ?_ hB.measurableSet ha
    exact hint.integral_prod_left.const_mul K
  have h2 : ∫ x in B, ∫ t in Q, F (Θ t * x) ∂volume ∂μ ≤
      (volume : Measure (Fin N → ℝ)).real Q * ∫ x in Ω, F x ∂μ := by
    rw [integral_integral_swap hint]
    have hc : (volume : Measure (Fin N → ℝ)).real Q * ∫ x in Ω, F x ∂μ =
        ∫ _t in Q, (∫ x in Ω, F x ∂μ) := by simp
    rw [hc]
    exact setIntegral_mono_on hint.integral_prod_right (integrableOn_const hQfin)
      hQ.measurableSet hstep
  rw [integral_const_mul] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hBpos, mul_comm a, mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeNatCastOfAddOneLe
section
namespace GlobalTheory.NatCastUpperBound

theorem le_natCast_of_add_one_le {a : WithBot ℕ∞} {n : ℕ}
    (h : a + (1 : WithBot ℕ∞) ≤ (↑(n + (1 : ℕ)) : WithBot ℕ∞)) :
    a ≤ (↑n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [h1, h2, WithBot.coe_le_coe, top_le_iff] at h
      exact ENat.coe_ne_top _ h
    | coe m =>
      have h1 : ((m : ℕ∞) : WithBot ℕ∞) + 1 = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      have h3 : ((n : ℕ) : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [h1, h2, WithBot.coe_le_coe, ENat.coe_le_coe] at h
      rw [h3, WithBot.coe_le_coe, ENat.coe_le_coe]
      omega

end GlobalTheory.NatCastUpperBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentComplexMap
section
open Matrix

namespace GlobalTheory

theorem linearIndependent_real_map_of_fieldEmb {E : Type} [Field E] {r n : ℕ} (τ : E →+* ℂ)
    (e : Fin n → Matrix (Fin r) (Fin r) E) (he : LinearIndependent E e) :
    LinearIndependent ℝ (fun i => (e i).map τ) := by
  letI : Algebra E ℂ := τ.toAlgebra
  have h1 : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[E] e i) :=
    Module.Flat.linearIndependent_one_tmul he
  let j := (matrixEquivTensor (Fin r) E ℂ).symm
  have hc : ∀ (c : ℂ) (x : TensorProduct E ℂ (Matrix (Fin r) (Fin r) E)),
      j (c • x) = c • j x := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a M =>
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      simp only [j, matrixEquivTensor_apply_symm, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  have h2 : LinearIndependent ℂ (j.toRingEquiv.toAddEquiv.toAddMonoidHom ∘
      fun i => (1 : ℂ) ⊗ₜ[E] e i) :=
    h1.map_of_injective_injective id _ (fun _ h => h)
      (fun m hm => by simpa using hm) (fun c x => hc c x)
  have h3 : (j.toRingEquiv.toAddEquiv.toAddMonoidHom ∘ fun i => (1 : ℂ) ⊗ₜ[E] e i) =
      fun i => (e i).map τ := by
    funext i
    simp only [Function.comp_apply]
    show j ((1 : ℂ) ⊗ₜ[E] e i) = _
    simp only [j, matrixEquivTensor_apply_symm, one_smul]
    rfl
  rw [h3] at h2
  exact h2.restrict_scalars' ℝ

end GlobalTheory
end

