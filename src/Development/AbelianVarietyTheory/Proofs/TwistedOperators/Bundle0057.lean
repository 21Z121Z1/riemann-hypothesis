import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistSupportPeriodicLevels
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.Proof.TwistSupportPeriodicLevels

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_latOf_eq {Y : Type} [Fintype Y] [DecidableEq Y] {g : GL Y k} (h : latOf g = latOf 1) :
    g ∈ KO k Y := by
  have h1 := latOf_le_iff.mp h.le
  have h2 := latOf_le_iff.mp h.ge
  simp only [inv_one, one_mul, mul_one] at h1 h2
  exact mem_KO.mpr ⟨h1, h2⟩

variable {r s s' : Type} [Fintype r] [DecidableEq r]

theorem intM_of_parPhi_ne_zero (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} (hx : parPhi δ x ≠ 0) : IntM x := by
  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  rw [← Matrix.fromBlocks_toBlocks x, intM_fromBlocks]
  refine ⟨?_, h12, h21.intM, h22⟩
  rw [← e]
  exact intM_of_mem_KO hg

private theorem parPhi_add_eq_of_maxM {δ : kˣ →* ℂˣ} (hδ : IsTame δ) {x y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) (hx : parPhi δ x ≠ 0) : parPhi δ (x + y) = parPhi δ x := by

  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  have hyb : MaxM (Matrix.fromBlocks y.toBlocks₁₁ y.toBlocks₁₂ y.toBlocks₂₁ y.toBlocks₂₂) := by
    rwa [Matrix.fromBlocks_toBlocks]
  obtain ⟨hy11, hy12, hy21, hy22⟩ := maxM_fromBlocks.mp hyb
  have a11 : (x + y).toBlocks₁₁ = x.toBlocks₁₁ + y.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
  have a12 : (x + y).toBlocks₁₂ = x.toBlocks₁₂ + y.toBlocks₁₂ := Matrix.ext fun _ _ => rfl
  have a21 : (x + y).toBlocks₂₁ = x.toBlocks₂₁ + y.toBlocks₂₁ := Matrix.ext fun _ _ => rfl
  have a22 : (x + y).toBlocks₂₂ = x.toBlocks₂₂ + y.toBlocks₂₂ := Matrix.ext fun _ _ => rfl
  have hM : MaxM ((x + y).toBlocks₁₁ - g.val) := by
    rw [a11, ← e]
    simpa using hy11
  obtain ⟨u, hu, hgu⟩ := exists_mul_KOne hg hM
  have k21 : MaxM (x + y).toBlocks₂₁ := by rw [a21]; exact h21.add hy21
  have k12 : IntM (x + y).toBlocks₁₂ := by rw [a12]; exact h12.add hy12.intM
  have k22 : IntM (x + y).toBlocks₂₂ := by rw [a22]; exact h22.add hy22.intM
  rw [parPhi_of_mem δ (mul_mem hg (KOne_le_KO hu)) hgu k21 k12 k22, parPhi_of_mem δ hg e h21 h12 h22]
  simp only [map_mul, tame_det_of_mem_KOne hδ hu, mul_one]

open Classical in

theorem parPhi_add {δ : kˣ →* ℂˣ} (hδ : IsTame δ) (x : Matrix (r ⊕ s) (r ⊕ s') k) {y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) : parPhi δ (x + y) = parPhi δ x := by
  by_cases hx : parPhi δ x = 0
  · by_contra hne
    have hxy : parPhi δ (x + y) ≠ 0 := fun h0 => hne (h0.trans hx.symm)
    have back := parPhi_add_eq_of_maxM hδ hy.neg hxy
    rw [add_neg_cancel_right] at back
    exact hxy (back.symm.trans hx)
  · exact parPhi_add_eq_of_maxM hδ hy hx

variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

theorem intM_of_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {x : Matrix Y Y' k} (h : IntM (F.coords F' x)) : IntM x := by
  have hM : IntM ((F.bas⁻¹).val * x * F'.bas.val) := fun a b => by
    have := h (F.ord.symm a) (F'.ord.symm b)
    simp only [LatFrame.coords, Matrix.submatrix_apply, Equiv.apply_symm_apply] at this
    exact this
  have hx : F.bas.val * ((F.bas⁻¹).val * x * F'.bas.val) * (F'.bas⁻¹).val = x := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [← hx]
  exact ((intM_of_mem_KO hF).mul hM).mul (mem_KO.mp hF').2

theorem maxM_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {y : Matrix Y Y' k} (h : MaxM y) : MaxM (F.coords F' y) := by
  have hM : MaxM ((F.bas⁻¹).val * y * F'.bas.val) :=
    ((mem_KO.mp hF).2.mul_maxM h).mul_intM (intM_of_mem_KO hF')
  show MaxM (((F.bas⁻¹).val * y * F'.bas.val).submatrix F.ord F'.ord)
  exact fun i j => hM (F.ord i) (F'.ord j)

theorem coords_add (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (x y : Matrix Y Y' k) :
    F.coords F' (x + y) = F.coords F' x + F.coords F' y := by
  unfold LatFrame.coords
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp

theorem stabLat_le_KO {g : GL Y k} (hg : g ∈ KO k Y) : stabLat g ≤ KO k Y := by
  intro a ha
  have hc := mem_stabLat.mp ha
  have e : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hg hc) (inv_mem hg)

private theorem transport_parPhi_add_eq_of_maxM [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s'] {δ : kˣ →* ℂˣ}
    (hδ : IsTame δ) {F : LatFrame k (r ⊕ s) Y} {F' : LatFrame k (r ⊕ s') Y'} (hF : F.bas ∈ KO k Y)
    (hF' : F'.bas ∈ KO k Y') (x : Matrix Y Y' k) {y : Matrix Y Y' k} (hy : MaxM y) :
    F.transport F' (parPhi δ) (x + y) = F.transport F' (parPhi δ) x := by
  show parPhi δ (F.coords F' (x + y)) = parPhi δ (F.coords F' x)
  rw [coords_add]
  exact parPhi_add hδ _ (maxM_coords hF hF' hy)

end

theorem ofTwist_support_periodic_levels : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (r t Z : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype Z] [DecidableEq Z] (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (μ₀ : ℕ → kˣ →* ℂˣ) (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z), (∀ j c h, latOf (F j c h).bas = latOf 1) → (∀ j c h x, (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x ≠ 0 → IntM x) ∧ (∀ j c h x y, MaxM y → (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h (x + y) = (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x) ∧ ∀ j c h, ((Chain.ofTwist δ hδ μ₀ F Ftop).lev j c h).J ≤ KO k (X j ⊕ Fin c) := by
  intro k _ _ _ _ s r t Z _ _ _ _ _ _ X _ _ δ hδ μ₀ F Ftop hF
  have hK : ∀ j c h, (F j c h).bas ∈ KO k (X j ⊕ Fin c) := fun j c h => mem_KO_of_latOf_eq (hF j c h)
  refine ⟨fun j c h x hx => ?_, fun j c h x y hy => ?_, fun j c h => ?_⟩
  · exact intM_of_coords (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) (intM_of_parPhi_ne_zero δ hx)
  · exact transport_parPhi_add_eq_of_maxM hδ (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) x hy
  · exact ((TypeDatum.map_conj (parahoric r (Fin j × t) δ hδ) (F j c h)).2.2).trans (stabLat_le_KO (hK j c h))

end GlobalTheory.Proof.TwistSupportPeriodicLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoBlockParahoricLowerBlockDetTameCharacter
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling
  GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ParahoricLowerBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_val (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem lower_block_det (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (j : GL (A ⊕ D) k) (hj : j ∈ parahoric k A D) :
    ∃ a b : 𝒪[k], (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det = algebraMap 𝒪[k] k a ∧
      ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det = algebraMap 𝒪[k] k b ∧
      IsLocalRing.residue 𝒪[k] (a * b) = 1 := by
  obtain ⟨⟨h, rfl⟩, hlow⟩ := mem_parahoric.1 hj
  set f := IsLocalRing.residue 𝒪[k]
  set Hb := f.mapMatrix h.val
  set Gb := f.mapMatrix (h⁻¹).val
  have hz : Hb.toBlocks₂₁ = 0 := by
    ext i j'
    exact (residue_eq_zero_iff_val _).2 (hlow i j')
  have hHG : Hb * Gb = 1 := by
    simp only [Hb, Gb, ← map_mul, Units.mul_inv, map_one]
  have h22 : Hb.toBlocks₂₂ * Gb.toBlocks₂₂ = 1 := by
    have := congrArg Matrix.toBlocks₂₂ hHG
    rw [← fromBlocks_toBlocks Hb, ← fromBlocks_toBlocks Gb, fromBlocks_multiply, hz] at this
    have e : (1 : Matrix (A ⊕ D) (A ⊕ D) 𝓀[k]).toBlocks₂₂ = 1 := by
      ext a b; simp [toBlocks₂₂, Matrix.one_apply]
    simpa [e] using this
  refine ⟨h.val.toBlocks₂₂.det, (h⁻¹).val.toBlocks₂₂.det, ?_, ?_, ?_⟩
  · rw [RingHom.map_det]; rfl
  · rw [RingHom.map_det, ← map_inv]; rfl
  · rw [map_mul, RingHom.map_det, RingHom.map_det, ← det_mul]
    exact (congrArg det h22).trans det_one

end GlobalTheory.ParahoricLowerBlock

namespace GlobalTheory.ParahoricLowerBlock

theorem lower_block_tame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ →
  ∀ j ∈ parahoric k A D, (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det ≠ 0 ∧
    ∀ d d' : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      (d' : k) = ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det → (ξ d : ℂ) * ξ d' = 1 := by
  intro k _ _ _ _ A D _ _ _ _ ξ hξ j hj
  obtain ⟨a, b, ha, hb, hab⟩ := lower_block_det A D j hj
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul, map_zero] at hab
    exact zero_ne_one hab
  refine ⟨?_, fun d d' hd hd' => ?_⟩
  · rw [ha]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective 𝒪[k] k)).2 ha0
  · have hv : valuation k (((d * d' : kˣ) : k) - 1) < 1 := by
      have e : ((d * d' : kˣ) : k) - 1 = algebraMap 𝒪[k] k (a * b - 1) := by
        rw [Units.val_mul, hd, hd', ha, hb, map_sub, map_mul, map_one]
      rw [e, ← residue_eq_zero_iff_val, map_sub, hab, map_one, sub_self]
    have := hξ (d * d') hv
    rw [map_mul] at this
    have := congrArg Units.val this
    simpa using this

end GlobalTheory.ParahoricLowerBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.ParahoricConjBlocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (z : k) :
    valuation k z < 1 ↔ valuation k z ≤ valuation k (ϖ : k) := by
  rw [hϖ, le_uniformizer_iff]

theorem scal₁ {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : k) (n : ℤ) :
    (valuation k y ≤ 1 ∧ valuation k (y * (ϖ : k) ^ n) ≤ 1) ↔
      valuation k y ≤ valuation k ((ϖ : k) ^ max 0 (-n)) := by
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  rw [map_mul, map_zpow₀, map_zpow₀, ← le_mul_inv_iff₀ (zpow_pos h0 n), one_mul, ← _root_.zpow_neg]
  rcases le_total 0 n with hn | hn
  · rw [max_eq_left (by omega), zpow_zero]
    have : (1 : ValueGroupWithZero k) ≤ valuation k (ϖ : k) ^ (-n) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show -n ≤ 0 by omega)
    exact ⟨fun h => h.1, fun h => ⟨h, h.trans this⟩⟩
  · rw [max_eq_right (by omega)]
    have : valuation k (ϖ : k) ^ (-n) ≤ 1 := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 0 ≤ -n by omega)
    exact ⟨fun h => h.2, fun h => ⟨h.trans this, h⟩⟩

theorem scal₂ {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : k) (n : ℤ) :
    (valuation k y < 1 ∧ valuation k ((ϖ : k) ^ (-n) * y) < 1) ↔
      valuation k y ≤ valuation k ((ϖ : k) ^ (1 + max 0 n)) := by
  rw [val_lt_one_iff hϖ, val_lt_one_iff hϖ]
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  rw [map_mul, map_zpow₀, map_zpow₀, mul_comm (valuation k (ϖ : k) ^ (-n)),
    ← le_mul_inv_iff₀ (zpow_pos h0 _), ← _root_.zpow_neg, neg_neg, ← zpow_one_add₀ h0.ne']
  rcases le_total 0 n with hn | hn
  · rw [max_eq_right hn]
    have : valuation k (ϖ : k) ^ (1 + n) ≤ valuation k (ϖ : k) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 1 ≤ 1 + n by omega)
    exact ⟨fun h => h.2, fun h => ⟨h.trans this, h⟩⟩
  · rw [max_eq_left hn, add_zero, zpow_one]
    have : valuation k (ϖ : k) ≤ valuation k (ϖ : k) ^ (1 + n) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 1 + n ≤ 1 by omega)
    exact ⟨fun h => h.1, fun h => ⟨h, h.trans this⟩⟩

theorem isUnit_det_iff_of_lower {R : Type} [CommRing R] [IsLocalRing R] {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (N : Matrix (A ⊕ D) (A ⊕ D) R)
    (hN : ∀ i j, N (.inr i) (.inl j) ∈ IsLocalRing.maximalIdeal R) :
    IsUnit N.det ↔ IsUnit N.toBlocks₁₁.det ∧ IsUnit N.toBlocks₂₂.det := by
  simp only [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply]
  have e : N.map (IsLocalRing.residue R) = fromBlocks (N.toBlocks₁₁.map (IsLocalRing.residue R))
      (N.toBlocks₁₂.map (IsLocalRing.residue R)) 0 (N.toBlocks₂₂.map (IsLocalRing.residue R)) := by
    ext (i | i) (j | j) <;> simp [IsLocalRing.residue_eq_zero_iff, hN, toBlocks₁₁, toBlocks₁₂, toBlocks₂₂]
  rw [e, det_fromBlocks_zero₂₁, mul_ne_zero_iff]

theorem mem_KO_val_iff {n : Type} [Fintype n] [DecidableEq n] (y : Matrix n n k) :
    y ∈ Units.val '' (KO k n : Set (GL n k)) ↔ (∀ i j, valuation k (y i j) ≤ 1) ∧ valuation k y.det = 1 := by
  have hI := Valuation.integer.integers (valuation k)
  constructor
  · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
    refine ⟨fun i j => (u.val i j).2, ?_⟩
    show valuation k ((algebraMap 𝒪[k] k).mapMatrix u.val).det = 1
    rw [← RingHom.map_det, ← hI.isUnit_iff_valuation_eq_one]
    exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  · rintro ⟨h1, h2⟩
    let N : Matrix n n 𝒪[k] := fun i j => ⟨y i j, h1 i j⟩
    have hN : (algebraMap 𝒪[k] k).mapMatrix N = y := rfl
    have hu : IsUnit N := by
      rw [Matrix.isUnit_iff_isUnit_det, hI.isUnit_iff_valuation_eq_one, RingHom.map_det, hN]
      exact h2
    exact ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hu.unit, ⟨hu.unit, rfl⟩, hN⟩

theorem val_det_iff_of_lower {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (y : Matrix (A ⊕ D) (A ⊕ D) k) (hi : ∀ i j, valuation k (y i j) ≤ 1)
    (hl : ∀ i j, valuation k (y (.inr i) (.inl j)) < 1) :
    valuation k y.det = 1 ↔ valuation k y.toBlocks₁₁.det = 1 ∧ valuation k y.toBlocks₂₂.det = 1 := by
  have hI := Valuation.integer.integers (valuation k)
  let N : Matrix (A ⊕ D) (A ⊕ D) 𝒪[k] := fun i j => ⟨y i j, hi i j⟩
  have hN : (algebraMap 𝒪[k] k).mapMatrix N = y := rfl
  have h11 : (algebraMap 𝒪[k] k).mapMatrix N.toBlocks₁₁ = y.toBlocks₁₁ := by ext; rfl
  have h22 : (algebraMap 𝒪[k] k).mapMatrix N.toBlocks₂₂ = y.toBlocks₂₂ := by ext; rfl
  have key := isUnit_det_iff_of_lower N (fun i j => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
    exact (hl i j).ne)
  rwa [hI.isUnit_iff_valuation_eq_one, hI.isUnit_iff_valuation_eq_one, hI.isUnit_iff_valuation_eq_one,
    RingHom.map_det, RingHom.map_det, RingHom.map_det, hN, h11, h22] at key

theorem mem_parahoric_val_iff {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (y : Matrix (A ⊕ D) (A ⊕ D) k) :
    y ∈ Units.val '' (parahoric k A D : Set (GL (A ⊕ D) k)) ↔
      y.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧ (∀ i j, valuation k (y.toBlocks₁₂ i j) ≤ 1) ∧
      (∀ i j, valuation k (y.toBlocks₂₁ i j) < 1) ∧ y.toBlocks₂₂ ∈ Units.val '' (KO k D : Set (GL D k)) := by
  have step : y ∈ Units.val '' (parahoric k A D : Set (GL (A ⊕ D) k)) ↔
      y ∈ Units.val '' (KO k (A ⊕ D) : Set (GL (A ⊕ D) k)) ∧ ∀ i j, valuation k (y (.inr i) (.inl j)) < 1 := by
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, (mem_parahoric.1 hg).1, rfl⟩, (mem_parahoric.1 hg).2⟩
    · rintro ⟨⟨g, hg, rfl⟩, h⟩
      exact ⟨g, mem_parahoric.2 ⟨hg, h⟩, rfl⟩
  rw [step, mem_KO_val_iff, mem_KO_val_iff, mem_KO_val_iff]
  constructor
  · rintro ⟨⟨hi, hd⟩, hl⟩
    have hd' := (val_det_iff_of_lower y hi hl).1 hd
    exact ⟨⟨fun i j => hi _ _, hd'.1⟩, fun i j => hi _ _, hl, ⟨fun i j => hi _ _, hd'.2⟩⟩
  · rintro ⟨⟨h11, d11⟩, h12, hl, ⟨h22, d22⟩⟩
    have hi : ∀ i j, valuation k (y i j) ≤ 1 := by
      rintro (i | i) (j | j)
      · exact h11 i j
      · exact h12 i j
      · exact (hl i j).le
      · exact h22 i j
    exact ⟨⟨hi, (val_det_iff_of_lower y hi hl).2 ⟨d11, d22⟩⟩, hl⟩

theorem mem_val_map_conj_inf {n : Type} [Fintype n] [DecidableEq n] (K : Subgroup (GL n k)) (t : GL n k)
    (y : Matrix n n k) :
    y ∈ Units.val '' ((K.map (MulAut.conj t).toMonoidHom ⊓ K : Subgroup (GL n k)) : Set (GL n k)) ↔
      y ∈ Units.val '' (K : Set (GL n k)) ∧
        (t⁻¹ : GL n k).val * y * t.val ∈ Units.val '' (K : Set (GL n k)) := by
  constructor
  · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
    replace hg1 : g ∈ K.map (MulAut.conj t).toMonoidHom := hg1
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hg1
    exact ⟨⟨g, hg2, rfl⟩, ⟨_, hg1, by simp⟩⟩
  · rintro ⟨⟨g, hg, rfl⟩, ⟨h, hh, e⟩⟩
    refine ⟨g, ⟨?_, hg⟩, rfl⟩
    show g ∈ K.map (MulAut.conj t).toMonoidHom
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have : t⁻¹ * g * t = h := Units.ext (by simp [e])
    rwa [this]

theorem val_inv_torusElt {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (f : n → ℤ) :
    ((torusElt k n ϖ f)⁻¹).val = diagonal fun i => (ϖ : k) ^ (-f i) := by
  have : (torusElt k n ϖ f)⁻¹ = torusElt k n ϖ (-f) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv]
    apply Units.ext
    rw [Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    simp only [Pi.neg_apply, _root_.zpow_neg]
    exact inv_mul_cancel₀ (zpow_ne_zero _ ϖ.ne_zero)
  rw [this, val_torusElt]
  rfl

section conjBlocks
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ)
  (x : Matrix (A ⊕ D) (A ⊕ D) k)

theorem conj_apply (i j : A ⊕ D) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)) i j =
      (ϖ : k) ^ (-(Sum.elim 0 e i : ℤ)) * x i j * (ϖ : k) ^ (Sum.elim 0 e j : ℤ) := by
  have h1 : ((mtor (A := A) ϖ e)⁻¹.val : Matrix (A ⊕ D) (A ⊕ D) k) =
      diagonal fun i => (ϖ : k) ^ (-(Sum.elim 0 e i : ℤ)) := val_inv_torusElt _ _
  have h2 : ((mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k) =
      diagonal fun i => (ϖ : k) ^ (Sum.elim 0 e i : ℤ) := val_torusElt _ _
  rw [h1, h2, mul_diagonal, diagonal_mul]

theorem conj_toBlocks₁₁ :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₁ =
      x.toBlocks₁₁ := by
  ext i j
  simp only [toBlocks₁₁, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₁₂ (i : A) (j : D) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₂ i j =
      x.toBlocks₁₂ i j * (ϖ : k) ^ e j := by
  simp only [toBlocks₁₂, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₂₁ (i : D) (j : A) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₂₁ i j =
      (ϖ : k) ^ (-e i) * x.toBlocks₂₁ i j := by
  simp only [toBlocks₂₁, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₂₂ :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₂₂ =
      ((torusElt k D ϖ e)⁻¹.val * x.toBlocks₂₂ * (torusElt k D ϖ e).val : Matrix D D k) := by
  have h1 : ((torusElt k D ϖ e)⁻¹.val : Matrix D D k) = diagonal fun i => (ϖ : k) ^ (-e i) := val_inv_torusElt _ _
  have h2 : ((torusElt k D ϖ e).val : Matrix D D k) = diagonal fun i => (ϖ : k) ^ e i := val_torusElt _ _
  rw [h1, h2]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  simp only [toBlocks₂₂, of_apply]
  rw [conj_apply]
  simp

end conjBlocks

theorem blockset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    Units.val '' (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)) =
      {x | x.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧
        x.toBlocks₁₂ ∈ {y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ max 0 (-e j))} ∧
        x.toBlocks₂₁ ∈ {y : Matrix D A k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ (1 + max 0 (e i)))} ∧
        x.toBlocks₂₂ ∈ Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k))} := by
  intro k _ _ _ _ ϖ hϖ A D _ _ _ _ e
  ext x
  rw [mem_val_map_conj_inf, mem_parahoric_val_iff, mem_parahoric_val_iff, conj_toBlocks₁₁, conj_toBlocks₂₂]
  simp only [conj_toBlocks₁₂, conj_toBlocks₂₁, Set.mem_setOf_eq, mem_val_map_conj_inf, ← scal₁ hϖ, ← scal₂ hϖ,
    forall_and]
  tauto

end GlobalTheory.ParahoricConjBlocks
end
end

