import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PClassMean
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PHeckeRatioInvariant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm
open scoped MatrixGroups

noncomputable section

namespace HeckeRatioInvariant

theorem discriminant_smul (γ : SL(2, ℤ)) (z : ℍ) :
    discriminant (γ • z) = (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) ^ 12 * discriminant z := by
  have h := congr_fun (SlashInvariantForm.slash_action_generators_SL2Z
    discriminant_S_invariant discriminant_T_invariant γ) z
  rw [SL_slash_apply] at h
  have hd : denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom]
  have hne : denom γ z ≠ 0 := denom_ne_zero _ _
  rw [← hd, ← h, zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp

theorem discriminant_eq_of_coe_eq (a b c d : ℤ) (hdet : a * d - b * c = 1) {z w : ℍ}
    (h : (w : ℂ) = ((a : ℂ) * z + b) / ((c : ℂ) * z + d)) :
    discriminant w = ((c : ℂ) * z + d) ^ 12 * discriminant z := by
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by simp [Matrix.det_fin_two_of, hdet]⟩
  have hw : w = γ • z := UpperHalfPlane.ext (by rw [h, coe_specialLinearGroup_apply]; simp [γ])
  rw [hw, discriminant_smul]
  simp [γ]

theorem map_range_succ_eq_cons (f : ℕ → ℂ) (m : ℕ) :
    (Multiset.range (m + 1)).map f = f 0 ::ₘ (Multiset.range m).map (fun a ↦ f (a + 1)) := by
  rw [← Multiset.coe_range, ← Multiset.coe_range, Multiset.map_coe, Multiset.map_coe,
    List.range_succ_eq_map]
  simp [Function.comp_def]

theorem map_range_shift (g : ℕ → ℂ) (m : ℕ) (h : g m = g 0) :
    (Multiset.range m).map (fun a ↦ g (a + 1)) = (Multiset.range m).map g := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [map_range_succ_eq_cons g m, Multiset.range_succ, Multiset.map_cons, h]

theorem heckeRatios_alt (n : ℕ+) (τ : ℍ) :
    heckeRatios n (ModularGroup.T • τ) = heckeRatios n τ := by
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
    rw [modular_T_smul, coe_vadd]; simp [add_comm]
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have h0 : discriminant (ModularGroup.T • τ) = discriminant τ := by
    rw [discriminant_eq_of_coe_eq 1 1 0 1 (by norm_num) (z := τ) (by rw [hT]; push_cast; ring)]
    simp
  have h1 : discriminant (mulPoint n (ModularGroup.T • τ)) = discriminant (mulPoint n τ) := by
    rw [discriminant_eq_of_coe_eq 1 (n : ℕ) 0 1 (by norm_num) (z := mulPoint n τ)
      (by rw [coe_mulPoint, coe_mulPoint, hT]; push_cast; ring)]
    simp
  have h2 : ∀ a : ℕ, divPoint n a (ModularGroup.T • τ) = divPoint n (a + 1) τ := fun a ↦
    UpperHalfPlane.ext (by rw [coe_divPoint, coe_divPoint, hT]; push_cast; ring)
  have h3 : discriminant (divPoint n n τ) = discriminant (divPoint n 0 τ) := by
    rw [discriminant_eq_of_coe_eq 1 1 0 1 (by norm_num) (z := divPoint n 0 τ)
      (by rw [coe_divPoint, coe_divPoint]; field_simp; push_cast; ring)]
    simp
  have h4 : (Multiset.range n).map
      (fun a : ℕ ↦ discriminant (divPoint n a (ModularGroup.T • τ)) / discriminant τ) =
      (Multiset.range n).map (fun a : ℕ ↦ discriminant (divPoint n a τ) / discriminant τ) := by
    simp_rw [h2]
    exact map_range_shift (fun a ↦ discriminant (divPoint n a τ) / discriminant τ) n (by simp [h3])
  unfold heckeRatios
  rw [h0, h1, h4]

def negInvMod (p j : ℕ) : ℕ := (-((j : ZMod p)⁻¹)).val

theorem negInvMod_spec {p : ℕ} [Fact p.Prime] {j : ℕ} (h0 : 0 < j) (hj : j < p) :
    0 < negInvMod p j ∧ negInvMod p j < p ∧ p ∣ j * negInvMod p j + 1 ∧
      negInvMod p (negInvMod p j) = j := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hj0 : ((j : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd h0 hd
    omega
  have hcast : ((negInvMod p j : ℕ) : ZMod p) = -((j : ZMod p)⁻¹) := ZMod.natCast_zmod_val _
  refine ⟨?_, ZMod.val_lt _, ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, negInvMod, Ne, ZMod.val_eq_zero, neg_eq_zero, inv_eq_zero]
    exact hj0
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hcast, mul_neg, mul_inv_cancel₀ hj0]
    ring
  · rw [negInvMod, hcast, inv_neg, neg_neg, inv_inv, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

theorem coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = (-(τ : ℂ))⁻¹ := by
  rw [modular_S_smul, coe_mk]

theorem discriminant_S_smul (τ : ℍ) :
    discriminant (ModularGroup.S • τ) = (τ : ℂ) ^ 12 * discriminant τ := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [discriminant_eq_of_coe_eq 0 (-1) 1 0 (by norm_num) (z := τ)
    (by rw [coe_S_smul]; push_cast; ring)]
  simp

theorem ratio_S (n : ℕ+) (τ : ℍ) (j b k : ℕ) (h : j * b + 1 = (n : ℕ) * k) :
    discriminant (divPoint n j (ModularGroup.S • τ)) / discriminant (ModularGroup.S • τ) =
      discriminant (divPoint n b τ) / discriminant τ := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hC : (j : ℂ) * b + 1 = (n : ℕ) * k := by exact_mod_cast h
  have hZ : (j : ℤ) * (-(b : ℤ)) - (-(k : ℤ)) * ((n : ℕ) : ℤ) = 1 := by
    have : ((j * b + 1 : ℕ) : ℤ) = (((n : ℕ) * k : ℕ) : ℤ) := by rw [h]
    push_cast at this
    linarith
  have hden : (((((n : ℕ) : ℤ)) : ℂ) * (divPoint n b τ : ℂ) + ((-(b : ℤ) : ℤ) : ℂ)) = τ := by
    rw [coe_divPoint]; push_cast; field_simp; ring
  have e := discriminant_eq_of_coe_eq (j : ℤ) (-(k : ℤ)) ((n : ℕ) : ℤ) (-(b : ℤ)) hZ
    (z := divPoint n b τ) (w := divPoint n j (ModularGroup.S • τ)) (by
      rw [hden, coe_divPoint, coe_divPoint, coe_S_smul]
      push_cast
      field_simp
      linear_combination (-1 : ℂ) * hC)
  rw [e, hden, discriminant_S_smul]
  have := discriminant_ne_zero τ
  field_simp

theorem heckeRatios_S (p : ℕ) (hp : p.Prime) (τ : ℍ) :
    heckeRatios ⟨p, hp.pos⟩ (ModularGroup.S • τ) = heckeRatios ⟨p, hp.pos⟩ τ := by
  have := Fact.mk hp
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  set n : ℕ+ := ⟨m + 1, hp.pos⟩ with hn_def
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hΔ := discriminant_ne_zero τ
  set g : ℕ → ℂ := fun a ↦ discriminant (divPoint n a τ) / discriminant τ with hg
  set gS : ℕ → ℂ := fun a ↦
    discriminant (divPoint n a (ModularGroup.S • τ)) / discriminant (ModularGroup.S • τ) with hgS
  have e1 : heckeRatios n (ModularGroup.S • τ) =
      ((n : ℂ) ^ 12 * discriminant (mulPoint n (ModularGroup.S • τ)) /
        discriminant (ModularGroup.S • τ)) ::ₘ
        (gS 0 ::ₘ (Multiset.range m).map (fun a ↦ gS (a + 1))) := by
    rw [← map_range_succ_eq_cons]; rfl
  have e2 : heckeRatios n τ = ((n : ℂ) ^ 12 * discriminant (mulPoint n τ) / discriminant τ) ::ₘ
      (g 0 ::ₘ (Multiset.range m).map (fun a ↦ g (a + 1))) := by
    rw [← map_range_succ_eq_cons]; rfl
  have hA : (n : ℂ) ^ 12 * discriminant (mulPoint n (ModularGroup.S • τ)) /
      discriminant (ModularGroup.S • τ) = g 0 := by
    rw [discriminant_eq_of_coe_eq 0 (-1) 1 0 (by norm_num) (z := divPoint n 0 τ)
      (by rw [coe_mulPoint, coe_divPoint, coe_S_smul]; push_cast; ring_nf; simp only [inv_inv]; try ring),
      discriminant_S_smul, hg]
    simp only [coe_divPoint]
    push_cast
    field_simp
    try ring
  have hB : gS 0 = (n : ℂ) ^ 12 * discriminant (mulPoint n τ) / discriminant τ := by
    rw [hgS]
    dsimp only
    rw [discriminant_eq_of_coe_eq 0 (-1) 1 0 (by norm_num) (z := mulPoint n τ)
      (by rw [coe_mulPoint, coe_divPoint, coe_S_smul]; push_cast; ring),
      discriminant_S_smul, coe_mulPoint]
    push_cast
    field_simp
    try ring
  have hmid : (Multiset.range m).map (fun a ↦ gS (a + 1)) =
      (Multiset.range m).map (fun a ↦ g (a + 1)) := by
    refine Multiset.map_eq_map_of_bij_of_nodup _ _ (Multiset.nodup_range m)
      (Multiset.nodup_range m) (fun a _ ↦ negInvMod (m + 1) (a + 1) - 1) ?_ ?_ ?_ ?_
    · intro a ha
      rw [Multiset.mem_range] at ha ⊢
      have := negInvMod_spec (p := m + 1) (j := a + 1) (by omega) (by omega)
      omega
    · intro a₁ ha₁ a₂ ha₂ he
      rw [Multiset.mem_range] at ha₁ ha₂
      have s₁ := negInvMod_spec (p := m + 1) (j := a₁ + 1) (by omega) (by omega)
      have s₂ := negInvMod_spec (p := m + 1) (j := a₂ + 1) (by omega) (by omega)
      have he' : negInvMod (m + 1) (a₁ + 1) = negInvMod (m + 1) (a₂ + 1) := by omega
      have := congrArg (negInvMod (m + 1)) he'
      rw [s₁.2.2.2, s₂.2.2.2] at this
      omega
    · intro b hb
      rw [Multiset.mem_range] at hb
      have s := negInvMod_spec (p := m + 1) (j := b + 1) (by omega) (by omega)
      refine ⟨negInvMod (m + 1) (b + 1) - 1, Multiset.mem_range.2 (by omega), ?_⟩
      rw [Nat.sub_add_cancel s.1, s.2.2.2]
      rfl
    · intro a ha
      rw [Multiset.mem_range] at ha
      have s := negInvMod_spec (p := m + 1) (j := a + 1) (by omega) (by omega)
      obtain ⟨k, hk⟩ := s.2.2.1
      rw [Nat.sub_add_cancel s.1]
      exact ratio_S n τ (a + 1) (negInvMod (m + 1) (a + 1)) k hk
  rw [e1, e2, hA, hB, hmid, Multiset.cons_swap]

theorem proof : HeckeRatioInvariant.Statement := by
  intro p hp γ τ
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {g | ∀ τ : ℍ, heckeRatios ⟨p, hp.pos⟩ (g • τ) = heckeRatios ⟨p, hp.pos⟩ τ}
      mul_mem' := by
        intro a b ha hb τ
        simp only [Set.mem_ofPred_eq] at ha hb
        rw [mul_smul, ha, hb]
      one_mem' := by intro τ; simp
      inv_mem' := by
        intro a ha τ
        simp only [Set.mem_ofPred_eq] at ha
        rw [← ha (a⁻¹ • τ), smul_inv_smul] }
  have hle : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ H := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact heckeRatios_S p hp
    · exact heckeRatios_alt _
  have hγ : γ ∈ H := hle (by rw [SpecialLinearGroup.SL2Z_generators]; trivial)
  exact hγ τ

end HeckeRatioInvariant

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PSuperlatticeRatio
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic

noncomputable section

namespace SuperlatticeRatio

theorem eq_of_le_of_relIndex {A B C : Submodule ℤ ℂ} {p : ℕ} (hp : p.Prime) (hAB : A ≤ B)
    (hBC : B ≤ C) (hidx : A.toAddSubgroup.relIndex C.toAddSubgroup = p) (hne : ¬ B ≤ A) :
    B = C := by
  have h := AddSubgroup.relIndex_mul_relIndex (H := A.toAddSubgroup) (K := B.toAddSubgroup)
    (L := C.toAddSubgroup) (fun _ hx ↦ hAB hx) (fun _ hx ↦ hBC hx)
  rw [hidx] at h
  rcases Nat.prime_mul_iff.1 (h ▸ hp) with ⟨-, h1⟩ | ⟨-, h1⟩
  · have h2 := AddSubgroup.relIndex_eq_one.1 h1
    exact le_antisymm hBC (fun x hx ↦ h2 hx)
  · have h2 := AddSubgroup.relIndex_eq_one.1 h1
    exact absurd (fun x hx ↦ h2 hx) hne

theorem mem_span_pair_iff {α β x : ℂ} :
    x ∈ Submodule.span ℤ ({α, β} : Set ℂ) ↔ ∃ m n : ℤ, (m : ℂ) * α + n * β = x := by
  simp [Submodule.mem_span_pair, zsmul_eq_mul]

theorem latticeDiscr_scale_latticeOfTau {c : ℂ} (hc : c ≠ 0) (σ : ℍ) :
    latticeDiscr (scaleLattice c (latticeOfTau σ).lattice) =
      (c ^ 12)⁻¹ * ((2 * Real.pi) ^ 12 * discriminant σ) := by
  rw [PhScale.latticeDiscr_scaleLattice _ hc, latticeDiscr_lattice, discr_latticeOfTau]

theorem proof : SuperlatticeRatio.Statement := by
  intro L L' p hp hle hidx
  obtain ⟨τ, c, hc, hL⟩ := ClassMean.exists_eq_scaleLattice L
  have hLs : L.lattice = Submodule.span ℤ {c * τ, c} := by
    rw [hL, ClassMean.scaleLattice_latticeOfTau]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hτ : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  have hcτ : c * τ ∈ L'.lattice := hle (hLs ▸ Submodule.subset_span (by simp))
  have hc' : c ∈ L'.lattice := hle (hLs ▸ Submodule.subset_span (by simp))

  refine ⟨τ, ?_, ?_⟩
  · rw [← weierstrassCurve_latticeOfTau_j, eq_comm, weierstrassCurve_j_eq_iff]
    refine ⟨c, hc, ?_⟩
    rw [hL, scaleLattice, Submodule.map_coe]
    rfl

  have hne : ¬ L'.lattice ≤ L.lattice := fun h ↦
    hp.one_lt.ne' (hidx ▸ AddSubgroup.relIndex_eq_one.2 (fun x hx ↦ h hx))
  obtain ⟨v, hvL', hvL⟩ := SetLike.not_le_iff_exists.1 hne
  have hpv : (p : ℂ) * v ∈ L.lattice := by
    have := AddSubgroup.nsmul_relIndex_mem L.lattice.toAddSubgroup
      (K := L'.lattice.toAddSubgroup) (g := v) hvL'
    rw [hidx, nsmul_eq_mul] at this
    exact this
  rw [hLs, mem_span_pair_iff] at hpv
  obtain ⟨m, n, hmn⟩ := hpv
  have hLdiscr : latticeDiscr L.lattice = (c ^ 12)⁻¹ * ((2 * Real.pi) ^ 12 * discriminant τ) := by
    rw [hL, latticeDiscr_scale_latticeOfTau hc]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have hz : ∀ (z : ℤ) {x : ℂ}, x ∈ L'.lattice → (z : ℂ) * x ∈ L'.lattice := fun z x hx ↦ by
    rw [← zsmul_eq_mul]; exact zsmul_mem hx z
  by_cases hm : (p : ℤ) ∣ m
  ·
    obtain ⟨k, rfl⟩ := hm
    have hn : ¬ (p : ℤ) ∣ n := by
      rintro ⟨l, rfl⟩
      apply hvL
      rw [hLs, mem_span_pair_iff]
      refine ⟨k, l, mul_left_cancel₀ hp0 ?_⟩
      rw [← hmn]; push_cast; ring
    obtain ⟨u, w, huw⟩ := (hpZ.coprime_iff_not_dvd.2 hn).symm
    set σ := mulPoint ⟨p, hp.pos⟩ τ
    have hσ : (σ : ℂ) = p * τ := coe_mulPoint _ _
    have hcp : c / p ≠ 0 := div_ne_zero hc hp0
    have hM : scaleLattice (c / p) (latticeOfTau σ).lattice = Submodule.span ℤ {c * τ, c / p} := by
      rw [ClassMean.scaleLattice_latticeOfTau, hσ, show c / p * (p * τ) = c * τ by field_simp]
    have heq : scaleLattice (c / p) (latticeOfTau σ).lattice = L'.lattice := by
      refine eq_of_le_of_relIndex hp ?_ ?_ hidx ?_
      · rw [hLs, hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩ <;> rw [SetLike.mem_coe, mem_span_pair_iff]
        · exact ⟨1, 0, by simp⟩
        · have key2 : (p : ℂ) * (c / p) = c := by field_simp
          exact ⟨0, p, by push_cast; linear_combination key2⟩
      · rw [hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩
        · exact hcτ
        · have e : c / p = (u : ℂ) * v + ((-(u * k) : ℤ) : ℂ) * (c * τ) + (w : ℂ) * c := by
            have hmn' : (p : ℂ) * v = p * k * (c * τ) + n * c := by rw [← hmn]; push_cast; ring
            have huw' : (u : ℂ) * n + w * p = 1 := by exact_mod_cast huw
            push_cast
            rw [div_eq_iff hp0]
            linear_combination (-(u : ℂ)) * hmn' - c * huw'
          rw [SetLike.mem_coe, e]
          exact add_mem (add_mem (hz u hvL') (hz _ hcτ)) (hz w hc')
      · intro h
        have : c / p ∈ L.lattice := h (hM ▸ Submodule.subset_span (by simp))
        rw [hLs, mem_span_pair_iff] at this
        obtain ⟨m', n', e⟩ := this
        have e2 : c * ((m' : ℂ) * τ + n' - 1 / p) = 0 := by linear_combination e
        have e' : (m' : ℂ) * τ + n' = 1 / p := sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left hc)
        have him : (m' : ℝ) * (τ : ℂ).im = 0 := by
          have := congrArg Complex.im e'
          simpa using this
        have hm0 : m' = 0 := by
          rcases mul_eq_zero.1 him with h0 | h0
          · exact_mod_cast h0
          · exact absurd h0 hτ
        subst hm0
        have hre : (n' : ℂ) * p = 1 := by
          have e3 : (n' : ℂ) = 1 / p := by simpa using e'
          rw [e3]; field_simp
        have : (p * n' : ℤ) = 1 := by rw [mul_comm]; exact_mod_cast hre
        exact hpZ.not_dvd_one ⟨n', this.symm⟩
    refine Multiset.mem_cons.2 (Or.inl ?_)
    rw [← heq, latticeDiscr_scale_latticeOfTau hcp, hLdiscr]
    have hΔ := discriminant_ne_zero τ
    simp only [PNat.mk_coe]
    field_simp
    rfl
  ·
    obtain ⟨u, w, huw⟩ := (hpZ.coprime_iff_not_dvd.2 hm).symm
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
    set r := u * n % p with hr
    set q := u * n / p
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hpz.ne'
    have hrp : r < p := Int.emod_lt_of_pos _ hpz
    have hrq : r + q * p = u * n := Int.emod_add_ediv_mul _ _
    set a := r.toNat
    have ha : (a : ℤ) = r := Int.toNat_of_nonneg hr0
    have hap : a < p := by omega
    have haC : (a : ℂ) = r := by exact_mod_cast ha
    set σ := divPoint ⟨p, hp.pos⟩ a τ
    have hσ : (σ : ℂ) = (a + τ) / p := coe_divPoint _ _ _
    have hM : scaleLattice c (latticeOfTau σ).lattice =
        Submodule.span ℤ {c * ((a + τ) / p), c} := by
      rw [ClassMean.scaleLattice_latticeOfTau, hσ]
    have heq : scaleLattice c (latticeOfTau σ).lattice = L'.lattice := by
      refine eq_of_le_of_relIndex hp ?_ ?_ hidx ?_
      · rw [hLs, hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩ <;> rw [SetLike.mem_coe, mem_span_pair_iff]
        · have key : (p : ℂ) * (c * ((a + τ) / p)) = c * (a + τ) := by field_simp
          exact ⟨p, -(a : ℤ), by push_cast; linear_combination key⟩
        · exact ⟨0, 1, by simp⟩
      · rw [hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩
        · have e : c * ((a + τ) / p) = (u : ℂ) * v + (w : ℂ) * (c * τ) + ((-q : ℤ) : ℂ) * c := by
            have hmn' : (p : ℂ) * v = m * (c * τ) + n * c := hmn.symm
            have huw' : (u : ℂ) * m + w * p = 1 := by exact_mod_cast huw
            have hrq' : (r : ℂ) + q * p = u * n := by exact_mod_cast hrq
            have haC' : (a : ℂ) - r = 0 := by rw [haC]; ring
            push_cast
            rw [mul_div_assoc', div_eq_iff hp0]
            linear_combination (-(u : ℂ)) * hmn' - c * τ * huw' + c * hrq' + c * haC'
          rw [SetLike.mem_coe, e]
          exact add_mem (add_mem (hz u hvL') (hz w hcτ)) (hz _ hc')
        · exact hc'
      · intro h
        have : c * ((a + τ) / p) ∈ L.lattice := h (hM ▸ Submodule.subset_span (by simp))
        rw [hLs, mem_span_pair_iff] at this
        obtain ⟨m', n', e⟩ := this
        have hdiv : c * ((a + τ) / p) * p = c * (a + τ) := by field_simp
        have e2 : c * ((a + τ) - p * (m' * τ + n')) = 0 := by
          linear_combination (-(p : ℂ)) * e - hdiv
        have e' : (a : ℂ) + τ - p * (m' * τ + n') = 0 := (mul_eq_zero.1 e2).resolve_left hc
        have him : τ.im * (1 - p * m') = 0 := by
          have := congrArg Complex.im e'
          simp at this
          linear_combination this
        have h1 : ((p * m' : ℤ) : ℝ) = 1 := by
          push_cast
          linarith [(mul_eq_zero.1 him).resolve_left τ.im_pos.ne']
        have h1' : (p * m' : ℤ) = 1 := by exact_mod_cast h1
        exact hpZ.not_dvd_one ⟨m', h1'.symm⟩
    refine Multiset.mem_cons_of_mem (Multiset.mem_map.2 ⟨a, Multiset.mem_range.2 hap, ?_⟩)
    rw [← heq, latticeDiscr_scale_latticeOfTau hc, hLdiscr]
    have hΔ := discriminant_ne_zero τ
    field_simp
    rfl

end SuperlatticeRatio

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

