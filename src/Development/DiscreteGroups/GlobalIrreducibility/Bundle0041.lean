import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0040
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzRedLift
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem rep_mul_apply {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (a b : G) (v : V) : π (a * b) v = π a (π b v) := by
  rw [map_mul]; rfl

theorem rep_one_apply {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (v : V) : π 1 v = v := by
  rw [map_one]; rfl

theorem superDiag_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (x : GL (Fin n) R) :
    superDiag (Matrix.GeneralLinearGroup.map f x) = f (superDiag x) := by
  simp only [superDiag, map_sum]
  rfl

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem exists_lift_unipB (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) {n : ℕ}
    {u : Gn g n} (hu : u ∈ unipB (ZMod g) (Fin n)) :
    ∃ κ : GL (Fin n) ℤ_[g], red g n κ = u ∧
      Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ) ∈ unipB (w.adicCompletion E) (Fin n) ∧
      ψ (superDiag (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ))) = ψ₀ (superDiag u) := by
  classical
  have hu' := (mem_unipB (R := ZMod g)).1 hu
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b => (((u : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℤ_[g])
  have hlow : ∀ a b, b < a → M a b = 0 := fun a b h => by simp only [M, hu'.1 a b h, ZMod.val_zero, Nat.cast_zero]
  have hdiag : ∀ a, M a a = 1 := fun a => by simp only [M, hu'.2 a, ZMod.val_one, Nat.cast_one]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun a b h => hlow a b h)]
    simp [hdiag]
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hdet]; exact isUnit_one)
  let κ : GL (Fin n) ℤ_[g] := hU.unit
  have hκ : (κ : Matrix (Fin n) (Fin n) ℤ_[g]) = M := hU.unit_spec
  have hred : red g n κ = u := by
    refine Units.ext (Matrix.ext fun a b => ?_)
    show PadicInt.toZMod ((κ : Matrix (Fin n) (Fin n) ℤ_[g]) a b) = _
    rw [hκ]
    simp only [M, map_natCast, ZMod.natCast_zmod_val]
  refine ⟨κ, hred, ?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun a b h => ?_, fun a => ?_⟩
    · show i (((κ : Matrix (Fin n) (Fin n) ℤ_[g]) a b : ℤ_[g]) : ℚ_[g]) = 0
      rw [hκ, hlow a b h]; simp
    · show i (((κ : Matrix (Fin n) (Fin n) ℤ_[g]) a a : ℤ_[g]) : ℚ_[g]) = 1
      rw [hκ, hdiag]; simp
  · rw [show inc g n κ = Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g]) κ from rfl, superDiag_map,
      superDiag_map, ← hred, show red g n κ = Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := g)) κ from rfl,
      superDiag_map]
    exact hψ _

def cellFun {m : ℕ} {V' : Type} [AddCommGroup V'] [Module ℂ V']
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (l' : Module.Dual ℂ V') (v' : V')
    (s : Gn g m → GL (Fin m) ℤ_[g]) (x : Gn g m) : ℂ :=
  l' (ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m (s x))) v')

theorem isLower_one {m : ℕ} : ∀ a b : Fin m, a < b → ((1 : Gn g m) : Mt g m) a b = 0 :=
  fun a b h => by simp [Matrix.one_apply_ne (ne_of_lt h)]

theorem cellFun_eq {m : ℕ} {V' : Type} [AddCommGroup V'] [Module ℂ V']
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (l' : Module.Dual ℂ V') (v' : V')
    (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (s : Gn g m → GL (Fin m) ℤ_[g]) (hs : ∀ κ, red g m (s κ) = κ) (κ₁ : GL (Fin m) ℤ_[g]) :
    cellFun i ρ₀ l' v' s (red g m κ₁) = l' (ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m κ₁)) v') := by
  unfold cellFun
  have h1 : red g m ((s (red g m κ₁))⁻¹ * κ₁) = 1 := by rw [map_mul, map_inv, hs, inv_mul_cancel]
  have h2 := hv' ((s (red g m κ₁))⁻¹ * κ₁) (by rw [h1]; exact isLower_one)
  conv_rhs => rw [show κ₁ = s (red g m κ₁) * ((s (red g m κ₁))⁻¹ * κ₁) by group]
  generalize (s (red g m κ₁))⁻¹ * κ₁ = y at h2 ⊢
  rw [map_mul (inc g m), map_mul (Matrix.GeneralLinearGroup.map i.toRingHom), rep_mul_apply, h2]

theorem cellFun_lower {m : ℕ} {V' : Type} [AddCommGroup V'] [Module ℂ V']
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (l' : Module.Dual ℂ V') (v' : V')
    (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (s : Gn g m → GL (Fin m) ℤ_[g]) (hs : ∀ κ, red g m (s κ) = κ) (x b : Gn g m)
    (hb : ∀ a c : Fin m, a < c → (b : Mt g m) a c = 0) :
    cellFun i ρ₀ l' v' s (x * b) = cellFun i ρ₀ l' v' s x := by
  rw [show x * b = red g m (s x * s b) by rw [map_mul, hs, hs], cellFun_eq i ρ₀ l' v' hv' s hs,
    map_mul (inc g m), map_mul (Matrix.GeneralLinearGroup.map i.toRingHom), rep_mul_apply, hv' (s b) (by rw [hs]; exact hb)]
  rfl

include hi in
theorem cellFun_unip (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) {m : ℕ} {V' : Type}
    [AddCommGroup V'] [Module ℂ V']
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (l' : Module.Dual ℂ V') (v' : V')
    (hl' : IsFunctional ψ⁻¹ ρ₀ l')
    (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (s : Gn g m → GL (Fin m) ℤ_[g]) (hs : ∀ κ, red g m (s κ) = κ) {u : Gn g m} (hu : u ∈ unipB (ZMod g) (Fin m))
    (x : Gn g m) :
    cellFun i ρ₀ l' v' s (u * x) = (((ψ₀ (superDiag u))⁻¹ : Circle) : ℂ) * cellFun i ρ₀ l' v' s x := by
  obtain ⟨κ, hred, hmem, hsd⟩ := exists_lift_unipB i hi hψ hu
  rw [show u * x = red g m (κ * s x) by rw [map_mul, hred, hs], cellFun_eq i ρ₀ l' v' hv' s hs,
    map_mul (inc g m), map_mul (Matrix.GeneralLinearGroup.map i.toRingHom), rep_mul_apply, hl' _ hmem, AddChar.inv_apply', hsd]
  rfl

theorem cellFun_one {m : ℕ} {V' : Type} [AddCommGroup V'] [Module ℂ V']
    (ρ₀ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V') (l' : Module.Dual ℂ V') (v' : V')
    (hv' : ∀ x : GL (Fin m) ℤ_[g], (∀ a b : Fin m, a < b → (red g m x : Mt g m) a b = 0) →
      ρ₀ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g m x)) v' = v')
    (s : Gn g m → GL (Fin m) ℤ_[g]) (hs : ∀ κ, red g m (s κ) = κ) :
    cellFun i ρ₀ l' v' s 1 = l' v' := by
  have h := cellFun_eq i ρ₀ l' v' hv' s hs 1
  rw [map_one] at h
  rw [h, map_one, map_one, rep_one_apply]

end DiscreteGroups.sglob.DzRed
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvGen
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem step {c : kˣ} (hc : HasConductor ψ c) (hcusp : IsCuspidal π) (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j)
    (h0 : KN π ψ (j + 1) ≠ ⊤) : KN π ψ j ≠ ⊤ := by
  obtain ⟨ξ, hξ⟩ := exists_col_char π ψ hc hcusp.1 j hj h0 Finset.univ
  by_cases hz : ∀ i : Fin n, i.val < j → ξ i = 0
  · exfalso
    have h : ∑ i, ![j, n - j] i = n := by simp [Fin.sum_univ_two]; omega
    have htw : twKer π (unipRad k (stdBlocks ![j, n - j] h)) 1 = ⊤ :=
      Submodule.Quotient.subsingleton_iff.1 (hcusp.2 2 ![j, n - j] (stdBlocks ![j, n - j] h)
        (GlobalTheory.T.unipRad_stdBlocks_two_ne_bot' k n j (n - j) h hj1 (by omega)))
    exact hξ (eq_top_iff.2 (by rw [← htw]; exact twKer_le π ψ j hj h ξ hz))
  · push Not at hz
    obtain ⟨p, hp, hpξ⟩ := hz
    obtain ⟨ξ1, h1, hξ1⟩ : ∃ ξ1 : Fin n → k, ξ1 (i0 j hj hj1) ≠ 0 ∧
        KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ1 ≠ ⊤ := by
      by_cases hi0 : ξ (i0 j hj hj1) = 0
      · have hne : p ≠ i0 j hj hj1 := fun e => hpξ (by rw [e]; exact hi0)
        refine ⟨_, ?_, ne_top_of_conj π ψ j hj (GlobalTheory.RootUp.elem hne (-1 : k))
          (topLeft_elem j hj hj1 hp hne _) (topLeft_elem_inv j hj hj1 hp hne _) ξ hξ⟩
        rw [rowMul_elem_inv j hj hj1 hp hne ξ, hi0, zero_add]
        exact hpξ
      · exact ⟨ξ, hi0, hξ⟩
    have h2 := ne_top_of_conj π ψ j hj (xA j hj hj1 ξ1 h1) (topLeft_xA j hj hj1 ξ1 h1)
      (topLeft_xA_inv j hj hj1 ξ1 h1) ξ1 hξ1
    exact fun htop => h2 (eq_top_iff.2 (by rw [← htop]; exact KN_le π ψ j hj hj1 _ (dotj_xA_inv j hj hj1 ξ1 h1)))

theorem KN_one_ne_top [Nontrivial V] {c : kˣ} (hc : HasConductor ψ c) (hcusp : IsCuspidal π) :
    KN π ψ 1 ≠ ⊤ := by
  have hbase : ∀ m, n ≤ m → KN π ψ m ≠ ⊤ := fun m hm => by rw [KN_top π ψ m hm]; exact bot_ne_top
  have key : ∀ d, d + 1 ≤ n → KN π ψ (n - d) ≠ ⊤ := by
    intro d
    induction d with
    | zero => intro _; exact hbase _ (by omega)
    | succ d ih =>
      intro hd
      refine step π ψ hc hcusp (n - (d + 1)) (by omega) (by omega) ?_
      rw [show n - (d + 1) + 1 = n - d by omega]
      exact ih (by omega)
  by_cases hn : n ≤ 1
  · exact hbase 1 hn
  · have := key (n - 1) (by omega)
    rwa [show n - (n - 1) = 1 by omega] at this

theorem sdS_one (M : Matrix (Fin n) (Fin n) k) : sdS 1 M = ∑ i : Fin n, ∑ l : Fin n with l.val = i.val + 1, M i l := by
  simp only [sdS, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem mem_Nset_one {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n)) : u ∈ Nset 1 := by
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hu
  intro i l hil
  have hli : l ≤ i := hil.elim id (fun h => by rw [Fin.le_iff_val_le_val]; omega)
  rcases hli.lt_or_eq with hlt | heq
  · rw [h1 i l hlt, one_apply_ne (ne_of_gt hlt)]
  · rw [heq, h2 i, one_apply_eq]

end DiscreteGroups.sglob.LConvGenR

namespace DiscreteGroups.sglob.LConv

open DiscreteGroups.sglob.LConvGenR

theorem cuspGen : CuspGen := by
  intro k _ _ _ _ ψ hψ hψ1 n V _ _ π hV hcusp
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ hψ1
  have hne := KN_one_ne_top π ψ hc hcusp
  obtain ⟨x, hx⟩ : ∃ x, x ∉ KN π ψ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨f, hfx, hker⟩ := Submodule.exists_le_ker_of_notMem hx
  refine ⟨f, fun h0 => hfx (by rw [h0]; rfl), fun u hu v => ?_⟩
  have hmem : π u v - chM ψ 1 u • v ∈ KN π ψ 1 := Submodule.subset_span ⟨u, mem_Nset_one hu, v, rfl⟩
  have h1 := hker hmem
  rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at h1
  rw [h1, smul_eq_mul, chM, sdS_one]
  rfl

end DiscreteGroups.sglob.LConv
end
end

