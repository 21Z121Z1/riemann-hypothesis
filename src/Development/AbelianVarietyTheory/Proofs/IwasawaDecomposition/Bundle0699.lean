import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0685

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey

theorem ell_eq_of_inRCone {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hlin : φ.LinearOn γ) (hsw : StrictWith bar φ N ℓ γ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    (ℓ β : ℝ) = N * φ.evalZ β := by
  obtain ⟨c, hc, hsum⟩ := hβ
  have h1 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  have h3 : φ.evalZ β = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff φ γ).1 hlin c hc
  have h4 : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by simp at h2; linarith
  rw [h4, h3, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hsw.1 i]; ring

example : InRCone ![mulForm] ((3 : ℤ) • mulForm) :=
  ⟨![3], fun i => by fin_cases i; norm_num, LinearMap.ext₂ fun a b => by simp⟩

end GlobalTheory.PolFan.StarKey
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace OrbMark

section Twist

variable {O : Type} [CommRing O]

def twv (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : Fin n → O := fun i => σ (a i)

@[simp] theorem twv_apply (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) (i : Fin n) : twv σ a i = σ (a i) := rfl

theorem twv_zero (σ : O ≃+* O) (n : ℕ) : twv σ (0 : Fin n → O) = 0 := funext fun _ => map_zero σ

theorem twv_smul (σ : O ≃+* O) {n : ℕ} (c : O) (a : Fin n → O) : twv σ (c • a) = σ c • twv σ a :=
  funext fun _ => by simp [twv]

theorem twv_twv (σ τ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv τ (twv σ a) = twv (σ.trans τ) a := rfl

theorem twv_symm_twv (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv σ.symm (twv σ a) = a :=
  funext fun _ => σ.symm_apply_apply _

theorem twv_twv_symm (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv σ (twv σ.symm a) = a :=
  funext fun _ => σ.apply_symm_apply _

def conjLin (σ : O ≃+* O) {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)) : (Fin n → O) →ₗ[O] (Fin m → O) where
  toFun a := twv σ.symm (r (twv σ a))
  map_add' a b := by
    have e : twv σ (a + b) = twv σ a + twv σ b := funext fun _ => map_add σ _ _
    rw [e, map_add]
    exact funext fun _ => map_add σ.symm _ _
  map_smul' c a := by
    rw [twv_smul, map_smul, twv_smul, RingHom.id_apply, σ.symm_apply_apply]

theorem twv_conjLin (σ : O ≃+* O) {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)) (a : Fin n → O) :
    twv σ (conjLin σ r a) = r (twv σ a) := twv_twv_symm σ _

theorem conjLin_surjective (σ : O ≃+* O) {n m : ℕ} {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r) :
    Function.Surjective (conjLin σ r) := fun b => by
  obtain ⟨a, ha⟩ := hr (twv σ b)
  refine ⟨twv σ.symm a, ?_⟩
  show twv σ.symm (r (twv σ (twv σ.symm a))) = b
  rw [twv_twv_symm, ha, twv_symm_twv]

end Twist

section Mark

variable {O : Type} [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀]

def IsOrbForm (v : LinearMap.BilinForm ℤ X₀) (σ : O ≃+* O) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : Prop :=
  ∃ s : (Fin n → O) →ₗ[O] (X₀ ⧸ (CarDim.orad v : Submodule O X₀)), Function.Surjective s ∧
    ∀ (a b : Fin n → O) (x y : X₀), Submodule.Quotient.mk x = s a → Submodule.Quotient.mk y = s b →
      B (twv σ a) (twv σ b) = v x y

theorem isOrbForm_comp_iff (v : LinearMap.BilinForm ℤ X₀) (σ : O ≃+* O) {n m : ℕ}
    {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r) (B : (Fin m → O) → (Fin m → O) → ℝ) :
    IsOrbForm v σ n (fun a b => B (r a) (r b)) ↔ IsOrbForm v σ m B := by
  set r' := conjLin σ r
  have hr' : Function.Surjective r' := conjLin_surjective σ hr
  constructor
  · rintro ⟨s, hs, H⟩
    obtain ⟨t, ht⟩ := Module.projective_lifting_property r' LinearMap.id hr'
    have hrt : ∀ a, r' (t a) = a := fun a => LinearMap.congr_fun ht a
    have hker : ∀ z, r' z = 0 → s z = 0 := by
      intro z hz
      obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (s z)
      rw [← hx]
      refine (Submodule.Quotient.mk_eq_zero _).2 fun c y => ?_
      obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
      have h1 := H (c • z) b (c • x) y (by rw [Submodule.Quotient.mk_smul, map_smul]; exact congrArg _ hx) hb.symm
      have h2 := H 0 b 0 y (by rw [map_zero]; rfl) hb.symm
      have e : r (twv σ (c • z)) = 0 := by
        rw [← twv_conjLin, map_smul, hz, smul_zero, twv_zero]
      have e0 : r (twv σ 0) = 0 := by rw [twv_zero, map_zero]
      dsimp only at h1 h2
      rw [e] at h1
      rw [e0, map_zero, LinearMap.zero_apply] at h2
      exact_mod_cast h1.symm.trans h2
    refine ⟨s ∘ₗ t, fun y => ?_, fun a b x y hx hy => ?_⟩
    · obtain ⟨a, rfl⟩ := hs y
      refine ⟨r' a, ?_⟩
      have : s (a - t (r' a)) = 0 := hker _ (by rw [map_sub, hrt, sub_self])
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    · have h := H (t a) (t b) x y hx hy
      dsimp only at h
      rwa [← twv_conjLin, ← twv_conjLin, hrt, hrt] at h
  · rintro ⟨s, hs, H⟩
    refine ⟨s ∘ₗ r', hs.comp hr', fun a b x y hx hy => ?_⟩
    have h := H (r' a) (r' b) x y hx hy
    show B (r (twv σ a)) (r (twv σ b)) = _
    rwa [twv_conjLin, twv_conjLin] at h

theorem eq_zero_of_isOrbForm_zero {v : LinearMap.BilinForm ℤ X₀} {σ : O ≃+* O} {B : (Fin 0 → O) → (Fin 0 → O) → ℝ}
    (h : IsOrbForm v σ 0 B) : v = 0 := by
  obtain ⟨s, hs, -⟩ := h
  refine LinearMap.ext₂ fun x y => ?_
  have hx : x ∈ (CarDim.orad v : Submodule O X₀) := by
    obtain ⟨a, ha⟩ := hs (Submodule.Quotient.mk x)
    rw [Subsingleton.elim a 0, map_zero] at ha
    exact (Submodule.Quotient.mk_eq_zero _).1 ha.symm
  simpa using hx 1 y

end Mark

section Fun

variable (O : Type) [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀]

open Classical in

def orbFun (w0 : O) (v : LinearMap.BilinForm ℤ X₀) : InvFun O where
  toFun n B := if v ≠ 0 ∧ ∃ σ : O ≃+* O, σ w0 = w0 ∧ IsOrbForm v σ n B then 1 else 0
  inv n m r hr B := by
    simp only [isOrbForm_comp_iff v _ hr]
  zero B := by
    rw [if_neg]
    rintro ⟨hv, σ, -, h⟩
    exact hv (eq_zero_of_isOrbForm_zero h)

variable {O}

open Classical in
theorem orbFun_toFun (w0 : O) (v : LinearMap.BilinForm ℤ X₀) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) :
    (orbFun O w0 v).toFun n B = if v ≠ 0 ∧ ∃ σ : O ≃+* O, σ w0 = w0 ∧ IsOrbForm v σ n B then 1 else 0 := rfl

theorem orbFun_eval_eq_zero_or_one (w0 : O) (v : LinearMap.BilinForm ℤ X₀) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] (B : X → X → ℝ) : (orbFun O w0 v).eval X B = 0 ∨ (orbFun O w0 v).eval X B = 1 := by
  unfold InvFun.eval
  rw [orbFun_toFun]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem eq_zero_of_isOrbForm_const {v : LinearMap.BilinForm ℤ X₀} {σ : O ≃+* O} {n : ℕ}
    (h : IsOrbForm v σ n fun _ _ => 0) : v = 0 := by
  obtain ⟨s, hs, H⟩ := h
  refine LinearMap.ext₂ fun x y => ?_
  obtain ⟨a, ha⟩ := hs (Submodule.Quotient.mk x)
  obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
  have := H a b x y ha.symm hb.symm
  simp only [LinearMap.zero_apply]
  have h0 : ((v x y : ℤ) : ℝ) = 0 := this.symm
  exact_mod_cast h0

theorem orbFun_evalZ_zero (w0 : O) {v : LinearMap.BilinForm ℤ X₀} (hv : v ≠ 0) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] : (orbFun O w0 v).evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun, if_neg]
  rintro ⟨-, σ, -, h⟩
  refine hv (eq_zero_of_isOrbForm_const (σ := σ) (n := n) ?_)
  simpa using h

theorem orbFun_evalZ_self (w0 : O) {v : LinearMap.BilinForm ℤ X₀} [Module.Finite O X₀] (hv : v ≠ 0)
    (hsym : ∀ y z, v y z = v z y) : (orbFun O w0 v).evalZ v = 1 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X₀
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun, if_pos]
  refine ⟨hv, RingEquiv.refl O, rfl, (CarDim.orad v).mkQ ∘ₗ r, (Submodule.mkQ_surjective _).comp hr,
    fun a b x y hx hy => ?_⟩
  have hx' : x - r a ∈ (CarDim.orad v : Submodule O X₀) := (Submodule.Quotient.eq _).1 hx
  have hy' : y - r b ∈ (CarDim.orad v : Submodule O X₀) := (Submodule.Quotient.eq _).1 hy
  have e1 : v x y = v (r a) y := by
    have := hx' 1 y
    rw [one_smul, map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have e2 : v (r a) y = v (r a) (r b) := by
    have := hy' 1 (r a)
    rw [one_smul, map_sub, LinearMap.sub_apply, sub_eq_zero, hsym, hsym (r b)] at this
    exact this
  show ((v (r a) (r b) : ℤ) : ℝ) = (v x y : ℝ)
  rw [e1, e2]

end Fun

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀]

theorem isTwInv_orbFun (H : Host E) (v : LinearMap.BilinForm ℤ X₀) : IsTwInv H (orbFun (𝓞 E) H.w0 v) := by
  intro τ hτ n B
  rw [orbFun_toFun, orbFun_toFun]
  congr 2
  apply propext
  constructor
  · rintro ⟨σ, hσ, s, hs, h⟩
    exact ⟨σ.trans τ, by simp [hσ, hτ], s, hs, fun a b x y hx hy => h a b x y hx hy⟩
  · rintro ⟨σ, hσ, s, hs, h⟩
    refine ⟨σ.trans τ.symm, by simp [hσ, RingEquiv.symm_apply_eq, hτ], s, hs, fun a b x y hx hy => ?_⟩
    have := h a b x y hx hy
    show B (twv τ (twv (σ.trans τ.symm) a)) (twv τ (twv (σ.trans τ.symm) b)) = _
    rw [twv_twv, twv_twv]
    convert this using 3 <;> ext i <;> simp

end Host

example : (orbFun ℤ 0 mulForm).evalZ mulForm = 1 ∧ (orbFun ℤ 0 mulForm).evalZ (0 : LinearMap.BilinForm ℤ ℤ) = 0 := by
  refine ⟨orbFun_evalZ_self 0 (fun h => by simpa using LinearMap.congr_fun₂ h 1 1) fun y z => by simp [mul_comm], ?_⟩
  exact orbFun_evalZ_zero 0 fun h => by simpa using LinearMap.congr_fun₂ h 1 1

end OrbMark

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRStarDepthLeOfCentreBound
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

namespace StarUpper

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone_cell {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCell bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

omit [Module O X] [Module.Finite O X] in

theorem sum_mem_rcone {p : ℕ} {δ : Fin p → LinearMap.BilinForm ℤ X} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (x : Fin p → ℝ) (hx : ∀ i, 0 ≤ x i)
    (h : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (d : Fin m → ℕ), 0 < k ∧ k • δ i = ∑ j, d j • γ j) :
    ∑ i, x i • toReal (δ i) ∈ rcone γ := by
  classical
  have hi : ∀ i, ∃ g : Fin m → ℝ, (∀ j, 0 ≤ g j) ∧ x i • toReal (δ i) = ∑ j, g j • toReal (γ j) := by
    intro i
    by_cases h0 : x i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    obtain ⟨k, d, hk, hkd⟩ := h i h0
    have hxi := hx i
    refine ⟨fun j => x i / k * d j, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
    have e := LinearMap.congr_fun₂ hkd a b
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul, smul_eq_mul] at e
    have e' : (k : ℝ) * (δ i a b : ℝ) = ∑ j, (d j : ℝ) * (γ j a b : ℝ) := by exact_mod_cast e
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    calc x i * (δ i a b : ℝ) = x i / k * ((k : ℝ) * (δ i a b : ℝ)) := by field_simp
      _ = _ := by rw [e', Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  choose g hg hgs using hi
  refine ⟨fun j => ∑ i, g i j, fun j => Finset.sum_nonneg fun i _ => hg i j, ?_⟩
  rw [Finset.sum_congr rfl fun i _ => hgs i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

end StarUpper

open StarUpper in

theorem evalR_starDepth_le : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (s : ℝ),
    IsCell bar ψ γ → B ∈ rcone γ → 0 ≤ s → (∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v →
      ∀ t : ℝ, 0 < t → B - t • toReal v ∈ rcone γ → t ≤ s) → evalR (starDepth bar ψ w) B ≤ s := by
  intro O _ bar ψ w X _ _ _ m γ B s hγ hB hs H
  obtain ⟨c, hc, hBc⟩ := hB
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' O X
  show (starDepth bar ψ w).eval X (fun a b => B a b) ≤ s
  rw [InvFun.eval_eq _ hq]
  refine Real.sSup_le (fun t ht => ?_) hs
  obtain ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB₁, ht0, m₁, γ₁, v₁, hγ₁, hv₁, hv₁p, hwv₁, ⟨e, he, hev⟩, -,
    ⟨d, hd, hdv⟩⟩ := ht
  rcases ht0.eq_or_lt with rfl | htpos
  · exact hs

  have hker : LinearMap.ker q ≤ LinearMap.ker ρ := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    refine hrad _ fun y => ?_
    obtain ⟨y', rfl⟩ := hρ y
    have h1 := hB₁ x y'
    simp only [hx, map_zero, LinearMap.zero_apply] at h1
    exact h1.symm
  let ρ' : X →ₗ[O] X₁ := (LinearMap.ker q).liftQ ρ hker ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hρ' : ∀ a, ρ' (q a) = ρ a := fun a => by
    have : (q.quotKerEquivOfSurjective hq).symm (q a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hρs : Function.Surjective ρ' := fun x => by
    obtain ⟨a, rfl⟩ := hρ x
    exact ⟨q a, hρ' a⟩
  have hBB : ∀ x y, B x y = B₁ (ρ' x) (ρ' y) := fun x y => by
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    rw [hρ', hρ']
    exact hB₁ a b

  set δ : Fin m₁ → LinearMap.BilinForm ℤ X := fun i => pull ρ' (γ₁ i) with hδ
  set v : LinearMap.BilinForm ℤ X := pull ρ' v₁ with hv
  have hv_eq : toReal v = ∑ i, e i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hev (ρ' a) (ρ' b)
    simpa [hδ, hv, LinearMap.sum_apply] using this
  have hd_eq : B - t • toReal v = ∑ i, d i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hdv (ρ' a) (ρ' b)
    simpa [hδ, hv, hBB, LinearMap.sum_apply] using this
  have hrel : ∑ i, (d i + t * e i) • toReal (δ i) = ∑ j, c j • toReal (γ j) := by
    rw [← hBc]
    refine LinearMap.ext₂ fun a b => ?_
    have h1 := LinearMap.congr_fun₂ hd_eq a b
    have h2 := LinearMap.congr_fun₂ hv_eq a b
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at h1 h2 ⊢
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [← h1, ← h2]
    ring
  have hnn : ∀ i, 0 ≤ d i + t * e i := fun i => add_nonneg (hd i) (mul_nonneg ht0 (he i))
  have hlin : evalR ψ (∑ i, (d i + t * e i) • toReal (δ i)) = ∑ i, (d i + t * e i) * ψ.evalZ (δ i) :=
    (linearOn_iff ψ δ).1 ((linearOn_pull_iff hρs).2 hγ₁.linear) _ hnn
  have hcone := inCone_cell hγ (fun i => pull_mem ρ' (hγ₁.mem i)) (fun i y => hγ₁.nonneg i _) hnn hc hlin hrel
  have hInR : InRCone γ v := by
    obtain ⟨c', hc', h'⟩ := sum_mem_rcone e he fun i hi => hcone i
      (add_pos_of_nonneg_of_pos (hd i) (mul_pos htpos (lt_of_le_of_ne (he i) (Ne.symm hi)))).ne'
    exact ⟨c', hc', hv_eq.trans h'⟩
  have hBt : B - t • toReal v ∈ rcone γ := by
    rw [hd_eq]
    exact sum_mem_rcone d hd fun i hi => hcone i
      (add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hd i) (Ne.symm hi)) (mul_nonneg ht0 (he i))).ne'
  exact H v (pull_mem ρ' hv₁) (fun y => hv₁p _) (by rw [hv, evalZ_pull w hρs]; exact hwv₁) hInR t htpos hBt

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedSiegelBasisBalancedForms
section
noncomputable section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem exists_siegel_split {X X₁ : Type} [AddCommGroup X] [AddCommGroup X₁] [Module.Finite ℤ X] [Module.Free ℤ X]
    [Module.Finite ℤ X₁] [Module.Free ℤ X₁] (r : X →ₗ[ℤ] X₁) (σ : X₁ →ₗ[ℤ] X) (hrσ : ∀ y, r (σ y) = y)
    (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hs₀ : ∀ y z, B₀ y z = B₀ z y) (hp₀ : IsPosDef B₀)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (hs₁ : ∀ y z, B₁ y z = B₁ z y) (hp₁ : IsPosDef B₁)
    (n : ℕ) (hn : Module.finrank ℤ X = n) :
    ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (t : ℝ),
      IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ (∀ i j, B₁ (r (b i)) (r (b j)) = gram d u i j) ∧
      ∀ i j, t * B₀ (b i - σ (r (b i))) (b j - σ (r (b j))) + B₁ (r (b i)) (r (b j)) = gram d' u i j := by
  classical
  have hfree : Module.Free ℤ (LinearMap.ker r) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, ⟨bK⟩⟩ : ∃ s, Nonempty (Module.Basis (Fin s) ℤ (LinearMap.ker r)) := ⟨_, ⟨Module.finBasis ℤ _⟩⟩
  obtain ⟨m, ⟨bQ⟩⟩ : ∃ m, Nonempty (Module.Basis (Fin m) ℤ X₁) := ⟨_, ⟨Module.finBasis ℤ _⟩⟩
  let BK : LinearMap.ker r →ₗ[ℤ] LinearMap.ker r →ₗ[ℤ] ℝ := B₀.compl₁₂ (LinearMap.ker r).subtype (LinearMap.ker r).subtype
  have hpK : IsPosDef BK := fun k x hx c hc =>
    hp₀ k (fun i => (x i : X)) (hx.map' (LinearMap.ker r).subtype (Submodule.ker_subtype _)) c hc
  obtain ⟨b₁, d₁, u₁, hS₁, hd₁, hg₁⟩ := GlobalTheory.T.exists_siegelReduced_basis_of_posDef_form s _ bK BK (fun y z => hs₀ _ _) hpK
  obtain ⟨b₂, d₂, u₂, hS₂, hd₂, hg₂⟩ := GlobalTheory.T.exists_siegelReduced_basis_of_posDef_form m _ bQ B₁ hs₁ hp₁
  obtain ⟨t, d, d', u, -, hS, hS', hd', g11, g12, g22⟩ := GlobalTheory.T.exists_siegel_reduction_orthogonal s m d₁ u₁ d₂ u₂ hS₁ hS₂ hd₁ hd₂
  let p : X →ₗ[ℤ] LinearMap.ker r := LinearMap.codRestrict _ (LinearMap.id - σ ∘ₗ r) fun x => by
    simp [hrσ]
  let e : X ≃ₗ[ℤ] LinearMap.ker r × X₁ := LinearEquiv.ofLinear (p.prod r) ((LinearMap.ker r).subtype.coprod σ)
    (by
      ext x
      · simp [p, LinearMap.mem_ker.1 x.2]
      · simp [LinearMap.mem_ker.1 x.2]
      · simp [p, hrσ]
      · simp [hrσ])
    (by ext x; simp [p])
  let c : Module.Basis (Fin (s + m)) ℤ X := ((b₁.prod b₂).map e.symm).reindex finSumFinEquiv
  have hc₁ : ∀ i, c (Fin.castAdd m i) = (b₁ i : X) := fun i => by
    have : finSumFinEquiv.symm (Fin.castAdd m i) = Sum.inl i := finSumFinEquiv_symm_apply_castAdd i
    simp [c, this, e]
  have hc₂ : ∀ j, c (Fin.natAdd s j) = σ (b₂ j) := fun j => by
    have : finSumFinEquiv.symm (Fin.natAdd s j) = Sum.inr j := finSumFinEquiv_symm_apply_natAdd j
    simp [c, this, e]
  have hnm : n = s + m := by
    rw [← hn, Module.finrank_eq_card_basis c, Fintype.card_fin]
  subst hnm
  have hr₁ : ∀ i, r (c (Fin.castAdd m i)) = 0 := fun i => by rw [hc₁]; exact (b₁ i).2
  have hr₂ : ∀ j, r (c (Fin.natAdd s j)) = b₂ j := fun j => by rw [hc₂, hrσ]
  have hq₁ : ∀ i, c (Fin.castAdd m i) - σ (r (c (Fin.castAdd m i))) = (b₁ i : X) := fun i => by
    rw [hr₁, map_zero, sub_zero, hc₁]
  have hq₂ : ∀ j, c (Fin.natAdd s j) - σ (r (c (Fin.natAdd s j))) = 0 := fun j => by rw [hr₂, hc₂, sub_self]
  refine ⟨c, d, d', u, t, hS, hS', hd', fun i j => ?_, fun i j => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [hr₁, (g11 _ _).1]
    · simp [hr₁, (g12 _ _).1]
    · simp [hr₁, (g12 _ _).2.1]
    · rw [hr₂, hr₂, hg₂, (g22 _ _).1]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [hq₁, hq₁, hr₁, hr₁, map_zero, add_zero, (g11 _ _).2, ← hg₁]
      rfl
    · rw [hq₁, hq₂, hr₁]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, add_zero]
      exact (g12 _ _).2.2.1.symm
    · rw [hq₂, hq₁, hr₁]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, add_zero]
      exact (g12 _ _).2.2.2.symm
    · rw [hq₂, hq₂, hr₂, hr₂]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, zero_add]
      rw [hg₂, (g22 _ _).2]

theorem projective_int_of_projective {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] [Module.Free ℤ O]
    [Module.Projective O M] : Module.Projective ℤ M := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective O M›
  let i : M →ₗ[ℤ] (M →₀ O) := s.toAddMonoidHom.toIntLinearMap
  let p : (M →₀ O) →ₗ[ℤ] M := (Finsupp.linearCombination O id).toAddMonoidHom.toIntLinearMap
  exact Module.Projective.of_split i p (LinearMap.ext fun x => LinearMap.congr_fun hs x)

theorem exists_adapted_siegel_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B₀ ∈ realForms H.bar X → IsPosDef B₀ → ∀ n : ℕ, Module.finrank ℤ X = n → ∀ B ∈ psdCone H.bar X, ∃ (b : Module.Basis (Fin n) ℤ X) (d d' : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ B' ∈ realForms H.bar X ∧ (∀ i j, B (b i) (b j) = gram d u i j) ∧ ∀ i j, B' (b i) (b j) = gram d' u i j := by
  intro E _ _ _ H X _ _ _ _ B₀ hB₀ hp₀ n hn B hB
  obtain ⟨X₁, _, _, _, r, B₁, hr, hB₁, hp₁, hBr⟩ := hB
  have : Module.Finite (𝓞 E) X₁ := Module.Finite.of_surjective r hr
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property r LinearMap.id hr
  have hrσ : ∀ y, r (σ y) = y := fun y => LinearMap.congr_fun hσ y
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Finite ℤ X₁ := Module.Finite.trans (𝓞 E) X₁
  have : Module.Projective ℤ X := projective_int_of_projective (O := 𝓞 E)
  have : Module.Projective ℤ X₁ := projective_int_of_projective (O := 𝓞 E)
  have : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  have : Module.Free ℤ X₁ := Module.free_of_finite_type_torsion_free'
  let rZ : X →ₗ[ℤ] X₁ := r.toAddMonoidHom.toIntLinearMap
  let σZ : X₁ →ₗ[ℤ] X := σ.toAddMonoidHom.toIntLinearMap
  obtain ⟨b, d, d', u, t, hS, hS', hd', hg, hg'⟩ := exists_siegel_split rZ σZ hrσ B₀ hB₀.1 hp₀ B₁ hB₁.1 hp₁ n hn
  let π : X →ₗ[𝓞 E] X := LinearMap.id - σ ∘ₗ r
  let πZ : X →ₗ[ℤ] X := π.toAddMonoidHom.toIntLinearMap
  refine ⟨b, d, d', u, t • B₀.compl₁₂ πZ πZ + B₁.compl₁₂ rZ rZ, hS, hS', hd', ⟨fun y z => ?_, fun a y z => ?_⟩,
    fun i j => (hBr _ _).trans (hg i j), fun i j => (hg' i j).symm ▸ ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply]
    rw [hB₀.1, hB₁.1]
  · have e₁ : ∀ y, πZ (a • y) = a • πZ y := fun y => π.map_smul a y
    have e₂ : ∀ y, rZ (a • y) = a • rZ y := fun y => r.map_smul a y
    have e₃ : ∀ y, πZ (H.bar a • y) = H.bar a • πZ y := fun y => π.map_smul _ y
    have e₄ : ∀ y, rZ (H.bar a • y) = H.bar a • rZ y := fun y => r.map_smul _ y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply, e₁, e₂, e₃, e₄]
    rw [hB₀.2, hB₁.2]
  · rfl

end GlobalTheory.RedTh
end
end

