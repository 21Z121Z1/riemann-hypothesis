import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerValuationLowerBoundSumPowTwelve
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0625
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridScalarOfProjectorScalar

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDegreeZeroCocyclesCorrespond
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq_id {a : (NE κ)ᵒᵖ} (f : a ⟶ a) : f = 𝟙 a :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem mp_single (c : CC F 0) (i j : κ) (hij : j = i) (h : sub (ne {j} (Finset.singleton_nonempty j)) ⊆
    sub (ne {i} (Finset.singleton_nonempty i))) (hc : ({j} : Finset κ).card = 0 + 1) :
    mp F (homOf h) (c ⟨{j}, hc⟩) = c ⟨{i}, Finset.card_singleton i⟩ := by
  subst hij
  rw [hom_eq_id (homOf h), mp_id]

theorem sum_cubeSign_two (t : Finset κ) (ht : t.card = 2) : ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hxy]
  rcases lt_or_gt_of_ne hxy with h | h
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]

theorem orderedCech_degreeZero_cocycles_correspond : (∀ c : CC F 0, δ F 0 c = 0 → e0 F c = 0 → c = 0) ∧
    ∀ g : C0 F, d0 F g = 0 → ∃ c : CC F 0, δ F 0 c = 0 ∧ e0 F c = g := by
  refine ⟨fun c _ he => ?_, fun g hg => ?_⟩
  · funext s
    obtain ⟨s, hs⟩ := s
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    have H := congrFun he (ne {i} (Finset.singleton_nonempty i))
    have hm : mn (ne {i} (Finset.singleton_nonempty i)) = i := Finset.min'_singleton i
    have := mp_single F c i _ hm
    simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply] at H
    exact (this (Finset.singleton_subset_iff.2 (mn_mem _)) (Finset.card_singleton _)).symm.trans H
  · have hg' : ∀ {T T' : (NE κ)ᵒᵖ} (φ : T ⟶ T'), mp F φ (g T) = g T' := by
      intro T T' φ
      have := congrFun (congrFun (congrFun hg T) T') φ
      rw [amitsur_d0_apply] at this
      exact (sub_eq_zero.1 this).symm
    refine ⟨fun s => g (ne s.1 (card_nonempty s)), ?_, ?_⟩
    · funext t
      rw [δ_apply]
      simp only [hg']
      rw [← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i),
        sum_cubeSign_two t.1 t.2, zero_smul]
      rfl
    · funext a
      simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact hg' _

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDifferentialZeroConstOne
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem sum_cubeSign_card_two {κ : Type} [LinearOrder κ] (t : Finset κ) (h : t.card = 2) :
    ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
  have key : ∀ x y : κ, x < y → ∑ i ∈ ({x, y} : Finset κ), GlobalTheory.cubeSign {x, y} i = 0 := by
    intro x y hxy
    rw [Finset.sum_pair hxy.ne]
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, hxy, hxy.not_gt]
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h
  rcases lt_or_gt_of_ne hxy with h' | h'
  · exact key x y h'
  · rw [Finset.pair_comm]; exact key y x h'

theorem δ_zero_one : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), δ F 0 (fun _ => 1) = 0 := by
  intro κ _ R _ F
  funext t
  rw [δ_apply]
  simp only [map_one, Pi.zero_apply]
  rw [← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i),
    sum_cubeSign_card_two t.1 t.2, zero_smul]

end GlobalTheory.CechPoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsOneCoboundaryComm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPosetDegreeOne
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

open Classical in

def val {p : ℕ} (c : CC F p) (s : Finset κ) (b : (NE κ)ᵒᵖ) : F.obj b :=
  if h : s.card = p + 1 ∧ s ⊆ sub b then
    mp F (homOf (a := ne s (card_nonempty ⟨s, h.1⟩)) (b := b) h.2) (c ⟨s, h.1⟩) else 0

theorem val_eq {p : ℕ} (c : CC F p) (s : {s : Finset κ // s.card = p + 1}) (b : (NE κ)ᵒᵖ)
    (f : ne s.1 (card_nonempty s) ⟶ b) : mp F f (c s) = val F c s.1 b := by
  unfold val
  obtain ⟨s, hs⟩ := s
  have hsub : s ⊆ sub b := sub_subset f
  rw [dif_pos (⟨hs, hsub⟩ : s.card = p + 1 ∧ s ⊆ sub b)]
  exact congrArg (fun φ => mp F φ (c ⟨s, hs⟩)) (Subsingleton.elim _ _)

theorem mp_val {p : ℕ} (c : CC F p) (s : Finset κ) {b d : (NE κ)ᵒᵖ} (g : b ⟶ d)
    (h : s.card = p + 1) (hs : s ⊆ sub b) : mp F g (val F c s b) = val F c s d := by
  rw [← val_eq F c ⟨s, h⟩ b (homOf hs), ← mp_comp, val_eq]

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (c : CC F 1) {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) :
    e1 F c a b f = if mn b < mn a then - val F c {mn b, mn a} b else 0 := by
  simp only [e1, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    exact congrArg Neg.neg (val_eq F c ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ b _)
  · rfl

theorem alternatingToOrderedCechDegreeTwo_apply_valueAtSubset (c : CC F 2) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    e2 F c a b d f g = if mn d < mn b ∧ mn b < mn a then - val F c {mn d, mn b, mn a} d else 0 := by
  simp only [e2, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    exact congrArg Neg.neg (val_eq F c ⟨{mn d, mn b, mn a}, card_three h.1 h.2⟩ d _)
  · rfl

theorem val_δ {p : ℕ} (c : CC F p) (t : Finset κ) (d : (NE κ)ᵒᵖ) (h : t.card = p + 1 + 1)
    (ht : t ⊆ sub d) :
    val F (δ F p c) t d = ∑ i ∈ t, GlobalTheory.cubeSign t i • val F c (t.erase i) d := by
  rw [← val_eq F (δ F p c) ⟨t, h⟩ d (homOf ht), δ_apply, map_sum,
    ← Finset.sum_coe_sort t (fun i => GlobalTheory.cubeSign t i • val F c (t.erase i) d)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← mp_comp, val_eq]

theorem val_δ_three (c : CC F 1) {x y z : κ} (h₁ : x < y) (h₂ : y < z) (d : (NE κ)ᵒᵖ)
    (ht : ({x, y, z} : Finset κ) ⊆ sub d) :
    val F (δ F 1 c) {x, y, z} d = val F c {y, z} d - val F c {x, z} d + val F c {x, y} d := by
  have h₃ := h₁.trans h₂
  rw [val_δ F c _ d (card_three h₁ h₂) ht, Finset.sum_insert (by simp [h₁.ne, h₃.ne]),
    Finset.sum_pair h₂.ne]
  have e₁ : ({x, y, z} : Finset κ).erase x = {y, z} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₁.ne', h₃.ne']
  have e₂ : ({x, y, z} : Finset κ).erase y = {x, z} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₁.ne, h₂.ne']
  have e₃ : ({x, y, z} : Finset κ).erase z = {x, y} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₃.ne, h₂.ne]
  have s₁ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) x = 1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₁.not_gt, h₃.not_gt]
  have s₂ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) y = -1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₁, h₂.not_gt]
  have s₃ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) z = 1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₃, h₂, Finset.card_pair h₁.ne]
  rw [e₁, e₂, e₃, s₁, s₂, s₃]
  simp only [one_smul, neg_smul]
  ring

theorem orderedCechToCatCochainsOne_coboundary_comm {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (c : CC F 1) : d1 F (e1 F c) = e2 F (δ F 1 c) := by
  funext a b d f g
  rw [d1_apply, orderedCechToCatCochainsOne_apply_valueAtSubset, orderedCechToCatCochainsOne_apply_valueAtSubset, orderedCechToCatCochainsOne_apply_valueAtSubset, alternatingToOrderedCechDegreeTwo_apply_valueAtSubset]
  rcases (mn_le_of_hom f).lt_or_eq with h₂ | h₂ <;> rcases (mn_le_of_hom g).lt_or_eq with h₁ | h₁
  · rw [if_pos h₂, if_pos h₁, if_pos (h₁.trans h₂), if_pos ⟨h₁, h₂⟩, map_neg,
      mp_val F c _ g (Finset.card_pair h₂.ne) (pair_subset f),
      val_δ_three F c h₁ h₂ d (triple_subset f g)]
    ring
  · rw [if_pos h₂, if_neg h₁.not_lt, if_pos (h₁ ▸ h₂), if_neg (fun h => h₁.not_lt h.1), map_neg,
      mp_val F c _ g (Finset.card_pair h₂.ne) (pair_subset f), h₁]
    ring
  · rw [if_neg h₂.not_lt, if_pos h₁, if_pos (h₂ ▸ h₁), if_neg (fun h => h₂.not_lt h.2), map_zero, h₂]
    ring
  · rw [if_neg h₂.not_lt, if_neg h₁.not_lt, if_neg (h₁.trans h₂).not_lt,
      if_neg (fun h => h₂.not_lt h.2), map_zero]
    ring

end GlobalTheory.CechPosetDegreeOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsZeroCoboundaryComm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem mp_cochain_congr {p : ℕ} (c : CC F p) {s s' : {s : Finset κ // s.card = p + 1}} (h : s.1 = s'.1)
    {b : (NE κ)ᵒᵖ} (φ : ne s.1 (card_nonempty s) ⟶ b) (φ' : ne s'.1 (card_nonempty s') ⟶ b) :
    mp F φ (c s) = mp F φ' (c s') := by
  obtain rfl : s = s' := Subtype.ext h
  rw [Subsingleton.elim φ φ']

theorem orderedCech_cochainsZero_coboundary_comm {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 0) : d0 F (e0 F c) = e1 F (δ F 0 c) := by
  funext a b f
  rw [amitsur_d0_apply]
  simp only [e0, e1, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    AlgHom.toLinearMap_apply]
  rw [← mp_comp]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      AlgHom.toLinearMap_apply]
    rw [δ_apply, map_sum]
    have hb : mn b ∈ ({mn b, mn a} : Finset κ) := by simp
    have ha : mn a ∈ ({mn b, mn a} : Finset κ) := by simp
    have s1 : GlobalTheory.cubeSign ({mn b, mn a} : Finset κ) (mn b) = 1 :=
      GlobalTheory.cubeSign_eq_one_of_forall_le (by simp [h.le])
    have s2 : GlobalTheory.cubeSign ({mn b, mn a} : Finset κ) (mn a) = -1 := by
      have := GlobalTheory.cubeSign_erase_of_lt (t := {mn b, mn a}) hb h
      rw [Finset.erase_insert (by simp [h.ne]), GlobalTheory.cubeSign_singleton] at this
      omega
    rw [Fintype.sum_eq_add (⟨mn b, hb⟩ : ({mn b, mn a} : Finset κ)) ⟨mn a, ha⟩
      (fun e => h.ne (congrArg Subtype.val e))
      (by
        rintro ⟨x, hx⟩ ⟨h1, h2⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (h1 rfl).elim
        · exact (h2 rfl).elim)]
    simp only [s1, s2, one_smul, neg_smul, map_neg, ← mp_comp]
    rw [neg_add, neg_neg, neg_add_eq_sub]
    refine congrArg₂ (· - ·) ?_ ?_
    · refine mp_cochain_congr F c (s := ⟨{mn b}, Finset.card_singleton _⟩)
        (s' := GlobalTheory.Cube.eraseIdx ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ ⟨mn a, ha⟩) ?_ _ _
      show {mn b} = Finset.erase {mn b, mn a} (mn a)
      rw [Finset.pair_comm, Finset.erase_insert (by simp [h.ne'])]
    · refine mp_cochain_congr F c (s := ⟨{mn a}, Finset.card_singleton _⟩)
        (s' := GlobalTheory.Cube.eraseIdx ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ ⟨mn b, hb⟩) ?_ _ _
      show {mn a} = Finset.erase {mn b, mn a} (mn b)
      rw [Finset.erase_insert (by simp [h.ne])]
  · have e : mn b = mn a := le_antisymm (mn_le_of_hom f) (not_lt.1 h)
    rw [LinearMap.zero_apply, sub_eq_zero]
    refine mp_cochain_congr F c (s := ⟨{mn b}, Finset.card_singleton _⟩)
      (s' := ⟨{mn a}, Finset.card_singleton _⟩) ?_ _ _
    show ({mn b} : Finset κ) = {mn a}
    rw [e]

end GlobalTheory.CechPoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectProjectionNaturalIdempotentReduced
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PerfectProj

theorem exists_pow_prime_pow_kill (p : ℕ) (hp : 1 < p) (k B : Type) [Field k] [CommRing B]
    [Algebra k B] [Module.Finite k B] :
    ∃ r : ℕ, ∀ x : B, IsNilpotent x → x ^ (p ^ r) = 0 := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := B)
  refine ⟨n, fun x hx => ?_⟩
  have hmem : x ^ n ∈ (nilradical B) ^ n := Ideal.pow_mem_pow (mem_nilradical.mpr hx) n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hmem
  exact pow_eq_zero_of_le (Nat.lt_pow_self hp).le hmem

theorem exists_eq_pow_prime_pow (p : ℕ) {A : Type} [CommRing A] (π : A → A)
    (h : ∀ a, ∃ b, π a = π b ^ p) : ∀ (m : ℕ) (a : A), ∃ b, π a = π b ^ (p ^ m) := by
  intro m
  induction m with
  | zero => intro a; exact ⟨a, by simp⟩
  | succ m ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨c, hc⟩ := h b
    exact ⟨c, by rw [hb, hc, ← pow_mul, pow_succ']⟩

theorem natural_idempotent_reduced : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A B : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Module.Finite k B] (π : A →ₐ[k] A) (π' : B →ₐ[k] B), ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : B, IsNilpotent (a - π' a)) ∧ ∀ a : B, ∃ b : B, π' a = π' b ^ p) → (∀ (f : A →ₐ[k] B) (a : A), f (π a) = π' (f a)) ∧ (∀ b, π' (π' b) = π' b) ∧ ∀ b, IsNilpotent (π' b) → π' b = 0 := by
  intro p _ k _ _ A B _ _ _ _ _ π π' hA hB
  rcases subsingleton_or_nontrivial B with hs | hs
  · exact ⟨fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _,
      fun _ _ => Subsingleton.elim _ _⟩
  haveI : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
  obtain ⟨r, hr⟩ := exists_pow_prime_pow_kill p (Fact.out : p.Prime).one_lt k B
  have iA := exists_eq_pow_prime_pow p π hA.2 r
  have iB := exists_eq_pow_prime_pow p π' hB.2 r
  have h3 : ∀ b, IsNilpotent (π' b) → π' b = 0 := by
    intro b hb
    obtain ⟨c, hc⟩ := iB b
    rw [hc] at hb ⊢
    exact hr _ hb.of_pow
  refine ⟨fun f a => ?_, fun y => ?_, h3⟩
  · obtain ⟨b, hb⟩ := iA a
    obtain ⟨c, hc⟩ := iB (f a)
    have hd : IsNilpotent (f (π a) - π' (f a)) := by
      have h1 : IsNilpotent (f (a - π a)) := (hA.1 a).map f
      have h2 := hB.1 (f a)
      have e : f (π a) - π' (f a) = (f a - π' (f a)) - f (a - π a) := by rw [map_sub]; ring
      rw [e]
      exact (Commute.all _ _).isNilpotent_sub h2 h1
    have he : f (π a) - π' (f a) = (f (π b) - π' c) ^ (p ^ r) := by
      rw [sub_pow_char_pow, hb, hc, map_pow]
    rw [he] at hd
    exact sub_eq_zero.mp (he.trans (hr _ hd.of_pow))
  · obtain ⟨c, hc⟩ := iB y
    have he : π' (π' y) - π' y = (π' (π' c) - π' c) ^ (p ^ r) := by
      rw [sub_pow_char_pow, hc, map_pow]
    have hn : IsNilpotent (π' (π' c) - π' c) := by
      rw [← neg_sub]; exact (hB.1 (π' c)).neg
    exact sub_eq_zero.mp (he.trans (hr _ hn))

end GlobalTheory.PerfectProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.SubstCalc

variable {R : Type} [CommRing R]

theorem constantCoeff_subst_of_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add, constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem hasSubst_elim {d : ℕ} {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

theorem subst_powerSeriesEvalTwoGroups {d : ℕ} {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {a : τ → MvPowerSeries τ' R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i)) := by
  unfold at2
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  funext s
  cases s <;> rfl

theorem powerSeriesEvalTwoGroups_rules_alt : ∀ (R : Type) [CommRing R] (d : ℕ) (τ τ' : Type) [Finite τ] (u v : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ f, at2 (inL f) u v = subst u f) ∧ (∀ f, at2 (inR f) u v = subst v f) ∧ (∀ c c', at2 (c + c') u v = at2 c u v + at2 c' u v ∧ at2 (c - c') u v = at2 c u v - at2 c' u v) ∧ (∀ c, constantCoeff (at2 c u v) = constantCoeff c) ∧ (∀ c, at2 (swap c) u v = at2 c v u) ∧ (∀ (e : ℕ) (μ : Fin e → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ f : MvPowerSeries (Fin e) R, at2 (subst μ f) u v = subst (fun i => at2 (μ i) u v) f) ∧ (∀ a : τ → MvPowerSeries τ' R, (∀ t, constantCoeff (a t) = 0) → ∀ c, subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, cob2 (addLaw R d) c = 0 → at2 c u v - at2 c (u + u) v + at2 c u (u + v) - at2 c u u = 0 := by
  intro R _ d τ τ' _ u v hu hv
  have hs := hasSubst_elim hu hv
  have hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold at2 inL
    rw [subst_comp_subst_apply hX hs]
    congr 1
    funext i
    rw [subst_X hs]; rfl
  · intro f
    unfold at2 inR
    rw [subst_comp_subst_apply hY hs]
    congr 1
    funext i
    rw [subst_X hs]; rfl
  · intro c c'
    unfold at2
    exact ⟨subst_add hs _ _, subst_sub hs _ _⟩
  · intro c
    unfold at2
    exact constantCoeff_subst_of_zero (fun s => by cases s <;> simp [hu, hv]) c
  · intro c
    have hW : HasSubst (Sum.elim (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (fun i => X (Sum.inl i))) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp
    unfold swap at2
    rw [subst_comp_subst_apply hW hs]
    congr 1
    funext s
    cases s <;> simp [subst_X hs]
  · intro e μ hμ f
    unfold at2
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ) hs]
  · intro a ha c
    exact subst_powerSeriesEvalTwoGroups hu hv ha c
  · intro c hc
    set w : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim u v) with hw
    have hw0 : ∀ t, constantCoeff (w t) = 0 := fun t => by
      rcases t with t | t | t <;> simp [hw, hu, hv]
    have hsw : HasSubst w := hasSubst_of_constantCoeff_zero hw0
    have h1 : ∀ i, subst w (x1 (R := R) (d := d) i) = u i := fun i => by
      unfold x1; rw [subst_X hsw]; rfl
    have h2 : ∀ i, subst w (x2 (R := R) (d := d) i) = u i := fun i => by
      unfold x2; rw [subst_X hsw]; rfl
    have h3 : ∀ i, subst w (x3 (R := R) (d := d) i) = v i := fun i => by
      unfold x3; rw [subst_X hsw]; rfl
    have hx0 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx20 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx30 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
        op (addLaw R d) a b = a + b := by
      intro a b ha hb
      funext i
      unfold op addLaw at2
      have := hasSubst_elim ha hb
      rw [subst_add this, subst_X this, subst_X this]
      rfl
    have hop0 : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
        ∀ i, constantCoeff ((a + b) i) = 0 := by
      intro a b ha hb i; simp [ha, hb]
    have key := congrArg (subst w) hc
    unfold cob2 at key
    rw [hop _ _ hx0 hx20, hop _ _ hx20 hx30] at key
    rw [subst_sub hsw, subst_add hsw, subst_sub hsw,
      subst_powerSeriesEvalTwoGroups hx20 hx30 hw0, subst_powerSeriesEvalTwoGroups (hop0 _ _ hx0 hx20) hx30 hw0,
      subst_powerSeriesEvalTwoGroups hx0 (hop0 _ _ hx20 hx30) hw0, subst_powerSeriesEvalTwoGroups hx0 hx20 hw0] at key
    have e : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (fun i => subst w ((a + b) i)) = (fun i => subst w (a i)) + (fun i => subst w (b i)) := by
      intro a b; funext i; simp only [Pi.add_apply]; exact subst_add hsw _ _
    rw [e, e] at key
    simp only [h1, h2, h3] at key
    have e0 : subst w (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := by
      simpa using (subst_sub hsw (0 : MvPowerSeries _ R) 0)
    rw [e0] at key
    convert key using 2

end GlobalTheory.Katz.SubstCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerValuationLowerBoundSumPowTwelveStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve : ∀ (l : ℕ), l.Prime → ∀ (r : ℝ) (J : Type) [Fintype J] (u x : J → ℂ), (∀ j, IntAt l (u j)) → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r (x j ^ 12)) → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r ((∑ j, u j * x j) ^ 12) := by
  first | exact @GlobalTheory.LatValSum.valGe_sum_pow_twelve | exact GlobalTheory.LatValSum.valGe_sum_pow_twelve | (intros; apply GlobalTheory.LatValSum.valGe_sum_pow_twelve <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfDiscreteSpacesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveBundleFormula_of_discrete_spaces : ∀ (q : ℕ) [NeZero q] (N : ℕ), (∀ (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V) → ∀ {E : Spc} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V := by
  first | (exact @GlobalTheory.PBFg.pbf_of_disc) | (exact GlobalTheory.PBFg.pbf_of_disc) | (intros; apply GlobalTheory.PBFg.pbf_of_disc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridDenominatorBoundStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projector_grid_denominator_bound : GlobalTheory.LeviCut.GridInt := by
  first | exact @GlobalTheory.LeviCut.gridInt_holds | exact GlobalTheory.LeviCut.gridInt_holds | (intros; apply GlobalTheory.LeviCut.gridInt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridScalarOfProjectorScalarStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectorGridScalar_of_projectorScalar : GlobalTheory.LeviCut.StepScalar → GlobalTheory.LeviCut.GridScalar := by
  first | exact @GlobalTheory.LeviCut.gridScalar_of_stepScalar | exact GlobalTheory.LeviCut.gridScalar_of_stepScalar | (intros; apply GlobalTheory.LeviCut.gridScalar_of_stepScalar <;> assumption)
end

