import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPairingEqProdFactorPairings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.PairVal

theorem cubN_succ {A U : Type} [CommGroup A] [CommGroup U] (θ : A → A → A → U) (k : ℕ) (m x : A) :
    cubN θ (k + 1) 1 m x = cubN θ k 1 m x * θ (m ^ k) m x := by
  simp [cubN, Finset.prod_range_succ]

theorem comp_one {B C : Type} [CommGroup B] [CommGroup C] {r : ℕ} {φ : B → Fin r → C}
    (h : ∀ x y j, φ (x * y) j = φ x j * φ y j) (j : Fin r) : φ 1 j = 1 := by
  have := h 1 1 j
  rw [_root_.one_mul] at this
  exact mul_eq_left.1 this.symm

theorem comp_pow {B C : Type} [CommGroup B] [CommGroup C] {r : ℕ} {φ : B → Fin r → C}
    (h : ∀ x y j, φ (x * y) j = φ x j * φ y j) (x : B) (m : ℕ) (j : Fin r) : φ (x ^ m) j = φ x j ^ m := by
  induction m with
  | zero => simp [comp_one h]
  | succ m ih => rw [pow_succ, h, ih, pow_succ]

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

theorem cube_prod (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (U : N'.A → Fˣ)
    (hφ : ∀ x y j, φ (x * y) j = φ x j * φ y j)
    (hc : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u =
      (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) *
      U (x * y) * U (x * u) * U (y * u) * U 1) (k : ℕ) (b a : N'.A) :
    cubN N'.θ k 1 b a * U (b ^ k * a) * U 1 * (U b * U a) ^ k =
      (∏ i, ∏ j, (cubN N.θ k 1 (φ b i * φ b j) (φ a i * φ a j) /
        (cubN N.θ k 1 (φ b i) (φ a i) * cubN N.θ k 1 (φ b j) (φ a j))) ^ W i j) *
      U (b ^ k) * U a * (U (b * a) * U 1) ^ k := by
  induction k with
  | zero => simp [cubN, mul_comm]
  | succ k ih =>
    have h := hc (b ^ k) b a
    simp only [comp_pow hφ, ← mul_pow] at h
    have split : ∀ P p Q q R s : Fˣ, P * p / (Q * q * (R * s)) = P / (Q * R) * (p / (q * s)) := by
      intro P p Q q R s
      rw [_root_.mul_mul_mul_comm, div_mul_div_comm]
    simp only [cubN_succ, split, mul_zpow, Finset.prod_mul_distrib, pow_succ]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_mul, ofMul_pow] at ih' h' ⊢
    linear_combination (norm := abel) ih' + h'

theorem torusExtensionPair_correction_eq_value_quotient (N : NumD F) (g g' : N.Gt) (z z' : N.X) (C C₁ C₂ : Fˣ) :
    g'.s z * g.s z' / (N.θ (N.c z') g'.b (N.c z) * N.θ (N.c z') g'.b g.b * N.θ (N.c z) g.b (N.c z' * g'.b)) *
      (C / (C₁ * C₂)) = (g * g').s (z + z') * C / (g.s z * C₁ * (g'.s z' * C₂)) := by
  rw [NumD.Gt.mul_s, N.c_add]
  have m1 := g.mult z z'
  have m2 := g'.mult z z'
  have co := N.cub.coc (N.c z) (N.c z') g'.b g.b
  rw [N.cub.s12 (N.c z * N.c z') g'.b g.b] at co
  rw [N.cub.s12 (N.c z') g'.b (N.c z), N.cub.s01 (N.c z') (N.c z), N.cub.s12 (N.c z) g.b]
  apply Additive.ofMul.injective
  replace m1 := congrArg Additive.ofMul m1
  replace m2 := congrArg Additive.ofMul m2
  replace co := congrArg Additive.ofMul co
  simp only [ofMul_mul, ofMul_div] at m1 m2 co ⊢
  linear_combination (norm := abel) -m1 - m2 + co

end GlobalTheory.Mum.TensTor.PairVal

namespace GlobalTheory.Mum.TensTor.PairVal

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

theorem tk_tens (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (hT : TensFacts W φ e wv) (U : N'.A → Fˣ) (hU : ∀ x, wv x = (U x : F)) {k : ℕ} (q' p' : N'.QT k)
    (qs ps : Fin r → N.QT k) (hq : QRelV W φ e wv q' qs) (hp : QRelV W φ e wv p' ps) :
    N'.tk q' p' * (U p'.1.2.b * U q'.1.2.b) ^ k =
      (∏ i, ∏ j, (N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j))) ^ W i j) *
      (U (p'.1.2.b * q'.1.2.b) * U 1) ^ k := by
  obtain ⟨hφ, -, -, -, -, -, hcube, -⟩ := hT
  have hcU : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u =
      (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) *
      U (x * y) * U (x * u) * U (y * u) * U 1 := by
    intro x y u
    apply Units.ext
    simp only [Units.val_mul, ← hU]
    exact hcube x y u
  have hA := cube_prod W φ U hφ hcU k p'.1.2.b q'.1.2.b
  simp only [hp.2.1, hq.2.1] at hA
  have hG := hq.2.2 p'.1.1.toAdd
  simp only [hU, ← Units.val_mul] at hG
  replace hG := Units.ext hG
  simp only [hp.1, hq.2.1, ← N'.QT_pow_b p'] at hG
  have hX : ∀ i j, N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) =
      (qs j).1.2.s (ps i).1.1.toAdd * (qs i).1.2.s (ps j).1.1.toAdd /
        (N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (N.c (ps i).1.1.toAdd) *
          N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (qs i).1.2.b *
          N.θ (N.c (ps i).1.1.toAdd) (qs i).1.2.b (N.c (ps j).1.1.toAdd * (qs j).1.2.b)) *
      (cubN N.θ k 1 ((ps i).1.2.b * (ps j).1.2.b) ((qs i).1.2.b * (qs j).1.2.b) /
        (cubN N.θ k 1 (ps i).1.2.b (qs i).1.2.b * cubN N.θ k 1 (ps j).1.2.b (qs j).1.2.b)) :=
    fun i j => (torusExtensionPair_correction_eq_value_quotient N (qs i).1.2 (qs j).1.2 (ps i).1.1.toAdd (ps j).1.1.toAdd _ _ _).symm
  simp only [hX, mul_zpow, Finset.prod_mul_distrib]
  rw [NumD.tk]
  apply Additive.ofMul.injective
  have hA' := congrArg Additive.ofMul hA
  have hG' := congrArg Additive.ofMul hG
  simp only [ofMul_mul, ofMul_pow] at hA' hG' ⊢
  linear_combination (norm := abel) hA' + hG'

theorem wp_eq_prod : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (k : ℕ), 1 ≤ k → ∀ (q' p' : N'.QT k) (qs ps : Fin r → N.QT k), QRelV W φ e wv q' qs → QRelV W φ e wv p' ps → N'.wp q' p' = ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j := by
  intro F _ N N' r W φ e wv hT k _ q' p' qs ps hq hp
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hT.2.2.2.2.2.1 x)
  have hU : ∀ x, wv x = (U x : F) := fun x => rfl
  have h1 := tk_tens W φ e wv hT U hU q' p' qs ps hq hp
  have h2 := tk_tens W φ e wv hT U hU p' q' ps qs hp hq
  rw [mul_comm q'.1.2.b p'.1.2.b] at h2
  have hper : ∀ i j, N.wp (qs i) (ps j) * N.wp (qs j) (ps i) =
      N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) /
        (N.tk (ps i * ps j) (qs i * qs j) / (N.tk (ps i) (qs i) * N.tk (ps j) (qs j))) := by
    intro i j
    have e1 := WpPairing.wp_mul_left N (qs i) (qs j) (ps i * ps j)
    have e2 := WpPairing.wp_mul_right N (qs i) (ps i) (ps j)
    have e3 := WpPairing.wp_mul_right N (qs j) (ps i) (ps j)
    simp only [NumD.wp] at e1 e2 e3 ⊢
    apply Additive.ofMul.injective
    replace e1 := congrArg Additive.ofMul e1
    replace e2 := congrArg Additive.ofMul e2
    replace e3 := congrArg Additive.ofMul e3
    simp only [ofMul_mul, ofMul_div] at e1 e2 e3 ⊢
    linear_combination (norm := abel) -e1 - e2 - e3
  have hR : ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j =
      ∏ i, ∏ j, (N.wp (qs i) (ps j) * N.wp (qs j) (ps i)) ^ W i j := by
    simp only [Matrix.add_apply, Matrix.transpose_apply, zpow_add, Finset.prod_mul_distrib, mul_zpow]
    congr 1
    rw [Finset.prod_comm]
  have hD : ∀ f g : Fin r → Fin r → Fˣ, ∏ i, ∏ j, (f i j / g i j) ^ W i j =
      (∏ i, ∏ j, f i j ^ W i j) / ∏ i, ∏ j, g i j ^ W i j := by
    intro f g
    simp only [div_zpow, Finset.prod_div_distrib]
  rw [hR]
  simp only [hper]
  rw [hD]
  rw [NumD.wp]
  apply Additive.ofMul.injective
  have h1' := congrArg Additive.ofMul h1
  have h2' := congrArg Additive.ofMul h2
  simp only [ofMul_mul, ofMul_pow, ofMul_div] at h1' h2' ⊢
  linear_combination (norm := abel) h1' - h2'

end GlobalTheory.Mum.TensTor.PairVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem cube_corr {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (xi xj yi yj ui uj : A) (sji sij tji tij : U) :
    sji * tji / θ xi yj uj * (sij * tij / θ xj yi ui) /
        (θ xj (yj * uj) xi * θ xj (yj * uj) (yi * ui) * θ xi (yi * ui) (xj * (yj * uj))) *
      (θ (xi * xj) (yi * yj) (ui * uj) / (θ xi yi ui * θ xj yj uj)) =
    sji * sij / (θ xj yj xi * θ xj yj yi * θ xi yi (xj * yj)) *
      (tji * tij / (θ xj uj xi * θ xj uj ui * θ xi ui (xj * uj))) := by
  have hp : ∀ x y z, θ x y z = θ y x z ∧ θ x y z = θ x z y ∧ θ x y z = θ z x y ∧ θ x y z = θ y z x ∧
      θ x y z = θ z y x := fun x y z =>
    ⟨h.s01 x y z, h.s12 x y z, (h.s12 x y z).trans (h.s01 x z y), (h.s01 x y z).trans (h.s12 y x z),
      ((h.s01 x y z).trans (h.s12 y x z)).trans (h.s01 y z x)⟩
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have c0 := E (show θ (xi * xj) (yi * yj) (ui * uj) * θ xi xj (ui * uj) = θ xi (xj * yi * yj) (ui * uj) * θ xj (yi * yj) (ui * uj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * yj) (ui * uj))
  have c1 := E (show θ (xj * ui) uj (yi * yj) * θ xj ui (yi * yj) = θ xj (ui * uj) (yi * yj) * θ ui uj (yi * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj ui uj (yi * yj))
  have c2 := E (show θ (xj * ui) (yi * yj) uj * θ xj ui uj = θ xj (yi * yj * ui) uj * θ ui (yi * yj) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj ui (yi * yj) uj)
  have c3 := E (show θ (xj * yj) uj (yi * ui) * θ xj yj (yi * ui) = θ xj (yj * uj) (yi * ui) * θ yj uj (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yj uj (yi * ui))
  have c4 := E (show θ (xj * yj) (yi * ui) uj * θ xj yj uj = θ xj (yi * yj * ui) uj * θ yj (yi * ui) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yj (yi * ui) uj)
  have c5 := E (show θ (xj * yi) ui yj * θ xj yi yj = θ xj (yi * ui) yj * θ yi ui yj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yi ui yj)
  have c6 := E (show θ (xj * yi) yj ui * θ xj yi ui = θ xj (yi * yj) ui * θ yi yj ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yi yj ui)
  have c7 := E (show θ (xi * xj) (yj * uj) (yi * ui) * θ xi xj (yi * ui) = θ xi (xj * yj * uj) (yi * ui) * θ xj (yj * uj) (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yj * uj) (yi * ui))
  have c8 := E (show θ (xi * xj) (yi * ui) (yj * uj) * θ xi xj (yj * uj) = θ xi (xj * yi * ui) (yj * uj) * θ xj (yi * ui) (yj * uj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * ui) (yj * uj))
  have c9 := E (show θ (xi * ui) uj (xj * yi * yj) * θ xi ui (xj * yi * yj) = θ xi (ui * uj) (xj * yi * yj) * θ ui uj (xj * yi * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui uj (xj * yi * yj))
  have c10 := E (show θ (xi * ui) (xj * yi * yj) uj * θ xi ui uj = θ xi (xj * yi * yj * ui) uj * θ ui (xj * yi * yj) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui (xj * yi * yj) uj)
  have c11 := E (show θ (xi * yj) uj (xj * yi * ui) * θ xi yj (xj * yi * ui) = θ xi (yj * uj) (xj * yi * ui) * θ yj uj (xj * yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yj uj (xj * yi * ui))
  have c12 := E (show θ (xi * yj) (xj * yi * ui) uj * θ xi yj uj = θ xi (xj * yi * yj * ui) uj * θ yj (xj * yi * ui) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yj (xj * yi * ui) uj)
  have c13 := E (show θ (xi * ui) uj xj * θ xi ui xj = θ xi (ui * uj) xj * θ ui uj xj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui uj xj)
  have c14 := E (show θ (xi * ui) xj uj * θ xi ui uj = θ xi (xj * ui) uj * θ ui xj uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui xj uj)
  have c15 := E (show θ (xi * xj) uj ui * θ xi xj ui = θ xi (xj * uj) ui * θ xj uj ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj uj ui)
  have c16 := E (show θ (xi * xj) ui uj * θ xi xj uj = θ xi (xj * ui) uj * θ xj ui uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj ui uj)
  have c17 := E (show θ (xi * yi) ui (xj * yj) * θ xi yi (xj * yj) = θ xi (yi * ui) (xj * yj) * θ yi ui (xj * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yi ui (xj * yj))
  have c18 := E (show θ (xi * yi) (xj * yj) ui * θ xi yi ui = θ xi (xj * yi * yj) ui * θ yi (xj * yj) ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yi (xj * yj) ui)
  have c19 := E (show θ (xi * xj) (yi * ui) yj * θ xi xj yj = θ xi (xj * yi * ui) yj * θ xj (yi * ui) yj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * ui) yj)
  have c20 := E (show θ (xi * xj) yj (yi * ui) * θ xi xj (yi * ui) = θ xi (xj * yj) (yi * ui) * θ xj yj (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj yj (yi * ui))
  have p0 := E (hp xj (yj * uj) xi).2.2.1
  have p1 := E (hp xj yj xi).2.2.1
  have p2 := E (hp xj yj yi).2.1
  have p3 := E (hp xj uj xi).2.2.1
  have p4 := E (hp (xj * ui) uj (yi * yj)).2.2.1
  have p5 := E (hp xj ui (yi * yj)).2.1
  have p6 := E (hp xj (ui * uj) (yi * yj)).2.1
  have p7 := E (hp ui uj (yi * yj)).2.2.1
  have p8 := E (hp (xj * ui) (yi * yj) uj).1
  have p9 := E (hp ui (yi * yj) uj).1
  have p10 := E (hp (xj * yj) uj (yi * ui)).2.1
  have p11 := E (hp yj uj (yi * ui)).2.1
  have p12 := E (hp (xj * yi) ui yj).2.1
  have p13 := E (hp xj (yi * ui) yj).2.1
  have p14 := E (hp yi ui yj).2.1
  have p15 := E (hp (xi * xj) (yj * uj) (yi * ui)).2.1
  have p16 := E (hp xi (xj * yj * uj) (yi * ui)).2.1
  have p17 := E (hp xj (yj * uj) (yi * ui)).2.1
  have p18 := E (hp (xi * ui) uj (xj * yi * yj)).2.2.1
  have p19 := E (hp xi ui (xj * yi * yj)).2.1
  have p20 := E (hp xi (ui * uj) (xj * yi * yj)).2.1
  have p21 := E (hp ui uj (xj * yi * yj)).2.2.1
  have p22 := E (hp (xi * ui) (xj * yi * yj) uj).1
  have p23 := E (hp ui (xj * yi * yj) uj).1
  have p24 := E (hp (xi * yj) uj (xj * yi * ui)).2.1
  have p25 := E (hp xi (yj * uj) (xj * yi * ui)).2.1
  have p26 := E (hp yj uj (xj * yi * ui)).2.1
  have p27 := E (hp (xi * ui) uj xj).2.2.1
  have p28 := E (hp xi ui xj).2.1
  have p29 := E (hp xi (ui * uj) xj).2.1
  have p30 := E (hp ui uj xj).2.2.1
  have p31 := E (hp (xi * ui) xj uj).1
  have p32 := E (hp ui xj uj).1
  have p33 := E (hp (xi * xj) uj ui).2.1
  have p34 := E (hp xi (xj * uj) ui).2.1
  have p35 := E (hp (xi * yi) ui (xj * yj)).2.1
  have p36 := E (hp xi (yi * ui) (xj * yj)).2.1
  have p37 := E (hp yi ui (xj * yj)).2.1
  have p38 := E (hp (xi * xj) (yi * ui) yj).2.1
  have p39 := E (hp xi (xj * yi * ui) yj).2.1
  rw [← mul_assoc xj yj uj]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at *
  linear_combination (norm := abel) c0 - c1 + c2 + c3 - c4 + c5 - c6 + c7 - c8 - c9 + c10 + c11 - c12 + c13 - c14 - c15 + c16 + c17 - c18 + c19 - c20 - p0 + p1 + p2 + p3 + p4 + p5 - p6 - p7 - p8 + p9 - p10 + p11 - p12 + 2 • p13 + p14 - p15 + p16 + p17 + p18 + p19 - p20 - p21 - p22 + p23 - p24 + p25 + p26 - p27 - p28 + p29 + p30 + p31 - p32 + p33 - p34 - p35 + p36 + p37 - p38 + p39

end GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem vmul_comb {U : Type} [CommGroup U] (s1 s2 t P1 P2 P Q wc wb wb' wcb wcb' wbb' wcbb' w1 : U)
    (h1 : s1 * wc * wb = P1 * wcb * w1) (h2 : s2 * wc * wb' = P2 * wcb' * w1)
    (h3 : t * wcbb' * wc * wb * wb' = Q * wcb * wcb' * wbb' * w1) (h4 : P * Q = P1 * P2) :
    s1 * s2 / t * wc * wbb' = P * wcbb' * w1 := by
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a1 := E h1; have a2 := E h2; have a3 := E h3; have a4 := E h4
  simp only [ofMul_mul, ofMul_div] at *
  linear_combination (norm := abel) a1 + a2 - a3 - a4

theorem gtRelV_mul : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv →
    ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us →
      GtRelV W φ e wv (v' * u') (vs * us) := by
  intro F _ N N' r W φ e wv hT v' u' vs us hv hu
  obtain ⟨hφ, -, -, -, hφc, hw0, hcub, -⟩ := hT
  refine ⟨fun j => ?_, fun χ' => ?_⟩
  · show φ (v'.b * u'.b) j = (vs j).b * (us j).b
    rw [hφ, hv.1, hu.1]
  · let w : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
    let Pf : (Fin r → N.Gt) → Fˣ := fun g => ∏ i, ∏ j, ((g j).s (e χ' i) * (g i).s (e χ' j) /
      (N.θ (N.c (e χ' j)) (g j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (g j).b (g i).b *
        N.θ (N.c (e χ' i)) (g i).b (N.c (e χ' j) * (g j).b))) ^ W i j
    let Qf : Fˣ := ∏ i, ∏ j, (N.θ (N.c (e χ' i) * N.c (e χ' j)) ((vs i).b * (vs j).b) ((us i).b * (us j).b) /
      (N.θ (N.c (e χ' i)) (vs i).b (us i).b * N.θ (N.c (e χ' j)) (vs j).b (us j).b)) ^ W i j
    have h1 : v'.s χ' * w (N'.c χ') * w v'.b = Pf vs * w (N'.c χ' * v'.b) * w 1 := Units.ext (hv.2 χ')
    have h2 : u'.s χ' * w (N'.c χ') * w u'.b = Pf us * w (N'.c χ' * u'.b) * w 1 := Units.ext (hu.2 χ')
    have h3 := hcub (N'.c χ') v'.b u'.b
    rw [mul_assoc (N'.c χ') v'.b u'.b] at h3
    simp only [hφc, hv.1, hu.1] at h3
    have h3' : N'.θ (N'.c χ') v'.b u'.b * w (N'.c χ' * (v'.b * u'.b)) * w (N'.c χ') * w v'.b * w u'.b =
        Qf * w (N'.c χ' * v'.b) * w (N'.c χ' * u'.b) * w (v'.b * u'.b) * w 1 := Units.ext h3
    have h4 : Pf (vs * us) * Qf = Pf vs * Pf us := by
      simp only [Pf, Qf]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← mul_zpow, ← mul_zpow]
      exact congrArg (· ^ W i j) (cube_corr N.cub (N.c (e χ' i)) (N.c (e χ' j)) (vs i).b (vs j).b (us i).b (us j).b
        ((vs j).s (e χ' i)) ((vs i).s (e χ' j)) ((us j).s (e χ' i)) ((us i).s (e χ' j)))
    exact congrArg Units.val (vmul_comb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3' h4)

end GlobalTheory.Mum.TensTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniqueComponents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem eq_zero_of_sum_smul_matrix {G : Type} [AddCommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : IsUnit M.det) (f : Fin r → G) (h : ∀ i, ∑ j, M i j • f j = 0) (k : Fin r) : f k = 0 := by
  have e1 : f k = ∑ j, (1 : Matrix (Fin r) (Fin r) ℤ) k j • f j := by
    simp [Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_mul M hM]
  simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, h, smul_zero, Finset.sum_const_zero]

theorem eq_one_of_prod_zpow_matrix {G : Type} [CommGroup G] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : IsUnit M.det) (f : Fin r → G) (h : ∀ i, ∏ j, f j ^ M i j = 1) (k : Fin r) : f k = 1 := by
  have := eq_zero_of_sum_smul_matrix M hM (fun j => Additive.ofMul (f j)) (fun i => by
    simpa [← ofMul_zpow, ← ofMul_prod] using congrArg Additive.ofMul (h i)) k
  simpa using this

theorem gtRelV_prod_tor_mul {F : Type} [Field F] {N : NumD F} {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (x : Fin r → N.X)
    (vs : Fin r → N.Gt) (T : Fin r → (Multiplicative N.X →* Fˣ)) :
    (∏ i, ∏ j, ((N.tor (T j) * vs j).s (x i) * (N.tor (T i) * vs i).s (x j) /
        (N.θ (N.c (x j)) (N.tor (T j) * vs j).b (N.c (x i)) * N.θ (N.c (x j)) (N.tor (T j) * vs j).b
            (N.tor (T i) * vs i).b *
          N.θ (N.c (x i)) (N.tor (T i) * vs i).b (N.c (x j) * (N.tor (T j) * vs j).b))) ^ W i j : Fˣ) =
      (∏ i, ∏ j, ((vs j).s (x i) * (vs i).s (x j) /
        (N.θ (N.c (x j)) (vs j).b (N.c (x i)) * N.θ (N.c (x j)) (vs j).b (vs i).b *
          N.θ (N.c (x i)) (vs i).b (N.c (x j) * (vs j).b))) ^ W i j) *
      ∏ i, ∏ j, (T j (Multiplicative.ofAdd (x i)) * T i (Multiplicative.ofAdd (x j))) ^ W i j := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← mul_zpow]
  congr 1
  simp only [NumD.tor_mul_s_apply, NumD.Gt.mul_b, NumD.tor_b, one_mul, div_eq_mul_inv]
  ac_rfl

theorem gtRelV_prod_single {G : Type} [CommGroup G] {A : Type} [AddCommGroup A] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Fin r → (Multiplicative A →* G)) (i : Fin r) (χ : A) :
    (∏ a, ∏ b, (T b (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) a)) *
        T a (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) b))) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ (W + W.transpose) i j := by
  simp only [mul_zpow, Finset.prod_mul_distrib]
  have h1 : (∏ a, ∏ b, T b (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) a)) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ W i j := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro a _ ha
      simp [Pi.single_apply, ha]
    · simp
  have h2 : (∏ a, ∏ b, T a (Multiplicative.ofAdd ((Pi.single i χ : Fin r → A) b)) ^ W a b) =
      ∏ j, T j (Multiplicative.ofAdd χ) ^ W j i := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.add_apply, Matrix.transpose_apply, zpow_add]

theorem gtRelV_components_unique : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F),
    TensFacts W φ e wv → IsUnit (W + W.transpose).det →
      ∀ (v' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv v' us → vs = us := by
  intro F _ N N' r W φ e wv hT hdet v' vs us hv hu
  have hb : ∀ j, (us j).b = (vs j).b := fun j => (hu.1 j).symm.trans (hv.1 j)
  have ht : ∀ j, ∃ t, N.tor t = us j / vs j := fun j =>
    (N.exists_tor_iff _).2 (by rw [div_eq_mul_inv, NumD.Gt.mul_b, NumD.Gt.inv_b, hb, mul_inv_cancel])
  choose T hT' using ht
  have hus : us = fun j => N.tor (T j) * vs j := funext fun j => by rw [hT', div_mul_cancel]
  subst hus
  have hwv : ∀ x, wv x ≠ 0 := hT.2.2.2.2.2.1
  have key : ∀ χ', (∏ i, ∏ j, (T j (Multiplicative.ofAdd (e χ' i)) * T i (Multiplicative.ofAdd (e χ' j))) ^ W i j) = 1 := by
    intro χ'
    have a := hv.2 χ'
    have b := hu.2 χ'
    rw [a, gtRelV_prod_tor_mul W (e χ') vs T] at b
    have c := mul_right_cancel₀ (hwv _) (mul_right_cancel₀ (hwv 1) b)
    have d := Units.ext c
    exact (mul_eq_left.1 d.symm)
  have hall : ∀ χ j, T j (Multiplicative.ofAdd χ) = 1 := by
    intro χ
    refine eq_one_of_prod_zpow_matrix (W + W.transpose) hdet (fun j => T j (Multiplicative.ofAdd χ)) fun i => ?_
    obtain ⟨χ', hχ'⟩ := hT.2.2.2.1.2 (Pi.single i χ)
    have := key χ'
    rw [hχ', gtRelV_prod_single W T i χ] at this
    exact this
  funext j
  have : T j = 1 := MonoidHom.ext fun m => by simpa using hall m.toAdd j
  rw [this, NumD.tor_one, _root_.one_mul]

end GlobalTheory.Mum.TensTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSquareUnitsLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_section_square_units_local : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (L2 : LB G₁.left) (h : L2.Sec) (Lθ : LB (pullback G₁.hom (jK R'))), Lθ.IsLB → ∀ θ : Lθ.Sec, (∀ j i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (L2.U j)).hom (h.f j))) → ∀ x : G₁.left, ∀ j (hx : x ∈ L2.U j), ∀ p : Ideal (G₁.left.presheaf.stalk x), p.IsPrime → Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p = ⊥ → ∃ a b c : G₁.left.presheaf.stalk x, b ∉ p ∧ c ∉ p ∧ b * (G₁.left.presheaf.germ (L2.U j) x hx).hom (h.f j) = c * a ^ 2 := by
  first | exact @GlobalTheory.SqHorizontal.horizontal | exact GlobalTheory.SqHorizontal.horizontal | (intros; apply GlobalTheory.SqHorizontal.horizontal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTransitionCompat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem isCoordEnd_thickMap_compat : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a' a) rosatiε)) (F : thickObj R I e G ⟶ thickObj R I e G) (F' : thickObj R I (e + 1) G ⟶ thickObj R I (e + 1) G), IsCoordEnd (U.gt e) a a' h' u F → IsCoordEnd (U.gt (e + 1)) a a' h' u F' → thickMap R I e G ≫ F'.left = F.left ≫ thickMap R I e G := by
  intro R _ _ I D A G _ _ U e a a' h' u F F' hF hF'
  have hq := U.gt_q e
  have hO : GlobalTheory.LevelCompat.thickMapOver I e G ≫ (U.gt (e + 1)).pG = (U.gt e).pG := Over.OverMorphism.ext hq
  have hL : ∀ χ, thickMap R I e G ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt (e + 1)).pG).left =
      (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left := by
    intro χ
    have : GlobalTheory.LevelCompat.thickMapOver I e G ≫ lift (toUnit _ ≫ D.toPre.c χ) (U.gt (e + 1)).pG =
        lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG := by
      simp only [comp_lift, comp_toUnit_assoc, hO]
    exact congrArg (·.left) this
  refine GlobalTheory.TorusCoord.ext_of_val (U.gt (e + 1)) _ _ ?_ ?_
  · calc (thickMap R I e G ≫ F'.left) ≫ (U.gt (e + 1)).pG.left
          = thickMap R I e G ≫ ((U.gt (e + 1)).pG.left ≫ a.left) := by rw [Category.assoc, hF'.1]
      _ = (U.gt e).pG.left ≫ a.left := by rw [← Category.assoc, hq]
      _ = F.left ≫ (U.gt e).pG.left := hF.1.symm
      _ = (F.left ≫ thickMap R I e G) ≫ (U.gt (e + 1)).pG.left := by rw [Category.assoc, hq]
  · intro χ w J hJ
    have e1 := hF'.2 χ _ (thickMap R I e G) w J hJ
    have e2 := hF.2 χ _ (𝟙 _) w J hJ
    rw [Category.id_comp] at e2
    rw [e1, ← val_pull hJ, val_corr hJ (U.gt_t e χ), e2]
    congr 1
    · have e3 := val_pull hJ ((U.gt (e + 1)).t (h' χ)) (thickMap R I e G) (𝟙 _)
      rw [Category.id_comp] at e3
      rw [← e3, val_corr hJ (U.gt_t e _)]
    · rw [val_pull hJ, val_pull hJ, hL, Category.id_comp]

end GlobalTheory.Mum.EndThick
end
end

