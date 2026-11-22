import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquiv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
noncomputable section
namespace GlobalTheory.Relabel.TwIso
variable {O : Type} [CommRing O] {N N' : NumD O} {k : ℕ} (β : N.Form k) (u : Oˣ)

def twP (r : Oˣ) (y : N.X) (g : N.Gt) : (N.twist β u).Gt :=
  ⟨g.b, fun z => g.s z * r ^ β.be y z, (N.twG β r g (fun z => β.be y z) (fun _ _ => map_add _ _ _)).mult⟩

theorem twistMap_add_mul (r : Oˣ) (y y' : N.X) (g g' : N.Gt) :
    twP β u r (y + y') (g * g') = twP β u r y g * twP β u r y' g' :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * g'.s z / N.θ (N.c z) g.b g'.b * r ^ β.be (y + y') z =
      g.s z * r ^ β.be y z * (g'.s z * r ^ β.be y' z) / N.θ (N.c z) g.b g'.b
    rw [map_add, LinearMap.add_apply, zpow_add]
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel)

theorem twistMap_mul_mul (r r' : Oˣ) (y : N.X) (g g' : N.Gt) :
    twP β u (r * r') y (g * g') = twP β u r y g * twP β u r' y g' :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * g'.s z / N.θ (N.c z) g.b g'.b * (r * r') ^ β.be y z =
      g.s z * r ^ β.be y z * (g'.s z * r' ^ β.be y z) / N.θ (N.c z) g.b g'.b
    rw [mul_zpow]
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel)

theorem twistMap_pow (r : Oˣ) (y : N.X) (g : N.Gt) (m : ℕ) : twP β u r y g ^ m = twP β u (r ^ m) y (g ^ m) := by
  induction m with
  | zero =>
    simp only [pow_zero]
    refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
    show (1 : Oˣ) = 1 * 1 ^ β.be y z
    simp
  | succ m ih =>
    rw [pow_succ (twP β u r y g) m, ih, ← twistMap_mul_mul, ← pow_succ, ← pow_succ]

theorem twistMap_io (y : N.X) : twP β u u y (N.io y) = (N.twist β u).io y :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show N.τ y z * u ^ β.be y z = (N.twist β u).τ y z
    rw [NumD.twist_τ])

theorem twistMap_nsmul (r : Oˣ) (j : ℕ) (y : N.X) (g : N.Gt) : twP β u r (j • y) g = twP β u (r ^ j) y g :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * r ^ β.be (j • y) z = g.s z * (r ^ j) ^ β.be y z
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast])

theorem twistMap_bijective₂ (r : Oˣ) (y : N.X) : Function.Bijective (twP β u r y) := by
  constructor
  · intro g g' h
    have hb : g.b = g'.b := congrArg (fun x => x.b) h
    have hs : ∀ z, g.s z * r ^ β.be y z = g'.s z * r ^ β.be y z :=
      fun z => congrFun (congrArg (fun x => x.s) h) z
    exact NumD.Gt.ext hb (funext fun z => mul_right_cancel (hs z))
  · intro h
    refine ⟨⟨h.b, fun z => h.s z * r⁻¹ ^ β.be y z,
      (N.twG β r⁻¹ ⟨h.b, h.s, h.mult⟩ (fun z => β.be y z) (fun _ _ => map_add _ _ _)).mult⟩, ?_⟩
    refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
    show h.s z * r⁻¹ ^ β.be y z * r ^ β.be y z = h.s z
    rw [inv_zpow, inv_mul_cancel_right]

def isoG {M M' : NumD O} (J : NumD.Iso M M') : M.Gt →* M'.Gt :=
  MonoidHom.mk' (NumD.Hom.ofIso J).img fun g h =>
    (((NumD.Hom.ofIso J).rel_iff _ _).1 (((NumD.Hom.ofIso J).rel_img g).mul ((NumD.Hom.ofIso J).rel_img h))).symm

theorem rel_iff_isoG {M M' : NumD O} (J : NumD.Iso M M') (g : M.Gt) (g' : M'.Gt) : J.Rel g g' ↔ g' = isoG J g := by
  rw [← NumD.Hom.ofIso_rel, NumD.Hom.rel_iff]
  exact Iff.rfl

theorem isoG_io {M M' : NumD O} (J : NumD.Iso M M') (y : M.X) : isoG J (M.io y) = M'.io (J.e y) :=
  (((NumD.Hom.ofIso J).rel_iff _ _).1 ((NumD.Hom.ofIso J).rel_io y)).symm

private theorem eq_of_div_eq_div_div {G : Type*} [CommGroup G] {a b c d x y : G} (h1 : a = b) (h2 : c = d)
    (h : x / y = a / b / (c / d)) : x = y := by
  rw [div_eq_one.mpr h1, div_eq_one.mpr h2, div_one] at h
  exact div_eq_one.mp h

theorem isoG_bijective {M M' : NumD O} (J : NumD.Iso M M') : Function.Bijective (isoG J) := by
  refine ⟨(injective_iff_map_eq_one (isoG J)).2 fun g hg => ?_, fun g' => ?_⟩
  · obtain ⟨hb, hs⟩ := (rel_iff_isoG J g 1).2 hg.symm
    have hgb : g.b = 1 := by
      have h1 : J.φ g.b = 1 := by rw [← hb]; rfl
      exact (MulEquiv.map_eq_one_iff J.φ).1 h1
    refine NumD.Gt.ext hgb (funext fun χ => ?_)
    have h2 := hs χ
    simp only [NumD.Gt.generator_inv_base, hgb, _root_.mul_one, J.h_one, _root_.one_mul] at h2
    show g.s χ = 1
    exact mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)
  · refine ⟨⟨J.φ.symm g'.b, fun χ => g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) /
        (J.h (M.c χ) * J.h (J.φ.symm g'.b)), fun χ χ' => ?_⟩, ?_⟩
    · have hm := g'.mult (J.e χ) (J.e χ')
      have ht := J.θ_eq (M.c χ) (M.c χ') (J.φ.symm g'.b)
      rw [J.c_eq, J.c_eq, ← map_add J.e χ χ'] at hm
      rw [MulEquiv.apply_symm_apply] at ht
      rw [M.c_add]
      refine eq_of_div_eq_div_div hm ht ?_
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel
    · refine ((rel_iff_isoG J _ g').1 ⟨(J.φ.apply_symm_apply _).symm, fun χ => ?_⟩).symm
      show g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) = g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) /
        (J.h (M.c χ) * J.h (J.φ.symm g'.b)) * J.h (M.c χ) * J.h (J.φ.symm g'.b)
      rw [mul_assoc _ (J.h (M.c χ)), div_mul_cancel]

variable {β u} (J : NumD.Iso (N.twist β u) N')

theorem twJ_elim {r : Oˣ} {j : ℕ} {q : N.QT j} {q' : N'.QT j} (h : TwJ β u r J q q') :
    q'.1.1.toAdd = J.e q.1.1.toAdd ∧ q'.1.2 = isoG J (twP β u r q.1.1.toAdd q.1.2) := by
  obtain ⟨p, ⟨h1, h2, h3⟩, e, hr⟩ := h
  have hp : p.1.2 = twP β u r q.1.1.toAdd q.1.2 := NumD.Gt.ext h2 (funext h3)
  refine ⟨e.trans (congrArg (fun x => J.e (Multiplicative.toAdd x)) h1), ?_⟩
  rw [← hp]
  exact (rel_iff_isoG J _ _).1 hr

def twQ {r : Oˣ} {j : ℕ} (h : r ^ j = u) (q : N.QT j) : (N.twist β u).QT j :=
  ⟨(q.1.1, twP β u r q.1.1.toAdd q.1.2), by
    change twP β u r q.1.1.toAdd q.1.2 ^ j = (N.twist β u).io q.1.1.toAdd
    rw [twistMap_pow, h, N.mem_QT.1 q.2, twistMap_io]⟩

def tauHom {r : Oˣ} {j : ℕ} (h : r ^ j = u) : N.QT j →* N'.QT j :=
  MonoidHom.mk' (fun q => ⟨(Multiplicative.ofAdd (J.e q.1.1.toAdd), isoG J (twP β u r q.1.1.toAdd q.1.2)), by
      change isoG J (twP β u r q.1.1.toAdd q.1.2) ^ j = N'.io (J.e q.1.1.toAdd)
      rw [← map_pow, twistMap_pow, h, N.mem_QT.1 q.2, twistMap_io]
      exact isoG_io J _⟩)
    fun q q' => Subtype.ext (Prod.ext (congrArg Multiplicative.ofAdd (map_add J.e q.1.1.toAdd q'.1.1.toAdd))
      ((congrArg (isoG J) (twistMap_add_mul β u r q.1.1.toAdd q'.1.1.toAdd q.1.2 q'.1.2)).trans (map_mul _ _ _)))

theorem tauHom_bijective {r : Oˣ} {j : ℕ} (h : r ^ j = u) : Function.Bijective (tauHom J h) := by
  constructor
  · intro q₁ q₂ hq
    have h1 : J.e q₁.1.1.toAdd = J.e q₂.1.1.toAdd := congrArg (fun q => q.1.1.toAdd) hq
    have h2 : isoG J (twP β u r q₁.1.1.toAdd q₁.1.2) = isoG J (twP β u r q₂.1.1.toAdd q₂.1.2) :=
      congrArg (fun q => q.1.2) hq
    have e1 : q₁.1.1.toAdd = q₂.1.1.toAdd := J.e.injective h1
    rw [e1] at h2
    have e2 := (twistMap_bijective₂ β u r _).1 ((isoG_bijective J).1 h2)
    exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective e1) e2)
  · intro q'
    obtain ⟨g', hg'⟩ := (isoG_bijective J).2 q'.1.2
    obtain ⟨g, hg⟩ := (twistMap_bijective₂ β u r (J.e.symm q'.1.1.toAdd)).2 g'
    refine ⟨⟨(Multiplicative.ofAdd (J.e.symm q'.1.1.toAdd), g), ?_⟩, ?_⟩
    · have hq := N'.mem_QT.1 q'.2
      have e0 : twP β u r (J.e.symm q'.1.1.toAdd) g ^ j = twP β u u (J.e.symm q'.1.1.toAdd) (g ^ j) :=
        (twistMap_pow β u r (J.e.symm q'.1.1.toAdd) g j).trans
          (congrArg (fun s => twP β u s (J.e.symm q'.1.1.toAdd) (g ^ j)) h)
      have hq2 : isoG J (twP β u u (J.e.symm q'.1.1.toAdd) (g ^ j)) = N'.io q'.1.1.toAdd :=
        (congrArg (isoG J) e0.symm).trans ((map_pow (isoG J) _ j).trans
          ((congrArg (fun t => isoG J t ^ j) hg).trans ((congrArg (· ^ j) hg').trans hq)))
      have hio : isoG J (twP β u u (J.e.symm q'.1.1.toAdd) (N.io (J.e.symm q'.1.1.toAdd))) = N'.io q'.1.1.toAdd :=
        (congrArg (isoG J) (twistMap_io β u (J.e.symm q'.1.1.toAdd))).trans
          ((isoG_io J _).trans (congrArg N'.io (J.e.apply_symm_apply _)))
      exact N.mem_QT.2 ((twistMap_bijective₂ β u u _).1 ((isoG_bijective J).1 (hq2.trans hio.symm)))
    · refine Subtype.ext (Prod.ext ?_ ?_)
      · show Multiplicative.ofAdd (J.e (J.e.symm q'.1.1.toAdd)) = q'.1.1
        rw [J.e.apply_symm_apply]
        rfl
      · exact (congrArg (isoG J) hg).trans hg'

theorem tauHom_qTriv {r : Oˣ} {j : ℕ} (h : r ^ j = u) (z : N.X) : tauHom J h (N.qTriv j z) = N'.qTriv j (J.e z) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact congrArg Multiplicative.ofAdd (map_nsmul J.e j z)
  · exact (congrArg (isoG J) ((twistMap_nsmul β u r j z (N.io z)).trans
      (show twP β u (r ^ j) z (N.io z) = (N.twist β u).io z by rw [h, twistMap_io]))).trans (isoG_io J z)

theorem wp_twQ {r : Oˣ} {j : ℕ} (h : r ^ j = u) (q₁ q₂ : N.QT j) :
    (N.twist β u).wp (twQ (β := β) h q₁) (twQ h q₂) = N.wp q₁ q₂ := by
  show q₁.1.2.s q₂.1.1.toAdd * r ^ β.be q₁.1.1.toAdd q₂.1.1.toAdd * cubN N.θ j 1 q₂.1.2.b q₁.1.2.b /
      (q₂.1.2.s q₁.1.1.toAdd * r ^ β.be q₂.1.1.toAdd q₁.1.1.toAdd * cubN N.θ j 1 q₁.1.2.b q₂.1.2.b) =
    q₁.1.2.s q₂.1.1.toAdd * cubN N.θ j 1 q₂.1.2.b q₁.1.2.b /
      (q₂.1.2.s q₁.1.1.toAdd * cubN N.θ j 1 q₁.1.2.b q₂.1.2.b)
  rw [β.symm q₂.1.1.toAdd q₁.1.1.toAdd]
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel

end GlobalTheory.Relabel.TwIso

open GlobalTheory.Relabel.TwIso in

theorem GlobalTheory.Relabel.twJ_mulEquiv : ∀ (O : Type) [CommRing O] (N N' : NumD O) (k : ℕ) (β : N.Form k) (u : Oˣ) (J : NumD.Iso (N.twist β u) N'), (∀ (r : Oˣ) (j : ℕ), r ^ j = u → ∃ τ : N.QT j ≃* N'.QT j, (∀ q q', τ q = q' ↔ TwJ β u r J q q') ∧ (∀ q₁ q₂, N.QEq q₁ q₂ ↔ N'.QEq (τ q₁) (τ q₂)) ∧ ∀ q₁ q₂, N'.wp (τ q₁) (τ q₂) = N.wp q₁ q₂) ∧ ∀ (r₁ r₂ : Oˣ) (n n' m : ℕ) (q₁ : N.QT n) (q₂ : N.QT n') (q₁' : N'.QT n) (q₂' : N'.QT n'), r₂ ^ m = r₁ → q₁.1.1 = q₂.1.1 → q₁.1.2 = q₂.1.2 ^ m → TwJ β u r₁ J q₁ q₁' → TwJ β u r₂ J q₂ q₂' → q₁'.1.1 = q₂'.1.1 ∧ q₁'.1.2 = q₂'.1.2 ^ m := by
  intro O _ N N' k β u J
  refine ⟨fun r j h => ?_, fun r₁ r₂ n n' m q₁ q₂ q₁' q₂' hr e1 e2 t1 t2 => ?_⟩
  · refine ⟨MulEquiv.ofBijective (tauHom J h) (tauHom_bijective J h), fun q q' => ?_,
      fun q₁ q₂ => ?_, fun q₁ q₂ => ?_⟩
    · show tauHom J h q = q' ↔ _
      constructor
      · rintro rfl
        exact ⟨twQ (β := β) h q, ⟨rfl, rfl, fun _ => rfl⟩, rfl, (rel_iff_isoG J _ _).2 rfl⟩
      · intro ht
        obtain ⟨e, he⟩ := twJ_elim J ht
        refine Subtype.ext (Prod.ext ?_ he.symm)
        exact (congrArg Multiplicative.ofAdd e).symm
    · rw [NumD.qEq_iff, NumD.qEq_iff]
      show (∃ z, q₂ = q₁ * N.qTriv j z) ↔ ∃ z, tauHom J h q₂ = tauHom J h q₁ * N'.qTriv j z
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨J.e z, (map_mul _ _ _).trans (congrArg _ (tauHom_qTriv J h z))⟩
      · rintro ⟨z, hz⟩
        refine ⟨J.e.symm z, (tauHom_bijective J h).1 ?_⟩
        exact hz.trans ((congrArg (tauHom J h q₁ * ·) ((tauHom_qTriv J h (J.e.symm z)).trans
          (congrArg (N'.qTriv j) (J.e.apply_symm_apply z))).symm).trans (map_mul (tauHom J h) q₁ _).symm)
    · have hrel : ∀ q : N.QT j, (NumD.Hom.ofIso J).Rel (twQ (β := β) h q).1.2 (tauHom J h q).1.2 :=
        fun q => (NumD.Hom.ofIso J).rel_img _
      have hw := NumD.Hom.wp_eq (NumD.Hom.ofIso J) (twQ (β := β) h q₁) (twQ (β := β) h q₂)
        (tauHom J h q₁) (tauHom J h q₂) rfl (hrel q₁) rfl (hrel q₂)
      rw [wp_twQ] at hw
      show N'.wp (tauHom J h q₁) (tauHom J h q₂) = _
      rw [hw]
      exact Units.ext rfl
  · obtain ⟨a1, b1⟩ := twJ_elim J t1
    obtain ⟨a2, b2⟩ := twJ_elim J t2
    refine ⟨?_, ?_⟩
    · exact Multiplicative.toAdd.injective
        (a1.trans ((congrArg (fun x => J.e (Multiplicative.toAdd x)) e1).trans a2.symm))
    · rw [b1, b2]
      calc isoG J (twP β u r₁ q₁.1.1.toAdd q₁.1.2) = isoG J (twP β u r₂ q₂.1.1.toAdd q₂.1.2 ^ m) := by
            rw [twistMap_pow, hr, e1, e2]
        _ = _ := map_pow _ _ _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxStOfPtSt
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.Arch
variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}

namespace Dict
variable (d : Dict N B)

theorem tx_ex_zero : d.ex 0 = 1 := (d.ab.2.2.1 0).2 B.abelian₂.zero_mem

theorem tx_ex_smul (n : ℕ) (x : Fin B.gB → ℂ) : d.ex ((n : ℂ) • x) = d.ex x ^ n := by
  induction n with
  | zero => simp [d.tx_ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, d.ab.1, ih, pow_succ]

theorem tx_ex_neg (x : Fin B.gB → ℂ) : d.ex (-x) = (d.ex x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← d.ab.1, neg_add_cancel, d.tx_ex_zero])

theorem tx_dbl (x : Fin B.gB → ℂ) : dbl N.θ N.σ (d.ex x) * d.fr (x + x) = d.fr x ^ 4 := by
  have a := d.ab.2.2.2.2.2.1 x (-x) x
  have b := d.ab.2.2.2.2.2.2.1 x
  rw [add_neg_cancel, neg_add_cancel, zero_add, d.ab.2.2.2.1, d.tx_ex_neg] at a
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a b ⊢
  linear_combination (norm := abel) a - b

theorem tx_cubN (x : Fin B.gB → ℂ) (i : ℕ) :
    cubN N.θ i 1 (d.ex x) (d.ex x) * d.fr ((i : ℂ) • x) * d.fr x * d.fr (x + x) ^ i =
      d.fr ((i : ℂ) • x + x) * d.fr x ^ (2 * i) := by
  induction i with
  | zero => simp [cubN, d.ab.2.2.2.1]
  | succ i ih =>
    have a := d.ab.2.2.2.2.2.1 ((i : ℂ) • x) x x
    rw [d.tx_ex_smul] at a
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, one_mul, Nat.mul_succ, pow_add (d.fr x), pow_succ (d.fr (x + x))]
    replace a := congrArg Additive.ofMul a
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [ofMul_mul, sq] at a ih ⊢
    linear_combination (norm := abel) a + ih

theorem tx_cubN_div (x : Fin B.gB → ℂ) (i : ℕ) :
    cubN N.θ i 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ i * d.fr ((i : ℂ) • x) * d.fr x * d.fr x ^ (2 * i) =
      d.fr ((i : ℂ) • x + x) := by
  have a := congrArg Additive.ofMul (d.tx_cubN x i)
  have b := congrArg (fun t => Additive.ofMul (t ^ i)) (d.tx_dbl x)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b ⊢
  linear_combination (norm := module) a - b

theorem tx_mulq (x : Fin B.gB → ℂ) (n : ℕ) :
    mulq N.θ N.σ n (d.ex x) * d.fr x ^ (n ^ 2) = d.fr ((n : ℂ) • x) := by
  induction n with
  | zero => simp [mulq, d.ab.2.2.2.1]
  | succ n ih =>
    rw [mulq] at ih
    rw [mulq, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, ← d.tx_cubN_div, ← ih,
      show (n + 1) ^ 2 = n ^ 2 + 1 + 2 * n by ring, pow_add, pow_succ]
    simp only [mul_assoc, mul_left_comm]

theorem tx_isPt_pow (h : PtSt) {v : B.V} {g : N.Gt} (hg : d.IsPt v g) (n : ℕ) : d.IsPt ((n : ℂ) • v) (g ^ n) := by
  obtain ⟨-, -, h3, h4, -⟩ := h O N B d
  induction n with
  | zero =>
    rw [pow_zero, h4]
    exact ⟨0, rfl, by simp⟩
  | succ n ih =>
    rw [Nat.cast_succ, add_smul, one_smul, pow_succ]
    exact h3 _ _ _ _ ih hg

theorem tx_vt {v : B.V} {g : N.Gt} (hg : d.IsPt v g) (x : B.X) :
    N.vt g (d.eX x) = B.term 1 0 d.th x v * d.fr v.2 := by
  have a := hg.2 x
  have b := congrArg Units.val (d.ψ_eq x)
  rw [NumD.vt, hg.1, d.c_eq, ← d.ab.1, d.ab.2.2.2.2.2.2.2.2, AnArc.term, add_comm v.2, ← b]
  simp only [Units.val_mul, pow_one, map_zero, AnArc.e_zero, zero_add, one_smul]
  linear_combination (N.ψ (d.eX x) : ℂ) * d.th (B.ct x + v.2) * a
end Dict

theorem Dict.tx_wQ (d : Dict N B) {k t : ℕ} (hk : k = 2 * t + 1) {la : B.La} {p : N.QT k} (hp : d.Rep k la p) :
    (N.wQ p : ℂ) * d.fr ((k : ℂ)⁻¹ • B.P0 la).2 ^ k * B.ah la.l (B.ct la.y) =
      B.psi la.y * Complex.exp (lin B la (B.P0 la) / k) ^ t := by
  obtain ⟨hy, hb, hs⟩ := hp
  have k0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  replace hs := hs la.y
  have hx : (k : ℂ) • ((k : ℂ)⁻¹ • B.P0 la).2 = B.ct la.y + la.l := by
    rw [Prod.smul_snd, smul_inv_smul₀ k0, AnArc.degeneratingTori_basePeriodMap_snd]
  have hE : Complex.exp (lin B la (B.P0 la) / k) * eTwoPi (((k : ℂ)⁻¹ • B.P0 la).1 la.y) =
      Complex.exp (Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la.l) := by
    rw [eTwoPi, ← Complex.exp_add, lin, Prod.smul_snd, B.H_smul_left, Prod.smul_fst, AddMonoidHom.smul_apply,
      smul_eq_mul]
    congr 1
    ring
  generalize ((k : ℂ)⁻¹ • B.P0 la).2 = x at *
  generalize Complex.exp (lin B la (B.P0 la) / k) = E at *
  generalize eTwoPi (((k : ℂ)⁻¹ • B.P0 la).1 la.y) = e at *
  have f1 := d.ab.2.2.2.2.1 la.l (B.ct la.y)
  have f2 := d.ab.2.2.2.2.1 la.l (B.ct la.y + x)
  rw [B.ah_add, ← hE, add_right_comm] at f2
  have a := congrArg Units.val (d.tx_mulq x k)
  have b := congrArg Units.val (d.tx_cubN_div x k)
  have c := congrArg Units.val (d.ψ_eq la.y)
  rw [hx] at a b
  have ht : (k - 1) / 2 = t := by omega
  rw [NumD.wQ, NumB.wS, hy, hb, ht, mul_div_assoc (p.1.2.s _)]
  generalize cubN N.θ k 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ k = D at *
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val] at a b c ⊢
  have hD : (p.1.2.s (d.eX la.y) : ℂ) * D * (d.fr x ^ (2 * k) * E) = 1 := by
    refine mul_right_cancel₀ (b := (d.fr (B.ct la.y) : ℂ) * d.fr x * e) ?_ ?_
    · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) ?_
      rintro rfl
      exact Complex.exp_ne_zero _ (hE.symm.trans (mul_zero _))
    · linear_combination hs - (p.1.2.s (d.eX la.y) : ℂ) * f2 +
        (p.1.2.s (d.eX la.y) : ℂ) * B.ah la.l (B.ct la.y) * E * e * b +
        (p.1.2.s (d.eX la.y) : ℂ) * D * (d.fr x ^ (2 * k) * E) * d.fr x * e * f1
  have hD' := (mul_eq_one_iff_inv_eq₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))).1 hD
  rw [div_eq_mul_inv, ← inv_pow, hD', mul_pow, ← pow_mul, ← c, f1, ← a,
    show k ^ 2 = 2 * k * t + k by rw [sq]; nth_rw 2 [hk]; ring, pow_add]
  ring

theorem IsPrim.tx_sign {w₀ : O} (h : IsPrim B w₀) (la : B.La) :
    (B.psi la.y : ℂ) =
      (-1) ^ B.EF la (w₀ • la) * Complex.exp (-(lin B la (B.P0 la) / 2)) * B.ah la.l (B.ct la.y) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hy : la.y = w₀ • la.y + star w₀ • la.y := by rw [← add_smul, h1, one_smul]
  have hT : B.T la.y la.y = 2 * B.T la.y (w₀ • la.y) := by
    have : B.T la.y la.y = B.T la.y (w₀ • la.y + star w₀ • la.y) := by rw [← hy]
    rw [this, map_add, ← B.T_adj, B.T_symm (w₀ • la.y), two_mul]
  have hn : la.n la.y = la.n (w₀ • la.y) + la.n (star w₀ • la.y) := by rw [← map_add, ← hy]
  have hm : ∀ z : ℤ, (-1 : ℂ) ^ z = Complex.exp (z * (Real.pi * Complex.I)) := fun z => by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [h3, AnArc.ah, h2, hm, hm, eTwoPi, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(la.n (star w₀ • la.y) + B.Ef la.l (B.FLam w₀ la.l)), ?_⟩
  simp only [lin, AnArc.EF_apply, AnArc.La.smul_y, AnArc.La.smul_n_apply, AnArc.La.smul_l, AnArc.degeneratingTori_basePeriodMap_fst_apply,
    AnArc.degeneratingTori_basePeriodMap_snd, AnArc.H_add_left, hT, hn]
  have := Complex.I_ne_zero
  push_cast
  field_simp
  ring

theorem txSt_of_ptSt (h : PtSt) : TxSt := by
  intro O _ _ N B d w₀ hw k β hβ m hm ho w u hu la p hp x
  obtain ⟨t, ht⟩ := ho.pow (n := 2)
  have m0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ho.pos.ne'
  have hQ := d.tx_wQ ht hp
  have hv := d.tx_vt (d.tx_isPt_pow h hp.2 m) x
  have hq := congrArg Units.val (d.tx_mulq (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2 m)
  have hmm : (m : ℂ) • ((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la = (m : ℂ)⁻¹ • B.P0 la := by
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  rw [← Prod.smul_snd (m : ℂ), hmm] at hq
  rw [hmm] at hv
  rw [hw.tx_sign, mul_right_comm _ (B.ah _ _), mul_left_inj' (B.ah_ne_zero _ _), mul_assoc, ← Complex.exp_nat_mul,
    ← Complex.exp_add] at hQ
  have hterm : B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.Pw w la) =
      B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * eTwoPi ((m : ℂ)⁻¹ * (w * B.be la.y x)) := by
    have e1 : ((m : ℂ)⁻¹ • B.Pw w la).1 (0 + 1 • x) =
        ((m : ℂ)⁻¹ • B.P0 la).1 (0 + 1 • x) + (m : ℂ)⁻¹ * (w * B.be la.y x) := by
      simp only [zero_add, one_smul, Prod.smul_fst, AddMonoidHom.smul_apply, smul_eq_mul, AnArc.Pw_fst_apply,
        AnArc.degeneratingTori_basePeriodMap_fst_apply]
      ring
    have e2 : ((m : ℂ)⁻¹ • B.Pw w la).2 = ((m : ℂ)⁻¹ • B.P0 la).2 := by
      rw [Prod.smul_snd, Prod.smul_snd, AnArc.Pw_snd, AnArc.degeneratingTori_basePeriodMap_snd]
    rw [AnArc.term, AnArc.term, e1, e2, AnArc.e_add]
    ring
  have hlin : lin B la (B.Pw w la) = lin B la (B.P0 la) - 2 * Real.pi * Complex.I * (w * B.be la.y la.y) := by
    simp only [lin, AnArc.Pw_fst_apply, AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.Pw_snd, AnArc.degeneratingTori_basePeriodMap_snd]
    ring
  obtain ⟨c, hc⟩ : (2 * (m : ℤ) ^ 2) ∣ β.be (d.eX la.y + m • d.eX x) (d.eX la.y + m • d.eX x) :=
    (mul_dvd_mul_left 2 (by exact_mod_cast hm)).trans (β.dvd _ _)
  have hc' : 2 * (m : ℤ) ^ 2 * c = B.be la.y la.y + 2 * m * B.be la.y x + m ^ 2 * (2 * B.q x) := by
    rw [← hc, ← map_nsmul, ← map_add, ← hβ, B.two_mul_q]
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, B.be_symm x la.y]
    ring
  replace hc' : (c : ℂ) = (B.be la.y la.y + 2 * m * B.be la.y x + m ^ 2 * (2 * B.q x)) / (2 * m ^ 2) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero (pow_ne_zero _ m0)), mul_comm]
    exact_mod_cast hc'
  have ht' : (t : ℂ) = (m ^ 2 - 1) / 2 := by
    have : (m : ℂ) ^ 2 = 2 * t + 1 := by exact_mod_cast ht
    rw [this]; ring
  have key : eTwoPi (w * c) * Complex.exp (-(lin B la (B.P0 la) / 2) + t * (lin B la (B.P0 la) / (m ^ 2 : ℕ))) =
      Complex.exp (-(lin B la (B.Pw w la) / (2 * (m : ℂ) ^ 2))) * eTwoPi ((m : ℂ)⁻¹ * (w * B.be la.y x)) *
        eTwoPi (w * B.exponent 1 0 x) := by
    simp only [eTwoPi, ← Complex.exp_add, hlin, hc', ht', AnArc.exponent, map_zero]
    congr 1
    push_cast
    field_simp
    ring
  have m0' : (2 * (m : ℤ) ^ 2) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ (Int.natCast_ne_zero.2 ho.pos.ne'))
  rw [N.twist_txT β u m hm ho, hp.1, hc, Int.mul_ediv_cancel_left _ m0', Units.val_zpow_eq_zpow_val, hu,
    ← AnArc.e_mul_intCast, NumD.txT, hv, hterm, hp.2.1, ← hq, Units.val_div_eq_div_val, Units.val_mul,
    Units.val_pow_eq_pow_val]
  have hmq := (mulq N.θ N.σ m (d.ex (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2)).ne_zero
  linear_combination (eTwoPi (w * c) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la)) * hQ +
    (-1) ^ B.EF la (w₀ • la) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * key +
    eTwoPi (w * c) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * N.wQ p *
      (d.fr (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2 : ℂ) ^ m ^ 2 * inv_mul_cancel₀ hmq

end GlobalTheory.Ex.Arch
end
end

