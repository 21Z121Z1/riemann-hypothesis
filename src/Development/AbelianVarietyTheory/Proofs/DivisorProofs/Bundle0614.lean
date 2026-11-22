import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0600
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordsOfGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.TateGlue

theorem bezout {N P : ℕ} (h : N.Coprime P) : (N : ℤ) * N.gcdA P + (P : ℤ) * N.gcdB P = 1 := by
  rw [← Nat.gcd_eq_gcd_ab, h.gcd_eq_one]; rfl

theorem eq_of_pow_eq {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a b : G}
    (h1 : a ^ N = b ^ N) (h2 : a ^ P = b ^ P) : a = b := by
  have key : ∀ g : G, g = (g ^ N) ^ N.gcdA P * (g ^ P) ^ N.gcdB P := fun g => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, bezout h, zpow_one]
  rw [key a, key b, h1, h2, ← h1, ← h2]

def glue {G : Type} [CommGroup G] (N P : ℕ) (a b : G) : G := a ^ N.gcdA P * b ^ N.gcdB P

theorem zpow_left {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a : G} (ha : a ^ P = 1) :
    a ^ ((N : ℤ) * N.gcdA P) = a := by
  have : a ^ ((N : ℤ) * N.gcdA P + (P : ℤ) * N.gcdB P) = a := by rw [bezout h, zpow_one]
  rwa [zpow_add, zpow_mul a (P : ℤ), zpow_natCast, ha, one_zpow, _root_.mul_one] at this

theorem zpow_right {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {b : G} (hb : b ^ N = 1) :
    b ^ ((P : ℤ) * N.gcdB P) = b := by
  have : b ^ ((N : ℤ) * N.gcdA P + (P : ℤ) * N.gcdB P) = b := by rw [bezout h, zpow_one]
  rwa [zpow_add, zpow_mul b (N : ℤ), zpow_natCast, hb, one_zpow, _root_.one_mul] at this

theorem zpow_pow_comm {G : Type} [CommGroup G] (a : G) (z : ℤ) (n : ℕ) : (a ^ z) ^ n = (a ^ n) ^ z := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem glue_pow_left {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a b : G} (ha : a ^ P = 1)
    (hb : b ^ N = 1) : glue N P a b ^ N = a := by
  rw [glue, mul_pow, zpow_pow_comm b, hb, one_zpow, _root_.mul_one, zpow_pow_comm, ← zpow_natCast, ← zpow_mul,
    zpow_left h ha]

theorem glue_pow_right {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a b : G} (ha : a ^ P = 1)
    (hb : b ^ N = 1) : glue N P a b ^ P = b := by
  rw [glue, mul_pow, zpow_pow_comm a, ha, one_zpow, _root_.one_mul, zpow_pow_comm, ← zpow_natCast, ← zpow_mul,
    zpow_right h hb]

theorem glue_mul {G : Type} [CommGroup G] (N P : ℕ) (a b a' b' : G) :
    glue N P (a * a') (b * b') = glue N P a b * glue N P a' b' := by
  simp only [glue, mul_zpow]; exact mul_mul_mul_comm _ _ _ _

theorem map_glue {G : Type} [CommGroup G] (N P : ℕ) (f : G → G) (hf : ∀ a b, f (a * b) = f a * f b) (a b : G) :
    f (glue N P a b) = glue N P (f a) (f b) := by
  let φ : G →* G := MonoidHom.mk' f hf
  change φ (glue N P a b) = glue N P (φ a) (φ b)
  simp only [glue, map_mul, map_zpow]

theorem hom_zsmul {A G : Type} [AddCommGroup A] [CommGroup G] (f : A → G) (hf : ∀ x y, f (x + y) = f x * f y)
    (z : ℤ) (x : A) : f (z • x) = f x ^ z := by
  let φ : Multiplicative A →* G := MonoidHom.mk' (fun x => f x.toAdd) (fun a b => hf _ _)
  change φ (Multiplicative.ofAdd (z • x)) = φ (Multiplicative.ofAdd x) ^ z
  rw [ofAdd_zsmul, map_zpow]

theorem tower_add {G : Type} [CommGroup G] (p : ℕ) (f : ℕ → G) (hf : ∀ r, f (r + 1) ^ p = f r) (r s : ℕ) :
    f (r + s) ^ (p ^ s) = f r := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ', pow_mul, ← add_assoc, hf, ih]

def sys {G : Type} [CommGroup G] (p : ℕ) (f g : ℕ → G) (n : ℕ) : G :=
  glue (n / p ^ n.factorization p) (p ^ n.factorization p) (f (n.factorization p)) (g (n / p ^ n.factorization p))

theorem cop {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (n / p ^ n.factorization p).Coprime (p ^ n.factorization p) :=
  ((Nat.coprime_ordCompl hp hn.ne').pow_left _).symm

theorem sys_left {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) {n : ℕ} (hn : 0 < n) :
    sys p f g n ^ (n / p ^ n.factorization p) = f (n.factorization p) :=
  glue_pow_left (cop hp hn) (hf _) (hg _ (Nat.ordCompl_pos p hn.ne') (Nat.coprime_ordCompl hp hn.ne').symm)

theorem sys_right {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) {n : ℕ} (hn : 0 < n) :
    sys p f g n ^ (p ^ n.factorization p) = g (n / p ^ n.factorization p) :=
  glue_pow_right (cop hp hn) (hf _) (hg _ (Nat.ordCompl_pos p hn.ne') (Nat.coprime_ordCompl hp hn.ne').symm)

theorem sys_pow_self {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) {n : ℕ} (hn : 0 < n) : sys p f g n ^ n = 1 := by
  have h := congrArg (· ^ (p ^ n.factorization p)) (sys_left hp hf hg hn)
  rwa [hf, ← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self] at h

theorem sys_tower {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) (hf' : ∀ r, f (r + 1) ^ p = f r)
    (hg' : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → g (n * m) ^ m = g n) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    sys p f g (n * m) ^ m = sys p f g n := by
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have hl := sys_left hp hf hg hnm
  have hr := sys_right hp hf hg hnm
  have hfac : (n * m).factorization p = n.factorization p + m.factorization p := by
    rw [Nat.factorization_mul hn.ne' hm.ne']; rfl
  have hc := Nat.ordCompl_mul n m p
  have hcp := (Nat.coprime_ordCompl hp hnm.ne').symm
  rw [hc] at hl hr hcp
  rw [hfac] at hl hr
  have hm' := Nat.ordProj_mul_ordCompl_eq_self m p
  have hnp := Nat.ordCompl_pos p hn.ne'
  have hmp := Nat.ordCompl_pos p hm.ne'
  refine eq_of_pow_eq (cop hp hn) ?_ ?_
  · rw [sys_left hp hf hg hn, ← tower_add p f hf' _ (m.factorization p), ← hl, ← pow_mul, ← pow_mul]
    congr 1
    generalize n / p ^ n.factorization p = a at *
    generalize m / p ^ m.factorization p = b at *
    generalize p ^ m.factorization p = c at *
    rw [← hm']; ring
  · rw [sys_right hp hf hg hn, ← hg' _ _ hnp hmp hcp, ← hr, ← pow_mul, ← pow_mul, pow_add]
    congr 1
    generalize m / p ^ m.factorization p = b at *
    generalize p ^ m.factorization p = c at *
    rw [← hm']; ring

theorem exists_gTateIso : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (E : ℕ → Q → Q → kˣ → Prop), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → ∃ c, E n a b c) → (∀ n, 0 < n → ∀ (a b : Q) (c c' : kˣ), E n a b c → E n a b c' → c = c') → (∀ n m, 0 < n → 0 < m → ∀ (a b : Q) (c : kˣ), a ^ (n * m) = 1 → b ^ (n * m) = 1 → E (n * m) a b c → E n (a ^ m) (b ^ m) (c ^ m)) → ∀ (I : TateIsoO D k Q act E) (ζ : ℕ → kˣ) (ev : ℕ → D.La → Q), (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) → (∀ r, ζ (r + 1) ^ p = ζ r) → (∀ r, (∀ x y, ev r (x + y) = ev r x * ev r y) ∧ (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) → (∀ r x, ev (r + 1) x ^ p = ev r x) → (∀ r x y, E (p ^ r) (ev r x) (ev r y) (ζ r ^ (2 * D.EF x y))) → ∃ J : GTateIso D.toG k Q act E, ∀ n, 0 < n → n.Coprime p → ∀ y : D.La, J.ev n y = I.ev n y := by
  intro p hpF D k _ Q _ act E hact hex huniq hlev I ζ ev hζ hζ' hev hev' hE
  have hp : p.Prime := hpF.out
  have ζ1 : ∀ r, ζ r ^ (p ^ r) = 1 := fun r => (hζ r).pow_eq_one
  have ζ2 : ∀ n, 0 < n → n.Coprime p → I.ζ n ^ n = 1 := fun n hn hc => (I.ζ_prim n hn hc).pow_eq_one
  have e1 : ∀ (y : D.La) r, ev r y ^ (p ^ r) = 1 := fun y r => ((hev r).2.2.2 _).2 ⟨y, rfl⟩
  have e2 : ∀ (y : D.La) n, 0 < n → n.Coprime p → I.ev n y ^ n = 1 := fun y n hn hc =>
    (I.onto n hn hc _).2 ⟨y, rfl⟩
  let Z : ℕ → kˣ := sys p ζ I.ζ
  let V : ℕ → D.La → Q := fun n y => sys p (fun r => ev r y) (fun n => I.ev n y) n
  have Zl : ∀ n, 0 < n → Z n ^ (n / p ^ n.factorization p) = ζ (n.factorization p) := fun n hn =>
    sys_left hp ζ1 ζ2 hn
  have Zr : ∀ n, 0 < n → Z n ^ (p ^ n.factorization p) = I.ζ (n / p ^ n.factorization p) := fun n hn =>
    sys_right hp ζ1 ζ2 hn
  have Vl : ∀ n, 0 < n → ∀ y, V n y ^ (n / p ^ n.factorization p) = ev (n.factorization p) y := fun n hn y =>
    sys_left hp (e1 y) (e2 y) hn
  have Vr : ∀ n, 0 < n → ∀ y, V n y ^ (p ^ n.factorization p) = I.ev (n / p ^ n.factorization p) y :=
    fun n hn y => sys_right hp (e1 y) (e2 y) hn
  have V1 : ∀ n, 0 < n → ∀ y, V n y ^ n = 1 := fun n hn y => sys_pow_self hp (e1 y) (e2 y) hn
  have hker : ∀ n, 0 < n → ∀ x : D.La, V n x = 1 ↔ ∃ y, x = n • y := by
    intro n hn x
    have hl := Vl n hn x
    have hr := Vr n hn x
    have hc := cop hp hn
    have hN := Nat.ordCompl_pos p hn.ne'
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have hn' := Nat.ordProj_mul_ordCompl_eq_self n p
    have k1 := (hev (n.factorization p)).2.2.1 x
    have k2 := I.ker _ hN hNp x
    generalize V n x = q at *
    generalize n / p ^ n.factorization p = N at *
    generalize ev (n.factorization p) x = a at *
    generalize p ^ n.factorization p = P at *
    constructor
    · rintro rfl
      obtain ⟨y1, h1⟩ := k1.1 (by rw [← hl, one_pow])
      obtain ⟨y2, h2⟩ := k2.1 (by rw [← hr, one_pow])
      refine ⟨N.gcdA P • y1 + N.gcdB P • y2, ?_⟩
      have hx : x = ((N : ℤ) * N.gcdA P) • x + ((P : ℤ) * N.gcdB P) • x := by
        rw [← add_smul, bezout hc, one_smul]
      rw [hx, ← hn']
      nth_rewrite 1 [h1]
      rw [h2]
      simp only [← natCast_zsmul, smul_add, smul_smul]
      congr 2 <;> push_cast <;> ring
    · rintro ⟨y, hy⟩
      refine eq_of_pow_eq hc ?_ ?_
      · rw [hl, one_pow]; exact k1.2 ⟨N • y, by rw [hy, ← hn', mul_smul]⟩
      · rw [hr, one_pow]; exact k2.2 ⟨P • y, by rw [hy, ← hn', mul_comm, mul_smul]⟩
  have honto : ∀ n, 0 < n → ∀ q : Q, q ^ n = 1 ↔ ∃ x, V n x = q := by
    intro n hn q
    refine ⟨fun hq => ?_, fun ⟨x, hx⟩ => hx ▸ V1 n hn x⟩
    have hl := Vl n hn
    have hr := Vr n hn
    have hc := cop hp hn
    have hN := Nat.ordCompl_pos p hn.ne'
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have hn' := Nat.ordProj_mul_ordCompl_eq_self n p
    have a1 := (hev (n.factorization p)).1
    have o1 := (hev (n.factorization p)).2.2.2
    have a2 := I.add (n / p ^ n.factorization p)
    have o2 := I.onto _ hN hNp
    generalize n / p ^ n.factorization p = N at *
    generalize ev (n.factorization p) = f at *
    generalize p ^ n.factorization p = P at *
    obtain ⟨x1, h1⟩ := (o1 (q ^ N)).1 (by rw [← pow_mul, mul_comm, hn', hq])
    obtain ⟨x2, h2⟩ := (o2 (q ^ P)).1 (by rw [← pow_mul, hn', hq])
    refine ⟨((N : ℤ) * N.gcdA P) • x1 + ((P : ℤ) * N.gcdB P) • x2, eq_of_pow_eq hc ?_ ?_⟩
    · rw [hl, a1, hom_zsmul f a1, hom_zsmul f a1, zpow_left hc ((o1 _).2 ⟨x1, rfl⟩), zpow_mul, zpow_natCast,
        (o1 _).2 ⟨x2, rfl⟩, one_zpow, _root_.mul_one, h1]
    · rw [hr, a2, hom_zsmul _ a2, hom_zsmul _ a2, zpow_right hc ((o2 _).2 ⟨x2, rfl⟩), zpow_mul, zpow_natCast,
        (o2 _).2 ⟨x1, rfl⟩, one_zpow, _root_.one_mul, h2]
  have hisom : ∀ n, 0 < n → ∀ x y : D.La, E n (V n x) (V n y) (Z n ^ (2 * D.EF x y)) := by
    intro n hn x y
    obtain ⟨c, hc0⟩ := hex n hn _ _ (V1 n hn x) (V1 n hn y)
    have hc := cop hp hn
    have hN := Nat.ordCompl_pos p hn.ne'
    have hP : 0 < p ^ n.factorization p := pow_pos hp.pos _
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have hn' := Nat.ordProj_mul_ordCompl_eq_self n p
    have hn'' := (mul_comm _ _).trans hn'
    have l1 := hlev _ _ hP hN (V n x) (V n y) c (by rw [hn']; exact V1 n hn x) (by rw [hn']; exact V1 n hn y)
      (by rw [hn']; exact hc0)
    have l2 := hlev _ _ hN hP (V n x) (V n y) c (by rw [hn'']; exact V1 n hn x) (by rw [hn'']; exact V1 n hn y)
      (by rw [hn'']; exact hc0)
    rw [Vl n hn, Vl n hn] at l1
    rw [Vr n hn, Vr n hn] at l2
    have c1 := huniq _ hP _ _ _ _ l1 (hE _ x y)
    have c2 := huniq _ hN _ _ _ _ l2 (I.isom _ hN hNp x y)
    have : c = Z n ^ (2 * D.EF x y) := by
      refine eq_of_pow_eq hc ?_ ?_
      · rw [c1, zpow_pow_comm, Zl n hn]
      · rw [c2, zpow_pow_comm, Zr n hn]
    exact this ▸ hc0
  refine ⟨{ ζ := Z
            ζ_prim := fun n hn => ⟨sys_pow_self hp ζ1 ζ2 hn, fun l hl => ?_⟩
            ζ_pow := fun n m hn hm => sys_tower hp ζ1 ζ2 hζ' I.ζ_pow hn hm
            ev := V
            add := fun n (x y : D.La) => ?_
            lin := fun n (b : D.O) (x : D.La) => ?_
            ker := hker
            onto := honto
            tower := fun n m hn hm x => sys_tower hp (e1 x) (e2 x) (fun r => hev' r x)
              (fun n m hn hm hc => I.tower n m hn hm hc x) hn hm
            isom := hisom }, fun n hn hc y => ?_⟩
  · have hN := Nat.ordCompl_pos p hn.ne'
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have d1 := (hζ (n.factorization p)).dvd_of_pow_eq_one l (by
      rw [← Zl n hn, ← pow_mul, mul_comm, pow_mul, hl, one_pow])
    have d2 := (I.ζ_prim _ hN hNp).dvd_of_pow_eq_one l (by
      rw [← Zr n hn, ← pow_mul, mul_comm, pow_mul, hl, one_pow])
    have := (cop hp hn).symm.mul_dvd_of_dvd_of_dvd d1 d2
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at this
  · change glue _ _ (ev _ (x + y)) (I.ev _ (x + y)) = glue _ _ (ev _ x) (I.ev _ x) * glue _ _ (ev _ y) (I.ev _ y)
    rw [(hev _).1, I.add, glue_mul]
  · change glue _ _ (ev _ (b • x)) (I.ev _ (b • x)) = act b (glue _ _ (ev _ x) (I.ev _ x))
    rw [(hev _).2.1, I.lin, map_glue _ _ (act b) (hact b)]
  · have h0 : n.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hc.symm)
    have := Vr n hn y
    rw [h0, pow_zero, pow_one, Nat.div_one] at this
    exact this

end GlobalTheory.TateGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullSymplecticLevelStructureOfTateIso
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E _

theorem exists_twist (l : Level H) (L : ℤ) (hL : (l.A : ℤ) ∣ L - 1) :
    ∃ u w c : 𝓞 E, c ∈ l.Mb ∧ u = 1 + (l.A : 𝓞 E) * c ∧
      H.bar u * u = (L : 𝓞 E) + (l.M' : 𝓞 E) * w := by
  obtain ⟨q, hq⟩ := hL
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.1 h1
  have hbn : H.bar n ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ hn
  have hbm : H.bar m ∈ l.Mb := by
    obtain ⟨m0, hm0, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 hm
    simpa [bar_bar] using hm0
  have hbar1 : H.bar n + H.bar m = 1 := by rw [← map_add, hnm, map_one]
  have hxN : H.bar n - m ∈ l.Mb := by
    have e : H.bar n - m = n - H.bar m := by linear_combination hbar1 - hnm
    rw [e]; exact sub_mem hn hbm
  have hxN' : H.bar n - m ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := sub_mem hbn hm
  have hx : H.bar n - m ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have e : H.bar n - m = n * (H.bar n - m) + (H.bar n - m) * m := by
      linear_combination -(H.bar n - m) * hnm
    rw [e]
    exact add_mem (Ideal.mul_mem_mul hn hxN') (Ideal.mul_mem_mul hxN hm)
  have hnn : n * H.bar n ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_mem_mul hn hbn
  rw [l.prod] at hx hnn
  obtain ⟨y1, hy1⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨y2, hy2⟩ := Ideal.mem_span_singleton'.1 hnn
  have hg : ((l.M : ℕ) : 𝓞 E) * l.A = (l.M' : 𝓞 E) * (Nat.gcd l.M l.A : ℕ) := by
    have := Nat.gcd_mul_lcm l.M l.A
    unfold Level.M'
    exact_mod_cast (by rw [mul_comm (Nat.lcm _ _), this] : l.M * l.A = Nat.lcm l.M l.A * Nat.gcd l.M l.A)
  have hq' : (L : 𝓞 E) - 1 = (l.A : 𝓞 E) * q := by exact_mod_cast hq
  refine ⟨1 + ((L : 𝓞 E) - 1) * n, (Nat.gcd l.M l.A : 𝓞 E) * q * (y1 + ((L : 𝓞 E) - 1) * y2),
    (q : 𝓞 E) * n, Ideal.mul_mem_left _ _ hn, ?_, ?_⟩
  · rw [hq']; ring
  · have hb : H.bar (1 + ((L : 𝓞 E) - 1) * n) = 1 + ((L : 𝓞 E) - 1) * H.bar n := by
      simp [map_add, map_mul, map_sub, map_one, map_intCast]
    rw [hb]
    linear_combination ((L : 𝓞 E) - 1) * hnm - ((L : 𝓞 E) - 1) * hy1 - ((L : 𝓞 E) - 1) ^ 2 * hy2
      + (l.M : 𝓞 E) * (y1 + ((L : 𝓞 E) - 1) * y2) * hq' + (q : 𝓞 E) * (y1 + ((L : 𝓞 E) - 1) * y2) * hg

theorem smul_mem_M (l : Level H) {D : Datum H} {c : 𝓞 E} (hc : c ∈ l.Mb) {a : D.La}
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ y : D.La, c • a = l.M • y := by
  refine Submodule.smul_induction_on ha ?_ ?_
  · intro r hr t _
    have : c * r ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := l.prod ▸ Ideal.mul_mem_mul hc hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨s • t, by rw [← mul_smul, ← hs, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]⟩
  · rintro x y ⟨x', hx'⟩ ⟨y', hy'⟩
    exact ⟨x' + y', by rw [smul_add, hx', hy', smul_add]⟩

theorem exists_sympLevel_of_tate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    {z : kˣ}, IsPrimitiveRoot z l.M' → z ^ (l.M' / l.A) = I.ζ l.A →
    ∃ ev : D.La → Q, IsSympLevel D act e l.M' z ev ∧ Induces l (I.ev l.A) (I.ev l.M) ev := by
  intro E _ _ _ H D l k _ Q _ act e I z hz hzA
  have hM' := M'_pos l
  haveI : NeZero l.M' := ⟨hM'.ne'⟩
  have hζ := I.ζ_prim l.M' hM'
  obtain ⟨L, -, hcop, hL⟩ := (hζ.isPrimitiveRoot_iff').1 hz
  obtain ⟨d, hd⟩ := A_dvd_M' l
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
  have hdiv : l.M' / l.A = d := by rw [hd, Nat.mul_div_cancel_left _ l.A_pos]
  have hζA : I.ζ l.M' ^ d = I.ζ l.A := by
    have := I.ζ_pow l.A d l.A_pos hd0; rwa [← hd] at this
  have hAL : (l.A : ℤ) ∣ (L : ℤ) - 1 := by
    have e1 : I.ζ l.M' ^ (L * d) = I.ζ l.M' ^ d := by
      rw [pow_mul, hL, ← hdiv, hzA, hdiv, hζA]
    have h2 : I.ζ l.M' ^ (((L : ℤ) - 1) * d) = 1 := by
      rw [sub_mul, one_mul, zpow_sub, show ((L : ℤ) * d) = ((L * d : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, zpow_natCast, e1, mul_inv_cancel]
    have h3 := (hζ.zpow_eq_one_iff_dvd _).1 h2
    rw [hd] at h3; push_cast at h3
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hd0.ne')).1 h3
  obtain ⟨a', b', hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨u, w, c, hc, hu, hw⟩ := exists_twist l L hAL
  set v : 𝓞 E := (a' : 𝓞 E) * H.bar u with hv
  have hvu : v * u = 1 + (l.M' : 𝓞 E) * ((a' : 𝓞 E) * w - b') := by
    have hab' : (a' : 𝓞 E) * (L : ℤ) + (b' : 𝓞 E) * ((l.M' : ℕ) : ℤ) = 1 := by exact_mod_cast hab
    push_cast at hab'
    rw [hv, mul_assoc, hw]
    push_cast
    linear_combination hab'
  have key : ∀ a : D.La, v • u • a = a + l.M' • (((a' : 𝓞 E) * w - b') • a) := by
    intro a; rw [← mul_smul, hvu, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul]
  have key' : ∀ a : D.La, u • v • a = a + l.M' • (((a' : 𝓞 E) * w - b') • a) := by
    intro a; rw [smul_comm]; exact key a
  have hcong : ∀ a b : D.La, I.ev l.M' (a + l.M' • b) = I.ev l.M' a := by
    intro a b; rw [I.add, (I.ker _ hM' _).2 ⟨b, rfl⟩, mul_one]
  have hEF : ∀ a b : D.La, D.EF (u • a) (u • b) = L * D.EF a b + l.M' * D.EF a (w • b) := by
    intro a b
    rw [D.adj, ← mul_smul, hw, add_smul, mul_smul, Nat.cast_smul_eq_nsmul]
    simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul, map_add, map_zsmul, map_nsmul, smul_eq_mul, nsmul_eq_mul]
  refine ⟨fun a => I.ev l.M' (u • a), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a b; simp only [smul_add, I.add]
  · intro c a; try simp only
    rw [smul_comm, I.lin]
  · intro a; try simp only
    rw [I.ker _ hM']
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨v • b - ((a' : 𝓞 E) * w - b') • a, ?_⟩
      have h := congrArg (v • ·) hb
      change v • u • a = v • (l.M' • b) at h
      rw [key, smul_comm v l.M' b] at h
      rw [smul_sub, ← h]; abel
    · rintro ⟨b, rfl⟩; exact ⟨u • b, smul_comm _ _ _⟩
  · intro x; rw [I.onto _ hM']
    constructor
    · rintro ⟨a0, rfl⟩; exact ⟨v • a0, by simp only [key', hcong]⟩
    · rintro ⟨a, rfl⟩; exact ⟨u • a, rfl⟩
  · intro a b
    have h := I.isom _ hM' (u • a) (u • b)
    convert h using 1
    rw [hEF, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hL, hζ.pow_eq_one, one_zpow, mul_one]
  · intro a
    have htow : I.ev l.M' (u • a) ^ d = I.ev l.A (u • a) := by
      have := I.tower l.A d l.A_pos hd0 (u • a); rwa [← hd] at this
    try simp only
    rw [hdiv, htow, hu, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul, I.add,
      (I.ker _ l.A_pos _).2 ⟨_, rfl⟩, mul_one]
  · intro a ha
    obtain ⟨dM, hdM⟩ := M_dvd_M' l
    have hMp : 0 < l.M := by have := l.three_le; omega
    have hdM0 : 0 < dM := Nat.pos_of_ne_zero (by rintro rfl; simp at hdM; omega)
    have hdivM : l.M' / l.M = dM := by rw [hdM, Nat.mul_div_cancel_left _ hMp]
    have htow : I.ev l.M' (u • a) ^ dM = I.ev l.M (u • a) := by
      have := I.tower l.M dM hMp hdM0 (u • a); rwa [← hdM] at this
    obtain ⟨y, hy⟩ := smul_mem_M l hc ha
    try simp only
    rw [hdivM, htow, hu, add_smul, one_smul, mul_smul, hy, Nat.cast_smul_eq_nsmul, smul_comm, I.add,
      (I.ker _ hMp _).2 ⟨_, rfl⟩, mul_one]

end GlobalTheory.FullLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackPowObjProjections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin

theorem exists_powPr_of_isGrpPullback : ∀ (S T : Scheme.{0}) (t : T ⟶ S) (A : Over S) [GrpObj A] (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left) (B' : Over T) [GrpObj B'] (r : ℕ) (φB : B'.left ⟶ (Out.powObj A r).left), IsGrpPullback A' A t φ' → IsGrpPullback B' (Out.powObj A r) t φB → ∃ pr' : Fin r → (B' ⟶ A'), (∀ u, IsMonHom (pr' u)) ∧ (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) ∧ ∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u := by
  intro S T t A _ A' _ φ' B' _ r φB hA hB
  have wu : ∀ u : Fin r, (φB ≫ (Out.powPr A u).left) ≫ A.hom = B'.hom ≫ t := fun u => by
    rw [Category.assoc, Over.w (Out.powPr A u)]; exact hB.1.w
  let pr' : Fin r → (B' ⟶ A') := fun u => Over.homMk (hA.1.lift _ _ (wu u)) (hA.1.lift_snd _ _ _)
  have hpr : ∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left := fun u => hA.1.lift_fst _ _ _
  have inj : ∀ {X : Over T} (a b : X ⟶ A'), a.left ≫ φ' = b.left ≫ φ' → a = b := fun a b h =>
    Over.OverMorphism.ext (hA.1.hom_ext h ((Over.w a).trans (Over.w b).symm))
  have key : ∀ {X : Over T} (z : X ⟶ B') (u : Fin r),
      pushPt hA.1.w (z ≫ pr' u) = pushPt hB.1.w z ≫ Out.powPr A u := fun z u =>
    Over.OverMorphism.ext (by
      show (z.left ≫ (pr' u).left) ≫ φ' = (z.left ≫ φB) ≫ (Out.powPr A u).left
      rw [Category.assoc, hpr, Category.assoc])
  refine ⟨pr', fun u => ?_, hpr, fun X y => ?_⟩
  · refine GlobalTheory.Serre.isMonHom_of_mul_comp _ fun X x y => inj _ _ ?_
    have hm : pushPt hB.1.w (x * y) = pushPt hB.1.w x * pushPt hB.1.w y := map_mul (pushHom hB X) x y
    calc ((x * y) ≫ pr' u).left ≫ φ' = (pushPt hA.1.w ((x * y) ≫ pr' u)).left := rfl
      _ = ((pushPt hB.1.w x * pushPt hB.1.w y) ≫ Out.powPr A u).left := by rw [key, hm]
      _ = ((pushPt hB.1.w x ≫ Out.powPr A u) * (pushPt hB.1.w y ≫ Out.powPr A u)).left := by
        rw [MonObj.mul_comp]
      _ = (pushPt hA.1.w (x ≫ pr' u) * pushPt hA.1.w (y ≫ pr' u)).left := by rw [key, key]
      _ = ((x ≫ pr' u) * (y ≫ pr' u)).left ≫ φ' := hA.2 X _ _ _ _ rfl rfl
  · let z : Over.mk (X.hom ≫ t) ⟶ Out.powObj A r :=
      (Out.powIsLimit A r).lift (Fan.mk (Over.mk (X.hom ≫ t)) fun u => pushPt hA.1.w (y u))
    have hz : ∀ u, z ≫ Out.powPr A u = pushPt hA.1.w (y u) := fun u =>
      (Out.powIsLimit A r).fac (Fan.mk (Over.mk (X.hom ≫ t)) fun u => pushPt hA.1.w (y u)) ⟨u⟩
    have hz0 : z.left ≫ (Out.powObj A r).hom = X.hom ≫ t := Over.w z
    let x : X ⟶ B' := Over.homMk (hB.1.lift z.left X.hom hz0) (hB.1.lift_snd _ _ _)
    have comp : ∀ (x₁ : X ⟶ B') (u : Fin r), (x₁ ≫ pr' u).left ≫ φ' = x₁.left ≫ φB ≫ (Out.powPr A u).left :=
      fun x₁ u => by
        show (x₁.left ≫ (pr' u).left) ≫ φ' = _
        rw [Category.assoc, hpr]
    have uniq : ∀ x₁ x₂ : X ⟶ B', (∀ u, x₁ ≫ pr' u = y u) → (∀ u, x₂ ≫ pr' u = y u) → x₁ = x₂ := by
      intro x₁ x₂ h₁ h₂
      refine Over.OverMorphism.ext (hB.1.hom_ext ?_ ((Over.w x₁).trans (Over.w x₂).symm))
      refine powext A r _ _ ?_ fun k => ?_
      · rw [Category.assoc, Category.assoc, hB.1.w, ← Category.assoc, ← Category.assoc, Over.w x₁, Over.w x₂]
      · rw [Category.assoc, Category.assoc, ← comp x₁ k, ← comp x₂ k, h₁, h₂]
    have hx : ∀ u, x ≫ pr' u = y u := fun u => inj _ _ (by
      rw [comp]
      show hB.1.lift z.left X.hom hz0 ≫ φB ≫ (Out.powPr A u).left = (y u).left ≫ φ'
      rw [← Category.assoc, hB.1.lift_fst]
      exact congrArg (fun w => w.left) (hz u))
    exact ⟨x, hx, fun x₁ h₁ => uniq _ _ h₁ hx⟩

end GlobalTheory.ActFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameMemFlagDomainStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_frame_mem_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  first | exact @GlobalTheory.OrthoFrame.exists_frm_mem_dom | exact GlobalTheory.OrthoFrame.exists_frm_mem_dom | (intros; apply GlobalTheory.OrthoFrame.exists_frm_mem_dom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimpleLabelOfSeriesIdempotentPairStatement
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.BasicNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_simple_label_of_seriesIdempotent_pair : ∀ (g : ℕ) [Fact g.Prime] (C : LabelConv (ZMod g)) (O : LabelMap (ZMod g) C) (r : ℕ) (f : (ZMod g)[X]) (ψ : GL (Fin r) (ZMod g) → ℂ), Formalism.L2.NT.IsIrrChar ψ → ∑ x, (Formalism.L2.NT.eSerO O r f).coeff x * ψ x = ψ 1 → ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ HasLabelO O τ f ∧ ∀ x, τ.character x = ψ x := by
  first | exact @GlobalTheory.SeriesIdem.exists_simple_of_eSerO_pair | exact GlobalTheory.SeriesIdem.exists_simple_of_eSerO_pair | (intros; apply GlobalTheory.SeriesIdem.exists_simple_of_eSerO_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCommonFixedLeOneOfCommutingHeckeStatement
section
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_commonFixed_le_one_of_commuting_hecke : ∀ (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Monoid (H c)] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V), (∀ c, e c * e c = e c) → (∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g)) → (∀ c c', c ≠ c' → Commute (e c) (e c')) → (∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h)) → (∀ c g h, e c * a c g * e c * a c h * e c = e c * a c h * e c * a c g * e c) → (∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤) → ∀ W : Submodule ℂ V, (∀ v ∈ W, ∀ c, e c v = v) → finrank ℂ W ≤ 1 := by
  first | exact @GlobalTheory.CommutingHecke.finrank_fixed_le_one | exact GlobalTheory.CommutingHecke.finrank_fixed_le_one | (intros; apply GlobalTheory.CommutingHecke.finrank_fixed_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockOperators_lie_representation_commute : ∀ (p q r s : ℕ), (∀ Y Z, omAct p q r s (Y * Z - Z * Y) = omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y) ∧ IsLieAct (fockAct1 p q r s) ∧ IsLieAct (fockAct2 p q r s) ∧ ∀ Y Z, fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  first | exact @GlobalTheory.FockAlg.fock_lie_and_commute | exact GlobalTheory.FockAlg.fock_lie_and_commute | (intros; apply GlobalTheory.FockAlg.fock_lie_and_commute <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCommOfIrreducibleMultiplicityLeOneStatement
section
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_comm_of_irreducible_multiplicity_le_one : ∀ (H : Type) [Group H] [Finite H] (U : Subgroup H) (χ : H → ℂ), (∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y) → χ 1 = 1 → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ H W), τ.IsIrreducible → finrank ℂ (eig τ (U : Set H) χ) ≤ 1) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V), ∃ e : Module.End ℂ V, e * e = e ∧ (∀ v ∈ eig τ (U : Set H) χ, e v = v) ∧ (∀ T : Module.End ℂ V, (∀ g, Commute T (τ g)) → Commute T e) ∧ ∀ g h : H, e * τ g * e * τ h * e = e * τ h * e * τ g * e := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_idem_hecke_comm | exact GlobalTheory.FinGL.LeviWh.exists_idem_hecke_comm | (intros; apply GlobalTheory.FinGL.LeviWh.exists_idem_hecke_comm <;> assumption)
end

