import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsProportionalSeriesMatchTorsio
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData.LabelMatch
section
variable {O : Type} [CommRing O] {N : NumD O}

theorem qEq_mul {k : ℕ} {p p' q q' : N.QT k} (h : N.QEq p p') (h' : N.QEq q q') : N.QEq (p * q) (p' * q') := by
  obtain ⟨z, h1, h2⟩ := h
  obtain ⟨w, h3, h4⟩ := h'
  refine ⟨z + w, ?_, ?_⟩
  · change p'.1.1.toAdd + q'.1.1.toAdd = p.1.1.toAdd + q.1.1.toAdd + _
    rw [h1, h3, smul_add]; abel
  · change p'.1.2 * q'.1.2 = p.1.2 * q.1.2 * _
    rw [h2, h4, N.io_add]; exact mul_mul_mul_comm _ _ _ _

theorem qEq_incl {k k' : ℕ} (p p' : N.QT k) (q q' : N.QT (k * k')) (hk : k' ≠ 0)
    (a : q.1.1 = p.1.1 ^ k') (b : q.1.2 = p.1.2) (c : q'.1.1 = p'.1.1 ^ k') (d : q'.1.2 = p'.1.2) :
    N.QEq p p' ↔ N.QEq q q' := by
  refine exists_congr fun z => ?_
  rw [a, b, c, d, toAdd_pow, toAdd_pow, mul_comm k, mul_smul, ← smul_add]
  simp only [← natCast_zsmul]
  exact and_congr_left' (smul_right_inj (Int.natCast_ne_zero.2 hk)).symm

theorem tx_congr [TopologicalSpace O] {m : ℕ} (hm : Odd m) {p p' : N.QT (m ^ 2)} (h : N.QEq p p') :
    N.tx m p' = N.tx m p := by
  obtain ⟨z, h1, h2⟩ := h
  exact (tsum_congr fun χ => (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m hm p p' χ).1 z h1 h2).trans
    ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)

theorem wp_congr {k : ℕ} {p p' q q' : N.QT k} (h : N.QEq p p') (h' : N.QEq q q') : N.wp p q = N.wp p' q' := by
  rw [WpPairing.wp_congr_left N h, N.wp_swap q p', WpPairing.wp_congr_left N h', ← N.wp_swap]

variable {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La} {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k}

theorem lab_pow (H : Labels N EF ζ lab) {k : ℕ} (hk : 0 < k) (x : La) (m : ℕ) :
    N.QEq (lab k x ^ (m + 1)) (lab k ((m + 1) • x)) := by
  have E := N.qEq_equivalence k
  induction m with
  | zero => rw [zero_add, pow_one, one_smul]; exact E.refl _
  | succ m ih =>
    rw [pow_succ, succ_nsmul x (m + 1)]
    exact E.trans (qEq_mul ih (E.refl _)) (H.1 k hk _ _)

theorem lab_incl (H : Labels N EF ζ lab) {k k' : ℕ} (hk : 0 < k) (hk' : k' ≠ 0) (x : La) (p : N.QT k)
    (q : N.QT (k * k')) (a : q.1.1 = p.1.1 ^ k') (b : q.1.2 = p.1.2) :
    N.QEq (lab k x) p ↔ N.QEq (lab (k * k') (k' • x)) q := by
  have hk0 : 0 < k' := Nat.pos_of_ne_zero hk'
  have E := N.qEq_equivalence k
  have E' := N.qEq_equivalence (k * k')
  let p₀ : N.QT k := ⟨((lab (k * k') x).1.1, (lab (k * k') x).1.2 ^ k'), by
    have h : (lab (k * k') x).1.2 ^ (k * k') = _ := N.mem_QT.1 (lab (k * k') x).2
    rw [NumD.mem_QT, ← pow_mul, ← h, mul_comm k' k]⟩
  have h0 : N.QEq p₀ (lab k x) := H.2.2.2.1 k k' hk hk0 x p₀ rfl rfl
  have h1 : N.QEq (lab (k * k') x ^ k') (lab (k * k') (k' • x)) := by
    have := lab_pow H (Nat.mul_pos hk hk0) x (k' - 1)
    rwa [Nat.sub_add_cancel hk0] at this
  have h2 := qEq_incl p₀ p (lab (k * k') x ^ k') q hk' rfl rfl a b
  exact ⟨fun h => E'.trans (E'.symm h1) (h2.1 (E.trans h0 h)), fun h => E.trans (E.symm h0) (h2.2 (E'.trans h1 h))⟩

theorem zeta_shift (H : Labels N EF ζ lab) {k : ℕ} (hk : 0 < k) (x e y : La) :
    ζ k ^ EF (x + k • e) y = ζ k ^ EF x y := by
  rw [← H.2.2.2.2 k hk, ← H.2.2.2.2 k hk]
  exact WpPairing.wp_congr_left N ((H.2.1 k hk _ _).2 ⟨e, rfl⟩) _

omit N lab in

theorem zeta_tower {k k' : ℕ} (h : ζ (k * k') ^ k' = ζ k) (x y : La) :
    ζ (k * k') ^ EF (k' • x) y = ζ k ^ EF x y := by
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, h]
end

theorem exists_match : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), n.Prime → Odd n → (∀ (k : ℕ) (x : La), 0 < k → k • x = 0 → x = 0) → Labels N EF ζ lab → Labels N' EF ζ' lab' → (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) → (∀ k m, 0 < k → 0 < m → ζ' (k * m) ^ m = ζ' k) → (∀ j, ζ' (n ^ j) = ζ (n ^ j)) → ∀ c₀ : C, c₀ ≠ 0 → (∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x)) → ∃ mt : GlobalTheory.Ex.Match N N' n, ∀ j p p', mt.r (n ^ j) p p' ↔ ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p' := by
  intro C _ N N' La _ EF ζ ζ' lab lab' n _ hn _ H H' hζ hζ' hζn c₀ hc htx
  have E := N.qEq_equivalence
  have E' := N'.qEq_equivalence
  have hpos : ∀ j, 0 < n ^ j := fun j => pow_pos hn.pos j
  have tr : ∀ k, 0 < k → ∀ a b, N.QEq (lab k a) (lab k b) ↔ N'.QEq (lab' k a) (lab' k b) := fun k hk a b =>
    (H.2.1 k hk a b).trans (H'.2.1 k hk a b).symm
  refine ⟨{
    r := fun k p p' => 0 < k ∧ ∃ x, N.QEq (lab k x) p ∧ N'.QEq (lab' k x) p' ∧ ∀ y, ζ' k ^ EF x y = ζ k ^ EF x y
    tot := fun j p => ?_
    cotot := fun j p' => ?_
    mul := ?_
    eqv := ?_
    inj := ?_
    incl := ?_
    wp := ?_
    c₀ := c₀
    c₀_ne := hc
    tx := ?_ }, fun j p p' => ⟨fun ⟨_, x, a, b, _⟩ => ⟨x, a, b⟩,
      fun ⟨x, a, b⟩ => ⟨hpos j, x, a, b, fun y => by rw [hζn]⟩⟩⟩
  · obtain ⟨x, hx⟩ := H.2.2.1 _ (hpos j) p
    exact ⟨_, hpos j, x, hx, (E' _).refl _, fun y => by rw [hζn]⟩
  · obtain ⟨x, hx⟩ := H'.2.2.1 _ (hpos j) p'
    exact ⟨_, hpos j, x, (E _).refl _, hx, fun y => by rw [hζn]⟩
  · rintro k p q p' q' ⟨hk, x, a, b, c⟩ ⟨-, y, a', b', c'⟩
    refine ⟨hk, x + y, (E _).trans ((E _).symm (H.1 k hk x y)) (qEq_mul a a'),
      (E' _).trans ((E' _).symm (H'.1 k hk x y)) (qEq_mul b b'), fun w => ?_⟩
    rw [map_add, LinearMap.add_apply, zpow_add, zpow_add, c, c']
  · rintro k p q p' q' ⟨hk, x, a, b, c⟩ h
    refine ⟨?_, fun h' => ⟨hk, x, (E _).trans a h, (E' _).trans b h', c⟩⟩
    rintro ⟨-, y, a', b', -⟩
    exact (E' _).trans ((E' _).symm b) ((E' _).trans
      ((tr k hk x y).1 ((E _).trans a ((E _).trans h ((E _).symm a')))) b')
  · rintro k p q p' ⟨hk, x, a, b, -⟩ ⟨-, y, a', b', -⟩
    exact (E _).trans ((E _).symm a) ((E _).trans ((tr k hk x y).2 ((E' _).trans b ((E' _).symm b'))) a')
  · intro k k' p p' q q' hk' a b c d
    have hk0 : 0 < k' := Nat.pos_of_ne_zero hk'
    constructor
    · rintro ⟨hk, x, h1, h2, h3⟩
      refine ⟨Nat.mul_pos hk hk0, k' • x, (lab_incl H hk hk' x p q a b).1 h1,
        (lab_incl H' hk hk' x p' q' c d).1 h2, fun y => ?_⟩
      rw [zeta_tower (hζ k k' hk hk0), zeta_tower (hζ' k k' hk hk0), h3]
    · rintro ⟨hkk, y, h1, h2, h3⟩
      have hk : 0 < k := Nat.pos_of_mul_pos_right hkk
      obtain ⟨x, hx⟩ := H.2.2.1 k hk p
      have h4 : N.QEq (lab _ y) (lab (k * k') (k' • x)) :=
        (E _).trans h1 ((E _).symm ((lab_incl H hk hk' x p q a b).1 hx))
      refine ⟨hk, x, hx, (lab_incl H' hk hk' x p' q' c d).2
        ((E' _).trans ((E' _).symm ((tr _ hkk _ _).1 h4)) h2), fun w => ?_⟩
      obtain ⟨e, rfl⟩ := (H.2.1 _ hkk _ _).1 h4
      have := h3 w
      rwa [zeta_shift H hkk, zeta_shift H' hkk, zeta_tower (hζ k k' hk hk0), zeta_tower (hζ' k k' hk hk0)] at this
  · rintro k p q p' q' ⟨hk, x, a, b, c⟩ ⟨-, y, a', b', -⟩
    rw [← wp_congr a a', ← wp_congr b b', H.2.2.2.2 k hk, H'.2.2.2.2 k hk, c]
  · rintro j p p' ⟨-, x, a, b, -⟩
    rw [tx_congr hn.pow a, tx_congr hn.pow b, htx]

end GlobalTheory.ModelData.LabelMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsSeriesScalarIndependentOfLeve
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData.Scalar

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.ModelData.Scalar.tx_congr {O : Type} [CommRing O] [TopologicalSpace O] (N : _root_.GlobalTheory.Ex.NumD O) {m : ℕ} (hm : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.tx m p = N.tx m p' := by
  unfold _root_.GlobalTheory.Ex.NumD.QEq at h
  obtain ⟨z, hz1, hz2⟩ := h
  unfold _root_.GlobalTheory.Ex.NumD.tx
  have ht : ∀ χ, N.txT m p' χ = N.txT m p (χ + m • z) := fun χ =>
    (_root_.GlobalTheory.Ex.txT_shift O N m hm p p' χ).1 z hz1 hz2
  rw [tsum_congr ht]
  exact ((Equiv.addRight (m • z)).tsum_eq (fun χ => N.txT m p χ)).symm

theorem qEq_mul_right {O : Type} [CommRing O] (N : NumD O) {k : ℕ} {p p' : N.QT k} (h : N.QEq p p') (r : N.QT k) :
    N.QEq (p * r) (p' * r) := by
  obtain ⟨z, rfl⟩ := (N.qEq_iff _ _).1 h
  exact (N.qEq_iff _ _).2 ⟨z, mul_right_comm _ _ _⟩

variable {O : Type} [CommRing O] {N : NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k}

theorem lab_nsmul (h : Labels N EF ζ lab) {k : ℕ} (hk : 0 < k) (a : La) (i : ℕ) :
    N.QEq (lab k a ^ i) (lab k (i • a)) := by
  induction i with
  | zero =>
    have e := qEq_mul_right N (h.1 k hk 0 0) (lab k 0)⁻¹
    rw [add_zero, mul_inv_cancel_right, mul_inv_cancel] at e
    rw [pow_zero, zero_nsmul]
    exact (N.qEq_equivalence k).symm e
  | succ i ih =>
    rw [pow_succ, succ_nsmul]
    exact (N.qEq_equivalence k).trans (qEq_mul_right N ih _) (h.1 k hk _ _)

theorem lab_tower (h : Labels N EF ζ lab) {k m K : ℕ} (hk : 0 < k) (hm : 0 < m) (hK : K = k * m) (a : La)
    (p : N.QT k) (h1 : p.1.1 = (lab K a).1.1) (h2 : p.1.2 = (lab K a).1.2 ^ m) : N.QEq p (lab k a) := by
  subst hK
  exact h.2.2.2.1 k m hk hm a p h1 h2

theorem tx_nest [TopologicalSpace O] (h : Labels N EF ζ lab) {n m M : ℕ} (hn : Odd n) (hm : Odd m) (hM : M = n * m)
    (x : La) : N.tx M (lab _ (n • x)) = N.tx m (lab _ x) := by
  subst hM
  have hK : (n * m) ^ 2 = m ^ 2 * n ^ 2 := by ring
  let P := lab ((n * m) ^ 2) x
  let p : N.QT (m ^ 2) := ⟨(P.1.1, P.1.2 ^ n ^ 2), by
    rw [NumD.mem_QT, ← pow_mul, mul_comm (n ^ 2), ← hK]
    exact N.mem_QT.1 P.2⟩
  have e1 := lab_nsmul h (pow_pos (hn.mul hm).pos 2) x n
  have e2 := lab_tower h (pow_pos hm.pos 2) (pow_pos hn.pos 2) hK x p rfl rfl
  rw [← tx_congr N (hn.mul hm) e1, ← tx_congr N hm e2, NumD.tx, NumD.tx]
  refine tsum_congr fun χ => GlobalTheory.T.degenerationSeriesTerms_nest O N n m hn hm _ p rfl ?_ χ
  change P.1.2 ^ n ^ 2 = (P.1.2 ^ n) ^ n
  rw [← pow_mul, sq n]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {O : Type} [CommRing O] {N : _root_.GlobalTheory.Ex.NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k} in
private theorem qEq_mul' (N : _root_.GlobalTheory.Ex.NumD O) {k : ℕ}
    {p p' q q' : N.QT k} (h : N.QEq p p')
    (h' : N.QEq q q') :
    N.QEq (p * q) (p' * q') := by
  unfold _root_.GlobalTheory.Ex.NumD.QEq at *
  obtain ⟨z, hz1, hz2⟩ := h
  obtain ⟨z', hz1', hz2'⟩ := h'
  refine ⟨z + z', ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Prod.fst_mul, toAdd_mul, hz1, hz1', smul_add]
    abel
  · simp only [Subgroup.coe_mul, Prod.snd_mul, hz2, hz2', N.io_add]
    ac_rfl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {O : Type} [CommRing O] {N : _root_.GlobalTheory.Ex.NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k} in
private theorem qEq_label_pow_nsmul
    (hL : _root_.GlobalTheory.ModelData.Labels N EF ζ lab) {k : ℕ} (hk : 0 < k) (x : La) :
    ∀ d : ℕ, 1 ≤ d → N.QEq ((lab k x) ^ d) (lab k (d • x)) := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => simpa using (N.qEq_equivalence k).refl (lab k x)
  | succ d hd ih =>
    rw [pow_succ, succ_nsmul]
    unfold _root_.GlobalTheory.ModelData.Labels at hL
    exact (N.qEq_equivalence k).trans
      (qEq_mul' N ih ((N.qEq_equivalence k).refl _)) (hL.1 k hk _ _)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {O : Type} [CommRing O] {N : _root_.GlobalTheory.Ex.NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k} in
private theorem tx_label_nsmul_eq_of_odd [TopologicalSpace O]
    (hL : _root_.GlobalTheory.ModelData.Labels N EF ζ lab) {d m : ℕ} (hd : Odd d) (hm : Odd m)
    (K : ℕ) (hK : K = d * m) (x : La) :
    N.tx K (lab (K ^ 2) (d • x)) = N.tx m (lab (m ^ 2) x) := by
  subst hK
  have hdm : Odd (d * m) := hd.mul hm
  set q := lab ((d * m) ^ 2) x with hq
  have hmem : ((q : Multiplicative N.X × N.Gt).1, (q : Multiplicative N.X × N.Gt).2 ^ (d ^ 2)) ∈
      N.QT (m ^ 2) := by
    rw [N.mem_QT]
    have hqm := (N.mem_QT).1 q.2
    rw [← pow_mul, show d ^ 2 * m ^ 2 = (d * m) ^ 2 by ring]
    exact hqm
  set p : N.QT (m ^ 2) := ⟨_, hmem⟩ with hp
  have h1 : N.tx (d * m) (lab ((d * m) ^ 2) (d • x)) =
      N.tx (d * m) (q ^ d) :=
    (_root_.GlobalTheory.ModelData.Scalar.tx_congr N hdm
      (qEq_label_pow_nsmul hL (pow_pos hdm.pos 2) x d hd.pos)).symm
  have h2 : N.tx (d * m) (q ^ d) = N.tx m p := by
    unfold _root_.GlobalTheory.Ex.NumD.tx
    refine tsum_congr (fun χ => ?_)
    refine _root_.GlobalTheory.Ex.Nest.txT_nest O N d m hd hm (q ^ d) p ?_ ?_ χ
    · rw [SubgroupClass.coe_pow, Prod.pow_fst]
    · rw [SubgroupClass.coe_pow, Prod.pow_snd, ← pow_mul, ← sq]
  have h3 : N.QEq p (lab (m ^ 2) x) := by
    have c4 : ∀ K, m ^ 2 * d ^ 2 = K → ∀ p' : N.QT (m ^ 2),
        (p' : Multiplicative N.X × N.Gt).1 = (lab K x : Multiplicative N.X × N.Gt).1 →
        (p' : Multiplicative N.X × N.Gt).2 = (lab K x : Multiplicative N.X × N.Gt).2 ^ (d ^ 2) →
        N.QEq p' (lab (m ^ 2) x) := by
      intro K hK
      subst hK
      unfold _root_.GlobalTheory.ModelData.Labels at hL
      exact hL.2.2.2.1 (m ^ 2) (d ^ 2) (pow_pos hm.pos 2) (pow_pos hd.pos 2) x
    exact c4 ((d * m) ^ 2) (by ring) p rfl rfl
  rw [h1, h2]
  exact _root_.GlobalTheory.ModelData.Scalar.tx_congr N hm h3

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {O : Type} [CommRing O] {N : _root_.GlobalTheory.Ex.NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k} in

theorem _root_.GlobalTheory.ModelData.Scalar.scalar_const : ∀ (C : Type) [NormedField C] (N N' : _root_.GlobalTheory.Ex.NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), Odd n → _root_.GlobalTheory.ModelData.Labels N EF ζ lab → _root_.GlobalTheory.ModelData.Labels N' EF ζ' lab' → (∀ j, ∃ c : Cˣ, ∀ x, N'.tx (n ^ j) (lab' _ x) = c * N.tx (n ^ j) (lab _ x)) → (∃ x, N.tx (n ^ 1) (lab _ x) ≠ 0) → ∃ c₀ : C, c₀ ≠ 0 ∧ ∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x) := by
  intro C _ N N' La _ EF ζ ζ' lab lab' n hn hL hL' hc hx
  obtain ⟨x₀, hx₀⟩ := hx
  obtain ⟨c₁, hc₁⟩ := hc 1
  have hn1 : Odd (n ^ 1) := by simpa using hn
  refine ⟨c₁, c₁.ne_zero, fun j x => ?_⟩
  cases j with
  | zero =>
    have e1 := tx_label_nsmul_eq_of_odd hL hn (Odd.pow hn : Odd (n ^ 0)) (n ^ 1) (by ring) x
    have e2 := tx_label_nsmul_eq_of_odd hL' hn (Odd.pow hn : Odd (n ^ 0)) (n ^ 1) (by ring) x
    rw [← e1, ← e2, hc₁]
  | succ i =>
    obtain ⟨c, hc'⟩ := hc (i + 1)
    have e1 := tx_label_nsmul_eq_of_odd hL (Odd.pow hn : Odd (n ^ i)) hn1 (n ^ (i + 1))
      (by ring) x₀
    have e2 := tx_label_nsmul_eq_of_odd hL' (Odd.pow hn : Odd (n ^ i)) hn1 (n ^ (i + 1))
      (by ring) x₀
    have hcc : (c : C) = c₁ := by
      have h := hc' (n ^ i • x₀)
      rw [e1, e2, hc₁] at h
      exact (mul_right_cancel₀ hx₀ h).symm
    rw [hc' x, hcc]

end GlobalTheory.ModelData.Scalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraceEqSumFinrank
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Ex.Arch

variable {E : Type} [Field E] [NumberField E]

theorem exists_types (m : (E →+* ℂ) → ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)),
    (∀ φ, Nat.card {i // ty i = φ} = m φ) ∧ ∀ a : E, ∑ i, ty i a = ∑ φ : E →+* ℂ, (m φ : ℂ) * φ a := by
  classical
  let e := (Fintype.equivFin (Σ φ : E →+* ℂ, Fin (m φ))).symm
  refine ⟨_, fun i => (e i).1, fun φ => ?_, fun a => ?_⟩
  · rw [Nat.card_congr (e.subtypeEquiv (q := fun k => k.1 = φ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype φ)]
    simp
  · rw [e.sum_comp fun k => k.1 a, Fintype.sum_sigma]
    simp

theorem trace_eq_sum_finrank {g : ℕ} (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (a : 𝓞 E) :
    LinearMap.trace ℂ _ (ρ a) = ∑ φ : E →+* ℂ,
      (Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : ℂ) * φ (a : E) := by
  obtain ⟨g', ty, hc, hs⟩ :=
    exists_types fun φ : E →+* ℂ => Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E)))
  obtain ⟨h, hh⟩ := PointUnif.exists_equiv_of_finrank_eq (PointUnif.isSplitting_embeddings (E := E))
    (PointUnif.diagRep ty) ρ fun φ => by rw [PointUnif.finrank_eigenSub_diagRep, hc]
  have h1 : ρ a = h.conj (PointUnif.diagRep ty a) := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hh]
  have h2 : PointUnif.diagRep ty a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
    LinearMap.ext fun z => funext fun i => by simp [PointUnif.diagRep_apply, Matrix.mulVec_diagonal]
  rw [h1, LinearMap.trace_conj', h2, ← hs]
  simp

theorem typeSt : TypeSt := by
  intro E _ _ _ H D
  let _ := H.starRing
  intro B hB
  classical
  obtain ⟨g, ty, hc, hs⟩ := exists_types fun φ : E →+* ℂ => if φ (H.rt : E) = H.rt0 then D.p else D.q
  have hbar : ∀ a : 𝓞 E, ∑ τ : E →+* ℂ, τ (H.bar a : E) = ∑ τ : E →+* ℂ, τ (a : E) := fun a => by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ _
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have := HomTrace.finite_hom B.X
  obtain ⟨h, hh⟩ := PeriodNonempty.exists_diag B.actV ty fun a => by
    let f : (B.X →+ ℂ) →ₗ[ℂ] (B.X →+ ℂ) := LinearMap.fst ℂ _ _ ∘ₗ B.actV a ∘ₗ LinearMap.inl ℂ _ _
    have h1 : B.actV a = f.prodMap (B.F a) := LinearMap.ext fun v => rfl
    rw [h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E B.X (H.bar a) f fun _ _ => rfl, hbar,
      trace_eq_sum_finrank, hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have h2 : Module.finrank ℂ (EigenSplit.eigenSub B.F (φ.comp (algebraMap (𝓞 E) E))) + Module.finrank (𝓞 E) B.X =
        if φ (H.rt : E) = H.rt0 then D.p else D.q := by
      have h3 := hB (φ.comp (algebraMap (𝓞 E) E))
      by_cases hφ : φ (H.rt : E) = H.rt0
      · rw [if_pos hφ]; exact h3.trans (if_pos hφ)
      · rw [if_neg hφ]; exact h3.trans (if_neg hφ)
    rw [← h2]
    push_cast
    ring
  exact ⟨g, ty, h, fun φ => ⟨fun hφ => (hc φ).trans (if_pos hφ), fun hφ => (hc φ).trans (if_neg hφ)⟩, hh⟩

end GlobalTheory.Ex.Arch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.GenericFibre

theorem exists_iso_section {X₁ X₂ Y : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {g : Y ⟶ X₁} {f : Y ⟶ X₂} (i : X₁ ⟶ Y)
    (hi : i ≫ g = 𝟙 X₁) (w₀ : LB.Iso (L₁.pull g) (L₂.pull f)) (hw : w₀.IsGen) :
    ∃ w : LB.Iso L₁ (L₂.pull (i ≫ f)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (k : L₁.ι),
      f (i (r z)) ∈ L₂.U j → r z ∈ L₁.U k → gw w r z j k = BoxExpansion.pw w₀ (r ≫ i) z k j := by
  have pt : ∀ x : X₁, g (i x) = x := fun x => congrArg (fun q : X₁ ⟶ X₁ => q x) hi
  have le : ∀ p : (PUnit → L₂.ι) × L₁.ι, (L₂.pull (i ≫ f)).U p.1 ⊓ L₁.U p.2 ≤
      i ⁻¹ᵁ ((L₂.pull f).U p.1 ⊓ (L₁.pull g).U (fun _ => p.2)) := fun p y hy =>
    ⟨mem_pull.2 ((mem_pull (F := i ≫ f)).1 hy.1), mem_pull.2 (by rw [pt]; exact hy.2)⟩
  let w : LB.Iso L₁ (L₂.pull (i ≫ f)) := ⟨fun p => res (le p) (pullU i _ (w₀.s (p.1, fun _ => p.2)))⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (k : L₁.ι),
      f (i (r z)) ∈ L₂.U j → r z ∈ L₁.U k → gw w r z j k = BoxExpansion.pw w₀ (r ≫ i) z k j := by
    intro Z r z j k hj hk
    have hm : r z ∈ (L₂.pull (i ≫ f)).U (fun _ => j) ⊓ L₁.U k := ⟨(mem_pull (F := i ≫ f)).2 hj, hk⟩
    exact (gm_res r z (le (fun _ => j, k)) hm _).trans (gm_pull r i z _ (le (fun _ => j, k) hm) _)
  refine ⟨w, (isGen_iff w).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, key⟩
  rw [key Z r z j k hj hk, key Z r z j' k' hj' hk',
    BoxExpansion.pw_trans hw (r ≫ i) z (j₁ := k) (j₁' := k') (j₂ := j) (j₂' := j')
      (by show g (i (r z)) ∈ _; rw [pt]; exact hk) (by show g (i (r z)) ∈ _; rw [pt]; exact hk') hj hj',
    Category.assoc, Category.assoc, hi, Category.comp_id]

theorem exists_pull_sec {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : φ' = fun k => h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ z J, Good L z J → sval s' (𝟙 _) z J = sval s h z J := by
  subst e
  exact ⟨pullSec L φ ε s h, fun z J hJ => (SectionScalarValuation.sval_pullSec φ ε s h (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩

theorem exists_isoData : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), ∃ (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧ NormW U w₀ ρ ∧ w.IsGen ∧ IsRigidificationPullbackCompatibleIso w (jK R) ρ U.LG.rig ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : H0 U.LG.L k) (th : SecA A F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J) (J'), Good U.LG.L z J → Good A.L z J' → sval σ (r ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) z J = (wVal w z J J' (r ≫ (snd (TFK (R := R) F) A.A).left) ^ (k : ℤ)).val * VVRank.sv A.A th r z J') → ∃ σ' : U.SecGF F k, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) ∧ ∀ s, U.ExpandsG F k σ' s → U.ExpandsF F k w₀ th s := by
  intro R _ _ I D A G _ _ U
  obtain ⟨w₀, hw₀⟩ := U.ext
  have hi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have hi' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  obtain ⟨w, hw, key⟩ := exists_iso_section U.gen.inv.left hi w₀ hw₀
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hp₁ : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have hp₂ := isGrpPullback_pullback G (jK R)
  have hp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (hp₁.comp hp₂).congr (Category.id_comp _) rfl
  obtain ⟨ρ, hρ, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw U.LG.isLB A.isLB (ρ₀ := U.LG.rig) U.LG.rigGen
  refine ⟨w₀, ρ, w, hp, ⟨hw₀, hρ, fun z JA JG hA hG => ?_⟩, hw, hr, fun F _ _ k σ th H => ?_⟩
  · have e₁ : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) :=
      (cubeMapOf hp₁).e_comm.trans (Category.id_comp _)
    have e₂ : eSec ((Over.pullback (jK R)).obj G) ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G :=
      (cubeMapOf hp₂).e_comm
    have := hr _ (𝟙 _) z JG JA hG hA
    rw [Category.id_comp, Category.id_comp, wVal, key _ _ _ _ _ (hG (eSec A.A ≫ _ ≫ _)) (hA _), ← Category.assoc, e₁, e₂] at this
    exact this.symm
  · obtain ⟨σ', hσ⟩ := exists_pull_sec σ (UnifPre.gFK (G := G) F) (fun _ : Fin 1 => UnifPre.gFK (G := G) F)
      (funext fun _ => (Category.comp_id _).symm)
    have e : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    refine ⟨σ', hσ, fun s hs => ⟨σ', BoxExpansion.isoRel_of_val A.isLB U.LG.isLB e (Category.id_comp _)
      fun y J₁ J₂ h₁ h₂ => ?_, hs⟩⟩
    have e' : ((U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
      rw [e, Category.assoc, hi', Category.comp_id]
    have := H _ (U.genF F).left y J₂ J₁ h₂ h₁
    rw [wVal, key _ _ _ _ _ (h₂ (((U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left) ≫ _ ≫ _)) (h₁ _),
      ← Category.assoc, ← Category.assoc, e', e, zpow_natCast] at this
    exact (hσ y J₂ h₂).trans this

end GlobalTheory.Ex.GenericFibre
end
end

