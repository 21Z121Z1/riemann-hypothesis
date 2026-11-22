import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubNSucc
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.CubeBalance

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem cubN_succ (θ : A → A → A → U) (k : ℕ) (x y : A) :
    cubN θ (k + 1) 1 x y = cubN θ k 1 x y * θ (x ^ k) x y := by
  simp only [cubN, Finset.prod_range_succ, _root_.one_mul]

theorem cubN_add (h : IsCub θ) (a b : ℕ) (x y : A) :
    cubN θ (a + b) 1 x y = θ (x ^ a) (x ^ b) y * cubN θ a 1 x y * cubN θ b 1 x y := by
  have s := h.N_split b (x ^ a) x y
  have e : cubN θ (a + b) 1 x y = cubN θ a 1 x y * cubN θ b (x ^ a) x y := by
    simp only [cubN, Finset.prod_range_add, _root_.one_mul, pow_add]
  rw [e, s, ← _root_.mul_assoc, mul_comm (cubN θ a 1 x y)]

theorem cubN_mul (h : IsCub θ) (a b : ℕ) (x y : A) :
    cubN θ (a * b) 1 x y = cubN θ a 1 (x ^ b) y * cubN θ b 1 x y ^ a := by
  induction a with
  | zero => simp [cubN]
  | succ a ih =>
    rw [Nat.succ_mul, cubN_add h, ih, cubN_succ, ← pow_mul, mul_comm b a, pow_succ]
    ac_rfl

theorem cubN_swap (h : IsCub θ) (a b : ℕ) (x y : A) :
    cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a = cubN θ b 1 y (x ^ a) * cubN θ a 1 x y ^ b := by
  induction b with
  | zero =>
    rw [pow_zero, h.N_one]
    simp [cubN]
  | succ b ih =>
    have n := h.N_add a 1 x (y ^ b) y
    rw [h.face, _root_.mul_one, _root_.one_mul] at n
    have r : ∀ z : A, θ (y ^ b) y z = θ z (y ^ b) y := fun z => by rw [h.s12, h.s01]
    rw [cubN_succ, cubN_succ, r, r, pow_succ y, mul_pow, pow_succ, mul_comm (cubN θ b 1 y x ^ a),
      ← _root_.mul_assoc, n]
    calc θ (x ^ a) (y ^ b) y * cubN θ a 1 x (y ^ b) * cubN θ a 1 x y * cubN θ b 1 y x ^ a
        = θ (x ^ a) (y ^ b) y * cubN θ a 1 x y * (cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a) := by ac_rfl
      _ = _ := by rw [ih]; ac_rfl

theorem balance : ∀ (A U : Type) [CommGroup A] [CommGroup U] (θ : A → A → A → U), IsCub θ → ∀ (a b : ℕ) (x y : A), cubN θ (a * b) 1 x y = cubN θ a 1 (x ^ b) y * cubN θ b 1 x y ^ a ∧ cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a = cubN θ b 1 y (x ^ a) * cubN θ a 1 x y ^ b ∧ cubN θ (a + b) 1 x y = θ (x ^ a) (x ^ b) y * cubN θ a 1 x y * cubN θ b 1 x y :=
  fun _ _ _ _ _ h a b x y => ⟨cubN_mul h a b x y, cubN_swap h a b x y, cubN_add h a b x y⟩

end GlobalTheory.CubeBalance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataPsiQuadraticGeneratorsLinear
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.PsiQuadratic
variable {O : Type} [CommRing O] (N : NumD O)

theorem τ_self (y : N.X) : N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) := by
  have a := N.τ_add_left y (-y) y
  rw [add_neg_cancel, N.τ_zero_left, one_mul, N.c_neg] at a
  have b := N.ψ_add (-y) y
  rw [neg_add_cancel, N.ψ_zero] at b
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  have c' := congrArg Additive.ofMul (N.even y)
  apply Additive.ofMul.injective
  simp only [dbl, sq, ofMul_mul, ofMul_div, ofMul_one] at a' b' c' ⊢
  linear_combination (norm := abel) -a' + b' + c'

theorem s_nsmul (g : N.Gt) (n : ℕ) (y : N.X) : g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have m := g.mult (n • y) y
    rw [N.c_nsmul] at m
    rw [cubN] at ih
    rw [succ_nsmul, cubN, Finset.prod_range_succ, one_mul, pow_succ, ← ih, mul_right_comm _ _ (g.s y), ← m,
      ← mul_assoc, mul_right_comm]

theorem ψ_nsmul (n : ℕ) (y : N.X) : N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) := by
  induction n with
  | zero => simp [mulq]
  | succ n ih =>
    have a := s_nsmul N (N.io y) n y
    rw [N.io_s, N.io_s, N.io_b, τ_self, N.τ_symm] at a
    rw [mulq] at ih
    rw [succ_nsmul, N.ψ_add, mulq, Finset.prod_range_succ, show (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 by ring,
      pow_succ, pow_add, pow_mul, ← ih]
    rw [mul_pow] at a
    have a' := congrArg Additive.ofMul a
    apply Additive.ofMul.injective
    generalize (N.ψ y ^ 2) ^ n = u at a' ⊢
    generalize dbl N.θ N.σ (N.c y) ^ n = v at a' ⊢
    simp only [ofMul_mul, ofMul_div] at a' ⊢
    linear_combination (norm := abel) a'

theorem main : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n : ℕ) (y : N.X),
    N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) ∧ N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) ∧
    ∀ (g : N.Gt), g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n ∧
      (g ^ n).s y * cubN N.θ n 1 g.b (N.c y) = g.s y ^ n :=
  fun _ _ N n y => ⟨τ_self N y, ψ_nsmul N n y, fun g => ⟨s_nsmul N g n y, g.pow_s n y⟩⟩

end GlobalTheory.PsiQuadratic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingProperties
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.WpPairing

variable {O : Type} [CommRing O] (N : NumD O)

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.WpPairing.s_nsmul (g : N.Gt) (n : ℕ) (y : N.X) : g.s (n • y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ n 1 (N.c y) g.b = g.s y ^ n := by
  induction n with
  | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, _root_.GlobalTheory.Ex.NumD.Gt.s_zero]
  | succ n ih =>
    have hm := g.mult (n • y) y
    rw [succ_nsmul, pow_succ, ← ih]
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, Finset.prod_range_succ, one_mul]
    rw [← N.c_nsmul, ← mul_assoc, mul_right_comm, hm]
    exact mul_right_comm _ _ _

theorem tk_mul_left {k : ℕ} (p p' p'' : N.QT k) :
    N.tk (p * p') p'' * N.θ p''.1.2.b p.1.2.b p'.1.2.b ^ k = N.tk p p'' * N.tk p' p'' := by
  have e := N.cub.N_add k 1 p''.1.2.b p.1.2.b p'.1.2.b
  rw [N.cub.face, mul_one, one_mul, N.QT_pow_b] at e
  change (p.1.2 * p'.1.2).s p''.1.1.toAdd * cubN N.θ k 1 p''.1.2.b (p.1.2.b * p'.1.2.b) * _ = _
  rw [NumD.Gt.mul_s, NumD.tk, NumD.tk]
  apply Additive.ofMul.injective
  replace e := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_div] at e ⊢
  linear_combination (norm := abel) e

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in
private lemma cubN_one_mul_mul_pow_eq {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
    (hθ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub θ) (n : ℕ) (b b' m : A) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN θ n 1 (b * b') m * θ b b' m ^ n =
      θ (b ^ n) (b' ^ n) m * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN θ n 1 b m * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN θ n 1 b' m := by
  induction n with
  | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, hθ.face]
  | succ n ih =>
    have c1 := hθ.coc (b ^ n * b' ^ n) b b' m
    have c2 := hθ.coc (b ^ n * b) (b' ^ n) b' m
    have c3 := hθ.coc (b ^ n) (b' ^ n) b m
    have c4 := hθ.coc (b ^ n) b (b' ^ n) m
    rw [mul_right_comm (b ^ n) b (b' ^ n)] at c2
    rw [mul_comm b (b' ^ n), hθ.s01 b (b' ^ n) m] at c4
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, Finset.prod_range_succ, one_mul, mul_pow, pow_succ] at ih ⊢
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c1' := congrArg Additive.ofMul c1
    have c2' := congrArg Additive.ofMul c2
    have c3' := congrArg Additive.ofMul c3
    have c4' := congrArg Additive.ofMul c4
    simp only [ofMul_mul, ofMul_pow] at ih' c1' c2' c3' c4' ⊢
    linear_combination (norm := abel) ih' + c2' + c3' - c1' - c4'

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.WpPairing.wp_mul_left {k : ℕ} (p p' p'' : N.QT k) : N.wp (p * p') p'' = N.wp p p'' * N.wp p' p'' := by
  have hθ := N.cub
  set g := (p : Multiplicative N.X × N.Gt).2 with hg
  set g' := (p' : Multiplicative N.X × N.Gt).2 with hg'
  set h := (p'' : Multiplicative N.X × N.Gt).2 with hh
  set x := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with hx
  set x' := Multiplicative.toAdd (p' : Multiplicative N.X × N.Gt).1 with hx'
  set y := Multiplicative.toAdd (p'' : Multiplicative N.X × N.Gt).1 with hy
  have bp := N.QT_pow_b p
  have bp' := N.QT_pow_b p'
  have bq := N.QT_pow_b p''
  rw [← hg, ← hx] at bp
  rw [← hg', ← hx'] at bp'
  rw [← hh, ← hy] at bq
  have e1 : N.tk (p * p') p'' = g.s y * g'.s y /
      N.θ (N.c y) g.b g'.b *
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b
        (g.b * g'.b) := by
    simp only [_root_.GlobalTheory.Ex.NumD.tk, Subgroup.coe_mul, Prod.snd_mul,
      _root_.GlobalTheory.Ex.NumD.Gt.mul_s,
      _root_.GlobalTheory.Ex.NumD.Gt.mul_b]
    rfl
  have e2 : N.tk p'' (p * p') = h.s (x + x') *
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 (g.b * g'.b)
        h.b := by
    simp only [_root_.GlobalTheory.Ex.NumD.tk, Subgroup.coe_mul, Prod.snd_mul, Prod.fst_mul,
      toAdd_mul, _root_.GlobalTheory.Ex.NumD.Gt.mul_b]
    rfl
  have e3 : N.tk p p'' =
      g.s y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b g.b := rfl
  have e4 : N.tk p' p'' =
      g'.s y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 h.b g'.b := rfl
  have e5 : N.tk p'' p =
      h.s x * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 g.b h.b := rfl
  have e6 : N.tk p'' p' =
      h.s x' * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ k 1 g'.b h.b := rfl
  have hm := h.mult x x'
  have hadd := hθ.N_add k 1 h.b g.b g'.b
  have hmid := cubN_one_mul_mul_pow_eq hθ k g.b g'.b
    h.b
  have hsym : N.θ h.b g.b g'.b =
      N.θ g.b g'.b h.b := by
    rw [hθ.s01, hθ.s12]
  rw [hθ.face, one_mul, hsym] at hadd
  rw [← bp, ← bp'] at hm
  rw [← bq] at e1
  simp only [_root_.GlobalTheory.Ex.NumD.wp]
  rw [e1, e2, e3, e4, e5, e6]
  apply Additive.ofMul.injective
  have hm' := congrArg Additive.ofMul hm
  have hadd' := congrArg Additive.ofMul hadd
  have hmid' := congrArg Additive.ofMul hmid
  simp only [ofMul_mul, ofMul_pow, ofMul_div, ofMul_one] at hm' hadd' hmid' ⊢
  linear_combination (norm := abel) hadd' - hmid' - hm'

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.WpPairing.wp_mul_right {k : ℕ} (p p' p'' : N.QT k) : N.wp p (p' * p'') = N.wp p p' * N.wp p p'' := by
  rw [N.wp_swap (p' * p'') p, _root_.GlobalTheory.Ex.WpPairing.wp_mul_left, mul_inv, ← N.wp_swap p' p, ← N.wp_swap p'' p]

noncomputable def wpHom {k : ℕ} (q : N.QT k) : N.QT k →* Oˣ :=
  MonoidHom.mk' (fun p => N.wp p q) fun p p' => wp_mul_left N p p' q

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.WpPairing.wp_pow_left {k : ℕ} (p q : N.QT k) (n : ℕ) : N.wp (p ^ n) q = N.wp p q ^ n :=
  map_pow (_root_.GlobalTheory.Ex.WpPairing.wpHom N q) p n

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.WpPairing.wp_qTriv {k : ℕ} (z : N.X) (q : N.QT k) : N.wp (N.qTriv k z) q = 1 := by
  have hq := N.mem_QT.mp q.2
  have h1 := _root_.GlobalTheory.Ex.WpPairing.s_nsmul N
    (q : Multiplicative N.X × N.Gt).2 k z
  have h2 := _root_.GlobalTheory.Ex.NumD.Gt.pow_s
    (q : Multiplicative N.X × N.Gt).2 k z
  rw [hq, _root_.GlobalTheory.Ex.NumD.io_s, _root_.GlobalTheory.Ex.NumD.τ_symm] at h2
  simp only [_root_.GlobalTheory.Ex.NumD.wp, _root_.GlobalTheory.Ex.NumD.tk,
    _root_.GlobalTheory.Ex.NumD.qTriv, _root_.GlobalTheory.Ex.NumD.io_s,
    _root_.GlobalTheory.Ex.NumD.io_b, toAdd_ofAdd, div_eq_one]
  rw [h1, h2]

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.WpPairing.wp_congr_left {k : ℕ} {p p' : N.QT k} (h : N.QEq p p') (q : N.QT k) : N.wp p q = N.wp p' q := by
  obtain ⟨z, rfl⟩ := (N.qEq_iff p p').mp h
  rw [_root_.GlobalTheory.Ex.WpPairing.wp_mul_left, _root_.GlobalTheory.Ex.WpPairing.wp_qTriv, mul_one]

open scoped BigOperators in
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.WpPairing.wp_pairing : ∀ (O : Type) [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O), ∀ (k : ℕ) (p p' p'' : N.QT k), N.wp (p * p') p'' = N.wp p p'' * N.wp p' p'' ∧ N.wp p p = 1 ∧ N.wp p p' * N.wp p' p = 1 ∧ N.wp p p' ^ k = 1 ∧ (N.QEq p p' → N.wp p p'' = N.wp p' p'') ∧ (p.1.1 = 1 → p.1.2.b = 1 → N.wp p p' = p.1.2.s p'.1.1.toAdd) ∧ (p.1.1 = 1 → p'.1.1 = 1 → N.wp p p' = N.weil k p.1.2.b p'.1.2.b) := by
  intro O _ N k p p' p''
  refine ⟨_root_.GlobalTheory.Ex.WpPairing.wp_mul_left N p p' p'', N.wp_self p, ?_, ?_,
    fun h => _root_.GlobalTheory.Ex.WpPairing.wp_congr_left N h p'', ?_,
    fun h1 h2 => N.wp_of_eq_zero p p' (by simp [h1]) (by simp [h2])⟩
  · rw [N.wp_swap p p', mul_inv_cancel]
  · have hp : p ^ k = N.qTriv k
        (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1) := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, _root_.GlobalTheory.Ex.NumD.qTriv]
      refine Prod.ext ?_ ?_
      · simp
      · simpa using N.mem_QT.mp p.2
    rw [← _root_.GlobalTheory.Ex.WpPairing.wp_pow_left, hp, _root_.GlobalTheory.Ex.WpPairing.wp_qTriv]
  · intro h1 hb
    obtain ⟨t, ht⟩ := (N.exists_tor_iff _).mpr hb
    have hk := N.mem_QT.mp p.2
    rw [h1, toAdd_one, N.io_zero] at hk
    have htk : t ^ k = 1 := N.tor_injective (by rw [N.tor_pow, ht, N.tor_one, hk])
    have hp : p = N.qTor t htk := by
      apply Subtype.ext
      simp only [_root_.GlobalTheory.Ex.NumD.qTor]
      exact Prod.ext h1 ht.symm
    calc N.wp p p' =
          N.wp (N.qTor t htk) p' := by
          rw [← hp]
      _ = t (p' : Multiplicative N.X × N.Gt).1 := N.wp_qTor t htk p'
      _ = _ := by rw [← ht, N.torus_generator_apply, ofAdd_toAdd]

end GlobalTheory.Ex.WpPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.SS.exists_complete_dvr_finite_extension : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L], ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : Algebra V W) (_ : Algebra W L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ Module.Finite V W ∧ Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W) ∧ (∀ x : L, RingHom.IsIntegralElem ((algebraMap K L).comp (algebraMap V K)) x → x ∈ Set.range (algebraMap W L)) ∧ ∀ (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] Q, _root_.GlobalTheory.SS.PotModel W L ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) Q → _root_.GlobalTheory.SS.PotModel V K A Q := by
  intro V K _ _ _ _ _ _ _ _ L _ _ _
  classical
  letI : Algebra V L := ((algebraMap K L).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' rfl
  have hinj : Function.Injective (algebraMap V L) :=
    (algebraMap K L).injective.comp (IsFractionRing.injective V K)
  haveI : CharZero V := (algebraMap V K).charZero
  haveI : FaithfulSMul V L := (faithfulSMul_iff_algebraMap_injective V L).mpr hinj
  haveI : Algebra.IsAlgebraic V L := (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
  haveI : Module.Finite V (integralClosure V L) := IsIntegralClosure.finite V K L (integralClosure V L)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := V) (M := integralClosure V L)
  obtain ⟨W, _, hc, -, hfin, -, hloc, -, hint⟩ :=
    _root_.GlobalTheory.exists_complete_dvr_finite_subalgebra V L (t.image Subtype.val)
  have hcl : ∀ x : L, IsIntegral V x → x ∈ W := by
    intro x hx
    have key : ∀ y ∈ Submodule.span V (t : Set (integralClosure V L)), (y : L) ∈ W := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hint _ (Finset.mem_image_of_mem _ hy) y.2
      | zero => exact W.zero_mem
      | add a b _ _ ha hb => exact W.add_mem ha hb
      | smul r a _ ha => exact W.smul_mem ha r
    exact key ⟨x, hx⟩ (by rw [ht]; trivial)
  have hWint : ∀ w : W, IsIntegral V (w : L) := fun w =>
    (Algebra.IsIntegral.isIntegral (R := V) w).map W.val
  haveI : IsIntegralClosure W V L :=
    ⟨Subtype.val_injective, fun {x} => ⟨fun hx => ⟨⟨x, hcl x hx⟩, rfl⟩, by
      rintro ⟨w, rfl⟩
      exact hWint w⟩⟩
  haveI : IsFractionRing W L :=
    IsIntegralClosure.isFractionRing_of_algebraic V W (fun x hx => hinj (by rw [hx, map_zero]))
  have hcomp : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) :=
    RingHom.ext fun _ => rfl
  refine ⟨W, inferInstance, inferInstance, ‹_›, hc, inferInstance, inferInstance, inferInstance,
    hcomp, hfin, fun a b h => hinj (congrArg Subtype.val h), hloc,
    fun x hx => ⟨⟨x, hcl x hx⟩, rfl⟩, ?_⟩
  intro A _ Q hP
  exact _root_.GlobalTheory.SS.potModel_trans V K W L hcomp hfin hloc A _
    (pullback.fst _ _) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A _) Q hP

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoverModelIrreducibleSpecialFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_model_irreducible_specialFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (M : Model R A), ∃ (n : ℕ) (N : Fin n → Model R A) (g : ∀ i, (N i).Y ⟶ M.Y), (∀ i, (N i).Irr ∧ IsOpenImmersion (g i).left ∧ (N i).j ≫ (g i).left = M.j) ∧ ∀ y ∈ M.sp, ∃ i, y ∈ Set.range (g i).left := by
  first | exact @GlobalTheory.SS.IrrSplit.exists_cover_irr | exact GlobalTheory.SS.IrrSplit.exists_cover_irr | (intros; apply GlobalTheory.SS.IrrSplit.exists_cover_irr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorusStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_oneParameter_quotient_torus : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → ∃ j : Gm (Sp k) ⟶ G, IsMonHom j ∧ j ≫ q = f := by
  first | exact @GlobalTheory.SS.exists_lift_oneParameter | exact GlobalTheory.SS.exists_lift_oneParameter | (intros; apply GlobalTheory.SS.exists_lift_oneParameter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowSectionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_section' : ∀ (X X' : Scheme.{0}) (β : X' ⟶ X) [IsClosedImmersion β] [Surjective β] [CompactSpace X] [QuasiSeparatedSpace X], (∀ (W : X.Opens) (x y : Γ(X, W)), (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0) → ∀ H : LB X, H.IsLB → ∀ (s₀ : LB.Sec (H.pull β)) (D : X.Opens), β ⁻¹ᵁ D = nonzeroLocus s₀ → ∀ t : SecOn H D, SecOn.pull H β D t = GlobalTheory.LB.ofSec s₀ (β ⁻¹ᵁ D) → ∃ n : ℕ, 1 ≤ n ∧ ∃ σ : LB.Sec (pw H n), nonzeroLocus σ = D := by
  first | exact @GlobalTheory.SecPow.exists_pow_section | exact GlobalTheory.SecPow.exists_pow_section | (intros; apply GlobalTheory.SecPow.exists_pow_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormalStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.existsUnique_rigidified_generator_extend_normal : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], IsNormalScheme S → ∀ (U H HU X : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  first | exact @GlobalTheory.GenExtendNormal.existsUnique_gen_extend | exact GlobalTheory.GenExtendNormal.existsUnique_gen_extend | (intros; apply GlobalTheory.GenExtendNormal.existsUnique_gen_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeModelFiniteRingExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupScheme_model_finite_ring_extension : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (V' : Type) [CommRing V'] [IsDomain V'] [Algebra V V'] [Algebra V' K'] [IsFractionRing V' K'], (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) → ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) → ∀ (V'' : Type) [CommRing V''] [IsDomain V''] [Algebra V' V''], Module.Finite V' V'' → Function.Injective (algebraMap V' V'') → ∃ (_ : Algebra K (FractionRing V'')) (_ : FiniteDimensional K (FractionRing V'')), (algebraMap V'' (FractionRing V'')).comp ((algebraMap V' V'').comp (algebraMap V V')) = (algebraMap K (FractionRing V'')).comp (algebraMap V K) ∧ ∃ e : baseChange V'' (FractionRing V'') (baseChange V' V'' G) ≅ baseChange K (FractionRing V'') A, IsMonHom e.hom := by
  first | exact @GlobalTheory.SS.model_finite_ext | exact GlobalTheory.SS.model_finite_ext | (intros; apply GlobalTheory.SS.model_finite_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSmoothAtOfSmoothModIdealPowers
section
namespace GlobalTheory.SmoothAdic

open TensorProduct IsLocalRing

theorem isSmoothAt_of_smooth_quotient_pow : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra.FiniteType R C], (∀ e : ℕ, Algebra.Smooth (R ⧸ I ^ (e + 1)) (TensorProduct R (R ⧸ I ^ (e + 1)) C)) → ∀ (q : Ideal C) [q.IsPrime], q.comap (algebraMap R C) = IsLocalRing.maximalIdeal R → Algebra.IsSmoothAt R q := by
  intro R _ _ _ I hI C _ _ _ h q _ hq
  refine GlobalTheory.SmoothLimit.isSmoothAt_of_smooth_quotient_pow (V := R) (A := C) (fun e => ?_) q hq
  have hle : I ^ (e + 1) ≤ maximalIdeal R ^ (e + 1) :=
    Ideal.pow_right_mono (le_maximalIdeal hI) (e + 1)
  let _ : Algebra (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1)) :=
    (Ideal.Quotient.factor hle).toAlgebra
  have : IsScalarTower R (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := h e
  exact Algebra.Smooth.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (R ⧸ I ^ (e + 1)) (R ⧸ maximalIdeal R ^ (e + 1))
      (R ⧸ maximalIdeal R ^ (e + 1)) C)

end GlobalTheory.SmoothAdic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulEqZeroOfAppEqZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.SquareZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open TopologicalSpace in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero : ∀ (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X X' : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (β : X' ⟶ X),
    IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : X.Opens) (x y : Γ(X, W)),
    (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0 := by
  intro A A' _ _ g hg hsq X X' f f' β hpb W x y hx hy
  apply TopCat.Presheaf.section_ext X.sheaf W (x * y) 0
  intro p hp
  obtain ⟨V, hVaff, hpV, hVW⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hp
  have hres : ∀ z : Γ(X, W), (β.app W).hom z = 0 →
      _root_.GlobalTheory.AbLaw.rs X hVW z ∈
        Ideal.map (_root_.GlobalTheory.SmallExtLift.cst f V) (RingHom.ker g) := fun z hz =>
    _root_.GlobalTheory.SmallExtLift.mem_of_app_eq_zero hg hpb hVaff _
      (by rw [_root_.GlobalTheory.SectionKernel.app_rs, hz, map_zero])
  have hzero : _root_.GlobalTheory.AbLaw.rs X hVW (x * y) = 0 := by
    rw [map_mul]
    have hmem := Ideal.mul_mem_mul (hres x hx) (hres y hy)
    rw [← Ideal.map_mul, ← pow_two, hsq, Ideal.map_bot, Ideal.mem_bot] at hmem
    exact hmem
  have h1 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) p hpV (x * y)
  have h2 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) p hpV 0
  change X.presheaf.germ W p hp (x * y) = X.presheaf.germ W p hp 0
  rw [← h1, ← h2, map_zero]
  exact congrArg _ hzero

end GlobalTheory.SquareZero
end

