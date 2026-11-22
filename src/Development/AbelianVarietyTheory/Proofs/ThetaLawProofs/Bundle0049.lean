import Mathlib
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0044
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0047

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedKeyInvariantRuleCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyNormRule

def HasValue (g n : ℕ) (ka : KeyIn ℂ → ℂˣ) (a₀ : ℂ) : Prop :=
  ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c₀ : ℂ), x.P.g = g →
    charHalf x.P.g a b → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx a b c₀ →
    (ka x : ℂ) = a₀ * (Mx.det ^ 4 / c₀ ^ 8) ^ n

theorem dim_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : x'.P.g = x.P.g := by
  obtain ⟨_, _, _, hg, -⟩ := h
  exact hg

theorem HasValue.holo {g n : ℕ} {ka : KeyIn ℂ → ℂˣ} {a₀ : ℂ} (h : HasValue g n ka a₀) (a b : Fin g → ℂ)
    (hab : charHalf g a b) : ∃ U : Matrix (Fin g) (Fin g) ℂ → ℂ, Key.IsHoloSiegel g U ∧
      ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) :=
  ⟨fun _ => a₀, differentiableOn_const _, fun x hx τ hn => by
    simpa using h x τ 1 _ _ 1 hx ⟨fun i => hab.1 _, fun i => hab.2 _⟩ one_ne_zero (by simp) hn⟩

theorem exists_rule_sq (hinv : Key.Chi.InversionStatement) {g c M : ℕ}
    {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK (2 * g) c M ka) {a₀ : ℂ}
    (ha : ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₀ : ℂ), x.P.g = 2 * g → c₀ ≠ 0 → Mx.det ≠ 0 →
      NormalAt x τ Mx 0 0 c₀ → (ka ℂ x : ℂ) = a₀ * (Mx.det ^ 4 / c₀ ^ 8) ^ c) :
    ∃ kb, KaRuleK g (2 * c) M kb ∧ HasValue g (2 * c) (kb ℂ) a₀ := by
  obtain ⟨hH, hF, hU, -⟩ := hka
  have hex : ∀ (R : Type) [CommRing R] (x : KeyIn R), ∃ y, IsKeyPow y x 2 :=
    fun R _ x => exists_isKeyPow R x 2 (by norm_num)
  choose sq hsq using hex
  have hdim : ∀ {R : Type} [CommRing R] {x y : KeyIn R}, x.P.g = g → IsKeyPow y x 2 → y.P.g = 2 * g :=
    fun hx hy => hx ▸ hy.dim_eq
  have indep : ∀ (K : Type) [Field K] [CharZero K] (x y : KeyIn K), x.P.g = g → IsKeyPow y x 2 →
      (ka K (sq K x) : K) = ka K y := fun K _ _ x y hx hy =>
    hF K K (RingHom.id K) y (sq K x) (hdim hx hy)
      (keyPB_of_isKeyPow K K (RingHom.id K) x y x (sq K x) 2 (GlobalTheory.keyPB_id K x) hy (hsq K x))
  have hval : HasValue g (2 * c) (fun x => ka ℂ (sq ℂ x)) a₀ := by
    intro x τ Mx a b c₀ hx hab hc hM hn₀
    obtain ⟨n, rfl⟩ := exists_int_half hab.1
    obtain ⟨n', rfl⟩ := exists_int_half hab.2
    have hy := hsq ℂ x
    obtain ⟨e, τ', M', hd, hn⟩ :=
      normalAt_pow x _ 2 τ Mx (fun i => (n i : ℝ) / 2) (fun i => (n' i : ℝ) / 2) c₀ hy hn₀
    obtain ⟨sp, hsp, hlaw⟩ := exists_thetaLaw_zero_of_even hinv _ _ _ (even_dot_double e n n')
    obtain ⟨M'', c', hc', hq, hn'⟩ := GlobalTheory.SpMove.normalAt_spAct (sq ℂ x) τ' M' (c₀ ^ 2) sp _ _ 0 0 hsp hlaw
      (pow_ne_zero _ hc) (by simpa using hn)
    have hq' : M''.det ^ 4 / c' ^ 8 = (Mx.det ^ 4 / c₀ ^ 8) ^ 2 := by rw [hq, hd]; ring
    have hM'' : M''.det ≠ 0 := fun h => by
      rw [h] at hq'
      exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 4 hM) (pow_ne_zero 8 hc)) (by rw [← hq']; simp)
    have := ha (sq ℂ x) _ M'' c' (hdim hx hy) hc' hM'' (by simpa [Pi.zero_def] using hn')
    rw [hq', ← pow_mul] at this
    exact this
  refine ⟨fun K _ _ x => ka K (sq K x), ⟨?_, ?_, ?_, hval.holo⟩, hval⟩
  · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a Mx hP h₁ h₂
    have hy := hsq K ⟨P, hg, rig, hr, th, hth, v, hv⟩
    obtain ⟨t, ht, w, hw, M', hp, ht', hw', hd⟩ :=
      GlobalTheory.PowChange.isKeyPow_change K P hg rig hr th hth v hv th' hth' v' hv' a Mx 2 _ h₁ h₂ hy
    have key := hH K _ (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).g_pos _
      (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).rig_gen _ (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).th_ne _
      (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).basis t ht w hw (a ^ 2) M' (hdim hP hy) ht' hw'
    dsimp only
    rw [indep K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ _ hP hp]
    rw [hd, ← pow_mul, ← pow_mul] at key
    rw [show 8 * (2 * c) = 2 * (8 * c) by ring, show 4 * (2 * c) = 2 * (4 * c) by ring]
    exact key
  · intro K K' _ _ _ _ f x x' hx h
    exact hF K K' f _ _ (hdim hx (hsq K x)) (keyPB_of_isKeyPow K K' f x _ x' _ 2 h (hsq K x) (hsq K' x'))
  · intro R K _ _ _ _ _ _ _ x xK hx hM h
    obtain ⟨u, hu, hu'⟩ := hU R K (sq R x) (sq K xK) (hdim hx (hsq R x)) hM
      (keyPB_of_isKeyPow R K _ x _ xK _ 2 h (hsq R x) (hsq K xK))
    exact ⟨u, hu, fun k _ _ r xk hr hk =>
      hu' k r (sq k xk) hr (keyPB_of_isKeyPow R k r x _ xk _ 2 hk (hsq R x) (hsq k xk))⟩

theorem exists_test (hT : ThetaUnifAV) {g n : ℕ} (hg : 1 ≤ g) {ka : KeyIn ℂ → ℂˣ} {a₀ : ℂ} (h : HasValue g n ka a₀)
    {S : Type} [CommRing S] (W : WeierstrassCurve S) [W.IsElliptic] (s : S →+* ℂ) :
    ∃ (y : KeyIn S) (z : KeyIn ℂ), y.P.g = g ∧ KeyPB z y s ∧ (ka z : ℂ) = a₀ * s W.Δ ^ (g * n) := by
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.T.exists_ellipticKeyData_value_eq_discriminant hT S W
  obtain ⟨y, hy⟩ := exists_isKeyPow S x g hg
  obtain ⟨x', hx'⟩ := exists_keyPB_ring x s
  obtain ⟨z, hz⟩ := exists_isKeyPow ℂ x' g hg
  obtain ⟨⟨τ, Mx, a, b, c, hab, hc, hM, hn₀⟩, -⟩ := GlobalTheory.KeyNormalExists.exists_normalAt hT x'
  have hΔ := hxv s x' τ Mx a b c hx' hab hc hn₀
  obtain ⟨m, rfl⟩ := exists_int_half hab.1
  obtain ⟨m', rfl⟩ := exists_int_half hab.2
  obtain ⟨e, τ', M', hd, hn⟩ :=
    normalAt_pow x' z g τ Mx (fun i => (m i : ℝ) / 2) (fun i => (m' i : ℝ) / 2) c hz hn₀
  refine ⟨y, z, by rw [hy.dim_eq, hx, Nat.mul_one], keyPB_of_isKeyPow S ℂ s x y x' z g hx' hy hz, ?_⟩
  rw [h z τ' M' _ _ _ (by rw [hz.dim_eq, dim_of_keyPB hx', hx, Nat.mul_one]) ⟨fun i => hab.1 _, fun i => hab.2 _⟩
    (pow_ne_zero _ hc) (by rw [hd]; exact pow_ne_zero _ hM) hn, ← hΔ, hd, pow_mul]
  congr 2
  ring

theorem const_rat_unit (hT : ThetaUnifAV) {g n M : ℕ} (hg : 1 ≤ g)
    {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK g n M ka) {a₀ : ℂ}
    (h : HasValue g n (ka ℂ) a₀) (W : WeierstrassCurve ℤ) (hW : W.Δ ≠ 0) :
    ∃ r : ℚ, r ≠ 0 ∧ (r : ℂ) = a₀ ∧ ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
      [CharZero K] [Algebra R K] [IsFractionRing R K], IsUnit (M : R) → IsUnit (W.Δ : R) →
      ∃ w : Rˣ, algebraMap R K w = (r : K) := by
  obtain ⟨-, hF, hU, -⟩ := hka
  let S := Localization.Away W.Δ
  have hext : ∀ {T : Type} [CommRing T] (f f' : S →+* T), f = f' := fun f f' =>
    IsLocalization.ringHom_ext (Submonoid.powers W.Δ) (RingHom.ext_int _ _)
  have hlift : ∀ {T : Type} [CommRing T], IsUnit (W.Δ : T) → Nonempty (S →+* T) := fun {T} _ hu =>
    ⟨IsLocalization.Away.lift (g := Int.castRingHom T) W.Δ hu⟩
  haveI : (W.map (algebraMap ℤ S)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ]; exact IsLocalization.Away.algebraMap_isUnit W.Δ⟩
  have hQ : (W.Δ : ℚ) ≠ 0 := Int.cast_ne_zero.2 hW
  obtain ⟨i⟩ := hlift (T := ℚ) hQ.isUnit
  obtain ⟨y, z, hy, hz, hv⟩ := exists_test hT hg h (W.map (algebraMap ℤ S)) ((Rat.castHom ℂ).comp i)
  obtain ⟨yQ, hyQ⟩ := exists_keyPB_ring y i
  have hyQg : yQ.P.g = g := (dim_of_keyPB hyQ).trans hy
  rw [hF ℚ ℂ (Rat.castHom ℂ) yQ z hyQg (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yQ z _ _ hyQ hz),
    WeierstrassCurve.map_Δ, eq_intCast (algebraMap ℤ S), map_intCast, eq_ratCast] at hv
  have hC : (W.Δ : ℂ) ≠ 0 := Int.cast_ne_zero.2 hW
  refine ⟨(ka ℚ yQ : ℚ) / (W.Δ : ℚ) ^ (g * n), div_ne_zero (Units.ne_zero _) (pow_ne_zero _ hQ), ?_, ?_⟩
  · push_cast
    rw [hv, mul_div_cancel_right₀ _ (pow_ne_zero _ hC)]
  · intro R K _ _ _ _ _ _ _ hM hΔ
    obtain ⟨j⟩ := hlift hΔ
    obtain ⟨yR, hyR⟩ := exists_keyPB_ring y j
    obtain ⟨yK, hyK⟩ := exists_keyPB_ring yQ (Rat.castHom K)
    have hyK' := GlobalTheory.keyPB_trans _ _ _ y yQ yK _ _ hyQ hyK
    rw [hext ((Rat.castHom K).comp i) ((algebraMap R K).comp j)] at hyK'
    obtain ⟨u, hu, -⟩ := hU R K yR yK ((dim_of_keyPB hyR).trans hy) hM
      (GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yR yK _ _ hyR hyK')
    rw [hF ℚ K _ yQ yK hyQg hyK, eq_ratCast] at hu
    have hK : (W.Δ : K) ≠ 0 := Int.cast_ne_zero.2 hW
    refine ⟨u * hΔ.unit⁻¹ ^ (g * n), ?_⟩
    have e : algebraMap R K (hΔ.unit⁻¹ : Rˣ) = (W.Δ : K)⁻¹ := by
      rw [map_units_inv, IsUnit.unit_spec, map_intCast]
    rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, e, ← hu, Rat.cast_div, Rat.cast_pow,
      Rat.cast_intCast, inv_pow, div_eq_mul_inv]

theorem rule_div {g n M : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hka : KaRuleK g n M ka)
    {r : ℚ} (hr : r ≠ 0) (h : HasValue g n (ka ℂ) r)
    (hu : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
      [CharZero K] [Algebra R K] [IsFractionRing R K], IsUnit (M : R) → ∃ w : Rˣ, algebraMap R K w = (r : K)) :
    ∃ κ, KaRuleK g n M κ ∧ HasValue g n (κ ℂ) 1 := by
  obtain ⟨hH, hF, hU, -⟩ := hka
  let κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ :=
    fun K _ _ x => ka K x * (Units.mk0 (r : K) (Rat.cast_ne_zero.2 hr))⁻¹
  have hκ : ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), (κ K x : K) = ka K x * (r : K)⁻¹ :=
    fun K _ _ x => by simp [κ]
  have hval : HasValue g n (κ ℂ) 1 := fun x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅ => by
    have : (r : ℂ) ≠ 0 := Rat.cast_ne_zero.2 hr
    rw [hκ, h x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅]
    field_simp
  refine ⟨κ, ⟨?_, ?_, ?_, hval.holo⟩, hval⟩
  · intro K _ _ P hg rig hrig th hth v hv th' hth' v' hv' a Mx hP h₁ h₂
    rw [hκ, hκ, ← _root_.mul_assoc, ← _root_.mul_assoc,
      hH K P hg rig hrig th hth v hv th' hth' v' hv' a Mx hP h₁ h₂]
  · intro K K' _ _ _ _ f x x' hx hp
    rw [hκ, hκ, hF K K' f x x' hx hp, map_mul, map_inv₀, map_ratCast]
  · intro R K _ _ _ _ _ _ _ x xK hx hM hp
    obtain ⟨u, hu₁, hu₂⟩ := hU R K x xK hx hM hp
    obtain ⟨w, hw⟩ := hu R K hM
    have hw' : (w : R) * (r.den : R) = (r.num : R) := IsFractionRing.injective R K (by
      rw [map_mul, hw, map_natCast, map_intCast]
      exact_mod_cast Rat.mul_den_eq_num r)
    refine ⟨u * w⁻¹, ?_, fun k _ _ ρ xk hρ hk => ?_⟩
    · rw [hκ, hu₁, Units.val_mul, map_mul, map_units_inv, hw]
    · have e : ρ w = (r : k) := by
        have := congrArg ρ hw'
        rw [map_mul, map_natCast, map_intCast] at this
        rw [Rat.cast_def, eq_div_iff (Nat.cast_ne_zero.2 r.den_ne_zero), this]
      rw [hκ, hu₂ k ρ xk hρ hk, Units.val_mul, map_mul, map_units_inv, e]

theorem exists_normalised_rule : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → ∀ (g c M : ℕ), 1 ≤ g → KaRule (2 * g) c M → ∃ κ, KaRuleK g (2 * c) M κ ∧ ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c₀ : ℂ), x.P.g = g → charHalf x.P.g a b → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx a b c₀ → (κ ℂ x : ℂ) = (Mx.det ^ 4 / c₀ ^ 8) ^ (2 * c) := by
  intro hL hT hinv hP hA g c M hg hR
  obtain ⟨ka, hka⟩ := GlobalTheory.KeyGalDesc.exists_kaRuleK hL.polBaseChange _ _ _ hR
  obtain ⟨a₀, ha⟩ := GlobalTheory.KeyConst.exists_const hT hinv hP hA _ c M ka (by omega) hka
  obtain ⟨kb, hkb, hv⟩ := exists_rule_sq hinv hka ha
  obtain ⟨r, hr, rfl, h₃⟩ := const_rat_unit hT hg hkb hv (WeierstrassCurve.ofJ0 ℤ)
    (by rw [WeierstrassCurve.ofJ0_Δ]; norm_num)
  obtain ⟨r', -, e, h₂⟩ := const_rat_unit hT hg hkb hv (WeierstrassCurve.ofJ1728 ℤ)
    (by rw [WeierstrassCurve.ofJ1728_Δ]; norm_num)
  obtain rfl : r' = r := Rat.cast_injective e
  obtain ⟨κ, hκ, hκv⟩ := rule_div hkb hr hv fun R K _ _ _ _ _ _ _ hM => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (3 : R) with h | h
    · refine h₃ R K hM ?_
      rw [WeierstrassCurve.ofJ0_Δ]
      convert (h.pow 3).neg using 1
      norm_num
    · refine h₂ R K hM ?_
      rw [WeierstrassCurve.ofJ1728_Δ]
      convert (h.pow 6).neg using 1
      norm_num
  exact ⟨κ, hκ, fun x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅ => by
    rw [hκv x τ Mx a b c₀ h₁ h₂ h₃ h₄ h₅, _root_.one_mul]⟩

end GlobalTheory.KeyNormRule
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralOfEtaleFaithfullyFlatCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_point_over_of_idempotent {F A B : Type} [Field F] [IsAlgClosed F] [CommRing A]
    [CommRing B] [Algebra F A] [Algebra F B] [IsNoetherianRing A] (f : A →ₐ[F] B)
    (hfin : f.toRingHom.Finite) (hflat : f.toRingHom.Flat) (P : B →ₐ[F] F) (Q : A →ₐ[F] F)
    (h : ∀ e : A, IsIdempotentElem e → P (f e) = Q e) (E : B) (hE : IsIdempotentElem E)
    (hP : P E = 1) : ∃ Q' : B →ₐ[F] F, Q' E = 1 ∧ ∀ a, Q' (f a) = Q a := by
  algebraize [f.toRingHom]
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hcl : IsClopen (PrimeSpectrum.basicOpen E : Set (PrimeSpectrum B)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨E, hE, rfl⟩
  have him : IsClopen (PrimeSpectrum.comap (algebraMap A B) ''
      (PrimeSpectrum.basicOpen E : Set (PrimeSpectrum B))) :=
    ⟨PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (Algebra.IsIntegral.isIntegral) _ hcl.1,
      PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _ hcl.2⟩
  obtain ⟨ε, hε, hεe⟩ := PrimeSpectrum.isClopen_iff.1 him
  have h1 : PrimeSpectrum.comap (algebraMap A B) ⟨RingHom.ker P, RingHom.ker_isPrime P⟩ ∈
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum A)) := by
    rw [← hεe]
    refine ⟨_, ?_, rfl⟩
    change ¬ (P E = 0)
    rw [hP]; exact one_ne_zero
  have h2 : (⟨RingHom.ker Q, RingHom.ker_isPrime Q⟩ : PrimeSpectrum A) ∈
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum A)) := by
    change ¬ (Q ε = 0)
    rw [← h ε hε]
    exact h1
  rw [← hεe] at h2
  obtain ⟨𝔮, h𝔮E, h𝔮⟩ := h2
  have hker : ∀ a : A, Q a = 0 → f a ∈ 𝔮.asIdeal := by
    intro a ha
    have : a ∈ (PrimeSpectrum.comap (algebraMap A B) 𝔮).asIdeal := by
      rw [h𝔮]; exact ha
    exact this
  have hcomp : ∀ a : A, Ideal.Quotient.mk 𝔮.asIdeal (f a) =
      algebraMap F (B ⧸ 𝔮.asIdeal) (Q a) := by
    intro a
    have := hker (a - algebraMap F A (Q a)) (by simp)
    rw [map_sub, AlgHom.commutes] at this
    exact Ideal.Quotient.eq.2 this
  have hint : (algebraMap F (B ⧸ 𝔮.asIdeal)).IsIntegral := by
    apply RingHom.IsIntegral.tower_top Q.toRingHom
    have : (algebraMap F (B ⧸ 𝔮.asIdeal)).comp Q.toRingHom =
        (Ideal.Quotient.mk 𝔮.asIdeal).comp f.toRingHom := by
      ext a; exact (hcomp a).symm
    rw [this]
    exact RingHom.IsIntegral.trans _ _ hfin.to_isIntegral
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  haveI : Algebra.IsIntegral F (B ⧸ 𝔮.asIdeal) := ⟨hint⟩
  have hbij : Function.Bijective (Algebra.ofId F (B ⧸ 𝔮.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ := (AlgEquiv.ofBijective _ hbij).symm
  refine ⟨φ.toAlgHom.comp (Ideal.Quotient.mkₐ F 𝔮.asIdeal), ?_, fun a => ?_⟩
  · rcases IsIdempotentElem.iff_eq_zero_or_one.1
      (hE.map (φ.toAlgHom.comp (Ideal.Quotient.mkₐ F 𝔮.asIdeal))) with h0 | h0
    · exfalso
      apply h𝔮E
      have : Ideal.Quotient.mk 𝔮.asIdeal E = 0 := φ.injective (by rw [map_zero]; exact h0)
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    · exact h0
  · change φ (Ideal.Quotient.mk 𝔮.asIdeal (f a)) = _
    rw [hcomp, AlgEquiv.commutes]; rfl

theorem exists_algHom_baseChange_away {k₀ k B L : Type} [Field k₀] [Field k] [Algebra k₀ k]
    [CommRing B] [Algebra k₀ B] [CommRing L] [Algebra k₀ L] [Algebra k L] [IsScalarTower k₀ k L]
    (e : B) (G : B →ₐ[k₀] L) (hG : G e = 1) :
    ∃ s : k ⊗[k₀] Localization.Away e →ₐ[k] L,
      ∀ b, s (1 ⊗ₜ algebraMap B (Localization.Away e) b) = G b := by
  have hu : ∀ y : Submonoid.powers e, IsUnit (G y) := by
    rintro ⟨_, n, rfl⟩
    simp [hG]
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId k L)
    (IsLocalization.liftAlgHom (S := Localization.Away e) hu) (fun _ _ => Commute.all _ _),
    fun b => ?_⟩
  simp

theorem exists_finset_integral_of_finiteType {K T L : Type} [Field K] [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] [CommRing L] [Algebra K L] (g : T →ₐ[K] L)
    (hg : ∀ x, IsIntegral K (g x)) :
    ∃ s : Set L, s.Finite ∧ (∀ y ∈ s, IsIntegral K y) ∧
      ∀ U : Subalgebra K L, s ⊆ U → ∀ x, g x ∈ U := by
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := K) (A := T)
  refine ⟨g '' t, t.finite_toSet.image _, ?_, fun U hU x => ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact hg x
  · have : Algebra.adjoin K (t : Set T) ≤ U.comap g :=
      Algebra.adjoin_le fun y hy => hU ⟨y, hy, rfl⟩
    rw [ht] at this
    exact this Algebra.mem_top

theorem finite_flat_tensor_map (K F R R₁ : Type) [CommRing K] [CommRing F] [Algebra K F]
    [CommRing R] [Algebra K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁]
    [Module.Finite R R₁] [Module.Flat R R₁] :
    (Algebra.TensorProduct.map (AlgHom.id F F) (IsScalarTower.toAlgHom K R R₁)).toRingHom.Finite ∧
    (Algebra.TensorProduct.map (AlgHom.id F F) (IsScalarTower.toAlgHom K R R₁)).toRingHom.Flat := by
  constructor
  · exact RingHom.Finite.tensorProductMap (f := AlgHom.id K F) (RingHom.Finite.id F)
      (g := IsScalarTower.toAlgHom K R R₁) (RingHom.finite_algebraMap.2 inferInstance)
  · exact RingHom.Flat.tensorProductMap (f := AlgHom.id F F)
      (g := IsScalarTower.toAlgHom K R R₁) (RingHom.Flat.id F)
      (RingHom.flat_algebraMap_iff.2 inferInstance)

theorem exists_geomInt_piece_of_finite_etale : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R R₁ : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁] (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (σ₁ : K₁ →ₐ[K] ℂ) (p : R₁ →ₐ[K] ℂ) (q : R →ₐ[K] K₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) → (∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _) e) → ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S) (j : R₁ →+* S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (ii : K₁ →+* k), GeomInt k S ∧ s.comp j = p.toRingHom ∧ (s₀.toRingHom.comp j).comp (algebraMap R R₁) = ii.comp q.toRingHom := by
  intro K _ _ _ R R₁ _ _ _ _ _ _ _ K₁ _ _ _ σ₁ p q ⟨hfin, het, hff⟩ hidem
  haveI : Algebra.Smooth K R₁ := Algebra.Smooth.comp K R R₁
  obtain ⟨k₀, e, hk₀, he, hpe, hgi⟩ := GlobalTheory.T.exists_finite_ext_geom_integral_localization K R₁ p
  haveI : IsNoetherianRing (ℂ ⊗[K] R) := Algebra.FiniteType.isNoetherianRing ℂ _
  let f : ℂ ⊗[K] R →ₐ[ℂ] ℂ ⊗[K] R₁ :=
    Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (IsScalarTower.toAlgHom K R R₁)
  obtain ⟨hf1, hf2⟩ : f.toRingHom.Finite ∧ f.toRingHom.Flat := finite_flat_tensor_map K ℂ R R₁
  let emb : k₀ ⊗[K] R₁ →ₐ[K] ℂ ⊗[K] R₁ := Algebra.TensorProduct.map k₀.val (AlgHom.id K R₁)
  let P : ℂ ⊗[K] R₁ →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _)
  have hPemb : ∀ x, P (emb x) = Algebra.TensorProduct.lift k₀.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [P, emb]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hPf : ∀ x, P (f x) = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ)
      (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [P, f]
    | add a b ha hb => simp only [map_add, ha, hb]
  obtain ⟨Q', hQE, hQ⟩ := exists_point_over_of_idempotent f hf1 hf2 P
    (Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _))
    (fun x hx => (hPf x).trans (hidem x hx)) (emb e) (he.map emb) ((hPemb e).trans hpe)
  let q' : R₁ →ₐ[K] ℂ := (Q'.restrictScalars K).comp Algebra.TensorProduct.includeRight
  have hq' : ∀ r, q' (algebraMap R R₁ r) = σ₁ (q r) := by
    intro r
    have := hQ (1 ⊗ₜ r)
    simpa [f, q'] using this
  have hq'int : ∀ x, IsIntegral K (q' x) := by
    intro x
    letI : Algebra K₁ ℂ := σ₁.toRingHom.toAlgebra
    haveI : IsScalarTower K K₁ ℂ := IsScalarTower.of_algebraMap_eq fun a => (σ₁.commutes a).symm
    have h1 : IsIntegral K₁ (q' x) :=
      (Algebra.IsIntegral.isIntegral (R := R) x).map_of_comp_eq q.toRingHom q'.toRingHom
        (RingHom.ext fun r => (hq' r).symm)
    exact isIntegral_trans _ h1
  obtain ⟨s₁, hs₁, hs₁i, hs₁U⟩ := exists_finset_integral_of_finiteType q' hq'int
  obtain ⟨s₂, hs₂, hs₂i, hs₂U⟩ := exists_finset_integral_of_finiteType σ₁
    (fun x => (Algebra.IsIntegral.isIntegral (R := K) x).map σ₁)
  let k : IntermediateField k₀ ℂ := IntermediateField.adjoin k₀ (s₁ ∪ s₂)
  haveI : Finite ↥(s₁ ∪ s₂) := (hs₁.union hs₂).to_subtype
  haveI : FiniteDimensional k₀ k := IntermediateField.finiteDimensional_adjoin (by
    rintro x (hx | hx)
    · exact (hs₁i x hx).tower_top
    · exact (hs₂i x hx).tower_top)
  haveI : NumberField k₀ := NumberField.of_module_finite K k₀
  haveI : NumberField k := NumberField.of_module_finite k₀ k
  have hm₁ : ∀ x, q' x ∈ k := hs₁U (k.toSubalgebra.restrictScalars K)
    (fun y hy => IntermediateField.subset_adjoin k₀ (s₁ ∪ s₂) (Or.inl hy))
  have hm₂ : ∀ x, σ₁ x ∈ k := hs₂U (k.toSubalgebra.restrictScalars K)
    (fun y hy => IntermediateField.subset_adjoin k₀ (s₁ ∪ s₂) (Or.inr hy))
  let qk : R₁ →ₐ[K] k :=
    { toRingHom := q'.toRingHom.codRestrict k hm₁
      commutes' := fun a => Subtype.ext (q'.commutes a) }
  let G : k₀ ⊗[K] R₁ →ₐ[k₀] ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId k₀ ℂ) p (fun _ _ => Commute.all _ _)
  let G₀ : k₀ ⊗[K] R₁ →ₐ[k₀] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k₀ k) qk (fun _ _ => Commute.all _ _)
  have hG : ∀ x, G x = Algebra.TensorProduct.lift k₀.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hG₀ : ∀ x, (G₀ x : ℂ) = Q' (emb x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have : emb (a ⊗ₜ b) = (a : ℂ) • ((1 : ℂ) ⊗ₜ[K] b) := by
        simp [emb, TensorProduct.smul_tmul']
      rw [this, map_smul, smul_eq_mul]
      rfl
    | add a b ha hb => simp only [map_add, ← ha, ← hb]; rfl
  obtain ⟨s, hs⟩ := exists_algHom_baseChange_away (k := k) e G ((hG e).trans hpe)
  obtain ⟨s₀, hs₀⟩ := exists_algHom_baseChange_away (k := k) e G₀
    (Subtype.ext ((hG₀ e).trans hQE))
  refine ⟨k, inferInstance, inferInstance, k ⊗[k₀] Localization.Away e, inferInstance,
    inferInstance,
    (Algebra.TensorProduct.includeRight (R := k₀) (A := k)).toRingHom.comp
      ((algebraMap (k₀ ⊗[K] R₁) (Localization.Away e)).comp
        (Algebra.TensorProduct.includeRight (R := K) (A := k₀)).toRingHom),
    s.toRingHom, s₀, σ₁.toRingHom.codRestrict k hm₂, (geomInt_baseChange_and_away k₀ k _ hgi).1, ?_, ?_⟩
  · ext x
    refine (hs (1 ⊗ₜ x)).trans ?_
    simp [G]
  · refine RingHom.ext fun x => ?_
    refine (hs₀ (1 ⊗ₜ algebraMap R R₁ x)).trans (Subtype.ext ?_)
    rw [hG₀]
    exact Eq.trans (by simp [emb, q']) (hq' x)

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SerreVanishingCubeTotalComplexExactAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.KeyKa

theorem secCube_tw_exactAt_of_veryAmpleBy : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ p, (cubeComplex (secCube f (tw M H t) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  intro R _ _ Y f H m s M hH hM hv
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hfin, hφ⟩ :=
    GlobalTheory.AbLaw.exists_finite_graded_module_secCube R Y f H m s M hH hM hv
  obtain ⟨n₀, hn⟩ := GlobalTheory.cubeComplex_grCube_exactAt_of_finite (Fin (m + 1)) R N 𝒩 hfin
  refine ⟨n₀, fun t ht p => ?_⟩
  have h01 := secCube_exactAt_zero_and_one R Y f (tw M H t) (Fin (m + 1))
    (fun i => Out.nonzeroLocus (s i)) hv.1
  match p with
  | 0 => exact h01.1
  | 1 => exact h01.2
  | p + 2 =>
    obtain ⟨φ, hb⟩ := hφ t
    have := isIso_cechComplexMap φ hb
    rw [← cechComplex_exactAt_succ_iff_cube]
    exact ((cechComplex_exactAt_succ_iff_cube _ p).2 (hn t ht (p + 2))).of_iso
      (asIso (cechComplexMap φ))

end GlobalTheory.KeyKa
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.VeryAmpleByDescendsCountableSubringStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.veryAmpleBy_descends_to_countable_subring : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Flat f] (H : LB X) (m : ℕ) (s : Fin (m + 1) → H.Sec) (S : Set R), H.IsLB → VeryAmpleBy f H s → S.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) (H₀ : LB X₀) (s₀ : Fin (m + 1) → H₀.Sec), Countable R₀ ∧ S ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ Module.FaithfullyFlat R₀ R ∧ IsPullback π f f₀ (spMap R₀.subtype) ∧ Flat f₀ ∧ H₀.IsLB ∧ VeryAmpleBy f₀ H₀ s₀ ∧ LBIso H (H₀.pull π) := by
  first | exact @GlobalTheory.veryAmpleBy_descends_countable_subring | exact GlobalTheory.veryAmpleBy_descends_countable_subring | (intros; apply GlobalTheory.veryAmpleBy_descends_countable_subring <;> assumption)
end

