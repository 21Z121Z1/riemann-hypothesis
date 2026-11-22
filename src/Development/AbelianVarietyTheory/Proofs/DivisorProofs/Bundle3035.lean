import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0149
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionPointCharacterEqWeilPairingLabel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section
namespace GlobalTheory.Poinc.Sep.Spz
open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem isPrimitiveRoot_map_of_isUnit_order {o K : Type} [CommRing o] [IsDomain o] [CommRing K] [IsDomain K] (φ : o →+* K)
    {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) : IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

theorem intCast_eq_of_zpow_eq {K : Type} [Field K] {m : ℕ} [NeZero m] {z : K} (hz : IsPrimitiveRoot z m) {a : ℤ}
    {b : ZMod m} (h : z ^ a = z ^ (b.val : ℤ)) : (a : ZMod m) = b := by
  have hz0 : z ≠ 0 := hz.ne_zero (NeZero.ne m)
  have h1 : z ^ (a - (b.val : ℤ)) = 1 := by rw [zpow_sub₀ hz0, h, div_self (zpow_ne_zero _ hz0)]
  have h2 := (hz.zpow_eq_one_iff_dvd _).1 h1
  have h3 : ((a - (b.val : ℤ) : ℤ) : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h2
  rw [Int.cast_sub, sub_eq_zero, Int.cast_natCast, ZMod.natCast_zmod_val] at h3
  exact h3

theorem torAt_char_eq_weil : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (c : 𝔪.D.toPre.X →+ ℤ) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), TorAt 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) c x → x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left → ∀ a mu, 𝔪.YY a mu → ((c (𝔪.e₈ mu) : ℤ) : ZMod (X₁.S.r * X₁.S.N)) = ((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a := by
  intro g n F W Z i X₁ z₁ act
  refine ⟨1, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 τ c x hT hxo a mu hY
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  obtain ⟨τ', q, hτv, hqy, hqt, hqx⟩ := hT
  obtain ⟨p', x', hp'y, hp'x, hx'o⟩ := hY
  have W₁ := weilQkIs_tor hG q p' hqy hqt
  have W₂ := (GlobalTheory.UT.weilQkIs_iff_weilIs hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk q p' x x' hqx hp'x (τ' (Multiplicative.ofAdd p'.y))).1 W₁
  have := X₁.ρ.P.isAb.comm
  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := (spMap_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := hy
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h
    (X₁.ρ.weil τ a (c₀ ^ (eStd X₁.S.g _ τ a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩
    (TFK (R := V) (AlgebraicClosure (FractionRing V))) _
    x x' (h ≫ X₁.ρ.pt τ) (h ≫ X₁.ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB W₂ W₃)
    rw [hp'y] at e
    have e' := congrArg Units.val e
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec] at e'
    rw [hτv] at e'
    rw [Units.val_one, one_smul]
    haveI : IsDomain X₁.o₁ := X₁.ar.ded.toIsDomain
    haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨by omega⟩
    have hzp := isPrimitiveRoot_map_of_isUnit_order ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (𝔪.yK.comp (algebraMap X₁.o₁ X₁.S.R))) (by omega) hζ X₁.S.unit
    refine intCast_eq_of_zpow_eq hzp ?_
    rw [zpow_natCast]
    simp only [RingHom.coe_comp, Function.comp_apply, map_pow] at e' ⊢
    exact e'
  · show h.left ≫ (X₁.ρ.pt τ).left = _
    rw [hh, hxo]
  · show h.left ≫ (X₁.ρ.pt a).left = _
    rw [hx'o, hh]

end GlobalTheory.Poinc.Sep.Spz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionPointOfTorusPointAtClosedPointField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem torAt_of_closedPoint : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (β : G.left ⟶ H.left), IsGrpPullback G H ξ β → ∀ (σ : Sp V ⟶ H.left), σ ≫ H.hom = ξ → ∀ (k : ℕ) (w : V), 1 ≤ k → IsUnit (k : V) → w ^ k = 1 → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (c : D.toPre.X →+ ℤ) (x : TFK (R := V) F ⟶ A.A), x ^ k = 1 → x.left ≫ genMap U ≫ β = spMap (algebraMap (FractionRing V) F) ≫ jK V ≫ σ → ∀ (κ : Type) [Field κ] (b : V →+* κ) (hb : ∀ y ∈ maximalIdeal V ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G.left) (hm : IsGrpPullback Gκ G (spMap b) m) (τ : Multiplicative D.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b w ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ σ = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb hm).left ≫ m ≫ β → TorAt U F k (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) c x := by
  intro B H _ V _ _ _ hV G _ _ hG D A U ξ β hβ σ hσ k w hk hkV hw F _ _ _ c x hx hxσ κ _ b hb Gκ _ m hm τ hτ z hz hbσ
  haveI : CharZero V := hV.2
  have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := Spec.map_id _
  let σ₀ : Sp V ⟶ G.left := hβ.1.lift σ (𝟙 _) (hσ.trans (Category.id_comp _).symm)
  have hσ₀ : σ₀ ≫ β = σ := hβ.1.lift_fst _ _ _
  have hσ₀' : σ₀ ≫ G.hom = 𝟙 _ := hβ.1.lift_snd _ _ _
  let σ₁ : Over.mk (spMap (RingHom.id V)) ⟶ G := Over.homMk σ₀ (hσ₀'.trans hid.symm)
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main V hV G hG D A U k hk
  have hwu : IsUnit w := IsUnit.of_pow_eq_one hw (by omega)
  obtain ⟨u, rfl⟩ := hwu
  have hu : u ^ k = 1 := Units.ext (by simpa using hw)
  let τV : Multiplicative D.toPre.X →* Vˣ := (zpowersHom Vˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hτV' : ∀ χ, τV χ = u ^ c (Multiplicative.toAdd χ) := fun χ => rfl
  have hτV : τV ^ k = 1 := MonoidHom.ext fun χ => by
    rw [MonoidHom.pow_apply, hτV', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]; rfl
  have hval : ∀ (L : Type) [Field L] (f : V →+* L) (n : ℤ), f ((u ^ n : Vˣ) : V) = f u ^ n := fun L _ f n => by
    have := congrArg Units.val (map_zpow (Units.map (f : V →* L)) u n)
    rw [Units.val_zpow_eq_zpow_val] at this
    exact this
  let a : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have ha : spMap a = spMap (algebraMap (FractionRing V) F) ≫ jK V := GlobalTheory.ToricTorsionSec.spMap_comp _ _
  have hainj : Function.Injective a :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hp₁ : IsGrpPullback A.A ((Over.pullback (jK V)).obj G) (𝟙 _) U.gen.inv.left :=
    isGrpPullback_of_iso U.gen.symm
  have hp₂ := isGrpPullback_pullback G (jK V)
  have hp : IsGrpPullback A.A G (jK V) (genMap U) := (hp₁.comp hp₂).congr (Category.id_comp _) rfl
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hp (TFK (R := V) F) (spMap a) ha
  let ρ : Over.mk (spMap a) ⟶ Over.mk (spMap (RingHom.id V)) :=
    Over.homMk (spMap a) (by show spMap a ≫ spMap (RingHom.id V) = spMap a; rw [hid, Category.comp_id])
  have hex : e x = ρ ≫ σ₁ := by
    refine Over.OverMorphism.ext (hβ.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [he]
    show (x.left ≫ genMap U) ≫ β = (spMap a ≫ σ₀) ≫ β
    rw [Category.assoc, Category.assoc, hσ₀, ha, hxσ, Category.assoc]
  haveI : IsSeparated G.hom := hG.separated
  haveI : IsDominant (spMap a) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hainj]; exact bot_le)⟩
  have hσ₁ : σ₁ ^ k = 1 := by
    have h1 : ρ ≫ σ₁ ^ k = ρ ≫ 1 := by
      rw [MonObj.comp_pow, ← hex, ← map_pow, hx, map_one, MonObj.comp_one]
    haveI : AlgebraicGeometry.IsReduced (Over.mk (spMap (RingHom.id V))).left :=
      inferInstanceAs (AlgebraicGeometry.IsReduced (Sp V))
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom
      ((Over.w _).trans (Over.w _).symm) (spMap a) ?_)
    exact congrArg (·.left) h1
  have hbl : IsLocalHom b := ⟨fun y hy => by
    by_contra hn
    rw [hb y (by simpa using (mem_maximalIdeal y).2 hn)] at hy
    exact not_isUnit_zero hy⟩
  have hτb : ∀ χ, (τ χ : κ) = b (τV χ : V) := fun χ => by
    rw [hτV', hval]; exact hτ (Multiplicative.toAdd χ)
  have hτk : τ ^ k = 1 := MonoidHom.ext fun χ => Units.ext (by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hτb, ← map_pow, ← Units.val_pow_eq_pow_val,
      ← MonoidHom.pow_apply, hτV]; simp)
  have hσs : σ₁ = s V (RingHom.id V) τV hτV := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp V) G hG.smooth V _ k hkV _ _ (by rw [hσ₁, s1]) κ b hbl ?_
    rw [← s2 V κ (RingHom.id V) b b τV hτV τ hτk rfl hτb,
      s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z rfl hz]
    refine hβ.1.hom_ext ?_ ?_
    · show (spMap b ≫ σ₀) ≫ β = _
      rw [Category.assoc, hσ₀, hbσ, Category.assoc]
    · show (spMap b ≫ σ₀) ≫ G.hom = _
      rw [Category.assoc, hσ₀', Category.comp_id,
        ← s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z rfl hz]
      exact (Over.w (s κ b τ hτk)).symm
  let τF : Multiplicative D.toPre.X →* Fˣ := (Units.map (a : V →* F)).comp τV
  have hτF : τF ^ k = 1 := MonoidHom.ext fun χ => by
    rw [MonoidHom.pow_apply]
    show Units.map (a : V →* F) (τV χ) ^ k = 1
    rw [← map_pow, ← MonoidHom.pow_apply, hτV, MonoidHom.one_apply, map_one]
  obtain ⟨q, hqy, hqt⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (k := k) τF hτF
  obtain ⟨f, ⟨i, -⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV.1 D A G hG U F k hk
  have hq := (i q _).2 rfl
  have hxq : x = f q := by
    apply e.injective
    refine Over.OverMorphism.ext ?_
    rw [he (f q), s4 F a τF hτF q (f q) rfl hqy hqt hq,
      s2 V F (RingHom.id V) a a τV hτV τF hτF rfl (fun χ => rfl), ← hσs, hex]
    rfl
  refine ⟨τF, q, fun χ => ?_, hqy, hqt, hxq ▸ hq⟩
  exact hval F a (c χ)

end GlobalTheory.Poinc.Sep.Spz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionSectionEqTorusPointAtClosedPointFiel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

theorem GlobalTheory.ToricTorsionClosedPt.main : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (β : G.left ⟶ H.left), IsGrpPullback G H ξ β → ∀ (σ : Sp V ⟶ H.left), σ ≫ H.hom = ξ → ∀ (k : ℕ) (w : V), 1 ≤ k → w ^ k = 1 → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (c : D.toPre.X →+ ℤ) (x : TFK (R := V) F ⟶ A.A), TorAt U F k (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) c x → x.left ≫ genMap U ≫ β = spMap (algebraMap (FractionRing V) F) ≫ jK V ≫ σ → ∀ (κ : Type) [Field κ] (b : V →+* κ) (hb : ∀ y ∈ maximalIdeal V ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G.left) (hm : IsGrpPullback Gκ G (spMap b) m) (τ : Multiplicative D.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b w ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ σ = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb hm).left ≫ m ≫ β := by
  intro B H _ V _ _ _ hV G _ _ hG D A U ξ β hβ σ hσ k w hk hw F _ _ _ c x hx hxσ κ _ b hb Gκ _ m hm τ hτ z hz
  have hk0 : k ≠ 0 := by omega
  let u : Vˣ := Units.ofPowEqOne w k hw hk0
  have hu : (u : V) = w := Units.val_ofPowEqOne w k hw hk0
  have huk : u ^ k = 1 := Units.pow_ofPowEqOne hw hk0
  let τV : Multiplicative D.toPre.X →* Vˣ := (zpowersHom Vˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hτVv : ∀ χ, τV χ = u ^ c (Multiplicative.toAdd χ) := fun χ => rfl
  have hτV : τV ^ k = 1 := MonoidHom.ext fun χ => by
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, hτVv, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, huk, one_zpow]
  have powk : ∀ {L : Type} [Field L] (t : Multiplicative D.toPre.X →* Lˣ) (y : L), y ^ k = 1 →
      (∀ χ, (t (Multiplicative.ofAdd χ) : L) = y ^ c χ) → t ^ k = 1 := by
    intro L _ t y hy ht
    refine MonoidHom.ext fun χ => Units.ext ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one,
      ← ofAdd_toAdd χ, ht, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have mapv : ∀ {L : Type} [Field L] (f : V →+* L) (χ : Multiplicative D.toPre.X),
      f (τV χ : V) = f w ^ c (Multiplicative.toAdd χ) := by
    intro L _ f χ
    rw [hτVv, ← hu]
    show ((Units.map (f : V →* L) (u ^ c (Multiplicative.toAdd χ)) : Lˣ) : L) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main V hV G hG D A U k hk
  let sV := s V (RingHom.id V) τV hτV
  let σ₁ : Sp V ⟶ G.left := hβ.1.lift σ (𝟙 _) (by rw [hσ, Category.id_comp])
  have hσ₁β : σ₁ ≫ β = σ := hβ.1.lift_fst _ _ _
  have hσ₁G : σ₁ ≫ G.hom = 𝟙 _ := hβ.1.lift_snd _ _ _
  have hsVG : sV.left ≫ G.hom = 𝟙 _ := by
    rw [Over.w sV]
    show Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
    exact Spec.map_id _

  let a : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have ha : spMap a = spMap (algebraMap (FractionRing V) F) ≫ jK V := by
    dsimp only [a, spMap, jK]
    rw [← Spec.map_comp]
    rfl
  have haI : Function.Injective a :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  haveI : IsDominant (spMap a) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 haI]; exact bot_le)⟩
  haveI : IsSeparated G.hom := hG.separated
  obtain ⟨τF, q, hτF, hq, hqt, hqx⟩ := hx
  have hτFk : τF ^ k = 1 := powk τF _ (by rw [← map_pow, ← map_pow, hw, map_one, map_one]) hτF
  have e4 := s4 F a τF hτFk q x rfl hq hqt hqx
  have e2 := s2 V F (RingHom.id V) a a τV hτV τF hτFk (RingHom.comp_id a).symm (fun χ => by
    rw [mapv a χ]; exact hτF (Multiplicative.toAdd χ))
  change _ = spMap a ≫ sV.left at e2
  have hi : σ₁ = sV.left := by
    refine ext_of_isDominant_of_isSeparated G.hom (hσ₁G.trans hsVG.symm) (spMap a) ?_
    refine hβ.1.hom_ext ?_ ?_
    · have l : spMap a ≫ σ₁ ≫ β = x.left ≫ genMap U ≫ β := by
        rw [hσ₁β, hxσ, ha, Category.assoc]
      have r : spMap a ≫ sV.left ≫ β = x.left ≫ genMap U ≫ β := by
        rw [← Category.assoc, ← e2, ← e4, Category.assoc]
      rw [Category.assoc, Category.assoc, l, r]
    · simp only [Category.assoc]
      exact congrArg (spMap a ≫ ·) (hσ₁G.trans hsVG.symm)
  have hτk : τ ^ k = 1 := powk τ (b w) (by rw [← map_pow, hw, map_one]) hτ
  have e2' := s2 V κ (RingHom.id V) b b τV hτV τ hτk (RingHom.comp_id b).symm (fun χ => by
    rw [mapv b χ]; exact hτ (Multiplicative.toAdd χ))
  have e3 := s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z (RingHom.id_comp b).symm hz
  rw [← hσ₁β, hi, ← Category.assoc, ← e2', e3, Category.assoc]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolTorsionAny

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

theorem triv_step (hA : IsAbelianScheme G) (hL : L.IsLB) {T : Over S} (a c : T ⟶ G) (n : ℕ) :
    GlobalTheory.AbLaw.Triv (LB.LinComb L (K := Fin 6)
      ![(a ^ n * c).left, c.left, (a ^ n).left, (1 : T ⟶ G).left, (a * c).left, a.left]
      ![1, (n : ℤ) - 1, -1, 1 - (n : ℤ), -(n : ℤ), (n : ℤ)]) := by
  induction n with
  | zero =>
    have h := GlobalTheory.CubeTop.cubeTheorem S G hA L hL T 1 1 c
    simp only [_root_.one_mul] at h
    obtain ⟨t, ht⟩ := h
    obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![((a ^ 0) * c).left, c.left, (a ^ 0).left, (1 : T ⟶ G).left,
      (a * c).left, a.left]) (ε' := ![1, ((0 : ℕ) : ℤ) - 1, -1, 1 - ((0 : ℕ) : ℤ), -((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)])
      (fun U _ h => by
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
          pow_zero, _root_.one_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        push_cast
        module) t ht
    exact ⟨u, hu⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    have h := GlobalTheory.CubeTop.cubeTheorem S G hA L hL T a (a ^ n) c
    rw [← pow_succ'] at h
    obtain ⟨q, hq⟩ := h
    obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![(a ^ (n + 1) * c).left, c.left, (a ^ (n + 1)).left,
      (1 : T ⟶ G).left, (a * c).left, a.left])
      (ε' := ![1, ((n + 1 : ℕ) : ℤ) - 1, -1, 1 - ((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)])
      (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_one]
        push_cast
        module) (LB.mulGen L _ _ _ _ t q) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht hq)
    exact ⟨u, hu⟩

theorem exists_theta_local (hA : IsAbelianScheme G) (hL : L.IsLB) {k : ℕ} {T : Over S} (x : T ⟶ G) (hx : x ^ k = 1)
    (p : T.left) : ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp G L (k : ℤ) (Out.overRes V), θ.pt = Out.overResι V ≫ x := by
  obtain ⟨V, hV, w, hw⟩ := exists_local_gen hL (Y := T.left) ![(1 : T ⟶ G).left, x.left] ![(k : ℤ), -(k : ℤ)] p
  refine ⟨V, hV, ?_⟩
  let xV : Out.overRes V ⟶ G := Out.overResι V ≫ x
  let a : Out.overRes V ⊗ G ⟶ G := fst (Out.overRes V) G ≫ xV
  let c : Out.overRes V ⊗ G ⟶ G := snd (Out.overRes V) G
  have ha : a ^ k = 1 := by
    show (fst (Out.overRes V) G ≫ Out.overResι V ≫ x) ^ k = 1
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, MonObj.comp_one]
  have hP := triv_step hA hL a c k
  rw [ha, _root_.one_mul] at hP
  obtain ⟨t, ht⟩ := hP
  have e₁ : (fst (Out.overRes V) G).left ≫ V.ι ≫ (1 : T ⟶ G).left = (1 : Out.overRes V ⊗ G ⟶ G).left := by
    have : (fst (Out.overRes V) G ≫ Out.overResι V ≫ (1 : T ⟶ G)) = 1 := by
      rw [MonObj.comp_one, MonObj.comp_one]
    rw [← this]
    rfl
  have e₂ : (fst (Out.overRes V) G).left ≫ V.ι ≫ x.left = a.left := rfl
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![(snd (Out.overRes V) G).left, (Out.translPt G xV).left])
    (ε' := ![(k : ℤ), -(k : ℤ)])
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, e₁, e₂]
      rw [translPt_eq]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ w (fst (Out.overRes V) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ hw _))
  exact ⟨⟨xV, u, hu⟩, rfl⟩

theorem exists_weilIs_pow_eq_one (hA : IsAbelianScheme G) (hL : L.IsLB) {k : ℕ} {T : Over S} {x y : T ⟶ G}
    (hx : x ^ k = 1) (hy : y ^ k = 1) : ∃ e : Γ(T.left, ⊤)ˣ, e ^ k = 1 ∧ Out.WeilIs G L (k : ℤ) x y e := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  obtain ⟨e, he⟩ := GlobalTheory.CommutatorPairing.exists_weilIs (k := (k : ℤ)) hG hA hL
    (fun p => exists_theta_local hA hL x hx p) (fun p => exists_theta_local hA hL y hy p)
  have pw : ∀ m : ℕ, Out.WeilIs G L (k : ℤ) (x ^ (m + 1)) y (e ^ (m + 1)) := fun m => by
    induction m with
    | zero => simpa only [zero_add, pow_one] using he
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ e (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih he
  have hk := pw k
  rw [pow_succ x k, hx, _root_.one_mul] at hk
  have := GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL hk he
  rw [pow_succ, mul_eq_right] at this
  exact ⟨e, this, he⟩

end GlobalTheory.HolTorsionAny

namespace GlobalTheory

open HolTorsion HolTorsionAny in

theorem torsion_eq_and_weilIs_of_isHolTo_anyLB : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), LocallyOfFiniteType s → IsAbelianScheme G → L.IsLB → ∀ (m k : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (c : ℂˣ) (b₀ : Fin m → ℂ), 0 < k → IsOpen B → IsPreconnected B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ = x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs G L k (x b₀) (x' b₀) (unitOn c) → ∀ b ∈ B, Out.WeilIs G L k (x b) (x' b) (unitOn c))) := by
  intro X s G _ _ L _ hA hLB m k B y x x' c b₀ hk _ hB hb₀ _ hx hx' htor
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds

  have hku : IsUnit (k : Γ(X, ⊤)) := by
    have h₁ : IsUnit ((k : ℂ)) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk.ne')
    have h₂ := (h₁.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).map s.appTop.hom
    simpa only [map_natCast] using h₂
  haveI : FormallyUnramified (Out.mulA G k).left := GlobalTheory.formallyUnramified_mulA X G k hku
  haveI : Smooth G.hom := hA.smooth
  haveI : IsProper G.hom := hA.proper
  haveI : LocallyOfFiniteType ((Out.mulA G k).left ≫ G.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType (Out.mulA G k).left := locallyOfFiniteType_of_comp _ G.hom
  haveI : IsSeparated ((Out.mulA G k).left ≫ G.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated (Out.mulA G k).left := IsSeparated.of_comp _ G.hom
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ k = 1 ↔ u.left ≫ (Out.mulA G k).left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ (Out.mulA G k).left = (u ^ k).left := by
      rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst (Out.mulA G k).left o
  let q := pullback.snd (Out.mulA G k).left o
  have H : IsPullback p q (Out.mulA G k).left o := IsPullback.of_hasPullback _ _
  haveI : FormallyUnramified q := MorphismProperty.of_isPullback (P := @FormallyUnramified) H ‹_›
  haveI : LocallyOfFiniteType q := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) H ‹_›
  haveI : IsSeparated q := MorphismProperty.of_isPullback (P := @IsSeparated) H ‹_›
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w (Out.mulA G k), ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  refine ⟨fun h₀ b hb => ?_, fun h₀ b hb => ?_⟩
  · have e₀ : a b₀ = a' b₀ := H.hom_ext (by rw [(hab b₀ hb₀).1, (hab' b₀ hb₀).1, h₀])
      (by rw [(hab b₀ hb₀).2, (hab' b₀ hb₀).2])
    have e := comp_eq_of_unramified q hz hB hb₀ hb (by rw [(hzb b₀ hb₀).1, (hzb b₀ hb₀).2, e₀])
    rw [(hzb b hb).1, (hzb b hb).2] at e
    apply Over.OverMorphism.ext
    rw [← (hab b hb).1, ← (hab' b hb).1, e]
  · let T : Over X := Over.mk (pullback.fst q q ≫ q)
    let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
      show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq])
    let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
      show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq, pullback.condition])
    have hu : u ^ k = 1 := (hkill T u).2 (by
      show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, Category.assoc])
    have hv : v ^ k = 1 := (hkill T v).2 (by
      show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, pullback.condition, Category.assoc])
    obtain ⟨e, hek', he⟩ := exists_weilIs_pow_eq_one hA hLB hu hv
    have hek : e.val ^ k = 1 := congrArg Units.val hek'
    have hpull : ∀ w ∈ B, Out.WeilIs G L k (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
      intro w hw
      let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
        show z w ≫ pullback.fst q q ≫ q = y w
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
      have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
        show z w ≫ pullback.fst q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
      have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
        show z w ≫ pullback.snd q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
      have := GlobalTheory.CommPairing.weilIs_pull hG hA hLB h he
      rw [e₁, e₂] at this
      exact this
    have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn c :=
      GlobalTheory.CommutatorPairing.weilIs_unique hG hA hLB (hpull b₀ hb₀) h₀
    have e₁ : Units.map (z b).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
      Units.ext ((val_map_appTop (z b) e.val).trans
        ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hk hek hb₀ hb)).trans (val_map_appTop (z b₀) e.val).symm))
    have := hpull b hb
    rw [e₁, e₀] at this
    exact this

end GlobalTheory
end
end

