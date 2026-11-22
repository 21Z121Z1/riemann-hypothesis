import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3604
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3603
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0192
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1028
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0180
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0162
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0439
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0487
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0476
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0488
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3483
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3579
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3605
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusCharOfLabelOrthogonalDividing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.TorPt

open GlobalTheory.ZH.TorusPerp in

theorem torus_label_over : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ b mu, 𝔪.YY b mu → (χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ b).val))))) → ∀ (q : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N)) (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), q.y = 0 → IsTor χ q.g → QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) q y → y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 τ χ hχ1 hlab q y hqy hqτ hq
  haveI : CharZero V := 𝔪.cn.2.2.2
  have : IsDomain X₁.o₁ := X₁.ar.inj.isDomain _
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hG := hL.1.globalFns
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hkpos : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hkpos

  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hkpos 2) (pow_two _)
  let yb : X₁.S.R →+* AlgebraicClosure (FractionRing V) :=
    (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit hkpos.ne').unit
  let ω : (AlgebraicClosure (FractionRing V))ˣ := Units.map yb.toMonoidHom c₀
  have hωv : (ω : AlgebraicClosure (FractionRing V)) = yb (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := rfl
  have hω : IsPrimitiveRoot ω (X₁.S.r * X₁.S.N) := by
    have : NeZero ((X₁.S.r * X₁.S.N : ℕ) : AlgebraicClosure (FractionRing V)) := ⟨Nat.cast_ne_zero.2 hkpos.ne'⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (yb.comp (algebraMap X₁.o₁ X₁.S.R))]
    exact (hζ.isRoot_cyclotomic hkpos).map

  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK = spMap yb := (Spec.map_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap yb := hy
  let Φ := ptHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))
  have hΦ : ∀ b, Φ (x b) = h ≫ X₁.ρ.pt b := fun b => Over.OverMorphism.ext ((hx b).trans (by rw [← hh]; rfl))
  have weil : ∀ b b', WeilIs 𝔪.A.A 𝔪.A.L (X₁.S.r * X₁.S.N : ℕ) (x b) (x b') (unitOn (ω ^ (eStd X₁.S.g _ b b').val)) :=
    fun b b' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h (X₁.ρ.weil b b' (c₀ ^ (eStd X₁.S.g _ b b').val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← hΦ, ← hΦ] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ _ _ _ _
      (Φ (x b)) (Φ (x b')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← map_unitOn, ← hh]
  have pt_nsmul : ∀ (n : ℕ) b, x (n • b) = x b ^ n := fun n b =>
    map_pow (MonoidHom.mk' (fun a : Multiplicative X₁.S.Gam => x a.toAdd) fun _ _ => xadd _ _) (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q', f q' = x b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (X₁.S.r * X₁.S.N)), ZMod.natCast_self, zero_smul]
    exact (MonoidHom.mk' (fun a : Multiplicative X₁.S.Gam => x a.toAdd) fun _ _ => xadd _ _).map_one)
  have hyf : y = f q := (f₁ q y).1 hq
  have hq1 : y ^ (X₁.S.r * X₁.S.N) = 1 := by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (hq w hw).1
  obtain ⟨a', rfl⟩ := xonto y hq1
  have haa : a' = τ := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hqy hqτ)
    rw [← hyf, hq'] at w₁
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB (weil a' b) w₁)
    have hYY : 𝔪.YY b (𝔪.e₈.symm q'.y) := ⟨q', x b, by simp, (f₁ _ _).2 hq'.symm, hx b⟩
    have e₂ := hlab b _ hYY
    rw [AddEquiv.apply_symm_apply] at e₂
    have e₃ : ω ^ (eStd X₁.S.g _ a' b).val = ω ^ (eStd X₁.S.g _ τ b).val := by
      rw [e₁]
      ext1
      rw [e₂, Units.val_pow_eq_pow_val, hωv, pow_mul, map_pow, map_pow, map_pow]
      rfl
    have e₄ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₃)
    have e₅ := eStd_add_left X₁.S.g _ (a' - τ) τ b
    rw [sub_add_cancel, e₄] at e₅
    exact left_eq_add.1 (e₅.trans (add_comm _ _))
  subst haa
  exact hx a'

theorem labels_hom : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ yy : X₁.S.Gam →+ 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range, Function.Surjective yy ∧ ∀ a mu, 𝔪.YY a mu ↔ yy a = QuotientAddGroup.mk (𝔪.e₈ mu) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V ev X t δ 𝔪
  choose mu hmu using h1
  have key : ∀ a nu, 𝔪.YY a nu ↔
      (QuotientAddGroup.mk (𝔪.e₈ (mu a)) : 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range) =
        QuotientAddGroup.mk (𝔪.e₈ nu) := by
    intro a nu
    rw [h3 a (mu a) nu (hmu a), QuotientAddGroup.eq]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨𝔪.e₈ w, ?_⟩
      have e : nu = mu a + (X₁.S.r * X₁.S.N) • w := hw
      rw [nsmulAddMonoidHom_apply, e, map_add, map_nsmul]
      abel
    · rintro ⟨z, hz⟩
      rw [nsmulAddMonoidHom_apply] at hz
      have e : nu = mu a + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add, map_nsmul, AddEquiv.apply_symm_apply, hz]
        abel)
      exact ⟨𝔪.e₈.symm z, e⟩
  let yy : X₁.S.Gam →+ 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range :=
    AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (𝔪.e₈ (mu a))) fun a b => by
      have h := (key (a + b) (mu a + mu b)).1 (h4 a b (mu a) (mu b) (hmu a) (hmu b))
      refine h.trans ?_
      rw [map_add, QuotientAddGroup.mk_add]
  refine ⟨yy, fun c => ?_, fun a nu => (key a nu)⟩
  induction c using QuotientAddGroup.induction_on with
  | H α =>
    obtain ⟨a, ha⟩ := h2 (𝔪.e₈.symm α)
    refine ⟨a, ?_⟩
    have := (key a _).1 ha
    rw [AddEquiv.apply_symm_apply] at this
    exact this

open GlobalTheory.ZH.TorusPerp GlobalTheory.ZH.PerpTorus GlobalTheory.TorusExt GlobalTheory.TorsionExt in
attribute [local instance] gtGroup in

theorem exists_torus_char : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 τ hτ
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hB := 𝔪.D.tau_bimult
  have hkpos : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)
  obtain ⟨yy, yyonto, hyy⟩ := GlobalTheory.GSep.TorPt.labels_hom I X₁ z₁ act V ev X t δ 𝔪
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  have hker : τ ∈ X₁.S.perp yy.ker := fun h hh => by
    have h0 : 𝔪.YY h 0 := (hyy h 0).2 (by rw [(AddMonoidHom.mem_ker).1 hh, map_zero]; rfl)
    exact hτ h ((GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hx₀ V ev X t δ 𝔪 h).2 h0)
  obtain ⟨mf, hmf⟩ := exists_form X₁.S yy yyonto τ hker
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) := X₁.S.prim.pow (pow_pos hkpos 2) (pow_two _)
  let ω : (FractionRing V)ˣ := Units.map (𝔪.yK.comp (algebraMap X₁.o₁ X₁.S.R)).toMonoidHom (hζ.isUnit hkpos.ne').unit
  have hωv : (ω : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := rfl
  have hω1 : ω ^ (X₁.S.r * X₁.S.N) = 1 := by
    ext1
    rw [Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, hζ.pow_eq_one, map_one, map_one, Units.val_one]
  let χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ :=
    (AddChar.zmodChar (X₁.S.r * X₁.S.N) hω1).toMonoidHom.comp mf.toMultiplicative
  have hχ : ∀ α, χ (Multiplicative.ofAdd α) = ω ^ (mf α).val := fun _ => rfl
  have hχ1 : χ ^ (X₁.S.r * X₁.S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (mf α.toAdd).val) ^ (X₁.S.r * X₁.S.N) = 1
    rw [pow_right_comm, hω1, one_pow]
  refine ⟨χ, hχ1, fun g₀ hg₀ => ?_⟩

  obtain ⟨q, hqy, hqg⟩ := GlobalTheory.ZH.ClassWeight.exists_qkPt_tor hg₀ hχ1
  have hsq : (spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) ≫ X₁.ρ.P.A.hom = 𝟙 _ ≫ spMap 𝔪.yK := by
    rw [Category.assoc, Over.w]; simp
  let ℓ := 𝔪.cart.1.lift (spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) (𝟙 _) hsq
  have hℓ : ℓ ≫ 𝔪.A.A.hom = (TFK (R := V) (FractionRing V)).hom := by
    rw [𝔪.cart.1.lift_snd]
    show _ = Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V)))
    rw [Algebra.algebraMap_self]
    exact (Spec.map_id _).symm
  let xF : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A := Over.homMk ℓ hℓ
  have hxF : xF.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left := 𝔪.cart.1.lift_fst _ _ _
  refine ⟨q, xF, hqy, hqg, ?_, hxF⟩
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) := by
    ext; simp
  let qb := qkExt hB (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf q
  have hqb : QkExt (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) q qb := (qkExt_iff hB _ hf _ _).2 rfl
  rw [qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow 𝔪.U hkpos hqb xF]
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  obtain ⟨f, f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hkpos
  have hqbf := (f₁ qb (f qb)).2 rfl
  let χb : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ :=
    (Units.map (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).toMonoidHom).comp χ
  have hχb1 : χb ^ (X₁.S.r * X₁.S.N) = 1 := MonoidHom.ext fun α => by
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show Units.map _ (χ α) ^ _ = 1
    rw [← map_pow, ← MonoidHom.pow_apply, hχ1, MonoidHom.one_apply, map_one]
  have hqbt : IsTor χb qb.g := by
    have e1 : q.g = torusPt _ _ (Additive.ofMul χ) := (isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 (hqg ▸ hg₀))
    show IsTor χb (gtExt _ _ hf q.g)
    rw [e1, GlobalTheory.QkNumberField.gtExt_torusPt, isTor_iff]
    exact isTorusPtF_torusPt _
  have hlab : ∀ b mu, 𝔪.YY b mu → (χb (Multiplicative.ofAdd (𝔪.e₈ mu)) : AlgebraicClosure (FractionRing V)) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))
        (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ b).val)))) := by
    intro b mu h
    show algebraMap _ _ ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : FractionRing V)) = _
    rw [hχ, hmf b _ ((hyy b mu).1 h), Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul]
  have hover := GlobalTheory.GSep.TorPt.torus_label_over I X₁ z₁ act V ev X t δ 𝔪 τ χb hχb1 hlab qb (f qb) hqy hqbt hqbf
  have heq : fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ xF = f qb := by
    refine Over.OverMorphism.ext (𝔪.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hover, Over.comp_left, Category.assoc, hxF, ← Category.assoc]
    congr 1
    exact (Spec.map_comp _ _).symm
  rw [heq]
  exact hqbf

end GlobalTheory.GSep.TorPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSystemClassicalTraitsClosedPoi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.PreSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

theorem rank_le (T : UTrait Xo c) : Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := GlobalTheory.T.character_group_finrank_le_min_signature_unitary_trait E H Dw l Xo c T

theorem lam (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (hz : IsClosed ({z₁} : Set X₁.M.Z)) :
    ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 →
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ :=
  GlobalTheory.T.classical_trait_periods_bounded_below_closed_point E H Dw l Xo c C X₁ p z₁ hz

theorem finite_X (T : UTrait Xo c) : Module.Finite (𝓞 E) T.P.D.toPre.X :=
  Module.Finite.of_restrictScalars_finite ℤ _ _

theorem projective_X (T : UTrait Xo c) : Module.Projective (𝓞 E) T.P.D.toPre.X := by
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := finite_X T
  have : Module.Flat (𝓞 E) T.P.D.toPre.X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨a, hx⟩
    by_contra hx0
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (a : 𝓞 E)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero (nonZeroDivisors.coe_ne_zero a))
    have h : n • x = 0 := by
      have hx' : (a : 𝓞 E) • x = 0 := hx
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hx', smul_zero]
    exact hx0 ((smul_eq_zero.1 h).resolve_left hn)
  have : Module.FinitePresentation (𝓞 E) T.P.D.toPre.X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

variable {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def evC (t : UCTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p :=
  (RatModel.valHomOf (gPt p ≫ t.y) z₁ (RatModel.gPt_specializes t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem evC_apply (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : evC t a = t.val a := rfl

theorem norm_evC_le (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖evC t a‖ ≤ 1 :=
  RatModel.norm_val_le_one t.cen (X₁.M.stalkEquiv z₁ a).2

theorem norm_evC_lt (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) (ha : a ∈ maximalIdeal _) :
    ‖evC t a‖ < 1 := by
  have h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a) := fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)
  exact (RatModel.norm_val_lt_one_iff t.cen (X₁.M.stalkEquiv z₁ a).2).2 h1

theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem be_bal (T : UTrait Xo c) : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X := by
  rw [balForms_eq_levelForms]; exact T.lev

end GlobalTheory.UPoinc.PreSys

namespace GlobalTheory.UPoinc.PreSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

variable (E X₁ p) in

abbrev Key : Type :=
  (Sp (OO p) ⟶ X₁.M.Z) × (Σ k : ℕ, (𝓞 E →+* Module.End ℤ (Fin k → ℤ)) × ((Fin k → ℤ) → (Fin k → ℤ) → ℝ))

def Rep (t : UCTrait X₁ p z₁) (q : Key E X₁ p) : Prop :=
  t.y = q.1 ∧ ∃ e : (Fin q.2.1 → ℤ) ≃ₗ[ℤ] t.T.P.D.toPre.X, (∀ (a : 𝓞 E) u, e (q.2.2.1 a u) = a • e u) ∧
    ∀ u v, q.2.2.2 u v = t.sc * t.T.be (e u) (e v)

def coord (t : UCTrait X₁ p z₁) : (Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) ≃ₗ[ℤ] t.T.P.D.toPre.X :=
  (Module.finBasis ℤ t.T.P.D.toPre.X).equivFun.symm

def actOf (t : UCTrait X₁ p z₁) : 𝓞 E →+* Module.End ℤ (Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) where
  toFun a := (coord t).symm.toLinearMap ∘ₗ (DistribSMul.toLinearMap ℤ t.T.P.D.toPre.X a) ∘ₗ (coord t).toLinearMap
  map_one' := LinearMap.ext fun u => by simp
  map_mul' a b := LinearMap.ext fun u => by simp [mul_smul]
  map_zero' := LinearMap.ext fun u => by simp
  map_add' a b := LinearMap.ext fun u => by simp [add_smul]

theorem coord_actOf (t : UCTrait X₁ p z₁) (a : 𝓞 E) (u : Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) :
    coord t (actOf t a u) = a • coord t u := by
  simp [actOf]

def keyOf (t : UCTrait X₁ p z₁) : Key E X₁ p :=
  (t.y, ⟨Module.finrank ℤ t.T.P.D.toPre.X, actOf t, fun u v => t.sc * t.T.be (coord t u) (coord t v)⟩)

theorem rep_keyOf (t : UCTrait X₁ p z₁) : Rep t (keyOf t) := ⟨rfl, coord t, coord_actOf t, fun _ _ => rfl⟩

variable (X₁ p z₁) in

def Pts : Type := {q : Key E X₁ p // ∃ t : UCTrait X₁ p z₁, Rep t q}

noncomputable def pick (y : Pts X₁ p z₁) : UCTrait X₁ p z₁ := Classical.choose y.2

theorem pick_rep (y : Pts X₁ p z₁) : Rep (pick y) y.1 := Classical.choose_spec y.2

theorem exists_equiv_of_rep {t t' : UCTrait X₁ p z₁} {q : Key E X₁ p} (h : Rep t q) (h' : Rep t' q) :
    ∃ e : t.T.P.D.toPre.X ≃ₗ[𝓞 E] t'.T.P.D.toPre.X, ∀ a b, t.sc * t.T.be a b = t'.sc * t'.T.be (e a) (e b) := by
  obtain ⟨-, f, hf, hfb⟩ := h
  obtain ⟨-, f', hf', hfb'⟩ := h'
  let g : t.T.P.D.toPre.X ≃ₗ[ℤ] t'.T.P.D.toPre.X := f.symm.trans f'
  have hg : ∀ (a : 𝓞 E) x, g (a • x) = a • g x := by
    intro a x
    obtain ⟨u, rfl⟩ := f.surjective x
    simp only [g, LinearEquiv.trans_apply, ← hf, LinearEquiv.symm_apply_apply, hf']
  refine ⟨{ g with map_smul' := hg }, fun a b => ?_⟩
  obtain ⟨u, rfl⟩ := f.surjective a
  obtain ⟨v, rfl⟩ := f.surjective b
  show _ = t'.sc * t'.T.be (g (f u)) (g (f v))
  simp only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [← hfb, ← hfb']

variable (X₁ p z₁) in

noncomputable def sys : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁) where
  Y := Pts X₁ p z₁
  ev y := evC (pick y)
  ev_le y h := norm_evC_le _ h
  ev_lt y h hh := norm_evC_lt _ h hh
  X y := (pick y).T.P.D.toPre.X
  fin y := finite_X _
  proj y := projective_X _
  rank_le y := rank_le _
  β y := (pick y).T.be
  bal y := be_bal _
  pos y x hx := be_pos _ x hx
  sc y := (pick y).sc
  sc_pos y := sc_pos _

theorem sys_matches : UMatches (sys X₁ p z₁) := by
  intro t
  refine ⟨⟨keyOf t, t, rep_keyOf t⟩, fun a => ?_, ?_⟩
  · obtain ⟨hy, -⟩ := pick_rep ⟨keyOf t, t, rep_keyOf t⟩
    show evC _ a = t.val a
    rw [evC_apply]
    unfold UCTrait.val
    rw [hy]
    rfl
  · exact exists_equiv_of_rep (pick_rep ⟨keyOf t, t, rep_keyOf t⟩) (rep_keyOf t)

theorem sys_lam (hz : IsClosed ({z₁} : Set X₁.M.Z)) : (sys X₁ p z₁).abelian₂ := by
  obtain ⟨K, hK⟩ := lam X₁ p z₁ hz
  exact ⟨K, fun y x hx => hK (pick y) x hx⟩

end GlobalTheory.UPoinc.PreSys

open GlobalTheory Classical in

theorem GlobalTheory.UPoinc.PreSys.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), UMatches Φ ∧ Φ.abelian₂ ∧ (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) := by
  intro E _ _ _ H Dw _ l Xo c C X₁ p _ z₁ hz
  exact ⟨GlobalTheory.UPoinc.PreSys.sys X₁ p z₁, GlobalTheory.UPoinc.PreSys.sys_matches, GlobalTheory.UPoinc.PreSys.sys_lam hz,
    fun y => ⟨GlobalTheory.UPoinc.PreSys.pick y, fun a => rfl, LinearEquiv.refl _ _, fun a b => rfl⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHypsOfPublishedUE
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Fc.S0.StageU

theorem nonempty_hyps_of_classicalTheoremsUE : S0.HypothesesUE → S0.RowRat → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (A : GroupRetwisting.AtP), EvLgG A → RL.At (prm1 hL cDep) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoAndThreeForFamily Fm) → RL.At (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)) S0.FunctorialityCondition → RL.At (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)) S0.CovolumeBound' → Nonempty (Hyps S0.NL DRS) := by
  intro P hR hL cDep A hA hN hF hL3
  obtain ⟨hP, hMem, hEx⟩ := GlobalTheory.T.linked_bundle_construction_exists P hR hL cDep A hA
  obtain ⟨_, prN, serN, _⟩ := GlobalTheory.T.local_langlands_hypotheses_of_literature P.litN P.toHypothesesX
  have hOL := GlobalTheory.Fc.S0.ontoX_and_lamLow_of_classicalTheoremsUE P
  have hO := GlobalTheory.T.open_first_parameters_of_hypothesesUE P hL cDep
  have hNrow := GlobalTheory.NLink.Final.main P.nLink prN P.toHypothesesX serN P.depthZeroWild' P.depthZeroSupport'
    P.localFiniteness P.localTateDuality P.localEulerChar hL cDep hN
  have hmono := GlobalTheory.Glob.open_and_linked_of_stronger_extension hL (GlobalTheory.HeightCounting.Up.NEl hL cDep) (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)
  have hO' := hmono.2 hO
  have hN' : RL.At (prmR (NEa hL (GlobalTheory.HeightCounting.Up.NEo hL cDep) A) SExt.none (geoCl anyGeometry)) (fun Q L => R1.PredicateAtBundlePoints Q L S0.NL) :=
    hmono.1 (fun 𝒜 _ => S0.NL (Cp.D3 3 𝒜)) hNrow
  have hAll := GlobalTheory.Fc.AllAtMemberStage0.allRows_of_open0 P.globalArtinReciprocity P.siegelWeilUnitaryConvergent2 P.discreteSeriesCover
    P.harishChandraModules P.cuspRapidDecay P.casselmanWallach P.discreteSeriesClassification hOL.1 hOL.2
    hL _ _ _ S0.NL hO' hL3 hF hN'
  exact GlobalTheory.Fc.nonempty_hyps_of_allRows hP GlobalTheory.ThinScaleLiterature.litThin GlobalTheory.wuDecayOfGap GlobalTheory.rowsFinDim_link
    GlobalTheory.rowsPos_typeP (GlobalTheory.rowNGP_of_siegelWeil P.siegelWeilUnitaryConvergent2)
    (GlobalTheory.rowMainEqP_of_siegelWeil P.siegelWeilUnitaryConvergent2)
    (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio P.siegelWeilUnitaryConvergent2) GlobalTheory.genusMassAt_two
    KPx _ _ _ S0.NL DRS (fun _ => hMem) hEx hAll

end GlobalTheory.Fc.S0.StageU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingIsPerfectAbelianSchemesBothKernelsZeroStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_isPerfect_abelianSchemes_both_kernels_zero : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair := by
  first | exact @GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham | exact GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham | (intros; apply GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthBoundSmallScaleStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_growth_bound_small_scale : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share → Covers fun Fm x _ ι p i Y PP _ => ∀ s : ℕ, 1 ≤ s → s ≤ 2 → (Y.rk (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤ (1 + min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i))) * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  first | exact @GlobalTheory.CovTop.HodgeSteps.rk_le | exact GlobalTheory.CovTop.HodgeSteps.rk_le | (intros; apply GlobalTheory.CovTop.HodgeSteps.rk_le <;> assumption)
end

