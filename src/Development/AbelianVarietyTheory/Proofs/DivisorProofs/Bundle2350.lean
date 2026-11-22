import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LgOfSingleNegOneEqNeg
section
namespace GradedLogInvariants
section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GradedInv

section Var

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem isEqn_sum {ι : Type} (s : Finset ι) (D : ι → Y.Dv) (g : ι → Y.Fnˣ) (x : Y.X)
    (h : ∀ i ∈ s, (D i).IsEqn x (g i)) : (∑ i ∈ s, D i).IsEqn x (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CartierDiv.isEqn_zero x
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem unitAt_genAt_mul (D D' : Y.Dv) (hD : D' = -D) (x : Y.X) : UnitAt x (genAt D' x * genAt D x) := by
  have h1 : D'.IsEqn x (eqn D x)⁻¹ := hD ▸ (Base.isEqn_eqn D x).neg
  have h2 := (Base.isEqn_eqn D' x).iff_unitAt.1 h1
  convert h2 using 1
  simp only [genAt, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  ring

theorem log_val_inv (D D' : Y.Dv) (hD : D' = -D) (y : AlgPt Y) (T : Y.Fnˣ) (hT : D.IsEqn (below y.1) T)
    {v : HeightOneSpectrum (𝓞 F)} (ε : TrueGeo.Ext v) :
    Real.log (ε.w (valAt y.1 ((T⁻¹ * (eqn D' (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn))) =
      -Real.log (ε.w (valAt y.1 ((T * (eqn D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn))) +
        Real.log (ε.w (valAt y.1 (genAt D' (below y.1) * genAt D (below y.1)))) := by
  have hG := unitAt_genAt_mul D D' hD (below y.1)
  have hU : UnitAt (below y.1) ((T * (eqn D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn) := by
    have h := (Base.isEqn_eqn D (below y.1)).iff_unitAt.1 hT
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv] using h
  have e : ((T⁻¹ * (eqn D' (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn) =
      (genAt D' (below y.1) * genAt D (below y.1)) * ((T * (eqn D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn)⁻¹ := by
    have h0 : ((eqn D (below y.1) : Y.Fnˣ) : Y.Fn) ≠ 0 := Units.ne_zero _
    have h1 : ((eqn D' (below y.1) : Y.Fnˣ) : Y.Fn) ≠ 0 := Units.ne_zero _
    have h2 : ((T : Y.Fnˣ) : Y.Fn) ≠ 0 := Units.ne_zero _
    simp only [genAt, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have n1 : ε.w (valAt y.1 (genAt D' (below y.1) * genAt D (below y.1))) ≠ 0 :=
    (AbsoluteValue.ne_zero_iff ε.w).2 (SmallSec.valAt_ne_zero hG)
  have n2 : ε.w (valAt y.1 ((T * (eqn D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn)) ≠ 0 :=
    (AbsoluteValue.ne_zero_iff ε.w).2 (SmallSec.valAt_ne_zero hU)
  rw [e, SmallSec.valAt_mul hG.regAt hU.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv hU, map_mul, map_inv₀,
    Real.log_mul n1 (inv_ne_zero n2), Real.log_inv]
  ring

end Var

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem divOf_neg (n : Letter Dw → ℤ) : divOf Y (-n) = -divOf Y n := by
  simp [divOf, neg_smul, Finset.sum_neg_distrib]

theorem expo_single_neg_one (a : Sym E) :
    expo Dw (Finsupp.single a (-1)) = -expo Dw (Finsupp.single a 1) := by
  funext x
  simp only [expo_single, Pi.neg_apply]
  split_ifs <;> simp

theorem isEqn_prod (x : Y.Y.X) (n : Letter Dw → ℤ) :
    (divOf Y n).IsEqn x (∏ z : Letter Dw, (Y.gr_spec x).choose_spec.choose_spec.choose z.1 z.2 ^ n z) :=
  isEqn_sum _ _ _ x fun z _ =>
    ((Y.gr_spec x).choose_spec.choose_spec.choose_spec.2 z.1 z.2).zsmul (n z)

theorem exists_lgOf_eq_val (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) :
    ∃ (κ : ℝ) (S : Sym E → ℝ), ∀ w : Sym E →₀ ℤ, lgOf Y w v ε y =
      Real.log (ε.w (valAt y.1 (((∏ z : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw w z) *
          (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) + κ * w.sum fun a n => (n : ℝ) * S a :=
  ⟨_, _, fun _ => dif_pos (residueCharacteristic_prime v)⟩

theorem exists_lgOf_single (a : Sym E) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) :
    ∃ S : ℝ, ∀ n : ℤ, lgOf Y (Finsupp.single a n) v ε y =
      Real.log (ε.w (valAt y.1 (((∏ z : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw (Finsupp.single a n) z) *
          (eqn (divOf Y (expo Dw (Finsupp.single a n))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) + n * S := by
  obtain ⟨κ, S, h⟩ := exists_lgOf_eq_val Y v ε y
  refine ⟨κ * S a, fun n => ?_⟩
  rw [h, Finsupp.sum_single_index (by simp)]
  ring

theorem lgOf_single_neg_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (a : Sym E) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y), lgOf Y (Finsupp.single a (-1)) v ε y = -lgOf Y (Finsupp.single a 1) v ε y + Real.log (ε.w (valAt y.1 (genAt (divOf Y (expo Dw (Finsupp.single a (-1)))) (below y.1) * genAt (divOf Y (expo Dw (Finsupp.single a 1))) (below y.1)))) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y a v ε y
  obtain ⟨S, hS⟩ := exists_lgOf_single Y a v ε y
  have hex := expo_single_neg_one (Dw := Dw) a
  have hD : divOf Y (expo Dw (Finsupp.single a (-1))) = -divOf Y (expo Dw (Finsupp.single a 1)) := by
    rw [hex, divOf_neg]
  have hT := isEqn_prod Y (below y.1) (expo Dw (Finsupp.single a 1))
  have key := log_val_inv _ _ hD y _ hT ε
  have hinv : (∏ z : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^
      expo Dw (Finsupp.single a (-1)) z) = (∏ z : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^
      expo Dw (Finsupp.single a 1) z)⁻¹ := by
    rw [hex, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [Pi.neg_apply, zpow_neg]
  rw [hS (-1), hS 1, hinv, key]
  push_cast
  ring

end Flag

end GlobalTheory.CompanionTheory.GradedInv

end

end GradedLogInvariants
section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

theorem _root_.GlobalTheory.Adopt.lgOf_single_neg_one_eq_neg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (a : Sym E) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y), lgOf Y (Finsupp.single a (-1)) v ε y = -lgOf Y (Finsupp.single a 1) v ε y + Real.log (ε.w (valAt y.1 (genAt (divOf Y (expo Dw (Finsupp.single a (-1)))) (below y.1) * genAt (divOf Y (expo Dw (Finsupp.single a 1))) (below y.1)))) := by
  first | exact @GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.lgOf_single_neg_one | exact GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.lgOf_single_neg_one | (intros; apply GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.lgOf_single_neg_one <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingOfComparison
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_extend_of_isProper {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {V : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] (y : Sp (FractionRing V) ⟶ X) (s : Sp V ⟶ B) (h : y ≫ f = spMap (algebraMap V (FractionRing V)) ≫ s) :
    ∃ χ : Sp V ⟶ X, y = spMap (algebraMap V (FractionRing V)) ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := V, K := FractionRing V, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

theorem liftSt_of_cmpSt (hC : CmpSt) : LiftSt := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle Z la p _ Xw hc _ T io e y₀ ho halg k y hy
  letI := io.toAlgebra
  have hfin : T.FinRes := halg.1
  obtain ⟨hOI, hW, -, -, -, -, -, -, hlift⟩ := hc
  obtain ⟨kO, hk⟩ : ∃ kO : T.V →+* 𝓞_ℂ_[p], ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a) := by
    letI := H.starRing
    obtain ⟨-, kO, P, _, _, hP, -⟩ := hy
    exact ⟨kO, hP.1⟩
  let kk : T.Fr →+* ℂ_[p] := k.toRingHom
  letI algT : Algebra T.Fr ℂ_[p] := kk.toAlgebra
  let K : IntermediateField T.Fr ℂ_[p] := algebraicClosure T.Fr ℂ_[p]
  haveI hKc : IsAlgClosure T.Fr K := algebraicClosure.isAlgClosure T.Fr ℂ_[p]
  haveI : IsAlgClosed K := hKc.isAlgClosed
  have hKa : Algebra.IsAlgebraic T.Fr K := hKc.isAlgebraic
  let O : ValuationSubring K := (𝓞_ℂ_[p]).comap K.val.toRingHom
  have hO : ∀ x : K, x ∈ O ↔ ‖(x : ℂ_[p])‖ ≤ 1 := fun x => by
    show (Valued.v (x : ℂ_[p]) ≤ 1) ↔ _
    rw [← coe_valued]
    exact NNReal.coe_le_one.symm
  let g : c.F →+* K := (algebraMap T.Fr K).comp io
  have hg : ∀ x : c.F, (x : ℂ) ∈ W ↔ g x ∈ O := fun x => by
    rw [hW, hO, ← GlobalTheory.T.p_adic_norm_le_one_iff_valuation la p T io e ho kk kO hk x]
    rfl
  obtain ⟨fK, hfK1, hfK2⟩ := GlobalTheory.T.exists_valuation_extension_field c.F c'.F hle c'.fin W K O g hg
  have hgf : (algebraMap T.Fr K).comp (algebraMap c.F T.Fr) = fK.comp (IntermediateField.inclusion hle).toRingHom :=
    RingHom.ext fun x => (hfK1 x).symm
  obtain ⟨yy, hyy1, hyy2, hyy3⟩ := hlift K fK (spMap (algebraMap T.Fr K) ≫ ptF y₀.1) (by
      rw [Category.assoc, ptF, pullback.lift_snd, spMap_spMap, hgf]) (by
      rintro _ ⟨q, rfl⟩
      exact halg.2 _)
  obtain ⟨L, yL, hLfin, hyL1, hyL2⟩ := GlobalTheory.T.exists_finite_subextension_point _ _ r (GlobalTheory.T.level_change_locally_finite_type r hle hOI) T.Fr K hKa yy (ptF y₀.1) hyy2
  obtain ⟨kL, hkL⟩ : ∃ kL : L →+* ℂ_[p], kL = K.val.toRingHom.comp L.val.toRingHom := ⟨_, rfl⟩
  have hkL1 : ∀ x : L, kL x = ((x : K) : ℂ_[p]) := fun x => by rw [hkL]; rfl
  obtain ⟨T', i, iF, ψ, kO', hT'fin, hkO'inj, hi, hψ, hkO', hint⟩ :=
    GlobalTheory.T.exists_finite_dvr_extension p T hfin kO kk hk L kL (fun a => by rw [hkL1]; rfl)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (yL ≫ pullback.snd _ _ : Sp L ⟶ Sp c'.F)
  obtain ⟨fL, hfLφ⟩ : ∃ fL : c'.F →+* L, fL = φ.hom := ⟨_, rfl⟩
  have hφ' : yL ≫ pullback.snd _ _ = spMap fL := by rw [← hφ, hfLφ]; rfl
  have hfL : ∀ x, ((fL x : K)) = fK x := fun x => by
    have e1 : spMap ((algebraMap L K).comp fL) = spMap fK := by
      rw [← spMap_spMap, ← hφ', ← Category.assoc, hyL1, hyy1]
    have e2 := congrArg (fun f => (CommRingCat.Hom.hom f) x) (Spec.map_injective e1)
    exact e2
  obtain ⟨β', hβ'⟩ := hint (c'.V W) (fL.comp (c'.V W).subtype) (fun a => by
    rw [RingHom.comp_apply, hkL1, hfL, ← hO]
    exact hfK2 a a.2)
  obtain ⟨yyT, hyyT⟩ : ∃ t : Sp T'.Fr ⟶ Xo'.XF c', t = spMap ψ.toRingHom ≫ yL := ⟨_, rfl⟩
  have hring : ψ.toRingHom.comp (fL.comp (c'.V W).subtype) = (algebraMap T'.V T'.Fr).comp β' :=
    RingHom.ext fun a => (hβ' a).symm
  have hsq : (yyT ≫ Y.j) ≫ Y.s = spMap (algebraMap T'.V (FractionRing T'.V)) ≫ spMap β' := by
    have hj : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    rw [hyyT, Category.assoc, Category.assoc, hj, ← Category.assoc yL, hφ', spMap_spMap, spMap_spMap, spMap_spMap,
      hring]
  obtain ⟨yT, hyT⟩ := exists_extend_of_isProper Y.s (projProper _ _ _ Y.proj) (yyT ≫ Y.j) (spMap β') hsq
  obtain ⟨k', hk'⟩ : ∃ k' : T'.Fr →+* ℂ_[p], k' = kL.comp ψ.symm.toRingHom := ⟨_, rfl⟩
  have hk'iF : ∀ a, k' (iF a) = k a := fun a => by
    rw [hk', RingHom.comp_apply, ← hψ a]
    show kL (ψ.symm (ψ _)) = _
    rw [RingEquiv.symm_apply_apply, hkL1]
    rfl
  have hkO'' : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = k' (algebraMap T'.V T'.Fr a) := fun a => by
    rw [hk', hkO' a]; rfl
  have hψi : ψ.toRingHom.comp (algebraMap T.Fr L) = iF := RingHom.ext hψ
  have hyyTr : yyT ≫ r = spMap iF ≫ ptF y₀.1 := by
    rw [hyyT, Category.assoc, hyL2, ← Category.assoc, spMap_spMap, hψi]
  obtain ⟨P, π, ψ2, hHT⟩ := hC E H Dw l l' Xo Xo' c c' W Y r ν hle hOI p T T' i iF hi io y₀ k y hy k' kO'
    hkO'' hk'iF yT yyT hyT.symm hyyTr
  refine ⟨spMap kO' ≫ yT, spMap k' ≫ yyT, ⟨⟨T', kO', yT, hT'fin, hkO'inj, rfl⟩, ?_⟩, P, π, ψ2, hHT⟩
  have hrk : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO' = k'.comp (algebraMap T'.V T'.Fr) := RingHom.ext hkO''
  have e3 : spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap kO' ≫ yT = (spMap k' ≫ spMap ψ.toRingHom) ≫ yL ≫ Y.j := by
    rw [← Category.assoc, spMap_spMap, hrk, ← spMap_spMap, Category.assoc, ← hyT, hyyT]
    simp only [Category.assoc]
  rw [e3]
  rintro _ ⟨q, rfl⟩
  obtain ⟨q0⟩ : Nonempty (Sp K) := inferInstance
  have hq : (spMap k' ≫ spMap ψ.toRingHom) q = spMap (algebraMap L K) q0 :=
    Subsingleton.elim (α := PrimeSpectrum L) _ _
  rw [Scheme.Hom.comp_apply, hq, ← Scheme.Hom.comp_apply, ← Category.assoc, hyL1]
  exact hyy3 ⟨q0, rfl⟩

end GlobalTheory.FlatModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongOfPrincipal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.LiftInduct

theorem same_comp {S : Scheme.{0}} (A : Over S) {T U Y Y' : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (e : Y' ⟶ Y) {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) : Same A N M (e ≫ y) (e ≫ u) :=
  LBIso.chartPull (h := (lift (fst A Y') (snd A Y' ≫ e)).left)
    (chartPullSame N _ _ _ _ fun _ => by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc])
    (chartPullSame M _ _ _ _ fun _ => by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]) h

variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {U : Over (Sp R)} (M : LB (A ⊗ U).left)

def LiftsVia {B C : Type} [CommRing B] [CommRing C] (φ : B →+* C) : Prop :=
  ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left)
    (u₀ : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) ⟶ U),
    Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ y) (by simp) :
      Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) ⟶ T) u₀ →
    ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u

theorem liftsVia_of_leftInverse {B C : Type} [CommRing B] [CommRing C] (φ : B →+* C) (ψ : C →+* B)
    (hψ : ψ.comp φ = RingHom.id B) : LiftsVia A M φ := by
  intro T N _ y u₀ h
  have hs : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_id, Spec.map_id]
  let e : Over.mk (y ≫ T.hom) ⟶ Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) :=
    Over.homMk (Spec.map (CommRingCat.ofHom ψ)) (by simp [reassoc_of% hs])
  refine ⟨e ≫ u₀, ?_⟩
  have h' := same_comp A e h
  convert h' using 1
  ext
  simp [e, reassoc_of% hs]

theorem liftsVia_comp {B C D : Type} [CommRing B] [CommRing C] [CommRing D] (φ : B →+* C) (ψ : C →+* D)
    (hφ : LiftsVia A M φ) (hψ : LiftsVia A M ψ) : LiftsVia A M (ψ.comp φ) := by
  intro T N hN y u₀ h
  have k : Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  let e : Over.mk (Spec.map (CommRingCat.ofHom ψ) ≫ (Spec.map (CommRingCat.ofHom φ) ≫ y) ≫ T.hom) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ y ≫ T.hom) := Over.homMk (𝟙 _) (by simp [k])
  obtain ⟨u₁, h₁⟩ := hψ T N hN (Spec.map (CommRingCat.ofHom φ) ≫ y) (e ≫ u₀) (by
    have h' := same_comp A e h
    convert h' using 1
    ext
    simp [e, k])
  let e' : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ y ≫ T.hom) ⟶
      Over.mk ((Spec.map (CommRingCat.ofHom φ) ≫ y) ≫ T.hom) := Over.homMk (𝟙 _) (by simp)
  exact hφ T N hN y (e' ≫ u₁) (by
    have h' := same_comp A e' h₁
    convert h' using 1
    ext
    simp [e'])

theorem liftsVia_of_list
    (hyp : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (t : B),
      t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ →
      LiftsAlong A M B (Ideal.span {t})) :
    ∀ (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (C : Type) [CommRing C] (φ : B →+* C)
      (l : List B), l.length = n → Function.Surjective φ → RingHom.ker φ = Ideal.span {x | x ∈ l} →
      RingHom.ker φ ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * RingHom.ker φ = ⊥ →
      LiftsVia A M φ := by
  intro n
  induction n with
  | zero =>
    intro B _ _ _ C _ φ l hl hs hk _ _
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero hl
    subst hl0
    have hinj : Function.Injective φ := by
      rw [RingHom.injective_iff_ker_eq_bot, hk]
      simp
    let e := RingEquiv.ofBijective φ ⟨hinj, hs⟩
    refine liftsVia_of_leftInverse A M φ e.symm.toRingHom ?_
    ext x
    exact e.symm_apply_apply x
  | succ n ih =>
    intro B _ _ _ C _ φ l hl hs hk hkm hmk
    obtain ⟨t, l', rfl⟩ : ∃ t l', l = t :: l' := by
      cases l with
      | nil => simp at hl
      | cons t l' => exact ⟨t, l', rfl⟩
    have ht : t ∈ RingHom.ker φ := hk ▸ Ideal.subset_span (by simp)
    have hJ : Ideal.span {t} ≤ RingHom.ker φ := (Ideal.span_singleton_le_iff_mem _).2 ht
    let ψ : B ⧸ Ideal.span {t} →+* C := Ideal.Quotient.lift _ φ (fun a ha => hJ ha)
    have hcomp : ψ.comp (Ideal.Quotient.mk _) = φ := by
      ext x
      rfl
    have hprin : LiftsVia A M (Ideal.Quotient.mk (Ideal.span {t})) :=
      hyp B t (hkm ht) (le_bot_iff.1 ((Ideal.mul_mono_right hJ).trans hmk.le))
    have hne : Ideal.span {t} ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ hJ.trans hkm))
    haveI : Nontrivial (B ⧸ Ideal.span {t}) := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (B ⧸ Ideal.span {t}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have hψs : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ _ hs
    have hC : Nontrivial C := by
      rcases subsingleton_or_nontrivial C with hC | hC
      · exact absurd (hkm (RingHom.mem_ker.2 (Subsingleton.elim _ _)))
          ((Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal B).ne_top)
      · exact hC
    have h0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self t)
    have hker : RingHom.ker ψ = (RingHom.ker φ).map (Ideal.Quotient.mk (Ideal.span {t})) := by
      refine le_antisymm (fun x hx => ?_) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_)
      · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 (RingHom.mem_ker.1 hx))
      · exact RingHom.mem_ker.2 (RingHom.mem_ker.1 hb)
    have hkerψ : RingHom.ker ψ =
        Ideal.span {x | x ∈ l'.map (Ideal.Quotient.mk (Ideal.span {t}))} := by
      rw [hker, hk, Ideal.map_span]
      have hset : (Ideal.Quotient.mk (Ideal.span {t})) '' {x | x ∈ t :: l'} =
          insert 0 {x | x ∈ l'.map (Ideal.Quotient.mk (Ideal.span {t}))} := by
        ext x
        simp only [List.mem_cons, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, List.mem_map]
        constructor
        · rintro ⟨a, rfl | ha, rfl⟩
          · exact Or.inl h0
          · exact Or.inr ⟨a, ha, rfl⟩
        · rintro (rfl | ⟨a, ha, rfl⟩)
          · exact ⟨t, Or.inl rfl, h0⟩
          · exact ⟨a, Or.inr ha, rfl⟩
      rw [hset, Ideal.span_insert_zero]
    have hkm' : RingHom.ker ψ ≤ IsLocalRing.maximalIdeal (B ⧸ Ideal.span {t}) :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)
    have hmk' : IsLocalRing.maximalIdeal (B ⧸ Ideal.span {t}) * RingHom.ker ψ = ⊥ := by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have ha : a ∈ IsLocalRing.maximalIdeal B := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
        exact fun h => hx (h.map _)
      have hb : b ∈ RingHom.ker φ := RingHom.mem_ker.2 (RingHom.mem_ker.1 hy)
      have hab : a * b = 0 := by
        have := Ideal.mul_mem_mul ha hb
        rw [hmk] at this
        simpa using this
      rw [Ideal.mem_bot, ← map_mul, hab, map_zero]
    have hlen : (l'.map (Ideal.Quotient.mk (Ideal.span {t}))).length = n := by
      simpa using hl
    have hψ := ih (B ⧸ Ideal.span {t}) C ψ _ hlen hψs hkerψ hkm' hmk'
    rw [← hcomp]
    exact liftsVia_comp A M _ _ hprin hψ

end GlobalTheory.DualCon.LiftInduct

namespace GlobalTheory.DualCon

theorem liftsAlong_of_principal : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U : Over (Sp R)) (M : LB (A ⊗ U).left), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t})) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → LiftsAlong A M B I := by
  intro R _ A _ U M hyp B _ _ _ I hI hmI
  obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
  refine LiftInduct.liftsVia_of_list A M hyp _ B (B ⧸ I) (Ideal.Quotient.mk I) s.toList rfl
    Ideal.Quotient.mk_surjective ?_ ?_ ?_
  · rw [Ideal.mk_ker, ← hs]
    congr 1
    ext x
    simp
  · rwa [Ideal.mk_ker]
  · rwa [Ideal.mk_ker]

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointFactorsOpenImmersion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory

theorem localSpec_fac_of_closedPoint_mem_range (S : Type) [CommRing S] [IsLocalRing S] (X : Scheme.{0})
    (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (yb : Sp S ⟶ X) (hξ : IsOpenImmersion ξ)
    (hc : yb (IsLocalRing.closedPoint S) ∈ Set.range ξ) : ∃ φ : R →+* S, spMap φ ≫ ξ = yb := by
  have hrange : Set.range yb ⊆ Set.range ξ := by
    rintro _ ⟨x, rfl⟩
    have hsp : x ⤳ IsLocalRing.closedPoint S := IsLocalRing.specializes_closedPoint x
    exact (hsp.map yb.base.hom.continuous).mem_open ξ.isOpenEmbedding.isOpen_range hc
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ξ yb hrange)).hom, ?_⟩
  show Spec.map (Spec.preimage _) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

example : ∀ (S : Type) [CommRing S] [IsLocalRing S] (X : Scheme.{0}) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (yb : Sp S ⟶ X), IsOpenImmersion ξ → yb (IsLocalRing.closedPoint S) ∈ Set.range ξ → ∃ φ : R →+* S, spMap φ ≫ ξ = yb := @localSpec_fac_of_closedPoint_mem_range

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationUnitsChartsStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_units_charts : ∀ (p n : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X) (Xw : X.Opens)
    (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (J : Type) (Q : J → R)
    (u : ∀ j, (Localization.Away ((p : R) * Q j))ˣ),
    (∀ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ) → (∃ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖) ∧
      ∀ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖ → ∀ ψ : Localization.Away ((p : R) * Q j) →+* ℂ_[p],
        ψ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
          ∀ κ ∈ K (spMap φ ≫ ξ), ‖ψ (u j) - κ‖ < ‖κ‖) →
    (∀ yb' : Sp 𝓞_ℂ_[p] ⟶ X', IsTest p (π ⁻¹ᵁ Xw) yb' → IsTest p Xw (yb' ≫ π)) →
    ∀ (R' : Type) [CommRing R'] (χ : Sp R' ⟶ X') (g : R →+* R') (x' : X'), IsOpenImmersion χ → x' ∈ Set.range χ →
      χ ≫ π = spMap g ≫ ξ →
      (((π ⁻¹ᵁ Xw : X'.Opens) : Set X').Nonempty → ∃ φ : R' →+* 𝓞_ℂ_[p], IsTest p (π ⁻¹ᵁ Xw) (spMap φ ≫ χ)) →
      ((∃ k, (∀ j, g (Q k) ∣ g (Q j)) ∧ g (Q k) ∣ (p : R') ^ n) ∨ ∀ j, (p : R') ^ n ∣ g (Q j)) →
      UnitChartAt p (π ⁻¹ᵁ Xw) (fun yb' => K (yb' ≫ π)) x' := by
  first | exact @GlobalTheory.FlatModel.unitChartAt_of_dvd | exact GlobalTheory.FlatModel.unitChartAt_of_dvd | (intros; apply GlobalTheory.FlatModel.unitChartAt_of_dvd <;> assumption)
end
end

