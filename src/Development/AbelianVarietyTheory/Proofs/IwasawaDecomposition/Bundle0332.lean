import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemFaceLevelMultiplicity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.DefiniteMult

theorem toMap_mem_levP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → R.cX.toMap R.prX Fn ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB b t Fn hFn hP
  have h := GlobalTheory.DefiniteEnd.isMultMap_toMap hB.models.inf D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX hB.models.cX
    hB.models.prX hFn
  refine (mem_multT R.θ R.MX _ _ _).2 (Submodule.subset_span ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩)
  have hkC : k ∈ GfC D.sp.X' := hk.1
  obtain ⟨hiff, hchi⟩ := GlobalTheory.T.mem_level_group_face_level_iff_flag_group D G Pl0 T A Ks R F hB.grp.red_R b t k hkC
  have hh := hiff.1 hk
  obtain ⟨hq, hp⟩ := hh
  have hc := hchi hq hp
  have hd := hP ⟨_, hq⟩ hp ((finHom D.sp.X').rangeRestrict g)
  have e : Fn ((finHom D.sp.X').rangeRestrict (g * k)) =
      levChi _ R.βX (datXP R t (R.levR F b)) k • Fn ((finHom D.sp.X').rangeRestrict g) :=
    (congrArg Fn (map_mul _ g k)).trans (hd.trans (congrArg (· • Fn ((finHom D.sp.X').rangeRestrict g)) hc.symm))
  have e2 : R.cX.ext Fn (g * k) = levChi _ R.βX (datXP R t (R.levR F b)) k • R.cX.ext Fn g :=
    ((congrArg (R.cX.ρ (g * k)⁻¹) e).trans
      (LinearMap.congr_fun (rho_right_inv R.cX.ρ g (hB.models.cX.1 _ (inv_mem hkC))) _)).trans (map_smul _ _ _)
  exact (congrArg (fun w => R.prX w (PiTensorProduct.tprod ℂ v)) e2).trans (LinearMap.congr_fun (map_smul R.prX _ _) _)

end GlobalTheory.DefiniteMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalIsometryIsometric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions

namespace GlobalTheory.HermIsom

theorem isometric_of_ratIsom : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (L M : HermLB p), RatIsom L M → L.Isometric M := by
  intro k _ X _ p L M ⟨D, r, r', h, h', hφ⟩
  choose a ha using fun q : M.B.ι × L.B.ι => exists_unit_fnOf_eq (U := M.B.U q.1 ⊓ L.B.U q.2)
    fun x hx => (h.isEqn _ x hx.2).iff_unitAt.1 (h'.isEqn _ x hx.1)
  refine ⟨⟨a⟩, fun p q => Units.ext (Cartier.fn_ext fun hpq => ?_), fun σ j i y hj hi => ?_⟩
  · have e := congrArg (fnOf (L.B.U p.2 ⊓ L.B.U q.2) (memInf hpq.1.2 hpq.2.2)) (L.B.g p.2 q.2).inv_mul
    rw [map_mul, map_one] at e
    refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ hpq _) (fnOf_resG _ hpq _)))
      (fnOf_resG _ hpq _))).symm)
    refine (ha p _).trans (Eq.trans ?_ (congrArg _ (ha q _)).symm)
    rw [h.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2), h'.isRatSec p.1 q.1 (memInf hpq.1.1 hpq.2.1),
      mul_div_mul_comm, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_left e]
    rfl
  · have hy : y ∈ ptsIn p σ (M.B.U j ⊓ L.B.U i) := mem_ptsIn_inf.2 ⟨hj, hi⟩
    have hg : genericPoint X ∈ M.B.U j ⊓ L.B.U i := gen_mem (mem_ptsIn.1 hy)
    rw [hφ σ y i j hi hj, Units.val_div_eq_div_val, ← ha (j, i) hg, ratVal_fnOf hy hg]
    rfl

end GlobalTheory.HermIsom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSectionExtension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

set_option autoImplicit false

namespace GlobalTheory.RestrictRatSec

theorem top_le_of_below {K : Type} [Field K] {Z : Scheme.{0}} (y : Sp K ⟶ Z) {U : Z.Opens}
    (hy : below y ∈ U) : ⊤ ≤ y ⁻¹ᵁ U := fun x _ => by
  have : x = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]
  exact hy

theorem valAt_appLE {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) (y : Sp K ⟶ Y)
    (z : Sp K ⟶ X) (e : z = y ≫ j) {U : X.Opens} {W : Y.Opens} (l : W ≤ j ⁻¹ᵁ U) (hW : below y ∈ W)
    (h : genericPoint Y ∈ W) (hz : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(X, U)) :
    valAt y (fnOf W h ((j.appLE U W l).hom a)) =
      (z.appLE U ⊤ hz ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom a := by
  subst e
  rw [OfModel.valAt_fnOf y hW (top_le_of_below y hW), ← Scheme.Hom.appLE_comp_appLE y j U W ⊤ l
    (top_le_of_below y hW)]
  rfl

theorem mem_pullU {X Y : Scheme.{0}} (B : LB X) (j : Y ⟶ X) (c : (B.pull j).ι) (x : Y) :
    x ∈ (B.pull j).U c ↔ j x ∈ B.U (c PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem inf_le_pull {X Y : Scheme.{0}} (B : LB X) (j : Y ⟶ X) (c c' : (B.pull j).ι) :
    (B.pull j).U c ⊓ (B.pull j).U c' ≤ j ⁻¹ᵁ (B.U (c PUnit.unit) ⊓ B.U (c' PUnit.unit)) :=
  fun x hx => ⟨(mem_pullU B j c x).1 hx.1, (mem_pullU B j c' x).1 hx.2⟩

theorem val_pull_g {X Y : Scheme.{0}} (B : LB X) (j : Y ⟶ X) (c c' : (B.pull j).ι) :
    ((B.pull j).g c c').val =
      (j.appLE _ _ (inf_le_pull B j c c')).hom (B.g (c PUnit.unit) (c' PUnit.unit)).val := by
  have : (B.pull j).g c c' =
      res (inf_le_pull B j c c') (pullU j _ (B.g (c PUnit.unit) (c' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  rw [this]
  rfl

theorem exists_lift {X Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [SurjectiveOnStalks j] (x : Y)
    {f : Y.functionField} (hf : UnitAt x f) :
    ∃ (W : X.Opens) (hx : j x ∈ W) (a : Γ(X, W)), j x ∈ X.basicOpen a ∧
      fnOf (j ⁻¹ᵁ W) (gen_mem (x := x) hx) ((j.appLE W _ le_rfl).hom a) = f := by
  obtain ⟨b, -, hb⟩ := id hf
  obtain ⟨b', rfl⟩ := j.stalkMap_surjective x b
  obtain ⟨W, hx, a, rfl⟩ := X.presheaf.exists_germ_eq b'
  have e : fnOf (j ⁻¹ᵁ W) (gen_mem (x := x) hx) ((j.app W).hom a) = f := by
    rw [← algebraMap_germ (x := x) hx, ← hb]
    exact congrArg _ (Scheme.Hom.germ_stalkMap_apply j W x hx a).symm
  refine ⟨W, hx, a, ?_, by rw [← Scheme.Hom.app_eq_appLE]; exact e⟩
  have := (unitAt_fnOf_iff (U := j ⁻¹ᵁ W) (x := x) hx _ _).1 (e ▸ hf)
  rw [← Scheme.preimage_basicOpen] at this
  exact this

theorem exists_restriction : ∀ (X Y Z : Scheme.{0}) [IsIntegral Y] [IsIntegral Z] (j : Y ⟶ X) [SurjectiveOnStalks j] (i : Z ⟶ X) (x : Y), i (genericPoint Z) = j x → ∀ (B : LB X), B.IsLB → ∀ (r : (B.pull j).ι → Y.functionFieldˣ), IsRatSec (B.pull j) r → ∀ (u : Y.functionFieldˣ), (∀ c, x ∈ (B.pull j).U c → UnitAt x ((u * r c : Y.functionFieldˣ) : Y.functionField)) → ∃ s : (B.pull i).ι → Z.functionFieldˣ, IsRatSec (B.pull i) s ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Y) (y' : Sp K ⟶ Z) (c : B.ι), y ≫ j = y' ≫ i → below y = x → below y' = genericPoint Z → j x ∈ B.U c → valAt y' (s (fun _ => c) : Z.functionField) = valAt y ((u * r (fun _ => c) : Y.functionFieldˣ) : Y.functionField) := by
  intro X Y Z _ _ j _ i x hi B hB r hr u hu
  obtain ⟨c₀, hc₀⟩ := exists_chart hB (j x)
  have hx₀ : x ∈ (B.pull j).U (fun _ => c₀) := (mem_pullU B j _ x).2 hc₀
  obtain ⟨W, hW, a, ha, e⟩ := exists_lift j x (hu _ hx₀)
  have hgW : genericPoint Z ∈ i ⁻¹ᵁ W := show i _ ∈ W from hi ▸ hW
  have hg₀ : genericPoint Z ∈ (B.pull i).U (fun _ => c₀) := (mem_pullU B i _ _).2 (hi ▸ hc₀)
  have hne : fnOf (i ⁻¹ᵁ W) hgW ((i.appLE W _ le_rfl).hom a) ≠ 0 := by
    refine UnitAt.ne_zero (x := genericPoint Z) ((unitAt_fnOf_iff hgW _ _).2 ?_)
    rw [← Scheme.Hom.app_eq_appLE, ← Scheme.preimage_basicOpen]
    exact show i _ ∈ X.basicOpen a from hi ▸ ha
  refine ⟨fun c => frameRat (B.pull i) _ hg₀ c * Units.mk0 _ hne, fun c c' h => ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, isRatSec_frameRat (LB.isLB_pull hB i) _ hg₀ c c' h, mul_assoc]
  intro K _ y y' c hy hyx hy' hc
  have hxc : x ∈ (B.pull j).U (fun _ => c) := (mem_pullU B j _ x).2 hc
  have hgc : genericPoint Z ∈ (B.pull i).U (fun _ => c) := (mem_pullU B i _ _).2 (hi ▸ hc)
  have hb : below (y ≫ j) = j x := hyx ▸ rfl
  have h₁ : ⊤ ≤ (y ≫ j) ⁻¹ᵁ (B.U c ⊓ B.U c₀) := top_le_of_below _ (hb ▸ memInf hc hc₀)
  have h₂ : ⊤ ≤ (y ≫ j) ⁻¹ᵁ W := top_le_of_below _ (hb ▸ hW)
  have hxx := memInf hxc hx₀
  have hgg := memInf hgc hg₀
  have e₁ : ((u * r (fun _ => c) : Y.functionFieldˣ) : Y.functionField) =
      fnOf _ (gen_mem hxx) ((B.pull j).g (fun _ => c) (fun _ => c₀)).val *
        ((u * r (fun _ => c₀) : Y.functionFieldˣ) : Y.functionField) := by
    rw [Units.val_mul, Units.val_mul, hr _ _ (gen_mem hxx), mul_left_comm]
  have hxW : x ∈ j ⁻¹ᵁ W := hW
  rw [← hyx] at hxx hxW
  rw [← hy'] at hgg hgW
  have v₁ := valAt_appLE j y _ rfl (inf_le_pull B j (fun _ => c) (fun _ => c₀)) hxx (gen_mem hxx) h₁
    (B.g c c₀).val
  have v₂ := valAt_appLE i y' _ hy (inf_le_pull B i (fun _ => c) (fun _ => c₀)) hgg (gen_mem hgg) h₁
    (B.g c c₀).val
  have w₁ := congrArg (fun t => valAt y (fnOf _ (gen_mem hxx) t)) (val_pull_g B j (fun _ => c) (fun _ => c₀))
  have w₂ := congrArg (fun t => valAt y' (fnOf _ (gen_mem hgg) t)) (val_pull_g B i (fun _ => c) (fun _ => c₀))
  have t₁ := valAt_appLE j y _ rfl le_rfl hxW (gen_mem hxW) h₂ a
  have t₂ := valAt_appLE i y' _ hy le_rfl hgW (gen_mem hgW) h₂ a
  rw [e₁, ← e, OfModel.valAt_mul y (regAt_fnOf hxx _ _) (regAt_fnOf hxW _ _), Units.val_mul, Units.val_mk0]
  refine (congrArg (fun t => valAt y' (t * _)) (val_frameRat _ hg₀ _ hgc)).trans ?_
  refine (OfModel.valAt_mul y' (regAt_fnOf hgg _ _) (regAt_fnOf hgW _ _)).trans ?_
  exact congrArg₂ (· * ·) ((w₂.trans v₂).trans (w₁.trans v₁).symm) (t₂.trans t₁.symm)

end GlobalTheory.RestrictRatSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RatAnnih

section Scalar

variable {F : Type} [Field F] [NumberField F]

theorem inf_rat (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ)) (y : Ainf F)
    (h : ∀ c : 𝓞 F, ∃ n : ℤ, L (y * algebraMap F _ (c : F)) = n) : ∃ d : F, y = algebraMap F _ d := by
  classical
  have hb : ∀ i, ∃ n : ℤ, L (y * algebraMap F _ (integralBasis F i)) = n := fun i => by
    rw [integralBasis_apply]; exact h _
  choose n hn using hb
  refine ⟨∑ i, (n i : F) * (integralBasis F).traceDual i, funext fun v => ?_⟩
  let φ : Ainf F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding v).comp (Pi.evalRingHom _ v)
  have hφ : Continuous φ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
  have key : (fun w : Ainf F => φ w) = fun w => ∑ i, L (w * algebraMap F _ (integralBasis F i)) *
      φ (algebraMap F _ ((integralBasis F).traceDual i)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hφ
      (continuous_finset_sum _ fun i _ => (hL.comp (continuous_id.mul continuous_const)).mul continuous_const) ?_
    funext x
    simp only [Function.comp_apply, ← map_mul, hT]
    conv_lhs => rw [← (integralBasis F).traceDual.sum_repr x]
    simp only [map_sum, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul,
      eq_ratCast]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← RingHom.comp_apply φ (algebraMap F (Ainf F)), map_ratCast]
  apply (InfinitePlace.Completion.extensionEmbedding v).injective
  change φ y = φ (algebraMap F (Ainf F) _)
  rw [congrFun key y]
  simp only [hn, map_sum, map_mul, map_intCast]

theorem fin_eq_zero {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (hv : ∀ v, ∃ y, psiV F ψ v y ≠ 1) (l : Af F)
    (h : ∀ c : F, ψ (pairA F 0 (l * algebraMap F _ c)) = 1) : l = 0 := by
  classical
  have hp : Continuous fun y : Af F => pairA F 0 (l * y) :=
    Continuous.prodMk continuous_const (continuous_const.mul continuous_id)
  have hall : ∀ z : Af F, ψ (pairA F 0 (l * z)) = 1 := by
    intro z
    obtain ⟨x, β, hβ, rfl⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 z
    have h1 : ψ (pairA F 0 (l * β)) = 1 :=
      GlobalTheory.IntDense.mem_of_isClosed F (C := {y | ψ (pairA F 0 (l * y)) = 1})
        (isClosed_eq (hψ.comp hp) continuous_const) (fun a => h a) β hβ
    have e : pairA F 0 (l * (algebraMap F _ x + 1 • β)) =
        pairA F 0 (l * algebraMap F _ x) + pairA F 0 (l * β) := by
      rw [one_smul, mul_add]
      exact Prod.ext (add_zero _).symm rfl
    rw [e, ψ.map_add_eq_mul, h, h1, one_mul]
  have hext : ∀ a b : Af F, (∀ w, evalV F w a = evalV F w b) → a = b := fun a b hab =>
    Subtype.ext (funext hab)
  refine hext _ _ fun v => ?_
  by_contra hne
  rw [map_zero] at hne
  obtain ⟨y, hy⟩ := hv v
  have same : ∀ t, evalV F v (singleV F v t) = t := fun t => RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v t
  have diff : ∀ t w, w ≠ v → evalV F w (singleV F v t) = 0 := fun t w hw => RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) t hw
  refine hy ?_
  rw [psiV, ← hall (singleV F v ((evalV F v l)⁻¹ * y))]
  congr 2
  refine hext _ _ fun w => ?_
  by_cases hw : w = v
  · subst hw
    rw [map_mul, same, same, mul_inv_cancel_left₀ hne]
  · rw [map_mul, diff _ _ hw, diff _ _ hw, mul_zero]

theorem adele_rat {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (hv : ∀ v, ∃ y, psiV F ψ v y ≠ 1)
    (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ))
    (hinf : ∀ x, psiInf F ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x))) (a : AF F)
    (h : ∀ c : F, ψ (a * algebraMap F _ c) = 1) : ∃ d : F, a = algebraMap F _ d := by
  have hsub : ∀ (b : AF F) (x : F), (∀ c : F, ψ (b * algebraMap F _ c) = 1) →
      ∀ c : F, ψ ((b - algebraMap F _ x) * algebraMap F _ c) = 1 := fun b x hb c => by
    rw [sub_mul, ← map_mul, AddChar.map_sub_eq_div, hb, hψ.2.2.1, div_one]
  obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 (sndA F a)
  have h1 := hsub a x h
  have hβ' : sndA F (a - algebraMap F _ x) = β := by
    rw [map_sub, AlgHom.commutes, hx, one_smul, add_sub_cancel_left]
  obtain ⟨d, hd⟩ := inf_rat L hL hT (fstA F (a - algebraMap F _ x)) fun c => by
    have h2 : ψ (pairA F 0 (β * algebraMap F _ (c : F))) = 1 := by
      refine GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 c (fun r => ?_) β hβ
      have h3 := GlobalTheory.StdAdelicChar.ratChar_integer F (r * c)
      rw [GlobalTheory.StdRat.char_fin_rat ψ hψ, hinf, hT, map_neg, ← h3, GlobalTheory.StdAdelicChar.ratChar]
      congr 1
      push_cast
      ring
    have e : (a - algebraMap F _ x) * algebraMap F _ (c : F) =
        pairA F (fstA F (a - algebraMap F _ x) * algebraMap F _ (c : F)) 0 +
          pairA F 0 (β * algebraMap F _ (c : F)) := by
      rw [← hβ']
      exact Prod.ext (add_zero _).symm (zero_add _).symm
    have h4 := h1 c
    rw [e, ψ.map_add_eq_mul, h2, mul_one] at h4
    have h5 := (hinf _).symm.trans h4
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h5
    refine ⟨-n, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
    push_cast
    linear_combination -hn
  have h6 := hsub _ d h1
  have h7 : fstA F (a - algebraMap F _ x - algebraMap F _ d) = 0 := by
    rw [map_sub, AlgHom.commutes, hd, sub_self]
  have h8 := fin_eq_zero hψ.1 hv (sndA F (a - algebraMap F _ x - algebraMap F _ d)) fun c => by
    rw [← h6 c]
    congr 1
    refine Prod.ext ?_ rfl
    change 0 = fstA F (a - algebraMap F _ x - algebraMap F _ d) * _
    rw [h7, zero_mul]
  refine ⟨x + d, ?_⟩
  rw [map_add, ← sub_eq_zero, ← sub_sub]
  exact Prod.ext h7 h8

end Scalar

theorem tensor_rat {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {R : Type} [CommRing R] [Algebra F R] (z : R ⊗[F] E)
    (h : ∀ e : E, ∃ d : F, Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e * z) = algebraMap F R d) :
    ∃ e : E, z = (1 : R) ⊗ₜ[F] e := by
  classical
  let b := Module.finBasis F E
  have key : ∀ z : R ⊗[F] E,
      z = ∑ i, Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] b i * z) ⊗ₜ[F] b.traceDual i := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [mul_add, map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | tmul a e =>
      conv_lhs => rw [← b.traceDual.sum_repr e, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, GlobalTheory.LatVac.trace_tmul, Module.Basis.traceDual_repr_apply,
        Algebra.traceForm_apply, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm, mul_comm e]
  choose d hd using h
  refine ⟨∑ i, d (b i) • b.traceDual i, ?_⟩
  rw [key z, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem trace_mul_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E]
    {R : Type} [CommRing R] [Algebra F R] (z : R ⊗[F] E) (e : E) (c : F) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e * z) * algebraMap F R c =
      Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] (c • e) * z) := by
  rw [mul_comm, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc, algebraMap_smul, ← TensorProduct.tmul_smul]

theorem sum_single {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {m n : ℕ} (P : Matrix (Fin m) (Fin m) E)
    (Q : Matrix (Fin n) (Fin n) E) (hP : IsUnit P.det) (hQ : IsUnit Q.det) (a₀ : Fin m) (d₀ : Fin n) (e : E)
    (x : Fin n → Fin m → A) :
    ∑ a, ∑ b, ∑ c, ∑ d, ι (P⁻¹ a b) * ι ((P * Matrix.single a₀ d₀ e * Q⁻¹) b c) * ι (Q c d) * x d a =
      ι e * x d₀ a₀ := by
  have h1 : P⁻¹ * (P * Matrix.single a₀ d₀ e * Q⁻¹) * Q = Matrix.single a₀ d₀ e := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ hP]
  generalize P * Matrix.single a₀ d₀ e * Q⁻¹ = M at h1
  have h2 : ∀ a, ∑ b, ∑ c, ∑ d, ι (P⁻¹ a b) * ι (M b c) * ι (Q c d) * x d a =
      ∑ d, ι (Matrix.single a₀ d₀ e a d) * x d a := fun a => by
    rw [← h1]
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm
  simp only [h2]
  rw [Finset.sum_eq_single a₀, Finset.sum_eq_single d₀, Matrix.single_apply_same]
  · intro d _ hd
    rw [Matrix.single_apply_of_col_ne _ _ hd.symm, map_zero, zero_mul]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun d _ => by rw [Matrix.single_apply_of_row_ne ha.symm, map_zero, zero_mul]
  · simp

theorem exists_symplO_eq {D : D7} (S T : HSp D) (x : WO S T) (i : Fin T.rank) (j : Fin S.rank) (e : D.host.E) :
    ∃ γ ∈ ratL T S, symplO S T x γ = Algebra.trace (AF D.host.F) (AE D) (incA D e * x i j) := by
  refine ⟨ratW T S fun c b => star ((S.gram * Matrix.single j i (D.host.xi0⁻¹ * e) * T.gram⁻¹) b c), ⟨_, rfl⟩, ?_⟩
  have h := sum_single (incA D) S.gram T.gram (GlobalTheory.LatVac.gram_det_isUnit S) (GlobalTheory.LatVac.gram_det_isUnit T) j i
    (D.host.xi0⁻¹ * e) x
  have h2 : hO S T x (ratW T S fun c b =>
      star ((S.gram * Matrix.single j i (D.host.xi0⁻¹ * e) * T.gram⁻¹) b c)) =
      incA D (D.host.xi0⁻¹ * e) * x i j := by
    rw [← h, hO]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    exact congrArg (fun t => incA D (S.gram⁻¹ a b) * t * incA D (T.gram c d) * x d a)
      ((GlobalTheory.DualPairCheck.cA_incA _).trans (congrArg (incA D) (star_star _)))
  rw [symplO, h2, ← mul_assoc, ← RingHom.map_mul, mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]

theorem ratL_annihilator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x : WO S T), (∀ γ ∈ ratL T S, ψ (symplO S T x γ) = 1) ↔ x ∈ ratL T S := by
  intro D ψ hψ S T x
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  constructor
  · intro h
    obtain ⟨θ, hθ⟩ := hψ.2.1
    let L : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))) fun a b => by
      simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
    have hrat := adele_rat hψ.1 (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) L
      (continuous_finset_sum _ fun ρ _ => (hθ ρ).2)
      (fun x => by
        show ∑ ρ, θ ρ (algebraMap D.host.F (Ainf D.host.F) x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace])
      (fun y => by
        rw [hψ.2.2 θ hθ]
        congr 1
        change _ = -(_ * ∑ ρ, θ ρ (y ⊗ₜ[D.host.F] (1 : D.host.E)))
        push_cast
        ring)
    have hent : ∀ i j, ∃ e : D.host.E, x i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := fun i j =>
      tensor_rat (x i j) fun e => hrat _ fun c => by
        obtain ⟨γ, hγ, hγe⟩ := exists_symplO_eq S T x i j (c • e)
        exact (congrArg ψ ((trace_mul_algebraMap (x i j) e c).trans hγe.symm)).trans (h γ hγ)
    choose M hM using hent
    exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩
  · rintro ⟨γ, rfl⟩ _ ⟨γ', rfl⟩
    obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D S T γ γ'
    exact (congrArg ψ ha).trans (hψ.1.2.2.1 a)

end GlobalTheory.RatAnnih

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalityDimPairingEqInner
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.TopSchur

theorem riesz {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, ℓ w = ⟪a, w⟫_ℂ :=
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap ℓ), fun w => by
    rw [InnerProductSpace.toDual_symm_apply]; rfl⟩

theorem exists_vec_prod_ne {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {W : Type}
    [AddCommGroup W] [Module ℂ W] (pr : W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (hpr : pr ≠ 0) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  classical
  have hτ : ∀ τ, ∃ x : M.sm τ, x ≠ 0 := by
    intro τ
    by_contra hz
    push_neg at hz
    apply hpr
    have hs : ∀ s : SmT M, s = 0 := by
      intro s
      induction s using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero τ (hz (f τ)), smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    refine LinearMap.ext fun w => LinearMap.ext fun s => ?_
    rw [hs s]
    simp
  choose v hv using hτ
  refine ⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => inner_self_ne_zero.mpr ?_⟩
  intro h0
  exact hv τ (Subtype.ext h0)

theorem alg_step {d I p q x : ℂ} (hd : d ≠ 0) (hI : d * I = q * x) (hq : q = p) : I = x / d * p := by
  subst hq
  field_simp
  linear_combination hI

theorem dualNumber_unit_mul_decomposition {P c d x : ℂ} (hP : P = d) (hc : c = x / d) (hd : d ≠ 0) : P * c = x := by
  subst hP hc
  field_simp

set_option maxHeartbeats 400000 in

theorem topSchur : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (t : T) (h h' : (R.HX t).H), (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) * ipMT R.MX (R.νX t) (R.fdX t) (R.cX.toMap R.prX ((R.HX t).e h)) (R.cX.toMap R.prX ((R.HX t).e h')) = ⟪h, h'⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hP t h h'
  classical
  have hC := GlobalTheory.T.finrank_coefficient_space_eq_prod_real_models D G Pl0 T A Ks R F hB
  haveI hWnt : Nontrivial R.cX.W := hB.models.cX.2.2.2.1
  have hd0 : (Module.finrank ℂ R.cX.W : ℂ) ≠ 0 := by
    have := Module.finrank_pos (R := ℂ) (M := R.cX.W)
    exact_mod_cast this.ne'
  have hcast : (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) = (Module.finrank ℂ R.cX.W : ℂ) := by
    rw [hC]; push_cast; rfl
  have key : ∀ v v' : R.MX.Vec,
      IntegrableOn (fun g => star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) *
        R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v')) (R.fdX t) (R.νX t) ∧
      ∫ g in R.fdX t, star (R.prX (R.cX.ext ((R.HX t).e h) g) (PiTensorProduct.tprod ℂ v)) *
        R.prX (R.cX.ext ((R.HX t).e h') g) (PiTensorProduct.tprod ℂ v') ∂(R.νX t) =
      ⟪h, h'⟫_ℂ / (Module.finrank ℂ R.cX.W : ℂ) * ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
    intro v v'
    have hr : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ := riesz (R.prX.flip _)
    have hr' : ∃ a : R.cX.W, ∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a, w⟫_ℂ := riesz (R.prX.flip _)
    obtain ⟨a, ha⟩ := hr
    obtain ⟨a', ha'⟩ := hr'
    have hA := GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients D G Pl0 T A Ks R F hB t h h' a a'
    obtain ⟨hint, hval⟩ := hA
    have hab := GlobalTheory.T.riesz_vectors_pure_tensors_inner_eq_prod D G Pl0 T A Ks R F hB hP v v' a a' ha ha'
    simp only [ha, ha']
    refine ⟨hint, ?_⟩
    exact alg_step hd0 hval hab
  have hv := exists_vec_prod_ne R.MX R.prX hB.models.prX.1
  obtain ⟨v0, hv0⟩ := hv
  unfold ipMT Mult.ipM
  split_ifs with hex
  · have e1 := (hex.choose_spec v0 v0).2
    have hch : hex.choose * _ = _ * _ := e1.symm.trans (key v0 v0).2
    have hch' := mul_right_cancel₀ hv0 hch
    exact dualNumber_unit_mul_decomposition hcast hch' hd0
  · exfalso
    exact hex ⟨_, fun v v' => key v v'⟩

end GlobalTheory.Mem.TopSchur
end
end

