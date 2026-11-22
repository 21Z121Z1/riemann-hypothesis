import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatePrimitiveOfAmpleKTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PrimitiveNonSym
open GlobalTheory.PrimitiveOverField GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.UU

theorem exists_point_translate_of_ample : ∀ (A : Type) [Field A] [IsAlgClosed A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  intro K _ _ B _ _ g L O hB _ hLl _ hK hΘ hO hu
  by_contra hno
  have := hB.smooth
  have := hB.proper
  have hpr : IsProjBy B.hom := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K B hB
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.StabFlat.isProjBy_baseChange hpr h
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hLl) (fst B B) (snd B B) -
    CechPic.pull (snd B B).left (cls O hO))
  have hpq : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ B, (toUnit B ≫ x).left = B.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit B)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (toUnit B ≫ x) (𝟙 B)).left) =
      lam (cls L hLl) (toUnit B ≫ x) (𝟙 B) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (𝟙 B) (toUnit B ≫ x)).left) =
      lam (cls L hLl) (toUnit B ≫ x) (𝟙 B) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst B B).left ≫ B.hom) F := by
    refine (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
    refine ⟨(lift (toUnit B ≫ x') (𝟙 B)).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit B ≫ x') (𝟙 B))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit B ≫ x') (𝟙 B))
    · rw [s₁, lam_sub, lam_lam hLl hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero, lam_const]
      refine fun e => hno ⟨x', (cls_eq_iff hO (LB.isLB_linComb hLl _ _)).1 (e.symm.trans ?_)⟩
      refine Eq.trans ?_ (cls_linComb hLl _ _ _).symm
      rw [Fin.sum_univ_two, sub_eq_add_neg]
      exact (congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)).symm
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ B.left := η[B].left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hcl : IsClosed ({o (IsLocalRing.closedPoint K)} : Set B.left) := by
    have : IsClosedImmersion (o ≫ B.hom) := by rw [ho]; infer_instance
    have : IsClosedImmersion o := IsClosedImmersion.of_comp o B.hom
    have h := o.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
      (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
        Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
    exact (congrArg IsClosed Set.image_singleton).mp h
  have all := (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance inferInstance F hF).2
    _ hcl (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
      refine ⟨(lift (𝟙 B) (toUnit B ≫ x')).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ x'))
      · rw [s₂, lam_lam hLl hΘ]
      · rw [s₂]
        intro e
        have e₁ : x' = η[B] := (eq_one_of_lam_eq_zero hLl hK x' e).trans (by
          rw [Hom.one_def, toUnit_unit, Category.id_comp])
        have e₂ : x = o := congrArg CommaMorphism.left e₁
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (e₂ ▸ hy)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 B) (toUnit B ≫ η[B])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ η[B]))).trans (cst_left η[B]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ η[B])))
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : Nonempty B.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.PrimitiveNonSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatesInOpenSemiAbelianLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearMeet

theorem exists_fst_mul_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ V : G.left.Opens, (∃ y₀ ∈ V, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ z : (G ⊗ G).left, (fst G G).left z = y ∧ (fst G G * snd G G).left z ∈ V ∧ (fst G G * (snd G G)⁻¹).left z ∈ V := by
  intro R _ _ G _ hG V ⟨y₀, hy₀, e₀⟩ y
  have := hG.smooth
  have : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_isSemiAbelian G

  obtain ⟨y₁, hy₁, e₁⟩ : ∃ y₁ ∈ V, G.hom y₁ = G.hom y := by
    have hs : G.hom y ⤳ G.hom y₀ := by rw [e₀]; exact IsLocalRing.specializes_closedPoint _
    obtain ⟨y₁, h₁, h₂⟩ := (Flat.generalizingMap G.hom) hs
    exact ⟨y₁, h₁.mem_open V.2 hy₀, h₂⟩
  let f := fst G G
  let g := snd G G
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) y y₁ e₁.symm
  have hf : GeometricallyIrreducible f.left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst G.hom G.hom))
  have hwf : f.left w = y := hw1
  have hwg : g.left w = y₁ := hw2

  let bp : G ⊗ G ⟶ G ⊗ G := lift f (f⁻¹ * g)
  let bm : G ⊗ G ⟶ G ⊗ G := lift f (g⁻¹ * f)
  have bp1 : bp ≫ (f * g) = g := by
    rw [MonObj.comp_mul, lift_fst, lift_snd, mul_inv_cancel_left]
  have bm1 : bm ≫ (f * g⁻¹) = g := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have bp2 : bp ≫ f = f := lift_fst _ _
  have bm2 : bm ≫ f = f := lift_fst _ _
  have hi : IsIrreducible (f.left ⁻¹' {y}) := by
    rw [← f.left.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.left.fiberι y).continuous.continuousOn
  have mp : (bp.left w) ∈ f.left ⁻¹' {y} ∩ (f * g).left ⁻¹ᵁ V := by
    refine ⟨?_, ?_⟩
    · show f.left (bp.left w) = y
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bp2]; exact hwf
    · show (f * g).left (bp.left w) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bp1, hwg]; exact hy₁
  have mm : (bm.left w) ∈ f.left ⁻¹' {y} ∩ (f * g⁻¹).left ⁻¹ᵁ V := by
    refine ⟨?_, ?_⟩
    · show f.left (bm.left w) = y
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bm2]; exact hwf
    · show (f * g⁻¹).left (bm.left w) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bm1, hwg]; exact hy₁
  obtain ⟨z, hz, k₁, k₂⟩ := hi.2 _ _ ((f * g).left ⁻¹ᵁ V).2 ((f * g⁻¹).left ⁻¹ᵁ V).2 ⟨_, mp⟩ ⟨_, mm⟩
  exact ⟨z, hz, k₁, k₂⟩

end GlobalTheory.ShearMeet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemCodimOneRegularChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem gp_comp {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (h : X ⟶ Sp R) :
    gp X ≫ h = spMap (cst h) := by
  apply ext_of_isAffine
  rw [gp, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  ext a
  have e : CommRingCat.ofHom (cst h) =
      (Scheme.ΓSpecIso _).inv ≫ h.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := rfl
  simp [e]

theorem exists_pow_mul_mem {O K : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (hd : ringKrullDim O ≤ 1) {a : O} (ha : a ∈ maximalIdeal O) (v : K) :
    ∃ N : ℕ, ∃ c : O, algebraMap O K a ^ N * v = algebraMap O K c := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := O) v
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  haveI : Ring.KrullDimLE 1 O := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hrad : a ∈ (Ideal.span {y}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hne : J ≠ ⊥ := fun h => hy0 (by
      have := hJ (Ideal.mem_span_singleton_self y); rw [h] at this; exact (Submodule.mem_bot _).1 this)
    have : J.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot J hne
    rw [IsLocalRing.eq_maximalIdeal this]; exact ha
  obtain ⟨N, hN⟩ := hrad
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hN
  refine ⟨N, c * x, ?_⟩
  have hy' : algebraMap O K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  rw [← map_pow, ← hc, map_mul, map_mul]
  field_simp

theorem regAt_pow {X : Scheme.{0}} [IsIntegral X] {z : X} {g : X.functionField} (h : RegAt z g) (n : ℕ) :
    RegAt z (g ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one z).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem eq_of_specializes {X : Scheme.{0}} [IsIntegral X] {z w : X} (hd : ringKrullDim (X.presheaf.stalk z) ≤ 1)
    (hwz : w ⤳ z) (hw : w ≠ genericPoint X) : w = z := by
  by_contra hne
  have hw' : w ∈ Set.range (X.fromSpecStalk z) := by rw [Scheme.range_fromSpecStalk]; exact hwz
  obtain ⟨p, rfl⟩ := hw'
  have hη : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec X).specializes trivial
  obtain ⟨q, hq⟩ := hη
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hp : p.asIdeal = ⊥ := by
    by_contra h
    haveI := p.isPrime
    have hm := Ideal.isMaximal_of_isPrime_of_ne_bot p.asIdeal h
    have : p = closedPoint _ := PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
    apply hne; rw [this, Scheme.fromSpecStalk_closedPoint]
  have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
    show p.asIdeal ≤ q.asIdeal; rw [hp]; exact bot_le)
  have h1 : X.fromSpecStalk z p ⤳ genericPoint X := hq ▸ hpq.map (X.fromSpecStalk z).continuous
  have h2 : genericPoint X ⤳ X.fromSpecStalk z p := (genericPoint_spec X).specializes trivial
  exact hw (h1.antisymm h2).eq

theorem θ_comp_c₀ (σ : Setup) (x : Sp σ.R) :
    (σ.θ x).comp σ.c₀ = (cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl₁, hl₂⟩ := σ.hθ x
  have w := (σ.cart x).w
  simp only [Category.assoc] at w
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    calc spMap ((σ.θ x).comp σ.c₀) = spMap (σ.θ x) ≫ spMap σ.c₀ := by
          simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
      _ = l ≫ σ.φ x ≫ σ.A.hom ≫ awayMap σ.f := by
          rw [Setup.c₀, ← gp_comp, ← Category.assoc, ← hl₂]; simp only [Category.assoc]
      _ = l ≫ (σ.V x).ι ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) := by rw [w]
      _ = gp _ ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) := by rw [← Category.assoc l, hl₁]
      _ = spMap ((cst (σ.C x).G.hom).comp (σ.ρ x)) := by
          rw [← Category.assoc, gp_comp]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 e)
  simpa using e'

theorem zeroAt_cst {R : Type} [CommRing R] {Y : Scheme.{0}} [IsIntegral Y] (h : Y ⟶ Sp R) (r : R) (z : Y)
    (hz : r ∈ (h z).asIdeal) : ZeroAt z (cst h r) := by
  rw [zeroAt_iff]
  refine ⟨regAt_fnOf (U := ⊤) trivial trivial _, fun hu => ?_⟩
  have h1 := (unitAt_fnOf_iff (x := z) (U := ⊤) trivial (gen_mem (x := z) trivial) _).1 hu
  rw [RingHom.comp_apply, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h1
  exact h1 hz

theorem exists_pow_mul_mem_codimOne_regular_chart : ∀ (σ : Setup) (x : Sp σ.R) (u : σ.A.left.functionField), ∃ m : ℕ, σ.c₀ σ.f ^ m * u ∈ σ.W x := by
  intro σ x u
  haveI := (σ.C x).semi
  haveI : Smooth (σ.C x).G.hom := IsSemiAbelian.smooth
  haveI : QuasiCompact (σ.C x).G.hom := IsSemiAbelian.quasiCompact
  haveI : IsLocallyNoetherian (σ.C x).G.left := LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom
  haveI : CompactSpace (σ.C x).G.left := QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom
  haveI : IsNoetherian (σ.C x).G.left := {}
  haveI : TopologicalSpace.NoetherianSpace (σ.C x).G.left := IsNoetherian.noetherianSpace
  have hg : σ.θ x (σ.c₀ σ.f) = cst (σ.C x).G.hom (σ.ρ x σ.f) := RingHom.congr_fun (θ_comp_c₀ σ x) σ.f
  set g := cst (σ.C x).G.hom (σ.ρ x σ.f)
  set v := σ.θ x u
  let P : Set (σ.C x).G.left := {z | ¬ RegAt z v}
  have hP : IsClosed P := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hzU, a, ha⟩ := RegAt.exists_fnOf (not_not.1 hz)
    exact ⟨U, fun y hy => not_not.2 (ha ▸ regAt_fnOf hy _ a), U.isOpen, hzU⟩
  obtain ⟨S, hS, hirr, hPS⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible ⟨P, hP⟩
  let F : Set (σ.C x).G.left := ⋃ t ∈ S, {w | IsGenericPoint w (t : Set _)}
  have hF : F.Finite := hS.biUnion fun t _ => Set.Subsingleton.finite fun a ha b hb => ha.eq hb
  have hPt : ∀ t ∈ S, (t : Set (σ.C x).G.left) ⊆ P := fun t ht => by
    have : t ≤ sSup S := le_sSup ht
    rw [← hPS] at this
    exact this
  let C : TopologicalSpace.Closeds (σ.C x).G.left :=
    ⟨⋃ t ∈ S, (t : Set _), hS.isClosed_biUnion fun t _ => t.isClosed⟩
  have hPC : P ⊆ (C : Set _) := by
    have : sSup S ≤ C := sSup_le fun t ht y hy => Set.mem_iUnion₂.2 ⟨t, ht, hy⟩
    rw [← hPS] at this
    exact this
  have key : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → z ∈ P → z ∈ F := by
    intro z hz hzP
    obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 (hPC hzP)
    have hw : IsGenericPoint (hirr t ht).genericPoint (t : Set _) := by
      have := (hirr t ht).isGenericPoint_genericPoint_closure
      rwa [t.isClosed.closure_eq] at this
    have hwP : (hirr t ht).genericPoint ∈ P := hPt t ht hw.mem
    have hwη : (hirr t ht).genericPoint ≠ genericPoint _ := fun h => hwP (h ▸ regAt_genericPoint v)
    have := eq_of_specializes hz.1.le (hw.specializes hzt) hwη
    exact Set.mem_iUnion₂.2 ⟨t, ht, this ▸ hw⟩
  have hpt : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → ∃ N : ℕ, RegAt z (g ^ N * v) := by
    intro z hz
    obtain ⟨a, ha, hag⟩ := zeroAt_cst (σ.C x).G.hom (σ.ρ x σ.f) z hz.2
    obtain ⟨N, c, hc⟩ := exists_pow_mul_mem hz.1.le ha v
    exact ⟨N, c, by rw [← hc, hag]⟩
  classical
  let N : (σ.C x).G.left → ℕ := fun z => if h : Vert (σ.C x).G.hom (σ.ρ x σ.f) z then Classical.choose (hpt z h) else 0
  refine ⟨hF.toFinset.sup N, fun z hz => ?_⟩
  have hgz : RegAt z g := (zeroAt_cst (σ.C x).G.hom (σ.ρ x σ.f) z hz.2).regAt
  rw [map_mul, map_pow, hg]
  by_cases hzP : z ∈ P
  · have hle : N z ≤ hF.toFinset.sup N := Finset.le_sup (hF.mem_toFinset.2 (key z hz hzP))
    have hN : RegAt z (g ^ N z * v) := by
      simp only [N, dif_pos hz]; exact Classical.choose_spec (hpt z hz)
    rw [← Nat.sub_add_cancel hle, pow_add, _root_.mul_assoc]
    exact (regAt_pow hgz _).mul hN
  · exact (regAt_pow hgz _).mul (not_not.1 hzP)

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
section
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

def IsQuasiInv {Y : Scheme.{0}} {A B : Over Y} [GrpObj A] [GrpObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) : Prop :=
  IsMonHom ψ ∧ IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 A) ^ k ∧ ψ' ≫ ψ = (𝟙 B) ^ k

theorem IsQuasiInv.id {Y : Scheme.{0}} (A : Over Y) [GrpObj A] : IsQuasiInv 1 (𝟙 A) (𝟙 A) :=
  ⟨inferInstance, inferInstance, by rw [pow_one, Category.comp_id], by rw [pow_one, Category.comp_id]⟩

def IsAxesTriv {Y : Scheme.{0}} (B : Over Y) [GrpObj B] [IsCommMonObj B] (Q : LB (G2 B).left) : Prop :=
  Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) ∧
    ∃ t : (Q.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {Y : Scheme.{0}}
  {s : Y ⟶ Sp R}

theorem isAxesTriv_obj (o : Obj b N s) : IsAxesTriv o.A o.P := ⟨o.isLB, o.rig₁, o.rig₂⟩

def KerStableAt (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ : o.A ⟶ B) {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ g : T ⟶ o.A, g ≫ ψ = 1 →
    ∀ a : D.O, g ≫ o.act.act a ≫ ψ = 1

def PullPolTriv (o : Obj b N s) {B : Over Y} (ψ' : B ⟶ o.A) {T : Over Y} (x : T ⟶ B) : Prop :=
  ∃ τ : (o.P.pull (lift (fst B T ≫ ψ') (snd B T ≫ x ≫ ψ')).left).Gen, τ.IsGen

def PolKerAt (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ' : B ⟶ o.A) (c : ℕ) {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ x : T ⟶ B, x ^ (c ^ 3) = 1 →
    (PullPolTriv o ψ' x ↔ x ^ c = 1)

def TjAt (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o : Obj b N s) {B : Over Y} [GrpObj B] (ψ : o.A ⟶ B)
    {Tb : Scheme.{0}} (t : Tb ⟶ Y) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ Y), (∃ σ : Sp k ⟶ Tb, σ ≫ t = x) →
    (∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)

theorem tjAt_id_iff (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) :
    TjAt r w j o ψ (𝟙 Y) ↔ IsTj r w j o o' ψ :=
  ⟨fun h k _ _ _ x => h k x ⟨x, Category.comp_id x⟩, fun h k _ _ _ x _ => h k x⟩

theorem IsPIsog.kerStableAt {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog c o o' ψ)
    {Tb : Scheme.{0}} (t : Tb ⟶ Y) : KerStableAt o ψ t := by
  intro T _ _ g hg a
  haveI := o'.act.hom a
  rw [h.2.2.1, ← Category.assoc, hg, one_comp]

theorem IsPIsog.exists_quasiInv {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (h : IsPIsog c o o' ψ) :
    ∃ ψ' : o'.A ⟶ o.A, IsQuasiInv c ψ ψ' := by
  obtain ⟨-, h1, -, -, -, ψ', h2, h3, h4⟩ := h
  exact ⟨ψ', h1, h2, h3, h4⟩

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroupStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_abelianScheme_finiteFlat_subgroup : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (B : Over (Sp R)) (_ : GrpObj B) (q : A ⟶ B) (π : B ⟶ A), IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsFinite π.left ∧ IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
  first | exact @GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme | exact GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme | (intros; apply GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioUnitOfLineBundleGeneratorsOnOpens
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

theorem exists_ratio_unit : ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (O₁ O₂ : Y.Opens) (s₁ : ∀ k, Γ(Y, L.U k ⊓ O₁)ˣ) (s₂ : ∀ k, Γ(Y, L.U k ⊓ O₂)ˣ), GlobalTheory.PinchLift.GenOn L O₁ s₁ → GlobalTheory.PinchLift.GenOn L O₂ s₂ → ∃ r : Γ(Y, O₁ ⊓ O₂)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k → f t ∈ O₁ → f t ∈ O₂ → gm f t (O₁ ⊓ O₂) r = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
  intro Y L hL O₁ O₂ s₁ s₂ h₁ h₂
  have hW : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ O₁ ⊓ O₂ := fun k => inf_le_right
  have hc : O₁ ⊓ O₂ ≤ ⨆ k, L.U k ⊓ (O₁ ⊓ O₂) := fun y hy => by
    obtain ⟨k, hk⟩ := exists_chart hL y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, hy⟩
  have i₁ : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ L.U k ⊓ O₁ := fun k => inf_le_inf_left _ inf_le_left
  have i₂ : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ L.U k ⊓ O₂ := fun k => inf_le_inf_left _ inf_le_right
  let u : ∀ k, Γ(Y, L.U k ⊓ (O₁ ⊓ O₂))ˣ := fun k => res (i₁ k) (s₁ k) * (res (i₂ k) (s₂ k))⁻¹
  have hu : ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k ⊓ (O₁ ⊓ O₂) →
      gm f t (L.U k ⊓ (O₁ ⊓ O₂)) (u k) = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
    intro T f t k hy
    simp only [u, map_mul, map_inv, gm_res f t (i₁ k) hy, gm_res f t (i₂ k) hy]
  obtain ⟨r, hr⟩ := glue_unit (O₁ ⊓ O₂) (fun k => L.U k ⊓ (O₁ ⊓ O₂)) hW hc u (by
    intro k l y hy
    have hk : y ∈ L.U k ⊓ (O₁ ⊓ O₂) := hy.1
    have hl : y ∈ L.U l ⊓ (O₁ ⊓ O₂) := hy.2
    show gm (𝟙 Y) y (L.U k ⊓ (O₁ ⊓ O₂)) (u k) = gm (𝟙 Y) y (L.U l ⊓ (O₁ ⊓ O₂)) (u l)
    rw [hu Y (𝟙 Y) y k hk, hu Y (𝟙 Y) y l hl, h₁ k l y hk.1 hl.1 hk.2.1, h₂ k l y hk.1 hl.1 hk.2.2,
      ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div])
  refine ⟨r, fun T f t k hk ht₁ ht₂ => ?_⟩
  have hy : f t ∈ L.U k ⊓ (O₁ ⊓ O₂) := ⟨hk, ht₁, ht₂⟩
  rw [← gm_res f t (hW k) hy r, hr k, hu T f t k hy]

end GlobalTheory.PinchLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelationsLiftVanishingConductor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem relations_lift_vanishing : (∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G) → ∀ (R R' C' D E ν : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R R'] [Algebra R' C'] (c : Ideal R) [Algebra (R ⧸ c) D], (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D) (ξ : ν → C'), RingHom.ker π = c.map ((algebraMap R' C').comp (algebraMap R R')) → ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) = (π.comp (algebraMap R' C')).comp (algebraMap R R') → (∀ s, π (ξ s) = ψ (ζ s)) → Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → ∀ f : MvPolynomial ν (R ⧸ c), MvPolynomial.aeval ζ f = 0 → ∃ F : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) F = f ∧ MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F) = 0 := by
  intro hH R R' C' D E ν _ _ _ _ _ _ _ c _ hc π ψ ζ ξ hker hcomm hξ hsurj f hf
  obtain ⟨F₀, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk c) Ideal.Quotient.mk_surjective f
  have hπ : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀)) = 0 := by
    have h1 : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀))
        = ψ (MvPolynomial.aeval ζ (MvPolynomial.map (Ideal.Quotient.mk c) F₀)) := by
      rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map,
        MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hcomm]
      congr 1
      funext s
      exact hξ s
    rw [h1, hf, map_zero]
  have hmem : MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀) ∈
      ((c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R')).map
        (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') := by
    rw [Ideal.map_map]
    change _ ∈ Ideal.map ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C') _
    rw [Ideal.map_map]
    have : ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C').comp
        ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp (algebraMap R R'))
        = (algebraMap R' C').comp (algebraMap R R') := by
      ext x; simp
    rw [this, ← hker]
    exact hπ
  obtain ⟨G, hG, hGe⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hmem
  obtain ⟨H, hH0, hHG⟩ := hH R R' ν c hc G hG
  refine ⟨F₀ - H, ?_, ?_⟩
  · rw [map_sub, hH0, sub_zero]
  · rw [map_sub, hHG, map_sub, hGe, sub_self]

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCyclotomicAwayToFieldPrimitiveRoot
section
open GlobalTheory.SiegelTor

namespace GlobalTheory.CycLift

theorem exists_hom_to_field : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
    ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  intro M hM K _ y hy hMK
  obtain ⟨p, hcp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharZero (WittVector p K) := by
      obtain ⟨q, hq⟩ := CharP.exists (WittVector p K)
      have h1 : ((q : ℕ) : K) = 0 := by
        have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) (CharP.cast_eq_zero (WittVector p K) q)
        rwa [map_natCast, map_zero] at this
      have h2 : p ∣ q := (CharP.cast_eq_zero_iff K p q).1 h1
      rcases CharP.char_is_prime_or_zero (WittVector p K) q with h | h
      · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp h).1 h2
        subst h3
        exact absurd (CharP.cast_eq_zero (WittVector p K) p) (WittVector.p_nonzero p K)
      · subst h
        exact CharP.charP_to_charZero _
    let π : WittVector p K →+* K := WittVector.constantCoeff
    have hcc : ∀ x : K, π (WittVector.teichmuller p x) = x := fun x => by simp [π]
    have hu : IsPrimitiveRoot (WittVector.teichmuller p y) M :=
      ⟨by rw [← map_pow, hy.pow_eq_one, map_one], fun l hl => hy.dvd_of_pow_eq_one l (by
        have := congrArg π hl
        rwa [map_pow, hcc, map_one] at this)⟩
    have hnV : IsUnit (M : WittVector p K) := by
      refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
      have : π (M : WittVector p K) ≠ 0 := by rw [map_natCast]; exact hMK.ne_zero
      exact this
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hu hnV
    exact ⟨π.comp f, by rw [RingHom.comp_apply, hfζ, hcc]⟩
  · haveI : CharZero K := CharP.charP_to_charZero K
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hy hMK
    exact ⟨f, hfζ⟩

end GlobalTheory.CycLift
end

