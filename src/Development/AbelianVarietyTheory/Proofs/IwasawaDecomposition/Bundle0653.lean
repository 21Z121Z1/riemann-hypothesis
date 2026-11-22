import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0632
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0639
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0635
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mem_V_of_forall (W : ValuationSubring ℂ) (h : ∀ p : ℕ, p.Prime → (p : ℂ) ∉ W.nonunits) (x : c.F) :
    x ∈ c.V W := by
  have hv1 : ∀ n : ℕ, n ≠ 0 → W.valuation (n : ℂ) = 1 := by
    intro n hn
    induction n using Nat.recOnMul with
    | zero => exact absurd rfl hn
    | one => simp
    | prime p hp =>
      refine le_antisymm ((W.valuation_le_one_iff _).2 (natCast_mem W p)) (not_lt.1 fun hlt => h p hp ?_)
      exact (W.mem_nonunits_iff).2 hlt
    | mul a b iha ihb =>
      have ha : a ≠ 0 := left_ne_zero_of_mul hn
      have hb : b ≠ 0 := right_ne_zero_of_mul hn
      rw [Nat.cast_mul, map_mul, iha ha, ihb hb, one_mul]
  have hvi : ∀ n : ℤ, n ≠ 0 → ((n : ℂ))⁻¹ ∈ W := by
    intro n hn
    have hn' : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
    have e : W.valuation (n : ℂ) = 1 := by
      rcases Int.natAbs_eq n with h1 | h1
      · rw [h1, Int.cast_natCast]; exact hv1 _ hn'
      · rw [h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact hv1 _ hn'
    refine (W.valuation_le_one_iff _).1 ?_
    rw [map_inv₀, e, inv_one]
  haveI := c.fin
  obtain ⟨n, hn, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := x)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).mpr (Algebra.IsAlgebraic.isAlgebraic _))
  let i : c.F →+* ℂ := c.F.val.toRingHom
  have h1 : _root_.IsIntegral ℤ (i (n • x)) := hint.map i.toIntAlgHom
  have h2 : _root_.IsIntegral W (i (n • x)) := h1.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : i (n • x) ∈ W := by
    have hw' : (w : ℂ) = i (n • x) := hw
    rw [← hw']; exact w.2
  have h4 : i x = ((n : ℂ))⁻¹ * i (n • x) := by
    have hn0 : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
    rw [zsmul_eq_mul, map_mul, map_intCast, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  change i x ∈ W
  rw [h4]
  exact W.mul_mem _ _ (hvi n hn) h3

theorem isOpenImmersion_j (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) : IsOpenImmersion Y.j := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ (p : ℂ) ∈ W.nonunits
  · obtain ⟨p, hp, hW⟩ := h
    exact GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hW Y
  · push_neg at h
    have hbij : Function.Bijective (c.V W).subtype :=
      ⟨Subtype.val_injective, fun x => ⟨⟨x, mem_V_of_forall W h x⟩, rfl⟩⟩
    have h1 : IsIso (CommRingCat.ofHom (c.V W).subtype) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have : IsIso (spMap (c.V W).subtype) := by
      unfold spMap; infer_instance
    have := Y.jQ_open
    unfold Model.j
    infer_instance

end GlobalTheory.TriplesAlong

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isDominant_jK (R : Type) [CommRing R] [IsDomain R] : IsDominant (Out.jK R) := by
  constructor
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hz : (Out.jK R) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R (FractionRing R)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)
  have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range (Out.jK R) := ⟨_, hz⟩
  exact closure_mono (Set.singleton_subset_iff.2 hmem)
    ((PrimeSpectrum.le_iff_mem_closure _ _).1 (show (⊥ : Ideal R) ≤ y.asIdeal from bot_le))

theorem exists_sab_congr {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f f' : S' ⟶ S} (m : SABMap t' t f)
    (h : f = f') : ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

end GlobalTheory.TriplesAlong

open GlobalTheory.TriplesAlong in

theorem GlobalTheory.TriplesAlong.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (W : ValuationSubring ℂ) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype)
    (bV : 𝓞 c.F →+* c.V W), (∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χZ : Sp R ⟶ Z.X) (χY : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo.XF c), Out.jK R ≫ χZ = y ≫ Z.j → Out.jK R ≫ χY = y ≫ Y.j →
      ∃ (t : SAB H (Sp R)) (m₁ : SABMap t Z.t χZ) (m₂ : SABMap t Y.t χY),
        ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
          g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
          g ≫ m₂.φ = g₂ ≫ Y.m.φ := by
  intro E _ _ _ H D l Xo c W Z Y bV hbV R _ _ _ _ χZ χY y hZ hY
  haveI : IsDominant (Out.jK R) := isDominant_jK R
  haveI hmono : Mono (spMap bV) := GlobalTheory.PolArcData.mono_spMap_incl bV hbV
  have hsub : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV :=
    GlobalTheory.PolArcData.spMap_algebraMap_eq bV hbV
  haveI : Mono (spMap (c.V W).subtype) := mono_spMap_subtype _
  haveI : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by rw [hsub]; exact mono_comp _ _
  haveI hZj : Mono Z.j := GlobalTheory.ThetaShiftProofs.mono_j Z inferInstance
  haveI hYj : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  haveI hYo : IsOpenImmersion Y.j := isOpenImmersion_j W Y
  haveI : IsProper Z.s := isProper_toroidalModel_structureMap Z

  have h1 : χZ ≫ Z.s = (χY ≫ Y.s) ≫ spMap bV := by
    refine ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _) (Out.jK R) ?_
    simp only [Category.assoc]
    rw [reassoc_of% hZ, reassoc_of% hY, Model.j_s, reassoc_of% (Model.j_s Y), hsub]

  let U : (Sp R).Opens := χY ⁻¹ᵁ Y.j.opensRange
  have hKU : Set.range (Out.jK R) ⊆ (U : Set (Sp R)) := by
    rintro _ ⟨p, rfl⟩
    show χY (Out.jK R p) ∈ Set.range Y.j
    rw [← Scheme.Hom.comp_apply, hY, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hKU' : Set.range (Out.jK R) ⊆ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hKU
  let jU : Sp (FractionRing R) ⟶ U.toScheme := IsOpenImmersion.lift U.ι (Out.jK R) hKU'
  have hjU : jU ≫ U.ι = Out.jK R := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant (jU ≫ U.ι) := by rw [hjU]; infer_instance
  haveI : IsDominant jU := IsDominant.of_comp_of_isOpenImmersion jU U.ι
  haveI hdomU : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact (Out.jK R).denseRange.mono hKU⟩
  have hUr : Set.range (U.ι ≫ χY) ⊆ Set.range Y.j := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact p.2
  let v : U.toScheme ⟶ Xo.XF c := IsOpenImmersion.lift Y.j (U.ι ≫ χY) hUr
  have hv : v ≫ Y.j = U.ι ≫ χY := IsOpenImmersion.lift_fac _ _ _
  have hjv : jU ≫ v = y := by
    rw [← cancel_mono Y.j, Category.assoc, hv, ← Category.assoc, hjU, hY]
  have hvZ : v ≫ Z.j = U.ι ≫ χZ := by
    refine ext_of_isDominant_of_isSeparated Z.s ?_ jU ?_
    · rw [Category.assoc, Model.j_s, Category.assoc, h1, hsub]
      simp only [Category.assoc]
      rw [← reassoc_of% hv, reassoc_of% (Model.j_s Y)]
    · rw [← Category.assoc, hjv, ← Category.assoc, hjU, hZ]

  obtain ⟨tZ, ⟨mZ⟩⟩ := GlobalTheory.TraitOrder.exists_pull χZ Z.t
  obtain ⟨tY, ⟨mY⟩⟩ := GlobalTheory.TraitOrder.exists_pull χY Y.t
  obtain ⟨t₀, ⟨n₀⟩⟩ := GlobalTheory.TraitOrder.exists_pull v Z.oF.t
  have hprop : IsProper t₀.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper
  obtain ⟨nZ, hnZ⟩ := GlobalTheory.ObjMaps.exists_sab_comp (show SABMap Z.oF.t Z.t Z.j from Z.m) n₀
  obtain ⟨nZ', hnZ'⟩ := exists_sab_congr nZ hvZ
  obtain ⟨a, ha⟩ := GlobalTheory.ObjMaps.exists_sab_cancel mZ nZ'
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.ObjMaps.exists_sab_comp Z.m0.toSABMap n₀
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.ObjMaps.exists_sab_cancel Y.m0.toSABMap n₁
  obtain ⟨n₃, hn₃⟩ := GlobalTheory.ObjMaps.exists_sab_comp (show SABMap Y.oF.t Y.t Y.j from Y.m) n₂
  obtain ⟨n₃', hn₃'⟩ := exists_sab_congr n₃ hv
  obtain ⟨a', ha'⟩ := GlobalTheory.ObjMaps.exists_sab_cancel mY n₃'

  have hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R
  obtain ⟨b, hb⟩ := GlobalTheory.TorRef.sabExtNormalSt_of_homExtNormalSt GlobalTheory.homExtNormal E H (Sp R) U.toScheme U.ι hnorm
    inferInstance hdomU t₀ tZ tY a a' hprop
  obtain ⟨m₂', hm₂'⟩ := GlobalTheory.ObjMaps.exists_sab_comp mY b
  obtain ⟨m₂, hm₂⟩ := exists_sab_congr m₂' (Category.id_comp χY)
  refine ⟨tZ, mZ, m₂, ?_⟩

  intro T g g₁ g₂ e1 e2 e3
  set q := g ≫ tZ.G.hom with hqdef
  set x := g₁ ≫ Z.oF.t.G.hom with hxdef
  have hq : q ≫ χZ = x ≫ Z.j := by
    have w1 := congrArg (· ≫ Z.t.G.hom) e1
    simp only [Category.assoc] at w1
    rw [mZ.cart.1.w, (show SABMap Z.oF.t Z.t Z.j from Z.m).cart.1.w] at w1
    simpa only [Category.assoc, hqdef, hxdef] using w1
  have hqY : (q ≫ χY) ≫ Y.s = (x ≫ pullback.snd _ _) ≫ spMap (c.V W).subtype := by
    rw [← cancel_mono (spMap bV)]
    simp only [Category.assoc]
    rw [← Category.assoc χY, ← h1, reassoc_of% hq, Model.j_s, hsub]
    all_goals simp only [Category.assoc]
  let L := pullback.lift (q ≫ χY) (x ≫ pullback.snd _ _) hqY
  have hab : ∀ p : T, q p ∈ abLocus tZ.G := fun p => by
    refine (abLocus_pullback abLocusOne Z.t.semi mZ.cart.1 (q p)).1 ?_
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply]
    exact GlobalTheory.ThetaShiftProofs.j_mem_abLocus Z _
  have hLr : Set.range L ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    refine (abLocus_pullback abLocusOne Y.t.semi mY.cart.1 (q p)).2 ?_
    exact (abLocus_pullback abLocusOne tY.semi b.cart.1 (q p)).2 (hab p)
  have hqU : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨z, hz⟩ := hLr ⟨p, rfl⟩
    refine ⟨z, ?_⟩
    show Y.j z = χY (q p)
    rw [Model.j, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
  let q' : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι q hqU
  have hq' : q' ≫ U.ι = q := IsOpenImmersion.lift_fac _ _ _
  have hw : g ≫ tZ.G.hom = q' ≫ U.ι := by rw [hq']
  let g' : T ⟶ t₀.G.left := a.cart.1.lift g q' hw
  have hg'1 : g' ≫ a.φ = g := a.cart.1.lift_fst _ _ _
  have hg'2 : g' ≫ t₀.G.hom = q' := a.cart.1.lift_snd _ _ _
  have hx' : q' ≫ v = x := by
    rw [← cancel_mono Z.j, Category.assoc, hvZ, ← Category.assoc, hq', hq]
  have hbase : g' ≫ t₀.G.hom ≫ v = x := by rw [← Category.assoc, hg'2, hx']
  have c1 : g' ≫ n₀.φ = g₁ := by
    refine (show SABMap Z.oF.t Z.t Z.j from Z.m).cart.1.hom_ext ?_ ?_
    · change (g' ≫ n₀.φ) ≫ Z.m.φ = g₁ ≫ Z.m.φ
      rw [Category.assoc, ← hnZ, ← hnZ', ha, ← Category.assoc, hg'1, e1]
    · rw [Category.assoc, n₀.cart.1.w, hbase]
  have c2 : g' ≫ n₂.φ = g₂ := by
    refine Y.m0.toSABMap.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, ← hn₂, hn₁, ← Category.assoc, c1, e2]
    · rw [Category.assoc, n₂.cart.1.w, hbase]
      exact e3
  rw [hm₂, hm₂', ← hg'1, Category.assoc, ← Category.assoc a.φ, hb, ← ha', hn₃', hn₃, ← Category.assoc, c2]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw TopologicalSpace

namespace GlobalTheory.ProperFinite

theorem finite_coh_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (f : X ⟶ Sp R)
    [IsProper f] (F : X.Modules) [QCoh.IsFiniteQC F] (p : ℕ) :
    letI := algebraΓOfHom f; Module.Finite R (coh F p) :=
  finite_coh_of_forall_modification f (fun Z _ ι _ => GlobalTheory.ChowLemma.exists_isProjOver_isIso_morphismRestrict R Z (ι ≫ f)) F p

theorem nonempty_perf_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R)
    [IsProper f] [Flat f] {M : LB Y} (hM : M.IsLB) : Nonempty (Perf f M) := by
  let := algebraΓOfHom f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := Y) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have := Twist.isFiniteQC_twist (F := structureModule Y) hM
  obtain ⟨K, φ, -, h2, -, h4, -, -, h7⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} (cechLB f M D) m
      (fun p hp => isZero_cechLB_X f M _ (by rw [Fintype.card_fin]; exact hp.le))
      (flat_cechLB_X f hM hD') (fun n => by
        obtain ⟨e⟩ := FieldChangeInter.nonempty_coh_equiv f hM hc hD' n
        have := finite_coh_of_isProper f (twist (structureModule Y) M) n
        exact Module.Finite.equiv e.symm)
  exact perf_of_projective_model R Y f M (Fin m) _ K φ hM hc hD' ⟨fun p => ⟨h2 p, h4 p⟩, h7⟩

open FibreLift in

theorem exists_pull_eq_smul {R : Type} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R)
    [IsProper f] [Flat f] {M : LB Y} (hM : M.IsLB) {K : Type} [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) {Y₀ : Scheme.{0}} {π : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ Sp K}
    (h : IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g))) (hH : FirstCohomologyVanishes (M.pull π))
    (x₀ : SecOnR f₀ (M.pull π) ⊤) :
    ∃ (c : R) (x : SecOnR f M ⊤), g c ≠ 0 ∧ SecOnR.pull M h.w ⊤ ⊤ le_top x = g c • x₀ := by
  obtain ⟨P⟩ := nonempty_perf_of_isProper f hM
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point R K g _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g Y₀ π f₀ h hH)
  obtain ⟨E, hE⟩ := P.sec K g Y₀ π f₀ h
  obtain ⟨v₀, hv₀⟩ := E.surjective (SecOnR.topEquiv f₀ _ x₀)
  obtain ⟨z, hz, -⟩ := hu K g hr.isUnit v₀.1 v₀.2
  obtain ⟨c, w, hc, hw⟩ := exists_common_denominator g hg z
  have hv : g ∘ B.mulVec w = g c • v₀.1 := by
    rw [← hz, ← Matrix.mulVec_smul, ← hw]
    exact funext fun j => RingHom.map_mulVec g _ _ j
  obtain ⟨s, hs⟩ := exists_sec_of_ker P (B.mulVec w)
    (by rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec])
  refine ⟨c, (SecOnR.topEquiv f M).symm s, hc, (SecOnR.topEquiv f₀ _).injective ?_⟩
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i)
    (fun i => le_pull M π (P.le i)) (fun y => Seesaw.exists_mem P (π y)) fun i => ?_
  have e₁ := Seesaw.loc_comp P h (B.mulVec w) i
  rw [hv, Seesaw.loc_smul, ← hs] at e₁
  have e₂ : Seesaw.loc P π f₀ v₀.1 i = _ := (hE v₀ i).symm
  rw [e₂, hv₀] at e₁
  refine Eq.trans ?_ ((rs_topEquiv_smul f₀ _ (g c) x₀ _ _).trans e₁).symm
  refine (rs_rs _ _ _).trans ?_
  refine (congrArg (rs Y₀ _) (SecOn.coord_pullLE π le_top _ _)).trans ?_
  refine (GlobalTheory.LB.resG_appLE π _ _ _).trans ?_
  refine (GlobalTheory.LB.appLE_resG π inf_le_right _ (s.f (P.ch i))).trans ?_
  rw [← Scheme.Hom.appLE_eq_app]
  exact (GlobalTheory.LB.appLE_resG π (P.le i) le_rfl _).symm

open AmpleNear in

theorem relAmple_near_fibre {R : Type} [CommRing R] [IsNoetherianRing R] (B : Over (Sp R)) [IsProper B.hom]
    [Flat B.hom] {L : LB B.left} (hL : L.IsLB) {K : Type} [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a)
    (hA : RelAmple ((Over.pullback (spMap g)).obj B) (L.pull (pullback.fst B.hom (spMap g)))) :
    ∃ r : R, g r ≠ 0 ∧
      RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r))).obj B)
        (L.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)))) := by
  have h := IsPullback.of_hasPullback B.hom (spMap g)
  obtain ⟨d, hd, h0, hv⟩ := exists_pw_h1Zero K _ _ (LB.isLB_pull hL _) hA
  have hv' : FirstCohomologyVanishes ((pw L d).pull (pullback.fst B.hom (spMap g))) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec ((pw L d).pull (pullback.fst B.hom (spMap g)))),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [pw_pull]
    obtain ⟨n, s, hs⟩ := hv
    exact ⟨h0, n, s, hs.1, fun i => (hs.2 i).1⟩
  obtain ⟨h1, n, s₀, hs₀, hs₀'⟩ := hv'
  choose c x hc hx using fun i => exists_pull_eq_smul B.hom (isLB_pw hL d) g hg h h1
    ((SecOnR.topEquiv _ _).symm (s₀ i))
  have e := fun i => preimage_nonzeroLocus_of_pull_eq h.w (pw L d) (x i) _ (hc i) (hx i)
  simp only [LinearEquiv.apply_symm_apply] at e
  obtain ⟨r, hr, hr'⟩ := exists_affine_loci_near B.hom (pw L d) (isLB_pw hL d)
    (fun i => SecOnR.topEquiv B.hom _ (x i)) g _ _ h (by simpa only [e] using hs₀)
    (by simpa only [e] using hs₀')
  refine ⟨r, hr, ?_⟩
  let j := Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)
  have : IsAffine (Scheme.Opens.toScheme (X := Sp R) (PrimeSpectrum.basicOpen r)) :=
    IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r
  have hv : ∃ s : Fin (n + 1) → LB.Sec (pw (L.pull (pullback.fst B.hom j)) d),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [← pw_pull]
    refine ⟨fun i => secPull (SecOnR.topEquiv B.hom _ (x i)) _, ?_⟩
    simp only [nonzeroLocus_secPull]
    exact hr' _ _ _ (IsPullback.of_hasPullback B.hom j)
  obtain ⟨s, hs, hs'⟩ := hv
  have : IsProper ((Over.pullback j).obj B).hom := inferInstanceAs (IsProper (pullback.snd B.hom j))
  exact relAmple_of_affine_loci ((Over.pullback j).obj B) _ (LB.isLB_pull hL _) hd s hs hs'

open FibreAmple in

theorem relAmple_of_geometricFibres {S : Scheme.{0}} [IsLocallyNoetherian S] (A : Over S) [IsProper A.hom]
    [Flat A.hom] {M : LB A.left} (hM : M.IsLB)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), IsAmpleLB (M.pull (pullback.fst A.hom y))) :
    RelAmple A M := by
  refine AmpleLocal.relAmple_of_locally S A M hM inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let t : Sp Γ(S, V) ⟶ S := hV.fromSpec
  obtain ⟨p, hp⟩ : s ∈ Set.range t := by rw [hV.range_fromSpec]; exact hs
  have hB := IsPullback.of_hasPullback A.hom t
  have hL := pull_isLB hM (pullback.fst A.hom t)
  have := p.isPrime
  let g := algebraMap Γ(S, V) p.asIdeal.ResidueField
  let i := algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
  have : IsProper (Over.mk (pullback.snd A.hom t)).hom := inferInstanceAs (IsProper (pullback.snd A.hom t))
  have : Flat (Over.mk (pullback.snd A.hom t)).hom := inferInstanceAs (Flat (pullback.snd A.hom t))
  have : IsProper (Over.mk (pullback.snd A.hom (spMap i ≫ spMap g ≫ t))).hom :=
    inferInstanceAs (IsProper (pullback.snd A.hom _))
  obtain ⟨r, hr, hA⟩ := relAmple_near_fibre (Over.mk (pullback.snd A.hom t)) hL g (residueField_fraction p.asIdeal)
    (relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback (pullback.snd A.hom t) (spMap g)).paste_horiz hB)
      (IsPullback.of_hasPullback A.hom _) (pull_isLB hL _) (lbIso_pull_pull hM _ _)
      ((relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hM _)).2 (hfib _ _)))
  let D : (Sp Γ(S, V)).Opens := PrimeSpectrum.basicOpen r
  have hD : p ∈ D := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  have hrange : Set.range (t ''ᵁ D).ι ⊆ Set.range (D.ι ≫ t) := by
    rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨t ''ᵁ D, ⟨p, hD, hp⟩, ?_⟩
  exact relAmple_of_factor hM ((IsPullback.of_hasPullback (pullback.snd A.hom t) D.ι).paste_horiz hB)
    (isPullback_morphismRestrict A.hom (t ''ᵁ D)).flip (IsOpenImmersion.lift (D.ι ≫ t) _ hrange)
    (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) hA

end GlobalTheory.ProperFinite

theorem GlobalTheory.PPAS.isProjOver_of_isProjOver_base : ∀ (S : Scheme.{0}) (P : GlobalTheory.PPAS S),
    IsProjOver (GlobalTheory.ShFam.Pad.toSpZ S) → IsProjOver (GlobalTheory.ShFam.Pad.toSpZ P.A.left) := by
  intro S P hS
  have := P.isAb.proper
  have := P.isAb.smooth
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hS).1
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (ShFam.Pad.toSpZ S)
  obtain ⟨M, hM, e⟩ := CechPic.cls_surj (CechPic.pull (lift (𝟙 P.A) (𝟙 P.A)).left P.c)
  have hA := ProperFinite.relAmple_of_geometricFibres P.A hM (DiagonalAmple.isAmpleLB_geometricFibre P hM e)
  refine DiagonalAmple.isProjOver_of_locally P.A hM (fun y => ?_) hS
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := y) trivial
  exact ⟨V, hV, hy, isAmpleLB_of_relAmple P.A hM hA V hV⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombinationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTanBasis_of_unique_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), (∀ i, IsTanAtG t x (e i)) → (∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x e cf u) → GlobalTheory.LineNorm.IsTanBasis t x e := by
  first | exact @GlobalTheory.LineNorm.isTanBasis_of_basis | exact GlobalTheory.LineNorm.isTanBasis_of_basis | (intros; apply GlobalTheory.LineNorm.isTanBasis_of_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeySectionEqConstMulThetaFunctionFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keySection_eq_const_mul_thetaFunction_fibre : ∀ (x : KeyIn ℂ) (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (y : Sp ℂ ⟶ S) (Φ : x.P.A.left ⟶ G.left) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (w : LB.Iso (L.pull Φ) x.P.L) (θ : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec), L.IsLB → IsPullback Φ x.P.A.hom G.hom y → w.IsGen → (∃ z, θ z ≠ 0) → (∀ j z, ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ k j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (x.P.L.U k ⊓ (L.pull Φ).U j) → u.fr k z = valAt' (u.ex z).left (x.P.L.U k ⊓ (L.pull Φ).U j) (w.s (k, j)).val * fr (j PUnit.unit) z) → (∀ j z (p : Sp ℂ ⟶ pullback G.hom y), p ≫ pullback.fst _ _ = (u.ex z).left ≫ Φ → p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → valAt' p ((L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) → ∃ c₀ : ℂ, u.IsFn x.th (fun z => c₀ * θ z) := by
  first | exact @GlobalTheory.FibreKeyTheta.th_isFn_const_mul | exact GlobalTheory.FibreKeyTheta.th_isFn_const_mul | (intros; apply GlobalTheory.FibreKeyTheta.th_isFn_const_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterSectionOnMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

theorem ratioAt_pull : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → N2 Y → ∀ (Z Z' : Mdl Y i₀) (f : Z'.X ⟶ Z.X), IsMap Z' Z f → (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ st (x : Letter Dw), letterOf Dw st = some x → ∀ (U : Z.X.Opens) (m m' : ℕ) (A : Fin m → Γ(Z.X, U)) (B : Fin m' → Γ(Z.X, U)), RatioAt Z st U A B → ∀ (U' : Z'.X.Opens) (h : U' ≤ f ⁻¹ᵁ U), RatioAt Z' st U' (fun j => (f.appLE U U' h).hom (A j)) (fun j => (f.appLE U U' h).hom (B j)) := by
  intro hB E _ _ _ H Dw Xo p W Y i₀ hp _ hN Z Z' f hf hty st x hx U m m' A B hR U' h
  obtain ⟨τ, mu, hT⟩ := Pull.exists_trans hN hf.1.1 hf.1.2.1
  have rad : ∀ {n : ℕ} (C : Fin n → Γ(Z.X, U)), (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range C)).radical →
      (p : Γ(Z'.X, U')) ∈ (Ideal.span (Set.range fun j => (f.appLE U U' h).hom (C j))).radical := by
    intro n C hC
    have := Ideal.map_radical_le (f.appLE U U' h).hom (Ideal.mem_map_of_mem _ hC)
    rw [Ideal.map_span, ← Set.range_comp] at this
    rw [map_natCast] at this
    exact this
  refine ⟨rad A hR.1, rad B hR.2.1, fun y a' φ' h' hU => ?_⟩
  obtain ⟨a, φ, e⟩ := Pull.exists_chart hf hT (Pull.range_opn Z' h')
  obtain ⟨c, c0, hc⟩ := Pull.exists_coeff (x := x) hf hT hty h' e
  obtain ⟨P, hP⟩ := Pull.exists_pt hf hT y
  have hU₂ : ⊤ ≤ (y.z ≫ f) ⁻¹ᵁ U := fun q hq => h (hU hq)
  have N := hR.2.2 ⟨y.C, P, y.z ≫ f, hP⟩ a φ (e.trans (Category.assoc _ _ _)) hU₂
  have g₀ : Mdl.Pt.gen (Z := Z) ⟨y.C, P, y.z ≫ f, hP⟩ = y.gen ≫ f := (Category.assoc _ _ _).symm
  have g₁ : y.gen ≫ Z'.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ Z'.π := Category.assoc _ _ _
  have g₂ : (y.gen ≫ f) ≫ Z.π = spMap (intO ↥y.C.S).subtype ≫ (y.z ≫ Z'.π) ≫ τ := by
    rw [Category.assoc, Pull.map_π hf hT, reassoc_of% g₁, Category.assoc]
  have F := Pull.chart_frame Z e
  have F' := Pull.push_frame hf hT h' e
  have T := Pull.push_tri hf hT hty h' e
  rw [g₀] at N
  rw [g₂] at N F F' T hc
  have step : ∀ b, lnStep (Y Z'.i).t (y.gen ≫ Z'.π) ((Z'.fr a').bc φ') p b st = Real.log ‖c x.2‖ +
      lnStep (Y Z.i).t (spMap (intO ↥y.C.S).subtype ≫ (y.z ≫ Z'.π) ≫ τ) ((Z.fr a).bc φ) p b st := fun b => by
    rw [g₁, Pull.lnStep_push mu b _ (Pull.ext_unique _ _) (fun σ j => g₁ ▸ ((Pull.chart_frame Z' h').1 σ j).1),
      Pull.lnStep_tri hB hp y.C b _ (Pull.ext_unique _ _) F F' T hx hc]
  have hgen : ⊤ ≤ y.gen ⁻¹ᵁ U' := fun q _ => hU (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
  have vals : ∀ {n : ℕ} (C : Fin n → Γ(Z.X, U)), (fun j => valF y.gen U' ((f.appLE U U' h).hom (C j))) =
      fun j => valF (y.gen ≫ f) U (C j) := fun C => funext fun j => Pull.valF_appLE f U h hgen _
  rw [step, step, vals, vals]
  linarith

end GlobalTheory.HTLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDefStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef → ∫⁻ y : Low m → ℂ, ENNReal.ofReal (dens A y) = ENNReal.ofReal (A.det.re ^ (1 - (m : ℤ)) / flagConst m) := by
  first | exact @GlobalTheory.FlagFibre.FlagInt.lintegral_dens | exact GlobalTheory.FlagFibre.FlagInt.lintegral_dens | (intros; apply GlobalTheory.FlagFibre.FlagInt.lintegral_dens <;> assumption)
end

