import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3438
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftedSectionDivMonomialOverChart
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3431

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpreadUniversalAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCovSep.LocalSpread

open GlobalTheory.Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_chart (C : UCompact Xo c) {o₁ Ω : Type} [CommRing o₁] [Field Ω] [Algebra o₁ Ω] [CharZero Ω]
    (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (uη : Sp Ω ⟶ Xo.XF c) (hπ : M.pt ≫ π = uη ≫ C.i) (w : M.Z)
    (hw : π w ∈ Set.range C.i) :
    ∃ (U₀ : M.Z.Opens) (u₀ : Sp (ratHull (M.ringOn U₀)) ⟶ Xo.XF c), w ∈ U₀ ∧
      spMap (ratHull (M.ringOn U₀)).val.toRingHom ≫ u₀ = uη := by
  haveI := C.iF_open
  haveI := C.ded
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb := Scheme.Hom.isEmbedding (pullback.fst C.z (spMap C.b))
  obtain ⟨V, hVo, hV⟩ := hemb.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  have hwV : w ∈ π ⁻¹ᵁ ⟨V, hVo⟩ := by
    obtain ⟨x, hx⟩ := hw
    show π w ∈ V
    have : C.iF x ∈ pullback.fst C.z (spMap C.b) ⁻¹' V := hV ▸ ⟨x, rfl⟩
    rw [← hx]
    simpa using this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) hwV
  have hne : ((U : M.Z.Opens) : Set M.Z).Nonempty := ⟨w, hwU⟩
  let R₀ := M.ringOn U
  let φ : Γ(M.Z, U) ⟶ CommRingCat.of R₀ := CommRingCat.ofHom (M.sectionsEquiv U hne).toRingHom
  let f : Sp R₀ ⟶ M.Z := Spec.map φ ≫ hU.fromSpec
  let g : Sp (ratHull R₀) ⟶ C.Z := spMap (toRat R₀) ≫ f ≫ π
  have hgV : ∀ y, g y ∈ V := by
    intro y
    have hy : hU.fromSpec (Spec.map φ (spMap (toRat R₀) y)) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hy
    exact hUV hy
  let ψ : C.o →+* ratHull R₀ := (Spec.preimage (g ≫ C.z)).hom
  have hψ : ∀ a : nonZeroDivisors C.o, IsUnit (ψ a) := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hn, hdvd⟩ := ChartAt.exists_int_dvd C (nonZeroDivisors.ne_zero ha)
    exact isUnit_of_dvd_unit (map_dvd ψ hdvd) (by simpa using isUnit_intCast_ratHull R₀ hn)
  let θ : c.F →+* ratHull R₀ := IsLocalization.lift (M := nonZeroDivisors C.o) hψ
  have hθ : θ.comp (algebraMap C.o c.F) = ψ := IsLocalization.lift_comp hψ
  have hw' : g ≫ C.z = spMap θ ≫ spMap C.b := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change _ = Spec.map (CommRingCat.ofHom (θ.comp (algebraMap C.o c.F)))
    rw [hθ]
    exact (Spec.map_preimage _).symm
  let g' : Sp (ratHull R₀) ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap θ) hw'
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hV]
    show pullback.fst C.z (spMap C.b) (g' y) ∈ V
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hgV y
  refine ⟨U, IsOpenImmersion.lift C.iF g' hrange, hwU, ?_⟩
  have hpt : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom R₀.val.toRingHom = valMap M.pt U hpt := by
    ext a
    show ((M.sectionsEquiv U hne a : M.ringOn U) : Ω) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap R₀.val.toRingHom ≫ f = M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  haveI := C.isPreimmersion_i
  rw [← cancel_mono C.i, ← hπ, Category.assoc, UCompact.i, ← Category.assoc (IsOpenImmersion.lift _ _ _),
    IsOpenImmersion.lift_fac, pullback.lift_fst]
  show spMap (ratHull R₀).val.toRingHom ≫ spMap (toRat R₀) ≫ f ≫ π = _
  rw [← Category.assoc, spMap_val_toRat, ← Category.assoc, hf]

theorem isUnit_intCast (C : UCompact Xo c) {o₁ Ω : Type} [CommRing o₁] [Field Ω] [Algebra o₁ Ω]
    (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (w : M.Z) (hw : π w ∈ Set.range C.i) (n : ℤ) (hn : n ≠ 0) :
    IsUnit (n : M.O w) := by
  obtain ⟨x, hx⟩ := hw
  rw [← map_intCast (M.stalkEquiv w) n, MulEquiv.isUnit_map, LocSpread.isUnit_intCast_stalk_iff π, ← hx,
    ← LocSpread.isUnit_intCast_stalk_iff C.i,
    LocSpread.isUnit_intCast_stalk_iff (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F)]
  have h : IsUnit (n : c.F) := IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
  have h' := (h.map (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom).map
    ((Sp c.F).presheaf.germ ⊤ ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) x) trivial).hom
  rwa [map_intCast, map_intCast] at h'

theorem exists_uAct {R R' Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R']
    [Field Ω] [Algebra R Ω] [IsFractionRing R Ω] {σ : R →+* R'} (τ : R' →+* Ω) (hτ : Function.Injective τ)
    (e : τ.comp σ = algebraMap R Ω) {P : PolAV (Sp R)} {u : Sp R' ⟶ Xo.XF c} (h : UOver Xo c P σ u) :
    ∃ act : 𝓞 E → (P.A ⟶ P.A), (∀ a, IsMonHom (act a)) ∧ UAct Xo c P act σ u := by
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have e' : spMap τ ≫ spMap σ = spMap (algebraMap R Ω) := by rw [← Spec.map_comp, ← e]; rfl
  have hG := isGrpPullback_pullback G (spMap τ)
  have hGP := (hG.comp hα).congr e' rfl
  have hs := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ P.isAb
  haveI := P.isAb.proper
  haveI := (PolPull.isAbelianScheme_of_isGrpPullback P.isAb hα).smooth
  haveI : IsSchemeTheoreticallyDominant (spMap τ) := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hτ
  haveI : IsSchemeTheoreticallyDominant (pullback.fst G.hom (spMap τ)) := .of_isPullback hG.1.flip
  have key : ∀ a : 𝓞 E, ∃ F : P.A ⟶ P.A, IsMonHom F ∧ ∃ f : G ⟶ G, f.left ≫ α = α ≫ F.left ∧
      f.left ≫ β = β ≫ (Xo.univ.t.act.act (H.bar a)).left := fun a => by
    have w : (β ≫ (Xo.univ.t.act.act (H.bar a)).left) ≫ Xo.univ.t.G.hom = G.hom ≫ u ≫ pullback.fst _ _ := by
      rw [Category.assoc, Over.w, hβ.1.w]
    let f : G ⟶ G := Over.homMk (hβ.1.lift _ _ w) (hβ.1.lift_snd _ _ w)
    have hf : f.left ≫ β = β ≫ (Xo.univ.t.act.act (H.bar a)).left := hβ.1.lift_fst _ _ w
    haveI := Xo.univ.t.act.hom (H.bar a)
    haveI : IsMonHom f := GlobalTheory.SharpPull.isMonHom_lift hβ hβ hf
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField_of_isGrpPullback hs hs hGP hGP
      ((Over.pullback (spMap τ)).map f)
    refine ⟨F, hF, f, ExtUnique.hom_ext_of_dominant P.A.hom ?_ (pullback.fst G.hom (spMap τ)) ?_, hf⟩
    · rw [Category.assoc, Category.assoc, Over.w, hα.1.w, Over.w_assoc]
    · rw [← Category.assoc, ← ExtUnique.pullback_map_left_fst, Category.assoc]
      exact hF'.trans (Category.assoc _ _ _)
  choose act h₁ h₂ using key
  exact ⟨act, h₁, G, _, α, β, hα, hβ, hL, h₂⟩

theorem exists_local_spread : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (o₁ Ω : Type) [CommRing o₁] [Field Ω] [Algebra o₁ Ω] [ArithBase o₁ Ω] (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (uη : Sp Ω ⟶ Xo.XF c), GlobalTheory.IsNormalScheme M.Z → M.pt ≫ π = uη ≫ C.i → ∀ (A₁ : PolAV (Sp Ω)) (m : ℕ) (ze : o₁ˣ), IsUnit (m : o₁) → UOver Xo c A₁ (RingHom.id Ω) uη → Out.Level A₁ m (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze)) → ∀ (K : Type) [Field K] (yM : Sp K ⟶ M.Z) (y : Sp K ⟶ Xo.XF c), yM ≫ π = y ≫ C.i → ∃ (R : Subalgebra o₁ Ω) (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c) (𝔭 : Ideal R), R.FG ∧ (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ P.g = A₁.g ∧ HypS P.A P.L ∧ Nonempty (Out.Level P m (unitOn (Units.map (algebraMap o₁ R).toMonoidHom ze))) ∧ (∀ a, IsMonHom (act a)) ∧ GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u ∧ spMap (ratHull R).val.toRingHom ≫ u = uη ∧ 𝔭.IsPrime ∧ ∀ a b : R, b ∉ 𝔭 → (a : Ω) / (b : Ω) ∈ M.O (yM (closedPoint K)) := by
  intro E _ _ _ H Dw _ l Xo c C o₁ Ω _ _ _ hb M π uη hM hπ A₁ m ze hm hU₁ lev K _ yM y hy
  haveI := hb.char
  haveI := hb.ded
  let w : M.Z := yM (closedPoint K)
  have hw : π w ∈ Set.range C.i := ⟨y (closedPoint K), (congrArg (fun χ : Sp K ⟶ C.Z => χ (closedPoint K)) hy).symm⟩
  obtain ⟨U₀, u₀, hw₀, hu₀⟩ := exists_chart C M π uη hπ w hw
  obtain ⟨U, hle, P₁, -, hU, hwU, hP₁⟩ := LocSpread.exists_model (isUnit_intCast C M π w hw) hw₀ u₀
  have hne : ((U : M.Z.Opens) : Set M.Z).Nonempty := ⟨w, hwU⟩
  let u : Sp (ratHull (M.ringOn U)) ⟶ Xo.XF c := spMap (Subalgebra.inclusion (ratHull_mono hle)).toRingHom ≫ u₀
  have hu : spMap (ratHull (M.ringOn U)).val.toRingHom ≫ u = uη := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]; rfl
  have gen : ∀ P : PolAV (Sp (M.ringOn U)), UOver Xo c P (toRat (M.ringOn U)) u →
      UOver Xo c P (M.ringOn U).val.toRingHom uη := fun P hP => by
    have := hP.comp (ratHull (M.ringOn U)).val.toRingHom
    rw [hu] at this
    exact this
  haveI := RatModel.isFractionRing_ringOn hU hne
  haveI := GlobalTheory.Poinc.TorsExtend.isIntegrallyClosed_ringOn M ((isNormalScheme_iff_pred _).1 hM) hU hne
  have fg : (M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ M U hU hne
  haveI : IsNoetherianRing (M.ringOn U) := isNoetherianRing_of_fg fg

  obtain ⟨Q, a, a', ha, ha', hL, hL'⟩ :=
    exists_common_baseChange_of_uOver E H Dw l Xo c Ω _ _ A₁ P₁ _ _ uη hU₁ (gen P₁ hP₁)
  have g₁ := GlobalTheory.polAV_g_eq_of_isGrpPullback Ω _ A₁ Q _ a ha
  have g₂ := GlobalTheory.polAV_g_eq_of_isGrpPullback Ω _ P₁ Q _ a' ha'
  obtain ⟨levQ, -⟩ := exists_level_baseChange GlobalTheory.abelianSchemeLaws_all.1 _ _ _ A₁ Q a ha hL g₁ _ _
    (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze)) (by rw [GSetup.map_unitOn']; rfl) lev.prim lev
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm.ne_zero Nat.cast_zero)
  obtain ⟨P, ψ, hg, hψ, hψL, hlev⟩ := GlobalTheory.SympLevelExt.level_extends P₁ (M.ringOn U) Ω (RingHom.id _) Q a' m
    (Units.map (algebraMap o₁ (M.ringOn U)).toMonoidHom ze) hm0
    (by simpa using hm.map (algebraMap o₁ (M.ringOn U))) g₂ ha' hL' ⟨levQ⟩
  have hP : UOver Xo c P (toRat (M.ringOn U)) u := (uOver_baseChange_iff hψ hψL _).2 hP₁

  obtain ⟨A₀, hS₀, hU₀⟩ := GSetup.exists_fibre Xo c uη
  obtain ⟨Q', b, b', hb₁, hb₂, hb₃, hb₄⟩ :=
    exists_common_baseChange_of_uOver E H Dw l Xo c Ω _ _ A₀ P _ _ uη hU₀ (gen P hP)
  have hS := GlobalTheory.Poinc.hypS_of_generic_ringOn o₁ Ω M U hU hne hM Ω A₀ P Q' _ b b' hb₁ hb₂ hb₃ hb₄ hS₀

  obtain ⟨act, hact, hA⟩ := exists_uAct (ratHull (M.ringOn U)).val.toRingHom Subtype.val_injective rfl hP
  let j : M.ringOn U →+* M.O w := (Subalgebra.inclusion (RatModel.ringOn_le_O hwU)).toRingHom
  refine ⟨M.ringOn U, P, act, u, (maximalIdeal (M.O w)).comap j, fg, fun x => ?_, hg.trans (g₂.symm.trans g₁), hS, hlev,
    hact, hA, hu, inferInstance, fun p q hq => ?_⟩
  · obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hU hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  · have hq' : IsUnit (j q) := by
      by_contra h
      exact hq h
    rw [div_eq_mul_inv]
    exact mul_mem (j p).2 ((RatModel.isUnit_O_iff _).1 hq').2

end GlobalTheory.UCovSep.LocalSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusTorsionPointsAreLevelSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevSurjOpen

theorem lev_nsmul {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : Type} [AddCommGroup L]
    (lev : L → (𝟙_ (Over S) ⟶ G)) (hadd : ∀ a b, lev (a + b) = lev a * lev b) (a : L) :
    ∀ n : ℕ, lev (n • a) = lev a ^ n
  | 0 => by
    have h := hadd 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.mp h.symm
  | n + 1 => by rw [succ_nsmul, hadd, lev_nsmul lev hadd a n, pow_succ]

theorem range_subset_iff_pt {k : Type} [Field k] {X : Scheme.{0}} (y : Sp k ⟶ X) (O : Set X) :
    Set.range y.base ⊆ O ↔ y.base (⊥ : PrimeSpectrum k) ∈ O := by
  haveI : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rw [Set.range_subset_iff]
  refine ⟨fun H => H _, fun H p => ?_⟩
  have : p = (⊥ : PrimeSpectrum k) := Subsingleton.elim (α := Sp k) p (⊥ : PrimeSpectrum k)
  rw [this]
  exact H

theorem torsion_hom_ext {S : Scheme.{0}} {G : Over S} [GrpObj G] {M : ℕ} {X : Over S} (u v : X ⟶ torsion G M)
    (h : u ≫ torsion.ι G M = v ≫ torsion.ι G M) : u = v :=
  pullback.hom_ext h (toUnit_unique _ _)

theorem exists_open_levSurj : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ g : Over.mk x₀ ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ g : Over.mk x ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g := by
  intro S _ M t G _ _ h lev hab hM hadd htors k _ _ x₀ hx₀
  haveI := hab
  have hM0 : M ≠ 0 := by omega
  have hu : IsUnit (M : Γ(S, ⊤)) := by
    simpa using (GlobalTheory.SiegelTor.isUnit_natCast hM0).map
      ((Scheme.ΓSpecIso (CommRingCat.of (cycAway M))).inv ≫ t.appTop).hom
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G hu
  haveI := hfin
  haveI := het
  let ℓ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ torsion G M) := fun a =>
    GlobalTheory.TorsionFamily.torsionLift G (lev a) M (htors a)
  have hℓ : ∀ a, ℓ a ≫ torsion.ι G M = lev a := fun a => GlobalTheory.TorsionFamily.torsionLift_ι _ _ _ _

  have hcl : ∀ a, GlobalTheory.LevCover.ClopenCond (torsion G M)
      fun _ y => y ≫ 𝟙 (torsion G M) = y ≫ (toUnit (torsion G M) ≫ ℓ a) :=
    fun a => GlobalTheory.LevCover.clopenCond_eq _ _
  choose U hUc hU using hcl
  obtain ⟨κ, _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod (Fin h ⊕ Fin h → ℤ) (n := M) (by omega)
  let rep : Set.range q → (Fin h ⊕ Fin h → ℤ) := fun c => c.2.choose
  have hrep : ∀ a, lev (rep ⟨q a, a, rfl⟩) = lev a := by
    intro a
    obtain ⟨c, hc⟩ := hq _ _ ((⟨q a, a, rfl⟩ : Set.range q).2.choose_spec)
    have e := congrArg lev hc
    rw [hadd, lev_nsmul lev hadd, htors, _root_.mul_one] at e
    exact e.symm

  let Zs : Set (torsion G M).left := ⋃ c : Set.range q, (U (rep c) : Set (torsion G M).left)
  have hZo : IsOpen Zs := isOpen_iUnion fun c => (U _).isOpen
  have hZc : IsClosed Zs := isClosed_iUnion_of_finite fun c => hUc _
  let C : (torsion G M).left.Opens := ⟨Zsᶜ, hZc.isOpen_compl⟩
  obtain ⟨V, i, hVf, hVe, -, hV⟩ := GlobalTheory.LevCover.exists_sub C hZo.isClosed_compl
  haveI := hVf
  haveI := hVe
  haveI : IsFinite (𝟙_ (Over S)).hom := by show IsFinite (𝟙 S); infer_instance
  haveI : Etale (𝟙_ (Over S)).hom := by show Etale (𝟙 S); infer_instance

  obtain ⟨U₀, hU₀c, hU₀⟩ := GlobalTheory.LevCover.exists_image (toUnit V)
  let U₁ : Set S := (U₀ : Set (𝟙_ (Over S)).left)
  have hU₁c : IsClosed U₁ := hU₀c
  have key : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S),
      Set.range x.base ⊆ U₁ ↔ Nonempty (Over.mk x ⟶ V) := by
    intro k' _ _ x
    have H := hU₀ k' x (toUnit _)
    have hz : (toUnit (Over.mk x) : Over.mk x ⟶ 𝟙_ (Over S)).left = x := by
      simpa using Over.w (toUnit (Over.mk x))
    rw [hz] at H
    exact H.trans ⟨fun ⟨w, _⟩ => ⟨w⟩, fun ⟨w⟩ => ⟨w, toUnit_unique _ _⟩⟩
  refine ⟨⟨U₁ᶜ, hU₁c.isOpen_compl⟩, ?_, ?_⟩
  · intro _ ⟨p, hp⟩ hpU
    subst hp
    have hr : Set.range x₀.base ⊆ U₁ := by
      rw [range_subset_iff_pt]
      have : p = (⊥ : PrimeSpectrum k) :=
        @Subsingleton.elim (Sp k) (inferInstanceAs (Subsingleton (PrimeSpectrum k))) p (⊥ : PrimeSpectrum k)
      rw [← this]
      exact hpU
    obtain ⟨w⟩ := (key k x₀).1 hr
    let y := w ≫ i
    have hy : Set.range y.left.base ⊆ (C : Set (torsion G M).left) := (hV _ y).2 ⟨w, rfl⟩
    have hg : (y ≫ torsion.ι G M) ^ M = 1 := by
      rw [← MonObj.comp_pow, GlobalTheory.TorsionFamily.torsion_ι_pow, MonObj.comp_one]
    obtain ⟨a, ha⟩ := hx₀ _ hg
    have e1 : (toUnit (Over.mk x₀) ≫ ℓ (rep ⟨q a, a, rfl⟩)) ≫ torsion.ι G M = toUnit _ ≫ lev a := by
      rw [Category.assoc, hℓ, hrep]
    have e2 : y ≫ torsion.ι G M = toUnit _ ≫ lev a := ha.symm
    have hy' : y = toUnit _ ≫ ℓ (rep ⟨q a, a, rfl⟩) := torsion_hom_ext _ _ (e2.trans e1.symm)
    have hin : Set.range y.left.base ⊆ (U (rep ⟨q a, a, rfl⟩) : Set (torsion G M).left) := by
      refine (hU _ _ y).1 ?_
      show y ≫ 𝟙 _ = y ≫ toUnit _ ≫ ℓ _
      rw [Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit _), ← hy']
    have h1 := (range_subset_iff_pt _ _).1 hy
    have h2 := (range_subset_iff_pt _ _).1 hin
    exact h1 (Set.mem_iUnion.2 ⟨⟨q a, a, rfl⟩, h2⟩)
  · intro k' _ _ x hx g hg
    let y := GlobalTheory.TorsionFamily.torsionLift G g M hg
    have hnC : ¬ Set.range y.left.base ⊆ (C : Set (torsion G M).left) := by
      intro H
      obtain ⟨w, -⟩ := (hV _ y).1 H
      have hr := (key k' x).2 ⟨w⟩
      have h1 := (range_subset_iff_pt _ _).1 hr
      have h2 := (range_subset_iff_pt _ _).1 hx
      exact h2 h1
    rw [range_subset_iff_pt] at hnC
    have hZ : y.left.base (⊥ : PrimeSpectrum k') ∈ Zs := not_not.1 hnC
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hZ
    have hin : Set.range y.left.base ⊆ (U (rep c) : Set (torsion G M).left) :=
      (range_subset_iff_pt _ _).2 hc
    have e : y ≫ 𝟙 _ = y ≫ toUnit _ ≫ ℓ (rep c) := (hU _ _ y).2 hin
    rw [Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit _)] at e
    refine ⟨rep c, ?_⟩
    rw [← hℓ, ← Category.assoc, ← e]
    exact GlobalTheory.TorsionFamily.torsionLift_ι _ _ _ _

end GlobalTheory.LevSurjOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowNormValLeUnitaryThetaFiniteModelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_norm_val_le_unitaryTheta_finite_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ X' : USetup C) (z₁ : X₁.M.Z), ∃ e : ℕ, 1 ≤ e ∧ ∀ (p : ℕ) [Fact p.Prime] (t : UCTrait X₁ p z₁) (z' : X'.M.Z) (t' : UCTrait X' p z'), t.y ≫ X₁.π = t'.y ≫ X'.π → ∀ h' ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖t'.val h'‖ ^ e ≤ ‖t.val h‖ := by
  first | exact @GlobalTheory.UPoinc.ValBound.exists_pow_norm_val_le | exact GlobalTheory.UPoinc.ValBound.exists_pow_norm_val_le | (intros; apply GlobalTheory.UPoinc.ValBound.exists_pow_norm_val_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelAdjointActionPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UPel.HT

theorem siegPre_actPB_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O)
    (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s)
    (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act →
    ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧
      Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  intro h M B _ ζ O _ bar S S' s s' f z act hs hz hR hA
  obtain ⟨⟨w, φ, φ₂, hφ, hsq, hP, hlev⟩, hpr⟩ := GlobalTheory.siegPre_pullback h M B ζ S S' s s' f z hs
  have hwP : w.Principal := hpr w ⟨φ, φ₂, hφ, hsq, hP, hlev⟩ hz
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hφ (isGrpPullback_pullback z.A f)
  haveI := he
  have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  let actw : O → (w.A ⟶ w.A) := fun a => e.hom ≫ (Over.pullback f).map (act a) ≫ e.inv
  have hv : ∀ a, (actw a).left ≫ φ = φ ≫ (act a).left := fun a => by
    have hm : ((Over.pullback f).map (act a)).left ≫ pullback.fst z.A.hom f =
        pullback.fst z.A.hom f ≫ (act a).left := pullback.lift_fst _ _ _
    rw [← heφ]
    simp only [actw, Over.comp_left, Category.assoc]
    rw [reassoc_of% hie, hm]
  have hRw : IsRAct w.A actw := ActUnr.isRAct_conj e _ (ActUnr.isRAct_pullback f z.A act hR)
  have lf : ∀ {T : Scheme.{0}} {X Y : Over T} (x y : X ⟶ Y), (lift x y).left ≫ (fst Y Y).left = x.left :=
    fun x y => by rw [← Over.comp_left, lift_fst]
  have ls : ∀ {T : Scheme.{0}} {X Y : Over T} (x y : X ⟶ Y), (lift x y).left ≫ (snd Y Y).left = y.left :=
    fun x y => by rw [← Over.comp_left, lift_snd]
  have hc1 : ∀ a, (lift (fst w.A w.A ≫ actw a) (snd w.A w.A)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst z.A z.A ≫ act a) (snd z.A z.A)).left := fun a => by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, hsq.1, ← Category.assoc, lf, Category.assoc, lf, Over.comp_left _ _ _ (fst w.A w.A) (actw a),
        Over.comp_left _ _ _ (fst z.A z.A) (act a), Category.assoc, hv, ← Category.assoc, ← hsq.1, Category.assoc]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ls, Category.assoc, ls, hsq.2]
  have hc2 : ∀ a, (lift (fst w.A w.A) (snd w.A w.A ≫ actw (bar a))).left ≫ φ₂ =
      φ₂ ≫ (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar a))).left := fun a => by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, hsq.1, ← Category.assoc, lf, Category.assoc, lf, hsq.1]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ls, Category.assoc, ls, Over.comp_left _ _ _ (snd w.A w.A) (actw (bar a)),
        Over.comp_left _ _ _ (snd z.A z.A) (act (bar a)), Category.assoc, hv, ← Category.assoc, ← hsq.2, Category.assoc]
  have hadj : Adj w.A w.P bar actw := fun a => by
    have h1 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP _ (hc1 a).symm
    have h2 := GlobalTheory.GenSpread.lbIso_pull_comp (L := z.P) (M := z.P) φ₂ rfl rfl (hA a)
    have h3 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP _ (hc2 a).symm
    exact LBIso.trans (pull_isLB w.isLB _) (pull_isLB z.isLB _) (pull_isLB w.isLB _)
      (LBIso.trans (pull_isLB w.isLB _) (pull_isLB z.isLB _) (pull_isLB z.isLB _) h1 h2) h3.symm
  exact ⟨w, actw, hwP, hRw, hadj, φ, φ₂, hφ, hsq, hP, hlev, hv⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMorphismOfGeneratingSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ (_ : IsIntegral (PSpace k D)) (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), π (genericPoint X) = genericPoint (PSpace k D) ∧ π.residueDegree (genericPoint X) ≠ 0 ∧ π.residueDegree (genericPoint X) * Module.finrank ℤ k = Module.finrank (ratF x) X.functionField ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  first | exact @GlobalTheory.HSAmp.toProj_gens | exact GlobalTheory.HSAmp.toProj_gens | (intros; apply GlobalTheory.HSAmp.toProj_gens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbeliaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O), ∃ (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG := by
  first | exact @GlobalTheory.Mum.exists_oLinear_of_oAct | exact GlobalTheory.Mum.exists_oLinear_of_oAct | (intros; apply GlobalTheory.Mum.exists_oLinear_of_oAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftedSectionDivMonomialOverChartStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shifted_section_div_monomial_over_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → (∀ i, 0 ≤ (e : ℤ) * n i + gam i mu α) ∧ ∀ σ : P.D.toPre.SecB e α, ∃ σ₁ σ₁u : P.D.toPre.SecB e (α + e • mu), ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ ((e : ℤ) * n i + gam i mu α).toNat)) * sval σ₁u x z J) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u (r ≫ (P.D.toPre.c 0).left) z J = ((val ψ₀ r z J) ^ e * val τ₀ r z J * (val P.D.toPre.rig r z J) ^ e).val * sval σ (r ≫ (P.D.toPre.c mu).left) z J := by
  first | exact @GlobalTheory.ShiftUnitPart.exists_shift_div_monomial | exact GlobalTheory.ShiftUnitPart.exists_shift_div_monomial | (intros; apply GlobalTheory.ShiftUnitPart.exists_shift_div_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyPointOfPrincipalObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

theorem dense_asIdeal_eq_bot_spMap (n : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁]
    (b₁ : cycAway n →+* V₁) : Dense {x : Sp V₁ | (spMap b₁ x).asIdeal = ⊥} := by
  let p₀ : Sp V₁ := ⟨⊥, Ideal.isPrime_bot⟩
  let K := FractionRing V₁
  have hinj : Function.Injective (algebraMap V₁ K) := IsFractionRing.injective V₁ K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hmem : p₀ ∈ {x : Sp V₁ | (spMap b₁ x).asIdeal = ⊥} := by
    let q : Sp K := ⟨⊥, Ideal.isPrime_bot⟩
    have h := GlobalTheory.AbChart.asIdeal_eq_bot_of_charZero n K (spMap ((algebraMap V₁ K).comp b₁)) q
    show Ideal.comap b₁ (⊥ : Ideal V₁) = ⊥
    have hc : Ideal.comap (algebraMap V₁ K) (⊥ : Ideal K) = ⊥ :=
      (RingHom.ker_eq_bot_iff_eq_zero _).2 fun a ha => hinj (by rw [ha, map_zero])
    rw [← hc, Ideal.comap_comap]
    exact h
  have hcl : closure ({p₀} : Set (Sp V₁)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    exact (PrimeSpectrum.le_iff_mem_closure (R := V₁) p₀ x).1 bot_le
  refine Dense.mono (Set.singleton_subset_iff.2 hmem) ?_
  exact dense_iff_closure_eq.2 hcl

theorem exists_sFam_point : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁]
    (b₁ : cycAway n →+* V₁) (s : SiegPre h n (zetaAway n) (spMap b₁)), s.Principal →
    ∃ (F : SFam h n (zetaAway n)) (x : Sp V₁ ⟶ F.X), x ≫ F.s = spMap b₁ ∧ SiegPB s F.univ x := by
  intro n hn hodd h V₁ _ _ _ b₁ s hs
  obtain ⟨F⟩ : Nonempty (SFam h n (zetaAway n)) := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · exact ⟨zeroFam n hn⟩
    · exact GlobalTheory.SiegelTor.exists_sFam_cycAway h n hh hn hodd
  obtain ⟨x, hx, hpb⟩ := F.rep (Sp V₁) (spMap b₁) s inferInstance (dense_asIdeal_eq_bot_spMap n V₁ b₁) hs
  exact ⟨F, x, hx, hpb⟩

end GlobalTheory.LowChart
end
end

