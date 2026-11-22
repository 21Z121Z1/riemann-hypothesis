import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0641
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialPointFactorsThroughChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

theorem exists_lift_toSpecΓ {Y : Scheme.{0}} (W : Y.Opens) (A : CommRingCat.{0})
    (ψ : Spec A ⟶ Y) (hψ : ⊤ ≤ ψ ⁻¹ᵁ W) :
    ∃ ψ' : Spec A ⟶ W.toScheme, ψ' ≫ W.ι = ψ ∧
      ψ' ≫ W.toSpecΓ = Spec.map (ψ.appLE W ⊤ hψ ≫ (Scheme.ΓSpecIso A).hom) := by
  refine ⟨(Spec A).topIso.inv ≫ ψ.resLE W ⊤ hψ, ?_, ?_⟩
  · rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.toIso_inv_ι,
      Category.id_comp]
  · rw [Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_appLE, Scheme.Opens.toSpecΓ_top,
      Spec.map_comp, SpecMap_ΓSpecIso_hom, ← Category.assoc, ← Category.assoc,
      Scheme.toIso_inv_ι, Category.id_comp]

theorem isAffineOpen_and_bijective_of_section :
    ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (U : B.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (N : Type) (n : N → Γ(Y, W)) (ψ : Spec (CommRingCat.of (MvPolynomial N Γ(B, U))) ⟶ Y), ψ ≫ π = Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U))) ≫ hU.fromSpec → ∀ (hψ : ⊤ ≤ ψ ⁻¹ᵁ W), (∀ s, (ψ.appLE W ⊤ hψ).hom (n s) = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N Γ(B, U)))).inv.hom (MvPolynomial.X s)) → W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n)) ≫ ψ = W.ι → IsAffineOpen W ∧ Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) := by
  intro B Y π U hU W hW N n ψ hπ hψ hn hι
  obtain ⟨ψ', h0, h1⟩ := exists_lift_toSpecΓ W _ ψ hψ
  set g := ψ.appLE W ⊤ hψ ≫ (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N Γ(B, U)))).hom with hg
  have h2 : π.appLE U W hW ≫ g =
      CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U)) := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, ← hπ, Spec.map_comp, ← h1, Category.assoc, Category.assoc,
      ← Category.assoc W.toSpecΓ, Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc,
      hU.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι, ← Category.assoc, h0]
  set ev : CommRingCat.of (MvPolynomial N Γ(B, U)) ⟶ Γ(Y, W) :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) with hev
  have h3 : ev ≫ g = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro c
      have := congrArg (fun f => f.hom c) h2
      simpa [hev] using this
    · intro s
      simp [hev, hg, hn s]
  have h4 : ψ' ≫ (W.toSpecΓ ≫ Spec.map ev) = 𝟙 _ := by
    rw [← Category.assoc, h1, ← Spec.map_comp, h3, Spec.map_id]
  have h5 : (W.toSpecΓ ≫ Spec.map ev) ≫ ψ' = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, h0, Category.assoc, hι, Category.id_comp]
  haveI : IsIso (W.toSpecΓ ≫ Spec.map ev) := ⟨ψ', h5, h4⟩
  have hWa : IsAffineOpen W := IsAffine.of_isIso (W.toSpecΓ ≫ Spec.map ev)
  refine ⟨hWa, ?_⟩
  haveI : IsIso W.toSpecΓ := by
    rw [← hWa.isoSpec_hom]; infer_instance
  haveI : IsIso (Spec.map ev) := IsIso.of_isIso_comp_left W.toSpecΓ _
  haveI : IsIso ev := by
    have h : IsIso (Scheme.Spec.map ev.op) := this
    haveI := isIso_of_reflects_iso ev.op Scheme.Spec
    exact isIso_of_op ev
  exact ConcreteCategory.bijective_of_isIso ev

end GlobalTheory.FlagCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.HomTor

theorem pow_comp_monHom {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem exists_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G), IsMonHom p → ∃ ρ, TorMatch U U' (RingHom.id R) p.left ρ := by
  intro R _ _ _ hR G _ _ hG D A U G' _ _ hG' D' A' U' p hpm
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have hp' := isGrpPullback_pullback G' (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G'.hom (spMap (residue R)) ≫ p.left := pullback.lift_fst _ _ _
  have hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map p) :=
    Out.PullGtPf.isMonHom_of_grpPullback hp' hp p _ e
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _
    (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p) inferInstance
  refine ⟨ρ, ?_⟩
  intro F _ _ i₁ i₂ hF k hk τ τ' q q' a a' hτ'k hττ' hqy hq hq'y hq' ha ha'
  have hi : i₁ = i₂ := Algebra.algebra_ext _ _ fun x =>
    RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R)
      (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext hF)) x
  subst hi
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.ToricTorsionUnif.main R hR G' hG' D' A' U' k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {H : Type} [CommGroup H] (f : Multiplicative D'.toPre.X →* H), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  let c : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  rw [s4 F c τ hτk q a rfl hqy hq ha, ← Category.assoc, s4' F c τ' hτ'k q' a' rfl hq'y hq' ha']
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing c
  let φ : R →+* O := c.codRestrict O.toSubring hO
  haveI : IsLocalHom φ := hloc
  have hc : c = O.subtype.comp φ := rfl
  obtain ⟨τO, hτO⟩ := GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl
  let τR := τO.comp ρm
  have hτR : τR ^ k = 1 := powc τO hτOk
  have hkO : IsUnit (k : O) := by simpa using hk.map φ
  have hxy : s O φ τR hτR = s' O φ τO hτOk ≫ p := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap φ) k hkO _ _ ?_
      (ResidueField O) (residue O) inferInstance ?_
    · rw [s1, ← pow_comp_monHom, s1', MonObj.one_comp]
    · let τ₀ : Multiplicative D'.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp τO
      have h₀ : τ₀ ^ k = 1 := by
        rw [show τ₀ ^ k = (Units.map (residue O).toMonoidHom).comp (τO ^ k) by ext x; simp [τ₀]]
        rw [hτOk]; ext; simp
      let τ₁ := τ₀.comp ρm
      have h₁ : τ₁ ^ k = 1 := powc τ₀ h₀
      let z : Over.mk (spMap (ResidueField.map φ)) ⟶ splitTorus (Sp (ResidueField R)) D'.toPre.X :=
        (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
          ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp τ₀)
      have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]; rfl
      have hz₁ : ∀ χ, GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap _ ρ) χ = unitOn (τ₁ (Multiplicative.ofAdd χ)) :=
        fun χ => by
          apply Units.ext
          rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
            GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
            ← GlobalTheory.UU.chV_val, hz]
          rfl
      have hres : (residue O).comp φ = (ResidueField.map φ).comp (residue R) := by
        ext r; simp [ResidueField.map_residue]
      rw [Over.comp_left, ← Category.assoc,
        ← s2 O _ φ ((residue O).comp φ) (residue O) τR hτR τ₁ h₁ rfl (fun χ => rfl),
        ← s2' O _ φ ((residue O).comp φ) (residue O) τO hτOk τ₀ h₀ rfl (fun χ => rfl),
        s3 _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp τ₁ h₁ _ hres hz₁,
        s3' _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp' τ₀ h₀ z hres hz,
        Category.assoc z, ← hρ, Category.assoc _ _ p.left, ← e]
      simp only [Over.comp_left, Category.assoc]
  rw [s2 O F φ c O.subtype τR hτR τ hτk hc (fun χ => by simp [τR, hτ, hτO]),
    s2' O F φ c O.subtype τO hτOk τ' hτ'k hc (fun χ => by simp [hτO]), hxy, Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.HomTor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverRestrictEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_restrict : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E' : DivOver (f ≫ p), E'.Through y → ∃ E : DivOver p, E.Through (f y) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  intro M W _ _ _ _ p f _ n _ _ U hf y hy E' hE'
  have e := functionFieldMap_comp_constFn p f
  have hc : ∀ a, functionFieldMap f (Cartier.constFn p a) ∈ E'.ring := fun a => by
    rw [← RingHom.comp_apply, e]; exact E'.const_mem a
  obtain ⟨z, hzy, hz⟩ := GlobalTheory.T.exists_specializes_dominatesStalk_of_regular M E'.ring y hE'
  have hzU : z ∈ U := hzy.mem_open U.isOpen hy
  have hfin := GlobalTheory.T.finiteDimensional_functionField_of_etale_on_open' M W f U hf ⟨y, hy⟩
  have hess' : ((functionFieldMap f).comp (Cartier.constFn p)).codRestrict E'.ring hc =
      (Cartier.constFn (f ≫ p)).codRestrict E'.ring E'.const_mem :=
    RingHom.ext fun a => Subtype.ext (RingHom.congr_fun e a)
  obtain ⟨hdvr, hess⟩ := GlobalTheory.T.dvr_comap_finiteIndex_essFiniteType_complex W.functionField M.functionField (functionFieldMap f)
    (Cartier.constFn p) hfin E'.ring hc (hess' ▸ E'.essFiniteType)
  let E : DivOver p := ⟨E'.ring.comap (functionFieldMap f), hc, hdvr, hess⟩
  haveI : IsDiscreteValuationRing (E'.ring.comap (functionFieldMap f)) := hdvr
  have hun := GlobalTheory.T.etale_restrict_dvr_comap_dominatesStalk M W f U hf z hzU E'.ring hz
  let ψ : E.ring →+* E'.ring := (functionFieldMap f).restrict E.ring E'.ring fun _ hx => hx
  letI := ψ.toAlgebra
  have hψ : ψ.comp E.const = E'.const := RingHom.ext fun a => Subtype.ext (RingHom.congr_fun e a)
  have hft : Algebra.EssFiniteType E.ring E'.ring := by
    have h1 : (ψ.comp E.const).EssFiniteType := hψ ▸ E'.essFiniteType
    exact RingHom.EssFiniteType.of_comp E.const h1
  have hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := fun g =>
    GlobalTheory.T.log_ordFrac_comap_formallyUnramified_dvr W.functionField M.functionField (functionFieldMap f) E'.ring ⟨hun, hft⟩ g g.ne_zero
  refine ⟨E, fun g ⟨a, ha⟩ => ?_, hord, fun η hη => ?_⟩
  · show functionFieldMap f g ∈ E'.ring
    exact hE' _ ⟨f.stalkMap y a, by rw [← functionFieldMap_algebraMap, ha]⟩
  · haveI := SmoothOfRelativeDimension.smooth n p
    haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
    have hnW : topologicalKrullDim W = n := NadelApp.topologicalKrullDim_eq_of_smooth W p n
    have hnM : topologicalKrullDim M = n := NadelApp.topologicalKrullDim_eq_of_smooth M (f ≫ p) n
    obtain ⟨ω, hω, g, rfl, hg⟩ := E.isFormOrd_formOrd hnW hη
    have hω' := GlobalTheory.T.isFreeGenerator_topForms_of_formallyUnramified E.const E'.const ψ hψ n hun ω hω (E'.exists_isFreeGen hnM)
    have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ψ hψ ω) := by
      have h1 := formMap_formMap (D := n) E.ring.subtype (functionFieldMap f)
        ((functionFieldMap f).comp E.ring.subtype) rfl rfl e
        (by rw [RingHom.comp_assoc]; exact e) ω
      have h2 := formMap_formMap (D := n) ψ E'.ring.subtype
        ((functionFieldMap f).comp E.ring.subtype) rfl hψ rfl
        (by rw [RingHom.comp_assoc]; exact e) ω
      exact h1.trans h2.symm
    have hpull : ratPull p f n ((g : W.functionField) • E.toRat n ω) =
        ((Units.map (functionFieldMap f).toMonoidHom g : M.functionFieldˣ) : M.functionField) •
          E'.toRat n (TopForm.formMap n ψ hψ ω) := by
      rw [map_smulₛₗ, key]; rfl
    have hne : ratPull p f n ((g : W.functionField) • E.toRat n ω) ≠ 0 := by
      rw [hpull]
      refine smul_ne_zero (Units.ne_zero _) fun h0 => ?_
      have := (E'.isFreeGen_toRat hω').1 (a₁ := 0) (a₂ := 1) (by simp [h0])
      exact zero_ne_one this
    rw [← hg, ← hord g]
    exact DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', _, hpull, rfl⟩

end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.PrimCmp

theorem esymm_map_hom {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') (M : Multiset R) (j : ℕ) :
    (M.map i).esymm j = i (M.esymm j) := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => ?_)
  simp only [Function.comp, map_multiset_prod]

theorem symTup_map {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun b => i (c b)) j := by
  unfold symTup
  rw [map_pow]
  congr 1
  have hm : Finset.univ.val.map (fun b => i (c b)) = (Finset.univ.val.map c).map i := by
    rw [Multiset.map_map]; rfl
  rw [hm, esymm_map_hom]

theorem esymm_map_mul {R : Type} [CommRing R] {A : Type} (t : R) (M : Multiset A) (f : A → R) (j : ℕ) :
    (M.map fun b => t * f b).esymm j = t ^ j * (M.map f).esymm j := by
  have : (M.map fun b => t * f b) = (M.map f).map (fun x => t * x) := by rw [Multiset.map_map]; rfl
  rw [this]
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
  have hc := (Multiset.mem_powersetCard.1 hs).2
  simp only [Function.comp]
  rw [Multiset.prod_map_mul]
  simp [hc]

theorem symTup_mul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (t : R) (j : Fin N) :
    symTup (fun b => t * c b) j = t ^ N.factorial * symTup c j := by
  unfold symTup
  have h := esymm_map_mul t (Finset.univ.val) c ((j : ℕ) + 1)
  rw [h, mul_pow, ← pow_mul, Nat.mul_div_cancel' (Nat.dvd_factorial (Nat.succ_pos _) j.2)]

theorem mem_of_isIntegralElem {V K : Type} [CommRing V] [Field K] (i : V →+* K) (W : ValuationSubring K)
    (hW : ∀ v, i v ∈ W) {x : K} (hx : i.IsIntegralElem x) : x ∈ W := by
  obtain ⟨p, hm, hp⟩ := hx
  let φ : V →+* W := i.codRestrict W.toSubring hW
  have hφ : (algebraMap W K).comp φ = i := by ext v; rfl
  have hint : IsIntegral W x := ⟨p.map φ, hm.map φ, by rw [Polynomial.eval₂_map, hφ]; exact hp⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact y.2

theorem mem_of_pow_mem {K : Type} [Field K] (W : ValuationSubring K) {w : K} {k : ℕ} (hk : 1 ≤ k)
    (h : w ^ k ∈ W) : w ∈ W := by
  rw [← W.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff (by omega)).1 h

theorem mem_range_of_forall {V K : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K]
    (io : FractionRing V →+* K) (z : FractionRing V)
    (h : ∀ W : ValuationSubring K, (∀ v, io (algebraMap V (FractionRing V) v) ∈ W) → io z ∈ W) :
    z ∈ Set.range (algebraMap V (FractionRing V)) := by
  letI : Algebra V K := (io.comp (algebraMap V (FractionRing V))).toAlgebra
  have hic : IsIntegrallyClosedIn (integralClosure V K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure V K) K)
  have h1 : io z ∈ (integralClosure V K).toSubring := by
    by_contra hn
    obtain ⟨W, hW, hzW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
    exact hzW (h W (fun v => hW ((integralClosure V K).algebraMap_mem v)))
  let f : FractionRing V →ₐ[V] K := { io with commutes' := fun _ => rfl }
  have h2 : IsIntegral V z := (isIntegral_algHom_iff f (f : FractionRing V →+* K).injective).1 h1
  exact IsIntegrallyClosed.isIntegral_iff.1 h2

end GlobalTheory.UMin.PrimCmp

namespace GlobalTheory.UMin.PrimCmp

theorem key {V K : Type} [CommRing V] [IsDomain V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (a : K)
    (ha : a ≠ 0) (hP : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a)) (e : Fin N → FractionRing V)
    (he : ∀ j, io (e j) = symTup c j) (j₀ : Fin N) (he0 : e j₀ ≠ 0)
    (hq : ∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) (W : ValuationSubring K)
    (hW : ∀ v, io (algebraMap V (FractionRing V) v) ∈ W) :
    io (e j₀) / a ^ N.factorial ∈ W ∧ (io (e j₀) / a ^ N.factorial)⁻¹ ∈ W := by
  have hcW : ∀ b, c b / a ∈ W := fun b => mem_of_isIntegralElem _ W hW (hP.1 b)
  obtain ⟨b₀, hb0, hb0i⟩ := hP.2
  have hb0W : (c b₀ / a)⁻¹ ∈ W := mem_of_isIntegralElem _ W hW hb0i
  let y : Fin N → W := fun b => ⟨c b / a, hcW b⟩
  have hu : IsUnit (y b₀) := (Units.mkOfMulEqOne (y b₀) ⟨_, hb0W⟩ (Subtype.ext (show c b₀ / a * (c b₀ / a)⁻¹ = 1 from mul_inv_cancel₀ hb0))).isUnit
  let z : Fin N → W := fun b => y b * ↑hu.unit⁻¹
  have hz : z b₀ = 1 := by simp [z]
  obtain ⟨k, hk1, hkN, hku⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one W (Fin N) z b₀ hz
  have hyz : ∀ b, y b = y b₀ * z b := by
    intro b; simp only [z]; rw [mul_left_comm, IsUnit.mul_val_inv, _root_.mul_one]
  have hesy : IsUnit ((Finset.univ.val.map y).esymm k) := by
    have hm : Finset.univ.val.map y = Finset.univ.val.map (fun b => y b₀ * z b) :=
      Multiset.map_congr rfl fun b _ => hyz b
    rw [hm, esymm_map_mul]
    exact (hu.pow k).mul hku
  have hkN' : k ≤ N := by simpa using hkN
  let j₁ : Fin N := ⟨k - 1, by omega⟩
  have hsy : IsUnit (symTup y j₁) := by
    unfold symTup
    have : (j₁ : ℕ) + 1 = k := by simp only [j₁]; omega
    rw [this]
    exact hesy.pow _
  have hcoe : ∀ j, ((symTup y j : W) : K) = io (e j) / a ^ N.factorial := by
    intro j
    have h1 := symTup_map W.subtype y j
    rw [ValuationSubring.coe_subtype] at h1
    rw [h1]
    have h2 : (fun b => ((y b : W) : K)) = fun b => a⁻¹ * c b := by
      funext b; simp [y, div_eq_inv_mul]
    rw [h2, symTup_mul, he, inv_pow, inv_mul_eq_div]
  have ht : io (e j₀) / a ^ N.factorial ∈ W := hcoe j₀ ▸ (symTup y j₀).2
  obtain ⟨v, hv⟩ := hq j₁
  have hr : io (e j₁ / e j₀) ∈ W := by rw [← hv]; exact hW v
  have hio0 : io (e j₀) ≠ 0 := (map_ne_zero io).2 he0
  have hsplit : symTup y j₁ = ⟨_, hr⟩ * ⟨_, ht⟩ := by
    apply Subtype.ext
    rw [hcoe]
    show _ = io (e j₁ / e j₀) * (io (e j₀) / a ^ N.factorial)
    rw [map_div₀]
    field_simp
  rw [hsplit] at hsy
  have htu := isUnit_of_mul_isUnit_right hsy
  refine ⟨ht, ?_⟩
  have h3 : ((↑htu.unit⁻¹ : W) : K) * (io (e j₀) / a ^ N.factorial) = 1 := by
    have := congrArg Subtype.val (IsUnit.val_inv_mul htu)
    rw [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact this
  rw [← eq_inv_of_mul_eq_one_left h3]
  exact (↑htu.unit⁻¹ : W).2

end GlobalTheory.UMin.PrimCmp

theorem GlobalTheory.UMin.prim_symTup_cmp : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N N' k : ℕ) (J : Type) (c : Fin N → K) (c' : Fin N' → K) (a : K) (e : Fin N → FractionRing V) (th : J → FractionRing V), a ≠ 0 → 1 ≤ k → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) → (∀ j, io (e j) = symTup c j) → (∀ x, ∃ b, c' x ^ k = io (th b) ^ k) → (∀ b, ∃ x, c' x ^ k = io (th b) ^ k) → ∀ j₀, e j₀ ≠ 0 → (∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, th b ^ N.factorial / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ e j₀ / th b ^ N.factorial ∈ Set.range (algebraMap V (FractionRing V)) := by
  intro V K _ _ _ _ io N N' k J c c' a e th ha hk hP hP' he hth1 hth2 j₀ he0 hq
  refine ⟨fun b => ?_, ?_⟩
  · apply GlobalTheory.UMin.PrimCmp.mem_range_of_forall io
    intro W hW
    obtain ⟨-, hti⟩ := GlobalTheory.UMin.PrimCmp.key io N c a ha hP e he j₀ he0 hq W hW
    obtain ⟨x, hx⟩ := hth2 b
    have hw : io (th b) / a ∈ W := by
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [div_pow, ← hx, ← div_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP'.1 x)) k
    have hio0 : io (e j₀) ≠ 0 := (map_ne_zero io).2 he0
    have heq : io (th b ^ N.factorial / e j₀) = (io (th b) / a) ^ N.factorial * (io (e j₀) / a ^ N.factorial)⁻¹ := by
      rw [map_div₀, map_pow, div_pow, inv_div]
      field_simp
    rw [heq]
    exact mul_mem (pow_mem hw _) hti
  · obtain ⟨x₀, hx0, hx0i⟩ := hP'.2
    obtain ⟨b₁, hb1⟩ := hth1 x₀
    have hk0 : k ≠ 0 := by omega
    have hth0 : io (th b₁) ≠ 0 := by
      intro h0
      apply hx0
      have h2 : c' x₀ ^ k = 0 := by rw [hb1, h0, zero_pow hk0]
      simp [pow_eq_zero_iff hk0 |>.1 h2]
    refine ⟨b₁, fun h => hth0 (by rw [h, map_zero]), ?_⟩
    apply GlobalTheory.UMin.PrimCmp.mem_range_of_forall io
    intro W hW
    obtain ⟨ht, -⟩ := GlobalTheory.UMin.PrimCmp.key io N c a ha hP e he j₀ he0 hq W hW
    have hwi : (io (th b₁) / a)⁻¹ ∈ W := by
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [inv_pow, div_pow, ← hb1, ← div_pow, ← inv_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hx0i) k
    have heq : io (e j₀ / th b₁ ^ N.factorial) = (io (e j₀) / a ^ N.factorial) * ((io (th b₁) / a)⁻¹) ^ N.factorial := by
      rw [map_div₀, map_pow, inv_div, div_pow]
      field_simp
    rw [heq]
    exact mul_mem ht (pow_mem hwi _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

theorem isGenSec_of_univBasis {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {K K' : Type} [CommRing K]
    [CommRing K'] {x : Sp K ⟶ S} {e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))} (he : UnivBasis G L x e)
    (i : K →+* K') {x' : Sp K' ⟶ S} (h : spMap i ≫ x = x') :
    IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e) :=
  (isGenSec_iff _).2 fun s => by
    obtain ⟨c, hc, -⟩ := he K' i x' h s
    exact ⟨c, hc⟩

theorem spMap_id (K : Type) [CommRing K] : spMap (RingHom.id K) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem gen_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (g : ℕ) (K : Type)
    [Field K] (x : Sp K ⟶ S), PolFib G L g x → (∃ θ : SecAt G L x, IsGenSec G L _ θ) ∧
    ∀ θ : SecAt G L x, IsGenSec G L _ θ → ∀ (K' : Type) [Field K'] (i : K →+* K'),
      IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g K _ x hP
  obtain ⟨P, α, -, hp, hw⟩ := hP
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x
    (Category.id_comp x)
  have h0 : spMap (RingHom.id K) ≫ x = x := by rw [spMap_id, Category.id_comp]
  refine ⟨⟨_, isGenSec_of_univBasis he (RingHom.id K) h0⟩, fun θ hθ K' _ i => ?_⟩
  set e₀ := VVRank.pullS G _ (Over.homMk (spMap (RingHom.id K)) h0 : Over.mk x ⟶ Over.mk x) e with he₀
  obtain ⟨c, hc, -⟩ := he K (RingHom.id K) x h0 (SecM.ofSec G θ)
  obtain ⟨r, hr⟩ := (isGenSec_iff θ).1 hθ (SecM.ofSec G e₀)
  obtain ⟨c₀, -, hu⟩ := he K (RingHom.id K) x h0 (SecM.ofSec G e₀)
  have hrc : r * c = 1 := by
    have e1 : SecM.ofSec G e₀ = (r * c) • SecM.ofSec G e₀ := by
      conv_lhs => rw [hr, hc]
      rw [smul_smul]
    exact (hu _ e1).trans (hu 1 (one_smul _ _).symm).symm
  have hcu : IsUnit c := ⟨⟨c, r, by rw [mul_comm]; exact hrc, hrc⟩, rfl⟩
  have ha : IsUnit ((fnR x).symm c) := hcu.map (fnR x).symm
  have hb := he.smul_pull hL (RingHom.id K) h0 ha
  have eq : SecM.toSec G (fnR x ((fnR x).symm c) • pl (RingHom.id K) h0 (SecM.ofSec G e)) = θ := by
    rw [RingEquiv.apply_symm_apply, pl_ofSec, ← hc]
    rfl
  rw [eq] at hb
  exact isGenSec_of_univBasis hb i rfl

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionSplitRegularDivisorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_function_split_regular_divisor : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens), Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) → ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) → ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧ ∀ y ∈ W₂, D.RegularAt y h₂ := by
  first | exact @GlobalTheory.ratsec_split_of_H1 | exact GlobalTheory.ratsec_split_of_H1 | (intros; apply GlobalTheory.ratsec_split_of_H1 <;> assumption)
end

