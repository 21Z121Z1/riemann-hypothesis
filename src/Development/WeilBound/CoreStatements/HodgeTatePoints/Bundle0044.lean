import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0020
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0046
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.WeilBound.CoreStatements.HodgeTatePoints.RdNonunit
import Development.WeilBound.CoreStatements.HodgeTatePoints.RbProj
import Development.WeilBound.CoreStatements.HodgeTatePoints.RcFlag

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenGen
section
noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem eig_generic : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (I : Type) [Fintype I] [DecidableEq I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), Function.Injective σ → Fintype.card I = Module.finrank ℚ F → DirectSum.IsInternal fun s => eigSp ρ (σ s) := by
  intro Ω _ _ E _ _ F _ _ ρ I _ _ σ hσ hcard
  classical
  let τ : I → (F →+* Ω) := fun s => IsFractionRing.lift (EigSplit.injective_of_charZero F (σ s))
  have hτ : ∀ s (a : 𝓞 F), τ s (a : F) = σ s a := fun s a =>
    IsFractionRing.lift_algebraMap (EigSplit.injective_of_charZero F (σ s)) a
  have hτinj : Function.Injective τ := by
    intro s t hst'
    apply hσ
    ext a
    rw [← hτ, ← hτ, hst']
  let j : (F →+* Ω) → (F →ₐ[ℚ] AlgebraicClosure Ω) := fun φ =>
    ((algebraMap Ω (AlgebraicClosure Ω)).comp φ).toRatAlgHom
  have hj : Function.Injective j := by
    intro φ ψ hφψ
    ext x
    apply (algebraMap Ω (AlgebraicClosure Ω)).injective
    have := DFunLike.congr_fun hφψ x
    simpa [j] using this
  haveI : Finite (F →+* Ω) := Finite.of_injective j hj
  letI : Fintype (F →+* Ω) := Fintype.ofFinite _
  have hle : Fintype.card (F →+* Ω) ≤ Module.finrank ℚ F := by
    rw [← AlgHom.card ℚ F (AlgebraicClosure Ω)]
    exact Fintype.card_le_of_injective j hj
  have hge : Module.finrank ℚ F ≤ Fintype.card (F →+* Ω) := hcard ▸ Fintype.card_le_of_injective τ hτinj
  have hc : Fintype.card (F →+* Ω) = Module.finrank ℚ F := le_antisymm hle hge
  have hbij : Function.Bijective τ :=
    (Fintype.bijective_iff_injective_and_card τ).2 ⟨hτinj, hcard.trans hc.symm⟩
  have hsum : ∑ s, HT.eigProj ρ (τ s) = 1 := by
    rw [← HT.sum_eigProj_eq_one Ω E F ρ hc]
    exact hbij.sum_comp fun φ => HT.eigProj ρ φ
  have heig : ∀ s, eigSp ρ (σ s) = HT.eigSp ρ (τ s) := by
    intro s
    ext v
    simp [GlobalTheory.CompanionTheory.Ar.eigSp, HT.eigSp, Submodule.mem_iInf, sub_eq_zero, hτ]
  have spec := fun s => HT.ProjEig.eigProj_spec Ω E F ρ (τ s)
  simp only [heig]
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (fun s => ?_) ?_
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have h0 : ⨆ t, ⨆ (_ : t ≠ s), HT.eigSp ρ (τ t) ≤ LinearMap.ker (HT.eigProj ρ (τ s)) :=
      iSup₂_le fun t ht y hy => (spec s).2.2.1 (τ t) (hτinj.ne ht) y hy
    have := h0 hx'
    rwa [LinearMap.mem_ker, (spec s).2.1 x hx] at this
  · rw [eq_top_iff]
    intro x _
    have h : x = ∑ s, HT.eigProj ρ (τ s) x := by
      rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
    rw [h]
    exact Submodule.sum_mem _ fun s _ => Submodule.mem_iSup_of_mem s ((spec s).1 x)

theorem isIntegral_tensor {O Ω₀ F : Type} [CommRing O] [Field Ω₀] [CharZero Ω₀] [Field F] [Algebra O Ω₀]
    [Algebra O F] (hF : ∀ u : F, IsAlgebraic ℤ u) : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := by
  have h1 : ∀ u : F, _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] u) := by
    intro u
    obtain ⟨a, ha, hi⟩ := (hF u).exists_integral_multiple
    have h2 : _root_.IsIntegral ℤ ((1 : Ω₀) ⊗ₜ[O] (a • u)) :=
      hi.map_of_comp_eq (RingHom.id ℤ) (Algebra.TensorProduct.includeRight : F →ₐ[O] Ω₀ ⊗[O] F).toRingHom
        (Subsingleton.elim _ _)
    have h3 : _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] (a • u)) :=
      h2.map_of_comp_eq (Int.castRingHom Ω₀) (RingHom.id _) (Subsingleton.elim _ _)
    have ha' : (a : Ω₀) ≠ 0 := Int.cast_ne_zero.2 ha
    have e : (1 : Ω₀) ⊗ₜ[O] u = (a : Ω₀)⁻¹ • ((1 : Ω₀) ⊗ₜ[O] (a • u)) := by
      rw [TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul Ω₀, smul_smul, inv_mul_cancel₀ ha', one_smul]
    rw [e]
    exact h3.smul _
  refine ⟨fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul a u =>
    have e : a ⊗ₜ[O] u = a • ((1 : Ω₀) ⊗ₜ[O] u) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e]
    exact (h1 u).smul a
  | add x y hx hy => exact hx.add hy

theorem eq_of_specializes_of_fst {X : Scheme.{0}} {O F Ω₀ : Type} [CommRing O] [Field F] [Field Ω₀] [CharZero Ω₀]
    (s : X ⟶ Sp O) (β : O →+* F) (g₀ : O →+* Ω₀) (ξ₀ : Sp Ω₀ ⟶ X) (h₀ : IsCptGen ξ₀) (hs : ξ₀ ≫ s = spMap g₀)
    (hF : ∀ u : F, IsAlgebraic ℤ u)
    {y y' : ↥(pullback s (spMap β))} (hy : pullback.fst s (spMap β) y = genPt ξ₀) (hyy : y' ⤳ y) : y' = y := by
  letI := β.toAlgebra
  letI := g₀.toAlgebra
  have hy' : pullback.fst s (spMap β) y' = genPt ξ₀ :=
    GlobalTheory.CompanionTheory.Ar.CptInh.nogen ξ₀ h₀ _ (hy ▸ hyy.map (pullback.fst s (spMap β)).continuous)
  have hsurj : SurjectiveOnStalks ξ₀ := by
    have : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀]
    infer_instance
  have hemb := SurjectiveOnStalks.isEmbedding_pullback (pullback.fst s (spMap β)) ξ₀
  obtain ⟨z, hz, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y
    (IsLocalRing.closedPoint Ω₀) hy
  obtain ⟨z', hz', hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y'
    (IsLocalRing.closedPoint Ω₀) hy'
  have hzz : z' ⤳ z := by
    rw [← hemb.isInducing.specializes_iff, specializes_prod]
    simp only [hz, hz', hz₂, hz₂']
    exact ⟨hyy, specializes_rfl⟩
  have sq : IsPullback (pullback.snd (pullback.fst s (spMap β)) ξ₀)
      (pullback.fst (pullback.fst s (spMap β)) ξ₀ ≫ pullback.snd s (spMap β)) (spMap g₀) (spMap β) := by
    rw [← hs]
    exact (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip.paste_vert
      (IsPullback.of_hasPullback s (spMap β))
  let e := sq.isoPullback ≪≫ pullbackSpecIso O Ω₀ F
  have hint : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := isIntegral_tensor hF
  let p' : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z'
  let p : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z
  have hle : p' ≤ p := (PrimeSpectrum.le_iff_specializes _ _).2 (hzz.map e.hom.continuous)
  have hcm : (Ideal.comap (algebraMap Ω₀ (Ω₀ ⊗[O] F)) p'.asIdeal).IsMaximal :=
    Ideal.IsPrime.isMaximal' (Ideal.comap_isPrime _ _)
  have hmax : p'.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Ω₀) p'.asIdeal hcm
  have heq : p' = p := PrimeSpectrum.ext (hmax.eq_of_le p.isPrime.ne_top hle)
  have hzeq : z' = z := by
    have h := congrArg e.inv heq
    simpa [p, p'] using h
  rw [← hz, ← hz', hzeq]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem exists_lift : ∃ x : Sp Ω ⟶ Xo.XF c, 𝔐.ξ ≫ 𝔐.f = x ≫ Y.j := by
  have hchar : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  haveI : CharZero 𝔐.Ω₀ := 𝔐.fn.charZero
  let g₀ : O →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hs : 𝔐.ξ₀ ≫ Y.s = spMap g₀ := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfn : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over
  have hw : (𝔐.ξ ≫ 𝔐.f) ≫ Y.s = spMap 𝔐.cst ≫ spMap β := by
    rw [Category.assoc, 𝔐.cst_over]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let g : Sp Ω ⟶ pullback Y.s (spMap β) := pullback.lift (𝔐.ξ ≫ 𝔐.f) (spMap 𝔐.cst) hw
  have hgf : g ≫ pullback.fst _ _ = 𝔐.ξ ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hall : ∀ w : Sp Ω, pullback.fst Y.s (spMap β) (g w) = genPt 𝔐.ξ₀ := by
    intro w
    rw [← Scheme.Hom.comp_apply, hgf, hfn, Scheme.Hom.comp_apply]
    exact congrArg 𝔐.ξ₀ (Subsingleton.elim (α := PrimeSpectrum 𝔐.Ω₀) _ _)
  have := HodgeBasic.noetherianSpace_pullback Y.proj β
  have := Y.jQ_open
  have := c.fin
  have hF : ∀ u : c.F, IsAlgebraic ℤ u := fun u =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic u)
  have hran : Set.range g ⊆ Set.range Y.jQ := by
    rintro _ ⟨w, rfl⟩
    exact HodgeBasic.mem_of_dense_of_maximal Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense fun y' h' =>
      eq_of_specializes_of_fst Y.s β g₀ 𝔐.ξ₀ 𝔐.gen₀ hs hF (hall w) h'
  refine ⟨IsOpenImmersion.lift Y.jQ g hran, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hgf]

theorem isProper_gen : IsProper (pullback.snd 𝔐.t.G.hom 𝔐.ξ) := by
  obtain ⟨x, hx⟩ := exists_lift 𝔐
  haveI := Y.oF.proper
  have sq : IsPullback (pullback.fst 𝔐.t.G.hom 𝔐.ξ ≫ 𝔐.m.φ) (pullback.snd 𝔐.t.G.hom 𝔐.ξ) Y.t.G.hom
      (𝔐.ξ ≫ 𝔐.f) := (IsPullback.of_hasPullback 𝔐.t.G.hom 𝔐.ξ).paste_horiz 𝔐.m.cart.1
  have sq' : IsPullback (pullback.fst Y.oF.t.G.hom x ≫ Y.m.φ) (pullback.snd Y.oF.t.G.hom x) Y.t.G.hom
      (x ≫ Y.j) := (IsPullback.of_hasPullback Y.oF.t.G.hom x).paste_horiz Y.m.cart.1
  rw [hx] at sq
  rw [← sq.isoIsPullback_hom_snd _ _ sq']
  infer_instance

theorem finrank_Vgen (s : CMType H ⊕ CMType H) : Module.Finite Ω (𝔐.Vgen s) ∧
    Module.finrank Ω (𝔐.Vgen s) = labelRk D s := by
  obtain ⟨U, hU, b, hb, hfr⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ (Set.mem_univ _)
  have hli := (hfr ⟨genPt 𝔐.ξ, specializes_rfl⟩ (Set.mem_univ _) hU).1
  have e : 𝔐.Vgen s = Submodule.span Ω (Set.range b) := hb.symm
  rw [e]
  exact ⟨Module.Finite.span_of_finite Ω (Set.finite_range b), by rw [finrank_span_eq_card hli, Fintype.card_fin]⟩

theorem two_mul_finrank : 2 * Module.finrank Ω 𝔐.Li = Module.finrank ℤ D.La := by
  classical
  have hchar : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hinj : Function.Injective 𝔐.emb := by
    intro s s' h
    refine HodgeBasic.labelEmb_injective c (RingHom.ext fun a => 𝔐.cst.injective ?_)
    exact congrArg (fun m : 𝓞 E →+* Ω => m a) h
  letI : Fintype (CMType H) := Fintype.ofFinite _
  have hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
    rw [Fintype.card_of_bijective (HodgeBasic.labelHom_bijective H), Embeddings.card]
  have hint : DirectSum.IsInternal 𝔐.Vgen := eig_generic Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hcard
  haveI := fun s => (finrank_Vgen 𝔐 s).1
  have h1 : Module.finrank Ω 𝔐.Li = ∑ s, labelRk D s := by
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap 𝔐.Vgen) hint).finrank_eq, Module.finrank_directSum]
    exact Finset.sum_congr rfl fun s _ => (finrank_Vgen 𝔐 s).2
  rw [h1, GlobalTheory.datum_finrank_int D, ← hcard, Fintype.sum_sum_type, Fintype.card_sum, ← two_mul,
    Nat.mul_div_cancel_left _ two_pos]
  simp [labelRk]
  ring

end PositivityTheory.HtPt.Hcptgen
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfTop
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.HtPt.Htat.HopfOrderEqTop

theorem btOrder_eq_top (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T]
    [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hU : Γ.IsFinOpenSub U) :
    Γ.btOrder U = Γ.btOrder ⊤ := by
  ext f
  rw [PositivityTheory.HtPt.Twhopf.mem_order, PositivityTheory.HtPt.Twhopf.mem_order]
  refine ⟨fun hf t g _ => ?_, fun hf t g _ => hf t g trivial⟩
  obtain ⟨R', _, _, _, _, hN, hflat, hP⟩ :=
    @hHenselian R _ _ _ (Γ.G.hom g).asIdeal (Γ.G.hom g).isPrime
  have hinj : Function.Injective (algebraMap R R') := FaithfulSMul.algebraMap_injective R R'
  obtain ⟨Γ', F, hF⟩ := hBaseChange R T Γ R' (algebraMap R R') hinj
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp (algebraMap R R')) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hinj
  let κ : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hκa : ∀ r, κ (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) := fun r =>
    IsFractionRing.lift_algebraMap hinj' r
  have hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') := RingHom.ext hκa
  obtain ⟨g', hg1, hg2⟩ := Scheme.exists_preimage_of_isPullback hF.cart g (IsLocalRing.closedPoint R') (by
    apply PrimeSpectrum.ext
    exact hP.symm)
  haveI := Γ'.quasiFinite
  haveI := Γ'.finPres
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  obtain ⟨U', hU'fin, hU'cl⟩ := PositivityTheory.HtPt.Twhopf.finite_part R' Γ'.G.left Γ'.G.hom
  have hU' := PositivityTheory.HtPt.Twhopf.finite_sub R' T Γ' U' hU'fin hU'cl
  have hFU := GlobalTheory.T.isFinOpenSub_base_change R T Γ R' Γ' F hF U hU
  have hle : F ⁻¹ᵁ U ≤ U' := PositivityTheory.HtPt.Twhopf.finite_le R' _ Γ'.G.hom _ _ hFU.finite hU'cl
  have h1 : (fun h => algebraMap R R' (f h)) ∈ Γ'.btSet (F ⁻¹ᵁ U) := by
    intro s x hx
    have := hRegular R T Γ R' Γ' F hF κ hκ _ x (hf s (F x) hx)
    simpa only [hκa] using this
  rw [← PositivityTheory.HtPt.Twhopf.mem_order, ← GlobalTheory.T.btOrder_eq_of_le_of_isFinOpenSub R' T Γ' U' _ hU' hFU hle, PositivityTheory.HtPt.Twhopf.mem_order] at h1
  rw [← hg1]
  refine PositivityTheory.HtPt.Htat.bt_reg_descent R T Γ R' Γ' F hF hflat κ hκ _ g' ?_
  simpa only [hκa] using h1 t g' (hU'cl g' hg2)

end PositivityTheory.HtPt.Htat.HopfOrderEqTop

theorem PositivityTheory.HtPt.Htat.bt_sub_eq_top_of (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  @PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top hHenselian hBaseChange hRegular
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RdNonunitFin
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem a_nonunit_rom_of (hom : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_product) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) :=
  a_nonunit_of @PositivityTheory.HtPt.Rb.proj_props @PositivityTheory.HtPt.Rc.step hom

end PositivityTheory.HtPt.Rd
end

