import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPelUniformisationCompleteDvrStatement
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0108
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0116
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0114
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnifAfterExt

theorem exists_finite_split {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      ∃ S : SplitExt (Sp k'), S.IsGt ((Over.pullback (spMap (algebraMap k k'))).obj G) := by
  have := hG.smooth
  obtain ⟨k', hk, T⟩ := exists_finite_torusExtension k (AlgebraicClosure k) G
    inferInstance hG.quasiCompact hG.separated (hG.fibres _ _)
  have := hG.comm
  exact ⟨k', inferInstance, inferInstance, hk, exists_splitExt_isGt_of_torusExtension _ _ T⟩

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [Finite (ResidueField W)] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧ Finite (ResidueField W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, E, ⟨d⟩⟩ := exists_finite_split _ h₀
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, hl, -, e, he⟩ := GlobalTheory.unramExt W k'
  have hfk : Finite k' := Module.finite_of_finite (ResidueField W)
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  have key : (e.symm.toRingHom.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') :=
    RingHom.ext fun v => e.symm_apply_eq.2 (he v).symm
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e.symm.toRingHom)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e.symm.toRingHom) E _ d)⟩

theorem exists_generic_square {V W : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (f : V →+* W)
    (hf : Function.Injective f) :
    ∃ g : Sp (FractionRing W) ⟶ Sp (FractionRing V), jK W ≫ spMap f = g ≫ jK V := by
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp f) := (IsFractionRing.injective W _).comp hf
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift hinj
  have hg : ∀ r, g (algebraMap _ _ r) = algebraMap W _ (f r) := fun r => IsFractionRing.lift_algebraMap hinj r
  clear_value g
  have e : spMap g ≫ jK V = jK W ≫ spMap f := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext hg))
  exact ⟨_, e.symm⟩

theorem isOpen_of_range_generic_subset (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (U : Set (Sp V)) (hU : Set.range (jK V) ⊆ U) : IsOpen U := by
  have hgen : ∀ x : Sp V, x ≠ closedPoint V → x ∈ U := fun x hx => by
    have h0 : x.asIdeal = ⊥ := by
      by_contra hne
      exact hx (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal hne)))
    refine hU ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)), PrimeSpectrum.ext ?_⟩
    rw [h0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  by_cases hc : (closedPoint V : Sp V) ∈ U
  · have : U = Set.univ := Set.eq_univ_of_forall fun x => by
      by_cases hx : x = closedPoint V
      · exact hx ▸ hc
      · exact hgen x hx
    rw [this]; exact isOpen_univ
  · have : U = {(closedPoint V : Sp V)}ᶜ := Set.ext fun x => ⟨fun hx h => hc (h ▸ hx), hgen x⟩
    rw [this]
    exact (IsLocalRing.isClosed_singleton_closedPoint V).isOpen_compl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_of_sabMap {S S' X : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K K' : Type} [Field K] [Field K'] {tK : SAB H (Sp K)} {j : Sp K ⟶ S} (mK : SABMap tK t j)
    {u : SAB H X} {x : Sp K ⟶ X} (mx : SABMap tK u x) (hp : IsProper u.G.hom) (ha : RelAmple u.G u.PP.L)
    (hk : KTriv u.G u.PP.L) (j' : Sp K' ⟶ S') (g : Sp K' ⟶ Sp K) (h : j' ≫ f = g ≫ j) : GlobalTheory.LN.PolAt t' j' := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull j' t'
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t₂ : SAB H (Sp K')) (p : Sp K' ⟶ S) (_ : p = g ≫ j) (_ : SABMap t₂ t p),
      Nonempty (SABMap t₂ u (g ≫ x)) := by
    intro t₂ p hp n
    subst hp
    exact ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx
      (sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mK n).choose).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ h n
  have h₂ : LBIso PP'.L (t'.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (u.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t'.PP.isLB (pullback.fst t'.G.hom j')
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 hp,
    amplePt _ _ (g ≫ x) _ _ m₃.φ m₃.cart _ _ u.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull u.PP.isLB _) h₂.symm h₃) ha hk⟩

theorem isOpen_and_uniformised (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [hz : CharZero W]
    (hc : IsAdicComplete (maximalIdeal W) W) (t : SAB H (Sp W)) (hp : GlobalTheory.LN.PolAt t (jK W))
    (hS : ∃ S : SplitExt (Sp (ResidueField W)), S.IsGt ((Over.pullback (spMap (residue W))).obj t.G)) :
    IsOpen (abLocus t.G) ∧ UniformisationConclusion t (abLocus t.G) := by
  obtain ⟨L₁, L₂, L₃, L₄, L₅⟩ := GlobalTheory.firstFiveLaws
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, hc, hz⟩
  have hadm : GlobalTheory.LN.admitted W (maximalIdeal W) := by
    refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hc, hz, inferInstance, ?_⟩
    letI := Ideal.Quotient.field (maximalIdeal W)
    infer_instance
  have ho := isOpen_of_range_generic_subset W _ (abLocusOne _ _ t.semi _ _ hp.1)
  obtain ⟨A, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H W t hp
  obtain ⟨P, -, -, hP⟩ := GlobalTheory.T.exists_pel_uniformisation_complete_dvr E H W hW t A gen hg hw hS
  exact ⟨ho, P, GlobalTheory.psiUnitOn_abLocus_pel L₁ L₂ L₃ L₄ L₅ E H W _ hadm t P hP ho, hP⟩

theorem exists_finite_ext_uniformised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (tK : SAB H (Sp T.Fr)) (_ : SABMap tK t (jK T.V)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap tK Xo.univ.t x), T.FinRes → ∃ (T' : Formalism.L2.Pj.CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)) (_ : SABMap t' t (spMap φ)), Function.Injective φ ∧ φ.Finite ∧ T'.FinRes ∧ IsOpen (abLocus t'.G) ∧ UniformisationConclusion t' (abLocus t'.G) := by
  intro E _ _ _ H Dw l Xo T t tK mK x mx hT
  have : Finite (ResidueField T.V) := hT
  obtain ⟨W, _, _, _, hc, _, hf, hi, hr, hS⟩ := exists_split_baseChange T.V t.G t.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  obtain ⟨t', m, hS'⟩ : ∃ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap (algebraMap T.V W))),
      ∃ S : SplitExt (Sp (ResidueField W)), S.IsGt ((Over.pullback (spMap (residue W))).obj t'.G) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap T.V W)) t
    exact ⟨_, m, hS⟩
  obtain ⟨gam, hsq⟩ := exists_generic_square (algebraMap T.V W) hi
  have hp := polAt_of_sabMap m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK W) gam hsq
  obtain ⟨ho, hN⟩ := isOpen_and_uniformised W hc t' hp hS'
  exact ⟨{ V := W }, algebraMap T.V W, t', m, hi, RingHom.finite_algebraMap.2 hf, hr, ho, hN⟩

end GlobalTheory.UnifAfterExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PermutesPeriodSpacesIdOfFixesCmCurveTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem isHolTo_subst {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set W} {y : W → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) {φ : V → W}
    (hφ : Differentiable ℂ φ) (hB : ∀ z, φ z ∈ B) : IsHolTo Set.univ (fun z => y (φ z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hy U f
  have e : {b ∈ (Set.univ : Set V) | ⊤ ≤ y (φ b) ⁻¹ᵁ U} = φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun z => ⟨fun h => ⟨hB z, h.2⟩, fun h => ⟨trivial, h.2⟩⟩
  refine ⟨?_, ?_⟩
  · beta_reduce
    rw [e]
    exact h1.preimage hφ.continuous
  · beta_reduce
    rw [e]
    exact DifferentiableOn.comp (g := fun b => valAt' (y b) U f) (f := φ) h2 hφ.differentiableOn fun z hz => hz

theorem isHolTo_ex_at_period {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) :
    IsHolTo Set.univ (fun z => (F.ex i P z).left) :=
  isHolTo_subst (φ := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z))
    (F.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
    (by fun_prop) fun _ => ⟨trivial, trivial⟩

theorem conj_point_eq_of_isSplit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0) (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ)
    (hτ : τ H.rt0 = H.rt0) (hfix : FixesCurve H τ l.M) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hs : IsSplit hP) : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
  obtain ⟨C, io, hC⟩ := hfix
  have hτσ : (τ : ℂ →+* ℂ).comp σ = σ := GlobalTheory.ConjPermutes.ringHom_ext hA (by
    show τ (σ _) = σ _
    rw [hσ, hτ])
  obtain ⟨i', P', hP', hu⟩ := F.onto (spMap (τ : ℂ →+* ℂ) ≫ F.u i P)
    (by rw [Category.assoc, F.over_σ i P hP, GlobalTheory.ConjPermutes.spMap_comp, hτσ])
  obtain ⟨Φ, hE, hp, hm, hlev⟩ := marking_conj E H D l Xo σ g ty F hD hσ hty hA τ hτ C io hC.1 i P hP i' P' hP' hs
    hu.symm (1, 0) hC
  obtain ⟨L, hL⟩ := exists_complex_linear_of_pure_types E H _ _ g ty P P' hP hP' Φ hs (fun a ha => (hp a).2 ha)
    (fun a ha => (hm a).2 ha)
  have hw : wE H (1, 0) = 1 := by simp [wE]
  have hA' : ∀ a, ∃ x, Φ (F.t i a) = F.t i' a + l.A • x := fun a =>
    ⟨Φ (F.t i a) - F.t i' a, by rw [hA, one_smul, add_sub_cancel]⟩
  refine hu.symm.trans ((GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      E H D l Xo σ g ty hD hσ hty (F.Di i) (F.Di i')
      (F.t i) (F.t i') P P' (F.u i P) (F.u i' P') (F.ex i P) (F.ex i' P')
      ⟨F.over_σ i P hP, hP, ⟨F.ex_add i P hP, F.ex_onto i P hP, isHolTo_ex_at_period F i P hP,
        (F.ex_diff i P hP).1, (F.ex_diff i P hP).2⟩, F.ex_ker i P hP, F.ex_lin i P hP, F.ex_weil i P hP,
        F.ex_eta i P hP, F.ex_etaA i P hP⟩
      ⟨F.over_σ i' P' hP', hP', ⟨F.ex_add i' P' hP', F.ex_onto i' P' hP', isHolTo_ex_at_period F i' P' hP',
        (F.ex_diff i' P' hP').1, (F.ex_diff i' P' hP').2⟩, F.ex_ker i' P' hP', F.ex_lin i' P' hP',
        F.ex_weil i' P' hP', F.ex_eta i' P' hP', F.ex_etaA i' P' hP'⟩).2 ⟨Φ, L, hE, fun v hv => ?_, hA', hL⟩).symm
  have hmem : F.t i v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0) := by
    rw [show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hs]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨e, he⟩ := hlev v hv a ha b hb hab.symm
  rw [hw, map_one, one_smul, one_smul, hab] at he
  exact ⟨-e, by rw [he, smul_neg, add_neg_cancel_right]⟩

theorem permutes_id_of_fixesCurve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → FixesCurve H τ l.M → ConjugationPermutesPeriods F τ id := by
  intro E _ _ _ H D l Xo σ g ty F hpq hσ hty hA hsig τ hτ hC
  obtain ⟨π, hπ⟩ := GlobalTheory.ConjPermutes.exists_perm E H D l Xo σ g ty F hpq hσ hty hA τ hτ
  have hid : ∀ i, π i = i := by
    intro i
    obtain ⟨P, hP, hs⟩ := exists_isSplit_period E H D l Xo σ g ty F hpq hσ hty hA hsig i
    have h1 := conj_point_eq_of_isSplit F hpq hσ hty hA τ hτ hC i P hP hs
    obtain ⟨P', hP', h2⟩ := hπ i P hP
    exact (F.disj i (π i) P P' hP hP' (h1.symm.trans h2)).symm
  have : (π : Fin F.n → Fin F.n) = id := funext hid
  rwa [this] at hπ

end GlobalTheory.CompRat
end

