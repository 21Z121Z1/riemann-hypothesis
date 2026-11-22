import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgeGenDesc

theorem isIso_fromNormalization {U X : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hX : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] :
    IsIso j.fromNormalization := by
  obtain ⟨h, ⟨h₁, h₂⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart X U X _ j hX ‹_› ‹_› ‹_› ‹_›
    j.fromNormalization (𝟙 X) j.toNormalization inferInstance (by simp)
  refine ⟨h, ?_, h₂⟩
  refine GlobalTheory.normalization_hom_ext j j.fromNormalization ?_ ?_
  · rw [Scheme.Hom.toNormalization_fromNormalization_assoc, h₁, Category.comp_id]
  · simp [h₂]

theorem bijective_app {U N X : Scheme.{0}} (hX : Geo.Tor.IsNormalScheme X) [IsLocallyNoetherian X] (u : U ⟶ N)
    (p : N ⟶ X) [QuasiCompact u] [IsSchemeTheoreticallyDominant u] [UniversallyClosed p] [IsPreimmersion (u ≫ p)]
    [Flat (u ≫ p)] [IsDominant (u ≫ p)] (V : X.Opens) : Function.Bijective (p.app V).hom := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have : IsDominant p := .of_comp u p
  have : IsSchemeTheoreticallyDominant p := .of_isDominant p
  have hI := (isIso_fromNormalization_iff (u ≫ p)).1 (isIso_fromNormalization (u ≫ p) hX)
  refine ⟨p.app_injective V, fun t => mem_range_app_of_forall_isAffineOpen p V t fun W hW _ => ?_⟩
  generalize N.presheaf.map _ t = t
  have ht : (p.app W).hom.IsIntegralElem t := GenPush.isIntegral_app_of_universallyClosed p W hW t
  have hs : ((u ≫ p).app W).hom.IsIntegralElem (u.app (p ⁻¹ᵁ W) t) := by
    change ((u.app (p ⁻¹ᵁ W)).hom.comp (p.app W).hom).IsIntegralElem _
    exact RingHom.IsIntegralElem.map ht _
  obtain ⟨h, hh⟩ := (hI W hW).2 _ hs
  refine ⟨h, u.app_injective (p ⁻¹ᵁ W) ?_⟩
  rw [← hh]
  rfl

theorem exists_iso_of_extensions {U X : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hX : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    {A : Over U} [GrpObj A] {G G' : Over X} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ G'.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A G' j ψ) :
    ∃ e : G ≅ G', IsMonHom e.hom := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have := hG.smooth
  have := hG'.smooth
  have := hG.separated
  have := hG'.separated
  obtain ⟨a, ha, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback G' j)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G G' hG hG' (a.inv ≫ b.hom) inferInstance
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G' G hG' hG (b.inv ≫ a.hom) inferInstance
  obtain ⟨h₁, h₂⟩ := ExtUnique.comp_eq_id_of_pullback j (a.symm ≪≫ b) F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, hF⟩

theorem lbIso_hodge_pull {S T : Scheme.{0}} {G : Over S} {G' : Over T} [GrpObj G] [GrpObj G'] [QuasiSeparated G.hom]
    {f : T ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {g : ℕ} (hg : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega G) g) :
    LBIso ((hodge G g).pull f) (hodge G' g) :=
  (hg.lbIso_det_pullback f).trans (pull_isLB hg.isLB_det f) (hg.pullback f).isLB_det
    (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h hg).isLB_det
    ((hg.pullback f).lbIso_det_of_iso (asIso (GlobalTheory.LieVB.omegaBase h)))

theorem isGenerated_of_pull {N X : Scheme.{0}} [CompactSpace X] (p : N ⟶ X) [Surjective p]
    (hp : ∀ V, Function.Bijective (p.app V).hom) {L : LB X} (h : IsGenerated (L.pull p)) : IsGenerated L := by
  refine isGenerated_iff_forall.2 fun x => ?_
  obtain ⟨n, rfl⟩ := p.surjective x
  obtain ⟨s', hs'⟩ := h.exists_mem n
  obtain ⟨s, rfl⟩ := (bijective_lbSecPull p hp _).2 s'
  exact ⟨s, by rwa [HodgeDominates.nonzeroLocus_lbSecPull] at hs'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F}

theorem j_s (Y : Model Xo c ω) : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap ω := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem exists_common_modification (hω : IsDedFrac ω) (Y C : Model Xo c ω) :
    ∃ (N : Scheme.{0}) (p : N ⟶ Y.X) (p' : N ⟶ C.X) (G : Over N) (_ : GrpObj G) (φ : G.left ⟶ Y.t.G.left)
      (ψ : G.left ⟶ C.t.G.left), Surjective p ∧ (∀ V, Function.Bijective (p.app V).hom) ∧
      IsGrpPullback G Y.t.G p φ ∧ IsGrpPullback G C.t.G p' ψ := by
  obtain ⟨_, _, _, _, _, _, _⟩ := ModelRelCompare.densePart Y hω
  obtain ⟨⟨_, _⟩, hi, -⟩ := hω
  have : CharZero R := ω.charZero
  have := Y.flat
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver C.proj
  have := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks Y.j
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap Y.j
  have : IsLocallyNoetherian (Xo.XF c) := AmpUniq.isLocallyNoetherian_of_isPreimmersion Y.j
  let f : Xo.XF c ⟶ pullback Y.s C.s := pullback.lift Y.j C.j ((j_s Y).trans (j_s C).symm)
  have hf₁ : f ≫ pullback.fst Y.s C.s = Y.j := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd Y.s C.s = C.j := pullback.lift_snd _ _ _
  have : IsPreimmersion (f ≫ pullback.fst Y.s C.s) := hf₁ ▸ inferInstance
  have : QuasiCompact (f ≫ pullback.fst Y.s C.s) := hf₁ ▸ inferInstance
  have : IsPreimmersion f := AmpUniq.isPreimmersion_of_comp f (pullback.fst Y.s C.s)
  have : QuasiCompact f := .of_comp f (pullback.fst Y.s C.s)
  have : Flat (f ≫ pullback.fst Y.s C.s ≫ Y.s) := by
    rw [reassoc_of% hf₁]; infer_instance
  have : IsFinite f.fromNormalization := AmpUniq.isFinite_fromNormalization_graph f (pullback.fst Y.s C.s ≫ Y.s)
  let u := f.toNormalization
  let p := f.fromNormalization ≫ pullback.fst Y.s C.s
  let p' := f.fromNormalization ≫ pullback.snd Y.s C.s
  have hu₁ : u ≫ p = Y.j := by simp [u, p, hf₁]
  have hu₂ : u ≫ p' = C.j := by simp [u, p', hf₂]
  have : IsPreimmersion (u ≫ p) := hu₁ ▸ inferInstance
  have : Flat (u ≫ p) := hu₁ ▸ inferInstance
  have : IsDominant (u ≫ p) := hu₁ ▸ inferInstance
  have : IsPreimmersion u := AmpUniq.isPreimmersion_of_comp u p
  have : Flat u := AmpUniq.flat_of_isPreimmersion u
  have hN := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsDominant p := .of_comp u p
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull p Y.t
  obtain ⟨_, _, _, _, _, n₂, -⟩ := sabPull Out.CubePf.cubePull p' C.t
  obtain ⟨m₀, -⟩ := ObjMaps.exists_sab_cancel (g := 𝟙 _) C.m0.toSABMap
    (by rw [Category.id_comp]; exact Y.m0.toSABMap : SABMap Y.oF.t Xo.univ.t (𝟙 _ ≫ pullback.fst _ _))
  obtain ⟨m₂, -⟩ := ObjMaps.exists_sab_comp C.m m₀
  obtain ⟨a₁, -⟩ := ObjMaps.exists_sab_cancel n₁ (hu₁ ▸ Y.m : SABMap Y.oF.t Y.t (u ≫ p))
  obtain ⟨a₂, -⟩ := ObjMaps.exists_sab_cancel n₂
    ((((Category.id_comp _).trans hu₂.symm : 𝟙 _ ≫ C.j = u ≫ p')) ▸ m₂ : SABMap Y.oF.t C.t (u ≫ p'))
  obtain ⟨e, _⟩ := exists_iso_of_extensions u hN (IsSemiAbelian.pullback p Y.t.G Y.t.semi)
    (IsSemiAbelian.pullback p' C.t.G C.t.semi) a₁.cart a₂.cart
  exact ⟨f.normalization, p, p', (Over.pullback p).obj Y.t.G, inferInstance, _, _,
    surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range, bijective_app Y.normal u p, n₁.cart,
    ((isGrpPullback_of_iso e).comp n₂.cart).congr (Category.id_comp _) rfl⟩

theorem isGenerated_of_isGenerated (hω : IsDedFrac ω) (Y C : Model Xo c ω) {g N : ℕ}
    (hY : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) g) (hC : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega C.t.G) g)
    (h : IsGenerated (lbPow (hodge C.t.G g) N)) : IsGenerated (lbPow (hodge Y.t.G g) N) := by
  obtain ⟨Z, p, p', G, _, φ, ψ, _, hp, h₁, h₂⟩ := exists_common_modification hω Y C
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have := Y.t.semi.separated
  have := C.t.semi.separated
  have l₁ : (hodge Y.t.G g).IsLB := hY.isLB_det
  have l₂ : (hodge C.t.G g).IsLB := hC.isLB_det
  have l₃ : (hodge G g).IsLB := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h₁ hY).isLB_det
  have e₁ := (cls_eq_iff (pull_isLB l₁ p) l₃).2 (lbIso_hodge_pull h₁ hY)
  have e₂ := (cls_eq_iff (pull_isLB l₂ p') l₃).2 (lbIso_hodge_pull h₂ hC)
  rw [cls_pull l₁] at e₁
  rw [cls_pull l₂] at e₂
  refine isGenerated_of_pull p hp ((h.pull p').of_lbIso (pull_isLB (isLB_lbPow l₁ N) p)
    ((cls_eq_iff (pull_isLB (isLB_lbPow l₁ N) p) (pull_isLB (isLB_lbPow l₂ N) p')).1 ?_))
  rw [cls_pull (isLB_lbPow l₁ N), cls_pull (isLB_lbPow l₂ N), cls_lbPow l₁, cls_lbPow l₂, map_nsmul, map_nsmul, e₁, e₂]

theorem main : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (R : Type) [CommRing R] (ω : R →+* c.F) (Y C : Model Xo c ω) (g N : ℕ), IsDedFrac ω → GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) g → GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega C.t.G) g → IsGenerated (lbPow (hodge C.t.G g) N) → IsGenerated (lbPow (hodge Y.t.G g) N) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ Y C _ _ hω hY hC h => isGenerated_of_isGenerated hω Y C hY hC h

end GlobalTheory.HodgeGenDesc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicWeightedSquareIntegrableVanishesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_weighted_square_integrable_vanishes : ∀ {n : ℕ}, 0 < n → ∀ (u : V n → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ u (Metric.ball 0 ρ) → ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) < ⊤ → u 0 = 0 := by
  first | exact @GlobalTheory.holo_vanish_of_critical_integrable | exact GlobalTheory.holo_vanish_of_critical_integrable | (intros; apply GlobalTheory.holo_vanish_of_critical_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevelsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_spec_points_levels : ∀ (D : Data) (Λ : Lift D), (∀ (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B), spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔ ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a) ∧ (∀ (U : AffOp D.X) (T : Thick D.κ D.t), ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ g : Sec D.s U.unop.1 →+* T.B₀, spMap g ≫ affPt D.s U.unop = T.x ≫ D.i ∧ ∀ r, g (algebraMap D.R _ r) = T.π (algebraMap D.R T.B r)) ∧ (∀ (U : AffOp D.X) (C : Type) [CommRing C] (g g' : Sec D.s U.unop.1 →+* C), spMap g ≫ affPt D.s U.unop = spMap g' ≫ affPt D.s U.unop → g = g') ∧ ∃ N₀, ∀ N, N₀ ≤ N → ∀ U, IsLev (Λ.L.obj U).δ N := by
  first | exact @GlobalTheory.PDForm.Lift.hom_spec | exact GlobalTheory.PDForm.Lift.hom_spec | (intros; apply GlobalTheory.PDForm.Lift.hom_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraicStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homomorphism_descends_to_algebraic : ∀ (A₀ B₀ : Over (Sp Qb)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B]
    (p : A.left ⟶ A₀.left) (q : B.left ⟶ B₀.left) (g g' : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
    IsAbelianScheme B₀ → SmoothOfRelativeDimension g' B₀.hom →
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p → IsGrpPullback B B₀ (spMap (algebraMap Qb ℂ)) q →
    ∀ α : A ⟶ B, IsMonHom α → ∃ α₀ : A₀ ⟶ B₀, IsMonHom α₀ ∧ α.left ≫ q = p ≫ α₀.left := by
  first | exact @GlobalTheory.HomDescentQb.hom_descends | exact GlobalTheory.HomDescentQb.hom_descends | (intros; apply GlobalTheory.HomDescentQb.hom_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostFieldDegreeDivisibility
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfCover

theorem half_gen_on_cover : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => letI := p.T.Q.H.starRing; ∃ α : 𝓞 (Fm.D x ι).host.E, α * star α = ((((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℕ) : 𝓞 (Fm.D x ι).host.E) ∧ ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) ∣ Y.d.l₂.M ∧ Y.d.l₂.Mb ≤ Ideal.span {star α} ∧ Module.finrank ℚ (Fm.D x ι).host.E * (dat p i).q ≤ 2 * (Fm.D x ι).R.f * (Fm.D x ι).R.m := by
  intro _ h2 _ _
  unfold Covers Lifts
  refine Formalism.MainNotions.Closed.imp h2 ?_
  intro eps Fm CH _ _
  refine ⟨0, le_rfl, 0, fun x hx _ ι p _ i hi Y hY => ?_⟩
  letI := p.T.Q.H.starRing
  have hL := p.fw.laws
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split (Fm.D x ι) p.T.toCore hL.toLawsM (Fm.ex x hx ι).errX
  have hM : p.T.Q.l.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := hL.pins.2.1.1
  have hlev := hY.1.lev.1
  have hq := (hL.pins.2.2.2 ((i : ℕ) + 1) ⟨by omega, by omega⟩).2.1
  refine ⟨α, by rw [hα1, hM], ?_, ?_, ?_⟩
  · rw [hlev.2.1, ← hM]
    exact dvd_mul_right _ _
  · rw [hlev.2.2.2.1, ← hα2]
    exact Ideal.mul_le_left
  · show Module.finrank ℚ (Fm.D x ι).host.E * (p.T.Q.Dw ((i : ℕ) + 1)).q ≤ _
    rw [GlobalTheory.DepthLink.finrank_host, hq]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

end GlobalTheory.HalfCover

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfIzumiSmallValueIdealMapLeSpan
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
open GlobalTheory.Izumi

noncomputable section
namespace GlobalTheory.Izumi

theorem algebraMap_completion_injective : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A], Function.Injective (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
  intro A _ _ _
  have h : IsHausdorff (maximalIdeal A) A := inferInstance
  intro a b hab
  exact AdicCompletion.of_injective (maximalIdeal A) A (by simpa [AdicCompletion.algebraMap_apply] using hab)

theorem exists_sub_algebraMap_mem_maximalIdeal_completion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (b : AdicCompletion (maximalIdeal A) A), ∃ a : A, b - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
  intro A _ _ _ b
  set ψ := AdicCompletion.evalₐ (maximalIdeal A) (R := A) 1
  have hψ : ∀ r : A, ψ (algebraMap A (AdicCompletion (maximalIdeal A) A) r) = Ideal.Quotient.mk _ r := fun r => ψ.commutes r
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ b)
  refine ⟨a, ?_⟩
  by_contra hn
  have hu : IsUnit (b - algebraMap A (AdicCompletion (maximalIdeal A) A) a) := by
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hn
  have h0 : ψ (b - algebraMap A (AdicCompletion (maximalIdeal A) A) a) = 0 := by
    rw [map_sub, hψ, ha, sub_self]
  have h1 := hu.map ψ
  rw [h0] at h1
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ 1) := by
    rw [pow_one]
    exact Ideal.Quotient.nontrivial_iff.2 (maximalIdeal.isMaximal A).ne_top
  exact not_isUnit_zero h1

theorem norm_le_of_mem_iInf_map_smallIdeal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (U : M.Z.Opens) (x : M.Z) (f : Ω) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ∀ ψ : AdicCompletion (maximalIdeal (M.O x)) (M.O x) →+* PadicAlgCl p, (∀ g, ‖ψ g‖ ≤ 1) → (∀ a : M.O x, ψ (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x)) a) = M.val (gPt p ≫ y) a) → ∀ G ∈ ⨅ N, (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))), ‖ψ G‖ ≤ ‖M.val (gPt p ≫ y) f‖ := by
  intro o Ω _ _ _ _ M U x f p _ y hy ψ hψ1 hψv G hG
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI : IsNoetherianRing (M.O x) := RatModel.isNoetherianRing_O M x
  have hadd : ∀ a b : M.O x, ‖M.val (gPt p ≫ y) ((a + b : M.O x) : Ω)‖ ≤
      max ‖M.val (gPt p ≫ y) (a : Ω)‖ ‖M.val (gPt p ≫ y) (b : Ω)‖ := norm_val_add_le M hy
  have hmul : ∀ c a : M.O x, ‖M.val (gPt p ≫ y) ((c * a : M.O x) : Ω)‖ ≤ ‖M.val (gPt p ≫ y) (a : Ω)‖ :=
    norm_val_mul_le M hy
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (maximalIdeal (M.O x)) : (maximalIdeal (M.O x)).FG)
  set ρ : ℝ := ((S.sup fun g => ‖M.val (gPt p ≫ y) (g : Ω)‖₊ : NNReal) : ℝ) with hρdef
  have hρ0 : 0 ≤ ρ := NNReal.coe_nonneg _
  have hρ1 : ρ < 1 := by
    rw [hρdef, ← NNReal.coe_one, NNReal.coe_lt_coe, Finset.sup_lt_iff (by simp)]
    intro g hg
    have hgm : g ∈ maximalIdeal (M.O x) := hS ▸ Submodule.subset_span hg
    have h1 := (hy.norm_val_lt_one_iff g.2).2 (by simpa using hgm)
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    simpa using h1
  have hρ : ∀ h ∈ maximalIdeal (M.O x), ‖M.val (gPt p ≫ y) (h : Ω)‖ ≤ ρ := by
    intro h hh
    rw [← hS] at hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
      rw [hρdef, ← coe_nnnorm, NNReal.coe_le_coe]
      exact Finset.le_sup (f := fun g : M.O x => ‖M.val (gPt p ≫ y) (g : Ω)‖₊) hg
    | zero =>
      have h0 : ((0 : M.O x) : Ω) = 0 := rfl
      rw [h0, RatModel.val_zero, norm_zero]
      exact hρ0
    | add a b _ _ ha hb => exact (hadd a b).trans (max_le ha hb)
    | smul c a _ ha => exact (hmul c a).trans ha
  have hnu : ∀ h, NonUnitAt M x h → ∀ hO : h ∈ M.O x, (⟨h, hO⟩ : M.O x) ∈ maximalIdeal (M.O x) := by
    intro h hh hO
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rcases hh.2 with h0 | hinv
    · subst h0
      have : (⟨0, hO⟩ : M.O x) = 0 := rfl
      rw [this] at hu
      exact not_isUnit_zero hu
    · obtain ⟨w, hw⟩ := hu.exists_right_inv
      have e : h * (w : Ω) = 1 := congrArg Subtype.val hw
      apply hinv
      rw [← eq_inv_of_mul_eq_one_right e]
      exact w.2
  have hN : ∀ N, ∀ g ∈ (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))),
      ‖ψ g‖ ≤ max ‖M.val (gPt p ≫ y) f‖ (ρ ^ N) := by
    intro N g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      rw [hψv]
      rcases (mem_smallIdeal.1 hk) p y hy with h | ⟨h, hh, hle⟩
      · exact h.trans (le_max_left _ _)
      · refine le_max_of_le_right (hle.trans ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (hρ _ (hnu h hh hh.1)) N
    | zero => rw [map_zero, norm_zero]; exact le_max_of_le_right (pow_nonneg hρ0 N)
    | add a b _ _ ha hb => rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | smul c a _ ha =>
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hψ1 c)).trans ha
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < ‖ψ G‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  obtain ⟨N, hNlt⟩ := exists_pow_lt_of_lt_one hpos hρ1
  have h1 := hN N G (Submodule.mem_iInf _ |>.1 hG N)
  rcases le_max_iff.1 h1 with h2 | h2
  · exact absurd h2 (not_le.2 hlt)
  · exact absurd h2 (not_le.2 hNlt)

set_option maxHeartbeats 800000 in

theorem iInf_map_smallIdeal_le_span : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ (f : Ω) (hf : f ∈ M.O x), f ≠ 0 → ⨅ N, (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))) ≤ Ideal.span {algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x)) ⟨f, hf⟩} := by
  intro o Ω _ _ _ _ M hN U hU x hx f hf hf0
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := ArithBase.char (o := o) (Ω := Ω)
  haveI : IsNoetherianRing (M.O x) := RatModel.isNoetherianRing_O M x
  haveI : IsIntegrallyClosed (M.O x) := RatModel.isIntegrallyClosed_O hN x
  haveI : CharZero (M.O x) := ⟨fun a b h => by
    have := congrArg Subtype.val h
    simpa using this⟩
  haveI : Algebra.EssFiniteType ℤ (M.O x) := GlobalTheory.T.modelLocalRing_essFiniteType_int o Ω M x
  haveI : Finite (ResidueField (M.O x)) := GlobalTheory.T.modelLocalRing_residueField_finite_of_closedPoint o Ω M x hx
  set A := M.O x with hA
  set R := AdicCompletion (maximalIdeal A) A with hR
  set φ := algebraMap A R with hφ
  obtain ⟨hdom, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed A
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  have hinj : Function.Injective φ := algebraMap_completion_injective A
  intro G hG
  by_contra hGf
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.exists_nonzero_classicalPoint_of_localHom_avoiding o Ω M U hU x
  obtain ⟨B, _, _, _, _, ι, hιinj, hιloc, hιres, u, hu, hfu⟩ := GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal R (φ ⟨f, hf⟩) G hGf
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hGf (Submodule.zero_mem _)
  haveI : CharZero B := ⟨fun a b h => by
    have h1 : ι (φ (a : A)) = ι (φ (b : A)) := by simpa using h
    have h2 := hinj (hιinj h1)
    exact_mod_cast h2⟩
  haveI : Finite (ResidueField B) := by
    let g : A → ResidueField B := fun a => residue B (ι (φ a))
    have hg : Function.Surjective g := by
      intro c
      obtain ⟨b, rfl⟩ := residue_surjective c
      obtain ⟨r, hr⟩ := hιres b
      obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_maximalIdeal_completion A r
      refine ⟨a, ?_⟩
      have h1 : ι r - ι (φ a) ∈ maximalIdeal B := by
        rw [← map_sub]
        exact map_nonunit ι _ ha
      show residue B (ι (φ a)) = residue B b
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      have := Ideal.add_mem _ h1 hr
      have e : ι (φ a) - b = -((ι r - ι (φ a)) + (b - ι r)) := by ring
      rw [e]
      exact (Ideal.neg_mem_iff _).2 this
    have hker : ∀ a a' : A, a - a' ∈ maximalIdeal A → g a = g a' := by
      intro a a' h
      show residue B _ = residue B _
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub, ← map_sub]
      refine map_nonunit ι _ (map_nonunit φ _ h)
    let g' : ResidueField A → ResidueField B := fun c => g (Classical.choose (residue_surjective c))
    refine Finite.of_surjective g' fun c => ?_
    obtain ⟨a, rfl⟩ := hg c
    refine ⟨residue A a, hker _ _ ?_⟩
    rw [← residue_eq_zero_iff, map_sub, Classical.choose_spec (residue_surjective (residue A a)), sub_self]
  have hh : ι (G * φ s) ≠ 0 := by
    rw [Ne, ← map_zero ι]
    intro h
    exact mul_ne_zero hG0 ((map_ne_zero_iff φ hinj).2 hs0) (hιinj h)
  obtain ⟨p, hp, χ, hχ1, hχm, hχh⟩ := GlobalTheory.T.exists_ringHom_padicAlgCl_ne_zero' B inferInstance (ι (G * φ s)) hh
  set ψ : R →+* PadicAlgCl p := χ.comp ι with hψ
  have hψ1 : ∀ g, ‖ψ g‖ ≤ 1 := fun g => hχ1 _
  have hψG : ψ G ≠ 0 := by
    intro h; apply hχh; rw [map_mul, map_mul]; simp [hψ] at h; simp [h]
  have hψs : ψ (φ s) ≠ 0 := by
    intro h; apply hχh; rw [map_mul, map_mul]; simp [hψ] at h; simp [h]
  have hlt : ‖ψ (φ ⟨f, hf⟩)‖ < ‖ψ G‖ := by
    have e : ψ (φ ⟨f, hf⟩) = ψ G * χ u := by
      simp only [hψ, RingHom.comp_apply, hfu, map_mul]
    rw [e, norm_mul]
    have h1 : ‖χ u‖ < 1 := hχm u hu
    have h2 : 0 < ‖ψ G‖ := norm_pos_iff.2 hψG
    nlinarith [norm_nonneg (χ u)]
  let χ0 : A →+* OO p := (ψ.comp φ).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hψ1 _)
  have hloc : IsLocalHom χ0 := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal A := hna
    have h1 : ι (φ a) ∈ maximalIdeal B := map_nonunit ι _ (map_nonunit φ _ hm)
    have e : ((χ0 a : OO p) : PadicAlgCl p) = χ (ι (φ a)) := rfl
    have h2 : ‖((χ0 a : OO p) : PadicAlgCl p)‖ < 1 := by rw [e]; exact hχm _ h1
    exact (not_isUnit_OO_iff (χ0 a)).2 h2 ha
  have hχ0s : χ0 s ≠ 0 := fun h => hψs (congrArg Subtype.val h)
  obtain ⟨y, hy, hval⟩ := hs p χ0 hloc hχ0s
  have hb := norm_le_of_mem_iInf_map_smallIdeal o Ω M U x f p y hy ψ hψ1 (fun a => (hval a).symm) G hG
  have hf' := hval ⟨f, hf⟩
  simp only at hf'
  rw [hf'] at hb
  exact absurd hb (not_le.2 hlt)

end GlobalTheory.Izumi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenTorsionKernelLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_torsion_kernel_locus : ∀ (Y : Scheme.{0}) (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) (J : Type) [Finite J] (B : J → Over Y) [∀ i, GrpObj (B i)] (f : ∀ i, A ⟶ B i) (B' : Over Y) [GrpObj B'] (f' : A ⟶ B'), IsAbelianScheme A → (∀ i, IsAbelianScheme (B i)) → IsAbelianScheme B' → (∀ i, IsMonHom (f i)) → IsMonHom f' → IsUnit (n : Γ(Y, ⊤)) → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
  first | (exact @GlobalTheory.LevCover.kerlocus_open_closed) | (exact GlobalTheory.LevCover.kerlocus_open_closed) | (intros; apply GlobalTheory.LevCover.kerlocus_open_closed  <;> assumption)
end

