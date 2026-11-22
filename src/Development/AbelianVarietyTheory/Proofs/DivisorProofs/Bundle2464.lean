import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0007
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0012
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorCenterProperLift
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.DivOver

theorem exists_through_of_isProper : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ x : X, E.Through x → ∃ y : Y, s y = x ∧ E'.Through y := by
  intro k _ X Y _ _ p s _ _ hprop E' E hOver x hx
  haveI := hprop
  have hmem : ∀ a : X.presheaf.stalk x,
      functionFieldMap s (algebraMap _ X.functionField a) ∈ E'.ring :=
    fun a => (hOver _).1 (hx _ ⟨a, rfl⟩)
  let ψ : X.presheaf.stalk x →+* E'.ring :=
    ((functionFieldMap s).comp (algebraMap _ X.functionField)).codRestrict E'.ring.toSubring hmem
  have hc : genericFieldPoint Y ≫ s = specAlgebraMap E'.ring Y.functionField ≫
      (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x) := by
    rw [← specMap_functionFieldMap, ← specAlgebraMap_fromSpecStalk x]
    simp only [specAlgebraMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨b, hb1, hb2⟩ := exists_valuativeExtension s _ (genericFieldPoint Y) hc
  have hdom : DominatesStalk E'.ring (b (IsLocalRing.closedPoint E'.ring)) :=
    dominatesStalk_iff_exists_hom.mpr ⟨b, hb1, rfl⟩
  have hw : E'.Through (b (IsLocalRing.closedPoint E'.ring)) := by
    rintro f ⟨c, rfl⟩
    exact hdom.1 c
  have hz : s (b (IsLocalRing.closedPoint E'.ring)) ⤳ x := by
    have e : s (b (IsLocalRing.closedPoint E'.ring)) = X.fromSpecStalk x
        (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint E'.ring)) := by
      have := congrArg (fun l : Spec (CommRingCat.of E'.ring) ⟶ X =>
        l (IsLocalRing.closedPoint E'.ring)) hb2
      exact this
    rw [e]
    have := (IsLocalRing.specializes_closedPoint
      (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint E'.ring))).map
        (X.fromSpecStalk x).continuous
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  obtain ⟨y, hwy, hy⟩ := s.isClosedMap.specializingMap hz
  exact ⟨y, hy, hw.of_specializes hwy⟩

end GlobalTheory.Discrepancy.DivOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSchroedingerModelSiegelRuleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubledWeil_blockEmbedding_acts_on_first_boxFactor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∃ (dd : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA)
                           (GlobalTheory.WeilM.dbl (incM D.host.F JB))) (κ ⊕ κ))
                         (omd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) →*
                           Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ)),
                         GlobalTheory.WeilM.IsDblCoord (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) co dd ∧
                         GlobalTheory.WeilM.IsUWeilSplit (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
                           (incM D.host.F JA) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) dd χT (GlobalTheory.WeilM.diagCols (Fin S.rank)) omd ∧
                         ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
                           (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
                           gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                           ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                             omd gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  first | exact @GlobalTheory.DblSchr.doubledModel | exact GlobalTheory.DblSchr.doubledModel | (intros; apply GlobalTheory.DblSchr.doubledModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownwardChartLocalHolomorphicSection
section
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.Cover

theorem valR_app_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ Y) (g : Y ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ U) (f : Γ(X, U)) : valR x (g ⁻¹ᵁ U) ((g.app U).hom f) = valR (x ≫ g) U f := by
  rw [ZH.CrdCalc.valR_eq x _ h, ZH.CrdCalc.valR_eq (x ≫ g) U h]
  rfl

theorem differentiableOn_chart_of_isDown : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ (σ : 𝓞 F →+* ℂ) (c : AlgChart V.p σ e) (y : CxPts V.p σ), y ∈ c.e.source → ∀ (j : Fin (M.A (ε σ)).n), π σ y ∈ ((M.A (ε σ)).chart j).source → ∃ U : Set (ReciprocityTheory.L2DbarEstimates.V e), IsOpen U ∧ c.e y ∈ U ∧ U ⊆ c.e.target ∧ (∀ v ∈ U, π σ (c.e.symm v) ∈ ((M.A (ε σ)).chart j).source) ∧ DifferentiableOn ℂ (fun v => FinChart.toV e (((M.A (ε σ)).chart j) (π σ (c.e.symm v)))) U := by
  intro F _ _ Y V e M I ε π hD σ c y hy j hj
  obtain ⟨c', hc⟩ := I.alg (ε σ) j
  have hcont : Continuous (π σ) := (isDown_continuous_surjective F Y V e M I ε π hD σ).1
  have hsrc : ∀ z, π σ z ∈ ((M.A (ε σ)).chart j).source ↔ I.pt (ε σ) (π σ z) ∈ c'.e.source := by
    intro z; rw [hc, Homeomorph.transOpenPartialHomeomorph_source]; rfl
  have happ : ∀ z, FinChart.toV e (((M.A (ε σ)).chart j) (π σ z)) = c'.e (I.pt (ε σ) (π σ z)) := by
    intro z; rw [hc, Homeomorph.transOpenPartialHomeomorph_apply]; rfl
  obtain ⟨w₀, hw₀j, hw₀π⟩ := (hD σ).2 y
  have hy' : I.pt (ε σ) (π σ y) ∈ c'.e.source := (hsrc y).1 hj
  have hx : w₀ (IsLocalRing.closedPoint ℂ) ∈ V.π ⁻¹ᵁ c'.U := by
    have := mem_ptsIn.1 (c'.source_subset hy')
    rw [← hw₀π] at this
    exact this
  obtain ⟨W', hW', hxW', n, g', hn, hg'⟩ := T.exists_integral_multiple_extension F V.X V.G V.p (V.π ≫ Y.str) V.j V.pb
    (V.π ⁻¹ᵁ c'.U) _ hx (Fin e) (fun b => (V.π.app c'.U).hom (c'.x b))
  have key : ∀ z : CxPts V.p σ, z ∈ ptsIn V.p σ W' → I.pt (ε σ) (π σ z) ∈ c'.e.source → ∀ b,
      c'.e (I.pt (ε σ) (π σ z)) b = (n : ℂ)⁻¹ * ev V.p σ W' (g' b) z := by
    intro z hz hz' b
    obtain ⟨w, hwj, hwπ⟩ := (hD σ).2 z
    have hz1 : ⊤ ≤ w ⁻¹ᵁ V.j ⁻¹ᵁ W' := by
      have : ⊤ ≤ z.1 ⁻¹ᵁ W' := hz
      rw [← hwj] at this; exact this
    have hz2 : ⊤ ≤ w ⁻¹ᵁ V.π ⁻¹ᵁ c'.U := hz1.trans (w.preimage_mono hW')
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [c'.apply_eq _ hz' b, eq_inv_mul_iff_mul_eq₀ hn']
    show (n : ℂ) * valR (I.pt (ε σ) (π σ z)).1 c'.U (c'.x b) = valR z.1 W' (g' b)
    rw [← hwπ, ← hwj, ← valR_app_comp w V.π c'.U hz2, ← valR_app_comp w V.j W' hz1, ← hg' b,
      ZH.CrdCalc.valR_eq w _ hz1, map_mul, map_natCast, ← ZH.CrdCalc.valR_eq w _ hz1]
    congr 1
    exact (Points.valR_res w hW' hz1 _).symm
  refine ⟨c.e.target ∩ c.e.symm ⁻¹' (ptsIn V.p σ W' ∩ (π σ) ⁻¹' ((M.A (ε σ)).chart j).source),
    c.e.isOpen_inter_preimage_symm ((isOpen_ptsIn W').inter
      (((M.A (ε σ)).chart j).open_source.preimage hcont)),
    ⟨c.e.map_source hy, ?_⟩, Set.inter_subset_left, fun v hv => hv.2.2, ?_⟩
  · rw [Set.mem_preimage, c.e.left_inv hy]
    refine ⟨mem_ptsIn.2 ?_, hj⟩
    rw [← hw₀j]
    exact hxW'
  · rw [differentiableOn_euclidean]
    intro b
    have hd := ((c.holo W' (g' b)).mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono
        (Set.inter_subset_left (t := (π σ) ⁻¹' ((M.A (ε σ)).chart j).source))))).const_mul ((n : ℂ)⁻¹)
    refine hd.congr fun v hv => ?_
    simp only [happ]
    exact key _ hv.2.1 ((hsrc _).1 hv.2.2) b

end GlobalTheory.Mean4O.Cover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointPreimageTopOfReduction
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem evalSectionAtPointOrZero_specMap_comp (Y : Scheme.{0}) (D D' : Type) [CommRing D] [CommRing D'] (φ : D →+* D') (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) (h : ⊤ ≤ x ⁻¹ᵁ U) : evU (spMap φ ≫ x) U a = φ (evU x U a) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ _)
  unfold evU
  rw [dif_pos h', dif_pos h]
  unfold GlobalTheory.Cris.evalAt
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
  have e := congrArg (fun k => k.hom (x.appLE U ⊤ h a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢
  exact e

theorem evalSectionAtPointOrZero_restriction (Y : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y, U)) (hV : ⊤ ≤ x ⁻¹ᵁ V) : evU x V ((Y.presheaf.map (homOfLE h).op).hom a) = evU x U a := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hV.trans (fun p hp ↦ h hp)
  unfold evU
  rw [dif_pos hV, dif_pos hU]
  unfold GlobalTheory.Cris.evalAt
  have e := congrArg (fun k => k.hom a) (Scheme.Hom.map_appLE x hV (homOfLE h).op)
  simp only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢
  rw [e]

theorem dualNumberSndMulInverseFst_mul_units (D : Type) [CommRing D] (u u' : DualNumber D) (hu : IsUnit u) (hu' : IsUnit u') : dl (u * u') = dl u + dl u' := by
  obtain ⟨v, hv⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  obtain ⟨v', hv'⟩ := hu'.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hv hv'
  unfold dl
  rw [TrivSqZeroExt.fst_mul, DualNumber.snd_mul, ← hv, ← hv', ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit]
  rw [mul_inv_rev, Units.val_mul]
  have a1 : (v : D) * ↑v⁻¹ = 1 := Units.mul_inv v
  have a2 : (v' : D) * ↑v'⁻¹ = 1 := Units.mul_inv v'
  linear_combination (u'.snd * ↑v'⁻¹) * a1 + (u.snd * ↑v⁻¹) * a2

theorem dualNumberAlgHomMap_fst_snd_logDerivative (R D D' : Type) [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (u : DualNumber D) : (epsHom φ u).fst = φ u.fst ∧ (epsHom φ u).snd = φ u.snd ∧ (IsUnit u → dl (epsHom φ u) = φ (dl u)) := by
  have h1 : (epsHom φ u).fst = φ u.fst := by
    simp [epsHom, DualNumber.lift_apply_apply]
  have h2 : (epsHom φ u).snd = φ u.snd := by
    simp [epsHom, DualNumber.lift_apply_apply]
  refine ⟨h1, h2, fun hu ↦ ?_⟩
  obtain ⟨v, hv⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hv
  unfold dl
  rw [h1, h2, ← hv, Ring.inverse_unit, map_mul]
  have : φ (v : D) = ((Units.map (φ : D →* D') v : D'ˣ) : D') := rfl
  rw [this, Ring.inverse_unit]
  rfl
theorem evalSectionAtPointOrZero_schemeHom_app (Y Z : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) : evU x (q ⁻¹ᵁ U) ((q.app U).hom a) = evU (x ≫ q) U a := by
  unfold evU
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (x ≫ q) ⁻¹ᵁ U := h
    rw [dif_pos h, dif_pos h']
    unfold GlobalTheory.Cris.evalAt
    simp only [RingHom.comp_apply]
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · have h' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ U := h
    rw [dif_neg h, dif_neg h']

theorem dualNumberPoint_preimage_top_of_reduction (Y : Scheme.{0}) (D : Type) [CommRing D] (y : Sp (DualNumber D) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom D D D).toRingHom ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  intro p _
  let q : Sp D := PrimeSpectrum.comap (TrivSqZeroExt.inlHom D D) p
  have hq : (spMap (TrivSqZeroExt.fstHom D D D).toRingHom) q = p := by
    apply PrimeSpectrum.ext
    ext z
    change z ∈ (PrimeSpectrum.comap ((TrivSqZeroExt.fstHom D D D).toRingHom) q).asIdeal ↔ z ∈ p.asIdeal
    simp only [q, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have heps : (DualNumber.eps : DualNumber D) ∈ p.asIdeal :=
      p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, DualNumber.eps_mul_eps]; exact p.asIdeal.zero_mem)
    have hz : z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inl z.snd * DualNumber.eps := by
      ext <;> simp
    constructor
    · intro hm
      rw [hz]
      exact p.asIdeal.add_mem hm (p.asIdeal.mul_mem_left _ heps)
    · intro hm
      have : TrivSqZeroExt.inl z.fst = z - TrivSqZeroExt.inl z.snd * DualNumber.eps := by
        rw [hz]; ext <;> simp
      change TrivSqZeroExt.inl z.fst ∈ p.asIdeal
      rw [this]
      exact p.asIdeal.sub_mem hm (p.asIdeal.mul_mem_left _ heps)
  have := h (Set.mem_univ q)
  rw [← hq]
  exact this

theorem evU_dl_rules : (∀ (Y : Scheme.{0}) (D D' : Type) [CommRing D] [CommRing D'] (φ : D →+* D') (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)), ⊤ ≤ x ⁻¹ᵁ U → evU (spMap φ ≫ x) U a = φ (evU x U a)) ∧ (∀ (Y : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y, U)), ⊤ ≤ x ⁻¹ᵁ V → evU x V ((Y.presheaf.map (homOfLE h).op).hom a) = evU x U a) ∧ (∀ (Y Z : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)), evU x (q ⁻¹ᵁ U) ((q.app U).hom a) = evU (x ≫ q) U a) ∧ (∀ (D : Type) [CommRing D] (u u' : DualNumber D), IsUnit u → IsUnit u' → dl (u * u') = dl u + dl u') ∧ (∀ (R D D' : Type) [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (u : DualNumber D), (epsHom φ u).fst = φ u.fst ∧ (epsHom φ u).snd = φ u.snd ∧ (IsUnit u → dl (epsHom φ u) = φ (dl u))) ∧ ∀ (Y : Scheme.{0}) (D : Type) [CommRing D] (y : Sp (DualNumber D) ⟶ Y) (U : Y.Opens), ⊤ ≤ (spMap (TrivSqZeroExt.fstHom D D D).toRingHom ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U :=
  ⟨evalSectionAtPointOrZero_specMap_comp, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_schemeHom_app, dualNumberSndMulInverseFst_mul_units, dualNumberAlgHomMap_fst_snd_logDerivative, dualNumberPoint_preimage_top_of_reduction⟩

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberReductionTangentFramedPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumberReduction_tangent_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D r))) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P := by
  first | exact @GlobalTheory.EpsRedFr.epsRed_tangent_frX | exact GlobalTheory.EpsRedFr.epsRed_tangent_frX | (intros; apply GlobalTheory.EpsRedFr.epsRed_tangent_frX <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem dvd_of_forall_height_one_exists_dvd_mul {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {h z : A} (hh : h ≠ 0)
    (H : ∀ P : Ideal A, P.IsPrime → P.height = 1 → ∃ s ∉ P, h ∣ s * z) : h ∣ z := by
  let K := FractionRing A
  have hhK : algebraMap A K h ≠ 0 := fun h0 =>
    hh (IsFractionRing.injective A K (by rw [h0, map_zero]))
  have hmem : algebraMap A K z / algebraMap A K h ∈ (algebraMap A K).range := by
    refine ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := A) _ ?_
    intro P hP h1
    obtain ⟨s, hs, t, ht⟩ := H P hP h1
    refine ⟨s, hs, t, ?_⟩
    rw [← mul_div_assoc, eq_div_iff hhK, ← map_mul, ← map_mul, ht, mul_comm]
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hc, mul_div_assoc', eq_div_iff hhK, mul_comm]

section SquareIdeal

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

theorem dvd_mul_of_dvd_sq_of_dvd_sq {h x y : A} (hx : h ∣ x ^ 2) (hy : h ∣ y ^ 2) : h ∣ x * y := by
  have : h ^ 2 ∣ (x * y) ^ 2 := by
    rw [mul_pow, sq h]; exact mul_dvd_mul hx hy
  exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 this

def sqDvdIdeal (h : A) : Ideal A where
  carrier := {x | h ∣ x ^ 2}
  add_mem' := by
    intro x y hx hy
    have hxy := dvd_mul_of_dvd_sq_of_dvd_sq hx hy
    show h ∣ (x + y) ^ 2
    have e : (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
    rw [e]
    exact dvd_add (dvd_add hx (dvd_mul_of_dvd_right hxy _)) hy
  zero_mem' := by show h ∣ (0 : A) ^ 2; simp
  smul_mem' := by
    intro c x hx
    show h ∣ (c * x) ^ 2
    rw [mul_pow]; exact dvd_mul_of_dvd_right hx _

theorem mem_sqDvdIdeal {h x : A} : x ∈ sqDvdIdeal h ↔ h ∣ x ^ 2 := Iff.rfl

end SquareIdeal

theorem isUnit_mul_sq_of_faithfullyFlat : ∀ (C C' : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] [IsIntegrallyClosed C] [CommRing C'] [IsDomain C'] [IsNoetherianRing C'] [IsIntegrallyClosed C'] [Algebra C C'] [Module.FaithfullyFlat C C'] (h : C), h ≠ 0 → (∃ (u : C'ˣ) (f : C'), algebraMap C C' h = u * f ^ 2) → (∀ p : Ideal C, p.IsPrime → p.height = 1 → ∃ a b c : C, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2) → ∃ (u : Cˣ) (a : C), h = u * a ^ 2 := by
  intro C C' _ _ _ _ _ _ _ _ _ _ _ h hh hsq Hp
  obtain ⟨u, f, hf⟩ := hsq
  have hflat : (algebraMap C C').Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  let J := sqDvdIdeal h

  have hJf : J.map (algebraMap C C') ≤ Ideal.span {f} := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨z, hz⟩ := mem_sqDvdIdeal.1 hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    apply (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1
    refine ⟨(u : C') * algebraMap C C' z, ?_⟩
    rw [← map_pow, hz, map_mul, hf]; ring

  have hcol : (Ideal.span {h}).colon (J : Set C) ≤ J := by
    intro y hy
    rw [Submodule.mem_colon] at hy
    apply mem_sqDvdIdeal.2
    apply dvd_of_forall_height_one_exists_dvd_mul hh
    intro P hP h1
    obtain ⟨a, b, c, hb, hc, habc⟩ := Hp P hP h1
    have hac : a * c ∈ J := mem_sqDvdIdeal.2 ⟨b * c, by linear_combination (-c) * habc⟩
    have hy' := hy (a * c) hac
    rw [smul_eq_mul, Ideal.mem_span_singleton] at hy'
    obtain ⟨t, ht⟩ := hy'
    refine ⟨b * c, fun hm => (hP.mem_or_mem hm).elim hb hc, t ^ 2, ?_⟩
    have e : h * (b * c * y ^ 2) = h * (h * t ^ 2) := by
      linear_combination (c * y ^ 2) * habc + (y * (a * c) + h * t) * ht
    exact mul_left_cancel₀ hh e

  have hfJ : f ∈ J.map (algebraMap C C') := by
    have hm : f ∈ ((Ideal.span {h}).colon (J : Set C)).map (algebraMap C C') := by
      rw [GlobalTheory.ideal_map_colon_eq_of_flat _ hflat, Ideal.map_span, Set.image_singleton,
        Submodule.mem_colon]
      intro p hp
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.1 (hJf hp)
      rw [smul_eq_mul, Ideal.mem_span_singleton, hf]
      exact ⟨((u⁻¹ : C'ˣ) : C') * w, by linear_combination (-(f ^ 2 * w)) * u.mul_inv⟩
    exact Ideal.map_mono hcol hm
  have hJeq : J.map (algebraMap C C') = Ideal.span {f} :=
    le_antisymm hJf ((Ideal.span_singleton_le_iff_mem _).2 hfJ)

  have hY : ((J * J).colon (Ideal.span {h} : Set C)).map (algebraMap C C') = ⊤ := by
    rw [GlobalTheory.ideal_map_colon_eq_of_flat _ hflat, Ideal.map_mul, hJeq, Ideal.map_span,
      Set.image_singleton, Ideal.span_singleton_mul_span_singleton, Ideal.eq_top_iff_one,
      Submodule.mem_colon]
    intro p hp
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.1 hp
    rw [smul_eq_mul, _root_.one_mul, Ideal.mem_span_singleton, hf]
    exact ⟨(u : C') * w, by ring⟩
  have hhJJ : h ∈ J * J := by
    have e := Ideal.comap_map_eq_self_of_faithfullyFlat (B := C')
      ((J * J).colon (Ideal.span {h} : Set C))
    rw [hY, Ideal.comap_top] at e
    have h1 : (1 : C) ∈ (J * J).colon (Ideal.span {h} : Set C) := e ▸ Submodule.mem_top
    rw [Submodule.mem_colon] at h1
    simpa using h1 h (Ideal.mem_span_singleton_self h)

  by_contra hne
  have hle : J * J ≤ Ideal.span {h} * maximalIdeal C := by
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨e, he⟩ := dvd_mul_of_dvd_sq_of_dvd_sq (mem_sqDvdIdeal.1 hx) (mem_sqDvdIdeal.1 hy)
    by_cases hem : e ∈ maximalIdeal C
    · rw [he]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self h) hem
    · exfalso
      have heu : IsUnit e := by
        rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hem; exact hem
      obtain ⟨a, ha⟩ := mem_sqDvdIdeal.1 hx
      obtain ⟨b, hb⟩ := mem_sqDvdIdeal.1 hy
      have hab : a * b = e ^ 2 := by
        have e2 : h ^ 2 * (a * b) = h ^ 2 * e ^ 2 := by
          linear_combination (-(h * b)) * ha - x ^ 2 * hb + (x * y + h * e) * he
        exact mul_left_cancel₀ (pow_ne_zero 2 hh) e2
      have hau : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ heu.pow 2)
      exact hne ⟨hau.unit⁻¹, x, by rw [ha]; linear_combination (-h) * hau.val_inv_mul⟩
  obtain ⟨z, hz, hz'⟩ := Ideal.mem_span_singleton_mul.1 (hle hhJJ)
  have hz1 : z = 1 := mul_left_cancel₀ hh (by rw [hz', _root_.mul_one])
  exact (maximalIdeal.isMaximal C).ne_top ((Ideal.eq_top_iff_one _).2 (hz1 ▸ hz))

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

def e8LB {S : Scheme.{0}} (G₀ : Over S) [GrpObj G₀] (L : LB G₀.left) (W : Matrix (Fin 8) (Fin 8) ℤ) :
    LB (powObj G₀ 8).left :=
  LB.LinComb L (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2))

end GlobalTheory.PowE8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFormallyUnramifiedOfEqAtClosedPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem eq_of_unramified_of_closedPoint : ∀ {S T : Scheme.{0}} (f : T ⟶ S) [FormallyUnramified f]
    [LocallyOfFiniteType f] (R : CommRingCat.{0}) [IsLocalRing R] (u₁ u₂ : Spec R ⟶ T) (h : u₁ ≫ f = u₂ ≫ f)
    (K : Type) [Field K] (k : Sp K ⟶ Spec R) (hk : ∀ x, k x = IsLocalRing.closedPoint R)
    (hku : k ≫ u₁ = k ≫ u₂), u₁ = u₂ := by
  intro S T f _ _ R _ u₁ u₂ h K _ k hk hku
  let g : Spec R ⟶ pullback f f := pullback.lift u₁ u₂ h
  have hkg : k ≫ g = (k ≫ u₁) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp [g, pullback.lift_fst]
    · simp [g, hku, pullback.lift_snd]
  obtain ⟨x⟩ : Nonempty (Sp K) := (inferInstance : Nonempty (PrimeSpectrum K))
  have hc : g (IsLocalRing.closedPoint R) ∈ Set.range (pullback.diagonal f) := by
    refine ⟨(k ≫ u₁) x, ?_⟩
    rw [← hk x, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hkg]
  have hopen : IsOpen (Set.range (pullback.diagonal f)) :=
    (pullback.diagonal f).isOpenEmbedding.isOpen_range
  have hr : Set.range g ⊆ Set.range (pullback.diagonal f) := by
    rintro _ ⟨y, rfl⟩
    have hs : y ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint y
    exact (hs.map g.continuous).mem_open hopen hc
  have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) g hr
  have h1 : u₁ = IsOpenImmersion.lift (pullback.diagonal f) g hr := by
    have e : (IsOpenImmersion.lift (pullback.diagonal f) g hr ≫ pullback.diagonal f) ≫ pullback.fst f f
        = g ≫ pullback.fst f f := by rw [hl]
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at e
    exact e.symm
  have h2 : u₂ = IsOpenImmersion.lift (pullback.diagonal f) g hr := by
    have e : (IsOpenImmersion.lift (pullback.diagonal f) g hr ≫ pullback.diagonal f) ≫ pullback.snd f f
        = g ≫ pullback.snd f f := by rw [hl]
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] at e
    exact e.symm
  exact h1.trans h2.symm

end GlobalTheory.TorsSpec
end

