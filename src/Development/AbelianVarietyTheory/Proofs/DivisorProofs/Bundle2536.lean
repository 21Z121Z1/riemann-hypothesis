import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullMulAddPullMulInv
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareSemiOpen

theorem isAb_pullback_open {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsSemiAbelian A) (U : S.Opens)
    (hU : IsProper (A.hom ∣_ U)) : IsAbelianScheme ((Over.pullback U.ι).obj A) := by
  have hB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback U.ι A hA
  refine ⟨hB.comm, hB.smooth, ?_, hB.geomConnected⟩
  change IsProper (pullback.snd A.hom U.ι)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  infer_instance

end GlobalTheory.SquareSemiOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackCompositionCompatible
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

variable {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

theorem functionFieldMap_comp_dominant (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t] :
    functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) := by
  ext f
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective
    (A := X.presheaf.stalk ((t ≫ s) (genericPoint Z))) f
  have key : ∀ c : X.presheaf.stalk ((t ≫ s) (genericPoint Z)),
      functionFieldMap (t ≫ s) (algebraMap _ X.functionField c) =
        functionFieldMap t (functionFieldMap s (algebraMap _ X.functionField c)) := by
    intro c
    have h1 := functionFieldMap_algebraMap (t ≫ s) (genericPoint Z) c
    have h2 := functionFieldMap_algebraMap s (t (genericPoint Z)) c
    have h3 := functionFieldMap_algebraMap t (genericPoint Z) (s.stalkMap (t (genericPoint Z)) c)
    refine h1.trans (Eq.trans ?_ ((congrArg (functionFieldMap t) h2).trans h3).symm)
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  simp only [map_div₀, RingHom.comp_apply, key]

theorem pullCart_comp (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t] (D : CartierDiv X) :
    pullCart (t ≫ s) D = pullCart t (pullCart s D) :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨g, hg⟩ := D.exists_isEqn ((t ≫ s) z)
    refine ⟨_, isEqn_pullCart (t ≫ s) hg, ?_⟩
    have e : fnPull (t ≫ s) g = fnPull t (fnPull s g) :=
      Units.ext (RingHom.congr_fun (functionFieldMap_comp_dominant s t) g)
    rw [e]
    exact isEqn_pullCart t (isEqn_pullCart s hg)

theorem isDivOfForm_ratPull_comp {k : Type} [Field k] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s]
    (t : Z ⟶ Y) [IsDominant t] (n : ℕ) (η : RatForms p n) (K : CartierDiv Z) :
    IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔
      IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) := by
  have key : ∀ (q q' : Z ⟶ Sp k) (_ : q = q') (φ : X.functionField →+* Z.functionField)
      (h : φ.comp (Cartier.constFn p) = Cartier.constFn q) (h' : φ.comp (Cartier.constFn p) = Cartier.constFn q'),
      IsDivOfForm (p := q) K (TopForm.formMap n φ h η) ↔
        IsDivOfForm (p := q') K (TopForm.formMap n φ h' η) := by
    intro q q' e φ h h'
    subst e
    rfl
  have h' : (functionFieldMap (t ≫ s)).comp (Cartier.constFn p) = Cartier.constFn (t ≫ s ≫ p) := by
    rw [EtaleKlt.functionFieldMap_comp_constFn, Category.assoc]
  have e : EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η) =
      TopForm.formMap n (functionFieldMap (t ≫ s)) h' η :=
    formMap_formMap _ _ _ (functionFieldMap_comp_dominant s t).symm _ _ _ η
  rw [e]
  exact key _ _ (Category.assoc t s p) _ _ h'

theorem pull_comp : ∀ (k : Type) [Field k] (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t], functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) ∧ (∀ D : CartierDiv X, pullCart (t ≫ s) D = pullCart t (pullCart s D)) ∧ ∀ (n : ℕ) (η : RatForms p n) (K : CartierDiv Z), IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔ IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) :=
  fun _ _ _ _ _ _ _ _ p s _ t _ =>
    ⟨functionFieldMap_comp_dominant s t, pullCart_comp s t, isDivOfForm_ratPull_comp p s t⟩

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackNonzeroSectionInjectiveDomainMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PullNonzero

theorem eq_zero_of_dominant {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L ψ ε)) (h : Y' ⟶ Y) [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (h0 : ∀ y J, Good L y J → sval s h y J = 0) (j : K → L.ι) : s.f j = 0 := by
  refine h.app_injective (LB.wchart L ψ j) (Eq.trans ?_ (map_zero (h.app (LB.wchart L ψ j)).hom).symm)
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
  have e₁ := gs_pull (𝟙 Y') h y (LB.wchart L ψ j) hy (s.f j)
  rw [Category.id_comp] at e₁
  have e₂ := sec_trans s h y (j := j) hy (Good.mem hI ψ h)
  have e₃ : gs h y _ _ = 0 := h0 y I hI
  rw [e₃, MulZeroClass.mul_zero] at e₂
  refine (e₁.trans e₂).trans ?_
  rw [gs_eq _ y _ hy, map_zero, map_zero]

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L ψ ε)) (h0 : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L ψ (fun k => J (r ≫ ψ k)))) (h0 _)).trans ((gs_eq r z _ (hJ.mem ψ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegPre V) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ (σ : U.SecGT (𝟙_ _) 1) (σ' : U'.SecGT (𝟙_ _) 1), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ 1 * sval σ' r' z J') → (∃ j, σ.f j ≠ 0) → ∃ j, σ'.f j ≠ 0 := by
  intro R _ _ _ _ D A G _ _ U V _ _ _ φ D' A' G' _ _ U' F C _ hφ σ σ' H ⟨j, hj⟩
  by_contra h0
  push Not at h0
  have hs := U.semi.smooth
  have : Flat G.hom := inferInstance
  have : IsDominant (spMap φ) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2
      (by rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap φ)
  have : IsSchemeTheoreticallyDominant F := IsSchemeTheoreticallyDominant.of_isPullback C.pb.1.flip
  have : QuasiCompact F := MorphismProperty.of_isPullback (P := @QuasiCompact) C.pb.1.flip inferInstance
  have e : ∀ {S : Scheme.{0}} (B : Over S), (λ_ B).inv.left ≫ (snd _ B).left = 𝟙 _ := fun B =>
    congrArg (fun q => q.left) (leftUnitor_inv_snd B)
  have : IsIso (λ_ G).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (λ_ G).inv))
  refine hj (eq_zero_of_dominant U.P.L.isLB σ (F ≫ (λ_ G).inv.left) (fun y J hJ => ?_) j)
  choose J' hJ' using fun χ : G'.left ⟶ G'.left => exists_chart U'.P.L.isLB (χ y)
  have e₁ := H _ (λ_ G').inv.left (F ≫ (λ_ G).inv.left)
    (by rw [Category.assoc, e, ← Category.assoc, e, Category.id_comp, Category.comp_id]) y J J' hJ hJ'
  rw [sval_zero σ' h0 _ y hJ', MulZeroClass.mul_zero] at e₁
  exact e₁

end GlobalTheory.PullNonzero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false
noncomputable section
open GlobalTheory.CxPts
open scoped ContDiff

namespace GlobalTheory.Mean4O.OnModelCInf

theorem cInfAt_of_manIs {F : Type} [Field F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)
    {u : M.Fun} (hu : M.Smooth u) (a : Fin (M.n + 1)) (y : Pts Y (I.ε a)) :
    CInfAt (fun w => u a ((I.pt a).symm w)) y := by
  obtain ⟨j, hj⟩ := (M.A a).cover ((I.pt a).symm y)
  obtain ⟨c, hc⟩ := I.alg a j
  have h := hu a j
  rw [hc, Homeomorph.transOpenPartialHomeomorph_symm_apply, Homeomorph.transOpenPartialHomeomorph_target] at h
  rw [hc, Homeomorph.transOpenPartialHomeomorph_source] at hj
  have h' : ContDiffOn ℝ ∞ ((fun w => u a ((I.pt a).symm w)) ∘ c.finChart.symm)
      (c.finChart.target ∩ c.finChart.symm ⁻¹' Set.univ) := by
    simpa [Function.comp_def] using h
  refine cInfAt_of_chart isOpen_univ c ((c.contDiffOn_finChart_iff _ _ _).1 h') ?_ trivial
  simpa using hj

theorem baseChange_cInfAt : ∀ (F : Type) [Field F] [NumberField F] (X G : Scheme.{0}) (p : X ⟶ Sp (𝓞 F))
    (q : G ⟶ Sp F) (j : G ⟶ X), IsPullback j q p (spMap (algebraMap (𝓞 F) F)) →
    ∀ (τ : F →+* ℂ) (σ : 𝓞 F →+* ℂ) (m : CxPts q τ → CxPts p σ), (∀ z, (m z).1 = z.1 ≫ j) →
    ∀ (f : CxPts p σ → ℝ) (z : CxPts q τ), CInfAt (fun w => f (m w)) z → CInfAt f (m z) := by
  intro F _ _ X G p q j H τ σ m hm f z hz
  obtain ⟨W, ι, _, g, Φ, O, h₁, h₂, h₃, h₄, h₅⟩ := hz
  obtain ⟨W', hle, hx, n, g', hn, hg⟩ := GlobalTheory.T.exists_integral_multiple_extension F X G p q j H W _ (mem_ptsIn.1 h₁) ι g
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hval (w : CxPts q τ) (hw : w ∈ ptsIn q τ (j ⁻¹ᵁ W')) (a : ι) :
      ev p σ W' (g' a) (m w) = n * ev q τ W (g a) w := by
    rw [ev_of_comp hm, ← hg a, ev_mul, ev_res hle hw]
    congr 1
    rw [ev_eq hw, map_natCast]
  have hστ : spMap σ = spMap τ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← (m z).2, hm, Category.assoc, H.w, ← Category.assoc, z.2]
  let s : CxPts p σ → CxPts q τ := fun y => ⟨H.lift y.1 (spMap τ) (y.2.trans hστ), H.lift_snd _ _ _⟩
  have hms (y : CxPts p σ) : m (s y) = y := Subtype.ext ((hm _).trans (H.lift_fst _ _ _))
  have hsm : s (m z) = z := Subtype.ext (H.hom_ext ((H.lift_fst _ _ _).trans (hm z))
    ((H.lift_snd _ _ _).trans z.2.symm))
  have hs : Continuous s := by
    refine Continuous.subtype_mk ?_ _
    rw [(Points.isEmbedding_of_isPullback H).continuous_iff]
    refine (continuous_subtype_val.prodMk (continuous_const (y := spMap τ))).congr fun y => ?_
    exact (Prod.ext (H.lift_fst _ _ _) (H.lift_snd _ _ _)).symm
  have hz' : z ∈ ptsIn q τ (j ⁻¹ᵁ W') := mem_ptsIn.2 hx
  have hmW : m z ∈ ptsIn p σ W' := by
    rw [mem_ptsIn, hm]
    exact hx
  have hd : ContDiff ℝ ∞ fun v : ι → ℂ => fun a => v a / (n : ℂ) :=
    contDiff_pi.2 fun a => (contDiff_apply ℝ ℂ a).div_const _
  refine ⟨W', ι, inferInstance, g', fun v => Φ fun a => v a / n, (fun v : ι → ℂ => fun a => v a / (n : ℂ)) ⁻¹' O,
    hmW, h₂.preimage hd.continuous, ?_, h₄.comp hd.contDiffOn fun v hv => hv, ?_⟩
  · show (fun a => ev p σ W' (g' a) (m z) / n) ∈ O
    simpa only [hval z hz', mul_div_cancel_left₀ _ hn'] using h₃
  · have ht : Filter.Tendsto s (nhds (m z)) (nhds z) := by
      have := hs.continuousAt (x := m z)
      rwa [ContinuousAt, hsm] at this
    filter_upwards [ht.eventually h₅, ht.eventually ((isOpen_ptsIn _).mem_nhds hz')] with y e hy
    have hv (a : ι) : ev p σ W' (g' a) y = n * ev q τ W (g a) (s y) := by
      have := hval (s y) hy a
      rwa [hms] at this
    calc f y = f (m (s y)) := by rw [hms]
      _ = Φ (fun a => ev q τ W (g a) (s y)) := e
      _ = Φ (fun a => ev p σ W' (g' a) y / n) := by
        congr 1
        funext a
        rw [hv, mul_div_cancel_left₀ _ hn']

theorem cInfAt_pull : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ u : M.Fun, M.Smooth u → ∀ σ (z : CxPts V.p σ), CxPts.CInfAt (M.pull ε π u σ) z := by
  intro F _ _ Y V e M I ε π hD u hu σ z
  obtain ⟨hσ, hw⟩ := hD σ
  have hm0 (w : CxPts (V.π ≫ Y.str) (I.ε (ε σ))) : (w.1 ≫ V.j) ≫ V.p = spMap σ := by
    rw [Category.assoc, V.pb.w, ← Category.assoc, w.2, show spMap σ = _ from congrArg spMap hσ.symm, spMap, spMap, spMap,
      ← Spec.map_comp]
    rfl
  let m : CxPts (V.π ≫ Y.str) (I.ε (ε σ)) → CxPts V.p σ := fun w => ⟨w.1 ≫ V.j, hm0 w⟩
  obtain ⟨w, hw1, hw2⟩ := hw z
  let z' : CxPts (V.π ≫ Y.str) (I.ε (ε σ)) := ⟨w, by rw [← Category.assoc, hw2]; exact (I.pt _ (π σ z)).2⟩
  have hz : m z' = z := Subtype.ext hw1
  have key (w' : CxPts (V.π ≫ Y.str) (I.ε (ε σ))) : M.pull ε π u σ (m w') =
      u (ε σ) ((I.pt (ε σ)).symm (Points.PtsOver.map V.π rfl _ w')) := by
    obtain ⟨w'', h1, h2⟩ := hw (m w')
    have e : w'' = w'.1 := V.pb.hom_ext h1 (by
      rw [← Category.assoc, h2, (I.pt _ (π σ (m w'))).2]
      exact w'.2.symm)
    show u (ε σ) (π σ (m w')) = _
    congr 1
    apply (I.pt (ε σ)).injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (h2.symm.trans (by rw [e]; rfl))
  have hY := CInfAt.pull V.π rfl (cInfAt_of_manIs I hu (ε σ) (Points.PtsOver.map V.π rfl _ z'))
  rw [← hz]
  exact baseChange_cInfAt F V.X V.G V.p (V.π ≫ Y.str) V.j V.pb _ σ m (fun _ => rfl) _ z'
    (hY.congr (.of_forall key))

end GlobalTheory.Mean4O.OnModelCInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareActionBundleIsoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_action_bundle_iso : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (rm' : OAct (𝓞 F) A'),
    (∀ a, (rm'.act a).left ≫ φ = φ ≫ (X.rm.act a).left) → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ (c c' : 𝔠.elt) (a : 𝓞 F),
      LBIso ((X.P c).pull φ₂) (((X.P c).pull φ₂).pull (lift (snd A' A') (fst A' A')).left) ∧
      LBIso ((X.P c').pull φ₂) (LB.div ((X.P (c + c')).pull φ₂) ((X.P c).pull φ₂)) ∧
      LBIso ((X.P (a • c)).pull φ₂) (((X.P c).pull φ₂).pull (lift (fst A' A') (snd A' A' ≫ rm'.act a)).left) := by
  first | exact @GlobalTheory.RealMult.PullPol.pol_pull | exact GlobalTheory.RealMult.PullPol.pol_pull | (intros; apply GlobalTheory.RealMult.PullPol.pol_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareDiagonalSectionsGeneratedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_square_diagonal_sections_generated : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ c : 𝔠.elt, HasGen (((X.P c).pull φ₂).pull (lift (1 : A' ⟶ A') (𝟙 A')).left) ∧
      HasGen (((X.P c).pull φ₂).pull (lift (𝟙 A') (1 : A' ⟶ A')).left) := by
  first | exact @GlobalTheory.hasGen_pull_rig_of_isGrpPullback | exact GlobalTheory.hasGen_pull_rig_of_isGrpPullback | (intros; apply GlobalTheory.hasGen_pull_rig_of_isGrpPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutQuotientSurjectiveKerEqMapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushout_quotient_surjective_ker_eq_map : ∀ (R C E : Type) [CommRing R] [CommRing C] [CommRing E] (c : Ideal R) (f : R →+* C) (π : C →+* E) (χ : R ⧸ c →+* E), IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom χ) → Function.Surjective π ∧ RingHom.ker π = c.map f := by
  first | exact @GlobalTheory.pushout_quotient_map_eq_quotient_map_ideal | exact GlobalTheory.pushout_quotient_map_eq_quotient_map_ideal | (intros; apply GlobalTheory.pushout_quotient_map_eq_quotient_map_ideal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenyPairBaseChangeGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem pullQuasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsAbelianScheme B → IsQuasiInv k ψ ψ' → IsGrpPullback A₁ A t φ → ∃ (B₁ : Over T) (_ : GrpObj B₁) (_ : IsCommMonObj B₁) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ ∧ IsGrpPullback B₁ B t θ ∧ IsQuasiInv k ψ₁ ψ₁' ∧ φ ≫ ψ.left = ψ₁.left ≫ θ ∧ θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  intro T Y t A B _ _ _ _ k ψ ψ' A₁ _ _ φ hB hq hA
  obtain ⟨hψ, hψ', h1, h2⟩ := hq
  obtain ⟨e, he, hφ⟩ := grpPullback_iso hA (isGrpPullback_pullback A t)
  have hinv : IsMonHom e.inv := inferInstance
  have hinvφ : e.inv.left ≫ φ = pullback.fst A.hom t := by
    rw [← hφ, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hmap : ∀ (X M : Over Y) [MonObj M] (f : X ⟶ M) (n : ℕ),
      (Over.pullback t).map (f ^ n) = ((Over.pullback t).map f) ^ n := fun X M _ f n => by
    rw [← Functor.homMonoidHom_apply, map_pow, Functor.homMonoidHom_apply]
  have hid : ∀ (M : Over Y) [GrpObj M], (Over.pullback t).map ((𝟙 M) ^ k) = (𝟙 _) ^ k := fun M _ => by
    rw [hmap, CategoryTheory.Functor.map_id]
  refine ⟨(Over.pullback t).obj B, inferInstance, inferInstance, pullback.fst B.hom t,
    e.hom ≫ (Over.pullback t).map ψ, (Over.pullback t).map ψ' ≫ e.inv,
    ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t B hB, isGrpPullback_pullback B t, ⟨inferInstance, inferInstance, ?_, ?_⟩, ?_, ?_⟩
  · calc (e.hom ≫ (Over.pullback t).map ψ) ≫ (Over.pullback t).map ψ' ≫ e.inv
          = e.hom ≫ (Over.pullback t).map (ψ ≫ ψ') ≫ e.inv := by simp
      _ = e.hom ≫ ((𝟙 ((Over.pullback t).obj A)) ^ k) ≫ e.inv := by rw [h1, hid]
      _ = (𝟙 A₁) ^ k := by
        rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, e.hom_inv_id]
  · calc ((Over.pullback t).map ψ' ≫ e.inv) ≫ e.hom ≫ (Over.pullback t).map ψ
          = (Over.pullback t).map (ψ' ≫ ψ) := by simp
      _ = (𝟙 _) ^ k := by rw [h2, hid]
  · rw [Over.comp_left, Category.assoc]
    show φ ≫ ψ.left = e.hom.left ≫ pullback.lift _ _ _ ≫ pullback.fst B.hom t
    rw [pullback.lift_fst, ← Category.assoc, hφ]
  · rw [Over.comp_left, Category.assoc, hinvφ]
    show pullback.fst B.hom t ≫ ψ'.left = pullback.lift _ _ _ ≫ pullback.fst A.hom t
    rw [pullback.lift_fst]

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointCharacterValuePowIsUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnramCharPow

open GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

attribute [local instance] gtGroup

theorem charVal_pow_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → (∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (val (D.psi χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) (closedPoint F) J) : F) = ((u : T) : F)) → ∀ (k : ℕ) (p : QkPt D F k) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = p.g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ χ, ∃ u : Tˣ, (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal p.g χ (closedPoint F) J) : F) ^ k = ((u : T) : F) := by
  intro R _ _ D hB F _ _ T _ φ₁ hφ J₀ h₀ J hJ eJ hψ k p b hb hbA χ
  let H : Subgroup Fˣ := (Units.map T.subtype.toMonoidHom).range
  let w : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ →* Fˣ ⧸ H :=
    (QuotientGroup.mk' H).comp (sig F)
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ₁) := Over.homMk (spMap T.subtype) (by
    show spMap T.subtype ≫ spMap φ₁ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  let b' : Over.mk (spMap φ₁) ⟶ D.P.A := Over.homMk b hbA
  have hb' : ρ ≫ b' = p.g.b := Over.OverMorphism.ext hb
  have mem : ∀ s : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ,
      (∃ u : Tˣ, (sig F s : F) = ((u : T) : F)) → w s = 1 := fun s ⟨u, hu⟩ => by
    show (QuotientGroup.mk' H) (sig F s) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨u, Units.ext hu.symm⟩
  have hw : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (Over.mk (spMap φ₁)).left ⟶ Y),
      w (val t (ρ.left ≫ r) (closedPoint F) J) = 1 := by
    intro Y K _ φ ε t r
    exact mem _ (val_integral T.subtype h₀ eJ t r)
  have e₁ := w_nsmul ρ hJ w hw p.g b' hb' χ k
  rw [qk_nsmul hB, iota_val hB _ _ hJ, w_tau ρ hJ w hw, mem _ (hψ _), mem _ (hψ _), mem _ (hψ _)] at e₁
  simp only [inv_one, _root_.mul_one] at e₁
  have e₂ : (QuotientGroup.mk' H) (sig F (charVal p.g χ (closedPoint F) J) ^ k) = 1 := by
    rw [map_pow]; exact e₁.symm
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at e₂
  obtain ⟨u, hu⟩ := e₂
  exact ⟨u, by rw [← Units.val_pow_eq_pow_val, ← hu]; rfl⟩

end GlobalTheory.UnramCharPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFiniteRepresentatives
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem qkPt_finite_reps : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), k ≠ 0 → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → ∃ Rep : Set (QkPt D F k), Rep.Finite ∧ ∀ p : QkPt D F k, ∃ p' ∈ Rep, ∃ (z : D.X) (t : GtPtF D F), t.b = 1 ∧ (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0 ∧ p.g = p'.g + GlobalTheory.TorusExt.iota hB F z + t) := by
  intro R _ _ D hB F _ _ k hk hfin
  letI := GlobalTheory.TorusExt.gtGroup D F
  classical
  by_cases hne : Nonempty (QkPt D F k)
  swap
  · exact ⟨∅, Set.finite_empty, fun p => (hne ⟨p⟩).elim⟩
  let K : AddSubgroup D.X := (nsmulAddMonoidHom (α := D.X) k).range
  haveI : K.FiniteIndex := ⟨by
    simp only [K, AddSubgroup.index_range_nsmul]; exact pow_ne_zero _ hk⟩
  haveI : Finite (D.X ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex
  let Q : QkPt D F k → D.X ⧸ K := fun p => (p.y : D.X ⧸ K)
  let bp : D.X ⧸ K → QkPt D F k := Function.invFun Q
  have hbp : ∀ p, Q (bp (Q p)) = Q p := fun p => Function.invFun_eq ⟨p, rfl⟩
  have hz : ∀ p, ∃ z : D.X, k • z = -(bp (Q p)).y + p.y := by
    intro p
    have h := QuotientAddGroup.eq.mp (hbp p)
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.mp h
    exact ⟨z, by simpa using hz⟩
  let zOf : QkPt D F k → D.X := fun p => (hz p).choose
  have hzOf : ∀ p, k • zOf p = -(bp (Q p)).y + p.y := fun p => (hz p).choose_spec
  let δ : QkPt D F k → GtPtF D F := fun p =>
    p.g - (bp (Q p)).g - GlobalTheory.TorusExt.iota hB F (zOf p)
  have hδk : ∀ p, k • δ p = 0 := by
    intro p
    simp only [δ, smul_sub, GlobalTheory.TorusExt.qk_nsmul hB, ← map_nsmul, hzOf]
    rw [map_add, map_neg]; abel
  have hδb : ∀ p, (δ p).b ^ k = 1 := by
    intro p
    rw [← GlobalTheory.TorusExt.nsmul_b, hδk p, GlobalTheory.TorusExt.zero_b]
  let Φ : QkPt D F k → (D.X ⧸ K) × {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} :=
    fun p => (Q p, ⟨(δ p).b, hδb p⟩)
  let rep : (D.X ⧸ K) × {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → QkPt D F k :=
    Function.invFun Φ
  have hrep : ∀ p, Φ (rep (Φ p)) = Φ p := fun p => Function.invFun_eq ⟨p, rfl⟩
  refine ⟨Set.range (rep ∘ Φ), ?_, ?_⟩
  · rw [Set.range_comp]; exact (Set.toFinite _).image _
  intro p
  set p' := rep (Φ p) with hp'
  have h1 : Q p' = Q p := congrArg Prod.fst (hrep p)
  have h2 : (δ p').b = (δ p).b := congrArg (fun x => x.2.1) (hrep p)
  refine ⟨p', ⟨p, rfl⟩, zOf p - zOf p', δ p - δ p', ?_, ?_, ?_⟩
  · rw [sub_eq_add_neg, GlobalTheory.TorusExt.add_b, GlobalTheory.TorusExt.neg_b, h2, mul_inv_cancel]
  · rw [smul_sub, hδk, hδk, sub_zero]
  · have hb : bp (Q p') = bp (Q p) := by rw [h1]
    simp only [δ, hb, map_sub]
    abel

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFunction_app_of_preservesGenericPoint : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (m : Y ⟶ X) (φ : X.functionField →+* Y.functionField), PFF (𝟙 _) m φ → ∀ (V : X.Opens) (hV : genericPoint X ∈ V) (hV' : genericPoint Y ∈ m ⁻¹ᵁ V) (a : Γ(X, V)), fnOf (m ⁻¹ᵁ V) hV' ((m.app V).hom a) = φ (fnOf V hV a) := by
  first | exact @GlobalTheory.Desc.fnOf_app_of_pff | exact GlobalTheory.Desc.fnOf_app_of_pff | (intros; apply GlobalTheory.Desc.fnOf_app_of_pff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianBasisVectorTraceFreeSkewCondStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianBasisVector_traceFreeSkewCond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, SkewCond d (boxVec d z k) := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec <;> assumption)
end

