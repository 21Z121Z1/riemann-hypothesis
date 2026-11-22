import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOnOfTExpGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.MumMult

theorem chartExpOn_of_tExp_gen {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (e : ℕ) (b : thickObj R I e G ⟶ thickObj R I e G) (n : ℕ)
    (F : ∀ β, SecT D.toPre a n 0 β) (f : ∀ β, D.toPre.SecB n β) (τ : SecE U b n 0) (hF : Small I (w := id) F)
    (hf : ∀ β, ∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (f β) x z J = sval (F β) x z J)
    (hτ : TExp U τ (w := id) F) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens)
    (g : Γ((thickObj R I e G).left, W))
    (hg : ∀ (z : (thickObj R I e G).left) (J'), z ∈ W → Good U.LG.L z J' → J' (𝟙 _ ≫ (fstG I e G).left) = i' 0 →
      gs (𝟙 _) z W g = sval τ (𝟙 _) z J') : ChartExpOn U e n i' W g f := by
  classical
  let S : Finset D.toPre.X := (hF e).toFinset
  have hS : ∀ α ∉ S, Van I (F α) e := fun α hα => by_contra fun h => hα ((hF e).mem_toFinset.2 h)
  refine ⟨S, fun α hα j => fn_ext fun y hy => ?_, ?_⟩
  · choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero (𝟙 _) y _ hy).symm)
    rw [Category.id_comp]
    have h0 : sval (f α) (DVR.pGl U e) y J = 0 := (hf α _ _ y J hJ).trans (hS α hα _ (U.gt e).q.left y J hJ)
    exact (sec_trans (f α) _ y hy (Good.mem hJ _ _)).trans ((congrArg _ h0).trans (mul_zero _))
  · rintro ⟨p₁, p₂⟩ jf jt hj hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ _ hc (by
      rintro (a | a | a)
      exacts [mem_pull.1 hy.1.1.1.1, Set.mem_iInter.1 (U.expW_le_f e _ _ jf jt a.1.2 hy.1) a.2,
        Set.mem_iInter.1 (U.expWeight_le_chart_weight e _ _ jf jt a.1.2 hy.1) a.2])
    obtain ⟨J', hJ', eJ'⟩ := exists_good U.LG.L U.LG.isLB y (K := PUnit.{1}) (fun _ => 𝟙 _ ≫ (fstG I e G).left)
      (fun _ => p₂ PUnit.unit) (fun _ _ _ => rfl) (fun _ => mem_pull.1 hy.1.1.1.2)
    have e₀ : J (𝟙 _ ≫ (U.gt e).pG.left) = p₁ PUnit.unit := by rw [Category.id_comp]; exact eJ (.inl PUnit.unit)
    have e₁ : J' (𝟙 _ ≫ (fstG I e G).left) = p₂ PUnit.unit := eJ' PUnit.unit
    have H := hτ S hS _ (𝟙 _) y J J' hJ hJ'
    rw [evalE, zpow_zero, _root_.mul_one, zpow_natCast, e₀, e₁] at H
    refine ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ?_ ((gs_res (𝟙 _) y inf_le_right hy g).trans
      (hg y J' hy.2 hJ' (e₁.trans hj.symm))))).trans
      (H.trans (Eq.symm ?_))
    · rw [← Units.val_pow_eq_pow_val, gs_unit (𝟙 _) y _ hy, map_pow]
      exact congrArg (fun u => (u ^ n).val) (gm_res (𝟙 _) y _ hy _)
    · refine (DVR.gs_fsum (𝟙 _) y _ hy _ _).trans (Eq.trans (Finset.sum_congr rfl fun α _ => ?_) (Finset.sum_attach S _))
      have l₁ : U.expW e (p₁, p₂) i' S jf jt ⊓ W ≤ _ := inf_le_left.trans (U.expW_le_f e (p₁, p₂) i' jf jt α.2)
      have l₂ : U.expW e (p₁, p₂) i' S jf jt ⊓ W ≤ _ := inf_le_left.trans (U.expWeight_le_chart_weight e (p₁, p₂) i' jf jt α.2)
      have a₁ := (gs_res (𝟙 _) y l₁ hy (((DVR.pGl U e).app _).hom ((f α.1).f (jf α.1)))).trans
        (gs_pull (𝟙 _) (DVR.pGl U e) y (LB.wchart D.toPre.P.L (D.toPre.famφB α.1) (jf α.1)) (l₁ hy) ((f α.1).f (jf α.1)))
      have a₂ := (gs_unit (𝟙 _) y _ hy (res l₂ ((DVR.tG U e α.1).s (jt α.1)))).trans
        (congrArg Units.val (gm_res (𝟙 _) y l₂ hy _))
      have b₁ := sval_of (f α.1) (𝟙 _ ≫ DVR.pGl U e) y J (jf α.1)
        (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inl (α, a))))
      have b₂ := val_of (DVR.tG U e α.1) (𝟙 _) y J (jt α.1)
        (fun a => by rw [Category.id_comp]; exact eJ (.inr (.inr (α, a))))
      exact (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (a₁.trans (b₁.symm.trans (hf α.1 _ _ y J hJ)))
        (a₂.trans (congrArg Units.val b₂.symm)))

theorem chartExpOn_of_tExp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n : ℕ) (F : ∀ β, SecT D.toPre a n 0 β) (f : ∀ β, D.toPre.SecB n β) (τ : SecE U.toUnifPre b n 0), Small (maximalIdeal R) (w := id) F → (∀ β, (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (f β) x z J = sval (F β) x z J)) → TExp U.toUnifPre τ (w := id) F → ∀ (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R (maximalIdeal R) e G).left.Opens) (g : Γ((thickObj R (maximalIdeal R) e G).left, W)), (∀ (z : (thickObj R (maximalIdeal R) e G).left) (J'), z ∈ W → Good U.LG.L z J' → J' (𝟙 _ ≫ (fstG (maximalIdeal R) e G).left) = i' 0 → gs (𝟙 _) z W g = sval τ (𝟙 _) z J') → GlobalTheory.MumMult.ChartExpOn U.toUnifPre e n i' W g f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U e b n F f τ hF hf hτ i' W g hg =>
    chartExpOn_of_tExp_gen U.toUnifPre e b n F f τ hF hf hτ i' W g hg

end GlobalTheory.MumMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassContractionTangentEqTorsorCocycleStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernClass_contraction_tangent_eq_torsorCocycle : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) → (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) → ∀ κ : Fn1 A, IsContr w.1 v κ → ∃ u : Fn1 (A ⊗ B), IsCoc P.U u ∧ Cohom (chartsA P) κ ((tanCoc P j v).add (sndPull u v)) := by
  first | exact @GlobalTheory.PtExt.contr_chern_eq_tanCoc | exact GlobalTheory.PtExt.contr_chern_eq_tanCoc | (intros; apply GlobalTheory.PtExt.contr_chern_eq_tanCoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegrableOnDescendGenericallyFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernDescend

theorem chernIntegrableOn_descend : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (ρ : Y' ⟶ Y), IsArithVar (ρ ≫ q) e → ρ (genericPoint Y') = genericPoint Y → ρ.residueDegree (genericPoint Y') ≠ 0 → ∀ (N : HermLB q) (σ : k →+* ℂ) (U : Y.Opens) (f : CxPts q σ → ℝ), ContinuousOn f (ptsIn q σ U) → ((N.restr ρ).φ σ).ChernIntegrableOn e (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (fun y => f (PtsOver.map ρ rfl _ y)) → (N.φ σ).ChernIntegrableOn e (ptsIn q σ U) f := by
  intro k _ Y _ q e hY Y' _ ρ hY' hη hδ N σ U f hf hint
  obtain ⟨V, hVη, hV⟩ := GlobalTheory.T.exists_open_etaleChart_covering_complexPoints hY hY' ρ rfl hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hV σ
  have hFm : Measurable (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ)) :=
    (PtsOver.continuous_map _ _ _).measurable
  have hpre : ∀ W : Y.Opens, PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' ptsIn q σ W =
      ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ W) := by
    intro W
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hUm : MeasurableSet (ptsIn q σ U) := (isOpen_ptsIn U).measurableSet
  have hVm : MeasurableSet (ptsIn q σ V) := (isOpen_ptsIn V).measurableSet
  have h0 : ∀ ε : ℤˣ, (N.φ σ).chernPart e ε (ptsIn q σ V)ᶜ = 0 := by
    intro ε
    have h := GlobalTheory.T.chernPart_over_properClosed_eq_zero hY ((V : Y.Opens) : Set Y)ᶜ V.isOpen.isClosed_compl (by simp [hVη]) σ
      (N.φ σ) ε
    convert h using 2
    ext y
    simp [mem_ptsIn]
  have hmeas : ∀ ε : ℤˣ, (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) •
      ((N.φ σ).chernPart e ε).restrict (ptsIn q σ U) =
      Measure.map (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ))
        ((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
          (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) := by
    intro ε
    ext A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.map_apply hFm hA,
      Measure.restrict_apply (hFm hA), ← Set.preimage_inter,
      GlobalTheory.T.chernPart_preimage_of_finite_liftedChartCovering hY hY' ρ rfl (N.φ σ) (N.cInf σ) ε (ptsIn q σ V) (isOpen_ptsIn V) _ hcard hchart
        hlift (fun c c' hc w hw => GlobalTheory.T.chernDensity_pullbackWeight_in_liftedChart ρ rfl (N.φ σ) (N.cInf σ) c c' hc w hw) _
        (hA.inter (hUm.inter hVm)) (fun x hx => hx.2.2), smul_eq_mul, ← Set.inter_assoc,
      measure_inter_conull (h0 ε)]
  have hδ1 : (1 : ℝ≥0∞) ≤ (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero hδ)
  have key : ∀ ε : ℤˣ, IntegrableOn (fun y => f (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (((N.φ σ).pull ρ rfl).chernPart e ε) →
      IntegrableOn f (ptsIn q σ U) ((N.φ σ).chernPart e ε) := by
    intro ε h
    refine ⟨hf.aestronglyMeasurable hUm, ?_⟩
    have h1 := h.2
    unfold HasFiniteIntegral at h1 ⊢
    refine lt_of_le_of_lt ?_ h1
    calc ∫⁻ y, ‖f y‖ₑ ∂((N.φ σ).chernPart e ε).restrict (ptsIn q σ U)
        ≤ (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) *
          ∫⁻ y, ‖f y‖ₑ ∂((N.φ σ).chernPart e ε).restrict (ptsIn q σ U) :=
          le_mul_of_one_le_left' hδ1
      _ = ∫⁻ y, ‖f y‖ₑ ∂Measure.map (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ))
          ((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
            (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) := by
          rw [← hmeas ε, lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ z, ‖f (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) z)‖ₑ
          ∂((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
            (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) :=
          lintegral_map_le _ _
      _ ≤ _ := by
          refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
          rw [← hpre U]
          exact Set.preimage_mono Set.inter_subset_left
  exact ⟨key 1 hint.1, key (-1) hint.2⟩

end GlobalTheory.ChernDescend

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMeasurePartPreimageCoveringFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMeasurePart_preimage_covering_field : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ n : ℕ, (∀ y ∈ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ) ⁻¹' U) = (n : ENNReal) * φ.chernPart D ε U := by
  first | exact @GlobalTheory.CoverChernField.chernPart_preimage_of_cover | exact GlobalTheory.CoverChernField.chernPart_preimage_of_cover | (intros; apply GlobalTheory.CoverChernField.chernPart_preimage_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.Points GlobalTheory.HermFrame
open scoped Classical

namespace GlobalTheory.ChernTop

theorem add_pow_of_sq_zero {R : Type} [CommRing R] (S t : R) (ht : t * t = 0) (m : ℕ) :
    (t + S) ^ (m + 1) = S ^ (m + 1) + ((m : R) + 1) * t * S ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((m : R) + 1) * S ^ m * ht

theorem sum_pow_card {R α : Type} [CommRing R] (t : α → R) (ht : ∀ a, t a * t a = 0) (s : Finset α) :
    (∑ a ∈ s, t a) ^ s.card = (s.card.factorial : R) * ∏ a ∈ s, t a ∧ (∑ a ∈ s, t a) ^ (s.card + 1) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      add_pow_of_sq_zero _ _ (ht a), add_pow_of_sq_zero _ _ (ht a), pow_succ _ (s.card + 1), ih.1, ih.2,
      Nat.factorial_succ]
    push_cast
    constructor <;> ring

variable {n : ℕ}

def rowForm (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n := Fintype.linearCombination ℂ fun b => sym (a, b)

theorem coe_rowForm (a : Fin n) (u : Fin n → ℂ) :
    (rowForm a u : Alt n) = dz a * ExteriorAlgebra.ι ℂ (∑ b, u b • Pi.single (Sum.inr b : Fin n ⊕ Fin n) (1 : ℂ)) := by
  simp only [rowForm, Fintype.linearCombination_apply, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym,
    map_sum, map_smul, Finset.mul_sum, mul_smul_comm, dzb]

theorem rowForm_mul_same (a a' : Fin n) (u : Fin n → ℂ) : rowForm a u * rowForm a' u = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, ← Subalgebra.mem_center_iff.1 (rowForm a u).2, coe_rowForm a']
  have h := Subalgebra.mem_center_iff.1 (rowForm a u).2
  rw [mul_assoc, h, coe_rowForm, mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero, mul_zero]
  rfl

def densL (n : ℕ) : Ev n →ₗ[ℂ] ℂ where
  toFun α := dens (α : Alt n)
  map_add' α β := by simp [dens, add_div]
  map_smul' c α := by simp [dens, mul_div_assoc]

def rowDeterminantForm (n : ℕ) : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ where
  toMultilinearMap := (densL n).compMultilinearMap
    ((MultilinearMap.mkPiAlgebra ℂ (Fin n) (Ev n)).compLinearMap rowForm)
  map_eq_zero_of_eq' v i j h hij := by
    change densL n (∏ a, rowForm a (v a)) = 0
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), ← mul_assoc, h,
      rowForm_mul_same, zero_mul, map_zero]

theorem dens_prod_rowForm (A : Matrix (Fin n) (Fin n) ℂ) :
    (Complex.I / 2) ^ n * densL n (∏ a, rowForm a (A a)) = A.det := by
  have h := congrArg (· A) ((rowDeterminantForm n).eq_smul_basis_det (Pi.basisFun ℂ (Fin n)))
  have h₁ : (Complex.I / 2) ^ n * rowDeterminantForm n (Pi.basisFun ℂ (Fin n)) = 1 := by
    rw [← dens_vol n]
    change _ * densL n (∏ a, rowForm a (Pi.basisFun ℂ (Fin n) a)) = densL n (vol n)
    rw [vol, Finset.prod_smul, map_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    simp [rowForm]
  change _ * rowDeterminantForm n A = _
  refine (congrArg _ h).trans ((mul_assoc _ _ _).symm.trans ?_)
  rw [h₁, one_mul]
  exact Pi.basisFun_det_apply _

def matForm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Ev n where
  toFun H := kappa • ∑ a, rowForm a (H a)
  map_add' H H' := by
    rw [← smul_add, ← Finset.sum_add_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_add _ _ _)
  map_smul' c H := by
    rw [RingHom.id_apply, smul_comm, Finset.smul_sum (r := c)]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul (rowForm a) c (H a))

theorem dens_matForm_pow (H : Matrix (Fin n) (Fin n) ℂ) :
    dens ((matForm n H ^ n : Ev n) : Alt n) = ((n.factorial / Real.pi ^ n : ℝ) : ℂ) * H.det := by
  have h := (sum_pow_card (fun a => rowForm a (H a)) (fun a => rowForm_mul_same a a _) Finset.univ).1
  rw [Finset.card_univ, Fintype.card_fin] at h
  change densL n ((kappa • ∑ a, rowForm a (H a)) ^ n) = _
  have e : kappa = (Real.pi : ℂ)⁻¹ * (Complex.I / 2) := by
    rw [kappa]; ring
  rw [smul_pow, h, ← nsmul_eq_mul, map_smul, map_nsmul, ← dens_prod_rowForm, e]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_pow]
  push_cast
  ring

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {σ : k →+* ℂ}

abbrev hessL (L : HermLB p) (c : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  c.hess (L.φ σ) (pick (L.φ σ).isLB y) y

variable {c : AlgChart p σ D} {y : CxPts p σ}

theorem c1F_eq_matForm_hessL (hX : IsRegVar p D) (L : HermLB p) (hy : y ∈ c.e.source) :
    c1F hX σ L ⟨(c, y), hy⟩ = matForm D (hessL L c y) := by
  have hd := (L.cInf σ).contDiffAt c hy (mem_pick (L.φ σ).isLB y)
  change ofValues _ = kappa • ∑ a, rowForm a _
  simp only [ofValues, rowForm, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact congrArg (kappa * ·) (CurveDens.cHess_apply_eq_ddbar (contDiffAt_ofReal_comp hd) a b).symm

theorem hessL_tens (L M : HermLB p) (hy : y ∈ c.e.source) : hessL (L.tens M) c y = hessL L c y + hessL M c y := by
  have ha := mem_pick (L.φ σ).isLB y
  have hb := mem_pick (M.φ σ).isLB y
  exact (c.hess_eq ((L.tens M).cInf σ) hy (i := (pick (L.φ σ).isLB y, pick (M.φ σ).isLB y))
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y)).trans (FlatMass.hess_tens (L.cInf σ) (M.cInf σ) hy ha hb)

theorem hessL_dual (L : HermLB p) (hy : y ∈ c.e.source) : hessL L.dual c y = -hessL L c y := by
  have ha := mem_pick (L.φ σ).isLB y
  exact (c.hess_eq (L.dual.cInf σ) hy (i := (pick (L.φ σ).isLB y : L.B.ι)) ha (mem_pick _ y)).trans
    (FlatMass.hess_dual (L.cInf σ) hy ha)

theorem hessL_pow (L : HermLB p) (m : ℕ) (hy : y ∈ c.e.source) : hessL (L.pow m) c y = (m : ℂ) • hessL L c y := by
  have ha := mem_pick (L.φ σ).isLB y
  refine (c.hess_eq ((L.pow m).cInf σ) hy (i := fun _ => pick (L.φ σ).isLB y) (mem_pow_iff.2 ha)
    (mem_pick _ y)).trans ((FlatMass.hess_zpow (L.cInf σ) hy (m : ℤ) _ ha).trans ?_)
  rw [Int.cast_natCast]

theorem hessL_zp (L : HermLB p) (m : ℤ) (hy : y ∈ c.e.source) : hessL (zp L m) c y = (m : ℂ) • hessL L c y := by
  rw [zp, hessL_tens _ _ hy, hessL_dual _ hy, hessL_pow _ _ hy, hessL_pow _ _ hy, ← sub_eq_add_neg, ← sub_smul]
  congr 1
  exact_mod_cast Int.toNat_sub_toNat_neg m

theorem hessL_comb {ι : Type} [Fintype ι] (L : ι → HermLB p) (m : ι → ℤ) (hy : y ∈ c.e.source) :
    hessL (comb L m) c y = ∑ i, (m i : ℂ) • hessL (L i) c y := by
  rw [comb, ← Finset.sum_map_toList]
  induction (Finset.univ : Finset ι).toList with
  | nil => exact FlatMass.cHess_zero _
  | cons i l ih => rw [List.foldr_cons, hessL_tens _ _ hy, ih, hessL_zp _ _ hy, List.map_cons, List.sum_cons]

theorem chernPart_comb_eq_part : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (ε : ℤˣ),
    ((comb L n).φ σ).chernPart D ε = (hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε := by
  intro k _ X p D hX σ ι _ L n ε
  have key (c : AlgChart p σ D) (y) (hy : y ∈ c.e.source) : c.chernDens ((comb L n).φ σ) y =
      (dens ((hX.atlas σ).loc (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D))
        c (c.e y))).re := by
    refine Eq.trans ?_ (congrArg (fun t => (dens t).re) ((hX.atlas σ).loc_crd _ ⟨(c, y), hy⟩)).symm
    have e : aeval (fun i => c1F hX σ (L i) ⟨(c, y), hy⟩) ((lin (fun i => (n i : ℝ)) ^ D).map (algebraMap ℝ ℂ)) =
        matForm D (hessL (comb L n) c y) ^ D := by
      rw [hessL_comb L n hy]
      simp only [lin, map_pow, map_sum, map_mul, map_C, map_X, aeval_C, aeval_X, map_smul, c1F_eq_matForm_hessL hX _ hy]
      simp [Algebra.smul_def]
    change _ = (dens ((aeval (fun i => c1F hX σ (L i) ⟨(c, y), hy⟩)
      ((lin (fun i => (n i : ℝ)) ^ D).map (algebraMap ℝ ℂ)) : Ev D) : Alt D)).re
    rw [e, dens_matForm_pow, Complex.re_ofReal_mul]
    rfl
  refine iSup_congr fun c => congrArg (Measure.map _) (withDensity_congr_ae ?_)
  filter_upwards [ae_restrict_mem c.e.open_target.measurableSet] with v hv
  exact congrArg (fun t => ENNReal.ofReal (_ * t)) (key c _ (c.e.map_target hv))

end GlobalTheory.ChernTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointNormPsiCoordinateExpNegQuadraticStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classicalPoint_norm_psi_coordinate_exp_neg_quadratic : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) α s, PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ = Real.exp (-l.q (ε α)) := by
  first | exact @GlobalTheory.Poinc.TestAtPt.norm_psi_coord | exact GlobalTheory.Poinc.TestAtPt.norm_psi_coord | (intros; apply GlobalTheory.Poinc.TestAtPt.norm_psi_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProductCoordinateIndependentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_product_coordinate_independent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s s' : Sp Ω ⟶ M.S) (a b c c' : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (x' y' : Over.mk s' ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → s' ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → N.Pt s' a x'.left → N.Pt s' b y'.left → N.Pt s' c' (x' * y').left → c = c' := by
  first | exact @GlobalTheory.Mum.Near.closed_product_unique | exact GlobalTheory.Mum.Near.closed_product_unique | (intros; apply GlobalTheory.Mum.Near.closed_product_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreValueEqUnitMulLeadingFourierTermStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_value_eq_unit_mul_leadingFourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left) (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' → GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' → IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  first | exact @GlobalTheory.Mum.RedVal.closedFibre_val | exact GlobalTheory.Mum.RedVal.closedFibre_val | (intros; apply GlobalTheory.Mum.RedVal.closedFibre_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointMemAbelianLocusOfFixedTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FixedTorsionTrait

theorem abLocus_of_retract {S : Scheme.{0}} (G H : Over S) (i : G ⟶ H) (r : H ⟶ G) (h : i ≫ r = 𝟙 G) :
    ∀ x ∈ abLocus H, x ∈ abLocus G := by
  intro x hx K _ _ t ht
  have hp : IsProper ((Over.pullback t).obj H).hom := hx K t ht
  exact GlobalTheory.Mum.RetractGeneric.isProper_of_retract ((Over.pullback t).map i) ((Over.pullback t).map r)
    (by rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]) hp

theorem closedPoint_mem_abLocus_of_fixedTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → (∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → closedPoint V ∈ abLocus ((Over.pullback (spMap φ)).obj G) := by
  intro R _ _ _ hR D A G _ _ hG U V _ _ _ φ hV hφ n hn hu H
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback (spMap φ) G hG
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj G) := Functor.isCommMonObj_obj
  obtain ⟨A', ψ, hψ⟩ := GlobalTheory.UnifProperOpen.exists_polGeneric_pullback R A G U.gen U.gen_hom V φ hφ
  obtain ⟨W, _, _, _, io, em, D₈, Q, H₈, _, _, U₈, i, r, hW, hfin, hinj, hem, hc, hH₈, htot, hr, hir, hmono⟩ :=
    GlobalTheory.T.degeneration_extension_local_domain V hV A' _ hG' ψ hψ
  have hem' : ∀ w : W, w ≠ 0 → IsUnit (em w) := fun w hw =>
    IsUnit.mk0 _ ((map_ne_zero_iff em hem).2 hw)
  letI : Algebra (FractionRing W) (AlgebraicClosure (FractionRing V)) :=
    (IsFractionRing.lift (A := W) (K := FractionRing W) (g := em) hem).toAlgebra
  have hlift : ∀ w : W, algebraMap (FractionRing W) (AlgebraicClosure (FractionRing V)) (algebraMap W _ w) = em w :=
    fun w => IsFractionRing.lift_algebraMap _ _
  have hcompat : ∀ v, algebraMap (FractionRing W) (AlgebraicClosure (FractionRing V)) (algebraMap W _ (io v)) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v) := fun v => (hlift _).trans (hc v)
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_dvr_algClosure_over_finite_dvr_extension V W hV hW io hfin hinj (AlgebraicClosure (FractionRing V)) hcompat
  have hsub : Subsingleton D₈.toPre.X := by
    refine GlobalTheory.T.characterGroup_subsingleton_of_bounded_ramification W hW D₈ Q H₈ hH₈ U₈ htot (AlgebraicClosure (FractionRing V)) n N hn fun j => ?_
    obtain ⟨T', hT', f, hf, hirr, hfix⟩ := H j
    obtain ⟨T'', hT'', g, e, hle, hg, he1, heN, hπ⟩ := hN T' hT' f hf hirr
    refine ⟨T'', hT'', g, e, hg, he1, heN, hπ, fun σ hσ x hx => ?_⟩
    exact GlobalTheory.T.fixedTorsion_transfer_jointlyMonic_homs V W io _ hcompat _ H₈ r hr hmono σ (fun w => hσ _ (by rw [← hg w]; exact (g w).2)) (n ^ j)
      (fun y hy => hfix σ (fun z hz => hσ z (hle hz)) y hy) x hx
  have := hW.1
  have := hW.2.2
  have hab : IsAbelianScheme H₈ := GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ W hW.2.1 D₈ Q H₈ hH₈ U₈ hsub
  have h₈ : closedPoint W ∈ abLocus H₈ := fun K _ _ t _ => by
    have := hab.proper
    infer_instance
  have h₁ : closedPoint W ∈ abLocus ((Over.pullback (spMap io)).obj ((Over.pullback (spMap φ)).obj G)) :=
    abLocus_of_retract _ H₈ i (r 0) hir _ h₈
  have h₂ := (abLocus_pullback (G' := (Over.pullback (spMap io)).obj ((Over.pullback (spMap φ)).obj G)) abLocusOne hG'
    (IsPullback.of_hasPullback ((Over.pullback (spMap φ)).obj G).hom (spMap io)) (closedPoint W)).2 h₁
  letI : Algebra V W := io.toAlgebra
  have : Algebra.IsIntegral V W := ⟨fun w => hfin.to_isIntegral w⟩
  have hm : (maximalIdeal W).comap io = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := V) (maximalIdeal W))
  have : IsLocalHom io := ((IsLocalRing.local_hom_TFAE io).out 4 0).1 hm
  have e : spMap io (closedPoint W) = closedPoint V := by
    have h : ⇑(spMap io) = PrimeSpectrum.comap io := by
      ext x : 1
      simp [spMap, Spec.map_base]
      rfl
    rw [h]
    exact IsLocalRing.comap_closedPoint io
  rw [← e]
  exact h₂

end GlobalTheory.FixedTorsionTrait

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpecRestrictionCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem spMap_restrict_comp_coefSpecMap : ∀ (M : Scheme.{0}) (W W' : M.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W)
    (R₀ : Type) [CommRing R₀],
    spMap (Algebra.TensorProduct.map (AlgHom.id R₀ R₀) (M.presheaf.map (homOfLE hle).op).hom.toIntAlgHom :
      R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W')).toRingHom ≫ coefSpecMap hW R₀ = coefSpecMap hW' R₀ := by
  intro M W W' hW hW' hle R₀ _
  unfold coefSpecMap spMap
  rw [← hW.map_fromSpec hW' (homOfLE hle).op, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2

end GlobalTheory.RealMult
end

