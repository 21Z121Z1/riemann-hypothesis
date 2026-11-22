import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExceptional
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (cokernel)

namespace GlobalTheory.FlagPull

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open MeasureTheory VMetric
open scoped ENNReal

theorem exists_open_finite_etale : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X), π ≫ p = q →
    π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 →
    ∃ (U : X.Opens) (x : Fin 1 → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Finite ∧
      (π.app U).hom.Etale ∧
      (letI := (π.app U).hom.toAlgebra; Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) =
        π.residueDegree (genericPoint Y) := by
  intro k _ X p _ Y _ q hp hq π hπ hg hd
  obtain ⟨U₁, x, hU₁, hg₁, hx⟩ := GlobalTheory.T.etale_coordinate_near_generic_point k X p hp
  obtain ⟨U, hle, hU, hgU, hV, h₁, h₂, h₃⟩ := GlobalTheory.T.finite_affine_neighbourhood_exists k X p Y q hp hq π hπ hg hd U₁ hg₁
  have hres := Scheme.Hom.etale_appLE (𝟙 X) hU₁ hU hle
  refine ⟨U, fun a => (Scheme.Hom.appLE (𝟙 X) U₁ U hle).hom (x a), hU, hgU, ?_, hV, h₁, h₂, h₃⟩
  have hw : 𝟙 X ≫ p = p ≫ spMap (RingHom.id k) := by
    rw [show spMap (RingHom.id k) = 𝟙 _ from Spec.map_id _, Category.comp_id, Category.id_comp]
  have e : (MvPolynomial.eval₂Hom (algX p U) fun a => (Scheme.Hom.appLE (𝟙 X) U₁ U hle).hom (x a)) =
      (Scheme.Hom.appLE (𝟙 X) U₁ U hle).hom.comp (MvPolynomial.eval₂Hom (algX p U₁) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · have := RingHom.congr_fun (TopForm.appLE_comp_algX (p := p) (p' := p) (φ := 𝟙 X)
        (σ := RingHom.id k) hw (V := U₁) (W := U) hle) a
      simpa using this.symm
    · simp
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ hx hres

theorem exists_finite_exceptional : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q),
    π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ σ : k →+* ℂ,
    ∃ T : Set (CxPts p σ), T.Finite ∧ (PtsOver.map π hπ (spMap σ) ⁻¹' T).Finite ∧
      (∀ x ∉ T, (PtsOver.map π hπ (spMap σ) ⁻¹' {x}).encard = π.residueDegree (genericPoint Y)) ∧
      ∀ z, PtsOver.map π hπ (spMap σ) z ∉ T → ∃ (c : AlgChart p σ 1) (c' : AlgChart q σ 1),
        z ∈ c'.e.source ∧ PtsOver.map π hπ (spMap σ) z ∈ c.e.source ∧
        ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source →
          c'.e w = c.e (PtsOver.map π hπ (spMap σ) w) := by
  intro k _ X p _ Y _ q hp hq π hπ hg hd σ
  obtain ⟨U, x, hU, hgU, hx, hV, hfin, het, hr⟩ := exists_open_finite_etale k X p Y q hp hq π hπ hg hd
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have hgV : genericPoint Y ∈ π ⁻¹ᵁ U := show π (genericPoint Y) ∈ U from hg ▸ hgU
  set m := PtsOver.map π hπ (spMap σ) with hm
  have hmem (z : CxPts q σ) : z ∈ ptsIn q σ (π ⁻¹ᵁ U) ↔ m z ∈ ptsIn p σ U := Iff.rfl
  have hCx (a : k) : algX q (π ⁻¹ᵁ U) a = (π.app U).hom (algX p U a) := by
    have hw : π ≫ p = q ≫ spMap (RingHom.id k) := by
      rw [hπ, show spMap (RingHom.id k) = 𝟙 _ from Spec.map_id _, Category.comp_id]
    have := RingHom.congr_fun (TopForm.appLE_comp_algX (p := p) (p' := q) (φ := π)
      (σ := RingHom.id k) hw (V := U) (W := π ⁻¹ᵁ U) le_rfl) a
    simpa [Scheme.Hom.app_eq_appLE] using this.symm
  have hcx : (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => π.app U (x a)) =
      (π.app U).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · simp [hCx]
    · simp
  have hx' : (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => π.app U (x a)).Etale := by
    rw [hcx]
    exact RingHom.Etale.stableUnderComposition _ _ hx het
  refine ⟨(ptsIn p σ U)ᶜ, GlobalTheory.T.complex_points_off_open_finite k X p hp U hgU σ, GlobalTheory.T.complex_points_off_open_finite k Y q hq _ hgV σ, fun y hy => ?_, fun z hz => ?_⟩
  · have hy' : y ∈ ptsIn p σ U := not_not.1 hy
    have hc := GlobalTheory.T.etale_fibre_embeddings_card Γ(X, U) Γ(Y, π ⁻¹ᵁ U) (π.app U).hom hfin het (evHom hy')
    rw [hr] at hc
    rw [← hc]
    have hz (z : m ⁻¹' {y}) : z.1 ∈ ptsIn q σ (π ⁻¹ᵁ U) := (hmem z.1).2 (by rw [z.2]; exact hy')
    have hev (z : m ⁻¹' {y}) (a) : ev q σ _ ((π.app U).hom a) z.1 = ev p σ U a y := by
      exact (ev_app π hπ U a z.1).trans (congrArg _ z.2)
    refine Set.encard_congr (Equiv.ofBijective (fun z => ⟨evHom (hz z), RingHom.ext fun a => ?_⟩) ⟨?_, ?_⟩)
    · simp only [RingHom.comp_apply, ← ev_eq]
      exact hev z a
    · intro z z' h
      refine Subtype.ext (Subtype.ext (ext_of_valR hV (hz z) (hz z') fun a => ?_))
      have := RingHom.congr_fun (congrArg Subtype.val h) a
      exact (ev_eq (hz z) a).trans (this.trans (ev_eq (hz z') a).symm)
    · rintro ⟨ψ, hψ⟩
      have hC (a : k) : ψ (algX q (π ⁻¹ᵁ U) a) = σ a := by
        have e₁ : algX q (π ⁻¹ᵁ U) a = (π.app U).hom (algX p U a) := hCx a
        rw [e₁]
        exact (RingHom.congr_fun hψ _).trans ((ev_eq hy' _).symm.trans (ev_algX hy' a))
      have hzz := ofHom_mem hV ψ hC
      have hy₂ : m (ofHom hV ψ hC) = y := by
        refine Subtype.ext (ext_of_valR hU hzz hy' fun a => ?_)
        exact ((ev_app π hπ U a _).symm.trans (ev_ofHom hV ψ hC _)).trans
          ((RingHom.congr_fun hψ a).trans (ev_eq hy' a).symm)
      refine ⟨⟨ofHom hV ψ hC, hy₂⟩, Subtype.ext (RingHom.ext fun a => ?_)⟩
      exact (ev_eq hzz a).symm.trans (ev_ofHom hV ψ hC a)
  · have hz' : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := not_not.1 hz
    obtain ⟨c, hc, hcU, hcx⟩ := AlgChart.exists_of_etale hU x hx (σ := σ) (hmem z |>.1 hz')
    obtain ⟨c', hc', hcU', hcx'⟩ := AlgChart.exists_of_etale hV _ hx' hz'
    refine ⟨c, c', hc', hc, fun w hw hw' => ?_⟩
    have key₁ : ∀ (U' : X.Opens) (h : U' = U) (x' : Fin 1 → Γ(X, U')), x' = h ▸ x → ∀ a y,
        ev p σ U' (x' a) y = ev p σ U (x a) y := by
      rintro U' rfl x' rfl a y
      rfl
    have key₂ : ∀ (U' : Y.Opens) (h : U' = π ⁻¹ᵁ U) (x' : Fin 1 → Γ(Y, U')),
        x' = h ▸ (fun a => π.app U (x a)) → ∀ a y,
        ev q σ U' (x' a) y = ev q σ (π ⁻¹ᵁ U) (π.app U (x a)) y := by
      rintro U' rfl x' rfl a y
      rfl
    ext a
    rw [c'.apply_eq w hw a, c.apply_eq _ hw' a, key₂ _ hcU' _ hcx', key₁ _ hcU _ hcx]
    exact ev_app π hπ U _ w

theorem bcMeas_pullStep {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X]
    {q : Y ⟶ Sp k} [IsIntegral Y] (hp : IsArithVar p 1) (hq : IsArithVar q 1) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hg : π (genericPoint Y) = genericPoint X) (hd : π.residueDegree (genericPoint Y) ≠ 0)
    {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) (i : Fin r) (σ : k →+* ℂ) :
    (((h.pull π hπ).stepMet (fl.pull π) i).met σ).bcMeas (stepSeq_shortExact (fl.pull π) i)
        ((fl.pull π).isVB i.castSucc) ((fl.pull π).isVB_gr i) univ =
      π.residueDegree (genericPoint Y) * ((h.stepMet fl i).met σ).bcMeas (stepSeq_shortExact fl i)
        (fl.isVB i.castSucc) (fl.isVB_gr i) univ := by
  obtain ⟨T, hT, hT', hf, hc⟩ := exists_finite_exceptional k X p Y q hp hq π hπ hg hd σ
  have H₁ : (h.stepMet fl i).IsCInf := H.restrict _ _
  have H₂ : ((h.pull π hπ).stepMet (fl.pull π) i).IsCInf := (H.pull π hπ).restrict _ _
  have := CxPts.t2Space_cxPts_of_isProjOver σ hp.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hq.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq.isProjOver
  refine GlobalTheory.T.glueMeas_univ_eq_mul_of_fibre_encard_eq 1 one_ne_zero (CxPts p σ) (CxPts q σ) (AlgChart p σ 1) (AlgChart q σ 1) _ _ _ _
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    _ (PtsOver.continuous_map π hπ _) T hT hT' _ hd hf fun z hz => ?_
  · rw [Met.bcDens_trans _ _ _ c c' (H₁ σ) hy hy', ENNReal.ofReal_mul (sq_nonneg _)]
  · rw [Met.bcDens_trans _ _ _ c c' (H₂ σ) hy hy', ENNReal.ofReal_mul (sq_nonneg _)]
  · obtain ⟨c, c', h₁, h₂, h₃⟩ := hc z hz
    exact ⟨c, c', h₁, h₂, fun w hw hw' => ⟨h₃ w hw hw', congrArg _ (bcDens_pullStep H hπ c c' hw hw' h₃)⟩⟩

theorem exists_isSelfInter (hA : Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (hp : IsArithVar p 1) (L : HermLB p) : ∃ x, L.IsSelfInter x := by
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p 1 hp).2 PUnit fun _ => L).1
  exact ⟨_, ((hA.arIso k X p 1 hp).2 PUnit _ Φ hΦ).1 PUnit.unit⟩

theorem isFlagCh2_pull : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r), ∃ fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) r, ∀ a : ℝ, VMetric.IsFlagCh2 H fl a ↔ VMetric.IsFlagCh2 (H.pull π hπ) fl' (π.residueDegree (genericPoint Y) * a) := by
  intro hA k _ X p _ Y _ q hp hq π hπ hg hd E r h H fl
  refine ⟨fl.pull π, fun a => ?_⟩
  set d := π.residueDegree (genericPoint Y) with hd'
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₀ : (d : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₁ : (d : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hm := fun i σ => bcMeas_pullStep hp hq π hπ hg hd H fl i σ
  have hfin : h.FlagBcFinite fl ↔ (h.pull π hπ).FlagBcFinite (fl.pull π) := by
    have key (x : ENNReal) : x ≠ ⊤ ↔ (d : ENNReal) * x ≠ ⊤ := by
      simp [ENNReal.mul_eq_top, hdE₀, hdE₁]
    refine forall_congr' fun i => forall_congr' fun σ => ?_
    rw [hm i σ]
    exact key _
  have := hp.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hbc : (h.pull π hπ).flagBc (fl.pull π) = d * h.flagBc fl := by
    rw [flagBc, flagBc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bcInt, bcInt, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hm i σ, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hx : ∀ (i : Fin r) (x : ℝ), (grLB fl i H).IsSelfInter x →
      (grLB (fl.pull π) i (H.pull π hπ)).IsSelfInter (d * x) := fun i x hx =>
    (GlobalTheory.T.graded_metric_pullback_isometric k X Y p q E r h H fl π hπ i).symm.isSelfInter hq ((hA.arProj k X Y p q 1 hp hq π hπ hg hd).1 _ x hx)
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, x, h₂, rfl⟩
    refine ⟨hfin.1 h₁, fun i => d * x i, fun i => hx i _ (h₂ i), ?_⟩
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [mul_div_assoc]
  · rintro ⟨h₁, x', h₂, e⟩
    choose x hx₀ using fun i => exists_isSelfInter hA hp (grLB fl i H)
    refine ⟨hfin.2 h₁, x, hx₀, mul_left_cancel₀ hd0 (e.trans ?_)⟩
    have e' (i) : x' i = d * x i := (h₂ i).unique hq (hx i _ (hx₀ i))
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [e', mul_div_assoc]

end GlobalTheory.FlagPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapSignaturesDependOnPlace
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem exists_isFockMapD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C →
    ∃ Φ, IsFockMapD ψ τ d A C Φ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ α β κ ψ JA JB d hψ
  have hDf : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
      fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x :=
    fun u hu f x => (hD u hu f).2 x
  obtain ⟨hadd, hsm, hcom⟩ := GlobalTheory.T.archHeisenbergDerivative_additive_commutator σ JA JB d D hDf
  have hex := fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose uOf huOf using fun c => (hex c).exists
  have huniq : ∀ c u, At (evI F) u → (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → u = uOf c :=
    fun c u hu hw => (hex c).unique ⟨hu, hw⟩ (huOf c)
  have hAt_add : ∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → At (evI F) (u + u') :=
    fun u u' hu hu' z hz => by rw [smul_add, hu z hz, hu' z hz, add_zero]
  have hAt_smul : ∀ (r : ℝ) (u : Matrix α β (AE F E)), At (evI F) u → At (evI F) (realAd F r • u) :=
    fun r u hu z hz => by rw [smul_comm, hu z hz, smul_zero]
  let H : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ (SInf F κ) :=
    fun c => (D (uOf c)).toLinearMap
  have hHadd : ∀ c c', H (c + c') = H c + H c' := by
    intro c c'
    have e : uOf (c + c') = uOf c + uOf c' := by
      symm
      refine huniq _ _ (hAt_add _ _ (huOf c).1 (huOf c').1) fun w => ?_
      rw [Matrix.map_add _ (map_add _), (huOf c).2 w, (huOf c').2 w]
      simp [Matrix.mul_add, Matrix.add_mul]
    ext1 f
    simp only [H, e, hadd _ _ (huOf c).1 (huOf c').1]
    rfl
  have hHsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c := by
    intro r c
    have e : uOf ((r : ℂ) • c) = realAd F r • uOf c := by
      symm
      refine huniq _ _ (hAt_smul r _ (huOf c).1) fun w => ?_
      rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (huOf c).2 w]
      simp [Matrix.mul_smul, Matrix.smul_mul]
    ext1 f
    simp only [H, e, hsm _ r (huOf c).1]
    rfl
  have hHcomm : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1 := by
    intro c c'
    ext1 f
    have h1 := hcom _ _ (huOf c).1 (huOf c').1 f
    rw [GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a b A C hCM hFr _ _ c c' (huOf c).1 (huOf c').1 (huOf c).2 (huOf c').2] at h1
    simp only [H, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [h1]
    congr 1
    push_cast
    ring
  obtain ⟨f₀, hf₀, hv⟩ := GlobalTheory.T.exists_gaussianVacuum_frames_placeSignatures σ τ JA JB d a b A C D hCM hFr hDf
  have hHvac : ∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0 := fun w a b =>
    hv w a b _ _ (huOf _).1 (huOf _).1 (huOf _).2 (huOf _).2
  obtain ⟨Φ, hinj, hint⟩ := GlobalTheory.T.fockMap_of_canonicalCommutation_placewise_signature H hHadd hHsmul hHcomm f₀ hf₀ hHvac
  refine ⟨Φ, hinj, fun u hu c hc T => ?_⟩
  rw [hint, huniq c u hu hc]
  exact (hD _ (huOf c).1 (Φ T)).1

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatVecDomain

theorem discrete_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    DiscreteTopology (GlobalTheory.ThetaParseval.ratVec F κ) := by
  obtain ⟨U, hU, hx⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have hN : (Set.univ.pi fun _ : κ => U) ∈ nhds (0 : κ → AdeleRing (𝓞 F) F) :=
    set_pi_mem_nhds Set.finite_univ fun _ _ => hU
  refine discreteTopology_of_isOpen_singleton_zero ?_
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
  have hc : ContinuousAt (fun x : GlobalTheory.ThetaParseval.ratVec F κ => (x : κ → AdeleRing (𝓞 F) F)) 0 :=
    continuous_subtype_val.continuousAt
  refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
  rintro ⟨y, hy⟩ hyU
  obtain ⟨ξ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff y).1 hy
  have hξ : ξ = 0 := funext fun i => hx _ (hyU i (Set.mem_univ i))
  subst hξ
  refine Subtype.ext ?_
  funext i
  simp

theorem exists_compact_cover_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ K : Set (κ → AdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ x, ∃ γ ∈ GlobalTheory.ThetaParseval.ratVec F κ, γ + x ∈ K := by
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  choose c hc using hx
  refine ⟨Set.univ.pi fun _ : κ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  refine ⟨fun i => algebraMap F (AdeleRing (𝓞 F) F) (-c (x i)),
    (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨fun i => -c (x i), rfl⟩, fun i _ => ?_⟩
  have := hc (x i)
  simpa [map_neg, neg_add_eq_sub] using this

theorem exists_fundamentalDomain : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ 𝓕₁ : Set (κ → AF F), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ ∧ μ 𝓕₁ ≠ 0 ∧ μ 𝓕₁ ≠ ⊤ := by
  intro F _ _ κ _ μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := discrete_ratVec F κ
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) :=
    GlobalTheory.countable_of_discrete_addSubgroup _
  obtain ⟨K, hK, hcov⟩ := exists_compact_cover_ratVec F κ
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup
    (GlobalTheory.ThetaParseval.ratVec F κ)
  exact ⟨D, hD μ, (hD μ).measure_ne_zero (NeZero.ne μ),
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact _ hK hcov μ (hD μ)).ne⟩

end GlobalTheory.RatVecDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedQuotientMapOfLocalQuotients
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotGlue

theorem exists_glueMap (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j)
    (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left)
    (G : Scheme.{0}) (F : G ⟶ S) (ψ : ∀ j, (B j).left ⟶ G)
    (hb : ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left)
    (hψ : ∀ j k, pullback.fst _ _ ≫ ψ j = b j k ≫ ψ k) (hψF : ∀ j, ψ j ≫ F = (B j).hom ≫ 𝒰.f j) :
    ∃ Qm : A.left ⟶ G, Qm ≫ F = A.hom ∧ ∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Qm := by
  let qL : ∀ j, pullback A.hom (𝒰.f j) ⟶ (B j).left := fun j => (q j).left
  have hq : ∀ j, qL j ≫ (B j).hom = pullback.snd A.hom (𝒰.f j) := fun j => Over.w (q j)
  have hb' : ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
      (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
      w ≫ pullback.fst _ _ = y ≫ qL j → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ qL k := hb
  have key : ∀ j k, pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL j ≫ ψ j =
      pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL k ≫ ψ k := by
    intro j k
    have e : pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.fst A.hom (𝒰.f j) =
        pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.fst A.hom (𝒰.f k) :=
      pullback.condition
    have hw : (pullback.fst (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ qL j) ≫ ((B j).hom ≫ 𝒰.f j) =
        (pullback.snd (pullback.fst A.hom (𝒰.f j)) (pullback.fst A.hom (𝒰.f k)) ≫ pullback.snd A.hom (𝒰.f k)) ≫ 𝒰.f k := by
      rw [Category.assoc, reassoc_of% (hq j), ← pullback.condition, ← Category.assoc, e,
        Category.assoc, Category.assoc, pullback.condition]
    have h1 := hb' j k _ _ _ (pullback.lift _ _ hw) e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    rw [← Category.assoc, ← pullback.lift_fst _ _ hw, Category.assoc, hψ, ← Category.assoc, h1, Category.assoc]
  have hc : ∀ j k, pullback.fst ((𝒰.pullback₁ A.hom).f j) ((𝒰.pullback₁ A.hom).f k) ≫ (qL j ≫ ψ j) =
      pullback.snd ((𝒰.pullback₁ A.hom).f j) ((𝒰.pullback₁ A.hom).f k) ≫ (qL k ≫ ψ k) := key
  have hι : ∀ j, pullback.fst A.hom (𝒰.f j) ≫ Scheme.Cover.glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc =
      qL j ≫ ψ j := fun j => Scheme.Cover.ι_glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc j
  refine ⟨Scheme.Cover.glueMorphisms (𝒰.pullback₁ A.hom) (fun j => qL j ≫ ψ j) hc, ?_, fun j => (hι j).symm⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ A.hom) _ _ fun (j : 𝒰.I₀) => ?_
  show pullback.fst A.hom (𝒰.f j) ≫ _ ≫ F = pullback.fst A.hom (𝒰.f j) ≫ A.hom
  rw [reassoc_of% (hι j), hψF, reassoc_of% (hq j), pullback.condition]

end GlobalTheory.QuotGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackAlongStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_pullback_along : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : GlobalTheory.UPel.HT.Obj b N s), ∃ o' : GlobalTheory.UPel.HT.Obj b N (f ≫ s), Nonempty (GlobalTheory.UPel.HT.ObjMap o' o f) := by
  first | exact @GlobalTheory.UPel.HT.Pull.exists_objMap | exact GlobalTheory.UPel.HT.Pull.exists_objMap | (intros; apply GlobalTheory.UPel.HT.Pull.exists_objMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGaloisStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_points_larger_field_galois : ∀ (K Ω Ω' : Type) [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') (A : Over (Sp K)) [GrpObj A], ∃ f : (ptOver K Ω ⟶ A) →* (ptOver K Ω' ⟶ A), Function.Injective f ∧ ∀ (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω'), (∀ x, σ' (j x) = j (σ x)) → ∀ x, f (specAut σ ≫ x) = specAut σ' ≫ f x := by
  first | exact @GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois | exact GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois | (intros; apply GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDualRiemann
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

theorem PPAS.exists_isDualRiemann : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (P : PPAS X) (t : ℝ), 0 < t → ∃ h : VMetric p (LieVB.omega P.A) P.g, P.IsDualRiemann t h :=
  PPAS.exists_isDualRiemann_of GlobalTheory.CovFactor.exists_cov_eq_mulVec GlobalTheory.UnifTangent.riemannData_tangent GlobalTheory.UnifImmersive.eq_zero_of_cov GlobalTheory.PPAS.exists_conj_riemannData
    GlobalTheory.RiemannExists.nonempty_riemannData GlobalTheory.RiemIndep.riemann_dual_form_indep

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGenIsoPullbackLineBundleZpowStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isGen_iso_pullback_lineBundle_zpow : ∀ {X Y Z : Scheme.{0}} (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y) (w : LB.Iso (M.pull f) (H.pull g)), M.IsLB → H.IsLB → w.IsGen → ∀ n : ℤ, ∃ w' : LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g), w'.IsGen := by
  first | exact @GlobalTheory.PullPow.exists_isGen_iso_pw | exact GlobalTheory.PullPow.exists_isGen_iso_pw | (intros; apply GlobalTheory.PullPow.exists_isGen_iso_pw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionOfGenericFibreDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_extension_of_genericFiber : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ N : LB (pullback G.hom (spMap (algebraMap W K'))), N.IsLB → ∃ (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), M.IsLB ∧ w.IsGen := by
  first | exact @GlobalTheory.exists_lineBundle_extension_of_genericFibre_dvr | exact GlobalTheory.exists_lineBundle_extension_of_genericFibre_dvr | (intros; apply GlobalTheory.exists_lineBundle_extension_of_genericFibre_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalWeightEqCharacterExponentAddStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremalWeight_eq_character_exponent_add : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC (Wc D i), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) u = ∏ ρ, (archM (Wc D i) (R.θ ρ) u).det ^ e ρ) ∧ ∀ k ρ (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin (Wc D i).rank, w ρ a = (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) k τ (Fin.cast (rank_Wc i) a) + e ρ := by
  first | exact @GlobalTheory.HolDict.extWt_eq_laU_add | exact GlobalTheory.HolDict.extWt_eq_laU_add | (intros; apply GlobalTheory.HolDict.extWt_eq_laU_add <;> assumption)
end

