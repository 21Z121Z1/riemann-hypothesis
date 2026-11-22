import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelStatementOfFrameGalois
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization GlobalTheory.ExpModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem atPts_and2 {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : AtPts Q) (h' : AtPts Q') : AtPts fun Fm x hx i p => Q Fm x hx i p ∧ Q' Fm x hx i p :=
  Closed.imp (Closed.and h h') fun _ _ _ H => by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := H
    exact ⟨max a b, fun x hx hle i p hp hm => ⟨ha x hx ((le_max_left _ _).trans hle) i p hp hm,
      hb x hx ((le_max_right _ _).trans hle) i p hp hm⟩⟩

theorem atPts_imp2 {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : AtPts Q) (f : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), More p →
      Q Fm x hx i p → Q' Fm x hx i p) : AtPts Q' :=
  Closed.imp h fun Fm _ _ H => by
    obtain ⟨a, ha⟩ := H
    exact ⟨a, fun x hx hle i p hp hm => f Fm x hx i p hm (ha x hx hle i p hp hm)⟩

theorem exists_lift_subquot {A V : Type} [Ring A] [AddCommGroup V] [Module A V] (S : Submodule A V) (E : Submodule A (V ⧸ S))
    (N' : Submodule A E) : ∃ (U : Submodule A V) (π : U →ₗ[A] (E ⧸ N')), Function.Surjective π ∧ ∀ x : U, (x : V) ∈ S → π x = 0 := by
  let g : E.comap S.mkQ →ₗ[A] E := (S.mkQ.domRestrict (E.comap S.mkQ)).codRestrict E (fun x => x.2)
  refine ⟨E.comap S.mkQ, N'.mkQ ∘ₗ g, fun z => ?_, fun x hx => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨v, hv⟩ := Submodule.mkQ_surjective S a
    have hvU : v ∈ E.comap S.mkQ := by rw [Submodule.mem_comap, hv]; exact a.2
    have hg : g ⟨v, hvU⟩ = a := Subtype.ext hv
    exact ⟨⟨v, hvU⟩, congrArg N'.mkQ hg⟩
  · have hg : g x = 0 := Subtype.ext ((Submodule.Quotient.mk_eq_zero S).2 hx)
    exact (congrArg N'.mkQ hg).trans (map_zero _)

set_option maxHeartbeats 800000 in

theorem winputs_of_simple {ι : Type} [DecidableEq ι] (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (W : Wts ι) (X : HidaSetting ι P.Nr W.lam) (l : ℕ) (ϖ : X.O)
    (n₀ : ℕ) (e : ι → (Fin P.Nr → ℕ) → X.A) (hfin : Finite (X.O ⧸ Ideal.span {(l : X.O)})) (hd : (l : X.O) ∣ ϖ ^ n₀)
    (hA : X.FrameA e) (hS : HeckeStable X.O X.Γ X.jK X.T (NablaT X.O P.Nr W.lam))
    (hQ : ∀ (Gm : Type) [AddCommGroup Gm] [Module X.O Gm] [Module X.A Gm] [IsScalarTower X.O X.A Gm], IsSimpleModule X.A Gm →
      (∃ (U : Submodule X.A (NablaT X.O P.Nr W.lam)) (π : U →ₗ[X.A] Gm), Function.Surjective π ∧
        ∀ (x : U) (y : NablaT X.O P.Nr W.lam), (x : NablaT X.O P.Nr W.lam) = ϖ • y → π x = 0) →
      ∃ (_ : Module X.T (Forms X.O X.Γ X.jK Gm)) (hw : ι → Fin P.Nr → ℕ),
        HeckeNat X.O X.Γ X.jK X.T (NablaT X.O P.Nr W.lam) Gm ∧ (∀ τ, ∃ z : Gm, e τ (hw τ) • z ≠ 0) ∧
        (¬ Subsingleton (LocalizedModule X.S (Forms X.O X.Γ X.jK Gm)) → ∀ τ, LatticeLink P W l τ (hw τ))) :
    WInputsLink P W X l := by
  have hsq : ∀ μ : SimpIx X ϖ, ∃ (U : Submodule X.A (NablaT X.O P.Nr W.lam)) (π : U →ₗ[X.A] SimpMod X ϖ μ), Function.Surjective π ∧
      ∀ (x : U) (y : NablaT X.O P.Nr W.lam), (x : NablaT X.O P.Nr W.lam) = ϖ • y → π x = 0 := by
    intro μ
    obtain ⟨U, π, h1, h2⟩ := exists_lift_subquot _ μ.1 μ.2.1
    exact ⟨U, π, h1, fun x y hxy => h2 x ⟨y, hxy⟩⟩
  have h := fun μ : SimpIx X ϖ => hQ (SimpMod X ϖ μ) μ.2.2 (hsq μ)
  choose mT hw h1 h2 h3 using h
  exact ⟨ϖ, n₀, e, SimpIx X ϖ, SimpMod X ϖ, fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, mT, hw, hfin, hd, hA, ⟨hS, h1⟩, ⟨fun Gm _ _ _ hq => exists_simpMod Gm hq, h2⟩,
    fun μ _ hn τ _ => h3 μ hn τ⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem winputs_frame : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), W.Ok P → (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK (NablaT F.O P.Nr W.lam))] [IsScalarTower F.O F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK (NablaT F.O P.Nr W.lam))], F.IsHecke W.lam jK (NablaT F.O P.Nr W.lam) → Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) → ¬ IsUnit ((l : ℕ) : F.O) → ∀ (m : Ideal F.T) [hm : m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → haveI := hm.isPrime; WInputsLink P (reFr W fr cjj) (F.setting W.lam jK m) l := by
  intro E Ω _ _ _ _ _ _ hCheb l _ ι _ _ inc fr cjj P W hW hlink F hF Bk hG jK hJ _ _ hH hfin hnu m hm θ0 h0e h0b h0o
  obtain ⟨ϖ, n₀, hϖ, hϖl, hlϖ⟩ := exists_unif_dvd F.O l (Fact.out : l.Prime).ne_zero hnu
  have hanti : ∀ τ, Antitone (res P.Nr (W.lam τ)) := fun τ a b h => hW.anti τ a b h b.2
  choose e0 he0 hu0 using GlobalTheory.ExpFrame.exists_unique_isProj F.O P.Nr ι W.lam
  let e : ι → (Fin P.Nr → ℕ) → alg F.O P.Nr W.lam := fun τ w => ⟨e0 τ w, Algebra.subset_adjoin (Or.inr ⟨τ, w, he0 τ w⟩)⟩
  have hQ : ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm]
      [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm], IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm →
      ∃ (_ : Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) (hw : ι → Fin P.Nr → ℕ),
        HeckeNat F.O (A := alg F.O P.Nr W.lam) F.Γ jK F.T (NablaT F.O P.Nr W.lam) Gm ∧ (∀ τ, ∃ z : Gm, e τ (hw τ) • z ≠ 0) ∧
        (¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) →
          ∀ τ, LatticeLink P (reFr W fr cjj) l τ (hw τ)) := by
    intro Gm _ _ _ _ hs hq
    obtain ⟨mT, _, hHG⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module l ι P.Nr F W.lam jK hF hJ Gm
    obtain ⟨mu, hmu, hemb⟩ := GlobalTheory.T.simpleSubquotient_dualWeyl_embeds_highestWeight F.O P.Nr ι W.lam ϖ hϖ hanti Gm hs hq
    refine ⟨mT, fun τ => res P.Nr (mu τ), (GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action l ι P.Nr F W.lam jK Gm hH hHG).2, fun τ => ?_, fun hn =>
      GlobalTheory.T.latticeLink_of_surviving_simple_subquotient E Ω hCheb l ι inc fr cjj P W hlink F hF Bk hG jK hJ ϖ hϖ hϖl hanti Gm hHG hs hq mu
        (fun τ => ⟨(hmu τ).1, (hmu τ).2.1, (hmu τ).2.2.1⟩) hemb m θ0 h0e h0b h0o hn⟩
    obtain ⟨e', z, hp, hz⟩ := (hmu τ).2.2.2
    have hee : e τ (res P.Nr (mu τ)) = e' := Subtype.ext (hu0 τ _ _ hp).symm
    exact ⟨z, hee ▸ hz⟩
  haveI := hm.isPrime
  exact winputs_of_simple P (reFr W fr cjj) (F.setting W.lam jK m) l ϖ n₀ e hfin hlϖ
    ⟨GlobalTheory.ExpFrame.alg_chainB_stable F.O P.Nr ι W.lam, fun τ w => he0 τ w⟩
    (GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action l ι P.Nr F W.lam jK (NablaT F.O P.Nr W.lam) hH hH).1
    (fun Gm i1 i2 i3 i4 => @hQ Gm i1 i2 i3 i4)

open Classical in
set_option maxHeartbeats 1600000 in

theorem modelSt_of_frames : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.ChebotarevDegreeOne → SmallSt → FrameSt →
    GlobalTheory.ExpTie.GalSt → ModelSt := by
  intro hBS hCheb hS hFr hGal
  refine atPts_imp2 (atPts_and2 hS (atPts_and2 hFr hGal)) ?_
  intro eps Fm x hx i p _ H j P W hD hN w hw hR
  obtain ⟨hs, hf, hg⟩ := H
  have hsm : SmallAt p j P w := hs j P W hD hN w hw hR
  haveI hl : Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime := ⟨hsm.1⟩
  obtain ⟨F, R, inc, hFok, ⟨T⟩⟩ := @hf j P W hD hN w hw hR hl
  have hG := @hg j P W hD hN w hw hR hl F R inc hFok T
  have hNr := hN.1.Nr_eq
  have ht := hN.1.t_ge
  have hl2 : Formalism.EigenvalueLevelCeiling.plc w ≠ 2 := by have := hsm.2.1; omega
  obtain ⟨fr, cjj, hlk⟩ := GlobalTheory.T.crystallineLatticeLink_of_blockData hBS _ (AlgebraicClosure (Fm.D x i).host.E) (Formalism.EigenvalueLevelCeiling.plc w) hl2 hsm.2.2.1 _ inc T.half
  obtain ⟨jK, hJ⟩ := GlobalTheory.ExpFrame.levelMap_exists (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam
  obtain ⟨_, _, hH⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam jK hFok hJ (NablaT F.O P.Nr W.lam)
  refine ⟨fr, cjj, {m : MaximalSpectrum F.T // ∃ θ, R.Occurs (subZ p j (p.R.mu w)) θ ∧ F.Over θ m.asIdeal},
    fun m => haveI := m.1.isMaximal.isPrime; F.setting W.lam jK m.1.asIdeal, ?_, ?_⟩
  · exact GlobalTheory.T.maximalIdeals_meeting_subspace_cover _ _ _ (blk p j (p.R.mu w)) w _ P.Nr F W.lam jK hFok hJ hH R (lvlL p) _ hsm.2.2.2.1
  · rintro ⟨m, θ0, hocc, hov⟩
    have hop : ∀ Q, (blk p j (p.R.mu w)).op (Q, 0) = 1 := fun Q => (p.charW.base.fam.degL j (p.R.mu w) Q).1
    obtain ⟨hb, he⟩ := GlobalTheory.T.hasBlocks_of_system_occurs_in_block_part _ _ _ (blk p j (p.R.mu w)) w (Formalism.EigenvalueLevelCeiling.plc w) _ P.Nr F W.lam R _ hop hsm.2.2.2.2 θ0 hocc
    exact ⟨GlobalTheory.T.frameCoeffRing_prime_not_isUnit _ _ _ F hFok, winputs_frame _ (AlgebraicClosure (Fm.D x i).host.E) hCheb (Formalism.EigenvalueLevelCeiling.plc w) _ inc fr cjj P W hN.2.2.1
      (hlk P W hN.1 hN.2.2.1 hD.box) F hFok R.HasBlock hG jK hJ hH (GlobalTheory.T.finite_frameCoeffRing_quotient_prime _ _ _ F hFok) (GlobalTheory.T.frameCoeffRing_prime_not_isUnit _ _ _ F hFok) m.asIdeal θ0 he hb hov⟩

end GlobalTheory.ExpModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleActionFractionFieldStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_action_fraction_field : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M]
    (K : Type) [Field K] [Algebra R K],
    (∀ k : K, ∃ a s : R, algebraMap R K s ≠ 0 ∧ algebraMap R K s * k = algebraMap R K a) →
    ∀ (N : Type) [AddCommGroup N] [Module K N] [Module O N] [SMulCommClass K O N]
    (e : K ⊗[R] M ≃ₗ[K] N),
    (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    (letI : Module (K ⊗[ℤ] O) N := TensorProduct.Algebra.module;
      Module.Invertible (K ⊗[ℤ] O) N) →
    ∃ m : M, Function.Bijective
      (Finsupp.linearCombination K (fun i => (1 : K) ⊗ₜ[R] (b i • m))) := by
  first | exact @GlobalTheory.exists_fibre_generator_basis | exact GlobalTheory.exists_fibre_generator_basis | (intros; apply GlobalTheory.exists_fibre_generator_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismTrivialOnReducedKernel
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelKill

theorem comp_eq_one_of_kill_closedPoints : ∀ (A Y Y' Z : Over (Sp ℂ)) [GrpObj A] [GrpObj Y] [GrpObj Y'] [IsSeparated Y'.hom] (u : A ⟶ Y) (f : A ⟶ Y')
    (i : Z ⟶ A), IsPullback i (toUnit Z) u η[Y] → ∀ [AlgebraicGeometry.IsReduced Z.left] [LocallyOfFiniteType Z.hom],
    (∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ u = 1 → x ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ u = 1 → x ≫ f = 1 := by
  intro A Y Y' Z _ _ _ _ u f i hk _ _ h T x hx
  have hiu : i ≫ u = 1 := hk.w
  have key : i ≫ f = 1 := by
    refine Over.OverMorphism.ext ?_
    have : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
    refine ext_of_fromSpecResidueField_eq _ _ Y'.hom (closedPoints Z.left) ?_ (fun z hz => ?_)
      ((Over.w _).trans (Over.w _).symm)
    · rw [dense_iff_closure_eq, closure_closedPoints]
    · have hz' : IsClosed ({z} : Set Z.left) := hz
      let q : 𝟙_ (Over (Sp ℂ)) ⟶ Z :=
        Over.homMk (pointOfClosedPoint Z.hom z hz') (pointOfClosedPoint_comp _ _ _)
      have hq : q ≫ i ≫ f = q ≫ 1 := by
        rw [MonObj.comp_one, ← Category.assoc]
        apply h
        rw [Category.assoc, hiu, MonObj.comp_one]
      have e := congrArg CommaMorphism.left hq
      simp only [Over.comp_left] at e
      have hp : Z.left.fromSpecResidueField z =
          Spec.map (residueFieldIsoBase Z.hom z hz').inv ≫ pointOfClosedPoint Z.hom z hz' := by
        simp only [pointOfClosedPoint, ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id,
          Category.id_comp]
      rw [hp, Category.assoc, Category.assoc]
      congr 1
  have hx' : x ≫ u = toUnit T ≫ η[Y] := hx
  rw [← hk.lift_fst x (toUnit T) hx', Category.assoc, key, MonObj.comp_one]

end GlobalTheory.KernelKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesIsAdicCompleteMapCOfNoetherian
section
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.PowerSeriesComplete

theorem isAdicComplete_map_C : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R))
      (MvPowerSeries (Fin n) R) := by
  intro R _ _ I hI n
  have hfg : I.FG := IsNoetherian.noetherian I
  have hC : (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) = algebraMap R (MvPowerSeries (Fin n) R) := rfl
  have hP : IsPrecomplete I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isPrecomplete_pi (M := R) (Fin n →₀ ℕ) hfg
  have hH : IsHausdorff I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isHausdorff_pi (M := R) (Fin n →₀ ℕ) hfg
  rw [hC]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 hH
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 hP }

end GlobalTheory.PowerSeriesComplete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatFamilyExistsUnique
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt

abbrev locAlg (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (s : D) :
    D →ₐ[R] Localization.Away s :=
  IsScalarTower.toAlgHom R D (Localization.Away s)

theorem sm_loc_of_mem {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} (W : K → X.left.Opens)
    (hW : ⨆ i, W i = ⊤) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) (P : PrimeSpectrum D) :
    ∃ s : D, s ∉ P.asIdeal ∧ Sm W (spOver (locAlg R s) ≫ x) := by
  have h1 : x.left.base P ∈ (⨆ i, W i) := by rw [hW]; trivial
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).mp h1
  obtain ⟨V, ⟨s, rfl⟩, hPV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := P)
      (u := (x.left ⁻¹ᵁ W i).1) hi (x.left ⁻¹ᵁ W i).isOpen
  refine ⟨s, hPV, i, fun q _ ↦ ?_⟩
  have hq : (spMap (algebraMap D (Localization.Away s))).base q ∈ PrimeSpectrum.basicOpen s := by
    change s ∉ (PrimeSpectrum.comap (algebraMap D (Localization.Away s)) q).asIdeal
    intro h
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
  exact hVU hq

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

def awR (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    Localization.Away a →ₐ[R] Localization.Away (a * b) where
  toRingHom := IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b
  commutes' r := by
    change IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b (algebraMap R _ r) = _
    rw [IsScalarTower.algebraMap_apply R D (Localization.Away a),
      IsLocalization.Away.awayToAwayRight_eq, ← IsScalarTower.algebraMap_apply]

def awL (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    Localization.Away b →ₐ[R] Localization.Away (a * b) where
  toRingHom := IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a
  commutes' r := by
    change IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a (algebraMap R _ r) = _
    rw [IsScalarTower.algebraMap_apply R D (Localization.Away b),
      IsLocalization.Away.awayToAwayLeft_eq, ← IsScalarTower.algebraMap_apply]

theorem awR_comp (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    (awR R a b).comp (locAlg R a) = locAlg R (a * b) := by
  ext z
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom']
  exact IsLocalization.Away.awayToAwayRight_eq (P := Localization.Away (a * b)) a b z

theorem awL_comp (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D] (a b : D) :
    (awL R a b).comp (locAlg R b) = locAlg R (a * b) := by
  ext z
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom']
  exact IsLocalization.Away.awayToAwayLeft_eq (P := Localization.Away (a * b)) b a z

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem natFamily_existsUnique : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (spOver ψ ≫ x) → τ E' (θ.comp ψ) = θ (τ E ψ)) → ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), Sm W (spOver ψ ≫ x) → τ E ψ = ψ d := by
  intro R _ X K W hW D _ _ x τ hτ
  let S : Set D := {s | Sm W (spOver (locAlg R s) ≫ x)}
  have key : ∀ (s : D), s ∈ S → ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
      (θ : Localization.Away s →ₐ[R] E), θ.comp (locAlg R s) = ψ → θ (τ _ (locAlg R s)) = τ E ψ := by
    intro s hs E _ _ ψ θ h
    rw [← hτ _ _ _ θ hs, h]
  have span : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hSM⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨s, hsM, hs⟩ := sm_loc_of_mem W hW x ⟨M, hM.isPrime⟩
    exact hsM (hSM (Ideal.subset_span hs))
  let v : ∀ a : S, Localization.Away a.1 := fun a ↦ τ _ (locAlg R a.1)
  obtain ⟨d, hd, hu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top S span v (fun a b ↦ by
    have e1 := key a a.2 _ _ (awR R (a : D) b) (awR_comp R _ _)
    have e2 := key b b.2 _ _ (awL R (a : D) b) (awL_comp R _ _)
    exact e1.trans e2.symm)
  refine ⟨d, fun E _ _ ψ hψ ↦ ?_, fun d' hd' ↦ hu d' fun a ↦ (hd' _ (locAlg R a.1) a.2).symm⟩
  have spanE : Ideal.span (ψ '' S) = ⊤ := by
    rw [← Ideal.map_span, span, Ideal.map_top]
  apply Localization.algebraMap_injective_of_span_eq_top _ spanE
  funext ⟨t, s, hs, ht⟩
  subst ht
  let θ : E →ₐ[R] Localization.Away (ψ s) := locAlg R (ψ s)
  let θ' : Localization.Away s →ₐ[R] Localization.Away (ψ s) := Localization.awayMapₐ ψ s
  have hc : θ'.comp (locAlg R s) = θ.comp ψ := AlgHom.ext fun z ↦ by
    simp [θ', θ, Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
  change θ (τ E ψ) = θ (ψ d)
  have e : τ _ (locAlg R s) = algebraMap D _ d := (hd ⟨s, hs⟩).symm
  rw [← hτ E _ ψ θ hψ, ← hc, ← key s hs _ _ θ' rfl, e]
  exact DFunLike.congr_fun hc d

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalBijectiveCoefficientsPull1Bijective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.BC

theorem natCoef_pull1_bijective (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F F' : C ⥤ CommAlgCat.{0} R)
    (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) :
    (∀ T, Function.Bijective (α T)) → Function.Bijective (GlobalTheory.Obs.BC.natCoef α nat smul).pull1 := by
  intro hb
  let β : ∀ T, F'.obj T →+* F.obj T := fun T ↦ (RingEquiv.ofBijective (α T) (hb T)).symm.toRingHom
  have hαβ : ∀ T (b : F'.obj T), α T (β T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).apply_symm_apply b
  have hβα : ∀ T (b : F.obj T), β T (α T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).symm_apply_apply b
  have natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b) := by
    intro T T' a b
    apply (hb T').1
    rw [hαβ, nat, hαβ]
  have smulβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b := by
    intro T r b
    apply (hb T).1
    rw [hαβ, smul, hαβ]
  let m := GlobalTheory.Obs.BC.natCoef α nat smul
  let n := GlobalTheory.Obs.BC.natCoef β natβ smulβ
  have left : ∀ c, n.pull1 (m.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hβα T' _
  have right : ∀ c, m.pull1 (n.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F' c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hαβ T' _
  exact ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩

end GlobalTheory.Obs.BC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefAtOfPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

namespace GlobalTheory.NefDeRhamAt

theorem nefAt_of_pull (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (hp : IsProjOver p) (hq : IsProjOver q) (π : Y ⟶ X) (hπ : π ≫ p = q) (hsurj : Function.Surjective π) (L : HermLB p)
    (r : ℕ) [Fact r.Prime]
    (hL : ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod r) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod r) ((L.pull π hπ).B.pull i) 1) :
    ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod r) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
  intro Z i _ _ _ hd
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hq).1
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : Surjective π := ⟨hsurj⟩
  have : IsNoetherian Y := isNoetherian_of_isProjOver hq
  have : IsNoetherian X := isNoetherian_of_isProjOver hp
  have : IsNoetherian Z := by
    have := LocallyOfFiniteType.isLocallyNoetherian i
    have := QuasiCompact.compactSpace_of_compactSpace i
    exact {}
  let g := pullback.snd π i
  have : IsProper g := inferInstance
  have : Surjective g := inferInstance
  obtain ⟨w, hw, hdeg⟩ := GlobalTheory.NefDescent.fibre_point _ Z g (genericPoint Z) (g.surjective _)
  let C : Closeds (pullback π i : Scheme.{0}) := ⟨closure {w}, isClosed_closure⟩
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  have hgen := GlobalTheory.NefDescent.red_genericPoint _ w C rfl
  let f := redι C ≫ g
  let i' := redι C ≫ pullback.fst π i
  have hη : f (genericPoint _) = genericPoint Z := by
    simp only [f, Scheme.Hom.comp_apply, hgen, hw]
  have hdeg' : 0 < f.residueDegree (genericPoint _) := by
    simp only [f, CurveDegreesCompare.residueDegree_comp, hgen, GlobalTheory.Published.residueDegree_of_isClosedImmersion, mul_one]
    exact hdeg
  have hd' := GlobalTheory.NefDescent.dim_eq_one _ Z f hd hη hdeg'
  have : IsNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    have := LocallyOfFiniteType.isLocallyNoetherian i'
    have := QuasiCompact.compactSpace_of_compactSpace i'
    exact {}
  have : IsFinite f := GlobalTheory.NefDescent.isFinite_of_dim _ Z f hd' hd hη
  letI : Algebra (ZMod r) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) := algebraΓAlong (ZMod r) f
  have h1 := hL _ i' hd'
  have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
  have hcomm : i' ≫ π = f ≫ i := by simp only [i', f, g, Category.assoc, pullback.condition]
  have e1 : topSelfIntersection (ZMod r) ((L.pull π hπ).B.pull i') 1 = topSelfIntersection (ZMod r) ((L.B.pull i).pull f) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod r) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB π) i')
      (fun _ => LB.isLB_pull hN f) fun _ => ?_
    show pull i' (pull π (cls L.B L.isLB)) = pull f (pull i (cls L.B L.isLB))
    rw [← pull_comp, ← pull_comp, hcomm]
  have e2 : topSelfIntersection (ZMod r) ((L.B.pull i).pull f) 1 = interNumOn (ZMod r) f (fun _ : Fin 1 => L.B.pull i) :=
    (interNumOn_const_eq_topSelf (k := ZMod r) (fun _ => rfl) hN 1).symm
  have e3 : interNumOn (ZMod r) f (fun _ : Fin 1 => L.B.pull i) = interNumOn (ZMod r) f ![L.B.pull i] :=
    congrArg _ (funext fun j => by fin_cases j; rfl)
  have hproj : IsProjOver (strHom (ZMod r) Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod r) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod r)))
    exact ProperCurve.isProjOver_of_isProper _ hd
  have e4 := GlobalTheory.T.intersection_number_finite_pushforward (ZMod r) Z _ f hproj hd hη (L.B.pull i) hN
  have e5 : interNum (ZMod r) (structureModule Z) ![L.B.pull i] = topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
    rw [topSelf_def]
    exact congrArg _ (funext fun j => by fin_cases j; rfl)
  have hT : 0 ≤ (f.residueDegree (genericPoint _) : ℤ) * topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
    rw [← e5, ← e4, ← e3, ← e2, ← e1]
    exact h1
  exact nonneg_of_mul_nonneg_right hT (by exact_mod_cast hdeg')

end GlobalTheory.NefDeRhamAt
end
end

