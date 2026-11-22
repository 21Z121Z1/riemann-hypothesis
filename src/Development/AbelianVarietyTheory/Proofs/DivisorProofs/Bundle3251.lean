import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3238
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3231
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3222
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeSubmoduleStable
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem eq_zero_of_cuspA_bot {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (j : Fin D.R.m)
    (hc : T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥) (x : Fin (R.nW j) → D.what₂.LL) : x = 0 := by
  obtain ⟨n, b, hb, -, -, -, hsp⟩ := fw.ks j
  have hWK : ∀ z ∈ (R.FW j).WK, z = 0 := fun z hz => by
    obtain ⟨f, hf⟩ := (fw.e j).surjective ⟨z, hz⟩
    have hf0 : f = 0 := by
      have h1 : (f : T.R ((j : ℕ) + 1)) ∈ (⊥ : Submodule T.Q.c.F (T.R ((j : ℕ) + 1))) := hc ▸ f.2
      exact Subtype.ext ((Submodule.mem_bot _).1 h1)
    have := congrArg Subtype.val hf
    rw [hf0, map_zero] at this
    exact this.symm
  have h0 : Set.range b ⊆ {0} := by
    rintro _ ⟨k, rfl⟩; exact hWK _ (hb k)
  have : x ∈ Submodule.span D.what₂.LL (Set.range b) := by rw [hsp]; trivial
  have h2 := Submodule.span_mono h0 this
  simpa using h2

theorem adForm_smul {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (c : D.what₂.LL) (x : Fin (R.nW i) → D.what₂.LL) : adForm R i (c • x) = sg0 D A c • adForm R i x := by
  unfold adForm
  rw [LinearMap.map_smulₛₗ, map_smul]

theorem adForm_zero {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    adForm R i 0 = 0 := by
  unfold adForm
  rw [map_zero, map_zero]

theorem kerRat_framed (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    {O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)} {t : D.ntw.Tw} {j : Fin D.R.m}
    {hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j} (hH : RatHyp T Rl F κ v₀ O t j hV) (hph : ∀ k, Rl.phs k = 1)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) {χ ξR ω φ}
    (hK : KerDat Rl.toRealDat j (Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver Rl.toRealDat (Rl.mu v) (ownAt D v)) ω φ)
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) {y : (Rl.cV j).W} (hy : InCoefLat Rl.toRealDat j h y)
    (u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ) (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j (sg0 D A3.A) τ) :
    ∃ x, adForm Rl.toRealDat j x (fun τ => u τ) = singleSeries Rl.toRealDat j ω φ h y u := by
  obtain ⟨gramR, c0R, c0L, hFT, P, hPm, rfl⟩ := hy
  obtain ⟨ph, hph1, hphC⟩ := hS D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hH.laws hH.core.lev hH.core.grp hH.core.fam
    hH.core.models hH.core.thP hH.tieIn j hV hH.frame hH.std gramR c0R c0L hFT u hu
  have hRP : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph := fun C hC _ => hphC C hC
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_adelicForm_eq_rationalPhase_kernelSeries hP hA hR D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O t j hV hH gramR c0R c0L hFT u hu ph hRP v χ ξR ω φ hK
    h hh P hPm
  have hph0 : ph ≠ 0 := fun e => by rw [e, norm_zero] at hph1; exact zero_ne_one hph1
  by_cases hc : T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥
  · refine ⟨0, ?_⟩
    rw [eq_zero_of_cuspA_bot hH.fw.some j hc x, adForm_zero] at hx
    rw [adForm_zero]
    funext g
    have e := congrFun hx.symm g
    have e2 : ph * singleSeries Rl.toRealDat j ω φ h (c0L j P) u g = 0 := e
    exact ((mul_eq_zero.1 e2).resolve_left hph0).symm
  · obtain ⟨c, hcph⟩ := GlobalTheory.T.unit_modulus_rational_phase_mem_coefficient_field hP hA hR D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O t j hV hH gramR c0R c0L hFT u hu hph hc ph
      hph1 hRP
    refine ⟨c⁻¹ • x, ?_⟩
    rw [adForm_smul]
    funext g
    have e := congrFun hx g
    have e2 : adForm Rl.toRealDat j x (fun τ => u τ) g = ph * singleSeries Rl.toRealDat j ω φ h (c0L j P) u g := e
    show sg0 D A3.A c⁻¹ * adForm Rl.toRealDat j x (fun τ => u τ) g = _
    rw [e2, map_inv₀, hcph, ← mul_assoc, inv_mul_cancel₀ hph0, one_mul]

open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt in

theorem kerRatAt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → KerRatAt := by
  intro hP hA hR hS
  refine (lowAt_holds.and twAdm).imp fun Fm x hx i p hp hM w hw j hLT => ?_
  obtain ⟨l1, l2⟩ := hLT
  have h0 := GlobalTheory.T.bad_prime_mem_exceptional_set Fm x hx i p hp hM _ l2.2.2 l1 j
  obtain ⟨c', w', hw', hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (GlobalTheory.T.rational_hypothesis_in_half_geometry hP Fm x hx i p hp hM _ j h0)
  obtain ⟨S', YS', -⟩ := GlobalTheory.T.seriesRationality_back_from_movedReadings p.R p.cG p.Sx p.nexp w' hw'
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w').toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w' hw' h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w').toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w').phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w') (F2 p) B'.κ B'.v₀ B'.O ((Fm.ex x hx i).nch.twI w) j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  intro χ ξR ω φ hK h hh y hy u hu
  have hK' : KerDat (fullHeckeRealDatMovedReadings p.R w').toRealDat j ((fullHeckeRealDatMovedReadings p.R w').C.delAt (Formalism.EigenvalueLevelCeiling.plc ((Fm.D x i).plEq w))) χ ξR
      (placesOver (fullHeckeRealDatMovedReadings p.R w').toRealDat ((fullHeckeRealDatMovedReadings p.R w').mu ((Fm.D x i).plEq w)) (ownAt (Fm.D x i) ((Fm.D x i).plEq w)))
      ω φ := ⟨hK.chr, hK.fin, hK.triv, hK.tame, hK.pl, hK.off, hK.ram, hK.res, hK.weil, hK.vec⟩
  have hy' : InCoefLat (fullHeckeRealDatMovedReadings p.R w').toRealDat j h y := hy
  obtain ⟨x', hx'⟩ := kerRat_framed (T := setCE p.T c') hP hA hR hS YS' hRat (fun k => p.phsOne k) ((Fm.D x i).plEq w) hK' hh
    hy' u (by rw [hv]; exact hu)
  exact ⟨(p.R.FW j).ρ (w' j (sg0 _ p.P.A3.A)) x', hx'⟩

end GlobalTheory.BigOn.Exp.SerBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLift

theorem psiQ : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (q : u.D.toPre.X → ℝ), (∀ χ, u.PsiNorm χ (Real.exp (-q χ))) → ∀ χ, l.q χ = q χ := by
  intro o Ω _ _ _ S ρ p _ y₀ u l q hq χ
  have := GlobalTheory.ZH.RealCase.psiNorm_unique u χ (l.q_eq χ) (hq χ)
  exact neg_injective (Real.exp_injective this)

theorem labels_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy ∧ D.Compat yy₁ yy := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ c yy₁ hLab y h
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', hS, hi, hR, y₀, hy₀, u, l, j, hq, hyy, hmat⟩ := hLab
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hS₂, hi₂, hR₂, y₂, hy₂, hint₂⟩ :=
    GlobalTheory.T.thetaSetup_rescale_into_localRing_classicalTrait g n F W Z i D.X hg hn hodd himm he8 hth D.proj D.ε D.diag p (y (cPt p)) (D.lift c y h)
  obtain ⟨u₂, e, T, hpsi, htor, heps, hfw, hbw⟩ := GlobalTheory.T.uniformisedModel_transport_deeperThetaSetup g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h
    c₀ hc R' fg frac hth' hev ρ' ε' hS hi hR y₀ hy₀ u c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS₂ hi₂ hR₂ y₂ hy₂
  obtain ⟨l₂⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed _ _ _ ρ₂ p y₂ u₂ hint₂
  set L₂ : ℕ := D.X.S.r * D.X.S.N with hL₂
  set L₁ : ℕ := X₁.S.r * X₁.S.N with hL₁
  let jj : u₂.D.toPre.X ≃+ (Fin 8 → c.T.D.toPre.X) := e.trans j
  have hrange : (nsmulAddMonoidHom L₂ : u₂.D.toPre.X →+ u₂.D.toPre.X).range ≤
      ((nsmulAddMonoidHom L₂ : (Fin 8 → c.T.D.toPre.X) →+ (Fin 8 → c.T.D.toPre.X)).range).comap jj.toAddMonoidHom := by
    rintro _ ⟨z, rfl⟩
    exact ⟨jj z, by simp⟩
  let f := QuotientAddGroup.map _ _ jj.toAddMonoidHom hrange
  have hf : ∀ χ, f (QuotientAddGroup.mk χ) = QuotientAddGroup.mk (jj χ) := fun χ => rfl
  refine ⟨f.comp l₂.yy, ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hS₂, hi₂, hR₂, y₂, hy₂, u₂, l₂, jj, ?_, ?_, ?_⟩, ?_⟩
  · intro χ
    rw [GlobalTheory.Poinc.GLift.psiQ _ _ _ ρ₂ p y₂ u₂ l₂ (fun χ => l.q (e χ)) (fun χ => hpsi χ _ (l.q_eq (e χ))) χ]
    exact hq (e χ)
  · intro a χ ha
    simp only [AddMonoidHom.comp_apply, ha]
    rfl
  · intro m pk pk' x x' E hm hx hx' hxx
    obtain ⟨q₁, hq₁y, hq₁⟩ := hfw m pk x hm hx
    obtain ⟨q₁', hq₁y', hq₁'⟩ := hfw m pk' x' hm hx'
    have := hmat m q₁ q₁' (T x) (T x') E hm hq₁ hq₁' (heps x x' E hxx)
    rw [hq₁y, hq₁y'] at this
    exact this
  · intro a μ hμ
    obtain ⟨pk, x, hx, hxa⟩ := GlobalTheory.T.exists_thetaTorsion_preimage_uniformised_model _ _ _ ρ' p y₀ u a
    have h1 := l.yy_eq a pk x hx hxa
    have h2 := hyy a pk.y h1
    have hL₁pos : 1 ≤ L₁ := by
      obtain ⟨jr, hjr, hr⟩ := X₁.ρ.r_eq
      have h1' : 0 < X₁.S.r := by rw [hr]; exact pow_pos X₁.ρ.n_prime.pos _
      have h2' : 0 < X₁.S.N := by rw [X₁.ρ.N_eq]; exact pow_pos (pow_pos X₁.ρ.n_prime.pos _) _
      exact Nat.mul_pos h1' h2'
    have hdvd : L₁ ∣ L₂ := by
      obtain ⟨t, ht⟩ := D.dvd
      refine ⟨t * (D.m * D.X.S.r), ?_⟩
      rw [hL₂, D.sq, ht]; ring
    have hL₂pos : 1 ≤ L₂ := by
      obtain ⟨jr, hjr, hr⟩ := D.X.ρ.r_eq
      have h1' : 0 < D.X.S.r := by rw [hr]; exact pow_pos D.X.ρ.n_prime.pos _
      have h2' : 0 < D.X.S.N := by rw [D.X.ρ.N_eq]; exact pow_pos (pow_pos D.X.ρ.n_prime.pos _) _
      exact Nat.mul_pos h1' h2'
    have hdpos : 1 ≤ L₂ / L₁ := by
      rw [Nat.one_le_div_iff (by omega)]
      exact Nat.le_of_dvd (by omega) hdvd
    obtain ⟨pk', hpk'y, hpk'⟩ := GlobalTheory.T.exists_levelPoint_rescale_same_torsionPoint _ _ _ ρ' p y₀ u L₁ L₂ (L₂ / L₁) pk x hL₁pos hdpos
      (Nat.div_mul_cancel hdvd).symm hx
    obtain ⟨pk₂, hpk₂y, hpk₂⟩ := hbw L₂ pk' x hL₂pos hpk'
    have h3 := (htor (T.symm x) a).2 (by simpa using hxa)
    have h4 := l₂.yy_eq (D.lab a) pk₂ (T.symm x) hpk₂ h3
    show f (l₂.yy (D.lab a)) = _
    rw [h4, hf]
    have h5 : jj pk₂.y = (L₂ / L₁) • j pk.y := by
      show j (e pk₂.y) = _
      rw [hpk₂y, hpk'y, map_nsmul]
    rw [h5]
    rw [hμ] at h2
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq).1 h2.symm
    apply (QuotientAddGroup.eq).2
    refine ⟨z, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← smul_neg, ← smul_add, ← hz, smul_smul, Nat.div_mul_cancel hdvd]

end GlobalTheory.Poinc.GLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitAbsoluteValueCriterionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unit_absolute_value_criterion : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) [Fact (resP v).Prime] (k : ℕ) (gn : Fin k → ℝ), (∀ l, 0 < gn l) → ∀ b : AlgebraicClosure F, (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) ≤ 1 ↔ ‖ioOf (resP v) ε b‖ ≤ ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) = 1 ↔ ‖ioOf (resP v) ε b‖ = ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) < 1 ↔ ‖ioOf (resP v) ε b‖ < ∏ l, gn l) := by
  first | exact @GlobalTheory.ShFam.Pad.w_mul_exp_cmp_iff | exact GlobalTheory.ShFam.Pad.w_mul_exp_cmp_iff | (intros; apply GlobalTheory.ShFam.Pad.w_mul_exp_cmp_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralOfRegularAtAllTraitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyIntegral_of_regular_at_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (k : ℕ) (s : SecK L α k), TraitReg M G L s → LocInt M G L α t hpb.w s := by
  first | exact @GlobalTheory.Mum.locInt_of_traitReg | exact GlobalTheory.Mum.locInt_of_traitReg | (intros; apply GlobalTheory.Mum.locInt_of_traitReg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyOfRegAfOfFixL
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem GlobalTheory.LKCx.minpoly_of_regAf_of_fixL : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h : G.GAf) (z : PosV G v β), FixL G v β y z.1 → RegAf G (h⁻¹ * toAfF G β x t hx y * h) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
  intro p _ G v hv β hβ hR x t hx y h z hfix hreg
  have hcomm : ∀ a b : G.C, Commute a (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) →
      Commute b (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) → Commute a b := by
    obtain ⟨w, hw⟩ := hreg
    obtain ⟨U, hU⟩ := ubc_val_eq G β x t hx y h w
    rw [hU] at hw
    intro a b ha hb
    let ι : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C := Algebra.TensorProduct.includeRight
    have hinj : Function.Injective ι :=
      Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (w.1.adicCompletion ℚ)).injective
    have e : ι (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
        (1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := rfl
    have ha' := ha.map ι
    have hb' := hb.map ι
    rw [e] at ha' hb'
    have hab := comm_of_conj U _ hw (ι a) (ι b) ha' hb'
    exact hinj (by rw [map_mul, map_mul]; exact hab.eq)
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G v β y
  have hs : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast y.2.2
  obtain ⟨c0, hc0⟩ := hfix
  obtain ⟨H, hH, hHM⟩ := GlobalTheory.T.similitude_signature_one_preserves_posDef_form G.n (G.gram v) (herm G v β) (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm v) Z _ (G.gram_det v) hv hZ hs (by rw [Complex.ofReal_ratCast]; exact hsim) z.1 c0 z.2 hc0
  have hsq := GlobalTheory.T.aeval_eq_zero_of_sq_eq_zero_of_posDef_similitude G.n H _ _ hH hs hHM
  have hsep := GlobalTheory.T.minpoly_separable_of_no_sq_zero_polynomial_image G.F G.C G.n v.embedding (G.psi v) G.n_pos (G.psi_F v) _ hsq
  exact ⟨GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser G.F G.C G.n G.rankC _ hsep hcomm, hsep⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAddOfDensityAdd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem GlobalTheory.Mix.part_le_add_of_dens_add {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L₁ L₂ L₃ : Fin D → MLine p σ)
    (h : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, dens L₁ c y = dens L₂ c y + dens L₃ c y) (ε : ℤˣ) :
    part L₁ ε ≤ part L₂ ε + part L₃ ε := by
  unfold part glueMeas
  refine iSup_le fun c => ?_
  refine le_trans ?_ (add_le_add
    (le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L₂ c y)) c)
    (le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L₃ c y)) c))
  refine Measure.le_iff.2 fun A hA => ?_
  have hB : MeasurableSet (c.e.source ∩ A) := c.e.open_source.measurableSet.inter hA
  have hI := GlobalTheory.ChartGlue.measurableSet_image c.e hB inter_subset_left
  have hsub : c.e '' (c.e.source ∩ A) ⊆ c.e.target := fun _ ⟨y, hy, e⟩ => e ▸ c.e.map_source hy.1
  have hcont : ContinuousOn (fun v => dens L₂ c (c.e.symm v)) c.e.target :=
    (GlobalTheory.T.continuousOn_mixedChernFormDensityInChart k X p σ D L₂ c).comp c.e.continuousOn_symm c.e.mapsTo_symm
  have hm : AEMeasurable (fun v => ENNReal.ofReal (((ε : ℤ) : ℝ) * dens L₂ c (c.e.symm v)))
      (volume.restrict (c.e '' (c.e.source ∩ A))) :=
    (((hcont.aemeasurable c.e.open_target.measurableSet).const_mul _).ennreal_ofReal).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  rw [Measure.add_apply, chartMeas_apply _ _ hA, chartMeas_apply _ _ hA, chartMeas_apply _ _ hA,
    ← lintegral_add_left' hm]
  refine setLIntegral_mono' hI fun v hv => ?_
  beta_reduce
  rw [h c _ (c.e.map_target (hsub hv)), mul_add]
  exact ENNReal.ofReal_add_le

theorem GlobalTheory.Mix.int_add_of_dens_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L₁ L₂ L₃ : Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, dens L₁ c y = dens L₂ c y + dens L₃ c y) → ∀ f : CxPts p σ → ℝ, (Intg L₂ f → Intg L₃ f → Intg L₁ f) ∧ (Intg L₁ f → Intg L₂ f → Intg L₃ f → Mix.int L₁ f = Mix.int L₂ f + Mix.int L₃ f) := by
  intro k _ X p σ _ D L₁ L₂ L₃ h f
  refine ⟨fun h₂ h₃ => ⟨(h₂.1.add_measure h₃.1).mono_measure (GlobalTheory.Mix.part_le_add_of_dens_add L₁ L₂ L₃ h 1),
    (h₂.2.add_measure h₃.2).mono_measure (GlobalTheory.Mix.part_le_add_of_dens_add L₁ L₂ L₃ h (-1))⟩, fun h₁ h₂ h₃ => ?_⟩
  have := GlobalTheory.T.linear_relation_mixed_densities_integrals k X p σ D (Fin 3) ![1, -1, -1] ![L₁, L₂, L₃]
    (fun c y hy => by
      rw [Fin.sum_univ_three]
      show 1 * dens L₁ c y + -1 * dens L₂ c y + -1 * dens L₃ c y = 0
      rw [h c y hy]; ring) f
    (fun i => by
      fin_cases i
      · exact h₁
      · exact h₂
      · exact h₃)
  rw [Fin.sum_univ_three] at this
  change 1 * Mix.int L₁ f + -1 * Mix.int L₂ f + -1 * Mix.int L₃ f = 0 at this
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductiveRhsSymmIsometryInvariantStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ T, IsMix q e T → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ L L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → recVal (T e L) L M hr = recVal (T e L') L' M hr) ∧ (∀ (L : Fin e → HermLB q) (τ : Equiv.Perm (Fin e)), recVal (T e fun a => L (τ a)) (fun a => L (τ a)) M hr = recVal (T e L) L M hr) ∧ (∀ (L : Fin e → HermLB q) (M' : HermLB q), M.Isometric M' → ∃ (r' : M'.B.ι → Y.functionFieldˣ) (hr' : IsRatSec M'.B r'), recVal (T e L) L M' hr' = recVal (T e L) L M hr) := by
  first | exact @GlobalTheory.MixHt.recVal_iso_symm | exact GlobalTheory.MixHt.recVal_iso_symm | (intros; apply GlobalTheory.MixHt.recVal_iso_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightUniqueRestrictClosedSubschemeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → ∀ (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (m m' : ℕ) T T', IsMix p m T → IsMix q m' T' → ∀ d : ℕ, d ≤ m → d ≤ m' → ∀ (L : Fin d → HermLB p) (L' : Fin d → HermLB q), (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ y : Y, HasDim y d → T d L (i y) = T' d L' y := by
  first | exact @GlobalTheory.MixHt.eq_of_isMix | exact GlobalTheory.MixHt.eq_of_isMix | (intros; apply GlobalTheory.MixHt.eq_of_isMix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFiniteStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedIntegral_pullback_genericallyFinite : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → (Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) = π.residueDegree (genericPoint Y) * Mix.int L f := by
  first | exact @GlobalTheory.PushInt.mixInt_pull | exact GlobalTheory.PushInt.mixInt_pull | (intros; apply GlobalTheory.PushInt.mixInt_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplierPowerMulPullbackSmallFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.ZmPow

theorem pow_mul_small : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N k : ℕ) (g : ∀ β, SecT D.toPre a N (-1) β) (ρ : ∀ β, SecT D.toPre a 0 k β), Small (maximalIdeal R) (w := id) g → Small (maximalIdeal R) (w := id) ρ → TFE h h' g → TFE h h' ρ → ∃ F : ∀ β, SecT D.toPre a ((N * k : ℕ) : ℤ) 0 β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k), TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ → ∃ τ'' : SecE U.toUnifPre (b e) ((N * k : ℕ) : ℤ) 0, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ k * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  intro R _ _ _ hAdm D a a' h h' hE A G _ _ hG U b hb N k g ρ hgS hρS hgT hρT
  have key : ∀ m : ℕ, ∀ n j : ℤ, n = (N : ℤ) * m → j = (k : ℤ) - m →
      ∃ F : ∀ β, SecT D.toPre a n j β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧
        ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k),
          TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ →
          ∃ τ'' : SecE U.toUnifPre (b e) n j,
            (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'),
              Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ m * sval τ' x z J') ∧
            TExp U.toUnifPre τ'' (w := id) F := by
    intro m
    induction m with
    | zero =>
      intro n j hn hj
      have hn' : n = 0 := by simp [hn]
      have hj' : j = (k : ℤ) := by simp [hj]
      subst hn' hj'
      refine ⟨ρ, hρS, hρT, fun e τ τ' _ hτ' => ⟨τ', fun Z x z J' _ => by simp, hτ'⟩⟩
    | succ m ih =>
      intro n j hn hj
      obtain ⟨Fm, hFS, hFT, hFm⟩ := ih ((N : ℤ) * m) ((k : ℤ) - m) rfl rfl
      obtain ⟨F, hS, hT, hP⟩ := GlobalTheory.T.exists_product_small_twistedFunctionalEqn_family R hAdm D a a' h h' hE A G hG U b hb
        (N : ℤ) (-1) ((N : ℤ) * m) ((k : ℤ) - m) n j (by rw [hn]; push_cast; ring)
        (by rw [hj]; push_cast; ring) g Fm hgS hFS hgT hFT
      refine ⟨F, hS, hT, fun e τ τ' hτ hτ' => ?_⟩
      obtain ⟨τm, hτmv, hτmE⟩ := hFm e τ τ' hτ hτ'
      obtain ⟨τ'', hv, hE''⟩ := hP e τ τm hτ hτmE
      refine ⟨τ'', fun Z x z J' hJ => ?_, hE''⟩
      rw [hv Z x z J' hJ, hτmv Z x z J' hJ]
      ring
  exact key k _ _ (by push_cast; ring) (by simp)

end GlobalTheory.ZmPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMapStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], (∀ (τ : Type) [Finite τ] (φ : MvPowerSeries τ k →ₐ[k] A), (∀ t, IsNilpotent (φ (X t))) → ∀ a : σ → MvPowerSeries τ k, (∀ i, constantCoeff (a i) = 0) → ∀ (y : σ → A) (hy : ∀ i, IsNilpotent (y i)), (∀ i, φ (a i) = y i) → ∀ f : MvPowerSeries σ k, φ (subst a f) = evA k y hy f) ∧ ∀ (B : Type) [CommRing B] [Algebra k B] (g : A →ₐ[k] B) (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : σ → B) (hy : ∀ i, IsNilpotent (y i)), (∀ i, g (x i) = y i) → ∀ f : MvPowerSeries σ k, g (evA k x hx f) = evA k y hy f := by
  first | exact @GlobalTheory.evA_subst_and_map | exact GlobalTheory.evA_subst_and_map | (intros; apply GlobalTheory.evA_subst_and_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelFamilyOfDivisorLevelSamePrimes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLev

theorem sFam_down : ∀ h n N : ℕ, 3 ≤ n → Odd N → n ∣ N → (∃ a, N ∣ n ^ a) → Nonempty (SFam h N (zetaAway N)) →
    Nonempty (SFam h n (zetaAway n)) := by
  intro h n N hn hN hnN hpow ⟨F⟩
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN)
  obtain ⟨j, hinj, hζ, hfes⟩ := GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale n N hN0 hnN
  obtain ⟨hfin, het, hsurj⟩ := hfes hpow
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_siegelLevelLoweringQuotientFamily h n N F j hn hN hnN hζ hfin het
  exact ⟨{
    X := Q.X
    s := Q.s
    smooth := Q.smooth
    qproj := Q.qproj
    univ := Q.univ
    princ := Q.princ
    rep := fun S s' c hred hdense hpr =>
      GlobalTheory.T.siegelLevelLoweringQuotient_represents_reduced h n N F j Q hn hN hnN hinj hζ hfin het hsurj S s' c hred hdense hpr
    inj := fun R _ _ x y s' c hs h₁ h₂ =>
      GlobalTheory.T.siegelQuotientFamily_local_points_eq_of_object h n N _ _ (zetaAway n) (zetaAway N) F j Q R x y s' c hs h₁ h₂ }⟩

end GlobalTheory.SiegLev
end

