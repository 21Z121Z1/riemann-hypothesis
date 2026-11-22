import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3498
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3499
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionDescendedSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DescLBExt

theorem exists_lb_extension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ M : LB G.left, M.IsLB ∧ LBIso (M.pull e) tF.PP.L := by
  intro E _ _ _ H Dw l Xo c φ h1 h2 h3 Z zs i OZ N d J S π j _ BD hU hpre tF hmap G _ _ e hsa he hch
  have hU' := hU
  obtain ⟨⟨-, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU'
  have := hsa.smooth
  have := hsa.geomConnected
  have := hsa.quasiCompact
  have := hsa.separated
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  haveI := GlobalTheory.IsNormalScheme.of_pred hS
  have hst := GlobalTheory.T.exists_lineBundle_extension_at_boundaryPoint Xo c φ h1 h2 h3 zs i OZ N d J π j BD hU hpre tF hmap G e hsa he hch
  exact GlobalTheory.T.exists_rigidifiedLineBundle_extension_of_local G.hom j hdense e tF.G.hom he.1 (eSec G) (eSec tF.G) (Over.w η[G]) (cubeMapOf he).e_comm
    tF.PP.L tF.PP.isLB tF.PP.rig tF.PP.rigGen fun x hx => by
      obtain ⟨Nx, hNx, hx'⟩ := hst x hx
      exact GlobalTheory.T.exists_lineBundle_spread_from_localScheme G.hom j e tF.G.hom he.1 tF.PP.L tF.PP.isLB x Nx hNx hx'

end GlobalTheory.DescLBExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LBObs.exists_lift_of_lam_iso_pull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left) (L₀ : LB B₀.left), P.IsLB → L₀.IsLB → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → ∃ L : LB B.left, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ _ π hπ hI B _ B₀ _ _ i i₂ hB hgp hsq P L₀ hP hL₀ hΛ
  have hab : IsAbelianScheme B₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hgp
  obtain ⟨g, hdim⟩ := GlobalTheory.AbelianDim.exists_relDim R₀ B₀ hab
  have hsm : Smooth B.hom := hB.smooth
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.Obs.exists_aug R R₀ (RingHom.ker π) hI π hπ rfl
  have hpb : IsPullback i B₀.hom B.hom (spMap π) := hgp.1
  obtain ⟨S, ⟨Pr⟩⟩ := GlobalTheory.LiftSys.exists_sys_presents R R₀ (RingHom.ker π) hI π hπ rfl B₀.left B₀.hom B.left B.hom i hpb hsm
  obtain ⟨k, hkp, hkμ, hkf, hks⟩ := GlobalTheory.T.exists_square_group_scheme_pullback (Sp R) (Sp R₀) (spMap π) B B₀ i hgp
  have hki : i₂ = k := (GlobalTheory.SqPull.tensor_isPullback B B).hom_ext (hsq.1.trans hkf.symm) (hsq.2.trans hks.symm)
  subst hki
  have hsm2 : Smooth (B ⊗ B).hom := inferInstanceAs (Smooth (Limits.pullback.fst B.hom B.hom ≫ B.hom))
  obtain ⟨S₂, ⟨P₂⟩⟩ := GlobalTheory.LiftSys.exists_sys_presents R R₀ (RingHom.ker π) hI π hπ rfl (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom (B ⊗ B).left
    (B ⊗ B).hom i₂ hkp hsm2
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α B₀.left B₀.hom S L₀ hL₀
  have h1 : (L₀.pull (fst B₀ B₀).left).IsLB := pull_isLB hL₀ _
  have h2 : (L₀.pull (snd B₀ B₀).left).IsLB := pull_isLB hL₀ _
  have h3 : (P.pull i₂).IsLB := pull_isLB hP _
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ h1
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ h2
  have hc₃ : IsObL S₂ α (P.pull i₂) 0 :=
    GlobalTheory.T.lineBundle_obstruction_zero_of_restriction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ (B ⊗ B).left (B ⊗ B).hom i₂ P₂ P hkp hP
  have hc₁₂ := GlobalTheory.T.lineBundleLiftObstruction_tensor_additive R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ _ c₁ c₂ hc₁ hc₂
  have hc₁₂₃ := GlobalTheory.T.lineBundleLiftObstruction_tensor_additive R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ _ _ _ hc₁₂ hc₃
  rw [add_zero] at hc₁₂₃

  have hz : GlobalTheory.CechPic.pull (1 : B₀ ⊗ B₀ ⟶ B₀).left (cls L₀ hL₀) = 0 := by
    rw [Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp]
    have h0 : cls (L₀.pull (η[B₀]).left) (pull_isLB hL₀ _) = 0 :=
      (cls_eq_zero_iff _).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R₀) (pull_isLB hL₀ _))
    rw [← cls_pull hL₀ _ (pull_isLB hL₀ _), h0, map_zero]
  have hmul : (fst B₀ B₀ * snd B₀ B₀ : B₀ ⊗ B₀ ⟶ B₀) = μ[B₀] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hLam : (abelian₂ B₀ L₀).IsLB := LB.isLB_linComb hL₀ _ _
  have hcube : cls (abelian₂ B₀ L₀) hLam = lam (cls L₀ hL₀) (fst B₀ B₀) (snd B₀ B₀) :=
    GlobalTheory.CechPic.cls_cube_two hL₀ (fst B₀ B₀) (snd B₀ B₀) hLam
  have hΛc : cls _ hLam = cls _ h3 := (cls_eq_iff hLam h3).2 hΛ
  have hiso : LBIso (tens (tens (L₀.pull (fst B₀ B₀).left) (L₀.pull (snd B₀ B₀).left)) (P.pull i₂))
      (L₀.pull (μ[B₀]).left) := by
    refine (cls_eq_iff (isLB_tens (isLB_tens h1 h2) h3) (pull_isLB hL₀ _)).1 ?_
    rw [cls_tens (isLB_tens h1 h2) h3, cls_tens h1 h2, ← hΛc, hcube, lam, hmul, hz, cls_pull hL₀, cls_pull hL₀,
      cls_pull hL₀]
    abel
  have hpb2 : IsPullback i₂ (B₀ ⊗ B₀).hom (B ⊗ B).hom (spMap π) := hkp
  have nat : ∀ (f₀ : (B₀ ⊗ B₀) ⟶ B₀) (f : (B ⊗ B) ⟶ B), i₂ ≫ f.left = f₀.left ≫ i →
      ∀ (L' : LB (B₀ ⊗ B₀).left) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff (B₀ ⊗ B₀).hom))), L'.IsLB →
        LBIso L' (L₀.pull f₀.left) → IsObL S₂ α L' c' → IsExtendedPullbackDegTwo R₁ (overW f₀) c c' := by
    intro f₀ f hf L' c' hL' hiso hob
    obtain ⟨l, hl, hn⟩ := GlobalTheory.Obs.exists_chart_lifts R R₀ _ hI π hπ rfl B₀.left (B₀ ⊗ B₀).left B.left (B ⊗ B).left
      B₀.hom (B₀ ⊗ B₀).hom B.hom (B ⊗ B).hom i i₂ hpb hkp S S₂ Pr P₂ f₀.left (overW f₀) f.left (Over.w f) hf
    exact GlobalTheory.T.lineBundleLiftObstruction_natural R R₀ _ hI π hπ rfl R₁ α B₀.left (B₀ ⊗ B₀).left B₀.hom (B₀ ⊗ B₀).hom S S₂ f₀.left (overW f₀)
      l hl hn L₀ L' c c' hL₀ hL' hiso hc hob
  have eμ := nat μ[B₀] μ[B] hkμ _ (c₁ + c₂) (isLB_tens (isLB_tens h1 h2) h3) hiso hc₁₂₃
  have e1 := nat (fst B₀ B₀) (fst B B) hkf _ c₁ h1 (GlobalTheory.PolBaseChange.lbIso_refl h1) hc₁
  have e2 := nat (snd B₀ B₀) (snd B B) hks _ c₂ h2 (GlobalTheory.PolBaseChange.lbIso_refl h2) hc₂
  have h0 : c = 0 := GlobalTheory.T.primitive_degree_two_any_ring R₀ R₁ α.q α.sq B₀ g hab hdim c c₁ c₂ eμ e1 e2
  subst h0
  exact GlobalTheory.T.exists_lineBundleLift_of_obstruction_zero R R₀ _ hI π hπ rfl R₁ α B₀.left B₀.hom S B.left B.hom i Pr L₀ hpb hL₀ hc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionOppositeCongrModStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_section_opposite_congr_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ σ : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') ∧ (∀ b ∈ Z', σ b = b) ∧ (∀ a, ∃ e, y (σ a) = y a + n • e) ∧
      ∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e := by
  first | exact @GlobalTheory.LowFilt.exists_cell_section | exact GlobalTheory.LowFilt.exists_cell_section | (intros; apply GlobalTheory.LowFilt.exists_cell_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPullbackLocalMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearUniformisation_pullback_localMap : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (θ : R →+* V), IsLocalHom θ → ∀ f : R, θ f ≠ 0 → (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg θ P.D.toPre P'.D.toPre), Nonempty (SABMap t' t (spMap θ)) ∧ (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧ (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (P.oD.onB.act x)) := by
  first | exact @GlobalTheory.LocalPull.exists_pelUnif_pull | exact GlobalTheory.LocalPull.exists_pelUnif_pull | (intros; apply GlobalTheory.LocalPull.exists_pelUnif_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspForm
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.LowNonzero

theorem gapGe_wt_add_parWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (P : WtPar Dw) (hB : WtBig P) (j : ℕ) (w : Psi H → ℤ) :
    GapGe (((FlagTan.dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (P.wt j + GlobalTheory.FlatLine.parWt Dw w - FlagTan.kap Dw) := by
  intro τ k hk
  have a := (gaps_of_wtBig _ _ _ P hB P.u₁ (by simp)).1 τ k hk
  have hg := hB.gaps τ k hk
  have b := (P.gap_rem τ k).1
  have c : gap (GlobalTheory.FlatLine.parWt Dw w τ) k = 0 := by
    simp [gap, GlobalTheory.FlatLine.parWt]
  have hC0 : (0 : ℤ) ≤ (((FlagTan.dimFlag Dw + 1).choose 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hD0 : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ (Dw.p : ℤ) := Int.natCast_nonneg _
  have hq0 : (0 : ℤ) ≤ (Dw.q : ℤ) := Int.natCast_nonneg _
  have e1 := mul_nonneg hD0 (le_trans zero_le_one a)
  have e2 := mul_nonneg (Int.natCast_nonneg j) (le_trans zero_le_one a)
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, gap_add, gap_sub, gap_nsmul, c]
  push_cast at hg ⊢
  nlinarith [mul_nonneg hD0 hC0, mul_nonneg hD0 hp0, mul_nonneg hD0 hq0, mul_nonneg hD0 hD0]

open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.Vanishing.H0 ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory in

theorem ne_zero_of_noBase {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {hB : B.IsLB}
    {W : Submodule k (H0 p B ⊤)} {U : Y.Opens} (h : NoBase hB W U) (hU : (U : Set Y).Nonempty) : ∃ f ∈ W, f ≠ 0 := by
  obtain ⟨y, hy⟩ := hU
  by_contra hne
  push Not at hne
  refine h y hy ((mem_support_baseIdeal hB W y).2 fun s hs hy' => ?_)
  obtain ⟨i, hi⟩ := exists_chart hB y
  have hu := (isUnit_ger_iff _ hi).2 hy'
  rw [ger_toSec, hne s hs, map_zero] at hu
  exact not_isUnit_zero hu

theorem exists_cusp_ne_zero (hP : Hypotheses2) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hT : GlobalTheory.Published.ToroidalChartsForFan)
    (hN : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7}
    {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j))
    (hla : GapGe (((FlagTan.dimFlag (T.Q.Dw j) + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap (T.Q.Dw j))) :
    ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0), f ≠ 0 := by
  have hP1 := GlobalTheory.T.stronger_published_hypotheses_imply hP
  obtain ⟨TF⟩ := GlobalTheory.T.toroidal_flag_nonempty hP1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hfree := GlobalTheory.T.toroidal_integral_weight_section hP1 hG hQ hP.q15 hP.q16 hS hT hN _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ hla
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY hf Z TF _⟩
  haveI := (GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hY.geo).2.2
  haveI : ConnectedSpace (Y₀ TF.X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ TF.X Z)
  obtain ⟨s, hs, hs0⟩ := ne_zero_of_noBase hfree (dense_U₀ TF.X Z).nonempty
  refine ⟨(ofSpace TF.X Z Y.U _ ⟨s, hs⟩).1, (ofSpace TF.X Z Y.U _ ⟨s, hs⟩).2, fun h0 => hs0 ?_⟩
  have h1 : ofSpace TF.X Z Y.U _ ⟨s, hs⟩ = 0 := Subtype.ext h0
  exact congrArg Subtype.val (ofSpace_injective TF.X Z Y.U _ (h1.trans (map_zero _).symm))

theorem exists_cusp_uM : GlobalTheory.Published.ScholzeWeinsteinB → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → Covers fun Fm x _ ι p i Y _ _ => ∃ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ f ∈ cuspOn Y.U Z (wtOf (dat p i) (uM p i) 0), f ≠ 0 := by
  intro _ hP hG hQ hS hT hN
  have R := GlobalTheory.T.weight_conditions_at_index
  have W := GlobalTheory.T.weight_parameter_strict_antitone GlobalTheory.CovTop.SizeRows.size
  have B := wtBig_run
  unfold Covers Lifts at *
  refine (R.and (W.and B)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, -, -, hf, hj, -⟩ := hA i hi
  obtain ⟨-, -, -, -, -, ⟨w, -, hw⟩, -⟩ := hB i hi
  have hbig := hC i hi
  obtain ⟨Z⟩ := GlobalTheory.CovTop.good_comp_nonempty _ p.T hL _ hj Y _ _ hY.1
  refine ⟨Z, exists_cusp_ne_zero hP hG hQ hS hT hN Y hY.1 hf hbig.one_le Z _ ?_⟩
  rw [hw]
  exact gapGe_wt_add_parWt _ hbig _ w

end GlobalTheory.CovTop.LowNonzero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationBlowupPullbackFiniteCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisation_blowup_pullback_finiteCover : ∀ {o : CommRingCat.{0}} [Algebra.FiniteType ℤ o] {Z Z' M : Scheme.{0}} (z : Z ⟶ Spec o) [LocallyOfFiniteType z] (b : Z' ⟶ Z) [IsProper b] (J : Z.IdealSheafData), FinalTheorems.Blowup b J → ∀ [IsIntegral M] [GlobalTheory.IsNormalScheme M] (U : Z.Opens) (g' : M ⟶ U.toScheme) [IsFinite g'], (∃ m, (g' ≫ U.ι) m ∉ J.support) → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (ν₁ : S₁ ⟶ (b ⁻¹ᵁ U).toScheme), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsFinite ν₁ ∧ ν₁ ≫ (b ∣_ U) = p₁ ≫ g' ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g' ≫ U.ι)) ∧ (∀ m, (g' ≫ U.ι) m ∉ J.support → m ∈ Set.range p₁) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (a : Sp R ⟶ (b ⁻¹ᵁ U).toScheme) (β : Sp R ⟶ M), a ≫ (b ∣_ U) = β ≫ g' → (∀ w, (jK R ≫ β ≫ g' ≫ U.ι) w ∉ J.support) → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ ν₁ = a ∧ ξ₁ ≫ p₁ = β := by
  first | exact @GlobalTheory.USep.exists_normalisation_pullback_cover | exact GlobalTheory.USep.exists_normalisation_pullback_cover | (intros; apply GlobalTheory.USep.exists_normalisation_pullback_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenNonemptyCrystallineTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_nonempty_crystalline_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime], ∃ U : X.M.Z.Opens, (U : Set X.M.Z).Nonempty ∧ ∀ y : Sp (OO p) ⟶ X.M.Z, Set.range (gPt p ≫ y) ⊆ U → ∃ ct : UCTrait X p (y (cPt p)), ct.y = y := by
  first | exact @GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open | exact GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open | (intros; apply GlobalTheory.UPoinc.UCTraitEx.exists_uCTrait_of_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSectionNonvanishingClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem spMap_eq_closedPoint_iff {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (ρ : R →+* R') (hρ : ρ.Finite) (y : Sp R') : spMap ρ y = closedPoint R ↔ y = closedPoint R' := by
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hρ
  haveI : Algebra.IsIntegral R R' := inferInstance
  constructor
  · intro h
    have hc : (y.asIdeal.comap (algebraMap R R')).IsMaximal := by
      have : (spMap ρ y).asIdeal = y.asIdeal.comap ρ := rfl
      rw [h] at this
      change (y.asIdeal.comap ρ).IsMaximal
      rw [← this]; exact IsLocalRing.maximalIdeal.isMaximal R
    haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (y : PrimeSpectrum R')
    have hm : y.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hc
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
  · rintro rfl
    have hc : ((maximalIdeal R').comap (algebraMap R R')).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hc)

theorem exists_open_secNz_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ θ : U'.LG.L.Sec, (∃ g' : G'.left, G'.hom g' = closedPoint R' ∧ g' ∈ secNz θ) → ∃ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact θ ⟨g0, hg0c, hg0⟩
  have hfin : IsFinite (spMap ρ) := by rw [IsFinite.SpecMap_iff]; exact hF.2.2
  haveI hβfin : IsFinite β := MorphismProperty.of_isPullback hβ.1.flip hfin
  have hcl : IsClosedMap β := β.isClosedMap
  have hsq : ∀ g' : G'.left, G.hom (β g') = spMap ρ (G'.hom g') := fun g' => by
    change (β ≫ G.hom) g' = (G'.hom ≫ spMap ρ) g'
    rw [hβ.1.w]

  obtain ⟨s, hs⟩ : ∃ s : (Sp R' : Scheme.{0}), s = closedPoint R' := ⟨_, rfl⟩
  rw [← hs] at hg0c
  haveI hirr : IrreducibleSpace (G'.hom.fiber s) :=
    GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G' hS' _ ((Sp R').fromSpecResidueField s)
  obtain ⟨η', hη'⟩ : ∃ η' : G'.left, η' = G'.hom.fiberι s (genericPoint (G'.hom.fiber s)) := ⟨_, rfl⟩
  have hspec : ∀ g' : G'.left, G'.hom g' = s → η' ⤳ g' := by
    intro g' hg'
    obtain ⟨z, hz⟩ : g' ∈ Set.range (G'.hom.fiberι s) := (Scheme.Hom.range_fiberι G'.hom s).ge hg'
    rw [← hz, hη']
    exact ((genericPoint_spec (G'.hom.fiber s)).specializes trivial).map (G'.hom.fiberι s).continuous
  have hηs : G'.hom η' = s := by
    rw [hη']; exact (Scheme.Hom.range_fiberι G'.hom s).le ⟨_, rfl⟩
  have hηnz : η' ∈ secNz θ := (hspec g0 hg0c).mem_open (secNz θ).isOpen hg0
  refine ⟨⟨farSet β θ, isOpen_farSet β hcl θ⟩, ⟨β η', ?_, ?_⟩, ?_⟩
  · show ∀ g', β g' = β η' → g' ∈ secNz θ
    intro g' hg'
    have hg's : G'.hom g' = s := by
      rw [hs, ← spMap_eq_closedPoint_iff ρ hF.2.2, ← hsq, hg', hsq, hηs]
      exact (spMap_eq_closedPoint_iff ρ hF.2.2 s).2 hs
    have := GlobalTheory.eq_of_specializes_of_isIntegralHom β (hspec g' hg's) hg'.symm
    rw [← this]; exact hηnz
  · rw [hsq, hηs]; exact (spMap_eq_closedPoint_iff ρ hF.2.2 s).2 hs
  · intro g' hg' _
    exact hg' g' rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfNeConjStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_ne_conj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (e' : 𝓞 E) (he1' : e' - 1 ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (he' : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) → e' ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (v₂ : Z') (hv₂ : y v₂ ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) X)) (ℓ₁ : Z' →ₗ[𝓞 E] 𝓞 E)
    (hℓ₁ : ℓ₁ v₂ ∉ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  first | exact @GlobalTheory.LowFilt.exists_improves_of_ne_conj | exact GlobalTheory.LowFilt.exists_improves_of_ne_conj | (intros; apply GlobalTheory.LowFilt.exists_improves_of_ne_conj <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratio_of_expansions_proportional_at_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (G : IntFam (maximalIdeal R) D.toPre k) (S Ψ : SecK C.P.L.L C.α k), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u Ψ G) → ∀ (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsLocalRing W₀] (T₀ : Trait C W₀) (a₀ b₀ : W₀), a₀ ≠ 0 → b₀ ≠ 0 → T₀.Exp a₀ b₀ S G → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp (T.φ t) (T.φ r * u) S G := by
  first | exact @GlobalTheory.Mum.exists_ratio_of_exp_one_trait | exact GlobalTheory.Mum.exists_ratio_of_exp_one_trait | (intros; apply GlobalTheory.Mum.exists_ratio_of_exp_one_trait <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRechartingThetaSystemAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_recharting_thetaSystem_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w₀ ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ ∧ ∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (ρ'.pt x).left := by
  first | exact @GlobalTheory.UPoinc.exists_rechart_wit | exact GlobalTheory.UPoinc.exists_rechart_wit | (intros; apply GlobalTheory.UPoinc.exists_rechart_wit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianTorsionTowerStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relativeDimension_abelian_torsionTower : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ G : PDivGroup p R, G.TorsionTower A → ∃ g, SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham | exact GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham | (intros; apply GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham <;> assumption)
end

