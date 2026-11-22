import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0179

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PfiFRangeFiniteClosed
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

private theorem pfiF_fib_subset_lemma {G' : Over (Sp Ω)} (σ : 𝟙_ (Over (Sp Ω)) ⟶ G') {K : Type} [Field K]
    (a : Spec (CommRingCat.of K) ⟶ G'.left) (p : (𝟙_ (Over (Sp Ω))).left)
    (ha : a (IsLocalRing.closedPoint K) = σ.left p) :
    a = (a ≫ G'.hom) ≫ σ.left := by
  have sec : σ.left ≫ G'.hom = 𝟙 _ := by simpa using Over.w σ
  obtain ⟨τ, hτ⟩ := GlobalTheory.exists_factor_of_lift_fromSpecResidueField G'.hom p
    (Scheme.fromSpecResidueField _ p ≫ σ.left)
    (by rw [Category.assoc, sec, Category.comp_id]; rfl) a
    (ha.trans (congrArg (fun q => σ.left q) (Scheme.fromSpecResidueField_apply p _)).symm)
  rw [← hτ]
  simp only [Category.assoc, sec, Category.comp_id]

theorem pfiF_range_finite_closed {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) (H : Over (Sp Ω))
    (j : H ⟶ G) (hH : IsFinite H.hom) :
    (Set.range j.left).Finite ∧ ∀ z ∈ Set.range j.left, IsClosed ({z} : Set G.left) := by
  haveI : IsFinite H.hom := hH
  haveI : IsProper G.hom := hG.proper
  haveI : IsLocallyArtinian H.left := .of_locallyQuasiFinite H.hom
  haveI : CompactSpace H.left := QuasiCompact.compactSpace_of_compactSpace H.hom
  haveI : IsProper (j.left ≫ G.hom) := by rw [Over.w j]; infer_instance
  haveI : IsProper j.left := IsProper.of_comp j.left G.hom
  haveI : Finite H.left := finite_of_compact_of_discrete
  refine ⟨Set.finite_range _, ?_⟩
  rintro _ ⟨h, rfl⟩
  have hc := j.left.isClosedMap {h} (isClosed_discrete _)
  simpa [Set.image_singleton] using hc

private theorem pfiF_fib_closed_lemma_2 {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G'] (f : G ⟶ G')
    [IsMonHom f] (H : Over (Sp Ω)) (j : H ⟶ G)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x)
    (s : 𝟙_ (Over (Sp Ω)) ⟶ G) (p : (𝟙_ (Over (Sp Ω))).left) (y : G.left)
    (hy : f.left y = f.left (s.left p)) : y ∈ Set.range (j * (toUnit H ≫ s)).left := by
  let T : Over (Sp Ω) := Over.mk (G.left.fromSpecResidueField y ≫ G.hom)
  let x : T ⟶ G := Over.homMk (G.left.fromSpecResidueField y) rfl
  let c : T ⟶ G := toUnit T ≫ s
  have e1 := Scheme.fromSpecResidueField_apply y (IsLocalRing.closedPoint (G.left.residueField y))
  have hfy : (G.left.fromSpecResidueField y ≫ f.left) (IsLocalRing.closedPoint _) =
      (s ≫ f).left p :=
    (congrArg f.left e1).trans hy
  have key := pfiF_fib_subset_lemma (s ≫ f) (G.left.fromSpecResidueField y ≫ f.left) p hfy
  have hxc : x ≫ f = c ≫ f := by
    apply Over.OverMorphism.ext
    change G.left.fromSpecResidueField y ≫ f.left = (toUnit T ≫ (s ≫ f)).left
    have hb : (G.left.fromSpecResidueField y ≫ f.left) ≫ G'.hom = (toUnit T).left := by
      simp [T]
    rw [Over.comp_left]
    exact key.trans (congrArg (· ≫ (s ≫ f).left) hb)
  have hx' : (x * c⁻¹) ≫ f = 1 := by
    change (IsMonHom.monoidHom f T) (x * c⁻¹) = 1
    rw [map_mul, map_inv]
    change (x ≫ f) * (c ≫ f)⁻¹ = 1
    rw [hxc, mul_inv_cancel]
  obtain ⟨z, hz⟩ := hj T _ hx'
  have hxz : x = z ≫ (j * (toUnit H ≫ s)) := by
    have hm : z ≫ (j * (toUnit H ≫ s)) = (z ≫ j) * c := by
      rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc z (toUnit H) s,
        toUnit_unique (z ≫ toUnit H) (toUnit T)]
    rw [hm, hz, inv_mul_cancel_right]
  refine ⟨z.left (IsLocalRing.closedPoint (G.left.residueField y)), ?_⟩
  have h2 := congrArg
    (fun g : T ⟶ G => g.left (IsLocalRing.closedPoint (G.left.residueField y))) hxz
  exact h2.symm.trans e1

theorem pfiF_fib_closed {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G'] (hG : IsAbelianScheme G) (f : G ⟶ G')
    [IsMonHom f] (H : Over (Sp Ω)) (j : H ⟶ G) (hH : IsFinite H.hom)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x)
    (x : G.left) (hx : IsClosed ({x} : Set G.left)) :
    (f.left ⁻¹' {f.left x}).Finite ∧ ∀ z ∈ f.left ⁻¹' {f.left x}, IsClosed ({z} : Set G.left) := by
  haveI : LocallyOfFiniteType G.hom := by haveI := hG.smooth; infer_instance
  obtain ⟨s, hs⟩ := GlobalTheory.RationalPoint.exists_pt_mem (X := G) hx ⟨x, rfl⟩
  have hsx : s.left (IsLocalRing.closedPoint Ω) = x := hs
  have hsub : f.left ⁻¹' {f.left x} ⊆ Set.range (j * (toUnit H ≫ s)).left := fun y hy =>
    pfiF_fib_closed_lemma_2 f H j hj s (IsLocalRing.closedPoint Ω) y
      ((hy : f.left y = f.left x).trans (congrArg f.left hsx).symm)
  obtain ⟨hfin, hcl⟩ := pfiF_range_finite_closed hG H (j * (toUnit H ≫ s)) hH
  exact ⟨hfin.subset hsub, fun z hz => hcl z (hsub hz)⟩

theorem isFinite_of_ker {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G']
    (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (f : G ⟶ G') [IsMonHom f] (H : Over (Sp Ω))
    (j : H ⟶ G) (hH : IsFinite H.hom)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x) : IsFinite f.left := by
  haveI : IsProper G.hom := hG.proper
  haveI : IsProper G'.hom := hG'.proper
  haveI : IsProper (f.left ≫ G'.hom) := by rw [Over.w f]; infer_instance
  haveI : IsProper f.left := IsProper.of_comp f.left G'.hom
  haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G.hom
  haveI : LocallyQuasiFinite f.left :=
    GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints f.left fun y hy =>
      (pfiF_fib_closed hG f H j hH hj y hy).1
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

end PositivityTheory.PrwZar.Z2
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.RelAmpleOfTwoSmulAlt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.Z2

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem relAmple_of_two_smul {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) {M N : LB G.left}
    (hM : M.IsLB) (hN : N.IsLB) (d : ℕ) (hd : 1 ≤ d) (e : d • cls M hM = d • cls N hN) (h : Out.RelAmple G N) :
    Out.RelAmple G M := by
  haveI : IsProper G.hom := hG.proper
  have hK := GlobalTheory.isLB_lbPow hN d
  have hcls : d • cls M hM = cls (lbPow N d) hK := by
    rw [cls_lbPow hN d hK, e]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hM hK hd hcls ?_
  refine GlobalTheory.relAmple_of_isAmpleLB G hK fun U hU => ?_
  have hNU := GlobalTheory.isAmpleLB_of_relAmple G hN h U hU
  have hpk : ∀ k : ℕ, ((lbPow N k).pull (G.hom ⁻¹ᵁ U).ι).IsLB :=
    fun k => pull_isLB (GlobalTheory.isLB_lbPow hN k) _
  have hN1 : (N.pull (G.hom ⁻¹ᵁ U).ι).IsLB := pull_isLB hN _
  have hc : ∀ k : ℕ, cls _ (hpk k) = k • cls _ hN1 := fun k => by
    rw [cls_pull (GlobalTheory.isLB_lbPow hN k), cls_lbPow hN k, map_nsmul, cls_pull hN]
  have key : ∀ k : ℕ, 1 ≤ k → GlobalTheory.IsAmpleLB ((lbPow N k).pull (G.hom ⁻¹ᵁ U).ι) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      exact GlobalTheory.IsAmpleLB.of_lbIso hNU (hpk 1) ((cls_eq_iff (hpk 1) hN1).1 (by rw [hc, one_smul]))
    | succ k hk ih =>
      refine GlobalTheory.IsAmpleLB.tensor ih hNU (hpk (k + 1)) ?_
      have h1 := LB.isLB_div (hpk (k + 1)) (hpk k)
      have h2 := LB.isLB_div h1 hN1
      refine (cls_eq_zero_iff h2).1 ?_
      rw [cls_div h1 hN1, cls_div (hpk (k + 1)) (hpk k), hc, hc, succ_nsmul]
      abel
  exact key d hd

end PositivityTheory.PrwZar.Z2
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.SurjOfFiniteDimS
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

theorem surj_of_finite_dimS {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f] (g : ℕ)
    (hX : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = g)
    (hY : ∀ y : Y, IsClosed ({y} : Set Y) → ringKrullDim (Y.presheaf.stalk y) = g)
    (o : X) (ho : IsClosed ({o} : Set X)) : Surjective f := by
  refine ⟨fun y => ?_⟩
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  suffices hη : genericPoint Y ∈ Set.range f by
    have hsub : closure ({genericPoint Y} : Set Y) ⊆ Set.range f :=
      closure_minimal (Set.singleton_subset_iff.mpr hη) hcl
    have hc : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
    rw [hc] at hsub
    exact hsub (Set.mem_univ y)
  by_contra hη
  have hmono : StrictMono f := GlobalTheory.FiniteEndFlat.strictMono_of_locallyQuasiFinite f
  let F : WithTop X → Y := fun a => WithTop.recTopCoe (genericPoint Y) (fun x => f x) a
  have hF : StrictMono F := by
    intro a b hab
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe a =>
      induction b using WithTop.recTopCoe with
      | top =>
        refine lt_of_le_of_ne (genericPoint_specializes (f a)) ?_
        intro h
        have hi : Inseparable (f a) (genericPoint Y) := h.symm
        exact hη ⟨a, hi.eq⟩
      | coe b => exact hmono (WithTop.coe_lt_coe.mp hab)
  have h1 := Order.coheight_le_coheight_apply_of_strictMono F hF (o : WithTop X)
  rw [Order.coheight_coe_withTop] at h1
  have hfo : IsClosed ({f o} : Set Y) := by
    have := f.isClosedMap _ ho
    rwa [Set.image_singleton] at this
  have e1 := hX o ho
  have e2 := hY (f o) hfo
  rw [ringKrullDim_stalk_eq_coheight] at e1 e2
  have e1' : Order.coheight o = g := by exact_mod_cast e1
  have e2' : Order.coheight (f o) = g := by exact_mod_cast e2
  change Order.coheight o + 1 ≤ Order.coheight (f o) at h1
  rw [e1', e2'] at h1
  exact absurd h1 (by norm_cast; omega)

theorem isClosed_originS {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] [IsProper G.hom] :
    IsClosed ({η[G].left (IsLocalRing.closedPoint Ω)} : Set G.left) := by
  have hc : IsClosed ({IsLocalRing.closedPoint Ω} : Set (Sp Ω)) := isClosed_singleton
  have h1 := (η[G].left).isClosedEmbedding.isClosedMap _ hc
  convert h1 using 1
  exact (Set.image_singleton).symm

theorem flat_surj_of_finite {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G']
    (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (g : ℕ) (hgG : SmoothOfRelativeDimension g G.hom)
    (hgG' : SmoothOfRelativeDimension g G'.hom) (f : G ⟶ G') [IsMonHom f] (hf : IsFinite f.left) :
    Flat f.left ∧ Surjective f.left := by
  haveI := hG.smooth
  haveI := hG'.smooth
  haveI := hG.proper
  haveI := hG'.proper
  haveI := hf
  haveI : AlgebraicGeometry.IsIntegral G.left := GlobalTheory.isIntegral_of_isAbelianScheme_field Ω G hG
  haveI : AlgebraicGeometry.IsIntegral G'.left := GlobalTheory.isIntegral_of_isAbelianScheme_field Ω G' hG'
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have hsurj : Surjective f.left :=
    surj_of_finite_dimS f.left g
      (fun x hx => GlobalTheory.CutDegree.ringKrullDim_stalk hgG hx)
      (fun y hy => GlobalTheory.CutDegree.ringKrullDim_stalk hgG' hy)
      _ (isClosed_originS (G := G))
  haveI := hsurj
  exact ⟨GlobalTheory.SS.flat_of_isDominant_grpHom Ω G G' f, hsurj⟩

end PositivityTheory.PrwZar.Z2
end
end

