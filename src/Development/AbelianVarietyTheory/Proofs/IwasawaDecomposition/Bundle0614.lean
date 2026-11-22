import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPullbackOfNormalFlatProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocalization
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.Pad.BCEx

theorem isPullback_open {A T B : Scheme.{0}} (b : T ⟶ B) (jT : A ⟶ T) (jB : A ⟶ B)
    [IsOpenImmersion jT] [IsOpenImmersion jB] (w : jT ≫ b = jB) (hb : ∀ x, b x ∈ Set.range jB ↔ x ∈ Set.range jT) :
    IsPullback jT (𝟙 _) b jB :=
  (IsOpenImmersion.isPullback (𝟙 _) _ _ _ (w.trans (Category.id_comp _).symm) (by ext x; exact hb x)).flip

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {p : ℕ} {W : ValuationSubring ℂ}

section Local

variable {Xo : ∀ l : Level H, Moduli Dw l} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_mdl (Z : Mdl Y i₀) [IsIso Z.π] {i : Idx H p} (hi : Z.i = i) {X' : Scheme.{0}} (f : X' ⟶ (Y i).X)
    (a : (Xo i.l).XF i.c ⟶ X') [IsOpenImmersion (Y i).j] (hp : IsPullback a (𝟙 _) f (Y i).j)
    (hs : IsProjOver (f ≫ (Y i).s)) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') (hf : Flat (f ≫ (Y i).s))
    (hd : Dense (Set.range a)) : ∃ (Z' : Mdl Y i₀) (h : Z'.i = i) (e : Z'.X ≅ X'), Z'.ty = Z.ty ∧
      Z'.π ≫ eqToHom (congrArg (fun j => (Y j).X) h) = e.hom ≫ f := by
  subst hi
  let U : Z.X.Opens := Z.π ⁻¹ᵁ (Y Z.i).j.opensRange
  have hU : (U : Set Z.X) = Z.opn := rfl
  let u : U.toScheme ≅ (Xo Z.i.l).XF Z.i.c := IsOpenImmersion.isoOfRangeEq (U.ι ≫ Z.π) (Y Z.i).j (by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, hU]
    exact Set.image_preimage_eq _ Z.π.surjective)
  have hu : u.hom ≫ (Y Z.i).j = U.ι ≫ Z.π := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨n, ι, hι, hs⟩ := hs
  have hiso : IsIso ι.toImage := inferInstance
  let e : ι.ker.subscheme ≅ X' := (asIso ι.toImage).symm
  have he : e.inv ≫ ι.ker.subschemeι = ι := ι.toImage_imageι
  have hp' : IsPullback (u.hom ≫ a ≫ e.inv) (𝟙 U.toScheme) (e.hom ≫ f ≫ inv Z.π) U.ι :=
    hp.of_iso u.symm e.symm u.symm (asIso Z.π).symm (by simp) (by simp) (by simp)
      (by simp [Iso.eq_inv_comp, ← Category.assoc, hu])
  have h₀ : (e.hom ≫ f ≫ inv Z.π) ≫ Z.s = e.hom ≫ f ≫ (Y Z.i).s := by
    rw [← Z.π_s]; simp
  have hs' : (e.hom ≫ f ≫ inv Z.π) ≫ Z.s = ι.ker.subschemeι ≫ PSpace.str _ n := by
    rw [h₀, ← hs, ← Category.assoc]
    congr 1
    exact ((Iso.inv_comp_eq e).1 he).symm
  have hn₀ := BaseMdl.normal_of_iso e.hom hn
  have hn' : GlobalTheory.IsNormalScheme ι.ker.subscheme := ⟨fun x => (hn₀ x).1, fun x => (hn₀ x).2⟩
  have hf' : Flat ((e.hom ≫ f ≫ inv Z.π) ≫ Z.s) := by rw [h₀]; infer_instance
  have hd' : Dense (Set.range (u.hom ≫ a ≫ e.inv)) := by
    have : DenseRange e.inv := e.inv.surjective.denseRange
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, u.hom.surjective.range_comp, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact this.comp hd e.inv.continuous
  refine ⟨Recode.mdl Z ι.ker _ hU hp' hs' hn' hf' hd', rfl, e, rfl, (Category.comp_id _).trans ?_⟩
  change (e.hom ≫ f ≫ inv Z.π) ≫ Z.π = e.hom ≫ f
  simp

theorem compat (Z : Mdl Y i₀) {i : Idx H p} (hi : Z.i = i) {O : Type} [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O)
    (j : (Xo i.l).XF i.c ⟶ X) (β : O → ℂ) (b : O →+* i.c.V W) (hb : ∀ x, (((b x : i.c.V W) : i.c.F) : ℂ) = β x)
    {X' : Scheme.{0}} (e : Z.X ≅ X') (f : X' ⟶ (Y i).X) (a : (Xo i.l).XF i.c ⟶ X') (hp : IsPullback a (𝟙 _) f (Y i).j)
    (hπ : Z.π ≫ eqToHom (congrArg (fun j => (Y j).X) hi) = e.hom ≫ f) (q : X' ⟶ pullback s (spMap b)) [IsIso q]
    (q₁ : a ≫ q ≫ pullback.fst _ _ = j) (q₂ : q ≫ pullback.snd _ _ = f ≫ (Y i).s) :
    ∃ (b' : O →+* Z.i.c.V W) (ν : Z.X ⟶ pullback s (spMap b')),
      (∀ x, (((b' x : Z.i.c.V W) : Z.i.c.F) : ℂ) = β x) ∧ IsFinite ν ∧ ν ≫ pullback.snd _ _ = Z.s ∧
      pullback.fst Z.π (Y Z.i).j ≫ ν ≫ pullback.fst _ _ =
        pullback.snd Z.π (Y Z.i).j ≫ eqToHom (congrArg (fun i : Idx H p => (Xo i.l).XF i.c) hi) ≫ j := by
  subst hi
  replace hπ : Z.π = e.hom ≫ f := (Category.comp_id _).symm.trans hπ
  refine ⟨b, e.hom ≫ q, hb, inferInstance, by rw [Category.assoc, q₂, ← Category.assoc, ← hπ, Z.π_s], ?_⟩
  have w : (pullback.fst Z.π (Y Z.i).j ≫ e.hom) ≫ f = pullback.snd Z.π (Y Z.i).j ≫ (Y Z.i).j := by
    rw [Category.assoc, ← hπ, pullback.condition]
  have h₁ := hp.lift_fst _ _ w
  have h₂ := hp.lift_snd _ _ w
  rw [Category.comp_id] at h₂
  rw [h₂] at h₁
  rw [eqToHom_refl, Category.id_comp, ← q₁, ← Category.assoc _ a, h₁]
  simp only [Category.assoc]

end Local

section Global

variable {l : Level H} {c : Coeff l}

theorem exists_isLocalization (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W)
    (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ∃ M : Submonoid (𝓞 c.F), letI := b.toAlgebra; IsLocalization M (c.V W) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨v, -, hv⟩ := GlobalModelGuards.exists_prime_eq c W p hp hW
  haveI hl : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) :=
    Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  letI := b.toAlgebra
  refine ⟨v.asIdeal.primeCompl, IsLocalization.isLocalization_of_algEquiv _ (S := v.valuationSubringAtPrime c.F)
    (AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hv)) fun x => ?_)⟩
  exact Subtype.ext (hb x).symm

variable {Xo : Moduli Dw l}

theorem normal_bc (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (b : 𝓞 c.F →+* c.V W) (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback Y.s (spMap b)) := by
  obtain ⟨M, hM⟩ := exists_isLocalization hp hW b hb
  letI := b.toAlgebra
  have h₁ : IsPreimmersion (spMap b) := IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 c.F)) (S := c.V W) M
  have h₂ : Flat (spMap b) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (c.V W) M)
  have : IsPreimmersion (pullback.fst Y.s (spMap b)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h₁
  intro x
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst Y.s (spMap b)) x
  have i := (asIso ((pullback.fst Y.s (spMap b)).stalkMap x)).commRingCatIsoToRingEquiv
  obtain ⟨_, _⟩ := Y.normal (pullback.fst Y.s (spMap b) x)
  exact ⟨i.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv i⟩

theorem exists_map (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Y' : Model Xo c (c.V W).subtype) (b : 𝓞 c.F →+* c.V W) (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F))
    (h : Dominates Y Y' b) : ∃ (f : pullback Y.s (spMap b) ⟶ Y'.X) (a : Xo.XF c ⟶ pullback Y.s (spMap b)),
      f ≫ Y'.s = pullback.snd _ _ ∧ a ≫ pullback.fst _ _ = Y.j ∧ IsPullback a (𝟙 _) f Y'.j ∧ Dense (Set.range a) := by
  obtain ⟨f, t, m₁, m₂, hf, hj, -⟩ := h
  have hc : spMap (c.V W).subtype ≫ spMap b = spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← spMap_comp]; exact congrArg spMap (RingHom.ext hb)
  let g : pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ pullback Y.s (spMap b) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (c.V W).subtype)
      (by rw [Category.assoc, hc, pullback.condition])
  have g₁ : g ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hg : IsPullback g (pullback.snd _ _) (pullback.snd _ _) (spMap (c.V W).subtype) :=
    IsPullback.of_right (by rw [g₁, hc]; exact IsPullback.of_hasPullback _ _) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
  have := c.fin
  have hV : (p : c.F) ∈ (c.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    refine Or.inr fun h => hW.elim (Nat.cast_ne_zero.2 hp.ne_zero) fun h' => h' ?_
    have h2 : c.F.val.toRingHom (p : c.F)⁻¹ ∈ W := h
    simpa using h2
  have := BaseMdl.away_of_valuation c.F (c.V W) p hp hV
  have ho : IsOpenImmersion (spMap (c.V W).subtype) := IsOpenImmersion.of_isLocalization (S := c.F) ((p : ℕ) : c.V W)
  have : IsOpenImmersion g := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hg.flip ho
  have := Y.jQ_open
  have := BaseMdl.isOpenImmersion_j hp hW Y'
  have ha : (Y.jQ ≫ g) ≫ pullback.fst _ _ = Y.j := by rw [Category.assoc, g₁]; rfl
  have hgen : ∀ x, pullback.snd Y.s (spMap b) x ∈ Set.range (spMap (c.V W).subtype) → x ∈ Set.range g :=
    fun x ⟨z, hz⟩ => (Scheme.exists_preimage_of_isPullback hg x z hz.symm).imp fun _ h => h.1
  refine ⟨f, Y.jQ ≫ g, hf, ha, isPullback_open _ _ _ (hj _ ha) fun x => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := hgen x ⟨pullback.snd Xo.s _ z, by
      rw [← Scheme.Hom.comp_apply, ← BaseMdl.j_s Y', Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, hf]⟩
    have h₁ : Y'.j z ∈ abLocus Y'.t.G := by
      have : Y'.jQ z ∈ pullback.fst Y'.s (spMap (c.V W).subtype) ⁻¹' abLocus Y'.t.G := Y'.ab_gen.ge ⟨z, rfl⟩
      rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply] at this
    rw [hz] at h₁
    have h₂ := (abLocus_pullback abLocusOne Y.t.semi m₁.cart.1 _).2
      ((abLocus_pullback abLocusOne Y'.t.semi m₂.cart.1 _).1 h₁)
    rw [← Scheme.Hom.comp_apply, g₁] at h₂
    obtain ⟨w, rfl⟩ := Y.ab_gen.le h₂
    exact ⟨w, Scheme.Hom.comp_apply _ _ w⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [← Scheme.Hom.comp_apply, hj _ ha]⟩
  · have := Y.flat
    have h1 : DenseRange g := by
      intro x
      let q : Sp c.F := (⊥ : PrimeSpectrum c.F)
      have hs : spMap (c.V W).subtype q ⤳ pullback.snd Y.s (spMap b) x := by
        refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
        show Ideal.comap (c.V W).subtype ⊥ ≤ _
        rw [Ideal.comap_bot_of_injective _ Subtype.val_injective]
        exact bot_le
      obtain ⟨x', hx', e⟩ := Flat.generalizingMap (pullback.snd Y.s (spMap b)) hs
      refine closure_mono ?_ (specializes_iff_mem_closure.1 hx')
      exact Set.singleton_subset_iff.2 (hgen _ ⟨q, e.symm⟩)
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact h1.comp Y.jQ_dense g.continuous

end Global

theorem exists_isBC {Xo : ∀ l : Level H, Moduli Dw l} {Y : LocFam Xo} {l : Level H} {c : Coeff l}
    {hg : ∀ p : ℕ, p.Prime → l.GoodAt p} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Code Y c hg)
    (Z₀ : Mdl (Y p W hp hW) ⟨l, c, hg p hp⟩) (hi : Z₀.i = ⟨l, c, hg p hp⟩) [IsIso Z₀.π] (hty : ∀ σ, Z₀.ty σ = ∅) :
    ∃ Z', Z.IsBC (hp := hp) (hW := hW) Z' := by
  obtain ⟨Y', e, he, hd⟩ := Z.ex
  obtain ⟨b, hb, -⟩ := GlobalModelGuards.exists_incl c W
  obtain ⟨f, a, hf, ha, hP, hD⟩ := exists_map hp hW Y' _ b hb (hd p W hp hW b hb)
  have := BaseMdl.isOpenImmersion_j hp hW (Y p W hp hW ⟨l, c, hg p hp⟩)
  have := Y'.flat
  obtain ⟨Z', h, e', h₁, h₂⟩ := exists_mdl Z₀ hi f a hP
    (by rw [hf]; exact ProjSpace.isProjOver_pullback_snd b Y'.proj) (normal_bc hp hW Y' b hb)
    (by rw [hf]; infer_instance) hD
  let q : pullback Y'.s (spMap b) ⟶ pullback Z.s (spMap b) :=
    pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _) (by rw [he.1, Category.comp_id]) (by simp)
  refine ⟨Z', h, fun σ => by rw [h₁, hty], compat Z' h Z.s Z.j (fun x => ((x : c.F) : ℂ)) b
    (fun x => congrArg _ (hb x)) e' f a hP h₂ q ?_ ?_⟩
  · rw [pullback.lift_fst, ← Category.assoc, ha, he.2]
  · rw [pullback.lift_snd, Category.comp_id, hf]

theorem exists_isBCAt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (Z : CodeAt S κ), ∃ Z', IsBCAt ct Z Z' := by
  intro D A N j S κ p ct Z
  have := ct.B.iso none
  exact exists_isBC ct.hp ct.hW Z (ct.B.X none) (ct.B.lvl none) (ct.B.ty none)

end GlobalTheory.ShFam.Pad.BCEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeyInputAtChartPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtEx

theorem nonempty_basis_of_isLieBasis {X : Scheme.{0}} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G x Φ) {n : ℕ} {v : Fin n → (epsR R ⟶ G')} (hb : IsLieBasis v) :
    Nonempty (Module.Basis (Fin n) R (TanM x G)) := by
  let u : Fin n → TanM x G := fun j => mkT (pushHom h (epsR R) (v j)) ((PullbackSections.isTangent_iff h _).1 (hb.1 j))
  have hcomb : ∀ (a : Fin n → R) (w : epsR R ⟶ G'), IsLieComb a v w ↔
      pushHom h (epsR R) w = tv (∑ i, a i • u i) := fun a w => by
    rw [PullbackSections.isLieComb_iff h, GlobalTheory.FlagMod.tv_sum']
    rfl
  have hbij : Function.Bijective (Fintype.linearCombination R u) := by
    rw [Function.bijective_iff_existsUnique]
    intro W
    obtain ⟨p, hp⟩ := PullbackSections.push_surj h (tv W)
    have ht : IsTangent p := (PullbackSections.isTangent_iff h p).2 (by rw [hp]; exact tv_mem W)
    refine (existsUnique_congr fun a => ?_).1 (hb.2 p ht)
    rw [hcomb, hp, Fintype.linearCombination_apply]
    exact ⟨fun e => (tanM_ext e).symm, fun e => by rw [e]⟩
  exact ⟨(Pi.basisFun R (Fin n)).map (LinearEquiv.ofBijective _ hbij)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_keyAt_of_sabMap (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) (hg : SmoothOfRelativeDimension M.n t.G.hom) (hn : 1 ≤ M.n) :
    ∃ x : KeyIn R, x.P.g = M.n ∧ KeyAt M z hz x := by
  obtain ⟨w, th, ⟨hw, hr⟩, hth, hne⟩ :=
    GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t z m M.U hz M.θ M.θ_mem M.θ_ne
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t Y.t (spMap (ev z M.U hz) ≫ M.hU.fromSpec), m'.φ = m.φ := by
    rw [GlobalTheory.FlagMod.spMap_ev z M.hU hz]
    exact ⟨m, rfl⟩
  obtain ⟨v, hv, hb, -⟩ := M.lie R (ev z M.U hz) t m'
  have he : eSec t.G ≫ m.φ = z ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec Y.t.G) m.base)
  have hrig : m.cm.rigPull Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ z he Y.t.PP.L Y.t.PP.rig := by
    have key : ∀ (a b : Sp R ⟶ Y.X) (_ : a = b) ha hb,
        rigPullOf (G' := t.G) m.φ a ha Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ b hb Y.t.PP.L Y.t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  refine ⟨⟨GlobalTheory.GenericPol.toPolAV t M.n hg hp hA hK, hn, t.PP.rig, t.PP.rigGen, th, fun s => ?_, v, hb⟩, rfl,
    m.φ, he, w, rfl, m.cart, hw, hrig ▸ hr, fun j i h => ?_, fun i => ?_⟩
  · obtain ⟨g, i, h₁, h₂⟩ := hne s
    exact ⟨g, h₁, Opens.mem_iSup.2 ⟨i, h₂⟩⟩
  · refine (hth (j PUnit.unit) i _ h le_rfl).trans ?_
    exact congrArg (· * _) (GlobalTheory.LB.resG_self _ _)
  · exact hm' ▸ hv i

theorem smoothOfRelativeDimension_fibre {K : Type} [Field K] {z : Sp K ⟶ Y.X} {t : SAB H (Sp K)} (m : SABMap t Y.t z)
    (h : Set.range z ⊆ Set.range Y.j) :
    SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t.G.hom := by
  obtain ⟨K', _, i, y, e⟩ := GlobalTheory.GenericPol.exists_lift z Y.j h
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.CubePf.cubePull (Out.specOf i) t
  generalize (⟨(Over.pullback (Out.specOf i)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t t' Y.j y Y.m (e ▸ n)
  have h₁ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m'.cart.1
      (GlobalTheory.ObjDim.smoothOfRelativeDimension Y.oF)
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace ↥t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have h₂ : SmoothOfRelativeDimension d t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m₁.cart.1 hd
  rw [← H1.dim_unique _ h₂ h₁ (eSec t'.G (default : PrimeSpectrum K'))]
  exact hd

theorem exists_keyAt_model (M : GChart Y) {K : Type} [Field K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    (h : Set.range z ⊆ Set.range Y.j) (hpos : 1 ≤ Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) :
    ∃ x : KeyIn K, x.P.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) ∧ KeyAt M z hz x := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull z Y.t
  generalize (⟨(Over.pullback z).obj Y.t.G, IsSemiAbelian.pullback _ Y.t.G Y.t.semi,
    Geo.Tor.OAct.pullback _ Y.t.G Y.t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t at m
  obtain ⟨hp, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv m h
  have hg := smoothOfRelativeDimension_fibre m h
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis t.G hg
  obtain ⟨b⟩ := nonempty_basis_of_isLieBasis m.cart hv
  have hn : Module.finrank ℚ E / 2 * (Dw.p + Dw.q) = M.n := by
    simpa using Fintype.card_congr (b.indexEquiv (GlobalTheory.FlagMod.lieBasis M.toMChart z hz))
  rw [hn] at hg hpos ⊢
  exact exists_keyAt_of_sabMap M z hz m hp hA hK hg hpos

theorem exists_keyAt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (M : ct.KeyChart) (K : Type) [Field K] (z : Sp K ⟶ ct.Xm.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U), Set.range z ⊆ ct.Xm.opn → ∃ x : KeyIn K, x.P.g = D.R.f * N ∧ KeyAt M z hz x := by
  intro D A N j S κ p ct M K _ z hz h
  have hd : Module.finrank ℚ D.host.E / 2 * (S.Dw.p + S.Dw.q) = D.R.f * N := by
    rw [GlobalTheory.PinNum.finrank_host, S.rank_eq, Nat.mul_div_cancel_left _ two_pos]
  have hf : 1 ≤ D.R.f := by
    have h₁ : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [GlobalTheory.PinNum.finrank_host] at h₁
    omega
  have hN := S.two_le
  rw [← hd]
  exact exists_keyAt_model (Y := ct.base) M z hz (ct.range_base_j ▸ h)
    (hd ▸ Nat.mul_pos hf (by omega))

end GlobalTheory.KeyAtEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjective
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModelOver

theorem isProjOver_comp_spMap {R S : Type} [CommRing R] [CommRing S] (ε : R ≃+* S) {X : Scheme.{0}} {s : X ⟶ Sp S}
    (h : IsProjOver s) : IsProjOver (s ≫ spMap ε.toRingHom) := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsIso (spMap ε.toRingHom) := by
    have : IsIso (CommRingCat.ofHom ε.toRingHom) := (ε.toCommRingCatIso).isIso_hom
    exact inferInstance
  have hb : IsIso (GlobalTheory.ProjSpace.baseChange N ε.toRingHom) :=
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme)
      (GlobalTheory.ProjSpace.isPullback_baseChange N ε.toRingHom).flip ‹_›
  refine ⟨N, i ≫ GlobalTheory.ProjSpace.baseChange N ε.toRingHom, inferInstance, ?_⟩
  rw [Category.assoc, GlobalTheory.ProjSpace.baseChange_str, Category.assoc]

theorem isSeparated_and_noetherian {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
    (h : IsProjOver s) : X.IsSeparated ∧ IsLocallyNoetherian X := by
  have := CommonModel.isProper_of_isProjOver h
  have hs : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from s]
    infer_instance
  exact ⟨⟨hs⟩, LocallyOfFiniteType.isLocallyNoetherian s⟩

theorem exists_normal_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (O : Type) [CommRing O] (ε : 𝓞 F ≃+* O) (X : Scheme.{0}) (sX : X ⟶ Sp O) (ρ : Y.X ⟶ X), IsProjOver sX → ρ ≫ sX ≫ spMap ε.toRingHom = Y.str ≫ spMap (algebraMap (𝓞 F) F) → X.IsSeparated ∧ IsLocallyNoetherian X ∧ ∃ (M : GlobalTheory.TrueGeo.Model Y) (ρ' : M.X ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X ∧ M.j ≫ ρ' = ρ := by
  intro F _ _ Y O _ ε X sX ρ hX hρ
  have hP := isProjOver_comp_spMap ε hX
  obtain ⟨hs, hn⟩ := isSeparated_and_noetherian hP
  refine ⟨hs, hn, ?_⟩
  obtain ⟨X', π, j, hXi, hπ, hfl, H, hg⟩ := GlobalTheory.IntModel.exists_flat_model (O := 𝓞 F) Y.str Y.isProjOver
    (fun _ : Unit => X) (fun _ => sX ≫ spMap ε.toRingHom) (fun _ => ρ) (fun _ => hP) (fun _ => hρ)
  obtain ⟨g, hg₁, -⟩ := hg ()
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 F)).2 inferInstance
  have har : IsArithVar π Y.dim := ⟨inferInstance, inferInstance, hXi, hπ, inferInstance,
    GlobalTheory.IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H Y.topologicalKrullDim_eq⟩
  let M : GlobalTheory.TrueGeo.Model Y := ⟨X', π, har, j, H⟩
  obtain ⟨N, π₁, -, hN, -, -, hj, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  refine ⟨N, π₁ ≫ g, hN, ?_⟩
  rw [← Category.assoc, hj]
  exact hg₁

end GlobalTheory.ModelOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetricStatement
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polyRep_inducedBundle_and_metric : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (E : Fr (ratOf X) m 0), ∃ E' : Fr (ratOf X) (fun _ : Unit => ρ.M) 0, (∀ z, ∀ A ∈ E.S z, (fun _ : Unit => ρ.ev A) ∈ E'.S z) ∧ ∀ (σ : F →+* ℂ) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∃ H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ, IsMetricOn E' O H' ∧ ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y) := by
  first | exact @GlobalTheory.GoodMetric.RepBundle.exists_repBundle | exact GlobalTheory.GoodMetric.RepBundle.exists_repBundle | (intros; apply GlobalTheory.GoodMetric.RepBundle.exists_repBundle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealUnitNotRootOfUnityStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_unit_not_root_of_unity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], 1 < Module.finrank ℚ E / 2 → ∃ u : (𝓞 E)ˣ, cc (u : E) = u ∧ ∀ n : ℕ, 0 < n → (u : E) ^ n ≠ 1 := by
  first | exact @GlobalTheory.UnipKill.exists_real_unit_infinite_order | exact GlobalTheory.UnipKill.exists_real_unit_infinite_order | (intros; apply GlobalTheory.UnipKill.exists_real_unit_infinite_order <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRefinedCocycleEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_refined_cocycle_embedding : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (Z : Scheme.{0}) (s : Z ⟶ Sp O), IsProjOver s → ∀ C : Coc Z, ∃ (Γ : Type) (a : Γ → C.A) (D : Γ → Z.Opens) (aff : ∀ g, IsAffineOpen (D g)) (cover : ∀ x : Z, ∃ g, x ∈ D g) (le : ∀ g, D g ≤ C.B (a g)) (N : ℕ), Nonempty ((C.refine a D aff cover le).Emb N) := by
  first | exact @GlobalTheory.DRFlag.Coc.exists_refine_emb | exact GlobalTheory.DRFlag.Coc.exists_refine_emb | (intros; apply GlobalTheory.DRFlag.Coc.exists_refine_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothHermitianMetricProjectiveVarietyStatement
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_hermitianMetric_projective_variety : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0), ∃ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H := by
  first | exact @GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top | exact GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top | (intros; apply GlobalTheory.GoodMetric.SmoothMetric.exists_isMetricOn_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitSectionOfLocalValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_section_of_local_values : ∀ (X : Scheme.{0}) [IsReduced X] (U : X.Opens) (P : ∀ (k : Type) [Field k], (Sp k ⟶ X) → k → Prop), (∀ (k : Type) [Field k] (w : Sp k ⟶ X) (a a' : k), ⊤ ≤ w ⁻¹ᵁ U → P k w a → P k w a' → a = a') → (∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → ¬ P k w 0) → (∀ z ∈ U, ∃ (V : X.Opens) (s : Γ(X, V)), z ∈ V ∧ V ≤ U ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ V → P k w (valF w V s)) → ∃ s : Γ(X, U)ˣ, ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U s.val) := by
  first | exact @GlobalTheory.FieldPtGlue.exists_unit_of_locally | exact GlobalTheory.FieldPtGlue.exists_unit_of_locally | (intros; apply GlobalTheory.FieldPtGlue.exists_unit_of_locally <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryStabilizerScalingIsotropicStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_stabilizer_scaling_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (ε : E) (c : 𝓞 E), 0 < d → ξ ∈ X.Λ → η ∈ X.Λ → herm X.Gm ξ ξ = 0 → herm X.Gm η η = 0 → herm X.Gm ξ η = d → cc ε = ε → ε ≠ 0 → IsIntegral ℤ ε → IsIntegral ℤ ε⁻¹ → ε - 1 = d * X.den * c → ∃ g : GL (Fin N) E, IsUStab X.Gm X.Λ g ∧ (g : Matrix (Fin N) (Fin N) E).mulVec ξ = ε • ξ := by
  first | exact @GlobalTheory.UnipKill.exists_isUStab_hypRot | exact GlobalTheory.UnipKill.exists_isUStab_hypRot | (intros; apply GlobalTheory.UnipKill.exists_isUStab_hypRot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_varieties_components_smooth_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), FnAlgClosed Xo c → SmoothOfRelativeDimension Dw.dim (genStr Z) → ∃ (B : Comp Xo c → GlobalTheory.ProjVar.Var F) (j : ∀ i, (B i).X ⟶ gen Z), (∀ i, IsOpenImmersion (j i) ∧ (B i).dim = Dw.dim ∧ j i ≫ genStr Z ≫ spMap e.toRingHom = (B i).str ∧ ∀ p ∈ i.1, Z.jQ p ∈ Set.range (j i)) ∧ ∀ z : gen Z, ∃! i, z ∈ Set.range (j i) := by
  first | exact @GlobalTheory.GenFibreComp.exists_vars | exact GlobalTheory.GenFibreComp.exists_vars | (intros; apply GlobalTheory.GenFibreComp.exists_vars <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_combination_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] (f : c.F →+* k) (x : Sp k ⟶ X) (u : Vecs Dw t k), GlobalTheory.LocM.IsFrame t f x u → (∀ cf cf' w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf w → IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf' w → cf = cf') ∧ ∀ (j : Fin (letters Dw).length) (cf : Fin (Dw.mult ((letters Dw).get j).1) → k) w, (∀ m, ((letters Dw).get j).2 < m → cf m = 0) → IsCombAtG t x (u ((letters Dw).get j).1) cf w → ∃ cg : Fin (letters Dw).length → k, (∀ m, j < m → cg m = 0) ∧ cg j = cf ((letters Dw).get j).2 ∧ IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cg w := by
  first | exact @GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame | exact GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame | (intros; apply GlobalTheory.Proof.frame_combination_coeff_unique.concat_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfFullIntStepStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDR_of_full_intStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀), (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ σ, IntStep (atlasOf Z) σ (Dw.mult σ)) → HasDR Z := by
  first | exact @GlobalTheory.DRFlag.hasDR_of_intStep | exact GlobalTheory.DRFlag.hasDR_of_intStep | (intros; apply GlobalTheory.DRFlag.hasDR_of_intStep <;> assumption)
end

