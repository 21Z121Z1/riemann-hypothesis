import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocalGroups
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.UnionFib

theorem exists_ringHom_extend {A R Ω : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [Field Ω]
    [IsAlgClosed Ω] (φ : A →+* R) [IsLocalHom φ] (hφ : ((residue R).comp φ).Finite) (ψ : A →+* Ω) [IsLocalHom ψ] :
    ∃ u : R →+* Ω, u.comp φ = ψ := by
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map φ).toAlgebra
  letI : Algebra (ResidueField A) Ω := (ResidueField.lift ψ).toAlgebra
  have hf : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hφ
    exact RingHom.Finite.of_comp_finite hφ
  haveI : Module.Finite (ResidueField A) (ResidueField R) := hf
  let l : ResidueField R →ₐ[ResidueField A] Ω := IsAlgClosed.lift
  refine ⟨l.toRingHom.comp (residue R), RingHom.ext fun a => ?_⟩
  exact l.commutes (residue A a)

theorem exists_geom_lift {X S : Scheme.{0}} {j : X ⟶ S} {A : Over X} [GrpObj A] {x : S} (C : Chart j A x) (Ω : Type)
    [Field Ω] [IsAlgClosed Ω] (p : Sp Ω ⟶ S) (hp : p (closedPoint Ω) = x) : ∃ q : Sp Ω ⟶ Sp C.R, q ≫ C.ξ = p := by
  obtain ⟨ψ, hl, hψ⟩ : ∃ ψ : S.presheaf.stalk (C.ξ (closedPoint C.R)) ⟶ CommRingCat.of Ω,
      IsLocalHom ψ.hom ∧ Spec.map ψ ≫ S.fromSpecStalk _ = p := by
    rw [C.centre, ← hp]
    exact ⟨Scheme.stalkClosedPointTo p, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk p⟩
  obtain ⟨u, hu⟩ := exists_ringHom_extend (Scheme.stalkClosedPointTo C.ξ).hom C.etc.2.2 ψ.hom
  refine ⟨spMap u, ?_⟩
  have e : Scheme.stalkClosedPointTo C.ξ ≫ CommRingCat.ofHom u = ψ := CommRingCat.hom_ext hu
  rw [← hψ, ← e, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

theorem isPullback_of_mono {A P G S X : Scheme.{0}} {i : A ⟶ P} {a : A ⟶ S} {p : P ⟶ X} {j : S ⟶ X} (κ : G ⟶ P)
    [Mono κ] {e : A ⟶ G} (h : IsPullback i a p j) (he : e ≫ κ = i) : IsPullback e a (κ ≫ p) j := by
  have w : e ≫ κ ≫ p = a ≫ j := by rw [← h.w, ← he, Category.assoc]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift (s.fst ≫ κ) s.snd (by rw [Category.assoc]; exact s.condition))
    (fun s => ?_) (fun s => h.lift_snd _ _ _) (fun s t h₁ h₂ => ?_)⟩⟩
  · rw [← cancel_mono κ, Category.assoc, he]
    exact h.lift_fst _ _ _
  · apply h.hom_ext
    · rw [h.lift_fst, ← h₁, Category.assoc, he]
    · rw [h.lift_snd, h₂]

variable {σ : Setup} (E : Emb σ)

theorem rho_closedPoint (x : Sp σ.R) : spMap (σ.ρ x) (closedPoint _) = x := by
  rw [← σ.hρ]; exact (σ.C x).centre

theorem range_subset : Set.range E.ιA ⊆ E.U := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨v, h1, h2⟩ := Scheme.exists_preimage_of_isPullback (σ.cart ((σ.A.hom ≫ awayMap σ.f) a)) a (closedPoint _)
    (rho_closedPoint _).symm
  refine ⟨_, (σ.V _).ι v, h2, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← E.onV, Scheme.Hom.comp_apply, h1]

theorem isPullback_chart (hC : σ.Common) {G : Scheme.{0}} (κ : G ⟶ E.P) [IsOpenImmersion κ] (hκ : Set.range κ = E.U)
    (x : Sp σ.R) : ∃ m : (σ.C x).G.left ⟶ G, m ≫ κ = E.emb x ∧
      IsPullback m (σ.C x).G.hom (κ ≫ E.p) (spMap (σ.ρ x)) := by
  obtain ⟨w, hw⟩ := E.openIn x
  let l := pullback.lift (E.emb x) (σ.C x).G.hom w
  have l1 : l ≫ pullback.fst _ _ = E.emb x := pullback.lift_fst _ _ _
  have l2 : l ≫ pullback.snd _ _ = (σ.C x).G.hom := pullback.lift_snd _ _ _
  have hr : Set.range (E.emb x) ⊆ Set.range κ := by
    rintro _ ⟨y, rfl⟩
    have e1 : pullback.fst E.p (spMap (σ.ρ x)) (l y) = E.emb x y := by rw [← Scheme.Hom.comp_apply, l1]
    rw [hκ, ← e1]
    exact (Emb.fst_mem_U_iff σ E hC x (l y)).2 ⟨y, e1.symm, by rw [← Scheme.Hom.comp_apply, l2]⟩
  refine ⟨IsOpenImmersion.lift κ _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have sq : IsPullback (IsOpenImmersion.lift κ _ hr) l κ (pullback.fst E.p (spMap (σ.ρ x))) := by
    refine IsOpenImmersion.isPullback _ _ _ _ (by rw [l1, IsOpenImmersion.lift_fac]) ?_
    ext z
    constructor
    · intro hz
      have hz' : pullback.fst E.p (spMap (σ.ρ x)) z ∈ E.U := hκ ▸ hz
      obtain ⟨x', y', hy', e⟩ := hz'
      obtain ⟨Ω, _, s, t', o, hst, hs, ht⟩ :=
        Sat.exists_field_pt (pullback.fst E.p (spMap (σ.ρ x))) (E.emb x') z y' e.symm
      obtain ⟨w', -⟩ := E.openIn x'
      obtain ⟨t, h1, h2⟩ := (Sat.transfer σ E hC x x' Ω (s ≫ pullback.snd _ _) (t' ≫ (σ.C x').G.hom) o
        (by rw [Scheme.Hom.comp_apply, ht]; exact hy')
        (by rw [Category.assoc, Category.assoc, ← pullback.condition, ← w', reassoc_of% hst])).2 t' rfl
      have : t ≫ l = s := by
        apply pullback.hom_ext
        · rw [Category.assoc, l1, h2, hst]
        · rw [Category.assoc, l2, h1]
      exact ⟨t o, by rw [← Scheme.Hom.comp_apply, this, hs]⟩
    · rintro ⟨y, rfl⟩
      exact hr ⟨y, by rw [← Scheme.Hom.comp_apply, l1]⟩
  have := sq.paste_vert (IsPullback.of_hasPullback E.p (spMap (σ.ρ x)))
  rwa [l2] at this

theorem alpha_comp (x : Sp σ.R) :
    (σ.C x).α ≫ E.ιA = pullback.fst (σ.C x).G.hom (jK (σ.C x).R) ≫ E.emb x := by
  have hr : Set.range (pullback.fst (σ.C x).G.hom (jK (σ.C x).R)) ⊆ Set.range (σ.V x).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine (σ.hV x _).2 ?_
    have e : spMap (σ.ρ x) ((σ.C x).G.hom (pullback.fst (σ.C x).G.hom (jK (σ.C x).R) z)) =
        awayMap σ.f ((σ.C x).y (pullback.snd (σ.C x).G.hom (jK (σ.C x).R) z)) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        pullback.condition_assoc, (σ.C x).hy, σ.hρ]
    intro hm
    have h1 : σ.f ∈ (spMap (σ.ρ x) ((σ.C x).G.hom (pullback.fst (σ.C x).G.hom (jK (σ.C x).R) z))).asIdeal := hm
    rw [e] at h1
    have h2 : algebraMap σ.R (Localization.Away σ.f) σ.f ∈
      ((σ.C x).y (pullback.snd (σ.C x).G.hom (jK (σ.C x).R) z)).asIdeal := h1
    exact (PrimeSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ h2 (IsLocalization.Away.algebraMap_isUnit σ.f))
  have h := σ.compat x _ (𝟙 _) (IsOpenImmersion.lift (σ.V x).ι _ hr)
    (by rw [Category.id_comp, IsOpenImmersion.lift_fac])
  rw [Category.id_comp] at h
  rw [h, Category.assoc, E.onV, IsOpenImmersion.lift_fac_assoc]

theorem isSemiAbelian_of_ext (hC : σ.Common) (G : Over (Sp σ.R)) [GrpObj G] (κ : G.left ⟶ E.P) [IsOpenImmersion κ]
    (hκ : Set.range κ = E.U) (hG : G.hom = κ ≫ E.p) [Smooth G.hom] [QuasiCompact G.hom] {e : σ.A.left ⟶ G.left}
    (he : e ≫ κ = E.ιA) (h : IsGrpPullback σ.A G (awayMap σ.f) e) : IsSemiAbelian G := by
  have := E.sep
  have hsep : IsSeparated G.hom := by rw [hG]; infer_instance
  have key : ∀ x, ∃ m, IsGrpPullback (σ.C x).G G (σ.C x).ξ m := fun x => by
    obtain ⟨m, hm, sq⟩ := isPullback_chart E hC κ hκ x
    rw [← hG, ← σ.hρ] at sq
    obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing (σ.C x).R (FractionRing (σ.C x).R)
    have := (σ.C x).semi.smooth
    refine ⟨m, ZJ.isGrpPullback_of_dominant (jK (σ.C x).R) sq (((σ.C x).gen.comp h).congr (σ.C x).hy ?_)⟩
    rw [← cancel_mono κ, Category.assoc, Category.assoc, he, hm]
    exact alpha_comp E x
  have fib : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Sp Ω ⟶ Sp σ.R), ∃ (x : Sp σ.R) (q : Sp Ω ⟶ Sp (σ.C x).R)
      (i : (Over.pullback q).obj (σ.C x).G ≅ (Over.pullback p).obj G), IsMonHom i.hom := fun Ω _ _ p => by
    obtain ⟨q, hq⟩ := exists_geom_lift (σ.C (p (closedPoint Ω))) Ω p rfl
    obtain ⟨m, hm⟩ := key (p (closedPoint Ω))
    obtain ⟨i, hi, -⟩ := grpPullback_iso (((isGrpPullback_pullback _ q).comp hm).congr hq rfl)
      (isGrpPullback_pullback G p)
    exact ⟨_, q, i, hi⟩
  refine ⟨?_, ‹_›, hsep, ‹_›, SemiAbelianCompare.geometricallyConnected_of_isAlgClosed _ fun Ω _ _ p => ?_,
    fun Ω _ _ p => ?_⟩
  · have := σ.ab.comm
    have : IsSchemeTheoreticallyDominant (awayMap σ.f) :=
      ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _
        (IsLocalization.injective (Localization.Away σ.f) (powers_le_nonZeroDivisors_of_noZeroDivisors σ.hf))
    exact SplitExtComm.isCommMonObj_of_dominant h
  · obtain ⟨x, q, i, -⟩ := fib Ω p
    have := (σ.C x).semi.geomConnected
    have : ConnectedSpace ((Over.pullback q).obj (σ.C x).G).left :=
      GeometricallyConnected.geometrically_connectedSpace (f := (σ.C x).G.hom) q _ _ (IsPullback.of_hasPullback _ _)
    have := isIso_inv_left i.symm
    exact (i.symm.inv.left).surjective.connectedSpace (i.symm.inv.left).continuous
  · obtain ⟨x, q, i, hi⟩ := fib Ω p
    obtain ⟨T⟩ := (σ.C x).semi.fibres Ω q
    exact ⟨torusExtOfIso i T⟩

end GlobalTheory.Desc.UnionFib

namespace GlobalTheory.Desc

open UnionFib GroupGlue in

theorem Emb.hasExt_of_locGrp : ∀ (σ : Setup) (E : Emb σ), σ.Common → (∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal}) → HasExt (awayMap σ.f) σ.A := by
  intro σ E hC hloc
  choose g hg H iH h hL hr using hloc
  have oi : ∀ x, IsOpenImmersion (h x) := fun x => (hL x).2.2.1
  have ra : ∀ a : σ.R, Set.range (awayMap a) = {z : Sp σ.R | a ∉ z.asIdeal} := fun a =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  have hU : IsOpen E.U := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    exact ⟨Set.range (h (E.p z)), by rw [hr]; exact Set.inter_subset_left, (h _).isOpenEmbedding.isOpen_range,
      by rw [hr]; exact ⟨hz, hg _⟩⟩
  let U : E.P.Opens := ⟨E.U, hU⟩
  have hι : Set.range U.ι = E.U := Scheme.Opens.range_ι U
  let G : Over (Sp σ.R) := Over.mk (U.ι ≫ E.p)
  let 𝒰 : (Sp σ.R).OpenCover := Scheme.Cover.mkOfCovers (Sp σ.R) (fun x => Sp (Localization.Away (g x)))
    (fun x => awayMap (g x)) (fun x => by
      obtain ⟨y, hy⟩ : x ∈ Set.range (awayMap (g x)) := by rw [ra]; exact hg x
      exact ⟨x, y, hy⟩)
  have hs : ∀ x, Set.range (h x) ⊆ Set.range U.ι := fun x => by rw [hι, hr]; exact Set.inter_subset_left
  let H' : ∀ i : 𝒰.I₀, Over (𝒰.X i) := H
  letI iH' : ∀ i : 𝒰.I₀, GrpObj (H' i) := iH
  let ψ : ∀ i : 𝒰.I₀, (H' i).left ⟶ G.left := fun x => IsOpenImmersion.lift U.ι (h x) (hs x)
  have hψι : ∀ x : Sp σ.R, ψ x ≫ U.ι = h x := fun x => IsOpenImmersion.lift_fac _ _ _
  have hψ : ∀ i, IsPullback (ψ i) (H' i).hom G.hom (𝒰.f i) := fun (x : Sp σ.R) => by
    have : IsOpenImmersion (ψ x ≫ U.ι) := by rw [hψι]; exact oi x
    have : IsOpenImmersion (ψ x) := IsOpenImmersion.of_comp _ U.ι
    refine (IsOpenImmersion.isPullback (H x).hom (ψ x) (awayMap (g x)) (U.ι ≫ E.p) ?_ ?_).flip
    · rw [reassoc_of% (hψι x)]; exact (hL x).2.2.2.1
    · ext z
      constructor
      · intro hz
        have hz' : E.p (U.ι z) ∈ Set.range (awayMap (g x)) := hz
        rw [ra] at hz'
        obtain ⟨y, hy⟩ : U.ι z ∈ Set.range (h x) := by rw [hr]; exact ⟨z.2, hz'⟩
        refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
        rw [← hy, ← hψι]; rfl
      · rintro ⟨y, rfl⟩
        refine ⟨(H x).hom y, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← (hL x).2.2.2.1, ← hψι]; rfl
  have op : ∀ x, OpenIn (h x) (H x).hom E.p (awayMap (g x)) := fun x => by
    refine ⟨(hL x).2.2.2.1, ?_⟩
    have : IsOpenImmersion (pullback.lift (h x) (H x).hom (hL x).2.2.2.1 ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; exact oi x
    exact IsOpenImmersion.of_comp _ (pullback.fst E.p (awayMap (g x)))
  have hm : MulCompat ψ := fun (x y : Sp σ.R) S u v a a' b b' e₁ e₂ => by
    have := (hL x).1
    have := (hL y).1
    have k := (GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel σ E _ _ (awayMap (g x)) (awayMap (g y)) (H x) (H y) (h x) (h y) inferInstance inferInstance
      inferInstance inferInstance (op x) (op y) (hL x).2.2.2.2 (hL y).2.2.2.2).1 S u v a a' b b'
      (by rw [← hψι, ← hψι, reassoc_of% e₁]) (by rw [← hψι, ← hψι, reassoc_of% e₂])
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hψι, hψι]
    exact k
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  have hA : Set.range E.ιA ⊆ Set.range U.ι := by rw [hι]; exact range_subset E
  let e : σ.A.left ⟶ G.left := IsOpenImmersion.lift U.ι _ hA
  have he : e ≫ U.ι = E.ιA := IsOpenImmersion.lift_fac _ _ _
  have hp : IsGrpPullback σ.A G (awayMap σ.f) e := by
    refine ⟨isPullback_of_mono U.ι E.cartA he, fun T a b a₀ b₀ ha hb => ?_⟩
    refine ext_small 𝒰 (T.hom ≫ awayMap σ.f) fun (x : Sp σ.R) S k u hu => ?_
    obtain ⟨c, hc⟩ := exists_rep hψ (T := Over.mk (T.hom ≫ awayMap σ.f)) hu a₀
    obtain ⟨d, hd⟩ := exists_rep hψ (T := Over.mk (T.hom ≫ awayMap σ.f)) hu b₀
    rw [← rep_mul hG (T := Over.mk (T.hom ≫ awayMap σ.f)) hu hc hd]
    let r : Over.mk (k ≫ T.hom) ⟶ T := Over.homMk k rfl
    have k' := (hL x).2.2.2.2 S u (k ≫ T.hom) c d (r ≫ a) (r ≫ b)
      (by rw [← hψι, reassoc_of% hc, ha, ← he]; simp [r]) (by rw [← hψι, reassoc_of% hd, hb, ← he]; simp [r])
    rw [← MonObj.comp_mul] at k'
    rw [← cancel_mono U.ι, Category.assoc, hψι, Category.assoc, Category.assoc, he]
    exact k'.trans (Category.assoc _ _ _)
  have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have : IsZariskiLocalAtTarget @QuasiCompact.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have : Smooth G.hom := of_charts @Smooth hψ fun x => (hL x).1
  have : QuasiCompact G.hom := of_charts @QuasiCompact hψ fun x => (hL x).2.1
  exact ⟨G, iG, e, isSemiAbelian_of_ext E hC G U.ι hι rfl he hp, hp⟩

end GlobalTheory.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPowCompAdicCompletionMapToQuotientPow
section
noncomputable section

namespace GlobalTheory.InvAlg

theorem factorPow_evalₐ {A : Type} [CommRing A] (I : Ideal A) {k n : ℕ} (hle : k ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I A x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq]
  have h := x.2 hle
  rw [SModEq.sub_mem] at h
  have hI : (I ^ k • ⊤ : Submodule A A) = I ^ k := by ext; simp
  rw [← neg_sub]
  exact neg_mem (hI ▸ h)

theorem pow_le_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {I : Ideal A} {J : Ideal B}
    (h : I.map f ≤ J) (n : ℕ) : I ^ n ≤ (J ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono h n)

def adicCompletionMapToQuotientPow {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (n : ℕ) : AdicCompletion I A →+* B ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f (pow_le_comap f h n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)

theorem factorPow_comp_adicCompletionMapToQuotientPow {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) {k n : ℕ} (hle : k ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (adicCompletionMapToQuotientPow f I J h n) = adicCompletionMapToQuotientPow f I J h k := by
  ext x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hk : AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r := by
    rw [← factorPow_evalₐ I hle, ← hr]
    rfl
  simp only [adicCompletionMapToQuotientPow, RingHom.comp_apply, RingHom.coe_coe]
  rw [← hr, hk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  rfl

def cmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) : AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J (adicCompletionMapToQuotientPow f I J h) (factorPow_comp_adicCompletionMapToQuotientPow f I J h)

theorem evalₐ_cmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (cmap f I J h x) =
      Ideal.quotientMap (J ^ n) f (pow_le_comap f h n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (factorPow_comp_adicCompletionMapToQuotientPow f I J h) n x

theorem cmap_of {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (a : A) : cmap f I J h (AdicCompletion.of I A a) = AdicCompletion.of J B (f a) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_cmap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

theorem map_algebraMap_le {A B B' : Type} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    (g : B →ₐ[A] B') (J : Ideal A) : (J.map (algebraMap A B)).map (g : B →+* B') ≤ J.map (algebraMap A B') := by
  rw [Ideal.map_map, g.comp_algebraMap]

def galAlg {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (σ : GlobalTheory.Mum.Gal (algebraMap R R')) :
    R' →ₐ[R] R' :=
  { σ.1.toRingHom with commutes' := σ.2 }

@[simp] theorem galAlg_apply {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) (x : R') : galAlg σ x = σ.1 x := rfl

def galTensor {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (O : Type) [CommRing O] [Algebra R O]
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) : TensorProduct R O R' →ₐ[O] TensorProduct R O R' :=
  Algebra.TensorProduct.map (AlgHom.id O O) (galAlg σ)

@[simp] theorem galTensor_tmul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (O : Type) [CommRing O]
    [Algebra R O] (σ : GlobalTheory.Mum.Gal (algebraMap R R')) (x : O) (y : R') :
    galTensor O σ (x ⊗ₜ[R] y) = x ⊗ₜ[R] σ.1 y := rfl

end GlobalTheory.InvAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDatumBaseChangeToCoarserPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsTrans

theorem exists_refactor {X X₁ X₂ A : Scheme.{0}} {L : LB X} {M : LB A} (hL : L.IsLB) (hM : M.IsLB)
    {F₁ : X₁ ⟶ X} {F₂ : X₂ ⟶ X} {φ₁ : A ⟶ X₁} {φ₂ : A ⟶ X₂} (e : φ₁ ≫ F₁ = φ₂ ≫ F₂)
    (w₂ : LB.Iso M ((L.pull F₂).pull φ₂)) (hw₂ : PGen w₂) :
    ∃ w₁ : LB.Iso M ((L.pull F₁).pull φ₁), PGen w₁ ∧
      (∀ (z : A) (J : PUnit → L.ι) (k : M.ι), F₁ (φ₁ z) ∈ L.U (J PUnit.unit) → z ∈ M.U k →
        gw w₁ (𝟙 A) z J k = gw w₂ (𝟙 A) z J k) ∧
      ∀ {Y Y₁ Y₂ B : Scheme.{0}} {u : Y ⟶ X} {u₁ : Y₁ ⟶ X₁} {u₂ : Y₂ ⟶ X₂} {v : B ⟶ A} {h₁ : Y₁ ⟶ Y} {h₂ : Y₂ ⟶ Y}
        {g₁ : B ⟶ Y₁} {g₂ : B ⟶ Y₂} (t : LB.Gen (LB.LinComb L (fun _ : PUnit => u) (fun _ => 1)))
        (t₁ : LB.Gen (LB.LinComb (L.pull F₁) (fun _ : PUnit => u₁) (fun _ => 1)))
        (t₂ : LB.Gen (LB.LinComb (L.pull F₂) (fun _ : PUnit => u₂) (fun _ => 1)))
        (a : LB.Gen (LB.LinComb M (fun _ : PUnit => v) (fun _ => 1))),
        v ≫ φ₁ = g₁ ≫ u₁ → v ≫ φ₂ = g₂ ≫ u₂ → g₁ ≫ h₁ = g₂ ≫ h₂ →
        PMaps (L := L) (F := F₁) (idIso (L.pull F₁)) (fun _ : PUnit => u₁) (fun _ => u) (fun _ => 1) t₁ t h₁ →
        PMaps (L := L) (F := F₂) (idIso (L.pull F₂)) (fun _ : PUnit => u₂) (fun _ => u) (fun _ => 1) t₂ t h₂ →
        PMaps w₂ (fun _ : PUnit => v) (fun _ => u₂) (fun _ => 1) a t₂ g₂ →
        PMaps w₁ (fun _ : PUnit => v) (fun _ => u₁) (fun _ => 1) a t₁ g₁ := by
  have hL₁ : (L.pull F₁).IsLB := LB.isLB_pull hL _
  have hL₂ : (L.pull F₂).IsLB := LB.isLB_pull hL _
  have p₁ := (isGen_iff (L := L) (F := F₁) (idIso _)).1 (idIso_isGen hL₁)
  have p₂ := (isGen_iff (L := L) (F := F₂) (idIso _)).1 (idIso_isGen hL₂)
  obtain ⟨w, T₂⟩ := exists_comp hL₂ (idIso (L.pull F₂)) w₂ p₂ hw₂ hL hM
  have pw := T₂.pgen_comp hL₂ p₂ hw₂
  have a₂ : ∀ (z : A) (J : PUnit → L.ι) (k : M.ι), (φ₂ ≫ F₂) z ∈ L.U (J PUnit.unit) → z ∈ M.U k →
      gw w (𝟙 A) z (J PUnit.unit) k = gw w₂ (𝟙 A) z J k := fun z J k hj hk => by
    have hJ : (𝟙 A ≫ φ₂) z ∈ (L.pull F₂).U J := mem_pull.2 hj
    rw [T₂ _ (𝟙 A) z (J PUnit.unit) J k hj hJ hk]
    have : gw (L := L) (F := F₂) (idIso (L.pull F₂)) (𝟙 A ≫ φ₂) z (J PUnit.unit) J = 1 := gm_self hL₂ _ z hJ
    rw [this, _root_.one_mul]
  have b₂ : ∀ {Y Y₂ B : Scheme.{0}} {u : Y ⟶ X} {u₂ : Y₂ ⟶ X₂} {v : B ⟶ A} {h₂ : Y₂ ⟶ Y}
        {g₂ : B ⟶ Y₂} (t : LB.Gen (LB.LinComb L (fun _ : PUnit => u) (fun _ => 1)))
        (t₂ : LB.Gen (LB.LinComb (L.pull F₂) (fun _ : PUnit => u₂) (fun _ => 1)))
        (a : LB.Gen (LB.LinComb M (fun _ : PUnit => v) (fun _ => 1))),
        v ≫ φ₂ = g₂ ≫ u₂ →
        PMaps (L := L) (F := F₂) (idIso (L.pull F₂)) (fun _ : PUnit => u₂) (fun _ => u) (fun _ => 1) t₂ t h₂ →
        PMaps w₂ (fun _ : PUnit => v) (fun _ => u₂) (fun _ => 1) a t₂ g₂ →
        PMaps w (fun _ : PUnit => v) (fun _ => u) (fun _ => 1) a t (g₂ ≫ h₂) :=
    fun t t₂ a hc H H' => T₂.pmaps_comp hL₂ (fun _ => hc) H H'
  clear T₂
  generalize φ₂ ≫ F₂ = H at e w pw a₂ b₂
  subst e
  obtain ⟨w₁, T₁⟩ := exists_cancel hL (idIso (L.pull F₁)) w p₁ pw hL₁ hM
  refine ⟨w₁, T₁.pgen_cancel hL p₁ pw, fun z J k hj hk => ?_, ?_⟩
  · have hJ : (𝟙 A ≫ φ₁) z ∈ (L.pull F₁).U J := mem_pull.2 hj
    rw [← a₂ z J k hj hk, T₁ _ (𝟙 A) z (J PUnit.unit) J k hj hJ hk]
    have : gw (L := L) (F := F₁) (idIso (L.pull F₁)) (𝟙 A ≫ φ₁) z (J PUnit.unit) J = 1 := gm_self hL₁ _ z hJ
    rw [this, _root_.one_mul]
  · intro Y Y₁ Y₂ B u u₁ u₂ v h₁ h₂ g₁ g₂ t t₁ t₂ a c₁ c₂ c H₁ H₂ H
    exact T₁.pmaps_cancel hL (fun _ => c₁) H₁ (c ▸ b₂ t t₂ a c₂ H₂ H)

theorem gs_locSec {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {δ : LB S}
    {σ : (CechPic.tens L.L (δ.pull G.hom)).Sec} {i : δ.ι} {R : Type} [CommRing R] {ξ : Sp R ⟶ S}
    {t : (KeyVals.bL L ξ).L.Sec} (hξ : ⊤ ≤ ξ ⁻¹ᵁ δ.U i) (ht : KeyVals.IsLocSec σ i ξ t) {Z : Scheme.{0}}
    (q : Z ⟶ (KeyVals.bG G ξ).left) (z : Z) (J : (KeyVals.bL L ξ).L.ι) (hJ : q z ∈ (KeyVals.bL L ξ).L.U J) :
    gs q z _ (t.f J) = gs (q ≫ pullback.fst G.hom ξ) z _ (σ.f (J PUnit.unit, fun _ => i)) := by
  have hle : (KeyVals.bL L ξ).L.U J ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (J PUnit.unit, fun _ => i) := by
    intro p hp
    refine ⟨mem_pull.1 hp, mem_pull.2 ?_⟩
    have e := congrArg (fun g => g p) (pullback.condition (f := G.hom) (g := ξ))
    have h2 : ξ (pullback.snd G.hom ξ p) ∈ δ.U i := hξ (show pullback.snd G.hom ξ p ∈ (⊤ : (Sp R).Opens) from trivial)
    exact e.symm ▸ h2
  rw [ht J hle]
  exact gs_appLE _ _ _ hle q z hJ _

theorem pmaps_bL {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) {R : Type} [CommRing R]
    (ξ : Sp R ⟶ S) : PMaps (L := L.L) (F := pullback.fst G.hom ξ) (idIso (L.L.pull (pullback.fst G.hom ξ))) (K := PUnit)
      (fun _ => eSec (KeyVals.bG G ξ)) (fun _ => eSec G) (fun _ => 1) (KeyVals.bL L ξ).rig L.rig (KeyVals.eb ξ) :=
  (maps_iff _ _ _ _ (KeyVals.bL L ξ).rig L.rig (KeyVals.eb ξ) (KeyVals.bL L ξ).rig
    (rigPull_le (G' := KeyVals.bG G ξ) (pullback.fst G.hom ξ) (KeyVals.eb ξ) (KeyVals.eSec_bG G ξ) L.L)
    (fun _ => rfl)).1 (idIso_maps (KeyVals.bL L ξ))

theorem keyOn_trans : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R R' K : Type) [CommRing R]
    [CommRing R'] [CommRing K] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (f : R' →+* K)
    (t : (KeyVals.bL L ξ).L.Sec) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ)) (t' : (KeyVals.bL L ξ').L.Sec)
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')) (x : KeyIn K) (hg : x.P.g = g),
    spMap r ≫ ξ = ξ' → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → KeyVals.IsLocSec σ i ξ' t' →
    (∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ) →
    KeyOn f x (KeyVals.bG G ξ') (KeyVals.bL L ξ') t' (fun j => y' (j.cast hg)) →
    KeyOn (f.comp r) x (KeyVals.bG G ξ) (KeyVals.bL L ξ) t (fun j => y (j.cast hg)) := by
  intro S G _ _ g L δ σ i R R' K _ _ _ ξ r ξ' f t y t' y' x hg hξ hU ht ht' hy hK
  obtain ⟨φ', he', ψ', F', hφ', hψ', hrig', hsec', hF1, hF2, hFv⟩ := hK
  have hU' : ⊤ ≤ ξ' ⁻¹ᵁ δ.U i := by
    intro p _
    rw [← hξ]
    exact hU (show spMap r p ∈ (⊤ : (Sp R).Opens) from trivial)
  have hP := isGrpPullback_pullback G ξ
  have hP' := isGrpPullback_pullback G ξ'
  obtain ⟨m, hm, hfst, hsnd⟩ : ∃ m : (KeyVals.bG G ξ').left ⟶ (KeyVals.bG G ξ).left,
      IsGrpPullback (KeyVals.bG G ξ') (KeyVals.bG G ξ) (spMap r) m ∧ m ≫ pullback.fst G.hom ξ = pullback.fst G.hom ξ' ∧
        m ≫ (KeyVals.bG G ξ).hom = (KeyVals.bG G ξ').hom ≫ spMap r := by
    have sq : pullback.fst G.hom ξ' ≫ G.hom = (pullback.snd G.hom ξ' ≫ spMap r) ≫ ξ := by
      rw [Category.assoc, hξ]; exact pullback.condition
    refine ⟨pullback.lift _ _ sq, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    refine IsGrpPullback.cancel hP ?_ (pullback.lift_snd _ _ _)
    rw [pullback.lift_fst, hξ]
    exact hP'
  have hφ : IsGrpPullback x.P.A (KeyVals.bG G ξ) (spMap (f.comp r)) (φ' ≫ m) := by
    rw [spMap_comp]
    exact IsGrpPullback.comp hφ' hm
  have he : eSec x.P.A ≫ φ' ≫ m = spMap (f.comp r) ≫ eSec (KeyVals.bG G ξ) := PolBaseChange.eSec_comm hφ
  have e : (φ' ≫ m) ≫ pullback.fst G.hom ξ = φ' ≫ pullback.fst G.hom ξ' := by rw [Category.assoc, hfst]
  obtain ⟨ψ, pψ, hgw, hmap⟩ := exists_refactor L.isLB x.P.isLB e ψ' ((isGen_iff ψ').1 hψ')
  have H' : PMaps ψ' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec (KeyVals.bG G ξ')) (fun _ => 1) x.rig
      (KeyVals.bL L ξ').rig (spMap f) :=
    (maps_iff ψ' _ _ _ x.rig (KeyVals.bL L ξ').rig (spMap f) _
      (rigPull_le (G' := x.P.A) φ' (spMap f) he' (KeyVals.bL L ξ').L) (fun _ => rfl)).1 hrig'
  have c : spMap (f.comp r) ≫ ξ = spMap f ≫ ξ' := by rw [spMap_comp, Category.assoc, hξ]
  have H := hmap L.rig (KeyVals.bL L ξ).rig (KeyVals.bL L ξ').rig x.rig he he' c (pmaps_bL L ξ) (pmaps_bL L ξ') H'
  have hD1 : ∀ a, Chart.dualMapR r (algebraMap R _ a) = algebraMap R' _ (r a) := fun a => by
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have hD2 : Chart.dualMapR r DualNumber.eps = DualNumber.eps := by
    ext <;> simp [Chart.dualMapR]
  refine ⟨φ' ≫ m, he, ψ, F'.comp (Chart.dualMapR r), hφ, (isGen_iff ψ).2 pψ,
    (maps_iff ψ _ _ _ x.rig (KeyVals.bL L ξ).rig (spMap (f.comp r)) _
      (rigPull_le (G' := x.P.A) (φ' ≫ m) (spMap (f.comp r)) he (KeyVals.bL L ξ).L) (fun _ => rfl)).2 H,
    ?_, fun a => ?_, ?_, fun j => ?_⟩
  · refine GlobalTheory.KeyPow.appLE_eq_of_stalk ψ t x.th ?_
    intro z J k hJ hk
    have ha : ((φ' ≫ m) ≫ pullback.fst G.hom ξ) z ∈ L.L.U (J PUnit.unit) :=
      (mem_pull (F := pullback.fst G.hom ξ)).1 hJ
    have ha' : (φ' ≫ pullback.fst G.hom ξ') z ∈ L.L.U (J PUnit.unit) := e ▸ ha
    have hJ' : φ' z ∈ (KeyVals.bL L ξ').L.U J := (mem_pull (F := pullback.fst G.hom ξ')).2 ha'
    have hW : (𝟙 x.P.A.left) z ∈ ((KeyVals.bL L ξ').L.pull φ').U (fun _ => J) ⊓ x.P.L.U k := ⟨mem_pull.2 hJ', hk⟩
    have s2 : gs (𝟙 _ ≫ φ') z _ (t'.f J) = (gw ψ' (𝟙 _) z J k).val * gs (𝟙 _) z _ (x.th.f k) := by
      have e0 := congrArg (gs (𝟙 _) z (((KeyVals.bL L ξ').L.pull φ').U (fun _ => J) ⊓ x.P.L.U k))
        (hsec' (fun _ => J) k (fun x hx => mem_pull.1 hx.1))
      exact (gs_appLE φ' _ _ _ (𝟙 _) z hW _).symm.trans (e0.trans ((gs_mul _ z _ hW _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hW _) (gs_res _ z _ hW _))))
    have e1 := gs_locSec hU ht (𝟙 _ ≫ φ' ≫ m) z J hJ
    have e2 := gs_locSec hU' ht' (𝟙 _ ≫ φ') z J hJ'
    have e3 : (𝟙 _ ≫ φ' ≫ m) ≫ pullback.fst G.hom ξ = (𝟙 _ ≫ φ') ≫ pullback.fst G.hom ξ' := by
      rw [Category.id_comp, Category.id_comp, e]
    rw [e3] at e1
    exact e1.trans (e2.symm.trans (s2.trans (congrArg (fun u : _ˣ => u.val * _) (hgw z J k ha hk).symm)))
  · rw [RingHom.comp_apply, hD1, hF1]; rfl
  · rw [RingHom.comp_apply, hD2, hF2]
  · have hv : (y' (j.cast hg)).left ≫ m = spMap (Chart.dualMapR r) ≫ (y (j.cast hg)).left := by
      refine hP.1.hom_ext ?_ ?_
      · rw [Category.assoc, hfst, Category.assoc]
        exact hy _ hD1 hD2 _
      · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (y' _), Category.assoc, Over.w (y _)]
        show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact RingHom.ext fun a => (hD1 a).symm
    rw [← Category.assoc, hFv j, Category.assoc, hv, spMap_comp, Category.assoc]

end GlobalTheory.KeyValsTrans

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDataBoundStatement
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_data_bound : GlobalTheory.FunPr.Hypotheses₂ → FinDatK := by
  first | exact @GlobalTheory.FunDat.finDatK | exact GlobalTheory.FunDat.finDatK | (intros; apply GlobalTheory.FunDat.finDatK <;> assumption)
end

