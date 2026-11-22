import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeNearPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LocAgree

theorem gs_prod {X Y : Scheme.{0}} {L : LB X} {k : ℕ} (u v : Y ⟶ X) (i i' : Fin 1 → L.ι) (y : Y)
    (hi : u y ∈ secChart L i) (hi' : v y ∈ secChart L i') (s t : H0 L k) :
    gs (𝟙 Y) y (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
        ((Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
          ((u.app (secChart L i)).hom (s.f i)) *
        (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
          ((v.app (secChart L i')).hom (t.f i'))) = secGerm u y s i * secGerm v y t i' := by
  have hy : (𝟙 Y : Y ⟶ Y) y ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := ⟨hi, hi'⟩
  rw [gs_mul _ _ _ hy, gs_res _ _ _ hy, gs_res _ _ _ hy]
  exact congrArg₂ (· * ·) (gs_pull (𝟙 Y) u y _ hi _) (gs_pull (𝟙 Y) v y _ hi' _)

theorem gs_nbhd {Z : Scheme.{0}} {O : Z.Opens} (a b : Γ(Z, O)) (z : Z) (hz : z ∈ O)
    (h : gs (𝟙 Z) z O a = gs (𝟙 Z) z O b) :
    ∃ V : Z.Opens, z ∈ V ∧ V ≤ O ∧ ∀ x ∈ V, gs (𝟙 Z) x O a = gs (𝟙 Z) x O b := by
  rw [gs_eq _ z O hz, gs_eq _ z O hz] at h
  obtain ⟨V, hzV, iU, iV, e⟩ := TopCat.Presheaf.germ_eq Z.presheaf z hz hz _ _ h
  refine ⟨V, hzV, leOfHom iU, fun x hx => ?_⟩
  have hxO : (𝟙 Z : Z ⟶ Z) x ∈ O := leOfHom iU hx
  rw [gs_eq _ x O hxO, gs_eq _ x O hxO]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf iU x hx _).symm.trans
    ((congrArg (Z.presheaf.germ V x hx).hom e).trans (TopCat.Presheaf.germ_res_apply Z.presheaf iV x hx _))

end GlobalTheory.Mum.LocAgree

namespace GlobalTheory.Mum.LocAgree

theorem locAgree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z → ∃ W : Z.Opens, z ∈ W ∧ W.ι ≫ u = W.ι ≫ u' := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₀, hk₀, hK⟩ := GlobalTheory.T.eq_of_sectionRatio_eq_near_thickening_point R hB D A G hG U
  refine ⟨k₀, hk₀, fun e k hk Z u u' hu s₀ i i'' z hg hz => ?_⟩
  obtain ⟨hi, hi'', hunit, hunit', hall⟩ := hg
  set p := (fstG (maximalIdeal R) e G).left with hp
  have hiw : p (u z) ∈ secChart U.LG.L i := hi
  have hunitw : IsUnit (secGerm p (u z) s₀ i) := by
    rw [secGerm_comp u p z s₀ hiw] at hunit
    exact (isUnit_map_iff (u.stalkMap z).hom _).1 hunit
  obtain ⟨N, m, σ, hwN, hmono⟩ := hK e k hk s₀ i (u z) hiw hunitw

  have hz' : z ∈ (u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' := ⟨hi, hi''⟩
  have hV : ∀ l, ∃ V : Z.Opens, z ∈ V ∧ V ≤ (u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' ∧
      ∀ x ∈ V, secGerm (u ≫ p) x (σ l) i * secGerm (u' ≫ p) x s₀ i'' =
        secGerm (u ≫ p) x s₀ i * secGerm (u' ≫ p) x (σ l) i'' := by
    intro l
    obtain ⟨V, hzV, hVO, hx⟩ := gs_nbhd _ _ z hz'
      ((gs_prod (u ≫ p) (u' ≫ p) i i'' z hi hi'' (σ l) s₀).trans ((hall (σ l)).trans
        (gs_prod (u ≫ p) (u' ≫ p) i i'' z hi hi'' s₀ (σ l)).symm))
    refine ⟨V, hzV, hVO, fun x hxV => ?_⟩
    have hxO := hVO hxV
    rw [← gs_prod (u ≫ p) (u' ≫ p) i i'' x hxO.1 hxO.2, ← gs_prod (u ≫ p) (u' ≫ p) i i'' x hxO.1 hxO.2]
    exact hx x hxV
  choose V hzV hVO hVx using hV
  let W : Z.Opens := ⟨(⋂ l, (V l : Set Z)) ∩ ((u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' : Z.Opens)
      ∩ (u ⁻¹ᵁ N : Set Z) ∩ (u' ⁻¹ᵁ N : Set Z),
    (((isOpen_iInter_of_finite fun l => (V l).isOpen).inter (TopologicalSpace.Opens.isOpen _)).inter (TopologicalSpace.Opens.isOpen _)).inter
      (TopologicalSpace.Opens.isOpen _)⟩
  have hzW : z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hzV, hz'⟩, hwN⟩, show u' z ∈ N from hz ▸ hwN⟩
  refine ⟨W, hzW, ?_⟩
  have hmem : ∀ x : W.toScheme, W.ι x ∈ W := fun x => by
    have h : W.ι x ∈ Set.range W.ι := ⟨x, rfl⟩
    rwa [Scheme.Opens.range_ι] at h
  apply hmono W.toScheme (W.ι ≫ u) (W.ι ≫ u')
  · simp only [Category.assoc, hu]
  · intro x; exact (hmem x).1.2
  · intro x; exact (hmem x).2
  · intro l
    refine secRatioEq_of_exists_germ fun x => ⟨i, i'', (hmem x).1.1.2.1, (hmem x).1.1.2.2, ?_⟩
    simp only [Category.assoc]
    rw [secGerm_comp W.ι (u ≫ p) x _ (hmem x).1.1.2.1, secGerm_comp W.ι (u ≫ p) x _ (hmem x).1.1.2.1,
      secGerm_comp W.ι (u' ≫ p) x _ (hmem x).1.1.2.2, secGerm_comp W.ι (u' ≫ p) x _ (hmem x).1.1.2.2,
      ← map_mul, ← map_mul, hVx l _ (Set.mem_iInter.1 (hmem x).1.1.1 l)]

end GlobalTheory.Mum.LocAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreAffine
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AlgConn

namespace GlobalTheory.ZariskiConn

theorem preconnectedSpace_of_isLocalRing (Y : Scheme.{0}) [IsLocalRing Γ(Y, ⊤)] : PreconnectedSpace Y := by
  refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
  obtain ⟨ε, he, hεU⟩ := exists_idempotent_basicOpen_eq_of_isClopen Y U hU
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ε with h | h
  · right
    rw [← hεU, Y.basicOpen_of_isUnit h]
    rfl
  · left
    have h0 : ε = 0 := by
      have h1 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, he, sub_self]
      exact (h.mul_right_eq_zero).1 h1
    rw [← hεU, h0, Scheme.basicOpen_zero]
    rfl

theorem range_thick (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Set.range (thick O (maximalIdeal O) n) = {closedPoint O} := by
  haveI : Nontrivial (O ⧸ maximalIdeal O ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal O).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have key : ∀ Q : PrimeSpectrum (O ⧸ maximalIdeal O ^ (n + 1)),
      thick O (maximalIdeal O) n Q = closedPoint O := by
    intro Q
    refine PrimeSpectrum.ext ?_
    change Q.asIdeal.comap (Ideal.Quotient.mk _) = maximalIdeal O
    have hp : (Q.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal O ^ (n + 1)))).IsPrime := inferInstance
    refine le_antisymm (le_maximalIdeal hp.ne_top) (hp.le_of_pow_le (n := n + 1) fun a ha => ?_)
    change Ideal.Quotient.mk _ a ∈ Q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Q.asIdeal.zero_mem
  ext x
  constructor
  · rintro ⟨Q, rfl⟩
    exact key Q
  · rintro rfl
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (O ⧸ maximalIdeal O ^ (n + 1))
    exact ⟨⟨M, hM.isPrime⟩, key _⟩

theorem isPreconnected_closedFibre (O : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (hI : IsAdicComplete (maximalIdeal O) O) (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [hP : IsProper f]
    [PreconnectedSpace Y] : _root_.IsPreconnected (f ⁻¹' {closedPoint O}) := by
  let ι : ∀ n, pullback f (thick O (maximalIdeal O) n) ⟶ Y := fun n => pullback.fst _ _
  have hTn : ∀ n, Set.range (ι n) = f ⁻¹' {closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (thick O (maximalIdeal O) n)
    rw [range_thick] at h
    exact h
  refine isPreconnected_closed_iff.2 fun A B hA hB hcov ⟨u, hu, huA⟩ ⟨u', hu', hu'B⟩ => ?_
  by_contra hcon
  have hdis : ∀ y, y ∈ f ⁻¹' {closedPoint O} → y ∈ A → y ∈ B → False :=
    fun y h1 h2 h3 => hcon ⟨y, h1, h2, h3⟩
  have hAB : ∀ n, (ι n ⁻¹' A)ᶜ = ι n ⁻¹' B := by
    intro n
    ext x
    have hx : ι n x ∈ f ⁻¹' {closedPoint O} := by rw [← hTn n]; exact ⟨x, rfl⟩
    exact ⟨fun h => (hcov hx).resolve_left h, fun h h' => hdis _ hx h' h⟩
  have hclo : ∀ n, IsClopen (ι n ⁻¹' A) := fun n =>
    ⟨hA.preimage (ι n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (ι n).continuous⟩
  choose h hhp hhU using fun n => GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen O _
    (ι n ≫ f) _ (hclo n)
  haveI : IsProper (Over.mk f).hom := hP
  haveI : IsProper (Over.mk (twoπ O)).hom := isProper_twoπ O
  have htr : ∀ n, thickMap O (maximalIdeal O) n (Over.mk f) ≫ ι (n + 1) = ι n := fun n =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hc : ∀ n, thickMap O (maximalIdeal O) n (Over.mk f) ≫ h (n + 1) = h n := by
    intro n
    refine GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen O _ _ _ ?_ ?_
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (thickMap O (maximalIdeal O) n (Over.mk f) ≫ ·) (hhp (n + 1))).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ f) (htr n)).trans (hhp n).symm
    · refine TopologicalSpace.Opens.ext ?_
      refine Eq.trans ?_ (hhU n).symm
      refine Eq.trans (congrArg (thickMap O (maximalIdeal O) n (Over.mk f) ⁻¹' ·) (hhU (n + 1))) ?_
      rw [← htr n]
      rfl
  obtain ⟨g, hg, -⟩ := GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick
    GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms hI (Over.mk f)
    (Over.mk (twoπ O)) h (fun n => hhp n) hc
  have hW : IsClopen ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) :=
    (isClopen_basicOpen_specProdSelfFirstIdempotent O).preimage g.left.continuous
  have h0 : ι 0 ⁻¹' ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) =
      ι 0 ⁻¹' A := by
    rw [← hhU 0, ← hg 0]
    rfl
  rw [← hTn 0] at hu hu'
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨x', rfl⟩ := hu'
  rcases isClopen_iff.1 hW with hW0 | hW1
  · have hxA : x ∈ ι 0 ⁻¹' A := huA
    rw [← h0, hW0] at hxA
    simp at hxA
  · have hxA : x' ∈ ι 0 ⁻¹'
        ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) := by
      rw [hW1]; trivial
    rw [h0] at hxA
    exact hdis _ (by rw [← hTn 0]; exact ⟨x', rfl⟩) hxA hu'B

theorem exists_complete_flat (X : Scheme.{0}) [IsAffine X] [IsLocallyNoetherian X] (x : X) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsNoetherianRing O) (_ : IsLocalRing O),
      IsAdicComplete (maximalIdeal O) O ∧ ∃ g : Spec (.of O) ⟶ X, Flat g ∧ g (closedPoint O) = x := by
  let B : Type := X.presheaf.stalk x
  let O : Type := AdicCompletion (maximalIdeal B) B
  haveI : IsNoetherianRing O := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B _
  let φ : X.presheaf.stalk x ⟶ CommRingCat.of O := CommRingCat.ofHom (algebraMap B O)
  haveI : IsLocalHom φ.hom := inferInstanceAs (IsLocalHom (algebraMap B O))
  haveI : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _)
  haveI : Flat (X.fromSpecStalk x) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk X x
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map φ ≫ X.fromSpecStalk x, inferInstance, ?_⟩
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := φ))).trans Scheme.fromSpecStalk_closedPoint

theorem isPreconnected_fibre : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) [IsProper f] [IsAffine X]
    [IsLocallyNoetherian X], Function.Bijective f.appTop →
    ∀ x : X, _root_.IsPreconnected (f.base ⁻¹' {x}) := by
  intro X Y f _ _ _ hf x
  obtain ⟨O, _, _, _, hO, g, hg, hx⟩ := exists_complete_flat X x
  haveI : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hf
  have H := IsPullback.of_hasPullback f g
  haveI : IsIso (pullback.snd f g).appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  haveI : IsLocalRing Γ(pullback f g, ⊤) :=
    ((Scheme.ΓSpecIso (.of O)).symm ≪≫ asIso (pullback.snd f g).appTop).commRingCatIsoToRingEquiv.isLocalRing
  haveI := preconnectedSpace_of_isLocalRing (pullback f g)
  have hc := isPreconnected_closedFibre O hO _ (pullback.snd f g)
  have hw : ∀ y, f (pullback.fst f g y) = g (pullback.snd f g y) := fun y => by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hR : pullback.fst f g '' (pullback.snd f g ⁻¹' {closedPoint O}) = f.base ⁻¹' {x} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : pullback.snd f g y = closedPoint O := hy
      change f (pullback.fst f g y) = x
      rw [hw, hy', hx]
    · intro hz
      have h1 : f z = g (closedPoint O) := (show f z = x from hz).trans hx.symm
      obtain ⟨y, hy1, hy2⟩ := Scheme.Pullback.exists_preimage_pullback z _ h1
      exact ⟨y, hy2, hy1⟩
  rw [← hR]
  exact hc.image _ (pullback.fst f g).continuous.continuousOn

end GlobalTheory.ZariskiConn
end
end

