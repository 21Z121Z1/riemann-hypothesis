import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Twist

namespace GlobalTheory.ProperFinite

variable {X X' : Scheme.{0}}

theorem notMem_support_of_subsingleton (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    [Subsingleton Γ(F, V)] {x : X} (hx : x ∈ V) : x ∉ support F := fun h => by
  have h' := (mem_support_iff_primeIdealOf (F := F) hV ⟨x, hx⟩).1 h
  rw [Module.support_eq_empty] at h'
  exact h'

theorem nonempty_coh_pushforward_equiv (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(X', ⊤)]
    (π : X' ⟶ X) (hπ : ∀ r, π.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(X', ⊤) r)
    (E : X'.Modules) [((Scheme.Modules.pushforward π).obj E).IsQuasicoherent] {m : ℕ} {U : Fin m → X.Opens}
    (hc : ⨆ i, U i = ⊤) (hU : ∀ s : Finset (Fin m), s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i))
    (hE : ∀ s : Finset (Fin m), s.Nonempty → ∀ q, 0 < q → Subsingleton (cohOn E (π ⁻¹ᵁ (⨅ i ∈ s, U i)) q))
    (p : ℕ) : Nonempty (coh ((Scheme.Modules.pushforward π).obj E) p ≃ₗ[R] coh E p) := by
  have hc' : π ⁻¹ᵁ ⊤ ≤ ⨆ i, π ⁻¹ᵁ U i := by rw [← Scheme.Hom.preimage_iSup, hc]
  have ha : CechAcyclicMod (π ⁻¹ᵁ ⊤) (fun i => π ⁻¹ᵁ U i) E :=
    (cechAcyclicMod_iff_of_le fun _ => le_top).2 fun s hs q hq => by
      have := hE s hs q hq
      have e : π ⁻¹ᵁ (⊤ ⊓ ⨅ i ∈ s, U i) = ⊤ ⊓ ⨅ i ∈ s, π ⁻¹ᵁ U i := preimage_cechOpen π ⊤ U s
      rwa [← top_inf_eq (⨅ i ∈ s, U i), e, top_inf_eq] at this
  exact ⟨(cechHEquivCoh R hc hU _ p).symm ≪≫ₗ
    ((HomologicalComplex.homologyFunctor _ _ p).mapIso (cechPushforwardIso ⊤ U E hπ)).toLinearEquiv ≪≫ₗ
    cechHEquivCohOn R hc' ha p⟩

theorem eventually_subsingleton_cohOn [IsLocallyNoetherian X] (π : X' ⟶ X) [IsProper π] {L : LB X'}
    (hL : IsAmpleLB L) (E : X'.Modules) [IsFiniteQC E] {V : X.Opens} (hV : IsAffineOpen V) :
    ∀ᶠ n : ℕ in atTop, ∀ q, 0 < q → Subsingleton (cohOn (twist E (lbPow L n)) (π ⁻¹ᵁ V) q) := by
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian π
  have := hL.noetherianSpace
  let j := (π ⁻¹ᵁ V).ι
  let g : (π ⁻¹ᵁ V).toScheme ⟶ Sp Γ(X, V) := π ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g := inferInstanceAs (IsProper (π ∣_ V ≫ hV.isoSpec.hom))
  letI := algebraΓOfHom g
  have hj : IsAmpleLB (L.pull j) := hL.pull_of_isImmersion j
  refine (hj.eventually_subsingleton_coh_twist (f := g) (fun _ => rfl) (E.restrict j)).mono fun n hn q hq => ?_
  have := hn q hq
  obtain ⟨e⟩ := nonempty_iso_of_lbIso (F := E.restrict j) (LB.isLB_pull (isLB_lbPow hL.isLB n) j)
    (isLB_lbPow hj.isLB n) (lbIso_lbPow_pull hL.isLB j n).symm
  let e' : (twist E (lbPow L n)).restrict j ≅ twist (E.restrict j) (lbPow (L.pull j) n) :=
    (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫ Twist.pullbackIso E j (isLB_lbPow hL.isLB n) ≪≫
      (twistFunctor _).mapIso ((Scheme.Modules.restrictFunctorIsoPullback j).app _).symm ≪≫ e
  exact ((cohOn.restrictEquiv ℤ (g := j) (fun r => by simp) _ (π ⁻¹ᵁ V).ι_image_top q).trans
    (cohOn.mapIso ℤ ⊤ q e')).injective.subsingleton

theorem topIso_inv_appTop (π : X' ⟶ X) (V : X.Opens) :
    V.topIso.inv ≫ (π ∣_ V).appTop = π.appLE V ((π ⁻¹ᵁ V).ι ''ᵁ ⊤) (π ⁻¹ᵁ V).ι_image_top.le := by
  rw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, Scheme.Hom.app_eq_appLE]
  exact (congrArg (_ ≫ ·) (π.appLE_map _ _)).trans (π.map_appLE _ _)

theorem isFiniteQC_pushforward [IsLocallyNoetherian X] (π : X' ⟶ X) [IsProper π] {L : LB X'}
    (hL : IsAmpleLB L) (E : X'.Modules) [IsFiniteQC E] : IsFiniteQC ((Scheme.Modules.pushforward π).obj E) := by
  refine ⟨inferInstance, fun V hV => ?_⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian π
  have := hL.noetherianSpace
  let j := (π ⁻¹ᵁ V).ι
  let g : (π ⁻¹ᵁ V).toScheme ⟶ Sp Γ(X, V) := π ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g := inferInstanceAs (IsProper (π ∣_ V ≫ hV.isoSpec.hom))
  letI := algebraΓOfHom g
  have hj : IsAmpleLB (L.pull j) := hL.pull_of_isImmersion j
  have hfin := hj.finite_coh (f := g) (fun _ => rfl) (E.restrict j) 0
  have hfin' := Module.Finite.equiv (cohOn.zeroEquiv Γ(X, V) (E.restrict j) ⊤)
  have hle : j ''ᵁ ⊤ ≤ π ⁻¹ᵁ V := (π ⁻¹ᵁ V).ι_image_top.le
  have ha : ∀ r, algebraMap Γ(X, V) Γ((π ⁻¹ᵁ V).toScheme, ⊤) r = π.appLE V (j ''ᵁ ⊤) hle r := fun r => by
    change (π ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(X, V)).inv r) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, ← CommRingCat.comp_apply, Category.assoc,
      Iso.inv_hom_id_assoc, topIso_inv_appTop]
    rfl
  let ρ : Γ((Scheme.Modules.pushforward π).obj E, V) →ₗ[Γ(X, V)] sectionsOn (E.restrict j) ⊤ :=
    { toFun := fun s => (sectionsOn.toΓ (E.restrict j) ⊤).symm (E.presheaf.map (homOfLE hle).op s)
      map_add' := fun s t => (congrArg _ (map_add (E.presheaf.map (homOfLE hle).op).hom s t)).trans (map_add _ _ _)
      map_smul' := fun r s => (sectionsOn.toΓ (E.restrict j) ⊤).injective (by
        rw [sectionsOn.toΓ_smul, RingHom.id_apply, ha]
        change E.presheaf.map (homOfLE hle).op (π.app V r • (show Γ(E, π ⁻¹ᵁ V) from s)) =
          (j.appIso ⊤).inv (restrictGlobal _ ⊤ (π.appLE V (j ''ᵁ ⊤) hle r)) • E.presheaf.map (homOfLE hle).op s
        rw [Scheme.Modules.map_smul, Scheme.Opens.ι_appIso]
        exact congrArg (· • _) (res_self_ring (X := (π ⁻¹ᵁ V).toScheme) le_top _).symm) }
  have hρ : Function.Bijective ρ :=
    (sectionsOn.toΓ (E.restrict j) ⊤).symm.bijective.comp (res_bijective_of_eq E hle (π ⁻¹ᵁ V).ι_image_top)
  exact Module.Finite.equiv (LinearEquiv.ofBijective ρ hρ).symm

theorem bijective_unit_app (π : X' ⟶ X) {U V : X.Opens} [IsIso (π ∣_ U)] (h : V ≤ U) (hV : IsAffineOpen V)
    (G : X.Modules) [G.IsQuasicoherent] :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app G).app V) := by
  have hi : IsIso (π ∣_ V) := by
    have h₁ : IsIso (π ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
    have h₂ := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict π U (U.ι ⁻¹ᵁ V))).1 h₁
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 h] at h₂
  have hV' : IsAffineOpen (π ⁻¹ᵁ V) := by
    have : IsAffine V := hV
    exact IsAffine.of_isIso (π ∣_ V)
  have hb : Function.Bijective (π.appLE V (π ⁻¹ᵁ V) le_rfl) := by
    have h₀ : IsIso (π ∣_ V).appTop := inferInstanceAs (IsIso ((π ∣_ V).app ⊤))
    have h₁ : IsIso (V.topIso.inv ≫ (π ∣_ V).appTop) := inferInstance
    rw [topIso_inv_appTop, ← π.appLE_map le_rfl (eqToHom (π ⁻¹ᵁ V).ι_image_top).op] at h₁
    have := @IsIso.of_isIso_comp_right _ _ _ _ _ (π.appLE V (π ⁻¹ᵁ V) le_rfl)
      (X'.presheaf.map (eqToHom (π ⁻¹ᵁ V).ι_image_top).op) inferInstance h₁
    exact ConcreteCategory.bijective_of_isIso _
  letI := appLEAlgebra π (le_refl (π ⁻¹ᵁ V))
  letI := appLEModule π ((Scheme.Modules.pullback π).obj G) (le_refl (π ⁻¹ᵁ V))
  haveI := appLE_isScalarTower π ((Scheme.Modules.pullback π).obj G) (le_refl (π ⁻¹ᵁ V))
  have hB := isBaseChange_pullbackSections π G hV' hV le_rfl
  have h₁ : Function.Bijective (pullbackSections π G (le_refl (π ⁻¹ᵁ V))) := by
    let e := (TensorProduct.lid Γ(X, V) Γ(G, V)).symm ≪≫ₗ
      (LinearEquiv.ofBijective (Algebra.linearMap Γ(X, V) Γ(X', π ⁻¹ᵁ V)) hb).rTensor Γ(G, V)
    have he : ⇑(pullbackSections π G (le_refl (π ⁻¹ᵁ V))) = hB.equiv ∘ e := funext fun m => by
      change _ = hB.equiv (algebraMap Γ(X, V) Γ(X', π ⁻¹ᵁ V) 1 ⊗ₜ m)
      rw [map_one, hB.equiv_tmul, one_smul]
    rw [he]
    exact hB.equiv.bijective.comp e.bijective
  exact (Function.Bijective.of_comp_iff' (res_bijective_of_eq ((Scheme.Modules.pullback π).obj G)
    (le_refl (π ⁻¹ᵁ V)) rfl) _).1 h₁

def VanishesSomewhere (E : X.Modules) : Prop :=
  ∃ W : X.Opens, (W : Set X).Nonempty ∧ ∀ V ≤ W, IsAffineOpen V → Subsingleton Γ(E, V)

theorem finite_coh_of_bijective [IsLocallyNoetherian X] (R : Type) [CommRing R] [IsNoetherianRing R]
    [Algebra R Γ(X, ⊤)]
    (ih : ∀ E : X.Modules, IsFiniteQC E → VanishesSomewhere E → ∀ p, Module.Finite R (coh E p))
    {F G : X.Modules} [IsFiniteQC F] [IsFiniteQC G] (φ : F ⟶ G) {W : X.Opens} (hW : (W : Set X).Nonempty)
    (hφ : ∀ V ≤ W, IsAffineOpen V → Function.Bijective (φ.app V)) (hG : ∀ p, Module.Finite R (coh G p)) :
    ∀ p, Module.Finite R (coh F p) := by
  let ψ : F ⟶ kernel (cokernel.π φ) := Abelian.factorThruImage φ
  have hψ : ψ ≫ kernel.ι _ = φ := Abelian.image.fac φ
  have : Epi ψ := inferInstanceAs (Epi (Abelian.factorThruImage φ))
  have h₂ : (ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ) (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  have h₁ : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  have hC := ih (cokernel φ) inferInstance ⟨W, hW, fun V hV ha => by
    refine subsingleton_of_forall_eq 0 fun c => ?_
    obtain ⟨g, rfl⟩ := app_surjective_of_epi_of_isAffineOpen (cokernel.π φ) ha c
    obtain ⟨f, rfl⟩ := (hφ V hV ha).2 g
    change (φ ≫ cokernel.π φ).app V f = 0
    rw [cokernel.condition]
    rfl⟩
  have hK := ih (kernel ψ) inferInstance ⟨W, hW, fun V hV ha => by
    refine subsingleton_of_forall_eq 0 fun c => injective_kernel_ι_app ψ V ((hφ V hV ha).1 ?_)
    change (kernel.ι ψ ≫ φ).app V c = (kernel.ι ψ ≫ φ).app V 0
    rw [show kernel.ι ψ ≫ φ = 0 from (congrArg (_ ≫ ·) hψ.symm).trans (by rw [kernel.condition_assoc, zero_comp])]
    rfl⟩
  exact cohOn.forall_finite₂ R h₁ ⊤ hK (cohOn.forall_finite₁ R h₂ ⊤ hG hC)

theorem finite_coh_of_modification {R : Type} [CommRing R] [IsNoetherianRing R] (f : X ⟶ Sp R) [IsProper f]
    (π : X' ⟶ X) (hP : IsProjOver (π ≫ f)) {U : X.Opens} (hU : (U : Set X).Nonempty) [IsIso (π ∣_ U)]
    (ih : letI := algebraΓOfHom f
      ∀ E : X.Modules, IsFiniteQC E → VanishesSomewhere E → ∀ p, Module.Finite R (coh E p))
    (G : X.Modules) [IsFiniteQC G] : letI := algebraΓOfHom f; ∀ p, Module.Finite R (coh G p) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom (π ≫ f)
  obtain ⟨_, L, hL⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hP
  have : IsProper π := .of_comp π f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  let E := (Scheme.Modules.pullback π).obj G
  obtain ⟨u, hu⟩ := hU
  let σ : U.toScheme ⟶ X' := inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι
  obtain ⟨d, hd, s, hs, -⟩ := hL.exists_affine (σ ⟨u, hu⟩)
  have H : ∀ᶠ n : ℕ in atTop, ∀ I : Finset (Fin m), I.Nonempty → ∀ q, 0 < q →
      Subsingleton (cohOn (twist E (lbPow L n)) (π ⁻¹ᵁ (⨅ i ∈ I, D i)) q) :=
    eventually_all.2 fun I => eventually_all.2 fun hI => eventually_subsingleton_cohOn π hL E (hD' I hI)
  obtain ⟨n, hn⟩ := eventually_atTop.1 H
  have hN := isLB_lbPow hL.isLB (d * (n + 1))
  let t : (lbPow L (d * (n + 1))).Sec := secPow s (n + 1)
  have ht : Out.nonzeroLocus t = Out.nonzeroLocus s := nonzeroLocus_secPow s n.succ_pos
  have := isFiniteQC_twist (F := E) hN
  have := isFiniteQC_pushforward π hL (twist E (lbPow L (d * (n + 1))))
  refine finite_coh_of_bijective R ih ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app G ≫
    (Scheme.Modules.pushforward π).map (secHom E t)) (W := U.ι ''ᵁ (σ ⁻¹ᵁ Out.nonzeroLocus s))
    ⟨u, ⟨u, hu⟩, hs, rfl⟩ (fun V hV ha => ?_) fun p => ?_
  · have h₁ : V ≤ U := hV.trans (U.ι_image_le _)
    have h₂ : π ⁻¹ᵁ V ≤ Out.nonzeroLocus t := fun x hx => by
      obtain ⟨y, hy, e⟩ := hV hx
      have e₁ : (π ∣_ U) ⟨x, h₁ hx⟩ = y := Subtype.ext ((morphismRestrict_base_coe π U _).trans e.symm)
      have e₂ : σ y = x := by
        rw [← e₁]
        exact congrArg (fun q => q (⟨x, h₁ hx⟩ : (π ⁻¹ᵁ U).toScheme)) (IsIso.hom_inv_id_assoc (π ∣_ U) (π ⁻¹ᵁ U).ι)
      rw [ht, ← e₂]
      exact hy
    exact (bijective_secHom_app hN t h₂).comp (bijective_unit_app π h₁ ha G)
  · obtain ⟨e⟩ := nonempty_coh_pushforward_equiv R π (fun _ => rfl) (twist E (lbPow L (d * (n + 1)))) hc hD'
      (hn _ (le_trans n.le_succ (Nat.le_mul_of_pos_left _ hd))) p
    have := hL.finite_coh (f := π ≫ f) (fun _ => rfl) (twist E (lbPow L (d * (n + 1)))) p
    exact Module.Finite.equiv e.symm

theorem support_pushforward_ssubset (ι : X' ⟶ X) [IsClosedImmersion ι] (E : X'.Modules) [E.IsQuasicoherent]
    (h : VanishesSomewhere E) : support ((Scheme.Modules.pushforward ι).obj E) ⊂ Set.range ι := by
  obtain ⟨W, ⟨z, hz⟩, hW⟩ := h
  refine ⟨fun x hx => by_contra fun hx' => ?_, fun hle => ?_⟩
  · obtain ⟨V, hV, hxV, hle⟩ := exists_affine_mem_le
      (U := ⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩) x hx'
    have e : ι ⁻¹ᵁ V = ⊥ := le_bot_iff.1 fun y hy => (hle hy ⟨y, rfl⟩).elim
    have : Subsingleton Γ((Scheme.Modules.pushforward ι).obj E, V) := by
      change Subsingleton Γ(E, ι ⁻¹ᵁ V)
      exact hW _ (e ▸ bot_le) (hV.preimage ι)
    exact notMem_support_of_subsingleton _ hV hxV hx
  · obtain ⟨O, hO, e⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.1 W.isOpen
    obtain ⟨V, hV, hxV, hle'⟩ := exists_affine_mem_le (U := ⟨O, hO⟩) (ι z) (e.ge hz)
    have : Subsingleton Γ((Scheme.Modules.pushforward ι).obj E, V) := by
      change Subsingleton Γ(E, ι ⁻¹ᵁ V)
      exact hW _ (fun y hy => e.le (hle' hy)) (hV.preimage ι)
    exact notMem_support_of_subsingleton _ hV hxV (hle ⟨z, rfl⟩)

theorem finite_coh_of_forall_modification {R : Type} [CommRing R] [IsNoetherianRing R] (f : X ⟶ Sp R) [IsProper f]
    (h : ∀ (Z : Scheme.{0}) [IsIntegral Z] (ι : Z ⟶ X) [IsClosedImmersion ι], ∃ (Z' : Scheme.{0}) (π : Z' ⟶ Z)
      (U : Z.Opens), IsProjOver (π ≫ ι ≫ f) ∧ (U : Set Z).Nonempty ∧ IsIso (π ∣_ U))
    (F : X.Modules) [IsFiniteQC F] : letI := algebraΓOfHom f; ∀ p, Module.Finite R (coh F p) := by
  letI := algebraΓOfHom f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : AlgebraicGeometry.IsNoetherian X := {}
  refine devissage X (fun F => ∀ p, Module.Finite R (coh F p)) (fun F hF p => ?_)
    (fun S hS _ _ h₁ h₃ => cohOn.forall_finite₂ R hS ⊤ h₁ h₃) (fun Z hZ ih G hG p => ?_) F inferInstance
  · have := cohOn.subsingleton_of_isZero hF ⊤ p
    infer_instance
  · have := isIntegral_red hZ
    letI := algebraΓOfHom (redι Z ≫ f)
    obtain ⟨Z', π, U, hP, hU, _⟩ := h _ (redι Z)
    have := finite_coh_of_modification (redι Z ≫ f) π hP hU (fun E hE hv q => by
      have := ih ((Scheme.Modules.pushforward (redι Z)).obj E)
        ⟨inferInstance, fun V hV => finite_sections_pushforward _ _ hV (hF := finite_sections E (hV.preimage _))⟩
        (range_redι Z ▸ support_pushforward_ssubset (redι Z) E hv) q
      exact Module.Finite.equiv (coh.pushforwardEquiv R (g := redι Z) (fun _ => rfl) E q)) G p
    exact Module.Finite.equiv (coh.pushforwardEquiv R (g := redι Z) (fun _ => rfl) G p).symm

end GlobalTheory.ProperFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GardingVectorDerivativeEqGardingVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmVec

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

def fieldDeriv (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (P : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ) where
  toFun X g := fderiv ℝ φ g (-(P * X * P⁻¹) * g)
  map_add' X Y := by
    funext g
    simp only [Pi.add_apply, ← map_add, Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply, ← map_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]

theorem isTest_fderiv {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    IsTest fun g => fderiv ℝ φ g (Y * g) := by
  refine ⟨(hφ.1.fderiv_right (m := ∞) (le_of_eq rfl)).clm_apply (contDiff_const.mul contDiff_id), ?_⟩
  refine HasCompactSupport.intro hφ.2 fun g hg => ?_
  rw [fderiv_of_notMem_tsupport ℝ hg]; rfl

variable {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem hasDerivAt_integral_translate (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}
    (hφ : IsTest φ) (Y : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    HasDerivAt (fun t : ℝ => ∫ g : Formalism.REAL.UJ ε, φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w
      ∂(Formalism.REAL.muG ε)) (gard ε σ (fun g => fderiv ℝ φ g (Y * g)) w) 0 := by
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := continuous_umat
  have hb := continuous_orbit hσ w
  have he : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z)) (Z * NormedSpace.exp (t • Z)) t :=
    fun Z t => hasDerivAt_exp_smul_const' Z t
  have hc : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Continuous fun t : ℝ => NormedSpace.exp (t • Z) :=
    fun Z => continuous_iff_continuousAt.2 fun t => (he Z t).continuousAt
  have hxy : ∀ t : ℝ, NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := fun t => by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).neg_left.smul_left t).smul_right t), ← smul_add]
    simp
  have hC : IsCompact (Set.image2 (· * ·) ((fun t : ℝ => NormedSpace.exp (t • (-Y))) '' Metric.closedBall 0 1)
      (tsupport φ)) := ((isCompact_closedBall (0 : ℝ) 1).image (hc _)).mul hφ.2
  have hK := hemb.isCompact_preimage hC
  set K := (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹' (Set.image2 (· * ·)
    ((fun t : ℝ => NormedSpace.exp (t • (-Y))) '' Metric.closedBall 0 1) (tsupport φ)) with hKdef
  replace hK : IsCompact K := hK
  have hout : ∀ t ∈ Metric.closedBall (0 : ℝ) 1, ∀ g ∉ K, NormedSpace.exp (t • Y) * umat g ∉ tsupport φ :=
    fun t ht g hg hm => hg ⟨_, ⟨t, ht, rfl⟩, _, hm, by
      show _ * (_ * _) = umat g
      rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]⟩
  set μ := Formalism.REAL.muG ε
  let F' : ℝ → Formalism.REAL.UJ ε → H := fun t g =>
    fderiv ℝ φ (NormedSpace.exp (t • Y) * umat g) (Y * NormedSpace.exp (t • Y) * umat g) • σ (umat g) w
  have hF'c : Continuous fun p : ℝ × Formalism.REAL.UJ ε => F' p.1 p.2 := by
    have h1 : Continuous fun p : ℝ × Formalism.REAL.UJ ε => NormedSpace.exp (p.1 • Y) := (hc Y).comp continuous_fst
    have h2 : Continuous fun p : ℝ × Formalism.REAL.UJ ε => umat p.2 := hu.comp continuous_snd
    exact (((hφ.1.continuous_fderiv (by simp)).comp (h1.mul h2)).clm_apply
      ((continuous_const.mul h1).mul h2)).smul (hb.comp continuous_snd)
  obtain ⟨C, hCb⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod hK).exists_bound_of_continuousOn hF'c.continuousOn
  have hint : ∀ t ∈ Metric.closedBall (0 : ℝ) 1, Integrable
      (fun g : Formalism.REAL.UJ ε => φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w) μ := fun t ht =>
    Continuous.integrable_of_hasCompactSupport ((hφ.continuous.comp (continuous_const.mul hu)).smul hb)
      (HasCompactSupport.intro hK fun g hg => by
        rw [image_eq_zero_of_notMem_tsupport (hout t ht g hg), zero_smul])
  have e0 : F' 0 = fun g : Formalism.REAL.UJ ε => fderiv ℝ φ (umat g) (Y * umat g) • σ (umat g) w := by
    funext g; simp [F']
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun t g => φ (NormedSpace.exp (t • Y) * umat g) • σ (umat g) w) (F' := F')
    (bound := K.indicator fun _ => C) (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    (by filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
        exact (hint t ht).aestronglyMeasurable)
    (hint 0 (Metric.mem_closedBall_self zero_le_one))
    (by rw [e0]; exact ((isTest_fderiv hφ Y).integrable hb).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g t ht => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg]; exact hCb (t, g) ⟨ht, hg⟩
      · rw [Set.indicator_of_notMem hg]
        simp [F', fderiv_of_notMem_tsupport ℝ (hout t ht g hg)])
    ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Filter.Eventually.of_forall fun g t _ =>
      (((hφ.1.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t ((he Y t).mul_const (umat g))).smul_const _)
  rw [e0] at key
  exact key.2

theorem dRep_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ φ, IsTest φ → ∃ ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ), ∀ X, IsTest (ψ X) ∧ (X ∈ lieG G → ∀ w, dRep (trRep σ P) X (gard ε σ φ w) = gard ε σ (ψ X) w) := by
  intro n ε H _ _ _ σ P G hP h hσ φ hφ
  refine ⟨fieldDeriv φ P, fun X => ⟨isTest_fderiv hφ _, fun hX w => ?_⟩⟩
  refine Eq.trans ?_ (hasDerivAt_integral_translate hσ hφ (-(P * X * P⁻¹)) w).deriv
  unfold dRep
  congr 1
  funext t
  rw [gard_eq hσ hφ]
  refine GlobalTheory.LowTypeRestriction.garding_translate hσ hφ.continuous hφ.2 w
    (conj_mem_UJ hP h (exp_mem_UH (gram_unit hP h) hX t)) ?_
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.exp_add_of_commute _ _ (((Commute.refl (P * X * P⁻¹)).neg_left.smul_left t).smul_right t), ← smul_add]
  simp

end GlobalTheory.SmVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.PlaceVec

open GlobalTheory.AdelicLatMove

variable {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem frMapAdj_eq (x : WO S T) : frMapAdj S T βS βT x =
    ((βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) * ((x.map (toEAf D)).map (cF D))ᵀ * (T.gram.map (eToEAf D) * βT.val) := by
  have e : ((x.map (cA D))ᵀ).map (toEAf D) = ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => toEAf_cA _
  unfold frMapAdj
  rw [Matrix.map_mul, Matrix.map_mul, e]
  simp only [Matrix.mul_assoc]
  rfl

theorem frMapAdj_add (x y : WO S T) : frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  have e : (((x + y).map (toEAf D)).map (cF D))ᵀ = ((x.map (toEAf D)).map (cF D))ᵀ + ((y.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => ((cF D).comp (toEAf D)).map_add (x j i) (y j i)
  rw [frMapAdj_eq, frMapAdj_eq, frMapAdj_eq, e, Matrix.mul_add, Matrix.add_mul]

theorem cF_cF_toEAf (a : AE D) : cF D (cF D (toEAf D a)) = toEAf D a := by
  rw [← toEAf_cA, ← toEAf_cA, GlobalTheory.DualPairCheck.cA_cA]

theorem sandwich_cancel {R : Type} [CommRing R] {m n : ℕ} (A A' G G' : Matrix (Fin m) (Fin m) R)
    (B B' H H' : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin m) (Fin n) R) (hA : A * A' = 1) (hG : G * G' = 1)
    (hB : B * B' = 1) (hH : H * H' = 1) : (G * A) * ((A' * G') * N * (H * B)) * (B' * H') = N := by
  calc _ = (G * (A * A') * G') * N * (H * (B * B') * H') := by simp only [Matrix.mul_assoc]
    _ = N := by rw [hA, hB, Matrix.mul_one, Matrix.mul_one, hG, hH, Matrix.one_mul, Matrix.mul_one]

theorem gram_map_mul_inv : S.gram.map (eToEAf D) * (S.gram⁻¹).map (eToEAf D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem frMapAdj_up : ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (x.map (toEAf D)) → IsIntM (k • frMapAdj S T βS βT x) := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_mul_int ((βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) (T.gram.map (eToEAf D) * βT.val)
  refine ⟨k, hk, fun x hx => ?_⟩
  rw [frMapAdj_eq]
  exact h _ fun i j => cF_mem_int (hx j i)

theorem frMapAdj_down :
    ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (frMapAdj S T βS βT x) → IsIntM (k • x.map (toEAf D)) := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_mul_int (S.gram.map (eToEAf D) * βS.val) ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))
  refine ⟨k, hk, fun x hx i j => ?_⟩
  have h1 := h _ hx
  rw [frMapAdj_eq, sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv (gram_map_mul_inv S) βT.mul_inv
    (gram_map_mul_inv T)] at h1
  have h2 : cF D (k • cF D (toEAf D (x i j))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := cF_mem_int (h1 j i)
  rw [nsmul_eq_mul, RingHom.map_mul, map_natCast, cF_cF_toEAf, ← nsmul_eq_mul] at h2
  exact h2

theorem thPVecExists : ∀ D : D7, ThPVecExists D := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ hS hT _ _ _ ⟨e, he⟩ f₀ hf₀
  classical
  have hinf := infPart_cA (idemSum_infPart he)
  obtain ⟨f, hf⟩ := exists_isThetaAt hf₀.1 hS hT (a := cA D e) (by rw [← RingHom.map_mul, idemSum_mul_self he]) hinf
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf₀.1 S T ΛS ΛT hS hT _ e he f₀ hf₀.2.theta hf₀.2.lat).2
    (isSBHalf_of_red hS.1 hT.1 hinf (frMapAdj S T βS βT) (frMapAdj_add S T βS βT) (frMapAdj_up S T βS βT)
      (frMapAdj_down S T βS βT) (Pg ∪ Q) (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
        rw [omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)])
  exact ⟨f, hf₀, e, he, hf⟩

end GlobalTheory.PlaceVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem isKFin_dRep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε,
      IsKFin ε σ (dRep σ X v) := by
  intro n ε H _ _ _ σ h v hv X hX
  obtain ⟨S, h1, h2, h3⟩ := hv
  have hS : S ≤ smooth (Jm ε) σ := fun s hs => h.2.2.1 s ⟨S, h1, hs, h3⟩
  let b := Module.finBasis ℝ (lie (Jm ε))
  let L : Fin (Module.finrank ℝ (lie (Jm ε))) → (S →ₗ[ℂ] H) := fun i =>
    (smooth (Jm ε) σ).subtype ∘ₗ dOp (isUnit_Jm ε) h.1 (b i).2 ∘ₗ Submodule.inclusion hS
  have hL : ∀ i (s : S), L i s = dRep σ (b i) s := fun _ _ => rfl
  let T : Submodule ℂ H := ⨆ i, LinearMap.range (L i)
  have hT : ∀ Y ∈ lieSet ε, ∀ s ∈ S, dRep σ Y s ∈ T := by
    intro Y hY s hs
    have e : Y = ∑ i, b.repr ⟨Y, hY⟩ i • (b i : Mx n) := by
      have := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
      simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using this.symm
    rw [e, h.dRep_sum (fun i => (b i).2) (hS hs)]
    refine T.sum_mem fun i _ => T.smul_mem _ ?_
    exact Submodule.mem_iSup_of_mem i ⟨⟨s, hs⟩, rfl⟩
  refine ⟨T, inferInstance, hT X hX v h2, fun k hk w hw => ?_⟩
  have hg := K_le_UJ hk
  have : T ≤ T.comap (σ k : H →ₗ[ℂ] H) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    have hinv : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv (mul_inv_UJ hg)
    have hY : k * (b i : Mx n) * k⁻¹ ∈ lieSet ε := by
      have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) (b i).2
      rwa [hinv] at this
    have e := Dw_translate h.1 hg (hS s.2) (l := [k * (b i : Mx n) * k⁻¹]) (by simpa using hY)
    have e2 : k⁻¹ * (k * (b i : Mx n) * k⁻¹) * k = b i := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_UJ hg, one_mul, mul_assoc, inv_mul_UJ hg, mul_one]
    simp only [Dw, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, e2] at e
    show σ k (dRep σ (b i) s) ∈ T
    rw [← e]
    exact hT _ hY _ (h3 k hk s s.2)
  exact this hw

end GlobalTheory.TypeSum
end

