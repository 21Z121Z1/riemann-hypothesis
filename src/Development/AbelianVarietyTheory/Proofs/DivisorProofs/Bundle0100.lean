import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexInfConjEqFinprodRestrictedProduct
section
open Filter
open scoped Classical

namespace GlobalTheory

theorem relIndex_inf_conj_eq_finprod_of_restricted_product
    (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (K T C : Subgroup G) (KH TH CH : ∀ i, Subgroup (H i)) (g : G)
    (hglue : ∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i)
    (hT : ∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i)
    (hC : ∀ x, x ∈ C ↔ x ∈ T ∧ ∀ i, p i x ∈ CH i)
    (hCT : ∀ i, CH i ≤ TH i)
    (_hloc : ∀ i, TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom ≤ CH i ∧
      (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) ≠ 0)
    (hCK : ∀ᶠ i in cofinite, CH i ≤ KH i) :
    (T ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex C =
      ∏ᶠ i, (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) := by
  have hfin : {i | ¬ (p i g ∈ KH i ∧ CH i ≤ KH i)}.Finite :=
    Filter.eventually_cofinite.1 ((hcof g).and hCK)
  set S : Finset ι := hfin.toFinset with hS
  have hSn : ∀ i, i ∉ S → p i g ∈ KH i ∧ CH i ≤ KH i := by
    intro i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have hmem : ∀ i (y : H i), y ∈ (KH i).map (MulAut.conj (p i g)).toMonoidHom ↔
      (p i g)⁻¹ * y * p i g ∈ KH i := by
    intro i y
    rw [Subgroup.mem_map_equiv]
    simp
  have hmemG : ∀ x : G, x ∈ K.map (MulAut.conj g).toMonoidHom ↔
      ∀ i, (p i g)⁻¹ * p i x * p i g ∈ KH i := by
    intro x
    rw [Subgroup.mem_map_equiv, hK]
    simp
  have hle : ∀ i, i ∉ S → CH i ≤ TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom := by
    intro i hi y hy
    obtain ⟨h1, h2⟩ := hSn i hi
    exact ⟨hCT i hy, (hmem i y).2 (mul_mem (mul_mem (inv_mem h1) (h2 hy)) h1)⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  swap
  · intro i hi
    by_contra h
    exact hi (Subgroup.relIndex_eq_one.2 (hle i h))
  let φ : C →* (∀ i : S, CH i) :=
    { toFun := fun x i => ⟨p i x, ((hC x).1 x.2).2 i⟩
      map_one' := by ext i; simp
      map_mul' := by intro x y; ext i; simp }
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hglue (fun i => if h : i ∈ S then (y ⟨i, h⟩ : H i) else 1) (by
      refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
      intro i hi
      by_contra h
      apply hi
      have h' : i ∉ S := h
      simp [h'])
    have hxC : ∀ i, p i x ∈ CH i := by
      intro i
      rw [hx]
      split_ifs with h
      · exact (y ⟨i, h⟩).2
      · exact one_mem _
    refine ⟨⟨x, (hC x).2 ⟨(hT x).2 fun i => hCT i (hxC i), hxC⟩⟩, ?_⟩
    funext i
    apply Subtype.ext
    show p i x = _
    rw [hx]
    simp
  have hcomap : (T ⊓ K.map (MulAut.conj g).toMonoidHom).subgroupOf C =
      (Subgroup.pi Set.univ (fun i : S =>
        (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).subgroupOf (CH i))).comap φ := by
    ext x
    have hx := (hC x).1 x.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Subgroup.mem_inf, hmemG]
    constructor
    · rintro ⟨h1, h2⟩ i _
      exact ⟨(hT x).1 h1 i, (hmem i _).2 (h2 i)⟩
    · intro h
      refine ⟨hx.1, fun i => ?_⟩
      by_cases hi : i ∈ S
      · exact (hmem i _).1 (h ⟨i, hi⟩ trivial).2
      · exact (hmem i _).1 (hle i hi (hx.2 i)).2
  have hpi : ∀ L : ∀ i : S, Subgroup (CH i),
      (Subgroup.pi Set.univ L).index = ∏ i, (L i).index := by
    intro L
    simp_rw [Subgroup.index, ← Nat.card_pi]
    refine Nat.card_congr
      ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
    rw [QuotientGroup.leftRel_pi]
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hφ, hpi,
    ← Finset.prod_coe_sort S]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapNsmulComapEqAbsNormDet
section
open NumberField Module

namespace GlobalTheory

theorem exists_basis_closure_eq_of_fg_of_nsmul_mem {Γ : Type} [AddCommGroup Γ] [Module ℚ Γ]
    (A : AddSubgroup Γ) (hA : A.FG) (hN : ∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ Γ), A = AddSubgroup.closure (Set.range b) := by
  classical
  have : IsAddTorsionFree Γ := .of_module_rat Γ
  have : Module.Finite ℤ A :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg A).mpr hA)
  let bA := Module.finBasis ℤ A
  let v : Fin (Module.finrank ℤ A) → Γ := fun i => (bA i : Γ)
  have hliZ : LinearIndependent ℤ v :=
    bA.linearIndependent.map' A.subtype.toIntLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hli : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hcl : A = AddSubgroup.closure (Set.range v) := by
    apply le_antisymm
    · intro a ha
      have h' : a = ∑ i, bA.repr ⟨a, ha⟩ i • v i := by
        conv_lhs => rw [show a = ((⟨a, ha⟩ : A) : Γ) from rfl, ← bA.sum_repr ⟨a, ha⟩]
        rw [AddSubgroup.val_finsetSum]
        simp [v]
      rw [h']
      exact AddSubgroup.sum_mem _ fun i _ =>
        AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact (bA i).2
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    intro x _
    obtain ⟨N, hN0, hNx⟩ := hN x
    have hmem : N • x ∈ Submodule.span ℚ (Set.range v) := by
      rw [hcl] at hNx
      exact (AddSubgroup.closure_le (Submodule.span ℚ (Set.range v)).toAddSubgroup).mpr
        Submodule.subset_span hNx
    rw [← Nat.cast_smul_eq_nsmul ℚ] at hmem
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
    have := Submodule.smul_mem _ (N : ℚ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hN', one_smul] at this
  refine ⟨Module.finrank ℤ A, Basis.mk hli hsp, ?_⟩
  rw [Basis.coe_mk]
  exact hcl

theorem relIndex_map_nsmul_comap_eq_abs_norm_det :
    ∀ (E Γ : Type) [Field E] [NumberField E] [AddCommGroup Γ] [Module E Γ] [FiniteDimensional E Γ] (A : AddSubgroup Γ), A.FG → (∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) → ∀ (m : Module.End E Γ) (N : ℕ), N ≠ 0 → LinearMap.det m ≠ 0 → (∀ x ∈ A, N • m x ∈ A) → (((A.map (N • AddMonoidHom.id Γ)).relIndex (A.comap m.toAddMonoidHom) : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ Module.finrank E Γ * LinearMap.det m)| := by
  intro E Γ _ _ _ _ _ A hA hAN m N hN0 hdet hmA
  classical
  letI : Module ℚ Γ := Module.compHom Γ (algebraMap ℚ E)
  have : IsScalarTower ℚ E Γ := ⟨fun q c x => by
    show (q • c) • x = algebraMap ℚ E q • (c • x)
    rw [Algebra.smul_def, mul_smul]⟩
  obtain ⟨n, b, hb⟩ := exists_basis_closure_eq_of_fg_of_nsmul_mem A hA hAN
  have : FiniteDimensional ℚ Γ := Module.Finite.of_basis b
  let mQ : Γ →ₗ[ℚ] Γ := m.restrictScalars ℚ
  have hdetQ : LinearMap.det mQ = Algebra.norm ℚ (LinearMap.det m) :=
    LinearMap.det_restrictScalars
  have hdetQ0 : LinearMap.det mQ ≠ 0 := by
    rw [hdetQ]
    exact Algebra.norm_ne_zero_iff.mpr hdet
  have hu : IsUnit mQ := (LinearMap.isUnit_iff_isUnit_det mQ).mpr (isUnit_iff_ne_zero.mpr hdetQ0)
  let e : Γ ≃ₗ[ℚ] Γ := LinearEquiv.ofBijective mQ ((Module.End.isUnit_iff mQ).mp hu)
  have he : ∀ x, e x = m x := fun x => rfl
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  let b₁ : Basis (Fin n) ℚ Γ := b.map (LinearEquiv.smulOfNeZero ℚ Γ (N : ℚ) hN')
  let b₂ : Basis (Fin n) ℚ Γ := b.map e.symm
  have hb₁ : ∀ i, b₁ i = N • b i := fun i => by
    simp [b₁, Nat.cast_smul_eq_nsmul]
  have h₁ : A.map (N • AddMonoidHom.id Γ) = AddSubgroup.closure (Set.range b₁) := by
    rw [hb, AddMonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext x
    simp [hb₁]
  have h₂ : A.comap m.toAddMonoidHom = AddSubgroup.closure (Set.range b₂) := by
    have hr : Set.range b₂ = e.symm.toLinearMap.toAddMonoidHom '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← AddMonoidHom.map_closure, ← hb]
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map]
    constructor
    · intro hx
      exact ⟨m x, hx, by rw [← he]; exact e.symm_apply_apply x⟩
    · rintro ⟨a, ha, rfl⟩
      change m (e.symm a) ∈ A
      rw [← he, e.apply_symm_apply]
      exact ha
  have hle : A.map (N • AddMonoidHom.id Γ) ≤ A.comap m.toAddMonoidHom := by
    rintro _ ⟨a, ha, rfl⟩
    change m (N • a) ∈ A
    rw [map_nsmul]
    exact hmA a ha
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hle b₁ b₂ h₁ h₂]
  congr 1
  have hcomp : e.symm.symm ∘ b₁ = ((N : ℚ) • mQ) ∘ b := by
    funext i
    simp only [Function.comp_apply, LinearEquiv.symm_symm, hb₁, LinearMap.smul_apply,
      Nat.cast_smul_eq_nsmul]
    rw [he, map_nsmul]
    rfl
  rw [Basis.det_map, hcomp, Basis.det_comp, Basis.det_self, mul_one, LinearMap.det_smul, hdetQ,
    map_mul, map_pow, ← map_natCast (algebraMap ℚ E), Algebra.norm_algebraMap, ← pow_mul,
    Module.finrank_mul_finrank]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelSpecMapIsIsoOverBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

set_option autoImplicit false
noncomputable section

namespace GlobalTheory

theorem isIso_specMap_restrict_basicOpen_of_bijective {R S : CommRingCat.{0}} (f : R ⟶ S) (r : R)
    (h : Function.Bijective (Localization.awayMap f.hom r)) :
    IsIso (Spec.map f ∣_ (PrimeSpectrum.basicOpen r : (Spec R).Opens)) := by
  set φ := Spec.map f with hφ
  set g : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv r with hg
  have hbo : (PrimeSpectrum.basicOpen r : (Spec R).Opens) = (Spec R).basicOpen g :=
    (basicOpen_eq_of_affine (R := R) r).symm
  rw [hbo]
  have hU := isAffineOpen_top (Spec R)
  have hpre : IsAffineOpen (φ ⁻¹ᵁ (⊤ : (Spec R).Opens)) := by
    simpa using isAffineOpen_top (Spec S)
  have nat : ∀ x : R, (φ.app ⊤).hom ((Scheme.ΓSpecIso R).inv x) =
      (Scheme.ΓSpecIso S).inv (f x) := fun x =>
    (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality f)).symm
  have hi := (IsLocalization.Away.map_injective_iff (S := Localization.Away r)
    (Q := Localization.Away (f.hom r)) f.hom r).mp h.1
  have hs := (IsLocalization.Away.map_surjective_iff (S := Localization.Away r)
    (Q := Localization.Away (f.hom r)) f.hom r).mp h.2
  rw [isIso_morphismRestrict_iff_isIso_app _ (hU.basicOpen g),
    hU.app_basicOpen_eq_away_map φ hpre g]
  refine IsIso.comp_isIso' ?_ inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  have := hU.isLocalization_basicOpen g
  have := hpre.isLocalization_basicOpen ((φ.app ⊤).hom g)
  constructor
  · refine (IsLocalization.Away.map_injective_iff _ _ _).2 fun a ha => ?_
    obtain ⟨x, rfl⟩ : ∃ x, (Scheme.ΓSpecIso R).inv x = a :=
      ⟨(Scheme.ΓSpecIso R).hom a, Iso.hom_inv_id_apply _ _⟩
    rw [nat] at ha
    have hx : f x = 0 := by
      have := congrArg (Scheme.ΓSpecIso S).hom ha
      rw [Iso.inv_hom_id_apply] at this
      exact this.trans (map_zero _)
    obtain ⟨n, hn⟩ := hi x hx
    exact ⟨n, by rw [hg, ← map_pow, ← map_mul, hn, map_zero]⟩
  · refine (IsLocalization.Away.map_surjective_iff _ _ _ _).2 fun b => ?_
    obtain ⟨y, rfl⟩ : ∃ y, (Scheme.ΓSpecIso S).inv y = b :=
      ⟨(Scheme.ΓSpecIso S).hom b, Iso.hom_inv_id_apply _ _⟩
    obtain ⟨c, m, e⟩ := hs y
    exact ⟨(Scheme.ΓSpecIso R).inv c, m, by
      rw [nat, hg, nat]
      exact (congrArg (Scheme.ΓSpecIso S).inv.hom e).trans
        ((map_mul _ _ _).trans (congrArg (· * _) (map_pow _ _ _)))⟩

set_option backward.isDefEq.respectTransparency false in

theorem relSpec_map_isIso_over_basicOpen : ∀ (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F), α' ≫ ι = α → ∀ (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued), g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase → (∀ V, (relativeGluingData hα).cover.f V ≫ g = Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V) → ∀ (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V)), Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b) → ∀ (W : (relativeGluingData hα').glued.Opens), (W : Set (relativeGluingData hα').glued) = (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V)))) → IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) = (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) : Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by
  intro X F F' α α' hα hα' ι hαι g hg hg' V b hb W hW
  haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI := (relativeGluingData hα).cover.map_prop V
  haveI := (relativeGluingData hα').cover.map_prop V
  set φ := Spec.map (ι.app (Opposite.op V)) with hφ
  have hnat : (relativeGluingData hα).natTrans.app V =
      φ ≫ (relativeGluingData hα').natTrans.app V := by
    subst hαι
    simp [relativeGluingData, hφ, Spec.map_comp]
  have H : IsPullback φ ((relativeGluingData hα).cover.f V) ((relativeGluingData hα').cover.f V) g := by
    refine IsPullback.of_right ?_ (hg' V).symm ((relativeGluingData hα').isPullback_natTrans_ι_toBase V)
    rw [← hnat, hg]
    exact (relativeGluingData hα).isPullback_natTrans_ι_toBase V
  have hW' : W = (relativeGluingData hα').cover.f V ''ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) := by
    ext1; exact hW
  subst hW'
  have h1 := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H
    (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens)
  have hpre : φ ⁻¹ᵁ (PrimeSpectrum.basicOpen b : (Spec (F'.obj (Opposite.op V))).Opens) =
      PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) := by
    ext x; rfl
  refine ⟨?_, ?_⟩
  · set D' : (Spec (F'.obj (Opposite.op V))).Opens := PrimeSpectrum.basicOpen b with hD'
    have H₂ := (isPullback_morphismRestrict φ D').paste_vert H
    haveI : IsIso (φ ∣_ D') := isIso_specMap_restrict_basicOpen_of_bijective _ b hb
    haveI : IsIso (pullback.snd g (D'.ι ≫ (relativeGluingData hα').cover.f V)) := by
      rw [← H₂.flip.isoPullback_inv_snd]
      infer_instance
    have hr : (D'.ι ≫ (relativeGluingData hα').cover.f V).opensRange =
        (relativeGluingData hα').cover.f V ''ᵁ D' := by
      ext1
      rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.Opens.range_ι]
      rfl
    have := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictOpensRange g (D'.ι ≫ (relativeGluingData hα').cover.f V))).mpr
      (show IsIso _ from inferInstance)
    rw [hr] at this
    exact this
  · rw [← h1, hpre]
    rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulTrace
section
open NumberField

namespace GlobalTheory
namespace RepTrace

theorem isUnit_of_ne_zero {E : Type} [Field E] [NumberField E] {P : Type} [CommRing P] [Algebra ℚ P]
    (g : 𝓞 E →+* P) (b : 𝓞 E) (hb : b ≠ 0) : IsUnit (g b) := by
  have hI : Ideal.span {b} ≠ ⊥ := by simpa using hb
  have hn : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {b}))
  set n := Ideal.absNorm (Ideal.span {b})
  have hu : IsUnit (g b * g c) := by
    rw [← map_mul, ← hc, map_natCast]
    have h1 : (n : P) = algebraMap ℚ P (n : ℚ) := by simp
    rw [h1]
    exact (isUnit_iff_ne_zero.2 (by exact_mod_cast hn : (n : ℚ) ≠ 0)).map _
  exact isUnit_of_mul_isUnit_left hu

theorem trace_lsmul_restrictScalars {K L V : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V] [FiniteDimensional L V] (a : L) :
    LinearMap.trace K V ((LinearMap.lsmul L V a).restrictScalars K) =
      (Module.finrank L V : K) * Algebra.trace K L a := by
  classical
  let b := Module.finBasis L V
  let c := Module.finBasis K L
  rw [LinearMap.trace_eq_matrix_trace K (c.smulTower b), Algebra.trace_eq_matrix_trace c]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.smulTower_repr_mk, smul_smul, Finsupp.single_apply, Finset.mul_sum, mul_comm]

end RepTrace

theorem repTrace_eq_mul_trace {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (s : ℕ)
    (hr : r = s * Module.finrank ℚ E) (a : 𝓞 E) : (ρ a).trace = s * Algebra.trace ℤ (𝓞 E) a := by
  classical
  let g : 𝓞 E →+* Module.End ℚ (Fin r → ℚ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp
      ((Int.castRingHom ℚ).mapMatrix.comp ρ)
  let A := Algebra.adjoin ℚ (Set.range g)
  letI : CommRing A := Algebra.adjoinCommRingOfComm ℚ (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])
  let g' : 𝓞 E →+* A := g.codRestrict A (fun x => Algebra.subset_adjoin ⟨x, rfl⟩)
  let φ : E →+* Module.End ℚ (Fin r → ℚ) :=
    (A.val : A →ₐ[ℚ] Module.End ℚ (Fin r → ℚ)).toRingHom.comp
      (IsLocalization.lift (M := nonZeroDivisors (𝓞 E)) (S := E) (g := g')
        (fun y => RepTrace.isUnit_of_ne_zero g' y (nonZeroDivisors.ne_zero y.2)))
  letI : Module E (Fin r → ℚ) := Module.compHom (Fin r → ℚ) φ
  have hφq : φ.comp (algebraMap ℚ E) = algebraMap ℚ (Module.End ℚ (Fin r → ℚ)) := Subsingleton.elim _ _
  haveI : IsScalarTower ℚ E (Fin r → ℚ) := ⟨fun q x v => by
    change φ (q • x) v = q • φ x v
    rw [Algebra.smul_def, map_mul, Module.End.mul_apply]
    have := RingHom.congr_fun hφq q
    simp only [RingHom.comp_apply] at this
    rw [this, Module.algebraMap_end_apply]⟩
  haveI : FiniteDimensional E (Fin r → ℚ) := Module.Finite.of_restrictScalars_finite ℚ E _
  have hfin : Module.finrank E (Fin r → ℚ) = s := by
    have h := Module.finrank_mul_finrank ℚ E (Fin r → ℚ)
    rw [Module.finrank_fin_fun] at h
    have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h2 : Module.finrank ℚ E * Module.finrank E (Fin r → ℚ) = Module.finrank ℚ E * s := by
      rw [h, hr, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hd h2
  have key : LinearMap.trace ℚ (Fin r → ℚ) (g a) = ((ρ a).trace : ℚ) := by
    change LinearMap.trace ℚ _ (Matrix.toLin' ((ρ a).map (Int.castRingHom ℚ))) = _
    rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin r)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    simp [Matrix.trace]
  have hga : g a = (LinearMap.lsmul E (Fin r → ℚ) (a : E)).restrictScalars ℚ := by
    refine LinearMap.ext fun v => ?_
    change g a v = φ (algebraMap (𝓞 E) E a) v
    simp only [φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  apply Int.cast_injective (α := ℚ)
  rw [← key, hga, RepTrace.trace_lsmul_restrictScalars, hfin]
  push_cast
  rw [Algebra.coe_trace_int]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqInertiaDegAffineChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.ResidueDegreeChart

theorem inertiaDeg_eq_finrank_of_ker {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R S] [Algebra K L] (φ : R →+* K) (ψ : S →+* L) (q : Ideal S)
    (hq : ∀ s, s ∈ q ↔ ψ s = 0)
    (hφ : ∀ z : K, ∃ a b, z = φ a / φ b) (hψ : ∀ z : L, ∃ a b, z = ψ a / ψ b)
    (hc : ∀ r, algebraMap K L (φ r) = ψ (algebraMap R S r)) :
    q.inertiaDeg R = Module.finrank K L := by
  have hq' : q = RingHom.ker ψ := by ext s; simp [hq, RingHom.mem_ker]
  subst hq'
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : (RingHom.ker ψ).LiesOver (RingHom.ker φ) := ⟨by
    ext r
    simp only [RingHom.mem_ker, Ideal.under, Ideal.mem_comap, ← hc]
    simp⟩
  let _ : Algebra R K := φ.toAlgebra
  let _ : Algebra S L := ψ.toAlgebra
  let _ : Algebra R L := (ψ.comp (algebraMap R S)).toAlgebra
  let _ : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  let _ : Algebra (S ⧸ RingHom.ker ψ) L := (RingHom.kerLift ψ).toAlgebra
  have : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  have : FaithfulSMul (S ⧸ RingHom.ker ψ) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ψ)
  have : IsFractionRing (R ⧸ RingHom.ker φ) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hφ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsFractionRing (S ⧸ RingHom.ker ψ) L := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hψ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsScalarTower R (R ⧸ RingHom.ker φ) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower S (S ⧸ RingHom.ker ψ) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => (hc r).symm
  exact Ideal.inertiaDeg_eq_of_isFractionRing (RingHom.ker φ) (RingHom.ker ψ) K L

theorem mem_primeIdealOf_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔ (X.evaluation U x hx).hom s = 0 := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s, ← IsLocalRing.residue_eq_zero_iff]
  rfl

theorem exists_eq_div_evaluation {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (z : X.residueField x) :
    ∃ a b, z = (X.evaluation U x hx).hom a / (X.evaluation U x hx).hom b := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨t, rfl⟩ := X.residue_surjective x z
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk x) t
  refine ⟨a, b, ?_⟩
  have hb : (X.evaluation U x hx).hom b ≠ 0 := fun h0 =>
    b.2 ((mem_primeIdealOf_iff hU x hx b).2 h0)
  rw [eq_div_iff hb]
  have := congrArg (X.residue x).hom h
  rw [map_mul] at this
  exact this

theorem residueDegree_eq_inertiaDeg : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  intro X Y g V hV hU w hw
  let _ : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.app V).hom.toAlgebra
  let _ : Algebra (X.residueField (g w)) (Y.residueField w) := (g.residueFieldMap w).hom.toAlgebra
  symm
  exact inertiaDeg_eq_finrank_of_ker (X.evaluation V (g w) hw).hom
    (Y.evaluation (g ⁻¹ᵁ V) w hw).hom _ (mem_primeIdealOf_iff hU w hw)
    (exists_eq_div_evaluation hV (g w) hw) (exists_eq_div_evaluation hU w hw)
    (fun r => Scheme.evaluation_naturality_apply g w hw r)

end GlobalTheory.ResidueDegreeChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteType
section
namespace GlobalTheory

theorem residueField_localization_atPrime_isSepClosed_of_finiteType :
    ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
      (P : Ideal B) [P.IsMaximal],
      IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  intro k B _ _ _ _ _ P _
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  haveI : Algebra.IsIntegral k (B ⧸ P) := inferInstance
  let f : k ≃+* (B ⧸ P) := RingEquiv.ofBijective (algebraMap k (B ⧸ P))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed (B ⧸ P) := IsAlgClosed.of_ringEquiv k (B ⧸ P) f
  let e : (B ⧸ P) ≃+* IsLocalRing.ResidueField (Localization.AtPrime P) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  haveI : IsAlgClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) :=
    IsAlgClosed.of_ringEquiv _ _ e
  infer_instance

end GlobalTheory
end

