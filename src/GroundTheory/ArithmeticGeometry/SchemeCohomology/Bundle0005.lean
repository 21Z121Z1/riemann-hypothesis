import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechLeray
import GroundTheory.ArithmeticGeometry.SchemeCohomology.AffineVanishing
import GroundTheory.FunctionField.PlaceBridge

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe w w' u

section Transport

variable {Y X : TopCat.{u}} {κ : Type w} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
  {P' : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}}

lemma cechAcyclic_of_transport (φ : Opens Y → Opens X) (hφ : Monotone φ)
    (e : ∀ W, P'.obj (op W) ≃+ P.obj (op (φ W)))
    (he : ∀ {V W : Opens Y} (h : V ≤ W) (x : P'.obj (op W)),
      e V (res P' h x) = res P (hφ h) (e W x))
    (U : κ → Opens Y) (hinter : ∀ {n : ℕ} (i : Fin (n + 1) → κ), φ (inter U i) = inter (φ ∘ U) i)
    (hU : CechAcyclic P' U) : CechAcyclic P (φ ∘ U) := by
  let E : ∀ n, Cochain P' U n → Cochain P (φ ∘ U) n := fun n σ i =>
    res P (hinter i).ge (e _ (σ i))
  let E' : ∀ n, Cochain P (φ ∘ U) n → Cochain P' U n := fun n σ i =>
    (e _).symm (res P (hinter i).le (σ i))
  have hEE' : ∀ n σ, E n (E' n σ) = σ := fun n σ => funext fun i => by
    simp only [E, E', AddEquiv.apply_symm_apply, res_res, res_refl]
  have hE'E : ∀ n σ, E' n (E n σ) = σ := fun n σ => funext fun i => by
    simp only [E, E', res_res, res_refl, AddEquiv.symm_apply_apply]
  have hE'0 : ∀ n, E' n 0 = 0 := fun n => funext fun i => by
    simp only [E', Pi.zero_apply, map_zero]
  have hEd : ∀ n σ, E (n + 1) (d P' U n σ) = d P (φ ∘ U) n (E n σ) := fun n σ => funext fun i => by
    simp only [E, d_apply, map_sum, map_zsmul, he, res_res]
  intro n σ hσ
  have hσ' : d P' U (n + 1) (E' (n + 1) σ) = 0 := by
    rw [← hE'E (n + 2) (d P' U (n + 1) _), hEd, hEE', hσ, hE'0]
  obtain ⟨τ, hτ⟩ := hU n _ hσ'
  exact ⟨E n τ, by rw [← hEd, hτ, hEE']⟩

end Transport

section Scheme

variable {X : Scheme.{u}}

noncomputable abbrev modulesAb (F : X.Modules) :
    Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj F

def IsBasicCover (V : X.Opens) {κ : Type u} (U : κ → X.Opens) : Prop :=
  IsAffineOpen V ∧ ∃ h : κ → Γ(X, V), (∀ a, U a = X.basicOpen (h a)) ∧ iSup U = V

lemma inter_basicOpen {V : X.Opens} {κ : Type u} (h : κ → Γ(X, V)) :
    ∀ {n : ℕ} (i : Fin (n + 1) → κ),
      inter (X := X.toTopCat) (fun a => X.basicOpen (h a)) i = X.basicOpen (∏ a, h (i a))
  | 0, i => by
    rw [Fin.prod_univ_one]
    apply le_antisymm (inter_le _ i 0)
    intro x hx
    rw [mem_inter_iff]
    intro a
    rwa [Fin.fin_one_eq_zero a]
  | n + 1, i => by
    rw [inter_succ, inter_basicOpen h (i ∘ Fin.succ), Fin.prod_univ_succ (fun a => h (i a)),
      Scheme.basicOpen_mul]
    rfl

lemma isCoverSystem_isBasicCover :
    IsCoverSystem (X := X.toTopCat) IsAffineOpen (fun {κ} V U => IsBasicCover (κ := κ) V U) where
  iSup_eq V κ U hU := hU.2.choose_spec.2
  inter_mem V κ U hU n i := by
    obtain ⟨hV, h, hUh, -⟩ := hU
    have : U = fun a => X.basicOpen (h a) := funext hUh
    subst this
    rw [inter_basicOpen h i]
    exact hV.basicOpen _
  exists_refinement V hV O hO := by
    choose f hfO hxf using fun x : V => hV.exists_basicOpen_le (V := O x) ⟨x.1, hO x⟩ x.2
    obtain ⟨fs, hfs⟩ := hV.isCompact.elim_finite_subcover
      (fun x : V => (X.basicOpen (f x) : Set X)) (fun x => (X.basicOpen (f x)).isOpen)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxf _⟩)
    refine ⟨{x // x ∈ fs}, inferInstance, fun a => X.basicOpen (f a.1),
      ⟨hV, fun a => f a.1, fun a => rfl, ?_⟩, fun a => ⟨a.1, hfO a.1⟩⟩
    refine le_antisymm (iSup_le fun a => X.basicOpen_le _) ?_
    intro y hy
    have := hfs hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, hyx⟩ := this
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyx⟩

lemma image_inter {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] {κ : Type w}
    (U : κ → Y.Opens) {n : ℕ} (i : Fin (n + 1) → κ) :
    g ''ᵁ inter (X := Y.toTopCat) U i = inter (X := X.toTopCat) (fun a => g ''ᵁ U a) i := by
  have key : ∀ (W : Y.Opens) (x : X), x ∈ g ''ᵁ W ↔ ∃ y ∈ W, g y = x := fun W x => by
    rw [← SetLike.mem_coe, Scheme.Hom.coe_image]
    rfl
  refine SetLike.ext fun x => ?_
  rw [mem_inter_iff, key]
  constructor
  · rintro ⟨y, hy, rfl⟩ a
    exact (key _ _).2 ⟨y, (mem_inter_iff U i y).1 hy a, rfl⟩
  · intro hx
    choose y hy hyx using fun a => (key _ x).1 (hx a)
    refine ⟨y 0, (mem_inter_iff U i (y 0)).2 fun a => ?_, hyx 0⟩
    have : y a = y 0 := g.isOpenEmbedding.injective ((hyx a).trans (hyx 0).symm)
    rw [← this]
    exact hy a

theorem cechAcyclic_of_isBasicCover (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    {κ : Type u} [Finite κ] {U : κ → X.Opens} (hU : IsBasicCover V U) :
    CechAcyclic (modulesAb F).obj U := by
  obtain ⟨hV, h, hUh, hsup⟩ := hU
  have hUeq : U = fun a => X.basicOpen (h a) := funext hUh
  subst hUeq
  let F' : (Spec Γ(X, V)).Modules := F.restrict hV.fromSpec
  let M := (modulesSpecToSheaf.obj F').presheaf.obj (op ⊤)
  let U' : κ → Opens (Spec Γ(X, V)).toTopCat := fun a => PrimeSpectrum.basicOpen (h a)
  have hsup' : iSup U' = ⊤ := by
    have h1 : hV.fromSpec ⁻¹ᵁ (⨆ a, X.basicOpen (h a)) = ⊤ := by
      rw [hsup]
      exact hV.fromSpec_preimage_self
    rw [Scheme.Hom.preimage_iSup] at h1
    simpa only [hV.fromSpec_preimage_basicOpen] using h1
  have hM : CechAcyclic (tildeAb M).obj U' :=
    cechCondition_tilde M ⊤ ⟨1, PrimeSpectrum.basicOpen_one.symm⟩ κ U' (fun a => ⟨h a, rfl⟩)
      hsup'
  have : F'.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor hV.fromSpec F
  have hiso : IsIso F'.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F'
  let e : tildeAb M ≅ modulesAb F' :=
    (SheafOfModules.toSheaf _).mapIso (@asIso _ _ _ _ F'.fromTildeΓ hiso)
  have hF' : CechAcyclic (modulesAb F').obj U' :=
    CechAcyclic.of_retract U' e.inv.hom e.hom.hom (congrArg (fun f => f.hom) e.inv_hom_id) hM
  have key := cechAcyclic_of_transport (P := (modulesAb F).obj) (P' := (modulesAb F').obj)
    (fun W => hV.fromSpec ''ᵁ W) (fun _ _ hle => hV.fromSpec.image_mono hle)
    (fun W => AddEquiv.refl _) (fun _ _ => rfl) U' (fun i => image_inter hV.fromSpec U' i) hF'
  convert key using 1
  funext a
  exact (hV.fromSpec_image_basicOpen (h a)).symm

lemma goodAcyclic_modulesAb (F : X.Modules) [F.IsQuasicoherent] :
    GoodAcyclic (X := X.toTopCat) IsAffineOpen (fun {κ} V U => IsBasicCover (κ := κ) V U)
      (modulesAb F) :=
  fun _ _ _ _ _ hU => cechAcyclic_of_isBasicCover F hU

lemma inter_eq_iInf {ι : Type w} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) :
    inter (X := X.toTopCat) U i = ⨅ a, U (i a) :=
  SetLike.ext fun x => by
    rw [mem_inter_iff, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    rfl

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

theorem nonempty_cechH_equiv_H (F : X.Modules) [F.IsQuasicoherent] {ι : Type w}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (n : ℕ) :
    Nonempty (cechH (modulesAb F).obj U n ≃+ Sheaf.H.{w'} (modulesAb F) n) :=
  nonempty_cechH_equiv isCoverSystem_isBasicCover U hU
    (fun i => by rw [inter_eq_iInf]; exact hUaff _ i) n (modulesAb F) (goodAcyclic_modulesAb F)

end Scheme

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.KaehlerPlace
section
namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField KaehlerDifferential IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable (k) in

def spanDField (x : K) : IntermediateField k K where
  carrier := {y | D k K y ∈ Submodule.span K {D k K x}}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Derivation.leibniz] at *
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact add_mem ha hb
  algebraMap_mem' c := by
    simp only [Set.mem_ofPred_eq, Derivation.map_algebraMap]
    exact zero_mem _
  inv_mem' a ha := by
    simp only [Set.mem_ofPred_eq, Derivation.leibniz_inv] at *
    exact Submodule.smul_mem _ _ ha

theorem D_mem_span_of_mem_adjoin (x : K) {y : K} (hy : y ∈ k⟮x⟯) :
    D k K y ∈ Submodule.span K {D k K x} := by
  have : k⟮x⟯ ≤ spanDField k x := by
    rw [adjoin_le_iff, Set.singleton_subset_iff]
    exact Submodule.subset_span rfl
  exact this hy

theorem span_D_eq_top (x : K) [Algebra.IsSeparable k⟮x⟯ K] :
    Submodule.span K {D k K x} = ⊤ := by
  have : Algebra.FormallyUnramified k⟮x⟯ K := .of_isSeparable _ _
  refine eq_top_iff.mpr fun ω hω ↦ ?_
  clear hω
  obtain ⟨z, rfl⟩ := (exact_mapBaseChange_map k k⟮x⟯ K ω).mp (Subsingleton.elim _ _)
  induction z with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul a b =>
    rw [mapBaseChange_tmul]
    refine Submodule.smul_mem _ _ ?_
    have hb : b ∈ Submodule.span k⟮x⟯ (Set.range (D k k⟮x⟯)) := by
      rw [span_range_derivation]; trivial
    induction hb using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨e, rfl⟩ := h
      rw [map_D]
      exact D_mem_span_of_mem_adjoin x e.2
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul c _ _ h =>
      rw [map_smul, algebra_compatible_smul K c]
      exact Submodule.smul_mem _ _ h

variable [IsFunctionField k K]

theorem kaehlerDifferential_nontrivial : Nontrivial Ω[K⁄k] := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Algebra.FormallyUnramified k K := ⟨h⟩
  have : Algebra.EssFiniteType k K := essFiniteType
  have : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
  have h1 := trdeg_eq_one (k := k) (K := K)
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  rw [_root_.trdeg_eq_zero] at h1
  exact zero_ne_one h1

theorem D_ne_zero_of_isSeparable (x : K) [Algebra.IsSeparable k⟮x⟯ K] : D k K x ≠ 0 := by
  intro h
  have htop := span_D_eq_top (k := k) x
  rw [h, Submodule.span_singleton_eq_bot.mpr rfl] at htop
  have := kaehlerDifferential_nontrivial (k := k) (K := K)
  exact bot_ne_top htop

section Perfect

variable [PerfectField k]

variable (k K) in

theorem exists_isSeparable_adjoin : ∃ x : K, Algebra.IsSeparable k⟮x⟯ K := by
  have : Algebra.EssFiniteType k K := essFiniteType
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg
    rw [trdeg_eq_one, Cardinal.mk_coe_finset] at h
    exact_mod_cast h
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
  refine ⟨x, ?_⟩
  convert hsep <;> simp

variable (k K) in

theorem finrank_kaehlerDifferential : Module.finrank K Ω[K⁄k] = 1 := by
  obtain ⟨x, hx⟩ := exists_isSeparable_adjoin k K
  rw [← finrank_top, ← span_D_eq_top (k := k) x, finrank_span_singleton (D_ne_zero_of_isSeparable x)]

theorem span_D_eq_top_of_ne_zero {z : K} (hz : D k K z ≠ 0) :
    Submodule.span K {D k K z} = ⊤ :=
  have : FiniteDimensional K Ω[K⁄k] :=
    Module.finite_of_finrank_pos (by rw [finrank_kaehlerDifferential]; norm_num)
  Submodule.eq_top_of_finrank_eq (by
    rw [finrank_span_singleton hz, finrank_kaehlerDifferential])

theorem isSeparable_of_D_ne_zero {z : K} (hz : D k K z ≠ 0) : Algebra.IsSeparable k⟮z⟯ K := by
  have hsub : Subsingleton Ω[K⁄k⟮z⟯] := by
    refine subsingleton_of_forall_eq 0 fun ω' ↦ ?_
    obtain ⟨ω, rfl⟩ := map_surjective k k⟮z⟯ K ω'
    have hω : ω ∈ Submodule.span K {D k K z} := by rw [span_D_eq_top_of_ne_zero hz]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hω
    have h0 : D k⟮z⟯ K z = 0 := (D k⟮z⟯ K).map_algebraMap ⟨z, mem_adjoin_simple_self k z⟩
    simp only [map_smul, map_D, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h0, smul_zero]
  have : Algebra.FormallyUnramified k⟮z⟯ K := ⟨hsub⟩
  have : Algebra.EssFiniteType k K := essFiniteType
  have : Algebra.EssFiniteType k⟮z⟯ K := .of_comp k k⟮z⟯ K
  exact Algebra.FormallyUnramified.isSeparable k⟮z⟯ K

theorem exists_ord_eq_one_D_ne_zero (v : Place k K) :
    ∃ t : K, v.ord t = 1 ∧ D k K t ≠ 0 := by
  obtain ⟨π, hπ⟩ := v.exists_ord_eq_one
  have hπ0 : π ≠ 0 := fun h ↦ by simp [h, v.ord_zero] at hπ
  by_cases hd : D k K π = 0
  swap
  · exact ⟨π, hπ, hd⟩
  obtain ⟨x, hx⟩ := exists_isSeparable_adjoin k K
  have hdx := D_ne_zero_of_isSeparable (k := k) x
  have hx0 : x ≠ 0 := fun h ↦ hdx (by simp [h])
  set m : ℕ := (2 - v.ord x).toNat + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hord : v.ord (π ^ m * x) = m + v.ord x := by
    rw [v.ord_mul (pow_ne_zero _ hπ0) hx0, v.ord_pow, hπ, mul_one]
  have hlt : v.valuation (π ^ m * x) < v.valuation π := by
    rw [v.valuation_eq_exp_neg_ord (mul_ne_zero (pow_ne_zero _ hπ0) hx0),
      v.valuation_eq_exp_neg_ord hπ0, hord, hπ, WithZero.exp_lt_exp]
    omega
  refine ⟨π + π ^ m * x, ?_, ?_⟩
  · have hne : π + π ^ m * x ≠ 0 := by
      intro h
      have := Valuation.map_add_eq_of_lt_left v.valuation hlt
      rw [h, map_zero] at this
      exact (v.valuation.ne_zero_iff.mpr hπ0) this.symm
    have h := Valuation.map_add_eq_of_lt_left v.valuation hlt
    rw [v.valuation_eq_exp_neg_ord hne, v.valuation_eq_exp_neg_ord hπ0, hπ] at h
    have := WithZero.exp_injective h
    omega
  · rw [map_add, hd, zero_add, Derivation.leibniz, Derivation.leibniz_pow, hd]
    simp only [smul_zero, add_zero]
    exact smul_ne_zero (pow_ne_zero _ hπ0) hdx

end Perfect

section Order

variable [PerfectField k]

noncomputable def kaehlerCoeff (t : K) (ω : Ω[K⁄k]) : K :=
  haveI := Classical.propDecidable
  if h : ∃ c : K, c • D k K t = ω then h.choose else 0

theorem kaehlerCoeff_smul_D {t : K} (ht : D k K t ≠ 0) (ω : Ω[K⁄k]) :
    kaehlerCoeff t ω • D k K t = ω := by
  have hω : ω ∈ Submodule.span K {D k K t} := by rw [span_D_eq_top_of_ne_zero ht]; trivial
  have h := Submodule.mem_span_singleton.mp hω
  classical
  rw [kaehlerCoeff, dif_pos h]
  exact h.choose_spec

theorem kaehlerCoeff_eq {t : K} (ht : D k K t ≠ 0) {ω : Ω[K⁄k]} {c : K} (h : c • D k K t = ω) :
    kaehlerCoeff t ω = c :=
  smul_left_injective K ht ((kaehlerCoeff_smul_D ht ω).trans h.symm)

theorem kaehlerCoeff_smul {t : K} (ht : D k K t ≠ 0) (f : K) (ω : Ω[K⁄k]) :
    kaehlerCoeff t (f • ω) = f * kaehlerCoeff t ω :=
  kaehlerCoeff_eq ht (by rw [mul_smul, kaehlerCoeff_smul_D ht])

theorem kaehlerCoeff_add {t : K} (ht : D k K t ≠ 0) (ω₁ ω₂ : Ω[K⁄k]) :
    kaehlerCoeff t (ω₁ + ω₂) = kaehlerCoeff t ω₁ + kaehlerCoeff t ω₂ :=
  kaehlerCoeff_eq ht (by rw [add_smul, kaehlerCoeff_smul_D ht, kaehlerCoeff_smul_D ht])

theorem kaehlerCoeff_ne_zero {t : K} (ht : D k K t ≠ 0) {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    kaehlerCoeff t ω ≠ 0 := by
  intro h
  have := kaehlerCoeff_smul_D ht ω
  rw [h, zero_smul] at this
  exact hω this.symm

theorem kaehlerCoeff_D_self {t : K} (ht : D k K t ≠ 0) : kaehlerCoeff t (D k K t) = 1 :=
  kaehlerCoeff_eq ht (one_smul _ _)

theorem kaehlerCoeff_trans {t t' : K} (ht : D k K t ≠ 0) (ht' : D k K t' ≠ 0) (ω : Ω[K⁄k]) :
    kaehlerCoeff t ω = kaehlerCoeff t' ω * kaehlerCoeff t (D k K t') := by
  refine kaehlerCoeff_eq ht ?_
  rw [mul_smul, kaehlerCoeff_smul_D ht, kaehlerCoeff_smul_D ht']

noncomputable def kaehlerUniformizer (v : Place k K) : K :=
  (exists_ord_eq_one_D_ne_zero v).choose

theorem ord_kaehlerUniformizer (v : Place k K) : v.ord (kaehlerUniformizer v) = 1 :=
  (exists_ord_eq_one_D_ne_zero v).choose_spec.1

theorem D_kaehlerUniformizer_ne_zero (v : Place k K) : D k K (kaehlerUniformizer v) ≠ 0 :=
  (exists_ord_eq_one_D_ne_zero v).choose_spec.2

noncomputable def kaehlerOrd (v : Place k K) (ω : Ω[K⁄k]) : ℤ :=
  v.ord (kaehlerCoeff (kaehlerUniformizer v) ω)

theorem kaehlerOrd_smul (v : Place k K) {f : K} (hf : f ≠ 0) {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    kaehlerOrd v (f • ω) = v.ord f + kaehlerOrd v ω := by
  rw [kaehlerOrd, kaehlerCoeff_smul (D_kaehlerUniformizer_ne_zero v),
    v.ord_mul hf (kaehlerCoeff_ne_zero (D_kaehlerUniformizer_ne_zero v) hω), kaehlerOrd]

end Order

end GroundTheory.Arith.SchemeCoh
end

