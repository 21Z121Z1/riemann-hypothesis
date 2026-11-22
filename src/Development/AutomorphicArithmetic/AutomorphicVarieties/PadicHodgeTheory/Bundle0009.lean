import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.AdmRes

variable {l : ℕ} [Fact l.Prime]

section Transport

variable {G G' A A' V : Type} [Group G] [Group G'] [CommRing A] [Algebra ℚ_[l] A] [CommRing A'] [Algebra ℚ_[l] A']
  [AddCommGroup V] [Module A V] [Module A' V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [IsScalarTower ℚ_[l] A' V]
  {φ : G →* GQ l} {ρ : Representation A G V} {φ' : G' →* GQ l} {ρ' : Representation A' G' V}

private theorem transport (e : G → G') (he : Function.Surjective e) (h1 : ∀ g, φ' (e g) = φ g)
    (h2 : ∀ g x, ρ' (e g) x = ρ g x) : (IsCr φ ρ ↔ IsCr φ' ρ') ∧ (IsDr φ ρ ↔ IsDr φ' ρ') := by
  have hr : φ.range = φ'.range := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, h1 g⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, (h1 g).symm⟩
  have hρ : ∀ g, resCoef ℚ_[l] ρ' (e g) = resCoef ℚ_[l] ρ g := fun g => LinearMap.ext fun x => h2 g x
  have hc : Dcr φ (resCoef ℚ_[l] ρ) = Dcr φ' (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    rw [he.iInf_comp (fun g => LinearMap.ker (actC φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actC
    rw [hρ, h1]
  have hd : Ddr φ (resCoef ℚ_[l] ρ) = Ddr φ' (resCoef ℚ_[l] ρ') := by
    unfold Ddr
    rw [he.iInf_comp (fun g => LinearMap.ker (actD φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actD
    rw [hρ, h1]
  unfold IsCr IsDr
  rw [hr, hc, hd]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Transport

private theorem field_case (K K' LL : FinExt l) (h : K.1 ≤ K'.1) {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) :
    (IsCr (GK K).subtype ρ → IsDr (GK K).subtype ρ) ∧
      (IsCr (GK K).subtype ρ → IsCr (GK K').subtype (ρ.comp (incl h) : Representation ↥LL.1 ↥(GK K') V)) ∧
      (IsDr (GK K).subtype ρ ↔ IsDr (GK K').subtype (ρ.comp (incl h) : Representation ↥LL.1 ↥(GK K') V)) := by
  have := LL.2
  have : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 V
  obtain ⟨T⟩ := tiedP l
  have hres := GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K K' LL h V ρ
  rw [(isCrIff K ρ).1, (isCrIff K ρ).2, (isCrIff K' _).1, (isCrIff K' _).2, (isCrField K ρ).1, (isCrField K ρ).2.1,
    (isCrField K' _).1, (isCrField K' _).2.1]
  exact ⟨fun hc => (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (PP l) (AIP l) T K LL V ρ hc).1, hres.1, hres.2⟩

private theorem gal_case (K K' : FinExt l) (h : K.1 ≤ K'.1) {A V : Type} [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    (ρ : Representation A ↥(GK K) V) :
    (IsCr (GK K).subtype ρ → IsDr (GK K).subtype ρ) ∧
      (IsCr (GK K).subtype ρ → IsCr (GK K').subtype (ρ.comp (incl h) : Representation A ↥(GK K') V)) ∧
      (IsDr (GK K).subtype ρ ↔ IsDr (GK K').subtype (ρ.comp (incl h) : Representation A ↥(GK K') V)) := by
  let β : ↥(botExt l).1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI : Module ↥(botExt l).1 V := Module.compHom V (β : ↥(botExt l).1 →+* ℚ_[l])
  have hs : ∀ (c : ↥(botExt l).1) (x : V), c • x = β c • x := fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥(botExt l).1 V := ⟨fun a c x => by
    rw [hs, hs, Algebra.smul_def, map_mul, β.commutes, mul_smul]; rfl⟩
  haveI : ContinuousConstSMul ↥(botExt l).1 V := ⟨fun c => continuous_const_smul (β c)⟩
  let ρ' : Representation ↥(botExt l).1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := map_add _
          map_smul' := fun c x => by
            rw [RingHom.id_apply, hs, hs]
            exact LinearMap.map_smul_of_tower _ _ _ }
      map_one' := by ext x; simp
      map_mul' := fun g g' => by ext x; simp }
  have t1 := transport (φ := (GK K).subtype) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρ') id
    Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)
  have t2 := transport (φ := (GK K').subtype) (ρ := (ρ.comp (incl h) : Representation A ↥(GK K') V))
    (φ' := (GK K').subtype) (ρ' := (ρ'.comp (incl h) : Representation ↥(botExt l).1 ↥(GK K') V)) id
    Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)
  rw [t1.1, t1.2, t2.1, t2.2]
  exact field_case K K' (botExt l) h ρ'

end UpperTheory.V.Loc.AdmRes

open UpperTheory.V.Loc.AdmRes in
theorem UpperTheory.V.Loc.isCrys_isDR_restrict_openSubgroup :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → (IsCr φ ρ → IsDr φ ρ) ∧ ∀ H : Subgroup G, IsOpen (H : Set G) → (IsCr φ ρ → CrOn φ ρ H) ∧ (IsDr φ ρ ↔ IsDr (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ _
  obtain ⟨K, e, -, -, he, hK, -, -⟩ := openField φ hφ
  have he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun he g
  let ρK : Representation A ↥(GK K) V := ρ.comp e.symm.toMonoidHom
  have t1 := transport (φ := φ) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρK) e e.surjective he'
    (fun g x => by simp [ρK])
  refine ⟨?_, fun H hH => ?_⟩
  · rw [t1.1, t1.2]
    exact (gal_case K K le_rfl ρK).1
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  obtain ⟨K', e', -, -, hf, hK', -, -⟩ := openField (φ.comp H.subtype) hφH
  have hf' : ∀ g, ((e' g : ↥(GK K')) : GQ l) = φ g := fun g => DFunLike.congr_fun hf g
  have hle : GK K' ≤ GK K := by
    rw [← hK, ← hK']
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h : K.1 ≤ K'.1 := by
    have : IsGalois ℚ_[l] (Om l) := inferInstance
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup K'.1]
    exact IntermediateField.fixedField_le hle
  have t2 := transport (φ := φ.comp H.subtype) (ρ := (ρ.comp H.subtype : Representation A H V))
    (φ' := (GK K').subtype) (ρ' := (ρK.comp (incl h) : Representation A ↥(GK K') V)) e' e'.surjective hf'
    (fun g x => by
      have : incl h (e' g) = e g := Subtype.ext ((hf' g).trans (he' g).symm)
      simp [ρK, this])
  unfold CrOn
  rw [t1.1, t1.2, t2.1, t2.2]
  exact (gal_case K K' h ρK).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section Generic

variable {G Q B : Type} [Group G] [Field Q] [AddCommGroup B] [Module Q B] (a : G → B →ₗ[Q] B)

private noncomputable def invT {V : Type} [AddCommGroup V] [Module Q V] (ρ : Representation Q G V) :
    Submodule Q (V ⊗[Q] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g) (a g) - LinearMap.id)

private theorem mem_invT {V : Type} [AddCommGroup V] [Module Q V] (ρ : Representation Q G V) (x : V ⊗[Q] B) :
    x ∈ invT a ρ ↔ ∀ g, AlgebraTensorModule.map (ρ g) (a g) x = x := by
  simp only [invT, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

private theorem rT_comm {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (y : V ⊗[Q] B) :
    f.rTensor B (AlgebraTensorModule.map (ρ g) (a g) y) =
      AlgebraTensorModule.map (ρ' g) (a g) (f.rTensor B y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hf g]
  | add x y hx hy => simp only [map_add, hx, hy]

private noncomputable def invMap {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) : invT a ρ →ₗ[Q] invT a ρ' :=
  (f.rTensor B).restrict fun x hx => (mem_invT a ρ' _).2 fun g => by
    rw [← rT_comm a hf, (mem_invT a ρ _).1 hx]

private theorem of_exact {V₀ V V' : Type} [AddCommGroup V₀] [Module Q V₀] [AddCommGroup V] [Module Q V]
    [AddCommGroup V'] [Module Q V'] [FiniteDimensional Q V]
    {ρ₀ : Representation Q G V₀} {ρ : Representation Q G V} {ρ' : Representation Q G V'}
    {i : V₀ →ₗ[Q] V} {p : V →ₗ[Q] V'}
    (hi : ∀ g x, i (ρ₀ g x) = ρ g (i x)) (hp : ∀ g x, p (ρ g x) = ρ' g (p x))
    (h1 : Function.Injective i) (h2 : Function.Exact i p) (h3 : Function.Surjective p) (n : ℕ)
    [Module.Finite Q (invT a ρ)] [Module.Finite Q (invT a ρ')]
    (c₀ : finrank Q (invT a ρ₀) ≤ n * finrank Q V₀) (c' : finrank Q (invT a ρ') ≤ n * finrank Q V')
    (h : finrank Q (invT a ρ) = n * finrank Q V) :
    finrank Q (invT a ρ₀) = n * finrank Q V₀ ∧ finrank Q (invT a ρ') = n * finrank Q V' := by
  have hex : Function.Exact (i.rTensor B) (p.rTensor B) := rTensor_exact B h2 h3
  have hinj : Function.Injective (i.rTensor B) := Module.Flat.rTensor_preserves_injective_linearMap _ h1
  have e1 : Function.Injective (invMap a hi) := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have e2 : Function.Exact (invMap a hi) (invMap a hp) := by
    refine fun x => ⟨fun h => ?_, ?_⟩
    · obtain ⟨y, hy⟩ := (hex x).1 (congrArg Subtype.val h)
      refine ⟨⟨y, (mem_invT a ρ₀ y).2 fun g => hinj ?_⟩, Subtype.ext hy⟩
      rw [rT_comm a hi, hy]
      exact (mem_invT a ρ _).1 x.2 g
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((hex _).2 ⟨_, rfl⟩)
  have h4 := (invMap a hp).finrank_range_add_finrank_ker
  rw [e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1] at h4
  have h5 := p.finrank_range_add_finrank_ker
  rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top] at h5
  have h6 := (LinearMap.range (invMap a hp)).finrank_le
  rw [← h5, mul_add] at h
  exact ⟨by omega, by omega⟩

private theorem sub_quot (n : ℕ)
    (hb : ∀ (W : Type) [AddCommGroup W] [Module Q W] [FiniteDimensional Q W] (σ : Representation Q G W),
      Module.Finite Q (invT a σ) ∧ finrank Q (invT a σ) ≤ n * finrank Q W)
    {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    [FiniteDimensional Q V] [FiniteDimensional Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    (Function.Injective f → finrank Q (invT a ρ') = n * finrank Q V' → finrank Q (invT a ρ) = n * finrank Q V) ∧
    (Function.Surjective f → finrank Q (invT a ρ) = n * finrank Q V →
      finrank Q (invT a ρ') = n * finrank Q V') := by
  have := (hb V ρ).1
  have := (hb V' ρ').1
  refine ⟨fun hi h => ?_, fun hs h => ?_⟩
  · have hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ' g) := by
      rintro g _ ⟨v, rfl⟩
      exact ⟨ρ g v, hf g v⟩
    have := (hb _ (ρ'.quotient (LinearMap.range f) hst)).1
    exact (of_exact a (ρ' := ρ'.quotient (LinearMap.range f) hst) hf (fun g v => rfl) hi
      (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective n (hb V ρ).2 (hb _ _).2 h).1
  · have hst : ∀ g, LinearMap.ker f ≤ (LinearMap.ker f).comap (ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]
    exact (of_exact a (ρ₀ := ρ.subrepresentation (LinearMap.ker f) hst) (fun g v => rfl) hf
      (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) hs n (hb _ _).2 (hb V' ρ').2 h).2

end Generic

private theorem bound {G H Q K B : Type} [Group G] [Group H] [Field Q] [Field K] [Algebra Q K] [CommRing B]
    [IsDomain B] [Algebra Q B] [Algebra K B] [IsScalarTower Q K B] [FiniteDimensional Q K]
    (e : G ≃* H) (act : H →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (a : G → B →ₗ[Q] B) (ha : ∀ g b, a g b = act (e g) b)
    (W : Type) [AddCommGroup W] [Module Q W] [FiniteDimensional Q W] (σ : Representation Q G W) :
    Module.Finite Q (invT a σ) ∧ finrank Q (invT a σ) ≤ finrank Q K * finrank Q W := by
  have h := GlobalTheory.Per.FontaineBound.finite_finrank_le_base (Qp := Q) (act.comp e.toMonoidHom)
    (fun b b' hb h => hreg b b' hb fun g => by simpa using h (e.symm g)) σ
  have : a = fun g => ((act.comp e.toMonoidHom g).toAlgHom.toLinearMap).restrictScalars Q :=
    funext fun g => LinearMap.ext fun b => ha g b
  subst this
  exact h

theorem UpperTheory.V.Loc.isCrys_isDR_sub_quot :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {A' : Type} [CommRing A'] [Algebra ℚ_[l] A'] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A G V) (ρ' : Representation A' G V'), ContAction ρ → ContAction ρ' → ∀ f : V →ₗ[ℚ_[l]] V', (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → (IsCr φ ρ' → IsCr φ ρ) ∧ (IsDr φ ρ' → IsDr φ ρ)) ∧ (Function.Surjective f → (IsCr φ ρ → IsCr φ ρ') ∧ (IsDr φ ρ → IsDr φ ρ')) := by
  intro l _ G _ _ _ φ hφ A _ _ A' _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' _ _ f hf
  obtain ⟨K, e, -, -, he, -, hK, hK0⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  have hF := GlobalTheory.Per.FontaineBound.isField_of_tied T
  have := GlobalTheory.Per.FontaineBound.isDomain_cris ((PP l).PD K) hF
  have := hF.isDomain
  have := ((PP l).PD K).finK₀
  have := K.2
  have hφe : ∀ g, φ g = (e g : GQ l) := fun g => by rw [← he]; rfl
  have hc := sub_quot (fun g => ((PP l).actQ (φ g)).toLinearMap) _
    (bound e ((PP l).PD K).actB (fun b b' hb h =>
      GlobalTheory.Per.FracInv.tied_frac_invariant l (PP l) (AIP l) T K b' b hb fun g hg => by
        have h1 := h ⟨g, hg⟩
        rw [(PP l).PD_actB, (PP l).PD_actB] at h1
        rw [mul_comm, h1, mul_comm]) _ fun g b => by rw [(PP l).PD_actB, hφe]; rfl)
    (ρ := resCoef ℚ_[l] ρ) (ρ' := resCoef ℚ_[l] ρ') (f := f) hf
  have hd := sub_quot (fun g => ((PP l).actQdR (φ g)).toLinearMap) _
    (bound e ((PP l).PD K).actdR (GlobalTheory.Per.FontaineBound.frac_dR ((PP l).PD K) hF) _
      fun g b => by rw [(PP l).PD_actdR, hφe]; rfl)
    (ρ := resCoef ℚ_[l] ρ) (ρ' := resCoef ℚ_[l] ρ') (f := f) hf
  unfold IsCr IsDr
  rw [hK, hK0]
  exact ⟨fun h => ⟨hc.1 h, hd.1 h⟩, fun h => ⟨hc.2 h, hd.2 h⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CardCoinvariantsModPowEqModPowCoinvariants
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.card_coinvariants_mod_pow_eq_mod_pow_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℤ_[l] G X) (m : ℕ), Nat.card ((X ⧸ lSub l X m) ⧸ coSub χ (redRep ρ m)) = Nat.card ((X ⧸ coSub χ ρ) ⧸ lSub l (X ⧸ coSub χ ρ) m) := by
  intro l _ G X _ _ _ χ ρ m
  have hq : ∀ g x, UpperTheory.V.Loc.redRep ρ m g ((lSub l X m).mkQ x) = (lSub l X m).mkQ (ρ g x) :=
    fun g x => rfl
  have hC : coSub χ (UpperTheory.V.Loc.redRep ρ m) = (coSub χ ρ).map (lSub l X m).mkQ := by
    unfold coSub
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨g, x, rfl⟩
      obtain ⟨x, rfl⟩ := (lSub l X m).mkQ_surjective x
      exact ⟨ρ g x - (χ g : ℤ_[l]) • x, ⟨g, x, rfl⟩, by rw [map_sub, map_smul, hq]⟩
    · rintro ⟨_, ⟨g, x, rfl⟩, rfl⟩
      exact ⟨g, (lSub l X m).mkQ x, by rw [map_sub, map_smul, hq]⟩
  have hL : lSub l (X ⧸ coSub χ ρ) m = (lSub l X m).map (coSub χ ρ).mkQ := by
    ext y
    rw [mem_lSub, Submodule.mem_map]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨z, rfl⟩ := (coSub χ ρ).mkQ_surjective z
      exact ⟨(l : ℤ_[l]) ^ m • z, mem_lSub.2 ⟨z, rfl⟩, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := mem_lSub.1 hx
      exact ⟨(coSub χ ρ).mkQ z, by simp⟩
  rw [hC, hL]
  exact Nat.card_congr ((Submodule.quotientQuotientEquivQuotientSup _ _).toEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).toEquiv.trans
      (Submodule.quotientQuotientEquivQuotientSup _ _).symm.toEquiv))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CardQuotientPowSubmoduleGrowsFinrank
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private noncomputable def redMap {l : ℕ} [Fact l.Prime] {X Y : Type} [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y]
    [Module ℤ_[l] Y] (f : X →ₗ[ℤ_[l]] Y) (m : ℕ) : (X ⧸ lSub l X m) →ₗ[ℤ_[l]] (Y ⧸ lSub l Y m) :=
  Submodule.mapQ _ _ f fun x hx => by
    obtain ⟨y, rfl⟩ := mem_lSub.1 hx
    exact mem_lSub.2 ⟨f y, (map_smul _ _ _).symm⟩

private theorem card_quotient_eq_card_of_isReps (l : ℕ) [Fact l.Prime] (k : ℕ) :
    Nat.card (ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ k}) = l ^ k := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hs : Function.Surjective (PadicInt.toZModPow (p := l) k) := fun z => by
    obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective z
    exact ⟨a, map_natCast _ a⟩
  rw [← PadicInt.ker_toZModPow, Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv,
    Nat.card_zmod]

private theorem finite_padicInt_quot_span_of_ne_zero (l : ℕ) [Fact l.Prime] {q : ℤ_[l]} (hq : q ≠ 0) :
    Finite (ℤ_[l] ⧸ Ideal.span {q}) := by
  have h : Ideal.span {q} = Ideal.span {(l : ℤ_[l]) ^ q.valuation} := by
    rw [Ideal.span_singleton_eq_span_singleton]
    refine Associated.symm ⟨PadicInt.unitCoeff hq, ?_⟩
    rw [mul_comm]
    exact (PadicInt.unitCoeff_spec hq).symm
  rw [h]
  apply Nat.finite_of_card_ne_zero
  rw [card_quotient_eq_card_of_isReps]
  exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero

private theorem card_pi_padicInt_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    Nat.card ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) = l ^ (m * n) := by
  let I : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l]) ^ m}
  let φ : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l] ⧸ I) :=
    LinearMap.pi (fun i => (Submodule.mkQ I) ∘ₗ LinearMap.proj i)
  have hsurj : Function.Surjective φ := by
    intro g
    choose y hy using fun i => Submodule.Quotient.mk_surjective I (g i)
    exact ⟨y, funext fun i => hy i⟩
  have hker : LinearMap.ker φ = lSub l (Fin n → ℤ_[l]) m := by
    ext x
    rw [LinearMap.mem_ker, mem_lSub]
    constructor
    · intro hx
      have h2 : ∀ i, ∃ y, (l : ℤ_[l]) ^ m * y = x i := fun i => by
        have h1 : (Submodule.Quotient.mk (x i) : ℤ_[l] ⧸ I) = 0 := congrFun hx i
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at h1
        obtain ⟨a, ha⟩ := h1
        exact ⟨a, by rw [mul_comm]; exact ha⟩
      choose y hy using h2
      exact ⟨y, funext fun i => by simp [hy]⟩
    · rintro ⟨y, rfl⟩
      funext i
      show (Submodule.Quotient.mk _ : ℤ_[l] ⧸ I) = 0
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
      exact ⟨y i, by simp [mul_comm]⟩
  rw [← hker, Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv, Nat.card_fun,
    card_quotient_eq_card_of_isReps, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]

theorem UpperTheory.card_quotient_powSubmodule_grows_finrank :
    ∀ (l : ℕ) [Fact l.Prime] (N : Type) [AddCommGroup N] [Module ℤ_[l] N] [Module.Finite ℤ_[l] N], Grows l (fun m => Nat.card (N ⧸ lSub l N m)) (finrank ℤ_[l] N) := by
  intro l _ N _ _ _
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum ℤ_[l] N
  set D := DirectSum ι fun i => ℤ_[l] ⧸ ℤ_[l] ∙ p i ^ e i with hD
  let g : N ≃ₗ[ℤ_[l]] (Fin n → ℤ_[l]) × D :=
    f.trans (LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite ℤ_[l] ℤ_[l] (Fin n))
      (LinearEquiv.refl _ _))
  haveI : Finite D := by
    haveI : ∀ i, Finite (ℤ_[l] ⧸ ℤ_[l] ∙ p i ^ e i) := fun i =>
      finite_padicInt_quot_span_of_ne_zero l (pow_ne_zero _ (hp i).ne_zero)
    exact Finite.of_injective _ (DirectSum.linearEquivFunOnFintype ℤ_[l] ι _).injective
  have hrank : finrank ℤ_[l] N = n := by
    apply Module.finrank_eq_of_rank_eq
    have h0 : Module.rank ℤ_[l] D = 0 := by
      rw [rank_eq_zero_iff]
      intro x
      refine ⟨(Nat.card D : ℤ_[l]), Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩
      rw [Nat.cast_smul_eq_nsmul]
      exact card_nsmul_eq_zero'
    rw [g.rank_eq, ← LinearMap.rank_range_add_rank_ker (LinearMap.fst ℤ_[l] (Fin n → ℤ_[l]) D),
      LinearMap.range_eq_top.2 LinearMap.fst_surjective, rank_top, LinearMap.ker_fst,
      rank_range_of_injective _ LinearMap.inr_injective, h0, add_zero, rank_fun', Fintype.card_fin]
  rw [hrank]
  refine ⟨Nat.card D, fun m _ => ?_⟩
  let f1 : N →ₗ[ℤ_[l]] (Fin n → ℤ_[l]) := LinearMap.fst _ _ _ ∘ₗ g.toLinearMap
  let f2 : N →ₗ[ℤ_[l]] D := LinearMap.snd _ _ _ ∘ₗ g.toLinearMap
  let Ψ := LinearMap.prod (redMap f1 m) (redMap f2 m)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have e1 : (Submodule.Quotient.mk (f1 x) : (Fin n → ℤ_[l]) ⧸ lSub l _ m) = 0 :=
      congrArg Prod.fst hq
    have e2 : (Submodule.Quotient.mk (f2 x) : D ⧸ lSub l D m) = 0 := congrArg Prod.snd hq
    rw [Submodule.Quotient.mk_eq_zero, mem_lSub] at e1 e2
    obtain ⟨y1, hy1⟩ := e1
    obtain ⟨y2, hy2⟩ := e2
    rw [Submodule.Quotient.mk_eq_zero, mem_lSub]
    refine ⟨g.symm (y1, y2), ?_⟩
    rw [← map_smul, Prod.smul_mk, hy1, hy2]
    simp [f1, f2]
  have hF := card_pi_padicInt_quot_lSub l n m
  haveI : Finite ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) :=
    Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  haveI : Finite (D ⧸ lSub l D m) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  haveI : Finite (N ⧸ lSub l N m) := Finite.of_injective _ hinj
  have hsurj : Function.Surjective (redMap f1 m) := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨Submodule.Quotient.mk (g.symm (y, 0)), ?_⟩
    simp [redMap, f1]
  constructor
  · rw [← hF]
    exact Nat.card_le_card_of_surjective _ hsurj
  · calc Nat.card (N ⧸ lSub l N m)
        ≤ Nat.card (((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) × (D ⧸ lSub l D m)) :=
          Nat.card_le_card_of_injective _ hinj
      _ = l ^ (m * n) * Nat.card (D ⧸ lSub l D m) := by rw [Nat.card_prod, hF]
      _ ≤ l ^ (m * n) * Nat.card D :=
          Nat.mul_le_mul_left _ (Nat.card_le_card_of_surjective _ (Submodule.Quotient.mk_surjective _))
      _ ≤ l ^ (m * n) * l ^ (Nat.card D) :=
          Nat.mul_le_mul_left _ (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
      _ = l ^ (m * n + Nat.card D) := (pow_add _ _ _).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankCoinvariantsEqFinrankLatticeCoinvariants
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G T V : Type} [Group G] [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℚ_[l] G V) (ρT : Representation ℤ_[l] G T) (j : T →ₗ[ℤ_[l]] V), Function.Injective j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) = finrank ℤ_[l] (T ⧸ coSub χ ρT) := by
  intro l _ G T V _ _ _ _ _ _ _ χ ρ ρT j hj hρ hs
  set N := coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ with hN
  have hl : ∀ m : ℕ, (l : ℤ_[l]) ^ m ∈ nonZeroDivisors ℤ_[l] := fun m =>
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  have hgen : ∀ g x, j (ρT g x - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x) =
      ρ g (j x) - ((((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) g : ℚ_[l]ˣ) : ℚ_[l]) • j x := by
    intro g x
    rw [map_sub, hρ, map_smul, ← algebraMap_smul ℚ_[l] ((χ g : ℤ_[l]ˣ) : ℤ_[l]) (j x)]
    rfl
  have hρs : ∀ g (c : ℤ_[l]) (v : V), ρ g (c • v) = c • ρ g v := fun g c v => by
    rw [← algebraMap_smul ℚ_[l] c v, map_smul, algebraMap_smul]
  let q : V →ₗ[ℤ_[l]] (V ⧸ N) := N.mkQ.restrictScalars ℤ_[l]
  have hle : coSub χ ρT ≤ LinearMap.ker (q ∘ₗ j) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    change N.mkQ (j _) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hgen]
    exact Submodule.subset_span ⟨g, j x, rfl⟩
  let f : (T ⧸ coSub χ ρT) →ₗ[ℤ_[l]] (V ⧸ N) := (coSub χ ρT).liftQ (q ∘ₗ j) hle
  have key : ∀ v ∈ N, ∃ c ∈ nonZeroDivisors ℤ_[l], c • v ∈ (coSub χ ρT).map j := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, x, rfl⟩ := hy
      obtain ⟨m, t, ht⟩ := hs x
      refine ⟨_, hl m, ρT g t - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • t, Submodule.subset_span ⟨g, t, rfl⟩, ?_⟩
      rw [hgen, ht, hρs, smul_sub, smul_comm]
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨d, hd, hy⟩ := hy
      refine ⟨c * d, mul_mem hc hd, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[l]) a
      refine ⟨c * s, mul_mem hc s.2, ?_⟩
      have : (s : ℤ_[l]) • a • x = r • x := by
        rw [← algebraMap_smul ℚ_[l] (s : ℤ_[l]), smul_smul, mul_comm, hrs, algebraMap_smul]
      rw [mul_smul, this, smul_comm]
      exact Submodule.smul_mem _ _ hx
  haveI : IsLocalizedModule (nonZeroDivisors ℤ_[l]) f := by
    refine ⟨(isLocalizedModule_id (nonZeroDivisors ℤ_[l]) (V ⧸ N) ℚ_[l]).map_units, ?_, ?_⟩
    · intro y
      obtain ⟨v, rfl⟩ := N.mkQ_surjective y
      obtain ⟨m, t, ht⟩ := hs v
      refine ⟨⟨Submodule.Quotient.mk t, ⟨_, hl m⟩⟩, ?_⟩
      change (l : ℤ_[l]) ^ m • q v = q (j t)
      rw [ht, map_smul]
    · intro x y h
      obtain ⟨x, rfl⟩ := (coSub χ ρT).mkQ_surjective x
      obtain ⟨y, rfl⟩ := (coSub χ ρT).mkQ_surjective y
      have h' : j x - j y ∈ N := (Submodule.Quotient.eq N).1 h
      obtain ⟨c, hc, t, ht, e⟩ := key _ h'
      rw [← map_sub, ← map_smul] at e
      obtain rfl := hj e
      refine ⟨⟨c, hc⟩, ?_⟩
      change c • (coSub χ ρT).mkQ x = c • (coSub χ ρT).mkQ y
      rw [← map_smul, ← map_smul]
      refine (Submodule.Quotient.eq _).2 ?_
      rw [← smul_sub]; exact ht
  rw [IsLocalization.finrank_eq ℚ_[l] (nonZeroDivisors ℤ_[l]) le_rfl,
    IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ_[l]) f le_rfl]
end

