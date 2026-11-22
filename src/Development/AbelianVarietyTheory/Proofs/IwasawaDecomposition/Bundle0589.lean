import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlowOrbitFirstMinimumOfIsotropicFlowMajorant

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedClosureLocalSystem
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
  GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp
  tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.StepLift

theorem initSpan_map {K N N' : Type} [CommRing K] [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] {m : ℕ}
    (L : N →ₗ[K] N') (v : Fin m → N) (j : ℕ) : initSpan K (fun i => L (v i)) j = (initSpan K v j).map L := by
  rw [initSpan, initSpan, Submodule.map_span, Set.image_image]

theorem initSpan_of_le {K N : Type} [CommRing K] [AddCommGroup N] [Module K N] {m : ℕ}
    (v : Fin m → N) {j : ℕ} (hj : m ≤ j) : initSpan K v j = Submodule.span K (Set.range v) := by
  rw [initSpan, ← Set.image_univ]
  congr 2
  exact Set.eq_univ_of_forall fun i => i.2.trans_le hj

theorem exists_isUnit_repr {R N : Type} [CommRing R] [IsLocalRing R] [AddCommGroup N] [Module R N] {k m : ℕ} {κ : Type}
    (b : Module.Basis (Fin k ⊕ Fin m) R N) (c : Module.Basis κ R N) (q : κ)
    (h : ∀ i, c.repr (b (.inl i)) q = 0) : ∃ j, IsUnit (b.repr (c q) (.inr j)) := by
  by_contra! hn
  have h1 : c.repr (c q) q ∈ IsLocalRing.maximalIdeal R := by
    rw [← b.sum_repr (c q), map_sum, Finsupp.finset_sum_apply]
    refine Ideal.sum_mem _ fun x _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rcases x with i | j
    · rw [h i, mul_zero]; exact Ideal.zero_mem _
    · exact Ideal.mul_mem_right _ _ (hn j)
  rw [c.repr_self, Finsupp.single_eq_same] at h1
  exact h1 isUnit_one

theorem repr_eq_zero_of_mem {K N : Type} [CommRing K] [AddCommGroup N] [Module K N] {κ : Type} {d : ℕ}
    (c : Module.Basis κ K N) (e : Fin d ↪ κ) {k : ℕ} (hk : k < d) {v : N}
    (hv : v ∈ initSpan K (fun j => c (e j)) k) : c.repr v (e ⟨k, hk⟩) = 0 := by
  have : initSpan K (fun j => c (e j)) k ≤ LinearMap.ker (c.coord (e ⟨k, hk⟩)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have hne : e j ≠ e ⟨k, hk⟩ := fun h => by
      obtain rfl := e.injective h
      exact lt_irrefl k hj
    simp [Finsupp.single_eq_of_ne hne.symm]
  exact this hv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem flagAt_of_initSpan_eq {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
    {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty}
    {K : Type} [Field K] {w : Sp K ⟶ X} {x : Sp K ⟶ M.X} (hx : w ≫ π = x) {u u' : TVecs Dw M.t x}
    (h : A.FlagAt w (up u)) (hli : ∀ σ, LinearIndependent K (u' σ))
    (hs : ∀ σ j, initSpan K (u' σ) j = initSpan K (u σ) j) : A.FlagAt w (up u') := by
  subst hx
  obtain ⟨a, φ, e, -⟩ := id h
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  obtain ⟨hf, hs'⟩ := (A.flagAt_iff e h₀ u).1 h
  refine (A.flagAt_iff e h₀ u').2 ⟨(isFrame_up_iff _ _).2 fun σ => ⟨hli σ, ?_⟩, fun σ j hj => (hs σ j).trans (hs' σ j hj)⟩
  rw [← initSpan_of_le _ le_rfl, hs, initSpan_of_le _ le_rfl]
  exact ((isFrame_up_iff _ _).1 hf σ).2

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_int_frame {Z : Mdl Y i₀} (hZ : HasDR Z) {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (φ : R →+* K)
    (z : Sp R ⟶ Z.X) {w : Sp K ⟶ Z.X} (e : spMap φ ≫ z = w) (e' : spMap φ ≫ z ≫ Z.π = w ≫ Z.π)
    (hw : Set.range w ⊆ Z.opn) {u : TVecs Dw (Y Z.i).t (w ≫ Z.π)} (hu : Z.FlagAt w (up u)) :
    ∃ T : TVecs Dw (Y Z.i).t (z ≫ Z.π),
      (∀ σ, ∃ (n : ℕ) (c : Module.Basis (Fin n) R (TanM (z ≫ Z.π) (Y Z.i).t.G)) (q : Fin (Dw.mult σ) ↪ Fin n),
        ∀ j, c (q j) = T σ j) ∧
      ∀ σ j, initSpan K (fun i => tanPull φ e' (T σ i)) j = initSpan K (u σ) j := by
  obtain ⟨U, hU, fr, hx, h1, h2⟩ := hZ.2 (z (IsLocalRing.closedPoint R))
  have hz : ⊤ ≤ z ⁻¹ᵁ U := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ U)).1 hx).ge
  have ht : ∀ σ j, IsTanAtG (Y Z.i).t (tau hU ≫ Z.π) (fr σ j) := fun σ j => by
    obtain ⟨n, v, q, hq, hv, -⟩ := h1 σ
    rw [← hq]; exact hv _
  have ez : spMap (ev z U hz) ≫ tau hU ≫ Z.π = z ≫ Z.π := by rw [← Category.assoc, tau, spMap_ev]
  refine ⟨fun σ j => tanPull (ev z U hz) ez (tanOf (ht σ j)), fun σ => ?_, fun σ j => ?_⟩
  · obtain ⟨n, v, q, hq, hv, hb⟩ := h1 σ
    have h3 : ∀ s : TanM (tau hU ≫ Z.π) (Y Z.i).t.G, ∃! a : Fin n → Γ(Z.X, U), s = ∑ i, a i • tanOf (x := tau hU ≫ Z.π) (hv i) :=
      fun s => (existsUnique_congr fun a => isComb_iff (fun i => tanOf (x := tau hU ≫ Z.π) (hv i)) a s).1 (hb _ (isTan_tv s))
    let b : Module.Basis (Fin n) Γ(Z.X, U) (TanM (tau hU ≫ Z.π) (Y Z.i).t.G) :=
      Module.Basis.mk (v := fun i => tanOf (x := tau hU ≫ Z.π) (hv i)) (Fintype.linearIndependent_iff.2 fun a ha => congrFun
        ((h3 0).unique ha.symm (by simp : (0 : TanM (tau hU ≫ Z.π) (Y Z.i).t.G) =
          ∑ i, (0 : Fin n → Γ(Z.X, U)) i • tanOf (x := tau hU ≫ Z.π) (hv i)))) fun s _ => by
        obtain ⟨a, rfl, -⟩ := h3 s
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨n, basPull _ ez b, q, fun j => ?_⟩
    rw [basPull_apply, Module.Basis.mk_apply]
    exact congrArg _ (tan_ext (hq j))
  · have ew : spMap (φ.comp (ev z U hz)) ≫ hU.fromSpec = w := by
      rw [← spMap_comp', Category.assoc, spMap_ev, e]
    have h4 := h2 K (φ.comp (ev z U hz)) (ew ▸ hw)
    rw [ew, ← Vecs.bc_bc] at h4
    let T : TVecs Dw (Y Z.i).t (w ≫ Z.π) := fun σ i => tanPull φ e' (tanPull (ev z U hz) ez (tanOf (ht σ i)))
    have h6 : up T = (fr.bc (ev z U hz)).bc φ := rfl
    rw [← h6, ← atlasOf_flagAt] at h4
    have h5 : ∀ j ∈ Z.ty σ, initSpan K (T σ) j = initSpan K (u σ) j := fun j hj =>
      Atlas.FlagAt.initSpan_eq h4 ((atlasOf_flagAt Z w _).2 hu) σ hj
    show initSpan K (T σ) j = _
    rw [hZ.1] at h5
    rcases le_total j (Dw.mult σ) with hj | hj
    · exact h5 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    · rw [initSpan_of_le _ hj, initSpan_of_le _ hj, ← initSpan_of_le _ le_rfl, ← initSpan_of_le _ le_rfl]
      exact h5 _ (Finset.mem_range.2 (Nat.lt_succ_self _))

theorem locMaps_closure {i : Idx H p} {X : Scheme.{0}} {π : X ⟶ (Y i).X} {ty : (E →+* ℂ) → Finset ℕ}
    {A : Atlas (Y i) π ty} {σ : E →+* ℂ} {k r : ℕ} (D : Adapted A σ k) (hk : k < Dw.mult σ) {Sb : D.C.Sub A.ch r}
    (Cl : Sb.Closure (π ≫ (Y i).s)) {ty' : (E →+* ℂ) → Finset ℕ} {A' : Atlas (Y i) (Cl.f ≫ π) ty'} {Z : Mdl Y i₀}
    {g : Z.X ⟶ X} (hS : StepRel D hk Cl.L A') (hZ : HasDR Z) (hg : MapsTo Z A g) : LocMaps Z A' := by
  intro K _ w hw
  obtain ⟨τ, mu, u, htr, hwτ, hu, hA⟩ := hg K w hw
  obtain ⟨u, rfl⟩ := Atlas.FlagAt.exists_up (A := atlasOf Z) hu
  obtain ⟨y, hy, hA'⟩ := hA.exists_point A'
  have e₁ : (w ≫ Z.π) ≫ τ = (y ≫ Cl.f) ≫ π := by rw [Category.assoc, ← hwτ, ← hy, Category.assoc]
  let u₁ : TVecs Dw (Y i).t ((y ≫ Cl.f) ≫ π) := fun σ j => pushE mu _ e₁ (u σ j)
  have hA₁ : A'.FlagAt y (up u₁) := hA'
  have hyf : y ≫ Cl.f = w ≫ g :=
    Atlas.FlagAt.point_eq ((hS K y u₁).1 hA₁).1 hA (by rw [← hy, Category.assoc])
  refine ⟨y, ⟨τ, mu, _, htr, hy.trans hwτ, hu, hA'⟩, fun R _ _ _ _ _ _ z ez => ?_⟩
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have e₂ : (z ≫ Z.π) ≫ τ = (z ≫ g) ≫ π := by
    have := projProper _ _ _ (Y i).proj
    have : (Y i).X.IsSeparated := ⟨by
      rw [← terminal.comp_from (Y i).s]
      infer_instance⟩
    have : IsDominant (spMap (algebraMap R K)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
    refine ext_of_isDominant (spMap (algebraMap R K)) ?_
    simp only [Category.assoc] at hwτ ⊢
    rw [reassoc_of% ez, reassoc_of% ez, hwτ]
  have e₃ : spMap (algebraMap R K) ≫ z ≫ Z.π = w ≫ Z.π := by rw [reassoc_of% ez]
  have e₄ : spMap (algebraMap R K) ≫ z ≫ g = y ≫ Cl.f := by rw [reassoc_of% ez, hyf]
  have e₅ : spMap (algebraMap R K) ≫ (z ≫ g) ≫ π = (y ≫ Cl.f) ≫ π := by rw [← Category.assoc, e₄]
  obtain ⟨T, hT, hs⟩ := exists_int_frame hZ (algebraMap R K) z ez e₃ hw hu
  let T₁ : TVecs Dw (Y i).t ((z ≫ g) ≫ π) := fun σ j => pushE mu _ e₂ (T σ j)
  let T₂ : TVecs Dw (Y i).t ((y ≫ Cl.f) ≫ π) := fun σ j => tanPull (algebraMap R K) e₅ (T₁ σ j)
  have hT₁ : ∀ σ, ∃ (n : ℕ) (c : Module.Basis (Fin n) R (TanM ((z ≫ g) ≫ π) (Y i).t.G)) (q : Fin (Dw.mult σ) ↪ Fin n),
      (∀ j, c (q j) = T₁ σ j) ∧ T₂ σ = fun j => basPull (algebraMap R K) e₅ c (q j) := fun σ => by
    obtain ⟨n, c, q, hq⟩ := hT σ
    have : ∀ j, c.map (pushE mu _ e₂) (q j) = T₁ σ j := fun j => by rw [Module.Basis.map_apply, hq]
    exact ⟨n, _, q, this, funext fun j => by rw [basPull_apply, this]⟩
  have hA₂ : A'.FlagAt y (up T₂) := by
    refine flagAt_of_initSpan_eq (Category.assoc _ _ _).symm hA₁ (fun σ => ?_) fun σ j => ?_
    · obtain ⟨n, c, q, -, h⟩ := hT₁ σ
      rw [h]
      exact (basPull _ e₅ c).linearIndependent.comp _ q.injective
    · have : T₂ σ = fun j => (pushE mu _ e₁).toLinearMap (tanPull (algebraMap R K) e₃ (T σ j)) :=
        funext fun j => tan_ext (Category.assoc _ _ _).symm
      rw [this, initSpan_map, hs]
      exact (initSpan_map (pushE mu _ e₁).toLinearMap _ _).symm
  obtain ⟨hA₃, hc⟩ := (hS K y T₂).1 hA₂
  obtain ⟨α, hα⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing (U := D.C.B)
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (D.C.cover x)) (z ≫ g)
  have hα' : ⊤ ≤ (y ≫ Cl.f) ⁻¹ᵁ D.C.B α := e₄ ▸ le_preimage_comp _ hα
  refine Cl.lift R K (z ≫ g) α hα (crd (D.b α) (z ≫ g) hα (T₁ σ ⟨k, hk⟩)) ?_ y e₄.symm fun h => ?_
  · obtain ⟨n, c, q, hq, h⟩ := hT₁ σ
    rw [← hq]
    refine exists_isUnit_repr _ c _ fun j => hinj ?_
    rw [← basPull_repr _ e₅, map_zero, tanPull_basAt _ _ _ _ e₄ hα']
    refine repr_eq_zero_of_mem _ q hk ?_
    rw [← h, D.int α K _ hα' T₂ hA₃ k le_rfl]
    exact Submodule.subset_span ⟨j, j.2, rfl⟩
  · have := hc α h
    convert this using 1
    exact funext fun j => (basAt_repr _ _ _ hα e₄ h e₅ _ _).symm

end GlobalTheory.DRFlag.StepLift

theorem GlobalTheory.DRFlag.locMaps_closure_of_hasDR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ (Y i).s)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y i) (Cl.f ≫ π) ty') (Z : Mdl Y i₀) (g : Z.X ⟶ X), StepRel D hk Cl.L A' → HasDR Z → MapsTo Z A g → LocMaps Z A' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D hk _ Cl _ _ _ _ => GlobalTheory.DRFlag.StepLift.locMaps_closure D hk Cl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedLinearPullback
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.StepInt

def optionSumEquiv (A B : Type) : Option A ⊕ B ≃ A ⊕ Option B where
  toFun
    | .inl none => .inr none
    | .inl (some a) => .inl a
    | .inr b => .inr (some b)
  invFun
    | .inl a => .inl (some a)
    | .inr none => .inl none
    | .inr (some b) => .inr b
  left_inv := by rintro ((_ | a) | b) <;> rfl
  right_inv := by rintro (a | (_ | b)) <;> rfl

theorem exists_basis_succ {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {k n : ℕ}
    (b : Module.Basis (Fin k ⊕ Fin n) R N) (η : Fin n → R) (c : Fin n) (hc : IsUnit (η c)) :
    ∃ (m : ℕ) (b' : Module.Basis (Fin (k + 1) ⊕ Fin m) R N), (∀ i : Fin k, b' (.inl i.castSucc) = b (.inl i)) ∧
      b' (.inl (Fin.last k)) = ∑ j, η j • b (.inr j) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.pos; omega⟩
  have hr : b.repr (∑ j, η j • b (.inr j)) (.inr c) = η c := by
    simp [Finsupp.single_apply]
  have hd : IsUnit (b.det (Function.update b (.inr c) (∑ j, η j • b (.inr j)))) := by
    rw [Module.Basis.det_apply, Module.Basis.toMatrix_update, Module.Basis.toMatrix_self, ← Matrix.cramer_apply,
      Matrix.cramer_one]
    rw [← hr] at hc
    exact hc
  obtain ⟨h1, h2⟩ := (Module.Basis.is_basis_iff_det b).2 hd
  let q : Fin (k + 1) ⊕ Fin m ≃ Fin k ⊕ Fin (m + 1) :=
    (Equiv.sumCongr finSuccEquivLast (Equiv.refl _)).trans
      ((optionSumEquiv _ _).trans (Equiv.sumCongr (Equiv.refl _) (finSuccEquiv' c).symm))
  refine ⟨m, (Module.Basis.mk h1 h2.ge).reindex q.symm, fun i => ?_, ?_⟩
  · have : q (.inl i.castSucc) = .inl i := by simp [q, optionSumEquiv]
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, this, Module.Basis.mk_apply, Function.update_of_ne (by simp)]
  · have : q (.inl (Fin.last k)) = .inr c := by simp [q, optionSumEquiv]
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, this, Module.Basis.mk_apply, Function.update_self]

theorem initSpan_castSucc {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {k : ℕ} (v : Fin (k + 1) → N)
    {j : ℕ} (hj : j ≤ k) : initSpan R v j = initSpan R (fun i : Fin k => v i.castSucc) j := by
  unfold initSpan
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < j := hi
    exact ⟨⟨i, by omega⟩, hi', rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, hi, rfl⟩

theorem initSpan_succ {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {M k : ℕ} (v : Fin M → N) (hk : k < M) :
    initSpan R v (k + 1) = initSpan R v k ⊔ Submodule.span R {v ⟨k, hk⟩} := by
  unfold initSpan
  rw [← Submodule.span_union, ← Set.image_singleton, ← Set.image_union]
  congr 2
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
  omega

theorem initSpan_step {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {M k n : ℕ}
    (b : Module.Basis (Fin k ⊕ Fin n) R N) (η : Fin n → R) (u : Fin M → N) (hk : k < M)
    (hu : ∀ j ≤ k, initSpan R u j = initSpan R (fun i : Fin k => b (.inl i)) j) (e : Rˣ)
    (he : ∀ i, b.repr (u ⟨k, hk⟩) (.inr i) = (e : R) * η i) (v : Fin (k + 1) → N)
    (hv : ∀ i : Fin k, v i.castSucc = b (.inl i)) (hv' : v (Fin.last k) = ∑ j, η j • b (.inr j)) :
    ∀ j ≤ k + 1, initSpan R u j = initSpan R v j := by
  have h0 : ∀ j ≤ k, initSpan R u j = initSpan R v j := fun j hj => by
    rw [initSpan_castSucc v hj, hu j hj]; simp only [hv]
  intro j hj
  rcases hj.eq_or_lt with rfl | hj
  · rw [initSpan_succ u hk, initSpan_succ v (Nat.lt_succ_self k), h0 k le_rfl]
    have hs : ∑ i : Fin k, b.repr (u ⟨k, hk⟩) (.inl i) • b (.inl i) ∈ initSpan R v k :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, i.2, hv i⟩)
    have hw : u ⟨k, hk⟩ = ∑ i : Fin k, b.repr (u ⟨k, hk⟩) (.inl i) • b (.inl i) +
        (e : R) • v ⟨k, Nat.lt_succ_self k⟩ := by
      conv_lhs => rw [← b.sum_repr (u ⟨k, hk⟩), Fintype.sum_sum_type]
      rw [show v ⟨k, Nat.lt_succ_self k⟩ = _ from hv', Finset.smul_sum]
      simp only [he, mul_smul]
    generalize ∑ i : Fin k, b.repr (u ⟨k, hk⟩) (.inl i) • b (.inl i) = s at hs hw
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · rw [Submodule.span_singleton_le_iff_mem, hw]
      exact Submodule.add_mem_sup hs (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    · rw [Submodule.span_singleton_le_iff_mem, ← Submodule.smul_mem_iff_of_isUnit _ e.isUnit,
        ← sub_eq_iff_eq_add'.2 hw]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        (Submodule.mem_sup_left hs)
  · exact h0 j (by omega)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem tanPull_basPull {Y X X' : Scheme.{0}} {t : SAB H Y} {π : X ⟶ Y} {f : X' ⟶ X} {U : X.Opens} {hU : IsAffineOpen U}
    {U' : X'.Opens} {hU' : IsAffineOpen U'} (le : U' ≤ f ⁻¹ᵁ U) {κ : Type} [Finite κ]
    (b : Module.Basis κ Γ(X, U) (TanM (tau hU ≫ π) t.G)) {S : Type} [CommRing S] (w : Sp S ⟶ X')
    (hw : ⊤ ≤ w ⁻¹ᵁ U') {x : Sp S ⟶ Y}
    (e₀ : spMap (ev (tau hU' ≫ f) U (le_preimage_map f le (tau_le hU' le_rfl))) ≫ tau hU ≫ π = tau hU' ≫ f ≫ π)
    (e₁ : spMap (ev w U' hw) ≫ tau hU' ≫ f ≫ π = x)
    (e₂ : spMap (ev (w ≫ f) U (le_preimage_map f le hw)) ≫ tau hU ≫ π = x) (i : κ) :
    tanPull (ev w U' hw) e₁ (basPull _ e₀ b i) = basPull _ e₂ b i := by
  have h1 : spMap (ev w U' hw) ≫ tau hU' ≫ f = w ≫ f := by rw [← Category.assoc, tau, spMap_ev]
  have h2 : (ev w U' hw).comp (ev (tau hU' ≫ f) U (le_preimage_map f le (tau_le hU' le_rfl))) =
      ev (w ≫ f) U (le_preimage_map f le hw) := by
    rw [← ev_spMap _ _ _ _ (h1 ▸ le_preimage_map f le hw)]
    exact FlagMod.ev_congr h1 _ _ _
  rw [basPull_apply, basPull_apply, tanPull_tanPull _ _ _ _ (by rw [h2]; exact e₂)]
  apply tan_ext
  rw [FlagMod.tanPull_left, FlagMod.tanPull_left, h2]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {σ : E →+* ℂ} {k : ℕ}

theorem flag_data {D : Adapted A σ k} {hk : k < Dw.mult σ} {X' : Scheme.{0}} {f : X' ⟶ X} {L : D.C.Line f}
    {ty' : (E →+* ℂ) → Finset ℕ} {A' : Atlas M (f ≫ π) ty'} (h : StepRel D hk L A') (β : L.J) {K : Type} [Field K]
    (w : Sp K ⟶ X') (hw : ⊤ ≤ w ⁻¹ᵁ L.B β) {x : Sp K ⟶ M.X} (e : (w ≫ f) ≫ π = x)
    (e₂ : spMap (ev (w ≫ f) _ (le_preimage_map f (L.le β) hw)) ≫ tau (D.C.aff (L.a β)) ≫ π = x)
    (u : TVecs Dw M.t x) (hu : A'.FlagAt w (up u)) :
    (∀ j ≤ k, initSpan K (u σ) j = initSpan K (fun i : Fin k => basPull _ e₂ (D.b (L.a β)) (.inl i)) j) ∧
      ∃ e : Kˣ, ∀ i, (basPull _ e₂ (D.b (L.a β))).repr (u σ ⟨k, hk⟩) (.inr i) = (e : K) * ev w _ hw (L.η β i) := by
  subst e
  obtain ⟨h1, h2⟩ := (h K w u).1 hu
  refine ⟨D.int (L.a β) K (w ≫ f) _ u h1, ?_⟩
  obtain ⟨e, he⟩ := h2 (L.a β) (le_preimage_map f (L.le β) hw) β hw
  rw [Coc.tr_self, Matrix.one_mulVec] at he
  exact ⟨e, fun i => congrFun he i⟩

theorem intStep_succ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F)
    [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X)
    (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ)
    (X' : Scheme.{0}) (f : X' ⟶ X) (L : D.C.Line f) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas M (f ≫ π) ty')
    (h : StepRel D hk L A') : IntStep A' σ (k + 1) := by
  intro x
  obtain ⟨β, hx⟩ := L.cover x
  obtain ⟨c₀, hc⟩ := L.unit β
  have e₀ : spMap (ev (tau (L.aff β) ≫ f) _ (le_preimage_map f (L.le β) (tau_le (L.aff β) le_rfl))) ≫
      tau (D.C.aff (L.a β)) ≫ π = tau (L.aff β) ≫ f ≫ π := by
    rw [← Category.assoc, tau.eq_1 (D.C.aff (L.a β)), spMap_ev, Category.assoc]
  obtain ⟨m, b', h1, h2⟩ := exists_basis_succ (basPull _ e₀ (D.b (L.a β))) (L.η β) c₀ hc
  refine ⟨L.B β, L.aff β, m, b', hx, fun K _ w hw u hu => ?_⟩
  have e₂ : spMap (ev (w ≫ f) _ (le_preimage_map f (L.le β) hw)) ≫ tau (D.C.aff (L.a β)) ≫ π = w ≫ f ≫ π := by
    rw [← Category.assoc, tau, spMap_ev, Category.assoc]
  obtain ⟨g1, e, g2⟩ := flag_data h β w hw (Category.assoc _ _ _) e₂ u hu
  refine initSpan_step _ _ (u σ) hk g1 e g2 _ (fun i => ?_) ?_
  · rw [basAt, basPull_apply, h1]
    exact tanPull_basPull (L.le β) _ w hw e₀ _ e₂ _
  · rw [basAt, basPull_apply, h2, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulₛₗ, tanPull_basPull (L.le β) _ w hw e₀ _ e₂ _]

end GlobalTheory.DRFlag.StepInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedNextStepType
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.FrSub

section Lin

variable {K N : Type} [Field K] [AddCommGroup N] [Module K N]

theorem repr_inr_eq_zero_iff {k m : ℕ} (b : Module.Basis (Fin k ⊕ Fin m) K N) (v : N) :
    (∀ j, b.repr v (.inr j) = 0) ↔ v ∈ initSpan K (fun i : Fin k => b (.inl i)) k := by
  have h : initSpan K (fun i : Fin k => b (.inl i)) k = Submodule.span K (b '' Set.range Sum.inl) := by
    rw [initSpan, ← Set.range_comp]
    congr 1
    ext x
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩⟩
  rw [h, Module.Basis.mem_span_image]
  constructor
  · rintro h (i | j) hi
    · exact ⟨i, rfl⟩
    · exact absurd (h j) (Finsupp.mem_support_iff.1 hi)
  · intro h j
    by_contra hne
    obtain ⟨i, hi⟩ := h (Finsupp.mem_support_iff.2 hne)
    exact Sum.inl_ne_inr hi

variable {n m k r : ℕ} (q : N →ₗ[K] (Fin m → K)) {u : Fin n → N} (hj : k + r + 1 ≤ n)

theorem eq_zero_of_sum (hu : LinearIndependent K u) (hq : ∀ v, q v = 0 → v ∈ initSpan K u k) (c : Fin (r + 1) → K)
    (hc : ∑ i, c i • q (u ⟨k + i, by omega⟩) = 0) : c = 0 := by
  let e : Fin (r + 1) → Fin n := fun i => ⟨k + i, by omega⟩
  have he : Function.Injective e := fun i i' h => Fin.ext (by have := congrArg Fin.val h; simp only [e] at this; omega)
  have h1 : ∑ i, c i • u (e i) ∈ initSpan K u k := hq _ (by simpa only [map_sum, map_smul] using hc)
  have h2 : ∑ i, c i • u (e i) ∈ Submodule.span K (u '' {j : Fin n | k ≤ (j : ℕ)}) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨e i, Nat.le_add_right _ _, rfl⟩)
  have hd : Disjoint {j : Fin n | (j : ℕ) < k} {j : Fin n | k ≤ (j : ℕ)} :=
    Set.disjoint_left.2 fun j h h' => (not_lt.2 (show k ≤ (j : ℕ) from h')) (show (j : ℕ) < k from h)
  have h3 := Submodule.disjoint_def.1 (hu.disjoint_span_image hd) _ h1 h2
  exact funext (Fintype.linearIndependent_iff.1 (hu.comp e he) c h3)

theorem exists_sum (hq : ∀ v ∈ initSpan K u k, q v = 0) {v : N} (hv : v ∈ initSpan K u (k + r + 1)) :
    ∃ c : Fin (r + 1) → K, ∑ i, c i • q (u ⟨k + i, by omega⟩) = q v := by
  rw [← Submodule.mem_span_range_iff_exists_fun]
  refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap q _)).2 ?_ hv)
  rintro _ ⟨j, hj', rfl⟩
  have hj'' : (j : ℕ) < k + r + 1 := hj'
  show q (u j) ∈ Submodule.span K _
  by_cases h : (j : ℕ) < k
  · rw [hq _ (Submodule.subset_span ⟨j, h, rfl⟩)]
    exact Submodule.zero_mem _
  · refine Submodule.subset_span ⟨⟨j - k, by omega⟩, ?_⟩
    have : (⟨k + (j - k), by omega⟩ : Fin n) = j := Fin.ext (by simp only; omega)
    simp only [this]

theorem initSpan_full (u : Fin n → N) : initSpan K u n = Submodule.span K (Set.range u) := by
  rw [initSpan]
  congr 1
  ext x
  exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩⟩

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {σ : E →+* ℂ} {k : ℕ}

def crdL {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) : TanM (z ≫ π) M.t.G →ₗ[S] (Fin m → S) :=
  LinearMap.pi fun j => (basAt b z h).coord (.inr j)

theorem crdL_apply {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) (v : TanM (z ≫ π) M.t.G) : crdL b z h v = crd b z h v := rfl

theorem crdL_eq_zero_iff (D : Adapted A σ k) (α : D.C.A) {K : Type} [Field K] (z : Sp K ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u)) (v : TanM (z ≫ π) M.t.G) :
    crdL (D.b α) z h v = 0 ↔ v ∈ initSpan K (u σ) k := by
  rw [D.int α K z h u hu k le_rfl, ← repr_inr_eq_zero_iff]
  exact funext_iff

theorem exists_isFrSub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hj : k + r + 1 ≤ Dw.mult σ), (k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) → ∀ α : A.ch.ι → D.C.A, (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ Sb : D.C.Sub A.ch r, IsFrSub D Sb hj := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A σ k r D hj hty α hα
  choose u hu using fun a => exists_up (Dw := Dw) (x := A.ch.χ a ≫ π) fun σ i => ((A.frame a).1 σ i).1
  let Mx : ∀ a, Matrix (Fin (D.C.n (α a))) (Fin (r + 1)) (A.ch.R a) := fun a j i =>
    crd (D.b (α a)) (A.ch.χ a) (hα a) (u a σ ⟨k + i, by omega⟩) j
  have key : ∀ (a : A.ch.ι) (S : Type) [CommRing S] (φ : A.ch.R a →+* S) (z : Sp S ⟶ X), spMap φ ≫ A.ch.χ a = z →
      ∀ (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (α a)) (w : TVecs Dw M.t (z ≫ π)), up w = (A.fr a).bc φ →
      ∀ i : Fin (r + 1), (fun j => φ (Mx a j i)) = crd (D.b (α a)) z h (w σ ⟨k + i, by omega⟩) := by
    intro a S _ φ z e h w hw i
    have e' : spMap φ ≫ A.ch.χ a ≫ π = z ≫ π := by rw [← Category.assoc, e]
    have hw' : w = fun σ i => tanPull φ e' (u a σ i) := up_injective (by rw [hw, up_tanPull, hu])
    subst hw'
    funext j
    exact (basAt_repr (D.b (α a)) φ (A.ch.χ a) (hα a) e h e' _ _).symm
  have mul : ∀ (a : A.ch.ι) (K : Type) [Field K] (φ : A.ch.R a →+* K) (z : Sp K ⟶ X), spMap φ ≫ A.ch.χ a = z →
      ∀ (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (α a)) (w : TVecs Dw M.t (z ≫ π)), up w = (A.fr a).bc φ →
      ∀ cf : Fin (r + 1) → K, ((Mx a).map φ).mulVec cf =
        ∑ i, cf i • crdL (D.b (α a)) z h (w σ ⟨k + i, by omega⟩) := by
    intro a K _ φ z e h w hw cf
    funext j
    simp only [crdL_apply, ← key a K φ z e h w hw, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨⟨α, hα, Mx, fun a K _ φ => ?_, fun a a' K _ φ φ' z e e' h h' => ?_⟩, key⟩
  · have h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a) := fun x _ => hα a (Set.mem_univ (spMap φ x))
    obtain ⟨w, hw⟩ := A.exists_up_fr (φ := φ) rfl
    have hf := A.isFrame_bc (φ := φ) rfl
    have hF := A.flagAt_fr (φ := φ) rfl
    rw [← hw] at hf hF
    refine (injective_iff_map_eq_zero ((Mx a).map φ).mulVecLin).2 fun cf hc => ?_
    refine eq_zero_of_sum (crdL (D.b (α a)) _ h) hj ((isFrame_up_iff _ _).1 hf σ).1
      (fun v hv => (crdL_eq_zero_iff D _ _ h hF v).1 hv) cf ?_
    rw [← mul a K φ _ rfl h w hw]
    exact hc
  · obtain ⟨w, hw⟩ := A.exists_up_fr e
    obtain ⟨w', hw'⟩ := A.exists_up_fr e'
    have hf := A.isFrame_bc e
    have hF := A.flagAt_fr e
    have hf' := A.isFrame_bc e'
    have hF' := A.flagAt_fr e'
    rw [← hw] at hf hF
    rw [← hw'] at hf' hF'
    have hs : initSpan K (w' σ) (k + r + 1) = initSpan K (w σ) (k + r + 1) := by
      rcases hty with hty | hty
      · exact hF'.initSpan_eq hF σ hty
      · rw [← A.alg_eq e e'] at hf'
        rw [hty, initSpan_full, initSpan_full, ((isFrame_up_iff _ _).1 hf σ).2, ((isFrame_up_iff _ _).1 hf' σ).2]
    have hm : ∀ i : Fin (r + 1), w' σ ⟨k + i, by omega⟩ ∈ initSpan K (w σ) (k + r + 1) := fun i =>
      hs ▸ Submodule.subset_span ⟨_, by show k + (i : ℕ) < k + r + 1; omega, rfl⟩
    choose cf hcf using fun i => exists_sum (crdL (D.b (α a)) z h) hj
      (fun v hv => (crdL_eq_zero_iff D _ _ h hF v).2 hv) (hm i)
    refine ⟨Matrix.of fun p i => cf i p, ?_⟩
    ext j i
    have h1 := D.coord (α a) (α a') K z h h' (w' σ ⟨k + i, by omega⟩)
    rw [← key a' K φ' z e' h' w' hw' i, ← crdL_apply, ← hcf i, ← mul a K φ z e h w hw] at h1
    exact congrFun h1 j

end GlobalTheory.DRFlag.FrSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcFramedPointExtendsToModelBoundaryStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_framed_point_extends_to_model_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) [Algebra c.F ℂ⸨X⸩] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (y : FrPt Xo c ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → ArcBasis W (fun τ => σ.comp (embK c τ)) e → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → χ (IsLocalRing.closedPoint (PowerSeries ℂ)) ∉ abLocus Y.t.G → BdExt Y ((PowerSeries.C (R := ℂ)).comp σ) y := by
  first | exact @GlobalTheory.CuspFrom.arc_bdExt | exact GlobalTheory.CuspFrom.arc_bdExt | (intros; apply GlobalTheory.CuspFrom.arc_bdExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlowOrbitFirstMinimumOfIsotropicFlowMajorantStatement
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flowOrbitFirstMinimum_of_isotropicFlowMajorant : FlowMajSt → OrbitThickSt := by
  first | exact @GlobalTheory.CuspFrom.OrbitThick.orbitThick_of_flowMaj | exact GlobalTheory.CuspFrom.OrbitThick.orbitThick_of_flowMaj | (intros; apply GlobalTheory.CuspFrom.OrbitThick.orbitThick_of_flowMaj <;> assumption)
end

