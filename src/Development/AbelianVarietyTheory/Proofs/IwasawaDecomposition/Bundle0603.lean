import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAdaptedOfIntStep
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.AdaptedOfStep

theorem eq_zero_of_dense {X : Scheme.{0}} [IsReduced X] {D : Set X} (hD : Dense D) {U : X.Opens} (f : Γ(X, U))
    (h : ∀ (K : Type) [Field K] (w : Sp K ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ U), w (IsLocalRing.closedPoint K) ∈ D →
      ev w U hw f = 0) : f = 0 := by
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen f).isOpen
    (((X.basicOpen f).ne_bot_iff_nonempty).1 hne)
  let w : Sp (X.residueField x) ⟶ X := X.fromSpecResidueField x
  have hr : ∀ p, w p = x := fun p => Scheme.fromSpecResidueField_apply x p
  have hb : ⊤ ≤ w ⁻¹ᵁ X.basicOpen f := fun p _ => show w p ∈ X.basicOpen f by rw [hr]; exact hx
  have hw : ⊤ ≤ w ⁻¹ᵁ U := le_preimage_mono (X.basicOpen_le f) hb
  have h0 := h _ w hw ((hr _).symm ▸ hxD)
  have hu : IsUnit (resG X (X.basicOpen_le f) f) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace f
  have := hu.map (ev w _ hb)
  rw [ev_res w _ hb hw, h0] at this
  exact not_isUnit_zero this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {σ : E →+* ℂ} {k : ℕ}

theorem isAffineOpen_inf (g : Geo M π) {U U' : X.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') :
    IsAffineOpen (U ⊓ U') := by
  have := projProper _ _ _ g.proj
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from (π ≫ M.s)]
    infer_instance⟩
  exact hU.inf hU'

variable {U U' : X.Opens} {hU : IsAffineOpen U} {hU' : IsAffineOpen U'} {m m' : ℕ}
  {b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)}
  {b' : Module.Basis (Fin k ⊕ Fin m') Γ(X, U') (TanM (tau hU' ≫ π) M.t.G)}

theorem crd_basAt {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (w : Sp S ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ U)
    (hw' : ⊤ ≤ w ⁻¹ᵁ U') {z : Sp S' ⟶ X} (e : spMap φ ≫ w = z) (hz : ⊤ ≤ z ⁻¹ᵁ U) (hz' : ⊤ ≤ z ⁻¹ᵁ U')
    (i : Fin k ⊕ Fin m') (j : Fin m) :
    crd b z hz (basAt b' z hz' i) j = φ (crd b w hw (basAt b' w hw' i) j) := by
  have e' : spMap φ ≫ w ≫ π = z ≫ π := by rw [← e, Category.assoc]
  rw [← tanPull_basAt b' φ w hw' e hz' e']
  exact basAt_repr b φ w hw e hz e' _ _

theorem crd_inl_field (hb : IntOn A σ k hU b) (hb' : IntOn A σ k hU' b') (K : Type) [Field K] (w : Sp K ⟶ X)
    (hw : ⊤ ≤ w ⁻¹ᵁ U) (hw' : ⊤ ≤ w ⁻¹ᵁ U') (hD : w (IsLocalRing.closedPoint K) ∈ π ⁻¹' Set.range M.j)
    (i : Fin k) (j : Fin m) : crd b w hw (basAt b' w hw' (.inl i)) j = 0 := by
  rw [← A.cover] at hD
  obtain ⟨a, φ, e⟩ := A.ch.exists_fac w hD
  obtain ⟨u, hu⟩ := A.exists_up_fr e
  have hf : A.FlagAt w (up u) := hu ▸ A.flagAt_fr e
  have h1 : basAt b' w hw' (.inl i) ∈ initSpan K (fun i : Fin k => basAt b' w hw' (.inl i)) k :=
    Submodule.subset_span ⟨i, i.2, rfl⟩
  rw [← hb' K w hw' u hf k le_rfl, hb K w hw u hf k le_rfl] at h1
  obtain ⟨cf, -, h2⟩ := mem_initSpan.1 h1
  rw [← h2]
  simp [crd]

theorem crd_inl (g : Geo M π) (hb : IntOn A σ k hU b) (hb' : IntOn A σ k hU' b') {S : Type} [CommRing S]
    (z : Sp S ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ U) (hz' : ⊤ ≤ z ⁻¹ᵁ U') (i : Fin k) (j : Fin m) :
    crd b z hz (basAt b' z hz' (.inl i)) j = 0 := by
  have hI := isAffineOpen_inf g hU hU'
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => have := (g.normal x).1; inferInstance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have h0 : crd b (tau hI) (tau_le hI inf_le_left) (basAt b' (tau hI) (tau_le hI inf_le_right) (.inl i)) j = 0 :=
    eq_zero_of_dense g.dense _ fun K _ w hw hD =>
      (crd_basAt _ (tau hI) _ _ (spMap_ev w hI hw) (le_preimage_mono inf_le_left hw)
        (le_preimage_mono inf_le_right hw) _ _).symm.trans (crd_inl_field hb hb' K w _ _ hD i j)
  rw [crd_basAt _ (tau hI) (tau_le hI inf_le_left) (tau_le hI inf_le_right)
    (spMap_ev z hI (le_preimage_inf hz hz')), h0, map_zero]

variable (b b') in

def trans (g : Geo M π) : Matrix (Fin m) (Fin m') Γ(X, U ⊓ U') := fun j i =>
  crd b (tau (isAffineOpen_inf g hU hU')) (tau_le _ inf_le_left)
    (basAt b' (tau (isAffineOpen_inf g hU hU')) (tau_le _ inf_le_right) (.inr i)) j

theorem trans_map (g : Geo M π) {S : Type} [CommRing S] (z : Sp S ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ U) (hz' : ⊤ ≤ z ⁻¹ᵁ U')
    (j : Fin m) (i : Fin m') : (trans b b' g).map (ev z _ (le_preimage_inf hz hz')) j i =
      crd b z hz (basAt b' z hz' (.inr i)) j :=
  (crd_basAt _ (tau (isAffineOpen_inf g hU hU')) _ _ (spMap_ev z _ (le_preimage_inf hz hz')) hz hz' _ _).symm

theorem trans_mulVec (g : Geo M π) (hb : IntOn A σ k hU b) (hb' : IntOn A σ k hU' b') {S : Type} [CommRing S]
    (z : Sp S ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ U) (hz' : ⊤ ≤ z ⁻¹ᵁ U') (v : TanM (z ≫ π) M.t.G) :
    ((trans b b' g).map (ev z _ (le_preimage_inf hz hz'))).mulVec (crd b' z hz' v) = crd b z hz v := by
  funext j
  have h0 := fun i => crd_inl g hb hb' z hz hz' i j
  conv_rhs => rw [← (basAt b' z hz').sum_repr v]
  simp only [Matrix.mulVec, dotProduct, trans_map g z hz hz']
  simp only [crd] at h0 ⊢
  rw [Fintype.sum_sum_type]
  simp only [map_add, map_sum, map_smul, Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    h0, mul_zero, Finset.sum_const_zero, zero_add]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem nonempty_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ), Geo M π → IntStep A σ k → Nonempty (Adapted A σ k) := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A σ k g h
  choose U hU m b hx hb using h
  refine ⟨⟨⟨X, U, hU, fun x => ⟨x, hx x⟩, m, fun α β => trans (b α) (b β) g, fun α S _ z hz => ?_,
    fun α β γ S _ z h₁ h₂ h₃ => ?_⟩, b, hb, fun α β S _ z h₁ h₂ v => trans_mulVec g (hb α) (hb β) z h₁ h₂ v⟩⟩
  · ext j i
    rw [trans_map g z hz hz]
    simp [crd, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  · ext j i
    rw [trans_map g z h₁ h₃, ← trans_mulVec g (hb α) (hb β) z h₁ h₂, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun q _ => by rw [trans_map g z h₂ h₃]

end GlobalTheory.DRFlag.AdaptedOfStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsChangeOfEigenFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.Chg

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {i : Fin Fu.n}
  {P : (Fu.Di i).La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ Xo.XF c}

variable (Z P y) in

def Lifts (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ Z.t.G.left) : Prop :=
  ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
    v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = v ∧
    IsDerivAt0 (fun w => (Fu.ex i P w).left) w (v₀ ≫ Z.m0.toSABMap.φ)

variable (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
  (hy : y ≫ pullback.fst _ _ = Fu.u i P) {x : Sp ℂ ⟶ Z.X} (hx : y ≫ Z.jQ ≫ pullback.fst _ _ = x)

include hP hy hx

theorem exists_dir {v : Sp (DualNumber ℂ) ⟶ Z.t.G.left} (hv : IsTanAtG Z.t x v) : ∃ w, Lifts Z P y w v := by
  obtain ⟨v₀, h1, rfl⟩ := exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [hv.1, ← hx, Category.assoc])
  obtain ⟨w, hw, -⟩ := (isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP).2.2 _
    ((tan_iff Z.m0.toSABMap hy h1).2 ((tan_iff Z.m hx h1).1 hv))
  exact ⟨w, v₀, h1, rfl, hw⟩

theorem eq_sum_of_comb {n : ℕ} {v : Fin n → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)} {W : Fin n → Fin g → ℂ}
    (hW : ∀ k, Lifts Z P y (W k) (v k)) {v' : Sp (DualNumber ℂ) ⟶ Z.t.G.left} {w : Fin g → ℂ} (hw : Lifts Z P y w v')
    {a : Fin n → ℂ} (h : IsCombAtG Z.t x v a v') : w = ∑ k, a k • W k := by
  choose u h1 h2 h3 using hW
  obtain ⟨u', h1', rfl, h3'⟩ := hw
  obtain rfl : v = fun k => u k ≫ Z.m.φ := funext fun k => (h2 k).symm
  have h4 := (comb_iff Z.m0.toSABMap hy h1 a h1').2 ((comb_iff Z.m hx h1 a h1').1 h)
  have h5 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP n _ W h3 a _).1 h4
  have ht := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  exact (ht.2.2 _ (ht.1 _ _ h3')).unique h3' h5

theorem span_eq_top (f : EigFrame Z σ x) {W : Letter Dw → Fin g → ℂ} (hW : ∀ z, Lifts Z P y (W z) (f.v z.1 z.2)) :
    ⊤ ≤ Submodule.span ℂ (Set.range W) := by
  rw [← (Pi.basisFun ℂ (Fin g)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have ht := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := ht.2.1 (Pi.basisFun ℂ (Fin g) j)
  have he := (isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ v (e j).1 hv).2 (fun k hk => by
    obtain rfl : k = j := by
      by_contra hne
      exact hk (by simp [hne])
    rfl)
  have htan := ht.1 _ _ hv
  obtain ⟨v₀, h1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [htan.1, ← hy, Category.assoc])
  obtain ⟨a, ha, -⟩ := f.basis (e j).1 (v₀ ≫ Z.m.φ) ((tan_iff Z.m hx h1).2 ((tan_iff Z.m0.toSABMap hy h1).1 htan))
    fun a => (eig_iff Z.m h1 a _).2 ((eig_iff Z.m0.toSABMap h1 a _).1 (he a))
  rw [eq_sum_of_comb hP hy hx (W := fun k => W ⟨(e j).1, k⟩) (fun k => hW ⟨_, k⟩) ⟨v₀, h1, rfl, hv⟩ ha]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem linearIndependent (f : EigFrame Z σ x) {W : Letter Dw → Fin g → ℂ}
    (hW : ∀ z, Lifts Z P y (W z) (f.v z.1 z.2)) : LinearIndependent ℂ W :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (span_eq_top hP hy hx f hW)
    (by rw [← Fintype.card_congr e]; simp)

end GlobalTheory.ShFam.Hor.Chg

namespace GlobalTheory.ShFam.Hor

theorem per_chg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a a' : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)), Per Fu a i Q → a.1 = a'.1 → ∃ Q', Per Fu a' i Q' ∧ ∀ ρ M, Chg a a' ρ M → ∀ v k, Q v ⟨ρ, k⟩ = ∑ j, Q' v ⟨ρ, j⟩ * M j k := by
  rintro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu ⟨x, f⟩ ⟨x', f'⟩ i Q ⟨P, W, y, hP, hy, hyx, hW, hQ⟩ hxx
  obtain rfl : x = x' := hxx
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = x.1 ≫ genι Z := by rw [← Category.assoc, hyx]
  choose W' hW' using fun z : Letter Dw => Chg.exists_dir hP hy hx (f'.tan z.1 z.2)
  let b := Module.Basis.mk (Chg.linearIndependent hP hy hx f' hW') (Chg.span_eq_top hP hy hx f' hW')
  let Q' : (Fu.Di i).La →+ (Letter Dw → ℂ) := b.equivFun.toLinearMap.toAddMonoidHom.comp P
  have hQ' : ∀ v, P v = ∑ z, Q' v z • W' z := fun v => by
    have := b.sum_equivFun (P v)
    simp only [b, Module.Basis.coe_mk] at this
    exact this.symm
  refine ⟨Q', ⟨P, W', y, hP, hy, hyx, hW', hQ'⟩, fun ρ M hM v k => ?_⟩
  choose N hN using fun (τ : E →+* ℂ) j => (f.basis τ _ (f'.tan τ j) (f'.eig τ j)).exists
  have hNM : ∀ j, N ρ j = M j := fun j => (f.basis ρ _ (f'.tan ρ j) (f'.eig ρ j)).unique (hN ρ j) (hM.2 j)
  have hc : ∀ τ j, W' ⟨τ, j⟩ = ∑ k, N τ j k • W ⟨τ, k⟩ := fun τ j =>
    Chg.eq_sum_of_comb hP hy hx (W := fun k => W ⟨τ, k⟩) (fun k => hW ⟨τ, k⟩) (hW' ⟨τ, j⟩) (hN τ j)
  have h1 : ∑ z, Q v z • W z = ∑ z : Letter Dw, (∑ j, Q' v ⟨z.1, j⟩ * N z.1 j z.2) • W z := by
    rw [← hQ, hQ', Fintype.sum_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [hc, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have h2 := Fintype.linearIndependent_iffₛ.1 (Chg.linearIndependent hP hy hx f hW) _ _ h1 ⟨ρ, k⟩
  simp only [hNM] at h2
  exact h2

end GlobalTheory.ShFam.Hor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpace
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.LineOfMap

open GlobalTheory.ProjSpace GlobalTheory.FlagMod

variable {Z : Scheme.{0}} {S : Type} [CommRing S]

theorem resG_refl {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  show (X.presheaf.map (homOfLE h).op).hom a = a
  rw [show (homOfLE h).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem fnOn_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U)) :
    fnOn ⊤ (ev z U h a) = (z.appLE U ⊤ h).hom a := by
  refine (resG_refl (X := Sp S) le_top _).trans ?_
  exact (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply _

theorem mem_basicOpen_of_isUnit_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U))
    (hu : IsUnit (ev z U h a)) (p : Sp S) : z p ∈ Z.basicOpen a := by
  have h1 := Scheme.basicOpen_of_isUnit _ (hu.map (fnOn ⊤))
  rw [fnOn_ev] at h1
  exact (((Scheme.basicOpen_appLE z ⊤ U h a).symm.trans h1).ge (Set.mem_univ p)).2

theorem isUnit_ev_of_le (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U))
    (hu : ⊤ ≤ z ⁻¹ᵁ Z.basicOpen a) : IsUnit (ev z U h a) := by
  rw [← ev_res z (Z.basicOpen_le a) hu h]
  exact (Z.toRingedSpace.isUnit_res_basicOpen a).map _

theorem residue_le {U : Z.Opens} {x : Z} (hx : x ∈ U) :
    ⊤ ≤ (Z.fromSpecResidueField x : Sp (Z.residueField x) ⟶ Z) ⁻¹ᵁ U := fun p _ => by
  show Z.fromSpecResidueField x p ∈ U
  rwa [Scheme.fromSpecResidueField_apply]

theorem eq_zero_of_dense [IsReduced Z] {Ω : Set Z} (hΩ : Dense Ω) {U : Z.Opens} (a : Γ(Z, U))
    (H : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), Set.range w ⊆ Ω → ∀ h : ⊤ ≤ w ⁻¹ᵁ U, ev w U h a = 0) : a = 0 := by
  refine eq_zero_of_basicOpen_eq_bot a ?_
  by_contra hne
  obtain ⟨x, hx, hxΩ⟩ := hΩ.inter_open_nonempty _ (Z.basicOpen a).isOpen
    ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne)
  have h1 := residue_le (Z.basicOpen_le a hx)
  refine (isUnit_ev_of_le _ U h1 a (residue_le hx)).ne_zero (H _ _ ?_ h1)
  rintro _ ⟨p, rfl⟩
  exact (Scheme.fromSpecResidueField_apply x p).symm ▸ hxΩ

variable {O : Type} [CommRing O] {N : ℕ}

theorem comp_eq_pt (q : Z ⟶ PSpace O N) {U : Z.Opens} {i : Fin (N + 1)} (hi : U ≤ q ⁻¹ᵁ chart O N i)
    (w : Sp S ⟶ Z) (hw : ⊤ ≤ w ⁻¹ᵁ U) (g : O →+* S) (hg : (w ≫ q) ≫ PSpace.str O N = spMap g) :
    ∃ hv, w ≫ q = pt g (fun j => ev w U hw (pullRatio q U i hi j)) hv := by
  have h1 : ev w U hw (pullRatio q U i hi i) = 1 := by rw [pullRatio_self, map_one]
  have hv : Ideal.span (Set.range fun j => ev w U hw (pullRatio q U i hi j)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (by simp only [h1, isUnit_one])
  refine ⟨hv, hom_ext (hg.trans (pt_str _ _ hv).symm) fun y => ?_⟩
  have h2 : ⊤ ≤ pt g _ hv ⁻¹ᵁ chart O N i := by
    rw [pt_preimage_chart, h1]
    exact fun p _ => mem_spOpen.2 ((Ideal.ne_top_iff_one _).1 p.isPrime.ne_top)
  refine ⟨⊤, trivial, i, le_preimage_map q hi hw, h2, fun j => ?_⟩
  have h3 := pullRatio_pt_mul g _ hv i j h2
  rw [h1, map_one, _root_.mul_one, fnOn_ev, appLE_pullRatio] at h3
  exact h3.symm

theorem exists_local {Z' : Scheme.{0}} (s : Z ⟶ Sp O) (f : Z' ⟶ Z) (C : Coc Z) (Em : C.Emb N) (q : Z' ⟶ PSpace O N)
    (Ω : Set Z') (hq : q ≫ PSpace.str O N = f ≫ s) [IsReduced Z'] (hΩ : Dense Ω)
    (H : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α),
      ∃ (ξ : Fin (C.n α) → K) (g : O →+* K) (hv : _),
        w ≫ q = pt g (((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ) hv) (x : Z') :
    ∃ (B : Z'.Opens) (_ : IsAffineOpen B) (_ : x ∈ B) (α : C.A) (le : B ≤ f ⁻¹ᵁ C.B α) (η : Fin (C.n α) → Γ(Z', B)),
      (∃ c, IsUnit (η c)) ∧ ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ B) (g : O →+* K),
        w ≫ f ≫ s = spMap g → ∃ hv, w ≫ q = pt g (((Em.A α).map (ev (w ≫ f) _ (le_preimage_map f le hw))).mulVec
          fun i => ev w _ hw (η i)) hv := by
  obtain ⟨α, hα⟩ := C.cover (f x)
  obtain ⟨i, hi⟩ := exists_mem_chart O N (q x)
  obtain ⟨A', hA'⟩ := Em.linv α
  let U : Z'.Opens := f ⁻¹ᵁ C.B α ⊓ q ⁻¹ᵁ chart O N i
  have hxU : x ∈ U := ⟨hα, hi⟩
  let φ : Γ(Z, C.B α) →+* Γ(Z', U) := (f.appLE (C.B α) U inf_le_left).hom
  let ξ : Fin (N + 1) → Γ(Z', U) := pullRatio q U i inf_le_right
  let η : Fin (C.n α) → Γ(Z', U) := (A'.map φ).mulVec ξ
  have hev : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U) {m n : ℕ}
      (M : Matrix (Fin m) (Fin n) Γ(Z, C.B α)) (v : Fin n → Γ(Z', U)),
      (fun j => ev w U hw ((M.map φ).mulVec v j)) =
        (M.map (ev (w ≫ f) _ (le_preimage_map f inf_le_left hw))).mulVec fun j => ev w U hw (v j) := by
    intro K _ w hw m n M v
    funext j
    rw [RingHom.map_mulVec, Matrix.map_map]
    congr 2
    exact funext fun a => ev_appLE w f _ hw _ a
  have hpt : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U) (g : O →+* K), w ≫ f ≫ s = spMap g →
      ∃ hv, w ≫ q = pt g (fun j => ev w U hw (ξ j)) hv := fun K _ w hw g hg =>
    comp_eq_pt q inf_le_right w hw g (by rw [Category.assoc, hq, hg])
  have key : ((Em.A α).map φ).mulVec η = ξ := by
    funext j
    refine sub_eq_zero.1 (eq_zero_of_dense hΩ _ fun K _ w hwΩ hw => ?_)
    obtain ⟨ξ₀, g, hv, e⟩ := H K w hwΩ α (le_preimage_map f inf_le_left hw)
    obtain ⟨hv', e'⟩ := hpt K w hw g (by rw [← hq, ← Category.assoc, e, pt_str])
    obtain ⟨u, hu⟩ := (pt_eq_pt_iff g hv hv').1 (e.symm.trans e')
    rw [map_sub, sub_eq_zero]
    refine congrFun (f := fun j => ev w U hw ((((Em.A α).map φ).mulVec η) j)) (g := fun j => ev w U hw (ξ j)) ?_ j
    rw [hev, hev, hu, Units.smul_def, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.map_mul, hA',
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, Matrix.mulVec_smul]
  have hc : ∃ c, x ∈ Z'.basicOpen (η c) := by
    have hw := residue_le hxU
    by_contra! hn
    have h0 : (fun c => ev _ U hw (η c)) = 0 := funext fun c => by
      by_contra hne
      have := mem_basicOpen_of_isUnit_ev _ U hw _ (Ne.isUnit hne) (IsLocalRing.closedPoint _)
      exact hn c ((Scheme.fromSpecResidueField_apply x _) ▸ this)
    have h1 := congrFun (hev _ _ hw (Em.A α) η) i
    rw [h0, Matrix.mulVec_zero, key] at h1
    have h2 : ξ i = 1 := pullRatio_self
    simp only [h2, map_one, Pi.zero_apply] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc⟩ := hc
  obtain ⟨_, ⟨B, hB, rfl⟩, hxB, hle⟩ := Z'.isBasis_affineOpens.exists_subset_of_mem_open hc (Z'.basicOpen (η c)).isOpen
  have hBU : B ≤ U := fun y hy => Z'.basicOpen_le _ (hle hy)
  refine ⟨B, hB, hxB, α, hBU.trans inf_le_left, fun j => resG Z' hBU (η j), ⟨c, ?_⟩, fun K _ w hw g hg => ?_⟩
  · refine isUnit_of_basicOpen_eq _ ((Scheme.basicOpen_res _ _ _).trans (inf_eq_left.2 hle))
  · have hw' := le_preimage_mono hBU hw
    obtain ⟨hv, e⟩ := hpt K w hw' g hg
    have e1 : (fun j => ev w U hw' (ξ j)) = ((Em.A α).map (ev (w ≫ f) _ (le_preimage_map f (hBU.trans inf_le_left)
        hw))).mulVec fun i => ev w _ hw (resG Z' hBU (η i)) := by
      rw [← key, hev]
      congr 1
      exact funext fun j => (ev_res w hBU hw hw' _).symm
    exact ⟨e1 ▸ hv, e.trans (by congr 1)⟩

theorem exists_line : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (s : Z ⟶ Sp O) (f : Z' ⟶ Z) (C : Coc Z) (N : ℕ) (Em : C.Emb N) (q : Z' ⟶ PSpace O N) (Ω : Set Z'), q ≫ PSpace.str O N = f ≫ s → IsReduced Z' → Dense Ω → (∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), ∃ (ξ : Fin (C.n α) → K) (g : O →+* K) (hv : _), w ≫ q = GlobalTheory.ProjSpace.pt g (((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ) hv) → ∃ L : C.Line f, ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin (C.n α) → K) (g : O →+* K), w ≫ f ≫ s = spMap g → (L.Carries w α h ξ ↔ ∃ hv, w ≫ q = GlobalTheory.ProjSpace.pt g (((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ) hv) := by
  intro O _ Z Z' s f C N Em q Ω hq hred hΩ H
  choose B aff mem a le η unit hη using exists_local s f C Em q Ω hq hΩ H
  refine ⟨⟨Z', B, aff, fun x => ⟨x, mem x⟩, a, le, η, unit⟩, fun K _ w α h ξ g hg => ⟨fun hL => ?_, ?_⟩⟩
  · have hw : ⊤ ≤ w ⁻¹ᵁ B (w (IsLocalRing.closedPoint K)) :=
      ((IsLocalRing.closed_point_mem_iff (U := w ⁻¹ᵁ B _)).1 (mem _)).ge
    generalize w (IsLocalRing.closedPoint K) = β at hw
    obtain ⟨u, hu⟩ := hL β hw
    obtain ⟨hv, e⟩ := hη β K w hw g hg
    obtain ⟨u', hu'⟩ := Em.compat (a β) α K (w ≫ f) (le_preimage_map f (le β) hw) h
    have hu1 : (C.tr (a β) α (w ≫ f) (le_preimage_map f (le β) hw) h).mulVec ξ =
      (u : K) • fun i => ev w _ hw (η β i) := hu
    have e1 : ((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ = (u'⁻¹ * u) • ((Em.A (a β)).map
        (ev (w ≫ f) _ (le_preimage_map f (le β) hw))).mulVec fun i => ev w _ hw (η β i) := by
      rw [mul_smul, eq_inv_smul_iff, Units.smul_def, Units.smul_def, ← Matrix.smul_mulVec, ← hu',
        ← Matrix.mulVec_mulVec, hu1, Matrix.mulVec_smul]
    have hv' := e1 ▸ span_range_units_smul hv (u'⁻¹ * u)
    exact ⟨hv', e.trans ((pt_eq_pt_iff g hv hv').2 ⟨_, e1⟩)⟩
  · rintro ⟨hv', e'⟩ β hw
    obtain ⟨hv, e⟩ := hη β K w hw g hg
    obtain ⟨u, hu⟩ := (pt_eq_pt_iff g hv hv').1 (e.symm.trans e')
    obtain ⟨u', hu'⟩ := Em.compat (a β) α K (w ≫ f) (le_preimage_map f (le β) hw) h
    obtain ⟨A', hA'⟩ := Em.linv (a β)
    have hl : ∀ v, (A'.map (ev (w ≫ f) _ (le_preimage_map f (le β) hw))).mulVec (((Em.A (a β)).map
        (ev (w ≫ f) _ (le_preimage_map f (le β) hw))).mulVec v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    refine ⟨u' * u, ?_⟩
    show (C.tr (a β) α (w ≫ f) (le_preimage_map f (le β) hw) h).mulVec ξ =
      ((u' * u : Kˣ) : K) • fun i => ev w _ hw (η β i)
    rw [← hl ((C.tr (a β) α (w ≫ f) (le_preimage_map f (le β) hw) h).mulVec ξ), Matrix.mulVec_mulVec ξ, hu',
      Matrix.smul_mulVec, hu, Units.smul_def, smul_smul, Matrix.mulVec_smul, hl, Units.val_mul]

end GlobalTheory.DRFlag.LineOfMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
section
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbMulFlat

open FibreFlat FiniteFibreFlat

set_option backward.isDefEq.respectTransparency false in

theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hY : LocallyOfFinitePresentation g) (h0 : LocallyOfFinitePresentation (f ≫ g))
    (h1 : Flat (f ≫ g)) (h2 : LocallyQuasiFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      inferInstance (MorphismProperty.of_isPullback (sq.paste_vert sq') h0)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) inferInstance (Y.affineCover.f i ≫ g)
      inferInstance (by rw [e]; infer_instance) (by rw [e]; infer_instance)
      (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    exact this (X.affineCover.f i ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h0
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at h2
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hY h0
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Algebra.QuasiFinite A B := h2
  haveI : Algebra.FinitePresentation R A := hY
  haveI : Algebra.FinitePresentation R B := h0
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  refine GlobalTheory.T.flat_of_quasiFinite_of_flat_fibres' R A B fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

theorem flat_and_locallyQuasiFinite_pow :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 →
      Flat ((𝟙 G) ^ q : G ⟶ G).left ∧ LocallyQuasiFinite ((𝟙 G) ^ q : G ⟶ G).left := by
  intro S G _ _ hG n hn
  change Flat (Out.mulA G n).left ∧ LocallyQuasiFinite (Out.mulA G n).left
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have hm := AbLaw.MulN.isMonHom_mulA G n
  have : LocallyOfFiniteType ((Out.mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (Out.mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((Out.mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (Out.mulA G n).left := QuasiCompact.of_comp _ G.hom
  have hq : LocallyQuasiFinite (Out.mulA G n).left :=
    locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      simp only [IntDiv.comp_mulA]
      exact HomExt.finite_torsion_points hG t (Nat.pos_of_ne_zero hn)
  refine ⟨flat_of_flatOver_fields _ G.hom inferInstance (by rw [Over.w]; infer_instance)
    (by rw [Over.w]; infer_instance) hq fun k _ t => ?_, hq⟩
  exact flatOver_of_pullback _ _ (IntDiv.flat_fibre G _ k t)

end GlobalTheory.SemiAbMulFlat
end

