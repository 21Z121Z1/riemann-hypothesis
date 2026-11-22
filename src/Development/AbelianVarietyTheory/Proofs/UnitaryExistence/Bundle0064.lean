import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFirstMinimumLowerBoundNearMax
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPosLowerBoundNearMax
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalCuspSectionsVanishingOffDomain
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.CuspSecFinData

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_finite_determining_set_SS
    {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    ∃ N : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), N.Finite ∧
      ∀ P ∈ X.SS la, (∀ y ∈ N, P y = 0) → ∀ x ∈ X.dom, P x = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨X.dom, Set.Subsingleton.finite ?_, fun P _ hP x hx => hP x hx⟩
    intro a _ b _
    funext τ i
    exact i.elim0
  obtain ⟨ε, hε, hla1⟩ := _root_.GlobalTheory.exists_lower_bound_half_max_norm E r X la hr
  obtain ⟨K, hK, hKdom, hKmove⟩ := _root_.GlobalTheory.FlagMahler.mahler_compactness r X ε hε
  obtain ⟨β, hβc, hβ⟩ := _root_.GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt r X
  have hcont : ContinuousOn (fun x => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) X.dom := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    fun_prop
  set K' := (fun x => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) '' K with hK'
  have hK'c : IsCompact K' := hK.image_of_continuousOn (hcont.mono hKdom)
  have hK'dom : K' ⊆ X.dom := by
    rintro _ ⟨x, hx, rfl⟩
    exact _root_.ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X (hKdom hx) (hβ x (hKdom hx)).1
  set δ : ℝ := 1 / (1000 * (r : ℝ) ^ 2 * (1 + ∑ τ, ∑ i, |(la τ i : ℝ)|)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    apply one_div_pos.mpr
    have : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
    have : (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by positivity
    positivity
  obtain ⟨N, hNK, hNnear⟩ := _root_.GlobalTheory.CuspNet.exists_finset_rmul_near_one X hK'c hK'dom hδpos
  refine ⟨(N : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), N.finite_toSet, ?_⟩
  intro P hP hPN
  have hP' := hP
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.SS at hP'
  obtain ⟨⟨hSec, C, hC⟩, -⟩ := hP'
  have hpz : ∀ x ∈ X.dom, X.pnorm la P x = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨x0, hx0, hx0ne⟩ := hne
    have hx0pos : 0 < X.pnorm la P x0 := lt_of_le_of_ne (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_nonneg X la P x0) (Ne.symm hx0ne)
    set T : Set ℝ := (fun x => X.pnorm la P x) '' X.dom with hT
    have hTbdd : BddAbove T := ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
    have hTne : T.Nonempty := ⟨_, x0, hx0, rfl⟩
    set S := sSup T with hS
    have hle : ∀ x ∈ X.dom, X.pnorm la P x ≤ S := fun x hx => le_csSup hTbdd ⟨x, hx, rfl⟩
    have hSpos : 0 < S := lt_of_lt_of_le hx0pos (hle x0 hx0)
    obtain ⟨_, ⟨z, hz, rfl⟩, hzS⟩ := exists_lt_of_lt_csSup hTne (half_lt_self hSpos)
    have hzpos : 0 < X.pnorm la P z := lt_trans (half_pos hSpos) hzS
    have hz2 : ∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z := fun x hx => by
      linarith [hle x hx]
    have hεz : ε ≤ X.la1 z := hla1 P hP z hz hz2 hzpos
    obtain ⟨γ, hγ, b, hb, hyK⟩ := hKmove z hz hεz
    set y := _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul z b) with hy
    have hydom : y ∈ X.dom := hKdom hyK
    have hpy : X.pnorm la P y = X.pnorm la P z :=
      _root_.GlobalTheory.NormFactor.pnormInv_holds r X la P hSec γ hγ z hz b hb
    obtain ⟨hβy, hnorm⟩ := hβ y hydom
    set y' := _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y (β y) with hy'
    have hpy' : X.pnorm la P y' = X.pnorm la P y := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul X la P hSec.2.1 y hydom (β y) hβy
    have hy'K : y' ∈ K' := ⟨y, hyK, rfl⟩
    obtain ⟨A, hA, hAN⟩ := hNnear y' hy'K
    have hnorm' := hnorm
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hnorm'
    have hhalf : S / 2 ≤ X.pnorm la P y' := by rw [hpy', hpy]; exact hzS.le
    obtain ⟨-, hquarter⟩ := _root_.GlobalTheory.pnorm_near_half_max X la P hSec.1 S hle y' hnorm' hhalf A hA
    have hzero : X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y' A) = 0 := by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, hPN _ (Finset.mem_coe.mpr hAN)]
      simp
    linarith
  intro x hx
  have h := hpz x hx
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq] at h
  have hn := _root_.ReciprocityTheory.ChartRestriction.G.FD.flowTermNormDecay.nfac_pos X la hx
  rcases mul_eq_zero.mp h with h | h
  · exact norm_eq_zero.mp h
  · exact absurd h hn.ne'

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] (X : Comp → _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : ∀ k, _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (W : Submodule ℂ (_root_.Formalism.L2.PjFree.FDSec X)), W ≤ _root_.Formalism.L2.PjFree.holSub X la →
    (∀ P ∈ W, ∀ k, ∀ x ∉ (X k).dom, P k x = 0) → FiniteDimensional ℂ W := by
  intro E _ _ _ r Comp _ X la W hW hoff
  choose N hNfin hN using fun k => exists_finite_determining_set_SS (X k) (la k)
  haveI : ∀ k, Fintype (N k) := fun k => (hNfin k).fintype
  let L : W →ₗ[ℂ] ((k : Comp) → N k → ℂ) :=
    { toFun := fun P k y => P.1 k y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    apply Subtype.ext
    funext k x
    show P.1 k x = 0
    have hcusp := _root_.GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub X la (hW P.2) k
    by_cases hx : x ∈ (X k).dom
    · exact hN k _ hcusp (fun y hy => congrFun (congrFun hP k) ⟨y, hy⟩) x hx
    · exact hoff P.1 P.2 k x hx
  exact Module.Finite.of_injective L hinj

end GlobalTheory.CuspSecFinData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.IntLie

section Pull

variable {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
  {φ : G'.left ⟶ G.left}

theorem one_push₀ (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let e0 : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    show ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have h1 : (e0 * e0).left = ((1 : T ⟶ G') * 1).left ≫ φ := h.2 T 1 1 e0 e0 rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : e0 * e0 = e0 := Over.OverMorphism.ext h1
  have h3 : e0 = 1 := mul_eq_left.1 h2
  rw [← h3]
  rfl

theorem one_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) : (1 : T' ⟶ G').left ≫ φ = g ≫ (1 : T ⟶ G).left := by
  let δ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g hg
  rw [← one_push₀ h T', ← MonObj.comp_one δ]
  rfl

theorem mul_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) (a b : T' ⟶ G') (a₀ b₀ : T ⟶ G) (ha : a.left ≫ φ = g ≫ a₀.left)
    (hb : b.left ≫ φ = g ≫ b₀.left) : (a * b).left ≫ φ = g ≫ (a₀ * b₀).left := by
  let δ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g hg
  rw [← h.2 T' a b (δ ≫ a₀) (δ ≫ b₀) ha.symm hb.symm, ← MonObj.comp_mul]
  rfl

theorem prod_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) {m : ℕ} (a : Fin m → (T' ⟶ G')) (a₀ : Fin m → (T ⟶ G))
    (ha : ∀ j, (a j).left ≫ φ = g ≫ (a₀ j).left) :
    ((List.ofFn a).prod).left ≫ φ = g ≫ ((List.ofFn a₀).prod).left := by
  induction m with
  | zero => simpa using one_push h T' T g hg
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact mul_push h T' T g hg _ _ _ _ (ha 0) (ih _ _ fun j => ha j.succ)

theorem isIso_of_pull {G₁ G₂ : Over S₀} [GrpObj G₁] [GrpObj G₂] {ψ : G₁.left ⟶ G₂.left}
    (h : IsGrpPullback G₁ G₂ (𝟙 _) ψ) : IsIso ψ :=
  h.1.isIso_fst_of_isIso

end Pull

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_frac_cancel {V K A : Type} [CommRing V] [CommRing K] [Algebra V K] [IsFractionRing V K] [CommRing A]
    (g h : Sp A ⟶ Sp K) (e : g ≫ spMap (algebraMap V K) = h ≫ spMap (algebraMap V K)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h] at e ⊢
  simp only [spMap, ← Spec.map_comp] at e
  have e1 := Spec.map_injective e
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (nonZeroDivisors V)
  exact congrArg CommRingCat.Hom.hom e1

theorem dualMap_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (dualMap f).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp f := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    (dualMap f).comp (epsMul a) = (epsMul (f a)).comp (dualMap f) := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, epsMul, _root_.mul_comm]

theorem epsMul_alg {A : Type} [CommRing A] (a : A) :
    (epsMul a).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem comb_generic {V K : Type} [CommRing V] [CommRing K] [Algebra V K] [IsFractionRing V K]
    {x : Sp K ⟶ Xo.X} {G : SAB H (Sp V)} {t : SAB H (Sp K)} (m₁ : SABMap t Xo.univ.t x)
    (m₂ : SABMap t G (spMap (algebraMap V K))) {m : ℕ} (ub : Fin m → (epsOver V V ⟶ G.G))
    (u' : Fin m → (Sp (DualNumber K) ⟶ t.G.left))
    (hu : ∀ j, u' j ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ (ub j).left)
    (w : epsOver V V ⟶ G.G) (w' : Sp (DualNumber K) ⟶ t.G.left)
    (hw : w' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ w.left) (a : Fin m → V) (ha : IsComb ub a w) :
    IsCombAt x (fun j => u' j ≫ m₁.φ) (fun j => algebraMap V K (a j)) (w' ≫ m₁.φ) := by
  obtain ⟨U, hU, hwU⟩ := ha
  have hδ : spMap (dualMap (algebraMap V K)) ≫
      spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)) =
      spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) := by
    rw [spMap_comp₂, spMap_comp₂]
    show spMap ((dualMap (algebraMap V K)).comp (algebraMap V (DualNumber V))) = _
    rw [dualMap_alg]
  have hov : ∀ (z : epsOver V V ⟶ G.G) (z' : Sp (DualNumber K) ⟶ t.G.left),
      z' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ z.left →
      z' ≫ t.G.hom = spMap (algebraMap K (DualNumber K)) := by
    intro z z' hz
    apply spMap_frac_cancel (V := V)
    rw [Category.assoc, ← m₂.cart.1.w, ← Category.assoc, hz, Category.assoc, Over.w z]
    exact hδ
  let T' : Over (Sp K) := Over.mk (spMap (algebraMap K (DualNumber K)))
  let Y : Fin m → (T' ⟶ t.G) := fun j => Over.homMk (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) (by
    show (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) ≫ t.G.hom = spMap (algebraMap K (DualNumber K))
    rw [Category.assoc, hov _ _ (hu j), spMap_comp₂, epsMul_alg])
  have hB := prod_push m₂.cart T' (epsOver V V) (spMap (dualMap (algebraMap V K))) hδ Y U (fun j => by
    show (spMap (epsMul (algebraMap V K (a j))) ≫ u' j) ≫ m₂.φ = _
    rw [Category.assoc, hu j, hU j, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂,
      dualMap_epsMul])
  have hY : ((List.ofFn Y).prod).left = w' := by
    apply m₂.cart.1.hom_ext
    · rw [hB, ← hwU]
      exact hw.symm
    · rw [hov _ _ hw]
      exact Over.w _
  let Z : Fin m → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk ((Y j).left ≫ m₁.φ) (by
    show ((Y j).left ≫ m₁.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x
    rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w (Y j)]
    rfl)
  have hA := prod_push m₁.cart T' (tEps x) (𝟙 _) (Category.id_comp _) Y Z (fun j => (Category.id_comp _).symm)
  refine ⟨Z, fun j => Category.assoc _ _ _, ?_⟩
  rw [← hY]
  exact ((Category.id_comp _).symm.trans hA.symm)

theorem tan_eig_iff {V K : Type} [CommRing V] [Field K] [Algebra V K] (io : c.F →+* K) {G G₂ : SAB H (Sp V)}
    (n : SABMap G G₂ (𝟙 _)) (τ : E →+* ℂ) (w : epsOver V V ⟶ G.G) (w₂ : epsOver V V ⟶ G₂.G)
    (h : w.left ≫ n.φ = w₂.left) :
    (IsTan w ↔ IsTan w₂) ∧ (IsEigV c io G τ w ↔ IsEigV c io G₂ τ w₂) := by
  have := isIso_of_pull n.cart
  constructor
  · have h1 := one_push n.cart (ptOver V V) (ptOver V V) (𝟙 _) (by simp)
    rw [Category.id_comp] at h1
    unfold IsTan
    rw [← h, ← h1, ← Category.assoc]
    exact (cancel_mono n.cm.F).symm
  · unfold IsEigV
    refine forall_congr' fun a => forall_congr' fun z => forall_congr' fun _ => ?_
    rw [Over.comp_left, Over.comp_left, ← h, Category.assoc, ← n.act a, ← Category.assoc, ← Category.assoc]
    exact (cancel_mono n.cm.F).symm

theorem mul_eq_one_of_comb {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (u u₂ : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ i, IsTanAt x (u i))
    (huniq : ∀ i, ∃! a : Fin m → S, IsCombAt x u a (u i)) (A B : Matrix (Fin m) (Fin m) S)
    (hA : ∀ i, IsCombAt x u (A i) (u₂ i)) (hB : ∀ i, IsCombAt x u₂ (B i) (u i)) : B * A = 1 := by
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x
  choose b hb using fun i => (htan _).1 (hu i)
  obtain rfl : u = fun i => v (b i) := funext fun i => (hb i).symm
  obtain rfl : u₂ = fun i => v (∑ j, A i j • b j) := funext fun i => (hcomb _ b _ _).1 (hA i)
  ext i k
  have h1 := (hcomb _ (fun i => ∑ j, A i j • b j) _ _).1 (hB i)
  have h2 : IsCombAt x (fun i => v (b i)) ((B * A) i) (v (b i)) := by
    refine (hcomb _ b _ _).2 (h1.trans (congrArg v ?_))
    simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have h3 : IsCombAt x (fun i => v (b i)) ((1 : Matrix (Fin m) (Fin m) S) i) (v (b i)) := by
    refine (hcomb _ b _ _).2 (congrArg v ?_)
    simp [Matrix.one_apply]
  exact congrFun ((huniq i).unique h2 h3) k

theorem integral_frames_differ_by_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)) (ub₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G)), ((∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t.G.left, u' ≫ m₁.φ = y.u τ i ∧ u' ≫ m₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) → ((∀ τ i, IsTan (ub₂ τ i)) ∧ (∀ τ i, IsEigV c io G₂ τ (ub₂ τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G₂.G), IsTan w → IsEigV c io G₂ τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub₂ τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t₂.G.left, u' ≫ n₁.φ = y'.u τ i ∧ u' ≫ n₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub₂ τ i).left) → ∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧ ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i) := by
  intro E _ _ _ H Dw l Xo c T io
  let _ := io.toAlgebra
  intro y y' G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn ub ub₂ ⟨ht, he, hb, hl⟩ ⟨ht₂, he₂, hb₂, hl₂⟩ τ
  have := isIso_of_pull n.cart
  have := isIso_of_pull k.cart
  have hnw : n.φ ≫ G₂.G.hom = G.G.hom := n.cart.1.w.trans (Category.comp_id _)
  choose u' hu1 hu2 using hl τ
  choose u₂ hv1 hv2 using hl₂ τ
  let w : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G) := fun i => Over.homMk ((ub₂ τ i).left ≫ inv n.φ) (by
    rw [← hnw, Category.assoc, IsIso.inv_hom_id_assoc]
    exact Over.w _)
  have hw : ∀ i, (w i).left ≫ n.φ = (ub₂ τ i).left := fun i => by
    show ((ub₂ τ i).left ≫ inv n.φ) ≫ n.φ = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let w₂ : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G) := fun i => Over.homMk ((ub τ i).left ≫ n.φ) (by
    rw [Category.assoc, hnw]
    exact Over.w _)
  have hw₂ : ∀ i, (ub τ i).left ≫ n.φ = (w₂ i).left := fun i => rfl
  choose A hA using fun i => (hb τ (w i) ((tan_eig_iff io n τ _ _ (hw i)).1.2 (ht₂ τ i))
    ((tan_eig_iff io n τ _ _ (hw i)).2.2 (he₂ τ i))).exists
  choose B hB using fun i => (hb₂ τ (w₂ i) ((tan_eig_iff io n τ _ _ (hw₂ i)).1.1 (ht τ i))
    ((tan_eig_iff io n τ _ _ (hw₂ i)).2.1 (he τ i))).exists
  have hA' : ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i) := by
    intro i
    have h := comb_generic m₁ m₂ (ub τ) u' hu2 (w i) (u₂ i ≫ inv k.φ) (by
      rw [← cancel_mono n.φ, Category.assoc, Category.assoc, hn, IsIso.inv_hom_id_assoc, hv2, Category.assoc,
        hw]) (A i) (hA i)
    rw [funext hu1, ← hk, Category.assoc, IsIso.inv_hom_id_assoc, hv1] at h
    exact h
  have hB' : ∀ i, IsCombAt y.x (y'.u τ) (fun j => algebraMap T.V T.Fr (B i j)) (y.u τ i) := by
    intro i
    have h := comb_generic n₁ n₂ (ub₂ τ) u₂ hv2 (w₂ i) (u' i ≫ k.φ) (by
      rw [Category.assoc, ← hn, ← Category.assoc, hu2, Category.assoc, hw₂]) (B i) (hB i)
    rw [funext hv1, Category.assoc, hk, hu1, hx] at h
    exact h
  refine ⟨Matrix.of A, ?_, hA'⟩
  have h1 := mul_eq_one_of_comb y.x (y.u τ) (y'.u τ) (y.tan τ)
    (fun i => y.basis τ _ (y.tan τ i) (y.eig τ i))
    ((Matrix.of A).map (algebraMap T.V T.Fr)) ((Matrix.of B).map (algebraMap T.V T.Fr)) hA' hB'
  have h2 : Matrix.of B * Matrix.of A = 1 := by
    apply Matrix.map_injective (IsFractionRing.injective T.V T.Fr)
    show (Matrix.of B * Matrix.of A).map (algebraMap T.V T.Fr) = (1 : Matrix _ _ T.V).map (algebraMap T.V T.Fr)
    rw [Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_left_inverse h2

end GlobalTheory.IntLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NatCastMemMaximalIdealOfOverLa
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

open IsDedekindDomain

theorem exists_prime_mem_place {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  have : la.asIdeal.IsMaximal := la.isMaximal
  let _ : Field (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.field _
  refine ⟨ringChar (𝓞 K ⧸ la.asIdeal), CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem natCast_mem_maximalIdeal_of_overLa {K : Type} [Field K] [NumberField K]
    {la : HeightOneSpectrum (𝓞 K)} {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] {io : K →+* K'} {e : ℕ} (ho : OverLa la V io e)
    {n : ℕ} (hn : n ≠ 0) (hmem : ((n : ℕ) : 𝓞 K) ∈ la.asIdeal) :
    (n : V) ∈ IsLocalRing.maximalIdeal V := by
  by_contra hV
  have hK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn
  have h1 : valV V ((n : ℕ) : K') = 1 := by
    have h : ((n : ℕ) : K') = algebraMap V K' (n : V) := (map_natCast _ n).symm
    rw [valV, h]
    apply le_antisymm (HeightOneSpectrum.valuation_le_one _ _)
    rw [← not_lt, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hV
  have h2 : la.valuation K ((n : ℕ) : K) < 1 := by
    have h : ((n : ℕ) : K) = algebraMap (𝓞 K) K (n : 𝓞 K) := (map_natCast _ n).symm
    rw [h, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hmem
  have h3 : WithZero.log (la.valuation K ((n : ℕ) : K)) < 0 := by
    have := (WithZero.log_lt_log ((la.valuation K).ne_zero_iff.2 hK) one_ne_zero).2 h2
    simpa using this
  have h4 := ho.2 ((n : ℕ) : K)
  rw [map_natCast, vV, h1, vLa, WithZero.log_one] at h4
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  nlinarith [mul_pos he (neg_pos.2 h3)]

theorem modelAtSt_of_good : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ la, Formalism.L2.Pj.ModelAtSt Xo c la := by
  intro hP hN E _ _ _ H Dw l Xo c hpq hg la
  exact Formalism.L2.Pj.modelAtSt_of (Formalism.L2.Pj.partIAt_of hP hN Xo c hpq) hg la

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RdUMulApply
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory

theorem rdU_mul_apply : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (f f' : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r), rdU U (f * f') k x = rdU U f k x * rdU U f' k x := by
  intro E _ _ _ H Dw l Xo c σ r U f f' k x
  classical
  by_cases h : x ∈ (U.X k).dom
  · have e := evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f f' (U.un k ⟨x, h⟩)
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]
    exact e
  · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h, mul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianSchemeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_values_complex_fibre_abelianScheme : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx y)), (∀ (a : ℂ) i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (scal y a i * s.f i) = a * valAt' pt ((PPx y).U i) (s.f i)) ∧ (SecGen y s ↔ ∃ (i : (PPx y).ι) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ ∧ valAt' pt ((PPx y).U i) (s.f i) ≠ 0) ∧ ∀ s' : LB.Sec (PPx y), (∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s'.f i) = valAt' pt ((PPx y).U i) (s.f i)) → ∀ i, s'.f i = s.f i := by
  first | exact @GlobalTheory.sec_values_complex_fibre | exact GlobalTheory.sec_values_complex_fibre | (intros; apply GlobalTheory.sec_values_complex_fibre <;> assumption)
end

