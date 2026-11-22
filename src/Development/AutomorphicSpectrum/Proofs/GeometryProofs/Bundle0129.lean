import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0123
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionPotentialPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.Twist

section Holo

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem continuousAt_holo (A : FinHolAtlas e X) {W : Set X} {g : X → ℂ} (hg : A.HoloOn W g) {x : X}
    (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) :=
    (hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩).continuousAt
  have h3 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm) h1 ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

theorem holoOn_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h) {U : Set X}
    {g : X → ℂ} (hg : A.HoloOn U g) : B.HoloOn (h ⁻¹' U) (fun y => g (h y)) := by
  rintro j y ⟨hy, hyU⟩
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm y))
  have a1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y := hh.2 j k y ⟨hy, hk⟩
  have a2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart j).symm) y) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      simpa [Function.comp, (A.chart k).left_inv hk] using hyU⟩
  refine (a2.comp a1).congr ?_
  filter_upwards [((B.chart j).isOpen_inter_preimage_symm
    ((A.chart k).open_source.preimage hh.1)).mem_nhds ⟨hy, hk⟩] with y' hy'
  simp [Function.comp, (A.chart k).left_inv hy'.2]

theorem exists_log (A : FinHolAtlas e X) {W : Set X} (hW : IsOpen W) {c : X → ℂ} (hc : A.HoloOn W c) {x : X}
    (hx : x ∈ W) (h0 : c x ≠ 0) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ ∃ L : X → ℂ, A.HoloOn V L ∧
      ∀ y ∈ V, c y ≠ 0 ∧ (L y).re = Real.log ‖c y‖ := by
  have hcont : ContinuousOn (fun y => c y / c x) W := fun y hy =>
    ((continuousAt_holo A hc hy).div_const _).continuousWithinAt
  have hV : IsOpen (W ∩ (fun y => c y / c x) ⁻¹' Complex.slitPlane) :=
    hcont.isOpen_inter_preimage hW Complex.isOpen_slitPlane
  refine ⟨_, hV, ⟨hx, ?_⟩, Set.inter_subset_left, fun y => Complex.log (c y / c x) + (Real.log ‖c x‖ : ℂ), ?_, ?_⟩
  · simp [div_self h0]
  · rintro j z ⟨hz, hzW, hzs⟩
    have a1 : AnalyticAt ℂ (c ∘ (A.chart j).symm) z := hc j z ⟨hz, hzW⟩
    have a2 : AnalyticAt ℂ (fun z => (c ∘ (A.chart j).symm) z / c x) z := a1.div analyticAt_const h0
    exact (a2.clog hzs).add analyticAt_const
  · rintro y ⟨-, hy⟩
    have hy' : c y / c x ≠ 0 := Complex.slitPlane_ne_zero hy
    have hcy : c y ≠ 0 := fun e => hy' (by simp [e])
    refine ⟨hcy, ?_⟩
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hcy) (norm_ne_zero_iff.2 h0)]
    ring

end Holo

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type}
  [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k}
  {P₀ Jd₀ : Ideal (MRing J₀)} {P Jd : Ideal (MRing J)} {D : ℕ}

theorem orbit_key (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (hv : IsBlockMap κ v) (h : R.X → R₀.X)
    (ho : ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) {x y : R.X} (hy : y ∈ R.U x)
    (hy₀ : h y ∈ R₀.U (h x)) :
    ∃ c : K₀ → ℂ, (∀ k, c k ≠ 0) ∧ ∀ p, R.lift x y (v p) = c p.1 * R₀.lift (h x) (h y) p := by
  obtain ⟨c₁, h₁, e₁⟩ := R.compat x y y ⟨hy, R.mem_U y⟩
  obtain ⟨c₂, h₂, e₂⟩ := ho y
  obtain ⟨c₃, h₃, e₃⟩ := R₀.compat (h x) (h y) (h y) ⟨hy₀, R₀.mem_U _⟩
  refine ⟨fun k => c₁ (κ k) / (c₃ k * c₂ k), fun k => div_ne_zero (h₁ _) (mul_ne_zero (h₃ k) (h₂ k)), fun p => ?_⟩
  have a₁ := congrFun e₁ (v p)
  have a₂ := congrFun e₂ p
  have a₃ := congrFun e₃ p
  simp only at a₁ a₂ a₃
  have n₂ := h₂ p.1
  have n₃ := h₃ p.1
  rw [a₃, a₂, a₁, hv.2.2.1 p]
  field_simp

theorem exists_coeff_log (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (hv : IsBlockMap κ v) (h : R.X → R₀.X)
    (hh : HoloMap R.A R₀.A h)
    (ho : ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) (x : R.X) (k : K₀) :
    ∃ V : Set R.X, IsOpen V ∧ x ∈ V ∧ V ⊆ R.U x ∩ h ⁻¹' R₀.U (h x) ∧ ∃ L : R.X → ℂ, R.A.HoloOn V L ∧
      ∀ y ∈ V, ∀ c : K₀ → ℂ, (∀ k, c k ≠ 0) →
        (∀ p, R.lift x y (v p) = c p.1 * R₀.lift (h x) (h y) p) → (L y).re = Real.log ‖c k‖ := by
  have oW : IsOpen (R.U x ∩ h ⁻¹' R₀.U (h x)) := (R.isOpen_U x).inter ((R₀.isOpen_U _).preimage hh.1)
  have mW : x ∈ R.U x ∩ h ⁻¹' R₀.U (h x) := ⟨R.mem_U x, R₀.mem_U _⟩
  obtain ⟨i, hi⟩ := (R₀.mem (h x) (h x) (R₀.mem_U _)).1 k
  obtain ⟨cx, hcx, ecx⟩ := orbit_key R₀ R hv h ho (R.mem_U x) (R₀.mem_U (h x))
  have hn : R.A.HoloOn (R.U x ∩ h ⁻¹' R₀.U (h x)) (fun y => R.lift x y (v ⟨k, i⟩)) := fun j z hz =>
    R.holo x (v ⟨k, i⟩) j z ⟨hz.1, hz.2.1⟩
  have hd : R.A.HoloOn (R.U x ∩ h ⁻¹' R₀.U (h x)) (fun y => R₀.lift (h x) (h y) ⟨k, i⟩) := fun j z hz =>
    holoOn_comp hh (R₀.holo (h x) ⟨k, i⟩) j z ⟨hz.1, hz.2.2⟩
  have hnx : R.lift x x (v ⟨k, i⟩) ≠ 0 := by
    rw [ecx ⟨k, i⟩]
    exact mul_ne_zero (hcx k) hi
  obtain ⟨Vn, oVn, mVn, sVn, Ln, hLn, eLn⟩ := exists_log R.A oW hn mW hnx
  obtain ⟨Vd, oVd, mVd, -, Ld, hLd, eLd⟩ := exists_log R.A oW hd mW hi
  refine ⟨Vn ∩ Vd, oVn.inter oVd, ⟨mVn, mVd⟩, Set.inter_subset_left.trans sVn, fun y => Ln y - Ld y, ?_, ?_⟩
  · rintro j z ⟨hz, hzn, hzd⟩
    exact (hLn j z ⟨hz, hzn⟩).sub (hLd j z ⟨hz, hzd⟩)
  · rintro y ⟨hyn, hyd⟩ c hc ec
    obtain ⟨-, e1⟩ := eLn y hyn
    obtain ⟨d0, e2⟩ := eLd y hyd
    simp only [Complex.sub_re, e1, e2]
    rw [ec ⟨k, i⟩, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 d0)]
    ring

theorem samePot_twist : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (κ : K₀ → K) (v : (Σ k, J₀ k) → Σ k, J k) (P₀ Jd₀ : Ideal (MRing J₀)) (P Jd : Ideal (MRing J)) (D : ℕ) (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (X : Type) [TopologicalSpace X] (B : FinHolAtlas D X) (Θ : LocPot X) (A₀ : HermLine J₀) (T : HermLine J) (π : R₀.X → X) (hπ : HoloMap R₀.A B π) (h : R.X → R₀.X) (hv : IsBlockMap κ v) (hc : Continuous (π ∘ h)), HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) → SamePot R₀.A Set.univ (potOf R₀ A₀) (Θ.pullback π hπ.1) → IsFlatOn R T → SamePot R.A Set.univ (potOf R ((pullHerm hv A₀).tensor T)) (Θ.pullback (π ∘ h) hc) := by
  intro K₀ K _ _ J₀ J _ _ κ v P₀ Jd₀ P Jd D R₀ R X _ B Θ A₀ T π hπ h hv hc hh ho h0 hF x _
  obtain ⟨V₀, oV₀, mV₀, G₀, hG₀, e₀⟩ := h0 (h x) trivial
  obtain ⟨V₁, oV₁, mV₁, G₁, hG₁, e₁⟩ := hF x trivial
  choose Vk oVk mVk sVk L hL eL using exists_coeff_log R₀ R hv h hh ho x
  refine ⟨(⋂ k, Vk k) ∩ ((h ⁻¹' V₀ ∩ V₁) ∩ (R.U x ∩ h ⁻¹' R₀.U (h x))),
    (isOpen_iInter_of_finite oVk).inter (((oV₀.preimage hh.1).inter oV₁).inter
      ((R.isOpen_U x).inter ((R₀.isOpen_U _).preimage hh.1))),
    ⟨Set.mem_iInter.2 mVk, ⟨mV₀, mV₁⟩, R.mem_U x, R₀.mem_U _⟩,
    fun y => G₀ (h y) + G₁ y + ∑ k, ((A₀.a k : ℝ) : ℂ) * L k y, ?_, ?_⟩
  · rintro j z ⟨hz, hzk, ⟨hz₀, hz₁⟩, -⟩
    have t0 : AnalyticAt ℂ (fun z => G₀ (h ((R.A.chart j).symm z))) z := holoOn_comp hh hG₀ j z ⟨hz, hz₀⟩
    have t1 : AnalyticAt ℂ (fun z => G₁ ((R.A.chart j).symm z)) z := hG₁ j z ⟨hz, hz₁⟩
    have t2 : ∀ k ∈ (Finset.univ : Finset K₀),
        AnalyticAt ℂ (fun z => ((A₀.a k : ℝ) : ℂ) * L k ((R.A.chart j).symm z)) z := fun k _ =>
      analyticAt_const.mul (hL k j z ⟨hz, Set.mem_iInter.1 hzk k⟩)
    exact (t0.add t1).add (Finset.analyticAt_fun_sum _ t2)
  · rintro y ⟨hyk, ⟨hy₀, hy₁⟩, hyU, hyU₀⟩
    obtain ⟨c, hc0, ec⟩ := orbit_key R₀ R hv h ho hyU hyU₀
    have E0 : Real.log (A₀.h (R₀.lift (h x) (h y))) - Θ.φ (π (h x)) (π (h y)) = (G₀ (h y)).re := e₀ (h y) hy₀
    have E1 : Real.log (T.h (R.lift x y)) - 0 = (G₁ y).re := e₁ y hy₁
    have E2 : (fun p => R.lift x y (v p)) = fun p => c p.1 * R₀.lift (h x) (h y) p := funext ec
    show Real.log (((pullHerm hv A₀).tensor T).h (R.lift x y)) - Θ.φ (π (h x)) (π (h y)) = _
    rw [log_tensor_pull hv A₀ T (R.mem x y hyU).1, E2, log_h_smul A₀ hc0 (R₀.mem _ _ hyU₀).1]
    simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, ← E0, ← E1,
      fun k => eL k y (Set.mem_iInter.1 hyk k) c hc0 ec]
    ring

end GlobalTheory.CompanionTheory.Ar.Chg.Twist
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairLatticeSumComap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeSum

section LinearAlgebra

open Submodule

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]

theorem range_append {α : Type} {r s : ℕ} (f : Fin r → α) (g : Fin s → α) :
    Set.range (Fin.append f g) = Set.range f ∪ Set.range g := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · exact Or.inl ⟨i, by simp⟩
    · exact Or.inr ⟨i, by simp⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd s i, by simp⟩
    · exact ⟨Fin.natAdd r i, by simp⟩

theorem linearIndependent_append {r s : ℕ} {f : Fin r → V} {g : Fin s → V} (hf : LinearIndependent Ω f)
    (hg : LinearIndependent Ω g) (hd : Disjoint (span Ω (Set.range f)) (span Ω (Set.range g))) :
    LinearIndependent Ω (Fin.append f g) := by
  have h := hf.sum_type hg hd
  have e : Fin.append f g = Sum.elim f g ∘ finSumFinEquiv.symm := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp
  rw [e]
  exact h.comp _ finSumFinEquiv.symm.injective

theorem span_lift_eq_top {W : Submodule Ω V} {n : ℕ} {v : Fin n → V} {c : Fin n → W} (hc : ∀ k, (c k : V) = v k)
    (hv : span Ω (Set.range v) = W) : span Ω (Set.range c) = ⊤ := by
  apply Submodule.map_injective_of_injective W.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  have e : (W.subtype ∘ c) = v := funext hc
  rw [show (⇑W.subtype ∘ c) = v from e, hv]

theorem comap_sup_span (A : Subring Ω) {W : Submodule Ω V} {r s : ℕ} {f : Fin r → V} {g : Fin s → V}
    {c : Fin (r + s) → W} (hc : ∀ k, (c k : V) = Fin.append f g k) :
    (span A (Set.range f) ⊔ span A (Set.range g)).comap (W.subtype.restrictScalars A) =
      span A (Set.range c) := by
  have hinj : Function.Injective (W.subtype.restrictScalars A) := W.injective_subtype
  have e : span A (Set.range f) ⊔ span A (Set.range g) =
      (span A (Set.range c)).map (W.subtype.restrictScalars A) := by
    rw [Submodule.map_span, ← Set.range_comp, ← Submodule.span_union, ← range_append]
    congr 2
    exact funext fun k => (hc k).symm
  rw [e, Submodule.comap_map_eq_of_injective hinj]

end LinearAlgebra

end GlobalTheory.CompanionTheory.Ar.HodgeSum

theorem GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H), a ≠ b → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsVB (labelRk D a + labelRk D b) ⊤ := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 a b hab
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, -, -, -, -, hind, -⟩ :=
    GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω K J y 𝔐 hβ
  have hdisj : Disjoint (𝔐.Vgen a) (𝔐.Vgen b) := hind.pairwiseDisjoint hab
  intro p _
  obtain ⟨Ua, hpa, f, hfs, hff⟩ := 𝔐.vb a p (Set.mem_univ _)
  obtain ⟨Ub, hpb, g, hgs, hgf⟩ := 𝔐.vb b p (Set.mem_univ _)
  have hfs' : Submodule.span Ω (Set.range f) = 𝔐.Vgen a := hfs
  have hgs' : Submodule.span Ω (Set.range g) = 𝔐.Vgen b := hgs
  have hspan : Submodule.span Ω (Set.range (Fin.append f g)) = 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
    rw [HodgeSum.range_append, Submodule.span_union, hfs', hgs']
  have hmem : ∀ k, Fin.append f g k ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := fun k => by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self k)
  have hli : LinearIndependent Ω (Fin.append f g) :=
    HodgeSum.linearIndependent_append (hff p (Set.mem_univ _) hpa).1 (hgf p (Set.mem_univ _) hpb).1
      (by rw [hfs', hgs']; exact hdisj)
  refine ⟨Ua ⊓ Ub, ⟨hpa, hpb⟩, fun k => ⟨Fin.append f g k, hmem k⟩,
    HodgeSum.span_lift_eq_top (fun _ => rfl) hspan, fun q _ hq => ⟨?_, ?_⟩⟩
  · exact LinearIndependent.of_comp (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype hli
  · have h1 : 𝔐.V a q = Submodule.span (regAt 𝔐.ξ q) (Set.range f) := (hff q (Set.mem_univ _) hq.1).2
    have h2 : 𝔐.V b q = Submodule.span (regAt 𝔐.ξ q) (Set.range g) := (hgf q (Set.mem_univ _) hq.2).2
    show (𝔐.V a q ⊔ 𝔐.V b q).comap ((𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype.restrictScalars (regAt 𝔐.ξ q)) = _
    rw [h1, h2]
    exact HodgeSum.comap_sup_span (regAt 𝔐.ξ q) fun _ => rfl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RingOfIntegersHomInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem ringOfIntegers_hom_injective {F : Type} [Field F] [NumberField F] {R : Type} [Field R] [CharZero R]
    (a : 𝓞 F →+* R) : Function.Injective a := by
  have hI : (RingHom.ker a).comap (algebraMap ℤ (𝓞 F)) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have h0 : ((n : ℤ) : R) = 0 := by
      have h1 : a (algebraMap ℤ (𝓞 F) n) = 0 := hn
      simpa using h1
    have h2 : n = 0 := by exact_mod_cast h0
    simp [h2]
  exact (RingHom.injective_iff_ker_eq_bot a).2 (Ideal.eq_bot_of_comap_eq_bot hI)

theorem exists_ringHom_extend {F : Type} [Field F] [NumberField F] {R : Type} [Field R] [CharZero R]
    (a : 𝓞 F →+* R) : ∃ κ : F →+* R, κ.comp (algebraMap (𝓞 F) F) = a :=
  ⟨IsFractionRing.lift (ringOfIntegers_hom_injective a),
    RingHom.ext fun x => IsFractionRing.lift_algebraMap (ringOfIntegers_hom_injective a) x⟩

theorem exists_isOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 𝔐.Interior z → ∃ (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hz
  have := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let a : 𝓞 c.F →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
  have ha : z ≫ 𝔐.f ≫ Y.s = spMap a := by
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨κ, hκ⟩ := exists_ringHom_extend a
  have hc : (z ≫ 𝔐.f) ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, ha, ← hκ, Chg.spMap_comp']
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift (z ≫ 𝔐.f) (spMap κ) hc
  have hw₁ : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
  have := Y.jQ_open
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨u, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, hw₁, Scheme.Hom.comp_apply]
    have hu : u = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hu
    exact (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 _).2 hz
  let x : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w hr
  have hx : x ≫ Y.jQ = w := IsOpenImmersion.lift_fac _ _ _
  refine ⟨κ, x ≫ pullback.fst _ _, x, ?_, rfl, ?_⟩
  · rw [Model.j, ← Category.assoc, hx, hw₁]
  · rw [← Y.jQ_over, ← Category.assoc, hx, hw₂]

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootHeightDifferenceBoundStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_height_difference_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (c t s lo hi : ℝ) (lam : Wt Ψ N), Close M R i u c → ArchBetween M R i u t lam s lo hi → ∀ (L : Type) [Field L] [NumberField L], ∀ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) - rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) ∈ Set.Icc (lo - (l1 lam + |s|) * c) (hi + (l1 lam + |s|) * c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht | exact GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.CoverEff

section Gen

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unitAt_div_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {s s' : Ω} (h : Λ.IsGenAt p s) (h' : Λ.IsGenAt p s') :
    unitAt ξ p (s' / s) := by
  obtain ⟨h0, e⟩ := h
  obtain ⟨h0', e'⟩ := h'
  have m1 : s' ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← e, e']; exact Submodule.mem_span_singleton_self s'
  have m2 : s ∈ Submodule.span (regAt ξ p) {s'} := by
    rw [← e', e]; exact Submodule.mem_span_singleton_self s
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 m1
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.1 m2
  have hr1 : (r : Ω) * s = s' := hr
  have hr2 : (r' : Ω) * s' = s := hr'
  refine ⟨div_ne_zero h0' h0, ?_, ?_⟩
  · rw [(div_eq_iff h0).2 hr1.symm]; exact r.2
  · rw [inv_div, (div_eq_iff h0').2 hr2.symm]; exact r'.2

theorem tens_isGenAt {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {p : Cpt ξ} {s : I → Ω}
    (h : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (h i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s', hs', rfl⟩
    have hu : unitAt ξ p (∏ i, (s' i / s i) ^ a i) :=
      unitAt.prod _ fun i _ => (unitAt_div_of_isGenAt (h i) (hs' i)).zpow _
    have e : ∏ i, s' i ^ a i = (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_zpow, div_mul_cancel₀ _ (h i).1]
    rw [e]
    exact Submodule.mem_span_singleton.2 ⟨⟨_, hu.2.1⟩, rfl⟩
  · refine Submodule.span_mono ?_
    rintro _ rfl
    exact ⟨s, h, rfl⟩

theorem exists_gen_of_tens {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {a : I → ℤ} {p : Cpt ξ} {t : Ω}
    (h : (Lat.tens Λ a).IsGenAt p t) : ∃ s : I → Ω, ∀ i, (Λ i).IsGenAt p (s i) := by
  by_contra hn
  have hE : {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨s, hs, _⟩ => hn ⟨s, hs⟩
  have m : t ∈ (Lat.tens Λ a) p := by
    rw [h.2]; exact Submodule.mem_span_singleton_self t
  have m' : t ∈ Submodule.span (regAt ξ p) (∅ : Set Ω) := by
    rw [← hE]; exact m
  rw [Submodule.span_empty, Submodule.mem_bot] at m'
  exact h.1 m'

theorem unitAt_of_mul {p : Cpt ξ} {a b : Ω} (hab : unitAt ξ p (a * b)) (hb : unitAt ξ p b) : unitAt ξ p a := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hab.1
  refine ⟨ha, ?_, ?_⟩
  · have e : a = a * b * b⁻¹ := by field_simp [hb.1]
    rw [e]; exact mul_mem hab.2.1 hb.2.2
  · have e : a⁻¹ = (a * b)⁻¹ * b := by field_simp [hb.1]
    rw [e]; exact mul_mem hab.2.2 hb.2.1

end Gen

section Below

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀}

theorem inChart_below {p : Cpt ξ} {p₀ : Cpt ξ₀} (i : Ω₀ →+* Ω)
    (hU : ∀ a : Ω₀, a ∈ regAt ξ₀ p₀ → unitAt ξ p (i a) → unitAt ξ₀ p₀ a)
    (hR : ∀ a : Ω₀, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p) {κ : Type} {x : κ → Ω₀} {a a₀ : κ}
    (h₀ : InChart ξ₀ x a₀ p₀) (h : InChart ξ (fun k => i (x k)) a p) : InChart ξ₀ x a p₀ := by
  have hx : x a ≠ 0 := fun e => h.1 (by simp [e])
  have hu : unitAt ξ₀ p₀ (x a / x a₀) := by
    refine hU _ (h₀.2 a) ⟨(map_ne_zero i).2 (div_ne_zero hx h₀.1), hR _ (h₀.2 a), ?_⟩
    rw [← map_inv₀, inv_div, map_div₀]
    exact h.2 a₀
  refine ⟨hx, fun c => ?_⟩
  have e : x c / x a = x c / x a₀ * (x a / x a₀)⁻¹ := by
    have := h₀.1
    field_simp
  rw [e]
  exact mul_mem (h₀.2 c) hu.2.2

end Below

theorem rootLat_isGenAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y}
    (Fl : 𝔐.Flag) (r : RootIx D) {p : Cpt 𝔐.ξ} {g : Ω}
    (hg : ((𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2).IsGenAt p g) :
    (Fl.rootLat r).IsGenAt p (g ^ HodgeCpt.rootSgn D r) := by
  have := tens_isGenAt (I := Unit)
    (Λ := fun _ => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
    (fun _ => HodgeCpt.rootSgn D r) (p := p) (s := fun _ => g) fun _ => hg
  simpa [HodgeCpt.Flag.rootLat] using this

theorem section_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (S₀ S : Finset ℕ) (o : RootOrigin Y S₀ R Fx) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (𝔐 : HodgeCpt Y S y) (i : R.Ω →+* Ω) (h : 𝔐.X ⟶ o.𝔐.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GenPull o.Fl Fl i hd → Fl.RootLines xdeg e → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt o.𝔐.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ x : 𝔐.X, x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus o.𝔐.t.G) → ∀ p : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p) → ∀ (a : Fin (Fx.m + 1)) (t : Ω), InChart 𝔐.ξ (fun i' => (i.comp o.g) (Fx.yf i')) a p → (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p t → (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t ∈ regAt 𝔐.ξ p ∧ (p.1 ∉ abLocus 𝔐.t.G → ¬ unitAt 𝔐.ξ p ((i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t)) := by
  intro E _ _ _ H D l Xo c O _ β Y Sys Fx R S₀ S o Ω _ K _ J _ y bk bx 𝔐 i h hd Fl xdeg e hy hG hL hU hR hab p hp a t
    hch ht
  have hp0 : ∀ r : ℕ, r.Prime → ¬ InFibre o.𝔐.ξ r (pushCpt hd p) := by
    intro r hr hf
    apply hf
    have u : unitAt 𝔐.ξ p (r : Ω) := not_not.1 (hp r hr)
    exact hU p (r : R.Ω) (natCast_mem _ r) (by rw [map_natCast]; exact u)
  obtain ⟨c₀, hc₀⟩ := o.𝔐.tie.cover (pushCpt hd p)
  have hprod : ∀ k, R.y ⟨k, c₀ k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc₀.1) k (Finset.mem_univ k)
  have ya₀ : o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) = R.y ⟨o.k₀, c₀ o.k₀⟩ := by
    rw [← o.y_eq, Equiv.apply_symm_apply]
  have hch₀ : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) (o.ix.symm (c₀ o.k₀)) (pushCpt hd p) := by
    refine ⟨?_, fun j => ?_⟩
    · show o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) ≠ 0
      rw [ya₀]; exact hprod _
    · show o.g (Fx.yf j) / o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) ∈ _
      rw [ya₀, ← o.y_eq]
      exact Lat.block_ratio_mem hc₀ o.k₀ (o.ix j)
  have hcha : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) a (pushCpt hd p) :=
    inChart_below i (hU p) (hR p) hch₀ hch
  have gens : ∀ r : RootIx D, ∃ g : R.Ω, ((o.𝔐.V (HodgeCpt.rootIdx D r).1).gr (o.Fl.b (HodgeCpt.rootIdx D r).1)
      (HodgeCpt.rootIdx D r).2).IsGenAt (pushCpt hd p) g := by
    intro r
    have hgen : (o.Fl.rootLat r).IsGenAt (pushCpt hd p) ((∏ k, R.y ⟨k, c₀ k⟩ ^ R.xdeg r k) • o.e r) :=
      ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hprod k)) (o.lines r).1,
        (o.lines r).2 _ trivial c₀ hc₀⟩
    obtain ⟨s, hs⟩ := exists_gen_of_tens hgen
    exact ⟨s (), hs ()⟩
  choose g hg using gens
  have ht₀ := tens_isGenAt (fun r => -Fx.n r) fun r => rootLat_isGenAt o.Fl r (hg r)
  have ht₁ : (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p
      (i (∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r))) := by
    have := tens_isGenAt (Λ := Fl.rootLat) (fun r => -Fx.n r) fun r =>
      rootLat_isGenAt Fl r (hG p hp _ _ _ (hg r))
    simpa only [map_prod, map_zpow₀] using this
  have hv := unitAt_div_of_isGenAt ht ht₁
  obtain ⟨hreg, hnu⟩ := o.eff (pushCpt hd p) hp0 a _ hcha ht₀
  have key : (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t =
      i (o.g Fx.sE * o.g (Fx.yf a) ^ Fx.q' / ∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r)) *
        (i (∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r)) / t) := by
    have h1 := ht₁.1
    have h2 := ht.1
    rw [map_div₀ i (o.g Fx.sE * o.g (Fx.yf a) ^ Fx.q'), div_mul_div_cancel₀ h1, map_mul, map_pow]
    rfl
  rw [key]
  refine ⟨mul_mem (hR p _ hreg) hv.2.1, fun hnab hu => ?_⟩
  exact hnu (fun hm => hnab ((hab p.1).2 hm)) (hU p _ hreg (unitAt_of_mul hu hv))

end GlobalTheory.CompanionTheory.Ar.Chg.CoverEff
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianStatementHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem saStatement_holds : ReciprocityTheory.ChartRestriction.G.SA.SAStatement := PositivityTheory.EqVol.sa

end GlobalTheory.CompanionTheory.Ar.Link
end

