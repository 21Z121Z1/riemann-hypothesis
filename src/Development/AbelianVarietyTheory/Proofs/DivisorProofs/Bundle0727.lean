import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0417
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsExistAffineZeroSection
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer.PerExist

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

theorem ev_cst (K : Charts F) (k : K.K) (p : Tot I g) (hp : p ∈ K.W k) :
    (Hol.ev p hp).toRingHom.comp (K.cst k) = (Hol.ev p.1 (K.base k p hp)).toRingHom :=
  RingHom.ext fun f ↦ by
    change Hol.ev p hp (K.cst k f) = Hol.ev p.1 (K.base k p hp) f
    rw [Hol.ev_apply, Hol.ev_apply]
    exact K.fn_cst k f hp

theorem ev_sh {K : Charts F} {l : Λ} {k k' : K.K} (h : K.le l k' k) (p : Tot I g) (hp : p ∈ K.W k') :
    (Hol.ev p hp).toRingHom.comp (Charts.sh h) = (Hol.ev (F.shift l p) (K.maps h p hp)).toRingHom :=
  RingHom.ext fun f ↦ by
    change Hol.ev p hp (Charts.sh h f) = Hol.ev (F.shift l p) (K.maps h p hp) f
    rw [Hol.ev_apply, Hol.ev_apply]
    exact Charts.fn_sh h f hp

def Pt (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  ∃ x : Sp (Hol W) ⟶ X, ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p

theorem Pt.mono {u : Unif F s σ} {W W' : Opens (Tot I g)} (hW : W' ≤ W) (h : Pt u W) : Pt u W' := by
  obtain ⟨x, hx⟩ := h
  refine ⟨spMap (Hol.comap id analyticOnNhd_id (fun p hp ↦ hW hp)).toRingHom ≫ x, fun p hp ↦ ?_⟩
  rw [← Category.assoc, ← Cris.spMap_comp]
  have e : (Hol.ev p hp).toRingHom.comp (Hol.comap id analyticOnNhd_id (fun p hp ↦ hW hp) : Hol W →ₐ[ℂ] Hol W').toRingHom =
      (Hol.ev p (hW hp)).toRingHom :=
    RingHom.ext fun f ↦ by
      change Hol.ev p hp (Hol.comap id analyticOnNhd_id (fun p hp ↦ hW hp) f) = Hol.ev p (hW hp) f
      rw [Hol.ev_apply, Hol.ev_apply]
      exact Hol.fn_comap _ _ _ f hp
  rw [e]
  exact hx p (hW hp)

theorem isHolTo (u : Unif F s σ) (W : Opens (Tot I g)) (hW : ∀ p ∈ W, p.1 ∈ F.V) : IsHolTo (W : Set (Tot I g)) u.E := by
  intro U f
  obtain ⟨ho, hd⟩ := u.hol U f
  have e : {b ∈ (W : Set (Tot I g)) | ⊤ ≤ u.E b ⁻¹ᵁ U} =
      (W : Set (Tot I g)) ∩ {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U} :=
    Set.ext fun b ↦ ⟨fun h ↦ ⟨h.1, hW b h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
  rw [e]
  exact ⟨W.isOpen.inter ho, hd.mono Set.inter_subset_right⟩

theorem pt_of_affine (u : Unif F s σ) (U : X.Opens) (hU : IsAffineOpen U) (W : Opens (Tot I g))
    (hW : ∀ p ∈ W, p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U) : Pt u W := by
  obtain ⟨x, -, hx⟩ := exists_point_hol (Tot I g) W X u.E U hU (isHolTo u W fun p hp ↦ (hW p hp).1)
    fun p hp ↦ (hW p hp).2
  exact ⟨x, hx⟩

def inU (u : Unif F s σ) (U : X.Opens) : Opens (Tot I g) :=
  ⟨{p | p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U}, (u.hol U 0).1⟩

variable (u : Unif F s σ)

abbrev Kmax : Charts F := Charts.std F (Pt u)

theorem rich : (Kmax u).Rich := by
  refine ⟨fun p hp ↦ ?_, fun l k₁ k₂ p h₁ h₂ ↦ ?_⟩
  · obtain ⟨_, ⟨U, hU, rfl⟩, hq, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (u.E p (default : PrimeSpectrum ℂ))) isOpen_univ
    have hpU : p ∈ inU u U := ⟨hp, fun y _ ↦ by
      rw [Subsingleton.elim (α := PrimeSpectrum ℂ) y default]
      exact hq⟩
    exact ⟨⟨inU u U, fun q hq ↦ hq.1, pt_of_affine u U hU _ fun q hq ↦ hq⟩, hpU⟩
  · let W : Opens (Tot I g) := ⟨(k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' (k₂.1 : Set (Tot I g)),
      (F.shift_analytic l k₁.2.1).continuousOn.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen⟩
    have hW : W ≤ k₁.1 := fun q hq ↦ hq.1
    refine ⟨⟨W, fun q hq ↦ k₁.2.1 q hq.1, k₁.2.2.mono hW⟩, ⟨h₁, h₂⟩, fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    change F.shift 0 q ∈ k₁.1
    rw [F.shift_zero]
    exact hq.1

theorem based (hu : u.Based) : (Kmax u).Based := by
  obtain ⟨U, hU, hz⟩ := hu
  exact ⟨⟨inU u U, fun q hq ↦ hq.1, pt_of_affine u U hU _ fun q hq ↦ hq⟩, fun z hz' ↦ ⟨hz', hz z hz'⟩⟩

theorem over_base (K : Charts F) (k : K.K) (x : Sp (Hol (K.W k)) ⟶ X)
    (hx : ∀ (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p) :
    x ≫ s = spMap ((K.cst k).comp σ) :=
  point_hol_ext (Tot I g) (K.W k) (Sp B) _ (Limits.terminal.from _) _ _ (Limits.terminal.hom_ext _ _) fun p hp ↦ by
    change spMap (Hol.ev p hp).toRingHom ≫ x ≫ s = spMap (Hol.ev p hp).toRingHom ≫ _
    rw [← Category.assoc, hx p hp, u.w p (K.base k p hp), ← Cris.spMap_comp, ← RingHom.comp_assoc, ev_cst]

variable [IsSeparated s]

theorem pt_unique (K : Charts F) (k : K.K) (x x' : Sp (Hol (K.W k)) ⟶ X)
    (hx : ∀ (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p)
    (hx' : ∀ (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ x' = u.E p) : x = x' :=
  point_hol_ext (Tot I g) (K.W k) X (Sp B) s _ _ ((over_base u K k x hx).trans (over_base u K k x' hx').symm)
    fun p hp ↦ (hx p hp).trans (hx' p hp).symm

def rmax : Real (Kmax u) s σ where
  x k := k.2.2.choose
  w k := over_base u (Kmax u) k _ k.2.2.choose_spec
  compat {l k k'} h := pt_unique u (Kmax u) k' _ _ (fun p hp ↦ by
    rw [← Category.assoc, ← Cris.spMap_comp, ev_sh h p hp]
    exact (k.2.2.choose_spec _ _).trans (u.per l p (k'.2.1 p hp))) k'.2.2.choose_spec

variable {u} {K : Charts F} {r : Real K s σ}

omit [IsSeparated s] in

def toMax (hr : r.IsFor u) : K.Obj ⥤ (Kmax u).Obj where
  obj T :=
    { k := ⟨K.W T.k, K.base T.k, r.x T.k, hr T.k⟩
      C := T.C
      J := T.J
      nil := T.nil
      ρ := T.ρ
      ρ_cst := T.ρ_cst }
  map {T T'} f :=
    { φ := (Charts.Hom.φ f : T.C →ₐ[Hol F.V] T'.C)
      deg := Charts.Hom.deg f
      le := K.maps (Charts.Hom.le f)
      mem := Charts.Hom.mem f
      close := Charts.Hom.close f }

omit [IsSeparated s] in

def toMaxCoef (hr : r.IsFor u) : CoefMap (RingHom.id (Hol F.V)) (Kmax u).Oc K.Oc where
  G := toMax hr
  α T := RingHom.id T.C
  naturality _ _ := rfl
  smul _ _ _ := rfl

def toMaxTrans (hr : r.IsFor u) : r.coef.G ⟶ ((rmax u).coef.comp (toMaxCoef hr)).G where
  app T :=
    { φ := { RingHom.id T.C with commutes' := fun _ ↦ rfl }
      φ₀ := RingHom.id (T.C ⧸ T.J)
      comm := fun _ ↦ rfl
      dp := letI := T.ratAlg; isDPMorphism_of_rat T.δ T.δ (RingHom.id T.C) fun _ h ↦ h
      pt := ((congrArg (· ≫ _) (Cris.spMap_id (T.C ⧸ T.J))).trans (Category.id_comp _)).trans
        (congrArg (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ ·)
          (pt_unique u K T.k _ _ (hr T.k) ((toMax hr).obj T).k.2.2.choose_spec)) }
  naturality _ _ _ := Thick.hom_ext fun _ ↦ rfl

end GlobalTheory.AnPer.PerExist

namespace GlobalTheory.AnPer

open PerExist in

theorem periods_exist : PExist := by
  intro I _ g Λ _ F B _ X s _ σ u hu c
  obtain ⟨per, hper⟩ := GlobalTheory.T.exists_period_cohomologyClass_of_rich_based (Kmax u) (rich u) (based u hu) ((rmax u).coef.pull1 c)
  refine ⟨per, fun K r hr ↦ ?_⟩
  refine (CoefMap.pullCohomologyOne_eq_of_natTrans r.coef _ (toMaxTrans hr) (fun _ _ ↦ rfl) c).trans ?_
  rw [CoefMap.pullCohomologyOne_comp, hper]
  rfl

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsOfDeRhamClassesUnique
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer.MaxCharts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

def Alg (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  ∃ x : Sp (Hol W) ⟶ X, (∀ h : ∀ p ∈ W, p.1 ∈ F.V,
      x ≫ s = spMap ((Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) h).toRingHom.comp σ)) ∧
    ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p

theorem alg_of_ev (u : Unif F s σ) (W : Opens (Tot I g)) (x : Sp (Hol W) ⟶ X)
    (hx : ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p) : Alg u W := by
  refine ⟨x, fun h ↦ ?_, hx⟩
  refine point_hol_ext _ W (Sp B) (⊤_ Scheme.{0}) (terminal.from _) _ _ (terminal.hom_ext _ _) fun p hp ↦ ?_
  have e := hx p hp
  change spMap (Hol.ev p hp).toRingHom ≫ _ = spMap (Hol.ev p hp).toRingHom ≫ _
  rw [← Category.assoc, e, u.w p (h p hp), ← Cris.spMap_comp]
  rfl

theorem alg_mono (u : Unif F s σ) {W W' : Opens (Tot I g)} (h : W' ≤ W) (a : Alg u W) : Alg u W' := by
  obtain ⟨x, -, hx⟩ := a
  refine alg_of_ev u W' (spMap (Hol.comap id analyticOnNhd_id (fun p hp ↦ h hp)).toRingHom ≫ x) fun p hp ↦ ?_
  rw [← Category.assoc, ← Cris.spMap_comp, ← hx p (h hp)]
  rfl

@[reducible] def charts (u : Unif F s σ) : Charts F := Charts.std F (Alg u)

def real [IsSeparated s] (u : Unif F s σ) : Real (charts u) s σ where
  x k := k.2.2.choose
  w k := k.2.2.choose_spec.1 k.2.1
  compat {l k k'} h := by
    refine point_hol_ext _ k'.1 X _ s _ _ ?_ fun p hp ↦ ?_
    · rw [Category.assoc, k.2.2.choose_spec.1 k.2.1, k'.2.2.choose_spec.1 k'.2.1, ← Cris.spMap_comp]
      exact congrArg spMap (RingHom.ext fun b ↦ Charts.sh_cst (K := charts u) h (σ b))
    · change spMap (Hol.ev p hp).toRingHom ≫ _ = spMap (Hol.ev p hp).toRingHom ≫ _
      rw [k'.2.2.choose_spec.2 p hp, ← Category.assoc, ← Cris.spMap_comp, ← u.per l p (k'.2.1 p hp),
        ← k.2.2.choose_spec.2 _ (h p hp)]
      rfl

theorem isFor [IsSeparated s] (u : Unif F s σ) : (real u).IsFor u := fun k ↦ k.2.2.choose_spec.2

theorem rich (u : Unif F s σ) : (charts u).Rich := by
  constructor
  · intro p hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := u.E p (default : PrimeSpectrum ℂ))
      (U := ⊤) trivial
    let W : Opens (Tot I g) := ⟨{q | q.1 ∈ F.V ∧ ⊤ ≤ u.E q ⁻¹ᵁ U}, (u.hol U 0).1⟩
    have hol : IsHolTo (W : Set (Tot I g)) u.E := fun U' f ↦ ⟨by
      have e : {q | q ∈ (W : Set (Tot I g)) ∧ ⊤ ≤ u.E q ⁻¹ᵁ U'} =
          (W : Set (Tot I g)) ∩ {q | q.1 ∈ F.V ∧ ⊤ ≤ u.E q ⁻¹ᵁ U'} :=
        Set.ext fun q ↦ ⟨fun h ↦ ⟨h.1, h.1.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
      exact e ▸ W.isOpen.inter (u.hol U' f).1,
      (u.hol U' f).2.mono fun q h ↦ ⟨h.1.1, h.2⟩⟩
    obtain ⟨x, -, hx⟩ := exists_point_hol _ W X u.E U hU hol fun q hq ↦ hq.2
    refine ⟨⟨W, fun q hq ↦ hq.1, alg_of_ev u W x hx⟩, hp, fun y _ ↦ ?_⟩
    obtain rfl : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact hpU
  · intro l k₁ k₂ p h₁ h₂
    have ho : IsOpen ((k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' (k₂.1 : Set (Tot I g))) :=
      (F.shift_analytic l k₁.2.1).continuousOn.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen
    refine ⟨⟨⟨_, ho⟩, fun q hq ↦ k₁.2.1 q hq.1, alg_mono u (fun q hq ↦ hq.1) k₁.2.2⟩, ⟨h₁, h₂⟩,
      fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    rw [F.shift_zero]
    exact hq.1

end GlobalTheory.AnPer.MaxCharts

namespace GlobalTheory.AnPer

theorem period_unique : PUniq := by
  intro I _ g Λ _ F B _ X s _ σ u c per per' h h'
  exact GlobalTheory.T.periodClass_injective_of_rich_charts (MaxCharts.charts u) (MaxCharts.rich u) per per'
    ((h _ _ (MaxCharts.isFor u)).symm.trans (h' _ _ (MaxCharts.isFor u)))

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshNormalFrameQuadraticComparison
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem leviV_re_le_sum_norm {n : ℕ} (g : V n → ℂ) (p ζ : V n) :
    (leviV n g p ζ.ofLp).re ≤
      (∑ j, ∑ k, ‖wd n j (wdb n k g) p‖) * ‖ζ‖ ^ 2 := by
  calc (leviV n g p ζ.ofLp).re ≤ ‖leviV n g p ζ.ofLp‖ := Complex.re_le_norm _
    _ ≤ ∑ j, ‖∑ k, wd n j (wdb n k g) p * ζ.ofLp j * (starRingEnd ℂ) (ζ.ofLp k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j, ∑ k, ‖wd n j (wdb n k g) p‖ * ‖ζ‖ ^ 2 := by
        gcongr with j _
        refine (norm_sum_le _ _).trans ?_
        gcongr with k _
        rw [norm_mul, norm_mul, Complex.norm_conj, sq, ← mul_assoc]
        have hj : ‖ζ.ofLp j‖ ≤ ‖ζ‖ := PiLp.norm_apply_le ζ j
        have hk : ‖ζ.ofLp k‖ ≤ ‖ζ‖ := PiLp.norm_apply_le ζ k
        gcongr
    _ = (∑ j, ∑ k, ‖wd n j (wdb n k g) p‖) * ‖ζ‖ ^ 2 := by
        simp only [Finset.sum_mul]

theorem psh_normal_frame : ∀ (n : ℕ) (O : Set (V n)) (φ : V n → ℝ) (p : V n), IsOpen O → p ∈ O → ContDiffOn ℝ ∞ φ O → (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => ((φ w : ℝ) : ℂ)) p ξ).re) → ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧ closedBall p ρ ⊆ O ∧ ∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ φ v - 2 * (q v).re ∧ φ v - 2 * (q v).re ≤ C * ‖v - p‖ ^ 2 := by
  intro n O φ p hO hp hφ hlevi
  set g : V n → ℂ := fun w => ((φ w : ℝ) : ℂ) with hg
  have hgs : ContDiffOn ℝ ∞ g O := Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  obtain ⟨m, hm, hmb⟩ := levi_pos_compact (g := g) hO hgs (K0 := {p}) isCompact_singleton
    (Set.singleton_subset_iff.2 hp) (fun u hu ζ hζ => by
      rw [Set.mem_singleton_iff.1 hu]
      refine hlevi _ ?_
      intro h0; apply hζ
      exact (WithLp.ofLp_eq_zero 2).1 h0)
  have hφ2 : ContDiffAt ℝ 2 φ p :=
    ((hφ.contDiffAt (hO.mem_nhds hp)).of_le (by norm_cast))
  obtain ⟨q, hq, ho⟩ := GlobalTheory.T.exists_holo_quadratic_add_levi_isLittleO n φ p hφ2
  set A : ℝ := ∑ j, ∑ k, ‖wd n j (wdb n k g) p‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _
  have hev := ho.def (half_pos hm)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨ε2, hε2, hε2O⟩ := Metric.isOpen_iff.1 hO p hp
  refine ⟨q, m / 2, A + m / 2, min ε ε2 / 2, hq, half_pos hm, by positivity,
    by positivity, ?_, ?_⟩
  · intro v hv
    apply hε2O
    rw [mem_closedBall] at hv
    rw [mem_ball]
    have : min ε ε2 / 2 < ε2 := by
      have := min_le_right ε ε2; linarith [lt_min hε hε2]
    linarith
  · intro v hv
    rw [mem_closedBall] at hv
    have hvε : dist v p < ε := by
      have := min_le_left ε ε2; linarith [lt_min hε hε2]
    have hR := hεb hvε
    rw [Real.norm_eq_abs, norm_pow, norm_norm] at hR
    have hlo := hmb p rfl (v - p)
    have hup := leviV_re_le_sum_norm g p (v - p)
    have habs := abs_le.1 hR
    change m * ‖v - p‖ ^ 2 ≤ (leviV n g p (fun j => (v - p) j)).re at hlo
    change (leviV n g p (fun j => (v - p) j)).re ≤ A * ‖v - p‖ ^ 2 at hup
    constructor <;> nlinarith [habs.1, habs.2, sq_nonneg ‖v - p‖]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantRankProperty
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem detElt_transport_isom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → ∃ (Δ' : RL p O Λ) (c' : (Λ →+* O) → C), IsDetElt ε ψ N Δ' ∧ HasOrders C ε N Δ' (fun σ => a ((γ : O →+* O).comp σ)) c' ∧ ∀ σ, v (c' σ) = v (c ((γ : O →+* O).comp σ)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ γ hγ N Δ a c hΔ hord
  obtain ⟨γC, hγC, hvγ⟩ := hγ
  obtain ⟨Γ, ε', hε', hξ, hμ, hψΓ, hθ⟩ := GlobalTheory.T.exists_tilt_automorphism_transport p O ε Λ ψ γ.symm hψ hε
  have halg : ∀ x : O, algebraMap O C (γ.symm x) = γC.symm (algebraMap O C x) := by
    intro x
    apply γC.injective
    rw [hγC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have huniq : ∀ (σ : Λ →+* O) (f g : RL p O Λ →+* O), IsTheta σ f → IsTheta σ g → f = g := by
    intro σ f g hf hg
    apply RingHom.ext
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [hf, hg]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcomp : ∀ σ : Λ →+* O, ((γ.symm : O ≃+* O) : O →+* O).comp ((γ : O →+* O).comp σ) = σ := by
    intro σ
    ext l
    simp
  have hkey : ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f →
      ∃ f₁ : RL p O Λ →+* O, IsTheta ((γ : O →+* O).comp σ) f₁ ∧ ∀ r, f (Γ r) = γ.symm (f₁ r) := by
    intro σ f hf
    obtain ⟨f₁, hf₁, -⟩ := theta_tensor_exists p C v O hv ε hε Λ ((γ : O →+* O).comp σ)
    obtain ⟨f'', hf'', hf''Γ⟩ := hθ _ f₁ hf₁
    rw [hcomp] at hf''
    have he := huniq σ f'' f hf'' hf
    exact ⟨f₁, hf₁, fun r => by rw [← he]; exact hf''Γ r⟩
  have hΔ' : IsDetElt ε' ψ N (Γ Δ) := by
    obtain ⟨hdiv, g, hg, hgdiv⟩ := hΔ
    refine ⟨?_, Γ g, ?_, ?_⟩
    · rw [← hμ, ← map_pow]; exact map_dvd Γ hdiv
    · rw [← hψΓ, ← map_mul, ← hg]
    · rw [← hξ, ← map_pow]; exact map_dvd Γ hgdiv
  have hord' : HasOrders C ε' N (Γ Δ) (fun σ => a ((γ : O →+* O).comp σ))
      (fun σ => γC.symm (c ((γ : O →+* O).comp σ))) := by
    intro σ f hf
    obtain ⟨f₁, hf₁, hfΓ⟩ := hkey σ f hf
    obtain ⟨hle, hc, s, t, hs, hst, ht⟩ := hord _ f₁ hf₁
    refine ⟨hle, (map_ne_zero γC.symm).mpr hc, Γ s, Γ t, ?_, ?_, ?_⟩
    · simp only [RingHom.comp_apply] at hs ⊢
      rw [hfΓ, halg]
      exact (map_ne_zero γC.symm).mpr hs
    · rw [← map_mul, hst, map_mul, map_pow, hξ]
    · simp only [RingHom.comp_apply] at ht ⊢
      rw [hfΓ, hfΓ, halg, halg, ht, map_mul]
  obtain ⟨hxi, hmu⟩ := GlobalTheory.T.xi_mu_associated_of_primitive_roots p C v O hv ε' hε' ε hε
  obtain ⟨c', h1, h2, h3⟩ := GlobalTheory.T.determinant_orders_independent_of_root p C v O hv ε' ε Λ ψ N (Γ Δ) _ _ hxi hmu hΔ' hord'
  refine ⟨Γ Δ, c', h1, h2, fun σ => ?_⟩
  rw [h3, ← hvγ (γC.symm _), RingEquiv.apply_symm_apply]

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomConnectedFactorThroughPartStatement
section
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearHom_connected_factor_through_part : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  first | exact @GlobalTheory.PDivGroup.semiHom_app_eq_conn_part | exact GlobalTheory.PDivGroup.semiHom_app_eq_conn_part | (intros; apply GlobalTheory.PDivGroup.semiHom_app_eq_conn_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomEtaleFactorThroughPartStatement
section
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearHom_etale_factor_through_part : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₀.IsConn → C.IsEt →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₁.app n (i₁.app n (x.app n a)) = x.app n a := by
  first | exact @GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt | exact GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt | (intros; apply GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapValHomFromSpec
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

variable {X : Scheme.{0}}

def valHom (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valHom x U h f = valAt' x U f := by
  rw [valAt', dif_pos h]; rfl

theorem specMap_valHom_fromSpec (x : Sp ℂ ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    spMap (valHom x U h) ≫ hU.fromSpec = x := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Sp ℂ)) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have e2 : CommRingCat.ofHom (valHom x U h) = x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := rfl
  rw [spMap, e2, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem exists_pt_of_affine : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) (W : Opens (Tot I g)), (∀ p ∈ W, p.1 ∈ F.V) → ∀ U : X.Opens, IsAffineOpen U → (∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U) → ∃ x : Sp (Hol W) ⟶ X, ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p := by
  intro I _ g Λ _ F B _ X s σ u W hW U hU hWU
  have han : ∀ f : Γ(X, U), AnalyticOnNhd ℂ (fun p ↦ valAt' (u.E p) U f) W := fun f p hp ↦
    GlobalTheory.SCV.analyticAt_of_differentiableOn (u.hol U f).2 ((u.hol U f).1.mem_nhds ⟨hW p hp, hWU p hp⟩)
  let φ : Γ(X, U) →+* Hol W :=
    (RingHom.pi fun p : W ↦ valHom (u.E p) U (hWU p p.2)).codRestrict (holSub W) fun f ↦
      ⟨fun p ↦ valAt' (u.E p) U f, han f, fun p ↦ valHom_apply _ _ _ f⟩
  refine ⟨spMap φ ≫ hU.fromSpec, ?_, fun p hp ↦ ?_⟩
  · simp [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
  · have e : (Hol.ev p hp).toRingHom.comp φ = valHom (u.E p) U (hWU p hp) := RingHom.ext fun f ↦ rfl
    rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    exact specMap_valHom_fromSpec _ hU _

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonInvariantDifferentialsOfEtaleStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_invariantDifferentials_of_etale : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  first | exact @GlobalTheory.PDivGroup.subsingleton_omega_of_isEt | exact GlobalTheory.PDivGroup.subsingleton_omega_of_isEt | (intros; apply GlobalTheory.PDivGroup.subsingleton_omega_of_isEt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleAdditiveEqCoboundaryAddStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricCocycle_additive_eq_coboundary_add : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R), IsCoc (addLaw R d) c → constantCoeff c = 0 → ∃ b : MvPowerSeries (Fin d) R, c = cob1 (addLaw R d) b + ∑ m : Fin d, at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (Pi.single m (X (Sum.inr m))) := by
  first | exact @GlobalTheory.symmetricCocycle_additive_eq_coboundary_add_alt | exact GlobalTheory.symmetricCocycle_additive_eq_coboundary_add_alt | (intros; apply GlobalTheory.symmetricCocycle_additive_eq_coboundary_add_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_spec_twist_independent : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → ∀ n i j : ℤ, Nonempty (Ht q (sp A) n i ≃+ Ht q (sp A) n j) := by
  first | (exact @GlobalTheory.EtC.untwist) | (exact GlobalTheory.EtC.untwist) | (intros; apply GlobalTheory.EtC.untwist  <;> assumption)
end

