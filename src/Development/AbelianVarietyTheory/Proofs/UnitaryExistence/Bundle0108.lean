import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunction
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0047
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0103
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0105
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOrthogonalIdempotentSectionsPeriodSpaces
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

noncomputable section

namespace GlobalTheory.CompSystem

open GlobalTheory.CompIdem GlobalTheory.CompFun

theorem orthogonal_of_fibres {R ι : Type} [CommRing R] [Fintype ι] (e : ι → R) (he : ∀ i, IsIdempotentElem (e i))
    (k : PrimeSpectrum R → ι) (h : ∀ i z, e i ∉ z.asIdeal ↔ k z = i) :
    (∀ i j, i ≠ j → e i * e j = 0) ∧ ∑ i, e i = 1 := by
  classical
  have ho : ∀ i j, i ≠ j → e i * e j = 0 := by
    intro i j hij
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem ((he i).mul (he j)) IsIdempotentElem.zero ?_
    ext z
    refine iff_of_false (fun hz => ?_) (fun hz => hz (zero_mem _))
    have hz' : e i * e j ∉ z.asIdeal := hz
    exact hij (((h i z).1 fun h1 => hz' (z.asIdeal.mul_mem_right _ h1)).symm.trans
      ((h j z).1 fun h1 => hz' (z.asIdeal.mul_mem_left _ h1)))
  refine ⟨ho, ?_⟩
  have hs : IsIdempotentElem (∑ i, e i) :=
    (OrthogonalIdempotents.mk he fun i j hij => ho i j hij).isIdempotentElem_sum
  refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem hs IsIdempotentElem.one ?_
  ext z
  refine iff_of_true (fun hz => ?_) (fun hz => z.2.ne_top ((Ideal.eq_top_iff_one _).2 hz))
  refine (h (k z) z).2 rfl ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (k z))] at hz
  refine (Ideal.add_mem_iff_left _ (sum_mem fun j hj => ?_)).1 hz
  by_contra hc
  exact (Finset.mem_erase.1 hj).1 ((h j z).1 hc).symm

theorem exists_complex_point {K : Type} [Field K] (σ : K →+* ℂ) {Y : Scheme.{0}} (s : Y ⟶ Sp K)
    [LocallyOfFiniteType s] {V : Set Y} (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ p : Sp ℂ ⟶ Y, p ≫ s = spMap σ ∧ p (IsLocalRing.closedPoint ℂ) ∈ V := by
  let g := pullback.snd s (spMap σ)
  let π := pullback.fst s (spMap σ)
  have hy : Surjective (spMap σ) :=
    ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have := LocallyOfFiniteType.jacobsonSpace g
  obtain ⟨z, hz⟩ := hne
  obtain ⟨w, rfl⟩ := π.surjective z
  obtain ⟨x, hx, hc'⟩ := nonempty_inter_closedPoints (Z := π ⁻¹' V) ⟨w, hz⟩
    (hV.preimage π.continuous).isLocallyClosed
  have hc : IsClosed ({x} : Set _) := hc'
  refine ⟨pointOfClosedPoint g x hc ≫ π, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · exact (congrArg (π · ∈ V) (pointOfClosedPoint_apply g x hc _)).mpr hx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem exists_indicator_test (hA : AllTest Xo c) (U : Set (Xo.XF c)) (hU : IsClopen U) :
    ∃ χ ∈ sec Xo c 0 0, (∀ (p : TRing c.F) (y : FrPt Xo c p.R), IsIdempotentElem (χ p y) ∧
      ∀ z : PrimeSpectrum p.R, χ p y ∉ z.asIdeal ↔ basePt y z ∈ U) ∧
      ∀ (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S),
      IsIdempotentElem (evR Xo c χ y) ∧
        ∀ z : PrimeSpectrum S, evR Xo c χ y ∉ z.asIdeal ↔ basePt y z ∈ U := by
  have hex : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃ e : p.R, IsIdempotentElem e ∧
      ∀ z : PrimeSpectrum p.R, e ∉ z.asIdeal ↔ basePt y z ∈ U := by
    intro p y
    obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (hU.preimage (basePt y).continuous)
    exact ⟨e, he, fun z => (Set.ext_iff.1 h z).symm⟩
  choose χ hi hχ using hex
  have hmap : ∀ (p : TRing c.F) (S : Type) [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R)
      (w : FrPt Xo c S), w.x = spMap φ.toRingHom ≫ y.x →
      ∀ z : PrimeSpectrum S, φ (χ p y) ∉ z.asIdeal ↔ basePt w z ∈ U := by
    intro p S _ _ φ y w h z
    rw [basePt_map φ y w h]
    exact hχ p y (PrimeSpectrum.comap φ.toRingHom z)
  have hw : ∀ (p : TRing c.F) (t : Ix D → (p.R)ˣ), wchar (ex D 0 0) t = 1 := by
    intro p t
    refine Finset.prod_eq_one fun i _ => ?_
    have : ex D 0 0 i = 0 := by rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
    rw [this, pow_zero]
  refine ⟨χ, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, fun p y => ⟨hi p y, hχ p y⟩, fun S _ _ _ y => ?_⟩
  · refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hi q z) ((hi p y).map φ) ?_
    ext w
    exact (hχ q z w).trans (hmap p q.R φ y z h.1 w).symm
  · rw [hw, _root_.one_mul]
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hi p y') (hi p y) ?_
    ext w
    have := hχ p y' w
    rw [basePt_congr y y' h.1] at this
    exact this.trans (hχ p y w).symm
  · have h := hA S y
    have e : evR Xo c χ y = h.choose_spec.choose (χ h.choose h.choose_spec.choose_spec.choose) := dif_pos h
    rw [e]
    exact ⟨(hi _ _).map _, hmap _ S _ _ y h.choose_spec.choose_spec.choose_spec.1⟩

theorem exists_index_map (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (hcl : FnAlgClosed Xo c) :
    ∃ k : Xo.XF c → Fin F.n, (∀ i, IsClopen (k ⁻¹' {i})) ∧ ∀ (y : FrPt Xo c (CAt σ)) (i : Fin F.n) P,
      IsPeriod (F.Di i) ty P → y.x = F.u i P → k (basePt (S := CAt σ) y (IsLocalRing.closedPoint ℂ)) = i := by
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := c.fin
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  let pr : Xo.XF c ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ →
      (p ≫ pr) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, CompIdem.spMap_comp]
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    refine const_on_component_of_closed σ s (fun Z x hx => ?_) (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
    have hx' : IsIntegral c.F (A := kap Z) x := hx
    obtain ⟨k, hk⟩ := hcl Z (algebraMap (kap Z) (Om Z) x) hx'.algebraMap.isAlgebraic
    rw [IsScalarTower.algebraMap_apply c.F (kap Z) (Om Z)] at hk
    exact ⟨k, (algebraMap (kap Z) (Om Z)).injective hk⟩
  have hex : ∀ z : Xo.XF c, ∃ i : Fin F.n, ∃ p : Sp ℂ ⟶ Xo.XF c, p ≫ s = spMap σ ∧
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i := by
    intro z
    obtain ⟨p, hp, hz⟩ := exists_complex_point σ s (isOpen_connectedComponent_of_noetherianSpace z)
      ⟨z, mem_connectedComponent⟩
    obtain ⟨i, P, hP, e⟩ := F.onto _ (hover p hp)
    exact ⟨i, p, hp, hz, e ▸ ht i P hP⟩
  choose k hk using hex
  have hk' : ∀ (z : Xo.XF c) (q : Sp ℂ ⟶ Xo.XF c), q ≫ s = spMap σ →
      q (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z → t (q ≫ pr) = k z := by
    intro z q hq hz
    obtain ⟨p, hp, h1, h2⟩ := hk z
    rw [← h2]
    exact hconst q p hq hp (connectedComponent_eq h1 ▸ hz)
  have hkc : ∀ z w, w ∈ connectedComponent z → k w = k z := by
    intro z w h
    obtain ⟨p, hp, h1, h2⟩ := hk w
    exact Fin.ext (h2.symm.trans (hk' z p hp (connectedComponent_eq h ▸ h1)))
  refine ⟨k, fun i => ?_, fun y i P hP hy => ?_⟩
  · refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hkc z w hw).symm.trans h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hkc z w hw).trans hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  · let p : Sp ℂ ⟶ Xo.XF c := basePt (S := CAt σ) y
    have hp : p ≫ s = spMap σ := pullback.lift_snd _ _ _
    have hp' : t (p ≫ pr) = i := by
      have : p ≫ pr = F.u i P := (pullback.lift_fst _ _ _).trans hy
      rw [this]
      exact ht i P hP
    exact Fin.ext ((hk' _ p hp mem_connectedComponent).symm.trans hp')

theorem exists_orthogonal_idempotents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), FnAlgClosed Xo c → ∃ χ : Fin F.n → Rul Xo c, (∀ i, χ i ∈ sec Xo c 0 0) ∧ (∀ i, χ i * χ i = χ i) ∧ (∀ i i', i ≠ i' → χ i * χ i' = 0) ∧ ∑ i, χ i = 1 ∧ ∀ (y : FrPt Xo c (CAt σ)) (i i' : Fin F.n) P, IsPeriod (F.Di i') ty P → y.x = F.u i' P → toC (evR Xo c (χ i) y) = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo c σ g ty F hcl
  classical
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.allSixLaws.1.secBaseChange E H D l Xo c
  obtain ⟨k, hk, hv⟩ := exists_index_map σ F hcl
  choose χ h1 h2 h3 using fun i => exists_indicator_test hA _ (hk i)
  have ho := fun (p : TRing c.F) (y : FrPt Xo c p.R) => orthogonal_of_fibres (fun i => χ i p y)
    (fun i => (h2 i p y).1) (fun z => k (basePt y z)) fun i z => (h2 i p y).2 z
  refine ⟨χ, h1, fun i => ?_, fun i j hij => ?_, ?_, fun y i i' P hP hy => ?_⟩
  · funext p y
    exact (h2 i p y).1.eq
  · funext p y
    exact (ho p y).1 i j hij
  · funext p y
    rw [Finset.sum_apply, Finset.sum_apply]
    exact (ho p y).2
  · have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    obtain ⟨h4, h5⟩ := h3 i (CAt σ) y
    let v : ℂ := evR Xo c (χ i) (S := CAt σ) y
    have h6 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔
        k (basePt (S := CAt σ) y (IsLocalRing.closedPoint ℂ)) = i := h5 (IsLocalRing.closedPoint ℂ)
    have h8 : v ∉ (IsLocalRing.closedPoint ℂ).asIdeal ↔ v ≠ 0 := by
      show v ∉ IsLocalRing.maximalIdeal ℂ ↔ _
      rw [IsLocalRing.notMem_maximalIdeal, isUnit_iff_ne_zero]
    rw [h8, hv y i' P hP hy] at h6
    have h9 : IsIdempotentElem v := h4
    show v = _
    split_ifs with h
    · exact (IsIdempotentElem.iff_eq_zero_or_one.1 h9).resolve_left (h6.2 h)
    · exact not_not.1 (mt h6.1 h)

end GlobalTheory.CompSystem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPermPeriodSpacesComplexAut
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.ConjPermutes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem ringHom_ext {l : Level H} (hA : l.A = 1) {f f' : KA l →+* ℂ} (h : f (baseKA l).ρ = f' (baseKA l).ρ) :
    f = f' := by
  have hz : zeta l.A = 1 := by
    unfold zeta
    rw [hA]
    simp
  suffices key : ∀ (x : ℂ) (hx : x ∈ IntermediateField.adjoin ℚ ({H.rt0, zeta l.A} : Set ℂ)),
      f ⟨x, hx⟩ = f' ⟨x, hx⟩ by
    ext y
    exact key y.1 y.2
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h
    · exact (congrArg f (Subtype.ext hz)).trans ((map_one f).trans
        ((map_one f').symm.trans (congrArg f' (Subtype.ext hz)).symm))
  | algebraMap r =>
    show f (algebraMap ℚ (KA l) r) = f' (algebraMap ℚ (KA l) r)
    rw [eq_ratCast (algebraMap ℚ (KA l)) r, map_ratCast, map_ratCast]
  | add x y hx hy ihx ihy =>
    show f (⟨x, hx⟩ + ⟨y, hy⟩) = f' (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  | inv x hx ih =>
    show f (⟨x, hx⟩⁻¹) = f' (⟨x, hx⟩⁻¹)
    rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
    show f (⟨x, hx⟩ * ⟨y, hy⟩) = f' (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]

theorem valAt'_top {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) :
    valAt' x ⊤ f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom f) := by
  unfold valAt'
  rw [dif_pos (by simp)]
  unfold valAt
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem valAt'_spMap_comp {X : Scheme.{0}} (τ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) :
    valAt' (spMap τ ≫ x) ⊤ f = τ (valAt' x ⊤ f) := by
  rw [valAt'_top, valAt'_top]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom τ)
  have h2 := congrArg (fun φ => φ.hom (x.appTop.hom f)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simp only [spMap, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  exact h2

theorem valAt'_idem {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {e : Γ(X, ⊤)} (he : e * e = e) :
    valAt' x ⊤ e ∈ ({0, 1} : Set ℂ) := by
  rw [valAt'_top]
  have h : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) *
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) := by
    rw [← map_mul, ← map_mul, he]
  generalize (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (x.appTop.hom e) = v at h ⊢
  have h2 : v * (v - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h0 | h1
  · simp [h0]
  · simp [sub_eq_zero.1 h1]

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_period (F : FamilyUnif Xo σ ty) (hty : IsTypeFn H D.p D.q ty) (i : Fin F.n) :
    ∃ P, IsPeriod (F.Di i) ty P := by
  obtain ⟨hp, hq⟩ := F.sig i
  exact GlobalTheory.PeriodNonempty.exists_isPeriod E H (F.Di i) g ty (by rw [hp, hq]; exact hty)

private theorem key_lemma' (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0)
    (i k k' : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (Q : (F.Di k).La →+ (Fin g → ℂ))
    (Q' : (F.Di k').La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    (hQ : IsPeriod (F.Di k) ty Q) (hQ' : IsPeriod (F.Di k') ty Q')
    (h1 : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u k Q) (h2 : spMap (τ : ℂ →+* ℂ) ≫ F.u i P' = F.u k' Q') :
    k' = k := by
  classical
  obtain ⟨c, -, he⟩ := GlobalTheory.T.exists_coeffField_idempotent_cutting_periodSpaces E H D l Xo σ g ty F hD hσ hty hA (Classical.arbitrary _)
  obtain ⟨e, hee, hev⟩ := he k
  have hs : τ.symm H.rt0 = H.rt0 := by
    rw [RingEquiv.symm_apply_eq]
    exact hτ.symm
  have hjc : σ = ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom).comp
      (IntermediateField.inclusion c.le).toRingHom :=
    ringHom_ext hA (hσ.trans hs.symm)
  have hw : F.u i P ≫ Xo.s = spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.10 i P hP, spMap_comp, ← hjc]
  have hw' : F.u i P' ≫ Xo.s = spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.10 i P' hP', spMap_comp, ← hjc]
  have hsnd : spMap (τ : ℂ →+* ℂ) ≫ spMap ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) =
      spMap c.F.val.toRingHom := by
    rw [spMap_comp]
    congr 1
    ext z
    simp
  have hv1 := hev k Q hQ (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift (F.u i P) _ hw)
    (by rw [Category.assoc, pullback.lift_fst]; exact h1)
    (by rw [Category.assoc, pullback.lift_snd]; exact hsnd)
  have hv2 := hev k' Q' hQ' (spMap (τ : ℂ →+* ℂ) ≫ pullback.lift (F.u i P') _ hw')
    (by rw [Category.assoc, pullback.lift_fst]; exact h2)
    (by rw [Category.assoc, pullback.lift_snd]; exact hsnd)
  have heq := GlobalTheory.CompRat.valAt_eq_of_finite_values E H D l Xo σ g ty F hD hσ hty hA c
    ((τ.symm : ℂ →+* ℂ).comp c.F.val.toRingHom) e {0, 1}
    (Set.toFinite _) (fun y _ => valAt'_idem y hee) i P P' hP hP'
    (pullback.lift (F.u i P) _ hw) (pullback.lift (F.u i P') _ hw')
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  rw [valAt'_spMap_comp, if_pos rfl] at hv1
  rw [valAt'_spMap_comp, ← heq, hv1] at hv2
  by_contra hne
  rw [if_neg hne] at hv2
  exact one_ne_zero hv2

private theorem spMap_comp_u_comp_s_eq_of_fixes_rt0 (F : FamilyUnif Xo σ ty) (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1)
    (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) : (spMap (τ : ℂ →+* ℂ) ≫ F.u i P) ≫ Xo.s = spMap σ := by
  rw [Category.assoc, F.10 i P hP, spMap_comp]
  congr 1
  exact ringHom_ext hA (by rw [RingHom.comp_apply, hσ]; exact hτ)

theorem exists_map (F : FamilyUnif Xo σ ty) (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ) (hτ : τ H.rt0 = H.rt0) :
    ∃ π : Fin F.n → Fin F.n, ConjugationPermutesPeriods F τ π := by
  classical
  choose P0 hP0 using fun i => exists_period F hty i
  choose k Q hQ hkQ using fun i => F.18 _ (spMap_comp_u_comp_s_eq_of_fixes_rt0 F hσ hA τ hτ i (P0 i) (hP0 i))
  refine ⟨k, fun i P hP => ?_⟩
  obtain ⟨k', Q', hQ', hk'⟩ := F.18 _ (spMap_comp_u_comp_s_eq_of_fixes_rt0 F hσ hA τ hτ i P hP)
  have hkk := key_lemma' F hD hσ hty hA τ hτ i (k i) k' (P0 i) P (Q i) Q' (hP0 i) hP (hQ i) hQ'
    (hkQ i).symm hk'.symm
  subst hkk
  exact ⟨Q', hQ', hk'.symm⟩

theorem exists_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∃ π : Equiv.Perm (Fin F.n), ConjugationPermutesPeriods F τ π := by
  intro E _ _ _ H D l Xo σ g ty F hD hσ hty hA τ hτ
  obtain ⟨π, hπ⟩ := exists_map F hD hσ hty hA τ hτ
  have hτ' : τ.symm H.rt0 = H.rt0 := by
    rw [RingEquiv.symm_apply_eq]
    exact hτ.symm
  obtain ⟨π', hπ'⟩ := exists_map F hD hσ hty hA τ.symm hτ'
  have hinv : ∀ i, π' (π i) = i := by
    intro i
    obtain ⟨P, hP⟩ := exists_period F hty i
    obtain ⟨Q, hQ, h1⟩ := hπ i P hP
    obtain ⟨R, hR, h2⟩ := hπ' (π i) Q hQ
    have h3 : spMap (τ.symm : ℂ →+* ℂ) ≫ spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
      rw [← Category.assoc, spMap_comp]
      have hid : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := by
        ext z
        simp
      rw [hid]
      unfold spMap
      simp
    rw [h1, h2] at h3
    exact F.19 _ _ _ _ hR hP h3
  have hinj : Function.Injective π := fun a b hab => by rw [← hinv a, ← hinv b, hab]
  exact ⟨Equiv.ofBijective π hinj.bijective_of_finite, hπ⟩

end GlobalTheory.ConjPermutes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_framedPoint_move_universalTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), (∃ y' : FrPt Xo c S, FrMove ρ ν y y') ∧ ∀ y' y'' : FrPt Xo c S, ∀ ν' : SABMap Xo.univ.t Xo.univ.t ρ, ν'.φ = ν.φ → FrMove ρ ν y y' → FrMove ρ ν' y y'' → y' = y'' := by
  first | exact @GlobalTheory.exists_unique_frMove | exact GlobalTheory.exists_unique_frMove | (intros; apply GlobalTheory.exists_unique_frMove <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsWeightZeroSectionOfPeriodSpaceFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightZero_section_of_periodSpace_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), 1 ≤ D.p + D.q → (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → FnAlgClosed Xo c → ∀ v : Fin F.n → c.F, ∃ f ∈ sec Xo c 0 0, (∀ m : ℕ, (∀ i, v i ^ m = 1) → f ^ m = 1) ∧ ∀ (y : FrPt Xo c (CAt σ)) (i : Fin F.n) P, IsPeriod (F.Di i) ty P → y.x = F.u i P → Formalism.L2.PjFree.toC (evR Xo c f y) = σ (v i) := by
  first | exact @GlobalTheory.CompFun.exists_section_of_function | exact GlobalTheory.CompFun.exists_section_of_function | (intros; apply GlobalTheory.CompFun.exists_section_of_function <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedUniformisationComponentsPeriodSpacesBijectStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedUniformisation_components_periodSpaces_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) → (∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ), (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((U.un k x).u τ i)) → Function.Bijective ik := by
  first | exact @GlobalTheory.CompBij.ik_bijective | exact GlobalTheory.CompBij.ik_bijective | (intros; apply GlobalTheory.CompBij.ik_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelMoveModuliUniqueUniversalTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMove_moduli_unique_universalTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') (gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La), 1 ≤ Dw.p + Dw.q → (∀ a, gM a - gM' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA a - gA' a)) → IsIso ρ → IsIso ρ' → IsLevMove ρ ν gM gA → IsLevMove ρ' ν' gM' gA' → (∃ g : Sim Dw, (∀ a, g.f l.M a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ a, Dw.ModN l.A (g.f l.A a - gA a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) → ρ = ρ' ∧ ν.φ = ν'.φ := by
  first | exact @GlobalTheory.levMove_unique | exact GlobalTheory.levMove_unique | (intros; apply GlobalTheory.levMove_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingComponentUniqueFrameUniqueArithmeticGroupStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h, (∀ k k' γ γ', C.Mark h k γ → C.Mark h k' γ' → k = k') ∧ ∀ k γ γ', C.Mark h k γ → C.Mark h k γ' → ∃ δ ∈ (C.M.X k).Γ, C.fr (γ' * h) k = lact δ (C.fr (γ * h) k) := by
  first | exact @GlobalTheory.MarkUniq.mark_unique | exact GlobalTheory.MarkUniq.mark_unique | (intros; apply GlobalTheory.MarkUniq.mark_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointArithmeticGroupInvariantSigStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = 1 := by
  first | exact @GlobalTheory.FrameUnif.normUn_gamma | exact GlobalTheory.FrameUnif.normUn_gamma | (intros; apply GlobalTheory.FrameUnif.normUn_gamma <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRuleStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = bchar (laU (unfOf e F M un) a n k) b := by
  first | exact @GlobalTheory.NormUnBor.normUn_bor | exact GlobalTheory.NormUnBor.normUn_bor | (intros; apply GlobalTheory.NormUnBor.normUn_bor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_detect_frobenius_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), PtsDetect (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (ex Dw a n) := by
  first | exact @GlobalTheory.Frames.ptsDetect_framed | exact GlobalTheory.Frames.ptsDetect_framed | (intros; apply GlobalTheory.Frames.ptsDetect_framed <;> assumption)
end

