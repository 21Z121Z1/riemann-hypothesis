import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartEigenframe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModuliChart

theorem exists_sec_of_secOn {X X' S S' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {t : S' ⟶ S} {F : X' ⟶ X}
    (hF : IsPullback F p' p t) {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull F))
    {V : S.Opens} (hV : ∀ y, t y ∈ V) {θ : ∀ i, Γ(X, p ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (p ⁻¹ᵁ V))
    (hne : ∀ y ∈ V, ∃ (g : X) (i : L.ι), p g = y ∧ g ∈ X.basicOpen (θ i)) :
    ∃ th : L'.Sec, ∀ y : S', ∃ x : X', p' x = y ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨w, hw⟩ := hw
  have hFV : ∀ y : X', p (F y) ∈ V := fun y => by
    rw [← Scheme.Hom.comp_apply, hF.w, Scheme.Hom.comp_apply]; exact hV _
  have le : ∀ j, F ⁻¹ᵁ L.U j ≤ F ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ L.U j) := fun j y hy => ⟨hFV y, hy⟩
  have val : ∀ (y : X') j, F y ∈ L.U j → gs (𝟙 X') y _ ((F.appLE _ _ (le j)).hom (θ j)) =
      (F.stalkMap y).hom (gs (𝟙 X) (F y) _ (θ j)) := fun y j h => by
    rw [gs_appLE F _ _ (le j) (𝟙 X') y h, Category.id_comp, gs_stalkMap F y _ (le j h)]
  obtain ⟨th, hth⟩ := sec_down ((isGen_iff w).1 hw) hL hL' (fun j => (F.appLE _ _ (le j)).hom (θ j))
    fun y j j' h h' => by
      rw [val y j h, val y j' h', LBGerm.gs_secOn hθ (F y) j j' (hFV y) h h', map_mul]
      congr 1
      have := PushInv.gm_comp F (𝟙 X) y (L.U j ⊓ L.U j') ⟨h, h'⟩ (L.g j j')
      rw [Category.comp_id] at this
      exact this.symm
  refine ⟨th, fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hne (t y) (hV y)
  obtain ⟨x, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback hF g y hg
  obtain rfl : F x = g := h₁
  obtain ⟨k, hk⟩ := exists_chart hL' x
  have hm : F x ∈ p ⁻¹ᵁ V ⊓ L.U i := X.basicOpen_le _ hi
  refine ⟨x, h₂, (SectionBaseChange.mem_nonzeroLocus th _).2 ⟨k, hk, ?_⟩⟩
  have e := hth _ (𝟙 _) x i k hm.2 hk
  rw [val x i hm.2] at e
  have hu : IsUnit (gs (𝟙 X) (F x) _ (θ i)) := by
    rw [gs_eq (𝟙 X) (F x) _ hm]
    exact (X.mem_basicOpen _ _ hm).1 hi
  exact isUnit_of_mul_isUnit_right (e ▸ hu.map (F.stalkMap x).hom)

theorem exists_away_point {R : Type} [CommRing R] (p : PrimeSpectrum R) {r : R} (hr : r ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away r), spMap (algebraMap R (Localization.Away r)) q = p := by
  have h : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} (s' : S' ⟶ Sp B)
    (f : S' ⟶ S) (h : f ≫ s = s') (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o f) :=
  ObjPull.objPull_of_pol pol_pull E H D l B B b b (RingHom.id B) S S' s s' f rfl rfl
    (h.trans ((Category.comp_id _).symm.trans (congrArg (s' ≫ ·) (Spec.map_id _).symm))) o

theorem objMap_comp {B : Type} [CommRing B] {b : Base l B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    {s'' : S'' ⟶ Sp B} {o : Obj D l b s} {o' : Obj D l b s'} {o'' : Obj D l b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (m' : ObjMap o'' o' f') (m : ObjMap o' o f) : Nonempty (ObjMap o'' o (f' ≫ f)) := by
  obtain ⟨n, -⟩ := ((ObjMaps.id_comp_cancel E H D l B B B b b b S S' S'' s s' s'' o o' o'').2 f f' m).1 m'
  exact ⟨n⟩

theorem exists_eigen_chart (c : Coeff l) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H D.p D.q ty)
    {R : Type} [CommRing R] (j : c.F →+* R)
    (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (p : Sp R) :
    ∃ (R' : Type) (_ : CommRing R') (f : R →+* R')
      (o' : Obj D l (baseKA l) (spMap (f.comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom))
      (v : Fin g → (epsR R' ⟶ o'.t.G)), IsOpenImmersion (spMap f) ∧ p ∈ Set.range (spMap f) ∧
      Nonempty (ObjMap o' o (spMap f)) ∧ IsLieBasis v ∧
      ∀ i a, (v i ≫ o'.t.act.act a).left =
        spMap (epsScaleR (f.comp j ⟨ty i (a : E), c.conj (ty i) a⟩)) ≫ (v i).left := by
  obtain ⟨r, hr, v₀, hv₀⟩ := LieLoc.lie_locally_free R o.t.G _ (ObjDim.smoothOfRelativeDimension o) p
  obtain ⟨p₁, hp₁⟩ := exists_away_point p hr
  let R₁ := Localization.Away r
  let f₁ : R →+* R₁ := algebraMap R R₁
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull
    (spMap (f₁.comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (spMap f₁)
    (by rw [spMap_comp j f₁, Category.assoc]) o
  obtain ⟨e, he, -⟩ := grpPullback_iso m₁.cart (isGrpPullback_pullback o.t.G (spMap f₁))
  have hv₁ : IsLieBasis (fun i => v₀ i ≫ e.inv) := Chart.isLieBasis_iso e (by
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using hv₀)
  obtain ⟨r', hr', Hv⟩ := exists_isLieBasis_eigen E H D l c g ty hty R₁ (f₁.comp j) o₁ _ _ hv₁ p₁
  obtain ⟨p₂, hp₂⟩ := exists_away_point p₁ hr'
  let R₂ := Localization.Away r'
  let f₂ : R₁ →+* R₂ := algebraMap R₁ R₂
  obtain ⟨o₂, ⟨m₂⟩⟩ := exists_pull
    (spMap ((f₂.comp f₁).comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (spMap f₂)
    (by rw [RingHom.comp_assoc, spMap_comp (f₁.comp j) f₂, Category.assoc]) o₁
  obtain ⟨v, hv, hev⟩ := Hv o₂.t ⟨m₂.toSABMap⟩
  have i₁ : IsOpenImmersion (spMap f₁) := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))
  have i₂ : IsOpenImmersion (spMap f₂) := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away r')))))
  refine ⟨R₂, inferInstance, f₂.comp f₁, o₂, v, ?_, ?_, ?_, hv, hev⟩
  · rw [spMap_comp f₁ f₂]; infer_instance
  · refine ⟨p₂, ?_⟩
    rw [spMap_comp f₁ f₂]
    exact (congrArg (spMap f₁) hp₂).trans hp₁
  · rw [spMap_comp f₁ f₂]; exact objMap_comp m₂ m₁

theorem exists_chart_eigenframe : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∀ x : Xo.XF c, ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.F R) (jR : Sp R ⟶ Xo.XF c) (o : Obj D l (baseKA l) (spMap (algebraMap c.F R) ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (v : Fin g → (epsR R ⟶ o.t.G)) (th : o.t.PP.L.Sec), Algebra.FiniteType c.F R ∧ IsReduced R ∧ IsOpenImmersion jR ∧ x ∈ Set.range jR ∧ jR ≫ pullback.snd _ _ = spMap (algebraMap c.F R) ∧ Nonempty (ObjMap o Xo.univ (jR ≫ pullback.fst _ _)) ∧ IsLieBasis v ∧ (∀ i a, (v i ≫ o.t.act.act a).left = spMap (epsScaleR (algebraMap c.F R ⟨ty i (a : E), c.conj (ty i) a⟩)) ≫ (v i).left) ∧ (∀ y : Sp R, ∃ x : o.t.G.left, o.t.G.hom x = y ∧ x ∈ Out.nonzeroLocus th) ∧ (∀ s : o.t.PP.L.Sec, ∃! a : R, ∀ i, s.f i = constFn o.t.G.hom _ a * th.f i) := by
  intro hS E _ _ _ H D l Xo c g ty hty x
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  let π : Xo.XF c ⟶ Xo.X := pullback.fst _ _
  let σ : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  have hσ : Smooth σ := inferInstanceAs (Smooth (pullback.snd Xo.s _))
  have hred : AlgebraicGeometry.IsReduced (Xo.XF c) :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ σ hσ).1
  obtain ⟨V, hV, θ, hθ, -, hne⟩ := PushInv.pushInvertible hS Xo.X (Obj.toPolAV Xo.univ) (π x)
  obtain ⟨B, j₀, hj₀, ⟨p, hp⟩, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := Xo.XF c) (x := x) (U := π ⁻¹ᵁ V) hV
  let j : c.F →+* B := (Spec.preimage (j₀ ≫ σ)).hom
  have hj : j₀ ≫ σ = spMap j := (Spec.map_preimage (j₀ ≫ σ)).symm
  obtain ⟨o₀, ⟨m₀⟩⟩ := exists_pull (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (j₀ ≫ π)
    (by rw [← hj, Category.assoc, Category.assoc]; exact congrArg (j₀ ≫ ·) pullback.condition) Xo.univ
  obtain ⟨R, _, f, o, v, hf, ⟨q, hq⟩, ⟨m₁⟩, hv, hev⟩ := exists_eigen_chart c hty j o₀ p
  obtain ⟨m⟩ := objMap_comp m₁ m₀
  let jR : Sp R ⟶ Xo.XF c := spMap f ≫ j₀
  have hjR : IsOpenImmersion jR := IsOpenImmersion.comp (spMap f) j₀
  have hs : jR ≫ σ = spMap (f.comp j) := by
    rw [spMap_comp j f, ← hj]; exact Category.assoc _ _ _
  have hL : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨th, hth⟩ := exists_sec_of_secOn m.cart.1 Xo.univ.t.PP.isLB o.t.PP.isLB hL (V := V)
    (fun y => hsub ⟨spMap f y, rfl⟩) hθ hne
  letI : Algebra c.F R := (f.comp j).toAlgebra
  refine ⟨R, inferInstance, inferInstance, jR, o, v, th, ?_, ?_, hjR, ⟨q, ?_⟩, hs, ?_, hv, hev, hth,
    SectionBaseChange.generates hS (Obj.toPolAV Xo.univ) m.cart.1 o.t.PP.isLB hL th hth⟩
  · have h : LocallyOfFiniteType (spMap (f.comp j)) := by rw [← hs]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := CommRingCat.ofHom (f.comp j))).1 h
  · have h : AlgebraicGeometry.IsReduced (Sp R) := isReduced_of_isOpenImmersion jR
    exact (affine_isReduced_iff (CommRingCat.of R)).1 h
  · exact (congrArg j₀ hq).trans hp
  · have e : jR ≫ π = spMap f ≫ j₀ ≫ π := Category.assoc _ _ _
    exact (congrArg (fun u => Nonempty (ObjMap o Xo.univ u)) e).mpr ⟨m⟩

end GlobalTheory.ModuliChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmEndomorphism_comm_conjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∃ W : C.P.A ⟶ C.P.A, IsMonHom W ∧ (∀ z, C.pt z ≫ W.left = C.pt (wC H (0, 1) * z)) ∧ (∀ z z', C.pt z = C.pt z' ↔ ∃ a, z - z' = wC H a) ∧ (∀ x : Sp ℂ ⟶ C.P.A.left, x ≫ C.P.A.hom = 𝟙 _ → ∃ z, C.pt z = x) ∧ ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → W.left ≫ io = io ≫ W.left := by
  first | exact @GlobalTheory.CurveEndo.exists_endo_comm | exact GlobalTheory.CurveEndo.exists_endo_comm | (intros; apply GlobalTheory.CurveEndo.exists_endo_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalGeneratorStableBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_away_lift {X : Scheme.{0}} {S R : Type} [CommRing S] [CommRing R]
    (x : Spec (CommRingCat.of S) ⟶ X) (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (p : Spec (CommRingCat.of S)) (hp : x p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∃ φ : R →+* Localization.Away g,
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x =
        Spec.map (CommRingCat.ofHom φ) ≫ j := by
  have hopen : IsOpen ((fun q : PrimeSpectrum S => x q) ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage x.continuous
  obtain ⟨_, ⟨g, rfl⟩, hg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) hp hopen
  refine ⟨g, hg, ?_⟩
  have hr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x) ⊆
      Set.range j := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    apply hsub
    have : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) q ∈
        Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := ⟨q, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at this
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j _ hr)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_local_generator : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (p : Sp S), ∃ g : S, g ∉ p.asIdeal ∧ ∃ θ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x)), ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (x' : Sp T ⟶ Xo.X) (θ' : LB.Sec (PPx x')), x' = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x → SecBC ψ 1 _ x' θ θ' → SecGen x' θ' ∧ SecNZ x' θ' := by
  intro hB E _ _ _ H Dw l Xo S _ x p
  obtain ⟨R, _, _, j, θ₀, hj, hz, hnz⟩ := GlobalTheory.T.exists_local_section_nonzero_all_fibres_moduli hB E H Dw l Xo (x p)
  obtain ⟨g, hg, φ, hφ⟩ := exists_away_lift x j p hz
  have hφ' : spMap (algebraMap S (Localization.Away g)) ≫ x = spMap φ ≫ j := hφ
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo R (Localization.Away g) φ 1 j _ hφ' θ₀
  refine ⟨g, hg, θ, ?_⟩
  intro T _ ψ x' θ' hx' hbc
  have h1 : SecBC (ψ.comp φ) 1 j x' θ₀ θ' :=
    ((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo R (Localization.Away g) T φ ψ j _ x' hφ' hx').1 1 θ₀ θ θ' hθ).1 hbc
  have hx'' : x' = spMap (ψ.comp φ) ≫ j := by
    rw [hx', hφ', ← Category.assoc]
    congr 1
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)).symm
  exact ⟨GlobalTheory.T.fibreSectionGenerates_of_nowhereZero_noetherian_baseChange hB E H Dw l Xo R j θ₀ hnz T (ψ.comp φ) x' θ' hx'' h1,
    fun p' => (GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff E H Dw l Xo R T (ψ.comp φ) j x' hx'' θ₀ θ' h1 p').2 (hnz _)⟩

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSabMapOfGroupIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Exist.CubicalExtension

theorem exists_sabMap_of_groupIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (t t' : SAB H (Sp T)) (tK : SAB H (Sp K)) (m : SABMap tK t (spMap (algebraMap T K))) (m' : SABMap tK t' (spMap (algebraMap T K))) (ψ : t.G ≅ t'.G), IsMonHom ψ.hom → m.φ ≫ ψ.hom.left = m'.φ → (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) → ∃ n : SABMap t t' (𝟙 _), n.φ = ψ.hom.left :=
  sabMap_of_iso_of_extendGen GlobalTheory.Exist.extendGen

end GlobalTheory.Exist.CubicalExtension
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPt
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif.ThetaPtEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_chart_top {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ p ⁻¹ᵁ L.U j := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hL.cover.ge (Set.mem_univ (p (default : PrimeSpectrum ℂ))))
  refine ⟨j, fun q _ => ?_⟩
  obtain rfl : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hj

theorem exists_gen (hT : Out.SecTwistSt) (y : Sp ℂ ⟶ Xo.X) {Z : Type} (ex : Z → (Over.mk y ⟶ Xo.univ.t.G))
    (θ : Z → ℂ) (fr : Xo.univ.t.PP.L.ι → Z → ℂ) (κ : ℂ) (hκ : κ ≠ 0) (hθ : ∃ z, θ z ≠ 0)
    (hfr : ∀ j z, ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).Sec)
    (hs : ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom y),
        x ≫ pullback.fst _ _ = (ex z).left → x ≫ pullback.snd _ _ = 𝟙 _ →
        ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).U (fun _ => j))
          (s.f (fun _ => j)) = θ z * fr j z) :
    ∃ t : LB.Sec (PPx y), SecGen y t ∧
      ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (ex z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
        ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
        valAt' pt ((PPx y).U (fun _ => j)) (t.f (fun _ => j)) = κ * θ z * fr j z := by
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_fibreSection_other_model_same_values E H Dw l Xo y s
  have hw : ∀ z, (ex z).left ≫ Xo.univ.t.G.hom = 𝟙 (Sp ℂ) ≫ y := fun z =>
    (Over.w (ex z)).trans (Category.id_comp y).symm
  have key : ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (ex z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
      ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y).U (fun _ => j)) ((SecPull.scalSec y κ s').f (fun _ => j)) = κ * θ z * fr j z := by
    intro j z pt h1 h2 h3
    have e1 := (GlobalTheory.T.sec_values_complex_fibre_abelianScheme hT E H Dw l Xo y s').1 κ (fun _ => j) pt h2
    have e2 := hs' j pt (pullback.lift (ex z).left (𝟙 _) (hw z)) ((pullback.lift_fst _ _ _).trans h1.symm)
      (pullback.lift_snd _ _ _) h2
    have e3 := hs j z (pullback.lift (ex z).left (𝟙 _) (hw z)) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _) h3
    refine e1.trans ?_
    rw [e2, e3, mul_assoc]
  refine ⟨SecPull.scalSec y κ s', ?_, key⟩
  obtain ⟨z, hz⟩ := hθ
  obtain ⟨j, hj⟩ := exists_chart_top Xo.univ.t.PP.isLB (ex z).left
  let pt : Sp ℂ ⟶ Gx y := pullback.lift (f := (Over.mk y).hom) (g := Xo.univ.t.G.hom) (𝟙 _) (ex z).left (hw z).symm
  have h1 : pt ≫ gxFst y = (ex z).left := pullback.lift_snd _ _ _
  have h2 : pt ≫ gxSnd y = 𝟙 (Sp ℂ) := pullback.lift_fst _ _ _
  refine (GlobalTheory.T.sec_values_complex_fibre_abelianScheme hT E H Dw l Xo y _).2.1.2 ⟨fun _ => j, pt, h2, ?_⟩
  rw [key j z pt h1 h2 hj]
  exact mul_ne_zero (mul_ne_zero hκ hz) (hfr j z hj)

theorem exists_thetaPt : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ κ : ℂ, κ ≠ 0 → ∃ y : FrPt Xo c (CAt σ), IsThetaPt T b κ y := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb κ hκ
  have hP := T.isPer _ hb
  obtain ⟨u, hu, htan, heig, hbas⟩ := GlobalTheory.T.exists_tangent_eigenbasis_exponential E H Dw l Xo c σ g e F k _ hP
  obtain ⟨s, hs⟩ := T.fr_sec b hb
  obtain ⟨hdet, hsym, hpos, -⟩ := T.norm b hb
  obtain ⟨w, hw⟩ := ((GlobalTheory.T.thetaChar_half_differentiable_ne_zero_families g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos).2
  have hθ : ∃ z, thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) ≠ 0 :=
    ⟨(T.h b)⁻¹ *ᵥ w, by rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]⟩
  obtain ⟨t, ht, hval⟩ := exists_gen hT (F.u k (T.Pf (T.co b))) (F.ex k (T.Pf (T.co b)))
    (fun z => thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) (fun j z => T.fr j (b, z)) κ hκ hθ
    (fun j z hz => T.fr_ne j b z hb hz) s hs
  exact ⟨⟨F.u k (T.Pf (T.co b)), F.over_σ k _ hP, u, htan, heig, hbas, t, ht⟩, rfl, hu, hval⟩

end GlobalTheory.FrameUnif.ThetaPtEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_complex_comap_eq : ∀ (F : IntermediateField ℚ ℂ) (U : ValuationSubring F) (p : ℕ), (p : F) ∈ U.nonunits → ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ W.comap F.val.toRingHom = U := by
  first | exact @GlobalTheory.exists_valuationSubring_complex_comap_val_eq | exact GlobalTheory.exists_valuationSubring_complex_comap_val_eq | (intros; apply GlobalTheory.exists_valuationSubring_complex_comap_val_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalCuspSectionsVanishingOffDomainStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_cuspSections_vanishing_offDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (W : Submodule ℂ (FDSec X)), W ≤ holSub X la → (∀ P ∈ W, ∀ k, ∀ x ∉ (X k).dom, P k x = 0) → FiniteDimensional ℂ W := by
  first | exact @GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub | exact GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub | (intros; apply GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frames_differ_by_unit' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)) (ub₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G₂.G)), ((∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t.G.left, u' ≫ m₁.φ = y.u τ i ∧ u' ≫ m₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) → ((∀ τ i, IsTan (ub₂ τ i)) ∧ (∀ τ i, IsEigV c io G₂ τ (ub₂ τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G₂.G), IsTan w → IsEigV c io G₂ τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub₂ τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t₂.G.left, u' ≫ n₁.φ = y'.u τ i ∧ u' ≫ n₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub₂ τ i).left) → ∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧ ∀ i, IsCombAt y.x (y.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.u τ i) := by
  first | exact @GlobalTheory.IntLie.integral_frames_differ_by_unit | exact GlobalTheory.IntLie.integral_frames_differ_by_unit | (intros; apply GlobalTheory.IntLie.integral_frames_differ_by_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xoNumPt_of_p_add_q_pos : N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Formalism.L2.PjFree.XoNumPt Xo c := by
  first | exact @GlobalTheory.moduli_exists_numberField_point | exact GlobalTheory.moduli_exists_numberField_point | (intros; apply GlobalTheory.moduli_exists_numberField_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RecordAllSgZeroIff
section
noncomputable section

namespace GlobalTheory.RecBCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
  Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction

variable {D : D7} (T : Core D)

def cuEquiv {j : ℕ} (hj : InR D j) : T.Cu j ≃ Cusps T j where
  toFun cu := cu.1
  invFun cu := ⟨cu, hj⟩
  left_inv _ := rfl
  right_inv _ := rfl

def cuTo {j : ℕ} (cu : T.Cu j) : Cusps T j := cu.1

def fjIncl {j : ℕ} (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)) (w : WeightFamilies.Wt D j) :
    domSec T j (cuTo T cu) w →ₗ[T.Q.c.F] T.FJt j cu χ w :=
  Submodule.subtype _

variable {T} (h : LawsCore T)

def recCu {j : ℕ} (cu : (recB h).Cu j) : (record h).Cu j := cuTo T cu

end GlobalTheory.RecBCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsFrameRatioStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoints_frame_ratio : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ : ℂ) (t₀ : (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)), IsThetaPt T b κ y → IsThetaPt T b (toC (t₀ : CAt σ) * κ) y' → FrBor (fun i => Option.elim i t₀ (fun _ => 1)) y y' := by
  first | exact @GlobalTheory.frBor_of_isThetaPt | exact GlobalTheory.frBor_of_isThetaPt | (intros; apply GlobalTheory.frBor_of_isThetaPt <;> assumption)
end

