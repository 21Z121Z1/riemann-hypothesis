import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.UnitAtOfIsLineGenOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBoundEventuallyBounds

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

open GlobalTheory.HolHom

variable {R : Type} [CommRing R]

def cst {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem cst_apply {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) : cst p U a = constFn p U a := rfl

theorem valR_cst {C : Type} [CommRing C] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (θ : R →+* C)
    (y : Sp C ⟶ X) (hy : y ≫ p = spMap θ) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : R) : evalHom y U h (cst p U a) = θ a := by
  have e := GlobalTheory.TangentOrigin.evalPt_constFn p y U h a
  have e2 := GlobalTheory.TangentOrigin.evalPt_spMap θ a
  rw [hy] at e
  exact e.trans e2

theorem exists_pt {G : Over (Sp R)} {V : G.left.Opens} (hV : IsAffineOpen V) (θ : R →+* ℂ)
    (χ : Γ(G.left, V) →+* ℂ) (hχ : ∀ r, χ (cst G.hom V r) = θ r) :
    ∃ x : Over.mk (spMap θ) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V ∧ ∀ a, valAt' x.left V a = χ a := by
  obtain ⟨y, hy, he⟩ := GlobalTheory.TangentOrigin.exists_evalPt_eq hV χ
  have hy' : y ≫ G.hom = spMap θ := GlobalTheory.TangentOrigin.eq_spMap_of_evalPt _ θ (fun a => by
    rw [← GlobalTheory.TangentOrigin.evalPt_constFn G.hom y V hy a, he]; exact hχ a)
  refine ⟨Over.homMk y hy', hy, fun a => ?_⟩
  show valAt' y V a = χ a
  rw [GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ hy, he]

theorem val_cst {G : Over (Sp R)} (V : G.left.Opens) {θ : R →+* ℂ} (x : Over.mk (spMap θ) ⟶ G)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (r : R) : valAt' x.left V (cst G.hom V r) = θ r :=
  (GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ hx _).trans (valR_cst G.hom V θ x.left (Over.w x) hx r)

theorem pt_ext {G : Over (Sp R)} {V : G.left.Opens} (hV : IsAffineOpen V) {θ : R →+* ℂ}
    {x y : Over.mk (spMap θ) ⟶ G} (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V)
    (h : ∀ a, valAt' x.left V a = valAt' y.left V a) : x = y :=
  Over.OverMorphism.ext (point_ext hV hx hy h)

theorem tan_der {X : Scheme.{0}} {x : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) {V : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ D : Γ(X, V) →+ ℂ, (∀ f, D f = TrivSqZeroExt.snd (valR v V f)) ∧
      ∀ f f', D (f * f') = valAt' x V f * D f' + valAt' x V f' * D f := by
  have hv := (le_preimage_dual_iff h V).2 hx
  refine ⟨AddMonoidHom.mk' (fun f => TrivSqZeroExt.snd (valR v V f)) fun a b => ?_, fun _ => rfl, fun f f' => ?_⟩
  · simp only [valR_eq _ _ hv, map_add, TrivSqZeroExt.snd_add]
  · have e1 := fst_valR h hx f
    have e2 := fst_valR h hx f'
    simp only [AddMonoidHom.mk'_apply]
    rw [← e1, ← e2]
    simp only [valR_eq _ _ hv, map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

theorem one_left_spMap {G : Over (Sp R)} [GrpObj G] (θ : R →+* ℂ) :
    (1 : Over.mk (spMap θ) ⟶ G).left = spMap θ ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left := by
  have e : (Over.homMk (spMap θ) (by simp) : Over.mk (spMap θ) ⟶ Over.mk (𝟙 (Sp R))) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  exact (congrArg (fun q => Over.Hom.left q) e).symm

theorem tan_base {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 (Sp R)) E) (θ : R →+* ℂ) (w : E) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (dualMap θ) ≫ (M.pt w).left) =
      (1 : Over.mk (spMap θ) ⟶ G).left := by
  rw [one_left_spMap, ← M.tan w, ← Category.assoc, ← Category.assoc]
  congr 1
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  show TrivSqZeroExt.fst (dualMap θ x) = θ (TrivSqZeroExt.fst x)
  simp [dualMap]

theorem tan_over {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 (Sp R)) E) (θ : R →+* ℂ) (w : E) :
    (spMap (dualMap θ) ≫ (M.pt w).left) ≫ G.hom = spMap ((algebraMap ℂ (DualNumber ℂ)).comp θ) := by
  have e : (M.pt w).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) := Over.w (M.pt w)
  rw [Category.assoc, e, Category.comp_id]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairFramesOnSet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator

theorem exists_ιMulti_eq_smul {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {v b : Fin r → E} (h : ∀ i, v i ∈ Submodule.span Ω (Set.range b)) :
    ∃ α : Ω, exteriorPower.ιMulti Ω r v = α • exteriorPower.ιMulti Ω r b := by
  classical
  have hc : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • b j = v i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (h i)
  choose c hc using hc
  have hv : v = fun i => ∑ j, c i j • b j := funext fun i => (hc i).symm
  have hsum : exteriorPower.ιMulti Ω r v =
      ∑ f : Fin r → Fin r, (∏ i, c i (f i)) • exteriorPower.ιMulti Ω r (fun i => b (f i)) := by
    rw [hv]
    refine ((exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_sum
      (fun i j => c i j • b j)).trans (Finset.sum_congr rfl fun f _ => ?_)
    exact (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_smul_univ
      (fun i => c i (f i)) (fun i => b (f i))
  have hmem : exteriorPower.ιMulti Ω r v ∈ Submodule.span Ω {exteriorPower.ιMulti Ω r b} := by
    rw [hsum]
    refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
    by_cases hf : Function.Injective f
    · let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
      have h5 : (fun i => b (f i)) = b ∘ σ := rfl
      rw [h5, (exteriorPower.ιMulti Ω r (M := E)).map_perm b σ]
      have hm := Submodule.mem_span_singleton_self (R := Ω) (exteriorPower.ιMulti Ω r b)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
        exact hm
      · rw [hs, Units.neg_smul, one_smul]
        exact neg_mem hm
    · have h6 : ¬ Function.Injective (fun i => b (f i)) := fun hh =>
        hf (Function.Injective.of_comp (f := b) hh)
      rw [(exteriorPower.ιMulti Ω r (M := E)).map_eq_zero_of_not_injective _ h6]
      exact zero_mem _
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨α, hα.symm⟩

theorem frame_mem_of_isVBOn {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} {v : Fin r → E} {x : Cpt ξ} (hx : x ∈ T) (hL : L.IsVBOn T r V)
    (hv : L.IsFrameAt v x) (i : Fin r) : v i ∈ V := by
  obtain ⟨U, hU, e, he, hfr⟩ := hL x hx
  have h1 : v i ∈ L x := hv.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  rw [(hfr x hx hU).2] at h1
  have h2 : Submodule.span (regAt ξ x) (Set.range e) ≤
      (Submodule.span Ω (Set.range e)).restrictScalars (regAt ξ x) :=
    Submodule.span_le.2 fun _ hy => Submodule.subset_span hy
  exact he ▸ h2 h1

theorem exists_wedge_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} {v b : Fin r → E} {x : Cpt ξ} (hx : x ∈ T) (hL : L.IsVBOn T r V)
    (hb : Submodule.span Ω (Set.range b) = V) (hv : L.IsFrameAt v x) :
    ∃ α : Ω, α ≠ 0 ∧ exteriorPower.ιMulti Ω r v = α • exteriorPower.ιMulti Ω r b := by
  obtain ⟨α, hα⟩ := exists_ιMulti_eq_smul (v := v) (b := b)
    fun i => hb ▸ frame_mem_of_isVBOn hx hL hv i
  refine ⟨α, ?_, hα⟩
  rintro rfl
  exact GenModel.ιMulti_ne_zero hv.1 (by rw [hα, zero_smul])

theorem isGenAt_div : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (Vp Vq : Submodule Ω V) (T : Set (Cpt ξ)) (b₁ v₁ : Fin p → V) (b₂ v₂ : Fin q → V) (x : Cpt ξ), x ∈ T → A.IsVBOn T p Vp → B.IsVBOn T q Vq → LinearIndependent Ω b₁ → Submodule.span Ω (Set.range b₁) = Vp → LinearIndependent Ω b₂ → Submodule.span Ω (Set.range b₂) = Vq → A.IsFrameAt v₁ x → B.IsFrameAt v₂ x → ∃ α κ : Ω, α ≠ 0 ∧ κ ≠ 0 ∧ exteriorPower.ιMulti Ω p v₁ = α • exteriorPower.ιMulti Ω p b₁ ∧ exteriorPower.ιMulti Ω q v₂ = κ • exteriorPower.ιMulti Ω q b₂ ∧ (lineLat A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂)).IsGenAt x (α / κ) := by
  intro X Ω _ ξ V _ _ A B p q Vp Vq T b₁ v₁ b₂ v₂ x hx hA hB hb₁ hs₁ hb₂ hs₂ hv₁ hv₂
  obtain ⟨α, hα, e₁⟩ := exists_wedge_coeff hx hA hs₁ hv₁
  obtain ⟨κ, hκ, e₂⟩ := exists_wedge_coeff hx hB hs₂ hv₂
  have hco : IsCoeffAt A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂) x (κ / α) :=
    ⟨α, κ, hα, hκ, by rw [GenModel.wedge_of_frame hv₁, e₁], by rw [GenModel.wedge_of_frame hv₂, e₂],
      div_mul_cancel₀ _ hα⟩
  have key := GlobalTheory.T.wedge_line_lattice_vector_bundle X Ω ξ V A B p q Vp Vq T _ _ hA hB (GenModel.ιMulti_ne_zero hb₁)
    (GenModel.ιMulti_ne_zero hb₂) ⟨x, hx, _, hco⟩
  exact ⟨α, κ, hα, hκ, e₁, e₂, key.2.2 x hx v₁ v₂ α κ hv₁ hv₂ e₁ e₂⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.EigDir

open GlobalTheory.HolHom GlobalTheory.DerivEig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σK : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem isComb_iff_isCombAt (x : Sp ℂ ⟶ Xo.X) {n : ℕ} (c : Fin n → ℂ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (w : epsAt x ⟶ Xo.univ.t.G) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsComb c v w ↔ Formalism.L2.Pj.IsCombAt x (fun i => (v i).left) c w.left := by
  constructor
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, hu, by rw [hw]⟩
  · rintro ⟨u, hu, hw⟩
    exact ⟨u, hu, Over.OverMorphism.ext hw.symm⟩

theorem isTanAt_of_isEigVec (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (v : epsAt x ⟶ Xo.univ.t.G)
    (h : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act x χ v) : Formalism.L2.Pj.IsTanAt x v.left :=
  ⟨Over.w v, h.1⟩

theorem isEigVec_of_isDerivAt0 (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (FU.Di i) ty P) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (hχ : ∀ a : 𝓞 E, χ a = τ (a : E))
    (w : Fin g → ℂ) (hw : ∀ k, w k ≠ 0 → ty k = τ) (v : epsAt (FU.u i P) ⟶ Xo.univ.t.G)
    (hv : IsDerivAt0 (fun z => (FU.ex i P z).left) w v.left) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ v := by
  obtain ⟨h1, -, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo σK g ty FU i P hP
  have hhol : HolAt (fun z => (FU.ex i P z).left) 0 := holAt_of_isHolTo (isHolTo_ex FU i hP) (Set.mem_univ 0)
  have hv' := (isDerivAt0_iff _ _ _).1 hv
  refine ⟨(h1 _ _ hv).2, fun a => ?_⟩
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
    ContinuousLinearMap.pi fun k => ty k (a : E) • ContinuousLinearMap.proj k
  have e1 := hv'.comp (Xo.univ.t.act.act a).left
  have e2 : (fun t => (FU.ex i P t).left ≫ (Xo.univ.t.act.act a).left) = fun t => (FU.ex i P (L t)).left := by
    funext t
    rw [← Over.comp_left, ← FU.ex_lin i P hP a t]
    rfl
  rw [e2] at e1
  have e3 := isDerivAt_of_comp_linear hhol L e1
  have e4 : L w = χ a • w := by
    funext k
    by_cases hk : w k = 0
    · simp [L, hk]
    · simp [L, hw k hk, hχ a]
  rw [e4] at e3
  exact e3.unique (isDerivAt_epsMul hv' _)

end GlobalTheory.CompanionTheory.Ar.Flat.EigDir

open GlobalTheory.CompanionTheory.Ar.Flat.EigDir in

theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σK : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (n : ℕ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)), IsPeriod (FU.Di i) ty P → x = FU.u i P → (∀ a : 𝓞 E, χ a = τ (a : E)) → IsEigFrame Xo.univ.t.act x χ v → ∃ V : Fin n → Fin g → ℂ, (∀ a u, IsDerivAt0 (fun z => (FU.ex i P z).left) u (v a).left ↔ u = V a) ∧ LinearIndependent ℂ V ∧ ∀ z, tyPart ty τ z ∈ Submodule.span ℂ (Set.range V) := by
  intro E _ _ _ H D l Xo σK g ty FU i P x χ τ n v hP hx hχ hF
  subst hx
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo σK g ty FU i P hP
  have ht : ∀ a, Formalism.L2.Pj.IsTanAt (FU.u i P) (v a).left := fun a => isTanAt_of_isEigVec _ χ _ (hF.1 a)
  choose V hV hVu using fun a => h3 _ (ht a)
  have comb : ∀ (c : Fin n → ℂ) (w : epsAt (FU.u i P) ⟶ Xo.univ.t.G),
      GlobalTheory.CompanionTheory.Ar.Fl.IsComb c v w ↔ IsDerivAt0 (fun z => (FU.ex i P z).left) (∑ k, c k • V k) w.left := fun c w =>
    (isComb_iff_isCombAt _ c v w).trans
      (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H D l Xo σK g ty FU i P hP n (fun k => (v k).left) V hV c w.left)
  refine ⟨V, fun a u => ⟨fun h => hVu a u h, fun h => h ▸ hV a⟩, ?_, fun z => ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    obtain ⟨w, hw, -⟩ := (FU.ex_diff i P hP).1 0
    have hw' : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ w :=
      isEigVec_of_isDerivAt0 FU i P hP χ τ hχ 0 (fun k hk => absurd rfl hk) w hw
    obtain ⟨c₀, -, hu⟩ := hF.2 w hw'
    have a1 := hu c ((comb c w).2 (by rw [hc]; exact hw))
    have a2 := hu 0 ((comb 0 w).2 (by simpa using hw))
    intro k
    exact congrFun (a1.trans a2.symm) k
  · obtain ⟨w, hw, -⟩ := (FU.ex_diff i P hP).1 (tyPart ty τ z)
    have hw' : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec Xo.univ.t.act (FU.u i P) χ w :=
      isEigVec_of_isDerivAt0 FU i P hP χ τ hχ _ (fun k hk => ?_) w hw
    · obtain ⟨c, hc, -⟩ := hF.2 w hw'
      have e := (h3 _ (isTanAt_of_isEigVec _ χ _ hw')).unique ((comb c w).1 hc) hw
      rw [← e]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · by_contra hne
      exact hk (by simp [tyPart, hne])
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramComparisonBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem logBound_term_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : 0 ≤ Real.log (1 / x ^ 2) := by
  rcases h0.eq_or_lt with h | h
  · subst h
    simp
  · apply Real.log_nonneg
    rw [le_div_iff₀ (pow_pos h 2), _root_.one_mul]
    nlinarith

theorem uncentre_recentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) :
    uncentre t₀ ρ π (recentre t₀ ρ π u) = u := by
  funext i
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  simp only [uncentre, recentre, Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
    Equiv.apply_symm_apply, add_sub_cancel_left]
  rw [← _root_.mul_assoc, inv_mul_cancel₀ hρ', _root_.one_mul]

theorem lipschitz_uncentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) :
    LipschitzWith (Real.toNNReal ρ⁻¹) (uncentre t₀ ρ π) := by
  refine LipschitzWith.of_dist_le_mul fun t s => ?_
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le)]
  refine (dist_pi_le_iff (mul_nonneg (inv_nonneg.mpr hρ.le) dist_nonneg)).2 fun i => ?_
  simp only [uncentre, dist_eq_norm]
  rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le,
    sub_sub_sub_cancel_right]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (t - s) (π.symm i)) (inv_nonneg.mpr hρ.le)

theorem norm_fderiv_comp_uncentre {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : (Fin n → ℂ) → E) (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    ‖fderiv ℝ (fun t' => G (uncentre t₀ ρ π t')) t‖ ≤ ‖fderiv ℝ G (uncentre t₀ ρ π t)‖ * ρ⁻¹ := by
  have hdu : Differentiable ℝ (uncentre t₀ ρ π) := by
    unfold uncentre
    fun_prop
  by_cases hG : DifferentiableAt ℝ G (uncentre t₀ ρ π t)
  · rw [show (fun t' => G (uncentre t₀ ρ π t')) = G ∘ uncentre t₀ ρ π from rfl, fderiv_comp t hG (hdu t)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := t) (lipschitz_uncentre t₀ hρ π)
    rwa [Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le)] at h
  · have hnd : ¬ DifferentiableAt ℝ (fun t' => G (uncentre t₀ ρ π t')) t := by
      intro h
      apply hG
      have hdr : Differentiable ℝ (recentre t₀ ρ π) := by
        unfold recentre
        fun_prop
      have h' : DifferentiableAt ℝ (fun t' => G (uncentre t₀ ρ π t'))
          (recentre t₀ ρ π (uncentre t₀ ρ π t)) := by
        rw [recentre_uncentre t₀ hρ π t]
        exact h
      have h2 := h'.comp (uncentre t₀ ρ π t) (hdr _)
      have he : ((fun t' => G (uncentre t₀ ρ π t')) ∘ recentre t₀ ρ π) = G := by
        funext u
        simp only [Function.comp_apply, uncentre_recentre t₀ hρ π u]
      rwa [he] at h2
    rw [fderiv_zero_of_not_differentiableAt hnd, norm_zero]
    exact mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hρ.le)

theorem logBound_weight_le {n a₀ a : ℕ} {t₀ t : Fin n → ℂ} {π : Equiv.Perm (Fin n)} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hπ : ∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a ∧ t₀ (π.symm i) = 0) (ht : ‖t‖ < 1)
    (hu : ∀ i : Fin n, (i : ℕ) < a₀ → uncentre t₀ ρ π t i ≠ 0) :
    (∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) ≤
      ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0 := by
  have hf : ∀ j : Fin n, 0 ≤ Real.log (1 / ‖t j‖ ^ 2) := fun j =>
    logBound_term_nonneg (norm_nonneg _) (lt_of_le_of_lt (norm_le_pi_norm t j) ht)
  calc (∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0)
      ≤ ∑ i : Fin n, if ((π.symm i : Fin n) : ℕ) < a then Real.log (1 / ‖t (π.symm i)‖ ^ 2) else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with h1 h2 h2
        · have hj := hπ i h1
          have hne := hu i h1
          have hx : ‖uncentre t₀ ρ π t i‖ = ρ⁻¹ * ‖t (π.symm i)‖ := by
            simp only [uncentre, hj.2, sub_zero, norm_mul, norm_inv, Complex.norm_real,
              Real.norm_of_nonneg hρ.le]
          have htpos : 0 < ‖t (π.symm i)‖ := by
            refine lt_of_le_of_ne (norm_nonneg _) (Ne.symm ?_)
            intro h0
            apply hne
            rw [← norm_eq_zero, hx, h0, mul_zero]
          have hρi : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ).mpr hρ1
          rw [hx]
          apply Real.log_le_log (one_div_pos.mpr (pow_pos (mul_pos (inv_pos.mpr hρ) htpos) 2))
          apply one_div_le_one_div_of_le (pow_pos htpos 2)
          exact pow_le_pow_left₀ (norm_nonneg _) (le_mul_of_one_le_left (norm_nonneg _) hρi) 2
        · exact absurd (hπ i h1).1 h2
        · exact hf _
        · exact le_rfl
    _ = ∑ j : Fin n, if (j : ℕ) < a then Real.log (1 / ‖t j‖ ^ 2) else 0 :=
        Equiv.sum_comp π.symm (fun j => if (j : ℕ) < a then Real.log (1 / ‖t j‖ ^ 2) else 0)

theorem logBound_recentred : ∀ (n a₀ g r a : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) → (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a ∧ t₀ (π.symm i) = 0) → ∃ ε c C : ℝ, 0 < ε ∧ ε ≤ ρ ∧ 0 < c ∧ 0 < C ∧ ∀ t : Fin n → ℂ, ‖t - t₀‖ < ε → ‖t‖ < 1 → HodgeMetric.uncentre t₀ ρ π t ∈ Flat.punct n a₀ 1 → ((HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹ - (c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef ∧ (((C * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹).PosSemidef ∧ ∀ p q, ‖fderiv ℝ (fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') p q) t‖ ≤ C * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) := by
  intro n a₀ g r a Λ _ L U t₀ π ρ hρ hρ1 hU hli hπ
  obtain ⟨ρ', c, C', hρ', hc, hC', hb⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cusp.logBound_subframe n a₀ g r Λ L U (periodGram L U) hU hli (fun z i j => rfl)
  refine ⟨min ρ (ρ * ρ'), c, C' / ρ, lt_min hρ (mul_pos hρ hρ'), min_le_left _ _, hc, div_pos hC' hρ, ?_⟩
  intro t htε ht hpun
  have hzb : uncentre t₀ ρ π t ∈ Flat.punct n a₀ ρ' := by
    refine ⟨?_, hpun.2⟩
    have h1 := (lipschitz_uncentre t₀ hρ π).dist_le_mul t t₀
    rw [uncentre_self, Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le), dist_eq_norm t t₀] at h1
    have h2 : ‖t - t₀‖ < ρ * ρ' := lt_of_lt_of_le htε (min_le_right _ _)
    rw [Metric.mem_ball]
    calc dist (uncentre t₀ ρ π t) 0 ≤ ρ⁻¹ * ‖t - t₀‖ := h1
      _ < ρ⁻¹ * (ρ * ρ') := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hρ)
      _ = ρ' := by rw [← _root_.mul_assoc, inv_mul_cancel₀ hρ.ne', _root_.one_mul]
  obtain ⟨b1, b2, b3⟩ := hb _ hzb
  have hle := logBound_weight_le hρ hρ1 hπ ht hpun.2
  have hX'0 : 0 ≤ (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) := by
    refine add_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun i _ => ?_)
    split_ifs
    · exact logBound_term_nonneg (norm_nonneg _) (lt_of_le_of_lt (norm_le_pi_norm t i) ht)
    · exact le_rfl
  have hS : (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) ≤ (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) := by linarith
  have hCρ : C' ≤ C' / ρ := le_div_self hC'.le hρ hρ1
  have hCC : C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) ≤ C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) :=
    (mul_le_mul_of_nonneg_left hS hC'.le).trans (mul_le_mul_of_nonneg_right hCρ hX'0)
  refine ⟨b1, ?_, ?_⟩
  · have hd : 0 ≤ C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) - C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) := by linarith
    have hsplit : (((C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) : ℝ)) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹ =
        ((((C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) : ℝ)) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹) +
          (((C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) - C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) : ℝ)) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [Complex.ofReal_sub, sub_smul]
      abel
    rw [hsplit]
    exact b2.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hd))
  · intro p q
    calc ‖fderiv ℝ (fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') p q) t‖
        ≤ ‖fderiv ℝ (fun w => periodGram L U w p q) (uncentre t₀ ρ π t)‖ * ρ⁻¹ :=
          norm_fderiv_comp_uncentre (fun w => periodGram L U w p q) t₀ hρ π t
      _ ≤ C' * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) / 2) * ρ⁻¹ :=
          mul_le_mul_of_nonneg_right (b3 p q) (inv_nonneg.mpr hρ.le)
      _ = C' * ρ⁻¹ * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) / 2) := by ring
      _ ≤ C' * ρ⁻¹ * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
            (mul_nonneg hC'.le (inv_nonneg.mpr hρ.le))
      _ = C' / ρ * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) := by ring

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem FamExp.per_discrete : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), ∀ b ∈ B, ∃ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b ∧ DiscreteTopology Γ₀ ∧ Module.Finite ℤ Γ₀ ∧ Module.Free ℤ Γ₀ := by
  intro R _ G _ _ g n M B ψ e b hb
  have h0 : e.ex b 0 = 1 := by
    have h := e.add b hb 0 0
    rw [add_zero] at h
    exact (left_eq_mul.mp h)
  let A : AddSubgroup (Fin g → ℂ) :=
    { carrier := e.per b
      zero_mem' := h0
      add_mem' := by
        intro z w hz hw
        have hz' : e.ex b z = 1 := hz
        have hw' : e.ex b w = 1 := hw
        show e.ex b (z + w) = 1
        rw [e.add b hb, hz', hw', _root_.one_mul]
      neg_mem' := by
        intro z hz
        have hz' : e.ex b z = 1 := hz
        show e.ex b (-z) = 1
        have h := e.add b hb z (-z)
        rw [add_neg_cancel, h0, hz', _root_.one_mul] at h
        exact h.symm }
  let Γ₀ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule A
  obtain ⟨V, N, f, L, -, -, hL, -⟩ := e.log b hb
  have hslice : ∀ᶠ z : Fin g → ℂ in 𝓝 0,
      L (b, fun j => valAt' (e.ex b z).left V (f j)) = z := by
    have hc : Tendsto (fun z : Fin g → ℂ => (b, z)) (𝓝 0) (𝓝 (b, 0)) :=
      (Continuous.prodMk_right b).tendsto 0
    exact hc.eventually hL
  have hiso : ∀ᶠ z : Fin g → ℂ in 𝓝 0, z ∈ e.per b → z = 0 := by
    have h00 := hslice.self_of_nhds
    filter_upwards [hslice] with z hz hper
    have hz' : e.ex b z = e.ex b 0 := by
      have : e.ex b z = 1 := hper
      rw [this, h0]
    rw [hz'] at hz
    exact hz.symm.trans h00
  have hdisc : DiscreteTopology Γ₀ := by
    obtain ⟨U, hU, hUo, h0U⟩ := _root_.eventually_nhds_iff.mp hiso
    apply discreteTopology_of_isOpen_singleton_zero
    have : ({0} : Set Γ₀) = Subtype.val ⁻¹' U := by
      ext ⟨z, hz⟩
      constructor
      · intro h
        have : z = 0 := congrArg Subtype.val h
        simpa [this] using h0U
      · intro h
        have : z = 0 := hU z h hz
        exact Subtype.ext this
    rw [this]
    exact hUo.preimage continuous_subtype_val
  refine ⟨Γ₀, rfl, hdisc, ?_, ?_⟩
  · exact instModuleFinite_of_discrete_submodule Γ₀
  · exact instModuleFree_of_discrete_submodule Γ₀

end GlobalTheory.CompanionTheory.Ar.Flat
end

