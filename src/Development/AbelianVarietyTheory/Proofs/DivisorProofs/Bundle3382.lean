import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

def VS {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y) (x : Sp Ω ⟶ Y)
    (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k : ℕ) (s : FractionRing Ω) : Prop :=
  ∃ (r : R) (σ : SecM (𝟙 Y) L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) L x g k σ ω ∧
    (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * s

theorem VS.half {R Ω : Type} [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}}
    {L : LB Y} {x : Sp Ω ⟶ Y} {g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)} {k : ℕ} {s : FractionRing Ω}
    (h : VS φ L x g k (2 * s)) : VS φ L x g k s := by
  haveI : CharZero R := algebraRat.charZero R
  obtain ⟨r, σ, ω, hr, hv, he⟩ := h
  refine ⟨2 * r, σ, ω, mul_ne_zero two_ne_zero hr, hv, ?_⟩
  rw [he, map_mul, map_mul, map_ofNat, map_ofNat]
  ring

theorem ringOp_sub {Ω : Type} [CommRing Ω] {n : ℕ} (d₁ d₂ : Ω → Ω) (dd : Fin n → Ω → Ω)
    (Θ₁ Θ₂ : Matrix (Fin n) (Fin n) Ω) (u₁ u₂ : Fin n → Ω) (p₁ p₁' p₂ p₂' : Ω) (k : ℕ) (f : Ω) :
    ringOp d₁ dd Θ₁ u₁ p₁ p₁' k f - ringOp d₂ dd Θ₂ u₂ p₂ p₂' k f =
      ringOp (fun y => d₁ y - d₂ y) dd (Θ₁ - Θ₂) (u₁ - u₂) (p₁ - p₂) (p₁' - p₂') k f := by
  simp only [ringOp, Matrix.sub_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem bracket {Ω : Type} [CommRing Ω] {n : ℕ} (d : Ω → Ω) (dd : Fin n → Ω → Ω)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (hl : ∀ a x y, dd a (x * y) = x * dd a y + y * dd a x)
    (ha : ∀ a x y, dd a (x + y) = dd a x + dd a y)
    (Θ : Matrix (Fin n) (Fin n) Ω) (hΘ : Θᵀ = Θ) (u : Fin n → Ω) (p p' : Ω) (k : ℕ) (b c : Ω) :
    b * (ringOp d dd Θ u p p' (k + k) (b * c) - b * ringOp d dd Θ u p p' k c -
        c * ringOp d dd Θ u p p' k b) -
      c * (ringOp d dd Θ u p p' (k + k) (b * b) - b * ringOp d dd Θ u p p' k b -
        b * ringOp d dd Θ u p p' k b) =
      2 * ((k : Ω) * b * (b * d c - c * d b) - ∑ a, ∑ e, Θ a e * dd a b * (b * dd e c - c * dd e b)) := by
  have sym : ∀ a e, Θ e a = Θ a e := fun a e => by
    have := congrFun (congrFun hΘ a) e
    simpa [Matrix.transpose_apply] using this
  have swap : ∑ a, ∑ e, Θ a e * (dd a c * dd e b) = ∑ a, ∑ e, Θ a e * (dd a b * dd e c) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [sym]; ring
  have s2 : ∀ f h : Ω, ∑ a, ∑ e, Θ a e * dd a (dd e (f * h)) =
      f * ∑ a, ∑ e, Θ a e * dd a (dd e h) + h * ∑ a, ∑ e, Θ a e * dd a (dd e f) +
        (∑ a, ∑ e, Θ a e * (dd a f * dd e h) + ∑ a, ∑ e, Θ a e * (dd a h * dd e f)) := by
    intro f h
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [hl, ha, hl, hl]
    ring
  have s1 : ∀ f h : Ω, ∑ a, u a * dd a (f * h) = f * ∑ a, u a * dd a h + h * ∑ a, u a * dd a f := by
    intro f h
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hl]
    ring
  have swap' : ∑ a, ∑ e, Θ a e * (dd a b * dd e c) - ∑ a, ∑ e, Θ a e * (dd a c * dd e b) = 0 := by
    rw [swap]; ring
  have t1 : ∑ a, ∑ e, Θ a e * dd a b * (b * dd e c - c * dd e b) =
      b * ∑ a, ∑ e, Θ a e * (dd a b * dd e c) - c * ∑ a, ∑ e, Θ a e * (dd a b * dd e b) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  simp only [ringOp]
  rw [s2, s2, s1, s1, t1, hd, hd]
  push_cast
  linear_combination b * swap'

end GlobalTheory.HeatSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueInFrameLinearCombination
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem sval_smul_add_smul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s t : LB.Sec (LB.LinComb L φ ε)) (a b : Γ(Y, ⊤)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (a • s + b • t) r z J = gs r z ⊤ a * sval s r z J + gs r z ⊤ b * sval t r z J := by
  have hm := hJ.mem φ r
  exact (gs_add r z _ hm _ _).trans (congrArg₂ (· + ·)
    ((gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a)))
    ((gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm b))))

theorem gs_base_fn {R Ω : Type} [CommRing R] [CommRing Ω] {Y Z : Scheme.{0}} (p : Y ⟶ Sp R) (φ : R →+* Ω)
    (x : Sp Ω ⟶ Y) (h : x ≫ p = spMap φ) (r : Z ⟶ Sp Ω) (z : Z) (a : R) :
    gs (r ≫ x) z ⊤ (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) =
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (φ a)) := by
  have e₁ := gs_pull (r ≫ x) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  have e₂ := gs_pull r (spMap φ) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  rw [Category.assoc, h] at e₁
  refine e₁.trans (e₂.symm.trans (congrArg (gs r z ⊤) ?_))
  exact (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem exists_isValue_lin : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (g : GlobalTheory.RayEv.Transport.Frame L (x' ≫ 𝟙 G.left)) (k : ℕ) (σ₁ σ₂ : SecM (𝟙 G.left) L k) (ω₁ ω₂ : Ω) (a b : R), IsValue (𝟙 _) L x' g k σ₁ ω₁ → IsValue (𝟙 _) L x' g k σ₂ ω₂ → ∃ σ : SecM (𝟙 G.left) L k, IsValue (𝟙 _) L x' g k σ (φ a * ω₁ + φ b * ω₂) := by
  intro R _ G L Ω _ φ x' h g k σ₁ σ₂ ω₁ ω₂ a b h₁ h₂
  refine ⟨(show Γ(G.left, ⊤) from G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) • σ₁ +
    (show Γ(G.left, ⊤) from G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b)) • σ₂,
    fun Z r z J hJ => ?_⟩
  refine (sval_smul_add_smul σ₁ σ₂ _ _ (r ≫ x') z hJ).trans ?_
  rw [h₁ Z r z J hJ, h₂ Z r z J hJ, map_add, map_mul, map_mul, gs_add r z ⊤ trivial, gs_mul r z ⊤ trivial,
    gs_mul r z ⊤ trivial, ← gs_base_fn G.hom φ x' h r z a, ← gs_base_fn G.hom φ x' h r z b, add_mul, _root_.mul_assoc,
    _root_.mul_assoc]

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkIdealVanishingIdealPreimageIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StalkVan

theorem comap_inv_eq_map {A B : CommRingCat.{0}} (e : A ≅ B) (I : Ideal A) :
    I.comap e.inv.hom = I.map e.hom.hom := by
  have := Ideal.map_comap_of_equiv (I := I) e.commRingCatIsoToRingEquiv
  exact this.symm

theorem ideal_comap_eq_map {X X' : Scheme.{0}} (f : X' ⟶ X) [IsIso f] (I : X.IdealSheafData)
    (V : X'.affineOpens) :
    (I.comap f).ideal V = (I.ideal ⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩).map
      (f.appLE (f ''ᵁ V.1) V.1 (f.preimage_image_eq V.1).ge).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, comap_inv_eq_map, Scheme.Hom.appIso_hom']

theorem map_germ_app_congr {X X' : Scheme.{0}} (f : X' ⟶ X) (I : X.IdealSheafData) (x : X') :
    ∀ (W U : X.affineOpens), W = U → ∀ (hW : x ∈ f ⁻¹ᵁ W.1) (hU : x ∈ f ⁻¹ᵁ U.1),
      (I.ideal W).map ((X'.presheaf.germ (f ⁻¹ᵁ W.1) x hW).hom.comp (f.app W.1).hom) =
      (I.ideal U).map ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hU).hom.comp (f.app U.1).hom) := by
  rintro W U rfl hW hU
  rfl

theorem stalkId_vanishingIdeal_preimage : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f]
    (Z : TopologicalSpace.Closeds X) (Z' : TopologicalSpace.Closeds X'),
    (Z' : Set X') = f ⁻¹' (Z : Set X) → ∀ (U : X.affineOpens) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1),
    ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z') x =
      ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).map
        ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom.comp (f.app U.1).hom) := by
  intro X X' f _ Z Z' hZ U x hx
  have hc : (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal Z' :=
    GlobalTheory.vanishingIdeal_comap_of_isOpenImmersion X' X f Z Z' fun y => by
      rw [← SetLike.mem_coe, hZ]; rfl
  let V : X'.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have hxV : x ∈ V.1 := hx
  rw [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x V hxV, ← hc, ideal_comap_eq_map, Ideal.map_map]
  have hWU : (⟨f ''ᵁ V.1, V.2.image_of_isOpenImmersion f⟩ : X.affineOpens) = U := by
    apply Subtype.ext
    show f ''ᵁ (f ⁻¹ᵁ U.1) = U.1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    refine inf_eq_right.2 fun y _ => ?_
    exact ⟨(inv f) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  have hxW : x ∈ f ⁻¹ᵁ (f ''ᵁ V.1) := (f.preimage_image_eq V.1).ge hxV
  rw [← map_germ_app_congr f _ x _ U hWU hxW hx]
  congr 1
  rw [Scheme.Hom.appLE, CommRingCat.hom_comp, ← RingHom.comp_assoc, ← CommRingCat.hom_comp,
    TopCat.Presheaf.germ_res]

end GlobalTheory.StalkVan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSpDualNumber
section
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InteriorKS

theorem subsingleton_sp_dualNumber (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem rigidity_dualNumber {K : Type} [Field K] (A₀ : Over (Sp K)) (A' G' : Over (Sp (DualNumber K))) [GrpObj A']
    [GrpObj G'] (j : A₀.left ⟶ A'.left) (a b : A' ⟶ G') (hA : IsAbelianScheme A')
    (hj : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI := subsingleton_sp_dualNumber K
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (hL.globalFns _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [Field K] {x₀ : Sp K ⟶ Xo.X} {x' : Sp (DualNumber K) ⟶ Xo.X}
  {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {π : A.left ⟶ Xo.univ.t.G.left}
  {π' : A'.left ⟶ Xo.univ.t.G.left} {i : A.left ⟶ A'.left} {q : A'.left ⟶ A.left}

theorem act_const (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg : g ≫ π' = m.cm.F) (hgw : g ≫ A'.hom = o.t.G.hom) (a : 𝓞 E) :
    (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  haveI := Xo.univ.t.act.hom a
  have wβ : (π ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A.hom ≫ x₀ := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ.1.w]
  let β : A ⟶ A := Over.homMk (hπ.1.lift _ A.hom wβ) (hπ.1.lift_snd _ _ _)
  have hβ : β.left ≫ π = π ≫ (Xo.univ.t.act.act a).left := hπ.1.lift_fst _ _ _
  haveI : IsMonHom β := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ hπ (Xo.univ.t.act.act a) β hβ
  have wα : (π' ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A'.hom ≫ x' := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ'.1.w]
  let α : A' ⟶ A' := Over.homMk (hπ'.1.lift _ A'.hom wα) (hπ'.1.lift_snd _ _ _)
  have hα : α.left ≫ π' = π' ≫ (Xo.univ.t.act.act a).left := hπ'.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ' hπ' (Xo.univ.t.act.act a) α hα
  have wδ : (q ≫ β.left) ≫ A.hom = A'.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w β, hq.1.w]
  let δ : A' ⟶ A' := Over.homMk (hq.1.lift _ A'.hom wδ) (hq.1.lift_snd _ _ _)
  have hδ : δ.left ≫ q = q ≫ β.left := hq.1.lift_fst _ _ _
  haveI : IsMonHom δ := GlobalTheory.UU.isMonHom_of_over_isMonHom hq hq β δ hδ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ'
  have e1 : i ≫ α.left = β.left ≫ i := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, reassoc_of% hiπ, hiπ, hβ]
    · simp only [Category.assoc]
      rw [Over.w α, hi.1.w, reassoc_of% (Over.w β)]
  have e2 : i ≫ δ.left = β.left ≫ i := by
    apply hq.1.hom_ext
    · simp only [Category.assoc]
      rw [hδ, reassoc_of% hiq, hiq, Category.comp_id]
    · simp only [Category.assoc]
      rw [Over.w δ, hi.1.w, reassoc_of% (Over.w β)]
  have hαδ : α = δ := rigidity_dualNumber A A' A' i α δ hA' hi.1 (e1.trans e2.symm)
    (by rw [IsMonHom.one_hom, IsMonHom.one_hom])
  have hga : (o.t.act.act a).left ≫ g = g ≫ α.left := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, hg, reassoc_of% hg]
      exact m.act a
    · simp only [Category.assoc]
      rw [hgw, Over.w α, hgw, Over.w (o.t.act.act a)]
  calc (o.t.act.act a).left ≫ (g ≫ q ≫ π) = g ≫ α.left ≫ q ≫ π := by rw [reassoc_of% hga]
    _ = g ≫ q ≫ π ≫ (Xo.univ.t.act.act a).left := by rw [hαδ, reassoc_of% hδ, hβ]
    _ = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by simp only [Category.assoc]

theorem cub_const (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg1 : g ≫ π' = m.cm.F) (hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π)) :
    (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    GlobalTheory.TangentConstLB.lbIso_tangent_const E H Dw l Xo c K x₀ x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)

theorem objMap_const (c : Coeff l) [Algebra c.F K] (hx : GlobalTheory.DeRham.epsRed K ≫ x' = x₀)
    (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') : Nonempty (ObjMap o Xo.univ (constPt x')) := by
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ x₀ = constPt x' := by
    rw [← hx]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]
  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.TorsConst.torsion_eq_const K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := act_const hi hπ hπ' hiπ hiq hq o m g hg hgw
    lin := cub_const c hi hπ hπ' hiπ hiq hq o m g hg hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩

theorem eq_constPt (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q) : x' = constPt x' := by
  obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  exact Xo.unram K x' o ⟨m⟩ (objMap_const c rfl hi (hi.comp hπ') hπ' rfl hiq hq o m)

end GlobalTheory.InteriorKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentAbsIntClosedLocalDomai
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.GmAic

theorem pull_spMap_bijective (R : Type) [CommRing R] {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (F : Shv R) (n : ℤ) : Function.Bijective (pull R (spMap (e : A →+* A')) F n) := by
  have key : ∀ {B B' : Type} [CommRing B] [CommRing B'] (g : B ≃+* B') (x : H R (sp B') F n),
      pull R (spMap (g : B →+* B')) F n (pull R (spMap (g.symm : B' →+* B)) F n x) = x := by
    intro B B' _ _ g x
    rw [← pull_comp]
    have h : spMap (g : B →+* B') ≫ spMap (g.symm : B' →+* B) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Spec.map_comp]
      have h' : CommRingCat.ofHom (g.symm : B' →+* B) ≫ CommRingCat.ofHom (g : B →+* B') = 𝟙 _ := by
        ext y; simp
      rw [h', Spec.map_id, CategoryTheory.Functor.map_id]
    rw [h, pull_id]
  refine ⟨fun x y hxy => ?_, fun x => ⟨_, key e x⟩⟩
  have hx := key e.symm x
  have hy := key e.symm y
  simp only [RingEquiv.symm_symm] at hx hy
  rw [← hx, ← hy, hxy]

def laurentEquiv (hC3 : C3) (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T)
    (hq : IsUnit (q : T)) (n i : ℤ) :
    Ht q (sp (LaurentPolynomial T)) n i ≃+ Ht q (sp (LaurentPolynomial (FractionRing T))) n i := by
  haveI : IsScalarTower T (Polynomial T) (LaurentPolynomial T) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Polynomial.toLaurent_C]
      rfl
  haveI : Algebra.Etale (Polynomial T) (LaurentPolynomial T) :=
    Algebra.Etale.of_isLocalizationAway (Polynomial.X : Polynomial T)
  have h1 := hC3 q T hA hq (LaurentPolynomial T) i n
  let e : TensorProduct T (FractionRing T) (LaurentPolynomial T) ≃+* LaurentPolynomial (FractionRing T) :=
    (AddMonoidAlgebra.scalarTensorEquiv (M := ℤ) T (FractionRing T)).toRingEquiv
  exact (AddEquiv.ofBijective _ h1).trans (AddEquiv.ofBijective _ (pull_spMap_bijective _ e (tw q i) n))

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial T)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial T)) 1 i ≃+ ZMod q) := by
  intro q _ T _ _ _ hA hq n i
  haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
  have hqK : IsUnit (q : FractionRing T) := by
    simpa using hq.map (algebraMap T (FractionRing T))
  obtain ⟨h2, _⟩ := GlobalTheory.T.tateTwistCohomology_laurentPolynomial_of_isAlgClosed q (FractionRing T) hqK n i
  obtain ⟨_, ⟨e1⟩⟩ := GlobalTheory.T.tateTwistCohomology_laurentPolynomial_of_isAlgClosed q (FractionRing T) hqK 1 i
  refine ⟨fun hn => ?_, ⟨(laurentEquiv GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq 1 i).trans e1⟩⟩
  haveI := h2 hn
  exact (laurentEquiv GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq n i).injective.subsingleton

end GlobalTheory.EtC.GmAic

end
end

