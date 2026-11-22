import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3408
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3417
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3424
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSSymmAbLocus
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
namespace GlobalTheory.HeatV

theorem isKS_symm_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (DV : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) DV Θ₁ → Θ₁ᵀ = Θ₁ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab c hc n v' dd' hinv DV Θ₁ hKS

  have hc' : spMap (resV R c) ≫ 𝟙 (Sp R) = chart (bo R c) := by
    rw [Category.comp_id]; exact spMap_resV R c
  obtain ⟨hv, hb⟩ : (∀ i, IsTanAtG t (spMap (resV R c) ≫ 𝟙 (Sp R))
        (spMap (dualMap (resV R c)) ≫ (tv (v' i)).left)) ∧
      ∀ w, IsTanAtG t (spMap (resV R c) ≫ 𝟙 (Sp R)) w →
        ∃! a : Fin n → Γ(Sp R, (bo R c).1), IsCombAtG t (spMap (resV R c) ≫ 𝟙 (Sp R))
          (fun i => spMap (dualMap (resV R c)) ≫ (tv (v' i)).left) a w := by
    refine GlobalTheory.LocM.FrameBase.tanBasis_baseChange t (resV R c) (𝟙 (Sp R)) n _
      (fun i => GlobalTheory.LieMet.isTan_tv (v' i)) ?_
    intro w hw
    refine ⟨v'.repr (GlobalTheory.LieMet.tanOf hw), ?_, fun a ha => ?_⟩
    · show IsCombAtG t _ _ _ (tv (GlobalTheory.LieMet.tanOf hw)).left
      rw [GlobalTheory.LieMet.isComb_iff]
      exact (v'.sum_repr _).symm
    · have h := (GlobalTheory.LieMet.isComb_iff v' a (GlobalTheory.LieMet.tanOf hw)).1 ha
      rw [h]
      ext i
      simp [Finsupp.single_apply]
  rw [hc'] at hv hb

  have hc0 : c ≠ 0 := by
    rw [hc]; exact Finset.prod_ne_zero_iff.2 fun i _ => htt i
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  let gg : Γ(Sp R, ⊤) →+* FractionRing R :=
    (algebraMap R (FractionRing R)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have hs : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s = c := by simp [s]
  have hu : IsUnit (gg s) := by
    rw [isUnit_iff_ne_zero]
    simp only [gg, RingHom.comp_apply, hs]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc0))
  have gg_inj : Function.Injective gg := by
    intro x y h
    have h1 := IsFractionRing.injective R (FractionRing R) h
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h1
  let x₀ : Γ(Sp R, (bo R c).1) →+* FractionRing R :=
    IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu
  have hx₀ : ∀ y, x₀ (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) y) = gg y := by
    intro y
    show IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu _ = _
    rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hinj : Function.Injective x₀ := by
    show Function.Injective (IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu)
    rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      have := congrArg x₀ h
      rwa [hx₀, hx₀] at this
    · intro h
      rw [gg_inj h]
  have hres : x₀.comp (resV R c) = algebraMap R (FractionRing R) := by
    ext r
    show x₀ (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    rw [hx₀]
    simp [gg]
  have hsp : spMap x₀ ≫ chart (bo R c) = ReciprocityTheory.ChartRestriction.G.Out.jK R := by
    rw [← spMap_resV R c]
    show Spec.map (CommRingCat.ofHom x₀) ≫ Spec.map (CommRingCat.ofHom (resV R c)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    rw [← hres, ← Spec.map_comp]
    rfl

  have gpG := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left)
      (t.PP.L.pull (pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R)) _ P.U.gen.inv.left
          fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have key := GlobalTheory.T.kodairaSpencer_matrix_transpose_eq_at_polarized_point E H (Sp R) t (bo R c).1 (bo R c) n _ hv hb (FractionRing R) x₀ P.A
    (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R)) (gpG.congr hsp.symm rfl) hL le_rfl DV Θ₁ hKS
  ext a b
  apply hinj
  have := congrFun (congrFun key a) b
  simpa [Matrix.transpose_apply, Matrix.map_apply] using this

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

variable {O : Type} [Ring O]

def ActPB {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (z' : SiegPre h M ζ s') (act' : O → (z'.A ⟶ z'.A)) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A))
    (f : S' ⟶ S) : Prop :=
  ∃ (φ : z'.A.left ⟶ z.A.left) (φ₂ : (G2 z'.A).left ⟶ (G2 z.A).left),
    IsGrpPullback z'.A z.A f φ ∧ IsSquare φ φ₂ ∧ LBIso z'.P (z.P.pull φ₂) ∧
      (∀ a, (z'.lev a).left ≫ φ = f ≫ (z.lev a).left) ∧ ∀ o, (act' o).left ≫ φ = φ ≫ (act o).left

theorem ActPB.trans {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B}
    {s' : S' ⟶ Sp B} {s'' : S'' ⟶ Sp B} {z : SiegPre h M ζ s} {z' : SiegPre h M ζ s'} {z'' : SiegPre h M ζ s''}
    {act : O → (z.A ⟶ z.A)} {act' : O → (z'.A ⟶ z'.A)} {act'' : O → (z''.A ⟶ z''.A)} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m' : ActPB z'' act'' z' act' f') (m : ActPB z' act' z act f) :
    ActPB z'' act'' z act (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl, ha⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl', ha'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, GlobalTheory.TChart.AbPol.isSquare_comp hs' hs,
    GlobalTheory.TChart.AbLevel.lbIso_comp z.isLB z'.isLB z''.isLB hw hw', fun a => ?_, fun o => ?_⟩
  · rw [← Category.assoc, hl' a, Category.assoc, hl a, Category.assoc]
  · rw [← Category.assoc, ha' o, Category.assoc, ha o, Category.assoc]

def ZRel {h h' M : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {t : S ⟶ Sp B} (e : O)
    (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) {n : ℕ} (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (c : SiegPre h M ζ t) (z : SiegPre h' M ζ t)
    (act : O → (z.A ⟶ z.A)) : Prop :=
  ∃ (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 c.A ∧ pr ≫ inc = act e ∧
    LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) ∧ (∀ a, c.lev a ≫ inc = z.lev (jl a)) ∧
    ∀ a, z.lev a = (List.ofFn fun k => c.lev (κ k a) ≫ inc ≫ act (o k)).prod

theorem isQProjOver_comp_immersion {R : Type} [CommRing R] {X Y : Scheme.{0}} (j : X ⟶ Y) (s : Y ⟶ Sp R)
    (hj : IsImmersion j) (hq : QuasiCompact j) (hs : IsQProjOver s) : IsQProjOver (j ≫ s) := by
  obtain ⟨N, i, hi, hiq, rfl⟩ := hs
  exact ⟨N, j ≫ i, inferInstance, inferInstance, (Category.assoc _ _ _).symm⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRigidOfBase
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TautRigid

def dlog (k : Type) [Field k] : (DualNumber k)ˣ →* Multiplicative k where
  toFun x := Multiplicative.ofAdd ((x : DualNumber k).snd / (x : DualNumber k).fst)
  map_one' := by simp
  map_mul' x y := by
    have fne : ∀ x : (DualNumber k)ˣ, (x : DualNumber k).fst ≠ 0 := fun x h => by
      have := congrArg TrivSqZeroExt.fst x.mul_inv
      rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at this
      exact zero_ne_one this
    have hx := fne x
    have hy := fne y
    rw [← ofAdd_add]
    congr 1
    simp only [Units.val_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    field_simp
    ring

theorem fst_ne_zero {k : Type} [Field k] (x : (DualNumber k)ˣ) : (x : DualNumber k).fst ≠ 0 := fun h => by
  have := congrArg TrivSqZeroExt.fst x.mul_inv
  rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at this
  exact zero_ne_one this

theorem dlog_apply {k : Type} [Field k] (x : (DualNumber k)ˣ) :
    Multiplicative.toAdd (dlog k x) = (x : DualNumber k).snd / (x : DualNumber k).fst := rfl

def onePlus {k : Type} [Field k] (s : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr s
  inv := 1 - TrivSqZeroExt.inr s
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

theorem dlog_onePlus {k : Type} [Field k] (s : k) : Multiplicative.toAdd (dlog k (onePlus s)) = s := by
  rw [dlog_apply]; simp [onePlus]

end GlobalTheory.TautRigid

namespace GlobalTheory.TautRigid

open GlobalTheory.RigChart GlobalTheory.ToricData

variable {R : Type} [CommRing R] [IsDomain R]

def lamC (Q : DegPre R) {k : Type} [Field k] {B' : Scheme.{0}} {π₁ π₂ : B' ⟶ Q.P.A.left}
    (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B')) (y z : Q.X)
    (zz : Sp (DualNumber k)) (J : (Sp (DualNumber k) ⟶ Q.P.A.left) → Q.P.L.ι) : ((Sp (DualNumber k)).presheaf.stalk zz)ˣ :=
  gm (c' (y + z)) zz _ (w.s (fun _ => J (c' (y + z) ≫ π₂), fun _ => J (c' (y + z) ≫ π₁))) *
    (gm (c' y) zz _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))))⁻¹ *
    (gm (c' z) zz _ (w.s (fun _ => J (c' z ≫ π₂), fun _ => J (c' z ≫ π₁))))⁻¹ *
    gm (c' 0) zz _ (w.s (fun _ => J (c' 0 ≫ π₂), fun _ => J (c' 0 ≫ π₁)))

def AbConst (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B']
    (π₁ π₂ : B'.left ⟶ Q.P.A.left) (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) :
    Prop :=
  IsGrpPullback B' Q.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ ∧
    (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) ∧
    w.IsGen ∧ (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left)

end GlobalTheory.TautRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven.LocPf

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (h : m = n)
    (y : Fin n → (epsR R ⟶ G)) (hy : IsLieBasis y) : IsLieBasis (fun i : Fin m => y (i.cast h)) := by
  subst h
  exact hy

theorem exists_away_subset {A : Type} [CommRing A] [IsDomain A] (U : Set (Sp A)) (hU : IsOpen U)
    (hgen : Set.range (spMap (algebraMap A (FractionRing A))) ⊆ U) :
    ∃ f : A, f ≠ 0 ∧ Set.range (spMap (algebraMap A (Localization.Away f))) ⊆ U := by
  obtain ⟨q⟩ : Nonempty (Sp (FractionRing A)) := inferInstance
  have hp := hgen ⟨q, rfl⟩
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := (spMap (algebraMap A (FractionRing A)) q : PrimeSpectrum A)) hp hU
  refine ⟨r, ?_, ?_⟩
  · rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hpr (Ideal.zero_mem _)
  · rw [show Set.range (spMap (algebraMap A (Localization.Away r))) =
        ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)) from
      PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hrU

theorem mem_range_of_traits {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A]
    [Algebra.FiniteType ℤ A] (f : A) (hf : f ≠ 0) (b : Localization.Away f)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
      ∀ (t : A →+* V), t f ≠ 0 → ∀ h : Localization.Away f →+* FractionRing V,
        h.comp (algebraMap A _) = (algebraMap V (FractionRing V)).comp t →
        ∃ w : V, h b = algebraMap V (FractionRing V) w) :
    ∃ c : A, algebraMap A (Localization.Away f) c = b := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) b
  obtain ⟨n, hn⟩ := s.2
  have hdiv : f ^ n ∣ a := by
    refine GlobalTheory.T.dvd_of_dvd_in_completeDVRs_finite_residue A a (f ^ n) (pow_ne_zero n hf) ?_
    intro V _ _ _ _ hc hfin t ht
    by_cases htf0 : t f = 0
    · cases n with
      | zero => simp
      | succ k => exact absurd (by rw [map_pow, htf0, zero_pow (Nat.succ_ne_zero k)]) ht
    have htf : t f ≠ 0 := htf0
    have hinjV := IsFractionRing.injective V (FractionRing V)
    have hu : IsUnit (((algebraMap V (FractionRing V)).comp t) f) :=
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinjV).2 htf)
    have hcomp := IsLocalization.Away.lift_comp (S := Localization.Away f) f hu
    obtain ⟨w, hw⟩ := H V hc hfin t htf _ hcomp
    have e := congrArg (IsLocalization.Away.lift (S := Localization.Away f) f hu) hs
    rw [map_mul, hw, ← RingHom.comp_apply, hcomp, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      RingHom.comp_apply, ← map_mul] at e
    have e' := hinjV e
    refine ⟨w, ?_⟩
    rw [← e', ← hn, map_pow, mul_comm]
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c, ?_⟩
  have hsu : IsUnit (algebraMap A (Localization.Away f) (s : A)) := IsLocalization.map_units _ s
  have hn' : (s : A) = f ^ n := hn.symm
  rw [hc, map_mul] at hs
  refine (hsu.mul_left_inj).1 ?_
  rw [hs, hn', mul_comm]

end GlobalTheory.KeyEven.LocPf

namespace GlobalTheory.KeyEven.LocPf

theorem keyLoc_of_famUnit_keyTrait : ∀ κ : Rule, FamUnit κ → KeyTrait κ → KeyLoc κ := by
  intro κ hFU hKT A _ _ _ _ _ G _ _ L σ x y hG hsm hopen hsym hpol hunif hy hσ hkey
  have hkey0 := hkey
  obtain ⟨φ, -, -, -, hpb, -⟩ := hkey
  haveI : IsProper x.P.A.hom := x.P.isAb.proper
  have hab := GlobalTheory.range_subset_abLocus_of_isProper hG hpb.1
  obtain ⟨f, hf0, hfab⟩ := exists_away_subset (abLocus G) hopen hab
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have hle : Submonoid.powers f ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing (Localization.Away f) :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) (Localization.Away f) inferInstance
  haveI : IsIntegrallyClosed (Localization.Away f) :=
    isIntegrallyClosed_of_isLocalization (Localization.Away f) (Submonoid.powers f) hle
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) := IsLocalization.injective _ hle
  haveI : CharZero (Localization.Away f) := charZero_of_injective_algebraMap hinj
  obtain ⟨xB, hgB, hkB⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (Localization.Away f) (algebraMap A _) G L σ x.P.g y x.g_pos hG hsm hopen
    hsym hpol hy hσ hfab
  obtain ⟨u, hu⟩ := hFU (Localization.Away f) xB
  have hfu : IsUnit ((algebraMap A (FractionRing A)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hf0)
  have hc := IsLocalization.Away.lift_comp (S := Localization.Away f) f hfu
  have hpbx : KeyPB x xB (IsLocalization.Away.lift (S := Localization.Away f) f hfu) :=
    GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing A) (algebraMap A _) _ G L σ x.P.g y xB x hgB rfl hkB
      (by rw [hc]; exact hkey0)
  have hval := hu _ _ x hpbx
  have trait : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
      ∀ (t : A →+* V), t f ≠ 0 → ∀ h : Localization.Away f →+* FractionRing V,
        h.comp (algebraMap A _) = (algebraMap V (FractionRing V)).comp t →
        ∃ w : Vˣ, h u = algebraMap V (FractionRing V) w := by
    intro V _ _ _ _ hcomp hfin t ht h hh
    have hrange : Set.range (spMap ((algebraMap V (FractionRing V)).comp t)) ⊆ abLocus G := by
      rw [← hh]
      rintro _ ⟨p, rfl⟩
      exact hfab ⟨spMap h p, rfl⟩
    obtain ⟨xV, hgV, hkV⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (FractionRing V) ((algebraMap V _).comp t) G L σ x.P.g y x.g_pos hG hsm
      hopen hsym hpol hy hσ hrange
    have hpbV : KeyPB xV xB h :=
      GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing V) (algebraMap A _) h G L σ x.P.g y xB xV hgB hgV hkB
        (by rw [hh]; exact hkV)
    have hvalV := hu _ h xV hpbV
    obtain ⟨L', σ', y', hiso, hy', hσ', hk'⟩ := GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis A V (FractionRing V) t (algebraMap V _) G L σ xV
      (fun i => y (i.cast hgV)) hG (isLieBasis_cast hgV y hy) hσ hkV
    have hne : (spMap t ⁻¹' abLocus G).Nonempty := by
      obtain ⟨q⟩ : Nonempty (Sp (FractionRing V)) := inferInstance
      exact ⟨spMap (algebraMap V _) q, hrange ⟨q, rfl⟩⟩
    obtain ⟨D, A', U, hU⟩ := hunif V hcomp hfin (spMap t) hne
    obtain ⟨w, hw⟩ := hKT V hcomp hfin _ L' σ' xV y' (IsSemiAbelian.pullback _ G hG)
      ⟨D, A', U, LBIso.trans U.LG.isLB (pull_isLB L.isLB _) L'.isLB hU hiso⟩ hy' hσ' hk'
    exact ⟨w, hvalV.symm.trans hw⟩
  obtain ⟨c, hcu⟩ := mem_range_of_traits f hf0 (u : Localization.Away f) (fun V _ _ _ _ hcomp hfin t ht h hh => by
    obtain ⟨w, hw⟩ := trait V hcomp hfin t ht h hh
    exact ⟨w, hw⟩)
  obtain ⟨c', hcu'⟩ := mem_range_of_traits f hf0 ((u⁻¹ : (Localization.Away f)ˣ) : Localization.Away f)
    (fun V _ _ _ _ hcomp hfin t ht h hh => by
      obtain ⟨w, hw⟩ := trait V hcomp hfin t ht h hh
      refine ⟨((w⁻¹ : Vˣ) : V), ?_⟩
      rw [map_units_inv, map_units_inv, hw])
  have hcc : c * c' = 1 := hinj (by rw [map_mul, hcu, hcu', Units.mul_inv, map_one])
  refine ⟨⟨c, c', hcc, by rw [mul_comm]; exact hcc⟩, ?_⟩
  rw [hval, Units.val_mk, ← hcu, ← RingHom.comp_apply, hc]

end GlobalTheory.KeyEven.LocPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfAdjunctionKltLocalModelStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.klt_of_adjunctionKlt_localModel : GlobalTheory.Published.Principalisation → ∀ {L : Type} [Field L] (c : ℂ →+* L) (n : ℕ) (T : Subring L) (x : Fin n → L) (φ : L →₀ ℚ) (f : L) (S : Place c), IsLocModel c T → IsIntegrallyClosed T → TrBasis c x → f ∈ T → f ≠ 0 → S.IsPrimeOf T → S.ord f = 1 → S.disc (dForm c x) φ = 0 → EffAt c n T (dForm c x) φ → AdjKlt c n T S (dForm c x) (φ + Finsupp.single f 1) → Klt c n T (dForm c x) φ := by
  first | exact @GlobalTheory.FieldPair.klt_of_adjKlt_locModel | exact GlobalTheory.FieldPair.klt_of_adjKlt_locModel | (intros; apply GlobalTheory.FieldPair.klt_of_adjKlt_locModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerInjectiveClosedInteriorPointStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_injective_closed_interior_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ interior Y, x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  first | exact @GlobalTheory.InteriorKS.mem_smul_top_of_isKS | exact GlobalTheory.InteriorKS.mem_smul_top_of_isKS | (intros; apply GlobalTheory.InteriorKS.mem_smul_top_of_isKS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUniqueOverChartAbelianLocus
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

namespace GlobalTheory.ChartKSUniq

theorem isKS_unique_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤)), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ' → Θ = Θ' := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _ n v hv hb D Θ Θ' h h'
  haveI : CharZero (ChartRing k m d) :=
    charZero_of_injective_algebraMap (R := k) (MvPowerSeries.C_injective (σ := Fin m ⊕ Fin d) (R := k))
  haveI : CharZero (FractionRing (ChartRing k m d)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (ChartRing k m d) (FractionRing (ChartRing k m d)))
  let φ : Γ(Sp (ChartRing k m d), ⊤) →+* FractionRing (ChartRing k m d) :=
    (algebraMap (ChartRing k m d) (FractionRing (ChartRing k m d))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom
  have hφ : Function.Injective φ := by
    exact (IsFractionRing.injective (ChartRing k m d) (FractionRing (ChartRing k m d))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).commRingCatIsoToRingEquiv.injective
  have hx : spMap φ ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) = jK (ChartRing k m d) := by
    show spMap φ ≫ (isAffineOpen_top (Sp (ChartRing k m d))).fromSpec = _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext r
    simp [φ]
  set R := ChartRing k m d with hRdef
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) :=
    GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  have hf : (∏ i, bdParam k m d i : R) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ h0 => by
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
      simp [bdParam, MvPowerSeries.coeff_X] at this
  have hV : ⊤ ≤ (spMap φ ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ⁻¹ᵁ
      (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, bdParam k m d i)) := by
    intro p _
    change (spMap φ) p ∈ (isAffineOpen_top (Sp R)).fromSpec ⁻¹ᵁ (Sp R).basicOpen _
    rw [(isAffineOpen_top (Sp R)).fromSpec_preimage_basicOpen]
    show PrimeSpectrum.comap φ p ∈ PrimeSpectrum.basicOpen _
    rw [PrimeSpectrum.mem_basicOpen]
    show _ ∉ Ideal.comap φ p.asIdeal
    haveI := p.isPrime
    rw [Ideal.mem_comap, Ideal.eq_bot_of_prime p.asIdeal, Ideal.mem_bot]
    intro h0
    apply hf
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_zero, ← h0]
    show _ = algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom _))
    rw [Iso.inv_hom_id_apply]
  have key := GlobalTheory.T.kodairaSpencer_unique_at_polarized_fieldPoint E H (Sp R) t _ (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) n v hv hb
    (FractionRing R) φ P.A _ hV (by rw [hx]; exact gpG) hL _ Θ Θ' h h'
  ext a b
  exact hφ (congrFun₂ key a b)

end GlobalTheory.ChartKSUniq
end

