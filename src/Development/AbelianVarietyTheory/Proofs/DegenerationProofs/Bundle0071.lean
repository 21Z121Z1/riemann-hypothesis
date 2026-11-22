import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdditivePointsDescendFieldExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_points_descend_field_extension : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → ∀ (X : Type) [AddCommGroup X] (I : Type) (b : I → X), AddSubgroup.closure (Set.range b) = ⊤ → ∀ c : X → (𝟙_ (Over (Sp K)) ⟶ P.A), (∀ y z, c (y + z) = padd P.A (c y) (c z)) → ∀ x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ k, (c (b k)).left ≫ Φ = spMap i ≫ (x₀ k).left) → ∃ c₀ : X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) ∧ ∀ y, (c y).left ≫ Φ = spMap i ≫ (c₀ y).left := by
  first | exact @GlobalTheory.PointDescent.additive_points_descend | exact GlobalTheory.PointDescent.additive_points_descend | (intros; apply GlobalTheory.PointDescent.additive_points_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BaseFactsOfIsEE
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem baseFacts_of_isEE :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.HasTests → S.Over₀ M U₀ → S.IsEE M U₀ EE → BaseFacts S M U₀ EE := by
  intro o Ω _ _ _ hb S M U₀ EE hT hO hE
  have := hb.ft
  have := hb.char
  have h1 := classical_points_and_local_regularity o Ω M U₀ hO.normal
  have h2 := exists_at_test_of_cen o Ω S M U₀ hT hO
  have h3 := ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ hO
  have h4 := isoFree_TT_and_supI_specializes o Ω S M U₀ hO h1 h2 h3
  have h5 := EE_contains_stable_weightZero o Ω S M U₀ EE hO h1 h2 h3 h4 hE
  have h6 := coord_regular_and_unit o Ω S M U₀ EE hO h1 h2 h3 h4 hE
  exact ⟨hO, hE, h1.2, fun z p _ y y₀ τ hc ha => (h3 z p y y₀ τ hc ha).2, h4.1, h4.2.2.1,
    fun ξ => (h5 ξ).1, fun ξ => (h5 ξ).2.1, fun ξ => (h5 ξ).2.2, h6⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisValueAtOrigin
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OriginFrame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {Z : Scheme.{0}}

theorem sval_valueAt {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J =
      gs t z ⊤ v * (val τ t z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) t
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J
    (fun _ => J (t ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]
  refine Eq.trans ?_ ((congrArg (gs t z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull t (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (t ≫ x.left))) (val_le A L x _ hy) _)).symm

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    val (rigT A L rig T k) t z J = val rig (t ≫ T.hom) z J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) t
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ z _ hy _).trans ?_))
  exact gm_pull t T.hom z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (t ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem torsFrame_pow_origin (P : PolAV S) {T : Over S} {m : ℕ}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} (hx : x = 1) {τ} (H : IsTorsFrame P rig m x τ)
    (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good P.L z J) :
    val τ t z J ^ (m ^ 2) = val rig (t ≫ T.hom) z J ^ (m ^ 2) := by
  subst hx
  obtain ⟨-, -, β, hβ, hn, hc⟩ := H
  have q₁ := val_corr hJ hn (t ≫ T.hom)
  have q₂ := val_corr hJ hc t
  rw [val_pull hJ, val_mul hJ, val_inv] at q₁
  rw [val_mul hJ, val_pull hJ, val_rigT _ _ _ hJ] at q₂
  have p₁ : val (rigPow P.A P.L rig ((m : ℤ) ^ 2)) (t ≫ T.hom) z J = val rig (t ≫ T.hom) z J ^ ((m : ℤ) ^ 2) :=
    map_zpow _ _ _
  have p₂ : val (powFrame P.A P.L 1 τ ((m : ℤ) ^ 2)) t z J = val τ t z J ^ ((m : ℤ) ^ 2) := map_zpow _ _ _
  have q₃ : val β (t ≫ (1 : T ⟶ P.A).left) z J = _ := q₁.trans (congrArg (· * _) p₁)
  rw [p₂, q₃, zpow_one] at q₂
  rw [← zpow_natCast, ← zpow_natCast, Nat.cast_pow, q₂]
  exact inv_mul_cancel_right _ _

theorem valF_spMap_fn {R K : Type} [CommRing R] [Field K] (y : R →+* K) (a : R) :
    valF (X := (baseOver (Sp R)).left) (spMap y) ⊤ (fn a) = y a := by
  rw [valF, dif_pos (by simp)]
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at h'
  refine Eq.trans ?_ h'.symm
  congr 1

end GlobalTheory.OriginFrame

namespace GlobalTheory

open OriginFrame ThetaScalar in

theorem basis_value_at_origin : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (y₀ : S.R →+* K) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = spMap y₀ ≫ eSec ρ.P.A → Set.range (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → ∃ ξ : K, ξ ^ ((S.r * S.N) ^ 2) = 1 ∧ ∀ l, valF r _ ((ρ.s l).f (fun _ => jP)) = y₀ ⟨S.ev 0 l, S.ev_mem 0 l⟩ * (ξ * valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val) ^ S.N := by
  intro o Ω _ _ _ S ρ K _ y₀ r jP hr hU
  have := ρ.P.isAb.comm
  have h0 : ρ.pt 0 = 1 := mul_left_cancel (a := ρ.pt 0) (by rw [← ρ.pt_add, add_zero, _root_.mul_one])
  let z : Sp K := IsLocalRing.closedPoint K
  let t : Sp K ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have ht : t ≫ (baseOver (Sp S.R)).hom = spMap y₀ := Category.comp_id _
  have hz : (spMap y₀ ≫ eSec ρ.P.A) z ∈ ρ.P.L.U jP := hU ⟨z, by rw [hr]⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good ρ.P.L ρ.P.isLB z (fun _ : PUnit => spMap y₀ ≫ eSec ρ.P.A) (fun _ => jP)
    (fun _ _ _ => rfl) (fun _ => hz)
  have hs : (t ≫ (ptSecT ρ.P.A (ρ.pt 0)).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = spMap y₀ ≫ eSec ρ.P.A := by
    rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd, h0, ← ht, Category.assoc]; rfl
  have er : r = t ≫ (ptSecT ρ.P.A (ρ.pt 0)).left := by
    haveI : Mono (snd (baseOver (Sp S.R)) ρ.P.A).left :=
      inferInstanceAs (Mono (pullback.snd (𝟙 (Sp S.R)) ρ.P.A.hom))
    rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, hr, hs]
  have hp := torsFrame_pow_origin ρ.P h0 (ρ.fr_tors 0) t hJ
  rw [ht] at hp
  have m₁ : r z ∈ LB.wchart ρ.P.L (fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) (fun _ => jP) :=
    Set.mem_iInter.2 fun _ => hU ⟨z, rfl⟩
  have m₂ : (spMap y₀) z ∈ LB.wchart ρ.P.L (fun _ : PUnit => eSec ρ.P.A) (fun _ => jP) :=
    Set.mem_iInter.2 fun _ => hz
  have m₃ := hJ.mem (fun _ : Fin 1 => (ρ.pt 0).left) t
  have a₂ : toStk z (valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val) = (val ρ.rig (spMap y₀) z J).val :=
    (toStk_valF_gs (spMap y₀) _ z m₂ _).trans ((gs_unit _ z _ m₂ _).trans
      (congrArg Units.val (val_of ρ.rig (spMap y₀) z J (fun _ => jP) (fun _ => eJ PUnit.unit)).symm))
  obtain ⟨a, ha⟩ : ∃ a : K, toStk z a = (val (ρ.fr 0) t z J).val :=
    ⟨_, (toStk_valF_gs t _ z m₃ _).trans (gs_unit _ z _ m₃ _)⟩
  generalize valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val = b at a₂ ⊢
  have hb : b ≠ 0 := fun e => (val ρ.rig (spMap y₀) z J).ne_zero (by rw [← a₂, e, map_zero])
  have hab : a ^ ((S.r * S.N) ^ 2) = b ^ ((S.r * S.N) ^ 2) := (toStk z).injective (by
    rw [map_pow, map_pow, ha, a₂, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    exact congrArg Units.val hp)
  refine ⟨a / b, by rw [div_pow, hab, div_self (pow_ne_zero _ hb)], fun l => (toStk z).injective ?_⟩
  have hv := sval_valueAt (ρ.ev_val l 0) t hJ
  have p : val (powFrame ρ.P.A ρ.P.L (ρ.pt 0) (ρ.fr 0) S.N) t z J = val (ρ.fr 0) t z J ^ (S.N : ℤ) :=
    map_zpow _ _ _
  rw [← er, p, zpow_natCast] at hv
  replace hv := (sval_of (φ := fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) (ε := fun _ => (S.N : ℤ))
    (ρ.s l) r z J (fun _ => jP) (fun _ => by rw [hr]; exact eJ PUnit.unit)).symm.trans hv
  have a₁ := toStk_valF_gs r _ z m₁ ((ρ.s l).f (fun _ => jP))
  have a₃ := toStk_valF_gs t ⊤ z trivial (fn (⟨S.ev 0 l, S.ev_mem 0 l⟩ : S.R))
  rw [valF_spMap_fn] at a₃
  refine a₁.trans (hv.trans ?_)
  rw [div_mul_cancel₀ _ hb, map_mul, map_pow, a₃, ha, Units.val_pow_eq_pow_val]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureEqKerOfMeetsTorsionCosetsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.closure_eq_ker_of_meets_torsion_cosets' : ∀ (I X : Type) [AddCommGroup X] [Module.Free ℤ X] (n J M : ℕ), n ≠ 0 → 2 ≤ J → M = n ^ J → ∀ (yy : (I → ZMod M) →+ X ⧸ (nsmulAddMonoidHom M : X →+ X).range), Function.Surjective yy → ∀ Z : Set (I → ZMod M), Z ⊆ yy.ker → (∀ a ∈ yy.ker, ∃ b, n • b = 0 ∧ a + b ∈ Z) → AddSubgroup.closure Z = yy.ker := by
  first | exact @GlobalTheory.closure_eq_ker_of_meets_torsion_cosets | exact GlobalTheory.closure_eq_ker_of_meets_torsion_cosets | (intros; apply GlobalTheory.closure_eq_ker_of_meets_torsion_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdmissibleAffineModelDividingTupleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_affine_model_dividing_tuple' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (J₀ : Type) [Fintype J₀] (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω → ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ ∧ IsAffineOpen U₀ ∧ M.HasDiv t₀ := by
  first | exact @GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple | exact GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple | (intros; apply GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineRefinementSplitExtCharts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

def refinePull {X Y : Scheme.{0}} (A : LB Y) (π : X ⟶ Y) {I : Type} (V : I → X.Opens) (idx : I → A.ι)
    (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) : LB X where
  «ι» := I
  U := V
  g l l' := res (show V l ⊓ V l' ≤ π ⁻¹ᵁ (A.U (idx l) ⊓ A.U (idx l')) from fun _ hy => ⟨le l hy.1, le l' hy.2⟩)
    (pullU π _ (A.g (idx l) (idx l')))

theorem gm_refinePull {X Y : Scheme.{0}} (A : LB Y) (π : X ⟶ Y) {I : Type} (V : I → X.Opens) (idx : I → A.ι)
    (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) (y : X) (l l' : I) (h : y ∈ V l) (h' : y ∈ V l') :
    gm (𝟙 X) y (V l ⊓ V l') ((refinePull A π V idx le).g l l') =
      gm π y (A.U (idx l) ⊓ A.U (idx l')) (A.g (idx l) (idx l')) := by
  have hm : (𝟙 X : X ⟶ X) y ∈ V l ⊓ V l' := ⟨h, h'⟩
  refine (gm_res (𝟙 X) y _ hm _).trans ((gm_pull (𝟙 X) π y (A.U (idx l) ⊓ A.U (idx l'))
    ⟨le l h, le l' h'⟩ _).trans ?_)
  rw [Category.id_comp]

theorem refinePull_isLB {X Y : Scheme.{0}} (A : LB Y) (hA : A.IsLB) (π : X ⟶ Y) {I : Type} (V : I → X.Opens)
    (idx : I → A.ι) (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) (hV : ⨆ l, V l = ⊤) : (refinePull A π V idx le).IsLB := by
  refine ⟨hV, fun (l : I) => unit_ext (V := V l) fun y hy => ?_,
    fun (i j k : I) => unit_ext (V := V i ⊓ V j ⊓ V k) fun y hy => ?_⟩
  · refine (gm_res (𝟙 X) y _ hy _).trans ((gm_refinePull A π V idx le y l l hy hy).trans ?_)
    exact (mul_eq_left.1 (gm_cocycle hA π y (le l hy) (le l hy) (le l hy))).trans (map_one _).symm
  · refine (map_mul _ _ _).trans ((congrArg₂ (· * ·)
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y i j hy.1.1 hy.1.2))
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y j k hy.1.2 hy.2))).trans
      ((gm_cocycle hA π y (le i hy.1.1) (le j hy.1.2) (le k hy.2)).trans
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y i k hy.1.1 hy.2)).symm))

theorem exists_mem_splitChart {S : Scheme.{0}} (E : SplitExt S) (y : E.B.left) : ∃ j, y ∈ E.chart j := by
  classical
  choose j hj using fun k : Module.Free.ChooseBasisIndex ℤ E.X => exists_chart (E.O (E.basis k)).isLB y
  refine ⟨j, ?_⟩
  show y ∈ ((⨅ k, (E.O (E.basis k)).L.U (j k) : E.B.left.Opens) : Set E.B.left)
  rw [TopologicalSpace.Opens.coe_iInf]
  exact Set.mem_iInter.2 hj

theorem exists_affine_refinement : ∀ (S : Scheme.{0}) (E : SplitExt S) (Y : Scheme.{0}) (A : LB Y), A.IsLB → ∀ π : E.B.left ⟶ Y, ∃ N₀ : LB E.B.left, N₀.IsLB ∧ (∀ l, IsAffineOpen (N₀.U l)) ∧ (∀ l, ∃ j, N₀.U l ≤ E.chart j) ∧ Nonempty (ChartPull N₀ A π) := by
  intro S E Y A hA π
  have key : ∀ y : E.B.left, ∃ (V : E.B.left.Opens) (i : A.ι), y ∈ V ∧ IsAffineOpen V ∧ V ≤ π ⁻¹ᵁ A.U i ∧
      ∃ j, V ≤ E.chart j := fun y => by
    obtain ⟨i, hi⟩ := exists_chart hA (π y)
    obtain ⟨j, hj⟩ := exists_mem_splitChart E y
    obtain ⟨V, hV, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := π ⁻¹ᵁ A.U i ⊓ E.chart j) ⟨hi, hj⟩
    exact ⟨V, i, hy, hV, fun z hz => (hle hz).1, j, fun z hz => (hle hz).2⟩
  choose V idx hy haff le hch using key
  refine ⟨refinePull A π V idx le, refinePull_isLB A hA π V idx le ?_, haff, hch,
    ⟨⟨idx, le, fun y l l' h h' => gm_refinePull A π V idx le y l l' h h'⟩⟩⟩
  exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAppEqOfHasWtZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ZH.UFib

theorem gm_charUnit_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have a : splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd 0) = pullU τ.left ⊤ (charUnit S X 0) :=
    Units.ext (splitTorusPointsEquiv_val S X Z τ 0)
  have b : pullU τ.left ⊤ (charUnit S X 0) = 1 := a.symm.trans (map_one _)
  have c := gm_pull (𝟙 Z.left) τ.left z ⊤ trivial (charUnit S X 0)
  rw [b, map_one, Category.id_comp] at c
  exact c.symm

theorem gs_id_appLE {X Z : Scheme.{0}} (r : Z ⟶ X) (U : X.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z) (f : Γ(X, U)) :
    gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom f) = gs r z U f := by
  have e := gs_pull (𝟙 Z) r z U (h trivial) f
  rw [Category.id_comp] at e
  exact (gs_res (𝟙 Z) z h trivial _).trans e

theorem exists_app_eq_of_hasWt_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (W : E.B.left.Opens) (f : Γ(G.left, D.q.left ⁻¹ᵁ W)), UFib.HasWt D.i (D.q.left ⁻¹ᵁ W) f 0 → ∃ a : Γ(E.B.left, W), (D.q.left.app W).hom a = f := by
  intro k _ _ E G _ D W f hf
  have := D.q_affine
  refine (invariant_functions_descend _ G E.B _ D.q D.i D.q_hom D.i_hom D.q_flat D.q_surjective inferInstance
    D.isKernel W).2.2 f fun Z t g h₁ h₂ => fn_ext fun z _ => ?_
  rw [gs_id_appLE, gs_id_appLE, hf Z t g z (h₂ trivial), gm_charUnit_zero, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundle_on_admissible_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.HasTests → S.admitted M U₀ → ∃ EE : M.Lat S.J, S.IsEE M U₀ EE ∧ (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) := by
  first | exact @GlobalTheory.ZH.exists_isEE_of_adm | exact GlobalTheory.ZH.exists_isEE_of_adm | (intros; apply GlobalTheory.ZH.exists_isEE_of_adm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsChartUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.CrdIso

variable {X : Scheme.{0}}

theorem rr {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem mem_res {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (resG X h a) ↔ x ∈ V ∧ x ∈ X.basicOpen a := by
  erw [Scheme.basicOpen_res]
  rfl

theorem isUnit_res {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (hV : V ≤ X.basicOpen a) :
    IsUnit (resG X h a) := by
  have hu : IsUnit (resG X (X.basicOpen_le a) a) := X.toRingedSpace.isUnit_res_basicOpen a
  have := hu.map (resG X hV)
  rwa [rr] at this

theorem cancel {V : X.Opens} {J : Type} (a : J → Γ(X, V)) (ha : ∀ x ∈ V, ∃ j, x ∈ X.basicOpen (a j))
    {u u' : Γ(X, V)} (h : ∀ j, u * a j = u' * a j) : u = u' := by
  apply TopCat.Presheaf.section_ext X.sheaf V
  intro x hx
  obtain ⟨j, hj⟩ := ha x hx
  have hu := (Scheme.mem_basicOpen X (a j) x hx).1 hj
  have := congrArg (X.presheaf.germ V x hx).hom (h j)
  rw [map_mul, map_mul] at this
  exact hu.mul_right_cancel this

theorem exists_unit {V : X.Opens} {J : Type} (a b : J → Γ(X, V))
    (ha : ∀ x ∈ V, ∃ j, x ∈ X.basicOpen (a j)) (hb : ∀ j, X.basicOpen (a j) ≤ X.basicOpen (b j))
    (hab : ∀ j k, b j * a k = b k * a j) : ∃ w : Γ(X, V)ˣ, ∀ j, b j = w.val * a j := by
  have hu : ∀ j, IsUnit (resG X (X.basicOpen_le (a j)) (a j)) := fun j => isUnit_res _ _ le_rfl
  have hq : ∀ j, ∃ q : Γ(X, X.basicOpen (a j)), resG X (X.basicOpen_le (a j)) (b j) =
      q * resG X (X.basicOpen_le (a j)) (a j) := fun j =>
    ⟨resG X (X.basicOpen_le (a j)) (b j) * ↑(hu j).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcov : V ≤ ⨆ j, X.basicOpen (a j) := fun x hx => TopologicalSpace.Opens.mem_iSup.2 (ha x hx)
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun j => X.basicOpen (a j)) q := by
    intro i j
    change resG X (inf_le_left : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _) (q i) =
      resG X (inf_le_right : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _) (q j)
    have hV : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ V := inf_le_left.trans (X.basicOpen_le _)
    have e1 := congrArg (resG X (inf_le_left : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _)) (hq j)
    have e3 := congrArg (resG X hV) (hab i j)
    rw [map_mul, rr, rr] at e1 e2
    rw [map_mul, map_mul, e1, e2] at e3
    have u := (isUnit_res hV (a i) inf_le_left).mul (isUnit_res hV (a j) inf_le_right)
    apply u.mul_right_cancel
    linear_combination e3
  obtain ⟨r, hr'⟩ : ∃ r : Γ(X, V), ∀ j, resG X (X.basicOpen_le (a j)) r = q j :=
    (X.sheaf.existsUnique_gluing' (fun j => X.basicOpen (a j)) V
      (fun j => homOfLE (X.basicOpen_le _)) hcov q hcomp).exists
  have key : ∀ j, b j = r * a j := by
    intro j
    refine X.sheaf.eq_of_locally_eq' (fun j => X.basicOpen (a j)) V
      (fun j => homOfLE (X.basicOpen_le _)) hcov _ _ fun k => ?_
    change resG X (X.basicOpen_le (a k)) _ = resG X (X.basicOpen_le (a k)) _
    apply (hu k).mul_right_cancel
    rw [← map_mul, hab j k, map_mul, map_mul, hr', hq k]
    ring
  have hunit : IsUnit r := by
    refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x hx => ?_
    obtain ⟨j, hj⟩ := ha x hx
    have := hb j hj
    rw [key j, Scheme.basicOpen_mul] at this
    exact (Scheme.mem_basicOpen X r x hx).1 this.1
  exact ⟨hunit.unit, key⟩

theorem exists_pt (x : X) :
    ∃ (K : Type) (_ : Field K) (p : Sp K ⟶ X), ∀ U : X.Opens, ⊤ ≤ p ⁻¹ᵁ U ↔ x ∈ U := by
  refine ⟨X.residueField x, inferInstance, X.fromSpecResidueField x, fun U => ?_⟩
  have e := Scheme.fromSpecResidueField_apply x
  constructor
  · intro hU
    have := hU (Set.mem_univ (IsLocalRing.closedPoint (X.residueField x)))
    exact e _ ▸ this
  · intro hx y _
    exact (congrArg (· ∈ U) (e y)).mpr hx

theorem mem_chart {H : LB X} (t : H.Sec) (l : H.ι) {x : X} (hx : x ∈ nonzeroLocus t) (hl : x ∈ H.U l) :
    x ∈ X.basicOpen (t.f l) := by
  have hu := SecRatio.isUnit_res t l (V := nonzeroLocus t ⊓ H.U l) inf_le_left inf_le_right
  have : x ∈ X.basicOpen (resG X (inf_le_right : nonzeroLocus t ⊓ H.U l ≤ _) (t.f l)) := by
    rw [Scheme.basicOpen_of_isUnit _ hu]; exact ⟨hx, hl⟩
  exact ((mem_res _ _ _).1 this).2

variable {H H' : LB X} {J : Type} {s : J → H.Sec} {s' : J → H'.Sec}

theorem val_prop (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v)
    {K : Type} [Field K] (x : Sp K ⟶ X) (i : H.ι) (i' : H'.ι) (hi : ⊤ ≤ x ⁻¹ᵁ H.U i)
    (hi' : ⊤ ≤ x ⁻¹ᵁ H'.U i') :
    ∃ c : Kˣ, ∀ j, valR x _ ((s' j).f i') = c * valR x _ ((s j).f i) := by
  have h1 : Crd H s x (fun j => valR x _ ((s j).f i)) := ⟨i, 1, hi, fun j => by simp⟩
  have h2 : Crd H' s' x (fun j => valR x _ ((s' j).f i')) := ⟨i', 1, hi', fun j => by simp⟩
  exact CrdCalc.crd_unique (h K x _ h1) h2

theorem exists_chart_unit [IsReduced X] (hs : ⨆ j, nonzeroLocus (s j) = ⊤)
    (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v)
    (i : H.ι) (i' : H'.ι) : ∃ w : Γ(X, H'.U i' ⊓ H.U i)ˣ, ∀ j,
      resG X inf_le_left ((s' j).f i') = w.val * resG X inf_le_right ((s j).f i) := by
  have hv : ∀ x ∈ H'.U i' ⊓ H.U i, ∃ (K : Type) (_ : Field K) (φ : Γ(X, H'.U i' ⊓ H.U i) →+* K) (c : Kˣ),
      (∀ j, φ (resG X inf_le_left ((s' j).f i')) = c * φ (resG X inf_le_right ((s j).f i))) ∧
      ∀ f, IsUnit (φ f) ↔ x ∈ X.basicOpen f := by
    intro x hx
    obtain ⟨K, _, p, hp⟩ := exists_pt x
    obtain ⟨c, hc⟩ := val_prop h p i i' ((hp _).2 hx.2) ((hp _).2 hx.1)
    refine ⟨K, inferInstance, CrdCalc.valHom p _ ((hp _).2 hx), c, fun j => ?_, fun f => ?_⟩
    · rw [← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res _ _ ((hp _).2 hx),
        CrdCalc.valR_res _ _ ((hp _).2 hx), hc]
    · rw [← CrdCalc.valR_eq, CrdCalc.isUnit_valR_iff _ _ ((hp _).2 hx), hp]
  apply exists_unit
  · intro x hx
    have : x ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨j, (mem_res _ _ _).2 ⟨hx, mem_chart _ _ hj hx.2⟩⟩
  · intro j x hx
    have hx' := X.basicOpen_le _ hx
    obtain ⟨K, _, φ, c, hc, hunit⟩ := hv x hx'
    rw [← hunit, hc, Units.isUnit_units_mul, hunit]
    exact hx
  · intro j k
    rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' := X.basicOpen_le _ hx
    obtain ⟨K, _, φ, c, hc, hunit⟩ := hv x hx'
    have := (hunit _).2 hx
    rw [map_sub, map_mul, map_mul, hc, hc] at this
    exact (this.ne_zero (by ring)).elim

theorem exists_iso_of_crd : ∀ (X : Scheme.{0}) [IsIntegral X] (H H' : LB X) (J : Type) (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → (∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v) → ∃ w : LB.Iso H H', w.IsGen ∧ ∀ j (x : X) (i : H.ι) (i' : H'.ι), x ∈ H.U i → x ∈ H'.U i' → gs (𝟙 X) x _ ((s' j).f i') = gs (𝟙 X) x _ (w.s (i', i)).val * gs (𝟙 X) x _ ((s j).f i) := by
  intro X _ H H' J s s' _ _ hs h
  choose w hw using exists_chart_unit hs h
  refine ⟨⟨fun p => w p.2 p.1⟩, ?_, ?_⟩
  · rintro ⟨i', i⟩ ⟨k', k⟩
    apply Units.ext
    have hi' : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H'.U i' := inf_le_left.trans inf_le_left
    have hi : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H.U i := inf_le_left.trans inf_le_right
    have hk' : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H'.U k' := inf_le_right.trans inf_le_left
    have hk : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H.U k := inf_le_right.trans inf_le_right
    refine cancel (V := H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k)) (fun j => resG X hi ((s j).f i)) ?_ fun j => ?_
    · intro x hx
      have : x ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
      exact ⟨j, (mem_res _ _ _).2 ⟨hx, mem_chart _ _ hj (hi hx)⟩⟩
    · have e1 := congrArg (resG X (inf_le_left : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _)) (hw i i' j)
      have e2 := congrArg (resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _)) (hw k k' j)
      rw [map_mul, rr, rr] at e1 e2
      have e3 := SecRatio.compat_res (s j) i k hi hk
      have e4 := SecRatio.compat_res (s' j) i' k' hi' hk'
      have e5 : ((res (le_inf hi hk) (H.g i k))⁻¹).val * resG X (le_inf hi hk) (H.g i k).val = 1 :=
        Units.inv_mul _
      change resG X (inf_le_left : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w i i').val *
          resG X hi ((s j).f i) =
        resG X (le_inf hi' hk') (H'.g i' k').val * ((res (le_inf hi hk) (H.g i k))⁻¹).val *
          resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w k k').val * resG X hi ((s j).f i)
      rw [← e1, e4, e2, e3]
      linear_combination (-(resG X (le_inf hi' hk') (H'.g i' k').val *
        resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w k k').val *
        resG X hk ((s j).f k))) * e5
  · intro j x i i' hi hi'
    have hx : (𝟙 X : X ⟶ X) x ∈ H'.U i' ⊓ H.U i := ⟨hi', hi⟩
    have e := congrArg (gs (𝟙 X) x (H'.U i' ⊓ H.U i)) (hw i i' j)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx] at e
    exact e

end GlobalTheory.ZH.CrdIso
end
end

