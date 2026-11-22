import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionOfBaseProductSection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem le_preimage_wchart_of_section {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (k : L.ι) : L.U k ≤ σ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => k) := by
  intro x hx
  refine Set.mem_iInter.2 fun _ => ?_
  change (σ ≫ π) x ∈ L.U k
  rw [h]
  exact hx

noncomputable def secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) : LB.Sec L where
  f k := (X.presheaf.map (homOfLE (le_preimage_wchart_of_section L π σ h k)).op).hom
    ((σ.app _).hom (s.f (fun _ => k)))
  compat i j := fn_ext fun x hx => by
    have li := le_preimage_wchart_of_section L π σ h i hx.1
    have lj := le_preimage_wchart_of_section L π σ h j hx.2
    rw [gs_res _ x inf_le_left hx, gs_mul _ x _ hx, gs_res _ x inf_le_right hx, gs_res _ x _ hx.1, gs_res _ x _ hx.2,
      gs_unit _ x _ hx]
    refine (gs_pull (𝟙 X) σ x _ li _).trans ((sec_trans s (𝟙 X ≫ σ) x li lj).trans
      (congrArg₂ (· * ·) ?_ (gs_pull (𝟙 X) σ x _ lj _).symm))
    simp only [trF, Fin.prod_univ_one, zpow_one, Category.assoc, h, Category.comp_id]

theorem gs_secOfSection {X Y Z : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) (r : Z ⟶ X) (z : Z) (k : L.ι)
    (hz : r z ∈ L.U k) : gs r z _ ((secOfSection L π σ h s).f k) =
      gs (r ≫ σ) z (LB.wchart L (fun _ : Fin 1 => π) (fun _ => k)) (s.f (fun _ => k)) :=
  (gs_res r z _ hz _).trans (gs_pull r σ z _ (le_preimage_wchart_of_section L π σ h k hz) _)

theorem valR_secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) {F : Type} [CommRing F] (r : Sp F ⟶ X)
    (k : L.ι) (hr : ⊤ ≤ r ⁻¹ᵁ L.U k) : valR r _ ((secOfSection L π σ h s).f k) =
      valR (r ≫ σ) (LB.wchart L (fun _ : Fin 1 => π) (fun _ => k)) (s.f (fun _ => k)) :=
  (HolHom.valR_res r _ _ hr).trans (HolHom.valR_comp r σ _ _).symm

theorem mem_nonzeroLocus_secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (h' : π ≫ σ = 𝟙 Y) (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) (y : Y)
    (hy : y ∈ nonzeroLocus s) : π y ∈ nonzeroLocus (secOfSection L π σ h s) := by
  obtain ⟨j, hj⟩ := AmpleSpan.exists_chart_of_mem s hy
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j (0 : Fin 1), funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hk : π y ∈ L.U k := Set.mem_iInter.1 hj 0
  rw [AmpleSpan.mem_nonzeroLocus_iff_gs _ π y hk, gs_secOfSection L π σ h s π y k hk, h']
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs s (𝟙 Y) y hj).1 hy

theorem exists_sec_of_baseOver : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), ∃ θ : LB.Sec P.L, (∀ y ∈ nonzeroLocus th, (snd (baseOver (Sp R)) P.A).left y ∈ nonzeroLocus θ) ∧ ∀ (z : baseOver (Sp R) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp R)).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (a : R), IsValueAt P.A P.L 1 th z τ (fn a) → ∀ (F : Type) [CommRing F] (f : R →+* F) (k : P.L.ι), ⊤ ≤ (spMap f ≫ z.left) ⁻¹ᵁ P.L.U k → valR (spMap f ≫ z.left) _ (θ.f k) = f a * valR (X := (baseOver (Sp R)).left) (spMap f) _ (τ.s (fun _ => k)).val := by
  intro R _ P th
  let σ : P.A ⟶ baseOver (Sp R) ⊗ P.A := lift (toUnit P.A) (𝟙 P.A)
  have h : σ ≫ snd _ _ = 𝟙 _ := lift_snd _ _
  have h' : snd _ _ ≫ σ = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, h, Category.comp_id, Category.id_comp]
  have hl : σ.left ≫ (snd (baseOver (Sp R)) P.A).left = 𝟙 _ := by rw [← Over.comp_left, h, Over.id_left]
  have hl' : (snd (baseOver (Sp R)) P.A).left ≫ σ.left = 𝟙 _ := by rw [← Over.comp_left, h', Over.id_left]
  refine ⟨secOfSection P.L _ σ.left hl th, mem_nonzeroLocus_secOfSection P.L _ σ.left hl hl' th, ?_⟩
  intro z τ a hv F _ f k hk
  have e : z ≫ σ = ptSecT P.A z := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, h, Category.comp_id, ptSecT, lift_snd]
  have e' : z.left ≫ σ.left = (ptSecT P.A z).left := by rw [← Over.comp_left, e]
  let x : Sp F ⟶ (baseOver (Sp R)).left := spMap f
  have hw : ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => z.left) (fun _ => k) :=
    fun p hp => Set.mem_iInter.2 fun _ => hk hp
  have H := congrArg (valR x _) (hv (fun _ => k))
  have H₁ := (HolHom.valR_comp x (ptSecT P.A z).left _ _).trans ((HolHom.valR_res x _ _ hw).symm.trans H)
  have H₂ := H₁.trans (((HolHom.valR_eq x _ hw _).trans (map_mul _ _ _)).trans (congrArg₂ (· * ·)
    ((HolHom.valR_eq x _ hw _).symm.trans ((HolHom.valR_res x _ _ hw).trans (Conv.valR_spMap_top f a)))
    (HolHom.valR_eq x _ hw _).symm))
  refine (valR_secOfSection P.L _ σ.left hl th (x ≫ z.left) k hk).trans ?_
  rw [Category.assoc, e']
  exact H₂

end GlobalTheory.UnitTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricLiftActionGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.ClassWeight

section General
open ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.ThetaPtMove
variable {B B' : Scheme.{0}} {G : Over B} [GrpObj G] {A : Over B'} [GrpObj A]
  {f : B' ⟶ B} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over B'} {T₀ : Over B} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem sv_sum_smul {L : LB A.left} {k : ℤ} {I : Type} (F : Finset I) (c : I → Γ(T.left, ⊤))
    (v : I → SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    ThetaAct.sv (∑ l ∈ F, c l • v l) r z J =
      ∑ l ∈ F, gs (r ≫ (fst T A).left) z ⊤ (c l) * ThetaAct.sv (v l) r z J := by
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have h := ThetaAct.sv_add (0 : SecM A L k T) 0 r z hJ
    rw [add_zero] at h
    exact left_eq_add.1 h
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ThetaAct.sv_add _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ, ih]

theorem secRel_sum {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T₀.left, ⊤))
    {t : I → LB.Sec (LPow A L₁ k T)} {s : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (s l)) :
    SecRel hp τ hτ w (SecM.toSec A (∑ l, τ.appTop.hom (c l) • SecM.ofSec A (t l)))
      (SecM.toSec G (∑ l, c l • SecM.ofSec G (s l))) := by
  intro Z r z J J' hJ hJ'
  refine (sv_sum_smul Finset.univ c (fun l => SecM.ofSec G (s l)) (r ≫ psi hp τ hτ) z hJ).trans (Eq.trans ?_
    (congrArg (_ * ·) (sv_sum_smul Finset.univ (fun l => τ.appTop.hom (c l)) (fun l => SecM.ofSec A (t l))
      r z hJ').symm))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, Category.assoc, psi_fst', ← Category.assoc]
  exact congrArg₂ (· * ·) (gs_pull _ τ z ⊤ trivial (c l)).symm (h l Z r z J J' hJ hJ')

theorem isActOf_unique {L : LB A.left} (hL : L.IsLB) {k : ℤ} {θ : ThetaGrp A L k T}
    {s s₁ s₂ : LB.Sec (LPow A L k T)} (h₁ : IsActOf A L k θ s s₁) (h₂ : IsActOf A L k θ s s₂) :
    SecM.ofSec A s₁ = SecM.ofSec A s₂ :=
  ThetaAct.sv_ext hL fun y J hJ =>
    ((ThetaAct.isActOf_iff hL θ s s₁).1 h₁ y J hJ).trans ((ThetaAct.isActOf_iff hL θ s s₂).1 h₂ y J hJ).symm

theorem exists_isActOf' {L : LB A.left} (hL : L.IsLB) {k : ℤ} (θ : ThetaGrp A L k T)
    (s : LB.Sec (LPow A L k T)) : ∃ s', IsActOf A L k θ s s' := by
  obtain ⟨v, hv⟩ := ThetaAct.exists_act hL θ (SecM.ofSec A s)
  exact ⟨SecM.toSec A v, (ThetaAct.isActOf_iff hL θ _ _).2 fun y J hJ => hv _ _ y J hJ⟩

theorem ofSec_eq_sum {L : LB A.left} {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T.left, ⊤))
    (s : I → LB.Sec (LPow A L k T)) (σ : LB.Sec (LPow A L k T))
    (h : ∀ j, σ.f j = ∑ l, liftFun A _ (c l) * (s l).f j) : σ = SecM.toSec A (∑ l, c l • SecM.ofSec A (s l)) := by
  have e : SecM.ofSec A σ = ∑ l, c l • SecM.ofSec A (s l) := by
    refine Subtype.ext (funext fun j => (h j).trans ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [← e]
  rfl

theorem symLift_act_move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ} {n : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ n = 1) {θ₀ : ThetaGrp G L₀ k T₀}
    (H₀ : SymLift G L₀ k n x₀ θ₀) {I : Type} [Fintype I] (c : I → I → Γ(T₀.left, ⊤)) (c' : I → I → Γ(T.left, ⊤))
    (hc : ∀ l i, τ.appTop.hom (c l i) = c' l i)
    {t : I → LB.Sec (LPow A L₁ k T)} {s : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (s l))
    (hs : ∀ i σ, IsActOf G L₀ k θ₀ (s i) σ → ∀ j, σ.f j = ∑ l, liftFun G _ (c l i) * (s l).f j) :
    ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧ ∀ i t', IsActOf A L₁ k θ (t i) t' →
      SecM.ofSec A t' = ∑ l, c' l i • SecM.ofSec A (t l) := by
  obtain ⟨θ, hθ, H⟩ := symLift_move hp τ hτ hw hL₀ hL₁ hx hn H₀
  refine ⟨θ, hθ, fun i t' ht' => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_isActOf' hL₀ θ₀ (s i)
  have e := ofSec_eq_sum _ _ σ (hs i σ hσ)
  have hr := secRel_sum hp τ hτ (fun l => c l i) h
  rw [← e] at hr
  refine (isActOf_unique hL₁ ht' (H _ _ _ _ (h i) hr hσ)).trans ?_
  simp only [hc]
  rfl

end General

theorem appTop_fn {R : Type} [CommRing R] (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F]
    [Algebra (FractionRing V) F] (y : R →+* F) (c : R) :
    (show (TFK (R := V) F).left ⟶ (baseOver (Sp R)).left from spMap y).appTop.hom (fn c) = kf V F (y c) :=
  (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem exists_symLift_act : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a)).left → x ^ S.N = 1 → ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)), SymLift u.A.A u.A.L S.N S.N x θ ∧ ∀ i t', IsActOf u.A.A u.A.L S.N θ (t i) t' → SecM.ofSec u.A.A t' = ∑ l, kf u.V (PadicAlgCl p) (y₀ (algebraMap o S.R (S.ρ a l i))) • SecM.ofSec u.A.A (t l) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u w hw t ht a x hx hn
  have := u.A.isAb.comm
  exact symLift_act_move u.cart (T := TFK (R := u.V) (PadicAlgCl p))
    (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) hw ρ.P.isLB u.A.isLB hx.symm hn (ρ.U_sym a)
    (fun l i => fn (algebraMap o S.R (S.ρ a l i))) _ (fun l i => appTop_fn u.V (PadicAlgCl p) y₀ _) ht (ρ.U_act a)

end GlobalTheory.ZH.ClassWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusQuotientNoCocharacter
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS.MaxTorus
open GlobalTheory.SplitTorus

theorem surjective_of_mono {S : Scheme.{0}} [Nonempty S] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (φ : Y →+ X) [Mono (torusMap S φ)] : Function.Surjective φ := by
  let π : X →+ X ⧸ φ.range := QuotientAddGroup.mk' _
  have h : π.comp φ = (0 : X →+ X ⧸ φ.range).comp φ := by
    ext y
    simp [π]
  have h' : π = 0 := by
    apply torusMap_injective (S := S)
    rw [← cancel_mono (torusMap S φ), ← torusMap_comp, ← torusMap_comp, h]
  intro x
  have : π x = 0 := by rw [h']; rfl
  exact (QuotientAddGroup.eq_zero_iff x).1 this

theorem injective_of_surjective {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (φ : Y →+ X) (h : Function.Surjective φ) (hr : Module.finrank ℤ Y ≤ Module.finrank ℤ X) :
    Function.Injective φ := by
  have h1 : Module.finrank ℤ X ≤ Module.finrank ℤ Y :=
    LinearMap.finrank_le_finrank_of_surjective (f := φ.toIntLinearMap) h
  let e : Y ≃ₗ[ℤ] X := LinearEquiv.ofFinrankEq _ _ (le_antisymm hr h1)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap φ.toIntLinearMap e.injective h

theorem exists_inv {S : Scheme.{0}} [ConnectedSpace S] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (σ : splitTorus S X ⟶ splitTorus S Y) [IsMonHom σ] [Mono σ]
    (hr : Module.finrank ℤ Y ≤ Module.finrank ℤ X) : ∃ τ, τ ≫ σ = 𝟙 _ := by
  obtain ⟨φ, rfl⟩ := exists_eq_torusMap σ
  have hs := surjective_of_mono (S := S) φ
  let e : Y ≃+ X := AddEquiv.ofBijective φ ⟨injective_of_surjective φ hs hr, hs⟩
  refine ⟨torusMap S e.symm.toAddMonoidHom, ?_⟩
  rw [← torusMap_comp, ← torusMap_id]
  congr 1
  ext y
  exact e.symm_apply_apply y

theorem exists_quot_no_cocharacter : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → f = 1 := by
  classical
  intro k _ _ G _ hG
  obtain ⟨hc, hsm, hsep, hqc, hgc⟩ := id hG
  have : ConnectedSpace G.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  let P : ℕ → Prop := fun n => ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
    (i : splitTorus (Sp k) X ⟶ G), IsMonHom i ∧ (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) ∧ Module.finrank ℤ X = n
  have hb : ∀ n, P n → n ≤ g := by
    rintro _ ⟨X, _, _, _, i, hi, hV, rfl⟩
    obtain ⟨B, _, q, -, hd⟩ := GlobalTheory.T.exists_smooth_torus_quotient_of_goodOpen_cover k G hG X i hi hV
    obtain ⟨a, -, ha⟩ := hd g hg
    omega
  obtain ⟨n₀, h₀⟩ : ∃ n, P n := by
    obtain ⟨X', _, _, _, i', ρ, h1, -, -, -, hV⟩ := GlobalTheory.T.splitTorus_image_factor_quotient_goodOpen k G hG PUnit 1
      (inferInstanceAs (IsMonHom (toUnit _ ≫ η[G])))
    exact ⟨_, X', _, ‹_›, ‹_›, i', h1, hV, rfl⟩
  obtain ⟨X, _, _, _, i, hi, hV, hn⟩ : P (Nat.findGreatest P g) := Nat.findGreatest_spec (hb _ h₀) h₀
  obtain ⟨B, _, q, hq, -⟩ := GlobalTheory.T.exists_smooth_torus_quotient_of_goodOpen_cover k G hG X i hi hV
  refine ⟨X, _, inferInstance, inferInstance, B, _, i, q, hq, fun f hf => ?_⟩
  obtain ⟨j, hj, rfl⟩ := GlobalTheory.T.exists_lift_oneParameter_quotient_torus k G hG X B i q hq f hf
  obtain ⟨-, hqm, -, -, -, hpb, -⟩ := hq
  have : Mono (η[B]) := ⟨fun a b _ => toUnit_unique a b⟩
  have : Mono i := hpb.mono_fst_of_mono
  let φ : splitTorus (Sp k) (X × ULift.{0} ℤ) ⟶ G :=
    (torusMap _ (AddMonoidHom.inl X (ULift.{0} ℤ)) ≫ i) * (torusMap _ (AddMonoidHom.inr X (ULift.{0} ℤ)) ≫ j)
  obtain ⟨X', _, _, _, i', ρ, h1, h2, -, h3, hV'⟩ := GlobalTheory.T.splitTorus_image_factor_quotient_goodOpen k G hG (X × ULift.{0} ℤ) φ
    (by simp only [φ]; rw [Hom.mul_def]; infer_instance)
  have hr : Module.finrank ℤ X' ≤ Module.finrank ℤ X := by
    have hP : P (Module.finrank ℤ X') := ⟨X', _, ‹_›, ‹_›, i', h1, hV', rfl⟩
    rw [hn]
    exact Nat.le_findGreatest (hb _ hP) hP
  have e1 : torusMap _ (AddMonoidHom.fst X (ULift.{0} ℤ)) ≫ φ = i := by
    simp only [φ, MonObj.comp_mul, ← Category.assoc, ← torusMap_comp, AddMonoidHom.fst_comp_inl,
      AddMonoidHom.fst_comp_inr, torusMap_id, torusMap_zero, Category.id_comp, MonObj.one_comp, _root_.mul_one]
  have e2 : torusMap _ (AddMonoidHom.snd X (ULift.{0} ℤ)) ≫ φ = j := by
    simp only [φ, MonObj.comp_mul, ← Category.assoc, ← torusMap_comp, AddMonoidHom.snd_comp_inl,
      AddMonoidHom.snd_comp_inr, torusMap_id, torusMap_zero, Category.id_comp, MonObj.one_comp, _root_.one_mul]
  let σ := torusMap _ (AddMonoidHom.fst X (ULift.{0} ℤ)) ≫ ρ
  have e3 : σ ≫ i' = i := by rw [Category.assoc, h3, e1]
  have : Mono σ := mono_of_mono_fac e3
  obtain ⟨τ, hτ⟩ := exists_inv σ hr
  have e4 : i' = τ ≫ i := by rw [← e3, ← Category.assoc, hτ, Category.id_comp]
  have e5 : i ≫ q = 1 := hpb.w
  rw [← e2, ← h3, e4]
  simp only [Category.assoc, e5, MonObj.comp_one]

end GlobalTheory.SS.MaxTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullback
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}

theorem GenTriv.exists_sec_hasVal (h : M.GenTriv H d) (x : Ω) (hx : ∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) :
    ∃ σ : H.Sec, M.HasVal d σ x := by
  have hf : ∀ k, ∃ f : Γ(M.Z, H.U k), (H.U k : Set M.Z).Nonempty → valF M.pt (H.U k) f = x / d k := fun k => by
    by_cases hk : (H.U k : Set M.Z).Nonempty
    · obtain ⟨f, hf⟩ := (mem_ringOn_iff_exists hk).1 (mem_ringOn.2 (hx k))
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose f hf using hf
  refine ⟨⟨f, fun i j => ?_⟩, hf⟩
  by_cases hij : ((H.U i ⊓ H.U j : M.Z.Opens) : Set M.Z).Nonempty
  · refine M.res_injective _ hij ?_
    have h1 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_left hij (f i)).trans
      (hf i (hij.mono (fun _ hz => hz.1))))
    have h2 := (M.res_apply _ hij _).trans ((M.valF_resG inf_le_right hij (f j)).trans
      (hf j (hij.mono (fun _ hz => hz.2))))
    have h3 := (M.res_apply _ hij _).trans (h.g_eq i j hij)
    rw [map_mul, h3]
    refine h1.trans (Eq.trans ?_ (congrArg (d j / d i * ·) h2.symm))
    have := h.ne i
    have := h.ne j
    field_simp
  · have e : (H.U i ⊓ H.U j : M.Z.Opens) = ⊥ :=
      SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hij)
    have : Subsingleton Γ(M.Z, H.U i ⊓ H.U j) := by
      rw [e]; infer_instance
    exact Subsingleton.elim _ _

theorem GenTriv.pull (h : M.GenTriv H d) {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}
    {N : RatModel o Ω'} {a : N.Z ⟶ M.Z} (ha : M.IsHom N φ a) :
    N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) := by
  refine ⟨fun k => (map_ne_zero φ).2 (h.ne _), fun k k' hk => ?_⟩
  have hle : (H.pull a).U k ⊓ (H.pull a).U k' ≤ a ⁻¹ᵁ (H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le H (fun _ => a) k PUnit.unit))
      (inf_le_right.trans (LB.wchart_le H (fun _ => a) k' PUnit.unit))
  have hne : ((H.U (k PUnit.unit) ⊓ H.U (k' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty := by
    obtain ⟨z, hz⟩ := hk
    exact ⟨a z, hle hz⟩
  have e : ((H.pull a).g k k' : Γ(N.Z, (H.pull a).U k ⊓ (H.pull a).U k')) =
      resG N.Z hle (a.app _ (H.g (k PUnit.unit) (k' PUnit.unit) : Γ(M.Z, _))) := by
    have e0 : (H.pull a).g k k' = Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) :=
      (Fintype.prod_unique (ι := PUnit) fun _ =>
        Semi.res hle (pullU a _ (H.g (k PUnit.unit) (k' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
    exact congrArg Units.val e0
  rw [e, N.valF_resG hle hk, ha.valF_app hne, h.g_eq _ _ hne, map_div₀]

theorem genTriv_sec_and_pull : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z)
    (d : H.ι → Ω), M.GenTriv H d →
    (∀ x : Ω, (∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) → ∃ σ : H.Sec, M.HasVal d σ x) ∧
    ∀ (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (a : N.Z ⟶ M.Z),
      M.IsHom N φ a → N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) :=
  fun _ _ _ _ _ _ _ _ h => ⟨h.exists_sec_hasVal, fun _ _ _ _ _ _ ha => h.pull ha⟩

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasTorusWeightIffTorusEquivariantStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTorusWeight_iff_torusEquivariant : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V) (h : V ≤ E.chart j) (f : Γ(G.left, D.q.left ⁻¹ᵁ V)) (α : E.X), UFib.HasWt D.i (D.q.left ⁻¹ᵁ V) f α ↔ ∀ χ, χ ≠ α → D.weight j V hV h χ f = 0 := by
  first | exact @GlobalTheory.ZH.PureWt.hasWt_iff_weight | exact GlobalTheory.ZH.PureWt.hasWt_iff_weight | (intros; apply GlobalTheory.ZH.PureWt.hasWt_iff_weight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesMulVecOfGenericValue
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem IsHom.valF_appLE {o Ω Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field Ω'] [Algebra o Ω']
    {M : RatModel o Ω} {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f)
    {U : M.Z.Opens} {V : M'.Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (hV : (V : Set M'.Z).Nonempty) (g : Γ(M.Z, U)) :
    M'.res V hV ((f.appLE U V e).hom g) = φ (valF M.pt U g) := by
  rw [res_apply, ← hf.valF_app ⟨_, e hV.some_mem⟩ g]
  exact (valR_appLE M'.pt f e (M'.top_le_preimage_pt hV) g).trans (valR_comp M'.pt f U g)

theorem crd_mulVec_of_hasVal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N N' : RatModel o Ω') (a : N'.Z ⟶ N.Z) (q : N'.Z ⟶ M.Z) (W : M.Z.Opens) (H : LB N.Z) (d : H.ι → Ω') (J : Type) [Fintype J] (st : J → H.Sec) (σ : J → (H.pull a).Sec) (t u : J → Ω') (c : Matrix J J Γ(M.Z, W)), N.IsHom N' (AlgHom.id o Ω') a → M.IsHom N' φ q → (∀ z, q z ∈ W) → (∀ j, N.HasVal d (st j) (t j)) → (∀ j, N'.HasVal (H := H.pull a) (fun k => d (k PUnit.unit)) (σ j) (u j)) → t = (c.map fun g => φ (valF M.pt W g)).mulVec u → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ N'.Z) (w : J → R), Crd (H.pull a) σ x w → Crd H st (x ≫ a) ((c.map (valR (x ≫ q) W)).mulVec w) := by
  intro o Ω _ _ _ M Ω' _ _ φ N N' a q W H d J _ st σ t u c ha hq hW ht hu htu R _ x w hx
  obtain ⟨k, e, hk, hw⟩ := hx
  have ea : (H.pull a).U k ≤ a ⁻¹ᵁ H.U (k PUnit.unit) := LB.wchart_le H _ k PUnit.unit
  have eq : (H.pull a).U k ≤ q ⁻¹ᵁ W := fun z _ => hW z
  refine ⟨k PUnit.unit, e, le_preimage_comp x a ea hk, fun i => ?_⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have hC : (((H.pull a).U k : N'.Z.Opens) : Set N'.Z).Nonempty := ⟨x y, hk (x := y) trivial⟩
  have key : (a.appLE _ _ ea).hom ((st i).f (k PUnit.unit)) =
      ∑ j, (q.appLE _ _ eq).hom (c i j) * (σ j).f k := by
    apply N'.res_injective _ hC
    rw [map_sum, ha.valF_appLE ea hC, ht i _ ⟨_, ea hC.some_mem⟩, htu]
    simp only [map_mul, hq.valF_appLE eq hC, AlgHom.id_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [res_apply, hu j k hC, mul_div_assoc]
  rw [← valR_appLE x a ea hk, key, valR_eq x _ hk, map_sum, Finset.mul_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← valR_eq x _ hk, ← valR_eq x _ hk, valR_appLE x q eq hk, hw j, mul_left_comm]

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesOfGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.CrdMove

theorem stk_onto {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

theorem stk_valR {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valR x U a) = gs x z U a := by
  rw [valR_of_field, valF, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem crd_iff {F : Type} [Field F] {X : Scheme.{0}} {H : LB X} {J : Type} (s : J → H.Sec) (x : Sp F ⟶ X)
    (v : J → F) (z : Sp F) : Crd H s x v ↔ ∃ (l : H.ι) (c : ((Sp F).presheaf.stalk z)ˣ), x z ∈ H.U l ∧
      ∀ j, toStk z (v j) = c.val * gs x z (H.U l) ((s j).f l) := by
  constructor
  · rintro ⟨l, c, hl, hv⟩
    have hz := (top_le_iff_mem x _ z).1 hl
    refine ⟨l, Units.map (toStk z).toMonoidHom c, hz, fun j => ?_⟩
    rw [hv, map_mul, stk_valR x _ z hz]
    rfl
  · rintro ⟨l, c, hz, hv⟩
    obtain ⟨d, hd⟩ := stk_onto z c.val
    have d0 : d ≠ 0 := fun h0 => by
      have : Nontrivial ((Sp F).presheaf.stalk z) := inferInstance
      rw [h0, map_zero] at hd
      exact Units.ne_zero _ hd.symm
    refine ⟨l, Units.mk0 d d0, (top_le_iff_mem x _ z).2 hz, fun j => (toStk z).injective ?_⟩
    rw [hv, map_mul, stk_valR x _ z hz, Units.val_mk0, hd]

theorem crd_move {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
    {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    {L₀ : LB G.left} {L₁ : LB A.left} (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) {n : ℤ} {I : Type}
    (t : I → LB.Sec (LPow A L₁ n T)) (s : I → LB.Sec (LPow G L₀ n T₀))
    (h : ∀ i, ThetaPtMove.SecRel hp τ hτ w (t i) (s i)) {F : Type} [Field F] (r : Sp F ⟶ (T ⊗ A).left) (v : I → F)
    (hv : Crd (LPow A L₁ n T) t r v) : Crd (LPow G L₀ n T₀) s (r ≫ ThetaPtMove.psi hp τ hτ) v := by
  let z : Sp F := IsLocalRing.closedPoint F
  obtain ⟨l, c, hl, hc⟩ := (crd_iff t r v z).1 hv
  obtain ⟨J, hJ, -⟩ := exists_good L₀ hL₀ z (K := Empty) (fun k => k.elim) (fun k => k.elim) (fun k => k.elim)
    (fun k => k.elim)
  obtain ⟨J', hJ', e⟩ := exists_good L₁ hL₁ z (fun _ : Fin 1 => r ≫ (snd T A).left) l
    (fun a b _ => congrArg l (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hl k)
  obtain ⟨d, hd⟩ : ∃ d : ((Sp F).presheaf.stalk z)ˣ, ∀ j,
      VVRank.sv G (s j) (r ≫ ThetaPtMove.psi hp τ hτ) z J = d.val * VVRank.sv A (t j) r z J' :=
    ⟨_, fun j => h j _ r z J J' hJ hJ'⟩
  refine (crd_iff s _ v z).2 ⟨fun _ => J ((r ≫ ThetaPtMove.psi hp τ hτ) ≫ (snd T₀ G).left),
    c * d⁻¹,
    hJ.mem (fun _ : Fin 1 => (snd T₀ G).left) _, fun j => ?_⟩
  have q := hd j
  have q' := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n) (t j) r z J' l e
  refine (hc j).trans ?_
  rw [Units.val_mul, _root_.mul_assoc]
  refine congrArg (c.val * ·) ?_
  rw [Units.eq_inv_mul_iff_mul_eq]
  exact (congrArg (_ * ·) q'.symm).trans q.symm

theorem crd_of_moved : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : u.PtC) (v : S.J → PadicAlgCl p), Crd (LPow u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v → ρ.Crd (u.toA a) v := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u w _ t ht a v hv
  refine ⟨_, ?_, crd_move u.cart (T := TFK (R := u.V) (PadicAlgCl p)) (T₀ := baseOver (Sp S.R)) (spMap y₀)
    (base_eq u) ρ.P.isLB u.A.isLB w t ρ.s ht _ v hv⟩
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ u.φ) (ThetaPtMove.ptSecT_snd _)).trans ?_)
  exact Category.assoc _ _ _

end GlobalTheory.ZH.CrdMove
end
end

