import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0058
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0093
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionTranslationActsOnExpansions

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfCubicalPowIsoPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubicalQuasiFinite

theorem triv_translDiff_of_fixes {S : Scheme.{0}} {B Z : Over S} [GrpObj B] (φ : B ⟶ Z) {M : LB B.left}
    {H : LB Z.left} (hM : M.IsLB) (hH : H.IsLB) (hw : LBIso M (H.pull φ.left)) (x : 𝟙_ (Over S) ⟶ B)
    (hx : ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ) : Triv (translDiff B M x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (isGen_iff w).1 hw
  have e : translPt B x ≫ φ = snd _ B ≫ φ := by
    have e₀ : translPt B x = snd _ B ≫ ((toUnit B ≫ x) * 𝟙 B) := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique (snd _ B ≫ toUnit B) (fst _ B)]
      rfl
    rw [e₀, Category.assoc, hx]
  have e' : (translPt B x).left ≫ φ.left = (snd _ B).left ≫ φ.left := congrArg CommaMorphism.left e
  obtain ⟨c, hc, -⟩ := exists_gen hH
    (φ' := fun k : Fin 2 => (![(translPt B x).left, (snd _ B).left] : Fin 2 → _) k ≫ φ.left) (ε' := ![1, -1])
    (fun U _ f => (Fintype.prod_empty _).trans (by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e', zpow_one, zpow_neg,
        mul_inv_cancel])) (LB.oneGen H (Y := (𝟙_ (Over S) ⊗ B).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  exact exists_down hw hH hM c hc

theorem locallyQuasiFinite_of_pow_iso_pull : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (r n : ℕ), n.Prime → (n : K) ≠ 0 → ¬ n ∣ r → (∀ x : baseOver _ ⟶ B, x ^ n = 1 → Triv (translDiff B L.L x) → x = 1) → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z) (H : LB Z.left), H.IsLB → LBIso (pw L.L r) (H.pull φ.left) → LocallyQuasiFinite φ.left := by
  intro hcount K _ _ B _ _ hB L c r n hn hnK hnr hK Z _ _ φ H hH hw
  obtain ⟨C, W, hW, hC, hCW⟩ := GlobalTheory.Stabiliser.exists_closed_stabiliser K B hB Z φ
  have hfin : Finite C := by
    refine GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion hcount K B n hB hn hnK C W hW hCW fun x hx hxn => ?_
    have h₁ : Triv (translDiff B L.L (x ^ r)) :=
      ((GlobalTheory.Square.square_of_cubical _ B L c K (𝟙 _)).2 r x).1
        (triv_translDiff_of_fixes φ (isLB_pw L.isLB r) hH hw x ((hC x).1 hx))
    have h₂ : x ^ r = 1 := hK (x ^ r) (by
      change (x ^ r) ^ n = 1
      rw [← pow_mul, _root_.mul_comm, pow_mul, hxn, one_pow]) h₁
    have h₃ := pow_gcd_eq_one.2 ⟨hxn, h₂⟩
    rwa [(Nat.Prime.coprime_iff_not_dvd hn).2 hnr, pow_one] at h₃
  refine GlobalTheory.FiniteStabiliser.locallyQuasiFinite_of_finite_stabiliser K B hB Z φ ?_
  have e : {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ} = (C : Set _) := Set.ext fun x => (hC x).symm
  rw [e]
  exact Set.toFinite _

end GlobalTheory.CubicalQuasiFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemKernelOfLineBundleBaseChangeRepresentable
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem memKL_baseChange_rep : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → ∀ (H : Over S) (j : H ⟶ B), (∀ (T : Over S) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ (T' : Over S') (x : T' ⟶ (Over.pullback f).obj B), GlobalTheory.MemKL ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f)) x ↔ ∃ z : T' ⟶ (Over.pullback f).obj H, z ≫ (Over.pullback f).map j = x := by
  intro S S' f B _ L hL H j hrep T' x
  have h := isGrpPullback_pullback B f
  have hL' : (L.pull (pullback.fst B.hom f)).IsLB := LB.isLB_pull hL _
  rw [GlobalTheory.memKL_iff_memKL_push S S' f B _ _ L _ h hL hL' (GlobalTheory.lbIso_self hL') T' x, hrep]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z.left ≫ j.left = x.left ≫ pullback.fst B.hom f := congrArg (·.left) hz
    refine ⟨Over.homMk (pullback.lift z.left T'.hom (Over.w z)) (pullback.lift_snd _ _ _), ?_⟩
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w x).symm))
    rw [← hz']
    simp [pullback.lift_fst, pullback.lift_fst_assoc]
  · rintro ⟨z, rfl⟩
    refine ⟨Over.homMk (z.left ≫ pullback.fst H.hom f) ?_, ?_⟩
    · have := Over.w z
      simp only [Over.pullback_obj_hom] at this
      simp [pullback.condition, ← this]
    · refine Over.OverMorphism.ext ?_
      change (z.left ≫ pullback.fst H.hom f) ≫ j.left = (z.left ≫ ((Over.pullback f).map j).left) ≫ pullback.fst B.hom f
      simp [pullback.lift_fst]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

section Germ
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}

theorem gm_eq_of_isWt {V : G.left.Opens} {u : Γ(G.left, V)ˣ} {χ : X} (hu : IsWt i V u.val χ) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (h₁ : ((t ≫ i) * g).left z ∈ V) (h₂ : g.left z ∈ V) :
    gm ((t ≫ i) * g).left z V u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z V u := by
  let W : Z.left.Opens := ((t ≫ i) * g).left ⁻¹ᵁ V ⊓ g.left ⁻¹ᵁ V
  have hz : z ∈ W := ⟨h₁, h₂⟩
  let ρ : Over.mk (W.ι ≫ Z.hom) ⟶ Z := Over.homMk W.ι rfl
  have hW : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  have inj : Function.Injective (W.ι.appLE W ⊤ hW).hom := by
    rw [Scheme.Opens.ι_appLE]
    exact (ConcreteCategory.bijective_of_isIso
      (Z.left.presheaf.mapIso (eqToIso (by simp : W.ι ''ᵁ ⊤ = W)).op).hom).1
  have e₁ : ((ρ ≫ t) ≫ i) * (ρ ≫ g) = ρ ≫ ((t ≫ i) * g) := by rw [MonObj.comp_mul, Category.assoc]
  have a : ∀ {Y : Scheme.{0}} (r : Z.left ⟶ Y) (U : Y.Opens) (k : W ≤ r ⁻¹ᵁ U) (x : Γ(Y, U)ˣ) k',
      ((W.ι ≫ r).appLE U ⊤ k').hom x.val = (W.ι.appLE W ⊤ hW).hom (res k (pullU r U x)).val := fun r U k x k' =>
    (congrArg (fun q => q.hom x.val) (Scheme.Hom.appLE_comp_appLE W.ι r U W ⊤ k hW)).symm
  have b : ∀ {Y : Scheme.{0}} (r : Z.left ⟶ Y) (U : Y.Opens) (k : W ≤ r ⁻¹ᵁ U) (x : Γ(Y, U)ˣ),
      gm (𝟙 Z.left) z W (res k (pullU r U x)) = gm r z U x := fun r U k x =>
    (gm_res (𝟙 Z.left) z k hz _).trans ((gm_pull (𝟙 Z.left) r z U (k hz) x).trans (by simp only [Category.id_comp]))
  have h := hu _ (ρ ≫ t) (ρ ≫ g) (by rw [e₁]; exact fun x _ => x.2.1) (fun x _ => x.2.2)
  have c : ∀ (r r' : Over.mk (W.ι ≫ Z.hom) ⟶ G) (_ : r = r') k k',
      (r.left.appLE V ⊤ k).hom u.val = (r'.left.appLE V ⊤ k').hom u.val := by
    rintro r _ rfl k k'; rfl
  have d : (ρ ≫ t).left.appTop = (W.ι ≫ t.left).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [c _ _ e₁ _ (fun x _ => x.2.1), d] at h
  have h' := ((a _ V inf_le_left u _).symm.trans h).trans
    ((congrArg₂ (· * ·) (a t.left ⊤ le_top (charUnit S X χ) _) (a g.left V inf_le_right u _)).trans
      (map_mul _ _ _).symm)
  rw [← b _ V inf_le_left, ← b t.left ⊤ le_top, ← b g.left V inf_le_right, ← map_mul]
  exact congrArg _ (Units.ext (inj h'))

end Germ

section Flat
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {F : Y' ⟶ Y}

theorem mem_pull_linComb {y : Y'} {j : PUnit → K → L.ι} :
    y ∈ ((LB.LinComb L φ ε).pull F).U j ↔ y ∈ LB.wchart L (fun k => F ≫ φ k) (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 h) k,
    fun h => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k)⟩

theorem gm_pull_linComb (y : Y') (j j' : PUnit → K → L.ι) (h : y ∈ ((LB.LinComb L φ ε).pull F).U j)
    (h' : y ∈ ((LB.LinComb L φ ε).pull F).U j') :
    gm (𝟙 Y') y _ (((LB.LinComb L φ ε).pull F).g j j') =
      gm (𝟙 Y') y _ ((LB.LinComb L (fun k => F ≫ φ k) ε).g (j PUnit.unit) (j' PUnit.unit)) := by
  have a := gm_pull_g (LB.LinComb L φ ε) F (𝟙 Y') y j j' h h'
  have m : ∀ j : PUnit → K → L.ι, y ∈ ((LB.LinComb L φ ε).pull F).U j →
      (𝟙 Y' ≫ F) y ∈ LB.wchart L φ (j PUnit.unit) := fun j h => by
    rw [Category.id_comp]; exact (mem_pull (L := LB.LinComb L φ ε)).1 h
  have b := gm_linComb L φ ε (𝟙 Y' ≫ F) y (j PUnit.unit) (j' PUnit.unit) (m j h) (m j' h')
  have c := gm_linComb L (fun k => F ≫ φ k) ε (𝟙 Y') y (j PUnit.unit) (j' PUnit.unit) (mem_pull_linComb.1 h)
      (mem_pull_linComb.1 h')
  simp only [Category.assoc] at b
  exact a.trans (b.trans c.symm)

def flatGen (u : LB.Gen ((LB.LinComb L φ ε).pull F)) : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε) :=
  ⟨fun j => res (show LB.wchart L (fun k => F ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull F).U (fun _ => j) from
    fun _ h => (mem_pull_linComb (ε := ε) (j := fun _ => j)).2 h) (u.s fun _ => j)⟩

def unflatGen (v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)) : LB.Gen ((LB.LinComb L φ ε).pull F) :=
  ⟨fun j => res (fun _ h => mem_pull_linComb.1 h) (v.s (j PUnit.unit))⟩

theorem flatGen_isGen {u : LB.Gen ((LB.LinComb L φ ε).pull F)} (hu : u.IsGen) : (flatGen u).IsGen := fun j j' =>
  unit_ext fun y hy => by
    have m : y ∈ ((LB.LinComb L φ ε).pull F).U (fun _ => j) ⊓ ((LB.LinComb L φ ε).pull F).U (fun _ => j') :=
      ⟨(mem_pull_linComb (j := fun _ => j)).2 hy.1, (mem_pull_linComb (j := fun _ => j')).2 hy.2⟩
    have e := congrArg (gm (𝟙 _) y _) (hu (fun _ => j) (fun _ => j'))
    rw [map_mul, gm_res _ y _ m, gm_res _ y _ m, gm_pull_linComb y _ _ m.1 m.2] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

theorem unflatGen_isGen {v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)} (hv : v.IsGen) : (unflatGen v).IsGen :=
  fun j j' => unit_ext fun y hy => by
    have m : y ∈ (LB.LinComb L (fun k => F ≫ φ k) ε).U (j PUnit.unit) ⊓
        (LB.LinComb L (fun k => F ≫ φ k) ε).U (j' PUnit.unit) := ⟨mem_pull_linComb.1 hy.1, mem_pull_linComb.1 hy.2⟩
    have e := congrArg (gm (𝟙 _) y _) (hv (j PUnit.unit) (j' PUnit.unit))
    rw [map_mul, gm_res _ y _ m, gm_res _ y _ m] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_pull_linComb y _ _ hy.1 hy.2]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

end Flat

section Add
variable {S A Y : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {L : LB A} {F : G.left ⟶ Y}
  (hF : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ F = g.left ≫ F)
include hF

theorem val_flatGen {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ} {u : LB.Gen ((LB.LinComb L φ ε).pull F)}
    {χ : X} (hu : ∀ j, IsWt i _ (u.s j).val χ) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) {z : Z.left} {J}
    (hJ : Good L z J) : val (flatGen u) ((t ≫ i) * g).left z J =
      gm t.left z ⊤ (charUnit S X χ) * val (flatGen u) g.left z J := by
  have e : ∀ k, J (((t ≫ i) * g).left ≫ F ≫ φ k) = J (g.left ≫ F ≫ φ k) := fun k => by
    rw [← Category.assoc, hF, Category.assoc]
  have m₁ := hJ.mem (fun k => F ≫ φ k) ((t ≫ i) * g).left
  have m₂ := hJ.mem (fun k => F ≫ φ k) g.left
  rw [funext e] at m₁
  rw [val_of _ _ z J _ e]
  exact (gm_res _ z _ m₁ _).trans ((gm_eq_of_isWt (hu fun _ k => J (g.left ≫ F ≫ φ k)) t g z
    (mem_pull_linComb.2 m₁) (mem_pull_linComb.2 m₂)).trans
    (congrArg _ (gm_res _ z _ m₂ _).symm))

theorem isWt_unflatGen (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ}
    {v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)} (hv : v.IsGen) {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
      val v ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val v g.left z J) (j) :
    IsWt i _ ((unflatGen v).s j).val χ := isWt_of_gm _ _ fun Z t g z m₂ => by
  obtain ⟨J, hJ⟩ := exists_good_pt hL z
  have m₁ : ((t ≫ i) * g).left z ∈ ((LB.LinComb L φ ε).pull F).U j := by
    have := mem_pull.1 m₂
    refine mem_pull.2 ?_
    exact (congrArg (fun q => q z) (hF Z t g)).symm ▸ this
  have le : ((LB.LinComb L φ ε).pull F).U j ≤ LB.wchart L (fun k => F ≫ φ k) (j PUnit.unit) :=
    fun _ h => mem_pull_linComb.1 h
  have e₁ := (gm_res _ z le m₁ _).trans (gen_trans hv _ z (mem_pull_linComb.1 m₁) (hJ.mem _ _))
  have e₂ := (gm_res _ z le m₂ _).trans (gen_trans hv _ z (mem_pull_linComb.1 m₂) (hJ.mem _ _))
  refine e₁.trans (Eq.trans ?_ (congrArg _ e₂.symm))
  rw [mul_left_comm]
  refine congrArg₂ (· * ·) ?_ (h Z t g z J hJ)
  have e : ∀ k, ((t ≫ i) * g).left ≫ F ≫ φ k = g.left ≫ F ≫ φ k := fun k => by
    rw [← Category.assoc, hF, Category.assoc]
  refine Finset.prod_congr rfl fun k _ => ?_
  beta_reduce
  rw [e]

theorem exists_genWt_add (hL : L.IsLB) {K K' K'' K₀ : Type} [Fintype K] [Fintype K'] [Fintype K''] [Fintype K₀]
    {φ : K → (Y ⟶ A)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A)} {ε' : K' → ℤ} {φ'' : K'' → (Y ⟶ A)} {ε'' : K'' → ℤ}
    {φ₀ : K₀ → (Y ⟶ A)} {ε₀ : K₀ → ℤ} (hw : Triv (LB.LinComb L φ₀ ε₀))
    (hs : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ A) → U),
      (∏ k, f (φ k) ^ ε k) * (∏ k, f (φ' k) ^ ε' k) * ∏ k, f (φ₀ k) ^ ε₀ k = ∏ k, f (φ'' k) ^ ε'' k) {χ χ' : X}
    (h : ∃ u : LB.Gen ((LB.LinComb L φ ε).pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ)
    (h' : ∃ u : LB.Gen ((LB.LinComb L φ' ε').pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ') :
    ∃ u : LB.Gen ((LB.LinComb L φ'' ε'').pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val (χ + χ') := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨u, hu, hχ⟩ := h
  obtain ⟨u', hu', hχ'⟩ := h'
  obtain ⟨v, hv, H⟩ := exists_gen (φ' := fun k => F ≫ φ'' k) (ε' := ε'') hL
    (fun U _ f => (Fintype.prod_sum_type _).trans ((congrArg (· * _) (Fintype.prod_sum_type _)).trans
      (hs U fun q => f (F ≫ q)))) _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (flatGen_isGen hu) (flatGen_isGen hu'))
      (DVR.pullGen_isGen _ _ _ _ hw F))
  refine ⟨unflatGen v, unflatGen_isGen hv, isWt_unflatGen hF hL hv fun Z t g z J hJ => ?_⟩
  rw [H _ _ z J hJ, H _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, hF,
    val_flatGen hF hχ t g hJ, val_flatGen hF hχ' t g hJ, gm_charUnit, gm_charUnit, gm_charUnit, chV_add, map_mul]
  ac_rfl

end Add

theorem TQ.mul_comp_q {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X)
    (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) : ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Hom.one_def, MonObj.comp_one, _root_.one_mul]

theorem triv_square_sections {V : Type} [CommRing V] [IsLocalRing V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B]
    [IsCommMonObj B] {L : RigLB B} (κ : CubicalStr B L) (c c' : 𝟙_ _ ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 4) ![((toUnit B ≫ (c * c')) * 𝟙 B).left, 𝟙 B.left, ((toUnit B ≫ c) * 𝟙 B).left,
      ((toUnit B ≫ c') * 𝟙 B).left] ![1, 1, -1, -1]) := by
  obtain ⟨w, hw⟩ := GlobalTheory.Square.triv_square (t := 𝟙 (Spec (CommRingCat.of V))) κ c c'
  let ρ : B ⟶ 𝟙_ _ ⊗ B := lift (toUnit B) (𝟙 B)
  have e : ∀ x : 𝟙_ _ ⟶ B, ρ.left ≫ (translPt (T := 𝟙_ _) B x).left = ((toUnit B ≫ x) * 𝟙 B).left := fun x => by
    rw [← Over.comp_left]
    change (ρ ≫ ((fst _ B ≫ x) * snd _ B)).left = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have e' : ρ.left ≫ (snd (𝟙_ _) B).left = 𝟙 B.left := by rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨u, hu, -⟩ := exists_gen (φ' := ![((toUnit B ≫ (c * c')) * 𝟙 B).left, 𝟙 B.left, ((toUnit B ≫ c) * 𝟙 B).left,
      ((toUnit B ≫ c') * 𝟙 B).left]) (ε' := ![1, 1, -1, -1]) L.isLB (fun U _ f => Finset.prod_congr rfl fun k _ => by
      fin_cases k
      exacts [congrArg (fun q => f q ^ (1 : ℤ)) (e _), congrArg (fun q => f q ^ (1 : ℤ)) e',
        congrArg (fun q => f q ^ (-1 : ℤ)) (e _), congrArg (fun q => f q ^ (-1 : ℤ)) (e _)])
    _ (DVR.pullGen_isGen _ _ _ _ hw ρ.left)
  exact ⟨u, hu⟩

theorem repWt_add : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ χ' : s.X) (c c' : 𝟙_ _ ⟶ a.B) (e : ℕ), a.RepWt c χ e → a.RepWt c' χ' e → a.RepWt (c * c') (χ + χ') e := by
  intro V _ _ _ A G _ _ s t a χ χ' c c' e h h'
  refine exists_genWt_add (fun Z x g => ?_) a.M.L.isLB (GlobalTheory.Square.triv_inv (triv_square_sections a.M.c c c'))
    (fun U _ f => ?_) h h'
  · rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, TQ.mul_comp_q]
  · simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtUnique
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem TQ.exists_genWt_pull_comp {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {Y : Scheme.{0}} (N : LB Y) (b : Q.B.left ⟶ Y) {χ : X} (u : LB.Gen (N.pull (Q.q.left ≫ b))) (hu : u.IsGen)
    (hw : ∀ j, IsWt Q.i _ (u.s j).val χ) : ∃ t, Q.GenWt (N.pull b) t χ := by
  have le : ∀ J : PUnit → PUnit → N.ι,
      ((N.pull b).pull Q.q.left).U J ≤ (N.pull (Q.q.left ≫ b)).U (J PUnit.unit) :=
    fun J y hy => mem_pull.2 ((mem_pull (L := N) (F := b)).1 ((mem_pull (L := N.pull b)).1 hy))
  refine ⟨⟨fun J => res (le J) (u.s (J PUnit.unit))⟩, fun i j => Geo.Tor.unit_ext fun y hy => ?_,
    fun J => (hw _).res (le J)⟩
  have hm : (𝟙 G.left : G.left ⟶ G.left) y ∈
      (N.pull (Q.q.left ≫ b)).U (i PUnit.unit) ⊓ (N.pull (Q.q.left ≫ b)).U (j PUnit.unit) := ⟨le i hy.1, le j hy.2⟩
  have h1 := congrArg (gm (𝟙 G.left) y _) (hu (i PUnit.unit) (j PUnit.unit))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_pull_g N _ (𝟙 _) y _ _ hm.1 hm.2] at h1
  have h2 := (gm_pull_g (N.pull b) Q.q.left (𝟙 _) y i j hy.1 hy.2).trans
    (gm_pull_g N b (𝟙 _ ≫ Q.q.left) y _ _ ((mem_pull (L := N.pull b)).1 hy.1)
      ((mem_pull (L := N.pull b)).1 hy.2))
  rw [Category.assoc] at h2
  rw [map_mul, gm_res _ y inf_le_left hy, gm_res _ y inf_le_right hy]
  exact (gm_res (𝟙 _) y (le i) hy.1 _).trans
    (h1.trans (congrArg₂ (· * ·) h2.symm (gm_res (𝟙 _) y (le j) hy.2 _).symm))

theorem hasGen_sum_of_lbIso {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (H : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    KerPow.HasGen L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k) := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ j : K' ⊕ K → L.ι, LB.wchart L (Sum.elim φ' φ) j ≤
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inr k)⟩
  refine gen_chartPull (A' := LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)) (h := 𝟙 Y)
    (A := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε))
    ⟨fun j => (j ∘ Sum.inl, j ∘ Sum.inr), le, fun y p q hp hq => ?_⟩ w hw
  refine (gm_linComb L _ _ (𝟙 Y) y p q hp hq).trans (Eq.trans ?_
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr)
      ⟨le p hp, le q hq⟩).symm)
  refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ' ε' (𝟙 Y) y _ _ (le p hp).1 (le q hq).1)
    (gm_linComb L φ ε (𝟙 Y) y _ _ (le p hp).2 (le q hq).2)).symm
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

theorem section_eq_of_lbIso {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (hK : KTriv B L)
    (c c' : 𝟙_ _ ⟶ B) {T : Over S} {Y : Scheme.{0}} {b : Y ⟶ B.left} {p : Y ⟶ T.left}
    (pb : IsPullback b p B.hom T.hom)
    (H : LBIso ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull b)
      ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c') * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull b)) :
    toUnit T ≫ c = toUnit T ≫ c' := by
  have H₁ := hasGen_sum_of_lbIso L _ _ _ _ (H.chartPull (chartPullIn _ _ _ _) (chartPullIn _ _ _ _))
  let x : T ⟶ B := toUnit T ≫ c
  let y : T ⟶ B := toUnit T ≫ c'
  let w : T ⊗ B ⟶ B := (fst T B ≫ y⁻¹) * snd T B
  let h : (T ⊗ B).left ⟶ Y := pb.lift w.left (fst T B).left ((Over.w w).trans (Over.w (fst T B)).symm)
  have hb : h ≫ b = w.left := pb.lift_fst _ _ _
  have key : ∀ d : 𝟙_ _ ⟶ B, w ≫ ((toUnit B ≫ d) * 𝟙 B) = translPt B ((toUnit T ≫ d) * y⁻¹) := fun d => by
    change _ = (fst T B ≫ ((toUnit T ≫ d) * y⁻¹)) * snd T B
    rw [MonObj.comp_mul, MonObj.comp_mul, Category.comp_id, _root_.mul_assoc, ← Category.assoc, ← Category.assoc,
      toUnit_unique (w ≫ toUnit B) (fst T B ≫ toUnit T)]
  have k₁ : w ≫ ((toUnit B ≫ c') * 𝟙 B) = snd T B := by
    rw [key, mul_inv_cancel, KerPow.translPt_one]
  have H₂ := H₁.pull h (φ' := Sum.elim ![(snd T B).left, w.left] ![(translPt B (x * y⁻¹)).left, w.left]) fun k => by
    rcases k with k | k <;> refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb).trans ?_) <;> fin_cases k
    exacts [congrArg (fun q => q.left) k₁, Category.comp_id _, congrArg (fun q => q.left) (key c), Category.comp_id _]
  have triv : KerPow.HasGen L (Y := (T ⊗ B).left) (K := Fin 0) ![] ![] :=
    KerPow.hasGen_of_trivial hL fun U _ h => by simp
  have H₃ := H₂.comb hL triv (φ'' := ![(translPt B (x * y⁻¹)).left, (snd T B).left]) (ε'' := ![1, -1])
    fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
      apply Additive.ofMul.injective
      simp
      abel
  exact mul_inv_eq_one.1 (KerPow.eq_one_of_locGen hK (x * y⁻¹) fun _ => ⟨⊤, trivial, H₃.pull _ fun _ => rfl⟩)

theorem section_eq_of_isWt {S S' : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (hK : KTriv B L)
    (c c' : 𝟙_ _ ⟶ B) {X : Type} [AddCommGroup X] {G : Over S'} [GrpObj G] (Q : TQ G X) {f : S' ⟶ S}
    {b : Q.B.left ⟶ B.left} (pb : IsPullback b Q.B.hom B.hom f) (χ : X)
    (hc : ∃ u : LB.Gen ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull
      (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ)
    (hc' : ∃ u : LB.Gen ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c') * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull
      (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ) :
    (toUnit (Over.mk f) ≫ c).left = (toUnit (Over.mk f) ≫ c').left := by
  obtain ⟨u, hu, hw⟩ := hc
  obtain ⟨u', hu', hw'⟩ := hc'
  obtain ⟨v, hv⟩ := Q.exists_genWt_pull_comp _ b u hu hw
  obtain ⟨v', hv'⟩ := Q.exists_genWt_pull_comp _ b u' hu' hw'
  have H := lbIso_of_genWt _ _ _ Q _ _ v v' χ (pull_isLB (DVR.linComb_isLB _ hL _ _) _)
    (pull_isLB (DVR.linComb_isLB _ hL _ _) _) hv hv'
  exact congrArg (fun q => q.left) (section_eq_of_lbIso hL hK c c' (T := Over.mk f) pb H)

theorem repWt_unique : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ (χ : s.X) (c c' : 𝟙_ _ ⟶ a.B), (∀ e, a.RepWt c χ e) → (∀ e, a.RepWt c' χ e) → c = c' := by
  intro _ V _ _ _ A G _ _ s t a hK χ c c' hc hc'
  have := s.cdvr.2.1
  refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isHausdorff (IsLocalRing.maximalIdeal V) fun e => ?_)
  obtain ⟨pb, -⟩ := a.b_pb e
  have k := section_eq_of_isWt a.M.L.isLB hK c c' (t.l e).Q pb.1 χ (hc e) (hc' e)
  rw [Over.comp_left, Over.comp_left, Rosenlicht.toUnit_left] at k
  exact k

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocalStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_regular_flat_of_smooth : ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ x : X, IsClosed ({x} : Set X) → ∀ σ : V →+* X.presheaf.stalk x, X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → IsNoetherianRing (X.presheaf.stalk x) ∧ σ.Flat ∧ IsRegularLocalRing (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal V).map σ) ∧ ringKrullDim (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal V).map σ) = g := by
  first | exact @GlobalTheory.StabFlat.stalk_of_smooth_local | exact GlobalTheory.StabFlat.stalk_of_smooth_local | (intros; apply GlobalTheory.StabFlat.stalk_of_smooth_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionFunctionalEquationDegreeOne
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU

theorem fe_one_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → U.FE (Kbar V) 1) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U θ f hθ hψ t s hts
  obtain ⟨hp, hq⟩ := PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hp θ
  obtain ⟨s₀, hs₀, -⟩ := hq f
  obtain ⟨c, hc⟩ := (GlobalTheory.T.expF_of_theta_degree_one h₁ h₂ V hV D A G U θ f hθ th s₀ hth hs₀).2.2 t s hts
  exact famFE_one_of_psiRel h₁.globalFns V D (Kbar V) s₀ s c (GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field V D (Kbar V) f s₀ hs₀ hψ) hc

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionTranslationActsOnExpansionsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionTranslation_acts_on_expansions : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W) (N : ℕ), 1 ≤ N → ∀ (x : TA V W ⟶ G) (g' : GtPt D (TA V W)) (g : GtPtF D F) (xA : TFK (R := V) F ⟶ A.A), x ^ N = 1 → U.Red x g' → GtPt.IsPullF F φ.left g' g → U.SamePt xA (φ ≫ x) → U.Acts F N 0 g xA) := by
  first | exact @GlobalTheory.UU.Transl.main | exact GlobalTheory.UU.Transl.main | (intros; apply GlobalTheory.UU.Transl.main <;> assumption)
end

