import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0060
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0061
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeEighthPowerOfMatrixActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_eighth_power_of_matrix_action : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsAbelianScheme G → (∀ m, IsMonHom (ρ m)) → (∀ m m', ρ (m * m') = ρ m' ≫ ρ m) → (∀ m m', ρ (m + m') = ρ m * ρ m') → ρ 1 = 𝟙 G → ∃ (A : Over S) (_ : GrpObj A) (pr : Fin 8 → (G ⟶ A)), IsAbelianScheme A ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧ ∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := by
  first | exact @GlobalTheory.MatrixPower.abelianScheme_matrix_power | exact GlobalTheory.MatrixPower.abelianScheme_matrix_power | (intros; apply GlobalTheory.MatrixPower.abelianScheme_matrix_power <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ChartPullCompOfPullPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

def chartPullCompOfPullPull {X Y Z : Scheme.{0}} (M : LB X) (π : Y ⟶ X) (φ : Z ⟶ Y) :
    ChartPull (M.pull (φ ≫ π)) ((M.pull π).pull φ) (𝟙 Z) where
  idx j := fun _ => j
  le j := RepBC.le₂ M π φ j
  g y j j' hj hj' := by
    have h := RepBC.le₂ M π φ j hj
    have h' := RepBC.le₂ M π φ j' hj'
    refine (gm_pull_g M (φ ≫ π) (𝟙 Z) y j j' hj hj').trans (Eq.symm ?_)
    refine (gm_pull_g (M.pull π) φ (𝟙 Z) y (fun _ => j) (fun _ => j') h h').trans ?_
    exact gm_pull_g M π (𝟙 Z ≫ φ) y j j' (mem_pull.1 h) (mem_pull.1 h')

theorem lbIso_pullPull_iff {X Y Z : Scheme.{0}} (A : LB Z) (M : LB X) (π : Y ⟶ X) (φ : Z ⟶ Y) :
    LBIso A ((M.pull π).pull φ) ↔ LBIso A (M.pull (φ ≫ π)) :=
  ⟨LBIso.chartPull (chartPullId A) (chartPullCompOfPullPull M π φ),
    LBIso.chartPull (chartPullId A) (chartPullLinComb M π (fun _ : PUnit => φ) (fun _ => φ ≫ π) (fun _ => 1) (𝟙 Z)
      fun _ => (Category.id_comp _).symm)⟩

theorem fam_baseChange : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec) (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (R' : Type) [CommRing R'] (ρ : R →+* R') (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → Fam b Mat κ β v m M th sc → ∃ (th' : Ix g (N' ^ 2) → (M.pull π).Sec) (sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z')), Fam b Mat κ (ρ.comp β) (fun a => ρ (v a)) m (M.pull π) th' sc' ∧ ∀ (K : Type) [Field K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ Z'.left), Fib m (M.pull π) th' sc' x t φ → Fib m M th sc (x.comp ρ) t (φ ≫ π) := by
  intro o _ g N' J b Mat κ R _ β v m Z M th sc R' _ ρ Z' π hp ⟨⟨I, p, hrep, hco⟩, hflat, hfib⟩
  obtain ⟨th', hrep', hc⟩ := RepBC.projRep_baseChange R R' _ ρ I _ _ _ _ π M th hrep hp
  have hw : ∀ h, (spMap ρ ≫ (sc h).left) ≫ Z.hom = 𝟙 _ ≫ spMap ρ := fun h => by
    rw [Category.assoc, Over.w (sc h), Category.id_comp]
    exact Category.comp_id _
  let sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z') := fun h =>
    Over.homMk (hp.lift (spMap ρ ≫ (sc h).left) (𝟙 _) (hw h)) (hp.lift_snd _ _ _)
  have hsc : ∀ h, (sc' h).left ≫ π = spMap ρ ≫ (sc h).left := fun h => hp.lift_fst _ _ _
  have hsc' : ∀ h, (sc' h).left ≫ Z'.hom = 𝟙 _ := fun h => hp.lift_snd _ _ _
  refine ⟨th', sc', ⟨⟨_, fun h a => ρ (p h a), hrep', fun h => (hc _ _ _).2 ?_⟩,
    MorphismProperty.of_isPullback (P := @Flat) hp hflat, ?_⟩, ?_⟩
  · rw [hsc]
    exact Coord.baseChange (hco h) ρ
  · intro K _ _ x s t ht
    obtain ⟨φ, h1, ⟨σ, hσ, h2⟩, h3, h4⟩ := hfib K (x.comp ρ) s t ((good_comp _ _ _).1 ht)
    have hw' : φ ≫ Z.hom = (t.A.hom ≫ spMap x) ≫ spMap ρ := by
      rw [h1.w, NearBuild.spMap_comp, Category.assoc]
    have e1 : hp.lift φ _ hw' ≫ π = φ := hp.lift_fst _ _ _
    have e2 : hp.lift φ _ hw' ≫ Z'.hom = t.A.hom ≫ spMap x := hp.lift_snd _ _ _
    generalize hp.lift φ _ hw' = φ' at e1 e2
    subst e1
    refine ⟨φ', IsPullback.of_right (by rw [← NearBuild.spMap_comp]; exact h1) e2 hp, ⟨σ, hσ, fun T _ y w => ?_⟩,
      (lbIso_pullPull_iff _ _ _ _).2 h3, fun h => ?_⟩
    · rw [h2 T y w, hc, Category.assoc, Category.assoc]
    · apply hp.hom_ext
      · rw [Category.assoc, h4, NearBuild.spMap_comp]
        erw [Category.assoc, Category.assoc, hsc]
      · rw [Category.assoc, e2, ← Category.assoc, Over.w (t.lab h ^ N')]
        erw [Category.assoc, hsc', Category.id_comp]
  · rintro K _ x s t φ ⟨h1, ⟨σ, hσ, h2⟩, h3, h4⟩
    refine ⟨by rw [NearBuild.spMap_comp]; exact h1.paste_horiz hp, ⟨σ, hσ, fun T _ y w => ?_⟩,
      (lbIso_pullPull_iff _ _ _ _).1 h3, fun h => ?_⟩
    · rw [h2 T y w, hc, Category.assoc, Category.assoc]
    · rw [← Category.assoc, h4, NearBuild.spMap_comp]
      erw [Category.assoc, Category.assoc, hsc]

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CommutatorPairingE8SharpLevelPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_e8Sharp_levelPoints : Out.Laws → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), IsSharpBasis W bas → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → ∀ (K : Type) [Field K] (p : Sp K ⟶ S) (β : o →+* K) (z : Kˣ), p ≫ s = spMap β → (z : K) = β b.ζ → ∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ t.A), (∀ u, y ≫ pr u = toUnit _ ≫ lev (X u)) → (∀ u, y' ≫ pr u = toUnit _ ≫ lev (Y u)) → Out.WeilIs t.A t.L k y y' (unitOn z ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v)) := by
  first | exact @GlobalTheory.weilIs_sharp_levelPoints | exact GlobalTheory.weilIs_sharp_levelPoints | (intros; apply GlobalTheory.weilIs_sharp_levelPoints <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CubeDescent

section Descent

variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_gen_comp (L : LB X) (F : X' ⟶ X) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb (L.pull F) φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε), u.IsGen := by
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => φ k ≫ F) j ≤
      LB.wchart (L.pull F) φ (fun k _ => j k) := fun j y hy =>
    Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (t.s fun k _ => j k)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  refine (gm_res (𝟙 Y) y (le j) hj _).trans ((gen_trans ht (𝟙 Y) y (le j hj) (le j' hj')).trans
    (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y (le j') hj' _).symm))
  refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
  exact (gm_pull_g L F (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
    (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans (by rw [Category.assoc])

theorem gs_appLE {Z : Scheme.{0}} (g : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)) (z : Z) :
    gs (𝟙 Z) z ⊤ ((g.appLE U ⊤ h).hom a) = gs g z U a :=
  (gs_res (𝟙 Z) z h trivial ((g.app U).hom a)).trans
    ((gs_pull (𝟙 Z) g z U (h (x := z) trivial) a).trans (by rw [Category.id_comp]))

theorem exists_gen_descend {L : LB X} (hL : L.IsLB) (π : Y' ⟶ Y) [Flat π] [Surjective π]
    [QuasiCompact π] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen)
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ Y') (z : Z) (J), Good L z J → g₁ ≫ π = g₂ ≫ π →
      val u g₁ z J = val u g₂ z J) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j),
      (π.app _).hom a = (res (le j) (u.s j)).val := by
    intro j
    refine FunDescent.exists_app_eq π _ _ fun Z g₁ g₂ h₁ h₂ e => fn_ext fun z _ => ?_
    rw [gs_appLE, gs_appLE, gs_unit _ _ _ (h₁ (x := z) trivial), gs_unit _ _ _ (h₂ (x := z) trivial)]
    choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
    have c₁ := gen_trans hu g₁ z (le j (h₁ (x := z) trivial)) (Good.mem hI _ g₁)
    have c₂ := gen_trans hu g₂ z (le j (h₂ (x := z) trivial)) (Good.mem hI _ g₂)
    have c₃ : trF (fun k => π ≫ φ k) ε g₁ z j (fun k => I (g₁ ≫ π ≫ φ k)) =
        trF (fun k => π ≫ φ k) ε g₂ z j (fun k => I (g₂ ≫ π ≫ φ k)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : g₁ ≫ π ≫ φ k = g₂ ≫ π ≫ φ k := by rw [reassoc_of% e]
      show gm (g₁ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (g₁ ≫ π ≫ φ k))) (L.g (j k) (I (g₁ ≫ π ≫ φ k))) ^ _ =
        gm (g₂ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (g₂ ≫ π ≫ φ k))) (L.g (j k) (I (g₂ ≫ π ≫ φ k))) ^ _
      rw [this]
    exact congrArg Units.val ((gm_res g₁ z (le j) (h₁ (x := z) trivial) _).trans
      ((c₁.trans ((congrArg₂ (· * ·) c₃ (h Z g₁ g₂ z I hI e)).trans c₂.symm)).trans
        (gm_res g₂ z (le j) (h₂ (x := z) trivial) _).symm))
  choose a ha using desc
  have hun : ∀ j, IsUnit (a j) := fun j =>
    FunDescent.isUnit_of_isUnit_app π _ _ (ha j ▸ Units.isUnit _)
  have hv : ∀ j (y : Y'), π y ∈ LB.wchart L φ j → gm π y (LB.wchart L φ j) (hun j).unit =
      gm (𝟙 Y') y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j y hy
    have e : pullU π _ (hun j).unit = res (le j) (u.s j) := Units.ext (ha j)
    refine Eq.trans ?_ ((gm_pull (𝟙 Y') π y _ hy _).symm.trans
      ((congrArg (gm (𝟙 Y') y _) e).trans (gm_res (𝟙 Y') y (le j) hy _)))
    rw [Category.id_comp]
  refine ⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext
    (FunDescent.app_injective π (LB.wchart L φ j ⊓ LB.wchart L φ j') ?_)⟩
  refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
  have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
  refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
  rw [Category.id_comp]
  refine ((gm_res π y _ hy' _).trans ((hv j y hy'.1).trans
    (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε π y j j' hy'.1 hy'.2).trans ?_)
    ((gm_res π y _ hy' _).trans (hv j' y hy'.2)))
  simp only [trF, Category.id_comp]

end Descent

section Group

variable {S X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {Q : Over S}
  {φ : K → (Q.left ⟶ X)} {ε : K → ℤ}

theorem val_eq_of_section (hL : L.IsLB) {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {P T : Over S} (p : P ⟶ T) (e : T ⟶ P) (he : e ≫ p = 𝟙 T)
    (hp : Function.Surjective p.left.appTop.hom) (a a' : P ⟶ Q)
    (hF : FormEq (fun k => a'.left ≫ φ k) ε (fun k => a.left ≫ φ k) ε)
    (h : ∀ y J, Good L y J → val u (e ≫ a).left y J = val u (e ≫ a').left y J)
    {T' : Over S} (ρ : T' ⟶ P) (z : T'.left) (J) (hJ : Good L z J) :
    val u (ρ ≫ a).left z J = val u (ρ ≫ a').left z J := by
  have := gen_unique' hL hF p.left e.left (congrArg (fun q => q.left) he) hp
    (DVR.pullGen_isGen _ _ _ _ hu a.left) (DVR.pullGen_isGen _ _ _ _ hu a'.left)
    (fun y J hJ => by rw [val_pull hJ, val_pull hJ]; exact h y J hJ) _ ρ.left z J hJ
  rw [val_pull hJ, val_pull hJ] at this
  exact this

variable {A : Over S} [GrpObj A]

theorem val_eq_of_axis (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (σ : A ⊗ A ⊗ A ⟶ Q)
    (H₁ : FormEq (fun k => (lift (1 : A ⟶ A) (lift 1 1) ≫ σ).left ≫ φ k) ε
      (fun k => (lift (𝟙 A) (lift 1 1) ≫ σ).left ≫ φ k) ε)
    {T : Over S} (x x' : T ⟶ A)
    (H₂ : ∀ (T' : Over S) (ρ : T' ⟶ T) (y w : T' ⟶ A) (k : K),
      (lift (ρ ≫ x') (lift y w) ≫ σ).left ≫ φ k = (lift (ρ ≫ x) (lift y w) ≫ σ).left ≫ φ k)
    (y w : T ⟶ A) (z : T.left) (J) (hJ : Good L z J) :
    val u (lift x (lift y w) ≫ σ).left z J = val u (lift x' (lift y w) ≫ σ).left z J := by
  have face : ∀ (v : T ⟶ A) (z : T.left) (J), Good L z J →
      val u (lift v (lift 1 1) ≫ σ).left z J = val u (lift (1 : T ⟶ A) (lift 1 1) ≫ σ).left z J := by
    intro v z J hJ
    have := val_eq_of_section hL hu (toUnit A) η[A] (toUnit_unique _ _) (hG _ _ hA).2
      (lift (𝟙 A) (lift 1 1) ≫ σ) (lift (1 : A ⟶ A) (lift 1 1) ≫ σ) H₁ (fun y J _ => by
        congr 2
        simp [comp_lift_assoc, Hom.one_def]) v z J hJ
    simpa only [comp_lift_assoc, comp_lift, Category.comp_id, MonObj.comp_one] using this
  have := val_eq_of_section hL hu (snd A (A ⊗ T) ≫ snd A T) (lift 1 (lift 1 (𝟙 T))) (by simp)
    (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
    (lift ((snd A (A ⊗ T) ≫ snd A T) ≫ x) (lift (fst _ _) (snd _ _ ≫ fst _ _)) ≫ σ)
    (lift ((snd A (A ⊗ T) ≫ snd A T) ≫ x') (lift (fst _ _) (snd _ _ ≫ fst _ _)) ≫ σ)
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (H₂ _ _ _ _ k))
    (fun z J hJ => by
      have e := (face x z J hJ).trans (face x' z J hJ).symm
      simpa only [comp_lift_assoc, comp_lift, lift_fst, lift_snd_assoc, lift_snd, Category.assoc,
        Category.id_comp] using e)
    (lift y (lift w (𝟙 T))) z J hJ
  simpa only [comp_lift_assoc, comp_lift, lift_fst, lift_snd_assoc, lift_snd, Category.assoc,
    Category.id_comp] using this

variable {B : Over S} [GrpObj B] [IsCommMonObj B]

theorem exists_gen_theta [IsCommMonObj A] (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    (ψ : A ⟶ B) [IsMonHom ψ] [Flat ψ.left] [Surjective ψ.left] [QuasiCompact ψ.left]
    {M : LB B.left} (hM : M.IsLB) (t : LB.Gen (Theta A (M.pull ψ.left))) (ht : t.IsGen) :
    ∃ t : LB.Gen (Theta B M), t.IsGen := by
  have := AbelianQuotient.flat_tensorHom ψ ψ
  have := AbelianQuotient.surjective_tensorHom ψ ψ
  have := AbelianQuotient.quasiCompact_tensorHom ψ ψ
  have := AbelianQuotient.flat_tensorHom ψ (ψ ⊗ₘ ψ)
  have := AbelianQuotient.surjective_tensorHom ψ (ψ ⊗ₘ ψ)
  have := AbelianQuotient.quasiCompact_tensorHom ψ (ψ ⊗ₘ ψ)
  let π : G3 A ⟶ G3 B := ψ ⊗ₘ ψ ⊗ₘ ψ
  have hπ : ∀ {T : Over S} (x y w : T ⟶ A),
      lift x (lift y w) ≫ π = lift (x ≫ ψ) (lift (y ≫ ψ) (w ≫ ψ)) := fun x y w => by
    simp [π, lift_map]
  obtain ⟨u₀, hu₀⟩ := exists_gen_comp M ψ.left (thφ A (x3 A)) thε t ht
  have hφ : ∀ I, thφ A (x3 A) I ≫ ψ.left = π.left ≫ thφ B (x3 B) I := fun I => by
    let ρ : (G3 A ⟶ A) →* (G3 A ⟶ B) := MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ
    exact congrArg (fun q => q.left) ((psum_hom ρ (x3 A) I.down).trans
      ((congrArg (fun q => psum B q I.down) (funext fun i => by
        fin_cases i <;> simp [ρ, π, preHom, x3])).trans (psum_hom (preHom π) (x3 B) I.down).symm))
  obtain ⟨u, hu, -⟩ := exists_gen hM (φ' := fun I => π.left ≫ thφ B (x3 B) I) (ε' := thε)
    (fun U _ h => Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (hφ I)) u₀ hu₀
  have hc : ∀ {T : Over S} (x y w : T ⟶ A) (I : thK),
      (lift x (lift y w)).left ≫ π.left ≫ thφ B (x3 B) I =
        (lift (x ≫ ψ) (lift (y ≫ ψ) (w ≫ ψ))).left ≫ thφ B (x3 B) I := fun x y w I => by
    rw [← Category.assoc, ← Over.comp_left, hπ]
  have hp : ∀ (x y w : A ⟶ A), (y = 1 ∧ w = 1 ∨ x = 1 ∧ w = 1 ∨ x = 1 ∧ y = 1) →
      ∀ (U : Type) [CommGroup U] (h : (A.left ⟶ B.left) → U),
      ∏ I, h ((lift x (lift y w)).left ≫ π.left ≫ thφ B (x3 B) I) ^ thε I = 1 := by
    intro x y w H U _ h
    refine (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (hc x y w I)).trans
      ((prod_cub _ _ _ h).trans ?_)
    apply Additive.ofMul.injective
    rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [MonObj.one_comp, _root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;>
      abel
  refine exists_gen_descend hM π.left (thφ B (x3 B)) thε u hu fun Z g₁ g₂ z J hJ e => ?_
  let T : Over S := Over.mk (g₂ ≫ (G3 A).hom)
  let k₂ : T ⟶ G3 A := Over.homMk g₂ rfl
  let k₁ : T ⟶ G3 A := Over.homMk g₁ (by
    change g₁ ≫ (G3 A).hom = g₂ ≫ (G3 A).hom
    rw [← Over.w π, reassoc_of% e])
  have e' : k₁ ≫ π = k₂ ≫ π := Over.OverMorphism.ext e
  obtain ⟨x, y, w, h₁⟩ : ∃ x y w, k₁ = lift x (lift y w) :=
    ⟨k₁ ≫ fst _ _, k₁ ≫ snd _ _ ≫ fst _ _, k₁ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
  obtain ⟨x', y', w', h₂⟩ : ∃ x y w, k₂ = lift x (lift y w) :=
    ⟨k₂ ≫ fst _ _, k₂ ≫ snd _ _ ≫ fst _ _, k₂ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
  rw [h₁, h₂, hπ, hπ] at e'
  have ex : x ≫ ψ = x' ≫ ψ := by simpa using e' =≫ fst _ _
  have ey : y ≫ ψ = y' ≫ ψ := by simpa using e' =≫ snd _ _ ≫ fst _ _
  have ew : w ≫ ψ = w' ≫ ψ := by simpa using e' =≫ snd _ _ ≫ snd _ _
  change val u k₁.left z J = val u k₂.left z J
  rw [h₁, h₂]
  let σ₁ : A ⊗ A ⊗ A ⟶ G3 A := lift (snd _ _ ≫ fst _ _) (lift (fst _ _) (snd _ _ ≫ snd _ _))
  let σ₂ : A ⊗ A ⊗ A ⟶ G3 A := lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _) (fst _ _))
  have s₁ : ∀ {T : Over S} (a b c : T ⟶ A), lift a (lift b c) ≫ σ₁ = lift b (lift a c) :=
    fun a b c => by simp [σ₁]
  have s₂ : ∀ {T : Over S} (a b c : T ⟶ A), lift a (lift b c) ≫ σ₂ = lift b (lift c a) :=
    fun a b c => by simp [σ₂]
  have v₀ := val_eq_of_axis hG hA hM hu (𝟙 _) (fun U _ h => by
      simp only [Category.comp_id]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).symm) x x'
    (fun T' ρ a b I => by
      rw [Category.comp_id, Category.comp_id]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ex]) (hc _ _ _ I).symm)) y w z J hJ
  have v₁ := val_eq_of_axis hG hA hM hu σ₁ (fun U _ h => by
      simp only [s₁]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inr (.inl ⟨rfl, rfl⟩)) U h).symm) y y'
    (fun T' ρ a b I => by
      rw [s₁, s₁]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ey]) (hc _ _ _ I).symm)) x' w z J hJ
  have v₂ := val_eq_of_axis hG hA hM hu σ₂ (fun U _ h => by
      simp only [s₂]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inr (.inr ⟨rfl, rfl⟩)) U h).symm) w w'
    (fun T' ρ a b I => by
      rw [s₂, s₂]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ew]) (hc _ _ _ I).symm)) x' y' z J hJ
  rw [Category.comp_id, Category.comp_id] at v₀
  rw [s₁, s₁] at v₁
  rw [s₂, s₂] at v₂
  exact v₀.trans (v₁.trans v₂)

end Group

end GlobalTheory.CubeDescent

namespace GlobalTheory

theorem cube_descends_along_etale_isogeny :
    Out.GlobalFnsSt → ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] [IsCommMonObj B] (ψ : A ⟶ B) (M : LB B.left) [IsCommMonObj A], IsAbelianScheme A → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∃ t : LB.Gen (Theta A (M.pull ψ.left)), t.IsGen) → ∃ t : LB.Gen (Theta B M), t.IsGen := by
  intro hG k _ _ A B _ _ _ ψ M _ hA _ hM _ _ _ _ ⟨t, ht⟩
  exact CubeDescent.exists_gen_theta hG hA ψ hM t ht

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseE8SharpAfterAdjoiningAllMatricesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_e8Sharp_after_adjoining_all_matrices : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s), (∀ u v, ∃ j, a j = Matrix.single u v 1) → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ t' : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s, Dense (fromSet em (SharpClass (b := b) W (Sum.elim a id) bas em) t') ∧ ∀ c : SiegPre h k (b.ζ : o) s, IsSharp W (Sum.elim a id) bas t' c → IsSharp W a bas t c := by
  first | exact @GlobalTheory.exists_dense_sharp_all_matrices | exact GlobalTheory.exists_dense_sharp_all_matrices | (intros; apply GlobalTheory.exists_dense_sharp_all_matrices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DetSpread

theorem exists_factor {S : Scheme.{0}} {R K : Type} [CommRing R] [Field K] (j : Sp R ⟶ S) [IsOpenImmersion j]
    (x : Sp K ⟶ S) (q : PrimeSpectrum R) (y : Sp K) (hy : x y = j q) :
    ∃ f : R →+* K, spMap f ≫ j = x ∧ RingHom.ker f = q.asIdeal := by
  have hsub : Set.range x ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact ⟨q, by rw [← hy, Subsingleton.elim z y]⟩
  have hx : IsOpenImmersion.lift j x hsub ≫ j = x := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift j x hsub)
  rw [← hg] at hx
  have hq : Spec.map g y = q := by
    apply j.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hx, hy]
  refine ⟨g.hom, hx, ?_⟩
  rw [← hq]
  have hy0 : PrimeSpectrum.asIdeal y = ⊥ := by
    rcases Ideal.eq_bot_or_top (PrimeSpectrum.asIdeal (R := K) y) with e | e
    · exact e
    · exact absurd e (PrimeSpectrum.isPrime y).ne_top
  change _ = Ideal.comap g.hom (PrimeSpectrum.asIdeal y)
  rw [hy0]
  rfl

theorem eq_comp_of_spMap {S : Scheme.{0}} {o R K : Type} [CommRing o] [CommRing R] [CommRing K]
    {j : Sp R ⟶ S} {s : S ⟶ Sp o} {δ : o →+* R} (hδ : j ≫ s = spMap δ) {f : R →+* K} {β : o →+* K}
    (h : (spMap f ≫ j) ≫ s = spMap β) (a : o) : β a = f (δ a) := by
  rw [Category.assoc, hδ] at h
  have h' : CommRingCat.ofHom δ ≫ CommRingCat.ofHom f = CommRingCat.ofHom β :=
    Spec.map_injective ((Spec.map_comp _ _).trans h)
  exact (congrArg (fun z => z.hom a) h').symm

theorem detCond_of_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) {o : Type} [CommRing o] (s : S ⟶ Sp o) (ρ : o)
    (hρ : ρ ^ 2 = -(H.d : o))
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S)
      (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)})
    {R : Type} [CommRing R] [IsReduced R] (j : Sp R ⟶ S) [IsOpenImmersion j]
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] (act' : OAct (𝓞 E) G') (hs : Smooth G'.hom)
    {n : ℕ} (v : Fin n → (epsR R ⟶ G')) (hv : IsLieBasis v)
    (h : ∀ (K : Type) [Field K] (y : Sp K ⟶ Sp R) (τ : 𝓞 E →+* K) (N : ℕ),
      LieMult act' y τ N ↔ LieMult act (y ≫ j) τ N)
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K) (β : o →+* K)
    (hβ : (spMap f ≫ j) ≫ s = spMap β) : DetCond D act (spMap f ≫ j) (β ρ) := by
  obtain ⟨δ₀, hδ₀⟩ := Spec.map_surjective (j ≫ s)
  have hδ : j ≫ s = spMap δ₀.hom := hδ₀.symm
  obtain ⟨M, hM⟩ := GlobalTheory.exists_lie_coordinates_lieMult_iff (𝓞 E) R G' act' n v hs hv
  obtain ⟨M', hM', e⟩ := hM K f
  have hr : (δ₀.hom ρ) ^ 2 = -(H.d : R) := by
    have := congrArg δ₀.hom hρ
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have main := GlobalTheory.T.cmType_eigenMultiplicity_of_dense_primes E H D.p D.q n R M (δ₀.hom ρ) hr (by
    refine (hd.preimage j.isOpenEmbedding.isOpenMap).mono ?_
    rintro q ⟨L, _, _, _, x, β', ⟨y, hy⟩, hx, hdet⟩
    obtain ⟨g, rfl, hg⟩ := exists_factor j x q y hy
    obtain ⟨N', hN', e'⟩ := hM L g
    refine ⟨L, inferInstance, inferInstance, inferInstance, g, N', hg, hN', fun τ => ?_⟩
    rw [← e', ← e', h, h, ← eq_comp_of_spMap hδ hx]
    exact hdet τ) K f M' hM'
  intro τ
  rw [← h, ← h, e, e, eq_comp_of_spMap hδ hβ]
  exact main τ

theorem detCond_of_dense : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsReduced S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (act : OAct (𝓞 E) G) (o : Type) [CommRing o] (s : S ⟶ Sp o) (ρ : o), SmoothOfRelativeDimension g G.hom → ρ ^ 2 = -(H.d : o) → Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : o →+* K), x ≫ s = spMap β → DetCond D act x (β ρ) := by
  intro E _ _ _ H D S _ G _ _ g act o _ s ρ hg hρ hd K _ _ _ x β hβ
  let y : Sp K := (default : PrimeSpectrum K)
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := x y) trivial
  let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
  have : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  obtain ⟨q, hq⟩ : x y ∈ Set.range j := hU.range_fromSpec.ge hs
  have hg₁ : SmoothOfRelativeDimension g ((Over.pullback j).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨r, hr, v, hv⟩ := GlobalTheory.LieLoc.lie_locally_free Γ(S, U) ((Over.pullback j).obj G) g hg₁ q
  let a : Sp (Localization.Away r) ⟶ Sp Γ(S, U) := spMap (algebraMap Γ(S, U) (Localization.Away r))
  have : IsOpenImmersion a := IsOpenImmersion.of_isLocalization r
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(S, U) (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨f, rfl, -⟩ := exists_factor (a ≫ j) x q' y (by
    rw [← hq, ← hq']
    rfl)
  obtain ⟨a₁, h₁⟩ := GlobalTheory.DetExtend.exists_oAct_pullback j act
  obtain ⟨a₂, h₂⟩ := GlobalTheory.DetExtend.exists_oAct_pullback a a₁
  have hg₂ : SmoothOfRelativeDimension g ((Over.pullback a).obj ((Over.pullback j).obj G)).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg₁
  refine detCond_of_basis D act s ρ hρ hd (a ≫ j) a₂ (SmoothOfRelativeDimension.smooth g _) v hv
    (fun L _ z τ N => ?_) K f β hβ
  rw [LiePull.lieMult_pull _ _ _ _ _ a _ a₁ a₂ (isGrpPullback_pullback _ a)
    (fun c => by rw [h₂]; exact pullback.lift_fst _ _ _) L z τ N,
    LiePull.lieMult_pull _ _ _ _ _ j _ act a₁ (isGrpPullback_pullback _ j)
    (fun c => by rw [h₁]; exact pullback.lift_fst _ _ _) L (z ≫ a) τ N, Category.assoc]

end GlobalTheory.DetSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBinaryOpGluedAlongCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_binary_op_glued_along_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) (ψ : ∀ i, (G i).left ⟶ A.left) (o : ∀ i, G i ⊗ G i ⟶ G i), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (lift x y ≫ o i).left ≫ ψ i = (lift x' y' ≫ o j).left ≫ ψ j) → ∃ m : A ⊗ A ⟶ A, ∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (lift x y ≫ o i).left ≫ ψ i := by
  first | exact @GlobalTheory.CoverGlue.exists_binary_op | exact GlobalTheory.CoverGlue.exists_binary_op | (intros; apply GlobalTheory.CoverGlue.exists_binary_op <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCechDataPullbackOfLineBundleOnOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechData_pullback_of_lineBundle_on_open : ∀ (X Y : Scheme.{0}) (ψ : Y ⟶ X) [IsOpenImmersion ψ] (L : LB Y), L.IsLB → ∃ M : LB X, ⨆ a, M.U a = ψ.opensRange ∧ (∀ (a : M.ι) (x : X), x ∈ M.U a → gm (𝟙 X) x (M.U a ⊓ M.U a) (M.g a a) = 1) ∧ (M.pull ψ).IsLB ∧ LBIso L (M.pull ψ) := by
  first | exact @GlobalTheory.LBPush.exists_push | exact GlobalTheory.LBPush.exists_push | (intros; apply GlobalTheory.LBPush.exists_push <;> assumption)
end

