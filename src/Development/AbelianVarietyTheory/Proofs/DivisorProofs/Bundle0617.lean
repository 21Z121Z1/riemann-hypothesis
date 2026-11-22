import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLineBundlePowerIsoGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section
namespace GlobalTheory.RigNorm
open Opposite TopologicalSpace

theorem glue_units {T : Scheme.{0}} {I : Type} (W : I → T.Opens) (hW : ∀ x : T, ∃ i, x ∈ W i)
    (u : ∀ i, Γ(T, W i)ˣ)
    (hu : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res (inf_le_right : W i ⊓ W j ≤ W j) (u j)) :
    ∃ v : Γ(T, ⊤)ˣ, ∀ i, res (le_top : W i ≤ ⊤) v = u i := by
  have hc : (⊤ : T.Opens) ≤ iSup W := fun x _ => by
    obtain ⟨i, hi⟩ := hW x
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  have glue : ∀ sf : ∀ i, Γ(T, W i), (∀ i j, (T.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (sf i) = (T.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (sf j)) →
      ∃ s : Γ(T, ⊤), ∀ i, (T.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom s = sf i := by
    intro sf hsf
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.sheaf W ⊤ (fun i => homOfLE le_top) hc sf hsf
    exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := glue (fun i => (u i).val) (fun i j => congrArg Units.val (hu i j))
  obtain ⟨s', hs'⟩ := glue (fun i => ((u i)⁻¹).val) (fun i j => by
    have := congrArg (fun x => (x⁻¹).val) (hu i j)
    simpa [res, map_inv] using this)
  have h1 : s * s' = 1 := by
    apply TopCat.Sheaf.eq_of_locally_eq' T.sheaf W ⊤ (fun i => homOfLE le_top) hc
    intro i
    have := hs i; have := hs' i
    change (T.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom (s * s') = (T.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom 1
    rw [map_mul, map_one, hs i, hs' i, Units.mul_inv]
  refine ⟨⟨s, s', h1, by rw [mul_comm, h1]⟩, fun i => Units.ext ?_⟩
  exact hs i

theorem val_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    (res h u).val = (X.presheaf.map (homOfLE h).op).hom u.val := rfl

theorem val_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    (pullU f U u).val = (f.app U).hom u.val := rfl

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (u : Γ(X, U)ˣ) :
    res h₁ (res h₂ u) = res (h₁.trans h₂) u := by
  apply Units.ext
  simp only [val_res]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem appLE_res {X Y : Scheme.{0}} (h : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (hU : U ≤ U') (x : Γ(Y, U')) :
    (h.appLE U V e).hom ((Y.presheaf.map (homOfLE hU).op).hom x) =
      (h.appLE U' V (e.trans fun _ hy => hU hy)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem res_appLE {X Y : Scheme.{0}} (h : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (hV : V' ≤ V) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE hV).op).hom ((h.appLE U V e).hom x) = (h.appLE U V' (hV.trans e)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_app {X Y Z : Scheme.{0}} (h : X ⟶ Y) (k : Y ⟶ Z) {U : Z.Opens} {W : X.Opens}
    (e : W ≤ h ⁻¹ᵁ (k ⁻¹ᵁ U)) (x : Γ(Z, U)) :
    (h.appLE (k ⁻¹ᵁ U) W e).hom ((k.app U).hom x) = ((h ≫ k).appLE U W (e.trans fun _ hy => hy)).hom x := by
  rw [Scheme.Hom.comp_appLE]; rfl

theorem appLE_congr' {X Y : Scheme.{0}} {h h' : X ⟶ Y} (H : h = h') {U : Y.Opens} {V : X.Opens}
    (e : V ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (h.appLE U V e).hom x = (h'.appLE U V (H ▸ e)).hom x := by
  subst H; rfl

theorem id_appLE' {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U V e).hom x = (X.presheaf.map (homOfLE e).op).hom x := by
  rfl

theorem alg {R : Type*} [CommRing R] (Bp Bq Ap Aq ap aq cM cL : R) (k : ℕ) (hB : Bp = cM * Bq)
    (hA : Ap = cL * Aq) (ha : ap * cL ^ k = cM ^ k * aq) : Bp ^ k * (aq * Aq ^ k) = Bq ^ k * (ap * Ap ^ k) := by
  subst hB hA; linear_combination (-(Bq ^ k * Aq ^ k)) * ha

theorem mul_inv_mul_cancel_comm {G : Type*} [CommGroup G] (m l a l' : G) (h : l = l') : m * l⁻¹ * a * l' = m * a := by
  subst h; rw [mul_right_comm, inv_mul_cancel_right]

theorem map_map' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom x) =
      (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem pre_mono {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} (h : U ≤ U') : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U' :=
  fun _ hx => h hx

theorem pre_inf {X Y : Scheme.{0}} (f : X ⟶ Y) (U U' : Y.Opens) : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ (U ⊓ U') :=
  fun _ hx => hx

theorem pull_inf_le {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : L.ι) :
    LB.wchart L (fun _ : PUnit => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : PUnit => φ) (fun _ => j) ≤ φ ⁻¹ᵁ (L.U i ⊓ L.U j) :=
  fun _ hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩

theorem pow_inf_le {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) i ⊓ LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)) :=
  fun _ hy => ⟨Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.2 0⟩

theorem pull_g_val {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (i j : PUnit → L.ι) :
    ((L.pull φ).g i j).val = (Y.presheaf.map (homOfLE (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit,
      Set.mem_iInter.1 hy.2 PUnit.unit⟩ : (L.pull φ).U i ⊓ (L.pull φ).U j ≤
        φ ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)))).op).hom
      ((φ.app _).hom (L.g (i PUnit.unit) (j PUnit.unit)).val) :=
by
  show (∏ m : PUnit, (res (le_inf (inf_le_left.trans (LB.wchart_le L _ i m)) (inf_le_right.trans (LB.wchart_le L _ j m)))
    (pullU φ (L.U (i m) ⊓ L.U (j m)) (L.g (i m) (j m)))) ^ (1 : ℤ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem powPull_g_val {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (i j : Fin 1 → L.ι) :
    ((powPull L φ (k : ℤ)).g i j).val = ((Y.presheaf.map (homOfLE (fun y hy => ⟨Set.mem_iInter.1 hy.1 0,
      Set.mem_iInter.1 hy.2 0⟩ : (powPull L φ (k : ℤ)).U i ⊓ (powPull L φ (k : ℤ)).U j ≤
        φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)))).op).hom ((φ.app _).hom (L.g (i 0) (j 0)).val)) ^ k :=
by
  show (∏ m : Fin 1, (res (le_inf (inf_le_left.trans (LB.wchart_le L _ i m)) (inf_le_right.trans (LB.wchart_le L _ j m)))
    (pullU φ (L.U (i m) ⊓ L.U (j m)) (L.g (i m) (j m)))) ^ (k : ℤ)).val = _
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl

theorem pull_rel {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (e : LB.Gen (L.pull φ)) (he : e.IsGen)
    (s : ∀ i : L.ι, Γ(Y, LB.wchart L (fun _ : PUnit => φ) (fun _ => i))ˣ) (hs : s = fun i => e.s (fun _ => i))
    (i j : L.ι) :
    (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (fun _ : PUnit => φ) (fun _ => i) ⊓
      LB.wchart L (fun _ : PUnit => φ) (fun _ => j) ≤ LB.wchart L (fun _ : PUnit => φ) (fun _ => i))).op).hom (s i).val =
    (Y.presheaf.map (homOfLE (pull_inf_le L φ i j)).op).hom ((φ.app _).hom (L.g i j).val) *
    (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (fun _ : PUnit => φ) (fun _ => i) ⊓
      LB.wchart L (fun _ : PUnit => φ) (fun _ => j) ≤ LB.wchart L (fun _ : PUnit => φ) (fun _ => j))).op).hom (s j).val := by
  subst hs
  exact (congrArg Units.val (he (fun _ => i) (fun _ => j))).trans
    (congrArg (· * _) (pull_g_val L φ (fun _ => i) (fun _ => j)))

theorem div_rel {X Y₁ Y₂ : Scheme.{0}} (L : LB Y₁) (M : LB Y₂) (f : X ⟶ Y₁) (g : X ⟶ Y₂) (k : ℕ)
    (α₀ : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ)))) (hα : α₀.IsGen)
    (s : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2)ˣ)
    (hs : s = fun p => α₀.s p) (p q : (Fin 1 → M.ι) × (Fin 1 → L.ι)) :
    (X.presheaf.map (homOfLE (inf_le_left : (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s p).val *
    ((X.presheaf.map (homOfLE ((inf_le_inf inf_le_right inf_le_right).trans (pow_inf_le L f p.2 q.2) :
      (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        f ⁻¹ᵁ (L.U (p.2 0) ⊓ L.U (q.2 0)))).op).hom ((f.app _).hom (L.g (p.2 0) (q.2 0)).val)) ^ k =
    ((X.presheaf.map (homOfLE ((inf_le_inf inf_le_left inf_le_left).trans (pow_inf_le M g p.1 q.1) :
      (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        g ⁻¹ᵁ (M.U (p.1 0) ⊓ M.U (q.1 0)))).op).hom ((g.app _).hom (M.g (p.1 0) (q.1 0)).val)) ^ k *
    (X.presheaf.map (homOfLE (inf_le_right : (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓
      (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2) ≤
        LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2)).op).hom (s q).val := by
  subst hs
  have hhL : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (powPull L f (k : ℤ)).U p.2 ⊓ (powPull L f (k : ℤ)).U q.2 :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have hhM : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (powPull M g (k : ℤ)).U p.1 ⊓ (powPull M g (k : ℤ)).U q.1 :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h2 : res (inf_le_left : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p) (α₀.s p) *
        res hhL ((powPull L f (k : ℤ)).g p.2 q.2) =
      res hhM ((powPull M g (k : ℤ)).g p.1 q.1) *
        res (inf_le_right : (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q ≤ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U q) (α₀.s q) := by
    rw [hα p q]
    exact mul_inv_mul_cancel_comm _ _ _ _ rfl
  have eL := ((congrArg (X.presheaf.map (homOfLE hhL).op).hom (powPull_g_val L f k p.2 q.2)).trans
    (map_pow _ _ _)).trans (congrArg (· ^ k) (map_map' _ _ _))
  have eM := ((congrArg (X.presheaf.map (homOfLE hhM).op).hom (powPull_g_val M g k p.1 q.1)).trans
    (map_pow _ _ _)).trans (congrArg (· ^ k) (map_map' _ _ _))
  have h3 := congrArg Units.val h2
  rw [Units.val_mul, Units.val_mul, val_res hhL, val_res hhM, eL, eM] at h3
  exact h3

theorem exists_rescaled_gen : ∀ {T X Z₀ Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (eL : Z₀ ⟶ Z₁) (eM : Z₀ ⟶ Z₂) (t : T ⟶ Z₀) (z : T ⟶ X) (π : X ⟶ T) (k : ℕ) (eA : LB.Gen (L.pull eL)) (eB : LB.Gen (M.pull eM)) (α₀ : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ)))), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → α₀.IsGen → z ≫ π = 𝟙 T → z ≫ f = t ≫ eL → z ≫ g = t ≫ eM → ∃ α : LB.Gen (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen ∧ ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (z.appLE ((LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_left)).hom (α.s p).val * ((t.appLE (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k = ((t.appLE (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  intro T X Z₀ Z₁ Z₂ L M f g eL eM t z π k eA eB α₀ hL hM hA hB hα hzπ hzf hzg
  obtain ⟨sA, hsA⟩ : ∃ s : ∀ i : L.ι, Γ(Z₀, LB.wchart L (fun _ : PUnit => eL) (fun _ => i))ˣ, s = fun i => eA.s (fun _ => i) := ⟨_, rfl⟩
  obtain ⟨sB, hsB⟩ : ∃ s : ∀ i : M.ι, Γ(Z₀, LB.wchart M (fun _ : PUnit => eM) (fun _ => i))ˣ, s = fun i => eB.s (fun _ => i) := ⟨_, rfl⟩
  obtain ⟨sα, hsα⟩ : ∃ s : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), Γ(X, (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2))ˣ, s = fun p => α₀.s p :=
    ⟨_, rfl⟩
  let Wo : (Fin 1 → M.ι) × (Fin 1 → L.ι) → T.Opens := fun p =>
    z ⁻¹ᵁ (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ⊓ t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)
  have hDU : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p = (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) := fun _ => rfl
  let a : ∀ p, Γ(T, Wo p)ˣ := fun p =>
    Units.map (z.appLE (LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) (Wo p) ((inf_le_left.trans inf_le_left).trans (pre_mono z (hDU p).le))).hom.toMonoidHom (sα p)
  let A : ∀ p, Γ(T, Wo p)ˣ := fun p =>
    Units.map (t.appLE (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0)) (Wo p) (inf_le_left.trans inf_le_right)).hom.toMonoidHom (sA (p.2 0))
  let B : ∀ p, Γ(T, Wo p)ˣ := fun p =>
    Units.map (t.appLE (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0)) (Wo p) inf_le_right).hom.toMonoidHom (sB (p.1 0))
  let u : ∀ p, Γ(T, Wo p)ˣ := fun p => B p ^ k * (a p * A p ^ k)⁻¹
  have hcov : ∀ x : T, ∃ p, x ∈ Wo p := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show eL (t x) ∈ ⨆ i, L.U i by rw [hL.cover]; trivial)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (show eM (t x) ∈ ⨆ j, M.U j by rw [hM.cover]; trivial)
    have hf : f (z x) = eL (t x) := by rw [← Scheme.Hom.comp_apply, hzf, Scheme.Hom.comp_apply]
    have hg : g (z x) = eM (t x) := by rw [← Scheme.Hom.comp_apply, hzg, Scheme.Hom.comp_apply]
    refine ⟨(fun _ => j, fun _ => i), ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
    · exact Set.mem_iInter.2 fun _ => show g (z x) ∈ M.U j by rw [hg]; exact hj
    · exact Set.mem_iInter.2 fun _ => show f (z x) ∈ L.U i by rw [hf]; exact hi
    · exact Set.mem_iInter.2 fun _ => hi
    · exact Set.mem_iInter.2 fun _ => hj
  have hcomp : ∀ p q, res (inf_le_left : Wo p ⊓ Wo q ≤ Wo p) (u p) =
      res (inf_le_right : Wo p ⊓ Wo q ≤ Wo q) (u q) := by
    intro p q
    have eV : Wo p ⊓ Wo q ≤ z ⁻¹ᵁ ((LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) ⊓ (LB.wchart M (fun _ : Fin 1 => g) q.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) q.2)) := (inf_le_inf ((inf_le_left.trans inf_le_left).trans (pre_mono z (hDU p).le))
      ((inf_le_left.trans inf_le_left).trans (pre_mono z (hDU q).le))).trans (pre_inf z _ _)
    have eVA : Wo p ⊓ Wo q ≤ t ⁻¹ᵁ (LB.wchart L (fun _ : PUnit => eL) (fun _ => p.2 0) ⊓ LB.wchart L (fun _ : PUnit => eL) (fun _ => q.2 0)) := (inf_le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right)).trans (pre_inf t _ _)
    have eVB : Wo p ⊓ Wo q ≤ t ⁻¹ᵁ (LB.wchart M (fun _ : PUnit => eM) (fun _ => p.1 0) ⊓ LB.wchart M (fun _ : PUnit => eM) (fun _ => q.1 0)) := (inf_le_inf inf_le_right inf_le_right).trans (pre_inf t _ _)
    have ra := congrArg (z.appLE _ _ eV).hom (div_rel L M f g k α₀ hα sα hsα p q)
    have rA := congrArg (t.appLE _ _ eVA).hom (pull_rel L eL eA hA sA hsA (p.2 0) (q.2 0))
    have rB := congrArg (t.appLE _ _ eVB).hom (pull_rel M eM eB hB sB hsB (p.1 0) (q.1 0))
    simp only [map_mul, map_pow, appLE_res, appLE_app, appLE_congr' hzf, appLE_congr' hzg] at ra rA rB
    simp only [u, map_mul, map_pow, map_inv]
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, val_res, a, A, B, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, res_appLE]
    exact alg _ _ _ _ _ _ _ _ k rB rA ra
  obtain ⟨v, hv⟩ := glue_units Wo hcov u hcomp
  refine ⟨⟨fun p => res (show (LB.div (powPull M g (k : ℤ)) (powPull L f (k : ℤ))).U p ≤ π ⁻¹ᵁ ⊤ from fun _ _ => trivial) (pullU π ⊤ v) * α₀.s p⟩, ?_, ?_⟩
  · intro p q
    dsimp only
    simp only [map_mul, res_res, hα p q]
    exact mul_left_comm _ _ _
  · intro p
    have key : ((z ≫ π).appLE ⊤ (Wo p) (fun _ _ => trivial)).hom v.val = (u p).val := by
      have h1 := appLE_congr' hzπ (U := ⊤) (V := Wo p) (fun _ _ => trivial) v.val
      rw [id_appLE'] at h1
      exact h1.trans (congrArg Units.val (hv p))
    have hu := congrArg Units.val (inv_mul_cancel_right (B p ^ k) (a p * A p ^ k))
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hu
    dsimp only
    simp only [Units.val_mul, val_res, val_pullU, map_mul, appLE_res, appLE_app]
    rw [key, _root_.mul_assoc]
    subst hsA hsB hsα
    exact hu

end GlobalTheory.RigNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivSumWedgeSemilinearPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem clRel_pullForm : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (w : GlobForm s) (n : ℕ) (u v : Fin n → GlobForm s), ClRel (OAff s) w u v → ClRel (OAff s') (GlobalTheory.CechDR.pullForm h w) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  intro R R' _ _ X X' s s' σ φ h w n u v hw T'
  have hp : ∀ (ω : GlobForm s) (p : Pair φ), (GlobalTheory.CechDR.pullForm h ω).1 (Opposite.op p.1.1) =
      (semiHom_secPull h p).m1 (ω.1 (Opposite.op p.1.2)) :=
    fun ω p ↦ ((isPullForm_iff.1 (isPullForm_pullForm h ω)) p).symm
  have hg : ∀ (ω : GlobForm s') {T T' : AffOp X'} (a : T ⟶ T'), p1 (OAff s') a (ω.1 T) = ω.1 T' :=
    fun ω _ _ a ↦ (ω.2 a).symm
  rw [← sub_eq_zero]
  refine twoForm_sep_of_basis s' (pairFst φ) (pair_cover_affine φ s') T' _ fun t a ↦ ?_
  rw [map_sub, sub_eq_zero, pOm_dOne, hg]
  have e1 : ∀ k, pOm (OAff s') 2 a (wedge R' _ ((GlobalTheory.CechDR.pullForm h (u k)).1 T')
      ((GlobalTheory.CechDR.pullForm h (v k)).1 T')) = wedge R' _ ((GlobalTheory.CechDR.pullForm h (u k)).1 ((pairFst φ).obj t))
      ((GlobalTheory.CechDR.pullForm h (v k)).1 ((pairFst φ).obj t)) := fun k ↦
    (pOm_wedge (OAff s') a _ _).trans (by rw [hg, hg])
  refine Eq.trans ?_ ((map_sum (pOm (OAff s') 2 a) _ _).trans (Finset.sum_congr rfl fun k _ ↦ e1 k)).symm
  have key : ∀ p : Pair φ, dOne R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h w).1 (Opposite.op p.1.1)) =
      ∑ k, wedge R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h (u k)).1 (Opposite.op p.1.1))
        ((GlobalTheory.CechDR.pullForm h (v k)).1 (Opposite.op p.1.1)) := by
    intro p
    calc dOne R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h w).1 (Opposite.op p.1.1))
        = dOne R' (Sec s' p.1.1.1) ((semiHom_secPull h p).m1 (w.1 (Opposite.op p.1.2))) :=
          congrArg _ (hp w p)
      _ = (semiHom_secPull h p).mOm 2 (dOne R (Sec s p.1.2.1) (w.1 (Opposite.op p.1.2))) :=
          (SemiHom.mOm_dOne _ _).symm
      _ = (semiHom_secPull h p).mOm 2 (wsum (OAff s) u v (Opposite.op p.1.2)) :=
          congrArg ((semiHom_secPull h p).mOm 2) (hw (Opposite.op p.1.2))
      _ = (semiHom_secPull h p).mOm 2 (∑ k, wedge R (Sec s p.1.2.1) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))) := rfl
      _ = ∑ k, (semiHom_secPull h p).mOm 2 (wedge R (Sec s p.1.2.1) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))) := map_sum _ _ _
      _ = ∑ k, wedge R' (Sec s' p.1.1.1) ((semiHom_secPull h p).m1 ((u k).1 (Opposite.op p.1.2)))
            ((semiHom_secPull h p).m1 ((v k).1 (Opposite.op p.1.2))) :=
          Finset.sum_congr rfl fun k _ ↦ SemiHom.mOm_wedge (semiHom_secPull h p) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))
      _ = ∑ k, wedge R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h (u k)).1 (Opposite.op p.1.1))
            ((GlobalTheory.CechDR.pullForm h (v k)).1 (Opposite.op p.1.1)) :=
          Finset.sum_congr rfl fun k _ ↦ congrArg₂ (fun a b ↦ wedge R' (Sec s' p.1.1.1) a b)
            (hp (u k) p).symm (hp (v k) p).symm
  exact key t.unop

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareKerOfSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtSqKer

variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem upd_congr {J : Type} [DecidableEq J] (p : M →ₗ[R] H) (F : M [⋀^J]→ₗ[R] Q)
    (hF : ∀ (u : J → M) (j : J), p (u j) = 0 → F u = 0)
    (u : J → M) (j : J) (a b : M) (hab : p a = p b) :
    F (Function.update u j a) = F (Function.update u j b) := by
  have h1 : a = b + (a - b) := by abel
  rw [h1, F.map_update_add, hF (Function.update u j (a - b)) j (by simp [hab]), add_zero]

noncomputable def descend {J : Type} (p : M →ₗ[R] H) (hp : Function.Surjective p)
    (F : M [⋀^J]→ₗ[R] Q)
    (hF : ∀ (u : J → M) (j : J), p (u j) = 0 → F u = 0) :
    H [⋀^J]→ₗ[R] Q where
  toFun v := F (fun k => Function.surjInv hp (v k))
  map_update_add' := by
    intro _ v j x y
    have e : ∀ z : H, (fun k => Function.surjInv hp (Function.update v j z k)) =
        Function.update (fun k => Function.surjInv hp (v k)) j (Function.surjInv hp z) := by
      intro z; funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [e]
    rw [upd_congr p F hF _ j _ (Function.surjInv hp x + Function.surjInv hp y)
      (by simp [Function.surjInv_eq hp]), F.map_update_add]
  map_update_smul' := by
    intro _ v j c x
    have e : ∀ z : H, (fun k => Function.surjInv hp (Function.update v j z k)) =
        Function.update (fun k => Function.surjInv hp (v k)) j (Function.surjInv hp z) := by
      intro z; funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [e]
    rw [upd_congr p F hF _ j _ (c • Function.surjInv hp x)
      (by simp [Function.surjInv_eq hp]), F.map_update_smul]
  map_eq_zero_of_eq' := by
    intro v a b hv hab
    exact F.map_eq_zero_of_eq _ (by simp [hv]) hab

end GlobalTheory.ExtSqKer

namespace GlobalTheory.ExtSqKer

variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem fin_two_vector_eq_matrixVecCons (u : Fin 2 → M) : u = ![u 0, u 1] := by
  ext k; fin_cases k <;> rfl

theorem congr_two (p : M →ₗ[R] H) (F : M [⋀^Fin 2]→ₗ[R] Q)
    (hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0)
    (u u' : Fin 2 → M) (h : ∀ k, p (u k) = p (u' k)) : F u = F u' := by
  calc F u = F (Function.update u 0 (u 0)) := by rw [Function.update_eq_self]
    _ = F (Function.update u 0 (u' 0)) := upd_congr p F hF u 0 _ _ (h 0)
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 ((Function.update u 0 (u' 0)) 1)) := by
        rw [Function.update_eq_self]
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 (u' 1)) :=
        upd_congr p F hF _ 1 _ _ (by simpa using h 1)
    _ = F u' := by
        congr 1; ext k; fin_cases k <;> simp

end GlobalTheory.ExtSqKer

open GlobalTheory.ExtSqKer in

theorem GlobalTheory.exteriorSquare_ker_of_surjective (R : Type) [CommRing R] (W M H : Type)
    [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (t : ⋀[R]^2 M) (ht : exteriorPower.map 2 p t = 0) :
    ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W),
      t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by
  set S : Set (⋀[R]^2 M) := {x | ∃ (a : M) (w : W), x = exteriorPower.ιMulti R 2 ![a, i w]}
  set N : Submodule R (⋀[R]^2 M) := Submodule.span R S
  let F : M [⋀^Fin 2]→ₗ[R] (⋀[R]^2 M ⧸ N) := N.mkQ.compAlternatingMap (exteriorPower.ιMulti R 2)
  have hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0 := by
    intro u j hj
    obtain ⟨w, hw⟩ := (hex (u j)).1 hj
    simp only [F, LinearMap.compAlternatingMap_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    fin_cases j
    · have e : u = ![u 1, i w] ∘ Equiv.swap 0 1 := by
        ext k; fin_cases k <;> simp [hw]
      rw [e, AlternatingMap.map_swap _ _ (by decide)]
      exact N.neg_mem (Submodule.subset_span ⟨u 1, w, rfl⟩)
    · rw [fin_two_vector_eq_matrixVecCons u]
      exact Submodule.subset_span ⟨u 0, w, by simp [hw]⟩
  let g := exteriorPower.alternatingMapLinearEquiv (descend p hp F hF)
  have hg : g ∘ₗ exteriorPower.map 2 p = N.mkQ := by
    apply exteriorPower.linearMap_ext
    ext m
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      exteriorPower.map_apply_ιMulti, g, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change F _ = F m
    exact congr_two p F hF _ _ (fun k => by simp [Function.surjInv_eq hp])
  have hN : t ∈ N := by
    have := congrArg (fun f => f t) hg
    simp only [LinearMap.coe_comp, Function.comp_apply, ht, map_zero, Submodule.mkQ_apply] at this
    exact (Submodule.Quotient.mk_eq_zero N).1 this.symm
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 hN
  choose a w haw using fun k => (x k).2
  refine ⟨n, fun k => c k • a k, w, ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [haw k]
  have e : ![c k • a k, i (w k)] = Function.update ![a k, i (w k)] 0 (c k • a k) := by
    ext l; fin_cases l <;> simp
  rw [e, AlternatingMap.map_update_smul]
  congr 2
  ext l; fin_cases l <;> simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgProjectiveConstantRankExtensionAndProd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem fp_prod (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W]
    [AddCommGroup H] [Module R H] (a b : ℕ) (hW : FP R W a) (hH : FP R H b) :
    FP R (W × H) (a + b) := by
  obtain ⟨hWf, hWp, hWr⟩ := hW
  obtain ⟨hHf, hHp, hHr⟩ := hH
  refine ⟨inferInstance, inferInstance, fun p => ?_⟩
  have := Module.rankAtStalk_prod (R := R) W H
  rw [congrFun this p, Pi.add_apply, hWr p, hHr p]

theorem fp_ext (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W]
    [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ)
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hW : FP R W a) (hH : FP R H b) : FP R M (a + b) := by
  have hWH := fp_prod R W H a b hW hH
  obtain ⟨-, hHp, -⟩ := hH
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : H →ₗ[R] H) hp
  obtain ⟨e, -⟩ := hex.splitSurjectiveEquiv hi ⟨s, hs⟩
  obtain ⟨hf, hpr, hr⟩ := hWH
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun q => ?_⟩
  rw [congrFun (Module.rankAtStalk_eq_of_equiv e) q, hr q]

theorem fp_ext_prod : (∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ) (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Injective i → Function.Surjective p → Function.Exact i p → FP R W a → FP R H b → FP R M (a + b)) ∧ ∀ (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W] [AddCommGroup H] [Module R H] (a b : ℕ), FP R W a → FP R H b → FP R (W × H) (a + b) :=
  ⟨fun R _ W M H _ _ _ _ _ _ a b i p hi hp hex hW hH => fp_ext R W M H a b i p hi hp hex hW hH,
   fun R _ W H _ _ _ _ a b hW hH => fp_prod R W H a b hW hH⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealLatticeHasNonrealMultiplierStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdealLattice_has_nonreal_multiplier : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → (∀ a : 𝓞 K, MulStable Λ (ι a)) ∧ MulStable Λ (ι δ) ∧ (ι δ).im ≠ 0 ∧ IsIntegral ℤ δ := by
  first | exact @GlobalTheory.LatOfMult.main | exact GlobalTheory.LatOfMult.main | (intros; apply GlobalTheory.LatOfMult.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeEndProductPowersTransportGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActFin

theorem prod_zpow_transport : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A t φ → ∀ (r : ℕ) (g : Fin r → (A' ⟶ A')) (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ), (∀ k, (g k).left ≫ φ = φ ≫ (f k).left) → (∏ k, g k ^ c k).left ≫ φ = φ ≫ (∏ k, f k ^ c k).left := by
  intro S S' t A _ _ A' _ _ φ h r g f c hc
  let U : Over.mk (A'.hom ≫ t) ⟶ A := pushPt h.1.w (𝟙 A')
  have hk : ∀ k, pushHom h A' (g k) = preHom U (f k) := fun k => by
    ext
    show (g k).left ≫ φ = (𝟙 A' : A' ⟶ A').left ≫ φ ≫ (f k).left
    rw [hc k, Over.id_left, Category.id_comp]
  have e : pushHom h A' (∏ k, g k ^ c k) = preHom U (∏ k, f k ^ c k) := by
    rw [map_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, map_zpow, hk k]
  have e' := congrArg (fun z => z.left) e
  change (∏ k, g k ^ c k).left ≫ φ = ((𝟙 A' : A' ⟶ A').left ≫ φ) ≫ (∏ k, f k ^ c k).left at e'
  rwa [Over.id_left, Category.id_comp] at e'

end GlobalTheory.ActFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLeStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  first | exact @GlobalTheory.TjCount.tj_cosets_finite_card_le | exact GlobalTheory.TjCount.tj_cosets_finite_card_le | (intros; apply GlobalTheory.TjCount.tj_cosets_finite_card_le <;> assumption)
end

