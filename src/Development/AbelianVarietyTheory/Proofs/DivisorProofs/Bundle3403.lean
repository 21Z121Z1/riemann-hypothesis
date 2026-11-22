import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeibnizAlongBaseConstantsAtPoints
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem Heat.acts_const_at_points : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (v : Fin n → TanM (𝟙 (Sp R)) G) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat G m L dd ⇑D) (k : ℕ) (a b : R) (ρ τ ρ' τ' : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ r z J) → h.Acts k ρ ρ' → h.Acts k τ τ' → ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D b)) * sval τ r z J := by
  intro R _ G _ _ n X m L hL v dd hinv D h k a b ρ τ ρ' τ' hpt hρ hτ

  have cTop : ∀ c : R, constFn G.hom ⊤ c = scal G.hom c := fun c => by
    simp only [constFn, Out.scal, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have gsR : ∀ {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z) {O O₀ : G.left.Opens} (hle : O ≤ O₀) (hz : r z ∈ O)
      (s : Γ(G.left, O₀)), gs r z O (rsT s O) = gs r z O₀ s := fun r z _ _ hle hz s => by
    rw [GlobalTheory.KS.rsT_of_le hle]; exact gs_res r z hle hz s
  have gsC : ∀ {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z) (O : G.left.Opens) (hz : r z ∈ O) (c : R),
      gs r z O (constFn G.hom O c) = gs r z ⊤ (scal G.hom c) := fun r z O hz c => by
    rw [← GlobalTheory.KS.rsT_constFn G.hom (le_top : O ≤ ⊤) c, gsR r z le_top hz, cTop]
  have cMul : ∀ (O : G.left.Opens) (c : R),
      constFn G.hom O (2 * (k : R) * c) = 2 * (k : Γ(G.left, O)) * constFn G.hom O c := fun O c => by
    simp [constFn, map_mul, map_natCast, map_ofNat]
  have hWc : ∀ i, h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := fun i => Glue.le_wchart _ (h.le i)

  have leib : ∀ i (c : R) (F : Γ(G.left, h.W i)),
      op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (constFn G.hom (h.W i) c * F) =
        constFn G.hom (h.W i) c * op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) F +
          constFn G.hom (h.W i) (2 * (k : R) * D c) * F := by
    intro i c F
    have hd := (h.lift i).1.2.1 (h.W i) le_rfl (constFn G.hom (h.W i) c) F
    have hdc := (h.lift i).2 (h.W i) le_rfl c
    have hdd : ∀ a' (f : Γ(G.left, h.W i)), dd a' (h.W i) (constFn G.hom (h.W i) c * f) =
        constFn G.hom (h.W i) c * dd a' (h.W i) f := fun a' f => by
      rw [(hinv a').1.2.1 (h.W i) le_top, IsInv.apply_constFn G (v a') (dd a') (hinv a'), mul_zero, add_zero]
    have hs : ∀ (f : Γ(G.left, h.W i)),
        ∑ a', ∑ b', constFn G.hom (h.W i) (h.Θ a' b') * dd a' (h.W i) (dd b' (h.W i) (constFn G.hom (h.W i) c * f)) =
          constFn G.hom (h.W i) c * ∑ a', ∑ b', constFn G.hom (h.W i) (h.Θ a' b') * dd a' (h.W i) (dd b' (h.W i) f) := by
      intro f
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [hdd, hdd]; ring
    have hs' : ∑ a', constFn G.hom (h.W i) (h.u a') * dd a' (h.W i) (constFn G.hom (h.W i) c * F) =
        constFn G.hom (h.W i) c * ∑ a', constFn G.hom (h.W i) (h.u a') * dd a' (h.W i) F := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [hdd]; ring
    simp only [op]
    rw [hs, hs', hd, hdc, cMul]
    ring

  have onW : ∀ i, constFn G.hom (h.W i) a * rsT (ρ'.f fun _ => h.j i) (h.W i) +
      constFn G.hom (h.W i) (2 * (k : R) * D a) * rsT (ρ.f fun _ => h.j i) (h.W i) =
      constFn G.hom (h.W i) b * rsT (τ'.f fun _ => h.j i) (h.W i) +
      constFn G.hom (h.W i) (2 * (k : R) * D b) * rsT (τ.f fun _ => h.j i) (h.W i) := by
    intro i
    have hA : constFn G.hom (h.W i) a * rsT (ρ.f fun _ => h.j i) (h.W i) =
        constFn G.hom (h.W i) b * rsT (τ.f fun _ => h.j i) (h.W i) := by
      refine fn_ext fun x hx => ?_
      obtain ⟨J, hJ, e⟩ := exists_good L hL x (fun _ : Fin 1 => m) (fun _ => h.j i) (fun _ _ _ => rfl)
        (fun _ => h.le i hx)
      have hp := hpt G.left (𝟙 _) x J hJ
      have s1 : ∀ σ : SecM m L k, sval σ (𝟙 G.left) x J = gs (𝟙 G.left) x (h.W i) (rsT (σ.f fun _ => h.j i) (h.W i)) :=
        fun σ => by
          rw [sval_of σ (𝟙 G.left) x J (fun _ => h.j i) (fun q => by rw [Category.id_comp]; exact e q)]
          exact (gsR (𝟙 G.left) x (hWc i) hx _).symm
      rw [s1, s1] at hp
      rw [gs_mul _ x _ hx, gs_mul _ x _ hx, gsC _ x _ hx, gsC _ x _ hx]
      exact hp
    rw [hρ i, hτ i, ← leib, ← leib, hA]

  intro Z r z J hJ
  obtain ⟨i, hi⟩ : ∃ i, r z ∈ h.W i := by
    have : r z ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hz1 := hJ.mem (fun _ : Fin 1 => m) r
  have hz2 : r z ∈ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := hWc i hi
  have sv : ∀ σ : SecM m L k, sval σ r z J =
      (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ m)) (fun _ => h.j i)).val *
        gs r z (h.W i) (rsT (σ.f fun _ => h.j i) (h.W i)) := fun σ => by
    exact (sec_trans σ r z hz1 hz2).trans (congrArg _ (gsR r z (hWc i) hi _).symm)
  have E := congrArg (gs r z (h.W i)) (onW i)
  simp only [gs_add r z _ hi, gs_mul r z _ hi, gsC r z _ hi] at E
  rw [sv ρ, sv τ, sv ρ', sv τ']
  linear_combination (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ m)) (fun _ => h.j i)).val * E

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEqUnitMulOneAddEpsPotential
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
namespace GlobalTheory.ConnUnit
open GlobalTheory.KS

theorem constFn_mul {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (O : X.Opens) (a b : R) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp only [constFn, map_mul]

theorem constFn_eps_sq {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Sp (DualNumber k)) (O : X.Opens) :
    constFn q O DualNumber.eps * constFn q O DualNumber.eps = 0 := by
  rw [← constFn_mul, DualNumber.eps_mul_eps]; simp only [constFn, map_zero]

theorem rsT_resG {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ U) (x : Γ(Y, U)) {Q : Y.Opens} (hQ : Q ≤ V) :
    rsT (resG Y h x) Q = rsT x Q := by
  rw [← rsT_of_le h, rsT_rsT h hQ]

theorem rsT_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (x : Γ(Y, U)) {Q : Z.Opens} (hQ : Q ≤ f ⁻¹ᵁ U) :
    rsT ((f.app U).hom x) Q = pbT f x Q := by
  rw [rsT_of_le hQ, pbT_of_le f hQ]
  rfl

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le (f ≫ g) (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem constFn_top_appTop {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (x : Γ(Sp R, ⊤)) :
    constFn q ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = q.appTop.hom x := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  unfold constFn
  rw [e]
  exact congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_eq_app (f := q) (U := ⊤))

theorem preimage_le_of_eps {k : Type} [Field k] {B X : Scheme.{0}} (q : B ⟶ Sp (DualNumber k)) (π₁ π₂ : B ⟶ X)
    (e : ∀ W : X.Opens, Γ(X, W) → Γ(B, π₂ ⁻¹ᵁ W))
    (hid : ∀ (W : X.Opens) (f : Γ(X, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) +
      constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W f) (W : X.Opens) : π₂ ⁻¹ᵁ W ≤ π₁ ⁻¹ᵁ W := by
  by_contra h
  have h1 := hid W 1
  rw [pbT, dif_neg h, pbT_one π₂ le_rfl] at h1
  have hu : (1 + constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W 1) *
      (1 - constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W 1) = 1 := by
    linear_combination (-(e W 1) ^ 2) * constFn_eps_sq q (π₂ ⁻¹ᵁ W)
  rw [← h1, zero_mul] at hu
  apply h
  intro y hy
  exfalso
  haveI : Nonempty (π₂ ⁻¹ᵁ W) := ⟨⟨y, hy⟩⟩
  exact zero_ne_one hu

theorem rsT_inv_mul {Y : Scheme.{0}} {U : Y.Opens} (u : Γ(Y, U)ˣ) {Q : Y.Opens} (hQ : Q ≤ U) :
    rsT (↑(u⁻¹) : Γ(Y, U)) Q * rsT (u : Γ(Y, U)) Q = 1 := by
  rw [← rsT_mul, Units.inv_mul, rsT_one hQ]

theorem rsT_res_val {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ U) (u : Γ(Y, U)ˣ) {Q : Y.Opens} (hQ : Q ≤ V) :
    rsT ((res h u : Γ(Y, V)ˣ) : Γ(Y, V)) Q = rsT (u : Γ(Y, U)) Q :=
  rsT_resG h (u : Γ(Y, U)) hQ

theorem rsT_pullU_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (u : Γ(Y, U)ˣ) {Q : Z.Opens}
    (hQ : Q ≤ f ⁻¹ᵁ U) : rsT ((pullU f U u : Γ(Z, f ⁻¹ᵁ U)ˣ) : Γ(Z, f ⁻¹ᵁ U)) Q = pbT f (u : Γ(Y, U)) Q :=
  rsT_app f U (u : Γ(Y, U)) hQ

theorem rsT_pull_g {Y Z : Scheme.{0}} (L : LB Y) (f : Z ⟶ Y) (a b : L.ι) (Q : Z.Opens)
    (hQ : Q ≤ f ⁻¹ᵁ (L.U a ⊓ L.U b)) (hQ' : Q ≤ (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) :
    rsT ((L.pull f).g (fun _ => a) (fun _ => b) : Γ(Z, (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b))) Q =
      pbT f (L.g a b : Γ(Y, L.U a ⊓ L.U b)) Q := by
  simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  erw [rsT_res_val _ _ hQ', rsT_pullU_val _ _ _ hQ]

theorem isGen_rel {B X : Scheme.{0}} (L : LB X) (π₁ π₂ : B ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂))
    (hw : w.IsGen) (a b : L.ι) (Q : B.Opens) (hQ1 : Q ≤ π₁ ⁻¹ᵁ (L.U a ⊓ L.U b))
    (hQ2 : Q ≤ π₂ ⁻¹ᵁ (L.U a ⊓ L.U b)) :
    rsT (w.s (fun _ => a, fun _ => a)).val Q * pbT π₁ (L.g a b).val Q =
      pbT π₂ (L.g a b).val Q * rsT (w.s (fun _ => b, fun _ => b)).val Q := by
  have hQa : Q ≤ ((L.pull π₂).div (L.pull π₁)).U (fun _ => a, fun _ => a) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => (hQ2 hy).1, Set.mem_iInter.2 fun _ => (hQ1 hy).1⟩
  have hQb : Q ≤ ((L.pull π₂).div (L.pull π₁)).U (fun _ => b, fun _ => b) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => (hQ2 hy).2, Set.mem_iInter.2 fun _ => (hQ1 hy).2⟩
  have hQab := le_inf hQa hQb
  have h := congrArg (fun u => rsT (Units.val u) Q) (hw (fun _ => a, fun _ => a) (fun _ => b, fun _ => b))
  rw [rsT_res_val _ _ hQab, Units.val_mul, rsT_mul, rsT_res_val _ _ hQab] at h
  rw [h]
  simp only [LB.div]
  rw [Units.val_mul, rsT_mul]
  erw [rsT_res_val _ _ hQab]
  have hM := rsT_pull_g L π₂ a b Q hQ2 (le_inf (hQa.trans inf_le_left) (hQb.trans inf_le_left))
  have hN := rsT_pull_g L π₁ a b Q hQ1 (le_inf (hQa.trans inf_le_right) (hQb.trans inf_le_right))
  rw [← map_inv]
  erw [rsT_res_val _ _ hQab]
  have hI := rsT_inv_mul ((L.pull π₁).g (fun _ => a) (fun _ => b))
    (le_inf (hQa.trans inf_le_right) (hQb.trans inf_le_right))
  rw [hN] at hI
  rw [hM]
  rw [show ∀ x y z t : Γ(B, Q), x * y * z * t = x * z * (y * t) from fun _ _ _ _ => by ring]
  erw [hI]
  exact _root_.mul_one _

theorem unit_mul_one_add_eps : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ _ _ A₀ _ m₀ _ pr hpr _ J V jj ed pb hconn hid w hw
  obtain ⟨-, hcov, hVU, hcoc⟩ := hconn
  have hle : ∀ W, π₂ ⁻¹ᵁ W ≤ π₁ ⁻¹ᵁ W :=
    preimage_le_of_eps B'.hom π₁ π₂ (fun W f => pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) hid
  have hpre : ∀ U, π₂ ⁻¹ᵁ U = pr ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := fun U => by rw [← hpr]; rfl
  have hE2 : ∀ O : B'.left.Opens, constFn B'.hom O DualNumber.eps * constFn B'.hom O DualNumber.eps = 0 :=
    fun O => constFn_eps_sq B'.hom O
  have hchart : ∀ i, π₂ ⁻¹ᵁ V i ≤ ((P.L.pull π₂).div (P.L.pull π₁)).U (fun _ => jj i, fun _ => jj i) :=
    fun i y hy => ⟨Set.mem_iInter.2 fun _ => hVU i hy, Set.mem_iInter.2 fun _ => hVU i (hle _ hy)⟩
  have hcovB : (⊤ : B'.left.Opens) ≤ ⨆ i, π₂ ⁻¹ᵁ V i := by
    have := GlobalTheory.KS.le_iSup_inf_preimage π₂ V hcov ⊤
    simpa only [top_inf_eq] using this

  let u : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i)
  let E : ∀ O : B'.left.Opens, Γ(B'.left, O) := fun O => constFn B'.hom O DualNumber.eps
  let Pf : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => pbT pr (pb i) (π₂ ⁻¹ᵁ V i)
  let t : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => u i * (1 - E _ * Pf i)
  let s : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i =>
    rsT ((w.s (fun _ => jj i, fun _ => jj i))⁻¹).val (π₂ ⁻¹ᵁ V i) * (1 + E _ * Pf i)

  have hres : ∀ i i', rsT (u i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (Pf i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (E (π₂ ⁻¹ᵁ V i)) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = E (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    refine ⟨rsT_rsT (hchart i) inf_le_left _, rsT_pbT pr (hpre (V i)).le inf_le_left _,
      rsT_constFn B'.hom inf_le_left _⟩
  have hres' : ∀ i i', rsT (u i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (Pf i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (E (π₂ ⁻¹ᵁ V i')) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = E (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    refine ⟨rsT_rsT (hchart i') inf_le_right _, rsT_pbT pr (hpre (V i')).le inf_le_right _,
      rsT_constFn B'.hom inf_le_right _⟩

  have key : ∀ i i', rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        (1 + E _ * (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i'))) := by
    intro i i'
    have hVV : V i ⊓ V i' ≤ P.L.U (jj i) ⊓ P.L.U (jj i') := inf_le_inf (hVU i) (hVU i')
    have hQ2 : π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' ≤ π₂ ⁻¹ᵁ (V i ⊓ V i') := le_rfl
    have hQ1 : π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' ≤ π₁ ⁻¹ᵁ (V i ⊓ V i') := hQ2.trans (hle _)
    have rel := isGen_rel P.L π₁ π₂ w hw (jj i) (jj i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')
      (hQ1.trans (π₁.preimage_mono hVV)) (hQ2.trans (π₂.preimage_mono hVV))
    have h := hid (V i ⊓ V i') (rsT (P.L.g (jj i) (jj i')).val (V i ⊓ V i'))
    rw [hcoc i i', pbT_mul, pbT_sub, pbT_pbT pr m₀ (m₀.preimage_mono hVV) (hpre _).le, hpr,
      pbT_rsT pr (m₀.preimage_mono inf_le_right) (hpre _).le, pbT_rsT pr (m₀.preimage_mono inf_le_left) (hpre _).le,
      pbT_rsT π₁ hVV (hle _), pbT_rsT π₂ hVV le_rfl] at h
    have hQeq : π₂ ⁻¹ᵁ (V i ⊓ V i') = π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' := rfl
    rw [hQeq] at h
    have hG : pbT π₂ ((P.L.g (jj i) (jj i'))⁻¹).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        pbT π₂ (P.L.g (jj i) (jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = 1 := by
      rw [← pbT_mul, Units.inv_mul, pbT_one π₂ (hQ2.trans (π₂.preimage_mono hVV))]
    rw [h] at rel
    linear_combination (-(rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') -
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        (1 + E _ * (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i'))))) * hG
      - pbT π₂ ((P.L.g (jj i) (jj i'))⁻¹).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * rel

  have ht : ∀ i i', rsT (t i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = rsT (t i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    obtain ⟨a1, a2, a3⟩ := hres i i'
    obtain ⟨b1, b2, b3⟩ := hres' i i'
    simp only [t, rsT_mul, rsT_sub, rsT_one inf_le_left, rsT_one inf_le_right, a1, a2, a3, b1, b2, b3, key i i']
    linear_combination (rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
      (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) *
      pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) * hE2 _
  have hts : ∀ i, t i * s i = 1 := by
    intro i
    have hinv := rsT_inv_mul (w.s (fun _ => jj i, fun _ => jj i)) (hchart i)
    simp only [t, s, u]
    linear_combination (1 - E _ * Pf i * (E _ * Pf i)) * hinv - (Pf i * Pf i) * hE2 _
  have hs : ∀ i i', rsT (s i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = rsT (s i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    have e1 := congrArg (fun f => rsT f (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) (hts i)
    have e2 := congrArg (fun f => rsT f (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) (hts i')
    simp only [rsT_mul, rsT_one inf_le_left, rsT_one inf_le_right] at e1 e2
    rw [← ht i i'] at e2
    linear_combination rsT (s i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * e1 - rsT (s i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * e2
  obtain ⟨T, hT⟩ := GlobalTheory.KS.exists_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB t ht
  obtain ⟨S, hS⟩ := GlobalTheory.KS.exists_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB s hs
  have hTS : T * S = 1 := by
    refine GlobalTheory.KS.eq_of_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB _ _ fun i => ?_
    rw [rsT_mul, hT, hS, hts, rsT_one le_top]

  have hab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback P.isAb h₁
  have hbij := GlobalTheory.allSixLaws.1.globalFns (Sp (DualNumber k)) B' hab
  obtain ⟨x, hx⟩ := hbij.2 T
  obtain ⟨y, hy⟩ := hbij.2 S
  have hxy : x * y = 1 := hbij.1 (by rw [map_mul, hx, hy, hTS, map_one])
  refine ⟨⟨(Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom x,
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom y,
    by rw [← map_mul, hxy, map_one], by rw [← map_mul, _root_.mul_comm, hxy, map_one]⟩, fun i => ?_⟩
  have hκ : constFn B'.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom x) = T :=
    (constFn_top_appTop B'.hom x).trans hx
  have hc := hT i
  rw [← hκ, rsT_constFn B'.hom le_top] at hc
  simp only [t, u, Pf, E] at hc
  show u i = _
  simp only [u]
  linear_combination (-(1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i))) * hc +
    (rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) * pbT pr (pb i) (π₂ ⁻¹ᵁ V i) ^ 2) * hE2 _

end GlobalTheory.ConnUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundary
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

namespace GlobalTheory.ChartAbLocus

theorem mem_abLocus_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m d))), SABMap t Y.t (ξ ≫ genι Y) → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal := by
  intro E _ _ _ H Dw l Xo c Y k _ m d ξ t φ hbd p
  rw [← hbd, mem_genBd_iff, not_not, ← abLocus_pullback abLocusOne Y.t.semi φ.cart.1 p]
  rfl

end GlobalTheory.ChartAbLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyParamNeZeroStatement
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
theorem _root_.GlobalTheory.T.monomialBoundaryFamily_param_ne_zero : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → LinearIndependent ℤ gam → (∀ i y z, gam i y z = gam i z y) → ∀ i, t i ≠ 0 := by
  first | exact @GlobalTheory.MonoParam.t_ne_zero | exact GlobalTheory.MonoParam.t_ne_zero | (intros; apply GlobalTheory.MonoParam.t_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfScaledSectionValues
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

theorem VS.mul : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y), L.IsLB → ∀ (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k l : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g l s' → GlobalTheory.HeatSym.VS φ L x g (k + l) (s * s') := by
  intro R Ω _ _ _ φ Y L hL x g k l s s' h h'
  obtain ⟨r, σ, ω, hr, hv, he⟩ := h
  obtain ⟨r', σ', ω', hr', hv', he'⟩ := h'
  have hF : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 Y) (fun _ : Fin 1 => 𝟙 Y))
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) (fun _ : Fin 1 => (l : ℤ)))
      (fun _ : Fin 1 => 𝟙 Y) (fun _ => ((k + l : ℕ) : ℤ)) := by
    intro U _ f
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.prod_singleton]
    push_cast
    rw [zpow_add]
  obtain ⟨σ'', hσ''⟩ := exists_sec hL hF (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec σ σ')
  refine ⟨r * r', σ'', ω * ω', mul_ne_zero hr hr', ?_, ?_⟩
  · intro Z q z J hJ
    rw [hσ'' Z (q ≫ x) z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec σ σ' (q ≫ x) z hJ, hv Z q z J hJ, hv' Z q z J hJ,
      map_mul, gs_mul q z ⊤ trivial, pow_add, Units.val_mul]
    ring
  · rw [map_mul, map_mul, map_mul, he, he']
    ring

end GlobalTheory.HeatSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenChartOfSmoothFamilyGeomFibreInjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openChart_of_smoothFamily_geomFibreInjective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → FibInj A M → IsChart A M := by
  first | exact @GlobalTheory.ChartCrit.openChart | exact GlobalTheory.ChartCrit.openChart | (intros; apply GlobalTheory.ChartCrit.openChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldCommVectorField
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

namespace GlobalTheory.GenericVal

theorem exists_affine_le_preimage {X : Scheme.{0}} {Ω : Type} [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := x.base (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
  refine ⟨U, hU, fun p _ => ?_⟩
  have hsp : (p : PrimeSpectrum Ω) ⤳ IsLocalRing.closedPoint Ω :=
    (PrimeSpectrum.le_iff_specializes (R := Ω) p (IsLocalRing.closedPoint Ω)).1
      (show p.asIdeal ≤ IsLocalRing.maximalIdeal Ω from IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
  exact hsp.mem_open (x ⁻¹ᵁ U).isOpen hyU

theorem valR_generic : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (dd : Fld X) (δ : Derivation ℤ Ω Ω) (δL : Derivation ℤ (FractionRing Ω) (FractionRing Ω)), IsField ⊤ dd → (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd O f) = δ (valR x O f)) → (∀ ω, δL (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω)) → ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (dd O f) = δL (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  intro X Ω _ _ _ x dd δ δL hF hx hδL O f hO
  obtain ⟨U, hU, hxU⟩ := exists_affine_le_preimage x
  set ξ := spMap (algebraMap Ω (FractionRing Ω)) ≫ x with hξ
  have hξU : ⊤ ≤ ξ ⁻¹ᵁ U := fun q _ => hxU (show (spMap (algebraMap Ω (FractionRing Ω))).base q ∈ (⊤ : (Sp Ω).Opens) from trivial)
  let q₀ : Sp (FractionRing Ω) := default
  have hq : ξ.base q₀ ∈ O ⊓ U := ⟨hO trivial, hξU trivial⟩
  obtain ⟨s, hsle, hsmem⟩ := hU.exists_basicOpen_le (V := O ⊓ U) ⟨ξ.base q₀, hq⟩ hq.2
  set W := X.basicOpen s with hWdef
  have hWO : W ≤ O := hsle.trans inf_le_left
  have hWU : W ≤ U := X.basicOpen_le s
  have hW : ⊤ ≤ ξ ⁻¹ᵁ W := fun q _ => by
    rw [Subsingleton.elim q q₀]; exact hsmem
  letI : Algebra Γ(X, U) Γ(X, W) := (resG X hWU).toAlgebra
  haveI : IsLocalization.Away s Γ(X, W) := hU.isLocalization_basicOpen s
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) (resG X hWO f)
  have hmu : IsUnit (resG X hWU (m : Γ(X, U))) := IsLocalization.map_units Γ(X, W) m
  change resG X hWO f * resG X hWU (m : Γ(X, U)) = resG X hWU a at hm
  have vres : ∀ {V' : X.Opens} (e : W ≤ V') (g : Γ(X, V')), valR ξ W (resG X e g) = valR ξ V' g :=
    fun e g => GlobalTheory.Points.valR_res ξ e hW g
  have vU : ∀ g : Γ(X, U), valR ξ U g = algebraMap Ω (FractionRing Ω) (valR x U g) := fun g =>
    GlobalTheory.Points.valR_spMap_comp _ x U hxU g
  have hdd : ∀ g : Γ(X, U), dd W (resG X hWU g) = resG X hWU (dd U g) := fun g => hF.2.2 U W hWU le_top g
  have hddO : dd W (resG X hWO f) = resG X hWO (dd O f) := hF.2.2 O W hWO le_top f
  have hL := hF.2.1 W le_top (resG X hWO f) (resG X hWU (m : Γ(X, U)))
  rw [hm, hdd, hdd, hddO] at hL
  have e1 := congrArg (valR ξ W) hL
  have e2 := congrArg (valR ξ W) hm
  simp only [GlobalTheory.Points.valR_add ξ W hW, GlobalTheory.Points.valR_mul ξ W hW, vres, vU, hx U _ hxU] at e1 e2
  have hM : IsUnit (algebraMap Ω (FractionRing Ω) (valR x U (m : Γ(X, U)))) := by
    have h1 := hmu.map (GlobalTheory.Points.valMap ξ W hW).hom
    rwa [← GlobalTheory.Points.valR_eq, vres, vU] at h1
  have e3 := congrArg δL e2
  rw [Derivation.leibniz, hδL, hδL, smul_eq_mul, smul_eq_mul] at e3
  apply hM.mul_left_cancel
  linear_combination -e1 - e3

end GlobalTheory.GenericVal
end
end

