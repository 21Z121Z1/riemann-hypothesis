import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Uniformization.FinrankComplexReal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaLin

theorem gs_scal_comp {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y)
    (z : Z) (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem exists_linearEquiv {F : Type} [CommRing F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) (pr m : Y ⟶ X) (τ σ : Y ⟶ Y) (hm : τ ≫ pr = m) (h₁ : σ ≫ τ = 𝟙 Y)
    (h₂ : τ ≫ σ = 𝟙 Y) (hq : τ ≫ q = q) (k : ℤ)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![k, -k])) (hu : u.IsGen) :
    ∃ Φ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) ≃ₗ[F]
        SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ v (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval (Φ v).sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := by
  have ex : ∀ v : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∃ w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval w.sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := fun v => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k)
      (fun U _ h => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
          hm, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
      (pullMulSec v.sec τ u hu)
    exact ⟨SecMod.mk q s', fun Z r z J hJ =>
      (hs' Z r z J hJ).trans ((sval_pullMulSec _ _ u hu r z hJ).trans (_root_.mul_comm _ _))⟩
  choose f hf using ex
  have ext : ∀ v w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      (∀ y J, Good L y J → sval v.sec (𝟙 Y) y J = sval w.sec (𝟙 Y) y J) → v = w :=
    fun v w h => SecMod.ext (sec_ext_val hL h)
  let Φ₀ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) →ₗ[F]
      SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) :=
    { toFun := f
      map_add' := fun v w => ext _ _ fun y J hJ => by
        rw [SecMod.sval_add hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_add hJ, mul_add]
      map_smul' := fun c v => ext _ _ fun y J hJ => by
        rw [RingHom.id_apply, SecMod.sval_smul hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_smul hJ,
          gs_scal_comp q (𝟙 Y ≫ τ), Category.assoc, hq, Category.id_comp q, mul_left_comm] }
  refine ⟨LinearEquiv.ofBijective Φ₀ ⟨fun v w h => ext _ _ fun y J hJ => ?_, fun w => ?_⟩, hf⟩
  · have e : f v = f w := h
    have := (hf v _ σ y J hJ).symm.trans (e ▸ hf w _ σ y J hJ)
    rwa [h₁, Units.mul_right_inj] at this
  · have hv := DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _ hu) σ
    have h₃ : σ ≫ m = pr := by rw [← hm, ← Category.assoc, h₁, Category.id_comp]
    obtain ⟨s, hs⟩ := exists_sec (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k) hL (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        h₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv, mul_inv_cancel_left])
      (pullMulSec w.sec σ _ hv)
    refine ⟨SecMod.mk q s, ext _ _ fun y J hJ => (hf _ _ _ y J hJ).trans ?_⟩
    rw [SecMod.sec_mk, hs _ _ y J hJ, sval_pullMulSec _ σ _ hv _ y hJ, val_pull hJ, val_inv, Category.assoc, h₂,
      Category.comp_id, mul_left_comm, Units.mul_inv, _root_.mul_one]

section Twist

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
  {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}

theorem sval_of_isTwistPull {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' r z J = (val α r z J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hz := hJ.mem ![(snd T A).left, m.left] r
  have key : ∀ j : Fin 2 → L.ι, r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j)).val *
          gs (r ≫ ψ.left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j hz =>
    (gs_res r z _ hz _).symm.trans ((congrArg (gs r z _) (H j)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hz _) ((gs_res r z _ hz _).trans
        (gs_pull r ψ.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
          (chart_le_pull A L ψ m hm j hz) _)))))
  have e₁ := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J
    (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, e])
  exact (key _ hz).trans (congrArg _ e₁.symm)

theorem isTwistPull_of_sval (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by
  intro j
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have h0 := chart_le_zero A L m j hy
  have h1 := chart_le_pull A L ψ m hm j hy
  refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hy _) ((gs_res _ y _ hy _).trans
      (gs_pull _ ψ.left y _ h1 _)))).symm)
  refine (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y h0
    (Good.mem hJ _ _)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val (gen_trans hα (𝟙 _) y hy (Good.mem hJ _ _)))
    (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y h1
    (Good.mem hJ _ _))).symm
  refine (congrArg _ (H y J hJ)).trans ?_
  rw [Units.val_mul]
  refine Eq.trans ?_ (_root_.mul_mul_mul_comm _ _ _ _)
  rw [← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e' : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, e]
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, zpow_neg]
  rw [e']
  exact (inv_mul_cancel_right _ _).symm

end Twist

section Transl

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem lift_translT {T' : Over S} (ρ : T' ⟶ T) (x : T' ⟶ A) (c : T ⟶ A) :
    lift ρ x ≫ translT A c = lift ρ ((ρ ≫ c) * x) := by
  have e : translPt A c = (fst T A ≫ c) * snd T A := rfl
  rw [translT, comp_lift, lift_fst, e, MonObj.comp_mul, lift_fst_assoc, lift_snd]

theorem translT_comp (c d : T ⟶ A) (h : d * c = 1) : translT A c ≫ translT A d = 𝟙 _ := by
  have e : translPt A c = (fst T A ≫ c) * snd T A := rfl
  rw [translT, lift_translT, e, ← _root_.mul_assoc, ← MonObj.comp_mul, h, MonObj.comp_one, _root_.one_mul,
    lift_fst_snd]

end Transl

theorem main : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) (θ : ThetaGrp P.A P.L (k : ℤ) (Over.mk p)), ∃ Φ : EA P p k ≃ₗ[F] EA P p k, (∀ v, IsActOf P.A P.L (k : ℤ) θ v.sec (Φ v).sec) ∧ (∀ v v', IsActOf P.A P.L (k : ℤ) θ v v' → v' = (Φ (SecMod.mk _ v)).sec) ∧ ∀ (v : EA P p k) (T : Over S) (ρ : T ⟶ Over.mk p) (x : T ⟶ P.A) (z : T.left) (J), Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) (Φ v).sec (lift ρ x).left z J = (val (L := P.L) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![(k : ℤ), -(k : ℤ)]) θ.φ (lift ρ x).left z J).val * sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := by
  intro S P F _ p k θ
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv (F := F) P.isLB (fst (Over.mk p) P.A).left (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (translT P.A θ.pt⁻¹).left
    (by rw [← Over.comp_left, translT, lift_snd])
    (by rw [← Over.comp_left, translT_comp _ _ _ (mul_inv_cancel _), Over.id_left])
    (by rw [← Over.comp_left, translT_comp _ _ _ (inv_mul_cancel _), Over.id_left])
    (((Over.comp_left _ _ _ _ _).symm.trans (by rw [translT, lift_fst]))) (k : ℤ) θ.φ θ.isGen
  refine ⟨Φ, fun v => isTwistPull_of_sval P.A P.isLB θ.isGen fun y J hJ => hΦ v _ _ y J hJ, fun v v' h => ?_,
    fun v T ρ x z J hJ => ?_⟩
  · exact DVR.SecOps.sec_ext (sec_ext_val P.isLB fun y J hJ =>
      (sval_of_isTwistPull P.A h (𝟙 _) y hJ).trans (hΦ (SecMod.mk _ v) _ _ y J hJ).symm)
  · refine (hΦ v _ _ z J hJ).trans ?_
    rw [← Over.comp_left, lift_translT]
    rfl

end GlobalTheory.ThetaLin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordinateSumDifferenceAdditionFactor
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.AddLevel

theorem expand_alg {S X : Type} [CommRing S] {n : ℕ} (s s₀ : Finset X) (F F' : Fin n → X → S) (σ σ' : Fin n → S)
    (p m : X → S) (θp θm r : S) (tx ty tp tm : X → Sˣ) (Wx Wy Wp Wm kL kM : Sˣ) (k u v : X → X → Sˣ)
    (hx : ∀ i, Wx.val ^ 2 * σ i = ∑ α ∈ s, F i α * (tx α).val)
    (hy : ∀ i, Wy.val ^ 2 * σ' i = ∑ α ∈ s, F' i α * (ty α).val)
    (hp : Wp.val ^ 1 * θp = ∑ a ∈ s₀, p a * (tp a).val) (hm : Wm.val ^ 1 * θm = ∑ a ∈ s₀, m a * (tm a).val)
    (hadd : ∑ i, σ i * σ' i = r * kL.val * (θp * θm))
    (hk : Wx ^ 2 * Wy ^ 2 * kL = kM * (Wp * Wm))
    (ht : ∀ a b, kM * (tp a * tm b) = k a b * (u a b * v a b)) :
    ∑ α ∈ s, ∑ β ∈ s, (∑ i, F i α * F' i β) * ((tx α).val * (ty β).val) =
      ∑ a ∈ s₀, ∑ b ∈ s₀, r * (k a b).val * (p a * m b) * ((u a b).val * (v a b).val) := by
  have hk' := congrArg Units.val hk
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hk'
  have e₁ : ∑ α ∈ s, ∑ β ∈ s, (∑ i, F i α * F' i β) * ((tx α).val * (ty β).val) =
      ∑ i, (∑ α ∈ s, F i α * (tx α).val) * (∑ β ∈ s, F' i β * (ty β).val) := by
    simp only [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.univ)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm (s := Finset.univ)]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun i _ => by ring
  have e₂ : ∑ a ∈ s₀, ∑ b ∈ s₀, r * (k a b).val * (p a * m b) * ((u a b).val * (v a b).val) =
      r * kM.val * ((∑ a ∈ s₀, p a * (tp a).val) * (∑ b ∈ s₀, m b * (tm b).val)) := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h := congrArg Units.val (ht a b)
    simp only [Units.val_mul] at h
    linear_combination (-(r * p a * m b)) * h
  have e₃ : ∑ i, Wx.val ^ 2 * σ i * (Wy.val ^ 2 * σ' i) = Wx.val ^ 2 * Wy.val ^ 2 * ∑ i, σ i * σ' i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e₁, e₂, ← hp, ← hm]
  simp only [← hx, ← hy]
  rw [e₃, hadd]
  linear_combination (r * θp * θm) * hk'

theorem unit_alg {U : Type} [CommGroup U] {k p m c₁ c₂ c₃ d₁ d₂ u v : U}
    (h : p * m * (c₁ * c₂ * c₃) = u * v * (d₁ * d₂)) :
    k * (p * m) = k * d₁ * d₂ * (c₁ * c₂ * c₃)⁻¹ * (u * v) := by
  rw [eq_mul_inv_of_mul_eq h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {e : ℕ}

noncomputable def toG (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
    map_mul (pushHom (isGrpPullback_pullback G (thick R I e)) T) x y

noncomputable def toB (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ g.pG) (GlobalTheory.TorusCoord.im_mul g)

theorem lift_snd_left {S : Scheme.{0}} {T B : Over S} (x : T ⟶ B) :
    (lift (toUnit T) x).left ≫ (snd (𝟙_ _) B).left = x.left := by
  rw [← Over.comp_left, lift_snd]

theorem lift_fst_left {S : Scheme.{0}} {T B : Over S} (x : T ⟶ B) :
    (lift (toUnit T) x).left ≫ (fst (𝟙_ _) B).left = (toUnit T).left := by
  rw [← Over.comp_left, lift_fst]

theorem exp_at (U : PreU I D A G) {k : ℕ} {σ : U.SecGT (𝟙_ _) k} {f : ∀ α, SecBT D (𝟙_ _) k α}
    (h : U.ExpT (𝟙_ _) k σ f) (e : ℕ) : ∃ s : Finset D.X,
      ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : T ⟶ thickObj R I e G) (z : T.left) (JG) (J),
      Good U.P.L.L z JG → Good D.P.L z J →
      (∀ α ∉ s, sval (Z := T.left) (f α) (lift (toUnit _) (toB (U.gt e) T x)).left z J = 0) ∧ ∀ s', s ⊆ s' →
      (gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => JG (x.left ≫ (fstG I e G).left))).val ^ k *
          sval (Z := T.left) σ (lift (toUnit _) (toG G T x)).left z JG =
        ∑ α ∈ s', sval (Z := T.left) (f α) (lift (toUnit _) (toB (U.gt e) T x)).left z J *
          (val ((U.gt e).t α) x.left z J).val := by
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, fun T x z JG J hG hJ => ?_⟩
  obtain ⟨h₁, h₂⟩ := hs T.left x.left (lift (toUnit _) (toG G T x)).left (lift (toUnit _) (toB (U.gt e) T x)).left
    (lift_snd_left _) (lift_snd_left _) ((lift_fst_left _).trans (lift_fst_left _).symm) z JG J hG hJ
  refine ⟨h₁, fun s' hs' => h₂.trans (Finset.sum_subset hs' fun α _ hα => ?_)⟩
  rw [h₁ α hα, zero_mul]

theorem val_t_add (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {z : T.left} {J}
    (hJ : Good D.P.L z J) (a b : D.X) (x : T ⟶ thickObj R I e G) :
    val (g.t (a + b)) x.left z J * @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
      (cT D _ a) (cT D _ b) (toB g T x)) = val (g.t a) x.left z J * val (g.t b) x.left z J := by
  refine Eq.trans ?_ ((val_corr hJ (g.t_mul a b) x.left).trans (val_mul hJ _ _ _))
  refine Eq.trans ?_ (val_mul hJ _ _ _).symm
  refine congrArg (_ * ·) (Eq.trans ?_ (val_cub D.cub ((Over.map (thick R I e)).map x) hJ _ _ _).symm)
  have e₁ : ∀ c : D.X, (Over.map (thick R I e)).map x ≫ toUnit _ ≫ D.c c = cT D _ c := fun c => by
    rw [← Category.assoc, comp_toUnit]
  rw [e₁, e₁]
  rfl
end

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {e : ℕ}

theorem additionFormulaFactor_comparisonIso_value (U : PreU I D A G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {z : T.left} {JG} {J}
    (hG : Good U.P.L.L z JG) (hJ : Good D.P.L z J) (W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ)
    (hW : ∀ x, W x = gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => JG (x.left ≫ (fstG I e G).left)))
    (x y : T ⟶ thickObj R I e G) :
    W x ^ 2 * W y ^ 2 * @id (T.left.presheaf.stalk z)ˣ
        (kap0 U.P.c U.P.sym (T := (Over.map (thick R I e)).obj T) z JG (toG G T x) (toG G T y)) =
      @id (T.left.presheaf.stalk z)ˣ
        (kap0 D.cub D.sym (T := (Over.map (thick R I e)).obj T) z J (toB (U.gt e) T x) (toB (U.gt e) T y)) *
        (W (x * y) * W (x * y⁻¹)) := by
  obtain ⟨h₁, h₂, h₃⟩ := U.w_vals e T z JG J hG hJ W hW
  have h := GlobalTheory.addition_factor_through_cubical_even_iso _ _ W _ _
    (fun a b c => cubV U.P.c (T := (Over.map (thick R I e)).obj T) z JG (toG G T a) (toG G T b) (toG G T c))
    (fun a b c => cubV D.cub (T := (Over.map (thick R I e)).obj T) z J (toB (U.gt e) T a) (toB (U.gt e) T b)
      (toB (U.gt e) T c)) _ _ h₁ h₂ h₃ x y
  simp only [map_inv] at h
  exact h

theorem torusCoordinate_sum_difference_additionFactor (hGF : GlobalFnsSt) (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {z : T.left} {J} (hJ : Good D.P.L z J) (x y : T ⟶ thickObj R I e G) (a b : D.X) :
    @id (T.left.presheaf.stalk z)ˣ
        (kap0 D.cub D.sym (T := (Over.map (thick R I e)).obj T) z J (toB g T x) (toB g T y)) *
        (val (g.t a) (x * y).left z J * val (g.t b) (x * y⁻¹).left z J) =
      @id (T.left.presheaf.stalk z)ˣ (kapV D a b (T := (Over.map (thick R I e)).obj T) z J (toB g T x) (toB g T y)) *
        (val (g.t (a + b)) x.left z J * val (g.t (a - b)) y.left z J) :=
  unit_alg (GlobalTheory.cub_coord_mul_mul_inv _ (T.left.presheaf.stalk z)ˣ D.X
    (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J)
    (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ) _ (toB g T) (cT D _)
    (fun a b => (congrArg (toUnit _ ≫ ·) (D.c_add a b)).trans (MonObj.comp_mul _ _ _))
    (fun a x => val (g.t a) x.left z J) (val_t_add g hJ)
    (fun a x y => torus_coord_add hGF R I D e G g T x y a z J hJ) a b x y)

theorem at_points (hGF : GlobalFnsSt) (U : PreU I D A G) (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : R)
    (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α) (hA : U.AddG θ r σ σ')
    (hθ : U.ExpT (𝟙_ _) 1 θ f₀) (hσ : ∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) (e : ℕ) :
    ∃ s₀ : Finset D.X, ∀ (T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x' y' : T' ⟶ thickObj R I e G)
      (x y : (Over.map (thick R I e)).obj T' ⟶ D.P.A), x = toB (U.gt e) T' x' → y = toB (U.gt e) T' y' →
      ∀ (z : ((Over.map (thick R I e)).obj T').left) (J), Good D.P.L z J →
      (∀ a ∉ s₀, sval (f₀ a) (lift (toUnit _) (x * y)).left z J = 0 ∧
        sval (f₀ a) (lift (toUnit _) (x * y⁻¹)).left z J = 0) ∧ ∀ s : Finset D.X, s₀ ⊆ s →
      ∑ α ∈ s, ∑ β ∈ s, (∑ i, sval (f i α) (lift (toUnit _) x).left z J * sval (f' i β) (lift (toUnit _) y).left z J) *
        ((val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t α) x'.left z J).val *
          (val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t β) y'.left z J).val) =
      ∑ a ∈ s₀, ∑ b ∈ s₀, gs (𝟙 _) z ⊤ (scal ((Over.map (thick R I e)).obj T').hom r) * (kapV D a b z J x y).val *
        (sval (f₀ a) (lift (toUnit _) (x * y)).left z J * sval (f₀ b) (lift (toUnit _) (x * y⁻¹)).left z J) *
        ((val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t (a + b)) x'.left z J).val *
          (val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t (a - b)) y'.left z J).val) := by
  classical
  obtain ⟨s₁, h₁⟩ := exp_at U hθ e
  choose s₂ h₂ using fun i => exp_at U (hσ i).1 e
  choose s₃ h₃ using fun i => exp_at U (hσ i).2 e
  obtain ⟨s₀, a₁, a₂, a₃⟩ : ∃ s₀ : Finset D.X, s₁ ⊆ s₀ ∧ (∀ i, s₂ i ⊆ s₀) ∧ ∀ i, s₃ i ⊆ s₀ :=
    ⟨s₁ ∪ (Finset.univ.biUnion s₂ ∪ Finset.univ.biUnion s₃), Finset.subset_union_left,
      fun i => ((Finset.subset_biUnion_of_mem s₂ (Finset.mem_univ i)).trans Finset.subset_union_left).trans
        Finset.subset_union_right,
      fun i => ((Finset.subset_biUnion_of_mem s₃ (Finset.mem_univ i)).trans Finset.subset_union_right).trans
        Finset.subset_union_right⟩
  refine ⟨s₀, fun T x y _ _ hx hy z J hJ => ?_⟩
  subst hx hy
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have p := h₁ T (x * y) z JG J hG hJ
  have m := h₁ T (x * y⁻¹) z JG J hG hJ
  simp only [map_mul, map_inv] at p m
  refine ⟨fun a ha => ⟨p.1 a fun h => ha (a₁ h), m.1 a fun h => ha (a₁ h)⟩, fun s hs => ?_⟩
  exact expand_alg s s₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun i => (h₂ i T x z JG J hG hJ).2 s ((a₂ i).trans hs)) (fun i => (h₃ i T y z JG J hG hJ).2 s ((a₃ i).trans hs))
    (p.2 s₀ a₁) (m.2 s₀ a₁) (hA _ (toG G T x) (toG G T y) z JG hG) (additionFormulaFactor_comparisonIso_value U hG hJ _ (fun _ => rfl) x y)
    (torusCoordinate_sum_difference_additionFactor hGF (U.gt e) hJ x y)

end

end GlobalTheory.AddLevel

theorem GlobalTheory.addition_formula_expanded_at_level : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α), U.AddG θ r σ σ' → U.ExpT (𝟙_ _) 1 θ f₀ → (∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) → ∀ e : ℕ, ∃ s₀ : Finset D.X, ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (U.gt e).pG.left = x.left → ye ≫ (U.gt e).pG.left = y.left → xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom = ye ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom → ∀ (z : T.left) (J), Good D.P.L z J → (∀ a ∉ s₀, sval (f₀ a) (lift (toUnit T) (x * y)).left z J = 0 ∧ sval (f₀ a) (lift (toUnit T) (x * y⁻¹)).left z J = 0) ∧ ∀ s : Finset D.X, s₀ ⊆ s → ∑ α ∈ s, ∑ β ∈ s, (∑ i, sval (f i α) (lift (toUnit T) x).left z J * sval (f' i β) (lift (toUnit T) y).left z J) * ((val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val) = ∑ a ∈ s₀, ∑ b ∈ s₀, gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val * (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J) * ((val ((U.gt e).t (a + b)) xe z J).val * (val ((U.gt e).t (a - b)) ye z J).val)) := by
  intro hGF V _ _ _ _ D A G _ _ U θ f₀ r n σ σ' f f' hA hθ hσ e
  obtain ⟨s₀, H⟩ := GlobalTheory.AddLevel.at_points hGF U θ f₀ r n σ σ' f f' hA hθ hσ e
  refine ⟨s₀, fun T x y xe ye hx hy hxy => ?_⟩
  have hT : T.hom = (xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom) ≫ thick V (IsLocalRing.maximalIdeal V) e := by
    rw [← Over.w x, ← hx, Category.assoc, Over.w, Category.assoc]
    rfl
  obtain ⟨Z, ⟨⟨⟩⟩, h⟩ := T
  change Z ⟶ _ at xe ye
  change h = (CategoryStruct.comp (X := Z) xe (thickObj V (IsLocalRing.maximalIdeal V) e G).hom ≫
    thick V (IsLocalRing.maximalIdeal V) e : Z ⟶ _) at hT
  subst hT
  exact H (Over.mk (xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom)) (Over.homMk xe rfl)
    (Over.homMk ye hxy.symm) x y (Over.OverMorphism.ext hx.symm) (Over.OverMorphism.ext hy.symm)
end

