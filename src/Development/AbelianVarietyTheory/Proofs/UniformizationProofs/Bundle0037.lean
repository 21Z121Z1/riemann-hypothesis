import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameOfOne
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.TorusWeight

theorem gs_map {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)) :
    gs r z U f = (r.stalkMap z).hom (gs (𝟙 X) (r z) U f) := by
  rw [gs_eq r z U h, gs_eq (𝟙 X) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h f).symm

theorem val_const {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (a : Γ(Y, ⊤))
    (h : ∀ y J, Good L y J → (val t (𝟙 _) y J).val = gs (𝟙 _) y ⊤ a) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    (val t r z J).val = gs r z ⊤ a := by
  have hJ' : Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ (r ≫ ψ)
  have e := h (r z) _ hJ'
  rw [val_of t (𝟙 _) (r z) _ (fun k => J (r ≫ φ k)) (fun k => by rw [Category.id_comp])] at e
  have hm := hJ.mem φ r
  refine (gs_unit r z _ hm _).symm.trans ((gs_map r z _ hm _).trans (Eq.trans ?_ (gs_map r z ⊤ trivial a).symm))
  exact congrArg _ ((gs_unit (𝟙 Y) (r z) _ hm _).trans e)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem normd_one {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    {u : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    val u (1 : TF (R := R) F ⟶ D.P.A).left z J = 1 :=
  (val_pull hJ u (eSec D.P.A) (toUnit (TF (R := R) F)).left).symm.trans ((val_corr hJ hu.2 _).trans (val_one _))

theorem psi_zero (hB : D.TauBimult) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi 0) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J = 1 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have z0 : (0 : D.X) + 0 = 0 := add_zero 0
  have hpt : ∀ a b c : D.X, a = b → ∀ (r : (TF (R := R) F).left ⟶ _),
      val (D.tau a c) r z J = val (D.tau b c) r z J := by rintro a b c rfl r; rfl
  have hpp : ∀ a b : D.X, a = b → ∀ (r : (TF (R := R) F).left ⟶ _), val (D.psi a) r z J = val (D.psi b) r z J := by
    rintro a b rfl r; rfl
  have hτ0 := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 0
  rw [hpt _ _ _ z0, cPoint_zero, C.face] at hτ0
  have t00 := (mul_left_cancel hτ0).symm
  have hψ := UUA.psi_add (𝟙 (TF (R := R) F)) hJ (0 : D.X) 0
  rw [hpp _ _ z0, t00, _root_.one_mul, _root_.mul_assoc] at hψ
  have h1 := left_eq_mul.1 hψ
  rw [Over.id_left, Category.id_comp] at h1
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) h1
  exact (val_pull hJ (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (toUnit (TK R)).left (jFK (R := R) F)).symm

theorem txFrame_of_one (hB : D.TauBimult) {N : ℕ} (p : QkPt D F N) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) {w : Frm D F N p.g.b} (hw : FrmOne w) : TXFrame N p w := by
  refine ⟨hw.1, fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
  · have e : val (p.g.s p.y) (𝟙 _) z J = 1 := Units.ext (by
      rw [hτ.2 _ z J hJ, hy, ofAdd_zero, map_one, CoefBasic.cst_eq]; exact map_one _)
    rw [hw.2 z J hJ, e, hτ.1, normd_one hν z hJ, one_pow, _root_.one_mul]
  · rw [hw.2 z J hJ, hτ.1, normd_one hκ z hJ, one_pow, _root_.one_mul, hy, psi_zero hB z hJ]

theorem sval_const {k : ℕ} (α : D.X) (ζ : F) (s s' : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) :
    (∀ j, s'.f j = DegPre.constBF D F ζ _ * s.f j) ↔
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        sval s' ρ.left z J = sval s ρ.left z J *
          gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) j, r z ∈ LB.wchart D.P.L (DegPre.famφ D F α) j →
      gs r z (LB.wchart D.P.L (DegPre.famφ D F α) j) (DegPre.constBF D F ζ _ * s.f j) =
        gs r z (LB.wchart D.P.L (DegPre.famφ D F α) j) (s.f j) *
          gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
    fun Z r z j hm => (gs_mul r z _ hm _ _).trans ((mul_comm _ _).trans (congrArg₂ (· * ·) rfl
      ((gs_res r z le_top hm _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _))))
  constructor
  · intro h T ρ z J hJ
    exact (congrArg (gs ρ.left z _) (h _)).trans (key _ ρ.left z _ (hJ.mem _ _))
  · intro h j
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB y
    have e := h _ (𝟙 _) y J hJ
    refine Eq.trans ?_ (key _ (𝟙 _) y j hy).symm
    refine (sec_trans s' (𝟙 _) y hy (hJ.mem _ (𝟙 _))).trans ?_
    rw [sec_trans s (𝟙 _) y hy (hJ.mem _ (𝟙 _)), _root_.mul_assoc]
    exact congrArg _ e

theorem phiRel_tor (hG : GlobalFnsSt) {N : ℕ} (p : QkPt D F N) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) {w : Frm D F N p.g.b} (hw : FrmOne w) (s s' : Fam D F N) :
    PhiRel D F N p w s s' ↔
      ∀ α j, (s'.s α).f j = DegPre.constBF D F (τ (Multiplicative.ofAdd α)).val _ * (s.s α).f j := by
  have tr : DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.id_comp]; exact tr_fst D F _
    · rw [Category.id_comp]
      refine (tr_pr D F _).trans ?_
      rw [hτ.1, MonObj.comp_one, _root_.mul_one]
  have v : ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      (uVal D F N α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val =
        gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd α)).val) := by
    intro α T ρ z J hJ
    have C : IsCub (th D z J) := isCub_cubV D.cub hJ
    have hu : uVal D F N α p.g.b ρ z J = 1 := by
      rw [uVal, hτ.1]
      simp only [MonObj.comp_one]
      unfold cubN
      simp only [C.face₃, C.face₂, Finset.prod_const_one, inv_one, _root_.mul_one]
    have h₁ := val_const (p.g.s α) _ (hτ.2 α) (ρ ≫ fst _ _).left z hJ
    have h₂ := val_const w 1 (fun y J hJ => by
      rw [hw.2 y J hJ, gs_eq _ _ ⊤ trivial, map_one, map_one]; rfl) (ρ ≫ fst _ _).left z hJ
    rw [gs_eq _ _ ⊤ trivial, map_one, map_one] at h₂
    rw [hu, _root_.one_mul, val_mul hJ, Units.val_mul, h₁, h₂, _root_.mul_one]
  rw [phiRel_iff hG p w hw.1]
  constructor
  · intro H α
    refine (sval_const α _ _ _).2 fun T ρ z J hJ => ?_
    have := H α α (by rw [hy, add_zero]) T ρ z J hJ
    rwa [v α T ρ z J hJ, tr, Category.comp_id] at this
  · intro H α β h T ρ z J hJ
    obtain rfl : α = β := by rw [← h, hy, add_zero]
    rw [v α T ρ z J hJ, tr, Category.comp_id]
    exact (sval_const α _ _ _).1 (H α) T ρ z J hJ

theorem torus_weight : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) τ, p.y = 0 → IsTor τ p.g → ∀ w, TXFrame N p w → FrmOne w ∧ ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N p w s s' ↔ ∀ α j, (s'.s α).f j = DegPre.constBF D.toPre F (τ (Multiplicative.ofAdd α)).val _ * (s.s α).f j := by
  intro hL R _ _ _ I hI D A G _ _ _ U F _ _ _ N hN p τ hy hτ w hw
  obtain ⟨w₀, hw₀⟩ := (CoefBasic.coef_basic R D.toPre F N p.g).2.1 hτ.1
  have h₁ : FrmOne w := ⟨hw.1, fun z J hJ =>
    ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p).2 w w₀ hw (txFrame_of_one D.tau_bimult p hy hτ hw₀) z J hJ).trans (hw₀.2 z J hJ)⟩
  exact ⟨h₁, phiRel_tor hL.1.globalFns p hy hτ h₁⟩

end GlobalTheory.UT.TorusWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.QkPairing

theorem cub_comm {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k : ℕ) (a m b x : A)
    (Sa Sy Say τa τy τay ζ : U) (h₁ : Say * θ a (m ^ k) b = Sa * Sy) (h₂ : τay * θ a (b ^ k) m = τa * τy)
    (h₃ : τy * cubN θ k 1 b m = ζ * (Sy * cubN θ k 1 m b)) :
    cubN θ k a b (x * m) * (θ a (x * m) b)⁻¹ * Sa * (cubN θ k (a * b ^ k) m x * (θ (a * b ^ k) x m)⁻¹ * τay) =
      ζ * (cubN θ k a m (x * b) * (θ a (x * b) m)⁻¹ * τa * (cubN θ k (a * m ^ k) b x * (θ (a * m ^ k) x b)⁻¹ * Say)) := by
  have e₀ := h.N_split k a m b
  have e₁ := h.N_add k a m x b
  have e₂ := h.N_add k a b x m
  have e₃ := h.N_split k (a * m ^ k) b x
  have e₄ := h.N_split k (a * b ^ k) m x
  have e₅ := h.N_split k a m x
  have e₆ := h.N_split k a b x
  have e₇ := h.N_split k a b m
  have e₈ := h.coc a (m ^ k) (b ^ k) x
  have e₉ := h.coc a (b ^ k) (m ^ k) x
  rw [mul_comm (b ^ k), h.s01 (b ^ k)] at e₉
  have f₁ := h.coc x b m a
  have f₂ := h.coc x m b a
  rw [mul_comm m b, h.s01 m b a] at f₂
  rw [h.s12 (x * b), h.s01 (x * b), h.s12 x b a, h.s01 x a b] at f₁
  rw [h.s12 (x * m), h.s01 (x * m), h.s12 x m a, h.s01 x a m] at f₂
  have f₃ : θ b x m = θ m x b := by rw [h.s01 b, h.s12 x, h.s01 x]
  rw [f₃] at e₂
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₀ := E e₀
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have a₈ := E e₈; have a₉ := E e₉; have b₁ := E f₁; have b₂ := E f₂
  have c₁ := E h₁; have c₂ := E h₂; have c₃ := E h₃
  simp only [ofMul_mul, ofMul_inv] at *
  linear_combination (norm := abel) -(a₁ - a₂ + a₃ - a₄ + a₅ - a₆ - a₇ + a₈ - a₉ - b₁ + b₂ + c₁ - c₂ - c₃ + a₀)

theorem exists_const {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {F : Type} [Field F] {K : Type} [Fintype K]
    {φ : K → (Spec (CommRingCat.of F) ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb M φ ε)) (hu : u.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Spec (CommRingCat.of F) ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) :
    ∃ ζ : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ.val) := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => (hF U h).trans (Fintype.prod_empty _).symm) u hu
  have le : (⊤ : (Spec (CommRingCat.of F)).Opens) ≤
      LB.wchart M (PEmpty.elim : PEmpty → (Spec (CommRingCat.of F) ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom (res le (t.s PEmpty.elim)),
    fun Z r z J hJ => ?_⟩
  rw [← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  refine (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    (congrArg (gs r z ⊤) ?_))
  exact ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _).symm

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

def IsRatio (p p' : QkPt D F k) (ζ : F) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) F) (z : T.left) (J), Good D.P.L z J →
    (val (p.g.s p'.y) σ.left z J * cubN (th D z J) k 1 (σ ≫ p'.g.b) (σ ≫ p.g.b)).val =
      gs σ.left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) *
        (val (p'.g.s p.y) σ.left z J * cubN (th D z J) k 1 (σ ≫ p.g.b) (σ ≫ p'.g.b)).val

theorem exists_ratio (p p' : QkPt D F k) : ∃ ζ : Fˣ, IsRatio p p' ζ.val := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub 1 p'.g.b p.g.b k
  obtain ⟨N', hN', vN'⟩ := exists_cubN D.cub 1 p.g.b p'.g.b k
  obtain ⟨ζ, hζ⟩ := exists_const D.P.isLB (F := F)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (p.g.s p'.y) N)
      (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (p'.g.s p.y) N')))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (p.g.isGen _) hN)
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (p'.g.isGen _) hN'))) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 4 ⊕ Fin 8) (K' := Fin 4 ⊕ Fin 8) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 8) (U := U) _ (prod_gt p.g.b p'.y h) rfl)
        (prod_neg _ _ (prod_sum₂ (K := Fin 4) (K' := Fin 8) (U := U) _ (prod_gt p'.g.b p.y h) rfl))).trans ?_
      rw [cPoint_y, cPoint_y]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, mul_comm p.g.b p'.g.b]
      module)
  refine ⟨ζ, fun T σ z J hJ => ?_⟩
  have e := hζ _ σ.left z J hJ
  rw [val_mul hJ, val_inv, val_mul hJ, val_mul hJ, vN T σ z J hJ, vN' T σ z J hJ, MonObj.comp_one] at e
  rw [← e, ← Units.val_mul, inv_mul_cancel_right]

theorem weil_of_ratio (hG : GlobalFnsSt) (p p' : QkPt D F k) {ζ : Fˣ} (H : IsRatio p p' ζ.val) :
    WeilQkIs D F k p p' ζ.val := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄
  rw [phiRel_iff hG _ _ hw'] at r₁ r₄
  rw [phiRel_iff hG _ _ hw] at r₂ r₃
  rw [isSmul_iff]
  refine fam_ext fun β j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  obtain ⟨α, rfl⟩ : ∃ α, α + p'.y + p.y = β := ⟨β - p.y - p'.y, by abel⟩
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have hy : ∀ q : QkPt D F k, cP D (DegPre.BF D F) q.y = (fst (TF (R := R) F) D.P.A ≫ q.g.b) ^ k := fun q => by
    rw [← comp_cP D (fst (TF (R := R) F) D.P.A), cPoint_y]; exact map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _
  have e₂ := r₂ (α + p'.y) _ rfl _ (𝟙 _) y J hJ
  have e₁ := r₁ α _ rfl _ (DegPre.trPt D F p.g.b) y J hJ
  have e₄ := r₄ (α + p.y) _ (add_right_comm α p.y p'.y) _ (𝟙 _) y J hJ
  have e₃ := r₃ α _ rfl _ (DegPre.trPt D F p'.g.b) y J hJ
  rw [Category.id_comp, Category.id_comp, Over.id_left, e₁, tr_fst, uVal_tr, uVal_id, val_mul hJ, val_mul hJ,
    cPoint_add, hy] at e₂
  rw [Category.id_comp, Category.id_comp, Over.id_left, e₃, tr_fst, uVal_tr, uVal_id, val_mul hJ, val_mul hJ,
    cPoint_add, hy, tr_comm] at e₄
  have t₁ := gt_mul (fst (TF (R := R) F) D.P.A) hJ p'.g α p.y
  have t₂ := gt_mul (fst (TF (R := R) F) D.P.A) hJ p.g α p'.y
  rw [hy] at t₁ t₂
  have t₃ := H _ (fst (TF (R := R) F) D.P.A) y J hJ
  obtain ⟨c, hc⟩ : ∃ c : ((DegPre.BF D F).left.presheaf.stalk y)ˣ, c.val =
      gs (fst (TF (R := R) F) D.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ.val) :=
    ⟨_, (gs_unit _ y ⊤ trivial (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ)).symm⟩
  rw [← hc, ← Units.val_mul] at t₃
  have key := cub_comm C k _ _ _ (DegPre.prB D F) _ _ _ _ _ _ _ t₁ t₂ (Units.ext t₃)
  rw [sval_smul _ _ _ _ y hJ, Category.id_comp, ← hc, e₂, e₄, _root_.mul_assoc (sval _ _ _ _), _root_.mul_assoc (sval _ _ _ _),
    ← Units.val_mul, ← Units.val_mul, mul_left_comm c.val, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at key' ⊢
  linear_combination (norm := abel) key'

theorem tr_inv (m : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
  · show (DegPre.trPt D F m⁻¹ ≫ DegPre.trPt D F m) ≫ DegPre.prB D F = 𝟙 _ ≫ DegPre.prB D F
    rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc, ← MonObj.comp_mul,
      inv_mul_cancel, MonObj.comp_one, _root_.mul_one, Category.id_comp]

theorem zero_of_phi {p : QkPt D F k} {w : Frm D F k p.g.b} {s t : Fam D F k} (h : PhiVal p w s.s t.s)
    (ht : ∀ β j, (t.s β).f j = 0) (α : D.X) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e := h α _ rfl _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [tr_inv, UUA.sval_zero_of (ht _) _ y J (hJ.mem _ _)] at e
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  exact (Units.mul_left_eq_zero _).1 e.symm

theorem weil_unique (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) (hk : 1 ≤ k) (p p' : QkPt D F k) {ζ ζ' : F}
    (h : WeilQkIs D F k p p' ζ) (h' : WeilQkIs D F k p p' ζ') : ζ = ζ' := by
  obtain ⟨w, hw⟩ : ∃ w : Frm D F k p.g.b, w.IsGen := H1.ClosedPointWeilPower.gen_local_linComb D.P.L D.P.isLB _ _
  obtain ⟨w', hw'⟩ : ∃ w : Frm D F k p'.g.b, w.IsGen := H1.ClosedPointWeilPower.gen_local_linComb D.P.L D.P.isLB _ _
  obtain ⟨s, hs⟩ := FamFree.exists_fam_support (D := D) (F := F) hG hT hB hk 0
  obtain ⟨s₁, r₁⟩ := exists_phi hG p' w' hw' hB s
  obtain ⟨s₂, r₂⟩ := exists_phi hG p w hw hB s₁
  obtain ⟨s₃, r₃⟩ := exists_phi hG p w hw hB s
  obtain ⟨s₄, r₄⟩ := exists_phi hG p' w' hw' hB s₃
  have a := fun {c : F} (h : WeilQkIs D F k p p' c) => (isSmul_iff _ _ _).1 (h w w' hw hw' s s₁ s₂ s₃ s₄
    ((phiRel_iff hG _ _ hw' _ _).2 r₁) ((phiRel_iff hG _ _ hw _ _).2 r₂) ((phiRel_iff hG _ _ hw _ _).2 r₃)
    ((phiRel_iff hG _ _ hw' _ _).2 r₄))
  have hne : s₄ ≠ 0 := fun h0 => (hs 0).2 ⟨0, by simp⟩
    (zero_of_phi r₃ (zero_of_phi r₄ fun β j => by rw [h0]; rfl) 0)
  exact smul_left_injective F hne ((a h).symm.trans (a h'))

theorem ratio_tor (p p' : QkPt D F k) (t : Multiplicative D.X →* Fˣ) (hy : p.y = 0) (ht : IsTor t p.g) {ζ : F}
    (H : IsRatio p p' ζ) : ζ = (t (Multiplicative.ofAdd p'.y)).val := by
  let z : (TF (R := R) F).left := (⊥ : PrimeSpectrum F)
  choose J hJ using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have e := H _ (𝟙 _) z J hJ
  have e₀ : val (p'.g.s p.y) (𝟙 _) z J = 1 := by
    rw [hy]; exact (val_corr hJ p'.g.s_zero _).trans (val_one _)
  have e₁ : cubN (th D (T := TF (R := R) F) z J) k 1 (𝟙 _ ≫ p'.g.b) (𝟙 _ ≫ p.g.b) = 1 := by
    rw [Category.id_comp p.g.b, ht.1]; exact C.N_one _ _ _
  have e₂ : cubN (th D (T := TF (R := R) F) z J) k 1 (𝟙 _ ≫ p.g.b) (𝟙 _ ≫ p'.g.b) = 1 := by
    rw [Category.id_comp p.g.b, ht.1]; exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  rw [e₁, e₂, Over.id_left, e₀, _root_.mul_one, _root_.mul_one, Units.val_one, _root_.mul_one, ht.2 _ z J hJ, cst,
    gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial] at e
  exact ((((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙 (TF (R := R) F).left :
    (TF (R := R) F).left ⟶ _).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)).injective e).symm

end GlobalTheory.QkPairing

theorem GlobalTheory.weilQk_existsUnique : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, (∃! ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ) ∧ ∀ t, p.y = 0 → IsTor t p.g → WeilQkIs D.toPre F k p p' (t (Multiplicative.ofAdd p'.y)).val := by
  intro hL R _ _ _ I _ D F _ _ _ k hk p p'
  obtain ⟨ζ, hζ⟩ := GlobalTheory.QkPairing.exists_ratio p p'
  have hW := GlobalTheory.QkPairing.weil_of_ratio hL.1.globalFns p p' hζ
  refine ⟨⟨ζ, hW, fun ζ' h => Units.ext (GlobalTheory.QkPairing.weil_unique hL.1.globalFns hL.2.1.secTwist D.tau_bimult hk p p' h hW)⟩,
    fun t hy ht => ?_⟩
  rw [← GlobalTheory.QkPairing.ratio_tor p p' t hy ht hζ]; exact hW
end
end

