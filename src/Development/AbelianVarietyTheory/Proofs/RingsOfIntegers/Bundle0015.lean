import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RatioTrans
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CubBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

section Box

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem bw_trans {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) (ψ : Z ⟶ X') (z : Z)
    {jN jN' : Fin j → M.ι} {k k' : M'.ι} (h₁ : ψ z ∈ LB.wchart M pr jN) (h₁' : ψ z ∈ LB.wchart M pr jN')
    (h₂ : ψ z ∈ M'.U k) (h₂' : ψ z ∈ M'.U k') :
    bw w ψ z jN k = (∏ i, gm (ψ ≫ pr i) z (M.U (jN i) ⊓ M.U (jN' i)) (M.g (jN i) (jN' i))) *
      (gm ψ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * bw w ψ z jN' k' := by
  have hm : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k'))) (hw (jN, k) (jN', k'))
  have d := gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (jN, k) (jN', k') hm
  have l := gm_linComb M pr (fun _ => 1) ψ z jN jN' h₁ h₁'
  simp only [zpow_one] at l
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res ψ z _ hm _))))

variable {K : Type} [Fintype K]

def ratio (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (ρ : Fin j → (Y ⟶ Y₀)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι) : (Z.presheaf.stalk z)ˣ :=
  (∏ a, bw w (r ≫ φ' a) z (jN a) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) *
    (∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)))⁻¹

theorem chart_le {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a) (jN : K → Fin j → M.ι) (i : Fin j) :
    LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ≤ ρ i ⁻¹ᵁ LB.wchart M φ (fun a => jN a i) := fun y hy =>
  Set.mem_iInter.2 fun a => (congrArg (fun g : Y ⟶ X => g y ∈ M.U (jN a i)) (hψ i a)).mp
    (Set.mem_iInter.1 (Set.mem_iInter.1 hy a) i)

theorem ratio_trans (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {jN jN' : K → Fin j → M.ι} {jM jM' : K → M'.ι}
    (h : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)
    (h' : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN' ⊓ LB.wchart M' φ' jM') :
    ratio w ρ t' t r z jN jM = ratio w ρ t' t r z jN' jM' := by
  have e₁ : ∀ a, bw w (r ≫ φ' a) z (jN a) (jM a) = _ := fun a => bw_trans w hw (r ≫ φ' a) z (jN' := jN' a) (k' := jM' a)
    (Set.mem_iInter.1 h.1 a) (Set.mem_iInter.1 h'.1 a) (Set.mem_iInter.1 h.2 a) (Set.mem_iInter.1 h'.2 a)
  have e₂ := gen_trans ht' r z h.2 h'.2
  have e₃ : ∀ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)) = _ := fun i =>
    gen_trans ht (r ≫ ρ i) z (j' := fun a => jN' a i) (chart_le hψ jN i h.1) (chart_le hψ jN' i h'.1)
  have e₄ : ∏ i, trF (L := M) φ ε (r ≫ ρ i) z (fun a => jN a i) (fun a => jN' a i) =
      ∏ a, (∏ i, gm ((r ≫ φ' a) ≫ pr i) z (M.U (jN a i) ⊓ M.U (jN' a i)) (M.g (jN a i) (jN' a i))) ^ ε a := by
    unfold trF
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Category.assoc, Category.assoc, hψ]
  unfold ratio
  rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e₁ a), e₂, Finset.prod_congr rfl fun i _ => e₃ i,
    Finset.prod_mul_distrib, e₄]
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, trF]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε)) (jN : K → Fin j → M.ι) (jM : K → M'.ι) :
    ∃ u : Γ(Y, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
        r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM →
        gm r z _ u = ratio w ρ t' t r z jN jM := by
  refine ⟨@id (Γ(Y, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
      ((LB.linCombIso w φ' ε).s (jN, jM)) * res inf_le_right (t'.s jM) *
      (∏ i, res (inf_le_left.trans (chart_le hψ jN i)) (pullU (ρ i) _ (t.s (fun a => jN a i))))⁻¹,
    fun Z r z hz => ?_⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linCombIso w φ' ε r z jN jM hz) (gm_res r z _ hz _))) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))))
  exact (gm_res r z _ hz _).trans (gm_pull r (ρ i) z _ (chart_le hψ jN i hz.1) _)

theorem box_unique {S₀ : Scheme.{0}} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h : ∀ y J J', Good M y J → Good M' y J' →
      (∏ a, bw w (e ≫ φ' a) y (fun i => J ((e ≫ φ' a) ≫ pr i)) (J' (e ≫ φ' a)) ^ ε a) * val t' e y J' =
        ∏ i, val t (e ≫ ρ i) y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J') (hJ : Good M z J) (hJ' : Good M' z J') :
    (∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' =
      ∏ i, val t (r ≫ ρ i) z J := by
  choose u hu using fun q : (K → Fin j → M.ι) × (K → M'.ι) => exists_ratio w hψ t' t q.1 q.2
  obtain ⟨s, hs⟩ := glue_unit (⊤ : Y.Opens)
    (fun q : (K → Fin j → M.ι) × (K → M'.ι) =>
      LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' q.1 ⊓ LB.wchart M' φ' q.2) (fun _ => le_top)
    (fun y _ => by
      choose a ha using fun k i => exists_chart hM (pr i (φ' k y))
      choose b hb using fun k => exists_chart hM' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(a, b), Set.mem_iInter.2 fun k => Set.mem_iInter.2 (ha k), Set.mem_iInter.2 hb⟩) u
    (fun q q' y hy => (hu q _ (𝟙 Y) y hy.1).trans ((ratio_trans w hw hψ ht' ht (𝟙 Y) y hy.1 hy.2).trans
      (hu q' _ (𝟙 Y) y hy.2).symm))
  obtain ⟨a, ha⟩ := hp s.val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' →
      ((∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' *
        (∏ i, val t (r ≫ ρ i) z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J J' hJ hJ'
    have hm : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) :=
      ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i), hJ'.mem _ r⟩
    have v : ∏ i, val t (r ≫ ρ i) z J = ∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => J ((r ≫ φ' a) ≫ pr i)))
        (t.s (fun a => J ((r ≫ φ' a) ≫ pr i))) := Finset.prod_congr rfl fun i _ =>
      val_of t _ z J _ (fun a => by rw [Category.assoc, Category.assoc, hψ])
    rw [v]
    have w₁ := (hu (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)) Z r z hm).symm.trans
      ((congrArg (gm r z _) (hs _).symm).trans (gm_res r z le_top hm s))
    exact (congrArg Units.val w₁).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    have := key _ e y I I' hI hI'
    rw [h y I I' hI hI', mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J J' hJ hJ'
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

end Box

theorem cubV_box : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J J'), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D'.P.L z J' → ∀ x x' y : T ⟶ D'.P.A, (let om := fun p : T ⟶ D'.P.A => bw pD.w p.left z (fun i => J (p.left ≫ (pD.pw.pr i).left)) (J' p.left); Geo.Tor.cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ i, Geo.Tor.cubV D.cub z J (x ≫ pD.pw.pr i) (x' ≫ pD.pw.pr i) (y ≫ pD.pw.pr i)) := by
  intro hG R _ _ j D D' pD T z J J' hJ hJ' x x' y om
  let ρ : Fin j → ((G3 D'.P.A).left ⟶ (G3 D.P.A).left) := fun i => (pD.pw.pr i ⊗ₘ pD.pw.pr i ⊗ₘ pD.pw.pr i).left
  have hψ : ∀ i a, thφ D'.P.A (x3 D'.P.A) a ≫ (pD.pw.pr i).left = ρ i ≫ thφ D.P.A (x3 D.P.A) a := fun i a =>
    letI := pD.pw.hom i
    (CubeMap.ofHom (pD.pw.pr i)).psum_comm a.down
  have hρ : ∀ {T : Over (Spec (CommRingCat.of R))} (a b c : T ⟶ D'.P.A) i, (lift a (lift b c)).left ≫ ρ i =
      (lift (a ≫ pD.pw.pr i) (lift (b ≫ pD.pw.pr i) (c ≫ pD.pw.pr i))).left := fun a b c i => by
    show (lift a (lift b c) ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i ⊗ₘ pD.pw.pr i)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := fun i => (pD.pw.pr i).left) D.P.isLB D'.P.isLB pD.w pD.w_gen (ε := thε) hψ
    D'.cub.isGen D.cub.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV D'.cub s I') := isCub_cubV D'.cub hI'
      have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I) := isCub_cubV D.cub hI
      have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) 1 1
        (fun q => bw pD.w q s (fun i => I (q ≫ (pD.pw.pr i).left)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun i _ => ?_).symm)
      have := pD.pw.hom i
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ pD.pw.pr i = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ i = _ from hρ 1 1 1 i, o]
      exact C.face 1 1) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bw pD.w q z (fun i => J (q ≫ (pD.pw.pr i).left)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun i _ => ?_)))
  rw [hρ]; rfl

end GlobalTheory.CubBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalOfPointwise
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxFamScalar

section Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Y' W W' Z : Scheme.{0}}

theorem sval_of_secScal {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  unfold GeneratorPullback.SecScal resTop at H
  have hV : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have hW : h (r z) ∈ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hV.2 k
  have hc : LB.Coh L (Sum.elim φ₁ fun k => h ≫ φ₂ k)
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> simp only [Sum.elim_inl, Sum.elim_inr] at e ⊢ <;> rw [e]
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc]),
    sval_of s₁ r z J (fun k => J (r ≫ φ₁ k)) (fun k => rfl)]
  calc _ = _ := (gs_pull r h z _ hW _).symm
    _ = _ := (gs_res r z _ hV _).symm
    _ = _ := congrArg (gs r z _) (H _ _ hc)
    _ = _ := gs_mul r z _ hV _ _
    _ = _ := congrArg₂ (· * ·) (gs_res r z _ hV _) (gs_res r z _ hV _)

theorem secScal_of_pointwise {L : LB X} (hL : L.IsLB) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J →
      sval s₂ (𝟙 Y' ≫ h) y J = gs (𝟙 Y') y ⊤ c * sval s₁ (𝟙 Y') y J) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c := by
  unfold GeneratorPullback.SecScal resTop
  intro j₁ j₂ hc
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL y (Sum.elim φ₁ fun k => h ≫ φ₂ k) (Sum.elim j₁ j₂) hc (by
    rintro (k | k)
    · exact Set.mem_iInter.1 hy.1 k
    · exact Set.mem_iInter.1 hy.2 k)
  have hW : h y ∈ LB.wchart L φ₂ j₂ := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
  have e := H y J hJ
  rw [sval_of s₂ (𝟙 Y' ≫ h) y J j₂ (fun k => by simpa using hJj (Sum.inr k)),
    sval_of s₁ (𝟙 Y') y J j₁ (fun k => by simpa using hJj (Sum.inl k))] at e
  calc _ = _ := gs_res _ y _ hy _
    _ = _ := gs_pull _ h y _ hW _
    _ = _ := e
    _ = _ := (congrArg₂ (· * ·) (gs_res _ y _ hy _) (gs_res _ y _ hy _)).symm
    _ = _ := (gs_mul _ y _ hy _ _).symm

variable {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem box_sval (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y' ⟶ Y)}
    (hφ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (s' : LB.Sec (LB.LinComb M' φ' ε))
    (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (hle : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι) i,
      LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM ≤
        ρ i ⁻¹ᵁ LB.wchart M (φ i) (fun a => jN a i))
    (H : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      (@id (Γ(Y', LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
        ((LB.linCombIso w φ' ε).s (jN, jM))).val * rs inf_le_right (s'.f jM) =
        ∏ i, rs (hle jN jM i) (((ρ i).app _).hom ((s i).f (fun a => jN a i))))
    (q : Z ⟶ Y') (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * sval s' q y J' =
      ∏ i, sval (s i) (q ≫ ρ i) y J := by
  have hq : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Good.mem (L := LB.LinComb M pr (fun _ => 1)) (J := fun ψ i => J (ψ ≫ pr i)) (fun ψ => hJ.mem pr ψ) φ' q,
      hJ'.mem φ' q⟩
  have key := congrArg (gs q y _) (H (fun a i => J ((q ≫ φ' a) ≫ pr i)) (fun a => J' (q ≫ φ' a)))
  calc _ = _ := congrArg (fun u => (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * u)
          ((sval_of s' q y J' _ (fun a => rfl)).trans (gs_res q y _ hq _).symm)
    _ = _ := congrArg (· * _) (congrArg Units.val (gm_linCombIso w φ' ε q y _ _ hq).symm)
    _ = _ := congrArg (· * _) (gs_unit q y _ hq _).symm
    _ = _ := (gs_mul q y _ hq _ _).symm
    _ = _ := key
    _ = _ := gs_prod q y _ hq Finset.univ _
    _ = _ := Finset.prod_congr rfl fun i _ =>
          ((gs_res q y _ hq _).trans (gs_pull q (ρ i) y _ (hle _ _ i hq) _)).trans
            (sval_of (s i) (q ≫ ρ i) y J _ (fun a => by simp only [Category.assoc, hφ])).symm

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  unfold scal
  have e := gs_pull (𝟙 Z) r z ⊤ trivial ((Scheme.Hom.appTop p).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))
  rw [Category.id_comp] at e
  rw [← e, Scheme.Hom.comp_appTop]
  rfl

theorem gs_scal_prod {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (p' : Y' ⟶ Spec (CommRingCat.of R))
    (ρ : Fin j → (Y' ⟶ Y)) (hρ : ∀ i, ρ i ≫ p = p') (y : Y') (r : Fin j → R) :
    ∏ i, gs (𝟙 _ ≫ ρ i) y ⊤ (scal p (r i)) = gs (𝟙 _) y ⊤ (scal p' (∏ i, r i)) := by
  have hsc : (∏ i, scal p' (r i)) = scal p' (∏ i, r i) := by
    simp only [scal, map_prod]
  rw [← hsc, gs_prod (𝟙 _) y ⊤ trivial Finset.univ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gs_scal, Category.id_comp, hρ]

theorem secScal_box (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    {K : Type} [Fintype K] {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X')} {φ : Fin j → K → (Y ⟶ X)} {ρ : Fin j → (Y' ⟶ Y)}
    {ψ' : K → (W' ⟶ X')} {ψ : Fin j → K → (W ⟶ X)} {σ : Fin j → (W' ⟶ W)}
    {h' : Y' ⟶ W'} {h : Y ⟶ W} (e' : ∀ a, φ' a = h' ≫ ψ' a) (e : ∀ i, h' ≫ σ i = ρ i ≫ h)
    (s' : LB.Sec (LB.LinComb M' φ' ε)) (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (t' : LB.Sec (LB.LinComb M' ψ' ε)) (t : ∀ i, LB.Sec (LB.LinComb M (ψ i) ε))
    (Hs : ∀ (y : Y') J J', Good M y J → Good M' y J' →
      (∏ a, bw w (𝟙 Y' ≫ φ' a) y (fun i => J ((𝟙 Y' ≫ φ' a) ≫ pr i)) (J' (𝟙 Y' ≫ φ' a)) ^ ε a).val *
        sval s' (𝟙 Y') y J' = ∏ i, sval (s i) (𝟙 Y' ≫ ρ i) y J)
    (Ht : ∀ (y : Y') J J', Good M y J → Good M' y J' →
      (∏ a, bw w (h' ≫ ψ' a) y (fun i => J ((h' ≫ ψ' a) ≫ pr i)) (J' (h' ≫ ψ' a)) ^ ε a).val *
        sval t' h' y J' = ∏ i, sval (t i) (h' ≫ σ i) y J)
    (c : Fin j → Γ(Y, ⊤)) (c' : Γ(Y', ⊤))
    (hc : ∀ y : Y', ∏ i, gs (𝟙 _ ≫ ρ i) y ⊤ (c i) = gs (𝟙 _) y ⊤ c')
    (H : ∀ i, GeneratorPullback.SecScal M (φ i) ε (s i) (ψ i) ε (t i) h (c i)) :
    GeneratorPullback.SecScal M' φ' ε s' ψ' ε t' h' c' := by
  apply secScal_of_pointwise hM'
  intro y J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good M hM y (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
  have hs := Hs y J J' hJ hJ'
  have ht := Ht y J J' hJ hJ'
  have hci := hc y
  have hH : ∀ i, sval (t i) (h' ≫ σ i) y J = gs (𝟙 Y' ≫ ρ i) y ⊤ (c i) * sval (s i) (𝟙 Y' ≫ ρ i) y J :=
    fun i => by rw [← sval_of_secScal (H i) (𝟙 Y' ≫ ρ i) y hJ, Category.id_comp, ← e i]
  simp only [Category.id_comp] at hs hH hci ⊢
  simp only [← e'] at ht
  refine (Units.isUnit (∏ a, bw w (φ' a) y (fun i => J (φ' a ≫ pr i)) (J' (φ' a)) ^ ε a)).mul_left_cancel ?_
  rw [ht, Finset.prod_congr rfl (fun i _ => hH i), Finset.prod_mul_distrib, hci, ← hs, mul_left_comm]

end Generic

set_option maxHeartbeats 800000 in

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (pD : IsPowDeg D'.toPre D.toPre j) (k : ℕ) (Fs : Fin j → Fam D.toPre (FractionRing R) k) (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α) (r : Fin j → R), (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((Fs i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom (r i))) → ∀ (F' : Fam D'.toPre (FractionRing R) k), IsBoxFam pD (FractionRing R) k F' Fs → ∀ α' : D'.toPre.X, GeneratorPullback.SecScal D'.toPre.P.L (DegPre.famφ D'.toPre (FractionRing R) α') (DegPre.famε k) (F'.s α') (D'.toPre.famφB α') (DegPre.famε k) (boxFamB pD k f α') (DegPre.prB D'.toPre (FractionRing R)).left (scal (DegPre.BF D'.toPre (FractionRing R)).hom (∏ i, r i)) := by
  intro R _ _ I j D D' pD k Fs f r hF F' hB α'
  have e1 : ∀ i, (D'.toPre.prB (FractionRing R)).left ≫ (pD.pw.pr i).left =
      prB pD (FractionRing R) i ≫ (D.toPre.prB (FractionRing R)).left := by
    intro i
    unfold prB DegPre.prB
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have e2 : ∀ i, prB pD (FractionRing R) i ≫ (D.toPre.BF (FractionRing R)).hom =
      (D'.toPre.BF (FractionRing R)).hom := fun i => Over.w (TF (FractionRing R) ◁ pD.pw.pr i)
  obtain ⟨hφ, hBα⟩ := hB α'
  obtain ⟨hφB, hBB⟩ := isBoxFamB_boxFamB pD k f α'
  exact secScal_box D.toPre.P.isLB D'.toPre.P.isLB pD.w
    (ρ := fun i => prB pD (FractionRing R) i) (σ := fun i => (pD.pw.pr i).left)
    (h' := (D'.toPre.prB (FractionRing R)).left) (h := (D.toPre.prB (FractionRing R)).left)
    (fun a => GC.famφ_eq D'.toPre (FractionRing R) α' a) e1
    (F'.s α') (fun i => (Fs i).s (pD.xe α' i)) (boxFamB pD k f α') (fun i => f i (pD.xe α' i))
    (fun y J J' hJ hJ' => box_sval pD.w hφ (F'.s α') _
      (fun jN _ i => inf_le_left.trans (box_le_of_comp _ _ _ _ _ i (hφ i) jN)) hBα (𝟙 _) y hJ hJ')
    (fun y J J' hJ hJ' => box_sval pD.w hφB (boxFamB pD k f α') _
      (fun jN _ i => inf_le_left.trans (box_le_of_comp _ _ _ _ _ i (hφB i) jN)) hBB _ y hJ hJ')
    (fun i => scal (D.toPre.BF (FractionRing R)).hom (r i)) _
    (fun y => gs_scal_prod _ _ _ e2 y r)
    (fun i => hF i (pD.xe α' i))

end GlobalTheory.BoxFamScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj
section
namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem smoothOfRelativeDimension_powObj {S : Scheme.{0}} (G : Over S) (g : ℕ)
    (hG : SmoothOfRelativeDimension g G.hom) : ∀ n : ℕ, SmoothOfRelativeDimension (n * g) (powObj G n).hom
  | 0 => by
    have h : SmoothOfRelativeDimension 0 (𝟙 S) := inferInstance
    rw [Nat.zero_mul]
    exact h
  | n + 1 => by
    have ih := smoothOfRelativeDimension_powObj G g hG n
    have h1 : SmoothOfRelativeDimension (n * g) (pullback.fst G.hom (powObj G n).hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _).flip ih
    have h2 : SmoothOfRelativeDimension (n * g + g) (pullback.fst G.hom (powObj G n).hom ≫ G.hom) :=
      inferInstance
    rw [Nat.succ_mul]
    exact h2

theorem polAV_g_of_isPowPolAV : ∀ (K : Type) [Field K] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of K))),
    IsPowPolAV A' A j → A'.g = j * A.g := by
  intro K _ j A A' p
  let e : A'.A ≅ powObj A.A j := p.lim.conePointUniqueUpToIso (powIsLimit A.A j)
  have hw : A'.A.hom = e.hom.left ≫ (powObj A.A j).hom := (Over.w e.hom).symm
  have h1 := smoothOfRelativeDimension_powObj A.A A.g A.smoothDim j
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h2 : SmoothOfRelativeDimension (0 + j * A.g) A'.A.hom := by
    rw [hw]; infer_instance
  have := H1.dim_unique _ A'.smoothDim h2 (eSec A'.A (default : PrimeSpectrum K))
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PsiZero

theorem cPoint_zero' {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) :
    cP D T 0 = 1 := by
  have := cPoint_add D T 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem val_psi_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {z : (TK R).left}
    {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val (D.psi 0) (𝟙 _) z J = (val D.rig (jK R) z J)⁻¹ := by
  have C : IsCub (th D (T := TK R) z J) := isCub_cubV D.cub hJ
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (jK R) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
    rfl
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 0 0 0)) (𝟙 _) z J = 1 := by
    refine (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ 0) (cP D _ 0) (cP D _ 0)).trans ?_
    rw [Category.id_comp, cPoint_zero']
    exact C.face _ _
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB 0 0 0) (𝟙 _)).trans (val_mul hJ _ _ _))
  have hp : ∀ a : D.X, a = 0 → val (D.psi a) (𝟙 _) z J = val (D.psi 0) (𝟙 _) z J := by
    rintro a rfl; rfl
  rw [vc, vτ, vτ, vρ, hp (0 + 0 + 0) (by simp), hp (0 + 0) (by simp), _root_.mul_one, mul_inv_cancel,
    _root_.one_mul] at e
  have e' := mul_eq_left.1 e.symm
  rw [← mul_inv, inv_eq_one] at e'
  exact eq_inv_of_mul_eq_one_left e'

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), (D.TauBimult → D.PsiIn 0 ⊤) ∧ ∀ (χ : D.X) (J J' : Ideal R), J ≤ J' → D.PsiIn χ J → D.PsiIn χ J' := by
  intro R _ _ D
  refine ⟨fun hB j V hV hle h => ?_, fun χ J J' hJ H j V hV hle h => ?_⟩
  · have c0 : (D.c 0).left = eSec D.P.A := by
      have := cPoint_zero' D (𝟙_ _)
      rw [cP, toUnit_unit, Category.id_comp, Hom.one_def, toUnit_unit, Category.id_comp] at this
      rw [this]; rfl
    have hx : D.xK 0 = jK R ≫ eSec D.P.A := by rw [← c0]; rfl
    have hle' : V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => eSec D.P.A) j := fun y hy =>
      Set.mem_iInter.2 fun _ => by rw [← c0]; exact hle hy
    refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.rig.s j)⁻¹.val,
      by rw [Ideal.map_top]; trivial, fn_ext fun y hy => ?_⟩
    have hy' : jK R y ∈ V := hy
    obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (K := PUnit) (fun _ => D.xK 0) j (fun _ _ _ => rfl)
      (fun k => Set.mem_iInter.1 (h hy) k)
    have e := val_psi_zero hB hJ
    rw [val_of (D.psi 0) _ y J j (fun k => (congrArg J (Category.id_comp (D.xK 0))).trans (eJ k)),
      val_of D.rig _ y J j (fun k => (congrArg J hx.symm).trans (eJ k))] at e
    refine (gs_pull (𝟙 _) (jK R) y V hy' _).trans (Eq.trans ?_
      ((gs_res (𝟙 _) y h hy _).trans (gs_unit _ _ _ (h hy) _)).symm)
    rw [Category.id_comp]
    refine (gs_res (jK R) y hle' hy' _).trans ((gs_unit _ _ _ (hle' hy') _).trans ?_)
    exact congrArg Units.val ((map_inv _ _).trans e.symm)
  · obtain ⟨r, hr, e⟩ := H j V hV hle h
    exact ⟨r, Ideal.map_mono hJ hr, e⟩

end GlobalTheory.PsiZero
end
end

