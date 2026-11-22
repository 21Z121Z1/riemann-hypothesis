import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxIso
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowerThickIso

section General

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull gm_div gm_linComb gm_pull_g gm_self mem_pull PGen isGen_iff glue_unit
  exists_chart)

variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'}
  {h : Fin j → (Ge' ⟶ Ge)}

theorem gm_box_g {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z) (a b : Fin j → M.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i))
    (hb : ∀ i, pr i (ψ z) ∈ M.U (b i)) :
    gm ψ z (LB.wchart M pr a ⊓ LB.wchart M pr b) ((LB.LinComb M pr (fun _ => 1)).g a b) =
      ∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i)) :=
  (gm_linComb M pr (fun _ => 1) ψ z a b (Set.mem_iInter.2 ha) (Set.mem_iInter.2 hb)).trans
    (Finset.prod_congr rfl fun _ _ => zpow_one _)

theorem bw_change {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen) {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z)
    (a b : Fin j → M.ι) (k k' : M'.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i)) (hb : ∀ i, pr i (ψ z) ∈ M.U (b i))
    (hk : ψ z ∈ M'.U k) (hk' : ψ z ∈ M'.U k') :
    bw w ψ z a k = (∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i))) *
      (gm ψ z _ (M'.g k k'))⁻¹ * bw w ψ z b k' := by
  have hm : ψ z ∈ LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k') :=
    ⟨⟨Set.mem_iInter.2 ha, hk⟩, Set.mem_iInter.2 hb, hk'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k'))) (hw (a, k) (b, k'))
  have e' := (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (a, k) (b, k') hm) (gm_res ψ z _ hm _))))
  rw [← gm_box_g ψ z a b ha hb]
  exact e'

def germ (pG' : Ge' ⟶ B') (h : Fin j → (Ge' ⟶ Ge)) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι)
    (jL : Fin j → L.ι) : (Z.presheaf.stalk z)ˣ :=
  (bw w (r ≫ pG') z jM jM')⁻¹ * ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i)

theorem germ_change (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : Fin j → M.ι) (jM' kM' : M'.ι) (jL kL : Fin j → L.ι)
    (a₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (jL i))
    (b₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (kM i)) (b₂ : pG' (r z) ∈ M'.U kM') (b₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (kL i)) :
    germ pG' h w we r z jM jM' jL =
      gm (r ≫ pG') z _ (M'.g jM' kM') *
        (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        germ pG' h w we r z kM kM' kL := by
  have p₁ : ∀ i, pG (h i (r z)) = pr i (pG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₁ i).symm
  have p₂ : ∀ i, fG (h i (r z)) = prG i (fG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₂ i)
  have a := bw_change hw (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have c : ∀ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) =
      gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i)) *
        (gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i) := fun i => by
    have c₃ : fG (h i (r z)) ∈ L.U (jL i) := p₂ i ▸ a₃ i
    have d₃ : fG (h i (r z)) ∈ L.U (kL i) := p₂ i ▸ b₃ i
    have c₁ : pG (h i (r z)) ∈ M.U (jM i) := p₁ i ▸ a₁ i
    have d₁ : pG (h i (r z)) ∈ M.U (kM i) := p₁ i ▸ b₁ i
    have c := hwe Z (r ≫ h i) z (jM i) (kM i) (fun _ => jL i) (fun _ => kL i) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
    rw [gm_pull_g L fG (r ≫ h i) z (fun _ => jL i) (fun _ => kL i) (mem_pull.2 c₃) (mem_pull.2 d₃),
      Category.assoc, Category.assoc, ← e₁, e₂] at c
    rw [Category.assoc, Category.assoc]
    exact c
  unfold germ
  rw [a, Finset.prod_congr rfl fun i _ => c i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  generalize (∏ i, gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i))) = A
  generalize (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i))) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize bw w (r ≫ pG') z kM kM' = P
  generalize (∏ i, Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i)) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    (jM' : M'.ι) (jL : Fin j → L.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι), (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) →
        pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        gm r z _ s = germ pG' h w we r z jM jM' jL := by
  have p₁ : ∀ i x, pG (h i x) = pr i (pG' x) := fun i x => congrArg (fun g => g x) (e₁ i).symm
  have p₂ : ∀ i x, fG (h i x) = prG i (fG' x) := fun i x => congrArg (fun g => g x) (e₂ i)
  obtain ⟨W, hW⟩ : ∃ W : (Fin j → M.ι) → Ge'.Opens, ∀ a x, x ∈ W a ↔
      (∀ i, pr i (pG' x) ∈ M.U (a i)) ∧ pG' x ∈ M'.U jM' ∧ ∀ i, prG i (fG' x) ∈ L.U (jL i) :=
    ⟨fun a => pG' ⁻¹ᵁ LB.wchart M pr a ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ fG' ⁻¹ᵁ LB.wchart L prG jL),
      fun _ _ => and_congr Set.mem_iInter (and_congr Iff.rfl Set.mem_iInter)⟩
  have l₀ : ∀ a, W a ≤ (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL) :=
    fun a x hx => ⟨mem_pull.2 ((hW a x).1 hx).2.1, mem_pull.2 (Set.mem_iInter.2 ((hW a x).1 hx).2.2)⟩
  have l₁ : ∀ a, W a ≤ pG' ⁻¹ᵁ (LB.wchart M pr a ⊓ M'.U jM') := fun a x hx =>
    ⟨Set.mem_iInter.2 ((hW a x).1 hx).1, ((hW a x).1 hx).2.1⟩
  have l₂ : ∀ a i, W a ≤ h i ⁻¹ᵁ ((M.pull pG).U (fun _ => a i) ⊓ (L.pull fG).U (fun _ => jL i)) := fun a i x hx =>
    ⟨mem_pull.2 ((p₁ i x).symm ▸ ((hW a x).1 hx).1 i), mem_pull.2 ((p₂ i x).symm ▸ ((hW a x).1 hx).2.2 i)⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ a, Γ(Ge', W a)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (a : Fin j → M.ι), r z ∈ W a →
      gm r z (W a) (u a) = germ pG' h w we r z a jM' jL :=
    ⟨fun a => (res (l₁ a) (pullU pG' _ (w.s (a, jM'))))⁻¹ *
        ∏ i, res (l₂ a i) (pullU (h i) _ (we.s (fun _ => a i, fun _ => jL i))),
      fun Z r z a hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ a) hz _).trans (gm_pull r pG' z _ (l₁ a hz) _)))) ((map_prod _ _ _).trans
          (Finset.prod_congr rfl fun i _ =>
            (gm_res r z (l₂ a i) hz _).trans (gm_pull r (h i) z _ (l₂ a i hz) _))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      choose a ha using fun i => exists_chart hM (pr i (pG' x))
      exact TopologicalSpace.Opens.mem_iSup.2
        ⟨a, (hW a x).2 ⟨ha, mem_pull.1 hx.1, Set.mem_iInter.1 (mem_pull.1 hx.2)⟩⟩) u
    (fun a a' x hx => by
      have h₁ := (hW a x).1 hx.1
      have h₂ := (hW a' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwe (𝟙 Ge') x a a' jM' jM' jL jL h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, Finset.prod_eq_one fun i _ =>
        gm_self hL ((𝟙 Ge' ≫ fG') ≫ prG i) x (h₁.2.2 i), inv_one, _root_.one_mul, _root_.one_mul] at k
      exact (hu _ (𝟙 Ge') x a hx.1).trans (k.trans (hu _ (𝟙 Ge') x a' hx.2).symm))
  refine ⟨s, fun Z r z jM a₁ a₂ a₃ => ?_⟩
  have hz := (hW jM (r z)).2 ⟨a₁, a₂, a₃⟩
  exact (gm_res r z (l₀ jM) hz s).symm.trans ((congrArg (gm r z (W jM)) (hs jM)).trans (hu Z r z jM hz))

theorem exists_box_iso (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen)
    (hwe : we.IsGen) :
    ∃ we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι) (jL : Fin j → L.ι),
        (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) → pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        bw w (r ≫ pG') z jM jM' * Geo.Tor.gw we' r z jM' (fun _ => jL) =
          ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) := by
  rw [isGen_iff] at hwe
  choose s hs using exists_unit hM hM' hL e₁ e₂ hw hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL a₁ a₂ a₃ => ?_⟩
  · intro Z r z l l' k k' a₂ b₂ a₄ b₄
    choose a ha using fun i => exists_chart hM (pr i (pG' (r z)))
    have a₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 a₄)
    have b₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k' PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 b₄)
    have c := germ_change e₁ e₂ hw hwe r z a a l l' _ _ ha a₂ a₄' ha b₂ b₄'
    rw [← hs l _ Z r z a ha a₂ a₄', ← hs l' _ Z r z a ha b₂ b₄', ← gm_box_g (r ≫ fG') z _ _ a₄' b₄'] at c
    rw [gm_pull_g (LB.LinComb L prG (fun _ => 1)) fG' r z k k' a₄ b₄]
    exact c
  · exact (congrArg (bw w (r ≫ pG') z jM jM' * ·) (hs jM' jL Z r z jM a₁ a₂ a₃)).trans
      (mul_inv_cancel_left _ _)

end General

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (e : ℕ) (g : GtCoord I D.toPre e G) (g' : GtCoord I D'.toPre e G'), (∀ i, g'.pG.left ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ g.pG.left) → ∀ (L : LB G.left), L.IsLB → ∀ w : LB.Iso (L.pull (fstG I e G).left) (D.toPre.P.L.pull g.pG.left), w.IsGen → ∃ w' : LB.Iso ((boxLB L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : Fin j → L.ι), (∀ i, (pD.pw.pr i).left (g'.pG.left (r z)) ∈ D.toPre.P.L.U (jM i)) → g'.pG.left (r z) ∈ D'.toPre.P.L.U jM' → (∀ i, (pG.pr i).left ((fstG I e G').left (r z)) ∈ L.U (jL i)) → bw pD.w (r ≫ g'.pG.left) z jM jM' * Geo.Tor.gw w' r z jM' (fun _ => jL) = ∏ i, Geo.Tor.gw w (r ≫ ((Over.pullback (thick R I e)).map (pG.pr i)).left) z (jM i) (fun _ => jL i) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG e g g' hq L hL w hw
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  exact exists_box_iso (Ge := (thickObj R I e G).left) (Ge' := (thickObj R I e G').left) (h := rhoE I pG e)
    (pG := g.pG.left) (pG' := g'.pG.left) (fG := fGl I G e) (fG' := fGl I G' e)
    D.toPre.P.isLB D'.toPre.P.isLB hL hq hρ pD.w w pD.w_gen hw

end GlobalTheory.PowerThickIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace SplitTorusPow

variable {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']

noncomputable def torusMap (S : Scheme.{0}) (φ : X →+ X') : splitTorus S X' ⟶ splitTorus S X :=
  (splitTorusPointsEquiv S X (splitTorus S X')).symm
    ((splitTorusPointsEquiv S X' (splitTorus S X') (𝟙 _)).comp (AddMonoidHom.toMultiplicative φ))

theorem torusMap_char (φ : X →+ X') (χ : X) :
    (torusMap S φ).left.appTop.hom (charUnit S X χ).val = (charUnit S X' (φ χ)).val := by
  rw [← splitTorusPointsEquiv_val, torusMap, MulEquiv.apply_symm_apply]
  change (splitTorusPointsEquiv S X' (splitTorus S X') (𝟙 _) (Multiplicative.ofAdd (φ χ))).val = _
  rw [splitTorusPointsEquiv_val]
  simp

theorem points_comp_torusMap (φ : X →+ X') {Z : Over S} (t : Z ⟶ splitTorus S X') :
    splitTorusPointsEquiv S X Z (t ≫ torusMap S φ) =
      (splitTorusPointsEquiv S X' Z t).comp (AddMonoidHom.toMultiplicative φ) := by
  refine MonoidHom.ext fun χ => Units.ext ?_
  change (splitTorusPointsEquiv S X Z (t ≫ torusMap S φ) (Multiplicative.ofAdd χ.toAdd)).val =
    (splitTorusPointsEquiv S X' Z t (Multiplicative.ofAdd (φ χ.toAdd))).val
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, ← torusMap_char, Over.comp_left,
    Scheme.Hom.comp_appTop]
  rfl

theorem mul_comp_torusMap (φ : X →+ X') {Z : Over S} (a b : Z ⟶ splitTorus S X') :
    (a * b) ≫ torusMap S φ = (a ≫ torusMap S φ) * (b ≫ torusMap S φ) := by
  apply (splitTorusPointsEquiv S X Z).injective
  rw [map_mul, points_comp_torusMap, points_comp_torusMap, points_comp_torusMap, map_mul,
    MonoidHom.mul_comp]

theorem isMonHom_torusMap (φ : X →+ X') : IsMonHom (torusMap S φ) where
  one_hom := by
    have h : (1 : 𝟙_ (Over S) ⟶ splitTorus S X') ≫ torusMap S φ = 1 := by
      apply (splitTorusPointsEquiv S X _).injective
      rw [points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
    simpa [Hom.one_def] using h
  mul_hom := by
    have h := mul_comp_torusMap (S := S) φ (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]
    congr 1

def incl {j : ℕ} (xe : X' ≃+ (Fin j → X)) (i : Fin j) : X →+ X' :=
  xe.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ => X) i)

theorem incl_apply {j : ℕ} (xe : X' ≃+ (Fin j → X)) (i : Fin j) (χ : X) :
    incl xe i χ = xe.symm (Pi.single i χ) := rfl

theorem sum_incl {j : ℕ} (xe : X' ≃+ (Fin j → X)) (x : X') : ∑ i, incl xe i (xe x i) = x := by
  simp only [incl_apply]
  rw [← map_sum, Finset.univ_sum_single, AddEquiv.symm_apply_apply]

theorem hom_ext_incl {M : Type} [CommGroup M] {j : ℕ} (xe : X' ≃+ (Fin j → X))
    {u v : Multiplicative X' →* M}
    (h : ∀ i, u.comp (AddMonoidHom.toMultiplicative (incl xe i)) =
      v.comp (AddMonoidHom.toMultiplicative (incl xe i))) : u = v := by
  refine MonoidHom.ext fun x => ?_
  have e : x = ∏ i, Multiplicative.ofAdd (incl xe i (xe x.toAdd i)) := by
    rw [← ofAdd_sum, sum_incl]; rfl
  rw [e, map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ =>
    DFunLike.congr_fun (h i) (Multiplicative.ofAdd (xe x.toAdd i))

theorem exists_hom_incl {M : Type} [CommGroup M] {j : ℕ} (xe : X' ≃+ (Fin j → X))
    (w : Fin j → (Multiplicative X →* M)) :
    ∃ u : Multiplicative X' →* M,
      ∀ i, u.comp (AddMonoidHom.toMultiplicative (incl xe i)) = w i := by
  refine ⟨∏ i, (w i).comp (AddMonoidHom.toMultiplicative
    ((Pi.evalAddMonoidHom (fun _ => X) i).comp xe.toAddMonoidHom)), fun i => ?_⟩
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.comp_apply, MonoidHom.finset_prod_apply, Finset.prod_eq_single i]
  · simp [incl_apply]
  · intro k _ hk
    simp [incl_apply, Pi.single_eq_of_ne hk]
  · simp

noncomputable def isPowGrp (S : Scheme.{0}) {j : ℕ} (xe : X' ≃+ (Fin j → X)) :
    IsPowGrp (splitTorus S X') (splitTorus S X) j where
  pr i := torusMap S (incl xe i)
  hom i := isMonHom_torusMap _
  lim := mkFanLimit _
    (fun s => (splitTorusPointsEquiv S X' s.pt).symm
      (exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose)
    (fun s i => by
      apply (splitTorusPointsEquiv S X s.pt).injective
      refine (points_comp_torusMap (incl xe i) _).trans ?_
      rw [MulEquiv.apply_symm_apply]
      exact (exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose_spec i)
    (fun s m hm => by
      apply (splitTorusPointsEquiv S X' s.pt).injective
      rw [MulEquiv.apply_symm_apply]
      refine hom_ext_incl xe fun i => ?_
      rw [(exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose_spec i,
        ← hm i]
      exact (points_comp_torusMap (incl xe i) m).symm)

end SplitTorusPow

theorem exists_isPowGrp_splitTorus : ∀ (S : Scheme.{0}) (X X' : Type) [AddCommGroup X] [AddCommGroup X'] (j : ℕ) (xe : X' ≃+ (Fin j → X)), ∃ p : IsPowGrp (splitTorus S X') (splitTorus S X) j, ∀ (i : Fin j) (χ : X), res (fun x _ => show (p.pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU (p.pr i).left ⊤ (charUnit S X χ)) = charUnit S X' (xe.symm (Pi.single i χ)) := by
  intro S X X' _ _ j xe
  refine ⟨SplitTorusPow.isPowGrp S xe, fun i χ => ?_⟩
  ext1
  rw [← SplitTorusPow.incl_apply, ← SplitTorusPow.torusMap_char]
  change ((splitTorus S X').left.presheaf.map (𝟙 _)).hom
    ((SplitTorusPow.torusMap S (SplitTorusPow.incl xe i)).left.appTop.hom (charUnit S X χ).val) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPivot
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.SatLin

theorem exists_pivot {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {Ix : Type}
    (x : Ix → V) (hx : x ≠ 0) :
    ∃ (i₀ : Ix) (u : Ix → V), x i₀ ≠ 0 ∧ ∀ i, x i = x i₀ * u i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  have : Nonempty Ix := ⟨j⟩
  let f : Ix → ℕ∞ := fun i => IsDiscreteValuationRing.addVal V (x i)
  let i₀ := Function.argmin f
  have h : ∀ i, x i₀ ∣ x i := fun i =>
    IsDiscreteValuationRing.addVal_le_iff_dvd.1 (Function.argmin_le f i)
  choose u hu using h
  refine ⟨i₀, u, fun h0 => hj ?_, hu⟩
  rw [hu j, h0, zero_mul]; rfl

theorem aux {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {K : Type} [Field K] {F : Type} [Field F] (φ : V →+* K) (hφ : Function.Injective φ) (κ : K →+* F)
    (v : AddValuation F (WithTop ℚ)) (hv : ∀ x : V, (0 : WithTop ℚ) ≤ v (κ (φ x))) {Ix : Type} (n : ℕ) :
    ∀ (w : Fin n → Ix → V) (c : Fin n → F),
      (∀ i, (0 : WithTop ℚ) ≤ v (∑ p, c p * κ (φ (w p i)))) →
      ∃ (m : ℕ) (c' : Fin m → F) (a : Fin m → Fin n → K) (u : Fin m → Ix → V),
        (∀ l, (0 : WithTop ℚ) ≤ v (c' l)) ∧ (∀ l i, φ (u l i) = ∑ p, a l p * φ (w p i)) ∧
        ∀ i, ∑ p, c p * κ (φ (w p i)) = ∑ l, c' l * κ (φ (u l i)) := by
  induction n with
  | zero =>
    intro w c _
    exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun l => l.elim0, fun l => l.elim0, fun i => by simp⟩
  | succ n ih =>
    intro w c hc
    by_cases h0 : w 0 = 0
    · obtain ⟨m, c', a, u, h1, h2, h3⟩ := ih (fun p => w p.succ) (fun p => c p.succ) (fun i => by
        have := hc i
        rw [Fin.sum_univ_succ, h0] at this
        simpa using this)
      refine ⟨m, c', fun l => Fin.cons 0 (a l), u, h1, fun l i => ?_, fun i => ?_⟩
      · rw [Fin.sum_univ_succ, h2]; simp
      · rw [Fin.sum_univ_succ, h0, ← h3]; simp
    · obtain ⟨i₀, u₀, hne, hu⟩ := exists_pivot (w 0) h0
      have hne' : φ (w 0 i₀) ≠ 0 := fun h => hne (hφ (by rw [h, map_zero]))
      have key : ∀ i, ∑ p : Fin n, c p.succ * κ (φ (w p.succ i - w p.succ i₀ * u₀ i)) =
          ∑ p, c p * κ (φ (w p i)) - (∑ p, c p * κ (φ (w p i₀))) * κ (φ (u₀ i)) := fun i => by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hu i, add_mul, Finset.sum_mul]
        simp only [map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, _root_.mul_assoc]
        ring
      obtain ⟨m, c', a, u, h1, h2, h3⟩ := ih (fun p i => w p.succ i - w p.succ i₀ * u₀ i)
        (fun p => c p.succ) (fun i => by
          rw [key i]
          refine AddValuation.map_le_sub v (hc i) ?_
          rw [AddValuation.map_mul]
          exact add_nonneg (hc i₀) (hv _))
      refine ⟨m + 1, Fin.cons (∑ p, c p * κ (φ (w p i₀))) c',
        Fin.cons (Fin.cons (φ (w 0 i₀))⁻¹ 0)
          (fun l => Fin.cons (-(∑ p, a l p * φ (w p.succ i₀)) * (φ (w 0 i₀))⁻¹) (a l)),
        Fin.cons u₀ u, fun l => ?_, fun l i => ?_, fun i => ?_⟩
      · refine Fin.cases ?_ (fun l => ?_) l
        · simpa using hc i₀
        · simpa using h1 l
      · refine Fin.cases ?_ (fun l => ?_) l
        · rw [Fin.sum_univ_succ, hu i]
          simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
            add_zero, map_mul]
          rw [inv_mul_cancel_left₀ hne']
        · rw [Fin.sum_univ_succ, hu i]
          simp only [Fin.cons_zero, Fin.cons_succ, map_mul]
          rw [h2, _root_.mul_assoc, inv_mul_cancel_left₀ hne', neg_mul, Finset.sum_mul]
          simp only [map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, _root_.mul_assoc]
          ring
      · rw [Fin.sum_univ_succ (n := m)]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [← h3, key]
        ring

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (Ix : Type) (n : ℕ) (w : Fin n → Ix → V) (c : Fin n → F), (∀ i, (0 : WithTop ℚ) ≤ v (∑ p, c p * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w p i)))) → ∃ (m : ℕ) (c' : Fin m → F) (a : Fin m → Fin n → (FractionRing V)) (u : Fin m → Ix → V), (∀ l, (0 : WithTop ℚ) ≤ v (c' l)) ∧ (∀ l i, algebraMap V (FractionRing V) (u l i) = ∑ p, a l p * algebraMap V (FractionRing V) (w p i)) ∧ ∀ i, ∑ p, c p * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w p i)) = ∑ l, c' l * algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (u l i)) := by
  intro V _ _ _ ϖ hϖ F _ _ v hv Ix n w c hc
  exact aux (algebraMap V (FractionRing V)) (IsFractionRing.injective V _)
    (algebraMap (FractionRing V) F) v (GC.v_alg_nonneg hϖ hv) n w c hc

end GlobalTheory.SatLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowAct
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

open GlobalTheory.Serre in

theorem exists_powAct : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j), (∀ (O : Type) [Ring O] (r : RingAct G O), ∃ r' : RingAct G' O, ∀ a i, r'.act a ≫ p.pr i = p.pr i ≫ r.act a) ∧ ∀ (O : Type) [CommRing O] (r : Geo.Tor.OAct O G), ∃ r' : Geo.Tor.OAct O G', ∀ a i, r'.act a ≫ p.pr i = p.pr i ≫ r.act a := by
  intro S G' G _ _ _ _ j p
  obtain ⟨pr, hpr, hl⟩ := p
  have hprI : ∀ i, IsMonHom (pr i) := hpr
  have hext : ∀ {X : Over S} (f g : X ⟶ G'), (∀ i, f ≫ pr i = g ≫ pr i) → f = g :=
    fun f g h => Fan.IsLimit.hom_ext hl f g h

  let lf : (G ⟶ G) → (G' ⟶ G') := fun f => Fan.IsLimit.lift hl (fun i => pr i ≫ f)
  have hlf : ∀ (f : G ⟶ G) (i : Fin j), lf f ≫ pr i = pr i ≫ f :=
    fun f i => Fan.IsLimit.fac hl _ i
  have hlf' : ∀ (f : G ⟶ G) (i : Fin j) {Z : Over S} (h : G ⟶ Z),
      lf f ≫ pr i ≫ h = pr i ≫ f ≫ h := by
    intro f i Z h
    rw [← Category.assoc, hlf, Category.assoc]
  have hone : lf (𝟙 G) = 𝟙 G' := hext _ _ (fun i => by rw [hlf]; simp)
  have hcomp : ∀ f g : G ⟶ G, lf (f ≫ g) = lf f ≫ lf g := fun f g =>
    hext _ _ (fun i => by simp only [Category.assoc, hlf, hlf'])
  have hmon : ∀ f : G ⟶ G, IsMonHom f → IsMonHom (lf f) := by
    intro f hf
    constructor
    · refine hext _ _ (fun i => ?_)
      simp only [Category.assoc, hlf, IsMonHom.one_hom]
    · refine hext _ _ (fun i => ?_)
      simp only [Category.assoc, hlf, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

  have hadd : ∀ f g : G ⟶ G, lf (lift f g ≫ μ) = lift (lf f) (lf g) ≫ μ := by
    intro f g
    refine hext _ _ (fun i => ?_)
    simp only [Category.assoc, hlf, IsMonHom.mul_hom, comp_lift_assoc, lift_map_assoc]
  refine ⟨fun O _ r => ⟨⟨fun a => lf (r.act a), fun a => hmon _ (r.hom a),
      by try dsimp only
         rw [r.map_one, hone],
      fun a b => by
        try dsimp only
        rw [r.map_mul, hcomp],
      fun a b => by
        try dsimp only
        rw [r.map_add]
        exact hadd (r.act a) (r.act b)⟩,
      fun a i => hlf _ i⟩,
    fun O _ r => ⟨⟨fun a => lf (r.act a), fun a => hmon _ (r.hom a),
      by try dsimp only
         rw [r.one, hone],
      fun a b => by
        try dsimp only
        rw [r.mul, hcomp],
      fun a b => by
        try dsimp only
        rw [r.add]
        exact hadd (r.act a) (r.act b)⟩,
      fun a i => hlf _ i⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralExpansionUniqueOfUniformizationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.integralExpansion_unique_of_uniformization : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (σ : H0 U.LG.L k) (f g : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → (∀ e, U.ExpandsAt e k σ g) → f = g := by
  first | exact @GlobalTheory.ExpUniq.main | exact GlobalTheory.ExpUniq.main | (intros; apply GlobalTheory.ExpUniq.main <;> assumption)
end

