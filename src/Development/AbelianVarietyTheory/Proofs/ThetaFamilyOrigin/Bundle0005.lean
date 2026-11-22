import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsoOfEqualCoordinateConesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_of_equal_coordinateCones : ∀ (K : Type) [Field K] [IsAlgClosed K] (X X' : Over (Sp K)) [IsIntegral X.left] [IsIntegral X'.left] [IsProper X.hom] [IsProper X'.hom] (H : LB X.left) (H' : LB X'.left) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy X.hom H s Set.univ → ImmBy X'.hom H' s' Set.univ → cone X.hom H s = cone X'.hom H' s' → ∃ φ : X ≅ X', ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ X.left) (v : J → R), Crd H s y v → Crd H' s' (y ≫ φ.hom.left) v := by
  first | exact @GlobalTheory.ZH.IsoCone.exists_iso | exact GlobalTheory.ZH.IsoCone.exists_iso | (intros; apply GlobalTheory.ZH.IsoCone.exists_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelThetaPtOfPolarisedIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_thetaPt_of_polarisedIso : Out.Laws → ∀ (g N' : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (hg : P.g = g) (hg' : P'.g = g) (φ : P.A ≅ P'.A), IsPolIso P P' φ → ∀ (ze : Γ(Sp K, ⊤)ˣ) (lev' : Out.Level P' (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P' N' (levelPoint lev' hg') v → ∃ lev : Out.Level P (N' ^ 2) ze, (∀ i, levelBasis lev hg i ≫ φ.hom = levelBasis lev' hg' i) ∧ Out.IsThetaPt P N' (levelPoint lev hg) v := by
  first | exact @GlobalTheory.exists_level_thetaPt_of_polIso | exact GlobalTheory.exists_level_thetaPt_of_polIso | (intros; apply GlobalTheory.exists_level_thetaPt_of_polIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.HomogeneousCoordsOfIsValueAtFrameStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoords_of_isValueAt_frame : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (x : (Out.baseOver (Sp K)) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (Out.baseOver (Sp K)).left) (K := Fin 1) (fun _ => x.left) (fun _ => (N : ℤ)))) (w : J → Γ((Out.baseOver (Sp K)).left, ⊤)), (∀ a, Out.IsValueAt P.A P.L N (t a) x τ (w a)) → Crd (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) (x.left : Sp K ⟶ P.A.left) (fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w a)) := by
  first | exact @GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt | exact GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt | (intros; apply GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsClosedImmersionOfSpanLinePowerSectionsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_of_span_linePowerSections : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) [Fintype J] (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left), 4 ≤ N → Submodule.span Γ((Out.baseOver (Sp K)).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (t a) : Out.SecM P.A P.L N (Out.baseOver (Sp K)))) = ⊤ → ImmBy P.A.hom (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) Set.univ := by
  first | exact @GlobalTheory.PowSec.immBy_down_of_span | exact GlobalTheory.PowSec.immBy_down_of_span | (intros; apply GlobalTheory.PowSec.immBy_down_of_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoPullOfHomPreservingCoordinates
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PolAgree

open FieldDescentGen

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem crd_pull {X Y : Scheme.{0}} (φ : X ⟶ Y) (H : LB Y) {J : Type} (s : J → H.Sec) {R : Type} [CommRing R]
    (y : Sp R ⟶ X) (v : J → R) (h : Crd H s (y ≫ φ) v) :
    Crd (H.pull φ) (fun j => secPull H φ (s j)) y v := by
  obtain ⟨l, c, hl, hv⟩ := h
  have hl' : ⊤ ≤ y ⁻¹ᵁ (H.pull φ).U (fun _ => l) := fun z hz => mem_pull.2 (hl hz)
  refine ⟨fun _ => l, c, hl', fun j => ?_⟩
  rw [hv j]
  congr 1
  unfold valR
  rw [dif_pos hl, dif_pos hl']
  congr 1
  change _ = (y.appLE _ ⊤ hl').hom ((φ.appLE _ _ (pull_le H φ (fun _ => l))).hom ((s j).f l))
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem mulA_comp {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (φ : A ⟶ B) [IsMonHom φ] (m : ℕ) :
    Out.mulA A m ≫ φ = φ ≫ Out.mulA B m := by
  unfold Out.mulA
  rw [MonObj.comp_pow, Category.comp_id]
  have := map_pow (IsMonHom.monoidHom φ A) (𝟙 A) m
  simpa using this

theorem lbIso_pull : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (s' : J → (lbPow P'.L N).Sec) (a : J) (θ : (lbPow P.L 1).Sec) (θ' : (lbPow P'.L 1).Sec) (φ : P.A ⟶ P'.A), 1 ≤ m → IsMonHom φ → ⨆ j, Out.nonzeroLocus (s j) = ⊤ → (∀ (F : Type) [Field F] (y : Sp F ⟶ P.A.left) (v : J → F), Crd (lbPow P.L N) s y v → Crd (lbPow P'.L N) s' (y ≫ φ.left) v) → (∃ l, θ.f l ≠ 0) → (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((s a).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((θ).f l))) → (∀ (y : P'.A.left) k l, y ∈ (lbPow P'.L N).U k → (Out.mulA P'.A m).left y ∈ (lbPow P'.L 1).U l → Associated (gs (𝟙 P'.A.left) y ((lbPow P'.L N).U k) ((s' a).f k)) (gs (Out.mulA P'.A m).left y ((lbPow P'.L 1).U l) ((θ').f l))) → LBIso (P'.L.pull φ.left) P.L := by
  intro h K _ _ P P' N m J s s' a θ θ' φ hm hφ hs hcrd hθ hP hP'
  have := polAV_isIntegral_of_isAlgClosed K P
  have hL := P.isLB
  have hL' := P'.isLB
  have hN : (lbPow P.L N).IsLB := LB.isLB_linComb hL _ _
  have hN' : (lbPow P'.L N).IsLB := LB.isLB_linComb hL' _ _
  have h1 : (lbPow P.L 1).IsLB := LB.isLB_linComb hL _ _
  have h1' : (lbPow P'.L 1).IsLB := LB.isLB_linComb hL' _ _
  have hmul := h.mulN _ P m hm
  have hfl : Flat (Out.mulA P.A m).left := hmul.2.1
  have hsu : Surjective (Out.mulA P.A m).left := hmul.2.2.1
  have hc : (Out.mulA P.A m).left ≫ φ.left = φ.left ≫ (Out.mulA P'.A m).left := by
    rw [← Over.comp_left, mulA_comp, Over.comp_left]
  have hw := CrdIso.exists_chart_unit (H := lbPow P.L N) (H' := (lbPow P'.L N).pull φ.left) (s := s)
    (s' := fun j => secPull _ φ.left (s' j)) hs (fun F _ y v hv => crd_pull _ _ _ _ _ (hcrd F y v hv))
  have key : LBIso (lbPow P.L 1) ((lbPow P'.L 1).pull φ.left) := by
    refine GlobalTheory.T.lbIso_of_associated_germs_flat _ _ (Out.mulA P.A m).left _ _ θ (secPull _ φ.left θ') h1 (pull_isLB h1' _) hθ fun y => ?_
    obtain ⟨k, hk⟩ := exists_chart hN y
    obtain ⟨k', hk'⟩ := exists_chart hN' (φ.left y)
    obtain ⟨l, hl⟩ := exists_chart h1 ((Out.mulA P.A m).left y)
    obtain ⟨l', hl'⟩ := exists_chart h1' (φ.left ((Out.mulA P.A m).left y))
    have hl'' : (Out.mulA P'.A m).left (φ.left y) ∈ (lbPow P'.L 1).U l' := by
      rw [← Scheme.Hom.comp_apply, ← hc]; exact hl'
    have hlp : (Out.mulA P.A m).left y ∈ ((lbPow P'.L 1).pull φ.left).U (fun _ => l') := mem_pull.2 hl'
    have hkp : y ∈ ((lbPow P'.L N).pull φ.left).U (fun _ => k') := mem_pull.2 hk'
    refine ⟨l, fun _ => l', hl, hlp, ?_⟩
    have e1 : gs (Out.mulA P.A m).left y _ ((secPull _ φ.left θ').f (fun _ => l')) =
        (φ.left.stalkMap y).hom (gs (Out.mulA P'.A m).left (φ.left y) _ (θ'.f l')) := by
      rw [← gs_comp _ _ _ _ hl'', ← hc]
      exact gs_appLE _ _ _ _ _ _ hlp _
    have e2 : gs (𝟙 P.A.left) y _ ((secPull _ φ.left (s' a)).f (fun _ => k')) =
        (φ.left.stalkMap y).hom (gs (𝟙 P'.A.left) (φ.left y) _ ((s' a).f k')) := by
      rw [← gs_stalkMap _ _ _ hk']
      exact (gs_appLE _ _ _ _ _ _ hkp _).trans (by rw [Category.id_comp])
    obtain ⟨w, hw⟩ := hw k (fun _ => k')
    have hx : (𝟙 P.A.left : _ ⟶ _) y ∈ ((lbPow P'.L N).pull φ.left).U (fun _ => k') ⊓ (lbPow P.L N).U k :=
      ⟨hkp, hk⟩
    have e := congrArg (gs (𝟙 P.A.left) y _) (hw a)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx, gs_unit _ _ _ hx, e2] at e
    have a1 := (hP' (φ.left y) k' l' hk' hl'').map (φ.left.stalkMap y).hom
    rw [e1]
    refine (hP y k l hk hl).symm.trans (Associated.trans ?_ a1)
    exact ⟨_, (_root_.mul_comm _ _).trans e.symm⟩
  have e := (CechPic.cls_eq_iff h1 (pull_isLB h1' _)).2 key
  rw [CechPic.cls_lbPow hL, CechPic.cls_pull h1', CechPic.cls_lbPow hL', one_smul, one_smul] at e
  rw [← CechPic.cls_eq_iff (pull_isLB hL' _) hL, CechPic.cls_pull hL', e]

end GlobalTheory.ZH.PolAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LevelBasisEqOfSameThetaPtStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelBasis_eq_of_same_thetaPt : Out.Laws → ∀ (g n j N' : ℕ), Odd n → N' = n ^ j → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev lev' : Out.Level P (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P N' (levelPoint lev hg) v → Out.IsThetaPt P N' (levelPoint lev' hg) v → (∀ i, levelBasis lev hg i ^ N' = levelBasis lev' hg i ^ N') → (∀ c : Fin (2 * g) → ZMod (N' ^ 2), ∃ d : Fin (2 * g) → ZMod (N' ^ 2), v (c + n • d) ≠ 0) → ∀ i, levelBasis lev hg i = levelBasis lev' hg i := by
  first | exact @GlobalTheory.levelBasis_eq_of_isThetaPt | exact GlobalTheory.levelBasis_eq_of_isThetaPt | (intros; apply GlobalTheory.levelBasis_eq_of_isThetaPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.MemVanishingIdealOfFormVanishingTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionForm

open TorsionZero in

theorem exists_sec_of_form {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp K) {L : LB X}
    (hL : L.IsLB) {N d : ℕ} {J : Type} (s : J → (lbPow L N).Sec) {F : MvPolynomial J K}
    (hF : F.IsHomogeneous d) :
    ∃ u : (lbPow L (N * d)).Sec, ∀ (z : Sp K ⟶ X) (v : J → K), z ≫ p = 𝟙 _ → Crd (lbPow L N) s z v →
      (⊤ ≤ z ⁻¹ᵁ Out.nonzeroLocus u ↔ MvPolynomial.eval v F ≠ 0) := by
  obtain ⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩ := SectionRing.exists_sectionRing K X p L hL
  have hm := aeval_mem_of_isHomogeneous 𝒜 (fun j => (Φ N (s j)).2) hF
  obtain ⟨u, hu⟩ := (Φ (N * d)).surjective ⟨_, hm⟩
  have hu' : (Φ _ u : R) = MvPolynomial.aeval (fun j => (Φ N (s j) : R)) F := congrArg Subtype.val hu
  refine ⟨u, ?_⟩
  rintro z v hz ⟨l, c, hl, hv⟩
  obtain ⟨ρ, hρc, hρ⟩ := hρ l
  let ev : R →ₐ[K] K :=
    { (TorsionZero.val z ((lbPow L 0).U l) hl).comp ρ with
      commutes' := fun a => (congrArg (TorsionZero.val z ((lbPow L 0).U l) hl) (hρc a)).trans
        (val_const p z hz _ hl a) }
  have e₁ : ev (Φ _ u) = TorsionZero.val z ((lbPow L (N * d)).U l) hl (u.f l) :=
    congrArg (TorsionZero.val z ((lbPow L 0).U l) hl) (hρ _ u)
  have e₂ : v = fun j => ev (Φ N (s j)) * c := funext fun j => by
    rw [hv, _root_.mul_comm, CrdCalc.valR_eq z _ hl]
    exact congrArg (· * (c : K)) (congrArg (TorsionZero.val z ((lbPow L 0).U l) hl) (hρ _ (s j))).symm
  rw [EndOnTorsion.le_nonzeroLocus_iff u z l hl, ← e₁, hu', MvPolynomial.comp_aeval_apply,
    ← MvPolynomial.coe_aeval_eq_eval]
  change _ ↔ MvPolynomial.aeval v F ≠ 0
  rw [e₂, aeval_mul_of_isHomogeneous _ _ hF, mul_ne_zero_iff]
  exact (and_iff_left (pow_ne_zero _ c.ne_zero)).symm

theorem mem_vanishingIdeal_of_vanish_on_torsion :
    Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (F : MvPolynomial J K), 4 ≤ N → (k : K) ≠ 0 → N ^ P.g * P.g.factorial * d < k ^ 2 → F.IsHomogeneous d → (∀ x : (Out.baseOver (Sp K)) ⟶ P.A, x ^ k = 1 → ∃ v : J → K, Crd (lbPow P.L N) s (x.left : Sp K ⟶ P.A.left) v ∧ MvPolynomial.eval v F = 0) → F ∈ MvPolynomial.vanishingIdeal K (cone P.A.hom (lbPow P.L N) s) := by
  intro h K _ _ P N d k J s F hN hk hd hF hx
  have := polAV_isIntegral_of_isAlgClosed K P
  obtain ⟨u, hu⟩ := exists_sec_of_form P.A.hom P.isLB s hF
  have h₅ : ∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus u := fun x e hx' => by
    obtain ⟨v, hv, h0⟩ := hx x e
    exact (hu x.left v (Over.w x) hv).1 hx' h0
  rintro v ⟨z, hz, hv⟩
  by_contra hne
  have hzu := (hu z v hz hv).2 hne
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · let x : Out.baseOver (Sp K) ⟶ P.A := Over.homMk z hz
    have e : 𝟙 P.A = 1 := EndOnTorsion.eq_of_dim_zero P P hg _ _ (by rw [Category.comp_id, MonObj.comp_one])
    have e' : x = 1 := by rw [← Category.comp_id x, e, MonObj.comp_one]
    exact h₅ x (by rw [e', one_pow]) hzu
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 ((TorsionZero.top_le_iff z _).1 hzu)
    have hM1 : 1 ≤ k := Nat.pos_of_ne_zero fun e => hk (by rw [e, Nat.cast_zero])
    have hcard := (h.mulN (Sp K) P _ hM1).2.2.2.2 K (𝟙 _) hk
    have h₄ := card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing
      (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull)
      SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem
      graded_bezout_bound K P N d k 1 hg hN hk u
      ⟨j, fun e => by rw [e, Scheme.basicOpen_zero] at hj; exact hj⟩
    have e : k ^ (2 * P.g) = k ^ 2 * k ^ (2 * P.g - 2) := by rw [← pow_add]; congr 1; omega
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (h₅ x)), hcard, e] at h₄
    exact absurd (Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)) (not_le.2 hd)

end GlobalTheory.TorsionForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaFamilyOriginGermOfMultiplicationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamily_origin_germ_of_multiplication : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (x : J → ((Out.baseOver (Sp K)) ⟶ P.A)) (th : LB.Sec (Out.LPow P.A P.L 1 (Out.baseOver (Sp K)))) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (a : J), Out.IsGenSec P.A P.L 1 th → IsThetaFamily P N m x th t → x a = 1 → (∃ l, (PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l ≠ 0) ∧ (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l))) := by
  first | exact @GlobalTheory.ThetaGerm.germ_origin | exact GlobalTheory.ThetaGerm.germ_origin | (intros; apply GlobalTheory.ThetaGerm.germ_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaPtSupportMeetsEveryCosetStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPt_support_meets_every_coset : Out.Laws → ∀ (g n N' : ℕ), 2 ≤ n → n ^ 2 ∣ N' → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev : Out.Level P (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P N' (levelPoint lev hg) v → ∀ c : Fin (2 * g) → ZMod (N' ^ 2), ∃ d : Fin (2 * g) → ZMod (N' ^ 2), v (c + n • d) ≠ 0 := by
  first | exact @GlobalTheory.ThetaSupport.exists_ne_zero_in_coset | exact GlobalTheory.ThetaSupport.exists_ne_zero_in_coset | (intros; apply GlobalTheory.ThetaSupport.exists_ne_zero_in_coset <;> assumption)
end

