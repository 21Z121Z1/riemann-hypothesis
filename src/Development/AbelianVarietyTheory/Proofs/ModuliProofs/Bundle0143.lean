import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.exists_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (b : O →+* O') (k : F →+* F') (r : U' ⟶ U) (hr : r ≫ c = c' ≫ spMap k) (ν : SABMap t' t r), IsDedFrac β → IsDedFrac β' → β'.comp b = k.comp β → Geo.Tor.IsNormalScheme U' → IsFinite (pullback.lift r c' hr) → ∃ C' : Cpt c' t' β', Nonempty (C'.Above C b r ν) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' C b k r hr ν _ hD hβ hN hfin
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hD
  let _ := β'.toAlgebra
  have hsq : spMap β' ≫ spMap b = spMap k ≫ spMap β := by rw [← spMap_comp, ← spMap_comp, hβ]
  have hjs : C.j ≫ C.s = c ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  have hopen := C.jQ_open
  let s₁ := pullback.snd C.s (spMap b)
  let q : pullback s₁ (spMap β') ⟶ pullback C.s (spMap β) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spMap k) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsq,
        Category.assoc])
  have q₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have q₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap k := pullback.lift_snd _ _ _
  have hq : IsPullback q (pullback.snd s₁ (spMap β')) (pullback.snd C.s (spMap β)) (spMap k) := by
    refine IsPullback.of_right ?_ q₂ (IsPullback.of_hasPullback C.s (spMap β))
    rw [q₁, ← hsq]
    exact (IsPullback.of_hasPullback s₁ (spMap β')).paste_horiz (IsPullback.of_hasPullback C.s (spMap b))
  let f : U' ⟶ pullback C.s (spMap b) := pullback.lift (r ≫ C.j) (c' ≫ spMap β') (by
    rw [Category.assoc, hjs, ← Category.assoc, hr, Category.assoc, Category.assoc, hsq])
  have f₁ : f ≫ pullback.fst _ _ = r ≫ C.j := pullback.lift_fst _ _ _
  let u : U' ⟶ pullback s₁ (spMap β') := pullback.lift f c' (pullback.lift_snd _ _ _)
  have u₁ : u ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have u₂ : u ≫ pullback.snd _ _ = c' := pullback.lift_snd _ _ _
  have hu : r ≫ C.jQ = u ≫ q := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, q₁, ← Category.assoc u, u₁, f₁, Cpt.j]
    · rw [Category.assoc, Category.assoc, q₂, ← Category.assoc u, u₂, C.jQ_over, hr]
  let g := pullback.snd C.jQ q
  let v : U' ⟶ pullback C.jQ q := pullback.lift r u hu
  have v₁ : v ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  have v₂ : v ≫ g = u := pullback.lift_snd _ _ _
  have hp : IsPullback (pullback.fst C.jQ q) (g ≫ pullback.snd _ _) c (spMap k) := by
    have := (IsPullback.of_hasPullback C.jQ q).paste_vert hq
    rwa [C.jQ_over] at this
  have hv : IsFinite v := by
    have e : v = pullback.lift r c' hr ≫ hp.isoPullback.inv := by
      rw [Iso.eq_comp_inv]
      apply pullback.hom_ext
      · rw [Category.assoc, hp.isoPullback_hom_fst, v₁, pullback.lift_fst]
      · rw [Category.assoc, hp.isoPullback_hom_snd, ← Category.assoc, v₂, u₂, pullback.lift_snd]
    rw [e]; infer_instance
  have hW : (v ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = u := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, v₂]
  obtain ⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open O' F' _ U' s₁ c' f g.opensRange (v ≫ g.isoOpensRange.hom)
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd b C.proj) hN inferInstance
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans u₁)
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans u₂)
  obtain ⟨_, _, _, _, _, mu, -⟩ := sabPull Out.CubePf.cubePull (π ≫ pullback.fst C.s (spMap b)) C.t
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m ν
  have hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β')) ≫ π ≫ pullback.fst C.s (spMap b) =
      r ≫ C.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ f₁
    rw [← j₁]
    simp only [Category.assoc]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap t' C.t ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β')) ≫ π ≫ pullback.fst C.s (spMap b)),
      n'.φ = ν.φ ≫ C.m.φ := by
    rw [hj]; exact ⟨n, hn⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'
  have hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst C.s (spMap b) (pullback.fst s₁ (spMap β') p) ∈ abLocus C.t.G := by
    intro p
    have e : pullback.fst C.s (spMap b) (pullback.fst s₁ (spMap β') p) = pullback.fst C.s (spMap β) (q p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, q₁]
    rw [e]
    change p ∈ Set.range (pullback.snd C.jQ q) ↔ q p ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G
    rw [C.ab_gen, Scheme.Pullback.range_snd]
    rfl
  refine ⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩,
    ⟨⟨π ≫ pullback.fst _ _, ?_, ?_, mu, hj, hm.symm.trans hn'⟩⟩⟩
  · ext y
    refine Iff.trans ?_ (jr y).symm
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne C.t.semi mu.cart.1, Scheme.Hom.comp_apply]
    constructor
    · intro h
      let w : pullback (π ≫ s₁) (spMap β') ⟶ pullback s₁ (spMap β') :=
        pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
      have hw : pullback.fst s₁ (spMap β') (w y) = π (pullback.fst (π ≫ s₁) (spMap β') y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      refine ⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).trans hw
    · rintro ⟨p, hp⟩
      replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp
      have := (hg p.1).1 p.2
      exact (congrArg (fun z => pullback.fst C.s (spMap b) z ∈ abLocus C.t.G) hp).mp this
  · simp only [Category.assoc, s₁, pullback.condition]
  · have key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst C.s (spMap b)) (π ≫ s₁) h) := fun h => by
      have e : pullback.lift (π ≫ pullback.fst C.s (spMap b)) (π ≫ s₁) h = π := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]
      rw [e]; exact hπ
    exact key _

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionPowerTransportCartesianSquare
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.SecMove

section General

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gs_comp {Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [gs_eq (r ≫ g) z U h, gs_eq g (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (g ⁻¹ᵁ U) z h _).symm

theorem exists_up_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (g : Y ⟶ Y') (a : LB.Sec (LB.LinComb L' φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => (g ≫ φ' k) ≫ F) ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p → r z ∈ LB.wchart L' (fun k => g ≫ φ' k) q →
        gs r z (LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p) (s.f p) =
          (pw w (fun k => g ≫ φ' k) ε r z p q).val * gs (r ≫ g) z (LB.wchart L' φ' q) (a.f q) := by
  choose u hu using fun p q => exists_pw w (fun k => g ≫ φ' k) ε p q
  have tr : ∀ {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (q q' : K → L'.ι),
      trF φ' ε (r ≫ g) z q q' = trF (fun k => g ≫ φ' k) ε r z q q' := fun r z q q' => by
    simp only [trF, Category.assoc]
  have glue : ∀ p : K → L.ι, ∃ s : Γ(Y, LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p → r z ∈ LB.wchart L' (fun k => g ≫ φ' k) q →
      gs r z _ s = (pw w (fun k => g ≫ φ' k) ε r z p q).val * gs (r ≫ g) z (LB.wchart L' φ' q) (a.f q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q =>
      LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p ⊓ LB.wchart L' (fun k => g ≫ φ' k) q
    have le : ∀ q, W q ≤ g ⁻¹ᵁ LB.wchart L' φ' q := fun q y hy =>
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
    obtain ⟨v, hv⟩ : ∃ v : ∀ q, Γ(Y, W q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gs r z (W q) (v q) = (pw w (fun k => g ≫ φ' k) ε r z p q).val * gs (r ≫ g) z (LB.wchart L' φ' q) (a.f q) :=
      ⟨fun q => (u p q).val * (Y.presheaf.map (homOfLE (le q)).op).hom ((g.app _).hom (a.f q)),
        fun Z r z q hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val (hu p q Z r z hz)))
          ((gs_res r z (le q) hz _).trans (gs_pull r g z _ (le q hz) _)))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' ((g ≫ φ' k) y)
        exact Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) v
      (fun q q' => fn_ext (V := W q ⊓ W q') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, sec_trans a (𝟙 Y ≫ g) y (le q hy.1) (le q' hy.2), tr,
          pw_trans hw _ ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2, trF_self hL _ ε (𝟙 Y) y hy.1.1, _root_.one_mul,
          ← _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel_comm])
    refine ⟨s, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz s).symm.trans ((congrArg (gs r z (W q)) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => hs p Z r z q⟩
  choose q hq using fun k => exists_chart hL' ((g ≫ φ' k) y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' (fun k => g ≫ φ' k) q := Set.mem_iInter.2 hq
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 Y) y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hs j _ (𝟙 Y) y q hy.1 m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y q hy.2 m)).symm)
  rw [pw_trans hw _ ε (𝟙 Y) y hy.1 hy.2 m m, trF_self hL' _ ε (𝟙 Y) y m, inv_one, _root_.mul_one, Units.val_mul,
    _root_.mul_assoc]
  rfl

def Rel (w : LB.Iso L' (L.pull F)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (a : LB.Sec (LB.LinComb L' φ' ε)) (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q)

theorem exists_equiv (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : w.IsGen)
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) [IsIso h] (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) :
    ∃ e : LB.Sec (LB.LinComb L' φ' ε) ≃ LB.Sec (LB.LinComb L φ ε), ∀ a, Rel w φ' φ ε h a (e a) := by
  have H := fun s => GlobalTheory.SecPull.existsUnique_secPull X X' Y Y' L L' F hL hL' w hw K φ' φ ε h hc s
  choose d hd hd' using H
  obtain rfl : φ = fun k => (inv h ≫ φ' k) ≫ F := funext fun k => by
    rw [Category.assoc, hc, IsIso.inv_hom_id_assoc]
  have inj : Function.Injective d := fun s s' e => by
    have e : s.f = s'.f := funext fun p => fn_ext fun y hy => by
      choose q hq using fun k => exists_chart hL' (φ' k (inv h y))
      have h₁ := hd s _ (inv h) y p q (Set.mem_iInter.1 hy) hq
      have h₂ := hd s' _ (inv h) y p q (Set.mem_iInter.1 hy) hq
      rw [IsIso.inv_hom_id] at h₁ h₂
      rw [e] at h₁
      exact h₁.trans h₂.symm
    cases s; cases s'; cases e; rfl
  have surj : Function.Surjective d := fun a => by
    obtain ⟨s, hs⟩ := exists_up_sec ((isGen_iff w).1 hw) hL hL' φ' ε (inv h) a
    refine ⟨s, (hd' s a fun Z r z p q hp hq => ?_).symm⟩
    have e : ∀ k, (r ≫ h) ≫ inv h ≫ φ' k = r ≫ φ' k := fun k => by simp
    rw [hs Z (r ≫ h) z p q (Set.mem_iInter.2 fun k => by
        show F (((r ≫ h) ≫ inv h ≫ φ' k) z) ∈ L.U (p k)
        rw [e]; exact hp k) (Set.mem_iInter.2 fun k => by
        show ((r ≫ h) ≫ inv h ≫ φ' k) z ∈ L'.U (q k)
        rw [e]; exact hq k), Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp only [pw, e]
  refine ⟨(Equiv.ofBijective d ⟨inj, surj⟩).symm, fun a => ?_⟩
  have := hd ((Equiv.ofBijective d ⟨inj, surj⟩).symm a)
  rw [show d ((Equiv.ofBijective d ⟨inj, surj⟩).symm a) = a from (Equiv.ofBijective d ⟨inj, surj⟩).apply_symm_apply a]
    at this
  exact this

def LinAt {Y₁ Y₂ T Z : Scheme.{0}} (L : LB X) (N : ℤ) (σ₁ : Y₁ ⟶ X) (σ₂ : Y₂ ⟶ X) (m : Y₂ ⟶ Y₁) (π : Y₂ ⟶ T) {n : ℕ}
    (b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₁) (fun _ => N))) (c : Fin n → Γ(T, ⊤))
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₂) (fun _ => N))) (r : Z ⟶ Y₂) (z : Z) (p : L.ι) : Prop :=
  gs r z (LB.wchart L (fun _ : Fin 1 => σ₂) (fun _ => p)) (s.f (fun _ => p)) =
    ∑ i, gs (r ≫ π) z ⊤ (c i) * gs (r ≫ m) z (LB.wchart L (fun _ : Fin 1 => σ₁) (fun _ => p)) ((b i).f (fun _ => p))

theorem val_iff {Y₁ Y₂ T : Scheme.{0}} (hL : L.IsLB) (N : ℤ) (σ₁ : Y₁ ⟶ X) (σ₂ : Y₂ ⟶ X) (m : Y₂ ⟶ Y₁) (π : Y₂ ⟶ T)
    (hm : m ≫ σ₁ = σ₂) {n : ℕ}
    (b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₁) (fun _ => N))) (c : Fin n → Γ(T, ⊤))
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₂) (fun _ => N))) :
    (∀ (z : Y₂) (J), Good L z J → sval s (𝟙 _) z J = ∑ i, gs π z ⊤ (c i) * sval (b i) m z J) ↔
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₂) (z : Z) (p : L.ι), σ₂ (r z) ∈ L.U p → LinAt L N σ₁ σ₂ m π b c s r z p := by
  constructor
  · intro H Z r z p hp
    obtain ⟨J, hJ, e⟩ := exists_good L hL (r z) (fun _ : Fin 1 => σ₂) (fun _ => p) (fun _ _ _ => rfl) (fun _ => hp)
    have := congrArg (r.stalkMap z).hom (H (r z) J hJ)
    rw [sval_of s _ _ J (fun _ => p) (fun k => by rw [Category.id_comp]; exact e k), map_sum] at this
    have e₀ := gs_comp r (𝟙 Y₂) z (LB.wchart L (fun _ : Fin 1 => σ₂) (fun _ => p)) (Set.mem_iInter.2 fun _ => hp)
      (s.f fun _ => p)
    rw [Category.comp_id] at e₀
    refine e₀.trans (this.trans (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_mul, sval_of (b i) _ _ J (fun _ => p) (fun k => by rw [hm]; exact e k)]
    exact congrArg₂ (· * ·) (gs_comp r π z ⊤ trivial _).symm
      (gs_comp r m z (LB.wchart L (fun _ : Fin 1 => σ₁) (fun _ => p)) (Set.mem_iInter.2 fun _ => by
        show (m ≫ σ₁) (r z) ∈ L.U p
        rw [hm]; exact hp) _).symm
  · intro H z J hJ
    have := H _ (𝟙 _) z (J σ₂) (hJ σ₂)
    rw [LinAt, Category.id_comp, Category.id_comp] at this
    rw [sval_of s _ _ J (fun _ => J σ₂) (fun k => by rw [Category.id_comp])]
    refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [sval_of (b i) _ _ J (fun _ => J σ₂) (fun k => by rw [hm])]

theorem linAt_iff {Y₁ Y₂ T Y₁' Y₂' T' Z : Scheme.{0}} (w : LB.Iso L' (L.pull F)) (N : ℤ)
    {σ₁ : Y₁ ⟶ X} {σ₂ : Y₂ ⟶ X} {m : Y₂ ⟶ Y₁} {π : Y₂ ⟶ T}
    {σ₁' : Y₁' ⟶ X'} {σ₂' : Y₂' ⟶ X'} {m' : Y₂' ⟶ Y₁'} {π' : Y₂' ⟶ T'}
    {h₁ : Y₁' ⟶ Y₁} {h₂ : Y₂' ⟶ Y₂} {u : T' ⟶ T} (hm' : m' ≫ σ₁' = σ₂') (hh : m' ≫ h₁ = h₂ ≫ m)
    (hπ : π' ≫ u = h₂ ≫ π) {n : ℕ}
    {b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₁) (fun _ => N))} (c : Fin n → Γ(T, ⊤))
    {s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₂) (fun _ => N))}
    {b' : Fin n → LB.Sec (LB.LinComb L' (fun _ : Fin 1 => σ₁') (fun _ => N))}
    {s' : LB.Sec (LB.LinComb L' (fun _ : Fin 1 => σ₂') (fun _ => N))}
    (hb : ∀ i, Rel w _ _ _ h₁ (b' i) (b i)) (hs : Rel w _ _ _ h₂ s' s) (r : Z ⟶ Y₂') (z : Z) (p : L.ι) (q : L'.ι)
    (hp : F (σ₂' (r z)) ∈ L.U p) (hq : σ₂' (r z) ∈ L'.U q) :
    LinAt L' N σ₁' σ₂' m' π' b' (fun i => u.appTop.hom (c i)) s' r z q ↔ LinAt L N σ₁ σ₂ m π b c s (r ≫ h₂) z p := by
  subst hm'
  have e₁ := hs Z r z (fun _ => p) (fun _ => q) (fun _ => hp) (fun _ => hq)
  have e₂ := fun i => hb i Z (r ≫ m') z (fun _ => p) (fun _ => q) (fun _ => hp) (fun _ => hq)
  have e₃ : pw w (fun _ : Fin 1 => σ₁') (fun _ => N) (r ≫ m') z (fun _ => p) (fun _ => q) =
      pw w (fun _ : Fin 1 => m' ≫ σ₁') (fun _ => N) r z (fun _ => p) (fun _ => q) := by
    simp only [pw, Category.assoc]
  have e₄ : ∀ i, gs (r ≫ π') z ⊤ (u.appTop.hom (c i)) = gs ((r ≫ h₂) ≫ π) z ⊤ (c i) := fun i =>
    (gs_pull (r ≫ π') u z ⊤ trivial (c i)).trans (by rw [Category.assoc, hπ, Category.assoc])
  have e₅ : (r ≫ h₂) ≫ m = (r ≫ m') ≫ h₁ := by rw [Category.assoc, ← hh, Category.assoc]
  unfold LinAt
  rw [e₁, e₅]
  simp only [e₂, e₃, e₄, mul_left_comm _ (Units.val _), ← Finset.mul_sum, Units.mul_right_inj]

end General

def totMap {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {f : Z' ⟶ Z} {φ : G'.left ⟶ G.left}
    (hp : IsPullback φ G'.hom G.hom f) {T' : Over Z'} {T : Over Z} (u : T'.left ≅ T.left)
    (hu : u.hom ≫ T.hom = T'.hom ≫ f) : (T' ⊗ G').left ⟶ (T ⊗ G).left :=
  pullback.lift ((fst T' G').left ≫ u.hom) ((snd T' G').left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hu, hp.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w])

section
variable {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {f : Z' ⟶ Z} {φ : G'.left ⟶ G.left}
    (hp : IsPullback φ G'.hom G.hom f) {T' : Over Z'} {T : Over Z} (u : T'.left ≅ T.left)
    (hu : u.hom ≫ T.hom = T'.hom ≫ f)

theorem totMap_fst : totMap hp u hu ≫ (fst T G).left = (fst T' G').left ≫ u.hom := pullback.lift_fst _ _ _

theorem totMap_snd : totMap hp u hu ≫ (snd T G).left = (snd T' G').left ≫ φ := pullback.lift_snd _ _ _

theorem totMap_isIso : IsIso (totMap hp u hu) := by
  have p₁ : IsPullback (snd T' G').left (fst T' G').left G'.hom T'.hom := (IsPullback.of_hasPullback T'.hom G'.hom).flip
  have p₂ : IsPullback (snd T G).left (fst T G).left G.hom T.hom := (IsPullback.of_hasPullback T.hom G.hom).flip
  have p₃ := p₁.paste_horiz hp
  rw [← totMap_snd hp u hu, ← hu] at p₃
  have p₄ := IsPullback.of_right p₃ (totMap_fst hp u hu) p₂
  exact p₄.isIso_fst_of_isIso

end

theorem transport : ∀ (Z Z' : Scheme.{0}) (G : Over Z) (G' : Over Z') (f : Z' ⟶ Z) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsPullback φ G'.hom G.hom f → LBIso L' (L.pull φ) → ∀ N : ℕ, ∃ e : ∀ (T' : Over Z') (T : Over Z) (u : T'.left ≅ T.left), u.hom ≫ T.hom = T'.hom ≫ f → (LB.Sec (Out.LPow G' L' (N : ℤ) T') ≃ LB.Sec (Out.LPow G L (N : ℤ) T)), ∀ (T₁' T₂' : Over Z') (T₁ T₂ : Over Z) (u₁ : T₁'.left ≅ T₁.left) (u₂ : T₂'.left ≅ T₂.left) (h₁ : u₁.hom ≫ T₁.hom = T₁'.hom ≫ f) (h₂ : u₂.hom ≫ T₂.hom = T₂'.hom ≫ f) (k' : T₂' ⟶ T₁') (k : T₂ ⟶ T₁), k'.left ≫ u₁.hom = u₂.hom ≫ k.left → ∀ (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) T₁')) (c : Fin n → Γ(T₂.left, ⊤)) (s : LB.Sec (Out.LPow G' L' (N : ℤ) T₂')), GlobalTheory.LN.Lin G' L' N k' b (fun i => u₂.hom.appTop.hom (c i)) s ↔ GlobalTheory.LN.Lin G L N k (fun i => e T₁' T₁ u₁ h₁ (b i)) c (e T₂' T₂ u₂ h₂ s) := by
  intro Z Z' G G' f φ L L' hL hL' hp ⟨w, hw⟩ N
  have H := fun (T' : Over Z') (T : Over Z) (u : T'.left ≅ T.left) (hu : u.hom ≫ T.hom = T'.hom ≫ f) =>
    haveI := totMap_isIso hp u hu
    exists_equiv hL hL' w hw (fun _ : Fin 1 => (snd T' G').left) (fun _ => (snd T G).left) (fun _ => (N : ℤ))
      (totMap hp u hu) (fun _ => (totMap_snd hp u hu).symm)
  choose e he using H
  refine ⟨e, fun T₁' T₂' T₁ T₂ u₁ u₂ h₁ h₂ k' k hk n b c s => ?_⟩
  have hm : (k ▷ G).left ≫ (snd T₁ G).left = (snd T₂ G).left := by rw [← Over.comp_left, whiskerRight_snd]
  have hm' : (k' ▷ G').left ≫ (snd T₁' G').left = (snd T₂' G').left := by rw [← Over.comp_left, whiskerRight_snd]
  have hf : (k ▷ G).left ≫ (fst T₁ G).left = (fst T₂ G).left ≫ k.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have hf' : (k' ▷ G').left ≫ (fst T₁' G').left = (fst T₂' G').left ≫ k'.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have hh : (k' ▷ G').left ≫ totMap hp u₁ h₁ = totMap hp u₂ h₂ ≫ (k ▷ G).left := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst T₁ G).left = (_ ≫ _) ≫ (fst T₁ G).left
      rw [Category.assoc, Category.assoc, totMap_fst, hf, reassoc_of% hf', hk, ← Category.assoc, ← Category.assoc,
        totMap_fst]
    · show (_ ≫ _) ≫ (snd T₁ G).left = (_ ≫ _) ≫ (snd T₁ G).left
      rw [Category.assoc, Category.assoc, totMap_snd, hm, reassoc_of% hm', totMap_snd]
  have key := fun (W : Scheme.{0}) (r : W ⟶ (T₂' ⊗ G').left) =>
    linAt_iff w (N : ℤ) hm' hh (totMap_fst hp u₂ h₂).symm c (fun i => he T₁' T₁ u₁ h₁ (b i)) (he T₂' T₂ u₂ h₂ s) r
  refine (val_iff hL' _ _ _ _ _ hm' b _ s).trans (Iff.trans ?_ (val_iff hL _ _ _ _ _ hm _ c _).symm)
  constructor
  · intro H W r z p hz
    haveI := totMap_isIso hp u₂ h₂
    obtain ⟨r', rfl⟩ : ∃ r', r = r' ≫ totMap hp u₂ h₂ := ⟨r ≫ inv (totMap hp u₂ h₂), by simp⟩
    obtain ⟨q, hq⟩ := exists_chart hL' ((snd T₂' G').left (r' z))
    refine (key W r' z p q ?_ hq).1 (H W r' z q hq)
    show ((snd T₂' G').left ≫ φ) (r' z) ∈ L.U p
    rw [← totMap_snd hp u₂ h₂]; exact hz
  · intro H W r z q hq
    obtain ⟨p, hz⟩ := exists_chart hL (φ ((snd T₂' G').left (r z)))
    refine (key W r z p q hz hq).2 (H W _ z p ?_)
    show (totMap hp u₂ h₂ ≫ (snd T₂ G).left) (r z) ∈ L.U p
    rw [totMap_snd]; exact hz

end GlobalTheory.SecMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymplecticSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EllipticLevel

theorem exists_stdSymp_of_rel {k g : ℕ} (hk : 0 < k) {G R : Type} [CommGroup G] [CommRing R] [IsDomain R]
    (hc : ∀ d, d ∣ k → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) {ze : Rˣ} (hz : IsPrimitiveRoot ze k)
    (W : G → G → Rˣ → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) (halt : ∀ x, x ^ k = 1 → W x x 1)
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x, x ^ k = 1 → (∀ y, y ^ k = 1 → W x y 1) → x = 1) :
    ∃ v : Fin (2 * g) → G, (∀ i, v i ^ k = 1) ∧ ∀ i j, W (v i) (v j) (ze ^ Out.stdSymp g i j) := by
  classical

  set H : Subgroup G := (powMonoidHom k : G →* G).ker with hH
  have memH : ∀ x : G, x ∈ H ↔ x ^ k = 1 := fun x => by
    rw [hH, MonoidHom.mem_ker, powMonoidHom_apply]
  have torsH : ∀ x : H, (x : G) ^ k = 1 := fun x => (memH x).1 x.2

  let f : H → H → Rˣ := fun x y => (hW x y (torsH x) (torsH y)).exists.choose
  have hf : ∀ x y : H, W x y (f x y) := fun x y => (hW x y (torsH x) (torsH y)).exists.choose_spec
  have uniq : ∀ (x y : H) (c : Rˣ), W x y c → c = f x y := fun x y c h =>
    (hW x y (torsH x) (torsH y)).unique h (hf x y)
  have fswap : ∀ x y : H, f y x = (f x y)⁻¹ := fun x y =>
    (uniq y x _ (hsymm _ _ _ (hf x y))).symm
  have fmulL : ∀ x x' y : H, f (x * x') y = f x y * f x' y := fun x x' y =>
    (uniq _ _ _ (hmul _ _ _ _ _ (hf x y) (hf x' y))).symm
  have fmulR : ∀ x y y' : H, f x (y * y') = f x y * f x y' := fun x y y' => by
    rw [← uniq x (y * y') _ (hsymm _ _ _ (hmul _ _ _ _ _ (hf y x) (hf y' x))), fswap x y, fswap x y',
      mul_inv, inv_inv, inv_inv]
  let e : H →* H →* Rˣ :=
    MonoidHom.mk' (fun x => MonoidHom.mk' (f x) (fmulR x)) (fun x x' => by
      ext y
      simp only [MonoidHom.mk'_apply, MonoidHom.mul_apply]
      rw [fmulL])
  have heq : ∀ x y : H, e x y = f x y := fun _ _ => rfl

  have hcH : ∀ d : ℕ, d ∣ k → Nat.card {x : H // x ^ d = 1} = d ^ (2 * g) := by
    intro d hd
    obtain ⟨m, hm⟩ := hd
    have eqv : {x : H // x ^ d = 1} ≃ {x : G // x ^ d = 1} :=
      { toFun := fun x => ⟨x.1, by simpa using congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, (memH _).2 (by rw [hm, pow_mul, y.2, one_pow])⟩,
          Subtype.ext (by simpa using y.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr eqv]
    exact hc d ⟨m, hm⟩
  have hkH : ∀ x : H, x ^ k = 1 := fun x => Subtype.ext (by simpa using torsH x)
  have halt' : ∀ x : H, e x x = 1 := fun x => by
    rw [heq]
    exact (uniq x x 1 (halt x (torsH x))).symm
  have hnd' : ∀ x : H, (∀ y, e x y = 1) → x = 1 := by
    intro x hx
    apply Subtype.ext
    refine hnd x (torsH x) (fun y hy => ?_)
    have h1 := hf x ⟨y, (memH y).2 hy⟩
    rwa [← heq, hx] at h1
  obtain ⟨v, hv⟩ := GlobalTheory.exists_stdSymp_of_alternating_pairing k g H R ze hk hz hkH hcH e halt' hnd'
  refine ⟨fun i => (v i : G), fun i => torsH (v i), fun i j => ?_⟩
  have h2 := hf (v i) (v j)
  rwa [← heq, hv i j] at h2

theorem exists_symplectic_system (hL : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (k : ℕ)
    (hk : (k : K) ≠ 0) (ze : Kˣ) (hze : IsPrimitiveRoot ze k) :
    ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), (∀ i, pt i ^ k = 1) ∧
      ∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j) := by
  obtain ⟨-, -, -, -, -, hmn, -, -, -, hw, hwn, -⟩ := hL
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have := P.isAb.comm

  have hc : ∀ d, d ∣ k → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} = d ^ (2 * P.g) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hk0
    have hdK : (d : K) ≠ 0 := by
      obtain ⟨m, rfl⟩ := hd
      intro h0
      apply hk
      rw [Nat.cast_mul, h0, zero_mul]
    exact ((hmn (Sp K) P d hd0).2.2.2.2 K (𝟙 _) hdK)

  have hleft : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = a := fun a => by simp
  have hleft' : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a) = a := fun a => by simp
  haveI : IsDomain Γ(Sp K, ⊤) := Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (Function.LeftInverse.injective hleft')
  have hz' : IsPrimitiveRoot (unitOn ze) k :=
    hze.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)
      (Units.map_injective (Function.LeftInverse.injective hleft))
  have hwB := hw (Sp K) P k (Out.baseOver (Sp K))
  obtain ⟨v, hv1, hv2⟩ := exists_stdSymp_of_rel (G := Out.baseOver (Sp K) ⟶ P.A) (R := Γ(Sp K, ⊤)) hk0 hc hz'
    (fun x y c => Out.WeilIs P.A P.L k x y c) hwB.1 hwB.2.1 hwB.2.2.1
    (fun _ _ _ h => GlobalTheory.CommPairing.weilIs_symm P.isLB h) (fun x hx h => hwn K P k hk x hx h)
  exact ⟨v, hv1, hv2⟩

end GlobalTheory.EllipticLevel

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriodMapGenusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateIso_of_periodMap_genus_alt : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (Q : D'.La →+ (Fin P.g → ℂ)), 1 ≤ D.p + D.q → (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → u.IsAH Hm χ → Function.Injective Q → (∀ z, z ∈ u.Λ ↔ z ∈ Q.range) → (∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : ℂ →+* K), ∃ I : TateIso D K (Over.mk (spMap β) ⟶ P.A) (fun c y => y ≫ act.act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n : ℕ, 0 < n → (I.ζ n : K) = β (Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n)) ∧ ∀ x, (I.ev n x).left = spMap β ≫ (u.ex ((n : ℂ)⁻¹ • Q (f n x))).left := by
  first | exact @GlobalTheory.exists_tateIso_of_periodMap_genus | exact GlobalTheory.exists_tateIso_of_periodMap_genus | (intros; apply GlobalTheory.exists_tateIso_of_periodMap_genus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAffineOpenNonzeroLocusOfFibrewiseAmpleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (d : ℕ) (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw M d)), 1 ≤ d → IsProper f → M.IsLB → (⨆ i, Out.nonzeroLocus (u i) = ⊤) → (∀ q : Ideal R, q.IsPrime → ∃ (k : Type) (_ : Field k) (β : R →+* k), RingHom.ker β = q ∧ Out.RelAmple (Over.mk (pullback.snd f (spMap β))) (M.pull (pullback.fst f (spMap β)))) → ∀ i, IsAffineOpen (Out.nonzeroLocus (u i)) := by
  first | exact @GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres | exact GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres | (intros; apply GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres <;> assumption)
end

