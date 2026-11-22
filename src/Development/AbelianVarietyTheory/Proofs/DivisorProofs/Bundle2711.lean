import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResPullURes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2677
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LinCombComp

variable {X Y Z : Scheme.{0}}

theorem gm_gen {M : LB Y} {t : LB.Gen M} (ht : t.IsGen) (f : Z ⟶ Y) (z : Z) {i j : M.ι}
    (hi : f z ∈ M.U i) (hj : f z ∈ M.U j) :
    gm f z (M.U i) (t.s i) = gm f z (M.U i ⊓ M.U j) (M.g i j) * gm f z (M.U j) (t.s j) := by
  have hm : f z ∈ M.U i ⊓ M.U j := ⟨hi, hj⟩
  exact (gm_res f z _ hm _).symm.trans ((congrArg (gm f z _) (ht i j)).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res f z _ hm _))))

theorem gm_div (M N : LB Y) (f : Z ⟶ Y) (z : Z) (p q : (LB.div M N).ι)
    (hp : f z ∈ (LB.div M N).U p) (hq : f z ∈ (LB.div M N).U q) :
    gm f z ((LB.div M N).U p ⊓ (LB.div M N).U q) ((LB.div M N).g p q) =
      gm f z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm f z (N.U p.2 ⊓ N.U q.2) (N.g p.2 q.2))⁻¹ := by
  have hm : f z ∈ (LB.div M N).U p ⊓ (LB.div M N).U q := ⟨hp, hq⟩
  show gm f z _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z _ hm _)
    ((map_inv _ _).trans (congrArg _ (gm_res f z _ hm _))))

theorem trF_self {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j) : trF φ ε r z j j = 1 :=
  Finset.prod_eq_one fun k _ => by
    rw [gm_self hL (r ≫ φ k) z (Set.mem_iInter.1 hj k), one_zpow]

theorem trF_sum {L : LB X} {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ)
    (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (r : Z ⟶ Y) (z : Z) (j₁ j₁' : K₁ → L.ι) (j₀ j₀' : K → L.ι) :
    trF (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)) r z (Sum.elim j₁ j₀) (Sum.elim j₁' j₀') =
      trF φ₁ ε₁ r z j₁ j₁' * (trF φ₀ ε₀ r z j₀ j₀')⁻¹ := by
  rw [trF, trF, trF, Fintype.prod_sum_type, ← Finset.prod_inv_distrib]
  congr 1
  exact Finset.prod_congr rfl fun k _ => zpow_neg _ _

theorem wchart_sum_le (L : LB X) {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X))
    (φ₁ : K₁ → (Y ⟶ X)) (j₁ : K₁ → L.ι) (j₀ : K → L.ι) :
    LB.wchart L φ₁ j₁ ⊓ LB.wchart L φ₀ j₀ ≤ LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀) :=
  fun _ hy => Set.mem_iInter.2 fun k => by
    cases k with
    | inl k => exact Set.mem_iInter.1 hy.1 k
    | inr k => exact Set.mem_iInter.1 hy.2 k

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem gm_iso_linComb {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K : Type} [Fintype K]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (u : LB.Iso A (LB.LinComb L φ₀ ε₀)) (hu : u.IsGen)
    (y : Y) (j₀ j₀' : K → L.ι) (a a' : A.ι) (h0 : y ∈ LB.wchart L φ₀ j₀) (ha : y ∈ A.U a)
    (h0' : y ∈ LB.wchart L φ₀ j₀') (ha' : y ∈ A.U a') :
    gm (𝟙 Y) y (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) =
      (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀' * (gm (𝟙 Y) y (A.U a ⊓ A.U a') (A.g a a'))⁻¹) *
        gm (𝟙 Y) y (LB.wchart L φ₀ j₀' ⊓ A.U a') (u.s (j₀', a')) := by
  have hp : (𝟙 Y) y ∈ (LB.div (LB.LinComb L φ₀ ε₀) A).U (j₀, a) := ⟨h0, ha⟩
  have hq : (𝟙 Y) y ∈ (LB.div (LB.LinComb L φ₀ ε₀) A).U (j₀', a') := ⟨h0', ha'⟩
  have e1 := gm_gen hu (𝟙 Y) y hp hq
  have e2 := gm_div (LB.LinComb L φ₀ ε₀) A (𝟙 Y) y (j₀, a) (j₀', a') hp hq
  have e3 : gm (𝟙 Y) y (LB.wchart L φ₀ j₀ ⊓ LB.wchart L φ₀ j₀') ((LB.LinComb L φ₀ ε₀).g j₀ j₀') =
      trF φ₀ ε₀ (𝟙 Y) y j₀ j₀' := gm_linComb L φ₀ ε₀ (𝟙 Y) y j₀ j₀' h0 h0'
  rw [e2] at e1
  exact e1.trans (congrArg (fun t => t * (gm (𝟙 Y) y (A.U a ⊓ A.U a') (A.g a a'))⁻¹ *
    gm (𝟙 Y) y (LB.wchart L φ₀ j₀' ⊓ A.U a') (u.s (j₀', a'))) e3)

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem gm_gen_sum {X Y : Scheme.{0}} {L : LB X} {K K₁ : Type} [Fintype K] [Fintype K₁]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ)
    (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))) (hc : c.IsGen)
    (y : Y) (j₁ j₁' : K₁ → L.ι) (j₀ j₀' : K → L.ι) (h1 : y ∈ LB.wchart L φ₁ j₁) (h0 : y ∈ LB.wchart L φ₀ j₀)
    (h1' : y ∈ LB.wchart L φ₁ j₁') (h0' : y ∈ LB.wchart L φ₀ j₀') :
    gm (𝟙 Y) y (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) =
      (trF φ₁ ε₁ (𝟙 Y) y j₁ j₁' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
        gm (𝟙 Y) y (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁' j₀')) (c.s (Sum.elim j₁' j₀')) := by
  rw [← trF_sum]
  exact gen_trans hc (𝟙 Y) y (wchart_sum_le L φ₀ φ₁ j₁ j₀ ⟨h1, h0⟩) (wchart_sum_le L φ₀ φ₁ j₁' j₀' ⟨h1', h0'⟩)

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem exists_iso_comp_val {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K K₁ : Type} [Fintype K] [Fintype K₁]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (hL : L.IsLB) (hA : A.IsLB)
    (u : LB.Iso A (LB.LinComb L φ₀ ε₀)) (hu : u.IsGen)
    (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))) (hc : c.IsGen) :
    ∃ u' : LB.Iso A (LB.LinComb L φ₁ ε₁), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z)
      (J : (Z ⟶ X) → L.ι) (a : A.ι), q z ∈ A.U a → Good L z J →
      gm q z _ (u'.s (fun k => J (q ≫ φ₁ k), a)) = gm q z _ (u.s (fun k => J (q ≫ φ₀ k), a)) * val c q z J := by
  have eu := gm_iso_linComb φ₀ ε₀ u hu
  have ec := gm_gen_sum φ₀ ε₀ φ₁ ε₁ c hc
  have glue : ∀ (j₁ : K₁ → L.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart L φ₁ j₁ ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K → L.ι), q z ∈ LB.wchart L φ₁ j₁ → q z ∈ A.U a →
        q z ∈ LB.wchart L φ₀ j₀ →
        gm q z (LB.wchart L φ₁ j₁ ⊓ A.U a) s =
          gm q z (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) *
            gm q z (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j₁ a
    obtain ⟨W, hW⟩ : ∃ W : (K → L.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart L φ₁ j₁ ⊓ A.U a ⊓ LB.wchart L φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart L φ₁ j₁ ⊓ A.U a := fun j₀ => (hW j₀).le.trans inf_le_left
    have l₁ : ∀ j₀, W j₀ ≤ LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀) := fun j₀ y hy => by
      rw [hW] at hy; exact wchart_sum_le L φ₀ φ₁ j₁ j₀ ⟨hy.1.1, hy.2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L φ₀ j₀ ⊓ A.U a := fun j₀ y hy => by
      rw [hW] at hy; exact ⟨hy.2, hy.1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K → L.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) *
            gm q z (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (c.s (Sum.elim j₁ j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart L φ₁ j₁ ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart L φ₁ j₁ ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ec y j₁ j₁ j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha, trF_self hL φ₁ ε₁ (𝟙 Y) y j₁ h1,
          gm_self hA (𝟙 Y) y ha, _root_.one_mul, _root_.inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, _root_.inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J a ha hJ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL (φ₀ k y)
    have h0 : y ∈ LB.wchart L φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart L φ₁ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ₁ ε₁ (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart L φ₁ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ec y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha', trF_self hL φ₀ ε₀ (𝟙 Y) y j₀ h0,
        _root_.inv_one, _root_.mul_one, _root_.one_mul, _root_.mul_mul_mul_comm, _root_.mul_assoc]
    have hm : y ∈ (LB.div (LB.LinComb L φ₁ ε₁) A).U p ⊓ (LB.div (LB.LinComb L φ₁ ε₁) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb L φ₁ ε₁ (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · have h1 := hJ.mem φ₁ q
    have h0 := hJ.mem φ₀ q
    refine (hs _ a Z q z (fun k => J (q ≫ φ₀ k)) h1 ha h0).trans ((mul_comm _ _).trans (congrArg _ ?_))
    exact (val_of c q z J _ (fun k => by cases k <;> rfl)).symm

end GlobalTheory.LinCombComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfObstructionZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LBObs.exists_lift_of_isObL_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L₀ : LB X₀), IsPullback i s₀ s (spMap π) → L₀.IsLB → IsObL S α L₀ 0 → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S X s i P L₀ hpb hL₀ hob
  obtain ⟨C', _, _, G, hbas, u, hfr, hobu⟩ := hob
  rw [map_zero] at hobu
  obtain ⟨v, hvp, hvc⟩ := GlobalTheory.T.unitCocycle_lift_of_obstruction_eq_zero R R₀ I hI π hπ hk R₁ α C' (G ⋙ OAff s₀) ((ofSys S).restrict G) u hobu
  obtain ⟨V, hV, hi, e, hpre, he, hred⟩ := GlobalTheory.T.exists_charts_squareZero_presented_scheme R R₀ I hI π hπ hk X₀ s₀ S X s i P hpb
  let V' : C' → X.Opens := fun T => V (G.obj T)
  have hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T := fun T T' a => hV (G.map a)
  let u' : ∀ (T T' : C') (_ : T ⟶ T'), Γ(X, V' T')ˣ := fun T T' a => Units.map (e (G.obj T')).toMonoidHom (v T T' a)
  have hcoc : IsCoc V' hV' u' := by
    intro T T' T'' a b
    ext
    have h1 := hvc T T' T'' a b
    change e (G.obj T'') (v T T'' (a ≫ b)).val = _
    rw [h1]
    refine ((e (G.obj T'')).map_mul _ _).trans ?_
    exact congrArg (· * e (G.obj T'') (v T' T'' b).val) (he (G.obj T') (G.obj T'') (G.map b) (v T T' a).val)
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip
    (IsClosedImmersion.spec_of_surjective _ hπ)
  haveI : Surjective i := surjective_of_isPullback_sqZero hI hπ hk hpb
  have hbas' : IsBas V' := GlobalTheory.LBObs.isBas_of_preimage_eq X X₀ i C' V' (opOf G) (fun T => hpre _) hbas
  obtain ⟨L, hL, hfrL⟩ := GlobalTheory.T.exists_lineBundle_of_thinBasis_cocycle X C' V' hV' u' hbas' hcoc
  have hH : ∀ T, opOf G T ≤ i ⁻¹ᵁ V' ((𝟭 C').obj T) := fun T => (hpre _).ge
  have hfr2 := GlobalTheory.LBObs.isFrame_pull X C' V' hV' L u' X₀ i C' (opOf G) (opOf_le G) (𝟭 C') hH hfrL
  have hueq : (fun T T' (a : T ⟶ T') => res (hH T') (pullU i _ (u' _ _ ((𝟭 C').map a)))) = u := by
    funext T T' a
    ext
    have h2 := hred (G.obj T') (v T T' a).val
    have h3 := hvp T T' a
    refine Eq.trans ?_ (h2.trans h3)
    rfl
  rw [hueq] at hfr2
  exact ⟨L, hL, GlobalTheory.LBObs.lbIso_of_isFrame X₀ C' (opOf G) (opOf_le G) (L.pull i) L₀ u hbas (LB.isLB_pull hL i) hL₀ hfr2 hfr⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLocalGeneratorNearFiniteSet
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch.Semiloc

theorem exists_basicOpen_cover : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∃ (J : Type) (_ : Fintype J) (f : J → Γ(X, W)) (k : J → L.ι), (∀ j, X.basicOpen (f j) ≤ L.U (k j)) ∧ ∀ x ∈ W, ∃ j, x ∈ X.basicOpen (f j) := by
  intro X L hL W hW
  classical
  have h : ∀ x : W, ∃ (f : Γ(X, W)) (i : L.ι), X.basicOpen f ≤ L.U i ∧ (x : X) ∈ X.basicOpen f := by
    intro x
    obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (x : X)
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le (V := L.U i) ⟨x, hi⟩ x.2
    exact ⟨f, i, hf, hxf⟩
  choose f i hf hx using h
  obtain ⟨s, hs⟩ := hW.isCompact.elim_finite_subcover (fun x : W => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).isOpen) (fun x hxW => Set.mem_iUnion.2 ⟨⟨x, hxW⟩, hx ⟨x, hxW⟩⟩)
  refine ⟨s, inferInstance, fun j => f j, fun j => i j, fun j => hf j, fun x hx => ?_⟩
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (hs hx)
  exact ⟨⟨j, hj⟩, hxj⟩

theorem exists_separating : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (F : Set X), F.Finite → F ⊆ W → (∀ x ∈ F, ∀ y ∈ F, y ⤳ x → y = x) → ∃ a : X → Γ(X, W), (∀ x ∈ F, x ∈ X.basicOpen (a x)) ∧ ∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x) := by
  intro X W hW F hF hFW hsp
  classical
  have hb : ∀ x ∈ F, ∀ y ∈ F, y ≠ x → ∃ b : Γ(X, W), x ∈ X.basicOpen b ∧ y ∉ X.basicOpen b := by
    intro x hx y hy hne
    have hn : ¬ y ⤳ x := fun h => hne (hsp x hx y hy h)
    rw [specializes_iff_forall_open] at hn
    push Not at hn
    obtain ⟨O, hO, hxO, hyO⟩ := hn
    obtain ⟨b, hbO, hxb⟩ := hW.exists_basicOpen_le (V := ⟨O, hO⟩) ⟨x, hxO⟩ (hFW hx)
    exact ⟨b, hxb, fun h => hyO (hbO h)⟩
  choose! b hb1 hb2 using hb
  refine ⟨fun x => ∏ y ∈ hF.toFinset.erase x, b x y, fun x hx => ?_, fun x hx y hy hne h => ?_⟩
  · refine Finset.prod_induction _ (fun c => x ∈ X.basicOpen c) (fun c d hc hd => ?_) ?_ (fun y hy => ?_)
    · rw [Scheme.basicOpen_mul]; exact ⟨hc, hd⟩
    · rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; exact hFW hx
    · obtain ⟨hyx, hyF⟩ := Finset.mem_erase.1 hy
      exact hb1 x hx y (hF.mem_toFinset.1 hyF) hyx
  · have hmem : y ∈ hF.toFinset.erase x := Finset.mem_erase.2 ⟨hne, hF.mem_toFinset.2 hy⟩
    dsimp only at h
    rw [← Finset.mul_prod_erase _ _ hmem, Scheme.basicOpen_mul] at h
    exact hb2 x hx y hy hne h.1

theorem exists_locGen_near_finite : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a := by
  intro X L hL W hW F hF hFW
  classical
  obtain ⟨J, _, f, k, hk, hcov⟩ := exists_basicOpen_cover X L hL W hW
  set F' : Set X := {x | x ∈ F ∧ ∀ y ∈ F, x ⤳ y → y = x} with hF'
  have hF'F : F' ⊆ F := fun x hx => hx.1
  have hF'fin : F'.Finite := hF.subset hF'F
  have hup : ∀ x ∈ F, ∃ x' ∈ F', x ⤳ x' := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.Finite.exists_minimalFor (fun y : X => closure ({y} : Set X)) {y | y ∈ F ∧ x ⤳ y}
      (hF.subset fun y hy => hy.1) ⟨x, hx, specializes_rfl⟩
    refine ⟨i, ⟨hi.1.1, fun y hy hiy => ?_⟩, hi.1.2⟩
    have h1 : closure ({y} : Set X) ⊆ closure {i} := specializes_iff_closure_subset.1 hiy
    have h2 := hi.2 ⟨hy, hi.1.2.trans hiy⟩ h1
    exact ((specializes_iff_closure_subset.2 h2).antisymm hiy).eq
  obtain ⟨a, ha, ha'⟩ := exists_separating X W hW F' hF'fin (hF'F.trans hFW)
    (fun x hx y hy hyx => (hy.2 x hx.1 hyx).symm)
  have hE : ∀ x : X, ∃ e : ∀ j, Γ(X, X.basicOpen (f j)), x ∈ W →
      GlobalTheory.Pinch.IsSecFam L (fun j => X.basicOpen (f j)) k hk e ∧
        ∀ j (h : x ∈ X.basicOpen (f j)), IsUnit ((X.presheaf.germ (X.basicOpen (f j)) x h).hom (e j)) := by
    intro x
    by_cases hx : x ∈ W
    · obtain ⟨e, he⟩ := GlobalTheory.T.exists_lineBundleLocalSectionFamily_unit_at_point X L hL W hW J f k hk x hx
      exact ⟨e, fun _ => he⟩
    · exact ⟨fun _ => 0, fun h => absurd h hx⟩
  choose E hE using hE
  obtain ⟨e, he, heu⟩ := GlobalTheory.T.lineBundleLocalSectionFamily_unit_at_finite_points X L W J (fun j => X.basicOpen (f j)) (fun j => X.basicOpen_le (f j)) k hk F'
    hF'fin a ha ha' E (fun x hx => (hE x (hFW (hF'F hx))).1) (fun x hx => (hE x (hFW (hF'F hx))).2)
  obtain ⟨V, u, hV, hgen⟩ := GlobalTheory.T.exists_localUnitGenerator_of_lineBundleLocalSectionFamily X L hL J (fun j => X.basicOpen (f j)) k hk e he
  refine ⟨V, u, fun x hx => ?_, hgen⟩
  obtain ⟨x', hx', hxx'⟩ := hup x hx
  obtain ⟨j, hj⟩ := hcov x' (hFW (hF'F hx'))
  exact hxx'.mem_open V.isOpen (hV j x' hj (heu x' hx' j hj))

end GlobalTheory.Pinch.Semiloc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCombinationTangentVectorsAffineOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS.LinTan

open GlobalTheory.FlagMod

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem le_preimage_top {T Z : Scheme.{0}} (z : T ⟶ Z) : ⊤ ≤ z ⁻¹ᵁ ⊤ := le_rfl

theorem eq_of_ev {Y : Scheme.{0}} {S : Type} [CommRing S] {U : Y.Opens} (hU : IsAffineOpen U) {z z' : Sp S ⟶ Y}
    (h : ⊤ ≤ z ⁻¹ᵁ U) (h' : ⊤ ≤ z' ⁻¹ᵁ U) (e : ∀ f, ev z U h f = ev z' U h' f) : z = z' := by
  rw [← spMap_ev z hU h, ← spMap_ev z' hU h', RingHom.ext e]

theorem le_preimage_of_fst {Y : Scheme.{0}} {B : Type} [CommRing B] {n : ℕ} {x : Sp B ⟶ Y}
    {w : Sp (TrivSqZeroExt B (Fin n → B)) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) :
    ⊤ ≤ w ⁻¹ᵁ O := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (TrivSqZeroExt B (Fin n → B))) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (TrivSqZeroExt B (Fin n → B)) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← hw] at this
  exact this

theorem exists_glue {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A →+* B) (d : Fin n → (A →+* DualNumber B))
    (hd : ∀ a f, (d a f).fst = e f) : ∃ q : A →+* TrivSqZeroExt B (Fin n → B),
      ∀ f, (q f).fst = e f ∧ ∀ a, (q f).snd a = (d a f).snd := by
  refine ⟨{ toFun := fun f => TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr fun a => (d a f).snd,
            map_one' := ?_, map_mul' := fun f g => ?_,
            map_zero' := ?_, map_add' := fun f g => ?_ }, fun f => ⟨add_zero (e f), fun a => zero_add (d a f).snd⟩⟩
  · ext <;> simp
  · ext
    · simp
    · simp [hd, mul_comm]
  · ext <;> simp
  · ext <;> simp

theorem exists_linComb {K B : Type} [CommRing K] [CommRing B] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (Y₀ : Y.affineOpens)
    (φ : K →+* B) (x : Sp B ⟶ Y) (hx : x ≫ p = spMap φ) (hxY : ⊤ ≤ x ⁻¹ᵁ Y₀.1) {n : ℕ}
    (w : Fin n → (Sp (DualNumber B) ⟶ Y)) (hwp : ∀ a, w a ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ))
    (hwx : ∀ a, spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w a = x) (c : Fin n → B) :
    ∃ S : Sp (DualNumber B) ⟶ Y, S ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ) ∧
      spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x ∧
      ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O), (valR S O f).snd = ∑ a, c a * (valR (w a) O f).snd := by
  have hwY : ∀ a, ⊤ ≤ w a ⁻¹ᵁ Y₀.1 := fun a => le_preimage_of_red (hwx a) hxY
  obtain ⟨q, hq⟩ := exists_glue (ev x Y₀.1 hxY) (fun a => ev (w a) Y₀.1 (hwY a)) (fun a f => by
    have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (w a) Y₀.1 (hwY a) (le_preimage_comp _ (hwY a))
    rw [ev_congr (hwx a) _ _ hxY] at this
    rw [this]; rfl)
  let T : Sp (TrivSqZeroExt B (Fin n → B)) ⟶ Y := spMap q ≫ tau Y₀.2
  have hT : ∀ {S : Type} [CommRing S] (σ : TrivSqZeroExt B (Fin n → B) →+* S) (z : Sp S ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ Y₀.1),
      (∀ f, σ (q f) = ev z Y₀.1 hz f) → spMap σ ≫ T = z := fun σ z hz e => by
    rw [← spMap_ev z Y₀.2 hz, ← RingHom.ext (f := σ.comp q) e, ← spMap_comp_spMap, Category.assoc]
    rfl
  let σ : ((Fin n → B) →ₗ[B] B) → (TrivSqZeroExt B (Fin n → B) →+* DualNumber B) := fun l =>
    (TrivSqZeroExt.map l).toRingHom
  have hσ1 : ∀ l r, (σ l r).fst = r.fst := fun l r => TrivSqZeroExt.fst_map l r
  have hσ2 : ∀ l r, (σ l r).snd = l r.snd := fun l r => TrivSqZeroExt.snd_map l r
  have hTx : spMap (TrivSqZeroExt.fstHom B B (Fin n → B)).toRingHom ≫ T = x := hT _ x hxY fun f => (hq f).1
  have hTw : ∀ a, spMap (σ (LinearMap.proj a)) ≫ T = w a := fun a => hT _ _ (hwY a) fun f => by
    ext
    · rw [hσ1, (hq f).1]
      have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom (w a) Y₀.1 (hwY a) (le_preimage_comp _ (hwY a))
      rw [ev_congr (hwx a) _ _ hxY] at this
      rw [this]; rfl
    · rw [hσ2]; exact (hq f).2 a
  let l : (Fin n → B) →ₗ[B] B := Fintype.linearCombination B c
  have hSx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (spMap (σ l) ≫ T) = x := by
    rw [← Category.assoc, spMap_comp_spMap, ← hTx]
    congr 2
    exact RingHom.ext fun r => hσ1 l r
  have hS : ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O),
      (valR (spMap (σ l) ≫ T) O f).snd = ∑ a, c a * (valR (w a) O f).snd := fun O hO f => by
    have hTO : ⊤ ≤ T ⁻¹ᵁ O := le_preimage_of_fst hTx hO
    have key : ∀ l', valR (spMap (σ l') ≫ T) O f = σ l' (ev T O hTO f) := fun l' => by
      rw [valR_eq_ev _ _ (le_preimage_comp _ hTO), ev_spMap _ _ _ hTO]; rfl
    rw [key, hσ2, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hTw a, key, hσ2, smul_eq_mul, mul_comm]; rfl
  refine ⟨spMap (σ l) ≫ T, ?_, hSx, hS⟩
  have hv : ∀ {S : Type} [CommRing S] (ψ : K →+* S) (f : Γ(Sp K, ⊤)),
      valR (spMap ψ) ⊤ f = ψ (ev (𝟙 (Sp K)) ⊤ (le_preimage_top _) f) := fun ψ f => by
    rw [← Category.comp_id (spMap ψ), valR_eq_ev _ _ (le_preimage_top _), ev_spMap _ _ _ (le_preimage_top _)]; rfl
  refine eq_of_ev (isAffineOpen_top (Sp K)) (le_preimage_top _) (le_preimage_top _) fun f => ?_
  rw [← valR_eq_ev, ← valR_eq_ev, hv]
  ext
  · have := ev_spMap (TrivSqZeroExt.fstHom B B B).toRingHom ((spMap (σ l) ≫ T) ≫ p) ⊤ (le_preimage_top _) (le_preimage_top _)
    rw [ev_congr (z' := spMap φ) (by rw [← Category.assoc, hSx, hx]) _ _ (le_preimage_top _)] at this
    have h2 := RingHom.congr_fun this f
    rw [← valR_eq_ev, hv] at h2
    rw [valR_eq_ev _ _ (le_preimage_top _)]
    exact h2.symm
  · rw [valR_comp_app, hS (p ⁻¹ᵁ ⊤) (le_preimage_top (x ≫ p))]
    simp only [← valR_comp_app, hwp, hv]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.CechKS.LinTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerLocalEigenFrame
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

theorem exists_genKS_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z (fun τ k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) D ∧ ∀ (U : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U), TopForm.IsFrame ω → ∀ hx : x ∈ U, RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ _ _ x φ f hφ
  obtain ⟨U, hU, hxU, ρ, n, e, v, φU, hρ, htan, hbas, heig, hw⟩ := GlobalTheory.T.exists_spread_eigenFrame_lieAlgebra_toroidalComponent E H Dw l Xo c TF Z x φ f hφ
  obtain ⟨ε, b, hKS⟩ := GlobalTheory.T.exists_logKS_symPair_basis_alt E H Dw l Xo c TF U n e v φU htan hbas heig
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_logVectorField_extend_functionFieldDerivation E H Dw l Xo c TF Z U hU ρ hρ (fun j => b j)
  exact ⟨D, ⟨U, hU, ρ, n, e, v, ε, fun j => b j, hρ, htan, hbas, fun τ i => hw τ i, hKS, hD⟩,
    fun U' ω hω hx => GlobalTheory.T.exists_logVectorField_topForm_pairing_regular_at_point E H Dw l Xo c TF Z x U hU hxU ρ hρ b D hD U' ω hω hx⟩

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatchingLineBundleGeneratorsNearPinchingPoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matching_lineBundle_generators_near_pinching_point : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X') (LZ : LB Z), L'.IsLB → LZ.IsLB → ∀ w : LB.Iso (L'.pull i') (LZ.pull p'), w.IsGen → ∀ z : Z, ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ) (sZ : ∀ j, Γ(Z, LZ.U j ⊓ i ⁻¹ᵁ W)ˣ), i z ∈ W ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' ∧ GlobalTheory.PinchLift.GenOn LZ (i ⁻¹ᵁ W) sZ ∧ GlobalTheory.PinchLift.Matched i' p' L' LZ w (p ⁻¹ᵁ W) (i ⁻¹ᵁ W) s' sZ := by
  first | exact @GlobalTheory.PinchLift.near_matched | exact GlobalTheory.PinchLift.near_matched | (intros; apply GlobalTheory.PinchLift.near_matched <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFibreOfGeometricLiftingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_fiber_of_geometric_lifting : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S P' X : Scheme.{0}) (π : S ⟶ Sp R) (h : P' ⟶ Sp R) (a : X ⟶ P') (q : X ⟶ S), Surjective π → ∀ x : P', h x = closedPoint R → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ h = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ q = s) → ∃ z : X, a z = x := by
  first | exact @GlobalTheory.Mum.exists_mem_fibre_of_geometric_lifting | exact GlobalTheory.Mum.exists_mem_fibre_of_geometric_lifting | (intros; apply GlobalTheory.Mum.exists_mem_fibre_of_geometric_lifting <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsNonzeroOfIsClosedMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), IsClosedMap p.base → ∀ (L : LB Z) (V : Y.Opens) (u : LB.Sec (L.pull (p ⁻¹ᵁ V).ι)) (y : Y), y ∈ V → (∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) = y → z ∈ nonzeroLocus u) → ∃ V₁ : Y.Opens, y ∈ V₁ ∧ V₁ ≤ V ∧ ∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) ∈ V₁ → z ∈ nonzeroLocus u := by
  first | exact @GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap | exact GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap | (intros; apply GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap <;> assumption)
end

