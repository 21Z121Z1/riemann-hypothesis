import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3488
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3484
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0751
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivCoordinateSubPotentialsConst
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
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

theorem exists_const_of_glue : ∀ {K : Type} [Field K] (A₀ : Over (Sp K)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ {I : Type} (U : I → A₀.left.Opens) (f : ∀ i, Γ(A₀.left, U i)), ⨆ i, U i = ⊤ → (∀ i i', resG A₀.left (inf_le_left : U i ⊓ U i' ≤ U i) (f i) = resG A₀.left (inf_le_right : U i ⊓ U i' ≤ U i') (f i')) → ∃ c : K, ∀ (Z : Scheme.{0}) (b : Z ⟶ A₀.left) (z : Z) (i : I), b z ∈ U i → gs b z (U i) (f i) = cst (b ≫ A₀.hom) z c := by
  intro K _ A₀ _ hab I U f hcov hcomp
  obtain ⟨F, hF, -⟩ := A₀.left.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) (by rw [hcov]) f hcomp
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨s, hs⟩ := (hG (Sp K) A₀ hab).2 F
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom s, fun Z b z i hz => ?_⟩
  rw [cst, Iso.hom_inv_id_apply, ← gs_pull b A₀.hom z ⊤ trivial s, ← hF i]
  refine (gs_res b z (le_top : U i ≤ ⊤) hz F).trans ?_
  rw [← hs]
  rfl

theorem exists_coordEq : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α → ∃ c : K, CoordEq Y h ν m₀ V pb α c := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD α hfree
  obtain ⟨T, hT₁, hT₂⟩ := hF.exists_strictHenselian_absolutely_closed_local_ring α
  have hT0 : T 0 = 𝟙 _ := hF.T_zero (hT₁ 0) (hT₂ 0)
  have hab : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb hF.pull
  have hV : ∀ i, V i ≤ Q.P.L.U (h.j i) := hC.2.2.1
  let U : (Fin 4 → h.J) → Q.P.A.left.Opens := fun i =>
    V (i 0) ⊓ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j))
  have hU : ∀ i, Y.q.left ⁻¹ᵁ U i ≤ h.W (i 0) ⊓ xU Y α (fun j => h.j (i j)) := by
    intro i y hy
    refine ⟨?_, Set.mem_iInter.2 fun k => ?_⟩
    · rw [hD.1]; exact hy.1
    · have := Set.mem_iInter.1 hy.2 (![1, 2, 0, 3] k)
      show y ∈ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k ⁻¹ᵁ Q.P.L.U (h.j (i (![1, 2, 0, 3] k)))
      rw [gtφT_eq, Scheme.Hom.comp_preimage]
      exact this
  have exA : ∀ i : Fin 4 → h.J, ∃ A : Γ(Q.P.A.left, U i), (Y.q.left.app (U i)).hom A *
      rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i) =
      dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i)) := fun i =>
    GlobalTheory.T.exists_abelianPart_function_of_weight_unit_logDeriv Y h ν hF.wt hF.basic (i 0) α (U i) ((hU i).trans inf_le_left) _
      (by rw [GlobalTheory.KS.GlueDer.rsT_eq ((hU i).trans inf_le_right)]; exact (Units.isUnit _).map _)
      (GlobalTheory.T.raynaud_coordinate_in_charts_has_character_weight Y α _ _ ((hU i).trans inf_le_right))
  choose A hA using exA
  let Oi : (Fin 4 → h.J) → A₀.left.Opens := fun i =>
    T 0 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 0)) ⊓ T 1 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 1)) ⊓ T 2 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 2)) ⊓ T 3 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 3))
  have memO : ∀ i (p : A₀.left), p ∈ Oi i ↔ ∀ j, m₀ (T j p) ∈ V (i j) := by
    intro i p
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ j
      fin_cases j
      exacts [h0, h1, h2, h3]
    · intro H
      exact ⟨⟨⟨H 0, H 1⟩, H 2⟩, H 3⟩
  have hOU : ∀ i, Oi i ≤ m₀ ⁻¹ᵁ U i := by
    intro i p hp
    have H := (memO i p).1 hp
    refine ⟨?_, Set.mem_iInter.2 fun k => ?_⟩
    · have := H 0
      rw [hT0] at this
      exact this
    · have := hV _ (H k)
      rw [← Scheme.Hom.comp_apply, hT₁ k, Scheme.Hom.comp_apply] at this
      exact this
  have hOT : ∀ i j, Oi i ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j)) := fun i j p hp => (memO i p).1 hp j
  let f : ∀ i, Γ(A₀.left, Oi i) := fun i =>
    pbT m₀ (A i) (Oi i) + pbT (T 0) (pb (i 0)) (Oi i) - pbT (T 1) (pb (i 1)) (Oi i) +
      pbT (T 2) (pb (i 2)) (Oi i) - pbT (T 3) (pb (i 3)) (Oi i)
  have hCA : ∀ i (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ z, b z ∈ Oi i →
      CoordAt Y h ν m₀ V pb α i T a b z (gs b z (Oi i) (f i)) := by
    intro i Z a b w z hz
    have hza : a z ∈ Y.q.left ⁻¹ᵁ U i := by
      show Y.q.left (a z) ∈ U i
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
      exact hOU i hz
    have e1 : rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i) =
        resG _ (hU i) (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))) := by
      rw [← GlobalTheory.KS.GlueDer.rsT_eq (hU i)]
      refine fn_ext fun y hy => ?_
      rw [gs_rsT (𝟙 _) y ((hU i).trans inf_le_right) hy, gs_rsT (𝟙 _) y (hU i) hy,
        gs_rsT (𝟙 _) y inf_le_right (hU i hy)]
    have e2 : dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i)) =
        resG _ (hU i) (dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j)))) := by
      rw [e1]
      exact (isField_dE h ν hF.field (i 0)).2.2 _ _ (hU i) inf_le_left _
    have lhs : gs a z (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))
        (dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j)))) =
        gs (b ≫ m₀) z (U i) (A i) * gs a z (xU Y α fun j => h.j (i j)) (xc Y α fun j => h.j (i j)).val := by
      rw [← gs_res a z (hU i) hza, ← e2, ← hA i, gs_mul a z _ hza, gs_rsT a z ((hU i).trans inf_le_right) hza,
        gs_pull a Y.q.left z (U i) hza, w]
    have rhs : gs b z (Oi i) (f i) = gs (b ≫ m₀) z (U i) (A i) +
        gs (b ≫ T 0) z (m₀ ⁻¹ᵁ V (i 0)) (pb (i 0)) - gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V (i 1)) (pb (i 1)) +
        gs (b ≫ T 2) z (m₀ ⁻¹ᵁ V (i 2)) (pb (i 2)) - gs (b ≫ T 3) z (m₀ ⁻¹ᵁ V (i 3)) (pb (i 3)) := by
      simp only [f, gs_add b z _ hz, gs_sub b z _ hz, gs_pbT b m₀ z (hOU i) hz, gs_pbT b (T _) z (hOT i _) hz]
    unfold CoordAt
    rw [lhs, rhs]
    ring
  have uniq : ∀ i (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left) (z : Z) (w₁ w₂ : Z.presheaf.stalk z),
      a z ∈ xU Y α (fun j => h.j (i j)) → CoordAt Y h ν m₀ V pb α i T a b z w₁ →
      CoordAt Y h ν m₀ V pb α i T a b z w₂ → w₁ = w₂ := by
    intro i Z a b z w₁ w₂ hm h₁ h₂
    unfold CoordAt at h₁ h₂
    rw [h₁, gs_unit a z _ hm] at h₂
    exact add_left_cancel ((Units.isUnit _).mul_left_cancel h₂)
  have hover : ∀ i i', resG A₀.left (inf_le_left : Oi i ⊓ Oi i' ≤ Oi i) (f i) =
      resG A₀.left (inf_le_right : Oi i ⊓ Oi i' ≤ Oi i') (f i') := by
    intro i i'
    refine ext_lift Y m₀ fun Z a b w z hz => ?_
    rw [gs_res b z inf_le_left hz, gs_res b z inf_le_right hz]
    have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => (memO i (b z)).1 hz.1 j
    have hi' : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i' j) := fun j => (memO i' (b z)).1 hz.2 j
    have h₁ := hfree T hT₁ hT₂ Z a b w z i i' hi hi' _ (hCA i Z a b w z hz.1)
    exact uniq i' Z a b z _ _ (hF.mem_chart hD hV hT₁ w hi').2 h₁ (hCA i' Z a b w z hz.2)
  have hcov : ⨆ i, Oi i = ⊤ := by
    refine eq_top_iff.2 fun p _ => ?_
    have ex : ∀ j, ∃ k, m₀ (T j p) ∈ V k := fun j => by
      have : m₀ (T j p) ∈ (⨆ k, V k) := by rw [hC.2.1]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    choose i hi using ex
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (memO i p).2 hi⟩
  obtain ⟨c, hc⟩ := exists_const_of_glue A₀ hab Oi f hcov hover
  refine ⟨c, fun T' hT'₁ hT'₂ Z a b w z i hi => ?_⟩
  obtain rfl : T' = T := funext fun j =>
    hF.pull.1.hom_ext ((hT'₁ j).trans (hT₁ j).symm) ((hT'₂ j).trans (hT₂ j).symm)
  have hz : b z ∈ Oi i := (memO i (b z)).2 hi
  rw [← hc Z b z i hz]
  exact hCA i Z a b w z hz

end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulZarhinDiagonalClassEqForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zClsDiag_comp_idPow {S : Scheme.{0}} {B Y : Over S} [GrpObj B] (b : Y ⟶ B) (n : ℕ) :
    b ≫ (𝟙 B) ^ n = b ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem zClsDiag_nsmul_evc {S : Scheme.{0}} {A B Y : Over S} [GrpObj A] [GrpObj B]
    {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (hs : IsDual B A (swap Q)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) :
    n • evc hQ a b = evc hQ a (b ^ n) := by
  induction n with
  | zero => rw [zero_smul, pow_zero, ← evc_swap hQ hs.isLB, hs.additive.evc_one hs.isLB]
  | succ n ih =>
    rw [succ_nsmul, ih, pow_succ, ← evc_swap hQ hs.isLB (b ^ n * b), (isAdditive_iff hs.isLB).1 hs.additive,
      evc_swap hQ hs.isLB, evc_swap hQ hs.isLB]

theorem zClsDiag_key {h M d : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)
    {B : Over S} [GrpObj B] [IsCommMonObj B] {Q : LB (c.A ⊗ B).left} {la : c.A ⟶ B} {mu : B ⟶ c.A}
    (hZ : ZData c d B Q la mu) {Y : Over S} (a : Y ⟶ c.A) (b : Y ⟶ B) :
    d • pull (lift a b).left (cls Q hZ.2.1.isLB) = pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := by
  have hQ := hZ.2.1.isLB
  have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
    (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hZ.2.2.2.2.2.2.2
  show d • evc hQ a b = _
  rw [e, pull_evc, lift_fst, lift_snd_assoc, Category.assoc, hZ.2.2.2.2.2.2.1, zClsDiag_comp_idPow,
    zClsDiag_nsmul_evc hQ hZ.2.2.1]

end GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zClsDiag_sum_sig {M : Type*} [AddCommMonoid M] (F : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → M) :
    ∑ kl : Fin 8 × Fin 8, F (sig kl.1) (sig kl.2) = ∑ s, ∑ t, F s t := by
  let e : Fin 8 ≃ Fin 4 ⊕ Fin 4 := Equiv.ofBijective sig (by decide)
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_congr rfl fun k _ => Equiv.sum_comp e (F (sig k))).trans (Equiv.sum_comp e fun s => ∑ t, F s t)

theorem nsmul_pull_diag_zCls : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → d • GlobalTheory.CechPic.pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left (GlobalTheory.ZarhinFam.zCls c.A B c.isLB hZ.2.1.isLB d mu) = ∑ kl : Fin 8 × Fin 8, GlobalTheory.ZarhinFam.zW d kl.1 kl.2 • GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.zpr c.A B mu kl.1) (GlobalTheory.ZarhinFam.zpr c.A B mu kl.2)).left (GlobalTheory.CechPic.cls c.P c.isLB) := by
  intro h M d S t c B _ _ Q la mu hZ _
  let F : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → Pic (Zob c.A B).left := fun s u =>
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 s u •
      pull (lift (Sum.elim (pa c.A B) (fun j => pb c.A B j ≫ mu) s)
        (Sum.elim (pa c.A B) (fun j => pb c.A B j ≫ mu) u)).left (cls c.P c.isLB)
  rw [show (∑ kl : Fin 8 × Fin 8, zW d kl.1 kl.2 • pull (lift (zpr c.A B mu kl.1) (zpr c.A B mu kl.2)).left
      (cls c.P c.isLB)) = ∑ kl : Fin 8 × Fin 8, F (sig kl.1) (sig kl.2) from rfl, zClsDiag_sum_sig]
  simp only [F, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, zero_smul,
    Finset.sum_const_zero, add_zero]
  simp only [zCls, map_add, map_sum, map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc, Category.id_comp]
  have hk : ∀ {Y : Over S} (a : Y ⟶ c.A) (b : Y ⟶ B), d • pull (lift a b).left (cls Q hZ.2.1.isLB) =
      pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := fun a b => zClsDiag_key c hZ a b
  have hk' : ∀ {Y : Over S} (z : ℤ) (a : Y ⟶ c.A) (b : Y ⟶ B), d • z • pull (lift a b).left (cls Q hZ.2.1.isLB) =
      z • pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := fun z a b => by rw [smul_comm, hk]
  simp only [smul_add, Finset.smul_sum, hk, hk', Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
    zero_add, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, one_smul, Finset.sum_add_distrib, mul_smul, two_smul, natCast_zsmul]
  abel

end GlobalTheory.ZarhinFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSeparationRegularDeterminant
section
set_option autoImplicit false

noncomputable section

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

namespace GlobalTheory.OrbitSep

theorem val_ofSec_ne_zero {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F) {B : LB X} (θ : B.Sec) (z : Sp ℂ ⟶ X)
    (k : B.ι) (hk : ⊤ ≤ z ⁻¹ᵁ B.U k) (hz : ∀ s, z s ∈ nonzeroLocus θ) :
    H0.val z k le_top hk (H0.ofSec p ⊤ θ) ≠ 0 := by
  refine (H0.val_ofSec z k le_top hk θ).trans_ne ?_
  have h : ⊤ ≤ z ⁻¹ᵁ X.basicOpen (θ.f k) := fun s hs =>
    (X.mem_basicOpen _ _ (hk hs)).2 ((isUnit_ger_iff θ (hk hs)).2 (hz s))
  rw [← TangentOrigin.evalPt_res z (X.basicOpen_le _) hk h]
  exact ((X.toRingedSpace.isUnit_res_basicOpen (θ.f k)).map _).ne_zero

theorem exists_chart_pt {X : Scheme.{0}} {B : LB X} (hB : B.IsLB) (z : Sp ℂ ⟶ X) : ∃ k, ⊤ ≤ z ⁻¹ᵁ B.U k := by
  obtain ⟨k, hk⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hB (z (IsLocalRing.closedPoint ℂ))
  refine ⟨k, fun s _ => ?_⟩
  obtain rfl : s = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hk

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := GlobalTheory.HSApp.cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih => rw [succ_nsmul, GlobalTheory.HSApp.cls_common_add C, ih, succ_nsmul]

set_option maxHeartbeats 2000000 in

theorem separate_orbit (hP2 : Hypotheses2) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSg : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS)
    (hLie : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7}
    {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂))
    {I : Ideal (𝓞 D.host.E)} {g : ℕ} (hI : NeatPrime I g ((T.Q.Dw j).p + (T.Q.Dw j).q)) (hM : Y.d.l₂.Mb ≤ I)
    (hS : ∀ γ ∈ S, UnipAt I γ) (s : ℕ)
    (hs : (T.Q.Dw j).p + (T.Q.Dw j).q + ((T.Q.Dw j).dim + 1).choose 2 + 1 ≤ s) (Z : Comp Y.d.Xo₂ Y.d.c₂) :
    ∃ y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ, LiesOn Z y ∧
      ∀ [Fintype {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)}]
        (a : {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)} → ℂ),
        (∀ u ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) ((s : ℤ) • hodgeWt (T.Q.Dw j)) 0),
          ∑ h, a h * evR Y.d.Xo₂ Y.d.c₂ u (move Y.d.Xo₂ Y.d.c₂ (h.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) = 0) → a = 0 := by
  have hP : Hypotheses₂ := GlobalTheory.T.stronger_published_hypotheses_imply hP2
  have hA : Y.d.l₂.A = 1 := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := hA ▸ Nat.coprime_one_left _
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hdim : 1 ≤ (T.Q.Dw j).dim := Nat.mul_pos (Nat.mul_pos (by omega) hp) hq
  have hfl : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) := by
    refine Nat.mul_pos (by omega) ?_
    exact Nat.choose_pos (by omega)
  obtain ⟨TF⟩ := GlobalTheory.T.toroidal_flag_nonempty hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hfl
  have hF := hY.geo
  have hV := GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hF
  obtain ⟨hint, hsm, hpr, hgc, hsurj, hnorm, hgen⟩ := GlobalTheory.T.compactificationComponent_integral_smooth_projective _ _ _ _ _ _ TF Z hF
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_complexFramedPoint_over_componentGenericPoint _ _ _ _ Y.d.Xo₂ Y.d.c₂ Z
  have hyZ : LiesOn Z y := fun s => hy s ▸ (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)).mem
  refine ⟨y, hyZ, fun a ha => ?_⟩
  have lift : ∀ w : FrPt Y.d.Xo₂ Y.d.c₂ ℂ, LiesOn Z w → ∃ v : Sp ℂ ⟶ V₀ TF.Y Z, v ≫ i₀ TF.Y Z = ptF w := fun w hw =>
    ⟨IsOpenImmersion.lift (i₀ TF.Y Z) (ptF w) (by
      rintro _ ⟨s, rfl⟩
      exact ⟨⟨_, (j_mem_barComp Z _).2 (hw s)⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨v₁, hv₁⟩ := lift y hyZ
  choose v hv using fun h : {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)} => lift _ h.2
  obtain ⟨Γ, ρ, hΓ, hρ, hmem⟩ := GlobalTheory.T.componentStabilizer_acts_by_levelChange _ _ _ _ _ _ TF.Y Z hpq hA S
  obtain ⟨X', W, φ, ℓ, ρ', q, sW, hint', n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ :=
    GlobalTheory.T.equivariant_normal_projective_compactification Y.d.c₂.F _ _ (s₀ TF.Y Z) (j₀ TF.Y Z) Γ ρ hpr ⟨v₁ (IsLocalRing.closedPoint ℂ)⟩ hnorm hρ.1
  obtain ⟨δ, hδ, eδ, hlin⟩ := GlobalTheory.T.exists_line_bundle_descends_hodge hP2 _ _ _ _ _ _ TF Z hpq hA hF
  obtain ⟨N, hN, eN⟩ := GlobalTheory.T.exists_descent_linearised_lineBundle_finiteGroup_quotient Y.d.c₂.F X' W q sW Γ ρ' _ _ (n7 ▸ n2) n6
    (hlin I g hI hM Γ Γ.subtype ρ (fun γ => hS _ (hΓ γ.2)) hρ X' φ ℓ ρ' n1 n2 n3 n4 n5)
  let K := CanonLB.all (s₀ TF.Y Z) (T.Q.Dw j).dim
  obtain ⟨κ, hκ, eκ, θ, hθ⟩ := GlobalTheory.T.exists_toroidalCanonicalBundle_weight_line _ _ _ _ _ _ TF Z hpq hF K
  set m := ((T.Q.Dw j).dim + 1).choose 2 + 1 with hm
  obtain ⟨t, rfl⟩ : ∃ t, s = m + t := Nat.exists_eq_add_of_le (by omega)
  obtain ⟨N', hN', eN'⟩ := cls_surj (t • cls δ hδ - cls κ hκ)
  obtain ⟨B, hB, eB⟩ := cls_surj (m • cls δ hδ + cls N' hN')
  have C := common₀ TF.X Z
  have nef : ∀ (L : LB (X₀ TF.Y Z)) (hL : L.IsLB) (w : AllWt.Weight (T.Q.Dw j)), GapGe 0 w →
      CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z w) (isLB_L₀ TF.X Z w) →
      (letI := algebraΓOfHom (s₀ TF.Y Z); IsNef Y.d.c₂.F L) := fun L hL w hw e =>
    GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective _ _ _ _ _ _ L hL _ _ (π₀_s₀ TF.X Z) hpr hV.2.1 hsurj e
      (GlobalTheory.T.nef_line_bundle_weight_gap hP hQ.nef hLie _ _ _ _ _ _ TF Z hF w hw)
  have ens : ∀ n : ℕ, cls (L₀ TF.X Z ((n : ℤ) • hodgeWt (T.Q.Dw j))) (isLB_L₀ TF.X Z _) =
      n • cls (L₀ TF.X Z (hodgeWt (T.Q.Dw j))) (isLB_L₀ TF.X Z _) := fun n => by
    rw [natCast_zsmul]; exact cls_nsmul (common₀ TF.X Z) n _
  have nefN' := nef N' hN' ((t : ℤ) • hodgeWt (T.Q.Dw j) - kapBase _) (gapGe_sub_kapBase _ (by omega)) (by
    have h := GlobalTheory.HSApp.cls_common_add (common₀ TF.X Z) ((t : ℤ) • hodgeWt (T.Q.Dw j) - kapBase _) (kapBase _)
    rw [sub_add_cancel] at h
    rw [eN', map_sub, map_nsmul, eδ, eκ, ← ens, sub_eq_iff_eq_add]
    exact h)
  have hKB := isLB_tens K.isLB hB
  have hθB := LB.isLB_div hκ K.isLB
  obtain ⟨Φ, hΦ, hval⟩ := GlobalTheory.T.exists_cuspRule_of_boundaryVanishing_componentSection D T j Y e o hY hf Z TF (((m + t : ℕ) : ℤ) • hodgeWt (T.Q.Dw j)) _
    (isLB_tens hθB hKB) (by
      rw [cls_tens hθB hKB, cls_div hκ K.isLB, cls_tens K.isLB hB, eB, eN', ens, ← eδ, ← map_nsmul]
      refine congrArg _ ?_
      have key : ∀ (A : Type 1) [AddCommGroup A] (a b k : A) (m t : ℕ),
          b - k + (k + (m • a + (t • a - b))) = (m + t) • a := fun A _ a b k m t => by
        rw [add_nsmul, ← add_assoc, sub_add_cancel, add_left_comm, add_sub_cancel]
      exact key _ _ _ _ _ _)
  choose k hk using fun h => exists_chart_pt hKB (v h ≫ j₀ TF.Y Z)
  choose k' hk' using fun h => exists_chart_pt hθB (v h ≫ j₀ TF.Y Z)
  choose lam hlam using fun h => hval _ (v h) (hv h) (k' h, k h) (fun s hs => ⟨hk' h hs, hk h hs⟩)
  have hc : ∀ h, H0.val (v h ≫ j₀ TF.Y Z) (k' h) le_top (hk' h) (H0.ofSec (s₀ TF.Y Z) ⊤ θ) ≠ 0 := fun h =>
    val_ofSec_ne_zero _ θ _ _ _ fun s => hθ ▸ ⟨v h s, rfl⟩
  have hvρ : ∀ h, v h = v₁ ≫ (ρ ⟨h.1, hmem _ h.1.2 y hyZ h.2⟩).hom := fun h => by
    rw [← cancel_mono (i₀ TF.Y Z), hv, Category.assoc, hρ.2 _ ℂ y v₁ hv₁]; rfl
  have h1 : LiesOn Z (move Y.d.Xo₂ Y.d.c₂ ((1 : S) : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) := by
    rw [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']; exact hyZ
  have key := GlobalTheory.T.sections_separate_quotient_generic_fibre_descends hP2.q15 hQ.nef hP2.q16 Y.d.c₂.F (algebraMap _ ℂ) (X₀ TF.Y Z) X' W (V₀ TF.Y Z) (s₀ TF.Y Z) _ φ q sW
    (j₀ TF.Y Z) ℓ hpr hgc hdim n2 n8 n10 n11 n7 inferInstance n3 n4 K δ N' B hδ hN' hB N hN m eN
    (nef δ hδ _ gapGe_hodgeWt eδ) (GlobalTheory.T.descended_bundle_hodge_class hP2 hG hQ hSg hKS _ _ _ _ _ _ TF Z hp hq hF δ hδ eδ) nefN' (by omega) eB _ v
    (fun h h' e => ?_) (fun h => ?_) (fun h h' => ?_) ⟨⟨1, h1⟩, fun s => hgen _ ?_⟩ k hk
    (fun h => a h * (lam h * H0.val (v h ≫ j₀ TF.Y Z) (k' h) le_top (hk' h) (H0.ofSec (s₀ TF.Y Z) ⊤ θ))) fun u => ?_
  · funext h
    exact (mul_eq_zero.1 (congrFun key h)).resolve_right (mul_ne_zero (lam h).ne_zero (hc h))
  · have e' := (hv h').symm.trans (e ▸ hv h)
    have e₂ : move Y.d.Xo₂ Y.d.c₂ (h'.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y =
        move Y.d.Xo₂ Y.d.c₂ ((h.1 * h'.1⁻¹ : S) : LevelAut (T.Q.Dw j) Y.d.l₂)
          (move Y.d.Xo₂ Y.d.c₂ (h.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) := by
      rw [← LevDesc.move_mul hpq hA']; simp
    rw [e₂] at e'
    have := GlobalTheory.T.levelAutomorphism_unipotent_fixes_complexPoint_eq_one _ _ _ _ _ _ hpq hA I g hI hM _ (hS _ (h.1 * h'.1⁻¹).2) _ e'
    exact Subtype.ext (mul_inv_eq_one.1 (Subtype.ext this))
  · have e₁ : TF.Y.j ≫ TF.Y.s = pullback.snd _ _ := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over]
      exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
    rw [← Category.assoc (j₀ _ _), j₀_ι, Category.assoc, e₁, ← Category.assoc, hv]
    exact pullback.lift_snd _ _ _
  · rw [hvρ h, hvρ h', Category.assoc, Category.assoc, reassoc_of% n5, reassoc_of% n5, n6.comp_eq, n6.comp_eq]
  · change (v ⟨1, h1⟩ ≫ i₀ TF.Y Z) s = _
    rw [hv]
    simp only [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']
    exact hy s
  · let P := tensChart hθB hKB
    have hu := ha _ (hΦ (P.mul (H0.ofSec (s₀ TF.Y Z) ⊤ θ) u) fun x hx => ?_)
    · rw [← hu]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [hlam, mul_assoc, mul_assoc]
      exact congrArg (fun x => a h * (lam h * x)) (P.val_mul _ _ (k' h, k h) _ le_top (hk' h) (hk h) _).symm
    · obtain ⟨τ, ha', hb', hc'⟩ := P.cover x
      have hu := (isUnit_ger_iff _ hc').2 hx
      rw [ger_toSec, P.germ_mul _ _ τ x _ ha' hb' hc', H0.germ_ofSec] at hu
      exact hθ ▸ (isUnit_ger_iff θ ha').1 (isUnit_of_mul_isUnit_left hu)

end GlobalTheory.OrbitSep

namespace GlobalTheory.OrbitSep

open Formalism.MainNotions Formalism.L2.Theta GlobalTheory.DegVal GlobalTheory.DegCmp GlobalTheory.BadCount

theorem exists_cusp_levDet_regular : Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ S u * f = 0 → f = 0 := by
  classical
  intro hP2 hG hQ hSg hKS hLie D T hT j hp hq hf hj Y e o hY _ hg fr S hS
  have hA : Y.d.l₂.A = 1 := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := hA ▸ Nat.coprime_one_left _
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hdat := hT.pins.2.2.2 j hj
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hdat.1, hdat.2.1]; exact Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hT.pins.2.1.1]
  obtain ⟨I, g, hI, hMb, hU⟩ := GlobalTheory.T.exists_neatPrime_levelAutSubgroup_unipotent D _ (T.Q.Dw j) Y.d.l₂ ⟨_, hM⟩ (hr ▸ hg) fr S hS
  have hs : (T.Q.Dw j).p + (T.Q.Dw j).q + ((T.Q.Dw j).dim + 1).choose 2 + 1 ≤ cZeroN D j := by
    have := (cZeroN_isLeast D j).1.2.1
    rw [hr, Datum.dim, GlobalTheory.FlagDim.finrank_host_div_two, hdat.1, hdat.2.1]
    omega
  choose y hyZ hy using separate_orbit hP2 hG hQ hSg hKS hLie Y hY hf hp hq S hI hMb hU _ hs
  have : Finite (Comp Y.d.Xo₂ Y.d.c₂) := CompFin.finite_comp _ _
  let G := wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0
  let ev : Comp Y.d.Xo₂ Y.d.c₂ → Y.V G →ₗ[Y.d.c₂.F] (S → ℂ) := fun Z => LinearMap.pi fun h =>
    evalL (K := Y.d.c₂.F) (fun R _ _ => FrPt Y.d.Xo₂ Y.d.c₂ R) (fun φ y z => FrMap φ y z)
      (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ (y Z)) ∘ₗ (Y.V G).subtype
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_vector_groupDeterminants_ne_zero Y.d.c₂.F (Y.V G) S _ ev
    (fun Z => {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ (y Z))}) (fun _ h => h.1)
    (fun Z => (AllWt.suppOn Z).comap (Y.V G).subtype)
    (fun Z => ⟨⟨1, by rw [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']; exact hyZ Z⟩, rfl⟩)
    (fun Z v hv h hh => hv ℂ _ ((AllWt.liesOff_iff Z _).2 fun h' => hh ⟨⟨h, h'⟩, rfl⟩))
    (fun Z a ha => hy Z a fun u hu => ha ⟨u, hu.1⟩ hu.2)
  have hu' := AllWt.cuspW_le_secZ _ u.2
  refine ⟨u, u.2, GlobalTheory.T.integerExponentSection_mul_eq_zero_imp_eq_zero _ _ _ _ _ _ _ _ (LevDesc.levDet_mem_secZ hpq hA' hu') fun Z => ⟨y Z, hyZ Z, ?_⟩⟩
  have ht := GlobalTheory.FlagTan.fromTest_of_isLocalRing (y Z)
  let χ : Rul Y.d.Xo₂ Y.d.c₂ →+* ℂ :=
    { toFun := fun f => evR Y.d.Xo₂ Y.d.c₂ f (y Z)
      map_one' := evalAt_one _ _ _ ht
      map_mul' := fun f g => evalAt_mul _ _ f g _
      map_zero' := evalAt_zero _ _ _
      map_add' := fun f g => evalAt_add _ _ f g _ }
  have e₁ := χ.map_det (LevDesc.levMat Y.d.Xo₂ Y.d.c₂ S u)
  refine fun h0 => hu Z ?_
  rw [← h0]
  refine Eq.trans ?_ (e₁.symm.trans ?_)
  · congr 1
    ext h g
    exact (GlobalTheory.LevelKeeps.evR_transl hpq hA' _ hu' (y Z)).symm
  · change χ _ = χ _
    unfold levDet
    congr!

end GlobalTheory.OrbitSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanDeRhamHomologyRankTwoG
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PeriodSpan

theorem main : PSpan := by
  intro A _ g hA _ L u P hP
  refine GlobalTheory.T.period_map_span_top_and_finrank_from_cech_periods A g L u hA P fun c => ?_
  exact GlobalTheory.T.crystalline_period_eq_cechDeRham_period A g L u c.1
    { toFun := fun l => P l c, map_zero' := by simp, map_add' := fun x y => by simp }
    _ (fun _ => rfl) (hP c)

end GlobalTheory.PeriodSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoAnyRingStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_degree_two_any_ring : PrimitiveExtendedDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primE2_any_ring | exact GlobalTheory.Obs.primE2_any_ring | (intros; apply GlobalTheory.Obs.primE2_any_ring <;> assumption)
end

