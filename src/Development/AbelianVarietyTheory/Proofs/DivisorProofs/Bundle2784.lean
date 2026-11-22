import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.LinearRestriction.ResPullUVal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreValueEqUnitMulLeadingFourierTerm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.RedVal

theorem commGroup_fourFactor_exponents_cancel_pow {M : Type} [CommGroup M] (a b c d : M) (k : ℕ) :
    a ^ ((k:ℤ)-1) * b ^ (1:ℤ) * c ^ (-1:ℤ) * d ^ (1:ℤ) * (b ^ (-1:ℤ) * c ^ (1:ℤ) * a ^ (1:ℤ) * d ^ (-1:ℤ)) = a ^ k := by
  rw [zpow_sub_one]; simp only [zpow_neg, zpow_one, zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem gs_pow' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {Ix : Type} (s : Finset Ix)
    (a : Ix → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem sval_zero_of_van {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {k : ℕ} (a : D'.X) (b : D.SecB k (hD.xe a))
    (b' : D'.SecB k a) (hb : PullB hD a b b') (I : Ideal R) (e : ℕ) (hv : VanMod I b e) {Z : Scheme.{0}}
    (r : Z ⟶ D'.P.A.left) (h' : Z ⟶ pullback D.P.A.hom (thick R I e))
    (hh : h' ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
    (z : Z) {J₁ : (Z ⟶ D'.P.A.left) → D'.P.L.ι} (hJ₁ : Good D'.P.L z J₁) : sval b' r z J₁ = 0 := by
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.P.isLB z
  have E := hb Z r z (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
    (fun κ => J₁ (r ≫ D'.famφB a κ)) (fun κ => hJ' _) (fun κ => hJ₁ _)
  have h0 : gs (r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) z
      (LB.wchart D.P.L (D.famφB (hD.xe a))
        (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))))
      (b.f (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) = 0 := by
    rw [← hh]
    by_cases hm : (h' ≫ pullback.fst D.P.A.hom (thick R I e)) z ∈ LB.wchart D.P.L (D.famφB (hD.xe a))
        (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
    · exact (gs_pull h' _ z _ hm _).symm.trans ((congrArg (gs h' z _) (hv _)).trans (gs_zero' _ _ _))
    · unfold gs
      exact dif_neg hm
  rw [h0] at E
  exact (Units.mul_right_eq_zero _).1 E.symm

theorem expand_eval {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing W)))} {G : Over (Spec (CommRingCat.of W))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {k : ℕ} (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hX : U.ExpandsAt 0 k σ f) {Z : Scheme.{0}} (g : Z ⟶ (thickObj W I 0 G).left) (z : Z)
    {J₁ : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} {J₂ : (Z ⟶ G.left) → U.LG.L.ι}
    (hJ₁ : Good D.toPre.P.L z J₁) (hJ₂ : Good U.LG.L z J₂) (x : D.toPre.X)
    (hv : ∀ a, a ≠ x → sval (f a) (g ≫ (U.gt 0).pG.left) z J₁ = 0) :
    (gm g z _ ((U.w 0).s (fun _ => J₁ (g ≫ (U.gt 0).pG.left),
        fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left)))).val ^ k *
      sval σ (g ≫ (fstG I 0 G).left) z J₂ =
    sval (f x) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t x) g z J₁).val := by
  obtain ⟨S, hS0, hS⟩ := hX
  let p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
    (fun _ => J₁ (g ≫ (U.gt 0).pG.left), fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left))
  let j₁ : Fin 1 → U.LG.L.ι := fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left)
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun a κ => J₁ ((g ≫ (U.gt 0).pG.left) ≫ D.toPre.famφB a κ)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun a κ => J₁ (g ≫ D.toPre.Oφ (U.gt 0).pG a κ)
  have hcoh : CohAll D.toPre.P.L
      (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
        (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
          (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2)))
      (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    have key : ∀ i, (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) i =
        J₁ (g ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2))) i) := by
      rintro (_ | (_ | _))
      · rfl
      · simp only [Sum.elim_inl, Sum.elim_inr, jf, Category.assoc]
      · rfl
    intro a b e
    rw [key a, key b, e]
  have E := hS p j₁ jf jt rfl hcoh
  have hA : g z ∈ (LB.div (D.toPre.P.L.pull (U.gt 0).pG.left) (U.LG.L.pull (fstG I 0 G).left)).U p :=
    ⟨mem_pull.2 (hJ₁ (g ≫ (U.gt 0).pG.left)), mem_pull.2 (hJ₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left))⟩
  have hB : g z ∈ (fstG I 0 G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁ :=
    hJ₂.mem (fun _ : Fin 1 => 𝟙 G.left) (g ≫ (fstG I 0 G).left)
  have hC : ∀ a, g z ∈ (U.gt 0).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB a) (jf a) := fun a =>
    hJ₁.mem (D.toPre.famφB a) (g ≫ (U.gt 0).pG.left)
  have hD' : ∀ a, g z ∈ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt 0).pG a) (jt a) := fun a =>
    hJ₁.mem (D.toPre.Oφ (U.gt 0).pG a) g
  have hm : g z ∈ U.expW 0 p j₁ S jf jt := by
    refine ⟨⟨hA, hB⟩, ?_⟩
    exact Finset.inf_induction (p := fun V : (thickObj W I 0 G).left.Opens => g z ∈ V) trivial
      (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) (fun a _ => ⟨hC a, hD' a⟩)
  have E' := congrArg (gs g z (U.expW 0 p j₁ S jf jt)) E
  rw [gs_mul g z _ hm, gs_pow' g z _ hm, gs_unit g z _ hm, gm_res g z _ hm, gs_res g z _ hm, gs_sum' g z _ hm] at E'
  erw [gs_pull g (fstG I 0 G).left z _ hB] at E'
  refine E'.trans ?_
  have hterm : ∀ a : S, gs g z (U.expW 0 p j₁ S jf jt)
      (((thickObj W I 0 G).left.presheaf.map (homOfLE (U.expW_le_f 0 p j₁ jf jt a.2)).op).hom
        (((U.gt 0).pG.left.app _).hom ((f a.1).f (jf a.1))) *
        (res (U.expWeight_le_chart_weight 0 p j₁ jf jt a.2) (((U.gt 0).t a.1).s (jt a.1))).val) =
      sval (f a.1) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t a.1) g z J₁).val := fun a => by
    rw [gs_mul g z _ hm, gs_res g z _ hm, gs_unit g z _ hm]
    erw [gm_res g z (U.expWeight_le_chart_weight 0 p j₁ jf jt a.2) hm, gs_pull g (U.gt 0).pG.left z _ (hC a.1)]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [Finset.sum_attach S (fun a => sval (f a) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t a) g z J₁).val)]
  refine Finset.sum_eq_single x (fun b _ hb => by rw [hv b hb, zero_mul]) (fun hx => ?_)
  have h0 : sval (f x) (g ≫ (U.gt 0).pG.left) z J₁ = 0 :=
    (gs_pull g (U.gt 0).pG.left z _ (hC x) _).symm.trans ((congrArg (gs g z _) (hS0 x hx _)).trans (gs_zero' _ _ _))
  rw [h0, zero_mul]

theorem closedFibre_val : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left) (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' → GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' → IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  intro R _ _ _ _ D C Y W _ _ _ T Z p' y g ξ' hg hpt hpull k u z J J' hJ hJ'
  subst hg
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.TorusCoord.exists_good' T.D'.toPre.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.TorusCoord.exists_good' T.U.LG.isLB z
  set Fm := T.hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf T.φ) with hFm
  set r := g ≫ (T.U.gt 0).pG.left with hr
  set p' := g ≫ (fstG (maximalIdeal W) 0 T.G).left with hp'
  let Gw : (Z ⟶ T.D'.toPre.P.A.left) → (Z.presheaf.stalk z)ˣ := fun f => gw T.hD.w f z (J' (f ≫ Fm)) (J₁ f)
  let W0 := gm g z _ ((T.U.w 0).s (fun _ => J₁ (g ≫ (T.U.gt 0).pG.left), fun _ => J₂ (p' ≫ 𝟙 T.G.left)))
  let uG : Γ(T.G.left, ⊤)ˣ := Units.map
    (T.G.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom).toMonoidHom u
  refine ⟨gm p' z ⊤ uG * gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k * (W0 ^ k)⁻¹ * (Gw r ^ k)⁻¹, ?_⟩
  intro α b τ F σ hτ hL hE
  obtain ⟨x, rfl⟩ := T.hD.xe.surjective α
  obtain ⟨σ', f', hC, hP, hX⟩ := hE

  have hb' : ξ'.b.left = r := hpt.1
  have hq : (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).b.left = y ≫ Y.q.left := by
    have h := (Y.rep.1 (Over.mk (y ≫ Y.H.hom)) Y.H (Over.homMk y rfl) (𝟙 _)).1
    rw [Category.comp_id] at h
    exact h
  have hrF : r ≫ Fm = y ≫ Y.q.left := by
    have h := hpull.1
    rw [hb'] at h
    exact h.trans ((Category.id_comp _).trans hq)
  haveI := T.loc
  have hmm : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal W ^ (0 + 1)).comap T.φ := by
    simp only [zero_add, pow_one]
    intro a ha
    exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit T.φ a hu)
  let qm : R ⧸ maximalIdeal R ^ (0 + 1) →+* W ⧸ maximalIdeal W ^ (0 + 1) := Ideal.quotientMap _ T.φ hmm
  have hsq : thick W (maximalIdeal W) 0 ≫ specOf T.φ =
      Spec.map (CommRingCat.ofHom qm) ≫ thick R (maximalIdeal R) 0 := by
    simp only [thick, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have hcond : (r ≫ Fm) ≫ D.toPre.P.A.hom = (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫
      Spec.map (CommRingCat.ofHom qm)) ≫ thick R (maximalIdeal R) 0 := by
    have e1 : Fm ≫ D.toPre.P.A.hom = T.D'.toPre.P.A.hom ≫ specOf T.φ := by
      rw [hFm, Category.assoc, pullback.condition, ← Category.assoc]
      congr 1
      exact Over.w T.hD.e.hom
    have e2 : r ≫ T.D'.toPre.P.A.hom =
        g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0 := by
      rw [hr, Category.assoc, Over.w (T.U.gt 0).pG]; rfl
    rw [Category.assoc, e1, ← Category.assoc, e2, Category.assoc, Category.assoc, hsq, Category.assoc,
      Category.assoc]
  let h' := pullback.lift (r ≫ Fm) _ hcond
  have hh : h' ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0) =
      r ≫ T.hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf T.φ) := pullback.lift_fst _ _ _
  have hvan : ∀ a, a ≠ x → sval (f' a) r z J₁ = 0 := fun a ha =>
    sval_zero_of_van T.hD a (F.f (T.hD.xe a)) (f' a) (hP a) (maximalIdeal R) 0
      (hL.2 _ (fun e => ha (T.hD.xe.injective e))) r h' hh z hJ₁
  have E1 := expand_eval T.U.toUnifPre σ' f' (hX 0) g z hJ₁ hJ₂ x hvan
  have E2 := hC Z p' z J J₂ hJ hJ₂
  have E3 := hτ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl) z J' hJ'
  have E4 := hP x Z r z (fun κ => J' ((r ≫ T.D'.toPre.famφB x κ) ≫ Fm)) (fun κ => J₁ (r ≫ T.D'.toPre.famφB x κ))
    (fun κ => hJ' _) (fun κ => hJ₁ _)
  rw [hL.1] at E4
  have E4' : sval b (y ≫ Y.q.left) z J' = (∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ).val *
      sval (f' x) r z J₁ := by
    have hfam : ∀ κ, (r ≫ Fm) ≫ D.toPre.famφB (T.hD.xe x) κ = (r ≫ T.D'.toPre.famφB x κ) ≫ Fm := fun κ => by
      have e := GlobalTheory.ExpGTrans.famφB_pull T.hD x κ
      rw [← hFm] at e
      exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)
    rw [sval_of b (y ≫ Y.q.left) z J' (fun κ => J' ((r ≫ T.D'.toPre.famφB x κ) ≫ Fm)) (fun κ => by
      rw [← hrF, hfam])]
    rw [← hrF]
    exact E4
  have E5 : val ((T.U.gt 0).t x) g z J₁ = val (ξ'.s x) (𝟙 Z) z J₁ := by
    rw [val_corr hJ₁ (hpt.2 x) (𝟙 Z), val_pull hJ₁, Category.id_comp]
  obtain ⟨hψ, hM⟩ := hpull.2 x
  have E6 := ReciprocityTheory.ChartRestriction.G.Out.OLinPf.ILin.val_maps _ T.hD.w _ DegPre.gtε _ (𝟙 Z) hψ _ _ hM (𝟙 Z) z J₁ J' hJ₁ hJ'
  have hO := (GlobalTheory.TorusCoord.comp_eq_of_left ξ'.b (𝟙 T.D'.toPre.P.A) (𝟙 Z) r (by rw [hb']; simp)).1 x
  have Gprod : (∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ) *
      (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ) = Gw r ^ k := by
    simp only [hO, Fin.prod_univ_four]
    simp only [DegPre.famφB, DegPre.Oφ, DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Over.id_left, Category.comp_id]
    exact commGroup_fourFactor_exponents_cancel_pow _ _ _ _ k
  have E3' : sval τ y z J' = sval b (y ≫ Y.q.left) z J' *
      (val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) (𝟙 Z) z J').val := E3
  have E6' : val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) (𝟙 Z) z J' =
      (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ) * val ((T.U.gt 0).t x) g z J₁ := by
    rw [E5]
    exact (congrArg (fun q => val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) q z J')
      (Category.comp_id (𝟙 Z)).symm).trans E6
  have hu : gs p' z ⊤ (scal T.G.hom u.val) = (gm p' z ⊤ uG).val := gs_unit p' z ⊤ trivial uG
  have hW : ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val * W0.val ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, Units.inv_mul]
  have hG : ((Gw r ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val *
      ((∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ).val *
        (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ).val) = 1 := by
    rw [← Units.val_mul, Gprod, Units.inv_mul]
  rw [E2, hu, E3', E4', E6']
  simp only [Units.val_mul]
  linear_combination (-((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val *
      ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val * sval (f' x) r z J₁ * (val ((T.U.gt 0).t x) g z J₁).val)) * hG -
    ((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val * sval σ' p' z J₂) * hW +
    ((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val *
      ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val) * E1

end GlobalTheory.Mum.RedVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetGaloisDescent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.DRLine

theorem eigK_finrank_eq_one : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (σ : E →+* FractionRing R),
      Module.finrank (FractionRing R) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ) = 1 := by
  intro hPC hDR hDC E _ _ _ _ I _ d φ hφ 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hcmF hα j hj φK hφK n eH σ
  classical
  choose α hαM hαp hαU using hα
  let T : orderC (condQ 𝔣 Q) → Module.End ℂ (HdR X.A) := fun a ↦ haveI := hαM a; push (dp0 ℂ) (𝟙 _) (α a)
  obtain ⟨B, hB⟩ := GlobalTheory.T.de_rham_basis_base_change hDR E (condQ 𝔣 Q) 𝔠 R X₀ X p cm hpull n eH
  have hTB : ∀ a i, T a (B i) = ∑ k, (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) k : R) : ℂ) • B k :=
    fun a i ↦ by haveI := hαM a; exact hB a (α a) (hαp a) i
  rw [GlobalTheory.T.order_action_matrix_eigenvalues E (condQ 𝔣 Q) R n _ j hj (HdR X.A) B T hTB σ]
  obtain ⟨ε, hε⟩ := hPC
  have hLB : (X.diag U.c).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (X.isLB U.c) _
  obtain ⟨P, hspan, hrank, -, hpush, -⟩ := hε X.A (Module.finrank ℚ (FR E)) X.ab X.dim (X.diag U.c) hLB U.u

  have hmem : ∀ x : E, x ∈ lattice (condQ 𝔣 Q) y ↔ algebraMap E (Af E) x * (↑y⁻¹ : Af E) ∈ hatO (condQ 𝔣 Q) := fun x ↦ Iff.rfl
  let L : AddSubgroup E :=
    { carrier := lattice (condQ 𝔣 Q) y
      add_mem' := fun {a b} ha hb ↦ by
        show a + b ∈ lattice (condQ 𝔣 Q) y
        rw [hmem, map_add, add_mul]; exact Subring.add_mem _ ((hmem a).1 ha) ((hmem b).1 hb)
      zero_mem' := by
        show (0 : E) ∈ lattice (condQ 𝔣 Q) y
        rw [hmem, map_zero, zero_mul]; exact Subring.zero_mem _
      neg_mem' := fun {a} ha ↦ by
        show -a ∈ lattice (condQ 𝔣 Q) y
        rw [hmem, map_neg, neg_mul]; exact Subring.neg_mem _ ((hmem a).1 ha) }
  have hLs : ∀ a ∈ orderC (condQ 𝔣 Q), ∀ x ∈ L, a * x ∈ L := fun a ha x hx ↦ by
    show a * x ∈ lattice (condQ 𝔣 Q) y
    rw [hmem, map_mul, _root_.mul_assoc]
    refine Subring.mul_mem _ ?_ ((hmem x).1 hx)
    exact Subring.le_topologicalClosure _ ⟨a, ha, rfl⟩
  let Φ : E → (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun x j ↦ φ (U.e j) x
  have hΦ : ∀ x ∈ L, Φ x ∈ U.u.Λ := fun x hx ↦ (U.lat _).2 ⟨x, hx, by funext j; simp [Φ, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  let P' : L →+ HdR X.A :=
    { toFun := fun x ↦ P ⟨Φ x, hΦ x x.2⟩
      map_zero' := by
        have : (⟨Φ ((0 : L) : E), hΦ _ (0 : L).2⟩ : U.u.Λ) = 0 := Subtype.ext (by funext j; simp [Φ])
        rw [this, map_zero]
      map_add' := fun x x' ↦ by
        have : (⟨Φ ((x + x' : L) : E), hΦ _ (x + x').2⟩ : U.u.Λ) = ⟨Φ x, hΦ x x.2⟩ + ⟨Φ x', hΦ x' x'.2⟩ :=
          Subtype.ext (by funext j; simp [Φ])
        rw [this, map_add] }
  have hspan' : Submodule.span ℂ (Set.range P') = ⊤ := by
    rw [← hspan]; congr 1
    ext v; constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨x, hx, hw⟩ := (U.lat w).1 w.2
      refine ⟨⟨x, hx⟩, ?_⟩
      show P _ = P w
      congr 1; apply Subtype.ext; rw [hw]; funext j; simp [Φ, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hdim : Module.finrank ℂ (HdR X.A) = Module.finrank ℚ E := by
    rw [hrank, ← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have hT : ∀ (a : orderC (condQ 𝔣 Q)) (x x' : L), (x' : E) = a * x → T a (P' x) = P' x' := by
    intro a x x' hx'
    haveI := hαM a
    let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      { toFun := fun w j ↦ φ (U.e j) (a : E) * w j
        map_add' := fun w w' ↦ by funext j; simp [mul_add]
        map_smul' := fun r w ↦ by funext j; simp; ring }
    exact hpush (α a) M (fun w ↦ hαU a w) _ _ (by funext j; simp [M, Φ, hx', map_mul])
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    unfold condQ
    refine mul_ne_zero h𝔣.1 ?_
    rw [Finset.prod_ne_zero_iff]
    exact fun q _ ↦ q.ne_bot
  exact GlobalTheory.T.cm_representation_eigen_decomposition E (orderC (condQ 𝔣 Q)) (GlobalTheory.T.bounded_denominator_in_order E _ hc0) L hLs (HdR X.A) P' hspan' hdim T hT (j.comp σ)

end GlobalTheory.DRLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetLevelStructure
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMAdjoint

theorem adjoint_of_holUnif (hP : GlobalTheory.Published.PeriodComparison) {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) (u : HolUnif A L g) (h : Fin g → ℝ)
    {χ : u.Λ → ℂ} (hah : u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ) {ψ : LinearMap.BilinForm ℂ (HdR A)}
    (hψ : IsPolForm (dp0 ℂ) (𝟙 _) A L ψ) (α β : A ⟶ A) [IsMonHom α] [IsMonHom β] (m m' : Fin g → ℂ)
    (hm : ∀ j, m' j = starRingEnd ℂ (m j))
    (hα : ∀ w, u.ex (fun j ↦ m j * w j) = u.ex w ≫ α) (hβ : ∀ w, u.ex (fun j ↦ m' j * w j) = u.ex w ≫ β) (x y : HdR A) :
    ψ (push (dp0 ℂ) (𝟙 _) α x) y = ψ x (push (dp0 ℂ) (𝟙 _) β y) := by
  obtain ⟨ε, hP⟩ := hP
  obtain ⟨P, hspan, -, -, hnat, hform⟩ := hP A g hA hg L hL u
  have key : ∀ (δ : A ⟶ A) [IsMonHom δ] (n : Fin g → ℂ), (∀ w, u.ex (fun j ↦ n j * w j) = u.ex w ≫ δ) → ∀ z : u.Λ,
      ∃ z' : u.Λ, (z' : Fin g → ℂ) = (fun j ↦ n j * z.1 j) ∧ push (dp0 ℂ) (𝟙 _) δ (P z) = P z' := by
    intro δ _ n hδ z
    have hz : (fun j ↦ n j * z.1 j) ∈ u.Λ := by
      rw [← u.ker, hδ, (u.ker _).2 z.2, MonObj.one_comp]
    exact ⟨⟨_, hz⟩, rfl, hnat δ (LinearMap.mulLeft ℂ n) hδ z _ rfl⟩
  have e : ψ ∘ₗ push (dp0 ℂ) (𝟙 _) α = ψ.compl₂ (push (dp0 ℂ) (𝟙 _) β) := by
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨z, rfl⟩
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨w, rfl⟩
    obtain ⟨z', hz', ez⟩ := key α m hα z
    obtain ⟨w', hw', ew⟩ := key β m' hβ w
    rw [LinearMap.comp_apply, LinearMap.compl₂_apply, ez, ew, hform _ χ ψ hah hψ, hform _ χ ψ hah hψ, hz', hw']
    congr 3
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hm, RCLike.star_def, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  exact LinearMap.congr_fun₂ e x y

theorem exists_polForm_pull {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem ne_zero_of_isTotPos {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {x : F} (h : IsTotPos x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa using h (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))

theorem adjoint_of_scale {R O M : Type*} [CommRing R] [IsDomain R] [CharZero R] [CommRing O] [AddCommGroup M] [Module R M]
    (ρ : O →+* Module.End R M) {ψ ψ₀ : LinearMap.BilinForm R M} {n : ℕ} (hn : n ≠ 0) {t a b : O}
    (ht : ∀ x z, (n : R) * ((2 : R) • ψ₀) x z = ψ x (ρ t z)) (adj : ∀ x z, ψ (ρ a x) z = ψ x (ρ b z)) (x z : M) :
    ψ₀ (ρ a x) z = ψ₀ x (ρ b z) := by
  have e := adj x (ρ t z)
  rw [← Module.End.mul_apply (ρ b), ← map_mul, mul_comm b, map_mul, Module.End.mul_apply, ← ht, ← ht] at e
  have e2 := mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) e
  simp only [LinearMap.smul_apply, smul_eq_mul] at e2
  exact mul_left_cancel₀ two_ne_zero e2

theorem half_form_adjoint : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) →
      ∀ a b : orderC (condQ 𝔣 Q), (b : E) = IsCMField.complexConj E a → ∀ h h' : HdR X₀.A,
        ψ₀ (act (dp0 R) (𝟙 _) cm a h) h' = ψ₀ h (act (dp0 R) (𝟙 _) cm b h') := by
  intro hP hD _ E _ _ _ _ I _ d φ _ 𝔣 _ l _ Q _ _ y _ lam 𝔠 R _ _ X₀ X U p cm hX hF hcm _ _ _ _ c₀ ψ₀ _ hψ₀ a b hab h h'
  obtain ⟨ψ, hψ⟩ := GlobalTheory.PureLift.exists_isPolForm hD.1 X₀.ab X₀.dim (L := X₀.diag U.c) (pull_isLB (X₀.isLB U.c) _)
  letI : Algebra R ℂ := R.subtype.toAlgebra
  have m := GlobalTheory.Published.AbelianDeRham.bcMor (R := R) (R' := ℂ) hX.grp
  have hBC : m.IsBC := (hD.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hX.grp).1
  obtain ⟨ψ', hψ', hc⟩ := exists_polForm_pull R.subtype hX m U.c hψ
  obtain ⟨χ, hχ⟩ := U.ah
  obtain ⟨α, _, eα, hα⟩ := hcm a
  obtain ⟨β, _, eβ, hβ⟩ := hcm b
  haveI := cm.hom
  have adj : ∀ x z : HdR X₀.A, ψ (act (dp0 R) (𝟙 _) cm a x) z = ψ x (act (dp0 R) (𝟙 _) cm b z) := by
    intro x z
    obtain ⟨x', hx⟩ := hBC.exists x
    obtain ⟨z', hz⟩ := hBC.exists z
    refine R.subtype_injective ?_
    rw [act_apply, act_apply, ← hc _ _ _ _ (hx.push m (cm.act a) α eα.symm) hz,
      ← hc _ _ _ _ hx (hz.push m (cm.act b) β eβ.symm)]
    exact adjoint_of_holUnif hP X.ab X.dim (pull_isLB (X.isLB U.c) _) U.u (fun j ↦ U.h (U.e j)) hχ hψ' α β _ _
      (fun j ↦ by rw [hab, IsCMField.complexEmbedding_complexConj]) hα hβ x' z'
  obtain ⟨n, t, hn, ht⟩ := GlobalTheory.T.polarization_forms_commensurable hD _ 𝔠 R X₀ c₀ U.c (ne_zero_of_isTotPos U.pos) _ ψ hψ₀ hψ
  have et : act (dp0 R) (𝟙 _) X₀.rm t = act (dp0 R) (𝟙 _) cm (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) t) := by
    haveI := X₀.rm.hom
    rw [act_apply, act_apply]
    exact push_congr _ _ (hF t).symm
  exact adjoint_of_scale (act (dp0 R) (𝟙 _) cm) hn (fun x z ↦ (ht x z).trans (congrArg (fun T ↦ ψ x (T z)) et)) adj h h'

end GlobalTheory.CMAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpL
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two.WeilCmp

variable {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S)

abbrev KK : Type := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))

def cmpφ (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) : KK → ((P₀.A ⊗ P₀.A).left ⟶ P₁.A.left ⨿ P₂.A.left) :=
  Sum.elim (fun I => (psum P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] I.down).left ≫ coprod.inr)
    (fun I => (psum P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] I.down).left ≫ coprod.inl)

def cmpε : KK → ℤ := Sum.elim (fun I => (-1) ^ (2 - I.down.card)) (fun I => -((-1) ^ (2 - I.down.card)))

abbrev CmpL (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) : LB (P₀.A ⊗ P₀.A).left :=
  LB.LinComb (join P₁.L P₂.L) (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) cmpε

end GlobalTheory.Mum.Two.WeilCmp
end
end

