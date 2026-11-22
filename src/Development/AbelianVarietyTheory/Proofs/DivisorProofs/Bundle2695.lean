import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2587
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataOfAdj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.AdjEnd

section Iso

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem wchart_le (j : K' ⊕ K → L.ι) :
    LB.wchart L (Sum.elim φ' φ) j ≤ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩

def isoGen (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k))) :=
  ⟨fun j => res (wchart_le j) (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩

theorem isoGen_isGen {w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')} (hw : w.IsGen) : (isoGen w).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have le := fun j : K' ⊕ K → L.ι => (wchart_le (φ := φ) (φ' := φ') j)
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 Y) y (LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr))))
    (hw (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr))
  have e' := (gm_res (𝟙 Y) y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr) hm)
    (gm_res (𝟙 Y) y _ hm _))))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 Y) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.2 _)))
  refine (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hm.1.1 hm.2.1).symm ?_)
  refine Eq.trans ?_ (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hm.1.2 hm.2.2).symm)
  simp only [Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp_apply]
  rfl

theorem val_isoGen (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (isoGen w) r z J = gm r z _ (w.s (fun k => J (r ≫ φ' k), fun k => J (r ≫ φ k))) :=
  gm_res r z _ (hJ.mem _ r) _

end Iso

end GlobalTheory.MumFam.AdjEnd

namespace GlobalTheory.MumFam.AdjEnd

theorem endData_of_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), Adj (pol D) (pol D) a a' h h' → EndData D.toPre a a' h h' := by
  intro R _ _ _ _ D a a' h h' H
  obtain ⟨ha, ha', hc, hc', w, hw, hτ⟩ := H
  have hL := D.toPre.P.isLB
  let B := D.toPre.P.A
  let t := isoGen w
  have ht : t.IsGen := isoGen_isGen hw
  let ℓ : (B ⊗ B).left ⟶ (B ⊗ B).left := (lift (1 : B ⊗ B ⟶ B) 1).left
  let v := LB.mulGen _ _ _ _ _ (LB.invGen _ _ _ t) (LB.pullGen _ _ _ t ℓ)
  have hv : v.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht) (DVR.pullGen_isGen _ _ _ _ ht _)
  let φ₀ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) := fun I => (psum B ![fst B B ≫ a, snd B B] I.down).left
  let φ₁ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) := fun I => (psum B ![fst B B, snd B B ≫ a'] I.down).left
  let e₂ : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
  have hF : FormEq (Sum.elim (Sum.elim φ₁ φ₀) (fun k => ℓ ≫ Sum.elim φ₁ φ₀ k))
      (Sum.elim (fun k => - Sum.elim e₂ (fun k => - e₂ k) k) (Sum.elim e₂ (fun k => - e₂ k))) (rosatiφ B a a') rosatiε := by
    intro U _ k
    haveI : IsMonHom a := ha
    haveI : IsMonHom a' := ha'
    have p := prod_ros a a' (fst B B) (snd B B) k
    rw [lift_fst_snd] at p
    rw [(Finset.prod_congr rfl fun i _ => by erw [Over.id_left, Category.id_comp]).trans p]
    have one : ∀ q : B ⊗ B ⟶ B, lift (1 : B ⊗ B ⟶ B) 1 ≫ q = 1 → k (ℓ ≫ q.left) = k (1 : B ⊗ B ⟶ B).left :=
      fun q hq => by rw [← hq]; rfl
    have o1 : lift (1 : B ⊗ B ⟶ B) 1 ≫ fst B B = 1 := lift_fst _ _
    have o2 : lift (1 : B ⊗ B ⟶ B) 1 ≫ snd B B = 1 := lift_snd _ _
    have o3 : lift (1 : B ⊗ B ⟶ B) 1 ≫ fst B B ≫ a = 1 := by rw [← Category.assoc, o1, MonObj.one_comp]
    have o4 : lift (1 : B ⊗ B ⟶ B) 1 ≫ snd B B ≫ a' = 1 := by rw [← Category.assoc, o2, MonObj.one_comp]
    have o5 : lift (1 : B ⊗ B ⟶ B) 1 ≫ (1 : B ⊗ B ⟶ B) = 1 := MonObj.comp_one _
    have o6 : lift (1 : B ⊗ B ⟶ B) 1 ≫ ((fst B B ≫ a) * snd B B) = 1 := by
      rw [MonObj.comp_mul, o3, o2, _root_.mul_one]
    have o7 : lift (1 : B ⊗ B ⟶ B) 1 ≫ (fst B B * (snd B B ≫ a')) = 1 := by
      rw [MonObj.comp_mul, o1, o4, _root_.mul_one]
    have s1 : ∏ I, k (φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ a') k
    have s0 : ∏ I, k (φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ a) (snd B B) k
    have s1' : ∏ I, k (ℓ ≫ φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ a') (fun ψ => k (ℓ ≫ ψ))
    have s0' : ∏ I, k (ℓ ≫ φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ a) (snd B B) (fun ψ => k (ℓ ≫ ψ))
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, Finset.prod_inv_distrib]
    rw [s1, s0, s1', s0']
    simp only [one _ o1, one _ o2, one _ o3, one _ o4, one _ o5, one _ o6, one _ o7]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine ⟨ha, ha', ?_, hc, hc', ?_⟩
  · obtain ⟨u, hu, -⟩ := exists_gen hL hF v hv
    exact fun _ => ⟨⊤, trivial, LB.pullGen _ _ _ u _, DVR.pullGen_isGen _ _ _ _ hu _⟩
  · intro u hu h₀ y y'
    haveI : IsMonHom a := ha
    haveI : IsMonHom a' := ha'
    have o : ∀ {T : Over (Spec (CommRingCat.of R))} (x x' : T ⟶ B), (lift x x').left ≫ ℓ = (lift (1 : T ⟶ B) 1).left :=
      fun x x' => by rw [← Over.comp_left, comp_lift, MonObj.comp_one]
    have hvv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (B ⊗ B).left) (z : Z) (J), Good D.toPre.P.L z J →
        val v r z J = (val t r z J)⁻¹ * val t (r ≫ ℓ) z J := fun Z r z J hJ =>
      (val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_inv _ _) (val_pull hJ _ _ _))
    have hn : ∀ (yy : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (J), Good D.toPre.P.L yy J →
        val v (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) 1).left yy J = 1 := fun yy J hJ =>
      (hvv _ _ yy J hJ).trans (by erw [o, inv_mul_cancel])
    have eq := DVR.gen_unique₂ GlobalTheory.globalFns_holds D.toPre.P.isAb hL hF hu hv (fun yy J hJ =>
      (DVR.val₂_one h₀ hJ).trans (hn yy J hJ).symm)
    have c0 : D.toPre.c 0 = 1 := mul_eq_left.1 ((D.toPre.c_add 0 0).symm.trans (by rw [add_zero]))
    refine corr_of_val hL fun z J hJ => ?_
    have hp : ∀ a b, val ((pol D).tau a b) (𝟙 _) z J = val (D.toPre.tau a b) (𝟙 _) z J :=
      fun a b => (Wit.exists_tau D.toPre a b).choose_spec.2 _ _ z J hJ
    have h00 : val t (D.toPre.pt2 0 0) z J = 1 := by
      have e := hτ 0 0 z J J hJ hJ
      erw [map_zero h, map_zero h', Data.val_tau_zero (pol D) 0 z J hJ] at e
      refine (val_isoGen w _ z hJ).trans ?_
      exact (_root_.mul_one _).symm.trans e.symm
    have e2 : D.toPre.pt2 y y' ≫ ℓ = D.toPre.pt2 0 0 := by rw [DegPre.pt2, o, DegPre.pt2, c0, MonObj.comp_one]
    have k1 : val v (D.toPre.pt2 y y') z J = (val t (D.toPre.pt2 y y') z J)⁻¹ :=
      (hvv _ _ z J hJ).trans (by erw [e2, h00, _root_.mul_one])
    have k2 : val t (D.toPre.pt2 y y') z J = adjVal w (D.toPre.pt2 y y') z J J := val_isoGen w _ z hJ
    have k4 : val (D.toPre.tau (h y) y') (𝟙 _) z J =
        adjVal w (D.toPre.pt2 y y') z J J * val (D.toPre.tau y (h' y')) (𝟙 _) z J :=
      (hp _ _).symm.trans ((hτ y y' z J J hJ hJ).trans (congrArg _ (hp _ _)))
    rw [val_mul hJ, val_pull hJ, Category.id_comp]
    refine (congrArg (_ * ·) ((eq _ _ z J hJ).trans (k1.trans (congrArg (·⁻¹) k2)))).trans ?_
    rw [k4, mul_comm, inv_mul_cancel_left]

end GlobalTheory.MumFam.AdjEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismCharacterActionConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem endChar_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (a : 𝓞 E), EndChar P.U (t.act.act a) (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) := by
  intro E _ _ _ H R _ _ _ _ t P a κ _ ρ hρ G₀ _ φ h f₀ hf
  letI := H.starRing
  obtain ⟨τ, hτ, hi⟩ := P.lin.i_lin 0 a
  have e : τ = GlobalTheory.SplitTorus.torusMap _ (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) :=
    (GlobalTheory.SplitTorus.eq_torusMap_iff _ _).2 fun x =>
      (GlobalTheory.SplitTorus.res_pullU_charUnit τ x _).symm.trans
        ((congrArg Units.val (hτ x)).trans (GlobalTheory.SplitTorus.charUnit_val _))
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift hρ h
  have c : f₀.left ≫ GlobalTheory.TorusPart.thickLift hρ h =
      GlobalTheory.TorusPart.thickLift hρ h ≫
        ((Over.pullback (Out.thick R (maximalIdeal R) 0)).map (t.act.act a)).left := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (GlobalTheory.TorusPart.thickLift_fst _ _)).trans (hf.trans ?_))
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (GlobalTheory.ExtUnique.pullback_map_left_fst _ _).symm)
      exact (congrArg (· ≫ _) (GlobalTheory.TorusPart.thickLift_fst _ _).symm).trans (Category.assoc _ _ _)
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k.1.w).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (_ ≫ ·)
        (Over.w ((Over.pullback (Out.thick R (maximalIdeal R) 0)).map (t.act.act a))).symm)
      refine Eq.trans ?_ k.1.w.symm
      rw [← Category.assoc, Over.w]
  exact (GlobalTheory.TorusPart.pullTorus_comp k k _ _ c (P.U.gt 0).i).symm.trans
    ((congrArg (GlobalTheory.TorusPart.pullTorus k) (hi.trans (congrArg (· ≫ _) e))).trans
      (GlobalTheory.TorusPart.pullTorus_torusMap_comp k _ _))

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismDescendsToAlgebraicModelStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_descends_to_algebraic_model : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X₀ : Obj F 𝔠 (Sp Qb)) (X : Obj F 𝔠 (Sp ℂ))
    (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
      ∀ (α : X.A ⟶ X.A) [IsMonHom α], ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left := by
  first | exact @GlobalTheory.RealMult.Obj.exists_end_descend_algebraic | exact GlobalTheory.RealMult.Obj.exists_end_descend_algebraic | (intros; apply GlobalTheory.RealMult.Obj.exists_end_descend_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMovesTorsionLatticeByAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.EndLattice

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem congMod_y_of_end : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D.toPre K m) (x : TFK (R := R) K ⟶ A.A), 1 ≤ m → QkToAkU U.toUnifPre K m pk x → QkToAkU U.toUnifPre K m pk' (x ≫ E.aA) → CongMod m pk'.y (E'.h pk.y) := by
  intro R _ _ _ hBase G _ _ hG D A U E E' hE K _ _ _ m pk pk' x hm h1 h2
  haveI : CharZero R := hBase.2
  have hAdm := hBase.1
  obtain ⟨-, hFE⟩ := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hAdm D A G hG U
  obtain ⟨-, hK⟩ := hFE E E' hE
  obtain ⟨hex, hiota, hmap⟩ := hK K
  have hcalc := (GlobalTheory.EndCalc.end_calculus GlobalTheory.firstFiveLaws R (maximalIdeal R) hAdm D A G hG U K E E E).2.1
  choose φ hφ using fun g => (hex g).exists
  have hadd : ∀ g g' : GtPtF D.toPre K, φ (g + g') = φ g + φ g' := fun g g' =>
    (isAdd_iff_eq _ _ _).1 (hcalc g g' (g + g') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (hφ g) (hφ g') (hφ _))
  let φh : GtPtF D.toPre K →+ GtPtF D.toPre K :=
    AddMonoidHom.mk' φ hadd
  obtain ⟨h, hns, hio⟩ := pk.eq
  have hh : h = m • pk.g := (isNsmul_iff_eq _ _ _).1 hns
  let p' : QkPt D.toPre K m :=
    ⟨E'.h pk.y, φ pk.g, φ h, (isNsmul_iff_eq _ _ _).2 (by rw [hh]; exact map_nsmul φh m pk.g), hiota _ _ _ hio (hφ h)⟩
  have h3 : QkToAkU U.toUnifPre K m p' (x ≫ E.aA) := hmap m hm pk p' x rfl (hφ pk.g) h1
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hAdm D A G hG U K m hm
  have e : f p' = f pk' := ((hf.1 _ _).1 h3).symm.trans ((hf.1 _ _).1 h2)
  obtain ⟨z, hz, -⟩ := (hf.2.2.1 _ _).1 e
  exact ⟨z, hz⟩

end GlobalTheory.EndLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFieldPointsClosedFibreSameProjectiveImageStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_fieldPoints_closedFibre_same_projective_image : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ E.H.toScheme), (∀ t, M.π (G'.hom (E.H.ι (p t))) = closedPoint R) → p ≫ E.H.ι ≫ G'.hom = p' ≫ E.H.ι ≫ G'.hom → p ≫ E.f = p' ≫ E.f → p = p' := by
  first | exact @GlobalTheory.Mum.Emb.eq_of_closedFibre | exact GlobalTheory.Mum.Emb.eq_of_closedFibre | (intros; apply GlobalTheory.Mum.Emb.eq_of_closedFibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfCoprime
section
set_option autoImplicit false

noncomputable section

open NumberField TensorProduct GlobalTheory.RealMult

namespace GlobalTheory.KSSymm

theorem dual_smul_comm {S L : Type*} [CommRing S] [AddCommGroup L] [Module S L] [Module.Invertible S L]
    (ℓ : Module.Dual S L) (x y : L) : ℓ x • y = ℓ y • x := by
  have e := congrArg (fun z ↦ TensorProduct.lid S L (ℓ.rTensor L z))
    (show x ⊗ₜ[S] y = y ⊗ₜ[S] x from Module.Invertible.tmul_comm ..)
  simpa using e

theorem eq_zero_of_coprime {M : Type*} [AddCommGroup M] {x : M}
    (h : ∀ l : ℕ, l.Prime → ∃ n : ℕ, n.Coprime l ∧ n • x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨l, hl, hd⟩ := Nat.exists_prime_and_dvd (n := addOrderOf x) (by rwa [Ne, AddMonoid.addOrderOf_eq_one_iff])
  obtain ⟨n, hn, e⟩ := h l hl
  exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hn.symm (hd.trans (addOrderOf_dvd_of_nsmul_eq_zero e)))

theorem symm_of_casimir {R S L W ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup L] [Module R L]
    [Module S L] [IsScalarTower R S L] [Module.Invertible S L] [AddCommGroup W] [Module R W] [Fintype ι]
    (e t : ι → S) (τ : S →ₗ[R] R) (n m : ℕ)
    (cas : ∀ (f : S →ₗ[R] R) (s : S), ∑ i, f (s * e i) • t i = s * ∑ i, f (e i) • t i)
    (tr : ∑ i, τ (t i) • e i = n)
    (ρ : S → W → W) (β : W →ₗ[R] L →ₗ[R] R) (hβ : ∀ s f v, β (ρ s f) v = β f (s • v))
    (rad : ∀ f, β f = 0 → m • f = 0) (κ : W →ₗ[R] L) (hκ : ∀ s f, κ (ρ s f) = s • κ f) (f f' : W) :
    (m * n * n) • (β f (κ f') - β f' (κ f)) = 0 := by
  let Φ : W → Module.Dual S L := fun f ↦
    { toFun v := ∑ i, β f (e i • v) • t i
      map_add' := fun v w ↦ by simp only [smul_add, map_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun s v ↦ by
        have := cas (β f ∘ₗ (LinearMap.toSpanSingleton S L v).restrictScalars R) s
        simpa [smul_smul, mul_comm] using this }
  have Φv : ∀ f v, Φ f v = ∑ i, β f (e i • v) • t i := fun _ _ ↦ rfl
  have Φρ : ∀ s f v, Φ (ρ s f) v = s * Φ f v := fun s f v ↦ by
    rw [← smul_eq_mul, ← map_smul]
    simp only [Φv, hβ, smul_comm s]
  have Φsub : ∀ f f' v, Φ (f - f') v = Φ f v - Φ f' v := fun f f' v ↦ by
    simp only [Φv, map_sub, LinearMap.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have τΦ : ∀ f v, τ (Φ f v) = n • β f v := fun f v ↦ by
    have : β f ((∑ i, τ (t i) • e i) • v) = n • β f v := by rw [tr, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [← this, Φv, Finset.sum_smul, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_assoc, τ.map_smul, (β f).map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  have k : ∀ u, (m * n) • (Φ f u • κ f' - Φ f' u • κ f) = 0 := fun u ↦ by
    have z : β (n • (ρ (Φ f u) f' - ρ (Φ f' u) f)) = 0 := LinearMap.ext fun v ↦ by
      have c := congrArg (Φ f') (dual_smul_comm (Φ f) u v)
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at c
      rw [map_nsmul, LinearMap.smul_apply, ← τΦ, Φsub, Φρ, Φρ, c, mul_comm, sub_self, map_zero, LinearMap.zero_apply]
    have := congrArg κ (rad _ z)
    rwa [← mul_smul, map_nsmul, map_sub, hκ, hκ, map_zero] at this
  have k' : ∀ w : Module.Dual S L ⊗[S] L,
      (m * n) • (contractLeft S L w * (Φ f (κ f') - Φ f' (κ f))) = 0 := fun w ↦ by
    induction w with
    | zero => simp
    | add x y hx hy => rw [map_add, add_mul, smul_add, hx, hy, add_zero]
    | tmul ℓ u =>
      have c := congrArg ℓ (k u)
      have c₁ := congrArg (Φ f) (dual_smul_comm ℓ u (κ f'))
      have c₂ := congrArg (Φ f') (dual_smul_comm ℓ u (κ f))
      simp only [map_nsmul, map_sub, map_smul, smul_eq_mul, map_zero] at c c₁ c₂
      rw [contractLeft_apply, mul_sub, c₁, c₂, ← c, mul_comm (ℓ _), mul_comm (ℓ _)]
  obtain ⟨w, hw⟩ := (Module.Invertible.bijective (R := S) (M := L)).2 1
  have := congrArg τ (k' w)
  rwa [hw, one_mul, map_nsmul, map_sub, τΦ, τΦ, map_zero, ← smul_sub, ← mul_smul] at this

theorem exists_form (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] :
    ∃ (n : ℕ) (τ : 𝓞 F →ₗ[ℤ] ℤ) (t : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → 𝓞 F), n.Coprime l ∧
      (∀ i x, τ (t i * x) = n * (RingOfIntegers.basis F).repr x i) ∧ ∀ y, (∀ x, τ (y * x) = 0) → y = 0 := by
  classical
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := one_ne_zero
  let 𝔡 : FracId F := Units.mk0 (FractionalIdeal.dual ℤ ℚ 1) (FractionalIdeal.dual_ne_zero ℤ ℚ h1)
  have mem : ∀ x : F, x ∈ 𝔡.elt ↔ ∀ a : 𝓞 F, ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ F (x * a) := fun x ↦ by
    refine (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) h1).trans ⟨fun h a ↦ ?_, fun h a ha ↦ ?_⟩
    · exact h _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
    · obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      exact h a
  have dual : ∀ i (x : 𝓞 F), Algebra.trace ℚ F ((integralBasis F).traceDual i * x) =
      ((RingOfIntegers.basis F).repr x i : ℚ) := fun i x ↦ by
    conv_lhs => rw [← (RingOfIntegers.basis F).sum_repr x]
    simp only [map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm, ← integralBasis_apply,
      RingOfIntegers.coe_eq_algebraMap, Module.Basis.trace_traceDual_mul]
    simp
  obtain ⟨δ, hδ, hgen⟩ := GlobalTheory.FracGen.exists_gen F 𝔡 l
  obtain ⟨n, -, hn, hu⟩ := GlobalTheory.PolPrimeTo.exists_uniform 𝔡 l δ hgen
  choose τ hτ using (mem δ).1 δ.2
  choose t ht using fun i ↦ hu ⟨(integralBasis F).traceDual i, (mem _).2 fun a ↦ ⟨_, (dual i a).symm⟩⟩
  refine ⟨n, (AddMonoidHom.mk' τ fun a b ↦ Int.cast_injective (α := ℚ) ?_).toIntLinearMap, t, hn,
    fun i x ↦ Int.cast_injective (α := ℚ) ?_, fun y hy ↦ ?_⟩
  · rw [Int.cast_add, hτ, hτ, hτ, ← map_add, ← mul_add]
    simp
  · have e := congrArg Subtype.val (ht i)
    simp only [Submodule.coe_smul, Algebra.smul_def, map_natCast] at e
    change ((τ _ : ℤ) : ℚ) = _
    rw [hτ, Int.cast_mul, ← dual, Int.cast_natCast, ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul, ← mul_assoc, e]
    simp [mul_comm, mul_left_comm]
  · have z : (δ : F) * y = 0 := by
      refine (traceForm_nondegenerate ℚ F).1 _ fun x ↦ ?_
      rw [← (integralBasis F).sum_repr x, map_sum]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have e : ((τ (y * RingOfIntegers.basis F i) : ℤ) : ℚ) = 0 := by exact_mod_cast hy _
      rw [hτ] at e
      rw [map_smul, Algebra.traceForm_apply, integralBasis_apply, mul_assoc]
      simpa using Or.inr e
    simpa using (mul_eq_zero.1 z).resolve_left hδ

theorem exists_casimir (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] :
    ∃ (n : ℕ) (e t : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → R ⊗[ℤ] 𝓞 F) (τ : R ⊗[ℤ] 𝓞 F →ₗ[R] R), n.Coprime l ∧
      (∀ (f : R ⊗[ℤ] 𝓞 F →ₗ[R] R) (s : R ⊗[ℤ] 𝓞 F), ∑ i, f (s * e i) • t i = s * ∑ i, f (e i) • t i) ∧
      ∑ i, τ (t i) • e i = n := by
  obtain ⟨n, τ, t, hn, ht, nd⟩ := exists_form F l
  set b := RingOfIntegers.basis F
  have cas : ∀ a j, a * t j = ∑ i, b.repr (a * b i) j • t i := fun a j ↦ sub_eq_zero.1 <| nd _ fun x ↦ by
    rw [sub_mul, map_sub, Finset.sum_mul, map_sum, mul_comm a, mul_assoc, ht, sub_eq_zero]
    conv_lhs => rw [← b.sum_repr x]
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, smul_mul_assoc, map_smul, ht, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  refine ⟨n, fun i ↦ 1 ⊗ₜ b i, fun i ↦ 1 ⊗ₜ t i, (AlgebraTensorModule.rid ℤ R R).toLinearMap ∘ₗ τ.baseChange R, hn,
    fun f s ↦ ?_, ?_⟩
  · induction s with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib, hx, hy]
    | tmul r a =>
      have e₁ : ∀ i, (r ⊗ₜ[ℤ] a * (1 : R) ⊗ₜ[ℤ] b i) = r • ∑ j, b.repr (a * b i) j • (1 : R) ⊗ₜ[ℤ] b j := fun i ↦ by
        simp only [← tmul_smul, ← tmul_sum, b.sum_repr]
        simp [smul_tmul']
      have e₂ : ∀ j, (r ⊗ₜ[ℤ] a * (1 : R) ⊗ₜ[ℤ] t j) = r • ∑ i, b.repr (a * b i) j • (1 : R) ⊗ₜ[ℤ] t i := fun j ↦ by
        simp only [← tmul_smul, ← tmul_sum, ← cas]
        simp [smul_tmul']
      simp only [Finset.mul_sum, mul_smul_comm, e₁, e₂, map_smul, map_sum, map_zsmul, Finset.smul_sum,
        Finset.sum_smul, smul_assoc]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [smul_comm (f _), smul_comm (f _)]
  · have e : ∀ i, τ (t i) = n * b.repr 1 i := fun i ↦ by rw [← ht, mul_one]
    have e' : ∑ i, τ (t i) • b i = n := by
      simp only [e, mul_smul, ← Finset.smul_sum, b.sum_repr]
      simp
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, AlgebraTensorModule.rid_tmul,
      smul_assoc, one_smul, ← tmul_smul, ← tmul_sum, e']
    exact map_natCast (Algebra.TensorProduct.includeRight (R := ℤ) (A := R)) n

end GlobalTheory.KSSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalisationOfEtaleAffineFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localisation_of_etale_affine_fibre' : ∀ (A C B : CommRingCat.{0}) (φ : A ⟶ C) (ψ : C ⟶ B) (Ω : Type) [Field Ω] (ω : A ⟶ CommRingCat.of Ω) (W : (pullback (Spec.map (φ ≫ ψ)) (Spec.map ω)).Opens) (w : ↥(pullback (Spec.map (φ ≫ ψ)) (Spec.map ω))), w ∈ W → Etale (W.ι ≫ pullback.map (Spec.map (φ ≫ ψ)) (Spec.map ω) (Spec.map φ) (Spec.map ω) (Spec.map ψ) (𝟙 _) (𝟙 _) (by simp [Spec.map_comp]) (by simp)) → letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra; letI : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl); ∃ (Q' : Ideal (TensorProduct A Ω B)) (_ : Q'.IsPrime) (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w).asIdeal ∧ f ∉ Q' ∧ ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale := by
  first | exact @GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre | exact GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre | (intros; apply GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNhdsAffineSpaceMapOfFlatBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_nhds_affineSpace_map_of_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)), LocallyOfFiniteType U.hom → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → ∀ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)), Flat h → ∀ (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), p ∈ W → Etale (W.ι ≫ pullback.snd τ h) → ∃ V : U.left.Opens, pullback.fst τ h p ∈ V ∧ Etale (V.ι ≫ τ) := by
  first | exact @GlobalTheory.EtaleAtDescent.etale_nhds_of_flat_baseChange | exact GlobalTheory.EtaleAtDescent.etale_nhds_of_flat_baseChange | (intros; apply GlobalTheory.EtaleAtDescent.etale_nhds_of_flat_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfCompEtaleSameRelativeDimensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_comp_etale_sameRelativeDimension : ∀ (X Y Z S : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z) (sX : X ⟶ S) (sY : Y ⟶ S) (d : ℕ), h ≫ sY = sX → SmoothOfRelativeDimension d sX → SmoothOfRelativeDimension d sY → Etale (h ≫ f) → Etale h := by
  first | (exact @GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension) | (exact GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension) | (intros; apply GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.even_cubical_tensor_posDef_form_positive : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ z : Fin r → X, z ≠ 0 → ∃ s ∈ maximalIdeal R, ((∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s := by
  first | exact @GlobalTheory.Mum.TPos.tensor_pos | exact GlobalTheory.Mum.TPos.tensor_pos | (intros; apply GlobalTheory.Mum.TPos.tensor_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.even_domain_weight_bound : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → 8 * D.R.f * D.R.r + 4 ≤ n → (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p → ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) → Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb → ∃ s : Set (Y.V (wtZ a n)), s ⊆ (AllWt.latW Y.U (wtZ a n) : Set (Y.V (wtZ a n))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, Y.nrm (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) ∧ ∀ Z, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtZ a n) σ y ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) := by
  first | exact @GlobalTheory.CovGmin.gmin_good_cover | exact GlobalTheory.CovGmin.gmin_good_cover | (intros; apply GlobalTheory.CovGmin.gmin_good_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalIntegralClosureUnitDegreeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_normal_integralClosure_unit_degree : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.TorRef.IsCN V → ∀ (K' : Type) [Field K'] [Algebra (FractionRing V) K'] [FiniteDimensional (FractionRing V) K'], IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (j : V' →+* K'), GlobalTheory.TorRef.IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ Function.Injective j ∧ j.comp io = (algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V)) ∧ ∀ x : K', (∃ P : Polynomial V, P.Monic ∧ P.eval₂ ((algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V))) x = 0) → ∃ y, j y = x := by
  first | exact @GlobalTheory.LocExt.exists_isCN_integralClosure_of_isUnit_finrank | exact GlobalTheory.LocExt.exists_isCN_integralClosure_of_isUnit_finrank | (intros; apply GlobalTheory.LocExt.exists_isCN_integralClosure_of_isUnit_finrank <;> assumption)
end

