import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimStalkLeTautologicalChartRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjTensorPowerIntMatrixEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingInvolutionActionGivesPolarisedAdjointPair
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.ActAdj

section Iso

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem chart_le (j' : K' → L.ι) (j : K → L.ι) :
    LB.wchart L φ' j' ⊓ LB.wchart L φ j ≤ LB.wchart L (Sum.elim φ' φ) (Sum.elim j' j) := fun _ hy =>
  Set.mem_iInter.2 fun k => match k with
    | Sum.inl k => Set.mem_iInter.1 hy.1 k
    | Sum.inr k => Set.mem_iInter.1 hy.2 k

def genIso (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) :
    LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') :=
  ⟨fun p => res (chart_le p.1 p.2) (t.s (Sum.elim p.1 p.2))⟩

theorem gm_genIso (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (p : (K' → L.ι) × (K → L.ι)) (hp : r z ∈ LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2) :
    gm r z _ ((genIso t).s p) = gm r z _ (t.s (Sum.elim p.1 p.2)) :=
  gm_res r z (chart_le p.1 p.2) hp _

theorem genIso_isGen {t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))} (ht : t.IsGen) :
    (genIso t).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have hp := chart_le (φ := φ) (φ' := φ') p.1 p.2 hy.1
  have hq := chart_le (φ := φ) (φ' := φ') q.1 q.2 hy.2
  have e := gen_trans ht (𝟙 Y) y hp hq
  refine ((gm_res (𝟙 Y) y _ hy _).trans ((gm_genIso t (𝟙 Y) y p hy.1).trans e)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y p q hy)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_genIso t (𝟙 Y) y q hy.2)))).trans ?_
  congr 1
  refine (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hy.1.1 hy.2.1)
    (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hy.1.2 hy.2.2))).trans ?_
  simp only [trF, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

end Iso

end GlobalTheory.MumFam.ActAdj

namespace GlobalTheory.MumFam

open ActAdj in

theorem adj_act : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), Adj (pol D) (pol D) (o.onB.act a) (o.onB.act (Star.star a)) (DistribMulAction.toAddMonoidHom D.toPre.X a) (DistribMulAction.toAddMonoidHom D.toPre.X (Star.star a)) := by
  intro R _ _ I D O _ _ _ o a
  have hL := D.toPre.P.isLB
  let B := D.toPre.P.A
  let f := o.onB.act a
  let g := o.onB.act (star a)
  haveI hf : IsMonHom f := o.onB.hom a
  haveI hg : IsMonHom g := o.onB.hom (star a)
  let φ₀ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
    fun I => (psum B ![fst B B ≫ f, snd B B] I.down).left
  let φ₁ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
    fun I => (psum B ![fst B B, snd B B ≫ g] I.down).left
  let e₂ : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
  obtain ⟨u, hu, h0⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb hL f g (o.onB.rosati a)
  have hF : FormEq (rosatiφ B f g) (fun i => - rosatiε i) (Sum.elim φ₁ φ₀) (Sum.elim e₂ (fun k => - e₂ k)) := by
    intro U _ k
    have p := prod_ros f g (fst B B) (snd B B) k
    rw [lift_fst_snd] at p
    have p' : ∏ i, k (rosatiφ B f g i) ^ rosatiε i = _ :=
      (Finset.prod_congr rfl fun i _ => by erw [Over.id_left, Category.id_comp]).trans p
    have s1 : ∏ I, k (φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ g) k
    have s0 : ∏ I, k (φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ f) (snd B B) k
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [p', s1, s0]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨t, ht, htv⟩ := exists_gen hL hF (LB.invGen _ _ _ u) (DVR.invGen_isGen _ _ _ _ hu)
  let w : LB.Iso (cubeLB B ![fst B B ≫ f, snd B B] D.toPre.P.L) (cubeLB B ![fst B B, snd B B ≫ g] D.toPre.P.L) :=
    genIso t
  refine ⟨hf, hg, fun y => o.c_lin a y, fun y => o.c_lin (star a) y, w, genIso_isGen ht,
    fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  let P := (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left
  have hp : ∀ b b' J, Good D.toPre.P.L z J → val ((pol D).tau b b') (𝟙 _) z J = val (D.toPre.tau b b') (𝟙 _) z J :=
    fun b b' J hJ => (Wit.exists_tau D.toPre b b').choose_spec.2 _ _ z J hJ
  have hK₁ : Good D.toPre.P.L z J₁ := hJ₁
  have hK₂ : Good D.toPre.P.L z J₂ := hJ₂

  have bal := val_corr hK₁ (o.tau_bal a u hu h0 y y') (𝟙 _)
  rw [val_mul hK₁, val_pull hK₁, Category.id_comp] at bal
  have hut : val t P z J₁ = (val u P z J₁)⁻¹ := (htv _ P z J₁ hK₁).trans (val_inv _ _)
  let h := DistribMulAction.toAddMonoidHom D.toPre.X a
  let h' := DistribMulAction.toAddMonoidHom D.toPre.X (star a)
  have single : val ((pol D).tau (h y) y') (𝟙 _) z J₁ =
      val t P z J₁ * val ((pol D).tau y (h' y')) (𝟙 _) z J₁ := by
    exact (hp _ _ _ hK₁).trans ((eq_inv_mul_of_mul_eq ((mul_comm _ _).trans bal)).trans
      (congrArg₂ (· * ·) hut.symm (hp _ _ _ hK₁).symm))

  let j₁ : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₁ (P ≫ φ₁ I)
  let j₂ : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₂ (P ≫ φ₀ I)
  let j₁' : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₁ (P ≫ φ₀ I)
  have m₁ : P z ∈ LB.wchart D.toPre.P.L φ₁ j₁ := hK₁.mem φ₁ P
  have m₂ : P z ∈ LB.wchart D.toPre.P.L φ₀ j₂ := hK₂.mem φ₀ P
  have m₁' : P z ∈ LB.wchart D.toPre.P.L φ₀ j₁' := hK₁.mem φ₀ P
  have eA : adjVal w P z J₁ J₂ = gm P z _ (t.s (Sum.elim j₁ j₂)) := gm_genIso t P z (j₁, j₂) ⟨m₁, m₂⟩
  have eT : val t P z J₁ = gm P z _ (t.s (Sum.elim j₁ j₁')) := val_of t P z J₁ _ (by rintro (k | k) <;> rfl)
  have tr := gen_trans ht P z (chart_le j₁ j₂ ⟨m₁, m₂⟩) (chart_le j₁ j₁' ⟨m₁, m₁'⟩)
  have trτ := gen_trans ((pol D).tau_gen (h y) y') (𝟙 _) z (hK₂.mem _ (𝟙 _)) (hK₁.mem _ (𝟙 _))
  let H : ((TK R).left ⟶ B.left) → ((TK R).left.presheaf.stalk z)ˣ :=
    fun ψ => gm ψ z (D.toPre.P.L.U (J₂ ψ) ⊓ D.toPre.P.L.U (J₁ ψ)) (D.toPre.P.L.g (J₂ ψ) (J₁ ψ))
  have kt : trF (Sum.elim φ₁ φ₀) (Sum.elim e₂ fun k => -e₂ k) P z (Sum.elim j₁ j₂) (Sum.elim j₁ j₁') =
      (∏ I, H (P ≫ φ₀ I) ^ e₂ I)⁻¹ := by
    unfold trF
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Finset.prod_eq_one (fun I _ => by erw [gm_self hL (P ≫ φ₁ I) z (hK₁ (P ≫ φ₁ I)), one_zpow]), _root_.one_mul]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    rfl
  have cx : (toUnit (TK R) ≫ D.toPre.c y) ≫ f = toUnit (TK R) ≫ (pol D).c (h y) :=
    (Category.assoc _ _ _).trans (congrArg (toUnit (TK R) ≫ ·) (o.c_lin a y)).symm
  let X : TK R ⟶ B := toUnit (TK R) ≫ (pol D).c (h y)
  let Y : TK R ⟶ B := toUnit (TK R) ≫ (pol D).c y'
  have q1 : P ≫ ((fst B B ≫ f) * snd B B).left = (X * Y).left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, cx]
    rfl
  have q2 : P ≫ (fst B B ≫ f).left = X.left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, lift_fst_assoc, cx]
    rfl
  have q3 : P ≫ (snd B B).left = Y.left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, lift_snd]
    rfl
  have q4 : P ≫ (1 : B ⊗ B ⟶ B).left = (1 : TK R ⟶ B).left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, MonObj.comp_one]
  have s0 : ∏ I, H (P ≫ φ₀ I) ^ e₂ I = H (P ≫ ((fst B B ≫ f) * snd B B).left) * (H (P ≫ (fst B B ≫ f).left))⁻¹ *
      (H (P ≫ (snd B B).left))⁻¹ * H (P ≫ (1 : B ⊗ B ⟶ B).left) :=
    GlobalTheory.NormRos.prod_square (fst B B ≫ f) (snd B B) (fun ψ => H (P ≫ ψ))
  have l4 : ∀ X Y : TK R ⟶ B, ∏ k, H (𝟙 _ ≫ lamPts X Y k) ^ negε k =
      (H (X * Y).left)⁻¹ * H X.left * H Y.left * (H (1 : TK R ⟶ B).left)⁻¹ := fun X Y => by
    have e := Wit.prod_neg_lamPts X Y (fun ψ => (H ψ)⁻¹)
    simpa only [inv_inv] using e
  have kτ : ∏ k, H (𝟙 _ ≫ lamPts X Y k) ^ negε k = (∏ I, H (P ≫ φ₀ I) ^ e₂ I)⁻¹ := by
    rw [l4 X Y, s0, q1, q2, q3, q4]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine (trτ.trans (congrArg (_ * ·) single)).trans (Eq.trans ?_
    (congrArg (· * _) (eA.trans (tr.trans (congrArg (_ * ·) eT.symm)))).symm)
  rw [_root_.mul_assoc]
  congr 1
  exact kτ.trans kt.symm

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLeOfIsEtaleCompletionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_le_of_isEtaleCompletion' : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ψ : O →+* A) [IsLocalHom ψ], IsEtaleCompletion ψ → ringKrullDim A ≤ ringKrullDim O := by
  first | exact @GlobalTheory.ringKrullDim_le_of_isEtaleCompletion | exact GlobalTheory.ringKrullDim_le_of_isEtaleCompletion | (intros; apply GlobalTheory.ringKrullDim_le_of_isEtaleCompletion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimStalkLeTautologicalChartRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_stalk_le_tautologicalChartRing : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite → ringKrullDim (S.presheaf.stalk (ξ (closedPoint C.R))) ≤ ringKrullDim C.R := by
  first | exact @GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart | exact GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart | (intros; apply GlobalTheory.TChart.ChartDim.ringKrullDim_stalk_le_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjTensorPowerIntMatrixEndomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiAdj_tensorPowerIntMatrixEndomorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → RosatiAdj D'.P.A D'.P.L (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') := by
  first | exact @GlobalTheory.TensAct.rosatiAdj_matAct | exact GlobalTheory.TensAct.rosatiAdj_matAct | (intros; apply GlobalTheory.TensAct.rosatiAdj_matAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumMemSpanCubicalTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBal.SpanPf

variable {r : ℕ}

abbrev S (r : ℕ) : Submodule ℤ (Vec r →₀ ℤ) :=
  Submodule.span ℤ (Set.range fun p : Vec r × Vec r × Vec r => theta p.1 p.2.1 p.2.2)

lemma lam_comm (u v : Vec r) : lam u v = lam v u := by
  unfold lam; rw [add_comm u v]; abel

lemma theta_eq (u u' v : Vec r) : theta u u' v = lam (u + u') v - lam u v - lam u' v := by
  unfold lam theta; abel

lemma theta_mem (a b c : Vec r) : theta a b c ∈ S r := Submodule.subset_span ⟨(a, b, c), rfl⟩

def f (u v : Vec r) : (Vec r →₀ ℤ) ⧸ S r := Submodule.Quotient.mk (lam u v)

lemma f_comm (u v : Vec r) : f u v = f v u := by unfold f; rw [lam_comm]

lemma f_add_left (u u' v : Vec r) : f (u + u') v = f u v + f u' v := by
  unfold f
  rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
  have h := theta_mem u u' v
  rw [theta_eq] at h
  convert h using 1; abel

lemma f_add_right (u v v' : Vec r) : f u (v + v') = f u v + f u v' := by
  rw [f_comm, f_add_left, f_comm v, f_comm v']

lemma f_smul_left (c : ℤ) (u v : Vec r) : f (c • u) v = c • f u v :=
  map_zsmul (AddMonoidHom.mk' (fun u => f u v) (fun a b => f_add_left a b v)) c u

lemma f_smul_right (c : ℤ) (u v : Vec r) : f u (c • v) = c • f u v := by
  rw [f_comm, f_smul_left, f_comm]

def B (r : ℕ) : Vec r →ₗ[ℤ] Vec r →ₗ[ℤ] (Vec r →₀ ℤ) ⧸ S r :=
  LinearMap.mk₂ ℤ f f_add_left f_smul_left f_add_right f_smul_right

lemma B_apply (u v : Vec r) : B r u v = Submodule.Quotient.mk (lam u v) := rfl

lemma B_comm (u v : Vec r) : B r u v = B r v u := f_comm u v

lemma axv_eq (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : axv A i = ∑ l, A i l • xv l := by
  funext s
  cases s <;> simp [axv, xv, Finset.sum_apply, Pi.single_apply]

lemma azv_eq (A' : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : azv A' i = ∑ l, A' i l • zv l := by
  funext s
  cases s <;> simp [azv, zv, Finset.sum_apply, Pi.single_apply]

def P (C : Matrix (Fin r) (Fin r) ℤ) : (Vec r →₀ ℤ) ⧸ S r := ∑ l, ∑ m, C l m • B r (xv l) (zv m)

lemma P_add (C D : Matrix (Fin r) (Fin r) ℤ) : P (C + D) = P C + P D := by
  simp [P, add_smul, Finset.sum_add_distrib]

lemma T1 (A V : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, V i j • B r (axv A i) (zv j) = P (A.transpose * V) := by
  simp only [P, axv_eq, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

lemma T3 (A' V : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, V i j • B r (xv i) (azv A' j) = P (V * A') := by
  simp only [P, azv_eq, map_sum, map_zsmul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma swapW (V : Matrix (Fin r) (Fin r) ℤ) (g : Fin r → Fin r → (Vec r →₀ ℤ) ⧸ S r) :
    ∑ i, ∑ j, V i j • g j i = ∑ i, ∑ j, V.transpose i j • g i j := by
  rw [Finset.sum_comm]; rfl

lemma per (A A' : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) :
    ∑ a : Fin 6, rosatiε a • B r (rosVec A A' a i) (rosVec A A' a j) =
      B r (axv A i) (zv j) + B r (zv i) (axv A j) - B r (xv i) (azv A' j) - B r (azv A' i) (xv j) := by
  simp [Fin.sum_univ_six, rosVec, rosatiε, map_add, LinearMap.add_apply]
  abel

theorem main {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (h : A.transpose * (W + W.transpose) = (W + W.transpose) * A') :
    GlobalTheory.TensBal.sig W A A' ∈ Submodule.span ℤ
      (Set.range fun p : GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r =>
        GlobalTheory.TensBal.theta p.1 p.2.1 p.2.2) := by
  rw [← Submodule.Quotient.mk_eq_zero]
  have e : (Submodule.Quotient.mk (sig W A A') : (Vec r →₀ ℤ) ⧸ S r) =
      ∑ i, ∑ j, W i j • ∑ a : Fin 6, rosatiε a • B r (rosVec A A' a i) (rosVec A A' a j) := by
    rw [sig, ← Submodule.mkQ_apply]
    simp only [map_sum, map_zsmul, Submodule.mkQ_apply, ← B_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  show (Submodule.Quotient.mk (sig W A A') : (Vec r →₀ ℤ) ⧸ S r) = 0
  rw [e]
  simp only [per, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ j, W i j • B r (zv i) (axv A j) = P (A.transpose * W.transpose) := by
    rw [← T1]; simp only [B_comm (zv _)]; exact swapW W (fun a b => B r (axv A a) (zv b))
  have h4 : ∑ i, ∑ j, W i j • B r (azv A' i) (xv j) = P (W.transpose * A') := by
    rw [← T3]; simp only [B_comm (azv A' _)]; exact swapW W (fun a b => B r (xv a) (azv A' b))
  rw [T1, h2, T3, h4, ← P_add, sub_sub, ← P_add, ← Matrix.add_mul, ← Matrix.mul_add, h, sub_self]

end GlobalTheory.TensBal.SpanPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumPsiValuesEqTauProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBalLat

open GlobalTheory.TensBal

section Calc

variable {M : Type} [CommGroup M] {α : Type}

def logHom (f : α → M) : (α →₀ ℤ) →+ Additive M :=
  Finsupp.liftAddHom fun v => zmultiplesHom (Additive M) (Additive.ofMul (f v)⁻¹)

theorem logHom_single (f : α → M) (v : α) : logHom f (Finsupp.single v 1) = Additive.ofMul (f v)⁻¹ := by
  simp [logHom]

theorem prod_eq_logHom (f : α → M) (c : α →₀ ℤ) :
    ∏ v ∈ c.support, f v ^ (-(c v)) = Additive.toMul (logHom f c) := by
  simp [logHom, Finsupp.liftAddHom_apply, Finsupp.sum, toMul_sum, toMul_zsmul, inv_zpow']

end Calc

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecLat_add (T : Tens D D' W) (u v : Vec r) (y y' : D'.X) :
    vecLat T (u + v) y y' = vecLat T u y y' + vecLat T v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel

theorem vecLat_zero (T : Tens D D' W) (y y' : D'.X) : vecLat T 0 y y' = 0 := by
  simp [vecLat]

theorem vecLat_rosVec (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (y y' : D'.X) (a : Fin 6) (i : Fin r) :
    vecLat T (rosVec A A' a i) y y' = T.xe (rosLat T A A' y y' a) i := by
  fin_cases a <;>
    simp [vecLat, rosVec, rosLat, axv, azv, xv, zv, GlobalTheory.TensAct.xe_latAct, map_add, Pi.single_apply,
      Finset.sum_add_distrib, add_smul, ite_smul]

theorem logHom_lam (T : Tens D D' W) (hB : D.TauBimult) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (y y' : D'.X) (u v : Vec r) :
    logHom (fun w => val (D.psi (vecLat T w y y')) (𝟙 _) z J) (lam u v) =
      Additive.ofMul (val (D.tau (vecLat T u y y') (vecLat T v y y')) (𝟙 _) z J)⁻¹ := by
  have hk : val (D.psi 0) (𝟙 _) z J = (val D.rigK (𝟙 _) z J)⁻¹ := by
    have e := (GlobalTheory.TauBalBox.tau_val D hJ 0 0 (𝟙 _)).symm.trans (GlobalTheory.TauBalElem.tau_zero_left hB hJ 0)
    rw [add_zero, mul_inv_cancel, _root_.one_mul] at e
    exact inv_mul_eq_one.mp e
  have h0 : vecLat T (0 : Vec r) y y' = 0 := vecLat_zero T y y'
  simp only [lam, map_add, map_sub, logHom_single, vecLat_add]
  rw [h0, vecLat_add]
  rw [GlobalTheory.TauBalBox.tau_val D hJ, hk]
  simp only [ofMul_mul, ofMul_inv, inv_inv]
  abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), D.TauBimult → ∀ (A A' : Matrix (Fin r) (Fin r) ℤ) (z : (TK R).left)
    (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ y y' : D'.X,
    ∏ v ∈ (GlobalTheory.TensBal.sig W A A').support,
        val (D.psi (GlobalTheory.TensBal.vecLat T v y y')) (𝟙 _) z J ^ (-(GlobalTheory.TensBal.sig W A A' v)) =
      ∏ a, GlobalTheory.TensBal.qv T z J (GlobalTheory.TensBal.rosLat T A A' y y' a) ^ (-(rosatiε a)) := by
  intro R _ _ D D' r W T hB A A' z J hJ y y'
  rw [prod_eq_logHom (fun w => val (D.psi (vecLat T w y y')) (𝟙 _) z J)]
  apply Additive.ofMul.injective
  rw [ofMul_toMul]
  simp only [sig, map_sum, map_zsmul, logHom_lam T hB hJ, vecLat_rosVec, qv, ofMul_prod, ofMul_zpow,
    Finset.smul_sum, ofMul_inv, smul_neg, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul, neg_mul, vecLat_rosVec, vecLat_rosVec]

end GlobalTheory.TensBalLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueOneZeroFirstFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RosZeroLeft

theorem val_lift_one_left : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB →
    IsAbelianScheme A → ∀ (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) →
    ∀ (T : Over S) (y : T ⟶ A) (z : T.left) (J : (T.left ⟶ A.left) → L.ι), Good L z J →
      val u (lift (1 : T ⟶ A) y).left z J = 1 := by
  intro S A _ _ L hL hA f g _ _ u hu h₀ T y z J hJ
  have one_isGen : (LB.oneGen L (Y := A.left)).IsGen :=
    isGen_of_gm _ fun _ _ _ _ _ =>
      (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)))
  have key := gen_unique' hL (u := LB.pullGen L _ _ u (lift (1 : A ⟶ A) (𝟙 A)).left)
    (u' := LB.oneGen L) (fun U _ h => by
      refine (Fintype.prod_empty _).trans (Eq.symm ((prod_ros f g 1 (𝟙 A) h).trans ?_))
      rw [MonObj.one_comp, _root_.one_mul, _root_.one_mul, Category.id_comp]
      simp)
    A.hom η[A].left (Over.w η[A]) (GlobalTheory.globalFns_holds _ _ hA).2 (DVR.pullGen_isGen _ _ _ _ hu _)
    one_isGen (fun y I hI => by
      have := val_corr hI h₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at this
      rw [val_pull hI, val_one, ← Over.comp_left]
      have e : η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) = lift η[A] η[A] := by simp [Hom.one_def]
      rw [e]; exact this) _ y.left z J hJ
  rw [val_pull hJ, val_one, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] at key
  exact key

end GlobalTheory.RosZeroLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsBOfClauses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj Formalism.L2 Formalism.L2.Rows Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsAtRealTB

set_option maxHeartbeats 1000000 in
theorem rowsB_of_clauses : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.ExAt → B.Q.Rl.toRealDat.LUnif → IoExt B.Q.Rl.toRealDat → RowsB B := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn hEx hUnif hIo
  exact ⟨hIo, fun i => GlobalTheory.T.oneMapRowR_of_weakCharacterisation D _ _ _ _ P.A3 B.T B.Q.Rl (faceT P Dcf Spf Zscf) B.κ B.v₀ B.O (phEff B.Q.Rl)
    hn B.Q.charW hEx ⟨B.fw⟩ hIo i (B.pins i) (B.phase i hUnif)⟩

end GlobalTheory.RowsAtRealTB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSiegelDomainDecayStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_siegel_domain_decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ c : ℝ, 0 < c →
    ∀ φ ∈ SB (Fin n × Fin d → Af F), (∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ M.So B.ψ B.τ₁) →
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (t : Fin q → ℝ) (a κ : UA σ X.J) (h : UA σ W.J),
      (∀ i, c ≤ t i) → IsTorusU x y t a → κ ∈ Cc →
      ‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ N ≤ C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := by
  first | exact @GlobalTheory.ThKTorus.torusDecay | exact GlobalTheory.ThKTorus.torusDecay | (intros; apply GlobalTheory.ThKTorus.torusDecay <;> assumption)
end

