import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionValueInFrameLinearUniqueExists
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre.CombValue

open GlobalTheory.UT.CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {x : TFK (R := R) F ⟶ A.A} {e : FrameAt A x}

theorem valIs_comb {J : Type} [Fintype J] {s : J → SecA A F k} {b c : J → F} {t : SecA A F k} (h : IsComb A s b t)
    (hs : ∀ i, ValIs A (s i) x e (c i)) : ValIs A t x e (∑ i, b i * c i) := fun z I hI => by
  have e₀ : SecM.ofSec A.A t = ∑ l, cF R (b l) • SecM.ofSec A.A (s l) := by
    refine Subtype.ext (funext fun j => (h j).trans ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  let φ : SecM A.A A.L k (TFK (R := R) F) →+ (TFK (R := R) F).left.presheaf.stalk z :=
    AddMonoidHom.mk' (fun v => ThetaAct.sv v (ptSecT A.A x).left z I) fun a b => ThetaAct.sv_add a b _ z hI
  let ψ : F →+* (TFK (R := R) F).left.presheaf.stalk z := cstH (R := R) z
  have e₁ : ∀ a : F, @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z a) = ψ a := fun a => cst_eq z a
  refine (congrArg φ e₀).trans ((map_sum φ _ _).trans ?_)
  rw [e₁, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => (ThetaAct.sv_smul _ _ _ z hI).trans ?_
  rw [ThetaPtMove.ptSecT_fst, map_mul, _root_.mul_assoc, ← e₁, ← e₁]
  exact congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (b i)) * ·) (hs i z I hI)

theorem valIs_smul {t t' : SecA A F k} {a c : F} (h : ∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j)
    (ht : ValIs A t x e c) : ValIs A t' x e (a * c) := by
  have := valIs_comb (J := Unit) (s := fun _ => t) (b := fun _ => a) (c := fun _ => c) (t := t')
    (fun j => (h j).trans (by rw [Fintype.sum_unique])) fun _ => ht
  rwa [Fintype.sum_unique] at this

theorem valIs_unique {t : SecA A F k} {c c' : F} (h : ValIs A t x e c) (h' : ValIs A t x e c') : c = c' := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  have := (Units.mul_left_inj _).1 ((h z J hJ).symm.trans (h' z J hJ))
  simp only [id, cst_eq] at this
  exact cstH_inj z this

theorem exists_valIs (hL : Laws) (he : e.IsGen) (t : SecA A F k) : ∃ c, ValIs A t x e c := by
  obtain ⟨w, hw, -⟩ := hL.evVal _ A k x e he t
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

theorem valIs_linear : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x), (∀ (J : Type) [Fintype J] (s : J → SecA A F k) (b c : J → F) (t : SecA A F k), IsComb A s b t → (∀ i, ValIs A (s i) x e (c i)) → ValIs A t x e (∑ i, b i * c i)) ∧ (∀ (t t' : SecA A F k) (a c : F), (∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j) → ValIs A t x e c → ValIs A t' x e (a * c)) ∧ (∀ (t : SecA A F k) c c', ValIs A t x e c → ValIs A t x e c' → c = c') ∧ (e.IsGen → ∀ t : SecA A F k, ∃ c, ValIs A t x e c) :=
  fun hL _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ _ _ _ h hs => valIs_comb h hs, fun _ _ _ _ h ht => valIs_smul h ht,
      fun _ _ _ h h' => valIs_unique h h', fun he t => exists_valIs hL he t⟩

end GlobalTheory.TestFibre.CombValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSystemsJointPropertiesOfLaws
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN

theorem partI_of_inputs : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ModelsSt → N0 → PartI := by
  intro hT h1 h2 h3 h4 h5 h6 hE hU hP hH hA hM h0
  refine ⟨h0, fun E _ _ _ H D hD Xo => ?_⟩
  obtain ⟨Y, hY, hgl⟩ := hM E H D hD Xo
  refine ⟨Y, fun p W hp hW => ⟨(hY p W hp hW).1, fun i => ⟨((hY p W hp hW).2 i).1, ?_, ?_⟩⟩, hgl⟩
  · exact GlobalTheory.T.model_uniformisation_of_abelianLocus_directImage h1 h2 h3 h4 h5 hE hU hP E H D _ _ _ _ _ p ((hY p W hp hW).1.1 i)
  · exact GlobalTheory.T.arcFamily_fourthCondition_invertible_pushforward hT h1 h2 h3 h4 h5 h6 hE hU hP hH hA E H D _ _ _ _ _ p ((hY p W hp hW).1.1 i)
      ((hY p W hp hW).2 i).2

end GlobalTheory.LN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetricLiftNormalisedPullbackThetaSmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

theorem act_normPull_smul : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th th' : SecA A F 1) (c : F), (∀ j, th.f j = liftFun A.A _ (cF R c) * th'.f j) → ∀ (s₁ σ t : SecA A F (m ^ 2)) (x : TFK (R := R) F ⟶ A.A) (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) F)) (c' : F), x ^ (m ^ 2) = 1 → IsNormPull A ρ m (m ^ 2) th s₁ → SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ → IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ σ → ThC A ρ m th' x t c' → ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j := by
  intro hLL R _ _ _ A F _ _ ρ hρ m hm th th' c hc s₁ σ t x θ c' hx ⟨α, hα, hn, hs₁⟩ hθ hσ
    ⟨α', s₁', θ', hα', hn', hs₁', hθ', ht', _⟩
  have hLaw : Laws := hLL.1
  have hL := A.isLB
  let T := TFK (R := R) F
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hm.pos.ne'))
  obtain ⟨-, huniq⟩ := hLaw.symLift _ A (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns A.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  have f₁ : (mulT A.A T m).left ≫ (fst T A.A).left = (fst T A.A).left := by
    rw [← Over.comp_left, mulT, lift_fst]
  have f₂ : (translT A.A θ.pt).left ≫ (fst T A.A).left = (fst T A.A).left := by
    rw [← Over.comp_left, translT, lift_fst]
  have key : SecM.ofSec A.A σ = cF R c • SecM.ofSec A.A t := ThetaAct.sv_ext hL fun y J hJ => by
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm
    have a₁ := ThetaLin.sval_of_isTwistPull A.A hσ (𝟙 _) y hJ
    have a₂ := ThetaLin.sval_of_isTwistPull A.A hs₁ (𝟙 _ ≫ (translT A.A θ.pt).left) y hJ
    have a₃ := ThetaPtMove.sv_of_eq_mul hc ((𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mulT A.A T m).left) y hJ
    have b₁ := ThetaLin.sval_of_isTwistPull A.A ht' (𝟙 _) y hJ
    have b₂ := ThetaLin.sval_of_isTwistPull A.A hs₁' (𝟙 _ ≫ (translT A.A θ.pt).left) y hJ
    rw [← val_corr hJ eθ, ← ept, b₂, ← ea _ _ y J hJ] at b₁
    rw [Category.assoc _ (mulT A.A T m).left (fst T A.A).left, f₁, Category.assoc _ _ (fst T A.A).left, f₂] at a₃
    refine a₁.trans (Eq.trans ?_ (congrArg (_ * ·) b₁.symm))
    rw [a₂]
    refine (congrArg (fun q => _ * (_ * q)) a₃).trans ?_
    ring
  exact fun j => congrArg (fun q => q.1 j) key

end GlobalTheory.TestFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.TestVal

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem odd_level (ρ : S.Real) : Odd (S.r * S.N) := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  rw [hj, ρ.N_eq]
  exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow

theorem powFrame_one {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) :
    powFrame A L x τ 1 = τ :=
  congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))

theorem mk_add_smul {X : Type} [AddCommGroup X] (m : ℕ) (χ y : X) :
    (QuotientAddGroup.mk y : X ⧸ (nsmulAddMonoidHom m : X →+ X).range) = QuotientAddGroup.mk (m • χ + y) :=
  QuotientAddGroup.eq.2 ⟨χ, by simp⟩

attribute [local instance] gtGroup in

theorem exists_scale (hL : Laws) (hL₂ : Laws2) {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}
    (u : ρ.UTest p y₀) (l : u.Lab) (h : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) :
    ∃ sc : ℝ, 0 ≤ sc ∧
      (∀ a, ∃ w : u.D.toPre.X, l.yy a = QuotientAddGroup.mk w ∧
        ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ sc * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) ∧
      (∀ a, sc ≠ 0 → ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = sc → a ∈ l.yy.ker) ∧
      ∀ n : ℕ, 2 ≤ n → n ∣ S.r * S.N → ∀ a ∈ l.yy.ker, ∃ a' ∈ l.yy.ker, n • (a' - a) = 0 ∧
        ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ = sc := by
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have := charZero u
  have hm := odd_level ρ
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  obtain ⟨ϖ, hϖ, Q, hQ, v, hv, lam, hlam, v₁, v₂, hq⟩ := exists_val u
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.T.uniformised_model_labelled_torsion_points o Ω S ρ p y₀ u
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.T.exists_frames_on_uniformisedModel_fibre o Ω S ρ p y₀ u x hx
  obtain ⟨t, ht⟩ := hsec 1 ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW u.U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ _ v hv u.A u.G
    u.semi u.U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ _ v hv u.A u.G u.semi u.U w₀ rig hw₀ th ϑ hE hP
    _ hm (isUnit_level u h)
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv).2 r
  have tv : ∀ a z J, Good u.A.L z J → cst (R := u.V) (PadicAlgCl p) z sc *
      @id ((TF (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z) (sA th (ptSecT u.A.A (x a)).left z J) =
      cst (R := u.V) (PadicAlgCl p) z (y₀ ⟨S.th a, S.th_mem a⟩) * @id ((TF (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z)
        (val (powFrame u.A.A u.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := ρ.th_val a
      rw [← powFrame_one (ρ.pt a) (ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x a) ∧ l.yy a = QuotientAddGroup.mk q.y :=
    fun a => by
      obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
      exact ⟨q, (f₁ _ _).2 hq.symm, l.yy_eq a q _ ((f₁ _ _).2 hq.symm) (hx a)⟩
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨S.th a, S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := u.V) (F := PadicAlgCl p)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := u.V) (PadicAlgCl p)).left) u.A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := u.V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    refine ⟨0, le_rfl, fun a => ?_, fun a hne => absurd rfl hne, fun n _ _ a ha => ⟨a, ha, by simp, by simp [z0]⟩⟩
    obtain ⟨q, -, hq⟩ := ex a
    exact ⟨q.y, hq, by simp [z0]⟩
  have hsc : 0 < ‖sc‖ := norm_pos_iff.2 h0
  have tv' : ∀ a z J, Good u.A.L z J → sA th (ptSecT u.A.A (x a)).left z J =
      @id ((TFK (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z)
        (cst (R := u.V) (PadicAlgCl p) z (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)) *
        (val (powFrame u.A.A u.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := u.V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) = 0 ↔ ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = ‖sc‖ := fun a => by
    refine (v₁ _ 0).trans ?_
    rw [norm_mul, norm_inv, Rat.cast_zero, mul_zero, neg_zero, Real.exp_zero, inv_mul_eq_one₀ hsc.ne', eq_comm]
  refine ⟨‖sc‖, hsc.le, fun a => ?_, fun a _ ha => ?_, fun n hn hnm a ha => ?_⟩
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((S.r * S.N) • χ + q.y) = k)
      ⟨0, by
        rintro _ ⟨χ, rfl⟩
        by_cases c : (S.r * S.N) • χ + q.y = 0
        · rw [c, QForm.Q_zero hϖ u.D hQ]
        · exact zero_le_one.trans (QForm.Q_pos hϖ u.D hQ c)⟩ ⟨_, 0, rfl⟩
    refine ⟨_, hq₂.trans (mk_add_smul _ χ _), ?_⟩
    have b := (v₂ _ _).1 (((key q _ hq₁).1 _ _ (he a) (tv' a)).1
      ((Q ((S.r * S.N) • χ + q.y) : ℚ) / ((S.r * S.N) ^ 2 : ℕ)) fun χ' =>
        div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _))
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hsc] at b
    refine b.trans (le_of_eq ?_)
    rw [hq]
    push_cast
    rw [mul_div_assoc]
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨z, hz⟩ := ((key q _ hq₁).1 _ _ (he a) (tv' a)).2 ((nz a).2 ha)
    exact hq₂.trans ((QuotientAddGroup.eq_zero_iff _).2 ⟨z, hz.symm⟩)
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).1 (hq₂.symm.trans ha)
    have hz' : (S.r * S.N) • z = q.y := hz
    let q₀ : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N) := qkMk hB 0 (q.g + iota hB _ (-z)) (by
      rw [smul_add, qk_nsmul hB, ← map_nsmul, ← map_add, smul_neg, hz', add_neg_cancel])
    have e₀ : f q = f q₀ := (f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨-z, by
      rw [smul_neg, hz', add_neg_cancel]; rfl, rfl⟩)
    obtain ⟨q', x', hy', hx', hpow, hval⟩ := (key q₀ (x a) ((f₁ _ _).2 (((f₁ _ _).1 hq₁).trans e₀))).2 n hn hnm rfl
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    have := u.A.isAb.comm
    let X : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
      MonoidHom.mk' (fun a => x a.toAdd) fun a b => xadd _ _
    refine ⟨a', (l.yy_eq a' q' _ hx' (hx a')).trans (by rw [hy']; rfl), xinj ?_, (nz a').1 (hval _ _ (he a') (tv' a'))⟩
    have b : X ((Multiplicative.ofAdd a' * (Multiplicative.ofAdd a)⁻¹) ^ n) = X 1 := by
      rw [map_pow, map_mul, map_inv, map_one]; exact hpow
    rw [sub_eq_add_neg]
    exact b

theorem norm_le_delta {p : ℕ} [Fact p.Prime] (ρ : S.Real) (y₀ : S.R →+* PadicAlgCl p) (a : S.Gam) :
    ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ S.delta y₀ := by
  have : NeZero (S.r * S.N) := ⟨(odd_level ρ).pos.ne'⟩
  exact le_ciSup (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (Set.finite_range _).bddAbove a

theorem main : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ x, y₀ ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : u.D.toPre.X, l.yy x = QuotientAddGroup.mk w ∧ ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) := by
  intro hL hL₂ _ o Ω _ _ _ _ S ρ p _ y₀ u l h a _
  obtain ⟨sc, -, h₁, -, h₃⟩ := exists_scale hL hL₂ u l h
  have h2 : 2 ≤ S.r * S.N := S.N_ge.trans (Nat.le_mul_of_pos_left _ S.r_pos)
  obtain ⟨a', -, -, ha'⟩ := h₃ _ h2 dvd_rfl 0 (zero_mem _)
  obtain ⟨w, hw, b⟩ := h₁ a
  exact ⟨w, hw, b.trans (mul_le_mul_of_nonneg_right (ha' ▸ norm_le_delta ρ y₀ a') (Real.exp_pos _).le)⟩

end GlobalTheory.ZH.TestVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsAtUniformisedTrait
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Rig
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]

theorem rigidification_map_on_values (m : CubeMap A G) {L₀ : LB G.left} {L₁ : LB A.left} (w : LB.Iso L₁ (L₀.pull m.F))
    {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec A) (fun _ => 1)) ρ₁ (m.rigPull L₀ ρ₀)) :
    IsRigidificationPullbackCompatibleIso w m.e ρ₁ ρ₀ := by
  have H := (maps_iff w _ (fun _ => eSec G) _ ρ₁ ρ₀ m.e _ (rigPull_le m.F m.e m.e_comm L₀) (fun _ => rfl)).1 h
  intro Z r z J J' hJ hJ'
  have e : (r ≫ m.e) ≫ eSec G = (r ≫ eSec A) ≫ m.F := by rw [Category.assoc, Category.assoc, m.e_comm]
  refine (val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ m.e) z J
    (fun _ => J ((r ≫ eSec A) ≫ m.F)) (fun _ => congrArg J e)).trans ?_
  refine (H Z r z (fun _ => J ((r ≫ eSec A) ≫ m.F)) (fun _ => J' (r ≫ eSec A)) (fun _ => hJ _) (fun _ => hJ' _)).trans ?_
  rw [Fintype.prod_unique, zpow_one]
  rfl

end Rig

section Move
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem mem_nonzeroLocus_iff_sv {a : ℤ} (s : LB.Sec (LPow A L₁ a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J} (hJ : Good L₁ z J) : r z ∈ nonzeroLocus s ↔ IsUnit (VVRank.sv A s r z J) := by
  have hz := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    have hz' : r z ∈ (LPow A L₁ a T).U k := (T ⊗ A).left.basicOpen_le _ hk
    have hu := (MulFinite.isUnit_gs r z _ hz' _).2 hk
    have e := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z hz' hz
    exact isUnit_of_mul_isUnit_right (e ▸ hu :)
  · intro h
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, (MulFinite.isUnit_gs r z _ hz _).1 h⟩

theorem SecRel.mem_nonzeroLocus (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {s : LB.Sec (LPow A L₁ a T)}
    {s₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w s s₀) (y : (T ⊗ A).left)
    (hy : psi hp τ hτ y ∈ nonzeroLocus s₀) : y ∈ nonzeroLocus s := by
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
  have q := (mem_nonzeroLocus_iff_sv s₀ (𝟙 _ ≫ psi hp τ hτ) y hJ).1 hy
  rw [h _ _ _ _ _ hJ hJ'] at q
  exact (mem_nonzeroLocus_iff_sv s (𝟙 _) y hJ').2 (isUnit_of_mul_isUnit_right q)

theorem SecRel.pullS {a : ℤ} {s : LB.Sec (LPow A L₁ a T)} {s₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w s s₀)
    {T' : Over S'} {T₀' : Over S} (τ' : T'.left ⟶ T₀'.left) (hτ' : τ' ≫ T₀'.hom = T'.hom ≫ f) (ξ : T' ⟶ T)
    (ξ₀ : T₀' ⟶ T₀) (e : τ' ≫ ξ₀.left = ξ.left ≫ τ) :
    SecRel hp τ' hτ' w (VVRank.pullS A a ξ s) (VVRank.pullS G a ξ₀ s₀) := by
  intro Z r z J J' hJ hJ'
  have e' : psi hp τ' hτ' ≫ (ξ₀ ▷ G).left = (ξ ▷ A).left ≫ psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst',
        Category.assoc, Category.assoc, psi_fst', e, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
        ← Over.comp_left, whiskerRight_fst]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', Category.assoc, psi_snd', ← Category.assoc,
        VVRank.whisker_snd_left]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, VVRank.sv_pullS _ _ _ _ _ _ hJ', Category.assoc, e', ← Category.assoc,
    h _ _ _ _ _ hJ hJ', Category.assoc, VVRank.whisker_snd_left]

include hp hτ in

theorem exists_pt_down (x₀ : T₀ ⟶ G) {n : ℕ} (hn : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have hc : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w, hτ]
  let x : T ⟶ A := Over.homMk (hp.1.lift _ _ hc) (hp.1.lift_snd _ _ hc)
  have hx : τ ≫ x₀.left = x.left ≫ φ := (hp.1.lift_fst _ _ hc).symm
  refine ⟨x, hx, Over.OverMorphism.ext (hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩
  rw [← over_pow hp τ hτ hx n, hn, over_one hp τ hτ]

include hp hτ in

theorem exists_pt_up [IsIso τ] (x : T ⟶ A) {n : ℕ} (hn : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  let x₀ : T₀ ⟶ G := Over.homMk (inv τ ≫ x.left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hp.1.w, Over.w_assoc, ← hτ, IsIso.inv_hom_id_assoc])
  have hx : τ ≫ x₀.left = x.left ≫ φ := IsIso.hom_inv_id_assoc _ _
  refine ⟨x₀, hx, Over.OverMorphism.ext ((cancel_epi τ).1 ?_)⟩
  rw [over_pow hp τ hτ hx n, hn, over_one hp τ hτ]

end Move

theorem theta_at_trait : HV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)) (_ : SABMap t' t χ) (_ : PELUnif (maximalIdeal V) t') (σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ))), NZ t.G t.PP.L χ σ → IsGenSec t.G t.PP.L ((1 : ℕ) : ℤ) σ ∧ ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (x' : Sp F ⟶ S) (ξ : Over.mk x' ⟶ Over.mk χ), ξ.left = jFK (R := V) F ≫ jK V → (∀ x (c : F), ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  intro hV E _ _ _ H S t V _ _ _ hC χ t' m P σ hσ
  obtain ⟨hD, hA, hZ⟩ := hC
  obtain ⟨w, hw, hr, -⟩ := m.lin
  have hR : IsRigidificationPullbackCompatibleIso w χ t'.PP.rig t.PP.rig := by
    have q := rigidification_map_on_values m.cm w hr
    rw [m.base] at q
    exact q
  have hp := m.cart
  have hL₀ := t.PP.isLB
  have hL₁ := t'.PP.isLB
  let τ : (Over.mk (𝟙 (Sp V))).left ⟶ (Over.mk χ).left := 𝟙 (Sp V)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp V)))
  have hτ : τ ≫ (Over.mk χ).hom = (Over.mk (𝟙 (Sp V))).hom ≫ χ := rfl
  obtain ⟨σ', hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ σ
  have hσ' : NZ t'.G t'.PP.L (𝟙 (Sp V)) σ' := by
    obtain ⟨g, hg, hg'⟩ := hσ
    obtain ⟨κ, -, h₂⟩ := ThetaPtUp.exists_psi_inv' hp τ hτ
    have e : psi hp τ hτ (κ g) = g := congrArg (fun q => q g) h₂
    refine ⟨κ g, ?_, SecRel.mem_nonzeroLocus hp τ hτ hL₀ hL₁ hs _ (e.symm ▸ hg')⟩
    have e' := congrArg (fun q => q (κ g)) (psi_fst' hp τ hτ)
    exact e'.symm.trans ((congrArg (fst (Over.mk χ) t.G).left e).trans hg)
  have key : ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F]
      (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → IsGenSec t'.G t'.PP.L ((1 : ℕ) : ℤ) σ' ∧ ∀ n : ℕ, Odd n →
      IsUnit (n : V) → 3 ≤ n → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))),
      (∀ x (c : F), ThG t'.G t'.PP.L t'.PP.rig n (VVRank.pullS t'.G _ ξ σ') x (fnOf c) → 0 ≤ v c) ∧
      ∃ x, ∃ c : F, ThG t'.G t'.PP.L t'.PP.rig n (VVRank.pullS t'.G _ ξ σ') x (fnOf c) ∧ v c = 0 := by
    intro ϖ hϖ F _ _ _ v hv
    choose Q hQ using QForm.exists_QVal hϖ P.D
    have q := GlobalTheory.T.thetaConstants_integral_unit_of_closedFibre_nonvanishing hV V hA ϖ hϖ P.D Q hQ F v hv P.A t'.G t'.semi P.U
    dsimp only at q
    rw [P.bundle] at q
    exact q σ' hσ'
  refine ⟨?_, fun ϖ hϖ F _ _ _ v hv n h₁ h₂ h₃ x' ξ hξ => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
    exact ThetaPtUp.isGenSec_up hp τ hτ hw hL₀ hL₁ hs (key ϖ hϖ _ v hv).1
  · let ξ' : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V)) :=
      Over.homMk (jFK (R := V) F ≫ jK V) (Category.comp_id _)
    obtain ⟨k₁, x, c, k₂, k₃⟩ := (key ϖ hϖ F v hv).2 n h₁ h₂ h₃ ξ'
    let τ' : (Over.mk (jFK (R := V) F ≫ jK V)).left ⟶ (Over.mk x').left := 𝟙 (Sp F)
    haveI : IsIso τ' := inferInstanceAs (IsIso (𝟙 (Sp F)))
    have hτ' : τ' ≫ (Over.mk x').hom = (Over.mk (jFK (R := V) F ≫ jK V)).hom ≫ χ :=
      (Category.id_comp _).trans ((Over.w ξ).symm.trans (congrArg (· ≫ χ) hξ))
    have hs' := SecRel.pullS hp τ hτ hs τ' hτ' ξ' ξ
      ((Category.id_comp _).trans (hξ.trans (Category.comp_id _).symm))
    have hi : inv τ' = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
    refine ⟨fun y₀ d hd => ?_, ?_⟩
    · obtain ⟨y, hy, hn⟩ := exists_pt_down hp τ' hτ' y₀ hd.1
      exact k₁ y d (ThG.move hp τ' hτ' hw hL₀ hL₁ hR hy hn hs' hd)
    · obtain ⟨x₀, hx, hn⟩ := exists_pt_up hp τ' hτ' x k₂.1
      have q := ThG.up hp τ' hτ' hw hL₀ hL₁ hR hx hn hs' k₂
      rw [hi] at q
      exact ⟨x₀, c, q, k₃⟩

end GlobalTheory.Ex.OneGen
end
end

