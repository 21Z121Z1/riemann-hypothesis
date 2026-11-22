import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0686
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2609

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PrincipalOfPairing

open GlobalTheory.CechPic

theorem lbIso_sq_diag {k : Type} [Field k] [IsAlgClosed k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {L : LB B.left} (hL : L.IsLB) (hs : Out.Sym B L) {P : LB (G2 B).left} (hP : P.IsLB)
    (hiso : LBIso (abelian₂ B L) P) : LBIso (lbPow L 2) (P.pull (lift (𝟙 B) (𝟙 B) : B ⟶ G2 B).left) := by
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hPow : (lbPow L 2).IsLB := LB.isLB_linComb hL _ _
  have hΘ := exists_gen_theta_of_isAbelianScheme k B hB L hL
  have h₀ : pull (1 : B ⟶ B).left (cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨N, hN, e⟩ := cls_surj (pull (η[B]).left (cls L hL))
    have z : cls N hN = 0 := (cls_eq_zero_iff hN).2 (DVR.exists_gen_of_isLB_local (V := k) N hN)
    rw [← e, z, map_zero]
  have h₁ : cls _ hlam = lam (cls L hL) (fst B B) (snd B B) := cls_cube_two hL _ _ hlam
  have h₂ := lam_mul_left hL hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left, lam.eq_1 _ (𝟙 B)⁻¹, inv_mul_cancel, h₀] at h₂
  have h₃ := exists_gen_neg_of_sym GlobalTheory.lawsAndExpansions.1.1.globalFns hB hL hs
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL] at h₃
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id] at h₃
  have einv : GrpObj.inv (X := B) = (𝟙 B)⁻¹ := by simp [Hom.inv_def]
  rw [einv, add_neg_eq_zero] at h₃
  rw [h₃, Over.id_left, pull_id] at h₂
  refine (cls_eq_iff hPow (pull_isLB hP _)).1 ?_
  rw [cls_lbPow hL 2 hPow, cls_pull hP, ← (cls_eq_iff hlam hP).2 hiso, h₁, pull_lam, lift_fst, lift_snd,
    eq_neg_of_add_eq_zero_left h₂.symm, two_smul]
  abel

theorem exists_principal : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∃ L : LB A.left, L.IsLB ∧ Out.Sym A L ∧ LBIso (abelian₂ A L) PP ∧ Out.RelAmple A L ∧ Out.KTriv A L := by
  intro K _ _ _ A _ _ hA P hP hs hb ha hk
  obtain ⟨L, hL, sL, iL⟩ := GlobalTheory.SymBiextHalf.exists_sym_lam K A hA P hP hs hb
  refine ⟨L, hL, sL, iL, ?_, GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ A hA P hP hk L hL iL⟩
  have := hA.proper
  have hMa := isAmpleLB_of_relAmple_of_isAffine A (pull_isLB hP _) ha
  have h2 : IsAmpleLB (lbPow L 2) := hMa.of_lbIso (isLB_lbPow hL 2) (lbIso_sq_diag hA hL sL hP iL)
  have hLa : IsAmpleLB L := (isAmpleLB_pow_iff hL (by norm_num)).1 h2
  refine relAmple_of_isAmpleLB A hL fun U hU => ?_
  have : CompactSpace (A.hom ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := A.hom) _ U.isOpen hU.isCompact)
  exact hLa.pull_of_isOpenImmersion _

end GlobalTheory.PrincipalOfPairing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiGeneratorsDegenerationLawsSymmetricBala
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

theorem formEq_psi {R : Type} [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) [IsMonHom f]
    (x x' : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (hx : x' = x ≫ f) :
    FormEq (Sum.elim (Sum.elim (PolDeg.lamPts x x') fun k => x.left ≫ w0φ D₀ f k) fun _ : PUnit => eSec D₀.P.A)
      (Sum.elim (Sum.elim PolDeg.negε w0ε) fun _ => (-1 : ℤ)) (fun _ : PUnit => x.left) (fun _ => (-1 : ℤ)) := by
  intro U _ h
  subst hx
  have m₁ : x ≫ padd D₀.P.A (𝟙 _) f = x * (x ≫ f) := (MonObj.comp_mul _ _ _).trans (by simp)
  have m₃ : x ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]) = 1 := by
    rw [← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit _), ← Hom.one_def]
  have m₄ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have e₁ : x.left ≫ (padd D₀.P.A (𝟙 _) f).left = (x * (x ≫ f)).left := by rw [← Over.comp_left, m₁]
  have e₂ : x.left ≫ f.left = (x ≫ f).left := (Over.comp_left _ _ _ _ _).symm
  have e₃ : x.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left := by
    rw [← Over.comp_left, m₃]
  have e₄ : eSec D₀.P.A = (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left := by rw [m₄]; rfl
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
    PolDeg.lamPts, PolDeg.negε, w0φ, w0ε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e₁, e₂, e₃, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

theorem exists_psi_rLaws : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ w0 : O, w0 + star w0 = 1 → ∀ uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ τ' : ∀ y z : D₀.X, LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.PolDeg.lamPts (D₀.c y) (D₀.c z)) GlobalTheory.PolDeg.negε),
    GlobalTheory.UTau0.BalTau ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub onB.toRingAct D₀.c τ' →
    (∀ y z p J, Good D₀.P.L p J → val (τ' y z) (𝟙 _) p J = val (τ' z y) (𝟙 _) p J) →
    ∃ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
      GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ := by
  intro R _ _ _ D₀ O _ _ _ onB hc w0 hw uw huw uw0 τ' hbal hsym
  haveI := onB.hom w0
  haveI := onB.hom (star w0)
  obtain ⟨u, hu, hu0⟩ := exists_ros GlobalTheory.globalFns_holds D₀.P.isAb D₀.P.isLB (onB.act w0) (onB.act (star w0))
    (onB.rosati w0)
  have hfg : padd D₀.P.A (onB.act w0) (onB.act (star w0)) = 𝟙 _ := by
    rw [← onB.map_add, hw, onB.map_one]
  have cadd : ∀ a b, D₀.c (a + b) = D₀.c a * D₀.c b := fun a b => D₀.c_add a b
  have c0 : D₀.c 0 = 1 := by
    have := cadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
  have cneg : ∀ a, D₀.c (-a) = (D₀.c a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_left (by rw [← cadd, neg_add_cancel, c0])
  let t := fun y : D₀.X => LB.mulGen D₀.P.L _ _ _ _
    (LB.mulGen D₀.P.L _ _ _ _ (τ' y (w0 • y)) (LB.pullGen D₀.P.L _ _ uw (D₀.c y).left))
    (LB.invGen D₀.P.L (fun _ : PUnit => eSec D₀.P.A) (fun _ => 1) D₀.rig)
  have ht : ∀ y, (t y).IsGen := fun y => DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hbal.1 y _) (DVR.pullGen_isGen _ _ _ _ huw _))
    (DVR.invGen_isGen _ _ _ _ D₀.rig_gen)
  choose ψ hψ hψv using fun y => exists_gen D₀.P.isLB (formEq_psi D₀ (onB.act w0) (D₀.c y) _ (hc w0 y)) (t y) (ht y)
  have Vψ : ∀ y p J, Good D₀.P.L p J → val (ψ y) (𝟙 _) p J =
      val (τ' y (w0 • y)) (𝟙 _) p J * val uw (D₀.c y).left p J * (rigV D₀ p J)⁻¹ := by
    intro y p J hJ
    rw [hψv y _ _ p J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, Category.id_comp]
    rfl
  have key : ∀ y z p J, Good D₀.P.L p J → tauV D₀ ψ p J y z = val (τ' y z) (𝟙 _) p J := by
    intro y z p J hJ
    have e1 := hbal.2.1 y z (w0 • y + w0 • z) p J hJ
    have e2 := hbal.2.2.1 y (w0 • y) (w0 • z) p J hJ
    have e3 := hbal.2.2.1 z (w0 • y) (w0 • z) p J hJ
    have e4 := hsym z (w0 • y) p J hJ
    have e5 := hbal.2.2.2 w0 u hu hu0 y z p J hJ
    have e6 := hbal.2.2.1 y (w0 • z) (star w0 • z) p J hJ
    rw [← add_smul, hw, one_smul] at e6
    have g := GlobalTheory.T.symmetricPullbackGenerator_second_difference R D₀ (onB.act w0) (onB.act (star w0)) hfg uw huw uw0 u hu hu0 _ (D₀.c y) (D₀.c z) p J hJ
    simp only [cadd, hc] at e1 e2 e3 e6
    unfold tauV
    rw [Vψ _ p J hJ, Vψ _ p J hJ, Vψ _ p J hJ, smul_add]
    simp only [cadd]
    apply Additive.ofMul.injective
    have E := fun {a b : ((𝟙_ (Over (Sp R))).left.presheaf.stalk p)ˣ} (e : a = b) => congrArg Additive.ofMul e
    have a1 := E e1; have a2 := E e2; have a3 := E e3; have a4 := E e4; have a5 := E e5; have a6 := E e6
    have b1 := E g
    simp only [ofMul_mul, ofMul_inv] at a1 a2 a3 a4 a5 a6 b1 ⊢
    linear_combination (norm := abel) a1 + a2 + a3 + b1 + a4 + a5 - a6
  refine ⟨ψ, hψ, ?_, ?_, ?_, ?_⟩
  · intro y y' z p J hJ
    rw [key _ _ p J hJ, key _ _ p J hJ, key _ _ p J hJ]
    exact hbal.2.1 y y' z p J hJ
  · intro y p J hJ
    have C := isCub_cubV D₀.cub hJ
    rw [Vψ _ p J hJ, Vψ _ p J hJ, smul_neg]
    have f1 := hbal.2.1 y (-y) (w0 • y) p J hJ
    have z1 := hbal.2.1 0 0 (w0 • y) p J hJ
    have f2 := hbal.2.2.1 (-y) (w0 • y) (-(w0 • y)) p J hJ
    have z2 := hbal.2.2.1 (-y) 0 0 p J hJ
    rw [add_neg_cancel] at f1 f2
    rw [add_zero] at z1 z2
    have g := GlobalTheory.T.symmetricPullbackGenerator_even_value R D₀ (onB.act w0) uw huw uw0 _ (D₀.c y) p J hJ
    simp only [cneg, hc, c0] at f1 z1 f2 z2 ⊢
    rw [C.face] at z1 z2
    apply Additive.ofMul.injective
    have E := fun {a b : ((𝟙_ (Over (Sp R))).left.presheaf.stalk p)ˣ} (e : a = b) => congrArg Additive.ofMul e
    have a1 := E f1; have a2 := E f2; have a3 := E z1; have a4 := E z2; have b1 := E g
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at a1 a2 a3 a4 b1 ⊢
    linear_combination (norm := abel) b1 + a1 - a2 + a3 - a4
  · intro a u' hu' hu0' y z p J hJ
    rw [key _ _ p J hJ, key _ _ p J hJ]
    exact hbal.2.2.2 a u' hu' hu0' y z p J hJ
  · intro y p J hJ
    rw [key _ _ p J hJ, Vψ _ p J hJ, inv_mul_cancel_right]

end GlobalTheory.UTau0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegArcDataAtUniformiser
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitArcMatch

open GlobalTheory.TraitArc GlobalTheory.TauTwist GlobalTheory.ArcBuild GlobalTheory.ArcOfPoint Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {T : CDVR}

theorem genRel_psi_twist (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
    (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing T.V) F] (y : D.toPre.X) :
    GenRel (isoPullId (idIso D.toPre.P.L) rfl)
      (LB.pullGen _ _ _ (D.toPre.psi y) (jFK (R := T.V) F))
      (LB.pullGen _ _ _ ((D0 (H := H) D hϖ).psi y) (jFK (R := T.V) F))
      ((algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF D hϖ y y / 2)) := by
  have h0 : algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)
  have hq : beF D hϖ y y / 2 = qv D hϖ y := by rw [beF_self]; omega
  let u : Fˣ := Units.mk0 _ h0 ^ (beF D hϖ y y / 2)
  have hu : ((u : Fˣ) : F) = (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF D hϖ y y / 2) := by
    simp only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [← hu]
  refine ArcOfPoint.genRel_id_of_val D.toPre.P.isLB (DVR.pullGen_isGen _ _ _ _ (D.toPre.psi_gen y) _) fun z J hJ => ?_
  have ht : Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (TraitArc.tF D hϖ y (H.w0 • y)) = u⁻¹ := by
    apply Units.ext
    simp only [u, TraitArc.tF, beF_w0 D oD, hq, Units.coe_map, map_zpow, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, zpow_neg]
    show (algebraMap (FractionRing T.V) F) ((((piK hϖ : (FractionRing T.V)ˣ) : FractionRing T.V) ^ qv D hϖ y)⁻¹) = _
    rw [map_inv₀, map_zpow₀]; rfl
  letI := H.starRing
  rw [val_pull hJ, val_pull hJ, Category.id_comp]
  erw [val_psi_twist H.w0 (TraitArc.tF D hϖ) y (jFK (R := T.V) F) hJ]
  rw [show jFK (R := T.V) F = 𝟙 _ ≫ spMap (algebraMap (FractionRing T.V) F) from (Category.id_comp _).symm,
    unitAt_spMap, ht, map_inv, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

theorem exists_isPullDeg_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) (ϖ : T.V) (hϖ : Irreducible ϖ) (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.TraitArc.beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : GlobalTheory.TraitArc.LieCl D oD Dm β b) (hTate : GlobalTheory.TraitArc.TateCl D oD hϖ Dm β b hdiv pA pM) (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp T.V ⟶ Y.X), Y.HasArcData (GlobalTheory.TraitArc.arc D oD hϖ β b hX hw hdiv pA pM hLie hTate) (maximalIdeal T.V) (RingHom.id T.V) ϖ y → ∃ (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), Nonempty (IsPullDeg (RingHom.id T.V) D.toPre P.D.toPre) := by
  intro E _ _ _ H Dm l c O _ β T b D _ oD ϖ hϖ hX hw hdiv pA pM hLie hTate Xo Y y hY
  obtain ⟨t, m, P, φ, he, w, e, h1, h2, h3, -, h5, h6⟩ := hY
  refine ⟨t, m, P, ?_⟩
  have hid : spMap (RingHom.id T.V) = 𝟙 _ := Spec.map_id _
  have he0 : eSec D.toPre.P.A ≫ 𝟙 _ = spMap (RingHom.id T.V) ≫ eSec D.toPre.P.A := by
    rw [hid, Category.comp_id]; exact (Category.id_comp _).symm
  have p : IsGrpPullback D.toPre.P.A D.toPre.P.A (spMap (RingHom.id T.V)) (𝟙 _) := by
    have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
    exact (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr hid.symm rfl
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  let F := AlgebraicClosure (FractionRing T.V)
  have k6 := (h6 F (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) (fun _ => rfl) rfl).1
  have r := (maps_iff (idW D.toPre.P.L) _ (fun _ => eSec D.toPre.P.A) _ D.toPre.rig D.toPre.rig _ _
    (rigPull_le (𝟙 _) _ he0 D.toPre.P.L) (fun _ => rfl)).1 (maps_rig_id D.toPre he0)
  have r' := (maps_iff w _ (fun _ => eSec D.toPre.P.A) _ P.D.toPre.rig D.toPre.rig _ _
    (rigPull_le φ _ he D.toPre.P.L) (fun _ => rfl)).1 h3
  let xe : P.D.toPre.X ≃+ D.toPre.X := e.symm.toAddEquiv
  have hxe : ∀ y, xe (e y) = y := fun y => e.symm_apply_apply y
  obtain ⟨hD, -⟩ := GlobalTheory.ArcData.exists_isPullDeg_id D.toPre P.D.toPre (A₀ := D.toPre.P.A) (M₀ := D.toPre.P.L)
    D.toPre.P.isLB D.toPre.rig p h1 (idW D.toPre.P.L) w
    ((isGen_iff _).1 ((isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.toPre.P.isLB) rfl))) ((isGen_iff _).1 h2)
    r r' xe (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      refine (h5 y).trans ?_
      rw [hid, Category.id_comp, Category.comp_id, hxe]; rfl)
    Wo hWo ψW (jFK (R := T.V) F) (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [hxe]
      exact ⟨_, _, _, genRel_psi_twist D oD hϖ F y, k6 y⟩)
  exact ⟨hD⟩

end GlobalTheory.TraitArcMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackEighthPowerEndomorphismsFieldPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_eighth_power_endomorphisms_field_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] (P : PolAV (Sp R)) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (u' : Sp R ⟶ F.X), IsDiagEnd F W P u' ε → ∀ (K : Type) [Field K] (yK : R →+* K), ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ P.A.left) (_ : IsGrpPullback A.A P.A (spMap yK) φ) (_ : LBIso A.L (P.L.pull φ)) (εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A)), IsDiagEnd F W A (spMap yK ≫ u') εA ∧ ∀ (Y : Over (Sp K)) (x x' : Y ⟶ A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), x'.left ≫ φ = x.left ≫ φ ≫ (ε E).left → x' = x ≫ εA E := by
  first | exact @GlobalTheory.Poinc.DiagPull.exists_pull_field | exact GlobalTheory.Poinc.DiagPull.exists_pull_field | (intros; apply GlobalTheory.Poinc.DiagPull.exists_pull_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDataRealizationStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_data_realization : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.Rows → More p →
  ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m), RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j →
  ∃ (T' : CoreJ (Fm.D x i)) (_ : Algebra T'.Q.c.F (Fm.D x i).what₂.LL) (Rl' : RealDat3 (Fm.D x i) p.P.A3 T'.Q.c.F)
    (cG' : G0 Rl'.Pg (Fm.D x i).R.r ≃* G0g (Fm.D x i).nd) (S' : NX.RatDat (Fm.D x i).ntw) (YS' : NX.NExpRealS Rl' cG' S')
    (F' : Face (Fm.D x i) p.P.A3.A) (κ' : ∀ j : Fin (Fm.D x i).R.m, WeightFamilies.Wt (Fm.D x i) ((j : ℕ) + 1))
    (v₀' : ∀ (j : Fin (Fm.D x i).R.m) (σ : (Fm.D x i).what₂.LL →+* ℂ), (Rl'.MW j σ).Vec)
    (O' : ∀ j, OMDat T'.toCore Rl'.toRealDat j Unit (fun _ => p.P.A3.A.μ0)) (hV' : T'.V ((j : ℕ) + 1) T'.σ₀ = Wc (Fm.D x i) j),
    RatHyp T' Rl' F' κ' v₀' O' t j hV' ∧ (∀ ρ : Setup (Fm.D x i).ntw, RealPin p.R p.cG ρ → RealPin Rl' cG' ρ) ∧
      ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool), RatRow YS' v₀' hρ t j b → RatRow p.nexp p.v₀ hρ t j b := by
  first | exact @GlobalTheory.UnframePt.rat_unframe | exact GlobalTheory.UnframePt.rat_unframe | (intros; apply GlobalTheory.UnframePt.rat_unframe <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointOfPointOverFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_point_of_point_over_field_extension : ∀ (H Q : Scheme.{0}) (φ : H ⟶ Q), LocallyOfFiniteType φ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ Q) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (q : Sp Ω' ⟶ H), q ≫ φ = spMap io ≫ ν → ∃ p : Sp Ω ⟶ H, p ≫ φ = ν := by
  first | exact @GlobalTheory.Mum.exists_pt_of_pt_ext | exact GlobalTheory.Mum.exists_pt_of_pt_ext | (intros; apply GlobalTheory.Mum.exists_pt_of_pt_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootsOfPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerRoot

open IsDedekindDomain Polynomial

theorem exists_ord (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    ∃ v : (FractionRing V)ˣ →* Multiplicative ℤ,
      (∀ x : (FractionRing V)ˣ, 0 ≤ (v x).toAdd → ∃ a : V, algebraMap V _ a = (x : FractionRing V)) ∧
      ∀ (x : (FractionRing V)ˣ) (a : V), algebraMap V _ a = (x : FractionRing V) →
        (0 < (v x).toAdd ↔ a ∈ maximalIdeal V) := by
  let w := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hw : ∀ x : (FractionRing V)ˣ, w x ≠ 0 := fun x => by simp [w]
  refine ⟨MonoidHom.mk' (fun x => Multiplicative.ofAdd (-WithZero.log (w x))) fun x y => ?_, fun x hx => ?_,
    fun x a ha => ?_⟩
  · rw [← ofAdd_add, Units.val_mul, map_mul, WithZero.log_mul (hw x) (hw y), neg_add]
  · refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
    simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_nonneg] at hx
    exact (WithZero.log_le_log (hw x) one_ne_zero).1 (by simpa using hx)
  · simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_pos]
    have h1 : WithZero.log (w x) < 0 ↔ w x < 1 := by
      simpa using WithZero.log_lt_log (hw x) one_ne_zero
    rw [h1, ← ha]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem _ a

theorem exists_nthRoots_ext (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] {I : Type} [Fintype I] (a : I → V) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (f : V →+* W) (s : I → W),
      Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ ∀ k, s k ^ n = f (a k) := by
  classical
  let K := FractionRing V
  haveI : CharZero K := algebraRat.charZero _
  let p : I → K[X] := fun k => X ^ n - C (algebraMap V K (a k))
  have hp : ∀ k, (p k).Monic := fun k => monic_X_pow_sub_C _ (by omega)
  let L := (∏ k, p k).SplittingField
  have hsp : ((∏ k, p k).map (algebraMap K L)).Splits := SplittingField.splits _
  have hroot : ∀ k, ∃ t : L, t ^ n = algebraMap K L (algebraMap V K (a k)) := fun k => by
    have h0 : (∏ k, p k).map (algebraMap K L) ≠ 0 :=
      ((monic_prod_of_monic _ _ fun k _ => hp k).map _).ne_zero
    have h1 : ((p k).map (algebraMap K L)).Splits :=
      hsp.of_dvd h0 (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)))
    obtain ⟨t, ht⟩ := h1.exists_eval_eq_zero (by
      rw [(hp k).degree_map, degree_X_pow_sub_C (by omega)]
      exact_mod_cast (by omega : n ≠ 0))
    refine ⟨t, ?_⟩
    simpa [p, sub_eq_zero] using ht
  choose t ht using hroot
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V K L
  have hs : ∀ k, t k ∈ Set.range (algebraMap W L) := fun k => hint _
    ⟨X ^ n - C (a k), monic_X_pow_sub_C _ (by omega), by simp [ht]⟩
  choose s hs using hs
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap V W, s, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, fun k => IsFractionRing.injective W L ?_⟩
  rw [map_pow, hs, ht]
  exact (RingHom.congr_fun hc (a k)).symm

theorem exists_form {G X : Type} [CommGroup G] [AddCommGroup X] (v : G →* Multiplicative ℤ) (q : X → X → G)
    (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃ β : LinearMap.BilinForm ℤ X, ∀ x y, β x y = (v (q x y)).toAdd := by
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  let F : X → X →ₗ[ℤ] ℤ := fun x =>
    (AddMonoidHom.mk' (fun y => (v (q x y)).toAdd) fun y y' => by simp [hadd']).toIntLinearMap
  exact ⟨(AddMonoidHom.mk' F fun x x' => LinearMap.ext fun y => by simp [F, hadd]).toIntLinearMap,
    fun x y => rfl⟩

theorem isSymBasis_of_basis {X I : Type} [AddCommGroup X] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) X)) :
    IsSymBasis fun k => (ε k : LinearMap.BilinForm ℤ X) := by
  refine ⟨fun k => mem_balForms_int.1 (ε k).2, ε.linearIndependent.map' (Submodule.subtype _) (by simp),
    fun β hβ => ?_⟩
  have h := Submodule.mem_map_of_mem (f := (balForms (id : ℤ → ℤ) X).subtype)
    (ε.mem_span ⟨β, mem_balForms_int.2 hβ⟩)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

theorem exists_roots_of_periods : ∀ (g n : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → 1 ≤ n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (r : ℕ), r ≤ g → ∀ (q : (Fin r → ℤ) → (Fin r → ℤ) → (FractionRing V)ˣ), (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V, w ≠ 0 ∧ (q a a : FractionRing V) = algebraMap V _ w) → ∃ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))), IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x) ∧ ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (fK : FractionRing V →+* FractionRing V') (s : Fin m ⊕ Fin N → V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ ∀ a b, fK (q a b : FractionRing V) = ∏ k, algebraMap V' _ (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) := by
  intro g n φ hφ hn V _ _ _ hV hD r hr q hsym hadd hpos
  obtain ⟨-, -, hcomp, hchar⟩ := hV
  obtain ⟨v, hv1, hv2⟩ := exists_ord V
  obtain ⟨β, hβ⟩ := exists_form v q hsym hadd
  have hβs : ∀ x y, β x y = β y x := fun x y => by rw [hβ, hβ, hsym]
  have hβp : ∀ x, x ≠ 0 → 0 < β x x := fun x hx => by
    obtain ⟨w, hw, -, h⟩ := hpos x hx
    rw [hβ]
    exact (hv2 _ w h.symm).2 hw
  have hβn : ∀ x, 0 ≤ β x x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hβp x hx).le
  obtain ⟨m, ga, c, hga, hc, hβc⟩ := GlobalTheory.ConeInterior.exists_pos_comb_int g φ hφ r hr β hβs
    (GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hβs) hβn)
  obtain ⟨N, ε, hε⟩ := hga.basis
  have hεga : ∀ k, (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) = ga k := fun k => by rw [hε]
  have hsb := isSymBasis_of_basis ε
  obtain ⟨u, hu, -⟩ := existsUnique_coeff hsb q hsym hadd
  have hβv : ∀ x y, β x y = ∑ j, (c j : ℤ) * ga j x y := fun x y => by
    rw [hβc]; simp [LinearMap.sum_apply]
  have hvu : (fun k => v (u k)) = fun k => Multiplicative.ofAdd (Sum.elim (fun j => (c j : ℤ)) 0 k) := by
    refine eq_of_prod_zpow hsb _ _ fun x y => ?_
    simp_rw [← map_zpow, ← map_prod, ← hu]
    apply Multiplicative.toAdd.injective
    rw [← hβ, hβv, toAdd_prod, Fintype.sum_sum_type]
    simp [hεga, mul_comm]
  have hvk : ∀ k, (v (u k)).toAdd = Sum.elim (fun j => (c j : ℤ)) 0 k := fun k => by
    rw [congrFun hvu k]; rfl
  choose a ha using fun k => hv1 (u k) (by rw [hvk]; cases k <;> simp)
  have ha0 : ∀ k, a k ≠ 0 := fun k h => (u k).ne_zero (by rw [← ha, h, map_zero])
  obtain ⟨W, _, _, _, _, f, s, hinj, hfin, hloc, hs⟩ := exists_nthRoots_ext V a hn
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp f) :=
    (IsFractionRing.injective W _).comp hinj
  have hfK : ∀ b, IsFractionRing.lift (K := FractionRing V) hinj' (algebraMap V _ b) =
      algebraMap W (FractionRing W) (f b) := fun b => IsFractionRing.lift_algebraMap hinj' b
  refine ⟨m, N, ε, by simpa only [hεga] using hga, fun x hx => ?_, W, inferInstance, inferInstance, inferInstance, f,
    IsFractionRing.lift hinj', s, ⟨inferInstance, inferInstance, inferInstance, ?_⟩, inferInstance, hinj, hfin, hloc,
    hfK, fun k => ⟨?_, fun h => ?_⟩, fun k => ?_, fun x y => ?_⟩
  · by_contra h
    push_neg at h
    have h1 := hβp x hx
    rw [hβv] at h1
    exact h1.not_ge (Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hεga j ▸ h j))
  · exact charZero_of_injective_ringHom hinj
  · have h1 : a (.inl k) ∈ maximalIdeal V := (hv2 _ _ (ha _)).1 (by rw [hvk]; simpa using hc k)
    intro h
    exact h1 (isUnit_of_map_unit f _ (hs _ ▸ h.pow n))
  · refine ha0 (.inl k) (hinj ?_)
    rw [← hs, h, map_zero, zero_pow (by omega)]
  · have h1 : a (.inr k) ∉ maximalIdeal V := fun h => by
      have := (hv2 _ _ (ha _)).2 h
      rw [hvk] at this
      simp at this
    have h2 : IsUnit (s (.inr k) ^ n) := hs _ ▸ (not_not.1 h1 : IsUnit (a (.inr k))).map f
    exact (isUnit_pow_iff (by omega)).1 h2
  · rw [hu, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, hfK, ← hs, map_pow, zpow_mul, zpow_natCast]

end GlobalTheory.PerRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingBasicOpenOfNearGeneratoStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_basicOpen_of_nearGenerator : ∀ (Z X : Scheme.{0}) (e : X ⟶ Z), IsOpenImmersion e → CompactSpace X → QuasiSeparatedSpace X → ∀ (M : LB Z), M.IsLB → ∀ (r : Γ(X, ⊤)) (O : Z.Opens), (∀ x ∈ X.basicOpen r, e x ∈ O) → ∀ t : LB.Gen (M.pull O.ι), t.IsGen → ∃ σ : LB.Sec (M.pull e), X.basicOpen r ≤ nonzeroLocus σ := by
  first | exact @GlobalTheory.GenNearExtend.exists_sec_of_gen_near | exact GlobalTheory.GenNearExtend.exists_sec_of_gen_near | (intros; apply GlobalTheory.GenNearExtend.exists_sec_of_gen_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingWhereSingleCoefficientStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_where_single_coefficient : ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L), ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) → (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_sum_nonzero | exact GlobalTheory.exists_sec_sum_nonzero | (intros; apply GlobalTheory.exists_sec_sum_nonzero <;> assumption)
end

