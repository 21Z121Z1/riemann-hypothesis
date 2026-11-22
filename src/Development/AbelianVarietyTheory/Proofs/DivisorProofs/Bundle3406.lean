import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3380
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3350
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfAgreeOnClosedFibreDualNumbers
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

namespace GlobalTheory.LogKS

theorem preimage_eq_of_agree_closedFibre : ∀ (k : Type) [Field k] (X B : Scheme.{0}) (h : B ⟶ Sp (DualNumber k)) (π₁ π₂ : B ⟶ X), (∀ (Z : Scheme.{0}) (x : Z ⟶ B) (y : Z ⟶ Sp k), x ≫ h = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ W : X.Opens, π₁ ⁻¹ᵁ W = π₂ ⁻¹ᵁ W := by
  intro k _ X B h π₁ π₂ hyp W
  have hpt : ∀ b : B, π₁ b = π₂ b := by
    intro b
    set x := B.fromSpecResidueField b
    set φ := Spec.preimage (x ≫ h)
    have hφ : Spec.map φ = x ≫ h := Spec.map_preimage _
    have hinr : ∀ c : k, φ.hom (TrivSqZeroExt.inr c) = 0 := by
      intro c
      have : φ.hom (TrivSqZeroExt.inr c) * φ.hom (TrivSqZeroExt.inr c) = 0 := by
        rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
      exact mul_self_eq_zero.mp this
    let ψ : k →+* B.residueField b := φ.hom.comp (TrivSqZeroExt.inlHom k k)
    have hψ : ψ.comp (TrivSqZeroExt.fstHom k k k).toRingHom = φ.hom := by
      refine RingHom.ext fun z => ?_
      conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
      rw [map_add, hinr, add_zero]
      rfl
    have hx : x ≫ h = Spec.map (CommRingCat.ofHom ψ) ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := by
      rw [← hφ, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      rfl
    have e := hyp _ x _ hx
    obtain ⟨s⟩ : Nonempty (Spec (B.residueField b)) := inferInstance
    have h1 : (x ≫ π₁) s = (x ≫ π₂) s := by rw [e]
    simpa [x] using h1
  apply TopologicalSpace.Opens.ext
  ext b
  change π₁ b ∈ W ↔ π₂ b ∈ W
  rw [hpt b]

end GlobalTheory.LogKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDivisorDegreeZeroFiniteFieldCurve
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PrincDegZero

theorem log_card_eq (κ : Type) [Field κ] [Finite κ] (V : Type) [AddCommGroup V] [Module κ V] :
    Real.log (Nat.card V) = Module.finrank κ V * Real.log (Nat.card κ) := by
  by_cases h : Module.Finite κ V
  · have : Finite V := Module.finite_of_finite κ
    rw [Module.natCard_eq_pow_finrank (K := κ)]
    push_cast
    rw [Real.log_pow]
  · rw [Module.finrank_of_not_finite h]
    have : Infinite V := by
      by_contra h'
      have := not_infinite_iff_finite.1 h'
      exact h (Module.Finite.of_finite)
    simp [Nat.card_eq_zero_of_infinite]

theorem log_card_residueField {κ : Type} [Field κ] [Finite κ] {Y : Scheme.{0}} [IsIntegral Y] [Algebra κ Γ(Y, ⊤)]
    [LocallyOfFiniteType (strHom κ Y)] (hd : topologicalKrullDim Y = (0 + 1 : ℕ)) {z : Y}
    (hz : Order.coheight z = 1) :
    Real.log (Nat.card (Y.residueField z)) =
      (interNumRed κ (⟨closure {z}, isClosed_closure⟩ : Closeds Y) (Fin.elim0 : Fin 0 → LB Y) : ℝ) *
        Real.log (Nat.card κ) := by
  have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Y) hd hz
  obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range j = closure {j (genericPoint W)} := by
    rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
  letI := algebraΓAlong κ j
  have hW : topologicalKrullDim W = (0 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
  rw [InterModel.interNumRed_eq_interNumOn _ j _ hrange,
    interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun i => i.elim0), interNum_of_isEmpty]
  have hu (w : W) : w = genericPoint W := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds W) ≤ 0
      from hW.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ W, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec W)
  have hZ : ({genericPoint W} : Set W) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint W} : Set W) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (W.fromSpecResidueField (genericPoint W)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (W.fromSpecResidueField (genericPoint W))
  have : IsAffine W := .of_isIso (inv (W.fromSpecResidueField (genericPoint W)))
  have : IsIso (W.fromSpecResidueField (genericPoint W)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (j.residueFieldMap (genericPoint W)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := W.residue_surjective _ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective _ a
    exact ⟨Y.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((W.fromSpecResidueField (genericPoint W)).appTop ≫
      (Scheme.ΓSpecIso (W.residueField (genericPoint W))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(W, ⊤) ≃ Y.residueField (j (genericPoint W)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, log_card_eq κ]
  push_cast
  ring

end GlobalTheory.PrincDegZero

namespace GlobalTheory.PrincDegZero

theorem finsum_ord_mul_log_card_eq_zero : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → topologicalKrullDim Y = (1 : ℕ) → ∀ (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Y, ⊤)] (f : Y.functionField), f ≠ 0 → ∑ᶠ z, (Scheme.ord f z : ℝ) * Real.log (Nat.card (Y.residueField z)) = 0 := by
  intro k _ Y _ _ q hA hd l _ _ f hf
  have : Module.Finite ℤ k := hA.finite
  have : AlgebraicGeometry.IsNoetherian Y := hA.isNoetherian
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨hpr, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hA.isProjOver
  have hp : IsProjOver (strHom (ZMod l) Y) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l)) = q ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod l) Y ≫ spMap (Int.castRingHom (ZMod l))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod l) Y) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨this, H, hH⟩
  have : IsProper (strHom (ZMod l) Y) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hd' : topologicalKrullDim Y = (0 + 1 : ℕ) := hd
  let r : (LB.triv Y).ι → Y.functionFieldˣ := fun _ => Units.mk0 f hf
  have hr : IsRatSec (LB.triv Y) r := fun _ _ h => by simp [r]
  have hM := LB.isLB_triv Y
  have key := GlobalTheory.ratSec_cycle_formula (ZMod l) Y hp 0 hd.le (LB.triv Y) hM Fin.elim0 (fun i => i.elim0) r hr
  rw [interNum_eq_zero_of_cls_eq_zero (ZMod l) _ (isLB_cons hM fun i => i.elim0) 0 (cls_triv _)] at key
  have hm (z : Y) : (divOfRatSec hM hr).mult z = Scheme.ord f z :=
    ((presents_divOfRatSec hM hr).isEqn PUnit.unit z trivial).mult_eq
  have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hM hr).mult w *
      interNumRed (ZMod l) (⟨closure {w}, isClosed_closure⟩ : Closeds _) (Fin.elim0 : Fin 0 → LB Y) :=
    (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
  have em := (AddMonoidHom.mulRight (Real.log (Nat.card (ZMod l)))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
  rw [← key] at em
  simp only [map_zero] at em
  refine (finsum_congr fun z => ?_).trans em.symm
  change (Scheme.ord f z : ℝ) * _ = (((divOfRatSec hM hr).mult z * _ : ℤ) : ℝ) * _
  rw [hm]
  by_cases hz : Scheme.ord f z = 0
  · simp [hz]
  have hc : Order.coheight z = 1 := by
    by_contra h
    exact hz (Scheme.ord_eq_zero_of_coheight_neq_one h f)
  rw [Int.cast_mul, mul_assoc, log_card_residueField (κ := ZMod l) hd' hc]

end GlobalTheory.PrincDegZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEqTauFromSignRelationFourTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PsiSignRel

open GlobalTheory.UT.SymFrame

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem act_zero' (o : D.OAct O) : o.onB.act (0 : O) = 1 := by
  have h := o.onB.map_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem act_add' (o : D.OAct O) (a c : O) : o.onB.act a * o.onB.act c = o.onB.act (a + c) :=
  (o.onB.map_add a c).symm

theorem act_comp' (o : D.OAct O) (a c : O) : o.onB.act a ≫ o.onB.act c = o.onB.act (c * a) :=
  (o.onB.map_mul c a).symm

theorem act_natCast' (o : D.OAct O) (n : ℕ) : o.onB.act (n : O) = 𝟙 D.P.A ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero', pow_zero]
  | succ n ih => rw [Nat.cast_succ, ← act_add', ih, o.onB.map_one, pow_succ]

theorem act_pow' (o : D.OAct O) (a : O) (n : ℕ) : o.onB.act a ^ n = o.onB.act ((n : O) * a) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, act_zero']
  | succ n ih => rw [pow_succ, ih, act_add', Nat.cast_succ, add_one_mul]

theorem prod_gam {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x : T ⟶ A) {U : Type} [CommGroup U]
    (k : (T.left ⟶ A.left) → U) :
    ∏ i : Fin 4, k (x.left ≫ (![(𝟙 A ^ 5).left, (𝟙 A ^ 4).left, 𝟙 _, (1 : A ⟶ A).left] : Fin 4 → _) i) ^
      (![2, -3, -2, 3] : Fin 4 → ℤ) i =
      k (x ^ 5).left ^ 2 * (k (x ^ 4).left ^ 3)⁻¹ * (k x.left ^ 2)⁻¹ * k (1 : T ⟶ A).left ^ 3 := by
  rw [Fin.prod_univ_four]
  show k (x ≫ 𝟙 A ^ 5).left ^ (2 : ℤ) * k (x ≫ 𝟙 A ^ 4).left ^ (-3 : ℤ) * k (x ≫ 𝟙 A).left ^ (-2 : ℤ) *
    k (x ≫ 1).left ^ (3 : ℤ) = _
  rw [MonObj.comp_pow, MonObj.comp_pow, MonObj.comp_one, Category.comp_id, zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat,
    zpow_ofNat, zpow_ofNat]

set_option maxHeartbeats 1600000 in

theorem core_id (hG : GlobalFnsSt) (o : D.OAct O) (w : O) (u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w)) (hu : Normd u)
    (gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]))
    (hgam : Normd gam)
    (ra : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (o.onB.act (star (1 + w))) (o.onB.act (1 + w))) rosatiε))
    (hra : GlobalTheory.TorusExt.IsRos D.P.L (o.onB.act (star (1 + w))) (o.onB.act (1 + w)) ra)
    (rw' : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (o.onB.act (star w)) (o.onB.act w)) rosatiε))
    (hrw : GlobalTheory.TorusExt.IsRos D.P.L (o.onB.act (star w)) (o.onB.act w) rw')
    (hw : w + star w = 1) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (z : T.left) {J} (hJ : Good D.P.L z J) :
    val u (b ^ 4).left z J * val₂ ra z J ((b ^ 4) ≫ o.onB.act (1 + w)) b ^ 2 * val gam (b ≫ o.onB.act (1 + w)).left z J =
      th D z J (b ^ 4 * b ^ 4) ((b ^ 4) ≫ o.onB.act (star w * w)) b ^ 2 * th D z J (b ^ 4) (b ^ 4) b ^ 2 *
        val gam b.left z J ^ 2 * val₂ rw' z J ((b ^ 4) ≫ o.onB.act w) b ^ 2 * val gam (b ≫ o.onB.act w).left z J := by
  have hm : ∀ t : O, IsMonHom (o.onB.act t) := o.onB.hom
  have Gu := (grep_gen (Y := D.P.A) u hu.1 (o.onB.act 4).left).congr (P' := fun _ _ h =>
      h (o.onB.act 4 * (o.onB.act 4 ≫ o.onB.act w)).left * (h (o.onB.act 4).left ^ 2)⁻¹ *
        (h (o.onB.act 4 ≫ o.onB.act w).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ 2)
    (fun _ _ h => GlobalTheory.PsiWZeroPull.prod_four _ _ h) (fun _ _ _ _ _ => rfl)
  have Gra := (grep_gen (Y := D.P.A) ra hra.1 (lift (o.onB.act 4 ≫ o.onB.act (1 + w)) (𝟙 D.P.A)).left).congr
    (fun _ _ h => prod_ros _ _ _ _ h) (fun _ _ _ _ _ => rfl)
  have Grw := (grep_gen (Y := D.P.A) rw' hrw.1 (lift (o.onB.act 4 ≫ o.onB.act w) (𝟙 D.P.A)).left).congr
    (fun _ _ h => prod_ros _ _ _ _ h) (fun _ _ _ _ _ => rfl)
  have Gga := (grep_gen (Y := D.P.A) gam hgam.1 (o.onB.act (1 + w)).left).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Ggw := (grep_gen (Y := D.P.A) gam hgam.1 (o.onB.act w).left).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Ggb := (grep_gen (Y := D.P.A) gam hgam.1 (Over.Hom.left (𝟙 D.P.A))).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Gt2 := grep_cub (D := D) (Y := D.P.A) (o.onB.act 4 * o.onB.act 4) (o.onB.act 4 ≫ o.onB.act (star w * w)) (𝟙 D.P.A)
  have Gt1 := grep_cub (D := D) (Y := D.P.A) (o.onB.act 4) (o.onB.act 4) (𝟙 D.P.A)
  have key := (((Gu.mul (Gra.pow 2)).mul Gga).mul (((((Gt2.pow 2).mul (Gt1.pow 2)).mul (Ggb.pow 2)).mul
    (Grw.pow 2)).mul Ggw).inv).triv hG (fun U _ h => by
      clear Gu Gra Grw Gga Ggw Ggb Gt2 Gt1
      have e1 : 𝟙 D.P.A = o.onB.act 1 := o.onB.map_one.symm
      have e0 : (1 : D.P.A ⟶ D.P.A) = o.onB.act 0 := (act_zero' o).symm
      have hsw : star w = 1 - w := eq_sub_of_add_eq' hw
      simp only [e1, e0, act_add', act_comp', act_pow', star_add, star_one, hsw]
      ring_nf
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
      abel) (fun y I hI => by
      clear Gu Gra Grw Gga Ggw Ggb Gt2 Gt1
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      have o1 : ∀ t : O, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left ≫ (o.onB.act t).left =
          (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left := fun t => by
        rw [← Over.comp_left, MonObj.one_comp]
      have l1 : ∀ t t' : O, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left ≫
          (lift (o.onB.act t ≫ o.onB.act t') (𝟙 D.P.A)).left =
          (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) 1).left := fun t t' => by
        rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, MonObj.one_comp, MonObj.one_comp]
      beta_reduce
      rw [o1, l1, l1, o1, o1, Over.id_left, Category.comp_id, normd_one hu hI, normd_one hgam hI]
      have r1 := hra.val_origin hI
      have r2 := hrw.val_origin hI
      unfold val₂ at r1 r2
      rw [r1, r2]
      simp only [MonObj.comp_mul, MonObj.one_comp, Category.comp_id, _root_.mul_one, C.face, one_pow, inv_one, normd_one hgam hI]) T b z J hJ
  have c4 : b ≫ o.onB.act 4 = b ^ 4 := by
    have := act_natCast' o 4
    rw [Nat.cast_ofNat] at this
    rw [this, comp_id_pow]
  beta_reduce at key
  simp only [← Over.comp_left, comp_lift, ← Category.assoc, c4, MonObj.comp_mul, Category.comp_id] at key
  exact mul_inv_eq_one.1 key

set_option maxHeartbeats 800000 in

theorem sign_rel : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (O : Type) [CommRing O] [StarRing O] [Module O D.X] (o : D.OAct O) (w : O), w + star w = 1 → ∀ u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w), Normd u → ∀ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam → ∀ p q r : QkPt D F 4, q.y = w • p.y → r.y = (1 + w) • p.y → GtAct o w p.g q.g → GtAct o (1 + w) p.g r.g → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ s s' s'' : ((TF (R := R) F).left.presheaf.stalk z)ˣ, s * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J → s' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (q.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (q.g.s q.y) (𝟙 _) z J ^ 2 * val gam q.g.b.left z J → s'' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (r.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (r.g.s r.y) (𝟙 _) z J ^ 2 * val gam r.g.b.left z J → s'' = s ^ 2 * s' → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) * val u (cP D (TF (R := R) F) p.y).left z J = @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J := by
  intro R _ _ D F _ _ O _ _ _ o w hw u hu gam hgam p q r hq hr hgq hgr z J hJ s s' s'' hs hs' hs'' hss
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  have hb4 : cP D (TF (R := R) F) p.y = p.g.b ^ 4 := cPoint_y p
  obtain ⟨qb, qv⟩ := (GlobalTheory.TorusExt.gtAct_iff_val hG o w p.g q.g).1 hgq
  obtain ⟨rb, rv⟩ := (GlobalTheory.TorusExt.gtAct_iff_val hG o (1 + w) p.g r.g).1 hgr
  have eq1 := qv (w • p.y) z J hJ
  have eq2 := rv ((1 + w) • p.y) z J hJ
  have sm1 : star w • w • p.y = (star w * w) • p.y := smul_smul _ _ _
  have sm2 : star (1 + w) • (1 + w) • p.y = (p.y + p.y) + (star w * w) • p.y := by
    rw [smul_smul, show star (1 + w) * (1 + w) = 1 + 1 + star w * w by
      rw [star_add, star_one]; linear_combination hw, add_smul, add_smul, one_smul]
  have e3 : (1 + w) • p.y = p.y + w • p.y := by rw [add_smul, one_smul]
  rw [sm1, GlobalTheory.TorusExt.cPoint_smul o, hb4] at eq1
  rw [sm2, GlobalTheory.TorusExt.cPoint_smul o, hb4] at eq2
  have g1 := GlobalTheory.TorusExt.charVal_add p.g hJ p.y p.y
  have g2 := GlobalTheory.TorusExt.charVal_add p.g hJ (p.y + p.y) ((star w * w) • p.y)
  rw [cPoint_add, GlobalTheory.TorusExt.cPoint_smul o, hb4] at g2
  rw [hb4] at g1
  have cid := core_id hG o w u hu gam hgam (GlobalTheory.TorusExt.rosGen hG o (1 + w)) (GlobalTheory.TorusExt.rosGen_isRos hG o (1 + w))
    (GlobalTheory.TorusExt.rosGen hG o w) (GlobalTheory.TorusExt.rosGen_isRos hG o w) hw p.g.b z hJ
  have vτ : @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) =
      @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi ((1 + w) • p.y)) (jFK (R := R) F) z J) *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi p.y) (jFK (R := R) F) z J))⁻¹ *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (w • p.y)) (jFK (R := R) F) z J))⁻¹ *
        (rigV D (TF (R := R) F).hom z J)⁻¹ := by
    rw [e3]
    exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans
        (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans rfl))))
  have gq : val gam q.g.b.left z J = val gam (p.g.b ≫ o.onB.act w).left z J := by rw [qb]
  have gr : val gam r.g.b.left z J = val gam (p.g.b ≫ o.onB.act (1 + w)).left z J := by rw [rb]
  rw [hq, gq] at hs'
  rw [hr, gr] at hs''
  rw [vτ, hb4]
  simp only [id_eq] at hs hs' hs'' ⊢
  apply Additive.ofMul.injective
  have E := fun {a c : ((TF (R := R) F).left.presheaf.stalk z)ˣ} (e : a = c) => congrArg Additive.ofMul e
  have hs := E hs; have hs' := E hs'; have hs'' := E hs''; have hss := E hss
  have eq1 := E eq1; have eq2 := E eq2; have g1 := E g1; have g2 := E g2; have cid := E cid
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at hs hs' hs'' hss eq1 eq2 g1 g2 cid ⊢
  linear_combination (norm := module) hs'' - 2 • hs - hs' - hss + 2 • eq2 - 2 • eq1 + 2 • g2 + 2 • g1 + cid

end GlobalTheory.PsiSignRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartRestrictionIsWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod

theorem isWt_fourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → W ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α W (rsT (τ.f fun _ => j) W) := by
  intro R _ _ Q Ω _ _ _ oa Y k α σ τ hT j W _ hW
  exact GlobalTheory.Heat.TermWt.isWt_term Y k α σ τ hT (fun _ => j) W fun _ hx => Set.mem_iInter.2 fun _ => hW hx

end GlobalTheory.HeatMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermLocalFunctionIsWeightStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudFourierTerm_localFunction_isWeight : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α (Y.q.left ⁻¹ᵁ V) (rsT (τ.f fun _ => j) (Y.q.left ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.Heat.isWt_rsT_of_isTerm | exact GlobalTheory.Heat.isWt_rsT_of_isTerm | (intros; apply GlobalTheory.Heat.isWt_rsT_of_isTerm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudProjectionSectionValuesIdentityStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudProjection_sectionValues_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α) (C : R), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval σ' Y.q.left y J = sval σ'' Y.q.left y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval σ Y.q.left y J) → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom C) * sval σ x.left z J := by
  first | exact @GlobalTheory.FourierDescent.values_identity | exact GlobalTheory.FourierDescent.values_identity | (intros; apply GlobalTheory.FourierDescent.values_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudShiftUnitIdentityFractionFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudShift_unitIdentity_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Q.TauBimult → ∀ (k : ℕ) (mu α : Q.X) (xp : 𝟙_ (Over (Sp R)) ⟶ Y.H) (A₀ B₀ P₀ : R) (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1)) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left ≫ Y.q.left] ![1, -1])), xp ≫ Y.q = Q.c mu → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z A₀ * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 Z) z J).val = cst (g ≫ jK R) z B₀ * (val (Q.tau mu α) g z J).val) → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi mu) g z J).val = cst (g ≫ jK R) z P₀ * (val ψ₀ (g ≫ jK R) z J).val) → (∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ xp⁻¹))).s mu) (𝟙 _) z J = 1) → ∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) k mu α) → ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (pp : Over.mk (g ≫ jK R) ⟶ DegPre.BF Q (FractionRing R)) (yp : Over.mk (g ≫ jK R) ⟶ Y.H), (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g → pp ≫ DegPre.prB Q (FractionRing R) = yp ≫ Y.q → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z B₀ * (val u (show Z ⟶ _ from pp.left) z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 Z) z J).val * ((val e (show Z ⟶ Y.H.left from (yp * (toUnit _ ≫ xp)).left) z J) ^ k).val = cst (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 Z) z J).val := by
  first | exact @GlobalTheory.ShiftUnit.shift_unit_identity | exact GlobalTheory.ShiftUnit.shift_unit_identity | (intros; apply GlobalTheory.ShiftUnit.shift_unit_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealDataWeightVectorFamilyCore
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.Closing3

theorem primRows3_typesSep3 : Hypotheses3 → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → PrimRows3 R F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr := by
  intro P hRSW hHL eps heps
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.multiplicity_one_rational_rows_sized P eps heps
  refine ⟨x₀, ?_⟩
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O L hLe hLx hSz hPar hT hG hM hRT
  obtain ⟨_hGiven, hGS, hCD, hLI, _hTR, _hUI, _hUIW⟩ := GlobalTheory.T.multiplicity_one_gives_lift_data P R F hT hM
  obtain ⟨hOk, hGU, hGE, _hBlk, hA, hB⟩ := GlobalTheory.T.multiplicity_one_gives_unit_equiv P R F hT hM
  obtain ⟨hPos, hK, hH2⟩ := hx₀ R F L hLe hLx hSz hPar hT hM hRT
  obtain ⟨hLT, hLTB, hML⟩ := GlobalTheory.T.liftTests_modularLattice_of_coreCompatibility T R F κ v₀ O hT hG
  have hU : R.toRealDat.LUnif := hG.unif
  obtain ⟨_hLev, _hW, hHk, hTS, htr⟩ := GlobalTheory.T.lift_test_positive_levels_kappa P R F hT hM hU hLT hPos hK
  obtain ⟨hGal, hPP⟩ := GlobalTheory.T.real_data_weight_vector_family P hRSW hHL T R F κ v₀ O hT hG hM hRT hPos hK
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hOnto := GlobalTheory.T.partial_L_function_of_hypotheses P.q5 P.q4 P.q2 P.q1 P.q7 P.q9 P.q10 P.q11 hRSW hHL R F hT.ok hT.char hT.ex hT.host hT.params
    hT.ccK hT.guard hT.types hOk.2 hGE hU
  have hPrim := GlobalTheory.primRows3_of_parts P.q2 P.q1 R F hLI hT.ok hT.char hT.ex hJ hGS hCD hM hOk.1 hOk.2 hHk hGU hGE hRT hLT hLTB
    hOnto hPos hPP hH2 hB hU hML hA hGal
  exact ⟨hPrim, hTS, htr⟩

end GlobalTheory.Closing3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformationStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigid_chart_dual_number_deformation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), IsKS Y.t (interior Y) U v D.1 Θ → IsKS Y.t (interior Y) U v D.1 Θ' → Θ = Θ' := by
  first | exact @GlobalTheory.KSUniq.isKS_unique_model | exact GlobalTheory.KSUniq.isKS_unique_model | (intros; apply GlobalTheory.KSUniq.isKS_unique_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelIntegralToroidalOfPolarisedChartsForFan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem siegelToroidalIntegral_of_polCharts :
    GlobalTheory.Published.SiegelToroidalPolCharts → GlobalTheory.Published.SiegelToroidalIntegral :=
  GlobalTheory.T.siegelIntegralToroidal_of_polarisedCharts GlobalTheory.T.exists_invariant_smoothProjFan_noSelfIntersections

end GlobalTheory
end

