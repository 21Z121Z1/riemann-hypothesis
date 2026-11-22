import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3651
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3654
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3652
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3455
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3645
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDegreeOneBiholomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.FinUnram

theorem formallyUnramified_of_dual_const : ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R] [Module.Finite K R], (∀ (φ : R →ₐ[K] DualNumber K) (r : R), (φ r).snd = 0) → Algebra.FormallyUnramified K R := by
  intro K _ _ R _ _ _ H
  haveI : Algebra.FiniteType K R := inferInstance
  refine GlobalTheory.TangentCrit.formallyUnramified_of_dual_const_field (K := K) (A := K) (B := R)
    (fun φ hK _ b => ?_)
  exact H { φ with commutes' := hK } b

end GlobalTheory.FinUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedOfDegDataFactorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentFactor_uniformised_of_degData_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G₁ : Over (Sp R₁)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (U₁ : Unif (maximalIdeal R₁) D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G' U'.LG.L).pull (β₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  first | exact @GlobalTheory.Mum.factor_unif | exact GlobalTheory.Mum.factor_unif | (intros; apply GlobalTheory.Mum.factor_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFinrankEqNormPowStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_and_finrank_act_eq_norm_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ), l.Prime → (l : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F) →
    ∀ c : 𝓞 F, c ≠ 0 → IsFinite (ρ.act c).left ∧
      (ρ.act c).left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) =
        (Algebra.norm ℤ c).natAbs ^ d := by
  first | (exact @GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow) | (exact GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow) | (intros; apply GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyOfSimilitudePullbackObjects
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ESPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem hom_ext_of_cart {A : Over S} {A₁ : Over S'} [GrpObj A] [GrpObj A₁] {φ : A₁.left ⟶ A.left}
    (h : IsGrpPullback A₁ A f φ) {T : Over S'} {u v : T ⟶ A₁} (e : u.left ≫ φ = v.left ≫ φ) : u = v :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w u, Over.w v]))

theorem exists_baseChange {A B : Over S} {A₁ B₁ : Over S'} [GrpObj A] [GrpObj B] [GrpObj A₁] [GrpObj B₁]
    {φ : A₁.left ⟶ A.left} {χ : B₁.left ⟶ B.left} (hA : IsGrpPullback A₁ A f φ) (hB : IsGrpPullback B₁ B f χ)
    (ψ : A ⟶ B) : ∃ ψ₁ : A₁ ⟶ B₁, ψ₁.left ≫ χ = φ ≫ ψ.left :=
  ⟨Over.homMk (hB.1.lift (φ ≫ ψ.left) A₁.hom (by rw [Category.assoc, Over.w ψ, hA.1.w]))
    (hB.1.lift_snd _ _ _), hB.1.lift_fst _ _ _⟩

theorem grpSchemeSquareProductMap_comp_fst {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    Hecke.sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    Hecke.sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem isPIsog_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N c : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N s) (o₁ o₁' : Obj b N s') (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := by
  intro p _ D R _ b N c S S' s s' f o o' o₁ o₁' m m' ψ hψ
  obtain ⟨hk, hm, hact, heta, ⟨hP⟩, ψ', hm', h₁, h₂⟩ := hψ
  obtain ⟨ψ₁, sq⟩ := exists_baseChange m.cart m'.cart ψ
  obtain ⟨ψ₁', sq'⟩ := exists_baseChange m'.cart m.cart ψ'
  haveI := hm
  haveI := hm'
  have hm₁ : IsMonHom ψ₁ := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback m.cart m'.cart ψ ψ₁ sq
  have hm₁' : IsMonHom ψ₁' := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback m'.cart m.cart ψ' ψ₁' sq'
  have hsq2 : Hecke.sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ Hecke.sq2 ψ := by
    apply Over.tensorObj_ext
    · change (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (fst o'.A o'.A).left
      have l : (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, m'.sq.1, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, Category.assoc, sq]
      have r : (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (fst o'.A o'.A).left = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, grpSchemeSquareProductMap_comp_fst, ← Category.assoc, m.sq.1, Category.assoc]
      exact l.trans r.symm
    · change (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (snd o'.A o'.A).left
      have l : (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, m'.sq.2, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, Category.assoc, sq]
      have r : (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (snd o'.A o'.A).left = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, grpSchemeSquareProductMap_comp_snd, ← Category.assoc, m.sq.2, Category.assoc]
      exact l.trans r.symm
  refine ⟨ψ₁, ⟨hk, hm₁, fun a => ?_, fun x => ?_, ⟨?_⟩, ψ₁', hm₁', ?_, ?_⟩, sq.symm⟩
  · apply hom_ext_of_cart m'.cart
    have e1 : (o₁.act.act a ≫ ψ₁).left ≫ m'.φ = m.φ ≫ (o.act.act a ≫ ψ).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, sq, ← Category.assoc, m.act, Category.assoc]
    have e2 : (ψ₁ ≫ o₁'.act.act a).left ≫ m'.φ = m.φ ≫ (ψ ≫ o'.act.act a).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, m'.act, ← Category.assoc, sq, Category.assoc]
    rw [e1, e2, hact a]
  · apply hom_ext_of_cart m'.cart
    have e1 : (o₁.eta x ≫ ψ₁).left ≫ m'.φ = f ≫ (o.eta x ≫ ψ).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, sq, ← Category.assoc, m.eta, Category.assoc]
    rw [e1, m'.eta, heta x]
  · have hL₁ : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hL₁ (pull_isLB o₁'.isLB _)).1 ?_
    have e₁ := (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol
    have e₂ := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol
    have e₃ := (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB o'.isLB (Hecke.sq2 ψ))).2 hP
    rw [GlobalTheory.BirigidPow.cls_lbPow o.isLB, GlobalTheory.CechPic.cls_pull o'.isLB] at e₃
    rw [GlobalTheory.CechPic.cls_pull o.isLB] at e₁
    rw [GlobalTheory.CechPic.cls_pull o'.isLB] at e₂
    rw [GlobalTheory.BirigidPow.cls_lbPow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB, e₂, ← GlobalTheory.CechPic.pull_comp, hsq2,
      GlobalTheory.CechPic.pull_comp, ← e₃, map_nsmul, ← e₁]
  · apply hom_ext_of_cart m.cart
    rw [ESDual.pow_left_comm m.cart c, Over.comp_left, Category.assoc, sq', ← Category.assoc, sq, Category.assoc,
      ← Over.comp_left, h₁]
  · apply hom_ext_of_cart m'.cart
    rw [ESDual.pow_left_comm m'.cart c, Over.comp_left, Category.assoc, sq, ← Category.assoc, sq', Category.assoc,
      ← Over.comp_left, h₂]

end GlobalTheory.UPel.HT.ESPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerOfCommutingHeatOperatorsRaynaud
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

namespace GlobalTheory.KBracket

theorem exists_der_ext {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (δ : Derivation ℤ A A) : ∃ δS : Derivation ℤ S S, ∀ a, δS (algebraMap A S a) = algebraMap A S (δ a) := by
  let h : A →+* DualNumber S :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A S a) + TrivSqZeroExt.inr (algebraMap A S (δ a))
      map_one' := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz, Algebra.smul_def, mul_comm, add_comm, -DualNumber.inr_eq_smul_eps]
      map_zero' := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
      map_add' := fun a b => by ext <;> simp [add_add_add_comm, -DualNumber.inr_eq_smul_eps] }
  have hu : ∀ m : M, IsUnit (h m) := fun m => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [h] using IsLocalization.map_units S m)
  let L : S →+* DualNumber S := IsLocalization.lift hu
  have hfst : ∀ x, (L x).fst = x := by
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp L = RingHom.id S := by
      refine IsLocalization.ringHom_ext M (RingHom.ext fun a => ?_)
      simp [L, h, -DualNumber.inr_eq_smul_eps]
    exact fun x => congr($this x)
  let δS : Derivation ℤ S S := Derivation.mk'
    ((show S →+ S from
      { toFun := fun x => (L x).snd, map_zero' := by simp, map_add' := fun x y => by simp }).toIntLinearMap)
    (fun x y => by
      show (L (x * y)).snd = x • (L y).snd + y • (L x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
      simp [mul_comm])
  refine ⟨δS, fun a => ?_⟩
  show (L (algebraMap A S a)).snd = _
  simp [L, h, Algebra.smul_def, -DualNumber.inr_eq_smul_eps]

theorem exists_der_fun {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (δ : Derivation ℤ A A) : ∃ f : S →+ S, (∀ x y, f (x * y) = x * f y + y * f x) ∧
      ∀ a, f (algebraMap A S a) = algebraMap A S (δ a) := by
  obtain ⟨δS, hδS⟩ := exists_der_ext M δ (S := S)
  exact ⟨δS.toLinearMap.toAddMonoidHom, fun x y => by simp [Derivation.leibniz, smul_eq_mul], hδS⟩

theorem exists_der_frac (Ω : Type) [CommRing Ω] [IsDomain Ω] (δ : Derivation ℤ Ω Ω) :
    ∃ δS : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ ω, δS (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω) := by
  obtain ⟨f, hf1, hf2⟩ := exists_der_fun (nonZeroDivisors Ω) δ (S := FractionRing Ω)
  have hf0 : f 1 = 0 := by
    have h11 := hf1 1 1
    rw [_root_.mul_one, _root_.one_mul] at h11
    linear_combination -h11
  have hfc : ∀ (c : ℤ) (y : FractionRing Ω), f ((c : FractionRing Ω) * y) = (c : FractionRing Ω) * f y := by
    intro c y
    have h2 : f (c : FractionRing Ω) = 0 := by
      rw [← zsmul_one, map_zsmul, hf0]
      simp
    rw [hf1, h2]
    simp
  refine ⟨{ toFun := f
            map_add' := f.map_add
            map_smul' := (fun c y => ?_)
            map_one_eq_zero' := hf0
            leibniz' := (fun x y => ?_) }, hf2⟩
  · simp only [RingHom.id_apply]
    rw [Algebra.smul_def, eq_intCast, zsmul_eq_mul]
    exact hfc c y
  · exact hf1 x y

theorem isKS_of_heat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix h.Θ) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab Y n vH dd hdd v' hv' D h hB hDef
  letI := H.starRing
  have hsm : Smooth Y.H.hom := GlobalTheory.RayTan.smooth_H R _ _ _ Y
  have hint : IsIntegral Y.H.left := GlobalTheory.T.isIntegral_raynaudExtension_noetherian_local R _ _ _ Y
  obtain ⟨i0, hi0⟩ : ∃ i0, ⊤ ≤ (η[Y.H]).left ⁻¹ᵁ h.W i0 := by
    have hm : (η[Y.H]).left (IsLocalRing.closedPoint R) ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i0, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨i0, (ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem ((η[Y.H]).left ⁻¹ᵁ h.W i0) hi).ge⟩
  obtain ⟨Ω, _, _, _, φ, x, δ, dΩ, hΩc, hx, hxW, hdΩ, hδφ, hδ, hd, hinj⟩ :=
    GlobalTheory.T.exists_formalPoint_origin_smoothCommGroupScheme R Y.H hsm hint n vH dd hdd ⇑D (h.W i0) (h.d i0) (h.lift i0) hi0
  set e := Scheme.ΓSpecIso (CommRingCat.of R) with he
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have h1 : valR x ⊤ (Y.H.hom.appTop.hom (e.inv.hom r)) = φ r := by
      refine (GlobalTheory.ZH.EvCrd.valR_comp x Y.H.hom ⊤ (by simp) _).trans ?_
      rw [hx]
      exact GlobalTheory.ZH.EvCrd.valR_fn φ r
    have h2 := GlobalTheory.PrimScale.valR_const (η[Y.H]).left Y.H.hom (Over.w η[Y.H]) r
    have h3 := hinj ⊤ _ (by simp) (h1.trans hr)
    rw [h3] at h2
    rw [← h2]
    simp [valR]

  obtain ⟨x', hx', dd', hdd', hδ', hinj', hpt⟩ :=
    GlobalTheory.T.exists_uniformisedGroup_point_sameDerivations E H R t P m tt gam hmon htt hab Y n vH dd hdd v' hv' Ω φ x δ hΩc hφ hx hδφ hδ
  obtain ⟨g, hg⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := Ω) t.PP.L t.PP.isLB (K := PUnit)
    (fun _ => x' ≫ 𝟙 t.G.left) (fun _ => 1)
  have hex : ∀ a, ∃ δS : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ ω, δS (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ a ω) :=
    fun a => exists_der_frac Ω (δ a)
  choose δL hδL using hex
  obtain ⟨dt, u', p, p', hdt, hact⟩ := GlobalTheory.T.commuting_heatOperators_act_on_values E H R t P m tt gam hmon htt hab Y n vH dd hdd v' hv' D h hB hDef
    i0 Ω φ x x' δ hΩc hx hx' hδφ hδ hpt dΩ hxW hd g hg δL hδL
  obtain ⟨b, rfl⟩ := GlobalTheory.T.tangentBasis_uniformisedGroup_of_raynaudExtension E H R t P Y n vH v' hv'
  let D₀ : Derivation ℤ Γ(Sp R, ⊤) Γ(Sp R, ⊤) := Derivation.mk'
    ((e.inv.hom.toAddMonoidHom.comp ((D : R →ₗ[ℤ] R).toAddMonoidHom.comp e.hom.hom.toAddMonoidHom)).toIntLinearMap)
    (fun a a' => by
      simp [Derivation.leibniz, smul_eq_mul])
  haveI := (isAffineOpen_top (Sp R)).isLocalization_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))
  obtain ⟨DV, hDV⟩ := exists_der_ext (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) D₀ (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))))
  have hDV' : ∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom (D r)) := fun r => by
    show DV (algebraMap _ _ (e.inv.hom r)) = algebraMap _ _ (e.inv.hom (D r))
    rw [hDV]
    congr 1
    simp [D₀]

  obtain ⟨Θ₁, hsym, hKS⟩ := GlobalTheory.T.exists_symmetric_kodairaSpencer_abelianLocus E H R t P m tt gam hmon htt hab n b DV
  obtain ⟨iota, dt₂, u₂, p₂, p₂', hiota, hdt₂, hact₂⟩ := GlobalTheory.T.heatOperators_kodairaSpencer_formal_point_values E H R t P m tt gam hmon htt hab n b D Ω φ x' δ dd'
    hΩc hx' hdd' hδφ hδ' hinj' g hg δL hδL Θ₁ DV hDV' hKS
  have heq := GlobalTheory.T.heatOperator_symbol_unique_principalPolarisation E H R t P m tt gam hmon htt hab n b D Ω φ x' δ dd' hΩc hx' hdd' hδφ hδ' hinj' g hg δL hδL
    (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) (iota.mapMatrix Θ₁) dt dt₂ u' u₂ p p' p₂ p₂'
    (by rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, h.symm])
    (by rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, hsym])
    (fun r => (hdt r).trans (hdt₂ r).symm) hact hact₂
  have hi : Function.Injective iota := by
    have key : ∀ y : Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))), iota y = 0 → y = 0 := by
      intro y hy
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) y
      dsimp only at hy ⊢
      have h1 : iota (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) a) = 0 := by
        rw [← IsLocalization.mk'_spec (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) a s]
        erw [map_mul, hy, zero_mul]
      have h2 : (algebraMap Γ(Sp R, ⊤) _ a : Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom (e.hom.hom a)) := by
        rw [Iso.hom_inv_id_apply]
        rfl
      rw [h2, hiota] at h1
      have h3 : φ (e.hom.hom a) = 0 := IsFractionRing.injective Ω (FractionRing Ω) (by rw [h1, map_zero])
      have h4 : e.hom.hom a = 0 := hφ (by rw [h3, map_zero])
      have h5 : a = 0 := by simpa using congrArg e.inv.hom h4
      rw [h5, IsLocalization.mk'_zero]
    exact (injective_iff_map_eq_zero iota).2 key
  have hΘ : Θ₁ = (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp e.inv.hom).mapMatrix h.Θ := by
    ext a a'
    apply hi
    have := congrFun (congrFun heq a) a'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply] at this ⊢
    rw [← this, hiota]
  rw [hΘ] at hKS
  exact GlobalTheory.T.isKodairaSpencer_affineChart_of_basicOpen E H R t m tt n ⇑b D DV h.Θ hDV' hKS

end GlobalTheory.KBracket
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceConstantLiftMemFilStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieConditionHodgeSubspace_constant_lift_mem_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ z ∈ GlobalTheory.HTCount.lieZ o₀ β, z ∈ Fil o₀.A ∧ IsFilLift m'.cart z 0 := by
  first | (exact @GlobalTheory.HTCount.lieZ_mem_fil_and_lift) | (exact GlobalTheory.HTCount.lieZ_mem_fil_and_lift) | (intros; apply GlobalTheory.HTCount.lieZ_mem_fil_and_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltrationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieConditionHodgeSubspace_le_hodgeFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R), s = spMap β → ∀ o₀ : GlobalTheory.UPel.HT.Obj b N s, GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A := by
  first | (exact @GlobalTheory.HTCount.lieZ_le_Fil) | (exact GlobalTheory.HTCount.lieZ_le_Fil) | (intros; apply GlobalTheory.HTCount.lieZ_le_Fil  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerLiftUnit

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.PrinThicken in

theorem ker_pow_eq_one_of_lift : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → ∀ (l : (G2 A₀).left ⟶ (G2 A).left), Geo.Tor.IsSquare i l → ∀ (P₀ : LB (G2 A₀).left) (P : LB (G2 A).left), P₀.IsLB → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → LBIso (P.pull l) P₀ → ∀ (e : ℕ), IsUnit (e : C) → (∀ (T : Over (Sp C₀)) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro C C₀ _ _ _ _ π hπ hsq A₀ _ _ A _ _ i hi hA l hl P₀ P hP₀ hP r₁ r₂ hsymm amp hred e he ker₀
  have csymm : cls P hP = GlobalTheory.CechPic.pull (lift (snd A A) (fst A A)).left (cls P hP) := by
    rw [← cls_pull hP]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hsymm
  have wS : (lift (snd A₀ A₀) (fst A₀ A₀)).left ≫ l = l ≫ (lift (snd A A) (fst A A)).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, hl.1, GlobalTheory.AbDual.lift_left_fst_assoc, Category.assoc, GlobalTheory.AbDual.lift_left_fst, hl.2]
    · rw [Category.assoc, hl.2, GlobalTheory.AbDual.lift_left_snd_assoc, Category.assoc, GlobalTheory.AbDual.lift_left_snd, hl.1]
  have c₀symm : cls P₀ hP₀ = GlobalTheory.CechPic.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left (cls P₀ hP₀) := by
    have e := (cls_eq_iff (pull_isLB hP l) hP₀).2 hred
    rw [cls_pull hP] at e
    rw [← e, ← pull_comp, wS, pull_comp, ← csymm]
  obtain ⟨D, _, Q, hDab, -, q, q'⟩ := GlobalTheory.abelianDualCrystal.1 _ A hA
  obtain ⟨lam, hlam, hiff⟩ := GlobalTheory.PoincarePull.exists_hom_triv_iff C A hA D Q q q' _ (pull_isLB hP _) amp P hP r₁ r₂
  haveI := hlam
  have hiff' : ∀ (T : Over (Sp C)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ≫ lam = 1 := fun T x hx ↦
    (hiff T x).1 ((triv_ev_iff hP _ _).2 ((evc_comm hP csymm _ _).trans ((triv_ev_iff hP _ _).1 hx)))
  have tors₀ : ∀ (T₀ : Over (Sp C₀)) (z : Over.mk (T₀.hom ≫ spMap π) ⟶ A), z ≫ lam = 1 → z ^ e = 1 := by
    intro T₀ z hz
    let z₀ : Over.mk T₀.hom ⟶ A₀ := liftPt hi T₀.hom z.left (Over.w z)
    have hz₀ : z₀.left ≫ i = z.left := liftPt_left hi _ _ _
    have k₁ : z₀ ^ e = 1 := ker₀ _ z₀ (by
      have e1 := evc_trR hi hi hl.1 hl.2 hP hP₀ hred (Over.mk T₀.hom) z₀
      have e0 : evc hP (fst A (Over.mk (T₀.hom ≫ spMap π))) (snd A _ ≫ z) = 0 :=
        (triv_ev_iff hP _ _).1 ((hiff _ z).2 hz)
      rw [show pushP hi (s := T₀.hom) rfl z₀ = z from Over.OverMorphism.ext hz₀] at e1
      obtain ⟨s, hs⟩ : ∃ s, s ≫ (trR hi (Over.mk T₀.hom)).left = 𝟙 _ := ⟨_, trR_section hi _⟩
      have e2 := congrArg (GlobalTheory.CechPic.pull s) (e1.trans e0)
      rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id, map_zero] at e2
      exact (triv_ev_iff hP₀ _ _).2 ((evc_comm hP₀ c₀symm _ _).symm.trans e2))
    have hp : ∀ m : ℕ, (z₀ ^ m).left ≫ i = (z ^ m).left := by
      intro m
      induction m with
      | zero =>
        simp only [pow_zero]
        exact one_left_comp hi (s := T₀.hom) rfl
      | succ m ih =>
        rw [pow_succ, pow_succ]
        exact mul_left_comp hi (s := T₀.hom) rfl ih hz₀
    apply Over.OverMorphism.ext
    rw [← hp e, k₁]
    exact one_left_comp hi (s := T₀.hom) rfl
  intro T x hx
  have hx0 : x ≫ lam = 1 := hiff' T x hx
  have hw0 : (x ^ e) ≫ lam = 1 := by rw [pow_comp, hx0, one_pow]
  have hwC : ∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ (x ^ e) = 1 := fun T₀ j ↦ by
    rw [comp_pow]
    exact tors₀ T₀ (j ≫ x) (by rw [Category.assoc, hx0, MonObj.comp_one])
  let k := equalizer.ι lam (1 : A ⟶ D)
  have hk : k ≫ lam = 1 := by rw [equalizer.condition, MonObj.comp_one]
  let u : 𝟙_ (Over (Sp C)) ⟶ equalizer lam (1 : A ⟶ D) :=
    equalizer.lift 1 (by rw [MonObj.one_comp, MonObj.comp_one])
  have hww : (x ^ e) ^ e = 1 := by
    have h1 := GlobalTheory.T.comp_eq_of_sqZero_agree_pairs C C₀ π hπ hsq (equalizer lam (1 : A ⟶ D)) A (k ^ e) 1
      (fun T₀ y ↦ by
        rw [comp_pow, MonObj.comp_one]
        exact tors₀ T₀ (y ≫ k) (by rw [Category.assoc, hk, MonObj.comp_one]))
      T (equalizer.lift (x ^ e) (by rw [hw0, MonObj.comp_one])) (toUnit T ≫ u)
      (fun T₀ j ↦ by
        rw [← cancel_mono k, Category.assoc, Category.assoc, Category.assoc,
          show equalizer.lift (x ^ e) _ ≫ k = x ^ e from equalizer.lift_ι _ _,
          show u ≫ k = 1 from equalizer.lift_ι _ _, hwC, MonObj.comp_one, MonObj.comp_one])
      (by rw [comp_pow, MonObj.comp_one, Category.assoc, show u ≫ k = 1 from equalizer.lift_ι _ _,
        MonObj.comp_one, one_pow])
    rw [comp_pow, show equalizer.lift (x ^ e) _ ≫ k = x ^ e from equalizer.lift_ι _ _, MonObj.comp_one] at h1
    exact h1
  exact GlobalTheory.T.grpObj_eq_one_of_pow_eq_one_of_sqZero_trivial C C₀ π hπ hsq A e he T (x ^ e) hwC hww

end GlobalTheory.KerLiftUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffDualNumberGraphReductionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hodgeFiltration_iff_dualNumberGraph_reduction : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (f : HdR A₀ →ₗ[k] HdR A₀) (y : HdR A₀), y ∈ Fil A₀ ↔ ∃ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).Corr d y := by
  first | (exact @GlobalTheory.HTRealise.mem_Fil_iff_exists_graphFil_corr) | (exact GlobalTheory.HTRealise.mem_Fil_iff_exists_graphFil_corr) | (intros; apply GlobalTheory.HTRealise.mem_Fil_iff_exists_graphFil_corr  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObjectStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFil_htObject : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y) := by
  first | exact @GlobalTheory.HTGlue.fil_iff_red_glueFil | exact GlobalTheory.HTGlue.fil_iff_red_glueFil | (intros; apply GlobalTheory.HTGlue.fil_iff_red_glueFil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFiltrationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y := by
  first | (exact @GlobalTheory.HTGlue.mem_fil_iff_exists_glueFil) | (exact GlobalTheory.HTGlue.mem_fil_iff_exists_glueFil) | (intros; apply GlobalTheory.HTGlue.mem_fil_iff_exists_glueFil  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagRootPullbackQuasiInverseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diag_root_pullback_quasiInverse : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → Out.RelAmple B (P'.pull (lift (𝟙 B) (𝟙 B)).left) := by
  first | (exact @GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull) | (exact GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull) | (intros; apply GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull  <;> assumption)
end

