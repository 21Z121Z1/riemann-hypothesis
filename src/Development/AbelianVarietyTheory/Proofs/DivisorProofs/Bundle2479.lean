import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectMapOfCommonPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTObjMap

theorem exists_objMap_of_common_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (T Z : Scheme.{0}) (t₁ : T ⟶ Sp R) (t₂ : Z ⟶ Sp R) (o : Obj b N t₁) (u : Obj b N t₂) (g : T ⟶ S₀) (πZ : Z ⟶ S₀) (z : T ⟶ Z) (φo : o.A.left ⟶ A₀.left) (φ₂o : (G2 o.A).left ⟶ (G2 A₀).left) (φu : u.A.left ⟶ A₀.left) (φ₂u : (G2 u.A).left ⟶ (G2 A₀).left) (ψ : o.A.left ⟶ u.A.left), IsGrpPullback o.A A₀ g φo → IsSquare φo φ₂o → LBIso o.P (P₀.pull φ₂o) → IsGrpPullback u.A A₀ πZ φu → IsSquare φu φ₂u → LBIso u.P (P₀.pull φ₂u) → z ≫ πZ = g → ψ ≫ φu = φo → ψ ≫ u.A.hom = o.A.hom ≫ z → (∀ a : D.O, (o.act.act a).left ≫ ψ = ψ ≫ (u.act.act a).left) → (∀ y, (o.eta y).left ≫ ψ = z ≫ (u.eta y).left) → ∃ m : ObjMap o u z, m.φ = ψ := by
  intro p _ D R _ b N S₀ A₀ _ P₀ hP₀ T Z t₁ t₂ o u g πZ z φo φ₂o φu φ₂u ψ ho sqo io hu squ iu hz hψ hw hact heta
  have cart : IsGrpPullback o.A u.A z ψ := IsGrpPullback.cancel hu (by rw [hz, hψ]; exact ho) hw
  have wc : ((fst o.A o.A).left ≫ ψ) ≫ u.A.hom = ((snd o.A o.A).left ≫ ψ) ≫ u.A.hom := by
    rw [Category.assoc, Category.assoc, hw, ← Category.assoc, ← Category.assoc, Over.w (fst o.A o.A), Over.w (snd o.A o.A)]
  let φ₂ : (G2 o.A).left ⟶ (G2 u.A).left := pullback.lift ((fst o.A o.A).left ≫ ψ) ((snd o.A o.A).left ≫ ψ) wc
  have s₁ : φ₂ ≫ (fst u.A u.A).left = (fst o.A o.A).left ≫ ψ := pullback.lift_fst _ _ _
  have s₂ : φ₂ ≫ (snd u.A u.A).left = (snd o.A o.A).left ≫ ψ := pullback.lift_snd _ _ _
  have sq : IsSquare ψ φ₂ := ⟨s₁, s₂⟩
  have a₁ : (φ₂ ≫ φ₂u) ≫ (fst A₀ A₀).left = φ₂o ≫ (fst A₀ A₀).left := by
    rw [Category.assoc, squ.1, ← Category.assoc, s₁, Category.assoc, hψ, sqo.1]
  have a₂ : (φ₂ ≫ φ₂u) ≫ (snd A₀ A₀).left = φ₂o ≫ (snd A₀ A₀).left := by
    rw [Category.assoc, squ.2, ← Category.assoc, s₂, Category.assoc, hψ, sqo.2]
  have e₂ : φ₂ ≫ φ₂u = φ₂o := Over.tensorObj_ext _ _ a₁ a₂
  have i₂ : LBIso (P₀.pull φ₂o) (u.P.pull φ₂) :=
    LBIso.chartPull (chartPullSame P₀ _ _ _ φ₂ (fun _ => e₂.symm)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull u.P φ₂ φ₂ rfl) (LBIso.symm iu)
  have pol : LBIso o.P (u.P.pull φ₂) :=
    LBIso.trans o.isLB (pull_isLB hP₀ _) (pull_isLB u.isLB _) io i₂
  exact ⟨{ φ := ψ, φ₂ := φ₂, cart := cart, sq := sq, act := hact, pol := pol, eta := heta }, rfl⟩

end GlobalTheory.HTObjMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOverLieTateLocus
section
noncomputable section

namespace GlobalTheory.HTMkObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem lieAt_of_lieHer (b : Base D R) {A : Over S} [GrpObj A] {act : OActN D.O A} {R' : Type} [CommRing R']
    {β : R →+* R'} {x : Sp R' ⟶ S} (h : LieHer b act β x) : LieAt b act β x := by
  have H := (h R' (RingHom.id R')).1
  have e : spMap (RingHom.id R') = 𝟙 _ := Spec.map_id _
  simp only [e, Category.id_comp, RingHom.id_comp] at H
  exact H

theorem lieMult_of_lieHer (b : Base D R) {A : Over S} [GrpObj A] {act : OActN D.O A} (k : Type) [Field k]
    [IsAlgClosed k] {β : R →+* k} {x : Sp k ⟶ S} (h : LieHer b act β x) (i : Fin D.a) :
    LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  have H := (h k (RingHom.id k)).2 k (RingHom.id k) i
  have e : spMap (RingHom.id k) = 𝟙 _ := Spec.map_id _
  simp only [e, Category.id_comp, RingHom.id_comp] at H
  exact H

end GlobalTheory.HTMkObj

namespace GlobalTheory.HTMkObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem exists_obj_of_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∀ (Z : Scheme.{0}) (j : Z ⟶ X), (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z), x ≫ j ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ j)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z) (β : R →+* k), x ≫ j ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ j)) → ∃ (u : Obj b N ((j ≫ πX) ≫ t)) (ψ : u.A.left ⟶ AX.left) (ψ₂ : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A AX j ψ ∧ IsSquare (ψ ≫ φX) ψ₂ ∧ LBIso u.P (c.P.pull ψ₂) ∧ (∀ a : D.O, (u.act.act a).left ≫ ψ = ψ ≫ (actX.act a).left) ∧ ∀ y, (u.eta y).left ≫ ψ = j ≫ (ηX y).left := by
  intro p _ D R _ b N _ _ h M B _ ζ S s₁ t c e he hc X πX AX _ _ φX φ₂X actX ηX hX sqX hRos hEta Z j hLie hGeom
  let A' := (Over.pullback (j ≫ πX)).obj c.A
  let φ := PullbackComparison.pφ (j ≫ πX) c.A
  let φ₂ := PullbackComparison.pφ₂ (j ≫ πX) c.A
  have pb : IsGrpPullback A' c.A (j ≫ πX) φ := PullbackComparison.isGrpPullback (j ≫ πX) c.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare (j ≫ πX) c.A
  have wψ : φ ≫ c.A.hom = (A'.hom ≫ j) ≫ πX := by
    rw [Category.assoc]; exact pb.1.w
  let ψ : A'.left ⟶ AX.left := hX.1.lift φ (A'.hom ≫ j) wψ
  have hψ : ψ ≫ φX = φ := hX.1.lift_fst _ _ _
  have hψh : ψ ≫ AX.hom = A'.hom ≫ j := hX.1.lift_snd _ _ _
  have pbj : IsGrpPullback A' AX j ψ := IsGrpPullback.cancel hX (by rw [hψ]; exact pb) hψh
  let ψ₂ : (G2 A').left ⟶ (G2 AX).left :=
    pullback.lift ((fst A' A').left ≫ ψ) ((snd A' A').left ≫ ψ) (by
      rw [Category.assoc, Category.assoc, hψh, ← Category.assoc, ← Category.assoc, Over.w (fst A' A'),
        Over.w (snd A' A')])
  have sqψ : IsSquare ψ ψ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hψ₂ : ψ₂ ≫ φ₂X = φ₂ := by
    refine pullback.hom_ext (f := c.A.hom) (g := c.A.hom) ?_ ?_
    · show (ψ₂ ≫ φ₂X) ≫ (fst c.A c.A).left = φ₂ ≫ (fst c.A c.A).left
      rw [Category.assoc, sqX.1, ← Category.assoc, sqψ.1, Category.assoc, hψ, sq.1]
    · show (ψ₂ ≫ φ₂X) ≫ (snd c.A c.A).left = φ₂ ≫ (snd c.A c.A).left
      rw [Category.assoc, sqX.2, ← Category.assoc, sqψ.2, Category.assoc, hψ, sq.2]
  have hab : IsAbelianScheme A' :=
    { comm := by have := c.ab.comm; infer_instance
      smooth := by have := c.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := c.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := c.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := GlobalTheory.ActPull.exists_act_pull X Z j AX A' ψ pbj D.Oᵐᵒᵖ
    (fun a => actX.act a.unop) (fun a => actX.hom _) (by simpa using actX.one)
    (fun a b => by simpa using actX.mul b.unop a.unop) (fun a b => by simpa using actX.add a.unop b.unop)
  let actN : OActN D.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ ψ = ψ ≫ (actX.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := c.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB c.isLB φ₂
  have iso : LBIso P' (c.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have hPX : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso P' ((c.P.pull φ₂X).pull ψ₂) :=
    LBIso.chartPull (chartPullSame c.P (fun _ : PUnit => φ₂) (fun _ => 𝟙 _) (fun _ => 1) φ₂
        (fun _ => (Category.comp_id _).symm))
      (chartPullLinComb c.P φ₂X (fun _ : PUnit => ψ₂) (fun _ => 𝟙 _) (fun _ => 1) φ₂
        (fun _ => by rw [hψ₂, Category.comp_id]))
      (PullbackComparison.gen_refl _ (pull_isLB c.isLB _))
  have dgX := SiegelPull.diag_iso sqψ H
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 AX ⟶ AX), x'.left ≫ ψ = ψ₂ ≫ x.left → y'.left ≫ ψ = ψ₂ ≫ y.left →
      (lift x' y').left ≫ ψ₂ = ψ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sqψ (T := Over.mk (ψ₂ ≫ (G2 AX).hom)) (T' := G2 A') (𝟙 _)
      x' y' (Z := G2 AX) ψ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  have rosP : RosatiFor D actN ((c.P.pull φ₂X).pull ψ₂) := fun a => LBIso.chartPull
    (chartPullLinComb (c.P.pull φ₂X) _ _ _ _ ψ₂ (fun _ => sqL _ _ _ _ (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sqψ.1, Category.assoc])
      (by rw [sqψ.2])))
    (chartPullLinComb (c.P.pull φ₂X) _ _ _ _ ψ₂ (fun _ => sqL _ _ _ _ (by rw [sqψ.1]) (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sqψ.2, Category.assoc])))
    (hRos a)
  obtain ⟨t₁, ht₁⟩ := c.rig₁
  obtain ⟨t₂, ht₂⟩ := c.rig₂
  let u : Obj b N ((j ≫ πX) ≫ t) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb c.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id (j ≫ πX) c.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb c.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one (j ≫ πX) c.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
        (chartPullLinComb c.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap (j ≫ πX) c.A)) c.symm
      ample := (pol_pull S Z c.A A' (j ≫ πX) φ _ _ (pull_isLB c.isLB _) (pull_isLB hP' _) c.ab pb dg).2.1 hc.1
      kerP := ⟨e, he, fun T x hx => kerBy_pull pb sq c.isLB hP' iso e hc.2 T x hx⟩
      rosati := RosatiFor.of_iso (pull_isLB hPX _) hP' (LBIso.symm H) rosP
      lie := fun R' _ β x hx v hv => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pbj (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ j)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := lieAt_of_lieHer b (hLie R' β x hx') (e v)
          ((HTPull.isTanScal_iff pbj actX actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (HTPull.isTanScal_iff pbj actX actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        exact (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) X Z AX A' j ψ (actX.toF D) (actN.toF D) pbj
          (fun c => hact _) k x (β.comp (b.t i)) D.m).2 (lieMult_of_lieHer b k (hLie k β x hx') i)
      eta := fun y => SiegelPull.secPull pbj (ηX y)
      eta_add := fun y z => SiegelPull.push_injective pbj _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', hEta.1, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pbj _ (by
        rw [HTPull.push_comp pbj (hact c), push_secPull', push_secPull', hEta.2.1, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pbj _ (by
        rw [push_secPull', hEta.2.2, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        obtain ⟨I, hI⟩ := hGeom k x β hx'
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ j) ⟶ AX) := MulEquiv.ofBijective (pushHom pbj (Over.mk x))
          ⟨SiegelPull.push_injective pbj _, SiegelPull.push_surjective pbj _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ actX.act c := fun c g => HTPull.push_comp pbj (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ ψ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm X Z AX A' j ψ _ _ (pull_isLB hPX _)
                    (pull_isLB hP' _) pbj dgX (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pbj (ηX y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pbj (ηX y) (Over.mk x)).symm }
  exact ⟨u, ψ, φ₂, pbj, by rw [hψ]; exact sq, iso, hact, fun y => SiegelPull.secPull_left pbj _⟩

end GlobalTheory.HTMkObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorPreObjectOfSiegelPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.PreEtaPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
  {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem one_left (h : IsGrpPullback A' A f φ) : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e : (1 : A' ⟶ A').left ≫ φ = (1 : Over.mk (A'.hom ≫ f) ⟶ A).left :=
    congrArg (fun q => q.left) (map_one (pushHom h A'))
  rw [e, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ← Category.assoc, h.1.w]
  rfl

theorem lift_one_id (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (1 : A' ⟶ A') (𝟙 A')
    (Z := A) φ (1 : A ⟶ A) (𝟙 A) (by exact (Category.id_comp _).trans (one_left h)) (by simp)
  exact (Category.id_comp _).symm.trans this

theorem lift_id_one (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (1 : A' ⟶ A')
    (Z := A) φ (𝟙 A) (1 : A ⟶ A) (by simp) (by exact (Category.id_comp _).trans (one_left h))
  exact (Category.id_comp _).symm.trans this

omit [GrpObj A] [GrpObj A'] in

theorem lift_swap (sq : IsSquare φ φ₂) :
    (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    (Z := A ⊗ A) φ₂ (snd A A) (fst A A) (by exact (Category.id_comp _).trans sq.2.symm)
    (by exact (Category.id_comp _).trans sq.1.symm)
  exact (Category.id_comp _).symm.trans this

end GlobalTheory.PreEtaPull

namespace GlobalTheory.UPel.HT

open GlobalTheory.PreEtaPull

theorem exists_preEta_of_siegPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ o : PreEta b N (πX ≫ t), ∀ (k : Type) [Field k] (x : Sp k ⟶ X), (o.GeomAt k x ↔ GeomAt D N actX (c.P.pull φ₂X) ηX k x) := by
  intro p _ D R _ b N h M B _ ζ S s₁ t c e he hK X πX AX _ _ φX φ₂X actX ηX hpb hsq hros heta
  have hP : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso (c.P.pull φ₂X) (c.P.pull φ₂X) := ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ hP
  refine ⟨{
    A := AX
    ab := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab hpb
    act := actX
    P := c.P.pull φ₂X
    isLB := hP
    rig₁ := by
      obtain ⟨t₁, ht₁⟩ := c.rig₁
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_one_id hpb hsq) t₁ ht₁
    rig₂ := by
      obtain ⟨t₂, ht₂⟩ := c.rig₂
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_id_one hpb hsq) t₂ ht₂
    symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
      (chartPullLinComb c.P _ _ _ _ φ₂X fun _ => lift_swap hsq) c.symm
    ample := (GlobalTheory.pol_pull S X c.A AX πX φX c.diag _ (pull_isLB c.isLB _) (pull_isLB hP _) c.ab hpb
      (GlobalTheory.SiegelPull.diag_iso hsq H)).2.1 hK.1
    kerP := ⟨e, he, kerBy_pull hpb hsq c.isLB hP H e hK.2⟩
    rosati := hros
    eta := ηX
    eta_add := heta.1
    eta_lin := heta.2.1
    eta_ker := heta.2.2 }, fun k _ x => Iff.rfl⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombination
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

theorem GlobalTheory.VolBr.Pair.exists_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (P : Pair p) (a b : ℤ), ∃ M : HermLB p, P.Rep a b M := by
  intro k _ X _ p P a b
  obtain ⟨hL, hA, -⟩ := Pair.rep_base k X p P
  have cast (x y x' y' : ℤ) (M : HermLB p) (h : P.Rep x y M) (hx : x = x') (hy : y = y') :
      P.Rep x' y' M := by subst hx; subst hy; exact h
  have hLa := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ a.toNat hL)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-a).toNat hL))
  have hAb := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ b.toNat hA)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-b).toNat hA))
  refine ⟨_, cast _ _ _ _ _ (Pair.rep_tens k X p P _ _ _ _ _ _ hLa hAb) ?_ ?_⟩
  · have h1 := Int.toNat_sub_toNat_neg a
    simp only [mul_one, mul_zero, neg_zero, add_zero]
    omega
  · have h1 := Int.toNat_sub_toNat_neg b
    simp only [mul_one, mul_zero, neg_zero, zero_add]
    omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToAffineOpenOfFunctionFieldMapRegularStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_to_affineOpen_of_functionField_map_regular : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (U : Y.Opens), genericPoint Y ∈ U → ∀ (V : P.Opens), IsAffineOpen V → ∀ (hVη : genericPoint P ∈ V) (φ : P.functionField →+* Y.functionField), (∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) → ∃ f : U.toScheme ⟶ P, (∀ y : U.toScheme, f y ∈ V) ∧ ∀ l : Sp Y.functionField ⟶ U.toScheme, l ≫ U.ι = gp Y → l ≫ f = spMap φ ≫ gp P := by
  first | exact @GlobalTheory.Desc.exists_hom_of_regAt_fnOf | exact GlobalTheory.Desc.exists_hom_of_regAt_fnOf | (intros; apply GlobalTheory.Desc.exists_hom_of_regAt_fnOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealCochainOfCoboundaryConstantsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S : Sys I π s₀) (z : Z1 S.F), S.IsIdealValuedLiftSystemCocycle z → H1.mk _ z = 0 → ∃ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g ∧ d0 _ g = z.1 := by
  first | exact @GlobalTheory.LiftSys.cobound_I | exact GlobalTheory.LiftSys.cobound_I | (intros; apply GlobalTheory.LiftSys.cobound_I <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentsAbelianSchemeConstantDimensionStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotents_abelianScheme_constant_dimension : ∀ (R₀ : Type) [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A], IsAbelianScheme A → ∃ (n : ℕ) (e : Fin n → R₀), CompleteOrthogonalIdempotents e ∧ ∀ k, ∃ g : ℕ, SmoothOfRelativeDimension g (Limits.pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k})))) := by
  first | exact @GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension | exact GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension | (intros; apply GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtaleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale : ∀ n N : ℕ, N ≠ 0 → n ∣ N → ∃ j : cycAway n →+* cycAway N, Function.Injective j ∧ j (zetaAway n) = zetaAway N ^ (N / n) ∧ ((∃ a, N ∣ n ^ a) → IsFinite (spMap j) ∧ Etale (spMap j) ∧ Surjective (spMap j)) := by
  first | exact @GlobalTheory.SiegelTor.exists_inclusion_cycAway | exact GlobalTheory.SiegelTor.exists_inclusion_cycAway | (intros; apply GlobalTheory.SiegelTor.exists_inclusion_cycAway <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInnerProductFormulaDataDefiniteBottomStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_innerProductFormula_data_definite_bottom : GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → A.SigOK → ∀ t : T,
  ∃ (χA χB : (AE D)ˣ →* Circle) (sA : RealMat (GlobalTheory.Grid.neg A)) (sB : RealMat WW) (cA : CptF (GlobalTheory.Grid.neg A))
    (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW))
    (LA : Lat (GlobalTheory.Grid.neg A)) (LB : Lat WW) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (κ : ℂ) (P : PolF D WW.rank A.rank),
    Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW χA χB sA sB A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W ∧ wittIndex WW = 0 ∧
    IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW sA sB (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧ Unram W.ψ (GlobalTheory.Grid.neg A) WW χB LA LB Sf (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) ∧
    (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA ∧
    GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram LA (Sf : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧
    SphFun (GlobalTheory.Grid.neg A) LA Sf (fun _ => (1 : ℂ)) ∧ κ ≠ 0 ∧
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 ∧
    (∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
      HolValueAt (fun s => GlobalTheory.LFun.LSD D Sf par χB (s + 1 / 2)) ((A'.rank : ℂ) / 2)
        (κ * GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
          ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s)) ∧
    ∀ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure →
      (∃ s₁ : ℝ, s₁ < (A'.rank : ℝ) / 2 ∧ IntegrableOn
        (integrand ((X.ω t).toSgn true) m νW 𝓕W LA a (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (fun _ => 1) (fun _ => 1) s₁) (openOff (GlobalTheory.Grid.neg A) LA Sf) m) ∧
      ∫ g in openOff (GlobalTheory.Grid.neg A) LA Sf, wcoef ((X.ω t).toSgn true) νW 𝓕W (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g * rcoef m (fun _ => 1) (fun _ => 1) g ∂m ≠ 0 := by
  first | exact @GlobalTheory.BottomIPData.data_exists | exact GlobalTheory.BottomIPData.data_exists | (intros; apply GlobalTheory.BottomIPData.data_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

def tensorEval {R₀ A R : Type} [CommRing R₀] [CommRing A] [CommRing R] [Algebra R₀ R] (ψ : A →+* R) :
    R₀ ⊗[ℤ] A →ₗ[ℤ] R :=
  TensorProduct.lift ((LinearMap.mul ℤ R).compl₁₂ (algebraMap R₀ R).toAddMonoidHom.toIntLinearMap
    ψ.toAddMonoidHom.toIntLinearMap)

@[simp] theorem tensorEval_tmul {R₀ A R : Type} [CommRing R₀] [CommRing A] [CommRing R] [Algebra R₀ R]
    (ψ : A →+* R) (r : R₀) (a : A) : tensorEval ψ (r ⊗ₜ a) = algebraMap R₀ R r * ψ a := rfl

def IsChartFun {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k) {A : Type} [CommRing A]
    (Y : Obj F 𝔠 (Sp A)) (δY : Y.DetGen) (h : R₀ ⊗[ℤ] A) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra R₀ R] (ψ : A →+* R) (X : Obj F 𝔠 (Sp R)) (φ : X.A.left ⟶ Y.A.left)
    (hX : X.IsRapoport) (δ : X.DetGen), X.IsPullBy Y (spMap ψ) φ → Obj.DetCorr ψ φ δY.1 δ.1 →
    r₀.val R X hX δ = tensorEval ψ h

def IsPresVal {R₀ : Type} [CommRing R₀] (k : ℕ) {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)} (δY : Y.DetGen)
    (h : R₀ ⊗[ℤ] A) {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)} (δ : X.DetGen) (ψ : A →+* R)
    (φ : X.A.left ⟶ Y.A.left) (v : R) : Prop :=
  ∀ (δ' : X.DetGen) (u : R), Obj.DetCorr ψ φ δY.1 δ'.1 → δ'.1 = u • δ.1 → v = u ^ k * tensorEval ψ h

def IsModelVal {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k) {M : Scheme.{0}} (U : Obj F 𝔠 M)
    {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) (v : R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R') (X' : Obj F 𝔠 (Sp R')) (φ' : X'.A.left ⟶ X.A.left)
    (δ' : X'.DetGen), X'.IsPullBy X (spMap (σ : R →+* R')) φ' → Obj.DetCorr (σ : R →+* R') φ' δ.1 δ'.1 →
    ∀ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φY : Y.A.left ⟶ U.A.left),
      Y.IsPullBy U hW.fromSpec φY → ∀ (δY : Y.DetGen) (h : R₀ ⊗[ℤ] Γ(M, W)), IsChartFun r₀ Y δY h →
      ∀ (ψ : Γ(M, W) →+* R') (χ : X'.A.left ⟶ Y.A.left), X'.IsPullBy Y (spMap ψ) χ →
        IsPresVal k δY h δ' ψ χ (σ v)

def IsDPModel (N : ℕ) {M : Scheme.{0}} (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N)
    (V : M.Opens) : Prop :=
  IsFineModuli s α ∧ IsSeparated s ∧ Flat s ∧ (V : Set M) = U.rapLocus ∧
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) ∧
    ∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
      pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)

theorem exists_isDPModel (hDP : GlobalTheory.Published.DelignePappasModel) (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (hN : 3 ≤ N) :
    ∃ (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N) (V : M.Opens),
      IsDPModel N s U α V := by
  obtain ⟨M, s, U, α, hfine, hsep, -, -, hflat, -, ⟨V, hV, -, -, hcod⟩, hnorm, -⟩ := hDP F 𝔠 N hN
  exact ⟨M, s, U, α, V, hfine, hsep, hflat, hV, hnorm, hcod⟩

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelActionTripleOverlapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernelAction_triple_overlap : ∀ (S : Scheme.{0}) (A N T : Over S) [GrpObj A] [GrpObj N] (i : N ⟶ A) (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsCharacter χ → ∃ (W : Scheme.{0}) (m₁₂ m₂₃ m₁₃ : W ⟶ (A ⊗ (N ⊗ T)).left), IsPullback m₁₂ m₂₃ (actMap i T).left (prMap A N T).left ∧ m₁₃ ≫ (prMap A N T).left = m₁₂ ≫ (prMap A N T).left ∧ m₁₃ ≫ (actMap i T).left = m₂₃ ≫ (actMap i T).left ∧ pullTop m₁₃ (pullTop (snd A (N ⊗ T)).left χ) = pullTop m₁₂ (pullTop (snd A (N ⊗ T)).left χ) * pullTop m₂₃ (pullTop (snd A (N ⊗ T)).left χ) := by
  first | exact @GlobalTheory.CharKer.triOverlap | exact GlobalTheory.CharKer.triOverlap | (intros; apply GlobalTheory.CharKer.triOverlap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisNearBoundaryFlagSpacePointStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenBasis_near_boundaryFlagSpace_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ y : Y₀ TF.X Z, ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), toBase TF Z y ∈ U.1 ∧ IsEigBasis TF U e v := by
  first | exact @GlobalTheory.LogPole.exists_eigBasis_near | exact GlobalTheory.LogPole.exists_eigBasis_near | (intros; apply GlobalTheory.LogPole.exists_eigBasis_near <;> assumption)
end

