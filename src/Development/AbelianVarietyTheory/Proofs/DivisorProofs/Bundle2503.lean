import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
section
noncomputable section

namespace GlobalTheory.UPel.HT.Gen.BaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

section Pull

open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud GlobalTheory.HTPull GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem exists_gObjMap_pull {b : GBase G R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} (f : S' ⟶ S)
    (o : GObj b N s) : ∃ o' : GObj b N (f ≫ s), Nonempty (GObjMap o' o f) := by
  let A' := (Over.pullback f).obj o.A
  let φ := PullbackComparison.pφ f o.A
  let φ₂ := PullbackComparison.pφ₂ f o.A
  have pb : IsGrpPullback A' o.A f φ := PullbackComparison.isGrpPullback f o.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare f o.A
  have hab : IsAbelianScheme A' :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := ActPull.exists_act_pull S S' f o.A A' φ pb G.Oᵐᵒᵖ
    (fun a => o.act.act a.unop) (fun a => o.act.hom _) (by simpa using o.act.one)
    (fun a b => by simpa using o.act.mul b.unop a.unop) (fun a b => by simpa using o.act.add a.unop b.unop)
  let actN : OActN G.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := o.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂
  have iso : LBIso P' (o.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 o.A ⟶ o.A), x'.left ≫ φ = φ₂ ≫ x.left → y'.left ≫ φ = φ₂ ≫ y.left →
      (lift x' y').left ≫ φ₂ = φ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (G2 o.A).hom)) (T' := G2 A') (𝟙 _) x' y'
      (Z := G2 o.A) φ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  let o' : GObj b N (f ≫ s) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P _ _ rfl)
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap f o.A)) o.symm
      ample := (pol_pull S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab pb dg).2.1 o.ample
      rosati := fun c => LBIso.chartPull
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.1, Category.assoc])
          (by rw [sq.2])))
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by rw [sq.1]) (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.2, Category.assoc])))
        (o.rosati c)
      lie := fun R' _ β x hx v hv => by
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hx]) (e v)
          ((isTanScal_iff pb o.act actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (isTanScal_iff pb o.act actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => (GlobalTheory.LiePull.lieMult_pull (𝓞 G.F) S S' o.A A' f φ (actF o.act) (actF actN) pb
        (fun c => hact _) k x (β.comp (b.t i)) G.m).2 (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hx]) i)
      eta := fun y => SiegelPull.secPull pb (o.eta y)
      eta_add := fun y z => SiegelPull.push_injective pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', o.eta_add, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pb _ (by
        rw [push_comp pb (hact c), push_secPull', push_secPull', o.eta_lin, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pb _ (by
        rw [push_secPull', o.eta_ker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ o.act.act c := fun c g => push_comp pb (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn y
                  onto := fun n hn q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm y => by rw [← map_pow, I.tower n m hn hm]
                  isom := fun n hn y z => (weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _)
                    (pull_isLB hP' _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pb (o.eta y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pb (o.eta y) (Over.mk x)).symm }
  exact ⟨o', ⟨{ φ := φ, φ₂ := φ₂, cart := pb, sq := sq, act := hact, pol := iso, eta := fun y => SiegelPull.secPull_left pb _ }⟩⟩

end Pull

section Cancel

open GlobalTheory.UPel.HT.MapComp

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem gObjMap_cancel {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : GObjMap o₁ o₃ (f ≫ g)) (m₂ : GObjMap o₂ o₃ g) : Nonempty (GObjMap o₁ o₂ f) := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := isSquare_unique m.sq (hφ ▸ isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }⟩

end Cancel

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem exists_ext {R₁ R₂ R' : Type} [CommRing R₁] [CommRing R₂] [CommRing R'] (ψ : R₁ →+* R₂) (β₁ : R₁ →+* R')
    (x : Sp R' ⟶ Sp R₂) (hx : x ≫ spMap ψ = spMap β₁) : ∃ β₂ : R₂ →+* R', x = spMap β₂ ∧ β₁ = β₂.comp ψ := by
  obtain ⟨g, hg⟩ := Spec.map_surjective (R := CommRingCat.of R₂) (S := CommRingCat.of R') x
  have e : x = spMap g.hom := hg.symm
  refine ⟨g.hom, e, ?_⟩
  rw [e, ← spMap_comp'] at hx
  have := Spec.map_injective (R := CommRingCat.of R₁) (S := CommRingCat.of R') hx
  exact (congrArg CommRingCat.Hom.hom this).symm

section Rebase

variable {G : GDatum} {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂] {ψ : R₁ →+* R₂}
  {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} (hρ : gb₂.ρ = ψ gb₁.ρ) (ht : ∀ i, gb₂.t i = ψ.comp (gb₁.t i)) {N : ℕ}
  {S : Scheme.{0}} {s₁ : S ⟶ Sp R₁} {s₂ : S ⟶ Sp R₂} (hs : s₂ ≫ spMap ψ = s₁)

def down (o : GObj gb₂ N s₂) : GObj gb₁ N s₁ where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := fun R' _ β x hx v hv => by
    obtain ⟨β₂, e, rfl⟩ := exists_ext ψ β (x ≫ s₂) (by rw [Category.assoc, hs, hx])
    obtain ⟨w, hw, hv⟩ := o.lie R' β₂ x e v (by rw [hρ]; exact hv)
    exact ⟨w, fun i c => by have := hw i c; rw [ht] at this; exact this, hv⟩
  lieRank := fun k _ _ x β hx i => by
    obtain ⟨β₂, e, rfl⟩ := exists_ext ψ β (x ≫ s₂) (by rw [Category.assoc, hs, hx])
    have := o.lieRank k x β₂ e i
    rw [ht] at this
    exact this
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := fun k _ _ x β hx => by
    obtain ⟨β₂, e, rfl⟩ := exists_ext ψ β (x ≫ s₂) (by rw [Category.assoc, hs, hx])
    exact o.geom k x β₂ e

def up (o : GObj gb₁ N s₁) : GObj gb₂ N s₂ where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := fun R' _ β x hx v hv => by
    obtain ⟨w, hw, hv⟩ := o.lie R' (β.comp ψ) x (by rw [← hs, ← Category.assoc, hx, spMap_comp']) v
      (by rw [hρ] at hv; exact hv)
    exact ⟨w, fun i c => by rw [ht]; exact hw i c, hv⟩
  lieRank := fun k _ _ x β hx i => by
    rw [ht]
    exact o.lieRank k x (β.comp ψ) (by rw [← hs, ← Category.assoc, hx, spMap_comp']) i
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := fun k _ _ x β hx => o.geom k x (β.comp ψ) (by rw [← hs, ← Category.assoc, hx, spMap_comp'])

end Rebase

end GlobalTheory.UPel.HT.Gen.BaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointCompStructureEqSpecMapConstantsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R), gp X ≫ p = spMap (cst p) := by
  first | exact @GlobalTheory.Desc.gp_comp_eq_spMap_cst | exact GlobalTheory.Desc.gp_comp_eq_spMap_cst | (intros; apply GlobalTheory.Desc.gp_comp_eq_spMap_cst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNotInSncBoundary
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem genericPoint_notMem_of_snc (Y : Scheme.{0}) [IsIntegral Y] (B : Closeds Y)
    (h : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) : genericPoint Y ∉ B := by
  obtain ⟨-, U, hy, n, f, J, ⟨-, hn⟩, hI⟩ := h (genericPoint Y)
  have hdim : ringKrullDim (Y.presheaf.stalk (genericPoint Y)) = 0 :=
    ringKrullDim_eq_zero_of_field Y.functionField
  rw [hdim] at hn
  have hn0 : n = 0 := by exact_mod_cast hn
  subst hn0
  have hJ : J = ∅ := Finset.eq_empty_of_isEmpty J
  subst hJ
  intro hB
  have hs : genericPoint Y ∈ (Scheme.IdealSheafData.vanishingIdeal B).support := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hB
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hy, hI, Scheme.mem_zeroLocus_iff] at hs
  refine hs 1 (Ideal.subset_span (by simp)) ?_
  simpa using hy

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermDvdOfSectionExpansionDvdClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.ClosedFibreDvd

theorem mem_span_of_forall_pow {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] (a s : O)
    (h : ∀ n : ℕ, s ∈ Ideal.span {a} ⊔ maximalIdeal O ^ (n + 1)) : s ∈ Ideal.span {a} := by
  by_cases ht : Ideal.span {a} = ⊤
  · rw [ht]; trivial
  haveI : Nontrivial (O ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.2 ht
  haveI : IsLocalRing (O ⧸ Ideal.span {a}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk (Ideal.span {a})) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing
    (maximalIdeal (O ⧸ Ideal.span {a})) (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]
  intro n
  have hle : Ideal.map (Ideal.Quotient.mk (Ideal.span {a})) (Ideal.span {a} ⊔ maximalIdeal O ^ (n + 1)) ≤
      maximalIdeal (O ⧸ Ideal.span {a}) ^ n := by
    rw [Ideal.map_sup, Ideal.map_pow]
    refine sup_le ?_ ?_
    · rw [Ideal.map_quotient_self]; exact bot_le
    · refine le_trans ?_ (Ideal.pow_le_pow_right (Nat.le_succ n))
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit _ r hr) _
  exact hle (Ideal.mem_map_of_mem _ (h n))

theorem ker_stalkMap_le {X H : Scheme.{0}} (j : H ⟶ X) [IsClosedImmersion j] (z : H)
    (I : Ideal (X.presheaf.stalk (j z))) (hI : I ≠ ⊤)
    (ℓ : Spec (CommRingCat.of (X.presheaf.stalk (j z) ⧸ I)) ⟶ H)
    (hℓ : ℓ ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk (j z)) :
    RingHom.ker (j.stalkMap z).hom ≤ I := by
  intro a ha
  haveI : Nontrivial (X.presheaf.stalk (j z) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : IsLocalRing (X.presheaf.stalk (j z) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have e : ℓ (IsLocalRing.closedPoint _) = z := by
    apply j.isEmbedding.injective
    refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hℓ).trans ?_
    exact (congrArg (X.fromSpecStalk (j z)) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint
  let ψ := H.presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo ℓ
  have hψ : j.stalkMap z ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (j z)), ← hℓ, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
  have hψ' := congrArg (fun q => q.hom a) hψ
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hψ'
  rw [RingHom.mem_ker.1 ha, map_zero] at hψ'
  exact Ideal.Quotient.eq_zero_iff_mem.1 hψ'.symm

def cstHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) : R →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p x) trivial ≫ p.stalkMap x).hom

theorem cstHom_apply {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) (c : R) :
    cstHom p x c = cst p x c := by
  rw [cst, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl

theorem fromSpecStalk_comp {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : X) :
    X.fromSpecStalk x ≫ p = Spec.map (CommRingCat.ofHom (cstHom p x)) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp]; rfl

theorem exists_lift {R : Type} [CommRing R] (J : Ideal R) {X Y P : Scheme.{0}} (π : Y ⟶ Sp R) (p : X ⟶ Sp R)
    (fs : P ⟶ Y) (sn : P ⟶ Spec (CommRingCat.of (R ⧸ J)))
    (hP : IsPullback fs sn π (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (k : Y ⟶ X) (h : X ⟶ Y) (hh : h ≫ π = p) (hk : h ≫ k = 𝟙 X) (z : P)
    (I : Ideal (X.presheaf.stalk ((fs ≫ k) z))) (hJ : Ideal.map (cstHom p _) J ≤ I) :
    ∃ ℓ : Spec (CommRingCat.of (X.presheaf.stalk ((fs ≫ k) z) ⧸ I)) ⟶ P,
      ℓ ≫ (fs ≫ k) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk _ := by
  let L : R ⧸ J →+* X.presheaf.stalk ((fs ≫ k) z) ⧸ I := Ideal.Quotient.lift J ((Ideal.Quotient.mk I).comp (cstHom p _))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hJ (Ideal.mem_map_of_mem _ ha)))
  have w : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk _) ≫ h) ≫ π =
      Spec.map (CommRingCat.ofHom L) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    rw [Category.assoc, Category.assoc, hh, fromSpecStalk_comp, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  refine ⟨hP.lift _ _ w, ?_⟩
  rw [← Category.assoc, hP.lift_fst, Category.assoc, hk, Category.comp_id]

theorem cst_stalkMap' {V : Type} [CommRing V] {X Z : Scheme.{0}} (r : Z ⟶ X) (p : X ⟶ Sp V) (z : Z) (a : V) :
    (r.stalkMap z).hom (cst p (r z) a) = cst (r ≫ p) z a := by
  have e := gs_pull (𝟙 X) p (r z) ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  rw [Category.id_comp] at e
  exact (congrArg (r.stalkMap z).hom e.symm).trans ((gs_stalkMap r z (p ⁻¹ᵁ ⊤) trivial _).symm.trans
    (gs_pull r p z ⊤ trivial _))

theorem germ_dvd_of_expT_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∀ (x : (𝟙_ (Over (Sp R)) ⊗ G).left), (𝟙_ (Over (Sp R)) ⊗ G).hom x = closedPoint R → ∀ (j : Fin 1 → U.P.L.L.ι), x ∈ LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j → ∃ t, gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) = cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q * t := by
  intro R _ _ _ hR D A G _ _ U σ f g q hE hM x hx j hxj
  haveI : IsNoetherianRing R := hR.1.1
  haveI : Smooth G.hom := U.semi.smooth
  have lam : (snd (𝟙_ (Over (Sp R))) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ (Over (Sp R))) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  have lamA' : (λ_ D.P.A).inv.left ≫ (snd (𝟙_ (Over (Sp R))) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  have toU : ∀ {Y : Over (Sp R)} (h : Y ⟶ 𝟙_ (Over (Sp R))), h.left = Y.hom := fun h => by simpa using Over.w h
  have hpG : (snd (𝟙_ (Over (Sp R))) G).left ≫ G.hom = (𝟙_ (Over (Sp R)) ⊗ G).hom := Over.w _
  haveI : IsIso (snd (𝟙_ (Over (Sp R))) G).left := ⟨⟨(λ_ G).inv.left, lam, lam'⟩⟩
  haveI : LocallyOfFiniteType (𝟙_ (Over (Sp R)) ⊗ G).hom := by rw [← hpG]; infer_instance
  haveI : IsLocallyNoetherian (𝟙_ (Over (Sp R)) ⊗ G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (𝟙_ (Over (Sp R)) ⊗ G).hom
  suffices H : gs (𝟙 _) x (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j) ∈
      Ideal.span {cst (𝟙_ (Over (Sp R)) ⊗ G).hom x q} by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 H
    exact ⟨t, by rw [← ht, mul_comm]⟩
  refine mem_span_of_forall_pow _ _ fun e => ?_
  have hxg : G.hom ((snd (𝟙_ (Over (Sp R))) G).left x) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, hpG]; exact hx
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  haveI : IsLocalRing (R ⧸ maximalIdeal R ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hl : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hw : thick R (maximalIdeal R) e (closedPoint _) = closedPoint R := by
    have := IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))
    exact this
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := thick R (maximalIdeal R) e) _ _
    (hxg.trans hw.symm)
  have hzx : (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z = x := by
    rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, lam]; rfl
  subst hzx

  have hc : IsClosedImmersion (thick R (maximalIdeal R) e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

  haveI : IsIso (λ_ G).inv.left := ⟨⟨(snd (𝟙_ (Over (Sp R))) G).left, lam', lam⟩⟩
  haveI : IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e)) := inferInstance
  haveI : IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) := inferInstance

  have hmap : Ideal.map (cstHom (𝟙_ (Over (Sp R)) ⊗ G).hom
      ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)) (maximalIdeal R ^ (e + 1)) ≤
      maximalIdeal _ ^ (e + 1) := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun c hc' => ?_) _
    rw [Ideal.mem_comap, cstHom_apply]
    exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (cst_not_isUnit _ _ hx hc'))
  have hker : RingHom.ker ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap z).hom ≤
      maximalIdeal _ ^ (e + 1) := by
    have hI : Ideal.map (cstHom (𝟙_ (Over (Sp R)) ⊗ G).hom
        ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)) (maximalIdeal R ^ (e + 1)) ≠ ⊤ :=
      ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (hmap.trans (Ideal.pow_le_self (Nat.succ_ne_zero e)))
    obtain ⟨ℓ, hℓ⟩ := exists_lift (maximalIdeal R ^ (e + 1)) G.hom (𝟙_ (Over (Sp R)) ⊗ G).hom
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _) (λ_ G).inv.left
      (snd (𝟙_ (Over (Sp R))) G).left hpG lam z _ le_rfl
    exact (ker_stalkMap_le _ z _ hI ℓ hℓ).trans hmap

  obtain ⟨S, hS⟩ := hE e
  obtain ⟨JG, hJG⟩ := GlobalTheory.UU.exists_good_pt U.P.L.isLB z
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  have h3 : ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (fst (𝟙_ (Over (Sp R))) D.P.A).left =
      (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫ (fst (𝟙_ (Over (Sp R))) G).left := by
    rw [toU, toU, Category.assoc, Category.assoc, Over.w (λ_ D.P.A).inv, Over.w (λ_ G).inv, Over.w (U.gt e).pG,
      pullback.condition]
    rfl
  have key := (hS _ (𝟙 _) (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left)
    ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left)
    (by rw [Category.assoc, lam', Category.comp_id, Category.id_comp]; rfl)
    (by rw [Category.assoc, lamA', Category.comp_id, Category.id_comp]) h3 z JG J hJG hJ).2

  have aux : ∀ {O : Type} [CommRing O] (u : Oˣ) (a b : O) (I : Ideal O), (u : O) ^ 1 * a = b → b ∈ I → a ∈ I :=
    fun u a b I h hb => by
      rw [pow_one] at h
      rw [← u.inv_mul_cancel_left a, h]
      exact I.mul_mem_left _ hb
  have hq : ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom =
      (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    rw [Category.assoc, Category.assoc, Over.w (λ_ D.P.A).inv, Over.w (λ_ G).inv, Over.w (U.gt e).pG,
      pullback.condition]
    rfl
  have hmem : sval σ (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z JG ∈
      Ideal.span {cst ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫
        (𝟙_ (Over (Sp R)) ⊗ G).hom) z q} := by
    refine aux _ _ _ _ key (Ideal.sum_mem _ fun α _ => ?_)
    have hF : sval (f α) ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) z J =
        cst (((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom) z q *
          sval (g α) ((U.gt e).pG.left ≫ (λ_ D.P.A).inv.left) z J :=
      secIsMul_gs (hM α) _ z _ (hJ.mem _ _)
    rw [hF, hq, _root_.mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hπ : ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap z).hom
      (gs (𝟙 _) ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z)
        (LB.wchart U.P.L.L (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left) j) (σ.f j)) ∈
      Ideal.span {cst ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) ≫
        (𝟙_ (Over (Sp R)) ⊗ G).hom) z q} := by
    have e1 := gs_stalkMap (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z _ hxj (σ.f j)
    erw [← e1, sec_trans σ _ z hxj (hJG.mem _ _)]
    exact Ideal.mul_mem_left _ _ hmem
  obtain ⟨t', ht'⟩ := Ideal.mem_span_singleton'.1 hπ
  obtain ⟨t, rfl⟩ := (pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left).stalkMap_surjective z t'
  refine Submodule.mem_sup.2 ⟨t * cst (𝟙_ (Over (Sp R)) ⊗ G).hom
    ((pullback.fst G.hom (thick R (maximalIdeal R) e) ≫ (λ_ G).inv.left) z) q,
    Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), _, hker ?_, add_sub_cancel _ _⟩
  rw [RingHom.mem_ker, map_sub, map_mul, cst_stalkMap', ht', sub_self]

end GlobalTheory.ClosedFibreDvd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemIdealSheafStalkOfClosedFibreUnivClosedStatement
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_mem_idealSheaf_stalk_of_closedFibre_univClosed : ∀ (P : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (p : P ⟶ Sp R) [UniversallyClosed p] (I : P.IdealSheafData) (s : Γ(P, ⊤)), (∀ v : P, p v = closedPoint R → (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) → ∀ v : P, (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  first | exact @GlobalTheory.SpreadIdeal.mem_stalkId_of_closedFibre | exact GlobalTheory.SpreadIdeal.mem_stalkId_of_closedFibre | (intros; apply GlobalTheory.SpreadIdeal.mem_stalkId_of_closedFibre <;> assumption)
end

