import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechRepresentativeChernClassTangentValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedPointLevelExtends
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.WeilSpec

set_option maxHeartbeats 1000000 in
theorem weil_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ (a : Dw.La)
      (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ),
      (∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ))))) →
    ∀ (f : R) (wf : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ ξ) ⟶ Y.t.G), wf ^ (p ^ n) = 1 →
    ∀ (g : Localization.Away f →+* FractionRing R), g.comp (algebraMap R _) = algebraMap R (FractionRing R) →
    ∀ (x0 : R →+* 𝓞_ℂ_[p]) (φ : Localization.Away f →+* ℂ_[p]),
      φ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0 →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c'), spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap x0 ≫ ξ = yy ≫ Y.j →
    ∀ (e σ : Over.mk yy ⟶ Y.oF.t.G), e.left = yy ≫ (Y.oF.etaA a).left → σ.left ≫ Y.m.φ = spMap φ ≫ wf.left →
      σ ^ (p ^ n) = 1 ∧ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
        (unitOn (Units.map ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0).toMonoidHom (κ (spMap g ≫ wf.left)))) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n hp hA R _ _ _ ξ y hy a κ hκ f wf hwf g hg x0 φ hφ yy hyy e σ he hσ
  set χ : R →+* ℂ_[p] := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0 with hχ
  set q : Ideal R := RingHom.ker χ with hq
  haveI : q.IsPrime := RingHom.ker_isPrime χ
  haveI hj : IsOpenImmersion Y.j := GlobalTheory.LocM.BaseMdl.isOpenImmersion_j (Fact.out) hp Y
  haveI hmono : Mono Y.j := GlobalTheory.PolArc.mono_j_of_valuationSubring _ Y
  have hyy' : spMap χ ≫ ξ = yy ≫ Y.j := by rw [← hyy, sp_sp]
  obtain ⟨yq, hyq⟩ := GlobalTheory.T.lift_to_prime_localization (Xo'.XF c') Y.X Y.j R ξ ℂ_[p] χ yy hyy' q rfl
  have hfq : f ∉ q := by
    intro hf
    have h1 : φ (algebraMap R (Localization.Away f) f) = χ f := by
      rw [← RingHom.comp_apply, hφ]
    have h2 : χ f = 0 := RingHom.mem_ker.1 hf
    have hu : IsUnit (algebraMap R (Localization.Away f) f) := IsLocalization.Away.algebraMap_isUnit f
    exact (hu.map φ).ne_zero (h1.trans h2)
  let Rq := Localization.AtPrime q
  let hf' : Localization.Away f →+* Rq :=
    IsLocalization.Away.lift f (g := algebraMap R Rq) (IsLocalization.map_units Rq (⟨f, hfq⟩ : q.primeCompl))
  have hhf' : hf'.comp (algebraMap R (Localization.Away f)) = algebraMap R Rq := IsLocalization.Away.lift_comp _ _
  have hχu : ∀ s : q.primeCompl, IsUnit (χ s) := fun s => by
    refine IsUnit.mk0 _ fun h0 => s.2 ?_
    exact RingHom.mem_ker.2 h0
  let ψq : Rq →+* ℂ_[p] := IsLocalization.lift (M := q.primeCompl) hχu
  have hψq : ψq.comp (algebraMap R Rq) = χ := IsLocalization.lift_comp _
  have hKu : ∀ s : q.primeCompl, IsUnit (algebraMap R (FractionRing R) s) := fun s => by
    refine IsUnit.mk0 _ fun h0 => s.2 ?_
    have : (s : R) = 0 := (IsFractionRing.injective R (FractionRing R)) (by rw [h0, map_zero])
    rw [this]; exact q.zero_mem
  let ιK : Rq →+* FractionRing R := IsLocalization.lift (M := q.primeCompl) hKu
  have hιK : ιK.comp (algebraMap R Rq) = algebraMap R (FractionRing R) := IsLocalization.lift_comp _
  have hιinj : Function.Injective ιK := by
    rw [IsLocalization.lift_injective_iff]
    intro u v
    rw [(IsLocalization.injective Rq q.primeCompl_le_nonZeroDivisors).eq_iff,
      (IsFractionRing.injective R (FractionRing R)).eq_iff]
  have hK : spMap ιK ≫ yq = y := by
    rw [← cancel_mono Y.j, Category.assoc, ← hyq, sp_sp, hιK, hy]
  have hC : spMap ψq ≫ yq = yy := by
    rw [← cancel_mono Y.j, Category.assoc, ← hyq, sp_sp, hψq, hyy']
  have hgK : ιK.comp hf' = g := IsLocalization.ringHom_ext (Submonoid.powers f) (by
    rw [RingHom.comp_assoc, hhf', hιK, hg])
  have hgC : ψq.comp hf' = φ := IsLocalization.ringHom_ext (Submonoid.powers f) (by
    rw [RingHom.comp_assoc, hhf', hψq, hφ])
  have hwq : (spMap hf' ≫ wf.left) ≫ Y.t.G.hom = yq ≫ Y.j := by
    rw [Category.assoc, Over.w wf]
    change spMap hf' ≫ spMap (algebraMap R (Localization.Away f)) ≫ ξ = _
    rw [sp_sp, hhf', hyq]
  let wq : Over.mk (yq ≫ Y.j) ⟶ Y.t.G := GlobalTheory.HTMap.mkPt (spMap hf' ≫ wf.left) hwq
  have hwqt : wq ^ (p ^ n) = 1 := GlobalTheory.HTMap.tors_of (g := spMap hf') (w := wf) rfl hwf
  obtain ⟨σq, hσq, htq⟩ := GlobalTheory.T.exists_torsion_section_pullback _ _ Y.oF.t.G Y.t.G _ Y.m.cm.F Y.m.cart (Over.mk yq) wq
  have hσqt : σq ^ (p ^ n) = 1 := htq _ hwqt
  let P := GlobalTheory.Obj.toPolAV Y.oF
  have tu : ∀ {T : Scheme.{0}} (z : T ⟶ Xo'.XF c'), (toUnit (Over.mk z)).left = z := fun z => by
    simpa using Over.w (toUnit (Over.mk z))
  let eq : Over.mk yq ⟶ Y.oF.t.G := toUnit _ ≫ Y.oF.etaA a
  have heq : eq ^ (p ^ n) = 1 := by
    rw [← MonObj.comp_pow, ← hA, GlobalTheory.ArcExt.etaA_pow_eq_one, MonObj.comp_one]
  obtain ⟨cq, hcq, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) eq σq heq hσqt
  obtain ⟨uq, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 cq

  let hKo : Over.mk y ⟶ Over.mk yq := Over.homMk (spMap ιK) hK
  have hN := (GlobalTheory.LevelCompare.weil_skew_natural P (p ^ n) (Over.mk yq)).2 (Over.mk y) hKo eq σq (unitOn uq) hcq
  have hKl : hKo.left = spMap ιK := rfl
  rw [hKl, GlobalTheory.Ex.Specialise.map_unitOn] at hN
  have t1 : (hKo ≫ eq) ^ (p ^ n) = 1 := by rw [← MonObj.comp_pow, heq, MonObj.comp_one]
  have t2 : (hKo ≫ σq) ^ (p ^ n) = 1 := by rw [← MonObj.comp_pow, hσqt, MonObj.comp_one]
  have hKe : (hKo ≫ eq).left = y ≫ (Y.oF.etaA a).left := by
    simp only [eq, Over.comp_left, tu, hKo, Over.homMk_left]
    rw [← Category.assoc, hK]
  have hKσ : (hKo ≫ σq).left ≫ Y.m.φ = spMap g ≫ wf.left := by
    rw [Over.comp_left, Category.assoc]
    change spMap ιK ≫ σq.left ≫ Y.m.cm.F = _
    rw [hσq]
    change spMap ιK ≫ spMap hf' ≫ wf.left = _
    rw [sp_sp, hgK]
  have hκK := hκ (hKo ≫ eq) (hKo ≫ σq) hKe t2
  rw [hKσ] at hκK
  have huK := (GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) (hKo ≫ eq) (hKo ≫ σq) t1 t2).unique hN hκK
  have huK' := GlobalTheory.Ex.Specialise.unitOn_bijective.1 huK
  set κK := κ (spMap g ≫ wf.left) with hκKdef
  have huq : uq = Units.map (algebraMap R Rq).toMonoidHom κK := by
    ext
    apply hιinj
    have := congrArg (fun u : (FractionRing R)ˣ => (u : FractionRing R)) huK'
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe] at this ⊢
    rw [this, ← RingHom.comp_apply, hιK]

  let hCo : Over.mk yy ⟶ Over.mk yq := Over.homMk (spMap ψq) hC
  have hN2 := (GlobalTheory.LevelCompare.weil_skew_natural P (p ^ n) (Over.mk yq)).2 (Over.mk yy) hCo eq σq (unitOn uq) hcq
  have hCl : hCo.left = spMap ψq := rfl
  rw [hCl, GlobalTheory.Ex.Specialise.map_unitOn] at hN2
  have hCe : hCo ≫ eq = e := by
    ext1
    simp only [eq, Over.comp_left, tu, hCo, Over.homMk_left]
    rw [← Category.assoc, hC, he]
  have hCσ : hCo ≫ σq = σ := by
    ext1
    refine Y.m.cart.1.hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc]
      change spMap ψq ≫ σq.left ≫ Y.m.cm.F = σ.left ≫ Y.m.φ
      rw [hσq, hσ]
      change spMap ψq ≫ spMap hf' ≫ wf.left = _
      rw [sp_sp, hgC]
    · rw [Over.w (hCo ≫ σq), Over.w σ]
  refine ⟨?_, ?_⟩
  · rw [← hCσ, ← MonObj.comp_pow, hσqt, MonObj.comp_one]
  · rw [← hCe, ← hCσ]
    have hval : Units.map (ψq : Rq →* ℂ_[p]) uq = Units.map χ.toMonoidHom κK := by
      rw [huq]
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
      rw [← RingHom.comp_apply, hψq]
    have hN3 : Out.WeilIs P.A P.L ((p ^ n : ℕ) : ℤ) (hCo ≫ eq) (hCo ≫ σq) (unitOn (Units.map χ.toMonoidHom κK)) := by
      rw [← hval]; exact hN2
    exact hN3

end GlobalTheory.WeilSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionComparisonGeneratorOfAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData.CmpTwoProof

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

theorem pull_cls_of_isPart {X X₁ : Scheme.{0}} {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι}
    (h : IsPart N M e π) (hN : N.IsLB) (hM : M.IsLB) : CechPic.pull e (cls N hN) = cls M hM := by
  have h1 := LB.isLB_linComb hN (fun _ : PUnit.{1} => 𝟙 X₁ ≫ e) (fun _ => 1)
  have h2 := LB.isLB_linComb hM (fun _ : PUnit.{1} => 𝟙 X₁) (fun _ => 1)
  have a := cls_linComb hN _ _ h1
  have b := cls_linComb hM _ _ h2
  have c := (cls_eq_iff h1 h2).2 (iso_of_chart h2 (h.up (fun _ : PUnit.{1} => 𝟙 X₁) (fun _ => 1)))
  have := (a.symm.trans c).trans b
  simpa only [Fintype.sum_unique, one_smul, Category.id_comp, pull_id] using this

theorem comp_one_pt {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit X) (toUnit Y)]

theorem one_comp_hom {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

end GlobalTheory.Mum.PowData.CmpTwoProof

open GlobalTheory.Mum.PowData.CmpTwoProof in
theorem GlobalTheory.Mum.PowData.cmpTwo_of_adjCls : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A), IsMonHom q → IsMonHom j → AdjCls (cls D.P.L D.P.isLB) (cls D₀.P.L D₀.P.isLB) q j → CmpTwo D D₀ q j := by
  intro R _ _ D D₀ q j hq hj hadj
  haveI := hq
  haveI := hj
  have hN : (JN D D₀).IsLB := jn_isLB D D₀
  have hG := GlobalTheory.globalFns_holds
  have pl := pull_cls_of_isPart (isPart_inl D.P.L D₀.P.L) hN D.P.isLB
  have pr := pull_cls_of_isPart (isPart_inr D.P.L D₀.P.L) hN D₀.P.isLB
  let φΓ : Fin 4 ⊕ Fin 4 → ((D.P.A ⊗ D₀.P.A).left ⟶ (D.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) :=
    Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j) k ≫ coprod.inl)
      (fun k => lamPts (fst D.P.A D₀.P.A ≫ q) (snd D.P.A D₀.P.A) k ≫ coprod.inr)
  let εΓ : Fin 4 ⊕ Fin 4 → ℤ := Sum.elim Oε Oinvε
  have hL1 := LB.isLB_linComb hN φΓ εΓ

  have h0 : cls _ hL1 = 0 := by
    rw [cls_linComb hN _ _ hL1, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, pull_comp, pl, pr]
    refine Eq.trans ?_ (sub_eq_zero.2 (hadj _ (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A)))
    simp only [lam, lamPts, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨Γ₀, hΓ₀⟩ := (cls_eq_zero_iff hL1).1 h0

  let o : (D.P.A ⊗ D₀.P.A).left ⟶ (D.P.A ⊗ D₀.P.A).left :=
    (toUnit (D.P.A ⊗ D₀.P.A) ≫ lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A)).left
  have hz : ∀ k, o ≫ φΓ k = Sum.elim (fun _ : Fin 4 => (1 : D.P.A ⊗ D₀.P.A ⟶ D.P.A).left ≫ coprod.inl)
      (fun _ : Fin 4 => (1 : D.P.A ⊗ D₀.P.A ⟶ D₀.P.A).left ≫ coprod.inr) k := by
    rintro (k | k) <;> simp only [φΓ, Sum.elim_inl, Sum.elim_inr, ← Category.assoc] <;> congr 1 <;>
      fin_cases k <;>
      simp only [lamPts, o, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, ← Over.comp_left, Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, comp_one_pt, one_comp_hom, _root_.mul_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  have fe0 : FormEq (Sum.elim φΓ (fun k => o ≫ φΓ k)) (Sum.elim εΓ (fun k => - εΓ k)) φΓ εΓ := by
    intro U _ h
    have hQ : ∏ k, h (o ≫ φΓ k) ^ (- εΓ k) = 1 := by
      simp only [hz]
      rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four]
      simp only [Sum.elim_inl, Sum.elim_inr, εΓ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      simp only [neg_neg, one_smul, neg_smul]
      abel
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hQ, _root_.mul_one]
  obtain ⟨Γ, hΓ, hΓv⟩ := exists_gen hN fe0 (LB.mulGen _ _ _ _ _ Γ₀ (LB.invGen _ _ _ (LB.pullGen _ _ _ Γ₀ o)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hΓ₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hΓ₀ o)))
  have hone : ∀ (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D₀.P.A).left) (z : Z) (J), Good (JN D D₀) z J → r ≫ o = r →
      val Γ r z J = 1 := by
    intro Z r z J hJ hr
    rw [hΓv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, hr, mul_inv_cancel]
  have o₀ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have o' : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

  let ι₀ : D₀.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left := (lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A)).left
  have fe1 : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => ι₀ ≫ φΓ k) εΓ := by
    intro U _ h
    rw [Fintype.prod_empty, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, lamPts, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ι₀, ← Category.assoc,
      ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, comp_one_pt, one_comp_hom, Category.id_comp,
      _root_.one_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    simp only [one_smul, neg_smul]
    abel
  have e0 : (η[D₀.P.A] ≫ lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A)) ≫ toUnit _ ≫
      lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) =
      η[D₀.P.A] ≫ lift (1 : D₀.P.A ⟶ D.P.A) (𝟙 D₀.P.A) := by
    rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (𝟙 _), Category.id_comp, comp_lift, comp_one_pt,
      Category.comp_id, o₀]
  have key1 := gen_unique' hN (u := LB.pullGen _ _ _ Γ ι₀) (u' := LB.oneGen (JN D D₀) (Y := D₀.P.A.left)) fe1
    D₀.P.A.hom (eSec D₀.P.A) (Over.w η[D₀.P.A]) (hG _ _ D₀.P.isAb).2 (DVR.pullGen_isGen _ _ _ _ hΓ ι₀)
    (oneGen_isGen _) (fun y J hJ => by
      rw [val_pull hJ, val_one]
      refine hone _ _ y J hJ ?_
      have := congrArg (fun f => f.left) e0
      simpa only [eSec, ι₀, o, Over.comp_left] using this)
  have hΓ1 : ∀ (T : Over (Sp R)) (w : T ⟶ D₀.P.A) (y : T.left) (J), Good (JN D D₀) y J →
      val Γ (lift (1 : T ⟶ D.P.A) w).left y J = 1 := by
    intro T w y J hJ
    have := key1 T.left w.left y J hJ
    rw [val_pull hJ, val_one] at this
    rwa [show w.left ≫ ι₀ = (lift (1 : T ⟶ D.P.A) w).left by
      rw [← Over.comp_left, comp_lift, comp_one_pt, Category.comp_id]] at this
  refine ⟨Γ, hΓ, ?_⟩
  intro χ' χ hc u hu T x z J hJ
  let m : D.P.A.left ⟶ (D.P.A ⊗ D₀.P.A).left := (lift (𝟙 D.P.A) (toUnit D.P.A ≫ D₀.c χ)).left
  have pm : ∀ {X Y : Over (Sp R)} [GrpObj Y] (a b : X ⟶ Y), padd Y a b = a * b := fun _ _ => rfl
  have fe2 : FormEq (fun k => m ≫ φΓ k) εΓ
      (Sum.elim (fun k => D.Oφ (𝟙 _) χ' k ≫ coprod.inl) (fun k => D₀.Oφ q χ k ≫ coprod.inr)) (Sum.elim Oε Oinvε) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_four,
      Fin.prod_univ_four]
    simp only [φΓ, εΓ, Sum.elim_inl, Sum.elim_inr, lamPts, DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, m, pm, ← Hom.one_def, hc,
      ← Category.assoc, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, Category.id_comp, Category.comp_id, comp_one_pt]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    simp only [one_smul, neg_smul]
    abel
  have ev2 : ∀ y I, Good (JN D D₀) y I → val u (eSec D.P.A) y I = val (LB.pullGen _ _ _ Γ m) (eSec D.P.A) y I := by
    intro y I hI
    rw [val_pull hI]
    have c := hu.2 _ (𝟙 _) y I hI
    rw [Category.id_comp] at c
    have e2 : eSec D.P.A ≫ m = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) (toUnit _ ≫ D₀.c χ)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D.P.A] ≫ toUnit _) (toUnit _), o']
    rw [c, e2, hΓ1 _ _ y I hI]
  have key := gen_unique' hN (u := u) (u' := LB.pullGen _ _ _ Γ m) fe2 D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A])
    (hG _ _ D.P.isAb).2 hu.1 (DVR.pullGen_isGen _ _ _ _ hΓ m) ev2 T.left x.left z J hJ
  rw [key, val_pull hJ]
  congr 1
  rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit T)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechRepresentativeChernClassTangentValueStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCechRepresentative_chernClass_tangentValue : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (I : Type) [Fintype I] (c : I → Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (ω : I → Form (A.hom ≫ 𝟙 (Sp K))), IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (c k)) (Form.cl _ (ω k))) → ∀ v : epsR K ⟶ A, IsTangent v → ∀ (J : Type) (V : J → A.left.affineOpens) (τ : J → L.ι), (∀ j, (V j).1 ≤ L.U (τ j)) → IsRep (fun j => (V j).1) (∑ k, tanVal v (ω k) • c k) (fun j j' => dlog L v (τ j) (τ j')) := by
  first | exact @GlobalTheory.CechKS.isRep_chern_tanVal | exact GlobalTheory.CechKS.isRep_chern_tanVal | (intros; apply GlobalTheory.CechKS.isRep_chern_tanVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellFrameOfSpans
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell

theorem form_pullCol {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B)
    (w : π ≫ q = p) {σ : k →+* ℂ} {E : B.Modules} {m : ℕ} (h : Met q σ E m) (cE : Chart E m) {W : Y.Opens}
    (hW : W ≤ π ⁻¹ᵁ cE.U) (M : Matrix (Fin m) (Fin m) Γ(Y, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (j l : Fin m) :
    (h.pull π w).form (pullCol π cE.e hW M j) (pullCol π cE.e hW M l) y =
      chg (Matrix.of fun a b => ev p σ W (M a b) y) (h.G cE (PtsOver.map π w (spMap σ) y)) j l := by
  have hc : y ∈ ptsIn p σ (π ⁻¹ᵁ cE.U) := mem_ptsIn.2 (hW (mem_ptsIn.1 hy))
  have hc' : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U := hc
  have key (b : Fin m) : (cE.pull h.isVB π).crd p σ (pullCol π cE.e hW M b) y =
      fun a => ev p σ W (M a b) y := by
    funext a
    simp only [pullCol, Chart.crd_sum, Chart.crd_smul, cE.crd_pull h.isVB π w _ hW hy hc, cE.crd_frame hc',
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [(h.pull π w).form_eq (cE.pull h.isVB π) hc _ _ hy, h.pull_G π w cE hc', key, key, chg_apply]
  rfl

theorem Spans.exists_adaptedChart {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {U : X.Opens}
    {v : Fin m → Γ(F, U)} (H : Spans fl U v) (i : Fin m) :
    ∃ (s : Fin i → Γ(fl.F i.castSucc, U)) (t : Fin 1 → Γ(fl.F i.succ, U)), IsFrame s ∧
      IsFrame (fun j => (fl.π i).app U (t j)) ∧
      ∀ j, (fl.ι i.succ).app U (Sum.elim (fun l => (fl.step i).app U (s l)) t j) = v (emb i j) := by
  obtain ⟨s, hs, es⟩ := H i.castSucc
  obtain ⟨s', hs', es'⟩ := H i.succ
  have e₁ (j : Fin i) : (fl.ι i.succ).app U ((fl.step i).app U (s j)) = v (Fin.castLE i.isLt.le j) := by
    refine Eq.trans ?_ (es j)
    rw [← fl.step_ι i]
    rfl
  refine ⟨s, fun j => s' (Fin.natAdd i j), hs,
    isFrame_cokernel_π (l := i) (m := 1) (fl.step i) hs' hs fun j => ?_, ?_⟩
  · exact QCoh.injective_app_of_mono (fl.ι i.succ) U ((e₁ j).trans (es' (Fin.castAdd 1 j)).symm)
  · rintro (j | j)
    · exact e₁ j
    · refine (es' _).trans (congrArg v (Fin.ext ?_))
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rfl

theorem isCellFrame_of_spans : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) (a : ι) (E : B.Modules) (h : VMetric q E (r a)) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) (r a)) (cE : Chart E (r a)) (c' : AlgChart p σ (d + 1)) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Low (r a) → Γ(Y, W)), GlobalTheory.FlagCell.Spans fl W (GlobalTheory.FlagCell.pullCol π cE.e hW (GlobalTheory.FlagCell.uniR n)) → c'.e.source ⊆ ptsIn p σ W → (∀ y ∈ c'.e.source, ∀ s, fib e (c'.e y) a s = ev p σ W (n s) y) → IsCellFrame e π w c' a h fl cE := by
  intro k _ B Y q p π w ι _ r d e σ a E h fl cE c' W hW n H hs hn i
  obtain ⟨s, t, h₁, h₂, h₃⟩ := H.exists_adaptedChart i
  refine ⟨⟨W, s, t, h₁, h₂⟩, fun y hy => ⟨hs hy, ?_⟩⟩
  have hM : uni (fib e (c'.e y) a) = Matrix.of fun j l => ev p σ W (uniR n j l) y := by
    ext j l
    rw [← uniR_eq_uni, of_apply, uniR_apply, uniR_apply, ev_eq (hs hy)]
    split_ifs
    · rw [hn y hy, ev_eq (hs hy)]
    · exact (map_one _).symm
    · exact (map_zero _).symm
  ext j l
  rw [submatrix_apply, hM, ← form_pullCol π w (h.met σ) cE hW (uniR n) (hs hy), ← h₃, ← h₃]
  exact Met.form_restrict _ (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ (hs hy)

end GlobalTheory.FlagCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassSumOfAdicSumUnitSmulTerms
section
open IsLocalRing GlobalTheory.Poinc GlobalTheory.UT

namespace GlobalTheory.Poinc

theorem isClassSum_of_sumI : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (y : Φ.Y) (N : ℕ), 1 ≤ N → ∀ (κ : Fin s → Φ.X y) (c : Φ.Q) (V' : Type) [CommRing V'] [IsLocalRing V'] (io : Φ.V y →+* V') (e : V'ˣ) (x : V'), SumI (maximalIdeal V') (fun nu : Fin s → Φ.X y => (e : V') * io (Φ.term y (κ + N • nu) c)) x → Φ.IsClassSum y N κ c io (((e⁻¹ : V'ˣ) : V') * x) := by
  intro O _ bar q s W A _ _ Φ y N hN κ c V' _ _ io e x hx j
  classical
  have hinj : Function.Injective (fun nu : Fin s → Φ.X y => κ + N • nu) := by
    intro a b h
    have h1 : N • a = N • b := add_left_cancel h
    funext v
    have h2 : (N : ℤ) • a v = (N : ℤ) • b v := by
      rw [natCast_zsmul, natCast_zsmul]; exact congrFun h1 v
    exact smul_right_injective (Φ.X y) (by omega : (N : ℤ) ≠ 0) h2
  obtain ⟨N', -, -, -, hx⟩ := hx
  obtain ⟨S₀, hS₀⟩ := hx j
  have hF : ((fun nu : Fin s → Φ.X y => κ + N • nu) ⁻¹'
      {mu | True ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ)}).Finite :=
    (PreModel.low_finite Φ y (fun _ => True) j).preimage hinj.injOn
  refine ⟨(S₀ ∪ hF.toFinset).image (fun nu => κ + N • nu), ?_, ?_, ?_⟩
  · intro mu hmu v
    obtain ⟨nu, -, rfl⟩ := Finset.mem_image.1 hmu
    exact ⟨nu v, rfl⟩
  · intro mu hmu hn
    choose nu hnu using hmu
    have e1 : mu = κ + N • nu := funext hnu
    by_contra hlt
    refine hn (Finset.mem_image.2 ⟨nu, Finset.mem_union_right _ ?_, e1.symm⟩)
    rw [Set.Finite.mem_toFinset]
    exact ⟨trivial, by show ∑ i, qW W (Φ.δ y i) (κ + N • nu) < _; rw [← e1]; omega⟩
  · have h := Submodule.smul_mono le_rfl (le_top : N' ≤ ⊤) (hS₀ (S₀ ∪ hF.toFinset) Finset.subset_union_left)
    rw [smul_eq_mul, Ideal.mul_top, ← Finset.mul_sum] at h
    rw [Finset.sum_image hinj.injOn, map_sum]
    have h' := Ideal.mul_mem_left _ ((e⁻¹ : V'ˣ) : V') h
    rwa [mul_sub, Units.inv_mul_cancel_left] at h'

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSndOfSubsetSemiAbelianFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_image_snd_of_subset_semiAbelian_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) → ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} → IsClosed ((snd G G).left '' N) := by
  first | exact @GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint | exact GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint | (intros; apply GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedTrivialLocusRigidifiedBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivLocus_closed : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A _ L₀ N hA hL₀ hamp hN hrig
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.closedSubscheme_glue_local_condition S (TrivCond A N) (trivCond_comp A N)
    (GlobalTheory.T.lineBundleTrivialOnPullbackSquares_of_local S A N hA hN hrig) (GlobalTheory.T.exists_closedSubscheme_rigidifiedBundle_trivialLocus S A L₀ N hA hL₀ hamp hN hrig)
  refine ⟨Z, i, hi, fun T t A' _ φ' hP => ?_⟩
  rw [trivCond_iff A N T t A'.left φ' A'.hom hP.1]
  exact hZ T t

end GlobalTheory.TrivLocus
end

