import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3379
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightPowEqDegreeLogCardFiniteField
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtVert

theorem isEmpty_cxPts {k : Type} [CommRing k] {Z : Scheme.{0}} (q : Z ⟶ Sp k) (σ : k →+* ℂ) (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] : IsEmpty (CxPts q σ) := by
  refine ⟨fun y => ?_⟩
  let f : κ →+* ℂ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp (y.1.appTop.hom.comp (algebraMap κ Γ(Z, ⊤)))
  have : CharZero κ := f.charZero
  exact not_finite κ

theorem mixArch_eq_zero {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (h : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) {e : ℕ} (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : mixArch L M hr = 0 := by
  have h0 : ∀ (L' : HermLB q), L'.archInt M e hr = 0 := by
    intro L'
    refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
    have := h σ
    simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]
  simp [mixArch, FibreProj.pol, h0]

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem finite_Γ {Z : Scheme.{0}} [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] [IsAffine Z]
    (hp : IsProjOver (strHom κ Z)) (φ : Γ(Z, ⊤) →+* Z.residueField (genericPoint Z)) (hφ : Function.Bijective φ) :
    Finite Γ(Z, ⊤) := by
  have : IsProper (strHom κ Z) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have h1 : (strHom κ Z).appTop.hom.FiniteType :=
    HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) |>.1 inferInstance
  have h2 : (algebraMap κ Γ(Z, ⊤)).FiniteType := by
    have e : algebraMap κ Γ(Z, ⊤) = (strHom κ Z).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom :=
      RingHom.ext (algebraMap_eq_strHom κ Z)
    rw [e]
    exact h1.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have hft : Algebra.FiniteType κ Γ(Z, ⊤) := RingHom.finiteType_algebraMap.1 h2
  letI : Algebra κ (Z.residueField (genericPoint Z)) := (φ.comp (algebraMap κ Γ(Z, ⊤))).toAlgebra
  let ψ : Γ(Z, ⊤) →ₐ[κ] Z.residueField (genericPoint Z) := { φ with commutes' := fun _ => rfl }
  have : Algebra.FiniteType κ (Z.residueField (genericPoint Z)) := Algebra.FiniteType.of_surjective ψ hφ.2
  have : Module.Finite κ (Z.residueField (genericPoint Z)) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Finite (Z.residueField (genericPoint Z)) := Module.finite_of_finite κ
  exact Finite.of_injective φ hφ.1

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem hasDim_iff {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (d : ℕ) :
    HasDim (i (genericPoint Z)) d ↔ topologicalKrullDim Z = d := by
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  rw [HasDim, topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding h₁.def.symm]

theorem dim_zero {X : Scheme.{0}} {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] (h0 : topologicalKrullDim Z = (0 : ℕ))
    (hp : IsProjOver (strHom κ Z)) :
    Real.log (Nat.card (X.residueField (i (genericPoint Z)))) = chi κ (structureModule Z) * Real.log (Nat.card κ) := by
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)
  have hZ : ({genericPoint Z} : Set Z) = Set.univ := Set.eq_univ_of_forall hu
  have hc : IsClosed ({genericPoint Z} : Set Z) := hZ ▸ isClosed_univ
  have := isClosed_singleton_iff_isClosedImmersion.1 hc
  have : Surjective (Z.fromSpecResidueField (genericPoint Z)) :=
    ⟨fun w => ⟨IsLocalRing.closedPoint _, (hu _).trans (hu w).symm⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (Z.fromSpecResidueField (genericPoint Z))
  have : IsAffine Z := .of_isIso (inv (Z.fromSpecResidueField (genericPoint Z)))
  have : IsIso (Z.fromSpecResidueField (genericPoint Z)).appTop := inferInstanceAs (IsIso (Scheme.Hom.app _ ⊤))
  have b₁ : Function.Bijective (i.residueFieldMap (genericPoint Z)) := by
    refine ⟨RingHom.injective _, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := Z.residue_surjective _ a
    obtain ⟨b, rfl⟩ := i.stalkMap_surjective _ a
    exact ⟨X.residue _ b, by rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩
  have b₂ : Function.Bijective ((Z.fromSpecResidueField (genericPoint Z)).appTop ≫
      (Scheme.ΓSpecIso (Z.residueField (genericPoint Z))).hom) := ConcreteCategory.bijective_of_isIso _
  have e : Γ(Z, ⊤) ≃ X.residueField (i (genericPoint Z)) :=
    (Equiv.ofBijective _ b₂).trans (Equiv.ofBijective _ b₁).symm
  have : Finite Γ(Z, ⊤) := finite_Γ κ hp _ b₂
  rw [← Nat.card_congr e, chi_structureModule_of_isAffine, Module.natCard_eq_pow_finrank (K := κ)]
  simp

theorem isProjOver_strHom {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (hX : IsAmb p) {Z : Scheme.{0}}
    (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)] : IsProjOver (strHom κ Z) := by
  have := hX.finite
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have hpr' : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  exact (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom κ Z)).2 ⟨hpr', _, hH.pull_of_isClosedImmersion i⟩

end GlobalTheory.MixHtVert

namespace GlobalTheory.MixHtVert

theorem mixHt_pow_eq_topSelf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ (m : ℕ) T, IsMix p m T → ∀ (N : HermLB p) (d : ℕ), d ≤ m → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = d → T d (fun _ => N) (i (genericPoint Z)) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ) := by
  intro k _ X p hA m T hT N d
  induction d with
  | zero =>
    intro _ Z i _ _ κ _ _ _ hd
    rw [hT.zero _ _ ((hasDim_iff i 0).2 hd), dim_zero i κ hd (isProjOver_strHom hA i κ), topSelf_def,
      interNum_of_isEmpty]
  | succ e ih =>
    intro hm Z i _ _ κ _ _ _ hd
    have hZa : IsAmb (i ≫ p) := hA.sub i
    have : IsNoetherian Z := hZa.isNoetherian
    have hp := isProjOver_strHom hA i κ
    have : IsProper (strHom κ Z) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
    obtain ⟨r, hr⟩ := exists_isRatSec (N.restr i).isLB
    have hL : (N.B.pull i).IsLB := (N.restr i).isLB
    have hrec := hT.recur Z (i ≫ p) i rfl e hm hd N (fun _ => N) (N.restr i) (fun _ => N.restr i)
      (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr
    have ec : (Fin.cons N (fun _ => N) : Fin (e + 1) → HermLB p) = fun _ => N :=
      funext (Fin.cases rfl fun _ => rfl)
    rw [ec] at hrec
    rw [hrec, recVal, mixArch_eq_zero (fun σ => isEmpty_cxPts (i ≫ p) σ κ), sub_zero]
    have key := GlobalTheory.ratSec_cycle_formula κ Z hp e hd.le (N.B.pull i) hL (fun _ => N.B.pull i) (fun _ => hL) r hr
    have ec' : (Fin.cons (N.B.pull i) (fun _ => N.B.pull i) : Fin (e + 1) → LB Z) = fun _ => N.B.pull i :=
      funext (Fin.cases rfl fun _ => rfl)
    rw [ec', ← topSelf_def] at key
    have hfin : Function.HasFiniteSupport fun w => (divOfRatSec hL hr).mult w *
        interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) fun _ : Fin e => N.B.pull i :=
      (CartierDiv.finite_support_mult _).subset (Function.support_mul_subset_left _ _)
    rw [key]
    have em := (AddMonoidHom.mulRight (Real.log (Nat.card κ))).comp (Int.castAddHom ℝ) |>.map_finsum hfin
    refine .trans (finsum_congr fun z => ?_) em.symm
    change ((divOfRatSec hL hr).mult z : ℝ) * _ = (((divOfRatSec hL hr).mult z * _ : ℤ) : ℝ) * _
    by_cases hz : (divOfRatSec hL hr).mult z = 0
    · simp [hz]
    rw [Int.cast_mul, mul_assoc]
    refine congrArg _ ?_
    have hdim := VdmRec.CutSec.dim_closure_of_coheight_field (strHom κ Z) hd
      (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
    obtain ⟨W, j, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    have hrange : Set.range j = closure {j (genericPoint W)} := by
      rw [← Set.image_singleton, j.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]
    letI := algebraΓAlong κ j
    have hW : topologicalKrullDim W = e :=
      (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).symm.trans hdim
    rw [← Scheme.Hom.comp_apply, ih (by omega) W (j ≫ i) κ hW, InterModel.interNumRed_eq_interNumOn _ j _ hrange,
      interNumOn_eq_interNum_pull (appTop_algebraMap_along κ j) (fun _ => hL), topSelf_def]
    congr 2
    refine interNum_congr_cls κ _ (fun _ => LB.isLB_pull N.isLB _) (fun _ => LB.isLB_pull hL _) fun _ => ?_
    rw [CechPic.cls_pull hL, CechPic.cls_pull N.isLB, CechPic.cls_pull N.isLB, CechPic.pull_comp]

end GlobalTheory.MixHtVert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegOfFieldExtension
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.AbPol

theorem relAmple_lam_diag {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) :
    haveI := P.isAb.comm
    RelAmple P.A ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left) := by
  haveI := P.isAb.comm
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hA := P.isAb
  have hLB := P.isLB
  have hΔ := GlobalTheory.FullSiegel.cls_diag hL.mulPull P
  have hΔ' := pull_isLB (GlobalTheory.FullSiegel.isLB_lam hLB) (lift (𝟙 P.A) (𝟙 P.A)).left
  have R := GlobalTheory.relAmple_finite_pow_iso S P.A P.A (𝟙 _) P.L 2 two_pos hA hA hLB (inferInstanceAs (IsFinite (𝟙 _)))
  have R' := GlobalTheory.relAmple_finite_pow_iso S P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos hA hA (isLB_lbPow hLB 2)
    (inferInstanceAs (IsFinite (𝟙 _)))
  exact R'.2.2.2 _ hΔ' ((CechPic.cls_eq_iff (isLB_lbPow hLB 2) hΔ').1 ((CechPic.cls_lbPow hLB 2 _).trans hΔ.symm))
    (R.2.1.2 P.ample)

theorem isBiRig_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] {P : LB (G2 A).left}
    (h : IsBiRig A P) : IsBiRig ((Over.pullback f).obj A) (P.pull (Pdiv.PullbackComparison.pφ₂ f A)) := by
  obtain ⟨hP, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, hs⟩ := h
  exact ⟨pull_isLB hP _,
    gen_chartPull (chartPullLinComb P _ _ _ _ (Pdiv.PullbackComparison.pφ f A) (fun _ => Pdiv.PullbackComparison.lift_one_id f A)) t₁ ht₁,
    gen_chartPull (chartPullLinComb P _ _ _ _ (Pdiv.PullbackComparison.pφ f A) (fun _ => Pdiv.PullbackComparison.lift_id_one f A)) t₂ ht₂,
    LBIso.chartPull (Geo.Tor.chartPullPull P _ _ rfl)
      (chartPullLinComb P _ _ _ _ (Pdiv.PullbackComparison.pφ₂ f A) (fun _ => Pdiv.PullbackComparison.lift_swap f A)) hs⟩

theorem nondeg_of_fieldExtension {K K' : Type} [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp K')) [GrpObj A'] {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : IsGrpPullback A' A (spMap i) φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (hP : P.IsLB) (hP' : P'.IsLB) (e : LBIso P' (P.pull φ₂))
    (hn : ∀ (T : Over (Sp K')) (x : T ⟶ A'),
      (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1)
    (T : Over (Sp K)) (x : T ⟶ A) (hx : ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) : x = 1 := by
  letI := i.toAlgebra
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of K')) := inferInstanceAs (Nonempty (PrimeSpectrum K'))
  have : Flat (spMap i) := inferInstanceAs (Flat (specOf i))
  have : Surjective (spMap i) := inferInstanceAs (Surjective (specOf i))
  let T' : Over (Sp K) := Over.mk (pullback.fst T.hom (spMap i) ≫ T.hom)
  let q : T' ⟶ T := Over.homMk (pullback.fst T.hom (spMap i)) rfl
  have hq : Epi q.left := Flat.epi_of_flat_of_surjective (pullback.fst T.hom (spMap i))
  have key : q ≫ x = 1 := by
    refine GlobalTheory.NondegSpread.eq_one_of_generic_nondeg K K' A A' φ φ₂ h sq P P' hP hP' e hn T'
      (pullback.snd T.hom (spMap i)) pullback.condition (q ≫ x) ?_
    have z := (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 hx
    refine (CechPic.cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [CechPic.cls_pull hP] at z ⊢
    have e' : lift (snd A T' ≫ q ≫ x) (fst A T') = (A ◁ q) ≫ lift (snd A T ≫ x) (fst A T) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [e', Over.comp_left, CechPic.pull_comp, z, map_zero]
  have e₂ : q ≫ x = q ≫ (1 : T ⟶ A) := by rw [key, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi q.left).1 (congrArg (fun r => r.left) e₂))

theorem relAmple_of_generic (O K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K]
    [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB)
    (hamp : RelAmple ((Over.pullback (spMap (algebraMap O K))).obj A) (M.pull (pullback.fst A.hom _))) :
    RelAmple A M := by
  haveI := hA.proper
  haveI := hA.smooth
  refine GlobalTheory.ProperFinite.relAmple_of_geometricFibres A hM fun K' _ _ y => ?_
  obtain ⟨g, rfl⟩ : ∃ g : O →+* K', spMap g = y := ⟨(Spec.preimage y).hom, by simp [spMap]⟩
  haveI : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  let Op := Localization.AtPrime (RingHom.ker g)
  haveI : IsDomain Op := IsLocalization.isDomain_localization (RingHom.ker g).primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing Op := IsLocalization.isNoetherianRing (RingHom.ker g).primeCompl _ inferInstance
  haveI : IsIntegrallyClosed Op := isIntegrallyClosed_of_isLocalization Op (RingHom.ker g).primeCompl
    (RingHom.ker g).primeCompl_le_nonZeroDivisors
  letI : Algebra Op K := IsLocalization.localizationAlgebraOfSubmonoidLe Op K (RingHom.ker g).primeCompl
    (nonZeroDivisors O) (RingHom.ker g).primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower O Op K := IsLocalization.localization_isScalarTower_of_submonoid_le Op K
    (RingHom.ker g).primeCompl (nonZeroDivisors O) (RingHom.ker g).primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing Op K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (RingHom.ker g).primeCompl Op K
  have e₁ : spMap (algebraMap Op K) ≫ spMap (algebraMap O Op) = spMap (algebraMap O K) := by
    rw [← spMap_comp, ← IsScalarTower.algebraMap_eq]
  have hu : ∀ x : (RingHom.ker g).primeCompl, IsUnit (g x) := fun x => isUnit_iff_ne_zero.2 x.2
  let g' : Op →+* K' := IsLocalization.lift hu
  have e₂ : spMap g' ≫ spMap (algebraMap O Op) = spMap g := by
    rw [← spMap_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  let Ap := (Over.pullback (spMap (algebraMap O Op))).obj A
  have pp := isGrpPullback_pullback A (spMap (algebraMap O Op))
  have pK := isGrpPullback_pullback A (spMap (algebraMap O K))
  let φ := pp.1.lift (pullback.fst A.hom (spMap (algebraMap O K)))
    (((Over.pullback (spMap (algebraMap O K))).obj A).hom ≫ spMap (algebraMap Op K))
    (by rw [Category.assoc, e₁]; exact pK.1.w)
  have hφ : φ ≫ pullback.fst A.hom (spMap (algebraMap O Op)) = pullback.fst A.hom (spMap (algebraMap O K)) :=
    pp.1.lift_fst _ _ _
  have hpb : IsGrpPullback _ Ap (spMap (algebraMap Op K)) φ :=
    pp.cancel (pK.congr e₁.symm hφ.symm) (pp.1.lift_snd _ _ _)
  have hp : RelAmple Ap (M.pull (pullback.fst A.hom _)) :=
    GlobalTheory.AmpleGenericLocal.relAmple_of_generic Op K Ap _ φ (Out.TLinPf.isAb_pullback _ A hA) hpb _ _ (pull_isLB hM _)
      (pull_isLB hM _) (GlobalTheory.FibreAmple.lbIso_pull_comp hφ.symm (GlobalTheory.lbIso_refl (pull_isLB hM _))) hamp
  exact GlobalTheory.isAmpleLB_of_relAmple_of_isAffine (Over.mk (pullback.snd A.hom (spMap g))) (pull_isLB hM _)
    (GlobalTheory.FibreAmple.relAmple_of_factor hM pp.1 (IsPullback.of_hasPullback A.hom (spMap g)) (spMap g') e₂
      (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) hp)

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isPPol_of_field (O K' : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K']
    (j : O →+* K') (hj : Function.Injective j) (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (A' : Over (Sp K')) [GrpObj A'] {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : IsGrpPullback A' A (spMap j) φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (hP : IsBiRig A P) (hP' : P'.IsLB) (e : LBIso P' (P.pull φ₂))
    (ha : RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left))
    (hn : ∀ (T : Over (Sp K')) (x : T ⟶ A'),
      (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) : IsPPol A P := by
  haveI := hA.proper
  let K := FractionRing O
  let i : K →+* K' := IsFractionRing.lift hj
  have e₁ : spMap i ≫ spMap (algebraMap O K) = spMap j := by
    rw [← spMap_comp]
    exact congrArg spMap (RingHom.ext fun x => IsFractionRing.lift_algebraMap hj x)
  let f := spMap (algebraMap O K)
  let AK := (Over.pullback f).obj A
  have pK := Pdiv.PullbackComparison.isGrpPullback f A
  have sK := Pdiv.PullbackComparison.isSquare f A
  let ψ := pK.1.lift φ (A'.hom ≫ spMap i) (by rw [Category.assoc, e₁]; exact h.1.w)
  have hψ : ψ ≫ Pdiv.PullbackComparison.pφ f A = φ := pK.1.lift_fst _ _ _
  have hpb : IsGrpPullback A' AK (spMap i) ψ := pK.cancel (h.congr e₁.symm hψ.symm) (pK.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  have e₂ := GlobalTheory.LamPull.isSquare_unique sq (hψ ▸ isSquare_comp sψ sK)
  have hM := pull_isLB hP.1 (lift (𝟙 A) (𝟙 A)).left
  haveI : IsProper A'.hom := MorphismProperty.of_isPullback h.1 hA.proper
  have ha' : RelAmple A' ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' (pull_isLB hM φ)).2
      ((GlobalTheory.isAmpleLB_congr (pull_isLB hP' _) (pull_isLB hM φ) (GlobalTheory.SiegelPull.diag_iso sq e)).1
        ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' (pull_isLB hP' _)).1 ha))
  have hamp : RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) :=
    relAmple_of_generic O K A hA hM (GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i (IsPullback.of_hasPullback A.hom f)
      (e₁ ▸ h.1) (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) ha')
  have hPK := pull_isLB hP.1 (Pdiv.PullbackComparison.pφ₂ f A)
  refine ⟨hP, hamp, GlobalTheory.NondegSpread.nondeg_of_generic O K A AK _ _ hA pK sK P _ hP.1 hPK (GlobalTheory.lbIso_refl hPK)
    hP.2.1 hP.2.2.1 hP.2.2.2 hamp (nondeg_of_fieldExtension i AK A' hpb sψ hPK hP' ?_ hn)⟩
  exact LBIso.trans hP' (pull_isLB hP.1 _) (pull_isLB hPK _) e
    (GlobalTheory.FibreAmple.lbIso_pull_comp e₂ (GlobalTheory.lbIso_refl hPK))

theorem exists_isPPol_away : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → ∃ (A : Over (Sp (Localization.Away (∏ k, C.t k)))) (_ : GrpObj A) (_ : IsCommMonObj A) (π₀ : A.left ⟶ G₁.left) (π₂ : (G2 A).left ⟶ (G2 G₁).left), IsGrpPullback A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) π₀ ∧ IsSquare π₀ π₂ ∧ IsAbelianScheme A ∧ IsPPol A (P.pull π₂) := by
  intro g n φ hn C G₁ _ _ P ⟨hCN, _, hG, hP, hU⟩ hab
  obtain ⟨hmono, -, hcone, hdef, ht⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ (by omega) C
  have hn' : (0 : ℤ) < n := by omega
  obtain ⟨R', _, _, _, ρ, -, D, ε, hCN', hρ, hfin, -, -, href, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised C.R C.Q C.m C.t (fun k => (n : ℤ) • C.δ k) hCN hmono C.bd ht
      (fun k y z => by simp only [LinearMap.smul_apply, (hcone.mem k).1 y z])
      (fun k y => by simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_nonneg hn'.le (hcone.nonneg k y))
      (fun y hy => by
        obtain ⟨k, hk⟩ := hdef y hy
        exact ⟨k, by simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_pos hn' hk⟩)
  obtain ⟨G', _, _, π, π₂, B, U, hπ, sπ, eπ⟩ := hU R' ρ hCN' hρ hfin D ε href
  set t := ∏ k, C.t k with htd
  have ht0 : t ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => ht k
  let O := Localization.Away t
  haveI := hCN.1
  haveI := hCN.2.1
  have hle : Submonoid.powers t ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors ht0
  haveI : IsDomain O := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Submonoid.powers t) _ inferInstance
  haveI : IsIntegrallyClosed O := isIntegrallyClosed_of_isLocalization O (Submonoid.powers t) hle
  let f := spMap (algebraMap C.R O)
  let A := (Over.pullback f).obj G₁
  have hG' : IsSemiAbelian A := IsSemiAbelian.pullback f G₁ hG
  have habA : abLocus A = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G₁.hom f) z).1 ((hab _).2 fun hz =>
      z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz (IsLocalization.Away.algebraMap_isUnit t)))
  have hA : IsAbelianScheme A :=
    { comm := hG'.comm
      smooth := hG'.smooth
      proper := GlobalTheory.AbLocusProperNormal.isProper_of_abLocus_eq_univ _ _ hG' habA
      geomConnected := hG'.geomConnected }
  have pA := Pdiv.PullbackComparison.isGrpPullback f G₁
  have sA := Pdiv.PullbackComparison.isSquare f G₁
  refine ⟨A, inferInstance, inferInstance, _, _, pA, sA, hA, ?_⟩

  let κ : C.R →+* FractionRing R' := (algebraMap R' (FractionRing R')).comp ρ
  have hκ : Function.Injective κ := (IsFractionRing.injective R' (FractionRing R')).comp hρ
  have hu : IsUnit (κ t) := isUnit_iff_ne_zero.2 ((map_ne_zero_iff κ hκ).2 ht0)
  let j : O →+* FractionRing R' := IsLocalization.Away.lift t hu
  have hjκ : j.comp (algebraMap C.R O) = κ := IsLocalization.Away.lift_comp t hu
  have hj : Function.Injective j := by
    refine (IsLocalization.lift_injective_iff _).2 fun x x' => ?_
    rw [(IsLocalization.injective O hle).eq_iff, hκ.eq_iff]
  have e₁ : spMap j ≫ f = (𝟙 _ ≫ jK R') ≫ spMap ρ := by
    rw [Category.id_comp, ← spMap_comp, hjκ, spMap_comp]
  haveI := U.gen_hom
  haveI := B.isAb.comm
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have ha : IsGrpPullback B.A G' (𝟙 _ ≫ jK R') (U.gen.inv.left ≫ pullback.fst G'.hom (jK R')) :=
    (isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G' (jK R'))
  have sa := GlobalTheory.LamPull.exists_isSquare ha.1.w
  have hb := ha.comp hπ
  let ψ := pA.1.lift _ (B.A.hom ≫ spMap j) (by rw [Category.assoc _ _ f, e₁]; exact hb.1.w)
  have hψ : ψ ≫ Pdiv.PullbackComparison.pφ f G₁ = _ := pA.1.lift_fst _ _ _
  have hpb : IsGrpPullback B.A A (spMap j) ψ := pA.cancel (hb.congr e₁.symm hψ.symm) (pA.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  have e₂ := GlobalTheory.LamPull.isSquare_unique (isSquare_comp sa sπ) (hψ ▸ isSquare_comp sψ sA)
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have eL : LBIso B.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G'.hom (jK R'))) := by
    have e := (CechPic.cls_eq_iff (pull_isLB B.isLB _) (pull_isLB hLG _)).2 U.ext
    rw [CechPic.cls_pull B.isLB, CechPic.cls_pull hLG] at e
    rw [← CechPic.cls_eq_iff B.isLB (pull_isLB hLG _), CechPic.cls_pull hLG, CechPic.pull_comp, ← e,
      ← CechPic.pull_comp, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, CechPic.pull_id]
  have hΛ := GlobalTheory.FullSiegel.isLB_lam (G := B.A) B.isLB
  have hΛ' := GlobalTheory.FullSiegel.isLB_lam (G := G') hLG
  refine isPPol_of_field O _ j hj A hA B.A hpb sψ (isBiRig_pullback f G₁ hP) hΛ ?_ (relAmple_lam_diag B)
    (GlobalTheory.FullSiegel.eq_one_of_lam_triv B.isLB B.rigid B.ktriv)
  have c₁ := (CechPic.cls_eq_iff hΛ (pull_isLB hΛ' _)).2 (GlobalTheory.LamPull.lbIso_lam_pull ha hLG B.isLB eL sa)
  have c₂ := (CechPic.cls_eq_iff hΛ' (pull_isLB hP.1 _)).2 eπ
  rw [← CechPic.cls_eq_iff hΛ (pull_isLB (pull_isLB hP.1 _) _), c₁, CechPic.cls_pull hΛ', c₂,
    CechPic.cls_pull hP.1, CechPic.cls_pull (pull_isLB hP.1 _), CechPic.cls_pull hP.1, ← CechPic.pull_comp,
    ← CechPic.pull_comp, e₂]

end GlobalTheory.TChart.AbPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldEqBasicOpenExtension
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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

theorem valR_cst_eq_iota : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R) (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* FractionRing Ω), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = algebraMap Ω (FractionRing Ω) (φ r)) → ∀ (O : G.left.Opens) (h : O ≤ G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ O → ∀ θ, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') O (GlobalTheory.HeatV.cst G.hom _ h θ) = iota θ := by
  intro R _ G Ω _ _ φ x' hx c iota hiota O h hO θ
  rw [GlobalTheory.CechKSSmul.valR_appLE_comp _ G.hom (GlobalTheory.HeatV.bo R c).1 O h hO θ]
  have hz : (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)) := by
    rw [Category.assoc, hx]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have h' : ⊤ ≤ ((spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom) ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 :=
    fun p hp => h (hO hp)
  set s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c with hs
  set z := (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom with hzdef
  let F : Γ(Sp R, (Sp R).basicOpen s) →+* FractionRing Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom.comp (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom
  have hF : ∀ θ, valR z (GlobalTheory.HeatV.bo R c).1 θ = F θ := fun θ => by
    simp only [valR, dif_pos h']; rfl
  suffices e : F = iota by rw [hF]; exact DFunLike.congr_fun e θ
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (S := Γ(Sp R, (Sp R).basicOpen s)) ?_
  ext y0
  obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r = y0 :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y0, by simp⟩
  have e1 : algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      GlobalTheory.HeatV.resV R c r := rfl
  change F (GlobalTheory.HeatV.resV R c r) = iota (GlobalTheory.HeatV.resV R c r)
  rw [hiota]
  show (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom
    ((z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom (GlobalTheory.HeatV.resV R c r)) = _
  have e2 : (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op ≫ z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h' =
      z.appTop := by
    exact (Scheme.Hom.map_appLE z h' _).trans (Scheme.Hom.appLE_eq_app z)
  have e3 : (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom
      (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      z.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [← e2]; rfl
  rw [show (GlobalTheory.HeatV.resV R c r) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) from rfl, e3]
  rw [hz]
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [n]
  simp

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToPdivisibleOmegaSurjectiveStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_hodge_to_pdivisible_omega_surjective : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K], (p : K) = 0 → ∀ (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p K) (t : G.TorsionTower A) (ψ : PrimitiveSubmodule A →ₗ[K] G.omega), (∀ c : PrimitiveSubmodule A, IsCan t c.1 (G.rigOfOmega (ψ c))) → Function.Surjective ψ := by
  first | exact @GlobalTheory.PtExt.surjective_of_isCan_field | exact GlobalTheory.PtExt.surjective_of_isCan_field | (intros; apply GlobalTheory.PtExt.surjective_of_isCan_field <;> assumption)
end

