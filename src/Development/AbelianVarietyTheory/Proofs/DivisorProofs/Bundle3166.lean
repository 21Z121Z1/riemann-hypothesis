import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0818
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws5
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0115
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.TwoUnifTors

set_option maxHeartbeats 1600000 in
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorRef in

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G G' : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (D D' : DegData V (maximalIdeal V)) (U : Unif (maximalIdeal V) D A G) (U' : Unif (maximalIdeal V) D' A G'), ∃ ε : D.toPre.X ≃+ D'.toPre.X, (∀ y r r', PsiCoord D.toPre y r → PsiCoord D'.toPre (ε y) r' → Associated r r') ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (k : ℕ) (q : QkPt D.toPre K k) (q' : QkPt D'.toPre K k) (x : TFK (R := V) K ⟶ A.A), 1 ≤ k → QkToAkU U.toUnifPre K k q x → QkToAkU U'.toUnifPre K k q' x → CongMod k q'.y (ε q.y) := by
  intro V _ _ _ _ hc A G G' _ _ _ _ hG hG' D D' U U'
  have hCN : IsCN V := ⟨inferInstance, inferInstance, hc, inferInstance⟩
  have aV := admissibleBase_of_completeNormalLocalCharZero hCN

  have hext := GlobalTheory.homExtDvr_and_laws.1
  have m₁ : IsMonHom (U.gen.hom ≫ U'.gen.inv) := by
    haveI := U.gen_hom; haveI := U'.gen_hom; infer_instance
  have m₂ : IsMonHom (U'.gen.hom ≫ U.gen.inv) := by
    haveI := U.gen_hom; haveI := U'.gen_hom; infer_instance
  obtain ⟨f, ⟨hfm, hfK⟩, -⟩ := hext V G G' hG hG' (U.gen.hom ≫ U'.gen.inv) m₁
  obtain ⟨g, ⟨hgm, hgK⟩, -⟩ := hext V G' G hG' hG (U'.gen.hom ≫ U.gen.inv) m₂
  have fg : f ≫ g = 𝟙 G := by
    have u := hext V G G hG hG (𝟙 _) inferInstance
    refine u.unique ⟨inferInstance, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_comp, hfK, hgK]; simp
  have gf : g ≫ f = 𝟙 G' := by
    have u := hext V G' G' hG' hG' (𝟙 _) inferInstance
    refine u.unique ⟨inferInstance, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_comp, hfK, hgK]; simp
  let ψ : G ≅ G' := ⟨f, g, fg, gf⟩
  haveI : IsMonHom ψ.hom := hfm
  have hψK : (Over.pullback (jK V)).map ψ.hom ≫ U'.gen.hom = U.gen.hom := by
    change (Over.pullback (jK V)).map f ≫ U'.gen.hom = U.gen.hom
    rw [hfK]; simp

  have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.specOf_id V
  have hpb : IsGrpPullback G G' (spMap (RingHom.id V)) ψ.hom.left := by
    rw [hid]; exact isGrpPullback_of_iso ψ
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hpb (isGrpPullback_pullback G' (spMap (RingHom.id V)))
  have he : eSec G ≫ bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V)) =
      spMap (RingHom.id V) ≫ eSec G' := by
    rw [hbc]; exact GlobalTheory.PolBaseChange.eSec_comm hpb
  let L' : RigLB G := ⟨U'.LG.L.pull (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V))),
    rigPullOf (G' := G) (G := G') (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V))) (spMap (RingHom.id V))
      he U'.LG.L U'.LG.rig, pull_isLB U'.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G) (G := G') (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V)))
      (spMap (RingHom.id V)) he U'.LG.L U'.LG.rig U'.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap (RingHom.id V)) G' G _ he U'.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U'.LG.isLB _))

  have wA : LBIso (A.L.pull U.gen.hom.left)
      (U'.LG.L.pull (pullback.fst G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)))) := by
    have k₁ : pullback.fst G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)) =
        ((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V) := by
      rw [hbc]; exact (pullback.lift_fst _ _ _).symm
    have k₂ : U.gen.hom.left = ((Over.pullback (jK V)).map ψ.hom).left ≫ U'.gen.hom.left := by
      rw [← Over.comp_left, hψK]
    rw [k₁, k₂]
    have t₁ : LBIso (A.L.pull (((Over.pullback (jK V)).map ψ.hom).left ≫ U'.gen.hom.left))
        ((A.L.pull U'.gen.hom.left).pull ((Over.pullback (jK V)).map ψ.hom).left) :=
      LBIso.symm ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen A.isLB _ _⟩
    have t₂ : LBIso ((A.L.pull U'.gen.hom.left).pull ((Over.pullback (jK V)).map ψ.hom).left)
        ((U'.LG.L.pull (pullback.fst G'.hom (jK V))).pull ((Over.pullback (jK V)).map ψ.hom).left) :=
      GlobalTheory.RigidBundleGlue.LBIso.pull U'.ext _
    have t₃ : LBIso ((U'.LG.L.pull (pullback.fst G'.hom (jK V))).pull ((Over.pullback (jK V)).map ψ.hom).left)
        (U'.LG.L.pull (((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V))) :=
      ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U'.LG.isLB _ _⟩
    exact (t₁.trans (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
      (pull_isLB (pull_isLB U'.LG.isLB _) _) t₂).trans (pull_isLB A.isLB _)
      (pull_isLB (pull_isLB U'.LG.isLB _) _) (pull_isLB U'.LG.isLB _) t₃

  obtain ⟨W, hW, hWψ⟩ := GlobalTheory.psiOnExists V (maximalIdeal V) aV D'
  have hWg : (specOf (RingHom.id V)).base (genericPoint (Spec (CommRingCat.of V))) ∈ W := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.specOf_id]; exact hW
  have hI : (maximalIdeal V).map (RingHom.id V) ≤ maximalIdeal V := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', -, hgen, hPU⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds V V _ _ aV aV (RingHom.id V) hI D' A G'
    hG' U' W hWψ hWg G bc mbc A rfl U.gen U.gen_hom wA L' wL he gL rL

  have h5 : Laws5 := GlobalTheory.allSixLaws.2.2.2.2.1
  have hUq : UnifUniqSt := GlobalTheory.allSixLaws.2.2.2.2.2.unifUniq
  have hQ : QkPullExistsSt := qkPullExists GlobalTheory.allSixLaws.1.globalFns

  have hLG : LBIso U''.LG.L U.LG.L := by
    refine GlobalTheory.FewAtTest.lbIso_of_generic hG U''.LG U.LG ?_
    have e1 := U''.ext
    rw [hgen] at e1
    exact LBIso.trans (pull_isLB U''.LG.isLB _) (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) (LBIso.symm e1) U.ext
  obtain ⟨wL₀, hwg₀, hwm₀⟩ := GlobalTheory.RigLBIso.exists_rig_iso_of_iso _ G U''.LG U.LG hLG
  obtain ⟨hD₀, hlev₀, -⟩ := hUq V (maximalIdeal V) aV D D'' A A G hG U U'' wL₀ hwg₀ hwm₀
  have hpb₀ : IsGrpPullback G G (spMap (RingHom.id V)) (Iso.refl G).hom.left := by
    haveI : IsMonHom (Iso.refl G).hom := by show IsMonHom (𝟙 G); infer_instance
    rw [hid]; exact isGrpPullback_of_iso (Iso.refl G)
  obtain ⟨bc₀, mbc₀, hbc₀⟩ := grpPullback_iso hpb₀ (isGrpPullback_pullback G (spMap (RingHom.id V)))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id V)) = 𝟙 _ := hbc₀
  have hPU₀ : IsPullUnif (RingHom.id V) hD₀ bc₀ U U'' :=
    isPullUnif_of_uniq U U'' hD₀ wL₀ hwg₀ hwm₀ hlev₀ bc₀ hbc₀'
  have hbc' : bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)) = ψ.hom.left := hbc

  have k₁ : U.gen.inv ≫ (Over.pullback (jK V)).map ψ.hom = U'.gen.inv := by
    rw [Iso.inv_comp_eq, ← hψK, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have k₂ : ((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ ψ.hom.left := pullback.lift_fst _ _ _
  refine ⟨hD₀.xe.symm.trans hD.xe, fun y r r' hr hr' => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := GlobalTheory.SameCoord.psiCoord_of_isPullDeg_id hD₀ (hD₀.xe.symm y) r
      (by rw [AddEquiv.apply_symm_apply]; exact hr)
    obtain ⟨u', hu'⟩ := GlobalTheory.SameCoord.psiCoord_of_isPullDeg_id hD (hD₀.xe.symm y) r' hr'
    have h1 : Associated (u * r) (u' * r') := GlobalTheory.TorRef.psiCoord_associated hu hu'
    exact ((associated_unit_mul_left r u u.isUnit).symm.trans h1).trans (associated_unit_mul_left r' u' u'.isUnit)
  · intro K _ _ _ k q q' x hk hq hq'
    obtain ⟨f, hf, -, hinj, -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G D U K k hk
    obtain ⟨f', hf', -, hinj', -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G' D' U' K k hk
    obtain ⟨f'', hf'', hsurj'', -, -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G D'' U'' K k hk
    obtain ⟨w, hw⟩ := U.ext
    have hxk := (hq w hw).1
    obtain ⟨q'', hq''⟩ := hsurj'' x hxk
    have hF : ∀ r : V, algebraMap (FractionRing V) K (algebraMap V (FractionRing V) r) =
        algebraMap (FractionRing V) K (algebraMap V (FractionRing V) ((RingHom.id V) r)) := fun _ => rfl

    obtain ⟨p, hp₁, hp₂⟩ := hQ V V (RingHom.id V) D.toPre D''.toPre hD₀ K hF k q''
    have A₁ : QkToAkU U''.toUnifPre K k q'' (f p) :=
      h5.qkBaseChange V V _ _ aV aV (RingHom.id V) D A G U G bc₀ mbc₀ A D'' hD₀ U'' hPU₀ K hF k hk p (f p) q''
        (f p) hp₁ hp₂ (by rw [hbc₀', Category.comp_id, hgen]) ((hf p (f p)).2 rfl)
    have hpx : f p = x := ((hf'' q'' (f p)).1 A₁).trans hq''
    obtain ⟨z, hz, -⟩ := (hinj p q).1 (hpx.trans ((hf q x).1 hq))

    obtain ⟨p', hp₁', hp₂'⟩ := hQ V V (RingHom.id V) D'.toPre D''.toPre hD K hF k q''
    have B₁ : QkToAkU U''.toUnifPre K k q'' (f' p') :=
      h5.qkBaseChange V V _ _ aV aV (RingHom.id V) D' A G' U' G bc mbc A D'' hD U'' hPU K hF k hk p' (f' p') q''
        (f' p') hp₁' hp₂' (by rw [hgen, hbc', ← k₂, ← k₁, Over.comp_left]; simp only [Category.assoc])
        ((hf' p' (f' p')).2 rfl)
    have hpx' : f' p' = x := ((hf'' q'' (f' p')).1 B₁).trans hq''
    obtain ⟨z', hz', -⟩ := (hinj' p' q').1 (hpx'.trans ((hf' q' x).1 hq'))
    refine ⟨z' - hD.xe (hD₀.xe.symm z), ?_⟩
    show q'.y = hD.xe (hD₀.xe.symm q.y) + k • (z' - hD.xe (hD₀.xe.symm z))
    rw [hz', hz]
    simp only [map_add, map_nsmul]
    rw [← hp₁, hp₁', AddEquiv.apply_symm_apply, smul_sub]
    abel

end GlobalTheory.TwoUnifTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromP
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKGeo.IntDvd

open IsDedekindDomain HeightOneSpectrum

theorem int_dvd_of_local (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) (c : ℤ)
    (h : ∀ v : AwayP p, ∃ y ∈ v.1.adicCompletionIntegers ℚ,
      algebraMap ℚ (v.1.adicCompletion ℚ) (c : ℚ) = algebraMap ℚ (v.1.adicCompletion ℚ) ((n : ℤ) : ℚ) * y) :
    (n : ℤ) ∣ c := by
  induction n using Nat.strong_induction_on generalizing c with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp
  · obtain ⟨ℓ, hℓ, n₁, hn₁⟩ : ∃ ℓ, ℓ.Prime ∧ ∃ n₁, n = ℓ * n₁ :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
    have hℓp : ℓ ≠ p := by
      intro he
      have h3 : ℓ.Coprime p := Nat.Coprime.coprime_dvd_left ⟨n₁, hn₁⟩ hc
      rw [he, Nat.coprime_self] at h3
      exact (Fact.out : p.Prime).one_lt.ne' h3
    let w : HeightOneSpectrum ℤ := ⟨Ideal.span {(ℓ : ℤ)},
      (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).2 (Nat.prime_iff_prime_int.1 hℓ),
      by simp [hℓ.ne_zero]⟩
    have hw : w.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro he
      rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at he
      simp only [Int.natAbs_natCast] at he
      exact hℓp he
    let v : AwayP p := ⟨w, hw⟩
    have hval : ∀ c : ℤ, Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (c : ℚ)) = v.1.intValuation c := by
      intro c
      rw [← valuation_of_algebraMap (K := ℚ), ← valuedAdicCompletion_eq_valuation]
      rfl
    have hℓc : (ℓ : ℤ) ∣ c := by
      obtain ⟨y, hy, e⟩ := h v
      have hy' : Valued.v y ≤ 1 := (mem_adicCompletionIntegers ℤ ℚ v.1).1 hy
      have h1 : v.1.intValuation c ≤ v.1.intValuation (n : ℤ) := by
        rw [← hval, ← hval, e, map_mul]
        exact mul_le_of_le_one_right' hy'
      have h2 : v.1.intValuation (n : ℤ) < 1 :=
        (intValuation_lt_one_iff_mem _ _).2 (Ideal.mem_span_singleton.2 ⟨n₁, by rw [hn₁]; push_cast; ring⟩)
      exact Ideal.mem_span_singleton.1 ((intValuation_lt_one_iff_mem _ _).1 (lt_of_le_of_lt h1 h2))
    obtain ⟨c₁, rfl⟩ := hℓc
    have hn₁pos : 0 < n₁ := by
      rcases Nat.eq_zero_or_pos n₁ with h0 | h0
      · rw [h0, mul_zero] at hn₁; omega
      · exact h0
    have hlt : n₁ < n := by
      rw [hn₁]; exact lt_mul_left hn₁pos hℓ.one_lt
    have hc₁ : n₁.Coprime p := Nat.Coprime.coprime_dvd_left ⟨ℓ, by rw [hn₁, Nat.mul_comm]⟩ hc
    have hd : (n₁ : ℤ) ∣ c₁ := ih n₁ hlt hn₁pos hc₁ c₁ fun v' => by
      obtain ⟨y, hy, e⟩ := h v'
      refine ⟨y, hy, ?_⟩
      have hne : algebraMap ℚ (v'.1.adicCompletion ℚ) ((ℓ : ℤ) : ℚ) ≠ 0 :=
        (map_ne_zero _).2 (by exact_mod_cast hℓ.ne_zero)
      apply mul_left_cancel₀ hne
      rw [← map_mul, ← _root_.mul_assoc, ← map_mul, ← Int.cast_mul, ← Int.cast_mul, e, hn₁]
      push_cast
      ring
    rw [hn₁]
    push_cast
    exact mul_dvd_mul_left _ hd

theorem int_dvd_of_eq_mul_isIntAf : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (c : ℤ) (a : AfP p),
    IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c := by
  intro p _ n hn hc c a ha e
  refine int_dvd_of_local p n hn hc c fun v => ⟨AfP.eval v a, ha v, ?_⟩
  have e' := congrArg (AfP.eval v) e
  rw [(AfP.eval v).commutes, map_mul, map_natCast] at e'
  rw [e']
  simp

end GlobalTheory.LKGeo.IntDvd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionMixedChernForms
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory Metric
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixLogSec

theorem exists_integrableOn {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {D : ℕ} [SecondCountableTopology (CxPts p σ)] (hσ : Function.Injective σ) (L : Fin D → MLine p σ)
    (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (ε : ℤˣ) (c : AlgChart p σ D)
    {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ∃ O ∈ 𝓝 y, IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s) ∩ O) (part L ε) := by
  have : IsDomain k := hσ.isDomain σ
  set i := pick M.φ.isLB y
  have hi : y ∈ ptsIn p σ (M.B.U i) := mem_pick _ y
  have hT' := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U i))).mem_nhds (mem_over c.e hy hi)
  have hd : ∀ᶠ v in 𝓝 (c.e y), DifferentiableAt ℂ (ev p σ _ (s.f i) ∘ c.e.symm) v :=
    (c.holo _ _).eventually_differentiableAt hT'
  have hfr : ∃ᶠ v in 𝓝 (c.e y), (ev p σ _ (s.f i) ∘ c.e.symm) v ≠ 0 := by
    have h := Measure.dense_of_ae (SemiPosBir.ae_mem hσ c (U := nonzeroLocus s) ⟨_, hs⟩)
    have h₁ := mem_closure_iff_frequently.1 (h (c.e y))
    refine (h₁.and_eventually hT').mono ?_
    rintro v ⟨h₂, h₃⟩
    exact (secVal_ne_zero_iff s h₃.2).2 (h₂ h₃.1)
  obtain ⟨δ, hδ, -, hint⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero volume hd hfr
  obtain ⟨η, hη, hηs⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hT' (ball_mem_nhds _ hδ))
  have hcont : ContinuousOn (fun v => dens L c (c.e.symm v)) c.e.target :=
    (GlobalTheory.T.continuousOn_mixedChernFormDensityInChart k X p σ D L c).comp c.e.continuousOn_symm c.e.mapsTo_symm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (c.e y) η).exists_bound_of_continuousOn
    (hcont.mono fun v hv => (hηs hv).1.1)
  set O := c.e.source ∩ c.e ⁻¹' ball (c.e y) η
  have hO : IsOpen O := c.e.continuousOn.isOpen_inter_preimage c.e.open_source isOpen_ball
  set S := ptsIn p σ (nonzeroLocus s) ∩ O
  have hS : IsOpen S := (isOpen_ptsIn _).inter hO
  have hSs : S ⊆ c.e.source := fun z hz => hz.2.1
  have him : c.e '' S ⊆ closedBall (c.e y) η := by
    rintro _ ⟨z, hz, rfl⟩
    exact ball_subset_closedBall hz.2.2
  have hSi (z) (hz : z ∈ S) : z ∈ ptsIn p σ (M.B.U i) := by
    have := (hηs (him (mem_image_of_mem _ hz))).1.2
    rwa [mem_preimage, c.e.left_inv (hSs hz)] at this
  have hne (z) (hz : z ∈ S) : ev p σ _ (s.f i) z ≠ 0 := (secVal_ne_zero_iff s (hSi z hz)).2 hz.1
  have heq (z) (hz : z ∈ S) : M.logSec s z = Real.log ‖ev p σ _ (s.f i) z‖ - M.φ.φ i z / 2 := by
    rw [MLine.logSec, M.φ.nsq_eq (secVal_mem s) (hSi z hz), secVal_apply,
      Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hne z hz))) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hm := measurableSet_image c.e hS.measurableSet hSs
  refine ⟨O, hO.mem_nhds ⟨hy, mem_ball_self hη⟩, LogNormInt.integrableOn_of_chart c.e
    (fun A hA hAs => GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply k X p σ D L ε c A hA hAs) hS.measurableSet hSs
    (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top (fun v hv => ENNReal.ofReal_le_ofReal ?_) ?_ ?_⟩
  · have h := hC v (him hv)
    rw [Real.norm_eq_abs, abs_le] at h
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simpa using h.2
    · simpa [neg_le] using h.1
  · refine ContinuousOn.congr (fun z hz => ContinuousAt.continuousWithinAt ?_) heq
    exact ((((continuousOn_ev (s.f i)).continuousAt ((isOpen_ptsIn _).mem_nhds (hSi z hz))).norm.log
      (norm_ne_zero_iff.2 (hne z hz))).sub ((M.cInf i z (hSi z hz)).continuousAt.div_const 2))
  · have hsub : c.e '' S ⊆ ball (c.e y) δ := fun v hv => (hηs (him hv)).2
    have h₁ : IntegrableOn (fun v => (M.φ.φ i ∘ c.e.symm) v / 2) (c.e '' S) :=
      (((((contDiffOn_chart (M.cInf i) c).continuousOn.mono fun v hv => (hηs hv).1).div_const
        2).integrableOn_compact (isCompact_closedBall _ _)).mono_set him)
    refine ((hint.mono_set hsub).sub h₁).congr ?_
    filter_upwards [ae_restrict_mem hm] with v hv'
    obtain ⟨z, hz, rfl⟩ := hv'
    simp only [Function.comp_apply, Pi.sub_apply, c.e.left_inv (hSs hz)]
    exact (heq z hz).symm

theorem intg_logSec : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro F _ X _ _ p σ D hp hsm L M s hs
  have := CxPts.compactSpace σ hp
  have := CxPts.secondCountableTopology_of_isProjOver σ hp
  have key (ε : ℤˣ) : Integrable (M.logSec s) (part L ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s) ∩ O) (part L ε) :=
      have ⟨c, hc⟩ := AlgChart.exists_mem_source (D := D) y
      exists_integrableOn σ.injective L M s hs ε c hc
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    have h₁ : IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s)) (part L ε) := by
      refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
      obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
      exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (s := ptsIn p σ (nonzeroLocus s))
      (mem_ae_iff.2 (GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ σ.injective hp D L ε _ hs))] at h₁
  exact ⟨key 1, key (-1)⟩

end GlobalTheory.MixLogSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFiniteStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_pullback_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left), IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  first | exact @GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite | exact GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite | (intros; apply GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnalyticSNCOfAlgebraicSNCSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → IsSNC A M.φ.locPot (M.φ.locSec (secVal p σ s)) (fun a => ((divOfSec M.φ.isLB s hs).mult (z a)).toNat) (fun a => Set.range (ptMap (closι (z a)) rfl σ)) := by
  first | exact @GlobalTheory.SecSnc.isSNC_locSec | exact GlobalTheory.SecSnc.isSNC_locSec | (intros; apply GlobalTheory.SecSnc.isSNC_locSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedLocusPullbackLineBundlesIsomorphic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixTrivLocus

theorem lbIso_pull_comp' {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem isoLocus_closed : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (Z₁ : Scheme.{0}) [IsLocallyNoetherian Z₁] (t₁ : Z₁ ⟶ Sp Rg) (A₁ B₁ : Over Z₁) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → RelAmple A L → IsGrpPullback A₁ A t₁ φA₁ → IsGrpPullback B₁ B t₁ φB₁ → IsMonHom Φ₁ → ∃ (Z : Scheme.{0}) (i : Z ⟶ Z₁), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (u : T ⟶ Z₁) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A₁ u ψA → IsGrpPullback B' B₁ u ψB → Φ'.left ≫ ψB = ψA ≫ Φ₁.left → (LBIso (L.pull (ψA ≫ φA₁)) ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ↔ ∃ w : T ⟶ Z, w ≫ i = u) := by
  intro Rg _ A B _ _ L M eA eB Z₁ _ t₁ A₁ B₁ _ _ φA₁ φB₁ Φ₁ hA hB hL hM hgA hgB hamp hpA hpB hΦ
  haveI : IsMonHom Φ₁ := hΦ
  haveI : IsCommMonObj A := hA.comm
  haveI : IsCommMonObj A₁ := GlobalTheory.isCommMonObj_of_grpPullback _ _ A A₁ t₁ φA₁ hpA
  obtain ⟨hA₁, hL₁, hrA₁, haA₁⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ t₁ A A₁ φA₁ L
    hpA hA hL ⟨eA, hgA⟩ hamp
  have hrB₁ : Out.Rigidified B₁ (M.pull φB₁) := GlobalTheory.PolBaseChange.rigidified_pull hpB ⟨eB, hgB⟩
  have hM₁ : (M.pull (Φ₁.left ≫ φB₁)).IsLB := pull_isLB hM _
  have hN : (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁)).IsLB := LB.isLB_div hM₁ hL₁
  have hrN : Out.Rigidified A₁ (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁)) := by
    refine (GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L.pull φA₁) (M.pull (Φ₁.left ≫ φB₁)) (eSec A₁)).1 ?_
    obtain ⟨s, hs⟩ := hrA₁
    obtain ⟨t, ht⟩ := hrB₁
    have e1 : LBIso ((L.pull φA₁).pull (eSec A₁)) ((M.pull φB₁).pull (eSec B₁)) :=
      GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    have hc : eSec A₁ ≫ Φ₁.left = eSec B₁ := congrArg (fun z => z.left) (IsMonHom.one_hom Φ₁)
    have e2 : LBIso ((M.pull φB₁).pull (eSec B₁)) ((M.pull (Φ₁.left ≫ φB₁)).pull (eSec A₁)) :=
      GlobalTheory.HomFixTransport.lbIso_pull_pull hM _ _ _ _ (by rw [← Category.assoc, hc])
    exact LBIso.trans (pull_isLB hL₁ _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM₁ _) e1 e2
  obtain ⟨Z, i, hi, H⟩ := GlobalTheory.T.trivial_locus_rigidified_bundle_closed_seesaw Z₁ A₁ (L.pull φA₁) (LB.div (M.pull (Φ₁.left ≫ φB₁)) (L.pull φA₁))
    hA₁ hL₁ haA₁ hN hrN
  refine ⟨Z, i, hi, fun T u A' B' _ _ ψA ψB Φ' hpA' hpB' hc => ?_⟩
  refine Iff.trans ?_ ((GlobalTheory.IsoExtend.lbIso_pull_iff_gen (L.pull φA₁) (M.pull (Φ₁.left ≫ φB₁)) ψA).trans
    (H T u A' ψA hpA'))
  have a1 : LBIso (L.pull (ψA ≫ φA₁)) ((L.pull φA₁).pull ψA) := lbIso_pull_comp' hL φA₁ ψA
  have a2 : LBIso ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ((M.pull (Φ₁.left ≫ φB₁)).pull ψA) :=
    GlobalTheory.HomFixTransport.lbIso_pull_pull hM _ _ _ _ (by rw [← Category.assoc, hc, Category.assoc])
  have h1 := pull_isLB hL (ψA ≫ φA₁)
  have h2 := pull_isLB hL₁ ψA
  have h3 := pull_isLB (pull_isLB hM (ψB ≫ φB₁)) Φ'.left
  have h4 := pull_isLB hM₁ ψA
  exact ⟨fun h => GlobalTheory.HomFixTransport.lbIso_congr h1 h2 h3 h4 (LBIso.symm a1) h a2,
    fun h => GlobalTheory.HomFixTransport.lbIso_congr h2 h1 h4 h3 a1 h (LBIso.symm a2)⟩

end GlobalTheory.HomFixTrivLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinementStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → IsMetricFr E' (pullGram E H φ f hf) := by
  first | exact @GlobalTheory.ChernCalc.isMetricFr_pullGram | exact GlobalTheory.ChernCalc.isMetricFr_pullGram | (intros; apply GlobalTheory.ChernCalc.isMetricFr_pullGram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefShiftedFubiniStudyOfShortGeneratorsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNef_shifted_fubiniStudy_of_short_generators : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → (L.shift (fun _ => t) (fun _ => rfl)).IsNef D := by
  first | exact @GlobalTheory.ImageModel.isNef_shift_of_isShortGen | exact GlobalTheory.ImageModel.isNef_shift_of_isShortGen | (intros; apply GlobalTheory.ImageModel.isNef_shift_of_isShortGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegOfPeriodicOfIsRegSubStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReg_of_periodic_of_isReg_sub' : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) (pre u.ex (W i))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i), h i (z + l) = h i z) → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ i, IsReg u.ex (W i) (h i) := by
  first | exact @GlobalTheory.CechPer.isReg_of_periodic_of_isReg_sub | exact GlobalTheory.CechPer.isReg_of_periodic_of_isReg_sub | (intros; apply GlobalTheory.CechPer.isReg_of_periodic_of_isReg_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarieStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∃ x : Fin D → X.functionField, IsTranscendenceBasis ℤ x) ∧ ∀ x : Fin D → X.functionField, AlgebraicIndependent ℤ x → IsTranscendenceBasis ℤ x := by
  first | exact @GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField | exact GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField | (intros; apply GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField <;> assumption)
end

