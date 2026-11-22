import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0521
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2952
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSymplecticLevelLiftClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevLift

theorem exists_eq_val_add {J : Type} {n : ℕ} [NeZero n] (a : J → ℤ) :
    ∃ b : J → ℤ, a = (fun i => (((a i : ZMod n)).val : ℤ)) + n • b :=
  ⟨fun i => a i / n, funext fun i => by
    rw [Pi.add_apply, Pi.smul_apply, ZMod.val_intCast, nsmul_eq_mul]
    exact (Int.emod_add_mul_ediv (a i) n).symm⟩

section Count

variable {G : Type} [CommGroup G] {J : Type} [Fintype J] [DecidableEq J] {n : ℕ} [NeZero n] (f : (J → ℤ) → G)
  (hadd : ∀ a b, f (a + b) = f a * f b) (hker : ∀ a, f a = 1 ↔ ∃ b, a = n • b)
include hadd hker

theorem eq_val (a : J → ℤ) : f a = f (fun i => (((a i : ZMod n)).val : ℤ)) := by
  obtain ⟨b, hb⟩ := exists_eq_val_add (n := n) a
  conv_lhs => rw [hb]
  rw [hadd, (hker (n • b)).2 ⟨b, rfl⟩, _root_.mul_one]

theorem inj : Function.Injective (fun c : J → ZMod n => f (fun i => ((c i).val : ℤ))) := by
  intro c c' h
  simp only at h
  have h1 : f ((fun i => ((c i).val : ℤ)) - (fun i => ((c' i).val : ℤ))) = 1 := by
    have e := hadd ((fun i => ((c i).val : ℤ)) - (fun i => ((c' i).val : ℤ))) (fun i => ((c' i).val : ℤ))
    rw [sub_add_cancel, h] at e
    exact mul_eq_right.1 e.symm
  obtain ⟨b, hb⟩ := (hker _).1 h1
  funext i
  have e := congrFun hb i
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at e
  have e2 := congrArg (fun z : ℤ => (z : ZMod n)) e
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul] at e2
  exact sub_eq_zero.1 e2

theorem card_eq (htors : ∀ a, f a ^ n = 1) (hsurj : ∀ x : G, x ^ n = 1 → ∃ a, f a = x) :
    Nat.card {x : G // x ^ n = 1} = n ^ Fintype.card J := by
  let F : (J → ZMod n) → {x : G // x ^ n = 1} := fun c => ⟨f (fun i => ((c i).val : ℤ)), htors _⟩
  have hF : Function.Bijective F := ⟨fun c c' e => inj f hadd hker (congrArg Subtype.val e), fun x => by
    obtain ⟨a, ha⟩ := hsurj x.1 x.2
    exact ⟨fun i => (a i : ZMod n), Subtype.ext (by rw [← ha, eq_val f hadd hker a])⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

theorem surj (htors : ∀ a, f a ^ n = 1) (hcard : Nat.card {x : G // x ^ n = 1} = n ^ Fintype.card J) :
    ∀ x : G, x ^ n = 1 → ∃ a, f a = x := by
  intro x hx
  let F : (J → ZMod n) → {x : G // x ^ n = 1} := fun c => ⟨f (fun i => ((c i).val : ℤ)), htors _⟩
  have hFi : Function.Injective F := fun c c' e => inj f hadd hker (congrArg Subtype.val e)
  have hne : Nat.card {x : G // x ^ n = 1} ≠ 0 := by
    rw [hcard]; exact pow_ne_zero _ (NeZero.ne n)
  haveI : Finite {x : G // x ^ n = 1} := Nat.finite_of_card_ne_zero hne
  have hle : Nat.card {x : G // x ^ n = 1} ≤ Nat.card (J → ZMod n) := by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  obtain ⟨c, hc⟩ := (hFi.bijective_of_nat_card_le hle).2 ⟨x, hx⟩
  exact ⟨_, congrArg Subtype.val hc⟩

end Count

end GlobalTheory.LevLift

namespace GlobalTheory.LevLift

theorem exists_level_lift : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (βV : cycAway n →+* V) (π : V →+* K), Function.Surjective π → ∀ (c : SiegPre g n (zetaAway n) (spMap (π.comp βV))), c.Principal → ∀ (AV : Over (Sp V)) [GrpObj AV] [IsCommMonObj AV] (φ : c.A.left ⟶ AV.left) (φ₂ : (G2 c.A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV → IsGrpPullback c.A AV (spMap π) φ → IsSquare φ φ₂ → PV.IsLB → (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) → (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) → LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) → Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) → (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) → LBIso c.P (PV.pull φ₂) → ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp V)) ⟶ AV), (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ n = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp V) (β : cycAway n →+* k) (z : kˣ), x ≫ spMap βV = spMap β → (z : k) = β (zetaAway n) → (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ g' : Over.mk x ⟶ AV, g' ^ n = 1 → ∃ a, toUnit _ ≫ lev a = g') ∧ ∀ a b, Out.WeilIs AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) n (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b)))) ∧ ∀ a, (c.lev a).left ≫ φ = spMap π ≫ (lev a).left := by
  intro g n hn3 hnodd K _ _ V _ _ _ _ hcV βV π hπ c hcP AV _ _ φ φ₂ PV hAV hφ hsq hPV hr₁ hr₂ hsym hamp hkerV hiso
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  have hnR : IsUnit (n : V) := by simpa using (isUnit_natCast hn0).map βV
  have hnΓ : IsUnit (n : Γ(Sp V, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
    rwa [map_natCast] at this
  have hP : GlobalTheory.TChart.IsPPol AV PV := ⟨⟨hPV, hr₁, hr₂, hsym⟩, hamp, hkerV⟩

  have hζc : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  let ζU : (cycAway n)ˣ := (hζc.isUnit hn0).unit
  let ζR : Vˣ := Units.map βV.toMonoidHom ζU
  have hζR : IsPrimitiveRoot ζR n := IsPrimitiveRoot.coe_units_iff.1 (GlobalTheory.LevSpread.prim_map hn0 βV)

  have hdiag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((PV.pull (lift (𝟙 AV) (𝟙 AV)).left).pull φ) := by
    have ext2 : ∀ {X : Scheme.{0}} (u v : X ⟶ (G2 AV).left), u ≫ (fst AV AV).left = v ≫ (fst AV AV).left →
        u ≫ (snd AV AV).left = v ≫ (snd AV AV).left → u = v := fun u v h1 h2 => Over.tensorObj_ext _ _ h1 h2
    have d1 : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ (fst c.A c.A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
    have d2 : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ (snd c.A c.A).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
    have d1' : (lift (𝟙 AV) (𝟙 AV)).left ≫ (fst AV AV).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
    have d2' : (lift (𝟙 AV) (𝟙 AV)).left ≫ (snd AV AV).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
    have hd : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 AV) (𝟙 AV)).left := by
      apply ext2
      · rw [Category.assoc, hsq.1, ← Category.assoc, d1, Category.id_comp, Category.assoc, d1', Category.comp_id]
      · rw [Category.assoc, hsq.2, ← Category.assoc, d2, Category.id_comp, Category.assoc, d2', Category.comp_id]
    have h3 := GlobalTheory.ThetaAffineGlue.lbIso_pull hiso (lift (𝟙 c.A) (𝟙 c.A)).left
    rw [hd] at h3
    have hΔ := pull_isLB hPV (lift (𝟙 AV) (𝟙 AV)).left
    exact h3.trans (pull_isLB c.isLB _) (pull_isLB hPV _) (pull_isLB hΔ _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull
        (show LBIso (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) from
          LBIso.trans hΔ (pull_isLB hΔ _) hΔ (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ)
            (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ))) φ).symm

  have hL := fun a => GlobalTheory.TorsLiftComplete.existsUnique_torsion_lift V K n hcV hnR π hπ c.A AV φ hAV hφ (c.lev a)
    (c.lev_tors a)
  choose σ hσ using fun a => (hL a).exists
  have hσn : ∀ a, σ a ^ n = 1 := fun a => (hσ a).1
  have hcomp : ∀ a, (c.lev a).left ≫ φ = spMap π ≫ (σ a).left := fun a => (hσ a).2
  let E := GlobalTheory.ObjPull.pushEquiv hφ (𝟙_ (Over (Sp K)))
  let T₁ : Over (Sp V) := Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap π)
  have hσx : ∀ a, toUnit T₁ ≫ σ a = E (c.lev a) := fun a => by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.pushEquiv_left, hcomp]
    exact congrArg (· ≫ (σ a).left) (Category.id_comp _)
  haveI : PreconnectedSpace (𝟙_ (Over (Sp V))).left := inferInstanceAs (PreconnectedSpace (Sp V))
  have inj : ∀ (T : Over (Sp V)) [Nonempty T.left] (s s' : 𝟙_ (Over (Sp V)) ⟶ AV), s ^ n = 1 → s' ^ n = 1 →
      toUnit T ≫ s = toUnit T ≫ s' → s = s' := fun T _ s s' hs hs' h =>
    GlobalTheory.LevSpread.eq_of_comp_eq AV hAV hnΓ (𝟙_ _) s s' hs hs' T (toUnit T) h
  haveI : Nonempty T₁.left := inferInstanceAs (Nonempty (Sp K))
  have hadd : ∀ a a', σ (a + a') = σ a * σ a' := fun a a' =>
    inj T₁ _ _ (hσn _) (by rw [mul_pow, hσn, hσn, _root_.mul_one])
      (by rw [MonObj.comp_mul, hσx, hσx, hσx, c.lev_add, map_mul])
  have one_iff : ∀ (T : Over (Sp V)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ σ a = 1 := fun T _ a =>
    ⟨fun h => inj T (σ a) 1 (hσn a) (one_pow n) (h.trans (MonObj.comp_one _).symm),
      fun h => by rw [h, MonObj.comp_one]⟩

  let iK : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap iK
  obtain ⟨g1, g2, g3⟩ := c.geom (AlgebraicClosure K) x₀ ((iK.comp π).comp βV)
    (Units.map ((iK.comp π).comp βV).toMonoidHom ζU) (by rw [← Spec.map_comp]; rfl) rfl
  let T₀ : Over (Sp V) := Over.mk ((Over.mk x₀).hom ≫ spMap π)
  haveI : Nonempty T₀.left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  have push : ∀ a, GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀) (toUnit _ ≫ c.lev a) = toUnit T₀ ≫ σ a := fun a => by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, hcomp,
      GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.toUnit_left']
    exact (Category.assoc _ _ _).symm
  have hker : ∀ a, σ a = 1 ↔ ∃ b, a = n • b := fun a => by
    rw [← one_iff T₀, ← push, map_eq_one_iff _ (GlobalTheory.ObjPull.pushEquiv hφ _).injective]
    exact g1 a

  haveI : ConnectedSpace (Sp V) := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing V
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim_of_connected AV hAV
  have kerAt : ∀ (T : Over (Sp V)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ ∃ b, a = n • b := fun T _ a => by
    rw [one_iff T]; exact hker a
  have addAt : ∀ (T : Over (Sp V)) a a', toUnit T ≫ σ (a + a') = (toUnit T ≫ σ a) * (toUnit T ≫ σ a') :=
    fun T a a' => by rw [hadd, MonObj.comp_mul]
  have torsAt : ∀ (T : Over (Sp V)) a, (toUnit T ≫ σ a) ^ n = 1 := fun T a => by
    rw [← MonObj.comp_pow, hσn, MonObj.comp_one]
  have surj₀ : ∀ gg : T₀ ⟶ AV, gg ^ n = 1 → ∃ a, toUnit T₀ ≫ σ a = gg := fun gg hg => by
    obtain ⟨a, ha⟩ := g2 ((GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀)).symm gg)
      (by rw [← map_pow, hg, map_one])
    exact ⟨a, by rw [← push, ha, MulEquiv.apply_symm_apply]⟩
  have card₀ := card_eq (fun a => toUnit T₀ ≫ σ a) (addAt T₀) (kerAt T₀) (torsAt T₀) surj₀
  have cardd := GlobalTheory.TorsionCover.card_torsion AV hAV hd ((Over.mk x₀).hom ≫ spMap π)
    (GlobalTheory.TorsionCover.natCast_ne_zero hnΓ ((Over.mk x₀).hom ≫ spMap π))
  have hdg : d = g := by
    have e : n ^ (2 * d) = n ^ (2 * g) := by
      rw [← cardd, show 2 * g = Fintype.card (Fin g ⊕ Fin g) by simp [two_mul]]
      exact card₀
    have := Nat.pow_right_injective (show 2 ≤ n by omega) e
    omega
  subst hdg
  refine ⟨σ, hadd, hσn, fun k _ _ x β z hxβ hz => ?_, hcomp⟩
  obtain ⟨ρ, rfl⟩ : ∃ ρ : V →+* k, spMap ρ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hβ : β = ρ.comp βV := by
    have e : spMap (ρ.comp βV) = spMap β := by rw [← hxβ]; exact Spec.map_comp _ _
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e)).symm
  have hzU : z = Units.map ρ.toMonoidHom ζR := Units.ext (by rw [hz, hβ]; rfl)
  subst hzU
  haveI : Nonempty (Over.mk (spMap ρ)).left := inferInstanceAs (Nonempty (Sp k))
  refine ⟨fun a => kerAt _ a, fun gg hg => ?_, fun a a' => ?_⟩
  · have cardk := GlobalTheory.TorsionCover.card_torsion AV hAV hd (spMap ρ) (GlobalTheory.TorsionCover.natCast_ne_zero hnΓ (spMap ρ))
    exact surj (fun a => toUnit (Over.mk (spMap ρ)) ≫ σ a) (addAt _) (kerAt _) (torsAt _)
      (by rw [cardk]; simp [two_mul]) gg hg
  · have H' := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm (Sp V) (Sp K) AV c.A (spMap π) φ
      (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) (pull_isLB hPV _)
      (pull_isLB c.isLB _) hφ hdiag (Over.mk x₀) (n : ℤ) _ _ (toUnit T₀ ≫ σ a) (toUnit T₀ ≫ σ a') _
      (by rw [← push]; rfl) (by rw [← push]; rfl)).1 (g3 a a')
    have ht : (Over.mk x₀).hom ≫ spMap π = spMap (iK.comp π) := by
      show x₀ ≫ spMap π = _
      rw [← Spec.map_comp]; rfl
    have hu : (Units.map ((iK.comp π).comp βV).toMonoidHom ζU) ^ (2 * omegaStd a a') =
        Units.map (iK.comp π).toMonoidHom (ζR ^ (2 * omegaStd a a')) := by
      rw [map_zpow]; rfl
    rw [hu] at H'
    simp only [T₀] at H'
    rw [ht] at H'
    have H'' := GlobalTheory.LevSpread.l3 V AV hAV PV hP n (by omega) hnR (σ a) (σ a') (hσn a) (hσn a') ζR hζR
      (2 * omegaStd a a') (AlgebraicClosure K) (iK.comp π) H' k ρ
    rw [← map_zpow]
    exact H''

end GlobalTheory.LevLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldLiftsAffineCoverSmoothGroup
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSLift

def twist {R A : Type} [CommRing R] [CommRing A] (ρ : R →+* A) (D : Derivation ℤ R R) : R →+* DualNumber A where
  toFun r := TrivSqZeroExt.inl (ρ r) + TrivSqZeroExt.inr (ρ (D r))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [Derivation.leibniz, smul_eq_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

def epsIdeal (A : Type) [CommRing A] : Ideal (DualNumber A) := RingHom.ker (TrivSqZeroExt.fstHom A A A).toRingHom

theorem mem_epsIdeal {A : Type} [CommRing A] (x : DualNumber A) : x ∈ epsIdeal A ↔ x.fst = 0 := Iff.rfl

theorem isNilpotent_epsIdeal (A : Type) [CommRing A] : IsNilpotent (epsIdeal A) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  rw [mem_epsIdeal] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]

theorem exists_lift {R A : Type} [CommRing R] [CommRing A] (ρ : R →+* A) (hρ : ρ.FormallySmooth)
    (D : Derivation ℤ R R) : ∃ σ : A →+* DualNumber A, (∀ a, (σ a).fst = a) ∧ ∀ r, (σ (ρ r)).snd = ρ (D r) := by
  have hg : ((Ideal.Quotient.mk (epsIdeal A)).comp (algebraMap A (DualNumber A))).comp ρ =
      (Ideal.Quotient.mk (epsIdeal A)).comp (twist ρ D) := by
    ext r
    simp only [RingHom.comp_apply]
    rw [Ideal.Quotient.eq, mem_epsIdeal]
    simp [twist, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨F, hF1, hF2⟩ := GlobalTheory.DI.exists_ringHom_lift_of_formallySmooth ρ hρ (twist ρ D) (epsIdeal A)
    (isNilpotent_epsIdeal A) _ hg
  refine ⟨F, fun a => ?_, fun r => ?_⟩
  · have h := hF1 a
    simp only [RingHom.comp_apply] at h
    rw [Ideal.Quotient.eq, mem_epsIdeal] at h
    simpa [sub_eq_zero, TrivSqZeroExt.algebraMap_eq_inl] using h
  · rw [hF2]; simp [twist]

theorem main (LA : ∀ (A : Type) [CommRing A] (σ : A →+* DualNumber A), (∀ a, (σ a).fst = a) → ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧ ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd) (LB : ∀ (Z : Scheme.{0}) (W : Z.Opens) (hW : IsAffineOpen W) (δ : Γ(Z, W) → Γ(Z, W)) (d' : ∀ O : (Spec Γ(Z, W)).Opens, Γ(Spec Γ(Z, W), O) → Γ(Spec Γ(Z, W), O)), IsField ⊤ d' → (∀ a, d' ⊤ ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom a) = (Scheme.ΓSpecIso Γ(Z, W)).inv.hom (δ a)) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField W d ∧ ∀ a, d W a = δ a) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) := by
  intro E _ _ _ H X t U D
  have key : ∀ (V : t.G.left.affineOpens) (h : V.1 ≤ t.G.hom ⁻¹ᵁ U.1),
      ∃ d : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O), IsField V.1 d ∧
        ∀ r, d V.1 ((t.G.hom.appLE U.1 V.1 h).hom r) = (t.G.hom.appLE U.1 V.1 h).hom (D r) := by
    intro V h
    have hsm : (t.G.hom.appLE U.1 V.1 h).hom.Smooth := t.semi.smooth.smooth_appLE U.2 V.2 h
    obtain ⟨σ, hσ1, hσ2⟩ := exists_lift _ hsm.formallySmooth D
    obtain ⟨d', hd'1, hd'2⟩ := LA _ σ hσ1
    obtain ⟨d, hd1, hd2⟩ := LB t.G.left V.1 V.2 (fun a => (σ a).snd) d' hd'1 hd'2
    exact ⟨d, hd1, fun r => by rw [hd2, hσ2]⟩
  choose dd hdd1 hdd2 using key
  let J := {p : t.G.left.affineOpens × t.PP.L.ι // p.1.1 ≤ t.G.hom ⁻¹ᵁ U.1 ⊓ t.PP.L.U p.2}
  refine ⟨J, fun i => i.1.1.1, fun i => i.1.2, fun i => dd i.1.1 (i.2.trans inf_le_left),
    fun i => i.1.1.2, ?_, fun i => i.2.trans inf_le_right, fun i => hdd1 _ _, fun i h r => hdd2 _ _ r⟩
  refine le_antisymm (iSup_le fun i => i.2.trans inf_le_left) fun x hx => ?_
  have hx' : x ∈ (⨆ k, t.PP.L.U k) := by rw [t.PP.isLB.cover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := t.G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ t.G.hom ⁻¹ᵁ U.1 ⊓ t.PP.L.U k from ⟨hx, hk⟩) (t.G.hom ⁻¹ᵁ U.1 ⊓ t.PP.L.U k).2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, k), hVle⟩, hxV⟩

theorem exists_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) :=
  main GlobalTheory.T.exists_spec_vectorField_of_dualNumber_section GlobalTheory.T.exists_vectorField_affineOpen_transport

end GlobalTheory.KSLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerUniformisedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_veryAmpleAlong_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), ∃ (m : ℕ) (σ : Fin (m + 1) → H0 U.LG.L 4), VeryAmpleAlong ((Over.pullback (jK R)).obj G).hom (pullback.fst G.hom (jK R)) U.LG.L σ := by
  intro R _ _ I D A G _ _ U
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_veryAmple_fourthPower_polarisedAbelian_field GlobalTheory.lawsAndExpansions.1.1.ample _ A
  obtain ⟨σ, c, H⟩ := GlobalTheory.T.exists_integral_sections_uniformisedGroup_power R I D A G U (k := 4) (by norm_num) b
  have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact ⟨m, σ, GlobalTheory.T.veryAmpleAlongPullback_transport_iso _ A.A.hom U.gen.hom.left (Over.w U.gen.hom) _ U.LG.isLB A.isLB b hb σ c H⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorOfLambdaBundleIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilComparisonGenerator_of_lambdaBundleIso : ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∃ u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u.IsGen := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso | exact GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso | (intros; apply GlobalTheory.Mum.Two.WeilCmp.exists_cmpGen_of_lbIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOddMultiplicationPullbackAtTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exp_mulPull_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)), MulFam m F₁ G → MulSecK C m θ₀ S → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  intro R _ _ _ hR D C m hm F₁ G θ₀ S hMF hMS W _ _ _ T a b ha hE
  obtain ⟨σ, ⟨σ', f', hcar, hpull, hexp⟩, hgen⟩ := hE
  obtain ⟨u, hu, hS⟩ := hMS
  obtain ⟨σ₂, hσ₂⟩ := GlobalTheory.T.exists_section_pullback_commuting_endomorphism_generator C.P.L.L C.P.L.isLB T.β (mulA T.G m).left (mulA C.G m).left
    (GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m) 1 (m ^ 2) u hu σ
  have hgen₂ := GlobalTheory.T.multiplicationPullback_trait_genericCondition R D C W T m a u θ₀ S hS σ σ₂ hgen hσ₂
  obtain ⟨G', hG'⟩ := GlobalTheory.Mum.exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc (m ^ 2) G
  obtain ⟨uG, σ'', huG, hσ'', hexp''⟩ := GlobalTheory.T.expansion_multiplicationPullback_trait_degreeOne R hR D C W T m hm F₁ G hMF σ' f' hpull hexp G'.f hG'
  obtain ⟨v, hv⟩ := GlobalTheory.T.multiplicationPullbacks_differ_by_unit R hR D C W T m u hu uG huG b σ' σ hcar σ₂ σ'' hσ₂ hσ''
  exact ⟨v, σ₂, ⟨σ'', G'.f, hv, hG', hexp''⟩, hgen₂⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOriginValuesSumModPowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_originValues_sum_modPow : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (D' : DegData W (maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal W) D' A G) (k e : ℕ) (σ' : H0 U.LG.L k) (f' : ∀ x, D'.toPre.SecB k x) (w : D'.toPre.X → W), (∀ x, OrigVal D'.toPre (f' x) (w x)) → U.ExpandsAt e k σ' f' → ∃ S : Finset D'.toPre.X, (∀ x ∉ S, w x ∈ maximalIdeal W ^ (e + 1)) ∧ ∀ J', Good U.LG.L (cpt W) J' → ∃ c ∈ maximalIdeal W ^ (e + 1), sval σ' (unitW G) (cpt W) J' = stalkOf (cpt W) (∑ x ∈ S, w x + c) * (val U.LG.rig (idW W) (cpt W) J').val ^ k := by
  first | exact @GlobalTheory.Mum.expandsAt_origVal | exact GlobalTheory.Mum.expandsAt_origVal | (intros; apply GlobalTheory.Mum.expandsAt_origVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransportTranslationTwistStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_transport_translation_twist : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A) (xe : D₂.toPre.X ≃+ D.toPre.X) (w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε)) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])) (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0 → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG I e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG I e G).left)) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z (N (r ≫ (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG I e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → ∀ (σ : H0 U.LG.L 1) (σ₂ : H0 U₂.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → U.ExpandsAt e 1 σ f → U₂.ExpandsAt e 1 σ₂ f₂ := by
  first | exact @GlobalTheory.TwistedExpTransport.expandsAt_twist | exact GlobalTheory.TwistedExpTransport.expandsAt_twist | (intros; apply GlobalTheory.TwistedExpTransport.expandsAt_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsAtOfCodimLeOneOverCompleteDVRsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendsAt_of_codim_le_one_over_completeDVRs : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (W : (Over.mk χ ⊗ G).left.Opens) (f : Γ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left, ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ s : Γ((Over.mk (spMap φ ≫ χ) ⊗ G).left, ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W), ∀ (O : (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⊗ G).left.Opens) (h₁ : O ≤ ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)) (h₂ : O ≤ ((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left.appLE _ O h₁).hom s = (((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left.appLE _ O h₂).hom f) → ∀ y ∈ W, Order.coheight y ≤ 1 → y ∉ Set.range ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left → GlobalTheory.GenericExtend.ExtAt ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left W f y := by
  first | exact @GlobalTheory.CodimOneExtend.extAt_of_coheight_le_one | exact GlobalTheory.CodimOneExtend.extAt_of_coheight_le_one | (intros; apply GlobalTheory.CodimOneExtend.extAt_of_coheight_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPeriodsProjectionPeriodPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

theorem GlobalTheory.Mum.Two.Fac.pt_ext (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (a b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (h : toUnit (TF (R := R) F) ≫ a = toUnit (TF (R := R) F) ≫ b) : a = b := by
  have : IsDominant (jK R) := isDominant_jK
  have : Surjective (jFK (R := R) F) := GlobalTheory.Balanced.surjective_spMap (algebraMap (FractionRing R) F)
  have : IsDominant (jFK (R := R) F) := inferInstance
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have e := congrArg (fun m => m.left) h
  simp only [Over.comp_left] at e
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) D.P.A.hom
    ((Over.w a).trans (Over.w b).symm) (jFK (R := R) F ≫ jK R) ?_)
  simpa using e

open GlobalTheory.Mum.Two.Fac in

theorem GlobalTheory.Mum.Two.Fac.periods_of_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R), D'.TauBimult → ∀ (O : Type) [Ring O] [StarRing O] [Module O D'.X] (o : D'.OAct O) (e f : O) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (φ : D'.X →+ D₀.X), IsMonHom inc → IsMonHom pr → pr ≫ inc = o.onB.act e → (∀ χ, ∃ u : LB.Gen (CmpLB D' D₀ pr (h χ) χ), Nrm u) → LBIso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ (y : D'.X) (g : GtPtF D' F), GtPtF.IsIota y g → ∃ g' : GtPtF D₀ F, Act D' D₀ pr h g g' ∧ GtPtF.IsIota (φ y) g') → (∀ y, h (φ y) = star e • f • e • y) → (∀ y, D₀.c (φ y) = D'.c y ≫ pr) ∧ ∃ w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left), w.IsGen ∧ ∀ y y' z J J', Good D'.P.L z J → Good D₀.P.L z J' → val (D₀.tau (φ y) (φ y')) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D₀.c (φ y)) (toUnit (TK R) ≫ D₀.c (φ y'))).left z J J' * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J := by
  intro R _ _ D₀ D' hB O _ _ _ o e f inc pr h φ hinc hpr hpi hu hw F _ _ hiota hh
  have hG := GlobalTheory.globalFns_holds
  have hc : ∀ y, D₀.c (φ y) = D'.c y ≫ pr := by
    intro y
    obtain ⟨g', ha, hg'⟩ := hiota y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have h1 := ha.1
    rw [hg'.1, (GlobalTheory.TorusExt.isIota_iota hB y).1] at h1
    refine pt_ext R D₀ F _ _ ?_
    simpa only [Category.assoc] using h1
  refine ⟨hc, ?_⟩
  haveI := hinc
  haveI := hpr
  haveI : IsMonHom (o.onB.act f) := o.onB.hom f
  haveI : IsMonHom (o.onB.act e) := o.onB.hom e
  haveI : IsMonHom (o.onB.act (star e)) := o.onB.hom (star e)
  obtain ⟨w, hwg, hwn⟩ := GlobalTheory.T.exists_mumfordBundleIso_twoHom_normalisedAtOrigin D₀.P.A D'.P.A D₀.P.L D'.P.L D₀.P.isLB D'.P.isLB inc (inc ≫ o.onB.act f) hw
  have hw1 := GlobalTheory.T.mumfordBundleIso_value_one_zero_first_factor D₀.P.A D'.P.A D₀.P.L D'.P.L D₀.P.isLB D'.P.isLB D₀.P.isAb inc (inc ≫ o.onB.act f)
    w hwg hwn
  refine ⟨w, hwg, fun y y' z J J' hJ hJ' => ?_⟩
  obtain ⟨ur, hur, hur0⟩ := exists_ros hG D'.P.isAb D'.P.isLB (o.onB.act e) (o.onB.act (star e)) (o.onB.rosati e)
  have hur1 := GlobalTheory.T.rosatiGenerator_value_one_zero_first_factor D'.P.A D'.P.L D'.P.isLB D'.P.isAb _ _ ur hur hur0
  obtain ⟨JN₀, hJN, hl, hr⟩ := exists_good_join D'.P.isLB D₀.P.isLB hJ hJ'
  obtain ⟨u, hun⟩ := hu (φ y')
  obtain ⟨g', ha, hg'⟩ := hiota y _ (GlobalTheory.TorusExt.isIota_iota hB y)
  have A := GlobalTheory.T.torusExtensionPointAction_period_value_fractionField R D₀ D' pr h F y (φ y) _ g' (GlobalTheory.TorusExt.isIota_iota hB y) hg' ha (φ y') u hun z JN₀ hJN
  rw [hl, hr] at A
  have B := val_corr hJ (o.tau_bal e ur hur hur0 y (f • e • y')) (𝟙 _)
  beta_reduce at B
  rw [val_mul hJ, val_pull hJ, Category.id_comp, ← hh y'] at B
  have hq : D₀.c (φ y') ≫ inc ≫ o.onB.act f = D'.c (f • e • y') := by
    rw [hc, o.c_lin, o.c_lin, ← hpi]; simp only [Category.assoc]
  have hq' : D'.c (h (φ y')) = D'.c (f • e • y') ≫ o.onB.act (star e) := by
    rw [hh y', o.c_lin]
  have C := GlobalTheory.T.mumfordIso_eq_rosatiGenerator_mul_comparison R D₀ D' inc pr (o.onB.act e) (o.onB.act f) (o.onB.act (star e)) hpi w hwg hw1 ur hur hur1
    (h (φ y')) (φ y') (D'.c (f • e • y')) hq hq' u hun (TK R) (toUnit (TK R) ≫ D'.c y) z JN₀ hJN
  rw [hl, hr, Category.assoc, ← hc] at C
  rw [A, ← B, C]
  show _ = _ * _ * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J
  rw [mul_comm (val ur _ z J)]
  ac_rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstOfSpecialisationInvariantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_const_of_specialisation_invariant : ∀ (Y Z : Type) [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z), Continuous q → ∀ z : Z, _root_.IsPreconnected (q ⁻¹' {z}) → ∀ P : Y → Prop, (∀ a b, q a = z → q b = z → a ⤳ b → (P a ↔ P b)) → ∀ a b, q a = z → q b = z → P a → P b := by
  first | exact @GlobalTheory.fibre_const_of_specializes_invariant | exact GlobalTheory.fibre_const_of_specializes_invariant | (intros; apply GlobalTheory.fibre_const_of_specializes_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsOverFieldIrreducibleJoinStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flags_over_field_irreducible_join : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (M : ι → (Spec (CommRingCat.of L)).Modules) (r : ι → ℕ), (∀ a, VB.IsVB (M a) (r a)) → ∀ φ : ∀ a, M a ≅ M a, ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (h₁ : t₁ ≫ c = 𝟙 _) (h₂ : t₂ ≫ c = 𝟙 _) (Φ : ∀ a, (Scheme.Modules.pullback c).obj (M a) ≅ (Scheme.Modules.pullback c).obj (M a)), IrreducibleSpace T ∧ (∀ a, (Scheme.Modules.pullback t₁).map (Φ a).hom = 𝟙 _) ∧ ∀ a, (Scheme.Modules.pullback t₂).map (Φ a).hom ≫ (Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a) = ((Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a)) ≫ (φ a).hom := by
  first | exact @GlobalTheory.FlagPath.exists_path_auto | exact GlobalTheory.FlagPath.exists_path_auto | (intros; apply GlobalTheory.FlagPath.exists_path_auto <;> assumption)
end

