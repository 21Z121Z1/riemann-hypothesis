import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRepUniversal
section
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem lbIso_pullPull {P X Y : Scheme.{0}} {M : LB P} (hM : M.IsLB) (b : X ⟶ P) (c : Y ⟶ X) :
    LBIso ((M.pull b).pull c) (M.pull (c ≫ b)) :=
  LBIso.chartPull (chartPullLinComb M b (fun _ : PUnit => c) (fun _ => c ≫ b) (fun _ => 1) (𝟙 _)
      fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hM _))

theorem lbIso_pullAlong {X Y : Scheme.{0}} {P Q : LB X} (H : LBIso P Q) (h : Y ⟶ X) :
    LBIso (P.pull h) (Q.pull h) :=
  LBIso.chartPull (chartPullPull P h h rfl) (chartPullPull Q h h rfl) H

theorem Pt.f_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z : Scheme.{0}} {x x' : Pt A B L M Z} (h : x = x') (e : x.t = x'.t) :
    pullback.lift (pullback.fst A.hom x'.t) (pullback.snd A.hom x'.t) (by rw [pullback.condition, e]) ≫ x.f = x'.f := by
  subst h
  rw [pullback.lift_fst_snd, Category.id_comp]

section
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
  {V : Scheme.{0}} {j : V ⟶ S} {A' B' : Over V} [GrpObj A'] [GrpObj B'] {φA : A'.left ⟶ A.left}
  {φB : B'.left ⟶ B.left}

theorem univ_iso (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)) :
    LBIso (L.pull (R.φA ≫ φA)) ((M.pull (R.φB ≫ φB)).pull R.Φ.left) :=
  LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _)
    (lbIso_pullPull hL φA R.φA).symm
    (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
      (pull_isLB (pull_isLB hM _) _) R.iso (lbIso_pullAlong (lbIso_pullPull hM φB R.φB) R.Φ.left))

def univPt (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB))
    (hA : IsGrpPullback A' A j φA) (hB : IsGrpPullback B' B j φB) : Pt A B L M R.H :=
  Pt.ofData (R.π ≫ j) R.AH R.BH (R.φA ≫ φA) (R.φB ≫ φB) R.Φ (R.pbA.comp hA) (R.pbB.comp hB) R.hom
    (univ_iso hL hM R)

theorem univPt_key (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB))
    (hA : IsGrpPullback A' A j φA) (hB : IsGrpPullback B' B j φB) {Z P : Scheme.{0}} (c : Z ⟶ R.H) (t : Z ⟶ V)
    (e : P ⟶ pullback A.hom (t ≫ j)) (ψ : P ⟶ R.AH.left)
    (h1 : ψ ≫ R.φA ≫ φA = e ≫ pullback.fst _ _) (h2 : ψ ≫ R.AH.hom = e ≫ pullback.snd _ _ ≫ c)
    (w : pullback.fst A.hom (t ≫ j) ≫ A.hom = pullback.snd A.hom (t ≫ j) ≫ c ≫ R.π ≫ j) :
    e ≫ pullback.lift (pullback.fst _ _) (pullback.snd _ _) w ≫ pmap A (R.π ≫ j) c ≫ (univPt hL hM R hA hB).f =
      ψ ≫ R.Φ.left ≫ R.φB ≫ φB := by
  have hk : e ≫ pullback.lift (pullback.fst _ _) (pullback.snd _ _) w ≫ pmap A (R.π ≫ j) c =
      ψ ≫ (R.pbA.comp hA).1.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pmap, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      exact h1.symm
    · simp only [pmap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_snd]
      exact h2.symm
  have e0 : (univPt hL hM R hA hB).f = (R.pbA.comp hA).1.isoPullback.inv ≫ R.Φ.left ≫ R.φB ≫ φB := rfl
  have := congrArg (· ≫ ((R.pbA.comp hA).1.isoPullback.inv ≫ R.Φ.left ≫ R.φB ≫ φB)) hk
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at this
  rw [e0]
  exact this

end
end GlobalTheory.EndLoc.HomGlue

namespace GlobalTheory.EndLoc.HomGlue

theorem localRep_universal : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)
    (hL : L.IsLB) (hM : M.IsLB) (V : Scheme.{0}) (j : V ⟶ S) [IsOpenImmersion j] (A' B' : Over V) [GrpObj A']
    [GrpObj B'] (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)),
    IsGrpPullback A' A j φA → IsGrpPullback B' B j φB → ∃ y : HomGlue.Pt A B L M R.H, y.t = R.π ≫ j ∧
      ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V), x.t = b ≫ j → ∃! c : Z ⟶ R.H, y.map hL hM c = x := by
  intro S A B _ _ L M hL hM V j _ A' B' _ _ φA φB R hA hB
  refine ⟨univPt hL hM R hA hB, rfl, ?_⟩
  rintro Z ⟨t, f, w⟩ b hx
  dsimp only at hx
  subst hx
  have w₀ := w
  obtain ⟨A'', B'', _, _, φ'', ψ'', Φ'', hA'', hB'', hΦ'', hI'', e, e1, e2, e3⟩ := w₀
  let φ'A : A''.left ⟶ A'.left := hA.1.lift φ'' (A''.hom ≫ b) (by rw [hA''.1.w, Category.assoc])
  have fA : φ'A ≫ φA = φ'' := hA.1.lift_fst _ _ _
  have sA : φ'A ≫ A'.hom = A''.hom ≫ b := hA.1.lift_snd _ _ _
  have pA : IsGrpPullback A'' A' b φ'A := hA.cancel (hA''.congr rfl fA.symm) sA
  let φ'B : B''.left ⟶ B'.left := hB.1.lift ψ'' (B''.hom ≫ b) (by rw [hB''.1.w, Category.assoc])
  have fB : φ'B ≫ φB = ψ'' := hB.1.lift_fst _ _ _
  have sB : φ'B ≫ B'.hom = B''.hom ≫ b := hB.1.lift_snd _ _ _
  have pB : IsGrpPullback B'' B' b φ'B := hB.cancel (hB''.congr rfl fB.symm) sB
  have iso' : LBIso ((L.pull φA).pull φ'A) (((M.pull φB).pull φ'B).pull Φ''.left) := by
    have h1 := lbIso_pullPull hL φA φ'A
    rw [fA] at h1
    have h2 := (lbIso_pullAlong (lbIso_pullPull hM φB φ'B) Φ''.left).symm
    rw [fB] at h2
    exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _) h1
      (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _) hI'' h2)
  obtain ⟨h, ⟨hh, ψA, ψB, qA, qB, gA, gB, qΦ⟩, huniq⟩ := R.rep Z b A'' B'' φ'A φ'B Φ'' pA pB hΦ'' iso'
  have he : e = hA''.1.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [e1, IsPullback.isoPullback_hom_fst]
    · rw [e2, IsPullback.isoPullback_hom_snd]
  have hΦw : Φ''.left ≫ B''.hom = A''.hom := Over.w Φ''
  refine ⟨h, ?_, ?_⟩
  · refine Pt.ext' (show h ≫ R.π ≫ j = b ≫ j by rw [← Category.assoc, hh]) ?_
    have : IsIso e := by rw [he]; infer_instance
    rw [← cancel_epi e, e3]
    refine (univPt_key hL hM R hA hB h b e ψA (by rw [← Category.assoc, gA, fA, e1])
      (by rw [qA.1.w, ← Category.assoc, e2]) _).trans ?_
    rw [← Category.assoc ψA, ← qΦ, Category.assoc, ← Category.assoc ψB, gB, fB]
  · intro c hc
    have ht : c ≫ R.π ≫ j = b ≫ j := congrArg Pt.t hc
    have hcb : c ≫ R.π = b := (cancel_mono j).1 (by rw [Category.assoc]; exact ht)
    have hf := Pt.f_eq hc ht
    let ψA' : A''.left ⟶ R.AH.left := R.pbA.1.lift φ'A (A''.hom ≫ c) (by rw [sA, ← hcb, Category.assoc])
    have kA : ψA' ≫ R.φA = φ'A := R.pbA.1.lift_fst _ _ _
    have kA2 : ψA' ≫ R.AH.hom = A''.hom ≫ c := R.pbA.1.lift_snd _ _ _
    let ψB' : B''.left ⟶ R.BH.left := R.pbB.1.lift φ'B (B''.hom ≫ c) (by rw [sB, ← hcb, Category.assoc])
    have kB : ψB' ≫ R.φB = φ'B := R.pbB.1.lift_fst _ _ _
    have kB2 : ψB' ≫ R.BH.hom = B''.hom ≫ c := R.pbB.1.lift_snd _ _ _
    have key := univPt_key hL hM R hA hB c b e ψA' (by rw [← Category.assoc, kA, fA, e1])
      (by rw [kA2, ← Category.assoc, e2]) (by rw [pullback.condition, ← ht])
    have hΦA : R.Φ.left ≫ R.BH.hom = R.AH.hom := Over.w R.Φ
    apply huniq
    refine ⟨hcb, ψA', ψB', R.pbA.cancel (pA.congr hcb.symm kA.symm) kA2,
      R.pbB.cancel (pB.congr hcb.symm kB.symm) kB2, kA, kB, ?_⟩
    apply R.pbB.1.hom_ext
    · rw [Category.assoc, kB]
      apply hB.1.hom_ext
      · rw [Category.assoc, fB, ← e3, Category.assoc, Category.assoc, ← key]
        exact congrArg (e ≫ ·) hf.symm
      · rw [Category.assoc, sB, ← Category.assoc, hΦw, Category.assoc, Category.assoc, R.pbB.1.w,
          ← Category.assoc R.Φ.left, hΦA, ← Category.assoc, kA2, Category.assoc, hcb]
    · rw [Category.assoc, kB2, ← Category.assoc, hΦw, Category.assoc, hΦA, kA2]

end GlobalTheory.EndLoc.HomGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLeStatement
section
open Formalism.BasicNotions

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_branching_constant_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B → (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) → Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  first | exact @GlobalTheory.BranchBound.log_brBd_sq_le | exact GlobalTheory.BranchBound.log_brBd_sq_le | (intros; apply GlobalTheory.BranchBound.log_brBd_sq_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmIntegersAdaptedBasisNoLieComponents
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.RedO

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → (∀ j, c.IsLie (e0 (Sum.inr j)) (lb j)) → ∀ h : MvPowerSeries (Fin d) C, QL c.μ ⊤ h → cob1 (up C c.μ) h = 0 → ∀ a : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (h - comb a e0) → (∀ j, a (Sum.inr j) = 0) ∧ ∀ i, lin h i = algebraMap O C (a (Sum.inl i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c k e0 lb hB hA hL h hh hcob a ha
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hμ : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, c.isLaw.const i]

  have lie0 : ∀ f : MvPowerSeries (Fin d) C, cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
    intro f hf
    have hd : ∀ n : ℕ, defect c.μ (p ^ n) f = defect c.μ (p ^ n) (0 : MvPowerSeries (Fin d) C) := fun n => by
      rw [defect, GlobalTheory.LieZero.subst_nmul_of_cob1_eq_zero c.μ c.isLaw.const f hf, sub_self, defect,
        ← coe_substAlgHom (hasSubst_up_nmul c.isLaw.const _), map_zero, smul_zero, sub_zero]
    have e : c.IsLie f 0 ↔ c.IsLie (0 : MvPowerSeries (Fin d) C) 0 := by
      unfold Chart.IsLie
      simp only [hd]
    exact e.2 (c.isLie_zero hv.hom_inj)

  have hcobE : ∀ i, cob1 (up C c.μ) (e0 (Sum.inl i)) = 0 := fun i => by
    ext α
    obtain ⟨b, hb, hb'⟩ := (hA i).1 α
    rw [RingHom.mem_ker, RingHom.id_apply] at hb
    rw [hb', hb, map_zero, map_zero]
  let L : Fin d ⊕ Fin k → G.dual.Lie := Sum.elim (fun _ => 0) lb
  have hLe : ∀ x, c.IsLie (e0 x) (L x) := by
    rintro (i | j)
    · exact lie0 _ (hcobE i)
    · exact hL j

  let e' : Unit ⊕ (Fin d ⊕ Fin k) → MvPowerSeries (Fin d) C := Sum.elim (fun _ => h) e0
  let b' : Unit ⊕ (Fin d ⊕ Fin k) → O := Sum.elim (fun _ => 1) (-a)
  have hcomb : comb b' e' = h - comb a e0 := by
    simp only [comb, Fintype.sum_sum_type, e', b', Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
      map_neg, neg_smul, Finset.sum_neg_distrib, map_one, one_smul, Finset.univ_unique,
      Finset.sum_singleton]
    abel
  have hQL : ∀ x, QL c.μ ⊤ (e' x) := by
    rintro (_ | x)
    · exact hh
    · exact hB.1 x
  have hLie' : ∀ x, c.IsLie (e' x) (Sum.elim (fun _ => (0 : G.dual.Lie)) L x) := by
    rintro (_ | x)
    · exact lie0 h hcob
    · exact hLe x
  have hs := GlobalTheory.QLog.Chart.isLie_comb p O C hF G d c _ e' _ b' hQL hLie'
  rw [hcomb] at hs
  have hc0 : constantCoeff (h - comb a e0) = 0 := by
    rw [map_sub, hh.1, comb, map_sum]
    simp [← coeff_zero_eq_constantCoeff_apply, coeff_smul,
      coeff_zero_eq_constantCoeff_apply, (hB.1 _).1]
  have hl0 := (GlobalTheory.LieZero.lie_eq_zero p O C hF G d c _ _ hs).1 ha hc0
  simp only [Fintype.sum_sum_type, b', Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero,
    zero_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, neg_eq_zero, L] at hl0
  have hinr : ∀ j, a (Sum.inr j) = 0 :=
    Fintype.linearIndependent_iff.1 lb.linearIndependent (fun j => a (Sum.inr j)) hl0
  refine ⟨hinr, fun i => ?_⟩

  have hcobc : cob1 (up C c.μ) (h - comb a e0) = 0 := by
    have hadd : ∀ f g, cob1 (up C c.μ) (f + g) = cob1 (up C c.μ) f + cob1 (up C c.μ) g :=
      formalCoboundary_add hμ
    let Φ : MvPowerSeries (Fin d) C →+ MvPowerSeries (Fin d ⊕ Fin d) C :=
      AddMonoidHom.mk' (cob1 (up C c.μ)) hadd
    have e1 : cob1 (up C c.μ) (comb a e0) = 0 := by
      change Φ (comb a e0) = 0
      rw [comb, map_sum]
      refine Finset.sum_eq_zero fun x _ => ?_
      change cob1 (up C c.μ) (algebraMap O C (a x) • e0 x) = 0
      rw [formalCoboundary_smul hμ]
      rcases x with i' | j
      · rw [hcobE i', smul_zero]
      · rw [hinr j, map_zero, zero_smul]
    rw [sub_eq_add_neg, ← neg_one_smul C (comb a e0), hadd, formalCoboundary_smul hμ, e1, smul_zero, hcob,
      add_zero]
  obtain ⟨s, hs'⟩ := In.top_iff.1 ha
  have hs0 : s = 0 :=
    GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero p C v O hv G d c C hF s (by rw [hs']; exact hcobc)
  rw [hs0, map_zero] at hs'
  have hEq : h = comb a e0 := sub_eq_zero.1 hs'.symm
  rw [hEq]
  simp only [lin, comb, Fintype.sum_sum_type, map_add, map_sum, coeff_smul, smul_eq_mul]
  have h2 : ∀ j, algebraMap O C (a (Sum.inr j)) * coeff (Finsupp.single i 1) (e0 (Sum.inr j)) = 0 :=
    fun j => by rw [hinr j, map_zero, zero_mul]
  have h1 : ∀ i', coeff (Finsupp.single i 1) (e0 (Sum.inl i')) = (Pi.single i' (1 : C) : Fin d → C) i :=
    fun i' => congrFun (hA i').2 i
  simp only [h2, h1, Finset.sum_const_zero, add_zero, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.QLog.RedO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
section
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.LeviOnly

theorem levi_polar {D : ℕ} {f : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f z) (a b : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ f) z a b + fderiv ℝ (fderiv ℝ f) z (Complex.I • a) (Complex.I • b) =
      2 * (levi f z (a + b) - levi f z a - levi f z b) := by
  have hs : IsSymmSndFDerivAt ℝ f z := hf.isSymmSndFDerivAt (by simp)
  unfold levi
  simp only [smul_add, map_add, ContinuousLinearMap.add_apply]
  rw [hs b a, hs (Complex.I • b) (Complex.I • a)]
  ring

theorem hessC_eq_of_levi {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (h : ∀ w, levi f z w = levi g z w) : hessC f z = hessC g z := by
  have key : ∀ a b : Fin D → ℂ,
      fderiv ℝ (fderiv ℝ f) z a b + fderiv ℝ (fderiv ℝ f) z (Complex.I • a) (Complex.I • b) =
      fderiv ℝ (fderiv ℝ g) z a b + fderiv ℝ (fderiv ℝ g) z (Complex.I • a) (Complex.I • b) := by
    intro a b
    rw [levi_polar hf, levi_polar hg, h, h, h]
  have key2 : ∀ a b : Fin D → ℂ,
      fderiv ℝ (fderiv ℝ f) z a (Complex.I • b) - fderiv ℝ (fderiv ℝ f) z (Complex.I • a) b =
      fderiv ℝ (fderiv ℝ g) z a (Complex.I • b) - fderiv ℝ (fderiv ℝ g) z (Complex.I • a) b := by
    intro a b
    have h1 := key a (Complex.I • b)
    have h2 : Complex.I • Complex.I • b = -b := by rw [smul_smul, Complex.I_mul_I]; simp
    rw [h2, map_neg, map_neg] at h1
    linarith
  funext i j
  simp only [hessC]
  rw [key, key2]

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem pot_two {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y := by
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  exact ((hP.1 x j).contDiffAt (ho.mem_nhds ⟨hy, hx⟩)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))

theorem levi_base {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) (w : Fin e → ℂ) :
    levi (P.φ x ∘ (A.chart j).symm) y w = leviAt A P j y w := by
  obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hP.2 x ((A.chart j).symm y) ((A.chart j).symm y) ⟨hx, P.mem_U _⟩
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hyW⟩
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ P.U x ∩ P.U ((A.chart j).symm y))) :=
    (A.chart j).isOpen_inter_preimage_symm ((hW.inter (P.isOpen_U x)).inter (P.isOpen_U _))
  have hev : (P.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun v =>
      (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) v + 1 * ((G ∘ (A.chart j).symm) v).re := by
    filter_upwards [ho.mem_nhds ⟨hy, ⟨hyW, hx⟩, P.mem_U _⟩] with v hv
    have := hGe _ hv.2
    simp only [Function.comp_apply]
    linarith
  have hRe : ContDiffAt ℝ 2 (fun v => ((G ∘ (A.chart j).symm) v).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 (pot_two hP _ j hy (P.mem_U _)) hRe, levi_re_analytic hGa]
  simp [leviAt]

theorem isPsh_of_leviEq {P Q : LocPot X} (hQ : IsPotential A Q)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A P j y w = leviAt A Q j y w) (hp : IsPsh A P) : IsPsh A Q := by
  intro x j y hy w
  rw [levi_base hQ x j hy.1 hy.2, ← h j y hy.1 w]
  exact hp _ j y ⟨hy.1, P.mem_U _⟩ w

theorem locDens_eq {P Q : Fin e → LocPot X} (hP : ∀ i, IsPotential A (P i)) (hQ : ∀ i, IsPotential A (Q i))
    (h : ∀ i, LeviEq A (P i) (Q i)) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    locDens A P j y = locDens A Q j y := by
  have hH : (fun k => hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) =
      fun k => hessC (fun y' => (Q k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    funext k
    exact hessC_eq_of_levi (pot_two (hP k) _ j hy ((P k).mem_U _)) (pot_two (hQ k) _ j hy ((Q k).mem_U _))
      (h k j y hy)
  unfold locDens maDens
  rw [hH]

theorem mInt_eq_of_leviEq : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (P Q : Fin e → LocPot X) (g : X → ℝ), (∀ i, IsPotential A (P i)) → (∀ i, IsPotential A (Q i)) → (∀ i, LeviEq A (P i) (Q i)) → mInt A P g = mInt A Q g ∧ ∀ i, (IsPsh A (P i) ↔ IsPsh A (Q i)) := by
  intro e X _ _ _ A P Q g hP hQ h
  refine ⟨?_, fun i => ⟨isPsh_of_leviEq (hQ i) (h i),
    isPsh_of_leviEq (hP i) (fun j y hy w => (h i j y hy w).symm)⟩⟩
  unfold mInt
  split_ifs with hn
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [locDens_eq hP hQ h j hy]
  · rfl

end GlobalTheory.LeviOnly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitOpUpperBlockLeviEqZeroStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixUnitOp_upperBlock_levi_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) (f : Sm E a), (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a), (i : ℕ) < r → r ≤ (j : ℕ) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  first | exact @GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero | exact GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero | (intros; apply GlobalTheory.LeviGA.Eop_upper_blkGL_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfDuplicationEqStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_duplication_eq_weierstrass : ∀ (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) (x y δ : ℂ), IntV V W → W.toAffine.Equation x y → 2 * y + W.a₁ * x + W.a₃ ∈ V → δ ∈ V → x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ = (2 * y + W.a₁ * x + W.a₃) ^ 2 * (x + δ) → x ∈ V ∧ y ∈ V := by
  first | exact @GlobalTheory.CMModel.mem_of_duplication_eq | exact GlobalTheory.CMModel.mem_of_duplication_eq | (intros; apply GlobalTheory.CMModel.mem_of_duplication_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAtShortOfSixUnitStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelAt_short_of_valuation_six_eq_one : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ j u D : ℂ), j ∈ V → j * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ = (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).c₄ ^ 3 → V.valuation (6 : ℂ) = 1 → u ∈ F → u ≠ 0 → D ∈ V → V.valuation u ^ 12 * V.valuation D = V.valuation (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D := by
  first | exact @GlobalTheory.CMModel.modelAt_short_of_six_unit | exact GlobalTheory.CMModel.modelAt_short_of_six_unit | (intros; apply GlobalTheory.CMModel.modelAt_short_of_six_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAtShortTwistFourMulAddOneStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ D : ℂ) (k : ℤ), a₄ ∈ F → a₆ ∈ F → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D → ModelAt V F (shortTwist (4 * (k : ℂ) + 1) a₄ a₆) ((4 * (k : ℂ) + 1) ^ 6 * D) := by
  first | exact @GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one | exact GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one | (intros; apply GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityLinearCharacterEqCharacterSum
section
open Formalism.L2.DIV NumberField Module

noncomputable section

namespace GlobalTheory.multiplicity_linearCharacter_eq_characterSum

theorem nOf_eq_charSum : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G) [Fintype H] (ψ : H →* Kˣ), (Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨H, ψ⟩ : K) = (Nat.card H : K)⁻¹ * ∑ h : H, Formalism.IndefR.TransferLatticeStatement.charOf τ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  intro K _ _ G _ _ W _ _ _ τ H _ ψ
  classical
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  set T : Module.End K W := ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) with hT
  have hep : Formalism.IndefR.IndefiniteEpsilonOperator.epOp τ ⟨H, ψ⟩ = (Nat.card H : K)⁻¹ • T := by
    unfold Formalism.IndefR.IndefiniteEpsilonOperator.epOp
    congr 1
    rw [hT]
    simp only [map_inv]
    congr!
  have h1 : ∀ a : H, ((((ψ a)⁻¹ : Kˣ) : K) • τ (a : G)) * T = T := by
    intro a
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => ?_
    simp [smul_smul, mul_comm]
  have h2 : T * T = (Nat.card H : K) • T := by
    conv_lhs => rw [hT, Finset.sum_mul, ← hT]
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  have hid : IsIdempotentElem (Formalism.IndefR.IndefiniteEpsilonOperator.epOp τ ⟨H, ψ⟩) := by
    rw [IsIdempotentElem, hep, smul_mul_smul_comm, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp
  rw [← htr, hep, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory.multiplicity_linearCharacter_eq_characterSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresModPrimeMulPermUpToSignStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzeroSquaresModPrime_mul_perm_up_to_sign : ∀ (p c : ℕ), p.Prime → p % 4 = 3 → ¬ p ∣ c → ∃ (e : Sq p ≃ Sq p) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ ∀ k : Sq p, (p : ℤ) ∣ (((k.1 : ℕ) : ℤ) * c - ε * (((e k).1 : ℕ) : ℤ)) := by
  first | exact @GlobalTheory.CMModel.sq_perm_mul | exact GlobalTheory.CMModel.sq_perm_mul | (intros; apply GlobalTheory.CMModel.sq_perm_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresSumEquivIcoModFourStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four : ∀ (p : ℕ), p.Prime → p % 4 = 3 → ∃ e : Sq p ⊕ Sq p ≃ (Finset.Ico 1 p : Finset ℕ), ∀ k : Sq p, ((e (Sum.inl k) : ℕ) = (k.1 : ℕ)) ∧ ((e (Sum.inr k) : ℕ) = p - (k.1 : ℕ)) := by
  first | exact @GlobalTheory.sq_sum_equiv_Ico | exact GlobalTheory.sq_sum_equiv_Ico | (intros; apply GlobalTheory.sq_sum_equiv_Ico <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedIsoPowerBundleRatioUnitEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_isoPowerBundle_ratio_unit_eq_one : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), IsAbelianScheme A → L.IsLB → M.IsLB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (α α₂ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) (v : Γ(A'.left, ⊤)ˣ), IsTest A B L M t A' B' φA' φB' Φ' → ψA ≫ (snd (topS Rg) A).left = φA' → ψB ≫ (snd (topS Rg) B).left = φB' → (∀ p, α.s p = res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v * α₂.s p) → RigEq L M k eA eB t Φ' ψA ψB α → RigEq L M k eA eB t Φ' ψA ψB α₂ → v = 1 := by
  first | (exact @GlobalTheory.HomFixUnit.ratio_unit_eq_one) | (exact GlobalTheory.HomFixUnit.ratio_unit_eq_one) | (intros; apply GlobalTheory.HomFixUnit.ratio_unit_eq_one  <;> assumption)
end

