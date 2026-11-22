import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0006
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
section
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem lbIso_pull {P Q Xa Xb Xa' Xb' : Scheme.{0}} {L : LB P} {M : LB Q} (hL : L.IsLB) (hM : M.IsLB)
    {a : Xa ⟶ P} {b : Xb ⟶ Q} {c : Xa ⟶ Xb} {a' : Xa' ⟶ P} {b' : Xb' ⟶ Q} {c' : Xa' ⟶ Xb'} (e : Xa' ⟶ Xa)
    (ha : a' = e ≫ a) (hc : c' ≫ b' = e ≫ c ≫ b) (H : LBIso (L.pull a) ((M.pull b).pull c)) :
    LBIso (L.pull a') ((M.pull b').pull c') := by
  have h1 : LBIso ((M.pull b).pull c) (M.pull (c ≫ b)) :=
    LBIso.chartPull (chartPullLinComb M b (fun _ : PUnit => c) (fun _ => c ≫ b) (fun _ => 1) (𝟙 _)
      fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hM _))
  have h2 : LBIso (L.pull a) (M.pull (c ≫ b)) :=
    LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) H h1
  exact LBIso.chartPull (chartPullSame L (fun _ : PUnit => a') (fun _ => a) (fun _ => 1) e fun _ => ha)
    (chartPullLinComb M b' (fun _ : PUnit => c') (fun _ => c ≫ b) (fun _ => 1) e fun _ => hc) h2

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)

def Wit {Z : Scheme.{0}} (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left) : Prop :=
  ∃ (A' B' : Over Z) (_ : GrpObj A') (_ : GrpObj B') (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (Φ : A' ⟶ B'),
    IsGrpPullback A' A t φA ∧ IsGrpPullback B' B t φB ∧ IsMonHom Φ ∧ LBIso (L.pull φA) ((M.pull φB).pull Φ.left) ∧
    ∃ e : A'.left ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = φA ∧ e ≫ pullback.snd _ _ = A'.hom ∧ e ≫ f = Φ.left ≫ φB

abbrev pmap {Z Z' : Scheme.{0}} (t : Z ⟶ S) (g : Z' ⟶ Z) : pullback A.hom (g ≫ t) ⟶ pullback A.hom t :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by rw [pullback.condition, Category.assoc])

variable {A B L M}

theorem wit_pull (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left}
    (h : Wit A B L M t f) (g : Z' ⟶ Z) : Wit A B L M (g ≫ t) (pmap A t g ≫ f) := by
  obtain ⟨A', B', _, _, φA, φB, Φ, hA, hB, hΦ, hI, e, e1, e2, e3⟩ := h
  refine ⟨(Over.pullback g).obj A', (Over.pullback g).obj B', inferInstance, inferInstance,
    pullback.fst _ _ ≫ φA, pullback.fst _ _ ≫ φB, (Over.pullback g).map Φ,
    (isGrpPullback_pullback A' g).comp hA, (isGrpPullback_pullback B' g).comp hB, inferInstance, ?_, ?_⟩
  · refine lbIso_pull hL hM (pullback.fst _ _) rfl ?_ hI
    rw [← Category.assoc, show ((Over.pullback g).map Φ).left ≫ pullback.fst B'.hom g =
      pullback.fst A'.hom g ≫ Φ.left from pullback.lift_fst _ _ _, Category.assoc]
  · have hw : (pullback.fst A'.hom g ≫ φA) ≫ A.hom = pullback.snd A'.hom g ≫ g ≫ t := by
      rw [Category.assoc, hA.1.w, ← Category.assoc, pullback.condition, Category.assoc]
    have key : pullback.lift (pullback.fst A'.hom g ≫ φA) (pullback.snd A'.hom g) hw ≫ pmap A t g =
        pullback.fst A'.hom g ≫ e := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, e1]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, e2, pullback.condition]
    refine ⟨pullback.lift (pullback.fst _ _ ≫ φA) (pullback.snd _ _) hw, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _, ?_⟩
    rw [← Category.assoc, key, Category.assoc, e3, ← Category.assoc, ← Category.assoc,
      show ((Over.pullback g).map Φ).left ≫ pullback.fst B'.hom g =
        pullback.fst A'.hom g ≫ Φ.left from pullback.lift_fst _ _ _]

variable (A B L M) in

structure Pt (Z : Scheme.{0}) where

  t : Z ⟶ S

  f : pullback A.hom t ⟶ B.left
  wit : Wit A B L M t f

theorem Pt.ext' {Z : Scheme.{0}} {x y : Pt A B L M Z} (e : x.t = y.t)
    (h : pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition, e]) ≫ x.f = y.f) :
    x = y := by
  obtain ⟨t, f, w⟩ := x
  obtain ⟨t', f', w'⟩ := y
  dsimp only at e h
  revert h
  subst e
  intro h
  rw [pullback.lift_fst_snd, Category.id_comp] at h
  cases h
  rfl

theorem lift_pmap_id {Z : Scheme.{0}} (t : Z ⟶ S) (h : pullback.fst A.hom t ≫ A.hom = pullback.snd A.hom t ≫ 𝟙 Z ≫ t) :
    pullback.lift (pullback.fst A.hom t) (pullback.snd A.hom t) h ≫ pmap A t (𝟙 Z) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]

theorem lift_pmap_comp {Z Z' Z'' : Scheme.{0}} (t : Z ⟶ S) (g : Z' ⟶ Z) (g' : Z'' ⟶ Z')
    (h : pullback.fst A.hom (g' ≫ g ≫ t) ≫ A.hom = pullback.snd A.hom (g' ≫ g ≫ t) ≫ (g' ≫ g) ≫ t) :
    pullback.lift (pullback.fst A.hom (g' ≫ g ≫ t)) (pullback.snd A.hom (g' ≫ g ≫ t)) h ≫ pmap A t (g' ≫ g) =
      pmap A (g ≫ t) g' ≫ pmap A t g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.assoc]

def Pt.map (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Pt A B L M Z) : Pt A B L M Z' :=
  ⟨g ≫ x.t, pmap A x.t g ≫ x.f, wit_pull hL hM x.wit g⟩

theorem Pt.map_id (hL : L.IsLB) (hM : M.IsLB) {Z : Scheme.{0}} (x : Pt A B L M Z) : x.map hL hM (𝟙 Z) = x := by
  refine Pt.ext' (Category.id_comp _) ?_
  show _ ≫ pmap A x.t (𝟙 Z) ≫ x.f = x.f
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x.f) (lift_pmap_id x.t _)).trans (Category.id_comp _))

theorem Pt.map_comp (hL : L.IsLB) (hM : M.IsLB) {Z Z' Z'' : Scheme.{0}} (g : Z' ⟶ Z) (g' : Z'' ⟶ Z')
    (x : Pt A B L M Z) : x.map hL hM (g' ≫ g) = (x.map hL hM g).map hL hM g' := by
  refine Pt.ext' (Category.assoc _ _ _) ?_
  show _ ≫ pmap A x.t (g' ≫ g) ≫ x.f = pmap A (g ≫ x.t) g' ≫ pmap A x.t g ≫ x.f
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x.f) (lift_pmap_comp x.t g g' _)).trans
    (Category.assoc _ _ _))

variable (A B L M) in

def homFun (hL : L.IsLB) (hM : M.IsLB) : Scheme.{0}ᵒᵖ ⥤ Type where
  obj Z := Pt A B L M Z.unop
  map g := TypeCat.ofHom (Pt.map hL hM g.unop)
  map_id Z := by
    ext x
    exact Pt.map_id hL hM x
  map_comp g g' := by
    ext x
    exact Pt.map_comp hL hM _ _ x

variable (A B L M) in

def homProj (hL : L.IsLB) (hM : M.IsLB) : homFun A B L M hL hM ⟶ yoneda.obj S where
  app Z := TypeCat.ofHom fun x => x.t

@[simp] theorem Pt.map_t (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Pt A B L M Z) :
    (x.map hL hM g).t = g ≫ x.t := rfl

def Pt.ofData {Z : Scheme.{0}} (t : Z ⟶ S) (A' B' : Over Z) [GrpObj A'] [GrpObj B'] (φA : A'.left ⟶ A.left)
    (φB : B'.left ⟶ B.left) (Φ : A' ⟶ B') (hA : IsGrpPullback A' A t φA) (hB : IsGrpPullback B' B t φB)
    (hΦ : IsMonHom Φ) (hI : LBIso (L.pull φA) ((M.pull φB).pull Φ.left)) : Pt A B L M Z :=
  ⟨t, hA.1.isoPullback.inv ≫ Φ.left ≫ φB, A', B', inferInstance, inferInstance, φA, φB, Φ, hA, hB, hΦ, hI,
    hA.1.isoPullback.hom, by simp, by simp, by simp⟩

@[simp] theorem Pt.ofGroupPullbackData_base {Z : Scheme.{0}} (t : Z ⟶ S) (A' B' : Over Z) [GrpObj A'] [GrpObj B']
    (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (Φ : A' ⟶ B') (hA : IsGrpPullback A' A t φA)
    (hB : IsGrpPullback B' B t φB) (hΦ : IsMonHom Φ) (hI : LBIso (L.pull φA) ((M.pull φB).pull Φ.left)) :
    (Pt.ofData (L := L) (M := M) t A' B' φA φB Φ hA hB hΦ hI).t = t := rfl

theorem homFun_map (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Pt A B L M Z) :
    (homFun A B L M hL hM).map g.op x = x.map hL hM g := rfl

theorem homProj_app (hL : L.IsLB) (hM : M.IsLB) {Z : Scheme.{0}} (x : Pt A B L M Z) :
    (homProj A B L M hL hM).app (Opposite.op Z) x = x.t := rfl

end GlobalTheory.EndLoc.HomGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZero
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

noncomputable section

namespace GlobalTheory.CMModel.SqNe

theorem natMul_mem {p : ℕ} {F : IntermediateField ℚ ℂ} {L : PeriodPair} {t : ℂ} (h : Datum p F L t) :
    (p : ℂ) * t ∈ L.lattice := by
  have h1 := neg_mem (h.mul _ h.ker)
  rw [← mul_assoc, ← sq, sqrtNegNat_sq, neg_mul, neg_neg] at h1
  exact h1

theorem mul_notMem {p : ℕ} {F : IntermediateField ℚ ℂ} {L : PeriodPair} {t : ℂ} (h : Datum p F L t)
    {n : ℕ} (hn : Nat.Coprime n p) : (n : ℂ) * t ∉ L.lattice := fun hm => by
  have h1 := natMul_mem h
  obtain ⟨a, b, e⟩ := Nat.isCoprime_iff_coprime.2 hn
  have e' : (a : ℂ) * n + b * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) e
  have := add_mem (zsmul_mem hm a) (zsmul_mem h1 b)
  rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← add_mul, e', one_mul] at this
  exact h.notMem this

theorem coprime_sq {p : ℕ} (hp : p.Prime) (k : Sq p) : Nat.Coprime (k.1 : ℕ) p :=
  ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => k.2.1 ((ZMod.natCast_eq_zero_iff _ _).2 h)).symm

theorem sqPt_and_sqProd_ne_zero : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
      (∀ k : Sq p, sqPt p t k ∉ L.lattice ∧ (p : ℂ) * sqPt p t k ∈ L.lattice) ∧ sqProd p L t ≠ 0 := by
  intro p F L t hp h4 h3 h
  have h2 : p ≠ 2 := by omega
  refine ⟨fun k => ⟨mul_notMem h (coprime_sq hp k), ?_⟩, ?_⟩
  · have := zsmul_mem (natMul_mem h) (k.1 : ℕ)
    rw [zsmul_eq_mul] at this
    convert this using 1
    rw [sqPt]; push_cast; ring
  · refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    rw [Ne, GlobalTheory.derivWeierstrassP_eq_zero_iff L (show sqPt p t k ∉ L.lattice from mul_notMem h (coprime_sq hp k))]
    have := mul_notMem h (Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hp).2 h2.symm)
      (coprime_sq hp k))
    intro hm
    apply this
    convert hm using 1
    rw [sqPt]; push_cast; ring

end GlobalTheory.CMModel.SqNe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdKernelMultiplierTranslateNeg
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.KerPerm

theorem prod_eq_of_perm_mod (Λ : Submodule ℤ ℂ) (T : Finset ℂ) (f ψ : ℂ → ℂ)
    (hψ : ∀ z l, l ∈ Λ → ψ (z + l) = ψ z)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ Λ → a = b)
    (hmap : ∀ t ∈ T, ∃ u ∈ T, f t - u ∈ Λ)
    (hinj : ∀ a b, f a - f b ∈ Λ → a - b ∈ Λ) :
    ∏ t ∈ T, ψ (f t) = ∏ t ∈ T, ψ t := by
  classical
  choose g hgT hg using hmap
  have ginj : ∀ a (ha : a ∈ T) b (hb : b ∈ T), g a ha = g b hb → a = b := by
    intro a ha b hb h
    apply hsep a ha b hb
    apply hinj
    have := Λ.sub_mem (hg a ha) (hg b hb)
    rw [h] at this
    simpa using this
  refine Finset.prod_bij g hgT ginj ?_ ?_
  · intro b hb
    obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le g hgT
      (fun a b ha hb h => ginj a ha b hb h) le_rfl b hb
    exact ⟨a, ha, h.symm⟩
  · intro a ha
    have := hψ (g a ha) _ (hg a ha)
    simpa using this

theorem prod_ker_translate_neg : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (φ : ℂ → ℂ), IsKerReps L α S → MulStable L α → (∀ z l, l ∈ L.lattice → φ (z + l) = φ z) → (∀ z s, α * s ∈ L.lattice → φ (z + s) * ∏ t ∈ S, φ (z + s + t) = φ z * ∏ t ∈ S, φ (z + t)) ∧ ∀ z, ∏ t ∈ S, φ (z - t) = ∏ t ∈ S, φ (z + t) := by
  classical
  intro L α S φ ⟨h1, h2, h3⟩ _ hφ
  have h0 : (0 : ℂ) ∉ S := fun h => (h1 0 h).2 L.lattice.zero_mem
  have hψ : ∀ z : ℂ, ∀ x l, l ∈ L.lattice → φ (z + (x + l)) = φ (z + x) := by
    intro z x l hl
    rw [← add_assoc, hφ _ _ hl]
  refine ⟨fun z s hs => ?_, fun z => ?_⟩
  · have key := prod_eq_of_perm_mod L.lattice (insert 0 S) (fun t => s + t) (fun x => φ (z + x)) (hψ z)
      (by
        intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
        · rfl
        · exact absurd (by simpa using hab) (h1 b hb).2
        · exact absurd (by simpa using hab) (h1 a ha).2
        · exact h2 a ha b hb hab)
      (by
        intro t ht
        have hk : α * (s + t) ∈ L.lattice := by
          rw [mul_add]
          refine L.lattice.add_mem hs ?_
          rcases Finset.mem_insert.1 ht with rfl | ht
          · simp
          · exact (h1 t ht).1
        by_cases hm : s + t ∈ L.lattice
        · exact ⟨0, Finset.mem_insert_self _ _, by simpa using hm⟩
        · obtain ⟨P, hP, h⟩ := h3 _ hk hm
          exact ⟨P, Finset.mem_insert_of_mem hP, h⟩)
      (by
        intro a b h
        simpa using h)
    rw [Finset.prod_insert h0, Finset.prod_insert h0] at key
    simpa [add_assoc] using key
  · have key := prod_eq_of_perm_mod L.lattice S (fun t => -t) (fun x => φ (z + x)) (hψ z) h2
      (by
        intro t ht
        refine h3 (-t) ?_ ?_
        · rw [mul_neg]; exact L.lattice.neg_mem (h1 t ht).1
        · intro h; exact (h1 t ht).2 (by simpa using h))
      (by
        intro a b h
        have := L.lattice.neg_mem h
        convert this using 1
        ring)
    simpa [sub_eq_add_neg] using key

end GlobalTheory.KerPerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixIndep

theorem eq_zero_of_locally {X : Scheme.{0}} {U : X.Opens} (s : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ (X.presheaf.map (homOfLE hW).op).hom s = 0) :
    s = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, h0⟩ := h x hx
  have e1 := X.presheaf.germ_res_apply (homOfLE hW) x hxW s
  change (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom 0
  rw [← e1, h0, map_zero, map_zero]

theorem appLE_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f₁ ⁻¹ᵁ U) (a : Γ(Y, U)) :
    (f₁.appLE U V e).hom a = (f₂.appLE U V (h ▸ e)).hom a := by
  subst h; rfl

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V W : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V)
    (a : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_appLE {X Y Z : Scheme.{0}} (g : X ⟶ Y) (f : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : W ≤ g ⁻¹ᵁ V) (a : Γ(Z, U)) :
    (g.appLE V W e₂).hom ((f.appLE U V e₁).hom a) =
      ((g ≫ f).appLE U W (fun _ hx => e₁ (e₂ hx))).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.HomFixIndep

open GlobalTheory.HomFixIndep in

theorem GlobalTheory.HomFixIndep.pulled_basis_indep : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (ψA : A'.left ⟶ (topS Rg ⊗ A).left), IsGrpPullback A' A t φA' → ψA ≫ (snd (topS Rg) A).left = φA' → ∀ (d : Fin mA → Γ(Sp R, ⊤)), (∀ (j : Fin 1 → L.ι) (x : A'.left), x ∈ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j → ∃ (W : A'.left.Opens) (hW : W ≤ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j), x ∈ W ∧ ∑ i, (A'.hom.appLE ⊤ W (by simp)).hom (d i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j) W (hW.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j))).hom ((bA i).f j) = 0) → d = 0 := by
  intro Rg _ A _ L k mA bA hB R _ t A' _ φA' ψA hT hψ d hloc
  let t'' : Spec (CommRingCat.of R) ⟶ (topS Rg).left :=
    IsOpenImmersion.lift (⊤ : (Sp Rg).Opens).ι t (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial)
  have ht'' : (baseAt t'').hom = t := by simp [t'', baseAt, topS, overRes, baseOver]
  set T := baseAt t'' with hTdef
  have hw : (snd T A).left ≫ A.hom = (fst T A).left ≫ t := by
    rw [← ht'', Over.w (snd T A), Over.w (fst T A)]
  let g : (T ⊗ A).left ⟶ A'.left := hT.1.lift (snd T A).left (fst T A).left hw
  have hg1 : g ≫ φA' = (snd T A).left := hT.1.lift_fst _ _ _
  have hg2 : g ≫ A'.hom = (fst T A).left := hT.1.lift_snd _ _ _
  have hgψ : g ≫ ψA = (homAt t'' ▷ A).left := by
    apply psi_unique
    rw [Category.assoc, hψ, hg1, ← Over.comp_left, whiskerRight_snd]
  let b' : Fin mA → LB.Sec (LPow A L (k : ℤ) T) := fun i =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLP A L (k : ℤ) (homAt t'' ▷ A) (whiskerRight_snd (homAt t'') A) (bA i)
  obtain ⟨hli, -⟩ := hB R t'' b' (fun i => ReciprocityTheory.ChartRestriction.G.PullbackSections.isPullSec_pullSecLP A L (k : ℤ) _ _ (bA i))
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  refine hli d ?_ i
  apply Subtype.ext
  funext j
  have hD : (LPow A L (k : ℤ) T).U j ≤ g ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j := by
    intro y hy
    have e : g ≫ ψA ≫ (snd (topS Rg) A).left = (snd T A).left := by
      rw [← Category.assoc, hgψ, ← Over.comp_left, whiskerRight_snd]
    have h1 : (g ≫ ψA ≫ (snd (topS Rg) A).left).base y ∈ (L.U (j 0) : Set A.left) := by
      rw [e]; exact Set.mem_iInter.1 hy 0
    exact Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h1
  have hF : (∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j) (by simp)).hom (d i) *
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j)
        (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j)).hom ((bA i).f j)) = 0 := by
    refine eq_zero_of_locally _ fun x hx => ?_
    obtain ⟨W, hW, hxW, h0⟩ := hloc j x hx
    refine ⟨W, hW, hxW, ?_⟩
    rw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h0
    rw [map_mul]
    exact congrArg₂ (· * ·) (res_appLE _ _ _ _ _ _ _) (res_appLE _ _ _ _ _ _ _)
  calc (∑ i, d i • SecM.ofSec A (b' i)).val j
      = ∑ i, ((fst T A).left.appLE ⊤ ((LPow A L (k : ℤ) T).U j) (by simp)).hom (d i) *
          ((homAt t'' ▷ A).left.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
            ((LPow A L (k : ℤ) T).U j) (chart_le_res A L _ (whiskerRight_snd (homAt t'') A) _ j)).hom ((bA i).f j) := by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
    _ = (g.appLE _ _ hD).hom (∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j) (by simp)).hom (d i) *
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j)
        (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j)).hom ((bA i).f j)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        exact congrArg₂ (· * ·) (((appLE_appLE _ _ _ _ _ _ _ _).trans (appLE_eq hg2 _ _ _ _)).symm)
          (((appLE_appLE _ _ _ _ _ _ _ _).trans (appLE_eq hgψ _ _ _ _)).symm)
    _ = _ := by rw [hF, map_zero]; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionAlgebraTopologicalRing
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QuatTop

variable {R : Type} [CommRing R] [TopologicalSpace R] {a b : R}

theorem continuous_coord_re : Continuous (fun x : ℍ[R, a, b] => x.re) :=
  (continuous_apply (0 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imI : Continuous (fun x : ℍ[R, a, b] => x.imI) :=
  (continuous_apply (1 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imJ : Continuous (fun x : ℍ[R, a, b] => x.imJ) :=
  (continuous_apply (2 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_coord_imK : Continuous (fun x : ℍ[R, a, b] => x.imK) :=
  (continuous_apply (3 : Fin 4)).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_of_coords {X : Type*} [TopologicalSpace X] {g : X → ℍ[R, a, b]}
    (h0 : Continuous fun x => (g x).re) (h1 : Continuous fun x => (g x).imI)
    (h2 : Continuous fun x => (g x).imJ) (h3 : Continuous fun x => (g x).imK) : Continuous g := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem isTopologicalRing [IsTopologicalRing R] : IsTopologicalRing ℍ[R, a, b] := by
  have c0 := (continuous_coord_re (R := R) (a := a) (b := b))
  have c1 := (continuous_coord_imI (R := R) (a := a) (b := b))
  have c2 := (continuous_coord_imJ (R := R) (a := a) (b := b))
  have c3 := (continuous_coord_imK (R := R) (a := a) (b := b))
  have p0 := c0.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p1 := c1.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p2 := c2.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have p3 := c3.comp (continuous_fst (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q0 := c0.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q1 := c1.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q2 := c2.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have q3 := c3.comp (continuous_snd (X := ℍ[R, a, b]) (Y := ℍ[R, a, b]))
  have hadd : ContinuousAdd ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_add]; exact p0.add q0) (by simp only [QuaternionAlgebra.imI_add]; exact p1.add q1) (by simp only [QuaternionAlgebra.imJ_add]; exact p2.add q2) (by simp only [QuaternionAlgebra.imK_add]; exact p3.add q3)⟩
  have hmul : ContinuousMul ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imJ_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_mul]; fun_prop)⟩
  have hneg : ContinuousNeg ℍ[R, a, b] := ⟨continuous_of_coords
    (by simp only [QuaternionAlgebra.re_neg]; exact c0.neg) (by simp only [QuaternionAlgebra.imI_neg]; exact c1.neg) (by simp only [QuaternionAlgebra.imJ_neg]; exact c2.neg) (by simp only [QuaternionAlgebra.imK_neg]; exact c3.neg)⟩
  exact {}

end GlobalTheory.QuatTop

open GlobalTheory.QuatTop in
theorem GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), IsTopologicalRing ℍ[R, a, b] ∧ Continuous (nrm : ℍ[R, a, b] → R) ∧ Continuous (fun x : ℍ[R, a, b] => x.re) ∧ (T2Space R → T2Space ℍ[R, a, b]) := by
  intro R _ _ _ a b
  have c0 := (continuous_coord_re (R := R) (a := a) (b := b))
  have c1 := (continuous_coord_imI (R := R) (a := a) (b := b))
  have c2 := (continuous_coord_imJ (R := R) (a := a) (b := b))
  have c3 := (continuous_coord_imK (R := R) (a := a) (b := b))
  refine ⟨isTopologicalRing, ?_, c0, fun _ => ?_⟩
  · unfold nrm; fun_prop
  · have hinj : Function.Injective (coords : ℍ[R, a, b] → Fin 4 → R) := by
      intro x y h
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      have e2 := congrFun h 2
      have e3 := congrFun h 3
      simp [coords] at e0 e1 e2 e3
      ext <;> assumption
    exact (Topology.IsEmbedding.mk ⟨rfl⟩ hinj).t2Space
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOnePrescribedReAtIdempotent
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory

theorem quat_norm_one_re_at_idem : ∀ (R : Type) [CommRing R] (a b ε p q : R), ε * ε = ε → IsUnit a → IsUnit b →
    IsUnit (2 : R) → ε * (b - (p ^ 2 - a * q ^ 2)) = 0 → ∀ t : R, ∃ h : ℍ[R, a, b], nrm h = 1 ∧ ε * h.re = ε * t := by
  intro R _ a b ε p q hε ha hb h2 hE t
  obtain ⟨c, hc⟩ := ((h2.mul ha).mul hb)
  have hu : 2 * a * b * ((c⁻¹ : Rˣ) : R) = 1 := by
    rw [← hc]; simp
  set u : R := ((c⁻¹ : Rˣ) : R) with hu_def
  set l : R := (t ^ 2 - a - 1) * u with hl
  refine ⟨⟨ε * t + (1 - ε), ε * (l * b + 1), ε * (l * a * q), ε * (l * p)⟩, ?_, ?_⟩
  · simp only [nrm]
    linear_combination ((t - 1) ^ 2 + (-a * (l * b + 1) ^ 2 - b * (l * a * q) ^ 2 + a * b * (l * p) ^ 2)) * hε
      - ε * (t ^ 2 - a - 1) * hu - l ^ 2 * a * b * hE
  · show ε * (ε * t + (1 - ε)) = ε * t
    linear_combination (t - 1) * hε

end GlobalTheory
end

