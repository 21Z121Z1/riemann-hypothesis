import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3172
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import GroundTheory.Brauer.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3173
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorPairingFactorInclusionPeriodsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorPairing_factorInclusion_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.Mum.pairing_factor | exact GlobalTheory.Mum.pairing_factor | (intros; apply GlobalTheory.Mum.pairing_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentXStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], ∀ φ ψ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) → (∀ i, φ (X i) = ψ (X i)) → φ = ψ := by
  first | exact @GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent | exact GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent | (intros; apply GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqDegCentralSimpleCommCentralise
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.RegDeg

open Polynomial

theorem natDegree_minpoly_eq : ∀ (F C : Type) [Field F] [Ring C] [Algebra F C] [Algebra.IsCentral F C]
    [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ), Module.finrank F C = n ^ 2 → ∀ c : C,
    (minpoly F c).Separable → (∀ a b : C, Commute a c → Commute b c → Commute a b) →
    (minpoly F c).natDegree = n := by
  intro F C _ _ _ _ _ _ n hC c hsep hcomm
  obtain ⟨k, hk0, hkC, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F C
  have hkn : k = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hkC.symm.trans hC)
  subst hkn
  set K := AlgebraicClosure F
  set x : K ⊗[F] C := (1 : K) ⊗ₜ[F] c with hx
  have hxi : IsIntegral K x := IsIntegral.of_finite K x
  have hxr : x = Algebra.TensorProduct.includeRight c := rfl
  have hdvd : minpoly K x ∣ (minpoly F c).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hxr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K c hxi
  have hmap : (minpoly F c).map (algebraMap F K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr
      (minpoly.ne_zero (IsIntegral.of_finite F c))
  have hle : (minpoly K x).natDegree ≤ (minpoly F c).natDegree := by
    calc (minpoly K x).natDegree ≤ ((minpoly F c).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap
      _ = (minpoly F c).natDegree := natDegree_map _
  have hxsep : (minpoly K x).Separable := (hsep.map).of_dvd hdvd

  let S := Subalgebra.centralizer F ({c} : Set C)
  letI : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b => Subtype.ext (by
        have ha : Commute (a : C) c := ((Subalgebra.mem_centralizer_iff F).mp a.2 c rfl).symm
        have hb : Commute (b : C) c := ((Subalgebra.mem_centralizer_iff F).mp b.2 c rfl).symm
        exact (hcomm _ _ ha hb).eq) }
  have hcent : ∀ y : C, y * c = c * y ↔ y ∈ Set.range (S.val) := by
    intro y
    constructor
    · intro h
      refine ⟨⟨y, ?_⟩, rfl⟩
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact h.symm
    · rintro ⟨w, rfl⟩
      exact ((Subalgebra.mem_centralizer_iff F).mp w.2 c rfl).symm
  set N := e x with hN
  have hmN : minpoly K N = minpoly K x := minpoly.algEquiv_eq e x
  have hNcomm : ∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B := by
    intro A B hA hB
    have hA' : e.symm A * x = x * e.symm A := by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hA.eq
    have hB' : e.symm B * x = x * e.symm B := by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hB.eq
    have h := GlobalTheory.LKCentAf.commute_of_centralizer F K C S c S.val hcent _ _ hA' hB'
    have h2 := congrArg e h
    rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h2
    exact h2
  have hdegN := GlobalTheory.T.natDegree_minpoly_eq_of_separable_commutant_comm K k N (by rw [hmN]; exact hxsep) hNcomm
  have hxk : (minpoly K x).natDegree = k := by rw [← hmN]; exact hdegN
  rw [← hxk]
  exact le_antisymm hge hle

end GlobalTheory.RegDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem neg_one_left_comp_self {K : Type} [Field K] (A : AbVar K) :
    (Hom.hom (-(𝟙 A))).left ≫ (Hom.hom (-(𝟙 A))).left = 𝟙 A.X.left := by
  have h : (-(𝟙 A)) ≫ (-(𝟙 A)) = 𝟙 A := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp]
  have h2 := congrArg (fun g : A ⟶ A => (Hom.hom g).left) h
  simpa only [comp_hom, Over.comp_left, id_hom, Over.id_left] using h2

theorem exists_symm_ample :
    ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c ∧ CechPic.pull (Hom.hom (-(𝟙 A))).left c = c := by
  intro K _ A
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.abelianVariety_exists_ampleClass K A
  set f : A.X.left ⟶ A.X.left := (Hom.hom (-(𝟙 A))).left with hf
  have hff : f ≫ f = 𝟙 A.X.left := neg_one_left_comp_self A
  have hiso : IsIso f := ⟨⟨f, hff, hff⟩⟩
  have hfin : IsFinite (Hom.hom (-(𝟙 A))).left := by
    rw [← hf]; infer_instance
  refine ⟨c₀ + CechPic.pull f c₀, GlobalTheory.T.isAbelianVarietyAmpleClass_add K A _ _ hc₀ (GlobalTheory.T.isAbelianVarietyAmpleClass_pullback_of_isFinite K A A (-(𝟙 A)) c₀ hfin hc₀), ?_⟩
  rw [map_add, ← CechPic.pull_comp, hff, CechPic.pull_id, add_comm]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyModuliMapOfMarkedPeriodIsometry
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTIso

theorem one_comp_monHom {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (f : A ⟶ A') [IsMonHom f] :
    (1 : A ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem comp_one' {S : Scheme.{0}} {A A' : Over S} [GrpObj A'] (f : A ⟶ A') : f ≫ (1 : A' ⟶ A') = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]

theorem pull_birig : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (f : A ⟶ A'), IsMonHom f → ∀ P : LB (G2 A').left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A' A') (fst A' A')).left) →
    (P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).IsLB ∧
    (∃ t : ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
    LBIso (P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left)
      ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (snd A A) (fst A A)).left) := by
  intro S A A' _ _ _ _ f hf P hP ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hs
  haveI := hf
  set φ₂ := (lift (fst A A ≫ f) (snd A A ≫ f)).left with hφ₂
  have hP₂ : (P.pull φ₂).IsLB := pull_isLB hP _

  have triv : ∀ (l : A ⟶ G2 A) (l' : A' ⟶ G2 A'), l ≫ lift (fst A A ≫ f) (snd A A ≫ f) = f ≫ l' →
      ∀ t : (P.pull l'.left).Gen, t.IsGen → ∃ s : ((P.pull φ₂).pull l.left).Gen, s.IsGen := by
    intro l l' hl t ht
    have e₁ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull l'.left).pull f.left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP f.left rfl
    have e₂ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull φ₂).pull l.left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP l.left (by rw [hφ₂, ← Over.comp_left, ← Over.comp_left, hl])
    obtain ⟨s, hs⟩ := GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e₁.symm
      (pullGenLB t f.left) (pullGenLB_isGen ht f.left)
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP _) (pull_isLB hP₂ _) e₂ s hs
  refine ⟨hP₂, triv _ _ ?_ t₁ ht₁, triv _ _ ?_ t₂ ht₂, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']
  · apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']
  · have eq : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A' A') (fst A' A')).left := by
      rw [hφ₂, ← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have e₁ : LBIso (P.pull φ₂) ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂) :=
      GlobalTheory.GenSpread.lbIso_pullback hs φ₂
    have e₂ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left))
        ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP φ₂ rfl
    have e₃ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left)) ((P.pull φ₂).pull (lift (snd A A) (fst A A)).left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq.symm
    exact LBIso.trans hP₂ (pull_isLB (pull_isLB hP _) _) (pull_isLB hP₂ _) e₁
      (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hP₂ _) e₂.symm e₃)

theorem weil_pull_iso : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (F : A ≅ A'), IsMonHom F.hom → ∀ P : LB (G2 A').left, P.IsLB → ∀ (T : Over S) (k : ℤ) (x y : T ⟶ A)
    (c : Γ(T.left, ⊤)ˣ), Out.WeilIs A' (P.pull (lift (𝟙 A') (𝟙 A')).left) k (x ≫ F.hom) (y ≫ F.hom) c →
    Out.WeilIs A ((P.pull (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left).pull (lift (𝟙 A) (𝟙 A)).left) k x y c := by
  intro S A A' _ _ _ _ F hF P hP T k x y c H
  haveI := hF
  set φ₂ := (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left with hφ₂
  have eq : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = F.hom.left ≫ (lift (𝟙 A') (𝟙 A')).left := by
    rw [hφ₂, ← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e₁ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP _ rfl
  have e₂ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull (lift (𝟙 A') (𝟙 A')).left).pull F.hom.left) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq
  have iso := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁.symm e₂
  let x₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A' := Over.homMk (x.left ≫ F.hom.left) (by simp)
  let y₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A' := Over.homMk (y.left ≫ F.hom.left) (by simp)
  refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm S S A' A (𝟙 S) F.hom.left _ _ (pull_isLB hP _)
    (pull_isLB (pull_isLB hP _) _) (isGrpPullback_of_iso F) iso T k x y x₀ y₀ c rfl rfl).2 ?_
  exact GlobalTheory.UnifPoint.weilIs_congr (Category.comp_id _).symm rfl rfl H

theorem nonempty_objMap_of_markedIsom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o o' : Obj b N (spMap σ)) h hL h' hL' (D' D'' : PLat D.O D.inv) t t' Q Q' e e' (w : D'.La ≃ₗ[D.O] D''.La) (u : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)), 0 < N → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → UnifAt (o'.fam h' hL') σ ρ N D'' t' Q' (𝟙 _) e' → IsMarkedIsom N D' D'' t t' w → (∀ x, Q' (w x) = u (Q x)) → Nonempty (ObjMap o o' (𝟙 _)) := by
  rintro p _ D R _ b N σ ρ o o' h hL h' hL' D' D'' t t' Q Q' e e' w u hN0
    ⟨-, hP, he, hk, hl, hw, hη⟩ ⟨-, hP', he', hk', hl', hw', hη'⟩ ⟨hiso, hmark⟩ hu

  have k1 : ∀ z, e z = 1 → e' (u z) = 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hk z).1 hz
    exact (hk' _).2 ⟨w x, hu x⟩
  have k2 : ∀ z, e' z = 1 → e (u.symm z) = 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hk' z).1 hz
    refine (hk _).2 ⟨w.symm x, ?_⟩
    apply u.injective
    rw [u.apply_symm_apply, ← hu, w.apply_symm_apply]
  obtain ⟨f, ⟨hf, hfe⟩, -⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o'.A D.g D.g o.ab o'.ab h h' e e' u.toLinearMap he he' k1
  obtain ⟨f', ⟨hf', hfe'⟩, -⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o'.A o.A D.g D.g o'.ab o.ab h' h e' e u.symm.toLinearMap he' he k2
  obtain ⟨f₀, -, uid⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o.A D.g D.g o.ab o.ab h h e e LinearMap.id he he (fun z hz => hz)
  obtain ⟨f₀', -, uid'⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o'.A o'.A D.g D.g o'.ab o'.ab h' h' e' e' LinearMap.id he' he' (fun z hz => hz)
  have hfe2 : ∀ z, e' (u z) = e z ≫ f := hfe
  have hfe2' : ∀ z, e (u.symm z) = e' z ≫ f' := hfe'
  haveI := hf
  haveI := hf'
  have c1 : f ≫ f' = 𝟙 _ := by
    rw [uid (f ≫ f') ⟨inferInstance, fun z => ?_⟩, uid (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]
    refine Eq.trans ?_ (Category.assoc (e z) f f')
    rw [← hfe2]
    exact (by rw [u.symm_apply_apply]; rfl : e (LinearMap.id z) = e (u.symm (u z))).trans (hfe2' (u z))
  have c2 : f' ≫ f = 𝟙 _ := by
    rw [uid' (f' ≫ f) ⟨inferInstance, fun z => ?_⟩, uid' (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]
    refine Eq.trans ?_ (Category.assoc (e' z) f' f)
    rw [← hfe2']
    exact (by rw [u.apply_symm_apply]; rfl : e' (LinearMap.id z) = e' (u (u.symm z))).trans (hfe2 (u.symm z))
  let F : o.A ≅ o'.A := ⟨f, f', c1, c2⟩
  haveI : IsMonHom F.hom := hf

  have hcomm : ∀ (c : D.O) z, u (ρ c *ᵥ z) = ρ c *ᵥ u z := by
    intro c
    have := LinearMap.ext_on_range (R := ℝ) (v := fun x => Q x) hP.2.2.2.1
      (f := (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)).restrictScalars ℝ)
      (g := (Matrix.toLin' (ρ c) ∘ₗ u.toLinearMap).restrictScalars ℝ) (fun x => by
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
        rw [← hP.1, ← hu, ← hu, w.map_smul, hP'.1])
    intro z
    simpa using LinearMap.congr_fun this z
  have hact : ∀ c, o.act.act c ≫ f = f ≫ o'.act.act c := by
    intro c
    haveI := o.act.hom c
    haveI := o'.act.hom c
    obtain ⟨fa, -, ua⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o'.A D.g D.g o.ab o'.ab h h' e e'
      (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)) he he' (fun z hz => by
        obtain ⟨x, rfl⟩ := (hk z).1 hz
        simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
        rw [← hP.1]
        exact k1 _ ((hk _).2 ⟨_, rfl⟩))
    rw [ua (o.act.act c ≫ f) ⟨inferInstance, fun z => ?_⟩, ua (f ≫ o'.act.act c) ⟨inferInstance, fun z => ?_⟩]
    · simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
      refine Eq.trans ?_ (Category.assoc (e z) f (o'.act.act c))
      rw [← hfe2, hcomm]
      exact hl' c (u z)
    · simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
      refine Eq.trans ?_ (Category.assoc (e z) (o.act.act c) f)
      rw [hfe2]
      exact congrArg (· ≫ f) (hl c z)
  have hT : (toUnit (Over.mk (𝟙 (Sp ℂ)))).left = 𝟙 _ := by
    simpa using Over.w (toUnit (Over.mk (𝟙 (Sp ℂ))))
  have heta : ∀ y, (o.eta y).left ≫ f.left = 𝟙 _ ≫ (o'.eta y).left := by
    intro y
    obtain ⟨e₀, he₀⟩ := hmark y
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hη2 : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y = e ((N : ℂ)⁻¹ • Q (t y)) := hη y
    have hη2' : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y = e' ((N : ℂ)⁻¹ • Q' (t' y)) := hη' y
    have a1 : (toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y) ≫ f = toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y := by
      refine (congrArg (· ≫ f) hη2).trans ((hfe2 _).symm.trans (Eq.trans ?_ hη2'.symm))
      have hz : (N : ℂ)⁻¹ • N • Q' e₀ = Q' e₀ := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]
      rw [map_smul, ← hu, he₀, map_add, map_nsmul, smul_add, hz, he'.1, (hk' (Q' e₀)).2 ⟨e₀, rfl⟩, _root_.mul_one]
    have a2 := congrArg (fun q => q.left) a1
    simp only [Over.comp_left, hT, Category.id_comp] at a2
    rw [Category.id_comp]
    exact a2
  obtain ⟨B1, B2, B3, B4⟩ := pull_birig (Sp ℂ) o.A o'.A f hf o'.P o'.isLB o'.rig₁ o'.rig₂ o'.symm
  have ew : ∀ (k : ℕ) a, e' ((k : ℂ)⁻¹ • Q' (w a)) = e ((k : ℂ)⁻¹ • Q a) ≫ f := by
    intro k a
    rw [hu, ← u.map_smul]
    exact hfe2 _
  have pol := GlobalTheory.T.birigidified_bundle_iso_of_weil_pairing_eq o.A D.g o.ab h o.P (o'.P.pull (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left)
    o.isLB o.rig₁ o.rig₂ o.symm B1 B2 B3 B4 e D'.La Q D'.EF he hP.2.1 hk hw (fun k a a₂ c hk0 hc => by
      have W' := hw' k (w a) (w a₂) c hk0 (by rw [hiso]; exact hc)
      rw [ew, ew] at W'
      exact weil_pull_iso (Sp ℂ) o.A o'.A F inferInstance o'.P o'.isLB _ k _ _ _ W')
  exact ⟨{ φ := f.left
           φ₂ := (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left
           cart := isGrpPullback_of_iso F
           sq := ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
           act := fun c => by rw [← Over.comp_left, hact c, Over.comp_left]
           pol := pol
           eta := heta }⟩

end GlobalTheory.HTIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelLevelLoweringQuotientFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_siegelLevelLoweringQuotientFamily : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Nonempty (SQuot F n (zetaAway n) j) := by
  first | exact @GlobalTheory.SiegLev.nonempty_sQuot | exact GlobalTheory.SiegLev.nonempty_sQuot | (intros; apply GlobalTheory.SiegLev.nonempty_sQuot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTwistedSectionComponent
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.KeyTwDeep

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.KeyRootTw in

theorem twSec_keyRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) →
    FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) →
    ∀ Z : Comp Xo c, Nonempty (TwSec U x Z (wtOf Dw 0 1)) := by
  intro E _ _ _ H Dw l Xo c r U x hU hx hF hpq hg
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨⟨ρ, hρmem⟩, hρ⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hval := GlobalTheory.T.theta_key_section_valuation_bounds_different κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval
  have hC := fun σ : c.F →+* ℂ => GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K
    (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨⟨ρ, hρmem⟩⟩ hpq hKmem hKval
  choose C hCpos hClog hCeq using hC
  have hgE := card_frame_index Dw e
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) := by
    simp [Fintype.card_sigma]
  have hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m :=
    wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 1) = -keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  have hadd : wtOf Dw 0 1 + wtOf Dw 0 (-1) = 0 := by
    rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]
  intro Z
  obtain ⟨a, ha, haK⟩ := hρ Z
  have hP : HasPts U Z := hasPts U hpq hg hU Z
  set s : Rul Xo c := idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs
  set s' : Rul Xo c := idem Z * (ρ : Rul Xo c) with hs'
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 1)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hρmem)
    rwa [zero_add, ← hex] at this
  have hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-1))) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hρmem
    have h2 : exZ Dw (wtOf Dw 0 (-1)) = keyEx Dw := by
      have h3 := exZ_add_eq (Dw := Dw) (wtOf Dw 0 1) (wtOf Dw 0 (-1))
      rw [hadd, hex] at h3
      have h4 : exZ Dw (0 : WTZ E) = 0 := by funext i; cases i <;> rfl
      rw [h4] at h3
      exact (neg_add_eq_zero.1 h3.symm).symm
    rwa [zero_add, ← h2] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsupp' : s' ∈ suppOn Z := by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hnorm := fun σ : c.F →+* ℂ => fun z (hz : z ∈ framesOn (U (goodOf c σ)) Z) =>
    homN_root E H Dw l Xo c (goodOf c σ) r (U (goodOf c σ)) x Z ρ K a (C σ) ha (hCpos σ) haK (hCeq σ) z hz
      ((hP.1 σ).2 z hz)
  have hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ := fun σ h => if_pos h
  have hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i) := fun m τ i j hij hj => by
    rw [hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]
  have hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 1) s z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).1.le
  have hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-1)) s' z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ ((1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).2.le
  let B : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)
  have hbnd := fun w (v : Rul Xo c → EReal) (hv : v ∈ valOn Z w) =>
    val_root E H Dw l Xo c Z w v hv ρ K a (B w) ha haK (hval w v (valOn_subset Z w hv)).1
      (hval w v (valOn_subset Z w hv)).2
  let t : TwSec U x Z (wtOf Dw 0 1) :=
    { even := even_wtOf _ _
      sig := s
      inv := s'
      sig_mem := hsm
      inv_mem := by
        have h5 := exZ_neg_eq (Dw := Dw) (wtOf Dw 0 1)
        have h6 : -wtOf Dw 0 1 = wtOf Dw 0 (-1) := neg_eq_of_add_eq_zero_right hadd
        rw [← h5, h6]; exact hsm'
      idem_sig := by rw [hs, ← mul_assoc, idem_mul_idem]
      idem_inv := by rw [hs', ← mul_assoc, idem_mul_idem]
      mul_inv := by rw [hs, hs', mul_mul_mul_comm, idem_mul_idem, Units.inv_mul, mul_one]
      cInf := fun σ => (‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ)
      cInf_pos := fun σ => Real.rpow_pos_of_pos (mul_pos (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) (hCpos σ)) _
      norm_inf := fun σ z hz => by
        rw [(hnorm σ z hz).1, norm_goodOf]
      cusp_sig := fun G hG f hf =>
        GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 1) s ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono 1) hsm hsupp hbd G hG f hf
      cusp_inv := fun G hG f hf => by
        have h7 := GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 (-1)) s' ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono (-1))
          hsm' hsupp' hbd' (G + wtOf Dw 0 1) (hG.add (even_wtOf _ _)) f hf
        rwa [add_assoc, hadd, add_zero] at h7
      lo := fun w => -(vAdd w a : ℝ) / 4 - B w
      hi := fun w => -(vAdd w a : ℝ) / 4
      lo_le := fun w v hv => (hbnd w v hv).1
      le_hi := fun w v hv => (hbnd w v hv).2
      finite_lo := by
        refine ((finite_vAdd ha).union (Set.finite_iUnion fun τ => finite_ord (embF c τ))).subset fun w hw => ?_
        by_contra hn
        simp only [Set.mem_union, Function.mem_support, Set.mem_iUnion, not_or, not_exists, not_not] at hn
        apply hw
        simp [B, hn.1, hn.2]
      finite_hi := by
        refine (finite_vAdd ha).subset fun w hw => ?_
        by_contra hn
        simp only [Function.mem_support, not_not] at hn
        apply hw
        simp [hn]
      pts := hP }
  exact ⟨t⟩

theorem exists_twSec_keyRoot_deep : Hypotheses2 → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, Nonempty (GlobalTheory.FlatTw.TwSec Y.U (xiR D) Z (wtOf (T.Q.Dw j) 0 1)) := by
  intro _ D T hT j hp _ _ hj Y e o hG _ _ Z
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hG.lev.1.2.1 hg0
  exact twSec_keyRoot _ _ _ _ _ _ _ _ _ hG.unf hG.xiAbs hG.geo (le_add_right hp) hg Z

end GlobalTheory.KeyTwDeep
end

