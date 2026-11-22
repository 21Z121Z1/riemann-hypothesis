import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3175
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3178

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidSymmetricBundleDescendsToSubringFinset
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RigSymDescent

theorem axes_sq {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {ψ : G'.left ⟶ G.left} {ψ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hG : IsGrpPullback G' G f ψ)
    (sq : Geo.Tor.IsSquare ψ ψ₂) :
    (lift (1 : G' ⟶ G') (𝟙 G')).left ≫ ψ₂ = ψ ≫ (lift (1 : G ⟶ G) (𝟙 G)).left ∧
    (lift (𝟙 G') (1 : G' ⟶ G')).left ≫ ψ₂ = ψ ≫ (lift (𝟙 G) (1 : G ⟶ G)).left ∧
    (lift (snd G' G') (fst G' G')).left ≫ ψ₂ = ψ₂ ≫ (lift (snd G G) (fst G G)).left := by
  let U : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ψ hG.1.w
  have o₁ : (1 : G' ⟶ G').left ≫ ψ = ψ ≫ (1 : G ⟶ G).left :=
    congrArg (fun q => q.left) ((map_one (pushHom hG G')).trans (MonObj.comp_one U).symm)
  have e : ∀ (x y : G' ⟶ G') (x₀ y₀ : G ⟶ G), x.left ≫ ψ = ψ ≫ x₀.left → y.left ≫ ψ = ψ ≫ y₀.left →
      (lift x y).left ≫ ψ₂ = ψ ≫ (lift x₀ y₀).left := fun x y x₀ y₀ hx hy =>
    (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (G'.hom ≫ f)) (𝟙 G'.left) x y ψ x₀ y₀
      ((Category.id_comp _).trans hx) ((Category.id_comp _).trans hy))
  refine ⟨e _ _ _ _ o₁ (by simp), e _ _ _ _ (by simp) o₁, ?_⟩
  exact (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk ((G' ⊗ G').hom ≫ f))
    (𝟙 (G' ⊗ G').left) _ _ ψ₂ _ _ ((Category.id_comp _).trans sq.2.symm) ((Category.id_comp _).trans sq.1.symm))

end GlobalTheory.RigSymDescent

namespace GlobalTheory

open GlobalTheory.CechPic in

theorem rigSym_descends_to_subring_containing_finset : ∀ (R : Type) [CommRing R] (R₁ : Subring R) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → IsTrivial ((P₁.pull π₂).pull (lift (1 : A₂ ⟶ A₂) (𝟙 A₂)).left) ∧ IsTrivial ((P₁.pull π₂).pull (lift (𝟙 A₂) (1 : A₂ ⟶ A₂)).left) ∧ LBIso (P₁.pull π₂) ((P₁.pull π₂).pull (lift (snd A₂ A₂) (fst A₂ A₂)).left) := by
  intro R _ R₁ A _ P A₁ _ P₁ φ φ₂ hab hP hP₁ hA sq hiso h1 h2 hs
  classical
  have := hab.proper
  haveI : QuasiCompact (A₁ ⊗ A₁).hom := inferInstanceAs (QuasiCompact (pullback.fst A₁.hom A₁.hom ≫ A₁.hom))
  haveI : QuasiSeparated (A₁ ⊗ A₁).hom :=
    inferInstanceAs (QuasiSeparated (pullback.fst A₁.hom A₁.hom ≫ A₁.hom))
  obtain ⟨e₁, e₂, e₃⟩ := GlobalTheory.RigSymDescent.axes_sq hA sq
  have hc : cls P hP = pull φ₂ (cls P₁ hP₁) := (cls_eq_iff hP (pull_isLB hP₁ _)).2 hiso
  have hT := LB.isLB_triv A₁.left
  have z : ∀ {Y : Scheme.{0}} (g : Y ⟶ A₁.left), pull g (cls _ hT) = 0 := fun g => map_zero (pull g)

  have d₁ : LBIso ((P₁.pull (lift (1 : A₁ ⟶ A₁) (𝟙 A₁)).left).pull φ) ((LB.triv A₁.left).pull φ) := by
    refine (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).1 ?_
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp, ← e₁, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 h1
  have d₂ : LBIso ((P₁.pull (lift (𝟙 A₁) (1 : A₁ ⟶ A₁)).left).pull φ) ((LB.triv A₁.left).pull φ) := by
    refine (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).1 ?_
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp, ← e₂, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 h2
  have d₃ : LBIso (P₁.pull φ₂) ((P₁.pull (lift (snd A₁ A₁) (fst A₁ A₁)).left).pull φ₂) := by
    refine (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).1 ?_
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, ← e₃, pull_comp, ← hc,
      ← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hs
  obtain ⟨F₁, H₁⟩ := lbIso_descends_to_subring_containing_finset R R₁ A.left A₁.left A.hom A₁.hom φ _ _ hA.1
    (pull_isLB hP₁ _) hT d₁
  obtain ⟨F₂, H₂⟩ := lbIso_descends_to_subring_containing_finset R R₁ A.left A₁.left A.hom A₁.hom φ _ _ hA.1
    (pull_isLB hP₁ _) hT d₂
  obtain ⟨F₃, H₃⟩ := lbIso_descends_to_subring_containing_finset R R₁ (A ⊗ A).left (A₁ ⊗ A₁).left (A ⊗ A).hom
    (A₁ ⊗ A₁).hom φ₂ _ _ (SiegDesc.isPullback_of_isSquare hA.1 sq) hP₁ (pull_isLB hP₁ _) d₃
  refine ⟨F₁ ∪ F₂ ∪ F₃, fun R₂ h hF A₂ _ π π₂ hB sqB => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.RigSymDescent.axes_sq hB sqB
  have k₁ := H₁ R₂ h hF.1.1 A₂.left A₂.hom π hB.1
  have k₂ := H₂ R₂ h hF.1.2 A₂.left A₂.hom π hB.1
  have k₃ := H₃ R₂ h hF.2 (A₂ ⊗ A₂).left (A₂ ⊗ A₂).hom π₂ (SiegDesc.isPullback_of_isSquare hB.1 sqB)
  refine ⟨(cls_eq_zero_iff (pull_isLB (pull_isLB hP₁ _) _)).1 ?_, (cls_eq_zero_iff (pull_isLB (pull_isLB hP₁ _) _)).1 ?_,
    (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).1 ?_⟩
  · have := (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).2 k₁
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp] at this
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₁]
    exact this
  · have := (cls_eq_iff (pull_isLB (pull_isLB hP₁ _) _) (pull_isLB hT _)).2 k₂
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, cls_pull hT, z, ← pull_comp] at this
    rw [cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₂]
    exact this
  · have := (cls_eq_iff (pull_isLB hP₁ _) (pull_isLB (pull_isLB hP₁ _) _)).2 k₃
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp] at this
    rw [cls_pull hP₁, cls_pull (pull_isLB hP₁ _), cls_pull hP₁, ← pull_comp, f₃]
    exact this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackAddAndPrimeSmulIdStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G H : PDivGroup p R), (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧ rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  first | exact @GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | exact GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | (intros; apply GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFlagIndependent
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem c2F_flag_indep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2), c2F hX σ h fl = c2F hX σ h fl' := by
  intro k _ X _ p D hX σ E h H fl fl'
  have gf : ∀ (f : Vert.Flag E 2) (y z : CxPts p σ), z ∈ ptsIn p σ (frameAt f y).U →
      (h.met σ).gram (frameAt f y).frame z =
        ((h.met σ).G ((frameAt f y).mid (lineSC_shortExact f)) z).submatrix finSumFinEquiv finSumFinEquiv :=
    fun f y z hz => Met.gram_frame (S := lineSC f) (r := 1) (s := 1) (h.met σ) (lineSC_shortExact f) (frameAt f y) hz
  have pf : ∀ (f : Vert.Flag E 2) (y z : CxPts p σ), z ∈ ptsIn p σ (frameAt f y).U →
      ((h.met σ).gram (frameAt f y).frame z).PosDef :=
    fun f y z hz => Met.posDef_gram_frame (S := lineSC f) (r := 1) (s := 1) (h.met σ) (lineSC_shortExact f) (frameAt f y) hz
  have sf : ∀ (f : Vert.Flag E 2) (y : CxPts p σ) (i j : Fin 1 ⊕ Fin 1),
      (hX.atlas σ).SmoothOn (ptsIn p σ (frameAt f y).U) fun z => (h.met σ).gram (frameAt f y).frame z i j :=
    fun f y i j => hX.smoothOn (fun _ hz => Met.IsCInf.gram (H σ) (frameAt f y).frame hz) i j
  let ch : Bool × CxPts p σ → Chart E (1 + 1) := fun a =>
    cond a.1 ((frameAt fl a.2).mid (lineSC_shortExact fl)) ((frameAt fl' a.2).mid (lineSC_shortExact fl'))
  let G : Bool × CxPts p σ → CxPts p σ → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fun a =>
    cond a.1 ((h.met σ).gram (frameAt fl a.2).frame) ((h.met σ).gram (frameAt fl' a.2).frame)
  let U : Bool × CxPts p σ → Set (CxPts p σ) := fun a => ptsIn p σ (ch a).U
  let g : Bool × CxPts p σ → Bool × CxPts p σ → CxPts p σ → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
    fun a b z => ((ch a).tr p σ (ch b) z).submatrix finSumFinEquiv finSumFinEquiv
  have hG : ∀ a, ∀ z ∈ U a, G a z = ((h.met σ).G (ch a) z).submatrix finSumFinEquiv finSumFinEquiv := by
    rintro ⟨b, y⟩ z hz
    cases b
    · exact gf fl' y z hz
    · exact gf fl y z hz
  have hUo : ∀ a, IsOpen (U a) := fun _ => isOpen_ptsIn _
  have hcov : ∀ y, ∃ a, y ∈ U a := fun y => ⟨(true, y), mem_frameAt fl y⟩
  have hholo : ∀ a b i j, (hX.atlas σ).HolOn (U a ∩ U b) fun z => g a b z i j := fun a b i j c =>
    (c.holo ((ch b).U ⊓ (ch a).U) (((ch a).isFrame.basis inf_le_right).repr
      (GlobalTheory.Twist.resM E inf_le_left ((ch b).e (finSumFinEquiv j))) (finSumFinEquiv i))).mono
      fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.2, hv.2.1⟩⟩
  have hsm : ∀ a i j, (hX.atlas σ).SmoothOn (U a) fun z => G a z i j := by
    rintro ⟨b, y⟩ i j
    cases b
    · exact sf fl' y i j
    · exact sf fl y i j
  have hpd : ∀ a, ∀ z ∈ U a, (G a z).PosDef := by
    rintro ⟨b, y⟩ z hz
    cases b
    · exact pf fl' y z hz
    · exact pf fl y z hz
  have htr : ∀ a b, ∀ z ∈ U a ∩ U b, G b z = chg (g a b z) (G a z) := by
    intro a b z hz
    rw [hG a z hz.1, hG b z hz.2, chg_submatrix, ← (h.met σ).trans _ _ z hz.1]
  have key := GlobalTheory.T.chernForms_frame_independent_closed (hX.atlas σ) U hUo hcov g hholo G hsm hpd htr 2
  funext x
  exact key.1 (true, x.pt) (false, x.pt) x (mem_frameAt fl x.pt) (mem_frameAt fl' x.pt)

end GlobalTheory.LineForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernRealClosed
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReal

section Point

open Matrix Filter Topology MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ComplexConjugate ComplexOrder

variable {n : ℕ}

theorem repr_bas_mul (S T U : Finset (Fin (n + n))) : ∃ m : ℤ, (bas n).repr (bas n S * bas n T) U = m ∧
    (m ≠ 0 → Disjoint S T ∧ U = S ∪ T) := by
  by_cases h : Disjoint S T
  · obtain ⟨ε, e⟩ := bas_mul h
    rw [e, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
    by_cases hU : S ∪ T = U
    · exact ⟨ε, by simp [hU], fun _ => ⟨h, hU.symm⟩⟩
    · exact ⟨0, by simp [Finsupp.single_apply, hU], fun h => (h rfl).elim⟩
  · have := ExteriorAlgebra.basis_mul_of_not_disjoint ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv)
      (Set.powersetCard.ofCard (s := S) rfl) (Set.powersetCard.ofCard (s := T) rfl) h
    have e : bas n S * bas n T = 0 := this
    exact ⟨0, by simp [e], fun h => (h rfl).elim⟩

theorem repr_mul (α β : Alt n) (U : Finset (Fin (n + n))) : (bas n).repr (α * β) U =
    ∑ S, ∑ T, (bas n).repr α S * (bas n).repr β T * (bas n).repr (bas n S * bas n T) U := by
  conv_lhs => rw [← (bas n).sum_repr α, ← (bas n).sum_repr β]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_comm

theorem isType_zero (p q : ℕ) : IsType p q (0 : Alt n) := fun S h => (h (by simp)).elim

theorem isType_add {p q : ℕ} {α β : Alt n} (h : IsType p q α) (h' : IsType p q β) : IsType p q (α + β) := fun S hS => by
  by_cases e : (bas n).repr α S = 0
  · exact h' S fun e' => hS (by simp [e, e'])
  · exact h S e

theorem isType_smul {p q : ℕ} {α : Alt n} (c : ℂ) (h : IsType p q α) : IsType p q (c • α) := fun S hS =>
  h S fun e => hS (by simp [e])

theorem isType_mul {p q p' q' : ℕ} {α β : Alt n} (h : IsType p q α) (h' : IsType p' q' β) :
    IsType (p + p') (q + q') (α * β) := fun U hU => by
  rw [repr_mul] at hU
  obtain ⟨S, -, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
  obtain ⟨T, -, hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  obtain ⟨m, e, hm⟩ := repr_bas_mul S T U
  obtain ⟨hd, rfl⟩ := hm fun h0 => hT (by rw [e, h0]; simp)
  obtain ⟨a, b⟩ := h S fun h0 => hT (by rw [h0]; simp)
  obtain ⟨a', b'⟩ := h' T fun h0 => hT (by rw [h0]; simp)
  rw [Finset.filter_union, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd),
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd), a, b, a', b']
  exact ⟨rfl, rfl⟩

theorem isType_dz (a : Fin n) : IsType 1 0 (dz a) := fun S hS => by
  rw [dz, ← bas_singleton] at hS
  obtain rfl : {finSumFinEquiv (.inl a)} = S := by
    by_contra h
    simp [Finsupp.single_apply, h, -finSumFinEquiv_apply_left] at hS
  simp [Finset.filter_singleton]

theorem isType_dzb (a : Fin n) : IsType 0 1 (dzb a) := fun S hS => by
  rw [dzb, ← bas_singleton] at hS
  obtain rfl : {finSumFinEquiv (.inr a)} = S := by
    by_contra h
    simp [Finsupp.single_apply, h, -finSumFinEquiv_apply_right] at hS
  simp [Finset.filter_singleton]

def IsConj (α β : Alt n) : Prop := ∀ S, (bas n).repr β S = conj ((bas n).repr α S)

theorem IsConj.add {α β α' β' : Alt n} (h : IsConj α β) (h' : IsConj α' β') : IsConj (α + α') (β + β') := fun S => by
  simp [h S, h' S]

theorem IsConj.smul {α β : Alt n} (c : ℂ) (h : IsConj α β) : IsConj (c • α) (conj c • β) := fun S => by
  simp [h S]

theorem IsConj.mul {α β α' β' : Alt n} (h : IsConj α β) (h' : IsConj α' β') : IsConj (α * α') (β * β') := fun U => by
  rw [repr_mul, repr_mul, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  obtain ⟨m, e, -⟩ := repr_bas_mul S T U
  rw [e, h S, h' T, map_mul, map_mul, map_intCast]

theorem isConj_bas (T : Finset (Fin (n + n))) : IsConj (bas n T) (bas n T) := fun S => by
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem isConj_sym (x : Fin n × Fin n) : IsConj (sym x : Alt n) (sym x : Alt n) := by
  change IsConj (dz x.1 * dzb x.2) (dz x.1 * dzb x.2)
  rw [dz, dzb, ← bas_singleton, ← bas_singleton]
  exact (isConj_bas _).mul (isConj_bas _)

theorem swap_sym (x : Fin n × Fin n) : swap (sym x.swap : Alt n) = -(sym x : Alt n) := by
  change swap (dz x.2 * dzb x.1) = -(dz x.1 * dzb x.2)
  rw [map_mul, (swap_dz _).1, (swap_dz _).2, dz, dzb]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

def star (n : ℕ) : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ :=
  eval₂Hom (C.comp (starRingEnd ℂ)) fun x => X x.swap

theorem star_C (c : ℂ) : star n (C c) = C (conj c) := by simp [star]

theorem star_X (x : Fin n × Fin n) : star n (X x) = X x.swap := by simp [star]

theorem homog {j : ℕ} {P : MvPolynomial (Fin n × Fin n) ℂ} (hP : P.IsHomogeneous j) :
    IsType j j ((aeval sym P : Ev n) : Alt n) ∧
      IsConj ((aeval sym P : Ev n) : Alt n) ((-1 : ℂ) ^ j • swap ((aeval sym (star n P) : Ev n) : Alt n)) := by
  rw [← mem_homogeneousSubmodule, ← homogeneousSubmodule_one_pow] at hP
  induction hP using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    have h1 := isType_isReal_const (n := n) 1
    rw [Complex.ofReal_one, map_one] at h1
    have h2 : IsConj (1 : Alt n) 1 := by rw [← bas_empty]; exact isConj_bas _
    rw [MvPolynomial.algebraMap_eq, star_C, aeval_C, aeval_C, pow_zero, one_smul, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, Subalgebra.coe_smul, Subalgebra.coe_one, map_smul, map_one]
    exact ⟨isType_smul _ h1.1, h2.smul _⟩
  | add x y i hx hy ihx ihy =>
    simp only [map_add, Subalgebra.coe_add, smul_add]
    exact ⟨isType_add ihx.1 ihy.1, ihx.2.add ihy.2⟩
  | mem_mul m hm i x hx ih =>
    have key : IsType 1 1 ((aeval sym m : Ev n) : Alt n) ∧
        IsConj ((aeval sym m : Ev n) : Alt n) (-swap ((aeval sym (star n m) : Ev n) : Alt n)) := by
      rw [homogeneousSubmodule_one_eq_span_X] at hm
      induction hm using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, rfl⟩ := hz
        rw [star_X, aeval_X, aeval_X, swap_sym, neg_neg]
        exact ⟨isType_mul (isType_dz _) (isType_dzb _), isConj_sym y⟩
      | zero => simpa using ⟨isType_zero 1 1, fun S => by simp⟩
      | add x y _ _ ihx ihy =>
        simp only [map_add, Subalgebra.coe_add, neg_add]
        exact ⟨isType_add ihx.1 ihy.1, ihx.2.add ihy.2⟩
      | smul c x _ ih =>
        rw [← C_mul', map_mul, map_mul, map_mul, star_C, aeval_C, aeval_C, ← Algebra.smul_def, ← Algebra.smul_def,
          Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul, ← smul_neg]
        exact ⟨isType_smul _ ih.1, ih.2.smul _⟩
    simp only [map_mul, Subalgebra.coe_mul]
    refine ⟨by simpa [add_comm] using isType_mul key.1 ih.1, ?_⟩
    have := key.2.mul ih.2
    rwa [mul_smul_comm, neg_mul, smul_neg, ← neg_smul, ← mul_neg_one, ← pow_succ] at this

variable {r : Type} [Fintype r] [DecidableEq r]

theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix r r R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem charpolyRev_conj {R : Type} [CommRing R] (P Q M : Matrix r r R) (hPQ : P * Q = 1) :
    (P * M * Q)ᵀ.charpolyRev = M.charpolyRev := by
  have hPQ' : P.map Polynomial.C * Q.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.charpolyRev, Matrix.charpolyRev]
  have e : (1 : Matrix r r (Polynomial R)) - (Polynomial.X : Polynomial R) • (P * M * Q)ᵀ.map Polynomial.C
      = (P.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * Q.map Polynomial.C)ᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ', Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.map_mul, ← Matrix.map_mul, transpose_sub, transpose_one, transpose_smul, transpose_map]
  rw [e, det_transpose, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hPQ', Matrix.det_one, one_mul]

theorem star_chernPoly {H : V n → Matrix r r ℂ} {v : V n} (h : MContDiffAt 2 H v) (hh : ∀ᶠ x in 𝓝 v, (H x).IsHermitian)
    (hu : IsUnit (H v).det) (j : ℕ) : star n (chernPoly H v j) = chernPoly H v j := by
  have hu' : IsUnit (H v)ᵀ.det := by rwa [det_transpose]
  have hc (ξ η : V n) : (curv H v ξ η)ᴴ = (H v)ᵀ * curv H v η ξ * (H v)ᵀ⁻¹ := by
    rw [← adj_curv h hh hu ξ η, adj]
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu', mul_nonsing_inv _ hu', Matrix.mul_one]
  have hP : (H v)ᵀ.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * ((H v)ᵀ⁻¹).map C = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu', Matrix.map_one _ (map_zero _) (map_one _)]
  have e0 : curvPoly H v = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (curv H v (coordVec a) (coordVec b)).map C := by
    ext i k : 2
    simp [curvPoly, Matrix.sum_apply, mul_comm]
  have e : (-curvPoly H v).map (star n) = ((H v)ᵀ.map C * (-curvPoly H v) * ((H v)ᵀ⁻¹).map C)ᵀ := by
    conv_rhs => rw [e0, Finset.sum_comm]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← Matrix.map_mul, ← hc]
    ext i k : 2
    simp [curvPoly, Matrix.sum_apply, star_C, star_X, mul_comm]
  rw [chernPoly, ← Polynomial.coeff_map, charpolyRev_map, e, charpolyRev_conj _ _ _ hP]

theorem chernAt_isType_isReal {H : V n → Matrix r r ℂ} {v : V n} (h : MContDiffAt 2 H v)
    (hh : ∀ᶠ x in 𝓝 v, (H x).IsHermitian) (hu : IsUnit (H v).det) (j : ℕ) :
    IsType j j (chernAt H v j : Alt n) ∧ IsReal (chernAt H v j : Alt n) := by
  obtain ⟨h1, h2⟩ := homog (ChernCoord.chernPoly_isHomogeneous H v j)
  rw [star_chernPoly h hh hu] at h2
  rw [chernAt, Subalgebra.coe_smul]
  refine ⟨isType_smul _ h1, ?_⟩
  have h3 := h2.smul (kappa ^ j)
  have hk : conj kappa * -1 = kappa := by simp [kappa, neg_div, map_ofNat]
  rw [smul_smul, map_pow, ← mul_pow, hk, ← map_smul] at h3
  exact h3

end Point

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical ComplexOrder

theorem c2F_isRealForm_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).IsRealForm 2 (fld _ (c2F hX σ h fl)) ∧ (hX.atlas σ).del (fld _ (c2F hX σ h fl)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c2F hX σ h fl)) = 0 := by
  intro k _ X _ p D hX σ E h H fl
  have hS := lineSC_shortExact fl
  have hsm (a : VBExt.AdaptedChart (lineSC fl) 1 1) (i j) :
      (hX.atlas σ).SmoothOn (ptsIn p σ a.U) fun y => (h.met σ).gram a.frame y i j :=
    hX.smoothOn (fun _ => (H σ).gram a.frame) i j
  have hpos (a : VBExt.AdaptedChart (lineSC fl) 1 1) (y) (hy : y ∈ ptsIn p σ a.U) :=
    (h.met σ).posDef_gram_frame hS a hy
  have hhol (a b : VBExt.AdaptedChart (lineSC fl) 1 1) (i j) :
      (hX.atlas σ).HolOn (ptsIn p σ a.U ∩ ptsIn p σ b.U) fun y => a.tr p σ hS b y i j :=
    fun c => (c.holo _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.2, hv.2.1⟩⟩
  have htr (a b : VBExt.AdaptedChart (lineSC fl) 1 1) (y) (hy : y ∈ ptsIn p σ a.U ∩ ptsIn p σ b.U) :=
    Met.gram_frame_trans (S := lineSC fl) (r := 1) (s := 1) (h.met σ) hS a b hy.1 hy.2
  have hcov (y : CxPts p σ) : ∃ a : VBExt.AdaptedChart (lineSC fl) 1 1, y ∈ ptsIn p σ a.U := ⟨_, mem_frameAt fl y⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.chernForms_frame_independent_closed (hX.atlas σ) (fun a : VBExt.AdaptedChart (lineSC fl) 1 1 => ptsIn p σ a.U)
    (fun _ => isOpen_ptsIn _) hcov (fun a b => a.tr p σ hS b) hhol
    (fun a => (h.met σ).gram a.frame) hsm hpos htr 2
  obtain ⟨h3, h4, h5⟩ := h2 (fld _ (c2F hX σ h fl)) fun a x hx =>
    congrArg Subtype.val (h1 _ a x (mem_frameAt fl x.pt) hx)
  refine ⟨⟨h3, fun x => ?_⟩, h4, h5⟩
  have hop : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' ptsIn p σ (frameAt fl x.pt).U) :=
    x.ch.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hx : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' ptsIn p σ (frameAt fl x.pt).U :=
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage]; rw [x.ch.left_inv x.2]; exact mem_frameAt fl x.pt⟩
  exact chernAt_isType_isReal (H := fun v => (h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm v))
    (fun i j => ((hsm _ i j x.1.1).contDiffAt (hop.mem_nhds hx)).of_le (by norm_cast))
    (Filter.eventually_of_mem (hop.mem_nhds hx) fun v hv => (hpos _ _ hv.2).isHermitian)
    ((Matrix.isUnit_iff_isUnit_det _).1 (hpos _ _ hx.2).isUnit) 2

end GlobalTheory.ChernReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField), f ∈ P.H a b → ∀ i j, ContinuousOn (ratVal (q := p) (σ := σ) (P.loc a b f i j)) (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) ∧ ∀ (D : ℕ) (c : AlgChart p σ D), DifferentiableOn ℂ (fun v => ratVal (P.loc a b f i j) (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j))) := by
  first | exact @GlobalTheory.HSAmp.loc_continuousOn_holo | exact GlobalTheory.HSAmp.loc_continuousOn_holo | (intros; apply GlobalTheory.HSAmp.loc_continuousOn_holo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameEqLocalFunctionUnitScalarStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ y f = θ * (ratVal (P.loc a b f i j) y * (Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ)) := by
  first | exact @GlobalTheory.HSAmp.val_frame | exact GlobalTheory.HSAmp.val_frame | (intros; apply GlobalTheory.HSAmp.val_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianFieldPointEqEighthPowerUniversalPullbStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_fieldPoint_eq_eighthPower_universal_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (K : Type) [Field K] (t : Sp K ⟶ V.toScheme) (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left), IsGrpPullback B FinalForm.G (t ≫ V.ι) φB → ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧ (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧ (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left → MatEnd pr' a b fB := by
  first | exact @GlobalTheory.Poinc.Eq8.FieldPt.main | exact GlobalTheory.Poinc.Eq8.FieldPt.main | (intros; apply GlobalTheory.Poinc.Eq8.FieldPt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLatticesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianHom_torsionCompatible_periods_lattices : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ E E' : EndU U₁.toUnifPre, LBIso (cubeLB G₁ ![fst G₁ G₁ ≫ E.aG, snd G₁ G₁] U₁.LG.L) (cubeLB G₁ ![fst G₁ G₁, snd G₁ G₁ ≫ E'.aG] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ c, snd A₁.A A₁.A ≫ c] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ E.aA, snd A₁.A A₁.A ≫ 𝟙 A₁.A] A₁.L) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], Key U₁.toUnifPre U₂.toUnifPre c b h F → ∃ φ : D₁.toPre.X →+ D₂.toPre.X, (∀ (y : D₁.toPre.X) (g : GtPtF D₁.toPre F), GtPtF.IsIota y g → ∃ g' : GtPtF D₂.toPre F, Act D₁.toPre D₂.toPre b h g g' ∧ GtPtF.IsIota (φ y) g') ∧ ∀ y, h (φ y) = E.h y := by
  first | exact @GlobalTheory.Mum.Two.periods_of_key | exact GlobalTheory.Mum.Two.periods_of_key | (intros; apply GlobalTheory.Mum.Two.periods_of_key <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullbackGenericallyBirationalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_pullback_generically_birational : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) = 1 → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  first | exact @GlobalTheory.SemiPullBir.semiPos_pull | exact GlobalTheory.SemiPullBir.semiPos_pull | (intros; apply GlobalTheory.SemiPullBir.semiPos_pull <;> assumption)
end

