import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0388
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0384
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0387
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0254
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0381
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0386
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0385
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0001
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BasSingleMulSelf
section
set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm

def holCount {n : ℕ} (S : Finset (Fin (n + n))) : ℕ := (S.filter (·.val < n)).card

def holGe (n p : ℕ) : Submodule ℂ (Alt n) :=
  Submodule.span ℂ (bas n '' {S | p ≤ holCount S})

theorem mem_holGe_iff {n p : ℕ} (β : Alt n) :
    β ∈ holGe n p ↔ ∀ S, (bas n).repr β S ≠ 0 → p ≤ holCount S := by
  rw [holGe, Module.Basis.mem_span_image]
  constructor
  · intro h S hS
    exact h (Finsupp.mem_support_iff.2 hS)
  · intro h S hS
    exact h S (Finsupp.mem_support_iff.1 hS)

theorem holGe_anti {n p q : ℕ} (h : p ≤ q) : holGe n q ≤ holGe n p :=
  Submodule.span_mono (Set.image_mono fun _ hS => le_trans h hS)

theorem bas_mem_holGe {n : ℕ} (S : Finset (Fin (n + n))) : bas n S ∈ holGe n (holCount S) :=
  Submodule.subset_span ⟨S, show holCount S ≤ holCount S from le_refl _, rfl⟩

theorem bas_insert_eq {n : ℕ} {a : Fin (n + n)} {s : Finset (Fin (n + n))} (h : a ∉ s) :
    ∃ ε : ℤˣ, bas n (insert a s) = ε • (bas n {a} * bas n s) := by
  obtain ⟨ε, e⟩ := bas_mul (n := n) (S := {a}) (T := s) (Finset.disjoint_singleton_left.2 h)
  refine ⟨ε, ?_⟩
  rw [e, smul_smul, Int.units_mul_self, one_smul, Finset.insert_eq]

theorem holCount_insert {n : ℕ} {a : Fin (n + n)} {s : Finset (Fin (n + n))} (h : a ∉ s) :
    holCount (insert a s) = holCount s + if a.val < n then 1 else 0 := by
  unfold holCount
  rw [Finset.filter_insert]
  split_ifs with ha
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1)]
  · simp

theorem bas_single_mul_self {n : ℕ} (a : Fin (n + n)) : bas n {a} * bas n {a} = 0 := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective a
  rw [bas_singleton]
  exact ExteriorAlgebra.ι_sq_zero _

theorem bas_single_mul_bas {n : ℕ} (a : Fin (n + n)) (T : Finset (Fin (n + n))) :
    bas n {a} * bas n T ∈ holGe n (holCount T + if a.val < n then 1 else 0) := by
  by_cases h : a ∈ T
  · obtain ⟨ε, e⟩ := bas_insert_eq (Finset.notMem_erase a T)
    rw [Finset.insert_erase h] at e
    rw [e, mul_smul_comm, ← mul_assoc, bas_single_mul_self, zero_mul, smul_zero]
    exact zero_mem _
  · obtain ⟨ε, e⟩ := bas_mul (n := n) (S := {a}) (T := T) (Finset.disjoint_singleton_left.2 h)
    rw [e, ← Finset.insert_eq, ← holCount_insert h, Units.smul_def]
    exact zsmul_mem (bas_mem_holGe _) _

theorem bas_single_mul_mem {n : ℕ} (a : Fin (n + n)) {q : ℕ} {y : Alt n} (hy : y ∈ holGe n q) :
    bas n {a} * y ∈ holGe n (q + if a.val < n then 1 else 0) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    exact holGe_anti (Nat.add_le_add_right hT _) (bas_single_mul_bas a T)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

theorem pull_bas_mem {n m : ℕ} (L : V n →L[ℂ] V m) (S : Finset (Fin (m + m))) :
    pull L (bas m S) ∈ holGe n (holCount S) := by
  induction S using Finset.induction_on with
  | empty =>
    have h0 : holCount (∅ : Finset (Fin (m + m))) = 0 := by simp [holCount]
    rw [bas_empty, map_one, h0, ← bas_empty]
    exact holGe_anti (Nat.zero_le _) (bas_mem_holGe _)
  | insert a s ha ih =>
    obtain ⟨ε, e⟩ := bas_insert_eq ha
    rw [e, holCount_insert ha, Units.smul_def, map_zsmul, map_mul]
    refine zsmul_mem ?_ _
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective a
    rw [bas_singleton]
    rcases i with i | i
    · have hi : (finSumFinEquiv (Sum.inl i : Fin m ⊕ Fin m)).val < m := by simp
      rw [if_pos hi, show ExteriorAlgebra.ι ℂ (Pi.single (Sum.inl i) 1) = dz (n := m) i from rfl, (pull_dz L i).1,
        Finset.sum_mul]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ _ ?_
      have hb : (finSumFinEquiv (Sum.inl b : Fin n ⊕ Fin n)).val < n := by simp
      have := bas_single_mul_mem (finSumFinEquiv (Sum.inl b)) ih
      rwa [if_pos hb, bas_singleton] at this
    · have hi : ¬ (finSumFinEquiv (Sum.inr i : Fin m ⊕ Fin m)).val < m := by simp
      rw [if_neg hi, show ExteriorAlgebra.ι ℂ (Pi.single (Sum.inr i) 1) = dzb (n := m) i from rfl, (pull_dz L i).2,
        Finset.sum_mul]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ _ ?_
      have hb : ¬ (finSumFinEquiv (Sum.inr b : Fin n ⊕ Fin n)).val < n := by simp
      have := bas_single_mul_mem (finSumFinEquiv (Sum.inr b)) ih
      rwa [if_neg hb, bas_singleton] at this

theorem pull_mem_holGe {n m : ℕ} (L : V n →L[ℂ] V m) {p : ℕ} {β : Alt m} (h : β ∈ holGe m p) :
    pull L β ∈ holGe n p := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    exact holGe_anti hS (pull_bas_mem L S)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

end GlobalTheory.CxForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulMat
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut.SsTwist

open Polynomial

theorem charpoly_smul_end {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {c : ℂ} (hc : c ≠ 0) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  generalize LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f = M
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpTwist (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (g : Weil h) :
    (x.lpTwist ξ hξ).charPol g = (x.charPol g).scaleRoots (ξ g : ℂ) := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ, charpoly_smul_end _ (Units.ne_zero _)]

theorem scaleRoots_cancel {p q : ℂ[X]} {c : ℂ} (hc : c ≠ 0) (H : p.scaleRoots c = q.scaleRoots c) : p = q := by
  have := congrArg (fun P : ℂ[X] => P.scaleRoots c⁻¹) H
  simpa only [← scaleRoots_mul, mul_inv_cancel₀ hc, scaleRoots_one] using this

end GlobalTheory.GalCut.SsTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwOfContinuous
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut

theorem exists_place_dvd_prime {K : Type} [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have hP : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(l : ℤ)}) ⊥
    (by
      intro x hx
      have : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (by simpa using hx)
      simp [this])
  have hmem : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self _
    simpa using this
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((l : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    have : ((l : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hl.out.ne_zero
    exact this h0
  exact ⟨⟨Q, hQ, hne⟩, hmem⟩

theorem continuous_tw_of_continuous {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {k : Type} [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} {r : Γ →* GL (Fin n) k} {μ : Γ →* kˣ} (hr : Continuous r) (hμ : Continuous μ) :
    Continuous (UpperTheory.V.Af.tw r μ) := by
  have h1 : Continuous fun s => (UpperTheory.V.Af.tw r μ s).val := by
    simp only [UpperTheory.V.Af.tw_val]
    exact (Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  simp only [← map_inv]
  exact h1.comp continuous_inv

theorem ex_good_of_ex_csd : AutomorphicFormsFiniteGL → Ex .csd → Ex .good := by
  intro hA hcsd E Ω _ _ _ _ _ _ l _ ι a ha π χ hs
  obtain ⟨w₀, hw₀⟩ := exists_place_dvd_prime (K := E) l
  have hsplit : GlobalTheory.UnitaryBC.IsSplitAt w₀ := by
    by_contra h
    exact (hs.2.2.2.2 w₀ h).1 hw₀
  obtain ⟨κ, m, hκ, -, hs'⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hA E l a ha π χ hs w₀ hsplit
  obtain ⟨r', hr'c, hr'⟩ := hcsd E Ω l ι a ha (π.twist κ) _ hs'
  have hκi : (κ⁻¹).IsAlg (-m) := fun k => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hκ k, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  obtain ⟨art, hart, hμ⟩ := (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hμ l ι κ⁻¹ (-m) (isAlgPos_of_isAlg hκi)
  refine ⟨UpperTheory.V.Af.tw r' μ, continuous_tw_of_continuous hr'c hμc, ?_⟩
  have h := UpperTheory.V.Af.Cq.attTwist E Ω l ι a r' (π.twist κ) hr' art κ⁻¹ (-m) μ hart hμ
  rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GalCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineAllOfGoodStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_all_of_good : Inputs → SphericalLevelCondition .good .crys → SphericalLevelCondition .all .crys := by
  first | (exact @GlobalTheory.RoadU.holdsS_all_crys) | (exact GlobalTheory.RoadU.holdsS_all_crys) | (intros; apply GlobalTheory.RoadU.holdsS_all_crys  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExAllOfGood
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.RoadU

open UpperTheory.V.Af in

theorem frobEig_of_dec {E Ω : Type} [Field E] [NumberField E]
    [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (π : CuspSub E a) (Q : GlobalTheory.RealGal.QCM E Ω) (P : CuspSub ↥Q.K a) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l))
    (ρ : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hdec : ∀ A : ValuationSubring Ω, IsPlaceOver A w → Dec (F := E) A ≤ (Bc.res E Ω ↥Q.K).range)
    (hsph : ∀ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w → (CG.mk P).HasSat w' B → SphAt .unr P ι r w' B)
    (hP : IsLift π P) (hB : (CG.mk π).HasSat w B) (hiso : RepIso r (ρ.comp (Bc.res E Ω ↥Q.K)))
    (hunr : ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, ρ s = 1) :
    FrobEig ι ρ w (algSat a (normV w) B) := by
  intro A hA
  refine ⟨hunr A hA, fun σ hσ => ?_⟩
  obtain ⟨w', hw', hA', hq⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA (hdec A hA)
  obtain ⟨τ, rfl⟩ := hdec A hA hσ.1
  have hτ : IsFrob (F := ↥Q.K) A (normV w') τ := by
    rw [hq]
    exact ⟨hσ.1, hσ.2⟩
  have hl' : ((l : ℕ) : 𝓞 ↥Q.K) ∉ w'.asIdeal := by
    intro h
    apply hl
    rw [← hw']
    change ((l : ℕ) : 𝓞 E) ∈ Ideal.comap (algebraMap (𝓞 E) (𝓞 ↥Q.K)) w'.asIdeal
    simpa using h
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hw', hq]) (by rw [hw']; exact hB)
    simpa using this
  have key := ((hsph w' hw' hB' hl') A hA').2 τ hτ
  obtain ⟨g, hg⟩ := hiso
  have e : ρ (Bc.res E Ω ↥Q.K τ)⁻¹ = g * r τ⁻¹ * g⁻¹ := by
    rw [← map_inv]
    exact hg τ⁻¹
  rw [e, ← hq, ← key, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

open UpperTheory.V.Af in

theorem ex_all_of_good : Inputs → Ex .good → SphericalLevelCondition .good .unr → Ex .all := by
  intro hIn hEx hHolds E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc
  have hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL := GlobalTheory.automorphicFormsFiniteGL
  have hQL : QuadLift := GlobalTheory.QuadLiftBridge.quadLift hIn.ac hIn.js
  obtain ⟨hreg, hpol, -⟩ := hsc
  let S : Set (GlobalTheory.RealGal.QCM E Ω) := {Q | ∃ P : CuspSub ↥Q.K a, IsLift π P ∧ Good l P}
  have fam := GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π
  have famS : ∀ (Q : GlobalTheory.RealGal.QCM E Ω),
      (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) →
      (∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P) → Q ∈ S := by
    intro Q hram hgood
    obtain ⟨P, hP⟩ := hQL E ↥Q.K Q.two a ha π hram
    exact ⟨P, hP, hgood P hP⟩
  obtain ⟨v0⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩⟩
  have hS : S.Infinite := (fam v0).mono fun Q hQ => famS Q hQ.2.2.1 hQ.2.2.2
  choose P hP using fun Q : ↥S => Q.2
  have key : ∀ Q : ↥S, ∃ (χ' : HChar (maximalRealSubfield ↥Q.1.K)) (r : G ↥Q.1.K Ω →* GL (Fin a) (Qbar l)),
      InScope .good l (P Q) χ' ∧ Weak (P Q) ι r := fun Q => by
    obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hIn.js hIn.gk E ↥Q.1.K l a ha π χ (P Q) (hP Q).1 ⟨hreg, hpol, trivial⟩
    have hs : InScope .good l (P Q) χ' := ⟨hχ'.1, hχ'.2.1, (hP Q).2⟩
    obtain ⟨r, hr⟩ := hEx ↥Q.1.K Ω l ι a ha (P Q) χ' hs
    exact ⟨χ', r, hs, hr⟩
  choose χ' r hχ' hr using key
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.CMBasePatch.main hAF E Ω l ι a π S hS P r fun Q => ⟨(hP Q).1, hr Q⟩
  refine ⟨ρ, hρc, hρs, ?_⟩
  haveI : Infinite ↥S := hS.to_subtype
  obtain ⟨Q0, hQ0⟩ := hev.exists
  have hunr := GlobalTheory.RealGal.ConjUnr.unr_of_conj_res E Ω Q0.1 l a ρ (r Q0) hQ0 ((hr Q0).2.2.mono fun w' hw' A hA => by
    obtain ⟨B, -, hF⟩ := hw'
    exact (hF A hA).1)
  have hlf : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hsat := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hAF E a π
  have hpick : ∀ w : HeightOneSpectrum (𝓞 E), ∃ Q : ↥S,
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → Dec (F := E) A ≤ (Bc.res E Ω ↥Q.1.K).range) ∧
      (∀ w' : HeightOneSpectrum (𝓞 ↥Q.1.K), w'.under (𝓞 E) = w → GlobalTheory.UnitaryBC.IsSplitAt w') ∧
      RepIso (r Q) (ρ.comp (Bc.res E Ω ↥Q.1.K)) := by
    intro w
    have hfin := (Filter.eventually_cofinite.1 hev).image Subtype.val
    obtain ⟨Q, hQ, hQn⟩ := ((fam w).diff hfin).nonempty
    have hQS : Q ∈ S := famS Q hQ.2.2.1 hQ.2.2.2
    refine ⟨⟨Q, hQS⟩, hQ.1, hQ.2.1, ?_⟩
    by_contra hc
    exact hQn ⟨⟨Q, hQS⟩, hc, rfl⟩
  filter_upwards [hlf, hsat, hunr] with w hl hB hu
  obtain ⟨B, hB⟩ := hB
  refine ⟨B, hB, ?_⟩
  obtain ⟨Q, hdec, hsplit, hiso⟩ := hpick w
  exact frobEig_of_dec ι π Q.1 (P Q) (r Q) ρ w B hl hdec
    (fun w' hw' hB' => hHolds ↥Q.1.K Ω l ι a ha (P Q) (χ' Q) (hχ' Q) (r Q) (hr Q) w' (hsplit w' hw') B hB')
    (hP Q).1 hB hiso hu

end GlobalTheory.RoadU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusAllOfGood
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiDescent

theorem wdRel_trivWD {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (a : ℕ) :
    WDRel φ (trivWD h a) (trivWD h' a) := by
  refine ⟨a, WDRep.diag h fun _ : Fin a => 1, WDRep.diag h' fun _ : Fin a => 1, rfl, rfl, ?_, ?_⟩
  · rfl
  · intro σ σ' _
    ext v i
    simp [WDRep.diag, WDRep.ofChars, GlobalTheory.WeilDeligne.unrChar]

theorem charPol_eq {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (hy : WDRel φ y y') {σ : Weil h} {σ' : Weil h'} (hs : WeilRel φ σ σ') :
    y.charPol σ = y'.charPol σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := hy
  rw [WD.charPol_mk, WD.charPol_mk, hb σ σ' hs]

end GlobalTheory.RoadU.PhiDescent

open GlobalTheory.RoadU.PhiDescent in

theorem GlobalTheory.RoadU.holdsS_all_phi : Inputs → SphericalLevelCondition .good .crys → SphericalLevelCondition .good .phi → SphericalLevelCondition .all .phi := by
  intro hIn _ hgood E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc r hr w _ B hB Pr AI hT A h O _ _ _ Bw hj g
  have hF := GlobalTheory.automorphicFormsFiniteGL
  have hQ := GlobalTheory.QuadLiftBridge.quadLift hIn.ac hIn.js
  obtain ⟨Q, hQdec, hQsplit, hQram, hQgood⟩ := (GlobalTheory.T.infinite_quadraticCM_goodBaseChange_split hF E Ω l a π w).nonempty
  obtain ⟨P, hP⟩ := hQ E Q.K Q.two a ha π hQram
  obtain ⟨⟨χ', hsc'⟩, -⟩ := GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight hF hIn.js hIn.gk E Q.K l a ha π χ P hP hsc.all
  have hsc'' : InScope .good l P χ' := ⟨hsc'.1, hsc'.2.1, hQgood P hP⟩
  have hr' := GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict E Q.K Ω l ι a π P hP r hr
  have hdec := hQdec A h
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A h hdec
  have hunder : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver h h'
    ext1
    exact this.over.symm
  obtain ⟨c, hc, hdegc, hq, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  obtain ⟨S, hS, -, -, -, -, hTw, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hunder, hq]) (by rw [hunder]; exact hB)
    simpa using this
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  have hrel : WDRel (RingEquiv.refl Ω) (wdAt Pr ι Bw h hj (r.comp (Dec (F := E) A).subtype))
      (wdAt Pr ι Bw' h' hj' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype)) := by
    by_cases hp : IsPstAt Pr Bw (r.comp (Dec (F := E) A).subtype)
    · exact GlobalTheory.RealGal.wdRelRes_gen E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r hp ι w w' h h' hj hj' i hi
    · have hp' : ¬ IsPstAt Pr Bw' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype) :=
        fun H => hp (D.2.2.2.1 H)
      rw [wdAt_of_not_isPstAt _ _ _ _ hp, wdAt_of_not_isPstAt _ _ _ _ hp']
      exact wdRel_trivWD h h' _ a
  have hsat : WDRel (RingEquiv.refl Ω) (satWD h a B) (satWD h' a B) := by
    have h0 := GlobalTheory.RSGam.Transport.wdRel_lpUnr c hc hdegc (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))
    unfold satWD
    rw [hS, hTw, (hS _ _).mp h0]
  have hgc : WeilRel (RingEquiv.refl Ω) g (c g) := (hc g (c g)).2 rfl
  have hcl := hgood Q.K Ω l ι a ha P χ' hsc'' _ hr' w' (hQsplit w' hunder) B hB' Pr AI hT A h' O Bw' hj' (c g)
  rw [charPol_eq hrel hgc, charPol_eq hsat hgc]
  exact hcl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesPositiveSteps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV.StepDel

theorem del_of_pos : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j, 1 ≤ j → j < D.R.m → S.Del j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP hPo hL j _ hj
  exact GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m S hD hP hPo hL j hj

end GlobalTheory.TwV.StepDel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedGoodOfSelfDualStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_good_of_self_dual : Inputs → SphericalLevelCondition .csd .unr → SphericalLevelCondition .good .unr := by
  first | (exact @GlobalTheory.RoadU.holdsS_good_unr) | (exact GlobalTheory.RoadU.holdsS_good_unr) | (intros; apply GlobalTheory.RoadU.holdsS_good_unr  <;> assumption)
end

