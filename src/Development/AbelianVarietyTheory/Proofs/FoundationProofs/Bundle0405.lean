import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0398
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0402
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimplePotentialsAtNewformEigensystem
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.SSPotBr

def opZ (N l w : ℕ) : Letter → Module.End ℂ (GlobalTheory.HeckeFamilyMatrices.Lev N l → Polynomial ℂ)
  | Letter.T q => GlobalTheory.HeckeFamilyMatrices.TqZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w q (sgD N l q)
  | Letter.U => GlobalTheory.HeckeFamilyMatrices.UlZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w l
  | Letter.D d => GlobalTheory.HeckeFamilyMatrices.DdZ (GlobalTheory.HeckeFamilyMatrices.Lev N l) w (sgD N l d)

section
open GlobalTheory.HeckeFamilyMatrices Polynomial

theorem eichlerShimuraCoboundaries_le_eichlerShimuraCocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : B1 Γ w ≤ Z1 Γ w := by
  rintro z ⟨⟨p, hp⟩, rfl⟩
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · exact Submodule.sub_mem _ (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) 1 p hp).1 hp
  · change GlobalTheory.HeckeFamilyMatrices.slP w (mat (γ * δ : Γ)) p - p = GlobalTheory.HeckeFamilyMatrices.slP w (mat δ) (GlobalTheory.HeckeFamilyMatrices.slP w (mat γ) p - p) + (GlobalTheory.HeckeFamilyMatrices.slP w (mat δ) p - p)
    have e : mat (γ * δ : Γ) = mat γ * mat δ := by
      simp only [mat, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [e, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) (mat δ) p hp).2.1, map_sub]
    abel

end

theorem letter_pot (N l w : ℕ) (hN : 5 ≤ N) (hl : l.Prime) (hlN : ¬ l ∣ N) (T : Letter) (hT : admitted N l T) :
    ∀ F ∈ Pot ℂ w (Gam N l), opL ℂ N l T F ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (opL ℂ N l T F) = opZ N l w T (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro F hF
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨hsg, hTq, hU, hD⟩ := GlobalTheory.T.chosenDiamondMatrix_letterOperators_cosetSums N l hN0 hl hlN
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.T.heckeDoubleCosetReps_gammaOneGammaZeroLevel N l hN hl hlN
  cases T with
  | T q =>
    obtain ⟨hq, hqN⟩ := hT
    have hcop : Nat.Coprime q N := (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right l)
    rw [hTq q, LinearMap.sum_apply]
    exact GlobalTheory.T.heckeSum_potentials_cocycle_eq N l w (GlobalTheory.HeckeFamilyMatrices.dg 1 q) _ _ hN0 hl0
      (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hq.pos) (rT q _ hq hqN (hsg q hcop)) F hF
  | U =>
    rw [hU, LinearMap.sum_apply]
    exact GlobalTheory.T.heckeSum_potentials_cocycle_eq N l w (GlobalTheory.HeckeFamilyMatrices.dg 1 l) _ _ hN0 hl0
      (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hl.pos) rU F hF
  | D d =>
    rw [hD d, LinearMap.sum_apply]
    exact GlobalTheory.T.heckeSum_potentials_cocycle_eq N l w (GlobalTheory.HeckeFamilyMatrices.mat (sgD N l d)) _ _ hN0 hl0 (by simp) (rD _ _ (hsg d hT)) F hF

theorem lift_pot (N l w : ℕ) (hN : 5 ≤ N) (hl : l.Prime) (hlN : ¬ l ∣ N) {P : FreeAlgebra ℂ Letter}
    (hP : P ∈ admissibleLettersSubalgebra ℂ N l) :
    ∀ F ∈ Pot ℂ w (Gam N l), FreeAlgebra.lift ℂ (opL ℂ N l) P F ∈ Pot ℂ w (Gam N l) ∧
      cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (FreeAlgebra.lift ℂ (opL ℂ N l) P F) =
        FreeAlgebra.lift ℂ (opZ N l w) P (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  have hN0 : 0 < N := by omega
  obtain ⟨-, hadd, hsmul⟩ := GlobalTheory.T.potentialCocycleDehomogenised_laws w N l hN0 hl.pos
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨T, hT, rfl⟩ := hy
    intro F hF
    simp only [FreeAlgebra.lift_ι_apply]
    exact letter_pot N l w hN hl hlN T hT F hF
  | algebraMap r =>
    intro F hF
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    exact ⟨(Betti.potSub ℂ w (Gam N l)).smul_mem r hF, hsmul r F⟩
  | add x y _ _ hx hy =>
    intro F hF
    obtain ⟨h1, h2⟩ := hx F hF
    obtain ⟨h3, h4⟩ := hy F hF
    simp only [map_add, LinearMap.add_apply]
    exact ⟨(Betti.potSub ℂ w (Gam N l)).add_mem h1 h3, by rw [hadd, h2, h4]⟩
  | mul x y _ _ hx hy =>
    intro F hF
    obtain ⟨h1, h2⟩ := hy F hF
    obtain ⟨h3, h4⟩ := hx _ h1
    simp only [map_mul, Module.End.mul_apply]
    exact ⟨h3, by rw [h4, h2]⟩

end GlobalTheory.KZ.SSPotBr

namespace GlobalTheory.KZ.SSPotBr

theorem ssPotB_at_newform : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) (hN : g.M ∣ N), 5 ≤ N → l.Prime → ¬ l ∣ N →
    Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 →
    α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) →
    ∀ lam : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam (Letter.T q) = g.a q) → lam Letter.U = α →
    (∀ d : ℕ, Nat.Coprime d N → lam (Letter.D d) = g.χ (d : ZMod g.M)) → SSPotB N l (k - 2) lam := by
  intro k g N l hN hN5 hl hlN hk hk3 α hα h1 h2 lam hlT hlU hlD
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hsg, -, -, -⟩ := GlobalTheory.T.chosenDiamondMatrix_letterOperators_cosetSums N l hN0 hl hlN
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.T.heckeDoubleCosetReps_gammaOneGammaZeroLevel N l hN5 hl hlN
  have hcopq : ∀ q, q.Prime → ¬ q ∣ N * l → Nat.Coprime q N := fun q hq hqN =>
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqN (h.mul_right l)

  obtain ⟨q0, hq0le, hq0⟩ := Nat.exists_infinite_primes (N * l + 1)
  have hq0N : ¬ q0 ∣ N * l := fun h => by
    have := Nat.le_of_dvd (Nat.mul_pos hN0 hl0) h; omega

  have hpres : ∀ t, admitted N l t →
      (∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), opZ N l (k - 2) t z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) ∧
      (∀ z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), opZ N l (k - 2) t z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) := by
    intro t ht
    cases t with
    | T q =>
      obtain ⟨hq, hqN⟩ := ht
      obtain ⟨a, b, -⟩ := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _
        (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hq.pos) (rT q _ hq hqN (hsg q (hcopq q hq hqN)))
      exact ⟨a, b⟩
    | U =>
      obtain ⟨a, b, -⟩ := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _
        (by simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two_of]; exact_mod_cast hl.pos) rU
      exact ⟨a, b⟩
    | D d =>
      obtain ⟨a, b, -⟩ := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) _ _ _ (by simp) (rD _ _ (hsg d ht))
      exact ⟨a, b⟩

  have comm := fun (q q' d d' : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N * l) (hq' : q'.Prime) (hq'N : ¬ q' ∣ N * l)
      (hd : Nat.Coprime d N) (hd' : Nat.Coprime d' N) =>
    GlobalTheory.T.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0 N l k hN5 hl hlN hk3 hk q q' (sgD N l q) (sgD N l q') (sgD N l d) (sgD N l d') (d : ZMod N)
      (d' : ZMod N) hq hqN hq' hq'N (hsg q (hcopq q hq hqN)) (hsg q' (hcopq q' hq' hq'N)) (hsg d hd) (hsg d' hd')
  have h1N : Nat.Coprime 1 N := Nat.coprime_one_left N
  have hcomm : ∀ t t', admitted N l t → admitted N l t' → ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2),
      opZ N l (k - 2) t (opZ N l (k - 2) t' z) - opZ N l (k - 2) t' (opZ N l (k - 2) t z) ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro t t' ht ht' z hz
    cases t with
    | T q =>
      cases t' with
      | T q' => exact (comm q q' 1 1 ht.1 ht.2 ht'.1 ht'.2 h1N h1N z hz).1
      | U => exact (comm q q 1 1 ht.1 ht.2 ht.1 ht.2 h1N h1N z hz).2.1
      | D d => exact (comm q q d 1 ht.1 ht.2 ht.1 ht.2 ht' h1N z hz).2.2.1
    | U =>
      cases t' with
      | T q' =>
        have := (comm q' q' 1 1 ht'.1 ht'.2 ht'.1 ht'.2 h1N h1N z hz).2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | U => rw [sub_self]; exact Submodule.zero_mem _
      | D d => exact (comm q0 q0 d 1 hq0 hq0N hq0 hq0N ht' h1N z hz).2.2.2.1
    | D d =>
      cases t' with
      | T q' =>
        have := (comm q' q' d 1 ht'.1 ht'.2 ht'.1 ht'.2 ht h1N z hz).2.2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | U =>
        have := (comm q0 q0 d 1 hq0 hq0N hq0 hq0N ht h1N z hz).2.2.2.1
        rw [← neg_sub]; exact Submodule.neg_mem _ this
      | D d' => exact (comm q0 q0 d d' hq0 hq0N hq0 hq0N ht ht' z hz).2.2.2.2

  have key : ∀ e : (ZMod N)ˣ → ℕ, (∀ u, Nat.Coprime (e u) N) → (∀ u, ((e u : ℕ) : ZMod N) = u) →
      ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), ∀ n : ℕ, (∀ t, admitted N l t →
        ((opZ N l (k - 2) t - lam t • 1) ^ n) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) →
      (∀ q, q.Prime → ¬ q ∣ N * l → (opZ N l (k - 2) (Letter.T q) - lam (Letter.T q) • 1) z ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) ∧
      (opZ N l (k - 2) Letter.U - lam Letter.U • 1) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) ∧
      ∀ u d, e u = d → (opZ N l (k - 2) (Letter.D d) - lam (Letter.D d) • 1) z ∈
        GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro e he1 he2 z hz n hgen
    have hσD : ∀ u : (ZMod N)ˣ, GlobalTheory.HeckeFamilyMatrices.IsDiam N l (u : ZMod N) (sgD N l (e u)) := fun u => by
      have := hsg (e u) (he1 u); rwa [he2 u] at this
    have hchi : ∀ u : (ZMod N)ˣ, lam (Letter.D (e u)) = g.χ (ZMod.castHom hN (ZMod g.M) (u : ZMod N)) := fun u => by
      rw [hlD _ (he1 u), ← he2 u, map_natCast (ZMod.castHom hN (ZMod g.M))]
    obtain ⟨cT, cU, cD⟩ := GlobalTheory.T.hecke_semisimple_generalised_eigen_newform_gamma1Gamma0 k g N l hN hN5 hl hlN hk hk3 α hα h1 h2 (fun q => sgD N l q)
      (fun u => sgD N l (e u)) (fun q hq hqN => hsg q (hcopq q hq hqN)) hσD z hz n
      (fun q hq hqN => by have h := hgen (Letter.T q) ⟨hq, hqN⟩; rw [hlT q hq hqN] at h; exact h)
      (by have h := hgen Letter.U trivial; rw [hlU] at h; exact h)
      (fun u => by have h := hgen (Letter.D (e u)) (he1 u); rw [hchi u] at h; exact h)
    refine ⟨fun q hq hqN => ?_, ?_, ?_⟩
    · rw [hlT q hq hqN]; exact cT q hq hqN
    · rw [hlU]; exact cU
    · rintro u d rfl
      rw [hchi u]; exact cD u
  have hval1 : ∀ u : (ZMod N)ˣ, Nat.Coprime (u : ZMod N).val N := fun u => ZMod.val_coe_unit_coprime u
  have hval2 : ∀ u : (ZMod N)ˣ, (((u : ZMod N).val : ℕ) : ZMod N) = u := fun u => ZMod.natCast_zmod_val _
  have heig : ∀ z ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2), ∀ n : ℕ, (∀ t, admitted N l t →
        ((opZ N l (k - 2) t - lam t • 1) ^ n) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) →
      ∀ t, admitted N l t → (opZ N l (k - 2) t - lam t • 1) z ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2) := by
    intro z hz n hgen t ht
    cases t with
    | T q => exact (key (fun u => (u : ZMod N).val) hval1 hval2 z hz n hgen).1 q ht.1 ht.2
    | U => exact (key (fun u => (u : ZMod N).val) hval1 hval2 z hz n hgen).2.1
    | D d =>
      have hd : Nat.Coprime d N := ht
      refine (key (fun u => if (u : ZMod N) = (d : ZMod N) then d else (u : ZMod N).val) ?_ ?_ z hz n hgen).2.2
        (ZMod.unitOfCoprime d hd) d (if_pos (ZMod.coe_unitOfCoprime d hd))
      · intro u; split_ifs
        · exact hd
        · exact hval1 u
      · intro u; split_ifs with h
        · exact h.symm
        · exact hval2 u
  obtain ⟨P, hP, hP1, hPz⟩ := GlobalTheory.T.exists_joint_genEigenspace_idempotent_poly ℂ (GlobalTheory.HeckeFamilyMatrices.Lev N l → Polynomial ℂ) (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2))
    (GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) (k - 2)) Letter (admitted N l) (opZ N l (k - 2)) lam (eichlerShimuraCoboundaries_le_eichlerShimuraCocycles _ _)
    (GlobalTheory.T.eichlerShimuraCocycles_gammaOneGammaZero_finiteDimensional N l (k - 2) hN0 hl0) (fun t ht => (hpres t ht).1) (fun t ht => (hpres t ht).2) hcomm heig
  refine ⟨P, hP, hP1, fun F hF T hT => ?_⟩
  obtain ⟨hD1, hD2, hD3⟩ := GlobalTheory.T.potentialCocycleDehomogenised_laws (k - 2) N l hN0 hl0
  obtain ⟨hPF, hcPF⟩ := lift_pot N l (k - 2) hN5 hl hlN hP F hF
  obtain ⟨hTF, hcTF⟩ := letter_pot N l (k - 2) hN5 hl hlN T hT _ hPF
  have hG : (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) = opL ℂ N l T (FreeAlgebra.lift ℂ (opL ℂ N l) P F) +
        (-lam T) • FreeAlgebra.lift ℂ (opL ℂ N l) P F := by
    simp [sub_eq_add_neg, neg_smul]
  have hGpot : opL ℂ N l T (FreeAlgebra.lift ℂ (opL ℂ N l) P F) + (-lam T) • FreeAlgebra.lift ℂ (opL ℂ N l) P F ∈
      Pot ℂ (k - 2) (Gam N l) :=
    (Betti.potSub ℂ (k - 2) (Gam N l)).add_mem hTF ((Betti.potSub ℂ (k - 2) (Gam N l)).smul_mem _ hPF)
  rw [hG]
  refine (hD1 _ hGpot).2.2 ?_
  rw [hD2, hD3, hcTF, hcPF]
  have := hPz (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) (hD1 F hF).1 T hT
  simpa [sub_eq_add_neg, neg_smul] using this

end GlobalTheory.KZ.SSPotBr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShiftedCocycleLimitIntegralStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_cocycle_limit_integral : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc (mat W) (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ ∃ v : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, y s = mat W s *ᵥ v - v := by
  first | exact @GlobalTheory.InertCoh.unr_of_limit_spec | exact GlobalTheory.InertCoh.unr_of_limit_spec | (intros; apply GlobalTheory.InertCoh.unr_of_limit_spec ; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorUpperULCommuteScaleOne
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThHeckeU

theorem eval_kmap {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (σ : X.K ≃+* X.K) (x : X.Khat l) (f : X.Kˣ)
    (h : AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l σ x) = X.cls l n (Units.map σ.toMonoidHom f) := by
  rw [AdicCompletion.eval_apply]
  change (AdicCompletion.map _ _ x).val n = _
  rw [AdicCompletion.map_val_apply, ← AdicCompletion.eval_apply, h]
  rw [Tower.cls, Tower.cls, LinearMap.reduceModIdeal_apply, LinearMap.baseChange_tmul]
  rfl

theorem cls_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (f g : X.Kˣ) : X.cls l n (f * g) = X.cls l n f + X.cls l n g := by
  simp only [Tower.cls, ← Submodule.Quotient.mk_add, ← TensorProduct.tmul_add]
  rfl

theorem eval_sum_kmap {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (s : Finset ℕ) (σ : ℕ → (X.K ≃+* X.K)) (x : X.Khat l) (f : X.Kˣ)
    (h : AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (∑ j ∈ s, X.kmap l (σ j) x) =
      X.cls l n (∏ j ∈ s, Units.map (σ j).toMonoidHom f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, map_zero, Finset.prod_empty]
    simp [Tower.cls]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, map_add, ih, cls_mul, eval_kmap X l n _ x f h]

theorem isThB_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω)
    (N l : ℕ) [Fact l.Prime] (b : X.Fn l) (ψ : HahnSeries ℚ Ω) (hψ : ∀ r, ψ.coeff r ∈ A) : IsThB X A N l 0 b ψ := by
  have hprim : Prim A (X.exp 1) := by
    rw [map_one]
    refine ⟨fun r => ?_, 0, by simp, by simp⟩
    by_cases h : r = 0
    · subst h; simp
    · simp [HahnSeries.coeff_one, h]
  refine ⟨1, fun γ _ => by simp, ?_, fun δ _ _ => ⟨1, fun γ _ => by simp, by simp⟩, hψ, 1, 1, 1, one_ne_zero, by simp,
    hprim, hprim, fun r => ⟨(ψ * X.exp 1 * X.exp 1).coeff r -
      (theta 1 (X.exp 1) * X.exp 1 - X.exp 1 * theta 1 (X.exp 1)).coeff r, ?_, by simp⟩⟩
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) 0 (b ![1, 0]))
    rw [← hy, Tower.cls, Submodule.Quotient.eq]
    simp
  · simp only [map_one, mul_one, one_mul, sub_self, HahnSeries.coeff_zero, sub_zero]
    exact hψ r

theorem isThB_act_heckeU_same : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l,
    b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (hq ε l φ) := by
  intro Ω _ _ _ ε X A N l _ n w d hd hl b hb φ hφ h
  rw [GlobalTheory.T.diamond_commutes_hecke_U Ω ε X N l w d hd hl b hb]
  obtain ⟨f, hinv, hcls, hδ, hdl⟩ := h
  have hint : ∀ r, (hq ε l φ).coeff r ∈ A := by
    intro r
    rw [GlobalTheory.T.heckeSumAtCuspHahn_coeff_of_integral_exponents Ω ε l (Nat.Prime.pos Fact.out) φ hφ r]
    split_ifs
    · exact hdl.1 _
    · exact A.zero_mem
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact isThB_zero X A N l _ _ hint
  set b' := X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b
  have hT : X.sl (ofSL ModularGroup.T) (f : X.K) = f := hinv _ (by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  have hcoe : ((∏ j ∈ Finset.range l,
      Units.map (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv.toMonoidHom f : X.Kˣ) : X.K)
      = ∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) (f : X.K) := by
    rw [Units.coe_prod]; rfl
  refine ⟨∏ j ∈ Finset.range l, Units.map (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv.toMonoidHom f,
    ?_, ?_, ?_, ?_⟩
  · rw [hcoe]; exact GlobalTheory.T.heckeNorm_gamma1PrimePow_invariant Ω ε X N l n hn _ hinv
  · have hv : X.heckeU l b' ![1, 0] = ∑ j ∈ Finset.range l,
        X.kmap l (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv (b' ![1, 0]) := by
      simp only [Tower.heckeU]
      rw [LinearMap.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      show X.kmap l _ (b' _) = _
      congr 2
      ext i; fin_cases i <;> simp [mZl]
    rw [hv]
    exact eval_sum_kmap X l n (Finset.range l)
      (fun j => (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv) _ f hcls
  · rw [hcoe]; exact GlobalTheory.T.heckeNorm_preserves_delta_powerCondition Ω ε X N l n hn hl _ hinv hδ
  · rw [hcoe]; exact GlobalTheory.T.isLogDerivQExpansionModPrimePow_heckeNorm Ω ε X A l n _ φ hT hφ hdl

theorem isThB_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ)
    (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (hlA : (l : Ω) ∈ A.nonunits)
    (x : X.Fn l) (ψ ψ₂ : HahnSeries ℚ Ω) (h : IsThB X A N l n x ψ) (hint : ∀ r, ψ₂.coeff r ∈ A)
    (hc : ∀ r, CgA A l n (ψ.coeff r) (ψ₂.coeff r)) : IsThB X A N l n x ψ₂ := by
  obtain ⟨f, h1, h2, h3, h4⟩ := h
  obtain ⟨φ₀, han, hdiff⟩ := hj
  exact ⟨f, h1, h2, h3, (GlobalTheory.T.isLogDerivQExpansionModPrimePow_calculus ε X ⟨φ₀, hdiff, han⟩ l A hlA n 1 (f : X.K) (f : X.K) ψ ψ₂).2.2.1 h4 hint hc⟩

theorem isThB_act_heckeU : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), Algebra.IsAlgebraic ℚ Ω →
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → 1 ≤ N → Odd w →
    (l : Ω) ∈ A.nonunits → d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsLat 1 φ →
  IsThB X A N l (n + 1) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (uq l φ) := by
  intro Ω _ _ _ ε X A N l _ n w d hAlg hj hl2 hN1 hw hlA hd hl b hb φ _ h
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, hAlg⟩
  have hl0 : 0 < l := Nat.Prime.pos Fact.out
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hl).symm
  obtain ⟨φ', h', hlat'⟩ := GlobalTheory.ThEx.of_lift GlobalTheory.ThLift.exists_invariant_lift Ω ε X A N l hAlg hj hl2 hl hN1 hlA n w hw _
    (GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l w d hN1 hNl hd b hb)
  have hU := isThB_act_heckeU_same Ω ε X A N l n w d hd hl b hb _
    (fun r hr => by simpa using hlat' r hr) h'
  rw [Api.hq_eq_uq_of_isAlgClosed hl0 hlat'] at hU
  have hc := GlobalTheory.ThBCompat.isThB_succ_coeff_cong Ω ε X A N l hl2 hl hN1 hlA n _ φ _ h h'
  have hφA : ∀ r, φ.coeff r ∈ A := by
    obtain ⟨f, -, -, -, hdl⟩ := h
    exact hdl.1
  refine isThB_congr X A N l n hj hlA _ _ _ hU ?_ ?_
  · intro r
    rw [Api.coeff_uq hl0]
    split_ifs
    · exact hφA _
    · exact A.zero_mem
  · intro r
    rw [Api.coeff_uq hl0, Api.coeff_uq hl0]
    split_ifs
    · obtain ⟨z, hz, e⟩ := hc ((l : ℚ) * r)
      exact ⟨-z, A.neg_mem _ hz, by linear_combination -e⟩
    · exact ⟨0, A.zero_mem, by simp⟩

end GlobalTheory.ThHeckeU
end
end

