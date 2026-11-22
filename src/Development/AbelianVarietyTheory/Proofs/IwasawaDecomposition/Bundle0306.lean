import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
section
namespace GlobalTheory.UnrLoc

theorem fixed_ne_bot_of_mem_iSup_range :
    ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
      {ι : Type} [Finite ι] {σ : Representation ℂ G V}, σ.IsIrreducible →
      ∀ {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X},
      f ∈ ⨆ j, LinearMap.range (T j).toLinearMap → f ≠ 0 → (∀ k ∈ K, ρ k f = f) →
      GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
  intro G V X _ _ _ _ _ ι _ σ hσ ρ T K f hf hf0 hfix
  classical
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  haveI : Fintype ι := Fintype.ofFinite ι

  let Y : Finset ι → Submodule ℂ X := fun t => ⨆ j ∈ t, LinearMap.range (T j).toLinearMap
  have hYst : ∀ (t : Finset ι) (g : G) (x : X), x ∈ Y t → ρ g x ∈ Y t := by
    intro t g x hx
    have hle : Y t ≤ (Y t).comap (ρ g) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      have : ρ g ((T j).toLinearMap v) = (T j).toLinearMap (σ g v) := by
        simp only [Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining]
      rw [this]
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => LinearMap.range (T j).toLinearMap) j hj)
        (LinearMap.mem_range_self _ _)
    exact hle hx
  have key : ∀ (t : Finset ι) (x : X), x ∈ Y t → x ≠ 0 → (∀ k ∈ K, ρ k x = x) →
      GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx hx0 _
      exact absurd (by simpa [Y] using hx) hx0
    | insert j t hjt ih =>
      intro x hx hx0 hxfix
      have hx' : x ∈ LinearMap.range (T j).toLinearMap ⊔ Y t := by
        simpa [Y, Finset.iSup_insert] using hx
      obtain ⟨y, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      let U : Subrepresentation σ :=
        ⟨(Y t).comap (T j).toLinearMap, fun g w hw => by
          rw [Submodule.mem_comap] at hw ⊢
          have : (T j).toLinearMap (σ g w) = ρ g ((T j).toLinearMap w) := by
            simp only [Representation.IntertwiningMap.toLinearMap_apply,
              Representation.IntertwiningMap.isIntertwining]
          rw [this]
          exact hYst t g _ hw⟩
      rcases eq_bot_or_eq_top U with hU | hU
      · have hU' : (Y t).comap (T j).toLinearMap = ⊥ := congrArg Subrepresentation.toSubmodule hU
        have hvfix : ∀ k ∈ K, σ k v = v := by
          intro k hk
          have hmem : σ k v - v ∈ (Y t).comap (T j).toLinearMap := by
            rw [Submodule.mem_comap, map_sub]
            have h1 := hxfix k hk
            have h2 : (T j).toLinearMap (σ k v) = ρ k ((T j).toLinearMap v) := by
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.IntertwiningMap.isIntertwining]
            rw [map_add] at h1
            have h3 : (T j).toLinearMap (σ k v) - (T j).toLinearMap v = z - ρ k z := by
              rw [h2, sub_eq_sub_iff_add_eq_add, h1, add_comm]
            rw [h3]
            exact sub_mem hz (hYst t k z hz)
          rw [hU'] at hmem
          exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hmem)
        by_cases hv : v = 0
        · subst hv
          simp only [map_zero, zero_add] at hx0 hxfix hz ⊢
          exact ih z hz hx0 hxfix
        · rw [Submodule.ne_bot_iff]
          refine ⟨v, ?_, hv⟩
          intro h
          simp [hvfix _ h.2]
      · have hv : (T j).toLinearMap v ∈ Y t := by
          have : v ∈ (⊤ : Subrepresentation σ).toSubmodule := Submodule.mem_top
          rw [← hU] at this
          exact this
        exact ih _ (add_mem hv hz) hx0 hxfix
  refine key Finset.univ f ?_ hf0 hfix
  simpa [Y] using hf

end GlobalTheory.UnrLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubst
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockBasis

section Mat

variable {m n : ℕ}

theorem unitMap_mul (B u : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j =
      ∑ a, ∑ b, (k a i * u⁻¹ j b) • Formalism.IndefR.Datum.unitMap B B' a b := by
  have e : k * Matrix.single i j (1 : ℂ) * u⁻¹ = ∑ a, ∑ b, (k a i * u⁻¹ j b) • Matrix.single a b (1 : ℂ) := by
    rw [Matrix.matrix_eq_sum_single (k * Matrix.single i j (1 : ℂ) * u⁻¹)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc]
    · simp
  unfold Formalism.IndefR.Datum.unitMap
  rw [Matrix.mul_inv_rev]
  calc B' * k * Matrix.single i j (1 : ℂ) * (u⁻¹ * B⁻¹) = B' * (k * Matrix.single i j (1 : ℂ) * u⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [e]
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

open scoped ComplexOrder in

theorem isCartanInv_one {G B : Matrix (Fin n) (Fin n) ℂ} (hB : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * 1 * B⁻¹ := by
    rw [← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  refine ⟨Matrix.one_mul _, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_mul_same Matrix.PosDef.one ?_
  exact Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu))

end Mat

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (s : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
include hψ hθ hf

theorem aPlus_add_dir (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (z + z') f =
      Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f + Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z' f := by
  have e : cplxO 1 s (z + z') = cplxO 1 s z + cplxO 1 s z' := by
    simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
  simp only [GlobalTheory.FockSubst.aPlus_eq, e, fun z => (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ z).2.2.1]
  module

theorem dRho_smul_dir (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.dRho (heisO ψ S T) θ τ (c • z) f =
      (c.re : ℂ) • Datum.dRho (heisO ψ S T) θ τ z f + (c.im : ℂ) • Datum.dRho (heisO ψ S T) θ τ (Complex.I • z) f := by
  have e : c • z = (c.re : ℂ) • z + (c.im : ℂ) • (Complex.I • z) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [e, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.1, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.2.1,
    (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.2.1]

theorem aPlus_smul_dir (e : Bool) (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (hz : cplxO 1 s z = (Complex.I * if e then 1 else -1) • z) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (c • z) f =
      (if e then c else star c) • Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f := by
  have e1 : cplxO 1 s (c • z) = c • cplxO 1 s z := by
    simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_comm c]
  simp only [GlobalTheory.FockSubst.aPlus_eq]
  rw [e1, hz, smul_smul, dRho_smul_dir hψ hθ τ hf c, dRho_smul_dir hψ hθ τ hf (c * _),
    dRho_smul_dir hψ hθ τ hf (Complex.I * _)]
  generalize ((fockScale D τ : ℝ) : ℂ)⁻¹ = r
  cases e
  · match_scalars <;> apply Complex.ext <;> simp <;> ring
  · match_scalars <;> apply Complex.ext <;> simp <;> ring

theorem aPlus_sum_dir {ι : Type} (t : Finset ι) (z : ι → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (∑ i ∈ t, z i) f =
      ∑ i ∈ t, Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (z i) f := by
  induction t using Finset.induction_on with
  | empty =>
    have h := aPlus_add_dir hψ hθ τ s hf 0 0
    rw [add_zero] at h
    rw [Finset.sum_empty, Finset.sum_empty]
    exact left_eq_add.1 h
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, aPlus_add_dir hψ hθ τ s hf, ih]

theorem aPlus_unitMap_mul {ε : Fin T.rank → Bool} {B' k : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (ht : s * B' = B' * diagonal fun a => if ε a then (1 : ℂ) else -1) (hk : k ∈ Formalism.REAL.Kset ε)
    (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) {u : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) (i : Fin T.rank) (j : Fin S.rank) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j) f =
      ∑ a, ∑ b, (if ε i = true then k a i * u⁻¹ j b else k⁻¹ i a * u b j) •
        Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (Formalism.IndefR.Datum.unitMap B B' a b) f := by
  rw [unitMap_mul, aPlus_sum_dir hψ hθ τ _ hf]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [aPlus_sum_dir hψ hθ τ _ hf]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [aPlus_smul_dir hψ hθ τ _ hf (ε a) _ _ (GlobalTheory.FockIndep.cplxO_unitMap ht a b)]
  refine congrArg (· • _) ?_
  have hk1 : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hk.1)
  have hu1 : u⁻¹ = uᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hu)
  have hc := congrFun (congrFun hk.2 a) i
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  rw [hk1, hu1, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, star_mul', star_star]
  by_cases h : ε a = ε i
  · rw [h]
  · have h0 : k a i = 0 := by
      cases h1 : ε a <;> cases h2 : ε i <;> simp only [h1, h2, not_true, if_true, Bool.false_eq_true, if_false] at h hc
      · linear_combination hc / 2
      · linear_combination -hc / 2
    simp [h0]

omit hψ hθ hf

section Generic

variable {ι κ μ X : Type} [Fintype κ] [Fintype μ] {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_subst {g : X → ℂ} (c : ι → κ → μ → ℂ) (e : ι → κ → μ → ι)
    (hm : ∀ Q, P (pureTensorL A g Q))
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (hA : ∀ v h, P h → A' v h = ∑ a, ∑ b, c v a b • A (e v a b) h) (Q : MvPolynomial ι ℂ) :
    pureTensorL A' g Q = pureTensorL A g
      (MvPolynomial.aeval (fun v => ∑ a, ∑ b, MvPolynomial.C (c v a b) * MvPolynomial.X (e v a b)) Q) := by
  have hC : ∀ (A : ι → (X → ℂ) → (X → ℂ)) a, pureTensorL A g (MvPolynomial.C a) = a • g := fun A a => by
    rw [← mul_one (MvPolynomial.C a), MvPolynomial.C_mul', map_smul, GlobalTheory.FockIndep.pure_one]
  induction Q using MvPolynomial.induction_on with
  | C a => rw [hC, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, hC]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, hX', hp, map_mul, MvPolynomial.aeval_X, hA _ _ (hm _)]
    simp only [Finset.sum_mul, map_sum, mul_assoc]
    simp only [MvPolynomial.C_mul', map_smul, smul_mul_assoc, hX]

end Generic

theorem pureTensorO_basis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (k : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∀ f, IsThetaFunO ψ S T f → ∀ P : PolF D T.rank S.rank, pureTensorO ψ θ S T (fun _ => 1) (cart M) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fsub M.ε k u P) := by
  intro D ψ θ S T Sp M BS hψ hθ hB k u hk hu f hf P
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hS := fun τ => isCartanInv_one (hB τ)
  have hfr := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have ht : ∀ τ, cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (hfr τ)]
    rfl
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ B B' v g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B' v g) :=
    fun _ _ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ B B' v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B') f Q) := fun B B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm (hth B B') ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hA : ∀ v g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) v g =
      ∑ a, ∑ b, (if M.ε v.1 v.2.1 = true then k v.1 a v.2.1 * (u v.1)⁻¹ v.2.2 b
        else (k v.1)⁻¹ v.2.1 a * u v.1 b v.2.2) •
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (onb M) (v.1, a, b) g := fun v g hg => by
    unfold aPlusAll
    exact aPlus_unitMap_mul hψ hθ v.1 _ hg (ht v.1) (hk v.1) _ (hu v.1) v.2.1 v.2.2
  have key := pure_subst (P := IsThetaFunO ψ S T) _ _
    (GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm (hth _ _) hf) (hX _ _) (hX _ _) hA P
  unfold pureTensorO fsub
  exact key

end GlobalTheory.FockBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitutStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_maximalCompact_basis_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (k c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → IsThetaFunO ψ S T f → (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ a b, c τ b a = if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (MvPolynomial.aeval (fun v : FVar D T.rank S.rank => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P) := by
  first | exact @GlobalTheory.FockSubst.pureTensorO_subst | exact GlobalTheory.FockSubst.pureTensorO_subst | (intros; apply GlobalTheory.FockSubst.pureTensorO_subst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVectors_injective_nonzero_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → IsThetaFunO ψ S T f → f ≠ 0 → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → Function.Injective (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f) := by
  first | exact @GlobalTheory.FockIndep.pureTensorO_injective | exact GlobalTheory.FockIndep.pureTensorO_injective | (intros; apply GlobalTheory.FockIndep.pureTensorO_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsEquiv
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2.StepZero

section Gen
open _root_.Formalism.L2.Forms
variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem mem_formsK (S : GStep E K n) (hS : S.Free) (hF : (S.fam emb lam).Ok) (x : S.Cl → VV K lam) : x ∈ S.FormsK emb lam hF := by
  intro c γ
  have hγ : (γ : S.G c.1) = 1 := hS c.1 γ (S.rp c.1 c.2) γ.2
  show (S.rho emb lam c.1) (γ : S.G c.1) (x c) = x c
  rw [hγ, map_one]
  rfl

theorem forms_equiv (S S' : GStep E K n) (hS : S.Free) (hS' : S'.Free) (hF : (S.fam emb lam).Ok) (hF' : (S'.fam emb lam).Ok)
    (e0 : S.Cl ≃ S'.Cl) (hL : ∀ c, S'.Lsh _ (S'.rep (e0 c)) = S.Lsh _ (S.rep c)) :
    ∃ e : (S.hlat emb lam hF).V ≃ₗ[K] (S'.hlat emb lam hF').V,
      (∀ x, x ∈ (S.hlat emb lam hF).L ↔ e x ∈ (S'.hlat emb lam hF').L) ∧
        ∀ x, S'.embF emb σ lam hF' (e x) = fun c => S.embF emb σ lam hF x (e0.symm c) := by
  let f : S.FormsK emb lam hF →ₗ[K] S'.FormsK emb lam hF' :=
    { toFun := fun x => ⟨fun c => x.1 (e0.symm c), mem_formsK emb lam S' hS' hF' _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g : S'.FormsK emb lam hF' →ₗ[K] S.FormsK emb lam hF :=
    { toFun := fun y => ⟨fun c => y.1 (e0 c), mem_formsK emb lam S hS hF _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_, ?_, ?_⟩
  · ext y c
    simp [f, g]
  · ext x c
    simp [f, g]
  · intro x
    constructor
    · intro hx c
      have h1 := hx (e0.symm c)
      have h2 := hL (e0.symm c)
      rw [Equiv.apply_symm_apply] at h2
      show x.1 (e0.symm c) ∈ delAtr emb lam (S'.Lsh c.1 (S'.rep c))
      rw [h2]
      exact h1
    · intro hx c
      have h1 : x.1 (e0.symm (e0 c)) ∈ delAtr emb lam (S'.Lsh (e0 c).1 (S'.rep (e0 c))) := hx (e0 c)
      rw [hL c, Equiv.symm_apply_apply] at h1
      exact h1
  · intro x
    rfl
end Gen

attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 1600000 in

theorem law0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ l : I.Laws, I.Law0 l := by
  intro B X I hI l u a
  obtain ⟨e, he1, he2⟩ := forms_equiv B.fields.emb B.embLL (lamT (B.hcW u) 0) (I.stp u I.mu0 0) (I.stp u a 0)
    (l.lev u I.mu0).free0 (l.lev u a).free0 ((l.fmL u I.mu0).fam 0) ((l.fmL u a).fam 0) (I.eCls0 l u a)
    (fun c => by
      have h := (GlobalTheory.T.cl0_bijective_and_deco_eq I hI u a (l.idx0 a).some).2 c
      show ((I.stp u a 0).rep (I.cl0 u a (l.idx0 a).some c)).1.1.deco.1.Lsh = ((I.stp u I.mu0 0).rep c).1.1.deco.1.Lsh
      rw [h])
  exact ⟨e, he1, fun x => he2 x⟩

end GlobalTheory.Mem.Col2.StepZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeightStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_model_holomorphic_integral_extremal_weight : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_order → ∀ i, HolShape (R.MW i (sg0 D A)) ∧ ∃ w, WtIs (R.MW i (sg0 D A)) w := by
  first | exact @GlobalTheory.DefLift.holShape_fixed | exact GlobalTheory.DefLift.holShape_fixed | (intros; apply GlobalTheory.DefLift.holShape_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalRStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldIntegralModel_exists_isHom_of_map_localRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') → ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | exact GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | (intros; apply GlobalTheory.ZH.RatModel.exists_isHom_of_map_O <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionCommuteUnitaryRepSmoothStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariantAction_commute_unitaryRep_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (k : ℕ), ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P), gelfH G (trRep σ P) k ((trRep σ P) g w) = (trRep σ P) g (gelfH G (trRep σ P) k w) := by
  first | exact @GlobalTheory.SmVecGelfComm.gelfH_rep | exact GlobalTheory.SmVecGelfComm.gelfH_rep | (intros; apply GlobalTheory.SmVecGelfComm.gelfH_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorCommutesIsometry
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem trace_pow_rect {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (E' : Fin m → Fin m → A)
    (P : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (h : ∀ a b, E' a b = ∑ c, ∑ d, (Q c a * P b d) • E c d) (k : ℕ) :
    ∑ c, (Matrix.of E' ^ k) c c = ∑ c, (Matrix.of E ^ k) c c := by
  first
  | exact @_root_.GlobalTheory.TracePowEq.trace_pow_eq
  | exact _root_.GlobalTheory.TracePowEq.trace_pow_eq
  | (apply _root_.GlobalTheory.TracePowEq.trace_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TracePowEq.trace_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TracePowEq.trace_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TracePowEq.trace_pow_eq ..)

namespace IsoMat

variable {D : D7} {V V' : HSp D} (I : IsoMat V V') {θ : InfF D}

def trSm (hθ : IsInfFam θ) : GlobalTheory.Mem.AutSpace.SmFun θ V ≃ₗ[ℂ] GlobalTheory.Mem.AutSpace.SmFun θ V' where
  toFun φ := ⟨I.tr φ.1, I.tr_mem_SmFun hθ φ.2⟩
  invFun ψ := ⟨I.symm.tr ψ.1, I.symm.tr_mem_SmFun hθ ψ.2⟩
  left_inv φ := Subtype.ext (funext fun x => congrArg φ.1 (I.kapF_symm x))
  right_inv ψ := Subtype.ext (funext fun x => congrArg ψ.1 (I.symm.kapF_symm x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def conjSm (hθ : IsInfFam θ) :
    Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) →+* Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V') where
  toFun f := (I.trSm hθ).toLinearMap ∘ₗ f ∘ₗ (I.trSm hθ).symm.toLinearMap
  map_one' := LinearMap.ext fun x => by simp
  map_mul' f g := LinearMap.ext fun x => by simp
  map_zero' := LinearMap.ext fun x => by simp
  map_add' f g := LinearMap.ext fun x => by simp

theorem conjSm_apply (hθ : IsInfFam θ) (f : Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V)) (x : GlobalTheory.Mem.AutSpace.SmFun θ V) :
    I.conjSm hθ f (I.trSm hθ x) = I.trSm hθ (f x) := by
  show I.trSm hθ (f ((I.trSm hθ).symm (I.trSm hθ x))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem conjSm_smul (hθ : IsInfFam θ) (c : ℂ) (f : Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V)) :
    I.conjSm hθ (c • f) = c • I.conjSm hθ f := LinearMap.ext fun x => by simp [conjSm]

theorem derEnd_tr (hθ : IsInfFam θ) (τ : D.what₂.Tau) (Z : Matrix (Fin V'.rank) (Fin V'.rank) ℂ) :
    GlobalTheory.Mem.RealTranslate.derEnd hθ τ Z = I.conjSm hθ (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (I.symm.adP τ Z)) := by
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨φ, rfl⟩ := (I.trSm hθ).surjective ψ
  rw [conjSm_apply]
  exact Subtype.ext (I.RderC_tr hθ τ Z φ.1)

theorem symm_adP_single (τ : D.what₂.Tau) (a b : Fin V'.rank) :
    I.symm.adP τ (Matrix.single a b 1) = ∑ c, ∑ d, (I.qT τ c a * I.pT τ b d) • (Matrix.single c d 1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
  rw [matrix_eq_sum_single (I.symm.adP τ _)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [adP, pT, qT, symm, Matrix.mul_apply, Matrix.single, ite_and]

theorem gelf_tr : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ →
    ∀ (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ), φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V →
      gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) := by
  intro D V V' I θ hθ τ k φ hφ
  let E0 : Fin V.rank → Fin V.rank → Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) :=
    fun c d => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (Matrix.single c d 1)
  let E' : Fin V'.rank → Fin V'.rank → Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V') :=
    fun a b => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (Matrix.single a b 1)
  have key := trace_pow_rect (fun c d => I.conjSm hθ (E0 c d)) E' (I.pT τ) (I.qT τ) (I.pT_qT τ) (I.qT_pT τ)
    (fun a b => by
      simp only [E', E0]
      rw [I.derEnd_tr hθ τ, I.symm_adP_single τ a b]
      simp only [map_sum, LinearMap.map_smul, conjSm_smul]) (k + 1)
  have hm : Matrix.of (fun c d => I.conjSm hθ (E0 c d)) = (I.conjSm hθ).mapMatrix (Matrix.of E0) := by
    ext c d; rfl
  have hs : ∑ c, (((I.conjSm hθ).mapMatrix (Matrix.of E0)) ^ (k + 1)) c c =
      I.conjSm hθ (∑ c, (Matrix.of E0 ^ (k + 1)) c c) := by
    rw [← RingHom.map_pow, map_sum]; rfl
  rw [hm, hs, ← GlobalTheory.SmoothForms.gelfA_eq_sum_pow, ← GlobalTheory.SmoothForms.gelfA_eq_sum_pow] at key
  have e1 := GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (I.trSm hθ ⟨φ, hφ⟩)
  have e2 := GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (⟨φ, hφ⟩ : GlobalTheory.Mem.AutSpace.SmFun θ V)
  refine e1.trans ?_
  change (GlobalTheory.SmoothForms.gelfA E' k (I.trSm hθ ⟨φ, hφ⟩)).1 = _
  rw [key, conjSm_apply]
  show I.tr _ = I.tr _
  rw [e2]

end IsoMat
end GlobalTheory.Mem.Isom

end
end

