import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Mathlib
import Formalism.DegreeFormula.PointDegree.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankAlgebraicModularFormsComplexification
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevCmp

theorem exists_finset_eval_eq_zero {X K W : Type} [Field K] [AddCommGroup W] [Module K W]
    (V : Submodule K (X → W)) [FiniteDimensional K V] :
    ∃ P : Finset X, ∀ f ∈ V, (∀ x ∈ P, f x = 0) → f = 0 := by
  classical
  let N : Finset X → Submodule K V := fun P =>
    ⨅ x ∈ P, LinearMap.ker ((LinearMap.proj (R := K) (φ := fun _ : X => W) x).comp V.subtype)
  have hN : ∀ P (f : V), f ∈ N P ↔ ∀ x ∈ P, (f : X → W) x = 0 := by
    intro P f; simp [N, Submodule.mem_iInf]
  obtain ⟨_, ⟨P, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min (Set.range N) ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨P, fun f hf h0 => ?_⟩
  have key : ∀ x, N P ≤ N (insert x P) := by
    intro x
    have hle : N (insert x P) ≤ N P := fun g hg =>
      (hN _ _).2 fun y hy => (hN _ _).1 hg y (Finset.mem_insert_of_mem hy)
    by_contra hne
    exact hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle fun h => hne h.ge)
  funext x
  exact (hN _ _).1 (key x ((hN P ⟨f, hf⟩).2 h0)) x (Finset.mem_insert_self x P)

section Omega
variable {K W W' ι : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W']
  [Fintype ι] [DecidableEq ι]

def coordCx (e : K →+* ℂ) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W') : W →ₛₗ[e] W' where
  toFun w := b'.equivFun.symm fun i => e (b.equivFun w i)
  map_add' x y := b'.equivFun.injective (by
    simp only [map_add, LinearEquiv.apply_symm_apply]; funext i; simp only [Pi.add_apply, map_add])
  map_smul' a x := b'.equivFun.injective (by
    simp only [map_smul, LinearEquiv.apply_symm_apply]; funext i; simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply])

theorem coordCx_coord (e : K →+* ℂ) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W') (w : W) (i : ι) :
    b'.equivFun (coordCx e b b' w) i = e (b.equivFun w i) := by
  simp only [coordCx, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]

end Omega

theorem finrank_typeSp_cx : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (W W' : Type) [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') (J : Subgroup (GAf L n)) (χ : J →* Kˣ), WtMatch e ρ ρ' → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → FiniteDimensional K (NX.TypeSpF L n K ρ J χ) → Module.finrank ℂ (NG.TypeSp ρ' J (cx e χ)) = Module.finrank K (NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ e W W' _ _ _ _ ρ ρ' J χ hW hN hfin
  classical
  obtain ⟨ι, _, _, b, b', hM⟩ := hW
  letI : Algebra K ℂ := e.toAlgebra
  let β := Module.Basis.ofVectorSpace K ℂ
  let ω := coordCx e b b'
  have hωc : ∀ w i, b'.equivFun (ω w) i = e (b.equivFun w i) := fun w i => coordCx_coord e b b' w i
  have hρ : ∀ γ w i, b.equivFun (ρ γ w) i = ∑ k, LinearMap.toMatrix b b (ρ γ) i k * b.equivFun w k := by
    intro γ w i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b b (ρ γ) w) i
    simp only [Module.Basis.equivFun_apply]; rw [← this]; rfl
  have hρ' : ∀ γ w i, b'.equivFun (ρ' γ w) i = ∑ k, e (LinearMap.toMatrix b b (ρ γ) i k) * b'.equivFun w k := by
    intro γ w i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b' b' (ρ' γ) w) i
    rw [hM γ] at this
    simp only [Module.Basis.equivFun_apply]; rw [← this]; rfl
  have hωρ : ∀ γ w, ω (ρ γ w) = ρ' γ (ω w) := fun γ w =>
    b'.equivFun.injective (funext fun i => by rw [hωc, hρ, hρ', map_sum]; simp only [map_mul, hωc])
  have hβ1 : ∀ (y : K) (z : ℂ) α, β.repr (e y * z) α = y * β.repr z α := by
    intro y z α
    rw [show e y * z = y • z from rfl, map_smul, Finsupp.smul_apply, smul_eq_mul]
  let V := NX.TypeSpF L n K ρ J χ
  let v := Module.finBasis K V
  have hωV : ∀ f ∈ V, (fun g => ω (f g)) ∈ NG.TypeSp ρ' J (cx e χ) := by
    rintro f ⟨h1, h2⟩
    obtain ⟨N, hN0, hNc⟩ := hN
    refine ⟨⟨fun γ g => by simp only [h1, hωρ], N, hN0, fun κ hκ g => ?_⟩, fun κ => ?_⟩
    · obtain ⟨h, h1'⟩ := hNc κ hκ
      show ω (f (g * κ)) = ω (f g)
      have := h2 ⟨κ, h⟩ g
      rw [this, h1', Units.val_one, one_smul]
    · funext g
      show ω (f (g * κ)) = ((cx e χ κ : ℂˣ) : ℂ) • ω (f g)
      rw [h2, map_smulₛₗ, cx_apply]

  have hlinK : LinearIndependent K (fun j => ((v j : V) : GAf L n → W)) :=
    v.linearIndependent.map' V.subtype V.ker_subtype
  have hli : LinearIndependent ℂ (fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    rw [Fintype.linearIndependent_iff] at hlinK ⊢
    intro c hc j
    have hcoord : ∀ g i, ∑ j, c j * e (b.equivFun (((v j : V) : GAf L n → W) g) i) = 0 := by
      intro g i
      have := congrArg (fun F => b'.equivFun (F g) i) hc
      simpa only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, hωc,
        Pi.zero_apply, map_zero] using this
    have hα : ∀ α, ∀ j, β.repr (c j) α = 0 := by
      intro α
      apply hlinK
      funext g
      apply b.equivFun.injective
      funext i
      have := congrArg (fun z => β.repr z α) (hcoord g i)
      simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, mul_comm (c _), hβ1, map_zero,
        Finsupp.coe_zero, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, map_zero, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact β.repr.injective (by ext α; simp [hα α j])

  have hspanV : ∀ a : Fin (Module.finrank K V) → K,
      (fun g => ω ((∑ j, a j • ((v j : V) : GAf L n → W)) g)) ∈
        Submodule.span ℂ (Set.range fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    intro a
    have : (fun g => ω ((∑ j, a j • ((v j : V) : GAf L n → W)) g)) =
        ∑ j, e (a j) • fun g => ω (((v j : V) : GAf L n → W) g) := by
      funext g
      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hspan : NG.TypeSp ρ' J (cx e χ) = Submodule.span ℂ (Set.range fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    refine le_antisymm ?_ (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hωV _ (v j).2))
    rintro F ⟨⟨hF1, -⟩, hF2⟩
    have hFk : ∀ (κ : J) g, F (g * κ) = e (χ κ) • F g := fun κ g => congrFun (hF2 κ) g
    let fa : _ → GAf L n → W := fun α g => b.equivFun.symm fun i => β.repr (b'.equivFun (F g) i) α
    have hfa : ∀ α g i, b.equivFun (fa α g) i = β.repr (b'.equivFun (F g) i) α := by
      intro α g i; simp only [fa, LinearEquiv.apply_symm_apply]
    have hfaV : ∀ α, fa α ∈ V := by
      intro α
      refine ⟨fun γ g => b.equivFun.injective (funext fun i => ?_), fun κ g => b.equivFun.injective (funext fun i => ?_)⟩
      · rw [hfa, hF1, hρ', hρ, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
        simp only [hβ1, hfa]
      · rw [hfa, hFk, map_smul, Pi.smul_apply, smul_eq_mul, hβ1, map_smul, Pi.smul_apply, smul_eq_mul, hfa]
    obtain ⟨P, hP⟩ := exists_finset_eval_eq_zero V
    let S := P.biUnion fun g => Finset.univ.biUnion fun i => (β.repr (b'.equivFun (F g) i)).support
    have hzero : ∀ α ∉ S, fa α = 0 := by
      intro α hα
      refine hP _ (hfaV α) fun g hg => b.equivFun.injective (funext fun i => ?_)
      rw [hfa, map_zero, Pi.zero_apply]
      by_contra h
      exact hα (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.2 h⟩⟩)
    have hsub : ∀ g i, (β.repr (b'.equivFun (F g) i)).support ⊆ S := by
      intro g i α hα
      by_contra hS
      have := congrArg (fun f => b.equivFun (f g) i) (hzero α hS)
      simp only [hfa, Pi.zero_apply, map_zero] at this
      exact (Finsupp.mem_support_iff.1 hα) this
    have hFeq : F = ∑ α ∈ S, β α • fun g => ω (fa α g) := by
      funext g
      apply b'.equivFun.injective
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, hωc, hfa]
      conv_lhs => rw [← β.linearCombination_repr (b'.equivFun (F g) i)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hsub g i) (fun a c => c • β a) (fun _ _ => zero_smul _ _)]
      exact Finset.sum_congr rfl fun α _ => mul_comm _ _
    rw [hFeq]
    refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ ?_
    have hrep := congrArg Subtype.val (v.sum_repr ⟨fa α, hfaV α⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
    rw [← hrep]
    exact hspanV _
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.LevCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagMapChernRootsPointPoly
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.SchubertPoint

theorem sign_revPerm_real (n : ℕ) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℝ) = (-1) ^ (∑ i : Fin n, (i : ℕ)) := by
  induction n with
  | zero =>
    rw [Subsingleton.elim (Fin.revPerm : Equiv.Perm (Fin 0)) 1]; simp
  | succ n ih =>
    have key : finRotate (n + 1) * (Fin.revPerm : Equiv.Perm (Fin (n + 1))) =
        Equiv.Perm.decomposeFin.symm (0, (Fin.revPerm : Equiv.Perm (Fin n))) := by
      ext i
      cases i using Fin.cases with
      | zero => simp
      | succ j =>
        simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.rev_succ]
    have hs := congrArg Equiv.Perm.sign key
    rw [Equiv.Perm.sign_mul, sign_finRotate, Equiv.Perm.decomposeFin.symm_sign] at hs
    simp only [if_true, one_mul, Nat.add_sub_cancel] at hs
    rw [Fin.sum_univ_castSucc, pow_add]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [← ih]
    have : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n + 1))) =
        (-1) ^ n * Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) := by
      rw [← hs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
    rw [this]; push_cast; ring

theorem esymm_self (n : ℕ) : esymm (Fin n) ℝ n = ∏ i : Fin n, X i := by
  have h : Finset.powersetCard n (Finset.univ : Finset (Fin n)) = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [esymm, h]
  simp

def revTail (p q : ℕ) : Equiv.Perm (Fin (p + q)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr 1 Fin.revPerm)

theorem revTail_castAdd (p q : ℕ) (i : Fin p) : revTail p q (Fin.castAdd q i) = Fin.castAdd q i := by
  simp [revTail, Equiv.permCongr_apply]

theorem revTail_natAdd (p q : ℕ) (j : Fin q) : revTail p q (Fin.natAdd p j) = Fin.natAdd p (Fin.rev j) := by
  simp [revTail, Equiv.permCongr_apply]

theorem sign_revTail (p q : ℕ) :
    ((Equiv.Perm.sign (revTail p q) : ℤ) : ℝ) = (-1) ^ (∑ j : Fin q, (j : ℕ)) := by
  rw [revTail, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_one, one_mul]
  exact sign_revPerm_real q

theorem sum_tail (q : ℕ) : ∑ j : Fin q, (q - 1 - (j : ℕ)) = ∑ j : Fin q, (j : ℕ) := by
  refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  simp [Fin.val_rev]; omega

def tailSgn (p q : ℕ) (k : Fin (p + q)) : ℝ := if (k : ℕ) < p then (-1) ^ (p + q - 1 - (k : ℕ)) else 1

theorem schubPoint_eq (ι : Type) [Fintype ι] [DecidableEq ι] (p q : ℕ) :
    (∏ τ : ι, ((∏ i : Fin p, (-X (τ, Fin.castAdd q i) : MvPolynomial (ι × Fin (p + q)) ℝ) ^ (p + q - 1 - (i : ℕ))) *
      ∏ j : Fin q, X (τ, Fin.natAdd p j) ^ (j : ℕ))) =
    C (∏ x : ι × Fin (p + q), tailSgn p q x.2) * monomial (Formalism.DegreeFormula.permExp (fun _ : ι => revTail p q)) 1 := by
  have h : C (∏ x : ι × Fin (p + q), tailSgn p q x.2) * monomial (Formalism.DegreeFormula.permExp (fun _ : ι => revTail p q)) 1 =
      ∏ x : ι × Fin (p + q), (C (tailSgn p q x.2) * X x ^ (Formalism.DegreeFormula.permExp (fun _ : ι => revTail p q) x)) := by
    rw [Finset.prod_mul_distrib, ← map_prod, monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by intro i; simp)]
  rw [h, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [tailSgn, Formalism.DegreeFormula.permExp, revTail_castAdd, Finsupp.equivFunOnFinite_symm_apply_apply,
      Fin.coe_castAdd]
    rw [if_pos i.2, neg_pow, map_pow, map_neg, map_one]
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [tailSgn, Formalism.DegreeFormula.permExp, revTail_natAdd, Finsupp.equivFunOnFinite_symm_apply_apply,
      Fin.coe_natAdd, Fin.val_rev]
    rw [if_neg (by omega), C_1, one_mul]
    congr 1
    omega

theorem degFl_schubPoint (ι : Type) [Fintype ι] [DecidableEq ι] (p q : ℕ) :
    Formalism.DegreeFormula.degFl ι (p + q) (∏ τ : ι, ((∏ i : Fin p, (-X (τ, Fin.castAdd q i) : MvPolynomial (ι × Fin (p + q)) ℝ) ^
      (p + q - 1 - (i : ℕ))) * ∏ j : Fin q, X (τ, Fin.natAdd p j) ^ (j : ℕ))) = 1 := by
  rw [schubPoint_eq]
  unfold Formalism.DegreeFormula.degFl
  rw [Finset.sum_eq_single (fun _ => revTail p q)]
  · rw [coeff_C_mul, coeff_monomial, if_pos rfl, mul_one]
    have hA : ∏ x : ι × Fin (p + q), tailSgn p q x.2 =
        ((-1 : ℝ) ^ (∑ i : Fin p, (p + q - 1 - (i : ℕ)))) ^ Fintype.card ι := by
      rw [Fintype.prod_prod_type]
      dsimp only
      rw [Finset.prod_const, Finset.card_univ]
      congr 1
      rw [Fin.prod_univ_add]
      simp [tailSgn, Finset.prod_pow_eq_pow_sum]
    have hB : ∏ τ : ι, ((Equiv.Perm.sign ((fun _ : ι => revTail p q) τ) : ℤ) : ℝ) =
        ((-1 : ℝ) ^ (∑ j : Fin q, (j : ℕ))) ^ Fintype.card ι := by
      rw [Finset.prod_const, sign_revTail, Finset.card_univ]
    have hD : Formalism.DegreeFormula.dimFl ι (p + q) =
        Fintype.card ι * ((∑ i : Fin p, (p + q - 1 - (i : ℕ))) + ∑ j : Fin q, (j : ℕ)) := by
      unfold Formalism.DegreeFormula.dimFl
      congr 1
      rw [← Formalism.DegreeFormula.PermutationPointDegree.sum_delta, Fin.sum_univ_add, ← sum_tail]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Fin.coe_natAdd]; omega
    have e : ∀ a b c : ℕ, (-1 : ℝ) ^ (c * (a + b)) * (((-1) ^ b) ^ c * ((-1) ^ a) ^ c) = 1 := by
      intro a b c
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      exact Even.neg_one_pow ⟨c * (a + b), by ring⟩
    rw [hA, hB, hD]
    exact e _ _ _
  · intro σ _ hσ
    rw [coeff_C_mul, coeff_monomial, if_neg, mul_zero, mul_zero]
    intro h
    exact hσ (Formalism.DegreeFormula.PermutationPointDegree.permExp_inj _ _ h).symm
  · simp

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjOff (H : Host E) : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} ≃ GlobalTheory.AllWt.Psi H where
  toFun τ := ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
  invFun τ := ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
  left_inv τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
  right_inv τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)

theorem flagMap_chernRoots_pointPoly {H : Host E} (Dw : Datum H) :
    GlobalTheory.Schubert.flagMap Dw (GlobalTheory.GoodMetric.chernRoots Dw.mult (GlobalTheory.LieBase.pointPoly H Dw)) =
      ∏ τ : GlobalTheory.AllWt.Psi H, (∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i))) ^ Dw.q := by
  rw [GlobalTheory.LieBase.pointPoly, map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
  have he : Dw.p + Dw.q - Dw.mult τ.1 = Dw.q := by omega
  rw [he, map_pow, map_pow]
  congr 1
  simp only [map_mul, GlobalTheory.GoodMetric.chernRoots, GlobalTheory.Schubert.flagMap, aeval_C, aeval_X, algebraMap_eq,
    esymm_self, map_prod, rename_X]
  have h1 : ∀ i : Fin (Dw.mult τ.1), GlobalTheory.Schubert.flagRoot Dw ⟨τ.1, i⟩ =
      X (τ, Fin.castAdd Dw.q (finCongr hm i)) := by
    intro i
    rw [GlobalTheory.Schubert.flagRoot, dif_pos τ.2]
    rfl
  simp only [h1]
  have h2 : (∏ i : Fin (Dw.mult τ.1), (-X (τ, Fin.castAdd Dw.q (finCongr hm i)) : MvPolynomial _ ℝ)) =
      C ((-1 : ℝ) ^ Dw.mult τ.1) * ∏ i : Fin (Dw.mult τ.1), X (τ, Fin.castAdd Dw.q (finCongr hm i)) := by
    simp only [← neg_one_mul (X _ : MvPolynomial _ ℝ), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, map_pow, map_neg, map_one]
  rw [← h2]
  exact Fintype.prod_equiv (finCongr hm) _ _ fun i => rfl

theorem flagMap_fibrePoint {H : Host E} (Dw : Datum H) :
    GlobalTheory.Schubert.flagMap Dw (GlobalTheory.GoodMetric.fibrePoint Dw.mult) =
      (∏ τ : GlobalTheory.AllWt.Psi H, ∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i)) ^ (Dw.p - 1 - (i : ℕ))) *
        ∏ τ : GlobalTheory.AllWt.Psi H, ∏ j : Fin Dw.q, X (τ, Fin.natAdd Dw.p j) ^ (j : ℕ) := by
  rw [GlobalTheory.GoodMetric.fibrePoint, map_prod]
  simp only [map_pow, map_neg, GlobalTheory.Schubert.flagMap, aeval_X]
  rw [Fintype.prod_sigma, ← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
    refine Fintype.prod_equiv (finCongr hm) _ _ fun i => ?_
    rw [GlobalTheory.Schubert.flagRoot, dif_pos τ.2]
    congr 1
    simp only [finCongr_apply, Fin.coe_cast]
    omega
  · refine Fintype.prod_equiv (conjOff H) _ _ fun τ => ?_
    have hm : Dw.mult τ.1 = Dw.q := GlobalTheory.PointChern.mult_of_not_mem Dw τ.2
    refine Fintype.prod_equiv ((finCongr hm).trans Fin.revPerm) _ _ fun i => ?_
    rw [GlobalTheory.Schubert.flagRoot, dif_neg τ.2, neg_neg]
    have hi : (i : ℕ) < Dw.q := hm ▸ i.2
    congr 1
    · congr 1
      refine Prod.ext rfl (Fin.ext ?_)
      simp [Fin.val_rev]
      omega
    · simp [Fin.val_rev]
      omega

end Host

theorem schubGam_pointPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    GlobalTheory.Schubert.schubGam Dw (GlobalTheory.LieBase.pointPoly H Dw) = 1 := by
  intro E _ _ _ H Dw
  rw [GlobalTheory.Schubert.schubGam_apply, map_mul, flagMap_chernRoots_pointPoly, flagMap_fibrePoint]
  have h : (∏ τ : GlobalTheory.AllWt.Psi H, (∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i) : MvPolynomial _ ℝ)) ^ Dw.q) *
      ((∏ τ : GlobalTheory.AllWt.Psi H, ∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i)) ^ (Dw.p - 1 - (i : ℕ))) *
        ∏ τ : GlobalTheory.AllWt.Psi H, ∏ j : Fin Dw.q, X (τ, Fin.natAdd Dw.p j) ^ (j : ℕ)) =
      ∏ τ : GlobalTheory.AllWt.Psi H, ((∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i)) ^ (Dw.p + Dw.q - 1 - (i : ℕ))) *
        ∏ j : Fin Dw.q, X (τ, Fin.natAdd Dw.p j) ^ (j : ℕ)) := by
    rw [← mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add]
    congr 1
    have := i.2
    omega
  rw [h]
  exact degFl_schubPoint _ _ _

end GlobalTheory.SchubertPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisCharacterAntiRamifiedExactly
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.GalTwist

theorem galOf_twist_props : PrN → ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)) (χ : HChar D.host.E) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), l.Prime → IsPsi (H := D.host) l Q χ → GalOf D χ ψ₀ → AntiHom D.ntw.cc ψ₀ ∧ RamExactly ψ₀ (↑Q : Set (PlE D.host)) ∧ BlochKatoReduction.Gen.TrivAbove ψ₀ l := by
  intro _ D l Q χ ψ₀ _ hψ hG
  classical
  obtain ⟨hker, art, ha, h⟩ := hG
  generalize hr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ₀ = r at h
  have hinj : ∀ g, r g = 1 ↔ ψ₀ g = 1 := fun g => by
    rw [← hr, MonoidHom.comp_apply]
    exact map_eq_one_iff _ (Units.map_injective (f := D.what₂.embLL.toMonoidHom) D.what₂.embLL.injective)
  have hrker : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := by
    convert hker using 1
    ext g
    exact hinj g
  have hrc : Continuous r := GlobalTheory.HeckeGal.continuous_of_isOpen_ker' r hrker
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, hc1, hcm, hrr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
    obtain ⟨j, hj⟩ := D.ntw.cc_cm.1
    have h1 : ∀ x : D.host.E, D.ntw.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (c x) := fun x => by
      apply j.injective
      rw [hj, hc1]
      exact (D.host.conjE_apply (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
    have h2 : ∀ x, D.ntw.cc (D.ntw.cc x) = x := fun x => j.injective (by rw [hj, hj, Complex.conj_conj])
    have hinv : ∀ x, c (c x) = x := fun x => (algebraMap D.host.E D.nd.Om).injective (by rw [← h1, ← h1, h2])
    have hc : ∀ x : D.host.E, ∃ y : D.host.E, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y :=
      fun x => ⟨c x, by rw [RingEquiv.symm_apply_eq, h1, hinv]⟩
    choose bar hbar using fun v => (GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv v).exists
    have hbb : ∀ v, bar (bar v) = v := fun v =>
      (GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv (bar v)).unique (hbar _) (GlobalTheory.AntiLAdic.conjPl_symm hinv (hbar v))
    let T := (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
    have key : r * r.comp (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc) = 1 := by
      refine GlobalTheory.FrobDense.eq_one_of_frob D.host.E D.nd.Om art ha ℂˣ _
        (hrc.mul (hrc.comp (GlobalTheory.AntiLAdic.continuous_conjHom D.ntw.cc hc))) (T ∪ T.image bar) fun v hv A hA σ hσ => ?_
      rw [Finset.mem_union, not_or] at hv
      have a2 : χ.UnrAt v := by simpa [T] using hv.1
      have b2 : χ.UnrAt (bar v) := by
        by_contra hn
        exact hv.2 (Finset.mem_image.2 ⟨bar v, by simpa [T] using hn, hbb v⟩)
      have hA' := GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl (c := c.toRingEquiv) h1 (hbar v) hA
      have hσ' := GlobalTheory.AntiLAdic.isFrob_conjHom D.ntw.cc hc hσ
      rw [← GlobalTheory.AntiLAdic.normV_conjPl (hbar v)] at hσ'
      have e3 := GlobalTheory.AntiLAdic.val_mul_val_conj c hcm.rank hcm.ne hrr χ hψ.triv (hbar v) a2 b2
      rw [h.val_eq ha a2 hA hσ, h.val_eq ha b2 hA' hσ', ← mul_inv, inv_eq_one] at e3
      show r σ * r (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc σ) = 1
      exact e3
    intro g g' hg
    have e : g' = GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc g := AlgEquiv.ext hg
    have k : r g * r (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc g) = 1 := DFunLike.congr_fun key g
    rw [← map_mul, hinj, map_mul, ← e] at k
    exact eq_inv_of_mul_eq_one_right k
  · intro v A hA
    rw [← not_iff_not, not_exists]
    simp only [not_and, not_not]
    rw [Finset.mem_coe, ← hψ.ram v, h.unr_iff ha hA]
    exact forall₂_congr fun σ _ => (hinj σ).symm
  · intro v hv A hA σ hσ
    rw [← hinj]
    have hcl : IsClosed ((GlobalTheory.HeckeGal.liftAb r hrc).ker : Set (Gab D.host.E D.nd.Om)) :=
      isClosed_singleton.preimage (GlobalTheory.HeckeGal.continuous_liftAb r hrc)
    have hle : (art.comp (Neutral.B1.localIdele D.host.E v)).range ≤ (GlobalTheory.HeckeGal.liftAb r hrc).ker := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨τ, hτ⟩ := GlobalTheory.HeckeGal.toAb_surjective (art (Neutral.B1.localIdele D.host.E v x))
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hτ, GlobalTheory.HeckeGal.liftAb_toAb, ← h _ τ hτ.symm]
      exact hψ.atl v hv x
    have hm : GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ ∈ (GlobalTheory.HeckeGal.liftAb r hrc).ker := by
      refine Subgroup.topologicalClosure_minimal _ hle hcl ?_
      rw [ha.dec v A hA]
      exact ⟨σ, hσ, rfl⟩
    rwa [MonoidHom.mem_ker, GlobalTheory.HeckeGal.liftAb_toAb] at hm

end GlobalTheory.GalTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorNotMemTwistPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.Mem.PdNotType

theorem pD_not_type : ∀ (D : D7) (i : D.ntw.Tw) (P : PlE D.host) (k : Fin 2), P ∈ D.ntw.pD i →
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro D i P k hP
  intro hg
  have hPs : P ∈ (D.ntw.pD i : Set (HeightOneSpectrum (𝓞 D.host.E))) := hP
  rw [D.ntw.pD_eq i] at hPs
  have hPg : P ∈ placesOver D.host.E (D.host.g k) := by
    simpa [placesOver] using hg
  split_ifs at hPs
  · exact GlobalTheory.InertialTypes.not_mem_placesOver_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 hPs hPg
  · exact GlobalTheory.InertialTypes.not_mem_placesOver_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 hPs hPg

end GlobalTheory.Mem.PdNotType
end

