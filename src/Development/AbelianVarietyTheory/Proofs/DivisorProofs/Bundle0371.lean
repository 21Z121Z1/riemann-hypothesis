import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairPowerSumValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0333
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChainsDiscBiprodDescIsIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogBasisAndVanishingAboveDimension
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

theorem IsFinCover.dlog_basis_and_vanish : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0))) ∧ ∀ q, d < q → ∀ y ∈ ⋀[K]^q Ω[K⁄k], y = 0 := by
  intro k _ _ F K _ _ _ _ _ _ d x h
  obtain ⟨b, hb⟩ := h.exists_basis
  have hu : ∀ j : Fin d, (algebraMap F K (x j.succ / x 0))⁻¹ ≠ 0 := fun j =>
    inv_ne_zero ((map_ne_zero _).2 (div_ne_zero (h.pd.ne _) (h.pd.ne 0)))
  haveI : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis b
  refine ⟨⟨b.unitsSMul (fun j => Units.mk0 _ (hu j)), fun j => ?_⟩, fun q hq y hy => ?_⟩
  · rw [Module.Basis.unitsSMul_apply, hb]
    rfl
  · rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨m, rfl⟩ := hz
      apply AlternatingMap.map_linearDependent
      intro hli
      have h1 := hli.fintype_card_le_finrank
      rw [Module.finrank_eq_card_basis b] at h1
      simp at h1
      omega
    | zero => rfl
    | add a c _ _ ha hc => rw [ha, hc, add_zero]
    | smul r a _ ha => rw [ha, smul_zero]

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrRepEigenspacesSpanTopStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_rep_eigenspaces_span_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (⨆ σ : Λ →+* O, eig C (⇑ρ) σ) = ⊤ := by
  first | exact @GlobalTheory.eigenspaces_span_of_integral_action | exact GlobalTheory.eigenspaces_span_of_integral_action | (intros; apply GlobalTheory.eigenspaces_span_of_integral_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EilenbergZilberHomotopyEquivalence
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eilenberg_zilber_homotopy_equivalence : ∀ (R : Type) [CommRing R] (X : SimplicialObject GlobalTheory.EtC.Spc), (∃ e : HomotopyEquiv (diagCx ((freeBi R).obj X)) (tot ((freeBi R).obj X)), ∀ n : ℕ, e.hom.f n = awF _ n) → ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X), ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n := by
  first | (exact @GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains) | (exact GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains) | (intros; apply GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegralityStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_delta_qExpansion_integrality : ∀ (N : ℕ), 0 < N → ∀ F : ℍ → ℂ, (F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) → (∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ)) ∧ (∀ R : Subring ℂ, QAll (· ∈ R) N F) ∧ ∀ g : ℂ ≃+* ℂ, QConj g N F F := by
  first | exact @GlobalTheory.QFam.eis_q | exact GlobalTheory.QFam.eis_q | (intros; apply GlobalTheory.QFam.eis_q <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfWeierstrassPDerivWeierstrassPTorsionEqStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 → wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by
  first | exact @GlobalTheory.WpFam.wp_wpd_separate | exact GlobalTheory.WpFam.wp_wpd_separate | (intros; apply GlobalTheory.WpFam.wp_wpd_separate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.LinSchur

theorem dual {k : Type} [Field k] [ValuativeRel k] {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k}
    {Y : Matrix (Fin n) (Fin d) k} (hY : Y ∉ latt ψ0 n d s) :
    ∃ l : Matrix (Fin n) (Fin d) k →ₗ[k] k, (∀ Z ∈ latt ψ0 n d s, ψ0 (l Z) = 1) ∧ ψ0 (l Y) ≠ 1 := by
  rw [mem_latt] at hY
  push_neg at hY
  obtain ⟨i, j, o, ho, h⟩ := hY
  let l : Matrix (Fin n) (Fin d) k →ₗ[k] k :=
    { toFun := fun Z => o * (s * Z i j)
      map_add' := fun a b => by simp only [Matrix.add_apply]; ring
      map_smul' := fun c a => by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  exact ⟨l, fun Z hZ => hZ i j o ho, h⟩

theorem cind_mem {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {L : AddSubgroup X}
    (ho : IsOpen (L : Set X)) (hc : IsCompact (L : Set X)) (y : X) : cind L y ∈ GlobalTheory.WeilM.SB X := by
  have hK : IsOpen {Z : X | Z - y ∈ L} := ho.preimage (continuous_sub_right y)
  have hKc : IsClosed {Z : X | Z - y ∈ L} := (AddSubgroup.isClosed_of_isOpen L ho).preimage (continuous_sub_right y)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro Y
    by_cases hY : Y - y ∈ L
    · exact ⟨_, hK, hY, fun Z hZ => by simp only [cind, if_pos (show Z - y ∈ L from hZ), if_pos hY]⟩
    · exact ⟨_, hKc.isOpen_compl, hY, fun Z hZ => by simp only [cind, if_neg (show Z - y ∉ L from hZ), if_neg hY]⟩
  · have himg : {Z : X | Z - y ∈ L} = (fun Z => Z + y) '' (L : Set X) := by
      ext Z
      constructor
      · intro h
        exact ⟨Z - y, h, sub_add_cancel Z y⟩
      · rintro ⟨W, hW, rfl⟩
        show W + y - y ∈ L
        rwa [add_sub_cancel_right]
    refine IsCompact.of_isClosed_subset (himg ▸ hc.image (continuous_add_right y)) (isClosed_tsupport _)
      (closure_minimal ?_ hKc)
    intro Z hZ
    by_contra h
    exact hZ (by simp only [cind, if_neg (show Z - y ∉ L from h)])

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have e := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at e
  exact one_ne_zero e

end GlobalTheory.LinSchur

open GlobalTheory.LinSchur in

theorem GlobalTheory.LinSchur.eq_smul_of_commute : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)) (ι₂ : Xt → Matrix (Fin n) (Fin d) k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → Xt → Xt) (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  intro k _ _ _ _ n d Xt _ _ V ψ0 hcont hne ι₁ ι₂ hbij hlin Tr Mu hTr hMu
  classical
  obtain ⟨hLoc, hBasis⟩ := GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis n d ψ0 hcont hne
  have inj : ∀ x ∈ V, ∀ y ∈ V, ι₁ x = ι₁ y → x = y := fun x hx y hy h => hbij.injOn hx hy h
  have surj : ∀ f ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k), ∃ x, x ∈ V ∧ ι₁ x = f := fun f hf => hbij.surjOn hf
  have maps : ∀ x ∈ V, ι₁ x ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := fun x hx => hbij.mapsTo hx
  have h20 : ι₂ 0 = 0 := by
    have e := hlin 0 V.zero_mem 0 V.zero_mem 1
    simpa using e
  have hsmul : ∀ x ∈ V, ∀ c : ℂ, ι₂ (c • x) = c • ι₂ x := by
    intro x hx c
    have e := hlin x hx 0 V.zero_mem c
    rwa [add_zero, h20, add_zero] at e
  have hsum : ∀ (F : Finset (Matrix (Fin n) (Fin d) k)) (a : Matrix (Fin n) (Fin d) k → ℂ)
      (xs : Matrix (Fin n) (Fin d) k → Xt), (∀ y ∈ F, xs y ∈ V) →
      ι₂ (∑ y ∈ F, a y • xs y) = ∑ y ∈ F, a y • ι₂ (xs y) := by
    intro F a xs hxs
    induction F using Finset.induction_on with
    | empty => simpa using h20
    | insert y F hy ih =>
      rw [Finset.sum_insert hy, Finset.sum_insert hy, hlin _ (hxs y (Finset.mem_insert_self _ _)) _
        (V.sum_mem fun z hz => V.smul_mem _ (hxs z (Finset.mem_insert_of_mem hz))),
        ih fun z hz => hxs z (Finset.mem_insert_of_mem hz)]
  have stepB : ∀ x ∈ V, ∀ C, (∀ Y, ι₁ x (Y + C) = ι₁ x Y) → ∀ Y, ι₂ x (Y + C) = ι₂ x Y := by
    intro x hx C hper Y
    obtain ⟨h1, h2, h3⟩ := hTr C x hx
    have e0 : Tr C x = x := inj _ h1 _ hx (by rw [h2]; funext Y; exact hper Y)
    have e := congrFun h3 Y
    rw [e0] at e
    exact e.symm
  have stepA : ∀ s : k, ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y → ∀ Y, Y - y ∉ latt ψ0 n d s → ι₂ x Y = 0 := by
    intro s x hx y hxy Y hY
    obtain ⟨l, hl1, hl2⟩ := dual hY
    obtain ⟨m1, m2, m3⟩ := hMu l x hx
    have e1 : ι₁ (Mu l x) = ι₁ (ψ0 (l y) • x) := by
      rw [m2, map_smul, hxy]
      funext Z
      simp only [cind, Pi.smul_apply, smul_eq_mul]
      split_ifs with hZ
      · rw [mul_one, mul_one, show l Z = l (Z - y) + l y by rw [← map_add, sub_add_cancel],
          AddChar.map_add_eq_mul, hl1 _ hZ, one_mul]
      · simp
    have e2 : Mu l x = ψ0 (l y) • x := inj _ m1 _ (V.smul_mem _ hx) e1
    have e3 := congrFun m3 Y
    rw [e2, hsmul x hx] at e3
    simp only [Pi.smul_apply, smul_eq_mul] at e3
    have hYy : ψ0 (l Y) = ψ0 (l (Y - y)) * ψ0 (l y) := by
      rw [← AddChar.map_add_eq_mul, ← map_add, sub_add_cancel]
    rw [hYy] at e3
    have e4 : ψ0 (l y) * (1 - ψ0 (l (Y - y))) * ι₂ x Y = 0 := by linear_combination e3
    rcases mul_eq_zero.mp e4 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (addChar_ne_zero ψ0 _)
      · exact absurd (sub_eq_zero.mp h).symm hl2
    · exact h
  have stepC : ∀ s : k, ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y → ι₂ x = ι₂ x y • ι₁ x := by
    intro s x hx y hxy
    funext Y
    rw [hxy]
    simp only [cind, Pi.smul_apply, smul_eq_mul]
    split_ifs with hY
    · rw [mul_one]
      have e := stepB x hx (Y - y) (fun Z => by
        rw [hxy]
        simp only [cind]
        rw [show Z + (Y - y) - y = (Z - y) + (Y - y) by abel, (latt ψ0 n d s).add_mem_cancel_right hY]) y
      rwa [add_sub_cancel] at e
    · rw [mul_zero]
      exact stepA s x hx y hxy Y hY
  have hcind : ∀ s : k, s ≠ 0 → ∀ y, cind (latt ψ0 n d s) y ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) :=
    fun s hs y => cind_mem (hLoc s hs).1 (hLoc s hs).2 y
  choose! xs hxsV hxs1 using fun s (hs : s ≠ 0) y => surj _ (hcind s hs y)
  have stepD : ∀ s : k, s ≠ 0 → ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y →
      ι₂ x = ι₂ (xs s 0) 0 • ι₁ x := by
    intro s hs x hx y hxy
    rw [stepC s x hx y hxy]
    congr 1
    obtain ⟨t1, t2, t3⟩ := hTr y x hx
    have e0 : Tr y x = xs s 0 := inj _ t1 _ (hxsV s hs 0) (by
      rw [t2, hxs1 s hs 0, hxy]
      funext Z
      simp only [cind, add_sub_cancel_right, sub_zero])
    have e := congrFun t3 0
    rw [e0, zero_add] at e
    exact e.symm
  have stepE : ∀ s : k, s ≠ 0 → ∀ x ∈ V, (∀ Y, ∀ C ∈ latt ψ0 n d s, ι₁ x (Y + C) = ι₁ x Y) →
      ι₂ x = ι₂ (xs s 0) 0 • ι₁ x := by
    intro s hs x hx hper
    obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator _ (hLoc s hs).1 (ι₁ x) (maps x hx) hper
    have hxeq : x = ∑ y ∈ F, ι₁ x y • xs s y :=
      inj _ hx _ (V.sum_mem fun y _ => V.smul_mem _ (hxsV s hs y)) (by
        rw [map_sum]
        simp only [map_smul, hxs1 s hs]
        exact hF)
    calc ι₂ x = ι₂ (∑ y ∈ F, ι₁ x y • xs s y) := congrArg ι₂ hxeq
      _ = ∑ y ∈ F, ι₁ x y • ι₂ (xs s y) := hsum F _ _ (fun y _ => hxsV s hs y)
      _ = ∑ y ∈ F, ι₁ x y • (ι₂ (xs s 0) 0 • cind (latt ψ0 n d s) y) :=
          Finset.sum_congr rfl fun y _ => by
            rw [stepD s hs (xs s y) (hxsV s hs y) y (hxs1 s hs y), hxs1 s hs y]
      _ = ι₂ (xs s 0) 0 • ∑ y ∈ F, ι₁ x y • cind (latt ψ0 n d s) y := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun y _ => smul_comm _ _ _
      _ = ι₂ (xs s 0) 0 • ι₁ x := by rw [← hF]
  have stepF : ∀ s : k, s ≠ 0 → ∀ s' : k, s' ≠ 0 →
      (latt ψ0 n d s' : Set (Matrix (Fin n) (Fin d) k)) ⊆ latt ψ0 n d s →
      ι₂ (xs s 0) 0 = ι₂ (xs s' 0) 0 := by
    intro s hs s' hs' hsub
    have e0 := stepE s' hs' (xs s 0) (hxsV s hs 0) (fun Y C hC => by
      rw [hxs1 s hs 0]
      simp only [cind, sub_zero, (latt ψ0 n d s).add_mem_cancel_right (hsub hC)])
    have e := congrFun e0 0
    rw [hxs1 s hs 0] at e
    simpa [cind] using e
  refine ⟨ι₂ (xs 1 0) 0, fun x hx => ?_⟩
  obtain ⟨⟨s, hs⟩, hper⟩ := GlobalTheory.T.exists_openSubgroup_periodic (fun s : {s : k // s ≠ 0} => latt ψ0 n d s) (fun s => (hLoc s.1 s.2).1)
    (fun W hW => by
      obtain ⟨s, hs, h⟩ := hBasis W hW
      exact ⟨⟨s, hs⟩, h⟩) (ι₁ x) (maps x hx)
  rw [stepE s hs x hx hper]
  congr 1
  obtain ⟨s'', hs'', hsub⟩ := hBasis ((latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∩ latt ψ0 n d 1)
    (inter_mem ((hLoc s hs).1.mem_nhds (latt ψ0 n d s).zero_mem) ((hLoc 1 one_ne_zero).1.mem_nhds (latt ψ0 n d 1).zero_mem))
  rw [stepF s hs s'' hs'' (fun z hz => (hsub hz).1), stepF 1 one_ne_zero s'' hs'' (fun z hz => (hsub hz).2)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvaluesStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.esymm_mem_virtualCharacters_of_powerSum_eigenvalues : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ) (x : G → Multiset ℂ), φ ∈ Virt ℂ ℂ G → (∀ (g : G) (j : ℕ), 0 < j → φ (g ^ j) = ((x g).map (· ^ j)).sum) → ∀ s : ℕ, (fun g => (x g).esymm s) ∈ Virt ℂ ℂ G := by
  first | exact @GlobalTheory.EsymmVirt.esymm_mem_virt | exact GlobalTheory.EsymmVirt.esymm_mem_virt | (intros; apply GlobalTheory.EsymmVirt.esymm_mem_virt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAtPrimeBaseChangeOfIntegralClosureEtale
section
open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem closureEtaleAt_comap_baseChange_atPrime : ∀ (A R R₁ DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R₁]
    [CommRing DA] [Algebra (GenFib A R) DA] (κ : R →+* R₁) (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    letI := closureAlg A R DA
    letI : Algebra R (Localization.AtPrime P₁) :=
      ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
    Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) := by
  intro A R R₁ DA _ _ _ _ _ _ κ P₁ _ h
  letI := closureAlg A R DA
  letI iRS : Algebra R (Localization.AtPrime P₁) :=
    ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
  have hunit : ∀ y : (P₁.comap κ).primeCompl,
      IsUnit (algebraMap R (Localization.AtPrime P₁) y) := by
    intro y
    exact IsLocalization.map_units (Localization.AtPrime P₁)
      (⟨κ y, y.2⟩ : P₁.primeCompl)
  letI : Algebra (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) :=
    (IsLocalization.lift (M := (P₁.comap κ).primeCompl) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (P₁.comap κ)) (Localization.AtPrime P₁) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsLocalization.lift_eq (M := (P₁.comap κ).primeCompl) hunit x).symm)
  haveI : Algebra.Etale (Localization.AtPrime (P₁.comap κ))
      (Localization.AtPrime (P₁.comap κ) ⊗[R] closure A R DA) := h
  haveI : Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[Localization.AtPrime (P₁.comap κ)]
      (Localization.AtPrime (P₁.comap κ) ⊗[R] closure A R DA)) :=
    Algebra.Etale.baseChange _ _ _
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime (P₁.comap κ))
      (Localization.AtPrime P₁) (Localization.AtPrime P₁) (closure A R DA))

end GlobalTheory.KeyOriginEnlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayOfIsEtaleAtOffSubmonoidStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_away_of_isEtaleAt : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (M : Submonoid R),
    (∀ (Q : Ideal C) [Q.IsPrime], (∀ m ∈ M, algebraMap R C m ∉ Q) → Algebra.IsEtaleAt R Q) →
    ∃ m ∈ M, Algebra.Etale R (Localization.Away (algebraMap R C m)) := by
  first | (exact @GlobalTheory.etale_away_of_isEtaleAt_off_submonoid) | (exact GlobalTheory.etale_away_of_isEtaleAt_off_submonoid) | (intros; apply GlobalTheory.etale_away_of_isEtaleAt_off_submonoid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullbackStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCechNerve_baseChange_isPullback : ∀ (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X), IsPullback a f' f b → ∃ m : cech f' ⟶ cech f, IsPullback m (cechAug f') (cechAug f) (sch.map b) ∧ ∀ (k : ℕ) (U : Scheme.{0}) (x : U ⟶ X') (y : Fin (k + 1) → (U ⟶ Y')) (h : ∀ i, y i ≫ f' = x), ∃ h', (m.app (op (SimplexCategory.mk (k)))).app (op U) (cechPt f' k x y h) = cechPt f k (x ≫ b) (fun i => y i ≫ a) h' := by
  first | (exact @GlobalTheory.cech_baseChange) | (exact GlobalTheory.cech_baseChange) | (intros; apply GlobalTheory.cech_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChainsDiscBiprodDescIsIsoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleChains_disc_biprod_desc_isIso : ∀ (R : Type) [CommRing R] {P₁ P₂ Q : PSh} (f₁ : P₁ ⟶ Q) (f₂ : P₂ ⟶ Q), IsIso (biprod.desc ((free R).map f₁) ((free R).map f₂)) → IsIso (biprod.desc ((chains R).map (disc.map f₁)) ((chains R).map (disc.map f₂))) := by
  first | exact @GlobalTheory.EtC.chains_disc_biprod_isIso | exact GlobalTheory.EtC.chains_disc_biprod_isIso | (intros; apply GlobalTheory.EtC.chains_disc_biprod_isIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties : ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  first | (exact @GlobalTheory.EtC.ev_basic) | (exact GlobalTheory.EtC.ev_basic) | (intros; apply GlobalTheory.EtC.ev_basic  <;> assumption)
end

