import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0012
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseOneProdIco
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

noncomputable def oneValue (q a : ℕ) : ℂ :=
  if a = 0 then 0 else ∏ i ∈ Finset.Ico 1 a, (1 - (q : ℂ) ^ i)

theorem sum_oneValue_finrank (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Fintype (Submodule F V)] :
    ∑ W : Submodule F V, oneValue (Nat.card F) (Module.finrank F W) = (Module.finrank F V : ℂ) := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h := GlobalTheory.QBinomialSum.sum_gaussian_mul_prod (Nat.card F) (Module.finrank F V)
    (fun a => Nat.card {W : Submodule F V // Module.finrank F W = a}) hq
    (fun a ha => GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases F V a ha)
  rw [← h, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.Icc 0 (Module.finrank F V))
    (g := fun W : Submodule F V => Module.finrank F W)
    (fun W _ => Finset.mem_Icc.2 ⟨Nat.zero_le _, W.finrank_le⟩)]
  have h2 : ∀ a : ℕ, ∑ W ∈ Finset.univ.filter (fun W : Submodule F V => Module.finrank F W = a),
      oneValue (Nat.card F) (Module.finrank F W) =
      (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * oneValue (Nat.card F) a := by
    intro a
    rw [Finset.sum_congr rfl (g := fun _ => oneValue (Nat.card F) a)
      (fun W hW => by rw [(Finset.mem_filter.1 hW).2]), Finset.sum_const, nsmul_eq_mul,
      Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = a}), Fintype.card_subtype]
  simp only [h2]
  symm
  refine Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) ?_ ?_
  · intro a ha
    have : a = 0 := by
      simp only [Finset.mem_sdiff, Finset.mem_Icc] at ha
      omega
    simp [this, oneValue]
  · intro a ha
    have : a ≠ 0 := by
      simp only [Finset.mem_Icc] at ha
      omega
    simp [this, oneValue]

theorem psi_one_eq_oneValue (F : Type) [Field F] [Finite F] (s : F[X] → ℂ)
    (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.finrank F V = n →
      psi s V 1 = oneValue (Nat.card F) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ hn
    classical
    haveI : Finite V := Module.finite_of_finite F
    haveI : Fintype (Submodule F V) := Fintype.ofFinite _
    have hc : LinearMap.charpoly (1 : Module.End F V) = (X - C 1) ^ n := by
      rw [LinearMap.charpoly_one, hn, C_1]
    rw [psi_eq, hc, hs]
    have h1 : ∀ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, (1 : Module.End F V) x ∈ W},
        psi s W.1 ((1 : Module.End F V).restrict W.2.2) = oneValue (Nat.card F) (Module.finrank F W.1) := by
      intro W
      have : (1 : Module.End F V).restrict W.2.2 = (1 : Module.End F W.1) := by
        ext x
        rfl
      rw [this]
      exact ih _ (hn ▸ Submodule.finrank_lt W.2.1) _ rfl
    rw [finsum_congr h1, finsum_eq_sum_of_fintype,
      ← Finset.sum_subtype (Finset.univ.erase (⊤ : Submodule F V)) (by intro W; simp)
        (fun W : Submodule F V => oneValue (Nat.card F) (Module.finrank F W))]
    have h2 := sum_oneValue_finrank F V
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⊤ : Submodule F V)), finrank_top, hn] at h2
    rw [← h2]
    ring

theorem psi_one (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (s : F[X] → ℂ) (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (h : 0 < Module.finrank F V) :
    psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by
  rw [psi_one_eq_oneValue F s hs _ V rfl, oneValue, if_neg h.ne']

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterEsymmRootsCharpoly
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

def compoundRep {G : Type} [Group G] {n : ℕ} (j : ℕ) (ρ : G →* GL (Fin n) ℂ) :
    Representation ℂ G (Set.powersetCard (Fin n) j → ℂ) where
  toFun g := Matrix.toLin' (GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ))
  map_one' := by
    rw [map_one, Units.val_one, GlobalTheory.compoundMatrix_one, Matrix.toLin'_one]; rfl
  map_mul' a b := by
    rw [map_mul, Units.val_mul, GlobalTheory.compoundMatrix_mul, Matrix.toLin'_mul]; rfl

open Polynomial in
private lemma det_submatrix_subsetEnum_eq_det_submatrix_val {n j : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (S : Set.powersetCard (Fin n) j) :
    (A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S)).det =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).det := by
  have hmem : ∀ i, _root_.GlobalTheory.subsetEnum S i ∈ S.1 := fun i => by
    have : _root_.GlobalTheory.subsetEnum S i ∈ Set.range (_root_.GlobalTheory.subsetEnum S) :=
      ⟨i, rfl⟩
    rw [_root_.GlobalTheory.range_subsetEnum] at this
    exact_mod_cast this
  let σ : Fin j ≃ {x // x ∈ S.1} := Equiv.ofBijective
    (fun i => ⟨_root_.GlobalTheory.subsetEnum S i, hmem i⟩)
    ⟨fun a b hab => _root_.GlobalTheory.subsetEnum_injective S (congrArg Subtype.val hab),
      fun x => by
        have hx : x.1 ∈ ((S.1 : Finset (Fin n)) : Set (Fin n)) := x.2
        rw [← _root_.GlobalTheory.range_subsetEnum] at hx
        obtain ⟨i, hi⟩ := hx
        exact ⟨i, Subtype.ext hi⟩⟩
  have hsub : A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S) =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).submatrix σ σ := rfl
  rw [hsub, Matrix.det_submatrix_equiv_self]

open Polynomial in
private lemma trace_compoundMatrix_eq_sum_principal_minors {n : ℕ} (j : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (_root_.GlobalTheory.compoundMatrix j A).trace = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (A.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  rw [Finset.sum_subtype (p := fun s : Finset (Fin n) => s ∈ Set.powersetCard (Fin n) j) _
    (fun s => by simp [Finset.mem_powersetCard, Set.powersetCard])]
  unfold _root_.GlobalTheory.compoundMatrix
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  exact Finset.sum_congr rfl fun S _ => det_submatrix_subsetEnum_eq_det_submatrix_val A S

open Polynomial in
private lemma esymm_roots_charpoly_eq_sum_principal_minors {n : ℕ} (j : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.roots.esymm j = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (M.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcard : M.charpoly.roots.card = M.charpoly.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits _)
  rcases le_or_gt j n with hj | hj
  · have h1 := coeff_eq_esymm_roots_of_card hcard (k := n - j) (by omega)
    have h2 := M.charpoly_coeff_eq_sum_minors j (by simp [hj])
    rw [hdeg, Nat.sub_sub_self hj, M.charpoly_monic.leadingCoeff, one_mul] at h1
    rw [Fintype.card_fin, h1] at h2
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h2
  · rw [Finset.powersetCard_eq_empty.mpr (by simp [hj]), Finset.sum_empty, Multiset.esymm,
      Multiset.powersetCard_eq_empty _ (by omega)]
    simp

open Polynomial in

theorem _root_.GlobalTheory.BI.isChar_esymm_roots_charpoly :
    ∀ (G : Type) [Group G] (n j : ℕ) (ρ : G →* GL (Fin n) ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ
      (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) := by
  intro G _ n j ρ
  have h := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (_root_.GlobalTheory.BI.compoundRep j ρ)).1
  have heq : (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) =
      fun g => algebraMap ℂ ℂ ((_root_.GlobalTheory.BI.compoundRep j ρ).character g) := by
    funext g
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    change _ = LinearMap.trace ℂ _
      (Matrix.toLin' (_root_.GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ)))
    rw [Matrix.trace_toLin'_eq, trace_compoundMatrix_eq_sum_principal_minors, esymm_roots_charpoly_eq_sum_principal_minors]
  rw [heq]
  exact h

end GlobalTheory.BI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveExtendZeroOfSumUnipotentRadical
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL

theorem exists_linearEquiv_mem_iff_of_finrank_eq {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A B : Submodule F V) (h : Module.finrank F A = Module.finrank F B) :
    ∃ e : V ≃ₗ[F] V, ∀ x, e x ∈ B ↔ x ∈ A := by
  obtain ⟨A', hA⟩ := A.exists_isCompl
  obtain ⟨B', hB⟩ := B.exists_isCompl
  have h' : Module.finrank F A' = Module.finrank F B' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hA
    have h2 := Submodule.finrank_add_eq_of_isCompl hB
    omega
  let e1 := LinearEquiv.ofFinrankEq A B h
  let e2 := LinearEquiv.ofFinrankEq A' B' h'
  refine ⟨(Submodule.prodEquivOfIsCompl A A' hA).symm ≪≫ₗ (e1.prodCongr e2) ≪≫ₗ
    Submodule.prodEquivOfIsCompl B B' hB, fun x => ?_⟩
  obtain ⟨⟨a, a'⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A A' hA).surjective x
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  simp only [LinearEquiv.prodCongr_apply, Submodule.coe_prodEquivOfIsCompl']
  rw [B.add_mem_iff_right (e1 a).2, A.add_mem_iff_right a.2,
    Submodule.mem_left_iff_eq_zero_of_disjoint hB.disjoint,
    Submodule.mem_left_iff_eq_zero_of_disjoint hA.disjoint]
  simp

theorem finsum_nilRad_extZero_eq_zero (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ)
    (hχ : IsChar ℂ ℂ χ) (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F))
    (hb : Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1)
      (H : Set (GL (Fin d) F)) (nilRad A))
    (h0 : ∑ᶠ u ∈ (H : Set (GL (Fin d) F)), χ u = 0)
    (g : Module.End F (Fin d → F)) (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ h ∈ nilRad A, extZero χ (g + h) = 0 := by
  obtain ⟨e1, e2, -, -⟩ := GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ
  by_cases hu : IsUnit g
  · have hm : IsUnit (LinearMap.toMatrix' g) := by
      have := hu.map (LinearMap.toMatrixAlgEquiv' (R := F) (n := Fin d))
      exact this
    obtain ⟨x, hx⟩ := hm
    have hgx : Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g := by
      rw [hx, Matrix.toLin'_toMatrix']
    have : Finite (Module.End F (Fin d → F)) := Module.finite_of_finite F
    have hb2 : Set.BijOn (fun h : Module.End F (Fin d → F) => g * h) (nilRad A) (nilRad A) := by
      refine ((Set.toFinite _).injOn_iff_bijOn_of_mapsTo ?_).1 ?_
      · intro h hh
        exact ⟨fun y => hg _ (hh.1 y), fun y hy => by simp [hh.2 y hy]⟩
      · intro a _ b _ hab
        exact hu.mul_left_cancel hab
    have h1 := GlobalTheory.T.character_coset_sum_eq_zero_of_subgroup_sum _ χ hχ H
      ((finsum_set_coe_eq_finsum_mem (f := χ) (H : Set (GL (Fin d) F))).trans h0) x
    have h2 := (finsum_set_coe_eq_finsum_mem (f := fun u => χ (x * u)) (H : Set (GL (Fin d) F))).symm.trans h1
    rw [← h2]
    symm
    refine finsum_mem_eq_of_bijOn _ (hb2.comp hb) fun u _ => ?_
    rw [← e1]
    congr 1
    simp only [Function.comp, Units.val_mul, Matrix.toLin'_mul, hgx, mul_sub, mul_one]
    rw [add_sub_cancel]
    rfl
  · refine finsum_mem_of_eqOn_zero fun h hh => ?_
    refine e2 _ fun hu' => hu ?_
    have hc := (GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F _ A g hg).2 h hh
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff] at hu' ⊢
    rwa [hc] at hu'

theorem isPrimitive_extZero_of_sum_unipotent : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), IsChar ℂ ℂ χ → (∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, χ u = 0) → IsPrimitive (extZero χ) := by
  intro F _ _ d χ hχ hs A hA0 hA1 g hg
  have ha0 : 0 < Module.finrank F A := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h => hA0 (Submodule.finrank_eq_zero.1 h)
  have ha1 : Module.finrank F A < d := by
    have := Submodule.finrank_lt hA1
    simpa using this
  obtain ⟨B, H, hB, hH, hb⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F d _ ha1.le
  have h0 := hs _ ha0 ha1
  rw [← hH] at h0
  obtain ⟨e, he⟩ := exists_linearEquiv_mem_iff_of_finrank_eq A B hB.symm
  have hcl := (GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ).2.2.2 (GlobalTheory.isChar_restrict_conj_one ℂ ℂ _ χ hχ).2.1
  have key := finsum_nilRad_extZero_eq_zero F d χ hχ B H hb h0 (e.conj g) (fun x hx => by
    rw [LinearEquiv.conj_apply_apply, he]
    apply hg
    rw [← he]
    simpa using hx)
  rw [← key]
  refine finsum_mem_eq_of_bijOn (fun h => e.conj h) ⟨fun h hh => ⟨fun y => ?_, fun y hy => ?_⟩,
    e.conj.injective.injOn, fun h hh => ⟨e.symm.conj h, ⟨fun y => ?_, fun y hy => ?_⟩, by ext y; simp [LinearEquiv.conj_apply_apply]⟩⟩ fun h _ => ?_
  · rw [LinearEquiv.conj_apply_apply, he]
    exact hh.1 _
  · rw [LinearEquiv.conj_apply_apply, hh.2 _ (by rw [← he]; simpa using hy), map_zero]
  · rw [← he, LinearEquiv.conj_apply_apply]
    simpa using hh.1 _
  · rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, hh.2 _ ((he y).2 hy), map_zero]
  · rw [← map_add, hcl]

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharacters
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem mem_virt_iff_sub (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L) :
    f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by
  obtain ⟨h0, hadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G
  unfold Virt
  constructor
  · intro hf
    induction hf using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨x, 0, hx, h0, (sub_zero x).symm⟩
    | zero => exact ⟨0, 0, h0, h0, (sub_zero 0).symm⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ihx
      obtain ⟨c, d, hc, hd, rfl⟩ := ihy
      exact ⟨a + c, b + d, hadd a c ha hc, hadd b d hb hd, by abel⟩
    | neg x _ ih =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ih
      exact ⟨b, a, hb, ha, by abel⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure ha) (AddSubgroup.subset_closure hb)
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.OrthogonalIntVectorsNotAgreeOnRegular
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

private lemma abs_sum_le_sum_sq_int (s : Finset ℕ) (a : ℕ → ℤ) :
    |∑ k ∈ s, a k| ≤ ∑ k ∈ s, a k ^ 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rcases eq_or_ne (a k) 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |a k| := Int.one_le_abs h
    nlinarith [sq_abs (a k)]

theorem orthogonal_int_vectors_not_agree_on_regular :
    ∀ (q n : ℕ) (ω : ℂ) (a b : ℕ → ℤ), 2 ≤ q → 0 < n → IsPrimitiveRoot ω (q ^ n - 1) → ∑ k ∈ Finset.range (q ^ n - 1), a k ^ 2 = n → ∑ k ∈ Finset.range (q ^ n - 1), b k ^ 2 = n → ∑ k ∈ Finset.range (q ^ n - 1), a k * b k = 0 → 0 < (∑ k ∈ Finset.range (q ^ n - 1), a k) * (∑ k ∈ Finset.range (q ^ n - 1), b k) → (∀ j : ℕ, (∀ e : ℕ, 0 < e → e < n → ¬ j * q ^ e ≡ j [MOD q ^ n - 1]) → ∑ k ∈ Finset.range (q ^ n - 1), (a k : ℂ) * ω ^ (j * k) = ∑ k ∈ Finset.range (q ^ n - 1), (b k : ℂ) * ω ^ (j * k)) → False := by
  intro q n ω a b hq hn hω ha2 hb2 hab hpos hreg
  have hN : 0 < q ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' (by omega))
  have hc2 : ∑ k ∈ Finset.range (q ^ n - 1), (a k - b k) ^ 2 = 2 * (n : ℤ) := by
    have e : ∀ k, (a k - b k) ^ 2 = a k ^ 2 + b k ^ 2 - 2 * (a k * b k) := fun k => by ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ha2, hb2, hab]
    ring
  have hcoef : ∀ j : ℕ, (∀ e : ℕ, 0 < e → e < n → ¬ j * q ^ e ≡ j [MOD q ^ n - 1]) →
      ∑ k ∈ Finset.range (q ^ n - 1), (((a k - b k : ℤ)) : ℂ) * ω ^ (j * k) = 0 := by
    intro j hj
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, hreg j hj, sub_self]
  by_cases hexc : q = 2 ∧ (n = 4 ∨ n = 6)
  · obtain ⟨rfl, rfl | rfl⟩ := hexc
    · refine GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15 ω (fun k => a k - b k) (by simpa using hω) (by simpa using hc2)
        (fun j hj h5 => by
          simpa using hcoef j (fun e he1 he2 => by
            revert h5
            interval_cases j <;> interval_cases e <;> decide))
    · refine GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63 ω (fun k => a k - b k) (by simpa using hω) (by simpa using hc2)
        (fun j hj h21 h9 => by
          simpa using hcoef j (fun e he1 he2 => by
            revert h21 h9
            interval_cases j <;> interval_cases e <;> decide))
  · have hsum : |∑ k ∈ Finset.range (q ^ n - 1), (a k - b k)| ≤ (n : ℤ) - 1 := by
      rw [Finset.sum_sub_distrib]
      have hA := abs_le.mp ((abs_sum_le_sum_sq_int _ a).trans ha2.le)
      have hB := abs_le.mp ((abs_sum_le_sum_sq_int _ b).trans hb2.le)
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact abs_le.mpr ⟨by omega, by omega⟩
    have h1 := GlobalTheory.T.parseval_bound_integerVector_smallFourierSupport n (q ^ n - 1) ω (fun k => a k - b k)
      ((Finset.Ioo 0 (q ^ n - 1)).filter
        (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1]))
      hn hN hω hc2 hsum (fun j hj0 hjN hjS => by
        refine hcoef j (fun e he1 he2 he => hjS ?_)
        simp only [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨hj0, hjN⟩, e, ⟨he1, he2⟩, he⟩)
    have h2 := GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le q n hq hn
    have h3 := GlobalTheory.T.separation_numerical_ineq_cuspidalGL q n hq hn hexc
    exact absurd (lt_of_le_of_lt (h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _)) h3)
      (lt_irrefl _)

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.TraceLiftMonomialMatrixEqSumEigenvalues
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.MonoTrace

theorem ncard_pow_eq_one (k : Type) [Field k] [IsAlgClosed k] (N : ℕ) (hN : (N : k) ≠ 0) :
    {μ : k | μ ^ N = 1}.Finite ∧ {μ : k | μ ^ N = 1}.ncard = N := by
  haveI : NeZero (N : k) := ⟨hN⟩
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  have hs : {μ : k | μ ^ N = 1} = (nthRootsFinset N (1 : k) : Set k) := by
    ext x
    simp [mem_nthRootsFinset (Nat.pos_of_ne_zero hN0)]
  rw [hs]
  exact ⟨Finset.finite_toSet _, by rw [Set.ncard_coe_finset, hζ.card_nthRootsFinset]⟩

theorem bijOn_pow_eq_one (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ)
    (hθ : ∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (N : ℕ) (hN : (N : k) ≠ 0) :
    Set.BijOn θ {μ : k | μ ^ N = 1} {μ : ℂ | μ ^ N = 1} := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hne : ∀ μ : k, μ ^ N = 1 → μ ≠ 0 := by
    rintro μ h rfl
    simp [hN0] at h
  have hmaps : Set.MapsTo θ {μ : k | μ ^ N = 1} {μ : ℂ | μ ^ N = 1} := by
    intro μ h
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [← map_pow, h, map_one]
  have hinj : Set.InjOn θ {μ : k | μ ^ N = 1} :=
    fun x hx y hy h => hθ x y (hne x hx) (hne y hy) h
  obtain ⟨_, h1⟩ := ncard_pow_eq_one k N hN
  obtain ⟨f2, h2⟩ := ncard_pow_eq_one ℂ N (by exact_mod_cast hN0)
  have himg : θ '' {μ : k | μ ^ N = 1} = {μ : ℂ | μ ^ N = 1} := by
    apply Set.eq_of_subset_of_ncard_le hmaps.image_subset _ f2
    rw [hinj.ncard_image, h1, h2]
  exact ⟨hmaps, hinj, himg.ge⟩

theorem trace_lift_monomial : ∀ (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (n N : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → k), (∀ j, c j ≠ 0) → (N : k) ≠ 0 → (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k) ^ N = 1 → (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) ^ N = 1 → Matrix.trace (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) = ((Matrix.charpoly (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k)).roots.map θ).sum := by
  intro k _ _ θ hθ n N σ c hc hN hA hB
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hE := GlobalTheory.T.finrank_eigenspace_monomial_matrix_lift k θ hθ n σ c hc
  set A : Matrix (Fin n) (Fin n) k := Matrix.of fun i j => if i = σ j then c j else 0 with hAdef
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if i = σ j then θ (c j) else 0 with hBdef
  have h1 := GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank k (Fin n → k) (Matrix.toLin' A) N hN
    (by rw [← Matrix.toLin'_pow, hA, Matrix.toLin'_one]; rfl) θ
  have h2 := GlobalTheory.T.sum_charpoly_roots_eq_finsum_eigenspace_finrank ℂ (Fin n → ℂ) (Matrix.toLin' B) N (by exact_mod_cast hN0)
    (by rw [← Matrix.toLin'_pow, hB, Matrix.toLin'_one]; rfl) id
  rw [Matrix.charpoly_toLin'] at h1 h2
  rw [Matrix.trace_eq_sum_roots_charpoly, h1]
  rw [Multiset.map_id] at h2
  rw [h2]
  symm
  apply finsum_mem_eq_of_bijOn θ (bijOn_pow_eq_one k θ hθ N hN)
  intro μ hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp [hN0] at hμ
  rw [hE μ hμ0]
  rfl

end GlobalTheory.MonoTrace
end

