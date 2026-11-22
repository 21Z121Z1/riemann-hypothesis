import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0257
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0357
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.EmbeddingValuationsAnti
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormConstantCoeffEqOneOfEisensteinFrobeniusCycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultVTwistedDual
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.DualJump

open GlobalTheory.DRFil GlobalTheory.DRDual

theorem multV_twisted_dual {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
    [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V')
    (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ) (hm : Function.Bijective m)
    (hg : ∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y)
    (h : IsDR (P.PD K) ρ) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) :
    multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  have := K.2
  have := LL.2
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  have hs := filSpans T K LL ρ h
  let ρ₀ : Representation ↥LL.1 ↥(GK K) V' := twistRep (cycLL (P.PD K) ↥LL.1 ^ (-j)) ρ'
  have hρ₀ : ∀ g y, ρ₀ g y = ((cycLL (P.PD K) ↥LL.1 g ^ (-j) : (↥LL.1)ˣ) : ↥LL.1) • ρ' g y :=
    fun g y => rfl
  have hβ : ∀ g x y, m (ρ g x) (ρ₀ g y) = m x y := fun g x y => by
    rw [hρ₀, map_smul, hg, smul_eq_mul, zpow_neg, Units.inv_mul_cancel_left]
  have hβ' : Function.Bijective m.flip := (LinearEquiv.ofBijective m hm).flip.bijective
  have ht : (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K : P.R.BdR) = (P.PD K).ι (P.PD K).t := rfl
  obtain ⟨-, h2⟩ := twist_unit (P.PD K) ρ₀ ρ' (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K ^ (-j)) (-j)
    (fun g => (P.PD K).χ g ^ (-j)) (tdR_zpow_mem T K _)
    (by rw [← zpow_neg]; exact tdR_zpow_mem T K _) (act_zpow _ _ ht _)
    (fun g => by rw [← zpow_neg, ← zpow_neg]; exact act_zpow _ _ ht _ g)
    (fun g x => by
      rw [hρ₀, ← algebraMap_smul ↥LL.1]
      congr 1
      exact congrArg Units.val
        (map_zpow (Units.map (algebraMap ℚ_[l] ↥LL.1 : ℚ_[l] →* ↥LL.1)) ((P.PD K).χ g) (-j)))
  obtain ⟨n, d, k, had⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (isField_dR T) ρ hs τ
  obtain ⟨d', had'⟩ := had.dual ρ₀ m hβ hβ'
  rw [show -a - j = -j + -a by ring, h2, had.multV_eq, had'.multV_eq]
  simp only [neg_inj]

theorem dualJumpL : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → DualJumpL L := by
  intro L AI hT l _ K LL A A' m hm h τ a
  obtain ⟨T⟩ := hT l
  obtain ⟨hg, h1, -, hd⟩ := hm
  have hi : Function.Injective m :=
    (injective_iff_map_eq_zero m).2 fun x hx => h1 x fun y => by rw [hx, LinearMap.zero_apply]
  have hb : Function.Bijective m :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hd.trans (Subspace.dual_finrank_eq (K := ↥LL.1) (V := A'.V)).symm)).1 hi⟩
  have key := multV_twisted_dual T K LL A.ρ A'.ρ m 1 hb (fun g x y => by rw [zpow_one]; exact hg g x y) h τ (-a - 1)
  rw [show -(-a - 1) - 1 = a by ring] at key
  rw [(GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (L l) (AI l) T K LL A'.V A'.ρ τ a).2.2,
    (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (L l) (AI l) T K LL A.V A.ρ τ (-a - 1)).2.2, key]

end GlobalTheory.DualJump
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardGenericIrreducibleCharactersGLnLe
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.GenericCount

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem ip_comm {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ip α β = ip β α := by
  unfold ip
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun x => by simp [mul_comm])

theorem tr_finset_sum {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (S : Finset (G → ℂ))
    (c : (G → ℂ) → ℂ) : tr a (∑ ρ ∈ S, c ρ • ρ) = ∑ ρ ∈ S, c ρ * tr a ρ := by
  unfold tr
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun x _ => by ring

theorem gg_isClass {g : ℕ} [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : IsClass (gg ψ n) := by
  intro x z
  simp only [gg]
  congr 1
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft z) _ _ (fun y => ?_)
  have h : (z * y)⁻¹ * (z * x * z⁻¹) * (z * y) = y⁻¹ * x * y := by group
  simp only [Equiv.coe_mulLeft, h]

end GlobalTheory.GLq.GenericCount

namespace GlobalTheory.GLq

open GlobalTheory.GLq.GenericCount in

theorem card_generic_irr_le : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n →
    Set.ncard {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0} ≤ g ^ n - g ^ (n - 1) := by
  intro g _ ψ hψ n hn
  obtain ⟨hfin, -⟩ := GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)
  set S := hfin.toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ IsIrr ρ := fun ρ => by rw [hS, Set.Finite.mem_toFinset]; rfl
  have hnorm := GlobalTheory.T.gelfandGraevCharacterGLn_norm_and_reciprocity g ψ hψ n hn
  have hdec := (GlobalTheory.T.character_decomposition_and_classFunction_expansion (Gn g n) (gg ψ n)).2.1 (gg_isClass ψ n)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hdec
  have hirrC : ∀ ρ : Gn g n → ℂ, IsIrr ρ → IsClass ρ := fun ρ h =>
    (GlobalTheory.T.character_decomposition_and_classFunction_expansion (Gn g n) ρ).2.2.1 (isChar_of_isIrr h)
  have hnat : ∀ ρ : Gn g n → ℂ, IsIrr ρ → ∃ m : ℕ, wh ψ ρ = m := fun ρ h =>
    (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g n) (eU g n ψ) ρ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g n 0 0 ψ).1 (isChar_of_isIrr h)
  choose! m hm using hnat
  have hsum : ((∑ ρ ∈ S, m ρ ^ 2 : ℕ) : ℂ) = ((g ^ n - g ^ (n - 1) : ℕ) : ℂ) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) (Nat.sub_le n 1))]
    push_cast
    rw [← hnorm.1]
    have hw : wh ψ (gg ψ n) = ∑ ρ ∈ S, ip (gg ψ n) ρ * wh ψ ρ := by
      conv_lhs => rw [hdec]
      unfold wh
      exact tr_finset_sum _ _ _
    rw [hw]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hI := (hmemS ρ).1 hρ
    rw [ip_comm, hnorm.2 ρ (hirrC ρ hI), hm ρ hI]
    ring
  have hsumN : ∑ ρ ∈ S, m ρ ^ 2 = g ^ n - g ^ (n - 1) := by exact_mod_cast hsum
  have hset : {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0} = ↑(S.filter fun ρ => m ρ ≠ 0) := by
    ext ρ
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hmemS]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h0 => h2 (by rw [hm ρ h1, h0, Nat.cast_zero])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h0 => h2 (by rw [hm ρ h1] at h0; exact_mod_cast h0)⟩
  rw [hset, Set.ncard_coe_finset, ← hsumN, Finset.card_eq_sum_ones]
  calc ∑ ρ ∈ S.filter (fun ρ => m ρ ≠ 0), 1 ≤ ∑ ρ ∈ S.filter (fun ρ => m ρ ≠ 0), m ρ ^ 2 :=
        Finset.sum_le_sum fun ρ hρ => Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (Finset.mem_filter.1 hρ).2)
    _ ≤ ∑ ρ ∈ S, m ρ ^ 2 := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end GlobalTheory.GLq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvTateDual
section
noncomputable section

namespace GlobalTheory.TateDualInv

section Bridge

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
open ReciprocityTheory.Gal (cycZ)

variable {l : ℕ} [Fact l.Prime]

theorem isJumpV_zero_of_invariant (P : LocPrime l) (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (x : V) (hx : x ≠ 0)
    (h : ∀ g, ρ g x = x) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : IsJumpV (P.PD K) ρ τ 0 := by
  have := LL.2
  refine GlobalTheory.HTW.isJumpV_of_injective (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) ρ
    (LinearMap.toSpanSingleton ↥LL.1 V x) (LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton _ hx))
    (fun g v => by simp [h]) τ 0 fun h0 => ?_
  have h1 := GlobalTheory.CrysExt.finrank_fildR_trivial (P.PD K) (LL := ↥LL.1) τ 0
  have h2 := GlobalTheory.CrysExt.finrank_fildR_trivial (P.PD K) (LL := ↥LL.1) τ (0 + 1)
  rw [h0, h1] at h2
  simp at h2

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycLL_eq (g : ↥(GK Bw.Kw)) :
    ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 g : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (Bw.e.symm g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l])) := by
  change algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
  rw [P.PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi Bw P g]
  exact (congrArg Subtype.val (Bw.eO_alg _)).symm

theorem dot_dual {O L : Type} [CommRing O] [CommRing L] (φ : O →+* L) {m : ℕ} (A : GL (Fin m) O) (ε : O)
    (x y : Fin m → L) :
    ((A : Matrix (Fin m) (Fin m) O).map φ).mulVec x ⬝ᵥ
      ((ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ).mulVec y = φ ε * (x ⬝ᵥ y) := by
  have h1 : (ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ =
      φ ε • (((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ).transpose := by
    ext a b
    simp
  have h2 : ((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ * (A : Matrix (Fin m) (Fin m) O).map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.coe_units_inv, Units.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]
  rw [h1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

omit [IsAlgClosed Ω] in
theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl

omit [IsAlgClosed Ω] in
theorem card_emb : Nat.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1) = Module.finrank ℚ_[l] ↥Bw.Kw.1 := by
  have : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  rw [← AlgHom.card ℚ_[l] ↥Bw.Kw.1 (Loc.Om l), ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun τ => Bw.LL.1.val.comp τ
      invFun := fun τ => τ.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split τ)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem dot_bijective {L : Type} [Field L] (m : ℕ) :
    Function.Bijective (dotProductBilin L L : (Fin m → L) →ₗ[L] (Fin m → L) →ₗ[L] L) := by
  have hi : Function.Injective (dotProductBilin L L : (Fin m → L) →ₗ[L] (Fin m → L) →ₗ[L] L) := by
    intro x y h
    funext i
    simpa using LinearMap.congr_fun h (Pi.single i 1)
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hi⟩

theorem local_noInv (AI : LocAinf l P) (T : LocTied l P AI) {m : ℕ} (r r' : ↥Gw →* GL (Fin m) O)
    (hd : ∀ g, ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O) =
      algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]) •
        ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)⁻¹.transpose)
    (hdR : Bw.IsdRW P r) (hj : ∀ τ, ¬ IsJumpV (P.PD Bw.Kw) (Bw.rep r) τ (-1))
    (x : Fin m → ↥Bw.LL.1) (hx : ∀ g, Bw.rep r' g x = x) : x = 0 := by
  by_contra h0
  have : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hc := card_emb Bw
  obtain ⟨⟨τ⟩, -⟩ := Nat.card_pos_iff.1 (hc ▸ Module.finrank_pos (R := ℚ_[l]) (M := ↥Bw.Kw.1))
  have hJ := isJumpV_zero_of_invariant P Bw.Kw Bw.LL (Bw.rep r') x h0 hx τ
  have hm := (GlobalTheory.DRDual.twisted_dual_deRham l P AI T Bw.Kw Bw.LL _ (Bw.rep r) _ (Bw.rep r')
    (dotProductBilin _ _) 1 (dot_bijective m) (fun g x y => by
      rw [zpow_one, cycLL_eq, rep_apply, rep_apply, hd]
      exact dot_dual _ _ _ _ _) (by simpa [IsDR, LocBridge.IsdRW] using hdR)).2 τ (-1) hc
  have h1 : multV (P.PD Bw.Kw) (Bw.rep r) τ (-1) = 0 := by
    unfold multV
    rw [not_not.1 (hj τ), sub_self]
  rw [h1, show -(-1 : ℤ) - 1 = 0 by norm_num] at hm
  apply hJ
  have hfin := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T Bw.Kw Bw.LL _ (Bw.rep r')).1
  have hle : FildR (P.PD Bw.Kw) (Bw.rep r') τ 0 ≤ DdR (P.PD Bw.Kw) (Bw.rep r') := le_trans inf_le_left inf_le_left
  have := Submodule.finiteDimensional_of_le hle
  refine Submodule.eq_of_le_of_finrank_eq (inf_le_inf_left _ ?_) ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => exact ⟨v ⊗ₜ[ℚ_[l]] ⟨b.1, (P.PD Bw.Kw).Fil_anti 0 b.2⟩, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · unfold multV at hm
    omega

end Bridge

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

section Global

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def dualHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun := Tdual i s
  map_one' := by simp [Tdual, ← Tgl_coe]
  map_mul' g h := by
    simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, smul_mul_smul_comm]

end Global

open scoped Pointwise in

theorem noInv_tateDual : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) → HodgeL bkP i s → NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tdual i s) v := by
  rintro D bkP i s ⟨AI, ⟨T⟩⟩ hH hJ v hv A hA x hx
  let φ := algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
  let M : Gen.GE D.nd → Matrix (Fin D.R.r) (Fin D.R.r) (FractionRing (D.ntw.O0 i)) := fun g => (Tdual i s g).map φ
  have hmul : ∀ g h, M (g * h) = M g * M h := fun g h => by
    simp only [M, ← Matrix.map_mul]
    exact congrArg (fun Y => Matrix.map Y φ) ((dualHom i s).map_mul g h)
  have hone : M 1 = 1 := by
    have : Tdual i s 1 = 1 := (dualHom i s).map_one
    simp only [M, this, Matrix.map_one _ φ.map_zero φ.map_one]
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hA (D.nd.plOm.2 v)
  have hy : ∀ g ∈ DecV D.nd v, (M g).mulVec ((M k).mulVec x) = (M k).mulVec x := by
    intro g hg
    have h1 : k⁻¹ * g * k ∈ Dec (F := D.host.E) A := by
      have hg' : g • D.nd.plOm.1 v = D.nd.plOm.1 v := hg
      change (k⁻¹ * g * k) • A = A
      rw [mul_smul, mul_smul, hk, hg', ← hk, inv_smul_smul]
    have h2 : (M (k⁻¹ * g * k)).mulVec x = x := hx _ h1
    conv_rhs => rw [← h2]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hmul, ← hmul]
    congr 2
    group
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  let Bw := bkP.br i v hv
  have hz := local_noInv Bw (D.loc (D.ntw.l i)) AI T ((Tgl i s).comp (DecV D.nd v).subtype)
    ((dualHom i s).toHomUnits.comp (DecV D.nd v).subtype)
    (fun g => by
      change Tdual i s g = _ • (((Tgl i s g : GL (Fin D.R.r) (D.ntw.O0 i)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)))⁻¹.transpose
      rw [Tgl_coe]
      rfl)
    (hH v hv _ (Set.mem_insert_of_mem _ rfl)).1
    (fun τ h => by
      have := hJ v hv τ (-1) h
      omega)
    (fun a => Br.toLLK Bw ((M k).mulVec x a)) (fun g => by
      rw [rep_apply]
      funext a
      have h3 := congrArg (Br.toLLK Bw) (congrFun (hy _ (Bw.e.symm g).2) a)
      rw [← h3, RingHom.map_mulVec]
      congr 1
      ext b c
      exact congrArg Subtype.val (Br.toLLK_alg Bw _).symm)
  have h4 : (M k).mulVec x = 0 := funext fun a => (Br.toLLK Bw).injective (by
    rw [Pi.zero_apply, map_zero]; exact congrFun hz a)
  have h5 := congrArg (M k⁻¹).mulVec h4
  rwa [Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel, hone, Matrix.one_mulVec, Matrix.mulVec_zero] at h5

end GlobalTheory.TateDualInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoMonodromyOfInertiaSeparableCharpoly
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

namespace GlobalTheory.WeilDeligne

theorem eq_zero_of_commute_of_separable {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {f N : Module.End ℂ V} (hf : f.charpoly.Separable)
    (hc : Commute f N) (hN : IsNilpotent N) : N = 0 := by
  obtain ⟨k, hk⟩ := hN

  have hline : ∀ μ : ℂ, ∀ v ∈ f.maxGenEigenspace μ, N v = 0 := by
    intro μ
    have hdim : Module.finrank ℂ (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hf μ
    obtain ⟨v₀, hv₀⟩ := finrank_le_one_iff.mp hdim
    have hgen : ∀ v ∈ f.maxGenEigenspace μ, ∃ c : ℂ, v = c • (v₀ : V) := by
      intro v hv
      obtain ⟨c, hcv⟩ := hv₀ ⟨v, hv⟩
      exact ⟨c, (congrArg Subtype.val hcv).symm⟩
    obtain ⟨c, hNv⟩ := hgen _ (Module.End.mapsTo_maxGenEigenspace_of_comm hc μ v₀.2)
    have hpow : ∀ m : ℕ, (N ^ m) (v₀ : V) = c ^ m • (v₀ : V) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hNv, smul_smul, ← pow_succ]
    have h0 : N (v₀ : V) = 0 := by
      have hz := hpow k
      rw [hk, LinearMap.zero_apply] at hz
      rcases smul_eq_zero.mp hz.symm with h | h
      · rw [hNv, (pow_eq_zero_iff'.mp h).1, zero_smul]
      · rw [h, map_zero]
    intro v hv
    obtain ⟨a, rfl⟩ := hgen v hv
    rw [map_smul, h0, smul_zero]
  ext v
  have hv : v ∈ ⨆ μ, f.maxGenEigenspace μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]; trivial
  exact Submodule.iSup_induction _ (motive := fun v => N v = 0) hv hline (map_zero N)
    (fun x y hx hy => by rw [map_add, hx, hy, add_zero])

end GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.WD.noMonodromy_of_inertia_separable_charpoly (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : GlobalTheory.WeilDeligne.WD h) :
    ∀ σ ∈ Ine (F := E) A, (x.inePol σ).Separable → x.mono0 := by
  intro σ hσ
  induction x using Quotient.inductionOn with
  | h a =>
    obtain ⟨n, a⟩ := a
    have hw : σ ∈ Weil h := Ine_le_Weil h hσ

    have hcomm : Commute (a.ρ ⟨σ, hw⟩) a.N := by
      have hc := a.comm ⟨σ, hw⟩
      rw [deg_eq_zero_iff.mpr hσ, zpow_zero, one_smul] at hc
      exact hc
    simp only [WD.mono0, WD.inePol, WD.charPol, dif_pos hw, Quotient.lift_mk, WDRep.Mono0]
    intro hs
    exact eq_zero_of_commute_of_separable hs hcomm a.nilpotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NodupIntShift
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings GlobalTheory.RowCuspPar

namespace GlobalTheory.RowRegAlg

theorem nodup_int_shift (R : Ranks) (S : Multiset ℂ) (hn : S.Nodup) (hi : ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ)) :
    S.Nodup ∧ ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ) + ((R.r : ℂ) - 1) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  obtain ⟨c, hc⟩ : ∃ c : ℕ, R.r = 2 * c + 1 := ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  refine ⟨hn, fun z hz => ?_⟩
  obtain ⟨n, rfl⟩ := hi z hz
  refine ⟨n - c, ?_⟩
  rw [hc]
  push_cast
  ring

theorem ralg_of_infG : ∀ (D : D7) (π : D.naut.CG D.R.r),
    (∀ τ : D.what₂.Tau, D.naut.infG π (embTau D τ) = hcSigma (D.hc τ) ∧
      D.naut.infG π (embTauBar D τ) = (hcSigma (D.hc τ)).map (fun z => -z)) →
    D.naut.ralg π := by
  intro D π h
  rw [D.naut.ralg_def]
  intro φ
  obtain ⟨τ, hτ | hτ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_cases D φ
  · have e : φ = embTau D τ := hτ
    rw [e, (h τ).1]
    exact nodup_int_shift D.R _ (GlobalTheory.Survey.EmbeddingValuationsAnti.nodup_hcSigma _) (hcSigma_int _)
  · have e : φ = embTauBar D τ := hτ
    rw [e, (h τ).2]
    refine nodup_int_shift D.R _ ((GlobalTheory.Survey.EmbeddingValuationsAnti.nodup_hcSigma _).map neg_injective) fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨n, rfl⟩ := hcSigma_int _ y hy
    exact ⟨-n, by push_cast; ring⟩

end GlobalTheory.RowRegAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCrysBKFunctorOLOfBhattScholze
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per

namespace GlobalTheory

theorem nonempty_crysBKFunctorOL_of_bhattScholze :
    GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → Nonempty (CrysBKFunctorOL a ϖ LL P) := by
  intro BS l _ a e _ _ ϖ LL _ P AI h
  refine ⟨BKFunctor.ofExists (fun T hT => GlobalTheory.T.exists_breuilKisin_module_basis_of_fCrystal BS l a e _ _ _ ϖ T ?_) fun M M' f => GlobalTheory.T.breuilKisin_full_faithfulness_lattice_morphism BS l a e _ _ _ ϖ _ _ _ _ _ _ M.I M'.I M.isBK M'.isBK f⟩
  obtain ⟨E, j, H⟩ := (BS l _ _ _ (isAinf_ainfObj (ϖ.field a))).1 P AI h LL T hT
  exact ⟨E, j, H⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormConstantCoeffEqOneOfEisensteinFrobeniusCycleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_constantCoeff_eq_one_of_eisenstein_frobenius_cycle : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (l e a M N : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (Δ k k' : ZMod a → K⟦X⟧), (∀ τ n, ‖coeff n (Δ τ)‖ ≤ 1) → (∀ τ, ∃ n, ‖coeff n (Δ τ)‖ = 1) → (∀ τ n, ‖coeff n (k τ)‖ ≤ 1) → (∀ τ n, ‖coeff n (k' τ)‖ ≤ 1) → (∀ τ, k τ * k' τ = E K l e ^ N) → (∀ τ, Δ τ * k τ = E K l e ^ M * frob K l (Δ (τ - 1))) → ∀ τ, ‖constantCoeff (Δ τ)‖ = 1 := by
  first | exact @GlobalTheory.BK.Cycle.norm_constantCoeff_eq_one_of_cycle | exact GlobalTheory.BK.Cycle.norm_constantCoeff_eq_one_of_cycle | (intros; apply GlobalTheory.BK.Cycle.norm_constantCoeff_eq_one_of_cycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMinpolyCoeffZeroPowOfPowEqNegStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_minpoly_coeff_zero_pow_of_pow_eq_neg_prime : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N → x ^ N = -(l : Om l) → ‖(((minpoly F x).coeff 0 : F) : Om l)‖ ^ N = ((l : ℝ)⁻¹) ^ (minpoly F x).natDegree := by
  first | exact @GlobalTheory.norm_minpoly_coeff_zero_pow_of_pow_eq_neg | exact GlobalTheory.norm_minpoly_coeff_zero_pow_of_pow_eq_neg | (intros; apply GlobalTheory.norm_minpoly_coeff_zero_pow_of_pow_eq_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerOrderFormulaDualSelmerStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selmer_order_formula_dual_selmer : PoitouTateTotallyComplex → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q := by
  first | exact @GlobalTheory.SelOrder.orderFormula | exact GlobalTheory.SelOrder.orderFormula | (intros; apply GlobalTheory.SelOrder.orderFormula <;> assumption)
end

