import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.Basics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviIdeleHomExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeLabelIsCuspidalParabolicProductCharact
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.SqfreeCuspProd

theorem labO_irreducible {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
    (O : LabelMap K C) {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {σ : FDRep ℂ (GL κ K)} (hs : Simple σ) (hc : IsCuspidal K σ) : Irreducible (labO O σ) :=
  (O.lab_spec _ _ (Nat.succ_le_of_lt Fintype.card_pos) (Formalism.L2.PT.simple_transp _ hs)
    (Formalism.L2.PT.isCuspidal_transp _ hc)).2.1

theorem injective_of_squarefree {R : Type} [CommMonoid R] {s : ℕ} (F : Fin s → R)
    (hF : ∀ c, Irreducible (F c)) (hsq : Squarefree (∏ c, F c)) : Function.Injective F := by
  intro c c' h
  by_contra hne
  have hd : F c * F c' ∣ ∏ x, F x := by
    rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ c),
      ← Finset.mul_prod_erase (Finset.univ.erase c) F
        (Finset.mem_erase.2 ⟨fun h' => hne h'.symm, Finset.mem_univ c'⟩), ← mul_assoc]
    exact dvd_mul_right _ _
  rw [h] at hd
  exact (hF c').not_isUnit (hsq _ hd)

theorem character_eq_of_constituent {Γ : Type} [Group Γ] (τ : FDRep ℂ Γ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ Γ V) (hτ : Simple τ) (hρ : IsIrrRep ρ) (hc : IsConstituent τ ρ)
    (x : Γ) : τ.character x = LinearMap.trace ℂ V (ρ x) := by
  obtain ⟨φ, hφ, hne⟩ := hc
  have hirr := (PI.GreenHCLabel.simple_irreducible Γ τ).1 hτ
  have hker : LinearMap.ker φ = ⊥ := by
    rcases hirr.2 (LinearMap.ker φ) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have := congrArg (fun k => k v) (hφ g)
      simp only [LinearMap.comp_apply] at this
      rw [this, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hne
  have hran : LinearMap.range φ = ⊤ := by
    rcases hρ.2 (LinearMap.range φ) (fun g v hv => by
      obtain ⟨y, rfl⟩ := hv
      exact ⟨τ.ρ g y, by simpa using congrArg (fun k => k y) (hφ g)⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.1 h) hne
    · exact h
  let e : τ ≃ₗ[ℂ] V :=
    LinearEquiv.ofBijective φ ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hran⟩
  haveI : Module.Finite ℂ V := Module.Finite.equiv e
  have hconj : e.conj (τ.ρ x) = ρ x := by
    ext v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply]
    show e (τ.ρ x (e.symm (e w))) = ρ x (e w)
    rw [e.symm_apply_apply]
    exact congrArg (fun k => k w) (hφ x)
  rw [FDRep.character, ← hconj, LinearMap.trace_conj']

theorem isCuspProdChar_of_squarefree : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K)
    (O : LabelMap K C) (r : ℕ) (τ : FDRep ℂ (GL (Fin r) K)) (f : K[X]), Simple τ → HasLabelO O τ f →
    Squarefree f → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => τ.character x) := by
  intro K _ _ _ C O r τ f hτ hL hsq
  obtain ⟨s, b, lam, hb, hl, hc, rfl⟩ := hL
  have hirrF : ∀ c, Irreducible (labO O (lam c)) := fun c => by
    obtain ⟨i, hi⟩ := hb c
    haveI : Nonempty {i // b i = c} := ⟨⟨i, hi⟩⟩
    exact labO_irreducible O (hl c).1 (hl c).2
  have hinj := injective_of_squarefree _ hirrF hsq
  have hirr := GlobalTheory.T.isIrrRep_harishChandra_distinct_cuspidal_labels K r s b lam hb hl C O hinj
  obtain ⟨b', lam', hb', hl', hmono, htr⟩ := GlobalTheory.T.exists_monotone_blocks_same_harishChandra_character K r s b lam hb hl
  have hcp := GlobalTheory.T.harishChandraInduction_cuspidalParabolicProduct K r s b' lam' hb' hl' hmono
  have hfun : (fun x : GL (Fin r) K => τ.character x) =
      fun x => LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) := by
    funext x
    rw [htr x]
    exact character_eq_of_constituent τ _ hτ hirr hc x
  rw [hfun]
  exact hcp

end GlobalTheory.SqfreeCuspProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRestrictsToOrthocomp
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IsoPlaneProj

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_cartan (B : Base F E) {n : ℕ} (Y : Spc F E n)
    (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) : Y.J.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (B.emb w).1
  let M : Matrix (Fin n) (Fin n) ℂ := Complex.I • Y.J.map τ
  let v' : Fin n → ℂ := fun i => τ (v i)
  have hv' : v' ≠ 0 := fun h => hv (funext fun i => τ.injective (by simpa [v'] using congrFun h i))
  have hMv : M *ᵥ v' = 0 := by
    ext i
    have := congrArg τ (congrFun hJv i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this
    simp only [M, v', Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Matrix.smul_apply, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  have hx : star v' ≠ 0 := fun h => hv' (by simpa using congrArg star h)
  have := (h w).2.2 (star v') hx
  rw [star_star] at this
  change 0 < (_ ⬝ᵥ M *ᵥ v').re at this
  rw [hMv, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem frame_of_gram {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {J₁ : Matrix (Fin n₁) (Fin n₁) E} (hsk : ∀ i j, σ (J j i) = -J i j) {x y : Fin n → E} {ι : Matrix (Fin n) (Fin n₁) E}
    (hn : n = n₁ + 2) (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hgram : ιᵀ * J * ι.map σ = J₁)
    (hJ₁ : IsUnit J₁.det) :
    ∃ π : Matrix (Fin n₁) (Fin n) E, vecMulVec x (J *ᵥ (⇑σ ∘ y)) + ι * π - vecMulVec y (J *ᵥ (⇑σ ∘ x)) = 1 := by
  obtain ⟨hax, hay, hbx, hby, hxJ, hyJ, haι, hbι⟩ := GlobalTheory.LeviIdeleHom.dual_facts hσ hsk hxx hyy hxy horth
  set aE := J *ᵥ (⇑σ ∘ y) with haE
  set bE := -(J *ᵥ (⇑σ ∘ x)) with hbE
  let π : Matrix (Fin n₁) (Fin n) E := (J₁⁻¹)ᵀ * (J * ι.map σ)ᵀ
  have hπι : π * ι = 1 := by
    calc π * ι = (J₁⁻¹)ᵀ * (ιᵀ * J * ι.map σ)ᵀ := by
          simp only [π, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [hgram, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hJ₁, Matrix.transpose_one]
  have hv : ∀ w : Fin n → E, (⇑σ ∘ w) ᵥ* ι.map σ = ⇑σ ∘ (w ᵥ* ι) := fun w =>
    funext fun j => by simp [vecMul, dotProduct, map_sum]
  have hπx : π *ᵥ x = 0 := by
    have inner : (J * ι.map σ)ᵀ *ᵥ x = 0 := by
      rw [mulVec_transpose, ← vecMul_vecMul, hxJ, hv, hbι]
      funext j; simp
    simp only [π]
    rw [← mulVec_mulVec, inner, mulVec_zero]
  have hπy : π *ᵥ y = 0 := by
    have inner : (J * ι.map σ)ᵀ *ᵥ y = 0 := by
      rw [mulVec_transpose, ← vecMul_vecMul, hyJ, neg_vecMul, hv, haι]
      funext j; simp
    simp only [π]
    rw [← mulVec_mulVec, inner, mulVec_zero]
  let X : Matrix (Fin n) (Fin 2) E := Matrix.of fun i k => ![x i, y i] k
  let L : Matrix (Fin 2) (Fin n) E := Matrix.of ![aE, bE]
  have hLX : L * X = 1 := by
    ext k l
    fin_cases k <;> fin_cases l <;> simp [Matrix.mul_apply, L, X, Matrix.one_apply]
    · exact hax
    · exact hay
    · exact hbx
    · exact hby
  have hLι : L * ι = 0 := by
    ext k j
    fin_cases k <;> simp [Matrix.mul_apply, L]
    · exact congrFun haι j
    · exact congrFun hbι j
  have hπX : π * X = 0 := by
    ext k l
    fin_cases l <;> simp [Matrix.mul_apply, X]
    · exact congrFun hπx k
    · exact congrFun hπy k
  have hXL : X * L = vecMulVec x aE + vecMulVec y bE := by
    ext i j
    simp [Matrix.mul_apply, X, L, Fin.sum_univ_two, vecMulVec_apply]
  have h1 : Matrix.fromRows π L * Matrix.fromCols ι X = 1 := by
    rw [Matrix.fromRows_mul_fromCols, hπι, hπX, hLι, hLX, Matrix.fromBlocks_one]
  have e : Fin n₁ ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr hn.symm)
  have h2 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  rw [Matrix.fromCols_mul_fromRows, hXL] at h2
  refine ⟨π, ?_⟩
  rw [← h2, hbE, Matrix.vecMulVec_neg]
  abel

end GlobalTheory.IsoPlaneProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeFlagUnipotentRadical
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix

namespace GlobalTheory.StdPar

theorem unip_le_unipFlag_initCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S m hm hS g hg
  have e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m} :=
    Set.ext fun i => ⟨fun ⟨k, hk, h⟩ => h.trans (hS k hk), fun h => ⟨m, hm, h⟩⟩
  apply Subgroup.subset_closure
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · have key : ∀ y ∈ colSpan F X {l | ∃ k ∈ S, l ≤ k ∧ k < i.castLE m.2},
        ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j : Fin (m.val + 1), (S.filter fun k => k.val < i.val).card ≤
          (S.filter fun k => k.val < j.val).card → a j = 0) ∧ y = adMat F (initCols X m) *ᵥ a := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, ⟨k, hk, hlk, hki⟩, rfl⟩ := hy
        have hl : l.val < m.val + 1 := Nat.lt_succ_of_le (hlk.trans (hS k hk))
        refine ⟨Pi.single ⟨l.val, hl⟩ 1, fun j hj => ?_, ?_⟩
        · refine Pi.single_eq_of_ne ?_ _
          rintro rfl
          refine absurd hj (not_le.2 (Finset.card_lt_card ⟨fun t ht => ?_, fun h => ?_⟩))
          · rw [Finset.mem_filter] at ht ⊢
            exact ⟨ht.1, lt_trans (lt_of_lt_of_le ht.2 hlk) hki⟩
          · have := (Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨hk, hki⟩))).2
            exact absurd this (not_lt.2 hlk)
        · rw [mulVec_single_one]
          rfl
      | zero => exact ⟨0, fun _ _ => rfl, (mulVec_zero _).symm⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha, rfl⟩ := hy
        obtain ⟨b, hb, rfl⟩ := hz
        exact ⟨a + b, fun j hj => by rw [Pi.add_apply, ha j hj, hb j hj, add_zero], (mulVec_add _ _ _).symm⟩
      | smul c y _ hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        exact ⟨c • a, fun j hj => by rw [Pi.smul_apply, ha j hj, smul_zero], (mulVec_smul _ _ _).symm⟩
    have := (Subgroup.mem_iInf.1 hg.1 (i.castLE m.2)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)
    obtain ⟨a, ha, e⟩ := key _ this
    refine ⟨a, ha, ?_⟩
    rw [sub_mulVec, one_mulVec]
    exact e
  · have := hg.2.2 (fun i => inclR (F := F) (AF F) (x i)) (by
      rw [e1, mem_colPerp_iff]
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    rw [e1, mem_colSpan_iff] at this
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

end GlobalTheory.StdPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentLeIsotropicFlagStabili
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
namespace GlobalTheory.StdParFlag

open Matrix

theorem unip_le_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)) (m : Fin r), T ⊆ S → m ∈ T → (∀ k ∈ T, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.parFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (T.filter fun k => k.val < i.val).card) := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S T m _ _ _
  classical
  have key : ∀ p ∈ GlobalTheory.StdPar.unip σ J X S, ∃ B : Matrix (Fin (m.val + 1)) (Fin (m.val + 1)) (AF F ⊗[F] E),
      B.BlockTriangular (fun i => (T.filter fun k => k.val < i.val).card) ∧
      (matHom _ σ J p).1 * adMat F (GlobalTheory.StdPar.initCols X m) = adMat F (GlobalTheory.StdPar.initCols X m) * B := by
    intro p hp
    have span_lemma : ∀ (i : Fin (m.val + 1)) (I : Set (Fin r)), (∀ l ∈ I, l.val < i.val) →
        ∀ y ∈ GlobalTheory.StdPar.colSpan F X I, ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j, i.val ≤ j.val → a j = 0) ∧
          adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a = y := by
      intro i I hI y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨l, hl, rfl⟩ := hx
        have hl' : l.val < m.val + 1 := by have := hI l hl; have := i.2; omega
        refine ⟨Pi.single ⟨l.val, hl'⟩ 1, fun j hj => Pi.single_eq_of_ne (fun e => ?_) _, ?_⟩
        · have := hI l hl; rw [e] at hj; simp at hj; omega
        · rw [mulVec_single_one]; rfl
      | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], by rw [mulVec_add]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨c • a, fun j hj => by simp [ha j hj], by rw [mulVec_smul]⟩
    have hcol : ∀ i : Fin (m.val + 1), ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j, (fun k : Fin (m.val + 1) => k.val) i ≤ (fun k : Fin (m.val + 1) => k.val) j → a j = 0) ∧
        ((matHom _ σ J p).1 - 1) *ᵥ (fun k => inclR (F := F) (AF F) (GlobalTheory.StdPar.initCols X m k i)) =
          adMat F (GlobalTheory.StdPar.initCols X m) *ᵥ a := by
      intro i
      have h := (Subgroup.mem_iInf.1 hp.1 (Fin.castLE m.2 i)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)
      have hv : (fun k => inclR (F := F) (AF F) (GlobalTheory.StdPar.initCols X m k i)) = (adMat F X)ᵀ (Fin.castLE m.2 i) := rfl
      rw [hv, sub_mulVec, one_mulVec]
      obtain ⟨a, ha, e⟩ := span_lemma i _ (fun l hl => by
        obtain ⟨k, _, hlk, hki⟩ := hl
        have := Fin.lt_def.1 (lt_of_le_of_lt hlk hki)
        simpa using this) _ h
      exact ⟨a, ha, e.symm⟩
    obtain ⟨A, hA, e⟩ := lower_iff.1 hcol
    refine ⟨1 + A, fun l j hlt => ?_, ?_⟩
    · have hjl : j.val ≤ l.val := by
        by_contra hc
        refine absurd hlt (not_lt.2 (Finset.card_le_card fun k hk => ?_))
        simp only [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, by omega⟩
      have hne : l ≠ j := fun h => by subst h; exact lt_irrefl _ hlt
      rw [Matrix.add_apply, Matrix.one_apply_ne hne, hA l j hjl, add_zero]
    · rw [Matrix.mul_add, Matrix.mul_one, ← e, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  intro p hp
  exact ⟨key p hp, key p⁻¹ (inv_mem hp)⟩

end GlobalTheory.StdParFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.StdPar

section DimensionMonotonicity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}

theorem unip_maps_colSpan {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∀ l, l < i → l ∈ I) {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I) :
    (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X I := by
  have key : colSpan F X I ≤ (colSpan F X I).comap (matHom _ σ J g).1.mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h1 := (Subgroup.mem_iInf.1 hg.1 i).2 _ (Submodule.subset_span ⟨i, rfl, rfl⟩)
    have h2 : colSpan F X {l | ∃ k ∈ T, l ≤ k ∧ k < i} ≤ colSpan F X I := by
      refine Submodule.span_mono (Set.image_mono ?_)
      rintro l ⟨k, -, hlk, hki⟩
      exact hI i hi l (lt_of_le_of_lt hlk hki)
    have h3 : (fun i => (adMat F X)ᵀ i) i ∈ colSpan F X I := Submodule.subset_span ⟨i, hi, rfl⟩
    show (matHom _ σ J g).1 *ᵥ _ ∈ colSpan F X I
    have := add_mem (h2 h1) h3
    rwa [sub_add_cancel] at this
  exact key hy

theorem unip_iff_colSpan {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∀ l, l < i → l ∈ I) (y : Fin n → AF F ⊗[F] E) :
    y ∈ colSpan F X I ↔ (matHom _ σ J g).1 *ᵥ y ∈ colSpan F X I := by
  refine ⟨unip_maps_colSpan hg hI, fun h => ?_⟩
  have := unip_maps_colSpan (inv_mem hg) hI h
  rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec] at this

end DimensionMonotonicity

theorem unip_mono_of_subset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)), T ⊆ S → GlobalTheory.StdPar.unip σ J X T ≤ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S T hTS g hg
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨unip_iff_colSpan hg ?_, fun y hy => ?_⟩,
    ⟨unip_iff_colSpan hg ?_, fun y hy => ?_⟩⟩
  · rintro i ⟨k, hk, hik, hkj⟩ l hl
    exact ⟨k, hk, (le_of_lt (lt_of_lt_of_le hl hik)), hkj⟩
  · refine Submodule.span_mono (Set.image_mono ?_) ((Subgroup.mem_iInf.1 hg.1 j).2 y hy)
    rintro l ⟨k, hk, h1, h2⟩
    exact ⟨k, hTS hk, h1, h2⟩
  · rintro i ⟨k, hk, hik⟩ l hl
    exact ⟨k, hk, le_of_lt (lt_of_lt_of_le hl hik)⟩
  · have hy' : y ∈ colPerp σ J X {i | ∃ k ∈ T, i ≤ k} := by
      simp only [colPerp, Submodule.mem_iInf] at hy ⊢
      rintro i ⟨k, hk, hik⟩
      exact hy i ⟨k, hTS hk, hik⟩
    refine Submodule.span_mono (Set.image_mono ?_) (hg.2.2 y hy')
    rintro l ⟨k, hk, h1⟩
    exact ⟨k, hTS hk, h1⟩

end GlobalTheory.StdPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicEmbeddedVanishesAdelicStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_isotropic_embedded_vanishes_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁),
    (∀ u, form σ JW (H'.ι *ᵥ u) H'.x = 0) → ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))),
      ∀ z : Matrix (Fin n) (Fin d₁) (AE F E),
        symp (cA σ) (-1) (incM F JX) (incM F JW) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) u = 0 := by
  first | exact @GlobalTheory.MixedLagr.symplectic_isotropic_embedded_vanishes | exact GlobalTheory.MixedLagr.symplectic_isotropic_embedded_vanishes | (intros; apply GlobalTheory.MixedLagr.symplectic_isotropic_embedded_vanishes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelicStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_isotropic_plane_vanishes_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁),
    form σ JW H'.x H'.x = 0 → ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))),
      ∀ u' ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), symp (cA σ) (-1) (incM F JX) (incM F JW) u u' = 0 := by
  first | exact @GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes | exact GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes | (intros; apply GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticPairingBlockReductionStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_pairing_block_reduction : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (r₀ : ℕ) (J₀ : Matrix α α S) (K : Matrix β β S)
    (z z' : Matrix (α ⊕ (Fin r₀ ⊕ Fin r₀)) β S),
    symp c ξ (Matrix.fromBlocks J₀ 0 0 (Matrix.fromBlocks 0 1 1 0)) K z z' =
      symp c ξ J₀ K (Matrix.of fun i l => z (Sum.inl i) l) (Matrix.of fun i l => z' (Sum.inl i) l) +
      ∑ i, (Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inl i)) j * K j l * c (z' (Sum.inr (Sum.inr i)) l)) +
        Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inr i)) j * K j l * c (z' (Sum.inr (Sum.inl i)) l))) := by
  first | exact @GlobalTheory.WeilM.symp_fromBlocks_hyperbolic | exact GlobalTheory.WeilM.symp_fromBlocks_hyperbolic | (intros; apply GlobalTheory.WeilM.symp_fromBlocks_hyperbolic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameConjMapStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_conj_map : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsTame F T → IsTame F (conjMap T) := by
  first | exact @GlobalTheory.DoublingEv.isTame_conjMap | exact GlobalTheory.DoublingEv.isTame_conjMap | (intros; apply GlobalTheory.DoublingEv.isTame_conjMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRightStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_part_right : ∀ (F : Type) [Field F] [NumberField F] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ₁' → AF F) → ℂ)), IsTame F T → IsTame F (partR (κ := κ) T) := by
  first | exact @GlobalTheory.TamePartR.isTame_partR | exact GlobalTheory.TamePartR.isTame_partR | (intros; apply GlobalTheory.TamePartR.isTame_partR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumIndicatorNonzeroStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_indicator_nonzero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator
        (fun _ => (1 : ℂ)))) ≠ 0 := by
  first | exact @GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero | exact GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero | (intros; apply GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero <;> assumption)
end

