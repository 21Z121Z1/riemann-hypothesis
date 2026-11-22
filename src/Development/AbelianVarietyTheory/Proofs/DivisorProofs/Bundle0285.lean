import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import ReciprocityTheory.Chebotarev.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegEqOne
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.LinSchur

theorem addChar_neg_eq_one {A : Type} [AddGroup A] (ψ : AddChar A ℂ) {x : A} (h : ψ x = 1) : ψ (-x) = 1 := by
  have e := AddChar.map_add_eq_mul ψ (-x) x
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at e
  exact e.symm

variable {k : Type} [Field k] [ValuativeRel k]

def latt (ψ0 : AddChar k ℂ) (n d : ℕ) (s : k) : AddSubgroup (Matrix (Fin n) (Fin d) k) where
  carrier := {Y | ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1}
  add_mem' := by
    intro a b ha hb i j o ho
    simp only [Set.mem_ofPred_eq, Matrix.add_apply, mul_add, AddChar.map_add_eq_mul] at *
    rw [ha i j o ho, hb i j o ho, one_mul]
  zero_mem' := by
    intro i j o _
    simp
  neg_mem' := by
    intro a ha i j o ho
    simp only [Set.mem_ofPred_eq, Matrix.neg_apply, mul_neg] at *
    exact addChar_neg_eq_one ψ0 (ha i j o ho)

theorem mem_latt {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k} {Y : Matrix (Fin n) (Fin d) k} :
    Y ∈ latt ψ0 n d s ↔ ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1 := Iff.rfl

open Classical in

def cind {X : Type} [AddGroup X] (L : AddSubgroup X) (y : X) : X → ℂ := fun Y => if Y - y ∈ L then 1 else 0

end GlobalTheory.LinSchur
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionOnMonoidLinear
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.AddExt

theorem nat_comb {ι : Type} (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) {x0 : ι → ℕ} (hx0 : x0 ∈ S)
    (T : Finset S) (n : S → ℕ) :
    x0 + ∑ s ∈ T, n s • (s : ι → ℕ) ∈ S ∧
      c (x0 + ∑ s ∈ T, n s • (s : ι → ℕ)) = c x0 + ∑ s ∈ T, (n s : ℝ) * c s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [hx0]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    suffices key : ∀ k : ℕ, x0 + (k • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ)) ∈ S ∧
        c (x0 + (k • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ))) =
          c x0 + ((k : ℝ) * c a + ∑ s ∈ T, (n s : ℝ) * c s) from key (n a)
    intro k
    induction k with
    | zero => simpa using ih
    | succ k ihk =>
      have e : x0 + ((k+1) • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ)) =
          (x0 + (k • (a : ι → ℕ) + ∑ s ∈ T, n s • (s : ι → ℕ))) + a := by
        rw [succ_nsmul]; abel
      rw [e]
      obtain ⟨h1, h2⟩ := hS _ ihk.1 _ a.2
      refine ⟨h1, ?_⟩
      rw [h2, ihk.2]; push_cast; ring

theorem ker_le {ι : Type} (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) {x0 : ι → ℕ} (hx0 : x0 ∈ S)
    (l : S →₀ ℤ)
    (hl : Finsupp.linearCombination ℤ (fun s : S => fun i => ((s : ι → ℕ) i : ℤ)) l = 0) :
    Finsupp.linearCombination ℤ (fun s : S => c s) l = 0 := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl ⊢
  obtain ⟨p, hp⟩ : ∃ p : S → ℕ, ∀ s, p s = (l s).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : S → ℕ, ∀ s, q s = (-l s).toNat := ⟨_, fun _ => rfl⟩
  have hpq : ∀ s, l s = (p s : ℤ) - q s := fun s => by
    rw [hp, hq]; omega
  have heq : ∑ s ∈ l.support, p s • (s : ι → ℕ) = ∑ s ∈ l.support, q s • (s : ι → ℕ) := by
    funext i
    have := congrFun hl i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hpq, sub_mul] at this
    rw [Finset.sum_sub_distrib, sub_eq_zero] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast this
  have h1 := (nat_comb S c hS hx0 l.support p).2
  have h2 := (nat_comb S c hS hx0 l.support q).2
  rw [heq, h2] at h1
  have h3 : ∑ s ∈ l.support, (p s : ℝ) * c s = ∑ s ∈ l.support, (q s : ℝ) * c s := by linarith
  simp only [hpq, zsmul_eq_mul, Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib, h3, sub_self]

theorem exists_linear : ∀ (ι : Type) [Fintype ι] (S : Set (ι → ℕ)) (c : (ι → ℕ) → ℝ),
    (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S ∧ c (x + y) = c x + c y) →
      ∃ κ : ι → ℝ, ∀ x ∈ S, c x = ∑ i, (x i : ℝ) * κ i := by
  intro ι _ S c hS
  classical
  rcases S.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
  · exact ⟨0, by simp [hE]⟩
  let v : S → ι → ℤ := fun s i => ((s : ι → ℕ) i : ℤ)
  let A : (S →₀ ℤ) →+ (ι → ℤ) := (Finsupp.linearCombination ℤ v).toAddMonoidHom
  let C : (S →₀ ℤ) →+ ℝ := (Finsupp.linearCombination ℤ (fun s : S => c s)).toAddMonoidHom
  have hker : A.ker ≤ C.ker := fun l hl =>
    AddMonoidHom.mem_ker.mpr (ker_le S c hS hx0 l (AddMonoidHom.mem_ker.mp hl))
  letI : DivisibleBy ℝ ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => ⟨u / n, by
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      show n • (u / (n : ℝ)) = u
      rw [nsmul_eq_mul]; field_simp⟩
  letI : DivisibleBy ℝ ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift A) (QuotientAddGroup.kerLift_injective A)
    (QuotientAddGroup.lift A.ker C hker)
  refine ⟨fun i => g (Pi.single i 1), fun x hx => ?_⟩
  have h1 := DFunLike.congr_fun hg (QuotientAddGroup.mk (Finsupp.single ⟨x, hx⟩ 1))
  have hA : A (Finsupp.single ⟨x, hx⟩ 1) = ∑ i, ((x i : ℤ)) • (Pi.single i (1:ℤ) : ι → ℤ) := by
    ext j; simp [A, v, Finset.sum_apply, Pi.single_apply]
  have hC : C (Finsupp.single ⟨x, hx⟩ 1) = c x := by simp [C]
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.kerLift_mk, QuotientAddGroup.lift_mk] at h1
  rw [hA, hC, map_sum] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_eq_mul, Int.cast_natCast]

end GlobalTheory.AddExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsLatticeFacts
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem GlobalTheory.herbrand_lattice_facts : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ev a τ (cofac a τ) ≠ 0 ∧ (∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0) ∧ LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) ∧ preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v) ∧ (preEig a Fil τ).map (mulR a N (lin a τ)) = filKer a Fil τ ∧ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥ ∧ (eigSub a τ (Fin N → RS a)).map (comp a N τ) = (⊤ : Submodule (Int0 v) (Fin N → Int0 v)).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) (ev a τ (cofac a τ))) ∧ (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧ eigSub a τ (Fin N → RS a) ≤ preEig a Fil τ ∧ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ ∧ (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0) ∧ (∃ g : RS a, ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x)) := by
  intro C _ v S _ _ a ha N Fil hFil τ
  obtain ⟨hfree, hfin, hlc, hev, hker, ⟨g, hg⟩, hann⟩ := GlobalTheory.T.adjoinRootProdLinearFactors_structure (Int0 v) S a τ
  have hd : ev a τ (cofac a τ) ≠ 0 := by
    rw [hev]
    exact Finset.prod_ne_zero_iff.mpr fun s hs =>
      sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hs (ha h).symm
  have hid : ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x) := by
    intro x
    have : cofac a τ • x = ev a τ (cofac a τ) • x + g • (lin a τ • x) := by
      conv_lhs => rw [hg]
      rw [add_smul, algebraMap_smul, mul_comm, mul_smul]
    rw [this, add_sub_cancel_right]
  have htf : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc hx
    haveI := hfree
    haveI : Module.IsTorsionFree (Int0 v) (Fin N → RS a) :=
      (Module.Free.chooseBasis (Int0 v) (Fin N → RS a)).isTorsionFree
    exact (smul_eq_zero_iff_right hc).mp hx
  have hcomp0 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ ∀ i, ev a τ (x i) = 0 := by
    intro x
    constructor
    · intro h i; exact congrFun h i
    · intro h; funext i; exact h i
  have h2 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0 := by
    intro x
    rw [hcomp0]
    constructor
    · intro h
      show cofac a τ • x = 0
      funext i
      obtain ⟨r', hr'⟩ := hker _ (h i)
      show cofac a τ * x i = 0
      rw [hr', ← mul_assoc, mul_comm (cofac a τ), hlc, zero_mul]
    · intro h i
      have hi : cofac a τ * x i = 0 := congrFun h i
      have := congrArg (ev a τ) hi
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hd
  have h3 : LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range, hcomp0]
    constructor
    · intro h
      choose r hr using fun i => hker _ (h i)
      exact ⟨r, funext fun i => (hr i).symm⟩
    · rintro ⟨y, rfl⟩ i
      show ev a τ (lin a τ * y i) = 0
      rw [map_mul, ev_lin, sub_self, zero_mul]
  have hcz : ∀ x : Fin N → RS a, comp a N τ x = 0 → cofac a τ • x = 0 := fun x h => (h2 x).mp h
  refine ⟨hd, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htf, ⟨g, hid⟩⟩
  ·
    rintro x ⟨hx1, hx2⟩
    have hx1' : lin a τ • x ∈ Fil := hx1
    have hc : cofac a τ • x = 0 := hcz x hx2
    apply hFil _ x hd
    rw [hid, hc, zero_sub]
    exact Fil.neg_mem (Fil.smul_mem g hx1')
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x ∈ Fil := hx
      refine ⟨hx', ?_⟩
      show cofac a τ • (lin a τ • x) = 0
      rw [smul_smul, mul_comm, hlc, zero_smul]
    · rintro ⟨hy1, hy2⟩
      have hy2' : mulR a N (cofac a τ) y = 0 := hy2
      have hk : y ∈ LinearMap.ker (comp a N τ) := (h2 y).mpr hy2'
      rw [h3] at hk
      obtain ⟨x, rfl⟩ := hk
      exact ⟨x, hy1, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx1' : lin a τ • x = 0 := hx1
    have hc : cofac a τ • x = 0 := hcz x hx2
    have : ev a τ (cofac a τ) • x = 0 := by rw [hid, hc, hx1', smul_zero, sub_zero]
    exact (Submodule.mem_bot _).mpr (htf _ x hd this)
  · ext y
    simp only [Submodule.mem_map, Submodule.mem_top, true_and, LinearMap.lsmul_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x = 0 := hx
      choose c hc using fun i => hann (x i) (congrFun hx' i)
      refine ⟨c, funext fun i => ?_⟩
      show ev a τ (cofac a τ) * c i = ev a τ (x i)
      rw [hc i, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ, ?_, ?_⟩
      · show lin a τ • (fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0
        funext i
        show lin a τ * (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0
        rw [mul_left_comm, hlc, mul_zero]
      · funext i
        show ev a τ (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = ev a τ (cofac a τ) * c i
        rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  · ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x ∈ Fil := hx
      show lin a τ • Fil.mkQ x = 0
      rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx'
    · intro hq
      have hq' : lin a τ • q = 0 := hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Fil q
      refine ⟨x, ?_, rfl⟩
      show lin a τ • x ∈ Fil
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hq'
  · intro x hx
    have hx' : lin a τ • x = 0 := hx
    show lin a τ • x ∈ Fil
    rw [hx']; exact Fil.zero_mem
  · intro x hx
    show lin a τ • x ∈ Fil
    exact Fil.smul_mem _ hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertBaseChangeAppLECompSpecTensorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertBaseChange_appLE_comp_specTensor : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)) (U : Z.Opens), letI := (GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra; ∀ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = GlobalTheory.HilbAff.secAlg C h U → ((GlobalTheory.HilbAff.bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤ ((pullback.snd (GlobalTheory.HilbAff.str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp)).hom.comp (GlobalTheory.HilbAff.psi A B C) = (GlobalTheory.HilbAff.theta A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).comp (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom := by
  first | (exact @GlobalTheory.HilbAff.bc_appLE_comp_psi) | (exact GlobalTheory.HilbAff.bc_appLE_comp_psi) | (intros; apply GlobalTheory.HilbAff.bc_appLE_comp_psi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertIdealSheafOfQuotientIdealTopStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)), (GlobalTheory.HilbAff.xI A B C J).ideal ⟨⊤, isAffineOpen_top _⟩ = J.map (GlobalTheory.HilbAff.psi A B C) := by
  first | (exact @GlobalTheory.HilbAff.xI_ideal_top) | (exact GlobalTheory.HilbAff.xI_ideal_top) | (intros; apply GlobalTheory.HilbAff.xI_ideal_top  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeFunctorIsSheafZariski
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff
theorem glue_exists {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (J : ∀ i, (V i).IdealSheafData)
    (hJ : ∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') :
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i :=
  GlobalTheory.T.exists_idealSheaf_comap_eq_of_openCover V f hf hcov J hJ
theorem glue_ext {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (I I' : X.IdealSheafData) (h : ∀ i, I.comap (f i) = I'.comap (f i)) : I = I' :=
  GlobalTheory.T.idealSheafData_ext_of_openCover' V f hf hcov I I' h
theorem good_local (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    {T : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ T)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : T, ∃ i y, f i y = x)
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (h : ∀ i, GlobalTheory.HilbAff.Good A B r (f i ≫ g) (I.comap (GlobalTheory.HilbAff.bc A B g (f i)))) :
    GlobalTheory.HilbAff.Good A B r g I :=
  GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_openCover A B r V f hf hcov g I h

theorem snd_eq_of_sigma {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}
    {g₀ g₁ : T ⟶ Spec (CommRingCat.of A)}
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I₁ : (pullback (str A B) g₁).IdealSheafData}
    {h₀ : Good A B r g₀ I₀} {h₁ : Good A B r g₁ I₁}
    (e : (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g₁, ⟨I₁, h₁⟩⟩) :
    ∃ h : g₀ = g₁, I₀ = I₁.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])) := by
  have hg : g₀ = g₁ := congrArg Sigma.fst e
  refine ⟨hg, ?_⟩
  subst hg
  have h2 : I₀ = I₁ := by
    have := (Sigma.mk.inj_iff.mp e).2
    exact congrArg Subtype.val (eq_of_heq this)
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id, h2]

theorem fac_bc {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {T Z : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (φ : Z ⟶ pullback (str A B) g) :
    pullback.lift (φ ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) ≫
      bc A B g (φ ≫ pullback.snd _ _) = φ := by
  apply pullback.hom_ext <;> simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem lift_map_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {T T' Z : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A))
    (φ : Z ⟶ pullback (str A B) g) (φ' : Z ⟶ pullback (str A B) g')
    (e1 : φ ≫ pullback.fst _ _ = φ' ≫ pullback.fst _ _)
    (hh : (φ ≫ pullback.snd _ _) ≫ g = (φ' ≫ pullback.snd _ _) ≫ g') :
    pullback.lift (φ ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) ≫
      pullback.map (str A B) ((φ ≫ pullback.snd _ _) ≫ g) (str A B) ((φ' ≫ pullback.snd _ _) ≫ g')
        (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hh]) =
    pullback.lift (φ' ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) := by
  apply pullback.hom_ext
  · simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    exact e1
  · simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem comap_eq_of_map_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    {X X' Z : Scheme.{0}} (y : (functor A B r).obj (op X)) (y' : (functor A B r).obj (op X'))
    (φ : Z ⟶ pullback (str A B) y.1) (φ' : Z ⟶ pullback (str A B) y'.1)
    (e1 : φ ≫ pullback.fst _ _ = φ' ≫ pullback.fst _ _)
    (e : (functor A B r).map (φ ≫ pullback.snd _ _).op y =
      (functor A B r).map (φ' ≫ pullback.snd _ _).op y') :
    y.2.1.comap φ = y'.2.1.comap φ' := by
  obtain ⟨hh, hI⟩ := snd_eq_of_sigma e
  simp only [Quiver.Hom.unop_op] at hh hI
  rw [← fac_bc y.1 φ, ← fac_bc y'.1 φ', Scheme.IdealSheafData.comap_comp, hI,
    Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp _ _ (pullback.map _ _ _ _ _ _ _ _ _),
    lift_map_eq y.1 y'.1 φ φ' e1 hh, ← Scheme.IdealSheafData.comap_comp]

theorem good_transport {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}
    {g₀ g : T ⟶ Spec (CommRingCat.of A)} (h : g₀ = g)
    {I : (pullback (str A B) g).IdealSheafData} (hI : Good A B r g I) :
    Good A B r g₀ (I.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h]))) := by
  subst h
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id]
  exact hI

theorem isOpenImmersion_bc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T T' : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) [IsOpenImmersion a] :
    IsOpenImmersion (bc A B g a) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_bc A B g a).flip inferInstance

theorem isSheaf_functor (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (functor A B r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hS
  rw [Presieve.isSheafFor_arrows_iff]
  intro (x : ∀ j, (functor A B r).obj (op (𝒰.X j))) hx
  replace hx : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ 𝒰.X i) (a' : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = a' ≫ 𝒰.f j → (functor A B r).map a.op (x i) = (functor A B r).map a'.op (x j) := hx
  let g : Y ⟶ Spec (CommRingCat.of A) := 𝒰.glueMorphisms (fun j => (x j).1) fun i j =>
    congrArg Sigma.fst (hx i j _ _ _ pullback.condition)
  have hg : ∀ j, 𝒰.f j ≫ g = (x j).1 := fun j => 𝒰.ι_glueMorphisms _ _ j
  have hoi : ∀ j, IsOpenImmersion (bc A B g (𝒰.f j)) := fun j => isOpenImmersion_bc A B g (𝒰.f j)
  have hcov : ∀ p : ↥(pullback (str A B) g : Scheme.{0}), ∃ j q, bc A B g (𝒰.f j) q = p := by
    intro p
    obtain ⟨j, t, ht⟩ := 𝒰.exists_eq (pullback.snd (str A B) g p)
    have hr := (isPullback_bc A B g (𝒰.f j)).isoPullback_hom_fst
    have hmem : p ∈ Set.range (bc A B g (𝒰.f j)) := by
      rw [← hr, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso _).2, Set.image_univ,
        Scheme.Pullback.range_fst]
      exact ⟨t, ht⟩
    obtain ⟨q, hq⟩ := hmem
    exact ⟨j, q, hq⟩
  let J : ∀ j, (pullback (str A B) (𝒰.f j ≫ g)).IdealSheafData := fun j =>
    (x j).2.1.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hg j]))
  have hJ : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ pullback (str A B) (𝒰.f i ≫ g))
      (a' : Z ⟶ pullback (str A B) (𝒰.f j ≫ g)),
      a ≫ bc A B g (𝒰.f i) = a' ≫ bc A B g (𝒰.f j) → (J i).comap a = (J j).comap a' := by
    intro i j Z a a' e
    have f1 : ∀ k, bc A B g (𝒰.f k) ≫ pullback.fst (str A B) g = pullback.fst _ _ := fun k =>
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    have f2 : ∀ k, bc A B g (𝒰.f k) ≫ pullback.snd (str A B) g = pullback.snd _ _ ≫ 𝒰.f k :=
      fun k => pullback.lift_snd _ _ _
    have p1 : ∀ k (b : Z ⟶ pullback (str A B) (𝒰.f k ≫ g)),
        (b ≫ pullback.map (str A B) (𝒰.f k ≫ g) (str A B) (x k).1 (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp [hg k])) ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ := by
      intro k b; simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    have p2 : ∀ k (b : Z ⟶ pullback (str A B) (𝒰.f k ≫ g)),
        (b ≫ pullback.map (str A B) (𝒰.f k ≫ g) (str A B) (x k).1 (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp [hg k])) ≫ pullback.snd _ _ = b ≫ pullback.snd _ _ := by
      intro k b; simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    have e1 : a ≫ pullback.fst _ _ = a' ≫ pullback.fst _ _ := by
      rw [← f1 i, ← f1 j, ← Category.assoc, e, Category.assoc]
    have e2 : (a ≫ pullback.snd _ _) ≫ 𝒰.f i = (a' ≫ pullback.snd _ _) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← f2 i, ← f2 j, ← Category.assoc, e, Category.assoc]
    change ((x i).2.1.comap _).comap a = ((x j).2.1.comap _).comap a'
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    refine comap_eq_of_map_eq (x i) (x j) _ _ (by rw [p1, p1, e1]) ?_
    rw [p2, p2]
    exact hx i j Z _ _ e2
  obtain ⟨I, hI⟩ := glue_exists (fun j : 𝒰.I₀ => pullback (str A B) (𝒰.f j ≫ g))
    (fun j : 𝒰.I₀ => bc A B g (𝒰.f j)) hoi hcov J hJ
  have good : Good A B r g I := good_local A B r 𝒰.X 𝒰.f (fun j => inferInstance)
    (fun y => 𝒰.exists_eq y) g I (fun j => by rw [hI j]; exact good_transport (hg j) (x j).2.2)
  have amal : ∀ j, (functor A B r).map (𝒰.f j).op ⟨g, ⟨I, good⟩⟩ = x j := fun j =>
    sigma_eq A B r (hg j) (hI j) _ (x j).2.2
  refine ⟨⟨g, ⟨I, good⟩⟩, amal, fun y' hy' => ?_⟩
  replace hy' : ∀ j, (functor A B r).map (𝒰.f j).op y' = x j := hy'
  have e : y'.1 = g := 𝒰.hom_ext _ _ fun j => (congrArg Sigma.fst (hy' j)).trans (hg j).symm
  obtain ⟨g', I', hI'⟩ := y'
  change g' = g at e
  subst e
  have : I' = I := by
    refine glue_ext (fun j : 𝒰.I₀ => pullback (str A B) (𝒰.f j ≫ g))
      (fun j : 𝒰.I₀ => bc A B g (𝒰.f j)) hoi hcov I' I fun j => ?_
    have := (hy' j).trans (amal j).symm
    exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp this).2)
  subst this
  rfl

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeValuativeCriterionExistenceStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertScheme_valuativeCriterion_existence : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ValuativeCriterion.Existence (R.homEquiv (𝟙 H)).1 := by
  first | (exact @GlobalTheory.HilbAff.valuativeExistence) | (exact GlobalTheory.HilbAff.valuativeExistence) | (intros; apply GlobalTheory.HilbAff.valuativeExistence  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSpanGenerationStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_frame_span_generation : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N d h : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (ρ : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O)) (x : Fin N → Fin h → Ainf p O), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) → h = N * d → Submodule.span (Ainf p O) (Set.range fun ij : Fin N × Fin d => ρ (b ij.2) *ᵥ x ij.1) = ⊤ → ∃ e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame ρ e ∧ ∀ (i : Fin N) (l : Λ), e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = ρ l *ᵥ x i := by
  first | exact @GlobalTheory.DetInv.frame_of_spanning | exact GlobalTheory.DetInv.frame_of_spanning | (intros; apply GlobalTheory.DetInv.frame_of_spanning <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEqMulPowOfEqLocalizationAwayStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_eq_of_algebraMap_localizationAway_eq : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  first | exact @GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway | exact GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway | (intros; apply GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraNormRatGaussianExtensionOfPairStatement
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (a b : F), ((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  first | exact @GlobalTheory.GaussExt.norm_gEmb | exact GlobalTheory.GaussExt.norm_gEmb | (intros; apply GlobalTheory.GaussExt.norm_gEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinSchreierSystemIntegralStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_schreier_system_integral : ∀ (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] (d : ℕ) (U : Matrix (Fin d) (Fin d) S) (z : Fin d → S) (y : Fin d → K), (∀ i, y i ^ p = (U.map (algebraMap S K) *ᵥ y) i + algebraMap S K (z i)) → ∀ i, y i ∈ (algebraMap S K).range := by
  first | exact @GlobalTheory.frobenius_affine_integral | exact GlobalTheory.frobenius_affine_integral | (intros; apply GlobalTheory.frobenius_affine_integral <;> assumption)
end

