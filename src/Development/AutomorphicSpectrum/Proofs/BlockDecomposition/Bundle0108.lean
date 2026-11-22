import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0098
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0099
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorGeneratedLiftStatement
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_tensor_generated_lift : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K](S₁ : Type) [CommRing S₁] (i : S →ₐ[A] B) (I : Ideal S) (κ : K →+* S₁) (j : S →+* S₁) (i₁ : S₁ →+* B ⊗[A] K), Pf p A → Pf p K → PQ p (i : S →+* B) I → κ.comp (algebraMap A K) = j.comp (algebraMap A S) → Subring.closure (Set.range κ ∪ Set.range j) = ⊤ → (∀ a, i₁ (κ a) = (1 : B) ⊗ₜ[A] a) → (∀ s, i₁ (j s) = i s ⊗ₜ[A] (1 : K)) → PQ p i₁ (I.map j) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.pq_baseChange | exact GlobalTheory.CompanionTheory.PerfectRing.pq_baseChange | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.pq_baseChange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationMatrixProperties
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

namespace GlobalTheory.CompanionTheory.TyFin.Pm

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype K] [DecidableEq K] in

theorem pm_apply (σ : Equiv.Perm ι) (i j : ι) :
    (pm K σ : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
  show (Matrix.permMatrixHom (n := ι) (R := K) σ) i j = _
  rw [Matrix.permMatrixHom_apply]
  show (σ⁻¹ : Equiv.Perm ι).toPEquiv.toMatrix i j = _
  rw [PEquiv.toMatrix_apply]
  by_cases h : i = σ j
  · subst h
    simp
  · have h' : j ≠ σ.symm i := fun e => h (by rw [e, Equiv.apply_symm_apply])
    simp [h, Ne.symm h']

omit [Fintype K] [DecidableEq K] in

theorem glEquiv_apply {κ : Type} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (g : GL ι K) (i j : κ) :
    (glEquiv K e g : Matrix κ κ K) i j = (g : Matrix ι ι K) (e.symm i) (e.symm j) := rfl

theorem pm_conj (σ : Equiv.Perm ι) (g : GL ι K) :
    pm K σ * g * (pm K σ)⁻¹ = glEquiv K σ g := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, pm_apply, glEquiv_apply]
  rw [Finset.sum_eq_single (σ.symm i), Finset.sum_eq_single (σ j)]
  · simp
  · intro x _ hx
    simp [hx]
  · simp
  · intro x _ hx
    have : i ≠ σ x := fun h => hx (by rw [h]; simp)
    simp [this]
  · simp

omit [Fintype K] [DecidableEq K] in
theorem isBlockUT_glEquiv {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (g : GL ι K) :
    IsBlockUT K b (glEquiv K σ g : Matrix ι ι K) ↔ IsBlockUT K (b ∘ σ) (g : Matrix ι ι K) := by
  constructor
  · intro H i j hlt
    have := H (σ i) (σ j) hlt
    simpa [glEquiv_apply] using this
  · intro H i j hlt
    rw [glEquiv_apply]
    exact H _ _ (by simpa using hlt)

theorem glEquiv_mem_parab {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (g : GL ι K) :
    glEquiv K σ g ∈ parab K b ↔ g ∈ parab K (b ∘ σ) := by
  show (IsBlockUT K b _ ∧ IsBlockUT K b _) ↔ (IsBlockUT K (b ∘ σ) _ ∧ IsBlockUT K (b ∘ σ) _)
  rw [← map_inv, isBlockUT_glEquiv, isBlockUT_glEquiv]

theorem cj_pm_parab {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) :
    cj (pm K σ) (parab K b) = parab K (b ∘ σ) := by
  ext h
  rw [mem_cj, pm_conj, glEquiv_mem_parab]

theorem blkGL_glEquiv {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (c : Fin s) (g : GL ι K)
    (e : {i // (b ∘ σ) i = c} ≃ {j // b j = c})
    (he : ∀ x, (e x : ι) = σ x) :
    blkGL b c (glEquiv K σ g) = glEquiv K e (blkGL (b ∘ σ) c g) := by
  unfold blkGL
  by_cases h : g ∈ parab K (b ∘ σ)
  · rw [dif_pos h, dif_pos ((glEquiv_mem_parab b σ g).2 h)]
    apply Units.ext
    ext ⟨i, hi⟩ ⟨j, hj⟩
    rw [glEquiv_apply]
    have key : ∀ y : {j // b j = c}, ((e.symm y : {i // (b ∘ σ) i = c}) : ι) = σ.symm y := by
      intro y
      rw [Equiv.eq_symm_apply, ← he, Equiv.apply_symm_apply]
    show (glEquiv K σ g : Matrix ι ι K) i j = (g : Matrix ι ι K) _ _
    rw [glEquiv_apply]
    exact congrArg₂ (g : Matrix ι ι K) (key ⟨i, hi⟩).symm (key ⟨j, hj⟩).symm
  · rw [dif_neg h, dif_neg (fun h' => h ((glEquiv_mem_parab b σ g).1 h')), map_one]

theorem pmFacts : ReciprocityTheory.Ty.Fin.St.PmFacts := by
  intro K _ _ _ ι _ _ σ
  refine ⟨pm_apply σ, pm_conj σ, fun s b => cj_pm_parab b σ, ?_⟩
  intro s b χ g
  unfold hcFun
  exact Finset.prod_congr rfl fun c _ => congrArg (χ c) (blkGL_glEquiv b σ c g
    (σ.subtypeEquiv (p := fun i => (b ∘ σ) i = c) (q := fun j => b j = c) fun _ => Iff.rfl) fun _ => rfl)

end GlobalTheory.CompanionTheory.TyFin.Pm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetOppositeNeg
section
open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliAntipode

theorem unop_ofFn_prod {A : Type*} [Ring A] : ∀ {t : ℕ} (f : Fin t → Aᵐᵒᵖ),
    MulOpposite.unop (List.ofFn f).prod = (List.ofFn fun i => MulOpposite.unop (f i.rev)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul, unop_ofFn_prod (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => MulOpposite.unop (f i.rev)), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]

theorem ofFn_prod_neg {A : Type*} [Ring A] [Algebra ℂ A] : ∀ {t : ℕ} (g : Fin t → A),
    (List.ofFn fun k => -g k).prod = ((-1 : ℂ) ^ t) • (List.ofFn g).prod
  | 0, g => by simp
  | t + 1, g => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_neg (fun k => g k.succ), List.ofFn_succ (f := g),
      List.prod_cons, pow_succ, mul_comm, mul_smul, neg_mul, mul_smul_comm, neg_one_smul]

theorem Tm_op_neg {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ)
    (i j : Fin n) :
    Tm (fun i j => MulOpposite.op (-X i j)) w i j = MulOpposite.op (-(Tm X (-w) i j)) := by
  unfold Tm
  by_cases h : i = j
  · simp [h, MulOpposite.algebraMap_apply, add_comm]
  · simp [h]

theorem arg_rev {t : ℕ} (v : ℂ) (j : Fin t) :
    -(v - (((Fin.rev j : Fin t) : ℕ) : ℂ)) = ((t : ℂ) - 1 - v) - ((j : ℕ) : ℂ) := by
  have hj := j.isLt
  rw [Fin.val_rev, Nat.cast_sub (by omega : (j : ℕ) + 1 ≤ t)]
  push_cast
  ring

theorem unop_term {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (v : ℂ)
    (σ : Equiv.Perm (Fin n)) :
    MulOpposite.unop ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Aᵐᵒᵖ) *
        (List.ofFn fun k : Fin n =>
          Tm (fun i j => MulOpposite.op (-X i j)) (v - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod) =
      ((-1 : ℂ) ^ n) • ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun j : Fin n =>
          Tm X (((n : ℂ) - 1 - v) - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod) := by
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast, unop_ofFn_prod]
  simp only [Tm_op_neg, MulOpposite.unop_op, id, arg_rev]
  rw [ofFn_prod_neg, smul_mul_assoc, ← Int.cast_comm]

theorem qminor_id_rev {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ) :
    qminor X id (id ∘ (Fin.revPerm : Equiv.Perm (Fin n))) w =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
        ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
          (List.ofFn fun j : Fin n => Tm X (w - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod := by
  unfold qminor
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ (fun σ => ?_)).symm
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Equiv.Perm.mul_apply, Fin.revPerm_apply,
    Function.comp_apply, id, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, Int.cast_comm]

theorem unop_qdet_op_neg (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (v : ℂ) :
    MulOpposite.unop (qdet (fun i j => MulOpposite.op (-X i j)) v) =
      ((-1 : ℂ) ^ n) • qdet X ((n : ℂ) - 1 - v) := by
  have hs := quantumMinorColSkew_holds A n n X hX id id (Fin.revPerm : Equiv.Perm (Fin n)) ((n : ℂ) - 1 - v)
  rw [qminor_id_rev] at hs
  have hu : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have h2 := congrArg (fun x => (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) * x) hs
  simp only [← mul_assoc, hu, one_mul] at h2
  have h3 : qdet X ((n : ℂ) - 1 - v) = _ := h2.symm
  rw [h3]
  unfold qdet qminor
  rw [Finset.unop_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun σ _ => unop_term X v σ

end GlobalTheory.CompanionTheory.CapelliAntipode
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexAnnihilatorsDuality
section
open Matrix
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.IndexDuality

theorem relIndex_le_of_pairing {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (b : X → Y → Circle)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (H₀ H : AddSubgroup Y) (R₀ R : AddSubgroup X)
    (hfin : H₀.relIndex H ≠ 0)
    (hann : ∀ x ∈ R₀, ∀ y ∈ H₀, b x y = 1)
    (hsep : ∀ x ∈ R₀, (∀ y ∈ H, b x y = 1) → x ∈ R) :
    R.relIndex R₀ ≠ 0 ∧ R.relIndex R₀ ≤ H₀.relIndex H := by
  classical
  have hQfin : Finite (H ⧸ H₀.addSubgroupOf H) := Nat.finite_of_card_ne_zero hfin
  have hb0 : ∀ x, b x 0 = 1 := by
    intro x
    have h := hr x 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (a := b x 0) (by rw [mul_one]; exact h)).symm
  have hb0' : ∀ y, b 0 y = 1 := by
    intro y
    have h := hl 0 0 y
    rw [add_zero] at h
    exact (mul_left_cancel (a := b 0 y) (by rw [mul_one]; exact h)).symm
  let f : R₀ → H →+ Additive Circle := fun x =>
    { toFun := fun y => Additive.ofMul (b x y)
      map_zero' := by simp [hb0]
      map_add' := fun y y' => by simp [hr] }
  have hker : ∀ x : R₀, ∀ y ∈ H₀.addSubgroupOf H, f x y = 0 := by
    intro x y hy
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    simp [f, hann x x.2 y hy]
  let g : R₀ → (H ⧸ H₀.addSubgroupOf H) →+ Additive Circle := fun x =>
    QuotientAddGroup.lift (H₀.addSubgroupOf H) (f x) (hker x)
  let χ : R₀ → AddChar (H ⧸ H₀.addSubgroupOf H) Circle := fun x =>
    { toFun := fun q => Additive.toMul (g x q)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun q q' => by simp [map_add] }
  have hχ : ∀ (x : R₀) (y : H), χ x (QuotientAddGroup.mk y) = b x y := fun x y => rfl
  let Ψ : R₀ →+ AddChar (H ⧸ H₀.addSubgroupOf H) Circle :=
    { toFun := χ
      map_zero' := by
        ext1 q
        induction q using QuotientAddGroup.induction_on with
        | H y =>
          rw [hχ]
          exact hb0' y
      map_add' := fun x x' => by
        ext1 q
        induction q using QuotientAddGroup.induction_on with
        | H y =>
          rw [hχ]
          change b (x + x') y = (χ x * χ x') (QuotientAddGroup.mk y)
          rw [AddChar.mul_apply, hχ, hχ]
          exact hl x x' y }
  have hkerle : Ψ.ker ≤ R.addSubgroupOf R₀ := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddSubgroup.mem_addSubgroupOf]
    refine hsep x x.2 (fun y hy => ?_)
    have := congrArg (fun φ : AddChar (H ⧸ H₀.addSubgroupOf H) Circle => φ (QuotientAddGroup.mk ⟨y, hy⟩)) hx
    simpa [Ψ, hχ] using this
  have : Fintype (H ⧸ H₀.addSubgroupOf H) := Fintype.ofFinite _
  have hinjC : Function.Injective fun φ : AddChar (H ⧸ H₀.addSubgroupOf H) Circle => Circle.coeHom.compAddChar φ :=
    MonoidHom.compAddChar_injective_right _ Circle.coe_injective
  have : Finite (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) := Finite.of_injective _ hinjC
  have hcardC : Nat.card (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) ≤ H₀.relIndex H := by
    have h1 := Nat.card_le_card_of_injective _ hinjC
    rw [Nat.card_eq_fintype_card (α := AddChar (H ⧸ H₀.addSubgroupOf H) ℂ), AddChar.card_eq,
      ← Nat.card_eq_fintype_card] at h1
    exact h1
  have : Finite (R₀ ⧸ Ψ.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective Ψ)
  have hkerfin : Ψ.ker.index ≤ Nat.card (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) :=
    Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective Ψ)
  have hker0 : Ψ.ker.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have hdvd := AddSubgroup.index_dvd_of_le hkerle
  have hR0 : (R.addSubgroupOf R₀).index ≠ 0 := fun h0 => hker0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  refine ⟨hR0, ?_⟩
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hker0) hdvd).trans (hkerfin.trans hcardC)

theorem relIndex_annihilator_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A₀ A P₀ P : AddSubgroup (Fin n → k)), IsCompact (A₀ : Set (Fin n → k)) →
    IsOpen (A₀ : Set (Fin n → k)) → IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → A₀ ≤ A → (∀ ξ, ξ ∈ P₀ ↔ ∀ a ∈ A₀, ψ (ξ ⬝ᵥ a) = 1) →
    (∀ ξ, ξ ∈ P ↔ ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1) → P.relIndex P₀ = A₀.relIndex A := by
  intro k _ _ _ _ ψ hψc hψ1 n A₀ A P₀ P hA₀c hA₀o hAc hAo hle hP₀ hP
  have hfin : A₀.relIndex A ≠ 0 :=
    GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen A A₀ hAc hA₀o hle
  have h1 := relIndex_le_of_pairing (fun ξ a : Fin n → k => ψ (ξ ⬝ᵥ a))
    (fun ξ ξ' a => by simp [add_dotProduct, AddChar.map_add_eq_mul])
    (fun ξ a a' => by simp [dotProduct_add, AddChar.map_add_eq_mul])
    A₀ A P₀ P hfin (fun ξ hξ a ha => (hP₀ ξ).mp hξ a ha) (fun ξ _ h => (hP ξ).mpr h)
  have h2 := relIndex_le_of_pairing (fun a ξ : Fin n → k => ψ (ξ ⬝ᵥ a))
    (fun a a' ξ => by simp [dotProduct_add, AddChar.map_add_eq_mul])
    (fun a ξ ξ' => by simp [add_dotProduct, AddChar.map_add_eq_mul])
    P P₀ A A₀ h1.1 (fun a _ ξ hξ => (hP ξ).mp hξ a ‹_›) (fun a _ h => by
      by_contra hna
      obtain ⟨η, hη, hne⟩ := GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne k ψ hψc hψ1 n A₀ hA₀c hA₀o a hna
      exact hne (h η ((hP₀ η).mpr hη)))
  exact le_antisymm h1.2 h2.2

end GlobalTheory.CompanionTheory.IndexDuality
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SamePartitionStatement
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinSamePart

theorem avg_of_surjective {G Q : Type} [Group G] [Group Q] [Fintype G] [Fintype Q]
    (f : G →* Q) (hf : Function.Surjective f) (F : Q → ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, F (f g) = (Fintype.card Q : ℂ)⁻¹ * ∑ q, F q := by
  classical
  set N : ℕ := (Finset.univ.filter fun g => f g = 1).card with hN
  have hfib : ∀ q, (Finset.univ.filter fun g => f g = q).card = N := fun q =>
    MonoidHom.card_fiber_eq_of_mem_range f (hf q) (hf 1)
  have hsum : ∀ F' : Q → ℂ, ∑ g, F' (f g) = N * ∑ q, F' q := by
    intro F'
    rw [← Finset.sum_fiberwise Finset.univ f (fun g => F' (f g)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => F' q)
      (by intro g hg; rw [(Finset.mem_filter.mp hg).2])]
    simp [hfib q]
  have hcard : (Fintype.card G : ℂ) = N * Fintype.card Q := by
    simpa using hsum fun _ => 1
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hN0 : (N : ℂ) ≠ 0 := fun h => hG (by rw [hcard, h, zero_mul])
  have hQ : (Fintype.card Q : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hsum, hcard]
  field_simp

theorem ip_coe {Γ : Type} [Group Γ] [Fintype Γ] (H : Subgroup Γ) [Fintype H] (a c : Γ → ℂ) :
    ip (H : Set Γ) a c = (Fintype.card H : ℂ)⁻¹ * ∑ h : H, a (h : Γ)⁻¹ * c h := by
  classical
  unfold ip
  have h1 : (H : Set Γ).ncard = Fintype.card H := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_eq_fintype_card
  rw [h1, ← Finset.sum_filter]
  congr 1
  exact Finset.sum_subtype _ (by simp) (fun g => a g⁻¹ * c g)

theorem ip_univ {Γ : Type} [Group Γ] [Fintype Γ] (a c : Γ → ℂ) :
    ip Set.univ a c = (Fintype.card Γ : ℂ)⁻¹ * ∑ g, a g⁻¹ * c g := by
  simp [ip, Set.ncard_univ, Nat.card_eq_fintype_card]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

def bd (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) : Matrix ι ι K :=
  fun i j => if h : b j = b i then L (b i) ⟨i, rfl⟩ ⟨j, h⟩ else 0

theorem bd_blk (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) (c : Fin s) :
    blk K b c (bd b L) = L c := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  subst hi
  simp [blk, bd, hj]

theorem bd_off (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) {i j : ι}
    (h : b j ≠ b i) : bd b L i j = 0 := dif_neg h

theorem eq_bd (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) {M : Matrix ι ι K}
    (h1 : ∀ c, blk K b c M = L c) (h2 : ∀ i j, b j ≠ b i → M i j = 0) : M = bd b L := by
  ext i j
  by_cases h : b j = b i
  · have := congrFun (congrFun (h1 (b i)) ⟨i, rfl⟩) ⟨j, h⟩
    simpa [bd, h, blk] using this
  · rw [bd_off b L h, h2 i j h]

theorem isBlockUT_bd {s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s')
    (hb : ∀ i j, b' j < b' i → b j ≠ b i) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) :
    IsBlockUT K b' (bd b L) := fun i j h => bd_off b L (hb i j h)

theorem bd_one (b : ι → Fin s) : bd b (fun c => (1 : Matrix {i // b i = c} {i // b i = c} K)) = 1 := by
  symm
  apply eq_bd
  · intro c
    exact Matrix.submatrix_one _ Subtype.val_injective
  · intro i j h
    exact Matrix.one_apply_ne fun e => h (by rw [e])

theorem bd_mul (b : ι → Fin s) (L L' : ∀ c, Matrix {i // b i = c} {i // b i = c} K) :
    bd b (fun c => L c * L' c) = bd b L * bd b L' := by
  have hut : ∀ M : ∀ c, Matrix {i // b i = c} {i // b i = c} K, IsBlockUT K b (bd b M) := fun M =>
    isBlockUT_bd b b (fun i j h e => by rw [e] at h; exact lt_irrefl _ h) M
  symm
  apply eq_bd
  · intro c
    rw [blk_mul b c (hut L) (hut L'), bd_blk, bd_blk]
  · intro i j h
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : b k = b i
    · rw [bd_off b L' (i := k) (j := j) (by rw [hk]; exact h), mul_zero]
    · rw [bd_off b L hk, zero_mul]

def dGL (b : ι → Fin s) (L : ∀ c, GL {i // b i = c} K) : GL ι K where
  val := bd b fun c => (L c : Matrix _ _ K)
  inv := bd b fun c => ((L c)⁻¹ : GL _ K).1
  val_inv := by
    rw [← bd_mul]
    simp only [Units.mul_inv]
    exact bd_one b
  inv_val := by
    rw [← bd_mul]
    simp only [Units.inv_mul]
    exact bd_one b

theorem dGL_mem {s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s')
    (hb : ∀ i j, b' j < b' i → b j ≠ b i) (L : ∀ c, GL {i // b i = c} K) : dGL b L ∈ parab K b' :=
  ⟨show IsBlockUT K b' (bd b fun c => (L c).1) from isBlockUT_bd b b' hb _,
    show IsBlockUT K b' (bd b fun c => ((L c)⁻¹ : GL _ K).1) from isBlockUT_bd b b' hb _⟩

def leviHom (b : ι → Fin s) : parab K b →* ∀ c, GL {i // b i = c} K where
  toFun p c := levi K b c p
  map_one' := by
    funext c
    apply Units.ext
    exact Matrix.submatrix_one _ Subtype.val_injective
  map_mul' p q := by
    funext c
    apply Units.ext
    exact blk_mul b c p.2.1 q.2.1

theorem blkGL_of_mem (b : ι → Fin s) (c : Fin s) {g : GL ι K} (h : g ∈ parab K b) :
    blkGL b c g = leviHom b ⟨g, h⟩ c := dif_pos h

theorem blkGL_inv (b : ι → Fin s) (c : Fin s) {g : GL ι K} (h : g ∈ parab K b) :
    blkGL b c g⁻¹ = (leviHom b ⟨g, h⟩ c)⁻¹ := by
  rw [blkGL_of_mem b c (inv_mem h), ← Pi.inv_apply, ← map_inv]
  rfl

abbrev ren {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') (c : Fin s) :
    {i // b i = c} ≃ {i // (π ∘ b) i = π c} :=
  Equiv.subtypeEquivRight (p := fun i => b i = c) (q := fun i => (π ∘ b) i = π c)
    fun _ => π.injective.eq_iff.symm

theorem blkGL_ren {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') (c : Fin s) {g : GL ι K}
    (h : g ∈ parab K b) (h' : g ∈ parab K (π ∘ b)) :
    blkGL (π ∘ b) (π c) g = glEquiv K (ren b π c) (leviHom b ⟨g, h⟩ c) := by
  rw [blkGL_of_mem _ _ h']
  apply Units.ext
  ext i j
  rfl

def ell {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') :
    (parab K b ⊓ parab K (π ∘ b) : Subgroup (GL ι K)) →* ∀ c, GL {i // b i = c} K :=
  (leviHom b).comp (Subgroup.inclusion inf_le_left)

theorem ell_surjective {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') :
    Function.Surjective (ell (K := K) b π) := by
  intro L
  have h1 : dGL b L ∈ parab K b := dGL_mem b b (fun i j h e => by rw [e] at h; exact lt_irrefl _ h) L
  have h2 : dGL b L ∈ parab K (π ∘ b) :=
    dGL_mem b (π ∘ b) (fun i j h e => by simp only [Function.comp, e] at h; exact lt_irrefl _ h) L
  refine ⟨⟨dGL b L, h1, h2⟩, ?_⟩
  funext c
  apply Units.ext
  exact bd_blk b (fun c => (L c).1) c

theorem samePart : ReciprocityTheory.Ty.Fin.St.SamePart := by
  intro K _ _ _ ι _ _ s s' b π χ ψ
  classical
  let F : (∀ c, GL {i // b i = c} K) → ℂ := fun q =>
    ∏ c, (χ c (q c)⁻¹ * ψ (π c) (glEquiv K (ren b π c) (q c)))
  have key : ∀ h : (parab K b ⊓ parab K (π ∘ b) : Subgroup (GL ι K)),
      hcFun b χ (h : GL ι K)⁻¹ * hcFun (π ∘ b) ψ h = F (ell b π h) := by
    rintro ⟨g, h1, h2⟩
    simp only [F, Finset.prod_mul_distrib, hcFun]
    congr 1
    · exact Finset.prod_congr rfl fun c _ => by rw [blkGL_inv b c h1]; rfl
    · rw [← Equiv.prod_comp π]
      exact Finset.prod_congr rfl fun c _ => by rw [blkGL_ren b π c h1 h2]; rfl
  rw [ip_coe, Finset.sum_congr rfl (fun h _ => key h),
    avg_of_surjective (ell (K := K) b π) (ell_surjective b π) F]
  simp only [ip_univ, F]
  rw [Finset.prod_mul_distrib, Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

end GlobalTheory.CompanionTheory.TyFinSamePart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformHorizontalInvarianceStatement
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tube_transform_horizontal_invariance : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) → ∀ t : ℝ × ℝ, phi G (a, c) t = phi G (b, c) t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst | exact GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformVerticalInvarianceStatement
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tube_transform_vertical_invariance : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (c, s) ∈ Ω) → ∀ t : ℝ × ℝ, phi G (c, a) t = phi G (c, b) t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd | exact GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_shift_snd <;> assumption)
end

