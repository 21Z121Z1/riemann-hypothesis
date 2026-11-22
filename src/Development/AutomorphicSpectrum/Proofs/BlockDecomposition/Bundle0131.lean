import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0125
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumNeZeroEqSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemInjectiveExtension
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

section Tuples
variable {ι : Type}

theorem cons_comp_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Fin.succAbove_zero]

theorem cons_comp_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons a i : Fin (n + 2) → ι) ∘ k.succ.succAbove = Fin.cons a (i ∘ k.succAbove) := by
  funext t
  cases t using Fin.cases with
  | zero => simp only [Function.comp_apply, Fin.succ_succAbove_zero, Fin.cons_zero]
  | succ t => simp only [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ]

theorem mem_ent_cons [DecidableEq ι] {n : ℕ} {a x : ι} {i : Fin n → ι}
    (h : x ∈ ent (Fin.cons a i : Fin (n + 1) → ι)) : x = a ∨ x ∈ ent i := by
  simp only [ent, Finset.mem_image, Finset.mem_univ, true_and] at h ⊢
  obtain ⟨k, rfl⟩ := h
  cases k using Fin.cases with
  | zero =>
    left
    simp only [Fin.cons_zero]
  | succ k =>
    right
    exact ⟨k, by simp only [Fin.cons_succ]⟩

end Tuples

section Coordinates
variable {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W] [Module K W] {Λ : Type}
  (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι)

def Sup (S : Finset ι) (w : W) : Prop := ∀ l, b.repr w l ≠ 0 → good' l ∧ T l ⊆ S

theorem mem_span_iff (S : Finset ι) (w : W) :
    w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S}) ↔ Sup b good' T S w := by
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h l hl
    exact h (Finsupp.mem_support_iff.2 hl)
  · intro h l hl
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hl
    exact h l hl

theorem coord_sum {n : ℕ} (D : Fin n → W) (l : Λ) :
    b.repr (∑ k : Fin n, (-1 : ℤ) ^ (k : ℕ) • D k) l = ∑ k : Fin n, (-1 : ℤ) ^ (k : ℕ) • b.repr (D k) l := by
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Finsupp.smul_apply]

open Classical in

def contr {n : ℕ} (C : (Fin (n + 1) → ι) → W) (a : ∀ l, good' l → ι) (i : Fin n → ι) : W :=
  b.repr.symm (Finsupp.onFinset (Finset.univ.biUnion fun a' : ι => (b.repr (C (Fin.cons a' i))).support)
    (fun l => if h : good' l then b.repr (C (Fin.cons (a l h) i)) l else 0) (by
      intro l hl
      by_cases h : good' l
      · rw [dif_pos h] at hl
        exact Finset.mem_biUnion.2 ⟨a l h, Finset.mem_univ _, Finsupp.mem_support_iff.2 hl⟩
      · rw [dif_neg h] at hl
        exact absurd rfl hl))

open Classical in
theorem contr_apply {n : ℕ} (C : (Fin (n + 1) → ι) → W) (a : ∀ l, good' l → ι) (i : Fin n → ι) (l : Λ) :
    b.repr (contr b good' C a i) l = if h : good' l then b.repr (C (Fin.cons (a l h) i)) l else 0 := by
  unfold contr
  rw [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply]

theorem contr_sup {n : ℕ} (C : (Fin (n + 1) → ι) → W) (hC : ∀ i, Sup b good' T (ent i) (C i))
    (a : ∀ l, good' l → ι) (ha : ∀ l h, a l h ∉ T l) (i : Fin n → ι) :
    Sup b good' T (ent i) (contr b good' C a i) := by
  intro l hl
  rw [contr_apply] at hl
  by_cases h : good' l
  · rw [dif_pos h] at hl
    obtain ⟨-, hT⟩ := hC _ l hl
    refine ⟨h, fun x hx => ?_⟩
    rcases mem_ent_cons (hT hx) with rfl | hx'
    · exact absurd hx (ha l h)
    · exact hx'
  · rw [dif_neg h] at hl
    exact absurd rfl hl

theorem homotopy {n : ℕ} (C : (Fin (n + 1) → ι) → W) (hC : ∀ i, Sup b good' T (ent i) (C i))
    (hZ : ∀ i : Fin (n + 2) → ι, ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • C (i ∘ k.succAbove) = 0)
    (a : ∀ l, good' l → ι) (i : Fin (n + 1) → ι) :
    ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • contr b good' C a (i ∘ k.succAbove) = C i := by
  apply b.repr.injective
  ext l
  rw [coord_sum]
  simp only [contr_apply]
  by_cases h : good' l
  · simp only [dif_pos h]
    have hz := congrArg (fun w => b.repr w l) (hZ (Fin.cons (a l h) i))
    rw [Fin.sum_univ_succ] at hz
    simp only [Fin.val_zero, pow_zero, one_smul, cons_comp_zero, Fin.val_succ, cons_comp_succ,
      map_add, map_sum, map_zsmul, Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, pow_succ, mul_neg, mul_one,
      neg_smul, Finset.sum_neg_distrib, map_neg, Finsupp.coe_neg, Pi.neg_apply] at hz
    rw [← sub_eq_add_neg, sub_eq_zero] at hz
    exact hz.symm
  · simp only [dif_neg h, smul_zero, Finset.sum_const_zero]
    by_contra hne
    exact h (hC i l (Ne.symm hne)).1

end Coordinates

section Main

theorem j_dZ {ι : Type} [DecidableEq ι] {W : Type} [AddCommGroup W] (M : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W)
    (hr : ∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) (i : Fin (m + 2) → ι) :
    j (ent i) (dZ M r m c i) = ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) := by
  simp only [dZ, map_sum, map_zsmul, hr]

theorem exP_of_basis : ∀ {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W]
    [Module K W] {Λ : Type} (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι),
    (∀ l, good' l → T l ≠ Finset.univ) → ∀ (M : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W), (∀ S, Function.Injective (j S)) →
    (∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) →
    (∀ S w, (∃ x, j S x = w) ↔ w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S})) → ExP M r := by
  intro K _ ι _ _ W _ _ Λ b good' T hT M _ r j hj hr hspan
  have hout : ∀ l, good' l → ∃ y, y ∉ T l := by
    intro l hl
    by_contra hc
    push Not at hc
    exact hT l hl (Finset.eq_univ_iff_forall.2 hc)
  choose a ha using hout
  have hsup : ∀ S (x : M S), Sup b good' T S (j S x) := fun S x =>
    (mem_span_iff b good' T S _).1 ((hspan S _).1 ⟨x, rfl⟩)
  have hlift : ∀ S w, Sup b good' T S w → ∃ x, j S x = w := fun S w h =>
    (hspan S w).2 ((mem_span_iff b good' T S w).2 h)
  refine ⟨fun x hx => ?_, fun c hc => ?_, fun m c hc => ?_⟩
  · have hw : j ∅ x = 0 := by
      apply b.repr.injective
      ext l
      rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
      by_contra hne
      obtain ⟨hg, -⟩ := hsup ∅ x l hne
      have h0 := hr (Finset.empty_subset (ent (fun _ : Fin 1 => a l hg))) x
      have hx0 : r (Finset.empty_subset (ent (fun _ : Fin 1 => a l hg))) x = 0 := hx _
      rw [hx0, map_zero] at h0
      rw [← h0] at hne
      exact hne (by rw [map_zero, Finsupp.coe_zero, Pi.zero_apply])
    exact hj ∅ (hw.trans (map_zero (j ∅)).symm)
  · have hZ : ∀ i : Fin (0 + 2) → ι,
        ∑ k : Fin (0 + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) = 0 := by
      intro i
      rw [← j_dZ M r j hr 0 c i, hc, Pi.zero_apply, map_zero]
    have hCs : ∀ i : Fin (0 + 1) → ι, Sup b good' T (ent i) (j (ent i) (c i)) := fun i => hsup _ (c i)
    have hw := contr_sup b good' T (fun i : Fin (0 + 1) → ι => j (ent i) (c i)) hCs a ha Fin.elim0
    have he : ent (Fin.elim0 : Fin 0 → ι) = ∅ := by simp [ent]
    rw [he] at hw
    obtain ⟨x, hx⟩ := hlift ∅ _ hw
    refine ⟨x, fun i => hj _ ?_⟩
    rw [hr, hx]
    have hh := homotopy b good' T (fun i : Fin (0 + 1) → ι => j (ent i) (c i)) hCs hZ a i
    rw [Fin.sum_univ_succ] at hh
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero,
      one_smul] at hh
    convert hh using 2
  · have hZ : ∀ i : Fin (m + 1 + 2) → ι,
        ∑ k : Fin (m + 1 + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) = 0 := by
      intro i
      rw [← j_dZ M r j hr (m + 1) c i, hc, Pi.zero_apply, map_zero]
    have hCs : ∀ i : Fin (m + 1 + 1) → ι, Sup b good' T (ent i) (j (ent i) (c i)) :=
      fun i => hsup _ (c i)
    have hb : ∀ i' : Fin (m + 1) → ι, ∃ x : M (ent i'),
        j (ent i') x = contr b good' (fun i : Fin (m + 1 + 1) → ι => j (ent i) (c i)) a i' :=
      fun i' => hlift _ _ (contr_sup b good' T _ hCs a ha i')
    choose b' hb' using hb
    refine ⟨b', funext fun i => hj _ ?_⟩
    rw [j_dZ M r j hr m b' i]
    simp only [hb']
    exact homotopy b good' T (fun i : Fin (m + 1 + 1) → ι => j (ent i) (c i)) hCs hZ a i

end Main

end GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemScalarTowerExt
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4 TensorProduct

section Core
variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A]
variable {P Q R P' Q' R' : Type} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
  [Module B P] [Module B Q] [Module B R]
  [AddCommGroup P'] [AddCommGroup Q'] [AddCommGroup R']
  [Module A P'] [Module A Q'] [Module A R'] [Module B P'] [Module B Q'] [Module B R']
  [IsScalarTower B A P'] [IsScalarTower B A Q'] [IsScalarTower B A R']

theorem equiv_lTensor {p : P →ₗ[B] P'} {q : Q →ₗ[B] Q'} (hp : IsBaseChange A p) (hq : IsBaseChange A q)
    (f : P →ₗ[B] Q) (f' : P' →ₗ[A] Q') (h : ∀ x, f' (p x) = q (f x)) (z : A ⊗[B] P) :
    f' (hp.equiv z) = hq.equiv (LinearMap.lTensor A f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [IsBaseChange.equiv_tmul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exact_core [Module.Flat B A] {p : P →ₗ[B] P'} {q : Q →ₗ[B] Q'} {s : R →ₗ[B] R'}
    (hp : IsBaseChange A p) (hq : IsBaseChange A q) (hs : IsBaseChange A s)
    (f : P →ₗ[B] Q) (g : Q →ₗ[B] R) (f' : P' →ₗ[A] Q') (g' : Q' →ₗ[A] R')
    (hf : ∀ x, f' (p x) = q (f x)) (hg : ∀ x, g' (q x) = s (g x))
    (hex : ∀ y, g y = 0 → ∃ x, f x = y) : ∀ y, g' y = 0 → ∃ x, f' x = y := by
  intro y hy
  let P0 : Submodule B P := (LinearMap.ker g).comap f
  let f0 : P0 →ₗ[B] Q := f ∘ₗ P0.subtype
  have h0 : Function.Exact f0 g := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hex y hy
      exact ⟨⟨x, hy⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.2
  have h1 := Module.Flat.lTensor_exact A h0
  have h2 : LinearMap.lTensor A g (hq.equiv.symm y) = 0 := by
    apply hs.equiv.injective
    rw [← equiv_lTensor hq hs g g' hg, LinearEquiv.apply_symm_apply, hy, map_zero]
  obtain ⟨z, hz⟩ := (h1 _).1 h2
  refine ⟨hp.equiv (LinearMap.lTensor A P0.subtype z), ?_⟩
  have h3 : LinearMap.lTensor A f (LinearMap.lTensor A P0.subtype z) = LinearMap.lTensor A f0 z := by
    simp only [f0, LinearMap.lTensor_comp, LinearMap.comp_apply]
  rw [equiv_lTensor hp hq f f' hf, h3, hz, LinearEquiv.apply_symm_apply]

theorem inj_core [Module.Flat B A] {q : Q →ₗ[B] Q'} {s : R →ₗ[B] R'}
    (hq : IsBaseChange A q) (hs : IsBaseChange A s)
    (g : Q →ₗ[B] R) (g' : Q' →ₗ[A] R') (hg : ∀ x, g' (q x) = s (g x))
    (hinj : ∀ y, g y = 0 → y = 0) : ∀ y, g' y = 0 → y = 0 := by
  intro y hy
  have hi : Function.Injective g := (injective_iff_map_eq_zero g).2 hinj
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := A) g hi
  have h2 : LinearMap.lTensor A g (hq.equiv.symm y) = 0 := by
    apply hs.equiv.injective
    rw [← equiv_lTensor hq hs g g' hg, LinearEquiv.apply_symm_apply, hy, map_zero]
  have h3 : hq.equiv.symm y = 0 := h1 (h2.trans (map_zero _).symm)
  simpa using h3
end Core

section Cech
variable {ι : Type} [DecidableEq ι]

def dZL (K : Type) [CommRing K] (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module K (M S)]
    (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (hr : ∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap K (r h)) (m : ℕ) :
    (∀ i : Fin (m + 1) → ι, M (ent i)) →ₗ[K] ∀ i : Fin (m + 2) → ι, M (ent i) where
  toFun := dZ M r m
  map_add' c c' := by
    funext i
    simp only [Pi.add_apply, dZ]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_add]
    exact congrArg _ ((hr (ent_comp i k.succAbove)).map_add _ _)
  map_smul' a c := by
    funext i
    rw [RingHom.id_apply, Pi.smul_apply]
    change ∑ k : Fin (m + 2), _ = a • ∑ k : Fin (m + 2), _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm a]
    exact congrArg _ ((hr (ent_comp i k.succAbove)).map_smul a _)

def augL (K : Type) [CommRing K] (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module K (M S)]
    (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (hr : ∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap K (r h)) :
    M ∅ →ₗ[K] ∀ i : Fin (0 + 1) → ι, M (ent i) where
  toFun x i := r (Finset.empty_subset (ent i)) x
  map_add' x y := by
    funext i
    exact (hr _).map_add x y
  map_smul' a x := by
    funext i
    exact (hr _).map_smul a x

theorem exP_flat : ∀ {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Module.Flat B A] {ι : Type}
    [DecidableEq ι] [Fintype ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, Module B (M S)]
    [∀ S, AddCommGroup (N S)] [∀ S, Module A (N S)] [∀ S, Module B (N S)] [∀ S, IsScalarTower B A (N S)]
    (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap B (r h)) →
    ∀ (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T), (∀ {S T : Finset ι} (h : S ⊆ T), IsLinearMap A (r' h)) →
    ∀ (ψ : ∀ S, M S →ₗ[B] N S), (∀ S, IsBaseChange A (ψ S)) →
    (∀ {S T : Finset ι} (h : S ⊆ T) x, r' h (ψ S x) = ψ T (r h x)) → ExP M r → ExP N r' := by
  intro B A _ _ _ _ ι _ _ M N _ _ _ _ _ _ r hr r' hr' ψ hψ hn hM
  let Ψ : ∀ m : ℕ, (∀ i : Fin (m + 1) → ι, M (ent i)) →ₗ[B] ∀ i : Fin (m + 1) → ι, N (ent i) :=
    fun m => .pi fun i => ψ (ent i) ∘ₗ .proj i
  have hΨ : ∀ m, IsBaseChange A (Ψ m) := fun m => IsBaseChange.pi _ fun i => hψ _
  have hd : ∀ m c, dZL A N r' hr' m (Ψ m c) = Ψ (m + 1) (dZL B M r hr m c) := by
    intro m c
    funext i
    change ∑ k : Fin (m + 2), _ = ψ _ (∑ k : Fin (m + 2), _)
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    congr 1
    exact hn _ _
  have ha : ∀ x, augL A N r' hr' (ψ ∅ x) = Ψ 0 (augL B M r hr x) := by
    intro x
    funext i
    exact hn _ _
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact inj_core (hψ ∅) (hΨ 0) (augL B M r hr) (augL A N r' hr') ha
      (fun y hy => h1 y fun i => congrFun hy i) x (funext hx)
  · intro c hc
    obtain ⟨x, hx⟩ := exact_core (hψ ∅) (hΨ 0) (hΨ 1) (augL B M r hr) (dZL B M r hr 0)
      (augL A N r' hr') (dZL A N r' hr' 0) ha (hd 0)
      (fun y hy => by
        obtain ⟨x, hx⟩ := h2 y hy
        exact ⟨x, funext hx⟩) c hc
    exact ⟨x, fun i => congrFun hx i⟩
  · intro m c hc
    exact exact_core (hΨ m) (hΨ (m + 1)) (hΨ (m + 2)) (dZL B M r hr m) (dZL B M r hr (m + 1))
      (dZL A N r' hr' m) (dZL A N r' hr' (m + 1)) (hd m) (hd (m + 1)) (h3 m) c hc

end Cech
end GlobalTheory.CompanionTheory.SurjectionOntoH4.ExFlat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCohomologyLocalizationExact
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.LocalPerfect

section General

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]
  {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ) (χ' : D →* Rˣ)

theorem twDual_comp_apply (h : χ.comp φ = χ') (g : D) (y : TDual R M) :
    ((twDual χ ρ).comp φ) g y = ((twDual χ' (ρ.comp φ)).comp (MonoidHom.id D)) g y := by
  subst h
  ext m
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply, map_inv]

def dualMap (h : χ.comp φ = χ') :
    H1 ((twDual χ ρ).comp φ) →ₗ[R] H1 ((twDual χ' (ρ.comp φ)).comp (MonoidHom.id D)) :=
  mapH1 _ _ LinearMap.id continuous_id (twDual_comp_apply χ ρ φ χ' h)

def coefMap : H1 (ρ.comp φ) →ₗ[R] H1 ((ρ.comp φ).comp (MonoidHom.id D)) :=
  mapH1 _ _ LinearMap.id continuous_id (fun _ _ => rfl)

theorem dualMap_bijective (h : χ.comp φ = χ') : Function.Bijective (dualMap χ ρ φ χ' h) := by
  refine Function.bijective_iff_has_inverse.2 ⟨mapH1 _ _ LinearMap.id continuous_id
    (fun g y => (twDual_comp_apply χ ρ φ χ' h g y).symm), fun x => ?_, fun x => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl

theorem coefMap_bijective : Function.Bijective (coefMap ρ φ) := by
  refine Function.bijective_iff_has_inverse.2 ⟨mapH1 ((ρ.comp φ).comp (MonoidHom.id D)) (ρ.comp φ)
    LinearMap.id continuous_id (fun _ _ => rfl), fun x => ?_, fun x => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl

theorem mapH2_cup_product_naturality (h : χ.comp φ = χ') (hc : ContAction (ρ.comp φ))
    (hc' : ContAction ((ρ.comp φ).comp (MonoidHom.id D)))
    (hq : ∀ (g : D) (m : R), ((charRep χ).comp φ) g m = charRep χ' g m)
    (y : H1 ((twDual χ ρ).comp φ)) (x : H1 (ρ.comp φ)) :
    mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y x) =
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y) (coefMap ρ φ x) := by
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

theorem injective_compr₂ (h : χ.comp φ = χ') (hc : ContAction (ρ.comp φ))
    (hc' : ContAction ((ρ.comp φ).comp (MonoidHom.id D)))
    (hq : ∀ (g : D) (m : R), ((charRep χ).comp φ) g m = charRep χ' g m)
    {P : H2 (charRep χ') →ₗ[R] R} (hP : Function.Injective P)
    (hL : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc'))
    (hF : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc').flip) :
    Function.Injective ((cupH1H1TwistedDual χ ρ φ hc).compr₂
        (P.comp (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq))) ∧
      Function.Injective ((cupH1H1TwistedDual χ ρ φ hc).compr₂
        (P.comp (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq))).flip := by
  have key : ∀ y x y' x', P (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y x)) =
      P (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y' x')) →
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y) (coefMap ρ φ x) =
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y') (coefMap ρ φ x') := by
    intro y x y' x' e
    have := hP e
    rwa [mapH2_cup_product_naturality χ ρ φ χ' h hc hc' hq, mapH2_cup_product_naturality χ ρ φ χ' h hc hc' hq] at this
  refine ⟨fun y y' e => (dualMap_bijective χ ρ φ χ' h).1 (hL (LinearMap.ext fun x => ?_)),
    fun x x' e => (coefMap_bijective ρ φ).1 (hF (LinearMap.ext fun y => ?_))⟩
  · obtain ⟨x, rfl⟩ := (coefMap_bijective ρ φ).2 x
    exact key y x y' x (LinearMap.congr_fun e x)
  · obtain ⟨y, rfl⟩ := (dualMap_bijective χ ρ φ χ' h).2 y
    exact key y x y x' (LinearMap.congr_fun e y)

end General

theorem locPerfect (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ) (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (hT : LocalTateDuality)
    (hr : 0 < r) (inv : InvFam F Ω l r)
    (hinv : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A))
    (hA : ∀ v : S, IsPlaceOver (Av v) v.1) (v : S) :
    Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v)
        (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)) ∧
      Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v)
        (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)).flip := by
  have hc := hρ.comp' (continuous_locFam S Av v)
  have hχ : μ.comp (locFam S Av v) = (cycMod F Ω l r).comp (Dec (F := F) (Av v)).subtype :=
    MonoidHom.ext fun g => DFunLike.congr_fun hμ (g : G F Ω)
  obtain ⟨-, -, h1, h2, -⟩ := hT F Ω l r M (Av v) (ρ.comp (locFam S Av v)) v.1 hr (hA v) hc
  exact injective_compr₂ μ ρ (locFam S Av v) _ hχ _ (hc.comp' continuous_id)
    (locFam_apply_eq S Av μ hμ v) (hinv _ _ (hA v)).1 h1.1 h2.1

end GlobalTheory.CompanionTheory.LocalPerfect

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIff
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Thick

theorem inU_iInf_finset : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (T : Thick (nlFun γ p X q κ)), InU (⨅ α ∈ S, U α) T ↔ ∀ α ∈ S, InU (U α) T := by
  intro O _ R _ I γ p X q κ ι U S T
  classical
  have htop : InU (⊤ : X.Opens) T := fun x _ => trivial
  have hinf : ∀ V W : X.Opens, InU (V ⊓ W) T ↔ InU V T ∧ InU W T := by
    intro V W
    constructor
    · intro h
      exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩
    · intro h x hx
      exact ⟨h.1 hx, h.2 hx⟩
  induction S using Finset.induction_on with
  | empty => simpa using htop
  | insert a s ha ih =>
    rw [Finset.iInf_insert]
    refine (hinf _ _).trans ?_
    constructor
    · rintro ⟨h1, h2⟩ α hα
      rcases Finset.mem_insert.1 hα with rfl | hα
      · exact h1
      · exact ih.1 h2 α hα
    · intro h
      exact ⟨h a (Finset.mem_insert_self a s), ih.2 fun α hα => h α (Finset.mem_insert_of_mem hα)⟩

end GlobalTheory.CompanionTheory.Thick
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarMeasureSingletonStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_haar_measure_singleton : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {0} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero | exact GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.isStdV_measure_singleton_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirrorPartitionsStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirror_partitions : ReciprocityTheory.Ty.Fin.St.MirrorsOf := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Mirrors.main | exact GlobalTheory.CompanionTheory.TyFin.Mirrors.main | (intros; apply GlobalTheory.CompanionTheory.TyFin.Mirrors.main <;> assumption)
end

