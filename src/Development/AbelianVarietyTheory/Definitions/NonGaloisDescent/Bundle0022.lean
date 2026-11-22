import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRegularOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.BCen

section Abstract

variable {M V W ι : Type} [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def shift (V : Type) [AddCommGroup V] [Module ℂ V] (μ : ι → ℤ) : Module.End ℂ ((ι → ℤ) →₀ V) :=
  Finsupp.lmapDomain V ℂ fun l => l + μ

def univ (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) : Representation ℂ M ((ι → ℤ) →₀ V) where
  toFun g := shift V (deg g).toAdd ∘ₗ Finsupp.mapRange.linearMap (ρ g)
  map_one' := by ext l v; simp [shift]
  map_mul' g h := by ext l v; simp [shift, add_assoc, add_comm (deg g).toAdd]

def lau (V : Type) [AddCommGroup V] [Module ℂ V] (c : (ι → ℤ) →₀ ℂ) : Module.End ℂ ((ι → ℤ) →₀ V) :=
  c.sum fun μ w => w • shift V μ

theorem shift_univ (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) (μ : ι → ℤ) (g : M) :
    shift V μ ∘ₗ univ deg ρ g = univ deg ρ g ∘ₗ shift V μ := by
  ext l v; simp [shift, univ, add_right_comm]

def lauHom (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) (c : (ι → ℤ) →₀ ℂ) :
    (univ deg ρ).IntertwiningMap (univ deg ρ) where
  toLinearMap := lau V c
  isIntertwining' g := by
    refine LinearMap.ext fun y => ?_
    simp only [lau, Finsupp.sum, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    exact Finset.sum_congr rfl fun μ _ => congrArg _ (LinearMap.congr_fun (shift_univ deg ρ μ g) y)

def evalLau [Fintype ι] (c : (ι → ℤ) →₀ ℂ) (u : ι → ℂˣ) : ℂ := c.sum fun μ w => w * ((∏ a, u a ^ μ a : ℂˣ) : ℂ)

def unr [Fintype ι] (deg : M →* Multiplicative (ι → ℤ)) (u : ι → ℂˣ) : M →* ℂˣ where
  toFun g := ∏ a, u a ^ (deg g).toAdd a
  map_one' := by simp
  map_mul' g h := by simp [zpow_add, Finset.prod_mul_distrib]

def part (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) (τ : Representation ℂ M W) : Submodule ℂ W :=
  ⨆ φ : (univ deg ρ).IntertwiningMap τ, LinearMap.range φ.toLinearMap

def copart (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) (τ : Representation ℂ M W) : Submodule ℂ W :=
  ⨅ (ψ : W →ₗ[ℂ] V) (_ : ∀ g, deg g = 1 → ψ ∘ₗ τ g = ρ g ∘ₗ ψ), LinearMap.ker ψ

variable [TopologicalSpace M] [IsTopologicalGroup M]

def IsLocProf (M : Type) [Group M] [TopologicalSpace M] : Prop :=
  ∀ U ∈ nhds (1 : M), ∃ K : Subgroup M, IsOpen (K : Set M) ∧ IsCompact (K : Set M) ∧ (K : Set M) ⊆ U

def IsCompactRep (ρ : Representation ℂ M V) : Prop :=
  IsSmooth ρ ∧ ∀ (v : V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual → ∃ C : Set M, IsCompact C ∧ ∀ g, l (ρ g v) ≠ 0 → g ∈ C

structure CuspDatum (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) : Prop where
  prof : IsLocProf M
  surj : Function.Surjective deg
  isOpen : IsOpen (deg.ker : Set M)
  index : (Subgroup.center M ⊔ deg.ker).FiniteIndex
  irr : ρ.IsIrreducible
  adm : IsAdmissible ρ
  central : ∀ z ∈ Subgroup.center M, ∃ c : ℂ, ∀ v, ρ z v = c • v
  cpt : IsCompactRep (ρ.comp deg.ker.subtype : Representation ℂ deg.ker V)

variable (M) in

structure Centre : Type 1 where

  act : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ M V), IsSmooth π → π.IntertwiningMap π
  nat : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ M V) (hπ : IsSmooth π)
    (τ : Representation ℂ M W) (hτ : IsSmooth τ) (f : π.IntertwiningMap τ) (v : V), f (act π hπ v) = act τ hτ (f v)

def Centre.one : Centre M where
  act π _ := .id π
  nat _ _ _ _ _ _ := rfl

def IsBlockOp (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) (c : (ι → ℤ) →₀ ℂ) (z : Centre M) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ M W) (hτ : IsSmooth τ),
    (∀ (φ : (univ deg ρ).IntertwiningMap τ) y, z.act τ hτ (φ y) = φ (lau V c y)) ∧ ∀ w ∈ copart deg ρ τ, z.act τ hτ w = 0

def IsInvariant [Fintype ι] (deg : M →* Multiplicative (ι → ℤ)) (ρ : Representation ℂ M V) (c : (ι → ℤ) →₀ ℂ) : Prop :=
  ∀ u u', Nonempty ((twist ρ (unr deg u)).Equiv (twist ρ (unr deg u'))) → evalLau c u = evalLau c u'

end Abstract

section Linear

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def degL (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] : Levi k m →* Multiplicative (α → ℤ) where
  toFun g := Multiplicative.ofAdd fun a => ord k (Matrix.GeneralLinearGroup.det (g a))
  map_one' := by ext a; simp [ord_eq_zero]
  map_mul' g h := by ext a; simp [ord_mul]

def permLevi (w : α ≃ β) (f : ∀ a, m' (w a) ≃ m a) : Levi k m' →* Levi k m :=
  MonoidHom.pi fun a => (Units.map (Matrix.reindexAlgEquiv k k (f a)).toMonoidHom).comp (Pi.evalMonoidHom (fun j => GL (m' j) k) (w a))

variable {k}

def IsCuspLevi (ρ : Representation ℂ (Levi k m) W) : Prop :=
  IsSmooth ρ ∧ ∀ (s : ℕ) (c : α → Fin s → ℕ) (f : ∀ i, (Σ j, Fin (c i j)) ≃ m i), relUnip k f ≠ ⊥ →
    Subsingleton (Jacquet ρ (relUnip k f))

def cellMap [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β] {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) {ρ : Representation ℂ (Levi k m) V}
    {σ : Representation ℂ (Levi k m) W} (b : ρ.IntertwiningMap σ) : (cellFunctor f g ρ).IntertwiningMap (cellFunctor f g σ) :=
  smIndMap (compMap (twistMap (compMap (twistMap (jacquetMap b _ _ _) _) _) _) _)

abbrev LeviOf {t : ℕ} (x : Fin t → IrrGL k) : Type := Levi k fun a => Fin (x a).1

abbrev tens {t : ℕ} (x : Fin t → IrrGL k) := piTensor fun a => (x a).rep

abbrev degOf {t : ℕ} (x : Fin t → IrrGL k) : LeviOf x →* Multiplicative (Fin t → ℤ) := degL k fun a => Fin (x a).1

def twFam {t : ℕ} (x : Fin t → IrrGL k) (u : Fin t → ℂˣ) (a : Fin t) : IrrGL k :=
  (x a).tw (unrChar k (u a)) (isSmoothChar_of_isUnram (isUnram_unrChar k (u a)))

def Reps (Z : Multiset (IrrGL k) → ℂ) {t : ℕ} (x : Fin t → IrrGL k) (c : (Fin t → ℤ) →₀ ℂ) : Prop :=
  ∀ u, Z (Finset.univ.val.map (twFam x u)) = evalLau c u

variable (k) in

def IsRegular (n : ℕ) (Z : Multiset (IrrGL k) → ℂ) : Prop :=
  ∀ (t : ℕ) (x : Fin t → IrrGL k), (∀ a, (x a).IsCusp) → ∑ a, (x a).1 = n → ∃ c, Reps Z x c

theorem isRegular_one (n : ℕ) : IsRegular k n fun _ => 1 := fun _ _ _ _ =>
  ⟨Finsupp.single 0 1, fun u => by simp [evalLau]⟩

end Linear

def CentreOp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (Z : Multiset (IrrGL k) → ℂ),
    IsRegular k n Z → ∀ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) → IsCompact (K : Set (GL (Fin n) k)) →
    ∃ f : GL (Fin n) k →₀ ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
      (s : Multiset (IrrGL k)), HasSupport π s → ∀ v ∈ fixed π K, GlobalTheory.Cong.opOf π f v = Z s • v

end GlobalTheory.BCen

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (Embeds isIrreducible_of_equiv mem_fixed)

namespace GlobalTheory.LocGL.Tests

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem nonempty_equiv_parInd_zero {d : Fin 0 → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin 0)
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) V) (L : ℂ ≃ₗ[ℂ] V) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (parInd e ρ)) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp e ρ :=
    { toFun := fun c => ⟨⟨fun _ => L c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_add L a b))
      map_smul' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_smul L a b)) }
  refine ⟨equivOfBijective ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ ⟨fun a b h => ?_, fun φ => ?_⟩⟩
  · have h1 : L a = L b := congrArg (fun φ : IndSp e ρ => φ.1.1 1) h
    exact L.injective h1
  · refine ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    rw [hg g]
    exact L.apply_symm_apply _

theorem nonempty_equiv_prodIrr_zero (x : Fin 0 → IrrGL k) (hd : ∑ a, (x a).1 = 0) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prodIrr x hd)) :=
  nonempty_equiv_parInd_zero _ _ (PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a => (x a).2.rep.V)).symm

theorem empty_spec : IsZ (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ∧
    IsL (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_zero (k := k) Fin.elim0 rfl
  have ho : IsOrderedForm (k := k) (Fin.elim0 : Fin 0 → Segment k) 0 := ⟨rfl, fun i => i.elim0⟩
  exact ⟨⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isSocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩,
    ⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isCosocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩⟩

theorem IsL_deg {N : ℕ} {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) :
    (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, rfl, ⟨Δ, ⟨rfl, -⟩, hΔ⟩, -⟩ := h
  rw [Multiset.map_map]
  exact Finset.sum_congr rfl fun i _ => (hΔ i).deg_eq

theorem eq_of_isZSeg_single {ρ x : IrrGL k} (hρ : ρ.IsCusp) (h : IsZSeg (.single ρ hρ) x.rep) : x = ρ := by
  obtain ⟨n, c⟩ := x
  obtain ⟨d, c'⟩ := ρ
  obtain rfl : d = n := (one_mul d).symm.trans h.deg_eq
  exact congrArg _ (irrCl_eq_iff.2 ((single_spec hρ).1.unique h))

theorem eq_of_embeds {e : (Σ _ : Fin 2, Fin 1) ≃ Fin 2} {χ : Fin 2 → kˣ →* ℂˣ} {ψ : kˣ →* ℂˣ}
    (h : Embeds (detRep (Fin 2) ψ) (multiProd e fun a => detRep (Fin 1) (χ a))) : χ 1 = χ 0 * absPow k 1 := by
  obtain ⟨f, hf⟩ := h
  have h1 : ∀ g : GL (Fin 2) k, (f 1).1.1 g = (ψ (GeneralLinearGroup.det g) : ℂ) • (f 1).1.1 1 := fun g => by
    have := congrArg (fun φ => φ.1.1 1) (f.isIntertwining _ _ g 1)
    have h2 : detRep (Fin 2) ψ g 1 = (ψ (GeneralLinearGroup.det g) : ℂ) • (1 : ℂ) := ofChar_apply _ _ _
    simp only [h2, map_smul] at this
    rw [← one_mul g]
    exact this.symm.trans (by rw [one_mul]; rfl)
  have h0 : (f 1).1.1 1 ≠ 0 := fun h0 => one_ne_zero (hf (by
    rw [map_zero]
    exact Subtype.ext (Subtype.ext (funext fun g => by rw [h1, h0, smul_zero]; rfl))))
  have key : ∀ (g : Levi k fun _ : Fin 2 => Fin 1) y, piTensor (fun a => detRep (Fin 1) (χ a)) g y =
      ((∏ a, χ a (GeneralLinearGroup.det (g a)) : ℂˣ) : ℂ) • y := by
    intro g y
    induction y using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | smul_tprod c x =>
      rw [map_smul, smul_comm, piTensor_tprod, Units.coe_prod, ← MultilinearMap.map_smul_univ]
      congr 2
  have law : ∀ g : Levi k fun _ : Fin 2 => Fin 1, ψ (∏ a, GeneralLinearGroup.det (g a)) =
      deltaHalf k _ g * ∏ a, χ a (GeneralLinearGroup.det (g a)) := fun g => by
    have := parInd_law e _ (f 1) ⟨_, leviEmb_mem_parab k e g⟩ 1
    rw [mul_one, leviProj_leviEmb, key, h1, smul_smul, det_leviEmb] at this
    exact Units.ext (smul_left_injective ℂ h0 this)
  refine MonoidHom.ext fun z => ?_
  have hz : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [GeneralLinearGroup.scalar]
  have a := law ![GeneralLinearGroup.scalar (Fin 1) z, 1]
  have b := law ![1, GeneralLinearGroup.scalar (Fin 1) z]
  rw [deltaHalf_apply] at a b
  simp only [Fin.prod_univ_two, modExp_fin (fun _ : Fin 2 => Fin 1) (fun _ => by simp), Matrix.cons_val_zero,
    Matrix.cons_val_one, hz, map_one, mul_one, one_mul] at a b
  have c : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by rw [← absPow_add]; norm_num
  have d : absPow k (-1 / 2) = (absPow k (1 / 2))⁻¹ := by rw [← absPow_neg, neg_div]
  norm_num at a b
  rw [← neg_div, d, a] at b
  rw [c, MonoidHom.mul_apply, MonoidHom.mul_apply]
  rw [MonoidHom.inv_apply, eq_inv_mul_iff_mul_eq] at b
  rw [← b, mul_comm ((χ 0) z), mul_assoc]

theorem eq_of_embeds_prodIrr {c : Fin 2 → kˣ →* ℂˣ} {ψ : kˣ →* ℂˣ} (hc : ∀ a, IsSmoothChar (c a)) {x : Fin 2 → IrrGL k}
    (hx : x = fun a => IrrGL.ofChar (c a) (hc a)) {hd : ∑ a, (x a).1 = 2}
    (h : Embeds (detRep (Fin 2) ψ) (prodIrr x hd)) : c 1 = c 0 * absPow k 1 := by
  subst hx
  let φ := multiProdEquiv (stdBlocks (fun _ : Fin 2 => 1) hd) fun a => equivRep (IrrRep.det (Fin 1) (c a) (hc a))
  exact eq_of_embeds (h.trans (.of_equiv φ.symm))

theorem not_isZ_pair {χ ψ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    ¬ IsZ {.single _ (IrrGL.isCusp_ofChar χ hχ), .single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)} (detRep (Fin 2) ψ) := by
  rintro ⟨h, x, hd, ⟨Δ, ⟨hm, ho⟩, hΔ⟩, hs⟩
  obtain rfl : h = 2 := by simpa using congrArg Multiset.card hm
  have hm' : ({Δ 0, Δ 1} : Multiset (Segment k)) = _ := hm
  have hp := single_precedes χ hχ
  have h01 : Δ 0 = .single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1) ∧ Δ 1 = .single _ (IrrGL.isCusp_ofChar χ hχ) := by
    rcases Multiset.cons_eq_cons.1 hm' with ⟨a, b⟩ | ⟨-, s, a, b⟩
    · exact absurd hp.1 (by rw [← a, ← Multiset.singleton_inj.1 b]; exact ho 0 1 (by decide))
    · obtain rfl : s = 0 := by simpa using congrArg Multiset.card a
      exact ⟨(Multiset.singleton_inj.1 b).symm, Multiset.singleton_inj.1 a⟩
  let c : Fin 2 → kˣ →* ℂˣ := ![χ * absPow k 1, χ]
  have hc : ∀ a, IsSmoothChar (c a) := Fin.forall_fin_two.2 ⟨hχ.mul (isSmoothChar_absPow 1), hχ⟩
  have hx : x = fun a => IrrGL.ofChar (c a) (hc a) := by
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · exact (eq_of_isZSeg_single _ (h01.1 ▸ hΔ 0)).trans (IrrGL.tw_ofChar _ _ _ _)
    · exact eq_of_isZSeg_single _ (h01.2 ▸ hΔ 1)
  have := eq_of_embeds_prodIrr hc hx hs.embeds
  have h2 : χ = χ * absPow k 1 * absPow k 1 := this
  rw [mul_assoc, ← absPow_add, left_eq_mul] at h2
  have h3 : (2 : ℝ) = 0 := (absPow_ofReal_eq_one (k := k)).1 (by rw [← h2]; norm_num)
  norm_num at h3

theorem not_isGeneric_detRep (χ : kˣ →* ℂˣ) : ¬ IsGeneric (detRep (Fin 2) χ) := by
  rintro ⟨ψ, -, hψ, h⟩
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra! h; exact hψ (AddChar.ext _ _ h)
  let u : GL (Fin 2) k := GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by simp)
  have hu : u ∈ unipB k (Fin 2) := (mem_unipB k).2 ⟨fun i j hij => by
    show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) k) i j = 0
    fin_cases i <;> fin_cases j <;> simp at hij ⊢, fun i => by
    show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) k) i i = 1
    fin_cases i <;> simp⟩
  have hw : (whitChar ψ 2 ⟨u, hu⟩ : ℂ) = ψ t := by
    show ((ψ (∑ p : Fin 2 × Fin 2 with (p.2 : ℕ) = p.1 + 1, (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) k) p.1 p.2) : Circle) : ℂ) = _
    simp [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hdet : GeneralLinearGroup.det u = 1 := by ext; simp [u]
  refine Submodule.Quotient.nontrivial_iff.1 h (eq_top_iff.2 fun v _ => ?_)
  have hne : (1 : ℂ) - ψ t ≠ 0 := sub_ne_zero.2 fun e => ht (Circle.ext e.symm)
  refine Submodule.subset_span ⟨⟨u, hu⟩, v / (1 - ψ t), ?_⟩
  rw [hw]
  show v = ofChar _ u _ - _
  rw [ofChar_apply, detChar_apply, hdet, map_one]
  simp only [Units.val_one, smul_eq_mul]
  field_simp

theorem linked_tests (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (Segment.icc _ (IrrGL.isCusp_ofChar χ hχ) 0 1 (by decide)).Precedes (.icc _ (IrrGL.isCusp_ofChar χ hχ) 1 2 (by decide)) ∧
    ¬ (Segment.icc _ (IrrGL.isCusp_ofChar χ hχ) 0 2 (by decide)).Linked (.icc _ (IrrGL.isCusp_ofChar χ hχ) 1 1 (by decide)) := by
  have inj : ∀ a b : ℤ, (IrrGL.ofChar χ hχ).nu a = (IrrGL.ofChar χ hχ).nu b → a = b := fun a b h => by
    exact_mod_cast (IrrGL.nu_ofChar_inj χ hχ (s := a) (t := b)).1 (by simpa using h)
  refine ⟨⟨⟨⟨.icc _ (IrrGL.isCusp_ofChar χ hχ) 0 2 (by decide), ?_⟩, fun h => ?_, fun h => ?_⟩, 1, one_pos, ?_⟩,
    fun h => h.2.2 fun x hx => ?_⟩
  · ext x
    simp only [Set.mem_union, Segment.mem_icc]
    constructor
    · rintro ⟨a, h1, h2, rfl⟩
      rcases le_or_gt a 1 with h | h
      exacts [Or.inl ⟨a, h1, h, rfl⟩, Or.inr ⟨a, h.le, h2, rfl⟩]
    · rintro (⟨a, h1, h2, rfl⟩ | ⟨a, h1, h2, rfl⟩) <;> exact ⟨a, by omega, by omega, rfl⟩
  · obtain ⟨a, h1, -, h2⟩ := Segment.mem_icc.1 (h (Segment.mem_icc.2 ⟨0, by decide, by decide, rfl⟩))
    have := inj _ _ h2; omega
  · obtain ⟨a, -, h1, h2⟩ := Segment.mem_icc.1 (h (Segment.mem_icc.2 ⟨2, by decide, by decide, rfl⟩))
    have := inj _ _ h2; omega
  · simp [Segment.icc]
  · obtain ⟨a, h1, h2, rfl⟩ := Segment.mem_icc.1 hx
    exact Segment.mem_icc.2 ⟨a, by omega, by omega, rfl⟩

end GlobalTheory.LocGL.Tests
end
end

