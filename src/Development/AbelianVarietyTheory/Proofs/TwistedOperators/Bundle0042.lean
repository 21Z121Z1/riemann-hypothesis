import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.InertSupp

section Blocks

variable {n : Type} [Fintype n] [DecidableEq n]

open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
omit [DecidableEq n] in

theorem _root_.GlobalTheory.InertSupp.exists_blocks (c : n → ℤ) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n),
    ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j := by
  classical
  let S : Finset ℤ := Finset.univ.image c
  let o := S.orderIsoOfFin rfl
  let φ : n → Fin S.card := fun i => o.symm ⟨c i, Finset.mem_image_of_mem c (Finset.mem_univ i)⟩
  refine ⟨S.card, fun a => Fintype.card {i // φ i = a},
    (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ), ?_⟩
  intro i j
  have key : ∀ x, (((Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ)).symm x).1 = φ x := fun x => rfl
  unfold _root_.GlobalTheory.SmGL.blk
  rw [key, key]
  simp only [φ, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

variable (R : Type) [CommRing R]

def unipOf (c : n → ℤ) : Subgroup (GL n R) :=
  (unipRad R (exists_blocks c).choose_spec.choose_spec.choose).copy
    {g | ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j} (by
      ext g
      simp only [SetLike.mem_coe, CuspMax.mem_unipRad_iff_entries,
        (exists_blocks c).choose_spec.choose_spec.choose_spec, Set.mem_setOf_eq])

variable {R}

open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable (R : Type) [CommRing R] in
variable {R} in

theorem _root_.GlobalTheory.InertSupp.mem_unipOf {c : n → ℤ} {g : GL n R} :
    g ∈ _root_.GlobalTheory.InertSupp.unipOf R c ↔
      ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j :=
  Iff.rfl

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable (R : Type) [CommRing R] in
variable {R} in
variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] in
variable (R) in

theorem _root_.GlobalTheory.InertSupp.unipRad_eq_unipOf {e : (Σ a, m a) ≃ n}
    {c : n → ℤ} (h : ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j) :
    _root_.GlobalTheory.SmGL.unipRad R e = _root_.GlobalTheory.InertSupp.unipOf R c := by
  ext g
  rw [_root_.GlobalTheory.InertSupp.mem_unipOf, _root_.GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries]
  simp only [h]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

def NoInert (π : Representation ℂ (GL n k) V) (θ : kˣ →* ℂˣ) : Prop :=
  ∀ (c : n → ℤ) (i : n), (∀ j, c j = c i → j = i) → ∀ v : V,
    (∀ u : kˣ, valuation k (u : k) = 1 →
      π (diagT k n (Pi.mulSingle i u)) v - (θ u : ℂ) • v ∈ twKer π (unipOf k c) 1) →
    v ∈ twKer π (unipOf k c) 1

def cut (I : Finset n) : n → ℤ := fun i => if i ∈ I then 0 else 1

variable [MeasurableSpace k] [BorelSpace k]

def zetaIntegrand (Φ : Matrix n n k → ℂ) (c : GL n k → ℂ) (s : ℂ) (g : GL n k) : ℂ :=
  Φ g.val * c g * (absPow k (s + ((Fintype.card n : ℂ) - 1) / 2) (GeneralLinearGroup.det g) : ℂ)

def IsLaurent (ν : Measure k) (c : GL n k → ℂ) : Prop :=
  ∀ Φ ∈ SB (Matrix n n k), ∃ (b : ℝ) (N : ℕ) (Q : Polynomial ℂ), ∀ s : ℂ, b < s.re →
    Integrable (zetaIntegrand Φ c s) (volGL ν n) ∧
    (∫ g, zetaIntegrand Φ c s g ∂(volGL ν n)) * ((resCard k : ℂ) ^ (-s)) ^ N =
      Q.eval ((resCard k : ℂ) ^ (-s))

end Local

end GlobalTheory.InertSupp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyConstantExtensionByZero
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

noncomputable section
namespace GlobalTheory.SBExtend

variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]

open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in

theorem _root_.GlobalTheory.SBExtend.exists_isCompact_isClopen_between {K W : Set X} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) : ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ K ⊆ V ∧ V ⊆ W := by
  have hB := loc_compact_Haus_tot_disc_of_zero_dim (H := X)
  have h : ∀ x ∈ K, ∃ U : Set X, (IsClopen U ∧ IsCompact U) ∧ x ∈ U ∧ U ⊆ W := by
    intro x hx
    obtain ⟨C, hCx, hCW, hC⟩ := local_compact_nhds (hW.mem_nhds (hKW hx))
    obtain ⟨U, hU, hxU, hUC⟩ :=
      hB.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.2 hCx) isOpen_interior
    exact ⟨U, ⟨hU, hC.of_isClosed_subset hU.isClosed (hUC.trans interior_subset)⟩, hxU,
      (hUC.trans interior_subset).trans hCW⟩
  choose U hU hxU hUW using h
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U fun x hx => (hU x hx).1.isOpen.mem_nhds (hxU x hx)
  exact ⟨⋃ x ∈ t, U x x.2, t.isCompact_biUnion fun x _ => (hU x x.2).2,
    isClopen_biUnion_finset fun x _ => (hU x x.2).1, ht, Set.iUnion₂_subset fun x _ => hUW x x.2⟩

open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in

theorem _root_.GlobalTheory.SBExtend.indicator_mem_SB {V : Set X} (hc : IsCompact V)
    (hV : IsClopen V) : (V.indicator fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.SplitWeil.SB X := by
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨fun s => ?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rcases Set.indicator_const_preimage V s (1 : ℂ) with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hV.isOpen, hV.compl.isOpen, isOpen_empty]

theorem exists_extension : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] (U Z : Set X), IsOpen U → Z ⊆ U → ∀ f : SB Z, ∃ F : SB X, (∀ z : Z, F.1 z = f.1 z) ∧ ∀ x, x ∉ U → F.1 x = 0 := by
  classical
  intro X _ _ _ _ U Z hU hZU f
  obtain ⟨f, hl, hs⟩ := f
  have hfin : (f '' tsupport f).Finite := by
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hs
    have := (hl.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport f)))).range_finite
    refine this.subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  have h : ∀ c : ℂ, ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ V ⊆ U ∧
      (c ≠ 0 → ∀ z : Z, (z : X) ∈ V ↔ f z = c) := by
    intro c
    by_cases hc : c = 0
    · exact ⟨∅, isCompact_empty, isClopen_empty, Set.empty_subset _, fun h => absurd hc h⟩
    have hcl := hl.isClopen_fiber c
    obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.1 hcl.isOpen
    have hcomp : IsCompact {z : Z | f z = c} :=
      hs.isCompact.of_isClosed_subset hcl.isClosed fun z hz =>
        subset_tsupport _ (by
          rw [Function.mem_support, show f z = c from hz]; exact hc)
    obtain ⟨V, hV1, hV2, hV3, hV4⟩ := exists_isCompact_isClopen_between
      (hcomp.image continuous_subtype_val) (hW.inter hU) (by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨(hWe.symm ▸ hz : z ∈ Subtype.val ⁻¹' W), hZU z.2⟩)
    refine ⟨V, hV1, hV2, fun x hx => (hV4 hx).2, fun _ z => ⟨fun hz => ?_, fun hz => hV3 ⟨z, hz, rfl⟩⟩⟩
    have : z ∈ Subtype.val ⁻¹' W := (hV4 hz).1
    rw [hWe] at this
    exact this
  choose V hV1 hV2 hV3 hV4 using h
  refine ⟨⟨∑ c ∈ hfin.toFinset.erase 0, c • (V c).indicator fun _ => (1 : ℂ),
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (indicator_mem_SB (hV1 c) (hV2 c))⟩,
    fun z => ?_, fun x hx => ?_⟩
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (f z)]
    · by_cases hz : f z = 0
      · simp [hz]
      · rw [Set.indicator_of_mem ((hV4 _ hz z).2 rfl), mul_one]
    · intro c hc hne
      rw [Set.indicator_of_notMem (fun h => hne ((hV4 c (Finset.ne_of_mem_erase hc) z).1 h).symm),
        mul_zero]
    · intro hn
      by_cases hz : f z = 0
      · simp [hz]
      · exact absurd (Finset.mem_erase.2 ⟨hz, hfin.mem_toFinset.2 ⟨z, subset_tsupport _ hz, rfl⟩⟩) hn
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun c _ => by
      rw [Set.indicator_of_notMem (fun h => hx (hV3 c h)), mul_zero]

end GlobalTheory.SBExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.TargetUnip

theorem det_eq_one_of_level {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (f : ι → ℕ)
    (M : Matrix ι ι k) (hM : ∀ r s, f s ≤ f r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have hb : M.BlockTriangular f := by
    intro r s h
    rw [hM r s h.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ h
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock f a = 1 := by
    ext i j
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, hM _ _ (by rw [i.2, j.2])]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type*} [Fintype n'] [DecidableEq n']

theorem mul_apply_of_inN {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) {m : Type*}
    (x : Matrix (n ⊕ Fin c) m k) (r : n ⊕ Fin c) (s : m) :
    (h.val * x) r s = x r s + ∑ r', if lev p r < lev p r' then h.val r r' * x r' s else 0 := by
  have h1 : x r s = ∑ r', (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r r' * x r' s := by
    rw [← Matrix.mul_apply, Matrix.one_mul]
  rw [Matrix.mul_apply, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r' _ => ?_
  split_ifs with hl
  · rw [Matrix.one_apply_ne, zero_mul, zero_add]
    rintro rfl
    exact lt_irrefl _ hl
  · rw [hh r r' (not_lt.1 hl), add_zero]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem affPt_of_not_free (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) {r s} (hrs : ¬ Free p (r, s)) :
    affPt p x₀ e r s = basePt c x₀ r s := by
  simp [affPt, hrs]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem affPt_eq_zero (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) {r r' : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hrs : ¬ Free p (r, s))
    (hl : lev p r < lev p r') : affPt p x₀ e r' s = 0 := by
  rcases r with r | r <;> rcases r' with r' | r' <;> rcases s with s | s <;>
    simp only [lev, Free, Sum.elim_inl, Sum.elim_inr, lt_irrefl] at hrs hl <;>
    rw [affPt_of_not_free _ _ _ (by simp only [Free]; omega)] <;>
    simp [basePt] <;> omega

open Classical in

def linPart (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) :
    Matrix {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
  Matrix.of fun a b => if a.1.2 = b.1.2 then h a.1.1 b.1.1 else 0

open Classical in
theorem det_linPart {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) :
    (linPart (n' := n') p h.val).det = 1 := by
  refine det_eq_one_of_level (fun a => lev p a.1.1) _ fun a b hab => ?_
  simp only [linPart, Matrix.of_apply]
  rw [hh _ _ hab]
  simp only [Matrix.one_apply, Subtype.ext_iff, Prod.ext_iff]
  by_cases h1 : a.1.1 = b.1.1 <;> by_cases h2 : a.1.2 = b.1.2 <;> simp [h1, h2]

open Classical in
theorem linPart_mulVec (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (a : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    (linPart p h).mulVec e a =
      ∑ r', h a.1.1 r' * (if hf : Free p (r', a.1.2) then e ⟨(r', a.1.2), hf⟩ else 0) := by
  let F : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k := fun b =>
    (if a.1.2 = b.2 then h a.1.1 b.1 else 0) * (if hf : Free p b then e ⟨b, hf⟩ else 0)
  have h1 : (linPart p h).mulVec e a = ∑ b : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}, F b.1 := by
    simp only [Matrix.mulVec, dotProduct, linPart, Matrix.of_apply, F]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dif_pos b.2]
  have h2 : ∑ b : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}, F b.1 = ∑ b, F b := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun b => Free p b) (by simp) F]
    refine Finset.sum_filter_of_ne fun b _ hb => ?_
    by_contra hf
    exact hb (by simp [F, hf])
  rw [h1, h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [Finset.sum_eq_single a.1.2]
  · simp [F]
  · intro s _ hs
    simp [F, hs.symm]
  · simp

open Classical in
theorem mul_affPt {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    h.val * affPt p x₀ e = affPt p x₀ ((linPart p h.val).mulVec e +
      fun a => (h.val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2) := by
  ext r s
  by_cases hf : Free p (r, s)
  · have : affPt p x₀ ((linPart p h.val).mulVec e +
      fun a => (h.val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2) r s =
        basePt c x₀ r s + ((linPart p h.val).mulVec e ⟨(r, s), hf⟩ +
          (h.val * basePt c x₀ - basePt c x₀) r s) := by
      simp [affPt, hf]
    rw [this, linPart_mulVec, affPt, Matrix.mul_add, Matrix.add_apply, Matrix.sub_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    ring
  · rw [affPt_of_not_free _ _ _ hf, mul_apply_of_inN hh, affPt_of_not_free _ _ _ hf,
      Finset.sum_eq_zero, add_zero]
    intro r' _
    split_ifs with hl
    · rw [affPt_eq_zero p x₀ e hf hl, mul_zero]
    · rfl

omit [Fintype n'] [DecidableEq n'] in
theorem ch_mul_affPt {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (h.val * affPt p x₀ e) = ch (affPt p x₀ e) + simpleSum h := by
  rw [ch, ch, simpleSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_apply_of_inN hh, Fintype.sum_sum_type, Finset.sum_eq_zero, zero_add]
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hl : lev (n := n) p (Sum.inr i) < lev (n := n) p (Sum.inr j)
    · rw [if_pos hl]
      simp only [lev, Sum.elim_inr] at hl
      rw [affPt_of_not_free _ _ _ (by simp only [Free, Fin.val_succ]; omega)]
      simp [basePt]
    · rw [if_neg hl]
      simp only [lev, Sum.elim_inr] at hl
      rw [if_neg (by omega)]
  · intro r _
    split_ifs with hl
    · simp only [lev, Sum.elim_inr, Sum.elim_inl] at hl
      rw [affPt_of_not_free _ _ _ (by simp only [Free, Fin.val_succ]; omega)]
      simp [basePt]
    · rfl

end GlobalTheory.RootEx.TargetUnip

open GlobalTheory.RootEx.TargetUnip in

theorem GlobalTheory.RootEx.opE_om_target_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), ∀ g ∈ N k n c p, opE ψ ν p (om μ 1 g Φ) = (ψ (-simpleSum g) : ℂ) • opE ψ ν p Φ := by
  classical
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ ν _ μ Φ g hg
  obtain ⟨hN, hadd, hdet, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c p
  have hg' : g⁻¹ ∈ N k n c p := inv_mem hg
  have hh : InN p g⁻¹ := (hN _).1 hg'
  have hs1 : simpleSum (1 : GL (n ⊕ Fin c) k) = 0 := by
    have := hadd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact left_eq_add.1 this
  have hs : simpleSum g⁻¹ = -simpleSum g := by
    have := hadd g hg g⁻¹ hg'
    rw [mul_inv_cancel, hs1] at this
    linear_combination -this
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  have hom : ∀ x, om μ 1 g Φ x = Φ ((g⁻¹).val * x) := by
    intro x
    simp [om, hdet g hg, hn1]
  haveI := secondCountable k
  funext x₀
  let F : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ := fun e =>
    Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)
  let t : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k :=
    fun a => ((g⁻¹).val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2
  let L := Matrix.GeneralLinearGroup.mkOfDetNeZero (linPart (n' := n') p (g⁻¹).val)
    (by rw [det_linPart hh]; exact one_ne_zero)
  have hL : Matrix.GeneralLinearGroup.det L = 1 := by
    ext
    exact det_linPart hh
  have key : ∀ e, om μ 1 g Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) =
      (ψ (-simpleSum g) : ℂ) * F (L.val.mulVec e + t) := by
    intro e
    have h1 := mul_affPt hh x₀ e
    have h2 := ch_mul_affPt hh x₀ e
    have h3 : F (L.val.mulVec e + t) = Φ ((g⁻¹).val * affPt p x₀ e) *
        (ψ (-ch ((g⁻¹).val * affPt p x₀ e)) : ℂ) := by
      rw [h1]; rfl
    rw [h3, h2, hs, hom, mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  have hcov := integral_comp_mulVec_eq_smul ν L
    (fun e => F (e + t))
  rw [hL, hn1, inv_one, one_smul, integral_add_right_eq_self] at hcov
  simp only [opE, Pi.smul_apply, smul_eq_mul, key]
  rw [integral_const_mul, hcov]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorMaximalStableContainsSlotKernelStatement
section
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensor_maximalStable_contains_positionKernel : ∀ {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i))) (i : ι)
    (Rel K : Submodule ℂ (M i)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ (M i), Rel ≤ N → GlobalTheory.TensHead.Stab (Op i) N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab (Op i) K →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)),
      (∀ x ∈ Rel, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N') →
      GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) U → N' ≤ U →
        U = N' ∨ U = ⊤) →
      ∀ x ∈ K, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N' := by
  first | exact @GlobalTheory.TensHead.position_mem_of_maximal_stable | exact GlobalTheory.TensHead.position_mem_of_maximal_stable | (intros; apply GlobalTheory.TensHead.position_mem_of_maximal_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexPerLat
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.PerIndex

variable {k : Type} [Field k] [ValuativeRel k] {n : Type}

theorem col_add (n' : Type) {c : ℕ}
    (e f : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) :
    UnfoldShape.col (n' := n') (e + f) i
      = UnfoldShape.col (n' := n') e i + UnfoldShape.col (n' := n') f i := by
  funext r
  simp only [UnfoldShape.col, Pi.add_apply]
  split_ifs <;> simp

theorem relIndex_perLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type)
    [Fintype n'] [DecidableEq n'] (c : ℕ) (ϖ : 𝒪[k]) (hϖ : (ϖ : k) ≠ 0)
    (L : Submodule 𝒪[k] (n → k)) :
    (perLat ϖ n' c L).relIndex (perLat ϖ n' c (stdLat k n))
      = (L.toAddSubgroup.relIndex (stdLat k n).toAddSubgroup) ^ c := by
  classical
  let φ : perLat ϖ n' c (stdLat k n) →+ (Fin c → (stdLat k n).toAddSubgroup) :=
    AddMonoidHom.mk' (fun e i => ⟨fun r => ((ϖ : k) ^ ((i : ℕ) + 1) •
      UnfoldShape.col (n' := n') e.1 i) (Sum.inl r), (mem_chainLat.1 (mem_perLat.1 e.2 i)).1⟩)
      (by
        intro e f
        funext i
        apply Subtype.ext
        funext r
        simp only [AddSubgroup.coe_add, Pi.add_apply, col_add, smul_add])
  have hφ : Function.Surjective φ := by
    intro v
    have hY : ∀ i : Fin c, ((ϖ : k) ^ ((i : ℕ) + 1))⁻¹ • inX k n c (v i).1
        ∈ Yle k n c ((i : ℕ) + 1) := by
      intro i
      rw [mem_Yle]
      intro l _
      simp [inX_apply]
    have hc := col_uncol (n' := n') hY
    have hs : ∀ i : Fin c, (ϖ : k) ^ ((i : ℕ) + 1) • UnfoldShape.col (n' := n')
        (uncol n' fun i : Fin c => ((ϖ : k) ^ ((i : ℕ) + 1))⁻¹ • inX k n c (v i).1) i
        = inX k n c (v i).1 := by
      intro i
      rw [hc, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hϖ), one_smul]
    refine ⟨⟨uncol n' fun i : Fin c => ((ϖ : k) ^ ((i : ℕ) + 1))⁻¹ • inX k n c (v i).1, ?_⟩, ?_⟩
    · rw [mem_perLat]
      intro i
      rw [hs, mem_chainLat]
      refine ⟨?_, fun l => ⟨0, ?_⟩⟩
      · simpa [inX_apply] using (v i).2
      · simp [inX_apply]
    · funext i
      apply Subtype.ext
      funext r
      exact congrFun (hs i) (Sum.inl r)
  have hcomap : (perLat ϖ n' c L).addSubgroupOf (perLat ϖ n' c (stdLat k n))
      = (AddSubgroup.pi Set.univ fun _ : Fin c =>
          L.toAddSubgroup.addSubgroupOf (stdLat k n).toAddSubgroup).comap φ := by
    ext e
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_pi, mem_perLat]
    constructor
    · intro h i _
      exact (mem_chainLat.1 (h i)).1
    · intro h i
      exact mem_chainLat.2 ⟨h i trivial, (mem_chainLat.1 (mem_perLat.1 e.2 i)).2⟩
  rw [AddSubgroup.relIndex, hcomap, AddSubgroup.index_comap_of_surjective _ hφ,
    AddSubgroup.index_pi]
  simp [AddSubgroup.relIndex]

end GlobalTheory.RootEx.PerIndex
end

