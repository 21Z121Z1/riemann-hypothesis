import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
import CompanionTheory.AutomorphicTheory.ThetaDilations.Nuabs
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0002
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixInductionTransvectionDiagonal

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AnnihilatorOfAnnihilatorLe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CofinalDual

theorem card_le_of_pairing {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
    (b : A → B → ℂ) (hn : ∀ x y, ‖b x y‖ = 1)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (hk : ∀ x, (∀ y, b x y = 1) → x = 0) : Nat.card A ≤ Nat.card B := by
  classical
  haveI := Fintype.ofFinite B
  have hne : ∀ x y, b x y ≠ 0 := fun x y h => by
    have := hn x y
    simp [h] at this
  have h0 : ∀ x, b x 0 = 1 := fun x => by
    have := hr x 0 0
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne x 0)).1 this.symm
  let f : A → AddChar B ℂ := fun x =>
    { toFun := b x, map_zero_eq_one' := h0 x, map_add_eq_mul' := hr x }
  have hf : Function.Injective f := by
    intro x x' h
    have e : ∀ y, b x y = b x' y := fun y => congrArg (fun ψ : AddChar B ℂ => ψ y) h
    have : x - x' = 0 := hk _ fun y => by
      have h1 := hl (x - x') x' y
      rw [sub_add_cancel, e y] at h1
      exact (mul_eq_right₀ (hne x' y)).1 h1.symm
    exact sub_eq_zero.1 this
  have e : Nat.card (AddChar B ℂ) = Nat.card B := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  exact e ▸ Nat.card_le_card_of_injective f hf

theorem index_eq_of_pairing {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (c : X → Y → ℂ)
    (hn : ∀ x y, ‖c x y‖ = 1)
    (hl : ∀ x x' y, c (x + x') y = c x y * c x' y)
    (hr : ∀ x y y', c x (y + y') = c x y * c x y')
    (N : AddSubgroup X) (M : AddSubgroup Y)
    (hN : ∀ x, x ∈ N ↔ ∀ y, c x y = 1) (hM : ∀ y, y ∈ M ↔ ∀ x, c x y = 1)
    [N.FiniteIndex] [M.FiniteIndex] : N.index = M.index := by
  have hx : ∀ (x x' : X) (y : Y), (x : X ⧸ N) = x' → c x y = c x' y := by
    intro x x' y h
    have hm : -x + x' ∈ N := QuotientAddGroup.eq.1 h
    have := hl x (-x + x') y
    rw [add_neg_cancel_left, (hN _).1 hm y, mul_one] at this
    exact this.symm
  have hy : ∀ (x : X) (y y' : Y), (y : Y ⧸ M) = y' → c x y = c x y' := by
    intro x y y' h
    have hm : -y + y' ∈ M := QuotientAddGroup.eq.1 h
    have := hr x y (-y + y')
    rw [add_neg_cancel_left, (hM _).1 hm x, mul_one] at this
    exact this.symm
  let b : X ⧸ N → Y ⧸ M → ℂ := fun p q => c (Quotient.out p) (Quotient.out q)
  have hb : ∀ (x : X) (y : Y), b (x : X ⧸ N) (y : Y ⧸ M) = c x y := fun x y => by
    change c (Quotient.out (x : X ⧸ N)) (Quotient.out (y : Y ⧸ M)) = c x y
    rw [hx _ x _ (QuotientAddGroup.out_eq' _), hy _ _ y (QuotientAddGroup.out_eq' _)]
  have bn : ∀ p q, ‖b p q‖ = 1 := fun p q => hn _ _
  have bl : ∀ p p' q, b (p + p') q = b p q * b p' q := by
    intro p p' q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective p'
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_add, hb, hb, hb, hl]
  have br : ∀ p q q', b p (q + q') = b p q * b p q' := by
    intro p q q'
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective q'
    rw [← QuotientAddGroup.mk_add, hb, hb, hb, hr]
  have k1 : ∀ p, (∀ q, b p q = 1) → p = 0 := by
    intro p h
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    exact (QuotientAddGroup.eq_zero_iff x).2 ((hN x).2 fun y => by rw [← hb, h])
  have k2 : ∀ q, (∀ p, b p q = 1) → q = 0 := by
    intro q h
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (QuotientAddGroup.eq_zero_iff y).2 ((hM y).2 fun x => by rw [← hb, h])
  exact le_antisymm (card_le_of_pairing b bn bl br k1)
    (card_le_of_pairing (fun q p => b p q) (fun q p => bn p q) (fun q q' p => br p q q')
      (fun q p p' => bl p p' q) k2)

theorem relIndex_ne_zero_of_isOpen {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (S T : AddSubgroup V) (hS : IsOpen (S : Set V))
    (hT : IsCompact (T : Set V)) : S.relIndex T ≠ 0 := by
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have ho : IsOpen ((S.addSubgroupOf T : AddSubgroup T) : Set T) :=
    hS.preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen _ ho
  have : (S.addSubgroupOf T).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact this.index_ne_zero

theorem measure_eq_relIndex_mul {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (S T : AddSubgroup V) (hST : S ≤ T) (hS : IsOpen (S : Set V))
    (hf : S.relIndex T ≠ 0) : μ T = S.relIndex T * μ S := by
  classical
  haveI : (S.addSubgroupOf T).FiniteIndex := ⟨hf⟩
  haveI := Fintype.ofFinite (T ⧸ S.addSubgroupOf T)
  let o : T ⧸ S.addSubgroupOf T → T := fun q => Quotient.out q
  have ho : ∀ q, ((o q : T) : T ⧸ S.addSubgroupOf T) = q := fun q => QuotientAddGroup.out_eq' q
  let C : T ⧸ S.addSubgroupOf T → Set V := fun q => (fun v => (-(o q : V)) + v) ⁻¹' (S : Set V)
  have hU : (T : Set V) = ⋃ q, C q := by
    ext v
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hv
      refine ⟨((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T), ?_⟩
      have h := QuotientAddGroup.eq.1 (ho ((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T))
      exact AddSubgroup.mem_addSubgroupOf.1 h
    · rintro ⟨q, hq⟩
      have h1 : -(o q : V) + v ∈ T := hST hq
      have := T.add_mem (o q).2 h1
      simpa using this
  have hd : Pairwise (Function.onFun Disjoint C) := by
    intro q q' hne
    refine Set.disjoint_left.2 fun v hv hv' => hne ?_
    have h1 : -(o q : V) + v ∈ S := hv
    have h2 : -(o q' : V) + v ∈ S := hv'
    have h3 : -(o q : V) + (o q' : V) ∈ S := by
      have := S.sub_mem h1 h2
      have e : -(o q : V) + v - (-(o q' : V) + v) = -(o q : V) + (o q' : V) := by abel
      rwa [e] at this
    have h4 : ((o q : T) : T ⧸ S.addSubgroupOf T) = (o q' : T) :=
      QuotientAddGroup.eq.2 (AddSubgroup.mem_addSubgroupOf.2 (by simpa using h3))
    rw [ho, ho] at h4
    exact h4
  have hm : ∀ q, MeasurableSet (C q) := fun q =>
    (hS.preimage (continuous_const.add continuous_id)).measurableSet
  have hc : ∀ q, μ (C q) = μ S := fun q => measure_preimage_add μ _ _
  rw [hU, measure_iUnion hd hm, tsum_fintype]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]

def perpSub {V : Type} [AddCommGroup V] (χ : V → V → ℂ) (hs : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1) (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (L : AddSubgroup V) : AddSubgroup V where
  carrier := perp χ L
  add_mem' := by
    intro y y' hy hy' x hx
    rw [hs, ha, hs y, hs y', hy x hx, hy' x hx, one_mul]
  zero_mem' := by
    intro x _
    have hne : χ 0 x ≠ 0 := fun h => by
      have := hn 0 x
      simp [h] at this
    have := ha 0 0 x
    rw [add_zero] at this
    rw [hs]
    exact (mul_eq_left₀ hne).1 this.symm
  neg_mem' := by
    intro y hy x hx
    have hne : χ 0 x ≠ 0 := fun h => by
      have := hn 0 x
      simp [h] at this
    have h0 : χ 0 x = 1 := by
      have := ha 0 0 x
      rw [add_zero] at this
      exact (mul_eq_left₀ hne).1 this.symm
    have := ha y (-y) x
    rw [add_neg_cancel, h0, hs y x, hy x hx, one_mul] at this
    rw [hs]
    exact this.symm

theorem relIndex_eq_of_pairing {V : Type} [AddCommGroup V] (χ : V → V → ℂ)
    (hs : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1)
    (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (X₀ X Y₀ Y : AddSubgroup V)
    (hX : ∀ x ∈ X, (x ∈ X₀ ↔ ∀ y ∈ Y, χ x y = 1))
    (hY : ∀ y ∈ Y, (y ∈ Y₀ ↔ ∀ x ∈ X, χ x y = 1))
    (fX : X₀.relIndex X ≠ 0) (fY : Y₀.relIndex Y ≠ 0) : X₀.relIndex X = Y₀.relIndex Y := by
  haveI : (X₀.addSubgroupOf X).FiniteIndex := ⟨fX⟩
  haveI : (Y₀.addSubgroupOf Y).FiniteIndex := ⟨fY⟩
  refine index_eq_of_pairing (fun (x : X) (y : Y) => χ x y) (fun x y => hn _ _)
    (fun x x' y => ha _ _ _)
    (fun x y y' => by
      change χ x ((y : V) + y') = _
      rw [hs, ha, hs y, hs y']) _ _ ?_ ?_
  · intro x
    rw [AddSubgroup.mem_addSubgroupOf, hX x x.2]
    exact ⟨fun h y => h y y.2, fun h y hy => h ⟨y, hy⟩⟩
  · intro y
    rw [AddSubgroup.mem_addSubgroupOf, hY y y.2]
    exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩

theorem selfDual_of_between : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (μ : Measure V), μ.IsAddHaarMeasure → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → ∀ L₁ L L₂ : AddSubgroup V, L₁ ≤ L → L ≤ L₂ → IsOpen (L₁ : Set V) → IsCompact (L₂ : Set V) → IsCompact (perp χ L₁) → IsOpen (perp χ L₂) → perp χ (perp χ L₁) ⊆ L₁ → perp χ (perp χ L₂) ⊆ L₂ → μ L₁ * μ (perp χ L₁) = 1 → μ L₂ * μ (perp χ L₂) = 1 → IsCompact (perp χ L) ∧ IsOpen (perp χ L) ∧ perp χ (perp χ L) ⊆ L ∧ μ L * μ (perp χ L) = 1 := by
  intro V _ _ _ _ _ χ μ hμ hs hn ha L₁ L L₂ h1 h2 oL₁ cL₂ cP₁ oP₂ dd₁ dd₂ _ m₂
  let Q : AddSubgroup V → AddSubgroup V := perpSub χ hs hn ha
  have hQ : ∀ (A : AddSubgroup V) (y : V), y ∈ Q A ↔ ∀ x ∈ A, χ x y = 1 := fun _ _ => Iff.rfl
  have hQc : ∀ A : AddSubgroup V, (Q A : Set V) = perp χ A := fun _ => rfl
  have anti : ∀ A B : AddSubgroup V, A ≤ B → Q B ≤ Q A :=
    fun A B h y hy x hx => hy x (h hx)
  have hself : ∀ A : AddSubgroup V, A ≤ Q (Q A) := fun A x hx y hy => by
    rw [hs]
    exact hy x hx
  have placeRankTwoOne : Q L₂ ≤ Q L₁ := anti _ _ (h1.trans h2)
  have P2 : Q L₂ ≤ Q L := anti _ _ h2
  have P1 : Q L ≤ Q L₁ := anti _ _ h1
  have LM : L ≤ Q (Q L) := hself L
  have ML : Q (Q L) ≤ L₂ := fun z hz => dd₂ (anti _ _ P2 hz)
  have n0 : L₁.relIndex L₂ ≠ 0 := relIndex_ne_zero_of_isOpen _ _ oL₁ cL₂
  have p0 : (Q L₂).relIndex (Q L₁) ≠ 0 := relIndex_ne_zero_of_isOpen _ _ oP₂ cP₁
  have ea := AddSubgroup.relIndex_mul_relIndex L₁ L L₂ h1 h2
  have ep := AddSubgroup.relIndex_mul_relIndex (Q L₂) (Q L) (Q L₁) P2 P1
  have ek := AddSubgroup.relIndex_mul_relIndex L (Q (Q L)) L₂ LM ML
  have a0 : L₁.relIndex L ≠ 0 := fun h => n0 (by rw [← ea, h, zero_mul])
  have a'0 : L.relIndex L₂ ≠ 0 := fun h => n0 (by rw [← ea, h, mul_zero])
  have q0 : (Q L₂).relIndex (Q L) ≠ 0 := fun h => p0 (by rw [← ep, h, zero_mul])
  have q'0 : (Q L).relIndex (Q L₁) ≠ 0 := fun h => p0 (by rw [← ep, h, mul_zero])
  have m0 : (Q (Q L)).relIndex L₂ ≠ 0 := fun h => a'0 (by rw [← ek, h, mul_zero])
  have kerL₁ : ∀ x, x ∈ L₁ ↔ ∀ y ∈ Q L₁, χ x y = 1 := fun x =>
    ⟨fun hx y hy => hy x hx, fun h => dd₁ fun y hy => by
      rw [hs]
      exact h y hy⟩
  have e1 : L₁.relIndex L = (Q L).relIndex (Q L₁) :=
    relIndex_eq_of_pairing χ hs hn ha L₁ L (Q L) (Q L₁) (fun x _ => kerL₁ x)
      (fun y _ => hQ L y) a0 q'0
  have e2 : (Q (Q L)).relIndex L₂ = (Q L₂).relIndex (Q L) :=
    relIndex_eq_of_pairing χ hs hn ha (Q (Q L)) L₂ (Q L₂) (Q L)
      (fun x _ => by
        rw [hQ]
        exact forall₂_congr fun y _ => by rw [hs])
      (fun y _ => hQ L₂ y) m0 q0
  have e3 : L₁.relIndex L₂ = (Q L₂).relIndex (Q L₁) :=
    relIndex_eq_of_pairing χ hs hn ha L₁ L₂ (Q L₂) (Q L₁) (fun x _ => kerL₁ x)
      (fun y _ => hQ L₂ y) n0 p0
  have e4 : L.relIndex L₂ = (Q L₂).relIndex (Q L) := by
    have : L₁.relIndex L * L.relIndex L₂ = L₁.relIndex L * (Q L₂).relIndex (Q L) := by
      rw [ea, e3, ← ep, e1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero a0) this
  have hk : L.relIndex (Q (Q L)) = 1 := by
    have : L.relIndex (Q (Q L)) * (Q (Q L)).relIndex L₂ = 1 * (Q (Q L)).relIndex L₂ := by
      rw [ek, one_mul, e2, e4]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero m0) this
  have MLe : Q (Q L) ≤ L := AddSubgroup.relIndex_eq_one.1 hk
  have oP : IsOpen (Q L : Set V) := AddSubgroup.isOpen_mono P2 oP₂
  refine ⟨?_, oP, MLe, ?_⟩
  · exact cP₁.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ oP) P1
  · change μ L * μ (Q L) = 1
    change μ L₂ * μ (Q L₂) = 1 at m₂
    rw [measure_eq_relIndex_mul μ L₁ L h1 oL₁ a0, measure_eq_relIndex_mul μ (Q L₂) (Q L) P2 oP₂ q0,
      ← m₂, measure_eq_relIndex_mul μ L₁ L₂ (h1.trans h2) oL₁ n0, ← ea, e4]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SW.CofinalDual
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompactSubgroupAndLevel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

theorem compact_open_sup {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    {L₁ L₂ : AddSubgroup V} (h₁ : IsCompact (L₁ : Set V)) (o₁ : IsOpen (L₁ : Set V))
    (h₂ : IsCompact (L₂ : Set V)) :
    IsCompact ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) ∧ IsOpen ((L₁ ⊔ L₂ : AddSubgroup V) : Set V) := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left o₁⟩
  rw [AddSubgroup.add_normal]
  exact h₁.add h₂

theorem compact_subgroup_and_level :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → (∀ K : Set V, IsCompact K → ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L) ∧ ∀ φ : V → ℂ, SB φ → ∃ L L' : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsCompact (L' : Set V) ∧ IsOpen (L' : Set V) ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x := by
  intro V _ _ _ χ μ h
  obtain ⟨hG, hT, -, -, -, -, hnb, hcov, -⟩ := h
  haveI := hG
  haveI := hT
  have cover : ∀ K : Set V, IsCompact K →
      ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ K ⊆ L := by
    intro K hK
    refine hK.induction_on (p := fun s => ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧
      IsOpen (L : Set V) ∧ s ⊆ L) ?_ ?_ ?_ ?_
    · obtain ⟨L, c, o, -⟩ := hcov 0
      exact ⟨L, c, o, Set.empty_subset _⟩
    · rintro s t hst ⟨L, c, o, hL⟩
      exact ⟨L, c, o, hst.trans hL⟩
    · rintro s t ⟨L₁, c₁, o₁, h₁⟩ ⟨L₂, c₂, o₂, h₂⟩
      obtain ⟨c, o⟩ := compact_open_sup c₁ o₁ c₂
      refine ⟨L₁ ⊔ L₂, c, o, Set.union_subset ?_ ?_⟩
      · exact h₁.trans (SetLike.coe_subset_coe.2 le_sup_left)
      · exact h₂.trans (SetLike.coe_subset_coe.2 le_sup_right)
    · intro x _
      obtain ⟨L, c, o, hx⟩ := hcov x
      exact ⟨L, mem_nhdsWithin_of_mem_nhds (o.mem_nhds hx), L, c, o, subset_rfl⟩
  refine ⟨cover, ?_⟩
  rintro φ ⟨hlc, hcs⟩
  obtain ⟨L, c, o, hL⟩ := cover _ hcs
  have hzero : ∀ x, x ∉ L → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hL hm))
  have hg : IsLocallyConstant (fun p : V × V => (φ (p.1 + p.2), φ p.1)) :=
    (hlc.comp_continuous continuous_add).prodMk (hlc.comp_continuous continuous_fst)
  have hW : IsOpen {p : V × V | φ (p.1 + p.2) = φ p.1} := hg {q : ℂ × ℂ | q.1 = q.2}
  have hsub : (L : Set V) ×ˢ ({0} : Set V) ⊆ {p : V × V | φ (p.1 + p.2) = φ p.1} := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    have hy' : y = 0 := hy
    simp [hy']
  obtain ⟨u, v, -, ov, hu, hv, huv⟩ := generalized_tube_lemma c isCompact_singleton hW hsub
  obtain ⟨L₀, c₀, o₀, h₀⟩ := hnb v (ov.mem_nhds (hv rfl))
  refine ⟨L, L₀ ⊓ L, c, o, ?_, ?_, inf_le_right, hzero, ?_⟩
  · have := c₀.inter_right c.isClosed
    simpa using this
  · simpa using o₀.inter o
  · intro x l hl
    have hl₀ : l ∈ L₀ := hl.1
    have hlL : l ∈ L := hl.2
    by_cases hx : x ∈ L
    · exact huv (Set.mk_mem_prod (hu hx) (h₀ hl₀))
    · rw [hzero x hx, hzero _ (fun hm => hx ?_)]
      simpa using L.sub_mem hm hlL

end GlobalTheory.CompanionTheory.SW.Core
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsCompactForMeasurePreservingEndosStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_for_measure_preserving_endos : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure], μ Set.univ = ⊤ → ∀ (Λ : Type) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) (C : Set V), IsCompact C → (∀ y, ∃ l, y - j l ∈ C) → ∃ Ω : Set V, IsCompact Ω ∧ ∀ e : V →+ V, Continuous e → μ.map e = μ → ∃ l, l ≠ 0 ∧ e (j l) ∈ Ω := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving | exact GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving | (intros; apply GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodularStatement
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_covolume_unimodular : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → μ 𝓕 ≠ 0 ∧ μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain | exact GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierTransformLatticeIndicator
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

theorem fou_indicator_coset :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V),
      NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V,
        fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y =
          ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
  intro V _ _ _ χ μ h L _ hLo a y
  obtain ⟨hTG, _, _, hSC, hB, hH, _, _, _, _, _, hadd, _⟩ := h
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet

  have key : ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      ((μ L).toReal : ℂ) * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
    by_cases hy : y ∈ perp χ L
    · have h1 : (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) =
          fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x := by
        funext x
        by_cases hx : x ∈ (L : Set V)
        · simp [Set.indicator_of_mem hx, hy x hx]
        · simp [Set.indicator_of_notMem hx]
      rw [h1, integral_indicator_const _ hLm, Set.indicator_of_mem hy]
      simp [Measure.real]
    · obtain ⟨l, hl, hne⟩ : ∃ l ∈ (L : Set V), χ l y ≠ 1 := by
        simpa [perp] using hy
      set J := ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ with hJ
      have hshift : J = χ l y * J := by
        have h2 := integral_add_right_eq_self (μ := μ)
          (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) l
        refine h2.symm.trans ?_
        rw [hJ, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hmem : x + l ∈ (L : Set V) ↔ x ∈ (L : Set V) := L.add_mem_cancel_right hl
        by_cases hx : x ∈ (L : Set V)
        · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
          ring
        · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
      have hJ0 : J = 0 := by
        have h3 : (1 - χ l y) * J = 0 := by
          rw [sub_mul, one_mul, ← hshift, sub_self]
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd (sub_eq_zero.1 h4).symm hne
        · exact h4
      rw [hJ0, Set.indicator_of_notMem hy, mul_zero]

  unfold fou
  have h5 := integral_add_right_eq_self (μ := μ)
    (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) x * χ x y) a
  rw [← h5]
  have h6 : (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) (x + a) * χ (x + a) y) =
      fun x => χ a y * (Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) := by
    funext x
    have hmem : x + a ∈ {x | x - a ∈ L} ↔ x ∈ (L : Set V) := by simp
    by_cases hx : x ∈ (L : Set V)
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
      ring
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
  rw [h6, integral_const_mul, key]
  ring

end GlobalTheory.CompanionTheory.SW.Core
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainOfSubgroupFromCosetReps
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem unfold_coset_sum_fundamentalDomain : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.unf

end GlobalTheory.CompanionTheory.Adelic
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GroupActionHaarScalingContinuousStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_action_haar_scaling_continuous : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : Type) [Group T] [TopologicalSpace T] [FirstCountableTopology T] [LocallyCompactSpace T] (a : T → V →+ V), (Continuous fun p : T × V => a p.1 p.2) → Continuous (fun t : T => t⁻¹) → (∀ y, a 1 y = y) → (∀ s t y, a (s * t) y = a s (a t y)) → ∃ χ : T →* ℝ≥0, Continuous χ ∧ ∀ t, μ.map (a t) = χ t • μ := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus | exact GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus | (intros; apply GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureIwasawaDecomposition
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem tripleProduct_map_leftInvariant : ∀ (G N H T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace N] [Group H] [MeasurableSpace H] [MeasurableMul H] [CommGroup T] [MeasurableSpace T] [MeasurableMul T] (μN : Measure N) [SFinite μN] (μH : Measure H) [SFinite μH] [μH.IsMulLeftInvariant] (μT : Measure T) [SFinite μT] [μT.IsMulLeftInvariant] (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0), Measurable nn → Measurable ι → Measurable mm → Measurable χ → (∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)) → (∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u) → (∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t) → (∀ u t, mm t * ι u = ι u * mm t) → ∀ (p : N) (u : H) (t : T), ((μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2).map (fun g => nn p * ι u * mm t * g) = (μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2 := by
  exact CompanionTheory.PlacePermOperatorBicommutantSpan.nuabs

end GlobalTheory.CompanionTheory.Adelic
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliableStatement
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_product_multipliable : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod | exact GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod | (intros; apply GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InvariantMeasureCompactCoverBound
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem integral_fundamentalDomain_le_siegel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∃ (C' : Set G) (K : ℝ≥0∞), IsCompact C' ∧ K < ⊤ ∧ ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ P → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ S : Set G, MeasurableSet S → (∀ᵐ p ∂ν, ∃ γ ∈ Γ, γ * p ∈ S) → ∀ f g : G → ℝ≥0∞, Measurable f → Measurable g → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ x, f x ≠ 0 → ∃ p ∈ P, ∃ c ∈ C, x = p * c) → (∀ p ∈ S, ∀ c ∈ C', f (p * c) ≤ g p) → ∫⁻ x in 𝓕, f x ∂μ ≤ K * ∫⁻ p in S, g p ∂ν := by
  first | exact CompanionTheory.PlacePermOperatorBicommutantSpan.cover | exact @CompanionTheory.PlacePermOperatorBicommutantSpan.cover

end GlobalTheory.CompanionTheory.Adelic
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixInductionTransvectionDiagonalStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_induction_transvection_diagonal : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : Matrix ι ι R → Prop), (∀ (i j : ι) (c : R), i ≠ j → p (Matrix.transvection i j c)) → (∀ D : ι → R, (∀ i, IsUnit (D i)) → p (Matrix.diagonal D)) → (∀ A B, IsUnit A.det → IsUnit B.det → p A → p B → p (A * B)) → ∀ A : Matrix ι ι R, IsUnit A.det → p A := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction | exact GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction | (intros; apply GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SymmetricInvertibleExistsPosdefCongruenceStatement
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_invertible_exists_posdef_congruence : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), B.IsSymm → B.det ≠ 0 → ∃ P : Matrix ι ι ℝ, P.PosDef ∧ P * B⁻¹ * P = B := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm | exact GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm | (intros; apply GlobalTheory.CompanionTheory.SW.exists_posDef_majorant_of_isSymm <;> assumption)
end

