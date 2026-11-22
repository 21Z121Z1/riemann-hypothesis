import Development.EtaleCohomology.TateTwists.Bundle0012
import Development.EtaleCohomology.TateTwists.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0007
import Development.EtaleCohomology.TateTwists.Bundle0010
import Development.EtaleCohomology.TateTwists.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0011
import Development.EtaleCohomology.TateTwists.Bundle0009

-- bundled from Development.EtaleCohomology.TateTwists.CcCupFlipPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.cc_cup_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k,
      ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
        c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def LateralTheory.EtaleFoundations.cc_aw_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1

def LateralTheory.EtaleFoundations.cc_aw_flip : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ}
    (h : n + m = k) (h' : m + n = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW h α.1 β.1 γ.1 → ν.IsAW h' β.1 α.1 γ'.1 →
      CohomologyClass.mk γ = (n * m).negOnePow • CohomologyClass.mk γ'
end

-- bundled from Development.EtaleCohomology.TateTwists.CupflipAwExistsPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_aw_cochain : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ γ : Cochain ((chains R).obj E) K k, μ.IsAW hk α β γ

def cupflip_aw_leibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
    (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)),
    μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ →
      δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂

theorem ev_zero_cochain {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  simp [ev]

theorem isAW_zero_left {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ}
    (hk : n + m = k) (β : Cochain ((chains R).obj E) J m) : μ.IsAW hk 0 β 0 := by
  intro N w h U x
  simp [ev_zero_cochain]

theorem isAW_zero_right {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ}
    (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) : μ.IsAW hk α 0 0 := by
  intro N w h U x
  simp [ev_zero_cochain]

theorem cupflip_aw_exists_of (hc : cupflip_aw_cochain) (hl : cupflip_aw_leibniz) : cupflip_aw_exists := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hc R μ E hk α.1 β.1
  have hα : δ n (n + 1) α.1 = 0 := Cocycle.δ_eq_zero α (n + 1)
  have hβ : δ m (m + 1) β.1 = 0 := Cocycle.δ_eq_zero β (m + 1)
  have h1 : μ.IsAW (by omega) (δ n (n + 1) α.1) β.1 (0 : Cochain ((chains R).obj E) K (k + 1)) := by
    rw [hα]; exact isAW_zero_left μ _ β.1
  have h2 : μ.IsAW (by omega) α.1 (δ m (m + 1) β.1) (0 : Cochain ((chains R).obj E) K (k + 1)) := by
    rw [hβ]; exact isAW_zero_right μ _ α.1
  have hδ : δ k (k + 1) γ = 0 := by
    rw [hl R μ hk α.1 β.1 γ 0 0 hγ h1 h2]; simp
  exact ⟨Cocycle.mk γ (k + 1) rfl hδ, hγ⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.CupflipAwFlipPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def CupflipSteen (h : ∀ N, Pr N →₀ ℤ) : Prop :=
  (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧
    ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1)

def cupflip_steen : Prop := ∃ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h

def cupflip_homotopy : Prop :=
  ∀ h : ∀ N, Pr N →₀ ℤ, CupflipSteen h →
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν →
    ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (hk' : m + n = k)
      (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → ν.IsAW hk' β.1 α.1 γ'.1 →
        ∃ η : Cochain ((chains R).obj E) K (k - 1), δ (k - 1) k η = γ.1 - (n * m).negOnePow • γ'.1

theorem cupflip_aw_flip_of (hst : cupflip_steen) (hho : cupflip_homotopy) : cupflip_aw_flip := by
  intro R _ I J K μ ν hflip E n m k h h' α β γ γ' hγ hγ'
  obtain ⟨s, hs⟩ := hst
  obtain ⟨η, hη⟩ := hho s hs R μ ν hflip E h h' α β γ γ' hγ hγ'
  rcases Int.units_eq_one_or ((n * m).negOnePow) with he | he
  · rw [he, one_smul] at hη ⊢
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (k - 1) (by omega)]
    exact ⟨η, hη⟩
  · rw [he, Units.neg_smul, one_smul] at hη ⊢
    rw [← sub_eq_zero, sub_neg_eq_add, ← CohomologyClass.mk_add, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (k - 1) (by omega)]
    exact ⟨η, by rw [hη, sub_neg_eq_add]; rfl⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.CupflipWdPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_wd_aw : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
    (∀ α β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β γ' → γ = γ') ∧
    (∀ α α' β γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ α β β' γ γ', μ.IsAW (E := E) hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ'))

def cupflip_wd_cobdry : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k),
    μ.IsAW hk α.1 β.1 γ.1 → (α ∈ coboundaries _ _ n ∨ β ∈ coboundaries _ _ m) → γ ∈ coboundaries _ _ k

theorem cupflip_wd_of (ha : cupflip_wd_aw) (hb : cupflip_wd_cobdry) : cupflip_wd := by
  intro R _ I J K μ E n m k hk
  classical
  obtain ⟨hex, huniq, haddl, haddr⟩ := ha R μ E hk
  let aw : Cocycle ((chains R).obj E) I n → Cocycle ((chains R).obj E) J m → Cocycle ((chains R).obj E) K k :=
    fun α β => Classical.choose (hex α β)
  have haw : ∀ α β, μ.IsAW hk α.1 β.1 (aw α β).1 := fun α β => Classical.choose_spec (hex α β)
  have heq : ∀ α β γ, μ.IsAW hk α.1 β.1 γ.1 → aw α β = γ := fun α β γ h =>
    Subtype.ext (huniq _ _ _ _ (haw α β) h)
  have addl : ∀ α α' β, aw (α + α') β = aw α β + aw α' β := fun α α' β =>
    heq _ _ _ (haddl _ _ _ _ _ (haw α β) (haw α' β))
  have addr : ∀ α β β', aw α (β + β') = aw α β + aw α β' := fun α β β' =>
    heq _ _ _ (haddr _ _ _ _ _ (haw α β) (haw α β'))
  let g : Cocycle ((chains R).obj E) I n →
      CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k :=
    fun α => CohomologyClass.descAddMonoidHom
      (AddMonoidHom.mk' (fun β => CohomologyClass.mk (aw α β))
        (fun β β' => by simp only [addr, CohomologyClass.mk_add]))
      (fun β hβ => by
        rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, CohomologyClass.mk_eq_zero_iff]
        exact hb R μ E hk α β _ (haw α β) (Or.inr hβ))
  have gmk : ∀ α β, g α (CohomologyClass.mk β) = CohomologyClass.mk (aw α β) := fun _ _ => rfl
  have gadd : ∀ α α', g (α + α') = g α + g α' := by
    intro α α'
    refine AddMonoidHom.ext fun b => ?_
    obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
    rw [AddMonoidHom.add_apply, gmk, gmk, gmk, addl, CohomologyClass.mk_add]
  let c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
      CohomologyClass ((chains R).obj E) K k :=
    CohomologyClass.descAddMonoidHom (AddMonoidHom.mk' g gadd) (fun α hα => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
      refine AddMonoidHom.ext fun b => ?_
      obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
      rw [gmk, AddMonoidHom.zero_apply, CohomologyClass.mk_eq_zero_iff]
      exact hb R μ E hk α β _ (haw α β) (Or.inl hα))
  refine ⟨c, fun α β γ h => ?_⟩
  change g α (CohomologyClass.mk β) = _
  rw [gmk, heq α β γ h]

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsForPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleAlexanderWhitneyCupCochainExistsForPairing : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ γ : Cochain ((chains R).obj E) K k, μ.IsAW hk α β γ

def EtaleAlexanderWhitneyCupUniqueBiadditive : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β γ' → γ = γ') ∧
    (∀ (α α' : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) (β β' : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) ∧
    (∀ (β : Cochain ((chains R).obj E) J m), μ.IsAW hk 0 β 0) ∧
    (∀ (α : Cochain ((chains R).obj E) I n), μ.IsAW hk α 0 0)

def EtaleAlexanderWhitneyCupLeibnizRule : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ → δ k k₁ γ = γ₁ + n.negOnePow • γ₂

theorem ev_add' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  unfold ev
  rw [Cochain.add_v, Preadditive.comp_add]
  rfl

theorem ev_zero' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  unfold ev
  rw [Cochain.zero_v, Limits.comp_zero]
  rfl

def EtaleAlexanderWhitneyCupCochainUnique : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β γ' → γ = γ'

theorem awalg_of (hu : EtaleAlexanderWhitneyCupCochainUnique) : EtaleAlexanderWhitneyCupUniqueBiadditive := by
  intro R _ I J K μ E n m k hk
  refine ⟨hu R μ hk, ?_, ?_, ?_, ?_⟩
  · intro α α' β γ γ' h h' N w hw U x
    rw [ev_add', h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_add', map_add, LinearMap.add_apply, smul_add]
  · intro α β β' γ γ' h h' N w hw U x
    rw [ev_add', h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_add', map_add, smul_add]
  · intro β N w hw U x
    rw [ev_zero']
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ev_zero', map_zero, LinearMap.zero_apply, smul_zero]
  · intro α N w hw U x
    rw [ev_zero']
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ev_zero', map_zero, smul_zero]

theorem cup_spec_part1 (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule)
    (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1 := by
  obtain ⟨γ, hγ⟩ := h1 R μ hk α.1 β.1
  obtain ⟨γ₁, hγ₁⟩ := h1 R μ (show (n + 1) + m = k + 1 by omega) (δ n (n + 1) α.1) β.1
  obtain ⟨γ₂, hγ₂⟩ := h1 R μ (show n + (m + 1) = k + 1 by omega) α.1 (δ m (m + 1) β.1)
  have hd := h3 R μ hk rfl rfl _ _ α.1 β.1 γ γ₁ γ₂ hγ hγ₁ hγ₂
  rw [Cocycle.δ_eq_zero] at hγ₁
  rw [Cocycle.δ_eq_zero] at hγ₂
  have e1 : γ₁ = 0 := (h2 R μ _).1 _ _ _ _ hγ₁ ((h2 R μ _).2.2.2.1 _)
  have e2 : γ₂ = 0 := (h2 R μ _).1 _ _ _ _ hγ₂ ((h2 R μ _).2.2.2.2 _)
  rw [e1, e2, smul_zero, add_zero] at hd
  exact ⟨Cocycle.mk γ (k + 1) rfl hd, hγ⟩

def EtaleAlexanderWhitneyCupDescendsToCohomology : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
        CohomologyClass ((chains R).obj E) K k,
      ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
        c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

section Desc
variable (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule)
  {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)

noncomputable def chZ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    Cocycle ((chains R).obj E) K k :=
  Classical.choose (cup_spec_part1 h1 h2 h3 R μ hk α β)

theorem chZ_spec (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    μ.IsAW hk α.1 β.1 (chZ h1 h2 h3 μ E hk α β).1 :=
  Classical.choose_spec (cup_spec_part1 h1 h2 h3 R μ hk α β)

theorem chZ_eq (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) : chZ h1 h2 h3 μ E hk α β = γ :=
  Cocycle.ext ((h2 R μ hk).1 _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) h)

theorem chZ_add_left (α α' : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    chZ h1 h2 h3 μ E hk (α + α') β = chZ h1 h2 h3 μ E hk α β + chZ h1 h2 h3 μ E hk α' β :=
  chZ_eq h1 h2 h3 μ E hk _ _ _ ((h2 R μ hk).2.1 _ _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) (chZ_spec h1 h2 h3 μ E hk α' β))

theorem chZ_add_right (α : Cocycle ((chains R).obj E) I n) (β β' : Cocycle ((chains R).obj E) J m) :
    chZ h1 h2 h3 μ E hk α (β + β') = chZ h1 h2 h3 μ E hk α β + chZ h1 h2 h3 μ E hk α β' :=
  chZ_eq h1 h2 h3 μ E hk _ _ _ ((h2 R μ hk).2.2.1 _ _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) (chZ_spec h1 h2 h3 μ E hk α β'))

theorem chZ_cob_left (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (hα : α ∈ coboundaries _ _ n) : chZ h1 h2 h3 μ E hk α β ∈ coboundaries _ _ k := by
  obtain ⟨m', hm', η, hη⟩ := hα
  obtain ⟨γ, hγ⟩ := h1 R μ (show m' + m = m' + m from rfl) η β.1
  obtain ⟨γ₂, hγ₂⟩ := h1 R μ (show m' + (m + 1) = k by omega) η (δ m (m + 1) β.1)
  have hd := h3 R μ rfl hm' rfl (show n + m = k from hk) (show m' + (m + 1) = k by omega) η β.1 γ
    (chZ h1 h2 h3 μ E hk α β).1 γ₂ hγ (by rw [hη]; exact chZ_spec h1 h2 h3 μ E hk α β) hγ₂
  rw [Cocycle.δ_eq_zero] at hγ₂
  have e2 : γ₂ = 0 := (h2 R μ _).1 _ _ _ _ hγ₂ ((h2 R μ _).2.2.2.2 _)
  rw [e2, smul_zero, add_zero] at hd
  exact ⟨m' + m, by omega, γ, hd⟩

theorem chZ_cob_right (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (hβ : β ∈ coboundaries _ _ m) : chZ h1 h2 h3 μ E hk α β ∈ coboundaries _ _ k := by
  obtain ⟨m', hm', θ, hθ⟩ := hβ
  obtain ⟨γ, hγ⟩ := h1 R μ (show n + m' = n + m' from rfl) α.1 θ
  obtain ⟨γ₁, hγ₁⟩ := h1 R μ (show (n + 1) + m' = k by omega) (δ n (n + 1) α.1) θ
  have hd := h3 R μ rfl rfl hm' (show (n + 1) + m' = k by omega) (show n + m = k from hk) α.1 θ γ
    γ₁ (chZ h1 h2 h3 μ E hk α β).1 hγ hγ₁ (by rw [hθ]; exact chZ_spec h1 h2 h3 μ E hk α β)
  rw [Cocycle.δ_eq_zero] at hγ₁
  have e1 : γ₁ = 0 := (h2 R μ _).1 _ _ _ _ hγ₁ ((h2 R μ _).2.2.2.1 _)
  rw [e1, zero_add] at hd
  refine ⟨n + m', by omega, n.negOnePow • γ, ?_⟩
  rw [δ_units_smul, hd, smul_smul, Int.units_mul_self, one_smul]

end Desc

theorem desc_of (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule) :
    EtaleAlexanderWhitneyCupDescendsToCohomology := by
  intro R _ I J K μ E n m k hk
  let G : Cocycle ((chains R).obj E) I n → (CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k) :=
    fun α => QuotientAddGroup.lift _
      (AddMonoidHom.mk' (fun β => CohomologyClass.mk (chZ h1 h2 h3 μ E hk α β))
        (fun β β' => by rw [chZ_add_right, CohomologyClass.mk_add]))
      (fun β hβ => by
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
        exact (QuotientAddGroup.eq_zero_iff _).2 (chZ_cob_right h1 h2 h3 μ E hk α β hβ))
  let F : Cocycle ((chains R).obj E) I n →+ (CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k) :=
    AddMonoidHom.mk' G (fun α α' => by
      refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β => ?_)
      show CohomologyClass.mk _ = CohomologyClass.mk _ + CohomologyClass.mk _
      rw [chZ_add_left, CohomologyClass.mk_add])
  refine ⟨QuotientAddGroup.lift _ F (fun α hα => ?_), ?_⟩
  · rw [AddMonoidHom.mem_ker]
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β => ?_)
    show CohomologyClass.mk _ = 0
    exact (QuotientAddGroup.eq_zero_iff _).2 (chZ_cob_left h1 h2 h3 μ E hk α β hα)
  · intro α β γ hγ
    show CohomologyClass.mk _ = _
    rw [chZ_eq h1 h2 h3 μ E hk α β γ hγ]

theorem etale_cup_compat_spec_of_alexander_whitney_exists_unique_leibniz (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (hu : EtaleAlexanderWhitneyCupCochainUnique)
    (h3 : EtaleAlexanderWhitneyCupLeibnizRule) : EtaleCupCompatAlexanderWhitneyCocycleSpec := by
  have h2 := awalg_of hu
  have h4 := desc_of h1 h2 h3
  intro R _ I J K μ E n m k hk
  refine ⟨fun α β => cup_spec_part1 h1 h2 h3 R μ hk α β, ?_⟩
  intro α β γ hγ
  exact pick_spec (h4 R μ E hk) α β γ hγ
end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ConerveIsomorphism

variable {T : Type 1} [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ)
  {U V : T} (g : U ⟶ V)

noncomputable def phi (n : ℕ) :
    (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop ⟶
      widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) :=
  WidePullback.lift (Ψ.map (WidePushout.head _)).unop (fun j => (Ψ.map (WidePushout.ι _ j)).unop)
    (fun j => by
      have h := WidePushout.arrow_ι (fun _ : Fin (n+1) => g) j
      rw [← unop_comp, ← Ψ.map_comp, h])

@[reassoc (attr := simp)]
lemma phi_π (n : ℕ) (j : Fin (n+1)) :
    phi Ψ g n ≫ WidePullback.π _ j = (Ψ.map (WidePushout.ι _ j)).unop := by
  unfold phi; erw [WidePullback.lift_π]

@[reassoc (attr := simp)]
lemma phi_base (n : ℕ) :
    phi Ψ g n ≫ WidePullback.base _ = (Ψ.map (WidePushout.head _)).unop := by
  unfold phi; erw [WidePullback.lift_base]

lemma aux (n : ℕ) (j : Fin (n+1)) :
    Ψ.map g ≫ (WidePullback.π (fun _ : Fin (n+1) => (Ψ.map g).unop) j).op =
      (WidePullback.base (fun _ : Fin (n+1) => (Ψ.map g).unop)).op := by
  rw [← WidePullback.π_arrow (fun _ : Fin (n+1) => (Ψ.map g).unop) j]
  rfl

noncomputable def cocone (n : ℕ) : Cocone (WidePushoutShape.wideSpan U (fun _ : Fin (n+1) => V) (fun _ => g) ⋙ Ψ) where
  pt := op (widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop))
  ι :=
    { app := fun j => match j with
        | none => (WidePullback.base _).op
        | some j => (WidePullback.π _ j).op
      naturality := by
        rintro X Y (_ | j)
        · rw [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
            Category.id_comp, Category.comp_id]
        · exact (aux Ψ g n j).trans (Category.comp_id _).symm }

lemma natural (a b : ℕ) (σ : Fin (a+1) → Fin (b+1)) :
    (Ψ.map (WidePushout.desc (WidePushout.head (fun _ : Fin (b+1) => g))
      (fun i => WidePushout.ι (fun _ : Fin (b+1) => g) (σ i))
      (fun i => WidePushout.arrow_ι (fun _ : Fin (b+1) => g) (σ i)))).unop ≫ phi Ψ g a =
    phi Ψ g b ≫ WidePullback.lift (WidePullback.base (fun _ : Fin (b+1) => (Ψ.map g).unop))
      (fun i => WidePullback.π (fun _ : Fin (b+1) => (Ψ.map g).unop) (σ i))
      (fun i => WidePullback.π_arrow (fun _ : Fin (b+1) => (Ψ.map g).unop) (σ i)) := by
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, Category.assoc, phi_π, WidePullback.lift_π, phi_π, ← unop_comp, ← Ψ.map_comp,
      WidePushout.ι_desc]
  · rw [Category.assoc, Category.assoc, phi_base, WidePullback.lift_base, phi_base, ← unop_comp,
      ← Ψ.map_comp, WidePushout.head_desc]

variable (hΨ : ∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ)

noncomputable def hc (n : ℕ) :
    IsColimit (Ψ.mapCocone (colimit.cocone (WidePushoutShape.wideSpan U (fun _ : Fin (n+1) => V) (fun _ => g)))) :=
  haveI := hΨ n
  isColimitOfPreserves Ψ (colimit.isColimit _)

noncomputable def psi (n : ℕ) :
    widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) ⟶
      (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop :=
  ((hc Ψ g hΨ n).desc (cocone Ψ g n)).unop

lemma desc_phi (n : ℕ) : (hc Ψ g hΨ n).desc (cocone Ψ g n) ≫ (phi Ψ g n).op = 𝟙 _ := by
  apply (hc Ψ g hΨ n).hom_ext
  rintro (_ | j)
  · rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ (phi Ψ g n).op)
      ((hc Ψ g hΨ n).fac (cocone Ψ g n) none)).trans (Quiver.Hom.unop_inj (phi_base Ψ g n)))
  · rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun x => x ≫ (phi Ψ g n).op)
      ((hc Ψ g hΨ n).fac (cocone Ψ g n) (some j))).trans (Quiver.Hom.unop_inj (phi_π Ψ g n j)))

noncomputable def levelIso (n : ℕ) :
    (Ψ.obj (widePushout U (fun _ : Fin (n+1) => V) (fun _ => g))).unop ≅
      widePullback (Ψ.obj U).unop (fun _ : Fin (n+1) => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) where
  hom := phi Ψ g n
  inv := psi Ψ g hΨ n
  hom_inv_id := congrArg Quiver.Hom.unop (desc_phi Ψ g hΨ n)
  inv_hom_id := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, phi_π, Category.id_comp]
      exact congrArg Quiver.Hom.unop ((hc Ψ g hΨ n).fac (cocone Ψ g n) (some j))
    · rw [Category.assoc, phi_base, Category.id_comp]
      exact congrArg Quiver.Hom.unop ((hc Ψ g hΨ n).fac (cocone Ψ g n) none)

end LateralTheory.EtaleFoundations.ConerveIsomorphism

open LateralTheory.EtaleFoundations.ConerveIsomorphism in
theorem LateralTheory.EtaleFoundations.etale_cech_conerve_image_iso_cech_nerve_of_preserves_wide_pushouts : LateralTheory.EtaleFoundations.EtaleCechConerveImageIsoCechNerveOfPreservesWidePushouts := by
  intro T _ _ Ψ hΨ U V g
  refine ⟨NatIso.ofComponents (fun n => levelIso Ψ g hΨ n.unop.len) ?_, ?_⟩
  · intro m n h
    exact natural Ψ g _ _ h.unop.toOrderHom
  · ext n : 1
    exact (phi_base Ψ g (unop n).len).symm
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCochainComplexBasicPropertiesOfComponents
section
namespace LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
theorem etale_cochain_complex_basic_properties_of_components : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  apply LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := etale_cochain_complex_basic_properties_of_components
end LateralTheory.Fin.EtaleSimplicialChainsFreeDescription
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCupProductFlipExistsOfComponents
section
namespace LateralTheory.Fin.EtaleComplexPairingFlipExists
theorem etale_cup_product_flip_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := by
  apply LateralTheory.EtaleFoundations.etale_complex_pairing_flip_exists
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := etale_cup_product_flip_exists_of_components
end LateralTheory.Fin.EtaleComplexPairingFlipExists
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleEvaluationMapConstructionOfComponents
section
namespace LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
theorem etale_evaluation_map_construction_of_components : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := by
  apply LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainExistsOfNaturalEvaluation := etale_evaluation_map_construction_of_components
end LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleFreeModuleCohomologyHomOfComponents
section
namespace LateralTheory.Fin.EtaleFreeSheafUniversalProperty
theorem etale_free_module_cohomology_hom_of_components : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_free_sheaf_hom_universal_property_holds
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleFreeSheafUniversalProperty := etale_free_module_cohomology_hom_of_components
end LateralTheory.Fin.EtaleFreeSheafUniversalProperty
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleRootsOfUnityTwistFlatOfLocalFree
section
namespace LateralTheory.Fin.EtaleTateTwistSheafFlat
theorem etale_roots_of_unity_twist_flat_of_local_free : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := by
  apply LateralTheory.EtaleFoundations.etale_tate_twist_sections_flat_of_quotient_iso
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := etale_roots_of_unity_twist_flat_of_local_free
end LateralTheory.Fin.EtaleTateTwistSheafFlat
end

-- bundled from Development.EtaleCohomology.TateTwists.PpEvDeltaPf
section
theorem LateralTheory.EtaleFoundations.pp_ev_delta_of : LateralTheory.EtaleFoundations.pp_ev_delta :=
  LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds
end

