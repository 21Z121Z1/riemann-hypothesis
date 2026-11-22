import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.CoboundaryTransfers.Statement

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def IsWachBasis {r : ℕ} (b : Fin r → W.DD T) : Prop :=
  LinearIndependent (LetA O n) b ∧ Submodule.span (LetA O n) (Set.range b) = W.N T ∧
    LinearIndependent W.EE b ∧ Submodule.span W.EE (Set.range b) = ⊤

def IsLetterBasis (i : ZMod n) {r : ℕ} (b : Fin r → W.DD T) : Prop :=
  (∀ k, b k ∈ W.Nl T i) ∧
    ∀ x ∈ W.Nl T i, ∃! c : Fin r → PowerSeries O,
      x = ∑ k, (Pi.single i (c k) : LetA O n) • b k

def FrobBounds (M₀ h₀ : ℕ) : Prop :=
  (∀ x ∈ W.N T, W.Q ^ M₀ • W.φD T x ∈ W.N T) ∧ ∀ y ∈ W.N T, W.Q ^ h₀ • y ∈ W.φpull T

def FreeLetters : Prop :=
  (∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, IsWachBasis W T b) ∧
    (∀ i : ZMod n, ∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, IsLetterBasis W T i b) ∧
    ∃ M₀ h₀ : ℕ, FrobBounds W T M₀ h₀

theorem IsWachBasis.letter {r : ℕ} {b : Fin r → W.DD T} (hb : IsWachBasis W T b) (i : ZMod n) :
    IsLetterBasis W T i (fun k => (letE i : LetA O n) • b k) := by
  obtain ⟨hli, hsp, -, -⟩ := hb
  have hmul : ∀ a : PowerSeries O,
      (Pi.single i a : LetA O n) * letE i = Pi.single i a := by
    intro a
    funext j
    by_cases h : j = i
    · subst h; simp [letE]
    · simp [letE, h]
  have hmul' : ∀ a : LetA O n, (letE i : LetA O n) * a = Pi.single i (a i) := by
    intro a
    funext j
    by_cases h : j = i
    · subst h; simp [letE]
    · simp [letE, h]
  refine ⟨fun k => ⟨b k, ?_, rfl⟩, ?_⟩
  · rw [← hsp]; exact Submodule.subset_span ⟨k, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span (LetA O n) (Set.range b) := by rw [hsp]; exact hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy'
    have key : (letE i : LetA O n) • (∑ k, a k • b k) =
        ∑ k, (Pi.single i (a k i) : LetA O n) • b k := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, hmul']
    refine ⟨fun k => a k i, ?_, fun c hc => ?_⟩
    · change (letE i : LetA O n) • (∑ k, a k • b k) = _
      rw [key]
      exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, hmul]
    · change (letE i : LetA O n) • (∑ k, a k • b k) = _ at hc
      rw [key] at hc
      simp only [smul_smul, hmul] at hc
      funext k
      have h0 := Fintype.linearIndependent_iff.1 hli
        (fun k => (Pi.single i (c k) : LetA O n) - Pi.single i (a k i))
        (by simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]) k
      have h1 := congrFun h0 i
      simpa [sub_eq_zero] using h1

theorem FrobBounds.pull {M₀ h₀ : ℕ} (hF : FrobBounds W T M₀ h₀) :
    ∀ y ∈ W.φpull T, W.Q ^ M₀ • y ∈ W.N T := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨z, hz, rfl⟩ := hx; exact hF.1 z hz
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact (W.N T).add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact (W.N T).smul_mem a hx

end Generic

def WachLettersFree (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    FreeLetters (H.W K s LL h) T

end GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachModuleUniqueness
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachModuleUniqueness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def invSub {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] (a : A) (M : Submodule A D) :
    Submodule A D where
  carrier := {x | ∃ k : ℕ, a ^ k • x ∈ M}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨k, hk⟩ ⟨m, hm⟩
    refine ⟨k + m, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]; exact M.smul_mem _ hk
    · rw [pow_add, mul_smul]; exact M.smul_mem _ hm
  smul_mem' := by
    rintro c x ⟨k, hk⟩
    exact ⟨k, by rw [smul_comm]; exact M.smul_mem _ hk⟩

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def BasisCond (N₁ : Submodule (LetA O n) (W.DD T)) : Prop :=
  ∃ (ι : Type) (b : Module.Basis ι (LetA O n) ↥N₁) (c : Module.Basis ι W.EE (W.DD T)),
    ∀ j, c j = (b j : W.DD T)

def GammaStable (N₁ : Submodule (LetA O n) (W.DD T)) : Prop :=
  W.γ T '' (N₁ : Set (W.DD T)) = (N₁ : Set (W.DD T))

def GammaTrivModπ (N₁ : Submodule (LetA O n) (W.DD T)) : Prop :=
  ∀ x ∈ N₁, ∃ y ∈ N₁, W.γ T x - x = (letπ : LetA O n) • y

def phiSpan (N₁ : Submodule (LetA O n) (W.DD T)) : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (N₁ : Set (W.DD T)))

def PhiIsoAwayQ (N₁ : Submodule (LetA O n) (W.DD T)) : Prop :=
  invSub W.Q (phiSpan W T N₁) = invSub W.Q N₁

example : GammaStable W T (W.N T) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact W.N_Γ T _ x hx
  · intro x hx
    refine ⟨W.γD T W.gam⁻¹ x, W.N_Γ T _ x hx, ?_⟩
    change W.γD T W.gam (W.γD T W.gam⁻¹ x) = x
    rw [← W.γD_mul, mul_inv_cancel, W.γD_one]

example : GammaTrivModπ W T (W.N T) := fun x hx => W.N_π T W.gam x hx

example : PhiIsoAwayQ W T (W.N T) := by
  apply le_antisymm
  · rintro x ⟨k, hk⟩
    have h : phiSpan W T (W.N T) ≤ invSub W.Q (W.N T) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      exact W.N_φ T y hy
    obtain ⟨m, hm⟩ := h hk
    exact ⟨m + k, by rw [pow_add, mul_smul]; exact hm⟩
  · rintro x ⟨k, hk⟩
    obtain ⟨m, hm⟩ := W.N_φinv T _ hk
    exact ⟨m + k, by rw [pow_add, mul_smul]; exact hm⟩

end Generic

def WachUnique (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (_C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ N₁ : Submodule (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ((H.W K s LL h).DD T),
      BasisCond (H.W K s LL h) T N₁ →
      GammaStable (H.W K s LL h) T N₁ →
      GammaTrivModπ (H.W K s LL h) T N₁ →
      PhiIsoAwayQ (H.W K s LL h) T N₁ →
      N₁ = (H.W K s LL h).N T

end GlobalTheory.IndefiniteRowSideFullHecke.WachModuleUniqueness
end
end

