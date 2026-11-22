import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0012
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LenTLeThree
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ContentBoundLevelIdeal

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AlgebraMapMemInvariants
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

open TypesA

variable (W : LocWach PD LL O v n)

section Smul

variable {T : LocLat G Qp LL O}

theorem algebraMap_mem_invariants (t : O) : algebraMap O (LetA O n) t ∈ W.AΔ := W.AΔ.algebraMap_mem t

theorem algebraMap_smul_eq_smul (t : O) (x : W.DD T) : algebraMap O (LetA O n) t • x = t • x :=
  algebraMap_smul (LetA O n) t x

theorem inI_algebraMap_smul {c : ZMod n} (t : O) {w : W.DD T} (h : InI W T c w) :
    InI W T c (algebraMap O (LetA O n) t • w) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (algebraMap O (LetA O n) t • w) = algebraMap O (LetA O n) t • w
    rw [smul_comm]
    exact congrArg _ h1
  · intro δ hδ
    rw [algebraMap_smul_eq_smul, map_smul, h2 δ hδ]
  · have : W.γ T (algebraMap O (LetA O n) t • w) - algebraMap O (LetA O n) t • w =
        algebraMap O (LetA O n) t • (W.γ T w - w) := by
      rw [algebraMap_smul_eq_smul, algebraMap_smul_eq_smul, map_smul, smul_sub]
    rw [this]
    exact InFNc_smul W (algebraMap_mem_invariants W t) h3

theorem repVV_smul_invariant {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ} {b : Fin d → W.DD T}
    {sol : Fin d → ℕ → Fin d → LL} (a : LetA O n) (ha : a ∈ W.AΔ) {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a • x) (fun k => algebraMap (LetA O n) W.EE a * f k) := by
  obtain ⟨κ, κ', H, a', hH, ha', hP⟩ := h
  refine ⟨κ, κ', H, fun k => a * a' k, hH,
    fun k => ⟨W.AΔ.mul_mem ha (ha' k).1, ?_⟩, ?_⟩
  · rw [map_mul, ← (ha' k).2]
    ring
  · have hs : ∑ k, (a * a' k) • ((W.φD T) ^ e) (H k) = a • ∑ k, a' k • ((W.φD T) ^ e) (H k) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_smul _ _ _
    rw [hs]
    have key : lA W ^ κ' • (lA W ^ κ • Λ • (a • x) - a • ∑ k, a' k • ((W.φD T) ^ e) (H k)) =
        a • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a' k • ((W.φD T) ^ e) (H k))) := by
      simp only [smul_sub]
      rw [smul_comm Λ a x, smul_comm (lA W ^ κ) a, smul_comm (lA W ^ κ') a, smul_comm (lA W ^ κ') a]
    rw [key]
    exact inMultiple_smul W ha hP

end Smul

theorem liftsAt_algebraMap_mul (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) {g : W.EE}
    {e : ℕ} (t : O) (h : LiftsAt W A F c bb sol k₀ g e) :
    LiftsAt W A F c bb sol k₀ (algebraMap O W.EE t * g) e := by
  obtain ⟨w₁, z, h1, ⟨Λ', hΛ', h2⟩, h3, h4, h5⟩ := h
  set a := algebraMap O (LetA O n) t with ha_def
  have ha : a ∈ W.AΔ := algebraMap_mem_invariants W t
  refine ⟨a • w₁, a • z, inI_algebraMap_smul W t h1, ⟨Λ', hΛ', ?_⟩, ?_, InFNc_smul W ha h4, ?_⟩
  · rw [smul_comm]
    exact InFNc_smul W ha h2
  · rw [map_smulA, smul_comm]
    exact inMultiple_smul W ha h3
  · have h6 := repVV_smul_invariant W a ha h5
    rw [map_smulA, ← smul_sub]
    refine RepVV_congr W h6 rfl fun k => ?_
    have hat : algebraMap (LetA O n) W.EE a = algebraMap O W.EE t := by
      rw [ha_def, ← IsScalarTower.algebraMap_apply]
    split_ifs
    · rw [hat]; ring
    · rw [mul_zero]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcBasic
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem arcBasic [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi) :
    let A := arcOf b w S η up size
    A.OK ∧ (∑ c ∈ A.cuts, A.len c) = n ∧
    (Alt b η up size → ∀ c ∈ A.cuts, A.len c ≤ 3) ∧
    (∀ R : ℕ, 1 ≤ R → One b η R up size → ∀ c ∈ A.cuts, A.len c ≤ R) ∧
    (A.σ PD.p : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size :=
  SetupA.arcBasic_core W F hB

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLenThreeThickLetters
section
open scoped TensorProduct

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace ArcLengthThreeFiltration

theorem φVB_inj (T : LocLat G Qp LL O) : Function.Injective (φVB PD (LL := LL) (V := T.V)) := by
  have hφ : Function.Injective (PD.φ.toLinearMap) := by simpa using PD.φ_inj
  have h : ⇑(φVB PD (LL := LL) (V := T.V)) = ⇑(LinearMap.lTensor T.V PD.φ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [φVB]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hφ

theorem crisMap_φ {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (x : T₁.V ⊗[Qp] B) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (φVB PD (LL := LL) (V := T₁.V) x) =
      φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp [φVB, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (W : LocWach PD LL O v n)

theorem dv_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dv W T e b c₀) := by
  first
  | (simp only [dv, pow_succ', Module.End.mul_apply, map_sum, map_smul]; done)
  | (simp only [dv, pow_succ', LinearMap.mul_apply, map_sum, map_smul]; done)
  | (simp [dv, LinearMap.pow_apply, Function.iterate_succ_apply']; done)
  | (simp [dv, pow_succ']; exact (trivial : True))

theorem dv_add (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ c₁ : Fin d → LL) :
    dv W T e b (c₀ + c₁) = dv W T e b c₀ + dv W T e b c₁ := by
  simp only [dv, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem dv_smul (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (t : LL) (c₀ : Fin d → LL) :
    dv W T e b (t • c₀) = t • dv W T e b c₀ := by
  simp only [dv, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem dv_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) {ι : Type*} (s : Finset ι)
    (c₀ : ι → Fin d → LL) : dv W T e b (∑ i ∈ s, c₀ i) = ∑ i ∈ s, dv W T e b (c₀ i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using dv_smul W T e b 0 0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dv_add, ih]

theorem dv_eq_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ m, c₀ m • dv W T e b (Pi.single m 1) := by
  have h : c₀ = ∑ m, c₀ m • (Pi.single m 1 : Fin d → LL) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  rw [dv_sum]
  simp only [dv_smul]

theorem dvO_eq (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
  first
  | (unfold dvO; exact dv_eq_sum W T e b _)
  | (simp only [dvO]; exact dv_eq_sum W T e b _)

theorem dvO_single (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (k : Fin d) :
    dvO W T e b (Pi.single k 1) = dv W T e b (Pi.single k 1) := by
  rw [dvO_eq]
  simp [Pi.single_apply, apply_ite (algebraMap O LL), ite_smul]

theorem filS_anti (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u u' : ℤ} (h : u ≤ u') :
    FilS W T a s u' ≤ FilS W T a s u := by
  unfold FilS
  apply Submodule.map_mono
  apply inf_le_inf_right
  unfold FilCris
  apply inf_le_inf_left
  apply Submodule.comap_mono
  unfold FilV
  have hF : PD.Fil u' ≤ PD.Fil u := antitone_int_of_succ_le PD.Fil_anti h
  intro y hy
  rw [LinearMap.mem_range] at hy
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => exact LinearMap.mem_range.mpr ⟨a ⊗ₜ ⟨c.1, hF c.2⟩, by simp⟩
  | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw

theorem filS_zero_iff (T : LocLat G Qp LL O) (a : ZMod n) (u : ℤ) (x : T.V ⊗[Qp] B) :
    x ∈ FilS W T a 0 u ↔ x ∈ FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb a) := by
  unfold FilS
  simp [pow_zero, Submodule.map_id]
  try rfl

theorem filS_one_of (T : LocLat G Qp LL O) (a : ZMod n) (u : ℤ) (x : T.V ⊗[Qp] B)
    (hx : x ∈ FilS W T a 0 u) : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T (a + 1) 1 u := by
  rw [filS_zero_iff] at hx
  unfold FilS
  rw [pow_one, Nat.cast_one, add_sub_cancel_right]
  exact Submodule.mem_map_of_mem hx

theorem filS_zero_of (T : LocLat G Qp LL O) (a : ZMod n) (u : ℤ) (x : T.V ⊗[Qp] B)
    (hx : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T (a + 1) 1 u) : x ∈ FilS W T a 0 u := by
  rw [filS_zero_iff]
  unfold FilS at hx
  rw [pow_one, Nat.cast_one, add_sub_cancel_right, Submodule.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [← φVB_inj T hyx]
  exact hy

theorem repVV_smulA {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
    {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL} {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) {t : LetA O n} (ht : t ∈ W.AΔ) :
    RepVV W T c' e M Λ b sol (t • x) (fun k => algebraMap (LetA O n) W.EE t * f k) := by
  unfold RepVV at h ⊢
  obtain ⟨κ, κ', Hh, a, hH, ha, hIn⟩ := h
  refine ⟨κ, κ', Hh, fun k => t * a k, hH, fun k => ⟨mul_mem ht (ha k).1, ?_⟩, ?_⟩
  · dsimp only
    rw [map_mul, ← (ha k).2]
    ring
  · have he : lA W ^ κ' • (lA W ^ κ • Λ • (t • x) - ∑ k, (t * a k) • ((W.φD T) ^ e) (Hh k)) =
        t • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k))) := by
      simp only [smul_sub, Finset.smul_sum, smul_smul, mul_comm, mul_assoc, mul_left_comm]
    rw [he]
    exact Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.inMultiple_smul (ha := ht) (h := hIn)

section ThetaShiftProofs
variable {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ}

theorem arc_ty [NeZero n] (i : ZMod n) :
    (arcOf b w S η up size).ty i = if up i then .up (size i) else .down (size i) := rfl

theorem arc_thick [NeZero n] (i : ZMod n) : ((arcOf b w S η up size).ty i).thick := by
  rw [arc_ty]
  split <;> rfl

theorem arc_len_three_thick_letters [NeZero n] {c : ZMod n} (hlen : (arcOf b w S η up size).len c = 3) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c ∧ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) ∧
      ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
  unfold arcOf at hlen
  dsimp only at hlen
  have hpos : 0 < sInf {d : ℕ | 1 ≤ d ∧ ¬Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
    rw [hlen]; norm_num
  have hne := Nat.nonempty_of_pos_sInf hpos
  have h3 := Nat.sInf_mem hne
  rw [hlen] at h3
  have hlt : ∀ d : ℕ, 1 ≤ d → d < 3 → Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1) := by
    intro d hd1 hd3
    by_contra hT
    have hle := Nat.sInf_le
      (show d ∈ {d : ℕ | 1 ≤ d ∧ ¬Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} from ⟨hd1, hT⟩)
    rw [hlen] at hle
    omega
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hlt 1 le_rfl (by norm_num)
    rwa [show c - ((1 : ℕ) : ZMod n) + 1 = c by push_cast; ring] at h1
  · have h1 := hlt 2 (by norm_num) (by norm_num)
    rwa [show c - ((2 : ℕ) : ZMod n) + 1 = c - 1 by push_cast; ring] at h1
  · have h1 := h3.2
    rwa [show c - ((3 : ℕ) : ZMod n) + 1 = c - 2 by push_cast; ring] at h1

theorem arc_types [NeZero n] {c : ZMod n} (halt : Alt b η up size) (hD : up (c - 2) = false) :
    up (c - 1) = true ∧ up c = false := by
  unfold Alt at halt
  have h1 := (halt (c - 2)).1
  have h2 := (halt (c - 1)).1
  rw [show c - 2 + 1 = c - 1 by ring, hD] at h1
  rw [show c - 1 + 1 = c by ring] at h2
  have e1 : up (c - 1) = true := by simpa using h1
  refine ⟨e1, ?_⟩
  rw [e1] at h2
  simpa using h2

theorem lam_inner [NeZero n] {c : ZMod n} (hlen : (arcOf b w S η up size).len c = 3) :
    abelian₂ W (arcOf b w S η up size) (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n)) 2 =
      ps W 0 ^ (arcOf b w S η up size).h * ps W 1 ^ (arcOf b w S η up size).G₀ := by
  unfold abelian₂
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have hs0 : ∀ a : ZMod n, (arcOf b w S η up size).Hs a 2 0 = (arcOf b w S η up size).h := by
    intro a
    unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
    rw [if_neg]
    rintro (hc | hc)
    · simp only [arcOf] at hc
      split at hc <;> simp at hc
    · norm_num [arcOf] at hc
  have hs1 : ∀ a : ZMod n, (arcOf b w S η up size).Hs a 2 1 = (arcOf b w S η up size).G₀ := by
    intro a
    unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
    rw [if_pos (Or.inr (by simp [arcOf]))]
  rw [hs0, hs1]

end ThetaShiftProofs

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthFourDenominator
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_four_denominator [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hU : up (c - 2) = true)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (κ : ℕ) (x : O)
    (hx : InFr W c (ps W 1 ^ (size (c - 1) + S)) (nnDen W (arcOf b w S η up size) c)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ s : ℕ, (s : ℝ) ≤ max 1 ((size (c - 2) : ℝ) - ((size (c - 1) : ℝ) + S) / PD.p + 16 / 5 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size) + 1 ∧
      ((PD.p : ℕ) : O) ^ κ ∣ ((PD.p : ℕ) : O) ^ s * x := by
  obtain ⟨hp11, hset, h20w, h20η, -, -⟩ := hB
  obtain ⟨-, -, hη, -, -, hsz, -⟩ := hset
  have hl3 : (arcOf b w S η up size).len c = 3 := hlen
  have hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 3 := hlen
  have hne : ({d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} : Set ℕ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Nat.sInf_empty] at hlen'
    omega
  have hT2 : ¬ TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
    have hm := Nat.sInf_mem hne
    rw [hlen'] at hm
    have hm' : 1 ≤ 3 ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - ((3 : ℕ) : ZMod n) + 1) := hm
    have e : c - ((3 : ℕ) : ZMod n) + 1 = c - 2 := by push_cast; ring
    rw [e] at hm'
    exact hm'.2
  have hT0 : TruncatedSeriesCountingBounds.Thick b η size c := by
    by_contra hnt
    have hmem : (1 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
      refine ⟨le_refl 1, ?_⟩
      simpa using hnt
    have hle := Nat.sInf_le hmem
    rw [hlen'] at hle
    omega
  have hT1 : TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    by_contra hnt
    have hmem : (2 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
      refine ⟨by norm_num, ?_⟩
      have e : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
      rw [e]
      exact hnt
    have hle := Nat.sInf_le hmem
    rw [hlen'] at hle
    omega
  have hu1 : up (c - 1) = false := by
    have h := (halt (c - 2)).1
    rw [show c - 2 + 1 = c - 1 by ring, hU] at h
    simpa using h
  have hu0 : up c = true := by
    have h := (halt (c - 1)).1
    rw [sub_add_cancel, hu1] at h
    simpa using h
  have hh : TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold TruncatedSeriesCountingBounds.hB
    rw [if_pos ⟨c, hT0⟩]
  obtain ⟨s₁, hs1, hs1le, hsB, hnot⟩ := exists_s1_bound_choice PD.p b w S η (size c) (size (c - 1))
    (size (c - 2)) hp11 (Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (by unfold Formalism.MainNotions.N.Ln17.Sg; rw [hh]) hsm h20w h20η
    (by have := hη (c - 2); omega) (hsz (c - 2) hT2) hT1.1 hT0.2
  refine ⟨s₁, hs1le, ?_⟩
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₂ hW₂.1 hO hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hps : ∀ s, ps W s = (fun _ => Br.ι (Br.P.p s) : LetA O n) := by
    intro s
    induction s with
    | zero =>
      funext i
      simp [ps, qA, LocWach.π₀, lA, PhiData.p, Br.ι_X]
    | succ s ih =>
      have e : ps W (s + 1) = W.φA (ps W s) := by
        simp only [ps, pow_succ', AlgHom.mul_apply]
      rw [e, ih]
      funext i
      simp [LocWach.φA, letφ, PhiData.p, Function.iterate_succ_apply', Br.ι_φ]
  have hpsc : ∀ s, Br.ι (Br.P.p s) = ps W s c := fun s => by rw [hps s]
  have hX : Br.ι PowerSeries.X = ps W 0 c := hpsc 0
  have hCι : ∀ a : O, Br.ι (PowerSeries.C a) = PowerSeries.C a := fun a => Br.ι.commutes a
  have hN : nnDen W (arcOf b w S η up size) c = ps W 0 ^ size c * ps W 2 ^ size (c - 2) := by
    unfold nnDen prodTy
    rw [hl3]
    simp [Finset.prod_range_succ, arcOf, hu0, hu1, hU]
  have hf1 : InFr W c 1 (nnDen W (arcOf b w S η up size) c) f := by
    unfold InFF at hf
    exact hf.1
  obtain ⟨u₀, hu₀, h0⟩ := hf1
  obtain ⟨u, hu, h1⟩ := hx
  have key : algebraMap (LetA O n) W.EE (letE c * (((PD.p : ℕ) : LetA O n) ^ κ * u₀ -
      nnDen W (arcOf b w S η up size) c * algebraMap O (LetA O n) x -
      ps W 1 ^ (size (c - 1) + S) * u)) = 0 := by
    have hx' : algebraMap O W.EE x = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x) :=
      IsScalarTower.algebraMap_apply O (LetA O n) W.EE x
    have hl : lE W κ = ((PD.p : ℕ) : W.EE) ^ κ := rfl
    rw [hx', hl] at h1
    simp only [map_sub, map_mul, map_pow, map_natCast, map_one] at h0 h1 ⊢
    linear_combination h1 - ((PD.p : ℕ) : W.EE) ^ κ * h0
  have key2 : letE c * (((PD.p : ℕ) : LetA O n) ^ κ * u₀ -
      nnDen W (arcOf b w S η up size) c * algebraMap O (LetA O n) x -
      ps W 1 ^ (size (c - 1) + S) * u) = 0 := W.EE_inj (key.trans (map_zero _).symm)
  have key3 := congrFun key2 c
  rw [hN] at key3
  simp only [letE, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.natCast_apply, Pi.zero_apply,
    Pi.single_eq_same, one_mul, Pi.algebraMap_apply] at key3
  have hAC : algebraMap O (PowerSeries O) x = PowerSeries.C x := rfl
  try rw [hAC] at key3
  haveI : Fact (Nat.Prime PD.p) := ⟨PD.hp⟩
  obtain ⟨U₁, hU₁⟩ := Br.range u₀ hu₀ c
  obtain ⟨U₂, hU₂⟩ := Br.range u hu c
  refine den_of_rel Br.P hϖ (D := Br.P.p 2 ^ size (c - 2) * PowerSeries.X ^ size c)
    (U₁ := U₁) (U₂ := U₂) (B := size (c - 1) + S) (s₁ := s₁) ?_ ?_
  · apply Br.inj
    simp only [map_mul, map_sub, map_pow, map_one, mul_one, hCι, map_natCast]
    rw [hX, hpsc 2, hpsc 1, ← hU₁, ← hU₂]
    linear_combination -key3
  · intro hmem
    exact hnot (content_bound_level_ideal (P := Br.P) hϖ (size (c - 2)) (size c) (size (c - 1) + S) s₁
      (by have := hη (c - 2); omega) hs1 hsB hmem)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

