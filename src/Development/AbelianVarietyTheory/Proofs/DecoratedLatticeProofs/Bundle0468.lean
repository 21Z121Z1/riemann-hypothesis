import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OverProof

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SchrTheta

theorem rd_bounded : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), IsHalf p.e u →
      ∀ i j, (N : k) * rd α β u i j ∈ 𝒪[k] := GlobalTheory.T.exists_nat_mul_splitHalf_latticeCoordinates_integral

theorem nsmul_mem_of_rd_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∃ N : ℕ, 0 < N ∧ ∀ t : WO S T, IsHalf p.e t → (∀ i j, rd α β t i j ∈ 𝒪[k]) →
      N • t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := GlobalTheory.T.exists_nsmul_mem_homLattice_of_integral_frameCoords

theorem sb_uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (Ψ : Matrix n n' k → ℂ), Ψ ∈ SB (Matrix n n' k) →
    ∃ N : ℕ, 0 < N ∧ (∀ X Y : Matrix n n' k, (∀ i j, Y i j ∈ 𝒪[k]) → Ψ (X + (N : k) • Y) = Ψ X) ∧
      ∀ X, Ψ X ≠ 0 → ∀ i j, (N : k) * X i j ∈ 𝒪[k] := GlobalTheory.T.schwartzBruhat_matrix_uniformly_locallyConstant_bounded

section Rd
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {S T : HSp D}

theorem rd_add (α : Frame p S n') (β : Frame p T n) (t s : WO S T) : rd α β (t + s) = rd α β t + rd α β s := by
  unfold rd
  rw [Matrix.map_add p.pr (map_add p.pr), Matrix.mul_add, Matrix.add_mul]

theorem rd_nsmul (α : Frame p S n') (β : Frame p T n) (N : ℕ) (t : WO S T) : rd α β (N • t) = (N : k) • rd α β t := by
  unfold rd
  have : (N • t).map p.pr = (N : k) • t.map p.pr := by
    ext i j
    simp [Matrix.map_apply, nsmul_eq_mul, map_mul, map_natCast]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

end Rd

theorem isSBHalf_extFun : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k), IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (extFun α β Ψ) := by
  classical
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT Ψ hΨ
  obtain ⟨Na, hNa, ha⟩ := rd_bounded D k p n n' S T α β LS LT hS hT
  obtain ⟨Nb, hNb, hb⟩ := nsmul_mem_of_rd_int D k p n n' S T α β LS LT hS hT
  obtain ⟨Nc, hNc, hc1, hc2⟩ := sb_uniform k n n' Ψ hΨ
  have hhalf_add : ∀ {t u : WO S T}, IsHalf p.e u → (IsHalf p.e (t + u) ↔ IsHalf p.e t) := fun {t u} hu =>
    forall_congr' fun i => forall_congr' fun j => by
      rw [Matrix.add_apply, mul_add, hu i j, add_left_inj]
  have hhalf_nsmul : ∀ (N : ℕ) {t : WO S T}, IsHalf p.e t → IsHalf p.e (N • t) := fun N t ht i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, ht i j]
  refine ⟨fun t ht => ?_, Na * Nb * Nc, Nat.mul_pos (Nat.mul_pos hNa hNb) hNc, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by simp [extFun, h])
  · have hu' : IsHalf p.e ((Na * Nb * Nc) • u) := hhalf_nsmul _ hh
    unfold extFun
    rw [if_congr (hhalf_add hu') rfl rfl]
    split_ifs with h
    · rw [rd_add, rd_nsmul, show ((Na * Nb * Nc : ℕ) : k) • rd α β u = (Nc : k) • (((Nb : k) * Na) • rd α β u) by
        rw [smul_smul]; push_cast; ring_nf]
      refine hc1 _ _ fun i j => ?_
      rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
      exact mul_mem (by exact_mod_cast (algebraMap ℤ 𝒪[k] Nb).2) (ha u hu hh i j)
    · rfl
  · have hth : IsHalf p.e t := by
      by_contra h
      exact ht (by simp [extFun, h])
    have hΨt : Ψ (rd α β t) ≠ 0 := by simpa [extFun, hth] using ht
    have h1 := hb (Nc • t) (hhalf_nsmul _ hth) fun i j => by
      rw [rd_nsmul, Matrix.smul_apply, smul_eq_mul]
      exact hc2 _ hΨt i j
    rw [show (Na * Nb * Nc) • t = Na • (Nb • (Nc • t)) by rw [smul_smul, smul_smul, mul_assoc]]
    exact nsmul_mem h1 Na

theorem symplO_off_eq_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop),
    ¬ P p.v → ∀ u ∈ latO S T MS MT P, ∀ x : WO S T, (∀ i j, (p.e + cA D p.e) * x i j = x i j) → symplO S T u x = 0 := GlobalTheory.T.symplecticPairing_latticeAway_supportedAt_place_eq_zero

theorem extFun_latInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → p.UnitAA →
    ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT →
      extFun α β (latInd ΛS ΛT) = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator

theorem latInd_mem_SB : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT →
      latInd ΛS ΛT ∈ SB (Matrix n n' k) := GlobalTheory.T.indicator_hom_selfDual_components_schwartzBruhat

variable {D : D7}

theorem dualPair {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : AE D} {v : Pl D} (hs : IsSplitIdem D e) {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (heq : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) :
    let Λ := latO S T (LS : Set _) (LT : Set _) (· = v)
    (∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1) ∧
    (∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e) ∧
    (∀ y ∈ half S T (cA D e), (∀ u ∈ Λ ⊓ half S T e, ψ (symplO S T u y) = 1) → y ∈ Λ ⊓ half S T (cA D e)) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u) ∧
    (∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ) := by
  intro Λ
  have he := hs.1
  have hec := hs.2.1
  have he' : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * e = e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T LS LT hS.1.fg hT.1.fg fun w => w = v
  refine ⟨fun u hu y hy => (hdual u (infPart_half hε heε hu.2)).1 (latO_le_top _ hu.1) y (latO_le_top _ hy.1),
    mem_of_dual hε hdual he heε heε', fun y hy h => ?_, fun k hk => ?_, fun y hy => ?_⟩
  · refine mem_of_dual hε hdual he' heε' (by rwa [cA_cA]) y hy fun u hu => ?_
    rw [cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, idem_smul_mem hε he heε (latO_le_top _ hu), ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  · obtain ⟨k, hk, hky⟩ := exists_nsmul_mem_latO' hS.1 hT.1 y (infPart_half hε heε' hy)
    refine ⟨k, hk, ?_⟩
    have := (idem_smul_mem hε he' heε' hky).1
    rwa [smul_comm, (mem_half S T).1 hy] at this

theorem heisO_zero_fun (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u 0 = 0 := by
  funext t; simp [heisO]

theorem isLatVac_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) :
    IsLatVac (heisO ψ S T) Λ 0 :=
  ⟨fun u _ => heisO_zero_fun ψ S T _, fun _ _ u _ _ => heisO_zero_fun ψ S T u⟩

theorem isLatVac_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f + g) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have := (heisL S T ψ (2 • u)).map_add f g
    change heisO ψ S T (2 • u) (f + g) = _ at this
    rw [this]; change heisO ψ S T (2 • u) f + heisO ψ S T (2 • u) g = _; rw [hf.1 u hu, hg.1 u hu]
  · have := (heisL S T ψ u).map_add f g
    change heisO ψ S T u (f + g) = _ at this
    rw [this]; change heisO ψ S T u f + heisO ψ S T u g = _; rw [hf.2 e he u hu hh, hg.2 e he u hu hh]

theorem isLatVac_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Λ : AddSubgroup (WO S T)} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) : IsLatVac (heisO ψ S T) Λ (c • f) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have := (heisL S T ψ (2 • u)).map_smul c f
    change heisO ψ S T (2 • u) (c • f) = _ at this
    rw [this]; change c • heisO ψ S T (2 • u) f = _; rw [hf.1 u hu]
  · have := (heisL S T ψ u).map_smul c f
    change heisO ψ S T u (c • f) = _ at this
    rw [this]; change c • heisO ψ S T u f = _; rw [hf.2 e he u hu hh]

theorem isLatVac_heis {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {x : WO S T}
    (hx : ∀ u ∈ Λ, symplO S T u x = 0) {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f) :
    IsLatVac (heisO ψ S T) Λ (heisO ψ S T x f) := by
  have key : ∀ u ∈ Λ, heisO ψ S T u f = f → heisO ψ S T u (heisO ψ S T x f) = heisO ψ S T x f := by
    intro u hu h
    have := heisL_comm S T ψ u x f
    change heisO ψ S T u (heisO ψ S T x f) = ψ (symplO S T u x) • heisO ψ S T x (heisO ψ S T u f) at this
    rw [this, hx u hu, AddChar.map_zero_eq_one, one_smul, h]
  exact ⟨fun u hu => key _ (nsmul_mem hu 2) (hf.1 u hu), fun e he u hu hh => key u hu (hf.2 e he u hu hh)⟩

theorem overBasic : ∀ D : D7, GlobalTheory.FinPl.OverBasic D := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ S T α β LS LT hS hT f₀ hvac
  obtain ⟨ε, hε, heq⟩ := p.above
  have hs := p.split
  have he := hs.1
  have hec := hs.2.1
  have he' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have hs' : IsSplitIdem D (cA D p.e) :=
    ⟨he', by rw [cA_cA, mul_comm, hec], p.v, ε, hε, by rw [cA_cA, add_comm, heq]⟩
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by rw [← heq]; linear_combination he' + hec
  obtain ⟨hLL', hX, hY, hfin, hden⟩ := dualPair hψ hS hT hs hε heq
  set Λ := latO S T (LS : Set _) (LT : Set _) (· = p.v) with hΛ
  have hex : ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e Λ 1 f₀ Tm :=
    exists_placeModel ψ hec Λ hLL' hX hY hfin one_ne_zero f₀
      (fun u hu => hvac.2.2 p.e hs u hu.1 ((isHalf_iff S T).2 hu.2))
      (fun u hu => hvac.2.2 _ hs' u hu.1 ((isHalf_iff S T).2 hu.2))
  obtain ⟨Tm, hTm⟩ := hex
  have huniq := fun {T₁ T₂} (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e Λ 1 f₀ T₁)
      (h₂ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e Λ 1 f₀ T₂) {Φ} (hΦ : IsSBHalf p.e Λ Φ) =>
    placeModel_unique_of_dual ψ Λ hLL' hX hfin hden h₁ h₂ hΦ
  have hfX : ∀ x ∈ half S T p.e, ∀ i j, (p.e + cA D p.e) * x i j = x i j := fun x hx i j => by
    have h1 := (isHalf_iff S T).2 hx i j
    linear_combination (1 - cA D p.e) * h1 + x i j * hec
  have hfY : ∀ y ∈ half S T (cA D p.e), ∀ i j, (p.e + cA D p.e) * y i j = y i j := fun y hy i j => by
    have h1 := (isHalf_iff S T).2 hy i j
    linear_combination (1 - p.e) * h1 + y i j * hec
  refine ⟨fun Ψ hΨ => ?_, fun Ψ f hf => ?_, fun hU ΛS ΛT hLS hLT => ?_⟩
  · have hΦ := isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
    refine ⟨Tm (extFun α β Ψ), ⟨hS, hT, hvac, hΨ, ⟨Tm, hTm⟩, fun T' hT' => huniq hTm hT' hΦ⟩, fun f hf => ?_⟩
    exact hf.2.2.2.2.2 Tm hTm
  · have hΦ := isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hf.2.2.2.1
    have hfe : f = Tm (extFun α β Ψ) := hf.2.2.2.2.2 Tm hTm
    rw [hfe]
    refine ⟨placeModel_induction ψ Λ hLL' hX hfin hden hTm (IsThetaFunO ψ S T) GlobalTheory.WeilVacMove.isTheta_zero
      (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) (fun c _ => GlobalTheory.WeilVacMove.isTheta_smul c)
      (fun x hx g hg => isTheta_heis_fin hψ hg (infPart_half hε heε hx))
      (fun y hy g hg => isTheta_heis_fin hψ hg (infPart_half hε heε' hy))
      hvac.1 hΦ, fun MS MT P hP hv => ⟨?_, ?_⟩⟩
    · exact placeModel_induction ψ Λ hLL' hX hfin hden hTm (IsThetaFunO ψ S T) GlobalTheory.WeilVacMove.isTheta_zero
        (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) (fun c _ => GlobalTheory.WeilVacMove.isTheta_smul c)
        (fun x hx g hg => isTheta_heis_fin hψ hg (infPart_half hε heε hx))
        (fun y hy g hg => isTheta_heis_fin hψ hg (infPart_half hε heε' hy))
        hvac.1 hΦ
    · have hv2 : IsLatVac (heisO ψ S T) (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) P) f₀ := hv.2
      exact placeModel_induction ψ Λ hLL' hX hfin hden hTm
        (IsLatVac (heisO ψ S T) (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) P)) (isLatVac_zero ψ S T _)
        (fun _ _ => isLatVac_add) (fun c _ => isLatVac_smul c)
        (fun x hx g hg => isLatVac_heis (fun u hu => symplO_off_eq_zero D k p S T _ _ P hP u hu x (hfX x hx)) hg)
        (fun y hy g hg => isLatVac_heis (fun u hu => symplO_off_eq_zero D k p S T _ _ P hP u hu y (hfY y hy)) hg)
        hv2 hΦ
  · have hE := extFun_latInd D k p n n' S T α β LS LT hS hT hU ΛS ΛT hLS hLT
    refine ⟨hS, hT, hvac, latInd_mem_SB D k p n n' S T α β LS LT hS hT ΛS ΛT hLS hLT, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
    have := hT'.vac
    rw [one_smul] at this
    change f₀ = T' (extFun α β (latInd ΛS ΛT))
    rw [hE, this]

end GlobalTheory.FinPl.OverProof

theorem GlobalTheory.FinPl.overBasic : ∀ D : D7, GlobalTheory.FinPl.OverBasic D := GlobalTheory.FinPl.OverProof.overBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBesselCoreMatrixEqBlockDiagonalOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl.CoreMat

theorem mt_emb_mulVec_ratV_vecB {D : D7} {ρ : ℕ} (B : BesLev D ρ) (κ : GA D B.A) :
    mt B.V₀ (B.o.emb (κ, 1)) *ᵥ ratV (vecB B.o B.ζ) = ratV (vecB B.o B.ζ) := by
  have hv : ratV (vecB B.o B.ζ) = B.o.jB *ᵥ ratV B.ζ :=
    funext fun i => RingHom.map_mulVec (incA D) B.o.iB B.ζ i
  have hB : mt B.V₀ (B.o.emb (κ, 1)) ⬝ B.o.jB = B.o.jB := by
    rw [B.o.emb_jB]
    have h1 : mt B.L (1 : GA D B.L) = 1 := by simp [Formalism.L2.Theta.mt]
    rw [h1, Matrix.mul_one]
  rw [hv, Matrix.mulVec_mulVec, hB]

theorem coreMat : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (β : GlobalTheory.FinPl.Frame p B.A n) (β₀ : GlobalTheory.FinPl.Frame p B.V₀ (n ⊕ Fin 1)), GlobalTheory.FinPl.IsSumFrame B.o B.ζ β β₀ → ∀ (κ : GA D B.A) (g : GL n k), (mt B.A κ).map p.pr = β.b * g.val * β.b' → (mt B.V₀ (B.o.emb (κ, 1))).map p.pr = β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by
  intro D k _ _ _ _ p n _ _ ρ B β β₀ hS κ g hg
  have hA : mt B.V₀ (B.o.emb (κ, 1)) ⬝ B.o.jA = B.o.jA ⬝ mt B.A κ := B.o.emb_jA κ 1
  have hv := mt_emb_mulVec_ratV_vecB B κ
  have key : (mt B.V₀ (B.o.emb (κ, 1))).map p.pr * β₀.b = β₀.b * (GlobalTheory.RootEx.embX 1 g).val := by
    rw [hS]
    have hX : ((GlobalTheory.RootEx.embX 1 g).val : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k) = fromBlocks g.val 0 0 1 := rfl
    rw [hX]
    rw [Matrix.mul_fromCols, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, Matrix.mul_zero, zero_add,
      Matrix.mul_one]
    congr 1
    · rw [← Matrix.mul_assoc, ← Matrix.map_mul, hA, Matrix.map_mul, Matrix.mul_assoc, hg, Matrix.mul_assoc,
        Matrix.mul_assoc, Matrix.mul_assoc, β.b'b, Matrix.mul_one]
    · ext i j
      have := congrFun hv i
      simp only [Matrix.mul_apply, replicateCol_apply, Matrix.map_apply, ← map_mul, ← map_sum]
      rw [← this]
      rfl
  calc (mt B.V₀ (B.o.emb (κ, 1))).map p.pr
      = (mt B.V₀ (B.o.emb (κ, 1))).map p.pr * β₀.b * β₀.b' := by rw [Matrix.mul_assoc, β₀.bb', Matrix.mul_one]
    _ = β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by rw [key]

end GlobalTheory.FinPl.CoreMat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjFrameMatrixReindex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

theorem GlobalTheory.Lev.conj_frameMatrix_submatrix_equiv {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (βF : Matrix (Fin N) Y k) (γF : Matrix Y (Fin N) k) (hβγ : βF * γF = 1) (hγβ : γF * βF = 1) (σ : Fin N ≃ Y)
    (gk : GL Y k) (Pi Bi B P G X Xi : Matrix (Fin N) (Fin N) k) (hG : G = βF * gk.val * γF) (hX : X = Pi * (Bi * G * B) * P)
    (hBP : B * P = βF.submatrix id σ) (hBB : Bi * B = 1) (hPP : Pi * P = 1) (hXi : Xi * X = 1) :
    X = gk.val.submatrix σ σ ∧ Xi = (gk⁻¹).val.submatrix σ σ := by
  subst hG
  have hMM : βF.submatrix id σ * γF.submatrix σ id = 1 := by
    rw [Matrix.submatrix_mul_equiv βF γF id σ id, hβγ, Matrix.submatrix_id_id]
  have hN : Pi * Bi = γF.submatrix σ id := by
    have h1 : (Pi * Bi) * βF.submatrix id σ = 1 := by
      rw [← hBP]
      calc Pi * Bi * (B * P) = Pi * ((Bi * B) * P) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hBB, Matrix.one_mul, hPP]
    calc Pi * Bi = (Pi * Bi) * (βF.submatrix id σ * γF.submatrix σ id) := by rw [hMM, Matrix.mul_one]
      _ = γF.submatrix σ id := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hX' : X = gk.val.submatrix σ σ := by
    have e0 : X = (Pi * Bi) * (βF * gk.val * γF) * (B * P) := by rw [hX]; simp only [Matrix.mul_assoc]
    rw [e0, hN, hBP]
    have e1 : γF.submatrix σ id * (βF * gk.val * γF) = (γF * (βF * gk.val * γF)).submatrix σ id := by
      rw [Matrix.submatrix_mul γF _ σ id id Function.bijective_id, Matrix.submatrix_id_id]
    rw [e1, ← Matrix.submatrix_mul _ βF σ id σ Function.bijective_id]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hγβ, Matrix.one_mul, Matrix.mul_assoc, hγβ, Matrix.mul_one]
  refine ⟨hX', ?_⟩
  have hR : gk.val.submatrix σ σ * (gk⁻¹).val.submatrix σ σ = 1 := by
    rw [Matrix.submatrix_mul_equiv _ _ σ σ σ, Units.mul_inv, Matrix.submatrix_one_equiv]
  calc Xi = Xi * (gk.val.submatrix σ σ * (gk⁻¹).val.submatrix σ σ) := by rw [hR, Matrix.mul_one]
    _ = (gk⁻¹).val.submatrix σ σ := by rw [← Matrix.mul_assoc, ← hX', hXi, Matrix.one_mul]

set_option maxHeartbeats 400000 in
theorem GlobalTheory.Lev.conj_frame_matrix : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → (∀ i j, q.prF he ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val i j) = gk.val (σ i) (σ j)) ∧ ∀ i j, q.prF he (((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹).val i j) = (gk⁻¹).val (σ i) (σ j) := by
  intro D k _ _ _ _ q PP he V β Y _ _ F σ b hmov g gk hloc
  have hm : (mt V (b⁻¹ * g * b)).map q.pr = (mt V b⁻¹).map q.pr * (mt V g).map q.pr * (mt V b).map q.pr := by
    rw [mt_mul, mt_mul, Matrix.map_mul, Matrix.map_mul]
  have hc : ∀ A : Matrix (Fin V.rank) (Fin V.rank) (AE D), (A.map (toEAf D)).map (q.prF he) = A.map q.pr := by
    intro A; ext i j; simp [Matrix.map_apply, GlobalTheory.FinPl.SplitPt.prF_toEAf]
  have hX : (β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val.map (q.prF he) =
      (β⁻¹).val.map (q.prF he) * (mt V (b⁻¹ * g * b)).map q.pr * β.val.map (q.prF he) := by
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, ← hc]
    rfl
  rw [hm] at hX
  obtain ⟨bt, hbt⟩ : ∃ bt : Matrix (Fin V.rank) (Fin V.rank) (AE D), bt.map (toEAf D) = β.val := by
    choose s hs using fun i j => GlobalTheory.ResLoc.toEAf_surj (D := D) (β.val i j)
    exact ⟨Matrix.of s, by ext i j; simp [hs]⟩
  have hM : ((mt V b * bt).map q.pr) = F.β.submatrix id σ := hmov bt hbt
  have hBP : (mt V b).map q.pr * β.val.map (q.prF he) = F.β.submatrix id σ := by
    rw [← hM, ← hbt, hc, Matrix.map_mul]
  have hBB : (mt V b⁻¹).map q.pr * (mt V b).map q.pr = 1 := by
    have h := mt_mul_inv V b⁻¹
    rw [inv_inv] at h
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPP : (β⁻¹).val.map (q.prF he) * β.val.map (q.prF he) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (mt V g).map q.pr = F.β * gk.val * F.γ := hloc.2
  have hXi : ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹).val.map (q.prF he) *
      (β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val.map (q.prF he) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨h1, h2⟩ := GlobalTheory.Lev.conj_frameMatrix_submatrix_equiv F.β F.γ F.βγ F.γβ σ gk _ _ _ _ _ _ _ hG hX hBP hBB hPP hXi
  exact ⟨fun i j => congrArg (fun M => M i j) h1, fun i j => congrArg (fun M => M i j) h2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjugateStabilizerKeepsMovedFrameLatt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.StMoves

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem int_mul {m n p : Type} [Fintype n] {A : Matrix m n k} {B : Matrix n p k} (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) : ∀ i j, (A * B) i j ∈ 𝒪[k] := fun i j =>
  Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)

theorem int_one_sub {m a b : Type} [DecidableEq m] (f : a → m) (g' : b → m) :
    ∀ i j, ((1 : Matrix m m k).submatrix f g') i j ∈ 𝒪[k] := fun i j => by
  rw [submatrix_apply, one_apply]
  split_ifs
  exacts [Subring.one_mem _, Subring.zero_mem _]

theorem mt_mul (S : HSp D) (a b : GA D S) : mt S (a * b) = mt S a * mt S b := by simp [Formalism.L2.Theta.mt]

theorem alg_frame {n : ℕ} {Y R A' : Type} [Fintype Y] [DecidableEq Y] [CommRing R] [CommRing A'] (pr : R →+* k) (toE : R →+* A')
    (π : A' →+* k) (hmap : ∀ x, π (toE x) = pr x) (mg mt' mh b : Matrix (Fin n) (Fin n) R) (βv I : Matrix (Fin n) (Fin n) A')
    (Fβ : Matrix (Fin n) Y k) (Fγ : Matrix Y (Fin n) k) (e : Y ≃ Fin n) (hγβ : Fγ * Fβ = 1) (hb : b.map toE = βv)
    (hmv : (mt' * b).map pr = Fβ.submatrix id e.symm) (hg1 : mg * mt' = mt' * mh) (hfin : mh.map toE * βv = βv * I) :
    Fγ * mg.map pr * Fβ = (1 : Matrix Y Y k).submatrix id e.symm * I.map π * (1 : Matrix Y Y k).submatrix e.symm id := by
  have hm : ∀ N : Matrix (Fin n) (Fin n) R, (N.map toE).map π = N.map pr := fun N => Matrix.ext fun _ _ => hmap _
  have eq2 : mg.map pr * Fβ.submatrix id e.symm = Fβ.submatrix id e.symm * I.map π := by
    rw [← hmv, ← Matrix.map_mul, ← Matrix.mul_assoc, hg1, Matrix.mul_assoc, Matrix.map_mul, ← hm (mh * b), Matrix.map_mul,
      hb, hfin, Matrix.map_mul, ← hb, hm, ← Matrix.mul_assoc, ← Matrix.map_mul]
  have eq1 : Fβ = Fβ.submatrix id e.symm * (1 : Matrix Y Y k).submatrix e.symm id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_one]; rfl
  have eq3 : Fγ * Fβ.submatrix id e.symm = (1 : Matrix Y Y k).submatrix id e.symm := by
    rw [← hγβ]
    exact Matrix.submatrix_mul_equiv Fγ Fβ id (Equiv.refl _) e.symm
  conv_lhs => rw [eq1]
  rw [Matrix.mul_assoc Fγ, ← Matrix.mul_assoc _ (Fβ.submatrix id e.symm), eq2, ← eq3]
  simp only [Matrix.mul_assoc]

theorem int_of_mem_St (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y)
    (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank)
    (hM : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm))
    (g : GA D S) (hg : Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β) :
    ∀ i j, (F.γ * (mt S g).map q.pr * F.β) i j ∈ 𝒪[k] := by
  obtain ⟨Y0, hY0⟩ := hg
  obtain ⟨π, h1, -, h3, -⟩ := GlobalTheory.LocMod.LevBack.exists_chart q hq
  have hb' : (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map (toEAf D) = β.val :=
    Matrix.ext fun _ _ => GlobalTheory.LocMod.LevBack.toEAf_finEmb _
  have hmv : (mt S t * β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map q.pr = F.β.submatrix id e.symm := hM _ hb'
  have hZi : ∀ i j, ((Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val.map π) i j ∈ 𝒪[k] := fun i j => h3 (Y0.val i j)
  have hmap : ∀ N : Matrix (Fin S.rank) (Fin S.rank) (AE D), (N.map (toEAf D)).map π = N.map q.pr :=
    fun N => Matrix.ext fun _ _ => h1 _
  have hfin : Lev.finE S (t⁻¹ * g * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0 := by
    rw [← hY0]
    simp [Formalism.L2.DIV.frGL]
  have hfin' : (mt S (t⁻¹ * g * t)).map (toEAf D) * β.val = β.val * (Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val := by
    have := congrArg Units.val hfin
    rwa [Units.val_mul, Units.val_mul] at this
  have hg1 : mt S g * mt S t = mt S t * mt S (t⁻¹ * g * t) := by
    rw [← mt_mul, ← mt_mul]; congr 1; group
  rw [alg_frame q.pr (toEAf D) π h1 (mt S g) (mt S t) (mt S (t⁻¹ * g * t)) (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)) β.val
    (Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val F.β F.γ e F.γβ hb' hmv hg1 hfin']
  exact int_mul (int_mul (int_one_sub _ _) hZi) (int_one_sub _ _)

open scoped Pointwise in

theorem moves_of_mem_St : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y), (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) → ∀ (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm) → ∀ g : GA D S, Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β → GlobalTheory.FinPl.Moves S g L L (· = q.v) := by
  intro D k _ _ _ _ q PP hq S L hL Y _ _ F hF t β e hM g hg
  obtain ⟨gl, h1, h2⟩ := GlobalTheory.GlEmbed.exists_gl D k q S Y F.β F.γ F.βγ F.γβ
  have hlat : (⟨F.β, F.γ, F.βγ, F.γβ, gl, h1, h2⟩ : GlobalTheory.FinPl.Frame q S Y).IsLat L (GlobalTheory.StepData.latOf 1) := fun x => by
    rw [GlobalTheory.StepData.mem_latOf_one]; exact hF x
  refine (GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes D k q S Y _ L _ hL hlat g).2 ?_
  have hA : ∀ i j, (GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g).val i j ∈ 𝒪[k] :=
    int_of_mem_St q hq S F t β e hM g hg
  have hAi : ∀ i j, ((GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g)⁻¹).val i j ∈ 𝒪[k] := by
    rw [← map_inv]
    refine int_of_mem_St q hq S F t β e hM g⁻¹ ?_
    have : t⁻¹ * g⁻¹ * t = (t⁻¹ * g * t)⁻¹ := by group
    rw [this, map_inv]
    exact Subgroup.inv_mem _ hg
  have hK : GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g ∈ GlobalTheory.StepData.stabLat 1 := by
    rw [GlobalTheory.StepData.mem_stabLat, inv_one, one_mul, mul_one]
    exact GlobalTheory.StepData.mem_KO.2 ⟨hA, hAi⟩
  have hs := GlobalTheory.StepData.mem_stabLat_iff.1 hK
  set A := GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g
  ext y
  conv_rhs => rw [← hs]
  change (∃ x, x ∈ GlobalTheory.StepData.latOf 1 ∧ A • x = y) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (GlobalTheory.StepData.mulVec_mem_latOf A).2 hx
  · intro hy
    refine ⟨A⁻¹ • y, (GlobalTheory.StepData.mulVec_mem_latOf A).1 ?_, smul_inv_smul _ _⟩
    have : A.val *ᵥ (A⁻¹ • y) = y := smul_inv_smul A y
    rwa [this]

end GlobalTheory.LocMod.StMoves
end
end

