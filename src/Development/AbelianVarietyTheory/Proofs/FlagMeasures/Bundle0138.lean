import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0068
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0096
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0120
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0128
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0105

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBound
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.FixIdx

section

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem idx_inf_le (A B C W : Submodule R V) (hAB : A ≤ B) (hAW : A ≤ W) (h : idx B C ≠ 0) :
    idx A (C ⊓ W) ≠ 0 ∧ idx A (C ⊓ W) ≤ idx B C := by
  have e : idx A (C ⊓ W) = idx A C := by
    unfold idx
    rw [← AddSubgroup.inf_relIndex_right (C ⊓ W).toAddSubgroup, ← AddSubgroup.inf_relIndex_right C.toAddSubgroup]
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hAW hx.2⟩, hx.2⟩⟩
  rw [e]
  have hle : A.toAddSubgroup ≤ B.toAddSubgroup := hAB
  exact ⟨fun h0 => h (AddSubgroup.relIndex_eq_zero_of_le_right hle h0),
    AddSubgroup.relIndex_le_of_le_right hle h⟩

theorem gens_of_sup (A C D : Submodule R V) (hD : A ⊓ C ≤ D) (hDA : D ≤ A) (e : ℕ) (t : Finset V)
    (ht : t.card ≤ e) (h : A ⊔ C = C ⊔ Submodule.span R (t : Set V)) :
    ∃ t' : Finset V, t'.card ≤ e ∧ A = D ⊔ Submodule.span R (t' : Set V) := by
  have h1 : ∀ x : V, ∃ a : V, x ∈ t → a ∈ A ∧ x - a ∈ C := by
    intro x
    by_cases hx : x ∈ t
    · have : x ∈ A ⊔ C := by rw [h]; exact Submodule.mem_sup_right (Submodule.subset_span hx)
      obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 this
      exact ⟨a, fun _ => ⟨ha, by simpa using hc⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using h1
  have hsA : Submodule.span R ((t.image f : Finset V) : Set V) ≤ A := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact (hf x hx).1
  refine ⟨t.image f, Finset.card_image_le.trans ht, le_antisymm ?_ (sup_le hDA hsA)⟩
  have h2 : A ≤ C ⊔ Submodule.span R ((t.image f : Finset V) : Set V) := by
    refine le_trans (le_sup_left (b := C)) ?_
    rw [h]
    refine sup_le le_sup_left (Submodule.span_le.2 fun x hx => ?_)
    have : x = (x - f x) + f x := by abel
    rw [SetLike.mem_coe, this]
    exact Submodule.add_mem_sup (hf x hx).2
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)))
  intro x hx
  obtain ⟨c, hc, s, hs, rfl⟩ := Submodule.mem_sup.1 (h2 hx)
  refine Submodule.add_mem_sup (hD ⟨?_, hc⟩) hs
  simpa using A.sub_mem hx (hsA hs)

end

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in

theorem isLatMod_of_idx (A B : Submodule (𝓞 K) V) (S I : Submodule K V) (hA : IsLatMod A S I) (hBA : B ≤ A)
    (hI : rs (𝓞 K) I ≤ B) (h : idx A B ≠ 0) : IsLatMod B S I := by
  obtain ⟨⟨M, hM, hL⟩, hsp⟩ := hA
  refine ⟨⟨B ⊓ M, ?_, ?_⟩, le_antisymm ?_ ?_⟩
  · haveI : IsNoetherian (𝓞 K) M := isNoetherian_of_fg_of_noetherian _ hM
    exact isNoetherian_submodule.1 this _ inf_le_right
  · rw [inf_sup_assoc_of_le _ hI, ← hL]
    exact (inf_eq_left.2 hBA).symm
  · rw [← hsp]; exact Submodule.span_mono hBA
  · rw [← hsp, Submodule.span_le]
    intro x hx
    have h1 : (idx A B) • x ∈ B := AddSubgroup.nsmul_relIndex_mem B.toAddSubgroup (K := A.toAddSubgroup) hx
    have h2 : ((idx A B : K))⁻¹ • ((idx A B) • x) ∈ Submodule.span K (B : Set V) :=
      Submodule.smul_mem _ _ (Submodule.subset_span h1)
    rwa [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 h), one_smul] at h2

variable [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}

theorem radical (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) :
    II N.F N.F' ≤ wSp N.F N.F' ∧
      ∀ x ∈ wSp N.F N.F', (∀ y ∈ wSp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
  obtain ⟨-, -, -, -, -, -, hw, -, hPD, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have h2 : ∀ x ∈ N.Wt ⊔ II N.F N.F', ∀ y ∈ II N.F N.F', H.B y x = 0 := by
    intro x hx y hy
    rw [← hw] at hx
    rw [← H.herm, (mem_perp_iff H _ x).1 hx y (Submodule.mem_sup_left (Submodule.mem_sup_left hy.1)),
      star_zero]
  rw [hw]
  refine ⟨le_sup_right, fun x hx => ⟨fun hx0 => ?_, fun hxI y hy => h2 y hy x hxI⟩⟩
  obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
  have haa := hx0 a (Submodule.mem_sup_left ha)
  rw [map_add, LinearMap.add_apply, h2 a (Submodule.mem_sup_left ha) i hi, add_zero] at haa
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have ha0 : a = 0 := by
    by_contra hne
    have := hPD τ ⟨a, ha⟩ (fun h => hne (congrArg Subtype.val h))
    have e : GlobalTheory.Mass.hRes H.B.flip N.Wt ⟨a, ha⟩ ⟨a, ha⟩ = H.B a a := rfl
    rw [e, haa] at this
    simp at this
  rw [ha0, zero_add]; exact hi

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K) ∧ 0 < N.gI g Λ ∧ 0 < N.iI g Λ ∧ (N.gI g Λ : ℝ) * (N.iI g Λ : ℝ) ^ 2 * (N.bI Λ : ℝ) ^ 2 ≤ N.Del ∧ ((N.gI g Λ : ℝ) * N.iI g Λ ≤ N.Del) ∧ GenBy (flagPairDefinitePartLattice N.F N.F' Λ) (latLa N.F N.F' Λ (g : 𝓞 K)) N.j ∧ del H (latTh N.F N.F' Λ) = (N.gI g Λ : ℝ) * N.iI g Λ * N.NT ∧ IsLatMod (latTh N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨hb0, -, hDel, hbar⟩ := GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hΛ
  obtain ⟨hnB, -, h1L, hB, t, ht, hgen⟩ := GlobalTheory.T.flagPairInnerLattice_indices_and_generators K V H hK r N g Λ hg hΛ
  obtain ⟨hd0, -, -, hlat0, -⟩ := GlobalTheory.T.flagPairDefinitePartLattice_discriminant_eq_quotient K V H hK r N g Λ hg hΛ
  obtain ⟨hIW, hrad⟩ := radical hK N
  have hww : wSp N.F' N.F = wSp N.F N.F' := by
    unfold wSp V0
    rw [sup_comm N.F'.X, Set.pair_comm]
  have hn0 : idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) ≠ 0 := by
    intro h0
    rw [h0] at hnB
    simp only [Nat.cast_zero, zero_mul] at hnB
    linarith
  have hB0 : cardB N.F N.F' Λ ≠ 0 := by
    intro h0
    rw [h0] at hnB
    simp only [Nat.cast_zero, mul_zero] at hnB
    linarith
  have hThLa : latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K) := by
    intro x hx
    refine ⟨⟨⟨(h1L hx.1).2, by rw [hww]; exact hx.2⟩, ⟨(h1L hx.1).1, hx.2⟩⟩, ?_⟩
    obtain ⟨l, hl, i, hi, rfl⟩ := Submodule.mem_sup.1 hx.1.1
    refine Submodule.mem_sup.2 ⟨(l, l), ⟨⟨hl.1, hl.1⟩, ?_⟩, (i, i), ⟨hi.2, hi.1⟩, rfl⟩
    simp
  have hLa0 : latLa N.F N.F' Λ (g : 𝓞 K) ≤ flagPairDefinitePartLattice N.F N.F' Λ := fun x hx => hx.1.2
  have hLaL : latLa N.F N.F' Λ (g : 𝓞 K) ≤ latL N.F N.F' Λ ⊓ latL N.F' N.F Λ :=
    fun x hx => ⟨hx.1.2.1, hx.1.1.1⟩
  have hmul : N.iI g Λ * N.gI g Λ = idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) :=
    AddSubgroup.relIndex_mul_relIndex _ _ _ hThLa hLa0
  obtain ⟨hp0, hpn⟩ : idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) ≠ 0 ∧
      idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) ≤ idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) :=
    idx_inf_le _ _ _ _ inf_le_left inf_le_right hn0
  have hq0 : idx (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ) (lamOne N.F N.F' Λ) ≠ 0 := fun h0 =>
    hn0 (AddSubgroup.relIndex_eq_zero_of_le_right
      (show (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ).toAddSubgroup ≤ (latL N.F N.F' Λ).toAddSubgroup from
        fun x hx => hx.1) h0)
  have hiB : N.iI g Λ ≤ cardB N.F N.F' Λ :=
    (idx_inf_le _ _ _ (rs (𝓞 K) (wSp N.F N.F')) hLaL (hLa0.trans inf_le_right) hq0).2.trans hB
  have hi0 : N.iI g Λ ≠ 0 := fun h0 => hp0 (by rw [← hmul, h0, zero_mul])
  have hg0 : N.gI g Λ ≠ 0 := fun h0 => hp0 (by rw [← hmul, h0, mul_zero])
  have hmulR : (N.gI g Λ : ℝ) * N.iI g Λ = idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) := by
    rw [← hmul]; push_cast; ring
  have hmain : (N.gI g Λ : ℝ) * (N.iI g Λ : ℝ) ^ 2 * (N.bI Λ : ℝ) ^ 2 ≤ N.Del := by
    rw [← hDel, ← hnB, sq (N.iI g Λ : ℝ), ← mul_assoc, hmulR]
    have e1 : (idx (flagPairDefinitePartLattice N.F N.F' Λ) (latTh N.F N.F' Λ) : ℝ) ≤ idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) := by
      exact_mod_cast hpn
    have e2 : (N.iI g Λ : ℝ) ≤ cardB N.F N.F' Λ := by exact_mod_cast hiB
    gcongr
  have hITh : rs (𝓞 K) (II N.F N.F') ≤ latTh N.F N.F' Λ := by
    intro x hx
    refine ⟨⟨Submodule.mem_sup_right hx, ?_⟩, hIW hx⟩
    exact (mem_perp_iff H _ x).2 fun y hy => (mem_perp_iff H _ x).1 (hIW hx) y (Submodule.mem_sup_left hy)
  have hlat : IsLatMod (latTh N.F N.F' Λ) (wSp N.F N.F') (II N.F N.F') :=
    isLatMod_of_idx _ _ _ _ hlat0 (hThLa.trans hLa0) hITh hp0
  refine ⟨hThLa, Nat.pos_of_ne_zero hg0, Nat.pos_of_ne_zero hi0, hmain, le_trans ?_ hmain, ?_, ?_, hlat⟩
  · have e1 : (1 : ℝ) ≤ N.iI g Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi0
    have e2 : (1 : ℝ) ≤ N.bI Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0
    calc (N.gI g Λ : ℝ) * N.iI g Λ = (N.gI g Λ : ℝ) * (N.iI g Λ * 1) * 1 ^ 2 := by ring
      _ ≤ (N.gI g Λ : ℝ) * (N.iI g Λ * N.iI g Λ) * (N.bI Λ : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  · have h1 : lamOne N.F N.F' Λ ≤ latL N.F N.F' Λ := h1L.trans inf_le_left
    obtain ⟨t', ht', h'⟩ := ((GlobalTheory.Mass.LatticeGens.gens_and_count K V _ _ h1 hn0).2 N.j t ht hgen).2
      (flagPairDefinitePartLattice N.F N.F' Λ ⊔ lamOne N.F N.F' Λ) le_sup_right (sup_le inf_le_left h1)
    exact gens_of_sup _ _ _
      (le_trans (show flagPairDefinitePartLattice N.F N.F' Λ ⊓ lamOne N.F N.F' Λ ≤ latTh N.F N.F' Λ from
        fun x hx => ⟨hx.2, hx.1.2⟩) hThLa) hLa0 N.j t' ht' h'
  · rw [(DelScale.main K V H hK _ _ _ _ hIW hrad hlat0 hlat).2.2.1, hd0, hmulR]
    have : idx (latTh N.F N.F' Λ) (flagPairDefinitePartLattice N.F N.F' Λ) = 1 :=
      AddSubgroup.relIndex_eq_one.2 (hThLa.trans hLa0)
    rw [gidx, this]
    simp

end GlobalTheory.DegCnt.FixIdx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CasimirEigen

variable {n : ℕ}

theorem gelfVal_two_eq (χ : Fin n → ℂ) :
    gelfVal χ 2 = ∑ a, χ a * χ a - ∑ a, (Formalism.QuantumDeterminants.rhoStd n a : ℂ) * (Formalism.QuantumDeterminants.rhoStd n a : ℂ) := by
  rw [gelfVal_succ χ 1, pow_one]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul]
  have e : ∀ a : Fin n, (if a = b then χ a + ((n : ℂ) - 1) / 2 else if a < b then -1 else 0) =
      (if a = b then χ a + ((n : ℂ) - 1) / 2 else 0) - (if a ∈ Finset.Iio b then 1 else 0) := by
    intro a
    by_cases h1 : a = b
    · subst h1; simp
    · by_cases h2 : a < b <;> simp [h1, h2]
  simp only [Amat, Matrix.of_apply, e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, Fin.card_Iio, Formalism.QuantumDeterminants.rhoStd]
  push_cast
  ring

theorem gelfVal_two_eq_cvalR (ε : Fin n → Bool) (lam : Fin n → ℝ) :
    gelfVal (fun a => (lam a : ℂ)) 2 = ((cvalR ε lam : ℝ) : ℂ) := by
  rw [gelfVal_two_eq]
  simp only [cvalR, nsq, dot, Pi.add_apply, half_sum_roots_standard n ε, Formalism.QuantumDeterminants.rhoStd]
  push_cast
  rfl

theorem gelf_one_eq (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    gelf ε 1 f g = ∑ a, ∑ b, Eab ε a b (Eab ε b a f) g := by
  unfold gelf
  rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rfl

theorem inner_eabV {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {f : Matrix (Fin n) (Fin n) ℂ → H} (hf : SmoothOnGV ε f) (y : H) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Eab ε a b (fun x => ⟪y, f x⟫_ℂ) g = ⟪y, EabV ε a b f g⟫_ℂ := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have k1 := (rdVPair_of vector_right_derivative_extends n ε H ℂ (innerSL ℂ y) f _ g hf h1 hg).2
  have k2 := (rdVPair_of vector_right_derivative_extends n ε H ℂ (innerSL ℂ y) f _ g hf h2 hg).2
  simp only [innerSL_apply_apply, rdV_eq] at k1 k2
  simp only [Eab, Ec, EabV, EcV, inner_add_right, inner_smul_right, k1, k2]

theorem cas_eq_of_isZEigen : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Vs : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ Vs) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → ((∀ u, u ∈ Vs ↔ SmoothOnGV ε (fun g => σ g u)) ∧ GlRel E ∧ IsUnitary ε E ∧ (∀ X, inG ε X → ∀ u : Vs, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0) ∧ ∀ a b (u : Vs), ∀ g ∈ UJset ε, σ g (E a b u) = EabV ε a b (fun g => σ g u) g) → ∀ u : Vs, (∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g u⟫_ℂ)) → Cas E u = ((cvalR ε lam : ℝ) : ℂ) • u := by
  intro n ε H _ _ _ σ Vs E lam hσ ⟨hV, _, _, _, hE⟩ u hu
  have hone : ∀ v, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := GlobalTheory.SmoothVecMod.inUJ_one
  have key : ∀ (y : H) (a b : Fin n) (v : Vs) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Eab ε a b (fun x => ⟪y, σ x v⟫_ℂ) g = ⟪y, σ g (E a b v)⟫_ℂ := by
    intro y a b v g hg
    rw [hE a b v g hg]
    exact inner_eabV ((hV v).1 v.2) y a b hg
  apply Subtype.ext
  refine ext_inner_left ℂ fun y => ?_
  have h := (hu y).2 1 1 h1
  rw [gelf_one_eq, gelfVal_two_eq_cvalR ε lam] at h
  have e : ∀ a b : Fin n, Eab ε a b (Eab ε b a (fun x => ⟪y, σ x u⟫_ℂ)) 1 =
      ⟪y, ((E a b (E b a u) : Vs) : H)⟫_ℂ := by
    intro a b
    have := GlobalTheory.SmoothVecMod.eabV_congr (E := ℂ) (key y b a u) a b h1
    rw [eabV_eq, eabV_eq] at this
    rw [this, key y a b _ 1 h1, hone]
  simp only [e, hone] at h
  simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, inner_sum, Submodule.coe_smul,
    inner_smul_right]
  exact h

end GlobalTheory.CasimirEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramSchmidtLengths
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramFlag

open InnerProductSpace in

theorem sub_gs_mem {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) (a : Fin r) :
    f a - gramSchmidt ℂ f a ∈ Submodule.span ℂ (f '' Set.Iio a) := by
  have h := gramSchmidt_def'' (𝕜 := ℂ) f a
  have hs : f a - gramSchmidt ℂ f a = ∑ i ∈ Finset.Iio a,
      (⟪gramSchmidt ℂ f i, f a⟫_ℂ / (‖gramSchmidt ℂ f i‖ : ℂ) ^ 2) • gramSchmidt ℂ f i := by
    rw [sub_eq_iff_eq_add']
    exact h
  rw [hs, ← span_gramSchmidt_Iio (𝕜 := ℂ) f a]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩)

open InnerProductSpace in

theorem norm_gs_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) (a : Fin r)
    {w : E} (hw : w ∈ Submodule.span ℂ (f '' Set.Iio a)) : ‖gramSchmidt ℂ f a‖ ≤ ‖f a - w‖ := by
  have horth : ∀ v ∈ Submodule.span ℂ (f '' Set.Iio a), ⟪gramSchmidt ℂ f a, v⟫_ℂ = 0 := by
    intro v hv
    rw [← span_gramSchmidt_Iio (𝕜 := ℂ) f a] at hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact gramSchmidt_orthogonal (𝕜 := ℂ) f (ne_of_gt (Set.mem_Iio.1 hi))
    | zero => exact inner_zero_right _
    | add y y' _ _ hy hy' => rw [inner_add_right, hy, hy', add_zero]
    | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]
  have hy : (f a - gramSchmidt ℂ f a) - w ∈ Submodule.span ℂ (f '' Set.Iio a) :=
    Submodule.sub_mem _ (sub_gs_mem f a) hw
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (gramSchmidt ℂ f a) _ (horth _ hy)
  have heq : gramSchmidt ℂ f a + ((f a - gramSchmidt ℂ f a) - w) = f a - w := by abel
  rw [heq] at hpy
  nlinarith [norm_nonneg (gramSchmidt ℂ f a), norm_nonneg (f a - w),
    mul_self_nonneg ‖(f a - gramSchmidt ℂ f a) - w‖]

open InnerProductSpace in

theorem exists_upper {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) :
    ∃ u : UT r → ℂ, ∀ a, ∑ b, upper u b a • f b = gramSchmidt ℂ f a := by
  classical
  choose l hl hlx using fun a => (Finsupp.mem_span_image_iff_linearCombination ℂ).1 (sub_gs_mem f a)
  refine ⟨fun p => -(l p.1.2 p.1.1), fun a => ?_⟩
  have hz : ∀ b, a ≤ b → l a b = 0 := by
    intro b hab
    by_contra hne
    have hb := (Finsupp.mem_supported ℂ (l a)).1 (hl a) (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
    exact absurd (Set.mem_Iio.1 hb) (not_lt.2 hab)
  have hc : ∀ b, upper (fun p : UT r => -(l p.1.2 p.1.1)) b a = (if b = a then 1 else 0) - l a b := by
    intro b
    rcases lt_trichotomy b a with hba | hba | hba
    · simp [upper, hba, hba.ne]
    · subst hba
      simp [upper, hz b le_rfl]
    · simp [upper, not_lt.2 hba.le, hba.ne', hz b hba.le]
  have hsum := hlx a
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℂ (f i))] at hsum
  simp_rw [hc, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hsum, sub_sub_cancel]

theorem eucl_eq {N : ℕ} (v : Fin N → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq, eucl]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_norm_sq]

theorem gramSchmidt_lengths : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), ∀ x ∈ GG k r, ∃ u : UT r → ℂ, (∀ a : Fin r, eucl (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = lA k r z x a.castSucc ∧ 0 < lA k r z x a.castSucc) ∧ ∀ a a' : Fin r, a ≠ a' → star (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) ⬝ᵥ (∑ b, upper u b a' • (x⁻¹ *ᵥ bvec (eI k r b))) = 0 := by
  intro k r z x hx
  classical
  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    obtain ⟨-, hsq, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
    have h := congrArg Matrix.det hsq
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.2 ⟨_, h⟩
  have hxu : IsUnit x.det := ((Formalism.QuantumDeterminants.uHGroup _ _ hH).2.2 x hx).1
  let L : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin x⁻¹
  have hLapp : ∀ v, L v = WithLp.toLp 2 (x⁻¹ *ᵥ v) := fun v => rfl
  let e : Fin r → Fin (2 * r + k + 1) → ℂ := fun b => bvec (eI k r b)
  let F : Fin r → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun b => L (e b)
  have hLinj : Function.Injective L := by
    intro v w hvw
    rw [hLapp, hLapp] at hvw
    have h1 : x⁻¹ *ᵥ v = x⁻¹ *ᵥ w := congrArg WithLp.ofLp hvw
    have h2 := congrArg (fun t => x *ᵥ t) h1
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv x hxu] using h2
  have heinj : Function.Injective (eI k r) := fun a b h => Fin.ext (by have h' := congrArg Fin.val h; exact h')
  have hlie : LinearIndependent ℂ e := by
    have h0 := (Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp _ heinj
    convert h0 using 1
    funext b
    simp [e, bvec]
  have hli : LinearIndependent ℂ F := hlie.map' L (LinearMap.ker_eq_bot.2 hLinj)
  obtain ⟨u, hu⟩ := exists_upper F
  have hG : ∀ a, WithLp.toLp 2 (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = InnerProductSpace.gramSchmidt ℂ F a := by
    intro a
    have htl : ∀ v : Fin (2 * r + k + 1) → ℂ,
        WithLp.toLp 2 v = (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm v := fun v => rfl
    rw [← hu a, htl, map_sum]
    simp only [map_smul]
    rfl
  have hset : ∀ a : Fin r, (Set.range fun b : {b : Fin r // b.val < (a.castSucc : Fin (r + 1)).val} =>
      bvec (eI k r b.1)) = e '' Set.Iio a := by
    intro a
    ext v
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.1, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hlA : ∀ a : Fin r, lA k r z x a.castSucc = ‖InnerProductSpace.gramSchmidt ℂ F a‖ := by
    intro a
    have hf : Formalism.QuantumDeterminants.fvec k r z a.castSucc = e a := by
      rw [Formalism.QuantumDeterminants.fvec, dif_pos (show (a.castSucc : Fin (r + 1)).val < r from a.isLt)]
      rfl
    have hspan : Submodule.span ℂ (F '' Set.Iio a) = (Submodule.span ℂ (e '' Set.Iio a)).map L := by
      rw [Submodule.map_span, Set.image_image]
    unfold lA
    rw [hf, hset a]
    apply IsLeast.csInf_eq
    constructor
    · have hm := sub_gs_mem F a
      rw [hspan] at hm
      obtain ⟨y, hy, hyL⟩ := Submodule.mem_map.1 hm
      refine ⟨y, hy, ?_⟩
      rw [eucl_eq, ← hLapp, map_sub, hyL]
      show _ = ‖F a - (F a - InnerProductSpace.gramSchmidt ℂ F a)‖
      rw [sub_sub_cancel]
    · rintro t ⟨y, hy, rfl⟩
      rw [eucl_eq, ← hLapp, map_sub]
      exact norm_gs_le F a (w := L y) (by rw [hspan]; exact Submodule.mem_map_of_mem hy)
  refine ⟨u, fun a => ⟨by rw [eucl_eq, hG a, hlA a], ?_⟩, fun a a' haa' => ?_⟩
  · rw [hlA a]
    exact norm_pos_iff.2 (InnerProductSpace.gramSchmidt_ne_zero (𝕜 := ℂ) a hli)
  · rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, hG a, hG a']
    exact InnerProductSpace.gramSchmidt_orthogonal (𝕜 := ℂ) F haa'

end GlobalTheory.Amp.GramFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairScalarEqQuotIdealsNormLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt

theorem mem_ipow_one_iff_exists {K : Type} [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K)) (t : K) :
    t ∈ ipow 𝔞 1 ↔ ∃ a ∈ 𝔞, algebraMap (𝓞 K) K a = t := by
  unfold ipow
  rw [zpow_one]
  exact FractionalIdeal.mem_coeIdeal _

theorem exists_ideal_coeff {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L M : Submodule (𝓞 K) V) (z : V) (hML : M ≤ L)
    (hidx : idx L M ≠ 0) (hz : ∀ t : K, t • z ∈ L ↔ t ∈ (1 : Submodule (𝓞 K) K)) :
    ∃ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ idx L M ∧ ∀ t : K, t ∈ ipow 𝔞 1 ↔ t • z ∈ M := by
  let f : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V z
  have hf : ∀ a : 𝓞 K, f a = (algebraMap (𝓞 K) K a) • z := fun a => by
    simp only [f, LinearMap.toSpanSingleton_apply, algebraMap_smul]
  let 𝔞 : Ideal (𝓞 K) := M.comap f
  have hr : f.toAddMonoidHom.range ≤ L.toAddSubgroup := by
    rintro _ ⟨a, rfl⟩
    show f a ∈ L
    rw [hf, hz]
    exact Submodule.mem_one.2 ⟨a, rfl⟩
  have hN : Ideal.absNorm 𝔞 = M.toAddSubgroup.relIndex f.toAddMonoidHom.range := by
    rw [← AddSubgroup.index_comap, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hle : Ideal.absNorm 𝔞 ≤ idx L M := by
    rw [hN]; exact AddSubgroup.relIndex_le_of_le_right hr hidx
  have hne : Ideal.absNorm 𝔞 ≠ 0 := by
    rw [hN]
    exact fun h => hidx (AddSubgroup.relIndex_eq_zero_of_le_right hr h)
  refine ⟨𝔞, fun h => hne (by rw [h, Ideal.absNorm_bot]), hle, fun t => ?_⟩
  rw [mem_ipow_one_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← hf]; exact ha
  · intro ht
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 ((hz t).1 (hML ht))
    refine ⟨a, ?_, rfl⟩
    show f a ∈ M
    rw [hf]; exact ht

theorem c_eq_quot_ideals : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ N.Del ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ N.Del ∧ ∀ t : K, t * N.c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, -, hz, hz', -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  obtain ⟨hb, -, hD, h1⟩ := GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hΛ
  obtain ⟨hi, hi', hle, -⟩ := GlobalTheory.T.flagPairInnerLattice_indices_and_generators K V H hK r N g Λ hg hΛ
  set i := idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) with hidef
  have hi0 : i ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hB : cardB N.F N.F' Λ ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hiD : (i : ℝ) ≤ N.Del := by
    have hB1 : (1 : ℝ) ≤ cardB N.F N.F' Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hB
    have hb1 : (1 : ℝ) ≤ N.bI Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb
    have hb2 : (1 : ℝ) ≤ (N.bI Λ : ℝ) ^ 2 := one_le_pow₀ hb1
    have hi1 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    calc (i : ℝ) ≤ i * cardB N.F N.F' Λ := le_mul_of_one_le_right hi1 hB1
      _ = delBar N.F N.F' Λ := hi
      _ ≤ delBar N.F N.F' Λ * (N.bI Λ : ℝ) ^ 2 := le_mul_of_one_le_right (by linarith) hb2
      _ = N.Del := hD
  obtain ⟨𝔞, h0, hn, hm⟩ := exists_ideal_coeff _ _ N.F.z (hle.trans inf_le_left) hi0 hz
  obtain ⟨𝔞', h0', hn', hm'⟩ := exists_ideal_coeff _ _ N.F'.z (hle.trans inf_le_right) (hi' ▸ hi0) hz'
  refine ⟨𝔞, 𝔞', h0, h0', le_trans (by exact_mod_cast hn) hiD,
    le_trans (by exact_mod_cast hi' ▸ hn') hiD, fun t => ?_⟩
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) (by simpa using N.j_le)
  rw [hm, hm', hzz, mul_smul]

end GlobalTheory.DegCnt
end

