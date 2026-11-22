import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0727
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0472
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoSegmentGenericSub
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.BZSeg.TwoSegWhit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem arith {Δ Δ' : Segment k} (hpre : Δ'.Precedes Δ) :
    ∃ j : ℕ, 0 < j ∧ j ≤ Δ'.len ∧ Δ'.len < j + Δ.len ∧ Δ.first = Δ'.first.nu (j : ℂ) := by
  obtain ⟨⟨⟨Γ, hΓ⟩, -, h2⟩, j, hj, e⟩ := hpre
  have hc : 0 < Δ'.first.1 := Δ'.isCusp_first.1
  have inj : ∀ a b : ℕ, Δ'.first.nu (a : ℂ) = Δ'.first.nu (b : ℂ) → a = b :=
    fun a b h => (IrrGL.nu_natCast_inj hc).1 h
  have memΔ' : ∀ n : ℕ, Δ'.first.nu (n : ℂ) ∈ Δ'.carrier ↔ n < Δ'.len := fun n =>
    ⟨fun h => by
      obtain ⟨a, ha, h⟩ := Segment.mem_carrier.1 h
      rwa [← inj _ _ h], fun h => Segment.mem_carrier.2 ⟨n, h, rfl⟩⟩
  have memΔ : ∀ n : ℕ, Δ'.first.nu (n : ℂ) ∈ Δ.carrier ↔ j ≤ n ∧ n < j + Δ.len := fun n => by
    constructor
    · intro h
      obtain ⟨a, ha, h⟩ := Segment.mem_carrier.1 h
      rw [e, IrrGL.nu_nu] at h
      have h' := inj (j + a) n (by push_cast; exact h)
      omega
    · rintro ⟨h1, h3⟩
      refine Segment.mem_carrier.2 ⟨n - j, by omega, ?_⟩
      rw [e, IrrGL.nu_nu]
      congr 1
      rw [← Nat.cast_add]
      congr 1
      omega
  have hρ : Δ'.first ∈ Γ.carrier := by
    rw [hΓ]
    exact Or.inl (Segment.mem_carrier.2 ⟨0, Δ'.len_pos, by simp⟩)
  have hΓ0 : Γ.first ∈ Γ.carrier := Segment.mem_carrier.2 ⟨0, Γ.len_pos, by simp⟩
  have hcΓ : ∃ c : ℕ, Γ.first = Δ'.first.nu (c : ℂ) := by
    rw [hΓ] at hΓ0
    rcases hΓ0 with h | h
    · obtain ⟨a, -, h⟩ := Segment.mem_carrier.1 h
      exact ⟨a, h.symm⟩
    · obtain ⟨a, -, h⟩ := Segment.mem_carrier.1 h
      refine ⟨j + a, ?_⟩
      rw [← h, e, IrrGL.nu_nu]
      push_cast
      rfl
  obtain ⟨c, hcΓ⟩ := hcΓ
  have hΓf : Γ.first = Δ'.first := by
    obtain ⟨a, -, h⟩ := Segment.mem_carrier.1 hρ
    rw [hcΓ, IrrGL.nu_nu] at h
    have h' := inj (c + a) 0 (by push_cast; simpa using h)
    have hc0 : c = 0 := by omega
    rw [hcΓ, hc0]
    simp
  have memΓ : ∀ n : ℕ, Δ'.first.nu (n : ℂ) ∈ Γ.carrier ↔ n < Γ.len := fun n =>
    ⟨fun h => by
      obtain ⟨a, ha, h⟩ := Segment.mem_carrier.1 h
      rw [hΓf] at h
      rwa [← inj _ _ h], fun h => Segment.mem_carrier.2 ⟨n, h, by rw [hΓf]⟩⟩
  have key : ∀ n : ℕ, n < Γ.len ↔ n < Δ'.len ∨ (j ≤ n ∧ n < j + Δ.len) := fun n => by
    rw [← memΓ, hΓ, Set.mem_union, memΔ', memΔ]
  have hlp := Δ.len_pos
  refine ⟨j, hj, ?_, ?_, e⟩
  · by_contra hlt
    have h1 := (key (j + Δ.len - 1)).2 (Or.inr ⟨by omega, by omega⟩)
    have h3 := (key Δ'.len).1 (by omega)
    omega
  · by_contra hge
    refine h2 fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
    rw [e, IrrGL.nu_nu]
    have h3 := (memΔ' (j + a)).2 (by omega)
    push_cast at h3
    exact h3

end GlobalTheory.CompanionTheory.BZSeg.TwoSegWhit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentMapContinuousAdditive
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelUnip

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (b c : hermA D n) : nb (b + c) = nb b * nb c := by
  apply mat_inj
  rw [mat_mul, h, h, h, submatrix_fromBlocks_mul]
  simp [add_comm]

theorem nb_zero {nb : hermA D n → G D n} (h : IsNMap nb) : nb 0 = 1 := by
  apply mat_inj
  rw [mat_one, h]
  exact block_matrix_one

theorem nb_neg {nb : hermA D n → G D n} (h : IsNMap nb) (b : hermA D n) : nb (-b) = (nb b)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← nb_add h, neg_add_cancel, nb_zero h])

theorem continuous_blk (f : hermA D n → Mx D n n) (hf : Continuous f) :
    Continuous fun b : hermA D n => (blk4 1 (f b) 0 1 : Mx D (n + n) (n + n)) := by
  unfold blk4
  exact (Continuous.matrix_fromBlocks continuous_const hf continuous_const continuous_const).matrix_submatrix _ _

theorem nb_continuous {nb : hermA D n → G D n} (h : IsNMap nb) : Continuous nb := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  rw [(isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_blk _ continuous_subtype_val).congr fun b => (h b).symm
  · refine (continuous_blk (fun b => -b.1) continuous_subtype_val.neg).congr fun b => ?_
    have e : (matHom (AF D.host.F) D.sp.cm.sig (Jst D n) (nb b))⁻¹ = matHom (AF D.host.F) D.sp.cm.sig (Jst D n) (nb (-b)) := by
      rw [nb_neg h, map_inv]
    simp only [Function.comp_apply]
    rw [e]
    exact (h (-b)).symm

theorem nb_rat {nb : hermA D n → G D n} (h : IsNMap nb) {γ : hermA D n} (hγ : γ ∈ ratHerm D n) : nb γ ∈ GF D n := by
  obtain ⟨x, hx⟩ := mem_ratMx.1 hγ
  have hadj : adj (rat x) = rat x := by rw [hx]; exact γ.2
  let u : GL (Fin (n + n)) D.host.E := ⟨blk4 1 x 0 1, blk4 1 (-x) 0 1, by simp [submatrix_fromBlocks_mul, block_matrix_one], by simp [submatrix_fromBlocks_mul, block_matrix_one]⟩
  have hm : rat u.1 = mat (nb γ) := by
    rw [h]
    change (blk4 1 x 0 1).map (incA D) = _
    rw [GlobalTheory.StdUnn.Frame.block_matrix_map, show γ.1 = rat x from hx.symm]
    congr 1
    · exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
    · exact Matrix.map_zero _ (map_zero (incA D))
    · exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  refine ⟨u, ?_, Units.ext hm⟩
  have hu : adj (mat (nb γ)) * JR (AF D.host.F) (Jst D n) * mat (nb γ) = JR (AF D.host.F) (Jst D n) := (nb γ).2
  change Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u.1 * Jst D n * u.1 = Jst D n
  apply rat_injective
  rw [rat_mul, rat_mul, cT_sig, rat_conjTranspose, hm]
  exact hu

theorem nb_facts : ∀ (D : D7) (n : ℕ) (nb : PositivityTheory.GramSchwartzFunctions.BC.hermA D n → GlobalTheory.StdUnn.G D n), PositivityTheory.PfSWUS.IsNMap nb →
    Continuous nb ∧ (∀ b c, nb (b + c) = nb b * nb c) ∧ ∀ γ ∈ PositivityTheory.GramSchwartzFunctions.BC.ratHerm D n, nb γ ∈ GlobalTheory.StdUnn.GF D n :=
  fun _ _ _ h => ⟨nb_continuous h, nb_add h, fun _ hγ => nb_rat h hγ⟩

end GlobalTheory.CompanionTheory.SiegelUnip
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

theorem zpow_mulVec (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ0 : ϖ ≠ 0) (r : ℤ) (y : Fin d → k) :
    ((z ^ r : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y = ϖ ^ r • y := by
  let φ : kˣ →* GL (Fin d) k := Units.map (Matrix.scalar (Fin d) : k →+* Matrix (Fin d) (Fin d) k).toMonoidHom
  have hφ : ∀ u : kˣ, ((φ u : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) = (u : k) • (1 : Matrix (Fin d) (Fin d) k) := by
    intro u
    ext i j
    simp [φ, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have h1 : z = φ (Units.mk0 ϖ hϖ0) := Units.ext (by rw [hφ, hz]; rfl)
  rw [h1, ← map_zpow, hφ, Matrix.smul_mulVec, one_mulVec]
  simp

theorem mem_latZ (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ0 : ϖ ≠ 0) (r : ℤ) (y : Fin d → k) :
    y ∈ (latZ z r).sub ↔ ∀ i, ValuativeRel.valuation k (y i) ≤ ValuativeRel.valuation k ϖ ^ r := by
  have hv : ValuativeRel.valuation k ϖ ≠ 0 := by simpa using hϖ0
  rw [latZ, COSub.mem_act, ← _root_.zpow_neg, zpow_mulVec z ϖ hz hϖ0]
  show (∀ i, ValuativeRel.valuation k ((ϖ ^ (-r) • y) i) ≤ 1) ↔ _
  refine forall_congr' fun i => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_zpow₀, _root_.zpow_neg, inv_mul_le_iff₀ (zero_lt_iff.2 (zpow_ne_zero _ hv)), mul_one]

theorem latZ_anti (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (r s : ℤ) (h : r ≤ s) : (latZ z s).sub ≤ (latZ z r).sub := by
  intro y hy
  have hv : 0 < ValuativeRel.valuation k ϖ := zero_lt_iff.2 (by simpa using hϖ0)
  rw [mem_latZ z ϖ hz hϖ0] at hy ⊢
  exact fun i => (hy i).trans (zpow_le_zpow_right_of_le_one₀ hv hϖ.le h)

theorem latZ_basis (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (L : COSub k d) : ∃ r : ℕ, (latZ z (r : ℤ)).sub ≤ L.sub := by
  have hall : ∀ᶠ t : k in 𝓝 0, ∀ w ∈ ((lat0 : COSub k d).sub : Set (Fin d → k)), t • w ∈ (L.sub : Set (Fin d → k)) := by
    refine (lat0 : COSub k d).isCompact.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun p : k × (Fin d → k) => p.1 • p.2 := continuous_fst.smul continuous_snd
    have h0 : (L.sub : Set (Fin d → k)) ∈ 𝓝 (((0 : k), w).1 • ((0 : k), w).2) := by
      simpa using L.isOpen.mem_nhds (show (0 : Fin d → k) ∈ (L.sub : Set (Fin d → k)) from L.sub.zero_mem)
    exact hc.continuousAt.eventually h0
  have ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  obtain ⟨r, hr⟩ := (ht.eventually hall).exists
  refine ⟨r, fun y hy => ?_⟩
  have h1 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) ∈ (L.sub : Set (Fin d → k)) := hr _ hy
  have h2 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) = y := by
    have := zpow_mulVec z ϖ hz hϖ0 (r : ℤ) ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, zpow_natCast] at this
    exact this.symm
  rw [h2] at h1
  exact h1

theorem exists_reps (L' L : COSub k d) (h : L'.sub ≤ L.sub) : ∃ S : Finset (Fin d → k), IsReps L' L S := by
  classical
  obtain ⟨t, ht⟩ := L.isCompact.elim_finite_subcover (fun c : L.sub => {y | y - (c : Fin d → k) ∈ L'.sub})
    (fun c => (isClopen_coset L' c).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, by simp⟩)
  let mk : (Fin d → k) → (Fin d → k) ⧸ L'.sub := QuotientAddGroup.mk
  have hout : ∀ c : Fin d → k, (-(Quotient.out (mk c)) + c) ∈ L'.sub := fun c =>
    QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (mk c))
  let S : Finset (Fin d → k) := (t.image fun c : L.sub => mk c.1).image Quotient.out
  refine ⟨S, ?_, ?_⟩
  · intro s hs
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hq
    have h1 := L.sub.sub_mem c.2 (h (hout c.1))
    simpa [sub_eq_add_neg] using h1
  · intro y hy
    obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hc' : y - c.1 ∈ L'.sub := hc
    have key : ∀ s ∈ S, y - s ∈ L'.sub → s = Quotient.out (mk y) := by
      intro s hs hys
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
      have e1 : mk (Quotient.out q) = q := QuotientAddGroup.out_eq' q
      have e2 : mk (Quotient.out q) = mk y :=
        QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using hys)
      rw [← e2, e1]
    have hmem : Quotient.out (mk c.1) ∈ S :=
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem (fun c : L.sub => mk c.1) hct)
    have hs : y - Quotient.out (mk c.1) ∈ L'.sub := by
      have := L'.sub.add_mem hc' (hout c.1)
      have e : y - c.1 + (-(Quotient.out (mk c.1)) + c.1) = y - Quotient.out (mk c.1) := by abel
      rwa [e] at this
    exact ⟨_, ⟨hmem, hs⟩, fun s' hs' => (key s' hs'.1 hs'.2).trans (key _ hmem hs).symm⟩

end GlobalTheory.CompanionTheory.BZCore

end
end

