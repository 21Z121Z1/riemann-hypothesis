import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0070
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGramOneZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceNotDvdDifferent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop

namespace GlobalTheory.DiffSOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_dvd_diff_of_split (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K) := by
  have h' : ({w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}).ncard = Module.finrank ℚ L := by
    rw [← h, Formalism.L2.SG.Pf.TypedLoc.primesOver_eq L hp]
    exact (Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw).symm
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef K L hp h' v hv
  have hvq : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq K hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem not_dvd_differentIdeal : ∀ {D : D7} (large₂ : SizeData₂ D), Rec large₂ → ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ S1 D →
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro D large₂ hR v hv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  rcases (S1_mem_OmF D).1 hv with h | h | h | h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 0 h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 1 h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde_prime Pm.pde_split.1 v h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde'_prime Pm.pde_split.2 v h

end GlobalTheory.DiffSOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeEqSublatticeDegreeAddLogIndex
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatIndexDeg
open NumberField IsDedekindDomain ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.FlatCM
open scoped nonZeroDivisors

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem ιMulti_ne_zero_of_li {m : ℕ} (v : Fin m → V) (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K m v ≠ 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination K v)
    (LinearMap.ker_eq_bot.2 (LinearIndependent.fintypeLinearCombination_injective hv))
  intro h
  have := congrArg (exteriorPower.alternatingMapLinearEquiv
    ((Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).compLinearMap g)) h
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero] at this
  have hgv : ∀ i, g (v i) = Pi.single i 1 := by
    intro i
    have : v i = Fintype.linearCombination K v (Pi.single i 1) := by simp
    rw [this, ← LinearMap.comp_apply, hg, LinearMap.id_apply]
  have e : (fun i => g (v i)) = fun i => Pi.single i 1 := funext hgv
  change Matrix.det (Matrix.of fun i => g (v i)) = 0 at this
  rw [e, show (Matrix.of fun i : Fin m => (Pi.single i 1 : Fin m → K)) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one] at this
  exact one_ne_zero this

omit [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V] in

theorem colon_smul_cancel (𝔞 : Ideal (𝓞 K)) (D : Submodule (𝓞 K) K)
    (hD : IsFractional (𝓞 K)⁰ D) (h0 : D ≠ ⊥) : (𝔞 • D).colon (D : Set K) = 𝔞 := by
  ext r
  rw [Submodule.mem_colon]
  constructor
  · intro h
    set Df : FractionalIdeal (𝓞 K)⁰ K := ⟨D, hD⟩
    have hDf : Df ≠ 0 := fun e => h0 (by
      have := congrArg (fun I : FractionalIdeal (𝓞 K)⁰ K => (I : Submodule (𝓞 K) K)) e
      simpa [Df] using this)
    have hmem : ∀ x ∈ 𝔞 • D, x ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * Df := by
      intro x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha d hd
        rw [Algebra.smul_def]
        exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩) hd
      · intro x y hx hy
        exact Submodule.add_mem (((𝔞 : FractionalIdeal (𝓞 K)⁰ K) * Df : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) hx hy
    have key : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r) * Df ≤
        (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * Df := by
      rw [FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      have h1 := hmem _ (h j hj)
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ a ?_
      rwa [Algebra.smul_def] at h1
    have key2 := mul_le_mul_left key Df⁻¹
    rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hDf, mul_one, mul_one] at key2
    have hr := key2 (FractionalIdeal.mem_spanSingleton_self _ _)
    obtain ⟨x, hx, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 hr
    rwa [← (FaithfulSMul.algebraMap_injective (𝓞 K) K) e]
  · intro hr s hs
    exact Submodule.smul_mem_smul hr hs

variable {m : ℕ}

variable (K) in

def coordMap (v : Fin m → V) : (Fin m → K) →ₗ[𝓞 K] V :=
  (Fintype.linearCombination K v).restrictScalars (𝓞 K)

theorem coordMap_apply (v : Fin m → V) (x : Fin m → K) : coordMap K v x = ∑ i, x i • v i := by
  simp [coordMap, Fintype.linearCombination_apply]

variable (K) in

def lineMap (ω : ⋀[K]^m V) : K →ₗ[𝓞 K] ⋀[K]^m V :=
  (LinearMap.toSpanSingleton K _ ω).restrictScalars (𝓞 K)

theorem lineMap_apply (ω : ⋀[K]^m V) (t : K) : lineMap K ω t = t • ω := rfl

theorem detSpan_map_coord (v : Fin m → V) (M' : Submodule (𝓞 K) (Fin m → K)) :
    detSpan K m (M'.map (coordMap K v)) =
      (GlobalTheory.BetaEx.detSpan M').map (lineMap K (exteriorPower.ιMulti K m v)) := by
  unfold detSpan GlobalTheory.BetaEx.detSpan
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    choose x hx hxy using fun i => Submodule.mem_map.1 (hy i)
    refine ⟨(Matrix.of x).det, (GlobalTheory.BetaEx.mem_detSet M' _).2 ⟨Matrix.of x, hx, rfl⟩, ?_⟩
    have e : y = fun i => ∑ j, (Matrix.of x) i j • v j := funext fun i => by
      rw [← hxy i, coordMap_apply]; rfl
    rw [lineMap_apply, e, GlobalTheory.FlatCM.Model.ιMulti_comb]
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M' d).1 hd
    refine ⟨fun i => coordMap K v (x i), fun i => Submodule.mem_map_of_mem (hx i), ?_⟩
    have e : (fun i => coordMap K v (x i)) = fun i => ∑ j, x i j • v j := funext fun i => by
      rw [coordMap_apply]
    rw [lineMap_apply, e, GlobalTheory.FlatCM.Model.ιMulti_comb]

omit [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V] in

theorem colon_map_of_injective {A B : Type} [AddCommGroup A] [Module (𝓞 K) A] [AddCommGroup B] [Module (𝓞 K) B]
    (f : A →ₗ[𝓞 K] B) (hf : Function.Injective f) (P Q : Submodule (𝓞 K) A) :
    (P.map f).colon ((Q.map f : Submodule (𝓞 K) B) : Set B) = P.colon (Q : Set A) := by
  ext r
  simp only [Submodule.mem_colon]
  constructor
  · intro h q hq
    have := h (f q) (Submodule.mem_map_of_mem hq)
    rw [← map_smul] at this
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 this
    rwa [hf e] at hp
  · intro h b hb
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hb
    rw [← map_smul]
    exact Submodule.mem_map_of_mem (h q hq)

omit [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V] in

theorem bdd_of_fg {M : Submodule (𝓞 K) (Fin m → K)} (hM : M.FG) : GlobalTheory.BetaEx.Bdd M := by
  classical
  obtain ⟨s, rfl⟩ := hM
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 K)⁰
    (s.biUnion fun x => Finset.univ.image x)
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [GlobalTheory.BetaEx.mem_std]
    intro j
    obtain ⟨c, hc⟩ := hint (x j) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
    exact ⟨c, hc⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem span_eq_of_latRank_eq [FiniteDimensional K V] {N L : Submodule (𝓞 K) V} (hNL : N ≤ L)
    (hr : latRank K L = latRank K N) :
    Submodule.span K (N : Set V) = Submodule.span K (L : Set V) :=
  Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono hNL) hr.symm

omit [IsScalarTower (𝓞 K) K V] in

theorem fg_of_le_fg' {N L : Submodule (𝓞 K) V} (hNL : N ≤ L) (hL : L.FG) : N.FG := by
  have : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
  have hfg := IsNoetherian.noetherian (N.comap L.subtype)
  have e : (N.comap L.subtype).map L.subtype = N := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hNL]
  exact e ▸ hfg.map _

theorem relIndex_eq_absNorm_idx [FiniteDimensional K V] {N L : Submodule (𝓞 K) V} (hNL : N ≤ L) (hL : L.FG)
    (hrL : latRank K L = m) (hrN : latRank K N = m) :
    idx K m L N ≠ ⊥ ∧ N.toAddSubgroup.relIndex L.toAddSubgroup = Ideal.absNorm (idx K m L N) := by
  have hN : N.FG := fg_of_le_fg' hNL hL
  obtain ⟨v, hv⟩ : ∃ v : Fin m → V, IsFrame K N v := hrN ▸ exists_isFrame N hN
  have hspanv : Submodule.span K (Set.range v) = Submodule.span K (N : Set V) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 hv.2.2)
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hv.1 i)
  have hLv : (L : Set V) ⊆ Submodule.span K (Set.range v) := by
    rw [hspanv, span_eq_of_latRank_eq hNL (hrL.trans hrN.symm)]
    exact Submodule.subset_span
  set ψ := coordMap K v with hψ
  have hinj : Function.Injective ψ := hv.2.1.fintypeLinearCombination_injective
  have hrange : L ≤ LinearMap.range ψ := by
    intro x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hLv hx)
    exact ⟨c, by rw [coordMap_apply]; exact hc⟩
  set L' := L.comap ψ with hL'def
  set N' := N.comap ψ with hN'def
  have hL' : L'.map ψ = L := Submodule.map_comap_eq_self hrange
  have hN' : N'.map ψ = N := Submodule.map_comap_eq_self (hNL.trans hrange)
  have hNL' : N' ≤ L' := Submodule.comap_mono hNL
  have hstd : ∀ x : Fin m → K, (∀ j, ∃ b : 𝓞 K, (b : K) = x j) → x ∈ N' := by
    intro x hx
    choose b hb using hx
    change ψ x ∈ N
    rw [coordMap_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← hb j, algebraMap_smul]
    exact N.smul_mem _ (hv.1 j)
  have hLfg : L'.FG := Submodule.fg_of_fg_map_injective ψ hinj (hL' ▸ hL)
  have hb : GlobalTheory.BetaEx.Bdd L' := bdd_of_fg hLfg
  have hb' : GlobalTheory.BetaEx.Bdd (N' ⊔ L') := by rwa [sup_eq_right.2 hNL']
  have ht : ∀ x ∈ L', ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ N' := by
    intro x hx
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk, hstd _ ((GlobalTheory.BetaEx.mem_std _).1 (h x hx))⟩
  obtain ⟨𝔞, h0, h1, -, h2⟩ := GlobalTheory.DetIdeal.exists_index_ideal_pair L' N' hLfg hb' ht
  rw [inf_eq_right.2 hNL'] at h1 h2
  have hω := ιMulti_ne_zero_of_li v hv.2.1
  have hℓ : Function.Injective (lineMap K (exteriorPower.ιMulti K m v)) :=
    fun s t e => smul_left_injective K hω e
  have hD0 : GlobalTheory.BetaEx.detSpan L' ≠ ⊥ := by
    intro e
    have h1m := GlobalTheory.BetaEx.det_mem (M := L') (1 : Matrix (Fin m) (Fin m) K) fun i => hNL' (hstd _ fun j =>
      ⟨if i = j then 1 else 0, by by_cases hij : i = j <;> simp [Matrix.one_apply, hij]⟩)
    rw [e, Matrix.det_one] at h1m
    exact one_ne_zero ((Submodule.mem_bot _).1 h1m)
  have hidx : idx K m L N = 𝔞 := by
    unfold idx
    rw [← hL', ← hN', detSpan_map_coord, detSpan_map_coord, colon_map_of_injective _ hℓ, h1]
    exact colon_smul_cancel 𝔞 _ (GlobalTheory.BetaEx.frac_of_bdd hb) hD0
  refine ⟨hidx ▸ h0, ?_⟩
  rw [hidx, h2]
  have e : L'.toAddSubgroup.map ψ.toAddMonoidHom = L.toAddSubgroup := by
    ext x
    rw [← hL']
    simp [Submodule.mem_map]
  rw [← e]
  exact (AddSubgroup.relIndex_comap N.toAddSubgroup ψ.toAddMonoidHom L'.toAddSubgroup).symm

end GlobalTheory.LatIndexDeg

namespace GlobalTheory.LatIndexDeg
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

theorem deg_eq_deg_add_log_absNorm_idx : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (m : ℕ) (L N : Submodule (𝓞 K) V), N ≤ L → L.FG → latRank K L = m → latRank K N = m → idx K m L N ≠ ⊥ ∧ deg h L = deg h N + Real.log (Ideal.absNorm (idx K m L N)) / Module.finrank ℚ K := by
  intro K V _ _ _ _ _ _ _ h m L N hNL hL hrL hrN
  obtain ⟨hne, hidx⟩ := relIndex_eq_absNorm_idx hNL hL hrL hrN
  refine ⟨hne, ?_⟩
  have hN : N.FG := fg_of_le_fg' hNL hL
  have hspan : (L : Set V) ⊆ Submodule.span K (N : Set V) := by
    rw [span_eq_of_latRank_eq hNL (hrL.trans hrN.symm)]
    exact Submodule.subset_span
  rw [deg_of_le h hN hL hNL hspan, hidx]
  ring

end GlobalTheory.LatIndexDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantSpanSpanEqGeneratorDets
section
open NumberField

namespace GlobalTheory.IdxTensor

theorem dets_span_eq {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)) :
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := by
  set T : Set F := {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} with hT
  apply le_antisymm
  · unfold dets
    rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    have key : ∀ s : Finset (Fin p), ∀ y : Fin p → Fin p → F,
        (∀ i, y i ∈ Submodule.span (𝓞 F) S) → (∀ i, i ∉ s → y i ∈ S) →
          (Matrix.of y).det ∈ Submodule.span (𝓞 F) T := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro y _ h
        exact Submodule.subset_span ⟨y, fun i => h i (Finset.notMem_empty i), rfl⟩
      | insert a s ha ih =>
        intro y hy hs
        have upd : ∀ v, Matrix.of (Function.update y a v) = Matrix.updateRow (Matrix.of y) a v := fun v => rfl
        have hv : ∀ v ∈ Submodule.span (𝓞 F) S,
            (Matrix.updateRow (Matrix.of y) a v).det ∈ Submodule.span (𝓞 F) T := by
          intro v hv
          induction hv using Submodule.span_induction with
          | mem x hx =>
            rw [← upd]
            apply ih
            · intro i
              by_cases h : i = a
              · subst h; simpa using Submodule.subset_span hx
              · simpa [Function.update_of_ne h] using hy i
            · intro i hi
              by_cases h : i = a
              · subst h; simpa using hx
              · simpa [Function.update_of_ne h] using hs i (by simp [h, hi])
          | zero =>
            rw [Matrix.det_eq_zero_of_row_eq_zero a (by intro j; simp)]
            exact Submodule.zero_mem _
          | add x z _ _ hx hz =>
            rw [Matrix.det_updateRow_add]
            exact Submodule.add_mem _ hx hz
          | smul r x _ hx =>
            rw [← algebraMap_smul F r x, Matrix.det_updateRow_smul, ← Algebra.smul_def]
            exact Submodule.smul_mem _ r hx
        have := hv (y a) (hy a)
        rwa [← upd, Function.update_eq_self] at this
    exact key Finset.univ y hy (by simp)
  · unfold dets
    apply Submodule.span_mono
    rintro d ⟨y, hy, rfl⟩
    exact ⟨y, fun i => Submodule.subset_span (hy i), rfl⟩

end GlobalTheory.IdxTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerStandardToSkewMemThetaSpaceStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwiner_standard_to_skew_mem_thetaSpace : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (𝔪 : Ideal (𝓞 D.host.E)), SD D (skewLat D 𝔪 d) → Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 ∈ ThSp D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) := by
  first | exact @GlobalTheory.SkewTheta.iop_mem_thSp | exact GlobalTheory.SkewTheta.iop_mem_thSp | (intros; apply GlobalTheory.SkewTheta.iop_mem_thSp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabilizerReductionEqLocalReductionStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (PP : Pl D.host.E), x ∈ St β → ∀ (i j : Fin n) (a : 𝓞 D.host.E), ((redFn β PP x : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j = Ideal.Quotient.mk PP.asIdeal a ↔ valuation (Kw PP) ((inBasis rfl β PP x).1 i j - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  first | exact @GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction | exact GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction | (intros; apply GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotTripleUnr

theorem unramAt_mul {D : D7} {ε : AF D.host.F} {χ₁ χ₂ : (AE D)ˣ →* Circle}
    (h₁ : GlobalTheory.WeilParts.UnramAt ε χ₁) (h₂ : GlobalTheory.WeilParts.UnramAt ε χ₂) : GlobalTheory.WeilParts.UnramAt ε (χ₁ * χ₂) := by
  intro x hx h1 h2
  rw [MonoidHom.mul_apply, h₁ x hx h1 h2, h₂ x hx h1 h2, one_mul]

theorem under_eq_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem unramAt_mu : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → (∀ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) ≠ v) → ∀ j : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1)) := by
  intro D T Lc sc G μ₀ hL t v e he hv hQ j
  have hmu : Lc.mu t (j + 1) = Lc.mu0 ((j : ℕ) + 1) * Lc.xi t := rfl
  rw [hmu]
  refine unramAt_mul ?_ ?_
  · refine GlobalTheory.UnramOver.unramAt_of_unrAt D _ (Lc.C.mu0 j) (hL.mu0 j) v e he fun P hP => ?_
    refine (Lc.C.isMu0 j).unr P fun k hk => hv ?_
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
      rw [← hP]
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]
      exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hk'
    · exact Or.inr (Or.inl hk')
  · refine GlobalTheory.UnramOver.unramAt_of_unrAt D _ (Lc.xiH t) (hL.xi t) v e he fun P hP => ?_
    by_contra hn
    rcases (hL.Q_ram t P).1 hn with hq | ⟨P', hq, hc⟩
    · exact hQ P hq hP
    · exact hQ P' hq ((under_eq_of_isConjPl hc).trans hP)

end GlobalTheory.BotTripleUnr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionWittFrameStabilizerStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviDecomposition_wittFrameStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ p β, ScalesBy σ J X p β → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, p = u * m ∧ ScalesBy σ J X m β ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) ∧ (absE F E (Matrix.GeneralLinearGroup.det β) = 1 → m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) := by
  first | exact @GlobalTheory.LeviDecompositionFrame.levi_dec_frame | exact GlobalTheory.LeviDecompositionFrame.levi_dec_frame | (intros; apply GlobalTheory.LeviDecompositionFrame.levi_dec_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionCommuteOfFixesIsotropicColumns
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem lv_comm_of_fix_cols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ α, ∀ x ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), lv α * x = x * lv α := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv α x hx
  obtain ⟨hxC, hxD⟩ := Subgroup.mem_inf.mp hx
  have hC : (matHom _ σ J x).1 * adMat F C = adMat F C := hxC
  have hD : (matHom _ σ J x).1 * adMat F D = adMat F D := hxD
  have formOf : ∀ (K : Matrix (Fin n) (Fin j) E), x⁻¹ ∈ fixG σ J K →
      adMat F (cT (σ : E →+* E) K * J) * (matHom _ σ J x).1 = adMat F (cT (σ : E →+* E) K * J) := by
    intro K hK
    have h1 : (matHom _ σ J x⁻¹).1 * adMat F K = adMat F K * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact hK
    have := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at this
  have fC := formOf C ((fixG σ J C).inv_mem hxC)
  have fD := formOf D ((fixG σ J D).inv_mem hxD)
  set X := (matHom _ σ J x).1 with hX
  have hZ : X * adMat F Z = adMat F Z * (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * X * adMat F Z) := by
    have h1 : adMat F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    have e : X * adMat F Z = adMat F (C * (cT (σ : E →+* E) D * J) +
        Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) * X * adMat F Z := by
      rw [hF.sum, h1, Matrix.one_mul]
    have z1 : adMat F (cT (σ : E →+* E) D * J) * X * adMat F Z = 0 := by
      rw [fD, adMat, adMat, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]
    have z2 : adMat F (cT (σ : E →+* E) C * J) * X * adMat F Z = 0 := by
      rw [fC, adMat, adMat, ← Matrix.map_mul, hF.cz, Matrix.map_zero _ (map_zero _)]
    have hadd : ∀ {p : ℕ} (A B : Matrix (Fin n) (Fin p) E), adMat F (A + B) = adMat F A + adMat F B :=
      fun A B => Matrix.map_add _ (map_add _) A B
    have hmul : ∀ {p : ℕ} (A : Matrix (Fin n) (Fin p) E) (B : Matrix (Fin p) (Fin n) E),
        adMat F (A * B) = adMat F A * adMat F B := fun A B => Matrix.map_mul
    rw [e, hadd, hadd, hmul, hmul, hmul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_assoc (adMat F C), Matrix.mul_assoc (adMat F C), z1, Matrix.mul_assoc (adMat F D),
      Matrix.mul_assoc (adMat F D), z2, Matrix.mul_zero, Matrix.mul_zero, zero_add, add_zero,
      Matrix.mul_assoc (adMat F Z), Matrix.mul_assoc (adMat F Z)]
  apply eq_of_frame_cols F E σ n J j m C D Z J₀ hF
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onC, ← hX, hC,
      ← Matrix.mul_assoc, hC, hlv.onC]
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onZ, ← hX, hZ,
      ← Matrix.mul_assoc, hlv.onZ]
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, hlv.onD, ← hX, hD,
      ← Matrix.mul_assoc, hD, hlv.onD]

end GlobalTheory.SphEis
end

