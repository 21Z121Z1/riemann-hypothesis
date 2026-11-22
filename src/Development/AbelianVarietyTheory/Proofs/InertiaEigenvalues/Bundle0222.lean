import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import ReciprocityTheory.Hypotheses.GalCohDefs
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0152
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0162
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0160
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0166
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0217
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticeQuotPrimePow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.LatticeCard

theorem mem_span_singleton_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : R) (x : M) : x ∈ (Ideal.span {b} • ⊤ : Submodule R M) ↔ ∃ y : M, b • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem card_quot_pow_succ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (ha : IsSMulRegular M a) (k : ℕ) :
    Nat.card (M ⧸ (Ideal.span {a ^ (k + 1)} • ⊤ : Submodule R M)) =
      Nat.card (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) *
      Nat.card (M ⧸ (Ideal.span {a ^ k} • ⊤ : Submodule R M)) := by
  set S : Submodule R M := Ideal.span {a ^ (k + 1)} • ⊤ with hS
  set T : Submodule R M := Ideal.span {a ^ k} • ⊤ with hT
  have hST : S ≤ T := by
    intro x hx
    rw [hS, mem_span_singleton_smul_top] at hx
    rw [hT, mem_span_singleton_smul_top]
    obtain ⟨y, rfl⟩ := hx
    exact ⟨a • y, by rw [smul_smul, ← pow_succ]⟩
  have h1 := Submodule.card_eq_card_quotient_mul_card (T.map S.mkQ)
  rw [Nat.card_congr (Submodule.quotientQuotientEquivQuotient S T hST).toEquiv] at h1
  rw [h1]
  congr 1
  have hmem : ∀ x : M, S.mkQ (a ^ k • x) ∈ T.map S.mkQ := fun x =>
    ⟨a ^ k • x, SetLike.mem_coe.2 ((mem_span_singleton_smul_top _ _).2 ⟨x, rfl⟩), rfl⟩
  let φ : M →ₗ[R] ↥(T.map S.mkQ) :=
    LinearMap.codRestrict (T.map S.mkQ) (S.mkQ ∘ₗ (a ^ k • LinearMap.id)) (fun x => hmem x)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, w, hw, rfl⟩
    rw [SetLike.mem_coe, mem_span_singleton_smul_top] at hw
    obtain ⟨x, rfl⟩ := hw
    exact ⟨x, rfl⟩
  have hker : LinearMap.ker φ = (Ideal.span {a} • ⊤ : Submodule R M) := by
    ext x
    rw [LinearMap.mem_ker, mem_span_singleton_smul_top]
    have hφ : φ x = 0 ↔ a ^ k • x ∈ S := by
      rw [← Subtype.coe_inj]
      change S.mkQ (a ^ k • x) = 0 ↔ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [hφ, hS, mem_span_singleton_smul_top]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, (ha.pow k) ?_⟩
      change a ^ k • (a • y) = a ^ k • x
      rw [smul_smul, ← pow_succ]; exact hy
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [smul_smul, ← pow_succ]⟩
  rw [← Nat.card_congr (LinearMap.quotKerEquivOfSurjective φ hsurj).toEquiv,
    Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv]

theorem card_quot_pow {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (ha : IsSMulRegular M a) (r : ℕ) :
    Nat.card (M ⧸ (Ideal.span {a ^ r} • ⊤ : Submodule R M)) =
      Nat.card (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) ^ r := by
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨0⟩⟩
    induction x using Submodule.Quotient.induction_on with | _ x => ?_
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    rw [Submodule.Quotient.eq, mem_span_singleton_smul_top]
    exact ⟨x - y, one_smul _ _⟩
  | succ k ih => rw [card_quot_pow_succ a ha k, ih, pow_succ, mul_comm]

theorem card_quot_equiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (b : R) :
    Nat.card (M ⧸ (Ideal.span {b} • ⊤ : Submodule R M)) =
      Nat.card (N ⧸ (Ideal.span {b} • ⊤ : Submodule R N)) := by
  refine Nat.card_congr (Submodule.Quotient.equiv _ _ e ?_).toEquiv
  ext y
  rw [Submodule.mem_map_equiv, mem_span_singleton_smul_top, mem_span_singleton_smul_top]
  constructor
  · rintro ⟨x, hx⟩; exact ⟨e x, by rw [← map_smul, hx, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩; exact ⟨e.symm x, by rw [map_smul]⟩

theorem card_quot_fun {ι O : Type*} [Fintype ι] [CommRing O] (b : O) :
    Nat.card ((ι → O) ⧸ (Ideal.span {b} • ⊤ : Submodule O (ι → O))) =
      Nat.card (O ⧸ Ideal.span {b}) ^ Fintype.card ι := by
  let π : (ι → O) →ₗ[O] (ι → O ⧸ Ideal.span {b}) :=
    LinearMap.pi (fun i => (Ideal.Quotient.mkₐ O (Ideal.span {b})).toLinearMap ∘ₗ LinearMap.proj i)
  have hπ : ∀ x i, π x i = Ideal.Quotient.mk _ (x i) := fun x i => rfl
  have hsurj : Function.Surjective π := by
    intro y
    refine ⟨fun i => (y i).out, funext fun i => ?_⟩
    rw [hπ, Ideal.Quotient.mk_out]
  have hker : LinearMap.ker π = (Ideal.span {b} • ⊤ : Submodule O (ι → O)) := by
    ext x
    rw [LinearMap.mem_ker, mem_span_singleton_smul_top]
    constructor
    · intro hx
      have : ∀ i, ∃ c, b * c = x i := fun i => by
        have h := congrFun hx i
        rw [hπ, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
        obtain ⟨c, hc⟩ := h
        exact ⟨c, hc.symm⟩
      choose c hc using this
      exact ⟨c, funext fun i => by simp [hc]⟩
    · rintro ⟨y, rfl⟩
      funext i
      rw [hπ, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨y i, by simp⟩
  rw [← Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv,
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective π hsurj).toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ι)]

end GlobalTheory.LatticeCard

namespace GlobalTheory.LatticeCard

theorem card_lattice_quot_pow : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ), Nat.card (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
  intro l _ G _ _ LL _ _ _ O _ _ hG A LA r
  obtain ⟨⟨hD, -, hFr⟩, -, -, -, -⟩ := hG
  haveI := hD
  haveI := hFr
  haveI : Module.Free O LA.T := LA.free
  haveI : Module.Finite O LA.T := Module.Finite.iff_fg.2 LA.fg
  let b := Module.Free.chooseBasis O LA.T
  have hli : LinearIndependent LL (fun i => (b i : A.V)) := by
    rw [← LinearIndependent.iff_fractionRing O LL]
    exact b.linearIndependent.map' LA.T.subtype (Submodule.ker_subtype _)
  have hT : (LA.T : Set A.V) ⊆ Submodule.span LL (Set.range fun i => (b i : A.V)) := by
    intro x hx
    have hx' : (⟨x, hx⟩ : LA.T) ∈ Submodule.span O (Set.range b) := by
      rw [b.span_eq]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span LA.T.subtype hx'
    rw [← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars O LL _ h2
  have hsp : ⊤ ≤ Submodule.span LL (Set.range fun i => (b i : A.V)) :=
    calc ⊤ = Submodule.span LL (LA.T : Set A.V) := LA.span.symm
      _ ≤ _ := Submodule.span_le.2 hT
  have hn : finrank LL A.V = Fintype.card (Module.Free.ChooseBasisIndex O LA.T) :=
    finrank_eq_card_basis (Basis.mk hli hsp)
  have hl : ((l : ℕ) : LL) ≠ 0 := by
    have h := (algebraMap ℚ_[l] LL).injective.ne
      (show ((l : ℕ) : ℚ_[l]) ≠ 0 from Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    simpa using h
  have hreg : IsSMulRegular LA.T ((l : ℕ) : O) := by
    intro x y hxy
    have h1 : ((l : ℕ) : O) • (x : A.V) = ((l : ℕ) : O) • (y : A.V) := by
      have := congrArg (fun z : LA.T => (z : A.V)) hxy
      simpa only [Submodule.coe_smul] using this
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul LL,
      ← Nat.cast_smul_eq_nsmul LL l (y : A.V)] at h1
    exact Subtype.ext (smul_right_injective A.V hl h1)
  rw [card_quot_pow _ hreg, card_quot_equiv b.equivFun, card_quot_fun, hn, ← pow_mul, mul_comm]

end GlobalTheory.LatticeCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CohomologyShapeOfTateDualityEuler
section
noncomputable section

namespace GlobalTheory.ShapeNeg

open Formalism.NG Formalism.RepresentationBoundsCohomology.JT ReciprocityTheory.Gal

theorem shapeG_of_localDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) :
    ReciprocityTheory.ChartRestriction.T2.ShapeG := by
  intro p _ K O _ _ _ _ _ _ _ G _ _ hK hO hF i ε hcyc e he M _ _ u ρ hρ
  haveI := hO.ring
  haveI := hO.compact
  haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace
  haveI hres : Finite (IsLocalRing.ResidueField O) := GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr hO.adic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]; exact hO.p_mem
  have hpn : ∀ n : ℕ, ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n} := fun n => by
    rw [← Ideal.span_singleton_pow]; exact Ideal.pow_mem_pow hpϖ n
  set q := Nat.card (IsLocalRing.ResidueField O) with hq
  set d := Module.finrank ℚ_[p] K with hd
  set ε' : Formalism.GaloisCohomology.GK p K →* Oˣ := ε.comp i.symm.toMulEquiv.toMonoidHom with hε'
  have hcyc' : ∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε') g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n} := hcyc
  have hlcε : ∀ N : ℕ, IsLocallyConstant
      (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O)) := by
    intro N
    have h := (GlobalTheory.T.cyclotomic_character_isLocallyConstant_mod_pow ε' hcyc' N).comp_continuous i.continuous
    convert h using 1
    funext g
    simp only [Function.comp_apply, ε', MonoidHom.comp_apply]
    first
      | rfl
      | (congr 3; exact (i.symm_apply_apply g).symm)
      | simp
  have hMt : ∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0 := fun m => by
    obtain ⟨n, hn⟩ := GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer hϖ (u m)
    exact ⟨n, u.injective (by rw [map_smul, hn, map_zero])⟩
  have hMp : ∀ m : M, ∃ N : ℕ, (p : O) ^ N • m = 0 := fun m => by
    obtain ⟨n, hn⟩ := hMt m
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hpn n)
    exact ⟨n, by rw [← hb, mul_smul, hn, smul_zero]⟩
  have hdiv : ∀ m : M, ∃ m' : M, ϖ • m' = m := fun m => by
    obtain ⟨y, hy⟩ := GlobalTheory.T.fractionRingQuot_divisible_by_uniformizer hϖ (u m)
    exact ⟨u.symm y, u.injective (by rw [map_smul, LinearEquiv.apply_symm_apply, hy])⟩
  have hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m) := fun m => by
    obtain ⟨N, hN⟩ := hMp m
    exact GlobalTheory.T.isLocallyConstant_orbit_of_inv_pow_character' ε hlcε e ρ hρ m N hN
  set ρ' : Representation O (Formalism.GaloisCohomology.GK p K) M := ρ.comp i.symm.toMulEquiv.toMonoidHom with hρ'def
  have hρ' : ∀ g m, ρ' g m = ((((ε' g) ^ e)⁻¹ : Oˣ) : O) • m := fun g m => hρ _ m
  have hcont : ∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ') := fun n h =>
    GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant ρ' p n (ϖ ^ n) h (fun m _ => (hlc m).comp_continuous i.symm.continuous)
  obtain ⟨σ1, hσ1⟩ := GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root hO.p_mem hO.p_ne ε' hcyc' e (GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity hK e he)
  obtain ⟨σ2, hσ2⟩ := GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root hO.p_mem hO.p_ne ε' hcyc' (e + 1) (GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity hK (e + 1) (Nat.succ_pos e))
  have hNfin : Finite ρ.invariants := by
    refine GlobalTheory.T.finite_invariants_of_scalar_ne_one_twist u ρ (i.symm σ1) ((((ε (i.symm σ1)) ^ e)⁻¹ : Oˣ) : O) ?_ (hρ _)
    intro h1
    apply hσ1
    have h2 : ((ε (i.symm σ1)) ^ e)⁻¹ = 1 := Units.ext h1
    exact inv_eq_one.1 h2
  obtain ⟨C, hC⟩ := GlobalTheory.T.h2_bounded_twist hT hK hϖ hpϖ ε' hcyc' e u ρ' hρ' σ2 hσ2 hcont
  have hone2 := GlobalTheory.T.card_H2_level_rep_one_le hT hK hϖ u ρ' (hpn 1) (hcont 1 (hpn 1))
  have key : ∀ n : ℕ, 0 < n →
      Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
      (letI := GlobalTheory.ShapeNeg.levZ (M := M) p n (hpn n)
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) =
        Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ')) * q ^ (n * d)) := by
    intro n hn
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p n (hpn n)
    obtain ⟨hLf, hLc⟩ := GlobalTheory.T.finite_card_torsionLevel_fractionRingQuot hϖ u n
    obtain ⟨hH1f, -⟩ := GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK n (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n))
      (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ') hn (hcont n (hpn n))
    have hEu := hE p K hK n (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ') hn
      (hcont n (hpn n))
    obtain ⟨t0, t1⟩ := GlobalTheory.T.transfer_card_H0_H1_eq i ρ p n (ϖ ^ n) (hpn n)
    have hH1O : Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) :=
      Nat.finite_of_card_ne_zero (by rw [t1]; exact Nat.card_pos.ne')
    obtain ⟨hXf, hX⟩ := GlobalTheory.T.card_H1_level_rep_formula ρ ϖ n hdiv hlc hH1O
    have h0c := GlobalTheory.T.card_H0_level_rep_eq ρ (ϖ ^ n) hNfin
    set Nq := Nat.card (ρ.invariants ⧸
      LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) with hNq
    haveI : Finite (ρ.invariants ⧸
        LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    have hpos : 0 < Nq := Nat.card_pos
    refine ⟨hXf, ?_⟩
    have e1 : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) * Nq =
        (Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ')) * q ^ (n * d)) * Nq := by
      rw [← hX, t1, hEu, ← t0, h0c, hLc, ← pow_mul]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos e1
  have htors := GlobalTheory.T.exists_pow_smul_eq_zero_of_mem_HcLC_of_torsion ρ ϖ hMt
  have hfin1 : Finite (LinearMap.ker (ϖ • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) := by
    have h1 := (key 1 one_pos).1
    simpa only [pow_one] using h1
  obtain ⟨a, F, _, _, hFf, ⟨φ⟩⟩ := GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite hϖ (Y := ReciprocityTheory.ChartRestriction.T2.HcLC ρ)
    (fun y => (htors y.1 y.2).imp fun n hn => Subtype.ext (by simpa using hn)) hfin1
  haveI := hFf
  refine GlobalTheory.T.torsion_shape_of_torsion_counts hϖ (ReciprocityTheory.ChartRestriction.T2.HcLC ρ) d a φ ⟨C, fun n hn => ?_⟩ ?_
  · obtain ⟨hXf, hX⟩ := key n hn
    try dsimp only at hX
    have hXpos : 0 < Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) :=
      Nat.card_pos
    rw [hX] at hXpos ⊢
    have hb := hC n hn (hpn n)
    try dsimp only at hb
    have h2pos := Nat.pos_of_mul_pos_right hXpos
    constructor
    · exact Nat.le_mul_of_pos_left _ h2pos
    · exact Nat.mul_le_mul_right _ hb
  · obtain ⟨-, hX⟩ := key 1 one_pos
    try dsimp only at hX hone2
    rw [hX]
    calc _ ≤ q * q ^ (1 * d) := Nat.mul_le_mul_right _ hone2
      _ = q ^ (d + 1) := by ring

end GlobalTheory.ShapeNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixDecomposeStatement
section
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_integral_matrix_decompose : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → ∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ x z a₁ a₂ a₃ : Matrix (Fin n) (Fin n) E, (x * N = N * x ∧ z * N = N * z ∧ a₁ * N = N * a₁ ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖x i j‖ ≤ 1 ∧ ‖z i j‖ ≤ 1 ∧ ‖a₁ i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ x * x - x = ϖ • a₁ ∧ y * (1 - x) = ϖ • a₂ ∧ y * z * x - x = ϖ • a₃ := by
  first | exact @GlobalTheory.UnitDiscAlg.Red.main | exact GlobalTheory.UnitDiscAlg.Red.main | (intros; apply GlobalTheory.UnitDiscAlg.Red.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CompactRepField

open Polynomial IntermediateField

theorem exists_mem_adjoin_simple (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (j : Ω →+* PadicAlgCl l) (x : PadicAlgCl l) : ∃ y : Ω, x ∈ ℚ_[l]⟮j y⟯ := by
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hfin : ({x' | IsConjRoot ℚ_[l] x x' ∧ x ≠ x'} : Set (PadicAlgCl l)).Finite := by
    refine ((minpoly ℚ_[l] x).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_
    exact (isConjRoot_iff_mem_minpoly_rootSet (hint x)).1 hx'.1
  have hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] x x' ∧ x ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖x - y‖ < ‖x - x'‖}) :=
    hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const
  obtain ⟨y, hy⟩ := (GlobalTheory.denseRange_of_isAlgClosed_padicAlgCl l Ω j).exists_mem_open hop
    ⟨x, by
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]
      exact fun x' h => h.2⟩
  refine ⟨y, IsKrasner.krasner (minpoly.irreducible (hint x)).separable (IsAlgClosed.splits _)
    (hint _) fun x' h1 h2 => ?_⟩
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hy
  exact hy x' ⟨h1, h2⟩

theorem exists_countable_family (l : ℕ) [Fact l.Prime] :
    ∃ (ι : Type) (_ : Countable ι) (K : ι → IntermediateField ℚ_[l] (PadicAlgCl l)),
      (∀ i, FiniteDimensional ℚ_[l] (K i)) ∧
      ∀ s : Set (PadicAlgCl l), s.Finite → ∃ i, s ⊆ K i := by
  classical
  haveI halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Countable (AlgebraicClosure ℚ) := by
    have h : {x : AlgebraicClosure ℚ | IsAlgebraic ℚ x}.Countable := Algebraic.countable ℚ _
    exact Set.countable_univ_iff.1 (h.mono fun x _ => halg.isAlgebraic x)
  let j : AlgebraicClosure ℚ →+* PadicAlgCl l :=
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := PadicAlgCl l)).toRingHom
  refine ⟨Finset (AlgebraicClosure ℚ), inferInstance,
    fun S => IntermediateField.adjoin ℚ_[l] (j '' (S : Set _)), fun S => ?_, fun s hs => ?_⟩
  · haveI : Finite (j '' (S : Set (AlgebraicClosure ℚ))) := (S.finite_toSet.image j).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  · choose y hy using exists_mem_adjoin_simple l (AlgebraicClosure ℚ) j
    refine ⟨(hs.image y).toFinset, fun x hx => ?_⟩
    refine IntermediateField.adjoin.mono _ _ _ ?_ (hy x)
    rw [Set.singleton_subset_iff]
    exact ⟨y x, by simpa using ⟨x, hx, rfl⟩, rfl⟩

def entrySubgroup {F E G : Type} [Field F] [Field E] [Algebra F E] [Group G] {a : ℕ}
    (r : G →* Matrix.GeneralLinearGroup (Fin a) E) (K : IntermediateField F E) : Subgroup G where
  carrier := {g | ∀ i j, (r g : Matrix (Fin a) (Fin a) E) i j ∈ K ∧
    (r g⁻¹ : Matrix (Fin a) (Fin a) E) i j ∈ K}
  one_mem' := fun i j => by
    have : (r 1 : Matrix (Fin a) (Fin a) E) i j ∈ K := by
      rw [map_one, Units.val_one, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    exact ⟨this, by rwa [inv_one]⟩
  mul_mem' := fun {g h} hg hh i j => by
    rw [mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
      Matrix.mul_apply]
    exact ⟨sum_mem fun k _ => mul_mem (hg i k).1 (hh k j).1,
      sum_mem fun k _ => mul_mem (hh i k).2 (hg k j).2⟩
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem exists_finiteDimensional_entries_mem (l : ℕ) [Fact l.Prime] (G : Type) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (n : ℕ)
    (r : G →* Matrix.GeneralLinearGroup (Fin n) (PadicAlgCl l))
    (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧
      ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K := by
  obtain ⟨ι, _, K, hK, hcov⟩ := exists_countable_family l
  have hKcl : ∀ m, IsClosed (K m : Set (PadicAlgCl l)) := fun m =>
    haveI : FiniteDimensional ℚ_[l] (K m).toSubalgebra.toSubmodule := hK m
    Submodule.closed_of_finiteDimensional (K m).toSubalgebra.toSubmodule
  have hcl : ∀ m, IsClosed (entrySubgroup r (K m) : Set G) := fun m => by
    have : (entrySubgroup r (K m) : Set G) = ⋂ i, ⋂ j,
        ((fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m) ∩
         (fun g => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m)) := by
      ext g
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      ((hKcl m).preimage (hr i j)).inter ((hKcl m).preimage ((hr i j).comp continuous_inv))
  have hun : ⋃ m, (entrySubgroup r (K m) : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨m, hm⟩ := hcov
      (Set.range (fun p : Fin n × Fin n => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2) ∪
       Set.range (fun p : Fin n × Fin n => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2))
      ((Set.finite_range _).union (Set.finite_range _))
    exact Set.mem_iUnion.2 ⟨m, fun i j =>
      ⟨hm (Or.inl ⟨(i, j), rfl⟩), hm (Or.inr ⟨(i, j), rfl⟩)⟩⟩
  obtain ⟨m, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (entrySubgroup r (K m) : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (G ⧸ entrySubgroup r (K m)) := Subgroup.quotient_finite_of_isOpen _ hop
  let s : Set (PadicAlgCl l) := Set.range fun p : (G ⧸ entrySubgroup r (K m)) × Fin n × Fin n =>
    (r p.1.out : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.2.1 p.2.2
  haveI : Finite s := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  haveI := hK m
  refine ⟨IntermediateField.adjoin ℚ_[l] s ⊔ K m, inferInstance, fun g i j => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (entrySubgroup r (K m)) g
  have hg : g = (g : G ⧸ entrySubgroup r (K m)).out * (h : G)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, map_mul, Units.val_mul, Matrix.mul_apply]
  refine sum_mem fun k _ => mul_mem ?_ ?_
  · exact (le_sup_left : IntermediateField.adjoin ℚ_[l] s ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(g, i, k), rfl⟩)
  · exact (le_sup_right : K m ≤ _) (h.2 k j).2

theorem exists_finExt_entries_mem :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (a : ℕ) (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l)), Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ L₀ : FinExt l, ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := by
  intro l _ G _ _ _ _ _ a r hr L₀
  obtain ⟨K, hK, h⟩ := exists_finiteDimensional_entries_mem l G a r
    fun i j => hr.matrix_elem i j
  haveI := L₀.2
  exact ⟨⟨L₀.1 ⊔ K, inferInstance⟩, le_sup_left, fun g i j =>
    (le_sup_right : K ≤ L₀.1 ⊔ K) (h g i j)⟩

end GlobalTheory.CompactRepField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAdicModuleIff
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open Topology Filter

namespace GlobalTheory

private lemma mem_span_pow_smul_iff_exists_pow_smul {R : Type} [CommRing R] (a : R) {M : Type} [AddCommGroup M]
    [Module R M] (n : ℕ) (x : M) :
    x ∈ (Ideal.span {a}) ^ n • (⊤ : Submodule R M) ↔ ∃ y : M, x = a ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp [eq_comm]

theorem continuous_adicModule_iff {R : Type} [CommRing R] (a : R) {M : Type} [AddCommGroup M]
    [Module R M] {G : Type} [TopologicalSpace G] (f : G → M) :
    @Continuous G M _ ((Ideal.span {a}).adicModuleTopology M) f ↔
      ∀ (g : G) (n : ℕ), ∀ᶠ h in 𝓝 g, ∃ y : M, f h - f g = a ^ n • y := by
  let _ : TopologicalSpace R := (Ideal.span {a}).ringFilterBasis.topology
  let _ : TopologicalSpace M := (Ideal.span {a}).adicModuleTopology M
  have hB : ∀ y : M, (𝓝 y).HasBasis
      (fun V : Set M => ∃ n : ℕ, V = ↑((Ideal.span {a}) ^ n • (⊤ : Submodule R M)))
      (fun V => (fun z => y + z) '' V) := fun y =>
    ((Ideal.span {a}).ringFilterBasis.moduleFilterBasis
      ((Ideal.span {a}).adic_module_basis M)).toAddGroupFilterBasis.nhds_hasBasis y
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun g => ?_
  refine ((hB (f g)).tendsto_right_iff).trans ⟨fun H n => ?_, fun H V hV => ?_⟩
  · filter_upwards [H _ ⟨n, rfl⟩] with h hh
    obtain ⟨z, hz, hzh⟩ := hh
    obtain ⟨y, rfl⟩ := (mem_span_pow_smul_iff_exists_pow_smul a n z).1 hz
    beta_reduce at hzh
    exact ⟨y, by rw [← hzh, add_sub_cancel_left]⟩
  · obtain ⟨n, rfl⟩ := hV
    filter_upwards [H n] with h hh
    obtain ⟨y, hy⟩ := hh
    exact ⟨a ^ n • y, (mem_span_pow_smul_iff_exists_pow_smul a n _).2 ⟨y, rfl⟩, by
      show f g + a ^ n • y = f h
      rw [← hy]; abel⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTateMaximalIdealKillsFirstCohomologyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (r : ℕ) (a : PadicComplex l), a ∈ inC (Kinf K) → ‖a‖ < 1 → ∀ c : GQ l → Fin r → PadicComplex l, CocOn (Hinf K) (fun g y k => act g (y k)) (ball l r) c → CobOn (Hinf K) (fun g y k => act g (y k)) (ball l r) (fun g => a • c g) := by
  first | exact @GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary | exact GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary | (intros; apply GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary <;> assumption)
end

