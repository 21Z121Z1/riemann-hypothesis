import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0296
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0306
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0299
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorH2Twist
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.FreeTwistH2

theorem powSub_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) (n : ℕ) :
    ((powSub (M := O) ϖ n : Submodule O O) : Set O) = ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
  ext x
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, SetLike.mem_coe,
    mem_powSub, Ideal.mem_span_singleton']
  simp only [smul_eq_mul, mul_comm]

theorem powSub_open_basis {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] (hO : PadicCoeff p O) {ϖ : O} (hϖ : Irreducible ϖ) :
    (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) ∧
      ∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U := by
  haveI := hO.ring
  obtain ⟨h1, h2⟩ := (isAdic_iff).1 hO.adic
  refine ⟨fun n => ?_, fun U hU => ?_⟩
  · rw [powSub_eq hϖ]; exact h1 n
  · obtain ⟨n, hn⟩ := h2 U hU
    exact ⟨n, by rw [powSub_eq hϖ]; exact hn⟩

theorem exists_free_H2_twist : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K →
    PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) →
    ∃ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) := by
  intro p _ K O _ _ _ _ _ G _ _ hT hK hO i ε hε
  haveI := hO.compact
  haveI := hO.t2
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hopen, hbasis⟩ := powSub_open_basis hO hϖ
  haveI := GlobalTheory.T.isAdicComplete_of_padicCoeff' hO
  have hd : ∀ n : ℕ, ringChar (O ⧸ IsLocalRing.maximalIdeal O ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)),
      Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow hO.p_mem n
  let φ : ℤ_[p] →+* O := IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal O)
    (fun n => (ZMod.castHom (hd n) (O ⧸ IsLocalRing.maximalIdeal O ^ n)).comp (PadicInt.toZModPow n))
    (fun {m n} hle => by
      rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
      congr 1
      exact RingHom.ext_zmod _ _)
  have hφ : Continuous φ := GlobalTheory.T.padicInt_ringHom_continuous_of_padicCoeff' hO φ
  let χZ : Formalism.GaloisCohomology.GK p K →* ℤ_[p]ˣ := (cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p))
  have hχc : Continuous fun g => (χZ g : ℤ_[p]) :=
    Units.continuous_val.comp (cyclotomicCharacter.continuous p K (PadicAlgCl p))
  obtain ⟨c, hc⟩ := GlobalTheory.TateTop.exists_gen_all hχc fun r => by
    have : NeZero (p ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    exact GlobalTheory.TateTop.exists_gen hχc
      (hT p K hK (r + 1) (ZMod (p ^ (r + 1))) (ReciprocityTheory.Gal.charRep (GlobalTheory.Cyc.TwistLift.redChar χZ (r + 1)))
        (Nat.succ_pos _) (GlobalTheory.Cyc.TwistLift.contAction_charRep _
          ((GlobalTheory.PadicH2Separated.continuous_reduction _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT p K hK (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  let e : G ≃* Formalism.GaloisCohomology.GK p K := i.toMulEquiv
  have he : Continuous e := i.continuous
  have he' : Continuous e.symm := i.symm.continuous
  let χ : G →* ℤ_[p]ˣ := χZ.comp e.toMonoidHom
  let cG : G × G → ℤ_[p] := fun q => c (e q.1, e q.2)
  have hcG : ∀ r, GlobalTheory.TateTop.Gen χ r cG := fun r => (hc r).transport e he he'
  have hεφ : ∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p]) := fun g => GlobalTheory.T.eq_cyclotomicCharacter_of_isCyc hO φ i hε g
  have hχGc : Continuous fun g => (χ g : ℤ_[p]) := hχc.comp he
  have hεc : Continuous fun g => ((ε g : Oˣ) : O) := by
    simp_rw [hεφ]
    exact hφ.comp hχGc
  have hcont : ContAction (twist ε O) := by
    show Continuous fun q : G × O => twist ε O q.1 q.2
    simp only [twist_apply, smul_eq_mul]
    exact (hεc.comp continuous_fst).mul continuous_snd
  have hfin := fun n => GlobalTheory.T.finite_cocycles_quotient_pow_smul_of_isOpen hT hK hO.p_mem i (twist ε O) hcont ϖ hϖ hopen n
  have hG := fun r => GlobalTheory.GenSpan.gen_zmod (hcG r)
  have hcc : Continuous cG :=
    GlobalTheory.PadicH2Separated.continuous_of_reductions cG fun s => (hG (s + 1)).1.1.continuous
  have hcoc : ∀ g h k, (χ g : ℤ_[p]) * cG (h, k) - cG (g * h, k) + cG (g, h * k) - cG (g, h) = 0 := by
    intro g h k
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    simpa only [map_sub, map_add, map_mul, map_zero] using (hG n).1.2 g h k
  let z0 : G × G → O := fun q => φ (cG q)
  have hz0 : z0 ∈ Z2 (twist ε O) := by
    refine (mem_cocycles2 _ _).2 ⟨hφ.comp hcc, fun g h k => ?_⟩
    simp only [twist_apply, smul_eq_mul, z0, hεφ]
    rw [← map_mul, ← map_sub, ← map_add, ← map_sub, hcoc, map_zero]
  let Z : H2 (twist ε O) := Submodule.Quotient.mk ⟨z0, hz0⟩
  refine ⟨Z, fun a b hab => ?_, fun y => ?_⟩
  · have h0 : (a - b) • Z = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 hab
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨f, hf, hfd⟩ := (separated_dvr_second_cohomology_mem _ _).1 h0
    refine sub_eq_zero.1 (GlobalTheory.T.fundamentalTwoCocycle_multiple_not_coboundary χ cG hcG φ ε hεφ ϖ hϖ hO.p_mem hopen (a - b) f hf
      fun g h => ?_)
    have e1 := congrFun hfd (g, h)
    rw [e1]
    rfl
  · induction y using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨a, ha⟩ := GlobalTheory.T.twoCocycle_fundamental_multiple_mod_pow χ cG hcG φ ε hεφ ϖ hϖ hO.p_mem hopen w.1 w.2
      refine ⟨a, ?_⟩
      show a • Z = Submodule.Quotient.mk w
      rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
      show (w.1 - a • z0) ∈ B2 (twist ε O)
      refine GlobalTheory.T.twoCocycle_mem_coboundaries_of_mod_uniformizer_pow ε ϖ hopen hbasis hfin _
        (sub_mem w.2 (Submodule.smul_mem _ a hz0)) fun n => ?_
      obtain ⟨b, hb, hbd⟩ := ha n
      exact ⟨b, hb, fun g h => by rw [hbd]; rfl⟩

end GlobalTheory.FreeTwistH2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLetterBasis
section
noncomputable section

namespace GlobalTheory.NL.LetterFree

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem letE_mul (i : ZMod n) (a : LetA O n) : (letE i : LetA O n) * a = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem single_mul_letE (i : ZMod n) (a : PowerSeries O) :
    (Pi.single i a : LetA O n) * letE i = Pi.single i a := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i :=
  single_mul_letE i 1

theorem letE_mul_ne {i j : ZMod n} (h : i ≠ j) : (letE i : LetA O n) * letE j = 0 := by
  rw [letE_mul]
  simp [letE, h]

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem sum_letE_smul [NeZero n] (x : W.DD T) : ∑ i : ZMod n, (letE i : LetA O n) • x = x := by
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem mem_Nl_iff (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(W.N T).smul_mem _ hy, ?_⟩
    change (letE i : LetA O n) • (letE i : LetA O n) • y = (letE i : LetA O n) • y
    rw [smul_smul, letE_mul_self]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, he⟩

theorem lettersDecompose [NeZero n] : GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersDecompose W T := by
  refine ⟨?_, le_antisymm (iSup_le fun i x hx => ((mem_Nl_iff W T i x).1 hx).1) fun x hx => ?_⟩
  · intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hk : (⨆ (j) (_ : j ≠ i), W.Nl T j) ≤
        LinearMap.ker (LinearMap.lsmul (LetA O n) (W.DD T) (letE i)) := by
      refine iSup_le fun j => iSup_le fun hj y hy => ?_
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ← ((mem_Nl_iff W T j y).1 hy).2, smul_smul,
        letE_mul_ne hj.symm, zero_smul]
    have h0 := hk hx'
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ((mem_Nl_iff W T i x).1 hx).2] at h0
    exact h0
  · rw [← sum_letE_smul W T x]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨x, hx, rfl⟩

theorem isLetterBasis {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsLetterBasis W T i (fun k => (letE i : LetA O n) • (b k : W.DD T)) := by
  have hli : LinearIndependent (LetA O n) (fun k => (b k : W.DD T)) :=
    b.linearIndependent.map' (W.N T).subtype (W.N T).ker_subtype
  refine ⟨fun k => ⟨b k, (b k).2, rfl⟩, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hy' : y = ∑ k, b.repr ⟨y, hy⟩ k • (b k : W.DD T) := by
    have := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    rw [AddSubmonoidClass.coe_finsetSum] at this
    exact this.symm
  generalize b.repr ⟨y, hy⟩ = a at hy'
  subst hy'
  have key : (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) =
      ∑ k, (Pi.single i (a k i) : LetA O n) • (b k : W.DD T) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, letE_mul]
  refine ⟨fun k => a k i, ?_, fun c hc => ?_⟩
  · change (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) = _
    rw [key]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, single_mul_letE]
  · change (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) = _ at hc
    rw [key] at hc
    simp only [smul_smul, single_mul_letE] at hc
    funext k
    have h0 := Fintype.linearIndependent_iff.1 hli
      (fun k => (Pi.single i (c k) : LetA O n) - Pi.single i (a k i))
      (by simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]) k
    have h1 := congrFun h0 i
    simpa [sub_eq_zero] using h1

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule

theorem exists_letter_basis {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n) :
    ∃ c : Module.Basis (Fin r) (PowerSeries O) ↥(W.Nl T i),
      ∀ k, (c k : W.DD T) = (letE i : LetA O n) • (b k : W.DD T) := by
  obtain ⟨hm, hu⟩ := isLetterBasis W T b i
  let f : Fin r → ↥(W.Nl T i) := fun k => ⟨_, hm k⟩
  have hs : ∀ c : Fin r → PowerSeries O, ((∑ k, c k • f k : ↥(W.Nl T i)) : W.DD T) =
      ∑ k, (Pi.single i (c k) : LetA O n) • (letE i : LetA O n) • (b k : W.DD T) := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul W T i (c k) (f k)
  have hli : LinearIndependent (PowerSeries O) f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 := hs c
    rw [hc] at h1
    have h2 := (hu 0 (Submodule.zero_mem _)).unique h1 (y₂ := fun _ => 0) (by simp)
    exact congrFun h2 k
  have hsp : ⊤ ≤ Submodule.span (PowerSeries O) (Set.range f) := by
    intro x _
    obtain ⟨c, hc, -⟩ := hu x.1 x.2
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, Subtype.ext ((hs c).trans hc.symm)⟩
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

end Generic

theorem letters_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersDecompose (H.W K s LL h) T ∧ GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersFree (H.W K s LL h) T ∧
      ∀ i, ∃ b : Fin (Module.finrank ↥(OL LL) ↥T.L.T) → (H.W K s LL h).DD T,
        GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsLetterBasis (H.W K s LL h) T i b := by
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨b⟩ := N_basis_loc H K s LL h T hT
  exact ⟨lettersDecompose _ T, fun i => ⟨(exists_letter_basis _ T b i).choose⟩,
    fun i => ⟨_, isLetterBasis _ T b i⟩⟩

end GlobalTheory.NL.LetterFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupUnderInertia
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
  GlobalTheory.ResSel GlobalTheory.TwistDet

namespace GlobalTheory.ResSel.SmallSub

theorem exists_fix_roots {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {n : ℕ}
    (hn : n ≠ 0) : ∃ K : Subgroup (G F Ω), IsOpen (K : Set (G F Ω)) ∧ (∀ a b : G F Ω, a * b * a⁻¹ * b⁻¹ ∈ K) ∧
      ∀ g ∈ K, ∀ ζ : Ω, ζ ^ n = 1 → g ζ = ζ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero n := ⟨hn⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have hp : ∀ ζ : Ω, ζ ^ n = 1 → ∃ k : ℕ, ξ ^ k = ζ := fun ζ h => by
    obtain ⟨k, -, hk⟩ := hξ.eq_pow_of_pow_eq_one h
    exact ⟨k, hk⟩
  have hc : ∀ a b : G F Ω, a (b ξ) = b (a ξ) := fun a b => by
    obtain ⟨j, hj⟩ := hp (a ξ) (by rw [← map_pow, hξ.pow_eq_one, map_one])
    obtain ⟨k, hk⟩ := hp (b ξ) (by rw [← map_pow, hξ.pow_eq_one, map_one])
    conv_lhs => rw [← hk, map_pow, ← hj]
    conv_rhs => rw [← hj, map_pow, ← hk]
    rw [← pow_mul, ← pow_mul, mul_comm]
  refine ⟨MulAction.stabilizer (G F Ω) ξ, stabilizer_isOpen_of_isIntegral ξ, fun a b => ?_, fun g hg ζ h => ?_⟩
  · show a (b (a⁻¹ (b⁻¹ ξ))) = ξ
    rw [hc a⁻¹ b⁻¹, mul_inv_apply, mul_inv_apply]
  · obtain ⟨k, rfl⟩ := hp ζ h
    have : g ξ = ξ := hg
    rw [map_pow, this]

theorem normal_of_comm {Γ : Type} [Group Γ] {K : Subgroup Γ} (h : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ K) : K.Normal :=
  ⟨fun k hk g => by simpa using K.mul_mem (h g k) hk⟩

theorem comm_mem_ker {Γ A : Type} [Group Γ] [CommGroup A] (φ : Γ →* A) (a b : Γ) : a * b * a⁻¹ * b⁻¹ ∈ φ.ker := by
  simp [MonoidHom.mem_ker]

theorem isOpen_ideal {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (h : IsAdic (IsLocalRing.maximalIdeal O)) {I : Ideal O} (hI : I ≠ ⊥) : IsOpen (I : Set O) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have := (isAdic_iff.1 h).1 n
  rwa [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hn] at this

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw)

theorem l_ne_zero : ((X.l i : ℕ) : X.O0 i) ≠ 0 := by
  intro h
  have : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  have h1 := (X.zk_prim i 1).neZero'.out
  apply h1
  have := congrArg (phiK X i 1) h
  simpa using this

theorem l_mem : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at h2
  exact X.O_l i h2

theorem exists_eps : ∃ K : Subgroup (GE N), IsOpen (K : Set (GE N)) ∧ (∀ a b : GE N, a * b * a⁻¹ * b⁻¹ ∈ K) ∧
    ∀ g ∈ K, IsLocalRing.residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1 := by
  refine ⟨((Units.map (IsLocalRing.residue (X.O0 i)).toMonoidHom).comp (eps0 X i)).ker, ?_, comm_mem_ker _,
    fun g hg => congrArg Units.val hg⟩
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hc : Continuous fun g : GE N => ‖((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) - 1‖ :=
    ((Units.continuous_val.comp (continuous_cycZ D.host.E N.Om (X.l i))).sub continuous_const).norm
  refine Filter.mem_of_superset ((isOpen_lt hc (continuous_const (y := (1 : ℝ)))).mem_nhds (by simp)) fun g hg => ?_
  obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hg
  apply Units.ext
  change IsLocalRing.residue (X.O0 i) (algebraMap ℤ_[X.l i] (X.O0 i) (cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ)) = 1
  rw [sub_eq_iff_eq_add.1 hc, map_add, map_add, map_one, map_one, map_mul, map_natCast, map_mul,
    (IsLocalRing.residue_eq_zero_iff _).2 (l_mem X i), zero_mul, zero_add]

theorem not_mem_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (v : PlE D.host)
    (h1 : v ∈ placesOver D.host.E p) : v ∉ placesOver D.host.E q := fun h2 => by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) := ((Nat.coprime_primes hp hq).mpr hne).cast
  obtain ⟨a, b, hab⟩ := hc
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  exact hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)

theorem pD_not_mem {v : PlE D.host} (hv : v ∈ X.pD i) :
    v ∉ placesOver D.host.E (X.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have hv' : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← X.pD_eq i]; exact hv
  have hl : (X.l i).Prime := (X.lPrime i).out
  split_ifs at hv' with h
  · exact ⟨not_mem_two D.host.pde'_prime hl (h ▸ D.host.pde_ne.symm) v hv',
      fun k => not_mem_two D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 v hv'⟩
  · exact ⟨not_mem_two D.host.pde_prime hl (Ne.symm h) v hv',
      fun k => not_mem_two D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 v hv'⟩

theorem exists_kerT (s : X.Sig i) {I : Ideal (X.O0 i)} (hI : I ≠ ⊥) : ∃ K : Subgroup (GE N), IsOpen (K : Set (GE N)) ∧
    K.Normal ∧ (∀ w, X.rhoS i s w = 1 → ∀ g, g * w * g⁻¹ * w⁻¹ ∈ K) ∧ ∀ g ∈ K, ∀ a b, (Tmat i s g - 1) a b ∈ I := by
  let φ : GE N →* GL (Fin D.R.r) (X.O0 i ⧸ I) := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (Tgl i s)
  have hφ : ∀ g, g ∈ φ.ker ↔ ∀ a b, (Tmat i s g - 1) a b ∈ I := by
    intro g
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff, ← Tgl_coe]
    refine forall₂_congr fun a b => ?_
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    have : ((1 : GL (Fin D.R.r) (X.O0 i ⧸ I)) : Matrix _ _ (X.O0 i ⧸ I)) a b =
        Ideal.Quotient.mk I ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) a b) := by
      rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [this]
    rfl
  refine ⟨φ.ker, ?_, inferInstance, fun w hw g => ?_, fun g hg => (hφ g).1 hg⟩
  · have h1 : Continuous fun g : GE N => (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) := by
      simp only [← map_inv]
      exact (X.twistCharacterFamily_continuous i _ _).comp continuous_inv
    have hc : Continuous (Tmat i s) := h1.smul (X.rhoS_cont i s)
    have e : (φ.ker : Set (GE N)) = ⋂ a, ⋂ b, (fun g => (Tmat i s g - 1) a b) ⁻¹' (I : Set (X.O0 i)) := by
      ext g
      simp only [SetLike.mem_coe, hφ, Set.mem_iInter, Set.mem_preimage]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_ideal (X.twistBaseCoefficientRing_isAdic i) hI).preimage ((hc.sub continuous_const).matrix_elem a b)
  · have h1 : Tgl i s w = scalGL D.R.r (chiS i s w)⁻¹ := by
      change scalGL _ _ * X.rhoS i s w = _
      rw [hw, mul_one]
    have h2 : Tgl i s (g * w * g⁻¹ * w⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1, ← scalGL_comm]
      group
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h2, map_one]

theorem exists_small : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (M : ℕ) (H : Subgroup (GE N)),
    IsOpen (H : Set (GE N)) → H.Normal →
    (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → Ine (F := D.host.E) A ≤ H) →
    ∃ L : Subgroup (GE N), IsOpen (L : Set (GE N)) ∧ L.Normal ∧ L ≤ H ∧ (∀ s ∈ T, Small i s L z) ∧
      (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ s ∈ T, ∀ g ∈ L, ∀ a b,
        (Tmat i s g - 1) a b ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) := by
  intro D N X bkP i T hT z hz M H hH hN hI
  obtain ⟨K₁, o₁, c₁, f₁⟩ := exists_fix_roots (F := D.host.E) (Ω := N.Om) (n := 2 * X.l i ^ M)
    (mul_ne_zero two_ne_zero (pow_ne_zero _ (X.lPrime i).out.ne_zero))
  obtain ⟨K₂, o₂, c₂, f₂⟩ := exists_eps X i
  have hne : Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) ≠ ⊥ :=
    mul_ne_zero (fun h => pow_ne_zero _ (l_ne_zero X i) (Ideal.span_singleton_eq_bot.1 h)) (IsDiscreteValuationRing.not_a_field _)
  choose K o n c f using fun s => exists_kerT X i s hne
  have := normal_of_comm c₁
  have := normal_of_comm c₂
  let H₀ : Subgroup (GE N) := H ⊓ (K₁ ⊓ (K₂ ⊓ ⨅ s : T, K s))
  have hK : (⨅ s : T, K s).Normal := Subgroup.normal_iInf_normal fun s => n s
  have hn₀ : H₀.Normal := inferInstance
  have ho₀ : IsOpen (H₀ : Set (GE N)) := by
    refine hH.inter (o₁.inter (o₂.inter ?_))
    change IsOpen ((⨅ s : T, K s : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun s => o s
  have hw : ∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ w ∈ Ine (F := D.host.E) A,
      ∀ g, g * w * g⁻¹ * w⁻¹ ∈ H₀ := fun v hv A hA w hw g =>
    ⟨H.mul_mem (hN.conj_mem _ (hI v hv A hA hw) g) (H.inv_mem (hI v hv A hA hw)), c₁ _ _, c₂ _ _,
      Subgroup.mem_iInf.2 fun s => c s w ((hT s s.2).1.1 v (pD_not_mem X i hv).1 (pD_not_mem X i hv).2 A hA w hw) g⟩
  have hL : IsOpen ((H₀ ⊓ H₀.comap (cConj X) : Subgroup (GE N)) : Set (GE N)) := ho₀.inter (isOpen_comap_cConj X ho₀)
  have hf : ∀ s ∈ T, ∀ g ∈ H₀ ⊓ H₀.comap (cConj X), ∀ a b,
      (Tmat i s g - 1) a b ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) :=
    fun s hs g hg => f s g (Subgroup.mem_iInf.1 hg.1.2.2.2 ⟨s, hs⟩)
  refine ⟨H₀ ⊓ H₀.comap (cConj X), hL, inferInstance, fun g hg => hg.1.1,
    fun s hs => ⟨hL, inferInstance, fun g g' hg => ?_, fun g => ?_, fun g hg => ⟨?_, f₂ g hg.1.2.2.1⟩⟩,
    fun g hg => f₁ g hg.1.2.1, hf⟩
  · obtain rfl : g' = cConj X g := AlgEquiv.ext hg
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, cConj_cConj]
    exact and_comm
  · obtain ⟨v, hv, A, hA, hzA, -⟩ := hz
    refine ⟨hw v hv A hA z hzA g, ?_⟩
    obtain ⟨v', hv'⟩ := exists_isConjPl v
    have hv'' : v' ∈ X.pD i := by
      rw [← Finset.mem_coe, X.pD_eq] at hv ⊢
      exact mem_placesOver_conj hv' hv
    have := hw v' hv'' _ (isPlaceOver_moveVal_cc X hv' hA) _ (cConj_mem_ine X hzA) (cConj X g)
    change cConj X _ ∈ H₀
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv]
  · ext a b
    have h0 : (Tmat i s g - 1) a b ∈ IsLocalRing.maximalIdeal (X.O0 i) := Ideal.mul_le_right (hf s hs g hg a b)
    have := (IsLocalRing.residue_eq_zero_iff _).2 h0
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.ResSel.SmallSub

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexOfIsOpenAbsGaloisFinExt
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.OpenFiniteIndex

theorem compactSpace_fixing (l : ℕ) [Fact l.Prime] (K : FinExt l) : CompactSpace ↥(GK K) := by
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  have hc : IsClosed ((K.1.fixingSubgroup : Subgroup (GQ l)) : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed K.1
  exact isCompact_iff_compactSpace.mp hc.isCompact

theorem finiteIndex_of_isOpen : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (H : Subgroup ↥(GK K)),
    IsOpen (H : Set ↥(GK K)) → H.FiniteIndex := by
  intro l _ K H hH
  haveI := compactSpace_fixing l K
  haveI : Finite (↥(GK K) ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  exact Subgroup.finiteIndex_of_finite_quotient

end GlobalTheory.OpenFiniteIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReductionStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_gamma_eq_deltaPi_teichmuller : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], (∃ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧ ∀ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap S.O k) a)) ∧ ∃ e : {δ // δ ∈ (S.W H).DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap S.O k) a) := by
  first | exact @GlobalTheory.RedAct.gamma_action_reduction | exact GlobalTheory.RedAct.gamma_action_reduction | (intros; apply GlobalTheory.RedAct.gamma_action_reduction <;> assumption)
end

