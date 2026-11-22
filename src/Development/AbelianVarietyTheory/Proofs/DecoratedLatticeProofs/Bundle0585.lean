import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0034
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0582
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0579
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
import Formalism.LocalToGlobal.Columns.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0583
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0491
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0573
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0534
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrsFBaseEqSelf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm GlobalTheory.QTw
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QTw

theorem frsF_base_eq_self : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀), A.Is → I.Ok → ∀ (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (i : ℕ), i ≤ B.R.m → ∀ (β : Ch₀ i), (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A.kb i β) = 1) → ∀ (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i β).1.1 P x = x := by
  intro B X I l Z u a Ch₀ A hA hI P hP i hi β hv x
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal := by
    intro hm
    apply GlobalTheory.KerT.T_notMem_rowSG (I.tup a) (GlobalTheory.BasePrimes.primes_ok B X).1 hI.sel_ok (hI.T_mem u) P.1 P.2
    have := Ideal.mem_comap.1 hm
    simpa [map_natCast] using this
  have hk := hv _ hT
  have hpt := (hA.base i hi β).1
  have hfr := hpt.fr ⟨P.1, hSQ⟩
  rw [frsF_eq_ptFr, ← extTo_fr I.SQ _ ⟨P.1, hSQ⟩]
  set f := (extTo I.SQ (A.p0 i β).1.1).fr ⟨P.1, hSQ⟩ with hf
  have key : ∀ j : Fin (B.R.N i), f (Pi.single j 1) = Pi.single j 1 := by
    intro j
    funext r
    have h1 := hfr r j
    rw [GlobalTheory.Mem.Col2.ZeroMove.adAt_entry_one P.1 hk r j] at h1
    apply (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)).injective
    rw [← h1, Pi.single_apply]
    split_ifs <;> simp
  have : (f : Formalism.L2.Col.Sp B.fields.E (B.R.N i) →ₗ[B.fields.E] Formalism.L2.Col.Sp B.fields.E (B.R.N i)) = LinearMap.id :=
    LinearMap.pi_ext' fun j => LinearMap.ext_ring (key j)
  exact congrArg (fun g => g x) this

end GlobalTheory.QTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LevelData

open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge GlobalTheory.LocMod
open Formalism.L2.Col (IntAt redP qOf)

section Gen

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def reFrame {N n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (M : Matrix (Fin N) (Fin n) k) (M' : Matrix (Fin n) (Fin N) k)
    (h : M * M' = 1) (h' : M' * M = 1) (e : Y ≃ Fin n) : Frame k N Y :=
  ⟨M.submatrix id e, M'.submatrix e id, by rw [submatrix_mul_equiv, h, submatrix_id_id],
    by rw [← Equiv.coe_refl, submatrix_mul_equiv, h', submatrix_one_equiv]⟩

variable {u : D.what₂.Word}

end Gen

section Chain

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_iff {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}
    (hi : ∀ x, ι x ∈ 𝒪[k] ↔ IntAt P x) (a : E) : valuation k (ι a) < 1 ↔ P.valuation E a < 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have h := hi a⁻¹
  rw [GlobalTheory.AtTypeExists.intAt_iff, Valuation.mem_integer_iff, map_inv₀, map_inv₀, map_inv₀,
    inv_le_one₀ (zero_lt_iff.2 (by simpa using ha)), inv_le_one₀ (zero_lt_iff.2 (by simpa using ha))] at h
  rw [← not_le, ← not_le, h]

theorem exists_unif {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}
    (hi : ∀ x, ι x ∈ 𝒪[k] ↔ IntAt P x) (hd : DenseRange ι) (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    ∃ ϖ : kˣ, (ϖ : k) = ι (qOf P : E) ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ := by
  have hq := GlobalTheory.AtTypeExists.valuation_norm P h
  have h0 : ((qOf P : ℕ) : E) ≠ 0 := fun e => by
    rw [e, map_zero] at hq
    exact WithZero.exp_ne_zero hq.symm
  have h1 : valuation k (ι (qOf P : E)) < 1 := by
    rw [val_lt_one_iff hi, hq, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨Units.mk0 _ ((map_ne_zero ι).2 h0), rfl, fun x => ⟨fun hx => ?_, fun hx => lt_of_le_of_lt hx h1⟩⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have h2 : {y : k | valuation k (y - x) < valuation k x} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨Units.mk0 (valuation k x) (by simpa using hx0), by simp⟩
  obtain ⟨a, ha⟩ := hd.mem_nhds h2
  have h3 : valuation k (ι a) = valuation k x := by simpa using Valuation.map_add_eq_of_lt_right (valuation k) ha
  have h4 : P.valuation E a < 1 := (val_lt_one_iff hi a).1 (h3 ▸ hx)
  have h5 : IntAt P (a / (qOf P : E)) := by
    rw [GlobalTheory.AtTypeExists.intAt_iff, map_div₀, hq, div_le_one₀ WithZero.exp_pos]
    by_cases ha0 : P.valuation E a = 0
    · simp [ha0]
    · rw [← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h4
      rw [← WithZero.exp_log ha0, WithZero.exp_le_exp]
      omega
  have h6 := (hi _).2 h5
  rw [Valuation.mem_integer_iff, map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ((map_ne_zero ι).2 h0))), h3] at h6
  exact h6

theorem mul_sec (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (y : k) : x * q.sec y = q.sec (q.pr x * y) := by
  have h := q.sec_pr (x * q.sec y)
  have h' := q.sec_pr (q.sec y)
  rw [map_mul, q.pr_sec] at h
  rw [q.pr_sec] at h'
  rw [h, mul_left_comm, ← h']

end Chain

section Place

end Place

section World

variable {B : Base} {X : PreX B.toPre}

theorem type_prime {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ (B.primes X).vGs) :
    ∃ i, qOf P = B.host.g i ∧ (B.host.g i).Prime ∧ ((B.host.g i : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal ∧
      ((B.host.g i : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal ^ 2 ∧ B.host.g i ∉ B.host.small ∧ B.host.g i ≠ B.host.q ∧ B.host.g i ≠ B.host.d ∧
      B.fields.conjO (X.piG i) ∈ P.asIdeal ∧ X.piG i ∉ P.asIdeal ∧ ∀ v, X.piT v - 1 ∈ P.asIdeal := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨i, hi⟩ : ∃ i, P ∈ (B.primes X).vG i := by
    unfold Formalism.L2.Col.Primes.vGs at hP
    rcases Finset.mem_union.1 hP with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  obtain ⟨h1, h2⟩ := GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hPr i P hi
  have hp : (B.host.g i).Prime := hPr.g_prime i
  have key : ¬ B.host.g i ∣ B.host.QS * B.host.q * B.host.d := fun h => by
    have h3 : B.host.g i ≡ 1 [MOD B.host.g i] := (hPr.g_cong i).of_dvd h
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd).1 (h3.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))))
  have hc : B.fields.conjO (X.piG i) ∈ P.asIdeal := by
    unfold Formalism.L2.Col.Primes.vG Formalism.L2.Col.divs at hi
    split_ifs at hi with h
    · exact h.mem_toFinset.1 hi
    · simp at hi
  refine ⟨i, hPr.vG_norm i P hi, hp, h1, h2, B.host.toHostRaw.notMem_small_of_not_dvd key,
    B.host.toHostRaw.ne_q_of_not_dvd key, B.host.toHostRaw.ne_d_of_not_dvd key, hc, fun h => ?_, fun v => ?_⟩
  · obtain ⟨x, y, e⟩ := hPr.piG_cop i
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hc)))
  · refine Ideal.mem_of_dvd _ (dvd_trans ?_ (hPr.piT_cong v)) h1
    refine Nat.cast_dvd_cast (Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _)
    fin_cases i
    exacts [dvd_mul_right _ _, dvd_mul_left _ _]

end World

end GlobalTheory.SeeSaw.LevelData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActOnRamifiedColumns
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TwSProof

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem ramAt_fixed {p₀ : SplitPt D k} {β : Frame p₀ S n} {P : Pair k n} {φ₀ : GA D S → ℂ} (h : GlobalTheory.FinPl.RamAt β P φ₀) {g : GL n k}
    (hg : g • P = P) : rTrans (β.gl g) φ₀ = φ₀ := by
  obtain ⟨φ, ⟨heq, -, -⟩, rfl⟩ := h
  have := heq g P
  rw [hg] at this
  exact this.symm

theorem comb_foldr (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ i) 1) (η : ι → 𝓀[k]ˣ) (J : List ι) :
    ∃ c : GA D S →₀ ℂ, (∀ g ∈ c.support, g ∈ grpAt S fun x => ∃ i, x = (p i).v) ∧
      ∀ φ, J.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) φ = trc c φ := by
  have hsub : ∀ i, grpAt S (· = (p i).v) ≤ grpAt S fun v => ∃ i, v = (p i).v :=
    fun i => AllBij.congGrp_mono S (AllBij.idAt_mono fun v hv => ⟨i, hv⟩)
  induction J with
  | nil =>
    refine ⟨Finsupp.single 1 1, fun g hg => ?_, fun φ => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]; exact Subgroup.one_mem _
    · exact (AllBij.act_single_one φ).symm
  | cons i l ih =>
    obtain ⟨c, hc, hl⟩ := ih
    obtain ⟨-, -, C, -, hC, -⟩ := ramBijective_holds D k (p i) n q (χ i) (hχ i) _ rfl (η i) S (β i) (Q i)
    refine ⟨AllBij.cmul (Finsupp.mapDomain (β i).gl C) c, fun g hg => ?_, fun φ => ?_⟩
    · exact AllBij.cmul_mem (S := grpAt S fun v => ∃ i, v = (p i).v)
        (fun g h => hsub i (AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) C g h))
        (fun g h => hc g (Finsupp.mem_support_iff.2 h)) g (Finsupp.mem_support_iff.1 hg)
    · show sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) (l.foldr _ φ) = _
      rw [hl, hC, AllBij.sum_rep_eq]
      exact (AllBij.act_cmul _ _ _).symm

theorem sOp_keeps (hinj : Function.Injective fun i => (p i).v) (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : 𝓀[k]ˣ) (i : ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') φ) :
    IsContAut S (sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ) ∧
      ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') (sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ) := by
  obtain ⟨hbij, -, c, -, hc, -⟩ := ramBijective_holds D k (p i) n q (χ i) (hχ i) _ rfl ε S (β i) (Q i)
  have hT : ∀ φ, sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ = AllBij.act (Finsupp.mapDomain (β i).gl c) φ :=
    fun φ => (hc φ).trans (AllBij.sum_rep_eq _ _ _)
  have hC := AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) c
  refine ⟨by rw [hT]; exact AllBij.isContAut_act _ hφ.1, fun i' => ?_⟩
  rcases eq_or_ne i' i with rfl | hne
  · exact hbij.mapsTo (hφ.2 i')
  · rw [hT]
    exact AllBij.ramAt_act _ _ _ (fun x hx g => AllBij.grpAt_comm S (fun e => hne (hinj e)) (hC x hx)
      (AllBij.gl_mem _ g)) (hφ.2 i')

theorem foldr_keeps (hinj : Function.Injective fun i => (p i).v) (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : ι → 𝓀[k]ˣ) (l : List ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') φ) :
    IsContAut S (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (ε i) φ') φ) ∧
      ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (ε i) φ') φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact sOp_keeps hinj β Q q χ hχ (ε i) i ih

end Local

theorem twS : TwS' := by
  intro B X I hOk hPins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hStd J q χ hχ
  have hinj : Function.Injective fun i => (p i).v := GlobalTheory.T.splitPoints_lie_over_distinct_places I hOk hPins l Z u p β Q L hStd
  have key : ∀ j (hj : j ≤ B.R.m) φ, RamT (I := I) (l := l) (u := u) (a := a) j φ → ∀ η : ι → 𝓀[k]ˣ,
      ∃ φ', RamT (I := I) (l := l) (u := u) (a := a) j φ' ∧ ∀ b y, A.rd θ j hj b φ' y =
        J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
    intro j hj φ hφ η
    obtain ⟨c, hc, hfold⟩ := comb_foldr (β j) (Q j) q χ hχ η J
    have hram := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ.1
    have hR : ∀ b y, IsContAut _ (trc c (A.rd θ j hj b φ y)) ∧
        ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (trc c (A.rd θ j hj b φ y)) := by
      intro b y
      rw [← hfold]
      exact foldr_keeps hinj (β j) (Q j) q χ hχ η J ⟨hram.1 b y, fun i => hram.2.1 hφ b y i⟩
    obtain ⟨φ', hφ'F, hφ'⟩ := GlobalTheory.T.twistTranslationsActAtLevelPrime_proof I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj c hc φ hφ.1
      (fun b y i g hg => ramAt_fixed ((hR b y).2 i) hg)
    refine ⟨φ', ?_, fun b y => (hφ' b y).trans (hfold _).symm⟩
    have hram' := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ' hφ'F
    exact hram'.2.2 fun b y i => by rw [hφ' b y]; exact (hR b y).2 i
  classical
  refine ⟨fun j η φ => if h : j ≤ B.R.m ∧ RamT (I := I) (l := l) (u := u) (a := a) j φ then
    (key j h.1 φ h.2 η).choose else φ, ?_⟩
  intro j hj φ hφ
  have hram := GlobalTheory.T.twistRamified_iff_scalarFormsRamified I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ.1
  refine ⟨fun b y => ⟨hram.1 b y, fun i => hram.2.1 hφ b y i⟩, fun η => ?_⟩
  have h : j ≤ B.R.m ∧ RamT (I := I) (l := l) (u := u) (a := a) j φ := ⟨hj, hφ⟩
  simp only [dif_pos h]
  exact (key j hj φ hφ η).choose_spec

end GlobalTheory.AdForm.TwSProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftNearOne
section
noncomputable section

namespace GlobalTheory.SeeSaw.BaseFrame

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.DetSpec Matrix

theorem near_left {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    {C M : Matrix (Fin n) (Fin n) K} (hC : ∀ i j, v (C i j) ≤ 1) (hM : ∀ i j, v (M i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1)
    (h : ∀ i j, v ((C * M) i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1) (i j : Fin n) :
    v (C i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1 := by
  have e : C - 1 = (C * M - 1) - C * (M - 1) := by rw [mul_sub, mul_one]; abel
  have e2 := congrFun (congrFun e i) j
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply (M := C) (N := M - 1)] at e2
  rw [e2]
  refine Valuation.map_sub_lt _ (h i j) (Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_)
  rw [map_mul]
  exact (mul_le_of_le_one_left' (hC i l)).trans_lt (hM l j)

theorem near_right {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    {C M : Matrix (Fin n) (Fin n) K} (hM : ∀ i j, v (M i j) ≤ 1) (hC : ∀ i j, v (C i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1)
    (h : ∀ i j, v ((C * M) i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1) (i j : Fin n) :
    v (M i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1 := by
  have e : M - 1 = (C * M - 1) - (C - 1) * M := by rw [_root_.sub_mul, one_mul]; abel
  have e2 := congrFun (congrFun e i) j
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply (M := C - 1) (N := M)] at e2
  rw [e2]
  refine Valuation.map_sub_lt _ (h i j) (Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_)
  rw [map_mul]
  exact (mul_le_of_le_one_right' (hM l j)).trans_lt (hC i l)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem kMat_mul (P : HeightOneSpectrum (𝓞 E)) (g k : GL (Fin n) (AfE F E)) (f : Sp E n ≃ₗ[E] Sp E n) :
    kMat P (g * k) f = kMat P k 1 * kMat P g f := by
  ext1 i j
  have e : ∀ l, kMat P k 1 i l = adAt F P ((k⁻¹ : GL (Fin n) (AfE F E)).1 i l) := fun l => by
    show adAt F P (Col2.pullV k (Pi.single l 1) i) = _
    unfold Col2.pullV
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single l]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [Matrix.mul_apply]
  simp only [e]
  unfold kMat Col2.pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct, map_sum]
  simp only [map_mul]

theorem kMat_one (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n) (i j : Fin n) :
    kMat P (1 : GL (Fin n) (AfE F E)) f i j = algebraMap E _ (f (Pi.single j 1) i) := by
  unfold kMat Col2.pullV
  rw [inv_one, Units.val_one, Matrix.one_mulVec, adAt_inclE]

variable [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem lift_near_one {y k k' : GL (Fin n) (AfE F E)} {p p₀ : DecoF E n ST SG Q} (h : IsPtOf hc (y * k) p) (h' : IsPtOf hc (y * k') p)
    (h₀ : IsPtOf hc k' p₀) (hN : p₀.deco.1.N = stdLat E n) (w : SG) (hk : bc (prV (E := E) (w.1.under (𝓞 F))) k = 1)
    {f : Sp E n ≃ₗ[E] Sp E n} (hf : TopStep.IsLiftFr p₀.deco.1 w f) (i j : Fin n) :
    w.1.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1 := by
  have hl := TopStep.liftFr_spec p.deco.2 w
  have h1 := val_kMat_sub_lt h w hl
  have h2 := val_kMat_sub_lt h' w hl
  have h3 := val_kMat_sub_lt h₀ w hf
  have e1 : kMat w.1 (y * k) (p.deco.1.liftFr w) = kMat w.1 y (p.deco.1.liftFr w) := by
    ext1 a b
    exact ZeroMove.adAt_pullV_mul w.1 y hk _ a
  rw [e1] at h1
  rw [kMat_mul] at h2
  rw [← one_mul k', kMat_mul] at h3
  have hc1 : Formalism.L2.Herm.Carries (1 : GL (Fin n) (AfE F E)) (stdLat E n) (stdLat E n) := fun x => by simp
  have i1 := val_kMat_le (P := w.1) (f := 1) (hN ▸ h₀.lat : Formalism.L2.Herm.Carries k' (stdLat E n) (stdLat E n)) fun _ => Iff.rfl
  have i2 := val_kMat_le (P := w.1) (f := f) hc1 (hN ▸ hf.1 : CharValCompare.IsFr w.1 (stdLat E n) f)
  have h4 := near_right _ i2 (near_left _ i1 h1 h2) h3 i j
  rw [kMat_one, Matrix.one_apply, if_congr (Fin.ext_iff (a := i) (b := j)) rfl rfl] at h4
  rw [← valued_algebraMap, map_sub, apply_ite (algebraMap E _), map_one, map_zero]
  exact h4

end Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.SeeSaw.BaseFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfEqOfEqOnRationalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_half_eq_of_eq_on_rational : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf E₂ (stdHom S T) Φ₁ → IsSBHalf E₂ (stdHom S T) Φ₂ → (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Φ₁ (γ.map fun a => E₂ * incA D a) = Φ₂ (γ.map fun a => E₂ * incA D a)) → Φ₁ = Φ₂ := by
  first | exact @GlobalTheory.RatHalfDense.eq_of_rat | exact GlobalTheory.RatHalfDense.eq_of_rat | (intros; apply GlobalTheory.RatHalfDense.eq_of_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegralLawLastStepsOfLocalFactoriStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawIteratedIntegralLawLastSteps_of_localFactorisation : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QLast v w := by
  first | exact @GlobalTheory.QLastPf.qLast_of_pin | exact GlobalTheory.QLastPf.qLast_of_pin | (intros; apply GlobalTheory.QLastPf.qLast_of_pin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLevelPrimeLawAllTuplesStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_levelPrime_law_all_tuples : ∀ D : D7, GlobalTheory.SeeSaw.TOfShape D := by
  first | exact @GlobalTheory.LevPrimeAll.lawLevelPrime_all | exact GlobalTheory.LevPrimeAll.lawLevelPrime_all | (intros; apply GlobalTheory.LevPrimeAll.lawLevelPrime_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawPlaceLawsGiveFiniteIntegralLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem placeLaws_finiteIntegrals : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c)
    (w : ∀ s, VTup (t s)), c.Is → c.VolLast → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) →
    (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  intro D c v 𝒯 t w hc hvl hv ht hp
  refine ⟨fun s => ?_, ?_, ?_⟩
  · exact GlobalTheory.T.locally_finite_of_tuple_conditions D c v (t s) (w s) hc hv (ht s) (hp s).form (hp s).off (hp s).gs (hp s).qfin
  · exact GlobalTheory.T.seeSaw_finiteIntegrals_doubleStep_value D c v 𝒯 t w hc hv ht hp (GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D) (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.seeSawWeilBiAction_commutes D)
  · exact GlobalTheory.T.seeSawLastTwoSteps_doubleLiftPeriod_value D c v 𝒯 t w hc hvl hv ht hp (GlobalTheory.Unf.LastSteps.lastLaw D) (GlobalTheory.T.lastSeeSaw_thetaIdentity D)
      (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.seeSawWeilBiAction_commutes D)

end GlobalTheory.SeeSaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawSupportOffLevelOfLatticeShapeStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_support_off_level_of_lattice_shape : ∀ D : D7, GlobalTheory.SeeSaw.OffOfShape D := by
  first | exact @GlobalTheory.SeeSaw.offOfShape_all | exact GlobalTheory.SeeSaw.offOfShape_all | (intros; apply GlobalTheory.SeeSaw.offOfShape_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_scalar : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (F0 W u).cls0.lev.U → ∀ (i : Fin a.n) (x : (a.G i).S.P.J), (∀ (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r), p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q → ∀ z : 𝓞 (I.rec7 l Z).host.E, Ideal.Quotient.mk (a.pl i).1.asIdeal z = (GlobalTheory.FamTraceChi.reductionYZero W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q' → valuation (a.G i).k (((x : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k)).val p q - (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) < 1) → (((a.G i).S.P.lam x : ℂˣ) : ℂ) = GlobalTheory.FamTraceChiCol.colLam (F0 W u) ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)) (y : GL _ _) := by
  first | exact @GlobalTheory.FamTraceChiCol.lam_eq_colLam | exact GlobalTheory.FamTraceChiCol.lam_eq_colLam | (intros; apply GlobalTheory.FamTraceChiCol.lam_eq_colLam <;> assumption)
end

