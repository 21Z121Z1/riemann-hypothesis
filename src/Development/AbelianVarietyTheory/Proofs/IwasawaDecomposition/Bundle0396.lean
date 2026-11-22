import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransferOfFundamentalDomains
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Formalism.LocalToGlobal.Columns.Bundle0008
import Formalism.LocalToGlobal.Divisibility.RowSideTie

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedEvaluationSquareIntegrableNormAllRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.EvalAllRows

theorem eq_zero_of_units {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (T : MMap M)
    (h : ∀ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) → T v = 0) : T = 0 := by
  classical
  refine MultilinearMap.ext fun v => ?_
  by_cases hz : ∃ τ, v τ = 0
  · obtain ⟨τ, hτ⟩ := hz
    exact T.map_coord_zero τ hτ
  · push_neg at hz
    have hn : ∀ τ, ‖(v τ : M.H τ)‖ ≠ 0 := fun τ e => hz τ (Subtype.ext (norm_eq_zero.1 e))
    let u : M.Vec := fun τ => ((‖(v τ : M.H τ)‖⁻¹ : ℝ) : ℂ) • v τ
    have hu : ∀ τ, ‖(u τ : M.H τ)‖ = 1 := fun τ => by
      simp only [u, Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (hn τ)
    have hv : v = fun τ => ((‖(v τ : M.H τ)‖ : ℝ) : ℂ) • u τ := by
      funext τ
      simp only [u, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hn τ), Complex.ofReal_one, one_smul]
    rw [hv, T.map_smul_univ, h u hu, smul_zero]
    rfl

end GlobalTheory.EvalAllRows

theorem GlobalTheory.EvalAllRows.evalTranslate_norm_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ MultR R F, MemLp (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) 2 (muX X) ∧ ∫ x, ‖ev (MP R) v₀ S ((iotaX X h).symm x * t)‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  intro _ hCusp _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hHE hGap hL hinf hν0 hsee
  haveI hνH : R.ν0.IsHaarMeasure := hν0.1.1
  obtain ⟨c, hc, hmap⟩ := @GlobalTheory.EvalNormTransfer.exists_map_eq_smul D X h R.ν0 hνH
  obtain ⟨hι, hιs⟩ := measurable_of_borel X (iotaX X h) (GlobalTheory.EvalNormTransfer.borel_inst X)
  have hTr : SquareIntegrableTransfer R.ν0 R.fd0 X (iotaX X h).toMulEquiv t c :=
    squareIntegrableTransfer_of_rational_points R.ν0 R.fd0 X _ t c hι hιs hc hmap hνH hν0.2 (GlobalTheory.EvalNormTransfer.iotaX_rat X h)
  refine ⟨c, hc, fun v₀ hv S hS => ?_⟩
  have hSch : ∀ S' ∈ MultR R F, ∃ c', IsMultIP (MP R) R.ν0 R.fd0 S' S' c' := fun S' hS' =>
    GlobalTheory.MultFinite.schurMult hCusp R.ν0 R.fd0 hinf hνH hν0.2 S' hS' S' hS'
  have hcont : ∀ S' ∈ MultR R F, ∀ v, Continuous (S' v) ∧ ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S' v (γ * g) = S' v g :=
    fun S' hS' v => Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (M := R.MY 0) (θ := R.θ) (J := JR R F) (χ := chiR R F) hS' v
  haveI : BorelSpace (GA D (D.sp.Y 0)) := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (Yc D 0)
  have hL2 : ∀ S' ∈ MultR R F, ∀ v, MemLp (S' v) 2 (R.ν0.restrict R.fd0) := by
    intro S' hS' v
    obtain ⟨c', hip⟩ := hSch S' hS'
    refine (memLp_two_iff_integrable_sq_norm (hcont S' hS' v).1.measurable.aestronglyMeasurable).2
      (((hip v v).1).norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨hm, hn⟩ := hTr (S v₀) (hcont S hS v₀).1 (hcont S hS v₀).2 (hL2 S hS v₀)
  refine ⟨hm, hn.trans (congrArg (c * ·) (re_ipM_eq (hSch S hS) hv).symm), ?_⟩
  intro h0
  refine GlobalTheory.EvalAllRows.eq_zero_of_units (MP R) S fun v hv' => ?_
  by_contra hne
  have hre := re_ipM_eq (hSch S hS) hv'
  have hint : IntegrableOn (fun x => ‖S v x‖ ^ 2) R.fd0 R.ν0 :=
    (memLp_two_iff_integrable_sq_norm (hL2 S hS v).1).1 (hL2 S hS v)
  have hp := Formalism.IndefR.PeterssonHilbertSpace.petPos (D.sp.Y 0) R.ν0 R.fd0 hνH hν0.2 (S v) (hcont S hS v).1 (hcont S hS v).2 hne hint
  rw [← hre, h0] at hp
  exact lt_irrefl _ hp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIs
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TupTie

section

variable {L : Type} [Field L] [NumberField L]

def Good (F : Type) [Field F] [NumberField F] [Algebra F L] (χ : HChar L) : Prop :=
  (∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) ∧ χ.TrivOn F ∧ ∀ v, χ.TameAt v

variable {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem resFin_mul (χ χ' : HChar L) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    (χ * χ').resFin v k = χ.resFin v k * χ'.resFin v k := by
  simp only [HChar.resFin, MonoidHom.finsetProd_apply, ← Finset.prod_mul_distrib]
  rfl

theorem resInf_mul (χ χ' : HChar L) (v : InfinitePlace F) (k : Fˣ) :
    (χ * χ').resInf v k = χ.resInf v k * χ'.resInf v k := by
  simp only [HChar.resInf, MonoidHom.finsetProd_apply, ← Finset.prod_mul_distrib]
  rfl

theorem good_one : Good F (1 : HChar L) := by
  refine ⟨⟨1, one_pos, one_pow 1⟩, ⟨fun v k => ?_, fun v k => ?_⟩, fun _ _ _ _ => rfl⟩
  · simp only [HChar.resFin, MonoidHom.finsetProd_apply]
    exact Finset.prod_eq_one fun _ _ => rfl
  · simp only [HChar.resInf, MonoidHom.finsetProd_apply]
    exact Finset.prod_eq_one fun _ _ => rfl

theorem Good.mul {χ χ' : HChar L} (h : Good F χ) (h' : Good F χ') : Good F (χ * χ') := by
  obtain ⟨⟨n, hn, h1⟩, h2, h3⟩ := h
  obtain ⟨⟨n', hn', h1'⟩, h2', h3'⟩ := h'
  refine ⟨⟨n * n', Nat.mul_pos hn hn', ?_⟩, ⟨fun v k => ?_, fun v k => ?_⟩, fun v x hx hx' => ?_⟩
  · unfold HChar.OrderDvd at *
    rw [mul_pow, pow_mul, h1, one_pow, pow_mul', h1', one_pow, one_mul]
  · rw [resFin_mul, h2.1, h2'.1, one_mul]
  · rw [resInf_mul, h2.2, h2'.2, one_mul]
  · rw [HChar.loc_mul, h3 v x hx hx', h3' v x hx hx', one_mul]

end

theorem good_set {B : Base} (f : Fr B.toPre) (T : TwDat B) {χ : HChar B.host.E} (h : χ ∈ T.set f) : Good B.host.F χ := by
  have hd : Good B.host.F f.del := ⟨f.isDel.fin, f.isDel.triv, f.isDel.tame⟩
  have hd' : Good B.host.F f.del' := ⟨f.isDel'.fin, f.isDel'.triv, f.isDel'.tame⟩
  rcases h with (rfl | rfl | rfl) | ⟨w, rfl⟩
  · exact good_one
  · exact hd
  · exact hd'
  · have hp : Good B.host.F (T.psi w) := ⟨(T.psi_tw w).1, (T.psi_tw w).2.1, (T.psi_tw w).2.2.1⟩
    unfold TwDat.xiTw
    split_ifs
    · exact hd'.mul hp
    · exact hd.mul hp

end GlobalTheory.Mem.Top.TupTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlace
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section
namespace GlobalTheory.Mem.HD.RamBoth

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
  simpa using h

theorem exists_intCast_cong {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (z : w.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ k : ℤ, Valued.v (algebraMap E (w.adicCompletion E) (k : E) - z) ≤ WithZero.exp (-1 : ℤ) := by
  obtain ⟨b, hb⟩ := GlobalTheory.CMVal.Euler.SplitPair.exists_int_cong w z hz
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Fact (Nat.card (𝓞 E ⧸ w.asIdeal)).Prime := ⟨hc ▸ hp⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  have htop : AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) = ⊤ := by
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card (AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal)) with h | h
    · exfalso
      have : (1 : 𝓞 E ⧸ w.asIdeal) ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := AddSubgroup.mem_zmultiples 1
      rw [h, AddSubgroup.mem_bot] at this
      exact one_ne_zero this
    · exact h
  obtain ⟨k, hk⟩ : Ideal.Quotient.mk w.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := htop ▸ AddSubgroup.mem_top _
  have hk' : ((k : 𝓞 E ⧸ w.asIdeal)) = Ideal.Quotient.mk w.asIdeal b := by simpa using hk
  have hmem : b - (k : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hk', map_intCast, sub_self]
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((b : E) - (k : E))) ≤ WithZero.exp (-1 : ℤ) := by
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval]
    refine le_exp_neg_one_of_lt_one ?_
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (b - (k : 𝓞 E))).2 hmem
    simpa using this
  have hb' : Valued.v (algebraMap E (w.adicCompletion E) (b : E) - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hb
  refine ⟨k, ?_⟩
  have := Valuation.map_sub_le _ (hb'.trans (by simp)) h1
  rw [map_sub (algebraMap E (w.adicCompletion E)), sub_sub_sub_cancel_left] at this
  exact this

theorem mem_aboveF_iff (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {R : HeightOneSpectrum (𝓞 D.host.E)} :
    R ∈ aboveF (L := D.host.E) D.host.F v ↔ R.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl

open Classical in

theorem aboveF_eq_pair (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w P : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ aboveF (L := D.host.E) D.host.F v) (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (hne : w ≠ P) :
    aboveF (L := D.host.E) D.host.F v = {w, P} := by
  haveI := v.isMaximal
  haveI : NoZeroSMulDivisors (𝓞 D.host.F) (𝓞 D.host.E) := ⟨fun {c x} e => by
    rw [Algebra.smul_def, mul_eq_zero,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))] at e
    exact e⟩
  have h1 := Ideal.card_primesOverFinset_le_finrank (𝓞 D.host.E) D.host.F D.host.E v.ne_bot
  rw [D.sp.cm.deg2] at h1
  have h2 : (aboveF (L := D.host.E) D.host.F v).card ≤ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 D.host.E)).card := by
    refine Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal (fun R hR => ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rw [Finset.mem_coe, mem_aboveF_iff] at hR
    rw [IsDedekindDomain.coe_primesOverFinset v.ne_bot]
    exact ⟨R.isPrime, ⟨hR ▸ rfl⟩⟩
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro R hR
    rw [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl <;> assumption
  · rw [Finset.card_pair hne]; omega

theorem unrAt_of_pair {E : Type} [Field E] [NumberField E] {F : Type} [Field F] [NumberField F] [Algebra F E]
    [DecidableEq (HeightOneSpectrum (𝓞 E))] (χ : HChar E) {v : HeightOneSpectrum (𝓞 F)} {w P : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 F) = v) (hP : P.under (𝓞 F) = v) (hne : w ≠ P) (hS : aboveF (L := E) F v = {w, P})
    (hp : (Ideal.absNorm w.asIdeal).Prime) (hF : χ.TrivOn F) (ht : χ.TameAt w) (hun : χ.UnrAt P) : χ.UnrAt w := by
  intro u hu
  have hu1 : Valued.v (u : w.adicCompletion E) = 1 := hu
  obtain ⟨k, hk⟩ := exists_intCast_cong w hp u hu1.le
  have hval : ∀ (R : HeightOneSpectrum (𝓞 E)), Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = 1 ↔
      (k : 𝓞 E) ∉ R.asIdeal := fun R => by
    have h1 : Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = R.valuation E (k : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' R (k : E)
    have h2 : R.valuation E (k : E) = R.intValuation (k : 𝓞 E) := by
      rw [← map_intCast (algebraMap (𝓞 E) E) k]
      exact HeightOneSpectrum.valuation_of_algebraMap (K := E) R (k : 𝓞 E)
    rw [h1, h2, HeightOneSpectrum.intValuation_eq_one_iff]
  have hmem : ∀ (R : HeightOneSpectrum (𝓞 E)), R.under (𝓞 F) = v → ((k : 𝓞 E) ∈ R.asIdeal ↔ (k : 𝓞 F) ∈ v.asIdeal) :=
    fun R hR => by
      rw [← hR, ← map_intCast (algebraMap (𝓞 F) (𝓞 E)) k]
      exact Iff.rfl
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h5 : Valued.v (algebraMap E (w.adicCompletion E) (k : E)) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ hk.trans_lt hlt), hu1]
  have hkw := (hval w).1 h5
  have hkP : (k : 𝓞 E) ∉ P.asIdeal := fun h => hkw ((hmem w hw).2 ((hmem P hP).1 h))
  have hk0 : (k : F) ≠ 0 := by
    intro h
    have : k = 0 := by exact_mod_cast h
    exact hkw (by simp [this])
  have hco : ∀ R : HeightOneSpectrum (𝓞 E), ((atFin R (upF F (Units.mk0 (k : F) hk0)) : (R.adicCompletion E)ˣ) :
      R.adicCompletion E) = algebraMap E (R.adicCompletion E) (k : E) := fun R => by
    rw [← map_intCast (algebraMap F E) k]
    rfl
  have h7 := hF.1 v (Units.mk0 (k : F) hk0)
  unfold HChar.resFin at h7
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h7
  have h6 : χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 := hun _ (by
    unfold IsUnitAt
    rw [hco, (hval P).2 hkP])
  change χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0))) * χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 at h7
  rw [h6, mul_one] at h7
  have h8 : χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0)) / u) = 1 := by
    refine ht _ ?_ ?_
    · unfold IsUnitAt
      rw [Units.val_div_eq_div_val, map_div₀, hco, h5, hu1, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, hco]
      exact hk
  rw [map_div, div_eq_one, h7] at h8
  exact h8.symm

theorem ram_both : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp →
    ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)),
    w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v →
    ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  classical
  intro D C nch Tp hT μ v w P hw hP hr hun
  by_cases hne : w = P
  · exact hr (hne ▸ hun)
  · exact hr (unrAt_of_pair _ ((mem_aboveF_iff D).1 hw) ((mem_aboveF_iff D).1 hP) hne
      (by convert aboveF_eq_pair D hw hP hne) (hT.ram μ w hr).2.1 (Tp.xi_triv μ) (Tp.xi_tame μ w) hun)

end GlobalTheory.Mem.HD.RamBoth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZOfSurjective
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder

namespace GlobalTheory.Mem.ColTie

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

abbrev csdK : CSD X.K := MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)

abbrev actK : Representation X.K (G0 X.E Pr.vGs R.r) (csdK W Ch sel mu hX).Forms :=
  g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)

abbrev dimP : ℕ := (csdK W Ch sel mu hX).lvlDim (actK W Ch sel mu hX) P.grp P.chr

abbrev resK : (mtildeKGSD W Ch sel mu).EqFun ≃ₗ[X.K] (csdK W Ch sel mu hX).Forms :=
  (mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)

abbrev formK (x : Fin (dimP W Ch sel mu P hX) → X.K) : (csdK W Ch sel mu hX).Forms :=
  LiftForms.lvlForm (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr x

theorem resK_symm_act (a : G0 X.E Pr.vGs R.r) (f : (csdK W Ch sel mu hX).Forms) :
    (resK W Ch sel mu hX).symm (actK W Ch sel mu hX a f) = g0HatRepEqFunX W Ch sel mu a ((resK W Ch sel mu hX).symm f) :=
  LinearEquiv.symm_apply_apply _ _

theorem resK_act (a : G0 X.E Pr.vGs R.r) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    actK W Ch sel mu hX a (resK W Ch sel mu hX φ) = resK W Ch sel mu hX (g0HatRepEqFunX W Ch sel mu a φ) := by
  show resK W Ch sel mu hX (g0HatRepEqFunX W Ch sel mu a ((resK W Ch sel mu hX).symm (resK W Ch sel mu hX φ))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem formK_mem (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    formK W Ch sel mu P hX x ∈ lvlForms (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr := by
  rw [← LiftForms.range_lvlForm]
  exact ⟨x, rfl⟩

theorem zOf_mem (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x)).1 ∈ (mtildeGSD W Ch sel mu P).EqFun := by
  refine (mem_MtildeV_iff W Ch sel mu P _).2 ⟨Subtype.prop _, fun a => ?_⟩
  refine (resK_symm_act W Ch sel mu hX a.1 _).symm.trans ?_
  rw [formK_mem W Ch sel mu P hX x a, map_smul]

def zOf : (Fin (dimP W Ch sel mu P hX) → X.K) →ₗ[X.K] MtildeV W Ch sel mu P where
  toFun x := ⟨_, zOf_mem W Ch sel mu P hX x⟩
  map_add' x y := Subtype.ext (by simp only [map_add]; rfl)
  map_smul' c x := Subtype.ext (by simp only [map_smul]; rfl)

theorem zOf_val (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    (zOf W Ch sel mu P hX x).1 = ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x)).1 := rfl

theorem zOf_injective : Function.Injective (zOf W Ch sel mu P hX) := by
  intro x y h
  apply LiftForms.lvlForm_injective (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr
  apply (resK W Ch sel mu hX).symm.injective
  have h1 : (zOf W Ch sel mu P hX x).1 = (zOf W Ch sel mu P hX y).1 := congrArg Subtype.val h
  exact Subtype.ext h1

theorem zOf_surjective : Function.Surjective (zOf W Ch sel mu P hX) := by
  intro φ
  obtain ⟨hφ, hact⟩ := (mem_MtildeV_iff W Ch sel mu P φ.1).1 φ.2
  have hf : resK W Ch sel mu hX ⟨φ.1, hφ⟩ ∈ lvlForms (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr := by
    intro a
    rw [resK_act, hact a, map_smul]
  rw [← LiftForms.range_lvlForm] at hf
  obtain ⟨x, hx⟩ := hf
  refine ⟨x, Subtype.ext ?_⟩
  rw [zOf_val]
  show ((resK W Ch sel mu hX).symm (LiftForms.lvlForm _ _ P.grp P.chr x)).1 = φ.1
  rw [hx, LinearEquiv.symm_apply_apply]

def zEquiv : (Fin (dimP W Ch sel mu P hX) → X.K) ≃ₗ[X.K] MtildeV W Ch sel mu P :=
  LinearEquiv.ofBijective (zOf W Ch sel mu P hX) ⟨zOf_injective W Ch sel mu P hX, zOf_surjective W Ch sel mu P hX⟩

end Gen

end GlobalTheory.Mem.ColTie
end
end

