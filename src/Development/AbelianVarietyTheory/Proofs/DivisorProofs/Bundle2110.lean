import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0053
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0006
import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveDualWeylTensorCuspFormsRationalPo
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.BetaInvIntegral

theorem betaH_inv_integral : ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ {n : ℕ} (Λ : GenLat D.host.E n) (σ : T.Q.c.F →+* ℂ) (p : ℕ), p.Prime → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt p → ∃ m : ℕ, Nat.Coprime m p ∧ IsIntegral ℤ ((m : ℂ) * (σ (betaH (Dw := T.Q.Dw j) T.Q.c Λ))⁻¹) := by
  intro D T hF j hj n Λ σ p hp hU hT hTp
  have hβ : betaH (Dw := T.Q.Dw j) T.Q.c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  obtain ⟨M, hM, hint⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hp
    (betaH (Dw := T.Q.Dw j) T.Q.c Λ)⁻¹ (fun w hw => by
      obtain ⟨k, hk, h1, h2⟩ := hTp
      have hA : ReciprocityTheory.ChartRestriction.G.PullbackSections.AdaptAt Λ w :=
        ⟨k, GlobalTheory.ShortUnits.not_mem_of_coprime' w hk.symm hw, h1, h2⟩
      have hv := GlobalTheory.ShortUnits.vLa_betaH T hF j hj Λ w hU hT hA
      have hne : w.valuation T.Q.c.F (betaH (Dw := T.Q.Dw j) T.Q.c Λ) ≠ 0 := by simpa using hβ
      have h1' : w.valuation T.Q.c.F (betaH (Dw := T.Q.Dw j) T.Q.c Λ) = 1 := by
        rw [← WithZero.exp_log hne]
        simp only [vLa, neg_eq_zero] at hv
        rw [hv]; rfl
      rw [map_inv₀, h1', inv_one])
  refine ⟨M, hM, ?_⟩
  have := map_isIntegral_int σ hint
  simpa [map_mul, map_inv₀, map_natCast] using this

end GlobalTheory.BetaInvIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetIdealCoprimeSplitSupportedPoint
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.DetIdealPrime

theorem exists_ideal_coprime : ∀ (D : D7) (V : HSp D), HSpace.gram V = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (y : (AE D)ˣ), IsIdemSum e P → SuppAt e V h → IsDetAt e V h y → ∀ (b : ℕ), (∀ Q ∈ P, (b : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) → ∀ (Λ : GenLat D.host.E V.rank), (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat V (fin V h)) → ∀ p : ℕ, p.Prime → Λ.TrivAt p → ∃ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(b : 𝓞 D.host.E)} = ⊤ ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ ((c y : Circle) : ℂ) = ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ) := by
  intro D V hg hL h e P y he hs hy b hb c ψ hc hu hr Λ hΛ p hp hT
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal V hg hL h e P y he hs hy b hb c ψ hc hu hr
  refine ⟨cc, c0, c2, ?_, c4⟩
  refine GlobalTheory.NormCoprime.coprime_absNorm_of_sup p hp c0 ?_
  obtain ⟨k, hk, -, hk2⟩ := hT
  have hdet : ((k : D.host.E) ^ V.rank) ∈ Submodule.span (𝓞 D.host.E) (detSet (Bridge.hLat V (fin V h))) := by
    refine Submodule.subset_span ⟨fun i => (k : D.host.E) • (Pi.single i 1 : Fin V.rank → D.host.E), fun i => ?_, ?_⟩
    · have hstd : (Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
        rw [Formalism.L2.Pj.stdLat, Submodule.mem_pi]
        intro j _
        by_cases hj : j = i
        · subst hj; simpa using (Submodule.one_le.1 le_rfl : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E))
        · simp [Pi.single_apply, hj]
      have h1 := hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 D.host.E)) hstd)
      have h2 : ((k : 𝓞 D.host.E) • (Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E)) =
          (k : D.host.E) • (Pi.single i 1 : Fin V.rank → D.host.E) := by
        rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E) k, algebraMap_smul]
      rw [h2] at h1
      have h3 := (hΛ _).1 h1
      convert h3 using 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · have : (Matrix.of fun i j => ((k : D.host.E) • (Pi.single j 1 : Fin V.rank → D.host.E)) i) =
          (k : D.host.E) • (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) := by
        ext i j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      rw [this, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hcM : cc ≤ M := le_trans le_sup_left hle
  have hpM : ((p : ℕ) : 𝓞 D.host.E) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hkM : ((k : ℕ) : 𝓞 D.host.E) ∉ M := by
    intro hkM
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hk
    have e1 := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at e1
    refine hM.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e1]
    exact M.add_mem (M.mul_mem_left _ hkM) (M.mul_mem_left _ hpM)
  have hkn : ((k : ℕ) : 𝓞 D.host.E) ^ V.rank ∉ M := fun h0 => hkM (hM.isPrime.mem_of_pow_mem _ h0)
  have hc'M : cc.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ M := by
    intro x hx
    have hm : (k : D.host.E) ^ V.rank * (x : D.host.E) ∈ idlE cc := by
      rw [← c3]
      exact Submodule.mul_mem_mul hdet ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := hm
    have hz' : z = ((k : ℕ) : 𝓞 D.host.E) ^ V.rank * x := by
      apply RingOfIntegers.ext
      rw [show (z : D.host.E) = Algebra.linearMap (𝓞 D.host.E) D.host.E z from rfl, hzeq]
      push_cast
      rfl
    rw [hz'] at hz
    exact ((hM.isPrime.mem_or_mem (hcM hz)).resolve_left hkn)
  exact hM.ne_top (top_le_iff.1 (c1 ▸ sup_le hcM hc'M))

end GlobalTheory.DetIdealPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtension
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.EvExtend

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

theorem norm_natCast_lt_one : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h := PadicComplex.norm_extends l ((l : ℕ) : PadicAlgCl l)
  rw [← h]
  simpa using ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one (p := l)

theorem norm_int_le_one (φ : F →+* PadicAlgCl l) (y : 𝓞 F) : ‖φ (y : F)‖ ≤ 1 := by
  have hi : IsIntegral ℤ (φ (y : F)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).isIntegral_iff_v_le_one.mp
    hi.tower_top
  exact_mod_cast (show ‖φ (y : F)‖₊ ≤ 1 from h2)

def placeOf (φ : F →+* PadicAlgCl l) : HeightOneSpectrum (𝓞 F) where
  asIdeal := ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal ((algebraMap (PadicAlgCl l) ℂ_[l]).comp φ)
  isPrime := ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal_isPrime _
  ne_bot := by
    intro h
    have hm : ((l : ℕ) : 𝓞 F) ∈ ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal ((algebraMap (PadicAlgCl l) ℂ_[l]).comp φ) := by
      rw [ReciprocityTheory.ChartRestriction.B3.IotaPl.mem_smallIdeal]
      simpa using ReciprocityTheory.ChartRestriction.B3.IotaPl.norm_p_lt_one (p := l)
    rw [h, Submodule.mem_bot] at hm
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hm

theorem mem_placeOf (φ : F →+* PadicAlgCl l) (x : 𝓞 F) : x ∈ (placeOf φ).asIdeal ↔ ‖φ (x : F)‖ < 1 := by
  show ‖(algebraMap (PadicAlgCl l) ℂ_[l]) (φ (x : F))‖ < 1 ↔ _
  rw [show ‖(algebraMap (PadicAlgCl l) ℂ_[l]) (φ (x : F))‖ = ‖φ (x : F)‖ from PadicComplex.norm_extends _ _]

theorem norm_le_one_iff (φ : F →+* PadicAlgCl l) (x : F) : ‖φ x‖ ≤ 1 ↔ (placeOf φ).valuation F x ≤ 1 :=
  Formalism.BasicNotions.Examples₂.norm_le_one_iff_val φ (placeOf φ) (norm_int_le_one φ) (mem_placeOf φ) x

theorem val_lt_one_iff (φ : F →+* PadicAlgCl l) (x : F) : (placeOf φ).valuation F x < 1 ↔ ‖φ x‖ < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := norm_le_one_iff φ x⁻¹
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx)
  have hv : 0 < (placeOf φ).valuation F x := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff _).2 hx
  rw [map_inv₀, norm_inv, inv_le_one₀ hpos, map_inv₀, inv_le_one₀ hv] at h
  rw [← not_le, ← not_le, h]

end GlobalTheory.EvExtend

namespace GlobalTheory.EvExtend

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

theorem exists_ext (φ : F →+* PadicAlgCl l) :
    ∃ j : (placeOf φ).adicCompletion F →+* PadicAlgCl l, Continuous j ∧
      (∀ x : F, j (algebraMap F _ x) = φ x) ∧
      (∀ y ∈ (placeOf φ).adicCompletionIntegers F, ‖j y‖ ≤ 1) ∧
      ∀ (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → (∀ x, φ x ∈ K) → ∀ y, j y ∈ K := by
  obtain ⟨j, hjc, hj⟩ := GlobalTheory.exists_continuous_extension_adicCompletion F l φ (placeOf φ) (val_lt_one_iff φ)
  have hj' : ∀ x : F, j (algebraMap F _ x) = φ x := fun x => RingHom.congr_fun hj x
  have hd := HeightOneSpectrum.denseRange_algebraMap F (placeOf φ)
  refine ⟨j, hjc, hj', fun y hy => ?_, fun K hK hφK y => ?_⟩
  · have hO : IsOpen (((placeOf φ).adicCompletionIntegers F : Set ((placeOf φ).adicCompletion F))) :=
      Valued.isOpen_valuationSubring _
    have hcl : IsClosed {y : (placeOf φ).adicCompletion F | ‖j y‖ ≤ 1} :=
      isClosed_le (continuous_norm.comp hjc) continuous_const
    refine closure_minimal ?_ hcl (hd.open_subset_closure_inter hO hy)
    rintro _ ⟨hy1, x, rfl⟩
    show ‖j (algebraMap F _ x)‖ ≤ 1
    rw [hj', norm_le_one_iff]
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, ReciprocityTheory.Aut.adic_valued_algebraMap] at hy1
    exact hy1
  · haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
    have hKc : IsClosed (K : Set (PadicAlgCl l)) := (completeSpace_coe_iff_isComplete.mp ‹_›).isClosed
    exact hd.induction_on (p := fun y => j y ∈ K) y (hKc.preimage hjc) fun x => by
      show j (algebraMap F _ x) ∈ K
      rw [hj']; exact hφK x

end GlobalTheory.EvExtend

namespace GlobalTheory.EvExtend

theorem exists_evOk : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (l : ℕ) [Fact l.Prime]
    (i : E →+* PadicAlgCl l), ∃ ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l, GlobalTheory.FrameOf.EvOk i ev := by
  intro F E _ _ _ _ _ l _ i
  let φ : F →+* PadicAlgCl l := i.comp (algebraMap F E)
  obtain ⟨j, -, hj, hint, hK⟩ := exists_ext φ
  let v := placeOf φ
  let e0 : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
    { toFun := fun a => a v, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  letI : Algebra F (PadicAlgCl l) := φ.toAlgebra
  let f : FiniteAdeleRing (𝓞 F) F →ₐ[F] PadicAlgCl l :=
    { j.comp e0 with commutes' := fun x => hj x }
  let g : E →ₐ[F] PadicAlgCl l := { i with commutes' := fun x => rfl }
  let ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l :=
    (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _).toRingHom
  have hev : ∀ a e, ev (a ⊗ₜ[F] e) = j (a v) * i e := fun a e => Algebra.TensorProduct.lift_tmul _ _ _ _ _
  refine ⟨ev, fun x => ?_, fun a ha => ?_, fun a ha => ?_, fun y => ?_⟩
  · rw [hev]
    show j 1 * i x = i x
    rw [map_one, one_mul]
  · rw [hev, map_one, mul_one]
    exact hint _ (ha v)
  · have hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [mem_placeOf]
      simpa [φ] using norm_natCast_lt_one (l := l)
    rw [hev, ha v hl, map_zero, zero_mul]
  · have hKle : Formalism.BasicNotions.Examples₂.LB.Kphi i ≤ IntermediateField.adjoin ℚ_[l] (Set.range i) :=
      IntermediateField.adjoin.mono _ _ _ (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)
    have hmem : ∀ a e, ev (a ⊗ₜ[F] e) ∈ Formalism.BasicNotions.Examples₂.LB.Kphi i := fun a e => by
      rw [hev]
      exact mul_mem (hK _ inferInstance (fun x => Formalism.BasicNotions.Examples₂.LB.phi_mem i _) _) (Formalism.BasicNotions.Examples₂.LB.phi_mem i e)
    refine hKle ?_
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a e => exact hmem a e
    | add y z hy hz => rw [map_add]; exact add_mem hy hz

end GlobalTheory.EvExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleGoodCoverLevelMap
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverGood

theorem hom_spQ_ext {X : Scheme.{0}} (f g : X ⟶ Sp ℚ) : f = g := by
  have key : ∀ h : X ⟶ Sp ℚ, h = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ h.appTop) := by
    intro h
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key f, key g]
  congr 2
  ext1
  exact RingHom.ext_rat _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem exists_objMap_lower' {l l₂ : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B'} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj Dw l b' s} {o₂ : Obj Dw l₂ b₂ s₂} {o' : Obj Dw l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    Nonempty (ObjMap (GlobalTheory.ObjLower.lower o' h hρ hζ) o (g ≫ π)) := by
  obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine GlobalTheory.ObjComp.sec_comp (h₁ a) ?_
    rw [← GlobalTheory.ObjLower.map_nsmul_of_add _ o'.eta_add, ← GlobalTheory.ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine GlobalTheory.ObjComp.sec_comp (h₂ a) ?_
    rw [← GlobalTheory.ObjLower.map_nsmul_of_add _ o'.etaA_add, ← GlobalTheory.ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

theorem eq_of_levelMaps {l l₂ : Level H} {Xo : Moduli Dw l} {Xo₂ : Moduli Dw l₂} (hd : l.Dvd l₂)
    (jK : KA l →+* KA l₂) (hjK : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {r r' : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) (m' : SABMap Xo₂.univ.t Xo.univ.t r')
    (he : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (heA : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (he' : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = r' ≫ (Xo.univ.eta a).left)
    (heA' : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = r' ≫ (Xo.univ.etaA a).left)
    {T : Scheme.{0}} [IsReduced T] (iU : T ⟶ Xo₂.X) (h : iU ≫ r ≫ Xo.s = iU ≫ Xo₂.s ≫ spMap jK)
    (h' : iU ≫ r' ≫ Xo.s = iU ≫ Xo₂.s ≫ spMap jK) : iU ≫ r = iU ≫ r' := by
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨o', ⟨u⟩⟩ := GlobalTheory.obj_pull E H Dw l₂ (KA l₂) (KA l₂) (baseKA l₂) (baseKA l₂) (RingHom.id _) Xo₂.X T Xo₂.s
    (iU ≫ Xo₂.s) iU rfl rfl (by simp [spMap]) Xo₂.univ
  obtain ⟨w⟩ := exists_objMap_lower' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA)
    (o := Xo.univ) m he heA u
  obtain ⟨w'⟩ := exists_objMap_lower' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA)
    (o := Xo.univ) m' he' heA' u
  have hρ : jK (baseKA l).ρ = (GlobalTheory.baseOfFinerLevel hA).ρ :=
    Subtype.ext ((hjK _).trans ((GlobalTheory.coe_baseKA_rho l).trans (GlobalTheory.coe_baseKA_rho l₂).symm))
  have hζ : jK (baseKA l).ζ = (GlobalTheory.baseOfFinerLevel hA).ζ :=
    Subtype.ext ((hjK _).trans (GlobalTheory.coe_levelFieldIncl hA _).symm)
  have hu := GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel E H Dw l Xo (KA l₂) (GlobalTheory.baseOfFinerLevel hA) jK T
    (iU ≫ Xo₂.s) (GlobalTheory.ObjLower.lower o' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA))
    inferInstance hρ hζ
  exact hu.unique ⟨by rw [Category.assoc, h, Category.assoc], ⟨w⟩⟩ ⟨by rw [Category.assoc, h', Category.assoc], ⟨w'⟩⟩

theorem formallyUnramified_spQ (l : Level H) : FormallyUnramified (spMap (algebraMap ℚ (KA l))) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := GlobalTheory.LevelUp.finiteDimensional_KA l
  exact Algebra.FormallyUnramified.of_isSeparable ℚ (KA l)

theorem locallyOfFiniteType_spQ (l : Level H) : LocallyOfFiniteType (spMap (algebraMap ℚ (KA l))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have := GlobalTheory.LevelUp.finiteDimensional_KA l
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end GlobalTheory.CoverGood

theorem GlobalTheory.CoverGood.exists_good_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := by
  intro E _ _ _ H Dw l Xo c d hpq hl
  obtain ⟨hdvd, hM, -, -, -, ⟨he, heA⟩, hlift, -, -⟩ := hl
  obtain ⟨r₀, jK, m₀, hjK, hr₀s, he₀, heA₀, -, hrF⟩ := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H Dw hpq).1 l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h₁, h₂, hfin, het, -, -⟩ := hrF c d.c₂ d.hF.symm
  have hdiv : d.l₂.M / l.M = d.pd := by
    rw [hM]; exact Nat.mul_div_cancel_left _ (by have := l.three_le; omega)
  rw [← hdiv] at he

  have hab : (d.r ≫ Xo.s) ≫ spMap (algebraMap ℚ (KA l)) = (d.Xo₂.s ≫ spMap jK) ≫ spMap (algebraMap ℚ (KA l)) :=
    GlobalTheory.CoverGood.hom_spQ_ext _ _
  have := GlobalTheory.CoverGood.formallyUnramified_spQ l
  have := GlobalTheory.CoverGood.locallyOfFiniteType_spQ l
  have hop : IsOpenImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    GlobalTheory.isOpenImmersion_equalizer_ι_of_unramified _ hab
  have hcl : IsClosedImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated _ hab
  have hred₂ : IsReduced d.Xo₂.X := by
    haveI := d.Xo₂.smooth
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ d.Xo₂.s
      (SmoothOfRelativeDimension.smooth Dw.dim d.Xo₂.s)).1
  have hredU : IsReduced (equalizer (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    isReduced_of_isOpenImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK))
  have hagree : equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK) ≫ d.r =
      equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK) ≫ r₀ :=
    GlobalTheory.CoverGood.eq_of_levelMaps hdvd jK hjK d.m m₀ he heA he₀ heA₀ _
      (equalizer.condition (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK))
      (by rw [hr₀s])

  obtain ⟨U, iU, hop', hcl', hagree', hlU⟩ : ∃ (U : Scheme.{0}) (iU : U ⟶ d.Xo₂.X), IsOpenImmersion iU ∧
      IsClosedImmersion iU ∧ iU ≫ d.r = iU ≫ r₀ ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ d.Xo₂.X),
        x ≫ d.r ≫ Xo.s = x ≫ d.Xo₂.s ≫ spMap jK → ∃ u : Sp K ⟶ U, u ≫ iU = x :=
    ⟨_, _, hop, hcl, hagree, fun K _ x hx =>
      ⟨equalizer.lift x (by simpa only [Category.assoc] using hx), equalizer.lift_ι _ _⟩⟩
  clear hop hcl hagree hredU
  haveI := hop'; haveI := hcl'; haveI := hfin; haveI := het
  have hsp : spMap (IntermediateField.inclusion d.hF.symm.le).toRingHom ≫
      spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) =
      spMap (IntermediateField.inclusion d.c₂.le).toRingHom := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨pullback iU (pullback.fst d.Xo₂.s (spMap (IntermediateField.inclusion d.c₂.le).toRingHom)),
    pullback.snd _ _ ≫ rF, pullback.fst _ _ ≫ iU, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · refine ⟨fun x => ?_⟩
    obtain ⟨K, _, _, j, ⟨k0, hk0⟩⟩ := GlobalTheory.ZM.IsGaloisCover.exists_algClosed_point (Xo.XF c) x
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ pullback.snd _ _ : Sp K ⟶ Sp c.F)
    letI : Algebra c.F K := φ.hom.toAlgebra
    letI : Algebra d.c₂.F K := ((algebraMap c.F K).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F K (d.eF a) = algebraMap c.F K a := fun a => by
      show algebraMap c.F K (d.eF.symm (d.eF a)) = _
      rw [AlgEquiv.symm_apply_apply]
    have hjs : j ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := hφ.symm
    have hx₀ : (j ≫ pullback.fst _ _) ≫ Xo.s = sOf c K := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hjs, sOf, spMap, spMap, ← Spec.map_comp]
      rfl
    obtain ⟨y, hy⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed _ hx₀
    obtain ⟨y₂, hy₂⟩ := hlift K hk y
    have hyr : y₂.x ≫ d.r = y.x := hy₂.1
    have hgood : y₂.x ≫ d.r ≫ Xo.s = y₂.x ≫ d.Xo₂.s ≫ spMap jK := by
      rw [reassoc_of% hyr, y.x_over, reassoc_of% y₂.x_over, sOf, sOf]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext t
      show algebraMap c.F K (IntermediateField.inclusion c.le t) =
        algebraMap c.F K (d.eF.symm (IntermediateField.inclusion d.c₂.le (jK t)))
      exact congrArg (algebraMap c.F K) (Subtype.ext (hjK t).symm)
    obtain ⟨u, hu⟩ := hlU K y₂.x hgood
    have hw : y₂.x ≫ d.Xo₂.s =
        spMap (algebraMap d.c₂.F K) ≫ spMap (IntermediateField.inclusion d.c₂.le).toRingHom := by
      rw [y₂.x_over, sOf, spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have hr₀ : y₂.x ≫ r₀ = y.x := by
      rw [← hu, Category.assoc, ← hagree', ← Category.assoc, hu, hyr]
    obtain ⟨w, hw₁, hw₂⟩ : ∃ w : Sp K ⟶ d.Xo₂.XF d.c₂, w ≫ pullback.fst _ _ = y₂.x ∧
        w ≫ pullback.snd _ _ = spMap (algebraMap d.c₂.F K) :=
      ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨z, hz⟩ : ∃ z : Sp K ⟶ pullback iU (pullback.fst d.Xo₂.s
        (spMap (IntermediateField.inclusion d.c₂.le).toRingHom)), z ≫ pullback.snd _ _ = w :=
      ⟨pullback.lift u w (by rw [hu, hw₁]), pullback.lift_snd _ _ _⟩
    have e : z ≫ pullback.snd _ _ ≫ rF = j := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, h₁, reassoc_of% hz, reassoc_of% hw₁, hr₀, hy]
      · rw [Category.assoc, Category.assoc, h₂, reassoc_of% hz, reassoc_of% hw₂, hjs, spMap, spMap,
          spMap, ← Spec.map_comp]
        rfl
    exact ⟨z k0, by rw [← Scheme.Hom.comp_apply, e, hk0]⟩
  · simp only [Category.assoc]
    rw [hagree', h₁, pullback.condition_assoc]
  · simp only [Category.assoc]
    rw [pullback.condition_assoc, reassoc_of% h₂, hsp, pullback.condition]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfDilatedReductionResidueMatricesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_half_dilated_reduction_residueMatrices : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ x : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1), ∃ y : WO (Vc D i) (Wc D i), IsHalf eQ y ∧ dil i (ϖ : D.host.E) y ∈ lattice₂ R i ∧ ∀ PP : ↥Q, redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) y)) = x PP := by
  first | exact @GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq | exact GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq | (intros; apply GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveDualWeylTensorCuspFormsRationalPoStatement
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_dualWeylTensor_cuspForms_rationalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), DefCase U ξ → Dom a n → ∀ (Z : Comp Xo c) (P : PtData Z), ∃ φ : (TIdx (part Dw a) → c.F) →ₗ[c.F] Rul Xo c, Function.Injective φ ∧ LinearMap.range φ = cuspOn U Z (wtZ a n) ∧ ∀ x, Reads Z P.y₀ a n x (φ x) := by
  first | exact @GlobalTheory.DefPt.ReadsPt.exists_linearMap_reads | exact GlobalTheory.DefPt.ReadsPt.exists_linearMap_reads | (intros; apply GlobalTheory.DefPt.ReadsPt.exists_linearMap_reads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearExtensionOfFormWithTransportedReStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_extension_of_form_with_transported_rep : ∀ {K LL Cs W G : Type} [Field K] [Field LL] [Algebra K LL] [AddCommGroup Cs] [Module K Cs] [AddCommGroup W] [Module ℂ W] [Group G] {n m : ℕ} (σ₀ : K →+* ℂ) (σ : LL →+* ℂ), (∀ a, σ (algebraMap K LL a) = σ₀ a) → ∀ (cu : Cs →ₗ[K] (Fin n → LL)) (b : Fin m → Cs), Submodule.span K (Set.range b) = ⊤ → LinearIndependent LL (fun k => cu (b k)) → Submodule.span LL (Set.range fun k => cu (b k)) = ⊤ → ∀ (R : Cs →ₛₗ[σ₀] W), LinearIndependent ℂ (fun k => R (b k)) → Submodule.span ℂ (Set.range R) = ⊤ → ∀ (ρL : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))), ∃ (f : (Fin n → LL) →ₛₗ[σ] W) (ρ : Representation ℂ G W), (∀ F, f (cu F) = R F) ∧ (∀ g w, ρ g (f w) = f (ρL g w)) ∧ (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  first | exact @GlobalTheory.SemilinearReading.exists_semilinear_extension_rep | exact GlobalTheory.SemilinearReading.exists_semilinear_extension_rep | (intros; apply GlobalTheory.SemilinearReading.exists_semilinear_extension_rep <;> assumption)
end

