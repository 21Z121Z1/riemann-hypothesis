import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.UnipotentAdelicQuotients.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0098
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Columns.TwQCmp
import Formalism.LocalToGlobal.Columns.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct Topology

namespace GlobalTheory.IdeleNormChar

open GlobalTheory.QuadSymbol

variable {K : Type} [Field K] [NumberField K]

def finEval (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infEval (w : InfinitePlace K) : AdeleRing (𝓞 K) K →* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl

def finComp : (AdeleRing (𝓞 K) K)ˣ →* FinFam K :=
  MonoidHom.pi fun v => Units.map (finEval v)

def infComp : (AdeleRing (𝓞 K) K)ˣ →* InfFam K :=
  MonoidHom.pi fun w => Units.map (infEval w)

theorem finComp_toUnits (t : Kˣ) : finComp (toUnits K (AdeleRing (𝓞 K) K) t) = finDiag K t :=
  funext fun _ => Units.ext rfl

theorem infComp_toUnits (t : Kˣ) : infComp (toUnits K (AdeleRing (𝓞 K) K) t) = infDiag K t :=
  funext fun _ => Units.ext rfl

theorem eventually_valued_eq_one (a : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  filter_upwards [(a : AdeleRing (𝓞 K) K).2.2, ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2.2]
    with v h3 h4
  have hmul : (a : AdeleRing (𝓞 K) K).2 v *
      ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
    congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one] at hm
  change Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1
  refine le_antisymm h3 ?_
  rw [← hm]
  exact mul_le_of_le_one_right' h4

theorem eventually_integral_form (δ : K) (hδ : δ ≠ 0) (a : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
        ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 := by
  filter_upwards [eventually_valued_eq_one a,
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 2 two_ne_zero)).compl_mem_cofinite,
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 δ hδ)).compl_mem_cofinite] with v ha h2 hd
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not, Units.val_mk0] at h2 hd
  have key : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  exact GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit K v (algebraMap K _ δ) _
    (by rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]; exact (key _).trans h2)
    (by rw [key, hd]) ha

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L]

omit [NumberField L] in

theorem almostNorm_finComp (a : (AdeleRing (𝓞 K) K)ˣ) : AlmostNorm K L (finComp a) := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  refine Filter.eventually_cofinite.1 ((eventually_integral_form δ hδ0 a).mono ?_)
  rintro v ⟨x, -, y, -, h⟩
  exact (mem_normGroup_iff_form b h0 h1).2 ⟨x, y, h⟩

omit [NumberField L] in

theorem mem_normGroup_iff_everywhereNorm (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ normGroup K L (AdeleRing (𝓞 K) K) ↔ EverywhereNorm K L (finComp a) (infComp a) := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  rw [mem_normGroup_iff_form b h0 h1]
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨fun v => (mem_normGroup_iff_form b h0 h1).2
        ⟨x.2 v, y.2 v, congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) h⟩,
      fun w => (mem_normGroup_iff_form b h0 h1).2
        ⟨x.1 w, y.1 w, congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) h⟩⟩
  · rintro ⟨hf, hi⟩
    have hc := eventually_integral_form δ hδ0 a
    have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K,
        ((∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
          ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2) →
          x ∈ v.adicCompletionIntegers K ∧ y ∈ v.adicCompletionIntegers K) ∧
        ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 := by
      intro v
      by_cases hv : ∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
          ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2
      · obtain ⟨x, hx, y, hy, h⟩ := hv
        exact ⟨x, y, fun _ => ⟨hx, hy⟩, h⟩
      · obtain ⟨x, y, h⟩ := (mem_normGroup_iff_form b h0 h1).1 (hf v)
        exact ⟨x, y, fun h' => absurd h' hv, h⟩
    choose x y hxy h using hloc
    choose r s hr using fun w => (mem_normGroup_iff_form b h0 h1).1 (hi w)
    let X : FiniteAdeleRing (𝓞 K) K := ⟨x, hc.mono fun v hv => (hxy v hv).1⟩
    let Y : FiniteAdeleRing (𝓞 K) K := ⟨y, hc.mono fun v hv => (hxy v hv).2⟩
    refine ⟨((r : InfiniteAdeleRing K), X), ((s : InfiniteAdeleRing K), Y), Prod.ext ?_ ?_⟩
    · funext w
      exact hr w
    · exact FiniteAdeleRing.ext K fun v => h v

def normSign : (AdeleRing (𝓞 K) K)ˣ →* ℤˣ :=
  MonoidHom.mk' (fun a => etaProd K L (finComp a) (infComp a)) fun a b => by
    obtain ⟨h1, h2⟩ := localCharacters K L
    unfold etaProd
    simp only [map_mul, Pi.mul_apply, h1, h2]
    rw [finprod_mul_distrib (almostNorm_finComp L a).finite_mulSupport
      (almostNorm_finComp L b).finite_mulSupport, Finset.prod_mul_distrib, mul_mul_mul_comm]

theorem normSign_eq_one_iff (a : (AdeleRing (𝓞 K) K)ˣ) :
    normSign L a = 1 ↔ ∃ t : Kˣ, a / toUnits K (AdeleRing (𝓞 K) K) t ∈ normGroup K L (AdeleRing (𝓞 K) K) := by
  refine ((exactSequence K L).2.2.1 _ _ (almostNorm_finComp L a)).symm.trans (exists_congr fun t => ?_)
  rw [mem_normGroup_iff_everywhereNorm, map_div, map_div, finComp_toUnits, infComp_toUnits]

theorem normSign_of_mem {a : (AdeleRing (𝓞 K) K)ˣ} (h : a ∈ normGroup K L (AdeleRing (𝓞 K) K)) :
    normSign L a = 1 :=
  (normSign_eq_one_iff L a).2 ⟨1, by rwa [map_one, div_one]⟩

theorem normSign_toUnits (t : Kˣ) : normSign L (toUnits K (AdeleRing (𝓞 K) K) t) = 1 :=
  (normSign_eq_one_iff L _).2 ⟨t, by rw [div_self']; exact one_mem _⟩

theorem exists_normSign_ne_one : ∃ a : (AdeleRing (𝓞 K) K)ˣ, normSign L a ≠ 1 := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  obtain ⟨a, ha⟩ := GlobalTheory.QNorm.exists_idele_not_mul_norm K δ hδ
  refine ⟨a, fun h => ?_⟩
  obtain ⟨t, ht⟩ := (normSign_eq_one_iff L a).1 h
  obtain ⟨x, y, e⟩ := (mem_normGroup_iff_form b h0 h1).1 ht
  refine ha t x y ?_
  rw [← e]
  exact (congrArg Units.val (mul_div_cancel (toUnits K (AdeleRing (𝓞 K) K) t) a)).symm

theorem eventually_normSign : ∀ᶠ a in 𝓝 (1 : (AdeleRing (𝓞 K) K)ˣ), normSign L a = 1 := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  filter_upwards [GlobalTheory.QNorm.norm_form_mem_nhds_one K δ hδ0] with a ha
  exact normSign_of_mem L ((mem_normGroup_iff_form b h0 h1).2 ha)

def signToCircle : ℤˣ →* Circle where
  toFun u := if u = 1 then 1 else -1
  map_one' := if_pos rfl
  map_mul' u u' := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or u' with rfl | rfl <;> simp

theorem circle_neg_one_ne_one : (-1 : Circle) ≠ 1 := fun h => by
  have := congrArg (fun z : Circle => (z : ℂ)) h
  norm_num at this

theorem eq_signToCircle_comp {G : Type} [Group G] (ε : G →* ℤˣ) (η : G →* Circle)
    (h : ∀ a, ε a = 1 → η a = 1) (hη : η ≠ 1) : η = signToCircle.comp ε := by
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push Not at hh
    exact hη (MonoidHom.ext hh)
  have hεb : ε b = -1 := (Int.units_eq_one_or _).resolve_left fun e => hb (h b e)
  refine MonoidHom.ext fun a => ?_
  rcases Int.units_eq_one_or (ε a) with e | e
  · rw [MonoidHom.comp_apply, e, map_one, h a e]
  · have h1 : η a * η b = 1 := by rw [← map_mul]; exact h _ (by rw [map_mul, e, hεb]; simp)
    have h2 : η a * η a = 1 := by rw [← map_mul]; exact h _ (by rw [map_mul, e]; simp)
    have h3 : (η a : ℂ) * η a = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h2
    rw [MonoidHom.comp_apply, e]
    change η a = if (-1 : ℤˣ) = 1 then 1 else -1
    rw [if_neg (by decide)]
    rcases mul_self_eq_one_iff.1 h3 with h4 | h4
    · have h5 : η a = 1 := Circle.ext h4
      rw [h5, one_mul] at h1
      exact absurd h1 hb
    · exact Circle.ext h4

theorem globalNormIndexTwo : Formalism.D.Classical.GlobalNormIndexTwo := by
  intro F E _ _ _ _ _ h2
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  refine ⟨signToCircle.comp (normSign E), ⟨?_, fun a => ?_, fun x => ?_, fun e => ?_⟩, ?_⟩
  · refine continuous_of_continuousAt_one _ ((continuousAt_const (y := (1 : Circle))).congr ?_)
    filter_upwards [eventually_normSign (K := F) E] with a ha
    rw [MonoidHom.comp_apply, ha, map_one]
  · exact (congrArg signToCircle (normSign_toUnits E a)).trans (map_one _)
  · exact (congrArg signToCircle (normSign_of_mem E ⟨x, rfl⟩)).trans (map_one _)
  · obtain ⟨a, ha⟩ := exists_normSign_ne_one (K := F) E
    have h : signToCircle (normSign E a) = 1 := DFunLike.congr_fun e a
    exact circle_neg_one_ne_one ((if_neg ha).symm.trans h)
  · rintro η ⟨-, h1, h3, h4⟩
    refine eq_signToCircle_comp _ η (fun a ha => ?_) h4
    obtain ⟨t, x, hx⟩ := (normSign_eq_one_iff E a).1 ha
    rw [← div_mul_cancel a (toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h3 x, one_mul]
    exact h1 t

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta in

theorem existsUnique_isEta : ∀ D : D7, ∃! η : (AF D.host.F)ˣ →* Circle, IsEta D η := fun D =>
  globalNormIndexTwo D.host.F D.host.E D.sp.cm.deg2

end GlobalTheory.IdeleNormChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicitySpaceDefiniteContinuousInvariantEqui
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open Classical in

theorem mult_equiv_update {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T T' _ _ h h' =>
    funext z
    simp only [MultilinearMap.add_apply, Pi.add_apply, h, h', rTr]
  | smul r T _ h =>
    funext z
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h, rTr]

theorem multT_cont_left_equiv :
    ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ), AllPlus M → (∀ τ, M.sm τ = ⊤) → Function.Injective (inclT M) → IsTensAct M π → ∀ L ∈ MultT θ M J χ, ∀ x, Continuous (L x) ∧ (∀ γ ∈ GQ V, ∀ h, L x (γ * h) = L x h) ∧ ∀ τ u, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x) := by
  classical
  intro D θ V S M π J χ hp hsm hinj hπ L hL x
  rw [mem_multT] at hL
  have hv : ∀ v, L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm L v := fun v => rfl
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    obtain ⟨a, b, -⟩ := mult_value_left_cont_level θ M J χ _ hL v
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_smul, hv]; exact b.const_smul r
    · rw [map_smul, hv]; simp only [Pi.smul_apply, a γ hγ h]
    · let w : M.sm τ := ⟨M.rep τ (unfr M τ u) (v τ), Submodule.eq_top_iff'.1 (hsm τ) _⟩
      have e : π τ u (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ w) := by
        apply hinj
        rw [hπ]
        unfold inclT actT
        simp only [PiTensorProduct.map_tprod]
        congr 1
        funext ρ
        by_cases hρ : ρ = τ
        · subst hρ
          simp [w]
        · simp [Function.update_of_ne hρ]
      rw [map_smul, map_smul, map_smul, e, hv, hv,
        mult_equiv_update θ M J χ _ hL τ _ (hp.unfr_mem τ u) v w rfl]
      rfl
  | add x y hx hy =>
    obtain ⟨a, b, c⟩ := hx
    obtain ⟨a', b', c'⟩ := hy
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_add]; exact a.add a'
    · simp only [map_add, Pi.add_apply, b γ hγ h, b' γ hγ h]
    · rw [map_add, map_add, map_add, c, c']; rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubMemIdS
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IdemOf (F : Type) [Field F] [NumberField F] [Algebra F E] (Q : Pl E) (ε : E ⊗[F] Formalism.L2.Herm.Af F) : Prop :=
  ε * ε = ε ∧ ∀ x : 𝓞 E, x ≠ 0 → (x ∈ Q.asIdeal ↔ ε * iA F E ((x : E)⁻¹) ∉ Formalism.L2.Herm.intAf F E)

namespace IdemOf

variable {Q : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε)
include h

theorem div_mem {t : 𝓞 E} (ht : t ∉ Q.asIdeal) : ε * iA F E ((t : E)⁻¹) ∈ Formalism.L2.Herm.intAf F E := by
  have t0 : t ≠ 0 := fun h0 => ht (h0 ▸ Q.asIdeal.zero_mem)
  by_contra hn
  exact ht ((h.2 t t0).2 hn)

theorem mem : ε ∈ Formalism.L2.Herm.intAf F E := by
  have := h.div_mem (one_notMem Q)
  simpa using this

theorem one_sub_mem : 1 - ε ∈ Formalism.L2.Herm.intAf F E := sub_mem (one_mem _) h.mem

theorem mul_one_sub : ε * (1 - ε) = 0 := by rw [mul_sub, h.1, mul_one, sub_self]

theorem mul_mem_of_val {x : E} (hx : Q.valuation E x ≤ 1) : ε * iA F E x ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨a, t, ht, e⟩ := qsp_frac Q x hx
  have t0 : (t : E) ≠ 0 := fun h0 => ht (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have e2 : x = (t : E)⁻¹ * algebraMap (𝓞 E) E a := by
    rw [← e]; field_simp
  rw [e2, map_mul, ← mul_assoc]
  exact mul_mem (h.div_mem ht) (iA_mem a)

theorem resS_eq_zero {w : Pl E} (hw : w ≠ Q) {a : E ⊗[F] Formalism.L2.Herm.Af F} (ha : ε * a ∈ Formalism.L2.Herm.intAf F E) :
    resS F w ⟨ε * a, ha⟩ = 0 := by
  obtain ⟨t, htw, htQ⟩ : ∃ t ∈ w.asIdeal, t ∉ Q.asIdeal := by
    by_contra hn
    push Not at hn
    exact hw (HeightOneSpectrum.ext (w.isMaximal.eq_of_le Q.isPrime.ne_top hn))
  have t0 : (t : E) ≠ 0 := fun h0 => htQ (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have e : (⟨ε * a, ha⟩ : Formalism.L2.Herm.intAf F E) = oToS F E t * (⟨_, h.div_mem htQ⟩ * ⟨ε * a, ha⟩) := by
    apply Subtype.ext
    show ε * a = iA F E (t : E) * (ε * iA F E ((t : E)⁻¹) * (ε * a))
    have : iA F E (t : E) * iA F E ((t : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ t0, map_one]
    linear_combination (-(ε * a) * ε) * this - a * h.1
  rw [e, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 htw, zero_mul]

omit h in
theorem val_unif {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    Q.valuation E (ϖ : E) = WithZero.exp (-1 : ℤ) := by
  rw [show (ϖ : E) = algebraMap (𝓞 E) E ϖ from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (Q.intValuation_le_pow_iff_mem ϖ 1).2 (by rwa [pow_one])
  have a2 := (Q.intValuation_le_pow_iff_mem ϖ 2).not.2 h2
  have h0 : Q.intValuation ϖ ≠ 0 := fun h0 => a2 (by rw [h0]; exact zero_le)
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at a1 a2
  rw [← WithZero.exp_log h0]
  congr 1
  push_cast at a1 a2
  omega

omit h in
theorem unif_ne {ϖ : 𝓞 E} (h2 : ϖ ∉ Q.asIdeal ^ 2) : (ϖ : E) ≠ 0 := fun h0 =>
  h2 (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)

theorem div_pow_mem {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (m : ℕ) {a : Formalism.L2.Herm.intAf F E}
    (ha : a ∈ idS F (Q.asIdeal ^ m)) :
    ε * iA F E (((ϖ : E) ^ m)⁻¹) * a ∈ Formalism.L2.Herm.intAf F E := by
  refine Submodule.span_induction
    (p := fun (a : Formalism.L2.Herm.intAf F E) _ => ε * iA F E (((ϖ : E) ^ m)⁻¹) * (a : E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨p, hp, rfl⟩
    rw [← iA_coe, mul_assoc, ← map_mul]
    refine h.mul_mem_of_val ?_
    have a1 := (Q.intValuation_le_pow_iff_mem p m).2 hp
    rw [map_mul, map_inv₀, map_pow, val_unif h1 h2, HeightOneSpectrum.valuation_of_algebraMap, ← WithZero.exp_nsmul,
      inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]
    simpa using a1
  · simp
  · intro a b _ _ ha hb
    rw [Subring.coe_add, mul_add]; exact add_mem ha hb
  · intro c a _ ha
    rw [smul_eq_mul, Subring.coe_mul, mul_left_comm]; exact mul_mem c.2 ha

theorem one_sub_mem_idS [StarRing E] (m : ℕ) : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) ∈ idS F (Q.asIdeal ^ m) := by
  obtain ⟨ϖ, h1, h2⟩ := Ideal.exists_mem_pow_notMem_pow_succ Q.asIdeal Q.ne_bot Q.isPrime.ne_top 1
  rw [pow_one] at h1
  have hi : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨ε, h.mem⟩ = 0 :=
    Subtype.ext (by show (1 - ε) * ε = 0; rw [mul_comm, h.mul_one_sub])
  have h3 : resS F Q ⟨1 - ε, h.one_sub_mem⟩ = 0 := by
    have := congrArg (resS F Q) hi
    rw [map_mul, map_zero] at this
    refine (mul_eq_zero.1 this).resolve_right fun h0 => ?_
    have h4 := h.div_pow_mem h1 h2 1 (a := ⟨ε, h.mem⟩) (by rw [pow_one]; exact mem_idS_of_resS h0)
    have ϖ0 : ϖ ≠ 0 := fun h0 => h2 (h0 ▸ zero_mem _)
    refine (h.2 ϖ ϖ0).1 h1 ?_
    rwa [pow_one, mul_right_comm, h.1] at h4
  have h5 := Ideal.pow_mem_pow (mem_idS_of_resS h3) m
  have h6 : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨1 - ε, h.one_sub_mem⟩ = ⟨1 - ε, h.one_sub_mem⟩ :=
    Subtype.ext (by show (1 - ε) * (1 - ε) = 1 - ε; linear_combination h.1)
  rcases m with _ | m
  · unfold idS
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial
  · rw [IsIdempotentElem.pow_succ_eq m h6] at h5
    unfold idS at h5 ⊢
    rwa [Ideal.map_pow]

theorem mem_idS_pow_iff [StarRing E] {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (m : ℕ) (a : Formalism.L2.Herm.intAf F E) :
    a ∈ idS F (Q.asIdeal ^ m) ↔ ε * iA F E (((ϖ : E) ^ m)⁻¹) * a ∈ Formalism.L2.Herm.intAf F E := by
  refine ⟨h.div_pow_mem h1 h2 m, fun ha => ?_⟩
  have e : a = oToS F E (ϖ ^ m) * ⟨_, ha⟩ + ⟨1 - ε, h.one_sub_mem⟩ * a := by
    apply Subtype.ext
    show (a : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * (ε * iA F E (((ϖ : E) ^ m)⁻¹) * a) + (1 - ε) * a
    have : iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * iA F E (((ϖ : E) ^ m)⁻¹) = 1 := by
      rw [← map_mul, map_pow, mul_inv_cancel₀ (pow_ne_zero _ (unif_ne h2)), map_one]
    linear_combination (-(ε * (a : E ⊗[F] Formalism.L2.Herm.Af F))) * this
  rw [e]
  exact add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow h1 m)))
    (Ideal.mul_mem_right _ _ (h.one_sub_mem_idS m))

end IdemOf

end GlobalTheory.InertNbr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalUnitaryPairToPairComponentMemLocalLevelStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → (pc P v c').act (glE γ) = pc P v c → mov K (A.eV v).1 c γ c' ∈ K.lev.Uloc (A.eV v).1 := by
  first | exact @GlobalTheory.LevelHecke.PairToLevel.main | exact GlobalTheory.LevelHecke.PairToLevel.main | (intros; apply GlobalTheory.LevelHecke.PairToLevel.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProdStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf → Integrable Φ ν ∧ Multipliable (fun v => ∫ X, Φv v X ∂(mv v)) ∧ ∫ X, Φ X ∂ν = (∫ X, Φinf X ∂mi) * ∏' v, ∫ X, Φv v X ∂(mv v) := by
  first | exact @GlobalTheory.GaugeEx.ProdInt.integral_pure | exact GlobalTheory.GaugeEx.ProdInt.integral_pure | (intros; apply GlobalTheory.GaugeEx.ProdInt.integral_pure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProofStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaWeightArithmeticAtPlace_proof : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.ArithAt D i τ := by
  first | exact @GlobalTheory.PairWeightArith.arithAt | exact GlobalTheory.PairWeightArith.arithAt | (intros; apply GlobalTheory.PairWeightArith.arithAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompactsStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoStep_pair_measure_finite_on_compacts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → TwoStep R σ J x B m m' N → IsFiniteMeasureOnCompacts N := by
  first | exact @GlobalTheory.GaugeEx.twoStep_finite_on_compacts | exact GlobalTheory.GaugeEx.twoStep_finite_on_compacts | (intros; apply GlobalTheory.GaugeEx.twoStep_finite_on_compacts <;> assumption)
end

