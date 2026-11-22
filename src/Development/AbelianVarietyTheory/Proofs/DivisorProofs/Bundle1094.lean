import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0142
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic : GlobalTheory.EtC.B5 := by
  first | (exact @GlobalTheory.EtC.b5) | (exact GlobalTheory.EtC.b5) | (intros; apply GlobalTheory.EtC.b5  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgr
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical Topology

noncomputable section

namespace GlobalTheory.WeilLevel

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  have h : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport Φ
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport Φ
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem Bd_half_f (u y : Fin N → Af F) : Bd (Af F) (half F N) u y = u ⬝ᵥ y := by
  simp [Bd, half, dotProduct]

theorem annih_basis (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    (∀ K : Set (Fin N → Af F), IsCompact K → {y : Fin N → Af F | ∀ u ∈ K, ψ (pairA F 0 (u ⬝ᵥ y)) = 1} ∈ 𝓝 0) ∧
    ∀ U ∈ 𝓝 (0 : Fin N → Af F), ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧ IsCompact (L : Set (Af F)) ∧
      ∀ u : Fin N → Af F, (∀ l, u l ∈ L) → u ∈ U := by
  obtain ⟨lam, ν, hc⟩ := ctx_exists F hF ψ hψ N (half F N) (fun l => half_ne_zero l)
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis F N ψ lam ν (half F N) hc
  refine ⟨fun K hK => ?_, h3⟩
  have := h2 K hK
  simpa only [Bd_half_f] using this

def levelSub (L : AddSubgroup (Af F)) : AddSubgroup (VA F N) where
  carrier := {u | ∀ l, sndA F (u.1 l) ∈ L ∧ sndA F (u.2 l) ∈ L}
  zero_mem' := fun l => by simp
  add_mem' := fun ha hb l => by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]
    exact ⟨L.add_mem (ha l).1 (hb l).1, L.add_mem (ha l).2 (hb l).2⟩
  neg_mem' := fun ha l => by
    simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, map_neg]
    exact ⟨L.neg_mem (ha l).1, L.neg_mem (ha l).2⟩

theorem isOpen_levelSub {L : AddSubgroup (Af F)} (hL : IsOpen (L : Set (Af F))) :
    IsOpen (levelSub (N := N) L : Set (VA F N)) := by
  have hs : Continuous fun z : AF F => sndA F z := continuous_snd
  have e : (levelSub (N := N) L : Set (VA F N)) =
      ⋂ l, ((fun u : VA F N => sndA F (u.1 l)) ⁻¹' L ∩ (fun u : VA F N => sndA F (u.2 l)) ⁻¹' L) := by
    ext u; simp [levelSub]
  rw [e]
  refine isOpen_iInter_of_finite fun l => IsOpen.inter ?_ ?_
  · exact hL.preimage (hs.comp ((continuous_apply l).comp continuous_fst))
  · exact hL.preimage (hs.comp ((continuous_apply l).comp continuous_snd))

end GlobalTheory.WeilLevel

namespace GlobalTheory.WeilLevel

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem adele_ext {z z' : AF F} (h1 : fstA F z = fstA F z') (h2 : sndA F z = sndA F z') : z = z' := Prod.ext h1 h2

theorem pure_level [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ)
    (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → Af F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin N → Af F)) :
    ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 →
      GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  obtain ⟨hann, hbas⟩ := annih_basis (N := N) hF ψ hψ
  have hV := eventually_invariant hg.1 hg.2
  obtain ⟨L0, hL0o, hL0c, hL0V⟩ := hbas _ hV
  set c : Af F := algebraMap F (Af F) (1 / 2)
  have hK2 : IsCompact ((fun a : Fin N → Af F => c • a) '' {a | ∀ l, a l ∈ L0}) := by
    have : IsCompact {a : Fin N → Af F | ∀ l, a l ∈ L0} := by
      have := isCompact_univ_pi (fun _ : Fin N => hL0c)
      simpa [Set.pi] using this
    exact this.image (continuous_const_smul c)
  have hA1 := hann _ hg.2.isCompact
  have hA2 := hann _ hK2
  obtain ⟨L1, hL1o, -, hL1⟩ := hbas _ (Filter.inter_mem (Filter.inter_mem hV hA1) hA2)
  refine ⟨levelSub (L0 ⊓ L1), isOpen_levelSub (by rw [AddSubgroup.coe_inf]; exact hL0o.inter hL1o),
    fun u hu h1 h2 => ?_⟩
  set a : Fin N → Af F := fun l => sndA F (u.1 l)
  set b : Fin N → Af F := fun l => sndA F (u.2 l)
  have ha0 : ∀ l, a l ∈ L0 := fun l => (AddSubgroup.mem_inf.mp (hu l).1).1
  have ha1 : ∀ l, a l ∈ L1 := fun l => (AddSubgroup.mem_inf.mp (hu l).1).2
  have hb1 : ∀ l, b l ∈ L1 := fun l => (AddSubgroup.mem_inf.mp (hu l).2).2
  obtain ⟨⟨hVa, -⟩, -⟩ := hL1 a ha1
  obtain ⟨⟨-, hAb⟩, hA2b⟩ := hL1 b hb1
  have i1 : ∀ l, fstA F (u.1 l) = 0 := fun l => congrFun h1 l
  have i2 : ∀ l, fstA F (u.2 l) = 0 := fun l => congrFun h2 l
  funext x
  set xf : Fin N → Af F := fun i => (x i).2
  have ex : (fun i => ((x + u.1) i).2) = xf + a := by
    funext i; rfl
  have ex' : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    have : ((x + u.1) i).1 = (x i).1 := by
      show (x i).1 + (u.1 i).1 = (x i).1
      rw [show (u.1 i).1 = fstA F (u.1 i) from rfl, i1 i, add_zero]
    rw [this]
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.pureA]
  rw [ex, ex', hVa xf]
  by_cases hg0 : g xf = 0
  · rw [hg0]; simp
  have hxK : xf ∈ tsupport g := subset_tsupport g hg0
  have e : x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2) = pairA F 0 (xf ⬝ᵥ b) + pairA F 0 ((c • a) ⬝ᵥ b) := by
    apply adele_ext
    · simp only [map_add, map_mul]
      rw [show fstA F (x ⬝ᵥ u.2) = (fstA F).toRingHom (x ⬝ᵥ u.2) from rfl,
        show fstA F (u.1 ⬝ᵥ u.2) = (fstA F).toRingHom (u.1 ⬝ᵥ u.2) from rfl, RingHom.map_dotProduct, RingHom.map_dotProduct]
      have : (fstA F).toRingHom ∘ u.2 = 0 := funext i2
      rw [this, dotProduct_zero, dotProduct_zero, mul_zero, add_zero]
      rw [show ∀ p, fstA F (pairA F 0 p) = 0 from fun _ => rfl, show ∀ p, fstA F (pairA F 0 p) = 0 from fun _ => rfl, add_zero]
    · simp only [map_add, map_mul]
      rw [show sndA F (x ⬝ᵥ u.2) = (sndA F).toRingHom (x ⬝ᵥ u.2) from rfl,
        show sndA F (u.1 ⬝ᵥ u.2) = (sndA F).toRingHom (u.1 ⬝ᵥ u.2) from rfl, RingHom.map_dotProduct, RingHom.map_dotProduct,
        invOf_two_eq, AlgHom.commutes, smul_dotProduct, smul_eq_mul]
      rw [show ∀ p, sndA F (pairA F 0 p) = p from fun _ => rfl, show ∀ p, sndA F (pairA F 0 p) = p from fun _ => rfl]
      rfl
  rw [e, AddChar.map_add_eq_mul, hAb _ hxK, hA2b _ ⟨a, ha0, rfl⟩]
  ring

end GlobalTheory.WeilLevel

namespace GlobalTheory.WeilLevel

theorem schA_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ),
    IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), ∃ U : AddSubgroup (VA F N),
      IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → GlobalTheory.WeilM.schr ψ u Φ = Φ := by
  intro F _ _ N _ ψ hF hψ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pure_level ψ hF hψ f g hg
  | zero =>
    exact ⟨⊤, isOpen_univ, fun u _ _ _ => by funext x; simp [GlobalTheory.WeilM.schr]⟩
  | add Φ Φ' _ _ h h' =>
    obtain ⟨U, hU, hUΦ⟩ := h
    obtain ⟨U', hU', hUΦ'⟩ := h'
    refine ⟨U ⊓ U', by rw [AddSubgroup.coe_inf]; exact hU.inter hU', fun u hu h1 h2 => ?_⟩
    funext x
    have e1 := congrFun (hUΦ u (AddSubgroup.mem_inf.mp hu).1 h1 h2) x
    have e2 := congrFun (hUΦ' u (AddSubgroup.mem_inf.mp hu).2 h1 h2) x
    simp only [GlobalTheory.WeilM.schr, Pi.add_apply] at e1 e2 ⊢
    rw [mul_add, e1, e2]
  | smul c Φ _ h =>
    obtain ⟨U, hU, hUΦ⟩ := h
    refine ⟨U, hU, fun u hu h1 h2 => ?_⟩
    funext x
    have e1 := congrFun (hUΦ u hu h1 h2) x
    simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul] at e1 ⊢
    rw [mul_left_comm, e1]

end GlobalTheory.WeilLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMemStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_restrict_translated_diagonal_mem : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ ⊕ κ → AF F) → ℂ), φ ∈ schA F (κ ⊕ κ) → ∀ u : κ → AF F, (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi F κ := by
  first | exact @GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi | exact GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi | (intros; apply GlobalTheory.DiagShift.shift_mem_schwartzBruhatPi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_unitary_character_trivial_at_nonsplit_place : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ v ε, NonSplitAt D v ε → ∀ ν : GA D V →* Circle, (∀ k, SuppPl ε V k → (∀ y, y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ (finMat D.sp.cm.sig V.gram k).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E))) → ν k = 1) → ∀ g, SuppPl ε V g → ν g = 1 := by
  first | exact @GlobalTheory.InertChar.char_eq_one_of_nonSplit | exact GlobalTheory.InertChar.char_eq_one_of_nonSplit | (intros; apply GlobalTheory.InertChar.char_eq_one_of_nonSplit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisHenselExistsUniqueSqrtStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_hensel_exists_unique_sqrt : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    ∀ u : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL u → IsSmallB v bL (u - 1) →
    ∃ f : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑f ∧ IsIntB v bL ↑f⁻¹ ∧ (f : v.adicCompletion ℚ ⊗[ℚ] L) ^ 2 = u ∧
      IsSmallB v bL (↑f - 1) ∧
      ∀ g : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL g → g ^ 2 = u → IsSmallB v bL (g - 1) → g = ↑f := by
  first | (exact @GlobalTheory.AdicSpan.HenselSqrt.exists_sqrt) | (exact GlobalTheory.AdicSpan.HenselSqrt.exists_sqrt) | (intros; apply GlobalTheory.AdicSpan.HenselSqrt.exists_sqrt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisIffExistsIntegralMultipleStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_iff_exists_integral_multiple : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ z : L,
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] z) ↔ ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral) | (exact GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisOfTraceMemEventuallyStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_of_trace_mem_eventually : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ E : v.adicCompletion ℚ ⊗[ℚ] L,
      (∀ i, Algebra.trace (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)
          (E * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i)) ∈ v.adicCompletionIntegers ℚ) →
        IsIntB v bL E := by
  first | (exact @GlobalTheory.LocIntSpan.isIntB_of_trace_mem) | (exact GlobalTheory.LocIntSpan.isIntB_of_trace_mem) | (intros; apply GlobalTheory.LocIntSpan.isIntB_of_trace_mem  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisRingEventuallyStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_ring_eventually : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (κ : Type) (b : Module.Basis κ ℚ A),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b 1 ∧
      ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_mul_eventually) | (exact GlobalTheory.AdicSpan.isIntB_one_mul_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_mul_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicTensorExistsRationalAddIntegralMulStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicTensor_exists_rational_add_integral_mul : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L)
    (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ ⊗[ℚ] L) (D : ℤ), D ≠ 0 →
    ∃ (y : L) (ρ : v.adicCompletion ℚ ⊗[ℚ] L), IsIntB v ℓ ρ ∧
      x = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y + (D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ := by
  first | (exact @GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB) | (exact GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB) | (intros; apply GlobalTheory.AdicSpan.exists_tmul_add_mul_isIntB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointBlockOrthogonality
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult.AdPCasimir

variable {R S : ℕ}

lemma adP_Eab_eq (a b : Ix R S) (y z : NC R S) :
    adP (Eab b a) y z = (if y.1 = (b, z.1.2) then (if a = z.1.1 then 1 else 0) else 0)
      - (if y.1 = (z.1.1, a) then (if b = z.1.2 then 1 else 0) else 0) := by
  obtain ⟨⟨y1, y2⟩, hy⟩ := y
  obtain ⟨⟨z1, z2⟩, hz⟩ := z
  simp only [adP, Formalism.BasicNotions.TH.Eab, Matrix.single_apply, Prod.mk.injEq]
  congr 1
  · by_cases h1 : y1 = b <;> by_cases h2 : y2 = z2 <;> by_cases h3 : a = z1 <;> simp [h1, h2, h3, eq_comm]
    exact fun h => h1 h.symm
  · by_cases h1 : y1 = z1 <;> by_cases h2 : y2 = a <;> by_cases h3 : b = z2 <;> simp [h1, h2, h3, eq_comm]
    exact fun h => h2 h.symm

lemma sum_point (p q : Ix R S × Ix R S) (c d : ℂ) :
    ∑ y : NC R S, (if y.1 = p then c else 0) * (if y.1 = q then d else 0)
      = if ¬ sameBlock p.1 p.2 ∧ p = q then c * d else 0 := by
  by_cases hp : sameBlock p.1 p.2
  · rw [if_neg (by simp [hp])]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg, zero_mul]
    rintro rfl
    exact y.2 hp
  · rw [Finset.sum_eq_single (⟨p, hp⟩ : NC R S)]
    · by_cases h : p = q <;> simp [h, hp]
      subst h
      simp [hp]
    · intro y _ hy
      rw [if_neg, zero_mul]
      intro h
      exact hy (Subtype.ext h)
    · simp

lemma star_adP (a b : Ix R S) (y z : NC R S) :
    (starRingEnd ℂ) (adP (Eab b a) y z) = adP (Eab b a) y z := by
  rw [adP_Eab_eq]
  split_ifs <;> simp

theorem sum_adP_mul_adP (R S : ℕ) (z w : NC R S) :
    ∑ a : Ix R S, ∑ b : Ix R S, (if sameBlock a b then
      ∑ y : NC R S, (starRingEnd ℂ) (adP (Eab b a) y z) * adP (Eab b a) y w else 0)
      = if z = w then ((R + S : ℕ) : ℂ) else 0 := by
  simp only [star_adP]
  simp only [adP_Eab_eq, sub_mul, mul_sub, Finset.sum_sub_distrib, sum_point]
  obtain ⟨⟨z1, z2⟩, hz⟩ := z
  obtain ⟨⟨w1, w2⟩, hw⟩ := w
  simp only [Subtype.mk.injEq, Prod.mk.injEq]
  rcases z1 with z1 | z1 <;> rcases z2 with z2 | z2 <;> rcases w1 with w1 | w1 <;> rcases w2 with w2 | w2 <;>
    first
    | exact absurd trivial hz
    | exact absurd trivial hw
    | skip
  all_goals
    simp [Fintype.sum_sum_type, Formalism.BasicNotions.TH.sameBlock, Finset.sum_add_distrib]
  all_goals
    by_cases h1 : z1 = w1 <;> by_cases h2 : z2 = w2 <;> simp [h1, h2, eq_comm, add_comm]

end GlobalTheory.SteepMult.AdPCasimir
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointInjectiveOnPart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.AdjPart

theorem adjoint_injective_on_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks), (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R hP hB p w hw h0
  have h2 := hB A3.A.μ0 p w hw
  rw [LinearMap.comp_apply, h0, map_zero, Formalism.IndefR.Links.RealDat3.prod_lamN] at h2
  have hpos : 0 < R.kap * ∏ j : Fin D.R.m, R.lam3 j A3.A.μ0 p A3.A.v0 :=
    mul_pos hP.1 (Finset.prod_pos fun j _ => hP.2 j A3.A.μ0 p)
  have hne : ((R.kap * ∏ j : Fin D.R.m, R.lam3 j A3.A.μ0 p A3.A.v0 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  exact (smul_eq_zero.1 h2.symm).resolve_left hne

end GlobalTheory.AdjPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostAllPlacesBasisIntegral
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almost_all_places_basis_integral : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (κ : Type) (ℓ : Module.Basis κ ℚ L) (κ' : Type) (b : Module.Basis κ' ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      IsIntB v b (∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)) ↔ ∀ i, IsIntB v ℓ (β i) := by
  first | (exact @GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually) | (exact GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually) | (intros; apply GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually  <;> assumption)
end

