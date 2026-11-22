import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductHeckeSum
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0733
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0732
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0738
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LUnlinkedIrr
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalSmoothModule
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CompanionTheory.StableMod

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem isCuspForm_fin (k : GL (Fin a) (Af E)) {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (finRep E a k φ) := by
  open GlobalTheory.CuspStab in
  obtain ⟨hA, hC⟩ := h
  refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · change φ.1 (ratGL E a γ * g * finGL E a k) = φ.1 (g * finGL E a k)
    rw [mul_assoc, hA.left]
  · have e : {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ} =
        (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E a k' φ = φ} := by
      ext k'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
      constructor
      · intro e
        rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply]
      · intro e
        have := congrArg (finRep E a k) e
        rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E a k), ← map_mul,
          mul_inv_cancel, map_one, Module.End.one_apply] at this
    change IsOpen {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ}
    rw [e]
    exact hA.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E a c φ)).map
      (finRep E a k)) (Submodule.span_le.2 ?_)
    rintro _ ⟨c, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
  · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) hA.zfin
  · obtain ⟨C, N, h1⟩ := hA.growth (g * finGL E a k)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (g * infGL E a y * finGL E a k)‖ ≤ _
    rw [mul_assoc, infGL_comm, ← mul_assoc]
    exact h1 y
  · intro r h0 h1 _ _ μ 𝓕 hμ hF g
    change ∫ x in 𝓕, φ.1 (unip x * g * finGL E a k) ∂μ = 0
    simp_rw [mul_assoc]
    exact hC r h0 h1 μ 𝓕 hμ hF (g * finGL E a k)

theorem isCuspForm_cpt (c : Kinf E a) {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (cptRep E a c φ) := by
  open GlobalTheory.CuspStab in
  obtain ⟨hA, hC⟩ := h
  refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits c)) = φ.1 (g * infGL E a (Unitary.toUnits c))
    rw [mul_assoc, hA.left]
  · exact level_of_le hA.level fun k hk => by
      change finRep E a k (cptRep E a c φ) = cptRep E a c φ
      rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E a c φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨c', rfl⟩
    refine Submodule.subset_span ⟨c' * c, ?_⟩
    change _ = (cptRep E a c' * cptRep E a c) φ
    rw [← map_mul]
  · exact zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_compactRep E a c z hz) hA.zfin
  · obtain ⟨C, N, h1⟩ := growth_mul (Unitary.toUnits c) (hA.growth g)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits c))‖ ≤ _
    rw [mul_assoc, ← map_mul]
    exact h1 y
  · intro r h0 h1 _ _ μ 𝓕 hμ hF g
    change ∫ x in 𝓕, φ.1 (unip x * g * infGL E a (Unitary.toUnits c)) ∂μ = 0
    simp_rw [mul_assoc]
    exact hC r h0 h1 μ 𝓕 hμ hF (g * infGL E a (Unitary.toUnits c))

theorem lieD_left {φ : Sm E a} (X : Lie E a) {u : GA E a} (hu : ∀ g, φ.1 (u * g) = φ.1 g) (g : GA E a) :
    (lie E a X φ).1 (u * g) = (lie E a X φ).1 g := by
  change lieD X φ.1 (u * g) = lieD X φ.1 g
  have e : chart φ.1 (u * g) = chart φ.1 g := by
    funext x
    unfold chart
    split_ifs
    · rw [mul_assoc, hu]
    · rfl
  unfold lieD
  rw [e]

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (H : Submodule ℂ (L2 (latticeGL E a) μ))

def formSpace (hH : IsSubrep (R (latticeGL E a) μ) H) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
    ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H}
  zero_mem' := by
    refine ⟨⟨isAutForm_const (zero_mem _), fun r _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩, fun _ _ => rfl, ?_⟩
    have h : MemL2Quotient (latticeGL E a) μ (0 : Sm E a).1 := ⟨fun _ _ _ => rfl, MemLp.zero⟩
    refine ⟨h, ?_⟩
    have : h.toL2 = 0 := MemLp.toLp_zero _
    rw [this]
    exact zero_mem _
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3, h4⟩ ⟨h5, h6, h7, h8⟩
    have e := GlobalTheory.CuspFormLin.isCuspForm_smul_add E a 1 φ ψ h1 h5
    rw [one_smul] at e
    refine ⟨e, fun t g => ?_, ?_⟩
    · exact congrArg₂ (· + ·) (h2 t g) (h6 t g)
    · have h : MemL2Quotient (latticeGL E a) μ (φ + ψ).1 := ⟨fun γ hγ g => congrArg₂ (· + ·) (h3.1 γ hγ g) (h7.1 γ hγ g), h3.2.add h7.2⟩
      refine ⟨h, ?_⟩
      have : h.toL2 = h3.toL2 + h7.toL2 := MemLp.toLp_add h3.2 h7.2
      rw [this]
      exact add_mem h4 h8
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3, h4⟩
    have hz : IsCuspForm (0 : Sm E a) :=
      ⟨isAutForm_const (zero_mem _), fun r _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩
    have e := GlobalTheory.CuspFormLin.isCuspForm_smul_add E a c φ 0 h1 hz
    rw [add_zero] at e
    refine ⟨e, fun t g => congrArg (c • ·) (h2 t g), ?_⟩
    have h : MemL2Quotient (latticeGL E a) μ (c • φ).1 := ⟨fun γ hγ g => congrArg (c • ·) (h3.1 γ hγ g), h3.2.const_smul c⟩
    refine ⟨h, ?_⟩
    have : h.toL2 = c • h3.toL2 := MemLp.toLp_const_smul c h3.2
    rw [this]
    exact H.smul_mem c h4

open GroundTheory.Automorphic in

theorem exists_stable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)) (_ : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) :
    ∃ V : Submodule ℂ (Sm E a), (∀ φ, φ ∈ V ↔ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) ∧ IsStable V := by
  have hS : IsSubrep (R (latticeGL E a) μ) H := hi.1
  refine ⟨formSpace μ H hS, fun φ => Iff.rfl, ?_⟩
  rintro o φ ⟨h1, h2, h3, h4⟩
  cases o with
  | fin k =>
    refine ⟨isCuspForm_fin k h1, fun t g => ?_, h3.mul_right (finGL E a k), ?_⟩
    · change φ.1 (splitCentre E a t * g * finGL E a k) = φ.1 (g * finGL E a k)
      rw [mul_assoc, h2]
    · exact (right_translate_toL2 h3 _) ▸ hS.2 _ _ h4
  | cpt k =>
    refine ⟨isCuspForm_cpt k h1, fun t g => ?_, h3.mul_right (infGL E a (Unitary.toUnits k)), ?_⟩
    · change φ.1 (splitCentre E a t * g * infGL E a (Unitary.toUnits k)) = φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mul_assoc, h2]
    · exact (right_translate_toL2 h3 _) ▸ hS.2 _ _ h4
  | lie X =>
    letI : MeasurableSpace (AutomorphicForm.archGroup E a) := borel _
    haveI : BorelSpace (AutomorphicForm.archGroup E a) := ⟨rfl⟩
    obtain ⟨D, hD, hDc, hrep⟩ := GlobalTheory.T.lie_derivative_convolution_kernel E a (Measure.haar : Measure (AutomorphicForm.archGroup E a)) φ h1.1 X
    have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h1.1.level
    obtain ⟨h', hW⟩ := GlobalTheory.T.l2_convolution_locally_compact_mem (latticeGL E a) μ (Measure.haar : Measure (AutomorphicForm.archGroup E a))
      (AutomorphicForm.infEmb E a) AutomorphicForm.continuous_infEmb D hD hDc φ.1 (lie E a X φ).1 hc h3 hrep
    refine ⟨⟨⟨fun γ g => lieD_left X (h1.1.left γ) g, ?_, GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative E a X φ h1.1.kfin,
      GlobalTheory.CuspStab.zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_lie_action E a X z hz) h1.1.zfin,
      GlobalTheory.T.moderate_growth_convolution_integral E a _ φ.1 _ hc h1.1.growth D hD hDc hrep⟩, GlobalTheory.T.isCuspidal_lieAction_of_isCuspForm E a X φ h1⟩,
      fun t g => lieD_left X (h2 t) g, h', hW H hS h4⟩
    exact GlobalTheory.CuspStab.level_of_le h1.1.level fun k hk => by
      change finRep E a k (lie E a X φ) = lie E a X φ
      change (rt E a (finGL E a k) * lie E a X) φ = _
      rw [← lie_rt_fin, Module.End.mul_apply]
      exact congrArg (lie E a X) hk

end GlobalTheory.CompanionTheory.StableMod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

variable (k d) in

@[ext] structure COSub where

  sub : AddSubgroup (Fin d → k)
  isOpen : IsOpen (sub : Set (Fin d → k))
  isCompact : IsCompact (sub : Set (Fin d → k))

def gHom (g : GL (Fin d) k) : (Fin d → k) →+ (Fin d → k) :=
  (Matrix.mulVecLin (g : Matrix (Fin d) (Fin d) k)).toAddMonoidHom

theorem gHom_apply (g : GL (Fin d) k) (y : Fin d → k) : gHom g y = (g : Matrix (Fin d) (Fin d) k).mulVec y := rfl

def COSub.act (L : COSub k d) (g : GL (Fin d) k) : COSub k d where
  sub := L.sub.comap (gHom g⁻¹)
  isOpen := L.isOpen.preimage (glHomeo g).symm.continuous
  isCompact := (glHomeo g).symm.isCompact_preimage.2 L.isCompact

theorem COSub.mem_act {L : COSub k d} {g : GL (Fin d) k} {y : Fin d → k} :
    y ∈ (L.act g).sub ↔ ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y ∈ L.sub := Iff.rfl

theorem COSub.mulVec_mem_act {L : COSub k d} (g : GL (Fin d) k) {y : Fin d → k} :
    (g : Matrix (Fin d) (Fin d) k).mulVec y ∈ (L.act g).sub ↔ y ∈ L.sub := by
  rw [COSub.mem_act, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem COSub.act_one (L : COSub k d) : L.act 1 = L := by
  ext y
  simp [COSub.mem_act]

theorem COSub.act_act (L : COSub k d) (g h : GL (Fin d) k) : (L.act g).act h = L.act (h * g) := by
  ext y
  simp only [COSub.mem_act, mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev]

theorem COSub.act_mono {L L' : COSub k d} (h : L'.sub ≤ L.sub) (g : GL (Fin d) k) :
    (L'.act g).sub ≤ (L.act g).sub := fun _ hy => h hy

def lat0 : COSub k d where
  sub :=
    { carrier := {y | ∀ i, ValuativeRel.valuation k (y i) ≤ 1}
      add_mem' := fun ha hb i => by
        rw [Pi.add_apply]
        exact (Valuation.map_add _ _ _).trans (max_le (ha i) (hb i))
      zero_mem' := fun i => by simp
      neg_mem' := fun ha i => by
        rw [Pi.neg_apply, Valuation.map_neg]
        exact ha i }
  isOpen := by
    have e : {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1} = Set.univ.pi fun _ => cball (1 : kˣ) := by
      ext y
      simp [cball, Set.mem_pi]
    show IsOpen {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1}
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball 1
  isCompact := by
    have e : {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1} = Set.univ.pi fun _ => cball (1 : kˣ) := by
      ext y
      simp [cball, Set.mem_pi]
    show IsCompact {y : Fin d → k | ∀ i, ValuativeRel.valuation k (y i) ≤ 1}
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_cball 1

def latZ (z : GL (Fin d) k) (r : ℤ) : COSub k d := lat0.act (z ^ r)

def IsReps (L' L : COSub k d) (S : Finset (Fin d → k)) : Prop :=
  (∀ s ∈ S, s ∈ L.sub) ∧ ∀ y ∈ L.sub, ∃! s, s ∈ S ∧ y - s ∈ L'.sub

theorem isClopen_coset (L : COSub k d) (c : Fin d → k) : IsClopen {y | y - c ∈ L.sub} :=
  ⟨L.isCompact.isClosed.preimage (continuous_id.sub continuous_const),
    L.isOpen.preimage (continuous_id.sub continuous_const)⟩

open Classical in

def ind (L : COSub k d) (c : Fin d → k) (a : V) : SchF k d V :=
  ⟨fun y => if y - c ∈ L.sub then a else 0, by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, ?_⟩
    · by_cases hx : x - c ∈ L.sub
      · filter_upwards [(isClopen_coset L c).isOpen.mem_nhds hx] with y hy
        have hy' : y - c ∈ L.sub := hy
        rw [if_pos hx, if_pos hy']
      · filter_upwards [(isClopen_coset L c).compl.isOpen.mem_nhds hx] with y hy
        have hy' : y - c ∉ L.sub := hy
        rw [if_neg hx, if_neg hy']
    · refine HasCompactSupport.intro (L.isCompact.image (continuous_add_right c)) fun x hx => ?_
      rw [if_neg]
      intro h
      exact hx ⟨x - c, h, by simp⟩⟩

open Classical in
theorem ind_apply (L : COSub k d) (c y : Fin d → k) (a : V) :
    (ind L c a).1 y = if y - c ∈ L.sub then a else 0 := rfl

theorem ind_add_mem (L : COSub k d) (x : Fin d → k) {l : Fin d → k} (hl : l ∈ L.sub) (a : V) :
    ind L (x + l) a = ind L x a := by
  refine Subtype.ext (funext fun y => ?_)
  rw [ind_apply, ind_apply]
  have : y - (x + l) ∈ L.sub ↔ y - x ∈ L.sub := by
    have e : y - (x + l) = y - x - l := by abel
    rw [e]
    exact ⟨fun h => by simpa using L.sub.add_mem h hl, fun h => L.sub.sub_mem h hl⟩
  by_cases h : y - x ∈ L.sub
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg (mt this.1 h)]

theorem ind_add (L : COSub k d) (c : Fin d → k) (a b : V) : ind L c (a + b) = ind L c a + ind L c b := by
  refine Subtype.ext (funext fun y => ?_)
  show (ind L c (a + b)).1 y = (ind L c a).1 y + (ind L c b).1 y
  simp only [ind_apply]
  split_ifs <;> simp

theorem ind_smul (L : COSub k d) (c : Fin d → k) (t : ℂ) (a : V) : ind L c (t • a) = t • ind L c a := by
  refine Subtype.ext (funext fun y => ?_)
  show (ind L c (t • a)).1 y = t • (ind L c a).1 y
  simp only [ind_apply]
  split_ifs <;> simp

theorem shiftF_ind (L : COSub k d) (x c : Fin d → k) (a : V) : shiftF x (ind L c a) = ind L (c - x) a := by
  refine Subtype.ext (funext fun y => ?_)
  rw [shiftF_apply, ind_apply, ind_apply]
  have e : y + x - c = y - (c - x) := by abel
  rw [e]

theorem actF_ind (X : Representation ℂ (GL (Fin d) k) V) (g : GL (Fin d) k) (L : COSub k d) (c : Fin d → k) (a : V) :
    actF X g (ind L c a) = ind (L.act g) ((g : Matrix (Fin d) (Fin d) k).mulVec c) (X g a) := by
  refine Subtype.ext (funext fun y => ?_)
  rw [actF_apply, ind_apply, ind_apply]
  have e : ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec (y - (g : Matrix (Fin d) (Fin d) k).mulVec c) =
      ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y - c := by
    rw [mulVec_sub, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have h : (y - (g : Matrix (Fin d) (Fin d) k).mulVec c ∈ (L.act g).sub) ↔
      ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y - c ∈ L.sub := by
    rw [COSub.mem_act, e]
  by_cases hc : ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y - c ∈ L.sub
  · rw [if_pos hc, if_pos (h.2 hc)]
  · rw [if_neg hc, if_neg (mt h.1 hc), map_zero]

def mL (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a : V) (a' : V') : ℂ :=
  B (ind L x a) (ind L 0 a')

theorem B_ind_ind (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hT : ∀ x f f', B (shiftF x f) (shiftF x f') = B f f') (L : COSub k d) (c c' : Fin d → k) (a : V) (a' : V') :
    B (ind L c a) (ind L c' a') = mL B L (c - c') a a' := by
  rw [mL, ← hT c' (ind L c a) (ind L c' a'), shiftF_ind, shiftF_ind, sub_self]

theorem mL_act (X : Representation ℂ (GL (Fin d) k) V) (Y : Representation ℂ (GL (Fin d) k) V')
    (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hG : ∀ g f f', B (actF X g f) (actF Y g f') = B f f') (g : GL (Fin d) k) (L : COSub k d) (x : Fin d → k)
    (a : V) (a' : V') :
    mL B (L.act g) ((g : Matrix (Fin d) (Fin d) k).mulVec x) (X g a) (Y g a') = mL B L x a a' := by
  rw [mL, mL, ← hG g (ind L x a) (ind L 0 a'), actF_ind, actF_ind, mulVec_zero]

theorem mL_add_mem (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) {l : Fin d → k}
    (hl : l ∈ L.sub) (a : V) (a' : V') : mL B L (x + l) a a' = mL B L x a a' := by
  rw [mL, mL, ind_add_mem L x hl]

theorem mL_add_left (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a b : V) (a' : V') :
    mL B L x (a + b) a' = mL B L x a a' + mL B L x b a' := by
  simp [mL, ind_add]

theorem mL_add_right (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a : V) (a' b' : V') :
    mL B L x a (a' + b') = mL B L x a a' + mL B L x a b' := by
  simp [mL, ind_add]

theorem mL_smul_left (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (t : ℂ) (a : V) (a' : V') :
    mL B L x (t • a) a' = t * mL B L x a a' := by
  simp [mL, ind_smul]

theorem mL_smul_right (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ) (L : COSub k d) (x : Fin d → k) (a : V) (t : ℂ) (a' : V') :
    mL B L x a (t • a') = t * mL B L x a a' := by
  simp [mL, ind_smul]

def Refines (F : COSub k d → (Fin d → k) → ℂ) : Prop :=
  ∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S → ∀ x,
    (S.card : ℂ) * F L x = ∑ s ∈ S, F L' (x + s)

end GlobalTheory.CompanionTheory.BZCore

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixPreservesIntegersAlmostAll
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.MatInt

theorem algebraMap_mem_integers_of_not_mem_support (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : F) (h : v ∉ HeightOneSpectrum.Support (𝓞 F) a) :
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : Valued.v (algebraMap F (Fv F v) a) = v.valuation F a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  rw [e]
  simpa [HeightOneSpectrum.Support] using h

theorem mulVec_mem_integers (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (v : HeightOneSpectrum (𝓞 F)) (B : Matrix ι ι (Fv F v)) (y : ι → Fv F v)
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F)
    (hy : ∀ i, y i ∈ v.adicCompletionIntegers F) (i : ι) :
    B.mulVec y i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hB i j) (hy j)

theorem exists_finset_mulVec_integral_iff : ∀ (F : Type) [Field F] [NumberField F] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 →
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ x : ι → Fv F v,
      (∀ i, (A.map (algebraMap F (Fv F v))).mulVec x i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
  intro F _ _ ι _ _ A hA
  classical
  have hfin : ∀ a : F, (HeightOneSpectrum.Support (𝓞 F) a).Finite :=
    HeightOneSpectrum.Support.finite (𝓞 F)
  refine ⟨Finset.univ.biUnion fun p : ι × ι =>
    (hfin (A p.1 p.2)).toFinset ∪ (hfin (A⁻¹ p.1 p.2)).toFinset, fun v hv x => ?_⟩
  have hout : ∀ i j, v ∉ HeightOneSpectrum.Support (𝓞 F) (A i j) ∧
      v ∉ HeightOneSpectrum.Support (𝓞 F) (A⁻¹ i j) := by
    intro i j
    constructor
    · intro h
      exact hv (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_union_left _ ((hfin _).mem_toFinset.2 h)⟩)
    · intro h
      exact hv (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_union_right _ ((hfin _).mem_toFinset.2 h)⟩)
  have hinv : (A⁻¹.map (algebraMap F (Fv F v))) * (A.map (algebraMap F (Fv F v))) = 1 := by
    have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
    have h1 := congrArg (fun M : Matrix ι ι F => M.map (algebraMap F (Fv F v)))
      (Matrix.nonsing_inv_mul A hu)
    simpa [Matrix.map_mul] using h1
  constructor
  · intro h i
    have e : (A⁻¹.map (algebraMap F (Fv F v))).mulVec
        ((A.map (algebraMap F (Fv F v))).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [← e]
    exact mulVec_mem_integers F ι v _ _
      (fun i j => algebraMap_mem_integers_of_not_mem_support F v _ (hout i j).2) h i
  · intro h i
    exact mulVec_mem_integers F ι v _ _
      (fun i j => algebraMap_mem_integers_of_not_mem_support F v _ (hout i j).1) h i

end GlobalTheory.CompanionTheory.MatInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductHeckeSumStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_hecke_sum : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (KH V : ∀ i, Subgroup (Hl i)) (f : ∀ i, Hl i → ℂ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hev : ∀ x, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hVK : ∀ i, V i ≤ KH i) (hVi : ∀ i, (V i).relIndex (KH i) ≠ 0)
    (hVe : ∀ᶠ i in cofinite, V i = KH i)
    (hfV : ∀ i, ∀ u ∈ V i, ∀ x, f i (x * u) = f i x)
    (hfs : ∀ i, {q : Hl i ⧸ V i | f i q.out ≠ 0}.Finite)
    (T : List ι) (hT : T.Nodup) (g : Γ → ℂ) (hg : ∀ u, (∀ i, p i u ∈ V i) → ∀ x, g (x * u) = g x) (y : Γ),
    ∑ᶠ q : Γ ⧸ (⨅ i, (V i).comap (p i)),
        (∏ᶠ j, if j ∈ T then f j (p j q.out) else (V j : Set (Hl j)).indicator (1 : Hl j → ℂ) (p j q.out)) * g (y * q.out) =
      (T.map fun i => (((V i).relIndex (KH i) : ℕ) : ℂ)).prod *
        T.foldr (fun i g' x => hint (KH i) fun m => f i m * g' (x * e i m)) g y := by
  first | exact @GlobalTheory.CompanionTheory.FinActSum.sum_formula | exact GlobalTheory.CompanionTheory.FinActSum.sum_formula | (intros; apply GlobalTheory.CompanionTheory.FinActSum.sum_formula <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_product_word_in_shuffle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSegJacquet k → ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k), (∀ i, IsLSeg (Δ i) (x i).rep) → ∀ w : List (IrrGL k), (∀ c ∈ w, c.IsCusp) → Wd (prodIrr x hd) w → InShW (Finset.univ.val.map Δ) w := by
  first | exact @GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd | exact GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd | (intros; apply GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedProductIrreducibleAltBis
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lUnlinkedIrr_of_irreducibleAdmissible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.BZSeg.NuPair k → GlobalTheory.BZSeg.WhitRankStd k → GlobalTheory.BZSeg.ProdIrrFiniteLength k → GlobalTheory.BZSeg.LUnlinkedIrr k := by
  first | exact @GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr | exact GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr | (intros; apply GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr <;> assumption)
end

