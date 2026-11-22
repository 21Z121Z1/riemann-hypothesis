import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0502
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySwapReduction
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistProductDistributesStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_product_distributes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (A : GRep k r) (B : GRep k t) (s : ℝ), GIso ((A.prod B).tw s) ((A.tw s).prod (B.tw s)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod | exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistTwistAddStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_twist_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : GRep k n) (s s' : ℝ), GIso ((A.tw s).tw s') (A.tw (s + s')) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw | exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentity
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

theorem setIntegral_inter_box_of_twists {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (ψ : AddChar k Circle) (c : kˣ) (hψ : Continuous ψ) (hc : HasConductor ψ c) (m : ℕ) (t : kˣ)
    (M : Set (Fin m → k)) (f : (Fin m → k) → ℂ) (A : ℂ) (hM : IsCompact M) (hMm : MeasurableSet M)
    (hf : Continuous f)
    (h : ∀ b ∈ box m (c * t⁻¹), ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x ∂(piHaar ν m) = A) :
    ∫ x in M ∩ (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) = A := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddHaarMeasure := by
    unfold GlobalTheory.CompanionTheory.MirPair.piHaar
    infer_instance
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.MirPair.piHaar ν m) := by
    unfold GlobalTheory.CompanionTheory.MirPair.piHaar
    infer_instance
  haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddRightInvariant := inferInstance
  set μ := GlobalTheory.CompanionTheory.MirPair.piHaar ν m with hμ
  have hbox : ∀ s : kˣ, GlobalTheory.SplitWeil.FourierPi.box (Fin m) s = (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s : Set (Fin m → k)) := by
    intro s
    rw [GlobalTheory.CompanionTheory.BZOnto.PerpSmall.coe_box]
    rfl
  set B' : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m (c * t⁻¹) : Set (Fin m → k)) with hB'
  set Bt : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m t : Set (Fin m → k)) with hBt
  have hB'c : IsCompact B' := GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m _
  have hB'm : MeasurableSet B' := hB'c.isClosed.measurableSet
  have hBtm : MeasurableSet Bt := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m t).isClosed.measurableSet
  have hpos : 0 < μ.real B' := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (μ.measure_pos_of_mem_nhds (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box_mem_nhds m _)).ne'
      hB'c.measure_lt_top.ne
  have hfour : ∀ x, ∫ b, B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ x) : Circle) : ℂ) ∂μ =
      Bt.indicator (fun _ => ((μ.real B' : ℝ) : ℂ)) x := by
    intro x
    have e := GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi μ hc t x
    rw [hbox, hbox] at e
    exact e
  have hcc : Continuous (fun z : Circle => (z : ℂ)) := continuous_induced_dom
  have hdot : Continuous fun q : (Fin m → k) × (Fin m → k) => q.1 ⬝ᵥ q.2 :=
    GlobalTheory.SplitWeil.FourierPi.continuous_dot
  have hψc : Continuous fun q : (Fin m → k) × (Fin m → k) => ((ψ (-(q.1 ⬝ᵥ q.2)) : Circle) : ℂ) :=
    hcc.comp (hψ.comp hdot.neg)
  have hg1 : Integrable (B'.indicator fun _ => (1 : ℂ)) μ :=
    (integrable_indicator_iff hB'm).2 (continuousOn_const.integrableOn_compact' hB'c hB'm)
  have hg2 : Integrable (M.indicator f) μ :=
    (integrable_indicator_iff hMm).2 (hf.continuousOn.integrableOn_compact' hM hMm)
  have hint : Integrable (fun z : (Fin m → k) × (Fin m → k) => ((ψ (-(z.1 ⬝ᵥ z.2)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) z.1 * M.indicator f z.2)) (μ.prod μ) := by
    refine (hg1.mul_prod hg2).bdd_mul (c := 1) hψc.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp [Circle.norm_coe]
  have hswap : ∫ b, (∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
        (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ =
      ∫ x, (∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
        (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ :=
    integral_integral_swap hint
  have hD : (fun b => ∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) = B'.indicator (fun _ => A) := by
    funext b
    by_cases hb : b ∈ B'
    · simp only [Set.indicator_of_mem hb, one_mul]
      have hx : (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * M.indicator f x) =
          M.indicator (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x) := by
        funext x
        by_cases hxM : x ∈ M
        · simp only [Set.indicator_of_mem hxM]
        · simp only [Set.indicator_of_notMem hxM, mul_zero]
      rw [hx, integral_indicator hMm]
      exact h b hb
    · simp [Set.indicator_of_notMem hb]
  have hE : (fun x => ∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) =
      fun x => ((μ.real B' : ℝ) : ℂ) * (M ∩ Bt).indicator f x := by
    funext x
    have e : ∀ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) =
        B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ -x) : Circle) : ℂ) * M.indicator f x := by
      intro b
      rw [dotProduct_neg]
      ring
    simp only [e]
    rw [integral_mul_const, hfour (-x)]
    have hneg : -x ∈ Bt ↔ x ∈ Bt := by
      simp only [hBt, SetLike.mem_coe, neg_mem_iff]
    by_cases hxB : x ∈ Bt
    · by_cases hxM : x ∈ M
      · simp only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_mem hxM,
          Set.indicator_of_mem (Set.mem_inter hxM hxB)]
      · simp only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_notMem hxM,
          Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxM hx.1), mul_zero]
    · simp only [Set.indicator_of_notMem (fun hx : -x ∈ Bt => hxB (hneg.1 hx)),
        Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxB hx.2), zero_mul, mul_zero]
  rw [hD, hE, integral_indicator_const _ hB'm, integral_const_mul,
    integral_indicator (hMm.inter hBtm), Complex.real_smul] at hswap
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hpos.ne') hswap).symm

end GlobalTheory.CompanionTheory.MirPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantPairingCharacter
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Descend

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_uM (ψ : AddChar k Circle) (n : ℕ) (u : MirUin k (n + 1)) :
    ∃ y : Fin (n + 1) → k, (u : Mir k (n + 1)) = uM (n + 1) y ∧
      ((mirChar k ψ n u : ℂˣ) : ℂ) = ((ψ (y (Fin.last n)) : Circle) : ℂ) := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp u.2)
  refine ⟨Multiplicative.toAdd w, Subtype.ext hw.symm, ?_⟩
  rw [GlobalTheory.BZMir.mirChar_eq k ψ n u w hw.symm, Circle.toUnits_apply, Units.val_mk0]

theorem left_kill (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (f : V →ₗ[ℂ] ℂ)
    (h : ∀ (y : Fin (n + 1) → k) v, f (T (uM (n + 1) y) v) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * f v) :
    twKer T (MirUin k (n + 1)) (mirChar k ψ n) ≤ LinearMap.ker f := by
  rw [GlobalTheory.PRep.twKer, Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  obtain ⟨y, hu, hχ⟩ := GlobalTheory.CompanionTheory.MirPair.Descend.exists_uM ψ n u
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hu, h, hχ, sub_self]

theorem phiMinus_mk (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (p : Mir k n) (v : V) :
    phiMinus k ψ T p (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) := rfl

theorem descend : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), (∀ (y : Fin (n + 1) → k) v v', B₀ (T (uM (n + 1) y) v) v' = ((ψ (y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (y : Fin (n + 1) → k) v v', B₀ v (T' (uM (n + 1) y) v') = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (p : Mir k n) v v', B₀ (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B₀ v v') → (∀ v, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ v', B₀ v v' ≠ 0) → ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ, (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧ (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ n s V V' _ _ _ _ T T' B₀ hT hT' hL hnd
  have hleft : ∀ v' : V', GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker (B₀.flip v') := fun v' =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ T (B₀.flip v') fun y v => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply]
      exact hT y v v'
  have hright : ∀ v : V, GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker (B₀ v) := fun v =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ⁻¹ T' (B₀ v) fun y v' => by
      rw [AddChar.inv_apply]
      exact hT' y v v'
  have h₁ : GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker B₀ := by
    intro v hv
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun v' => ?_
    have h := LinearMap.mem_ker.mp (hleft v' hv)
    rw [LinearMap.flip_apply] at h
    rw [h, LinearMap.zero_apply]
  let B₁ : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] V' →ₗ[ℂ] ℂ :=
    Submodule.liftQ _ B₀ h₁
  have h₂ : GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker B₁.flip := by
    intro v' hv'
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact LinearMap.mem_ker.mp (hright v hv')
  let B' : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] GlobalTheory.PRep.TwJacquet T'
      (GlobalTheory.BZMir.MirUin k (n + 1)) (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ :=
    (Submodule.liftQ _ B₁.flip h₂).flip
  have hB' : ∀ (v : V) (v' : V'), B' (Submodule.Quotient.mk v) (Submodule.Quotient.mk v') = B₀ v v' :=
    fun _ _ => rfl
  refine ⟨B', ?_, ?_⟩
  · intro p w w'
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ w'
    rw [GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, hB', hB', hL]
  · intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hv : v ∉ GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
        (GlobalTheory.BZMir.mirChar k ψ n) := fun h =>
      hw ((Submodule.Quotient.mk_eq_zero _).mpr h)
    obtain ⟨v', hv'⟩ := hnd v hv
    exact ⟨Submodule.Quotient.mk v', by rw [hB']; exact hv'⟩

end GlobalTheory.CompanionTheory.MirPair.Descend

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerDividesFrobeniusDifferenceStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_divides_frobenius_difference : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), (Ideal.span {π}).IsMaximal →
    Finite (↥(OL K) ⧸ Ideal.span {π}) → ∀ c : ↥(OL K), π ∣ c ^ qOf π - c := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.dvd_pow_qOf_sub_self | exact GlobalTheory.CompanionTheory.LTPer.Tilt.dvd_pow_qOf_sub_self | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.dvd_pow_qOf_sub_self <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerResidueFieldFinitePowerStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_residue_field_finite_power : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    (Ideal.span {π}).IsMaximal ∧ Finite (↥(OL K) ⧸ Ideal.span {π}) ∧ ∃ f : ℕ, 0 < f ∧ qOf π = l ^ f := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.resfield_of_irreducible | exact GlobalTheory.CompanionTheory.LTPer.Tilt.resfield_of_irreducible | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.resfield_of_irreducible <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentCommuteShiftedEmbeddingStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_commute_shifted_embedding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k), ∃ u : HPG k (i + 1) (t + 1), (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1) ∧ (pgProj k (i + 1) (t + 1) u).2 = 1 ∧ dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * (u : Mir k ((i + 1) + t + 1)) * dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.DConj.dEmb_mul_sEmb | exact GlobalTheory.CompanionTheory.BZPhiPG.DConj.dEmb_mul_sEmb | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.DConj.dEmb_mul_sEmb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFrameLevelTriangular
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

section Frame

variable {E : Type} [Field E] {n r : ℕ} {S : E →+* E} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem cT_pre_mul (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (s : Fin r) :
    cT S (pre X s) * J = (cT S X * J).submatrix (Fin.castLE s.2) id := by
  ext i l
  simp [Matrix.mul_apply, cT, pre]

theorem mul_pre (A : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (s : Fin r) :
    A * pre X s = (A * X).submatrix id (Fin.castLE s.2) := by
  ext i l
  simp [Matrix.mul_apply, pre]

theorem castLE_ne {s i : Fin r} (hi : ¬ i ≤ s) (j : Fin (s.val + 1)) : Fin.castLE s.2 j ≠ i := by
  intro e
  apply hi
  have : (j : ℕ) = i := congrArg Fin.val e
  have hj := j.2
  exact Fin.le_def.2 (by omega)

theorem exists_frameIdem_eq_pre_mul (s : Fin r) {β : FrameIx r} (h : frameLev s β = 2) :
    ∃ Q : Matrix (Fin (s.val + 1)) (Fin n) E, frameIdem S J X Y β = pre X s * Q := by
  rcases β with _ | b | b
  · simp [frameLev] at h
  · have hb : b ≤ s := by
      by_contra hb
      simp [frameLev, hb] at h
    have hlt : b.val < s.val + 1 := Nat.lt_succ_of_le (Fin.le_def.1 hb)
    let P : Matrix (Fin (s.val + 1)) (Fin r) E := single ⟨b.val, hlt⟩ b (1 : E)
    refine ⟨P * (cT S Y * J), ?_⟩
    have e : X * (single b b (1 : E) : Matrix (Fin r) (Fin r) E) = pre X s * P := by
      ext k j
      by_cases hj : j = b
      · subst hj
        simp [P, pre, Matrix.mul_apply, Matrix.single_apply]
      · simp [P, Matrix.mul_apply, Matrix.single_apply, Ne.symm hj]
    simp only [frameIdem]
    rw [e, Matrix.mul_assoc]
  · by_cases hb : b ≤ s <;> simp [frameLev, hb] at h

theorem exists_frameIdem_eq_mul_form (s : Fin r) {α : FrameIx r} (h : frameLev s α = 0) :
    ∃ Q : Matrix (Fin n) (Fin (s.val + 1)) E, frameIdem S J X Y α = Q * (cT S (pre X s) * J) := by
  rcases α with _ | a | a
  · simp [frameLev] at h
  · by_cases ha : a ≤ s <;> simp [frameLev, ha] at h
  · have ha : a ≤ s := by
      by_contra ha
      simp [frameLev, ha] at h
    have hlt : a.val < s.val + 1 := Nat.lt_succ_of_le (Fin.le_def.1 ha)
    let P : Matrix (Fin r) (Fin (s.val + 1)) E := single a ⟨a.val, hlt⟩ (1 : E)
    refine ⟨Y * P, ?_⟩
    have e : (single a a (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S X * J) = P * (cT S (pre X s) * J) := by
      rw [cT_pre_mul]
      ext i l
      by_cases hi : i = a
      · subst hi
        simp [P, Matrix.mul_apply, Matrix.single_apply]
      · simp [P, Matrix.mul_apply, Matrix.single_apply, Ne.symm hi]
    simp only [frameIdem]
    rw [Matrix.mul_assoc, e, Matrix.mul_assoc]

variable (hxx : cT S X * J * X = 0) (hxy : cT S X * J * Y = 1) (hyx : cT S Y * J * X = 1)
include hxx hxy hyx

theorem frameIdem_mul_pre (s : Fin r) {α : FrameIx r} (h : frameLev s α = 1) : frameIdem S J X Y α * pre X s = 0 := by
  rw [mul_pre]
  rcases α with _ | i | i
  · have : (1 - X * (cT S Y * J) - Y * (cT S X * J)) * X = 0 := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hyx, Matrix.mul_one, Matrix.mul_assoc, hxx,
        Matrix.mul_zero, sub_self, sub_zero]
    simp only [frameIdem, this]
    rfl
  · have hi : ¬ i ≤ s := by
      intro hi
      simp [frameLev, hi] at h
    have : X * (single i i (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S Y * J) * X =
        X * (single i i (1 : E) : Matrix (Fin r) (Fin r) E) := by
      rw [Matrix.mul_assoc _ _ X, hyx, Matrix.mul_one]
    ext k j
    simp only [frameIdem, this, Matrix.submatrix_apply, id]
    simp [Matrix.mul_apply, Matrix.single_apply, (castLE_ne hi j).symm]
  · have : Y * (single i i (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S X * J) * X = 0 := by
      rw [Matrix.mul_assoc _ _ X, hxx, Matrix.mul_zero]
    simp only [frameIdem, this]
    rfl

theorem form_mul_frameIdem (s : Fin r) {β : FrameIx r} (h : frameLev s β = 1) :
    (cT S (pre X s) * J) * frameIdem S J X Y β = 0 := by
  have e : ∀ A : Matrix (Fin n) (Fin n) E, (cT S (pre X s) * J) * A = ((cT S X * J) * A).submatrix (Fin.castLE s.2) id := fun A => by
    rw [cT_pre_mul]
    ext i l
    simp [Matrix.mul_apply]
  rw [e]
  rcases β with _ | i | i
  · have : (cT S X * J) * (1 - X * (cT S Y * J) - Y * (cT S X * J)) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc _ X, hxx, Matrix.zero_mul,
        ← Matrix.mul_assoc _ Y, hxy, Matrix.one_mul, sub_zero, sub_self]
    simp only [frameIdem, this]
    rfl
  · have : (cT S X * J) * (X * (single i i (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S Y * J)) = 0 := by
      rw [Matrix.mul_assoc X, ← Matrix.mul_assoc _ X, hxx, Matrix.zero_mul]
    simp only [frameIdem, this]
    rfl
  · have hi : ¬ i ≤ s := by
      intro hi
      simp [frameLev, hi] at h
    have : (cT S X * J) * (Y * (single i i (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S X * J)) =
        (single i i (1 : E) : Matrix (Fin r) (Fin r) E) * (cT S X * J) := by
      rw [Matrix.mul_assoc Y, ← Matrix.mul_assoc _ Y, hxy, Matrix.one_mul]
    ext j l
    simp only [frameIdem, this, Matrix.submatrix_apply, id]
    simp [Matrix.mul_apply, Matrix.single_apply, (castLE_ne hi j).symm]

end Frame

theorem map_mul_mul_map_eq_zero {E : Type} [Field E] {n k : ℕ} (t : E →+* ℂ) {C : Matrix (Fin n) (Fin k) E}
    {T : Matrix (Fin k) (Fin n) E} {M : Matrix (Fin n) (Fin n) ℂ}
    (h3 : ∀ x : Fin n → E, T *ᵥ x = 0 → ∃ b : Fin k → ℂ, M *ᵥ (fun i => t (x i)) = C.map t *ᵥ b)
    {P Q : Matrix (Fin n) (Fin n) E} (hP : P * C = 0) (hQ : T * Q = 0) : P.map t * M * Q.map t = 0 := by
  ext i j
  obtain ⟨b, hb⟩ := h3 (fun l => Q l j) (funext fun a => congrFun (congrFun hQ a) j)
  have e1 : P.map t * C.map t = 0 := by
    rw [← Matrix.map_mul, hP]
    exact Matrix.map_zero _ (map_zero _)
  have e2 : (P.map t * M * Q.map t) i j = (P.map t *ᵥ (M *ᵥ fun l => t (Q l j))) i := by
    rw [Matrix.mulVec_mulVec]
    rfl
  rw [e2, hb, Matrix.mulVec_mulVec, e1, Matrix.zero_mulVec]
  rfl

section Unip

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem arch_of_mem_unipRad (h : IsCMExt F E σ) (hJ : IsHermND σ J) {C : Matrix (Fin n) (Fin r) E}
    (hC : GlobalTheory.UAut.IsIsoCols σ J C) {m : GAd σ J} (hm : m ∈ unipRad σ J C) (w : InfinitePlace F) (τ : EmbOver E w) :
    (archMat σ J τ (projArch σ J w m) - 1) * C.map τ.1 = 0 ∧
    (cT (σ : E →+* E) C * J).map τ.1 * (archMat σ J τ (projArch σ J w m) - 1) = 0 ∧
    ∀ x : Fin n → E, (cT (σ : E →+* E) C * J) *ᵥ x = 0 → ∃ b : Fin r → ℂ,
      (archMat σ J τ (projArch σ J w m) - 1) *ᵥ (fun i => τ.1 (x i)) = C.map τ.1 *ᵥ b := by
  have hg : m ∈ GlobalTheory.UAut.unipSet σ J C fun _ => 0 := by
    refine (GlobalTheory.UAut.mem_unipFlag hJ (GlobalTheory.SiegelSet.sigma_sigma h) hC _).1 ?_
    rw [GlobalTheory.UAut.unipFlag_const]
    exact hm
  obtain ⟨A, hA, e1⟩ := GlobalTheory.UAut.lower_iff.1 hg.1
  have h1 : ((matHom _ σ J m).1 - 1) * adMat F C = 0 := by
    rw [e1, show A = 0 from Matrix.ext fun j i => hA j i le_rfl, Matrix.mul_zero]
  have h2 : adMat F (cT (σ : E →+* E) C * J) * ((matHom _ σ J m).1 - 1) = 0 := by
    have e : (matHom _ σ J m).1 * adMat F C = adMat F C * (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) := by
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      rw [h1, Matrix.mul_one]
    have e2 := GlobalTheory.UAut.form_mul_of_mul_cols e
    have hi : (matHom _ σ J m⁻¹).1 * (matHom _ σ J m).1 = 1 := Units.inv_mul m.1
    rw [Formalism.UG.cT_one, Matrix.one_mul] at e2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
    conv_lhs => rw [← e2, Matrix.mul_assoc, hi, Matrix.mul_one]
  let φ := (infEmb τ).comp (compInf F E w)
  have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
    change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
    simp
  have hM : archMat σ J τ (projArch σ J w m) - 1 = ((matHom _ σ J m).1 - 1).map φ := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have hZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), (adMat F Z).map φ = Z.map τ.1 := fun Z =>
    Matrix.ext fun i j => h0 _
  rw [hM]
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← hZ, ← Matrix.map_mul, h1]
    exact Matrix.map_zero _ (map_zero _)
  · rw [← hZ, ← Matrix.map_mul, h2]
    exact Matrix.map_zero _ (map_zero _)
  · obtain ⟨a, ha⟩ := hg.2 x hx
    refine ⟨fun i => φ (a i), ?_⟩
    have e3 := congrArg (fun v : Fin n → AF F ⊗[F] E => fun i => φ (v i)) ha
    rw [show (fun i => τ.1 (x i)) = fun i => φ (inclR (F := F) (AF F) (x i)) from funext fun i => (h0 _).symm, ← hZ]
    funext i
    have l1 := RingHom.map_mulVec φ ((matHom _ σ J m).1 - 1) (fun i => inclR (F := F) (AF F) (x i)) i
    have l2 := RingHom.map_mulVec φ (adMat F C) a i
    exact l1.symm.trans ((congrFun e3 i).trans l2)

end Unip

theorem frameIdem_mul_unipRad_mul_frameIdem (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (s : Fin r) (m : GAd σ J)
    (hm : m ∈ unipRad σ J (pre X s)) (w : InfinitePlace F) (τ : EmbOver E w) (α β : FrameIx r)
    (hαβ : frameLev s α ≤ frameLev s β) :
    (frameIdem (σ : E →+* E) J X Y α).map τ.1 * (archMat σ J τ (projArch σ J w m) - 1) *
      (frameIdem (σ : E →+* E) J X Y β).map τ.1 = 0 := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma h
  have yx : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, show cT (σ : E →+* E) (cT (σ : E →+* E) X) = X from
      Matrix.ext fun i j => hσ _, GlobalTheory.UAut.cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have hC : GlobalTheory.UAut.IsIsoCols σ J (pre X s) :=
    GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ s.2
  obtain ⟨h1, h2, h3⟩ := arch_of_mem_unipRad h hJ hC hm w τ
  have hβ : frameLev s β ≤ 2 := by
    rcases β with _ | b | b <;> simp only [frameLev] <;> try split_ifs
    all_goals omega
  by_cases e2 : frameLev s β = 2
  · obtain ⟨Q, hQ⟩ := exists_frameIdem_eq_pre_mul (S := (σ : E →+* E)) (J := J) (Y := Y) s e2
    rw [hQ, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ ((pre X s).map τ.1), h1, Matrix.zero_mul,
      Matrix.mul_zero]
  by_cases e0 : frameLev s α = 0
  · obtain ⟨Q, hQ⟩ := exists_frameIdem_eq_mul_form (S := (σ : E →+* E)) (J := J) (X := X) (Y := Y) s e0
    rw [hQ, Matrix.map_mul, Matrix.mul_assoc (Q.map τ.1), h2, Matrix.mul_zero, Matrix.zero_mul]
  have hα : frameLev s α = 1 := by omega
  have hβ' : frameLev s β = 1 := by
    have : frameLev s β ≠ 0 := by omega
    omega
  exact map_mul_mul_map_eq_zero τ.1 h3 (frameIdem_mul_pre hW.xx hW.xy yx s hα) (form_mul_frameIdem hW.xx hW.xy yx s hβ')

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySwapReductionStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_swap_reduction : PositivityTheory.SphericalProduct.SwapStepU := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.swapStepU | exact GlobalTheory.CompanionTheory.SwapRoot.swapStepU | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.swapStepU <;> assumption)
end

