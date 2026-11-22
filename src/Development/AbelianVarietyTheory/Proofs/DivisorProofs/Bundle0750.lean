import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonZeroDivisor
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonzeroNonunitDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenforms
section
open NumberField

namespace GlobalTheory.CuspRep

theorem Zalg_acts_by_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (c : (E →+* ℂ) → ℂ → ℂ) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a →
    ∃ s : ℂ, ∀ φ : GlobalTheory.CuspRep.Sm E a, (∀ τ u, GlobalTheory.CuspRep.cap τ u φ = c τ u • φ) → z φ = s • φ := by
  intro E _ _ _ a c z hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨c τ u, fun φ hφ => hφ τ u⟩
  | algebraMap r => exact ⟨r, fun φ _ => by simp [Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, fun φ hφ => by rw [LinearMap.add_apply, hs φ hφ, ht φ hφ, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s * t, fun φ hφ => by rw [Module.End.mul_apply, ht φ hφ, map_smul, hs φ hφ, smul_smul, mul_comm]⟩

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartEvNmulPowSelf
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem chart_ev_nmul_pow_self : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (i : Fin d), c.ev n (nmul c.μ (p ^ n) i) = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n i
  rw [GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c n (p ^ n) i, G.mulBy_pow_self n (c.x n i), c.aug n i, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
section
open NumberField GlobalTheory.CuspRep Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CuspRep.JointCont

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

theorem map_unip {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : BlockIx a r → R) :
    Matrix.GeneralLinearGroup.map f (unip x) = unip (fun p => f (x p)) := by
  apply Units.ext
  ext i j
  change f ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) = (1 + nilM fun p => f (x p) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

theorem continuous_nilM {R : Type} [CommRing R] [TopologicalSpace R] :
    Continuous (fun x : BlockIx a r → R => (nilM x : Matrix (Fin a) (Fin a) R)) := by
  refine continuous_matrix fun i j => ?_
  simp only [nilM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_unip {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun x : BlockIx a r → R => unip x) :=
  Units.continuous_iff.2 ⟨continuous_const.add continuous_nilM, continuous_const.sub continuous_nilM⟩

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem chart_mul_finGL_of_fix (φ : Sm E a) (h : GA E a) (k : GL (Fin a) (Af E)) (hk : finRep E a k φ = φ) :
    chart φ.1 (h * finGL E a k) = chart φ.1 h := by
  rw [← chart_rt_fin]
  congr 1
  funext z
  exact congrArg (fun ψ : Sm E a => ψ.1 z) hk

def infPart (g : GA E a) (x : BlockIx a r → Ad E) : GL (Fin a) (Cinf E) :=
  unip (fun p => pInf E (x p)) * Matrix.GeneralLinearGroup.map (pInf E) g

def finPart (g : GA E a) (x : BlockIx a r → Ad E) : GL (Fin a) (Af E) :=
  unip (fun p => pFin E (x p)) * Matrix.GeneralLinearGroup.map (pFin E) g

theorem unip_mul_eq (g : GA E a) (x : BlockIx a r → Ad E) :
    unip x * g = finGL E a (finPart g x) * infGL E a (infPart g x) := by
  refine ga_ext ?_ ?_ <;>
    simp only [finPart, infPart, map_mul, map_unip, pInf_finGL, pInf_infGL, pFin_finGL, pFin_infGL, one_mul, mul_one]

theorem continuous_infPart (g : GA E a) : Continuous (fun x : BlockIx a r → Ad E => toL (infPart g x).val) := by
  have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pInf E (x p)) :=
    continuous_pi fun p => continuous_pInf.comp (continuous_apply p)
  have h2 : Continuous (fun x : BlockIx a r → Ad E =>
      ((infPart g x : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) :=
    Units.continuous_val.comp ((continuous_unip.comp h1).mul continuous_const)
  exact h2

theorem continuous_finPart (g : GA E a) : Continuous (fun x : BlockIx a r → Ad E => finPart g x) := by
  have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pFin E (x p)) :=
    continuous_pi fun p => continuous_pFin.comp (continuous_apply p)
  exact (continuous_unip.comp h1).mul continuous_const

theorem eventually_chart_eq (φ : Sm E a) (hφ : IsAutForm φ) (g : GA E a) (x₀ : BlockIx a r → Ad E) :
    ∀ᶠ x in 𝓝 x₀, chart φ.1 (unip x * g) =
      chart φ.1 (finGL E a (finPart g x₀)) ∘ lmul (toL (infPart g x).val) := by
  have hc : Continuous (fun x : BlockIx a r → Ad E => (finPart g x₀)⁻¹ * finPart g x) := continuous_const.mul (continuous_finPart g)
  have h1 : finRep E a ((finPart g x₀)⁻¹ * finPart g x₀) φ = φ := by rw [inv_mul_cancel]; simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hφ.level.mem_nhds h1)] with x hx
  have hx' : finRep E a ((finPart g x₀)⁻¹ * finPart g x) φ = φ := hx
  rw [unip_mul_eq, ← mul_inv_cancel_left (finPart g x₀) (finPart g x), map_mul, mul_assoc, ← infGL_comm,
    ← mul_assoc, chart_mul_finGL_of_fix φ _ _ hx', chart_mul]

theorem chart_unipotent_translate_continuousOn (φ : Sm E a) (hφ : IsAutForm φ) (g : GA E a) (X : Lie E a) :
    ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E a => chart φ.1 (unip p.1 * g) p.2)
        (Set.univ ×ˢ invSet E a) ∧
      ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E a => fderiv ℝ (chart φ.1 (unip p.1 * g)) p.2 X)
        (Set.univ ×ˢ invSet E a) := by
  have hP : Continuous (fun p : (BlockIx a r → Ad E) × Lie E a => lmul (toL (infPart g p.1).val) p.2) := by
    have := ((continuous_infPart g).comp continuous_fst).matrix_mul
      (continuous_snd : Continuous fun p : (BlockIx a r → Ad E) × Matrix (Fin a) (Fin a) (Cinf E) => p.2)
    exact this
  have hQ : Continuous (fun p : (BlockIx a r → Ad E) × Lie E a => lmul (toL (infPart g p.1).val) X) := by
    have := ((continuous_infPart g).comp continuous_fst).matrix_mul
      (continuous_const : Continuous fun _ : (BlockIx a r → Ad E) × Lie E a => (Matrix.of X))
    exact this
  have hinv : ∀ p : (BlockIx a r → Ad E) × Lie E a, p.2 ∈ invSet E a →
      lmul (toL (infPart g p.1).val) p.2 ∈ invSet E a := fun p hp => (infPart g p.1).isUnit.mul hp
  constructor
  · rintro ⟨x₀, y₀⟩ ⟨-, hy₀⟩
    set f₀ := chart φ.1 (finGL E a (finPart g x₀))
    have hf₀ : ContDiffOn ℝ ∞ f₀ (invSet E a) := φ.2 _
    have hA : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E a => f₀ (lmul (toL (infPart g p.1).val) p.2))
        (x₀, y₀) :=
      ContinuousAt.comp (g := f₀) (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (hinv (x₀, y₀) hy₀)))
        hP.continuousAt
    refine (hA.congr ?_).continuousWithinAt
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually (eventually_chart_eq φ hφ g x₀)] with p hp
    rw [hp]; rfl
  · rintro ⟨x₀, y₀⟩ ⟨-, hy₀⟩
    set f₀ := chart φ.1 (finGL E a (finPart g x₀))
    have hf₀ : ContDiffOn ℝ ∞ f₀ (invSet E a) := φ.2 _
    have hD : ContinuousOn (fun z => fderiv ℝ f₀ z) (invSet E a) :=
      hf₀.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)
    have hA : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E a =>
        fderiv ℝ f₀ (lmul (toL (infPart g p.1).val) p.2) (lmul (toL (infPart g p.1).val) X)) (x₀, y₀) :=
      ContinuousAt.clm_apply
        (ContinuousAt.comp (g := fun z => fderiv ℝ f₀ z)
          (hD.continuousAt (isOpen_invSet.mem_nhds (hinv (x₀, y₀) hy₀))) hP.continuousAt)
        hQ.continuousAt
    refine (hA.congr ?_).continuousWithinAt
    have hy : ∀ᶠ p : (BlockIx a r → Ad E) × Lie E a in 𝓝 (x₀, y₀), p.2 ∈ invSet E a :=
      (continuous_snd.tendsto (x₀, y₀)).eventually (isOpen_invSet.mem_nhds hy₀)
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually (eventually_chart_eq φ hφ g x₀), hy]
      with p hp hp2
    have hd : DifferentiableAt ℝ f₀ (lmul (toL (infPart g p.1).val) p.2) :=
      (hf₀.contDiffAt (isOpen_invSet.mem_nhds (hinv p hp2))).differentiableAt (by simp)
    change _ = fderiv ℝ (chart φ.1 (unip p.1 * g)) p.2 X
    rw [hp, fderiv_comp _ hd (lmul _).differentiableAt, ContinuousLinearMap.fderiv]
    rfl

theorem chart_jointCont : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ → ∀ (g : GlobalTheory.CuspRep.GA E a) (X : GlobalTheory.CuspRep.Lie E a), ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g) p.2) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) ∧ ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => fderiv ℝ (GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g)) p.2 X) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) :=
  fun _ _ _ _ _ _ φ hφ g X => chart_unipotent_translate_continuousOn φ hφ g X

end GlobalTheory.CuspRep.JointCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonZeroDivisorStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_vanishes_away_nonZeroDivisor : ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ (n i : ℤ) (z : Ht q (sp R) n i), pull _ (spMap (algebraMap R (FractionRing R))) _ _ z = 0 → ∃ g ∈ nonZeroDivisors R, pull _ (spMap (algebraMap R (Localization.Away g))) _ _ z = 0 := by
  first | (exact @GlobalTheory.EtC.classVanishesAwayNZD) | (exact GlobalTheory.EtC.classVanishesAwayNZD) | (intros; apply GlobalTheory.EtC.classVanishesAwayNZD  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassVanishesAwayNonzeroNonunitDomainStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain : ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B], ¬ IsField B → IsUnit (q : B) → ∀ (n i : ℤ) (x : Ht q (sp B) n i), pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 → ∃ f : B, f ≠ 0 ∧ ¬ IsUnit f ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.classVanishesAway) | (exact GlobalTheory.EtC.classVanishesAway) | (intros; apply GlobalTheory.EtC.classVanishesAway  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTensor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CloseTen

theorem baseChange_tensor_holomorphic_closeness {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C)
    (ρ : Hol W →+* R ⊗[ℂ] Hol W₀)
    (hρ : ∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h))
    (ψ₂ : R ⊗[ℂ] Hol W₀ →+* C) (ρ₁ : Hol W₀ →+* C)
    (hc : Close J ρ₁ (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom)) :
    ∀ φ : R ⊗[ℂ] Hol W₀ →+* C,
      (∀ h : Hol W₀, φ ((1 : R) ⊗ₜ[ℂ] h) = ρ₁ h) →
      (∀ d : R, φ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (φ.comp ρ) (ψ₂.comp ρ) := by
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro φ hφ hφd
    have e : φ = ψ₂ := by
      apply RingHom.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul d h =>
        have e1 : d ⊗ₜ[ℂ] h = (d ⊗ₜ[ℂ] (1 : Hol W₀)) * ((1 : R) ⊗ₜ[ℂ] h) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
        rw [e1, map_mul, map_mul, hφd, hφ]
        rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    subst e
    exact Relation.ReflTransGen.refl
  | head hs _ ih =>
    intro φ hφ hφd
    obtain ⟨n, hnJ, hn2, hn⟩ := hs
    obtain ⟨φ', hφ'⟩ := GlobalTheory.T.exists_squareZero_move_tensor_holomorphic φ n hn2
    refine Relation.ReflTransGen.head ⟨n, hnJ, hn2, fun h => ?_⟩ (ih φ' (fun h => ?_) (fun d => ?_))
    · rw [RingHom.comp_apply, hφ']
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [RingHom.comp_apply, hρ]
    · rw [hφ', hn h, hφ]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, hφ]
    · rw [hφ', ← hφd]
      conv_rhs => rw [← add_zero (φ (d ⊗ₜ[ℂ] 1))]
      congr 1
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
        TensorProduct.tmul_zero, map_zero, zero_mul]

theorem close_tensor : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C) (ρ : Hol W →+* R ⊗[ℂ] Hol W₀), (∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h)) → ∀ ψ₁ ψ₂ : R ⊗[ℂ] Hol W₀ →+* C, (∀ d : R, ψ₁ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (ψ₁.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) → Close J (ψ₁.comp ρ) (ψ₂.comp ρ) := by
  intro I _ g W W₀ R _ _ C _ J ρ hρ ψ₁ ψ₂ hd hc
  exact baseChange_tensor_holomorphic_closeness J ρ hρ ψ₂ _ hc ψ₁ (fun h => rfl) hd

end GlobalTheory.CloseTen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1FormalLogMapMemKerStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob1_formalLog_mem_ker_of_map_grouplike : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ' i) = 0) → ∀ g : MvPowerSeries (Fin d) B, constantCoeff g = 1 → subst (fun i => map θ (μ' i)) (map θ g) = inL (map θ g) * inR (map θ g) → In (RingHom.ker θ) (cob1 (up Q μ') (formalLog (map (algebraMap B Q) g))) := by
  first | exact @GlobalTheory.CobLog.cob1_formalLog_mem_ker | exact GlobalTheory.CobLog.cob1_formalLog_mem_ker | (intros; apply GlobalTheory.CobLog.cob1_formalLog_mem_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryFrobeniusCommuteModPQuasiLogStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_frobenius_commute_mod_p_quasiLog : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ b : ι → F.B, In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb b e)) - frob p F.s (cob1 (up F.Q μ') (comb b e))) := by
  first | exact @GlobalTheory.FrobCongr.frob_cong | exact GlobalTheory.FrobCongr.frob_cong | (intros; apply GlobalTheory.FrobCongr.frob_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffQuasiLogarithmIntegralLowDegreeStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_quasiLogarithm_integral_low_degree : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ l : MvPowerSeries (Fin d) Q, QL μ ⊤ l → ∀ α : Fin d →₀ ℕ, α.degree ≤ p → (∀ i, α ≠ Finsupp.single i p) → ∃ b : B, coeff α l = algebraMap B Q b := by
  first | exact @GlobalTheory.QLogInt.coeff_integral_of_QL | exact GlobalTheory.QLogInt.coeff_integral_of_QL | (intros; apply GlobalTheory.QLogInt.coeff_integral_of_QL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStripsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedHeckeL_bounded_in_vertical_strips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  first | exact @GlobalTheory.HeckeStrip.completedLBoundedInStrips | exact GlobalTheory.HeckeStrip.completedLBoundedInStrips | (intros; apply GlobalTheory.HeckeStrip.completedLBoundedInStrips <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMonomialStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_iterate_invariant_derivation_monomial : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → (∀ i, swap (μ i) = μ i) → ∀ (u : Fin d → R) (α : Fin d →₀ ℕ), constantCoeff ((invDer μ u)^[α.degree] (monomial α (1 : R))) = (α.degree.factorial : R) * ∏ i, u i ^ α i := by
  first | exact @GlobalTheory.LawDer.MonoIter.constantCoeff_iterate_invDer_monomial | exact GlobalTheory.LawDer.MonoIter.constantCoeff_iterate_invDer_monomial | (intros; apply GlobalTheory.LawDer.MonoIter.constantCoeff_iterate_invDer_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityBaseChangeAffineCofilteredLimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuity_baseChange_affine_cofiltered_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S), IsAffine W → ContCone R F ((bc (sch.map r)).mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_bc_affine
  | exact GlobalTheory.EtC.contCone_bc_affine
  | (intros; apply GlobalTheory.EtC.contCone_bc_affine <;> assumption)
end

