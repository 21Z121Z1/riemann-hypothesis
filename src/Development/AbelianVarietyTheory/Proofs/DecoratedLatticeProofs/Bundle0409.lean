import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0366
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemPerOInfHalfAO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HalfAConj
open GlobalTheory.LatVac

theorem conjPl_eq_conjP {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.DIV.conjPl P = Formalism.L2.Col.conjPrime₂ P := by
  apply HeightOneSpectrum.ext
  apply Ideal.ext
  intro r
  show Formalism.L2.DIV.starOHom r ∈ P.asIdeal ↔ Formalism.L2.Col.cO E r ∈ P.asIdeal
  have : Formalism.L2.DIV.starOHom r = Formalism.L2.Col.cO E r := by
    first
      | rfl
      | (apply RingOfIntegers.ext; simp [Formalism.L2.DIV.starOHom, Formalism.L2.DIV.starO_coe, Formalism.L2.Col.cO])
  rw [this]

set_option maxHeartbeats 1000000 in
theorem mem_perO_inf_halfAO : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ c : ℕ, 0 < c → ∀ M ∈ GlobalTheory.LatVac.latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)), (∃ w ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), cA D e • GlobalTheory.LatVac.finTens 1 M = c • w) → Matrix.toLin' M ∈ (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c := by
  intro D S T hcc e SS hE N N' hN hN' c hc M hM hw
  obtain ⟨w, hw, hcw⟩ := hw
  have h1 : Matrix.toLin' M ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
    have := (GlobalTheory.AdForm.RatLat.mem_latRat_iff_perO N' hN M).1 hM
    rwa [GlobalTheory.AdForm.RatLat.AA_eq hcc] at this
  refine Submodule.mem_inf.2 ⟨h1, ?_⟩
  have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have h0 : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hE)
  have hconj : ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • Matrix.toLin' M)).map fun r => cA D e * incA D r : WO S T) = w := by
    ext i j
    have hij := congrFun (congrFun hcw i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    have e1 : cA D e * finTens 1 M i j = cA D e * incA D (M i j) := by
      refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
      · rw [RingHom.map_mul, RingHom.map_mul, h0, zero_mul, zero_mul]
      · rw [RingHom.map_mul, RingHom.map_mul]
        rfl
    have e2 : LinearMap.toMatrix' ((c : D.host.E)⁻¹ • Matrix.toLin' M) i j = (c : D.host.E)⁻¹ * M i j := by
      have e2' : (c : D.host.E)⁻¹ • Matrix.toLin' M = Matrix.toLin' ((c : D.host.E)⁻¹ • M) :=
        (map_smul Matrix.toLin' _ _).symm
      rw [e2', LinearMap.toMatrix'_toLin']
      rfl
    rw [Matrix.map_apply, e2, RingHom.map_mul, mul_left_comm, ← e1, hij, nsmul_eq_mul, ← mul_assoc]
    have e3 : incA D (c : D.host.E)⁻¹ * (c : AE D) = 1 := by
      rw [← map_natCast (incA D) c, ← RingHom.map_mul, inv_mul_cancel₀ hcE, map_one]
    rw [e3, one_mul]
  have hloc := (GlobalTheory.T.idempotentHalf_mem_completedHomLattice_iff_local D S T hcc (cA D e) _ (Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hE) N N' hN hN' _).1
    (hconj ▸ hw)
  rw [halfAO, Formalism.L2.Ker.mem_twO]
  intro Q
  by_cases hQ : Q ∈ SS
  · have ex : expS SS Q = 1 := by simp [expS, hQ]
    rw [ex]
    have e4 : (((c : D.host.E) ^ (-(1 : ℤ)))⁻¹) = (c : D.host.E) := by simp
    rw [e4]
    exact Formalism.L2.Ker.le_locP' _ _ (Formalism.L2.Ker.nat_smul_mem _ c h1)
  · by_cases hQ' : Formalism.L2.Col.conjPrime₂ Q ∈ SS
    · have ex : expS SS Q = -1 := by simp [expS, hQ, hQ']
      rw [ex]
      have e4 : (((c : D.host.E) ^ (-(-1 : ℤ)))⁻¹) = (c : D.host.E)⁻¹ := by simp
      rw [e4]
      refine hloc Q (Finset.mem_image.2 ⟨Formalism.L2.Col.conjPrime₂ Q, hQ', ?_⟩)
      rw [conjPl_eq_conjP, Formalism.L2.Ker.conjP_conjP']
    · have ex : expS SS Q = 0 := by simp [expS, hQ, hQ']
      rw [ex]
      simpa using Formalism.L2.Ker.le_locP' _ _ h1

end GlobalTheory.HalfAConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemScaledLatticeCompletionIffPolarisationInverse
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LatAt

variable {D : D7}

theorem pairA_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  refine Prod.ext ?_ ?_
  · show (0 : Ainf D.host.F) * 0 = 0
    rw [zero_mul]
  · rfl

theorem pair_tmul_mul (α β : Af D.host.F) (a b : D.host.E) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (a * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul]

def Good (v : Pl D) (α : Af D.host.F) : Prop :=
  α ∈ intAf D.host.F ∧ ∀ w, w ≠ v → evalV D.host.F w α = 0

theorem Good.mul {v : Pl D} {α β : Af D.host.F} (hα : Good v α) (hβ : Good v β) : Good v (α * β) :=
  ⟨fun w => by rw [map_mul]; exact mul_mem (hα.1 w) (hβ.1 w), fun w hw => by rw [map_mul, hα.2 w hw, zero_mul]⟩

theorem good_indP (v : Pl D) : Good v (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [GlobalTheory.SelfDualAt.evalV_indP, if_neg hw]

theorem indicatorAdele_mul_self (v : Pl D) :
    GlobalTheory.SelfDualAt.indP (D := D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v) = GlobalTheory.SelfDualAt.indP (D := D) (· = v) := by
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  have h1 : evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v)) =
      evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by
    rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs <;> simp
  exact h1

theorem gen_mem_idAt (v : Pl D) (α : Af D.host.F) (hα : ∀ w, w ≠ v → evalV D.host.F w α = 0) (x : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hα _ w.2, TensorProduct.zero_tmul]

theorem AA_ne_zero : D.host.AA ≠ 0 :=
  (GlobalTheory.SeeSaw.LiftModel.AA_ne (D := D) Formalism.IndefR.Fin.factPrincipalDatum).1

theorem int_of_mem {c d : D.host.E} (hc : c ∈ D.host.AA) (hd : d ∈ D.host.AA⁻¹) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = d * c := by
  have h : d * c ∈ D.host.AA⁻¹ * D.host.AA := FractionalIdeal.mul_mem_mul hd hc
  rw [inv_mul_cancel₀ AA_ne_zero] at h
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨o, ho⟩

theorem smul_latV_mem_latA (S : HSp D) (L : Lat S) (v : Pl D) {ε : Af D.host.F} (hε : Good v ε) {c : D.host.E}
    (hc : c ∈ D.host.AA) {z : Fin S.rank → AE D} (hz : z ∈ latV S L (· = v)) :
    ((pairA D.host.F 0 ε) ⊗ₜ[D.host.F] c : AE D) • z ∈ latA S L (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hz
  unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβ1, hβ2, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    apply AddSubgroup.subset_closure
    have g := hε.mul ⟨hβ1, hβ2⟩
    refine ⟨ε * β, g.1, g.2, c, hc, x, hx, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.SeeSaw.LatAt

namespace GlobalTheory.SeeSaw.LatAt

variable {D : D7}

theorem mem_latA_fwd (S : HSp D) (L : Lat S) (v : Pl D) (y : Fin S.rank → AE D) (hy : y ∈ latA S L (· = v)) :
    (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := by
  unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα1, hα2, c, hc, x, hx, rfl⟩ := hy
    refine ⟨fun i => gen_mem_idAt v α hα2 _, fun s hs => ?_⟩
    unfold idV at hs
    induction hs using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨β, hβ1, hβ2, d, hd, rfl⟩ := hs
      obtain ⟨o, ho⟩ := int_of_mem hc hd
      unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
      apply AddSubgroup.subset_closure
      have g := Good.mul (v := v) ⟨hβ1, hβ2⟩ ⟨hα1, hα2⟩
      refine ⟨β * α, g.1, g.2, 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      rw [Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul, Pi.smul_apply, Algebra.smul_def, ← mul_assoc]
      congr 2
      exact ho.symm
    | zero => rw [zero_smul]; exact zero_mem _
    | add s t _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
    | neg s _ h => rw [neg_smul]; exact neg_mem h
  | zero => exact ⟨fun i => zero_mem _, fun s _ => by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ h1 h2 =>
    exact ⟨fun i => add_mem (h1.1 i) (h2.1 i), fun s hs => by rw [smul_add]; exact add_mem (h1.2 s hs) (h2.2 s hs)⟩
  | neg y _ h => exact ⟨fun i => neg_mem (h.1 i), fun s hs => by rw [smul_neg]; exact neg_mem (h.2 s hs)⟩

theorem mem_latA_bwd (S : HSp D) (L : Lat S) (v : Pl D) (y : Fin S.rank → AE D) (hsupp : ∀ i, y i ∈ idAt D (· = v))
    (h : ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v)) : y ∈ latA S L (· = v) := by
  have hε : Good v (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := good_indP v
  have key : ∀ t ∈ D.host.AA * D.host.AA⁻¹,
      ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] t : AE D) • y ∈ latA S L (· = v) := by
    intro t ht
    refine FractionalIdeal.mul_induction_on ht ?_ ?_
    · intro c hc d hd
      have e : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] (c * d) : AE D) =
          ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] c) *
            ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] d) := by
        rw [pair_tmul_mul, indicatorAdele_mul_self]
      rw [e, mul_smul]
      refine smul_latV_mem_latA S L v hε hc (h _ ?_)
      unfold idV
      exact AddSubgroup.subset_closure ⟨_, hε.1, hε.2, d, hd, rfl⟩
    · intro a b ha hb
      rw [TensorProduct.tmul_add, add_smul]
      exact add_mem ha hb
  have h1 := key 1 (by rw [mul_inv_cancel₀ AA_ne_zero]; exact FractionalIdeal.one_mem_one _)
  have e1 : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • y = y := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) (y i) (hsupp i)
  rwa [e1] at h1

end GlobalTheory.SeeSaw.LatAt

theorem GlobalTheory.SeeSaw.mem_latA_iff_mul_inv : ∀ (D : D7) (v : Pl D) (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) :=
  fun _ v S L y => ⟨GlobalTheory.SeeSaw.LatAt.mem_latA_fwd S L v y, fun h => GlobalTheory.SeeSaw.LatAt.mem_latA_bwd S L v y h.1 h.2⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedVac

theorem halfBack : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (e : AE D) (u : WO S T),
    IsHalf e (actO S T g h u) → IsHalf e u := by
  intro D S T g h e u hu
  have hA : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom T h))
  have hB : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom S g))
  have cancel : ∀ X : Matrix (Fin T.rank) (Fin S.rank) (AE D),
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) X)
        (Formalism.L2.Theta.mt S g⁻¹))) (Formalism.L2.Theta.mt S g) = X := by
    intro X
    simp only [Matrix.mul_assoc, hB, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have key : e • actO S T g h u = actO S T g h u := by
    ext i j; exact hu i j
  have key2 : e • u = u := by
    have h1 := congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) M) (Formalism.L2.Theta.mt S g)) key
    simp only [actO] at h1
    rw [cancel u] at h1
    simp only [Matrix.mul_smul, Matrix.smul_mul] at h1
    rw [cancel u] at h1
    exact h1
  intro i j
  have := congrFun (congrFun key2 i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this

theorem norm_weilRepresentation_thetaFunction_preserved : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : (AE D)ˣ →* Circle) (om : Om S T),
    IsWeilDatumO ψ S T μ μ om → ∀ f, IsThetaFunO ψ S T f → ∀ p (m : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsCovolOne (ratL T S) m 𝓕 → nrm2 m 𝓕 (om p f) = nrm2 m 𝓕 f := by
  intro D ψ S T μ om hW f hf p m 𝓕 hm
  have hU := hW.om_unit m 𝓕 hm.1 hm.2.1 p f hf
  have hf' := hW.om_pres p f hf
  haveI : OpensMeasurableSpace (WO S T) := ⟨le_rfl⟩
  have key : ∀ F : WO S T → ℂ, Continuous F → nrm2 m 𝓕 F = (∫⁻ w in 𝓕, ‖F w‖ₑ ^ 2 ∂m).toReal := by
    intro F hF
    unfold nrm2
    have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
      (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun w => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [key _ hf'.cont, key _ hf.cont, hU]

theorem latMove : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' →
    ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True),
      ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := GlobalTheory.T.unitaryPair_maps_completedHomLattice_onto_translate

theorem latSign : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a)
    (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f →
    ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
    toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ v, GlobalTheory.AdTh.IsFinOf S T γ v →
    ∀ w, alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT γ)) * heisO ψ S T v f w = f w := GlobalTheory.T.heisenberg_fixes_latticeVacuum_periodLattice

theorem lamPre : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N',
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧
      embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := GlobalTheory.T.exists_rationalMatrix_of_mem_periodLattice

theorem fixedLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a)
    (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f →
    xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc)
      (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' f hf hl x hx z
  obtain ⟨γ, hγ, rfl, v, hv⟩ := lamPre D S T a b hS hT δ N N' x hx
  have hs := latSign D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' f hf hl γ hγ v hv
  have hu := GlobalTheory.T.gaussianReading_finiteRationalHeisenbergTranslate D ψ θ S T a b hS hT δ sc hP f hf γ v hv
  rw [← hu]
  simp only [xiN]
  rw [← hs]
  ring

theorem vac_moved : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ N N', Moves S hS g N → Moves T hT h N' → IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) ∧ xiN θ S T hS hT δ sc (om (g, h) f) ∈ Formalism.L2.Th1.H.Th (HV sc) (alV D.host.d sc) (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ∧ xiN θ S T hS hT δ sc (om (g, h) f) ≠ 0 := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hW f hf g hg h hh N N' hN hN'
  obtain ⟨hstd, hv⟩ := hf
  have hhol : IsHol θ S T ψ f := ⟨hv.theta, hv.fock⟩
  have hI := GlobalTheory.T.om_pureTensorO_comm D ψ θ S T a b hS hT δ sc hP μ om hW g hg h hh f hhol
  have hth' : IsThetaFunO ψ S T (om (g, h) f) := hW.om_pres _ f hv.theta
  have hvac : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) := by
    refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ?_, fock := hI.1.2, norm := ?_ }⟩
    · refine ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩
      · obtain ⟨u, hu, rfl⟩ := latMove D S T a b hS hT hP.gS hP.gT g hg h hh N N' hN hN' u' hu'
        have h2 : actO S T g h u + actO S T g h u = actO S T g h (u + u) := by
          simp only [actO, Matrix.mul_add, Matrix.add_mul]
        have h3 := hv.lat.1 u hu
        rw [two_nsmul] at h3 ⊢
        rw [h2, ← hW.om_heis g h _ f hv.theta, h3]
      · obtain ⟨u, hu, rfl⟩ := latMove D S T a b hS hT hP.gS hP.gT g hg h hh N N' hN hN' u' hu'
        rw [← hW.om_heis g h u f hv.theta, hv.lat.2 e he u hu (halfBack D S T g h e u hhalf)]
    · refine ⟨hv.norm.1, fun p hp => ?_⟩
      show nrm2 p.1 p.2 (om (g, h) f) = 1
      rw [norm_weilRepresentation_thetaFunction_preserved D ψ S T μ om hW f hv.theta (g, h) p.1 p.2 hp]
      exact hv.norm.2 p hp
  have hne : om (g, h) f ≠ 0 := by
    intro h0
    obtain ⟨p, hp⟩ := hvac.2.norm.1
    have h1 := hvac.2.norm.2 p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hII := GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective D ψ θ S T a b hS hT δ sc hP
  refine ⟨hvac, ⟨GlobalTheory.SCV.analyticOnNhd_of_differentiable (hII.1 _ hI.1) _,
    fixedLine D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' _ hth' hvac.2.lat⟩, fun h0 => hne (hII.2 _ hth' h0)⟩

end GlobalTheory.MovedVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NoTransvectionInvariantPairOnScaledKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

noncomputable section
namespace GlobalTheory.LatPair

theorem no_pair_on_scaled_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → False := by
  intro k _ _ _ _ n _ _ i P c hn hc hlat hcl
  have hmem : ∀ b, b ≠ i → Pi.single b c ∈ P.lat := by
    intro b hb
    rw [hlat]
    refine ⟨fun j => ?_, ⟨0, zero_mem _, ?_⟩⟩
    · by_cases h : j = b
      · subst h; simp [hc]
      · rw [Pi.single_eq_of_ne h]; simp
    · rw [Pi.single_eq_of_ne (Ne.symm hb)]; simp
  have hzero : ∀ a, a ≠ i → P.HasVal (Pi.single a c) 0 := by
    intro a ha
    obtain ⟨d, hda, hdi⟩ : ∃ d, d ≠ a ∧ d ≠ i := by
      by_contra h
      push_neg at h
      have hsub : (Finset.univ : Finset n) ⊆ {a, i} := fun d _ => by
        by_cases hd : d = a
        · simp [hd]
        · simp [h d hd]
      have h1 := Finset.card_le_card hsub
      have h2 : ({a, i} : Finset n).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ] at h1
      omega
    obtain ⟨v, hv⟩ := (Pair.mem_lat_iff (P := P)).1 (hmem d hdi)
    obtain ⟨w, hw⟩ := (Pair.mem_lat_iff (P := P)).1 (hmem a ha)
    have h1 := hcl _ _ hv a d 1 (Ne.symm hda) (Or.inl ha)
    have hx : (Pi.single d c + Pi.single a (((1 : 𝒪[k]) : k) * (Pi.single d c : n → k) d) : n → k) = Pi.single d c + Pi.single a c := by
      simp
    rw [hx] at h1
    have h3 := h1.unique (hv.add hw)
    have hw0 : w = 0 := by linear_combination -h3
    exact hw0 ▸ hw
  obtain ⟨a, ha⟩ : ∃ a, a ≠ i := by
    by_contra h
    push_neg at h
    have : Fintype.card n ≤ 1 := Fintype.card_le_one_iff.2 (fun x y => (h x).trans (h y).symm)
    omega
  have hzi : ∀ t : 𝒪[k], t ∈ IsLocalRing.maximalIdeal 𝒪[k] → P.HasVal (Pi.single i ((t : k) * c)) 0 := by
    intro t ht
    have h1 := hcl _ _ (hzero a ha) i a t (Ne.symm ha) (Or.inr ht)
    rw [Pi.single_eq_same] at h1
    simpa using h1.sub (hzero a ha)
  apply P.fn_ne
  ext ⟨x, hx⟩
  obtain ⟨hxj, s, hs, hsx⟩ := (hlat x).1 hx
  have hsing : ∀ b, P.HasVal (Pi.single b (x b)) 0 := by
    intro b
    by_cases hb : b = i
    · subst hb
      have he : (s : k) * c = x b := by rw [hsx]; field_simp
      simpa [he] using hzi s hs
    · have h := (hzero b hb).smul ⟨c⁻¹ * x b, hxj b⟩
      have he : (⟨c⁻¹ * x b, hxj b⟩ : 𝒪[k]) • (Pi.single b c : n → k) = Pi.single b (x b) := by
        rw [← Pi.single_smul']; congr 1; change (c⁻¹ * x b) * c = x b; field_simp
      simpa [he] using h
  have hsum : P.HasVal (∑ b, Pi.single b (x b)) 0 :=
    Finset.sum_induction _ (fun y => P.HasVal y 0) (fun _ _ h h' => by simpa using h.add h')
      ⟨P.lat.zero_mem, map_zero P.fn⟩ (fun b _ => hsing b)
  rw [Finset.univ_sum_single] at hsum
  rw [LinearMap.zero_apply]
  exact hsum.2

end GlobalTheory.LatPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodIdealZpow_completion_adeleConj_iff : ∀ (D : D7) (v : Pl D) (n : ℤ) (s : AE D), s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v := by
  first | exact @GlobalTheory.SeeSaw.idV_AA_zpow_conj | exact GlobalTheory.SeeSaw.idV_AA_zpow_conj | (intros; apply GlobalTheory.SeeSaw.idV_AA_zpow_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepVectorTwoLevelLawStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStep_vector_twoLevel_law : ∀ D : D7, ForStep D fun _ _ s s' p => VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L) (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  first | exact @GlobalTheory.ChainOnto.StepVecLawBoth.vecLaw | exact GlobalTheory.ChainOnto.StepVecLawBoth.vecLaw | (intros; apply GlobalTheory.ChainOnto.StepVecLawBoth.vecLaw <;> assumption)
end

