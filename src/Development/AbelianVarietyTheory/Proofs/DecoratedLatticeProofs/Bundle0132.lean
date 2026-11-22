import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualLatticeCosetIndicatorIsSchwartzBruhat
section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetSB

theorem cosetInd_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (f : Module.Dual 𝓀[k] (Red L)), cosetInd q L f ∈ SB (n → k) := by
  intro k _ _ _ _ n _ _ q L _ f
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  by_cases hex : ∃ F : n → k, Lifts L F f
  · obtain ⟨F, hF⟩ := hex
    have e : cosetInd q L f = fun η => dualInd L (η - q.inv • F) := by
      funext η
      rw [← GlobalTheory.FinPl.CosetPairing.cosetInd_add q hF (η - q.inv • F), sub_add_cancel]
    rw [e]
    exact GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.Comm.dualInd_mem L) (s := fun η => η + q.inv • F)
      (by fun_prop) (by fun_prop) fun η => sub_add_cancel η _
  · have e : cosetInd q L f = 0 := by
      classical
      funext η
      unfold cosetInd
      rw [if_neg fun ⟨F, hF, _⟩ => hex ⟨F, hF⟩]
      rfl
    rw [e]
    exact (SB (n → k)).zero_mem

end GlobalTheory.FinPl.CosetSB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteComponentUnitaryActingOnFiniteSupporStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteComponent_unitary_acting_on_finiteSupported : ∀ (D : D7) (S : HSp D) (g : GA D S), ∃ x ∈ GfC S, ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → mt S g *ᵥ y = mt S x *ᵥ y := by
  first | exact @GlobalTheory.GlobFin.fin_rep | exact GlobalTheory.GlobFin.fin_rep | (intros; apply GlobalTheory.GlobFin.fin_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaFlag

variable {D : D7} {v : Pl D}

def intGrpAt (D : D7) (v : Pl D) : AddSubgroup (AE D) where
  carrier := intAt D (· = v)
  zero_mem' := ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add]; exact add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem mul_mem_intAt {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) : a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem exists_nat_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

theorem exists_nat_isIntegral_fin {ι : Type} [Fintype ι] (z : ι → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ l, IsIntegral ℤ ((d : D.host.E) * z l) := by
  classical
  choose c hc hi using fun p : ι => exists_nat_isIntegral (z p)
  refine ⟨∏ p, c p, Finset.prod_pos fun p _ => hc p, fun l => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ c (Finset.mem_univ l), Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi l)
  rw [← Int.cast_natCast]
  exact isIntegral_algebraMap (R := ℤ)

theorem mul_incA_mem {ε : AE D} (hεI : ε ∈ intAt D (· = v)) {o : D.host.E} (ho : IsIntegral ℤ o) :
    ε * incA D o ∈ intAt D (· = v) := by
  have h : finPart D (incA D o) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, ⟨o, ho⟩, rfl⟩
  exact ⟨Ideal.mul_mem_right _ _ hεI.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE hεI.2 h⟩

theorem princ_intGrpAt {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v))
    (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (ht : Tame D v) : Princ ε (intGrpAt D v) := by
  rintro J h1 h2 ⟨m, hm, h3⟩ ⟨N, hN, h4⟩
  obtain ⟨β, β', g1, g2, g3, g4, g5⟩ := GlobalTheory.IwaPlace.FreeAt.exists_basis D 1 v ε (J.comap (Pi.evalAddMonoidHom (fun _ : Fin 1 => AE D) 0))
    ht hεε hεc hεI hε
    (fun y hy i => by rw [Subsingleton.elim i 0]; exact (hε _).2 (h1 _ hy))
    (fun a ha y hy => h2 a ha _ hy)
    ⟨m, hm, fun y hy => by
      have := h2 _ (hy 0) _ h3
      rw [mul_left_comm, mul_comm (y 0), (hε _).1 (hy 0).1] at this
      exact this⟩
    ⟨N, hN, fun y hy i => by rw [Subsingleton.elim i 0]; exact h4 _ hy⟩
  have e3 : β 0 0 * β' 0 0 = ε := by
    have := congrFun (congrFun g3 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
  have ev : ∀ (a : AE D) (i : Fin 1), (β' *ᵥ fun _ => a) i = β' 0 0 * a := fun a i => by
    rw [Subsingleton.elim i 0, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  refine ⟨β 0 0, (g5 (fun _ => β 0 0) fun _ => g1 0 0).2 fun i => ?_, β' 0 0, (hε _).1 (g2 0 0), e3, fun a ha => ?_⟩
  · rw [ev, mul_comm, e3]; exact hεI
  · have := (g5 (fun _ => a) fun _ => (hε _).2 (h1 a ha)).1 ha 0
    rw [ev] at this
    exact this

theorem exists_flag_basis : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∀ M : AddSubgroup (Fin S.rank → AE D), IsSDAt S v M → ∃ b : Mx D ρ ρ, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, b i j ∈ idAt D (· = v)) ∧ (∀ i, (fun k => (d.jX ⬝ b) k i) ∈ M) ∧ ∃ c' : Mx D S.rank ρ, (∀ i, (fun k => c' k i) ∈ M) ∧ adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε ht M ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨K, hK, hint⟩ := exists_nat_isIntegral_fin
    (Sum.elim (fun p : Fin S.rank × Fin ρ => d.e p.1 p.2) (fun p : Fin S.rank × Fin ρ => d.e' p.1 p.2))
  have hcol : ∀ z : Fin S.rank → D.host.E, (∀ l, IsIntegral ℤ ((K : D.host.E) * z l)) →
      (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) ∈ M := fun z hz => by
    have e : (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) =
        (m : AE D) • fun l => ε * incA D ((K : D.host.E) * z l) := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, map_natCast, Nat.cast_mul]
      ring
    rw [e]
    exact hmul _ fun l => mul_incA_mem hεI (hz l)
  obtain ⟨b, h1, h2, h3, c', h4, h5⟩ := exists_flag_dual_matrix (c := cA D) (O := intGrpAt D v) (M := M) (gA S)
    cA_cA hεε hεc hεI (fun a ha => (hε a).1 ha.1) (fun a ha b hb => mul_mem_intAt ha hb)
    (fun a ha => ⟨(hε _).2 (by rw [← hεc, ← RingHom.map_mul, (hε a).1 ha.1]), (FrameLat.cA_int_iff a).2 ha.2⟩)
    (princ_intGrpAt hεε hεc hεI hε ht) (fun y hy i => (hε _).1 (hsupp y hy i))
    (fun y hy => hdual y fun i => (hε _).2 (hy i)) d.jX d.jY d.gram_YX (m * K) (Nat.mul_pos hm hK)
    (fun k => hcol (fun l => d.e l k) fun l => hint (Sum.inl (l, k)))
    (fun k => hcol (fun l => d.e' l k) fun l => hint (Sum.inr (l, k)))
  exact ⟨b, h1, fun i j => (hε _).2 (h2 i j), h3, c', h4, h5⟩

end GlobalTheory.IwaFlag

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergAverageCompactSymplecticTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeisAvgCompact

theorem exists_average_of_compact {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (K : AddSubgroup X) (hK : IsCompact (K : Set X)) (f : X → X → ℂ)
    (hf : Continuous fun p : X × X => f p.1 p.2) :
    ∃ g : X → ℂ, Continuous g ∧
      (∀ (c : ℂ) (x y : X), (∀ u ∈ K, f x u = c * f y u) → g x = c * g y) ∧
      (∀ (c : ℂ) (x y : X), ∀ u₀ ∈ K, (∀ u ∈ K, c * f x u = f y (u₀ + u)) → c * g x = g y) ∧
      ∀ (δ : ℝ) (z : ℂ) (w : X), (∀ a ∈ K, ‖f w a - z‖ ≤ δ) → ‖g w - z‖ ≤ δ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  letI mK : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let ν : Measure K := Measure.addHaarMeasure ⊤
  haveI : IsProbabilityMeasure ν := ⟨by
    have h := Measure.addHaarMeasure_self (G := K) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h⟩
  have hF : Continuous (Function.uncurry fun (w : X) (u : K) => f w u) :=
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hfw : ∀ w, Continuous fun u : K => f w u := fun w => hF.comp (Continuous.prodMk_right w)
  have hint : ∀ w, Integrable (fun u : K => f w u) ν := fun w =>
    integrableOn_univ.1 ((hfw w).continuousOn.integrableOn_compact isCompact_univ)
  refine ⟨fun w => ∫ u : K, f w u ∂ν, ?_, ?_, ?_, ?_⟩
  · have h := continuous_parametric_integral_of_continuous (μ := ν) hF isCompact_univ
    simpa only [Measure.restrict_univ] using h
  · intro c x y h
    show (∫ u : K, f x u ∂ν) = c * ∫ u : K, f y u ∂ν
    rw [← integral_const_mul]
    congr 1
    funext u
    exact h u u.2
  · intro c x y u₀ hu₀ h
    show c * (∫ u : K, f x u ∂ν) = ∫ u : K, f y u ∂ν
    rw [← integral_const_mul, ← integral_add_left_eq_self (fun u : K => f y u) (⟨u₀, hu₀⟩ : K)]
    congr 1
    funext u
    exact h u u.2
  · intro δ z w hδ
    have hc : (∫ _u : K, z ∂ν) = z := by
      rw [integral_const, probReal_univ, one_smul]
    show ‖(∫ u : K, f w u ∂ν) - z‖ ≤ δ
    rw [← hc, ← integral_sub (hint w) (integrable_const _)]
    have h := norm_integral_le_of_norm_le_const (μ := ν) (C := δ) (f := fun u : K => f w u - z)
      (Filter.Eventually.of_forall fun u : K => hδ u u.2)
    rwa [probReal_univ, mul_one] at h

theorem exists_average : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (K : AddSubgroup (WO A T)), IsCompact (K : Set (WO A T)) → (∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1) → ∀ (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∃ g : WO A T → ℂ, Continuous g ∧ (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), g (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * g u) ∧ (∀ u ∈ K, heisO ψ A T u g = g) ∧ ∀ δ : ℝ, (∀ a ∈ K, ∀ w, ‖heisO ψ A T a q w - q w‖ ≤ δ) → ∀ w, ‖g w - q w‖ ≤ δ := by
  intro D ψ hψ A T K hK hKψ q hq hquasi
  obtain ⟨hTG, hLC, hSC, hT2, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank A.rank
  have hψc : Continuous ψ := hψ.1.1
  have hadd : Continuous fun p : WO A T × WO A T => p.1 + p.2 := hTG.toContinuousAdd.continuous_add
  have hf : Continuous fun p : WO A T × WO A T => heisO ψ A T p.2 q p.1 :=
    (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd)).mul (hq.comp hadd)
  obtain ⟨g, h1, h2, h3, h4⟩ := @exists_average_of_compact (WO A T) _ _ hTG hLC hSC hT2 K hK
    (fun w u => heisO ψ A T u q w) hf
  refine ⟨g, h1, fun γ w => h2 _ _ _ fun u _ => GlobalTheory.OrientedHeis.heisO_quasi u q hquasi γ w,
    fun u₀ hu₀ => funext fun w => h3 (ψ (symplOH A T w u₀)) (w + u₀) w u₀ hu₀ fun u hu => ?_,
    fun δ hδ w => h4 δ (q w) w fun a ha => hδ a ha w⟩
  have h := congrFun (GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) u₀ u q) w
  rw [hKψ u₀ hu₀ u hu, one_smul] at h
  exact h

end GlobalTheory.HeisAvgCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInjectiveModel
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod Filter
open GlobalTheory.PlaceModel (half mem_half isHalf_iff heisL heisL_half heisL_comm hO_smul_left infPart_half)
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LocMod.Inhab

namespace GlobalTheory.LocMod.Exist

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def stdFrame (k : Type) [Field k] (N : ℕ) : GlobalTheory.LocMod.Frame k N (Fin N) := ⟨1, 1, by simp, by simp⟩

def ofSplitPt (q : GlobalTheory.FinPl.SplitPt D k) : Place D k :=
  ⟨q.e, q.split, q.pr, q.sec, q.pr_sec, q.sec_pr, q.cont_pr, q.cont_sec⟩

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
  (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)

def loc {m n : Type} (a : Matrix m n D.host.E) : Matrix m n k := a.map (p.π.comp (incA D))

theorem loc_gram_mul (V : HSp D) : loc p V.gram * loc p V.gram⁻¹ = 1 := by
  rw [loc, loc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (gram_det_ne V).isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

theorem loc_mul_gram (V : HSp D) : loc p V.gram⁻¹ * loc p V.gram = 1 := mul_eq_one_comm.1 (loc_gram_mul p V)

def dual (b : Matrix Y Y' k) : WO S T :=
  (loc p S.gram * FS.β * bᵀ * FT.γ * loc p T.gram⁻¹)ᵀ.map fun z => cA D (p.ι z)

theorem up_mem (x : Matrix Y Y' k) : p.up FS FT x ∈ half S T p.e :=
  (isHalf_iff S T).1 fun _ _ => e_mul_ι p _

theorem dual_mem (b : Matrix Y Y' k) : dual p FS FT b ∈ half S T (cA D p.e) :=
  (isHalf_iff S T).1 fun _ _ => by
    simp only [dual, Matrix.map_apply]
    rw [← map_mul, e_mul_ι]

theorem up_add (x y : Matrix Y Y' k) : p.up FS FT (x + y) = p.up FS FT x + p.up FS FT y := by
  ext i j
  simp only [Place.up, Matrix.mul_add, Matrix.add_mul, Matrix.map_apply, Matrix.add_apply, map_add]

theorem dual_add (x y : Matrix Y Y' k) : dual p FS FT (x + y) = dual p FS FT x + dual p FS FT y := by
  ext i j
  simp only [dual, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Matrix.map_apply, Matrix.add_apply, map_add]

theorem up_zero : p.up FS FT 0 = 0 := by simpa using up_add p FS FT 0 0

theorem dual_zero : dual p FS FT 0 = 0 := by simpa using dual_add p FS FT 0 0

theorem continuous_up : Continuous (p.up FS FT) :=
  ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_map p.cont_ι

theorem continuous_dual : Continuous (dual p FS FT) :=
  ((((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_transpose).matrix_map ((GlobalTheory.DualPairCompare.continuous_cA D).comp p.cont_ι)

theorem π_hO (x y : WO S T) : p.π (hO S T x y) = Matrix.trace
    (loc p S.gram⁻¹ * (Matrix.map y fun z => p.π (cA D z))ᵀ * loc p T.gram * Matrix.map x p.π) := by
  simp only [hO, map_sum, map_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, loc, Matrix.map_apply,
    Matrix.transpose_apply, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm

theorem π_hO_dual (t b : Matrix Y Y' k) : p.π (hO S T (p.up FS FT t) (dual p FS FT b)) = ∑ r, ∑ q, b r q * t r q := by
  have h1 : (Matrix.map (dual p FS FT b) fun z => p.π (cA D z)) = (loc p S.gram * FS.β * bᵀ * FT.γ * loc p T.gram⁻¹)ᵀ := by
    ext i j
    simp only [dual, Matrix.map_apply, cA_cA, p.π_ι]
  have h2 : Matrix.map (p.up FS FT t) p.π = FT.β * t * FS.γ := by
    ext i j
    simp only [Place.up, Matrix.map_apply, p.π_ι]
  rw [π_hO, h1, h2, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [loc_mul_gram, Matrix.one_mul, Matrix.mul_assoc _ _ (loc p T.gram), loc_mul_gram, Matrix.mul_one,
    Matrix.mul_assoc _ _ FT.β, FT.γβ, Matrix.mul_one, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [FS.γβ, Matrix.one_mul, Finset.sum_comm]
  rfl

theorem exists_dual {y : WO S T} (hy : IsHalf (cA D p.e) y) : ∃ b, dual p FS FT b = y := by
  refine ⟨(FS.γ * loc p S.gram⁻¹ * (Matrix.map y fun z => p.π (cA D z))ᵀ * loc p T.gram * FT.β)ᵀ, ?_⟩
  rw [dual, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ FS.β, FS.βγ, Matrix.mul_one, loc_gram_mul, Matrix.one_mul, Matrix.mul_assoc _ FT.β, FT.βγ,
    Matrix.mul_one, Matrix.mul_assoc, loc_gram_mul, Matrix.mul_one, Matrix.transpose_transpose]
  ext i j
  simp only [Matrix.map_apply, p.ι_π, map_mul, cA_cA]
  exact hy i j

theorem char_sympl {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) (t b : Matrix Y Y' k) :
    ψ (symplO S T (p.up FS FT t) (dual p FS FT b)) = pairing ψk t b := by
  rw [pairing, ← π_hO_dual p FS FT, h, p.ι_π, ← hO_smul_left, (mem_half S T).1 (up_mem p FS FT t)]
  rfl

theorem exists_isLoc (F : GlobalTheory.LocMod.Frame k S.rank Y) (gk : GL Y k) : ∃ g, p.IsLoc F g gk := by
  obtain ⟨he1, he2, -⟩ := p.split
  have keyM : ∀ X Z : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Theta.AE D), X.map p.π = Z.map p.π ↔ p.e • X = p.e • Z :=
    fun X Z => by
      simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← p.ι_π]
      exact forall₂_congr fun i j => ⟨congrArg _, fun h => by simpa only [p.π_ι] using congrArg p.π h⟩
  have lift : ∀ Z : Matrix (Fin S.rank) (Fin S.rank) k, (Z.map p.ι).map p.π = Z := fun Z => Matrix.ext fun i j => p.π_ι _
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.SplitOnto.exists_unitary (c := cA D) cA_cA (GlobalTheory.SplitOnto.gram_mul_inv S)
    (GlobalTheory.SplitOnto.gram_conj S) he1 he2 ((F.β * gk.val * F.γ).map p.ι) ((F.β * (gk⁻¹).val * F.γ).map p.ι) (by
      rw [← keyM, Matrix.map_mul, lift, lift, Matrix.map_one _ (map_zero _) (map_one _)]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc _ F.γ, F.γβ, Matrix.mul_one, Matrix.mul_assoc F.β, Units.inv_mul, Matrix.mul_one, F.βγ])
  let g' : HR (AF D.host.F) D.sp.cm.sig S.gram := ⟨g, h1⟩
  exact ⟨g', fun i j => congrFun (congrFun h2 i) j, ((keyM _ _).2 h3).trans (lift _)⟩

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  smul_mem' c _ h := GlobalTheory.OrientedHeis.theta_smul c h

theorem exists_injective_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), ∃ Tm, p.IsModel ψ FS FT Tm ∧ Function.Injective Tm := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT
  obtain ⟨⟨ψk, hk⟩, hk', -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨he, hec, v, ε, hε, heq⟩ := p.split
  have he' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε * cA D p.e = cA D p.e := by
    rw [← heq]; linear_combination he' + hec
  have i1 := fun x => infPart_half hε heε (up_mem p FS FT x)
  have i2 := fun x => infPart_half hε heε' (dual_mem p FS FT x)
  have h0 : ∀ f, heisL S T ψ 0 f = f := fun f => by
    funext w
    change ψ (symplOH S T w 0) * f (w + 0) = f w
    rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]
  have sm : ∀ j : Matrix Y Y' k → WO S T, Continuous j → j 0 = 0 → (∀ x, (j x).map (infPart D) = 0) →
      ∀ f ∈ thetaSub ψ S T, ∀ᶠ x in 𝓝 0, heisL S T ψ (j x) f = f := fun j hj j0 hi f hf => by
    obtain ⟨U, hU, h⟩ := IsThetaFunO.level hf
    filter_upwards [(hU.preimage hj).mem_nhds (show j 0 ∈ U by rw [j0]; exact U.zero_mem)] with x hx
    exact h _ hx (hi x)
  obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ S T
  have a1 : ∀ x x' f, heisL S T ψ (p.up FS FT x) (heisL S T ψ (p.up FS FT x') f) = heisL S T ψ (p.up FS FT (x + x')) f :=
    fun x x' f => by rw [up_add, heisL_half S T ψ (by rw [mul_comm, hec]) _ (up_mem p FS FT x) _ (up_mem p FS FT x')]
  have a2 : ∀ x x' f, heisL S T ψ (dual p FS FT x) (heisL S T ψ (dual p FS FT x') f) =
      heisL S T ψ (dual p FS FT (x + x')) f := fun x x' f => by
    rw [dual_add, heisL_half S T ψ (by rw [cA_cA, hec]) _ (dual_mem p FS FT x) _ (dual_mem p FS FT x')]
  have a3 : ∀ x y f, heisL S T ψ (p.up FS FT x) (heisL S T ψ (dual p FS FT y) f) =
      pairing ψk x y • heisL S T ψ (dual p FS FT y) (heisL S T ψ (p.up FS FT x) f) := fun x y f => by
    rw [heisL_comm, char_sympl p FS FT hk]
  have a4 : ∀ x, ∀ f ∈ thetaSub ψ S T, heisL S T ψ (p.up FS FT x) f ∈ thetaSub ψ S T :=
    fun x f hf => GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (i1 x)
  have a5 : ∀ x, ∀ f ∈ thetaSub ψ S T, heisL S T ψ (dual p FS FT x) f ∈ thetaSub ψ S T :=
    fun x f hf => GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (i2 x)
  obtain ⟨g, hg, g0, h1, h2⟩ := exists_vacuum (hk' ψk hk).1 (hk' ψk hk).2 (fun x => heisL S T ψ (p.up FS FT x))
    (fun b => heisL S T ψ (dual p FS FT b)) a1 a2 (fun f => by rw [up_zero, h0]) (fun f => by rw [dual_zero, h0]) a3
    (thetaSub ψ S T) a4 a5 (sm _ (continuous_up p FS FT) (up_zero p FS FT) i1)
    (sm _ (continuous_dual p FS FT) (dual_zero p FS FT) i2) hf f0
  obtain ⟨Tm, hT⟩ := exists_embedding (hk' ψk hk).1 (hk' ψk hk).2 (fun x => heisL S T ψ (p.up FS FT x))
    (fun b => heisL S T ψ (dual p FS FT b)) a1 a2 a3 (thetaSub ψ S T) a4 a5 hg g0 h1 h2
  refine ⟨Tm ∘ₗ (SB (Matrix Y Y' k)).subtype, ⟨fun Φ => (hT Φ.1 Φ.2).2.1, fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩,
    (injective_iff_map_eq_zero _).2 fun Φ hΦ => Subtype.ext ((hT Φ.1 Φ.2).1 hΦ)⟩
  · exact (congrArg Tm (funext h)).trans ((hT Φ.1 Φ.2).2.2.1 x)
  · obtain ⟨b, rfl⟩ := exists_dual p FS FT hy
    simp only [char_sympl p FS FT hk] at h
    exact (congrArg Tm (funext h)).trans ((hT Φ.1 Φ.2).2.2.2 b)

theorem exists_place : ∀ (D : D7) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (p : Place D k), p.e = e := GlobalTheory.PlaceOfIdem.exists_place

theorem exists_place_closed (D : D7) : ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k)
    (_ : IsNonarchimedeanLocalField k), Nonempty (Place D k) :=
  let ⟨e, he⟩ := GlobalTheory.LocMod.Inhab.exists_isSplitIdem D
  let ⟨k, a, b, c, d, q, _⟩ := exists_place D e he
  ⟨k, a, b, c, d, ⟨q⟩⟩

theorem exists_char_comp_loc : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), (∀ ψ, IsStdChar D ψ (-1) → ∃ ψk : AddChar k Circle, p.IsChar ψ ψk ∧ Continuous ψk ∧ ψk ≠ 1) ∧ (∀ χ : (Formalism.L2.Theta.AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ) ∧ (∀ (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (gk : GL Y k), ∃ g, p.IsLoc F g gk) :=
  fun D k _ _ _ _ p => ⟨fun ψ hψ => let ⟨⟨ψk, h⟩, h', _⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ; ⟨ψk, h, h' ψk h⟩,
    let ⟨ψ, hψ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).2; (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.2.2,
    fun _ _ _ _ F gk => exists_isLoc p F gk⟩

theorem exists_frames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := GlobalTheory.LocMod.normalFrames_exist

theorem inhabitants : (∀ D : D7, ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k)
      (_ : IsNonarchimedeanLocalField k), Nonempty (Place D k)) ∧
    (∀ (D : D7) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (p : Place D k), p.e = e) ∧
    (∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), (∀ ψ, IsStdChar D ψ (-1) → ∃ ψk : AddChar k Circle, p.IsChar ψ ψk ∧ Continuous ψk ∧ ψk ≠ 1) ∧ (∀ χ : (Formalism.L2.Theta.AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ) ∧ (∀ (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (gk : GL Y k), ∃ g, p.IsLoc F g gk)) ∧
    (∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y), ∃ Tm, p.IsModel ψ FS FT Tm ∧ Function.Injective Tm) ∧
    (∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F) :=
  ⟨exists_place_closed, exists_place, exists_char_comp_loc, exists_injective_model, exists_frames⟩

end GlobalTheory.LocMod.Exist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdeleAtPlaceWithComponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralAdele_atPlace_with_component : ∀ (D : D7) (v : Pl D) (z : Fv D.host.F v ⊗[D.host.F] D.host.E), z ∈ intV D v → ∃ x ∈ intAt D (· = v), compAt D v x = z := by
  first | exact @GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq | exact GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq | (intros; apply GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralBasis_of_latticeAtPlace_stable : ∀ (D : D7) (n : ℕ) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin n → AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ y ∈ Λ, ∀ i, y i ∈ idAt D (· = v)) → (∀ a ∈ intAt D (· = v), ∀ y ∈ Λ, a • y ∈ Λ) → (∃ m : ℕ, 0 < m ∧ ∀ y : Fin n → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ Λ) → (∃ N : ℕ, 0 < N ∧ ∀ y ∈ Λ, ∀ i, (N : AE D) * y i ∈ intAt D (· = v)) → ∃ β β' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, β i j ∈ idAt D (· = v)) ∧ (∀ i j, β' i j ∈ idAt D (· = v)) ∧ β * β' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ β' * β = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ (∀ y : Fin n → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) := by
  first | exact @GlobalTheory.IwaPlace.FreeAt.exists_basis | exact GlobalTheory.IwaPlace.FreeAt.exists_basis | (intros; apply GlobalTheory.IwaPlace.FreeAt.exists_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaxCompactRealPointsOfOrthonormalFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maxCompact_realPoints_of_orthonormalFrames : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D), ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∃ K : Subgroup (GA D V), IsMaxCompactInf V K ∧ (∃ j : (∀ τ, Formalism.REAL.KG (ε τ)) →* K, Function.Surjective j ∧ ∀ τ k, (j (Pi.mulSingle τ k) : GA D V) = kAt θ V τ (ε τ) (fr τ) k) := by
  first | exact @GlobalTheory.FrameCompact.exists_maxCompact_of_frames | exact GlobalTheory.FrameCompact.exists_maxCompact_of_frames | (intros; apply GlobalTheory.FrameCompact.exists_maxCompact_of_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPadicCoordinatesOfDegreeOneSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicCoordinates_of_degreeOne_splitPlace : ∀ (D : D7) (T : ℕ) [Fact T.Prime] (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ (v : Pl D) (pr : AE D →+* ℚ_[T]) (sec : ℚ_[T] →+ AE D), (∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a, pr (sec a) = a) ∧ (∀ x, sec (pr x) = e * x) ∧ Continuous pr ∧ Continuous sec ∧ ∀ a, ‖a‖ ≤ 1 ↔ finPart D (sec a) ∈ intAE D := by
  first | exact @GlobalTheory.FinPl.SplitQT.exists_coord_padic | exact GlobalTheory.FinPl.SplitQT.exists_coord_padic | (intros; apply GlobalTheory.FinPl.SplitQT.exists_coord_padic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_orb_rat_eq_x0 : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x ∈ orb B, (rat x : Mx D B.V.rank (σ + 1)) = x0 B := by
  first | exact @GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint | exact GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint | (intros; apply GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagStabilizer_eq_unipotent_torus_levi_atPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S g ⬝ d.jX = d.jX ⬝ a) → ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), g = n * d.levi t * d.emb0 γ := by
  first | exact @GlobalTheory.IwaFlag.flag_stab | exact GlobalTheory.IwaFlag.flag_stab | (intros; apply GlobalTheory.IwaFlag.flag_stab <;> assumption)
end

