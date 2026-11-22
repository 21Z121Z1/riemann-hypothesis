import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0128
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatDual

theorem lamHat_eq_hat {D : D7} (V : HSp D) :
    LamHat V = GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  have : (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    rw [SetLike.mem_coe, GlobalTheory.Member.mem_latC, Module.Basis.equivFun_symm_apply]
    rfl
  rw [this]
  rfl

theorem integralTensorAdeles_eq_adelicCompletion_one (D : D7) :
    intAE D = GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
  unfold intAE GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
    exact ⟨a, ha, x, rfl⟩

theorem hR_eq_hermA {D : D7} (V : HSp D)
    (z y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y =
      GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y z := by
  unfold hR Formalism.UG.hform GlobalTheory.AdLat.hermA
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm, mul_comm (sigR _ _ _), ← mul_assoc]
  rfl

theorem smul_mem_lamHat {D : D7} (V : HSp D) :
    ∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V := by
  intro a ha y hy
  rw [lamHat_eq_hat] at hy ⊢
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨s, hs, o, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x,
        (GlobalTheory.Member.latC V).smul_mem o hx, ?_⟩
      funext i
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero =>
      simp only [Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add]
      exact add_mem hu hw
    | neg u _ hu =>
      simp only [Pi.neg_apply, mul_neg]
      exact neg_mem hu
  | zero =>
    simp only [zero_mul]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [add_mul]
    exact add_mem hu hw
  | neg u _ hu =>
    simp only [neg_mul]
    exact neg_mem hu

theorem lamHat_selfDual_and_module : ∀ {D : D7} (V : HSp D), (∀ y, y ∈ LamHat V ↔ ∀ z ∈ LamHat V, hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y ∈ intAE D) ∧ (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) := by
  intro D V
  refine ⟨fun y => ?_, smul_mem_lamHat V⟩
  obtain ⟨-, -, hfg, hspan, hcc, -, -, hG, hdet, -, hL⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := GlobalTheory.AdLat.hat_selfDual D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (GlobalTheory.Member.cF D)
    V.gram.transpose 1 hfg hspan hcc hG hdet one_ne_zero hL
  rw [← integralTensorAdeles_eq_adelicCompletion_one, ← lamHat_eq_hat] at key
  simp only [hR_eq_hermA]
  constructor
  · intro hy z hz
    rw [lamHat_eq_hat] at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hz
      have h1 : (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨t, ht, 1, rfl⟩
      have h2 := (key _).2 (smul_mem_lamHat V _ h1 y hy) x hx
      convert h2 using 1
      unfold GlobalTheory.AdLat.hermA
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have e : GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (t ⊗ₜ[D.host.F] x b) =
          (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) *
            GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (GlobalTheory.AdLat.fv D.host.F x b) := by
        simp [GlobalTheory.AdLat.sg, GlobalTheory.AdLat.fv]
      rw [e]
      ring
    | zero =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y 0 = 0 := by simp [GlobalTheory.AdLat.hermA]
      rw [this]; exact zero_mem _
    | add u w _ _ hu hw =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (u + w) =
          GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u +
            GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y w := by
        simp only [GlobalTheory.AdLat.hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      rw [this]; exact add_mem hu hw
    | neg u _ hu =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (-u) =
          -GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u := by
        simp only [GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
      rw [this]; exact neg_mem hu
  · intro h
    refine (key y).1 fun x hx => h _ ?_
    rw [lamHat_eq_hat]
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

end GlobalTheory.LatDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceBelowCMFieldOfSqrtNegPrime
section
open NumberField IsDedekindDomain

namespace GlobalTheory.SplitOfNegPrime

theorem sqrt_neg_not_mem_maximalRealSubfield (L : Type) [Field L] [NumberField L] [IsCMField L]
    (p : ℕ) (δ : L) (hp : 0 < p) (hδ : δ ^ 2 = -(p : L)) : δ ∉ maximalRealSubfield L := by
  intro hmem
  let x : maximalRealSubfield L := ⟨δ, hmem⟩
  have hx : x ^ 2 = -(p : maximalRealSubfield L) := Subtype.ext (by simpa [x] using hδ)
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield L)) := inferInstance
  have hv : v.IsReal := IsTotallyReal.isReal v
  have h := congrArg (InfinitePlace.embedding_of_isReal hv) hx
  rw [map_pow, map_neg, map_natCast] at h
  have h1 : (0 : ℝ) < p := by exact_mod_cast hp
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]

theorem isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L), 0 < p → δ ^ 2 = -(p : L) → ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 → ∀ w : HeightOneSpectrum (𝓞 L), (q : 𝓞 L) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
  intro L _ _ _ p q δ hp hδ hdvd w hw
  set Lp := maximalRealSubfield L
  set u := w.under (𝓞 Lp)
  obtain ⟨k, hk⟩ := hdvd
  set z : 𝓞 Lp := -(2 * (q : 𝓞 Lp) * (k : 𝓞 Lp)) with hz
  have hq : (q : 𝓞 Lp) ∈ u.asIdeal := by
    change _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  have hzu : z ∈ u.asIdeal := by
    rw [hz]
    exact u.asIdeal.neg_mem_iff.2 (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq))
  have hk' : ((p : ℤ) : 𝓞 Lp) + 1 = (((8 * q : ℕ) : ℤ) : 𝓞 Lp) * (k : 𝓞 Lp) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 Lp) hk
  have hsq : (1 + 4 * z : 𝓞 Lp) = -(p : 𝓞 Lp) := by
    rw [hz]
    push_cast at hk'
    linear_combination hk'
  have h1 := GlobalTheory.HenselSquare.isSquare_one_add_four_mul Lp u z hzu
  rw [hsq] at h1
  refine GlobalTheory.SplitOfSquare.isSplitAt_of_isSquare L (-(p : Lp)) δ (by rw [hδ]; push_cast; rfl)
    (sqrt_neg_not_mem_maximalRealSubfield L p δ hp hδ) w ?_
  simpa using h1

end GlobalTheory.SplitOfNegPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelOperatorMapsStabiliserEquivariantForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ.FiCore

theorem isVal_sum {ι Yv : Type} [Fintype ι] {n : ℕ} (fr : Yv → ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    {κ : Type} (s : Finset κ) (w : κ → ℂ) (f : κ → Yv → ℂ) (h : ∀ c, IsVal fr lam (RingHom.id ℂ) (f c)) :
    IsVal fr lam (RingHom.id ℂ) (∑ c ∈ s, w c • f c) := by
  choose P hP hf using h
  refine ⟨∑ c ∈ s, w c • P c, Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hP c), ?_⟩
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hf, evG, MvPolynomial.eval₂_sum, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, RingHom.id_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem lawAt_sum {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (i : ℕ)
    (g : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E × ℂ)
    {κ : Type} (s : Finset κ) (w : κ → ℂ) (f : κ → C.Y i → ℂ) (h : ∀ c, LawAt O i g (f c)) :
    LawAt O i g (∑ c ∈ s, w c • f c) := by
  intro y y' hy
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [h c y y' hy]; ring

theorem K_mem_Fi : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (G : StabDat C), FormsAre M O G → (∀ i < D.R.m, UnfIs O i (nuT D u i)) → (∀ i < D.R.m, ∀ c c', Differentiable ℂ (O.Th i c c')) → (∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw O i c c' g) → ∀ i < D.R.m, ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  intro D u C A Pm M O G hF hU hd hT i hi φ hφ
  have hv := hF.1 i hi.le φ hφ
  refine (hF.2 (i + 1) (Nat.le_add_left 1 i) hi _).2 fun c' => ?_
  have hK : C.K i φ c' = ∑ c, C.wt i c • C.Kmap i c c' (φ c) := by
    simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM]
  rw [hK]
  exact ⟨isVal_sum _ _ _ _ _ fun c => GlobalTheory.T.pair_kernel_maps_step_weight_values D u C A Pm M O i hi (hU i hi) c c' _ (hv c),
    fun g hg => lawAt_sum O _ g _ _ _ fun c =>
      GlobalTheory.T.pair_kernel_term_target_stabiliser_law D u C A Pm M O i hi (hU i hi) c c' (hd i hi c c') g (hT i hi c c' g hg) _ (hv c)⟩

end GlobalTheory.KerJ.FiCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

def Clos {R : Type} [CommRing R] (S : Subring R) (π : R) : Subring R where
  carrier := {x | ∀ n : ℕ, ∃ s ∈ S, π ^ n ∣ x - s}
  mul_mem' := by
    intro a b ha hb n
    obtain ⟨s, hs, c, hc⟩ := ha n
    obtain ⟨s', hs', c', hc'⟩ := hb n
    refine ⟨s * s', mul_mem hs hs', a * c' + s' * c, ?_⟩
    linear_combination a * hc' + s' * hc
  one_mem' := fun n => ⟨1, one_mem _, by simp⟩
  add_mem' := by
    intro a b ha hb n
    obtain ⟨s, hs, c, hc⟩ := ha n
    obtain ⟨s', hs', c', hc'⟩ := hb n
    refine ⟨s + s', add_mem hs hs', c + c', ?_⟩
    linear_combination hc + hc'
  zero_mem' := fun n => ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    intro a ha n
    obtain ⟨s, hs, c, hc⟩ := ha n
    refine ⟨-s, neg_mem hs, -c, ?_⟩
    linear_combination -hc

variable {l : ℕ} [Fact l.Prime]

def linv (l : ℕ) [Fact l.Prime] : Per.AinfP l := ((GlobalTheory.RingBasics.isUnit_l l).unit⁻¹ : (Per.AinfP l)ˣ)

theorem mul_linv : ((l : ℕ) : Per.AinfP l) * linv l = 1 := (GlobalTheory.RingBasics.isUnit_l l).mul_val_inv

def beta (ϖ : Per.Fl l) : Per.AinfP l :=
  linv l * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) - 1

theorem l_mul_beta (ϖ : Per.Fl l) : ((l : ℕ) : Per.AinfP l) * beta ϖ =
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) - ((l : ℕ) : Per.AinfP l) := by
  have h := mul_linv (l := l)
  rw [beta]
  linear_combination algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) * h

def Sa (ϖ : Per.Fl l) : Subalgebra (Per.Ainf l) (Per.AinfP l) := Algebra.adjoin _ {beta ϖ}

def Sg (ϖ : Per.Fl l) : Subring (Per.BdRp l) :=
  (Sa ϖ).toSubring.map (algebraMap (Per.AinfP l) (Per.BdRp l))

def betaD (ϖ : Per.Fl l) : Per.BdRp l := algebraMap (Per.AinfP l) (Per.BdRp l) (beta ϖ)

end GlobalTheory.Pst.StLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ N → (∀ k ∈ Formalism.IndefR.Lev.levG V β L, ∃ n : ℕ, 0 < n ∧ Formalism.IndefR.Lev.levChi V β L k ^ n = 1) ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ g, SuppF V f g → (g ∈ Formalism.IndefR.Lev.levG V β L ↔ g ∈ KsphC V ∅)) ∧ (∀ g ∈ Formalism.IndefR.Lev.levG V β L, SuppF V f g → Formalism.IndefR.Lev.levChi V β L g = 1) ∧ ∀ k ∈ Formalism.IndefR.Lev.levG V β L, ∃ k₁ ∈ Formalism.IndefR.Lev.levG V β L, ∃ k₂ ∈ Formalism.IndefR.Lev.levG V β L, SuppF V f k₁ ∧ SuppF V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  first | exact @GlobalTheory.LevSplit.lev_split | exact GlobalTheory.LevSplit.lev_split | (intros; apply GlobalTheory.LevSplit.lev_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTransportIsometry
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section
open scoped BigOperators ComplexConjugate

namespace GlobalTheory.ThLoc.LocPull

open Formalism.L2.Th1.H (blk4 pow4 slice imgLat tens4 kernel4)

variable {n : Type} [Fintype n] [DecidableEq n]

def diagonalPowFourEquiv (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun z w := φ (slice w.1 z) w.2
  invFun z w := φ.symm (slice w.1 z) w.2
  map_add' x y := by
    funext w
    have e : slice w.1 (x + y) = slice w.1 x + slice w.1 y := rfl
    simp only [e, map_add, Pi.add_apply]
  map_smul' c x := by
    funext w
    have e : slice w.1 (c • x) = c • slice w.1 x := rfl
    simp only [e, map_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv z := by
    funext w
    have e : slice w.1 (fun w' : Fin 4 × n => φ (slice w'.1 z) w'.2) = φ (slice w.1 z) := rfl
    simp only [e, LinearEquiv.symm_apply_apply]
    rfl
  right_inv z := by
    funext w
    have e : slice w.1 (fun w' : Fin 4 × n => φ.symm (slice w'.1 z) w'.2) = φ.symm (slice w.1 z) := rfl
    simp only [e, LinearEquiv.apply_symm_apply]
    rfl

theorem slice_pow4E (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (a : Fin 4) (z : Fin 4 × n → ℂ) :
    slice a (diagonalPowFourEquiv φ z) = φ (slice a z) := rfl

theorem fourCopiesHermitianForm_eq_sum_blocks (h : Matrix n n ℂ) (x y : Fin 4 × n → ℂ) :
    matH (blk4 h) x y = ∑ a : Fin 4, matH h (slice a x) (slice a y) := by
  show (∑ w, ∑ w', x w * blk4 h w w' * conj (y w')) = ∑ a : Fin 4, ∑ i, ∑ j, x (a, i) * h i j * conj (y (a, j))
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [blk4]
  · intro b _ hb
    simp [blk4, Ne.symm hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem blockwiseActionOnFourCopies_isometry (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (h : Matrix n n ℂ)
    (hφ : IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ))) (x y : Fin 4 × n → ℂ) :
    matH (blk4 h) (diagonalPowFourEquiv φ x) (diagonalPowFourEquiv φ y) = matH (blk4 h) x y := by
  rw [fourCopiesHermitianForm_eq_sum_blocks, fourCopiesHermitianForm_eq_sum_blocks]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [slice_pow4E, slice_pow4E]
  exact hφ _ _

theorem imgLat_pull (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    imgLat (((diagonalPowFourEquiv φ).trans g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
        (pow4 (Λ.comap φ.toLinearMap.toAddMonoidHom)) =
      imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨diagonalPowFourEquiv φ x, fun a => hx a, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(diagonalPowFourEquiv φ).symm x, fun a => ?_, ?_⟩
    · show φ (slice a ((diagonalPowFourEquiv φ).symm x)) ∈ Λ
      rw [← slice_pow4E, LinearEquiv.apply_symm_apply]
      exact hx a
    · show g (diagonalPowFourEquiv φ ((diagonalPowFourEquiv φ).symm x)) = g x
      rw [LinearEquiv.apply_symm_apply]

theorem locNorm_pull : ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)), IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h (Λ.comap φ.toLinearMap.toAddMonoidHom) (fun z => θ (φ z)) p ι := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι φ hφ H
  obtain ⟨g₁, ε, hiso, hnd, hidx, hε, hker⟩ := H
  have hI := imgLat_pull φ Λ g₁
  refine ⟨(diagonalPowFourEquiv φ).trans g₁, ε, ?_, ?_, ?_, hε, ?_⟩
  · intro x y
    exact (hiso (diagonalPowFourEquiv φ x) (diagonalPowFourEquiv φ y)).trans (blockwiseActionOnFourCopies_isometry φ h hφ x y)
  · rw [hI]
    exact hnd
  · rw [hI]
    exact hidx
  · funext z
    have t1 : tens4 (fun z => θ (φ z)) z = tens4 θ (diagonalPowFourEquiv φ z) := rfl
    rw [t1, hker]
    simp only [Pi.smul_apply]
    congr 1
    unfold kernel4
    rw [hI]
    rfl

end GlobalTheory.ThLoc.LocPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesLinearCoordsEqFlatTaylor
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.FlatTaylorBridge

open MvPowerSeries

theorem coeff_taylorMv_flatV (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (hG : AnalyticOnNhd ℂ G Set.univ) (m : DVar X.Tau N N' →₀ ℕ) :
    coeff m (taylorMv fun z => G (s.flatV N N' z)) =
      TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  have hc : ∀ k : ℕ, ContDiff ℂ k G := fun k => hG.contDiff
  let G' : VCx X.Tau N N' → ℂ := fun w => G fun τ => w (s.iT.symm τ)
  let L : VCx X.Tau N N' →L[ℂ] TaylorLogMetric.VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
  have hG' : AnalyticOnNhd ℂ G' Set.univ := by
    have : G' = G ∘ L := rfl
    rw [this]
    exact hG.comp (L.analyticOnNhd _) (fun _ _ => trivial)
  have h1 := Formalism.L2.AlgTh.taylor_jet_expansion X.Tau N N' G' hG' m
  have h2 := GlobalTheory.SeamTransport.deriv_transport s.iT G hc m
  rw [GlobalTheory.SeamTransport.taylor_eq] at h2
  have hfl : (fun z => G (s.flatV N N' z)) = fun z => G' (Formalism.L2.AlgTh.flat X.Tau N N' z) := rfl
  have hne : ((m.mapDomain fun v => (s.iT v.1, v.2)).prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hpr : ((m.mapDomain fun v => (s.iT v.1, v.2)).prod fun _ n => (n.factorial : ℂ)) =
      ((Formalism.DworkPowerSeriesWeights.mfact m : ℕ) : ℂ) := by
    rw [Finsupp.prod_mapDomain_index_inj]
    · simp [Formalism.DworkPowerSeriesWeights.mfact, Finsupp.prod]
    · intro v w h
      exact Prod.ext (s.iT.injective (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2
  apply mul_left_cancel₀ hne
  rw [← h2, hpr, hfl]
  convert h1 using 3

end GlobalTheory.FlatTaylorBridge

namespace GlobalTheory.FlatTaylorBridge
open MvPowerSeries

theorem subst_rename_lin {σ τ γ : Type} [Finite σ] [Finite τ] {R : Type} [CommRing R] (f : σ → τ)
    (a : τ → MvPowerSeries γ R) (ha : ∀ t, constantCoeff (a t) = 0) (Φ : MvPowerSeries σ R) :
    subst a (rename f Φ) = subst (fun s => a (f s)) Φ := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp f) hs Φ]
  congr 1
  funext x
  exact subst_X hs (f x)

theorem bridge : ∀ (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), Formalism.L2.KerInert.IotaExt lm ι → ∀ G : TaylorLogMetric.VC D N N' → ℂ, AnalyticOnNhd ℂ G Set.univ → TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (TaylorLogMetric.pSer D lm G) = Formalism.L2.Th1.G.linSub (fun (i : DVar X.Tau N N') x => M (s.iT i.1, i.2) x) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
  intro D X s N N' p _ lm ι hι G hG hC ν _ M
  let eE : DVar X.Tau N N' ≃ D.what₂.Tau × Fin N' × Fin N := s.iT.prodCongr (Equiv.refl _)
  have hP : TaylorLogMetric.pSer D lm G =
      rename (eE : DVar X.Tau N N' → D.what₂.Tau × Fin N' × Fin N)
        (map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
    ext α
    obtain ⟨m, rfl⟩ := Finsupp.mapDomain_surjective eE.surjective α
    have h := coeff_embDomain_rename eE.toEmbedding
      (map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) m
    rw [Finsupp.embDomain_eq_mapDomain] at h
    refine Eq.trans ?_ h.symm
    rw [coeff_map, coeff_taylorMv_flatV D X s N N' G hG m]
    change TaylorLogMetric.lamC lm (TaylorLogMetric.taylor D G _) = _
    unfold TaylorLogMetric.lamC
    rw [dif_pos (hC _)]
    exact (hι ⟨_, hC _⟩).symm
  rw [hP]
  unfold TaylorLogMetric.atLin Formalism.L2.Th1.G.linSub
  rw [subst_rename_lin]
  · congr 1
  · intro t
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_mul, constantCoeff_X, mul_zero]

end GlobalTheory.FlatTaylorBridge
end
end

