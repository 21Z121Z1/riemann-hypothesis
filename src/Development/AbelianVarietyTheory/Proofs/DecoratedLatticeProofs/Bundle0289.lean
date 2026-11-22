import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFockSpaceOfPolynomialGaussianSlices
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.FockSlice

theorem exists_finset_inf_eq_iInf {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (U : I → Submodule K V) : ∃ F : Finset I, F.inf U = ⨅ i, U i := by
  classical
  have hex : ∃ n, ∃ F : Finset I, Module.finrank K ((F.inf U : Submodule K V)) = n := ⟨_, ∅, rfl⟩
  obtain ⟨F, hF⟩ := Nat.find_spec hex
  refine ⟨F, le_antisymm (le_iInf fun i => ?_) (Finset.le_inf fun i _ => iInf_le U i)⟩
  have hle : (insert i F).inf U ≤ F.inf U := Finset.inf_mono (Finset.subset_insert i F)
  have hmin : Nat.find hex ≤ Module.finrank K (((insert i F).inf U : Submodule K V)) := Nat.find_min' hex ⟨_, rfl⟩
  have heq : (insert i F).inf U = F.inf U := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq]
  exact Finset.inf_le (Finset.mem_insert_self i F)

theorem exists_eval_recon {Y : Type} (W : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (S : Finset Y) (g' : Y → Y → ℂ), (∀ y, g' y ∈ W) ∧ ∀ g ∈ W, g = ∑ y ∈ S, g y • g' y := by
  classical
  let U : Y → Submodule ℂ W := fun y => LinearMap.ker ((LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp W.subtype)
  obtain ⟨S, hS⟩ := exists_finset_inf_eq_iInf U
  let R : W →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun s => (LinearMap.proj (s : Y) : (Y → ℂ) →ₗ[ℂ] ℂ).comp W.subtype
  have hR : LinearMap.ker R = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hmem : w ∈ S.inf U := by
      rw [Submodule.mem_finsetInf]
      intro y hy
      have := congrFun hw ⟨y, hy⟩
      simpa [U, R] using this
    rw [hS, Submodule.mem_iInf] at hmem
    ext y
    simpa [U] using hmem y
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
  refine ⟨S, fun y => if h : y ∈ S then (L (Pi.single ⟨y, h⟩ 1) : Y → ℂ) else 0, fun y => ?_, fun g hg => ?_⟩
  · by_cases h : y ∈ S
    · simp only [h, dite_true]; exact (L _).2
    · simp only [h, dite_false]; exact W.zero_mem
  · have h1 : (⟨g, hg⟩ : W) = L (R ⟨g, hg⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨g, hg⟩ = ∑ s : S, g s • (Pi.single s 1 : S → ℂ) := by
      ext t
      simp [R, Finset.sum_apply, Pi.single_apply]
    have h3 := congrArg Subtype.val h1
    rw [h2, map_sum] at h3
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
    refine h3.trans ?_
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [s.2]

end GlobalTheory.StdUnn.FockSlice

namespace GlobalTheory.StdUnn.FockSlice

theorem mem_fockA_of_slices : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), ∀ φ ∈ schwartzA θ V.rank n, (∀ x₀ : Mx D V.rank n, ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ x : Mx D V.rank n, x.map (finPart D) = x₀.map (finPart D) → φ x = evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x)) → φ ∈ fockA θ V n l s := by
  intro D θ hθ V n l s φ hφ hslice
  classical
  obtain ⟨k, c, t, rfl⟩ := Submodule.mem_span_set'.1 hφ
  choose F G hG hFG using fun i => (t i).2
  let fin : Mx D V.rank n → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun x i j => finPart D (x i j)
  let Pre : ((Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) →ₗ[ℂ] (Mx D V.rank n → ℂ) :=
    LinearMap.funLeft ℂ ℂ fin
  let W : Submodule ℂ (Mx D V.rank n → ℂ) := Submodule.span ℂ (Set.range fun i => Pre (G i))
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  obtain ⟨S, g', hg'W, hrec⟩ := exists_eval_recon W
  have hWle : W ≤ (WeilM.SB _).map Pre := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨G i, hG i, rfl⟩)
  choose g'' hg''SB hg''eq using fun y => hWle (hg'W y)
  choose pt hpt _ using fun x y : Mx D V.rank n => GlobalTheory.T.existsUnique_adelicMatrix_realComponents_finitePart D θ hθ V.rank n (fun τ => compAt θ τ x) y
  choose p hp using hslice
  set Φ : Mx D V.rank n → ℂ := ∑ i, c i • (t i : Mx D V.rank n → ℂ) with hΦ
  have hΦx : ∀ x, Φ x = ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin x)) := by
    intro x
    simp only [hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFG i]
  have hpt' : ∀ x y, Φ (pt x y) = ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) := by
    intro x y
    rw [hΦx]
    have e1 : (fun τ a b => compAt θ τ (pt x y) a b) = (fun τ a b => compAt θ τ x a b) := by
      funext τ a b; rw [(hpt x y).1 τ]
    have e2 : fin (pt x y) = fin y := by
      funext a b
      have := congrFun (congrFun (hpt x y).2 a) b
      simpa [fin, Matrix.map_apply] using this
    rw [e1, e2]
  have hG' : ∀ i x, G i (fin x) = ∑ y ∈ S, G i (fin y) * g' y x := by
    intro i x
    have := congrFun (hrec (Pre (G i)) (Submodule.subset_span ⟨i, rfl⟩)) x
    simpa [Pre, LinearMap.funLeft_apply, Finset.sum_apply, smul_eq_mul] using this
  have key : ∀ x, Φ x = ∑ y ∈ S, Φ (pt x y) * g' y x := by
    intro x
    rw [hΦx]
    calc ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin x))
        = ∑ i, ∑ y ∈ S, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) * g' y x :=
          Finset.sum_congr rfl fun i _ => by
            rw [hG' i x, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ y ∈ S, ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) * g' y x := Finset.sum_comm
      _ = ∑ y ∈ S, Φ (pt x y) * g' y x := Finset.sum_congr rfl fun y _ => by rw [hpt', Finset.sum_mul]
  have hfin : ∀ x y, (pt x y).map (finPart D) = y.map (finPart D) := fun x y => (hpt x y).2
  have hcomp : ∀ x y, (fun τ => compAt θ τ (pt x y)) = (fun τ => compAt θ τ x) := fun x y => funext (hpt x y).1
  have hEq : Φ = ∑ y ∈ S, (fun x => evalPoly (p y) (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g'' y (fun i j => finPart D (x i j))) := by
    funext x
    rw [key x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hp y (pt x y) (hfin x y), hcomp x y]
    congr 1
    rw [← hg''eq y]
    rfl
  rw [hEq]
  exact Submodule.sum_mem _ fun y _ => Submodule.subset_span ⟨p y, g'' y, hg''SB y, rfl⟩

end GlobalTheory.StdUnn.FockSlice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SuppGrp

open GlobalTheory.FinPl

theorem placeIdem_mem_idAt {D : D7} {v : Pl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (P : Pl D → Prop) (hP : P v) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D P := by
  obtain ⟨α, rfl, -, h2⟩ := h
  refine Submodule.mem_inf.2 ⟨?_, (Submodule.mem_iInf _).2 fun u => ?_⟩
  · exact TensorProduct.zero_tmul _ (1 : D.host.E)
  · have hu : u.1 ≠ v := fun e => u.2 (e ▸ hP)
    show (evalV D.host.F u.1 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h2 u.1 hu, TensorProduct.zero_tmul]

theorem mem_congGrp {D : D7} (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (h : ∀ i j, (mt V g - 1) i j ∈ I) :
    g ∈ congGrp V I := by
  rw [congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  intro i j
  have h1 := h i j
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at h1
  have : Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this] at h1
  exact h1

theorem mem_grpAt_of_suppAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V), SuppAt q.e V g → ∀ P : GlobalTheory.FinPl.Pl D → Prop, P q.v → g ∈ GlobalTheory.FinPl.grpAt V P := by
  intro D k _ _ _ _ q V g hg P hP
  obtain ⟨ε, h1, h2⟩ := q.above
  refine mem_congGrp V _ g fun i j => ?_
  have h3 := hg i j
  rw [h2] at h3
  rw [← h3]
  exact Ideal.mul_mem_right _ _ (placeIdem_mem_idAt h1 P hP)

end GlobalTheory.SuppGrp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem rTrans_rTrans {G : Type} [Semigroup G] (a b : G) (F : G → ℂ) : rTrans a (rTrans b F) = rTrans (a * b) F := by
  funext g; simp [rTrans, mul_assoc]

theorem rTrans_one {G : Type} [Monoid G] (F : G → ℂ) : rTrans 1 F = F := by
  funext g; simp [rTrans]

def space (Q : QStep S) : Submodule ℂ (GA D S.B'.V → ℂ) where
  carrier := {f | (∀ y, IsContAut S.B'.V (rTrans (Q.gl₂ y) f)) ∧
    ∃ U : Subgroup (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k), IsOpen (U : Set (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)) ∧
      ∀ u ∈ U, rTrans (Q.gl₂ u) f = f}
  zero_mem' := ⟨fun y => ⟨fun _ _ _ => rfl, continuous_const⟩, ⊤, isOpen_univ, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf, U, hU, hfU⟩ ⟨hg, V, hV, hgV⟩
    refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, U ⊓ V, hU.inter hV, fun u hu => ?_⟩
    · change f (γ * x * _) + g (γ * x * _) = f (x * _) + g (x * _)
      have h1 := (hf y).1 γ hγ x
      have h2 := (hg y).1 γ hγ x
      simp only [rTrans] at h1 h2
      rw [h1, h2]
    · exact (hf y).2.add (hg y).2
    · have h1 := hfU u hu.1
      have h2 := hgV u hu.2
      funext x
      have e1 := congrFun h1 x
      have e2 := congrFun h2 x
      simp only [rTrans, Pi.add_apply] at e1 e2 ⊢
      rw [e1, e2]
  smul_mem' := by
    rintro a f ⟨hf, U, hU, hfU⟩
    refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, U, hU, fun u hu => ?_⟩
    · have h1 := (hf y).1 γ hγ x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      rw [h1]
    · exact continuous_const.mul (hf y).2
    · have h1 := hfU u hu
      funext x
      have e1 := congrFun h1 x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul] at e1 ⊢
      rw [e1]

theorem mem_translate (Q : QStep S) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) {f : GA D S.B'.V → ℂ} (hf : f ∈ space Q) :
    rTrans (Q.gl₂ y) f ∈ space Q := by
  obtain ⟨hc, U, hU, hfU⟩ := hf
  refine ⟨fun y' => ?_, U.comap (MulAut.conj y⁻¹).toMonoidHom, ?_, fun u hu => ?_⟩
  · rw [rTrans_rTrans, ← map_mul]; exact hc _
  · have hc : Continuous fun x : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k => y⁻¹ * x * y⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hU.preimage hc
  · have hu' : y⁻¹ * u * y ∈ U := by simpa using hu
    rw [rTrans_rTrans, ← map_mul, show u * y = y * (y⁻¹ * u * y) by group, map_mul, ← rTrans_rTrans, hfU _ hu']

def rep (Q : QStep S) : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) (space Q) where
  toFun y :=
    { toFun := fun f => ⟨rTrans (Q.gl₂ y) f.1, mem_translate Q y f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp [rTrans]
  map_mul' x y := by
    ext f g
    rw [Module.End.mul_apply]
    change f.1 (g * Q.gl₂ (x * y)) = f.1 (g * Q.gl₂ x * Q.gl₂ y)
    rw [map_mul, mul_assoc]

def valK (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ)
    (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ))
    (Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k)) (f : GA D S.B'.V → ℂ) : ℂ :=
  S.B'.per ψ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ))) f

theorem smooth (Q : QStep S) : IsSmoothRep (rep Q) := by
  intro v
  obtain ⟨-, U, hU, hfU⟩ := v.2
  let H : Subgroup (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) :=
    { carrier := {g | rep Q g v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : U ≤ H := fun u hu => Subtype.ext (hfU u hu)
  exact Subgroup.isOpen_mono hle hU

end GlobalTheory.TriStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

variable {D : D7}

def indQ (D : D7) (Q : Finset (Pl D)) : Af D.host.F := ∑ v ∈ Q, singleV D.host.F v 1

def idemQ (D : D7) (Q : Finset (Pl D)) : AF D.host.F := pairA D.host.F 0 (indQ D Q)

def idemQc (D : D7) (Q : Finset (Pl D)) : AF D.host.F := pairA D.host.F 0 (1 - indQ D Q)

open Classical in
theorem evalV_indQ (Q : Finset (Pl D)) (w : Pl D) :
    evalV D.host.F w (indQ D Q) = if w ∈ Q then 1 else 0 := by
  classical
  rw [indQ, map_sum]
  have h : ∀ v ∈ Q, evalV D.host.F w (singleV D.host.F v 1) = if w = v then 1 else 0 := by
    intro v _
    by_cases hwv : w = v
    · subst hwv
      rw [if_pos rfl]
      change (singleV D.host.F w 1) w = 1
      exact RestrictedProduct.single_eq_same _ _ _
    · rw [if_neg hwv]
      change (singleV D.host.F v 1) w = 0
      exact RestrictedProduct.single_eq_of_ne (fun u : Pl D => u.adicCompletionIntegers D.host.F)
        (1 : Fv D.host.F v) hwv
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

theorem parts_pairA (α : Af D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
        evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have ha : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨?_, fun w => ?_⟩
  · rw [ha]
    change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  · exact (placeIdempotent_infinite_and_finite_components D w _ α rfl).2 w

open Classical in
theorem parts_idemQ (Q : Finset (Pl D)) :
    infPart D (algebraMap (AF D.host.F) (AE D) (idemQ D Q)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (idemQ D Q)) = if w ∈ Q then 1 else 0 := by
  refine ⟨(parts_pairA _).1, fun w => ?_⟩
  rw [idemQ, (parts_pairA _).2 w, evalV_indQ]
  split_ifs
  · rfl
  · exact TensorProduct.zero_tmul _ _

open Classical in
theorem parts_idemQc (Q : Finset (Pl D)) :
    infPart D (algebraMap (AF D.host.F) (AE D) (idemQc D Q)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (idemQc D Q)) = if w ∈ Q then 0 else 1 := by
  refine ⟨(parts_pairA _).1, fun w => ?_⟩
  rw [idemQc, (parts_pairA _).2 w, map_sub, map_one, evalV_indQ]
  split_ifs
  · rw [sub_self]; exact TensorProduct.zero_tmul _ _
  · rw [sub_zero]; rfl

theorem mem_idAt_iff_mul (P : Pl D → Prop) [DecidablePred P] (c : AE D) (h0 : infPart D c = 0)
    (hc : ∀ w, compAt D w c = if P w then 1 else 0) (a : AE D) : a ∈ idAt D P ↔ c * a = a := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
  constructor
  · rintro ⟨ha0, haw⟩
    rw [← sub_eq_zero]
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]
    · intro w
      rw [RingHom.map_sub, RingHom.map_mul, hc w]
      by_cases h : P w
      · rw [if_pos h, one_mul, sub_self]
      · rw [if_neg h, haw w h, zero_mul, sub_zero]
  · intro ha
    refine ⟨?_, fun w hw => ?_⟩
    · rw [← ha, RingHom.map_mul, h0, zero_mul]
    · rw [← ha, RingHom.map_mul, hc w, if_neg hw, zero_mul]

theorem mem_idOff_iff_mul (P : Pl D → Prop) [DecidablePred P] (c : AE D) (h0 : infPart D c = 0)
    (hc : ∀ w, compAt D w c = if P w then 1 else 0) (a : AE D) : a ∈ idOff D P ↔ c * a = 0 := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  constructor
  · intro ha
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_mul, h0, zero_mul]
    · intro w
      rw [RingHom.map_mul, hc w]
      by_cases h : P w
      · rw [ha w h, mul_zero]
      · rw [if_neg h, zero_mul]
  · intro ha w hw
    have := congrArg (compAt D w) ha
    rwa [RingHom.map_mul, hc w, if_pos hw, one_mul, RingHom.map_zero] at this

open Classical in
theorem mem_idAt_Q_iff (Q : Finset (Pl D)) (a : AE D) :
    a ∈ idAt D (· ∈ Q) ↔ algebraMap (AF D.host.F) (AE D) (idemQ D Q) * a = a :=
  mem_idAt_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (parts_idemQ Q).2 a

open Classical in
theorem mem_idAt_Qc_iff (Q : Finset (Pl D)) (a : AE D) :
    a ∈ idAt D (· ∉ Q) ↔ algebraMap (AF D.host.F) (AE D) (idemQc D Q) * a = a :=
  mem_idAt_iff_mul (· ∉ Q) _ (parts_idemQc Q).1
    (fun w => by rw [(parts_idemQc Q).2 w]; by_cases h : w ∈ Q <;> simp [h]) a

theorem idemQ_mul_self (Q : Finset (Pl D)) : idemQ D Q * idemQ D Q = idemQ D Q := by
  have e : (idemQ D Q * idemQ D Q : AF D.host.F) = pairA D.host.F 0 (indQ D Q * indQ D Q) :=
    Prod.ext (mul_zero _) rfl
  rw [e, idemQ]
  congr 1
  apply RestrictedProduct.ext
  intro w
  have h := evalV_indQ (D := D) Q w
  change evalV D.host.F w (indQ D Q * indQ D Q) = evalV D.host.F w (indQ D Q)
  rw [map_mul, h]
  split_ifs <;> simp

theorem one_sub_idemQ_mul_self (Q : Finset (Pl D)) :
    (1 - idemQ D Q) * (1 - idemQ D Q) = 1 - idemQ D Q := by
  have h := idemQ_mul_self (D := D) Q
  linear_combination h

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change ((matHom V g).1.map (Ideal.Quotient.mk I)) i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j ↔ _
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, map_zero]
    rfl

def cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) : GA D V →* GA D V :=
  GlobalTheory.UnitaryIdemCut.cutUJ (sigR (AF D.host.F) D.sp.cm.sig) (JR (AF D.host.F) V.gram)
    (algebraMap (AF D.host.F) (AE D) ε) (by rw [← map_mul, hε])
    (GlobalTheory.UnitaryIdemCut.sigR_algebraMap (AF D.host.F) D.sp.cm.sig ε)

theorem mt_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutG V ε hε g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g +
      (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

end GlobalTheory.FinPl.SetCut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

noncomputable section
namespace GlobalTheory.HaarR

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def prodR (p : ℕ) (q : GL n k × N k n c p) : R k n c p :=
  ⟨embX c q.1 * (q.2 : GL (n ⊕ Fin c) k), mul_mem (Subgroup.mem_sup_left ⟨q.1, rfl⟩) (Subgroup.mem_sup_right q.2.2)⟩

def prodRFJ (ρ : ℕ) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) : RFJ k n c ρ :=
  ⟨embX c q.1.1 * (q.1.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) q.2,
    mul_mem (Subgroup.mem_sup_right (mul_mem (Subgroup.mem_sup_left ⟨q.1.1, rfl⟩) (Subgroup.mem_sup_right q.1.2.2)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        ((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c ρ).2.2.2.2.2.2.2 (ρ + 1) q.2 (Nat.lt_succ_self ρ)).1))⟩

@[simp] theorem prodR_coe (p : ℕ) (q : GL n k × N k n c p) :
    (prodR p q : GL (n ⊕ Fin c) k) = embX c q.1 * (q.2 : GL (n ⊕ Fin c) k) := rfl

@[simp] theorem prodRFJ_coe (ρ : ℕ) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    (prodRFJ ρ q : GL (n ⊕ Fin c) k) = embX c q.1.1 * (q.1.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) q.2 := rfl

def cjE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (u : N k n c (ρ + 1)) : N k n c (ρ + 1) :=
  ⟨colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹,
    (GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ h1 h2).2 β u u.2⟩

@[simp] theorem cjE_coe (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (u : N k n c (ρ + 1)) :
    (cjE ρ h1 h2 β u : GL (n ⊕ Fin c) k) = colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹ := rfl

end GlobalTheory.HaarR
end
end

