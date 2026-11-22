import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0128
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.NonemptyAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def finP : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

def infP : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

def intA : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

variable {F}

def evF (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom

def ordAt (v : HeightOneSpectrum (𝓞 F)) : Subring (Fv F v ⊗[F] E) :=
  Subring.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def sgT (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] Af F ⊗[F] E :=
  TensorProduct.map (GlobalTheory.AutFunCompare.sgV v) LinearMap.id

def IsIdemOf (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) : Prop :=
  infP F E e = 0 ∧ evF E v (finP F E e) = 1 ∧ ∀ w, w ≠ v → evF E w (finP F E e) = 0

variable {E}

omit [NumberField E] in
theorem evF_sgT_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) : evF E v (sgT E v y) = y := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleV F v a) ⊗ₜ e = _
    rw [GlobalTheory.AutFunCompare.evalV_singleV, Pi.single_eq_same]

omit [NumberField E] in
theorem evF_sgT_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fv F v ⊗[F] E) : evF E w (sgT E v y) = 0 := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul a e =>
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleV F v a) ⊗ₜ e = _
    rw [GlobalTheory.AutFunCompare.evalV_singleV, Pi.single_eq_of_ne h, TensorProduct.zero_tmul]

omit [NumberField E] in
theorem evF_ext {z z' : Af F ⊗[F] E} (h : ∀ v, evF E v z = evF E v z') : z = z' :=
  GlobalTheory.LatticeLocalGlobal.ext_components z z' h

omit [NumberField E] in
theorem evF_finP_incl (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    evF E v (finP F E (inclR (AF F) x)) = inclR (Fv F v) x := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F 1) ⊗ₜ x = (1 : Fv F v) ⊗ₜ x
  rw [map_one, map_one]

omit [NumberField E] in

theorem isIdemOf_algebraMap {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α = 1)
    (h2 : ∀ w, w ≠ v → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w α = 0) :
    IsIdemOf E v (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 α)) := by
  refine ⟨?_, ?_, fun w hw => ?_⟩
  · show (0 : Ainf F) ⊗ₜ (1 : E) = 0
    exact TensorProduct.zero_tmul _ _
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α ⊗ₜ (1 : E) = 1
    rw [h1]; rfl
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w α ⊗ₜ (1 : E) = 0
    rw [h2 w hw]; exact TensorProduct.zero_tmul _ _

variable [StarRing E] (hc : CMData F E) (V : HSpace E)

abbrev lamHat (F : Type) [Field F] [NumberField F] [Algebra F E] (V : HSpace E) :
    AddSubgroup (Fin V.rank → Af F ⊗[F] E) :=
  latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0}

def locMat (v : HeightOneSpectrum (𝓞 F)) : HA (AF F) hc.sig V.gram →* GL (Fin V.rank) (Fv F v ⊗[F] E) :=
  (Formalism.UG.bc (evF E v)).comp ((Formalism.UG.bc (finP F E)).comp (HR (AF F) hc.sig V.gram).subtype)

def Supp (f : AF F ⊗[F] E) (g : HA (AF F) hc.sig V.gram) : Prop :=
  ∀ i j, f * ((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j = ((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j

def IsFin (g : HA (AF F) hc.sig V.gram) : Prop :=
  Formalism.UG.bc (infP F E) (HA.mat (AF F) hc.sig V.gram g) = 1

def Stab (g : HA (AF F) hc.sig V.gram) : Prop :=
  ∀ y, y ∈ lamHat F V ↔ (finMat hc.sig V.gram g).mulVec y ∈ lamHat F V

def DivG (e : AF F ⊗[F] E) (ϖ : E) (d : Fin V.rank → ℤ) (α : HA (AF F) hc.sig V.gram) : Prop :=
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E),
    (∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → (fun a => finP F E e * B.mulVec z a) ∈ lamHat F V) ∧
    (∀ y ∈ lamHat F V, ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
      (fun a => finP F E e * y a) = fun a => finP F E e * B.mulVec z a) ∧
    (∀ y ∈ lamHat F V, ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
      (fun a => finP F E e * (finMat hc.sig V.gram α).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a) ∧
    (∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → ∃ y ∈ lamHat F V,
      (fun a => finP F E e * (finMat hc.sig V.gram α).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a)

theorem locMat_val (v : HeightOneSpectrum (𝓞 F)) (g : HA (AF F) hc.sig V.gram) :
    (locMat hc V v g).1 = (finMat hc.sig V.gram g).map (evF E v) := rfl

theorem locMat_mem (v : HeightOneSpectrum (𝓞 F)) (g : HA (AF F) hc.sig V.gram) :
    locMat hc V v g ∈ HR (Fv F v) hc.sig V.gram :=
  (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projLoc hc V v (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V g)).2

theorem mem_lamHat_iff (y : Fin V.rank → Af F ⊗[F] E) :
    y ∈ lamHat F V ↔ ∀ v, (fun i => evF E v (y i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v :=
  GlobalTheory.LatticeLocalGlobal.mem_latHat_iff F E V y

def IsFrameAt (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) : Prop :=
  ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ ∀ i, (h⁻¹).1.mulVec x i ∈ ordAt E v

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing
open GlobalTheory.SelfDualGenus

theorem mem_ordAt_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (z : LocAlg v) :
    z ∈ ordAt E v ↔ z ∈ locOrder v := by
  constructor
  · intro hz
    refine (Subring.closure_le (t := (locOrder v).toSubring)).2 ?_ hz
    rintro _ ⟨a, ha, x, rfl⟩
    have := mul_mem ((locOrder v).algebraMap_mem ⟨a, ha⟩) (locEmb_mem_locOrder v x)
    have e : algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (LocAlg v) ⟨a, ha⟩ * locEmb v (x : E) =
        a ⊗ₜ (x : E) := by
      show (a ⊗ₜ 1 : LocAlg v) * (1 ⊗ₜ (x : E)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e] at this
    exact this
  · intro hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Subring.subset_closure ⟨1, one_mem _, a, rfl⟩
    | algebraMap r => exact Subring.subset_closure ⟨r, r.2, 1, rfl⟩
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy

theorem unramified (hc : CMData (maximalRealSubfield E) E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem exists_orthonormal (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ h : GL (Fin V.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E), IsFrameAt V v h ∧
      Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) h.1 * JR (Fv (maximalRealSubfield E) v) V.gram * h.1 = 1 := by
  haveI := unramified hc
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (V.gramᵀ a b) = V.gramᵀ b a :=
    fun a b => V.herm.eq (V.frame b) (V.frame a)
  have hd : V.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame hG hd
    (GlobalTheory.LocalConjugacy.isLattice_coordLat V V.L0 V.standardTuple_isLattice)
    (GlobalTheory.LocalConjugacy.selfDual_coordLat V V.L0 V.baseLattice_isUnimodular) v
  refine ⟨h, fun x => (GlobalTheory.LocalConjugacy.mem_latLoc_iff V v x).trans ((h2 x).trans
    (forall_congr' fun i => (mem_ordAt_iff v _).symm)), ?_⟩
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.transpose_one] at h3
  exact h3

end CM

end GlobalTheory.PlaceComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceBelowCMFieldOfSqrtNegPrimeStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplitPlaceBelowCMField_of_sqrt_neg_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L), 0 < p → δ ^ 2 = -(p : L) → ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 → ∀ w : HeightOneSpectrum (𝓞 L), (q : 𝓞 L) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
  first | exact @GlobalTheory.SplitOfNegPrime.isSplitAt | exact GlobalTheory.SplitOfNegPrime.isSplitAt | (intros; apply GlobalTheory.SplitOfNegPrime.isSplitAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLine
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLine

theorem isUnit_of_stable_line : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l),
  (∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB) → GlobalTheory.RegularRing.LineUnit (P.PD K) →
  ∀ b : Bst P, b ≠ 0 → (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b := by
  intro l _ P _ K hno hLU b hb hst
  unfold GlobalTheory.RegularRing.LineUnit at hLU
  haveI : CharZero P.R.B := charZero_of_injective_algebraMap (algebraMap ℚ_[l] P.R.B).injective

  have hact : ∀ (g : GQ l) (p : Bst P),
      actSt P g p = stHom P (P.actQ g) (X + C ((kummer P g : ℚ_[l]) • P.tB)) p := fun g p => rfl

  have hder : ∀ (g : GQ l) (p : Bst P), derivative (actSt P g p) = actSt P g (derivative p) := by
    intro g p
    rw [hact, hact, derivative_stHom]
    simp
  have hiter : ∀ (k : ℕ) (g : GQ l) (p : Bst P),
      actSt P g (derivative^[k] p) = derivative^[k] (actSt P g p) := by
    intro k g
    induction k with
    | zero => intro p; rfl
    | succ k ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hder]

  have heig : ∀ (k : ℕ) (g : ↥(GK K)), ∃ x : ℚ_[l],
      actSt P (g : GQ l) (derivative^[k] b) = algebraMap ℚ_[l] (Bst P) x * derivative^[k] b := by
    intro k g
    obtain ⟨x, hx⟩ := hst g
    refine ⟨x, ?_⟩
    rw [hiter, hx, Polynomial.algebraMap_apply, iterate_derivative_C_mul]

  have hlin : ∀ p : Bst P, p.natDegree ≤ 1 → p.coeff 1 ≠ 0 →
      (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) p = algebraMap ℚ_[l] (Bst P) x * p) → False := by
    intro p hp1 hp0 hpe
    obtain ⟨u, v, rfl⟩ : ∃ u v, p = C u * X + C v := ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one hp1⟩
    have hu0 : u ≠ 0 := by simpa using hp0
    have hco : ∀ (g : GQ l), g ∈ GK K → ∃ x : ℚ_[l],
        P.actQ g u = algebraMap ℚ_[l] P.R.B x * u ∧
        P.actQ g u * ((kummer P g : ℚ_[l]) • P.tB) + P.actQ g v = algebraMap ℚ_[l] P.R.B x * v := by
      intro g hg
      obtain ⟨x, hx⟩ := hpe ⟨g, hg⟩
      refine ⟨x, ?_, ?_⟩
      · have h1 := congrArg (fun q => Polynomial.coeff q 1) hx
        simpa [Polynomial.algebraMap_apply, mul_add] using h1
      · have h0 := congrArg (fun q => Polynomial.coeff q 0) hx
        simpa [Polynomial.algebraMap_apply, mul_add] using h0
    have hU : IsUnit u := hLU u hu0 (fun g => by
      obtain ⟨x, h1, -⟩ := hco (g : GQ l) g.2
      exact ⟨x, by rw [P.PD_actB]; exact h1⟩)
    obtain ⟨w, hw⟩ : ∃ w, w = v * ↑hU.unit⁻¹ := ⟨_, rfl⟩
    have hwu : w * u = v := by rw [hw, mul_assoc, IsUnit.val_inv_mul, mul_one]
    refine hno (-w) (fun g hg => ?_)
    obtain ⟨x, h1, h0⟩ := hco g hg
    have hne : P.actQ g u ≠ 0 := (hU.map (P.actQ g)).ne_zero
    have key : P.actQ g w * P.actQ g u = (w - (kummer P g : ℚ_[l]) • P.tB) * P.actQ g u := by
      rw [← map_mul, hwu]
      linear_combination h0 - w * h1 - (algebraMap ℚ_[l] P.R.B x) * hwu
    have hgw : P.actQ g w = w - (kummer P g : ℚ_[l]) • P.tB := mul_right_cancel₀ hne key
    rw [map_neg, hgw]
    ring
  by_cases hn : b.natDegree = 0
  · obtain ⟨c, rfl⟩ : ∃ c, b = C c := ⟨_, eq_C_of_natDegree_eq_zero hn⟩
    apply IsUnit.map C
    refine hLU c (fun h => hb (by rw [h, C_0])) (fun g => ?_)
    obtain ⟨x, hx⟩ := hst g
    refine ⟨x, ?_⟩
    rw [P.PD_actB]
    rw [actSt_C, Polynomial.algebraMap_apply, ← C_mul] at hx
    exact C_injective hx
  · exfalso
    apply hlin (derivative^[b.natDegree - 1] b)
    · have := natDegree_iterate_derivative b (b.natDegree - 1)
      omega
    · rw [coeff_iterate_derivative, show 1 + (b.natDegree - 1) = b.natDegree by omega]
      refine smul_ne_zero ?_ (leadingCoeff_ne_zero.mpr hb)
      intro h
      rw [Nat.descFactorial_eq_zero_iff_lt] at h
      omega
    · exact heig (b.natDegree - 1)

end GlobalTheory.Pst.StLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerPEqSpanBeta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem ker_localizedTheta_eq_span_beta : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    Per.kerP l = Ideal.span {beta ϖ} := by
  intro l _ ϖ hϖ
  obtain ⟨_, _, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  have hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := (hK ϖ hϖ).1
  obtain ⟨-, hker, hA, -⟩ := thetaP_facts l
  have hu := GlobalTheory.RingBasics.isUnit_l l
  have hmem : ∀ a : Per.Ainf l, Per.θ l a = 0 →
      algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := by
    intro a ha
    rw [← hker, RingHom.mem_ker, hA, ha]
    rfl
  have h0 : Per.θ l (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) = 0 := by
    have : ((l : ℕ) : Per.Ainf l) - Per.tm ϖ ∈ RingHom.ker (Per.θ l) := by
      rw [hk]; exact Ideal.mem_span_singleton_self _
    exact this
  have hlb : ((l : ℕ) : Per.AinfP l) * beta ϖ =
      -algebraMap (Per.Ainf l) (Per.AinfP l) (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) := by
    rw [l_mul_beta, map_sub, map_natCast]; ring
  refine le_antisymm (fun y hy => ?_) ?_
  · rw [← hker, RingHom.mem_ker] at hy
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    rw [map_natCast] at h
    have ha : Per.θ l a = 0 := by
      apply Subtype.ext
      rw [← hA, ← h, map_mul, hy, zero_mul]
      rfl
    have h2 : a ∈ Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hk ▸ ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h2
    rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h, map_mul]
    have : algebraMap (Per.Ainf l) (Per.AinfP l) (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) =
        -(((l : ℕ) : Per.AinfP l) * beta ϖ) := by rw [hlb, neg_neg]
    rw [this]
    exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · rw [Ideal.span_singleton_le_iff_mem]
    have h3 : ((l : ℕ) : Per.AinfP l) * beta ϖ ∈ Per.kerP l := by
      rw [hlb]; exact neg_mem (hmem _ h0)
    have h4 : linv l * (((l : ℕ) : Per.AinfP l) * beta ϖ) = beta ϖ := by
      rw [← mul_assoc, mul_comm (linv l), mul_linv, one_mul]
    rw [← h4]
    exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.Pst.StLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalBasisUnitScalarsExist
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory

theorem locBasisW_clear_den : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ρ : D.host.E →+* ℂ_[p]) (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : Matrix (Fin N) (Fin N) D.host.E) (P' : Matrix (Fin N') (Fin N') D.host.E), L₁.FG → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → TaylorLogMetric.LocBasisW D ρ L P → TaylorLogMetric.LocBasisW D ρ L' P' → ∃ σ σ' : 𝓞 D.host.E, ‖ρ (σ : D.host.E)‖ = 1 ∧ ‖ρ (σ' : D.host.E)‖ = 1 ∧ (∀ (a : Fin N) (x : Fin N → D.host.E), x ∈ L₁ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = (σ : D.host.E) * ∑ j, P⁻¹ a j * x j) ∧ ∀ b : Fin N', (fun i => (σ' : D.host.E) * P' i b) ∈ L₁' := by
  first
  | exact @_root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers
  | exact _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers
  | (apply _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeUnitMultipliers.exists_unit_multipliers ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTransportIsometryStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalisation_transport_isometry : ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)), IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h (Λ.comap φ.toLinearMap.toAddMonoidHom) (fun z => θ (φ z)) p ι := by
  first | exact @GlobalTheory.ThLoc.LocPull.locNorm_pull | exact GlobalTheory.ThLoc.LocPull.locNorm_pull | (intros; apply GlobalTheory.ThLoc.LocPull.locNorm_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
section
noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def intMat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) L) where
  carrier := {u | ∀ i j, u i j ∈ Formalism.UG.intL L}
  zero_mem' := fun _ _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i j => (Formalism.UG.intL L).add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => (Formalism.UG.intL L).neg_mem (ha i j)

def intVec (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a : ℕ) : AddSubgroup (Fin a → L) where
  carrier := {u | ∀ i, u i ∈ Formalism.UG.intL L}
  zero_mem' := fun _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i => (Formalism.UG.intL L).add_mem (ha i) (hb i)
  neg_mem' := fun ha i => (Formalism.UG.intL L).neg_mem (ha i)

theorem mem_intMat {a b : ℕ} (u : Matrix (Fin a) (Fin b) L) : u ∈ intMat L a b ↔ ∀ i j, u i j ∈ Formalism.UG.intL L := Iff.rfl

theorem mem_intVec {a : ℕ} (u : Fin a → L) : u ∈ intVec L a ↔ ∀ i, u i ∈ Formalism.UG.intL L := Iff.rfl

def latIdx {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) : ℕ :=
  Nat.card (Set.range fun u : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a))

end GlobalTheory.Hk3.HoweDuality

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormLeOneHostBaseModuleAtD
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.IntegralAtPlace

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := ℂ_[p])).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (φ : D.host.E →+* ℂ_[p]) (a : D.host.E), a ∈ D.host.AA0 → ‖φ a‖ ≤ 1 := by
  intro D p hpF hpd φ a ha
  obtain ⟨-, -, hqd, -, hd2⟩ := hypOdd_of_hostHyp D.host.hyp
  have hint : ∀ y : 𝓞 D.host.E, ‖φ (y : D.host.E)‖ ≤ 1 := fun y => by
    have h : IsIntegral ℤ (φ (y : D.host.E)) := by
      obtain ⟨f, hf, hx⟩ := RingOfIntegers.isIntegral_coe y
      refine ⟨f, hf, ?_⟩
      have := congrArg φ hx
      rw [Polynomial.hom_eval₂, map_zero] at this
      rwa [RingHom.ext_int (φ.comp (algebraMap ℤ D.host.E)) (algebraMap ℤ ℂ_[p])] at this
    exact norm_le_one_of_isIntegral h
  let Q : Ideal (𝓞 D.host.E) :=
    { carrier := {y | ‖φ (y : D.host.E)‖ < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        rw [norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hint c)) hx }
  have hmem : ∀ y, y ∈ Q ↔ ‖φ (y : D.host.E)‖ < 1 := fun y => Iff.rfl
  haveI hQ : Q.IsPrime := by
    refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
    · have h1 := (hmem 1).1 (h ▸ Submodule.mem_top)
      simp at h1
    · rw [hmem, show ((x * y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) * y from rfl, map_mul,
        norm_mul] at hxy
      by_contra hc
      push_neg at hc
      rw [hmem, hmem, not_lt, not_lt] at hc
      have := mul_le_mul hc.1 hc.2 zero_le_one (norm_nonneg _)
      linarith
  have hpQ : (p : 𝓞 D.host.E) ∈ Q := by
    rw [hmem]
    have e : ((p : 𝓞 D.host.E) : D.host.E) = (p : D.host.E) := by simp
    rw [e, map_natCast]
    have : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨z, hz, hden⟩ := GlobalTheory.AAUnitAway.exists_den D Q hpF.out (by rw [hpd]; exact UpperTheory.Small.d_not_mem D.host)
    (by rw [hpd]; exact hqd.symm) hpQ
  have hz1 : ‖φ (z : D.host.E)‖ = 1 := le_antisymm (hint z) (not_lt.1 ((hmem z).not.1 hz))
  obtain ⟨w, hw⟩ := hden a ha
  have := hint w
  rwa [hw, map_mul, norm_mul, hz1, mul_one] at this

end GlobalTheory.IntegralAtPlace
end

