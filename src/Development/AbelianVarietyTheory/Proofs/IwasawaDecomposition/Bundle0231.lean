import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFrames
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Formalism.LocalToGlobal.Columns.Bundle0002
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0129
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.JoinForms
import Formalism.LocalToGlobal.Columns.RecLevelSymF

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRef

variable {D : D7} {S T : HSp D} {r g : ℕ}

def IsSet (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hr : T.rank = r) (X : Data D.host.E r)
    (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) : Prop :=
  IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ S.gram = 1 ∧ Even S.rank ∧ ModelW T hr X ∧ X.κ0 = -(2 * D.host.xi0) ∧
    (∀ ρ, (eT ρ).1 = tauE D ρ) ∧ IsSympl X bas

abbrev Fam (T : HSp D) : Type := D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ

def negM (T : HSp D) (q : ℕ) : Matrix (Fin T.rank) (Fin T.rank) ℂ :=
  Matrix.diagonal fun a : Fin T.rank => ((-(sgn q (a : ℕ)) : ℝ) : ℂ)

def IsONeg (T : HSp D) (q : ℕ) (Z : Fam T) : Prop := ∀ ρ, (Z ρ)ᴴ * gramAt D T ρ * Z ρ = negM T q

def cartZ (T : HSp D) (q : ℕ) (Z : Fam T) : Fam T := fun ρ => Z ρ * negM T q * (Z ρ)⁻¹

def mvZ (θ : InfFam D) (h : GA D T) (Z : Fam T) : Fam T := fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * Z ρ

def frOf (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) (Z : Fam T) : Frame X.Ψ r :=
  fun τ a b => Z (eT.symm τ) (Fin.cast hr.symm a) (Fin.cast hr.symm b)

def rePt (θ : InfFam D) (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) (w : WO S T) :
    Ker.WR X S.rank :=
  fun τ k a => compAt θ (eT.symm τ) w (Fin.cast hr.symm a) k

def Zak (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hr : T.rank = r) {X : Data D.host.E r}
    (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (φ : TF S.rank g) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ w, Ker.IsRealPt w → f w = Ker.thR X bas idx φ x (rePt θ hr eT w)

def finR (S : HSp D) (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) : WO S T :=
  Ker.finW S T (y.submatrix id (Fin.cast hr))

def latW (hr : T.rank = r) (L : Lt D.host.E r) : Lt D.host.E T.rank :=
  L.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr.symm))

def toP (S : HSp D) (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) {q0 : ℕ} (hq : X.p0 + q0 = r) :
    MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] Harm.Poly ℂ X.Ψ q0 X.p0 (Fin S.rank) :=
  MvPolynomial.aeval fun v => MvPolynomial.C (((2 / fockScale D v.1 : ℝ) : ℂ)) *
    MvPolynomial.X (eT v.1, (rowIdx hq).symm (Fin.cast hr v.2.1), v.2.2)

def fv (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (q : ℕ) (Z : Fam T) (f : WO S T → ℂ)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) : WO S T → ℂ :=
  pureTensorO ψ θ S T (fun _ => 1) (cartZ T q Z) (fun _ => 1) Z f Q

def ctxOf {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hn : Even S.rank)
    (X' : Data D.host.E T.rank) (m : Ker.Match S T X') {q : ℕ} (hq : X'.p0 + q = T.rank)
    (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin T.rank) (hs : IsSympl X' bas') : Ker.Ctx S T :=
  ⟨ψ, hψ, θ, hθ, X', m, g, q, hq, bas', idx', hs, hn⟩

section Geo

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

def MarkAd (hr : T.rank = r) (l : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)) (h : GA D T)
    (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat T h,
    finVec T (mk a ∘ Fin.cast hr) - (finHom T h).1.mulVec (finVec T (ι a)) = (l.M : ℕ) • w

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

def Matched (c : Coeff l) (σ : c.F →+* ℂ) (X : Data D.host.E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) : Prop :=
  (∀ x v j, pv X idx x v j = perFr X x v (relab c σ (e j).1) (e j).2) ∧ ∀ j, rowType X (idx j) = relab c σ (e j).1

abbrev ptC (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) : @FrPt D.host.E _ _ _ H Dw l Xo c ℂ _ σ.toAlgebra :=
  unC (Formalism.L2.PjFree.Unf.ofPj U) k x

def FrConst (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S : HSp D) (hr : T.rank = r)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f₀ : WO S T → ℂ) (U : Unf Xo c σ r)
    (dict : GA D T → Σ k, Frame (U.X k).Ψ r) (mu : GA D T → ℂ) (Z₀ : Fam T) (cc : U.Comp → ℂ) : Prop :=
  ∀ (h γ : GA D T), γ ∈ GQ T → ∀ (g : ℕ) (eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw),
    IsSet ψ θ S T hr (U.X (dict h).1) eT bas → Matched c σ (U.X (dict h).1) idx e →
    (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀) → ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom),
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩))
      (th : (Fin g → ℂ) → ℂ), A.Reads 1 (ptC U (dict h).1 ⟨(dict h).2, hx⟩).s th →
      ∀ w : WO S T, Ker.IsRealPt w →
        om (1, γ * h) f₀ w = cc (dict h).1 * mu h *
          (Ker.gaussR (U.X (dict h).1) bas idx (dict h).2 (Ker.zR (U.X (dict h).1) idx (dict h).2 (rePt θ hr eT w)) *
            ∏ b, th (Ker.zR (U.X (dict h).1) idx (dict h).2 (rePt θ hr eT w) b))

section Field

variable {c' : Coeff l} {hle : c.F ≤ c'.F} [Algebra c.F ℂ] [Algebra c'.F ℂ] (hA : AlgOver c c' hle ℂ) {X : Data D.host.E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
  {L : Lt D.host.E r} {y : FrPt Xo c ℂ}

def fibExt (A : AnFib X bas idx e x L y) : AnFib X bas idx e x L (y.ext hle hA) :=
  ⟨A.ex, A.ex_add, A.ex_onto, A.ex_ker, A.ex_lin, A.hol, A.der, A.fr, A.fr_hol, A.fr_ne, A.fr_g, A.fr_0, A.χ, A.χ_norm,
    A.fr_per⟩

end Field

end Geo

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev baseZ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    Fam (Wc D i) := x0Mat (R.MW i (sg0 D A))

def FrConstAt {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) : Prop :=
  FrConst R.ψ R.θ (Vc D i) (rank_Wc i) (R.ωP i A.μ0) (R.vacP i) (C.U ((i : ℕ) + 1) O.s0)
    O.dict O.mu (baseZ R i) cc

end Rec

end GlobalTheory.OneMapRef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZero
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.FibProp

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem form_eq (x y : Fin n → A) :
    Formalism.UG.hform s J x y = dotProduct (fun i => s (x i)) (J.mulVec y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_mulVec {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT s g * J * g = J) (x y : Fin n → A) :
    Formalism.UG.hform s J (g.mulVec x) (g.mulVec y) = Formalism.UG.hform s J x y := by
  have e : (fun i => s (g.mulVec x i)) = Matrix.vecMul (fun i => s (x i)) (Formalism.UG.cT s g) := by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, mul_comm]
  rw [form_eq, form_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem form_smul (a : A) (x : Fin n → A) :
    Formalism.UG.hform s J (a • x) (a • x) = s a * a * Formalism.UG.hform s J x x := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem det_norm {g : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) (hg : Formalism.UG.cT s g * J * g = J) :
    g.det * s g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at h
  apply hJ.mul_left_cancel
  linear_combination h

theorem lrAct_one (g : Matrix (Fin n) (Fin n) A) {k : ℕ} (X : Fin k → Fin n → A) :
    lrAct g 1 X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

end Alg

section Q

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem sig_alg (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sig_incl (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem q_scale (r : R) (z : Fin M → R ⊗[F] E) :
    qR R σ J (algebraMap R (R ⊗[F] E) r • z) = r * r * qR R σ J z := by
  unfold qR hR
  rw [form_smul, sig_alg, ← map_mul, ← Algebra.smul_def (r * r), map_smul, smul_eq_mul]
  ring

theorem q_rat [CharZero F] (h2 : Module.finrank F E = 2) (x : Fin M → E) (β : F)
    (hx : hE σ J x x = algebraMap F E β) :
    qR R σ J (fun i => inclR R (x i)) = algebraMap F R β := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have e : hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (x i)) = inclR R (hE σ J x x) := by
    simp only [hR, hE, Formalism.UG.hform, JR, Matrix.map_apply, sig_incl, map_sum, map_mul]
    rfl
  have e2 : inclR R (algebraMap F E β) = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  unfold qR
  rw [e, hx, e2, Algebra.trace_algebraMap_of_basis
    (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2))]
  simp only [Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ← map_natCast (algebraMap F R), ← map_mul]
  norm_num

theorem q_cont [TopologicalSpace R] [FiniteDimensional F E] [IsTopologicalRing R] :
    Continuous (qR R σ J) := by
  have hs : Continuous (sigR R σ) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  have ht : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  unfold qR hR Formalism.UG.hform
  fun_prop

end Q

theorem fibre_invariant_orbit_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 M) ν (algebraMap F R β) m → IsInvTup R σ J m ∧ OnOrbit R σ J x m ∧ m ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ _ _ _ _ hN M J x β lam ν m hJ hβ hx hlam hν hm
  have hu : IsUnit (algebraMap F R β) := (IsUnit.mk0 β hβ).map _
  have hq : qR R σ J (ratTup (F := F) R x 0) = algebraMap F R β := q_rat R σ J hCM.2.2.1 (x 0) β hx
  obtain ⟨hsupp, -, huniq⟩ := GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hN M J _ ν _ m hν hu hm
  have h1 : modu R 1 = 1 := (GlobalTheory.GaugeEx.modu_basic R).2.2.1
  refine ⟨fun g => ?_, ?_, ?_⟩
  · set G : Matrix (Fin M) (Fin M) (R ⊗[F] E) := (HA.mat R σ J g).val with hG
    have hg : Formalism.UG.cT (sigR R σ) G * JR R J * G = JR R J := g.2
    have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).1 (HA.mat R σ J g).isUnit
    have hJu : IsUnit (JR (F := F) R J).det := by
      unfold JR
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (IsUnit.mk0 _ hJ.2).map _
    have hm1 : modu (R ⊗[F] E) G.det = 1 := by
      rw [(GlobalTheory.T.haarModulus_tensor_eq_modulus_norm F E σ hCM R G.det 1 hd (by rw [map_one, det_norm _ _ hJu hg])).2, h1]
    have := GlobalTheory.T.fibreMeasures_transport_unitary_similitude F E σ R hN M J J lam ν _ 1 m G hlam hν hd isUnit_one
      (fun z => by rw [one_mul]; unfold qR hR; rw [form_mulVec _ _ hg]) hm
    rw [one_mul, hm1, h1, inv_one, mul_one, one_smul] at this
    have e : lrAct G 1 = fun X : Fin 1 → Fin M → R ⊗[F] E => g • X := by
      funext X; rw [lrAct_one]; rfl
    rw [e] at this
    exact huniq _ this
  · refine measure_mono_null (fun y hy => ?_) hsupp
    exact fun h => hy (GlobalTheory.T.cmExtension_localFieldProductRing_exists_smul_eq F E σ hCM R hN M J hJ _ _ y hu hq h)
  · rintro rfl
    obtain ⟨-, -, hO, U, hU, h1U, s, -, -, hs⟩ := id hN
    obtain ⟨fib, hfib, -⟩ := id hm
    obtain ⟨w, hw⟩ := hu
    let T : Set R := {b | IsUnit b} ∩ (fun b => b * (↑w⁻¹ : R)) ⁻¹' U
    have hT : IsOpen T := by
      refine IsOpen.inter ?_ (hU.preimage (by fun_prop))
      exact hO.isOpenEmbedding_unitsVal.isOpen_range
    have hz : ∀ b ∈ T, fib b = 0 := by
      rintro b ⟨hb, hbU⟩
      set r := s (b * (↑w⁻¹ : R))
      have hr : r * r = b * (↑w⁻¹ : R) := hs _ hbU
      have hrr : IsUnit (r * r) := hr ▸ IsUnit.mul hb (Units.isUnit _)
      have hru : IsUnit r := isUnit_of_mul_isUnit_left hrr
      have := GlobalTheory.T.fibreMeasures_transport_unitary_similitude F E σ R hN M J J lam ν _ (r * r) 0
        (algebraMap R (R ⊗[F] E) r • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hlam hν
        (by rw [Matrix.det_smul, Matrix.det_one, mul_one]; exact (hru.map _).pow _) hrr
        (fun z => by rw [Matrix.smul_mulVec, Matrix.one_mulVec, q_scale]) hm
      rw [Measure.map_zero, smul_zero, hr, ← hw, Units.inv_mul_cancel_right] at this
      exact (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hN M J _ ν _ 0 hν hb this).2.2 _ ⟨fib, hfib, rfl⟩
    let O : Set (Fin 1 → Fin M → R ⊗[F] E) := (fun X => qR R σ J (X 0)) ⁻¹' T
    have hOo : IsOpen O := hT.preimage ((q_cont R σ J).comp (continuous_apply 0))
    have hne : O.Nonempty := ⟨ratTup (F := F) R x, by
      show qR R σ J (ratTup (F := F) R x 0) ∈ T
      rw [hq, ← hw]
      exact ⟨w.isUnit, by simpa using h1U⟩⟩
    have key := hfib.2.1 (O.indicator 1) (measurable_one.indicator hOo.measurableSet)
    have hz' : ∀ b, fib b O = 0 := by
      intro b
      by_cases hb : b ∈ T
      · rw [hz b hb]; rfl
      · refine measure_mono_null (fun y hy => ?_) (hfib.1 b)
        intro h
        apply hb
        have : qR R σ J (y 0) = b := h.1
        rw [← this]; exact hy
    simp only [Measure.restrict_univ, lintegral_indicator_one hOo.measurableSet, hz',
      lintegral_zero] at key
    haveI : (tupMeas lam 1 M).IsOpenPosMeasure := by
      unfold tupMeas
      haveI : (Measure.pi fun _ : Fin M => lam).IsOpenPosMeasure :=
        Measure.pi.isOpenPosMeasure (fun _ : Fin M => lam)
      exact Measure.pi.isOpenPosMeasure (fun _ : Fin 1 => Measure.pi fun _ : Fin M => lam)
    exact (hOo.measure_pos _ hne).ne' key

end GlobalTheory.GaugeEx.FibProp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinPartAlgebraMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocWeil.PlaceIdem

section General

variable (F : Type) [Field F] [NumberField F]

theorem evalV_single_same (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 :=
  RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

theorem evalV_single_ne {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) : evalV F u (singleV F v 1) = 0 :=
  RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

theorem af_ext {a b : Af F} (h : ∀ u, evalV F u a = evalV F u b) : a = b :=
  DFunLike.ext _ _ h

def eFin (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (singleV F v 1)

def eInf (v : InfinitePlace F) : AF F := pairA F (Pi.single v 1) 0

theorem eFin_mul_eFin {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) : eFin F u * eFin F v = 0 := by
  refine Prod.ext (mul_zero _) ?_
  change singleV F u 1 * singleV F v 1 = 0
  refine af_ext F fun w => ?_
  rw [map_mul, map_zero]
  by_cases hw : w = u
  · subst hw
    rw [evalV_single_ne F h, mul_zero]
  · rw [evalV_single_ne F hw, zero_mul]

theorem eFin_mul_eInf (u : HeightOneSpectrum (𝓞 F)) (v : InfinitePlace F) : eFin F u * eInf F v = 0 :=
  Prod.ext (zero_mul _) (mul_zero _)

theorem eInf_mul_eInf {u v : InfinitePlace F} (h : u ≠ v) : eInf F u * eInf F v = 0 := by
  refine Prod.ext ?_ (mul_zero _)
  funext w
  change (Pi.single u 1 : ∀ w : InfinitePlace F, w.Completion) w *
    (Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion) w = 0
  by_cases hw : w = u
  · subst hw
    rw [Pi.single_eq_of_ne h, mul_zero]
  · rw [Pi.single_eq_of_ne hw, zero_mul]

theorem eq_zero_of_idem (a : AF F) (h1 : ∀ v, eFin F v * a = 0) (h2 : ∀ v, eInf F v * a = 0) : a = 0 := by
  refine Prod.ext ?_ ?_
  · funext w
    have h : (Pi.single w 1 : ∀ w : InfinitePlace F, w.Completion) w * a.1 w = 0 :=
      congrFun (congrArg Prod.fst (h2 w)) w
    rw [Pi.single_eq_same, one_mul] at h
    exact h
  · refine af_ext F fun w => ?_
    have h : singleV F w 1 * sndA F a = 0 := congrArg Prod.snd (h1 w)
    have h' := congrArg (evalV F w) h
    rw [map_mul, evalV_single_same, one_mul] at h'
    exact h'

theorem tensor_eq_zero {K E R I : Type} [Field K] [Field E] [Algebra K E] [CommRing R] [Algebra K R] (e : I → R)
    (he : ∀ a : R, (∀ i, e i * a = 0) → a = 0) (x : R ⊗[K] E)
    (hx : ∀ i, algebraMap R (R ⊗[K] E) (e i) * x = 0) : x = 0 := by
  let b := Algebra.TensorProduct.basis R (Module.Free.chooseBasis K E)
  refine b.ext_elem fun j => ?_
  rw [map_zero]
  refine he _ fun i => ?_
  have h := hx i
  rw [← Algebra.smul_def] at h
  have h' := congrArg (fun y => b.repr y j) h
  simpa using h'

theorem sum_single_one : (∑ v : InfinitePlace F, fstA F (eInf F v)) = 1 := by
  change (∑ v : InfinitePlace F, (Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion)) = fun _ => 1
  exact Finset.univ_sum_single (fun w : InfinitePlace F => (1 : w.Completion))

theorem ext_eInf (σ : F →+* ℂ) (v : InfinitePlace F) :
    GlobalTheory.InfAdeleCM.ext σ (fstA F (eInf F v)) = if InfinitePlace.mk σ = v then 1 else 0 := by
  rw [GlobalTheory.InfAdeleCM.ext_apply]
  change InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)
    ((Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion) (InfinitePlace.mk σ)) = _
  split_ifs with h
  · subst h
    rw [Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, map_zero]

end General

def plc (D : D7) (τ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))

theorem plc_bijective (D : D7) : Function.Bijective (plc D) := GlobalTheory.CMTypePlaces.places_bijective D

theorem idem_inl (D : D7) (v : FinF D) :
    idem D (.inl v) = algebraMap (AF D.host.F) (AE D) (eFin D.host.F v) := rfl

theorem idem_inr (D : D7) (τ : D.what₂.Tau) :
    idem D (.inr τ) = algebraMap (AF D.host.F) (AE D) (eInf D.host.F (plc D τ)) := rfl

theorem infPart_algebraMap (D : D7) (a : AF D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) a) = fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem finPart_algebraMap (D : D7) (a : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) a) = sndA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem idem_props : ∀ D : D7, (∀ v v' : Pl D, v ≠ v' → idem D v * idem D v' = 0) ∧ (∀ θ : InfF D, IsInfFam θ → ∀ τ τ', θ τ' (infPart D (idem D (.inr τ))) = if τ' = τ then 1 else 0) ∧ (∀ τ, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ, idem D (.inr τ)) = 1 ∧ (∀ v : FinF D, ∃ a, IsPlaceIdem D v a ∧ idem D (.inl v) = algebraMap (AF D.host.F) (AE D) a) ∧ ∀ x : AE D, (∀ v, idem D v * x = 0) → x = 0 := by
  intro D
  have hb := plc_bijective D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (v | τ) (v' | τ') h
    · rw [idem_inl, idem_inl, ← RingHom.map_mul, eFin_mul_eFin _ fun e => h (congrArg _ e), RingHom.map_zero]
    · rw [idem_inl, idem_inr, ← RingHom.map_mul, eFin_mul_eInf, RingHom.map_zero]
    · rw [idem_inr, idem_inl, ← RingHom.map_mul, mul_comm, eFin_mul_eInf, RingHom.map_zero]
    · rw [idem_inr, idem_inr, ← RingHom.map_mul, eInf_mul_eInf _ fun e => h (congrArg _ (hb.1 e)), RingHom.map_zero]
  · intro θ hθ τ τ'
    haveI := D.sp.cm.totReal
    have h := GlobalTheory.InfAdeleCM.hom_tmul (tauE D τ') (θ τ') (hθ τ').1 (hθ τ').2
      (fstA D.host.F (eInf D.host.F (plc D τ))) 1
    rw [RingHom.map_one, mul_one, ext_eInf] at h
    rw [idem_inr, infPart_algebraMap]
    refine h.trans ?_
    exact if_congr (hb.1.eq_iff (a := τ') (b := τ)) rfl rfl
  · intro τ
    rw [idem_inr, finPart_algebraMap]
    exact TensorProduct.zero_tmul _ _
  · have h : (∑ τ, idem D (.inr τ)) =
        algebraMap (AF D.host.F) (AE D) (∑ v : InfinitePlace D.host.F, eInf D.host.F v) := by
      rw [← hb.sum_comp, map_sum (algebraMap (AF D.host.F) (AE D))]
      rfl
    rw [h, infPart_algebraMap, map_sum (fstA D.host.F), sum_single_one]
    rfl
  · intro v
    exact ⟨eFin D.host.F v, ⟨singleV D.host.F v 1, rfl, evalV_single_same _ v, fun v' h => evalV_single_ne _ h⟩, rfl⟩
  · intro x hx
    refine tensor_eq_zero (Sum.elim (eFin D.host.F) fun τ => eInf D.host.F (plc D τ)) (fun a ha => ?_) x ?_
    · refine eq_zero_of_idem _ a (fun v => ha (.inl v)) fun w => ?_
      obtain ⟨τ, rfl⟩ := hb.2 w
      exact ha (.inr τ)
    · rintro (v | τ)
      · exact hx (.inl v)
      · exact hx (.inr τ)

end GlobalTheory.LocWeil.PlaceIdem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact : ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e → (∃ K : Set (NFlag B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NFlagQ B e, ∃ k ∈ K, n = γ * k) ∧ (∃ K : Set (NI B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NIQ B e, ∃ k ∈ K, n = γ * k) := by
  first | exact @GlobalTheory.Mem.UnipCocompact.radicals_cocompact | exact GlobalTheory.Mem.UnipCocompact.radicals_cocompact | (intros; apply GlobalTheory.Mem.UnipCocompact.radicals_cocompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightVectorTransferStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_weight_vector_transfer : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (μ : ι → Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P') (x : P) (x' : P'), IsHolFam ε B ϖ → IsHolFam ε B' ϖ' → IsBotFam ε ϖ μ x → IsBotFam ε ϖ' μ x' → x' ≠ 0 → ∃ ψ : P' →ₗ[ℂ] P, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)) → ψ (ϖ' u x') = ϖ u x := by
  first | exact @GlobalTheory.JointHarm.OrbitMap.exists_orbit_map | exact GlobalTheory.JointHarm.OrbitMap.exists_orbit_map | (intros; apply GlobalTheory.JointHarm.OrbitMap.exists_orbit_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemHJsymIffJSymG
section
open Formalism.L2.Col

namespace GlobalTheory

theorem mem_HJsym_iff_JSymG : ∀ (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n), r = k + 2 * rS + 1 → 0 < t → n = r + m * t →
    ∀ M : GL (Fin n) κ, M ∈ HJsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t false := by
  intro κ _ n k r t m rS h hr ht hn M
  subst hr
  rw [HJsym_eq_JSymG ht (by omega) h]

end GlobalTheory
end

