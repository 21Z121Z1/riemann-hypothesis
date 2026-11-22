import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0202
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0061
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0367
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceActionDeterminant
section
noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise Kronecker

namespace GlobalTheory.CompanionTheory.ConeLin

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hOf_add (v w : Fin n × Fin n → ℝ) : hOf (v + w) = hOf v + hOf w := by
  simp only [hOf, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

theorem hOf_smul (c : ℝ) (v : Fin n × Fin n → ℝ) : hOf (c • v) = (c : ℂ) • hOf v := by
  simp only [hOf, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum, smul_smul]

theorem hOf_single (q : Fin n × Fin n) : hOf (Pi.single q (1 : ℝ)) = hb q := by
  classical
  simp [hOf, Pi.single_apply, ite_smul]

theorem hOf_herm (v : Fin n × Fin n → ℝ) : (hOf v)ᴴ = hOf v := by
  simp [hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]

theorem re_trace (P : Mat n) (hP : Pᴴ = P) (p : Fin n × Fin n) :
    (((P * hb p).trace).re : ℂ) = (P * hb p).trace := by
  apply Complex.conj_eq_iff_re.1
  have h1 : star (P * hb p).trace = (P * hb p).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hP, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose,
      Matrix.trace_mul_comm]
  exact h1

theorem hOf_re (P : Mat n) (hP : Pᴴ = P) : hOf (fun p => ((P * hb p).trace).re) = P := by
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr P
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, re_trace P hP]

theorem conj_herm (g P : Mat n) (hP : Pᴴ = P) : (g * P * gᴴ)ᴴ = g * P * gᴴ := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]

def realMap (g : Mat n) : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) where
  toFun v p := ((g * hOf v * gᴴ * hb p).trace).re
  map_add' v w := by
    funext p
    simp [hOf_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' c v := by
    funext p
    simp [hOf_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

def cplxMap (g : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun X := g * X * gᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem cplxMap_apply (g X : Mat n) : cplxMap g X = g * X * gᴴ := rfl

theorem hOf_realMap (g : Mat n) (v : Fin n × Fin n → ℝ) : hOf (realMap g v) = g * hOf v * gᴴ :=
  hOf_re _ (conj_herm g _ (hOf_herm v))

theorem det_realMap (g : Mat n) : ((LinearMap.det (realMap g) : ℝ) : ℂ) = LinearMap.det (cplxMap g) := by
  rw [← LinearMap.det_toMatrix' (realMap g), ← GlobalTheory.CompanionTheory.TopClass.det_of_trace (cplxMap g),
    ← Matrix.det_transpose (Matrix.of _)]
  have h : ((LinearMap.toMatrix' (realMap g)).det : ℂ) =
      Complex.ofRealHom (LinearMap.toMatrix' (realMap g)).det := rfl
  rw [h, RingHom.map_det]
  congr 1
  ext p q
  have hh : (g * hb q * gᴴ)ᴴ = g * hb q * gᴴ := conj_herm g _ (GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose q)
  have := re_trace _ hh p
  simpa [LinearMap.toMatrix'_apply, realMap, hOf_single, cplxMap_apply, Pi.single_apply] using this

theorem det_cplxMap (g : Mat n) : LinearMap.det (cplxMap g) = (g.det * star g.det) ^ n := by
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)) (Matrix.stdBasis ℂ (Fin n) (Fin n)) (cplxMap g) =
      g ⊗ₖ g.map star := by
    ext ⟨i, j⟩ ⟨k, l⟩
    have hr : ∀ X : Mat n, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr X (i, j) = X i j := by
      intro X
      simp [Matrix.stdBasis]
    rw [LinearMap.toMatrix_apply, hr]
    simp [cplxMap_apply, Matrix.stdBasis_eq_single, Matrix.mul_apply, Matrix.single_apply, ite_and]
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)), h, Matrix.det_kronecker]
  have h2 : (g.map star).det = star g.det := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
    rfl
  rw [h2, Fintype.card_fin, mul_pow]

theorem cone_lin (n : ℕ) (g : Mat n) (_hg : g.det ≠ 0) :
    ∃ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ),
      (∀ v, hOf (T v) = g * hOf v * gᴴ) ∧ LinearMap.det T = ‖g.det‖ ^ (2 * n) := by
  refine ⟨realMap g, hOf_realMap g, ?_⟩
  apply Complex.ofReal_injective
  rw [det_realMap, det_cplxMap]
  have : g.det * star g.det = ((‖g.det‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.mul_conj' g.det
  rw [this, pow_mul]
  simp

end GlobalTheory.CompanionTheory.ConeLin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjective
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg Matrix

namespace GlobalTheory.CompanionTheory.SegNu

theorem exists_ne_zero_of_irr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra h
  push_neg at h
  haveI := hi
  refine (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤) (Subrepresentation.toSubmodule_injective ?_)
  show (⊥ : Submodule ℂ V) = ⊤
  ext v
  simp [h v]

theorem eq_smul_of_eigenvector {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) {z : G} (hz : ∀ g, z * g = g * z) {c : ℂ} {w : V}
    (hw : w ≠ 0) (hc : π z w = c • w) (v : V) : π z v = c • v := by
  haveI := hi
  let E : Subrepresentation π :=
    { toSubmodule := LinearMap.ker (π z - c • (1 : Module.End ℂ V))
      apply_mem_toSubmodule := fun g v hv => by
        have hv' : π z v = c • v := by
          simpa [sub_eq_zero] using hv
        have h1 : π z (π g v) = π g (π z v) := by
          rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply]
        simp [sub_eq_zero, h1, hv'] }
  have hE : E ≠ ⊥ := fun h => hw (by
    have h1 : w ∈ E.toSubmodule := by
      show w ∈ LinearMap.ker (π z - c • (1 : Module.End ℂ V))
      simp [sub_eq_zero, hc]
    rw [h] at h1
    exact (Submodule.mem_bot ℂ).1 h1)
  have hT : E = ⊤ := (eq_bot_or_eq_top E).resolve_left hE
  have h2 : v ∈ E.toSubmodule := by
    rw [hT]
    exact Submodule.mem_top
  have h3 : v ∈ LinearMap.ker (π z - c • (1 : Module.End ℂ V)) := h2
  simpa [sub_eq_zero] using h3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_scalar {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
    (ha : IsAdmissible π) (hi : π.IsIrreducible) {z : GL (Fin n) k} (hz : ∀ g, z * g = g * z) :
    ∃ ω : ℂ, ∀ v, π z v = ω • v := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_irr hi
  let S : Subgroup (GL (Fin n) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} ha hb => by
        have ha' : π a v = v := ha
        have hb' : π b v = v := hb
        show π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show π 1 v = v
        simp
      inv_mem' := fun {a} ha => by
        have ha' : π a v = v := ha
        show π a⁻¹ v = v
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSo : IsOpen (S : Set (GL (Fin n) k)) := ha.1 v
  let K : Subgroup (GL (Fin n) k) := S ⊓ KO k (Fin n)
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := hSo.inter SplitFlip.isOpen_KO
  have hKc : IsCompact (K : Set (GL (Fin n) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (K.isClosed_of_isOpen hKo) Set.inter_subset_right
  haveI : FiniteDimensional ℂ (fixed π K) := ha.2 K hKo hKc
  have hvK : v ∈ fixed π K := fun h => by
    have h' : π (h : GL (Fin n) k) v = v := h.2.1
    simpa using h'
  haveI : Nontrivial (fixed π K) := ⟨⟨⟨v, hvK⟩, 0, fun e => hv (congrArg Subtype.val e)⟩⟩
  have hst : ∀ u ∈ fixed π K, π z u ∈ fixed π K := fun u hu h => by
    have hu' := hu h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at hu' ⊢
    rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply, hu']
  let T : Module.End ℂ (fixed π K) := (π z).restrict hst
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have h1 : π z (w : V) = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have h2 : (w : V) ≠ 0 := fun e => hw.2 (Subtype.ext e)
  exact ⟨c, eq_smul_of_eigenvector hi hz h2 h1⟩

theorem eq_zero_of_nu_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (hd : 0 < x.1) {s : ℝ}
    (hs : x.nu (s : ℂ) = x) : s = 0 := by
  have h1 := IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr (absPow k (s : ℂ)) (isSmoothChar_absPow _)
  rw [IrrGL.of_rep] at h1
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 (h1.symm.trans (hs.trans (IrrGL.of_rep x).symm))
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  let z : GL (Fin x.1) k := GeneralLinearGroup.scalar (Fin x.1) ϖ
  have hz : ∀ g, z * g = g * z := fun g => by
    ext i j
    simp [z, GeneralLinearGroup.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have hdet : GeneralLinearGroup.det z = ϖ ^ x.1 := by
    ext
    simp [z, GeneralLinearGroup.scalar]
  obtain ⟨ω, hω⟩ := exists_scalar (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr hz
  obtain ⟨v, hv⟩ := exists_ne_zero_of_irr x.2.rep.irr
  have hω0 : ω ≠ 0 := fun e => hv (by
    have h2 : x.rep z⁻¹ (x.rep z v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [hω, e, zero_smul, map_zero] at h2
    exact h2.symm)
  have h3 := LinearMap.congr_fun (φ.isIntertwining' z) v
  have hLv : φ.toLinearEquiv v ≠ 0 := fun e => hv (φ.toLinearEquiv.map_eq_zero_iff.1 e)
  have h4 : φ.toLinearEquiv (((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) • x.rep z v) = x.rep z (φ.toLinearEquiv v) := by
    have h5 : φ.toLinearEquiv ((twist x.rep (detChar _ (absPow k (s : ℂ)))) z v) = x.rep z (φ.toLinearEquiv v) := h3
    rwa [twist_apply, detChar_apply, hdet] at h5
  rw [hω, hω, map_smul, map_smul, smul_smul] at h4
  have h6 : ((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) * ω = ω := smul_left_injective ℂ hLv h4
  have h7 : ((absPow k (s : ℂ) (ϖ ^ x.1) : ℂˣ) : ℂ) = 1 := mul_right_cancel₀ hω0 (h6.trans (one_mul ω).symm)
  have h8 : ((absPow k (s : ℂ) ϖ : ℂˣ) : ℂ) ^ x.1 = 1 := by
    rw [← h7, map_pow, Units.val_pow_eq_pow_val]
  rw [val_absPow_ofReal] at h8
  have h9 : (nabs k ϖ ^ s) ^ x.1 = 1 := by exact_mod_cast h8
  have hpos : 0 < nabs k ϖ := nabs_pos' k ϖ
  have h10 : nabs k ϖ ^ s = 1 := (pow_eq_one_iff_of_nonneg (Real.rpow_nonneg hpos.le s) hd.ne').1 h9
  have hne : nabs k ϖ ≠ 1 := fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have h11 := congrArg Real.log h10
  rw [Real.log_rpow hpos, Real.log_one] at h11
  exact (mul_eq_zero.1 h11).resolve_right (Real.log_ne_zero_of_pos_of_ne_one hpos hne)

theorem nu_natCast_inj : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (hx : x.IsCusp) (a b : ℕ)
    (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  intro k _ _ _ _ hA x hx a b h
  have h1 : x.nu (((a : ℝ) - (b : ℝ) : ℝ) : ℂ) = x := by
    have h2 := congrArg (fun y => IrrGL.nu y (-(b : ℂ))) h
    simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h2
    rw [← h2]
    congr 1
    push_cast
    ring
  have h3 := eq_zero_of_nu_eq hA x hx.1 h1
  exact_mod_cast sub_eq_zero.1 h3

end GlobalTheory.CompanionTheory.SegNu
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.FineStep

theorem isSubquotient_subQuot_self {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {J : Representation ℂ G V} (S R : Subrepresentation J) : IsSubquotient (subQuot S R) J := by
  refine GlobalTheory.SmGL.IsSubquotient.trans (σ := S.toRepresentation) ?_ ?_
  · refine GlobalTheory.SmGL.IsSubquotient.of_surjective
      ⟨(Submodule.comap S.toSubmodule.subtype R.toSubmodule).mkQ, fun g => ?_⟩ ?_
    · ext v
      rfl
    · exact Submodule.mkQ_surjective _
  · refine GlobalTheory.SmGL.IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun g => ?_⟩ ?_
    · ext v
      rfl
    · exact Subtype.val_injective

theorem nonempty_equiv_of_jhMult_eq_one :
    ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (T : Representation ℂ G W) (J : Representation ℂ G V), T.IsIrreducible → HasFiniteLength J →
      jhMult T J = 1 →
      (∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X), ρ.IsIrreducible →
        IsSubquotient ρ J → Nonempty (ρ.Equiv T)) → Nonempty (J.Equiv T) := by
  intro G V W _ _ _ _ _ T J hT hfin hJ hall
  have hstep : ∀ {P Q : Subrepresentation J}, Q ⋖ P → GlobalTheory.JHMult.Step T P Q := fun {P Q} h =>
    GlobalTheory.JHMult.step_iff.mp
      (hall _ (subQuot P Q) (GlobalTheory.SmGL.isIrreducible_subQuot h) (isSubquotient_subQuot_self P Q))
  have hwf : WellFounded ((· < ·) : Subrepresentation J → Subrepresentation J → Prop) := by
    haveI : IsArtinian (MonoidAlgebra ℂ G) J.asModule :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (show IsFiniteLength (MonoidAlgebra ℂ G) J.asModule from hfin)).2
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := J)).toOrderEmbedding.ltEmbedding.wellFounded
      wellFounded_lt
  have hne : (⊥ : Subrepresentation J) ≠ ⊤ := by
    intro h
    haveI : Subsingleton V := ⟨fun a b => by
      have ha : a ∈ (⊤ : Subrepresentation J).toSubmodule := Submodule.mem_top
      have hb : b ∈ (⊤ : Subrepresentation J).toSubmodule := Submodule.mem_top
      rw [← h] at ha hb
      rw [(Submodule.mem_bot ℂ).mp ha, (Submodule.mem_bot ℂ).mp hb]⟩
    have h0 := GlobalTheory.SmGL.jhMult_of_subsingleton hT J
    rw [hJ] at h0
    exact one_ne_zero h0
  have hirr : J.IsIrreducible := by
    show IsSimpleOrder (Subrepresentation J)
    refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := fun S => ?_ }
    by_contra hS
    obtain ⟨hS0, hS1⟩ := not_or.mp hS
    obtain ⟨A, ⟨hA0, hAS⟩, hAmin⟩ := hwf.has_min {A | ⊥ < A ∧ A ≤ S}
      ⟨S, show ⊥ < S ∧ S ≤ S from ⟨bot_lt_iff_ne_bot.mpr hS0, le_rfl⟩⟩
    obtain ⟨B, hB, hBmin⟩ := hwf.has_min {B | S < B}
      ⟨⊤, show S < ⊤ from lt_top_iff_ne_top.mpr hS1⟩
    have hcA : (⊥ : Subrepresentation J) ⋖ A := ⟨hA0, by
      intro c hc hcA
      exact hAmin c (show ⊥ < c ∧ c ≤ S from ⟨hc, hcA.le.trans hAS⟩) hcA⟩
    have hSB : S < B := hB
    have hcB : S ⋖ B := ⟨hSB, by
      intro c hc hcB
      exact hBmin c (show S < c from hc) hcB⟩
    have hocc : GlobalTheory.SmGL.OccursTimes T J 2 := by
      have := GlobalTheory.JHMult.occurs_of_finset (σ := T) (ρ := J) (r := 2) Finset.univ ![A, B] ![⊥, S]
        (by simp [Fin.forall_fin_two, hSB.le]) (by simp [Fin.forall_fin_two, hAS])
        (by simp [Fin.forall_fin_two, hstep hcA, hstep hcB])
      simpa using this
    have h2 : ((2 : ℕ) : ℕ∞) ≤ GlobalTheory.SmGL.jhMult T J := by
      unfold GlobalTheory.SmGL.jhMult
      exact le_iSup₂_of_le 2 hocc le_rfl
    rw [hJ] at h2
    have h21 : ¬ ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by
      rw [ENat.natCast_le_natCast]
      omega
    exact h21 (by simpa using h2)
  exact hall V J hirr (GlobalTheory.SmGL.IsSubquotient.refl J)

end GlobalTheory.CompanionTheory.FineStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitPowTendstoZero
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocalFieldPow

open ValuativeRel in

theorem exists_unit_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∃ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) := by
  intro k _ _ _ _
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr : r ≠ 0 := by simpa using hr0
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  refine ⟨Units.mk0 r hr, ?_⟩
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hr1 (Units.mk0 γ hγ)
  rw [Units.val_mk0] at hm
  filter_upwards [eventually_ge_atTop m] with n hn
  have h : valuation k ((Units.mk0 r hr : kˣ) : k) ^ n ≤ valuation k r ^ m := by
    simpa using pow_le_pow_of_le_one zero_le' hr1.le hn
  simpa using lt_of_le_of_lt h hm

end GlobalTheory.CompanionTheory.LocalFieldPow
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWeightNilradicalIntegralOneStatement
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_nilradical_integral_one : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure],
  (∀ Y : nilrad W₁ W₂, MeasurePreserving (nmul hW Y) ν ν) →
  ∃ w : GL (Fin n) ℂ → ℝ≥0∞, Measurable w ∧
    ∀ g : GL (Fin n) ℂ, ∫⁻ X, w ((uOf X)⁻¹ * g) ∂ν = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.exists_nilrad_normaliser | exact GlobalTheory.CompanionTheory.LocVan.exists_nilrad_normaliser | (intros; apply GlobalTheory.CompanionTheory.LocVan.exists_nilrad_normaliser <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDeterminingStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_coefficients_finite_determining : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W), ∃ S : Finset K, ∀ c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent | exact GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent | (intros; apply GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatom
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.FiniteLengthQuot

theorem exists_isCoatom_subrepresentation :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      HasFiniteLength ρ → Nontrivial V → ∃ S : Subrepresentation ρ, IsCoatom S := by
  intro G V _ _ _ ρ hfl hnt
  have : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hfl).1
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨M, hM, -⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  exact ⟨M, hM⟩

end GlobalTheory.CompanionTheory.FiniteLengthQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
section
noncomputable section

open NumberField IsDedekindDomain Matrix Topology Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.KerTwFin

section Rational

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem discreteTopology_range : DiscreteTopology (ratGL E n).range :=
  GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n

theorem isClosed_range : IsClosed ((ratGL E n).range : Set (GA E n)) :=
  GroundTheory.Automorphic.AdelicGLn.isClosed_rationalGL E n

theorem injective_ratGL : Function.Injective (ratGL E n) :=
  GroundTheory.Automorphic.AdelicGLn.diagonal_injective E n

theorem finite_ratGL_mem {K : Set (GA E n)} (hK : IsCompact K) : {d : GL (Fin n) E | ratGL E n d ∈ K}.Finite := by
  have hcomp : IsCompact (K ∩ ((ratGL E n).range : Set (GA E n))) := hK.inter_right isClosed_range
  have hdisc : DiscreteTopology ↥(K ∩ ((ratGL E n).range : Set (GA E n))) :=
    DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n))) discreteTopology_range inter_subset_right
  have hfin := hcomp.finite ⟨hdisc⟩
  refine (hfin.preimage (f := ratGL E n) injective_ratGL.injOn).subset fun d hd => ?_
  exact ⟨hd, d, rfl⟩

end Rational

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_thetaA : Continuous (thetaA E n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h0 : Continuous fun g : GA E n => ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) :=
      Units.continuous_coe_inv
    exact (h0.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose
  · have h0 : Continuous fun g : GA E n => (g : Matrix (Fin n) (Fin n) (Ad E)) := Units.continuous_val
    exact (h0.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose

theorem finite_kernel {φ : GA E n → ℂ} (hφ : HasCompactSupport φ) {C C' : Set (GA E n)} (hC : IsCompact C)
    (hC' : IsCompact C') :
    {d : GL (Fin n) E | ∃ x ∈ C, ∃ y ∈ C', φ (x⁻¹ * ratGL E n d * thetaA E n y) ≠ 0}.Finite := by
  have hK : IsCompact (C * tsupport φ * (thetaA E n '' C')⁻¹) :=
    (hC.mul hφ).mul (hC'.image continuous_thetaA).inv
  refine (finite_ratGL_mem hK).subset ?_
  rintro d ⟨x, hx, y, hy, h⟩
  have hd : ratGL E n d =
      x * (x⁻¹ * ratGL E n d * thetaA E n y) * (thetaA E n y)⁻¹ := by group
  change ratGL E n d ∈ C * tsupport φ * (thetaA E n '' C')⁻¹
  rw [hd]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx (subset_tsupport _ h))
    (Set.inv_mem_inv.2 (mem_image_of_mem _ hy))

theorem finite_twConj {φ : GA E n → ℂ} (hφ : HasCompactSupport φ) {C : Set (GA E n)} (hC : IsCompact C) :
    {d : GL (Fin n) E | ∃ x ∈ C, φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0}.Finite :=
  (finite_kernel hφ hC hC).subset fun _ ⟨x, hx, h⟩ => ⟨x, hx, x, hx, h⟩

theorem finite_twConj_of_isTest {φ : GA E n → ℂ} (hφ : IsTest φ) {C : Set (GA E n)} (hC : IsCompact C) :
    {d : GL (Fin n) E | ∃ x ∈ C, φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0}.Finite :=
  finite_twConj hφ.supp hC

theorem kerFin : PositivityTheory.Rg.BcB.D4.KerFin := fun _ _ _ _ _ _ hφ _ hC => finite_twConj_of_isTest hφ hC

end GlobalTheory.CompanionTheory.KerTwFin

end
end

