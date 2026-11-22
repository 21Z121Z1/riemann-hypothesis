import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.LemmaDensOfSteps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SupportPhiZeroSubset
section
namespace Formalism.FourierDecayAlt.P.PBI

open Finset Filter Topology MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

open Classical

def gPoly {r : ℕ} (TT : ℝ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ℝ :=
  Complex.normSq M.det - TT * Complex.normSq (M.submatrix Fin.castSucc Fin.castSucc).det

theorem gf_eq_gPoly (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Gf k r z z' g = gPoly (Tz k r z * Tz k r z') (Zhat k r z z' g) := by
  first
    | rfl
    | (unfold Gf gPoly Dmin; rfl)
    | (simp only [Gf, gPoly, Dmin]; rfl)

theorem continuous_gPoly (r : ℕ) (TT : ℝ) : Continuous fun Z : G.Mat (r + 1) => gPoly TT (Matrix.of Z) := by
  have hc : Continuous fun Z : G.Mat (r + 1) =>
      (Matrix.of Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := continuous_id
  unfold gPoly
  exact (Complex.continuous_normSq.comp hc.matrix_det).sub
    (continuous_const.mul (Complex.continuous_normSq.comp (hc.matrix_submatrix _ _).matrix_det))

section fibre

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def fibInt (Bs : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p, B.rho Bs p F g ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0'))

def phi0 (Bs : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (sec : G.Mat (r + 1) → Mt k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) : G.Mat (r + 1) → (Wq →L[ℂ] Wp) := fun Z =>
  if 0 < gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z) then fibInt Bs μ0 μ0' F (Matrix.of (sec Z)) else 0

def IsSec (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (sec : G.Mat (r + 1) → Mt k r) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sec {Z | 0 < gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z)} ∧
    ∀ Z, 0 < gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z) →
      Matrix.of (sec Z) ∈ B.GV k r ∧ Zhat k r Bs.z Bs.z' (Matrix.of (sec Z)) = Matrix.of Z ∧
        D.IsDFrame Bs ν' m₀ (Matrix.of (sec Z))

theorem cpt_of_fibre {E : Type*} [NormedAddCommGroup E] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef Bs F) (Ψ : G.Mat (r + 1) → E)
    (hΨ : ∀ Z, Ψ Z ≠ 0 → ∃ g ∈ B.GV k r, F g ≠ 0 ∧ Zhat k r Bs.z Bs.z' g = Matrix.of Z) :
    HasCompactSupport Ψ ∧ ∀ Z ∈ tsupport Ψ, G.detM Z ≠ 0 := by
  obtain ⟨_, ⟨R, hR⟩, ε, hε, hεG⟩ := hF
  obtain ⟨C, hC⟩ := zhat_norm_bound k r Bs.z Bs.z'
  set TT : ℝ := Tz k r Bs.z * Tz k r Bs.z' with hTT
  set K : Set (G.Mat (r + 1)) :=
    Metric.closedBall 0 (max C 0 * R) ∩ {Z | ε ≤ gPoly TT (Matrix.of Z)} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 _).inter_right (isClosed_le continuous_const (continuous_gPoly r TT))
  have hsub : Function.support Ψ ⊆ K := by
    intro Z hZ
    obtain ⟨g, hg, hFg, hZg⟩ := hΨ Z hZ
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : C2.mx (Zhat k r Bs.z Bs.z' g) ≤ C * B.gN g := hC g
      rw [hZg] at h1
      have h2 : C2.mx (Matrix.of Z) = ‖Z‖ := rfl
      rw [h2] at h1
      have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
      have hRg : B.gN g ≤ R := hR g hg hFg
      calc ‖Z‖ ≤ C * B.gN g := h1
        _ ≤ max C 0 * B.gN g := mul_le_mul_of_nonneg_right (le_max_left _ _) hgN
        _ ≤ max C 0 * R := mul_le_mul_of_nonneg_left hRg (le_max_right _ _)
    · show ε ≤ gPoly TT (Matrix.of Z)
      have := hεG g hg hFg
      rw [gf_eq_gPoly, hZg] at this
      exact this
  have hts : tsupport Ψ ⊆ K := closure_minimal hsub hKc.isClosed
  refine ⟨hKc.of_isClosed_subset (isClosed_tsupport Ψ) hts, fun Z hZ => ?_⟩
  have hZK := (hts hZ).2
  simp only [Set.mem_ofPred_eq, gPoly] at hZK
  have hTT0 : 0 ≤ TT := mul_nonneg Bs.T_pos.le Bs.T'_pos.le
  have hpos : 0 < Complex.normSq (Matrix.of Z).det := by
    have := mul_nonneg hTT0 (Complex.normSq_nonneg ((Matrix.of Z).submatrix Fin.castSucc Fin.castSucc).det)
    linarith
  intro h0
  unfold G.detM at h0
  rw [h0, map_zero] at hpos
  exact lt_irrefl _ hpos

theorem support_phi_zero_subset (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (μ0 μ0' : Measure (Mt k r)) (hμ0 : B.IsHaarOn (C2.N0set k r Bs.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r Bs.z') μ0') (sec : G.Mat (r + 1) → Mt k r) (hsec : IsSec Bs ν' m₀ sec)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (Z : G.Mat (r + 1)) (hZ : phi0 Bs μ0 μ0' sec F Z ≠ 0) :
    ∃ g ∈ B.GV k r, F g ≠ 0 ∧ Zhat k r Bs.z Bs.z' g = Matrix.of Z := by
  unfold phi0 at hZ
  split_ifs at hZ with hG
  · obtain ⟨hg0, hZg0, -⟩ := hsec.2 Z hG
    set g0 : B.Mat k r := Matrix.of (sec Z) with hg0def
    by_contra hno
    push Not at hno
    apply hZ
    unfold fibInt
    have hW := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF Bs.haarW
    have hW' := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF Bs.haarW'
    have hN := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hμ0
    have hN' := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hμ0'
    have b1 : ∀ᵐ q ∂(Bs.μW.prod μ0), Matrix.of q.1 ∈ UWset k r Bs.z :=
      (Measure.quasiMeasurePreserving_fst (μ := Bs.μW) (ν := μ0)).ae
        (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem Bs.haarW)
    have b2 : ∀ᵐ q ∂(Bs.μW.prod μ0), Matrix.of q.2 ∈ C2.N0set k r Bs.z :=
      (Measure.quasiMeasurePreserving_snd (μ := Bs.μW) (ν := μ0)).ae (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hμ0)
    have c1 : ∀ᵐ q ∂(Bs.μW'.prod μ0'), Matrix.of q.1 ∈ UWset k r Bs.z' :=
      (Measure.quasiMeasurePreserving_fst (μ := Bs.μW') (ν := μ0')).ae
        (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem Bs.haarW')
    have c2 : ∀ᵐ q ∂(Bs.μW'.prod μ0'), Matrix.of q.2 ∈ C2.N0set k r Bs.z' :=
      (Measure.quasiMeasurePreserving_snd (μ := Bs.μW') (ν := μ0')).ae (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hμ0')
    have d1 : ∀ᵐ p ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')),
        Matrix.of p.1.1 ∈ UWset k r Bs.z ∧ Matrix.of p.1.2 ∈ C2.N0set k r Bs.z :=
      (Measure.quasiMeasurePreserving_fst (μ := Bs.μW.prod μ0) (ν := Bs.μW'.prod μ0')).ae (b1.and b2)
    have d2 : ∀ᵐ p ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')),
        Matrix.of p.2.1 ∈ UWset k r Bs.z' ∧ Matrix.of p.2.2 ∈ C2.N0set k r Bs.z' :=
      (Measure.quasiMeasurePreserving_snd (μ := Bs.μW.prod μ0) (ν := Bs.μW'.prod μ0')).ae (c1.and c2)
    apply integral_eq_zero_of_ae
    filter_upwards [d1, d2] with p h1 h2
    have hGG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
    have hNN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
    have hz : C2.StdZ k r Bs.z := ⟨Bs.z_mem, Bs.T_pos⟩
    have hz' : C2.StdZ k r Bs.z' := ⟨Bs.z'_mem, Bs.T'_pos⟩
    set h := (Matrix.of p.1.1 : B.Mat k r)
    set n := (Matrix.of p.1.2 : B.Mat k r)
    set h' := (Matrix.of p.2.1 : B.Mat k r)
    set n' := (Matrix.of p.2.2 : B.Mat k r)
    have hhG : h ∈ B.GV k r := h1.1.1
    have hnG : n ∈ B.GV k r := h1.2.1.1
    have hh'G : h' ∈ B.GV k r := h2.1.1
    have hn'G : n' ∈ B.GV k r := h2.2.1.1
    have hsgs : B.sgs p g0 = h⁻¹ * (n⁻¹ * g0 * n') * h' := by
      simp only [B.sgs, Matrix.mul_assoc]; rfl
    have hmem : B.sgs p g0 ∈ B.GV k r := by
      rw [hsgs]
      exact hGG.mul_mem _ (hGG.mul_mem _ (hGG.inv_mem _ hhG)
        _ (hGG.mul_mem _ (hGG.mul_mem _ (hGG.inv_mem _ hnG) _ hg0) _ hn'G)) _ hh'G
    have hS_h : h ∈ Sset k r Bs.z := ⟨h, h1.1, 1, hNN.one_mem, (Matrix.mul_one h).symm⟩
    have hS_h' : h' ∈ Sset k r Bs.z' := ⟨h', h2.1, 1, hNN.one_mem, (Matrix.mul_one h').symm⟩
    have hS_n : n ∈ Sset k r Bs.z :=
      ⟨1, (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs.z).one_mem, n, h1.2.1, (Matrix.one_mul n).symm⟩
    have hS_n' : n' ∈ Sset k r Bs.z' :=
      ⟨1, (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs.z').one_mem, n', h2.2.1, (Matrix.one_mul n').symm⟩
    have e1 := Formalism.FourierDecayAlt.P.zhat_equivalence k r Bs.z Bs.z' hz hz' h hS_h h' hS_h' (n⁻¹ * g0 * n')
    have e2 := Formalism.FourierDecayAlt.P.zhat_equivalence k r Bs.z Bs.z' hz hz' n hS_n n' hS_n' g0
    have u1 : C2.uMap k r Bs.z h = 1 := (Formalism.FourierDecayAlt.P.unipotent_map_frame k r Bs.z hz).2 h h1.1
    have u1' : C2.uMap k r Bs.z' h' = 1 := (Formalism.FourierDecayAlt.P.unipotent_map_frame k r Bs.z' hz').2 h' h2.1
    rw [u1, u1', Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at e1
    rw [h1.2.2, h2.2.2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at e2
    have hZs : Zhat k r Bs.z Bs.z' (B.sgs p g0) = Matrix.of Z := by rw [hsgs, e1, e2, hZg0]
    have hF0 : F (B.sgs p g0) = 0 := by
      by_contra hne
      exact hno _ hmem hne hZs
    simp [B.rho, hF0]
  · exact absurd rfl hZ

end fibre

def SectionExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r),
    D.IsBaseFrame Bs ν' m₀ → ∃ sec : G.Mat (r + 1) → Mt k r, IsSec Bs ν' m₀ sec

def FibIntSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (μ0 μ0' : Measure (Mt k r)) (sec : G.Mat (r + 1) → Mt k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    D.IsBaseFrame Bs ν' m₀ → B.IsHaarOn (C2.N0set k r Bs.z) μ0 → B.IsHaarOn (C2.N0set k r Bs.z') μ0' →
    IsSec Bs ν' m₀ sec → KB.CptCoef Bs F → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (phi0 Bs μ0 μ0' sec F)

def FibIntCells : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    ∃ (μ0 μ0' : Measure (Mt P.k P.r)) (c : ℂ), B.IsHaarOn (C2.N0set P.k P.r p.T.base.z) μ0 ∧
      B.IsHaarOn (C2.N0set P.k P.r p.T.base.z') μ0' ∧
      ∀ sec : G.Mat (P.r + 1) → Mt P.k P.r, IsSec p.T.base p.ν' p.m₀ sec →
      ∀ F, KB.CptCoef p.T.base F →
      ∀ (a : C.LPt) (σ : Equiv.Perm (Fin (P.r + 1))) (d : Fin (P.r + 1) → ℂ), D.IsLocPt a (P.r + 1) →
        U.hMat σ d = D.ptMatN a (P.r + 1) →
        p.V F a = U.PhiTop (p := P.r + 1) (s := 0) U.betaU σ d (c • phi0 p.T.base μ0 μ0' sec F)
          fun x => x.elim0

def Phi0Support : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (μ0 μ0' : Measure (Mt k r)) (sec : G.Mat (r + 1) → Mt k r) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.IsHaarOn (C2.N0set k r Bs.z) μ0 → B.IsHaarOn (C2.N0set k r Bs.z') μ0' → IsSec Bs ν' m₀ sec →
    KB.CptCoef Bs F → HasCompactSupport (phi0 Bs μ0 μ0' sec F) ∧
      ∀ Z ∈ tsupport (phi0 Bs μ0 μ0' sec F), G.detM Z ≠ 0

def PhiZeroOfParts : Prop := SectionExists → FibIntSmooth → FibIntCells → KB.PhiZero

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Formalism.FourierDecayAlt

theorem phi_zero_support : PBI.Phi0Support := by
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ μ0 μ0' sec F hμ0 hμ0' hsec hF
  exact PBI.cpt_of_fibre Bs F hF (PBI.phi0 Bs μ0 μ0' sec F)
    (fun Z hZ => PBI.support_phi_zero_subset Bs ν' m₀ μ0 μ0' hμ0 hμ0' sec hsec F Z hZ)

theorem phi_zero_of_parts : PBI.PhiZeroOfParts := by
  intro hSec hSm hCells Wp Wq _ _ _ _ _ _ P p F hF
  obtain ⟨μ0, μ0', c, hμ0, hμ0', hV⟩ := hCells Wp Wq P p
  obtain ⟨sec, hsec⟩ := hSec P.k P.r Wp Wq p.T.base p.ν' p.m₀ p.hF
  have hsupp := phi_zero_support P.k P.r Wp Wq p.T.base p.ν' p.m₀ μ0 μ0' sec F hμ0 hμ0' hsec hF
  refine ⟨c • PBI.phi0 p.T.base μ0 μ0' sec F, ?_, ?_, ?_, ?_⟩
  · exact (hSm P.k P.r Wp Wq p.T.base p.ν' p.m₀ μ0 μ0' sec F p.hF hμ0 hμ0' hsec hF).const_smul c
  · exact hsupp.1.mono (Function.support_const_smul_subset c _)
  · intro Z hZ
    exact hsupp.2 Z (closure_mono (Function.support_const_smul_subset c _) hZ)
  · intro a σ d ha hd
    exact hV sec hsec F hF a σ d ha hd

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UnitriangularEqOneOfMinorsNonzero
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isLowUni_det)

theorem unitriangular_eq_one_of_minors_nonzero {m : ℕ} {Z u u' : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (hu' : u' ∈ C2.UTset m)
    (h : uᴴ * Z * u' = Z)
    (hZ : ∀ (l : ℕ) (hl : l ≤ m), (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0) : u = 1 := by
  obtain ⟨L, U, d, hL, hU, e⟩ := S3x7.ldu_exists m Z (fun l hl => isUnit_iff_ne_zero.mpr (hZ l hl.le))
  have hUp : IsUpUni u' := S3x7.mk_up (fun i j hij => hu'.1 i j hij) hu'.2
  have hLow : IsLowUni uᴴ := S3x7.mk_low (fun i j hij => by simp [Matrix.conjTranspose_apply, hu.1 j i hij])
    (fun i => by simp [Matrix.conjTranspose_apply, hu.2 i])
  have e2 : L * diagonal d * U = (uᴴ * L) * diagonal d * (U * u') := by
    calc L * diagonal d * U = Z := e.symm
      _ = uᴴ * Z * u' := h.symm
      _ = _ := by rw [e]; simp only [Matrix.mul_assoc]
  have hd : S3.lead (L * diagonal d * U) m le_rfl ∈ nonZeroDivisors ℂ := by
    rw [← e]; exact mem_nonZeroDivisors_of_ne_zero (hZ m le_rfl)
  obtain ⟨hLL, -, -⟩ := S3x7.ldu_unique hL hU (isLowUni_mul ℂ hLow hL) (isUpUni_mul ℂ hU hUp) hd e2
  have hLu : IsUnit L.det := by rw [isLowUni_det ℂ hL]; exact isUnit_one
  have hu1 : uᴴ = 1 := by
    have h1 := congrArg (· * L⁻¹) hLL
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLu, Matrix.mul_one] at h1
    exact h1.symm
  have := congrArg Matrix.conjTranspose hu1
  simpa using this

theorem relevant_trivial_big_cell_of_parts : Formalism.FourierDecayAlt.DensityAveraging.RTrivBigOfParts := by
  intro h2 h3 k r Wp Wq _ _ _ _ _ D γ hγ hrel
  have hStd : C2.Std k r D.z D.z' := ⟨D.k_pos, ⟨D.z_mem, D.T_pos⟩, ⟨D.z'_mem, D.T'_pos⟩⟩
  have hPos : C2.PosPt k r D.z D.z' γ := ⟨hγ.1, hγ.2.1⟩
  have hγu : IsUnit γ.det := Dx2.OrbJ.isUnit_of_G hγ.1
  obtain ⟨_, hReq, _, _, _⟩ := h2 k r D.z D.z' γ hStd hPos
  obtain ⟨hbij, hinj, _⟩ := h3 k r D.z D.z' γ hStd hPos
  have hN1 : (1 : B.Mat k r) ∈ Nset k r := (unipotent_radical_closed k r).one_mem
  have hconj : ∀ ρ : B.Mat k r, γ * (γ⁻¹ * ρ * γ) * γ⁻¹ = ρ := by
    intro ρ
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hγu, Matrix.mul_nonsing_inv_cancel_left _ _ hγu]
  have mem : ∀ ρ ∈ Rset γ, ρ ∈ C2.Rst k r D.z D.z' γ := by
    intro ρ hρ
    rw [hReq]
    exact ⟨hρ.1, γ⁻¹ * ρ * γ, hρ.2, (hconj ρ).symm⟩
  have one_R : (1 : B.Mat k r) ∈ Rset γ := ⟨hN1, by simpa [Matrix.nonsing_inv_mul _ hγu] using hN1⟩
  have hZ : ∀ (l : ℕ) (hl : l ≤ r + 1),
      ((Zhat k r D.z D.z' γ).submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 :=
    fun l hl => hγ.2.2 ⟨l, by omega⟩ (Finset.mem_univ _)
  have huOne : ∀ x ∈ C2.Rst k r D.z D.z' γ, C2.uMap k r D.z x = 1 := by
    intro x hx
    obtain ⟨h1, h2', h3'⟩ := hbij.mapsTo hx
    exact unitriangular_eq_one_of_minors_nonzero h1 h2' h3' hZ
  ext ρ
  constructor
  · intro hρ
    exact hinj (mem ρ hρ) (mem 1 one_R) ((huOne ρ (mem ρ hρ)).trans (huOne 1 (mem 1 one_R)).symm)
  · intro hρ
    rw [Set.mem_singleton_iff.mp hρ]
    exact one_R

end Formalism.FourierDecayAlt.P
end
end

