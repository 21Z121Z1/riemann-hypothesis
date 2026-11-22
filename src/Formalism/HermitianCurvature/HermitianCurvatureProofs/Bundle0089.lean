import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0081
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0084
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0024
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0062
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0060
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ebM (k r : ℕ) (v b : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  Matrix.of fun p q => v p * herm (Hpk k r) (bvec q) b

section tht

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sandw (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp A).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B')

def tht (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (Bw Bw' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ p, ∑ q, herm (Hpk k r) (ι *ᵥ Bw' q) (Bw p) •
    sandw (QrD.ecOp π (ebM k r (Bw p) (SSn.prWv k r z a))) (QrD.ecOp π' (ebM k r (SSn.prWv k r z' a') (Bw' q)))

def thtA (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (Bw Bw' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ p, ∑ q, conj (herm (Hpk k r) (ι *ᵥ Bw' q) (Bw p)) •
    sandw (QrD.ecOp π (ebM k r (SSn.prWv k r z a) (Bw p))) (QrD.ecOp π' (ebM k r (Bw' q) (SSn.prWv k r z' a')))

end tht

def ThtFacts : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * P.r + P.k + 1) → ℂ) × (Fin (2 * P.r + P.k + 1) → ℂ) ×
          B.Mat P.k P.r => tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' x.1 x.2.1 x.2.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * P.r + P.k + 1) → ℂ) × (Fin (2 * P.r + P.k + 1) → ℂ) ×
          B.Mat P.k P.r => thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' x.1 x.2.1 x.2.2) ∧
      (∀ a a' ι A B', B.hsInner (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι A) B' =
        B.hsInner A (thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι B')) ∧
      (∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z', ∀ a a' ι X,
        tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹)
            ((Bs.π h).comp (X.comp (Bs.π' h'⁻¹))) =
          (Bs.π h).comp ((tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι X).comp (Bs.π' h'⁻¹)) ∧
        thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹)
            ((Bs.π h).comp (X.comp (Bs.π' h'⁻¹))) =
          (Bs.π h).comp ((thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι X).comp (Bs.π' h'⁻¹))) ∧
      ∀ (c : ℂ) a a' ι, tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (c • a) (conj c • a') ι =
        (conj c) ^ 2 • tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι

def DatumUnit : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ), BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ (v : Fin S.f) (ζ : ℂ), (D.parOf S v).TT < Complex.normSq ζ →
      SSn.prWv S.G.k S.G.r (T v).base.z (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) =
          SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ ∧
        herm (Hpk S.G.k S.G.r) (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) = 1 ∧
        SSn.prWv S.G.k S.G.r (T v).base.z' (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) =
          SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ ∧
        herm (Hpk S.G.k S.G.r) (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) = 1

def ThtGaugeConst : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    PRho.Hyp Cc S T f χ ν' m₀ top A₀ v e → 2 ≤ S.G.k → ∀ l ∈ Finset.Icc 1 (S.G.k - 1),
    ∀ Bw Bw' : Fin S.G.k → Fin (2 * S.G.r + S.G.k + 1) → ℂ,
      Q.IsFrameOf S.G.k S.G.r [(T v).base.z] Bw → Q.IsFrameOf S.G.k S.G.r [(T v).base.z'] Bw' →
      ∃ κ : M.Ty (D.parOf S v) → ℂ, ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ → ∀ π ρ : M.Ty (D.parOf S v),
        M.Up (D.parOf S v) l π ρ →
        κ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw'
          (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) (e π ζ))) =
          ((Real.sqrt (M.Nrm (D.parOf S v) l π) : ℝ) : ℂ)

def SSnRepOfCut : Prop :=
  PRho.PRhoExists → PRho.GaugeLines → ThtFacts → DatumUnit → ThtGaugeConst → SSnRep

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EHcChange
section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dx_repF {X : Mat k r} (hX : inLie k r X) {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) : Dx (false, X) φ g = F' (g * X) := by
  rw [← dx_false]
  have hc := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hF0 : HasFDerivAt F F' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by simpa using hF
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (F' (g * X)) 0 :=
    hF0.comp_hasDerivAt (0 : ℝ) hc
  have hU0 : U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by simpa using hU.mem_nhds hgU
  have hev : (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      fun t => F (g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with t ht
    exact hff _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hg hX t)
  exact (hcomp.congr_of_eventuallyEq hev).deriv

theorem EH_psi {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) (a b : Fin (2 * r + k + 1)) :
    Q.EH k r a b φ g = Psi F' g (Matrix.single a b 1) := by
  have h1 : RdV (Xa k r a b) φ g = F' (g * Xa k r a b) := dx_repF (Xa_lie a b) hU hgU hg hF hff
  have h2 : RdV (Xb k r a b) φ g = F' (g * Xb k r a b) := dx_repF (Xb_lie a b) hU hgU hg hF hff
  show RdV (Xa k r a b) φ g + Complex.I • RdV (Xb k r a b) φ g =
    F' (g * Xa k r a b) + Complex.I • F' (g * Xb k r a b)
  rw [h1, h2]

private theorem inLie_conj_of_mem_GV' {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) :
    inLie k r (y⁻¹ * X * y) := by
  have hu : IsUnit y.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have h1 : Hpk k r * y⁻¹ = yᴴ * Hpk k r := by
    calc Hpk k r * y⁻¹ = yᴴ * Hpk k r * y * y⁻¹ := by rw [hy']
      _ = yᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have h2 : (y⁻¹)ᴴ * Hpk k r = Hpk k r * y := by
    calc (y⁻¹)ᴴ * Hpk k r = (y⁻¹)ᴴ * (yᴴ * Hpk k r * y) := by rw [hy']
      _ = (y * y⁻¹)ᴴ * Hpk k r * y := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * y := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold inLie at hX ⊢
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, h2]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    simp only [← Matrix.mul_assoc]
    rw [h1]
  rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem EHc_psi {y : Mat k r} (hy : y ∈ GV k r) {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) (c d : Fin (2 * r + k + 1)) :
    EHc k r y c d φ g = Psi F' g (y⁻¹ * Matrix.single c d 1 * y) := by
  rw [EHc_eq]
  beta_reduce
  rw [dx_repF (inLie_conj_of_mem_GV' hy (Xa_lie c d)) hU hgU hg hF hff,
    dx_repF (inLie_conj_of_mem_GV' hy (Xb_lie c d)) hU hgU hg hF hff]
  have hZ : y⁻¹ * Matrix.single c d 1 * y = y⁻¹ * Xa k r c d * y + Complex.I • (y⁻¹ * Xb k r c d * y) := by
    conv_lhs => rw [← hp_decomp (Matrix.single c d 1)]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    all_goals rfl
  obtain ⟨h1, h2⟩ := hp_of_parts (inLie_conj_of_mem_GV' hy (Xa_lie c d)) (inLie_conj_of_mem_GV' hy (Xb_lie c d))
  unfold Psi
  rw [hZ, h1, h2]

theorem conj_single (P Q : Mat k r) (c d : Fin (2 * r + k + 1)) :
    P * Matrix.single c d 1 * Q = ∑ a, ∑ b, (P a c * Q d b) • Matrix.single a b 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and, mul_ite, ite_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

private theorem psi_add_hermitian_curvature (D : Mat k r →L[ℝ] E) (g A B : Mat k r) :
    Psi D g (A + B) = Psi D g A + Psi D g B := by
  have h1 : hpart1 (Hpk k r) (A + B) = hpart1 (Hpk k r) A + hpart1 (Hpk k r) B := by
    simp only [hpart1, Matrix.conjTranspose_add, mul_add, add_mul]
    rw [← smul_add]
    congr 1
    abel
  have h2 : hpart2 (Hpk k r) (A + B) = hpart2 (Hpk k r) A + hpart2 (Hpk k r) B := by
    simp only [hpart2, Matrix.conjTranspose_add, mul_add, add_mul]
    rw [← smul_add]
    congr 1
    abel
  simp only [Psi, h1, h2, mul_add, map_add, smul_add]
  abel

theorem Psi_sum {ι : Type*} (s : Finset ι) (D : Mat k r →L[ℝ] E) (g : Mat k r) (Z : ι → Mat k r) :
    Psi D g (∑ i ∈ s, Z i) = ∑ i ∈ s, Psi D g (Z i) := by
  exact map_sum (AddMonoidHom.mk' (Psi D g) (psi_add_hermitian_curvature D g)) Z s

theorem rep1 {φ : Mat k r → E} (hφ : CkOn 1 (GV k r) φ) {g : Mat k r} (hg : g ∈ GV k r) :
    ∃ (U : Set (Mat k r)) (F : Mat k r → E), IsOpen U ∧ g ∈ U ∧ HasFDerivAt F (fderiv ℝ F g) g ∧
      ∀ h ∈ U, h ∈ GV k r → φ h = F h := by
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hφ g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.differentiableOn (by first | exact le_rfl | simp)).differentiableAt (hU.mem_nhds hgU)
  exact ⟨U, f', hU, hgU, hd.hasFDerivAt, hff⟩

theorem EH_HC : HC (Q.EH (E := E) k r) := by
  intro a b m f hf
  have h := EHc_ck (Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := r)) a b m f hf
  rwa [EHc_one] at h

theorem EH_HL : HL (Q.EH (E := E) k r) := by
  intro a b f f₂ h
  exact EH_congr a b f f₂ h

theorem EH_HA : HA (Q.EH (E := E) k r) := by
  intro a b f f₂ hf hf₂ g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hf hg
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, hff₂⟩ := rep1 hf₂ hg
  rw [EH_psi (φ := fun x => f x + f₂ x) (hU.inter hU₂) ⟨hgU, hgU₂⟩ hg (hF.add hF₂)
      (fun h hh hG => by simp only [hff h hh.1 hG, hff₂ h hh.2 hG, Pi.add_apply]) a b,
    EH_psi hU hgU hg hF hff a b, EH_psi hU₂ hgU₂ hg hF₂ hff₂ a b]
  simp only [Psi]
  show fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      fderiv ℝ F₂ g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      Complex.I • (fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single a b 1)) +
        fderiv ℝ F₂ g (g * hpart2 (Hpk k r) (Matrix.single a b 1))) = _
  rw [smul_add]
  abel

theorem EH_HS : HS (Q.EH (E := E) k r) := by
  intro a b c f hf g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hf hg
  rw [EH_psi (φ := fun x => c • f x) hU hgU hg (hF.const_smul c)
      (fun h hh hG => by simp only [hff h hh hG, Pi.smul_apply]) a b,
    EH_psi hU hgU hg hF hff a b]
  simp only [Psi]
  show c • fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      Complex.I • c • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single a b 1)) = _
  rw [smul_add, smul_comm Complex.I c]

theorem EHc_HL {y : Mat k r} (hy : y ∈ GV k r) : HL (EHc (E := E) k r y) := by
  intro a b f f₂ h g hg
  rw [EHc_eq, EHc_eq]
  beta_reduce
  rw [Dx_congr (x := (false, y⁻¹ * Xa k r a b * y)) (inLie_conj_of_mem_GV' hy (Xa_lie a b)) h g hg,
    Dx_congr (x := (false, y⁻¹ * Xb k r a b * y)) (inLie_conj_of_mem_GV' hy (Xb_lie a b)) h g hg]

theorem EHc_change {y : Mat k r} (hy : y ∈ GV k r) (c d : Fin (2 * r + k + 1)) (φ : Mat k r → E)
    (hφ : CkOn 1 (GV k r) φ) : ∀ g ∈ GV k r,
      EHc k r y c d φ g = ∑ a, ∑ b, (y⁻¹ a c * y d b) • Q.EH k r a b φ g := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hφ hg
  rw [EHc_psi hy hU hgU hg hF hff c d, conj_single, Psi_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Psi_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Psi_smul, EH_psi hU hgU hg hF hff a b]

end Formalism.FourierDecayAlt.P.JFxE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormCvecSq
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section cpic

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cvec (s : ℕ) (F : ℂ → ℂ → H) (x c : ℂ) : H :=
  (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x (c / x ^ (s - 1))

theorem cvec_inner (s : ℕ) (F G : ℂ → ℂ → H) (x x' : ℂ) (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ∫ c, ⟪cvec s F x c, cvec s G x' c⟫_ℂ =
      ∫ D, ⟪F x D, ((‖x ^ (s - 1) / x' ^ (s - 1)‖ : ℝ) : ℂ) • G x' ((x ^ (s - 1) / x' ^ (s - 1)) * D)⟫_ℂ := by
  have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hx0' : ‖x'‖ ≠ 0 := norm_ne_zero_iff.mpr hx'
  have hk : ‖x ^ (s - 1)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have key := integral_comp_mul_C (fun c => ⟪cvec s F x c, cvec s G x' c⟫_ℂ) (x ^ (s - 1)) ha
  have hL : ∫ c, ⟪cvec s F x c, cvec s G x' c⟫_ℂ
      = (‖x ^ (s - 1)‖ ^ 2) • ∫ z, ⟪cvec s F x (x ^ (s - 1) * z), cvec s G x' (x ^ (s - 1) * z)⟫_ℂ := by
    rw [key, smul_smul, mul_inv_cancel₀ hk, one_smul]
  rw [hL, ← integral_smul]
  congr 1
  funext D
  simp only [cvec]
  rw [mul_div_cancel_left₀ D ha, mul_div_right_comm (x ^ (s - 1)) D (x' ^ (s - 1))]
  have hc : ‖x ^ (s - 1)‖ ^ 2 * (‖x‖ ^ (s - 1))⁻¹ * (‖x'‖ ^ (s - 1))⁻¹
      = ‖x ^ (s - 1) / x' ^ (s - 1)‖ := by
    rw [norm_div, norm_pow, norm_pow]
    field_simp
  rw [inner_smul_left, inner_smul_right, inner_smul_right, Complex.conj_ofReal, Complex.real_smul, ← hc]
  push_cast
  ring

theorem integral_norm_cvec_sq (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) (hx : x ≠ 0) :
    ∫ c, ‖cvec s F x c‖ ^ 2 = ∫ D, ‖F x D‖ ^ 2 := by
  have ha : (x ^ (s - 1))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hx)
  have hr : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hce : cvec s F x = fun c => (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c) := by
    funext c
    simp only [cvec, div_eq_inv_mul]
  rw [hce]
  have h1 : ∀ c, ‖((((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c))‖ ^ 2
      = ((‖x‖ ^ (s - 1)) ^ 2)⁻¹ * ‖F x ((x ^ (s - 1))⁻¹ * c)‖ ^ 2 := by
    intro c
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow, inv_pow]
  simp_rw [h1]
  rw [integral_const_mul, integral_comp_mul_C (fun D => ‖F x D‖ ^ 2) _ ha, smul_eq_mul,
    norm_inv, norm_pow, inv_pow, inv_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hr), one_mul]

theorem cvec_eq_comp (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) :
    cvec s F x = fun c => (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c) := by
  funext c
  simp only [cvec, div_eq_inv_mul]

theorem memLp_cvec (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) (hx : x ≠ 0) :
    MemLp (F x) 2 volume ↔ MemLp (cvec s F x) 2 volume := by
  have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hr : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [cvec_eq_comp]
    exact (memLp_comp_mul h _ (inv_ne_zero ha)).const_smul _
  · have := (memLp_comp_mul h (x ^ (s - 1)) ha).const_smul ((‖x‖ ^ (s - 1) : ℝ) : ℂ)
    convert this using 1
    funext D
    simp only [Pi.smul_apply, cvec, smul_smul]
    rw [mul_div_cancel_left₀ D ha, ← Complex.ofReal_mul, mul_inv_cancel₀ hr, Complex.ofReal_one, one_smul]

theorem cvec_sub (s : ℕ) (F G : ℂ → ℂ → H) (x c : ℂ) :
    cvec s F x c - cvec s G x c = cvec s (fun x D => F x D - G x D) x c := by
  simp only [cvec, smul_sub]

theorem rhoR_pow_eq {s : ℕ} (hs : s ≠ 0) (σ x : ℂ) :
    rhoR s σ x ^ s = x ^ (s - 1) / (x + σ) ^ (s - 1) := by
  unfold rhoR lamR
  rw [Complex.cpow_nat_inv_pow _ hs, div_pow]

theorem norm_rhoR_pow {s : ℕ} (hs : s ≠ 0) (σ x : ℂ) :
    ‖rhoR s σ x‖ ^ s = ‖x ^ (s - 1) / (x + σ) ^ (s - 1)‖ := by
  rw [← norm_pow, rhoR_pow_eq hs]

end cpic

section cpicMain

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pairD_of_cvec {s : ℕ} (hs : s ≠ 0) (β ε : ℂ) (bt bt' : ℂ → H) (σ x : ℂ) (hx : x ≠ 0) (hxσ : x + σ ≠ 0) :
    ∫ c, ⟪cvec s (fun x D => mainD s β ε bt x D) x c, cvec s (fun x D => mainD s β ε bt' x D) (x + σ) c⟫_ℂ =
      pairD s β ε bt bt' x (x + σ) (rhoR s σ x) := by
  rw [cvec_inner s _ _ x (x + σ) hx hxσ]
  unfold pairD
  rw [rhoR_pow_eq hs, norm_rhoR_pow hs]

end cpicMain

end

end Formalism.FourierDecayAlt.P.PBK
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfExhaustOfAvgCutoff
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxI

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def AvgCutoff : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (K : Set ((Fin r → ℂ) × ℂ)),
    IsCompact K → K ⊆ QDom k r D.z D.z' →
    ∃ φ : B.Mat k r → ℂ, B.CkOn ⊤ (B.GV k r) φ ∧
      (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → φ g = 0) ∧
      ∀ p₀, D.inSS p₀ → ∀ q ∈ K, ∫ p, φ (B.sgs p (B.sgs p₀ (B.gq D q))) ∂D.μSS = 1

def AdjLeibniz : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq),
    B.SmoothCoef (Om k r D.z D.z') Θ →
    ∃ Θ' : B.DiffOp k r Wp Wq, B.opOrder Θ' = B.opOrder Θ ∧
      ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn (B.opOrder Θ : ℕ∞) (Om k r D.z D.z') f →
        ∀ g ∈ Om k r D.z D.z', B.opApply Θ' f g = B.opAdj Θ f g

def AdjCommutes : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq),
    B.SmoothCoef (Om k r D.z D.z') Θ → B.Commutes D (Om k r D.z D.z') Θ →
    ∀ p, D.inSS p → ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn (B.opOrder Θ : ℕ∞) (B.GV k r) f →
      ∀ g ∈ Om k r D.z D.z', B.opAdj Θ (B.rho D p f) g = B.rho D p (B.opAdj Θ f) g

variable {k r : ℕ}

theorem ckOn_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {U V : Set (Mat k r)}
    (hUV : U ⊆ V) {f : Mat k r → E} (h : CkOn m V f) : CkOn m U f := by
  exact fun g₀ hg => h g₀ (hUV hg)

theorem om_sub_gv (z z' : Fin (2 * r + k + 1) → ℂ) : Om k r z z' ⊆ GV k r := by
  exact Set.inter_subset_left

end Formalism.FourierDecayAlt.P.JFxI

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

