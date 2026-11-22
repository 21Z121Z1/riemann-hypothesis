import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0125
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0146
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0148
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockRelationTwistedHeight

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapR
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {k r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def dMul (d : (Fin r → ℂ) → ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X := fun c g => d c • Φ c g

def drF (r : ℕ) : (Fin r → ℂ) → ℂ := fun c => ∏ a, c a

def drbF (r : ℕ) : (Fin r → ℂ) → ℂ := fun c => starRingEnd ℂ (∏ a, c a)

variable (k r)

def rhGrp (z z' : Fin (2 * r + k + 1) → ℂ) (y : ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X :=
  dMul (drbF r) (Q.QL k r z z' (Fin.last r) y 1 0 (Q.crd (Q.cmp (Q.vAB r y r) 0) Φ) +
    Q.QL k r z z' (Fin.last r) y 1 1 (Q.crd (Q.cmp (Q.vAB r y r) 1) Φ))

def rhvGrp (z z' : Fin (2 * r + k + 1) → ℂ) (y : ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X :=
  dMul (drF r) (Q.QL k r z z' (Fin.last r) y 0 1 (Q.crd (Q.cmp (Q.vABs r y r) 0) Φ) +
    Q.QL k r z z' (Fin.last r) y 1 1 (Q.crd (Q.cmp (Q.vABs r y r) 1) Φ))

end defs

def JDRGrp : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                rhGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g ∧
              Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                rhvGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

def JDRDrTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      (∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drbF P.r) Φ) ρ) =
        MA.actA P L.Drb (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) ∧
      ∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drF P.r) Φ) ρ) =
        MA.actA P L.Dr (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ

def JDRModelV : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℝ,
    (∀ b : Fin 2, Wd.v0 (MA.sites P (MA.DQ P)) (y : ℂ) b = L.Tprod (y : ℂ) b 0) ∧
    ∀ a : Fin 2, star (Wd.v0 (MA.sites P (MA.DQ P)) (y : ℂ) a) = L.Tvprod (y : ℂ) a 0

def JDRGrpP : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                rhGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

def JDRGrpM : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                rhvGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

theorem jDRGrp_of_halves (hP : JDRGrpP) (hM : JDRGrpM) : JDRGrp := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, h1, h3, hR⟩ := hP Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θv, h2, h4, hRv⟩ := hM Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  exact ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ c hc g hg hcg => ⟨hR J hJ c hc g hg hcg, hRv J hJ c hc g hg hcg⟩⟩

section assembly

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jdr_tr_at (hD : JDRDrTr) (hM : JDRModelV) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : Gauge.IsFrameB P Bs e)
    (hQQ : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ)
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : Gauge.FamR P Bs Dc Φ)
    (y : ℝ) :
    Gauge.VLem.trR P Bs.μsec e (rhGrp P.k P.r Bs.z Bs.z' (y : ℂ) Φ) =
        MA.actA P (RhM P L y) (Gauge.VLem.trR P Bs.μsec e Φ) ∧
      Gauge.VLem.trR P Bs.μsec e (rhvGrp P.k P.r Bs.z Bs.z' (y : ℂ) Φ) =
        MA.actA P (RhvM P L y) (Gauge.VLem.trR P Bs.μsec e Φ) := by
  have hV := fun b => Gauge.gauge_vector_transition_holds Wp Wq P Bs hpl hk e he Dc Φ hΦ y b
  have hVs := fun a => Gauge.gauge_conj_vector_transition Wp Wq P Bs hpl hk e he Dc Φ hΦ y a
  have hsm := fun (Dc' : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    (hΨ : Gauge.FamR P Bs Dc' Ψ) => Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc' Ψ hΨ
  have hql := fun (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΨ : Gauge.FamR P Bs Dc Ψ) (a b : Fin 2) =>
    Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Ψ hΨ y a b
  obtain ⟨hMv, hMs⟩ := hM P L hL y
  have hsum : ∀ (Ψ₀ Ψ₁ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Ψ₀ → Gauge.FamR P Bs Dc Ψ₁ →
      Gauge.FamR P Bs Dc (Ψ₀ + Ψ₁) := fun _ _ h₀ h₁ => Gauge.VLem.famR_add h₀ h₁
  constructor
  · have hF0 := hql _ (hV 0).1 1 0
    have hF1 := hql _ (hV 1).1 1 1
    funext ρ
    show MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drbF P.r) _) ρ) = _
    rw [(hD Wp Wq P Bs hpl hk e he L hL Dc _ (hsum _ _ hF0 hF1)).1 ρ]
    have e1 : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 0 (Q.crd (Q.cmp (Q.vAB P.r (y : ℂ) P.r) 0) Φ) +
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 1 (Q.crd (Q.cmp (Q.vAB P.r (y : ℂ) P.r) 1) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (y : ℂ) 1 0 * L.Ar (y : ℂ) + MA.QQr P (MA.DQ P) (y : ℂ) 1 1 * L.Br (y : ℂ))
          (Gauge.VLem.trR P Bs.μsec e Φ) := by
      have := Gauge.VLem.trR_add Bs.μsec e _ _ (hsm _ _ hF0) (hsm _ _ hF1)
      unfold Gauge.VLem.trR at this
      rw [this, Gauge.actA_add, Gauge.actA_mul, Gauge.actA_mul, R.LevelData.Ar, R.LevelData.Br, ← hMv 0, ← hMv 1]
      congr 1
      · funext ρ'; rw [hQQ _ _ (hV 0).1 y 1 0 ρ']; congr 1; funext ρ''; exact (hV 0).2 ρ''
      · funext ρ'; rw [hQQ _ _ (hV 1).1 y 1 1 ρ']; congr 1; funext ρ''; exact (hV 1).2 ρ''
    rw [e1, ← Gauge.actA_mul]
    rfl
  · have hF0 := hql _ (hVs 0).1 0 1
    have hF1 := hql _ (hVs 1).1 1 1
    funext ρ
    show MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drF P.r) _) ρ) = _
    rw [(hD Wp Wq P Bs hpl hk e he L hL Dc _ (hsum _ _ hF0 hF1)).2 ρ]
    have e1 : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 0 1 (Q.crd (Q.cmp (Q.vABs P.r (y : ℂ) P.r) 0) Φ) +
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 1 (Q.crd (Q.cmp (Q.vABs P.r (y : ℂ) P.r) 1) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (y : ℂ) 0 1 * L.Avr (y : ℂ) + MA.QQr P (MA.DQ P) (y : ℂ) 1 1 * L.Bvr (y : ℂ))
          (Gauge.VLem.trR P Bs.μsec e Φ) := by
      have := Gauge.VLem.trR_add Bs.μsec e _ _ (hsm _ _ hF0) (hsm _ _ hF1)
      unfold Gauge.VLem.trR at this
      rw [this, Gauge.actA_add, Gauge.actA_mul, Gauge.actA_mul, R.LevelData.Avr, R.LevelData.Bvr, ← hMs 0, ← hMs 1]
      congr 1
      · funext ρ'; rw [hQQ _ _ (hVs 0).1 y 0 1 ρ']; congr 1; funext ρ''; exact (hVs 0).2 ρ''
      · funext ρ'; rw [hQQ _ _ (hVs 1).1 y 1 1 ρ']; congr 1; funext ρ''; exact (hVs 1).2 ρ''
    rw [e1, ← Gauge.actA_mul]
    rfl

end assembly

theorem jDCapR_of_parts (hG : JDRGrp) (hD : JDRDrTr) (hM : JDRModelV) : JDCapR := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  obtain ⟨Θ, Θv, h1, h2, h3, h4, hR⟩ := hG Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ => ?_⟩
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  have hF := Gauge.tc_famR (D.parOf S v) (T v).base hpl J hJ
  obtain ⟨tR, tRv⟩ := jdr_tr_at hD hM (D.parOf S v) (T v).base hpl hk e hFr
    (fun Dc Φ hΦ Y a b ρ => hQQ Dc Φ hΦ Y a b ρ) L hL _ _ hF y
  have hJR : trJ S T v e J = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e
      (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) := by
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e J ρ) = _
    rw [Gauge.tc_rawJ]
    rfl
  have hpt : ∀ (Θ' : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (F : Q.Fn S.G.k S.G.r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
      (∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
        Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
        Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ' J) c g = F c g) →
      trJ S T v e (B.opApply Θ' J) = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e F := by
    intro Θ' F hF'
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e (B.opApply Θ' J) ρ) = _
    rw [Gauge.tc_rawJ]
    show MA.toSm _ _ = MA.toSm _ _
    congr 1
    funext q
    have hmu := Gauge.tc_mu (D.parOf S v) (T v).base hpl q
    simp only [Gauge.rawR]
    rw [hF' q.1.1 q.2.1 _ hmu.1 hmu.2]
  constructor
  · rw [hpt Θ _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).1), hJR]
    exact tR
  · rw [hpt Θv _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).2), hJR]
    exact tRv

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianInsertionVectorOrthogonal
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section SpacedProductLowerBound

variable {k : ℕ}

def pidx (m : ℕ) (i : Fin (m + 1)) (c : ℕ) (h : c < m + 1 ∧ c ≠ i.val) : Fin m :=
  ⟨if c < i.val then c else c - 1, by split_ifs <;> omega⟩

theorem succAbove_pidx (m : ℕ) (i : Fin (m + 1)) (c : ℕ) (h : c < m + 1 ∧ c ≠ i.val) :
    (i.succAbove (pidx m i c h)).val = c := by
  rw [succAbove_val]; unfold pidx; simp only; split_ifs <;> omega

theorem pidx_succAbove (m : ℕ) (i : Fin (m + 1)) (b : Fin m) (h : (i.succAbove b).val < m + 1 ∧ (i.succAbove b).val ≠ i.val) :
    pidx m i (i.succAbove b).val h = b := by
  ext; unfold pidx; simp only; rw [succAbove_val]; split_ifs <;> omega

theorem herm_add_smul_right {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w1 w2 : Fin n → ℂ) (a b : ℂ) :
    herm H v (a • w1 + b • w2) = star a * herm H v w1 + star b * herm H v w2 := by
  unfold herm
  simp [star_add, star_smul, add_dotProduct, smul_dotProduct]

def ViF (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ) : Fin (2 * (m + 1) + k + 1) → ℂ :=
  fun p => if p = esI k (m + 1) i then 1
    else if h : p.val < m + 1 ∧ p.val ≠ i.val then -star (Vc (pidx m i p.val h) (eI k (m + 1) i)) else 0

variable (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem insertion_vector_zero_off_index (p : Fin (2 * (m + 1) + k + 1)) (hp : m + 1 ≤ p.val) (hne : p ≠ esI k (m + 1) i) : ViF m i Vc p = 0 := by
  unfold ViF; rw [if_neg hne, dif_neg (by omega)]

theorem ViF_eI : ViF m i Vc (eI k (m + 1) i) = 0 := by
  unfold ViF
  rw [if_neg, dif_neg]
  · simp [eI]
  · intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega

theorem tau_eI (c : Fin (m + 1)) : WeylGroupFacts.tau k (m + 1) (eI k (m + 1) c) = esI k (m + 1) c := by
  have := c.isLt
  ext; rw [tau_val, if_pos (by left; simp only [eI]; omega)]; simp only [eI, esI]

theorem tau_esI (c : Fin (m + 1)) : WeylGroupFacts.tau k (m + 1) (esI k (m + 1) c) = eI k (m + 1) c := by
  have := c.isLt
  ext; rw [tau_val, if_pos (by right; simp only [esI]; omega)]; simp only [esI, eI]; omega

end SpacedProductLowerBound

section N2c

variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem sg_val' (q : Fin (2 * (m + 1) + k + 1)) : (NFOne.sg k (m + 1) q).val = 2 * (m + 1) + k - q.val := rfl

theorem ViF_alt (l : Fin (2 * (m + 1) + k + 1)) : ViF m i Vc l = 0 ∨ ViF m i Vc (WeylGroupFacts.tau k (m + 1) l) = 0 := by
  by_cases h1 : l = esI k (m + 1) i
  · right; rw [h1, tau_esI]; exact ViF_eI m i Vc
  by_cases h2 : l = eI k (m + 1) i
  · left; rw [h2]; exact ViF_eI m i Vc
  by_cases h3 : m + 1 ≤ l.val
  · left; exact insertion_vector_zero_off_index m i Vc l h3 h1
  · right
    apply insertion_vector_zero_off_index
    · rw [tau_val]; split_ifs <;> omega
    · intro h; apply h2
      have := congrArg (WeylGroupFacts.tau k (m + 1)) h
      rw [WeylGroupFacts.tau_tau, tau_esI] at this; exact this

theorem ViF_iso : herm (Hpk k (m + 1)) (ViF m i Vc) (ViF m i Vc) = 0 := by
  rw [herm_expand]
  apply Finset.sum_eq_zero
  intro l _
  rcases ViF_alt m i Vc l with h | h <;> simp [h]

theorem hermitian_insertion_vector_orthogonal (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (hz : inWb k (m + 1) z') :
    herm (Hpk k (m + 1)) z' (ViF m i Vc) = 0 := by
  rw [herm_expand]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hW : m + 1 ≤ l.val ∧ l.val ≤ m + 1 + k
  · rw [insertion_vector_zero_off_index m i Vc l hW.1 (by intro h; rw [h] at hW; simp [esI] at hW; omega)]; simp
  · rw [hz (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]; simp

theorem ViF_star (q : Fin (2 * (m + 1) + k + 1)) (hq : m + 1 + k < q.val) :
    ViF m i Vc q = if (NFOne.sg k (m + 1) q).val = i.val then 1 else 0 := by
  by_cases h : q = esI k (m + 1) i
  · rw [if_pos (by rw [sg_val', h]; simp [esI]; omega)]
    unfold ViF; rw [if_pos h]
  · rw [insertion_vector_zero_off_index m i Vc q (by omega) h, if_neg]
    intro h'; apply h; ext; rw [sg_val'] at h'; simp [esI]; omega

theorem ViF_Vc (hVs : ∀ (b : Fin m) (q : Fin (2 * (m + 1) + k + 1)), m + 1 + k < q.val →
      Vc b q = if (NFOne.sg k (m + 1) q).val = (i.succAbove b).val then 1 else 0) (c' : Fin m) :
    herm (Hpk k (m + 1)) (ViF m i Vc) (Vc c') = 0 := by
  have hs := (i.succAbove c').isLt
  have hsi : (i.succAbove c').val ≠ i.val := fun h' => Fin.succAbove_ne i c' (Fin.ext h')
  rw [herm_expand, Finset.sum_eq_add (eI k (m + 1) i) (esI k (m + 1) (i.succAbove c'))]
  · rw [tau_eI, tau_esI]
    have e1 : ViF m i Vc (esI k (m + 1) i) = 1 := by unfold ViF; rw [if_pos rfl]
    have e2 : ViF m i Vc (eI k (m + 1) (i.succAbove c')) = -star (Vc c' (eI k (m + 1) i)) := by
      unfold ViF
      rw [if_neg (by intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega),
        dif_pos ⟨by simp only [eI]; omega, by simpa [eI] using hsi⟩]
      congr 3
      have := pidx_succAbove m i c' ⟨hs, hsi⟩
      simpa [eI] using this
    have e3 : Vc c' (esI k (m + 1) (i.succAbove c')) = 1 := by
      rw [hVs c' _ (by simp [esI]; omega), if_pos (by rw [sg_val']; simp [esI]; omega)]
    rw [e1, e2, e3, sgn_one _ (by simp [eI]; omega), sgn_one _ (by simp [esI]; omega)]
    simp
  · intro h; have := congrArg Fin.val h; simp [eI, esI] at this; omega
  · intro l _ hl
    by_cases hS : m + 1 + k < l.val
    · rw [hVs c' l hS, if_neg]
      · simp
      · intro h'; apply hl.2; ext; rw [sg_val'] at h'; simp [esI]; omega
    · by_cases hX : l.val < m + 1
      · rw [insertion_vector_zero_off_index m i Vc (WeylGroupFacts.tau k (m + 1) l) (by rw [tau_val]; split_ifs <;> omega)]
        · simp
        · intro h; apply hl.1
          have := congrArg (WeylGroupFacts.tau k (m + 1)) h
          rw [WeylGroupFacts.tau_tau, tau_esI] at this; exact this
      · have ht : WeylGroupFacts.tau k (m + 1) l = l := by ext; rw [tau_val]; split_ifs <;> omega
        rw [ht, insertion_vector_zero_off_index m i Vc l (by omega) (by intro h; rw [h] at hS; simp [esI] at hS; omega)]; simp
  · simp
  · simp

end N2c

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Tower
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ}

theorem lift_lift_V (j ρ n r : ℕ) (hn : 1 + ρ = n) (h1 : j + n = r) (h2 : j + 1 + ρ = r)
    (v : Fin (2 * ρ + k + 1) → ℂ) :
    D.castV h1 (liftVec k j n (D.castV hn (liftVec k 1 ρ v))) = D.castV h2 (liftVec k (j + 1) ρ v) := by
  funext i
  simp only [D.castV, liftVec, Fin.coe_cast]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, Fin.coe_cast] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk, Fin.coe_cast] <;> omega)

theorem lift_lift_M (j ρ n r : ℕ) (hn : 1 + ρ = n) (h1 : j + n = r) (h2 : j + 1 + ρ = r) (y : B.Mat k ρ) :
    D.castM h1 (ιLev k j n (D.castM hn (ιLev k 1 ρ y))) = D.castM h2 (ιLev k (j + 1) ρ y) := by
  ext p q
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Fin.coe_cast, ιLev]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, Fin.coe_cast] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk, Fin.coe_cast] <;> omega)

theorem castV_inj {a b : ℕ} (h : a = b) {v w : Fin (2 * a + k + 1) → ℂ} (e : D.castV h v = D.castV h w) : v = w := by
  subst h
  funext i
  simpa [D.castV] using congrFun e i

section tower

variable {r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem levTower_bs_z_eq_castV_liftVec (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) :
    (T.bs j).z = D.castV (by omega : 1 + (r - (j + 1)) = r - j) (liftVec k 1 (r - (j + 1)) (T.bs (j + 1)).z) := by
  have e1 := T.z_lev j (by omega)
  have e2 := T.z_lev (j + 1) hj
  rw [← lift_lift_V j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)] at e2
  have e3 := castV_inj _ (e1.trans e2.symm)
  funext i
  have hi := i.isLt
  have hi' : i.val ≤ 2 * (r - j) + k := by omega
  have := congrFun e3 ⟨i.val + j, by omega⟩
  simpa [liftVec, hi'] using this

theorem levTower_bs_z'_eq_castV_liftVec (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) :
    (T.bs j).z' = D.castV (by omega : 1 + (r - (j + 1)) = r - j) (liftVec k 1 (r - (j + 1)) (T.bs (j + 1)).z') := by
  have e1 := T.z'_lev j (by omega)
  have e2 := T.z'_lev (j + 1) hj
  rw [← lift_lift_V j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)] at e2
  have e3 := castV_inj _ (e1.trans e2.symm)
  funext i
  have hi := i.isLt
  have hi' : i.val ≤ 2 * (r - j) + k := by omega
  have := congrFun e3 ⟨i.val + j, by omega⟩
  simpa [liftVec, hi'] using this

theorem tower_π (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) (y : B.Mat k (r - (j + 1))) :
    (T.bs (j + 1)).π y = (T.bs j).π (D.castM (by omega : 1 + (r - (j + 1)) = r - j) (ιLev k 1 (r - (j + 1)) y)) := by
  rw [T.π_lev (j + 1) hj y, T.π_lev j (by omega),
    lift_lift_M j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)]

theorem tower_π' (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) (y : B.Mat k (r - (j + 1))) :
    (T.bs (j + 1)).π' y = (T.bs j).π' (D.castM (by omega : 1 + (r - (j + 1)) = r - j) (ιLev k 1 (r - (j + 1)) y)) := by
  rw [T.π'_lev (j + 1) hj y, T.π'_lev j (by omega),
    lift_lift_M j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)]

end tower

end Formalism.FourierDecayAlt.P.PBH
end
end

