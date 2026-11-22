import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHyperbolicSwapExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
section
noncomputable section

open Matrix
open scoped Quaternion

namespace GlobalTheory.PlaneSU

open Formalism.UG

section Emb

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def emb (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R) (X : Matrix (Fin 2) (Fin 2) R) : Matrix n n R :=
  1 + A * (X - 1) * B

theorem emb_one (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R) : emb A B 1 = 1 := by
  simp [emb]

theorem emb_mul {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} (hBA : B * A = 1)
    (X Y : Matrix (Fin 2) (Fin 2) R) : emb A B (X * Y) = emb A B X * emb A B Y := by
  have e1 : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  have e2 : A * (X - 1) * B * (A * (Y - 1) * B) = A * ((X - 1) * (Y - 1)) * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]
  unfold emb
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, e2, e1,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

theorem det_emb {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} (hBA : B * A = 1)
    (X : Matrix (Fin 2) (Fin 2) R) : (emb A B X).det = X.det := by
  unfold emb
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hBA, Matrix.mul_one, add_sub_cancel]

theorem emb_map {S : Type} [CommRing S] (f : R →+* S) (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R)
    (X : Matrix (Fin 2) (Fin 2) R) : (emb A B X).map f = emb (A.map f) (B.map f) (X.map f) := by
  simp [emb, Matrix.map_mul, Matrix.map_add, Matrix.map_sub, Matrix.map_one]

theorem cT_add (c : R →+* R) {m p : Type} (P Q : Matrix m p R) : cT c (P + Q) = cT c P + cT c Q := by
  ext i j; simp [cT]

theorem cT_sub (c : R →+* R) {m p : Type} (P Q : Matrix m p R) : cT c (P - Q) = cT c P - cT c Q := by
  ext i j; simp [cT]

theorem emb_unitary (c : R →+* R) {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} {J : Matrix n n R}
    {H X : Matrix (Fin 2) (Fin 2) R} (hBA : B * A = 1) (h1 : cT c A * J = H * B) (h2 : J * A = cT c B * H)
    (hX : cT c X * H * X = H) : cT c (emb A B X) * J * emb A B X = J := by
  have hc : cT c (emb A B X) = 1 + cT c B * (cT c X - 1) * cT c A := by
    unfold emb
    rw [cT_add, cT_one, cT_mul, cT_mul, cT_sub, cT_one, Matrix.mul_assoc]
  set P := X - 1 with hP
  set P' := cT c X - 1 with hP'
  have key : H * P + P' * H + P' * H * P = 0 := by
    rw [hP, hP']
    calc H * (X - 1) + (cT c X - 1) * H + (cT c X - 1) * H * (X - 1) = cT c X * H * X - H := by noncomm_ring
      _ = 0 := by rw [hX, sub_self]
  have h1' : ∀ Z : Matrix n n R, cT c A * (J * Z) = H * (B * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h1'' : ∀ {k : Type} [Fintype k] (Z : Matrix n k R), cT c A * (J * Z) = H * (B * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h2' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), J * (A * Z) = cT c B * (H * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc]
  have hBA' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), B * (A * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [hc]
  unfold emb
  rw [← hP]
  have e : (1 + cT c B * P' * cT c A) * J * (1 + A * P * B) =
      J + cT c B * ((H * P + P' * H + P' * H * P) * B) := by
    have hAB' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), cT c A * (cT c B * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, ← cT_mul, hBA, cT_one, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, h1, h1'', h2', hBA', hAB']
    abel
  rw [e, key, Matrix.zero_mul, Matrix.mul_zero, add_zero]

end Emb

section Quat

variable {S T : Type} [CommRing S] [CommRing T]

def qm (ι : S →+* T) (θ : T) {a b : S} (x : ℍ[S, a, b]) : Matrix (Fin 2) (Fin 2) T :=
  !![ι x.re + ι x.imI * θ, ι b * (ι x.imJ + ι x.imK * θ); ι x.imJ - ι x.imK * θ, ι x.re - ι x.imI * θ]

variable (ι : S →+* T) (θ : T) {a b : S}

theorem qm_one : qm ι θ (1 : ℍ[S, a, b]) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm]

theorem qm_sub (x y : ℍ[S, a, b]) : qm ι θ (x - y) = qm ι θ x - qm ι θ y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm] <;> ring

theorem qm_smul (r : S) (x : ℍ[S, a, b]) : qm ι θ (r • x) = ι r • qm ι θ x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm] <;> ring

theorem qm_mul (hθ : θ * θ = ι a) (x y : ℍ[S, a, b]) : qm ι θ (x * y) = qm ι θ x * qm ι θ y := by
  ext i j
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  fin_cases i <;> fin_cases j <;> simp [qm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp only [hθ2] <;> ring

theorem det_qm (hθ : θ * θ = ι a) (x : ℍ[S, a, b]) : (qm ι θ x).det = ι (GlobalTheory.QSA.nrm x) := by
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  simp [qm, Matrix.det_fin_two, GlobalTheory.QSA.nrm]
  ring_nf
  simp only [hθ2]
  ring

theorem qm_unitary (c : T →+* T) (hc : ∀ s, c (ι s) = ι s) (hcθ : c θ = -θ) (hθ : θ * θ = ι a)
    {h₁ h₂ : T} (hb : ι b * h₁ = -h₂) {x : ℍ[S, a, b]} (hx : GlobalTheory.QSA.nrm x = 1) :
    cT c (qm ι θ x) * Matrix.diagonal ![h₁, h₂] * qm ι θ x = Matrix.diagonal ![h₁, h₂] := by
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  have hn : ι x.re ^ 2 - ι a * ι x.imI ^ 2 - ι b * ι x.imJ ^ 2 + ι a * ι b * ι x.imK ^ 2 = 1 := by
    have := congrArg ι hx
    simp only [GlobalTheory.QSA.nrm, map_sub, map_add, map_mul, map_pow, map_one] at this
    exact this
  have hh2 : h₂ = -(ι b * h₁) := by rw [hb, neg_neg]
  subst hh2
  ext i j
  fin_cases i <;> fin_cases j
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf; simp only [hθ2]; linear_combination h₁ * hn
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf; simp only [hθ2]; linear_combination (-(ι b * h₁)) * hn

end Quat

section Plane

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [Field E] [Algebra F E] {M : ℕ}

def planeA (e₁ e₂ : Fin M → E) : Matrix (Fin M) (Fin 2) E := Matrix.of fun i k => ![e₁, e₂] k i

def planeH (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E) : Matrix (Fin 2) (Fin 2) E :=
  Matrix.diagonal ![hE σ J e₁ e₁, hE σ J e₂ e₂]

def planeB (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E) : Matrix (Fin 2) (Fin M) E :=
  Matrix.diagonal ![(hE σ J e₁ e₁)⁻¹, (hE σ J e₂ e₂)⁻¹] * cT (σ : E →+* E) (planeA e₁ e₂) * J

end Plane

end GlobalTheory.PlaneSU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConstOfTendsto
section
noncomputable section

open MeasureTheory Filter Topology GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open Formalism.MainNotions.S (IsDS)
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.Pc1

def LocalPC4 : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ), Gap4 r lam →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X))
      (hD : IsDS ε (fun a => (lam a : ℝ)) D) (μ : Measure (UJ ε)) [μ.IsHaarMeasure],
      ∃ f, GlobalTheory.PsCo.Pc.IsPC' ε lam μ D hD f

theorem eq_of_const_of_tendsto {a L : ℂ} {u : ℝ → ℂ} (h : ∀ t, 1 ≤ t → u t = a) (hL : Tendsto u atTop (𝓝 L)) : a = L :=
  tendsto_nhds_unique (tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun t ht => (h t ht).symm)) hL

theorem injective_of_regSS {n : ℕ} {z : Fin n → ℂ} (h : IsRegSS (Matrix.diagonal z)) : Function.Injective z := by
  rw [IsRegSS, Matrix.charpoly_diagonal] at h
  exact Polynomial.separable_prod_X_sub_C_iff.1 h

theorem dMode_ne_zero {n : ℕ} (ε : Fin n → Bool) {θ : Fin n → ℝ}
    (h : Function.Injective fun a => Complex.exp (θ a * Complex.I)) : (dMode ε θ : ℂ) ≠ 0 := by
  refine Complex.ofReal_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun x _ => pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 fun e => ?_)))
  have h1 := x.2.1
  rw [h e, x.2.2] at h1
  exact Bool.noConfusion h1

theorem torusPt_mem_KG {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) : torusPt ε θ ∈ KG ε := by
  change toM (torusPt ε θ) ∈ Formalism.REAL.Kset ε
  have e : toM (torusPt ε θ) = Matrix.diagonal fun a => Complex.exp (θ a * Complex.I) := rfl
  rw [e]
  refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem localPC4_of (hAlg : StAlg) (hProf : StProfile) (hFam : StFam) (hHom : StHomot) (hLim : StLim)
    (hSh : StShape) (hOA : StOrbAd) (hOC : StOrbCpt) (hNE : StNonEll) (hTr : StTr) (hTA : StTrAd)
    (hK : StKData) : LocalPC4 := by
  intro r hr ε lam hgap X _ _ D hD μ _
  haveI := hD.1
  haveI := hD.2.1
  obtain ⟨M, P, hP, hcl, htor, hone, hzero⟩ := hK r hr ε lam hgap X D hD
  obtain ⟨p, q, hpq, htop⟩ := hAlg r ε M P hP
  obtain ⟨G, hG⟩ := hProf (nMode ε)
  obtain ⟨d, hd, hfam⟩ := hFam r ε G p hG
  obtain ⟨c, hc, hlim⟩ := hLim r ε μ G hG
  obtain ⟨hl1, hl2⟩ := hlim p
  let φ : ℝ → Mat r → ℂ := fun t => c⁻¹ • famF ε G p t
  have hφ : ∀ t, 1 ≤ t → φ t ∈ ShapeM ε d := fun t ht => Submodule.smul_mem _ _ (hfam t (by linarith)).1
  have hdiff : ∀ t, 1 ≤ t → φ 1 - φ t ∈ AdSpanM ε := fun t ht => by
    rw [← smul_sub]; exact Submodule.smul_mem _ _ (hHom r ε G p q hG hpq t ht)
  have hsum : ∀ t, (fun g : UJ ε => φ 1 (toM g)) = (fun g => φ t (toM g)) + fun g => (φ 1 - φ t) (toM g) :=
    fun t => funext fun g => by simp
  have key : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
      (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∃ (B : U →L[ℂ] U) (a : ℂ),
        (∀ v, B v = ∫ k : KG ε, ev (toMK k) (topP ε M P) • π k v ∂(muK ε)) ∧ HasTrace B a ∧
          HasTrace (repOp π μ fun g => φ 1 (toM g)) a := by
    intro U _ _ _ π hu hi
    obtain ⟨w, hw, hw1, hw2⟩ := hTr r ε μ U π hu hi d
    obtain ⟨B, hB, hBt⟩ := hw2 _ (hd _ le_rfl)
    rw [htop] at hB hBt
    refine ⟨B, _, hB, hBt, ?_⟩
    have hint : ∀ t, 1 ≤ t → Integrable (fun g : UJ ε => φ t (toM g) * w g) μ := fun t ht =>
      ((hSh r ε d _ (hφ t ht)).2.2.1.mul hw).integrable_of_hasCompactSupport (hSh r ε d _ (hφ t ht)).2.2.2.mul_right
    have hconst : ∀ t, 1 ≤ t → ∫ g, φ t (toM g) * w g ∂μ = ∫ g, φ 1 (toM g) * w g ∂μ := fun t ht => by
      have h1 := (hw1 _ (Submodule.sub_mem _ (hφ 1 le_rfl) (hφ t ht))).2
      rw [(hTA r ε μ U π hu hi _ (hdiff t ht)).2] at h1
      simp only [Pi.sub_apply, sub_mul] at h1
      rw [integral_sub (hint 1 le_rfl) (hint t ht)] at h1
      exact (sub_eq_zero.1 h1.symm).symm
    have hT := (hl1 w hw).const_mul c⁻¹
    rw [inv_mul_cancel_left₀ hc, htop] at hT
    rw [← eq_of_const_of_tendsto hconst (hT.congr fun t => by
      rw [← integral_const_mul]; simp [φ, mul_assoc])]
    exact hw1 _ (hφ 1 le_rfl)
  refine ⟨fun g => φ 1 (toM g), (hSh r ε d _ (hφ 1 le_rfl)).1, (hSh r ε d _ (hφ 1 le_rfl)).2.1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨B, a, hB, hBa, h⟩ := key X (ujRep hD.2.2.1)
      (isUnitaryRep_repVia _ _ GlobalTheory.HCChar.continuous_ujMat)
      (isTopIrreducible_repVia _ _ (fun x hx => by
        have hJ : IsUnit x := by
          have h : x.conjTranspose * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := hx
          have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
            rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
            congr 1; funext a; split_ifs <;> simp
          have h2 : (Formalism.REAL.Jm ε * x.conjTranspose * Formalism.REAL.Jm ε) * x = 1 := by
            rw [mul_assoc, mul_assoc, ← mul_assoc x.conjTranspose, h, hJ]
          exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse h2)
        exact ⟨⟨hJ.unit, hx⟩, rfl⟩) hD.2.2.2.1)
    rwa [hone B a hB hBa] at h
  · intro U _ _ _ π hu hi hne
    obtain ⟨B, a, hB, hBa, h⟩ := key U π hu hi
    rwa [hzero U π hu hi hne B a hB hBa] at h
  · intro s hs hnc dt _ _
    obtain ⟨R, hR, hx⟩ := hNE r ε s hs hnc
    have ht : (1 : ℝ) ≤ 1 + 2 / R := by have := div_pos two_pos hR; linarith
    have h0 : HasOrbInt μ s dt (fun g => φ (1 + 2 / R) (toM g)) 0 := by
      have e : conjFn s (fun g : UJ ε => φ (1 + 2 / R) (toM g)) = 0 := funext fun x => by
        have h1 : 1 < (1 + 2 / R) * rM ε (toM (x⁻¹ * s * x)) := by
          have h2 : (1 + 2 / R) * R ≤ (1 + 2 / R) * rM ε (toM (x⁻¹ * s * x)) :=
            mul_le_mul_of_nonneg_left (hx x) (by linarith)
          have h3 : (1 + 2 / R) * R = R + 2 := by field_simp
          linarith
        simp [conjFn, φ, (hfam _ (by linarith)).2 _ h1]
      rw [HasOrbInt, e]
      exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
    rw [hsum (1 + 2 / R)]
    simpa using h0.add (hOA r ε μ s hs dt _ (hdiff _ ht))
  · intro s hs hcp y θ hy dt _ _
    have hreg : IsRegSS (ujMat ε (torusPt ε θ)) := by
      rw [← hy, IsRegSS, map_mul, Matrix.charpoly_mul_comm, ← map_mul, mul_inv_cancel_left]
      exact hs
    have hinj : Function.Injective fun a => Complex.exp (θ a * Complex.I) := injective_of_regSS hreg
    have hO := fun t (ht : 1 ≤ t) => hOC r ε μ s hs hcp dt y _ (hSh r ε d _ (hφ t ht)).2.2.1 (hSh r ε d _ (hφ t ht)).2.2.2
    rw [hy] at hO
    have hconst : ∀ t, 1 ≤ t → (∫ x, φ t (toM (x⁻¹ * torusPt ε θ * x)) ∂μ) / (dt.real Set.univ : ℂ) =
        (∫ x, φ 1 (toM (x⁻¹ * torusPt ε θ * x)) ∂μ) / (dt.real Set.univ : ℂ) := fun t ht => by
      have h1 := (hO t ht).add (hOA r ε μ s hs dt _ (hdiff t ht))
      rw [← hsum t, add_zero] at h1
      exact h1.2.symm.trans (hO 1 le_rfl).2
    have hT := ((hl2 θ (torusPt ε θ) rfl hinj fun k => by
      rw [htop]; exact hcl ⟨_, torusPt_mem_KG ε θ⟩ k).const_mul c⁻¹).div_const (dt.real Set.univ : ℂ)
    rw [htop, htor θ hinj, mul_div_assoc c, inv_mul_cancel_left₀ hc, mul_div_cancel_right₀ _ (dMode_ne_zero ε hinj)] at hT
    rw [← eq_of_const_of_tendsto hconst (hT.congr fun t => by
      rw [← integral_const_mul]; simp [φ])]
    exact hO 1 le_rfl

theorem localPC_of_steps : StAlg → StProfile → StFam → StHomot → StLim → StShape → StOrbAd → StOrbCpt → StNonEll → StTr →
    StTrAd → StKData → GlobalTheory.PsCo.Pc.LocalPC :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => localPC4_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end GlobalTheory.PsCo.Pc1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeOfSmallSectionLogCountUpperBound
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNefAsymp

theorem tendsto_log_nat_div : Tendsto (fun m : ℕ => Real.log m / m) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  refine h.congr' (Eventually.of_forall fun m => ?_)
  simp

theorem tendsto_log_sq_div {X : ℕ → ℝ} {D : ℕ} {L : ℝ} (h1 : ∀ m, 1 ≤ X m)
    (hX : Tendsto (fun m : ℕ => X m / (m : ℝ) ^ (D + 1)) atTop (𝓝 L)) :
    Tendsto (fun m : ℕ => Real.log (X m ^ 2) / m) atTop (𝓝 0) := by
  set C : ℝ := max (L + 1) 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  have hev : ∀ᶠ m : ℕ in atTop, X m / (m : ℝ) ^ (D + 1) < C :=
    hX.eventually (gt_mem_nhds (lt_of_lt_of_le (lt_add_one L) (le_max_left _ _)))
  have hup : Tendsto (fun m : ℕ => 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => 2 * Real.log C * (m : ℝ)⁻¹) atTop (𝓝 (2 * Real.log C * 0)) :=
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _
    have h2 := tendsto_log_nat_div.const_mul (2 * ((D : ℝ) + 1))
    have := h1.add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun m => ?_)
    simp [div_eq_mul_inv]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · refine Eventually.of_forall fun m => ?_
    exact div_nonneg (Real.log_nonneg (by nlinarith [h1 m])) (Nat.cast_nonneg m)
  · filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hP : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm0 _
    have hXle : X m ≤ C * (m : ℝ) ^ (D + 1) := by
      rw [div_lt_iff₀ hP] at hm; exact hm.le
    have hX0 : 0 < X m := lt_of_lt_of_le one_pos (h1 m)
    have hlog : Real.log (X m) ≤ Real.log C + ((D : ℝ) + 1) * Real.log m := by
      have := Real.log_le_log hX0 hXle
      rw [Real.log_mul (by positivity) hP.ne', Real.log_pow] at this
      push_cast at this
      linarith
    rw [Real.log_pow]
    rw [show 2 * Real.log C / m + (2 * ((D : ℝ) + 1)) * (Real.log m / m)
        = (2 * (Real.log C + ((D : ℝ) + 1) * Real.log m)) / m by ring]
    apply div_le_div_of_nonneg_right _ hm0.le
    push_cast
    linarith

theorem tendsto_bound_div (D q : ℕ) (hq : 3 ≤ q) {β g : ℕ → ℝ} {a γ : ℝ} (hβ0 : ∀ m, 0 ≤ β m)
    (hg0 : ∀ m, 0 ≤ g m) (hβ : Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a))
    (hg : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ)) :
    Tendsto (fun m : ℕ => bound D q (β m) (g m) / (m : ℝ) ^ (D + 1)) atTop
      (𝓝 (Real.log q * (a / (((D + 1).factorial : ℝ) * Real.log ((q : ℝ) / 2))))) := by
  set Δ : ℝ := Real.log ((q : ℝ) / 2) with hΔdef
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hΔ : 0 < Δ := Real.log_pos (by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith)
  have hF : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have hFΔ : 0 < F * Δ := mul_pos hF hΔ
  set c1 : ℝ := ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2) with hc1
  have hc1p : 0 ≤ c1 := mul_nonneg (by positivity)
    (add_nonneg hΔ.le (div_nonneg (mul_nonneg (Nat.cast_nonneg D) (Real.log_nonneg one_le_two)) zero_le_two))
  set A : ℕ → ℝ := fun m => (β m + c1 * g m) / (F * Δ) with hA
  set B : ℕ → ℝ := fun m => ((D : ℝ) + 1) * g m / (2 * (F * Δ)) with hB
  have hunf : ∀ m, bound D q (β m) (g m) = Real.log q * (A m + B m * Real.log ((A m + 2 * B m + 1) ^ 2)) :=
    fun m => rfl
  have hinv := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hgP : Tendsto (fun m : ℕ => g m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := hg.mul hinv
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by ring)
  have hAP : Tendsto (fun m : ℕ => A m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (a / (F * Δ))) := by
    have := (hβ.add (hgP.const_mul c1)).div_const (F * Δ)
    rw [mul_zero, add_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hA]; ring)
  have hBP : Tendsto (fun m : ℕ => B m / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := hgP.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)
  have hA0 : ∀ m, 0 ≤ A m := fun m => div_nonneg (add_nonneg (hβ0 m) (mul_nonneg hc1p (hg0 m))) hFΔ.le
  have hB0 : ∀ m, 0 ≤ B m := fun m => div_nonneg (mul_nonneg (by positivity) (hg0 m)) (by positivity)
  have hX1 : ∀ m, 1 ≤ A m + 2 * B m + 1 := fun m => by linarith [hA0 m, hB0 m]
  have hXP : Tendsto (fun m : ℕ => (A m + 2 * B m + 1) / (m : ℝ) ^ (D + 1)) atTop
      (𝓝 (a / (F * Δ) + 2 * 0 + 0 ^ (D + 1))) := by
    have := (hAP.add (hBP.const_mul 2)).add (hinv.pow (D + 1))
    exact this.congr' (Eventually.of_forall fun m => by ring)
  have hlog := tendsto_log_sq_div hX1 hXP
  have h2 : Tendsto (fun m : ℕ => B m * Real.log ((A m + 2 * B m + 1) ^ 2) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
    have := ((hg.const_mul (((D : ℝ) + 1) / (2 * (F * Δ)))).mul hlog)
    rw [mul_zero] at this
    exact this.congr' (Eventually.of_forall fun m => by simp only [hB]; ring)
  have := (hAP.add h2).const_mul (Real.log q)
  rw [add_zero] at this
  exact this.congr' (Eventually.of_forall fun m => by show _ = bound D q (β m) (g m) / _; rw [hunf]; ring)

theorem eventually_le_of_bound : ∀ (D : ℕ) (u β g : ℕ → ℝ) (a γ : ℝ), (∀ m, 0 ≤ β m) → (∀ m, 0 ≤ g m) →
    Tendsto (fun m : ℕ => β m / (m : ℝ) ^ (D + 1)) atTop (𝓝 a) →
    Tendsto (fun m : ℕ => g m / (m : ℝ) ^ D) atTop (𝓝 γ) →
    (∀ m q, 3 ≤ q → u m ≤ bound D q (β m) (g m)) → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ m : ℕ in atTop, u m ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro D u β g a γ hβ0 hg0 hβ hg hu ε hε
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have ha : 0 ≤ a := ge_of_tendsto' hβ (fun m => div_nonneg (hβ0 m) (by positivity))
  set K : ℝ := Real.log 2 * a / (F * ε) with hK
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.exp K)
  set q : ℕ := max n 3 with hqdef
  have hq3 : 3 ≤ q := le_max_right _ _
  have hqn : (n : ℝ) ≤ q := by exact_mod_cast le_max_left n 3
  have hq3r : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hKΔ : K < Real.log ((q : ℝ) / 2) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith
  have hΔ : 0 < Real.log ((q : ℝ) / 2) := Real.log_pos (by linarith)
  have hlogq : Real.log q = Real.log ((q : ℝ) / 2) + Real.log 2 := by
    rw [Real.log_div hq0.ne' two_ne_zero]; ring
  have hL : Real.log q * (a / (F * Real.log ((q : ℝ) / 2))) < a / F + ε := by
    have e : Real.log q * (a / (F * Real.log ((q : ℝ) / 2)))
        = a / F + Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) := by
      rw [hlogq]; field_simp
    rw [e]
    have h1 : Real.log 2 * a < Real.log ((q : ℝ) / 2) * (F * ε) := by
      rw [hK, div_lt_iff₀ (mul_pos hF hε)] at hKΔ; exact hKΔ
    have h2 : Real.log 2 * a / (F * Real.log ((q : ℝ) / 2)) < ε := by
      rw [div_lt_iff₀ (mul_pos hF hΔ)]; nlinarith
    linarith
  have ht := tendsto_bound_div D q hq3 hβ0 hg0 hβ hg
  filter_upwards [ht.eventually (gt_mem_nhds hL), eventually_ge_atTop 1] with m hm hm1
  have hP : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast hm1) _
  rw [div_lt_iff₀ hP] at hm
  exact (hu m q hq3).trans hm.le

end GlobalTheory.HSNefAsymp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithFrobeniusEmbeddingPermCmConjStatement
section
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithFrobenius_embedding_perm_cmConj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime], ¬ (l : ℤ) ∣ NumberField.discr E → ∃ σ : Equiv.Perm (E →+* PadicAlgCl l), IsFrobPerm σ ∧ ∀ τ, σ (cj τ) = cj (σ τ) := by
  first | exact @GlobalTheory.FrobEmb.exists_frobPerm | exact GlobalTheory.FrobEmb.exists_frobPerm | (intros; apply GlobalTheory.FrobEmb.exists_frobPerm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHermitianSignatureStatement
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_hermitianSignature : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  first | exact @GlobalTheory.PlaneSkew.CartanInv.exists_isCartan | exact GlobalTheory.PlaneSkew.CartanInv.exists_isCartan | (intros; apply GlobalTheory.PlaneSkew.CartanInv.exists_isCartan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionHyperbolicSwapExtensionStatement
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_hyperbolicSwap_extension : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), M.conjTranspose = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y = Complex.I →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    IsCartan (ιᵀ * M * ι.map star) θ₁ →
    ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ ∃ c : ℂ, c ≠ 0 ∧ Y = c • θ *ᵥ X := by
  first | exact @GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap | exact GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap | (intros; apply GlobalTheory.PlaneCartan.exists_cartan_hyperbolic_swap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInfStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity : ∀ (F : Type) [Field F] [NumberField F] (lam : (AF F)ˣ →* Circle), Continuous lam →
    (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) → ∃ M : ℕ, 0 < M ∧ ∀ b : (AF F)ˣ,
      (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1 := by
  first | exact @GlobalTheory.HeckeExtend.exists_cong_ker | exact GlobalTheory.HeckeExtend.exists_cong_ker | (intros; apply GlobalTheory.HeckeExtend.exists_cong_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjIntegralGaloisRepStatement
section
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_integral_galoisRep : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)), Continuous r → (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) → ∃ A : GL (Fin n) (PadicAlgCl l), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ i j, ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ g i j, ‖((A⁻¹ * r g * A : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ 1 := by
  first | exact @GlobalTheory.GalIntegral.exists_conj_integral | exact GlobalTheory.GalIntegral.exists_conj_integral | (intros; apply GlobalTheory.GalIntegral.exists_conj_integral <;> assumption)
end

