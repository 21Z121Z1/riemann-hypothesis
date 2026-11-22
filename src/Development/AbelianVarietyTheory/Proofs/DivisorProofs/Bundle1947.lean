import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1927
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1928
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1929

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
section
noncomputable section

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem idem_mul_one_sub {R : Type} [CommRing R] {ε : R} (hε : ε * ε = ε) : ε * (1 - ε) = 0 := by
  rw [mul_sub, mul_one, hε, sub_self]

theorem one_sub_idem {R : Type} [CommRing R] {ε : R} (hε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  linear_combination hε

theorem idem_smul_mul {A : Type} [CommRing A] [Algebra (AF F) A] {ε : AF F} (hε : ε * ε = ε) (a b : A) :
    (ε • a + (1 - ε) • (1 : A)) * (ε • b + (1 - ε) • (1 : A)) = ε • (a * b) + (1 - ε) • (1 : A) := by
  simp only [Algebra.smul_def, mul_one]
  have he : algebraMap (AF F) A ε * algebraMap (AF F) A ε = algebraMap (AF F) A ε := by rw [← map_mul, hε]
  rw [map_sub, map_one]
  linear_combination (a * b - a - b + 1) * he

theorem idem_smul_mat_mul {A : Type} [CommRing A] [Algebra (AF F) A] {n : ℕ} {ε : AF F} (hε : ε * ε = ε)
    (G H : Matrix (Fin n) (Fin n) A) :
    (ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) A)) * (ε • H + (1 - ε) • 1) = ε • (G * H) + (1 - ε) • 1 := by
  have h1 := idem_mul_one_sub hε
  have h2 := one_sub_idem hε
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add,
    smul_smul, hε, h1, h2, mul_comm (1 - ε) ε, zero_smul, add_zero, zero_add]

theorem idem_smul_unitary {A : Type} [CommRing A] [Algebra (AF F) A] (c : A →ₐ[AF F] A) {n : ℕ} {ε : AF F}
    (hε : ε * ε = ε) {G J : Matrix (Fin n) (Fin n) A} (hG : Gᵀ * J * G.map c = J) :
    (ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) A))ᵀ * J * (ε • G + (1 - ε) • 1).map c = J := by
  have h1 := idem_mul_one_sub hε
  have h2 := one_sub_idem hε
  have hm : (ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) A)).map c = ε • G.map c + (1 - ε) • 1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, map_add, map_smul]
    split_ifs <;> simp
  rw [hm, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add,
    smul_smul, hε, h1, h2, mul_comm (1 - ε) ε, zero_smul, add_zero, zero_add]
  rw [hG, ← add_smul, add_sub_cancel, one_smul]

variable (E) in

def idemUnit (ε : AF F) (hε : ε * ε = ε) : (AE F E)ˣ →* (AE F E)ˣ where
  toFun l := ⟨ε • l.1 + (1 - ε) • 1, ε • (l⁻¹ : (AE F E)ˣ).1 + (1 - ε) • 1,
    by rw [idem_smul_mul hε, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul],
    by rw [idem_smul_mul hε, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]⟩
  map_one' := Units.ext (by simp only [Units.val_one, Units.val_mk]; rw [← add_smul, add_sub_cancel, one_smul])
  map_mul' a b := Units.ext (by simp only [Units.val_mul, Units.val_mk]; rw [idem_smul_mul hε])

theorem val_idemUnit (ε : AF F) (hε : ε * ε = ε) (l : (AE F E)ˣ) :
    (idemUnit E ε hε l : AE F E) = ε • (l : AE F E) + (1 - ε) • 1 := rfl

variable (σ) in

def idemU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : AF F) (hε : ε * ε = ε) : UA σ J →* UA σ J where
  toFun g := ⟨⟨ε • mat g + (1 - ε) • 1, ε • mat g⁻¹ + (1 - ε) • 1,
      by rw [idem_smul_mat_mul hε, GlobalTheory.StabHaar.mat_mul_inv, ← add_smul, add_sub_cancel, one_smul],
      by rw [idem_smul_mat_mul hε, show mat g⁻¹ * mat g = 1 from by
        rw [← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one], ← add_smul, add_sub_cancel, one_smul]⟩, idem_smul_unitary (cA σ) hε g.2⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    change ε • mat (1 : UA σ J) + (1 - ε) • 1 = 1
    rw [GlobalTheory.StabHaar.mat_one, ← add_smul, add_sub_cancel, one_smul]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    change ε • mat (a * b) + (1 - ε) • 1 = (ε • mat a + (1 - ε) • 1) * (ε • mat b + (1 - ε) • 1)
    rw [idem_smul_mat_mul hε, GlobalTheory.StabHaar.mat_mul]

def eFin (v : Pl F) : AF F := GlobalTheory.LatVac.liftV v 1

def eInf (F : Type) [Field F] [NumberField F] : AF F := realAd F 1

theorem eFin_idem (v : Pl F) : eFin v * eFin v = eFin v := by
  have h := GlobalTheory.LatVac.at_liftV v 1 (eFin v - 1) (by
    rw [eFin, map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem eInf_idem : eInf F * eInf F = eInf F := by
  have h := at_partInf (M := AF F) (1 : AF F) (eInf F - 1) (by
    rw [eInf, GlobalTheory.ArchUniq.evI_eq_evIHom, map_sub, map_one, ← GlobalTheory.ArchUniq.evI_eq_evIHom, evI_realAd_one, sub_self])
  simp only [partInf, smul_eq_mul, mul_one] at h
  unfold eInf at h ⊢
  rw [sub_mul, one_mul, sub_eq_zero] at h
  exact h

variable (E) in

def unitAt (v : Pl F) : (AE F E)ˣ →* (AE F E)ˣ := idemUnit E (eFin v) (eFin_idem v)

variable (F E) in

def unitArch : (AE F E)ˣ →* (AE F E)ˣ := idemUnit E (eInf F) eInf_idem

variable (σ) in

def compAt {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) : UA σ J →* UA σ J := idemU σ J (eFin v) (eFin_idem v)

variable (σ) in

def compArch {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J →* UA σ J := idemU σ J (eInf F) eInf_idem

theorem mat_compAt {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : UA σ J) :
    mat (compAt σ J v g) = eFin v • mat g + (1 - eFin v) • 1 := rfl

theorem mat_compArch {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    mat (compArch σ J g) = eInf F • mat g + (1 - eInf F) • 1 := rfl

theorem compAt_mem {n : ℕ} {X : Spc F E n} (v : Pl F) (g : UA σ X.J) : compAt σ X.J v g ∈ UAt σ X (evFin F v) := by
  intro u hu
  have h := GlobalTheory.LatVac.at_liftV v 1 u hu
  rw [mat_compAt, show eFin v • mat g + (1 - eFin v) • (1 : Matrix (Fin _) (Fin _) (AE F E)) - 1 =
    eFin v • (mat g - 1) by rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eFin v = 0 from h, zero_smul]

theorem compArch_mem {n : ℕ} {X : Spc F E n} (g : UA σ X.J) : compArch σ X.J g ∈ UAt σ X (evI F) := by
  intro u hu
  have h := at_partInf (M := AF F) (1 : AF F) u hu
  simp only [partInf, smul_eq_mul, mul_one] at h
  rw [mat_compArch, show eInf F • mat g + (1 - eInf F) • (1 : Matrix (Fin _) (Fin _) (AE F E)) - 1 =
    eInf F • (mat g - 1) by rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eInf F = 0 from h, zero_smul]

theorem unitAt_mem (v : Pl F) (l : (AE F E)ˣ) : unitAt E v l ∈ idelesAt E (evFin F v) := by
  intro u hu
  have h := GlobalTheory.LatVac.at_liftV v 1 u hu
  change u • (eFin v • (l : AE F E) + (1 - eFin v) • 1 - 1) = 0
  rw [show eFin v • (l : AE F E) + (1 - eFin v) • 1 - 1 = eFin v • ((l : AE F E) - 1) by
    rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eFin v = 0 from h, zero_smul]

theorem unitArch_mem (l : (AE F E)ˣ) : unitArch F E l ∈ idelesAt E (evI F) := by
  intro u hu
  have h := at_partInf (M := AF F) (1 : AF F) u hu
  simp only [partInf, smul_eq_mul, mul_one] at h
  change u • (eInf F • (l : AE F E) + (1 - eInf F) • 1 - 1) = 0
  rw [show eInf F • (l : AE F E) + (1 - eInf F) • 1 - 1 = eInf F • ((l : AE F E) - 1) by
    rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eInf F = 0 from h, zero_smul]

end GlobalTheory.ThK.ConeEuler
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmul
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.VacUniqInert

theorem eq_smul_of_eigen {K κ : Type} [Field K] [Fintype κ] [Invertible (2 : K)] (ψ₀ : AddChar K ℂ) {ι : Type}
    (L : ι → (κ → K) × (κ → K)) (c : ι → ℂ)
    (hD : ∀ u : κ → K, (∀ i, (L i).1 = 0 → ψ₀ (u ⬝ᵥ (L i).2) = 1) → ∃ i, (L i).1 = u)
    (f η : (κ → K) → ℂ) (hf : ∀ i, schr ψ₀ (L i) f = c i • f) (hη : ∀ i, schr ψ₀ (L i) η = c i • η)
    (hη0 : η ≠ 0) : ∃ c' : ℂ, f = c' • η := by
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, η X₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hη0 (funext h)
  have hne : ∀ t, ψ₀ t ≠ 0 := fun t h => by
    have e := AddChar.map_add_eq_mul ψ₀ t (-t)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at e
    exact one_ne_zero e
  refine ⟨f X₀ / η X₀, funext fun X => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hu : ∀ i, (L i).1 = 0 → ψ₀ ((X - X₀) ⬝ᵥ (L i).2) = 1
  · obtain ⟨i, hi⟩ := hD _ hu
    have hX : X₀ + (L i).1 = X := by rw [hi]; abel
    have e1 := congrFun (hf i) X₀
    have e2 := congrFun (hη i) X₀
    simp only [schr, Pi.smul_apply, smul_eq_mul, hX] at e1 e2
    have hA := hne (X₀ ⬝ᵥ (L i).2 + ⅟(2 : K) * ((L i).1 ⬝ᵥ (L i).2))
    field_simp
    refine mul_left_cancel₀ hA ?_
    linear_combination η X₀ * e1 - f X₀ * e2
  · push_neg at hu
    obtain ⟨i, hi0, hne1⟩ := hu
    have key : ∀ g : (κ → K) → ℂ, schr ψ₀ (L i) g = c i • g → ∀ Y, ψ₀ (Y ⬝ᵥ (L i).2) * g Y = c i * g Y := by
      intro g hg Y
      have e := congrFun hg Y
      simpa [schr, hi0] using e
    have hc : ψ₀ (X₀ ⬝ᵥ (L i).2) = c i := mul_right_cancel₀ hX₀ (key η (hη i) X₀)
    have hz : ∀ g : (κ → K) → ℂ, schr ψ₀ (L i) g = c i • g → g X = 0 := by
      intro g hg
      by_contra hgX
      have h1 : ψ₀ (X ⬝ᵥ (L i).2) = ψ₀ (X₀ ⬝ᵥ (L i).2) := by
        rw [hc]; exact mul_right_cancel₀ hgX (key g hg X)
      apply hne1
      have e : X ⬝ᵥ (L i).2 = (X - X₀) ⬝ᵥ (L i).2 + X₀ ⬝ᵥ (L i).2 := by rw [sub_dotProduct]; ring
      rw [e, AddChar.map_add_eq_mul] at h1
      exact mul_right_cancel₀ (hne _) (h1.trans (one_mul _).symm)
    rw [hz f (hf i), hz η (hη i), mul_zero]

theorem vac_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • (G.M'.vac v))) →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • G.M'.vac v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin θ _ hvac φ hφ hfix
  classical
  have hat : ∀ γ ∈ latAtV G.V' G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  let cf : latAtV G.V' G.W v → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ)
  have hloc : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (G.M'.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • f)) →
      ∀ γ : latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) f = cf γ • f := by
    intro f hf h γ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v f _ _ hf fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v γ (hat γ γ.2) f r hr).symm.trans (h γ γ.2 r hr)
  have hsd : ∀ z, z ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) ↔
      ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), GlobalTheory.LatVac.psiAt B.ψ v (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1 :=
    GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ (latAtV G.V' G.W v) hat
      (fun z hz => GlobalTheory.T.inertPlace_tensorLattice_selfDual_symplectic F E σ B hTr.base G.V' G.W _ _ _ _ hTr.geo.hV' hTr.geo.hW v w hin z hz)
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v),
      t • l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) := by
    rintro t ht _ ⟨γ, hγ, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • γ, (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).2 t ht γ hγ, ?_⟩
    rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hbd : ∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hTr.geo.hV'.lat hTr.geo.hW.lat
    exact ⟨c, hc0, by rintro _ ⟨γ, hγ, rfl⟩ i; exact (hc γ hγ i).1⟩
  have hD := GlobalTheory.T.exists_second_coordinate_of_orthogonal_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) _ hsd hst hbd
  refine eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v) (fun γ : latAtV G.V' G.W v => GlobalTheory.LatVac.locCo G.M'.co v γ) cf
    (fun u hu => ?_) φ (G.M'.vac v) (hloc φ hφ hfix) (hloc _ (hTr.geo.hM'.vac v).1 hvac) (hTr.geo.hM'.vac v).2.1
  obtain ⟨y', γ, hγ, he⟩ := hD u (by
    rintro y ⟨γ, hγ, he⟩
    have h1 := hu ⟨γ, hγ⟩ (congrArg Prod.fst he)
    have h2 : (GlobalTheory.LatVac.locCo G.M'.co v γ).2 = y := congrArg Prod.snd he
    simp only at h1
    rw [h2] at h1
    exact h1)
  exact ⟨⟨γ, hγ⟩, congrArg Prod.fst he⟩

end GlobalTheory.VacUniqInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChartStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_vacuum_isLocalVacuum_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∃ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v ∧ s ≠ 0 ∧
      GlobalTheory.Hk3.LocVac ρ s := by
  first | exact @GlobalTheory.InertBridgeVac.vac_locVac | exact GlobalTheory.InertBridgeVac.vac_locVac | (intros; apply GlobalTheory.InertBridgeVac.vac_locVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.StdPairCone

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk₁ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a) k :=
  Matrix.of fun i j => X i (Fin.castAdd a' j)

def blk₂ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a') k :=
  Matrix.of fun i j => X i (Fin.natAdd a j)

def IsGLO {n : ℕ} (g : Matrix (Fin n) (Fin n) k) : Prop := (∀ i j, g i j ∈ 𝒪[k]) ∧ valuation k g.det = 1

open Classical in

def stdA (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (X : Matrix (Fin a) (Fin (a + a')) k) : ℂ :=
  if h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0

open Classical in

def stdB (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (Y : Matrix (Fin a') (Fin (a + a')) k) : ℂ :=
  if h : (blk₂ Y).det ≠ 0 ∧ IsGLO (blk₂ Y) ∧ ∀ i j, blk₁ Y i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0

open Classical in

def unitInd (ν : kˣ →* ℂˣ) (y : k) : ℂ :=
  if h : y ≠ 0 ∧ valuation k y = 1 then (((ν (Units.mk0 y h.1))⁻¹ : ℂˣ) : ℂ) else 0

def sgn (s : ℤˣ) : kˣ := Units.map (Int.castRingHom k).toMonoidHom s

end Local

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsLocPart {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W)
    (M₁ : Model σ X₁ W₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) : Prop :=
  ei ≠ 0 ∧ (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance measFvL (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFvL (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

def coneKer (ψ : AddChar (AF F) ℂ) {v : Pl F} (t t' : E →ₐ[F] Fv F v) (ν : (Fv F v)ˣ →* ℂˣ) (μ₀ : Measure (Fv F v))
    (s₁ s₂ : ℤˣ) (l : (AE F E)ˣ) : ℂ :=
  unitInd ν (((sgn s₁ : (Fv F v)ˣ) : Fv F v) * piW t l) *
    ∫ y, unitInd ν y * psiLoc ψ v (((sgn s₂ : (Fv F v)ˣ) : Fv F v) * piW t' l * y) ∂μ₀

end Glob

end GlobalTheory.StdPairCone
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarboux
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaTransformTheta

theorem isThetaFunO_thetaTr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
          Formalism.IndefR.Datum.IsThetaFunO ψ S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ) := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hco φ hφ
  exact
    { quasi := fun γ w => GlobalTheory.T.thetaTransform_rational_translate_quasiInvariant D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ γ w
      level := GlobalTheory.T.thetaTransform_fixed_by_small_finiteHeisenberg D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ
      cont := GlobalTheory.T.continuous_thetaTransform_adelicSchwartz D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ
      smooth := fun k L hL hfin w => GlobalTheory.T.contDiff_thetaTransform_adelicSchwartz_realDirections D ψ hψ S T JA JB ξ hA hB κ co hco φ hφ k L hL hfin w }

end GlobalTheory.ThetaTransformTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalDarbouxCoordinatesBoundedStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeLocalDarbouxCoordinates_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl F, ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ latAtV G.V G.W v, ∀ k,
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).1 k ∈ HeightOneSpectrum.adicCompletionIntegers F v ∧
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).2 k ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  first | exact @GlobalTheory.LatVacBdd.locCo_bounded | exact GlobalTheory.LatVacBdd.locCo_bounded | (intros; apply GlobalTheory.LatVacBdd.locCo_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnitStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_norm_one_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : Chr F E) (v : Pl F) (τ : E →ₐ[F] Fv F v) (z : (AE F E)ˣ), At (evFin F v) ((z : AE F E) - 1) →
    piW (τ.comp σ) (z : AE F E) = 1 → chrW χ τ (Units.map (piW τ).toMonoidHom z) = Circle.toUnits (χ z) := by
  first | exact @GlobalTheory.ChrLocal.chrW_piW_eq | exact GlobalTheory.ChrLocal.chrW_piW_eq | (intros; apply GlobalTheory.ChrLocal.chrW_piW_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormUnramifiedFactorizationStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_norm_unramified_factorization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : Pl F) (τ : E →ₐ[F] Fv F v) (z : AE F E), At (evFin F v) (z - 1) →
    At (evFin F v) (Algebra.norm (AF F) z - 1) ∧ evFin F v (Algebra.norm (AF F) z) = piW τ z * piW (τ.comp σ) z := by
  first | exact @GlobalTheory.NormLocSplit.norm_at_split | exact GlobalTheory.NormLocSplit.norm_at_split | (intros; apply GlobalTheory.NormLocSplit.norm_at_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalProductActsOfAdelicProductActsFirstStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localProduct_acts_of_adelicProduct_acts_first : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  first | exact @GlobalTheory.BoxAct.boxFun_acts | exact GlobalTheory.BoxAct.boxFun_acts | (intros; apply GlobalTheory.BoxAct.boxFun_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorNormalisesSchroedingerOperatorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localWeilOperator_normalises_schroedingerOperator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (AE F E)),
      (∀ y, At (evFin F v) (Xm y)) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J) (ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v))),
      (∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)) (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ actY : Γ → Y → Y, (∀ g x, actAB (cA σ) (j g) (Xm x) = Xm (actY g x)) →
      ∀ g x, ω g * ρ x = ρ (actY g x) * ω g := by
  first | exact @GlobalTheory.InertLocModel.weil_normalises_schr | exact GlobalTheory.InertLocModel.weil_normalises_schr | (intros; apply GlobalTheory.InertLocModel.weil_normalises_schr <;> assumption)
end

