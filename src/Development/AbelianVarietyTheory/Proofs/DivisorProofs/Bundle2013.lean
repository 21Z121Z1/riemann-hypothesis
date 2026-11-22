import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsAlt
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0008
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1844
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBump
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.KirSemi

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem gl_af_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w => ?_))
  exact congrArg (fun x : GL (Fin a) (w.adicCompletion E) => x.1 i j) (H w)

theorem map_loc_fin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comm_of_supp (S : Finset (HeightOneSpectrum (𝓞 E))) {s t : GA E a} (hs : s ∈ supS E a S)
    (h1 : GeneralLinearGroup.map (pInf E) t = 1)
    (h2 : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) : s * t = t * s := by
  apply ga_ext
  · simp [map_mul, h1]
  · apply gl_af_ext
    intro w
    simp only [map_mul, map_loc_fin]
    by_cases hw : w ∈ S
    · rw [h2 w hw]; simp
    · rw [hs w hw]; simp

theorem supS_mul (S : Finset (HeightOneSpectrum (𝓞 E))) {x y : GA E a} (hx : x ∈ supS E a S)
    (hy : y ∈ supS E a S) : x * y ∈ supS E a S := by
  intro w hw
  rw [map_mul, hx w hw, hy w hw, one_mul]

theorem whit_rt (F : GA E a → ℂ) (h g : GA E a) : whit (fun y => F (y * h)) g = whit F (g * h) := by
  simp only [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker, mul_assoc]

theorem ratGL_scalar_val (α : Eˣ) :
    ((ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) : GA E a) :
      Matrix (Fin a) (Fin a) (Ad E)) = Matrix.scalar (Fin a) (algebraMap E (Ad E) (α : E)) := by
  ext i j
  by_cases h : i = j <;> simp [ratGL, Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem aut_central {φ : Sm E a} (hφ : IsAutForm φ) (α : Eˣ) (g : GA E a) :
    φ.1 (g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α)) = φ.1 g := by
  have hc : g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) =
      ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) * g := by
    apply Units.ext
    simp only [Units.val_mul, ratGL_scalar_val]
    exact ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _)).symm
  rw [hc, hφ.left]

theorem exists_mirabolic_nonzero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ ψ ∈ π.V, (∃ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit ψ.1 p ≠ 0) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, ψ.1 (g * k) = ψ.1 g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit ψ.1 (x * t) = c * GlobalTheory.JSW.whit ψ.1 x := by
  intro E _ _ _ m S π φ hφ ⟨x, hxS, hx⟩
  have haut : IsAutForm φ := (π.cusp φ hφ).1
  set xf := GeneralLinearGroup.map (pFin E) x with hxf
  obtain ⟨p0, ρ, k, hp0, hy⟩ := GlobalTheory.T.exists_mirabolic_scalar_unitary_decomposition_archimedean E m (GeneralLinearGroup.map (pInf E) x)
  let sc : (Cinf E)ˣ →* GL (Fin (m + 1)) (Cinf E) :=
    Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom
  have hsc : Continuous sc := by
    apply Continuous.units_map
    show Continuous (fun c : Cinf E => Matrix.scalar (Fin (m + 1)) c)
    simp only [Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  let ζ : (Cinf E)ˣ → ℂ := fun c =>
    whit φ.1 (infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf)
  have hζc : Continuous ζ :=
    (GlobalTheory.T.continuous_globalWhittakerCoefficient_archimedean E (m + 1) φ haut _ _).comp (hsc.mul continuous_const)
  have hζρ : ζ ρ ≠ 0 := by
    have hx' : infGL E (m + 1) p0 * infGL E (m + 1) (sc ρ * Unitary.toUnits k) * finGL E (m + 1) xf = x := by
      rw [← map_mul, ← mul_assoc]
      rw [show p0 * sc ρ * Unitary.toUnits k = GeneralLinearGroup.map (pInf E) x from hy.symm]
      exact infGL_mul_finGL x
    show whit φ.1 _ ≠ 0
    rw [hx']
    exact hx
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_field_unit_mem_open_archimedean_units E {c | ζ c ≠ 0} (isOpen_ne_fun hζc continuous_const) ⟨ρ, hζρ⟩
  set c := Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β with hc
  let zE : GL (Fin (m + 1)) E := Units.map (Matrix.scalar (Fin (m + 1)) : E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) E).toMonoidHom β⁻¹
  set s := infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf with hs
  have hcen : ∀ g : GL (Fin (m + 1)) (Cinf E), sc c * g = g * sc c := by
    intro g
    apply Units.ext
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _
  have hzinf : GeneralLinearGroup.map (pInf E) (ratGL E (m + 1) zE) = (sc c)⁻¹ := by
    have hci : (sc c)⁻¹ = sc (Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹) := by
      simp only [hc, map_inv]
    rw [hci]
    apply Units.ext
    show ((ratGL E (m + 1) zE : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map (pInf E) =
      Matrix.scalar (Fin (m + 1)) (((Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹ : (Cinf E)ˣ)) : Cinf E)
    rw [ratGL_scalar_val]
    simp [Matrix.scalar_apply, Matrix.diagonal_map]
    funext v
    simp [pInf_algebraMap, map_inv₀]
  set z := GeneralLinearGroup.map (pFin E) (ratGL E (m + 1) zE) with hz
  have hsz : s * ratGL E (m + 1) zE = infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z) := by
    apply ga_ext
    · simp only [hs, map_mul, pInf_infGL, hzinf]
      simp
      rw [hcen]; group
    · simp [hs, hz, mul_assoc]
  let ψ : Sm E (m + 1) := act (Op.cpt k) (act (Op.fin (xf * z)) φ)
  have hψV : ψ ∈ π.V := π.stable _ _ (π.stable _ _ hφ)
  have hψ : ∀ g, ψ.1 g = φ.1 (g * s) := by
    intro g
    have h0 : ψ.1 g = φ.1 (g * infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z)) := rfl
    rw [h0, mul_assoc, ← hsz, ← mul_assoc, aut_central haut β⁻¹]
  have hψf : ψ.1 = fun g => φ.1 (g * s) := funext hψ
  have hsS : s ∈ supS E (m + 1) S := by
    intro w hw
    rw [← map_loc_fin, hs, map_mul, pFin_infGL, pFin_finGL, one_mul, hxf, map_loc_fin]
    exact hxS w hw
  refine ⟨ψ, hψV, ⟨infGL E (m + 1) p0, ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro w hw
    rw [← map_loc_fin]
    simp
  · intro j
    have h1 : pInf E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        (p0 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Cinf E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j)
        (pInf_infGL (E := E) p0)
    have h2 : pFin E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        ((1 : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Af E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j)
        (pFin_infGL (E := E) p0)
    rw [hp0 j] at h1
    apply ad_ext
    · rw [h1]; split_ifs <;> simp
    · rw [h2]; split_ifs with h <;> simp [Matrix.one_apply, h, eq_comm]
  · rw [hψf, whit_rt]
    have : infGL E (m + 1) p0 * s = infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf := by
      rw [hs, mul_assoc]
    rw [this]
    exact hβ
  · intro k' h1 h2 hk g
    rw [hψ, hψ, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc, hk]
  · intro t c' h1 h2 hrel y hy
    rw [hψf, whit_rt, whit_rt, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc]
    exact hrel (y * s) (supS_mul S hy hsS)

theorem kirillov_semilocal_bump : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ t : GA E (m + 1), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ g, φ.1 (g * t) = φ.1 g) → ∀ g, F (g * t) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ m S b hb hC hU hsm π φ hφ hx
  obtain ⟨ψ, hψ, hp, hk, hrel⟩ := exists_mirabolic_nonzero E m S π φ hφ hx
  obtain ⟨F, hF, hFb, hFU, hFk, hFrel⟩ := GlobalTheory.T.kirillov_semilocal_mirabolic_whittaker E m S b hb hC hU hsm π ψ hψ hp
  exact ⟨F, hF, hFb, hFU, fun k h1 h2 h3 => hFk k h1 h2 (hk k h1 h2 h3),
    fun t c h1 h2 h3 => hFrel t c h1 h2 (hrel t c h1 h2 h3)⟩

end GlobalTheory.JSW.KirSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviConjScalarIdeleUnipotentCoordinates
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section

namespace GlobalTheory.ResidueEisenstein.LeviConj

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cT_smul' (s : AF F ⊗[F] E →+* AF F ⊗[F] E) {p q : Type} (a : AF F ⊗[F] E) (M : Matrix p q (AF F ⊗[F] E)) :
    cT s (a • M) = s a • cT s M := by
  ext i k; simp [cT]

theorem det_conj_mul_det (s : AF F ⊗[F] E →+* AF F ⊗[F] E) {k : ℕ} (M K : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))
    (hK : IsUnit K.det) (h : cT s M * K * M = K) : s M.det * M.det = 1 := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have e : (cT s M).det = s M.det := by
    rw [cT, Matrix.det_transpose]; exact (RingHom.map_det s M).symm
  rw [e] at hd
  apply hK.mul_right_cancel
  rw [one_mul]; nth_rewrite 2 [← hd]; ring

open GlobalTheory.SphEis.UnipCrd in

theorem crd_conj_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (l : (AF F ⊗[F] E)ˣ) (γ : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F C = (l : AF F ⊗[F] E) • adMat F C → (matHom _ σ J g).1 * adMat F D = adMat F D * γ → ∃ δ : GL (Fin m) (AF F ⊗[F] E), absE F E (Matrix.GeneralLinearGroup.det δ) = 1 ∧ δ.1 * adMat F J₀⁻¹ * cT (sigR (AF F) σ) δ.1 = adMat F J₀⁻¹ ∧ ∀ u b c, GlobalTheory.SphEis.Crd σ J C D Z J₀ u b c → GlobalTheory.SphEis.Crd σ J C D Z J₀ (g * u * g⁻¹) ((l : AF F ⊗[F] E) • (b * δ.1)) (((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • c) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g l γ hC hD
  set s := sigR (AF F) σ with hs
  set G := (matHom _ σ J g).1 with hG
  have hU : cT s G * adMat F J * G = adMat F J := g.2
  have pres : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) (AF F ⊗[F] E)) (Y : Matrix (Fin n) (Fin q) (AF F ⊗[F] E)),
      cT s (G * X) * adMat F J * (G * Y) = cT s X * adMat F J * Y := by
    intro p q X Y
    rw [Formalism.UG.cT_mul]
    calc cT s X * cT s G * adMat F J * (G * Y) = cT s X * (cT s G * adMat F J * G) * Y := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]
  have g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 →
      cT s (adMat F X) * adMat F J * adMat F Y = 0 := by
    intro p q X Y h; have := gr_adMat (F := F) σ J X Y; rw [h] at this; simpa [gr] using this
  have hcd : cT s (adMat F C) * adMat F J * adMat F D = 1 := by
    have := gr_adMat (F := F) σ J C D; rw [hF.cd] at this; simpa [gr] using this
  have hzz : cT s (adMat F Z) * adMat F J * adMat F Z = adMat F J₀ := by
    have := gr_adMat (F := F) σ J Z Z; rw [hF.zz] at this; simpa [gr] using this
  have hcz := g0 C Z hF.cz
  have hdz := g0 D Z hF.dz
  have linv : (l : AF F ⊗[F] E) * ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 := Units.mul_inv l
  have sinv : s (l : AF F ⊗[F] E) * s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 := by rw [← map_mul, linv, map_one]
  have ssl : ∀ x, s (s x) = x := sigR_invol σ hF.cm

  have hγ : γ = s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • 1 := by
    have e := pres (adMat F C) (adMat F D)
    rw [hC, hD, hcd, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc, hcd,
      Matrix.one_mul] at e
    calc γ = (s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * s (l : AF F ⊗[F] E)) • γ := by rw [mul_comm, sinv, one_smul]
      _ = _ := by rw [← smul_smul, e]

  have hcgz : cT s (adMat F C) * adMat F J * (G * adMat F Z) = 0 := by
    have e := pres (adMat F C) (adMat F Z)
    rw [hC, hcz, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Matrix.smul_mul, Matrix.smul_mul] at e
    calc _ = (s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * s (l : AF F ⊗[F] E)) •
          (cT s (adMat F C) * adMat F J * (G * adMat F Z)) := by rw [mul_comm, sinv, one_smul]
      _ = 0 := by rw [← smul_smul, e, smul_zero]
  have cTγ : cT s γ = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • 1 := by
    rw [hγ, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', ssl, Formalism.UG.cT_one]
  have hdgz : cT s (adMat F D) * adMat F J * (G * adMat F Z) = 0 := by
    have e := pres (adMat F D) (adMat F Z)
    rw [hD, hdz, Formalism.UG.cT_mul, cTγ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul] at e
    calc _ = ((l : AF F ⊗[F] E) * ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) •
          (cT s (adMat F D) * adMat F J * (G * adMat F Z)) := by rw [linv, one_smul]
      _ = 0 := by rw [← smul_smul, e, smul_zero]
  have hsum : adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J))
      + adMat F D * (cT s (adMat F C) * adMat F J) = 1 := by
    have := congrArg (fun M => adMat F M) hF.sum
    simp only [adMat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [cT_adMat, cT_adMat, cT_adMat]
    simpa only [adMat] using this
  obtain ⟨δ₀, hδ₀⟩ : ∃ X, X = adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J * (G * adMat F Z)) := ⟨_, rfl⟩
  have hGZ : G * adMat F Z = adMat F Z * δ₀ := by
    calc G * adMat F Z = (adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J))
      + adMat F D * (cT s (adMat F C) * adMat F J)) * (G * adMat F Z) := by rw [hsum, Matrix.one_mul]
      _ = _ := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
        simp only [← Matrix.mul_assoc (cT s (adMat F D)), ← Matrix.mul_assoc (cT s (adMat F C)),
          ← Matrix.mul_assoc (cT s (adMat F Z))]
        rw [hdgz, hcgz, Matrix.mul_zero, Matrix.mul_zero, zero_add, add_zero, hδ₀]
  have hδu : cT s δ₀ * adMat F J₀ * δ₀ = adMat F J₀ := by
    have e := pres (adMat F Z) (adMat F Z)
    rw [hGZ, hzz, Formalism.UG.cT_mul] at e
    calc cT s δ₀ * adMat F J₀ * δ₀ = cT s δ₀ * (cT s (adMat F Z) * adMat F J * adMat F Z) * δ₀ := by rw [hzz]
      _ = _ := by rw [← e]; simp only [Matrix.mul_assoc]

  have hu0 : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have jj : adMat F J₀⁻¹ * adMat F J₀ = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu0, Matrix.map_one _ (map_zero _) (map_one _)]
  have jj' : adMat F J₀ * adMat F J₀⁻¹ = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ0 : cT s (adMat F J₀) = adMat F J₀ := by
    rw [cT_adMat]; congr 1; ext i k; simp [Formalism.UG.cT, hF.herm₀.1]
  have hJ0i : cT s (adMat F J₀⁻¹) = adMat F J₀⁻¹ := by
    rw [cT_adMat, cT_inv_herm σ J₀ hF.herm₀]
  have hK : IsUnit (adMat F J₀).det := by
    rw [show (adMat F J₀).det = inclR (F := F) (AF F) J₀.det from (RingHom.map_det _ _).symm]; exact hu0.map _
  obtain ⟨δi, hδi⟩ : ∃ X, X = adMat F J₀⁻¹ * cT s δ₀ * adMat F J₀ := ⟨_, rfl⟩
  have hl : δi * δ₀ = 1 := by
    rw [hδi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s δ₀), hδu, jj]
  have hr : δ₀ * δi = 1 := mul_eq_one_comm.mp hl
  let δ : GL (Fin m) (AF F ⊗[F] E) := ⟨δi, δ₀, hl, hr⟩
  have hδval : δ.1 = δi := rfl
  have hiu : cT s δi * adMat F J₀ * δi = adMat F J₀ := by
    calc cT s δi * adMat F J₀ * δi = cT s δi * (cT s δ₀ * adMat F J₀ * δ₀) * δi := by rw [hδu]
      _ = cT s (δ₀ * δi) * adMat F J₀ * (δ₀ * δi) := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hr, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  have cTδi : cT s δi = adMat F J₀ * δ₀ * adMat F J₀⁻¹ := by
    rw [hδi, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJ0, hJ0i, cT_cT σ hF.cm, Matrix.mul_assoc]
  have key : δ₀ * adMat F J₀⁻¹ = adMat F J₀⁻¹ * cT s δi := by
    rw [cTδi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jj, Matrix.one_mul]
  refine ⟨δ, ?_, ?_, ?_⟩
  · have h1 := GlobalTheory.ResidueEisenstein.LeviConj.det_conj_mul_det s δi (adMat F J₀) hK hiu
    have hu : GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det δ) * Matrix.GeneralLinearGroup.det δ = 1 := by
      ext
      show sigR (AF F) σ _ * _ = 1
      exact h1
    have h2 := congrArg (absE F E) hu
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
    exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2
  · rw [hδval, Matrix.mul_assoc, ← key, hδi]
    calc adMat F J₀⁻¹ * cT s δ₀ * adMat F J₀ * (δ₀ * adMat F J₀⁻¹)
        = adMat F J₀⁻¹ * (cT s δ₀ * adMat F J₀ * δ₀) * adMat F J₀⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hδu, jj, Matrix.one_mul]
  · intro u b c hu
    set Gi := (matHom _ σ J g⁻¹).1 with hGi
    have hGiG : Gi * G = 1 := by
      rw [hGi, hG, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have iC : Gi * adMat F C = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • adMat F C := by
      have e : adMat F C = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (G * adMat F C) := by
        rw [hC, smul_smul, Units.inv_mul, one_smul]
      conv_lhs => rw [e]
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have iZ : Gi * adMat F Z = adMat F Z * δi := by
      have e : adMat F Z = G * adMat F Z * δi := by rw [hGZ, Matrix.mul_assoc, hr, Matrix.mul_one]
      conv_lhs => rw [e]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have hGD : G * adMat F D = s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • adMat F D := by
      rw [hD, hγ, Matrix.mul_smul, Matrix.mul_one]
    have iD : Gi * adMat F D = s (l : AF F ⊗[F] E) • adMat F D := by
      have e : adMat F D = s (l : AF F ⊗[F] E) • (G * adMat F D) := by
        rw [hGD, smul_smul, sinv, one_smul]
      conv_lhs => rw [e]
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have hplus : adMat F Z * GlobalTheory.SphEis.plus σ J₀ ((l : AF F ⊗[F] E) • (b * δi)) =
        s (l : AF F ⊗[F] E) • (G * (adMat F Z * GlobalTheory.SphEis.plus σ J₀ b)) := by
      simp only [GlobalTheory.SphEis.plus]
      rw [GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Formalism.UG.cT_mul, ← Matrix.mul_assoc G, hGZ, Matrix.mul_smul, Matrix.mul_smul]
      congr 1
      rw [← hs, ← Matrix.mul_assoc (adMat F J₀⁻¹), ← key]; simp only [Matrix.mul_assoc]
    have hm : (matHom _ σ J (g * u * g⁻¹)).1 = G * (matHom _ σ J u).1 * Gi := by
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm]
      calc G * (matHom _ σ J u).1 * Gi * adMat F C
          = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (G * ((matHom _ σ J u).1 * adMat F C)) := by
            rw [Matrix.mul_assoc, iC, Matrix.mul_smul, Matrix.mul_assoc]
        _ = adMat F C := by rw [hu.onC, hC, smul_smul, Units.inv_mul, one_smul]
    · rw [hm, hδval]
      calc G * (matHom _ σ J u).1 * Gi * adMat F Z = G * ((matHom _ σ J u).1 * adMat F Z) * δi := by
            rw [Matrix.mul_assoc, iZ, ← Matrix.mul_assoc, Matrix.mul_assoc G]
        _ = _ := by
            rw [hu.onZ, Matrix.mul_add, ← Matrix.mul_assoc G (adMat F C), hGZ, hC, Matrix.add_mul, Matrix.mul_assoc,
              hr, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    · rw [hm, hδval, hplus]
      calc G * (matHom _ σ J u).1 * Gi * adMat F D
          = s (l : AF F ⊗[F] E) • (G * ((matHom _ σ J u).1 * adMat F D)) := by
            rw [Matrix.mul_assoc, iD, Matrix.mul_smul, Matrix.mul_assoc]
        _ = s (l : AF F ⊗[F] E) • (G * adMat F D - G * (adMat F Z * GlobalTheory.SphEis.plus σ J₀ b) + G * (adMat F C * c)) := by
            rw [hu.onD, Matrix.mul_add, Matrix.mul_sub]
        _ = _ := by
            rw [hGD, ← Matrix.mul_assoc G (adMat F C), hC]
            simp only [smul_add, smul_sub, smul_smul, sinv, one_smul, Matrix.smul_mul, Matrix.mul_smul]
            rw [mul_comm (s (l : AF F ⊗[F] E))]

end GlobalTheory.ResidueEisenstein.LeviConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntegralRatioOfHyp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open GlobalTheory.SumSize.TopInt
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pair_integral_ratio_of_norm_sums : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → GlobalTheory.SumSize.PairInt.PairIntRatK := by
  intro hP hI hD
  obtain ⟨C1, hC1, hPL⟩ := UpperTheory.WildA.ker
  obtain ⟨C0, hC0, hS⟩ := UpperTheory.WildA.lossOne C1 hC1
  obtain ⟨CF2, hD⟩ := hD
  refine ⟨CF2, fun CF hCF => ?_⟩
  obtain ⟨C02, hD⟩ := hD CF hCF
  refine ⟨max C0 C02, fun ε C hC => ?_⟩
  obtain ⟨x2, hD⟩ := hD ε C (le_of_max_le_right hC)
  refine ⟨x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hch hsc hfo => ?_⟩
  have dict : DictAt ch := hD D large₂ he hx Γ Pl0 T A Ks R F hs ch hch hsc hfo
  obtain ⟨S, δ, hL⟩ := (GlobalTheory.NormSum.letters_and_sizes D (hI D).g1).1
  have hgap : ch.sc.cGap = 1 := by
    have e : ch.sc = ⟨1, CF, large₂.sc.b⟩ := hsc
    rw [e]
  obtain ⟨S', h, hE, hh⟩ := hS (G := ch.G) large₂ hs.size hs.host hgap S δ hL
  obtain ⟨l1, l2, l3⟩ := UpperTheory.WildA.expLoss D S' h _ hE
  obtain ⟨-, -, -, -, hm2, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs.size
  refine ⟨_, ⟨l1, l2, fun s => (l3 s).trans ?_⟩, ?_⟩
  · have hlog : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
    have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have hCC : C0 ≤ C := le_of_max_le_left hC
    have h1 : C0 ≤ C * D.R.m := by nlinarith
    have h2 : (0 : ℝ) ≤ D.R.f * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b := by
      have : (0 : ℝ) ≤ large₂.sc.b := by linarith
      positivity
    have := mul_le_mul_of_nonneg_right h1 h2
    unfold bOne
    linarith
  · intro t p hp w hw k d hk hcos hz hPl hdep x y hr a v hv
    have key := hPL D large₂ Γ Pl0 T A Ks R F hs ch CF hch hsc hfo hP (hI D) dict S δ hL t p hp k d hk hcos hz hPl x y hr
      w (primeUnder w) (primeUnder_prime w) (primeUnder_mem w) hw a v hv
    refine inLat_mono key ?_
    have h1 := kerLoss_mono ch.G δ C1 large₂.sc.b p.small p.big (primeUnder w)
      (hdep _ (primeUnder_prime w) (primeUnder_mem w))
    have h2 := (mul_le_mul_of_nonneg_left h1 hC1.le).trans (hh p hp _ (primeUnder_prime w))
    have h0 : (0 : ℝ) ≤ (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) := by exact_mod_cast vw_natCast_nonneg w _
    have h3 := mul_le_mul_of_nonneg_left h2 h0
    rw [mul_assoc]
    linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PublishedLocalTheoryConsequence
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

namespace GlobalTheory.MultEqHead

theorem multEq_of_classicalTheorems :
    GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.PseudoCoefficientUpq → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.CuspMult.MultEq R := by
  intro hHCA hDSC hCRD hHCF hCTC hDMF hFF hPC hHCC hLC hLW hZPR hGL hGC
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG
  exact GlobalTheory.T.cuspidal_trace_multiplicity_given hCRD hHCF hDMF hGC
    (GlobalTheory.T.published_inputs_imply_trace_formula hHCA hDSC hCRD hHCF hCTC hDMF hFF hPC hHCC hLC hLW hZPR hGL) R F hG

end GlobalTheory.MultEqHead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_line_polynomial_equivariance : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → (∀ γ ∈ Lines σ G.V, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb) ∧ (∀ k ∈ KInf σ G.V B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb) ∧ (∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁) ∧ (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb, Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁) := by
  first | exact @GlobalTheory.PolStabInf.polStab | exact GlobalTheory.PolStabInf.polStab | (intros; apply GlobalTheory.PolStabInf.polStab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsDetRationalPointsGodementStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_absDet_rational_points_godement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (ι : Type) (x p k : ι → GAd σ J) (β : ι → GL (Fin j) (AF F ⊗[F] E)) (K : Set (GAd σ J)), IsCompact K → (∀ q, x q ∈ ratPts σ J) → (∀ q, x q = p q * k q) → (∀ q, k q ∈ K) → (∀ q, (matHom _ σ J (p q)).1 * adMat F C = adMat F C * (β q).1) → (∀ q q', x q' * (x q)⁻¹ ∈ parFlag σ J C (fun _ => 0) → q = q') → ∀ t : ℝ, ((m + j : ℕ) : ℝ) < t → Summable fun q => (absE F E (Matrix.GeneralLinearGroup.det (β q)) : ℝ) ^ t := by
  first | exact @GlobalTheory.SphEis.Summ.summable_absDet | exact GlobalTheory.SphEis.Summ.summable_absDet | (intros; apply GlobalTheory.SphEis.Summ.summable_absDet <;> assumption)
end

