import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0208
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0165
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0752
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCloseToComponentLocalDegreeOne
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.NormCompat.LocalDegOne

theorem valued_algebraMap_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem mul_sub_one_le {R : Type} [CommRing R] (v : Valuation R (WithZero (Multiplicative ℤ))) (a b : R) (M : ℕ)
    (ha : v (a - 1) ≤ WithZero.exp (-(M : ℤ))) (hb : v (b - 1) ≤ WithZero.exp (-(M : ℤ))) :
    v (a * b - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  have e : a * b - 1 = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) := by ring
  have h1 : WithZero.exp (-(M : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  rw [e]
  refine (v.map_add _ _).trans (max_le ?_ ((v.map_add _ _).trans (max_le ha hb)))
  rw [v.map_mul]
  calc v (a - 1) * v (b - 1) ≤ WithZero.exp (-(M : ℤ)) * 1 := mul_le_mul' ha (hb.trans h1)
    _ = _ := mul_one _

theorem norm_div_close_to_one : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ M : ℕ, ∃ M' : ℕ, ∀ (c : E) (z : E'), c ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → w'.valuation E' (z / algebraMap E E' c - 1) ≤ WithZero.exp (-(M' : ℤ)) → w.valuation E (Algebra.norm E z / c - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  intro E E' _ _ _ _ _ w w' i hi hcomp M
  set σ : E' →+* w.adicCompletion E := (i.symm : w'.adicCompletion E' →+* w.adicCompletion E).comp (algebraMap E' (w'.adicCompletion E')) with hσ
  have hσE : ∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x := fun x => by
    simp only [hσ, RingHom.comp_apply, RingEquiv.coe_toRingHom, ← hcomp x, RingEquiv.symm_apply_apply]
  have hσv : ∀ x : E', Valued.v (σ x) = w'.valuation E' x := fun x => by
    rw [← GlobalTheory.T.valued_map_eq_of_continuous_completionIso_extending E E' w w' i hi hcomp (σ x)]
    simp only [hσ, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact valued_algebraMap_eq w' x
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.T.norm_div_localEmbedding_close_to_one E E' w w' σ hσE hσv M
  refine ⟨max (max M M₁) 1, fun c z hc hz hzw => ?_⟩
  have hle : ∀ k, k ≤ max (max M M₁) 1 → WithZero.exp (-((max (max M M₁) 1 : ℕ) : ℤ)) ≤ WithZero.exp (-(k : ℤ)) := fun k hk => by
    rw [WithZero.exp_le_exp]; omega
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, Valuation.map_one] at hzw
    have := hzw.trans (hle 1 (le_max_right _ _))
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at this
    omega
  have hF := hM₁ z hz0 fun w'' h1 h2 => (hz w'' h1 h2).trans (hle M₁ (by omega))
  have hσz : σ z ≠ 0 := (map_ne_zero σ).2 hz0
  have hcE : algebraMap E (w.adicCompletion E) c ≠ 0 := (map_ne_zero _).2 hc
  have h2 : Valued.v (σ z / algebraMap E (w.adicCompletion E) c - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    have e : σ z / algebraMap E (w.adicCompletion E) c - 1 = σ (z / algebraMap E E' c - 1) := by
      rw [map_sub, map_div₀, hσE, map_one]
    rw [e, hσv]
    exact hzw.trans (hle M (by omega))
  rw [← valued_algebraMap_eq, map_sub, map_div₀, map_one]
  have e2 : algebraMap E (w.adicCompletion E) (Algebra.norm E z) / algebraMap E (w.adicCompletion E) c =
      (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z) * (σ z / algebraMap E (w.adicCompletion E) c) := by
    field_simp
  rw [e2]
  exact mul_sub_one_le Valued.v _ _ M hF h2

end GlobalTheory.NormCompat.LocalDegOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductDatumThetaHasShapeAdjointPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.ProdShape

variable {D : D7}

theorem isSBHalf_sub_smul {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f g : Mx D m n → ℂ}
    (hf : IsSBHalf e Λ f) (hg : IsSBHalf e Λ g) (c : ℂ) : IsSBHalf e Λ (f - c • g) := by
  obtain ⟨f1, k, hk, f2, f3⟩ := hf
  obtain ⟨g1, l, hl, g2, g3⟩ := hg
  have hne : ∀ t, (f - c • g) t ≠ 0 → f t ≠ 0 ∨ g t ≠ 0 := fun t ht => by
    by_contra h
    push_neg at h
    exact ht (by rw [Pi.sub_apply, Pi.smul_apply, h.1, h.2, smul_zero, sub_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (hne t ht).elim (f1 t) (g1 t), k * l, mul_pos hk hl, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have e1 : f (t + (k * l) • u) = f t := by
      rw [mul_smul]; exact f2 _ (nsmul_mem hu l) (hh l u hu') t
    have e2 : g (t + (k * l) • u) = g t := by
      rw [mul_comm, mul_smul]; exact g2 _ (nsmul_mem hu k) (hh k u hu') t
    rw [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact nsmul_mem (f3 t h) l
    · rw [mul_smul]; exact nsmul_mem (g3 t h) k

theorem isHalf_add_iff {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (t : Mx D m n) :
    IsHalf e (t + x) ↔ IsHalf e t := by
  rw [GlobalTheory.SplitScalar.isHalf_iff] at hx
  rw [GlobalTheory.SplitScalar.isHalf_iff, GlobalTheory.SplitScalar.isHalf_iff, smul_add, hx, add_left_inj]

theorem isSBHalf_transl {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f : Mx D m n → ℂ}
    (hf : IsSBHalf e Λ f) {x : Mx D m n} (hx : IsHalf e x) (hx' : ∃ l : ℕ, 0 < l ∧ l • x ∈ Λ) :
    IsSBHalf e Λ fun t => f (t + x) := by
  obtain ⟨f1, k, hk, f2, f3⟩ := hf
  obtain ⟨l, hl, hlx⟩ := hx'
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (isHalf_add_iff hx t).1 (f1 _ ht), k * l, mul_pos hk hl, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · beta_reduce
    rw [add_right_comm, mul_smul]
    exact f2 _ (nsmul_mem hu l) (hh l u hu') _
  · have h1 : (k * l) • (t + x) ∈ Λ := by rw [mul_comm, mul_smul]; exact nsmul_mem (f3 _ ht) l
    have h2 : (k * l) • x ∈ Λ := by rw [mul_smul]; exact nsmul_mem hlx k
    have := sub_mem h1 h2
    rwa [smul_add, add_sub_cancel_right] at this

theorem frMapAdj_conj_smul (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D))
    (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (e : AE D) (x : WO S T) :
    frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := by
  have h : (((cA D e • x).map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      toEAf D e • ((x.map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ := Matrix.ext fun i j => by
    change GlobalTheory.AdelicLatMove.cF D (toEAf D (cA D e * x j i)) = toEAf D e * GlobalTheory.AdelicLatMove.cF D (toEAf D (x j i))
    rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.AdelicLatMove.toEAf_cA, GlobalTheory.PlaceVec.cF_cF_toEAf]
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq, h, Matrix.mul_smul, Matrix.smul_mul]

section Red

variable {a b : ℕ} {p : Formalism.IndefR.Datum.EAf D} {M N : Matrix (Fin a) (Fin b) (Formalism.IndefR.Datum.EAf D)}

theorem isIntM_add_iff (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hM : p • M = 0) (hN : p • N = N) :
    IsIntM (M + N) ↔ IsIntM M ∧ IsIntM N := by
  refine ⟨fun h => ?_, fun h i j => add_mem (h.1 i j) (h.2 i j)⟩
  have h1 : p • (M + N) = N := by rw [smul_add, hM, hN, zero_add]
  have h2 : IsIntM N := fun i j => by
    rw [← h1]
    exact mul_mem hp (h i j)
  exact ⟨fun i j => (add_mem_cancel_right (h2 i j)).1 (h i j), h2⟩

theorem redM_add (PP : Pl D.host.E) (hM : IsIntM M) (hN : IsIntM N) : redM PP (M + N) = redM PP M + redM PP N := by
  funext i j
  have h2 : (M + N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := add_mem (hM i j) (hN i j)
  rw [Matrix.add_apply]
  unfold redM
  rw [dif_pos h2, dif_pos (hM i j), dif_pos (hN i j), ← RingHom.map_add]
  rfl

theorem redM_smul (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hM : IsIntM M) :
    redM PP (p • M) = resS D.host.F PP ⟨p, hp⟩ • redM PP M := by
  funext i j
  have h2 : (p • M) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem hp (hM i j)
  rw [Matrix.smul_apply, smul_eq_mul]
  unfold redM
  rw [dif_pos h2, dif_pos (hM i j), ← RingHom.map_mul]
  rfl

theorem redM_add_of_one (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1 : resS D.host.F PP ⟨p, hp⟩ = 1) (hM : p • M = 0) (hN : p • N = N) (iM : IsIntM M) (iN : IsIntM N) :
    redM PP (M + N) = redM PP N := by
  have h := redM_smul PP hp ((isIntM_add_iff hp hM hN).2 ⟨iM, iN⟩)
  rw [h1, one_smul, smul_add, hM, hN, zero_add] at h
  exact h.symm

theorem redM_add_of_zero (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h0 : resS D.host.F PP ⟨p, hp⟩ = 0) (hN : p • N = N) (iM : IsIntM M) (iN : IsIntM N) :
    redM PP (M + N) = redM PP M := by
  have h := redM_smul PP hp iN
  rw [h0, zero_smul, hN] at h
  rw [redM_add PP iM iN, h, add_zero]

end Red

theorem hasShape_adjDat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (P : Finset (Pl D.host.E)) (e e₀ : AE D) (PP : Pl D.host.E), IsIdemSum e P → PP ∈ P → Formalism.L2.NTheta.IsIdemAt e₀ PP → ∀ ω₁ ω₂ : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ, (∀ y y', y PP = y' PP → ω₁ y = ω₁ y') → (∀ y y', (∀ PP' ∈ P, PP' ≠ PP → y PP' = y' PP') → ω₂ y = ω₂ y') → ∀ f₀ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latH S T ΛS ΛT) 1 f₀ (adjDat S T βS βT e fun y => ω₁ y * ω₂ y) f → HasShape ψ S T (cA D e₀) (adjDat S T βS βT e₀ ω₁) f := by
  intro D ψ S T hψ ΛS ΛT hS hT βS βT P e e₀ PP he hPP he₀ ω₁ ω₂ h₁ h₂ f₀ f hf₀ hf ℓ hℓ
  classical
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  have hfT : f = Tm (adjDat S T βS βT e fun y => ω₁ y * ω₂ y) := hall Tm hTm
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hee : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hec : cA D e * cA D (cA D e) = 0 := by rw [← RingHom.map_mul, he.2, RingHom.map_zero]
  have hee₀ : cA D e * cA D e₀ = cA D e₀ := by rw [← RingHom.map_mul, GlobalTheory.DiagLiftFix.idemSum_mul he hPP he₀]
  have hSB : ∀ ω : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ,
      (∀ y y', (∀ PP ∈ P, y PP = y' PP) → ω y = ω y') →
      IsSBHalf (cA D e) (latH S T ΛS ΛT) (adjDat S T βS βT e ω) := fun ω hω =>
    GlobalTheory.PlaceVec.isSBHalf_of_red hS.1 hT.1 hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
      (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) P ω hω
  have s12 := hSB (fun y => ω₁ y * ω₂ y) fun y y' h => by
    rw [h₁ y y' (h PP hPP), h₂ y y' fun Q hQ _ => h Q hQ]
  have s2 := hSB ω₂ fun y y' h => h₂ y y' fun Q hQ _ => h Q hQ
  refine ⟨ℓ (Tm (adjDat S T βS βT e ω₂)), fun x hx => ?_⟩
  have hxs : cA D e₀ • x = x := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx
  have hx' : IsHalf (cA D e) x := by
    rw [GlobalTheory.SplitScalar.isHalf_iff, ← hxs, smul_smul, hee₀]
  have st := isSBHalf_transl s12 hx' (GlobalTheory.PlaceVec.exists_nsmul_mem_latO hS.1 hT.1 x
    (GlobalTheory.PlaceVec.half_infPart hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hx')))
  obtain ⟨hp, hp1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e₀ PP he₀
  have hN : toEAf D e₀ • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
    rw [← frMapAdj_conj_smul, hxs]
  have key := GlobalTheory.T.placeInvariantForm_kills_vanishing_schwartzBruhat D ψ S T hψ ΛS ΛT hS hT (cA D e₀) (cA D e) (GlobalTheory.SplitScalar.isSplitIdem_conj he₀.1)
    hee hec hinf hee₀ f₀ Tm hf₀ hTm ℓ hℓ _ (isSBHalf_sub_smul st s2 (adjDat S T βS βT e₀ ω₁ x)) fun t ht => by
      have hz : frMapAdj S T βS βT 0 = 0 :=
        (AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_zero
      have hM : toEAf D e₀ • frMapAdj S T βS βT t = 0 := by
        rw [← frMapAdj_conj_smul, ht, hz]
      have hI := isIntM_add_iff hp hM hN
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      unfold adjDat
      rw [GlobalTheory.PlaceVec.frMapAdj_add]
      by_cases c1 : IsIntM (frMapAdj S T βS βT x)
      · by_cases c2 : IsHalf (cA D e) t ∧ IsIntM (frMapAdj S T βS βT t)
        · rw [if_pos ⟨(isHalf_add_iff hx' t).2 c2.1, hI.2 ⟨c2.2, c1⟩⟩, if_pos ⟨hx, c1⟩, if_pos c2]
          beta_reduce
          rw [h₁ _ (fun Q => redM Q (frMapAdj S T βS βT x)) (redM_add_of_one PP hp hp1 hM hN c2.2 c1),
            h₂ _ (fun Q => redM Q (frMapAdj S T βS βT t)) fun Q _ hQ =>
              redM_add_of_zero Q hp (GlobalTheory.TameProd.resS_idem_eq_zero he₀ hQ.symm hp) hN c2.2 c1]
        · rw [if_neg c2, if_neg fun h => c2 ⟨(isHalf_add_iff hx' t).1 h.1, (hI.1 h.2).1⟩, mul_zero]
      · rw [if_neg fun h => c1 (hI.1 h.2).2, if_neg fun h => c1 h.2, zero_mul]
  rw [map_sub, map_smul, hTm.trans _ s12 x hx', ← hfT, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at key
  rw [key, mul_comm]

end GlobalTheory.DownLift.ProdShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParametersUnramifiedUnitaryStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_parameters_unramified_unitary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)) (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), Formalism.UG.IsUnramInv ϖ s q → ∀ p : locU n w →* Formalism.UG.GU s n, Function.Surjective p → ∀ σ : SmIrr (Formalism.UG.GU s n), IsCompAlong U (locU n w) p σ.ρ → ∀ α0 : Fin (n / 2) → ℂˣ, GlobalTheory.LFun.HasSatU ϖ q σ.ρ α0 → ∀ φ ∈ U, (∀ x : locU n w, p x ∈ Formalism.UG.KU s n → RU L n x.val φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU s n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU s n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU ϖ q h (fun i => (α0 i : ℂ)) • φ := by
  first | exact @GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed | exact GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed | (intros; apply GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApply
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem schurSquareMatrixToBlocks_blockDiagonal_one {R : Type} [CommRing R] (m r : ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    blk (GroundTheory.Automorphic.FourierWhittaker.blockMat (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      Matrix.fromBlocks h 0 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blk, eqv, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, Matrix.one_apply, Fin.ext_iff]
  all_goals
    have hi := i.isLt
    have hj := j.isLt
    try intro
    split_ifs <;> first | rfl | (exfalso; omega) | omega

theorem schurF_blockGL (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ)
    (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (h : GA E (m + 1)) :
    schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      β h * b₁ 1 * (χ 0 : ℂ) := by
  classical
  have hb := schurSquareMatrixToBlocks_blockDiagonal_one (R := Ad E) m r (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))
  have hD : Dof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 1 := by
    rw [Dof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₂]
  have hA : Aof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = h := by
    rw [Aof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₁]
  have hB : Bof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Bof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₁₂]
  have hC : Cof ((GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h : GA E (m + r + 1 + 1)) :
      Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = 0 := by
    rw [Cof, GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, hb, Matrix.toBlocks_fromBlocks₂₁]
  have hmk : mkGL (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) = h :=
    Units.ext (coe_mkGL (Matrix.isUnits_det_units h))
  have hmk1 : mkGL (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) = 1 :=
    Units.ext (by rw [coe_mkGL (by simp)]; rfl)
  have hpsi : psi (0 : Ad E) = 1 := by
    simp [psi]
  have hchi : chiF (m := m) (r := r) χ 0 = (χ 0 : ℂ) := by
    have h0 : (fun i j => pInf E ((0 : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) i j)) = 0 := by
      funext i j; simp
    rw [chiF, h0]
    simp [zero_mem]
  rw [schurF, if_pos (by rw [hD]; simp), Xof, Scof, Yof, hA, hB, hC, hD]
  simp only [inv_one, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, sub_zero, Matrix.zero_apply]
  rw [hpsi, hmk, hmk1, hchi, one_mul]

end GlobalTheory.SchurExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocyclesBetweenBlochKatoAndContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_cocycles_between_blochKato_and_continuous : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v : V, Continuous fun g => ρ g v) → IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) → ∃ S : Submodule ℚ_[l] (↥(GK K) → V), finiteCocycles (P.PD K) ρ ≤ S ∧ S ≤ continuousCocycles ρ ∧ (∀ c ∈ S, ∃ z : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ (∀ c ∈ S, ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) ∧ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) ≤ finrank ℚ_[l] ↥S := by
  first | exact @GlobalTheory.PMon.exists_stCocycles_lower | exact GlobalTheory.PMon.exists_stCocycles_lower | (intros; apply GlobalTheory.PMon.exists_stCocycles_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqProdOfParabolicInductionChainStatement
section
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_eq_prod_of_parabolic_induction_chain : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (π : GLRep g) (L : List (GLRep g)), InInd π L → ∀ F, Has S π.2.ρ F → ∃ fs : List (ZMod g)[X], List.Forall₂ (fun (ρ : GLRep g) f => Has S ρ.2.ρ f) L fs ∧ F = fs.prod := by
  first | exact @GlobalTheory.SerSys.has_prod_of_inInd | exact GlobalTheory.SerSys.has_prod_of_inInd | (intros; apply GlobalTheory.SerSys.has_prod_of_inInd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqMapBijective
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.ColumnForm GlobalTheory.GenericUnitary ValuativeRel

noncomputable section

namespace GlobalTheory.HermDualSelf

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def sesqMap (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w) :
    W →ₗ⋆[ℂ] smoothPart π.dual :=
  LinearMap.codRestrict (smoothPart π.dual) C.flip fun w =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((hσ w).mem_nhds (by simp)) fun g hg => by
      have hg' : σ g w = w := hg
      ext a
      show C (π g⁻¹ a) w = C a w
      have h := hC g (π g⁻¹ a) w
      rw [hg'] at h
      rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])

theorem sesqMap_apply (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w) (w : W) (a : V) :
    ((sesqMap π hσ C hC w : smoothPart π.dual) : Module.Dual ℂ V) a = C a w := rfl

theorem sesqMap_comm (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w) (g : G) (w : W) :
    sesqMap π hσ C hC (σ g w) = contra π g (sesqMap π hσ C hC w) := by
  refine Subtype.ext (LinearMap.ext fun a => ?_)
  rw [contra_apply, sesqMap_apply, sesqMap_apply]
  have h := hC g (π g⁻¹ a) w
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  exact h

theorem sesqMap_bijective (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w)
    (hinj : ∀ w, (∀ v, C v w = 0) → w = 0) (hne : ∃ w : W, w ≠ 0)
    (hirr : (contra π).IsIrreducible) : Function.Bijective (sesqMap π hσ C hC) := by
  set f := sesqMap π hσ C hC with hf
  have hi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine hinj w fun v => ?_
    have := congrArg (fun l : smoothPart π.dual => (l : Module.Dual ℂ V) v) hw
    simpa [hf, sesqMap_apply] using this
  refine ⟨hi, ?_⟩
  let R : Subrepresentation (contra π) :=
    { toSubmodule := LinearMap.range f
      apply_mem_toSubmodule := fun g l hl => by
        obtain ⟨w, rfl⟩ := hl
        exact ⟨σ g w, sesqMap_comm π hσ C hC g w⟩ }
  rcases hirr.eq_bot_or_eq_top R with hR | hR
  · exfalso
    obtain ⟨w, hw⟩ := hne
    have : f w ∈ R.toSubmodule := ⟨w, rfl⟩
    rw [hR] at this
    exact hw (hi (by rw [(Submodule.mem_bot ℂ).1 this, map_zero]))
  · intro l
    have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩

end GlobalTheory.HermDualSelf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialised_universal_series_eq_twisted_thetaSeries : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      specXi ρ Y i j b k Q M χ h P = specSer ρ Y i j b k Q M χ h P := by
  first | exact @GlobalTheory.SpecFac.specXi_eq_specSer | exact GlobalTheory.SpecFac.specXi_eq_specSer | (intros; apply GlobalTheory.SpecFac.specXi_eq_specSer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramifiedStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalSegmentRep_length_one_unramified : LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL k), IsLSeg Δ y.rep → IsSpherical y.rep → Δ.len = 1 ∧ Δ.first.IsUnramChar := by
  first | exact @GlobalTheory.SphSeg.len_eq_one_and_isUnramChar | exact GlobalTheory.SphSeg.len_eq_one_and_isUnramChar | (intros; apply GlobalTheory.SphSeg.len_eq_one_and_isUnramChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSphericalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L) (α β : GAf L n) (Ra Rb : Finset (GAf L n)), TrivOutside {s.v} α → TrivOutside {s.v} β → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * α * k₂) → ∃! γ, γ ∈ Ra ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Ra, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * α * k₂) → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * β * k₂) → ∃! γ, γ ∈ Rb ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Rb, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * β * k₂) → ∀ f : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → ∑ γ ∈ Ra, NG.rt L n γ (∑ δ ∈ Rb, NG.rt L n δ f) = ∑ δ ∈ Rb, NG.rt L n δ (∑ γ ∈ Ra, NG.rt L n γ f) := by
  first | exact @GlobalTheory.SplitHeckeComm.doubleCoset_comm | exact GlobalTheory.SplitHeckeComm.doubleCoset_comm | (intros; apply GlobalTheory.SplitHeckeComm.doubleCoset_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (F : GA E a → ℂ) :
    GA E a → ℂ := fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν

structure IsBCC (F : GA E a → ℂ) : Prop where
  cont : Continuous F
  bdd : ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C
  cusp : IsCuspidal F
  left : ∀ γ g, F (ratGL E a γ * g) = F g

variable (E a) in

def lieBasis : Module.Basis (Fin (Module.finrank ℝ (Lie E a))) ℝ (Lie E a) := Module.finBasis ℝ (Lie E a)

variable (E a) in

def lieCoord (i : Fin (Module.finrank ℝ (Lie E a))) : Lie E a →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap ((lieBasis E a).coord i))

def adCoef (γ : GL (Fin a) (Cinf E)) (p : Fin (Module.finrank ℝ (Lie E a)) × Fin (Module.finrank ℝ (Lie E a))) : ℂ :=
  lieCoord E a p.1 (toL ((γ⁻¹).val * Matrix.of (lieBasis E a p.2) * γ.val))

theorem sum_lieCoord (X : Lie E a) : ∑ i, ((lieBasis E a).coord i X) • lieBasis E a i = X :=
  (lieBasis E a).sum_repr X

end GlobalTheory.JSW
end
end

