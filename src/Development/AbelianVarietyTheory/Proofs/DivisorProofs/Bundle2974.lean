import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingBinomialSumEqPolynomialStatement
section
open MvPolynomial GlobalTheory.LineForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_binomial_sum_eq_polynomial : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), C ((-1) ^ j * (m.choose j : ℝ) / (m + j + 1 : ℝ)) * X 0 ^ (m - j) * hs (m + j) = pm m := by
  first | exact @GlobalTheory.LineForm.sum_choose_hs_eq_pm | exact GlobalTheory.LineForm.sum_choose_hs_eq_pm | (intros; apply GlobalTheory.LineForm.sum_choose_hs_eq_pm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleCubicalLineBundle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SS.AbAmple

open GlobalTheory.CechPic GlobalTheory.TripleExt

theorem cubeCls_eq_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (c : Pic A.left) : cubeCls (x3 A) c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have h := GlobalTheory.CubeTop.cubeTheorem S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have h₀ := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h
  rw [cls_linComb hL, Fin.sum_univ_eight] at h₀
  have e : x3 A = ![x3 A 0, x3 A 1, x3 A 2] := by
    funext i; fin_cases i <;> rfl
  rw [e, GlobalTheory.SS.AmpCub.cubeCls_three]
  rw [← h₀]
  simp
  abel

end GlobalTheory.SS.AbAmple

namespace GlobalTheory.SS

open GlobalTheory.CechPic AbAmple

theorem exists_ampleCub_of_isAbelianScheme :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B →
      ∃ L : LB B.left, GlobalTheory.SS.AmpleCub B L := by
  intro k _ _ B _ hB
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom := geometricallyIntegral_of_smooth _
  have : IsIntegral B.left :=
    GeometricallyIntegral.geometrically_isIntegral (f := B.hom) (𝟙 _) _ _ (IsPullback.id_horiz B.hom)
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  have hst : ∀ x : B.left, UniqueFactorizationMonoid (B.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth k B.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨y⟩ : Nonempty B.left := inferInstance
  obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  obtain ⟨L, s, hL, hs⟩ := exists_nonzeroLocus_eq_of_isAffineOpen B.left hst W hW ⟨y, hy⟩
  exact AmpCub.exists_ampleCub (cubeCls_eq_zero B hB (cls L hL)) ⟨L, hL, s, rfl, hs⟩ hW ⟨y, hy⟩

end GlobalTheory.SS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidLevelRigidStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_level_rigid : GlobalTheory.AmpleRigid.SerreAmpleSt → GlobalTheory.AmpleRigid.LevelRigidSt := by
  first | exact @GlobalTheory.AmpleRigid.levelRigid_of_serreAmple | exact GlobalTheory.AmpleRigid.levelRigid_of_serreAmple | (intros; apply GlobalTheory.AmpleRigid.levelRigid_of_serreAmple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalRealStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_diagonal_real : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ (c' : 𝔠.elt) (l l' : u.Λ), ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (((e j ((c' : F) / (2 * (c : F))) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im = n := by
  first | exact @GlobalTheory.RiemInt.riemannForm_int | exact GlobalTheory.RiemInt.riemannForm_int | (intros; apply GlobalTheory.RiemInt.riemannForm_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFrameLogDerivativeQuasiPeriodic
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer.LogDer

open Filter Topology

theorem logDer_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f c d : E → ℂ} {z : E}
    (h : f =ᶠ[𝓝 z] fun w => c w * d w) (hc : DifferentiableAt ℂ c z) (hd : DifferentiableAt ℂ d z)
    (hc0 : c z ≠ 0) (hd0 : d z ≠ 0) (v : E) :
    fderiv ℂ f z v / f z = fderiv ℂ c z v / c z + fderiv ℂ d z v / d z := by
  have hm : HasFDerivAt (fun w => c w * d w) (c z • fderiv ℂ d z + d z • fderiv ℂ c z) z :=
    hc.hasFDerivAt.mul hd.hasFDerivAt
  rw [h.fderiv_eq, hm.fderiv, h.eq_of_nhds]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem hasFDerivAt_factor {g : ℕ} (a b c : ℂ) (m z : Fin g → ℂ) :
    ∃ D : (Fin g → ℂ) →L[ℂ] ℂ, HasFDerivAt (fun w : Fin g → ℂ => a * Complex.exp (b * (w ⬝ᵥ m) + c)) D z ∧
      ∀ v, D v = a * Complex.exp (b * (z ⬝ᵥ m) + c) * (b * (v ⬝ᵥ m)) := by

  let ℓ : (Fin g → ℂ) →L[ℂ] ℂ := ∑ i, m i • ContinuousLinearMap.proj i
  have hℓ : ∀ w, ℓ w = w ⬝ᵥ m := by
    intro w
    simp [ℓ, dotProduct, mul_comm]
  have H := (((ℓ.hasFDerivAt (x := z)).const_mul b).add_const c).cexp.const_mul a
  have hfun : (fun w : Fin g → ℂ => a * Complex.exp (b * (w ⬝ᵥ m) + c)) = fun w => a * Complex.exp (b * ℓ w + c) := by
    funext w
    rw [hℓ]
  refine ⟨a • (Complex.exp (b * ℓ z + c) • (b • ℓ)), ?_, ?_⟩
  · rw [hfun]
    exact H
  · intro v
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hℓ]
    ring

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → L.IsLB → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH H χ → ∀ v : Fin g → ℂ, (∀ i, DifferentiableOn ℂ (fun z => fderiv ℂ (u.fr i) z v / u.fr i z) (pre u.ex (L.U i))) ∧ (∀ i j, IsReg u.ex (L.U i ⊓ L.U j) ((fun z => fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => fderiv ℂ (u.fr j) z v / u.fr j z)) ∧ ∀ i (l : u.Λ), ∀ z ∈ pre u.ex (L.U i), fderiv ℂ (u.fr i) (z + l) v / u.fr i (z + l) = fderiv ℂ (u.fr i) z v / u.fr i z - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  intro A _ g L u hA _ H χ hAH v
  obtain ⟨hopen, hdval, hshift, -, hinf, -, -, -, -, hev, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u

  have hfrd : ∀ i, DifferentiableOn ℂ (u.fr i) (pre u.ex (L.U i)) := u.10
  have hfr0 : ∀ i, ∀ z ∈ pre u.ex (L.U i), u.fr i z ≠ 0 := fun i z hz => u.11 i z hz
  have hfrg : ∀ i j, ∀ z ∈ pre u.ex (L.U i ⊓ L.U j),
      u.fr i z = val u.ex (L.U i ⊓ L.U j) (L.g i j : Γ(A.left, L.U i ⊓ L.U j)) z * u.fr j z :=
    fun i j z hz => u.12 i j z hz
  have hfra : ∀ i, ∀ z ∈ pre u.ex (L.U i), DifferentiableAt ℂ (u.fr i) z :=
    fun i z hz => (hfrd i).differentiableAt ((hopen _).mem_nhds hz)
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i z hz

    let e : ReciprocityTheory.L2DbarEstimates.V g ≃L[ℂ] (Fin g → ℂ) := EuclideanSpace.equiv (Fin g) ℂ
    have hpre : IsOpen (e ⁻¹' pre u.ex (L.U i)) := (hopen _).preimage e.continuous
    have hsm := ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn g (u.fr i ∘ e) _ hpre
      ((hfrd i).comp e.differentiableOn (fun y hy => hy))
    have hsm' : ContDiffOn ℂ (↑(⊤ : ℕ∞)) (u.fr i) (pre u.ex (L.U i)) := by
      have h2 := hsm.comp e.symm.contDiff.contDiffOn (fun y hy => by simpa using hy)
      have h3 : (u.fr i ∘ e) ∘ e.symm = u.fr i := by
        funext y
        simp
      rwa [h3] at h2
    have hca := (hsm'.contDiffAt ((hopen _).mem_nhds hz)).fderiv_right (m := 1)
      (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
    have h1 : DifferentiableAt ℂ (fun w => fderiv ℂ (u.fr i) w v) z :=
      (hca.differentiableAt one_ne_zero).clm_apply (differentiableAt_const v)
    have h4 := h1.mul ((hfra i z hz).inv (hfr0 i z hz))
    simp only [div_eq_mul_inv]
    exact h4.differentiableWithinAt
  ·
    intro i j
    set U := L.U i ⊓ L.U j with hU
    set G : Γ(A.left, U) := (L.g i j).val with hG
    set G' : Γ(A.left, U) := ((L.g i j)⁻¹ : (Γ(A.left, U))ˣ).val with hG'
    obtain ⟨-, hring, hcongr, -, -, -⟩ := GlobalTheory.T.isRegularOnOpenUniformised_subalgebra_restrict A g L u U
    have hder : IsReg u.ex U fun z => fderiv ℂ (val u.ex U G) z v := GlobalTheory.T.isRegular_fderiv_constant_vector_uniformised A g L u hA U G v
    have hinv : IsReg u.ex U (val u.ex U G') := ⟨G', fun z _ => rfl⟩
    have hprod := (hring _ _ hder hinv).2.2
    refine hcongr _ _ hprod ?_
    intro z hz
    have hzij : z ∈ pre u.ex (L.U i) ∩ pre u.ex (L.U j) := by rw [← hinf]; exact hz
    have hGG : val u.ex U G z * val u.ex U G' z = 1 := by
      obtain ⟨e, he⟩ := hev U z hz
      have h1 : G * G' = 1 := Units.mul_inv _
      rw [he, he]
      exact (map_mul e G G').symm.trans ((congrArg e h1).trans (map_one e))
    have hG0 : val u.ex U G z ≠ 0 := left_ne_zero_of_mul_eq_one hGG
    have hev' : ∀ᶠ w in 𝓝 z, u.fr i w = val u.ex U G w * u.fr j w :=
      Filter.eventually_of_mem ((hopen U).mem_nhds hz) (fun w hw => hfrg i j w hw)
    have key := logDer_mul hev' ((hdval U G).differentiableAt ((hopen U).mem_nhds hz))
      (hfra j z hzij.2) hG0 (hfr0 j z hzij.2) v
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [key, eq_inv_of_mul_eq_one_right hGG]
    ring
  ·
    intro i l z hz
    set m := H.mulVec (star (l : Fin g → ℂ)) with hm
    have hzl : z + (l : Fin g → ℂ) ∈ pre u.ex (L.U i) := (hshift (L.U i) l z).2 hz
    have hχ : χ l ≠ 0 := by
      intro h0
      have := hAH.2.2.1 l
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    obtain ⟨D, hD, hDv⟩ := hasFDerivAt_factor (χ l) (Real.pi : ℂ) ((Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m)) m z
    have hev' : ∀ᶠ w in 𝓝 z, u.fr i w = (χ l * Complex.exp ((Real.pi : ℂ) * (w ⬝ᵥ m) + (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m))) * u.fr i (w + l) :=
      Filter.eventually_of_mem ((hopen _).mem_nhds hz) (fun w hw => hAH.2.2.2 l i w hw)
    have hdl : DifferentiableAt ℂ (fun w => u.fr i (w + l)) z :=
      (hfra i _ hzl).comp z (differentiableAt_id.add_const _)
    have key := logDer_mul hev' hD.differentiableAt hdl
      (mul_ne_zero hχ (Complex.exp_ne_zero _)) (hfr0 i _ hzl) v
    rw [hD.fderiv, hDv, fderiv_comp_add_right] at key
    have hE : χ l * Complex.exp ((Real.pi : ℂ) * (z ⬝ᵥ m) + (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ m)) ≠ 0 :=
      mul_ne_zero hχ (Complex.exp_ne_zero _)
    rw [key, mul_div_cancel_left₀ _ hE]
    ring

end GlobalTheory.CechPer.LogDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVarietyStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archIntegrable_regular_variety : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsRegVar p D →
    ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ} (hr : IsRatSec N.B r), M.ArchIntegrable N D hr := by
  first | exact @GlobalTheory.LogNormInt.archIntegrable | exact GlobalTheory.LogNormInt.archIntegrable | (intros; apply GlobalTheory.LogNormInt.archIntegrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMassProductLowerBoundUnitaryPq
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.MassLow

theorem perm_conj' {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix (Fin r) (Fin r) ℂ) :
    permM e * M * (permM e)ᵀ = M.submatrix e e := by
  ext i j
  simp [Matrix.mul_apply, permM]

theorem det_lift {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) (s : realSU Ψ G) (u : UpqT (p ρ) (q ρ))
    (hu : UpqT.mat u * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) :
    (UpqT.mat u).det = 1 := by
  obtain ⟨h1, h2, h3, -⟩ := MassUp.inv_facts hI ρ
  set S := ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
  set P := permM (e ρ)
  have hS : S.det = 1 := (s.2 (σ ρ)).1
  set M := (Pᵀ * A ρ) * S * mat x (σ ρ) with hM
  have hx : mat x (σ ρ) * M = S * mat x (σ ρ) := by
    rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hu' : UpqT.mat u = P * M * Pᵀ := by
    calc UpqT.mat u = UpqT.mat u * (A ρ * (mat x (σ ρ) * Pᵀ)) := by rw [h3, Matrix.mul_one]
      _ = A ρ * (S * mat x (σ ρ)) * Pᵀ := by
        rw [← Matrix.mul_assoc, hu]; simp only [Matrix.mul_assoc]
      _ = P * M * Pᵀ := by
        rw [← hx, ← Matrix.mul_assoc, (hI ρ).2]
  rw [hu', perm_conj', Matrix.det_submatrix_equiv_self, hM, Matrix.det_mul, Matrix.det_mul, hS, mul_one,
    ← Matrix.det_mul, h1, Matrix.det_one]

theorem arith (f r : ℕ) (ε : ℝ) (hr : 1 ≤ r) (hε : 0 < ε) :
    (1 / 16 : ℝ) ^ (f * r ^ 2) * (8 * ε) ^ (f * (r ^ 2 - 1)) ≤ (ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1)) ^ f := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have key : (1 / 16 : ℝ) ^ (r ^ 2) * (8 * ε) ^ (r ^ 2 - 1) ≤ ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1) := by
    have hrp : (r : ℝ) ^ (r - 1) ≤ 2 ^ (r ^ 2) := by
      have h1 : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self).le
      calc (r : ℝ) ^ (r - 1) ≤ ((2 : ℝ) ^ r) ^ (r - 1) := pow_le_pow_left₀ hr0.le h1 _
        _ = 2 ^ (r * (r - 1)) := by rw [← pow_mul]
        _ ≤ 2 ^ (r ^ 2) := pow_le_pow_right₀ (by norm_num) (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h8 : (8 : ℝ) ^ (r ^ 2 - 1) ≤ 8 ^ (r ^ 2) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    rw [le_div_iff₀ (pow_pos hr0 _), mul_pow]
    have hε' : 0 ≤ ε ^ (r ^ 2 - 1) := pow_nonneg hε.le _
    calc (1 / 16 : ℝ) ^ (r ^ 2) * (8 ^ (r ^ 2 - 1) * ε ^ (r ^ 2 - 1)) * (r : ℝ) ^ (r - 1)
        ≤ (1 / 16 : ℝ) ^ (r ^ 2) * (8 ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) * 2 ^ (r ^ 2) := by gcongr
      _ = ((1 / 16 : ℝ) * 8 * 2) ^ (r ^ 2) * ε ^ (r ^ 2 - 1) := by rw [mul_pow, mul_pow]; ring
      _ = ε ^ (r ^ 2 - 1) := by norm_num
  have e1 : (1 / 16 : ℝ) ^ (f * r ^ 2) = ((1 / 16 : ℝ) ^ (r ^ 2)) ^ f := by rw [← pow_mul, mul_comm f]
  have e2 : (8 * ε) ^ (f * (r ^ 2 - 1)) = ((8 * ε) ^ (r ^ 2 - 1)) ^ f := by rw [← pow_mul, mul_comm f]
  rw [e1, e2, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) key f

theorem massLow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))) (ρ₀ : κ), 1 ≤ r → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → ENNReal.ofReal ((1 / 16 : ℝ) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S ≤ Measure.pi m (π ⁻¹' S ∩ {b | 0 < (UpqT.mat (b ρ₀)).det.im}) := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ π m ρ₀ hr hI hπc hP hT hm S hS
  classical
  haveI : ∀ ρ, IsTopologicalGroup (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  haveI : ∀ ρ, LocallyCompactSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.1
  haveI : ∀ ρ, SecondCountableTopology (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.1
  haveI : ∀ ρ, BorelSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.1
  haveI : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1
  have hcard : Fintype.card κ = Ψ.card := by
    rw [Fintype.card_congr σ]; simp
  have hΨ : 1 ≤ Ψ.card := by
    rw [← hcard]; exact Fintype.card_pos_iff.2 ⟨ρ₀⟩
  have hG : G.det ≠ 0 := MassUp.det_ne hI ρ₀
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    exact Matrix.det_ne_zero_of_right_inverse (MassUp.inv_facts hI ρ).2.1
  have hpq : ∀ ρ, p ρ + q ρ = r := by
    intro ρ; simpa using Fintype.card_congr (e ρ)
  have hπm : Measurable π := hπc.measurable
  set μ := Measure.pi m with hμ
  set T : Set (∀ ρ, UpqT (p ρ) (q ρ)) := {b | 0 < (UpqT.mat (b ρ₀)).det.im} with hTdef
  have hTo : IsOpen T := isOpen_lt continuous_const
    (Complex.continuous_im.comp ((GlobalTheory.UpqTopology.continuous_mat.comp (continuous_apply ρ₀)).matrix_det))
  have hTm : MeasurableSet T := hTo.measurableSet
  set ν := (μ.restrict T).map π with hν

  haveI hinv : ν.IsMulLeftInvariant := by
    constructor
    intro s
    obtain ⟨b₀, hb₀⟩ := MassUp.exists_lift E r κ p q Ψ G x σ A e hI s
    have hd : (UpqT.mat (b₀ ρ₀)).det = 1 := det_lift hI ρ₀ s (b₀ ρ₀) (hb₀ ρ₀)
    have hpre : (fun b => b₀ * b) ⁻¹' T = T := by
      ext b
      simp only [Set.mem_preimage, hTdef, Set.mem_setOf_eq, Pi.mul_apply]
      rw [show UpqT.mat (b₀ ρ₀ * b ρ₀) = UpqT.mat (b₀ ρ₀) * UpqT.mat (b ρ₀) from rfl, Matrix.det_mul, hd, one_mul]
    rw [hν, Measure.map_map (measurable_const_mul s) hπm]
    have h : (fun y => s * y) ∘ π = π ∘ (fun b => b₀ * b) := funext fun b => (hT s b₀ hb₀ b).symm
    rw [h, ← Measure.map_map hπm (measurable_const_mul b₀)]
    congr 1
    calc (μ.restrict T).map (fun b => b₀ * b)
        = (μ.restrict ((fun b => b₀ * b) ⁻¹' T)).map (fun b => b₀ * b) := by rw [hpre]
      _ = (μ.map (fun b => b₀ * b)).restrict T := (Measure.restrict_map (measurable_const_mul b₀) hTm).symm
      _ = μ.restrict T := by rw [map_mul_left_eq_self]
  haveI hH : (riemHaar Ψ G x).IsHaarMeasure :=
    (GlobalTheory.SUVol.DensOne.tangentHaar_riemLie (Ψ := Ψ) (G := G) (hG := hG) (x := x) (hx := hx)).1

  have hup := MassUp.massUp E r κ p q Ψ G x σ A e a₀ π m hr hΨ hI hπc hP hT hm
  haveI : IsFiniteMeasureOnCompacts ν := by
    constructor
    intro K hK
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [hν, Measure.map_apply hπm hKm]
    calc μ.restrict T (π ⁻¹' K) ≤ μ (π ⁻¹' K) := Measure.restrict_le_self _
      _ ≤ _ := hup K hKm
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  have hc := Measure.isMulLeftInvariant_eq_smul ν (riemHaar Ψ G x)
  set c := ν.haarScalarFactor (riemHaar Ψ G x) with hcdef

  have hplace := fun ρ => GlobalTheory.T.le_measure_unitaryDetOneFactor_near_identity (p ρ) (q ρ) (a₀ ρ) (m ρ) (hm ρ)
  choose εp hεp hbp using hplace
  obtain ⟨εu, hεu, hbu⟩ := GlobalTheory.T.riemannianHaar_frameBall_le E r κ p q Ψ G x σ A e hr hI
  set δ := Finset.univ.inf' ⟨ρ₀, Finset.mem_univ _⟩ εp with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun ρ _ => hεp ρ
  set ε := min δ εu / 2 with hεdef
  have hεm : ε < min δ εu := half_lt_self (lt_min hδ hεu)
  have hε : 0 < ε := half_pos (lt_min hδ hεu)
  have hεδ : ∀ ρ, ε < εp ρ := fun ρ =>
    lt_of_lt_of_le (lt_of_lt_of_le hεm (min_le_left _ _)) (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hεu' : ε < εu := lt_of_lt_of_le hεm (min_le_right _ _)
  have hopen : IsOpen (frBall Ψ G x ε) := by
    have hc' : ∀ τ a b, Continuous fun s : realSU Ψ G =>
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ := by
      intro τ a b
      have h1 : Continuous fun s : realSU Ψ G => ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) :=
        Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)
      exact ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).sub continuous_const).matrix_elem a b).norm
    have : frBall Ψ G x ε = ⋂ τ, ⋂ a, ⋂ b, {s : realSU Ψ G |
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε} := by
      ext s; simp [frBall]
    rw [this]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => isOpen_lt (hc' τ a b) continuous_const
  set L := ε ^ (r ^ 2 - 1) / (r : ℝ) ^ (r - 1) with hL
  have hlow : ENNReal.ofReal (L ^ Ψ.card) ≤ ν (frBall Ψ G x ε) := by
    rw [hν, Measure.map_apply hπm hopen.measurableSet, Measure.restrict_apply (hπm hopen.measurableSet),
      MassUp.preimage_frBall E r κ p q Ψ G x σ A e a₀ π hI hP ε]
    have hsub : Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) | (∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε) ∧
        0 < (UpqT.mat u).det.im}) ⊆ Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) |
          ∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε}) ∩ T := by
      intro b hb
      simp only [Set.mem_univ_pi, Set.mem_setOf_eq] at hb
      exact ⟨fun ρ _ => (hb ρ).1, (hb ρ₀).2⟩
    refine le_trans ?_ (measure_mono hsub)
    rw [hμ, Measure.pi_pi]
    calc ENNReal.ofReal (L ^ Ψ.card) = ∏ _ρ : κ, ENNReal.ofReal L := by
          rw [Finset.prod_const, Finset.card_univ, hcard, ENNReal.ofReal_pow (by positivity)]
      _ ≤ _ := Finset.prod_le_prod' fun ρ _ => by
          have := hbp ρ ε hε (hεδ ρ)
          rw [hpq ρ] at this
          exact this
  have hupB := hbu ε hε hεu'
  set U := (8 * ε) ^ (Ψ.card * (r ^ 2 - 1)) with hU
  have hcU : L ^ Ψ.card ≤ (c : ℝ) * U := by
    have h1 : ENNReal.ofReal (L ^ Ψ.card) ≤ ENNReal.ofReal ((c : ℝ) * U) := by
      calc ENNReal.ofReal (L ^ Ψ.card) ≤ ν (frBall Ψ G x ε) := hlow
        _ = (c : ℝ≥0∞) * riemHaar Ψ G x (frBall Ψ G x ε) := by
          conv_lhs => rw [hc]
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        _ ≤ (c : ℝ≥0∞) * ENNReal.ofReal U := mul_le_mul_of_nonneg_left hupB (zero_le)
        _ = ENNReal.ofReal ((c : ℝ) * U) := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (NNReal.coe_nonneg _) (by positivity))).1 h1
  have hK := arith Ψ.card r ε hr hε
  have hUpos : 0 < U := by positivity
  have hcK : (1 / 16 : ℝ) ^ (Ψ.card * r ^ 2) ≤ c :=
    le_of_mul_le_mul_right (hK.trans hcU) hUpos
  calc ENNReal.ofReal ((1 / 16 : ℝ) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S
      ≤ (c : ℝ≥0∞) * riemHaar Ψ G x S := by
        gcongr
        rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hcK
    _ = ν S := by
        conv_rhs => rw [hc]
        rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    _ = μ (π ⁻¹' S ∩ T) := by
        rw [hν, Measure.map_apply hπm hS, Measure.restrict_apply (hπm hS)]

end GlobalTheory.CovTop.VolUp.MassLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingDegreeOneExtensionStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.axes_vanishing_degree_one_extension : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  first | exact @GlobalTheory.Obs.axesE1_of_axesO1 | exact GlobalTheory.Obs.axesE1_of_axesO1 | (intros; apply GlobalTheory.Obs.axesE1_of_axesO1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniCoordinateStrataEtaleChartCotangentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bertini_coordinateStrata_etaleChart_cotangent : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)), ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) → ∀ (J : Finset (Fin n)) (h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) j, h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  first | exact @GlobalTheory.StrataBertini.bertini_strata_cotangent | exact GlobalTheory.StrataBertini.bertini_strata_cotangent | (intros; apply GlobalTheory.StrataBertini.bertini_strata_cotangent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoVariablesResCocycleEqStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgebraPullbackTwoVariables_res_cocycle_eq : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ), pullbackTwo (G.res n) (d.coc (n + 1)) = d.coc n := by
  first | exact @GlobalTheory.PtExt.Dat.pullTwo_res_coc | exact GlobalTheory.PtExt.Dat.pullTwo_res_coc | (intros; apply GlobalTheory.PtExt.Dat.pullTwo_res_coc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUniqueStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalRigidifiedExtensionOfDeRhamClass_unique : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A), IsAbelianScheme A → ∀ x x' : G.RigExt, IsCan t c x → IsCan t c x' → x = x' := by
  first | exact @GlobalTheory.PtExt.isCan_unique | exact GlobalTheory.PtExt.isCan_unique | (intros; apply GlobalTheory.PtExt.isCan_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocycleFormEqConnectionFormStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleFormsCocycle_form_eq_connectionForm : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (k : (KK (dp0 R) s).Z1) (f : Z1 (O (dp0 R) s)), k.1.1 = f.1 → ∀ (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)), k.1.2 (Thick.triv B x hx) = Submodule.Quotient.mk (connForm f x hx) := by
  first | exact @GlobalTheory.ConnCocycle.form_eq_connForm | exact GlobalTheory.ConnCocycle.form_eq_connForm | (intros; apply GlobalTheory.ConnCocycle.form_eq_connForm <;> assumption)
end

