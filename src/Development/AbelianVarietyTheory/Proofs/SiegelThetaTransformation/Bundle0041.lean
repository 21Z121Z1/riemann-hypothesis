import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0006
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExOfPow

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.VacEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {n : ℕ}

theorem row_mul_transpose (y : Matrix (Fin n) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (k : Fin n) : (y * γᵀ) k = γ *ᵥ y k := by
  funext j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem epsW_mul_transpose (w : E) (γ : GL (Fin r) E) (hγ : IsUn X γ)
    (y : Matrix (Fin n) (Fin r) E) :
    epsW X w (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = epsW X w y := by

  have key : ∀ k, EF X ((y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) (w • (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) k) =
      EF X (y k) (w • y k) := by
    intro k
    rw [row_mul_transpose, ← Matrix.mulVec_smul, EF_def, EF_def, hγ (y k) (w • y k)]
  unfold epsW
  simp only [key]

end GlobalTheory.SW.VacEx

namespace GlobalTheory.SW

open VacEx

theorem exists_vacua_and_multipliers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ D : Level X, ∃ (v₀ : Lt E r → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) ∧ ∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L) := by
  intro E _ _ _ r X g bas idx n hs hn D

  obtain ⟨-, huniq, hgrp, hlats, -, -, -⟩ :=
    GlobalTheory.T.level_structure_properties E r X g bas idx (2 * r) hs ⟨r, two_mul r⟩ D (by omega)
  obtain ⟨-, hstd, -⟩ := GlobalTheory.SW.finite_cls_and_stab E n 1 one_pos

  have hvac : ∀ L, SelfD X L → (∃ v, IsVac X bas D.w (tens (stdL E n) L) v) ∧
      ∀ v v', IsVac X bas D.w (tens (stdL E n) L) v → IsSB v' →
        (∀ y ∈ tens (stdL E n) L, epsW X D.w y • heisG X bas y v' = v') → ∃ c : ℂ, v' = c • v := by
    intro L hL
    obtain ⟨h1, h2, -, -⟩ :=
      GlobalTheory.SW.TensVac.vacua E r X g bas idx n hs hn D.w D.w_int D.w_tr L hL 1 (stdL E n) hstd
    exact ⟨h1, fun v v' hv hv' hfix => ⟨_, h2 v v' hv hv' hfix⟩⟩
  classical
  let v₀ : Lt E r → TF n g := fun L =>
    if h : ∃ v, IsVac X bas D.w (tens (stdL E n) (D.sh L)) v then h.choose else 0
  have hv₀ : ∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L) := by
    intro L hL
    have h := (hvac _ (hlats L hL).1).1
    rw [show v₀ L = h.choose from dif_pos h]
    exact h.choose_spec

  let μ : GL (Fin r) E → Lt E r → ℂ := fun γ L =>
    if h : (∃ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧
        ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L)
    then h.2.choose * (((D.lam h.1.choose)⁻¹ : ℂˣ) : ℂ) else 0
  refine ⟨v₀, μ, hv₀, ?_⟩
  intro γ hγ L hL k hk
  obtain ⟨hγu, -⟩ := (hgrp γ).1 hγ
  obtain ⟨-, -, -, hmove⟩ := hlats L hL
  obtain ⟨hL', hsh⟩ := hmove γ hγ
  obtain ⟨hSB, -, hfix⟩ := hv₀ L hL
  have hv' := hv₀ _ hL'
  rw [hsh] at hv'
  have hSD' : SelfD X (mapL γ (D.sh L)) := by
    rw [← hsh]
    exact (hlats _ hL').1
  have hlaw := GlobalTheory.SW.wG_laws E r X g bas idx n hs hn γ hγu (v₀ L) hSB

  have himg : ∀ y ∈ tens (stdL E n) (mapL γ (D.sh L)),
      epsW X D.w y • heisG X bas y (wG X bas idx γ (v₀ L)) = wG X bas idx γ (v₀ L) := by
    intro y hy
    set y₀ : Matrix (Fin n) (Fin r) E := y * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᵀ with hy₀
    have hyy : y₀ * (γ : Matrix (Fin r) (Fin r) E)ᵀ = y := by
      rw [hy₀, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
        Matrix.mul_one]
    have hy₀m : y₀ ∈ tens (stdL E n) (D.sh L) := by
      rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hy ⊢
      intro k
      obtain ⟨x, hx, hxk⟩ := Submodule.mem_map.mp (hy k)
      rw [hy₀, VacEx.row_mul_transpose, ← hxk]
      simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        Units.inv_mul, Matrix.one_mulVec]
      exact hx
    have hSB0 : IsSB (heisG X bas y₀ (v₀ L)) := (GlobalTheory.SW.TensVac.laws idx hs hn y₀ hSB).1
    have hlaw0 := GlobalTheory.SW.wG_laws E r X g bas idx n hs hn γ hγu _ hSB0
    rw [← hyy, ← hlaw.2.2.2.2.2.2 y₀, VacEx.epsW_mul_transpose X D.w γ hγu y₀, ← hlaw0.2.2.2.1,
      hfix y₀ hy₀m]
  have hex : ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L) :=
    (hvac _ hSD').2 _ _ hv' hlaw.1 himg
  have hcond : (∃ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧
      ∃ c : ℂ, wG X bas idx γ (v₀ L) = c • v₀ (mapL γ L) := ⟨⟨k, hk⟩, hex⟩

  have hk' : hcond.1.choose = k := Subtype.ext (huniq _ _ _ hcond.1.choose_spec hk)
  have hμ : μ γ L = hcond.2.choose * (((D.lam hcond.1.choose)⁻¹ : ℂˣ) : ℂ) := dif_pos hcond
  rw [hμ, hk', mul_assoc, Units.inv_mul, mul_one]
  exact hcond.2.choose_spec

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicRowHighestEqSpanIntegralHarmonicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicRowHighest_eq_span_integral_harmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g q0 n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c σ X g q0 n a) (Λ : Lt E n) (N : ℕ), 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∀ Q ∈ Harm.rowHighest ℂ Dc.k Dc.k', ∃ (m : ℕ) (t : Fin m → ℂ) (P : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, P i ∈ harmL c (⟨Λ⟩ : GenLat E n) a) ∧ Q = ∑ i, t i • MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P i)) := by
  first | exact @GlobalTheory.Dict.rowHighest_eq_sum_harmL | exact GlobalTheory.Dict.rowHighest_eq_sum_harmL | (intros; apply GlobalTheory.Dict.rowHighest_eq_sum_harmL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisGFixOfMemLattice
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

private lemma isIntegral_crd_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) {v : Fin r → E}
    (hv : v ∈ X.Λ) (j : Fin g ⊕ Fin g) : IsIntegral ℤ (crd X bas v j) := by

  obtain ⟨m, rfl⟩ : ∃ m, (bas m : Fin r → E) = v := ⟨bas.symm ⟨v, hv⟩, by simp⟩
  rw [← vecQ_intCast X bas m, crd_vecQ hs]
  simpa using isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := m j)

theorem heisG_fix_of_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ : TF n g, IsSB φ → ∃ N : ℕ, 0 < N ∧ ∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ j : ℕ, heisG X bas (((j * N : ℕ) : E) • y) φ = φ := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn φ hφ
  obtain ⟨R, hR, hlev⟩ := hφ
  refine ⟨2 * R, by omega, fun y hy j => ?_⟩

  have hmem : ∀ k, (j • y) k ∈ X.Λ := fun k => nsmul_mem (hy k) j
  have hsc : (((j * (2 * R) : ℕ) : E) • y) = (2 * R) • (j • y) := by
    rw [Nat.cast_smul_eq_nsmul, smul_smul]
    congr 1
    ring
  rw [hsc, GlobalTheory.SW.TensVac.heisG_eq hs, map_nsmul, Prod.smul_fst, Prod.smul_snd,
    ← Nat.cast_smul_eq_nsmul ℚ (2 * R) (GlobalTheory.SW.TensVac.crdHom hs (j • y)).1,
    ← Nat.cast_smul_eq_nsmul ℚ (2 * R) (GlobalTheory.SW.TensVac.crdHom hs (j • y)).2]
  exact GlobalTheory.SW.TensVac.heisS_fix hlev (fun k i => isIntegral_crd_of_mem hs (hmem k) (Sum.inl i))
    (fun k i => isIntegral_crd_of_mem hs (hmem k) (Sum.inr i))

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLawsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFormAtFrame_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) ∧ (∀ z, z ≠ 0 → 0 < (hx X bas idx x z z).re) ∧ (∀ u v, (hx X bas idx x (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) ∧ (∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w = hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j)) ∧ (∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j) ∧ Function.Injective (pv X idx x) ∧ (∀ L : Lt E r, Submodule.span E (L : Set (Fin r → E)) = ⊤ → Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ ∧ ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ u ∈ L, ∀ v ∈ L, (hermForm Hm (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) → ∀ z w, hermForm Hm z w = hx X bas idx x z w) ∧ ∀ ga : GL (Fin r) E, IsUn X ga → lact ga x ∈ X.dom ∧ (∀ v, pv X idx (lact ga x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = pv X idx x v) ∧ (IsUnitFr X x → IsUnitFr X (lact ga x)) ∧ ∀ z w, hx X bas idx (lact ga x) z w = hx X bas idx x z w := by
  first | exact @GlobalTheory.Dict.hx_laws | exact GlobalTheory.Dict.hx_laws | (intros; apply GlobalTheory.Dict.hx_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStabiliserInvariant_pull_bounded_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ), IsUn X ga → (∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) → (∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) → HasPrinc X' M → ChiOne X' la' → X'.IsBddSec la' P → IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → DifferentiableOn ℂ (fun x => Q (lact ga (castFr h.psi x))) X'.dom ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x ∧ ∀ b ∈ Bor X'.Ψ r, Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * Q (lact ga (castFr h.psi x)) := by
  first | exact @GlobalTheory.Dict.isStabForm_pull | exact GlobalTheory.Dict.isStabForm_pull | (intros; apply GlobalTheory.Dict.isStabForm_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatticeOperatorCoefficients
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Coef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ip_smul_smul {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
    {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) (a b : ℂ) :
    ip (a • φ) (b • ψ) = a * conj b * ip φ ψ := by
  have hc : IsSB fun x => conj (ψ x) :=
    (isSB_algebra_haar_linear K κ ι ψ ψ hψ hψ).2.2.2.1
  have hp : IsSB (φ * fun x => conj (ψ x)) :=
    (isSB_algebra_haar_linear K κ ι φ _ hφ hc).2.2.1
  have hs := (isSB_algebra_haar_linear K κ ι _ _ hp hp).2.2.2.2.2.1 (a * conj b)
  have key : (fun x => (a • φ) x * conj ((b • ψ) x)) =
      (a * conj b) • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul]
    ring
  unfold ip
  rw [key, hs]
  rfl

theorem classSum_eq_sum {M : ℕ} [Fintype (Cls E n M)] (f : Lt E n → ℂ) :
    classSum M f = ∑ c : Cls E n M, (wt M (Quot.out c).1 : ℂ) * f (Quot.out c).1 := by
  unfold classSum
  exact finsum_eq_sum_of_fintype _

theorem exists_mass {M : ℕ} (hM : 0 < M) : ∃ m : ℝ, 0 < m ∧
    (∀ (f : Lt E n → ℂ) (a : ℂ), (∀ Λ ∈ Vset E n M, f Λ = a) → classSum M f = m * a) ∧
    ∀ (f : Lt E n → ℂ) (b : ℝ), (∀ Λ ∈ Vset E n M, ‖f Λ‖ ≤ b) → ‖classSum M f‖ ≤ m * b := by
  classical
  obtain ⟨hfin, hstd, hwt, -, -⟩ := finite_cls_and_stab E n M hM
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  refine ⟨∑ c : Cls E n M, wt M (Quot.out c).1, ?_, ?_, ?_⟩
  · apply Finset.sum_pos
    · intro c _
      exact (hwt _ (Quot.out c).2).2
    · exact ⟨(Quot.mk _ ⟨stdL E n, hstd⟩ : Cls E n M), Finset.mem_univ _⟩
  · intro f a hf
    rw [classSum_eq_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hf _ (Quot.out c).2]
  · intro f b hf
    rw [classSum_eq_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    have hw := (hwt _ (Quot.out c).2).2
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    exact mul_le_mul_of_nonneg_left (hf _ (Quot.out c).2) hw.le

theorem classSum_mul {M : ℕ} (hM : 0 < M) (f : Lt E n → ℂ) (a : ℂ) :
    classSum M f * a = classSum M fun Λ => f Λ * a := by
  classical
  have := (finite_cls_and_stab E n M hM).1
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  rw [classSum_eq_sum, classSum_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => mul_assoc _ _ _

end GlobalTheory.SW.Coef

namespace GlobalTheory.SW

open Coef

private theorem classSum_congr_of_eqOn_Vset {E : Type} [Field E] [NumberField E] [IsCMField E]
    {n M : ℕ} {f g : Lt E n → ℂ} (h : ∀ Λ ∈ Vset E n M, f Λ = g Λ) :
    classSum M f = classSum M g := by
  unfold classSum
  exact finsum_congr fun c => by rw [h _ (Quot.out c).2]

theorem lattice_operator_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), 0 < M → IsSystem X bas idx M Δ 𝓛 Φ μ → ∃ (a θ : ℝ), 0 < a ∧ θ < 1 ∧ (∀ L ∈ 𝓛, classSum M (fun Λ => ip (Φ L Λ) (Φ L Λ)) = a ∧ Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖) ∧ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖ ≤ θ * a) ∧ ∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, classSum M (fun Λ => ip (Φ (mapL γ L) Λ) (Φ (mapL γ L') Λ)) * μ γ L * conj (μ γ L') = classSum M (fun Λ => ip (Φ L Λ) (Φ L' Λ)) := by
  intro E _ _ _ r X g bas idx n hs hn M Δ 𝓛 Φ μ hM hsys
  obtain ⟨m, hm, hconst, hbd⟩ := Coef.exists_mass (E := E) (n := n) hM
  obtain ⟨a, ha, hdiag, b, θ, hθ, hoff, hbt⟩ := hsys.norm
  have hma : 0 < m * a := mul_pos hm ha
  refine ⟨m * a, θ, hma, hθ, fun L hL => ?_, ?_⟩
  · have hb : ∀ L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L},
        ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖ ≤ m * a * b L L'.1 := fun L' => by
      rw [mul_assoc]
      exact hbd _ (a * b L L'.1) fun Λ hΛ => hoff L hL L'.1 L'.2.1 Λ hΛ
    have hS : Summable fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => m * a * b L L'.1 :=
      (hbt L hL).1.mul_left (m * a)
    have hT := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hS
    refine ⟨?_, hT, ?_⟩
    · rw [hconst _ (a : ℂ) fun Λ hΛ => hdiag L hL Λ hΛ]
      exact (Complex.ofReal_mul m a).symm
    · calc _ ≤ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, m * a * b L L'.1 :=
            Summable.tsum_le_tsum hb hT hS
        _ = m * a * ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, b L L'.1 := tsum_mul_left
        _ ≤ m * a * θ := mul_le_mul_of_nonneg_left (hbt L hL).2 hma.le
        _ = θ * (m * a) := mul_comm _ _
  · intro γ hγ L hL L' hL'
    have hun := hsys.un γ hγ
    have key : ∀ Λ ∈ Vset E n M, ip (Φ L Λ) (Φ L' Λ) =
        ip (Φ (mapL γ L) Λ) (Φ (mapL γ L') Λ) * (μ γ L * conj (μ γ L')) := by
      intro Λ hΛ
      have hw := wG_laws E r X g bas idx n hs hn γ hun (Φ L Λ) (hsys.sb L hL Λ hΛ)
      rw [← (hw.2.2.1 (Φ L' Λ) (hsys.sb L' hL' Λ hΛ)).1, (hsys.mu γ hγ L hL).2 Λ hΛ,
        (hsys.mu γ hγ L' hL').2 Λ hΛ,
        Coef.ip_smul_smul (hsys.sb _ (hsys.stab γ hγ L hL) Λ hΛ)
          (hsys.sb _ (hsys.stab γ hγ L' hL') Λ hΛ)]
      ring
    rw [mul_assoc, Coef.classSum_mul hM]
    exact classSum_congr_of_eqOn_Vset fun Λ hΛ => (key Λ hΛ).symm

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivLetterPushforwardEqColumnActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (s : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = relab c s (e j).1) → ∀ (h : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) (F : (Fin n → Fin g → ℂ) → ℂ), AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h P))) (letterDir X hr idx) F 0 = I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s P)) (letterDir X hr idx) (fun z => F (Dict.hAct X idx h z)) 0 := by
  first | exact @GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct | exact GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct | (intros; apply GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProjProjOfGood
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ProjProj

open GlobalTheory.SW.TensVac

theorem proj_proj_of_good {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (hn : Even n) {w : E}
    {A₁ A₂ A₃ : AddSubgroup (Matrix (Fin n) (Fin r) E)} (h₂ : Good X w A₂) (h₃ : Good X w A₃)
    (hle : A₂ ≤ (A₂ ⊓ A₁) ⊔ (A₂ ⊓ A₃)) {v : TF n g} (hv : IsVac X bas w A₁ v) :
    projA X bas w A₃ (projA X bas w A₂ v) = projA X bas w A₃ v := by
  obtain ⟨v₂, hv₂, -⟩ := h₂.vac hs
  obtain ⟨v₃, hv₃, -⟩ := h₃.vac hs
  have hsb₂ := (h₂.proj idx hs hn hv.1 hv₂).1
  rw [(h₃.proj idx hs hn hsb₂ hv₃).2, (h₃.proj idx hs hn hv.1 hv₃).2]
  congr 1
  have hfin := h₂.finite idx hs hn hv.1
  have hsb : ∀ ψ ∈ hfin.toFinset, IsSB ψ := by
    intro ψ hψ
    obtain ⟨y, -, rfl⟩ := hfin.mem_toFinset.1 hψ
    exact rho_sb idx hs hn y hv.1
  have hpos : (((fun y => epsW X w y • heisG X bas y v) '' A₂).ncard : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 ((Set.ncard_pos hfin).2 ⟨_, 0, A₂.zero_mem, rfl⟩).ne'
  obtain ⟨h1, h2⟩ := sum_sb_ip _ hsb hv₃.1
  rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, ip_smul_left _ h1 hv₃.1, h2,
    Finset.sum_congr rfl (g := fun _ => SW.ip v v₃), Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul, inv_mul_cancel_left₀ hpos]
  intro ψ hψ
  obtain ⟨y, hy, rfl⟩ := hfin.mem_toFinset.1 hψ
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 (hle hy)
  show SW.ip (epsW X w (a + b) • heisG X bas (a + b) v) v₃ = SW.ip v v₃
  rw [add_comm a b, ← h₂.rho_rho idx hs hn hb.1 ha.1 hv.1, hv.2.2 a ha.2,
    ← rho_ip (w := w) idx hs hn b hv.1 hv₃.1, hv₃.2.2 b hb.2]

theorem proj_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L₁ L₂ L₃ : Lt E r, SelfD X L₁ → SelfD X L₂ → SelfD X L₃ → ∀ Λ₁ ∈ Vset E n 1, ∀ Λ₂ ∈ Vset E n 1, ∀ Λ₃ ∈ Vset E n 1, tens Λ₂ L₂ ≤ (tens Λ₂ L₂ ⊓ tens Λ₁ L₁) ⊔ (tens Λ₂ L₂ ⊓ tens Λ₃ L₃) → ∀ v : TF n g, IsVac X bas w (tens Λ₁ L₁) v → projA X bas w (tens Λ₃ L₃) (projA X bas w (tens Λ₂ L₂) v) = projA X bas w (tens Λ₃ L₃) v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L₁ L₂ L₃ _ hL₂ hL₃ Λ₁ _ Λ₂ hΛ₂ Λ₃ hΛ₃ hle v hv
  have good (L) (hL : SelfD X L) (Λ) (hΛ : Λ ∈ Vset E n 1) : Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  exact proj_proj_of_good idx hs hn (good L₂ hL₂ Λ₂ hΛ₂) (good L₃ hL₃ Λ₃ hΛ₃) hle hv

end GlobalTheory.Dict.ProjProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDefiniteHermitianOfFourMulLt
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem siegel_weil_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → SWAt Ψ n N := by
  intro E _ _ _ Ψ hΨ n N hn
  induction N with
  | zero =>
    intro _ M R φ _ Z _
    rw [Base.swd_zero, Base.swDiff_deg_zero]
  | succ N ih =>
    intro h
    exact GlobalTheory.T.siegelWeil_formula_degree_succ E Ψ hΨ n N hn h (ih (by omega))

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUniqueStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLattice_vacua_exist_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L, SelfD X L → ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, (∃ v, IsVac X bas w (tens Λ L) v) ∧ (∀ v v', IsVac X bas w (tens Λ L) v → IsSB v' → (∀ y ∈ tens Λ L, epsW X w y • heisG X bas y v' = v') → v' = ip v' v • v) ∧ (∀ φ : TF n g, IsSB φ → ∀ v, IsVac X bas w (tens Λ L) v → projA X bas w (tens Λ L) φ = ip φ v • v) ∧ ∀ L', SelfD X L' → ∀ Λ' ∈ Vset E n M, ∀ v v', IsVac X bas w (tens Λ L) v → IsVac X bas w (tens Λ' L') v' → ((tens Λ' L').relIndex (tens Λ L) : ℝ) * ‖ip v v'‖ ^ 2 = 1 := by
  first | exact @GlobalTheory.SW.TensVac.vacua | exact GlobalTheory.SW.TensVac.vacua | (intros; apply GlobalTheory.SW.TensVac.vacua <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkingsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_component_lattices_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp), (U.X k).κ0 = 2 * (U.X k).ξ0 ∧ SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (W.mark k) ∧ r = (W.F.Di (W.ik k)).p + (W.F.Di (W.ik k)).q ∧ Function.Injective (W.emb k) ∧ Submodule.span E (Set.range (W.emb k)) = ⊤ ∧ ∀ a b, (((W.F.Di (W.ik k)).EF a b : ℤ) : ℚ) = EF (U.X k) (W.emb k a) (W.emb k b) := by
  first | exact @GlobalTheory.Dict.uw_lattice | exact GlobalTheory.Dict.uw_lattice | (intros; apply GlobalTheory.Dict.uw_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumTensorLatticeFixedRationalHeisenberg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase

theorem vacS_of_isVac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas w (tens Λ L) v → ∃ A ε, VacS A ε v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L hL Λ hΛ v hv
  have hA : TensVac.Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  let e := AddEquiv.ofBijective _ (TensVac.crdHom_bijective (n := n) hs)
  have he (y) : e.symm (TensVac.crdHom hs y) = y := e.symm_apply_apply y
  have ho (y y' : Matrix (Fin n) (Fin r) E) :
      Phase.om (TensVac.crdHom hs y) (TensVac.crdHom hs y') = -∑ k, EF X (y k) (y' k) :=
    TensVac.om_crdHom hs y y'
  refine ⟨(tens Λ L).map (TensVac.crdHom hs), fun p => epsW X w (e.symm p),
    Vac.fg_map hA.1 _, ?_, ?_, ?_, ⟨2, two_pos, ?_⟩, hv.1, ?_⟩
  · intro p
    obtain ⟨y, rfl⟩ := (TensVac.crdHom_bijective hs).2 p
    rw [AddSubgroup.mem_map_iff_mem (TensVac.crdHom_bijective hs).1, hA.2.1]
    constructor
    · rintro h _ ⟨y', hy', rfl⟩
      obtain ⟨k, hk⟩ := h y' hy'
      exact ⟨-k, by rw [ho, hk, Int.cast_neg]⟩
    · intro h y' hy'
      obtain ⟨k, hk⟩ := h _ ⟨y', hy', rfl⟩
      rw [ho] at hk
      exact ⟨-k, by rw [Int.cast_neg, ← hk, neg_neg]⟩
  · rintro _ ⟨y, hy, rfl⟩
    have := congrArg norm (TensVac.epsW_mul_conj (X := X) w (e.symm (TensVac.crdHom hs y)))
    rw [norm_mul, Complex.norm_conj, norm_one] at this
    exact (mul_self_eq_one_iff.1 this).resolve_right fun h => by
      linarith [norm_nonneg (epsW X w (e.symm (TensVac.crdHom hs y)))]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    rw [← map_add, he, he, he, ho, (hA.2.2 y hy).2 y' hy', Rat.cast_neg, mul_neg]
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_nsmul, he, hA.eps_two hs hy]
  · rintro _ ⟨y, hy, rfl⟩
    rw [he]
    exact hv.2.2 y hy

end GlobalTheory.Phase
end

