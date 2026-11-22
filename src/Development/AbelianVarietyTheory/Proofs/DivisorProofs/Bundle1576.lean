import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraRepDerivationMatrix
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

theorem commutator_add_I_smul {R : Type} [Ring R] [Algebra ℂ R] (u v u' v' : R) :
    (u + Complex.I • v) * (u' + Complex.I • v') - (u' + Complex.I • v') * (u + Complex.I • v) =
      (u * u' - u' * u) + Complex.I • (u * v' - v' * u) + Complex.I • (v * u' - u' * v) - (v * v' - v' * v) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  linear_combination (norm := module) Complex.I_mul_I • (v * v' - v' * v)

theorem re_im_smul_add_I_smul {M : Type} [AddCommGroup M] [Module ℂ M] (a b : ℝ) (u v : M) :
    (a : ℂ) • u + ((-b : ℝ) : ℂ) • v + Complex.I • ((a : ℂ) • v + (b : ℂ) • u) =
      ((a : ℂ) + b * Complex.I) • (u + Complex.I • v) := by
  simp only [smul_add, add_smul, smul_smul]
  push_cast
  linear_combination (norm := module) Complex.I_mul_I • ((-(b : ℂ)) • v)

theorem exists_complexLinear_bracket_ext : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Aᴴ = A → IsUnit A.det → ∀ (B : Type) [Ring B] [Algebra ℂ B]
    (ρ : Matrix (Fin n) (Fin n) ℂ → B),
    (∀ X X', Xᴴ * A + A * X = 0 → X'ᴴ * A + A * X' = 0 → ρ (X + X') = ρ X + ρ X') →
    (∀ (c : ℝ) X, Xᴴ * A + A * X = 0 → ρ (c • X) = (c : ℂ) • ρ X) →
    (∀ X X', Xᴴ * A + A * X = 0 → X'ᴴ * A + A * X' = 0 → ρ (X * X' - X' * X) = ρ X * ρ X' - ρ X' * ρ X) →
    ∃ D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B, (∀ X X', D (X * X' - X' * X) = D X * D X' - D X' * D X) ∧
      ∀ X, Xᴴ * A + A * X = 0 → D X = ρ X := by
  intro n A hA hd B _ _ ρ hadd hr hbr
  let P : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun X => (1 / 2 : ℂ) • (X - adj A X)
  let Q : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun X => (-Complex.I / 2 : ℂ) • (X + adj A X)
  have hP : ∀ X, (P X)ᴴ * A + A * P X = 0 := fun X => (skew_parts hA hd X).1
  have hQ : ∀ X, (Q X)ᴴ * A + A * Q X = 0 := fun X => (skew_parts hA hd X).2.1
  have hPQ : ∀ X, X = P X + Complex.I • Q X := fun X => (skew_parts hA hd X).2.2
  have ssmul : ∀ (c : ℝ) Y, Yᴴ * A + A * Y = 0 → ((c : ℂ) • Y)ᴴ * A + A * ((c : ℂ) • Y) = 0 := by
    intro c Y h
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h,
      smul_zero]
  have sbr : ∀ Y Y', Yᴴ * A + A * Y = 0 → Y'ᴴ * A + A * Y' = 0 →
      (Y * Y' - Y' * Y)ᴴ * A + A * (Y * Y' - Y' * Y) = 0 := by
    intro Y Y' h h'
    have e : Yᴴ * A = -(A * Y) := eq_neg_of_add_eq_zero_left h
    have e' : Y'ᴴ * A = -(A * Y') := eq_neg_of_add_eq_zero_left h'
    have e1 : Y'ᴴ * Yᴴ * A = A * Y' * Y := by
      rw [Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc, e', Matrix.neg_mul, neg_neg]
    have e2 : Yᴴ * Y'ᴴ * A = A * Y * Y' := by
      rw [Matrix.mul_assoc, e', Matrix.mul_neg, ← Matrix.mul_assoc, e, Matrix.neg_mul, neg_neg]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    abel
  have hr' : ∀ (c : ℝ) Y, Yᴴ * A + A * Y = 0 → ρ ((c : ℂ) • Y) = (c : ℂ) • ρ Y := fun c Y h => by
    rw [Complex.coe_smul]; exact hr c Y h
  have adj_add : ∀ X X', adj A (X + X') = adj A X + adj A X' := fun X X' => by
    simp only [adj, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  have adj_smul : ∀ (c : ℂ) X, adj A (c • X) = star c • adj A X := fun c X => by
    simp only [adj, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have Padd : ∀ X X', P (X + X') = P X + P X' := fun X X' => by
    simp only [P, adj_add]; module
  have Qadd : ∀ X X', Q (X + X') = Q X + Q X' := fun X X' => by
    simp only [Q, adj_add]; module
  have Psmul : ∀ (a b : ℝ) X, P (((a : ℂ) + b * Complex.I) • X) = (a : ℂ) • P X + ((-b : ℝ) : ℂ) • Q X := by
    intro a b X
    simp only [P, Q, adj_smul]
    ext i j
    simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
    ring
  have Qsmul : ∀ (a b : ℝ) X, Q (((a : ℂ) + b * Complex.I) • X) = (a : ℂ) • Q X + (b : ℂ) • P X := by
    intro a b X
    simp only [P, Q, adj_smul]
    ext i j
    simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
    ring_nf; simp only [Complex.I_sq]; ring
  have skew_zero : (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * A + A * 0 = 0 := by simp
  have ρ0 : ρ 0 = 0 := by
    have := hadd 0 0 skew_zero skew_zero
    rw [add_zero] at this
    simpa using this
  have hsk : ∀ Y, Yᴴ * A + A * Y = 0 → adj A Y = -Y := fun Y h => by
    rw [adj, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  have PY : ∀ Y, Yᴴ * A + A * Y = 0 → P Y = Y := fun Y h => by
    simp only [P, hsk Y h]; module
  have QY : ∀ Y, Yᴴ * A + A * Y = 0 → Q Y = 0 := fun Y h => by
    simp only [Q, hsk Y h, add_neg_cancel, smul_zero]
  let D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B :=
    { toFun := fun X => ρ (P X) + Complex.I • ρ (Q X)
      map_add' := fun X X' => by
        rw [Padd, Qadd, hadd _ _ (hP _) (hP _), hadd _ _ (hQ _) (hQ _), smul_add]
        abel
      map_smul' := fun c X => by
        obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = a + b * Complex.I := ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
        simp only [RingHom.id_apply]
        rw [Psmul, Qsmul, hadd _ _ (ssmul _ _ (hP _)) (ssmul _ _ (hQ _)),
          hadd _ _ (ssmul _ _ (hQ _)) (ssmul _ _ (hP _)), hr' _ _ (hP _), hr' _ _ (hQ _), hr' _ _ (hQ _),
          hr' _ _ (hP _)]
        exact re_im_smul_add_I_smul a b _ _ }
  have hD : ∀ X, D X = ρ (P X) + Complex.I • ρ (Q X) := fun X => rfl
  have hDs : ∀ Y, Yᴴ * A + A * Y = 0 → D Y = ρ Y := fun Y h => by
    rw [hD, PY Y h, QY Y h, ρ0, smul_zero, add_zero]
  have key : ∀ p q p' q', pᴴ * A + A * p = 0 → qᴴ * A + A * q = 0 → p'ᴴ * A + A * p' = 0 →
      q'ᴴ * A + A * q' = 0 →
      D ((p + Complex.I • q) * (p' + Complex.I • q') - (p' + Complex.I • q') * (p + Complex.I • q)) =
        D (p + Complex.I • q) * D (p' + Complex.I • q') - D (p' + Complex.I • q') * D (p + Complex.I • q) := by
    intro p q p' q' hp hq hp' hq'
    rw [commutator_add_I_smul, map_sub, map_add, map_add, map_smul, map_smul, hDs _ (sbr _ _ hp hp'),
      hDs _ (sbr _ _ hp hq'), hDs _ (sbr _ _ hq hp'), hDs _ (sbr _ _ hq hq'), hbr _ _ hp hp', hbr _ _ hp hq',
      hbr _ _ hq hp', hbr _ _ hq hq', map_add, map_add, map_smul, map_smul, hDs _ hp, hDs _ hq, hDs _ hp', hDs _ hq',
      commutator_add_I_smul]
  refine ⟨D, fun X X' => ?_, hDs⟩
  have := key _ _ _ _ (hP X) (hQ X) (hP X') (hQ X')
  rwa [← hPQ X, ← hPQ X'] at this

end GlobalTheory.LeviHC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

open Matrix GlobalTheory.SmoothForms
open GlobalTheory.Orb (archMat)

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.LeviHC.LineLie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

section Chart

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def sigA (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := A⁻¹ * Xᴴ * A
  map_add' X Y := by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    change A⁻¹ * (c • X)ᴴ * A = c • (A⁻¹ * Xᴴ * A)
    rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]

abbrev LieL (A : Matrix (Fin n) (Fin n) ℂ) : Type := ↥(GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU A).toSubmodule

def jA (A : Matrix (Fin n) (Fin n) ℂ) : LieL A →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU A).toSubmodule.subtype

variable (σ J) in
open Classical in

def secA (τ : EmbOver E w) (u : Matrix (Fin n) (Fin n) ℂ) : GAd σ J :=
  if hu : ∃ y : GArch σ J w, archMat σ J τ y = u then embArch σ J w hu.choose else 1

theorem archMat_injective (h : IsCMExt F E σ) (τ : EmbOver E w) : Function.Injective (archMat σ J τ) := fun a b e => by
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
  exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))

theorem secA_archMat (h : IsCMExt F E σ) (τ : EmbOver E w) (y : GArch σ J w) :
    secA σ J τ (archMat σ J τ y) = embArch σ J w y := by
  have hu : ∃ y' : GArch σ J w, archMat σ J τ y' = archMat σ J τ y := ⟨y, rfl⟩
  rw [secA, dif_pos hu, archMat_injective h τ hu.choose_spec]

theorem exists_archMat (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) {u : Matrix (Fin n) (Fin n) ℂ}
    (hu : sigA (J.map τ.1) u * u = 1) : ∃ y : GArch σ J w, archMat σ J τ y = u := by
  have hA := isUnit_det_map hJ τ.1
  have hu1 : (J.map τ.1)⁻¹ * uᴴ * J.map τ.1 * u = 1 := hu
  have hu2 : uᴴ * J.map τ.1 * u = J.map τ.1 := by
    have := congrArg (J.map τ.1 * ·) hu1
    simpa only [← Matrix.mul_assoc, mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.mul_one] using this
  let v : GL (Fin n) ℂ := ⟨u, (J.map τ.1)⁻¹ * uᴴ * J.map τ.1, mul_eq_one_comm.1 hu1, hu1⟩
  refine ⟨(archEquiv J h τ).symm ⟨v, show _ * _ * _ = _ from hu2⟩, ?_⟩
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]

theorem isLieData (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    IsLieData (sigA (J.map τ.1)) (jA (J.map τ.1)) (secA σ J τ) := by
  have hA := isUnit_det_map hJ τ.1
  have hAh := conjTranspose_map h hJ τ.1
  have anti : ∀ a b, sigA (J.map τ.1) (a * b) = sigA (J.map τ.1) b * sigA (J.map τ.1) a := fun a b => by
    change _ * (a * b)ᴴ * _ = (_ * bᴴ * _) * (_ * aᴴ * _)
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hA]
  refine ⟨anti, ?_, fun a => ?_, Subtype.val_injective, fun X => ⟨fun hX => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change (J.map τ.1)⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J.map τ.1 = 1
    rw [conjTranspose_one, Matrix.mul_one, nonsing_inv_mul _ hA]
  · change _ * (_ * aᴴ * _)ᴴ * _ = a
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hAh]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hA, nonsing_inv_mul _ hA, Matrix.mul_one]
  · refine ⟨⟨X, ?_⟩, rfl⟩
    have h1 : (J.map τ.1)⁻¹ * Xᴴ * J.map τ.1 = -X := hX
    change Xᴴ * J.map τ.1 + J.map τ.1 * X = 0
    rw [← mul_nonsing_inv_cancel_left _ (Xᴴ * J.map τ.1) hA, ← Matrix.mul_assoc (J.map τ.1)⁻¹, h1, Matrix.mul_neg,
      neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    have h1 : Y.1ᴴ * J.map τ.1 + J.map τ.1 * Y.1 = 0 := Y.2
    change _ * Y.1ᴴ * _ = -Y.1
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h1, Matrix.mul_neg, nonsing_inv_mul_cancel_left _ _ hA]
  · have hab : sigA (J.map τ.1) (a * b) * (a * b) = 1 := by
      rw [anti, Matrix.mul_assoc, ← Matrix.mul_assoc (sigA (J.map τ.1) a), ha, Matrix.one_mul, hb]
    obtain ⟨ya, rfl⟩ := exists_archMat h hJ τ ha
    obtain ⟨yb, rfl⟩ := exists_archMat h hJ τ hb
    rw [← map_mul, secA_archMat h, secA_archMat h, secA_archMat h, map_mul]

theorem hasLog (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    HasLog (sigA (J.map τ.1)) (jA (J.map τ.1)) :=
  GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData _ _ _ _ _ _ (isLieData h hJ τ)

theorem isLineOf_expMap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (Y : LieL (J.map τ.1)) :
    IsLineOf σ J τ Y.1 fun t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • Y) := fun t => by
  have hA := isUnit_det_map hJ τ.1
  have hY : (t • Y.1)ᴴ * J.map τ.1 + J.map τ.1 * (t • Y.1) = 0 := by
    have h1 : Y.1ᴴ * J.map τ.1 + J.map τ.1 * Y.1 = 0 := Y.2
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  have h1 : (NormedSpace.exp (t • Y.1))ᴴ * J.map τ.1 * NormedSpace.exp (t • Y.1) = J.map τ.1 :=
    GlobalTheory.SmoothForms.exp_mem_UH hA hY
  have hu : sigA (J.map τ.1) (NormedSpace.exp (t • Y.1)) * NormedSpace.exp (t • Y.1) = 1 := by
    change (J.map τ.1)⁻¹ * _ * J.map τ.1 * _ = 1
    rw [Matrix.mul_assoc _ _ (J.map τ.1), Matrix.mul_assoc, h1, nonsing_inv_mul _ hA]
  obtain ⟨y, hy⟩ := exists_archMat h hJ τ hu
  refine ⟨y, ?_, hy⟩
  change secA σ J τ (NormedSpace.exp (t • Y.1)) = _
  rw [← hy, secA_archMat h]

theorem sm_of_isSm (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) {f : GAd σ J → ℂ} (hf : IsSm σ J f) :
    Sm (expMap (jA (J.map τ.1)) (secA σ J τ)) f := by
  rw [GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind _ _ _ _ _ _ (isLieData h hJ τ) (hasLog h hJ τ) Set.univ Submodule.span_univ]
  intro k Y _ g
  exact hf k (fun i t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • Y i))
    (fun i => (isLineOf_expMap h hJ τ (Y i)).isRealLine h) g

theorem lineDer_add_bracket : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (f : GAd σ J → ℂ), IsSm σ J f →
    ∀ (X X' : Matrix (Fin n) (Fin n) ℂ) (γ δ ε : ℝ → GAd σ J), IsLineOf σ J τ X γ → IsLineOf σ J τ X' δ →
      (IsLineOf σ J τ (X + X') ε → lineDer ε f = lineDer γ f + lineDer δ f) ∧
      (IsLineOf σ J τ (X * X' - X' * X) ε → lineDer ε f = lineDer γ (lineDer δ f) - lineDer δ (lineDer γ f)) := by
  intro F E _ _ _ _ _ σ h n J hJ w τ f hf X X' γ δ ε hγ hδ
  have H := isLieData h hJ τ
  have hl := hasLog h hJ τ
  have hs := sm_of_isSm h hJ τ hf
  have hX := hγ.skew h
  have hX' := hδ.skew h
  let Y : LieL (J.map τ.1) := ⟨X, hX⟩
  let Y' : LieL (J.map τ.1) := ⟨X', hX'⟩
  obtain rfl : γ = _ := hγ.unique h (isLineOf_expMap h hJ τ Y)
  obtain rfl : δ = _ := hδ.unique h (isLineOf_expMap h hJ τ Y')
  refine ⟨fun hε => ?_, fun hε => ?_⟩
  · obtain rfl : ε = _ := hε.unique h (isLineOf_expMap h hJ τ (Y + Y'))
    exact (GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear _ _ _ _ _ _ H hl f hs).2.1 Y Y'
  · have hZ := hε.skew h
    let Z : LieL (J.map τ.1) := ⟨X * X' - X' * X, hZ⟩
    obtain rfl : ε = _ := hε.unique h (isLineOf_expMap h hJ τ Z)
    exact (GlobalTheory.T.rightDerivativeAlongLie_commutator_eq_bracket _ _ _ _ _ _ H hl f hs Y Y' Z rfl).symm

end Chart

end GlobalTheory.LeviHC.LineLie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeBlockConjugate
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.BlockTriLine

open NormedSpace in
theorem entry_exp_sub_one {m : ℕ} (b : Fin m → ℕ) (s : ℕ) (W : Matrix (Fin m) (Fin m) ℂ)
    (hW : ∀ i j, b j < b i + s → W i j = 0) : ∀ i j, b j < b i + s → (exp W - 1) i j = 0 := by
  have hpow : ∀ k, ∀ i j, b j < b i + s → (W ^ (k + 1)) i j = 0 := by
    intro k
    induction k with
    | zero => simpa using hW
    | succ k ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases h : b l < b i + s
      · rw [ih i l h, zero_mul]
      · rw [hW l j (by omega), mul_zero]
  intro i j hij
  have hs : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • W ^ n) (exp W) := by
    open scoped Matrix.Norms.Operator in exact exp_series_hasSum_exp' (𝕂 := ℂ) W
  have h1 := hs.map (Matrix.entryAddMonoidHom ℂ i j) (continuous_id.matrix_elem i j)
  have h2 : HasSum (⇑(Matrix.entryAddMonoidHom ℂ i j) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • W ^ n)
      ((1 : Matrix (Fin m) (Fin m) ℂ) i j) := by
    convert hasSum_single (f := ⇑(Matrix.entryAddMonoidHom ℂ i j) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • W ^ n) 0 _
    · show _ = ((((Nat.factorial 0 : ℕ) : ℂ))⁻¹ • W ^ 0) i j
      simp
    · intro k hk
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      show ((((k + 1).factorial : ℂ))⁻¹ • W ^ (k + 1)) i j = 0
      rw [Matrix.smul_apply, hpow k i j hij, smul_zero]
  rw [Matrix.sub_apply, sub_eq_zero]
  exact h1.unique h2

open NormedSpace in

theorem conj_exp {n m : ℕ} (R : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ) (hQR : Q * R = 1)
    (hRQ : R * Q = 1) (X : Matrix (Fin n) (Fin n) ℂ) : R * exp X * Q = exp (R * X * Q) := by
  let L : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun A => R * A * Q
      map_one' := by simp [hRQ]
      map_mul' := fun A B => by
        calc R * (A * B) * Q = R * A * (Q * R) * B * Q := by rw [hQR, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc]
      map_zero' := by simp
      map_add' := fun A B => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hc : Continuous L := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  open scoped Matrix.Norms.Operator in exact map_exp L hc X

open NormedSpace in

theorem entry_conj_exp {n m : ℕ} (R : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ) (hQR : Q * R = 1)
    (hRQ : R * Q = 1) (b : Fin m → ℕ) (s : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ)
    (hZ : ∀ i j, b j < b i + s → (R * Z * Q) i j = 0) (t : ℝ) :
    ∀ i j, b j < b i + s → (R * (exp (t • Z) - 1) * Q : Matrix (Fin m) (Fin m) ℂ) i j = 0 := by
  have e : (R * (exp (t • Z) - 1) * Q : Matrix (Fin m) (Fin m) ℂ) = exp (t • (R * Z * Q)) - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRQ, conj_exp R Q hQR hRQ]
    congr 2
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  refine entry_exp_sub_one b s _ fun i j hij => ?_
  rw [Matrix.smul_apply, hZ i j hij, smul_zero]

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

variable (F E) in

def placeToAdeles (w : InfinitePlace F) : w.Completion ⊗[F] E →ₙ+* AE F E :=
  (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (R' := AF F) (LinearMap.inl F (Ainf F) (Af F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm)).comp
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AutFunCompare.sgW w) (GlobalTheory.AutFunCompare.sgW_mul w))

theorem placeToAdeles_apply (x : w.Completion ⊗[F] E) :
    placeToAdeles F E w x = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (R' := AF F) (LinearMap.inl F (Ainf F) (Af F))
      (fun _ _ => Prod.ext rfl (mul_zero _).symm)
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AutFunCompare.sgW w) (GlobalTheory.AutFunCompare.sgW_mul w) x) := rfl

theorem mat_embArch_sub_one (y : GArch σ J w) :
    (((embArch σ J w y).1 : GL (Fin n) (AE F E)).1 - 1 : Matrix (Fin n) (Fin n) (AE F E)) =
      ((y.1 : GL (Fin n) (w.Completion ⊗[F] E)).1 - 1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)).map
        (placeToAdeles F E w) := by
  ext r s
  rw [Matrix.sub_apply, Matrix.map_apply, Matrix.sub_apply]
  have e1 := GlobalTheory.AutFunCompare.mat_extH (R' := AF F) σ J (LinearMap.inl F (Ainf F) (Af F))
    (fun _ _ => Prod.ext rfl (mul_zero _).symm) (embArchInf σ J w y) r s
  have e2 := GlobalTheory.AutFunCompare.mat_extH σ J (GlobalTheory.AutFunCompare.sgW w) (GlobalTheory.AutFunCompare.sgW_mul w) y r s
  change (HA.mat _ σ J (ofInf σ J (embArchInf σ J w y))).1 r s - _ = placeToAdeles F E w ((HA.mat _ σ J y).1 r s - _)
  rw [ofInf, e1]
  erw [e2]
  rw [placeToAdeles_apply]
  by_cases h : r = s
  · subst h
    simp only [Matrix.one_apply_eq, mul_one, map_sub, map_add]
    ring
  · simp [Matrix.one_apply_ne h]

theorem placeToAdeles_inclR_mul (e : E) (x : w.Completion ⊗[F] E) :
    placeToAdeles F E w (inclR (F := F) w.Completion e * x) = inclR (F := F) (AF F) e * placeToAdeles F E w x := by
  have h1 : placeToAdeles F E w (inclR (F := F) w.Completion e) = inclR (F := F) (AF F) e * placeToAdeles F E w 1 := by
    show placeToAdeles F E w ((1 : w.Completion) ⊗ₜ[F] e) =
      ((1 : AF F) ⊗ₜ[F] e) * placeToAdeles F E w ((1 : w.Completion) ⊗ₜ[F] (1 : E))
    rw [placeToAdeles_apply, placeToAdeles_apply]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul]
    erw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul]
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [map_mul, h1, mul_assoc, ← map_mul, one_mul]

theorem incM_mul_map_mul {m : ℕ} (R : Matrix (Fin m) (Fin n) E) (Q : Matrix (Fin n) (Fin m) E)
    (N : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) :
    (incM F R * N.map (placeToAdeles F E w) * incM F Q : Matrix (Fin m) (Fin m) (AE F E)) =
      (R.map (inclR (F := F) w.Completion) * N * Q.map (inclR (F := F) w.Completion)).map (placeToAdeles F E w) := by
  have key : ∀ (a c : E) (x : w.Completion ⊗[F] E), inclR (F := F) (AF F) a * placeToAdeles F E w x *
      inclR (F := F) (AF F) c = placeToAdeles F E w (inclR (F := F) w.Completion a * x * inclR (F := F) w.Completion c) := by
    intro a c x
    have k : placeToAdeles F E w (inclR (F := F) w.Completion c * (inclR (F := F) w.Completion a * x)) =
        inclR (F := F) (AF F) c * (inclR (F := F) (AF F) a * placeToAdeles F E w x) :=
      (placeToAdeles_inclR_mul c _).trans (congrArg (inclR (F := F) (AF F) c * ·) (placeToAdeles_inclR_mul a x))
    calc _ = inclR (F := F) (AF F) c * (inclR (F := F) (AF F) a * placeToAdeles F E w x) := by ring
      _ = _ := k.symm
      _ = _ := congrArg _ (by ring)
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, incM, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  exact key _ _ _

end Adelic

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

theorem map_infEmb_conj (τ : EmbOver E w) {m : ℕ} (R : Matrix (Fin m) (Fin n) E) (Q : Matrix (Fin n) (Fin m) E)
    (y : GArch σ J w) :
    (R.map (inclR (F := F) w.Completion) * ((y.1 : GL (Fin n) (w.Completion ⊗[F] E)).1 - 1) *
        Q.map (inclR (F := F) w.Completion)).map (infEmb τ) =
      R.map τ.1 * (GlobalTheory.Orb.archMat σ J τ y - 1) * Q.map τ.1 := by
  have hι : (infEmb τ ∘ inclR (F := F) w.Completion) = τ.1 := funext fun e => by
    show infEmb τ ((1 : w.Completion) ⊗ₜ[F] e) = τ.1 e
    rw [infEmb_tmul, map_one, one_mul]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, hι, GlobalTheory.Orb.archMat_apply]
  congr 2
  ext r s
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
  split_ifs <;> simp <;> rfl

theorem entry_embArch (h : IsCMExt F E σ) (τ : EmbOver E w) {m : ℕ} (R : Matrix (Fin m) (Fin n) E)
    (Q : Matrix (Fin n) (Fin m) E) (b : Fin m → ℕ) (s : ℕ) (y : GArch σ J w)
    (hy : ∀ i j, b j < b i + s → (R.map τ.1 * (GlobalTheory.Orb.archMat σ J τ y - 1) * Q.map τ.1 : Matrix (Fin m) (Fin m) ℂ) i j = 0) :
    ∀ i j, b j < b i + s →
      (incM F R * (((embArch σ J w y).1 : GL (Fin n) (AE F E)).1 - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F Q :
        Matrix (Fin m) (Fin m) (AE F E)) i j = 0 := by
  intro i j hij
  rw [mat_embArch_sub_one, incM_mul_map_mul, Matrix.map_apply]
  have h0 : (R.map (inclR (F := F) w.Completion) * ((y.1 : GL (Fin n) (w.Completion ⊗[F] E)).1 - 1) *
      Q.map (inclR (F := F) w.Completion) : Matrix (Fin m) (Fin m) (w.Completion ⊗[F] E)) i j = 0 := by
    apply (infEmb_bijective h τ).1
    rw [map_zero, ← hy i j hij, ← map_infEmb_conj τ R Q y]
    rfl
  rw [h0, map_zero]

end Main

open NormedSpace in

theorem blockTri_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (m : ℕ) (Q : Matrix (Fin n) (Fin m) E) (R : Matrix (Fin m) (Fin n) E), Q * R = 1 → R * Q = 1 →
    ∀ (b : Fin m → ℕ) (s : ℕ) (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J),
      IsLineOf σ J τ Z γ → (∀ i j, b j < b i + s → (R.map τ.1 * Z * Q.map τ.1) i j = 0) → ∀ t i j, b j < b i + s →
        (incM F R * (((γ t).1 : GL (Fin n) (AE F E)).1 - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F Q : Matrix (Fin m) (Fin m) (AE F E)) i j = 0 ∧
        (incM F R * ((((γ t)⁻¹).1 : GL (Fin n) (AE F E)).1 - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F Q : Matrix (Fin m) (Fin m) (AE F E)) i j = 0 := by
  intro F E _ _ _ _ _ σ h n J _ m Q R hQR hRQ b s w τ Z γ hγ hZ t i j hij
  have hQR' : Q.map τ.1 * R.map τ.1 = 1 := by
    rw [← Matrix.map_mul, hQR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hRQ' : R.map τ.1 * Q.map τ.1 = 1 := by
    rw [← Matrix.map_mul, hRQ, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨y, hy1, hy2⟩ := hγ t
  have hA : GlobalTheory.Orb.archMat σ J τ y⁻¹ = exp ((-t) • Z) := by
    have e1 : GlobalTheory.Orb.archMat σ J τ y⁻¹ * GlobalTheory.Orb.archMat σ J τ y = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have e2 : exp (t • Z) * exp ((-t) • Z) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left t).smul_right (-t)), ← add_smul,
        add_neg_cancel, zero_smul, exp_zero]
    calc GlobalTheory.Orb.archMat σ J τ y⁻¹ = GlobalTheory.Orb.archMat σ J τ y⁻¹ * (exp (t • Z) * exp ((-t) • Z)) := by
          rw [e2, Matrix.mul_one]
      _ = (GlobalTheory.Orb.archMat σ J τ y⁻¹ * GlobalTheory.Orb.archMat σ J τ y) * exp ((-t) • Z) := by
          rw [hy2, Matrix.mul_assoc]
      _ = _ := by rw [e1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · rw [hy1]
    refine entry_embArch h τ R Q b s y (fun i j hij => ?_) i j hij
    rw [hy2]
    exact entry_conj_exp _ _ hQR' hRQ' b s Z hZ t i j hij
  · rw [hy1, ← map_inv]
    refine entry_embArch h τ R Q b s y⁻¹ (fun i j hij => ?_) i j hij
    rw [hA]
    exact entry_conj_exp _ _ hQR' hRQ' b s Z hZ (-t) i j hij

end GlobalTheory.LeviHC.BlockTriLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemHilbertFunctionEqFinrankConePieceStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSystemHilbertFunction_eq_finrank_conePiece : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (N : ℕ) (b : Module.Basis (Fin N) K V) (τ : ℕ), hilb ev τ = ((Module.finrank K (GlobalTheory.quotPiece (imageIdeal ev b) (τ : ℤ)) : ℕ) : ℕ∞) := by
  first | exact @GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece | exact GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece | (intros; apply GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuumStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum : GlobalTheory.ColNorms.FamilyTie := by
  first | exact @GlobalTheory.FamilyTieProof.familyTie | exact GlobalTheory.FamilyTieProof.familyTie | (intros; apply GlobalTheory.FamilyTieProof.familyTie <;> assumption)
end

