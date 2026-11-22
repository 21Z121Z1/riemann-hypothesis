import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistInvTransposeDetChar
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.InvTransposeTwist

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_invTranspose (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (GlobalTheory.TypeTame.invTranspose n g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  ext
  simp [GlobalTheory.TypeTame.invTranspose, Matrix.GeneralLinearGroup.det, Matrix.det_transpose]

theorem nabs_inv (x : kˣ) : GlobalTheory.SplitWeil.nabs k x⁻¹ = (GlobalTheory.SplitWeil.nabs k x)⁻¹ := by
  simp [GlobalTheory.SplitWeil.nabs]

theorem absPow_det_invTranspose (n : ℕ) (s : ℂ) (g : GL (Fin n) k) :
    detChar (Fin n) (absPow k s) (GlobalTheory.TypeTame.invTranspose n g) =
      detChar (Fin n) (absPow k (-s)) g := by
  ext
  have hp := GlobalTheory.SplitWeil.nabs_pos k (Matrix.GeneralLinearGroup.det g)
  simp only [detChar, absPow, MonoidHom.comp_apply, det_invTranspose]
  simp [nabs_inv, Complex.cpow_neg]

theorem twist_comp_invTranspose (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ) :
    (twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n) =
      twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))) := by
  ext g v
  simp only [MonoidHom.comp_apply, twist, MonoidHom.coe_mk, OneHom.coe_mk, absPow_det_invTranspose]

end GlobalTheory.InvTransposeTwist

theorem GlobalTheory.InvTransposeTwist.main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ), Nonempty (Representation.Equiv ((twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n)) (twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))))) := by
  intro k _ _ _ _ n V _ _ π s
  rw [GlobalTheory.InvTransposeTwist.twist_comp_invTranspose]
  exact ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => rfl)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerEquivNormOneTorusNonsplit
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

theorem twCent_iff_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (β : B.A), IsUnit (GlobalTheory.TwLat.gram e b β) → ∀ g : GLw m w, g ∈ twCent (thL m w) (GlobalTheory.TwLat.dlt e b β) ↔ g.valᵀ * GlobalTheory.TwLat.gram e b β * g.val.map (cj w) = GlobalTheory.TwLat.gram e b β := by
  intro E _ _ _ w hw K e B m b β hG g
  have hth : thL m w = thetaGL m (cj w) := by rw [thL, if_neg hw]
  have hd : dlt e b β = invT m _ hG.unit * (PhiU m _)⁻¹ := by rw [dlt, dif_pos hG]
  rw [hth, hd]
  change g * _ = _ * _ ↔ _
  rw [Units.ext_iff]
  set G := gram e b β with hGdef
  set Φ := GlobalTheory.Tw.Phi m (w.adicCompletion E) with hΦdef
  have hΦ' : Φᵀ * Φ = 1 := mul_eq_one_comm.1 (Phi_mul_transpose m _)
  set Gi := (hG.unit⁻¹).val with hGidef
  have hGi1 : G * Gi = 1 := hG.unit.mul_inv
  have hGi2 : Gi * G = 1 := hG.unit.inv_mul
  set H := g.val.map (cj w) with hHdef
  set Hi := (g⁻¹ : GLw m w).val.map (cj w) with hHidef
  have hH : H * Hi = 1 := by
    rw [hHdef, hHidef, show g.val.map (cj w) = (cj w).mapMatrix g.val from rfl,
      show (g⁻¹ : GLw m w).val.map (cj w) = (cj w).mapMatrix (g⁻¹ : GLw m w).val from rfl, ← map_mul, Units.mul_inv,
      map_one]
  have hL : (g * (invT m _ hG.unit * (PhiU m _)⁻¹)).val = g.val * (Giᵀ * Φᵀ) := rfl
  have hR : (invT m _ hG.unit * (PhiU m _)⁻¹ * thetaGL m (cj w) g).val = Giᵀ * Φᵀ * (Φ * Hiᵀ * Φᵀ) := rfl
  rw [hL, hR]
  have hA : Giᵀ * Φᵀ * (Φ * Hiᵀ * Φᵀ) = Giᵀ * Hiᵀ * Φᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Φᵀ Φ, hΦ', Matrix.one_mul]
  rw [hA]
  have hB : g.val * (Giᵀ * Φᵀ) = Giᵀ * Hiᵀ * Φᵀ ↔ g.val * Giᵀ = Giᵀ * Hiᵀ := by
    constructor
    · intro h
      have := congrArg (· * Φ) h
      simp only [Matrix.mul_assoc, hΦ', Matrix.mul_one] at this
      simpa only [Matrix.mul_assoc] using this
    · intro h
      rw [← Matrix.mul_assoc, h]
  rw [hB]
  have hC : g.val * Giᵀ = Giᵀ * Hiᵀ ↔ Gi * g.valᵀ = Hi * Gi := by
    rw [← Matrix.transpose_inj]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hC]
  constructor
  · intro h
    calc g.valᵀ * G * H = (G * Gi) * g.valᵀ * G * H := by rw [hGi1, Matrix.one_mul]
      _ = G * (Gi * g.valᵀ) * G * H := by simp only [Matrix.mul_assoc]
      _ = G * Hi * (Gi * G) * H := by rw [h]; simp only [Matrix.mul_assoc]
      _ = G * (Hi * H) := by rw [hGi2, Matrix.mul_one, Matrix.mul_assoc]
      _ = G := by rw [mul_eq_one_comm.1 hH, Matrix.mul_one]
  · intro h
    calc Gi * g.valᵀ = Gi * g.valᵀ * ((G * H) * Hi * Gi) := by
          rw [Matrix.mul_assoc G, hH, Matrix.mul_one, hGi1, Matrix.mul_one]
      _ = Gi * (g.valᵀ * G * H) * Hi * Gi := by simp only [Matrix.mul_assoc]
      _ = Hi * Gi := by rw [h, hGi2, Matrix.one_mul]

theorem herm_finsum_left {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (β : B.A) {ι : Type} (s : Finset ι)
    (v : ι → K.E) (x : ι → B.A) (z : B.A) :
    B.herm β (∑ i ∈ s, v i • x i) z = ∑ i ∈ s, v i * B.herm β (x i) z := by
  simp only [GlobalTheory.UnitLemma.InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc,
    map_smul, smul_eq_mul]

theorem herm_finsum_right {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (β y : B.A) {ι : Type} (s : Finset ι)
    (r : ι → K.E) (x : ι → B.A) :
    B.herm β y (∑ i ∈ s, r i • x i) = ∑ i ∈ s, K.c (r i) * B.herm β y (x i) := by
  simp only [GlobalTheory.UnitLemma.InvAlg.herm, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, RingEquiv.map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem gram_isometry_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (β : B.A) (f : B.A →ₗ[K.E] B.A), ((LinearMap.toMatrix b b f).map e)ᵀ * GlobalTheory.TwLat.gram e b β * ((LinearMap.toMatrix b b f).map e).map (cj w) = GlobalTheory.TwLat.gram e b β ↔ ∀ y z, B.herm β (f y) (f z) = B.herm β y z := by
  intro E _ _ _ w K e hec B m b β f
  set M := LinearMap.toMatrix b b f with hM
  have hf : ∀ i, f (b i) = ∑ k, M k i • b k := by
    intro i
    simp only [hM, LinearMap.toMatrix_apply]
    exact (b.sum_repr (f (b i))).symm
  have hent : ∀ i j, ((M.map e)ᵀ * gram e b β * (M.map e).map (cj w)) i j = e (B.herm β (f (b i)) (f (b j))) := by
    intro i j
    rw [hf i, hf j, herm_finsum_left]
    simp only [herm_finsum_right, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, gram, Matrix.of_apply,
      Finset.mul_sum, Finset.sum_mul, map_sum, map_mul, hec]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  constructor
  · intro h y z
    have hij : ∀ i j, B.herm β (f (b i)) (f (b j)) = B.herm β (b i) (b j) := by
      intro i j
      apply e.injective
      rw [← hent, h]
      rfl
    rw [← b.sum_repr y, ← b.sum_repr z]
    simp only [map_sum, map_smul, herm_finsum_left, herm_finsum_right, hij]
  · intro h
    ext i j
    rw [hent, h]
    rfl

theorem twCent_equiv_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit β → B.σ β = β * ((-1) ^ (m - 1) * u) → Algebra.adjoin K.E {u} = ⊤ → IsUnit (GlobalTheory.TwLat.gram e b β) → ∃ φ : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β) ≃* B.T, (∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), (t : GLw m w).val = GlobalTheory.TwLat.mulMat e b (((φ t : B.T) : B.Aˣ) : B.A)) ∧ ∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), ((t : GLw m w) ∈ cptPart (twCent (thL m w) (GlobalTheory.TwLat.dlt e b β)) ↔ ((φ t : B.T) : B.Aˣ) ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  intro E _ _ _ hE w hw K e hec hint hval B m b u β hβu hβ hadj hG

  have hnd : ∀ y, (∀ z, B.herm β y z = 0) → y = 0 := by
    intro y hy
    have hsum : ∀ z, B.herm β y z = ∑ i, b.repr y i * B.herm β (b i) z := by
      intro z
      conv_lhs => rw [← b.sum_repr y]
      simp only [GlobalTheory.UnitLemma.InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm,
        smul_mul_assoc, map_smul, smul_eq_mul]
    have h1 : Matrix.vecMul (fun i => e (b.repr y i)) (gram e b β) = 0 := by
      funext j
      have := congrArg e (hsum (b j))
      rw [hy, map_zero, map_sum] at this
      simp only [Matrix.vecMul, dotProduct, gram, Matrix.of_apply, Pi.zero_apply]
      rw [this]
      simp only [map_mul]
    have hGi : gram e b β * (gram e b β)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hG)
    have h2 : (fun i => e (b.repr y i)) = 0 := by
      rw [← Matrix.vecMul_one (fun i => e (b.repr y i)), ← hGi, ← Matrix.vecMul_vecMul, h1, Matrix.zero_vecMul]
    have h3 : b.repr y = 0 := by
      ext i
      have := congrFun h2 i
      simpa using this
    simpa using h3

  have hT : ∀ t : B.Aˣ, t ∈ B.T → mulU e b t ∈ twCent (thL m w) (dlt e b β) := by
    intro t ht
    have ht' : (t : B.A) * B.σ (t : B.A) = 1 := ht
    rw [twCent_iff_gram E w hw K e B m b β hG]
    refine (gram_isometry_iff E w K e hec B m b β (LinearMap.mulLeft K.E (t : B.A))).2 fun y z => ?_
    simp only [LinearMap.mulLeft_apply, GlobalTheory.UnitLemma.InvAlg.herm]
    rw [map_mul B.σ, show β * ((t : B.A) * y) * (B.σ t * B.σ z) = β * y * B.σ z * ((t : B.A) * B.σ t) by ring,
      ht', mul_one]

  have hsurj : ∀ g : GLw m w, g ∈ twCent (thL m w) (dlt e b β) → ∃ t : B.Aˣ, t ∈ B.T ∧ mulU e b t = g := by
    intro g hg
    have hg1 := (twCent_iff_gram E w hw K e B m b β hG g).1 hg
    let em := (e.symm : w.adicCompletion E →+* K.E).mapMatrix (m := Fin m)
    let f : B.A →ₗ[K.E] B.A := Matrix.toLin b b (em g.val)
    have hfM : (LinearMap.toMatrix b b f).map e = g.val := by
      simp only [f, LinearMap.toMatrix_toLin, em, RingHom.mapMatrix_apply, Matrix.map_map]
      ext i j; simp
    have hiso := (gram_isometry_iff E w K e hec B m b β f).1 (by rw [hfM]; exact hg1)
    have hfs : Function.Surjective f := by
      intro y
      refine ⟨Matrix.toLin b b (em (g⁻¹ : GLw m w).val) y, ?_⟩
      rw [← LinearMap.comp_apply, ← Matrix.toLin_mul, ← map_mul, Units.mul_inv, map_one, Matrix.toLin_one,
        LinearMap.id_apply]
    obtain ⟨a, haT, hfa⟩ := GlobalTheory.T.traceForm_linearIsometry_eq_mul_normOneTorus K B (m - 1) u β hβ hadj hnd f hfs hiso
    refine ⟨a, haT, Units.ext ?_⟩
    rw [mulU_val, ← hfM]
    have : LinearMap.mulLeft K.E (a : B.A) = f := LinearMap.ext fun y => (hfa y).symm
    rw [mulMat, this]
  let ψ : B.T →* twCent (thL m w) (dlt e b β) :=
    { toFun := fun t => ⟨mulU e b t, hT t t.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp) }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun s t h => Subtype.ext (mulU_injective e b (congrArg Subtype.val h)), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨t, ht, rfl⟩ := hsurj g hg
    exact ⟨⟨t, ht⟩, rfl⟩
  let φ := (MulEquiv.ofBijective ψ hψ).symm
  have hφ : ∀ t : twCent (thL m w) (dlt e b β), (t : GLw m w) = mulU e b ((φ t : B.T) : B.Aˣ) := by
    intro t
    have := congrArg Subtype.val ((MulEquiv.ofBijective ψ hψ).apply_symm_apply t)
    exact this.symm
  refine ⟨φ, fun t => by rw [hφ t, mulU_val], fun t => ?_⟩

  have hset : {t | t ∈ twCent (thL m w) (dlt e b β) ∧
      IsCompact (closure (Subgroup.zpowers t : Set (GLw m w)))} =
      (((GlobalTheory.UnitLemma.intUnits K.O B.A) ⊓ B.T).map (mulU e b) : Set (GLw m w)) := by
    ext g
    constructor
    · rintro ⟨hg, hc⟩
      obtain ⟨a, haT, rfl⟩ := hsurj g hg
      exact ⟨a, ⟨GlobalTheory.T.integralUnits_of_isCompact_closure_zpowers_mul E hE w hw K e hec hint hval B m b a hc, haT⟩, rfl⟩
    · rintro ⟨a, ⟨hai, haT⟩, rfl⟩
      exact ⟨hT a haT, GlobalTheory.T.isCompact_closure_zpowers_mul_integralUnit E hE w hw K e hec hint hval B m b a hai⟩
  rw [cptPart, hset, Subgroup.closure_eq, hφ t]
  constructor
  · rintro ⟨a, ⟨hai, -⟩, ha⟩
    rwa [← mulU_injective e b ha]
  · intro h
    exact ⟨_, ⟨h, (φ t).2⟩, rfl⟩

end GlobalTheory.TwLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspli
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwClassForms

theorem twConj_gram (L : Type) [Field L] (c : L →+* L) (a : ℕ) (δ q : GL (Fin a) L) :
    (((q⁻¹ * δ * thetaGL a c q).val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ =
      q.valᵀ * ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ * q.val.map c := by
  have hΦ : GlobalTheory.Tw.Phi a L * (GlobalTheory.Tw.Phi a L)ᵀ = 1 := Phi_mul_transpose a L
  have hΦ' : (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 := mul_eq_one_comm.1 hΦ
  have hinv : (GlobalTheory.Tw.Phi a L)⁻¹ = (GlobalTheory.Tw.Phi a L)ᵀ := Matrix.inv_eq_left_inv hΦ'
  have hθ : (thetaGL a c q).val =
      GlobalTheory.Tw.Phi a L * ((GeneralLinearGroup.map c q)⁻¹).valᵀ * (GlobalTheory.Tw.Phi a L)ᵀ := rfl
  have hC : ((GeneralLinearGroup.map c q)⁻¹).valᵀ * (q.val.map c)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, show q.val.map c = (GeneralLinearGroup.map c q).val from rfl,
      Units.mul_inv, Matrix.transpose_one]
  have k1 : ∀ X : Matrix (Fin a) (Fin a) L, (GlobalTheory.Tw.Phi a L)ᵀ * (GlobalTheory.Tw.Phi a L * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hΦ', Matrix.one_mul]
  have k2 : ∀ X : Matrix (Fin a) (Fin a) L, ((GeneralLinearGroup.map c q)⁻¹).valᵀ * ((q.val.map c)ᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  have k3 : ∀ X : Matrix (Fin a) (Fin a) L, GlobalTheory.Tw.Phi a L * ((GlobalTheory.Tw.Phi a L)ᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, hΦ, Matrix.one_mul]
  have k4 : ∀ X : Matrix (Fin a) (Fin a) L, δ.val * ((δ⁻¹).val * X) = X := by
    intro X; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hY : (q⁻¹ * δ * thetaGL a c q).val * GlobalTheory.Tw.Phi a L *
      ((q.val.map c)ᵀ * (GlobalTheory.Tw.Phi a L)ᵀ * (δ⁻¹).val * q.val) = 1 := by
    simp only [Units.val_mul, hθ, Matrix.mul_assoc, k1, k2, k3, k4]
    exact Units.inv_mul q
  rw [Matrix.inv_eq_right_inv hY, Matrix.mul_inv_rev, hinv, ← Matrix.coe_units_inv]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem gram_delta (L : Type) [Field L] (a : ℕ) :
    (∀ G : Matrix (Fin a) (Fin a) L, IsUnit G.det → ∃ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = G) ∧
    (∀ δ δ' : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = ((δ'.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ → δ = δ') := by
  have hΦ : GlobalTheory.Tw.Phi a L * (GlobalTheory.Tw.Phi a L)ᵀ = 1 := Phi_mul_transpose a L
  have hΦ' : (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 := mul_eq_one_comm.1 hΦ
  have hdΦ : IsUnit (GlobalTheory.Tw.Phi a L).det := Matrix.isUnit_det_of_right_inverse hΦ
  refine ⟨fun G hG => ?_, fun δ δ' h => ?_⟩
  · have hGT : IsUnit (Gᵀ)⁻¹.det := by
      rw [Matrix.det_nonsing_inv, Matrix.det_transpose]; exact hG.ringInverse
    have hd : IsUnit ((Gᵀ)⁻¹ * (GlobalTheory.Tw.Phi a L)ᵀ).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]; exact hGT.mul hdΦ
    refine ⟨Matrix.nonsingInvUnit _ hd, ?_⟩
    change (((Gᵀ)⁻¹ * (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = G
    rw [Matrix.mul_assoc, hΦ', Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hG),
      Matrix.transpose_transpose]
  · have hu : ∀ x : GL (Fin a) L, IsUnit (x.val * GlobalTheory.Tw.Phi a L).det := by
      intro x; rw [Matrix.det_mul]; exact (Matrix.isUnits_det_units x).mul hdΦ
    have h1 := congrArg Matrix.transpose h
    simp only [Matrix.transpose_transpose] at h1
    have h2 := congrArg Inv.inv h1
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu δ), Matrix.nonsing_inv_nonsing_inv _ (hu δ')] at h2
    have h3 := congrArg (· * (GlobalTheory.Tw.Phi a L)ᵀ) h2
    simp only [Matrix.mul_assoc, hΦ, Matrix.mul_one] at h3
    exact Units.ext h3

theorem herm_norm_basis (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (a : ℕ) (β t : B.Aˣ)
    (b : Module.Basis (Fin a) K.E B.A) : ∃ b' : Module.Basis (Fin a) K.E B.A,
      ∀ i j, B.herm ((β : B.A) * (t * B.σ t)) (b i) (b j) = B.herm β (b' i) (b' j) := by
  let f : B.A ≃ₗ[K.E] B.A := LinearEquiv.ofLinear (LinearMap.mulLeft K.E (t : B.A))
    (LinearMap.mulLeft K.E ((t⁻¹ : B.Aˣ) : B.A))
    (by ext y; simp [← mul_assoc]) (by ext y; simp [← mul_assoc])
  refine ⟨b.map f, fun i j => ?_⟩
  simp only [Module.Basis.map_apply, f, LinearEquiv.ofLinear_apply, LinearMap.mulLeft_apply,
    GlobalTheory.UnitLemma.InvAlg.herm, map_mul]
  congr 1
  ring

theorem twCl_equiv_cl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → ∀ (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P = Q.map e.symm.toRingHom → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (a - 1) * B.g) → ∃ F : B.Cl ≃ {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q}, ∀ k : B.Cl, ∃ b : Module.Basis (Fin a) K.E B.A, ∀ i j, (((F k).1.rep.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm ((β₀ : B.A) * k.rep) (b i) (b j)) := by
  intro E _ _ _ hE w hw K e he hO a Q hQm hQd hQs B hg hP β₀ hβ₀
  have hthL : thL a w = thetaGL a (cj w) := by rw [thL, if_neg hw]
  have hnrm : ∀ y, nrmL a w y = y * thetaGL a (cj w) y := by intro y; rw [nrmL, if_neg hw]
  have hcc : ∀ x, cj w (cj w x) = x := by
    intro x; obtain ⟨y, rfl⟩ := e.surjective x; rw [← he, ← he, K.c_c]
  have hPsep : B.P.Separable := by rw [hP]; exact hQs.map
  have hfr : Module.finrank K.E B.A = a := by
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E B.g)]
    change B.P.natDegree = a
    rw [hP, natDegree_map, hQd]
  let b0 : Module.Basis (Fin a) K.E B.A := Module.finBasisOfFinrankEq K.E B.A hfr
  have hε : ((-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1) := neg_one_pow_eq_or B.A (a - 1)
  have hβx : ∀ x : B.Aˣ, B.σ (x : B.A) = x →
      B.σ ((β₀ * x : B.Aˣ) : B.A) = (β₀ * x : B.Aˣ) * ((-1) ^ (a - 1) * B.g) := by
    intro x hx; simp only [Units.val_mul, map_mul, hβ₀, hx]; ring

  have htwE : ∀ δ δ' : GLw a w, Relation.EqvGen (fun x y : GLw a w => ∃ g, y = g⁻¹ * x * thL a w g) δ δ' →
      ∃ q, δ' = q⁻¹ * δ * thL a w q := by
    intro δ δ' h
    induction h with
    | rel x y hxy => exact hxy
    | refl x => exact ⟨1, by simp⟩
    | symm x y _ ih =>
      obtain ⟨q, rfl⟩ := ih
      exact ⟨q⁻¹, by simp [mul_assoc]⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨q, rfl⟩ := ih1
      obtain ⟨r, rfl⟩ := ih2
      exact ⟨q * r, by simp [mul_assoc]⟩
  have hσinv : ∀ u : B.Aˣ, B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A) = 1 := by
    intro u; rw [← map_mul, Units.inv_mul, map_one]
  have hclE : ∀ x y : {x : B.Aˣ // B.σ (x : B.A) = x}, Relation.EqvGen (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) x y → ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A)) := by
    intro x y h
    induction h with
    | rel x y hxy => exact hxy
    | refl x => exact ⟨1, by simp⟩
    | symm x y _ ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨u⁻¹, ?_⟩
      have h1 := hσinv u
      have h2 : ((u⁻¹ : B.Aˣ) : B.A) * u = 1 := Units.inv_mul u
      rw [hu]
      linear_combination (-(x.1 : B.A) * (B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A))) * h2 - (x.1 : B.A) * h1
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨u, hu⟩ := ih1
      obtain ⟨v, hv⟩ := ih2
      exact ⟨u * v, by rw [hv, hu, Units.val_mul, map_mul]; ring⟩

  obtain ⟨F0i, F0u⟩ := gram_delta (w.adicCompletion E) a
  have hF1 := GlobalTheory.T.hermitian_form_det_unit_and_twist K B (w.adicCompletion E) e (cj w) he hcc a Q hP hQs hQd
  have hF4 := GlobalTheory.T.gramMatrix_traceForm_basis_change K B (w.adicCompletion E) e (cj w) he a
  have hF6 := twConj_gram (w.adicCompletion E) (cj w) a
  have hcl : ∀ k : B.Cl, B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = (Quot.out k).1 := fun k => (Quot.out k).2
  have hG : ∀ k : B.Cl, IsUnit (Matrix.of fun i j => e (B.herm (((β₀ * (Quot.out k).1 : B.Aˣ)) : B.A) (b0 i) (b0 j))).det :=
    fun k => (hF1 _ (hβx _ (hcl k)) b0).1
  choose δk hδk using fun k => F0i _ (hG k)

  have hrep : ∀ k : B.Cl, ∀ δ : GLw a w, Relation.EqvGen (fun x y : GLw a w => ∃ g, y = g⁻¹ * x * thL a w g) (δk k) δ →
      ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ =
        Matrix.of fun i j => e (B.herm (((β₀ * (Quot.out k).1 : B.Aˣ)) : B.A) (b i) (b j)) := by
    intro k δ h
    obtain ⟨q, rfl⟩ := htwE _ _ h
    rw [hthL, hF6, hδk k]
    obtain ⟨b', hb'⟩ := (hF4 _ b0).1 q
    exact ⟨b', hb'.symm⟩
  let F : B.Cl → {c : TwCl (thL a w) // (nrmL a w c.rep).val.charpoly = Q} := fun k =>
    ⟨Quot.mk _ (δk k), by
      obtain ⟨b, hb⟩ := hrep k _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ (δk k)))).symm
      rw [hnrm]
      exact (hF1 _ (hβx _ (hcl k)) b).2 _ hb⟩
  have hinj : Function.Injective F := by
    intro k k' hkk
    have h1 : (Quot.mk _ (δk k) : TwCl (thL a w)) = Quot.mk _ (δk k') := congrArg Subtype.val hkk
    obtain ⟨b', hb'⟩ := hrep k _ (Quot.eqvGen_exact h1)
    rw [hδk k'] at hb'
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_norm_of_equal_gram_traceForms K B hPsep _ hε a _ _ (hβx _ (hcl k')) (hβx _ (hcl k)) b0 b' (fun i j => by
      have := congrFun (congrFun hb' i) j
      simpa using e.injective this)
    have hrel : (Quot.mk _ (Quot.out k') : B.Cl) = Quot.mk _ (Quot.out k) := by
      apply Quot.sound
      refine ⟨t, ?_⟩
      have h2 : ((β₀⁻¹ : B.Aˣ) : B.A) * β₀ = 1 := Units.inv_mul β₀
      simp only [Units.val_mul] at ht
      linear_combination ((β₀⁻¹ : B.Aˣ) : B.A) * ht - (((Quot.out k).1 : B.A) - ((Quot.out k').1 : B.A) * ((t : B.A) * B.σ (t : B.A))) * h2
    exact (Quot.out_eq k).symm.trans (hrel.symm.trans (Quot.out_eq k'))

  have hsurj : Function.Surjective F := by
    rintro ⟨cl, hclQ⟩
    have hQδ : ((Quot.out cl) * thetaGL a (cj w) (Quot.out cl)).val.charpoly = Q := by
      rw [← hnrm]; exact hclQ
    obtain ⟨β, hβ, b, hb⟩ := GlobalTheory.T.exists_traceForm_of_twistedNorm_charpoly K B (w.adicCompletion E) e (cj w) he hcc hg a Q hP hQs hQd _ hQδ
    have hx : B.σ (((β₀⁻¹ * β : B.Aˣ)) : B.A) = ((β₀⁻¹ * β : B.Aˣ) : B.A) := by
      have h1 : B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * ((β₀ : B.A) * ((-1) ^ (a - 1) * B.g)) = 1 := by
        rw [← hβ₀, ← map_mul, Units.inv_mul, map_one]
      have h2 : ((β₀⁻¹ : B.Aˣ) : B.A) * β₀ = 1 := Units.inv_mul β₀
      simp only [Units.val_mul, map_mul, hβ]
      linear_combination (((β₀⁻¹ : B.Aˣ) : B.A) * β) * h1 - (B.σ ((β₀⁻¹ : B.Aˣ) : B.A) * β * ((-1) ^ (a - 1) * B.g)) * h2
    let k : B.Cl := Quot.mk _ ⟨β₀⁻¹ * β, hx⟩
    refine ⟨k, ?_⟩
    obtain ⟨u, hu⟩ := hclE _ _ (Quot.eqvGen_exact (Quot.out_eq k)).symm
    have hβu : ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) = (β : B.A) * ((u : B.A) * B.σ (u : B.A)) := by
      rw [Units.val_mul, hu, Units.val_mul]
      have h2 : (β₀ : B.A) * ((β₀⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv β₀
      linear_combination ((β : B.A) * ((u : B.A) * B.σ (u : B.A))) * h2
    obtain ⟨b'', hb''⟩ := herm_norm_basis K B a β u b0
    obtain ⟨P, hPb⟩ := (hF4 (β : B.A) b).2 b''
    have hmat : ((δk k).val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹ᵀ =
        (((P⁻¹ * Quot.out cl * thetaGL a (cj w) P)).val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹ᵀ := by
      rw [hF6, hb, ← hPb, hδk k]
      ext i j
      simp only [Matrix.of_apply, hβu, hb'']
    have hδeq := F0u _ _ hmat
    apply Subtype.ext
    change (Quot.mk _ (δk k) : TwCl (thL a w)) = cl
    rw [hδeq]
    have hθP : thL a w P = thetaGL a (cj w) P := by rw [hthL]
    exact (Quot.sound (⟨P, by rw [hθP]⟩ : ∃ g, P⁻¹ * Quot.out cl * thetaGL a (cj w) P = g⁻¹ * Quot.out cl * thL a w g)).symm.trans (Quot.out_eq cl)
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun k => ?_⟩
  obtain ⟨b, hb⟩ := hrep k _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ (δk k) : TwCl (thL a w)))).symm
  refine ⟨b, fun i j => ?_⟩
  have := congrFun (congrFun hb i) j
  rw [Matrix.of_apply, Units.val_mul] at this
  exact this

end GlobalTheory.TwClassForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCuspidalSatakeParameterStarEqInv
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.UnitaryParam

theorem map_star_eq_map_inv_of_form : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  intro E _ _ _ a π H hH hpos hinv w B hB
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
  refine GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w a π.V (π.locRep w) x B ?_ hx
  refine ⟨H.flip, fun v u => ?_, fun v hv => ?_, fun g v u => ?_⟩
  · simp only [LinearMap.flip_apply]
    exact (hH u v).symm
  · simpa only [LinearMap.flip_apply] using hpos v hv
  · simp only [LinearMap.flip_apply]
    exact hinv _ u v

end GlobalTheory.CuspRep.UnitaryParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieOneParameterIsRealOneParamSubgroupAdel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
open Matrix GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UAut

theorem isRealLine_oneP (D : D7) (θ : InfF D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) :
    GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  obtain ⟨-, h2⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hZ : Xᴴ * V.gram.map (embOverOf D τ).1 + V.gram.map (embOverOf D τ).1 * X = 0 := hX
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.SiegelSet.exists_isRealLine (isCMExt_host D) (h2 V) (embOverOf D τ) hZ
  refine ⟨placeOf D τ, embOverOf D τ, X, hZ, fun t => ⟨_, ?_, hγ t⟩⟩
  rw [oneP, ← hγ t, GlobalTheory.Orb.archMat_eq_archEquiv _ (isCMExt_host D), atTau_archEquiv hθ V _ rfl]

end GlobalTheory.UAut
end

