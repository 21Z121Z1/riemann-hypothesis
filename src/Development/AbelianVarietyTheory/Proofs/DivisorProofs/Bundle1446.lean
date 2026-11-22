import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetRationalSectionsEqPowProductLinearForms
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort

theorem det_symbolBlock {E ι κ : Type} [Field E] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (w : κ → E) (e : ℕ) (r : κ → κ → E) :
    (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then w i.2 ^ e * r i'.2 i.2 else 0).det =
      (∏ p, w p) ^ (e * Fintype.card ι) *
        (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then r i'.2 i.2 else 0).det := by
  have h : (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then w i.2 ^ e * r i'.2 i.2 else 0) =
      Matrix.diagonal (fun i : ι × κ => w i.2 ^ e) *
        Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then r i'.2 i.2 else 0 := by
    ext i i'
    simp only [Matrix.of_apply, Matrix.diagonal_mul]
    split_ifs <;> simp
  rw [h, Matrix.det_mul, Matrix.det_diagonal, Fintype.prod_prod_type]
  simp only [Finset.prod_pow, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm (Fintype.card ι)]

theorem det_rational_eq_pow : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → S.deepRank s ≤ (Finset.univ.filter fun k => (col k).j = S.D).card → ∃ γ : E, ∀ l : Fin S.N → E, aeval (join (fun i k => algebraMap F E (s i k)) l) (S.det c col) = γ * (∏ p, ∑ k, l k * Φ.y p k) ^ S.expo := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc col m ix hsh hrank
  classical
  obtain ⟨c', -, hev⟩ := GlobalTheory.T.hermitianMultiplicationFlat_columns_eval F A S hS E A' (fun i k => algebraMap F E (s i k)) δ Φ d b c hc
  have hsym := GlobalTheory.T.symbols_of_evaluated_columns_hermitianMultSystem F A S hS E A' (fun i k => algebraMap F E (s i k)) δ Φ d col m ix hsh
  obtain ⟨hfd, hfr, -⟩ := GlobalTheory.T.finrank_deepestFiltrationStep_eq_rational F A S hS E A' s δ Φ
  obtain ⟨hcard, -, -⟩ := GlobalTheory.T.monomial_counts_degree_and_weighted_sum S.D S.T hS.one_le hS.le_T
  let v : (Fin S.N → E) → Fin d → A' := fun l k =>
    word Φ.mul (fun q j => join (fun i k => algebraMap F E (s i k)) l ((col k).β q, j)) (Φ.ι (col k).x)
  let ω : A' [⋀^Fin d]→ₗ[E] E := (Matrix.detRowAlternating).compLinearMap (LinearMap.pi c')
  have hdet : ∀ l, aeval (join (fun i k => algebraMap F E (s i k)) l) (S.det c col) = ω (v l) := by
    intro l
    rw [Sys.det, AlgHom.map_det, AlternatingMap.compLinearMap_apply]
    change _ = Matrix.det (fun k i => c' i (v l k))
    rw [← Matrix.det_transpose]
    congr 1
    ext i k
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply]
    exact (hev (col i) (join (fun i k => algebraMap F E (s i k)) l)).2 k

  let ix' : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a × Fin δ) ↪ Fin d :=
    (Equiv.sigmaProdDistrib (fun a : Fin (S.T - S.D) => MonoDeg (Fin S.D) a) (Fin δ)).symm.toEmbedding.trans ix
  have hix' : ∀ q, ix' q = ix (⟨q.1, q.2.1⟩, q.2.2) := fun q => rfl

  have hind : ∀ l k, k ∉ Set.range ix → v l k = v 0 k := by
    intro l k hk
    have hL : (fun q j => join (fun i k => algebraMap F E (s i k)) l ((col k).β q, j)) = (fun q j => join (fun i k => algebraMap F E (s i k)) 0 ((col k).β q, j)) := by
      rcases hsh.rest k hk with ⟨-, hβ⟩ | hj
      · funext q j
        obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr (hβ q)
        rw [← hi]
        simp [join]
      · have ht : (col k).t = 0 := by have := (col k).add; omega
        funext q
        exact absurd q.isLt (by omega)
    show word Φ.mul _ _ = word Φ.mul _ _
    rw [hL]

  have hzq : ∀ q : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a × Fin δ),
      ∃ x : A', ∃ hx : x ∈ Φ.U q.1, Φ.sym q.1 ⟨x, hx⟩ = Pi.single q.2 1 := by
    rintro ⟨a, α, p⟩
    obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp (Φ.y_ne p)
    have hk₀' : Φ.y p k₀ ≠ 0 := hk₀
    have ht : Φ.y p k₀ ^ (S.T - (a : ℕ)) ≠ 0 := pow_ne_zero _ hk₀'
    have hmem : (Pi.single p (Φ.y p k₀ ^ (S.T - (a : ℕ)))⁻¹ : Fin δ → E) ∈
        (Submodule.span E (Φ.ι '' S.V 0)).map Φ.res := by
      rw [Φ.onto]; exact Submodule.mem_top
    obtain ⟨m₀, hm₀, hres⟩ := hmem
    obtain ⟨h, hh⟩ := Φ.mono a a.2 α (fun _ => Pi.single k₀ 1) m₀ hm₀
    refine ⟨_, h, ?_⟩
    funext i
    obtain ⟨α', p'⟩ := i
    rw [hh, hres]
    by_cases hp : p' = p
    · rw [hp]
      by_cases hα : α' = α
      · rw [hα]
        simp [Finset.prod_const, Pi.single_apply, ht]
      · have hα' : α'.1 ≠ α.1 := fun e => hα (Subtype.ext e)
        simp [hα', hα]
    · simp [hp, Pi.single_apply]
  choose zq hzqU hzqS using hzq
  let z : Fin d → A' := Function.extend ix' zq (v 0)
  have hz_ix : ∀ q, z (ix' q) = zq q := fun q => ix'.injective.extend_apply zq (v 0) q
  have hz : ∀ q, z (ix' q) ∈ Φ.U q.1 := fun q => (hz_ix q).symm ▸ hzqU q
  have hzs : ∀ q, Φ.sym q.1 ⟨z (ix' q), hz q⟩ = Pi.single q.2 1 := by
    intro q
    have e : (⟨z (ix' q), hz q⟩ : Φ.U q.1) = ⟨zq q, hzqU q⟩ := Subtype.ext (hz_ix q)
    rw [e]; exact hzqS q
  have hzout : ∀ l k, k ∉ Set.range ix' → z k = v l k := by
    intro l k hk
    show Function.extend ix' zq (v 0) k = _
    rw [Function.extend_apply' _ _ _ hk]
    have hk' : k ∉ Set.range ix := by
      rintro ⟨q, rfl⟩; exact hk ⟨(Equiv.sigmaProdDistrib _ _) q, rfl⟩
    exact (hind l k hk').symm

  let J : Finset (Fin d) := Finset.univ.filter fun k => (col k).j = S.D
  have hnotix : ∀ k, (col k).j = S.D → k ∉ Set.range ix := by
    rintro k hk ⟨q, rfl⟩
    have := hsh.x_j q
    have := hS.one_le
    omega
  have hv : ∀ l q, v l (ix' q) ∈ Φ.U q.1 := fun l q => ((hsym l).1 q.1 q.2.1 q.2.2).fst
  have hJ : ∀ l, ∀ k ∈ J, k ∉ Set.range ix' ∧ v l k ∈ Φ.U (S.T - S.D) := by
    intro l k hk
    have hk' : (col k).j = S.D := (Finset.mem_filter.mp hk).2
    refine ⟨?_, (hsym l).2 k (hnotix k hk') hk'⟩
    rintro ⟨q, hq⟩
    exact hnotix k hk' ⟨_, (hix' q).symm.trans hq⟩
  haveI := hfd
  have hrank' : Module.finrank E (Φ.U (S.T - S.D)) ≤ J.card := hfr ▸ hrank
  let B : ∀ a : Fin (S.T - S.D), Matrix (MonoDeg (Fin S.D) a × Fin δ) (MonoDeg (Fin S.D) a × Fin δ) E :=
    fun a => Matrix.of fun i i' => if i.1 = i'.1 then Φ.res (Φ.ι (m i'.2)) i.2 else 0
  have hexp : ∑ a : Fin (S.T - S.D), (S.T - (a : ℕ)) * Fintype.card (MonoDeg (Fin S.D) a) = S.expo := by
    rw [Sys.expo, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Nat.card_eq_fintype_card, hcard, mul_comm]
  refine ⟨(∏ a, (B a).det) * ω z, fun l => ?_⟩
  rw [hdet]
  have key := GlobalTheory.T.alternatingMap_det_filtration_with_symbols E A' (S.T - S.D) d (fun a => MonoDeg (Fin S.D) a × Fin δ) Φ.U (fun a => Φ.sym a)
    Φ.le (fun a x => Φ.ker a a.2 x) ix' J (v l) (hv l) (hJ l) hrank' z hz hzs (hzout l) ω
  rw [key]
  have hblock : ∀ a : Fin (S.T - S.D),
      (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v l (ix' ⟨a, i'⟩), hv l ⟨a, i'⟩⟩ i).det =
        (∏ p, ∑ k, l k * Φ.y p k) ^ ((S.T - (a : ℕ)) * Fintype.card (MonoDeg (Fin S.D) a)) * (B a).det := by
    intro a
    have hM : (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v l (ix' ⟨a, i'⟩), hv l ⟨a, i'⟩⟩ i) =
        Matrix.of fun (i i' : MonoDeg (Fin S.D) a × Fin δ) =>
          if i.1 = i'.1 then (∑ k, l k * Φ.y i.2 k) ^ (S.T - (a : ℕ)) * Φ.res (Φ.ι (m i'.2)) i.2 else 0 := by
      ext i i'
      refine (((hsym l).1 a i'.1 i'.2).snd i.1 i.2).trans ?_
      simp only [Matrix.of_apply, Subtype.val_inj]
    rw [hM, det_symbolBlock (ι := MonoDeg (Fin S.D) a) (fun p => ∑ k, l k * Φ.y p k) (S.T - (a : ℕ))
      (fun p' p => Φ.res (Φ.ι (m p')) p)]
  simp only [hblock]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hexp]
  ring

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ModuNorm

open scoped Pointwise

def mulUnitCE {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a : Rˣ) : R ≃ₜ+ R where
  toFun x := (a : R) * x
  invFun x := ((a⁻¹ : Rˣ) : R) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  map_add' x y := mul_add _ x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem distribHaarChar_eq_addEquivAddHaarChar {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R] (a : Rˣ) :
    distribHaarChar R a = addEquivAddHaarChar (mulUnitCE a) := by
  let μ : Measure R := Measure.addHaar
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : R)
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hKn).ne'
  have hT : μ K ≠ ⊤ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) h0 hT ?_
  have e := addEquivAddHaarChar_smul_preimage μ (X := a • K) (mulUnitCE a)
  have hpre : (mulUnitCE a : R → R) ⁻¹' (a • K) = K := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := (Units.mul_right_inj a).1 hxy
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hpre] at e
  rw [← e]
  rfl

def evalUnitCE (R : Type) [AddCommGroup R] [TopologicalSpace R] : (Unit → R) ≃ₜ+ R where
  toFun f := f ()
  invFun x := fun _ => x
  left_inv f := rfl
  right_inv x := rfl
  map_add' f g := rfl
  continuous_toFun := continuous_apply ()
  continuous_invFun := continuous_pi fun _ => continuous_id

theorem modu_norm_eq_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], NumberField.IsTotallyReal F →
    ∀ t : (AE F E)ˣ, (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) : ℝ≥0) : ℝ) = (absE F E t : ℝ) := by
  intro F E _ _ _ _ _ hF t
  haveI := hF
  letI : MeasurableSpace (AF F) := borel _
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  set a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) t with ha
  let M : Matrix Unit Unit (AF F) := fun _ _ => (a : AF F)
  have hdet : M.det = (a : AF F) := Matrix.det_unique M
  have hM : IsUnit M.det := hdet ▸ a.isUnit
  have hχ := GlobalTheory.ModuLR.chi_AF F M hM
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (evalUnitCE (AF F)) (GlobalTheory.ModuLR.mulVecCE M hM)
  have hext : ((evalUnitCE (AF F)).symm.trans (GlobalTheory.ModuLR.mulVecCE M hM)).trans (evalUnitCE (AF F)) = mulUnitCE a := by
    ext x
    show (M *ᵥ fun _ => x) () = (a : AF F) * x
    simp [Matrix.mulVec, dotProduct, M]
  rw [hext] at htr
  show ((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) = _
  rw [show distribHaarChar (AdeleRing (𝓞 F) F) a = distribHaarChar (AF F) a from rfl,
    distribHaarChar_eq_addEquivAddHaarChar, htr, hχ, hdet]
  exact GlobalTheory.absE_eq_prod_norm_fstA_sndA F E t

end GlobalTheory.ModuNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledFockVacuumEqSmulVacuumMulConj
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section
namespace GlobalTheory.RealLift.VacBox

def eL {R S : ℕ} : Ix R S → Ix (R + S) (S + R) :=
  Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))

def eR {R S : ℕ} : Ix R S → Ix (R + S) (S + R) :=
  Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))

theorem dbl_cols {α β : Type} [Fintype β] {P Q R S : ℕ} (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (c : Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ) :
    (A * c * (dblM C)ᵀ).toCols₁ = A * c.submatrix id eL * Cᵀ ∧
    (A * c * (dblM C)ᵀ).toCols₂ = A * c.submatrix id eR * Cᵀ ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id eL = Jm P Q * c.submatrix id eL * Jm R S ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id eR = -(Jm P Q * c.submatrix id eR * Jm R S) :=
  GlobalTheory.T.doubledSpaceFrame_colBlocks_eq α β P Q R S A C c

theorem heisOp_rot_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) :
    heisOp (((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) 1 = ((t : ℂ) * Complex.I) • heisOp c 1 :=
  GlobalTheory.T.fockHeisenbergOperatorOfCoords_real_I_smul_signConj_one P Q R S c t

theorem box_deriv {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (a₁ b₁ a₂ b₂ : κ → AF F)
    (f g₁ g₂ : SInf F κ) (f₀ h : SInf F (κ ⊕ κ))
    (hg₁ : ∀ y, g₁ y = fderiv ℝ f y (fun i => evI F (a₁ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₁ i)) : ℝ) * f y)
    (hg₂ : ∀ y, g₂ y = fderiv ℝ f y (fun i => evI F (a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₂ i)) : ℝ) * f y)
    (hh : ∀ x, h x = fderiv ℝ f₀ x (fun i => evI F (Sum.elim a₁ a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ) * f₀ x)
    (hf₀ : ∀ x, f₀ x = f (x ∘ Sum.inl) * star (f (x ∘ Sum.inr))) (x : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    h x = g₁ (x ∘ Sum.inl) * star (f (x ∘ Sum.inr)) + f (x ∘ Sum.inl) * star (g₂ (x ∘ Sum.inr)) :=
  GlobalTheory.T.heisenberg_derivative_on_schwartz_tensor_conj F κ a₁ b₁ a₂ b₂ f g₁ g₂ f₀ h hg₁ hg₂ hh hf₀ x

def conjS {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => starRingEnd ℂ (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := by
      funext y; simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem sumPl_smul_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (L L' : ι → Module.End ℂ V) (v : V) (z : ℂ) (h : ∀ w, L' w v = z • L w v) :
    sumPl (V := fun _ : ι => V) L' (PiTensorProduct.tprod ℂ fun _ => v) =
      z • sumPl (V := fun _ : ι => V) L (PiTensorProduct.tprod ℂ fun _ => v) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, atPl, PiTensorProduct.map_tprod]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : ∀ M : Module.End ℂ V, (fun i => Function.update (fun i => (LinearMap.id : V →ₗ[ℂ] V)) w M i v) =
      Function.update (fun _ => v) w (M v) := by
    intro M; funext i
    by_cases hi : i = w
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [e, e, h w]
  exact MultilinearMap.map_update_smul _ _ _ _ _

theorem sub_smul' {m n k : Type} (z : ℂ) (M : Matrix m n ℂ) (e : k → n) :
    (z • M).submatrix id e = z • M.submatrix id e := rfl

theorem toCols_at {F E α β₁ β₂ : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {u : Matrix α (β₁ ⊕ β₂) (AE F E)} (hu : At (evI F) u) : At (evI F) u.toCols₁ ∧ At (evI F) u.toCols₂ :=
  ⟨fun r hr => by ext i j; exact congrFun (congrFun (hu r hr) i) (Sum.inl j),
   fun r hr => by ext i j; exact congrFun (congrFun (hu r hr) i) (Sum.inr j)⟩

theorem vac_box : DerEx → VacLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ))
    (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ)),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsDblCoord (cA σ) (-1) JA JB d dd →
    IsFockMap ψ τ dd A (fun w => dblM (C w)) Φd →
    ∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr)) := by
  intro hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd
  obtain ⟨D, hD1⟩ := hD F E σ α β κ ψ JA JB d hψ
  obtain ⟨Dd, hDd⟩ := hD F E σ α (β ⊕ β) (κ ⊕ κ) ψ JA (dbl JB) dd hψ
  set f₁ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hf₁
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box f₁ (conjS f₁)
  have hf₀' : ∀ x, f₀ x = f₁ (x ∘ Sum.inl) * star (f₁ (x ∘ Sum.inr)) := fun x => hf₀ x
  have hFrd := GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr
  have hder : ∀ u₁ : Matrix α β (AE F E), At (evI F) u₁ → ∀ c₁ : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u₁.map (piInf (τ w)) = A w * c₁ w * (C w)ᵀ) →
      D u₁ f₁ = Φ (sumPl (fun w => heisOp (c₁ w)) (PiTensorProduct.tprod ℂ fun _ => 1)) := fun u₁ hu₁ c₁ hc₁ =>
    GlobalTheory.SDUnique.sd_unique ((hD1 u₁ hu₁ f₁).1) (hΦ.2 u₁ hu₁ c₁ hc₁ _)
  have hbox : ∀ u : Matrix α (β ⊕ β) (AE F E), At (evI F) u → ∀ x, Dd u f₀ x =
      D u.toCols₁ f₁ (x ∘ Sum.inl) * star (f₁ (x ∘ Sum.inr)) +
        f₁ (x ∘ Sum.inl) * star (D u.toCols₂ f₁ (x ∘ Sum.inr)) := by
    intro u hu x
    obtain ⟨hu₁, hu₂⟩ := toCols_at hu
    have e := hdd u.toCols₁ u.toCols₂
    rw [Matrix.fromCols_toCols] at e
    refine box_deriv (d.e u.toCols₁).1 (d.e u.toCols₁).2 (d.e u.toCols₂).1 (d.e u.toCols₂).2 f₁ _ _ f₀ _
      ((hD1 _ hu₁ f₁).2) ((hD1 _ hu₂ f₁).2) (fun y => ?_) hf₀' x
    rw [(hDd u hu f₀).2 y, e]
  have key : ∀ u u' : Matrix α (β ⊕ β) (AE F E), At (evI F) u → At (evI F) u' →
      ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (dblM (C w))ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * (((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) •
        (Jm P Q * c w * Jm (R + S) (S + R))) * (dblM (C w))ᵀ) →
      ∀ f f' : SInf F (κ ⊕ κ), SD (fun t => dd.rho ψ (realAd F t • u)) f₀ f →
        SD (fun t => dd.rho ψ (realAd F t • u')) f₀ f' → f' = Complex.I • f := by
    intro u u' hu hu' c hc hc' f f' hf hf'
    rw [← GlobalTheory.SDUnique.sd_unique ((hDd u hu f₀).1) hf, ← GlobalTheory.SDUnique.sd_unique ((hDd u' hu' f₀).1) hf']
    obtain ⟨hu₁, hu₂⟩ := toCols_at hu
    obtain ⟨hu₁', hu₂'⟩ := toCols_at hu'
    have hI : ∀ w, ((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) = ((1 : ℝ) : ℂ) * Complex.I := fun w => by simp
    have h1 := hder _ hu₁ (fun w => (c w).submatrix id eL) (fun w => by
      rw [← (dbl_cols (A w) (C w) (c w)).1, ← hc w]; rfl)
    have h2 := hder _ hu₂ (fun w => (c w).submatrix id eR) (fun w => by
      rw [← (dbl_cols (A w) (C w) (c w)).2.1, ← hc w]; rfl)
    have h1' := hder _ hu₁' (fun w => (((1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eL * Jm R S))
      (fun w => by
        rw [← (dbl_cols (A w) (C w) (c w)).2.2.1, ← sub_smul', ← hI w,
          ← (dbl_cols (A w) (C w) _).1, ← hc' w]; rfl)
    have h2' := hder _ hu₂' (fun w => (((-1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eR * Jm R S))
      (fun w => by
        have e : (((-1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eR * Jm R S) =
            ((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) • (-(Jm P Q * (c w).submatrix id eR * Jm R S)) := by
          rw [hI w, smul_neg, ← neg_smul]; congr 1; push_cast; ring
        rw [e, ← (dbl_cols (A w) (C w) (c w)).2.2.2, ← sub_smul', ← (dbl_cols (A w) (C w) _).2.1, ← hc' w]; rfl)
    rw [sumPl_smul_tprod _ _ _ _ (fun w => heisOp_rot_one _ 1)] at h1'
    rw [sumPl_smul_tprod _ _ _ _ (fun w => heisOp_rot_one _ (-1))] at h2'
    rw [map_smul] at h1' h2'
    ext x
    rw [SchwartzMap.smul_apply, hbox u' hu' x, hbox u hu x, h1', h2', h1, h2]
    simp only [SchwartzMap.smul_apply, smul_eq_mul, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast
    ring
  obtain ⟨z', hz'⟩ := hV F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) Φd hCM hψ hFrd hΦd f₀ 1 key
  have hne1 : f₁ ≠ 0 := fun h0 => GlobalTheory.T.tprod_constant_polynomials_ne_zero F P Q R S (hΦ.1 (h0.trans (map_zero Φ).symm))
  obtain ⟨y, hy⟩ : ∃ y, f₁ y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne1 (SchwartzMap.ext h)
  have hz0 : z' ≠ 0 := by
    rintro rfl
    have h := congrArg (fun g : SInf F (κ ⊕ κ) => g (Sum.elim y y)) hz'
    simp only [zero_smul, SchwartzMap.zero_apply, hf₀', Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    exact mul_ne_zero hy (star_ne_zero.2 hy) h
  refine ⟨z'⁻¹, inv_ne_zero hz0, fun x => ?_⟩
  have h := congrArg (fun g : SInf F (κ ⊕ κ) => g x) hz'
  simp only [SchwartzMap.smul_apply, smul_eq_mul, hf₀'] at h
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]

end GlobalTheory.RealLift.VacBox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegralStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F),
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ W v, ∀ t : GL (Fin d) (AE F E),
      GlobalTheory.InertDbl.matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (AE F E)) →
      At (evFin F v) ((t : Matrix (Fin d) (Fin d) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
        ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.InertDbl.parD_diag_action | exact GlobalTheory.InertDbl.parD_diag_action | (intros; apply GlobalTheory.InertDbl.parD_diag_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerBigCellFactorizatiStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
    IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d).det →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v,
      ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d)⁻¹ *ᵥ z ∈
        GlobalTheory.InertSph.latAt W v) →
    ∃ p q : GlobalTheory.DblVac.UD σ W, p ∈ GlobalTheory.DblVac.KD σ W v ∧ p ∈ GlobalTheory.DblVac.PDiag σ W ∧
      q ∈ GlobalTheory.DblVac.KD σ W v ∧ q ∈ GlobalTheory.DblVac.PAnti σ W ∧ g = p * q := by
  first | exact @GlobalTheory.DblVacFactor.factor | exact GlobalTheory.DblVacFactor.factor | (intros; apply GlobalTheory.DblVacFactor.factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmall

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def coneI (B : Base F E) {a b : ℕ} (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)) (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b))
    (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ) (ν : Chr F E) (om' : Rep σ G.V' G.W)
    (om₁' : Rep σ G₁.V' G₁.W) (Φ' : Fn F (b + 2) (a + (b + 2))) (z : ℂ) (h : UA σ G.W.J) : ℂ :=
  ∫ k, ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1 * (ν l : ℂ) *
    ((absE F E l : ℝ) : ℂ) ^ z ∂μ ∂μK

def IsIwaHt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J)) (x : Fin n → E) (hf : UA σ J → ℝ) : Prop :=
  ∀ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K → mat p *ᵥ incV F x = l.1 • incV F x → hf (p * k) = absE F E l

def IsEisSer {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J)) (x : Fin n → E) (Eis : ℂ → UA σ J → ℂ) :
    Prop :=
  ∃ hf : UA σ J → ℝ, IsIwaHt K x hf ∧
    (∀ g, ∃ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F x = l.1 • incV F x ∧ g = p * k) ∧
    ∀ T : Set (UA σ J), T ⊆ ratU σ J → (∀ γ ∈ ratU σ J, ∃! t, t ∈ T ∧ ∃ l : (AE F E)ˣ,
        mat (γ * t⁻¹) *ᵥ incV F x = l.1 • incV F x) →
      ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
        HasSum (fun t : T => (hf (t.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) (Eis s g)

def EisAtMinusRho : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K → ∃ Eis : ℂ → UA σ G.V'.J → ℂ, IsEisSer K H.x Eis ∧
      (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → UA σ G.V'.J → ℂ) (C : ℝ) (N : ℕ), U ∈ 𝓝 s₀ ∧
        (∀ s ∈ U, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g) ∧ (∀ g, DifferentiableOn ℂ (Hol · g) U) ∧
        ∀ s ∈ U, ∀ g, ‖Hol s g‖ ≤ C * (ht g : ℝ) ^ N) ∧
      ∃ U ∈ 𝓝 (-((((b + 2 : ℕ) : ℂ) - 1) / 2)), ∃ (C : ℝ) (N : ℕ), ∀ g, DifferentiableOn ℂ (Eis · g) U ∧
        (∀ s ∈ U, ‖Eis s g‖ ≤ C * (ht g : ℝ) ^ N) ∧ Eis (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) g = 1

end GlobalTheory.ConeSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInertStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_unitary_conj_of_same_elliptic_charpoly_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w → γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  first | exact @GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert | exact GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert | (intros; apply GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert <;> assumption)
end

