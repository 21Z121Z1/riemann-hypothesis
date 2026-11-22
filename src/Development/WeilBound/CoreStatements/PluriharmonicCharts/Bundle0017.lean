import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsBlockMapInitialVertex
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0036
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0016

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsPositivePeriodLine
section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

local instance (priority := 2000) intAlg4 {Φ : Type} [Field Φ] : Algebra ℤ (RatFunc Φ) := Ring.toIntAlgebra _

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem exists_lift_gen {A F E : Type} [CommRing A] [Field F] [Field E] (a : A →+* F) (b : A →+* E)
    (hk : RingHom.ker a = RingHom.ker b) (gen : ∀ c, ∃ f g, c = a f / a g) : ∃ ψ : F →+* E, ∀ f, ψ (a f) = b f := by
  letI : Algebra (A ⧸ RingHom.ker a) F := (RingHom.kerLift a).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker a) F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective a)
  haveI : IsFractionRing (A ⧸ RingHom.ker a) F := IsFractionRing.of_field _ _ fun c => by
    obtain ⟨f, g, e⟩ := gen c
    exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, e⟩
  let b' : A ⧸ RingHom.ker a →+* E := Ideal.Quotient.lift _ b fun f hf => by rwa [hk] at hf
  have hb' : Function.Injective b' := RingHom.lift_injective_of_ker_le_ideal _ _ hk.ge
  exact ⟨IsFractionRing.lift hb', fun f => IsFractionRing.lift_algebraMap hb' (Ideal.Quotient.mk _ f)⟩

def fibEquiv (ι : K → Type) (k₀ : K) :
    (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) ≃ ι k₀ where
  toFun
    | ⟨⟨some k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨none, _⟩, m⟩ => m
  invFun m := ⟨⟨none, by rintro ⟨k, hk⟩; cases hk⟩, m⟩
  left_inv := by
    rintro ⟨⟨_ | k, h⟩, m⟩
    · rfl
    · exact absurd ⟨k, rfl⟩ h
  right_inv _ := rfl

theorem fibreBlock_subsingleton (k k' : FibreBlock (some : K → Option K)) : k = k' := by
  rcases k with ⟨_ | k, hk⟩
  · rcases k' with ⟨_ | k', hk'⟩
    · rfl
    · exact absurd ⟨k', rfl⟩ hk'
  · exact absurd ⟨k, rfl⟩ hk

theorem isMultiHomog_lin {F : Type} [Field F] (k₀ : K)
    (μ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → F) :
    IsMultiHomog (∑ q, C (μ q) * X q : MRingOver F (fibreIdx (iW ι k₀) some)) fun _ => 1 := by
  intro s hs k
  obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hs)
  rw [C_mul_X_eq_monomial] at hq
  have hs' := support_monomial_subset hq
  rw [Finset.mem_singleton] at hs'
  subst hs'
  obtain ⟨qk, qi⟩ := q
  obtain rfl : qk = k := fibreBlock_subsingleton _ _
  simp [Finsupp.single_apply]

variable {y : (Σ k, ι k) → Φ} {k₀ : K} {B : ι k₀ → Φ}

theorem cone_homog {E : Type} [Field E] (i₀ : MvPolynomial K Φ →+* E) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) : i₀ (mConeMap y g) = (∏ k, i₀ (X k) ^ d k) * i₀ (C (aeval y g)) := by
  have e : i₀.comp (mConeMap y).toRingHom =
      (aeval (fun p : Σ k, ι k => i₀ (X p.1) * ((i₀.comp C) ∘ y) p) : MRing ι →ₐ[ℤ] E).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) fun p => by simp [mConeMap, mul_comm]
  have := RingHom.congr_fun e g
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this, aeval_scale' (fun k => i₀ (X k)) _ hg, CPts.aeval_comp_ringHom]
  rfl

theorem exists_positive_period_line {E : Type} [Field E] (i₀ : MvPolynomial K Φ →+* E) (hi : Function.Injective i₀)
    {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e y c)
    (G : GenFibre (v₀ k₀) (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X))) :
    ∃ T : Set (MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K))),
      (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T := by
  let a : MRing ι →+* G.Φ := (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom
  have hka : RingHom.ker a = mCoordIdeal y := G.ker_x.trans (image_pen _ _ _ _ _)
  obtain ⟨ψ, hψ⟩ := exists_lift_gen a (i₀.comp (mConeMap y).toRingHom)
    (by rw [hka, RingHom.ker_comp_of_injective _ hi]; rfl)
    (fun c => by obtain ⟨f, g, -, e⟩ := G.gen c; exact ⟨f, g, e⟩)
  have lift : ∀ s v, HasVal y y s v → ∃ s', ψ s' = i₀ (C s) := by
    rintro s v ⟨d, g, h, hg, hh, h0, e, -⟩
    refine ⟨a g / a h, ?_⟩
    rw [map_div₀, hψ, hψ]
    show i₀ (mConeMap y g) / i₀ (mConeMap y h) = _
    have hp : (∏ k, i₀ (X k) ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ ((map_ne_zero_iff _ hi).2 (X_ne_zero _))
    have h1 : i₀ (C (aeval y h)) ≠ 0 := (map_ne_zero_iff _ hi).2 (by rwa [Ne, C_eq_zero])
    rw [cone_homog i₀ hg, cone_homog i₀ hh, mul_div_mul_left _ _ hp, e, map_mul, map_mul,
      mul_div_cancel_right₀ _ h1]
  choose p hp using fun m => lift _ _ (Fr.hp m)
  choose r hr using fun m => lift _ _ (Fr.hr m)
  choose α hα using fun m => lift _ _ (Fr.hα m)
  choose β hβ using fun m => lift _ _ (Fr.hβ m)
  let eF := fibEquiv ι k₀
  let ℓ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → Fin 2 → G.Φ :=
    fun q => ![p (eF q), r (eF q)]
  have hν : ∀ a b : Fin 2, ∑ q, ![fun q => α (eF q), fun q => β (eF q)] a q * ℓ q b = if a = b then 1 else 0 := by
    have key : ∀ (u w : ι k₀ → G.Φ) (u' w' : ι k₀ → Φ) (s : G.Φ) (s' : Φ), (∀ m, ψ (u m) = i₀ (C (u' m))) →
        (∀ m, ψ (w m) = i₀ (C (w' m))) → ψ s = i₀ (C s') → ∑ m, u' m * w' m = s' →
        ∑ q, u (eF q) * w (eF q) = s := fun u w u' w' s s' hu hw hs h => by
      rw [Equiv.sum_comp eF fun m => u m * w m]
      apply ψ.injective
      rw [hs, ← h]
      simp only [map_sum, map_mul, hu, hw]
    intro a b
    fin_cases a <;> fin_cases b
    · exact key α p _ _ 1 1 hα hp (by simp) Fr.αp
    · exact key α r _ _ 0 0 hα hr (by simp) Fr.αr
    · exact key β p _ _ 0 0 hβ hp (by simp) Fr.βp
    · exact key β r _ _ 1 1 hβ hr (by simp) Fr.βr
  refine ⟨linKerForms ℓ, ?_, ?_⟩
  · rintro f ⟨μ, -, rfl⟩
    exact isMultiHomog_lin k₀ μ
  rw [← ker_linSubst ℓ _ hν]
  let W' : MRing (iW ι k₀) →+* MvPolynomial (Fin 2) E := (MvPolynomial.map i₀).comp (planeMap y k₀ Fr.p Fr.r)
  let x' : MRing (iW ι k₀) →+* G.Φ' := (aeval G.x' : MRing (iW ι k₀) →ₐ[ℤ] G.Φ').toRingHom
  have hker : RingHom.ker x' = RingHom.ker W' := by
    rw [RingHom.ker_comp_of_injective _ (MvPolynomial.map_injective _ hi), ← Fr.ker_eq, ← ideal_pen_plane]
    exact G.genericFibre_ker_target
  have r1 : ∀ f, x' (rename (v₀ k₀) f) = algebraMap G.Φ G.Φ' (a f) := fun f => by
    have e : x'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom = (algebraMap G.Φ G.Φ').comp a :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simpa [x', a] using G.compat q
    exact RingHom.congr_fun e f
  have r2 : ∀ f, W' (rename (v₀ k₀) f) = C (ψ (a f)) := fun f => by
    rw [hψ]
    have e : W'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom =
        (C : E →+* _).comp (i₀.comp (mConeMap y).toRingHom) :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simp [W', planeMap, ext2, v₀, mConeMap]
    exact RingHom.congr_fun e f
  have main : ∀ f : MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K)), ∃ (Dn : MRing ι) (f' : MRing (iW ι k₀)),
      a Dn ≠ 0 ∧ x' f' = algebraMap G.Φ G.Φ' (a Dn) *
        aeval (fun q : Σ k : FibreBlock (some : K → Option K), iW ι k₀ k.1 => G.x' ⟨q.1.1, q.2⟩) f ∧
      W' f' = C (ψ (a Dn)) * MvPolynomial.map ψ (linSubst ℓ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C s =>
      obtain ⟨f, g, hg, e⟩ := G.gen s
      have e' : a f = a g * s := by rw [e]; exact (mul_div_cancel₀ _ hg).symm
      refine ⟨g, rename (v₀ k₀) f, hg, ?_, ?_⟩
      · rw [r1, e', map_mul, aeval_C]
      · rw [r2, e', map_mul, map_mul, algHom_C, algebraMap_eq, map_C]
    | add f g hf hg =>
      obtain ⟨D₁, f₁, h₁, a₁, b₁⟩ := hf
      obtain ⟨D₂, f₂, h₂, a₂, b₂⟩ := hg
      refine ⟨D₁ * D₂, f₁ * rename (v₀ k₀) D₂ + f₂ * rename (v₀ k₀) D₁, by rw [map_mul]; exact mul_ne_zero h₁ h₂,
        ?_, ?_⟩
      · simp only [map_add, map_mul, r1, a₁, a₂]; ring
      · simp only [map_add, map_mul, r2, b₁, b₂]; ring
    | mul_X f q hf =>
      obtain ⟨D₁, f₁, h₁, a₁, b₁⟩ := hf
      refine ⟨D₁, f₁ * X ⟨q.1.1, q.2⟩, h₁, ?_, ?_⟩
      · rw [map_mul, map_mul, a₁, aeval_X, mul_assoc]
        congr 2
        exact aeval_X _ _
      · rw [map_mul, map_mul, map_mul, b₁, mul_assoc]
        congr 2
        obtain ⟨m, rfl⟩ := eF.symm.surjective q
        have : W' (X ⟨none, m⟩) = C (i₀ (C (Fr.p m))) * X 0 + C (i₀ (C (Fr.r m))) * X 1 := by
          simp [W', planeMap, ext2]
        refine this.trans ?_
        simp [linSubst, ℓ, Fin.sum_univ_two, hp, hr]
  ext f
  obtain ⟨Dn, f', h0, h1, h2⟩ := main f
  have h3 : x' f' = 0 ↔ W' f' = 0 := SetLike.ext_iff.1 hker f'
  rw [h1, h2, mul_eq_zero, mul_eq_zero, or_iff_right ((map_ne_zero _).2 h0),
    or_iff_right (by rw [C_eq_zero]; exact (map_ne_zero _).2 h0),
    map_eq_zero_iff _ (MvPolynomial.map_injective _ ψ.injective)] at h3
  exact h3

theorem line_pen {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e y c)
    (G : GenFibre (v₀ k₀) (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X))) :
    ∃ T : Set (MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K))),
      (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T :=
  exists_positive_period_line (algebraMap _ (FractionRing (MvPolynomial K Φ))) (IsFractionRing.injective _ _) Fr G

end PositivityTheory.Xgp.W
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.MapSumMinor
section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem map_sum_minor {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u : Finset (Fin N) → R)
    (H : Matrix (Fin N) (Fin N) R) (J : Finset (Fin N)) :
    f (∑ I, u I * minorIJ H I J) = ∑ I, f (u I) * minorIJ (H.map f) I J := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun I _ => by rw [map_mul, CPts.minorIJ_map]

theorem frame_colsB {τ : Ψ} {a b ca cb : Fin N} {k₀ : K} (s : Swp N j a b ca cb) (hk : M.blk (τ, a) = some k₀)
    {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {H bb : Matrix (Fin N) (Fin N) Φ} (hH : IsBlockDiag j H)
    (hbb : IsBlockDiag j bb) (hbt : bb.BlockTriangular id)
    (e : (F.T τ).map (algebraMap M.Ω Φ) * H = M.g τ * bb) (m : ι k₀) :
    algebraMap M.Ω Φ (detFac j a (F.T τ)) * ((∏ c ∈ (stepCols N j a).erase ca, bb c c) *
      (bb cb cb * vecB M τ a k₀ ca cb m + bb ca cb * y ⟨k₀, m⟩)) =
      algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, a) k') *
        ∑ I, algebraMap M.Ω Φ (F.u ⟨k₀, m⟩ I) * minorIJ H I (colsB N j a ca cb) := by
  haveI : Infinite M.Ω := Infinite.of_injective (Nat.cast : ℕ → M.Ω) Nat.cast_injective
  have h1 := GlobalTheory.T.minor_sum_identity_base_change M.Ω N j (F.T τ) _ _ (M.coef ⟨k₀, m⟩) (F.u ⟨k₀, m⟩) (stepCols N j a)
    (hF.2.1 (τ, a) k₀ hk m) Φ _ (s.block_swap hH)
  have e2 : (F.T τ).map (algebraMap M.Ω Φ) * H.updateCol ca (fun r => H r cb) =
      (M.g τ * bb).updateCol ca fun r => (M.g τ * bb) r cb := by
    rw [← e]
    ext r c
    simp only [Matrix.mul_apply, updateCol_apply]
    split_ifs <;> rfl
  simp only [e2, ← s.minor_colsB, s.minor_colsB_mul _ hbb hbt] at h1
  rw [← h1, vecB, M.y_step (τ, a) k₀ hk m]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun I _ => by ring

theorem core {τ : Ψ} {a b ca cb : Fin N} {k₀ : K} (s : Swp N j a b ca cb) (hk : M.blk (τ, a) = some k₀)
    {z : (Σ k, ι k) → L} (hz : IsPt y z) (c : ∀ k, ι k) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0)
    {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z)))
    (uv : (Σ k, ι k) → Finset (Fin N) → L) (huv : ∀ q I, HasVal M.x (basePart M.blk z) (F.u q I) (uv q I))
    (υv : Fin N → L) (hυ : ∀ i, M.blk (τ, i) = none → HasVal M.x (basePart M.blk z) (F.υ (τ, i)) (υv i)) :
    ∃ (PF : PenFrame y k₀ (vecB M τ a k₀ ca cb) (cFac M τ a) (eDeg M τ a k₀) z c) (H₀ : Matrix (Fin N) (Fin N) L)
      (ev : Fin N → L), IsBlockDiag j H₀ ∧ H₀.det ≠ 0 ∧
      (∀ i k, M.blk (τ, i) = some k → ev i ≠ 0 ∧
        ∀ m, ev i * z ⟨k, m⟩ = ∑ I, uv ⟨k, m⟩ I * minorIJ H₀ I (stepCols N j i)) ∧
      (∀ m, PF.pv m = ∑ I, uv ⟨k₀, m⟩ I * minorIJ H₀ I (stepCols N j a)) ∧
      (∀ m, PF.rv m = ∑ I, uv ⟨k₀, m⟩ I * minorIJ H₀ I (colsB N j a ca cb)) ∧
      PF.sv = muI N j b H₀ * PF.pv (c k₀) ^ 2 * ∏ i, ((if IsProperStep N j i then ev i else υv i) *
        (∏ k', basePart M.blk z ⟨k', F.c k'⟩ ^ M.b (τ, i) k') * chartMono z c (M.dy (τ, i))) ^ xiCoef τ a (τ, i) := by
  obtain ⟨bb, H, H', hbb, hbt, hbd, hH, hH', e⟩ := exists_flag_frame M τ hz hF hG
  let am := algebraMap M.Ω Φ
  let O := regO y z
  let val := valO hz
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hz.coord_ne (hc k)
  let u : (Σ k, ι k) → Finset (Fin N) → O := fun q I => ⟨am (F.u q I), _, hasVal_base M (huv q I)⟩
  let u' : Finset (Fin N) → (Σ k, ι k) → O := fun I q => ⟨am (F.u' I q),
    (exists_hasVal_of_regAt (hG.2.1 q I).2).imp fun _ => hasVal_base M⟩
  have hu : ∀ q I, val (u q I) = uv q I := fun q I => valO_eq hz _ (hasVal_base M (huv q I))
  have horth : ∀ i k, M.blk (τ, i) = some k → ∀ I I', IsStepRows N j i I → IsStepRows N j i I' →
      ∑ m, u' I ⟨k, m⟩ * u ⟨k, m⟩ I' = if I = I' then 1 else 0 := fun i k hp I I' h1 h2 => Subtype.ext (by
    have := congrArg am (hF.2.2.1 (τ, i) k hp I I' h1 h2)
    rw [map_sum] at this
    simp only [map_mul] at this
    simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
    refine this.trans ?_
    split_ifs <;> simp)
  let wf : (Σ k, ι k) → Finset (Fin N) → O := fun q J => ∑ I, u q I * minorIJ H I J
  let du : Fin N → Finset (Fin N) → (Σ k, ι k) → O := fun i J q =>
    ∑ I, (if IsStepRows N j i I then minorIJ H' J I else 0) * u' I q
  have hwf : ∀ q J, (wf q J : Φ) = ∑ I, am (F.u q I) * minorIJ (H.map O.subtype) I J := fun q J =>
    map_sum_minor O.subtype _ _ _
  have hwv : ∀ q J, val (wf q J) = ∑ I, uv q I * minorIJ (H.map val) I J := fun q J => by
    rw [map_sum_minor]; simp only [hu]
  have hdu : ∀ i k, M.blk (τ, i) = some k → ∀ J J', (∀ I, ¬ IsStepRows N j i I → minorIJ H I J = 0) →
      ∑ m, du i J' ⟨k, m⟩ * wf ⟨k, m⟩ J = minorIJ 1 J' J := fun i k hp J J' h0 => by
    rw [← hH']
    exact dual_sum' i (fun m I => u ⟨k, m⟩ I) (fun I m => u' I ⟨k, m⟩) (horth i k hp) H H' J J' h0
  have hD : ∀ i, am (detFac j i (F.T τ)) ≠ 0 := fun i =>
    (map_ne_zero am).2 (CPts.detFac_ne_zero M.j_le i (hF.1 τ).1 (hF.1 τ).2)
  let xF : Fin N → Φ := fun i => am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k')
  have hE : ∀ i, xF i ≠ 0 := fun i => (map_ne_zero am).2
    (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (M.x_chart_ne (isPt_base M hz).le hG k'))
  have rel : ∀ i k, M.blk (τ, i) = some k → ∀ m, am (detFac j i (F.T τ)) * (∏ c ∈ stepCols N j i, bb c c) * y ⟨k, m⟩ =
      xF i * wf ⟨k, m⟩ (stepCols N j i) := fun i k hp m => by
    rw [hwf]
    exact CPts.frame_gen M hF (RingHom.id Φ) hp m (hH.map _) hbb hbt e
  have hev : ∀ i, ∃ ev : L, ∀ k, M.blk (τ, i) = some k → ev ≠ 0 ∧
      ∀ m, ev * z ⟨k, m⟩ = val (wf ⟨k, m⟩ (stepCols N j i)) := fun i => by
    cases hp : M.blk (τ, i) with
    | none => exact ⟨0, fun k h => by cases h⟩
    | some k =>
      have h1 : ∀ m, val (wf ⟨k, c k⟩ (stepCols N j i)) / z ⟨k, c k⟩ * z ⟨k, m⟩ =
          val (wf ⟨k, m⟩ (stepCols N j i)) := fun m => by
        have h2 := (hasVal_ratio hz m (c k) (hc k)).mul (hasVal_valO hz (wf ⟨k, c k⟩ (stepCols N j i)))
        have h3 : y ⟨k, m⟩ / y ⟨k, c k⟩ * wf ⟨k, c k⟩ (stepCols N j i) = wf ⟨k, m⟩ (stepCols N j i) := by
          refine mul_left_cancel₀ (hE i) ?_
          have := hyc k
          rw [mul_left_comm, ← rel i k hp, ← rel i k hp]
          field_simp
        rw [h3] at h2
        rw [show val (wf ⟨k, m⟩ (stepCols N j i)) = _ from valO_eq hz _ h2]
        ring
      refine ⟨val (wf ⟨k, c k⟩ (stepCols N j i)) / z ⟨k, c k⟩, fun k' h => ?_⟩
      obtain rfl := Option.some.inj h
      refine ⟨fun h0 => ?_, h1⟩
      have h4 := congrArg val (hdu i k hp _ (stepCols N j i) fun I hI => minor_stepCols_eq_zero M.j_le H I hH hI)
      rw [CPts.minorIJ_one, map_one, map_sum] at h4
      refine zero_ne_one (Eq.trans (Finset.sum_eq_zero fun m _ => ?_).symm h4)
      rw [map_mul, ← h1 m, h0, zero_mul, mul_zero]
  choose ev hev using hev
  let lam : Fin N → Φ := fun i => am (M.lam (τ, i))
  let Tm := (F.T τ).map am
  let Nv : Fin N → L := fun i => (if IsProperStep N j i then ev i else υv i) *
    (∏ k', basePart M.blk z ⟨k', F.c k'⟩ ^ M.b (τ, i) k') * chartMono z c (M.dy (τ, i))
  have hN : ∀ i, HasVal y z (nI N j lam Tm bb i * chartMono y c (M.dy (τ, i))) (Nv i) ∧ Nv i ≠ 0 := fun i => by
    have hzF : (∏ k', basePart M.blk z ⟨k', F.c k'⟩ ^ M.b (τ, i) k') ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (chart_ne M hG k')
    have hR : HasVal y z (xF i * ∏ k : NonPluckerBlocks M.blk, (y ⟨k.1, c k.1⟩ ^ M.b (τ, i) k)⁻¹)
        ((∏ k', basePart M.blk z ⟨k', F.c k'⟩ ^ M.b (τ, i) k') *
          ∏ k : NonPluckerBlocks M.blk, (z ⟨k.1, c k.1⟩ ^ M.b (τ, i) k)⁻¹) := by
      simp only [xF, map_prod, map_zpow₀, ← Finset.prod_mul_distrib]
      refine HasVal.prod _ fun k _ => ?_
      have := (hasVal_ratio hz (F.c k) (c k.1) (hc k.1)).zpow hz (div_ne_zero (chart_ne M hG k) (hc k.1)) (M.b (τ, i) k)
      rw [div_zpow, div_zpow, div_eq_mul_inv, div_eq_mul_inv] at this
      rw [← M.y_base ⟨k, F.c k⟩]
      exact this
    simp only [Nv, nI, chartMono_dy, Tm, detFac_map]
    by_cases hp : IsProperStep N j i
    · obtain ⟨k, hk⟩ := blk_some M τ hp
      rw [if_pos hp, if_pos hp, hk]
      simp only [Option.elim]
      refine ⟨?_, mul_ne_zero (mul_ne_zero (hev i k hk).1 hzF) (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k' _ =>
        inv_ne_zero (zpow_ne_zero _ (hc _))) (hc k))⟩
      have := (hasVal_valO hz (wf ⟨k, c k⟩ (stepCols N j i))).mul hR
      convert this using 1
      · linear_combination (∏ k : NonPluckerBlocks M.blk, (y ⟨k.1, c k.1⟩ ^ M.b (τ, i) k)⁻¹) * rel i k hk (c k)
      · rw [show valO hz (wf ⟨k, c k⟩ (stepCols N j i)) = _ from ((hev i k hk).2 (c k)).symm]; ring
    · have hk : M.blk (τ, i) = none := (M.blk_none _).2 hp
      have hυ0 : υv i ≠ 0 := fun h0 => by
        obtain ⟨w, hw⟩ := exists_hasVal_of_regAt (hG.2.2 _ hk).2.2
        have := (hυ i hk).mul hw
        rw [mul_inv_cancel₀ (hG.2.2 _ hk).1, h0, zero_mul] at this
        exact zero_ne_one (this.unique (isPt_base M hz) hasVal_one)
      rw [if_neg hp, if_neg hp, hk]
      simp only [Option.elim]
      refine ⟨?_, mul_ne_zero (mul_ne_zero hυ0 hzF) (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k' _ =>
        inv_ne_zero (zpow_ne_zero _ (hc _))) one_ne_zero)⟩
      have := (hasVal_base M (hυ i hk)).mul hR
      have h5 := congrArg am (hF.2.2.2 (τ, i) hk)
      rw [map_mul, map_mul] at h5
      convert this using 1
      · linear_combination (∏ k : NonPluckerBlocks M.blk, (y ⟨k.1, c k.1⟩ ^ M.b (τ, i) k)⁻¹) * h5
      · ring
  let S := stepCols N j a
  let S' := colsB N j a ca cb
  let P := ∏ c ∈ S.erase ca, bb c c
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hbd c
  have hPa : ∏ c ∈ S, bb c c = bb ca ca * P := (Finset.mul_prod_erase _ _ s.ca_mem).symm
  have h0 : ∀ I, ¬ IsStepRows N j a I → minorIJ H I S = 0 := fun I hI => minor_stepCols_eq_zero M.j_le H I hH hI
  have h0' : ∀ I, ¬ IsStepRows N j a I → minorIJ H I S' = 0 := fun I hI => s.minor_colsB_eq_zero hH I hI
  have coe : ∀ {J J' : Finset (Fin N)} {t : O}, ∑ m, du a J' ⟨k₀, m⟩ * wf ⟨k₀, m⟩ J = t →
      ∑ m, (du a J' ⟨k₀, m⟩ : Φ) * wf ⟨k₀, m⟩ J = t := fun h => by
    rw [← h]; simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
  let ε := am (detFac j a (F.T τ)) * (bb ca ca * P) / xF a
  let γ := am (detFac j a (F.T τ)) * (P * bb cb cb) / xF a
  have hp : ∀ m, (wf ⟨k₀, m⟩ S : Φ) = ε * y ⟨k₀, m⟩ := fun m => by
    have := rel a k₀ hk m
    rw [hPa] at this
    rw [div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ (hE a)]
  have hmu : HasVal y z (muI N j b (H.map O.subtype)) (muI N j b (H.map val)) := by
    rw [muI_map, muI_map]; exact hasVal_valO hz _
  have hmu0 : muI N j b (H.map val) ≠ 0 := by
    have := congrArg val (muI_unit M.j_le b hH hH')
    rw [map_mul, map_one] at this
    rw [muI_map]
    exact right_ne_zero_of_mul_eq_one this
  have hpv0 : val (wf ⟨k₀, c k₀⟩ S) ≠ 0 := by
    rw [← (hev a k₀ hk).2]; exact mul_ne_zero (hev a k₀ hk).1 (hc k₀)
  have hsv : HasVal y z (cFac M τ a * ε * γ / chartMono y c (eDeg M τ a k₀))
      (muI N j b (H.map val) * val (wf ⟨k₀, c k₀⟩ S) ^ 2 * ∏ i, Nv i ^ xiCoef τ a (τ, i)) := by
    have h1 := (hmu.mul ((hasVal_valO hz (wf ⟨k₀, c k₀⟩ S)).pow 2)).mul
      (HasVal.prod Finset.univ fun i _ => (hN i).1.zpow hz (hN i).2 (xiCoef τ a (τ, i)))
    convert h1 using 1
    have hTd : Tm.det ≠ 0 := by
      rw [show Tm.det = am (F.T τ).det from (RingHom.map_det am _).symm]
      exact (map_ne_zero am).2 (hF.1 τ).2
    have h2 := s.alg τ lam ((hF.1 τ).1.map am) hTd (hH.map O.subtype) hbb hbt hbd e
    have h3 : cFac M τ a = ∏ i, facI N j a lam (M.g τ) i ^ xiCoef τ a (τ, i) := prod_xi_pair τ a _
    have h4 := chartMono_eDeg M hyc τ a k₀
    have h5 : γ * bb ca ca = ε * bb cb cb := by simp only [γ, ε]; ring
    rw [← h3] at h2
    simp only [mul_zpow, Finset.prod_mul_distrib]
    rw [hp, div_eq_iff (chartMono_ne hyc _)]
    refine mul_right_cancel₀ (hbd ca) ?_
    linear_combination (cFac M τ a * ε) * h5 + ε ^ 2 * h2 -
      (ε ^ 2 * muI N j b (H.map O.subtype) * bb ca ca * ∏ i, nI N j lam Tm bb i ^ xiCoef τ a (τ, i)) * h4
  have hcaS' : ca ∉ S' := by
    simp only [S', colsB, Finset.mem_insert, Finset.notMem_erase, or_false]; exact s.lt_cb.ne
  refine ⟨{
      p := fun m => wf ⟨k₀, m⟩ S, r := fun m => wf ⟨k₀, m⟩ S', α := fun m => du a S ⟨k₀, m⟩,
      β := fun m => du a S' ⟨k₀, m⟩, pv := fun m => val (wf ⟨k₀, m⟩ S), rv := fun m => val (wf ⟨k₀, m⟩ S'),
      αv := fun m => val (du a S ⟨k₀, m⟩), βv := fun m => val (du a S' ⟨k₀, m⟩), ε := ε, γ := γ,
      δ := am (detFac j a (F.T τ)) * (P * bb ca cb) / xF a, sv := _,
      hp := fun m => hasVal_valO hz _, hr := fun m => hasVal_valO hz _, hα := fun m => hasVal_valO hz _,
      hβ := fun m => hasVal_valO hz _,
      ε_ne := div_ne_zero (mul_ne_zero (hD a) (mul_ne_zero (hbd _) hP)) (hE a),
      γ_ne := div_ne_zero (mul_ne_zero (hD a) (mul_ne_zero hP (hbd _))) (hE a),
      p_eq := hp, r_eq := fun m => ?_,
      αp := coe (t := 1) ((hdu a k₀ hk S S h0).trans (CPts.minorIJ_one _)),
      αr := coe (t := 0) ((hdu a k₀ hk S' S h0').trans (minor_one_of_ne s.ca_mem hcaS')),
      βp := coe (t := 0) ((hdu a k₀ hk S S' h0).trans (minor_one_of_ne (Finset.mem_insert_self _ _) s.cb_notMem)),
      βr := coe (t := 1) ((hdu a k₀ hk S' S' h0').trans (CPts.minorIJ_one _)),
      hs := hsv,
      sv_ne := mul_ne_zero (mul_ne_zero hmu0 (pow_ne_zero _ hpv0))
        (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hN i).2) },
    H.map val, ev, hH.map _, ?_, fun i k hp => ⟨(hev i k hp).1, fun m => ((hev i k hp).2 m).trans (hwv _ _)⟩,
    fun m => hwv _ _, fun m => hwv _ _, rfl⟩
  · have := frame_colsB M s hk hF (hH.map O.subtype) hbb hbt e m
    refine mul_left_cancel₀ (hE a) ?_
    rw [hwf]
    refine this.symm.trans ?_
    have := hE a
    simp only [γ]
    field_simp
    ring
  · have := congrArg (fun A => val (Matrix.det A)) hH'
    simp only [det_mul, map_mul, det_one, map_one] at this
    rw [show (H.map val).det = val H.det from (RingHom.map_det val _).symm]
    exact right_ne_zero_of_mul_eq_one this

end PositivityTheory.Xgp.W
end
end

