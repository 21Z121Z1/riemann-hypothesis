import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0232
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientConjugateThetaForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1686
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TripleSpaceW

open scoped ComplexOrder

theorem hasSig_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by simpa using (Fintype.card_congr e).symm, (P.1.submatrix e id).map star, ?_⟩
  have hJ : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := rfl
  rw [hJ, ← hP]
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id, Formalism.UG.cT,
    Matrix.reindex_apply, star_star]
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  · rw [← e.symm.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [e.apply_symm_apply]; rfl
  · rw [e.apply_symm_apply]

theorem isCartan_map_conj {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (G.map (starRingEnd ℂ)) s := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, fun x hx => ?_⟩
  · have := congrArg (fun A : Matrix (Fin k) (Fin k) ℂ => A.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul] at this
    rw [← this]
    congr 2
    ext a b
    simp [Matrix.conjTranspose_apply]
  · have hsG : sᴴ * G = G * s := by
      calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
        _ = G * s := by rw [← Matrix.mul_assoc, h2]
    have e1 : (s *ᵥ x) ⬝ᵥ G.map (starRingEnd ℂ) *ᵥ star x = star (star x ⬝ᵥ (G * s) *ᵥ x) := by
      calc (s *ᵥ x) ⬝ᵥ G.map (starRingEnd ℂ) *ᵥ star x = (s *ᵥ x) ⬝ᵥ star (G *ᵥ x) := by
            congr 1; ext a; simp [Matrix.mulVec, dotProduct, star_sum]
        _ = star (star (s *ᵥ x) ⬝ᵥ G *ᵥ x) := by rw [Matrix.star_dotProduct, star_star, dotProduct_comm]
        _ = star (star x ⬝ᵥ (G * s) *ᵥ x) := by
            rw [← hsG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star x) sᴴ, ← Matrix.star_mulVec]
    have := h3.dotProduct_mulVec_pos hx
    rw [e1, Complex.star_def, Complex.conj_re]
    exact (Complex.lt_def.1 this).1

section ConjLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def conjO (r : 𝓞 E) : 𝓞 E := ⟨star (r : E), (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom⟩

theorem coe_conjO (r : 𝓞 E) : ((conjO r : 𝓞 E) : E) = star (r : E) := rfl

theorem star_smulO (r : 𝓞 E) (y : Fin n → E) : star (r • y) = conjO r • star y := by
  ext i
  simp only [Pi.star_apply, Pi.smul_apply, Algebra.smul_def, star_mul']
  rfl

def conjSub (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | star y ∈ Λ}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, star_add] at ha hb ⊢; exact Λ.add_mem ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, star_zero]; exact Λ.zero_mem
  smul_mem' := fun r y hy => by
    have e : star (r • y) = conjO r • star y := star_smulO r y
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [e]; exact Λ.smul_mem _ hy

theorem mem_conjSub {Λ : Submodule (𝓞 E) (Fin n → E)} {y : Fin n → E} : y ∈ conjSub Λ ↔ star y ∈ Λ := Iff.rfl

theorem star_mem_span {R : Type} [CommRing R] [Module R (Fin n → E)] (c : R → R)
    (hc : ∀ (r : R) (y : Fin n → E), star (r • y) = c r • star y) {s : Set (Fin n → E)} {y : Fin n → E}
    (hy : y ∈ Submodule.span R s) : star y ∈ Submodule.span R (star '' s) := by
  induction hy using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [star_add]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [hc]; exact Submodule.smul_mem _ _ hx

theorem star_smulE (r : E) (y : Fin n → E) : star (r • y) = star r • star y := by
  ext i; simp [star_mul']

theorem conjSub_isLattice {Λ : Submodule (𝓞 E) (Fin n → E)} (h : Λ.IsLattice E) : (conjSub Λ).IsLattice E := by
  obtain ⟨S, hS⟩ := h.fg
  have e : conjSub Λ = Submodule.span (𝓞 E) (star '' (S : Set (Fin n → E))) := by
    refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
    · have := star_mem_span conjO star_smulO (hS ▸ (mem_conjSub.1 hy))
      rwa [star_star] at this
    · rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, mem_conjSub, star_star, ← hS]
      exact Submodule.subset_span hx
  refine ⟨?_, ?_⟩
  · rw [e, Submodule.fg_def]
    exact ⟨_, S.finite_toSet.image _, rfl⟩
  · refine eq_top_iff.2 fun v _ => ?_
    have hv : star v ∈ Submodule.span E (Λ : Set (Fin n → E)) := h.span_eq_top ▸ Submodule.mem_top
    have := star_mem_span star star_smulE hv
    rw [star_star] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_conjSub, star_star]
    exact hx

theorem exists_coe_iff (z : E) : (∃ b : 𝓞 E, (b : E) = z) ↔ IsIntegral ℤ (star z) := by
  refine ⟨fun ⟨b, hb⟩ => hb ▸ (RingOfIntegers.isIntegral_coe b).map (starRingEnd E).toIntAlgHom, fun h => ?_⟩
  have h' : IsIntegral ℤ z := by simpa [starRingEnd_apply] using h.map (starRingEnd E).toIntAlgHom
  exact ⟨⟨z, h'⟩, rfl⟩

end ConjLat

end GlobalTheory.TripleSpaceW

namespace GlobalTheory.FunObj

theorem isHerm_spaceW : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin (spW G i j).rank → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin (spW G i j).rank) (Fv D.host.F v)),
      Spc.IsHerm D.sp.cm.sig B
        (Spc.mk ((1 : D.host.E) • (spW G i j).gram) Λ (fun w => W.cart (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) (τf w)) bas)
        ((spW G i j).rank - (D.R.m - j - 1) / 2) ((D.R.m - j - 1) / 2) := by
  intro D T L sc G μ₀ hL W i j B τf hemb
  have hX : (Node.grid ((i : ℕ) + 1) ((j : ℕ) + 1)).InRange D.R.m := ⟨i.2, j.2⟩
  have hV := node_isV G hL hX
  haveI hlat : (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))).IsLattice D.host.E :=
    GlobalTheory.TripleSpaceW.conjSub_isLattice hV.sd.1
  choose bas0 hbas0 using fun v : B.P =>
    GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))))
      (GlobalTheory.AdelicU.isCMExt_host D)
  have hq : Node.neg D.R.m (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) = (D.R.m - j - 1) / 2 := by
    show (D.R.m - ((j : ℕ) + 1)) / 2 = _
    rw [Nat.sub_sub]
  have hherm : ∀ a b, star ((spW G i j).gram b a) = (spW G i j).gram a b := fun a b =>
    (spW G i j).herm.eq ((spW G i j).frame b) ((spW G i j).frame a)
  refine ⟨GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))),
    fun v => if h : v ∈ B.P then bas0 ⟨v, h⟩ else 1, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => ?_, fun w => ?_, fun v => ?_⟩⟩
  · show star (((1 : D.host.E) • (spW G i j).gram) b a) = ((1 : D.host.E) • (spW G i j).gram) a b
    rw [one_smul]
    exact hherm a b
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1) _ _
    have hs := hV.sigOK (B.emb w).1
    rw [hV.sig, hq, ← hV.rank] at hs
    rw [one_smul]
    exact GlobalTheory.TripleSpaceW.hasSig_of_hasSignature hs
  · have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
    have hh' : ∀ a b, star ((spW G i j).gram a b) = (spW G i j).gram b a := fun a b => hherm b a
    have key : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((1 : D.host.E) • (spW G i j).gram) y x =
        star (∑ a, ∑ b, star ((star x) a) * (spW G i j).gram a b * (star y) b) := fun x => by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, one_smul, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star,
        Pi.star_apply, hσ, hh', Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    show star y ∈ G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ↔ _
    rw [hV.sd.2 (star y)]
    constructor
    · intro h x hx
      rw [key, ← GlobalTheory.TripleSpaceW.exists_coe_iff]
      exact h _ hx
    · intro h x' hx'
      have := h (star x') (by rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx')
      rw [key, ← GlobalTheory.TripleSpaceW.exists_coe_iff, star_star] at this
      exact this
  · have e : ((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1 =
        (gramAt D (spW G i j) (τf w)).map (starRingEnd ℂ) := by
      ext a b
      simp only [one_smul, Matrix.map_apply, hemb, gramAt]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1) _
    rw [e]
    exact GlobalTheory.TripleSpaceW.isCartan_map_conj (W.cart_is _ hX (τf w))
  · show GlobalTheory.AdelicU.IsSplitBasis (B.τ v) _ (if h : v.1 ∈ B.P then bas0 ⟨v.1, h⟩ else 1)
    rw [dif_pos v.2]
    exact hbas0 v

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixCongrAdelicMatrixModNat
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.CosetApprox

theorem exists_mem_approx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (m : ℕ) (hm : 0 < m) (y : AE D)
    (hy : y ∈ hatId D 𝔪) : ∃ b ∈ 𝔪, ∃ t ∈ IhE D ⊤, inc D (b : D.host.E) - y = (m : AE D) * t := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    obtain ⟨r, w, hw, e⟩ := GlobalTheory.AdelicApprox.exists_approx D m hm s hs
    have hr : inc D r ∈ OhE D := by
      have : inc D r = s - (m : AE D) * w := by rw [e]; ring
      rw [this]
      exact sub_mem hs (mul_mem (natCast_mem _ m) hw)
    have hri : IsIntegral ℤ r := Formalism.UG.P.csGlob_int (F := ℚ) _ hr
    let r' : 𝓞 D.host.E := ⟨r, hri⟩
    have hbr : b * r' ∈ 𝔪 := Ideal.mul_mem_right _ _ hb
    have hbw : inc D (b : D.host.E) * w ∈ OhE D := mul_mem (Formalism.UG.P.adelstab_incl_int b) hw
    refine ⟨b * r', hbr, -(inc D (b : D.host.E) * w), neg_mem ?_, ?_⟩
    · have := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ _ hbw
      simpa using this
    · have hc : ((b * r' : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) * r := rfl
      rw [hc, map_mul, e]
      ring
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, t, ht, e⟩ := hx
    obtain ⟨b', hb', t', ht', e'⟩ := hy
    refine ⟨b + b', add_mem hb hb', t + t', add_mem ht ht', ?_⟩
    push_cast
    rw [map_add]
    linear_combination e + e'
  | neg x _ hx =>
    obtain ⟨b, hb, t, ht, e⟩ := hx
    refine ⟨-b, neg_mem hb, -t, neg_mem ht, ?_⟩
    push_cast
    rw [map_neg]
    linear_combination -e

theorem matrix_approx : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (Y : Matrix (Fin d) (Fin a) (AE D)),
    (∀ i j, Y i j ∈ hatId D 𝔪) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ ∀ i j, ∃ y ∈ IhE D ⊤, (w.map (inc D) - Y) i j = (m : AE D) * y := by
  intro D 𝔪 a d Y hY m hm
  choose b hb t ht e using fun i j => exists_mem_approx D 𝔪 m hm (Y i j) (hY i j)
  refine ⟨Matrix.of fun i j => ((b i j : 𝓞 D.host.E) : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩,
    fun i j => ⟨t i j, ht i j, ?_⟩⟩
  simpa using e i j

end GlobalTheory.FunObj.CosetApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIoConjOfFive
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedWeights

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift in

theorem exists_io_conj_ofFive : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → HypConj R i σ μ' η' → ∀ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ io, IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ B f) (deltaConj i σ) io := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ _ μ' η' _ hH c c₁ hc ω f₀ f B hω hv
  have hM := hR.models
  have hθ : IsInfFam R.θ := hM.inf
  have hψ : IsStdChar D R.ψ (-1) := hv.vec.1.1
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f :=
    hv.vec.2.elim fun _ h => isThetaFunO_of_isThetaAt hψ hθ h.2 hv.vec.1.2.theta
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => onb_eq_one (hM.BV i τ)
  have hBu : ∀ τ, IsUnit (R.BV i τ) := fun τ => (IsUnit.of_mul_eq_one_right _ (hBS τ))
  have hw := fun ρ => weights_label D i (lab σ ρ) (pW D i ρ) (qW D i ρ)
    (congrArg Prod.fst ((hH.sig ρ).trans (hH.sig _).symm)) (congrArg Prod.snd ((hH.sig ρ).trans (hH.sig _).symm))
    ((R.MW i σ).lam ρ) ((R.MW i σ).ε ρ) (by have := (R.MW i σ).enum ρ; rw [hH.par ρ] at this; exact this)
  choose x₁ x₂ x₃ hx₁ hx₂ hx₃ hK hU hpq hε hap ham using hw
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hj := exists_poly_model (Vc D i) R.θ c (lamV D i) σ (Equiv.ofBijective _ hH.lab_bij) hH.lab_at c₁ hθ
    hc.coef hc.act hc.indep hc.span (R.BV i) hBu
  obtain ⟨j, hj1, hj2⟩ := hj
  exact exists_isIoW D (Vc D i) (Wc D i) R.ψ R.θ _ (R.MW i σ) c (lamV D i) (Equiv.ofBijective _ hH.lab_bij) (R.BV i) B
    j hj1 hj2 _ _ _ _ x₁ x₂ x₃ (hrk.le.trans (r_le_V i)) hpq hε hap ham hK hU _ _ ω hω hψ hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS hv.onb _ _ hH.mu_inf
    (fun τ => GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hH.mu_inf τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hH.eta_inf τ)))
    hx₁ hx₂ hx₃ f hth (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv.vec hth)

end GlobalTheory.MovedWeights

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompactOfUnipotentCoordinatesMem
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_isCompact_of_crd_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ Ω : Set (AF F ⊗[F] E), IsCompact Ω → ∃ V : Set (GAd σ J), IsCompact V ∧ ∀ (u : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (∀ i k, b i k ∈ Ω) → (∀ i k, c i k ∈ Ω) → u ∈ V := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hFr Ω hΩ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  let Φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := fun p =>
    adMat F C * adMat F (cT (σ : E →+* E) D * J) + (adMat F Z + adMat F C * p.1) * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (adMat F D - adMat F Z * plus σ J₀ p.1 + adMat F C * p.2) * adMat F (cT (σ : E →+* E) C * J)
  have key : ∀ u b c, Crd σ J C D Z J₀ u b c → (matHom _ σ J u).1 = Φ (b, c) := by
    intro u b c h
    have hs : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
        adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
      have := congrArg (Matrix.map · (inclR (F := F) (E := E) (AF F))) hFr.sum
      simpa only [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using this
    calc (matHom _ σ J u).1 = (matHom _ σ J u).1 * 1 := (Matrix.mul_one _).symm
      _ = Φ (b, c) := by
        rw [← hs, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), ← Matrix.mul_assoc _ (adMat F Z),
          ← Matrix.mul_assoc _ (adMat F D), h.onC, h.onZ, h.onD]
  have hsig := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
  have hΦ : Continuous Φ := by
    have h1 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.1 := continuous_fst
    have h2 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.2 := continuous_snd
    have hp : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => plus σ J₀ p.1 :=
      continuous_const.matrix_mul (h1.matrix_map hsig).matrix_transpose
    exact ((continuous_const.add ((continuous_const.add (continuous_const.matrix_mul h1)).matrix_mul continuous_const)).add
      (((continuous_const.sub (continuous_const.matrix_mul hp)).add (continuous_const.matrix_mul h2)).matrix_mul continuous_const))
  have hadj : Continuous (adjA σ J) := by
    have : Continuous fun X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) => cT (sigR (AF F) σ) X :=
      (continuous_id.matrix_map hsig).matrix_transpose
    exact (continuous_const.matrix_mul this).matrix_mul continuous_const
  let S : Set (Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω) ×ˢ (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω)
  have hS : IsCompact S := (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ).prod
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ)
  let ψ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) × (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ :=
    fun p => (Φ p, MulOpposite.op (adjA σ J (Φ p)))
  have hψ : Continuous ψ := hΦ.prodMk (MulOpposite.continuous_op.comp (hadj.comp hΦ))
  have hce : IsClosedEmbedding fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g) :=
    (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).comp (isClosedEmbedding_matHom_GAd σ J)
  refine ⟨(fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g)) ⁻¹' (ψ '' S), hce.isCompact_preimage (hS.image hψ), ?_⟩
  intro u b c h hb hc
  refine ⟨(b, c), ⟨fun i _ k _ => hb i k, fun i _ k _ => hc i k⟩, ?_⟩
  have e1 := key u b c h
  have e2 := adjA_mat hFr.herm u
  simp only [ψ, Units.embedProduct_apply, ← e1, e2, ← map_inv]

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.ArInt

namespace GlobalTheory.ThetaRR

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def IsTate (f : X ⟶ X) (hf : f ≫ p = p) (L : HermLB p) (w : LB.Iso (L.pull f hf).B (L.pow 4).B)
    (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) : Prop :=
  ∀ (σ : k →+* ℂ) (a : (L.pow 4).B.ι) (b : (L.pull f hf).B.ι) (y : CxPts p σ),
    y ∈ ptsIn p σ ((L.pow 4).B.U a) → y ∈ ptsIn p σ ((L.pull f hf).B.U b) →
      ((L.pow 4).φ σ).φ a y + 4 * u σ y = ((L.pull f hf).φ σ).φ b y + u σ (PtsOver.map f hf _ y) +
        Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2)

theorem exists_isTate_zero {f : X ⟶ X} {hf : f ≫ p = p} {L : HermLB p}
    (h : (L.pull f hf).Isometric (L.pow 4)) : ∃ w, w.IsGen ∧ IsTate f hf L w fun _ _ => 0 := by
  obtain ⟨w, hw, h⟩ := h
  exact ⟨w, hw, fun σ a b y ha hb => by simpa using h σ a b y ha hb⟩

theorem IsTate.isometric {f : X ⟶ X} {hf : f ≫ p = p} {L : HermLB p}
    {w : LB.Iso (L.pull f hf).B (L.pow 4).B} (hw : w.IsGen) {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (h : IsTate f hf L w u) (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) :
    ((L.raise u hu hc).pull f hf).Isometric ((L.raise u hu hc).pow 4) := by
  refine ⟨w, hw, fun σ a b y ha hb => ?_⟩
  have e := h σ a b y ha hb
  have e₁ : (((L.raise u hu hc).pow 4).φ σ).φ a y = ((L.pow 4).φ σ).φ a y + 4 * u σ y := by
    refine (((L.raise u hu hc).φ σ).zpow_φ _ a y).trans ?_
    refine Eq.trans ?_ (congrArg (· + 4 * u σ y) ((L.φ σ).zpow_φ _ a y).symm)
    change _ * (_ + _) = _
    push_cast
    ring
  have e₂ : (((L.raise u hu hc).pull f hf).φ σ).φ b y =
      ((L.pull f hf).φ σ).φ b y + u σ (PtsOver.map f hf _ y) :=
    (((L.raise u hu hc).φ σ).pull_φ f hf b y).trans
      (congrArg (· + u σ (PtsOver.map f hf _ y)) ((L.φ σ).pull_φ f hf b y).symm)
  rw [e₁, e₂]
  exact e

end GlobalTheory.ThetaRR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionVanishingDegreePosStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_pow_section_vanishing_degree_pos : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ L : LB C, L.IsLB → 0 < interNum k (GlobalTheory.structureModule C) ![L] → ∃ (m : ℕ) (σ : (lbPow L m).Sec) (c : C), 0 < m ∧ σ ≠ 0 ∧ c ∉ Out.nonzeroLocus σ := by
  first | exact @GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos | exact GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos | (intros; apply GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEndomorphismOfConjugateAdjointForm
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

namespace GlobalTheory.GramAdj

theorem exists_endo_of_adjoint :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (β : D.La → D.La → ℤ), (∀ x y z, β (x + y) z = β x z + β y z) → (∀ x y z, β x (y + z) = β x y + β x z) → (∀ (s : 𝓞 E) x y, β (s • x) y = β x (H.bar s • y)) → ∃ γ : D.La →+ D.La, (∀ (s : 𝓞 E) x, γ (s • x) = s • γ x) ∧ ∀ x y, β x y = D.EF (γ x) y := by
  intro E _ _ _ H D β hl hr hs
  let f : D.La → (D.La →ₗ[ℤ] ℤ) := fun x => (AddMonoidHom.mk' (β x) (hr x)).toIntLinearMap
  have hf : ∀ x y, f x y = β x y := fun _ _ => rfl
  let e := Equiv.ofBijective D.EF D.unimod
  have he : ∀ g, D.EF (e.symm g) = g := fun g => e.apply_symm_apply g
  have key : ∀ x y, D.EF (e.symm (f x)) y = β x y := fun x y => by rw [he, hf]
  have hadd : ∀ x x', e.symm (f (x + x')) = e.symm (f x) + e.symm (f x') := by
    intro x x'
    apply D.unimod.1
    ext y
    simp only [map_add, LinearMap.add_apply, key, hl]
  refine ⟨AddMonoidHom.mk' (fun x => e.symm (f x)) hadd, ?_, ?_⟩
  · intro s x
    show e.symm (f (s • x)) = s • e.symm (f x)
    apply D.unimod.1
    ext y
    rw [key, hs, ← key, D.adj]
  · intro x y
    show β x y = D.EF (e.symm (f x)) y
    rw [key]

end GlobalTheory.GramAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransformStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lintegral_sq_eq_mul_setLIntegral_thetaTransform : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ 𝓕 : Set ((κ → AF F) × (κ → AF F)),
      @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
      ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
        ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta | exact GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta | (intros; apply GlobalTheory.ThetaParseval.exists_lintegral_sq_eq_mul_setLIntegral_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatHeckeCharacterTrivialCongruentUnitsStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_heckeCharacter_trivial_congruent_units : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles L, a ∈ GlobalTheory.Mem.Chr.unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((a : AdeleRing (𝓞 L) L).2 P - 1) ≤ Valued.v ((M : L) : P.adicCompletion L)) → χ.1 a = 1 := by
  first | exact @GlobalTheory.Mem.HeckeLevel.exists_level_nat | exact GlobalTheory.Mem.HeckeLevel.exists_level_nat | (intros; apply GlobalTheory.Mem.HeckeLevel.exists_level_nat <;> assumption)
end

