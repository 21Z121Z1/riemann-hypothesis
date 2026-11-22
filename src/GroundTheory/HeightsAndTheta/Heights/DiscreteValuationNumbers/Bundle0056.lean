import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionKoszul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section ClassNumPairDiff

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_pairDiff_mul {n e : ℕ} {W : Ideal (MRing ι O)}
    (hadd : ∀ (a₁ a₂ : K → ℤ) (l : List (K → ℤ)), e ≤ l.length →
      vNumL W ((a₁ + a₂) :: l) = vNumL W (a₁ :: l) + vNumL W (a₂ :: l))
    (z z' : Fin n → K → ℤ) (j : Fin n) {H : MvPolynomial (Fin n ⊕ Fin n) ℤ} {t : ℕ}
    (hH : H.IsHomogeneous t) (Q : List (K → ℤ)) (ht : e ≤ t + Q.length) :
    classNum (Sum.elim z z') (pairDiff j * H) Q W =
      ∑ μ ∈ H.support,
        H.coeff μ * vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)) := by
  have hsub : classNum (Sum.elim z z') (pairDiff j * H) Q W =
      classNum (Sum.elim z z') (X (Sum.inl j) * H) Q W -
        classNum (Sum.elim z z') (X (Sum.inr j) * H) Q W := by
    rw [pairDiff, sub_mul]
    exact map_sub (classNumAddHom (Sum.elim z z') Q W) _ _
  rw [hsub, classNum_X_mul, classNum_X_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hlen : e ≤ (classList (Sum.elim z z') μ ++ Q).length := by
    rw [List.length_append, classList_length_of_mem_support _ hH hμ]
    exact ht
  have h := hadd (z j - z' j) (z' j) _ hlen
  rw [sub_add_cancel] at h
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [h]
  ring

end ClassNumPairDiff

theorem cycEval_vNumL_comm (hC2 : VerticalDivisorsCommute.Statement.{0}) {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (l : List (K → ℤ))
    (hP : IsModelOver P (l.length + 1)) {b b' : K → ℤ} {f g f' g' : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (hD' : IsVerticalDivisor P ϖ b' f' g') :
    cycEval (fun W => vNumL W (b' :: l)) (ratDiv P f g) =
      cycEval (fun W => vNumL W (b :: l)) (ratDiv P f' g') := by
  have h := hC2 O ϖ hϖ K ι P l.length hP b b' f g f' g' hD hD' l.get
  simp only [vNum_vecCons_eq, List.ofFn_get] at h
  exact h

theorem PairNumberExpansionIndependence.proof (hC2 : VerticalDivisorsCommute.Statement.{0}) :
    PairNumberExpansionIndependence.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP n z z' f g hD m A hA As Bs hAs hBs Q hQ
  have hrel : ∑ i, pairDiff i * (As - Bs) i = 0 := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, pairDiff, ← hAs.expansion,
      ← hBs.expansion, sub_self]
  obtain ⟨Kz, hKa, hKh, hK0, hKs⟩ := koszul_homogeneous (m := m) (As - Bs)
    (fun i => (hAs.homogeneous i).sub (hBs.homogeneous i)) hrel
  rw [← sub_eq_zero, ← pairNumHom_apply, ← pairNumHom_apply, ← map_sub]
  by_cases hm : m - 1 = 0
  · have h0 : As - Bs = 0 := funext fun i => by
      rw [hKs i]
      simp [hK0 hm]
    rw [h0, map_zero]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hlen : ∀ i j μ, μ ∈ (Kz i j).support → (classList (Sum.elim z z') μ ++ Q).length = e := by
    intro i j μ hμ
    rw [List.length_append, classList_length_of_mem_support _ (hKh i j) hμ]
    omega

  let V : Fin n → Fin n → (Fin n ⊕ Fin n →₀ ℕ) → ℤ := fun i j μ =>
    cycEval (fun W => vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)))
      (ratDiv P (f i) (g i))
  let F : Fin n → Fin n → ℤ := fun i j => ∑ μ ∈ (Kz i j).support, (Kz i j).coeff μ * V i j μ
  have hexp : pairNumHom P z z' f g Q (As - Bs) = ∑ i, ∑ j, F i j := by
    rw [pairNumHom_apply]
    unfold pairNum
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfin := ratDiv_finite_support P (f i) (g i)
    have hW : ∀ W ∈ hfin.toFinset, classNum (Sum.elim z z') ((As - Bs) i) Q W =
        ∑ j, ∑ μ ∈ (Kz i j).support,
          (Kz i j).coeff μ * vNumL W ((z j - z' j) :: (classList (Sum.elim z z') μ ++ Q)) := by
      intro W hWm
      rw [Set.Finite.mem_toFinset, Function.mem_support] at hWm
      rw [hKs i]
      have h := map_sum (classNumAddHom (Sum.elim z z') Q W) (fun j => pairDiff j * Kz i j)
        Finset.univ
      simp only [classNumAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact classNum_pairDiff_mul (vNumL_add_of_ratDiv_ne_zero hϖ hP (hD i) hWm) z z' j (hKh i j) Q
        (by omega)
    simp only [F, V, cycEval_eq_sum hfin]
    rw [Finset.sum_congr rfl
      (fun W hW' => congrArg (ratDiv P (f i) (g i) W * ·) (hW W hW'))]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
    ring
  have hF : ∀ i j, F j i = -F i j := by
    intro i j
    simp only [F]
    rw [hKa j i, support_neg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hP' : IsModelOver P ((classList (Sum.elim z z') μ ++ Q).length + 1) := by
      rw [hlen i j μ hμ]
      exact hP
    have hc := cycEval_vNumL_comm hC2 hϖ _ hP' (hD i) (hD j)
    simp only [V, coeff_neg]
    rw [hc]
    ring
  rw [hexp]
  have hS : ∑ i, ∑ j, F i j = -∑ i, ∑ j, F i j := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hF i j
  linarith

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagClosureModel

theorem exists_flag_ne_zero {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (w e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∃ l, ∑ j, flagCoord w e t k j * algebraMap Ω Φ (ψ l (w j)) ≠ 0 := by
  have hN : 0 < N := by omega
  by_contra! h0

  let θ : Fin P → Module.Dual Ω E := fun l =>
    ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) • w.coord j
  have hθe : ∀ l i, θ l (e i) = ∑ j : Fin N, (if (j : ℕ) < k then ψ l (w j) else 0) * w.repr (e i) j := by
    intro l i
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  have hθ : ∀ l, θ l = 0 := by
    intro l
    refine e.ext fun i => ?_
    have key := Fintype.linearIndependent_iff.1 ht (fun i => θ l (e i)) (by
      rw [← h0 l]
      simp only [hθe, Algebra.smul_def, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [flagCoord]
      split_ifs
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
      · simp)
    simpa using key i
  have hw0 : ∀ l, ψ l (w ⟨0, hN⟩) = 0 := by
    intro l
    have h := congrArg (fun f : Module.Dual Ω E => f (w ⟨0, hN⟩)) (hθ l)
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, LinearMap.zero_apply] at h
    rw [Finset.sum_eq_single ⟨0, hN⟩ (fun j _ hj => by simp [Ne.symm hj])
      (by simp)] at h
    simpa [show (0 : ℕ) < k by omega] using h
  have hall : ∀ f ∈ Submodule.span Ω (Set.range ψ), f (w ⟨0, hN⟩) = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hw0 l
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have := hall (w.coord ⟨0, hN⟩) (hψ ▸ Submodule.mem_top)
  simp at this

end SegreFlagClosureModel

open GenericProjClosureDim GenericProjClosureDivisor SegreFlagClosureModel in

theorem SegreFlagClosureModel.proof (hTr : SegreFlagClosureTrdeg.Statement) :
    SegreFlagClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk hkN
  have hpt : flagClosurePt y w e φ φ' t k = pairProjCoord y w φ φ' (flagCoord w e t k) := rfl

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent

  have hz : ∀ o, ∃ i, flagClosurePt y w e φ φ' t k ⟨o, i⟩ ≠ 0 := by
    rintro (_ | _ | k')
    · exact exists_flag_ne_zero w e hli φ'
        (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) hk hkN
    · exact exists_flag_ne_zero w e hli φ
        (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc) hk hkN
    · exact ⟨c k', fun h0 => hc k' ((FaithfulSMul.algebraMap_injective Ω Φ)
        (by simpa [flagClosurePt, pairProjCoord, projCoord] using h0))⟩
  have hP := isMultiProjPrime_pointIdeal (R := O) _ hz

  have hnt : (pointIdeal O (flagClosurePt y w e φ φ' t k)).comap (C : O →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply,
      C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)] at ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy

  have hdy := DvrConeDimTrdeg.proof O K ι (pointIdeal O y) hV.multiProj hV.noTorsion
  rw [hV.dim] at hdy
  have hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) =
        (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      have := WithBot.coe_injective hdy
      rw [← this]
      push_cast
      ring
    exact (Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)
  have hZ : IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t k)) (d + (k - 1)) := by
    refine ⟨hP, hnt, ?_⟩
    rw [DvrConeDimTrdeg.proof _ _ _ _ hP hnt,
      hTr O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN, hty,
      ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option,
      show d + (k - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (k + 1) + 1 by omega]
    norm_cast
  refine ⟨hZ, ?_⟩

  rw [hpt] at hZ ⊢
  have hP' : (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).IsPrime := hZ.multiProj.isPrime
  have hϖP : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉
      pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k)) := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k))).comap
        (C : O →+* MRing (bundleIdx (bundleIdx ι M) M') O) := hm
    rw [hZ.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  have pairs := pairs_at TwistedDualGensExpress.proof y B B' hB a₀ a₀' φ φ' hφ hφ' w (flagCoord w e t k)
  obtain ⟨⟨f₀, g₀, hp₀, hg₀⟩, -⟩ := pairs _ hP' le_rfl hZ.multiProj.relevant hϖP
  have hf₀ : f₀ ∉ pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t k)) := by
    intro hm
    obtain ⟨⟨bf, bg, -, hg, -⟩, hv⟩ := hp₀
    exact hg₀ (mem_of_homog hg (by rw [← hv]; exact aeval_eq_zero_of_mem hm))
  refine ⟨f₀, g₀, IsVerticalDivisor.of_unit_off_special hp₀.1 hf₀ hg₀ ?_, hp₀.2⟩
  intro W hW hPW hWr hϖW
  obtain ⟨⟨f₁, g₁, hp₁, hg₁⟩, ⟨f₂, g₂, hp₂, hf₂⟩⟩ := pairs W hW hPW hWr hϖW
  have h12 := hPW (hp₁.cross hp₂)
  refine ⟨g₁, f₁, hg₁, fun hf₁ => ?_, ?_⟩
  · have h' : f₁ * g₂ - (f₁ * g₂ - f₂ * g₁) ∈ W := W.sub_mem (W.mul_mem_right _ hf₁) h12
    rw [sub_sub_cancel] at h'
    rcases hW.mem_or_mem h' with h | h
    · exact hf₂ h
    · exact hg₁ h
  · rw [show g₁ * f₀ - f₁ * g₀ = f₀ * g₁ - f₁ * g₀ by ring]
    exact hp₀.cross hp₁

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinCkOnFlagPair
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

namespace ChernClassOnFlagPair

theorem fieldNum_spec (F : Type) [Field F] {K : Type} [Fintype K] (κ : K → Type) [∀ k, Fintype (κ k)] :
    IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : IFamily F κ => IsFieldIntersection I)
    ⟨_, IntNumIsFieldIntersection.full F K κ⟩

theorem append_pullDeg {K K' : Type} {a b : ℕ} (u : Fin a → K → ℤ) (v : Fin b → K → ℤ) :
    Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (u i))
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (v j)) =
      fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (Fin.append u v l) := by
  funext l
  induction l using Fin.addCases with
  | left i => simp
  | right j => simp

theorem isVertDiv_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    (b : K → ℤ) (hb : b = 0) : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b 1 1 := by
  subst hb
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι O) 0 := by
    simpa using IndefiniteRowSideFullHecke.NumbersDVR.Bundles.isMultiHomog_C O (ι := ι) (1 : O)
  refine ⟨⟨0, 0, h1, h1, by simp⟩, ?_, ?_, fun Q hQ _ _ => ⟨1, 1, ⟨0, h1⟩, ⟨0, h1⟩, ?_, ?_, by simp⟩⟩
  · exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  · exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)

theorem length_classList {K σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) :
    (classList cls μ).length = μ.degree := by
  simp [classList, Finsupp.card_toMultiset, Finsupp.sum]
  rfl

theorem isFlagPair_self {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {y : (Σ k, ι k) → Ω} [(pointIdeal O y).IsPrime] {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
    {B : ChartBundle O (segreVec y) N E} {w : Module.Basis (Fin N) Ω E} {x : Fin N → K → ℤ}
    (h : IsFlagFrame y B w x) :
    IsFlagPair ϖ y B B w w x x (fun _ => 1) (fun _ => 1) where
  flag := h
  flag' := h
  sameFlag i j hij := by rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg hij.ne]
  vertical i := by
    rw [sub_self]
    exact isVerticalDivisor_one ϖ _
  generic i := by simp [Module.Basis.repr_self]

end ChernClassOnFlagPair

open ChernClassOnFlagPair in

theorem ChernClassOnFlagPair.proof (h1 : JoinPointFlagModel.Statement)
    (h2 : JoinPointNumbers.Statement) (h3 : FlagModelValueIndependence.Statement)
    (h4 : FlagModelRootIndependence.Statement) (h5 : plainPolynomialPairNumber.Statement)
    (h6 : RootPolynomialNumber.Statement) (h7 : PairNumberExpansionIndependence.Statement)
    (h8 : dividedDifferenceExpansion.Statement) : ChernClassOnFlagPair.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hK hW N E _ _ B B' hBB' w w' x x' f g hfp
  have hW2 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) d :=
    (BundleExamples.isModelOver_iff O _ d).mpr ⟨hK, hW⟩
  have hprime : (pointIdeal O y).IsPrime := hW2.2.1.1
  refine ⟨fun k hk1 hk2 Gs hGs q L Q hQ => ?_, fun c G hsym hG hc q L Q hQ a ha => ?_⟩
  · obtain ⟨EB, E'B, φ, hm, hb, hp, hp', hd, hd', hf, hg⟩ :=
      h1 O ϖ hϖ Ω K ι y d hW N E B B' hBB' w w' x x' f g hfp
    let F₀ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B' :=
      { K' := Unit, ι' := ptIdx, z := ptCoord, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B') := ⟨F₀⟩
    have hv : F₀.value O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
        (psum (Fin N) ℤ k) L L (fun _ => 1) (fun _ => 1) Q =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (rename (Fin.castAdd q) (psum (Fin N) ℤ k) * rename (Fin.natAdd N) Q) := by
      show IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O _ _ d (Fin.append φ.deg _) (Fin.append φ.deg' _)
        (Fin.append φ.f _) (Fin.append φ.g _) _ = _
      rw [hd, hd', hf, hg]
    have hW' : ∀ H : MvPolynomial (Fin (N + q)) ℤ, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1) H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          (pointIdeal O y) d (Fin.append x L) (Fin.append x' L) (Fin.append f fun _ => 1)
          (Fin.append g fun _ => 1) H := by
      intro H
      unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
      simp only [append_pullDeg]
      refine Finset.sum_congr rfl fun l _ => ?_
      induction l using Fin.addCases with
      | left i =>
        simp only [Fin.append_left]
        exact (h2 O ϖ hϖ Ω K ι y d hW _ _ _).1 _ _ _ (hfp.vertical i)
      | right j =>
        simp only [Fin.append_right, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, sub_self,
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval, Finsupp.sum_zero_index]
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ck
    rw [dif_pos hne]
    let _ := (Classical.choice hne).finK
    let _ := (Classical.choice hne).finι
    refine (h3 O Ω K ι y d N E B B' hW2 ((BundleExamples.sameGeneric_iff hϖ y B B').mpr hBB')
      (Classical.choice hne) F₀ _ _ (fieldNum_spec _ _) (fieldNum_spec _ _) (psum (Fin N) ℤ k)
      (psum_isSymmetric _ _ k) q L L (fun _ => 1) (fun _ => 1)
      (fun l => isVertDiv_one hprime _ (sub_self _)) k Q hk2 (isHomogeneous_psum N k) hQ).trans ?_
    refine hv.trans ((hW' _).trans ((h5 O K ι (pointIdeal O y) d N x x' f g k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) hk2 q L Q hQ).trans ?_))
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hlen : (classList L μ).length + k = d + 1 := by
      have h := hQ (mem_support_iff.mp hμ)
      rw [length_classList, Finsupp.degree_eq_weight_one]
      have : Finsupp.weight (fun _ => 1) μ = Finsupp.weight 1 μ := rfl
      omega
    rw [h7 O ϖ hϖ K ι (pointIdeal O y) d hW N x x' f g hfp.vertical k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) _ Gs (h8 N k _ (isHomogeneous_psum N k)) hGs (classList L μ) hlen]
  · have hsame : SameGenericFibre ϖ B B := fun c _ =>
      ⟨fun v hv => ⟨0, by simpa using hv⟩, fun v hv => ⟨0, by simpa using hv⟩⟩
    obtain ⟨EB, E'B, φ, hm, hb, hp, hp', hd, -, -, -⟩ :=
      h1 O ϖ hϖ Ω K ι y d hW N E B B hsame w w x x _ _ (isFlagPair_self hfp.flag)
    let F₀ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B :=
      { K' := Unit, ι' := ptIdx, z := ptCoord, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B) := ⟨F₀⟩
    have hv : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι F₀.ι')) W d
          (Fin.append F₀.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₀.K') (L l))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y F₀.z)) (C a))) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) W d
          (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (Fin.append x L j))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (C a))) := by
      show IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum _ W d
          (Fin.append φ.deg _) _) _ = _
      rw [hd, append_pullDeg]
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.rootNum
    rw [dif_pos hne]
    let _ := (Classical.choice hne).finK
    let _ := (Classical.choice hne).finι
    refine (h4 O Ω K ι y d N E B B hW2 ((BundleExamples.sameGeneric_iff hϖ y B B).mpr hsame)
      (Classical.choice hne) F₀ _ _ (fieldNum_spec _ _) (fieldNum_spec _ _) c G hsym hG hc q L Q hQ a
      ha).trans ?_
    refine hv.trans (((h2 O ϖ hϖ Ω K ι y d hW _ _ _).2 a ha).trans ?_)
    exact h6 O K ι (pointIdeal O y) d N x c G hG hc q L Q hQ a

end GroundTheory.Heights₂.Heights.NumbersDVR
end

