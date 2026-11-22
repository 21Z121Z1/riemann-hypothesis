import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsFieldIntersectionNoBlockFam
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherBis
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

def IntersectionWithSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (A : HermLine ι) (A' : HermLine ι') (s : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → IsSmoothHerm A → IsPullHerm κ v A A' →
    IsSectionOn (imageZ v P') A s →
    ptsIntegral P' (pot L') (logNorm A' (rename v s)) =
      (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * ptsIntegral (imageZ v P') (pot L) (logNorm A s)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalPrime.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (p : ℤ) (y : funField P),
    IsArithVar P 1 → Prime p →
    (∀ W, IsClosedPt W → P ≤ W → C p ∈ W → (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P W) →
    ∃ n : ℤ, ¬ p ∣ n ∧ (n : funField P) * y ∈ regRing P

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (b : regRing P),
    IsArithVar P 1 → b ≠ 0 →
    {W | IsClosedPt W ∧ P ≤ W ∧
        Nat.card (locRing P W ⧸ locIdeal P W ((b : funField P) : FractionRing (MRing ι ⧸ P))) ≠ 1}.Finite ∧
      ∑ᶠ W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W},
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W ((b : funField P) : FractionRing (MRing ι ⧸ P)))) =
        Real.log (Nat.card (regRing P ⧸ Ideal.span {b}))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityMaximalSurjective.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ m : Ideal (regRing P), m.IsMaximal →
    ∃ W : Ideal (MRing ι), IsClosedPt W ∧ P ≤ W ∧ ∀ x ∈ m, ∀ z ∈ locRing P W,
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z ≠ 1

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityMaximalSpectrum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∃ e : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} ≃ MaximalSpectrum (regRing P),
      ∀ (W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}) (y : FractionRing (MRing ι ⧸ P)),
        y ∈ locRing P W.1 ↔ ∃ x s : regRing P, s ∉ (e W).asIdeal ∧
          y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ x : regRing P, IsIntegral ℤ ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PushforwardArithIntersection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

open Classical in

def blkW : (Σ k, ι k) → K → ℕ := fun p => Pi.single p.1 1

open Classical in

theorem isMultiHomog_of_wh {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    IsMultiHomog s a := by
  intro m hm k
  rw [← h (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, Ne.symm hb]
  · simp

omit [Fintype K] in
open Classical in

theorem sum_single_eq_extend {K₀ : Type} [Fintype K₀] (κ : K₀ → K) (hκ : Function.Injective κ) (α : K₀ → ℕ) :
    (∑ k, α k • (Pi.single (κ k) 1 : K → ℕ)) = Function.extend κ α 0 := by
  funext k'
  rw [Finset.sum_apply]
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hκ.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hκ.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : k' ≠ κ k := fun e => h ⟨k, e.symm⟩
    simp [hk]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem wh_prod_X_pow {K₀ : Type} [Fintype K₀] (q : K₀ → Σ k, ι k) (α : K₀ → ℕ) :
    IsWeightedHomogeneous (blkW (ι := ι)) (∏ k, (X (q k) : MRing ι) ^ α k) (∑ k, α k • blkW (q k)) :=
  IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℤ _ (q k)).pow (α k)

theorem isMultiHomog_coordPow (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by
  have h := wh_prod_X_pow (ι := ι) (fun k => ⟨k, i k⟩) α
  have e : (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) = α := by
    funext k
    simp only [blkW, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [e] at h
  exact isMultiHomog_of_wh h

omit [∀ k, Fintype (ι k)] in

theorem isMultiHomog_rename_coordPow {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)) (Function.extend κ α 0) := by
  have h := wh_prod_X_pow (ι := ι') (fun k => v ⟨k, i k⟩) α
  have e : (∑ k, α k • blkW (ι := ι') (v ⟨k, i k⟩)) = Function.extend κ α 0 := by
    simp only [blkW, hv.2.2.1]
    exact sum_single_eq_extend κ hv.1 α
  rw [e] at h
  simp only [map_prod, map_pow, rename_X]
  exact isMultiHomog_of_wh h

omit [∀ k, Fintype (ι k)] in

theorem coordPow_not_mem {V : Ideal (MRing ι)} (hV : V.IsPrime) (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ V) (α : K → ℕ) : (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) ∉ V := by
  intro h
  obtain ⟨k, -, hk⟩ := (hV.prod_mem_iff).mp h
  exact hi k (hV.mem_of_pow_mem _ hk)

theorem isSmoothHerm_pull {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem genDegAt_zero (h0 : ArithVarZeroStatement) (I : AllFam) : GenDegAt I 0 := by
  intro K _ ι _ K' _ ι' _ κ v P' G J L L' _ hP'
  exact absurd hP' (h0 K' ι' P')

theorem genDegAt_succ (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement)
    (I : AllFam) (hI : I.IsFamily) (n : ℕ) (ih : GenDegAt I n) : GenDegAt I (n + 1) := by
  intro K _ ι _ K' _ ι' _ κ v P' G J L L' hv hP' hP hJ hL hLL'
  have hrel := hP.2.1.2.2
  choose i hi using hrel
  have hPp : (imageZ v P').IsPrime := hP.2.1.1
  let α : K → ℕ := fun k => ((L (Fin.last n)).a k).toNat
  let β : K → ℕ := fun k => (-(L (Fin.last n)).a k).toNat
  have hfP := coordPow_not_mem hPp i hi α
  have hgP := coordPow_not_mem hPp i hi β
  have hfP' : rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) ∉ P' := fun h => hfP (Ideal.mem_comap.mpr h)
  have hgP' : rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k) ∉ P' := fun h => hgP (Ideal.mem_comap.mpr h)
  have hsec : IsRatSectionOn (imageZ v P') (L (Fin.last n)) (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)
      (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k) :=
    ⟨α, β, isMultiHomog_coordPow i α, isMultiHomog_coordPow i β, hfP, hgP,
      fun k => Int.toNat_sub_toNat_neg _⟩
  have hsec' : IsRatSectionOn P' (L' (Fin.last n)) (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k))
      (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k)) := by
    refine ⟨_, _, isMultiHomog_rename_coordPow hv i α, isMultiHomog_rename_coordPow hv i β, hfP', hgP',
      fun k' => ?_⟩
    rw [(hLL' (Fin.last n)).1, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hv.1.extend_apply]
      exact Int.toNat_sub_toNat_neg _
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => isSmoothHerm_pull hv (hL j) (hLL' j)
  have e1 := hRat K' ι' (I K' ι') (hI K' ι') P' n (Fin.init L') (L' (Fin.last n)) _ _ hP'
    (fun j => hL' _) (hL' _) hsec'
  have e2 := hRat K ι (I K ι) (hI K ι) (imageZ v P') n (Fin.init L) (L (Fin.last n)) _ _ hP
    (fun j => hL _) (hL _) hsec
  rw [Fin.snoc_init_self] at e1 e2
  rw [e1, e2, recRRat, recRRat,
    hCyc I hI n ih K ι K' ι' κ v P' G J (Fin.init L) (Fin.init L') _ α hv hP' hP hJ (fun j => hL _)
      (fun j => hLL' _) (isMultiHomog_coordPow i α) hfP,
    hCyc I hI n ih K ι K' ι' κ v P' G J (Fin.init L) (Fin.init L') _ β hv hP' hP hJ (fun j => hL _)
      (fun j => hLL' _) (isMultiHomog_coordPow i β) hgP,
    hInt K ι K' ι' κ v P' n G J (Fin.init L) (Fin.init L') (L (Fin.last n)) (L' (Fin.last n)) _ _ hv hP' hP
      hJ (fun j => hL _) (fun j => hLL' _) (hL _) (hLL' _) hsec]
  ring

end PushforwardArithIntersection

theorem PushforwardArithIntersection.proof (h0 : ArithVarZeroStatement) (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement)
    (hInt : ArithmeticIntersectionIntegral.Statement) : PushforwardArithIntersection.Statement := by
  unfold PushforwardArithIntersection.Statement GenDegStatement
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G J L L' hv hP' hP hJ hL hLL'
  have key : ∀ n, GenDegAt I n := fun n =>
    Nat.rec (PushforwardArithIntersection.genDegAt_zero h0 I) (fun n ih => PushforwardArithIntersection.genDegAt_succ hRat hCyc hInt I hI n ih) n
  exact key d K ι K' ι' κ v P' G J L L' hv hP' hP hJ hL hLL'

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsPrimeSpanXb
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def GenericPointExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')),
    W'.IsPrime → Nonempty (GenFibre v W')

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem imageZ_id (W : Ideal (MRing ι)) : imageZ (ι := ι) (ι' := ι) id W = W := by
  ext f
  simp [imageZ, rename_id]

def genFibreIdOf (W : Ideal (MRing ι)) [W.IsPrime] : GenFibre (ι := ι) (ι' := ι) id W where
  Φ := FnField W
  Φ' := FnField W
  x := genPt W
  x' := genPt W
  ker_x := by
    rw [imageZ_id]
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ W) c
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨f, g, ?_, ?_⟩
    · rw [aeval_genPt]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    · rw [aeval_genPt, aeval_genPt]
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, aeval_genPt]
    exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W) f
  compat _ := rfl

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermOfIsPullHermInl
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

section Patch

abbrev Amb : Type 1 := Σ (K : Type) (_ : Fintype K) (ι : K → Type), ∀ k, Fintype (ι k)

abbrev AmbFam (a : Amb) : Type :=
  letI := a.2.1; letI := a.2.2.2
  Ideal (MRing a.2.2.1) → (n : ℕ) → (Fin n → HermLine a.2.2.1) → ℝ

def AmbIsFam (a : Amb) (F : AmbFam a) : Prop :=
  letI := a.2.1; letI := a.2.2.2
  IsIntersectionFamily (ι := a.2.2.1) F

open Classical in

def patchFam (J : AllFam) (a : Amb) (F : AmbFam a) : AllFam :=
  fun K _ ι _ => if h : (⟨K, ‹_›, ι, ‹_›⟩ : Amb) = a then cast (congrArg AmbFam h.symm) F else J K ι

end Patch

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem imageZ_projBundleIdeal (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    imageZ (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B) = P := by
  have key : (projBundleMap P B).comp
      (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom =
      (C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp
        ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · have hC := RingHom.ext_int
        (((projBundleMap P B).comp
          (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom).comp C)
        (((C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp
          ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P))).comp C)
      exact RingHom.congr_fun hC r
    · obtain ⟨k, i⟩ := p
      simp [projBundleMap, inlV, genPt]
  ext f
  change projBundleMap P B ((rename (inlV (ι₂ := fun _ : Unit => Fin N1)) :
      MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom f) = 0 ↔ f ∈ P
  rw [← RingHom.comp_apply, key, RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.C_eq_zero,
    map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

end Lemmas

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.MultAtPosOfMemDivSupp
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem multAt_pos_of_mem_divSupp {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp P s) : 0 < multAt (P ⊔ Ideal.span {s}) W := by
  have hmin := hW.1
  have hWp : W.IsPrime := hmin.1.1
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      ((P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W)]
    rw [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hmin
  have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
  have : Nontrivial (Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
  have hpos := Module.length_pos (R := Localization.AtPrime W)
    (M := Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W)))
  rw [multAt, dif_pos hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
  exact ENat.toNat_pos hpos.ne' hne

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem pfAt_zero (hAI3 : PushforwardArithIntersection.Statement) (I : AllFam) (hI : I.IsFamily) : PFAt I 0 := by
  intro K _ ι _ K' _ ι' _ κ v P' d G J L L' N hv hP' hP hJ hL hL' _
  have hN : (fun j => fibreDeg κ (N j).a) = (Fin.elim0 : Fin 0 → FibreBlock κ → ℤ) :=
    funext fun j => j.elim0
  have hA : Fin.append L' N = L' := funext fun j => by
    rw [Fin.append_right_nil L' N rfl]
    rfl
  rw [hN, hA]
  exact hAI3 I hI K ι K' ι' κ v P' d G J L L' hv hP' hP hJ hL hL'

theorem PushforwardProjLineFlag.proof (hAI3 : PushforwardArithIntersection.Statement) (hStep : PFStep.Statement) : PushforwardProjLineFlag.Statement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d r
  have key : ∀ r, PFAt I r := fun r =>
    Nat.rec (pfAt_zero hAI3 I hI) (fun r h => hStep I hI r h) r
  exact key r K ι K' ι' κ v P' d

end GroundTheory.Heights₂.Heights.Inter
end

