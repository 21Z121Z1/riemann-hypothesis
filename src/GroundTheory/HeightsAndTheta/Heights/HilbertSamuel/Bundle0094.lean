import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0085
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace H1VanishingDevissage

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem cechHc_subsingleton_iff (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι 𝓜 c n) ↔ KH.cechZc ι 𝓜 c n ≤ KH.cechBc ι 𝓜 c n := by
  show Subsingleton (_ ⧸ _) ↔ _
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

theorem locPart_shift (𝓜 : (K → ℤ) → Submodule S M) (T : Submonoid (MRingOver S ι)) (c x : K → ℤ) :
    KH.locPart ι (fun d => 𝓜 (d + c)) T x = KH.locPart ι 𝓜 T (x + c) := by
  have h : ∀ a : K → ℕ, x + (fun k => (a k : ℤ)) + c = x + c + fun k => (a k : ℤ) :=
    fun _ => add_right_comm _ _ _
  simp only [KH.locPart, h]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

theorem cechCc_shift (𝓜 : (K → ℤ) → Submodule S M) (c x : K → ℤ) (n : ℕ) :
    KH.cechCc ι (fun d => 𝓜 (d + c)) x n = KH.cechCc ι 𝓜 (x + c) n := by
  simp only [KH.cechCc, locPart_shift]

theorem cechHc_shift_iff (𝓜 : (K → ℤ) → Submodule S M) (c x : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι (fun d => 𝓜 (d + c)) x n) ↔ Subsingleton (KH.cechHc ι 𝓜 (x + c) n) := by
  rw [cechHc_subsingleton_iff, cechHc_subsingleton_iff]
  cases n <;> simp only [KH.cechZc, KH.cechBc, cechCc_shift]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

theorem isMGraded_shift {𝓜 : (K → ℤ) → Submodule S M} (h : KH.IsMGraded S ι 𝓜) (c : K → ℤ) :
    KH.IsMGraded S ι (fun d => 𝓜 (d + c)) := by
  refine ⟨?_, fun a d p m hp hm => ?_⟩
  · have h1 := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top 𝓜).1 h.1
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
      ⟨h1.1.comp (add_left_injective c), ?_⟩
    rw [← h1.2]
    exact (Equiv.addRight c).iSup_comp (g := 𝓜)
  · have := h.2 a (d + c) p m hp hm
    rwa [add_right_comm] at this

theorem cechHc_subsingleton_of_bij (hSES : KH.CechSESStatement)
    {A B : Type} [AddCommGroup A] [Module (MRingOver S ι) A] [Module S A] [IsScalarTower S (MRingOver S ι) A]
    [AddCommGroup B] [Module (MRingOver S ι) B] [Module S B] [IsScalarTower S (MRingOver S ι) B]
    (𝓐 : (K → ℤ) → Submodule S A) (𝓑 : (K → ℤ) → Submodule S B) (g : A →ₗ[MRingOver S ι] B)
    (hA : KH.IsMGraded S ι 𝓐) (hB : KH.IsMGraded S ι 𝓑) (hg : KH.IsMGradedMap S ι 𝓐 𝓑 g)
    (hinj : Function.Injective g) (hsurj : Function.Surjective g) (c : K → ℤ) (n : ℕ)
    (h : Subsingleton (KH.cechHc ι 𝓐 c n)) : Subsingleton (KH.cechHc ι 𝓑 c n) := by
  have hhG : KH.IsMGradedMap S ι 𝓑 (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) 0 :=
    fun _ _ _ => Submodule.zero_mem _
  have hex : LinearMap.range g = LinearMap.ker (0 : B →ₗ[MRingOver S ι] PUnit) := by
    rw [LinearMap.range_eq_top.2 hsurj, LinearMap.ker_zero]
  have hU' : Subsingleton (KH.cechHc ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) c n) := by
    have : Subsingleton (KH.CechC S ι PUnit n) :=
      ⟨fun f g => funext fun I => Subsingleton.elim (α := LocalizedModule _ PUnit) _ _⟩
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]
  exact (hSES S K ι A B PUnit 𝓐 𝓑 _ g 0 hA hB isMGraded_punit hg hhG hinj
    (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex c n).1 h hU'

end H1VanishingDevissage

theorem H1VanishingDevissage.proof (hPF : KH.PrimeFiltStatement) (hSES : KH.CechSESStatement)
    (hGQ : GradedSubquot.Statement) : H1VanishingDevissage.Statement := by
  intro S _ K _ _ ι _ _ V N hS hP M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩ := hPF S K ι M 𝓜 hS hfin hgr
  let G : ℕ → Set M := fun j => m '' {l | (l : ℕ) < j}
  let F : ℕ → Submodule (MRingOver S ι) M := fun j => Submodule.span _ (G j)
  have hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c' := by
    rintro j _ ⟨l, -, rfl⟩
    exact ⟨c l, hm l⟩
  have hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)
  have hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j)) := fun j =>
    (hGQ S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1
  have key : ∀ j ≤ r, ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      Subsingleton (KH.cechHc ι (subGrading 𝓜 (F j)) (e + n • N) 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hF0 : F 0 = ⊥ := by simp [F, G]
      refine ⟨0, fun n _ => (h1_vanish_generated_of_localized_subsingleton
        (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun y => ?_) _ _).1⟩
      rw [one_smul]
      have hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M) := by
        rw [← hF0]
        exact y.2
      exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot _).1 hy)
    | succ j ih =>
      intro hj
      obtain ⟨c₀, hc₀⟩ := ih (Nat.le_of_succ_le hj)
      let l : Fin r := ⟨j, hj⟩
      let L : Submodule (MRingOver S ι) (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hq := (hGQ S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1)) (hFmono (Nat.le_succ j))).2
      have hml : m l ∈ F (j + 1) := Submodule.subset_span ⟨l, Nat.lt_succ_self j, rfl⟩

      let ψ : MRingOver S ι →ₗ[MRingOver S ι] (F (j + 1) ⧸ L) :=
        LinearMap.toSpanSingleton _ _ (L.mkQ ⟨m l, hml⟩)
      have hψ : ∀ p, ψ p = L.mkQ (p • ⟨m l, hml⟩) := fun p => (L.mkQ.map_smul p _).symm
      have hker : ∀ p, ψ p = 0 ↔ p ∈ 𝔭 l := by
        intro p
        rw [hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hcol l p
      let φ : (MRingOver S ι ⧸ 𝔭 l) →ₗ[MRingOver S ι] (F (j + 1) ⧸ L) :=
        (𝔭 l).liftQ ψ fun p hp => (LinearMap.mem_ker).2 ((hker p).2 hp)
      have hφ : ∀ p, φ (Ideal.Quotient.mk (𝔭 l) p) = ψ p := fun _ => rfl
      have hinj : Function.Injective φ := LinearMap.ker_eq_bot.1
        (Submodule.ker_liftQ_eq_bot _ _ _ fun p hp => (hker p).1 (LinearMap.mem_ker.1 hp))

      have hdec : ∀ y ∈ F (j + 1), ∃ p : MRingOver S ι, y - p • m l ∈ F j := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨l', hl', rfl⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h
          · exact ⟨0, by rw [zero_smul, sub_zero]; exact Submodule.subset_span ⟨l', h, rfl⟩⟩
          · exact ⟨1, by rw [one_smul, show l' = l from Fin.ext h, sub_self]; exact (F j).zero_mem⟩
        | zero => exact ⟨0, by rw [zero_smul, sub_zero]; exact (F j).zero_mem⟩
        | add x y _ _ hx hy =>
          obtain ⟨p, hp⟩ := hx
          obtain ⟨p', hp'⟩ := hy
          refine ⟨p + p', ?_⟩
          have : x + y - (p + p') • m l = (x - p • m l) + (y - p' • m l) := by rw [add_smul]; abel
          rw [this]
          exact (F j).add_mem hp hp'
        | smul a x _ hx =>
          obtain ⟨p, hp⟩ := hx
          refine ⟨a * p, ?_⟩
          rw [mul_smul, ← smul_sub]
          exact (F j).smul_mem a hp
      have hsurj : Function.Surjective φ := by
        intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective L q
        obtain ⟨p, hp⟩ := hdec y y.2
        refine ⟨Ideal.Quotient.mk (𝔭 l) p, ?_⟩
        rw [hφ, hψ, Submodule.mkQ_apply, Submodule.Quotient.eq]
        show ((p • ⟨m l, hml⟩ - y : F (j + 1)) : M) ∈ F j
        rw [Submodule.coe_sub, Submodule.coe_smul, ← neg_sub]
        exact (F j).neg_mem hp
      obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n →
          Subsingleton (KH.cechHc ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) 1) := by
        by_cases hrel : IsMultiProjPrime (𝔭 l)
        ·
          obtain ⟨c₂, hc₂⟩ := hP (𝔭 l) hrel (hV.trans (h𝔭 l).2.2) (e + -c l)
          have hA := isMGraded_shift (QuotPartGraded.proof S K ι (𝔭 l) (h𝔭 l).2.1) (-c l)
          have hG : KH.IsMGradedMap S ι (fun d => KH.quotPart S (𝔭 l) (d + -c l))
              (quotGrading (subGrading 𝓜 (F (j + 1))) L) φ := by
            intro d x hx
            refine (Submodule.span_le (p := (quotGrading (subGrading 𝓜 (F (j + 1))) L d).comap
              (φ.restrictScalars S))).2 ?_ hx
            rintro _ ⟨p, ⟨h0, hp⟩, rfl⟩
            refine ⟨p • ⟨m l, hml⟩, ?_, (hψ p).symm⟩
            have h := hgr.2 _ (c l) p (m l) hp (hm l)
            have hd : c l + (fun k => (((d + -c l) k).toNat : ℤ)) = d := by
              funext k
              have := h0 k
              simp only [Pi.add_apply, Pi.neg_apply] at this ⊢
              rw [Int.toNat_of_nonneg this]
              ring
            rw [hd] at h
            exact h
          refine ⟨c₂, fun n hn => cechHc_subsingleton_of_bij hSES _ _ φ hA hq hG hinj hsurj _ _ ?_⟩
          rw [cechHc_shift_iff, show e + n • N + -c l = e + -c l + n • N by abel]
          exact hc₂ n hn
        · have hirr : ¬ IsRelevant (𝔭 l) := fun h => hrel ⟨(h𝔭 l).1, (h𝔭 l).2.1, h⟩
          simp only [IsRelevant, not_forall, not_exists, not_not] at hirr
          obtain ⟨k, hk⟩ := hirr
          refine ⟨0, fun n _ => (h1_vanish_generated_of_localized_subsingleton (fun _ I => ?_) _ _).1⟩
          obtain ⟨i, hi⟩ := I.2.1 k
          refine loc_subsingleton_of_kill (Submonoid.subset_closure ⟨k, i, hi, rfl⟩) fun y => ?_
          obtain ⟨y, rfl⟩ := hsurj y
          obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [← LinearMap.map_smul, show (X ⟨k, i⟩ : MRingOver S ι) • Ideal.Quotient.mk (𝔭 l) p' =
            Ideal.Quotient.mk (𝔭 l) (X ⟨k, i⟩ * p') from rfl, hφ]
          exact (hker _).2 (Ideal.mul_mem_right _ _ (hk i))
      refine ⟨max c₀ c₂, fun n hn => ?_⟩
      let g := Submodule.inclusion (hFmono (Nat.le_succ j))
      have hex : LinearMap.range g = LinearMap.ker L.mkQ := by
        rw [Submodule.range_inclusion, Submodule.ker_mkQ]
      have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g := fun _ _ hx => hx
      have hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L)
          L.mkQ := fun _ _ hx => Submodule.mem_map_of_mem hx
      exact (hSES S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex (e + n • N) 1).1
        (hc₀ n (le_of_max_le_left hn)) (hc₂ n (le_of_max_le_right hn))
  have hFr : F r = ⊤ := by
    rw [← hspan]
    simp [F, G]
  obtain ⟨c₁, hc₁⟩ := key r le_rfl
  exact ⟨c₁, fun n hn => cechHc_subsingleton_of_bij hSES _ 𝓜 (F r).subtype (hgrF r) hgr (fun _ _ hx => hx)
    (Submodule.injective_subtype _) (fun y => ⟨⟨y, hFr ▸ Submodule.mem_top⟩, rfl⟩) _ _ (hc₁ n hn)⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenerationOfH1Vanishing.proof (hU : ClosedPtGenUniform.Statement) (hC : GenNearCover.Statement) :
    GenerationOfH1Vanishing.Statement := by
  intro S _ K _ _ ι _ _ V N hS hH M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨c₂, hc₂⟩ := hH M 𝓜 hfin hgr hV e
  obtain ⟨c₃, hc₃⟩ := hC S K ι V M 𝓜 (fun c => e + c • N) hS hgr hV
    (fun P hP _ => hU S K ι V N hS hH M 𝓜 hfin hgr hV e P hP)
  exact ⟨max c₂ c₃, fun c hc => ⟨hc₂ c (le_of_max_le_left hc), hc₃ c (le_of_max_le_right hc)⟩⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockChiCovolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Matrix SupBoundCount

noncomputable section

namespace BlockChiCovolume

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem gram_symm (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (k l : Fin r) :
    blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) l k =
      blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) k l := by
  rw [blockGram_eq d n f hf, blockGram_eq d n f hf]
  simp only [pairRe_comm]

theorem quad_nonneg (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (a : Fin r → ℝ) :
    0 ≤ a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) := by
  rw [gram_quad d n f hf]
  have h : ∀ z, 0 ≤ ‖comb f a z‖ ^ 2 / d.A.h z ^ (2 * n) := fun z =>
    div_nonneg (sq_nonneg _) ((even_two_mul n).pow_nonneg _)
  have h1 := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n)) fun x => h _
  have h2 := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n)) fun x => h _
  exact mul_nonneg (by norm_num) (add_nonneg h1 h2)

theorem entry_of_quad {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (hG : ∀ k l, G l k = G k l) (k l : Fin r) :
    G k l = ((Pi.single k 1 + Pi.single l 1) ⬝ᵥ (G *ᵥ (Pi.single k 1 + Pi.single l 1)) -
      Pi.single k 1 ⬝ᵥ (G *ᵥ Pi.single k 1) - Pi.single l 1 ⬝ᵥ (G *ᵥ Pi.single l 1)) / 2 := by
  simp [mulVec_add, dotProduct_add, add_dotProduct, hG l k]
  ring

theorem cast_single_add {r : ℕ} (k l : Fin r) :
    (fun j => (((Pi.single k 1 + Pi.single l 1 : Fin r → ℤ) j : ℤ) : ℝ)) = Pi.single k 1 + Pi.single l 1 := by
  funext j
  simp only [Pi.add_apply, Int.cast_add, Pi.single_apply]
  split_ifs <;> simp

theorem cast_single {r : ℕ} (k : Fin r) :
    (fun j => (((Pi.single k 1 : Fin r → ℤ) j : ℤ) : ℝ)) = Pi.single k 1 := by
  funext j
  simp only [Pi.single_apply]
  split_ifs <;> simp

end BlockChiCovolume

open BlockChiCovolume in

theorem BlockChiCovolume.proof : BlockChiCovolume.Statement := by
  intro D K _ _ ι _ Ω _ _ d n E hE r ψ hψ hnorm _ _
  have hex := exists_isSecBasisM d.y d.k₀ n
  rw [blockChi, dif_pos hex]
  have hb := hex.choose_spec
  generalize hex.choose = p at hb ⊢
  obtain ⟨hbf, hli, hspan⟩ := hb
  choose f hf hfb using hbf
  have hbeq : p.2 = fun j => map (Int.castRingHom ℚ) (f j) := funext hfb
  rw [hbeq] at hli hspan ⊢
  beta_reduce at hli hspan
  obtain ⟨w, hw⟩ : ∃ w : Fin p.1 → Ω, w = fun j => aeval d.y (map (Int.castRingHom ℚ) (f j)) := ⟨_, rfl⟩
  rw [← hw] at hli hspan
  have hEN : E = (Submodule.span ℤ (Set.range w)).toAddSubgroup := hE.trans hspan.symm
  let eN : E ≃+ Submodule.span ℤ (Set.range w) :=
    (AddEquiv.addSubgroupCongr hEN).trans (AddEquiv.refl _)
  let bE : Module.Basis (Fin p.1) ℤ E := (Module.Basis.span hli).map eN.symm.toIntLinearEquiv
  have hrange : LinearMap.range ψ.toIntLinearMap = imageLattice ψ := by
    ext v
    simp [imageLattice]
  let B : Module.Basis (Fin p.1) ℤ (imageLattice ψ) :=
    (bE.map (LinearEquiv.ofInjective ψ.toIntLinearMap hψ)).map (LinearEquiv.ofEq _ _ hrange)
  let ε : Fin p.1 → E := fun j => ⟨w j, hEN ▸ Submodule.subset_span ⟨j, rfl⟩⟩
  have hB : ∀ j, (B j : EuclideanSpace ℝ (Fin r)) = ψ (ε j) := by
    intro j
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.map_apply]
    show ψ (bE j) = ψ (ε j)
    congr 1
    apply Subtype.ext
    rw [Module.Basis.map_apply]
    have h : ((Module.Basis.span hli j : Submodule.span ℤ (Set.range w)) : Ω) = w j :=
      congrArg Subtype.val (Module.Basis.span_apply hli j)
    exact h
  set G := blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) with hG
  have key : ∀ m : Fin p.1 → ℤ,
      ‖ψ (∑ j, m j • ε j)‖ ^ 2 = (fun j => (m j : ℝ)) ⬝ᵥ (G *ᵥ fun j => (m j : ℝ)) := by
    intro m
    rw [hnorm _ (∑ j, m j • f j) (isMultiHomog_zsum f m hf), blockL2Norm_sum_eq_sqrt_gram d n f hf m,
      Real.sq_sqrt (quad_nonneg d n f hf _)]
    simp [ε, hw, aeval_map_int, map_sum]
  have hgram : Matrix.gram ℝ (fun i => (B i : EuclideanSpace ℝ (Fin r))) = G := by
    ext k l
    rw [entry_of_quad G (gram_symm d n f hf) k l, ← cast_single_add, ← cast_single, ← cast_single, ← key, ← key,
      ← key]
    simp only [Matrix.gram, of_apply, hB]
    simp [Pi.single_apply, add_smul, Finset.sum_add_distrib]
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
    ring
  have hdet : 0 ≤ G.det := hgram ▸ (Matrix.posSemidef_gram ℝ _).det_nonneg
  rw [covolume_eq_sqrt_det_gram (imageLattice ψ) B, hgram, Real.log_sqrt hdet]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGraphDeg

theorem isMultiHomog_blockForms {K : Type} [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type}
    (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (q : Σ k, GlobalTheory κ k) :
    IsMultiHomog (blockForms k₀ M q) (blockDeg k₀ 1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk, Sigma.ext_iff]

theorem x'_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} [Fintype K₂]
    {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι}
    (G : GenFibre (inrV (ι := ι) (ι₂ := ι₂)) (graphIdeal P g)) (k : K) (i : ι k)
    (hi : (X ⟨k, i⟩ : MRing ι) ∉ P) : G.x' ⟨Sum.inl k, i⟩ ≠ 0 := by
  intro h
  have h1 : (X ⟨Sum.inl k, i⟩ : MRing (Sum.elim ι ι₂)) ∈ graphIdeal P g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    simpa using h
  rw [graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at h1
  exact hi (Ideal.Quotient.eq_zero_iff_mem.1 (MvPolynomial.C_eq_zero.1 h1))

end BlockGraphDeg

open BlockGraphDeg in

theorem BlockGraphDeg.proof (hGr : GraphStatement) (hImg : BlockGraphImage.Statement)
    (hEx : GenFibreExistsStatement) (hDim : FibreDimStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCR : Inter.ChartRankAdjoin.Statement) (hRat : BlockGraphFibreRatio.Statement) :
    BlockGraphDeg.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hy hB hx hI
  have hImage := hImg K ι Ω κ y k₀ M N x hI
  have hIm : IsArithVar (imageZ (inrV (ι := ι) (ι₂ := GlobalTheory κ))
      (graphIdeal (mCoordIdeal y) (blockForms k₀ M))) (D + 1) := by
    rw [hImage]
    exact hx

  have hnv : ∀ u : Unit, ∃ j, blockForms k₀ M ⟨u, j⟩ ∉ mCoordIdeal y := by
    intro u
    obtain ⟨j, hj⟩ := hIm.2.1.2.2 u
    refine ⟨j, fun hm => hj ?_⟩
    rw [imageZ, Ideal.mem_comap]
    change rename inrV (X ⟨u, j⟩) ∈ _
    rw [rename_X, graphIdeal, RingHom.mem_ker, inrV, graphMap, eval₂Hom_X']
    change C (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨u, j⟩)) * X u = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero, zero_mul]
  have hΓ := (hGr K ι Unit (GlobalTheory κ) (mCoordIdeal y) (D + 1) (blockForms k₀ M) (fun _ => blockDeg k₀ 1) hy
    (isMultiHomog_blockForms k₀ M) hnv).1
  obtain ⟨G⟩ := hEx Unit (GlobalTheory κ) (K ⊕ Unit) (Sum.elim ι (GlobalTheory κ)) Sum.inr inrV _ (D + 1) isBlockMap_inr hΓ
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → K ⊕ Unit)) (fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr)
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (GlobalTheory κ) (K ⊕ Unit) (Sum.elim ι (GlobalTheory κ)) Sum.inr inrV _ (D + 1) 0 G isBlockMap_inr hΓ hIm

  choose c hc using hy.2.1.2.2
  let ch : (k : FibreBlock (Sum.inr : Unit → K ⊕ Unit)) → fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr k := fun
    | ⟨Sum.inl k, _⟩ => c k
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → K ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(k | u), h⟩
    · exact x'_ne_zero G k (c k) (hc k)
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := hCR (FibreBlock (Sum.inr : Unit → K ⊕ Unit)) (fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr) G.Φ G.Φ'
    (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → K ⊕ Unit),
      fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(k | u), h⟩, i⟩, rfl⟩
    · exact IntermediateField.mem_bot.2 (hRat D K ι Ω κ y k₀ M N x hy hB hI G k i (c k) (x'_ne_zero G k (c k) (hc k)))
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

theorem BlockResolutionMixedBridge.proof : BlockResolutionMixedBridge.Statement := by
  intro D K _ _ ι _ Ω _ _ d L A₁ hL hdeg hA₁
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (mCoordIdeal d.y) Ψ :=
    goodProjExists K ι (mCoordIdeal d.y) D d.arith
  set B : HermLine ι := A₁.tensor d.A.inv with hBdef
  have hB0 : B.a = 0 := by
    funext k
    simp [B, HermLine.tensor, HermLine.inv, hdeg, d.deg]
  have hgl : (fun z => Real.log (A₁.h z / d.A.h z)) = logNorm B.inv 1 := by
    funext z
    rw [logNorm_inv_one]
    simp only [B, HermLine.tensor, HermLine.inv, div_eq_mul_inv]
  have hBs : IsSmoothHerm B.inv :=
    isSmoothHerm_inv (isSmoothHerm_tensor hA₁ (isSmoothHerm_inv d.semipos.1))
  have hsec : IsSectionOn (mCoordIdeal d.y) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 hB0
  have key := AnResBridge.bridge d.R hex.choose L B.inv 1 d.arith hex.choose_spec hL hBs hsec
  have hgr : (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x))) =
      fun x => logNorm B.inv 1 (d.R.lift x x) :=
    funext fun x => congrFun hgl (d.R.lift x x)
  unfold ptsIntegral
  rw [dif_pos hex, hgl, hgr]
  exact key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

