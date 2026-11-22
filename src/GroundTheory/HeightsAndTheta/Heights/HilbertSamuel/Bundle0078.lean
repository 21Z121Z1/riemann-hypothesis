import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicAdjoinRangeIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0075

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubquot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GradedSubquot

set_option linter.unusedSectionVars false

theorem iSupIndep_comap {R N M : Type*} [Ring R] [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    {κ : Type*} {p : κ → Submodule R M} (hp : iSupIndep p) (g : N →ₗ[R] M) (hg : Function.Injective g) :
    iSupIndep fun i => (p i).comap g := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ i), (p j).comap g) ≤ (⨆ (j) (_ : j ≠ i), p j).comap g :=
    iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => p j) j hj)
  have h0 := (Submodule.disjoint_def.mp (hp i)) (g x) (Submodule.mem_comap.mp hx) (Submodule.mem_comap.mp (hle hx'))
  exact hg (by rw [h0, map_zero])

theorem iSupIndep_map_of_ker_le {R N Q : Type*} [Ring R] [AddCommGroup N] [AddCommGroup Q] [Module R N]
    [Module R Q] {κ : Type*} {p : κ → Submodule R N} (hp : iSupIndep p) (f : N →ₗ[R] Q)
    (hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ p c)) :
    iSupIndep fun i => (p i).map f := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  rw [Submodule.disjoint_def]
  intro y hy hy'
  obtain ⟨x, hx, rfl⟩ := hy
  have hy2 : f x ∈ (⨆ (j) (_ : j ≠ i), p j).map f := by
    simpa only [Submodule.map_iSup] using hy'
  obtain ⟨z, hz, hzx⟩ := hy2
  have hk : x - z ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hzx, sub_self]
  have hk' := hL hk
  rw [iSup_split_single (fun c => LinearMap.ker f ⊓ p c) i, Submodule.mem_sup] at hk'
  obtain ⟨l, hl, w, hw, hlw⟩ := hk'
  have hw1 : w ∈ ⨆ (j) (_ : j ≠ i), p j :=
    (show (⨆ (j) (_ : j ≠ i), LinearMap.ker f ⊓ p j) ≤ ⨆ (j) (_ : j ≠ i), p j from
      iSup₂_mono fun j _ => inf_le_right) hw
  have hxl : x - l ∈ p i := sub_mem hx (Submodule.mem_inf.mp hl).2
  have hxl' : x - l ∈ ⨆ (j) (_ : j ≠ i), p j := by
    have e : x - l = z + w := by
      calc x - l = (x - z) - l + z := by abel
        _ = z + w := by rw [← hlw]; abel
    rw [e]
    exact Submodule.add_mem _ hz hw1
  have h0 := (Submodule.disjoint_def.mp (hp i)) (x - l) hxl hxl'
  rw [sub_eq_zero.mp h0]
  exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hl).1

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem isMultiHomog_monomial (d : (Σ k, ι k) →₀ ℕ) (r : S) (a : K → ℕ)
    (hd : ∀ k, ∑ i, d ⟨k, i⟩ = a k) : IsMultiHomog (monomial d r : MRingOver S ι) a := by
  classical
  intro m hm k
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  exact hd k

variable (S ι) in

def monTimes (H : Set M) : Set M :=
  {y | ∃ (u : (Σ k, ι k) →₀ ℕ) (h : M), h ∈ H ∧ y = (monomial u (1 : S) : MRingOver S ι) • h}

theorem monTimes_subset_span (H : Set M) : monTimes S ι H ⊆ Submodule.span (MRingOver S ι) H := by
  rintro _ ⟨u, h, hh, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span hh)

theorem span_monTimes_le (H : Set M) :
    Submodule.span S (monTimes S ι H) ≤ (Submodule.span (MRingOver S ι) H).restrictScalars S :=
  Submodule.span_le.mpr (monTimes_subset_span H)

theorem monomial_smul_mem (H : Set M) (u : (Σ k, ι k) →₀ ℕ) {y : M}
    (hy : y ∈ Submodule.span S (monTimes S ι H)) :
    (monomial u (1 : S) : MRingOver S ι) • y ∈ Submodule.span S (monTimes S ι H) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, h, hh, rfl⟩ := hx
    refine Submodule.subset_span ⟨u + v, h, hh, ?_⟩
    rw [smul_smul, monomial_mul, one_mul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
  | smul s x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ s hx

theorem span_le_span_monTimes (H : Set M) :
    (Submodule.span (MRingOver S ι) H).restrictScalars S ≤ Submodule.span S (monTimes S ι H) := by
  let T : Submodule (MRingOver S ι) M :=
    { carrier := Submodule.span S (monTimes S ι H)
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro p y hy
        refine MvPolynomial.induction_on' p (fun u a => ?_) (fun p q hp hq => ?_)
        · have e : (monomial u a : MRingOver S ι) = a • monomial u (1 : S) := by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
          rw [e, smul_assoc]
          exact Submodule.smul_mem _ a (monomial_smul_mem H u hy)
        · rw [add_smul]
          exact Submodule.add_mem _ hp hq }
  have hT : Submodule.span (MRingOver S ι) H ≤ T := by
    rw [Submodule.span_le]
    intro h hh
    have e : h = (monomial 0 (1 : S) : MRingOver S ι) • h := by
      rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_smul]
    exact Submodule.subset_span ⟨0, h, hh, e⟩
  exact fun x hx => hT hx

theorem monTimes_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {y : M} (hy : y ∈ monTimes S ι H) : ∃ c, y ∈ 𝓜 c := by
  obtain ⟨u, h, hh, rfl⟩ := hy
  obtain ⟨c, hc⟩ := hH h hh
  exact ⟨_, hM.2 (fun k => ∑ i, u ⟨k, i⟩) c _ h (isMultiHomog_monomial u 1 _ fun _ => rfl) hc⟩

theorem mem_iSup_inf {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {N : Submodule (MRingOver S ι) M}
    (hHN : Submodule.span (MRingOver S ι) H ≤ N) (x : N) (hx : (x : M) ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
  obtain ⟨x, hxN⟩ := x
  have hmem : ∀ y ∈ Submodule.span S (monTimes S ι H), ∀ hy : y ∈ N, (⟨y, hy⟩ : N) ∈
      ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro _
      obtain ⟨c, hc⟩ := monTimes_homog hM hH hy
      exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.mpr ⟨monTimes_subset_span H hy, hc⟩)
    | zero => intro _; exact Submodule.zero_mem _
    | add y z hy hz ihy ihz =>
      intro _
      exact Submodule.add_mem _ (ihy (hHN (span_monTimes_le H hy))) (ihz (hHN (span_monTimes_le H hz)))
    | smul s y hy ihy =>
      intro _
      exact Submodule.smul_mem _ s (ihy (hHN (span_monTimes_le H hy)))
  exact hmem x (span_le_span_monTimes H hx) hxN

end GradedSubquot

open GradedSubquot in

theorem GradedSubquot.proof : GradedSubquot.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 G H hM hG hH hGH

  have hind : iSupIndep (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) :=
    iSupIndep_comap hM.1.submodule_iSupIndep ((Submodule.span (MRingOver S ι) H).subtype.restrictScalars S)
      (fun a b h => Subtype.ext h)
  have hsup : ⨆ c, subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    exact (show (⨆ c, ((Submodule.span (MRingOver S ι) H).comap (Submodule.span (MRingOver S ι) H).subtype).restrictScalars S ⊓
        subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c) ≤ ⨆ c, subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c from
      iSup_mono fun c => inf_le_right) (mem_iSup_inf hM hH le_rfl x x.2)
  refine ⟨⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup,
    fun a c p m hp hm => hM.2 a c p (m : M) hp hm⟩, ?_⟩

  set L := (Submodule.span (MRingOver S ι) G).comap (Submodule.span (MRingOver S ι) H).subtype with hLdef
  set f := L.mkQ.restrictScalars S with hfdef
  have hker : LinearMap.ker f = L.restrictScalars S := by
    ext x
    simp [hfdef]
  have hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c) := by
    rw [hker]
    intro x hx
    exact mem_iSup_inf hM hG hGH x hx
  have hind2 := iSupIndep_map_of_ker_le hind f hL
  have hsup2 : ⨆ c, quotGrading (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) L c = ⊤ := by
    change ⨆ c, (subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c).map f = ⊤
    rw [← Submodule.map_iSup, hsup, Submodule.map_top, LinearMap.range_eq_top]
    exact Submodule.mkQ_surjective L
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind2 hsup2, ?_⟩
  rintro a c p _ hp ⟨x, hx, rfl⟩
  exact ⟨p • x, hM.2 a c p (x : M) hp hx, L.mkQ.map_smul p x⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIsomInvariance
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace IsomInvariance

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_ratSection {P : Ideal (MRing ι)} (hP : P.IsPrime) (hrel : IsRelevant P) (B : HermLine ι) :
    ∃ s t : MRing ι, IsRatSectionOn P B s t := by
  classical
  let c : ∀ k, ι k := fun k => (hrel k).choose
  have hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P := fun k => (hrel k).choose_spec
  exact ⟨_, _, fun k => (B.a k).toNat, fun k => (-B.a k).toNat, Inter.AvoidRing.isMultiHomog_coordProd c _,
    Inter.AvoidRing.isMultiHomog_coordProd c _, Inter.AvoidRing.coordProd_not_mem hP c hc _,
    Inter.AvoidRing.coordProd_not_mem hP c hc _, fun k => Int.toNat_sub_toNat_neg _⟩

theorem snoc_eq (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {m : ℕ} (N : Fin m → HermLine ι) (A B : HermLine ι)
    (hP : IsArithVar P (m + 1)) (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAB : IsIsometricOn P A B) : I P (m + 1) (Fin.snoc N A) = I P (m + 1) (Fin.snoc N B) := by
  obtain ⟨f, g, α, β, hf, hg, hfP, hgP, hdeg, hdiv, hnorm⟩ := hAB
  have hPp : P.IsPrime := hP.2.1.1
  have nm : ∀ {x y : MRing ι}, x ∉ P → y ∉ P → x * y ∉ P := fun hx hy h => (hPp.mem_or_mem h).elim hx hy
  obtain ⟨s, t, σ, τ, hs, ht, hsP, htP, hst⟩ := exists_ratSection hPp hP.2.1.2.2 B
  have hB' : IsRatSectionOn P B (s * g) (t * g) :=
    ⟨σ + β, τ + β, Inter.AvoidRing.isMultiHomog_mul hs hg, Inter.AvoidRing.isMultiHomog_mul ht hg,
      nm hsP hgP, nm htP hgP, fun k => by have := hst k; simp only [Pi.add_apply]; push_cast; linarith⟩
  have hA' : IsRatSectionOn P A (s * f * g) (t * g * g) :=
    ⟨σ + α + β, τ + β + β,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hs hf) hg,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul ht hg) hg,
      nm (nm hsP hfP) hgP, nm (nm htP hgP) hgP,
      fun k => by have := hst k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith⟩
  rw [hR K ι I hI P m N A _ _ hP hN hA hA', hR K ι I hI P m N B _ _ hP hN hB hB']
  unfold recRRat
  have hfg : cycR I P N f = cycR I P N g := by
    rw [Inter.cycR_eq_sum, Inter.cycR_eq_sum, hdiv]
  have hint : ptsIntegral P (pot N) (logNormRat A (s * f * g) (t * g * g)) =
      ptsIntegral P (pot N) (logNormRat B (s * g) (t * g)) := by
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun _ _ _ => rfl) fun z hz => ?_
    unfold logNormRat
    congr 1
    have ha := A.pos z hz.1
    have hb := B.pos z hz.1
    have hn := hnorm z hz
    simp only [map_mul, norm_mul] at hn ⊢
    set S := ‖eval z (map (Int.castRingHom ℂ) s)‖
    set T := ‖eval z (map (Int.castRingHom ℂ) t)‖
    set F := ‖eval z (map (Int.castRingHom ℂ) f)‖
    set G := ‖eval z (map (Int.castRingHom ℂ) g)‖
    rcases eq_or_ne T 0 with hT | hT
    · simp [hT]
    rcases eq_or_ne G 0 with hG | hG
    · simp [hG]
    rw [div_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (S * G * G * T) * hn
  rw [Inter.cycR_mul I hPp N (nm hsP hfP) hgP, Inter.cycR_mul I hPp N hsP hfP,
    Inter.cycR_mul I hPp N (nm htP hgP) hgP, Inter.cycR_mul I hPp N htP hgP,
    Inter.cycR_mul I hPp N hsP hgP, hint, hfg]
  ring

theorem update_eq (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {n : ℕ} (L : Fin n → HermLine ι) (j : Fin n)
    (B : HermLine ι) (hP : IsArithVar P n) (hL : ∀ i, IsSmoothHerm (L i)) (hB : IsSmoothHerm B)
    (hLB : IsIsometricOn P (L j) B) : I P n L = I P n (Function.update L j B) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) j.2))
  have hL' : ∀ i, IsSmoothHerm (Function.update L j B i) := fun i => by
    by_cases hi : i = j
    · subst hi; simpa using hB
    · simpa [Function.update_of_ne hi] using hL i
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
  let N : Fin m → HermLine ι := fun i => L (σ i.castSucc)
  have hne : ∀ i : Fin m, σ i.castSucc ≠ j := fun i h => by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact Fin.castSucc_ne_last i h
  have e1 : L ∘ σ = Fin.snoc N (L j) := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp [N]
  have e2 : Function.update L j B ∘ σ = Fin.snoc N B := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp [N, Function.update_of_ne (hne i)]
  rw [← hI.1 P _ L σ hP hL, ← hI.1 P _ _ σ hP hL', e1, e2]
  exact snoc_eq hR hI N (L j) B hP (fun i => hL _) (hL j) hB hLB

end IsomInvariance

theorem IsomInvariance.proof (hR : Inter.RatR.Statement) : IsomInvariance.Statement := by
  classical
  intro K _ ι _ I hI P n L L' hP hL hL' hiso
  let M : Finset (Fin n) → Fin n → HermLine ι := fun S j => if j ∈ S then L' j else L j
  have hM : ∀ S j, IsSmoothHerm (M S j) := fun S j => by
    by_cases h : j ∈ S
    · simpa [M, h] using hL' j
    · simpa [M, h] using hL j
  have key : ∀ S : Finset (Fin n), I P n L = I P n (M S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [M]
    | insert a S ha ih =>
      have e : M (insert a S) = Function.update (M S) a (L' a) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [M]
        · simp [M, hj]
      have hMa : M S a = L a := by simp [M, ha]
      rw [ih, e]
      exact IsomInvariance.update_eq hR hI (M S) a (L' a) hP (hM S) (hL' a) (hMa ▸ hiso a)
  have hU : M Finset.univ = L' := by funext j; simp [M]
  rw [key Finset.univ, hU]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanScheme
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem nefOnF_mono {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {I : IFamily F ι} {V Q : Ideal (MRingOver F ι)} {α : K → ℤ} (hN : KH.NefOnF I V α) (hVQ : V ≤ Q) :
    KH.NefOnF I Q α :=
  fun W hW hQW => hN W hW (hVQ.trans hQW)

theorem ampleV_of_nsmul {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {V : Ideal (MRingOver S ι)} {N : K → ℤ} {q : ℕ} (hq : 1 ≤ q)
    (h : KH.AmpleV S V (q • N)) : KH.AmpleV S V N := by
  obtain ⟨q₂, hq₂, hgen, hvan⟩ := h
  refine ⟨q₂ * q, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun e => ?_⟩
  · rwa [mul_smul]
  · obtain ⟨c₁, hc⟩ := hvan e
    refine ⟨c₁, fun c hc' => ?_⟩
    have := hc c hc'
    rwa [smul_smul, mul_assoc] at this

theorem KleimanScheme.proof (hVar : KleimanVarietyH1Generation.Statement) (hDev : H1GenerationDevissage.Statement)
    (hGen : GenerationOfH1GenAmple.Statement) (hAG : AmpleOfGenTwist.Statement) : KleimanScheme.Statement := by
  intro F _ K _ _ ι _ _ I V α b a hI hV hN hb ha

  have hamp : H1GenAmple F V (b • α + fun _ => (a : ℤ)) :=
    hDev F K ι V _ inferInstance fun P hP hVP => hVar F K ι I P α b a hI hP (nefOnF_mono hN hVP) hb ha

  obtain ⟨c₁, hc⟩ := hGen F K ι V _ hV hamp (fun _ => -1)
  have hg := hc (c₁ + 1) (Nat.le_succ c₁)

  have h := hAG F K ι V _ 1 1 hV hg le_rfl
  have e : ((1 : ℕ) : ℤ) • ((fun _ => (-1 : ℤ)) + (c₁ + 1) • (b • α + fun _ => (a : ℤ))) +
      (fun _ => ((1 : ℕ) : ℤ)) = (c₁ + 1) • (b • α + fun _ => (a : ℤ)) := by
    funext k
    simp only [Nat.cast_one, one_smul, Pi.add_apply]
    ring
  rw [e] at h
  exact ampleV_of_nsmul (Nat.le_add_left 1 c₁) h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKrullDimMatAct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KrullDimMatAct

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

def coneAdjoinQ (x : J → Ω) : Subalgebra ℚ (Polynomial Ω) :=
  Algebra.adjoin ℚ (Set.range fun j => Polynomial.C (x j) * Polynomial.X)

theorem mem_coneAdjoinQ_matAct (A : Matrix J J ℚ) (x : J → Ω) (i : J) :
    Polynomial.C (matAct A x i) * Polynomial.X ∈ coneAdjoinQ x := by
  have h : Polynomial.C (matAct A x i) * Polynomial.X =
      ∑ j, A i j • (Polynomial.C (x j) * Polynomial.X) := by
    simp only [matAct, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Polynomial.algebraMap_apply, eq_ratCast, Polynomial.C_mul, mul_assoc]
  rw [h]
  exact Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) _

theorem coneAdjoinQ_matAct_le (A : Matrix J J ℚ) (x : J → Ω) :
    coneAdjoinQ (matAct A x) ≤ coneAdjoinQ x :=
  Algebra.adjoin_le (Set.range_subset_iff.mpr fun i => mem_coneAdjoinQ_matAct A x i)

theorem coneAdjoinQ_matAct_eq {B : Matrix J J ℚ} (hB : IsInvMat B) (x : J → Ω) :
    coneAdjoinQ (matAct B x) = coneAdjoinQ x := by
  classical
  obtain ⟨B', _, hB'B⟩ := isInvMat_mul hB
  refine le_antisymm (coneAdjoinQ_matAct_le B x) ?_
  have h := coneAdjoinQ_matAct_le B' (matAct B x)
  rwa [matAct_matAct hB'B] at h

theorem ringKrullDim_quot_coordIdeal (x : J → Ω) :
    ∃ s : ℕ, Algebra.trdeg ℚ (coneAdjoinQ x) = s ∧
      ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ x) = (s : WithBot ℕ∞) + 1 := by
  obtain ⟨s, h1, h2⟩ := GroundTheory.Heights₂.Heights.TrdegAdjoin.ringKrullDim_quotient_ker
    (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω)
  have hX : (fun v => (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω) (X v)) =
      fun j => Polynomial.C (x j) * Polynomial.X :=
    funext fun v => by simp [coneMap]
  rw [hX] at h1
  exact ⟨s, h1, h2⟩

theorem proof : KrullDimMatAct.Statement := by
  intro Ω _ _ J _ x B hB
  obtain ⟨s, hs, hds⟩ := ringKrullDim_quot_coordIdeal (matAct B x)
  obtain ⟨t, ht, hdt⟩ := ringKrullDim_quot_coordIdeal x
  rw [coneAdjoinQ_matAct_eq hB, ht] at hs
  have hst : s = t := by exact_mod_cast hs.symm
  rw [hds, hdt, hst]

end KrullDimMatAct

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelLatticeFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem RelLatticeFinite.proof (hL : RelSectionsLarge.Statement) : RelLatticeFinite.Statement := by
  intro K _ ι _ Ω _ y a n m g hy
  have hN : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g)) := adjoin_isNoetherianRing g
  obtain ⟨n₁, hn₁⟩ := hL K ι Ω (Algebra.adjoin ℤ (Set.range g)) hN y hy
  choose c0 hc0 using hy
  set R := Algebra.adjoin ℤ (Set.range g)
  let e : K → ℕ := fun k => n₁ + ((n : ℤ) * a k).natAbs
  let b : K → ℕ := fun k => ((n : ℤ) * a k + e k).toNat
  have hb : ∀ k, ((b k : ℕ) : ℤ) = (n : ℤ) * a k + e k := by
    intro k
    refine Int.toNat_of_nonneg ?_
    simp only [e]
    push_cast
    have := neg_abs_le ((n : ℤ) * a k)
    omega
  have hbn : ∀ k, n₁ ≤ b k := by
    intro k
    have h1 := hb k
    simp only [e] at h1
    push_cast at h1
    have := neg_abs_le ((n : ℤ) * a k)
    omega
  set mon : Ω := ∏ k, y ⟨k, c0 k⟩ ^ e k
  have hmon : mon ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  let φ : Ω →ₗ[R] Ω := LinearMap.mulRight R mon
  have hφ : Function.Injective φ := mul_left_injective₀ hmon
  have hmap : (relChartLat R y a n).map φ ≤ relSecM R y b := by
    rintro _ ⟨s, hs, rfl⟩
    exact hn₁ b hbn (mul_prod_mem_relChartLat R y e c0 (fun k => hb k) hs)
  have : IsNoetherian R (relSecM R y b) := isNoetherian_of_fg_of_noetherian _ (relSecM_fg R y b)
  exact Submodule.fg_of_fg_map_injective φ hφ (Submodule.FG.of_le_of_isNoetherian hmap)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNefGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedNefGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    NefOnGenericDeg (mCoordIdeal y) a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

