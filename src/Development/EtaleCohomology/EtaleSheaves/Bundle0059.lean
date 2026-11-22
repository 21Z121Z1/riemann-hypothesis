import Development.EtaleCohomology.EtaleSheaves.Bundle0051
import Development.EtaleCohomology.EtaleSheaves.Bundle0048
import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.NormAICOf
import Development.EtaleCohomology.EtaleSheaves.Bundle0052
import Development.EtaleCohomology.EtaleSheaves.Bundle0045

-- bundled from Development.EtaleCohomology.EtaleSheaves.LiftPf
section
noncomputable section
open Polynomial LateralTheory.E.PartDiagCut

namespace LateralTheory.E.LiftPf

theorem orthF {A : Type} [CommRing A] (P : PartDiagCut.Part A) {n : ℕ} (ε : Fin n → A)
    (hfo : ∀ l m, l ≠ m → ε l * ε m = 0) {e e' : A} (he : e ∈ P.1) (he' : e' ∈ P.1) {l m : Fin n}
    (hne : (e, l) ≠ (e', m)) : e * ε l * (e' * ε m) = 0 := by
  by_cases hee : e = e'
  · subst hee
    have hlm : l ≠ m := fun h => hne (by rw [h])
    calc e * ε l * (e * ε m) = e * e * (ε l * ε m) := by ring
      _ = 0 := by rw [hfo l m hlm, mul_zero]
  · calc e * ε l * (e' * ε m) = (e * e') * (ε l * ε m) := by ring
      _ = 0 := by rw [P.orth e he e' he' hee, zero_mul]

theorem refine_exists {A : Type} [CommRing A] (P : PartDiagCut.Part A) {n : ℕ} (ε : Fin n → A)
    (hfi : ∀ l, IsIdempotentElem (ε l)) (hfo : ∀ l m, l ≠ m → ε l * ε m = 0)
    (hfs : ∑ l, ε l = 1) : ∃ Q : PartDiagCut.Part A, P ≤ Q ∧ ∀ g ∈ Q.1, ∃ l, g * ε l = g := by
  classical
  let F : A × Fin n → A := fun x => x.1 * ε x.2
  let T := (P.1 ×ˢ (Finset.univ : Finset (Fin n))).filter (fun x => F x ≠ 0)
  have memT : ∀ x ∈ T, x.1 ∈ P.1 ∧ F x ≠ 0 := by
    intro x hx
    simp only [T, Finset.mem_filter, Finset.mem_product] at hx
    exact ⟨hx.1.1, hx.2⟩
  have idF : ∀ x ∈ T, IsIdempotentElem (F x) := fun x hx => (P.idem x.1 (memT x hx).1).1.mul (hfi x.2)
  have oF : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → F x * F y = 0 := fun x hx y hy hxy =>
    orthF P ε hfo (memT x hx).1 (memT y hy).1 (by simpa using hxy)
  have inj : Set.InjOn F T := by
    intro x hx y hy hxy
    by_contra hne
    apply (memT x hx).2
    rw [← (idF x hx).eq]
    nth_rewrite 2 [hxy]
    exact oF x hx y hy hne
  refine ⟨⟨T.image F, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨idF x hx, (memT x hx).2⟩
  · intro g hg g' hg' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg'
    exact oF x hx y hy (fun h => hne (by rw [h]))
  · rw [Finset.sum_image inj, Finset.sum_filter_ne_zero, Finset.sum_product]
    simp only [F]
    simp_rw [← Finset.mul_sum, hfs, mul_one]
    exact P.sum_eq
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨x.1, (memT x hx).1, ?_⟩
    show x.1 * ε x.2 * x.1 = x.1 * ε x.2
    rw [mul_right_comm, (P.idem x.1 (memT x hx).1).1.eq]
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨x.2, by show x.1 * ε x.2 * ε x.2 = x.1 * ε x.2; rw [mul_assoc, (hfi x.2).eq]⟩

variable {B : Type} [CommRing B]

theorem natHom (I : Ideal B) {P Q : PartDiagCut.Part (B ⧸ I)} (h : P ≤ Q) :
    (stageMap I h).comp (βP I P) = βP I Q := by
  refine RingHom.ext fun x => funext fun g => ?_
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact IsLocalization.map_eq _ _

theorem isUnit_comp (I : Ideal B) (Q : PartDiagCut.Part (B ⧸ I)) (g : Q.1) (x : B) (hx : x ∈ S I g.1) :
    IsUnit (βP I Q x g) := by
  simpa [βP] using IsLocalization.map_units (Localization (S I g.1)) (⟨x, hx⟩ : S I g.1)

theorem mem_of_comp (I : Ideal B) (Q : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I Q)
    (hz : ∀ g : Q.1, ∃ w ∈ I.map (βP I Q), ∃ c : Localization (S I g.1), z g = c * w g) :
    z ∈ I.map (βP I Q) := by
  classical
  rw [← Finset.univ_sum_single z]
  refine Ideal.sum_mem _ fun g _ => ?_
  obtain ⟨w, hw, c, hc⟩ := hz g
  have : (Pi.single g (z g) : PiLocalization₂ I Q) = (Pi.single g c : PiLocalization₂ I Q) * w := by
    funext g'
    by_cases hg : g' = g
    · subst hg; simp [hc]
    · simp [hg]
  rw [this]; exact Ideal.mul_mem_left _ _ hw

theorem Lift_of : LateralTheory.E.PartCPf.Lift := by
  classical
  intro B _ I P p a₀ n r f hp hfi hfo hfs hy
  obtain ⟨Q, h, hL⟩ := refine_exists P (fun l => Ideal.Quotient.mk I (f l)) hfi hfo hfs
  choose L hLg using fun g : Q.1 => hL g.1 g.2
  refine ⟨Q, h, fun g => stageMap I h (r (L g)) g, ?_, ?_⟩
  · rw [hp, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, IsRoot.def, eval_prod, eval_sub, eval_X, eval_C]
    funext g
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ (L g)) (by simp)
  · apply mem_of_comp
    intro g
    have hw : βP I Q (f (L g)) * stageMap I h (a₀ - r (L g)) ∈ I.map (βP I Q) := by
      have := Ideal.mem_map_of_mem (stageMap I h) (hy (L g))
      rw [Ideal.map_map, natHom, map_mul, ← RingHom.comp_apply, natHom] at this
      exact this
    have hmem : f (L g) ∈ S I g.1 := ⟨1, by rw [mul_one, mul_comm]; exact hLg g⟩
    obtain ⟨u, hu⟩ := isUnit_comp I Q g (f (L g)) hmem
    refine ⟨_, hw, -(↑u⁻¹ : Localization (S I g.1)), ?_⟩
    simp only [Pi.sub_apply, Pi.mul_apply, map_sub]
    rw [← hu]
    linear_combination (stageMap I h a₀ g - stageMap I h (r (L g)) g) * u.inv_mul

end LateralTheory.E.LiftPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocSurjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafLocStalkPf

namespace LateralTheory.E.LocSurjPf

def bcMap {Y X V : Scheme.{0}} (f : Y ⟶ X) (v : V ⟶ X) : cech (pullback.snd f v) ⟶ cech f :=
  Arrow.mapCechNerve (Arrow.homMk (f := Arrow.mk (yoneda.map (pullback.snd f v))) (g := Arrow.mk (yoneda.map f))
    (yoneda.map (pullback.fst f v)) (yoneda.map v)
    (by simp only [Arrow.mk_hom, ← Functor.map_comp, pullback.condition]))

def EtLift (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (i m : ℤ) (y : Ht q (cech f) m i) : Prop :=
  ∃ (V : Scheme.{0}) (v : V ⟶ X), Etale v ∧ Surjective v ∧
    ∃ z : Ht q (sch.obj V) m i, pull (ZMod q) (cechAug (pullback.snd f v)) (tw q i) m z = pull (ZMod q) (bcMap f v) (tw q i) m y

def LocLiftEt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ m < n, QAll q m) →
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, StalkH q f i →
    ∀ m : ℤ, m + 1 = n → ∀ y : Ht q (cech f) m i, EtLift q f i m y

def LocGlueEt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ m < n, QAll q m) →
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, StalkH q f i →
    ∀ m : ℤ, m + 1 = n → ∀ y : Ht q (cech f) m i, EtLift q f i m y →
      y ∈ Set.range (pull (ZMod q) (cechAug f) (tw q i) m)

end LateralTheory.E.LocSurjPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocalIntegralClosureRoots
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut Polynomial

namespace LateralTheory.E.LocalIntegralClosureRoots

theorem root_mem (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] (h : GlobalTheory.EtC.AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → ∀ x : K, aeval x p = 0 →
      ∃ a : A, algebraMap A K a = x := by
  intro n
  induction n with
  | zero =>
    intro p hn hp x hx
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hp hn
    subst h1
    simp at hx
  | succ n ih =>
    intro p hn hp x hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdvd : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hq : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hdvd]; exact hp)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hdvd, map_mul] at hx
    rcases mul_eq_zero.mp hx with h1 | h1
    · refine ⟨a, ?_⟩
      simp only [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
      exact h1.symm
    · exact ih _ hqd hq x h1

theorem isIntegrallyClosed_of_aic (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x ⟨p, hp, hx⟩
  exact root_mem A (FractionRing A) h _ p rfl hp x (by rw [aeval_def]; exact hx)

theorem LocAIC_of : NormPf.AICPf.LocAIC := by
  intro X _ hcov
  refine ⟨inferInstance, fun V hV hVne => ?_⟩
  have : Nonempty V := hVne.to_subtype
  have hst : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro x
    obtain ⟨U, hxU, hU, hA⟩ := hcov x
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    have := isIntegrallyClosed_of_aic _ hA
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)
  have hR : IsIntegrallyClosed Γ(X, V) := by
    apply IsIntegrallyClosed.of_localization_maximal
    intro P _ hP
    let y : PrimeSpectrum Γ(X, V) := ⟨P, hP.isPrime⟩
    have hy : hV.fromSpec y ∈ V := by
      show hV.fromSpec y ∈ (V : Set X)
      rw [← hV.range_fromSpec]; exact ⟨y, rfl⟩
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hV.fromSpec y, hy⟩ : V)
    have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec y)) P := hV.isLocalization_stalk' y hy
    have := hst (hV.fromSpec y)
    exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv P.primeCompl
      (X.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime P)).toRingEquiv
  have hK : IsAlgClosed X.functionField := by
    obtain ⟨x⟩ := ‹Nonempty V›
    obtain ⟨U, hxU, hU, hA⟩ := hcov x.1
    have : Nonempty U := ⟨⟨x.1, hxU⟩⟩
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    exact NormPf.FFPf.algClosed_of_aic _ _ hA
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  intro p hp hd
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (algebraMap Γ(X, V) X.functionField))
    (by
      rw [degree_map_eq_of_injective (IsFractionRing.injective Γ(X, V) X.functionField),
        degree_eq_natDegree hp.ne_zero]
      exact_mod_cast hd.ne')
  have hint : IsIntegral Γ(X, V) z := ⟨p, hp, by rwa [IsRoot, Polynomial.eval_map] at hz⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, IsFractionRing.injective Γ(X, V) X.functionField ?_⟩
  have hz' : eval z (p.map (algebraMap Γ(X, V) X.functionField)) = 0 := hz
  rw [map_zero, ← hz', Polynomial.eval_map, ← ha, eval₂_at_apply]

end LateralTheory.E.LocalIntegralClosureRoots

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.NbIsoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut

namespace LateralTheory.E.NbIsoPf

def FlatMonoLim : Prop := ∀ {Y : Scheme.{0}} {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0})
  (ι : ∀ j, D.obj j ⟶ Y), (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) →
  (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) →
  ∀ {X : Scheme.{0}} (m : X ⟶ Y), Mono m → Flat m → QuasiCompact m → Set.range m = ⋂ j, Set.range (ι j) →
  ∀ c : Cone D, IsLimit c → Nonempty (c.pt ≅ X)

def SysFM : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ∃ m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization,
        Mono m ∧ Flat m ∧ QuasiCompact m ∧ Set.range m = ⋂ j, Set.range (ι j)

theorem NbIso_of (hS : SysFM) (hL : FlatMonoLim) : LateralTheory.E.SysPf.NbIso := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, m, hm, hf, hq, hr⟩ := hS W w hW y
  refine ⟨q, J, inferInstance, inferInstance, D, ι, h1, h2, fun c hc => ?_⟩
  exact hL D ι (fun j => ⟨(h1 j).1, (h1 j).2.1⟩) (fun f => (h2 f).1) m hm hf hq hr c hc

end LateralTheory.E.NbIsoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.NoetherianLocalChartOverlapFiniteComplement
section
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemSumNoetherian

def NoetherianLocalChartOverlapFiniteComplement : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG →
  ∃ N : Submodule A K, N.FG ∧ Subalgebra.toSubmodule (AdjoinInv B t) ≤
    Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N

def LZIdemPow : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f → ∀ k : ℕ,
  ∃ b ∈ B, ∃ c ∈ C, e - b ∈ mS B ∧ c - f ∈ mS C ∧
    b - c ∈ (IsLocalRing.maximalIdeal A ^ k) • Subalgebra.toSubmodule (AdjoinInv B t)

def LZARStep : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (M : Type) [AddCommGroup M]
  [Module A M] (N P : Submodule A M), N.FG →
  ∃ k : ℕ, 1 ≤ k ∧ (IsLocalRing.maximalIdeal A ^ k) • N ⊓ P ≤ IsLocalRing.maximalIdeal A • P

theorem goal_of (h1 : NoetherianLocalChartOverlapFiniteComplement) (h2 : LZIdemPow) (h3 : LZARStep) :
    LateralTheory.E.IdempotentLiftingAlt.LZIdemSumNoeth := by
  intro A _ _ _ K _ _ B C t hc hB hC e f hp
  obtain ⟨N, hN, hD⟩ := h1 A K B C t hc hB hC
  obtain ⟨k, hk, hAR⟩ := h3 A K N (Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C) hN
  obtain ⟨b, hb, c, hcC, heb, hcf, hbc⟩ := h2 A K B C t hc e f hp k
  have hmk : IsLocalRing.maximalIdeal A ^ k ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self (by omega)
  have hbc' := Submodule.smul_mono (le_refl (IsLocalRing.maximalIdeal A ^ k)) hD hbc
  rw [Submodule.smul_sup, Submodule.smul_sup] at hbc'
  obtain ⟨x, hx, n, hn, hxn⟩ := Submodule.mem_sup.mp hbc'
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hx
  have hβB : β ∈ B := Submodule.smul_le_right hβ
  have hγC : γ ∈ C := Submodule.smul_le_right hγ
  have hnP : n ∈ Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C := by
    refine Submodule.mem_sup.mpr ⟨b - β, B.sub_mem hb hβB, -(c + γ), C.neg_mem (C.add_mem hcC hγC), ?_⟩
    linear_combination -hxn - hβγ
  have hnm := hAR ⟨hn, hnP⟩
  rw [Submodule.smul_sup] at hnm
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hnm
  have hβm : β ∈ mS B := Submodule.smul_mono_left hmk hβ
  have hγm : γ ∈ mS C := Submodule.smul_mono_left hmk hγ
  have hum : u ∈ mS B := hu
  have hvm : v ∈ mS C := hv
  refine Submodule.mem_sup.mpr ⟨(e - b) + β + u, (mS B).add_mem ((mS B).add_mem heb hβm) hum,
    γ + v + (c - f), (mS C).add_mem ((mS C).add_mem hγm hvm) hcf, ?_⟩
  linear_combination hxn + hβγ + huv

end LateralTheory.E.LZIdemSumNoetherian
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PartCPfSplit
section
noncomputable section
open Polynomial LateralTheory.E.PartDiagCut GlobalTheory.EtC

namespace LateralTheory.E.PartCPfSplit

theorem split_of (hLoc : LateralTheory.E.HensCut.LocAIC) (hMS : LateralTheory.E.HensCut.MonicSplits) : LateralTheory.E.PartCPf.Split := by
  intro B _ _ I hB P p hm
  have key : ∀ e : P.1, ∃ g : Fin p.natDegree → Localization (S I e.1),
      p.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) = ∏ l, (X - C (g l)) := by
    intro e
    have h0 : (0:B) ∉ S I e.1 := by
      rintro ⟨t, ht⟩
      apply (P.idem e.1 e.2).2
      simpa using ht.symm
    obtain ⟨hdom, haic⟩ := hLoc B (S I e.1) h0 hB
    have hme := hm.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)
    obtain ⟨s, hs⟩ := hMS _ haic _ hme
    have hcard : s.toList.length = p.natDegree := by
      have := congrArg natDegree hs
      rw [natDegree_multiset_prod_X_sub_C_eq_card, hm.natDegree_map] at this
      simp [this]
    refine ⟨fun l => s.toList.get (Fin.cast hcard.symm l), ?_⟩
    rw [hs]
    conv_lhs => rw [← Multiset.coe_toList s]
    rw [Multiset.map_coe, Multiset.prod_coe]
    rw [← Fintype.prod_equiv (finCongr hcard) (fun i : Fin s.toList.length => X - C (s.toList.get i)) _ (fun _ => rfl)]
    rw [← List.prod_ofFn]
    congr 1
    apply List.ext_get <;> simp
  choose g hg using key
  refine ⟨p.natDegree, fun l e => g e l, ?_⟩
  refine Polynomial.ext fun k => funext fun e => ?_
  have h2 : (∏ l, (X - C (fun e => g e l))).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)
      = ∏ l, (X - C (g e l)) := by simp [Polynomial.map_prod]
  have := congrArg (coeff · k) ((hg e).trans h2.symm)
  simpa [coeff_map] using this

theorem PartC_of (hLoc : LateralTheory.E.HensCut.LocAIC) (hMS : LateralTheory.E.HensCut.MonicSplits) (hIP : LateralTheory.E.HensCut.IdemPart)
    (hA : LateralTheory.E.PartDiagCut.PartA) (hl : LateralTheory.E.PartCPf.Lift) : LateralTheory.E.PartDiagCut.PartC :=
  LateralTheory.E.PartCPf.PartC_of' (split_of hLoc hMS) hIP hA hl

end LateralTheory.E.PartCPfSplit
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PointDetect0Of
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.PointDetect0Pf

def SecDetect : Prop := ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (i : ℤ) (s : Sec (tw q i) X),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ X), SH A → IsUnit (q : A) → Sec.res t s = 0) → s = 0

def NbhdKillGood : Prop := ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (i : ℤ) (s : Sec (tw q i) X) (x : X),
  IsUnit (q : X.residueField x) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ X), SH A → IsUnit (q : A) → Sec.res t s = 0) →
  ∃ (U : Scheme.{0}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧ Sec.res g s = 0

def NbhdKillBad : Prop := ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (i : ℤ) (s : Sec (tw q i) X) (x : X),
  ¬ IsUnit (q : X.residueField x) →
  ∃ (U : Scheme.{0}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧ Sec.res g s = 0

def EtSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  (∀ x : X, ∃ (U : Scheme.{0}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧ Sec.res g s = 0) → s = 0

theorem etSep : EtSep := by
  intro R _ F X s h
  choose U g hE hx h0 using h
  have hR : Presieve.ofArrows U g ∈ Scheme.precoverage @Etale X := by
    exact (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun x => ⟨x, hx x⟩, hE⟩
  have hT : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
    have := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget _)).1 F.property
    exact (isSheaf_iff_isSheaf_of_type _ _).1 this
  apply (hT.isSheafFor_of_mem_precoverage hR).isSeparatedFor.ext
  rintro Y f ⟨x⟩
  change Sec.res (g x) s = (F.obj.map (g x).op).hom 0
  rw [h0 x, map_zero]

end LateralTheory.E.PointDetect0Pf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RelDescPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.RelDescPf

theorem hkpull_comp (R : Type) [CommRing R] {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (a ≫ b) F n x = HK.pull R a F n (HK.pull R b F n x) := by
  obtain ⟨y, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  change (Cochain.ofHom (a ≫ b)).comp y.1 (zero_add n) =
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp y.1 (zero_add n)) (zero_add n)
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm : f' ≫ e = u ≫ f) (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) comm'' = rmap R f' f'' u' e' comm' ≫ rmap R f f' u e comm := by
  simp only [rmap, Functor.map_comp]
  exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

theorem rpull_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm : f' ≫ e = u ≫ f) (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    rpull R f f'' (u' ≫ u) (e' ≫ e) comm'' F n y = rpull R f' f'' u' e' comm' F n (rpull R f f' u e comm F n y) := by
  simp only [rpull]
  rw [rmap_comp R f f' f'' u e u' e' comm comm' comm'']
  exact hkpull_comp R _ _ F n y

def RelEqvInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f), Eqv R u F → Eqv R e F → ∀ n : ℤ, Function.Injective (rpull R f f' u e comm F n)

def CechEqv : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E)
  (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''), Et e → SpS e → IsPushout φ' e u φ'' →
  Eqv (ZMod q) (cechAug (Spec.map e)) (tw q i) ∧ Eqv (ZMod q) (cechAug (Spec.map u)) (tw q i)

def LevelInj : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → IsPushout φ' e u φ'' →
  ∃ (g : cech (Spec.map u) ⟶ cech (Spec.map e)) (_hA : g ≫ cechAug (Spec.map e) = cechAug (Spec.map u) ≫ sch.map (Spec.map φ'))
    (i0 : sch.obj (Spec E) ⟶ cech (Spec.map e)) (j0 : sch.obj (Spec Y'') ⟶ cech (Spec.map u))
    (h0 : sch.map (Spec.map φ'') ≫ i0 = j0 ≫ g),
    i0 ≫ cechAug (Spec.map e) = sch.map (Spec.map e) ∧ j0 ≫ cechAug (Spec.map u) = sch.map (Spec.map u) ∧
    Function.Injective (rpull (ZMod q) g (sch.map (Spec.map φ'')) j0 i0 h0 (tw q i) n)

theorem relDesc_of (hEq : RelEqvInj) (hC : CechEqv) (hL : LevelInj) : LateralTheory.E.TruncationKernel.RelDesc := by
  intro hH q _ i n A Y φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  obtain ⟨g, hA, i0, j0, h0, hi, hj, hinj⟩ := hL hH q i n φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  obtain ⟨hCe, hCu⟩ := hC hH q i φ' e u φ'' he hs hpo'
  have h1 := hEq (ZMod q) (tw q i) (sch.map (Spec.map φ')) g (cechAug (Spec.map u)) (cechAug (Spec.map e)) hA hCu hCe n
  have key : ∀ (a : sch.obj (Spec Y'') ⟶ sch.obj (Spec Y')) (b : sch.obj (Spec E) ⟶ sch.obj (Spec D))
      (ha : j0 ≫ cechAug (Spec.map u) = a) (hb : i0 ≫ cechAug (Spec.map e) = b)
      (c : sch.map (Spec.map φ'') ≫ b = a ≫ sch.map (Spec.map φ')),
      Function.Injective (rpull (ZMod q) (sch.map (Spec.map φ')) (sch.map (Spec.map φ'')) a b c (tw q i) n) := by
    intro a b ha hb c
    subst ha hb
    intro x y hxy
    rw [rpull_comp _ _ g _ _ _ _ _ hA h0 c, rpull_comp _ _ g _ _ _ _ _ hA h0 c] at hxy
    exact h1 (hinj hxy)
  exact key _ _ hj hi _

theorem etale_spec {D E : CommRingCat.{0}} (e : D ⟶ E) (he : Et e) : Etale (Spec.map e) :=
  HasRingHomProperty.Spec_iff.mpr he

theorem surj_spec {D E : CommRingCat.{0}} (e : D ⟶ E) (hs : SpS e) : Surjective (Spec.map e) := by
  constructor
  intro x
  obtain ⟨Q, hQ, hQr⟩ := hs x.asIdeal x.isPrime
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQr⟩

theorem cechEqv : CechEqv := by
  intro hH q _ i D Y' E Y'' φ' e u φ'' he hs hpo
  have hpb := isPullback_SpecMap_of_isPushout φ' e u φ'' hpo
  have hE : Etale (Spec.map e) := etale_spec e he
  have hS : Surjective (Spec.map e) := surj_spec e hs
  have hEu : Etale (Spec.map u) := MorphismProperty.of_isPullback (P := @Etale) hpb.flip hE
  have hSu : Surjective (Spec.map u) := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  exact ⟨hH.2.1 (ZMod q) (Spec.map e) (tw q i), hH.2.1 (ZMod q) (Spec.map u) (tw q i)⟩

end LateralTheory.E.RelDescPf
end
end

