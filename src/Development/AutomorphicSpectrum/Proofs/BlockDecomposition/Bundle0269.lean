import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import GroundTheory.GlobalFields.Adele.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0137
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxProduct

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDiagonalTwoPlaces
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.DensePair

variable {F : Type} [Field F] [NumberField F]

theorem idem_mul_of_subset {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))}
    {a b : AF F} (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂) :
    b * a = a := by
  refine adele_ext ?_ (finAdele_ext fun v => ?_)
  · rw [map_mul]
    funext w
    change fstA F b w * fstA F a w = fstA F a w
    by_cases hw : w ∈ A₁
    · rw [hb.1 w (h₁ hw), one_mul]
    · rw [ha.2.1 w hw, mul_zero]
  · rw [map_mul, map_mul]
    by_cases hv : v ∈ A₂
    · rw [hb.2.2.1 v (h₂ hv), one_mul]
    · rw [ha.2.2.2 v hv, mul_zero]

theorem idem_mul_of_disjoint {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))}
    {a b : AF F} (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁)
    (h₂ : Disjoint A₂ B₂) : a * b = 0 := by
  refine adele_ext ?_ (finAdele_ext fun v => ?_)
  · rw [map_mul, map_zero]
    funext w
    change fstA F a w * fstA F b w = 0
    by_cases hw : w ∈ A₁
    · rw [hb.2.1 w (Finset.disjoint_left.1 h₁ hw), mul_zero]
    · rw [ha.2.1 w hw, zero_mul]
  · rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hv : v ∈ A₂
    · rw [hb.2.2.2 v (Finset.disjoint_left.1 h₂ hv), mul_zero]
    · rw [ha.2.2.2 v hv, zero_mul]

def sumIdem (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) : AF F :=
  ∑ w : S₁, (placeMapInf w.1).inj 1 + ∑ v : S₂, (placeMapFin v.1).inj 1

def glue (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F)))
    (p : (∀ v : S₂, v.1.adicCompletion F) × (∀ w : S₁, w.1.Completion)) : AF F :=
  ∑ w : S₁, (placeMapInf w.1).inj (p.2 w) + ∑ v : S₂, (placeMapFin v.1).inj (p.1 v)

theorem continuous_glue (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (glue S₁ S₂) := by
  unfold glue
  refine Continuous.add ?_ ?_
  · exact continuous_finset_sum _ fun w _ =>
      (placeMapInf w.1).cont_inj.comp ((continuous_apply w).comp continuous_snd)
  · exact continuous_finset_sum _ fun v _ =>
      (placeMapFin v.1).cont_inj.comp ((continuous_apply v).comp continuous_fst)

theorem glue_proj (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (a : AF F) :
    glue S₁ S₂ (fun v => (placeMapFin v.1).proj a, fun w => (placeMapInf w.1).proj a) = sumIdem S₁ S₂ * a := by
  simp only [glue, sumIdem, PlaceMap.inj_proj, add_mul, Finset.sum_mul]

theorem inf_proj_inf_ne {w u : InfinitePlace F} (h : w ≠ u) (y : u.Completion) :
    (placeMapInf w).proj ((placeMapInf u).inj y) = 0 :=
  singleI_ne h y

theorem inf_proj_fin (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    (placeMapInf w).proj ((placeMapFin v).inj y) = 0 := rfl

theorem fin_proj_inf (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) (y : w.Completion) :
    (placeMapFin v).proj ((placeMapInf w).inj y) = 0 :=
  map_zero (evalV F v)

theorem fin_proj_fin_ne {v u : HeightOneSpectrum (𝓞 F)} (h : v ≠ u) (y : u.adicCompletion F) :
    (placeMapFin v).proj ((placeMapFin u).inj y) = 0 :=
  StrongApprox.evalV_single_ne h y

theorem isPlacesIdem_sumIdem (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    IsPlacesIdem S₁ S₂ (sumIdem S₁ S₂) := by
  classical
  have hI : ∀ w, (placeMapInf w).proj (sumIdem S₁ S₂) =
      ∑ u : S₁, (placeMapInf w).proj ((placeMapInf u.1).inj 1) := by
    intro w
    simp only [sumIdem, map_add, map_sum, inf_proj_fin, Finset.sum_const_zero, add_zero]
  have hF : ∀ v, (placeMapFin v).proj (sumIdem S₁ S₂) =
      ∑ u : S₂, (placeMapFin v).proj ((placeMapFin u.1).inj 1) := by
    intro v
    simp only [sumIdem, map_add, map_sum, fin_proj_inf, Finset.sum_const_zero, zero_add]
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · refine (hI w).trans ?_
    rw [Finset.sum_eq_single (⟨w, hw⟩ : S₁)]
    · exact (placeMapInf w).proj_inj 1
    · intro u _ hu
      exact inf_proj_inf_ne (fun h => hu (Subtype.ext h.symm)) 1
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine (hI w).trans (Finset.sum_eq_zero fun u _ => ?_)
    exact inf_proj_inf_ne (fun h : w = u.1 => hw (by rw [h]; exact u.2)) 1
  · refine (hF v).trans ?_
    rw [Finset.sum_eq_single (⟨v, hv⟩ : S₂)]
    · exact (placeMapFin v).proj_inj 1
    · intro u _ hu
      exact fin_proj_fin_ne (fun h => hu (Subtype.ext h.symm)) 1
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine (hF v).trans (Finset.sum_eq_zero fun u _ => ?_)
    exact fin_proj_fin_ne (fun h : v = u.1 => hv (by rw [h]; exact u.2)) 1

section Two

variable {K₁ K₂ : Type} [Field K₁] [Algebra F K₁] [TopologicalSpace K₁] [Field K₂] [Algebra F K₂]
  [TopologicalSpace K₂]

theorem proj_idem_one (P : PlaceMap F K₁) {A₁ B₁ : Finset (InfinitePlace F)}
    {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {d : AF F} (hP : IsPlacesIdem A₁ A₂ (P.inj 1))
    (hd : IsPlacesIdem B₁ B₂ d) (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂) : P.proj d = 1 := by
  have h := congrArg P.proj (idem_mul_of_subset hP hd h₁ h₂)
  rwa [map_mul, P.proj_inj, mul_one] at h

theorem proj_inj_other (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂) (h : P₁.inj 1 * P₂.inj 1 = 0) (x : K₂) :
    P₁.proj (P₂.inj x) = 0 := by
  have e : P₂.inj x = P₂.inj 1 * P₂.inj x := by
    have := P₂.inj_proj (P₂.inj x)
    rwa [P₂.proj_inj] at this
  have h0 : P₁.proj (P₂.inj 1) = 0 := by
    have := congrArg P₁.proj h
    rwa [map_mul, P₁.proj_inj, one_mul, map_zero] at this
  rw [e, map_mul, h0, zero_mul]

end Two

theorem denseRange_pair {K₁ K₂ : Type} [Field K₁] [Algebra F K₁] [TopologicalSpace K₁] [Field K₂] [Algebra F K₂]
    [TopologicalSpace K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂) {A₁ B₁ : Finset (InfinitePlace F)}
    {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} (h₁ : IsPlacesIdem A₁ A₂ (P₁.inj 1))
    (h₂ : IsPlacesIdem B₁ B₂ (P₂.inj 1)) (d₁ : Disjoint A₁ B₁) (d₂ : Disjoint A₂ B₂) :
    DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) := by
  classical
  have hD := isPlacesIdem_sumIdem (A₁ ∪ B₁) (A₂ ∪ B₂)
  have p₁ : P₁.proj (sumIdem (A₁ ∪ B₁) (A₂ ∪ B₂)) = 1 :=
    proj_idem_one P₁ h₁ hD Finset.subset_union_left Finset.subset_union_left
  have p₂ : P₂.proj (sumIdem (A₁ ∪ B₁) (A₂ ∪ B₂)) = 1 :=
    proj_idem_one P₂ h₂ hD Finset.subset_union_right Finset.subset_union_right
  have z₁ : P₁.inj 1 * P₂.inj 1 = 0 := idem_mul_of_disjoint h₁ h₂ d₁ d₂
  have z₂ : P₂.inj 1 * P₁.inj 1 = 0 := by rw [mul_comm]; exact z₁
  let G := fun p => (P₁.proj (glue (A₁ ∪ B₁) (A₂ ∪ B₂) p), P₂.proj (glue (A₁ ∪ B₁) (A₂ ∪ B₂) p))
  have hG : Continuous G :=
    (P₁.cont_proj.comp (continuous_glue _ _)).prodMk (P₂.cont_proj.comp (continuous_glue _ _))
  have hval : ∀ a : AF F, G (fun v => (placeMapFin v.1).proj a, fun w => (placeMapInf w.1).proj a) =
      (P₁.proj a, P₂.proj a) := by
    intro a
    simp only [G, glue_proj, map_mul, p₁, p₂, one_mul]
  have hsurj : Function.Surjective G := by
    rintro ⟨x₁, x₂⟩
    refine ⟨_, (hval (P₁.inj x₁ + P₂.inj x₂)).trans ?_⟩
    rw [map_add, map_add, P₁.proj_inj, P₂.proj_inj, proj_inj_other P₁ P₂ z₁, proj_inj_other P₂ P₁ z₂, add_zero,
      zero_add]
  have hdense := hsurj.denseRange.comp (GroundTheory.Global.denseRange_algebraMap_prod_pi (A₂ ∪ B₂) (A₁ ∪ B₁)) hG
  convert hdense using 1
  funext f
  have := hval (algebraMap F (AF F) f)
  simp only [AlgHom.commutes] at this
  exact this.symm

end GlobalTheory.CompanionTheory.SaGen.DensePair
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowersOnFiltration
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

noncomputable section

namespace GlobalTheory.CompanionTheory.RedInEx

section Abstract

variable {A : Type} [CommRing A] {I : Ideal A} {γ : DividedPowers I} {l s : ℕ}

theorem one_eq (γ : DividedPowers I) : pdP γ 1 = I := by
  refine le_antisymm (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_one_le γ) fun x hx => ?_
  have h := GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ 1 hx
  rwa [γ.dpow_one hx] at h

theorem mem_of_pow_mul (hb : TFBase γ l s) (N : ℕ) (x : A) (h : (l : A) ^ N * x ∈ I) : x ∈ I := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih ?_
    have := hb.tf 1 ((l : A) ^ N * x) (by
      rw [one_eq]
      rwa [pow_succ', mul_assoc] at h)
    rwa [one_eq] at this

theorem eq_zero_of_pow_mul (hb : TFBase γ l s) (N : ℕ) (x : A) (h : (l : A) ^ N * x = 0) : x = 0 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih ?_
    have := hb.tf s ((l : A) ^ N * x) (by
      rw [hb.nil]
      rw [pow_succ', mul_assoc] at h
      exact h)
    rw [hb.nil] at this
    exact this

theorem mem_of_fact_mul (hb : TFBase γ l s) (k : ℕ) (x : A) (h : (k.factorial : A) * x ∈ I) : x ∈ I := by
  obtain ⟨N, u, hu⟩ := hb.dv _ k.factorial_ne_zero
  refine mem_of_pow_mul hb N x ?_
  rw [← hu, mul_comm _ u, mul_assoc]
  exact Ideal.mul_mem_left _ _ h

theorem eq_of_fact_mul (hb : TFBase γ l s) (k : ℕ) {x y : A} (h : (k.factorial : A) * x = (k.factorial : A) * y) :
    x = y := by
  obtain ⟨N, u, hu⟩ := hb.dv _ k.factorial_ne_zero
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_mul hb N _ ?_
  rw [← hu, mul_comm _ u, mul_assoc, mul_sub, h, sub_self, mul_zero]

theorem dpow_congr (hb : TFBase γ l s) {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (h : Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) x = Ideal.Quotient.mk _ y) (k : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) (γ.dpow k x) = Ideal.Quotient.mk _ (γ.dpow k y) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have haI : a ∈ I := mem_of_pow_mul hb n a (by rw [mul_comm, ha]; exact sub_mem hx hy)
  have hc : (l : A) ^ n * a ∈ I := Ideal.mul_mem_left _ _ haI
  have e : x = y + (l : A) ^ n * a := by rw [mul_comm, ha]; ring
  rw [e, γ.dpow_add hy hc, map_sum, Finset.sum_eq_single (k, 0)]
  · rw [γ.dpow_zero hc, mul_one]
  · rintro ⟨i, j⟩ hij hne
    have hj : j ≠ 0 := by
      rintro rfl
      have : i = k := by simpa using hij
      exact hne (by rw [this])
    change Ideal.Quotient.mk _ (γ.dpow i y * γ.dpow j ((l : A) ^ n * a)) = 0
    rw [γ.dpow_mul haI, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (by
      rw [pow_succ]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · intro h0
    exact absurd (by simp) h0

end Abstract

section Concrete

open PAlg

variable {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A]

def e0 (l : ℕ) [Fact l.Prime] : Acris0 l ≃+* (base l).Acr0 :=
  RingEquiv.ofBijective (base l).cris0 (RL.base_acr (base l) isBase_base).1.1

def lam0 (lam : Acris l →+* A) : (base l).Acr0 →+* A :=
  (lam.comp (algebraMap (Acris0 l) (Acris l))).comp (e0 l).symm.toRingHom

theorem lam0_cris0_eq_lam_of (lam : Acris l →+* A) (y : Acris0 l) :
    lam0 lam ((base l).cris0 y) = lam (AdicCompletion.of _ _ y) := by
  have h : (e0 l).symm ((base l).cris0 y) = y := (e0 l).symm_apply_apply y
  change lam (algebraMap (Acris0 l) (Acris l) ((e0 l).symm ((base l).cris0 y))) = _
  rw [h]
  rfl

theorem lam0_algebraMap_sW_eq_lam_algebraMap (lam : Acris l →+* A) (w : Ainf l) :
    lam0 lam (algebraMap (base l).W (base l).Acr0 ((base l).sW w)) = lam (algebraMap (Ainf l) (Acris l) w) := by
  have h : algebraMap (base l).W (base l).Acr0 ((base l).sW w) = (base l).cris0 (algebraMap (Ainf l) (Acris0 l) w) :=
    Subtype.ext (awayW_algebraMap (base l).s w).symm
  rw [h, lam0_cris0_eq_lam_of, AdicCompletion.algebraMap_apply]

def rho (lam : Acris l →+* A) (n : ℕ) : (base l).Acr n →+* A ⧸ Ideal.span {(l : A) ^ n} :=
  ((base l).cris n).liftOfSurjective ((RL.base_acr (base l) isBase_base).2 n).1
    ⟨(Ideal.Quotient.mk _).comp lam, fun x hx => by
      rw [((RL.base_acr (base l) isBase_base).2 n).2] at hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      have hz : Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) ((l : A) ^ n) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_mul, map_pow, map_natCast, hz, mul_zero]⟩

theorem rho_cris (lam : Acris l →+* A) (n : ℕ) (c : Acris l) :
    rho lam n ((base l).cris n c) = Ideal.Quotient.mk _ (lam c) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ c

theorem rho_mk (lam : Acris l →+* A) (n : ℕ) (y : (base l).Acr0) :
    rho lam n ((base l).mkAcr n y) = Ideal.Quotient.mk _ (lam0 lam y) := by
  obtain ⟨y, rfl⟩ := (e0 l).surjective y
  change rho lam n ((base l).mkAcr n ((base l).cris0 y)) = Ideal.Quotient.mk _ (lam0 lam ((base l).cris0 y))
  rw [← cris_of, rho_cris, lam0_cris0_eq_lam_of]

variable {I : Ideal A} {γ : DividedPowers I} {s : ℕ}

theorem lam0_mem_of_mem_fil0_one (hb : TFBase γ l s) (lam : Acris l →+* A)
    (hξ : lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I) {x : (base l).Acr0} (hx : x ∈ (base l).Fil0 1) :
    lam0 lam x ∈ I := by
  have : (base l).Fil0 1 ≤ I.comap (lam0 lam) := by
    rw [Fil0, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    refine mem_of_fact_mul hb k _ ?_
    rw [← map_natCast (lam0 lam), ← map_mul, (RL.filtration_multiplicative (base l)).2.2.1 k, map_pow]
    refine Ideal.pow_mem_of_mem _ ?_ _ hk
    rw [show (base l).xi = (base l).sW (xi0 l) from rfl, lam0_algebraMap_sW_eq_lam_algebraMap]
    exact hξ
  exact this hx

theorem lam0_dpow (hb : TFBase γ l s) (lam : Acris l →+* A)
    (hξ : lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I) {x z : (base l).Acr0} (hx : x ∈ (base l).Fil0 1) (k : ℕ)
    (hz : (k.factorial : (base l).Acr0) * z = x ^ k) : lam0 lam z = γ.dpow k (lam0 lam x) := by
  refine eq_of_fact_mul hb k ?_
  rw [γ.factorial_mul_dpow_eq_pow (lam0_mem_of_mem_fil0_one hb lam hξ hx), ← map_natCast (lam0 lam), ← map_mul, hz, map_pow]

theorem exists_unit_one_add_generator (x : (base l).Acr0) (hx : x ∈ (base l).Fil0 1) (k : ℕ) :
    ∃ z : (base l).Acr0, (k.factorial : (base l).Acr0) * z = x ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨1, by simp⟩
  · obtain ⟨z, -, hz⟩ := (RL.pdi (base l)).1 x hx k hk
    exact ⟨z, hz⟩

end Concrete

theorem redIn_ex : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {A : Type} [CommRing A] [Algebra (OK l K) A]
    {I : Ideal A} (γ : DividedPowers I) (s : ℕ) (lam : Acris l →+* A), TFBase γ l s →
    lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I →
    (∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a → algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w) ∈ I) →
    ∀ n : ℕ, ∃ d : RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) γ l n,
      ∀ c, d.ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (lam c) := by
  intro l _ K A _ _ I γ s lam hb hξ hO n
  have hfil : ∀ x ∈ (PAlg.base l).Fil n 1, ∃ x₀ ∈ (PAlg.base l).Fil0 1, (PAlg.base l).mkAcr n x₀ = x := by
    intro x hx
    rw [((PAlg.base l).isPd_pdFil n).1] at hx
    exact (Ideal.mem_map_iff_of_surjective _ ((PAlg.base l).mkAcr_surjective n)).1 hx
  refine ⟨{ hl := (Fact.out : l.Prime).ne_zero, ρ := rho lam n, mem := ?_, dp := ?_, hκ := ?_ }, rho_cris lam n⟩
  · intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hfil x hx
    exact ⟨lam0 lam x₀, lam0_mem_of_mem_fil0_one hb lam hξ hx₀, rho_mk lam n x₀⟩
  · intro k x hx y hy e
    obtain ⟨x₀, hx₀, rfl⟩ := hfil x hx
    obtain ⟨z, hz⟩ := exists_unit_one_add_generator x₀ hx₀ k
    have e1 : (B.DD false (PAlg.base l) n).dpow k ((PAlg.base l).mkAcr n x₀) = (PAlg.base l).mkAcr n z :=
      ((PAlg.base l).isPd_pdFil n).2 k x₀ z hx₀ hz
    rw [e1, rho_mk, lam0_dpow hb lam hξ hx₀ k hz]
    rw [rho_mk] at e
    exact dpow_congr hb (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) hy e k
  · intro a r h
    obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l (okToOC l K a)
    have h1 : B.κb (okToOC l K) false n a = Ideal.Quotient.mk _ ((PAlg.base l).toAcr n ((PAlg.base l).sW w)) := by
      change B.uJ false (PAlg.base l) n ((PAlg.base l).oC (okToOC l K a)) = _
      rw [← hw, PAlg.oC_theta0, B.uJ_th]
    rw [h1] at h
    have h2 : r - (PAlg.base l).toAcr n ((PAlg.base l).sW w) ∈ (PAlg.base l).Fil n 1 :=
      Ideal.Quotient.eq.1 h.symm
    obtain ⟨x₀, hx₀, e⟩ := hfil _ h2
    have h3 : rho lam n r = Ideal.Quotient.mk _ (lam (algebraMap (Ainf l) (Acris l) w) + lam0 lam x₀) := by
      rw [map_add, ← rho_mk, e, ← PAlg.cris_algebraMap, ← rho_cris, PAlg.cris_algebraMap, map_sub, add_sub_cancel]
    refine ⟨lam0 lam x₀ - (algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w)),
      sub_mem (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) (hO a w hw), ?_⟩
    rw [h3]
    congr 1
    ring

end GlobalTheory.CompanionTheory.RedInEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDerivationExt
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.DerivExt

theorem exists_derivation_ext {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →+* B) (hf : f.comp (algebraMap K A) = algebraMap K B) (M : Submonoid A)
    (hloc : letI := f.toAlgebra; IsLocalization M B) (D : Derivation K A A) :
    ∃ p : Derivation K B B, ∀ x, p (f x) = f (D x) := by
  letI := f.toAlgebra
  let φ : A →+* TrivSqZeroExt B B :=
    { toFun := fun x => (f x, f (D x))
      map_one' := by
        ext <;> simp
      map_zero' := by
        ext <;> simp
      map_add' := fun x y => by
        ext <;> simp
      map_mul' := fun x y => by
        ext
        · simp
        · simp [Derivation.leibniz]
          ring }
  have hu : ∀ y : M, IsUnit (φ y) := fun y => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact IsLocalization.map_units B y
  let ψ : B →+* TrivSqZeroExt B B := IsLocalization.lift hu
  have hψ : ∀ x, ψ (f x) = φ x := fun x => IsLocalization.lift_eq hu x
  have hfst : ∀ b, (ψ b).fst = b := by
    have : (TrivSqZeroExt.fstHom B B B).toRingHom.comp ψ = RingHom.id B :=
      IsLocalization.ringHom_ext M (RingHom.ext fun x => by
        change (ψ (f x)).fst = f x
        rw [hψ]; rfl)
    exact fun b => congrArg (· b) (congrArg DFunLike.coe this)
  have hmul : ∀ b c, (ψ (b * c)).snd = b * (ψ c).snd + c * (ψ b).snd := fun b c => by
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul]
    simp [hfst, mul_comm]
  have hadd : ∀ b c, (ψ (b + c)).snd = (ψ b).snd + (ψ c).snd := fun b c => by
    rw [map_add, TrivSqZeroExt.snd_add]
  have hsm : ∀ (k : K) b, (ψ (k • b)).snd = k • (ψ b).snd := fun k b => by
    have e : algebraMap K B k = f (algebraMap K A k) := (congrArg (· k) (congrArg DFunLike.coe hf)).symm
    rw [Algebra.smul_def, Algebra.smul_def, hmul, e, hψ]
    have : (φ (algebraMap K A k)).snd = 0 := by
      change f (D _) = 0
      rw [Derivation.map_algebraMap, map_zero]
    rw [this, mul_zero, add_zero]
  let L : B →ₗ[K] B :=
    { toFun := fun b => (ψ b).snd
      map_add' := hadd
      map_smul' := hsm }
  refine ⟨Derivation.mk' L fun b c => ?_, fun x => ?_⟩
  · change (ψ (b * c)).snd = b • (ψ c).snd + c • (ψ b).snd
    rw [hmul]; rfl
  · change (ψ (f x)).snd = _
    rw [hψ]; rfl

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {V : X.Opens}, IsAffineOpen V → ∀ (a : Γ(X, V)),
    letI := (strV q V).toAlgebra
    letI := (strV q (X.basicOpen a)).toAlgebra
    ∀ {d : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), ∃ p : Fin d → Derivation K Γ(X, X.basicOpen a) Γ(X, X.basicOpen a),
      ∀ k x, p k (rs (X.basicOpen_le a) x) = rs (X.basicOpen_le a) (D k x) := by
  intro K _ X q V hV a
  letI := (strV q V).toAlgebra
  letI := (strV q (X.basicOpen a)).toAlgebra
  intro d D
  have hloc : letI := (rs (X.basicOpen_le a)).toAlgebra; IsLocalization (Submonoid.powers a) Γ(X, X.basicOpen a) := by
    letI := (rs (X.basicOpen_le a)).toAlgebra
    exact hV.isLocalization_basicOpen a
  have hf : (rs (X.basicOpen_le a)).comp (algebraMap K Γ(X, V)) = algebraMap K Γ(X, X.basicOpen a) :=
    GlobalTheory.CompanionTheory.CoordRes.rs_comp_strV q _
  choose p hp using fun k => exists_derivation_ext _ hf _ hloc (D k)
  exact ⟨p, hp⟩

end GlobalTheory.CompanionTheory.ConeLocal.DerivExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLubinTateCharacterUnitary
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTHodge

theorem exists_lubinTateChar : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l), ∃ χ : ↥(GK K) →* (↥K.1)ˣ, IsLTChar K χ ∧
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) ∧ ∀ g, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ = 1 :=
  fun K => GlobalTheory.CompanionTheory.LTHodge.CharEx.exists_ltChar K

end GlobalTheory.CompanionTheory.LTHodge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceTopIdeal
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Unit

theorem eq_top_of_killed_top {X : Scheme.{0}} {E : X.Modules} (S : Subobject E)
    (h : Killed (⊤ : X.IdealSheafData) S) : S = ⊤ := by
  refine top_le_iff.mp ((GlobalTheory.CompanionTheory.GE.le_iff_secs_subset ⊤ S).mpr fun U x _ => ?_)
  have hx := h U 1 (by simp [Scheme.IdealSheafData.ideal_top]) x
  rwa [one_smul] at hx

theorem statement_top {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] : Statement I (⊤ : X.IdealSheafData) := by
  intro E _ S hS hann hprop
  have htop : ∀ e, S e = ⊤ := fun e => GlobalTheory.CompanionTheory.GE.Unit.eq_top_of_killed_top (S e) (hann e)
  obtain ⟨hqc, -, -⟩ := hS
  unfold GlobalTheory.CompanionTheory.GE.Alg
  refine ⟨S 0, hqc 0, hprop, fun e => ?_⟩
  rw [htop 0, htop e, top_sup_eq]

end GlobalTheory.CompanionTheory.GE.Unit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxProductStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_strong_approx_product : Sa2.PropProd := by
  first | exact @GlobalTheory.CompanionTheory.Sa2Prod.propProd | exact GlobalTheory.CompanionTheory.Sa2Prod.propProd | (intros; apply GlobalTheory.CompanionTheory.Sa2Prod.propProd <;> assumption)
end

