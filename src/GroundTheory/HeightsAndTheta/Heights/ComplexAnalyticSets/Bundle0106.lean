import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PDehomogOrd
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0089
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SliceComponents

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type} [Field F] {n : ℕ}

theorem isHomogIdeal_sup_linForm {J : Ideal (MvPolynomial (Fin n) F)} (hJ : IsHomogIdeal J) (u : Fin n → F) :
    IsHomogIdeal (J ⊔ Ideal.span {linForm u}) := by
  rw [isHomogIdeal_iff_isHomogeneous_degree] at hJ ⊢
  refine hJ.sup (Ideal.homogeneous_span _ _ fun x hx => ?_)
  rw [Set.mem_singleton_iff.mp hx]
  exact ⟨1, (mem_homogeneousSubmodule _ _).mpr (ChartLocDomain.linForm_isHomogeneous u)⟩

theorem le_of_le_sup {V W : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F} (hV : IsHomogIdeal V)
    (hW : W.IsPrime) (hWh : IsHomogIdeal W) (ht : linForm t ∉ W) (h : V ≤ W ⊔ Ideal.span {linForm t - 1}) :
    V ≤ W := fun g hg => by
  rw [← sum_homogeneousComponent g]
  exact Ideal.sum_mem _ fun d _ => ChartDehomog.proof F n W t _ d hW hWh ht
    (homogeneousComponent_isHomogeneous d g) (h (hV g hg d))

theorem isPrime_sup {W : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F} (hW : W.IsPrime)
    (hH : IsHomogIdeal W) (ht : linForm t ∉ W) : (W ⊔ Ideal.span {linForm t - 1}).IsPrime := by
  set a : MvPolynomial (Fin n) F ⧸ W := Ideal.Quotient.mk W (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  have hM := powers_le_nonZeroDivisors_of_noZeroDivisors ha
  have : IsDomain A := IsLocalization.isDomain_localization hM
  let v : A := IsLocalization.Away.invSelf a
  let φ : MvPolynomial (Fin n) F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ W) A).comp (Ideal.Quotient.mkₐ F W)
  have hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g := fun g => by
    rw [← comp_aeval_apply]; simp
  let ψ : MvPolynomial (Fin n) F →ₐ[F] A := aeval fun m => v * φ (X m)
  have hhom : ∀ {g : MvPolynomial (Fin n) F} {k : ℕ}, g.IsHomogeneous k → ψ g = v ^ k * φ g :=
    fun hg => by rw [← hφ]; exact ChartLocDomain.aeval_mul_of_isHomogeneous hg _ _
  have hle : W ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    refine sup_le (fun g hg => ?_) ?_
    · rw [RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hhom (homogeneousComponent_isHomogeneous k g)]
      have : φ (homogeneousComponent k g) = 0 := by
        simp [φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hH g hg k)]
      rw [this, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
        hhom (ChartLocDomain.linForm_isHomogeneous t), pow_one]
      have : φ (linForm t) = algebraMap _ A a := rfl
      rw [this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
  have hv : IsUnit v := IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf a)
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ W) A) := IsLocalization.injective A hM
  suffices e : RingHom.ker ψ = W ⊔ Ideal.span {linForm t - 1} by rw [← e]; exact RingHom.ker_isPrime _
  refine le_antisymm (fun g hg => ?_) hle
  obtain ⟨G, D, hG, hGg⟩ :=
    ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) g (ChartLocDomain.linForm_isHomogeneous t)
  have h1 := hle (Ideal.mem_sup_right hGg)
  rw [RingHom.mem_ker, map_sub, (RingHom.mem_ker).mp hg, sub_zero, hhom hG] at h1
  have h2 : algebraMap _ A (Ideal.Quotient.mk W G) = 0 := (hv.pow D).mul_right_eq_zero.mp h1
  have hGW : G ∈ W := Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h2.trans (map_zero _).symm))
  rw [show g = G - (G - g) by ring]
  exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)

theorem mem_support_divCycle {J W : Ideal (MvPolynomial (Fin n) F)} {u : Fin n → F} :
    W ∈ (divCycle J u).support ↔
      W ∈ relComps (J ⊔ Ideal.span {linForm u}) ∧ localMult (J ⊔ Ideal.span {linForm u}) W ≠ 0 := by
  classical
  simp only [divCycle, fundCycle, Finsupp.mem_support_iff, Finsupp.onFinset_apply]
  split_ifs with h <;> simp [h]

theorem divCycle_apply {J W : Ideal (MvPolynomial (Fin n) F)} {u : Fin n → F}
    (h : W ∈ relComps (J ⊔ Ideal.span {linForm u})) :
    divCycle J u W = localMult (J ⊔ Ideal.span {linForm u}) W := by
  classical
  simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
  rw [if_pos h]

theorem localMult_ne_zero {A : Type} [CommRing A] [IsNoetherianRing A] {J W : Ideal A} {x : A}
    (hW : W ∈ (J ⊔ Ideal.span {x}).minimalPrimes) : localMult (J ⊔ Ideal.span {x}) W ≠ 0 := by
  have := hW.1.1
  have hP : (W.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact le_sup_left.trans hW.1.2)
  intro h0
  have e := LocalMultOrd.proof A J W x hW
  rw [h0, Nat.cast_zero, eq_comm, Ring.ord, Module.length_eq_zero_iff,
    Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top] at e
  have hx : Ideal.Quotient.mk J x ∈ W.map (Ideal.Quotient.mk J) :=
    Ideal.mem_map_of_mem _ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mp e hx

theorem mem_support_iff {J W : Ideal (MvPolynomial (Fin n) F)} {u ℓ : Fin n → F}
    (hℓ : ∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) :
    W ∈ (divCycle J u).support ↔ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes ∧ linForm ℓ ∉ W := by
  refine ⟨fun h => ⟨(mem_support_divCycle.mp h).1.1, hℓ W h⟩, fun ⟨hm, hW⟩ => ?_⟩
  refine mem_support_divCycle.mpr ⟨⟨hm, ?_⟩, localMult_ne_zero hm⟩
  by_contra hr
  simp only [IsRelevant, not_exists, not_not] at hr
  exact hW (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hr j))

end SliceComponents

open SliceComponents in

theorem SliceComponents.proof : SliceComponents.Statement := by
  intro n J u ℓ hJ hℓ
  have := hJ.isPrime
  set K := J ⊔ Ideal.span {linForm u} with hKdef
  set L : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span {linForm ℓ - 1} with hLdef
  have hK : IsHomogIdeal K := isHomogIdeal_sup_linForm hJ.isHomog u
  have hK' : J ⊔ L ⊔ Ideal.span {linForm u} = K ⊔ L := sup_right_comm _ _ _
  have hsupp := fun W => mem_support_iff (W := W) hℓ
  have hhom : ∀ W ∈ K.minimalPrimes, IsHomogIdeal W := fun W hW => MinimalPrimeHomog.proof ℂ n K W hK hW

  have hchart : ∀ Q : Ideal _, Q.IsPrime → K ⊔ L ≤ Q →
      ∃ V, IsProjPrime V ∧ linForm ℓ ∉ V ∧ V ⊔ L = Q ∧ K ≤ V := fun Q hQ hKQ => by
    obtain ⟨V, hV, hℓV, hVQ, hVmax⟩ :=
      ChartHomogenise.proof ℂ n Q ℓ hQ (hKQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact ⟨V, hV, hℓV, hVQ, hVmax K hK (le_sup_left.trans hKQ)⟩
  have hmin : ∀ W ∈ (divCycle J u).support, W ⊔ L ∈ (K ⊔ L).minimalPrimes := fun W hW => by
    obtain ⟨hWm, hℓW⟩ := (hsupp W).mp hW
    have := hWm.1.1
    refine ⟨⟨isPrime_sup hWm.1.1 (hhom W hWm) hℓW, sup_le_sup_right hWm.1.2 _⟩, fun Q ⟨hQ, hKQ⟩ hQW => ?_⟩
    obtain ⟨V, hV, -, hVQ, hKV⟩ := hchart Q hQ hKQ
    have hVW : V ≤ W :=
      le_of_le_sup hV.isHomog hWm.1.1 (hhom W hWm) hℓW ((le_sup_left.trans hVQ.le).trans hQW)
    rw [← hVQ]
    exact sup_le_sup_right (hWm.2 ⟨hV.isPrime, hKV⟩ hVW) _
  refine ⟨fun W₁ h₁ W₂ h₂ (e : W₁ ⊔ L = W₂ ⊔ L) => ?_, ?_, fun W hW => ?_⟩
  · obtain ⟨hm₁, hℓ₁⟩ := (hsupp W₁).mp h₁
    obtain ⟨hm₂, hℓ₂⟩ := (hsupp W₂).mp h₂
    exact le_antisymm
      (le_of_le_sup (hhom W₁ hm₁) hm₂.1.1 (hhom W₂ hm₂) hℓ₂ (e ▸ le_sup_left))
      (le_of_le_sup (hhom W₂ hm₂) hm₁.1.1 (hhom W₁ hm₁) hℓ₁ (e.symm ▸ le_sup_left))
  · rw [hK']
    ext Q
    refine ⟨fun ⟨W, hW, hWQ⟩ => hWQ ▸ hmin W hW, fun hQ => ?_⟩
    have := hQ.1.1
    obtain ⟨V, hV, hℓV, hVQ, hKV⟩ := hchart Q hQ.1.1 hQ.1.2
    have := hV.isPrime
    obtain ⟨W, hWm, hWV⟩ := Ideal.exists_minimalPrimes_le hKV
    have hW : W ∈ (divCycle J u).support := (hsupp W).mpr ⟨hWm, fun h => hℓV (hWV h)⟩
    have hle : W ⊔ L ≤ Q := hVQ ▸ sup_le_sup_right hWV _
    exact ⟨W, hW, le_antisymm hle (hQ.2 (hmin W hW).1 hle)⟩
  · obtain ⟨hWm, hℓW⟩ := (hsupp W).mp hW
    have := hWm.1.1
    have hWL := isPrime_sup hWm.1.1 (hhom W hWm) hℓW
    have hJW : J ≤ W := le_sup_left.trans hWm.1.2
    have : (W.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJW)
    have hmapeq : (W ⊔ L).map (Ideal.Quotient.mk (J ⊔ L)) = W.map (Ideal.Quotient.mk (J ⊔ L)) := by
      have hL0 : L.map (Ideal.Quotient.mk (J ⊔ L)) = ⊥ :=
        (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker]; exact le_sup_right)
      rw [Ideal.map_sup, hL0, sup_bot_eq]
    have hP' : ((W ⊔ L).map (Ideal.Quotient.mk (J ⊔ L))).IsPrime := Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact sup_le_sup_right hJW _)
    have : (W.map (Ideal.Quotient.mk (J ⊔ L))).IsPrime := hmapeq ▸ hP'
    rw [divCycle_apply (mem_support_divCycle.mp hW).1]
    have e₁ := LocalMultOrd.proof _ J W (linForm u) hWm
    have e₂ := DehomogOrd.proof OrdPolynomialLocalization.proof ℂ n J W ℓ hJ.isHomog (hhom W hWm) hJW hℓW
      (linForm u) 1 (ChartLocDomain.linForm_isHomogeneous u)
    have e₃ := LocalMultOrd.proof _ (J ⊔ L) (W ⊔ L) (linForm u) (hK' ▸ hmin W hW)
    have e₄ := ord_atPrime_congr hmapeq (Ideal.Quotient.mk (J ⊔ L) (linForm u))
    exact_mod_cast e₃.trans (e₄.trans (e₂.symm.trans e₁.symm))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLocalDimGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

theorem ringKrullDim_quotient_le_sup_span_add {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R)
    (hI : I ≠ ⊤) {d : ℕ} (t : Fin d → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) + (d : ℕ) := by
  classical
  let s : Finset (R ⧸ I) := Finset.univ.image fun i => Ideal.Quotient.mk I (t i)
  have hs : Ideal.span (s : Set (R ⧸ I)) = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp [s]
  have hjac : (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) ≤ Ring.jacobson (R ⧸ I) := by
    rw [← Ideal.jacobson_bot, ← Ideal.map_quotient_self I,
      ← Ideal.map_jacobson_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]),
      IsLocalRing.jacobson_eq_maximalIdeal I hI]
    refine Ideal.map_mono ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ht i
  have hkey := ringKrullDim_le_ringKrullDim_quotient_add_card s
    fun x hx => hjac (hs ▸ Ideal.subset_span hx)
  rw [hs, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)] at hkey
  refine hkey.trans ?_
  gcongr
  exact_mod_cast Finset.card_image_le.trans (by simp)

theorem one_le_ringKrullDim_localRingAt_sliceIdeal {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ)
    (hdim : ringKrullDim (localRingAt J q) = (d + 1 : ℕ)) :
    ((1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) := by
  let φ := algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))
  let t : Fin d → MvPolynomial (Fin n) ℂ := fun i => linPoly L i - C ((L *ᵥ q) i)
  have hI : J.map φ ≠ ⊤ := by
    intro h
    unfold localRingAt at hdim
    have : Subsingleton (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸
        J.map φ) := Ideal.Quotient.subsingleton_iff.mpr h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have ht : ∀ i, φ (t i) ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) := by
    intro i
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine Ideal.mem_map_of_mem _ ?_
    simp [t, RingHom.mem_ker, eval_linPoly]
  have hkey := ringKrullDim_quotient_le_sup_span_add (J.map φ) hI (fun i => φ (t i)) ht
  have hsl : (sliceIdeal J L q).map φ = J.map φ ⊔ Ideal.span (Set.range fun i => φ (t i)) := by
    rw [sliceIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [← hsl] at hkey
  change ringKrullDim (localRingAt J q) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) + (d : ℕ)
    at hkey
  rw [hdim] at hkey
  generalize ringKrullDim (localRingAt (sliceIdeal J L q) q) = D at hkey ⊢
  induction D using WithBot.recBotCoe with
  | bot => simp at hkey
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe k =>
      have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((k + d : ℕ) : WithBot ℕ∞) := by simpa using hkey
      have h3 : d + 1 ≤ k + d := by exact_mod_cast h2
      exact_mod_cast (show 1 ≤ k by omega)

theorem SliceLocalDimGeneral.proof (hL : LocalDimDomain.Statement)
    (hU : SliceLocalDimUpperZariski.Statement) : SliceLocalDimGeneral.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨F, hF, hgood⟩ := hU n d J q hJ hdim hq
  have hloc := hL n (d + 1) J hJ hdim q hq
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let ψ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hψ : Continuous ψ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hLF => le_antisymm (hgood L hLF)
    (one_le_ringKrullDim_localRingAt_sliceIdeal J L q hloc)⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ := exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hψ) ⟨e L₀, hL₀⟩
    exact ⟨ψ y, hyU, hyF⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLocalDimUpperZariski
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

theorem SliceLocalDimUpperZariski.ringKrullDim_le_of_finite {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) : ringKrullDim S ≤ ringKrullDim R := by
  let _ := f.toAlgebra
  have : Module.Finite R S := hf
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  refine Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) p) ?_
  intro p p' h
  have h' : p.asIdeal < p'.asIdeal := h
  exact Ideal.IsIntegral.comap_lt_comap (R := R) h'

theorem SliceLocalDimUpperZariski.localDim_le {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (q : Fin n → ℂ) (hq : q ∈ zeroSet I) :
    ringKrullDim (localRingAt I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) := by
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hIM : I ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ I) := M.map (Ideal.Quotient.mk I)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ I) M.primeCompl =
      m.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      change Ideal.Quotient.mk I y ∉ m
      rw [← hzy]
      change Ideal.Quotient.mk I z ∉ M.map (Ideal.Quotient.mk I)
      rw [Ideal.mem_quotient_iff_mem hIM]
      exact hz
    · intro h
      change Ideal.Quotient.mk I y ∉ M.map (Ideal.Quotient.mk I) at h
      rw [Ideal.mem_quotient_iff_mem hIM] at h
      exact ⟨y, h, rfl⟩
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt I q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt I q)]
  exact Ideal.height_le_ringKrullDim_of_isPrime

theorem SliceLocalDimUpperZariski.quotient_dim_le_one {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) (M : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (hML : ∀ i j, M (Fin.castSucc i) j = L i j) (hfin : (projHom J M).toRingHom.Finite) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q) ≤ (1 : ℕ) := by
  set I := sliceIdeal J L q with hI
  have hJI : J ≤ I := le_sup_left
  let g : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    (Ideal.Quotient.factor hJI).comp (projHom J M).toRingHom
  have hg : g.Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJI)) hfin
  let π : MvPolynomial (Fin (d + 1)) ℂ →+* Polynomial ℂ :=
    (aeval (Fin.lastCases (motive := fun _ => Polynomial ℂ) Polynomial.X
      (fun k => Polynomial.C ((L *ᵥ q) k)))).toRingHom
  let ψ : Polynomial ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    Polynomial.eval₂RingHom (algebraMap ℂ _) (Ideal.Quotient.mk I (linPoly M (Fin.last d)))
  have hlin : ∀ k : Fin d, linPoly M k.castSucc = linPoly L k := by
    intro k
    simp only [linPoly, hML]
  have hCI : ∀ c : ℂ, algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) c = Ideal.Quotient.mk I (C c) :=
    fun c => rfl
  have hcomp : ψ.comp π = g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [π, ψ, g, projHom, pullback, hCI]
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [π, ψ, g, projHom, pullback]
      · have hmem : linPoly L k - C ((L *ᵥ q) k) ∈ I :=
          Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
        have hq : Ideal.Quotient.mk I (linPoly L k) = Ideal.Quotient.mk I (C ((L *ᵥ q) k)) :=
          Ideal.Quotient.eq.mpr hmem
        simp [π, ψ, g, projHom, pullback, hlin, hq, hCI]
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (f := π) (by rw [hcomp]; exact hg)
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ringKrullDim (Polynomial ℂ) :=
        SliceLocalDimUpperZariski.ringKrullDim_le_of_finite ψ hψ
    _ = (1 : ℕ) := by
        rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        rfl

theorem SliceLocalDimUpperZariski.proof : SliceLocalDimUpperZariski.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hWfin⟩ :=
    ComplexSets.FiniteProjectionsContainOpen.proof ComplexSets.ConeAvoidsFinite.proof
      ComplexSets.FiniteProjHomInjective.proof ComplexSets.ConeAvoidsOpen.proof
      (ComplexSets.ConeAvoidsExists.proof ComplexSets.LeadIdealDim.proof
        ComplexSets.LinearFormCut.proof ComplexSets.HomogDimZeroPow.proof) n (d + 1) J hJ hdim
  rw [hS] at hA₀
  obtain ⟨G, hGS, hG⟩ := hA₀
  let ext : Matrix (Fin d) (Fin n) ℂ → Matrix (Fin (d + 1)) (Fin n) ℂ :=
    fun L i j => if h : (i : ℕ) < d then L ⟨i, h⟩ j else A₀ i j
  let F : MvPolynomial (Fin d × Fin n) ℂ :=
    bind₁ (fun ij : Fin (d + 1) × Fin n =>
      if h : (ij.1 : ℕ) < d then X (⟨ij.1, h⟩, ij.2) else C (A₀ ij.1 ij.2)) G
  have hevF : ∀ L : Matrix (Fin d) (Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F =
        eval (fun ij : Fin (d + 1) × Fin n => ext L ij.1 ij.2) G := by
    intro L
    change eval₂Hom (RingHom.id ℂ) _ (bind₁ _ G) = _
    rw [eval₂Hom_bind₁]
    change eval _ G = _
    refine congrArg (fun f => eval f G) (funext fun ij => ?_)
    simp only [ext]
    split_ifs <;> simp
  have hext0 : ext (fun i j => A₀ i.castSucc j) = A₀ := by
    funext i j
    simp only [ext]
    split_ifs with h
    · rfl
    · rfl
  refine ⟨F, fun h0 => hG ?_, fun L hL => ?_⟩
  · have h1 := hevF (fun i j => A₀ i.castSucc j)
    rw [hext0, h0, map_zero] at h1
    exact h1.symm
  · have hmem : ext L ∈ W := by
      rw [hS]
      exact ⟨G, hGS, (hevF L) ▸ hL⟩
    have hfp : IsFiniteProjection J (ext L) := hWfin hmem
    have hq' : q ∈ zeroSet (sliceIdeal J L q) := by
      rw [zeroSet_sliceIdeal]
      exact ⟨hq, rfl⟩
    refine (SliceLocalDimUpperZariski.localDim_le _ q hq').trans
      (SliceLocalDimUpperZariski.quotient_dim_le_one J L q (ext L) (fun i j => ?_) hfp.finite)
    simp [ext, i.isLt]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem isRadicalAt_of_associatedPrimes {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hA : ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I),
      P ≤ RingHom.ker (eval q) → P ∈ I.minimalPrimes ∧ P ≠ RingHom.ker (eval q))
    (hB : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → I ≤ P → P ≠ RingHom.ker (eval q) →
      ∀ g ∈ I.radical, ∃ s ∉ P, s * g ∈ I) :
    IsRadicalAt I q := by
  intro g hg
  by_contra hno
  simp only [not_exists, not_and] at hno
  have : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  set N : Submodule (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Submodule.span _ {Ideal.Quotient.mk I g}
  have hK : ∀ s, s ∈ Module.annihilator (MvPolynomial (Fin n) ℂ) N ↔ s * g ∈ I := by
    intro s
    change s ∈ N.annihilator ↔ _
    rw [Submodule.mem_annihilator_span_singleton]
    change Ideal.Quotient.mk I s * Ideal.Quotient.mk I g = 0 ↔ _
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hKq : Module.annihilator (MvPolynomial (Fin n) ℂ) N ≤ RingHom.ker (eval q) := by
    intro s hs
    by_contra h
    exact hno s h ((hK s).1 hs)
  obtain ⟨P, hPmin, hPq⟩ := Ideal.exists_minimalPrimes_le hKq
  have hPass : P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    associatedPrimes.subset_of_injective (f := N.subtype) Subtype.val_injective
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes _ _ hPmin)
  obtain ⟨hPI, hPne⟩ := hA P hPass hPq
  obtain ⟨s, hsP, hsg⟩ := hB P hPI.1.1 hPI.1.2 hPne g hg
  exact hsP (hPmin.1.2 ((hK s).2 hsg))

theorem SliceReducedGeneral.proof (hU : SliceUnmixedGeneral.Statement)
    (hB : SliceReducedAway.Statement) : SliceReducedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hU n d J W u hJ hdim hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf q hq hfq
  obtain ⟨O₂, hO₂o, hO₂d, hO₂⟩ := hB n d J q hJ.isRadical
  exact ⟨O₁ ∩ O₂, hO₁o.inter hO₂o, hO₁d.inter_of_isOpen_left hO₂d hO₁o,
    fun L hL => isRadicalAt_of_associatedPrimes (hO₁ L hL.1) (hO₂ L hL.2)⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRegularElement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

def CMRegularElement.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (y : B), y ∈ maximalIdeal B →
    (∀ p ∈ minimalPrimes B, y ∉ p) →
      y ∈ nonZeroDivisors B ∧ IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y})

end GroundTheory.Heights₂.Heights
end

