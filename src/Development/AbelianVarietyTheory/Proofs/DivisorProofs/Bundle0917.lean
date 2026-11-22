import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0585
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0564
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearClosedImmersionProjectiveSpaceCodimT
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.LinearCodimTwo

open GlobalTheory.ProjSpace GlobalTheory.Adelic

theorem exists_linear_closedImmersion_two_le_ringKrullDim_stalk :
    ∀ (F : Type) [Field F] (N : ℕ), ∃ ℓ : PSpace F N ⟶ PSpace F (N + 2), IsClosedImmersion ℓ ∧
      ℓ ≫ PSpace.str F (N + 2) = PSpace.str F N ∧
      ∀ y, 2 ≤ ringKrullDim ((PSpace F (N + 2)).presheaf.stalk (ℓ y)) := by
  intro F _ N
  have h1 : Function.Injective (Fin.castSucc : Fin (N + 1) → Fin (N + 1 + 1)) := Fin.castSucc_injective _
  have h2 : Function.Injective (Fin.castSucc : Fin (N + 1 + 1) → Fin (N + 2 + 1)) := Fin.castSucc_injective _
  let ℓ₁ : PSpace F N ⟶ PSpace F (N + 1) := linearι F h1
  let ℓ₂ : PSpace F (N + 1) ⟶ PSpace F (N + 2) := linearι F h2
  refine ⟨ℓ₁ ≫ ℓ₂, inferInstance, by rw [Category.assoc, linearι_str, linearι_str], fun y => ?_⟩
  have last1 : Fin.last (N + 1) ∉ Set.range (Fin.castSucc : Fin (N + 1) → Fin (N + 1 + 1)) := by
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  have last2 : Fin.last (N + 2) ∉ Set.range (Fin.castSucc : Fin (N + 1 + 1) → Fin (N + 2 + 1)) := by
    rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi
  have n1 : ℓ₁ y ∉ chart F (N + 1) (Fin.last (N + 1)) := fun h => by
    have : y ∈ ℓ₁ ⁻¹ᵁ chart F (N + 1) (Fin.last (N + 1)) := h
    rw [linearι_preimage_chart_of_notMem F h1 last1] at this
    exact this
  have n2 (z : PSpace F (N + 1)) : ℓ₂ z ∉ chart F (N + 2) (Fin.last (N + 2)) := fun h => by
    have : z ∈ ℓ₂ ⁻¹ᵁ chart F (N + 2) (Fin.last (N + 2)) := h
    rw [linearι_preimage_chart_of_notMem F h2 last2] at this
    exact this
  have s1 : projSys.gen F (N + 1) ⤳ ℓ₁ y :=
    specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1
      (show ⊥ ≤ (ℓ₁ y).asHomogeneousIdeal from bot_le))
  have s2 : projSys.gen F (N + 2) ⤳ ℓ₂ (projSys.gen F (N + 1)) :=
    specializes_iff_mem_closure.2 ((ProjectiveSpectrum.le_iff_mem_closure _ _ _).1
      (show ⊥ ≤ (ℓ₂ (projSys.gen F (N + 1))).asHomogeneousIdeal from bot_le))
  have lt1 : ℓ₂ (ℓ₁ y) < ℓ₂ (projSys.gen F (N + 1)) := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2 (s1.map ℓ₂.continuous)) fun h => ?_
    have := ℓ₂.isClosedEmbedding.injective ((Scheme.le_iff_specializes.1 h).antisymm (s1.map ℓ₂.continuous)).eq
    exact n1 (this ▸ projSys.gen_mem F (N + 1) (Fin.last (N + 1)))
  have lt2 : ℓ₂ (projSys.gen F (N + 1)) < projSys.gen F (N + 2) := by
    refine lt_of_le_not_ge ((Scheme.le_iff_specializes).2 s2) fun h => ?_
    have e : ℓ₂ (projSys.gen F (N + 1)) = projSys.gen F (N + 2) := ((Scheme.le_iff_specializes.1 h).antisymm s2).eq
    exact n2 _ (by rw [e]; exact projSys.gen_mem F (N + 2) (Fin.last (N + 2)))
  have hc : (2 : ℕ∞) ≤ Order.coheight (ℓ₂ (ℓ₁ y)) := by
    have a := Order.coheight_add_one_le lt1
    have b := Order.coheight_add_one_le lt2
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (projSys.gen F (N + 2)) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight (ℓ₂ (projSys.gen F (N + 1))) + 1 := by gcongr
      _ ≤ _ := a
  rw [Scheme.Hom.comp_apply, ringKrullDim_stalk_eq_coheight]
  have := WithBot.coe_le_coe.2 hc
  simpa using this

end GlobalTheory.LinearCodimTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLubinTatePeriodElement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
open GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LTPeriodShape

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∃ (ω : AK K) (t u : BK K), thetaK K ω = 0 ∧ ω ∉ RingHom.ker (thetaK K) ^ 2 ∧
      t = toB K (ofA K ω) * (1 + toB K (ofA K ω) * u) ∧ ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  intro l _ K χ π z h
  obtain ⟨hπ, hF, v, hv0, hv1, hv, hg⟩ := GlobalTheory.T.lubin_tate_torsion_sequence l K χ π z h
  have hπu := GlobalTheory.LTTilt.not_isUnit_intToOC K hπ
  have hcomp : ∀ n, v (n + 1) ^ (l ^ fK K) - v n ∈ Ideal.span {intToOC K π} := fun n =>
    Ideal.mem_span_singleton.2 ⟨-v (n + 1), by rw [← hv n]; ring⟩
  obtain ⟨x, hx, -⟩ := GlobalTheory.LTTilt.existsUnique_isTiltOf (fK K) (NeZero.pos _) (intToOC K π) hπu
    (GlobalTheory.LTTilt.natCast_mem_span_intToOC K hπ) v hcomp
  obtain ⟨ω₀, hred, hω₀⟩ := GlobalTheory.T.exists_frobenius_lift_lubin_tate l K π hπ x
  choose r hr using (frobq_bijective K).2
  let ω : ℕ → AK K := fun n => r^[n] ω₀
  have hch : ∀ n, frobq K (ω (n + 1)) = ω n := fun n => by
    simp only [ω, Function.iterate_succ_apply', hr]
  have hθ : ∀ n, thetaK K (ω n) = v n := GlobalTheory.T.theta_of_tilt_compatible_sequence l K π hπ v ω hv (hred ▸ hx) hch hω₀
  have h0 : thetaK K ω₀ = 0 := (hθ 0).trans hv0
  have hne : ω₀ ≠ 0 := fun e => hv1 (by
    have : ω 1 = 0 := (frobq_bijective K).1 (by rw [hch, map_zero]; exact e)
    rw [← hθ, this, map_zero])
  have hker : ∀ (M : ℕ) (y : AK K), ω₀ ^ M ∣ y → y ∈ RingHom.ker (thetaK K) ^ M := fun M y ⟨c, hc⟩ =>
    hc ▸ Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (show ω₀ ∈ RingHom.ker (thetaK K) from h0) M)
  have hev := ev_ltLog hπ hF ω₀ h0
  have hq : resCard K = l ^ fK K := rfl
  have hsq : ω₀ ∉ RingHom.ker (thetaK K) ^ 2 :=
    GlobalTheory.LTPeriodKerSq.not_mem_sq hπ hne h0 (by rw [hq]; exact hω₀)
  obtain ⟨L', u₁, hL', hc, hu₁, ht⟩ := GlobalTheory.AcrisK.ev_shift l K _ (onDisc_log hπ hF) ω₀ h0 _ hev
  obtain ⟨L'', u, -, -, -, hu⟩ := GlobalTheory.AcrisK.ev_shift l K L' hL' ω₀ h0 u₁ hu₁
  refine ⟨ω₀, ltLog hπ hF ω₀ h0, u, h0, hsq, ?_, fun g => ?_⟩
  · rw [ht, hu, hc, PowerSeries.coeff_zero_eq_constantCoeff_apply, GlobalTheory.LTLog.constantCoeff_log _ hπ hF,
      GlobalTheory.LTLog.coeff_one_log _ hπ hF, map_zero, map_one, zero_add]
  · obtain ⟨a, ha, hs⟩ := hg g
    obtain ⟨y, hy1, hy2, hy3⟩ := GlobalTheory.T.exists_compatible_power_series_value l K ω (lubinTateHom hπ hF hF a).toPowerSeries
      (fun n => Per.σO (g : GQ l) (v n)) hch
      (fun n => by rw [hθ]; exact GlobalTheory.LTTilt.norm_lt_one_of_compat K hπ hcomp hv0 n)
      (fun n => by rw [hθ]; exact hs n)
    have hy : gal K g ω₀ = y 0 := sub_eq_zero.1 (GlobalTheory.T.frobenius_compatible_theta_zero l K (fun n => gal K g (ω n) - y n)
      (fun n => by rw [map_sub, hy1, ← gal_frobq, hch])
      (fun n => by rw [map_sub, hy2, thetaK_gal, hθ, sub_self]))
    rw [← ha]
    exact ev_log_hom hπ hF a h0 (fun n => hker n _ (hy ▸ hy3 n)) (hev.gal g)

end GlobalTheory.LTPeriodShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemRangeToF
section
noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.OneFormTest

section Abstract

variable {K : Type} [Field K] {σ : K →+* ℂ} {E : Type} [AddCommGroup E] [Module ℂ E]
  {V : Type} [AddCommGroup V] [Module K V]

theorem exists_coord {I : Type} (ψ : I → E →ₗ[ℂ] ℂ) (ι : V →ₛₗ[σ] E) (h : ∀ x a, ∃ z : K, σ z = ψ a (ι x)) :
    ∃ f : V →ₗ[K] (I → K), ∀ x a, σ (f x a) = ψ a (ι x) := by
  choose f hf using h
  refine ⟨⟨⟨f, fun x y => funext fun a => σ.injective ?_⟩, fun c x => funext fun a => σ.injective ?_⟩, hf⟩
  · rw [Pi.add_apply, map_add, hf, hf, hf, map_add, map_add]
  · simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, map_mul, hf, map_smulₛₗ]

theorem semi_apply_pi {n : ℕ} (ι : (Fin n → K) →ₛₗ[σ] E) (u : Fin n → K) :
    ι u = ∑ a, σ (u a) • ι (Pi.single a 1) := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : (Pi.single a (u a) : Fin n → K) = u a • Pi.single a 1 := by
    funext i; by_cases hi : i = a <;> simp [hi]
  rw [this, map_smulₛₗ]

theorem mem_span_of_ker {H : Type} [AddCommGroup H] [Module ℂ H] {n : ℕ} (ψ : Fin n → E →ₗ[ℂ] ℂ)
    (hψ : ∀ e, (∀ a, ψ a e = 0) → e = 0) (j : V →ₛₗ[σ] H) (hj : Submodule.span ℂ (Set.range j) = ⊤) (Θ : H →ₗ[ℂ] E)
    (h : ∀ x a, ∃ z : K, σ z = ψ a (Θ (j x))) {y : H} (hy : Θ y = 0) :
    y ∈ Submodule.span ℂ (j '' {x | Θ (j x) = 0}) := by
  obtain ⟨f, hf⟩ := exists_coord ψ (Θ.comp j) h
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict f.range_rangeRestrict
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype (Submodule.ker_subtype _)
  have hfg : ∀ x, f (s (p (f x))) = f x := fun x => by
    have h1 : p (f x) = f.rangeRestrict x := congrArg (fun L => L (f.rangeRestrict x)) hp
    have h2 : f.rangeRestrict (s (f.rangeRestrict x)) = f.rangeRestrict x := congrArg (fun L => L (f.rangeRestrict x)) hs
    rw [h1]
    exact congrArg Subtype.val h2
  let L : H →ₗ[ℂ] H := ∑ a, (ψ a ∘ₗ Θ).smulRight (j (s (p (Pi.single a 1))))
  have hL : ∀ y, L y = ∑ a, ψ a (Θ y) • j (s (p (Pi.single a 1))) := fun y => by
    simp only [L, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]
  have hLj : ∀ x, L (j x) = j (s (p (f x))) := fun x => by
    rw [hL]
    refine Eq.trans ?_ (semi_apply_pi (j.comp (s ∘ₗ p)) (f x)).symm
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hf]
    rfl
  have key : Submodule.span ℂ (Set.range j) ≤
      (Submodule.span ℂ (j '' {x | Θ (j x) = 0})).comap (LinearMap.id - L) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    change j x - L (j x) ∈ Submodule.span ℂ _
    rw [hLj, ← map_sub]
    refine Submodule.subset_span ⟨_, hψ _ fun a => ?_, rfl⟩
    have := hf (x - s (p (f x))) a
    rw [map_sub, hfg, sub_self, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h3 : y - L y ∈ Submodule.span ℂ (j '' {x | Θ (j x) = 0}) := key (hj ▸ Submodule.mem_top)
  rwa [hL, hy, Finset.sum_eq_zero fun a _ => by rw [map_zero, zero_smul], sub_zero] at h3

theorem exists_orth [FiniteDimensional K V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : V →ₛₗ[σ] H)
    (hj : Function.Injective j) (hr : ∀ x y, ∃ z : K, σ z = ⟪j x, j y⟫_ℂ) (U : Submodule K V) (x : V) :
    ∃ k ∈ U, ∀ k' ∈ U, ⟪j k', j (x - k)⟫_ℂ = 0 := by
  let b := Module.finBasis K U
  obtain ⟨f, hf⟩ := exists_coord (fun i => innerₛₗ ℂ (j (b i : V))) j fun y i => hr _ y
  have horth : ∀ y, f y = 0 → ∀ k' ∈ U, ⟪j k', j y⟫_ℂ = 0 := by
    intro y hy k' hk'
    have e : k' = ∑ i, b.repr ⟨k', hk'⟩ i • (b i : V) := by
      have := congrArg U.subtype (b.sum_repr ⟨k', hk'⟩)
      rw [map_sum] at this
      exact this.symm
    rw [e, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : ⟪j (b i : V), j y⟫_ℂ = 0 := by
      have := hf y i
      rw [hy, Pi.zero_apply, map_zero] at this
      exact this.symm
    rw [map_smulₛₗ, inner_smul_left, h0, mul_zero]
  have hinj : Function.Injective (f ∘ₗ U.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have := horth u hu u u.2
    rw [inner_self_eq_zero, ← map_zero j] at this
    exact Subtype.ext (hj this)
  have hsurj : Function.Surjective (f ∘ₗ U.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨k, hk⟩ := hsurj (f x)
  exact ⟨k, k.2, horth _ (by rw [map_sub, ← hk]; exact sub_self _)⟩

end Abstract

section Coord

variable {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K) {E : Type} [AddCommGroup E] [Module ℂ E]

theorem injective_and_rat {n d : ℕ} (ψ : Fin n → E →ₗ[ℂ] ℂ) (hψ : ∀ e, (∀ a, ψ a e = 0) → e = 0)
    (ι : (Fin d → ℂ) →ₗ[ℂ] E) (h : ∀ x a, ∃ z : K, v.embedding z = ψ a (ι (cpt v.embedding x)))
    (hι : ∀ x : Fin d → K, ι (cpt v.embedding x) = 0 → x = 0) :
    Function.Injective ι ∧
      ∀ w, (∀ a, ∃ z : K, v.embedding z = ψ a (ι w)) → ∃ y : Fin d → K, cpt v.embedding y = w := by
  obtain ⟨f, hf⟩ := exists_coord ψ (ι.comp (cptL v.embedding d)) h
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    refine hι x (hψ _ fun a => ?_)
    have := hf x a
    rw [hx, Pi.zero_apply, map_zero] at this
    exact this.symm
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let L : E →ₗ[ℂ] (Fin d → ℂ) := ∑ a, (ψ a).smulRight (cpt v.embedding (g (Pi.single a 1)))
  have hL : ∀ (e : E) (u : Fin n → K), (∀ a, v.embedding (u a) = ψ a e) → L e = cpt v.embedding (g u) := fun e u hu => by
    refine Eq.trans ?_ (semi_apply_pi ((cptL v.embedding d).comp g) u).symm
    simp only [L, LinearMap.sum_apply, LinearMap.smulRight_apply, hu]
    rfl
  have hid : L ∘ₗ ι = LinearMap.id := by
    refine GlobalTheory.EquivariantEuclideanComplex.ext_cpt v fun x => ?_
    rw [LinearMap.comp_apply, hL (ι (cpt v.embedding x)) (f x) (hf x), LinearMap.id_apply]
    exact congrArg _ (congrArg (fun M => M x) hg)
  have hid' : ∀ w, L (ι w) = w := fun w => congrArg (fun M => M w) hid
  refine ⟨Function.LeftInverse.injective hid', fun w hw => ?_⟩
  choose u hu using hw
  exact ⟨g u, (hL _ u hu).symm.trans (hid' w)⟩

end Coord

section Family

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] {F : DefFam K G Pl0 T J} (X : CxData F.amb)

structure FormsTie : Prop where

  inner_eq : ∀ t (x y : (F.R t).S.Forms),
    ⟪X.jR t x, X.jR t y⟫_ℂ = F.v0.embedding ((F.R t).S.csum (x : (F.R t).S.Cl → (F.R t).S.V) (y : (F.R t).S.Cl → (F.R t).S.V))

  inj : ∀ t, Function.Injective (X.jR t)

  span : ∀ t, Submodule.span ℂ (Set.range (X.jR t)) = ⊤

def ThroughGood : Prop :=
  ∀ t (x : (F.R t).S.Forms), X.Θ t (X.jR t ((F.R t).S.gaOp (F.R t).r (goodAt F.X ⊥ 1) x)) = X.Θ t (X.jR t x)

omit X in
theorem csum_gaOp_good (B : BlockDat K G Pl0) {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (hB : B.Ok s)
    {Y : Finset (G → K)} (hY : ∀ χ ∈ Y, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) (x y : B.S.Forms) :
    B.S.csum (B.S.gaOp B.r (goodAt Y P ψ) x : B.S.Cl → B.S.V) (y : B.S.Cl → B.S.V) =
      B.S.csum (x : B.S.Cl → B.S.V) (B.S.gaOp B.r (goodAt Y P ψ) y : B.S.Cl → B.S.V) := by
  have hp := good_at_spec K v0 hv0 G Y hY P ψ
  have hadj := group_action_matrix_adjoint K B.S G B.r hB.act (goodAt Y P ψ)
  rw [hp.selfAdj] at hadj
  have e : ∀ a b : B.S.Forms, B.S.csum (a : B.S.Cl → B.S.V) (b : B.S.Cl → B.S.V) =
      hform B.S.H (B.S.basis.equivFun a) (B.S.basis.equivFun b) := fun a b => by
    have := B.S.isClassSum (B.S.basis.equivFun a) (B.S.basis.equivFun b)
    rw [CSD.I_apply, CSD.I_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at this
    exact this.symm
  rw [e, e, ← CSD.gaMat_mulVec_equivFun, ← CSD.gaMat_mulVec_equivFun, RationalHermitianForm.hform_eq_dot, RationalHermitianForm.hform_eq_dot,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hadj]

variable {X}

theorem exists_mem_range_toF {s : ℕ} (hF : F.Ok s) (hT : FormsTie X) (hg : ThroughGood X)
    (hr : GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTest X) (t : T) (x : (F.R t).S.Forms) :
    ∃ z ∈ LinearMap.range ((F.R t).toF (F.lvl ⊥ 1) (X.Z t)), X.Θ t (X.jR t z) = X.Θ t (X.jR t x) := by
  obtain ⟨n, ψ, hψ, hrat⟩ := hr
  haveI : FiniteDimensional K (F.amb.FR t) := Module.Finite.of_basis (F.R t).S.basis
  obtain ⟨k, hk, horth⟩ := exists_orth (X.jR t) (hT.inj t) (fun a b => ⟨_, (hT.inner_eq t a b).symm⟩)
    (LinearMap.ker ((X.Θ t).comp (X.jR t))) x
  have hk' : X.Θ t (X.jR t k) = 0 := hk
  refine ⟨(F.R t).S.gaOp (F.R t).r (goodAt F.X ⊥ 1) (x - k), ?_, ?_⟩
  · rw [GlobalTheory.OneForm.range_toF]
    refine ⟨?_, x - k, ?_⟩
    · change X.jR t _ ∈ LinearMap.range (LinearMap.adjoint (X.Θ t))
      rw [← LinearMap.orthogonal_ker, Submodule.mem_orthogonal]
      intro u hu
      refine GlobalTheory.EquivariantEuclideanComplex.orth_span ?_ u (mem_span_of_ker ψ hψ (X.jR t) (hT.span t) (X.Θ t) (hrat t) hu)
      rintro _ ⟨a, ha, rfl⟩
      have h1 := horth ((F.R t).S.gaOp (F.R t).r (goodAt F.X ⊥ 1) a) ((hg t a).trans ha)
      refine ((hT.inner_eq t _ _).trans ?_).trans (((hT.inner_eq t _ _).symm).trans h1)
      rw [csum_gaOp_good (F.R t) hF.conj (hF.what₂ t) hF.irr]
    · rw [GlobalTheory.OneForm.asAlg_eq_sum, CSD.gaOp, LinearMap.sum_apply]
      rfl
  · refine (hg t _).trans ?_
    have e : X.jR t (x - k) = X.jR t x - X.jR t k := map_sub (X.jR t) x k
    exact (congrArg (X.Θ t) e).trans (by rw [map_sub, hk', sub_zero])

theorem bijective_and_ratMu {s : ℕ} (hF : F.Ok s) (hT : FormsTie X) (hg : ThroughGood X)
    (hr : GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTest X) (hon : ∀ t, Function.Surjective (X.Θ t))
    {fc : DefSub F.amb → DefFace F.base} (cr : Crd F.amb fc) (b : Bool) (hc : GlobalTheory.EquivariantEuclideanComplex.IsCoord cr b X.zs ⊥ 1) :
    (∀ t, Function.Bijective (X.iC cr b t)) ∧ X.RATmu cr b := by
  have hex := exists_mem_range_toF hF hT hg hr
  obtain ⟨n, ψ, hψ, hrat⟩ := hr
  have key := fun t => injective_and_rat F.v0 ψ hψ (X.iC cr b t)
    (fun x a => by
      obtain ⟨z, hz⟩ := hrat t (cr.toR X.zs b t x) a
      exact ⟨z, hz.trans (congrArg (ψ a) (GlobalTheory.OneForm.iC_cpt X cr b t x).symm)⟩)
    (fun x hx => by
      have h0 : X.Θ t (X.jR t (cr.toR X.zs b t x)) = 0 := (GlobalTheory.OneForm.iC_cpt X cr b t x).symm.trans hx
      have h1 : cr.toR X.zs b t x ∈ LinearMap.range ((F.R t).toF (F.lvl ⊥ 1) (X.zs.Z t)) := (hc t).2 ▸ ⟨x, rfl⟩
      rw [GlobalTheory.OneForm.range_toF] at h1
      obtain ⟨y, hy⟩ : X.jR t (cr.toR X.zs b t x) ∈ LinearMap.range (LinearMap.adjoint (X.Θ t)) := h1.1
      have h2 : ⟪X.jR t (cr.toR X.zs b t x), X.jR t (cr.toR X.zs b t x)⟫_ℂ = 0 := by
        conv_lhs => enter [2]; rw [← hy]
        rw [LinearMap.adjoint_inner_left, h0, inner_zero_right]
      rw [inner_self_eq_zero, ← map_zero (X.jR t)] at h2
      exact (hc t).1 ((hT.inj t h2).trans (map_zero _).symm))
  have hsur : ∀ t, Function.Surjective (X.iC cr b t) := fun t => by
    have h1 : Submodule.span ℂ (Set.range (X.jR t)) ≤ (LinearMap.range (X.iC cr b t)).comap (X.Θ t) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      obtain ⟨z, hz, e⟩ := hex t x
      obtain ⟨y, rfl⟩ : z ∈ LinearMap.range (cr.toR X.zs b t) := (hc t).2.symm ▸ hz
      exact ⟨_, (GlobalTheory.OneForm.iC_cpt X cr b t y).trans e⟩
    intro e
    obtain ⟨u, rfl⟩ := hon t e
    exact h1 (hT.span t ▸ Submodule.mem_top)
  refine ⟨fun t => ⟨(key t).1, hsur t⟩, GlobalTheory.OneForm.rat_of_image_le X cr b (key F.μ0).1 fun t y _ => ?_⟩
  obtain ⟨w, hw⟩ := hsur F.μ0 (X.Θ t (X.jR t y))
  obtain ⟨y₀, rfl⟩ := (key F.μ0).2 w fun a => by
    obtain ⟨z, hz⟩ := hrat t y a
    exact ⟨z, hz.trans (congrArg (ψ a) hw.symm)⟩
  exact ⟨_, ⟨y₀, rfl⟩, (GlobalTheory.OneForm.iC_cpt X cr b F.μ0 y₀).symm.trans hw⟩

end Family

end GlobalTheory.OneFormTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLatticeProdDerivWeierstrassPMem
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_datum_sqProd_mem :
    ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p →
      Datum p F L t → ∃ (L' : PeriodPair) (t' : ℂ), Datum p F L' t' ∧
        (latticeCurve L').j = (latticeCurve L).j ∧ sqProd p L' t' ∈ F := by
  intro p F L t hp h4 h3 hD
  set c := sqProd p L t with hc
  have hc0 : c ≠ 0 := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2
  have hc2 : c ^ 2 ∈ F := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable p F L t hp h4 h3 hD).1
  obtain ⟨L', hlat, hg₂, hg₃, hder, hj⟩ := GlobalTheory.T.exists_scaled_periodPair_invariants L c hc0
  obtain ⟨hcard, -⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4
  refine ⟨L', c * t, ⟨?_, ?_, ?_, ?_, ?_⟩, hj, ?_⟩
  · intro ω hω
    have hz : c * (c⁻¹ * ω) ∈ L'.lattice := by rwa [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hz' := (hlat _).1 hz
    have := (hlat _).2 (hD.mul _ hz')
    rwa [← mul_assoc, mul_comm c, mul_assoc, ← mul_assoc c, mul_inv_cancel₀ hc0, one_mul] at this
  · rw [hg₂]
    have : (c ^ 4)⁻¹ = ((c ^ 2) ^ 2)⁻¹ := by ring
    rw [this]
    exact mul_mem (inv_mem (pow_mem hc2 _)) hD.g₂_mem
  · rw [hg₃]
    have : (c ^ 6)⁻¹ = ((c ^ 2) ^ 3)⁻¹ := by ring
    rw [this]
    exact mul_mem (inv_mem (pow_mem hc2 _)) hD.g₃_mem
  · rw [hlat]; exact hD.notMem
  · have := (hlat _).2 hD.ker
    rwa [← mul_assoc, mul_comm c, mul_assoc] at this
  · have hprod : sqProd p L' (c * t) = ((c ^ 3)⁻¹) ^ Fintype.card (Sq p) * c := by
      unfold sqProd
      have : ∀ k : Sq p, L'.derivWeierstrassP (sqPt p (c * t) k) =
          (c ^ 3)⁻¹ * L.derivWeierstrassP (sqPt p t k) := by
        intro k
        unfold sqPt
        rw [← hder, ← mul_assoc, mul_comm ((k.1 : ℕ) : ℂ) c, mul_assoc]
      rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, hc]
      rfl
    rw [hprod]
    set n := Fintype.card (Sq p) with hn
    have : ((c ^ 3)⁻¹) ^ n * c = ((c ^ 2) ^ (3 * ((n - 1) / 2) + 1))⁻¹ := by
      obtain ⟨m, hm⟩ : Odd n := (GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4).2
      rw [hm]
      have : (2 * m + 1 - 1) / 2 = m := by omega
      rw [this]
      apply eq_inv_of_mul_eq_one_left
      rw [inv_pow, mul_assoc, show c * (c ^ 2) ^ (3 * m + 1) = (c ^ 3) ^ (2 * m + 1) by ring,
        inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hc0))]
    rw [this]
    exact inv_mem (pow_mem hc2 _)

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpaceOfSignature
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem hasSignature_diag_signs (p q : ℕ) : Formalism.UG.HasSignature
    (Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ)) p q := by
  have hne : ∀ (i : Fin p) (j : Fin q), Fin.castAdd q i ≠ Fin.natAdd p j := fun i j h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  refine ⟨(finSumFinEquiv (m := p) (n := q)).symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply,
      Matrix.one_apply, (Fin.castAdd_injective p q).eq_iff]
    simp [Examples₂.sgn, Nat.not_le.2 i.isLt]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne i j)]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne j i).symm]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply,
      Matrix.neg_apply, Matrix.one_apply, (Fin.natAdd_injective q p).eq_iff]
    split_ifs <;> simp [Examples₂.sgn]

theorem exists_isV : ∀ (D : D7) (ν q : ℕ), q ≤ ν → ∃ X : LSp D, X.IsV ν q := by
  intro D ν q h
  obtain ⟨p, rfl⟩ : ∃ p, ν = p + q := ⟨ν - q, by omega⟩
  refine ⟨⟨diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q, GlobalTheory.PlaceModel.latFrame _⟩, rfl, fun τ => ?_,
    fun τ => ?_, GlobalTheory.PlaceModel.isSelfDualC_latFrame _⟩
  · have hg : (diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ =
        Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ) := by
      rw [diagSp_gram]
      ext i j
      change τ (if i = j then _ else 0) = if i = j then _ else 0
      by_cases hij : i = j <;> simp [hij, Examples₂.map_sgn]
    change Formalism.UG.HasSignature ((diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ) p q
    rw [hg]
    exact hasSignature_diag_signs p q
  · rw [Nat.add_sub_cancel]
    rfl

end GlobalTheory.ChiGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitCongruenceSubgroupRelIndexNeZeroStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnitCongruenceSubgroup_relIndex_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → (congr (radN E N)).relIndex (congr (fun _ => 1)) ≠ 0 := by
  first | exact @GlobalTheory.CMVal.LatEnt.relIndex_congr_radN_ne_zero | exact GlobalTheory.CMVal.LatEnt.relIndex_congr_radN_ne_zero | (intros; apply GlobalTheory.CMVal.LatEnt.relIndex_congr_radN_ne_zero <;> assumption)
end

