import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameAdelicLatticeAtFinitePlaceOfInert
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjSelfRecip

open ComplexConjugate

theorem reverse_X_sub_C' (μ : ℂ) : (X - C μ : ℂ[X]).reverse = 1 - C μ * X := by
  have h1 : (1 : ℂ[X]).reverse = 1 := by simp only [reverse, natDegree_one, reflect_one, pow_zero]
  have hX : (X : ℂ[X]).reverse = 1 := by simpa [h1] using reverse_X_mul (1 : ℂ[X])
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg, neg_mul, ← sub_eq_add_neg]

theorem prod_conj_reverse (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ = 1) :
    (((s.map fun z => X - C z).prod).map (starRingEnd ℂ)).reverse =
      C (conj (((s.map fun z => X - C z).prod).coeff 0)) * (s.map fun z => X - C z).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    have hs' : ∀ z ∈ s, ‖z‖ = 1 := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have ha : ‖a‖ = 1 := hs a (Multiset.mem_cons_self a s)
    have hca : conj a * a = 1 := by
      rw [Complex.conj_mul', ha]; simp
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, reverse_mul_of_domain, ih hs',
      mul_coeff_zero]
    have hlin : ((X - C a : ℂ[X]).map (starRingEnd ℂ)).reverse = C (-conj a) * (X - C a) := by
      rw [Polynomial.map_sub, map_X, map_C, reverse_X_sub_C']
      have hw : C (conj a) * C a = (1 : ℂ[X]) := by rw [← C_mul, hca, C_1]
      rw [C_neg]
      linear_combination (-1 : ℂ[X]) * hw
    have hc0 : (X - C a : ℂ[X]).coeff 0 = -a := by simp
    rw [hlin, hc0, map_mul, C_mul]
    simp only [map_neg]
    ring

end GlobalTheory.ConjSelfRecip

namespace GlobalTheory.ConjSelfRecip

open ComplexConjugate

theorem reverse_map_inj {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

theorem ell_conj_selfRecip : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    P.coeff 0 ≠ 0 ∧ C (IsCMField.complexConj E (P.coeff 0)) * P =
      (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse := by
  intro E _ _ _ n P hP
  obtain ⟨hm, -, -, hroots⟩ := hP
  let τ : E →+* ℂ := Classical.choice inferInstance
  have hQm : (P.map τ).Monic := hm.map τ
  have hQ : ((P.map τ).roots.map fun z => X - C z).prod = P.map τ :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm IsAlgClosed.card_roots_eq_natDegree
  have hr : ∀ z ∈ (P.map τ).roots, ‖z‖ = 1 := hroots τ
  have key := prod_conj_reverse (P.map τ).roots hr
  rw [hQ] at key
  constructor
  · intro h0
    have h0' : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots hQm.ne_zero, IsRoot, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
    have := hr 0 h0'
    simp at this
  · apply Polynomial.map_injective τ τ.injective
    have hcomp : τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom = (starRingEnd ℂ).comp τ := by
      ext x
      simp [IsCMField.complexEmbedding_complexConj]
    rw [Polynomial.map_mul, map_C, ← reverse_map_inj τ τ.injective, Polynomial.map_map, hcomp,
      ← Polynomial.map_map, key, coeff_map]
    congr 2
    simp [IsCMField.complexEmbedding_complexConj]

end GlobalTheory.ConjSelfRecip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfKillsIdealPowerTorsionSemiAbelian
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.IdealTorsion

open RationalPoint GlobalTheory.TorsionDense
open scoped nonZeroDivisors

theorem exists_pow_eq_span (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (hI' : I ≠ ⊤) : ∃ (h : ℕ) (π : 𝓞 E), 0 < h ∧ I ^ h = Ideal.span {π} ∧ π ≠ 0 ∧ ¬ IsUnit π := by
  have hmem : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  let c := ClassGroup.mk0 ⟨I, hmem⟩
  have hc : c ^ Fintype.card (ClassGroup (𝓞 E)) = 1 := pow_card_eq_one
  have hmem' : I ^ Fintype.card (ClassGroup (𝓞 E)) ∈ (Ideal (𝓞 E))⁰ := pow_mem hmem _
  have hp : (I ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hmem']
    rw [← hc, ← map_pow]
    rfl
  obtain ⟨π, hπ⟩ := hp
  have hpos : 0 < Fintype.card (ClassGroup (𝓞 E)) := Fintype.card_pos
  refine ⟨_, π, hpos, by rw [hπ], ?_, ?_⟩
  · rintro rfl
    have : I ^ Fintype.card (ClassGroup (𝓞 E)) = ⊥ := by rw [hπ]; simp
    exact hI (pow_eq_zero_iff hpos.ne' |>.1 this)
  · intro hu
    have : I ^ Fintype.card (ClassGroup (𝓞 E)) = ⊤ := by
      rw [hπ]; exact Ideal.span_singleton_eq_top.2 hu
    exact hI' (eq_top_iff.2 (this ▸ Ideal.pow_le_self hpos.ne'))

theorem exists_act_pow_stable {k : Type} [Field k] [IsAlgClosed k] {O : Type} [CommRing O]
    (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (act : OAct O G) (π : O)
    (K : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left) (hZ : IsClosed Z)
    (hK : ∀ x, x ∈ K ↔ Set.range x.left ⊆ Z) (hKs : ∀ x ∈ K, x ≫ act.act π ∈ K) :
    ∃ a : ℕ, ∀ x ∈ K, ∃ y ∈ K, y ≫ act.act (π ^ (a + 1)) = x ≫ act.act (π ^ a) := by
  letI := zariski G
  haveI := noetherianSpace_zariski G
  have hcl : ∀ n : ℕ, IsClosed {z : 𝟙_ (Over (Sp k)) ⟶ G | ∃ y ∈ K, y ≫ act.act (π ^ n) = z} :=
    fun n => by
    obtain ⟨Z', hZ', h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (act.act (π ^ n))
      (act.hom _) inferInstance inferInstance inferInstance inferInstance K Z hZ hK
    refine isClosed_induced_iff.2 ⟨Z', hZ', ?_⟩
    ext z
    rw [Set.mem_preimage, ← range_left_subset_iff, ← h]
    rfl
  let F : ℕ → Closeds (𝟙_ (Over (Sp k)) ⟶ G) := fun a => ⟨_, hcl a⟩
  obtain ⟨_, ⟨a, rfl⟩, hmin⟩ := (wellFounded_lt (α := Closeds (𝟙_ (Over (Sp k)) ⟶ G))).has_min
    (Set.range F) ⟨_, 0, rfl⟩
  have hle : F (a + 1) ≤ F a := by
    rintro _ ⟨y, hy, rfl⟩
    haveI := act.hom π
    refine ⟨y ≫ act.act π, ?_, by rw [Category.assoc, ← act.mul, ← pow_succ']⟩
    exact hKs y hy
  have heq : F (a + 1) = F a := hle.eq_of_not_lt (hmin _ ⟨_, rfl⟩)
  refine ⟨a, fun x hx => ?_⟩
  have : x ≫ act.act (π ^ a) ∈ F (a + 1) := by
    rw [heq]
    exact ⟨x, hx, rfl⟩
  exact this

end GlobalTheory.IdealTorsion

namespace GlobalTheory.IdealTorsion

open RationalPoint GlobalTheory.TorsionDense

theorem eq_one_of_idealTorsion_comp_eq_one : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (u : G ⟶ G) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom u → (∀ a, act.act a ≫ u = u ≫ act.act a) → I ≠ ⊤ → (∀ (j : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), (∀ a ∈ I ^ j, x ≫ act.act a = 1) → x ≫ u = 1) → u = 1 := by
  intro E _ _ k _ _ _ G _ act u I hG hu hcomm hI hkill
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  have := isIntegral_left_of_isSemiAbelian G
  haveI := hu
  have hact : ∀ a, IsMonHom (act.act a) := act.hom
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ u) fun x y => MonObj.mul_comp x y u
  by_cases hbot : I = ⊥
  · subst hbot
    refine eq_one_of_finite_range u ?_
    have : (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ u) ⊆ {1} := by
      rintro _ ⟨x, rfl⟩
      refine hkill 1 x fun a ha => ?_
      rw [pow_one, Ideal.mem_bot] at ha
      rw [ha, h0, MonObj.comp_one]
    exact (Set.finite_singleton _).subset this
  obtain ⟨h, π, hh, hπ, hπ0, hπu⟩ := exists_pow_eq_span E I hbot hI
  have htors : ∀ (n : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), x ≫ act.act (π ^ n) = 1 → x ≫ u = 1 := by
    intro n x hx
    refine hkill (h * n) x fun a ha => ?_
    rw [pow_mul, hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [mul_comm, act.mul, ← Category.assoc, hx, MonObj.one_comp]
  obtain ⟨a, ha⟩ := exists_act_pow_stable G act π φ.ker (u.left ⁻¹' {pt (1 : 𝟙_ (Over (Sp k)) ⟶ G)})
    ((isClosed_pt _).preimage u.left.continuous) (fun x => by
      rw [range_left_subset_iff, Set.mem_preimage, ← pt_comp, Set.mem_singleton_iff,
        pt_injective.eq_iff]
      rfl) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      change x ≫ act.act π ≫ u = 1
      rw [hcomm, ← Category.assoc]
      change (x ≫ u) ≫ act.act π = 1
      rw [show x ≫ u = 1 from hx, MonObj.one_comp])
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G G u hu inferInstance
    inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ (by simp)
  have hfin : Finite φ.range := by
    refine GlobalTheory.T.finite_closed_stable_subgroup_semiAbelian_no_torsion E k G act π hG hπ0 hπu _ Z' hZ' (fun y => ?_) ?_ ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
    · rintro b _ ⟨g, rfl⟩
      refine ⟨g ≫ act.act b, ?_⟩
      change (g ≫ act.act b) ≫ u = (g ≫ u) ≫ act.act b
      rw [Category.assoc, hcomm, Category.assoc]
    · rintro _ ⟨g, rfl⟩ hg
      have hgk : g ≫ act.act π ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        change (g ≫ act.act π) ≫ u = 1
        rw [Category.assoc, hcomm, ← Category.assoc]
        exact hg
      obtain ⟨y, hy, hyg⟩ := ha _ hgk
      let ψ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
        MonoidHom.mk' (fun x => x ≫ act.act (π ^ (a + 1))) fun x y => MonObj.mul_comp x y _
      have h1 : φ (g / y) = 1 := htors (a + 1) (g / y) (by
        change ψ (g / y) = 1
        rw [map_div, div_eq_one]
        change g ≫ act.act (π ^ (a + 1)) = y ≫ act.act (π ^ (a + 1))
        rw [hyg, pow_succ', act.mul, Category.assoc])
      rwa [map_div, MonoidHom.mem_ker.1 hy, div_one] at h1
  exact eq_one_of_finite_range u hfin

end GlobalTheory.IdealTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ArchInj

theorem eq_zero_of_at_of_piInf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E), At (evI F) z → (∀ w, piInf (τ w) z = 0) → z = 0 :=
  fun _ _ _ _ _ _ _ _ hCM τ z hz h0 => GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hCM τ z hz h0

end GlobalTheory.ArchInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusTheta

variable (F : Type) [Field F] [NumberField F]

def infScale (s : ℝ) : AF F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedEmbedding.mixedSpace F) s), 1)

theorem infScale_mul_fst (s : ℝ) (x : AF F) : (infScale F s * x).1 = (infScale F s).1 * x.1 := rfl

theorem infScale_mul_snd (s : ℝ) (x : AF F) : (infScale F s * x).2 = x.2 := by
  show (infScale F s).2 * x.2 = x.2
  simp [infScale]

theorem evI_infScale_mul (s : ℝ) (x : AF F) : evI F (infScale F s * x) = s • evI F x := by
  unfold evI
  rw [infScale_mul_fst, map_mul]
  simp [infScale, Algebra.smul_def]

end GlobalTheory.TorusTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryConjOfCharpolyEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.IntUnitConj

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P.Separable →
    ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ y y' : UL n w, y ∈ KL n w → y' ∈ KL n w → y.1.val.charpoly = atPl w P →
      y'.1.val.charpoly = atPl w P → ∃ g ∈ KL n w, y' = g⁻¹ * y * g := by
  intro E _ _ _ hU n P hP
  filter_upwards [UnitInert.eventually_separable P hP] with w hsep γ γ' hγK hγ'K hγ hγ'
  let O := w.adicCompletionIntegers E
  let ι := algebraMap O (w.adicCompletion E)
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨y', hy'⟩ : ∃ y' : GL (Fin n) O, GeneralLinearGroup.map ι y' = γ.1 := (Subgroup.mem_subgroupOf.1 hγK)
  obtain ⟨z', hz'⟩ : ∃ z' : GL (Fin n) O, GeneralLinearGroup.map ι z' = γ'.1 := (Subgroup.mem_subgroupOf.1 hγ'K)
  have hch : ∀ x : GL (Fin n) O, x.val.charpoly.map ι = (GeneralLinearGroup.map ι x).val.charpoly := fun x =>
    (Matrix.charpoly_map _ _).symm
  have e1 : y'.val.charpoly.map ι = atPl w P := by rw [hch, hy', hγ]
  have e2 : z'.val.charpoly.map ι = atPl w P := by rw [hch, hz', hγ']
  have e12 : z'.val.charpoly = y'.val.charpoly := Polynomial.map_injective ι hι (e2.trans e1.symm)
  suffices H : ∃ u : GL (Fin n) O, GeneralLinearGroup.map ι u ∈ UL n w ∧ y'.val * u.val = u.val * z'.val by
    obtain ⟨u, hu, hcu⟩ := H
    let g : GLw n w := GeneralLinearGroup.map ι u
    have key : γ.1 * g = g * γ'.1 := by
      rw [← hy', ← hz', ← map_mul, ← map_mul]
      congr 1
      exact Units.ext hcu
    refine ⟨⟨g, hu⟩, Subgroup.mem_subgroupOf.2 ⟨u, rfl⟩, Subtype.ext ?_⟩
    change γ'.1 = g⁻¹ * γ.1 * g
    rw [mul_assoc, key, inv_mul_cancel_left]
  by_cases hw : IsSplitAt w
  · obtain ⟨u, hu⟩ := GlobalTheory.ConjLocal.conj_of_charpoly_local O n y'.val z'.val e12.symm (hsep _ e1)
    refine ⟨u, by rw [UL, if_pos hw]; exact Subgroup.mem_top _, ?_⟩
    rw [hu, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  · obtain ⟨-, hcc, hv, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩ := (h4 hw).2.1
    have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
    haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
    haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
      Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
    let c : O →+* O := (cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)
    have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hcc _)
    have hmapc : ∀ M : Matrix (Fin n) (Fin n) O, (cT c M).map ι = cT (cj w) (M.map ι) := fun M => by
      ext i j; rfl
    have hUL : ∀ x : GLw n w, x ∈ UL n w ↔ cT (cj w) x.val * x.val = 1 := fun x => by
      rw [UL, if_neg hw]
      change cT (cj w) x.val * 1 * x.val = 1 ↔ _
      rw [mul_one]
    have hmv : ∀ x : GL (Fin n) O, (GeneralLinearGroup.map ι x).val = x.val.map ι := fun x => by
      ext i j; rfl
    have hunit : ∀ (x : GL (Fin n) O), GeneralLinearGroup.map ι x ∈ UL n w → cT c x.val * x.val = 1 := fun x hx => by
      refine Matrix.map_injective hι ?_
      show (cT c x.val * x.val).map ι = (1 : Matrix (Fin n) (Fin n) O).map ι
      rw [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι), ← hmv]
      exact (hUL _).1 hx
    obtain ⟨u, hu, hcu⟩ := UnitInert.exists_unitary_conj (IsLocalRing.maximalIdeal O) (σ := c) hc
      (fun x hx => by
        rw [GlobalTheory.InertUQ.mem_max_iff] at hx ⊢
        exact (hv _).trans_lt hx)
      ⟨⟨x₀, hx₀⟩, by
        rw [← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]
        change ¬ Valued.v (x₀ - cj w x₀) < 1
        rw [Valuation.map_sub_swap, hx₁]
        exact lt_irrefl _⟩
      (hunit y' (hy' ▸ γ.2)) (hunit z' (hz' ▸ γ'.2)) (hsep _ e1) e12
    refine ⟨u, ?_, hcu⟩
    rw [hUL]
    have := congrArg (fun M => M.map ι) hu
    simp only [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι)] at this
    exact this

end GlobalTheory.BCT.IntUnitConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSkewHermitianCorrectionOfLocalSolutiStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_skewHermitian_correction_of_local_solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (v : Pl F) (O : Type) [CommRing O] (c : O →+* O) (ι : O →ₙ+* AE F E)
    (P Q : Matrix (Fin n) (Fin n) (AE F E)) (JL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (ι 1) → (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) → (∀ x, cA σ (ι x) = ι (c x)) →
    P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) → Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) →
    ι 1 • P = P → ι 1 • Q = Q → Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι →
    (∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O)
      (ZL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (M - 1) → M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    ZLᵀ * JL + JL * ZL.map c = 0 →
    IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL).det →
    ∃ Z : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) Z ∧
      (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  first | exact @GlobalTheory.TransportBack.transport_back | exact GlobalTheory.TransportBack.transport_back | (intros; apply GlobalTheory.TransportBack.transport_back <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK

theorem exists_at_evI_piInf_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) :
    ∃ z : AE F E, At (evI F) z ∧ ∀ w, piInf (τ w) z = c w := by
  classical
  have := h.1
  have := h.2.1

  have hloc : ∀ w : InfinitePlace F, ∃ (α : E) (a b : w.Completion),
      InfinitePlace.Completion.extensionEmbedding w a +
        InfinitePlace.Completion.extensionEmbedding w b * (τ w).1 α = c w := by
    intro w
    have hα : ∃ α : E, ((τ w).1 α).im ≠ 0 := by
      by_contra hn
      push Not at hn
      refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (τ w).1)))
        (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
      exact Complex.conj_eq_iff_im.2 (hn x)
    obtain ⟨α, hα⟩ := hα
    have hs := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
    obtain ⟨a, ha⟩ := hs ((c w).re - (c w).im / ((τ w).1 α).im * ((τ w).1 α).re)
    obtain ⟨b, hb⟩ := hs ((c w).im / ((τ w).1 α).im)
    refine ⟨α, a, b, ?_⟩
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w),
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w), ha, hb]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]; field_simp; ring
  choose α a b hab using hloc
  let δ : ∀ w : InfinitePlace F, w.Completion → AF F := fun w x =>
    ((Pi.single w x : ∀ v : InfinitePlace F, v.Completion), 0)
  have hδ : ∀ (u : AF F), evI F u = 0 → ∀ w x, u * δ w x = 0 := by
    intro u hu w x
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  have hp : ∀ w v x (e : E), piInf (τ w) (δ v x ⊗ₜ[F] e) =
      InfinitePlace.Completion.extensionEmbedding w ((Pi.single v x : ∀ v : InfinitePlace F, v.Completion) w)
        * (τ w).1 e := fun _ _ _ _ => rfl
  refine ⟨∑ w, (δ w (a w) ⊗ₜ[F] (1 : E) + δ w (b w) ⊗ₜ[F] α w), fun u hu => ?_, fun w => ?_⟩
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hδ u hu, hδ u hu,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  · rw [map_sum, Finset.sum_eq_single w]
    · rw [map_add, hp, hp, Pi.single_eq_same, Pi.single_eq_same, map_one, mul_one, hab]
    · intro v _ hv
      rw [map_add, hp, hp, Pi.single_eq_of_ne hv.symm, Pi.single_eq_of_ne hv.symm, map_zero, zero_mul, zero_mul, add_zero]
    · simp

end GlobalTheory.ThK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothinStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure], ∃ α : ℕ → Lie E a → ℂ, (∀ n, IsTest (invSet E a) (α n) ∧ KInv (α n)) ∧ ∀ ψ ∈ Sm E a, ∀ g, Tendsto (fun n => smoothing ν (α n) ψ g) atTop (𝓝 (ψ g)) := by
  first | exact @GlobalTheory.AutGrowth.ApproxId.exists_approx_identity | exact GlobalTheory.AutGrowth.ApproxId.exists_approx_identity | (intros; apply GlobalTheory.AutGrowth.ApproxId.exists_approx_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteUnitaryRationalPointFiniteAndInfinStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteUnitaryRationalPoint_finite_and_infinite_parts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), ∃ r ∈ ratU E n, splitFin E n r = finPt γ ∧ ∀ v : InfinitePlace E, cEmb v.embedding r = GeneralLinearGroup.map v.embedding γ.1 := by
  first | exact @GlobalTheory.BCT.RatPt.ratPt | exact GlobalTheory.BCT.RatPt.ratPt | (intros; apply GlobalTheory.BCT.RatPt.ratPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d)
    (v : Pl F), ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ g : GlobalTheory.DblVac.UD σ W,
      ((g : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 ∧
      g ∈ GlobalTheory.DblVac.KD σ W v := by
  first | exact @GlobalTheory.DblVacDiag.diag_mem_KD | exact GlobalTheory.DblVacDiag.diag_mem_KD | (intros; apply GlobalTheory.DblVacDiag.diag_mem_KD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameAdelicLatticeAtFinitePlaceOfInertStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_adelicLatticeAtFinitePlace_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (n : ℕ) (X : Spc F E n), X.L.IsLattice E →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ AE F E),
      Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∃ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) := by
  first | exact @GlobalTheory.InertLocBasis.exists_basis_at_inert | exact GlobalTheory.InertLocBasis.exists_basis_at_inert | (intros; apply GlobalTheory.InertLocBasis.exists_basis_at_inert <;> assumption)
end

