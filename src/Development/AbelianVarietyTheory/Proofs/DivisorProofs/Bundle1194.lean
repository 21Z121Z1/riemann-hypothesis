import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.BigFieldChange

theorem isBig_pull_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k)
    (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q →
    topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB →
    ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  intro k E _ _ _ Y X p q π H hp hq hd L hL
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := hp
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hL' := LB.isLB_pull hL π
  have e : ∀ m : ℕ, lbH0 E (lbPow (L.pull π) m) = lbH0 k (lbPow L m) := fun m => by
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL' m) (LB.isLB_pull (isLB_lbPow hL m) π)
      (by rw [cls_lbPow hL', cls_pull hL, cls_pull (isLB_lbPow hL m), cls_lbPow hL, map_nsmul])]
    exact FieldChangeInter.hdim_pull H (isLB_lbPow hL m) 0
  constructor
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL, fun m => finite_coh_zero_twist_of_isProjOver (f := p) (fun _ => rfl) hp (isLB_lbPow hL m),
      D, hd.symm.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m))⟩
  · intro h
    obtain ⟨D, hD, c, hc, hm⟩ := h.3
    exact ⟨hL', fun m => finite_coh_zero_twist_of_isProjOver (f := q) (fun _ => rfl) hq (isLB_lbPow hL' m),
      D, hd.trans hD, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ (e m).symm)⟩

end GlobalTheory.BigFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelIdAndComp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isModel_id (X : Scheme.{0}) [IsIntegral X] : IsModel (𝟙 X) (RingHom.id X.functionField) where
  gen := rfl
  deg := Scheme.Hom.residueDegree_id _
  compat y a := by
    simp only [RingHom.id_apply, Scheme.Hom.stalkMap_id]
    rfl

theorem IsModel.comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] {π : Y ⟶ X} {π' : Z ⟶ Y}
    {φ : X.functionField →+* Y.functionField} {φ' : Y.functionField →+* Z.functionField}
    (h : IsModel π φ) (h' : IsModel π' φ') : IsModel (π' ≫ π) (φ'.comp φ) where
  gen := by
    show π (π' (genericPoint Z)) = genericPoint X
    rw [h'.gen, h.gen]
  deg := by
    rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp π' π (genericPoint Z), h'.deg]
    rw [h'.gen, h.deg]
  compat z a := by
    refine (congrArg φ' (h.compat (π' z) a)).trans ((h'.compat z _).trans ?_)
    rw [Scheme.Hom.stalkMap_comp]
    rfl

theorem isModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y)
    (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField),
    IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) :=
  fun X _ _ _ _ _ _ _ _ _ => ⟨isModel_id X, fun h h' => h.comp h'⟩

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactCentOfConj
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open GlobalTheory.Orb
open Formalism.REAL (UJ KG toM)

namespace GlobalTheory.PsCo.NonEll

theorem isRegSS_conj {n : ℕ} {ε : Fin n → Bool} (s x : UJ ε) (hs : IsRegSS (ujMat ε s)) :
    IsRegSS (ujMat ε (x⁻¹ * s * x)) := by
  unfold IsRegSS at hs ⊢
  rw [map_mul, Matrix.charpoly_mul_comm, ← map_mul, ← mul_assoc, mul_inv_cancel,
    one_mul]
  exact hs

theorem isCompact_cent_of_conj {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (s x : G) (h : IsCompact (cent (x⁻¹ * s * x) : Set G)) : IsCompact (cent s : Set G) := by
  have hc : Continuous fun y : G => x * y * x⁻¹ := by fun_prop
  have := h.image hc
  convert this using 1
  ext y
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, Set.mem_image]
  constructor
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by group⟩
    calc x⁻¹ * y * x * (x⁻¹ * s * x) = x⁻¹ * (y * s) * x := by group
      _ = x⁻¹ * (s * y) * x := by rw [hy]
      _ = x⁻¹ * s * x * (x⁻¹ * y * x) := by group
  · rintro ⟨z, hz, rfl⟩
    calc x * z * x⁻¹ * s = x * (z * (x⁻¹ * s * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * s * x) * z) * x⁻¹ := by rw [hz]
      _ = s * (x * z * x⁻¹) := by group

theorem stNonEll : GlobalTheory.PsCo.Pc1.StNonEll := by
  intro n ε s hs hnc
  set r : UJ ε → ℝ := fun g => rM ε (toM g) with hr
  have hcont : Continuous r := (GlobalTheory.offDiagBlockNorm_cont_inv n ε).1
  have hsub : IsCompact {g : UJ ε | r g ≤ r s} := GlobalTheory.isCompact_offDiag_sublevel n ε (r s)
  have hcl : IsClosed (Set.range fun x : UJ ε => x⁻¹ * s * x) := isClosed_class_realUJ hs
  have hK := hsub.inter_right hcl
  have hne : ({g : UJ ε | r g ≤ r s} ∩ Set.range fun x : UJ ε => x⁻¹ * s * x).Nonempty :=
    ⟨s, le_refl (r s), 1, by simp⟩
  obtain ⟨g, ⟨hg1, x₀, rfl⟩, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  refine ⟨r (x₀⁻¹ * s * x₀), ?_, fun x => ?_⟩
  · have h0 : 0 ≤ r (x₀⁻¹ * s * x₀) := Finset.sum_nonneg fun z _ => by positivity
    refine lt_of_le_of_ne h0 fun h => hnc ?_
    have hk : x₀⁻¹ * s * x₀ ∈ KG ε := (GlobalTheory.offDiag_zero_iff_mem_K n ε _).1 h.symm
    exact isCompact_cent_of_conj s x₀ (GlobalTheory.isCompact_cent_of_mem_KG n ε _ hk (isRegSS_conj s x₀ hs))
  · change r (x₀⁻¹ * s * x₀) ≤ r (x⁻¹ * s * x)
    by_cases hx : r (x⁻¹ * s * x) ≤ r s
    · exact hmin ⟨hx, x, rfl⟩
    · exact le_trans hg1 (not_le.1 hx).le

end GlobalTheory.PsCo.NonEll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContinuousCrystallineMatrixRepOfIntertwinesDet
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachPlace

theorem matGood_of_tw {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (f n : ℕ)
    (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r r' : ↥(GK K) →* GL (Fin n) ↥(OL LL))
    (U : ZMod f → Multiset ℤ) (a : Mx ↥(OL LL) n n) :
    MatGood P emb r U → Tw r' r a → a.det ≠ 0 → MatGood P emb r' U := by
  rintro ⟨hc, hcr, hj⟩ ht hdet
  set φ := algebraMap ↥(OL LL) ↥LL.1 with hφ
  have hinj : Function.Injective φ := fun x y h => Subtype.ext h
  set aL : Mx ↥LL.1 n n := a.map φ with haL
  have hdL : IsUnit aL.det := by
    have hd : aL.det = φ a.det := (RingHom.map_det φ a).symm
    rw [hd]
    exact isUnit_iff_ne_zero.mpr (fun h => hdet (hinj (by rw [h, map_zero])))
  have htL : ∀ g, aL * (r' g : Mx ↥(OL LL) n n).map φ = (r g : Mx ↥(OL LL) n n).map φ * aL := fun g => by
    rw [haL, ← Matrix.map_mul, ← Matrix.map_mul, ht g]
  have hconj : ∀ g, (r' g : Mx ↥(OL LL) n n).map φ = aL⁻¹ * ((r g : Mx ↥(OL LL) n n).map φ * aL) := fun g => by
    rw [← htL g, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdL, Matrix.one_mul]
  let e : (Fin n → ↥LL.1) ≃ₗ[↥LL.1] (Fin n → ↥LL.1) :=
    LinearEquiv.ofLinear (Matrix.toLin' aL) (Matrix.toLin' aL⁻¹)
      (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hdL, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hdL, Matrix.toLin'_one])
  have he : ∀ g v, e (repOf r' g v) = repOf r g (e v) := fun g v => by
    show aL.mulVec (repOf r' g v) = repOf r g (aL.mulVec v)
    rw [repOf_apply, repOf_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, htL g]
  refine ⟨fun i j => ?_, GlobalTheory.HTW.Rec.isCrys_of_equiv _ e he hcr, fun i τ hτ u => ?_⟩
  · have hform : (fun g => (((r' g : Mx ↥(OL LL) n n) i j : ↥(OL LL)) : ↥LL.1)) =
        fun g => ∑ k, aL⁻¹ i k * ∑ m, (((r g : Mx ↥(OL LL) n n) k m : ↥(OL LL)) : ↥LL.1) * aL m j := by
      funext g
      have := congrFun (congrFun (hconj g) i) j
      simp only [Matrix.map_apply, Matrix.mul_apply] at this
      exact this
    rw [hform]
    refine continuous_finset_sum _ fun k _ => continuous_const.mul ?_
    exact continuous_finset_sum _ fun m _ => (hc k m).mul continuous_const
  · rw [GlobalTheory.HTW.Rec.multV_eq_of_equiv _ e he]
    exact hj i τ hτ u

end GlobalTheory.WachPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainTensorComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.TensorFields

theorem exists_finset_lift {k κ K : Type} [Field k] [Field κ] [Field K] [Algebra k κ] [Algebra k K]
    (x : κ ⊗[k] K) : ∃ S : Finset K, ∀ T : Finset K, S ⊆ T →
      ∃ x' : κ ⊗[k] (Algebra.adjoin k (T : Set K)),
        Algebra.TensorProduct.map (AlgHom.id k κ) (Algebra.adjoin k (T : Set K)).val x' = x := by
  classical
  obtain ⟨P, rfl⟩ := TensorProduct.exists_finset x
  refine ⟨P.image Prod.snd, fun T hT => ?_⟩
  refine ⟨∑ i ∈ P.attach, i.1.1 ⊗ₜ[k] (⟨i.1.2, Algebra.subset_adjoin
    (hT (Finset.mem_image_of_mem Prod.snd i.2))⟩ : Algebra.adjoin k (T : Set K)), ?_⟩
  rw [map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Subalgebra.coe_val]
  exact Finset.sum_attach P (fun i => i.1 ⊗ₜ[k] i.2)

theorem isDomain_tensor_complex : ∀ (K κ : Type) [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ],
    IsDomain (K ⊗[ℂ] κ) := by
  classical
  intro K κ _ _ _ _
  suffices h : IsDomain (κ ⊗[ℂ] K) from (Algebra.TensorProduct.comm ℂ K κ).toMulEquiv.isDomain
  haveI : Nontrivial (κ ⊗[ℂ] K) := inferInstance
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  obtain ⟨S₁, h₁⟩ := exists_finset_lift (k := ℂ) x
  obtain ⟨S₂, h₂⟩ := exists_finset_lift (k := ℂ) y
  let A := Algebra.adjoin ℂ ((S₁ ∪ S₂ : Finset K) : Set K)
  obtain ⟨x', hx'⟩ := h₁ (S₁ ∪ S₂) Finset.subset_union_left
  obtain ⟨y', hy'⟩ := h₂ (S₁ ∪ S₂) Finset.subset_union_right
  haveI : Algebra.FiniteType ℂ A := ⟨(Subalgebra.fg_top _).mpr (Subalgebra.fg_adjoin_finset _)⟩
  haveI : IsDomain A := inferInstance
  haveI : IsDomain (κ ⊗[ℂ] A) := GlobalTheory.GeomComp.isDomain_tensor_of_isAlgClosed ℂ A κ
  let φ := Algebra.TensorProduct.map (AlgHom.id ℂ κ) A.val
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := κ) A.val.toLinearMap Subtype.val_injective
  have h0 : x' * y' = 0 := hφ (by rw [map_mul, hx', hy', hxy, map_zero])
  rcases mul_eq_zero.mp h0 with h | h
  · left; rw [← hx', h, map_zero]
  · right; rw [← hy', h, map_zero]

end GlobalTheory.TensorFields
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffQDivAddOfIsQCart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem isEffQDiv_add {X : Scheme.{0}} {Δ D : X → ℚ} (hΔ : IsEffQDiv Δ) (hD : IsEffQDiv D) :
    IsEffQDiv (Δ + D) where
  finite := (hΔ.finite.union hD.finite).subset (Function.support_add _ _)
  coheight z hz := by
    by_cases h : Δ z = 0
    · exact hD.coheight z fun h' => hz (by simp [h, h'])
    · exact hΔ.coheight z h
  nonneg z := add_nonneg (hΔ.nonneg z) (hD.nonneg z)

theorem isEffQDiv_add_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (Δ D : X → ℚ), IsEffQDiv Δ → IsQCart D → IsEffQDiv (Δ + D) := by
  intro X _ _ p hp Δ D hΔ hD
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨m, D₀, -, hD₀, rfl⟩ := hD
  exact isEffQDiv_add hΔ (isEffQDiv_qWeil hD₀ m)

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectiveQCartierDivisorConvexCone
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.QCartCone

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem mult_zero' (z : X) : (0 : CartierDiv X).mult z = 0 := by
  have := CartierDiv.mult_add (0 : CartierDiv X) 0 z
  rw [add_zero] at this
  omega

theorem mult_nsmul' (D : CartierDiv X) (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero']; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul' {D : CartierDiv X} (h : D.Eff) (n : ℕ) : (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem isQCart_cone : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (D B : X → ℚ) (c : ℚ),
    IsQCart D → IsQCart B → 0 ≤ c → IsQCart (D + B) ∧ IsQCart (c • D) ∧ IsQCart (0 : X → ℚ) := by
  intro X _ _ D B c hD hB hc
  obtain ⟨m, D₀, hm, hD₀, rfl⟩ := hD
  obtain ⟨n, B₀, hn, hB₀, rfl⟩ := hB
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨m * n, n • D₀ + m • B₀, Nat.mul_pos hm hn, (eff_nsmul' hD₀ n).add (eff_nsmul' hB₀ m), ?_⟩,
    ⟨c.den * m, c.num.toNat • D₀, Nat.mul_pos c.den_pos hm, eff_nsmul' hD₀ _, ?_⟩,
    ⟨1, 0, one_pos, CartierDiv.eff_zero, ?_⟩⟩
  · funext z
    simp only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul']
    push_cast
    field_simp
  · funext z
    have hnum : ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) := by
      have h1 : ((c.num.toNat : ℤ) : ℚ) = (c.num : ℚ) := by
        rw [Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)]
      exact_mod_cast h1
    have hden : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
    simp only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul']
    push_cast
    rw [hnum]
    conv_lhs => rw [← Rat.num_div_den c]
    field_simp
  · funext z
    simp [qWeil, mult_zero']

end GlobalTheory.QCartCone
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFubiniStudyRatFnsMemPairSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isFS_mem_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → ∃ P : Pair p, P.L = M ∧ ∀ j, f j ∈ P.H 1 0 := by
  intro k _ X _ p M J _ f w h
  obtain ⟨ρ, hρ, hreg, -⟩ := h
  refine ⟨⟨M, M, ρ, ρ, hρ, hρ⟩, rfl, fun j x i c hi _ => ?_⟩
  have e : Pair.loc ⟨M, M, ρ, ρ, hρ, hρ⟩ 1 0 (f j) i c = f j * (ρ i : X.functionField) := by
    simp [Pair.loc]
  rw [e]
  exact (hreg x i hi).1 j

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedOfIsEtaleTowerOverNormalLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.EtNormal

theorem isDomain_and_isIntegrallyClosed_of_formallyEtale (A T : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [CommRing T] [IsLocalRing T] [Algebra A T]
    [Algebra.FormallyEtale A T] [Algebra.EssFiniteType A T] :
    IsDomain T ∧ IsIntegrallyClosed T := by
  let B := Algebra.EssFiniteType.subalgebra A T
  let P : Ideal B := (IsLocalRing.maximalIdeal T).comap (algebraMap B T)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hM : Algebra.EssFiniteType.submonoid A T = P.primeCompl := by
    ext x
    change IsUnit (algebraMap B T x) ↔ x ∉ P
    simp [P, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI hloc : IsLocalization.AtPrime T P := by
    have := Algebra.EssFiniteType.isLocalization A T
    rw [hM] at this
    exact this
  haveI : Algebra.FinitePresentation A B :=
    (Algebra.FinitePresentation.of_finiteType).1 inferInstance
  let e : T ≃ₐ[A] Localization.AtPrime P :=
    (IsLocalization.algEquiv P.primeCompl T (Localization.AtPrime P)).restrictScalars A
  haveI : Algebra.FormallySmooth A (Localization.AtPrime P) := Algebra.FormallySmooth.of_equiv e
  haveI : Algebra.IsSmoothAt A P := inferInstance
  obtain ⟨f, hfP, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := P)
  have := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f)
    (Localization.Away f) P ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) T
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

end GlobalTheory.EtNormal

namespace GlobalTheory.FieldPair

theorem isIntegrallyClosed_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T), IsEtTower cK R cL T ι ψ τ → IsIntegrallyClosed T := by
  intro K L _ _ cK cL r R T ι ψ τ h
  haveI := h.top.isLocalRing
  haveI := h.normal
  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  letI : Algebra ℂ R := c0.toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.base.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra A T := φ.toAlgebra
  letI : Algebra ℂ T := cT.toAlgebra
  haveI : Algebra.FormallyEtale A T := h.etale
  haveI : Algebra.EssFiniteType ℂ T := h.top.essFiniteType
  haveI : IsScalarTower ℂ A T := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change cT a = φ (MvPolynomial.C (c0 a))
    have e : φ (MvPolynomial.C (c0 a)) = ι (c0 a) := MvPolynomial.eval₂Hom_C _ _ _
    rw [e]
    exact Subtype.ext (h.const a).symm
  haveI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_comp ℂ A T
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_mvPolynomial_fin R r
  exact (GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale A T).2

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedPointLocalRingNormalScheme
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem isIntegrallyClosed_locRing : ∀ (X : Scheme.{0}) [IsIntegral X] [GlobalTheory.IsNormalScheme X] (x : X),
    IsIntegrallyClosed (locRing x) := by
  intro X _ _ x
  let e : X.presheaf.stalk x ≃+* locRing x := RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective _ X.functionField (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  haveI : IsIntegrallyClosed (X.presheaf.stalk x) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk x
  exact IsIntegrallyClosed.of_equiv e

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeSublatticePullbackAlongEmbeddingStatement
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_sublatticePullbackAlongEmbedding : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (ι : Matrix (Fin n) (Fin n₁) E), L.IsLattice E → Function.Injective ι.mulVec → (lowLat ι L).IsLattice E := by
  first | exact @GlobalTheory.PlaneSkew.isLattice_lowLat | exact GlobalTheory.PlaneSkew.isLattice_lowLat | (intros; apply GlobalTheory.PlaneSkew.isLattice_lowLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiplesStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_integralTensorAdeleMultiples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ), 0 < N →
    IsOpen (CE F E N : Set (AF F ⊗[F] E)) := by
  first | exact @GlobalTheory.HeckeExtend.CE_isOpen | exact GlobalTheory.HeckeExtend.CE_isOpen | (intros; apply GlobalTheory.HeckeExtend.CE_isOpen <;> assumption)
end

