import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0116
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002
import Formalism.LocalToGlobal.NumberFieldFamilies.IdTransSM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixTraceFormBasisChange
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GramChange

open GlobalTheory.UnitLemma

theorem herm_sum_sum (K : UQ) (B : InvAlg K) (β : B.A) {a : ℕ} (b : Fin a → B.A)
    (M : Matrix (Fin a) (Fin a) K.E) (i j : Fin a) :
    B.herm β (∑ k, M k i • b k) (∑ l, M l j • b l) =
      ∑ k, ∑ l, M k i * B.herm β (b k) (b l) * K.c (M l j) := by
  have hσ : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  unfold InvAlg.herm
  simp only [map_sum, hσ, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    LinearMap.map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_of_sum (K : UQ) (B : InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L)
    (he : ∀ x, e (K.c x) = c (e x)) {a : ℕ} (β : B.A) (b v : Fin a → B.A)
    (M : Matrix (Fin a) (Fin a) K.E) (hv : ∀ j, v j = ∑ i, M i j • b i) :
    (Matrix.of fun i j => e (B.herm β (v i) (v j))) =
      (M.map e)ᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * (M.map e).map c := by
  ext i j
  simp only [Matrix.of_apply, hv, herm_sum_sum, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, he, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_basis_change : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → ∀ (a : ℕ) (β : B.A) (b : Module.Basis (Fin a) K.E B.A), (∀ P : GL (Fin a) L, ∃ b' : Module.Basis (Fin a) K.E B.A, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c) ∧ ∀ b' : Module.Basis (Fin a) K.E B.A, ∃ P : GL (Fin a) L, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c := by
  intro K B L _ e c he a β b
  refine ⟨fun P => ?_, fun b' => ?_⟩
  · set M : Matrix (Fin a) (Fin a) K.E := P.val.map e.symm with hM
    have hMe : M.map e = P.val := by
      ext i j; simp [hM]
    have hdet : IsUnit M.det := by
      have h1 : e M.det = P.val.det := by
        rw [← hMe]; exact RingHom.map_det (e : K.E →+* L) M
      have h2 : IsUnit P.val.det := (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      rw [← h1] at h2
      exact (isUnit_map_iff e _).mp h2
    refine ⟨b.map (Matrix.toLinearEquiv b M hdet), ?_⟩
    rw [gram_of_sum K B L e c he β b _ M, hMe]
    intro j
    simp [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  · have hdet : IsUnit ((b.toMatrix b').map e).det := by
      have h1 : e (b.toMatrix b').det = ((b.toMatrix b').map e).det :=
        RingHom.map_det (e : K.E →+* L) _
      rw [← h1]
      exact (isUnit_map_iff e _).mpr (b.isUnit_det b')
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet.ne_zero, ?_⟩
    rw [gram_of_sum K B L e c he β b b' (b.toMatrix b')]
    · rfl
    · intro j; rw [b.sum_toMatrix_smul_self]

end GlobalTheory.GramChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonalStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u x : WOF F E nS nT),
      u.map (infPartF F E) = 0 → x.map (finPartF F E) = 0 → symplOHF σ JS JT ξ₀ u x = 0 ∧ symplOHF σ JS JT ξ₀ x u = 0 := by
  first | exact @GlobalTheory.WeilDatumF.symplOHF_fin_real_orth | exact GlobalTheory.WeilDatumF.symplOHF_fin_real_orth | (intros; apply GlobalTheory.WeilDatumF.symplOHF_fin_real_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalResidueFieldPointLocalRingClosedPointStatement
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRationalResidueField_pointLocalRing_closedPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (q : Z ⟶ Sp ℂ) [LocallyOfFiniteType q] (y : Z), IsClosed ({y} : Set Z) → RatRes (GlobalTheory.Cartier.constFn q) (locRing y) := by
  first | exact @GlobalTheory.FieldPair.ratRes_locRing_of_isClosed | exact GlobalTheory.FieldPair.ratRes_locRing_of_isClosed | (intros; apply GlobalTheory.FieldPair.ratRes_locRing_of_isClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
section
open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LFun.SphComp

theorem hasSatake_of_isLocComp : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} (π : GlobalTheory.CuspRep.CuspSub E m) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}, GlobalTheory.LFun.HasSatGL w (π.locRep w) B → ∀ {σ : GlobalTheory.CuspRep.SmIrr (GL (Fin m) (w.adicCompletion E))}, π.IsLocComp w σ → ∃ α : Fin m → ℂˣ, Finset.univ.val.map α = B ∧ GlobalTheory.SmGL.HasSatake σ.ρ α := by
  intro E _ _ _ m π w B hB σ hσ
  obtain ⟨f, hf0, hf⟩ := hσ
  obtain ⟨x, hx⟩ := hB.exists_vec

  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine (((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 _ fun g u hu => ?_).resolve_right fun h => hf0 ?_
    · rw [LinearMap.mem_ker] at hu ⊢; rw [hf, hu, map_zero]
    · exact LinearMap.ext fun u => by
        have : u ∈ LinearMap.ker f := h ▸ Submodule.mem_top
        simpa using this

  obtain ⟨v, hv0, hvK⟩ : ∃ v : σ.V, v ≠ 0 ∧ ∀ k ∈ (GlobalTheory.LFun.KGL w m : Set _), σ.ρ k v = v := by
    refine GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup ((GlobalTheory.CuspRep.finRep E m).comp (GlobalTheory.CuspRep.locGL E m w)) σ.ρ
      σ.irred (fun i : GlobalTheory.CuspRep.LocSph.Maps π w σ => i.1) (fun i g u => i.2.2 g u) _ (x : GlobalTheory.CuspRep.Sm E m)
      (fun h => hx.1 (Subtype.ext h)) (fun k hk => ?_) ?_
    · exact congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk)
    · rw [GlobalTheory.CuspRep.LocSph.iSup_range_eq π w σ ⟨f, hf0, hf⟩]; exact x.2
  have hfv : f v ≠ 0 := fun h => hv0 (hinj (h.trans (map_zero f).symm))
  have hs : GlobalTheory.LFun.IsSatVecGL w σ.ρ v B := GlobalTheory.LFun.IsSatVecGL.of_map f hf hinj
    (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hf, hvK k hk]) hfv)
  exact (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ (Fin m) σ.V σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL ⟨σ.smooth, σ.irred⟩ hs)

end GlobalTheory.LFun.SphComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOne
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HCharUnit

theorem locK_eq_one {E : Type} [Field E] [NumberField E] (χ : HChar E) (k : Eˣ) (v : HeightOneSpectrum (𝓞 E))
    (hu : χ.UnrAt v) (ho : ordF v k = 0) : χ.locK v k = 1 := by
  apply hu
  show Valued.v (((k : E) : v.adicCompletion E)) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have hl : WithZero.log (v.valuation E (k : E)) = 0 := by
    unfold ordF at ho; omega
  rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]

theorem finprod_locK_mul_inf : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (k : Eˣ),
    (Function.mulSupport fun w : Pl E => χ.locK w k).Finite ∧ (∏ᶠ w : Pl E, χ.locK w k) * χ.inf k = 1 := by
  intro E _ _ χ k
  have hT : ({v | ¬ χ.UnrAt v} ∪ {v : HeightOneSpectrum (𝓞 E) | ordF v k ≠ 0}).Finite :=
    Set.Finite.union (Filter.eventually_cofinite.mp (Formalism.L2.Fam.IdTrans.unrAe χ)) (GlobalTheory.HeckeProduct.finite_ordF k)
  set S := hT.toFinset with hSdef
  have hsub : (Function.mulSupport fun w : Pl E => χ.locK w k) ⊆ (S : Set (HeightOneSpectrum (𝓞 E))) := by
    intro v hv
    rw [hSdef, Set.Finite.coe_toFinset]
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (locK_eq_one χ k v h.1 h.2)
  refine ⟨S.finite_toSet.subset hsub, ?_⟩
  have hS : ∀ v, v ∉ S → χ.UnrAt v := by
    intro v hv
    by_contra h
    exact hv (by rw [hSdef, Set.Finite.mem_toFinset]; exact Or.inl h)
  have hpr := Formalism.L2.Host.HChar.productRule χ S hS k
  have hrest : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [finprod_eq_if]
    split_ifs with hv
    · rfl
    have : ordF v k = 0 := by
      by_contra h
      exact hv (by rw [hSdef, Set.Finite.mem_toFinset]; exact Or.inr h)
    rw [this, zpow_zero]
  rw [hrest, mul_one] at hpr
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, mul_comm]
  exact hpr

end GlobalTheory.HCharUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.MuProps

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem atEmb_emb (w : InfinitePlace E) (z : ℂ) : atEmb w.embedding z = Pi.single w z := by
  unfold atEmb; simp [InfinitePlace.mk_embedding]

theorem chiInf_expU_single {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) (z : ℂ) :
    ((chiInf μ (expU (Pi.single v z)) : ℂˣ) : ℂ) =
      Complex.exp ((e v : ℂ) / 2 * z + (-(e v : ℂ) / 2) * starRingEnd ℂ z) := by
  rw [h.2.2.2.2, Finset.prod_eq_single v]
  · change (Complex.exp ((Pi.single v z : Cinf E) v) / ((‖Complex.exp ((Pi.single v z : Cinf E) v)‖ : ℝ) : ℂ)) ^ e v = _
    rw [Pi.single_eq_same, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub, ← Complex.exp_int_mul]
    congr 1
    have := Complex.add_conj z
    push_cast at this
    linear_combination ((e v : ℂ) / 2) * this
  · intro u _ hu
    change (Complex.exp ((Pi.single v z : Cinf E) u) / ((‖Complex.exp ((Pi.single v z : Cinf E) u)‖ : ℝ) : ℂ)) ^ e u = 1
    rw [Pi.single_eq_of_ne hu]
    simp
  · simp

theorem expo_emb {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) :
    expo μ v.embedding = (e v : ℂ) / 2 :=
  expo_eq_of_exp μ v.embedding _ (-(e v : ℂ) / 2) fun z => by
    rw [atEmb_emb]; exact chiInf_expU_single h v z

theorem expo_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) :
    expo μ (ComplexEmbedding.conjugate v.embedding) = -(e v : ℂ) / 2 :=
  expo_eq_of_exp μ _ _ ((e v : ℂ) / 2) fun z => by
    rw [atEmb_conj, atEmb_emb, chiInf_expU_single h v]
    congr 1
    simp only [Complex.conj_conj]
    ring

theorem dchi_single {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) (w : ℂ) :
    dchi μ (Pi.single v w) = (w.im : ℂ) * dchi μ (Pi.single v Complex.I) := by
  have h1 := expo_emb h v
  have h2 := expo_conj h v
  simp only [expo, atEmb_conj, atEmb_emb, map_one, Complex.conj_I, Pi.single_neg, map_neg] at h1 h2
  have hd1 : dchi μ (Pi.single v 1) = 0 := by linear_combination h1 + h2
  rw [← atEmb_emb, atEmb_eq, map_add, map_smul, map_smul, atEmb_emb, atEmb_emb, hd1]
  rw [smul_zero, zero_add, Complex.real_smul]

theorem dchi_neg_star {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (z : Cinf E) :
    dchi μ (-star z) = dchi μ z := by
  conv_lhs => rw [← Finset.univ_sum_single (-star z)]
  conv_rhs => rw [← Finset.univ_sum_single z]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dchi_single h v, dchi_single h v (z v), Pi.neg_apply, Pi.star_apply, Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg]

theorem finId_conjFin (u : (Af E)ˣ) :
    finId E (Units.map (conjFin (IsCMField.complexConj E).toRingEquiv).toMonoidHom u) =
      Units.map (conjAd E).toMonoidHom (finId E u) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = (infEq E) (starRingEnd (Cinf E) ((infEq E).symm ((1 : InfiniteAdeleRing E) - 0 + 0)))
    simp
  · change (1 : Af E) - 1 + conjFin (IsCMField.complexConj E).toRingEquiv (u : Af E) =
      conjFin (IsCMField.complexConj E).toRingEquiv ((1 : Af E) - 1 + (u : Af E))
    simp

theorem mu_mul_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (x : Neutral.B1.Ideles E) :
    μ.1 x * μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x) = 1 := by
  rw [← map_mul, ← GlobalTheory.GalOfCusp.ideleMap_ideleNorm, h.2.1]
  have := congrArg (fun c : HChar E => c.1 x) (GlobalTheory.GalOfCusp.compNorm_quadChar E)
  exact this

theorem thetaInv {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (a : ℕ) : ThetaInv a μ := by
  refine CG.thetaInv_of (fun u => ?_) (dchi_neg_star h)
  rw [map_inv, finId_conjFin, ← GlobalTheory.PolChar.ideleConj_eq, map_inv]
  have := mu_mul_conj h (finId E u)
  exact inv_eq_of_mul_eq_one_left this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → (∀ a, ThetaInv a μ) ∧ (∀ v : InfinitePlace E, expo μ v.embedding = (e v : ℂ) / 2) ∧ ∀ v : InfinitePlace E, expo μ (ComplexEmbedding.conjugate v.embedding) = -(e v : ℂ) / 2 :=
  fun _ _ _ _ _ _ _ h => ⟨thetaInv h, expo_emb h, expo_conj h⟩

end GlobalTheory.BCT.MuProps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem levOp_id_mem_inf_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) (F : G → ℂ) (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x)
    (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, ρ g v ∈ M) (v : V) (hv : v ∈ M ⊓ fixed ρ K') :
    levOp ρ K K' F LinearMap.id v ∈ M ⊓ fixed ρ K' := by
  obtain ⟨hvM, hvK⟩ := Submodule.mem_inf.1 hv
  have hfix : ∀ k ∈ K', ρ k v = v := fun k hk => by simpa using hvK ⟨k, hk⟩
  set φ : G ⧸ K' → V →ₗ[ℂ] V := fun q => F q.out • (ρ q.out ∘ₗ LinearMap.id) with hφ
  unfold levOp
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  by_cases hs : (Function.support φ).Finite
  · have hs' : (Function.support fun q => φ q v).Finite :=
      hs.subset (fun q hq h => hq (by simp [h]))
    have happ : (∑ᶠ q, φ q) v = ∑ᶠ q, φ q v := map_finsum (LinearMap.applyₗ v) hs
    rw [happ]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [finsum_eq_sum _ hs']
      exact Submodule.sum_mem _ fun q _ => M.smul_mem _ (hM _ _ hvM)
    · intro k
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      rw [map_finsum (ρ (k : G)) hs']
      have key : ∀ q : G ⧸ K', ρ (k : G) (φ q v) = φ ((k : G) • q) v := by
        intro q
        have hq : ((((k : G) • q).out : G) : G ⧸ K') = ((k : G) * q.out : G) := by
          rw [QuotientGroup.out_eq']
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        have hk2 : ((k : G) * q.out)⁻¹ * ((k : G) • q).out ∈ K' := QuotientGroup.eq.1 hq.symm
        obtain ⟨c, hc, hg'⟩ : ∃ c ∈ K', ((k : G) • q).out = (k : G) * q.out * c := ⟨_, hk2, by group⟩
        simp only [hφ, LinearMap.smul_apply, LinearMap.comp_id, map_smul]
        rw [hg', (hF _ hc _).2, (hF _ k.2 _).1, map_mul, Module.End.mul_apply, hfix _ hc, map_mul,
          Module.End.mul_apply]
      rw [finsum_congr key]
      exact finsum_comp_equiv (MulAction.toPerm (k : G)) (f := fun q => φ q v)
  · rw [finsum_of_infinite_support hs]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_mul_left_eq {w : Pl E} {U : Subgroup (UL n w)} (g : UL n w → ℂ) (hg : ∀ k ∈ U, ∀ x, g (k * x) = g x)
    (a : UL n w) (ha : a ∈ U) (y : GLw n w) : g (toSub (UL n w) (a.1 * y)) = g (toSub (UL n w) y) := by
  unfold toSub
  by_cases hy : y ∈ UL n w
  · rw [dif_pos (mul_mem a.2 hy), dif_pos hy, ← hg a ha ⟨y, hy⟩]
    rfl
  · have : a.1 * y ∉ UL n w := fun h => hy (by simpa using mul_mem (inv_mem a.2) h)
    rw [dif_neg this, dif_neg hy]

theorem toSub_mul_right_eq {w : Pl E} {U : Subgroup (UL n w)} (g : UL n w → ℂ) (hg : ∀ k ∈ U, ∀ x, g (x * k) = g x)
    (a : UL n w) (ha : a ∈ U) (y : GLw n w) : g (toSub (UL n w) (y * a.1)) = g (toSub (UL n w) y) := by
  unfold toSub
  by_cases hy : y ∈ UL n w
  · rw [dif_pos (mul_mem hy a.2), dif_pos hy, ← hg a ha ⟨y, hy⟩]
    rfl
  · have : y * a.1 ∉ UL n w := fun h => hy (by simpa using mul_mem h (inv_mem a.2))
    rw [dif_neg this, dif_neg hy]

theorem mem_globLev_iff (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (k : finU E n) :
    k ∈ globLev S K' ↔ ∀ w ∈ S, ∃ a ∈ K' w, (a : GLw n w) = cLoc w k.1 := by
  simp [globLev, Subgroup.mem_iInf]

theorem globFn_inv (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
    (hf : ∀ w, ∀ k ∈ K' w, ∀ x, f w (k * x) = f w x ∧ f w (x * k) = f w x) :
    ∀ k ∈ globLev S K', ∀ x, globFn S f (k * x) = globFn S f x ∧ globFn S f (x * k) = globFn S f x := by
  intro k hk x
  rw [mem_globLev_iff] at hk
  constructor
  · unfold globFn
    refine finprod_mem_congr rfl fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := hk w hw
    rw [Subgroup.coe_mul, map_mul, ← hae]
    exact toSub_mul_left_eq (f w) (fun k hk x => (hf w k hk x).1) a ha _
  · unfold globFn
    refine finprod_mem_congr rfl fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := hk w hw
    rw [Subgroup.coe_mul, map_mul, ← hae]
    exact toSub_mul_right_eq (f w) (fun k hk x => (hf w k hk x).2) a ha _

end GlobalTheory.BCT

open GlobalTheory.BCT in

theorem GlobalTheory.BCT.hop_mem_inf_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ v ∈ π ⊓ fixed (RF E n) (globLev S K'), hop S K' f v ∈ π ⊓ fixed (RF E n) (globLev S K') := by
  intro E _ _ _ n S _ K' _ f hf π hπ v hv
  exact levOp_id_mem_inf_fixed (RF E n) _ _ _ (globFn_inv S K' f fun w => (hf.1 w).2) π
    (fun g v hv => hπ.stable _ v hv) v hv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAddMulGeometricDegreeNonnegOfSmallSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_add_mul_geometricDegree_nonneg_of_smallSection : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → ∀ (C : HermLB p) (h : X → ℝ), C.SemiPos D → C.IsArithHeight h → (∀ z, z ≠ genericPoint X → 0 ≤ h z) → ∀ (m : ℕ) (u : ℝ), 0 < m → 0 ≤ u → (∃ s ∈ ((C.shift (fun _ => u) fun _ => rfl).pow m).smallSec, s ≠ 0) → 0 ≤ h (genericPoint X) + u * gdeg C D := by
  first | exact @GlobalTheory.HSNef.height_add_mul_gdeg_nonneg_of_smallSec | exact GlobalTheory.HSNef.height_add_mul_gdeg_nonneg_of_smallSec | (intros; apply GlobalTheory.HSNef.height_add_mul_gdeg_nonneg_of_smallSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianQuasiFiniteFinitePart
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.FinPolysIrr

theorem eig_norm_sq_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (y : grp G β) (a : PosV G v β) (hfix : FixL G v β y a.1) (w : InfinitePlace G.F) (μ : ℂ)
    (x : Fin G.n → ℂ) (hx : x ≠ 0) (hμ : G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *ᵥ x = μ • x) :
    ‖μ‖ ^ 2 = ((((y : G.Cˣ × ℚˣ).2 : ℚ)) : ℝ) := by
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G w β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G w β y
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hsig := G.sig w
  refine GlobalTheory.eig_norm_sq_of_similitude G.n (G.gram w) (herm G w β) (toV G w β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm w) Z _ ?_ ?_ hZ hs0 ?_ ?_ μ x hx hμ
  · rcases hsig with h | h <;> omega
  · have := G.n_pos
    rcases hsig with h | h <;> omega
  · rw [Complex.ofReal_ratCast]; exact hsim
  · by_cases hw : w = v
    · subst hw
      obtain ⟨c, hc⟩ := hfix
      exact Or.inr ⟨c, a.1, hc, a.2⟩
    · left
      have h1 : sigPosH (G.gram_herm w) ≠ 1 := by
        intro h1
        have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := ha.le
        have := Fintype.card_le_one_iff.1 hcard ⟨w, h1⟩ ⟨v, hv⟩
        exact hw (congrArg Subtype.val this)
      rcases hsig with h | h
      · exact absurd h.1 h1
      · exact h.1

theorem minpoly_coeff_bdd_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (S : ℝ) : ∃ B : ℝ, ∀ (y : grp G β) (a : PosV G v β),
    FixL G v β y a.1 → (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S → ∀ (φ : G.F →+* ℂ) (k : ℕ),
    ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  refine ⟨max (√(max S 0)) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y a hfix hS φ k
  set γ : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hγ
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly G.F γ).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le γ
  have hbd : ∀ (w : InfinitePlace G.F) (z : ℂ), (minpoly G.F γ).eval₂ w.embedding z = 0 → ‖z‖ ≤ √(max S 0) := by
    intro w z hz
    obtain ⟨x, hx, hzx⟩ := GlobalTheory.LKCx.PolyArch.roots_eig_any p G w γ z hz
    have h2 := eig_norm_sq_of_a_one p G ha v hv β hβ hR y a hfix w z x hx hzx
    have h3 : ‖z‖ ^ 2 ≤ max S 0 := h2 ▸ le_max_of_le_left hS
    simpa using Real.abs_le_sqrt h3
  have hroots : ∀ z ∈ ((minpoly G.F γ).map φ).roots, ‖z‖ ≤ √(max S 0) := by
    intro z hz
    have hr : (minpoly G.F γ).eval₂ φ z = 0 := by
      have := (Polynomial.mem_roots'.1 hz).2
      rwa [Polynomial.IsRoot, Polynomial.eval_map] at this
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [← h] at hr; exact hbd _ z hr
    · have hr' : (minpoly G.F γ).eval₂ (InfinitePlace.mk φ).embedding (starRingEnd ℂ z) = 0 := by
        rw [h]
        have := congrArg (starRingEnd ℂ) hr
        rw [map_zero, Polynomial.hom_eval₂] at this
        convert this using 2
        exact RingHom.ext fun x => rfl
      simpa using hbd _ _ hr'
  have := Polynomial.coeff_bdd_of_roots_le φ (minpoly.monic hint) (IsAlgClosed.splits _) hdeg hroots k
  rwa [Polynomial.coeff_map] at this

end GlobalTheory.LKCx.FinPolysIrr

namespace GlobalTheory.LKCx

open GlobalTheory.LKCx.FinPolysIrr in

theorem finite_minpoly_fix_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsym hR
  obtain ⟨D, hD, hDy⟩ := GlobalTheory.T.minpoly_bounded_denominators p G L f hf β x t hx
  obtain ⟨Bp, hBp⟩ := GlobalTheory.T.minpoly_padic_bounded p G K' f' hf' β
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.bounded_denominator_integral_power G.F p Bp
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support p G L f hf K' f' hf' β x t hx
  obtain ⟨B, hB⟩ := minpoly_coeff_bdd_of_a_one p G ha v hv β hsym hR S
  have hpD : 0 < p ^ m₀ * D := Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hD
  refine (GlobalTheory.T.finite_monic_bounded_polynomials G.F (G.n ^ 2) (p ^ m₀ * D) B hpD).subset ?_
  rintro P ⟨y, a, rfl, hfix, hne⟩
  have h1 : f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) ≠ 0 := left_ne_zero_of_mul hne
  have h2 : f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0 := right_ne_zero_of_mul hne
  have hint : IsIntegral G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly.monic hint, ?_, fun k => ⟨?_, fun φ => hB y a.2 hfix (hS y a.1.1 a.1.2 h1 h2) φ k⟩⟩
  · rw [← G.rankC]; exact minpoly.natDegree_le _
  · have := hm₀ _ D (hDy y a.1.1 h1 k) (fun φ => hBp y a.1.2 h2 φ k)
    push_cast
    simpa [mul_assoc] using this

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} :=
  finite_minpoly_fix_a_one

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContinuousCrystallineMatrixRepOfIntertwinesDetStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isContinuousCrystallineMatrixRep_of_intertwines_det_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (f n : ℕ) (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r r' : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (U : ZMod f → Multiset ℤ) (a : Mx ↥(OL LL) n n), MatGood P emb r U → Tw r' r a → a.det ≠ 0 → MatGood P emb r' U := by
  first | exact @GlobalTheory.WachPlace.matGood_of_tw | exact GlobalTheory.WachPlace.matGood_of_tw | (intros; apply GlobalTheory.WachPlace.matGood_of_tw <;> assumption)
end

