import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLocalRingOfVarietyPointResidueCStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleCoords_localRingOfVarietyPoint_residueComplex : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B),
    RatRes (algebraMap ℂ κ') B → ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth →
    ∃ (r : ℕ) (τ : Fin r → B), (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
      (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
      TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) := by
  first | exact @GlobalTheory.EtaleCoordLocal.exists_etaleCoords | exact GlobalTheory.EtaleCoordLocal.exists_etaleCoords | (intros; apply GlobalTheory.EtaleCoordLocal.exists_etaleCoords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointCutToFibreUnionStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryPoint_cut_to_fibreUnion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Set (Pl E)),
    (∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P) →
    ∀ g ∈ finU E n, ∃ x ∈ finU E n, ∀ v : Pl E, cLoc v x = if v ∈ P then cLoc v g else 1 := by
  first | exact @GlobalTheory.FibreCut.exists_cut | exact GlobalTheory.FibreCut.exists_cut | (intros; apply GlobalTheory.FibreCut.exists_cut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamilyStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryPoint_of_local_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ y : ∀ w : Pl E, UL n w, (∀ᶠ w in cofinite, y w ∈ KL n w) → ∃ x : finU E n, ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = y w := by
  first | exact @GlobalTheory.BCT.exists_finU_of_loc | exact GlobalTheory.BCT.exists_finU_of_loc | (intros; apply GlobalTheory.BCT.exists_finU_of_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteControllingPoints
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem exists_finite_controlling_points : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∃ S : Set X, S.Finite ∧ ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ τ g : X.functionField, RegAt x τ → (∀ z ∈ S, z ⤳ x → UnitAt z τ) → RegAt x g → RegAt x (g * τ / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j) := by
  intro k _ X _ p D hX P s hs hs0
  have : IsNoetherian X := hX.isNoetherian
  have hloc0 : ∀ (i : P.L.B.ι) (j : P.A.B.ι), P.loc 0 1 s i j = s * (P.r' j : X.functionField) := by
    intro i j; simp [Pair.loc]
  have hloc : ∀ x : X, ∃ (V : X.Opens) (j : P.A.B.ι) (_ : IsAffineOpen V) (hx : x ∈ V) (a : Γ(X, V)),
      V ≤ P.A.B.U j ∧ fnOf V (gen_mem hx) a = s * (P.r' j : X.functionField) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (P.L.isLB.cover ▸ Opens.mem_top x : x ∈ ⨆ i, P.L.B.U i)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (P.A.isLB.cover ▸ Opens.mem_top x : x ∈ ⨆ j, P.A.B.U j)
    obtain ⟨c, hc⟩ := hs x i j hi hj
    obtain ⟨U, hxU, f, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf c
    obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ U ⊓ P.A.B.U j from ⟨hxU, hj⟩)
    refine ⟨V, j, hV, hxV, resG X (hVW.trans inf_le_left) f, hVW.trans inf_le_right, ?_⟩
    rw [fnOf_resG, ← algebraMap_germ hxU, hc, hloc0]
  choose V jj hV hxV a hVj ha using hloc
  have hne : ∀ y, fnOf (V y) (gen_mem (hxV y)) (a y) ≠ 0 := by
    intro y; rw [ha]; exact mul_ne_zero hs0 (P.r' (jj y)).ne_zero
  choose T hTfin hT using fun y => GlobalTheory.T.exists_finite_points_regular_div_affineOpen X (V y) (hV y) (gen_mem (hxV y)) (a y) (hne y)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hxV y⟩)
  refine ⟨⋃ y ∈ t, T y, t.finite_toSet.biUnion fun y _ => hTfin y, ?_⟩
  intro x i j hi hj τ g hτ hS hg hgτ
  obtain ⟨y, hyt, hxy⟩ : ∃ y ∈ t, x ∈ V y := by
    have := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, h⟩ := this
    exact ⟨y, hy, h⟩
  have hxj' : x ∈ P.A.B.U j ⊓ P.A.B.U (jj y) := ⟨hj, hVj y hxy⟩
  set w : X.functionField := fnOf _ (gen_mem hxj') (P.A.B.g j (jj y) : Γ(X, P.A.B.U j ⊓ P.A.B.U (jj y))) with hw
  have hwu : UnitAt x w := unitAt_fnOf hxj' _ _
  have hw0 : w ≠ 0 := hwu.ne_zero
  have hrel : P.loc 0 1 s i j = fnOf (V y) (gen_mem (hxV y)) (a y) * w := by
    rw [hloc0, ha, P.hr' j (jj y) (gen_mem hxj')]; ring
  rw [hrel] at hgτ ⊢
  set σ := fnOf (V y) (gen_mem (hxV y)) (a y)
  have h1 : RegAt x (g * τ / σ) := by
    have := hgτ.mul hwu.regAt
    convert this using 1
    field_simp
  have h2 := hT y x hxy τ g hτ (fun z hz hzx => hS z (Set.mem_biUnion hyt hz) hzx) hg h1
  have := h2.mul hwu.inv.regAt
  convert this using 1
  rw [div_mul_eq_div_div, div_eq_mul_inv (g / σ)]

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCompletionLatticeEqColumnsStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_completion_lattice_eq_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ L : Submodule K.O B.A, GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ g : GLw m w, GlobalTheory.TwLat.lat e b g = L := by
  first | exact @GlobalTheory.TwLat.exists_GLw_lat_eq | exact GlobalTheory.TwLat.exists_GLw_lat_eq | (intros; apply GlobalTheory.TwLat.exists_GLw_lat_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLattice
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

theorem exists_lat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A)
    (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ q : GLw a w, GlobalTheory.TwLat.lat e b q = L := by
  intro E _ _ _ w K e a B b L hL
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors K.O B.A := ⟨fun {r x} h => by
    rw [← algebraMap_smul K.E r x] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)
    · right; exact h⟩
  haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'
  let y := Module.Free.chooseBasis K.O L
  let v : Module.Free.ChooseBasisIndex K.O L → B.A := fun i => (y i : B.A)
  have hli : LinearIndependent K.O v := y.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliE : LinearIndependent K.E v := (LinearIndependent.iff_fractionRing K.O K.E).mp hli
  have hLv : Submodule.span K.O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range y := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, y.span_eq, Submodule.map_subtype_top]
  have hspE : Submodule.span K.E (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower K.O K.E, hLv]; exact hspan
  let c := Module.Basis.mk hliE hspE.ge
  let c' := c.reindex (c.indexEquiv b)
  let U : (Matrix (Fin a) (Fin a) K.E)ˣ :=
    ⟨b.toMatrix c', c'.toMatrix b, b.toMatrix_mul_toMatrix_flip c', c'.toMatrix_mul_toMatrix_flip b⟩
  refine ⟨Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U, ?_⟩
  rw [latOf_eq, ← hLv]
  have hcol : ∀ j, (ofCrd e b fun i =>
      (Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U).val i j) = c' j := by
    intro j
    rw [← ofCrd_crd e b (c' j)]
    congr 1
  simp only [hcol]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨(c.indexEquiv b).symm j, ?_⟩
    simp [c', c, v]
  · rintro ⟨i, rfl⟩
    refine ⟨c.indexEquiv b i, ?_⟩
    simp [c', c, v]

end GlobalTheory.TwOrbLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjEigenSystemCongruentStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisConj_eigenSystem_congruent : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), F.Ok → ∀ (θ θ0 : F.I → PadicAlgCl l) (m : Ideal F.T), F.IsEig lam θ → F.Over θ m → F.Over θ0 m → ∃ θ', F.IsEig lam θ' ∧ (∀ i, ‖θ' i‖ ≤ 1) ∧ ∀ i, ‖θ' i - θ0 i‖ < 1 := by
  first | exact @GlobalTheory.ExpFrame.Conj.exists_eig_congr | exact GlobalTheory.ExpFrame.Conj.exists_eig_congr | (intros; apply GlobalTheory.ExpFrame.Conj.exists_eig_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIffEtaProd
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadRecip

open GlobalTheory.QuadSymbol

theorem exists_global_iff_etaProd (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (x : FinFam K) (y : InfFam K)
    (hx : AlmostNorm K L x) :
    (∃ t : Kˣ, (∀ v, x v / finDiag K t v ∈ normGroup K L (v.adicCompletion K)) ∧
        ∀ w, y w / infDiag K t w ∈ normGroup K L w.Completion) ↔
      etaProd K L x y = 1 :=
  (exactSequence K L).2.2.1 x y hx

theorem ringEquivReal_infDiag {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}
    (hw : w.IsReal) (t : Kˣ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infDiag K t w : (w.Completion)ˣ) : w.Completion) =
      InfinitePlace.embedding_of_isReal hw (t : K) :=
  InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv _).symm (t : K))

theorem mem_normGroup_of_pos {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] {w : InfinitePlace K} (hw : w.IsReal) (z : (w.Completion)ˣ)
    (hz : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (z : w.Completion)) :
    z ∈ normGroup K L w.Completion := by
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  rw [mem_normGroup_iff_form b h0 h1]
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  refine ⟨e.symm (Real.sqrt (e z)), 0, e.injective ?_⟩
  simp [Real.sq_sqrt hz.le]

theorem mem_normGroup_iff_pos {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : IsTotallyComplex L)
    {w : InfinitePlace K} (hw : w.IsReal) (z : (w.Completion)ˣ) :
    z ∈ normGroup K L w.Completion ↔
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (z : w.Completion) := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  refine ⟨fun hz => ?_, mem_normGroup_of_pos hw z⟩
  have hne : e (z : w.Completion) ≠ 0 := (map_ne_zero e).2 z.ne_zero
  refine lt_of_le_of_ne (not_lt.1 fun hlt => ?_) hne.symm
  have hm : (-z) ∈ normGroup K L w.Completion :=
    mem_normGroup_of_pos hw (-z) (by rw [Units.val_neg, map_neg]; exact neg_pos.2 hlt)
  have h1 : (-1 : (w.Completion)ˣ) = z * (-z)⁻¹ := by rw [inv_neg, mul_neg, mul_inv_cancel]
  exact SignCount.neg_one_not_mem_normGroup hL hw (h1 ▸ mul_mem hz (inv_mem hm))

end GlobalTheory.QuadRecip

namespace GlobalTheory.QuadRecip

open GlobalTheory.QuadSymbol

open Classical in

theorem prod_sign_eq {K : Type} [Field K] [NumberField K] (S : Finset {w : InfinitePlace K // w.IsReal})
    (f : InfinitePlace K → ℤˣ)
    (hf : ∀ w, f w = if (∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S) then -1 else 1) :
    ∏ w, f w = (-1) ^ S.card := by
  classical
  simp_rw [hf]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 1
  have : (Finset.univ.filter fun w : InfinitePlace K =>
      ∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S) =
      S.map (Function.Embedding.subtype _) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨hw, h⟩
      exact ⟨_, h, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
  rw [this, Finset.card_map]

open Classical in

theorem exists_signs_iff_even (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : IsTotallyComplex L)
    (S : Finset {w : InfinitePlace K // w.IsReal}) :
    (∃ h : Kˣ, (∀ w : {w : InfinitePlace K // w.IsReal},
        (w ∈ S → InfinitePlace.embedding_of_isReal w.2 (h : K) < 0) ∧
        (w ∉ S → 0 < InfinitePlace.embedding_of_isReal w.2 (h : K))) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), finDiag K h v ∈ normGroup K L (v.adicCompletion K)) ↔
      Even S.card := by
  classical
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hneg1 : ((-1 : ℤˣ) ≠ 1) := by decide
  constructor
  · rintro ⟨h, hsgn, hfin⟩
    have hpf := (productFormula K L h).2
    unfold etaProd at hpf
    have hf1 : ∀ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (finDiag K h v) = 1 :=
      fun v => eta_eq_one_iff.2 (hfin v)
    simp only [hf1, finprod_one, one_mul] at hpf
    rw [prod_sign_eq S _ (fun w => ?_)] at hpf
    · exact (neg_one_pow_eq_one_iff_even hneg1).1 hpf
    · by_cases hw : w.IsReal
      · have key := mem_normGroup_iff_pos hL hw (infDiag K h w)
        rw [ringEquivReal_infDiag hw h] at key
        by_cases hS : (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S
        · rw [if_pos ⟨hw, hS⟩, eta_eq_neg_one_iff, key]
          exact not_lt.2 ((hsgn ⟨w, hw⟩).1 hS).le
        · rw [if_neg (by rintro ⟨hw', h'⟩; exact hS h'), eta_eq_one_iff, key]
          exact (hsgn ⟨w, hw⟩).2 hS
      · rw [if_neg (by rintro ⟨hw', _⟩; exact hw hw'), eta_eq_one_iff]
        exact Converse.mem_normGroup_of_isComplex b h0 h1 (InfinitePlace.not_isReal_iff_isComplex.1 hw) _
  · intro hS
    let P : InfinitePlace K → Prop := fun w =>
      ∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S
    let y : InfFam K := fun w => if P w then -1 else 1
    have hy : ∀ w, eta K L w.Completion (y w) = if P w then -1 else 1 := by
      intro w
      by_cases hP : P w
      · simp only [y, if_pos hP]
        exact eta_eq_neg_one_iff.2 (SignCount.neg_one_not_mem_normGroup hL hP.1)
      · simp only [y, if_neg hP]
        exact eta_eq_one_iff.2 (one_mem _)
    have hx : AlmostNorm K L (1 : FinFam K) := by
      refine Set.Finite.subset Set.finite_empty fun v hv => hv ?_
      exact one_mem _
    have hprod : etaProd K L 1 y = 1 := by
      unfold etaProd
      have hf1 : ∀ v : HeightOneSpectrum (𝓞 K),
          eta K L (v.adicCompletion K) ((1 : FinFam K) v) = 1 := fun v => eta_eq_one_iff.2 (one_mem _)
      simp only [hf1, finprod_one, one_mul]
      rw [prod_sign_eq S _ hy]
      exact hS.neg_one_pow
    obtain ⟨t, htf, hti⟩ := (exists_global_iff_etaProd K L 1 y hx).2 hprod
    refine ⟨t, fun w => ?_, fun v => ?_⟩
    · have key := (mem_normGroup_iff_pos hL w.2 _).1 (hti w.1)
      rw [Units.val_div_eq_div_val, map_div₀, ringEquivReal_infDiag w.2 t] at key
      have hP : P w.1 ↔ w ∈ S := ⟨by rintro ⟨_, h⟩; exact h, fun h => ⟨w.2, h⟩⟩
      constructor
      · intro hw
        have hyw : y w.1 = -1 := if_pos (hP.2 hw)
        rw [hyw, Units.val_neg, Units.val_one, map_neg, map_one] at key
        have := (div_pos_iff.1 key)
        rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
        · linarith
        · exact h2
      · intro hw
        have hyw : y w.1 = 1 := if_neg (fun h => hw (hP.1 h))
        rw [hyw, Units.val_one, map_one] at key
        exact (one_div_pos).1 key
    · have := htf v
      rw [Pi.one_apply, one_div, inv_mem_iff] at this
      exact this

theorem exists_signs_of_even (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hK : IsTotallyReal K) (hL : IsTotallyComplex L)
    (S : Finset (InfinitePlace K)) (hS : Even S.card) :
    ∃ h : Kˣ, (∀ w (hw : w ∈ S), InfinitePlace.embedding_of_isReal (hK.isReal w) (h : K) < 0) ∧
      (∀ w (hw : w ∉ S), 0 < InfinitePlace.embedding_of_isReal (hK.isReal w) (h : K)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), finDiag K h v ∈ normGroup K L (v.adicCompletion K) := by
  classical
  let S' : Finset {w : InfinitePlace K // w.IsReal} := S.subtype _
  have hc : S'.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem fun w _ => hK.isReal w
  obtain ⟨h, hsgn, hfin⟩ := (exists_signs_iff_even K L hL S').2 (hc ▸ hS)
  refine ⟨h, fun w hw => (hsgn ⟨w, hK.isReal w⟩).1 ?_, fun w hw => (hsgn ⟨w, hK.isReal w⟩).2 ?_, hfin⟩
  · simpa [S'] using hw
  · simpa [S'] using hw

end GlobalTheory.QuadRecip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSphericalVectorOfSatakeFamilyStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_spherical_vector_of_satake_family : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ), (∀ w ∉ S, GlobalTheory.LFun.HasSatGL w (π.locRep w) (B w)) → ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w a, act (.fin (locGL E a w k)) φ = φ := by
  first | exact @GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat | exact GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat | (intros; apply GlobalTheory.JSW.SphVec.exists_sphVec_of_hasSat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPatchOfComplexPointOpenPart
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem exists_goodPatch_of_mem : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ y ∈ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  intro F _ σ X m E O H hH y hy
  classical
  obtain ⟨ch, hc⟩ := AlgChart.exists_mem_source (D := X.dim) (p := X.str) (σ := σ) y
  obtain ⟨A, hA⟩ := E.nonempty (under y)
  have hhol : IsHoloChart ch.e := ch.holo
  obtain ⟨hsm, hu⟩ := GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hhol hy hc hA
  set G : V X.dim → Matrix (Fin m) (Fin m) ℂ := fun v => H A (ch.e.symm v) () with hG
  have h1 : ((0 : WithTop ℕ∞) + 1) ≤ ∞ := by exact_mod_cast le_top
  have h2 : ((0 : WithTop ℕ∞) + 2) ≤ ∞ := by
    rw [zero_add]
    first
    | exact (WithTop.coe_le_coe (a := (2 : ℕ∞)) (b := ⊤)).2 le_top
    | exact ENat.LEInfty.out
    | simp
    | decide
  have hconn : ∀ (a : Fin X.dim) (i j : Fin m),
      ContinuousAt (fun z => conn G (ch.e z) (coordVec a) i j) y := fun a i j =>
    ((hsm.conn hu h1 (coordVec a)) i j).continuousAt.comp (ch.e.continuousAt hc)
  have hcurv : ∀ (a b : Fin X.dim) (i j : Fin m),
      ContinuousAt (fun z => curv G (ch.e z) (coordVec a) (coordVec b) i j) y := fun a b i j =>
    ((hsm.curv hu h2 (coordVec a) (coordVec b)) i j).continuousAt.comp (ch.e.continuousAt hc)
  let C : ℝ := (∑ a : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1)) +
    ∑ a : Fin X.dim, ∑ b : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m,
      (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1)
  have hP1 : ∀ a i j, ‖conn G (ch.e y) (coordVec a) i j‖ + 1 ≤ C := by
    intro a i j
    refine le_add_of_le_of_nonneg ?_ (by positivity)
    refine (Finset.single_le_sum (f := fun j => ‖conn G (ch.e y) (coordVec a) i j‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ i)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ i : Fin m, ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ a)
  have hP2 : ∀ a b i j, ‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1 ≤ C := by
    intro a b i j
    refine le_add_of_nonneg_of_le (by positivity) ?_
    refine (Finset.single_le_sum (f := fun j => ‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ i)).trans ?_
    refine (Finset.single_le_sum (f := fun b => ∑ i : Fin m, ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ b)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ b : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ a)
  let T : Set (CxPts X.str σ) := {z | z ∈ ch.e.source ∧ z ∈ ptsIn X.str σ O ∧ A ∈ E.S (under z) ∧
    (∀ a i j, ‖conn G (ch.e z) (coordVec a) i j‖ ≤ C) ∧
    (∀ a b i j, ‖curv G (ch.e z) (coordVec a) (coordVec b) i j‖ ≤ C)}
  have hT : T ∈ 𝓝 y := by
    have e1 : ∀ᶠ z in 𝓝 y, ∀ a i j, ‖conn G (ch.e z) (coordVec a) i j‖ ≤ C := by
      simp only [eventually_all]
      intro a i j
      filter_upwards [(hconn a i j).norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      exact hz.le.trans ((le_refl _).trans (by linarith [hP1 a i j]))
    have e2 : ∀ᶠ z in 𝓝 y, ∀ a b i j, ‖curv G (ch.e z) (coordVec a) (coordVec b) i j‖ ≤ C := by
      simp only [eventually_all]
      intro a b i j
      filter_upwards [(hcurv a b i j).norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      exact hz.le.trans ((le_refl _).trans (by linarith [hP2 a b i j]))
    filter_upwards [ch.e.open_source.mem_nhds hc, (isOpen_ptsIn (p := X.str) (σ := σ) O).mem_nhds hy,
      GlobalTheory.T.adaptedFrame_eventually_near_complexPoint E hA, e1, e2] with z h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  refine ⟨ch.e, ∅, A, interior T, C, mem_interior_iff_mem_nhds.2 hT, ?_⟩
  have hsub : ∀ z ∈ interior T, z ∈ T := fun z hz => interior_subset hz
  refine ⟨hhol, isOpen_interior, fun z hz => (hsub z hz).1, fun z hz => (hsub z hz).2.2.1,
    fun z _ a ha => absurd ha (Finset.notMem_empty a), fun z hz => ?_, fun z hz _ a i j => ?_,
    fun z hz _ a b i j => ?_⟩
  · simp only [Finset.notMem_empty, false_imp_iff, implies_true, iff_true]
    exact (hsub z hz).2.1
  · simp only [poinWt, Finset.notMem_empty, if_false, mul_one]
    exact (hsub z hz).2.2.2.1 a i j
  · simp only [poinWt, Finset.notMem_empty, if_false, mul_one]
    exact (hsub z hz).2.2.2.2 a b i j

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermPairSectionsChangeOfIsometricCombinatiStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermPairSections_change_of_isometric_combinations : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M N : HermLB p), P.Rep a b M → P.Rep a' b' N → ∃ Q : Pair p, Q.L = M ∧ Q.A = N ∧ ∀ (i j : ℤ) (R : ℝ), Q.Bl i j R = P.Bl (i * a + j * a') (i * b + j * b') R := by
  first | exact @GlobalTheory.HSNef.change_pair | exact GlobalTheory.HSNef.change_pair | (intros; apply GlobalTheory.HSNef.change_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasisStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianModel_of_orthonormal_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.exists_model_of_orthonormal_basis | exact GlobalTheory.KapLat.exists_model_of_orthonormal_basis | (intros; apply GlobalTheory.KapLat.exists_model_of_orthonormal_basis <;> assumption)
end

