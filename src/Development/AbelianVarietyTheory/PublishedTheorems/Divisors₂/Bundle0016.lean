import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.Published

def NefProductNonneg : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (d : ℕ),
    IsProjOver (strHom k X) → topologicalKrullDim X = d →
    ∀ N : Fin d → LB X, (∀ i, IsNef k (N i)) → 0 ≤ interNum k (structureModule X) N

def NefBigIff : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)]
    (D : ℕ), IsProjOver (strHom k X) → topologicalKrullDim X = D →
    ∀ N : LB X, IsNef k N → (IsBig k N ↔ 0 < topSelfIntersection k N D)

def NefRiemannRoch : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (D : ℕ),
    IsProjOver (strHom k X) → topologicalKrullDim X = D →
    ∀ L : LB X, IsNef k L →
      (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L D : ℝ) * (m : ℝ) ^ D / D.factorial)
        =O[atTop] fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1)

def NefNumerics : Prop := NefProductNonneg ∧ NefBigIff ∧ NefRiemannRoch

theorem dim_affineOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) :=
  (topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
    hU.range_fromSpec).trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U)))

theorem dim_le_of_isIntegralHom {X Y : Scheme.{0}} (π : Y ⟶ X) [IsIntegralHom π] :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  refine ⟨(π ⁻¹ᵁ U : Y.Opens), (π ⁻¹ᵁ U).isOpen, hy, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le X (U : Set X))
  rw [dim_affineOpen (hU.preimage π), dim_affineOpen hU]
  letI := (π.app U).hom.toAlgebra
  have : Algebra.IsIntegral Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := ⟨IsIntegralHom.isIntegral_app π U hU⟩
  exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(Y, π ⁻¹ᵁ U)))
    fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h

theorem exists_algClosed_baseChange {k : Type} [Field k] {X : Scheme.{0}} [a : Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k X)) :
    ∃ (X' : Scheme.{0}) (_ : Algebra (AlgebraicClosure k) Γ(X', ⊤)) (π : X' ⟶ X),
      IsProjOver (strHom (AlgebraicClosure k) X') ∧
      topologicalKrullDim X' = topologicalKrullDim X ∧
      (∀ L : LB X, IsNef k L → IsNef (AlgebraicClosure k) (L.pull π)) ∧
      (∀ L : LB X, L.IsLB → lbH0 (AlgebraicClosure k) (L.pull π) = lbH0 k L) ∧
      ∀ (d : ℕ) (L : Fin d → LB X), (∀ i, (L i).IsLB) →
        interNum (AlgebraicClosure k) (structureModule X') (fun i => (L i).pull π) =
          interNum k (structureModule X) L := by
  obtain ⟨f, rfl⟩ : ∃ f : X ⟶ Sp k, a = algebraΓOfHom f :=
    ⟨strHom k X, Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)⟩
  letI := algebraΓOfHom f
  rw [strHom_eq (f := f) fun _ => rfl] at hp
  have H := IsPullback.of_hasPullback f (spMap (algebraMap k (AlgebraicClosure k)))
  set π := pullback.fst f (spMap (algebraMap k (AlgebraicClosure k)))
  set f' := pullback.snd f (spMap (algebraMap k (AlgebraicClosure k)))
  letI := algebraΓOfHom f'
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hp
  have : IsIntegralHom (spMap (algebraMap k (AlgebraicClosure k))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  have : IsIntegralHom π := MorphismProperty.of_isPullback (P := @IsIntegralHom) H.flip this
  have : IsProper (strHom k X) := by rwa [strHom_eq (f := f) fun _ => rfl]
  refine ⟨_, algebraΓOfHom f', π, ?_, ?_, fun L h => ?_, fun L hL => ?_, fun d L hL => ?_⟩
  · rw [strHom_eq (f := f') fun _ => rfl]
    exact PosBaseChange.isProjOver_of_isPullback H hp
  · exact (dim_le_of_isIntegralHom π).antisymm
      (PosBaseChange.dim_le_of_isClosedMap π.isClosedMap (PosBaseChange.surjective_proj H))
  · exact PosBaseChange.isNef_pull h hA (hA.pull_of_isAffineHom π) π π.isClosedMap
  · exact FieldChangeInter.hdim_pull H hL 0
  · exact FieldChangeInter.interNum_pull H hL

section AnyField

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {D : ℕ}

theorem NefProductNonneg.interNum_nonneg (h : NefProductNonneg) (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = D) {N : Fin D → LB X} (hN : ∀ i, IsNef k (N i)) :
    0 ≤ interNum k (structureModule X) N := by
  obtain ⟨X', _, π, hp', hd, hn, -, hi⟩ := exists_algClosed_baseChange hp
  rw [← hi D N fun i => (hN i).isLB]
  exact h _ X' D hp' (hd.trans hD) _ fun i => hn _ (hN i)

theorem NefProductNonneg.interNumOn_nonneg (h : NefProductNonneg) (hp : IsProjOver (strHom k X))
    {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (hD : topologicalKrullDim Z = D)
    {N : Fin D → LB X} (hN : ∀ j, IsNef k (N j)) : 0 ≤ interNumOn k i N := by
  letI := algebraΓAlong k i
  have hi := appTop_algebraMap_along k i
  rw [interNumOn_eq_interNum_pull hi fun j => (hN j).isLB]
  refine h.interNum_nonneg ?_ hD fun j => (hN j).pull_of_isClosedImmersion i hi
  obtain ⟨n, e, he, hs⟩ := hp
  exact ⟨n, i ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩

theorem NefProductNonneg.interNumRed_nonneg (h : NefProductNonneg) (hp : IsProjOver (strHom k X))
    {Z : Closeds X} (hD : topologicalKrullDim (Z : Set X) = D)
    {N : Fin D → LB X} (hN : ∀ j, IsNef k (N j)) : 0 ≤ interNumRed k Z N :=
  h.interNumOn_nonneg hp (redι Z) ((topologicalKrullDim_red Z).trans hD) hN

theorem NefRiemannRoch.isBigO (h : NefRiemannRoch) (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L D : ℝ) * (m : ℝ) ^ D / D.factorial)
      =O[atTop] fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1) := by
  obtain ⟨X', _, π, hp', hd, hn, h0, hi⟩ := exists_algClosed_baseChange hp
  have hL' := LB.isLB_pull hL.isLB π
  refine (h _ X' D hp' (hd.trans hD) _ (hn _ hL)).congr_left fun m => ?_
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL' m) (LB.isLB_pull (isLB_lbPow hL.1 m) π)
    (by rw [cls_lbPow hL', cls_pull hL.1, cls_pull (isLB_lbPow hL.1 m), cls_lbPow hL.1, map_nsmul]),
    h0 _ (isLB_lbPow hL.1 m), topSelf_def, hi D (fun _ => L) fun _ => hL.1, topSelf_def]

theorem NefRiemannRoch.tendsto (h : NefRiemannRoch) (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    Tendsto (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) / (m : ℝ) ^ D) atTop
      (nhds ((topSelfIntersection k L D : ℝ) / D.factorial)) := by
  have ho : (fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1)) =o[atTop] fun m : ℕ => (m : ℝ) ^ D := by
    refine (isLittleO_iff_tendsto' ?_).2 ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).congr' ?_)
    · filter_upwards [eventually_gt_atTop 0] with m hm h0
      exact absurd h0 (by positivity)
    · filter_upwards [eventually_gt_atTop 0] with m hm
      have : (m : ℝ) ≠ 0 := by positivity
      rw [zpow_sub_one₀ this, zpow_natCast]
      field_simp
  have ht := ((h.isBigO hp hD hL).trans_isLittleO ho).tendsto_div_nhds_zero.add_const
    ((topSelfIntersection k L D : ℝ) / D.factorial)
  rw [zero_add] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem NefRiemannRoch.topSelf_nonneg (h : NefRiemannRoch) (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) : 0 ≤ topSelfIntersection k L D := by
  have h0 := ge_of_tendsto' (h.tendsto hp hD hL) fun m => (by positivity : (0 : ℝ) ≤ _)
  have hf : (0 : ℝ) < D.factorial := by positivity
  exact_mod_cast (div_nonneg_iff.1 h0).elim And.left fun h' => absurd h'.2 hf.not_ge

theorem NefRiemannRoch.isBig_iff (h : NefRiemannRoch) (hp : IsProjOver (strHom k X))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    IsBig k L ↔ 0 < topSelfIntersection k L D := by
  have ht := h.tendsto hp hD hL
  have hf : (0 : ℝ) < D.factorial := by positivity
  rw [GlobalTheory.isBig_iff (algebraMap_eq_strHom k X) hp hD, ← Int.cast_pos (R := ℝ),
    ← div_pos_iff_of_pos_right hf]
  refine ⟨fun ⟨_, c, hc, hm⟩ => hc.trans_le (ge_of_tendsto_of_frequently ht
    ((hm.and_eventually (eventually_gt_atTop 0)).mono fun m hm => ?_)),
    fun ha => ⟨hL.isLB, _, half_pos ha, Eventually.frequently ?_⟩⟩
  · have := hm.2
    exact (le_div_iff₀ (by positivity)).2 hm.1
  · filter_upwards [ht.eventually_const_le (half_lt_self ha), eventually_gt_atTop 0] with m h₁ h₂
    exact (le_div_iff₀ (by positivity)).1 h₁

end AnyField

theorem NefRiemannRoch.nefBigIff (h : NefRiemannRoch) : NefBigIff :=
  fun _ _ _ _ _ _ _ hp hD _ hL => h.isBig_iff hp hD hL

open GlobalTheory.ProjSpace in

example (k : Type) [Field k] (d : ℕ) :
    IsIntegral (PSpace k (d + 1)) ∧ IsProjOver (strHom k (PSpace k (d + 1))) ∧
    topologicalKrullDim (PSpace k (d + 1)) = (d + 1 : ℕ) ∧
    IsNef k (O1 k (d + 1)) ∧ IsBig k (O1 k (d + 1)) ∧
    IsNef k (LB.triv (PSpace k (d + 1))) ∧ ¬ IsBig k (LB.triv (PSpace k (d + 1))) := by
  rw [strHom_eq (algebraMap_top_eq k (d + 1))]
  exact ⟨inferInstance, isProjOver_str k _, topologicalKrullDim_eq k _, isNef_twistingSheaf k _, isBig_twistingSheaf k _,
    (triv_nef_not_big k d).1, (triv_nef_not_big k d).2.2⟩

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.Published.ChernDegreeComplexModel

variable (Y : Var ℂ)

theorem exists_presents {L : LB Y.X} (φ : Weight Y.str (RingHom.id ℂ) L) :
    ∃ (Δ : Y.Dv) (r : L.ι → Y.Fnˣ), Presents Δ L r := by
  obtain ⟨i₀, h₀⟩ := exists_chart φ.isLB (genericPoint Y.X)
  exact ⟨ofLB φ.isLB i₀ h₀, frameRat L i₀ h₀, presents_ofLB φ.isLB i₀ h₀⟩

theorem hyp_proj (n : ℕ) : ∃ r, Presents (projHyp ℂ n) (proj ℂ n).O1 r ∧
    (fs (proj ℂ n) (RingHom.id ℂ)).IsCInf ∧ (proj ℂ n).inter (fun _ => projHyp ℂ n) = 1 :=
  ⟨_, (proj ℂ n).presents_hyp (proj_gen_mem ℂ n 0), isCInf_fs (proj ℂ n) (RingHom.id ℂ), inter_projHyp ℂ n⟩

theorem integrable {L : LB Y.X} (φ : Weight Y.str (RingHom.id ℂ) L) (h : φ.IsCInf) :
    φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) := by
  have : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  let R := AnRead.all Y.str (RingHom.id ℂ) Y.dim
  have hs : φ.IsSmooth R := (Weight.isCInf_iff_isSmooth R).1 h
  have hm := ReciprocityTheory.AnForm.M.mIntegrableCont R.finAtlas (fun _ => φ.locPot)
    (fun _ => Weight.isPotential_locPot hs) (fun _ => 1) continuous_const
  exact ((Weight.chernInt_eq_mInt R h measurable_const).1).2 hm

theorem mass_fs_nonneg : 0 ≤ (fs Y (RingHom.id ℂ)).chernInt Y.dim Set.univ (fun _ => 1) := by
  have hneg : (fs Y (RingHom.id ℂ)).chernPart Y.dim (-1) = 0 :=
    Weight.chernPart_neg_eq_zero (isCInf_fs Y (RingHom.id ℂ)) (Weight.semiPosReg_fsBasis _ _ _ _ _)
  unfold Weight.chernInt
  rw [hneg]
  rw [MeasureTheory.Measure.restrict_zero, MeasureTheory.integral_zero_measure, sub_zero]
  exact MeasureTheory.integral_nonneg fun _ => zero_le_one

theorem point (Δ : (proj ℂ 0).Dv) (L : LB (proj ℂ 0).X) (φ : Weight (proj ℂ 0).str (RingHom.id ℂ) L)
    (h : φ.IsCInf) : φ.chernInt 0 Set.univ (fun _ => 1) = ((proj ℂ 0).inter (fun _ => Δ) : ℝ) :=
  (chernDegree_point (RingHom.id ℂ) Δ L φ h).2

theorem mass_proj (H : ChernDegreeComplex) (n : ℕ) :
    (fs (proj ℂ n) (RingHom.id ℂ)).chernInt n Set.univ (fun _ => 1) = 1 := by
  obtain ⟨r, hr, hfs, hint⟩ := hyp_proj n
  have key := (H (proj ℂ n) (projHyp ℂ n) (proj ℂ n).O1 r hr _ hfs).2
  rw [hint, proj_dim] at key
  exact_mod_cast key

theorem mass_indep (H : ChernDegreeComplex) {L : LB Y.X} (φ ψ : Weight Y.str (RingHom.id ℂ) L)
    (h : φ.IsCInf) (h' : ψ.IsCInf) :
    φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  obtain ⟨Δ, r, hp⟩ := exists_presents Y φ
  exact (H Y Δ L r hp φ h).2.trans (H Y Δ L r hp ψ h').2.symm

end GlobalTheory.Published.ChernDegreeComplexModel
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWAniso

section Coord

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Invertible (2 : R)] {n m : ℕ}

omit [Invertible (2 : R)] in

theorem symp_dblGram (c : A →ₐ[R] A) (ξ : A) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin m) (Fin m) A)
    (u v : Matrix (Fin (n + n)) (Fin m) A) :
    symp c ξ (dblGram finSumFinEquiv J) J' u v =
      symp c ξ J J' (fun i => u (finSumFinEquiv (.inl i))) (fun i => v (finSumFinEquiv (.inl i))) -
        symp c ξ J J' (fun i => u (finSumFinEquiv (.inr i))) (fun i => v (finSumFinEquiv (.inr i))) := by
  simp only [symp, hTens, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, mul_add, map_add,
    map_neg]

theorem exists_dblCoord (c : A →ₐ[R] A) (ξ : A) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin m) (Fin m) A)
    (d : Darboux (symp c ξ J J') (Fin n × Fin m)) :
    ∃ co : Darboux (symp c ξ (dblGram finSumFinEquiv J) J') (Fin (n + n) × Fin m), ∀ u i j,
      let a := d.e fun i => u (finSumFinEquiv (.inl i))
      let b := d.e fun i => u (finSumFinEquiv (.inr i))
      (co.e u).1 (finSumFinEquiv (.inl i), j) = a.1 (i, j) - b.1 (i, j) ∧
      (co.e u).1 (finSumFinEquiv (.inr i), j) = a.2 (i, j) - b.2 (i, j) ∧
      (co.e u).2 (finSumFinEquiv (.inl i), j) = ⅟(2 : R) * (a.2 (i, j) + b.2 (i, j)) ∧
      (co.e u).2 (finSumFinEquiv (.inr i), j) = -(⅟(2 : R) * (a.1 (i, j) + b.1 (i, j))) := by
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  let S : Matrix (Fin (n + n)) (Fin m) A ≃ₗ[R] Matrix (Fin n) (Fin m) A × Matrix (Fin n) (Fin m) A :=
    (LinearEquiv.funCongrLeft R (Fin m → A) finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ R _)
  let G : (Fin (n + n) × Fin m → R) ≃ₗ[R] (Fin n × Fin m → R) × (Fin n × Fin m → R) :=
    (LinearEquiv.funCongrLeft R R
      ((Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _)))).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ R _)
  let T : (((Fin n × Fin m → R) × (Fin n × Fin m → R)) × ((Fin n × Fin m → R) × (Fin n × Fin m → R))) ≃ₗ[R]
      (((Fin n × Fin m → R) × (Fin n × Fin m → R)) × ((Fin n × Fin m → R) × (Fin n × Fin m → R))) :=
    { toFun := fun p => ((p.1.1 - p.2.1, p.1.2 - p.2.2), (⅟(2 : R) • (p.1.2 + p.2.2), -(⅟(2 : R) • (p.1.1 + p.2.1))))
      invFun := fun q => ((⅟(2 : R) • q.1.1 - q.2.2, ⅟(2 : R) • q.1.2 + q.2.1),
        (-(⅟(2 : R) • q.1.1) - q.2.2, -(⅟(2 : R) • q.1.2) + q.2.1))
      map_add' := fun p q => by
        ext <;> simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
          smul_eq_mul] <;> ring
      map_smul' := fun r p => by
        ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
          smul_eq_mul, RingHom.id_apply] <;> ring
      left_inv := fun p => by
        ext k <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        · linear_combination p.1.1 k * h2
        · linear_combination p.1.2 k * h2
        · linear_combination p.2.1 k * h2
        · linear_combination p.2.2 k * h2
      right_inv := fun q => by
        ext k <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        · linear_combination q.1.1 k * h2
        · linear_combination q.1.2 k * h2
        · linear_combination q.2.1 k * h2
        · linear_combination q.2.2 k * h2 }
  have hG : ∀ x y : Fin (n + n) × Fin m → R, x ⬝ᵥ y = (G x).1 ⬝ᵥ (G y).1 + (G x).2 ⬝ᵥ (G y).2 := fun x y => by
    simp only [dotProduct, Fintype.sum_prod_type, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    rfl
  have hl : ∀ p i j, G.symm p (finSumFinEquiv (.inl i), j) = p.1 (i, j) := fun p i j =>
    congrArg (fun z => z.1 (i, j)) (G.apply_symm_apply p)
  have hr : ∀ p i j, G.symm p (finSumFinEquiv (.inr i), j) = p.2 (i, j) := fun p i j =>
    congrArg (fun z => z.2 (i, j)) (G.apply_symm_apply p)
  refine ⟨⟨S.trans ((d.e.prodCongr d.e).trans (T.trans (G.symm.prodCongr G.symm))), fun u v => ?_⟩,
    fun u i j => ⟨hl _ i j, hr _ i j, hl _ i j, hr _ i j⟩⟩
  rw [(symp_dblGram c ξ J J' u v).trans (congrArg₂ (· - ·) (d.form _ _) (d.form _ _)), hG, hG]
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.apply_symm_apply]
  change (d.e (S u).1).1 ⬝ᵥ (d.e (S v).1).2 - (d.e (S v).1).1 ⬝ᵥ (d.e (S u).1).2 -
    ((d.e (S u).2).1 ⬝ᵥ (d.e (S v).2).2 - (d.e (S v).2).1 ⬝ᵥ (d.e (S u).2).2) = _
  generalize d.e (S u).1 = a, d.e (S u).2 = b, d.e (S v).1 = a', d.e (S v).2 = b'
  simp only [T, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sub_dotProduct, dotProduct_smul, dotProduct_add,
    dotProduct_neg, smul_eq_mul, dotProduct_comm a.2, dotProduct_comm b.2, dotProduct_comm a'.2, dotProduct_comm b'.2]
  linear_combination (-(a.1 ⬝ᵥ a'.2) + a'.1 ⬝ᵥ a.2 + b.1 ⬝ᵥ b'.2 - b'.1 ⬝ᵥ b.2) * h2

end Coord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n m : ℕ}

omit [NumberField E] in

theorem exists_rational_dblCoord {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin m) (Fin m) E}
    {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (hJ : J₂ = dblGram finSumFinEquiv J)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin m))
    (hd : ∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin m),
      (∀ x : Matrix (Fin (n + n)) (Fin m) E, ∃ y z : Fin (n + n) × Fin m → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ u, (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) ∧
      ∀ u, (∀ j, uᵀ j ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0 := by
  have e : incM F J₂ = dblGram finSumFinEquiv (incM F J) := by
    rw [hJ, incM, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]; rfl
  rw [e]
  obtain ⟨co, h⟩ := exists_dblCoord (cA σ) (-1) (incM F J) (incM F J') d
  refine ⟨co, fun x => ?_, fun u hu => funext fun p => ?_, fun u hu => funext fun p => ?_⟩
  · obtain ⟨y, z, h1⟩ := hd fun i => x (finSumFinEquiv (.inl i))
    obtain ⟨y', z', h2⟩ := hd fun i => x (finSumFinEquiv (.inr i))
    have h3 : ⅟(2 : AF F) = algebraMap F (AF F) 2⁻¹ := invOf_eq_right_inv (by
      rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one])
    refine ⟨fun p => pairVec finSumFinEquiv (fun i => y (i, p.2) - y' (i, p.2)) (fun i => z (i, p.2) - z' (i, p.2)) p.1,
      fun p => pairVec finSumFinEquiv (fun i => 2⁻¹ * (z (i, p.2) + z' (i, p.2)))
        (fun i => -(2⁻¹ * (y (i, p.2) + y' (i, p.2)))) p.1, ?_⟩
    have h4 := h (incM F x)
    change d.e (fun i => incM F x (finSumFinEquiv (.inl i))) = _ at h1
    change d.e (fun i => incM F x (finSumFinEquiv (.inr i))) = _ at h2
    simp only [h1, h2, h3] at h4
    refine Prod.ext (funext fun ⟨k, j⟩ => ?_) (funext fun ⟨k, j⟩ => ?_) <;>
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k <;>
      simp only [h4 i j, pairVec_inl, pairVec_inr, map_sub, map_add, map_mul, map_neg]
  · have h1 : (fun i => u (finSumFinEquiv (.inr i))) = fun i => u (finSumFinEquiv (.inl i)) :=
      funext fun i => funext fun j => (congrFun (hu j) i).symm
    obtain ⟨k, j⟩ := p
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
    · rw [(h u i j).1, h1, sub_self]; rfl
    · rw [(h u i j).2.1, h1, sub_self]; rfl
  · have h1 : d.e (fun i => u (finSumFinEquiv (.inl i))) = -d.e fun i => u (finSumFinEquiv (.inr i)) := by
      exact (congrArg d.e (funext fun i => funext fun j => congrFun (hu j) i)).trans (map_neg d.e _)
    obtain ⟨k, j⟩ := p
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective k
    · rw [(h u i j).2.2.1, h1]; simp
    · rw [(h u i j).2.2.2, h1]; simp

end GlobalTheory.SWAniso

namespace GlobalTheory.Published

def SiegelWeilAnisotropicCM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ B : Base F E, IsCharAF F B.ψ →
  ∀ (n m : ℕ), 1 ≤ n → n < m →
  ∀ X : Spc F E n, IsHermND σ X.J → X.L.IsLattice E →
    (∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)) → (∀ w, IsCartan (X.J.map (B.emb w).1) (X.θ w)) →
  ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J → X₂.L = sumLat finSumFinEquiv X.L X.L →
    (∀ w, X₂.θ w = blkMat finSumFinEquiv (X.θ w) (-X.θ w)) →
  ∀ W : Spc F E m, (∀ i j, σ (W.J j i) = -W.J i j) → (∀ x, form σ W.J x x = 0 → x = 0) →
  ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X₂.J) (incM F W.J)) (Fin (n + n) × Fin m),
    (∀ x : Matrix (Fin (n + n)) (Fin m) E, ∃ y z : Fin (n + n) × Fin m → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ u, (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
    (∀ u, (∀ j, uᵀ j ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : Rep σ X₂ W, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X₂.J) (incM F W.J) co 1 χ om →
  ∀ K : Subgroup (UA σ X₂.J), IsStab B K →
    IwasawaOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K →
  ∀ Φ ∈ schA F (Fin (n + n) × Fin m), FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (k, 1) Φ}) →
  ∀ (ν : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 ν →
    let P : Subgroup (UA σ X₂.J) := siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype
    let s₀ : ℂ := ((m : ℂ) - (n : ℂ)) / 2
    let f : ℂ → UA σ X₂.J → ℂ :=
      flatOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K (fun g => om (g, 1) Φ 0) s₀
    (∀ g, IntegrableOn (fun h => theta om Φ g h) 𝓕 ν) ∧
    (∀ s : ℂ, (n : ℝ) / 2 < s.re →
      AutomorphicL2Unitary.LeftInv (P ⊓ ratU σ X₂.J) (f s) ∧ ∀ g, Eis.CosetConv P (ratU σ X₂.J) (f s) g) ∧
    ∀ g, Cont.HolValueAt (fun s => Eis.cosetSum P (ratU σ X₂.J) (f s) g) s₀ (⨍ h in 𝓕, theta om Φ g h ∂ν)

end GlobalTheory.Published

end
end

