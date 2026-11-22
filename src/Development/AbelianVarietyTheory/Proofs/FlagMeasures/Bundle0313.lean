import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularColumnOpsPreserveHaarTuplesHermitia
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.UnitriTuple

theorem exists_compactOpen (k G : Type*) [NormedField k] [IsUltrametricDist k] [ProperSpace k]
    [AddCommGroup G] [Module k G] [Module.Finite k G] [TopologicalSpace G] [IsModuleTopology k G] :
    ∃ K : AddSubgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) := by
  have : IsTopologicalAddGroup G := IsModuleTopology.topologicalAddGroup k G
  let e₀ : G ≃ₗ[k] (Fin (Module.finrank k G) → k) := (Module.finBasis k G).equivFun
  let e : G ≃ₜ (Fin (Module.finrank k G) → k) :=
    { e₀.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap }
  let K₀ := IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank k G) → k) one_pos
  exact ⟨K₀.toAddSubgroup.comap e₀.toLinearMap.toAddMonoidHom, K₀.isOpen.preimage e.continuous,
    e.isCompact_preimage.2 (isCompact_closedBall (0 : Fin (Module.finrank k G) → k) 1)⟩

theorem map_add_nilpotent_of_compactOpen {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (K : AddSubgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (N : Module.End ℤ G) (hNc : Continuous N) (hN : IsNilpotent N) :
    μ.map (fun x => x + N x) = μ := by
  have hpow : ∀ (f : Module.End ℤ G), Continuous f → ∀ j : ℕ, Continuous (f ^ j : Module.End ℤ G) :=
    fun f hf j => by rw [Module.End.coe_pow]; exact hf.iterate j
  have hnegc : Continuous (-N : Module.End ℤ G) := by
    have : ⇑(-N : Module.End ℤ G) = fun x => -(N x) := rfl
    rw [this]; exact hNc.neg
  obtain ⟨m, hm⟩ := hN
  let B : AddSubgroup G := ⨅ j : ℕ, K.comap (N ^ j).toAddMonoidHom
  have hB : ∀ x, x ∈ B ↔ ∀ j : ℕ, (N ^ j) x ∈ K := fun x => by
    simp [B, AddSubgroup.mem_iInf]
  have hBo : IsOpen (B : Set G) := by
    have : (B : Set G) = ⋂ j ∈ Finset.range m, (N ^ j : Module.End ℤ G) ⁻¹' (K : Set G) := by
      ext x
      simp only [SetLike.mem_coe, hB, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
      refine ⟨fun h j _ => h j, fun h j => ?_⟩
      by_cases hj : j < m
      · exact h j hj
      · rw [pow_eq_zero_of_le (not_lt.1 hj) hm]; exact K.zero_mem
    rw [this]
    exact isOpen_biInter_finset fun j _ => hKo.preimage (hpow N hNc j)
  have hBc : IsCompact (B : Set G) :=
    hKc.of_isClosed_subset (B.isClosed_of_isOpen hBo) fun x hx => by
      simpa using (hB x).1 hx 0
  have hNB : ∀ x ∈ B, N x ∈ B := fun x hx => (hB _).2 fun j => by
    rw [← Module.End.mul_apply, ← pow_succ]; exact (hB x).1 hx _
  have hNp : ∀ (j : ℕ), ∀ x ∈ B, ((-N) ^ j) x ∈ B := fun j => by
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      exact B.neg_mem (hNB _ (ih x hx))
  have hm' : (-N) ^ m = 0 := by rw [neg_pow, hm, mul_zero]
  have h1 : (∑ j ∈ Finset.range m, (-N) ^ j) * (1 + N) = 1 := by
    have := geom_sum_mul_neg (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  have h2 : (1 + N) * (∑ j ∈ Finset.range m, (-N) ^ j) = 1 := by
    have := mul_neg_geom_sum (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  have hinv : Continuous (∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G) := by
    have : ⇑(∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G) =
        fun x => ∑ j ∈ Finset.range m, ((-N) ^ j : Module.End ℤ G) x :=
      funext fun x => LinearMap.sum_apply _ _ _
    rw [this]
    exact continuous_finset_sum _ fun j _ => hpow _ hnegc j
  let L : G ≃ₜ+ G :=
    { toFun := fun x => x + N x
      invFun := (∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G)
      left_inv := fun x => LinearMap.congr_fun h1 x
      right_inv := fun x => LinearMap.congr_fun h2 x
      map_add' := fun x y => by rw [map_add]; abel
      continuous_toFun := continuous_id.add hNc
      continuous_invFun := hinv }
  have hLB : L ⁻¹' (B : Set G) = B := by
    ext x
    refine ⟨fun hx => ?_, fun hx => B.add_mem hx (hNB x hx)⟩
    have : x = (∑ j ∈ Finset.range m, (-N) ^ j : Module.End ℤ G) (L x) := (L.left_inv x).symm
    rw [this, LinearMap.sum_apply]
    exact B.sum_mem fun j _ => hNp j _ hx
  change μ.map L = μ
  have : (μ.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have h3 := Measure.isAddLeftInvariant_eq_smul (μ.map L) μ
  have h4 : μ.map L B = μ B := by
    rw [Measure.map_apply (show Continuous L from L.continuous).measurable hBo.measurableSet, hLB]
  have h5 : μ B ≠ 0 := (hBo.measure_pos μ ⟨0, B.zero_mem⟩).ne'
  have h6 : μ B ≠ ⊤ := hBc.measure_lt_top.ne
  have h7 : Measure.addHaarScalarFactor (μ.map L) μ = 1 := by
    rw [h3, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h4
    have := (ENNReal.mul_left_inj h5 h6).1 (h4.trans (one_mul _).symm)
    exact_mod_cast this
  rw [h3, h7, one_smul]

theorem sub_one_pow {R : Type*} [CommRing R] {a : ℕ} (u : Matrix (Fin a) (Fin a) R)
    (h1 : ∀ i, u i i = 1) (h0 : ∀ i j, j < i → u i j = 0) : (u - 1) ^ a = 0 := by
  refine GlobalTheory.UnitriHaar.nilpotent_of_strict _ fun i j h => ?_
  rcases (not_lt.1 h).eq_or_lt with rfl | h
  · simp [h1]
  · simp [h0 i j h, Matrix.one_apply_ne h.ne']

def colOp {R : Type*} [CommRing R] {a n : ℕ} (w : Matrix (Fin a) (Fin a) R) :
    Module.End R (Fin a → Fin n → R) where
  toFun X b := ∑ c, w c b • X c
  map_add' X Y := by funext b; simp [Finset.sum_add_distrib, smul_add]
  map_smul' r X := by funext b; simp [Finset.smul_sum, smul_comm r]

theorem colOp_pow {R : Type*} [CommRing R] {a n : ℕ} (w : Matrix (Fin a) (Fin a) R) (j : ℕ)
    (X : Fin a → Fin n → R) (b : Fin a) :
    ((colOp (n := n) w ^ j) X) b = ∑ c, (w ^ j) c b • X c := by
  induction j generalizing b with
  | zero => simp [Matrix.one_apply]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ]
    change ∑ c, w c b • (((colOp (n := n) w ^ j) X) c) = _
    simp only [ih, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by rw [mul_comm]

open GlobalTheory.GaugeEx in

theorem unitri_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ.map (fun X b => ∑ c, u c b • X c) = μ) ∧ ∀ ν : Measure (HermR (Fv F v) σ a), ν.IsAddHaarMeasure → ∀ φ : HermR (Fv F v) σ a → HermR (Fv F v) σ a, (∀ S, (φ S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u) → ν.map φ = ν := by
  intro F E _ _ _ _ _ σ _ n J _ v a u h1 h0
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨fun μ hμ => ?_, fun ν hν φ hφ => ?_⟩
  · let N := colOp (n := n) (u - 1)
    have hN : IsNilpotent N := ⟨a, LinearMap.ext fun X => funext fun b => by
      rw [colOp_pow, sub_one_pow u h1 h0]; simp⟩
    have hN' : IsNilpotent (N.restrictScalars (Fv F v) : Module.End (Fv F v) _) := by
      obtain ⟨m, hm⟩ := hN
      refine ⟨m, LinearMap.ext fun x => ?_⟩
      have := LinearMap.congr_fun hm x
      rw [Module.End.pow_apply] at this ⊢
      exact this
    have h2 := GlobalTheory.UnitriHaar.map_add_nilpotent μ _ hN'
    have hx : (fun (X : Fin a → Fin n → Fv F v ⊗[F] E) b => ∑ c, u c b • X c) =
        fun X => X + N.restrictScalars (Fv F v) X := by
      funext X b
      change _ = X b + ∑ c, (u - 1) c b • X c
      simp [sub_smul, Finset.sum_sub_distrib, Matrix.one_apply]
    rw [hx]; exact h2
  · have hTR : IsTopologicalRing (Fv F v) := inferInstance
    let Ev := Fv F v ⊗[F] E
    have : LocallyCompactSpace (Matrix (Fin a) (Fin a) Ev) :=
      inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Ev))
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) Ev) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ev))
    have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
    have hc : IsClosed (HermR (Fv F v) σ a : Set (Matrix (Fin a) (Fin a) Ev)) := by
      have : (HermR (Fv F v) σ a : Set (Matrix (Fin a) (Fin a) Ev)) =
          ⋂ i, ⋂ j, {S | sigR (Fv F v) σ (S j i) = S i j} := by
        ext S
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rfl
      rw [this]
      refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
      · exact (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Fv F v) σ).comp (continuous_id.matrix_elem j i)
      · exact continuous_id.matrix_elem i j
    have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
      hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : SecondCountableTopology (HermR (Fv F v) σ a) :=
      hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
    obtain ⟨K₀, hK₀o, hK₀c⟩ := exists_compactOpen (Fv F v) (Fin a → Fin a → Ev)
    let K : AddSubgroup (HermR (Fv F v) σ a) :=
      AddSubgroup.comap (HermR (Fv F v) σ a).subtype K₀
    have hKo : IsOpen (K : Set (HermR (Fv F v) σ a)) := hK₀o.preimage continuous_subtype_val
    have hKc : IsCompact (K : Set (HermR (Fv F v) σ a)) :=
      hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK₀c
    set A : Matrix (Fin a) (Fin a) Ev := (u.map (sigR (Fv F v) σ)).transpose with hA
    have hS1 : ∀ i, (u.map (sigR (Fv F v) σ)) i i = 1 := fun i => by simp [h1]
    have hS0 : ∀ i j, j < i → (u.map (sigR (Fv F v) σ)) i j = 0 := fun i j h => by simp [h0 i j h]
    have hAn : (A - 1) ^ a = 0 := by
      have := sub_one_pow _ hS1 hS0
      have h3 : A - 1 = (u.map (sigR (Fv F v) σ) - 1).transpose := by
        rw [Matrix.transpose_sub, Matrix.transpose_one]
      rw [h3, ← Matrix.transpose_pow, this, Matrix.transpose_zero]
    have hun : (u - 1) ^ a = 0 := sub_one_pow u h1 h0
    let La : Module.End Ev (Matrix (Fin a) (Fin a) Ev) := LinearMap.mulLeft Ev A
    let Ru : Module.End Ev (Matrix (Fin a) (Fin a) Ev) := LinearMap.mulRight Ev u
    have hLR : Commute La Ru := LinearMap.commute_mulLeft_right A u
    have hLn : IsNilpotent (La - 1) := by
      have : La - 1 = LinearMap.mulLeft Ev (A - 1) := by
        ext1 S; simp [La, sub_mul]
      rw [this]
      exact ⟨a, by rw [LinearMap.pow_mulLeft, hAn, LinearMap.mulLeft_zero_eq_zero]⟩
    have hRn : IsNilpotent (Ru - 1) := by
      have : Ru - 1 = LinearMap.mulRight Ev (u - 1) := by
        ext1 S; simp [Ru, mul_sub]
      rw [this]
      exact ⟨a, by rw [LinearMap.pow_mulRight, hun, LinearMap.mulRight_zero_eq_zero]⟩
    have hTn : IsNilpotent (La * Ru - 1) := by
      have : La * Ru - 1 = (La - 1) * Ru + (Ru - 1) := by noncomm_ring
      rw [this]
      have c1 : Commute (La - 1) Ru := hLR.sub_left (Commute.one_left _)
      have c2 : Commute ((La - 1) * Ru) (Ru - 1) :=
        Commute.mul_left (c1.sub_right (Commute.one_right _))
          ((Commute.refl Ru).sub_right (Commute.one_right _))
      exact c2.isNilpotent_add (c1.isNilpotent_mul_right hLn) hRn
    have hadd : ∀ S S', φ (S + S') = φ S + φ S' := fun S S' => Subtype.ext (by
      rw [AddSubgroup.coe_add, hφ, hφ, hφ, AddSubgroup.coe_add, mul_add, add_mul])
    let N₀ : HermR (Fv F v) σ a →+ HermR (Fv F v) σ a :=
      AddMonoidHom.mk' (fun S => φ S - S) fun S S' => by rw [hadd]; abel
    let N : Module.End ℤ (HermR (Fv F v) σ a) := N₀.toIntLinearMap
    have hNa : ∀ S, ((N S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) =
        (La * Ru - 1) (S : Matrix (Fin a) (Fin a) Ev) := fun S => by
      change ((φ S - S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) = _
      rw [AddSubgroup.coe_sub, hφ]
      simp [La, Ru, mul_assoc]
    have hNp : ∀ (j : ℕ) S, (((N ^ j) S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) =
        ((La * Ru - 1) ^ j) (S : Matrix (Fin a) (Fin a) Ev) := fun j => by
      induction j with
      | zero => intro S; simp
      | succ j ih =>
        intro S
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hNa, ih]
    have hN : IsNilpotent N := by
      obtain ⟨m, hm⟩ := hTn
      refine ⟨m, LinearMap.ext fun S => Subtype.ext ?_⟩
      rw [hNp, hm]; rfl
    have hNc : Continuous N := by
      refine continuous_induced_rng.2 ?_
      have : (Subtype.val ∘ ⇑N) = fun S : HermR (Fv F v) σ a =>
          A * (S : Matrix (Fin a) (Fin a) Ev) * u - (S : Matrix (Fin a) (Fin a) Ev) :=
        funext fun S => by
          change ((N S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) Ev) = _
          rw [hNa]; simp [La, Ru, mul_assoc]
      rw [this]
      exact ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).sub
        continuous_subtype_val
    have h2 := map_add_nilpotent_of_compactOpen ν K hKo hKc N hNc hN
    have hx : φ = fun S => S + N S := funext fun S => by
      change φ S = S + (φ S - S); abel
    rw [hx]; exact h2

end GlobalTheory.UnitriTuple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExistsHolds
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St.WittT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Witt

variable {D : D7}

abbrev Ix (D : D7) : Type := Fin D.R.rS ⊕ (Fin D.R.rS ⊕ Unit)

def mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) : Ix D → (VS D).V
  | Sum.inl a => e a
  | Sum.inr (Sum.inl a) => f a
  | Sum.inr (Sum.inr _) => z

def gstd (T : D.host.E) : Ix D → Ix D → D.host.E
  | Sum.inl a, Sum.inr (Sum.inl b) => if a = b then 1 else 0
  | Sum.inr (Sum.inl a), Sum.inl b => if a = b then 1 else 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => -T
  | _, _ => 0

def swp : Ix D → Ix D
  | Sum.inl a => Sum.inr (Sum.inl a)
  | Sum.inr (Sum.inl a) => Sum.inl a
  | Sum.inr (Sum.inr t) => Sum.inr (Sum.inr t)

def cstd (T : D.host.E) : Ix D → D.host.E
  | Sum.inr (Sum.inr _) => -T
  | _ => 1

theorem gram_mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) (T : D.host.E)
    (hee : ∀ a b, (VS D).hT (e a) (e b) = 0) (hff : ∀ a b, (VS D).hT (f a) (f b) = 0)
    (hef : ∀ a b, (VS D).hT (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, (VS D).hT (e a) z = 0) (hfz : ∀ a, (VS D).hT (f a) z = 0) (hzz : (VS D).hT z z = -T) :
    ∀ i j, (VS D).hT (mkFr e f z i) (mkFr e f z j) = gstd T i j := by
  rintro (a | a | ⟨⟩) (b | b | ⟨⟩)
  · exact hee a b
  · exact hef a b
  · exact hez a
  · show (VS D).hT (f a) (e b) = if a = b then 1 else 0
    rw [← (VS D).herm.eq (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · exact hff a b
  · exact hfz a
  · show (VS D).hT z (e b) = 0
    rw [← (VS D).herm.eq (e b) z, hez b, map_zero]
  · show (VS D).hT z (f b) = 0
    rw [← (VS D).herm.eq (f b) z, hfz b, map_zero]
  · exact hzz

theorem gstd_swp (T : D.host.E) (i j : Ix D) : gstd T (swp j) i = if i = j then cstd T j else 0 := by
  rcases i with a | a | ⟨⟩ <;> rcases j with b | b | ⟨⟩ <;>
    simp [gstd, swp, cstd, eq_comm]

theorem indep_of_dual {ι : Type} [Fintype ι] [DecidableEq ι] (v d : ι → (VS D).V) (c : ι → D.host.E)
    (hc : ∀ j, c j ≠ 0) (hd : ∀ i j, (VS D).hT (d j) (v i) = if i = j then c j else 0) :
    LinearIndependent D.host.E v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg ((VS D).hT (d j)) hg
  simp only [map_sum, map_smul, map_zero, hd, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  exact (mul_eq_zero.1 h).resolve_right (hc j)

theorem indep_mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) (T : D.host.E) (hT : T ≠ 0)
    (hG : ∀ i j, (VS D).hT (mkFr e f z i) (mkFr e f z j) = gstd T i j) :
    LinearIndependent D.host.E (mkFr e f z) := by
  refine indep_of_dual (mkFr e f z) (fun j => mkFr e f z (swp j)) (cstd T) ?_ ?_
  · rintro (a | a | ⟨⟩) <;> simp [cstd, hT]
  · intro i j
    rw [hG, gstd_swp]

theorem witt_family {ι : Type} [Fintype ι] [DecidableEq ι] (v w : ι → (VS D).V)
    (hv : LinearIndependent D.host.E v) (hw : LinearIndependent D.host.E w)
    (hG : ∀ i j, (VS D).hT (v i) (v j) = (VS D).hT (w i) (w j)) :
    ∃ g : (VS D).V ≃ₗ[D.host.E] (VS D).V, (∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y) ∧ ∀ i, g (v i) = w i := by
  set U := Submodule.span D.host.E (Set.range v) with hU
  let b : Module.Basis ι D.host.E U := Module.Basis.span hv
  let f : U →ₗ[D.host.E] (VS D).V :=
    Finsupp.linearCombination D.host.E w ∘ₗ (b.repr : U →ₗ[D.host.E] (ι →₀ D.host.E))
  have hfb : ∀ i, f (b i) = w i := by
    intro i
    simp [f, Module.Basis.repr_self, Finsupp.linearCombination_single]
  have hbv : ∀ i, ((b i : U) : (VS D).V) = v i := by
    intro i
    exact congrArg Subtype.val (Module.Basis.span_apply hv i)
  have hinj : Function.Injective f := by
    have h2 : Function.Injective (Finsupp.linearCombination D.host.E w) := hw
    exact h2.comp b.repr.injective
  have hB : ((VS D).hT.comp f).compl₂ f = ((VS D).hT.comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hfb, Submodule.subtype_apply, hbv]
    exact (hG i j).symm
  have hiso : ∀ x y : U, (VS D).hT (f x) (f y) = (VS D).hT x y := by
    intro x y
    have h := congrArg (fun B => B x y) hB
    simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply] using h
  obtain ⟨g, hg, hgf⟩ := _root_.witt_extension_theorem D.host.E (VS D).V (VS D).hT
    (fun x y => (VS D).herm.eq x y) (fun x hx => (VS D).nondeg.1 x hx) U f hinj hiso
  refine ⟨g, hg, fun i => ?_⟩
  have h := hgf (b i)
  rw [hbv, hfb] at h
  exact h

theorem hypF_zmOf (u : D.what₂.Word) (a : Fin D.R.rS) : (VS D).hT (D.sp.hypF a) (D.zmOf u) = 0 := by
  unfold D7.zmOf
  rw [map_smul, ← (VS D).herm.eq D.sp.zm (D.sp.hypF a), (D.sp.hyp_orthz a).2, map_zero, smul_zero]

theorem wittExists_holds (D : D7) : WittExists D := by
  intro X u
  have hT : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hGX := gram_mkFr X.eX X.fY (X.zu u) (((D.mem u).A.T : ℕ) : D.host.E) X.ee X.ff X.ef
    (fun a => (X.zu_orth u a).1) (fun a => (X.zu_orth u a).2) (X.zu_norm u)
  have hGR := gram_mkFr D.sp.hypE D.sp.hypF (D.zmOf u) (((D.mem u).A.T : ℕ) : D.host.E) D.sp.hyp_ee D.sp.hyp_ff
    D.sp.hyp_ef (fun a => (Formalism.MainNotions.S.Inh.tie_flag0 D u).z_orth a) (hypF_zmOf u) (Formalism.MainNotions.S.Inh.tie_zmOf_norm D u)
  obtain ⟨g, hg, hgi⟩ := witt_family (mkFr X.eX X.fY (X.zu u)) (mkFr D.sp.hypE D.sp.hypF (D.zmOf u))
    (indep_mkFr _ _ _ _ hT hGX) (indep_mkFr _ _ _ _ hT hGR) (fun i j => by rw [hGX, hGR])
  exact ⟨g, hg, fun a => hgi (Sum.inl a), fun a => hgi (Sum.inr (Sum.inl a)), hgi (Sum.inr (Sum.inr ()))⟩

end Witt

theorem wittExists : ∀ D : D7, WittExists D := wittExists_holds

end GlobalTheory.St.WittT

end
end

