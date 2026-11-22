import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCoordinateActionUnitaryPreservesHermitianFor
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.RealWeilF

section Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_tmul_one_F {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hσ : ∀ x, τ (σ x) = star (τ x))
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmbF τ θ) (a : Ainf F) :
    starRingEnd ℂ (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap F) a
    (isClosed_eq (Complex.continuous_conj.comp hθ.2) hθ.2) fun f => ?_
  have e : (algebraMap F (Ainf F) f) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] (algebraMap F E f) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [e, hθ.1, starRingEnd_apply, ← hσ, AlgHom.commutes]

theorem comp_cAF {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hσ : ∀ x, τ (σ x) = star (τ x))
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmbF τ θ) (z : AEF F E) :
    θ (infPartF F E (cAF σ z)) = starRingEnd ℂ (θ (infPartF F E z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a x =>
    have e : ∀ y : E, fstA F a ⊗ₜ[F] y = (fstA F a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] y) := by
      intro y; simp
    have e2 : infPartF F E (cAF σ (a ⊗ₜ[F] x)) = fstA F a ⊗ₜ[F] (σ x) := rfl
    have e3 : infPartF F E (a ⊗ₜ[F] x) = fstA F a ⊗ₜ[F] x := rfl
    rw [e2, e3, e (σ x), e x, map_mul, map_mul, map_mul, conj_tmul_one_F hσ hθ, hθ.1, hθ.1, hσ]
    rfl

theorem compAtF_unitary {σ : E →ₐ[F] E} {tau : InfinitePlace F → (E →+* ℂ)}
    {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} (hσ : ∀ w x, tau w (σ x) = star (tau w x))
    (hθ : IsInfFamF tau θ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (w : InfinitePlace F) :
    (compAtF θ w (mtF σ J g))ᴴ * J.map (tau w) * compAtF θ w (mtF σ J g) = J.map (tau w) := by
  have hg : ((mtF σ J g).map (cAF σ))ᵀ * JR (AF F) J * mtF σ J g = JR (AF F) J := g.2
  have hJ : (JR (AF F) J).map ((θ w).comp (infPartF F E)) = J.map (tau w) := by
    ext i j
    have : infPartF F E (inclR (AF F) (J i j)) = (1 : Ainf F) ⊗ₜ[F] J i j := rfl
    show θ w (infPartF F E (inclR (AF F) (J i j))) = _
    rw [this]
    exact (hθ w).1 (J i j)
  rw [← hJ]
  exact GlobalTheory.FockCompare.RealAction.unitary_map (cAF σ) ((θ w).comp (infPartF F E)) (comp_cAF (hσ w) (hθ w)) _ _ hg

theorem compAtF_mul_inv (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (w : InfinitePlace F) :
    compAtF θ w (mtF σ J g) * compAtF θ w (mtF σ J g⁻¹) = 1 := by
  have h1 : mtF σ J 1 = 1 := by unfold mtF; rw [map_one]; rfl
  rw [compAtF, compAtF, ← Matrix.map_mul, ← GlobalTheory.WeilPartsF.mtF_mul, mul_inv_cancel, h1,
    Matrix.map_one _ (map_zero _) (map_one _)]

end Unitary

theorem mMF_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ p : GAF σ JS × GAF σ JT, (mMF σ JS JT θ p)ᴴ * HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) * mMF σ JS JT θ p = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι _ p
  obtain ⟨g, h⟩ := p
  have hσ : ∀ w x, (B.emb w).1 (σ x) = star ((B.emb w).1 x) := fun w x => hB.cm.2.2.2 _ x
  unfold HMF
  rw [mMF_apply, blk_conjTranspose, blk_mul, blk_mul]
  congr 1 <;> funext w
  · rw [Matrix.mul_smul, Matrix.smul_mul, compAtF_unitary hσ hθ]
  · have h1 := compAtF_unitary hσ hθ JS g w
    have h2 := compAtF_mul_inv θ JS g w
    conv_rhs => rw [← h1, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, inv_eq_right_inv h2]

end GlobalTheory.RealWeilF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOne
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.Hartogs

theorem regAt_of_forall_dvr : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
    ∀ (φ : X.functionField) (x : X),
      (∀ z : X, z ⤳ x → IsDiscreteValuationRing (X.presheaf.stalk z) → RegAt z φ) → RegAt x φ := by
  intro X _ _ hN f x hreg
  by_contra hf
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI := isIntegrallyClosed_sections_of_stalks hN hU
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  have key : ∀ y : U, RegAt (y : X) f ↔ ∃ s c : Γ(X, U), algebraMap _ X.functionField s * f =
      algebraMap _ X.functionField c ∧ s ∉ (hU.primeIdealOf y).asIdeal := fun y =>
    haveI := hU.isLocalization_stalk y
    GlobalTheory.NormalPole.mem_range_iff (B := X.presheaf.stalk (y : X)) (hU.primeIdealOf y).asIdeal f
  obtain ⟨p, hp, hpQ, h1, hpf⟩ := GlobalTheory.NormalPole.exists_height_one f (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    fun s c e => by_contra fun hs => hf ((key ⟨x, hx⟩).2 ⟨s, c, e, hs⟩)
  let P : PrimeSpectrum Γ(X, U) := ⟨p, hp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ x := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hpQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
  have hfz : ¬ RegAt (z : X) f := fun h => by
    obtain ⟨s, c, e, hs⟩ := (key z).1 h
    rw [hP] at hs
    exact hs (hpf s c e)
  clear_value z
  haveI := hU.isLocalization_stalk z
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    isDiscreteValuationRing_of_height_eq_one (hU.primeIdealOf z).asIdeal (by rw [hP]; exact h1) _
  exact hfz (hreg z hzx inferInstance)

end GlobalTheory.Hartogs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  show (∀ h : H, ρ (h : G) v = ((1 : H →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun H h hh => H ⟨h, hh⟩, fun H h => H h h.2⟩

theorem finite_out_support [TopologicalSpace G] [IsTopologicalGroup G] {K' : Subgroup G}
    (hK' : IsOpen (K' : Set G)) {f : G → ℂ} (hf : HasCompactSupport f) :
    {q : G ⧸ K' | f q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K') := QuotientGroup.discreteTopology hK'
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K') '' tsupport f) :=
    hf.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

theorem term_fin (ρ : Representation ℂ G V) (K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : {q : G ⧸ K' | f q.out ≠ 0}.Finite) :
    Function.HasFiniteSupport fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ A) :=
  h.subset (Function.support_smul_subset_left (fun q : G ⧸ K' => f q.out) fun q => ρ q.out ∘ₗ A)

theorem levOp_add (ρ : Representation ℂ G V) (K K' : Subgroup G) (f f' : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : {q : G ⧸ K' | f q.out ≠ 0}.Finite) (h' : {q : G ⧸ K' | f' q.out ≠ 0}.Finite) :
    levOp ρ K K' (f + f') A = levOp ρ K K' f A + levOp ρ K K' f' A := by
  unfold levOp
  rw [← smul_add, ← finsum_add_distrib (term_fin ρ K' f A h) (term_fin ρ K' f' A h')]
  congr 1
  exact finsum_congr fun q => by simp [add_smul]

theorem levOp_smul_fun (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (c : ℂ) :
    levOp ρ K K' (c • f) A = c • levOp ρ K K' f A := by
  unfold levOp
  rw [smul_comm c, smul_finsum c]
  congr 1
  exact finsum_congr fun q => by simp [mul_smul]

theorem levOp_smul_op (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (c : ℂ) :
    levOp ρ K K' f (c • A) = c • levOp ρ K K' f A := by
  unfold levOp
  rw [smul_comm c, smul_finsum c]
  congr 1
  exact finsum_congr fun q => by rw [LinearMap.comp_smul, smul_comm]

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem A_fixed (ρ : Representation ℂ G V) (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (K' : Subgroup G)
    (hK'θ : ∀ k ∈ K', θ k ∈ K') (A : V →ₗ[ℂ] V) (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) {v : V}
    (hv : v ∈ fixed ρ K') : A v ∈ fixed ρ K' := by
  rw [mem_fixed_iff] at hv ⊢
  intro k hk
  have := LinearMap.congr_fun (hA (θ k)) v
  simp only [LinearMap.comp_apply, hθ] at this
  rw [← this, hv _ (hK'θ k hk)]

theorem levOp_mapsTo (ρ : Representation ℂ G V) (K K' : Subgroup G) (A : V →ₗ[ℂ] V) (f : G → ℂ)
    (hfin : {q : G ⧸ K' | f q.out ≠ 0}.Finite)
    (hl : ∀ k ∈ K', ∀ x, f (k * x) = f x) (hr : ∀ k ∈ K', ∀ x, f (x * k) = f x)
    (hA : ∀ v ∈ fixed ρ K', A v ∈ fixed ρ K') :
    ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K' := by
  intro v hv
  have hw := hA v hv
  have hw' := (mem_fixed_iff ρ K' (A v)).1 hw
  let F : G ⧸ K' → V := fun q => f q.out • ρ q.out (A v)
  have hF : ∀ x : G, F (QuotientGroup.mk x) = f x • ρ x (A v) := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' x
    simp only [F, hh, hr _ h.2, map_mul, Module.End.mul_apply, hw' _ h.2]
  have hFfin : Function.HasFiniteSupport F :=
    hfin.subset (Function.support_smul_subset_left (fun q : G ⧸ K' => f q.out) fun q => ρ q.out (A v))
  have hL : levOp ρ K K' f A v = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q, F q := by
    unfold levOp
    rw [LinearMap.smul_apply, ← LinearMap.applyₗ_apply_apply (R := ℂ) v,
      map_finsum _ (term_fin ρ K' f A hfin)]
    rfl
  rw [hL, mem_fixed_iff]
  intro k hk
  rw [map_smul, map_finsum _ hFfin]
  congr 1
  have hk' : ∀ q, ρ k (F q) = F (k • q) := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [MulAction.Quotient.smul_mk, hF, smul_eq_mul, hl _ hk]
    simp only [F, map_smul, map_mul, Module.End.mul_apply]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ K'))

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem twTr_eq (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K') :
    twTr ρ K K' f A = LinearMap.trace ℂ (fixed ρ K') ((levOp ρ K K' f A).restrict h) := dif_pos h

theorem trace_restrict_congr {W : Submodule ℂ V} {L L' : V →ₗ[ℂ] V} (e : L = L') (h : ∀ v ∈ W, L v ∈ W)
    (h' : ∀ v ∈ W, L' v ∈ W) : LinearMap.trace ℂ W (L.restrict h) = LinearMap.trace ℂ W (L'.restrict h') := by
  subst e; rfl

theorem restrict_add' {W : Submodule ℂ V} (L₁ L₂ : V →ₗ[ℂ] V) (h₁ : ∀ v ∈ W, L₁ v ∈ W) (h₂ : ∀ v ∈ W, L₂ v ∈ W)
    (h : ∀ v ∈ W, (L₁ + L₂) v ∈ W) : (L₁ + L₂).restrict h = L₁.restrict h₁ + L₂.restrict h₂ := by
  ext x; simp [LinearMap.restrict_apply]

theorem restrict_smul' {W : Submodule ℂ V} (L : V →ₗ[ℂ] V) (c : ℂ) (h₁ : ∀ v ∈ W, L v ∈ W)
    (h : ∀ v ∈ W, (c • L) v ∈ W) : (c • L).restrict h = c • L.restrict h₁ := by
  ext x; simp [LinearMap.restrict_apply]

theorem trace_id_eq_finrank (W : Type) [AddCommGroup W] [Module ℂ W] :
    LinearMap.trace ℂ W LinearMap.id = (Module.finrank ℂ W : ℂ) := by
  by_cases hW : Module.Finite ℂ W
  · exact LinearMap.trace_id ℂ W
  · rw [Module.finrank_of_not_finite hW]
    unfold LinearMap.trace
    rw [dif_neg]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hW (Module.Finite.of_basis b)

theorem relIndex_ne_zero_of_isOpen [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hK'o : IsOpen (K' : Set G)) : K'.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : Finite (K ⧸ K'.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hK'o.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem levOp_unit (ρ : Representation ℂ G V) (K K' : Subgroup G) :
    ∃ x₀ ∈ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ρ x₀ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' (1 : G)
  refine ⟨h, h.2, ?_⟩
  unfold levOp
  have hout : ∀ q : G ⧸ K', q ≠ (QuotientGroup.mk 1 : G ⧸ K') → q.out ∉ K' := by
    intro q hq hm
    apply hq
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using K'.inv_mem hm)
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K')
    (fun q hq => by rw [Set.indicator_of_notMem (hout q hq), zero_smul])]
  rw [hh, one_mul, Set.indicator_of_mem h.2]
  simp

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

theorem twTr_linear : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), ∀ (θ : G →* G), (∀ g, θ (θ g) = g) → ∀ A : V →ₗ[ℂ] V, (∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) → ∀ K' : Subgroup G, IsLevel θ K K' → (∀ f f' (c : ℂ), IsHecke K' f → IsHecke K' f' → twTr ρ K K' (f + f') A = twTr ρ K K' f A + twTr ρ K K' f' A ∧ twTr ρ K K' (c • f) A = c * twTr ρ K K' f A ∧ twTr ρ K K' f (c • A) = c * twTr ρ K K' f A) ∧ (fixed ρ K' = ⊥ → ∀ f, twTr ρ K K' f A = 0) ∧ twTr ρ K K' ((K' : Set G).indicator 1) LinearMap.id = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed ρ K') : ℂ) ∧ K'.relIndex K ≠ 0 := by
  intro G _ _ _ K _ hKc V _ _ ρ θ hθ A hA K' hlev
  obtain ⟨hK'o, _, hK'θ⟩ := hlev
  have hAf : ∀ v ∈ fixed ρ K', A v ∈ fixed ρ K' := fun v hv => A_fixed ρ θ hθ K' hK'θ A hA hv
  have hmaps : ∀ f, IsHecke K' f → ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K' := fun f hf =>
    levOp_mapsTo ρ K K' A f (finite_out_support hK'o hf.1) (fun k hk x => (hf.2 k hk x).1)
      (fun k hk x => (hf.2 k hk x).2) hAf
  refine ⟨?_, ?_, ?_, relIndex_ne_zero_of_isOpen hKc hK'o⟩
  · intro f f' c hf hf'
    have h1 := hmaps f hf
    have h2 := hmaps f' hf'
    have e1 := levOp_add ρ K K' f f' A (finite_out_support hK'o hf.1) (finite_out_support hK'o hf'.1)
    have e2 := levOp_smul_fun ρ K K' f A c
    have e3 := levOp_smul_op ρ K K' f A c
    have h12 : ∀ v ∈ fixed ρ K', levOp ρ K K' (f + f') A v ∈ fixed ρ K' := by
      intro v hv; rw [e1]; exact add_mem (h1 v hv) (h2 v hv)
    have hs : ∀ v ∈ fixed ρ K', (c • levOp ρ K K' f A) v ∈ fixed ρ K' := fun v hv =>
      Submodule.smul_mem _ c (h1 v hv)
    have hc : ∀ v ∈ fixed ρ K', levOp ρ K K' (c • f) A v ∈ fixed ρ K' := by
      intro v hv; rw [e2]; exact hs v hv
    have hc' : ∀ v ∈ fixed ρ K', levOp ρ K K' f (c • A) v ∈ fixed ρ K' := by
      intro v hv; rw [e3]; exact hs v hv
    refine ⟨?_, ?_, ?_⟩
    · rw [twTr_eq _ _ _ _ _ h12, twTr_eq _ _ _ _ _ h1, twTr_eq _ _ _ _ _ h2,
        trace_restrict_congr e1 h12 (fun v hv => add_mem (h1 v hv) (h2 v hv)), restrict_add' _ _ h1 h2, map_add]
    · rw [twTr_eq _ _ _ _ _ hc, twTr_eq _ _ _ _ _ h1, trace_restrict_congr e2 hc hs, restrict_smul' _ c h1,
        map_smul, smul_eq_mul]
    · rw [twTr_eq _ _ _ _ _ hc', twTr_eq _ _ _ _ _ h1, trace_restrict_congr e3 hc' hs, restrict_smul' _ c h1,
        map_smul, smul_eq_mul]
  · intro h0 f
    unfold twTr
    split_ifs with h
    · haveI : Subsingleton (fixed ρ K') := by
        have key : ∀ v : V, v ∈ fixed ρ K' → v = 0 := fun v hv => by
          rw [h0] at hv
          exact (Submodule.mem_bot ℂ).1 hv
        exact ⟨fun a b => Subtype.ext ((key _ a.2).trans (key _ b.2).symm)⟩
      rw [show (levOp ρ K K' f A).restrict h = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
    · rfl
  · obtain ⟨x₀, hx₀, hL⟩ := levOp_unit ρ K K'
    have hfx : ∀ v ∈ fixed ρ K', ρ x₀ v = v := fun v hv => (mem_fixed_iff ρ K' v).1 hv x₀ hx₀
    have hm : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K' := by
      intro v hv
      rw [hL, LinearMap.smul_apply, hfx v hv]
      exact Submodule.smul_mem _ _ hv
    rw [twTr_eq _ _ _ _ _ hm]
    have hr : (levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id).restrict hm =
        ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
      ext x
      simp [LinearMap.restrict_apply, hL, hfx x.1 x.2]
    rw [hr, map_smul, trace_id_eq_finrank, smul_eq_mul]

end GlobalTheory.TwTrLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.LocFinU

theorem relIndex_ne_zero_of_subset_cpt {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U P : Subgroup G) (hU : IsOpen (U : Set G)) (Ω : Set G) (hΩ : IsCompact Ω) (hP : (P : Set G) ⊆ Ω) :
    U.relIndex P ≠ 0 := by
  obtain ⟨s, hs⟩ := hΩ.elim_finite_subcover (fun g : Ω => (g : G) • (U : Set G)) (fun g => hU.smul _)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, U.one_mem, mul_one x⟩⟩)
  have hmem : ∀ q : P ⧸ U.subgroupOf P, ∃ i : s, ((Quotient.out q : P) : G) ∈ ((i : Ω) : G) • (U : Set G) := by
    intro q
    have := hs (hP (Quotient.out q).2)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨i, hi⟩, h⟩
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro q q' h
    have h1 := hf q
    have h2 := hf q'
    rw [h] at h1
    obtain ⟨u, hu, hu'⟩ := h1
    obtain ⟨u', hu2, hu2'⟩ := h2
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change QuotientGroup.mk _ = QuotientGroup.mk _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hu', ← hu2']
    simp only [smul_eq_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact U.mul_mem (U.inv_mem hu) hu2
  haveI : Finite (P ⧸ U.subgroupOf P) := Finite.of_injective f hinj
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem continuous_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

theorem isClosed_UL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) :
    IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) :=
      ((Units.continuous_val.matrix_map (continuous_cj w)).matrix_transpose.matrix_mul continuous_const).matrix_mul
        Units.continuous_val
    exact isClosed_eq hc continuous_const

theorem isCompact_KL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) :
    IsCompact (KL n w : Set (UL n w)) := by
  rw [Subtype.isCompact_iff]
  have hK : IsCompact (GlobalTheory.LFun.KGL w n : Set (GLw n w)) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  have : (Subtype.val '' (KL n w : Set (UL n w))) = (GlobalTheory.LFun.KGL w n : Set (GLw n w)) ∩ (UL n w : Set (GLw n w)) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨g, h2⟩, h1, rfl⟩
  rw [this]
  exact hK.inter_right (isClosed_UL n w)

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem cptPart_subset_of_comm {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (T : Subgroup G) (hc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    (cptPart T : Set G) ⊆ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨T.one_mem, ?_⟩
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
    exact isCompact_singleton
  | mul x y _ _ hx hy =>
    refine ⟨T.mul_mem hx.1 hy.1, ?_⟩
    have hxy : Commute x y := hc x hx.1 y hy.1
    have hcp : IsCompact (closure (Subgroup.zpowers x : Set G) * closure (Subgroup.zpowers y : Set G)) :=
      hx.2.mul hy.2
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcp.isClosed)
    rintro _ ⟨k, rfl⟩
    exact ⟨x ^ k, subset_closure ⟨k, rfl⟩, y ^ k, subset_closure ⟨k, rfl⟩, (hxy.mul_zpow k).symm⟩
  | inv x _ hx =>
    refine ⟨T.inv_mem hx.1, ?_⟩
    rw [Subgroup.zpowers_inv]
    exact hx.2

end GlobalTheory.LocFinU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexProd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.LevOpTmul

theorem finite_supp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) {f : G → ℂ} (hf : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport f) := hf
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x : G => (fun y : G => x⁻¹ * y) ⁻¹' (K : Set G))
    (fun x => hK.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun x : G => (x : G ⧸ K))).subset ?_
  intro q hq
  have hmem : q.out ∈ tsupport f := subset_tsupport f hq
  obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.1 (ht hmem)
  refine ⟨x, hx, ?_⟩
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  exact QuotientGroup.eq.2 hqx

theorem levOp_apply {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K₁ : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (S : Finset (G ⧸ K₁)) (hS : ∀ q : G ⧸ K₁, f q.out ≠ 0 → q ∈ S)
    (v : V) : levOp ρ K K₁ f A v = ((K₁.relIndex K : ℕ) : ℂ)⁻¹ • ∑ q ∈ S, f q.out • ρ q.out (A v) := by
  unfold levOp
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  · intro q hq
    rw [Function.mem_support] at hq
    apply hS
    intro h0
    apply hq
    rw [h0, zero_smul]

theorem term_mk {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K₁ : Subgroup G) (f : G → ℂ) (hf : ∀ k ∈ K₁, ∀ x, f (x * k) = f x) (w : V) (hw : ∀ k ∈ K₁, ρ k w = w) (g : G) :
    f (g : G ⧸ K₁).out = f g ∧ ρ (g : G ⧸ K₁).out w = ρ g w := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ g
  rw [hk]
  exact ⟨hf k k.2 g, by rw [map_mul, Module.End.mul_apply, hw k k.2]⟩

end GlobalTheory.BCT.LevOpTmul
end

